use std::fs::{File, OpenOptions};
use std::sync::Mutex;
use std::io::Write;

#[allow(unused_imports)]
use rayon::prelude::*;

#[macro_use]
extern crate lazy_static;

type N = usize;

lazy_static! {
    static ref OUTPUT_FILE: Mutex<File> = Mutex::new(
        OpenOptions::new()
            .append(true)
            .create(true)
            .open("output.txt")
            .expect("can't open output.txt")
    );
    static ref PERIODS_COMPLETED: Mutex<Vec<bool>> = Mutex::new(vec![false; 64]);
}

fn is_trivial_masks(masks: &[u64]) -> bool {
    masks[0].count_ones() == 1 && masks[1].count_ones() == 1 && masks[0].trailing_zeros() == 1 && masks[1].trailing_zeros() == 1
}

fn output(s: String) {
    println!("{}", s);
    let mut output_file = OUTPUT_FILE.lock().expect("can't lock mutex");
    writeln!(*output_file, "{}", s).expect("failed to write to output file");
    output_file.sync_data().expect("failed to flush output file");
}

fn masks_to_sequence(masks: &[u64]) -> Vec<N> {
    masks.into_iter().map(|mask| {
        if mask.count_ones() == 1 {
            mask.trailing_zeros() as N
        } else {
            10000+(mask.count_ones() as N)
        }
    }).collect()
}

#[allow(dead_code)]
fn masks_to_string(masks: &[u64]) -> String {
    masks.into_iter().map(|mask| {
        if mask.count_ones() == 1 {
            format!("{}", mask.trailing_zeros())
        } else if mask.count_ones() <= 7 {
            let mut s = "".to_owned();
            let mut x = *mask;
            while x > 0 {
                let d = x.trailing_zeros() as usize;
                s += &format!("{}", d);
                x -= 1 << d;
                if x != 0 {
                    s += "/";
                }
            }
            s
        } else {
            format!("???({})", mask.count_ones())
        }
    }).collect::<Vec<_>>().join(", ")
}

fn extend_sequence(period: N, i: N, masks: &[u64]) {
    debug_assert!(i > 0);
    if masks[i].count_ones() == 1 {
        if i == period - 1 {
            if is_trivial_masks(masks) {
                output(format!("Trivial sequence found for period: {}", period));
            } else {
                output("==========================================".to_owned());
                output(format!("Found: {:?}, period: {}", masks_to_sequence(masks), period));
                output("==========================================".to_owned());
            }
        } else {
            extend_sequence(period, i+1, masks);
        }
    } else {
        for n in 1..=period {
            let n_mask = 1 << n;
            if masks[i] & n_mask == 0 {
                continue;
            }

            let mut masks = masks[0..period].to_owned();

            masks[i] = n_mask;

            struct LoopState<'a> {
                impossible: bool,
                changed: bool,
                masks: &'a mut [u64],
                period: usize, // the only reason we take this up into the loop is just convenience
            }

            let mut loop_state = LoopState {
                impossible: false,
                changed: true,
                masks: &mut masks,
                period,
            };

            fn apply_mask_to_pos(pos: usize, mask: u64, loop_state: &mut LoopState) {
                debug_assert!(pos < loop_state.period);
                let prev_mask = loop_state.masks[pos];
                loop_state.masks[pos] &= mask;
                let new_mask = loop_state.masks[pos];
                if new_mask == 0 {
                    loop_state.impossible = true;
                } else if new_mask != prev_mask {
                    loop_state.changed = true;
                }
            }

            // if we know the next element, say it is x,
            // then the current element and the element x back must be the same
            // so only elements that are in both of their masks are actually possible
            fn project_back(projected_pos: usize, loop_state: &mut LoopState) {
                let next_el_pos = if projected_pos == loop_state.period-1 { 0 } else { projected_pos+1 };
                let next_el_mask = loop_state.masks[next_el_pos];
                debug_assert!(next_el_mask != 0);
                if next_el_mask.count_ones() == 1 {
                    let d = next_el_mask.trailing_zeros() as usize;
                    debug_assert!(d <= loop_state.period);
                    let new_test_loc = if d <= projected_pos {
                        projected_pos - d
                    } else {
                        loop_state.period + projected_pos - d
                    };
                    let overlap = loop_state.masks[projected_pos] & loop_state.masks[new_test_loc];
                    apply_mask_to_pos(projected_pos, overlap, loop_state);
                    apply_mask_to_pos(new_test_loc, overlap, loop_state);
                }
            }

            // if the element at projected_pos is a concrete element x,
            // make the elements between projected_pos and the minimum projected location to the left not be x
            fn eliminate_x_up_to_projection(projected_pos: usize, loop_state: &mut LoopState) {
                if loop_state.masks[projected_pos].count_ones() == 1 {
                    let next_el_pos = if projected_pos == loop_state.period-1 { 0 } else { projected_pos+1 };
                    let next_el_mask = loop_state.masks[next_el_pos];
                    let min_d = next_el_mask.trailing_zeros() as usize;
                    debug_assert!(min_d <= loop_state.period);
                    for j in 1..min_d {
                        let new_test_loc = if j <= projected_pos {
                            projected_pos - j
                        } else {
                            loop_state.period + projected_pos - j
                        };
                        apply_mask_to_pos(new_test_loc, !loop_state.masks[projected_pos], loop_state);
                    }
                }
            }

            // the range (next element) of an element must be:
            //  - not x, if the mask of the element doesn't overlap with the mask of the element x back
            //  - at most x, if the element is known and the earliest time it reappears is x elements back
            fn bound_range_of(of_pos: usize, loop_state: &mut LoopState) {
                let of_mask = loop_state.masks[of_pos];
                let range_pos = if of_pos == loop_state.period-1 { 0 } else { of_pos+1 };
                let mut new_range_mask : u64 = !0;
                for j in 1..loop_state.period {
                    let new_test_loc = if j <= of_pos {
                        of_pos - j
                    } else {
                        loop_state.period + of_pos - j
                    };
                    if loop_state.masks[new_test_loc] & of_mask == 0 {
                        new_range_mask &= !(1 << j);
                    } else if of_mask.count_ones() == 1 && loop_state.masks[new_test_loc] == of_mask {
                        new_range_mask &= (1 << (j+1)) - 1;
                        break;
                    }
                }
                apply_mask_to_pos(range_pos, new_range_mask, loop_state);
            }

            // if we know that the range is at least x,
            // then the value can't be equal to any of the known values that appear in the previous x-1 elements 
            fn bound_val_based_on_min_range(val_pos: usize, loop_state: &mut LoopState) {
                if loop_state.masks[val_pos].count_ones() == 1 {
                    // we can't get more info by running this function,
                    // only detect impossibilities here that would also be detected in eliminate_x_up_to_projection,
                    // so just don't run this function
                    return;
                }
                let range_pos = if val_pos == loop_state.period-1 { 0 } else { val_pos+1 };
                let range_mask = loop_state.masks[range_pos];
                let min_d = range_mask.trailing_zeros() as usize;
                debug_assert!(min_d <= loop_state.period);
                let mut new_val_mask : u64 = !0;
                for j in 1..min_d {
                    let new_test_loc = if j <= val_pos {
                        val_pos - j
                    } else {
                        loop_state.period + val_pos - j
                    };
                    if loop_state.masks[new_test_loc].count_ones() == 1 {
                        new_val_mask &= !loop_state.masks[new_test_loc];
                    }
                }
                apply_mask_to_pos(val_pos, new_val_mask, loop_state);
            }

            // do some first iterations that are simple and fast, but likely effective
            project_back(i-1, &mut loop_state);
            if loop_state.impossible {
                continue;
            }
            for j in i..period {
                loop_state.changed = false;
                bound_range_of(j, &mut loop_state);
                if loop_state.changed == false || loop_state.impossible {
                    break;
                }
                project_back(j, &mut loop_state);
                if loop_state.changed == false || loop_state.impossible {
                    break;
                }
            }

            loop_state.changed = true;

            while loop_state.changed && !loop_state.impossible {
                loop_state.changed = false;

                for i in 0..period {
                    project_back(i, &mut loop_state);
                    if loop_state.impossible {
                        break;
                    }
                    eliminate_x_up_to_projection(i, &mut loop_state);
                    if loop_state.impossible {
                        break;
                    }
                    bound_range_of(i, &mut loop_state);
                    if loop_state.impossible {
                        break;
                    }
                    bound_val_based_on_min_range(i, &mut loop_state);
                }
            }

            if loop_state.impossible {
                continue;
            }

            if i == period - 1 {
                if is_trivial_masks(&masks) {
                    output(format!("Trivial sequence found for period: {}", period));
                } else {
                    output("==========================================".to_owned());
                    output(format!("Found: {:?}, period: {}", masks_to_sequence(&masks), period));
                    output("==========================================".to_owned());
                }
            } else {
                extend_sequence(period, i+1, &mut masks);
            }
        }
    }
}

fn start_sequence(period: N, masks: &mut [u64]) {
    debug_assert!(period >= 3);
    for n in 1..=period {
        if n == period-1 {
            continue;
        }
        // due to the cyclic nature of periodic sequences we can assume that the first element is the largest
        for mask in masks[0..period].iter_mut() {
            *mask = (1 << (n+1)) - 2; // - 2 because elements also can't be 0.
            if n == period {
                *mask -= 1 << (period-1);
            }
        }
        masks[0] &= 1 << n;
        // also, at least once in the sequence, the element after the largest element has to be at most floor(period/2)
        // (note that you can't have 2x period in a row).
        masks[1] &= (1 << ((period/2)+1)) - 1;
        extend_sequence(period, 1, masks);
    }
}

fn main() {
    let start_period = 5;

    // set periods below start_period as completed
    {
        let mut periods_completed = PERIODS_COMPLETED.lock().unwrap();
        for p in 0..start_period {
            periods_completed[p] = true;
        }
    }

    rayon::ThreadPoolBuilder::new().num_threads(7).build_global().unwrap();

    (start_period..61).into_iter().par_bridge().for_each(|period| {
    //(start_period..61).into_iter().for_each(|period| {
        let mut masks = Vec::new();

        masks.resize(period as usize, 0);

        start_sequence(period as N, &mut masks);

        {
            let mut periods_completed = PERIODS_COMPLETED.lock().unwrap();
            assert_eq!(periods_completed[period], false);
            periods_completed[period] = true;

            let least_uncompleted_period = periods_completed.iter().enumerate().find(|(_, complete)| !**complete).expect("all periods completed?!").0;
            output(format!("Completed period: {}, least uncompleted period: {}", period, least_uncompleted_period));
        }
    });
}

// almost work (last one wrong):
// 6, 1, 7, 5, 7, 2, 6
// 12, 1, 13, 6, 13, 2, 8, 13, 3, 13, 2, 5, 12

// only first one wrong:
// 5, 1, 5, 2, 5
// 6, 3, 2, 6, 3, 3

// almost work (2nd-to last wrong):
// 4, 4, 1, 8, 4, 3, 6, 8
// 3, 6, 10, 3, 3, 1, 10, 4, 8, 10
// 4, 11, 2, 6, 11, 3, 11, 2, 5, 9, 11
// 3, 8, 12, 3, 3, 1, 12, 4, 12, 2, 10, 12
