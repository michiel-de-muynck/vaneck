use std::fs::{File, OpenOptions};
use std::sync::Mutex;
use std::io::Write;
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

fn is_trivial(sequence: &[N]) -> bool {
    sequence[0] == 1 && sequence[1] == 1
}

fn output(s: String) {
    println!("{}", s);
    let mut output_file = OUTPUT_FILE.lock().expect("can't lock mutex");
    writeln!(*output_file, "{}", s).expect("failed to write to output file");
    output_file.sync_data().expect("failed to flush output file");
}

fn check_sequence(period: N, i: N, prev_num: N, sequence: &[N], last_index: &mut [N]) {
    if i == 0 && !is_trivial(sequence) {
        output(format!("Testing sequence: {:?}, period: {}", &sequence[0..period], period));
    }
    let prev_num_last_i = last_index[prev_num];
    if prev_num_last_i != 999 {
        last_index[prev_num] = period + i - 1;
        let cur_num = (period + i - 1) - prev_num_last_i;
        if sequence[i] == cur_num {
            if i == period - 3 {
                if is_trivial(sequence) {
                    output(format!("Trivial sequence found for period: {}", period));
                } else {
                    output("==========================================".to_owned());
                    output(format!("Valid sequence found: {:?}, period: {}", &sequence[0..period], period));
                    output("==========================================".to_owned());
                }
            } else {
                check_sequence(period, i+1, cur_num, sequence, last_index);
            }
        }
        last_index[prev_num] = prev_num_last_i;
    }
}

fn extend_sequence(period: N, i: N, prev_num: N, sequence: &mut [N], last_index: &mut [N], masks: &mut [u64]) {
    debug_assert!(i > 0);
    let prev_num_last_i = last_index[prev_num];
    if period <= 25 && i >= period-1 && !is_trivial(sequence) {
        output(format!("Close: {:?}, period: {}, i: {}", &sequence[0..period], period, i));
    }
    if prev_num_last_i != 999 {
        let cur_num = (i - 1) - prev_num_last_i;
        let cur_num_mask = 1 << cur_num;
        if masks[i] & cur_num_mask == 0 {
            return;
        }
        let prev_sequence_i = sequence[i];
        debug_assert_eq!(prev_sequence_i, 999);
        sequence[i] = cur_num;
        last_index[prev_num] = i - 1;
        let prev_mask = std::mem::replace(&mut masks[i], cur_num_mask);
        if i == period - 1 {
            check_sequence(period, 0, cur_num, sequence, last_index);
        } else {
            extend_sequence(period, i+1, cur_num, sequence, last_index, masks);
        }
        masks[i] = prev_mask;
        last_index[prev_num] = prev_num_last_i;
        sequence[i] = prev_sequence_i;
    } else {
        // TODO: can't have 2x period in a row
        let prev_sequence_i = sequence[i];
        debug_assert_eq!(prev_sequence_i, 999);
        for n in i..=period {
            let n_mask = 1 << n;
            let prev_num_mask = 1 << prev_num;
            if masks[i] & n_mask == 0 {
                continue;
            }
            if n == period {
                if prev_num == period {
                    // can't have 2x period in a row
                    continue;
                }
                let mut backup_mask = 0u64;
                for mask in masks[i+1..period].iter_mut() {
                    backup_mask <<= 1;
                    if *mask & prev_num_mask != 0 {
                        *mask -= prev_num_mask;
                    }
                    debug_assert_ne!(*mask, 0);
                }
                last_index[prev_num] = i - 1;
                sequence[i] = n;
                let prev_mask = std::mem::replace(&mut masks[i], n_mask);
                if i == period - 1 {
                    check_sequence(period, 0, n, sequence, last_index);
                } else {
                    extend_sequence(period, i+1, n, sequence, last_index, masks);
                }
                masks[i] = prev_mask;
                for mask in masks[i+1..period].iter_mut().rev() {
                    debug_assert_eq!(*mask & prev_num_mask, 0);
                    if backup_mask & 1 != 0 {
                        *mask |= prev_num_mask;
                    }
                    debug_assert_ne!(*mask, 0);
                    backup_mask >>= 1;
                }
                sequence[i] = prev_sequence_i;
                last_index[prev_num] = prev_num_last_i;
            } else {
                let projected_n = period + i - 1 - n;
                /*dbg!(projected_n);
                dbg!(i);
                dbg!(n);
                dbg!(&sequence[0..period]);*/
                debug_assert!(projected_n > i);
                debug_assert!(projected_n < period);
                let prev_projected_n_mask = masks[projected_n];
                if prev_projected_n_mask & prev_num_mask == 0 {
                    continue;
                }
                if i < period &&
                    (
                        projected_n == period-1 ||
                        projected_n == i+1 ||
                        masks[projected_n-1].count_ones() == 1 ||
                        masks[projected_n+1].count_ones() == 1
                    )
                {
                    let mut masks = masks[0..period].to_owned();

                    for mask in masks[projected_n+1..period].iter_mut() {
                        if *mask & prev_num_mask != 0 {
                            *mask -= prev_num_mask;
                        }
                    }

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

                    while loop_state.changed && !loop_state.impossible {
                        loop_state.changed = false;

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

                        // if we know the next element, project the current mask back that far
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
                                apply_mask_to_pos(new_test_loc, loop_state.masks[projected_pos], loop_state);
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

                        fn bound_range_of(of_pos: usize, loop_state: &mut LoopState) {
                            let of_mask = loop_state.masks[of_pos];
                            let range_pos = if of_pos == loop_state.period-1 { 0 } else { of_pos+1 };
                            for j in 1..=loop_state.period {
                                let new_test_loc = if j <= of_pos {
                                    of_pos - j
                                } else {
                                    loop_state.period + of_pos - j
                                };
                                if loop_state.masks[new_test_loc] & of_mask != 0 {
                                    let mut new_range_mask : u64 = !0;
                                    new_range_mask &= !((1 << j) - 1);
                                    if of_mask.count_ones() == 1 {
                                        for k in j..=loop_state.period {
                                            let new_test_loc = if k <= of_pos {
                                                of_pos - k
                                            } else {
                                                loop_state.period + of_pos - k
                                            };
                                            if loop_state.masks[new_test_loc] == of_mask {
                                                new_range_mask &= (1 << (k+1)) - 1;
                                                break;
                                            }
                                        }
                                    }
                                    apply_mask_to_pos(range_pos, new_range_mask, loop_state);
                                    break;
                                }
                            }
                        }

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
                        }
                    }

                    if loop_state.impossible {
                        return;
                    }

                    last_index[prev_num] = i - 1;
                    sequence[i] = n;
                    if i == period - 1 {
                        check_sequence(period, 0, n, sequence, last_index);
                    } else {
                        extend_sequence(period, i+1, n, sequence, last_index, &mut masks);
                    }
                    sequence[i] = prev_sequence_i;
                    last_index[prev_num] = prev_num_last_i;
                } else {
                    masks[projected_n] = prev_num_mask;
                    let mut backup_mask = 0u64;
                    for mask in masks[projected_n+1..period].iter_mut() {
                        backup_mask <<= 1;
                        if *mask & prev_num_mask != 0 {
                            backup_mask += 1;
                            *mask -= prev_num_mask;
                        }
                        debug_assert_ne!(*mask, 0);
                    }
                    last_index[prev_num] = i - 1;
                    sequence[i] = n;
                    let prev_mask = std::mem::replace(&mut masks[i], n_mask);
                    if i == period - 1 {
                        check_sequence(period, 0, n, sequence, last_index);
                    } else {
                        extend_sequence(period, i+1, n, sequence, last_index, masks);
                    }
                    masks[i] = prev_mask;
                    sequence[i] = prev_sequence_i;
                    last_index[prev_num] = prev_num_last_i;
                    masks[projected_n] = prev_projected_n_mask;
                    for mask in masks[projected_n+1..period].iter_mut().rev() {
                        debug_assert_eq!(*mask & prev_num_mask, 0);
                        if backup_mask & 1 != 0 {
                            *mask |= prev_num_mask;
                        }
                        debug_assert_ne!(*mask, 0);
                        backup_mask >>= 1;
                    }
                }
            }
        }
    }
}

fn start_sequence(period: N, sequence: &mut [N], last_index: &mut [N], masks: &mut [u64]) {
    debug_assert!(period >= 3);
    for n in 1..=period {
        sequence[0] = n;
        if n == period-1 {
            continue;
        }
        //println!("Start seq: {:?}, last_index: {:?}", &sequence[0..period], &last_index[0..period]);
        for mask in masks[0..period].iter_mut() {
            *mask = (1 << (n+1)) - 2;
            if n == period {
                *mask -= 1 << (period-1);
            }
        }
        extend_sequence(period, 1, n, sequence, last_index, masks);
    }
}

fn main() {
    //std::fs::create_dir_all("output").expect("Can't create output directory");

    let start_period = 5;

    // set periods below start_period as completed
    {
        let mut periods_completed = PERIODS_COMPLETED.lock().unwrap();
        for p in 0..start_period {
            periods_completed[p] = true;
        }
    }

    (start_period..62).into_iter().par_bridge().for_each(|period| {
        let mut sequence = Vec::new();
        let mut last_index = Vec::new();
        let mut masks = Vec::new();

        sequence.resize(3*period as usize, 999);
        last_index.resize(3*period as usize, 999);
        masks.resize(3*period as usize, 0);

        start_sequence(period as N, &mut sequence, &mut last_index, &mut masks);

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
