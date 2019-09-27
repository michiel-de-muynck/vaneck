type N = usize;

fn check_sequence(period: N, i: N, prev_num: N, sequence: &[N], last_index: &mut [N]) {
    /*if i == 0 {
        println!("Testing sequence: {:?}, period: {}", &sequence[0..period], period);
    }*/
    let prev_num_last_i = last_index[prev_num];
    if prev_num_last_i != 999 {
        last_index[prev_num] = period + i - 1;
        let cur_num = (period + i - 1) - prev_num_last_i;
        if sequence[i] == cur_num {
            if i == period - 3 {
                println!("Valid sequence found: {:?}, period: {}", &sequence[0..period], period);
            } else {
                check_sequence(period, i+1, cur_num, sequence, last_index);
            }
        }
        last_index[prev_num] = prev_num_last_i;
    }
}

fn extend_sequence(period: N, i: N, prev_num: N, max: N, sequence: &mut [N], last_index: &mut [N]) {
    debug_assert!(i > 0);
    let prev_num_last_i = last_index[prev_num];
    if prev_num_last_i != 999 {
        let cur_num = (i - 1) - prev_num_last_i;
        if cur_num == period-1 {
            // period-1 can't appear in the sequence
            return;
        }
        if cur_num > max {
            return;
        }
        let prev_sequence_i = sequence[i];
        if prev_sequence_i != 999 && prev_sequence_i != cur_num {
            return;
        }
        sequence[i] = cur_num;
        last_index[prev_num] = i - 1;
        if i == period - 1 {
            check_sequence(period, 0, cur_num, sequence, last_index);
        } else {
            extend_sequence(period, i+1, cur_num, max, sequence, last_index);
        }
        last_index[prev_num] = prev_num_last_i;
        sequence[i] = prev_sequence_i;
    } else {
        let prev_sequence_i = sequence[i];
        for n in i..=max {
            if prev_sequence_i != 999 && prev_sequence_i != n {
                continue;
            }
            if n == period-1 {
                // period-1 can't appear in the sequence
                continue;
            } else if n == period {
                if prev_num == period {
                    // can't have 2x period in a row
                    continue;
                }
                last_index[prev_num] = i - 1;
                sequence[i] = n;
                if i == period - 1 {
                    check_sequence(period, 0, n, sequence, last_index);
                } else {
                    extend_sequence(period, i+1, n, max, sequence, last_index);
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
                if sequence[projected_n] != 999 {
                    debug_assert_ne!(sequence[projected_n], prev_num);
                    continue;
                } else {
                    last_index[prev_num] = i - 1;
                    sequence[i] = n;
                    sequence[projected_n] = prev_num;
                    if i == period - 1 {
                        check_sequence(period, 0, n, sequence, last_index);
                    } else {
                        extend_sequence(period, i+1, n, max, sequence, last_index);
                    }
                    sequence[i] = prev_sequence_i;
                    sequence[projected_n] = 999;
                    last_index[prev_num] = prev_num_last_i;
                }
            }
        }
    }
}

fn start_sequence(period: N, sequence: &mut [N], last_index: &mut [N]) {
    debug_assert!(period >= 2);
    for n in 1..=period {
        sequence[0] = n;
        //println!("Start seq: {:?}, last_index: {:?}", &sequence[0..period], &last_index[0..period]);
        extend_sequence(period, 1, n, n, sequence, last_index);
        sequence[0] = 999;
    }
}

fn main() {
    let mut sequence = Vec::new();
    let mut last_index = Vec::new();

    sequence.resize(100, 999);
    last_index.resize(100, 999);

    for period in 5..=25 {
        start_sequence(period, &mut sequence, &mut last_index);
    }
}

// almost work (last one wrong):
// 6, 1, 7, 5, 7, 2, 6
// 12, 1, 13, 6, 13, 2, 8, 13, 3, 13, 2, 5, 12

// almost work (2nd-to last wrong):
// 4, 4, 1, 8, 4, 3, 6, 8
// 3, 6, 10, 3, 3, 1, 10, 4, 8, 10
// 4, 11, 2, 6, 11, 3, 11, 2, 5, 9, 11
// 3, 8, 12, 3, 3, 1, 12, 4, 12, 2, 10, 12