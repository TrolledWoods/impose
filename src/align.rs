/// Checks if a value is aligned to some alignment. The alignment has to
/// be a power of two, or else the output will nonsensical.
///
/// # Panics
/// If you pass a non-power-of-two align, it will panic in debug mode.
/// If you pass 0, it will panic in debug mode.
#[inline]
pub fn is_aligned(align: usize, value: usize) -> bool {
    debug_assert_ne!(align, 0, "Alignment cannot be 0");
    debug_assert!(
        align.is_power_of_two(),
        "Alignment has to be a power of two"
    );

    value & (align - 1) == 0
}

/// Returns a number that is aligned to the align passed in.
/// * return value >= value
/// * return value < value + align
///
/// # Panics
/// If you pass a non-power-of-two align, it will panic in debug mode.
#[inline]
pub fn to_aligned(align: usize, value: usize) -> usize {
    debug_assert_ne!(align, 0, "Alignment cannot be 0");
    debug_assert!(
        align.is_power_of_two(),
        "Alignment has to be a power of two"
    );

    (align + value - 1) & !(align - 1)
}

#[test]
fn test_is_aligned() {
    assert!(is_aligned(4, 8));
    assert!(is_aligned(4, 16));
    assert!(is_aligned(4, 0));
    assert!(!is_aligned(4, 3));
    assert!(!is_aligned(8, 7));
    assert!(is_aligned(8, 64));
    assert!(is_aligned(1, 2));
}

#[test]
fn test_to_aligned() {
    assert_eq!(8, to_aligned(4, 8));
    assert_eq!(16, to_aligned(4, 16));
    assert_eq!(0, to_aligned(4, 0));
    assert_eq!(4, to_aligned(4, 3));
    assert_eq!(8, to_aligned(8, 7));
    assert_eq!(64, to_aligned(8, 64));
    assert_eq!(64, to_aligned(8, 59));
    assert_eq!(2, to_aligned(1, 2));
}
