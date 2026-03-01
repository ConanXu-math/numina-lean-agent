import Mathlib

/-- What is the greatest common divisor of $2^{1001}-1$ and $2^{1012}-1$?
Show that it is $2^{11} - 1$. -/
theorem mathd_numbertheory_284 : Nat.gcd (2 ^ 1001 - 1) (2 ^ 1012 - 1) = 2 ^ 11 - 1 := by
  have h : Nat.gcd 1001 1012 = 11 := by decide
  calc
    Nat.gcd (2 ^ 1001 - 1) (2 ^ 1012 - 1) = 2 ^ (Nat.gcd 1001 1012) - 1 := by
      rw [Nat.pow_sub_one_gcd_pow_sub_one]
    _ = 2 ^ 11 - 1 := by rw [h]
