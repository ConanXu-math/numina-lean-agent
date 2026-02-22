import Mathlib

/-- (a) Find all positive integers $n$ for which $2^n-1$ is divisible by $7$.
(b) Prove that there is no positive integer $n$ for which $2^n+1$ is divisible by $7$. -/
theorem imo_1964_p1_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h_order : orderOf (2 : ZMod 7) = 3 := by
    have h3 : (2 : ZMod 7) ^ 3 = 1 := by decide
    have h1 : (2 : ZMod 7) ^ 1 ≠ 1 := by decide
    have prime3 : Nat.Prime 3 := by decide
    have h_div : orderOf (2 : ZMod 7) ∣ 3 :=
      (orderOf_dvd_iff_pow_eq_one (x := (2 : ZMod 7))).mpr h3
    rcases (Nat.dvd_prime prime3).mp h_div with (h | h)
    · exfalso
      exact h1 (by simpa [h] using pow_orderOf_eq_one (2 : ZMod 7))
    · exact h
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  constructor
  · intro h
    have h1 : (2 : ZMod 7) ^ n = 1 := by
      have h1' : (2 ^ n : ZMod 7) = (1 : ZMod 7) :=
        (ZMod.natCast_eq_natCast_iff (2 ^ n) 1 7).mpr (((Nat.modEq_iff_dvd' hpos).2 h).symm)
      simpa using h1'
    have h2 : orderOf (2 : ZMod 7) ∣ n := (orderOf_dvd_iff_pow_eq_one (x := (2 : ZMod 7))).mpr h1
    rw [h_order] at h2
    exact h2
  · intro h
    have h1 : (2 : ZMod 7) ^ n = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, h_order]
      exact h
    have h2 : (2 ^ n : ZMod 7) = (1 : ZMod 7) := by
      simpa using h1
    have h3 : 2 ^ n ≡ 1 [MOD 7] := (ZMod.natCast_eq_natCast_iff (2 ^ n) 1 7).mp h2
    exact (Nat.modEq_iff_dvd' hpos).1 h3.symm

theorem imo_1964_p1_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  sorry