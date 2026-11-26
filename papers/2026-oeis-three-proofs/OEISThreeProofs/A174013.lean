import Mathlib

/-!
# OEIS A174013: Generating Function Identity and Linear Recurrences

We formalize the proof that the power series `A_ps(x) = ∑ n, a(n) x^n ∈ PowerSeries ℤ`
defined by the quadratic equation
`x (1 - x - x^2) A(x)^2 + (1 - 3x - x^2) A(x) - (1 - x) = 0`
(equivalently `(B(x) A(x) + H(x))^2 = D(x)` with `B = 2x(1 - x - x^2)`,
`H = 1 - 3x - x^2`, `D = 1 - 2x - x^2 + 6x^3 + 5x^4`) satisfies:
1. Uniqueness in `PowerSeries ℤ`.
2. A square-root-free first-order linear ODE over `PowerSeries ℤ`.
3. A sixth-order linear recurrence `E_op a n = 0` for all `n ≥ 5`.
4. R. J. Mathar's conjectured seventh-order linear recurrence `M_op a n = E_op a n + 4 E_op a (n - 1) = 0`
   for all `n ≥ 6` (in particular, all `n ≥ 7`).
-/

namespace OEISThreeProofs.A174013

open PowerSeries

/-- Recursive integer sequence for OEIS A174013 determined by
`x (1 - x - x^2) A(x)^2 + (1 - 3x - x^2) A(x) - (1 - x) = 0`. -/
def a174013 : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
    let get (k : ℕ) : ℤ := if k ≤ n then a174013 k else 0
    let c (m : ℕ) : ℤ := ∑ i ∈ Finset.range (m + 1), get i * get (m - i)
    (if n = 0 then -1 else 0) +
      3 * get n +
      (if 1 ≤ n then get (n - 1) else 0) -
      c n +
      (if 1 ≤ n then c (n - 1) else 0) +
      (if 2 ≤ n then c (n - 2) else 0)
termination_by n => n

/-- The formal power series `A_ps(x) = ∑ n, a174013 n * x^n` over `ℤ`. -/
noncomputable def A_ps : PowerSeries ℤ := PowerSeries.mk a174013

/-- Polynomial `B(x) = 2x(1 - x - x^2)`. -/
noncomputable def B_ps : PowerSeries ℤ :=
  2 * X * (1 - X - X ^ 2)

/-- Polynomial `H(x) = 1 - 3x - x^2`. -/
noncomputable def H_ps : PowerSeries ℤ :=
  1 - 3 * X - X ^ 2

/-- Polynomial `D(x) = 1 - 2x - x^2 + 6x^3 + 5x^4`. -/
noncomputable def D_ps : PowerSeries ℤ :=
  1 - 2 * X - X ^ 2 + 6 * X ^ 3 + 5 * X ^ 4

lemma coeff_A_ps (n : ℕ) : coeff n A_ps = a174013 n :=
  coeff_mk n a174013

private lemma coeff_X_mul' (p : PowerSeries ℤ) (d : ℕ) :
    coeff d (X * p) = if 1 ≤ d then coeff (d - 1) p else 0 := by
  simpa using coeff_X_pow_mul' p 1 d

private lemma coeff_X_sq_mul' (p : PowerSeries ℤ) (d : ℕ) :
    coeff d (X ^ 2 * p) = if 2 ≤ d then coeff (d - 2) p else 0 :=
  coeff_X_pow_mul' p 2 d

private lemma coeff_X_cube_mul' (p : PowerSeries ℤ) (d : ℕ) :
    coeff d (X ^ 3 * p) = if 3 ≤ d then coeff (d - 3) p else 0 :=
  coeff_X_pow_mul' p 3 d

private lemma coeff_A_ps_sq (m : ℕ) :
    coeff m (A_ps ^ 2) = ∑ i ∈ Finset.range (m + 1), a174013 i * a174013 (m - i) := by
  rw [sq, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i A_ps * coeff j A_ps)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_A_ps, coeff_A_ps]

private lemma sum_range_congr_le (n m : ℕ) (hm : m ≤ n) :
    (∑ i ∈ Finset.range (m + 1),
      (if i ≤ n then a174013 i else 0) * (if m - i ≤ n then a174013 (m - i) else 0)) =
      ∑ i ∈ Finset.range (m + 1), a174013 i * a174013 (m - i) := by
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : i ≤ n := le_trans hi_le hm
  have h2 : m - i ≤ n := le_trans (Nat.sub_le m i) hm
  simp [h1, h2]

private lemma a174013_zero : a174013 0 = 1 := by
  rw [a174013]

private lemma a174013_succ (n : ℕ) :
    a174013 (n + 1) =
      (if n = 0 then -1 else 0) +
        3 * a174013 n +
        (if 1 ≤ n then a174013 (n - 1) else 0) -
        (∑ i ∈ Finset.range (n + 1), a174013 i * a174013 (n - i)) +
        (if 1 ≤ n then ∑ i ∈ Finset.range (n - 1 + 1), a174013 i * a174013 (n - 1 - i) else 0) +
        (if 2 ≤ n then ∑ i ∈ Finset.range (n - 2 + 1), a174013 i * a174013 (n - 2 - i) else 0) := by
  conv_lhs => rw [a174013]
  have hsub1 : n - 1 ≤ n := Nat.sub_le n 1
  simp only [le_refl, ↓reduceIte, hsub1,
    sum_range_congr_le n n le_rfl,
    sum_range_congr_le n (n - 1) (Nat.sub_le n 1),
    sum_range_congr_le n (n - 2) (Nat.sub_le n 2)]

/-- `A_ps` satisfies the quadratic equation
`x(1 - x - x^2) A(x)^2 + (1 - 3x - x^2) A(x) - (1 - x) = 0`. -/
theorem A174013_quadratic :
    X * (1 - X - X ^ 2) * A_ps ^ 2 + (1 - 3 * X - X ^ 2) * A_ps - (1 - X) = 0 := by
  ext d
  have h1 : X * (1 - X - X ^ 2) * A_ps ^ 2 =
      X * A_ps ^ 2 - X ^ 2 * A_ps ^ 2 - X ^ 3 * A_ps ^ 2 := by ring
  have h2 : (1 - 3 * X - X ^ 2) * A_ps =
      A_ps - C 3 * (X * A_ps) - X ^ 2 * A_ps := by
    simp [map_ofNat]; ring
  rw [map_zero, map_sub, map_add, h1, h2]
  simp only [map_sub, coeff_one, coeff_X, coeff_C_mul, coeff_X_mul',
    coeff_X_sq_mul', coeff_X_cube_mul', coeff_A_ps]
  cases d with
  | zero =>
    simp [a174013_zero]
  | succ n =>
    have h1le : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have hsq0 : coeff n (A_ps ^ 2) =
        ∑ i ∈ Finset.range (n + 1), a174013 i * a174013 (n - i) := coeff_A_ps_sq n
    have ha := a174013_succ n
    rcases n with _ | _ | m
    · simp [ha, hsq0, a174013_zero]
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.le_add_left, Nat.add_sub_cancel_right]
      have h2le : (2 : ℕ) ≤ 2 := le_rfl
      have h3le : ¬ (3 : ℕ) ≤ 2 := by omega
      simp only [h2le, ↓reduceIte, h3le, Nat.sub_self, coeff_A_ps_sq]
      rw [ha]
      have h10 : ¬ (1 : ℕ) = 0 := by omega
      have h21 : ¬ (2 : ℕ) = 1 := by omega
      simp only [h10, h21, one_ne_zero, ↓reduceIte, le_rfl, Nat.sub_self,
        Nat.not_le_of_lt (by omega : 1 < 2)]
      ring
    · have h2le : 2 ≤ m + 2 + 1 := by omega
      have h3le : 3 ≤ m + 2 + 1 := by omega
      simp only [Nat.succ_ne_zero, ↓reduceIte, h1le, h2le, h3le, Nat.add_sub_cancel_right]
      have hs1 : m + 2 + 1 - 2 = m + 1 := by omega
      have hs2 : m + 2 + 1 - 3 = m := by omega
      rw [hs1, hs2, coeff_A_ps_sq, coeff_A_ps_sq, coeff_A_ps_sq, ha]
      simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte,
        Nat.le_add_left, Nat.le_add_right]
      have hm1 : m + 2 - 1 = m + 1 := by omega
      have hm2 : m + 2 - 2 = m := by omega
      rw [hm1, hm2]
      have hne0 : ¬ m + 2 = 0 := by omega
      have hne1 : ¬ m + 2 + 1 = 1 := by omega
      have hm_ne : ¬ m + 1 + 1 = 0 := by omega
      have hm_ne1 : ¬ 3 + m = 1 := by omega
      simp only [hne0, hne1, hm_ne, hm_ne1, ↓reduceIte]
      simp
      ring

/-- Polynomial identity `H(x)^2 - D(x) = -2(1 - x) B(x)`. -/
lemma H_sq_sub_D : H_ps ^ 2 - D_ps = -2 * (1 - X) * B_ps := by
  unfold H_ps D_ps B_ps
  ring

/-- `A_ps` satisfies the generating function identity `(B(x) A(x) + H(x))^2 = D(x)`. -/
theorem A174013_genfun_sq : (B_ps * A_ps + H_ps) ^ 2 = D_ps := by
  have hq := A174013_quadratic
  have hB : B_ps = 2 * (X * (1 - X - X ^ 2)) := by unfold B_ps; ring
  have hH : H_ps = 1 - 3 * X - X ^ 2 := rfl
  have hH2 : H_ps ^ 2 = D_ps - 2 * (1 - X) * B_ps := by
    linear_combination H_sq_sub_D
  calc
    (B_ps * A_ps + H_ps) ^ 2
        = B_ps ^ 2 * A_ps ^ 2 + 2 * B_ps * H_ps * A_ps + H_ps ^ 2 := by ring
    _ = B_ps ^ 2 * A_ps ^ 2 + 2 * B_ps * H_ps * A_ps + (D_ps - 2 * (1 - X) * B_ps) := by
        rw [hH2]
    _ = D_ps + 2 * B_ps *
          (X * (1 - X - X ^ 2) * A_ps ^ 2 + (1 - 3 * X - X ^ 2) * A_ps - (1 - X)) := by
        rw [hB, hH]; ring
    _ = D_ps := by rw [hq]; ring

/-- Uniqueness in `PowerSeries ℤ`: `A_ps` is the unique formal power series solving
`(B(x) A(x) + H(x))^2 = D(x)`. -/
theorem A174013_unique (A : PowerSeries ℤ) (hA : (B_ps * A + H_ps) ^ 2 = D_ps) :
    A = A_ps := by
  have hdiff : (B_ps * (A - A_ps)) * (B_ps * (A + A_ps) + 2 * H_ps) = 0 := by
    have h0 : (B_ps * A + H_ps) ^ 2 - (B_ps * A_ps + H_ps) ^ 2 = 0 := by
      rw [hA, A174013_genfun_sq, sub_self]
    linear_combination h0
  rcases mul_eq_zero.mp hdiff with h1 | h2
  · have hB_ne : B_ps ≠ 0 := by
      intro h0
      have hc := congrArg (coeff 1) h0
      have hBexp : B_ps = C 2 * X - C 2 * X ^ 2 - C 2 * X ^ 3 := by
        unfold B_ps; simp [map_ofNat]; ring
      rw [hBexp] at hc
      simp [coeff_X, coeff_X_pow] at hc
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hB_ne)
  · exfalso
    have hc := congrArg constantCoeff h2
    have hB0 : constantCoeff B_ps = 0 := by
      unfold B_ps
      simp
    have hH0 : constantCoeff H_ps = 1 := by
      unfold H_ps
      simp
    rw [map_add, map_mul, map_mul, hB0, zero_mul, zero_add, map_ofNat, hH0] at hc
    simp only [map_zero] at hc
    omega

/-- Helper: `derivative (C c * f) = C c * derivative f` over `PowerSeries ℤ`. -/
private lemma deriv_C_mul (c : ℤ) (f : PowerSeries ℤ) :
    derivative (C c * f) = C c * derivative f := by
  rw [Derivation.leibniz, derivative_C, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]

/-- Square-root-free first-order linear ODE satisfied by any power series `A` with
`(B(x) A(x) + H(x))^2 = D(x)`. -/
theorem ode_of_genfun_sq (A : PowerSeries ℤ) (hA : (B_ps * A + H_ps) ^ 2 = D_ps) :
    (X - 3 * X ^ 2 + 9 * X ^ 4 - 11 * X ^ 6 - 5 * X ^ 7) * derivative A +
      (1 - 3 * X + 3 * X ^ 3 - 6 * X ^ 4 - 9 * X ^ 5 - 5 * X ^ 6) * A =
      1 - X + 3 * X ^ 2 - 6 * X ^ 4 := by
  have hd := congrArg derivative hA
  rw [derivative_pow] at hd
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, map_add, Derivation.leibniz,
    smul_eq_mul] at hd
  set Y := B_ps * A + H_ps
  have hmul : (2 * Y * (B_ps * derivative A + A * derivative B_ps + derivative H_ps)) * Y =
      derivative D_ps * Y := congrArg (· * Y) hd
  have hY2 : Y * Y = D_ps := by simpa [sq] using hA
  have h_ode4 : (2 * D_ps * B_ps) * derivative A +
      (2 * D_ps * derivative B_ps - derivative D_ps * B_ps) * A =
      derivative D_ps * H_ps - 2 * D_ps * derivative H_ps := by
    linear_combination hmul - 2 * (B_ps * derivative A + A * derivative B_ps + derivative H_ps) * hY2
  have hB' : derivative B_ps = 2 - 4 * X - 6 * X ^ 2 := by
    have h1 : B_ps = C 2 * X - C 2 * X ^ 2 - C 2 * X ^ 3 := by
      unfold B_ps; simp [map_ofNat]; ring
    rw [h1, map_sub, map_sub, deriv_C_mul, deriv_C_mul, deriv_C_mul,
      derivative_X, derivative_X_pow, derivative_X_pow]
    simp [map_ofNat]
    ring
  have hH' : derivative H_ps = -3 - 2 * X := by
    have h1 : H_ps = 1 - C 3 * X - X ^ 2 := by
      unfold H_ps; simp [map_ofNat]
    rw [h1, map_sub, map_sub, derivative_one, deriv_C_mul, derivative_X, derivative_X_pow]
    simp [map_ofNat]
  have hD' : derivative D_ps = -2 - 2 * X + 18 * X ^ 2 + 20 * X ^ 3 := by
    have h1 : D_ps = 1 - C 2 * X - X ^ 2 + C 6 * X ^ 3 + C 5 * X ^ 4 := by
      unfold D_ps; simp [map_ofNat]
    rw [h1, map_add, map_add, map_sub, map_sub, derivative_one,
      deriv_C_mul, derivative_X, deriv_C_mul, deriv_C_mul,
      derivative_X_pow, derivative_X_pow, derivative_X_pow]
    simp [map_ofNat]
    ring
  have hP : 2 * D_ps * B_ps =
      4 * (X - 3 * X ^ 2 + 9 * X ^ 4 - 11 * X ^ 6 - 5 * X ^ 7) := by
    unfold D_ps B_ps; ring
  have hQ : 2 * D_ps * derivative B_ps - derivative D_ps * B_ps =
      4 * (1 - 3 * X + 3 * X ^ 3 - 6 * X ^ 4 - 9 * X ^ 5 - 5 * X ^ 6) := by
    rw [hB', hD']; unfold D_ps B_ps; ring
  have hR : derivative D_ps * H_ps - 2 * D_ps * derivative H_ps =
      4 * (1 - X + 3 * X ^ 2 - 6 * X ^ 4) := by
    rw [hD', hH']; unfold D_ps H_ps; ring
  rw [hP, hQ, hR] at h_ode4
  have h4 : (4 : PowerSeries ℤ) ≠ 0 := by
    intro h0
    have hc := congrArg constantCoeff h0
    rw [map_ofNat] at hc
    simp only [map_zero] at hc
    omega
  apply mul_left_cancel₀ h4
  linear_combination h_ode4

/-- The sixth-order recurrence operator `E_op a n`. -/
def E_op (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  (n + 1 : ℤ) * a n -
    3 * (n : ℤ) * a (n - 1) +
    (9 * (n : ℤ) - 24) * a (n - 3) -
    6 * a (n - 4) +
    (46 - 11 * (n : ℤ)) * a (n - 5) +
    (25 - 5 * (n : ℤ)) * a (n - 6)

/-- R. J. Mathar's seventh-order recurrence operator `M_op a n = E_op a n + 4 E_op a (n - 1)`. -/
def M_op (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  (n + 1 : ℤ) * a n +
    (n : ℤ) * a (n - 1) +
    12 * (1 - (n : ℤ)) * a (n - 2) +
    (9 * (n : ℤ) - 24) * a (n - 3) +
    (36 * (n : ℤ) - 138) * a (n - 4) +
    (22 - 11 * (n : ℤ)) * a (n - 5) +
    (253 - 49 * (n : ℤ)) * a (n - 6) +
    (120 - 20 * (n : ℤ)) * a (n - 7)

lemma M_op_eq_E_add (a : ℕ → ℤ) (n : ℕ) (hn : 6 ≤ n) :
    M_op a n = E_op a n + 4 * E_op a (n - 1) := by
  unfold M_op E_op
  have h1 : n - 1 - 1 = n - 2 := by omega
  have h3 : n - 1 - 3 = n - 4 := by omega
  have h4 : n - 1 - 4 = n - 5 := by omega
  have h5 : n - 1 - 5 = n - 6 := by omega
  have h6 : n - 1 - 6 = n - 7 := by omega
  rw [h1, h3, h4, h5, h6]
  have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [hn1]
  ring

private lemma coeff_X_pow_mul_deriv (A : PowerSeries ℤ) (k n : ℕ) (hk : k ≤ n) :
    coeff n (X ^ k * derivative A) =
      coeff (n - k + 1) A * ((n : ℤ) - (k : ℤ) + 1) := by
  rw [coeff_X_pow_mul', ite_eq_left_iff.mpr (fun h => (h hk).elim), coeff_derivative]
  have hcast : ((n - k : ℕ) : ℤ) = (n : ℤ) - (k : ℤ) := by omega
  rw [hcast]

private lemma coeff_X_pow_mul_zero (A : PowerSeries ℤ) (k n : ℕ) (hk : n < k) :
    coeff n (X ^ k * A) = 0 := by
  rw [coeff_X_pow_mul', ite_eq_right_iff.mpr (fun h => by omega)]

private lemma coeff_X_pow_mul_pos (A : PowerSeries ℤ) (k n : ℕ) (hk : k ≤ n) :
    coeff n (X ^ k * A) = coeff (n - k) A := by
  rw [coeff_X_pow_mul', ite_eq_left_iff.mpr (fun h => (h hk).elim)]

/-- Sixth-order linear recurrence for `n ≥ 5`. -/
theorem sixth_order_recurrence (A : PowerSeries ℤ) (hA : (B_ps * A + H_ps) ^ 2 = D_ps)
    (n : ℕ) (hn : 5 ≤ n) : E_op (fun k => coeff k A) n = 0 := by
  have hode := congrArg (coeff n) (ode_of_genfun_sq A hA)
  have hL1 : (X - 3 * X ^ 2 + 9 * X ^ 4 - 11 * X ^ 6 - 5 * X ^ 7 : PowerSeries ℤ) =
      X ^ 1 - C 3 * X ^ 2 + C 9 * X ^ 4 - C 11 * X ^ 6 - C 5 * X ^ 7 := by
    simp [map_ofNat]
  have hL2 : (1 - 3 * X + 3 * X ^ 3 - 6 * X ^ 4 - 9 * X ^ 5 - 5 * X ^ 6 : PowerSeries ℤ) =
      1 - C 3 * X ^ 1 + C 3 * X ^ 3 - C 6 * X ^ 4 - C 9 * X ^ 5 - C 5 * X ^ 6 := by
    simp [map_ofNat]
  have hR : coeff n (1 - X + 3 * X ^ 2 - 6 * X ^ 4 : PowerSeries ℤ) = 0 := by
    have h1 : n ≠ 0 := by omega
    have h2 : n ≠ 1 := by omega
    have h3 : n ≠ 2 := by omega
    have h4 : n ≠ 4 := by omega
    have hR' : (1 - X + 3 * X ^ 2 - 6 * X ^ 4 : PowerSeries ℤ) =
        1 - X + C 3 * X ^ 2 - C 6 * X ^ 4 := by
      simp [map_ofNat]
    rw [hR']
    simp [coeff_one, coeff_X, coeff_X_pow, h1, h2, h3, h4]
  rw [hR, hL1, hL2] at hode
  have hX1 : coeff n (X ^ 1 * derivative A) = coeff n A * (n : ℤ) := by
    have h := coeff_X_pow_mul_deriv A 1 n (by omega)
    have hsub : n - 1 + 1 = n := by omega
    rw [hsub] at h
    linear_combination h
  have hX2 : coeff n (X ^ 2 * derivative A) = coeff (n - 1) A * ((n : ℤ) - 1) := by
    have h := coeff_X_pow_mul_deriv A 2 n (by omega)
    have hsub : n - 2 + 1 = n - 1 := by omega
    rw [hsub] at h
    linear_combination h
  have hX4 : coeff n (X ^ 4 * derivative A) = coeff (n - 3) A * ((n : ℤ) - 3) := by
    have h := coeff_X_pow_mul_deriv A 4 n (by omega)
    have hsub : n - 4 + 1 = n - 3 := by omega
    rw [hsub] at h
    linear_combination h
  have hA1 : coeff n (X ^ 1 * A) = coeff (n - 1) A := coeff_X_pow_mul_pos A 1 n (by omega)
  have hA3 : coeff n (X ^ 3 * A) = coeff (n - 3) A := coeff_X_pow_mul_pos A 3 n (by omega)
  have hA4 : coeff n (X ^ 4 * A) = coeff (n - 4) A := coeff_X_pow_mul_pos A 4 n (by omega)
  have hA5 : coeff n (X ^ 5 * A) = coeff (n - 5) A := coeff_X_pow_mul_pos A 5 n (by omega)
  have h_expand :
      coeff n ((X ^ 1 - C 3 * X ^ 2 + C 9 * X ^ 4 - C 11 * X ^ 6 - C 5 * X ^ 7) * derivative A +
        (1 - C 3 * X ^ 1 + C 3 * X ^ 3 - C 6 * X ^ 4 - C 9 * X ^ 5 - C 5 * X ^ 6) * A) =
      coeff n (X ^ 1 * derivative A) - 3 * coeff n (X ^ 2 * derivative A) +
        9 * coeff n (X ^ 4 * derivative A) - 11 * coeff n (X ^ 6 * derivative A) -
        5 * coeff n (X ^ 7 * derivative A) +
        coeff n A - 3 * coeff n (X ^ 1 * A) + 3 * coeff n (X ^ 3 * A) -
        6 * coeff n (X ^ 4 * A) - 9 * coeff n (X ^ 5 * A) - 5 * coeff n (X ^ 6 * A) := by
    simp only [sub_mul, add_mul, mul_assoc, map_add, map_sub, coeff_C_mul, one_mul]
    ring
  rw [h_expand, hX1, hX2, hX4, hA1, hA3, hA4, hA5] at hode
  unfold E_op
  rcases eq_or_lt_of_le hn with rfl | hn6
  · have h6d : coeff 5 (X ^ 6 * derivative A) = 0 := coeff_X_pow_mul_zero _ 6 5 (by omega)
    have h7d : coeff 5 (X ^ 7 * derivative A) = 0 := coeff_X_pow_mul_zero _ 7 5 (by omega)
    have h6a : coeff 5 (X ^ 6 * A) = 0 := coeff_X_pow_mul_zero _ 6 5 (by omega)
    rw [h6d, h7d, h6a] at hode
    linear_combination hode
  · have hn6' : 6 ≤ n := hn6
    have hX6 : coeff n (X ^ 6 * derivative A) = coeff (n - 5) A * ((n : ℤ) - 5) := by
      have h := coeff_X_pow_mul_deriv A 6 n hn6'
      have hsub : n - 6 + 1 = n - 5 := by omega
      rw [hsub] at h
      linear_combination h
    have hA6 : coeff n (X ^ 6 * A) = coeff (n - 6) A := coeff_X_pow_mul_pos A 6 n hn6'
    rcases eq_or_lt_of_le hn6' with rfl | hn7
    · have h7d : coeff 6 (X ^ 7 * derivative A) = 0 := coeff_X_pow_mul_zero _ 7 6 (by omega)
      rw [hX6, h7d, hA6] at hode
      linear_combination hode
    · have hn7' : 7 ≤ n := hn7
      have hX7 : coeff n (X ^ 7 * derivative A) = coeff (n - 6) A * ((n : ℤ) - 6) := by
        have h := coeff_X_pow_mul_deriv A 7 n hn7'
        have hsub : n - 7 + 1 = n - 6 := by omega
        rw [hsub] at h
        linear_combination h
      rw [hX6, hX7, hA6] at hode
      linear_combination hode

/-- Sixth-order recurrence specialized to `a174013`. -/
theorem a174013_sixth_order (n : ℕ) (hn : 5 ≤ n) : E_op a174013 n = 0 := by
  have h := sixth_order_recurrence A_ps A174013_genfun_sq n hn
  simpa [coeff_A_ps] using h

/-- R. J. Mathar's seventh-order recurrence for `n ≥ 6` (and hence all `n ≥ 7`). -/
theorem mathar_seventh_order_recurrence (A : PowerSeries ℤ)
    (hA : (B_ps * A + H_ps) ^ 2 = D_ps) (n : ℕ) (hn : 6 ≤ n) :
    M_op (fun k => coeff k A) n = 0 := by
  rw [M_op_eq_E_add _ n hn]
  have h1 := sixth_order_recurrence A hA n (by omega)
  have h2 := sixth_order_recurrence A hA (n - 1) (by omega)
  rw [h1, h2]
  norm_num

/-- R. J. Mathar's seventh-order recurrence specialized to `a174013` for all `n ≥ 7`. -/
theorem a174013_mathar_recurrence (n : ℕ) (hn : 7 ≤ n) : M_op a174013 n = 0 := by
  have h := mathar_seventh_order_recurrence A_ps A174013_genfun_sq n (by omega)
  simpa [coeff_A_ps] using h

/-- Verification of initial terms `a_0, ..., a_{10}` against OEIS A174013. -/
theorem a174013_initial_terms :
    [a174013 0, a174013 1, a174013 2, a174013 3, a174013 4, a174013 5,
     a174013 6, a174013 7, a174013 8, a174013 9, a174013 10] =
      [1, 1, 3, 6, 12, 22, 37, 56, 73, 75, 44] := by
  have h0 : a174013 0 = 1 := a174013_zero
  have h1 : a174013 1 = 1 := by norm_num [a174013_succ, h0]
  have h2 : a174013 2 = 3 := by norm_num [a174013_succ, Finset.sum_range_succ, h0, h1]
  have h3 : a174013 3 = 6 := by norm_num [a174013_succ, Finset.sum_range_succ, h0, h1, h2]
  have h4 : a174013 4 = 12 := by norm_num [a174013_succ, Finset.sum_range_succ, h0, h1, h2, h3]
  have h5 : a174013 5 = 22 := by norm_num [a174013_succ, Finset.sum_range_succ, h0, h1, h2, h3, h4]
  have h6 : a174013 6 = 37 := by
    norm_num [a174013_succ, Finset.sum_range_succ, h0, h1, h2, h3, h4, h5]
  have h7 : a174013 7 = 56 := by
    norm_num [a174013_succ, Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, h6]
  have h8 : a174013 8 = 73 := by
    norm_num [a174013_succ, Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, h6, h7]
  have h9 : a174013 9 = 75 := by
    norm_num [a174013_succ, Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  have h10 : a174013 10 = 44 := by
    norm_num [a174013_succ, Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

end OEISThreeProofs.A174013
