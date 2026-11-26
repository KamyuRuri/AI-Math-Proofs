import Mathlib

/-!
# OEIS A352834: Subpolynomial Growth and Global Extremum

Let `τ(m) = (Nat.divisors m).card` and define `a352834 n` as the least positive integer
`k` such that `gcd (τ (k * n)) (k * n) = k` (equivalently, the reduced denominator of
`τ(kn)/(kn)` equals `n`), or `0` if no such `k` exists.

We prove:
1. `IsValidA352834_iff_den`: exact equivalence with the reduced denominator of `τ(kn)/(kn)`.
2. `divisor_bound_explicit` and `a352834_subpolynomial`: for every `ε > 0`, there exists
   `C > 0` such that `a352834 n ≤ C * n ^ ε` for all `n ≥ 1`.
3. `a352834_154440`: `a352834 154440 = 840`.
4. `a352834_global_bound` and `a352834_strict_of_ne`: for every `n ≥ 1`,
   `154440 * (a352834 n)^3 ≤ 840^3 * n`, with strict inequality whenever `n ≠ 154440`.
5. `a352834_real_extremum`: `(a352834 n : ℝ) / (n : ℝ) ^ (1 / 3 : ℝ) ≤ 840 / (154440 : ℝ) ^ (1 / 3 : ℝ)`
   for all `n ≥ 1`, with equality iff `n = 154440`.
-/

namespace OEISThreeProofs.A352834

open scoped BigOperators

/-- Divisor counting function `τ(m)`. -/
def tau (m : ℕ) : ℕ := (Nat.divisors m).card

/-- Feasibility predicate for `k` at index `n`: `k > 0` and `gcd(τ(kn), kn) = k`. -/
def IsValidA352834 (n k : ℕ) : Prop :=
  0 < k ∧ Nat.gcd (tau (k * n)) (k * n) = k

instance (n k : ℕ) : Decidable (IsValidA352834 n k) := by
  unfold IsValidA352834
  infer_instance

/-- OEIS A352834: least `k > 0` with `gcd(τ(kn), kn) = k`, or `0` if none exists. -/
noncomputable def a352834 (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, IsValidA352834 n k then Nat.find h else 0

/-- Equivalence with the OEIS rational-denominator definition: for `n > 0` and `k > 0`,
`((τ(kn) : ℚ) / (kn : ℚ)).den = n ↔ IsValidA352834 n k`. -/
theorem IsValidA352834_iff_den (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    ((tau (k * n) : ℚ) / (k * n : ℚ)).den = n ↔ IsValidA352834 n k := by
  set m := k * n
  have hm : 0 < m := mul_pos hk hn
  set g := Nat.gcd (tau m) m
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right (tau m) hm
  have hg_dvd_t : g ∣ tau m := Nat.gcd_dvd_left (tau m) m
  have hg_dvd_m : g ∣ m := Nat.gcd_dvd_right (tau m) m
  set a := tau m / g
  set b := m / g
  have hb_pos : 0 < b := Nat.div_pos (Nat.le_of_dvd hm hg_dvd_m) hg_pos
  have hcop : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd hg_pos
  have hrat : (tau m : ℚ) / (m : ℚ) = (a : ℚ) / (b : ℚ) := by
    have h1n : tau m = a * g := (Nat.div_mul_cancel hg_dvd_t).symm
    have h2n : m = b * g := (Nat.div_mul_cancel hg_dvd_m).symm
    have h1 : (tau m : ℚ) = (a : ℚ) * (g : ℚ) := by exact_mod_cast h1n
    have h2 : (m : ℚ) = (b : ℚ) * (g : ℚ) := by exact_mod_cast h2n
    have hg0 : (g : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hg_pos.ne'
    rw [h1, h2, mul_div_mul_right _ _ hg0]
  have hden : ((tau m : ℚ) / (m : ℚ)).den = b := by
    have hcopz : ((a : ℤ).natAbs).Coprime ((b : ℤ).natAbs) := by simpa using hcop
    have hdz := Rat.den_div_eq_of_coprime (Int.natCast_pos.mpr hb_pos) hcopz
    have hdz_nat : ((a : ℚ) / (b : ℚ)).den = b := by
      have h1 : (((a : ℤ) : ℚ) / ((b : ℤ) : ℚ)).den = (b : ℤ).toNat := by
        exact_mod_cast congrArg Int.toNat hdz
      simpa using h1
    exact (congrArg Rat.den hrat).trans hdz_nat
  have hden' : ((tau (k * n) : ℚ) / (k * n : ℚ)).den = b := by
    simpa [m, Nat.cast_mul] using hden
  rw [hden']
  constructor
  · intro hbn
    refine ⟨hk, ?_⟩
    have hm1 : b * g = m := Nat.div_mul_cancel hg_dvd_m
    rw [hbn] at hm1
    have hkm : k * n = g * n := by simpa [m, mul_comm] using hm1.symm
    exact (Nat.mul_right_cancel hn hkm).symm
  · rintro ⟨_, hgk⟩
    dsimp only [b, m, g]
    rw [hgk]
    exact Nat.mul_div_cancel_left n hk

lemma a352834_le_of_valid {n j : ℕ} (hj : IsValidA352834 n j) : a352834 n ≤ j := by
  classical
  have hex : ∃ k, IsValidA352834 n k := ⟨j, hj⟩
  rw [a352834, dif_pos hex]
  exact Nat.find_min' hex hj

lemma a352834_spec_of_pos {n : ℕ} (hk : 0 < a352834 n) :
    IsValidA352834 n (a352834 n) := by
  classical
  by_cases hex : ∃ k, IsValidA352834 n k
  · rw [a352834, dif_pos hex]
    exact Nat.find_spec hex
  · exfalso
    rw [a352834, dif_neg hex] at hk
    omega

lemma tau_pos {m : ℕ} (hm : 0 < m) : 0 < tau m :=
  Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd m, hm.ne'⟩⟩

lemma a352834_dvd_tau {n : ℕ} (hk : 0 < a352834 n) :
    a352834 n ∣ tau (a352834 n * n) := by
  have h := (a352834_spec_of_pos hk).2
  have hd := Nat.gcd_dvd_left (tau (a352834 n * n)) (a352834 n * n)
  rw [h] at hd
  exact hd

lemma a352834_le_tau {n : ℕ} (hn : 1 ≤ n) (hk : 0 < a352834 n) :
    a352834 n ≤ tau (a352834 n * n) :=
  Nat.le_of_dvd (tau_pos (Nat.mul_pos hk hn)) (a352834_dvd_tau hk)

/-! ## Part 1a: Explicit Elementary Divisor Bound and `a(n) = O_ε(n^ε)` -/

section Asymptotic

private lemma nat_add_one_le_two_pow (e : ℕ) : (e : ℝ) + 1 ≤ (2 : ℝ) ^ e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    have h1 : (e : ℝ) + 1 + 1 ≤ 2 * ((e : ℝ) + 1) := by
      have : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg e
      linarith
    calc
      ((e + 1 : ℕ) : ℝ) + 1 = (e : ℝ) + 1 + 1 := by push_cast; ring
      _ ≤ 2 * ((e : ℝ) + 1) := h1
      _ ≤ 2 * (2 : ℝ) ^ e := by linarith
      _ = (2 : ℝ) ^ (e + 1) := by ring

private lemma rpow_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) (z : ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, f i) ^ z = ∏ i ∈ s, (f i) ^ z := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hprod_nn : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hfs
    rw [Finset.prod_insert ha, Real.mul_rpow hfa hprod_nn, ih hfs, Finset.prod_insert ha]

private lemma real_prod_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfgs : ∀ i ∈ s, f i ≤ g i := fun i hi => hfg i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul (hfg a (Finset.mem_insert_self a s)) (ih hfs hfgs)
      (Finset.prod_nonneg hfs) (le_trans hfa (hfg a (Finset.mem_insert_self a s)))

/-- Explicit divisor bound: for any `δ > 0`, there exists `C > 0` such that
`τ(m) ≤ C * m ^ δ` for all `m ≥ 1`. -/
theorem divisor_bound_explicit (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → (tau m : ℝ) ≤ C * (m : ℝ) ^ δ := by
  let η : ℝ := (2 : ℝ) ^ δ - 1
  have h2gt1 : (1 : ℝ) < (2 : ℝ) ^ δ := Real.one_lt_rpow (by norm_num) hδ
  have hη : 0 < η := sub_pos.mpr h2gt1
  let C₀ : ℝ := 1 + 1 / η
  have hC₀_gt1 : 1 < C₀ := by
    dsimp [C₀]
    have : 0 < 1 / η := one_div_pos.mpr hη
    linarith
  have hC₀_pos : 0 < C₀ := by linarith
  let N : ℕ := Nat.floor ((2 : ℝ) ^ (1 / δ))
  refine ⟨C₀ ^ (N + 1), pow_pos hC₀_pos _, fun m hm => ?_⟩
  have hm0 : m ≠ 0 := by omega
  have htau : (tau m : ℝ) = ∏ p ∈ m.primeFactors, ((m.factorization p : ℝ) + 1) := by
    unfold tau
    rw [Nat.card_divisors hm0]
    push_cast
    rfl
  have hm_eq_nat := Nat.prod_primeFactors_pow_factorization hm0
  have hm_eq : (m : ℝ) = ∏ p ∈ m.primeFactors, (p : ℝ) ^ (m.factorization p) := by
    conv_lhs => rw [hm_eq_nat]
    push_cast
    rfl
  have hm_rpow : (m : ℝ) ^ δ = ∏ p ∈ m.primeFactors, (p : ℝ) ^ (δ * (m.factorization p : ℝ)) := by
    rw [hm_eq, rpow_finset_prod m.primeFactors _ δ (fun p _ => pow_nonneg (Nat.cast_nonneg p) _)]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← Real.rpow_natCast (p : ℝ) (m.factorization p),
      ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm]
  have h_large : ∀ p ∈ m.primeFactors, N < p →
      ((m.factorization p : ℝ) + 1) ≤ (p : ℝ) ^ (δ * (m.factorization p : ℝ)) := by
    intro p _ hpN
    have h2_lt_p : (2 : ℝ) ^ (1 / δ) < (p : ℝ) :=
      (Nat.floor_lt (Real.rpow_nonneg (by norm_num) _)).mp hpN
    have h2_le_pδ : (2 : ℝ) ≤ (p : ℝ) ^ δ := by
      have htmp : ((2 : ℝ) ^ (1 / δ)) ^ δ ≤ (p : ℝ) ^ δ :=
        Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) h2_lt_p.le hδ.le
      rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ.ne', Real.rpow_one] at htmp
    calc
      ((m.factorization p : ℝ) + 1) ≤ (2 : ℝ) ^ (m.factorization p) :=
        nat_add_one_le_two_pow _
      _ ≤ ((p : ℝ) ^ δ) ^ (m.factorization p) :=
        pow_le_pow_left₀ (by norm_num) h2_le_pδ _
      _ = (p : ℝ) ^ (δ * (m.factorization p : ℝ)) := by
        rw [← Real.rpow_natCast ((p : ℝ) ^ δ), ← Real.rpow_mul (Nat.cast_nonneg p)]
  have h_all : ∀ p ∈ m.primeFactors,
      ((m.factorization p : ℝ) + 1) ≤ C₀ * (p : ℝ) ^ (δ * (m.factorization p : ℝ)) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have h1η_le : 1 + η ≤ (p : ℝ) ^ δ := by
      have : 1 + η = (2 : ℝ) ^ δ := by dsimp [η]; ring
      rw [this]
      exact Real.rpow_le_rpow (by norm_num) hp2 hδ.le
    have hbern : 1 + (m.factorization p : ℝ) * η ≤ (1 + η) ^ (m.factorization p) :=
      one_add_mul_le_pow (by linarith) _
    have h_step : ((m.factorization p : ℝ) + 1) ≤
        C₀ * (1 + (m.factorization p : ℝ) * η) := by
      have hne : η ≠ 0 := hη.ne'
      have he0 : 0 ≤ (m.factorization p : ℝ) := Nat.cast_nonneg _
      have hdiff : C₀ * (1 + (m.factorization p : ℝ) * η) - ((m.factorization p : ℝ) + 1) =
          (m.factorization p : ℝ) * η + 1 / η := by
        dsimp [C₀]
        field_simp
        ring
      have hnonneg : 0 ≤ (m.factorization p : ℝ) * η + 1 / η :=
        add_nonneg (mul_nonneg he0 hη.le) (one_div_nonneg.mpr hη.le)
      linarith
    calc
      ((m.factorization p : ℝ) + 1)
          ≤ C₀ * (1 + (m.factorization p : ℝ) * η) := h_step
      _ ≤ C₀ * (1 + η) ^ (m.factorization p) :=
          mul_le_mul_of_nonneg_left hbern hC₀_pos.le
      _ ≤ C₀ * ((p : ℝ) ^ δ) ^ (m.factorization p) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h1η_le _) hC₀_pos.le
      _ = C₀ * (p : ℝ) ^ (δ * (m.factorization p : ℝ)) := by
          rw [← Real.rpow_natCast ((p : ℝ) ^ δ), ← Real.rpow_mul (Nat.cast_nonneg p)]
  let S₁ := m.primeFactors.filter (· ≤ N)
  let S₂ := m.primeFactors.filter (fun p => ¬ p ≤ N)
  have hS₁ : (∏ p ∈ S₁, ((m.factorization p : ℝ) + 1)) ≤
      C₀ ^ S₁.card * ∏ p ∈ S₁, (p : ℝ) ^ (δ * (m.factorization p : ℝ)) := by
    calc
      (∏ p ∈ S₁, ((m.factorization p : ℝ) + 1))
          ≤ ∏ p ∈ S₁, (C₀ * (p : ℝ) ^ (δ * (m.factorization p : ℝ))) :=
            real_prod_le_prod S₁ _ _ (fun _ _ => by positivity)
              fun p hp => h_all p (Finset.filter_subset _ _ hp)
      _ = C₀ ^ S₁.card * ∏ p ∈ S₁, (p : ℝ) ^ (δ * (m.factorization p : ℝ)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hS₂ : (∏ p ∈ S₂, ((m.factorization p : ℝ) + 1)) ≤
      ∏ p ∈ S₂, (p : ℝ) ^ (δ * (m.factorization p : ℝ)) := by
    refine real_prod_le_prod S₂ _ _ (fun _ _ => by positivity) fun p hp => ?_
    rw [Finset.mem_filter] at hp
    exact h_large p hp.1 (Nat.lt_of_not_le hp.2)
  have hcard : S₁.card ≤ N + 1 := by
    calc
      S₁.card ≤ (Finset.range (N + 1)).card := by
        refine Finset.card_le_card fun p hp => ?_
        rw [Finset.mem_filter] at hp
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le hp.2)
      _ = N + 1 := Finset.card_range _
  have hpowC : C₀ ^ S₁.card ≤ C₀ ^ (N + 1) :=
    pow_le_pow_right₀ hC₀_gt1.le hcard
  rw [htau, hm_rpow]
  rw [← Finset.prod_filter_mul_prod_filter_not m.primeFactors (· ≤ N)]
  rw [← Finset.prod_filter_mul_prod_filter_not m.primeFactors (· ≤ N)
    (fun p => (p : ℝ) ^ (δ * (m.factorization p : ℝ)))]
  calc
    (∏ p ∈ S₁, ((m.factorization p : ℝ) + 1)) * (∏ p ∈ S₂, ((m.factorization p : ℝ) + 1))
        ≤ (C₀ ^ S₁.card * ∏ p ∈ S₁, (p : ℝ) ^ (δ * (m.factorization p : ℝ))) *
            (∏ p ∈ S₂, (p : ℝ) ^ (δ * (m.factorization p : ℝ))) :=
          mul_le_mul hS₁ hS₂ (Finset.prod_nonneg fun _ _ => by positivity)
            (mul_nonneg (pow_nonneg hC₀_pos.le _) (Finset.prod_nonneg fun _ _ => by positivity))
    _ = C₀ ^ S₁.card *
          ((∏ p ∈ S₁, (p : ℝ) ^ (δ * (m.factorization p : ℝ))) *
           (∏ p ∈ S₂, (p : ℝ) ^ (δ * (m.factorization p : ℝ)))) := by ring
    _ ≤ C₀ ^ (N + 1) *
          ((∏ p ∈ S₁, (p : ℝ) ^ (δ * (m.factorization p : ℝ))) *
           (∏ p ∈ S₂, (p : ℝ) ^ (δ * (m.factorization p : ℝ)))) := by
          refine mul_le_mul_of_nonneg_right hpowC ?_
          exact mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
            (Finset.prod_nonneg fun _ _ => by positivity)

/-- Subpolynomial growth for OEIS A352834: for every `ε > 0`, `a(n) = O_ε(n^ε)`. -/
theorem a352834_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (a352834 n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let δ : ℝ := ε / (1 + ε)
  have hδ_pos : 0 < δ := div_pos hε (by linarith)
  have hδ_lt1 : δ < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have h1mδ : 0 < 1 - δ := sub_pos.mpr hδ_lt1
  have hexp : 1 / (1 - δ) = 1 + ε := by
    dsimp [δ]
    field_simp
    ring
  have hδε : δ / (1 - δ) = ε := by
    dsimp [δ]
    field_simp
    ring
  obtain ⟨Cδ, hCδ_pos, hbound⟩ := divisor_bound_explicit δ hδ_pos
  refine ⟨Cδ ^ (1 + ε), Real.rpow_pos_of_pos hCδ_pos _, fun n hn => ?_⟩
  by_cases hk0 : a352834 n = 0
  · rw [hk0, Nat.cast_zero]
    exact mul_nonneg (Real.rpow_nonneg hCδ_pos.le _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · have hk_pos : 0 < a352834 n := Nat.pos_of_ne_zero hk0
    have hle_tau : (a352834 n : ℝ) ≤ (tau (a352834 n * n) : ℝ) := by
      exact_mod_cast a352834_le_tau hn hk_pos
    have hm1 : 1 ≤ a352834 n * n := Nat.succ_le_of_lt (Nat.mul_pos hk_pos hn)
    have htau_bd := hbound (a352834 n * n) hm1
    have hk_r_pos : (0 : ℝ) < (a352834 n : ℝ) := Nat.cast_pos.mpr hk_pos
    have hn_r_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hmul_rpow : ((a352834 n * n : ℕ) : ℝ) ^ δ =
        (a352834 n : ℝ) ^ δ * (n : ℝ) ^ δ := by
      push_cast
      exact Real.mul_rpow hk_r_pos.le hn_r_pos.le
    rw [hmul_rpow] at htau_bd
    have h1 : (a352834 n : ℝ) ≤ Cδ * (a352834 n : ℝ) ^ δ * (n : ℝ) ^ δ := by
      linarith
    have hkδ_pos : 0 < (a352834 n : ℝ) ^ δ := Real.rpow_pos_of_pos hk_r_pos δ
    have hsplit : (a352834 n : ℝ) = (a352834 n : ℝ) ^ (1 - δ) * (a352834 n : ℝ) ^ δ := by
      rw [← Real.rpow_add hk_r_pos, sub_add_cancel, Real.rpow_one]
    have h2 : (a352834 n : ℝ) ^ (1 - δ) ≤ Cδ * (n : ℝ) ^ δ := by
      rw [hsplit] at h1
      have h1' : (a352834 n : ℝ) ^ (1 - δ) * (a352834 n : ℝ) ^ δ ≤
          (Cδ * (n : ℝ) ^ δ) * (a352834 n : ℝ) ^ δ := by linarith
      exact le_of_mul_le_mul_right h1' hkδ_pos
    have h3 : ((a352834 n : ℝ) ^ (1 - δ)) ^ (1 / (1 - δ)) ≤
        (Cδ * (n : ℝ) ^ δ) ^ (1 / (1 - δ)) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hk_r_pos.le _) h2 (one_div_nonneg.mpr h1mδ.le)
    rw [← Real.rpow_mul hk_r_pos.le, mul_one_div_cancel h1mδ.ne', Real.rpow_one] at h3
    have h4 : (Cδ * (n : ℝ) ^ δ) ^ (1 / (1 - δ)) =
        Cδ ^ (1 + ε) * (n : ℝ) ^ (δ * (1 + ε)) := by
      rw [Real.mul_rpow hCδ_pos.le (Real.rpow_nonneg hn_r_pos.le _),
        ← Real.rpow_mul hn_r_pos.le, hexp]
    have h5 : δ * (1 + ε) = ε := by
      rw [← hexp, mul_one_div, hδε]
    rw [h4, h5] at h3
    exact h3

end Asymptotic

/-! ## Part 1b: Exact Global Maximum at `(n, a(n)) = (154440, 840)` -/

section GlobalExtremum

/-- Per-prime score `h_p(e) = (e + 1)^4 / p^e`. -/
def h_score (p e : ℕ) : ℚ := ((e + 1 : ℚ) ^ 4) / (p : ℚ) ^ e

/-- Global score `H(m) = τ(m)^4 / m`. -/
def H_score (m : ℕ) : ℚ := ((tau m : ℚ) ^ 4) / (m : ℚ)

/-- Target threshold `T = 840^3 / 154440 = 548800 / 143`. -/
def T_val : ℚ := (840 : ℚ) ^ 3 / 154440

/-- Global product bound `B = ∏_{p ≤ 13} M_p = 127401984 / 25025`. -/
def B_val : ℚ :=
  h_score 2 5 * h_score 3 3 * h_score 5 2 * h_score 7 1 * h_score 11 1 * h_score 13 1

lemma h_score_nonneg (p e : ℕ) : 0 ≤ h_score p e := by
  unfold h_score
  positivity

lemma h_score_zero (p : ℕ) : h_score p 0 = 1 := by
  simp [h_score]

lemma H_score_eq_prod {m : ℕ} (hm : 1 ≤ m) :
    H_score m = ∏ p ∈ m.primeFactors, h_score p (m.factorization p) := by
  have hm0 : m ≠ 0 := by omega
  unfold H_score tau h_score
  have hcard : (Nat.divisors m).card = ∏ x ∈ m.primeFactors, (m.factorization x + 1) :=
    Nat.card_divisors hm0
  have hm_eq_nat := Nat.prod_primeFactors_pow_factorization hm0
  have hm_q : (m : ℚ) = ∏ p ∈ m.primeFactors, (p : ℚ) ^ (m.factorization p) := by
    conv_lhs => rw [hm_eq_nat]
    push_cast
    rfl
  have htau_q : ((Nat.divisors m).card : ℚ) ^ 4 =
      ∏ p ∈ m.primeFactors, ((m.factorization p : ℚ) + 1) ^ 4 := by
    rw [hcard]
    push_cast
    rw [Finset.prod_pow]
  rw [htau_q, hm_q, Finset.prod_div_distrib]

lemma h_score_step {p e : ℕ} (hp : 0 < p) (hstep : (e + 2) ^ 4 ≤ p * (e + 1) ^ 4) :
    h_score p (e + 1) ≤ h_score p e := by
  unfold h_score
  have hpq : (0 : ℚ) < (p : ℚ) := Nat.cast_pos.mpr hp
  have hpow1 : (0 : ℚ) < (p : ℚ) ^ (e + 1) := pow_pos hpq (e + 1)
  have hpow0 : (0 : ℚ) < (p : ℚ) ^ e := pow_pos hpq e
  rw [div_le_div_iff₀ hpow1 hpow0]
  have hstep_q : ((e : ℚ) + 2) ^ 4 ≤ (p : ℚ) * ((e : ℚ) + 1) ^ 4 := by exact_mod_cast hstep
  have hcast : (((e + 1 : ℕ) : ℚ) + 1) ^ 4 = ((e : ℚ) + 2) ^ 4 := by
    have : (((e + 1 : ℕ) : ℚ) + 1) = (e : ℚ) + 2 := by push_cast; ring
    rw [this]
  rw [hcast]
  have hmul := mul_le_mul_of_nonneg_right hstep_q hpow0.le
  have hrhs : (p : ℚ) * ((e : ℚ) + 1) ^ 4 * (p : ℚ) ^ e =
      ((e : ℚ) + 1) ^ 4 * (p : ℚ) ^ (e + 1) := by
    rw [pow_succ]; ring
  exact le_trans hmul (le_of_eq hrhs)

lemma h_score_antitone_from {p e₀ : ℕ} (hp : 0 < p)
    (hstep : (e₀ + 2) ^ 4 ≤ p * (e₀ + 1) ^ 4) :
    ∀ e : ℕ, e₀ ≤ e → h_score p e ≤ h_score p e₀ := by
  have h_all : ∀ k : ℕ, (e₀ + k + 2) ^ 4 ≤ p * (e₀ + k + 1) ^ 4 := by
    intro k
    have hmul : (e₀ + k + 2) * (e₀ + 1) ≤ (e₀ + k + 1) * (e₀ + 2) := by nlinarith
    have hpow4 : ((e₀ + k + 2) * (e₀ + 1)) ^ 4 ≤ ((e₀ + k + 1) * (e₀ + 2)) ^ 4 :=
      Nat.pow_le_pow_left hmul 4
    have hlhs : (e₀ + k + 2) ^ 4 * (e₀ + 1) ^ 4 = ((e₀ + k + 2) * (e₀ + 1)) ^ 4 := by ring
    have hrhs : (e₀ + k + 1) ^ 4 * (e₀ + 2) ^ 4 = ((e₀ + k + 1) * (e₀ + 2)) ^ 4 := by ring
    have hpow4' : (e₀ + k + 2) ^ 4 * (e₀ + 1) ^ 4 ≤ (e₀ + k + 1) ^ 4 * (e₀ + 2) ^ 4 := by
      rw [hlhs, hrhs]; exact hpow4
    have hmul_p : (e₀ + k + 2) ^ 4 * (e₀ + 1) ^ 4 ≤ (p * (e₀ + k + 1) ^ 4) * (e₀ + 1) ^ 4 := by
      calc
        (e₀ + k + 2) ^ 4 * (e₀ + 1) ^ 4
            ≤ (e₀ + k + 1) ^ 4 * (e₀ + 2) ^ 4 := hpow4'
        _ ≤ (e₀ + k + 1) ^ 4 * (p * (e₀ + 1) ^ 4) :=
            Nat.mul_le_mul_left _ hstep
        _ = (p * (e₀ + k + 1) ^ 4) * (e₀ + 1) ^ 4 := by ring
    exact Nat.le_of_mul_le_mul_right hmul_p (by positivity)
  intro e he
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      h_score p (e₀ + (k + 1)) = h_score p (e₀ + k + 1) := by ring_nf
      _ ≤ h_score p (e₀ + k) := h_score_step hp (h_all k)
      _ ≤ h_score p e₀ := ih (Nat.le_add_right e₀ k)

lemma h_score_le_one_of_ge_17 {p : ℕ} (hp : 17 ≤ p) (e : ℕ) : h_score p e ≤ 1 := by
  have h := h_score_antitone_from (by omega : 0 < p) (by nlinarith : (0 + 2) ^ 4 ≤ p * (0 + 1) ^ 4)
    e (Nat.zero_le e)
  simpa [h_score_zero] using h

lemma h_score_le_16_div_23 {p : ℕ} (hp : 23 ≤ p) {e : ℕ} (he : 1 ≤ e) :
    h_score p e ≤ 16 / 23 := by
  have h := h_score_antitone_from (by omega : 0 < p) (by nlinarith : (1 + 2) ^ 4 ≤ p * (1 + 1) ^ 4)
    e he
  have h1 : h_score p 1 ≤ 16 / 23 := by
    unfold h_score
    have hpq : (23 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    have h16 : (((1 : ℕ) : ℚ) + 1) ^ 4 / (p : ℚ) ^ 1 = 16 / (p : ℚ) := by norm_num
    rw [h16]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpq
  exact le_trans h h1

lemma h_score_2_le (e : ℕ) : h_score 2 e ≤ h_score 2 5 := by
  rcases le_or_gt 5 e with he | he
  · exact h_score_antitone_from (by norm_num) (by norm_num) e he
  · interval_cases e <;> norm_num [h_score]

lemma h_score_3_le (e : ℕ) : h_score 3 e ≤ h_score 3 3 := by
  rcases le_or_gt 3 e with he | he
  · exact h_score_antitone_from (by norm_num) (by norm_num) e he
  · interval_cases e <;> norm_num [h_score]

lemma h_score_5_le (e : ℕ) : h_score 5 e ≤ h_score 5 2 := by
  rcases le_or_gt 2 e with he | he
  · exact h_score_antitone_from (by norm_num) (by norm_num) e he
  · interval_cases e <;> norm_num [h_score]

lemma h_score_7_le (e : ℕ) : h_score 7 e ≤ h_score 7 1 := by
  rcases le_or_gt 1 e with he | he
  · exact h_score_antitone_from (by norm_num) (by norm_num) e he
  · interval_cases e <;> norm_num [h_score]

lemma h_score_11_le (e : ℕ) : h_score 11 e ≤ h_score 11 1 := by
  rcases le_or_gt 1 e with he | he
  · exact h_score_antitone_from (by norm_num) (by norm_num) e he
  · interval_cases e <;> norm_num [h_score]

lemma h_score_13_le (e : ℕ) : h_score 13 e ≤ h_score 13 1 := by
  rcases le_or_gt 1 e with he | he
  · exact h_score_antitone_from (by norm_num) (by norm_num) e he
  · interval_cases e <;> norm_num [h_score]

private def smallPrimes6 : Finset ℕ := {2, 3, 5, 7, 11, 13}

private def maxPrime6 (p : ℕ) : ℚ :=
  if p = 2 then h_score 2 5
  else if p = 3 then h_score 3 3
  else if p = 5 then h_score 5 2
  else if p = 7 then h_score 7 1
  else if p = 11 then h_score 11 1
  else if p = 13 then h_score 13 1
  else 1

private lemma prod_smallPrimes6 : ∏ p ∈ smallPrimes6, maxPrime6 p = B_val := by
  unfold smallPrimes6 maxPrime6 B_val h_score
  norm_num

private lemma one_le_maxPrime6 (p : ℕ) : 1 ≤ maxPrime6 p := by
  unfold maxPrime6 h_score
  split_ifs <;> norm_num

private lemma h_score_le_maxPrime6 (p e : ℕ) (hp : p.Prime) :
    h_score p e ≤ maxPrime6 p := by
  unfold maxPrime6
  split_ifs with h2 h3 h5 h7 h11 h13
  · subst h2; exact h_score_2_le e
  · subst h3; exact h_score_3_le e
  · subst h5; exact h_score_5_le e
  · subst h7; exact h_score_7_le e
  · subst h11; exact h_score_11_le e
  · subst h13; exact h_score_13_le e
  · have hp17 : 17 ≤ p := by
      have hp2 := hp.two_le
      by_contra hlt
      have hp16 : p ≤ 16 := by omega
      interval_cases p <;> simp_all <;> norm_num at hp
    exact h_score_le_one_of_ge_17 hp17 e

private lemma factorization_eq_zero_of_notMem {m p : ℕ} (hm0 : m ≠ 0) (hp : p ∉ m.primeFactors) :
    m.factorization p = 0 := by
  by_cases hrp : p.Prime
  · have hnd : ¬ p ∣ m := fun h => hp (Nat.mem_primeFactors.mpr ⟨hrp, h, hm0⟩)
    exact Nat.factorization_eq_zero_of_not_dvd hnd
  · exact Nat.factorization_eq_zero_of_not_prime m hrp

private lemma rat_prod_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℚ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfgs : ∀ i ∈ s, f i ≤ g i := fun i hi => hfg i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul (hfg a (Finset.mem_insert_self a s)) (ih hfs hfgs)
      (Finset.prod_nonneg hfs) (le_trans hfa (hfg a (Finset.mem_insert_self a s)))

private lemma rat_prod_ge_one {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    nlinarith

/-- Global bound `H(m) ≤ B_val` for every `m ≥ 1`, and if `q` is prime
then `H(m) ≤ h_score q (m.factorization q) * (B_val / maxPrime6 q)`. -/
lemma H_score_le_insert {m q : ℕ} (hm : 1 ≤ m) (hq : q.Prime) :
    H_score m ≤ h_score q (m.factorization q) * (B_val / maxPrime6 q) := by
  have hm0 : m ≠ 0 := by omega
  rw [H_score_eq_prod hm]
  let S := m.primeFactors ∪ (smallPrimes6 ∪ {q})
  have hS_sub : m.primeFactors ⊆ S := Finset.subset_union_left
  have hS_eq : (∏ p ∈ m.primeFactors, h_score p (m.factorization p)) =
      ∏ p ∈ S, h_score p (m.factorization p) := by
    refine Finset.prod_subset hS_sub fun p _ hp_not => ?_
    rw [factorization_eq_zero_of_notMem hm0 hp_not, h_score_zero]
  rw [hS_eq]
  have hqS : q ∈ S := Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_singleton_self q))
  rw [← Finset.mul_prod_erase S (fun p => h_score p (m.factorization p)) hqS]
  refine mul_le_mul_of_nonneg_left ?_ (h_score_nonneg _ _)
  have hprod_le : (∏ p ∈ S.erase q, h_score p (m.factorization p)) ≤
      ∏ p ∈ S.erase q, maxPrime6 p := by
    refine rat_prod_le_prod (S.erase q) _ _ (fun _ _ => h_score_nonneg _ _) fun p hp => ?_
    by_cases hpm : p ∈ m.primeFactors
    · exact h_score_le_maxPrime6 p _ (Nat.prime_of_mem_primeFactors hpm)
    · rw [factorization_eq_zero_of_notMem hm0 hpm, h_score_zero]
      exact one_le_maxPrime6 p
  have h_erase_le : (∏ p ∈ S.erase q, maxPrime6 p) ≤ B_val / maxPrime6 q := by
    have hq_pos : 0 < maxPrime6 q := by linarith [one_le_maxPrime6 q]
    rw [le_div_iff₀ hq_pos, Finset.prod_erase_mul S maxPrime6 hqS]
    have h6S : smallPrimes6 ⊆ S := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_right
    have h1 : B_val = ∏ p ∈ smallPrimes6, maxPrime6 p := prod_smallPrimes6.symm
    rw [h1, ← Finset.prod_sdiff h6S]
    have hsdiff_eq : ∏ p ∈ S \ smallPrimes6, maxPrime6 p = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      have hp_not : p ∉ smallPrimes6 := (Finset.mem_sdiff.mp hp).2
      simp only [smallPrimes6, Finset.mem_insert, Finset.mem_singleton, not_or] at hp_not
      rcases hp_not with ⟨h2, h3, h5, h7, h11, h13⟩
      simp [maxPrime6, h2, h3, h5, h7, h11, h13]
    rw [hsdiff_eq, one_mul]
  exact le_trans hprod_le h_erase_le

lemma H_score_le_bound {m : ℕ} (hm : 1 ≤ m) : H_score m ≤ B_val := by
  have h := H_score_le_insert hm Nat.prime_two
  have h2 : h_score 2 (m.factorization 2) ≤ maxPrime6 2 := h_score_le_maxPrime6 2 _ Nat.prime_two
  have h2pos : 0 < maxPrime6 2 := by linarith [one_le_maxPrime6 2]
  have hBnonneg : 0 ≤ B_val := by unfold B_val h_score; positivity
  calc
    H_score m ≤ h_score 2 (m.factorization 2) * (B_val / maxPrime6 2) := h
    _ ≤ maxPrime6 2 * (B_val / maxPrime6 2) :=
        mul_le_mul_of_nonneg_right h2 (div_nonneg hBnonneg h2pos.le)
    _ = B_val := mul_div_cancel₀ _ h2pos.ne'

/-- If `n ≥ 1` and `T_val ≤ (a352834 n)^3 / n`, then `k = τ(kn)`, `τ(kn) ∣ kn`,
every prime factor of `kn` is `≤ 19`, and its exponents lie in the 240-tuple box. -/
lemma candidate_constraints {n : ℕ} (hn : 1 ≤ n)
    (hge : T_val ≤ ((a352834 n : ℚ) ^ 3) / (n : ℚ)) :
    let k := a352834 n
    let m := k * n
    0 < k ∧ k = tau m ∧ tau m ∣ m ∧
      (∀ p ∈ m.primeFactors, p ∈ ({2, 3, 5, 7, 11, 13, 17, 19} : Finset ℕ)) ∧
      m.factorization 2 ∈ Finset.Icc 3 7 ∧
      m.factorization 3 ∈ Finset.Icc 2 4 ∧
      m.factorization 5 ∈ Finset.Icc 1 2 ∧
      m.factorization 7 = 1 ∧
      m.factorization 11 = 1 ∧
      m.factorization 13 ≤ 1 ∧
      m.factorization 17 ≤ 1 ∧
      m.factorization 19 ≤ 1 := by
  intro k m
  have hT_pos : (0 : ℚ) < T_val := by unfold T_val; norm_num
  have hk_pos : 0 < k := by
    by_contra hk0
    have hk_eq : k = 0 := by omega
    rw [show (a352834 n : ℚ) = 0 by exact_mod_cast hk_eq] at hge
    simp at hge
    linarith
  have hm_lt : 0 < m := Nat.mul_pos hk_pos hn
  have hm_pos : 1 ≤ m := Nat.succ_le_of_lt hm_lt
  have hspec := a352834_spec_of_pos hk_pos
  have hkdvd_tau : k ∣ tau m := by
    have hd := Nat.gcd_dvd_left (tau m) m
    rw [hspec.2] at hd
    exact hd
  have hkdvd_m : k ∣ m := ⟨n, rfl⟩
  have hratio : ((k : ℚ) ^ 3) / (n : ℚ) = ((k : ℚ) ^ 4) / (m : ℚ) := by
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk_pos.ne'
    have hm_cast : (m : ℚ) = (k : ℚ) * (n : ℚ) := by
      show ((k * n : ℕ) : ℚ) = (k : ℚ) * (n : ℚ)
      push_cast
      rfl
    rw [hm_cast]
    field_simp
  have hk_eq_tau : k = tau m := by
    by_contra hne
    have hlt : k < tau m := lt_of_le_of_ne (a352834_le_tau hn hk_pos) hne
    rcases hkdvd_tau with ⟨q, hq⟩
    have hq2 : 2 ≤ q := by
      have : k * 1 < k * q := by simpa [← hq] using hlt
      exact Nat.lt_of_mul_lt_mul_left this
    have h2k : 2 * k ≤ tau m := by rw [hq, mul_comm]; exact Nat.mul_le_mul_left k hq2
    have h2kq : (2 : ℚ) * (k : ℚ) ≤ (tau m : ℚ) := by exact_mod_cast h2k
    have h16 : 16 * ((k : ℚ) ^ 4 / (m : ℚ)) ≤ H_score m := by
      unfold H_score
      have hm0 : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm_pos
      have hnum : 16 * (k : ℚ) ^ 4 ≤ (tau m : ℚ) ^ 4 := by
        calc
          16 * (k : ℚ) ^ 4 = ((2 : ℚ) * (k : ℚ)) ^ 4 := by ring
          _ ≤ (tau m : ℚ) ^ 4 := pow_le_pow_left₀ (by positivity) h2kq 4
      calc
        16 * ((k : ℚ) ^ 4 / (m : ℚ)) = (16 * (k : ℚ) ^ 4) / (m : ℚ) := by ring
        _ ≤ (tau m : ℚ) ^ 4 / (m : ℚ) := div_le_div_of_nonneg_right hnum hm0.le
    have hB16 : B_val / 16 < T_val := by unfold B_val T_val h_score; norm_num
    have hHB := H_score_le_bound hm_pos
    rw [hratio] at hge
    linarith
  have hH_ge : T_val ≤ H_score m := by
    unfold H_score
    rw [← hk_eq_tau, ← hratio]
    exact hge
  have htau_dvd : tau m ∣ m := hk_eq_tau ▸ hkdvd_m
  have hpf : ∀ p ∈ m.primeFactors, p ∈ ({2, 3, 5, 7, 11, 13, 17, 19} : Finset ℕ) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    by_contra hnot
    have hp23 : 23 ≤ p := by
      have hp2 := hprime.two_le
      by_contra hlt
      have hp22 : p ≤ 22 := by omega
      interval_cases p <;> simp_all <;> norm_num at hprime
    have he1 : 1 ≤ m.factorization p := Nat.Prime.factorization_pos_of_dvd hprime hm_lt.ne'
      (Nat.dvd_of_mem_primeFactors hp)
    have hbound_p := H_score_le_insert hm_pos hprime
    have h16_23 := h_score_le_16_div_23 hp23 he1
    have hmp : maxPrime6 p = 1 := by
      unfold maxPrime6
      have hne2 : p ≠ 2 := by omega
      have hne3 : p ≠ 3 := by omega
      have hne5 : p ≠ 5 := by omega
      have hne7 : p ≠ 7 := by omega
      have hne11 : p ≠ 11 := by omega
      have hne13 : p ≠ 13 := by omega
      simp [hne2, hne3, hne5, hne7, hne11, hne13]
    rw [hmp, div_one] at hbound_p
    have hB23 : (16 / 23 : ℚ) * B_val < T_val := by unfold B_val T_val h_score; norm_num
    have hBnn : 0 ≤ B_val := by unfold B_val h_score; positivity
    have : H_score m ≤ (16 / 23 : ℚ) * B_val :=
      le_trans hbound_p (mul_le_mul_of_nonneg_right h16_23 hBnn)
    linarith
  have hexp_bd : ∀ q : ℕ, q.Prime →
      T_val ≤ h_score q (m.factorization q) * (B_val / maxPrime6 q) := fun q hq =>
    le_trans hH_ge (H_score_le_insert hm_pos hq)
  have he2 : m.factorization 2 ∈ Finset.Icc 3 7 := by
    have h := hexp_bd 2 Nat.prime_two
    have h_ub : m.factorization 2 ≤ 7 := by
      by_contra hgt
      have h8 : 8 ≤ m.factorization 2 := by omega
      have hanti := h_score_antitone_from (by norm_num : 0 < 2) (by norm_num) _ h8
      have hfail : h_score 2 8 * (B_val / maxPrime6 2) < T_val := by
        unfold maxPrime6 B_val T_val h_score; norm_num
      have hpos : 0 ≤ B_val / maxPrime6 2 := by unfold maxPrime6 B_val h_score; norm_num
      linarith [mul_le_mul_of_nonneg_right hanti hpos]
    have h_lb : 3 ≤ m.factorization 2 := by
      by_contra hlt
      rcases (by omega : m.factorization 2 = 0 ∨ m.factorization 2 = 1 ∨ m.factorization 2 = 2) with
        hval | hval | hval <;>
        (rw [hval] at h; unfold maxPrime6 B_val T_val h_score at h; norm_num at h)
    exact Finset.mem_Icc.mpr ⟨h_lb, h_ub⟩
  have he3 : m.factorization 3 ∈ Finset.Icc 2 4 := by
    have h := hexp_bd 3 Nat.prime_three
    have h_ub : m.factorization 3 ≤ 4 := by
      by_contra hgt
      have h5 : 5 ≤ m.factorization 3 := by omega
      have hanti := h_score_antitone_from (by norm_num : 0 < 3) (by norm_num) _ h5
      have hfail : h_score 3 5 * (B_val / maxPrime6 3) < T_val := by
        unfold maxPrime6 B_val T_val h_score; norm_num
      have hpos : 0 ≤ B_val / maxPrime6 3 := by unfold maxPrime6 B_val h_score; norm_num
      linarith [mul_le_mul_of_nonneg_right hanti hpos]
    have h_lb : 2 ≤ m.factorization 3 := by
      by_contra hlt
      rcases (by omega : m.factorization 3 = 0 ∨ m.factorization 3 = 1) with hval | hval <;>
        (rw [hval] at h; unfold maxPrime6 B_val T_val h_score at h; norm_num at h)
    exact Finset.mem_Icc.mpr ⟨h_lb, h_ub⟩
  have he5 : m.factorization 5 ∈ Finset.Icc 1 2 := by
    have h := hexp_bd 5 (by decide)
    have h_ub : m.factorization 5 ≤ 2 := by
      by_contra hgt
      have h3 : 3 ≤ m.factorization 5 := by omega
      have hanti := h_score_antitone_from (by norm_num : 0 < 5) (by norm_num) _ h3
      have hfail : h_score 5 3 * (B_val / maxPrime6 5) < T_val := by
        unfold maxPrime6 B_val T_val h_score; norm_num
      have hpos : 0 ≤ B_val / maxPrime6 5 := by unfold maxPrime6 B_val h_score; norm_num
      linarith [mul_le_mul_of_nonneg_right hanti hpos]
    have h_lb : 1 ≤ m.factorization 5 := by
      by_contra hlt
      have h0 : m.factorization 5 = 0 := by omega
      rw [h0] at h; unfold maxPrime6 B_val T_val h_score at h; norm_num at h
    exact Finset.mem_Icc.mpr ⟨h_lb, h_ub⟩
  have he7 : m.factorization 7 = 1 := by
    have h := hexp_bd 7 (by decide)
    have h_ub : m.factorization 7 ≤ 1 := by
      by_contra hgt
      have h2 : 2 ≤ m.factorization 7 := by omega
      have hanti := h_score_antitone_from (by norm_num : 0 < 7) (by norm_num) _ h2
      have hfail : h_score 7 2 * (B_val / maxPrime6 7) < T_val := by
        unfold maxPrime6 B_val T_val h_score; norm_num
      have hpos : 0 ≤ B_val / maxPrime6 7 := by unfold maxPrime6 B_val h_score; norm_num
      linarith [mul_le_mul_of_nonneg_right hanti hpos]
    have h_lb : 1 ≤ m.factorization 7 := by
      by_contra hlt
      have h0 : m.factorization 7 = 0 := by omega
      rw [h0] at h; unfold maxPrime6 B_val T_val h_score at h; norm_num at h
    omega
  have he11 : m.factorization 11 = 1 := by
    have h := hexp_bd 11 (by decide)
    have h_ub : m.factorization 11 ≤ 1 := by
      by_contra hgt
      have h2 : 2 ≤ m.factorization 11 := by omega
      have hanti := h_score_antitone_from (by norm_num : 0 < 11) (by norm_num) _ h2
      have hfail : h_score 11 2 * (B_val / maxPrime6 11) < T_val := by
        unfold maxPrime6 B_val T_val h_score; norm_num
      have hpos : 0 ≤ B_val / maxPrime6 11 := by unfold maxPrime6 B_val h_score; norm_num
      linarith [mul_le_mul_of_nonneg_right hanti hpos]
    have h_lb : 1 ≤ m.factorization 11 := by
      by_contra hlt
      have h0 : m.factorization 11 = 0 := by omega
      rw [h0] at h; unfold maxPrime6 B_val T_val h_score at h; norm_num at h
    omega
  have he13 : m.factorization 13 ≤ 1 := by
    have h := hexp_bd 13 (by decide)
    by_contra hgt
    have h2 : 2 ≤ m.factorization 13 := by omega
    have hanti := h_score_antitone_from (by norm_num : 0 < 13) (by norm_num) _ h2
    have hfail : h_score 13 2 * (B_val / maxPrime6 13) < T_val := by
      unfold maxPrime6 B_val T_val h_score; norm_num
    have hpos : 0 ≤ B_val / maxPrime6 13 := by unfold maxPrime6 B_val h_score; norm_num
    linarith [mul_le_mul_of_nonneg_right hanti hpos]
  have he17 : m.factorization 17 ≤ 1 := by
    have h := hexp_bd 17 (by decide)
    by_contra hgt
    have h2 : 2 ≤ m.factorization 17 := by omega
    have hanti := h_score_antitone_from (by norm_num : 0 < 17) (by norm_num) _ h2
    have hfail : h_score 17 2 * (B_val / maxPrime6 17) < T_val := by
      unfold maxPrime6 B_val T_val h_score; norm_num
    have hpos : 0 ≤ B_val / maxPrime6 17 := by unfold maxPrime6 B_val h_score; norm_num
    linarith [mul_le_mul_of_nonneg_right hanti hpos]
  have he19 : m.factorization 19 ≤ 1 := by
    have h := hexp_bd 19 (by decide)
    by_contra hgt
    have h2 : 2 ≤ m.factorization 19 := by omega
    have hanti := h_score_antitone_from (by norm_num : 0 < 19) (by norm_num) _ h2
    have hfail : h_score 19 2 * (B_val / maxPrime6 19) < T_val := by
      unfold maxPrime6 B_val T_val h_score; norm_num
    have hpos : 0 ≤ B_val / maxPrime6 19 := by unfold maxPrime6 B_val h_score; norm_num
    linarith [mul_le_mul_of_nonneg_right hanti hpos]
  exact ⟨hk_pos, hk_eq_tau, htau_dvd, hpf, he2, he3, he5, he7, he11, he13, he17, he19⟩

/-! ### Fast Exact Kernel Verification (Zero `native_decide`) -/

private lemma prime_dvd_finset_prod {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℕ}
    {p : ℕ} (hp : p.Prime) (h : p ∣ ∏ i ∈ s, f i) : ∃ i ∈ s, p ∣ f i := by
  induction s using Finset.induction with
  | empty =>
    simp at h
    exact absurd h hp.ne_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, hp.dvd_mul] at h
    rcases h with h1 | h2
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨i, hi, hpi⟩ := ih h2
      exact ⟨i, Finset.mem_insert_of_mem hi, hpi⟩

private def primes8 : Fin 8 → ℕ := ![2, 3, 5, 7, 11, 13, 17, 19]

private lemma primes8_prime (i : Fin 8) : (primes8 i).Prime := by
  fin_cases i <;> decide

private lemma primes8_inj : Function.Injective primes8 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [primes8] at h ⊢

/-- Product of `p_i ^ e_i` over the eight primes `{2,3,5,7,11,13,17,19}`. -/
def val8 (e : Fin 8 → ℕ) : ℕ :=
  2 ^ e 0 * 3 ^ e 1 * 5 ^ e 2 * 7 ^ e 3 * 11 ^ e 4 * 13 ^ e 5 * 17 ^ e 6 * 19 ^ e 7

/-- Divisor count `(e_0+1) ⋯ (e_7+1)`. -/
def tau8 (e : Fin 8 → ℕ) : ℕ :=
  (e 0 + 1) * (e 1 + 1) * (e 2 + 1) * (e 3 + 1) *
    (e 4 + 1) * (e 5 + 1) * (e 6 + 1) * (e 7 + 1)

lemma val8_eq_prod (e : Fin 8 → ℕ) : val8 e = ∏ i : Fin 8, primes8 i ^ e i := by
  unfold val8 primes8
  simp [Fin.prod_univ_eight, mul_assoc]

lemma tau_val8 (e : Fin 8 → ℕ) : tau (val8 e) = tau8 e := by
  rw [val8_eq_prod]
  unfold tau tau8
  have hne : (∏ i : Fin 8, primes8 i ^ e i) ≠ 0 :=
    (Finset.prod_pos fun i _ => pow_pos (primes8_prime i).pos (e i)).ne'
  rw [Nat.card_divisors hne]
  have hfac : (∏ i : Fin 8, primes8 i ^ e i).factorization =
      ∑ i : Fin 8, (e i) • (primes8 i).factorization := by
    rw [Nat.factorization_prod (fun i _ => (pow_pos (primes8_prime i).pos _).ne')]
    refine Finset.sum_congr rfl fun i _ => Nat.factorization_pow _ _
  have hpf_sub : (∏ i : Fin 8, primes8 i ^ e i).primeFactors ⊆ Finset.univ.image primes8 := by
    intro p hp
    have hrp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    rcases prime_dvd_finset_prod hrp hdvd with ⟨i, _, hi⟩
    have hpi : p ∣ primes8 i := hrp.dvd_of_dvd_pow hi
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i,
      ((Nat.prime_dvd_prime_iff_eq hrp (primes8_prime i)).mp hpi).symm⟩
  have hprod_sub :
      (∏ x ∈ (∏ i : Fin 8, primes8 i ^ e i).primeFactors,
        ((∏ i : Fin 8, primes8 i ^ e i).factorization x + 1)) =
      ∏ x ∈ Finset.univ.image primes8,
        ((∏ i : Fin 8, primes8 i ^ e i).factorization x + 1) := by
    refine Finset.prod_subset hpf_sub fun p _ hp => ?_
    rw [factorization_eq_zero_of_notMem hne hp, zero_add]
  rw [hprod_sub, Finset.prod_image (fun i _ j _ h => primes8_inj h)]
  have hval : ∀ i : Fin 8, (∏ j : Fin 8, primes8 j ^ e j).factorization (primes8 i) = e i := by
    intro i
    rw [hfac]
    simp only [Finset.sum_apply', Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      (primes8_prime _).factorization]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hne' : primes8 j ≠ primes8 i := fun h => hji (primes8_inj h)
      simp [hne']
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hprod_eight := Fin.prod_univ_eight
    (fun i => (∏ j : Fin 8, primes8 j ^ e j).factorization (primes8 i) + 1)
  rw [hprod_eight]
  simp only [hval]

lemma val8_of_primeFactors_subset {m : ℕ} (hm : 1 ≤ m)
    (hpf : ∀ p ∈ m.primeFactors, p ∈ ({2, 3, 5, 7, 11, 13, 17, 19} : Finset ℕ)) :
    val8 (fun i => m.factorization (primes8 i)) = m := by
  rw [val8_eq_prod]
  have hm0 : m ≠ 0 := by omega
  have hsub : m.primeFactors ⊆ Finset.univ.image primes8 := by
    intro p hp
    have hp8 := hpf p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp8
    rw [Finset.mem_image]
    rcases hp8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, Finset.mem_univ 0, rfl⟩
    · exact ⟨1, Finset.mem_univ 1, rfl⟩
    · exact ⟨2, Finset.mem_univ 2, rfl⟩
    · exact ⟨3, Finset.mem_univ 3, rfl⟩
    · exact ⟨4, Finset.mem_univ 4, rfl⟩
    · exact ⟨5, Finset.mem_univ 5, rfl⟩
    · exact ⟨6, Finset.mem_univ 6, rfl⟩
    · exact ⟨7, Finset.mem_univ 7, rfl⟩
  have hm_eq_m : m = ∏ x ∈ m.primeFactors, x ^ m.factorization x :=
    Nat.prod_primeFactors_pow_factorization hm0
  have himg : (∏ i : Fin 8, primes8 i ^ m.factorization (primes8 i)) =
      ∏ p ∈ Finset.univ.image primes8, p ^ m.factorization p := by
    rw [← Finset.prod_image (f := fun p => p ^ m.factorization p)
      (fun i _ j _ h => primes8_inj h)]
  rw [himg]
  conv_rhs => rw [hm_eq_m]
  refine (Finset.prod_subset (f := fun p => p ^ m.factorization p) hsub fun p _ hp => ?_).symm
  rw [factorization_eq_zero_of_notMem hm0 hp, pow_zero]

/-- Fast computable prime-stripping helper; `fuel = 10` handles all `x < 2^10 = 1024`. -/
private def stripPrime (p : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, x => (0, x)
  | fuel + 1, x =>
    if 1 < p ∧ x ≠ 0 ∧ x % p = 0 then
      let res := stripPrime p fuel (x / p)
      (res.1 + 1, res.2)
    else (0, x)

private lemma stripPrime_spec (p : ℕ) (fuel x : ℕ) (hp : p.Prime) (hx : 0 < x)
    (hfuel : x < 2 ^ fuel) :
    let res := stripPrime p fuel x
    x = p ^ res.1 * res.2 ∧ 0 < res.2 ∧ ¬ (p ∣ res.2) := by
  induction fuel generalizing x with
  | zero => simp at hfuel; omega
  | succ fuel ih =>
    unfold stripPrime
    split_ifs with hcond
    · have hx0 : x / p ≠ 0 := by
        rcases Nat.dvd_of_mod_eq_zero hcond.2.2 with ⟨c, hc⟩
        rw [hc, Nat.mul_div_cancel_left _ hp.pos]
        intro hc0; rw [hc0, mul_zero] at hc; exact hcond.2.1 hc
      have hdiv_le : x / p ≤ x / 2 := Nat.div_le_div_left hp.two_le (by omega)
      have hdiv_lt : x / p < 2 ^ fuel := by
        have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
        omega
      have ih_res := ih (x / p) (Nat.pos_of_ne_zero hx0) hdiv_lt
      dsimp only at ih_res
      rcases ih_res with ⟨h1, h2, h3⟩
      refine ⟨?_, h2, h3⟩
      calc
        x = p * (x / p) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hcond.2.2)).symm
        _ = p * (p ^ (stripPrime p fuel (x / p)).1 * (stripPrime p fuel (x / p)).2) := by
            rw [← h1]
        _ = p ^ ((stripPrime p fuel (x / p)).1 + 1) * (stripPrime p fuel (x / p)).2 := by
            rw [pow_succ', mul_assoc]
    · refine ⟨by simp, hx, ?_⟩
      intro hdvd
      apply hcond
      exact ⟨hp.one_lt, hx.ne', Nat.mod_eq_zero_of_dvd hdvd⟩

private def stripList (fuel : ℕ) : List ℕ → ℕ → List ℕ × ℕ
  | [], x => ([], x)
  | p :: ps, x =>
    let res1 := stripPrime p fuel x
    let res2 := stripList fuel ps res1.2
    (res1.1 :: res2.1, res2.2)

private lemma stripList_spec (fuel : ℕ) (ps : List ℕ) (x : ℕ)
    (hps : ∀ p ∈ ps, p.Prime) (hnd : ps.Nodup) (hx : 0 < x) (hfuel : x < 2 ^ fuel) :
    let res := stripList fuel ps x
    x = (List.zipWith (· ^ ·) ps res.1).prod * res.2 ∧
      0 < res.2 ∧ res.2 ≤ x ∧
      (∀ p ∈ ps, ¬ (p ∣ res.2)) ∧
      res.1.length = ps.length := by
  induction ps generalizing x with
  | nil =>
    simp [stripList, hx]
  | cons p ps ih =>
    have hp : p.Prime := hps p (by simp)
    have hps' : ∀ q ∈ ps, q.Prime := fun q hq => hps q (by simp [hq])
    have hnd_split := List.nodup_cons.mp hnd
    have h1 := stripPrime_spec p fuel x hp hx hfuel
    set res1 := stripPrime p fuel x
    have hr1_le : res1.2 ≤ x := by
      have : p ^ res1.1 * res1.2 = x := h1.1.symm
      exact Nat.le_of_dvd hx ⟨p ^ res1.1, by rw [mul_comm, this]⟩
    have h2 := ih res1.2 hps' hnd_split.2 h1.2.1 (lt_of_le_of_lt hr1_le hfuel)
    dsimp only [stripList]
    rcases h1 with ⟨hx_eq, _, hndvd_p⟩
    rcases h2 with ⟨hr1_eq, hr2_pos, hr2_le, hndvd_ps, hlen⟩
    refine ⟨?_, hr2_pos, le_trans hr2_le hr1_le, ?_, by simpa [res1] using hlen⟩
    · simp only [List.zipWith_cons_cons, List.prod_cons]
      have hx_eq' : x = p ^ res1.1 * res1.2 := hx_eq
      have hr1_eq' : res1.2 = (List.zipWith (· ^ ·) ps (stripList fuel ps res1.2).1).prod *
          (stripList fuel ps res1.2).2 := hr1_eq
      change x = p ^ res1.1 * (List.zipWith (· ^ ·) ps (stripList fuel ps res1.2).1).prod *
        (stripList fuel ps res1.2).2
      rw [mul_assoc, ← hr1_eq', ← hx_eq']
    · intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hqps
      · intro hdvd
        exact hndvd_p (dvd_trans hdvd ⟨(List.zipWith (· ^ ·) ps (stripList fuel ps res1.2).1).prod,
          by rw [mul_comm, ← hr1_eq]⟩)
      · exact hndvd_ps q hqps

private def primes10 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

/-- Fast computable `τ(154440 * j)` for `1 ≤ j < 840`. Since `154440 = 2^3 * 3^3 * 5 * 11 * 13`
and `840 < 2^10`, `fuel = 10` suffices and leaves a cofactor `r < 31^2` that is `1` or prime. -/
def tauMul154440 (j : ℕ) : ℕ :=
  let res := stripList 10 primes10 j
  let exps154440 := [3, 3, 1, 0, 1, 1, 0, 0, 0, 0]
  let base := (List.zipWith (fun a b => a + b + 1) exps154440 res.1).prod
  if res.2 = 1 then base else 2 * base

private lemma tau_mul_coprime {a b : ℕ} (hcop : Nat.Coprime a b) :
    tau (a * b) = tau a * tau b := by
  unfold tau
  have := (ArithmeticFunction.isMultiplicative_sigma (k := 0)).map_mul_of_coprime hcop
  simpa [ArithmeticFunction.sigma_zero_apply] using this

private lemma tau_prime_pow_mul_coprime {p e r : ℕ} (hp : p.Prime) (hndvd : ¬ p ∣ r) :
    tau (p ^ e * r) = (e + 1) * tau r := by
  have hcop : Nat.Coprime (p ^ e) r := (hp.coprime_iff_not_dvd.mpr hndvd).pow_left e
  rw [tau_mul_coprime hcop]
  congr 1
  unfold tau
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

private lemma prime_dvd_zipWith_pow_prod {ps es : List ℕ} {p : ℕ} (hp : p.Prime)
    (hps : ∀ q ∈ ps, q.Prime) (h : p ∣ (List.zipWith (· ^ ·) ps es).prod) :
    ∃ q ∈ ps, p = q := by
  induction ps generalizing es with
  | nil =>
    simp at h
    exact absurd h hp.ne_one
  | cons q qs ih =>
    cases es with
    | nil =>
      simp at h
      exact absurd h hp.ne_one
    | cons e es =>
      simp only [List.zipWith_cons_cons, List.prod_cons] at h
      rcases hp.dvd_mul.mp h with hq | hrest
      · exact ⟨q, by simp, (Nat.prime_dvd_prime_iff_eq hp (hps q (by simp))).mp (hp.dvd_of_dvd_pow hq)⟩
      · obtain ⟨q', hq', heq⟩ := ih (fun x hx => hps x (by simp [hx])) hrest
        exact ⟨q', by simp [hq'], heq⟩

private lemma tau_prod_primes_mul {ps es : List ℕ} {r : ℕ}
    (hps : ∀ p ∈ ps, p.Prime) (hnd : ps.Nodup) (hlen : ps.length = es.length)
    (hndvd : ∀ p ∈ ps, ¬ p ∣ r) :
    tau ((List.zipWith (· ^ ·) ps es).prod * r) =
      (es.map (· + 1)).prod * tau r := by
  induction ps generalizing es with
  | nil =>
    cases es with
    | nil => simp
    | cons => simp at hlen
  | cons p ps ih =>
    cases es with
    | nil => simp at hlen
    | cons e es =>
      have hp : p.Prime := hps p (by simp)
      have hps' : ∀ q ∈ ps, q.Prime := fun q hq => hps q (by simp [hq])
      have hnd_split := List.nodup_cons.mp hnd
      have hndvd_p : ¬ p ∣ (List.zipWith (· ^ ·) ps es).prod * r := by
        intro hdvd
        rcases hp.dvd_mul.mp hdvd with hprod | hr_dvd
        · obtain ⟨q, hq_mem, rfl⟩ := prime_dvd_zipWith_pow_prod hp hps' hprod
          exact hnd_split.1 hq_mem
        · exact hndvd p (by simp) hr_dvd
      simp only [List.zipWith_cons_cons, List.prod_cons, List.map_cons, mul_assoc]
      rw [tau_prime_pow_mul_coprime hp hndvd_p,
        ih hps' hnd_split.2 (by simpa using hlen) (fun q hq => hndvd q (by simp [hq]))]

private lemma prod_zipWith_pow_mul (ps es₁ es₂ : List ℕ)
    (h1 : es₁.length = ps.length) (h2 : es₂.length = ps.length) :
    (List.zipWith (· ^ ·) ps es₁).prod * (List.zipWith (· ^ ·) ps es₂).prod =
      (List.zipWith (· ^ ·) ps (List.zipWith (· + ·) es₁ es₂)).prod := by
  induction ps generalizing es₁ es₂ with
  | nil => simp
  | cons p ps ih =>
    cases es₁ with
    | nil => simp at h1
    | cons a as =>
      cases es₂ with
      | nil => simp at h2
      | cons b bs =>
        simp only [List.zipWith_cons_cons, List.prod_cons, pow_add]
        have hih := ih as bs (by simpa using h1) (by simpa using h2)
        calc
          p ^ a * (List.zipWith (· ^ ·) ps as).prod * (p ^ b * (List.zipWith (· ^ ·) ps bs).prod)
              = p ^ a * p ^ b * ((List.zipWith (· ^ ·) ps as).prod * (List.zipWith (· ^ ·) ps bs).prod) := by ring
          _ = p ^ a * p ^ b * (List.zipWith (· ^ ·) ps (List.zipWith (· + ·) as bs)).prod := by rw [hih]

private lemma map_succ_zipWith_add (es₁ es₂ : List ℕ) :
    (List.zipWith (· + ·) es₁ es₂).map (· + 1) =
      List.zipWith (fun a b => a + b + 1) es₁ es₂ := by
  induction es₁ generalizing es₂ with
  | nil => simp
  | cons a as ih =>
    cases es₂ with
    | nil => simp
    | cons b bs => simp [ih bs]

private lemma tauMul154440_eq {j : ℕ} (hj1 : 1 ≤ j) (hj840 : j < 840) :
    tau (154440 * j) = tauMul154440 j := by
  have hps : ∀ p ∈ primes10, p.Prime := by
    intro p hp; fin_cases hp <;> decide
  have hnd : primes10.Nodup := by decide
  have hspec := stripList_spec 10 primes10 j hps hnd hj1 (by omega)
  rcases hspec with ⟨hj_eq, hr_pos, hr_le, hndvd, hlen⟩
  set res := stripList 10 primes10 j
  have hr_prime_or_one : res.2 = 1 ∨ res.2.Prime := by
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hr_pos) with h1 | hr2
    · left; exact h1.symm
    · right
      rw [Nat.prime_def_minFac]
      refine ⟨hr2, ?_⟩
      by_contra hmin
      set q := res.2.minFac
      have hqp : q.Prime := Nat.minFac_prime (by omega)
      have hqr : q ∣ res.2 := Nat.minFac_dvd res.2
      have hq_sq : q * q ≤ res.2 := by
        have hnotp : ¬ res.2.Prime := fun hp => hmin (Nat.Prime.minFac_eq hp)
        have := Nat.minFac_sq_le_self hr_pos hnotp
        simpa [sq] using this
      have hq31 : q < 31 := by nlinarith
      have hq_mem : q ∈ primes10 := by
        have hq2 := hqp.two_le
        interval_cases q <;> simp_all [primes10] <;> norm_num at hqp
      exact hndvd q hq_mem hqr
  have h154440 : 154440 = (List.zipWith (· ^ ·) primes10 [3, 3, 1, 0, 1, 1, 0, 0, 0, 0]).prod := by
    decide
  have hzip := prod_zipWith_pow_mul primes10 [3, 3, 1, 0, 1, 1, 0, 0, 0, 0] res.1
    (by decide) hlen
  have hmul_eq : 154440 * j =
      (List.zipWith (· ^ ·) primes10 (List.zipWith (· + ·) [3, 3, 1, 0, 1, 1, 0, 0, 0, 0] res.1)).prod * res.2 := by
    calc
      154440 * j = (List.zipWith (· ^ ·) primes10 [3, 3, 1, 0, 1, 1, 0, 0, 0, 0]).prod *
          ((List.zipWith (· ^ ·) primes10 res.1).prod * res.2) := by rw [← h154440, ← hj_eq]
      _ = _ := by rw [← mul_assoc, hzip]
  have hlen_sum : primes10.length = (List.zipWith (· + ·) [3, 3, 1, 0, 1, 1, 0, 0, 0, 0] res.1).length := by
    simp [primes10, hlen]
  rw [hmul_eq, tau_prod_primes_mul hps hnd hlen_sum hndvd, map_succ_zipWith_add]
  unfold tauMul154440
  change (List.zipWith (fun a b => a + b + 1) [3, 3, 1, 0, 1, 1, 0, 0, 0, 0] res.1).prod * tau res.2 =
    if res.2 = 1 then (List.zipWith (fun a b => a + b + 1) [3, 3, 1, 0, 1, 1, 0, 0, 0, 0] res.1).prod
    else 2 * (List.zipWith (fun a b => a + b + 1) [3, 3, 1, 0, 1, 1, 0, 0, 0, 0] res.1).prod
  rcases hr_prime_or_one with hr1 | hrp
  · have htau1 : tau 1 = 1 := by decide
    rw [hr1, htau1]
    simp
  · have hr_ne1 : res.2 ≠ 1 := hrp.ne_one
    have htau_r : tau res.2 = 2 := by
      unfold tau
      rw [hrp.divisors, Finset.card_pair hr_ne1.symm]
    simp [hr_ne1, htau_r, mul_comm]

/-- Binary-splitting bounded quantifier so `decide` runs with depth `≤ 11` instead of `840`. -/
private def allIcoAux (p : ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    if b ≤ a then true
    else if a + 1 = b then p a
    else
      let mid := (a + b) / 2
      allIcoAux p fuel a mid && allIcoAux p fuel mid b

private lemma allIcoAux_spec (p : ℕ → Bool) (fuel a b : ℕ)
    (h : allIcoAux p fuel a b = true) : ∀ j, a ≤ j → j < b → p j = true := by
  induction fuel generalizing a b with
  | zero => simp [allIcoAux] at h
  | succ fuel ih =>
    unfold allIcoAux at h
    split_ifs at h with hba hab
    · intro j hj1 hj2; omega
    · intro j hj1 hj2
      have hja : j = a := by omega
      subst hja; exact h
    · simp only [Bool.and_eq_true] at h
      intro j hj1 hj2
      by_cases hj : j < (a + b) / 2
      · exact ih a ((a + b) / 2) h.1 j hj1 hj
      · exact ih ((a + b) / 2) b h.2 j (by omega) hj2

private lemma gcd_eq_self_iff_dvd_and_coprime {t n j : ℕ} (hj : 0 < j) :
    Nat.gcd t (n * j) = j ↔ j ∣ t ∧ Nat.Coprime (t / j) n := by
  constructor
  · intro hg
    have hdvd : j ∣ t := hg ▸ Nat.gcd_dvd_left t (n * j)
    refine ⟨hdvd, ?_⟩
    have ht : t = j * (t / j) := (Nat.mul_div_cancel' hdvd).symm
    rw [ht, mul_comm n j, Nat.gcd_mul_left] at hg
    unfold Nat.Coprime
    exact Nat.mul_left_cancel hj (by simpa using hg)
  · rintro ⟨hdvd, hcop⟩
    have ht : t = j * (t / j) := (Nat.mul_div_cancel' hdvd).symm
    rw [ht, mul_comm n j, Nat.gcd_mul_left, hcop]
    ring

private def notValid154440Fast (j : ℕ) : Bool :=
  let t := tauMul154440 j
  (t % j != 0) || (let q := t / j; q % 2 == 0 || q % 3 == 0 || q % 5 == 0 || q % 11 == 0 || q % 13 == 0)

private lemma notValid154440Fast_sound {j : ℕ} (hj : 0 < j)
    (h : notValid154440Fast j = true) : Nat.gcd (tauMul154440 j) (154440 * j) ≠ j := by
  intro hg
  rcases (gcd_eq_self_iff_dvd_and_coprime hj).mp hg with ⟨hdvd, hcop⟩
  set t := tauMul154440 j
  set q := t / j
  have hmod0 : t % j = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hndvd : ∀ p : ℕ, 1 < p → p ∣ 154440 → q % p ≠ 0 := by
    intro p hp1 hp154 hmod
    have hpq : p ∣ q := Nat.dvd_of_mod_eq_zero hmod
    have hpg : p ∣ Nat.gcd q 154440 := Nat.dvd_gcd hpq hp154
    rw [hcop] at hpg
    have := Nat.le_of_dvd (by norm_num) hpg
    omega
  have h2 : q % 2 ≠ 0 := hndvd 2 (by norm_num) (by decide)
  have h3 : q % 3 ≠ 0 := hndvd 3 (by norm_num) (by decide)
  have h5 : q % 5 ≠ 0 := hndvd 5 (by norm_num) (by decide)
  have h11 : q % 11 ≠ 0 := hndvd 11 (by norm_num) (by decide)
  have h13 : q % 13 ≠ 0 := hndvd 13 (by norm_num) (by decide)
  unfold notValid154440Fast at h
  simp [t, q, hmod0, h2, h3, h5, h11, h13] at h

private lemma min_154440_c1 : allIcoAux notValid154440Fast 9 1 170 = true := by decide
private lemma min_154440_c2 : allIcoAux notValid154440Fast 9 170 340 = true := by decide
private lemma min_154440_c3 : allIcoAux notValid154440Fast 9 340 510 = true := by decide
private lemma min_154440_c4 : allIcoAux notValid154440Fast 9 510 680 = true := by decide
private lemma min_154440_c5 : allIcoAux notValid154440Fast 9 680 840 = true := by decide

/-- Exact value `a(154440) = 840`. -/
theorem a352834_154440 : a352834 154440 = 840 := by
  have h840 : IsValidA352834 154440 840 := by
    refine ⟨by norm_num, ?_⟩
    have hm : 840 * 154440 = val8 ![6, 4, 2, 1, 1, 1, 0, 0] := by decide
    rw [hm, tau_val8]
    decide
  have hle : a352834 154440 ≤ 840 := a352834_le_of_valid h840
  have hmin : ∀ j, 1 ≤ j → j < 840 → ¬ (Nat.gcd (tauMul154440 j) (154440 * j) = j) := by
    intro j hj1 hj2
    refine notValid154440Fast_sound hj1 ?_
    by_cases h1 : j < 170
    · exact allIcoAux_spec _ 9 1 170 min_154440_c1 j hj1 h1
    · by_cases h2 : j < 340
      · exact allIcoAux_spec _ 9 170 340 min_154440_c2 j (by omega) h2
      · by_cases h3 : j < 510
        · exact allIcoAux_spec _ 9 340 510 min_154440_c3 j (by omega) h3
        · by_cases h4 : j < 680
          · exact allIcoAux_spec _ 9 510 680 min_154440_c4 j (by omega) h4
          · exact allIcoAux_spec _ 9 680 840 min_154440_c5 j (by omega) hj2
  by_contra hne
  have hk_pos : 0 < a352834 154440 := by
    classical
    have hex : ∃ k, IsValidA352834 154440 k := ⟨840, h840⟩
    rw [a352834, dif_pos hex]
    exact (Nat.find_spec hex).1
  have hk_lt : a352834 154440 < 840 := lt_of_le_of_ne hle hne
  have hk_spec := a352834_spec_of_pos hk_pos
  have hspec2 := hk_spec.2
  rw [mul_comm (a352834 154440) 154440, tauMul154440_eq hk_pos hk_lt] at hspec2
  exact hmin (a352834 154440) hk_pos hk_lt hspec2

/-! ### Finite Enumeration of the 240-Tuple Box -/

private structure Vec8 where
  e2 : ℕ
  e3 : ℕ
  e5 : ℕ
  e7 : ℕ
  e11 : ℕ
  e13 : ℕ
  e17 : ℕ
  e19 : ℕ
  deriving DecidableEq

private def Vec8.toFun (v : Vec8) : Fin 8 → ℕ :=
  ![v.e2, v.e3, v.e5, v.e7, v.e11, v.e13, v.e17, v.e19]

private def Vec8.val (v : Vec8) : ℕ :=
  2 ^ v.e2 * 3 ^ v.e3 * 5 ^ v.e5 * 7 ^ v.e7 *
    11 ^ v.e11 * 13 ^ v.e13 * 17 ^ v.e17 * 19 ^ v.e19

private def Vec8.tau (v : Vec8) : ℕ :=
  (v.e2 + 1) * (v.e3 + 1) * (v.e5 + 1) * (v.e7 + 1) *
    (v.e11 + 1) * (v.e13 + 1) * (v.e17 + 1) * (v.e19 + 1)

private def Vec8.add (a b : Vec8) : Vec8 :=
  ⟨a.e2 + b.e2, a.e3 + b.e3, a.e5 + b.e5, a.e7 + b.e7,
    a.e11 + b.e11, a.e13 + b.e13, a.e17 + b.e17, a.e19 + b.e19⟩

private lemma Vec8.val_eq (v : Vec8) : v.val = val8 v.toFun := by
  unfold Vec8.val val8 Vec8.toFun
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]

private lemma Vec8.tau_eq (v : Vec8) : v.tau = tau8 v.toFun := by
  unfold Vec8.tau tau8 Vec8.toFun
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]

private lemma Vec8.val_add (a b : Vec8) : (a.add b).val = a.val * b.val := by
  unfold Vec8.add Vec8.val
  simp only [pow_add]
  ring

private lemma Vec8.tau_val (v : Vec8) : A352834.tau v.val = v.tau := by
  rw [v.val_eq, v.tau_eq, tau_val8]

private def winnerVec : Vec8 := ⟨6, 4, 2, 1, 1, 1, 0, 0⟩

private def witnessVec (v : Vec8) : Vec8 :=
  match v with
  | ⟨5, 4, 2, 1, 1, 1, 0, 0⟩ => ⟨5, 1, 0, 1, 0, 0, 0, 0⟩ -- 672
  | ⟨6, 3, 2, 1, 1, 1, 0, 0⟩ => ⟨4, 3, 0, 0, 0, 0, 0, 0⟩ -- 432
  | ⟨5, 3, 2, 1, 1, 0, 0, 0⟩ => ⟨2, 2, 0, 0, 0, 0, 0, 0⟩ -- 36
  | ⟨4, 2, 2, 1, 1, 1, 0, 0⟩ => ⟨3, 0, 1, 0, 0, 0, 0, 0⟩ -- 40
  | ⟨5, 2, 1, 1, 1, 0, 0, 0⟩ => ⟨4, 0, 0, 0, 0, 0, 0, 0⟩ -- 16
  | ⟨4, 4, 2, 1, 1, 1, 0, 0⟩ => ⟨4, 1, 0, 0, 0, 0, 0, 0⟩ -- 48
  | ⟨4, 3, 2, 1, 1, 0, 0, 0⟩ => ⟨2, 1, 0, 0, 0, 0, 0, 0⟩ -- 12
  | ⟨6, 2, 2, 1, 1, 1, 0, 0⟩ => ⟨3, 1, 0, 0, 0, 0, 0, 0⟩ -- 24
  | ⟨6, 2, 1, 1, 1, 1, 0, 0⟩ => ⟨4, 0, 0, 0, 0, 0, 0, 0⟩ -- 16
  | ⟨6, 2, 2, 1, 1, 1, 1, 0⟩ => ⟨4, 1, 0, 0, 0, 0, 0, 0⟩ -- 48
  | ⟨6, 2, 1, 1, 1, 1, 1, 0⟩ => ⟨5, 0, 0, 0, 0, 0, 0, 0⟩ -- 32
  | ⟨5, 4, 2, 1, 1, 1, 1, 0⟩ => ⟨2, 1, 0, 0, 0, 0, 0, 0⟩ -- 12
  | ⟨4, 2, 1, 1, 1, 1, 0, 0⟩ => ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ -- 1
  | ⟨5, 2, 1, 1, 1, 1, 0, 0⟩ => ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ -- 1
  | ⟨6, 3, 1, 1, 1, 1, 0, 0⟩ => ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ -- 1
  | ⟨6, 3, 2, 1, 1, 1, 1, 0⟩ => ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ -- 3
  | ⟨6, 3, 2, 1, 1, 1, 0, 1⟩ => ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ -- 3
  | ⟨5, 4, 1, 1, 1, 1, 0, 0⟩ => ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ -- 1
  | ⟨4, 2, 2, 1, 1, 1, 1, 0⟩ => ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ -- 1
  | ⟨4, 2, 2, 1, 1, 1, 0, 1⟩ => ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ -- 1
  | _ => ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

private def nVecOf (v : Vec8) : Vec8 :=
  let res := stripList 12 [2, 3, 5, 7] v.tau
  match res.1 with
  | [t2, t3, t5, t7] =>
    ⟨v.e2 - t2, v.e3 - t3, v.e5 - t5, v.e7 - t7, v.e11, v.e13, v.e17, v.e19⟩
  | _ => ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

private def coprimeVec8Check (q : ℕ) (nv : Vec8) : Bool :=
  (nv.e2 == 0 || q % 2 != 0) &&
  (nv.e3 == 0 || q % 3 != 0) &&
  (nv.e5 == 0 || q % 5 != 0) &&
  (nv.e7 == 0 || q % 7 != 0) &&
  (nv.e11 == 0 || q % 11 != 0) &&
  (nv.e13 == 0 || q % 13 != 0) &&
  (nv.e17 == 0 || q % 17 != 0) &&
  (nv.e19 == 0 || q % 19 != 0)

private lemma coprime_pow_of_check {q p e : ℕ} (hp : p.Prime)
    (h : (e == 0 || q % p != 0) = true) : Nat.Coprime q (p ^ e) := by
  by_cases he : e = 0
  · simp [he]
  · simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, he, false_or] at h
    have hndvd : ¬ p ∣ q := fun hd => h (Nat.mod_eq_zero_of_dvd hd)
    exact (hp.coprime_iff_not_dvd.mpr hndvd).symm.pow_right e

private lemma coprimeVec8Check_sound {q : ℕ} {nv : Vec8}
    (h : coprimeVec8Check q nv = true) : Nat.Coprime q nv.val := by
  unfold coprimeVec8Check at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨h2, h3⟩, h5⟩, h7⟩, h11⟩, h13⟩, h17⟩, h19⟩
  unfold Vec8.val
  exact (((((((coprime_pow_of_check (by decide) h2).mul_right
    (coprime_pow_of_check (by decide) h3)).mul_right
    (coprime_pow_of_check (by decide) h5)).mul_right
    (coprime_pow_of_check (by decide) h7)).mul_right
    (coprime_pow_of_check (by decide) h11)).mul_right
    (coprime_pow_of_check (by decide) h13)).mul_right
    (coprime_pow_of_check (by decide) h17)).mul_right
    (coprime_pow_of_check (by decide) h19)

private def checkBox240 (v : Vec8) : Bool :=
  if 154440 * v.tau ^ 4 < 840 ^ 3 * v.val then true
  else if v.val % v.tau ≠ 0 then true
  else if v == winnerVec then true
  else
    let nv := nVecOf v
    let wv := witnessVec v
    let t := (wv.add nv).tau
    (nv.val * v.tau == v.val) &&
      (0 < wv.val) &&
      (t % wv.val == 0) &&
      coprimeVec8Check (t / wv.val) nv &&
      (154440 * wv.val ^ 3 < 840 ^ 3 * nv.val)

private def sliceForE2 (e2 : ℕ) : List Vec8 :=
  [2, 3, 4].flatMap fun e3 =>
  [1, 2].flatMap fun e5 =>
  [0, 1].flatMap fun e13 =>
  [0, 1].flatMap fun e17 =>
  [0, 1].map fun e19 =>
    ⟨e2, e3, e5, 1, 1, e13, e17, e19⟩

private lemma slice3_ok : (sliceForE2 3).all checkBox240 = true := by decide
private lemma slice4_ok : (sliceForE2 4).all checkBox240 = true := by decide
private lemma slice5_ok : (sliceForE2 5).all checkBox240 = true := by decide
private lemma slice6_ok : (sliceForE2 6).all checkBox240 = true := by decide
private lemma slice7_ok : (sliceForE2 7).all checkBox240 = true := by decide

private lemma box240_sound (v : Vec8)
    (h2 : v.e2 ∈ Finset.Icc 3 7) (h3 : v.e3 ∈ Finset.Icc 2 4)
    (h5 : v.e5 ∈ Finset.Icc 1 2) (h7 : v.e7 = 1) (h11 : v.e11 = 1)
    (h13 : v.e13 ≤ 1) (h17 : v.e17 ≤ 1) (h19 : v.e19 ≤ 1) :
    checkBox240 v = true := by
  rcases v with ⟨e2, e3, e5, e7, e11, e13, e17, e19⟩
  dsimp at h2 h3 h5 h7 h11 h13 h17 h19
  subst h7; subst h11
  rw [Finset.mem_Icc] at h2 h3 h5
  have he3 : e3 = 2 ∨ e3 = 3 ∨ e3 = 4 := by omega
  have he5 : e5 = 1 ∨ e5 = 2 := by omega
  have he13 : e13 = 0 ∨ e13 = 1 := by omega
  have he17 : e17 = 0 ∨ e17 = 1 := by omega
  have he19 : e19 = 0 ∨ e19 = 1 := by omega
  have hmem : ∀ x, ⟨x, e3, e5, 1, 1, e13, e17, e19⟩ ∈ sliceForE2 x := fun x => by
    simp only [sliceForE2, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨e3, he3, e5, he5, e13, he13, e17, he17, e19, he19, rfl⟩
  have he2 : e2 = 3 ∨ e2 = 4 ∨ e2 = 5 ∨ e2 = 6 ∨ e2 = 7 := by omega
  rcases he2 with rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp slice3_ok _ (hmem 3)
  · exact List.all_eq_true.mp slice4_ok _ (hmem 4)
  · exact List.all_eq_true.mp slice5_ok _ (hmem 5)
  · exact List.all_eq_true.mp slice6_ok _ (hmem 6)
  · exact List.all_eq_true.mp slice7_ok _ (hmem 7)

/-- Global sharp bound (OEIS A352834): for all `n ≥ 1`, `154440 * a(n)^3 ≤ 840^3 * n`. -/
theorem a352834_global_bound (n : ℕ) (hn : 1 ≤ n) :
    154440 * (a352834 n) ^ 3 ≤ 840 ^ 3 * n := by
  by_contra hlt
  have hgt : 840 ^ 3 * n < 154440 * (a352834 n) ^ 3 := Nat.lt_of_not_le hlt
  have hT : T_val ≤ ((a352834 n : ℚ) ^ 3) / (n : ℚ) := by
    unfold T_val
    have hn_pos : (0 : ℚ) < (n : ℚ) := Nat.cast_pos.mpr hn
    rw [div_le_div_iff₀ (by norm_num) hn_pos]
    have hcomm : (840 : ℕ) ^ 3 * n ≤ (a352834 n) ^ 3 * 154440 := by linarith
    exact_mod_cast hcomm
  obtain ⟨hk_pos, hk_eq_tau, htau_dvd, hpf, he2, he3, he5, he7, he11, he13, he17, he19⟩ :=
    candidate_constraints hn hT
  set m := a352834 n * n
  let v : Vec8 := ⟨m.factorization 2, m.factorization 3, m.factorization 5, m.factorization 7,
    m.factorization 11, m.factorization 13, m.factorization 17, m.factorization 19⟩
  have hm_pos : 1 ≤ m := Nat.succ_le_of_lt (Nat.mul_pos hk_pos hn)
  have hm_eq : v.val = m := by
    rw [v.val_eq]
    exact val8_of_primeFactors_subset hm_pos hpf
  have htau_eq : v.tau = tau m := by
    rw [← v.tau_val, hm_eq]
  have hchk : checkBox240 v = true :=
    box240_sound v he2 he3 he5 he7 he11 he13 he17 he19
  have hnot_small : ¬ (154440 * v.tau ^ 4 < 840 ^ 3 * v.val) := by
    rw [hm_eq, htau_eq, ← hk_eq_tau]
    have h4 : 840 ^ 3 * m ≤ 154440 * (a352834 n) ^ 4 := by
      have : m = a352834 n * n := rfl
      rw [this]
      nlinarith [hgt]
    omega
  have hdvd_v : v.val % v.tau = 0 := by
    rw [hm_eq, htau_eq]
    exact Nat.mod_eq_zero_of_dvd htau_dvd
  unfold checkBox240 at hchk
  simp only [hnot_small, ↓reduceIte, hdvd_v, ne_eq, not_true_eq_false] at hchk
  by_cases hwin : v = winnerVec
  · have hm_win : m = 154440 * 840 := by
      rw [← hm_eq, hwin]
      decide
    have htau_win : tau m = 840 := by
      rw [← htau_eq, hwin]
      decide
    have hn_eq : n = 154440 := by
      have hk840 : a352834 n = 840 := hk_eq_tau.trans htau_win
      rw [show m = a352834 n * n from rfl, hk840] at hm_win
      nlinarith
    rw [hn_eq, a352834_154440] at hgt
    omega
  · have hwin_false : (v == winnerVec) = false := beq_false_of_ne hwin
    rw [ite_eq_right_iff.mpr (fun h => by simp [hwin_false] at h)] at hchk
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
    rcases hchk with ⟨⟨⟨⟨hnv_mul, hw_pos⟩, hmod0⟩, hcop_chk⟩, hw_lt⟩
    set nv := nVecOf v
    set wv := witnessVec v
    have hn_eq : n = nv.val := by
      have h1 : nv.val * tau m = a352834 n * n := by
        rw [← htau_eq, hnv_mul, hm_eq]
      rw [← hk_eq_tau, mul_comm (a352834 n) n] at h1
      exact (Nat.mul_right_cancel hk_pos h1).symm
    have hgcd : Nat.gcd (wv.add nv).tau (wv.val * nv.val) = wv.val := by
      rw [mul_comm wv.val nv.val]
      exact (gcd_eq_self_iff_dvd_and_coprime hw_pos).mpr
        ⟨Nat.dvd_of_mod_eq_zero hmod0, coprimeVec8Check_sound hcop_chk⟩
    have hvalid : IsValidA352834 n wv.val := by
      refine ⟨hw_pos, ?_⟩
      have htau_wv : tau (wv.val * n) = (wv.add nv).tau := by
        rw [hn_eq, ← wv.val_add, (wv.add nv).tau_val]
      rw [htau_wv, hn_eq]
      exact hgcd
    have hle_w : a352834 n ≤ wv.val := a352834_le_of_valid hvalid
    have hle_pow : (a352834 n) ^ 3 ≤ wv.val ^ 3 := Nat.pow_le_pow_left hle_w 3
    have hmul : 154440 * (a352834 n) ^ 3 ≤ 154440 * wv.val ^ 3 :=
      Nat.mul_le_mul_left 154440 hle_pow
    rw [← hn_eq] at hw_lt
    omega

/-- Strict inequality away from `n = 154440`: for every `n ≥ 1` with `n ≠ 154440`,
`154440 * a(n)^3 < 840^3 * n`. -/
theorem a352834_strict_of_ne (n : ℕ) (hn : 1 ≤ n) (hne : n ≠ 154440) :
    154440 * (a352834 n) ^ 3 < 840 ^ 3 * n := by
  have hle := a352834_global_bound n hn
  refine lt_of_le_of_ne hle ?_
  intro heq
  have heq_q : ((a352834 n : ℚ) ^ 3) / (n : ℚ) = T_val := by
    unfold T_val
    have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [div_eq_div_iff hn0 (by norm_num)]
    have hcomm : (a352834 n) ^ 3 * 154440 = 840 ^ 3 * n := by linarith
    exact_mod_cast hcomm
  have hT : T_val ≤ ((a352834 n : ℚ) ^ 3) / (n : ℚ) := heq_q.ge
  obtain ⟨hk_pos, hk_eq_tau, htau_dvd, hpf, he2, he3, he5, he7, he11, he13, he17, he19⟩ :=
    candidate_constraints hn hT
  set m := a352834 n * n
  let v : Vec8 := ⟨m.factorization 2, m.factorization 3, m.factorization 5, m.factorization 7,
    m.factorization 11, m.factorization 13, m.factorization 17, m.factorization 19⟩
  have hm_pos : 1 ≤ m := Nat.succ_le_of_lt (Nat.mul_pos hk_pos hn)
  have hm_eq : v.val = m := by rw [v.val_eq]; exact val8_of_primeFactors_subset hm_pos hpf
  have htau_eq : v.tau = tau m := by rw [← v.tau_val, hm_eq]
  have hchk : checkBox240 v = true :=
    box240_sound v he2 he3 he5 he7 he11 he13 he17 he19
  have hnot_small : ¬ (154440 * v.tau ^ 4 < 840 ^ 3 * v.val) := by
    rw [hm_eq, htau_eq, ← hk_eq_tau]
    have h4 : 840 ^ 3 * m = 154440 * (a352834 n) ^ 4 := by
      have : m = a352834 n * n := rfl
      rw [this]
      nlinarith [heq]
    omega
  have hdvd_v : v.val % v.tau = 0 := by
    rw [hm_eq, htau_eq]
    exact Nat.mod_eq_zero_of_dvd htau_dvd
  unfold checkBox240 at hchk
  simp only [hnot_small, ↓reduceIte, hdvd_v, ne_eq, not_true_eq_false] at hchk
  by_cases hwin : v = winnerVec
  · have hm_win : m = 154440 * 840 := by rw [← hm_eq, hwin]; decide
    have htau_win : tau m = 840 := by rw [← htau_eq, hwin]; decide
    have : n = 154440 := by
      have hk840 : a352834 n = 840 := hk_eq_tau.trans htau_win
      rw [show m = a352834 n * n from rfl, hk840] at hm_win
      nlinarith
    exact hne this
  · have hwin_false : (v == winnerVec) = false := beq_false_of_ne hwin
    rw [ite_eq_right_iff.mpr (fun h => by simp [hwin_false] at h)] at hchk
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
    rcases hchk with ⟨⟨⟨⟨hnv_mul, hw_pos⟩, hmod0⟩, hcop_chk⟩, hw_lt⟩
    set nv := nVecOf v
    set wv := witnessVec v
    have hn_eq : n = nv.val := by
      have h1 : nv.val * tau m = a352834 n * n := by
        rw [← htau_eq, hnv_mul, hm_eq]
      rw [← hk_eq_tau, mul_comm (a352834 n) n] at h1
      exact (Nat.mul_right_cancel hk_pos h1).symm
    have hgcd : Nat.gcd (wv.add nv).tau (wv.val * nv.val) = wv.val := by
      rw [mul_comm wv.val nv.val]
      exact (gcd_eq_self_iff_dvd_and_coprime hw_pos).mpr
        ⟨Nat.dvd_of_mod_eq_zero hmod0, coprimeVec8Check_sound hcop_chk⟩
    have hvalid : IsValidA352834 n wv.val := by
      refine ⟨hw_pos, ?_⟩
      have htau_wv : tau (wv.val * n) = (wv.add nv).tau := by
        rw [hn_eq, ← wv.val_add, (wv.add nv).tau_val]
      rw [htau_wv, hn_eq]
      exact hgcd
    have hle_w : a352834 n ≤ wv.val := a352834_le_of_valid hvalid
    have hle_pow : (a352834 n) ^ 3 ≤ wv.val ^ 3 := Nat.pow_le_pow_left hle_w 3
    have hmul : 154440 * (a352834 n) ^ 3 ≤ 154440 * wv.val ^ 3 :=
      Nat.mul_le_mul_left 154440 hle_pow
    rw [← hn_eq] at hw_lt
    omega

/-- Real-valued sharp extremum: for all `n ≥ 1`,
`a(n) / n^(1/3) ≤ 840 / 154440^(1/3)`, with equality iff `n = 154440`. -/
theorem a352834_real_extremum (n : ℕ) (hn : 1 ≤ n) :
    (a352834 n : ℝ) / (n : ℝ) ^ (1 / 3 : ℝ) ≤ 840 / (154440 : ℝ) ^ (1 / 3 : ℝ) ∧
      ((a352834 n : ℝ) / (n : ℝ) ^ (1 / 3 : ℝ) = 840 / (154440 : ℝ) ^ (1 / 3 : ℝ) ↔
        n = 154440) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h154_pos : (0 : ℝ) < (154440 : ℝ) := by norm_num
  have hnr_pos : (0 : ℝ) < (n : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hn_pos _
  have h154r_pos : (0 : ℝ) < (154440 : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos h154_pos _
  have hcube_n : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]
    norm_num
  have hcube_154 : ((154440 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = 154440 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h154_pos.le]
    norm_num
  have hle_nat := a352834_global_bound n hn
  have hle_real : (a352834 n : ℝ) / (n : ℝ) ^ (1 / 3 : ℝ) ≤ 840 / (154440 : ℝ) ^ (1 / 3 : ℝ) := by
    have hpow : ((a352834 n : ℝ) / (n : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) ≤
        (840 / (154440 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by
      rw [div_pow, div_pow, hcube_n, hcube_154, div_le_div_iff₀ hn_pos h154_pos]
      have hcomm : (a352834 n) ^ 3 * 154440 ≤ 840 ^ 3 * n := by linarith
      exact_mod_cast hcomm
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hpow
  refine ⟨hle_real, ⟨fun heq => ?_, fun heq => ?_⟩⟩
  · by_contra hne
    have hlt_nat := a352834_strict_of_ne n hn hne
    have hpow_eq : ((a352834 n : ℝ) / (n : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) =
        (840 / (154440 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by rw [heq]
    rw [div_pow, div_pow, hcube_n, hcube_154, div_eq_div_iff hn_pos.ne' h154_pos.ne'] at hpow_eq
    have hlt_real : (154440 : ℝ) * (a352834 n : ℝ) ^ (3 : ℕ) < (840 : ℝ) ^ (3 : ℕ) * (n : ℝ) := by
      exact_mod_cast hlt_nat
    linarith
  · rw [heq, a352834_154440]
    norm_num

end GlobalExtremum

end OEISThreeProofs.A352834
