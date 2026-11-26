import Mathlib

/-!
# OEIS A304362: Surjectivity onto `ℤ` with Infinite Fibers

We define:
`IsPerfectPower d ↔ ∃ u s : ℕ, 2 ≤ u ∧ 2 ≤ s ∧ u ^ s = d`
`b304362 n = ∑ d ∈ n.divisors.filter (fun d => d = 1 ∨ ¬ IsPerfectPower d), μ (n / d)`

and prove:
1. `b304362_example`: `b304362 (2^36 * 3^21 * 5^15) = -4`.
2. `b304362_prime`: `b304362 p = 0` for every prime `p`.
3. `a304362_infinite_fibers`: for every `t : ℤ`, `{n : ℕ | 0 < n ∧ b304362 n = t}` is infinite
   (using the explicit Fermat–CRT exponent family `u_i = Q_i^(q_i - 1) + Q`).
-/

namespace OEISThreeProofs.A304362

open scoped BigOperators
open ArithmeticFunction

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

/-- `d` is a perfect power `u^s` with `u ≥ 2` and `s ≥ 2`. -/
def IsPerfectPower (d : ℕ) : Prop :=
  ∃ u s : ℕ, 2 ≤ u ∧ 2 ≤ s ∧ u ^ s = d

lemma isPerfectPower_iff_bounded (d : ℕ) :
    IsPerfectPower d ↔
      ∃ u ∈ Finset.range (d + 1), ∃ s ∈ Finset.range (d + 1),
        2 ≤ u ∧ 2 ≤ s ∧ u ^ s = d := by
  constructor
  · rintro ⟨u, s, hu, hs, rfl⟩
    have h1 : u ≤ u ^ s := Nat.le_self_pow (by omega) u
    have h2 : s ≤ 2 ^ s := le_of_lt Nat.lt_two_pow_self
    have h3 : 2 ^ s ≤ u ^ s := Nat.pow_le_pow_left hu s
    exact ⟨u, Finset.mem_range.mpr (by omega), s, Finset.mem_range.mpr (by omega),
      hu, hs, rfl⟩
  · rintro ⟨u, _, s, _, hu, hs, rfl⟩
    exact ⟨u, s, hu, hs, rfl⟩

instance (d : ℕ) : Decidable (IsPerfectPower d) :=
  decidable_of_iff _ (isPerfectPower_iff_bounded d).symm

lemma not_isPerfectPower_one : ¬ IsPerfectPower 1 := by
  rintro ⟨u, s, hu, hs, h⟩
  have h4 : 4 ≤ u ^ s := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) hs
      _ ≤ u ^ s := Nat.pow_le_pow_left hu s
  omega

/-- OEIS A304362: `b(n) = ∑_{d ∣ n, d = 1 ∨ ¬ IsPerfectPower d} μ(n / d)`. -/
def b304362 (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors.filter (fun d => d = 1 ∨ ¬ IsPerfectPower d),
    ArithmeticFunction.moebius (n / d)

lemma sum_divisors_moebius_div {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius (n / d)) = if n = 1 then 1 else 0 := by
  have hzeta := congrFun (congrArg (fun f : ArithmeticFunction ℤ => (f : ℕ → ℤ))
    ArithmeticFunction.coe_moebius_mul_coe_zeta) n
  rw [ArithmeticFunction.mul_apply] at hzeta
  have hrhs : ((1 : ArithmeticFunction ℤ) n) = if n = 1 then 1 else 0 := by
    simp [ArithmeticFunction.one_apply]
  rw [hrhs] at hzeta
  rw [← hzeta]
  refine Finset.sum_bij (fun d _ => (n / d, d)) ?_ ?_ ?_ ?_
  · intro d hd
    rw [Nat.mem_divisors] at hd
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨Nat.div_mul_cancel hd.1, hn.ne'⟩
  · intro d₁ _ d₂ _ h
    exact (Prod.ext_iff.mp h).2
  · rintro ⟨a, b⟩ hab
    rw [Nat.mem_divisorsAntidiagonal] at hab
    have hb0 : b ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hab
      exact hn.ne' hab.1.symm
    have hb : 0 < b := Nat.pos_of_ne_zero hb0
    refine ⟨b, Nat.mem_divisors.mpr ⟨⟨a, by rw [mul_comm, hab.1]⟩, hn.ne'⟩, ?_⟩
    ext
    · simp [← hab.1, Nat.mul_div_cancel _ hb]
    · rfl
  · intro d hd
    rw [Nat.mem_divisors] at hd
    have hd0 : d ≠ 0 := fun h0 => by simp [h0, hn.ne'] at hd
    simp [ArithmeticFunction.zeta_apply, hd0]

lemma b304362_eq_neg_sum_perfectPower {n : ℕ} (hn : 2 ≤ n) :
    b304362 n = - ∑ d ∈ n.divisors.filter IsPerfectPower, ArithmeticFunction.moebius (n / d) := by
  have hn0 : 0 < n := by omega
  have hne1 : n ≠ 1 := by omega
  have htot := sum_divisors_moebius_div hn0
  rw [ite_eq_right_iff.mpr (fun h => (hne1 h).elim)] at htot
  have hsplit :
      (∑ d ∈ n.divisors.filter IsPerfectPower, ArithmeticFunction.moebius (n / d)) +
        (∑ d ∈ n.divisors.filter (fun d => ¬ IsPerfectPower d), ArithmeticFunction.moebius (n / d)) =
      ∑ d ∈ n.divisors, ArithmeticFunction.moebius (n / d) :=
    Finset.sum_filter_add_sum_filter_not n.divisors IsPerfectPower
      (fun d => ArithmeticFunction.moebius (n / d))
  have hfilt :
      n.divisors.filter (fun d => d = 1 ∨ ¬ IsPerfectPower d) =
        n.divisors.filter (fun d => ¬ IsPerfectPower d) := by
    ext d
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    constructor
    · rintro (rfl | h)
      · exact not_isPerfectPower_one
      · exact h
    · exact fun h => Or.inr h
  unfold b304362
  rw [hfilt]
  linarith

/-- For every prime `p`, `b304362 p = 0`. -/
theorem b304362_prime {p : ℕ} (hp : p.Prime) : b304362 p = 0 := by
  rw [b304362_eq_neg_sum_perfectPower hp.two_le]
  have hfilt : p.divisors.filter IsPerfectPower = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    rcases hp.eq_one_or_self_of_dvd d hd.1.1 with rfl | hd_eq
    · exact not_isPerfectPower_one hd.2
    · rw [hd_eq] at hd
      rcases hd.2 with ⟨u, s, hu, hs, hus⟩
      have hu_dvd : u ∣ p := ⟨u ^ (s - 1), by
        calc
          p = u ^ s := hus.symm
          _ = u ^ (1 + (s - 1)) := by rw [Nat.add_sub_cancel' (by omega)]
          _ = u * u ^ (s - 1) := by rw [pow_add, pow_one]⟩
      rcases hp.eq_one_or_self_of_dvd u hu_dvd with h1 | hself
      · omega
      · have hgt : u < u ^ s := by
          calc
            u = u ^ 1 := (pow_one u).symm
            _ < u ^ s := Nat.pow_lt_pow_right (by omega) (by omega)
        omega
  simp [hfilt]

section PrimePowerForm

variable {m : ℕ} (p e : Fin m → ℕ)

/-- Divisor of `∏ k, (p k)^(e k)` obtained by decrementing exponents in `S`. -/
def dOfS (S : Finset (Fin m)) : ℕ :=
  ∏ k : Fin m, p k ^ (e k - if k ∈ S then 1 else 0)

lemma dOfS_pos (hp : ∀ k, (p k).Prime) (S : Finset (Fin m)) : 0 < dOfS p e S := by
  unfold dOfS
  exact Finset.prod_pos fun k _ => pow_pos (hp k).pos _

lemma dOfS_factorization (hp : ∀ k, (p k).Prime) (hinj : Function.Injective p)
    (S : Finset (Fin m)) (k : Fin m) :
    (dOfS p e S).factorization (p k) = e k - if k ∈ S then 1 else 0 := by
  unfold dOfS
  rw [Nat.factorization_prod (fun j _ => (pow_pos (hp j).pos _).ne')]
  simp only [Finset.sum_apply', Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul, (hp _).factorization]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    have hne : p j ≠ p k := fun h => hjk (hinj h)
    simp [hne]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

lemma dOfS_injective (hp : ∀ k, (p k).Prime) (hinj : Function.Injective p)
    (he : ∀ k, 2 ≤ e k) : Function.Injective (dOfS p e) := by
  intro S₁ S₂ h
  ext k
  have hf := congrArg (fun x => x.factorization (p k)) h
  rw [dOfS_factorization p e hp hinj S₁ k, dOfS_factorization p e hp hinj S₂ k] at hf
  have hk2 : 2 ≤ e k := he k
  by_cases h1 : k ∈ S₁ <;> by_cases h2 : k ∈ S₂ <;> simp [h1, h2] at hf ⊢ <;> omega

lemma n_div_dOfS (he : ∀ k, 2 ≤ e k) (S : Finset (Fin m)) :
    (∏ k : Fin m, p k ^ e k) = dOfS p e S * ∏ k ∈ S, p k := by
  unfold dOfS
  have hite : ∏ k : Fin m, (if k ∈ S then p k else 1) = ∏ k ∈ S, p k := by
    simp [Finset.prod_ite_mem]
  rw [← hite, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : k ∈ S
  · simp only [hk, ↓reduceIte]
    rw [← pow_succ, Nat.sub_add_cancel (by have := he k; omega)]
  · simp [hk]

lemma dOfS_dvd (he : ∀ k, 2 ≤ e k) (S : Finset (Fin m)) :
    dOfS p e S ∣ ∏ k : Fin m, p k ^ e k :=
  ⟨∏ k ∈ S, p k, n_div_dOfS p e he S⟩

lemma moebius_n_div_dOfS (hp : ∀ k, (p k).Prime) (hinj : Function.Injective p)
    (he : ∀ k, 2 ≤ e k) (S : Finset (Fin m)) :
    ArithmeticFunction.moebius ((∏ k : Fin m, p k ^ e k) / dOfS p e S) = (-1 : ℤ) ^ S.card := by
  have hd_pos := dOfS_pos p e hp S
  rw [n_div_dOfS p e he S, Nat.mul_div_cancel_left _ hd_pos]
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (hp i).coprime_iff_not_dvd.mpr fun hdvd =>
      hij (hinj ((Nat.prime_dvd_prime_iff_eq (hp i) (hp j)).mp hdvd))
  rw [ArithmeticFunction.isMultiplicative_moebius.map_prod p S (fun i _ j _ hij => hcop hij)]
  simp only [ArithmeticFunction.moebius_apply_prime (hp _), Finset.prod_const]

lemma isPerfectPower_dOfS_iff (hm : 0 < m) (hp : ∀ k, (p k).Prime) (hinj : Function.Injective p)
    (he : ∀ k, 2 ≤ e k) (S : Finset (Fin m)) :
    IsPerfectPower (dOfS p e S) ↔
      ∃ q : ℕ, q.Prime ∧ ∀ k : Fin m, q ∣ (e k - if k ∈ S then 1 else 0) := by
  constructor
  · rintro ⟨u, s, hu, hs, hus⟩
    let q := s.minFac
    have hq : q.Prime := Nat.minFac_prime (by omega)
    have hqs : q ∣ s := Nat.minFac_dvd s
    refine ⟨q, hq, fun k => ?_⟩
    have hf := congrArg (fun x => x.factorization (p k)) hus
    rw [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      dOfS_factorization p e hp hinj S k] at hf
    exact dvd_trans hqs ⟨u.factorization (p k), hf.symm⟩
  · rintro ⟨q, hq, hdvd⟩
    let u := ∏ k : Fin m, p k ^ ((e k - if k ∈ S then 1 else 0) / q)
    refine ⟨u, q, ?_, hq.two_le, ?_⟩
    · have k0 : Fin m := ⟨0, hm⟩
      have ha0 : 1 ≤ e k0 - if k0 ∈ S then 1 else 0 := by
        have := he k0
        split_ifs <;> omega
      have hq_le : 1 ≤ (e k0 - if k0 ∈ S then 1 else 0) / q := by
        rcases hdvd k0 with ⟨c, hc⟩
        have hc0 : c ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hc
          omega
        rw [hc, Nat.mul_div_cancel_left _ hq.pos]
        omega
      have hdiv : p k0 ∣ u := by
        refine dvd_trans ⟨p k0 ^ ((e k0 - if k0 ∈ S then 1 else 0) / q - 1), ?_⟩
          (Finset.dvd_prod_of_mem _ (Finset.mem_univ k0))
        rw [← pow_succ', Nat.sub_add_cancel hq_le]
      exact le_trans (hp k0).two_le (Nat.le_of_dvd (Finset.prod_pos fun k _ => pow_pos (hp k).pos _) hdiv)
    · unfold u dOfS
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← pow_mul, Nat.div_mul_cancel (hdvd k)]

lemma b304362_prime_powers (hm : 0 < m) (hp : ∀ k, (p k).Prime) (hinj : Function.Injective p)
    (he : ∀ k, 2 ≤ e k) :
    b304362 (∏ k : Fin m, p k ^ e k) =
      - ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => IsPerfectPower (dOfS p e S)),
          (-1 : ℤ) ^ S.card := by
  set n := ∏ k : Fin m, p k ^ e k
  have hn_pos : 0 < n := Finset.prod_pos fun k _ => pow_pos (hp k).pos _
  have k0 : Fin m := ⟨0, hm⟩
  have h2n : 2 ≤ n := by
    have hp0 : p k0 ^ e k0 ∣ n := Finset.dvd_prod_of_mem _ (Finset.mem_univ k0)
    have h4 : 2 ≤ p k0 ^ e k0 := le_trans (hp k0).two_le (Nat.le_self_pow (by have := he k0; omega) _)
    exact le_trans h4 (Nat.le_of_dvd hn_pos hp0)
  rw [b304362_eq_neg_sum_perfectPower h2n]
  congr 1
  have hzero :
      ∀ d ∈ n.divisors.filter IsPerfectPower,
        d ∉ (Finset.univ.filter (fun S : Finset (Fin m) => IsPerfectPower (dOfS p e S))).image (dOfS p e) →
          ArithmeticFunction.moebius (n / d) = 0 := by
    intro d hd hnot
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    set q := n / d
    have hqn : q ∣ n := Nat.div_dvd_of_dvd hd.1.1
    have hq0 : q ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn_pos hd.1.1) (Nat.pos_of_dvd_of_pos hd.1.1 hn_pos)).ne'
    have hq_fac : ∀ r ∈ q.primeFactors, r ∈ Finset.univ.image p := by
      intro r hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrn : r ∣ n := dvd_trans (Nat.dvd_of_mem_primeFactors hr) hqn
      rcases prime_dvd_finset_prod hrp hrn with ⟨k, _, hk⟩
      have hrpk : r ∣ p k := hrp.dvd_of_dvd_pow hk
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k,
        ((Nat.prime_dvd_prime_iff_eq hrp (hp k)).mp hrpk).symm⟩
    have hq_eq : q = ∏ k : Fin m, p k ^ (q.factorization (p k)) := by
      have hq_fac_prod : q = ∏ r ∈ q.primeFactors, r ^ q.factorization r :=
        Nat.prod_primeFactors_pow_factorization hq0
      conv_lhs => rw [hq_fac_prod]
      have himg : (∏ r ∈ Finset.univ.image p, r ^ q.factorization r) =
          ∏ k : Fin m, p k ^ q.factorization (p k) :=
        Finset.prod_image (fun i _ j _ hij => hinj hij)
      rw [← himg]
      refine Finset.prod_subset (f := fun r => r ^ q.factorization r)
        (Finset.subset_iff.mpr hq_fac) fun r _ hr => ?_
      by_cases hrp : r.Prime
      · have hnd : ¬ r ∣ q := fun h => hr (Nat.mem_primeFactors.mpr ⟨hrp, h, hq0⟩)
        simp [Nat.factorization_eq_zero_of_not_dvd hnd]
      · simp [Nat.factorization_eq_zero_of_not_prime q hrp]
    by_cases hle1 : ∀ k : Fin m, q.factorization (p k) ≤ 1
    · exfalso
      apply hnot
      let S : Finset (Fin m) := Finset.univ.filter (fun k => q.factorization (p k) = 1)
      have hqS : q = ∏ k ∈ S, p k := by
        have hite : (∏ k : Fin m, p k ^ q.factorization (p k)) =
            ∏ k : Fin m, (if k ∈ S then p k else 1) := by
          refine Finset.prod_congr rfl fun k _ => ?_
          have hk1 := hle1 k
          by_cases hkS : k ∈ S
          · have : q.factorization (p k) = 1 := (Finset.mem_filter.mp hkS).2
            simp [hkS, this]
          · have : q.factorization (p k) = 0 := by
              have hne : q.factorization (p k) ≠ 1 := fun h => hkS (Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩)
              omega
            simp [hkS, this]
        rw [hq_eq, hite]
        simp [Finset.prod_ite_mem]
      have hd_eq : d = dOfS p e S := by
        have hmul1 : d * q = n := Nat.mul_div_cancel' hd.1.1
        have hmul2 : dOfS p e S * q = n := by rw [hqS, ← n_div_dOfS p e he S]
        exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hq0) (hmul1.trans hmul2.symm)
      rw [Finset.mem_image]
      refine ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, ?_⟩, hd_eq.symm⟩
      simpa [hd_eq] using hd.2
    · push Not at hle1
      rcases hle1 with ⟨k, hk2⟩
      have hcop_q : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).Pairwise
          (Function.onFun Nat.Coprime (fun j => p j ^ q.factorization (p j))) := by
        intro i _ j _ hij
        exact ((hp i).coprime_iff_not_dvd.mpr fun h =>
          hij (hinj ((Nat.prime_dvd_prime_iff_eq (hp i) (hp j)).mp h))).pow _ _
      rw [hq_eq, ArithmeticFunction.isMultiplicative_moebius.map_prod
        (fun j => p j ^ q.factorization (p j)) Finset.univ hcop_q]
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      rw [ArithmeticFunction.moebius_apply_prime_pow (hp k) (by omega),
        ite_eq_right_iff.mpr (fun h => by omega)]
  have hsub :
      (Finset.univ.filter (fun S : Finset (Fin m) => IsPerfectPower (dOfS p e S))).image (dOfS p e) ⊆
        n.divisors.filter IsPerfectPower := by
    intro d hd
    rw [Finset.mem_image] at hd
    rcases hd with ⟨S, hS, rfl⟩
    rw [Finset.mem_filter] at hS ⊢
    exact ⟨Nat.mem_divisors.mpr ⟨dOfS_dvd p e he S, hn_pos.ne'⟩, hS.2⟩
  rw [← Finset.sum_subset hsub hzero,
    Finset.sum_image (fun S₁ _ S₂ _ h => dOfS_injective p e hp hinj he h)]
  refine Finset.sum_congr rfl fun S _ => ?_
  exact moebius_n_div_dOfS p e hp hinj he S

end PrimePowerForm

/-- Concrete example from the note: `b304362 (2^36 * 3^21 * 5^15) = -4`. -/
theorem b304362_example : b304362 (2 ^ 36 * 3 ^ 21 * 5 ^ 15) = -4 := by
  let p : Fin 3 → ℕ := ![2, 3, 5]
  let e : Fin 3 → ℕ := ![36, 21, 15]
  have hp : ∀ k : Fin 3, (p k).Prime := by
    intro k; fin_cases k <;> decide
  have hinj : Function.Injective p := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp [p] at h ⊢
  have he : ∀ k : Fin 3, 2 ≤ e k := by
    intro k; fin_cases k <;> decide
  have hn : 2 ^ 36 * 3 ^ 21 * 5 ^ 15 = ∏ k : Fin 3, p k ^ e k := by
    simp [Fin.prod_univ_three, p, e]
  rw [hn, b304362_prime_powers p e (by omega) hp hinj he]
  have hiff : ∀ S : Finset (Fin 3),
      IsPerfectPower (dOfS p e S) ↔
        S = ∅ ∨ S = {0, 1} ∨ S = {0, 2} ∨ S = {1, 2} := by
    intro S
    rw [isPerfectPower_dOfS_iff p e (by omega) hp hinj he S]
    constructor
    · rintro ⟨q, hq, hdvd⟩
      have h0 := hdvd 0
      have h1 := hdvd 1
      have h2 := hdvd 2
      simp only [e, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2
      have hq2 := hq.two_le
      by_cases b0 : (0 : Fin 3) ∈ S <;>
        by_cases b1 : (1 : Fin 3) ∈ S <;>
        by_cases b2 : (2 : Fin 3) ∈ S
      · simp only [b0, b1, b2, ↓reduceIte] at h0 h1 h2
        have : q ∣ Nat.gcd 35 (Nat.gcd 20 14) := Nat.dvd_gcd h0 (Nat.dvd_gcd h1 h2)
        norm_num at this; omega
      · right; left; ext x; fin_cases x <;> simp [b0, b1, b2]
      · right; right; left; ext x; fin_cases x <;> simp [b0, b1, b2]
      · simp only [b0, b1, b2, ↓reduceIte] at h0 h1 h2
        have : q ∣ Nat.gcd 35 (Nat.gcd 21 15) := Nat.dvd_gcd h0 (Nat.dvd_gcd h1 h2)
        norm_num at this; omega
      · right; right; right; ext x; fin_cases x <;> simp [b0, b1, b2]
      · simp only [b0, b1, b2, ↓reduceIte] at h0 h1 h2
        have : q ∣ Nat.gcd 36 (Nat.gcd 20 15) := Nat.dvd_gcd h0 (Nat.dvd_gcd h1 h2)
        norm_num at this; omega
      · simp only [b0, b1, b2, ↓reduceIte] at h0 h1 h2
        have : q ∣ Nat.gcd 36 (Nat.gcd 21 14) := Nat.dvd_gcd h0 (Nat.dvd_gcd h1 h2)
        norm_num at this; omega
      · left; ext x; fin_cases x <;> simp [b0, b1, b2]
    · rintro (rfl | rfl | rfl | rfl)
      · refine ⟨3, by decide, fun k => ?_⟩; fin_cases k <;> decide
      · refine ⟨5, by decide, fun k => ?_⟩; fin_cases k <;> decide
      · refine ⟨7, by decide, fun k => ?_⟩; fin_cases k <;> decide
      · refine ⟨2, by decide, fun k => ?_⟩; fin_cases k <;> decide
  have hfilt :
      Finset.univ.filter (fun S : Finset (Fin 3) => IsPerfectPower (dOfS p e S)) =
        {∅, {0, 1}, {0, 2}, {1, 2}} := by
    ext S
    rw [Finset.mem_filter, and_iff_right (Finset.mem_univ S), hiff S]
    simp [Finset.mem_insert, Finset.mem_singleton]
  rw [hfilt]
  decide

section Construction

private noncomputable def qPrime (i : ℕ) : ℕ := Nat.nth Nat.Prime i

private lemma qPrime_prime (i : ℕ) : (qPrime i).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i

private lemma qPrime_strictMono : StrictMono qPrime :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

private lemma qPrime_zero : qPrime 0 = 2 :=
  Nat.nth_prime_zero_eq_two

private lemma lt_qPrime (i : ℕ) : i < qPrime i := by
  induction i with
  | zero => simp [qPrime_zero]
  | succ i ih =>
    have hlt : qPrime i < qPrime (i + 1) := qPrime_strictMono (Nat.lt_succ_self i)
    omega

private lemma exists_strictMono_primes_gt (m M : ℕ) :
    ∃ p : Fin m → ℕ, (∀ k, (p k).Prime) ∧ (∀ k, M < p k) ∧ StrictMono p := by
  refine ⟨fun k => qPrime (M + k.1), fun k => qPrime_prime _, fun k => ?_, fun i j hij => ?_⟩
  · have h := lt_qPrime (M + k.1)
    exact lt_of_le_of_lt (Nat.le_add_right M k.1) h
  · exact qPrime_strictMono (Nat.add_lt_add_left hij M)

private noncomputable def Q_prod (r : ℕ) : ℕ := ∏ i : Fin r, qPrime i.1

private noncomputable def Qi_prod (r : ℕ) (i : Fin r) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, qPrime j.1

private noncomputable def u_exp (r : ℕ) (i : Fin r) : ℕ :=
  (Qi_prod r i) ^ (qPrime i.1 - 1) + Q_prod r

private lemma Q_prod_even {r : ℕ} (hr : 1 ≤ r) : 2 ∣ Q_prod r := by
  have h0 : qPrime 0 ∣ Q_prod r :=
    Finset.dvd_prod_of_mem (fun i : Fin r => qPrime i.1) (Finset.mem_univ ⟨0, hr⟩)
  simpa [qPrime_zero] using h0

private lemma Q_prod_ge_two {r : ℕ} (hr : 1 ≤ r) : 2 ≤ Q_prod r :=
  Nat.le_of_dvd (Finset.prod_pos fun i _ => (qPrime_prime i.1).pos) (Q_prod_even hr)

private lemma u_exp_ge_two {r : ℕ} (hr : 1 ≤ r) (i : Fin r) : 2 ≤ u_exp r i := by
  unfold u_exp
  have := Q_prod_ge_two hr
  omega

private lemma q_dvd_Q_prod {r : ℕ} (i : Fin r) : qPrime i.1 ∣ Q_prod r :=
  Finset.dvd_prod_of_mem (fun j : Fin r => qPrime j.1) (Finset.mem_univ i)

private lemma q_dvd_Qi_prod {r : ℕ} {i j : Fin r} (hij : j ≠ i) :
    qPrime j.1 ∣ Qi_prod r i :=
  Finset.dvd_prod_of_mem (fun k : Fin r => qPrime k.1)
    (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩)

private lemma coprime_Qi_q {r : ℕ} (i : Fin r) : Nat.Coprime (Qi_prod r i) (qPrime i.1) := by
  rw [Nat.coprime_comm, (qPrime_prime i.1).coprime_iff_not_dvd]
  intro hdvd
  rcases prime_dvd_finset_prod (qPrime_prime i.1) hdvd with ⟨j, hj, hjdvd⟩
  rw [Finset.mem_erase] at hj
  have heq := (Nat.prime_dvd_prime_iff_eq (qPrime_prime i.1) (qPrime_prime j.1)).mp hjdvd
  exact hj.1 (Fin.ext (qPrime_strictMono.injective heq.symm))

private lemma q_dvd_u_sub_one {r : ℕ} (i : Fin r) : qPrime i.1 ∣ (u_exp r i - 1) := by
  unfold u_exp
  have hpos : 1 ≤ (Qi_prod r i) ^ (qPrime i.1 - 1) :=
    Nat.one_le_pow _ _ (Finset.prod_pos fun j _ => (qPrime_prime j.1).pos)
  have hmod : (Qi_prod r i) ^ (qPrime i.1 - 1) ≡ 1 [MOD qPrime i.1] := by
    rw [← Nat.totient_prime (qPrime_prime i.1)]
    exact Nat.ModEq.pow_totient (coprime_Qi_q i)
  have hq1 : qPrime i.1 ∣ (Qi_prod r i) ^ (qPrime i.1 - 1) - 1 :=
    (Nat.modEq_iff_dvd' hpos).mp hmod.symm
  have hadd : (Qi_prod r i) ^ (qPrime i.1 - 1) + Q_prod r - 1 =
      ((Qi_prod r i) ^ (qPrime i.1 - 1) - 1) + Q_prod r := by omega
  rw [hadd]
  exact dvd_add hq1 (q_dvd_Q_prod i)

private lemma not_q_dvd_u {r : ℕ} (i : Fin r) : ¬ qPrime i.1 ∣ u_exp r i := by
  intro hdvd
  have h1 := q_dvd_u_sub_one i
  have hpos : 1 ≤ u_exp r i := by
    unfold u_exp
    have := Nat.one_le_pow (qPrime i.1 - 1) (Qi_prod r i)
      (Finset.prod_pos fun j _ => (qPrime_prime j.1).pos)
    omega
  have hq1 : qPrime i.1 ∣ 1 := by
    have : u_exp r i = (u_exp r i - 1) + 1 := (Nat.sub_add_cancel hpos).symm
    exact (Nat.dvd_add_right h1).mp (this ▸ hdvd)
  exact (qPrime_prime i.1).not_dvd_one hq1

private lemma q_dvd_u_of_ne {r : ℕ} {i j : Fin r} (hij : j ≠ i) : qPrime j.1 ∣ u_exp r i := by
  unfold u_exp
  have hpow : qPrime j.1 ∣ (Qi_prod r i) ^ (qPrime i.1 - 1) :=
    dvd_pow (q_dvd_Qi_prod hij) (Nat.sub_ne_zero_of_lt (qPrime_prime i.1).one_lt)
  exact dvd_add hpow (q_dvd_Q_prod j)

private lemma not_q_dvd_u_sub_one_of_ne {r : ℕ} {i j : Fin r} (hij : j ≠ i) :
    ¬ qPrime j.1 ∣ (u_exp r i - 1) := by
  intro hdvd
  have h1 := q_dvd_u_of_ne hij
  have hpos : 1 ≤ u_exp r i := by
    unfold u_exp
    have := Nat.one_le_pow (qPrime i.1 - 1) (Qi_prod r i)
      (Finset.prod_pos fun k _ => (qPrime_prime k.1).pos)
    omega
  have hq1 : qPrime j.1 ∣ 1 := by
    have : u_exp r i = (u_exp r i - 1) + 1 := (Nat.sub_add_cancel hpos).symm
    exact (Nat.dvd_add_right hdvd).mp (this ▸ h1)
  exact (qPrime_prime j.1).not_dvd_one hq1

private lemma not_dvd_Q_sub_one_two_Q {r : ℕ} (hr : 1 ≤ r) {q : ℕ} (hq : q.Prime)
    (hqa : q ∣ Q_prod r - 1) (hqb : q ∣ 2 * Q_prod r) : False := by
  have hQ2 := Q_prod_ge_two hr
  rcases hq.dvd_mul.mp hqb with hq2 | hqQ
  · have hq_eq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2
    have hqQ : q ∣ Q_prod r := hq_eq2 ▸ Q_prod_even hr
    have h1 : q ∣ 1 := by
      have : Q_prod r = (Q_prod r - 1) + 1 := by omega
      exact (Nat.dvd_add_right hqa).mp (this ▸ hqQ)
    exact hq.not_dvd_one h1
  · have h1 : q ∣ 1 := by
      have : Q_prod r = (Q_prod r - 1) + 1 := by omega
      exact (Nat.dvd_add_right hqa).mp (this ▸ hqQ)
    exact hq.not_dvd_one h1

private lemma not_dvd_Q_two_Q_sub_one {r : ℕ} (hr : 1 ≤ r) {q : ℕ} (hq : q.Prime)
    (hqa : q ∣ Q_prod r) (hqb : q ∣ 2 * Q_prod r - 1) : False := by
  have hQ2 := Q_prod_ge_two hr
  have h2Q : q ∣ 2 * Q_prod r := dvd_mul_of_dvd_right hqa 2
  have h1 : q ∣ 1 := by
    have : 2 * Q_prod r = (2 * Q_prod r - 1) + 1 := by omega
    exact (Nat.dvd_add_right hqb).mp (this ▸ h2Q)
  exact hq.not_dvd_one h1

private lemma not_dvd_Q_sub_one_two_Q_sub_one {r : ℕ} (hr : 1 ≤ r) {q : ℕ} (hq : q.Prime)
    (hqa : q ∣ Q_prod r - 1) (hqb : q ∣ 2 * Q_prod r - 1) : False := by
  have hQ2 := Q_prod_ge_two hr
  have h2 : q ∣ 2 * (Q_prod r - 1) := dvd_mul_of_dvd_right hqa 2
  have h1 : q ∣ 1 := by
    have : 2 * Q_prod r - 1 = 2 * (Q_prod r - 1) + 1 := by omega
    exact (Nat.dvd_add_right h2).mp (this ▸ hqb)
  exact hq.not_dvd_one h1

private lemma dvd_Q_prod_prime {r : ℕ} {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Q_prod r) :
    ∃ i : Fin r, q = qPrime i.1 := by
  rcases prime_dvd_finset_prod hq hdvd with ⟨i, _, hi⟩
  exact ⟨i, (Nat.prime_dvd_prime_iff_eq hq (qPrime_prime i.1)).mp hi⟩

/-- For every `r ≥ 1` and bound `M`, there exists `n > M` with `b304362 n = r`. -/
lemma exists_pos_gt (r : ℕ) (hr : 1 ≤ r) (M : ℕ) :
    ∃ n : ℕ, M < n ∧ b304362 n = (r : ℤ) := by
  obtain ⟨p, hp, hgt, hmono⟩ := exists_strictMono_primes_gt (r + 2) M
  let e : Fin (r + 2) → ℕ := fun k =>
    if k.1 = 0 then Q_prod r
    else if k.1 = 1 then 2 * Q_prod r
    else u_exp r ⟨k.1 - 2, by omega⟩
  have hQ2 := Q_prod_ge_two hr
  have he : ∀ k, 2 ≤ e k := by
    intro k
    dsimp [e]
    split_ifs with h0 h1
    · exact hQ2
    · omega
    · exact u_exp_ge_two hr _
  let n := ∏ k : Fin (r + 2), p k ^ e k
  have hn_gt : M < n := by
    have k0 : Fin (r + 2) := ⟨0, by omega⟩
    have hdvd : p k0 ^ e k0 ∣ n := Finset.dvd_prod_of_mem _ (Finset.mem_univ k0)
    have hn_pos : 0 < n := Finset.prod_pos fun k _ => pow_pos (hp k).pos _
    have hp0 : M < p k0 := hgt k0
    have hpow : p k0 ≤ p k0 ^ e k0 := Nat.le_self_pow (by have := he k0; omega) _
    have hle : p k0 ^ e k0 ≤ n := Nat.le_of_dvd hn_pos hdvd
    omega
  refine ⟨n, hn_gt, ?_⟩
  rw [show n = ∏ k : Fin (r + 2), p k ^ e k from rfl]
  rw [b304362_prime_powers p e (by omega) hp hmono.injective he]
  let idx : Fin r → Fin (r + 2) := fun i => ⟨i.1 + 2, by omega⟩
  have hiff : ∀ S : Finset (Fin (r + 2)),
      IsPerfectPower (dOfS p e S) ↔ ∃ i : Fin r, S = {idx i} := by
    intro S
    rw [isPerfectPower_dOfS_iff p e (by omega) hp hmono.injective he S]
    constructor
    · rintro ⟨q, hq, hdvd⟩
      let k0 : Fin (r + 2) := ⟨0, by omega⟩
      let k1 : Fin (r + 2) := ⟨1, by omega⟩
      have h0 := hdvd k0
      have h1 := hdvd k1
      dsimp [e] at h0 h1
      simp only [show k0.1 = 0 from rfl, ↓reduceIte] at h0
      simp only [show k1.1 ≠ 0 by simp [k1], show k1.1 = 1 from rfl, ↓reduceIte] at h1
      have h00 : ¬ k0 ∈ S := by
        intro hmem
        simp only [hmem, ↓reduceIte] at h0
        by_cases h1mem : k1 ∈ S
        · simp only [h1mem, ↓reduceIte] at h1
          exact not_dvd_Q_sub_one_two_Q_sub_one hr hq h0 h1
        · simp only [h1mem, ↓reduceIte, Nat.sub_zero] at h1
          exact not_dvd_Q_sub_one_two_Q hr hq h0 h1
      have h11 : ¬ k1 ∈ S := by
        intro hmem
        simp only [h00, ↓reduceIte, Nat.sub_zero] at h0
        simp only [hmem, ↓reduceIte] at h1
        exact not_dvd_Q_two_Q_sub_one hr hq h0 h1
      simp only [h00, ↓reduceIte, Nat.sub_zero] at h0
      obtain ⟨i, hqi⟩ := dvd_Q_prod_prime hq h0
      refine ⟨i, ?_⟩
      ext k
      rw [Finset.mem_singleton]
      constructor
      · intro hkS
        have hk0 : k ≠ k0 := fun heq => h00 (heq ▸ hkS)
        have hk1 : k ≠ k1 := fun heq => h11 (heq ▸ hkS)
        have hk_ge : 2 ≤ k.1 := by
          have : k.1 ≠ 0 := fun h => hk0 (Fin.ext h)
          have : k.1 ≠ 1 := fun h => hk1 (Fin.ext h)
          omega
        let j : Fin r := ⟨k.1 - 2, by omega⟩
        have hkj : k = idx j := Fin.ext (by dsimp [idx, j]; omega)
        have hdk := hdvd k
        dsimp [e] at hdk
        simp only [show k.1 ≠ 0 by omega, show k.1 ≠ 1 by omega, ↓reduceIte, hkS] at hdk
        rw [hqi] at hdk
        have hji : j = i := by
          by_contra hne
          exact not_q_dvd_u_sub_one_of_ne (Ne.symm hne) hdk
        rw [hkj, hji]
      · rintro rfl
        by_contra hnot
        have hdk := hdvd (idx i)
        dsimp only [e, idx] at hdk
        rw [ite_eq_right_iff.mpr (fun h => absurd h hnot), Nat.sub_zero] at hdk
        simp only [show i.1 + 2 ≠ 0 by omega, show i.1 + 2 ≠ 1 by omega, ↓reduceIte] at hdk
        have hidx_eq : (⟨i.1 + 2 - 2, by omega⟩ : Fin r) = i := Fin.ext (by simp)
        rw [hidx_eq, hqi] at hdk
        exact not_q_dvd_u i hdk
    · rintro ⟨i, rfl⟩
      refine ⟨qPrime i.1, qPrime_prime i.1, fun k => ?_⟩
      dsimp only [e]
      by_cases hk0 : k.1 = 0
      · have hkS : k ∉ ({idx i} : Finset (Fin (r + 2))) := by
          rw [Finset.mem_singleton]
          intro h; have hv := congrArg Fin.val h; simp [idx] at hv; omega
        simp only [hk0, ↓reduceIte, hkS, Nat.sub_zero]
        exact q_dvd_Q_prod i
      · by_cases hk1 : k.1 = 1
        · have hkS : k ∉ ({idx i} : Finset (Fin (r + 2))) := by
            rw [Finset.mem_singleton]
            intro h; have hv := congrArg Fin.val h; simp [idx] at hv; omega
          simp only [hk0, hk1, ↓reduceIte, hkS, Nat.sub_zero]
          exact dvd_mul_of_dvd_right (q_dvd_Q_prod i) 2
        · simp only [hk0, hk1, ↓reduceIte]
          by_cases hkS : k ∈ ({idx i} : Finset (Fin (r + 2)))
          · simp only [hkS, ↓reduceIte]
            rw [Finset.mem_singleton] at hkS
            have hki : (⟨k.1 - 2, by omega⟩ : Fin r) = i := by
              have hv : k.1 = i.1 + 2 := by simpa [idx] using congrArg Fin.val hkS
              ext; simp [hv]
            rw [hki]
            exact q_dvd_u_sub_one i
          · simp only [hkS, ↓reduceIte, Nat.sub_zero]
            rw [Finset.mem_singleton] at hkS
            have hne : i ≠ ⟨k.1 - 2, by omega⟩ := by
              intro heq; apply hkS
              have hv : i.1 = k.1 - 2 := by simpa using congrArg Fin.val heq
              have hk2 : 2 ≤ k.1 := by omega
              ext; simp [idx]; omega
            exact q_dvd_u_of_ne hne
  have hfilt :
      Finset.univ.filter (fun S : Finset (Fin (r + 2)) => IsPerfectPower (dOfS p e S)) =
        Finset.univ.image (fun i : Fin r => ({idx i} : Finset (Fin (r + 2)))) := by
    ext S
    rw [Finset.mem_filter, and_iff_right (Finset.mem_univ S), hiff S, Finset.mem_image]
    simp [eq_comm]
  rw [hfilt, Finset.sum_image]
  · simp
  · intro i _ j _ hij
    have := Finset.singleton_injective hij
    ext; have := congrArg Fin.val this; dsimp [idx] at this; omega

/-- For every `r ≥ 1` and bound `M`, there exists `n > M` with `b304362 n = -r`. -/
lemma exists_neg_gt (r : ℕ) (hr : 1 ≤ r) (M : ℕ) :
    ∃ n : ℕ, M < n ∧ b304362 n = -(r : ℤ) := by
  obtain ⟨p, hp, hgt, hmono⟩ := exists_strictMono_primes_gt (r + 3) M
  let e : Fin (r + 3) → ℕ := fun k =>
    if _h0 : k.1 = 0 then Q_prod r
    else if _h1 : k.1 = 1 then 2 * Q_prod r
    else if hlt : k.1 < r + 2 then u_exp r ⟨k.1 - 2, by omega⟩
    else Q_prod r + 1
  have hQ2 := Q_prod_ge_two hr
  have he : ∀ k, 2 ≤ e k := by
    intro k
    dsimp [e]
    split_ifs <;> first | exact hQ2 | omega | exact u_exp_ge_two hr _
  let n := ∏ k : Fin (r + 3), p k ^ e k
  have hn_gt : M < n := by
    have k0 : Fin (r + 3) := ⟨0, by omega⟩
    have hdvd : p k0 ^ e k0 ∣ n := Finset.dvd_prod_of_mem _ (Finset.mem_univ k0)
    have hn_pos : 0 < n := Finset.prod_pos fun k _ => pow_pos (hp k).pos _
    have hp0 : M < p k0 := hgt k0
    have hpow : p k0 ≤ p k0 ^ e k0 := Nat.le_self_pow (by have := he k0; omega) _
    have hle : p k0 ^ e k0 ≤ n := Nat.le_of_dvd hn_pos hdvd
    omega
  refine ⟨n, hn_gt, ?_⟩
  rw [show n = ∏ k : Fin (r + 3), p k ^ e k from rfl]
  rw [b304362_prime_powers p e (by omega) hp hmono.injective he]
  let idx : Fin r → Fin (r + 3) := fun i => ⟨i.1 + 2, by omega⟩
  let kLast : Fin (r + 3) := ⟨r + 2, by omega⟩
  have hiff : ∀ S : Finset (Fin (r + 3)),
      IsPerfectPower (dOfS p e S) ↔ ∃ i : Fin r, S = {idx i, kLast} := by
    intro S
    rw [isPerfectPower_dOfS_iff p e (by omega) hp hmono.injective he S]
    constructor
    · rintro ⟨q, hq, hdvd⟩
      let k0 : Fin (r + 3) := ⟨0, by omega⟩
      let k1 : Fin (r + 3) := ⟨1, by omega⟩
      have h0 := hdvd k0
      have h1 := hdvd k1
      dsimp [e] at h0 h1
      simp only [show k0.1 = 0 from rfl, ↓reduceIte] at h0
      simp only [show k1.1 ≠ 0 by simp [k1], show k1.1 = 1 from rfl, ↓reduceIte] at h1
      have h00 : ¬ k0 ∈ S := by
        intro hmem
        simp only [hmem, ↓reduceIte] at h0
        by_cases h1mem : k1 ∈ S
        · simp only [h1mem, ↓reduceIte] at h1
          exact not_dvd_Q_sub_one_two_Q_sub_one hr hq h0 h1
        · simp only [h1mem, ↓reduceIte, Nat.sub_zero] at h1
          exact not_dvd_Q_sub_one_two_Q hr hq h0 h1
      have h11 : ¬ k1 ∈ S := by
        intro hmem
        simp only [h00, ↓reduceIte, Nat.sub_zero] at h0
        simp only [hmem, ↓reduceIte] at h1
        exact not_dvd_Q_two_Q_sub_one hr hq h0 h1
      simp only [h00, ↓reduceIte, Nat.sub_zero] at h0
      obtain ⟨i, hqi⟩ := dvd_Q_prod_prime hq h0
      have hLastMem : kLast ∈ S := by
        by_contra hnot
        have hdl := hdvd kLast
        dsimp only [e, kLast] at hdl
        rw [ite_eq_right_iff.mpr (fun h => absurd h hnot), Nat.sub_zero] at hdl
        simp only [show r + 2 ≠ 0 by omega, show r + 2 ≠ 1 by omega,
          lt_self_iff_false, ↓reduceIte] at hdl
        rw [hqi] at hdl
        have hqQ : qPrime i.1 ∣ Q_prod r := q_dvd_Q_prod i
        have h1 : qPrime i.1 ∣ 1 := (Nat.dvd_add_right hqQ).mp hdl
        exact (qPrime_prime i.1).not_dvd_one h1
      refine ⟨i, ?_⟩
      ext k
      rw [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hkS
        by_cases hkl : k = kLast
        · right; exact hkl
        · left
          have hk0 : k ≠ k0 := fun heq => h00 (heq ▸ hkS)
          have hk1 : k ≠ k1 := fun heq => h11 (heq ▸ hkS)
          have hk_lt : k.1 < r + 2 := by
            have hk_ne : k.1 ≠ r + 2 := fun heq => hkl (Fin.ext heq)
            omega
          have hk_ge : 2 ≤ k.1 := by
            have : k.1 ≠ 0 := fun h => hk0 (Fin.ext h)
            have : k.1 ≠ 1 := fun h => hk1 (Fin.ext h)
            omega
          let j : Fin r := ⟨k.1 - 2, by omega⟩
          have hkj : k = idx j := Fin.ext (by dsimp [idx, j]; omega)
          have hdk := hdvd k
          dsimp [e] at hdk
          simp only [show k.1 ≠ 0 by omega, show k.1 ≠ 1 by omega, hk_lt, ↓reduceIte, hkS] at hdk
          rw [hqi] at hdk
          have hji : j = i := by
            by_contra hne
            exact not_q_dvd_u_sub_one_of_ne (Ne.symm hne) hdk
          rw [hkj, hji]
      · rintro (rfl | rfl)
        · by_contra hnot
          have hdk := hdvd (idx i)
          have hne0 : (idx i).1 ≠ 0 := by simp [idx]
          have hne1 : (idx i).1 ≠ 1 := by simp [idx]
          have hlt2 : (idx i).1 < r + 2 := by simp [idx]
          have hdk' : q ∣ e (idx i) := by
            rw [ite_eq_right_iff.mpr (fun h => absurd h hnot), Nat.sub_zero] at hdk
            exact hdk
          have he_idx : e (idx i) = u_exp r i := by
            dsimp only [e]
            split_ifs <;> first | contradiction | congr 1
          rw [he_idx, hqi] at hdk'
          exact not_q_dvd_u i hdk'
        · exact hLastMem
    · rintro ⟨i, rfl⟩
      refine ⟨qPrime i.1, qPrime_prime i.1, fun k => ?_⟩
      dsimp only [e]
      by_cases hk0 : k.1 = 0
      · have hkS : k ∉ ({idx i, kLast} : Finset (Fin (r + 3))) := by
          rw [Finset.mem_insert, Finset.mem_singleton]
          rintro (h | h) <;> (have hv := congrArg Fin.val h; simp [idx, kLast] at hv; omega)
        simp only [hk0, ↓reduceIte, hkS, Nat.sub_zero]
        exact q_dvd_Q_prod i
      · by_cases hk1 : k.1 = 1
        · have hkS : k ∉ ({idx i, kLast} : Finset (Fin (r + 3))) := by
            rw [Finset.mem_insert, Finset.mem_singleton]
            rintro (h | h) <;> (have hv := congrArg Fin.val h; simp [idx, kLast] at hv; omega)
          simp only [hk0, hk1, ↓reduceIte, hkS, Nat.sub_zero]
          exact dvd_mul_of_dvd_right (q_dvd_Q_prod i) 2
        · by_cases hklt : k.1 < r + 2
          · simp only [hk0, hk1, hklt, ↓reduceIte]
            by_cases hkS : k ∈ ({idx i, kLast} : Finset (Fin (r + 3)))
            · simp only [hkS, ↓reduceIte]
              rw [Finset.mem_insert, Finset.mem_singleton] at hkS
              rcases hkS with hk_idx | hk_last
              · have hv : k.1 = i.1 + 2 := by simpa [idx] using congrArg Fin.val hk_idx
                have hki_sub : (⟨k.1 - 2, by omega⟩ : Fin r) = i := by ext; simp [hv]
                have hk_lt_proof : k.1 < r + 2 := by omega
                change qPrime i.1 ∣ u_exp r ⟨k.1 - 2, by omega⟩ - 1
                rw [hki_sub]
                exact q_dvd_u_sub_one i
              · exfalso
                have hv : k.1 = r + 2 := by simpa [kLast] using congrArg Fin.val hk_last
                omega
            · simp only [hkS, ↓reduceIte, Nat.sub_zero]
              rw [Finset.mem_insert, Finset.mem_singleton] at hkS
              have hne : i ≠ ⟨k.1 - 2, by omega⟩ := by
                intro heq; apply hkS; left
                have hv : i.1 = k.1 - 2 := by simpa using congrArg Fin.val heq
                have hk2 : 2 ≤ k.1 := by omega
                ext; simp [idx]; omega
              exact q_dvd_u_of_ne hne
          · have hkl : k = kLast := by ext; simp [kLast]; omega
            have hkS : k ∈ ({idx i, kLast} : Finset (Fin (r + 3))) := by
              rw [hkl]; simp
            simp only [hk0, hk1, hklt, hkS, ↓reduceIte, Nat.add_sub_cancel]
            exact q_dvd_Q_prod i
  have hfilt :
      Finset.univ.filter (fun S : Finset (Fin (r + 3)) => IsPerfectPower (dOfS p e S)) =
        Finset.univ.image (fun i : Fin r => ({idx i, kLast} : Finset (Fin (r + 3)))) := by
    ext S
    rw [Finset.mem_filter, and_iff_right (Finset.mem_univ S), hiff S, Finset.mem_image]
    simp [eq_comm]
  have hcard : ∀ i : Fin r, ({idx i, kLast} : Finset (Fin (r + 3))).card = 2 := by
    intro i
    refine Finset.card_pair ?_
    intro h
    have hv := congrArg Fin.val h
    simp [idx, kLast] at hv
    omega
  rw [hfilt, Finset.sum_image]
  · simp [hcard]
  · intro i _ j _ hij
    dsimp only at hij
    have hmem : idx i ∈ ({idx i, kLast} : Finset (Fin (r + 3))) := by simp
    have hmem' : idx i ∈ ({idx j, kLast} : Finset (Fin (r + 3))) := hij ▸ hmem
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem'
    rcases hmem' with h | h
    · have hv := congrArg Fin.val h; simp [idx] at hv; exact Fin.ext hv
    · exfalso; have hv := congrArg Fin.val h; simp [idx, kLast] at hv; omega

end Construction

/-- Main Theorem (OEIS A304362): every integer `t` is attained infinitely often by `b304362`. -/
theorem a304362_infinite_fibers (t : ℤ) :
    Set.Infinite {n : ℕ | 0 < n ∧ b304362 n = t} := by
  refine Set.infinite_of_forall_exists_gt fun M => ?_
  rcases Int.lt_trichotomy t 0 with ht_neg | rfl | ht_pos
  · obtain ⟨r, hr⟩ : ∃ r : ℕ, 1 ≤ r ∧ t = -(r : ℤ) :=
      ⟨(-t).toNat, by omega, by omega⟩
    obtain ⟨n, hn, hbn⟩ := exists_neg_gt r hr.1 M
    exact ⟨n, ⟨by omega, hbn.trans hr.2.symm⟩, hn⟩
  · obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + 1)
    exact ⟨p, ⟨hp.pos, b304362_prime hp⟩, by omega⟩
  · obtain ⟨r, hr⟩ : ∃ r : ℕ, 1 ≤ r ∧ t = (r : ℤ) :=
      ⟨t.toNat, by omega, by omega⟩
    obtain ⟨n, hn, hbn⟩ := exists_pos_gt r hr.1 M
    exact ⟨n, ⟨by omega, hbn.trans hr.2.symm⟩, hn⟩

/-- Corollary: `b304362 : ℕ+ → ℤ` is surjective onto `ℤ`. -/
theorem a304362_surjective (t : ℤ) : ∃ n : ℕ, 0 < n ∧ b304362 n = t :=
  (a304362_infinite_fibers t).nonempty

end OEISThreeProofs.A304362
