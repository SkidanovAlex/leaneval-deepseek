import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

open scoped LSeries.notation

namespace Commons.NumberTheory.LSeries

private lemma primeFactors_mul_forall {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) {c : ℕ → Prop} :
    (∀ p ∈ (m * n).primeFactors, c p) ↔
      (∀ p ∈ m.primeFactors, c p) ∧ (∀ p ∈ n.primeFactors, c p) := by
  simp only [Nat.primeFactors_mul hm hn, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨h1, h2⟩ p (hp | hp); exacts [h1 p hp, h2 p hp]

private lemma mul_boole (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then (1 : ℂ) else 0) * (if Q then 1 else 0) = if P ∧ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

private noncomputable def rg (z : ℝ) : ℕ → ℂ :=
  fun n => (ArithmeticFunction.moebius n : ℂ) *
    (if ∀ p ∈ n.primeFactors, z ≤ (p : ℝ) then 1 else 0)

private lemma rg_zero (z : ℝ) : rg z 0 = 0 := by
  simp [rg]

private lemma rg_one (z : ℝ) : rg z 1 = 1 := by
  simp [rg]

private lemma rg_mul {z : ℝ} {m n : ℕ} (h : m.Coprime n) :
    rg z (m * n) = rg z m * rg z n := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Nat.coprime_zero_left] at h
    subst h
    simp [rg]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at h
    subst h
    simp [rg]
  have hmul := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h
  have hfor := primeFactors_mul_forall hm hn (c := fun p => z ≤ (p : ℝ))
  simp only [rg]
  rw [hmul]
  push_cast
  rw [if_congr hfor rfl rfl, ← mul_boole]
  ring

private noncomputable def rgf (z : ℝ) (u : ℂ) : ℕ → ℂ :=
  fun n => rg z n * (n : ℂ) ^ (-u)

private lemma rgf_zero (z : ℝ) (u : ℂ) : rgf z u 0 = 0 := by
  simp [rgf, rg]

private lemma rgf_one (z : ℝ) (u : ℂ) : rgf z u 1 = 1 := by
  simp [rgf, rg]

private lemma rgf_mul {z : ℝ} {u : ℂ} {m n : ℕ} (h : m.Coprime n) :
    rgf z u (m * n) = rgf z u m * rgf z u n := by
  simp only [rgf]
  rw [rg_mul h]
  rw [show (↑(m * n) : ℂ) = (↑m : ℂ) * (↑n : ℂ) from by push_cast; ring]
  rw [show (↑m : ℂ) = ((m:ℝ):ℂ) from by simp, show (↑n : ℂ) = ((n:ℝ):ℂ) from by simp]
  rw [Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

private lemma norm_rg_le_one (z : ℝ) (n : ℕ) : ‖rg z n‖ ≤ 1 := by
  have h1 : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  simp only [rg, norm_mul]
  refine mul_le_one₀ h1 ?_ ?_
  · split <;> simp
  · split <;> simp

private lemma summable_rgf {z : ℝ} {u : ℂ} (hu : 1 < u.re) :
    Summable (fun n => ‖rgf z u n‖) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ u.re)⁻¹) := Real.summable_nat_rpow_inv.mpr hu
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hbase
  rcases eq_or_ne n 0 with rfl | hn
  · rw [rgf_zero]
    simp [Real.zero_rpow (by linarith : u.re ≠ 0)]
  · simp only [rgf, norm_mul]
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    calc ‖rg z n‖ * (n : ℝ) ^ (-u.re)
        ≤ 1 * (n : ℝ) ^ (-u.re) := by
          gcongr; exact norm_rg_le_one z n
      _ = ((n : ℝ) ^ u.re)⁻¹ := by
          rw [one_mul, Real.rpow_neg (Nat.cast_nonneg n)]

private lemma rg_prime {z : ℝ} {p : ℕ} (hp : p.Prime) :
    rg z p = -(if z ≤ (p : ℝ) then 1 else 0) := by
  simp only [rg, ArithmeticFunction.moebius_apply_prime hp, hp.primeFactors]
  by_cases hz : z ≤ (p : ℝ) <;> simp [hz]

private lemma rg_pow_succ_succ {z : ℝ} {p e : ℕ} (hp : p.Prime) :
    rg z (p ^ (e + 2)) = 0 := by
  have hmu : ArithmeticFunction.moebius (p ^ (e + 2)) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp
  simp [rg, hmu]

private lemma rgf_local {z : ℝ} {u : ℂ} {p : ℕ} (hp : p.Prime) :
    ∑' e : ℕ, rgf z u (p ^ e) = if z ≤ (p : ℝ) then 1 - (p : ℂ) ^ (-u) else 1 := by
  have hzero : ∀ e ∉ ({0, 1} : Finset ℕ), rgf z u (p ^ e) = 0 := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    obtain ⟨he0, he1⟩ := he
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
    simp only [rgf]
    rw [rg_pow_succ_succ hp]
    simp
  rw [tsum_eq_sum hzero]
  rw [Finset.sum_insert (by simp : (0 : ℕ) ∉ ({1} : Finset ℕ)), Finset.sum_singleton]
  have h0 : rgf z u (p ^ 0) = 1 := by simp [rgf, rg]
  have h1 : rgf z u (p ^ 1) = -(if z ≤ (p : ℝ) then 1 else 0) * (p : ℂ) ^ (-u) := by
    simp only [pow_one, rgf, rg_prime hp]
  rw [h0, h1]
  by_cases hz : z ≤ (p : ℝ)
  · simp [hz]; ring
  · simp [hz]

private lemma one_sub_cpow_ne_zero {u : ℂ} (hu : 0 < u.re) {p : ℕ} (hp : p.Prime) :
    1 - (p : ℂ) ^ (-u) ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-u) = 1 := (sub_eq_zero.mp h).symm
  have h2 : (p : ℝ) ^ (-u.re) = 1 := by
    have := Complex.norm_natCast_cpow_of_pos hp.pos (-u)
    rw [h1, norm_one] at this
    simpa using this.symm
  have h3 : (p : ℝ) ^ (-u.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  rw [h2] at h3
  exact lt_irrefl 1 h3

private lemma prod_local_eq {z : ℝ} {u : ℂ} (hu : 0 < u.re) {n : ℕ} (hn : ⌈z⌉₊ ≤ n) :
    (∏ p ∈ Nat.primesBelow n, (if z ≤ (p : ℝ) then 1 - (p : ℂ) ^ (-u) else 1))
      = (∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-u))) *
          (∏ p ∈ Nat.primesBelow ⌈z⌉₊, (1 - (p : ℂ) ^ (-u)))⁻¹ := by
  have ht : Nat.primesBelow ⌈z⌉₊ ⊆ Nat.primesBelow n := Nat.primesBelow_mono hn
  have htL : ∏ p ∈ Nat.primesBelow ⌈z⌉₊, (if z ≤ (p : ℝ) then 1 - (p : ℂ) ^ (-u) else 1) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    rw [if_neg]
    exact not_le.mpr (Nat.lt_ceil.mp (Nat.mem_primesBelow.mp hp).1)
  have hstL : ∏ p ∈ Nat.primesBelow n \ Nat.primesBelow ⌈z⌉₊,
        (if z ≤ (p : ℝ) then 1 - (p : ℂ) ^ (-u) else 1)
      = ∏ p ∈ Nat.primesBelow n \ Nat.primesBelow ⌈z⌉₊, (1 - (p : ℂ) ^ (-u)) := by
    apply Finset.prod_congr rfl
    intro p hp
    obtain ⟨hpn, hpt⟩ := Finset.mem_sdiff.mp hp
    have hpp : p.Prime := (Nat.mem_primesBelow.mp hpn).2
    have hz : z ≤ (p : ℝ) := by
      have hle : ⌈z⌉₊ ≤ p := by
        by_contra h
        exact hpt (Nat.mem_primesBelow.mpr ⟨lt_of_not_ge h, hpp⟩)
      calc z ≤ (⌈z⌉₊ : ℝ) := Nat.le_ceil z
        _ ≤ (p : ℝ) := by exact_mod_cast hle
    rw [if_pos hz]
  have hne : (∏ p ∈ Nat.primesBelow ⌈z⌉₊, (1 - (p : ℂ) ^ (-u))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp =>
      one_sub_cpow_ne_zero hu (Nat.mem_primesBelow.mp hp).2
  rw [← Finset.prod_sdiff ht, htL, mul_one, hstL, eq_mul_inv_iff_mul_eq₀ hne]
  exact Finset.prod_sdiff ht

end Commons.NumberTheory.LSeries

namespace Commons.NumberTheory.LSeries

theorem LSeries_rough_moebius_eq (z : ℝ) (hz : 0 ≤ z) {u : ℂ} (hu : 1 < u.re) :
    LSeries (fun n => (ArithmeticFunction.moebius n : ℂ) *
        (if ∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p : ℝ) then 1 else 0)) u
      = (riemannZeta u)⁻¹ * ∏ p ∈ Nat.primesBelow ⌈z⌉₊, (1 - (p : ℂ) ^ (-u))⁻¹ := by
  have _ : (0 : ℝ) ≤ z := hz
  change LSeries (rg z) u = (riemannZeta u)⁻¹ * ∏ p ∈ Nat.primesBelow ⌈z⌉₊, (1 - (p : ℂ) ^ (-u))⁻¹
  have hure : 0 < u.re := by linarith
  have hzeta : riemannZeta u ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hu
  have heuler := EulerProduct.eulerProduct (f := rgf z u) (rgf_one z u)
      (fun {m n} h => rgf_mul h) (summable_rgf hu) (rgf_zero z u)
  have hloc : (fun n => ∏ p ∈ Nat.primesBelow n, ∑' e : ℕ, rgf z u (p ^ e))
      = fun n => ∏ p ∈ Nat.primesBelow n, (if z ≤ (p : ℝ) then 1 - (p : ℂ) ^ (-u) else 1) := by
    funext n
    exact Finset.prod_congr rfl fun p hp => rgf_local (Nat.mem_primesBelow.mp hp).2
  rw [hloc] at heuler
  have htsum : ∑' n : ℕ, rgf z u n = LSeries (rg z) u := by
    rw [LSeries_def₀ (rg_zero z) u]
    exact tsum_congr fun n => by simp [rgf, div_eq_mul_inv, Complex.cpow_neg]
  rw [htsum] at heuler
  have hT2 : Filter.Tendsto (fun n => ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-u)))
      Filter.atTop (nhds ((riemannZeta u)⁻¹)) := by
    have h := (riemannZeta_eulerProduct hu).inv₀ hzeta
    have heq : (fun n => (∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-u))⁻¹)⁻¹)
        = fun n => ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-u)) := by
      funext n
      simp only [Finset.prod_inv_distrib, inv_inv]
    rwa [heq] at h
  set C : ℂ := (∏ p ∈ Nat.primesBelow ⌈z⌉₊, (1 - (p : ℂ) ^ (-u)))⁻¹ with hC
  have hev : (fun n => ∏ p ∈ Nat.primesBelow n, (if z ≤ (p : ℝ) then 1 - (p : ℂ) ^ (-u) else 1))
      =ᶠ[Filter.atTop]
        (fun n => (∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-u))) * C) :=
    Filter.eventually_atTop.mpr ⟨⌈z⌉₊, fun n hn => by rw [hC]; exact prod_local_eq hure hn⟩
  have hT3 : Filter.Tendsto
      (fun n => ∏ p ∈ Nat.primesBelow n, (if z ≤ (p : ℝ) then 1 - (p : ℂ) ^ (-u) else 1))
      Filter.atTop (nhds ((riemannZeta u)⁻¹ * C)) :=
    Filter.Tendsto.congr' hev.symm (hT2.mul_const C)
  have key := tendsto_nhds_unique heuler hT3
  rw [key, hC, Finset.prod_inv_distrib]

end Commons.NumberTheory.LSeries