import Mathlib
import Submission.Work.LinnikAreas.Setup
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_ballZeroCount_uniform
import Submission.Commons.Analysis.Dyadic.invSq_le_dyadic_layer
import Submission.Commons.Analysis.Asymptotics.geom_finset_le
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
namespace Work.LinnikAreas
open Work.LinnikContract

/-- Norm bound for the kernel `Hk`: for `Re ρ ≤ 1` and `L ≥ 0`,
`‖Hk L K ((1-ρ)L)‖ ≤ 4 e^{-(L-2K)(1-Re ρ)L}/‖(1-ρ)L‖²`. -/
lemma Hk_norm_le {L : ℝ} (hL : 0 ≤ L) {ρ : ℂ} (hre : ρ.re ≤ 1) :
    ‖Hk (11/2) (3/10) ((1 - ρ) * L)‖
      ≤ 4 * Real.exp (-(49/10) * ((1 - ρ.re) * L)) / ‖(1 - ρ) * L‖ ^ 2 := by
  have hzre : ((1 - ρ) * L).re = (1 - ρ.re) * L := by simp
  have hzre0 : 0 ≤ ((1 - ρ) * L).re := by rw [hzre]; nlinarith
  have hF2 : ‖F2 (3/10) ((1 - ρ) * L)‖ ≤ 4 / ‖(1 - ρ) * L‖ ^ 2 := by
    rw [F2, norm_pow, norm_div]
    have h1 : ‖(1 : ℂ) - Complex.exp (-((3/10 : ℝ) : ℂ) * ((1 - ρ) * L))‖ ≤ 2 := by
      have := norm_sub_le (1 : ℂ) (Complex.exp (-((3/10 : ℝ) : ℂ) * ((1 - ρ) * L)))
      have hnorm1 : ‖(1:ℂ)‖ = 1 := by simp
      have hnorm2 : ‖Complex.exp (-((3/10 : ℝ) : ℂ) * ((1 - ρ) * L))‖
          = Real.exp (-(3/10) * ((1-ρ)*L).re) := by
        rw [Complex.norm_exp]; simp
      rw [hnorm1, hnorm2] at this
      have hle : Real.exp (-(3/10) * ((1-ρ)*L).re) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        nlinarith [hzre0]
      linarith
    rcases eq_or_lt_of_le (norm_nonneg ((1 - ρ) * L)) with hz | hz
    · rw [← hz]; simp
    · rw [div_pow, div_le_div_iff_of_pos_right (pow_pos hz 2)]
      nlinarith [h1, norm_nonneg ((1:ℂ) - Complex.exp (-((3/10 : ℝ) : ℂ) * ((1 - ρ) * L)))]
  rw [Hk, norm_mul]
  have hcoef : ((11/2 : ℝ) - 2*(3/10)) = 49/10 := by norm_num
  rw [hcoef]
  have hexp : ‖Complex.exp (-(((49/10) : ℝ) : ℂ) * ((1 - ρ) * L))‖
      = Real.exp (-(49/10) * ((1 - ρ.re) * L)) := by
    rw [Complex.norm_exp]
    have h1 : (-(((49/10 : ℝ)) : ℂ) * ((1 - ρ) * L)).re = -(49/10) * ((1 - ρ.re) * L) := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, neg_zero, hzre]
    rw [h1]
  rw [hexp]
  have hexpnn : 0 ≤ Real.exp (-(49/10) * ((1 - ρ.re) * L)) := Real.exp_nonneg _
  calc Real.exp (-(49/10) * ((1 - ρ.re) * L)) * ‖F2 (3/10) ((1 - ρ) * L)‖
      ≤ Real.exp (-(49/10) * ((1 - ρ.re) * L)) * (4 / ‖(1 - ρ) * L‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hF2 hexpnn
    _ = 4 * Real.exp (-(49/10) * ((1 - ρ.re) * L)) / ‖(1 - ρ) * L‖ ^ 2 := by ring

/-- Layer-cake bound for `1/d²` with `d ≥ 1`. -/
lemma one_div_sq_le_layer {d : ℝ} (hd : 1 ≤ d) (K : ℕ) (hdK : d ≤ (2:ℝ)^K) :
    (1:ℝ)/d^2 ≤ ∑ k ∈ Finset.range (K+1), (8/(4:ℝ)^k) * (if d ≤ (2:ℝ)^k then 1 else 0) := by
  have hd0 : (0:ℝ) < d := by linarith
  have h1 : (1:ℝ)/(1+d^2) ≤ ∑ k ∈ Finset.range (K+1), (if d ≤ (2:ℝ)^k then 4/(4:ℝ)^k else 0) :=
    Commons.Analysis.Dyadic.invSq_le_dyadic_layer d (by linarith) K hdK
  have h2 : (1:ℝ)/d^2 ≤ 2 * ((1:ℝ)/(1+d^2)) := by
    have hd2 : (0:ℝ) < d^2 := by positivity
    have hh : (1:ℝ)/d^2 ≤ 2/(1+d^2) := by
      rw [div_le_div_iff₀ hd2 (by positivity)]
      nlinarith
    calc (1:ℝ)/d^2 ≤ 2/(1+d^2) := hh
      _ = 2 * ((1:ℝ)/(1+d^2)) := by ring
  have h3 : 2 * ((1:ℝ)/(1+d^2)) ≤ 2 * (∑ k ∈ Finset.range (K+1),
      (if d ≤ (2:ℝ)^k then 4/(4:ℝ)^k else 0)) := by
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  have h4 : 2 * (∑ k ∈ Finset.range (K+1), (if d ≤ (2:ℝ)^k then 4/(4:ℝ)^k else 0))
      = ∑ k ∈ Finset.range (K+1), (8/(4:ℝ)^k) * (if d ≤ (2:ℝ)^k then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : d ≤ (2:ℝ)^k
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  linarith [h2, h3, h4.le, h4.ge]


/-! ### Character/zero preliminaries -/

/-- The completed `L`-function of the primitive character inducing `χ`. -/
def primL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  completedLFunction χ.primitiveCharacter

/-- The primitive character inducing a non-trivial character is non-trivial. -/
lemma primitiveCharacter_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  intro h
  refine hχ ?_
  have h2 := DirichletCharacter.changeLevel_primitiveCharacter χ
  rw [h, map_one] at h2
  exact h2.symm

lemma primL_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    primL χ = (letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
      completedLFunction χ.primitiveCharacter) := rfl

lemma zeroMult_eq_primL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    zeroMult χ ρ = analyticOrderNatAt (primL χ) ρ := rfl

lemma primL_analytic {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    AnalyticOnNhd ℂ (primL χ) Set.univ := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hdiff : Differentiable ℂ (primL χ) := by
    rw [primL]
    exact differentiable_completedLFunction (primitiveCharacter_ne_one χ hχ)
  exact fun z _ => hdiff.analyticAt z

/-- Every zero of `Λ(χ*)` (counted by `zeroMult`) lies in the critical strip. -/
lemma zeroMult_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {ρ : ℂ}
    (h : zeroMult χ ρ ≠ 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  have h' : analyticOrderNatAt (primL χ) ρ ≠ 0 := by
    rw [← zeroMult_eq_primL]; exact h
  have hz : primL χ ρ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero h'
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [primL] at hz
  exact Commons.NumberTheory.DirichletCharacter.zerosInStrip χ.primitiveCharacter
    (primitiveCharacter_ne_one χ hχ) (primitiveCharacter_isPrimitive χ) ρ hz

/-- A finite multiplicity sum over zeros of `Λ(χ*)` inside a compact set `U` is bounded by the
divisor sum of `Λ(χ*)` over `U`. -/
lemma mult_sum_le_divisor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (U : Set ℂ) (hU : IsCompact U) (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ∈ U) :
    (∑ ρ ∈ S, (analyticOrderNatAt (primL χ) ρ : ℝ))
      ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (primL χ) U) u : ℝ) := by
  classical
  have han : AnalyticOnNhd ℂ (primL χ) U := fun z _ => (primL_analytic χ hχ) z (Set.mem_univ z)
  set D : ℂ → ℤ := fun u => MeromorphicOn.divisor (primL χ) U u with hD
  have hfin : D.support.Finite := by
    rw [hD]
    exact (MeromorphicOn.divisor (primL χ) U).finiteSupport hU
  have hmem : ∀ u : ℂ, u ∈ hfin.toFinset ↔ D u ≠ 0 := by
    intro u; rw [Set.Finite.mem_toFinset]; exact Iff.rfl
  have hval : ∀ u : ℂ, u ∈ U → D u = (analyticOrderNatAt (primL χ) u : ℤ) := by
    intro u hu
    rw [hD]
    exact Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hu
  have hUsub : ∀ u : ℂ, u ∈ hfin.toFinset → u ∈ U := by
    intro u hu
    have hne : D u ≠ 0 := (hmem u).mp hu
    exact (MeromorphicOn.divisor (primL χ) U).supportWithinDomain (by simpa [hD] using hne)
  have hfs : (∑ᶠ u : ℂ, (D u : ℝ)) = ∑ u ∈ hfin.toFinset, (D u : ℝ) := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro u hu
    rw [Function.mem_support] at hu
    exact (hmem u).mpr (by intro h0; exact hu (by simp [h0]))
  rw [hfs]
  have hleft : (∑ ρ ∈ S, (analyticOrderNatAt (primL χ) ρ : ℝ))
      = ∑ ρ ∈ S.filter (fun ρ => ρ ∈ hfin.toFinset),
          (analyticOrderNatAt (primL χ) ρ : ℝ) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro u hu hnot
    have hnotin : u ∉ hfin.toFinset := fun hc => hnot (Finset.mem_filter.mpr ⟨hu, hc⟩)
    have hD0 : D u = 0 := by
      by_contra hne
      exact hnotin ((hmem u).mpr hne)
    have huU := hS u hu
    rw [hval u huU] at hD0
    have hz : analyticOrderNatAt (primL χ) u = 0 := by exact_mod_cast hD0
    simp [hz]
  rw [hleft]
  have hsub : S.filter (fun ρ => ρ ∈ hfin.toFinset) ⊆ hfin.toFinset :=
    fun u hu => (Finset.mem_filter.mp hu).2
  have hcongr : (∑ ρ ∈ S.filter (fun ρ => ρ ∈ hfin.toFinset),
        (analyticOrderNatAt (primL χ) ρ : ℝ))
      = ∑ ρ ∈ S.filter (fun ρ => ρ ∈ hfin.toFinset), (D ρ : ℝ) := by
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have huU := hS u (Finset.mem_filter.mp hu).1
    have h1 := hval u huU
    rw [h1]
    push_cast
    ring
  rw [hcongr]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro u hu _
  have h0 : (0 : ℤ) ≤ D u := by
    rw [hval u (hUsub u hu)]
    exact Int.natCast_nonneg _
  exact_mod_cast h0

/-- Multiplicity sum over a finite set of pairs sharing a fixed non-trivial character `χ`,
with all zeros satisfying `σ ≤ Re ρ` and `|Im ρ| ≤ T`, bounded by `zeroCountIn`. -/
lemma fiber_sum_le_zeroCountIn {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {σ T : ℝ} (hσ : 0 ≤ σ) (hT : 0 ≤ T) (S : Finset (DirichletCharacter ℂ q × ℂ))
    (h1 : ∀ z ∈ S, z.1 = χ) (hre : ∀ z ∈ S, σ ≤ z.2.re) (him : ∀ z ∈ S, |z.2.im| ≤ T) :
    (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ)) ≤ zeroCountIn χ σ T := by
  classical
  -- the relevant rectangle is contained in a closed ball
  have hR0 : (0:ℝ) ≤ 1 + T := by linarith
  have hrect : ∀ ρ : ℂ, σ ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
      ρ ∈ Metric.closedBall (0:ℂ) (1+T) := by
    intro ρ h1' h2' h3'
    rw [Metric.mem_closedBall, dist_zero_right]
    have him2 : ρ.im^2 ≤ T^2 := by
      have := abs_le.mp h3'; nlinarith
    have hre2 : ρ.re^2 ≤ 1 := by nlinarith
    have hsq : ‖ρ‖^2 = ρ.re^2 + ρ.im^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hmain : ‖ρ‖^2 ≤ (1+T)^2 := by
      rw [hsq]; nlinarith [sq_nonneg T]
    nlinarith [norm_nonneg ρ, hmain]
  -- injectivity of the second projection on `S`
  have hinj : Set.InjOn (fun z : DirichletCharacter ℂ q × ℂ => z.2) ↑S := by
    intro a ha b hb hab
    have h1a := h1 a ha
    have h1b := h1 b hb
    have hEq : a.1 = b.1 := by rw [h1a, h1b]
    exact Prod.ext hEq hab
  -- the support finset of the indicator function
  let U : Set ℂ := Metric.closedBall (0:ℂ) (1+T)
  have hUan : AnalyticOnNhd ℂ (primL χ) U := fun z _ => (primL_analytic χ hχ) z (Set.mem_univ z)
  let D : ℂ → ℤ := fun u => MeromorphicOn.divisor (primL χ) U u
  have hfin : D.support.Finite :=
    (MeromorphicOn.divisor (primL χ) U).finiteSupport (isCompact_closedBall _ _)
  have hmem : ∀ u : ℂ, u ∈ hfin.toFinset ↔ D u ≠ 0 := by
    intro u; rw [Set.Finite.mem_toFinset]; exact Iff.rfl
  have hval : ∀ u : ℂ, u ∈ U → D u = (analyticOrderNatAt (primL χ) u : ℤ) := by
    intro u hu
    exact Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast hUan hu
  have hUsub : ∀ u : ℂ, u ∈ hfin.toFinset → u ∈ U := by
    intro u hu
    have hne : D u ≠ 0 := (hmem u).mp hu
    exact (MeromorphicOn.divisor (primL χ) U).supportWithinDomain hne
  let f : ℂ → ℝ := fun ρ => if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
    then (zeroMult χ ρ : ℝ) else 0
  have hfnn : ∀ ρ : ℂ, 0 ≤ f ρ := by
    intro ρ; simp only [f]; split_ifs <;> positivity
  have hfsupp : Function.support f ⊆ ↑hfin.toFinset := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    simp only [f] at hρ
    split_ifs at hρ with hc
    · have hne : zeroMult χ ρ ≠ 0 := by
        intro h0; exact hρ (by simp [h0])
      have hne' : analyticOrderNatAt (primL χ) ρ ≠ 0 := by
        rw [← zeroMult_eq_primL]; exact hne
      have hz : primL χ ρ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hne'
      have hmemU : ρ ∈ U := hrect ρ hc.1 hc.2.1 hc.2.2
      have hDρ : D ρ = (analyticOrderNatAt (primL χ) ρ : ℤ) := hval ρ hmemU
      have hDne : D ρ ≠ 0 := by rw [hDρ]; exact_mod_cast hne'
      exact (hmem ρ).mpr hDne
    · exact absurd rfl hρ
  have hzc : zeroCountIn χ σ T = ∑ᶠ ρ : ℂ, f ρ := rfl
  rw [hzc]
  -- LHS equals the sum of `f` over the image
  have hL : (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ)) = ∑ ρ ∈ S.image (fun z => z.2), f ρ := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    have hzx : z.1 = χ := h1 z hz
    rw [hzx]
    simp only [f]
    by_cases hz0 : zeroMult χ z.2 = 0
    · simp [hz0]
    · have hstrip := zeroMult_re χ hχ hz0
      rw [if_pos ⟨hre z hz, le_of_lt hstrip.2, him z hz⟩]
  rw [hL]
  -- the finsum is the sum over the support
  have hfs : (∑ᶠ ρ : ℂ, f ρ) = ∑ ρ ∈ hfin.toFinset, f ρ :=
    finsum_eq_sum_of_support_subset f hfsupp
  rw [hfs]
  -- remove the terms outside the support, then monotonicity
  have hstep : (∑ ρ ∈ S.image (fun z => z.2), f ρ)
      = ∑ ρ ∈ (S.image (fun z => z.2)).filter (fun ρ => ρ ∈ hfin.toFinset), f ρ := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro u hu hnot
    by_contra hne
    have hmem' : u ∈ hfin.toFinset := hfsupp (by rw [Function.mem_support]; exact hne)
    exact hnot (Finset.mem_filter.mpr ⟨hu, hmem'⟩)
  rw [hstep]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun u hu => (Finset.mem_filter.mp hu).2) (fun u _ _ => hfnn u)

lemma zeroCountIn_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) :
    0 ≤ zeroCountIn χ σ T := by
  rw [zeroCountIn]
  exact finsum_nonneg (fun ρ => by split <;> positivity)

/-- Family count of pairs with `σ ≤ Re ρ` and `|Im ρ| ≤ T`, from the family zero-density
hypothesis. -/
lemma finset_sum_le_fam {q : ℕ} [NeZero q] (C A : ℝ)
    (hfam : ∀ σ T : ℝ, 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T ≤ C * ((q:ℝ) * T) ^ (A * (1 - σ)))
    {σ T : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hT : 1 ≤ T)
    {S : Finset (DirichletCharacter ℂ q × ℂ)}
    (h1 : ∀ z ∈ S, z.1 ≠ 1) (hre : ∀ z ∈ S, σ ≤ z.2.re) (him : ∀ z ∈ S, |z.2.im| ≤ T) :
    (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ)) ≤ C * ((q:ℝ) * T) ^ (A * (1 - σ)) := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := Finset.univ) (g := fun z : DirichletCharacter ℂ q × ℂ => z.1)
    (f := fun z => (zeroMult z.1 z.2 : ℝ)) (fun z _ => Finset.mem_univ _)
  rw [← hfib]
  refine le_trans (Finset.sum_le_sum (fun χ _ => ?_)) (hfam σ T hσ hσ1 hT)
  by_cases hχ : χ = 1
  · have hempty : S.filter (fun z => z.1 = χ) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro z hz hc
        exact h1 z hz (by rw [hc, hχ])
    rw [hempty, Finset.sum_empty]
    exact zeroCountIn_nonneg χ σ T
  · exact fiber_sum_le_zeroCountIn χ hχ hσ (by linarith) _
      (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => hre z (Finset.mem_filter.mp hz).1)
      (fun z hz => him z (Finset.mem_filter.mp hz).1)

/-- Cardinality of the group of Dirichlet characters mod `q`. -/
lemma card_dirichletCharacter (q : ℕ) [NeZero q] :
    Fintype.card (DirichletCharacter ℂ q) = q.totient := by
  rw [← Nat.card_eq_fintype_card]
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q


/-- Variant of `mult_sum_le_divisor` that ignores terms of multiplicity zero. -/
lemma mult_sum_le_divisor' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (U : Set ℂ) (hU : IsCompact U) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, zeroMult χ ρ ≠ 0 → ρ ∈ U) :
    (∑ ρ ∈ S, (zeroMult χ ρ : ℝ))
      ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (primL χ) U) u : ℝ) := by
  classical
  have h1 : (∑ ρ ∈ S, (zeroMult χ ρ : ℝ))
      = ∑ ρ ∈ S.filter (fun ρ => zeroMult χ ρ ≠ 0), (zeroMult χ ρ : ℝ) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro ρ hρ hnot
    have h0 : zeroMult χ ρ = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hρ, hne⟩)
    simp [h0]
  rw [h1]
  have h2 : (∑ ρ ∈ S.filter (fun ρ => zeroMult χ ρ ≠ 0), (zeroMult χ ρ : ℝ))
      = ∑ ρ ∈ S.filter (fun ρ => zeroMult χ ρ ≠ 0),
          (analyticOrderNatAt (primL χ) ρ : ℝ) :=
    Finset.sum_congr rfl (fun ρ _ => by rw [zeroMult_eq_primL])
  rw [h2]
  refine mult_sum_le_divisor χ hχ U hU _ (fun ρ hρ => ?_)
  exact hS ρ (Finset.mem_filter.mp hρ).1 (Finset.mem_filter.mp hρ).2

/-- Family count of pairs with `0 ≤ Re ρ` and `|Im ρ| ≤ T`, from the *trivial* uniform zero
count (an absolute constant). -/
lemma finset_sum_le_trivial {q : ℕ} [NeZero q] {c0 : ℝ} (hc0 : 0 < c0)
    (hball : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ))
        ≤ c0 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N:ℝ) + 2))
    {T : ℝ} (hT : 0 ≤ T)
    {S : Finset (DirichletCharacter ℂ q × ℂ)}
    (h1 : ∀ z ∈ S, z.1 ≠ 1) (hre : ∀ z ∈ S, 0 ≤ z.2.re) (him : ∀ z ∈ S, |z.2.im| ≤ T) :
    (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ))
      ≤ (q : ℝ) * c0 * (4 + T) * (Real.log (7 + T) + Real.log (q:ℝ) + 2) := by
  classical
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlogq : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg hq1
  have hlog7 : 0 ≤ Real.log (7 + T) := Real.log_nonneg (by linarith)
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := Finset.univ) (g := fun z : DirichletCharacter ℂ q × ℂ => z.1)
    (f := fun z => (zeroMult z.1 z.2 : ℝ)) (fun z _ => Finset.mem_univ _)
  rw [← hfib]
  have hcard : (Fintype.card (DirichletCharacter ℂ q) : ℝ) ≤ (q:ℝ) := by
    rw [card_dirichletCharacter q]
    exact_mod_cast Nat.totient_le q
  have hkey : ∀ χ : DirichletCharacter ℂ q,
      (∑ z ∈ S.filter (fun z => z.1 = χ), (zeroMult z.1 z.2 : ℝ))
        ≤ c0 * (4 + T) * (Real.log (7 + T) + Real.log (q:ℝ) + 2) := by
    intro χ
    by_cases hχ : χ = 1
    · have hempty : S.filter (fun z => z.1 = χ) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro z hz hc
        exact h1 z hz (by rw [hc, hχ])
      rw [hempty, Finset.sum_empty]
      exact mul_nonneg (mul_nonneg hc0.le (by linarith)) (by linarith)
    · haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      have hinj : Set.InjOn (fun z : DirichletCharacter ℂ q × ℂ => z.2)
          ↑(S.filter (fun z => z.1 = χ)) := by
        intro a ha b hb hab
        rw [Finset.mem_coe, Finset.mem_filter] at ha hb
        exact Prod.ext (by rw [ha.2, hb.2]) hab
      have himg : (∑ z ∈ S.filter (fun z => z.1 = χ), (zeroMult z.1 z.2 : ℝ))
          = ∑ ρ ∈ (S.filter (fun z => z.1 = χ)).image (fun z => z.2), (zeroMult χ ρ : ℝ) := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl (fun z hz => ?_)
        rw [← (Finset.mem_filter.mp hz).2]
      rw [himg]
      have hballU : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T →
          ρ ∈ Metric.closedBall (2:ℂ) (3+T) := by
        intro ρ hr0 hr1 hiT
        rw [Metric.mem_closedBall, dist_eq_norm]
        have him2 : ρ.im^2 ≤ T^2 := by have := abs_le.mp hiT; nlinarith
        have hre2 : (ρ.re - 2)^2 ≤ 4 := by nlinarith
        have hsq : ‖ρ - 2‖^2 = (ρ.re-2)^2 + ρ.im^2 := by
          rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
          norm_num
          ring
        have hmain : ‖ρ - 2‖^2 ≤ (3+T)^2 := by rw [hsq]; nlinarith [sq_nonneg (3+T)]
        nlinarith [norm_nonneg (ρ - 2), hmain]
      have hSsub : ∀ ρ ∈ (S.filter (fun z => z.1 = χ)).image (fun z => z.2),
          zeroMult χ ρ ≠ 0 → ρ ∈ Metric.closedBall (2:ℂ) (3+T) := by
        intro ρ hρ hne
        obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hρ
        have hne' : zeroMult χ z.2 ≠ 0 := by rw [hzx]; exact hne
        rw [← hzx]
        exact hballU z.2 (zeroMult_re χ hχ hne').1 (zeroMult_re χ hχ hne').2
          (him z (Finset.mem_filter.mp hz).1)
      refine le_trans (mult_sum_le_divisor' χ hχ _ (isCompact_closedBall _ _) _ hSsub) ?_
      have hb := hball (N := χ.conductor) χ.primitiveCharacter
        (primitiveCharacter_ne_one χ hχ) (primitiveCharacter_isPrimitive χ)
        (2:ℂ) (3+T) (by linarith)
      have hcondq : (χ.conductor : ℝ) ≤ (q:ℝ) := by
        exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q))
          (DirichletCharacter.conductor_dvd_level χ)
      have hlogcond : Real.log (χ.conductor : ℝ) ≤ Real.log (q:ℝ) :=
        Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)) hcondq
      have hnorm2 : ‖(2:ℂ)‖ = 2 := by norm_num
      calc (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (primL χ)
              (Metric.closedBall (2:ℂ) (3+T))) u : ℤ) : ℝ))
          ≤ c0 * (3+T+1) * (Real.log (‖(2:ℂ)‖ + (3+T) + 2) + Real.log (χ.conductor:ℝ) + 2) := hb
        _ = c0 * (4+T) * (Real.log (7 + T) + Real.log (χ.conductor:ℝ) + 2) := by
            rw [hnorm2]; ring_nf
        _ ≤ c0 * (4+T) * (Real.log (7 + T) + Real.log (q:ℝ) + 2) := by
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc (∑ χ ∈ Finset.univ, ∑ z ∈ S.filter (fun z => z.1 = χ), (zeroMult z.1 z.2 : ℝ))
      ≤ ∑ χ ∈ Finset.univ, c0 * (4 + T) * (Real.log (7 + T) + Real.log (q:ℝ) + 2) :=
        Finset.sum_le_sum (fun i _ => hkey i)
    _ = (Fintype.card (DirichletCharacter ℂ q) : ℝ) *
          (c0 * (4 + T) * (Real.log (7 + T) + Real.log (q:ℝ) + 2)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (q:ℝ) * (c0 * (4 + T) * (Real.log (7 + T) + Real.log (q:ℝ) + 2)) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg (mul_nonneg hc0.le (by linarith)) (by linarith))
    _ = (q:ℝ) * c0 * (4 + T) * (Real.log (7 + T) + Real.log (q:ℝ) + 2) := by ring

/-- Dyadic tail sum bound: for `e ≤ 3/2` and `X ≥ 1`,
`∑_{k<N} [X ≤ 2^k] (2^k)^{e-2} ≤ 5 X^{e-2}`. -/
lemma dyadic_tail_le {e X : ℝ} (he : e ≤ 3/2) (hX : 1 ≤ X) (N : ℕ) :
    (∑ k ∈ Finset.range N, (if X ≤ (2:ℝ)^k then ((2:ℝ)^k)^(e-2) else 0)) ≤ 5 * X^(e-2) := by
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX
  have h2pos : (0:ℝ) < (2:ℝ)^(e-2) := Real.rpow_pos_of_pos (by norm_num) _
  have hr0 : 0 ≤ (2:ℝ)^(e-2) := le_of_lt h2pos
  have hr1 : (2:ℝ)^(e-2) < 1 := by
    have h1 : (2:ℝ)^(e-2) ≤ (2:ℝ)^(-(1/2:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (show e - 2 ≤ -(1/2:ℝ) by linarith)
    have h2 : (2:ℝ)^(-(1/2:ℝ)) = (Real.sqrt 2)⁻¹ := by
      rw [Real.rpow_neg (by norm_num), Real.sqrt_eq_rpow]
    rw [h2] at h1
    have h3 : (1:ℝ) < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    exact lt_of_le_of_lt h1 (inv_lt_one_of_one_lt₀ h3)
  have hpt : ∀ k : ℕ, ((2:ℝ)^k)^(e-2) = ((2:ℝ)^(e-2))^k := by
    intro k
    have h1 : ((2:ℝ)^k)^(e-2) = (2:ℝ)^((k:ℝ)*(e-2)) := by
      rw [← Real.rpow_natCast (2:ℝ) k, ← Real.rpow_mul (x := (2:ℝ)) (by norm_num)]
    have h2 : ((2:ℝ)^(e-2))^k = (2:ℝ)^((e-2)*(k:ℝ)) := by
      rw [← Real.rpow_natCast ((2:ℝ)^(e-2)) k, ← Real.rpow_mul (x := (2:ℝ)) (by norm_num)]
    rw [h1, h2]
    congr 1
    ring
  set s : Finset ℕ := (Finset.range N).filter (fun k => X ≤ (2:ℝ)^k) with hs
  have hsum : (∑ k ∈ Finset.range N, (if X ≤ (2:ℝ)^k then ((2:ℝ)^k)^(e-2) else 0))
      = ∑ k ∈ s, ((2:ℝ)^(e-2))^k := by
    rw [show (∑ k ∈ Finset.range N, (if X ≤ (2:ℝ)^k then ((2:ℝ)^k)^(e-2) else 0))
        = ∑ k ∈ Finset.range N, (if X ≤ (2:ℝ)^k then ((2:ℝ)^(e-2))^k else 0) from
      Finset.sum_congr rfl (fun k _ => by
        by_cases hk : X ≤ (2:ℝ)^k
        · rw [if_pos hk, if_pos hk, hpt k]
        · rw [if_neg hk, if_neg hk])]
    rw [hs]
    exact (Finset.sum_filter _ _).symm
  rw [hsum]
  set k₀ : ℕ := Nat.ceil (Real.logb 2 X) with hk0
  have hk0le : ∀ k ∈ s, k₀ ≤ k := by
    intro k hk
    rw [hs, Finset.mem_filter] at hk
    have h1 : Real.logb 2 X ≤ (k : ℝ) := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) hX0]
      simpa only [Real.rpow_natCast] using hk.2
    exact Nat.ceil_le.mpr h1
  have h2k0 : X ≤ (2:ℝ)^k₀ := by
    have h1 : Real.logb 2 X ≤ (k₀ : ℝ) := Nat.le_ceil _
    have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) h1
    rwa [Real.rpow_logb (by norm_num) (by norm_num) hX0, Real.rpow_natCast] at h2
  have hsub : s ⊆ Finset.range N := by rw [hs]; exact Finset.filter_subset _ _
  have hstep : ∑ k ∈ s, ((2:ℝ)^(e-2))^k
      ≤ ∑ k ∈ Finset.Ico k₀ N, ((2:ℝ)^(e-2))^k := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro k hk
      rw [Finset.mem_Ico]
      exact ⟨hk0le k hk, Finset.mem_range.mp (hsub hk)⟩
    · intro k _ _
      positivity
  have hIco : ∑ k ∈ Finset.Ico k₀ N, ((2:ℝ)^(e-2))^k
      = ((2:ℝ)^(e-2))^k₀ * ∑ j ∈ Finset.range (N - k₀), ((2:ℝ)^(e-2))^j := by
    rw [Finset.sum_Ico_eq_sum_range]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pow_add]
  have hgeom : ∑ j ∈ Finset.range (N - k₀), ((2:ℝ)^(e-2))^j ≤ 1 / (1 - (2:ℝ)^(e-2)) :=
    Commons.Analysis.Asymptotics.geom_finset_le hr0 hr1 _
  have hrk0 : ((2:ℝ)^(e-2))^k₀ ≤ X^(e-2) := by
    have hh : ((2:ℝ)^(e-2))^k₀ = (2:ℝ)^((e-2)*(k₀:ℝ)) := by
      rw [← Real.rpow_natCast ((2:ℝ)^(e-2)) k₀, ← Real.rpow_mul (x := (2:ℝ)) (by norm_num)]
    have hg : ((2:ℝ)^k₀)^(e-2) = (2:ℝ)^((k₀:ℝ)*(e-2)) := by
      rw [← Real.rpow_natCast (2:ℝ) k₀, ← Real.rpow_mul (x := (2:ℝ)) (by norm_num)]
    calc ((2:ℝ)^(e-2))^k₀ = (2:ℝ)^((e-2)*(k₀:ℝ)) := hh
      _ = (2:ℝ)^((k₀:ℝ)*(e-2)) := by ring_nf
      _ = ((2:ℝ)^k₀)^(e-2) := hg.symm
      _ ≤ X^(e-2) := Real.rpow_le_rpow_of_nonpos hX0 h2k0 (by linarith)
  have hconst : 1 / (1 - (2:ℝ)^(e-2)) ≤ 5 := by
    have h4 : (2:ℝ)^(e-2) ≤ 3 / 4 := by
      have h1 : (2:ℝ)^(e-2) ≤ (2:ℝ)^(-(1/2:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
          (show e - 2 ≤ -(1/2:ℝ) by linarith)
      have h2 : (2:ℝ)^(-(1/2:ℝ)) ≤ (3/4 : ℝ) := by
        rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
        rw [inv_le_comm₀ (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)]
        rw [inv_eq_one_div, Real.le_sqrt (by norm_num) (by norm_num)]
        norm_num
      linarith
    have h5 : (0:ℝ) < 1 - (2:ℝ)^(e-2) := by linarith
    rw [div_le_iff₀ h5]
    nlinarith
  calc ∑ k ∈ s, ((2:ℝ)^(e-2))^k
      ≤ ∑ k ∈ Finset.Ico k₀ N, ((2:ℝ)^(e-2))^k := hstep
    _ = ((2:ℝ)^(e-2))^k₀ * ∑ j ∈ Finset.range (N - k₀), ((2:ℝ)^(e-2))^j := hIco
    _ ≤ ((2:ℝ)^(e-2))^k₀ * (1 / (1 - (2:ℝ)^(e-2))) := by
        exact mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ ≤ X^(e-2) * 5 := by
        exact mul_le_mul hrk0 hconst (by positivity) (Real.rpow_nonneg (le_of_lt hX0) _)
    _ = 5 * X^(e-2) := by ring

/-- `(1/4)^k (q 2^k)^c = q^c (2^k)^{c-2}` (for `q > 0`). -/
lemma quarter_mul_rpow (k : ℕ) {c q : ℝ} (hq : 0 < q) :
    (1/4:ℝ)^k * (q * (2:ℝ)^k)^c = q^c * ((2:ℝ)^k)^(c-2) := by
  have h2k : (0:ℝ) < (2:ℝ)^k := pow_pos (by norm_num) k
  have h4 : ((2:ℝ)^k)^2 = (4:ℝ)^k := by
    have h : ((2:ℝ)^k)^2 = ((2:ℝ)^2)^k := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    rw [h]; norm_num
  have h14 : (1/4:ℝ)^k = (((2:ℝ)^k)^2)⁻¹ := by
    rw [one_div_pow, h4, one_div]
  have hneg : (((2:ℝ)^k)^2)⁻¹ = ((2:ℝ)^k)^(-(2:ℝ)) := by
    rw [← Real.rpow_natCast ((2:ℝ)^k) 2]
    exact (Real.rpow_neg (le_of_lt h2k) (2:ℝ)).symm
  calc (1/4:ℝ)^k * (q * (2:ℝ)^k)^c
      = (((2:ℝ)^k)^2)⁻¹ * (q^c * ((2:ℝ)^k)^c) := by
        rw [Real.mul_rpow (le_of_lt hq) (le_of_lt h2k), h14]
    _ = q^c * ((((2:ℝ)^k)^2)⁻¹ * ((2:ℝ)^k)^c) := by ring
    _ = q^c * (((2:ℝ)^k)^(-(2:ℝ)) * ((2:ℝ)^k)^c) := by rw [hneg]
    _ = q^c * ((2:ℝ)^k)^(-(2:ℝ)+c) := by rw [← Real.rpow_add h2k]
    _ = q^c * ((2:ℝ)^k)^(c-2) := by ring_nf

/-- `q^{c/L} = exp c` when `L = log q` and `q > 1`. -/
lemma rpow_div_log {q : ℝ} (hq : 1 < q) (c : ℝ) :
    q^(c / Real.log q) = Real.exp c := by
  have hL : Real.log q ≠ 0 := ne_of_gt (Real.log_pos hq)
  rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ hL]

/-- The `k`-sum of the trivial-count weights is bounded by `10 log q + 100`. -/
lemma sum_quarter_B_le {q : ℝ} (hq : 1 ≤ q) (N : ℕ) :
    (∑ k ∈ Finset.range N, (1/4:ℝ)^k *
        ((4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log q + 2)))
      ≤ 10 * Real.log q + 100 := by
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hlog7 : ∀ k : ℕ, Real.log (7 + (2:ℝ)^k) ≤ ((k:ℕ):ℝ) + 3 := by
    intro k
    have h7 : (0:ℝ) < 7 + (2:ℝ)^k := by positivity
    have hle : 7 + (2:ℝ)^k ≤ 8 * (2:ℝ)^k := by
      have h1 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
      nlinarith
    have hlog := Real.log_le_log h7 hle
    rw [Real.log_mul (by norm_num : (8:ℝ) ≠ 0) (by positivity)] at hlog
    have hlog2 : Real.log ((2:ℝ)^k) = (k:ℝ) * Real.log 2 := Real.log_pow 2 k
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    have hlog8 : Real.log (8:ℝ) ≤ 3 := by
      have h8 : (8:ℝ) = 2^3 := by norm_num
      rw [h8, Real.log_pow]; push_cast; nlinarith
    rw [hlog2] at hlog
    nlinarith
  have hpt : ∀ k : ℕ, (1/4:ℝ)^k *
      ((4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log q + 2))
      ≤ 4 * (1/4:ℝ)^k * Real.log q + 4 * ((1/4:ℝ)^k * (k:ℝ))
        + (1/2:ℝ)^k * Real.log q + ((1/2:ℝ)^k * (k:ℝ)) + 20 * (1/4:ℝ)^k + 5 * (1/2:ℝ)^k := by
    intro k
    have h1 := hlog7 k
    have h12 : (1/4:ℝ)^k * (2:ℝ)^k = (1/2:ℝ)^k := by rw [← mul_pow]; norm_num
    have hstep : (1/4:ℝ)^k * ((4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log q + 2))
        ≤ (1/4:ℝ)^k * ((4 + (2:ℝ)^k) * (((k:ℕ):ℝ) + 3 + Real.log q + 2)) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
      linarith
    refine le_trans hstep ?_
    have hexp : (1/4:ℝ)^k * ((4 + (2:ℝ)^k) * (((k:ℕ):ℝ) + 3 + Real.log q + 2))
        = 4 * (1/4:ℝ)^k * Real.log q + 4 * ((1/4:ℝ)^k * (k:ℝ))
          + (1/2:ℝ)^k * Real.log q + ((1/2:ℝ)^k * (k:ℝ)) + 20 * (1/4:ℝ)^k + 5 * (1/2:ℝ)^k := by
      rw [← h12]; ring
    rw [hexp]
  refine le_trans (Finset.sum_le_sum (fun k _ => hpt k)) ?_
  have hsum1 : (∑ k ∈ Finset.range N, (1/4:ℝ)^k) ≤ 4/3 := by
    have h := Commons.Analysis.Asymptotics.geom_finset_le (r := (1/4:ℝ))
      (by norm_num) (by norm_num) (Finset.range N)
    have h2 : (1:ℝ) / (1 - 1/4) = 4/3 := by norm_num
    linarith
  have hsum2 : (∑ k ∈ Finset.range N, (1/2:ℝ)^k) ≤ 2 := by
    have h := Commons.Analysis.Asymptotics.geom_finset_le (r := (1/2:ℝ))
      (by norm_num) (by norm_num) (Finset.range N)
    have h2 : (1:ℝ) / (1 - 1/2) = 2 := by norm_num
    linarith
  have hsumk1 : (∑ k ∈ Finset.range N, (1/4:ℝ)^k * (k:ℝ)) ≤ 4/9 := by
    rw [show (∑ k ∈ Finset.range N, (1/4:ℝ)^k * (k:ℝ))
        = ∑ k ∈ Finset.range N, (k:ℝ) * (1/4:ℝ)^k from
      Finset.sum_congr rfl (fun k _ => by ring)]
    have h := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1/4:ℝ)) (by norm_num)
    have hval : (∑' k : ℕ, (k:ℝ) * (1/4:ℝ)^k) = 4/9 := by rw [h.tsum_eq]; norm_num
    have hle := Summable.sum_le_tsum (Finset.range N) (f := fun k : ℕ => (k:ℝ) * (1/4:ℝ)^k)
      (fun k _ => by positivity) h.summable
    linarith
  have hsumk2 : (∑ k ∈ Finset.range N, (1/2:ℝ)^k * (k:ℝ)) ≤ 2 := by
    rw [show (∑ k ∈ Finset.range N, (1/2:ℝ)^k * (k:ℝ))
        = ∑ k ∈ Finset.range N, (k:ℝ) * (1/2:ℝ)^k from
      Finset.sum_congr rfl (fun k _ => by ring)]
    have h := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1/2:ℝ)) (by norm_num)
    have hval : (∑' k : ℕ, (k:ℝ) * (1/2:ℝ)^k) = 2 := by rw [h.tsum_eq]; norm_num
    have hle := Summable.sum_le_tsum (Finset.range N) (f := fun k : ℕ => (k:ℝ) * (1/2:ℝ)^k)
      (fun k _ => by positivity) h.summable
    linarith
  have e1 : (∑ k ∈ Finset.range N, 4 * (1/4:ℝ)^k * Real.log q)
      = 4 * Real.log q * ∑ k ∈ Finset.range N, (1/4:ℝ)^k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have e2 : (∑ k ∈ Finset.range N, 4 * ((1/4:ℝ)^k * (k:ℝ)))
      = 4 * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * (k:ℝ) := by
    rw [Finset.mul_sum]
  have e3 : (∑ k ∈ Finset.range N, (1/2:ℝ)^k * Real.log q)
      = Real.log q * ∑ k ∈ Finset.range N, (1/2:ℝ)^k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have e4 : (∑ k ∈ Finset.range N, 20 * (1/4:ℝ)^k)
      = 20 * ∑ k ∈ Finset.range N, (1/4:ℝ)^k := by
    rw [Finset.mul_sum]
  have e5 : (∑ k ∈ Finset.range N, 5 * (1/2:ℝ)^k)
      = 5 * ∑ k ∈ Finset.range N, (1/2:ℝ)^k := by
    rw [Finset.mul_sum]
  have hsplit : (∑ k ∈ Finset.range N, (4 * (1/4:ℝ)^k * Real.log q
        + 4 * ((1/4:ℝ)^k * (k:ℝ)) + (1/2:ℝ)^k * Real.log q + ((1/2:ℝ)^k * (k:ℝ))
        + 20 * (1/4:ℝ)^k + 5 * (1/2:ℝ)^k))
      = (∑ k ∈ Finset.range N, 4 * (1/4:ℝ)^k * Real.log q)
        + (∑ k ∈ Finset.range N, 4 * ((1/4:ℝ)^k * (k:ℝ)))
        + (∑ k ∈ Finset.range N, (1/2:ℝ)^k * Real.log q)
        + (∑ k ∈ Finset.range N, (1/2:ℝ)^k * (k:ℝ))
        + (∑ k ∈ Finset.range N, 20 * (1/4:ℝ)^k)
        + (∑ k ∈ Finset.range N, 5 * (1/2:ℝ)^k) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsplit, e1, e2, e3, e4, e5]
  linarith [hsum1, hsum2, hsumk1, hsumk2, hlogq,
    mul_le_mul_of_nonneg_left hsum1 hlogq, mul_le_mul_of_nonneg_left hsum2 hlogq]

/-- Tail bound for `∑ e^{-4.9 m}` over indices above `(3/5)L - 1`. -/
lemma geom_exp_tail {L : ℝ} (_hL : 0 < L) {s : Finset ℕ}
    (h : ∀ m ∈ s, (3/5)*L - 1 < (m:ℝ)) :
    (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))) ≤ 500 * Real.exp (-(2.94) * L) := by
  set r : ℝ := Real.exp (-(49/10)) with hr
  have hr0 : 0 ≤ r := le_of_lt (Real.exp_pos _)
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hpow : ∀ m : ℕ, Real.exp (-(49/10) * (m:ℝ)) = r^m := by
    intro m
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun m _ => hpow m)]
  set M : ℕ := Nat.ceil ((3/5)*L - 1) with hM
  have hmge : ∀ m ∈ s, M ≤ m := fun m hm => Nat.ceil_le.mpr (le_of_lt (h m hm))
  set N : ℕ := s.sup id + 1 with hN
  have hsub : s ⊆ Finset.Ico M N := by
    intro m hm
    rw [Finset.mem_Ico]
    exact ⟨hmge m hm, by
      rw [hN]; exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)⟩
  have hstep : ∑ m ∈ s, r^m ≤ ∑ m ∈ Finset.Ico M N, r^m :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => pow_nonneg hr0 k)
  have hIco : ∑ m ∈ Finset.Ico M N, r^m = r^M * ∑ j ∈ Finset.range (N - M), r^j := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_); rw [pow_add]
  have hgeom : ∑ j ∈ Finset.range (N - M), r^j ≤ 1/(1-r) :=
    Commons.Analysis.Asymptotics.geom_finset_le hr0 hr1 _
  have hgeom2 : 1/(1-r) ≤ 2 := by
    have h2 : r ≤ 1/2 := by
      rw [hr]
      have h1 : -((49:ℝ)/10) ≤ Real.log (1/2) := by
        have h2' : Real.log (1/2) = -Real.log 2 := by rw [one_div, Real.log_inv]
        rw [h2']
        have h3 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
        linarith
      calc Real.exp (-(49/10)) ≤ Real.exp (Real.log (1/2)) := Real.exp_le_exp.mpr h1
        _ = 1/2 := Real.exp_log (by norm_num)
    have h3 : (0:ℝ) < 1 - r := by linarith
    rw [div_le_iff₀ h3]; linarith
  have hMle : ((M:ℕ):ℝ) ≥ (3/5)*L - 1 := Nat.le_ceil _
  have hrM : r^M ≤ Real.exp (-(49/10) * ((3/5)*L - 1)) := by
    rw [show r^M = Real.exp (-(49/10) * (M:ℝ)) by
      rw [hr, ← Real.exp_nat_mul]; congr 1; ring]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hexp4 : Real.exp (-(49/10) * ((3/5)*L - 1)) = Real.exp (49/10) * Real.exp (-(2.94)*L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp49 : Real.exp (49/10) ≤ 250 := by
    have h1 : (49:ℝ)/10 ≤ 5 := by norm_num
    calc Real.exp (49/10) ≤ Real.exp 5 := Real.exp_le_exp.mpr h1
      _ = (Real.exp 1)^5 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 3^5 := pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_three) 5
      _ = 243 := by norm_num
      _ ≤ 250 := by norm_num
  calc ∑ m ∈ s, r^m ≤ ∑ m ∈ Finset.Ico M N, r^m := hstep
    _ = r^M * ∑ j ∈ Finset.range (N - M), r^j := hIco
    _ ≤ r^M * 2 := mul_le_mul_of_nonneg_left (le_trans hgeom hgeom2) (pow_nonneg hr0 M)
    _ ≤ Real.exp (-(49/10) * ((3/5)*L - 1)) * 2 := mul_le_mul_of_nonneg_right hrM (by norm_num)
    _ = 2 * Real.exp (49/10) * Real.exp (-(2.94)*L) := by rw [hexp4]; ring
    _ ≤ 500 * Real.exp (-(2.94) * L) := by
        have hpos : 0 ≤ Real.exp (-(2.94) * L) := le_of_lt (Real.exp_pos _)
        nlinarith [hexp49, hpos]


/-- The dyadic layer weight used to bound the far-zero mass. -/
def farLayer (K R m : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (K+1),
    (1/4:ℝ)^k * (if (R:ℝ) ≤ (2:ℝ)^k ∧ y ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then 1 else 0)

/-- `⌊(1 - Re ρ)·𝓛⌋`. -/
def farM {q : ℕ} (L : ℝ) (z : DirichletCharacter ℂ q × ℂ) : ℕ :=
  Nat.floor ((1 - z.2.re) * L)

/-- `|Im ρ|·𝓛`. -/
def farY {q : ℕ} (L : ℝ) (z : DirichletCharacter ℂ q × ℂ) : ℝ :=
  |z.2.im| * L

/-- Multiplicity sum over a cell of the dyadic decomposition. -/
def cellMult {q : ℕ} [NeZero q] (L : ℝ) (S : Finset (DirichletCharacter ℂ q × ℂ))
    (m k : ℕ) : ℝ :=
  ∑ z ∈ S.filter (fun z => farM L z = m ∧ farY L z ≤ (2:ℝ)^k), (zeroMult z.1 z.2 : ℝ)

/-- Pointwise bound of `‖Hk‖` by the exponential weight times the dyadic layer sum. -/
lemma Hk_le_farLayer {q : ℕ} [NeZero q] (R : ℕ) (hR : 1 ≤ R)
    {L : ℝ} (hL : 0 < L) {z : DirichletCharacter ℂ q × ℂ}
    (hz : z.1 ≠ 1) (hz0 : zeroMult z.1 z.2 ≠ 0)
    (hfar : (R:ℝ) < max ((1 - z.2.re) * L) (|z.2.im| * L))
    (K : ℕ) (hK : max (farM L z : ℝ) (farY L z) + 1 ≤ (2:ℝ)^K) :
    ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖
      ≤ 32 * Real.exp (-(49/10) * (farM L z : ℝ)) * farLayer K R (farM L z) (farY L z) := by
  classical
  obtain ⟨hr0, hr1⟩ := zeroMult_re z.1 hz hz0
  have hX0 : 0 ≤ (1 - z.2.re) * L := by nlinarith
  have hdX : (farM L z : ℝ) ≤ (1 - z.2.re) * L := Nat.floor_le hX0
  -- kernel bound
  have hk : ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖
      ≤ 4 * Real.exp (-(49/10) * ((1 - z.2.re) * L)) / ‖(1 - z.2) * L‖ ^ 2 :=
    Hk_norm_le (le_of_lt hL) (le_of_lt hr1)
  -- the argument's norm
  have hnorm : ‖(1 - z.2) * L‖ ^ 2 = ((1 - z.2.re) * L) ^ 2 + (|z.2.im| * L) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h1 : ((1 - z.2) * (L : ℂ)).re = (1 - z.2.re) * L := by
      simp [Complex.mul_re]
    have h2 : ((1 - z.2) * (L : ℂ)).im = -(z.2.im * L) := by
      simp [Complex.mul_im]
    rw [h1, h2]
    have hY2 : (|z.2.im| * L)^2 = (z.2.im * L)^2 := by
      rw [show |z.2.im| * L = |z.2.im * L| by rw [abs_mul, abs_of_pos hL], sq_abs]
    rw [hY2]
    ring
  -- `max X Y > R`
  have hd1 : 1 ≤ max ((1 - z.2.re) * L) (|z.2.im| * L) :=
    le_trans (by exact_mod_cast hR : (1:ℝ) ≤ (R:ℝ)) hfar.le
  have hdK : max ((1 - z.2.re) * L) (|z.2.im| * L) ≤ (2:ℝ)^K := by
    have h3 : (1 - z.2.re) * L < (farM L z : ℝ) + 1 := by
      have hh : (1 - z.2.re) * L < ((Nat.floor ((1 - z.2.re) * L) : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      exact hh
    have h4 : max ((1 - z.2.re) * L) (|z.2.im| * L)
        ≤ max ((farM L z : ℝ)) (farY L z) + 1 := by
      refine max_le ?_ ?_
      · have hh := le_max_left ((farM L z : ℝ)) (farY L z)
        linarith
      · have hh := le_max_right ((farM L z : ℝ)) (farY L z)
        simp only [farY] at hh ⊢
        linarith
    linarith
  -- the layer cake
  have hlayer : (1:ℝ) / (max ((1 - z.2.re) * L) (|z.2.im| * L))^2
      ≤ ∑ k ∈ Finset.range (K+1),
          (8/(4:ℝ)^k) * (if max ((1 - z.2.re) * L) (|z.2.im| * L) ≤ (2:ℝ)^k then 1 else 0) :=
    one_div_sq_le_layer hd1 K hdK
  -- rewrite the layer sum into `farLayer`
  have hind : ∀ k : ℕ,
      (8/(4:ℝ)^k) * (if max ((1 - z.2.re) * L) (|z.2.im| * L) ≤ (2:ℝ)^k then 1 else 0)
        ≤ 8 * (1/4:ℝ)^k * (if (R:ℝ) ≤ (2:ℝ)^k ∧ farY L z ≤ (2:ℝ)^k
            ∧ (farM L z : ℝ) ≤ (2:ℝ)^k then 1 else 0) := by
    intro k
    have hiff : (if max ((1 - z.2.re) * L) (|z.2.im| * L) ≤ (2:ℝ)^k then (1:ℝ) else 0)
        ≤ (if (R:ℝ) ≤ (2:ℝ)^k ∧ farY L z ≤ (2:ℝ)^k ∧ (farM L z : ℝ) ≤ (2:ℝ)^k
            then 1 else 0) := by
      by_cases hc : max ((1 - z.2.re) * L) (|z.2.im| * L) ≤ (2:ℝ)^k
      · have hRk : (R:ℝ) ≤ (2:ℝ)^k := le_trans hfar.le hc
        have hYk : farY L z ≤ (2:ℝ)^k := le_trans (le_max_right _ _) hc
        have hMk : (farM L z : ℝ) ≤ (2:ℝ)^k :=
          le_trans (le_trans hdX (le_max_left _ _)) hc
        rw [if_pos hc, if_pos ⟨hRk, hYk, hMk⟩]
      · rw [if_neg hc]
        split_ifs with h2
        · norm_num
        · norm_num
    have h84 : (8:ℝ)/(4:ℝ)^k = 8*(1/4:ℝ)^k := by
      rw [div_eq_mul_inv, one_div, inv_pow]
    calc (8/(4:ℝ)^k) * (if max ((1 - z.2.re) * L) (|z.2.im| * L) ≤ (2:ℝ)^k then 1 else 0)
        ≤ (8/(4:ℝ)^k) * (if (R:ℝ) ≤ (2:ℝ)^k ∧ farY L z ≤ (2:ℝ)^k
            ∧ (farM L z : ℝ) ≤ (2:ℝ)^k then 1 else 0) :=
          mul_le_mul_of_nonneg_left hiff (by positivity)
      _ = 8 * (1/4:ℝ)^k * (if (R:ℝ) ≤ (2:ℝ)^k ∧ farY L z ≤ (2:ℝ)^k
            ∧ (farM L z : ℝ) ≤ (2:ℝ)^k then 1 else 0) := by rw [h84]
  -- put everything together
  have hb1 : 4 * Real.exp (-(49/10) * ((1 - z.2.re) * L)) / ‖(1 - z.2) * L‖ ^ 2
      = 4 * Real.exp (-(49/10) * ((1 - z.2.re) * L))
        * (1 / ‖(1 - z.2) * L‖ ^ 2) := by ring
  have hb2 : 1 / ‖(1 - z.2) * L‖ ^ 2 ≤ 1 / (max ((1 - z.2.re) * L) (|z.2.im| * L))^2 := by
    rw [hnorm]
    refine one_div_le_one_div_of_le ?_ ?_
    · exact pow_pos (lt_of_lt_of_le (by norm_num) hd1) 2
    · by_cases hxy : (1 - z.2.re) * L ≤ |z.2.im| * L
      · rw [max_eq_right hxy]; nlinarith [sq_nonneg ((1 - z.2.re) * L)]
      · rw [max_eq_left (le_of_not_ge hxy)]; nlinarith [sq_nonneg (|z.2.im| * L)]
  have hexp : Real.exp (-(49/10) * ((1 - z.2.re) * L))
      ≤ Real.exp (-(49/10) * (farM L z : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  calc ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖
      ≤ 4 * Real.exp (-(49/10) * ((1 - z.2.re) * L)) / ‖(1 - z.2) * L‖ ^ 2 := hk
    _ = 4 * Real.exp (-(49/10) * ((1 - z.2.re) * L)) * (1 / ‖(1 - z.2) * L‖ ^ 2) := hb1
    _ ≤ 4 * Real.exp (-(49/10) * (farM L z : ℝ))
          * (1 / (max ((1 - z.2.re) * L) (|z.2.im| * L))^2) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hexp (by norm_num)) hb2 (by positivity)
          (by positivity)
    _ ≤ 4 * Real.exp (-(49/10) * (farM L z : ℝ))
          * (∑ k ∈ Finset.range (K+1), (8/(4:ℝ)^k)
              * (if max ((1 - z.2.re) * L) (|z.2.im| * L) ≤ (2:ℝ)^k then 1 else 0)) := by
        exact mul_le_mul_of_nonneg_left hlayer (by positivity)
    _ = ∑ k ∈ Finset.range (K+1), 4 * Real.exp (-(49/10) * (farM L z : ℝ))
          * ((8/(4:ℝ)^k) * (if max ((1 - z.2.re) * L) (|z.2.im| * L) ≤ (2:ℝ)^k then 1 else 0)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range (K+1), 4 * Real.exp (-(49/10) * (farM L z : ℝ))
          * (8 * (1/4:ℝ)^k * (if (R:ℝ) ≤ (2:ℝ)^k ∧ farY L z ≤ (2:ℝ)^k
              ∧ (farM L z : ℝ) ≤ (2:ℝ)^k then 1 else 0)) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        exact mul_le_mul_of_nonneg_left (hind k) (by positivity)
    _ = 32 * Real.exp (-(49/10) * (farM L z : ℝ)) * farLayer K R (farM L z) (farY L z) := by
        rw [farLayer, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_); ring

/-- The bound for the multiplicity sum over a dyadic cell: the family zero-density bound in the
near-line region and the trivial uniform zero count beyond it. -/
def cellBound (q : ℕ) (C c0 L : ℝ) (m k : ℕ) : ℝ :=
  if ((m:ℝ) + 1) ≤ (3/5)*L then
    C * ((q:ℝ) * (2:ℝ)^k) ^ ((12/5 + 1/1000) * (((m:ℝ) + 1)/L))
  else
    (q:ℝ) * c0 * (4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2)

lemma cellMult_le_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q) {L : ℝ} (hLp : 0 < L) (hL1 : 1 ≤ L)
    {C c0 : ℝ} (hC : 0 < C) (hc0 : 0 < c0)
    (hfam : ∀ σ T : ℝ, 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T
        ≤ C * ((q:ℝ) * T) ^ ((12/5 + 1/1000) * (1 - σ)))
    (hball : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ))
        ≤ c0 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N:ℝ) + 2))
    {S : Finset (DirichletCharacter ℂ q × ℂ)}
    (hS : ∀ z ∈ S, z.1 ≠ 1 ∧ zeroMult z.1 z.2 ≠ 0) (m k : ℕ) :
    cellMult L S m k ≤ cellBound q C c0 L m k := by
  classical
  by_cases hd : ((m:ℝ) + 1) ≤ (3/5)*L
  · rw [cellBound, if_pos hd]
    set σ : ℝ := 1 - ((m:ℝ)+1)/L with hσdef
    have hσ0 : 0 ≤ σ := by
      rw [hσdef, sub_nonneg, div_le_one hLp]; linarith
    have hσ1 : σ ≤ 1 := by
      rw [hσdef]; have := div_nonneg (by positivity : (0:ℝ) ≤ (m:ℝ)+1) hLp.le; linarith
    have hT1 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    refine le_trans (finset_sum_le_fam C (12/5+1/1000) hfam hσ0 hσ1 hT1 ?_ ?_ ?_) ?_
    · intro z hz
      exact (hS z (Finset.mem_filter.mp hz).1).1
    · intro z hz
      obtain ⟨hzS, hzm, hzy⟩ := Finset.mem_filter.mp hz
      have h0 := (hS z hzS).2
      have hstrip := zeroMult_re z.1 (hS z hzS).1 h0
      have hX0 : 0 ≤ (1 - z.2.re) * L := by nlinarith [hstrip.2]
      have hmlt : (1 - z.2.re) * L < (m:ℝ) + 1 := by
        have hh : (1 - z.2.re) * L < ((farM L z : ℕ) : ℝ) + 1 := by
          simp only [farM]
          exact Nat.lt_floor_add_one _
        rw [hzm] at hh
        linarith
      rw [hσdef]
      have h2 : 1 - z.2.re < ((m:ℝ)+1)/L := by
        rw [lt_div_iff₀ hLp]; linarith
      linarith
    · intro z hz
      obtain ⟨hzS, hzm, hzy⟩ := Finset.mem_filter.mp hz
      have hz' : farY L z = |z.2.im| * L := rfl
      rw [hz'] at hzy
      have : |z.2.im| ≤ (2:ℝ)^k / L := by
        rw [le_div_iff₀ hLp]; linarith
      have h2k : (0:ℝ) < (2:ℝ)^k := pow_pos (by norm_num) k
      have : (2:ℝ)^k / L ≤ (2:ℝ)^k := by
        rw [div_le_iff₀ hLp]; nlinarith
      linarith
    · rw [hσdef]
      have : 1 - (1 - ((m:ℝ)+1)/L) = ((m:ℝ)+1)/L := by ring
      rw [this]
  · rw [cellBound, if_neg hd]
    have hT1 : (0:ℝ) ≤ (2:ℝ)^k := pow_nonneg (by norm_num) k
    refine le_trans (finset_sum_le_trivial (q := q) hc0 hball hT1 ?_ ?_ ?_) ?_
    · intro z hz
      exact (hS z (Finset.mem_filter.mp hz).1).1
    · intro z hz
      obtain ⟨hzS, hzm, hzy⟩ := Finset.mem_filter.mp hz
      exact le_of_lt (zeroMult_re z.1 (hS z hzS).1 (hS z hzS).2).1
    · intro z hz
      obtain ⟨hzS, hzm, hzy⟩ := Finset.mem_filter.mp hz
      have hz' : farY L z = |z.2.im| * L := rfl
      rw [hz'] at hzy
      have : |z.2.im| ≤ (2:ℝ)^k / L := by
        rw [le_div_iff₀ hLp]; linarith
      have : (2:ℝ)^k / L ≤ (2:ℝ)^k := by
        rw [div_le_iff₀ hLp]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) k]
      linarith
    · rfl

/-- The `k`-sum over a single cell in the near-line region. -/
lemma cell_k_sum_density {q R : ℝ} (hR1 : 1 ≤ R) (hq0 : 0 < q) {e : ℝ} (he : e ≤ 3/2)
    (N : ℕ) (m : ℕ) :
    (∑ k ∈ Finset.range N, (1/4:ℝ)^k
        * (if R ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
        * (q * (2:ℝ)^k)^e) ≤ 5 * q^e * R^(e-2) := by
  have h1 : (∑ k ∈ Finset.range N, (1/4:ℝ)^k
        * (if R ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
        * (q * (2:ℝ)^k)^e)
      ≤ ∑ k ∈ Finset.range N, (1/4:ℝ)^k * (if R ≤ (2:ℝ)^k then (1:ℝ) else 0)
        * (q * (2:ℝ)^k)^e := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    have hind : (if R ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
        ≤ (if R ≤ (2:ℝ)^k then (1:ℝ) else 0) := by
      by_cases hc : R ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k
      · rw [if_pos hc, if_pos hc.1]
      · rw [if_neg hc]
        split_ifs with h2 <;> norm_num
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hind (by positivity))
      (by positivity)
  refine le_trans h1 ?_
  have h2 : ∀ k : ℕ, (1/4:ℝ)^k * (if R ≤ (2:ℝ)^k then (1:ℝ) else 0) * (q * (2:ℝ)^k)^e
      = q^e * (if R ≤ (2:ℝ)^k then ((2:ℝ)^k)^(e-2) else 0) := by
    intro k
    by_cases hc : R ≤ (2:ℝ)^k
    · calc (1/4:ℝ)^k * (if R ≤ (2:ℝ)^k then (1:ℝ) else 0) * (q * (2:ℝ)^k)^e
          = (1/4:ℝ)^k * (q * (2:ℝ)^k)^e := by rw [if_pos hc, mul_one]
        _ = q^e * ((2:ℝ)^k)^(e-2) := quarter_mul_rpow k hq0
        _ = q^e * (if R ≤ (2:ℝ)^k then ((2:ℝ)^k)^(e-2) else 0) := by rw [if_pos hc]
    · rw [if_neg hc, if_neg hc]; ring
  rw [Finset.sum_congr rfl (fun k _ => h2 k)]
  rw [← Finset.mul_sum]
  have h3 := dyadic_tail_le he hR1 N
  calc q^e * ∑ k ∈ Finset.range N, (if R ≤ (2:ℝ)^k then ((2:ℝ)^k)^(e-2) else 0)
      ≤ q^e * (5 * R^(e-2)) := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hq0.le _)
    _ = 5 * q^e * R^(e-2) := by ring

/-- The `k`-sum over a single cell beyond the near-line region. -/
lemma cell_k_sum_trivial {q : ℝ} (hq : 1 ≤ q) (N : ℕ) (m k0 : ℕ) :
    (∑ k ∈ Finset.range N, (1/4:ℝ)^k
        * (if (k0:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
        * ((4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log q + 2)))
      ≤ 10 * Real.log q + 100 := by
  refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (sum_quarter_B_le hq N)
  by_cases hc : (k0:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k
  · rw [if_pos hc]
    have : (1/4:ℝ)^k * 1 * ((4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log q + 2))
        = (1/4:ℝ)^k * ((4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log q + 2)) := by ring
    rw [this]
  · rw [if_neg hc]
    rw [mul_zero, zero_mul]
    refine mul_nonneg (by positivity) (mul_nonneg (by positivity) ?_)
    have h2k : (0:ℝ) ≤ (2:ℝ)^k := pow_nonneg (by norm_num) k
    linarith [Real.log_nonneg (by linarith : (1:ℝ) ≤ 7 + (2:ℝ)^k), Real.log_nonneg hq]

lemma exp_neg_2_499_le : Real.exp (-(2.499:ℝ)) ≤ 1/8 := by
  have hlog8 : Real.log (8:ℝ) ≤ 2.499 := by
    have h := Real.log_two_lt_d9
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow] at *
    push_cast
    linarith
  calc Real.exp (-(2.499:ℝ)) ≤ Real.exp (Real.log (1/8)) := by
        refine Real.exp_le_exp.mpr ?_
        rw [one_div, Real.log_inv]
        linarith
    _ = 1/8 := Real.exp_log (by norm_num)

lemma two_rpow_half_eq_sqrt (x : ℝ) : x^(1/2:ℝ) = Real.sqrt x :=
  Real.sqrt_eq_rpow x ▸ rfl

/-- The double sum bound for the far-zero mass. -/
lemma msum_bound {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) {L : ℝ} (hLp : 0 < L)
    (hLdef : L = Real.log (q:ℝ)) (R : ℕ) (hR1 : 1 ≤ R)
    {C c0 : ℝ} (hC : 0 < C) (hc0 : 0 < c0) (Mmax N : ℕ) :
    (∑ m ∈ Finset.range Mmax, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k
            * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
            * cellBound q C c0 L m k)
      ≤ 6 * C * Real.exp (2401/1000) / Real.sqrt (R:ℝ) + 60000 * c0 / (q:ℝ) := by
  classical
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith
  have hq1' : (1:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 1 < q)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range Mmax)
      (fun m : ℕ => ((m:ℝ)+1) ≤ (3/5)*L)
      (fun m => Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k
          * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
          * cellBound q C c0 L m k)]
  have hP1 : (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (3/5)*L),
      Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k
          * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
          * cellBound q C c0 L m k)
      ≤ 6 * C * Real.exp (2401/1000) / Real.sqrt (R:ℝ) := by
    have hstep : ∀ m : ℕ, m ∈ (Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (3/5)*L) →
        Real.exp (-(49/10) * (m:ℝ)) * (∑ k ∈ Finset.range N, (1/4:ℝ)^k
            * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
            * cellBound q C c0 L m k)
        ≤ Real.exp (2401/1000) * Real.exp (-(2.499:ℝ) * (m:ℝ))
            * (5 * C * (R:ℝ)^(-(1/2:ℝ))) := by
      intro m hm
      rw [Finset.mem_filter] at hm
      obtain ⟨-, hmc⟩ := hm
      have hm1 : ((m:ℝ)+1)/L ≤ 3/5 := by
        rw [div_le_iff₀ hLp]; linarith
      have he1 : (12/5 + 1/1000) * (((m:ℝ)+1)/L) ≤ 3/2 := by nlinarith
      have hcb : ∀ k ∈ Finset.range N, cellBound q C c0 L m k
          = C * ((q:ℝ) * (2:ℝ)^k) ^ ((12/5 + 1/1000) * (((m:ℝ)+1)/L)) := by
        intro k _
        rw [cellBound, if_pos hmc]
      rw [Finset.sum_congr rfl (fun k hk => by rw [hcb k hk])]
      rw [show (∑ k ∈ Finset.range N, (1/4:ℝ)^k
            * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
            * (C * ((q:ℝ) * (2:ℝ)^k) ^ ((12/5 + 1/1000) * (((m:ℝ)+1)/L))))
          = C * ∑ k ∈ Finset.range N, (1/4:ℝ)^k
            * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
            * ((q:ℝ) * (2:ℝ)^k) ^ ((12/5 + 1/1000) * (((m:ℝ)+1)/L)) from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => by ring)]
      have hk := cell_k_sum_density (q := (q:ℝ)) (R := (R:ℝ))
        (e := (12/5 + 1/1000) * (((m:ℝ)+1)/L)) (by exact_mod_cast hR1) hq0 he1 N m
      -- convert `q^e` into an exponential, and `R^(e-2)` into `R^(-1/2)`
      have hqe : ((q:ℝ)) ^ ((12/5 + 1/1000) * (((m:ℝ)+1)/L))
          = Real.exp ((12/5 + 1/1000) * ((m:ℝ)+1)) := by
        rw [show (12/5 + 1/1000) * (((m:ℝ)+1)/L)
            = ((12/5 + 1/1000) * ((m:ℝ)+1)) / Real.log (q:ℝ) by rw [hLdef]; ring]
        exact rpow_div_log hq1' _
      have hRe : (R:ℝ) ^ ((12/5 + 1/1000) * (((m:ℝ)+1)/L) - 2) ≤ (R:ℝ)^(-(1/2:ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hR1) ?_
        linarith
      have hkey : C * (∑ k ∈ Finset.range N, (1/4:ℝ)^k
            * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
            * ((q:ℝ) * (2:ℝ)^k) ^ ((12/5 + 1/1000) * (((m:ℝ)+1)/L)))
          ≤ 5 * C * Real.exp ((12/5 + 1/1000) * ((m:ℝ)+1)) * (R:ℝ)^(-(1/2:ℝ)) := by
        refine le_trans (mul_le_mul_of_nonneg_left hk hC.le) ?_
        rw [hqe]
        have h5 : Real.exp ((12/5 + 1/1000) * ((m:ℝ)+1))
              * (R:ℝ) ^ ((12/5+1/1000)*(((m:ℝ)+1)/L) - 2)
            ≤ Real.exp ((12/5 + 1/1000) * ((m:ℝ)+1)) * (R:ℝ)^(-(1/2:ℝ)) :=
          mul_le_mul_of_nonneg_left hRe (Real.exp_nonneg _)
        have hR0 : (0:ℝ) < (R:ℝ)^(-(1/2:ℝ)) := Real.rpow_pos_of_pos (by exact_mod_cast hR1) _
        have hE0 : (0:ℝ) < Real.exp ((12/5 + 1/1000) * ((m:ℝ)+1)) := Real.exp_pos _
        nlinarith [h5, hC.le, hR0, hE0]
      refine le_trans (mul_le_mul_of_nonneg_left hkey (Real.exp_nonneg _)) ?_
      · have hE : Real.exp (-(49/10) * (m:ℝ)) * Real.exp ((12/5 + 1/1000) * ((m:ℝ)+1))
            = Real.exp (2401/1000) * Real.exp (-(2.499:ℝ) * (m:ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [show Real.exp (-(49/10) * (m:ℝ))
              * (5 * C * Real.exp ((12/5 + 1/1000) * ((m:ℝ)+1)) * (R:ℝ)^(-(1/2:ℝ)))
            = (Real.exp (-(49/10) * (m:ℝ)) * Real.exp ((12/5 + 1/1000) * ((m:ℝ)+1)))
              * (5 * C * (R:ℝ)^(-(1/2:ℝ))) by ring]
        rw [hE]
    -- geometric series in `m`
    have hgeo : (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (3/5)*L),
        Real.exp (-(2.499:ℝ) * (m:ℝ))) ≤ 8/7 := by
      have hpow : ∀ m : ℕ, Real.exp (-(2.499:ℝ) * (m:ℝ)) = (Real.exp (-(2.499:ℝ)))^m := by
        intro m
        rw [mul_comm (-2.499:ℝ), Real.exp_nat_mul]
      rw [Finset.sum_congr rfl (fun m _ => hpow m)]
      have h1 := Commons.Analysis.Asymptotics.geom_finset_le
        (r := Real.exp (-(2.499:ℝ))) (le_of_lt (Real.exp_pos _)) (by
          rw [Real.exp_lt_one_iff]; norm_num)
        ((Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (3/5)*L))
      refine le_trans h1 ?_
      have hr : Real.exp (-(2.499:ℝ)) ≤ 1/8 := exp_neg_2_499_le
      have hpos : (0:ℝ) < 1 - Real.exp (-(2.499:ℝ)) := by
        have := Real.exp_pos (-(2.499:ℝ)); linarith
      rw [div_le_iff₀ hpos]
      nlinarith [hr]
    refine le_trans (Finset.sum_le_sum (fun m hm => hstep m hm)) ?_
    rw [show (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (3/5)*L),
        Real.exp (2401/1000) * Real.exp (-(2.499:ℝ) * (m:ℝ))
          * (5 * C * (R:ℝ)^(-(1/2:ℝ))))
        = Real.exp (2401/1000) * (5 * C * (R:ℝ)^(-(1/2:ℝ)))
          * (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (3/5)*L),
              Real.exp (-(2.499:ℝ) * (m:ℝ))) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => by ring)]
    have hsqrt : (R:ℝ)^(-(1/2:ℝ)) = 1 / Real.sqrt (R:ℝ) := by
      rw [Real.rpow_neg (by exact_mod_cast (Nat.zero_le R)), Real.sqrt_eq_rpow, inv_eq_one_div]
    rw [hsqrt]
    have hpos : 0 < Real.sqrt (R:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hR1)
    rw [show Real.exp (2401/1000) * (5 * C * (1 / Real.sqrt (R:ℝ)))
          * (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (3/5)*L),
              Real.exp (-(2.499:ℝ) * (m:ℝ)))
        = (Real.exp (2401/1000) * (5 * C *
            (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (3/5)*L),
              Real.exp (-(2.499:ℝ) * (m:ℝ))))) / Real.sqrt (R:ℝ) by ring]
    rw [show (6 * C * Real.exp (2401/1000) / Real.sqrt (R:ℝ))
        = (6 * C * Real.exp (2401/1000)) / Real.sqrt (R:ℝ) by ring]
    refine div_le_div_of_nonneg_right ?_ hpos.le
    have hS : (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (3/5)*L),
        Real.exp (-(2.499:ℝ) * (m:ℝ))) ≤ 6/5 := by linarith [hgeo]
    have hposC : (0:ℝ) ≤ C * Real.exp (2401/1000) := (mul_pos hC (Real.exp_pos _)).le
    nlinarith [hS, hposC, mul_nonneg hposC (by linarith [hS] : (0:ℝ) ≤ 6/5 -
      (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ((m:ℝ)+1) ≤ (3/5)*L),
        Real.exp (-(2.499:ℝ) * (m:ℝ))))]
  have hP2 : (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ¬(((m:ℝ)+1) ≤ (3/5)*L)),
      Real.exp (-(49/10) * (m:ℝ)) * ∑ k ∈ Finset.range N, (1/4:ℝ)^k
          * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
          * cellBound q C c0 L m k)
      ≤ 60000 * c0 / (q:ℝ) := by
    have hstep : ∀ m : ℕ, m ∈ (Finset.range Mmax).filter (fun m : ℕ => ¬(((m:ℝ)+1) ≤ (3/5)*L)) →
        Real.exp (-(49/10) * (m:ℝ)) * (∑ k ∈ Finset.range N, (1/4:ℝ)^k
            * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
            * cellBound q C c0 L m k)
        ≤ Real.exp (-(49/10) * (m:ℝ)) * ((q:ℝ) * c0 * (10 * L + 100)) := by
      intro m hm
      rw [Finset.mem_filter] at hm
      obtain ⟨-, hmc⟩ := hm
      have hcb : ∀ k ∈ Finset.range N, cellBound q C c0 L m k
          = (q:ℝ) * c0 * (4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2) := by
        intro k _
        rw [cellBound, if_neg hmc]
      rw [Finset.sum_congr rfl (fun k hk => by rw [hcb k hk])]
      rw [show (∑ k ∈ Finset.range N, (1/4:ℝ)^k
            * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
            * ((q:ℝ) * c0 * (4 + (2:ℝ)^k)
              * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2)))
          = (q:ℝ) * c0 * ∑ k ∈ Finset.range N, (1/4:ℝ)^k
            * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
            * ((4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2)) from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => by ring)]
      have hk := cell_k_sum_trivial (q := (q:ℝ)) hq1 N m R
      have hlogq : Real.log (q:ℝ) = L := hLdef.symm
      rw [hlogq] at hk ⊢
      refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk
        (mul_nonneg hq0.le hc0.le)) (Real.exp_nonneg _)) ?_
      refine le_of_eq ?_
      ring
    refine le_trans (Finset.sum_le_sum (fun m hm => hstep m hm)) ?_
    rw [show (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ¬(((m:ℝ)+1) ≤ (3/5)*L)),
        Real.exp (-(49/10) * (m:ℝ)) * ((q:ℝ) * c0 * (10 * L + 100)))
        = ((q:ℝ) * c0 * (10 * L + 100))
          * (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ¬(((m:ℝ)+1) ≤ (3/5)*L)),
              Real.exp (-(49/10) * (m:ℝ))) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => by ring)]
    have hgeo : (∑ m ∈ (Finset.range Mmax).filter (fun m : ℕ => ¬(((m:ℝ)+1) ≤ (3/5)*L)),
        Real.exp (-(49/10) * (m:ℝ))) ≤ 500 * Real.exp (-(2.94)*L) :=
      geom_exp_tail hLp (fun m hm => by
        rw [Finset.mem_filter] at hm
        have := not_le.mp hm.2
        linarith)
    refine le_trans (mul_le_mul_of_nonneg_left hgeo (by positivity)) ?_
    · -- numeric: `q * exp (-2.94 L) * (10 L + 100) ≤ 120 / q`
      have hexpL : Real.exp (-(2.94)*L) = (q:ℝ)^(-(2.94:ℝ)) := by
        rw [Real.rpow_def_of_pos hq0, hLdef]; ring_nf
      have hlogq_le : L ≤ (q:ℝ)^(0.9:ℝ) / 0.9 := by
        rw [hLdef]; exact Real.log_le_rpow_div hq0.le (by norm_num)
      have hq09 : (q:ℝ)^(0.9:ℝ) = Real.exp (0.9 * L) := by
        rw [Real.rpow_def_of_pos hq0, hLdef]; ring_nf
      rw [hexpL]
      have hb1 : (q:ℝ) * (q:ℝ)^(-(2.94:ℝ)) = (q:ℝ)^(-(1.94:ℝ)) := by
        have h2 : (q:ℝ)^(1:ℝ) * (q:ℝ)^(-(2.94:ℝ)) = (q:ℝ)^(-(1.94:ℝ)) := by
          rw [← Real.rpow_add hq0]
          norm_num
        rwa [Real.rpow_one] at h2
      rw [show (q:ℝ) * c0 * (10 * L + 100) * (500 * (q:ℝ)^(-(2.94:ℝ)))
          = (q:ℝ) * (q:ℝ)^(-(2.94:ℝ)) * (500 * c0 * (10 * L + 100)) by ring]
      rw [hb1]
      rw [show (q:ℝ)^(-(1.94:ℝ)) = Real.exp (-1.94 * L) by
        rw [Real.rpow_def_of_pos hq0, hLdef]; ring_nf]
      rw [le_div_iff₀ hq0]
      have h1 : Real.exp (-1.94 * L) * (10 * L + 100) * (q:ℝ) ≤ 120 := by
        have h2 : (q:ℝ) = Real.exp L := by rw [← Real.exp_log hq0, hLdef]
        rw [h2]
        rw [show Real.exp (-1.94 * L) * (10 * L + 100) * Real.exp L
            = Real.exp (-1.94 * L) * Real.exp L * (10 * L + 100) by ring]
        rw [← Real.exp_add]
        have : -1.94 * L + L = -(0.94) * L := by ring
        rw [this]
        have h3 : 10 * L + 100 ≤ 120 * Real.exp (0.94 * L) := by
          have h4 : Real.exp (0.9 * L) = (q:ℝ)^(0.9:ℝ) := hq09.symm
          have h5 : 10 * L ≤ 10 * ((q:ℝ)^(0.9:ℝ) / 0.9) := by linarith [hlogq_le]
          have h6 : 10 * ((q:ℝ)^(0.9:ℝ) / 0.9) = (10/0.9) * Real.exp (0.9*L) := by
            rw [hq09]; ring
          have h7 : Real.exp (0.9*L) ≤ Real.exp (0.94*L) := Real.exp_le_exp.mpr (by nlinarith)
          have h8 : (1:ℝ) ≤ Real.exp (0.94*L) := Real.one_le_exp (by linarith [hLp])
          nlinarith [h5, h6, h7, h8, Real.exp_pos (0.94*L)]
        calc Real.exp (-(0.94) * L) * (10 * L + 100)
            ≤ Real.exp (-(0.94) * L) * (120 * Real.exp (0.94 * L)) :=
              mul_le_mul_of_nonneg_left h3 (Real.exp_nonneg _)
          _ = 120 * (Real.exp (-(0.94)*L) * Real.exp (0.94*L)) := by ring
          _ = 120 := by rw [← Real.exp_add]; norm_num
      nlinarith [h1, hc0.le]
  linarith [hP1, hP2]

lemma finset_bound (q : ℕ) [NeZero q] (hq : 2 ≤ q) (R : ℕ) (hR : 1 ≤ R)
    (C c0 : ℝ) (hC : 0 < C) (hc0 : 0 < c0)
    (hfam : ∀ σ T : ℝ, 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T
        ≤ C * ((q:ℝ) * T) ^ ((12/5 + 1/1000) * (1 - σ)))
    (hball : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ))
        ≤ c0 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N:ℝ) + 2))
    (hL : 1000 ≤ Real.log (q:ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ)) :
    (∑ z ∈ S, (if z.1 = 1 then 0 else if InBox q (R:ℝ) z.2 then 0
        else (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * Real.log (q:ℝ))‖))
      ≤ 200 * C * Real.exp (2401/1000) / Real.sqrt (R:ℝ) + 2 * (10:ℝ)^6 * c0 / (q:ℝ) := by
  classical
  set L : ℝ := Real.log (q:ℝ) with hLdef
  have hL1000 : 1000 ≤ L := by rw [hLdef]; exact hL
  have hLpos : 0 < L := by linarith
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith
  set S₁ : Finset (DirichletCharacter ℂ q × ℂ) :=
    (S.filter (fun z => z.1 ≠ 1 ∧ ¬ InBox q (R:ℝ) z.2)).filter
      (fun z => zeroMult z.1 z.2 ≠ 0) with hS1
  have hS1mem : ∀ z ∈ S₁, z ∈ S ∧ z.1 ≠ 1 ∧ ¬ InBox q (R:ℝ) z.2
      ∧ zeroMult z.1 z.2 ≠ 0 := by
    intro z hz
    rw [hS1, Finset.mem_filter, Finset.mem_filter] at hz
    exact ⟨hz.1.1, hz.1.2.1, hz.1.2.2, hz.2⟩
  -- step 1: reduce to the far, non-principal, nonzero-multiplicity pairs
  have hstep1 : (∑ z ∈ S, (if z.1 = 1 then 0 else if InBox q (R:ℝ) z.2 then 0
        else (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖))
      = ∑ z ∈ S₁, (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖ := by
    have hS1sub : S₁ ⊆ S := fun z hz => (hS1mem z hz).1
    have hzero : ∀ z ∈ S, z ∉ S₁ →
        (if z.1 = 1 then 0 else if InBox q (R:ℝ) z.2 then 0
          else (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖) = 0 := by
      intro z hz hnot
      by_cases h1 : z.1 = 1
      · simp [h1]
      · have h3 : InBox q (R:ℝ) z.2 ∨ zeroMult z.1 z.2 = 0 := by
          by_contra hc
          push_neg at hc
          exact hnot (by
            rw [hS1, Finset.mem_filter, Finset.mem_filter]
            exact ⟨⟨hz, h1, hc.1⟩, hc.2⟩)
        rcases h3 with h3 | h3
        · simp [h1, h3]
        · simp [h1, h3]
    have hcong : ∀ z ∈ S₁, (if z.1 = 1 then 0 else if InBox q (R:ℝ) z.2 then 0
          else (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖)
        = (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖ := by
      intro z hz
      obtain ⟨-, hz1, hz2, -⟩ := hS1mem z hz
      simp only [if_neg hz1, if_neg hz2]
    rw [← Finset.sum_subset hS1sub hzero]
    exact Finset.sum_congr rfl hcong
  rw [hstep1]
  -- the bound `K` for the layer cake
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ z ∈ S₁,
      max (farM L z : ℝ) (farY L z) + 1 ≤ (2:ℝ)^K := by
    refine ⟨S₁.sup (fun z => Nat.ceil (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))), ?_⟩
    intro z hz
    have h1 : Nat.ceil (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))
        ≤ S₁.sup (fun z => Nat.ceil (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))) :=
      Finset.le_sup (f := fun z => Nat.ceil
        (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))) hz
    have h2 : Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1)
        ≤ ((S₁.sup (fun z => Nat.ceil
          (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))) : ℕ) : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
    have h3 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) h2
    have h4 : (2:ℝ) ^ (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))
        = (max (farM L z : ℝ) (farY L z) + 1 : ℝ) :=
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    rw [h4, Real.rpow_natCast] at h3
    exact h3
  -- pointwise weight bound
  have hweight : ∀ z ∈ S₁, (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖
      ≤ 32 * (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49/10) * (farM L z : ℝ))
          * farLayer K R (farM L z) (farY L z) := by
    intro z hz
    obtain ⟨-, hz1, hz2, hz0⟩ := hS1mem z hz
    have hfar : (R:ℝ) < max ((1 - z.2.re) * L) (|z.2.im| * L) := by
      by_contra hc
      push_neg at hc
      refine hz2 ⟨?_, ?_⟩
      · have hX : (1 - z.2.re) * L ≤ (R:ℝ) := le_trans (le_max_left _ _) hc
        simpa only [lamOf, hLdef] using hX
      · have hY : |z.2.im| * L ≤ (R:ℝ) := le_trans (le_max_right _ _) hc
        simpa only [hLdef] using hY
    have h1 := Hk_le_farLayer R hR hLpos hz1 hz0 hfar K (hK z hz)
    calc (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖
        ≤ (zeroMult z.1 z.2 : ℝ) * (32 * Real.exp (-(49/10) * (farM L z : ℝ))
            * farLayer K R (farM L z) (farY L z)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = 32 * (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49/10) * (farM L z : ℝ))
            * farLayer K R (farM L z) (farY L z) := by ring
  -- step 2: sum the pointwise bounds
  have hstep2 : (∑ z ∈ S₁, (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖)
      ≤ 32 * ∑ m ∈ Finset.range (Nat.ceil L + 1),
          Real.exp (-(49/10) * (m:ℝ))
          * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k
              * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
              * cellMult L S₁ m k := by
    refine le_trans (Finset.sum_le_sum hweight) ?_
    -- expand the layer sums
    have hexp : (∑ z ∈ S₁, 32 * (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49/10) * (farM L z : ℝ))
          * farLayer K R (farM L z) (farY L z))
        = 32 * ∑ z ∈ S₁, ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k
            * (if (R:ℝ) ≤ (2:ℝ)^k ∧ farY L z ≤ (2:ℝ)^k ∧ (farM L z : ℝ) ≤ (2:ℝ)^k
                then (1:ℝ) else 0)
            * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49/10) * (farM L z : ℝ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [farLayer, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [hexp]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 32)
    -- reindex the outer `z`-sum by the size `farM` of the spectral parameter
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := S₁) (t := Finset.range (Nat.ceil L + 1)) (g := fun z => farM L z)
      (f := fun z => ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k
        * (if (R:ℝ) ≤ (2:ℝ)^k ∧ farY L z ≤ (2:ℝ)^k ∧ (farM L z : ℝ) ≤ (2:ℝ)^k
            then (1:ℝ) else 0)
        * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49/10) * (farM L z : ℝ))))
      (fun z hz => by
        have h := zeroMult_re z.1 (hS1mem z hz).2.1 (hS1mem z hz).2.2.2
        have hX0 : 0 ≤ (1 - z.2.re) * L := by nlinarith [h.2]
        rw [Finset.mem_range]
        have hlt : (farM L z : ℝ) < L := by
          have h2 : (farM L z : ℝ) ≤ (1 - z.2.re) * L := Nat.floor_le hX0
          nlinarith [h.1]
        have : ((farM L z : ℕ) : ℝ) < ((Nat.ceil L + 1 : ℕ) : ℝ) := by
          push_cast
          linarith [Nat.le_ceil L]
        exact_mod_cast this)
    rw [← hfib]
    refine Finset.sum_le_sum (fun m _ => ?_)
    rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun k _ => ?_)
    -- the conditional involving `farY` becomes a filter, and `farM z = m` on the cell
    have h1 : (∑ z ∈ S₁.filter (fun z => farM L z = m), (1/4:ℝ)^k
          * (if (R:ℝ) ≤ (2:ℝ)^k ∧ farY L z ≤ (2:ℝ)^k ∧ (farM L z : ℝ) ≤ (2:ℝ)^k
              then (1:ℝ) else 0)
          * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49/10) * (farM L z : ℝ))))
        = ∑ z ∈ S₁.filter (fun z => farM L z = m),
            (if farY L z ≤ (2:ℝ)^k
              then (1/4:ℝ)^k * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
                * (Real.exp (-(49/10) * (m:ℝ)) * (zeroMult z.1 z.2 : ℝ))
              else 0) := by
      refine Finset.sum_congr rfl (fun z hz => ?_)
      have hzm : farM L z = m := (Finset.mem_filter.mp hz).2
      rw [hzm]
      by_cases h : farY L z ≤ (2:ℝ)^k
      · by_cases hc : (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k
        · rw [if_pos h]
          rw [if_pos ⟨hc.1, h, hc.2⟩]
          rw [if_pos hc]
          ring
        · rw [if_pos h]
          rw [if_neg (fun hcc : (R:ℝ) ≤ (2:ℝ)^k ∧ farY L z ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k
            => hc ⟨hcc.1, hcc.2.2⟩)]
          rw [if_neg hc]
          ring
      · rw [if_neg h]
        rw [if_neg (fun hcc : (R:ℝ) ≤ (2:ℝ)^k ∧ farY L z ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k
          => h hcc.2.1)]
        ring
    rw [h1, ← Finset.sum_filter]
    rw [cellMult]
    rw [show (∑ z ∈ S₁.filter (fun z => farM L z = m ∧ farY L z ≤ (2:ℝ)^k),
              (zeroMult z.1 z.2 : ℝ))
          = ∑ z ∈ (S₁.filter (fun z => farM L z = m)).filter (fun z => farY L z ≤ (2:ℝ)^k),
              (zeroMult z.1 z.2 : ℝ) from
        Finset.sum_congr (Finset.filter_filter (fun z => farM L z = m)
          (fun z => farY L z ≤ (2:ℝ)^k) S₁).symm (fun _ _ => rfl)]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun z _ => le_of_eq (by ring))
  -- bound the double sum
  refine le_trans hstep2 ?_
  have hcell2 : (∑ m ∈ Finset.range (Nat.ceil L + 1), Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k
            * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
            * cellMult L S₁ m k)
      ≤ (∑ m ∈ Finset.range (Nat.ceil L + 1), Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k
            * (if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then (1:ℝ) else 0)
            * cellBound q C c0 L m k) := by
    refine Finset.sum_le_sum (fun m _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
    refine Finset.sum_le_sum (fun k _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ ?_
    · exact cellMult_le_bound hq hLpos hL1 hC hc0 hfam hball
        (fun z hz => ⟨(hS1mem z hz).2.1, (hS1mem z hz).2.2.2⟩) m k
    · by_cases hc : (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k
      · rw [if_pos hc]; positivity
      · rw [if_neg hc]; norm_num
  refine le_trans (mul_le_mul_of_nonneg_left hcell2 (by norm_num : (0:ℝ) ≤ 32)) ?_
  have hfin := msum_bound hq hLpos hLdef R hR hC hc0 (Nat.ceil L + 1) (K+1)
  refine le_trans (mul_le_mul_of_nonneg_left hfin (by norm_num : (0:ℝ) ≤ 32)) ?_
  have hRpos : 0 < Real.sqrt (R:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hR)
  have h1 : 32 * (6 * C * Real.exp (2401/1000) / Real.sqrt (R:ℝ))
      ≤ 200 * C * Real.exp (2401/1000) / Real.sqrt (R:ℝ) := by
    rw [show (32:ℝ) * (6 * C * Real.exp (2401/1000) / Real.sqrt (R:ℝ))
        = (32 * (6 * C * Real.exp (2401/1000))) / Real.sqrt (R:ℝ) by ring]
    rw [div_le_div_iff_of_pos_right hRpos]
    nlinarith [hC.le, Real.exp_pos (2401/1000)]
  have h2 : 32 * (60000 * c0 / (q:ℝ)) ≤ 2 * (10:ℝ)^6 * c0 / (q:ℝ) := by
    rw [show (32:ℝ) * (60000 * c0 / (q:ℝ)) = (32 * (60000 * c0)) / (q:ℝ) by ring]
    rw [div_le_div_iff_of_pos_right hq0]
    nlinarith [hc0.le]
  calc 32 * (6 * C * Real.exp (2401/1000) / Real.sqrt (R:ℝ) + 60000 * c0 / (q:ℝ))
      = 32 * (6 * C * Real.exp (2401/1000) / Real.sqrt (R:ℝ))
        + 32 * (60000 * c0 / (q:ℝ)) := by ring
    _ ≤ 200 * C * Real.exp (2401/1000) / Real.sqrt (R:ℝ) + 2 * (10:ℝ)^6 * c0 / (q:ℝ) :=
        add_le_add h1 h2

/-- **Heath-Brown (1992), Lemma 13.2 (far zeros).**  The family zero-density hypothesis
(`FamilyZeroDensityHyp`, Heath-Brown's (1.4)) implies the far-zero bound `FarBoundHyp`: the total
mass, with multiplicity and weighted by the kernel `Hk (11/2) (3/10)`, of the zeros of all
non-principal characters mod `q` lying **outside** the box `InBox q R` can be made arbitrarily
small by taking `R` large and `q` large. -/
theorem FarBoundOfDensity :
    Work.LinnikAreas.FamilyZeroDensityHyp → Work.LinnikAreas.FarBoundHyp := by
  intro hd
  obtain ⟨C, hCpos, hCfam⟩ := hd (1/1000) (by norm_num)
  obtain ⟨c0, hc0pos, hball⟩ :=
    Commons.NumberTheory.DirichletCharacter.completedL_ballZeroCount_uniform
  intro ε hε
  set A : ℝ := 400 * C * Real.exp (2401/1000) / ε with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  set Rn : ℕ := Nat.floor (A^2) + 2 with hRndef
  have hRn1 : 1 ≤ Rn := by rw [hRndef]; omega
  have hRval : (0:ℝ) < (Rn:ℝ) := by exact_mod_cast (by omega : 0 < Rn)
  -- (i) the "density" part of the bound is `≤ ε/2`
  have hsqrt : A ≤ Real.sqrt (Rn:ℝ) := by
    refine (Real.le_sqrt hApos.le hRval.le).mpr ?_
    have h1 : A^2 < ((Nat.floor (A^2) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (A^2)
    have h2 : ((Nat.floor (A^2) : ℕ) : ℝ) + 1 ≤ ((Rn : ℕ) : ℝ) := by
      rw [hRndef]; push_cast; linarith
    linarith
  have hKey : A * ε = 400 * C * Real.exp (2401/1000) := by
    rw [hAdef, div_mul_cancel₀ _ hε.ne']
  have hBhalf : 200 * C * Real.exp (2401/1000) / Real.sqrt (Rn:ℝ) ≤ ε/2 := by
    have hsqrtpos : 0 < Real.sqrt (Rn:ℝ) := Real.sqrt_pos.mpr hRval
    rw [div_le_iff₀ hsqrtpos]
    have h2 : A * ε ≤ ε * Real.sqrt (Rn:ℝ) := by nlinarith [hsqrt, hε.le]
    nlinarith [hKey, h2, Real.exp_pos (2401/1000), hCpos]
  -- (ii) the trivial part is `≤ ε/2` for all large `q`
  set q₀ : ℕ := max (max (Nat.ceil (Real.exp 1000))
      (Nat.ceil (4 * (10:ℝ)^6 * c0 / ε))) 2 with hq₀def
  have hq₀2 : 2 ≤ q₀ := by rw [hq₀def]; exact le_max_right _ _
  have hq₀exp : Nat.ceil (Real.exp 1000) ≤ q₀ := by
    rw [hq₀def]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hq₀eps : Nat.ceil (4 * (10:ℝ)^6 * c0 / ε) ≤ q₀ := by
    rw [hq₀def]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨(Rn:ℝ), hRval, q₀, ?_⟩
  intro q hq hqN
  have hq2 : 2 ≤ q := le_trans hq₀2 hq
  have hq0' : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hexpq : Real.exp 1000 ≤ (q:ℝ) := by
    have h1 : Real.exp 1000 ≤ ((Nat.ceil (Real.exp 1000) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.exp 1000) : ℕ) : ℝ) ≤ (q:ℝ) := by
      refine Nat.cast_le.mpr (le_trans hq₀exp hq)
    linarith
  have hL : 1000 ≤ Real.log (q:ℝ) := by
    rw [← Real.log_exp 1000]
    exact Real.log_le_log (Real.exp_pos 1000) hexpq
  have hqeps : 4 * (10:ℝ)^6 * c0 / ε ≤ (q:ℝ) := by
    have h1 : 4 * (10:ℝ)^6 * c0 / ε
        ≤ ((Nat.ceil (4 * (10:ℝ)^6 * c0 / ε) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (4 * (10:ℝ)^6 * c0 / ε) : ℕ) : ℝ) ≤ (q:ℝ) := by
      refine Nat.cast_le.mpr (le_trans hq₀eps hq)
    linarith
  have h2e6 : 2 * (10:ℝ)^6 * c0 / (q:ℝ) ≤ ε/2 := by
    have hh : 4 * (10:ℝ)^6 * c0 ≤ ε * (q:ℝ) := by
      rw [div_le_iff₀ hε] at hqeps
      linarith [hqeps]
    rw [div_le_iff₀ hq0']
    nlinarith [hh]
  -- (iii) the total far-zero mass
  let F : DirichletCharacter ℂ q × ℂ → ℝ := fun z =>
    if z.1 = 1 then 0 else if InBox q (Rn:ℝ) z.2 then 0
      else (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * Real.log (q:ℝ))‖
  have hFbound : ∀ u : Finset (DirichletCharacter ℂ q × ℂ), ∑ z ∈ u, F z
      ≤ 200 * C * Real.exp (2401/1000) / Real.sqrt (Rn:ℝ) + 2 * (10:ℝ)^6 * c0 / (q:ℝ) := by
    intro u
    show ∑ z ∈ u, (if z.1 = 1 then 0 else if InBox q (Rn:ℝ) z.2 then 0
        else (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * Real.log (q:ℝ))‖)
      ≤ 200 * C * Real.exp (2401/1000) / Real.sqrt (Rn:ℝ) + 2 * (10:ℝ)^6 * c0 / (q:ℝ)
    exact finset_bound q hq2 Rn hRn1 C c0 hCpos hc0pos
      (fun σ T h0 h1 hT => hCfam q hq2 σ T h0 h1 hT) hball hL u
  have hFnn : 0 ≤ F := fun z => by
    show 0 ≤ (if z.1 = 1 then 0 else if InBox q (Rn:ℝ) z.2 then 0
      else (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * Real.log (q:ℝ))‖)
    split_ifs with h1 h2
    · exact le_refl 0
    · exact le_refl 0
    · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hsumm : Summable F := summable_of_sum_le hFnn hFbound
  have htsum : ∑' z : DirichletCharacter ℂ q × ℂ, F z
      ≤ 200 * C * Real.exp (2401/1000) / Real.sqrt (Rn:ℝ) + 2 * (10:ℝ)^6 * c0 / (q:ℝ) :=
    Real.tsum_le_of_sum_le hFnn hFbound
  rw [Summable.tsum_prod hsumm] at htsum
  rw [tsum_fintype] at htsum
  have hstep : (∑ χ : DirichletCharacter ℂ q, ∑' ρ : ℂ, F (χ, ρ))
      = ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          farSum q (11/2) (3/10) (Rn:ℝ) χ := by
    have h1z : (∑' ρ : ℂ, F ((1 : DirichletCharacter ℂ q), ρ)) = 0 := by
      rw [tsum_congr (fun ρ => ?_), tsum_zero]
      have hp : ((1 : DirichletCharacter ℂ q), ρ).1 = 1 := rfl
      show (if ((1 : DirichletCharacter ℂ q), ρ).1 = 1 then (0:ℝ) else _) = 0
      rw [if_pos hp]
    rw [← Finset.sum_erase_add _ (fun χ => ∑' ρ : ℂ, F (χ, ρ))
        (Finset.mem_univ (1 : DirichletCharacter ℂ q)), h1z, add_zero]
    refine Finset.sum_congr rfl (fun χ hχ => ?_)
    have hχ1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
    rw [farSum]
    refine tsum_congr (fun ρ => ?_)
    have hpt : (χ, ρ).1 ≠ 1 := by simpa using hχ1
    simp only [F]
    rw [if_neg hpt]
  rw [hstep] at htsum
  have hfin : 200 * C * Real.exp (2401/1000) / Real.sqrt (Rn:ℝ)
      + 2 * (10:ℝ)^6 * c0 / (q:ℝ) ≤ ε := by
    linarith [hBhalf, h2e6]
  linarith [htsum, hfin]

end Work.LinnikAreas
