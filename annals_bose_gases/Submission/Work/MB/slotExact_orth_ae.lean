import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotExact_orth_gen
import Submission.Work.MB.slotExact_comp_ae
import Submission.Work.MB.slotProj_adjoint_bdd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MB

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `Work.MB.slotExact_orth_ae` — the sector pairing identity at the weak mode hypotheses

The strong pairing identity `Work.BoseBoxFock.slotExact_orth_gen` needs the modes `e l` to be
`Continuous` with `HasCompactSupport` and the *first* state to be continuous with compact support.
Those regularity hypotheses are unsatisfiable at the honest modes of the box ↔ model bridge
(`FINDING_continuous_hypotheses_UNSATISFIABLE.md`: the condensate mode is a.e. the box indicator,
which has no continuous representative), so the bridge has to run the whole slot calculus on the
weak bundle

* `hmeas : ∀ l, Measurable (e l)`,
* `hbdE  : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C` (everywhere bounded),
* `hsupp : ∀ l, support (e l) ⊆ boxL ℓ` (supported in the corpus box),

with states that are only measurable, everywhere bounded and supported in the `n`-particle box
`boxPow n ℓ`.  This module proves the weak twin of the pairing identity.

The proof follows the strong one, with `L¹`-integrability supplied by *finite measure of the box*
instead of compact support:

* `integral_star_sum_mul_weak`, `integral_mul_sum_weak` — the finite-sum/integral interchanges, in
  the form needed here (the factor carrying the support is the one that vanishes outside
  `boxPow n ℓ`, so `Work.MB.integrable_of_bdd_of_support` applies);
* `sx_exact_adjoint_bdd` — weak self-adjointness of the sector `slotExact e S`, obtained by
  expanding it as the finite combination `∑_{T ⊇ S} (-1)^{|T|−|S|} slotProj e T` and applying the
  weak self-adjointness `Work.MB.slotProj_adjoint_bdd` of each slot projection;
* the composition law `Work.MB.slotExact_comp_ae` (already available) closes the argument exactly
  as `slotExact_comp` does in the strong case.
-/

/-! ## 0. Support preservation for the weak slot calculus

The sector `slotExact e S Ψ` of a state vanishing outside the box `boxPow n ℓ` vanishes outside
`boxPow n ℓ` as well.  This is what replaces compact support in the strong chain: the product of
two box-supported bounded measurable functions is integrable on the box, of finite measure
(`Work.MB.integrable_of_bdd_of_support`). -/

/-- The slot projection of a state vanishing off `boxPow n ℓ` vanishes off `boxPow n ℓ`: either
one of the projected slots `i ∈ T` lies outside the box, and then the whole `PV`-factor dies
(`PV_eq_zero_of_fst` + the box support of the modes), or a slot `i ∉ T` outside the box is left
untouched by `updateFinset`, so `Ψ` of it vanishes. -/
private theorem slotProj_eq_zero_of_notMem_boxPow {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : Finset (Fin n)) {Φ : (Fin n → E3) → ℂ}
    (hΦsupp : Function.support Φ ⊆ boxPow n ℓ) {x : Fin n → E3}
    (hx : x ∉ boxPow n ℓ) :
    Work.BoseBoxFock.slotProj e T Φ x = 0 := by
  have hbot : ∃ j : Fin n, x j ∉ Work.BoseK15.corpusBox.boxL ℓ := by
    simpa [mem_boxPow_iff] using hx
  obtain ⟨j, hj⟩ := hbot
  have hzero : (fun z : (↥T → E3) =>
      (∏ i : ↥T, Work.BoseBoxFock.PV e (x i.1) (z i)) *
        Φ (fun i => if h : i ∈ T then z ⟨i,h⟩ else x i)) = 0 := by
    funext z
    rw [Pi.zero_apply]
    by_cases hjT : j ∈ T
    · rw [Finset.prod_eq_zero (Finset.mem_univ (⟨j, hjT⟩ : ↥T))]
      · exact zero_mul _
      · exact Work.BoseBoxFock.PV_eq_zero_of_fst e (fun l => by
          by_contra hne
          exact hj (hsupp l (Function.mem_support.mpr hne)))
    · rw [show Φ (fun i => if h : i ∈ T then z ⟨i,h⟩ else x i) = 0 from ?_, mul_zero]
      by_contra hne
      have hmem : (fun i => if h : i ∈ T then z ⟨i,h⟩ else x i) ∈ Function.support Φ :=
        Function.mem_support.mpr hne
      have h2 := hΦsupp hmem
      rw [mem_boxPow_iff] at h2
      have h2j := h2 j
      simp only [dif_neg hjT] at h2j
      exact hj h2j
  have hval : Work.BoseBoxFock.slotProj e T Φ x
      = ∫ z : (↥T → E3), (∏ i : ↥T, Work.BoseBoxFock.PV e (x i.1) (z i)) *
          Φ (fun i => if h : i ∈ T then z ⟨i,h⟩ else x i) := rfl
  rw [hval, hzero]
  exact MeasureTheory.integral_zero _ _

private theorem slotProj_support_boxPow {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : Finset (Fin n)) {Φ : (Fin n → E3) → ℂ}
    (hΦsupp : Function.support Φ ⊆ boxPow n ℓ) :
    Function.support (Work.BoseBoxFock.slotProj e T Φ) ⊆ boxPow n ℓ := by
  intro x hx
  by_contra hxbox
  exact Function.mem_support.mp hx
    (slotProj_eq_zero_of_notMem_boxPow hsupp T hΦsupp hxbox)

private theorem slotExact_support_boxPow {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {Φ : (Fin n → E3) → ℂ}
    (hΦsupp : Function.support Φ ⊆ boxPow n ℓ) :
    Function.support (Work.BoseBoxFock.slotExact e S Φ) ⊆ boxPow n ℓ := by
  intro x hx
  by_contra hxbox
  have hne := Function.mem_support.mp hx
  have hval : Work.BoseBoxFock.slotExact e S Φ x
      = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
          (-1 : ℂ) ^ (T.card - S.card) • Work.BoseBoxFock.slotProj e T Φ x := by
    simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply]
  rw [hval] at hne
  refine hne (Finset.sum_eq_zero fun T _ => ?_)
  rw [show Work.BoseBoxFock.slotProj e T Φ x = 0 from
    slotProj_eq_zero_of_notMem_boxPow hsupp T hΦsupp hxbox]
  simp

/-! ## 1. The finite-sum/integral interchanges at the weak hypotheses -/

/-- **`∫ star (∑ G i) * Ψ = ∑ ∫ star (G i) * Ψ`** for bounded measurable `G i`, with the *second*
factor `Ψ` measurable, bounded and supported in the box `boxPow n ℓ`.

The finite measure of `boxPow n ℓ` (`Work.MB.volume_boxPow_lt_top`) replaces the compact support of
the strong version `Work.BoseBoxFock.integral_star_sum_mul`: every summand is measurable and
bounded, and vanishes outside `boxPow n ℓ` together with `Ψ`. -/
theorem integral_star_sum_mul_weak {ι : Type*} [DecidableEq ι] {n : ℕ} {ℓ : ℝ}
    (s : Finset ι) (G : ι → (Fin n → E3) → ℂ) (Ψ : (Fin n → E3) → ℂ)
    (hGm : ∀ i, Measurable (G i)) (hGb : ∀ i, ∃ C, ∀ x, ‖G i x‖ ≤ C)
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C)
    (hΨsupp : Function.support Ψ ⊆ boxPow n ℓ) :
    ∫ x, star (∑ i ∈ s, G i x) * Ψ x
      = ∑ i ∈ s, ∫ x, star (G i x) * Ψ x := by
  have hpt : ∀ x, star (∑ i ∈ s, G i x) * Ψ x = ∑ i ∈ s, star (G i x) * Ψ x := by
    intro x
    rw [star_sum, Finset.sum_mul]
  rw [show (∫ x, star (∑ i ∈ s, G i x) * Ψ x)
      = ∫ x, ∑ i ∈ s, star (G i x) * Ψ x from
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finsetSum (f := fun i x => star (G i x) * Ψ x)]
  intro i _
  obtain ⟨Ci, hCi⟩ := hGb i
  obtain ⟨CΨ, hCΨ⟩ := hΨb
  refine integrable_of_bdd_of_support (measurableSet_boxPow n ℓ) (volume_boxPow_lt_top n ℓ)
    ((continuous_star.measurable.comp (hGm i)).mul hΨm).aestronglyMeasurable
    (C := max Ci 0 * max CΨ 0) ?_ ?_
  · intro x
    rw [norm_mul, norm_star]
    exact mul_le_mul ((hCi x).trans (le_max_left _ _)) ((hCΨ x).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · intro x hx
    rw [Function.notMem_support.mp (fun hmem => hx (hΨsupp hmem)), mul_zero]

/-- **`∫ star Θ * (∑ G i) = ∑ ∫ star Θ * G i`** for bounded measurable `G i`, with the *first*
factor `Θ` measurable, bounded and supported in the box `boxPow n ℓ` (the weak twin of
`Work.BoseBoxFock.integral_mul_sum`). -/
theorem integral_star_mul_sum_weak {ι : Type*} [DecidableEq ι] {n : ℕ} {ℓ : ℝ}
    (s : Finset ι) (G : ι → (Fin n → E3) → ℂ) (Θ : (Fin n → E3) → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ boxPow n ℓ)
    (hGm : ∀ i, Measurable (G i)) (hGb : ∀ i, ∃ C, ∀ x, ‖G i x‖ ≤ C) :
    ∫ x, star (Θ x) * (∑ i ∈ s, G i x) = ∑ i ∈ s, ∫ x, star (Θ x) * G i x := by
  have hpt : ∀ x, star (Θ x) * (∑ i ∈ s, G i x) = ∑ i ∈ s, star (Θ x) * G i x := by
    intro x
    rw [Finset.mul_sum]
  rw [show (∫ x, star (Θ x) * (∑ i ∈ s, G i x)) = ∫ x, ∑ i ∈ s, star (Θ x) * G i x from
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finsetSum (f := fun i x => star (Θ x) * G i x)]
  intro i _
  obtain ⟨Ci, hCi⟩ := hGb i
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  refine integrable_of_bdd_of_support (measurableSet_boxPow n ℓ) (volume_boxPow_lt_top n ℓ)
    ((continuous_star.measurable.comp hΘm).mul (hGm i)).aestronglyMeasurable
    (C := max CΘ 0 * max Ci 0) ?_ ?_
  · intro x
    rw [norm_mul, norm_star]
    exact mul_le_mul ((hCΘ x).trans (le_max_left _ _)) ((hCi x).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · intro x hx
    rw [Function.notMem_support.mp (fun hmem => hx (hΘsupp hmem))]
    simp

/-! ## 2. Weak self-adjointness of the sectors -/

/-- **Self-adjointness of the sector `slotExact e S` at the weak mode hypotheses.**

Both states are measurable, everywhere bounded and supported in the box `boxPow n ℓ`; the modes are
only measurable, everywhere bounded and supported in `boxL ℓ`.  Mirror of the strong
`Work.BoseBoxFock.slotExact_adjoint_meas`, with `integral_star_sum_mul_weak`/`integral_mul_sum_weak`
in place of the compactly supported interchanges and the weak self-adjointness
`Work.MB.slotProj_adjoint_bdd` of the slot projections in place of `slotProj_adjoint_meas`. -/
theorem sx_exact_adjoint_bdd {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {Φ Ψ : (Fin n → E3) → ℂ}
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (hΦsupp : Function.support Φ ⊆ boxPow n ℓ)
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C)
    (hΨsupp : Function.support Ψ ⊆ boxPow n ℓ) :
    (∫ x, star (Work.BoseBoxFock.slotExact e S Φ x) * Ψ x)
      = ∫ x, star (Φ x) * Work.BoseBoxFock.slotExact e S Ψ x := by
  classical
  set sS : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T) with hsS
  set cP : Finset (Fin n) → ℂ := fun T => (-1 : ℂ) ^ (T.card - S.card) with hcP
  have hcPstar : ∀ T : Finset (Fin n), star (cP T) = cP T := by
    intro T
    rw [hcP, Complex.star_def, map_pow]
    simp
  have hE : ∀ (Θ : (Fin n → E3) → ℂ) (x : Fin n → E3),
      Work.BoseBoxFock.slotExact e S Θ x
        = ∑ T ∈ sS, cP T * Work.BoseBoxFock.slotProj e T Θ x := by
    intro Θ x
    simp only [Work.BoseBoxFock.slotExact, hsS, hcP, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
  have hGm : ∀ T : Finset (Fin n),
      Measurable (fun x => cP T * Work.BoseBoxFock.slotProj e T Φ x) := fun T =>
    ((slotProj_mb_weak hmeas hbdE hsupp T hΦm hΦb).1).const_mul (cP T)
  have hGb : ∀ T : Finset (Fin n),
      ∃ C, ∀ x, ‖cP T * Work.BoseBoxFock.slotProj e T Φ x‖ ≤ C := by
    intro T
    obtain ⟨C, hC⟩ := (slotProj_mb_weak hmeas hbdE hsupp T hΦm hΦb).2
    exact ⟨‖cP T‖ * max C 0, fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((hC x).trans (le_max_left _ _)) (norm_nonneg _)⟩
  have hQm : ∀ T : Finset (Fin n),
      Measurable (fun x => cP T * Work.BoseBoxFock.slotProj e T Ψ x) := fun T =>
    ((slotProj_mb_weak hmeas hbdE hsupp T hΨm hΨb).1).const_mul (cP T)
  have hQb : ∀ T : Finset (Fin n),
      ∃ C, ∀ x, ‖cP T * Work.BoseBoxFock.slotProj e T Ψ x‖ ≤ C := by
    intro T
    obtain ⟨C, hC⟩ := (slotProj_mb_weak hmeas hbdE hsupp T hΨm hΨb).2
    exact ⟨‖cP T‖ * max C 0, fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((hC x).trans (le_max_left _ _)) (norm_nonneg _)⟩
  -- step 1: expand the sector and pull the finite sum out of the integral
  have h1 : (∫ x, star (Work.BoseBoxFock.slotExact e S Φ x) * Ψ x)
      = ∑ T ∈ sS, cP T * ∫ x, star (Work.BoseBoxFock.slotProj e T Φ x) * Ψ x := by
    have hpt : ∀ x, star (Work.BoseBoxFock.slotExact e S Φ x) * Ψ x
        = star (∑ T ∈ sS, cP T * Work.BoseBoxFock.slotProj e T Φ x) * Ψ x :=
      fun x => by rw [hE Φ x]
    rw [show (∫ x, star (Work.BoseBoxFock.slotExact e S Φ x) * Ψ x)
        = ∫ x, star (∑ T ∈ sS, cP T * Work.BoseBoxFock.slotProj e T Φ x) * Ψ x from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_star_sum_mul_weak (s := sS)
      (G := fun T x => cP T * Work.BoseBoxFock.slotProj e T Φ x) (Ψ := Ψ)
      hGm hGb hΨm hΨb hΨsupp]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [show (fun x => star (cP T * Work.BoseBoxFock.slotProj e T Φ x) * Ψ x)
        = fun x => cP T * (star (Work.BoseBoxFock.slotProj e T Φ x) * Ψ x) from by
      funext x
      rw [star_mul, hcPstar T]
      ring]
    rw [integral_const_mul]
  -- step 2: self-adjointness of each slot projection
  have h2 : ∑ T ∈ sS, cP T * ∫ x, star (Work.BoseBoxFock.slotProj e T Φ x) * Ψ x
      = ∑ T ∈ sS, ∫ x, star (Φ x) * (cP T * Work.BoseBoxFock.slotProj e T Ψ x) := by
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [slotProj_adjoint_bdd hmeas hbdE hsupp T Φ Ψ hΦm hΦb hΦsupp hΨm hΨb hΨsupp]
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  -- step 3: fold the sum back into the sector
  have h3 : ∑ T ∈ sS, ∫ x, star (Φ x) * (cP T * Work.BoseBoxFock.slotProj e T Ψ x)
      = ∫ x, star (Φ x) * Work.BoseBoxFock.slotExact e S Ψ x := by
    have hstep := integral_star_mul_sum_weak (s := sS)
      (G := fun T x => cP T * Work.BoseBoxFock.slotProj e T Ψ x)
      (Θ := Φ) hΦm hΦb hΦsupp hQm hQb
    rw [← hstep]
    have hpt : ∀ x, star (Φ x) * (∑ T ∈ sS, cP T * Work.BoseBoxFock.slotProj e T Ψ x)
        = star (Φ x) * Work.BoseBoxFock.slotExact e S Ψ x :=
      fun x => by rw [hE Ψ x]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [h1, h2, h3]

/-! ## 3. The pairing identity -/

theorem slotExact_orth_ae {m n : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (S S' : Finset (Fin n)) (Φ Ψ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (hΦsupp : Function.support Φ ⊆ Work.MB.boxPow n ℓ)
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C)
    (hΨsupp : Function.support Ψ ⊆ Work.MB.boxPow n ℓ) :
    ∫ x, star (Work.BoseBoxFock.slotExact e S Φ x)
        * Work.BoseBoxFock.slotExact e S' Ψ x
      = if S = S' then ∫ x, star (Φ x) * Work.BoseBoxFock.slotExact e S Ψ x else 0 := by
  classical
  obtain ⟨hQm, hQb⟩ := Work.MB.sx_exact_mb_weak hmeas hbdE hsupp S' hΨm hΨb
  have hQsupp' : Function.support (Work.BoseBoxFock.slotExact e S' Ψ) ⊆ boxPow n ℓ :=
    slotExact_support_boxPow hsupp S' hΨsupp
  -- self-adjointness of `slotExact e S` against the sector `slotExact e S' Ψ`
  have hA : (∫ x, star (Work.BoseBoxFock.slotExact e S Φ x)
        * Work.BoseBoxFock.slotExact e S' Ψ x)
      = ∫ x, star (Φ x)
          * Work.BoseBoxFock.slotExact e S (Work.BoseBoxFock.slotExact e S' Ψ) x :=
    sx_exact_adjoint_bdd hmeas hbdE hsupp S hΦm hΦb hΦsupp hQm hQb hQsupp'
  have hcomp := slotExact_comp_ae hmeas hbdE hsupp horth S S' Ψ hΨm hΨb
  rw [hA]
  by_cases h : S = S'
  · rw [if_pos h]
    have hfun : (fun x : Fin n → E3 => star (Φ x)
          * Work.BoseBoxFock.slotExact e S (Work.BoseBoxFock.slotExact e S' Ψ) x)
        = fun x : Fin n → E3 => star (Φ x) * Work.BoseBoxFock.slotExact e S Ψ x := by
      funext x
      simp only [congrFun hcomp x, if_pos h]
    rw [hfun]
  · rw [if_neg h]
    have hfun : (fun x : Fin n → E3 => star (Φ x)
          * Work.BoseBoxFock.slotExact e S (Work.BoseBoxFock.slotExact e S' Ψ) x)
        = fun x : Fin n → E3 => star (Φ x) * (0 : ℂ) := by
      funext x
      rw [congrFun hcomp x, if_neg h]
      simp
    rw [hfun]
    simp

end Work.MB
