import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.ScatKernelChosen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A rotation-invariant `L¹_loc` function has an a.e. radial representative

The main statement `radial_rep_of_rotation_invariant` is the standard
"a.e.-rotation-invariant functions are a.e. radial" fact, in the form needed by
the scattering analysis: given `f` fixed (a.e.) by every orthogonal
transformation of `ℝ³`, locally integrable, and supported in the open ball of
radius `R`, there is an entirely *radial* function `g` with `f =ᵐ g`,
`g ∈ L¹_loc` and `tsupport g ⊆ ball 0 R`.

The construction is by *radialisation with a radial approximate identity*:
`H j x` is the average of `f` over the closed ball of radius `1/(j+1)` around
`x`.  Each `H j` is invariant under all orthogonal transformations (change of
variables plus `f ∘ A =ᵐ f`), and by the Lebesgue differentiation theorem
`H j x → f x` for a.e. `x`.  Hence `G := limsup_j H j` is invariant under all
orthogonal transformations, and `G =ᵐ f`.  Finally one truncates `G` to a
ball of radius `ρ < R` (which exists because `tsupport f` is a compact subset
of `ball 0 R`), which is still radial and still agrees with `f` a.e. while
having support inside `ball 0 R`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology

namespace Work.SmallBoxA0

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Any two vectors of `ℝ³` with the same norm are related by an orthogonal
transformation: reflection in the line spanned by `x - y` (followed by
negation) sends `x` to `y` when `‖x‖ = ‖y‖`.  The case `x = y` is the
identity. -/
lemma exists_linearIsometryEquiv_of_norm_eq {x y : ℝ³} (h : ‖x‖ = ‖y‖) :
    ∃ A : ℝ³ ≃ₗᵢ[ℝ] ℝ³, A x = y := by
  rcases eq_or_ne x y with rfl | hxy
  · exact ⟨LinearIsometryEquiv.refl ℝ ℝ³, rfl⟩
  · refine ⟨(Submodule.reflection (ℝ ∙ (x - y))).trans (LinearIsometryEquiv.neg ℝ), ?_⟩
    have hnorm : (‖x - y‖ : ℝ) ≠ 0 := by
      rw [norm_ne_zero_iff]; exact sub_ne_zero.mpr hxy
    have hrefl : (Submodule.reflection (ℝ ∙ (x - y))) x = -y := by
      rw [Submodule.reflection_singleton_apply]
      have hinner : 2 * inner ℝ (x - y) x = ‖x - y‖ ^ 2 := by
        have hA : inner ℝ (x - y) x = ‖x‖ ^ 2 - inner ℝ y x := by
          rw [inner_sub_left, real_inner_self_eq_norm_sq]
        have hB : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 := norm_sub_sq_real x y
        have hsym : inner ℝ y x = inner ℝ x y := real_inner_comm x y
        rw [hA, hB, hsym, h]
        ring
      have hcoef : inner ℝ (x - y) x / (↑‖x - y‖ : ℝ) ^ 2 = (1 : ℝ) / 2 := by
        have hcc : (↑‖x - y‖ : ℝ) ^ 2 = ‖x - y‖ ^ 2 := by ring
        rw [hcc, div_eq_iff (pow_ne_zero 2 hnorm)]
        linarith
      erw [hcoef]
      rw [← smul_assoc]
      norm_num
    simp [hrefl]

/-- If the closed support of `f` is contained in the open ball of radius `R`,
then `f` vanishes outside a *closed* ball of some radius `ρ < R`. -/
lemma exists_radius_of_tsupport_subset_ball {f : ℝ³ → ℝ} {R : ℝ}
    (hsupp : tsupport f ⊆ Metric.ball (0 : ℝ³) R) :
    ∃ ρ : ℝ, ρ < R ∧ ∀ x : ℝ³, ρ < ‖x‖ → f x = 0 := by
  by_cases hT : tsupport f = ∅
  · refine ⟨R - 1, by linarith, ?_⟩
    intro x _
    have hx : x ∉ Function.support f := by
      intro hxs
      have : x ∈ tsupport f := subset_closure hxs
      rw [hT] at this
      exact this
    exact Function.notMem_support.mp hx
  · have hne : (tsupport f).Nonempty := Set.nonempty_iff_ne_empty.mpr hT
    have hbdd : Bornology.IsBounded (tsupport f) :=
      (Metric.isBounded_ball (x := (0 : ℝ³)) (r := R)).subset hsupp
    have hcomp : IsCompact (tsupport f) :=
      isCompact_iff_isClosed_bounded.mpr ⟨isClosed_tsupport f, hbdd⟩
    obtain ⟨y, hyT, hymax⟩ := hcomp.exists_isMaxOn hne continuous_norm.continuousOn
    refine ⟨‖y‖, ?_, ?_⟩
    · have hy : y ∈ Metric.ball (0 : ℝ³) R := hsupp hyT
      simpa [Metric.mem_ball, dist_zero_right] using hy
    · intro x hx
      have hxT : x ∉ Function.support f := by
        intro hxs
        have hxm : x ∈ tsupport f := subset_closure hxs
        have hle : ‖x‖ ≤ ‖y‖ := by simpa using hymax hxm
        linarith
      exact Function.notMem_support.mp hxT

/-- The ball average of an a.e.-rotation-invariant function is *exactly*
invariant under orthogonal transformations. -/
lemma setAverage_closedBall_linearIsometryEquiv {f : ℝ³ → ℝ}
    (hrot : ∀ A : ℝ³ ≃ₗᵢ[ℝ] ℝ³, f =ᵐ[MeasureTheory.volume] fun x => f (A x))
    (A : ℝ³ ≃ₗᵢ[ℝ] ℝ³) (x : ℝ³) {r : ℝ} :
    (⨍ y in Metric.closedBall (A x) r, f y) = (⨍ y in Metric.closedBall x r, f y) := by
  have hvol : (volume : Measure ℝ³).real (Metric.closedBall (A x) r)
      = (volume : Measure ℝ³).real (Metric.closedBall x r) := by
    rw [Measure.real, Measure.real, InnerProductSpace.volume_closedBall (A x) r,
      InnerProductSpace.volume_closedBall x r]
  have hint : (∫ y in Metric.closedBall (A x) r, f y)
      = ∫ y in Metric.closedBall x r, f y := by
    rw [← LinearIsometryEquiv.image_closedBall A x r]
    rw [MeasureTheory.MeasurePreserving.setIntegral_image_emb A.measurePreserving
      (A.toMeasurableEquiv.measurableEmbedding) f (Metric.closedBall x r)]
    refine MeasureTheory.setIntegral_congr_ae measurableSet_closedBall ?_
    filter_upwards [(hrot A).symm] with z hz
    exact fun _ => hz
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, hvol, hint]

/-- Lebesgue differentiation along the sequence of balls centred at `x` with
radii `1/(j+1)`: the averages converge to `f x` for a.e. `x`. -/
lemma tendsto_setAverage_closedBall_one_div {f : ℝ³ → ℝ}
    (hli : MeasureTheory.LocallyIntegrable f) :
    ∀ᵐ x : ℝ³, Filter.Tendsto
      (fun j : ℕ => ⨍ y in Metric.closedBall x (1 / ((j : ℝ) + 1)), f y)
      Filter.atTop (nhds (f x)) := by
  filter_upwards
    [IsUnifLocDoublingMeasure.ae_tendsto_average (volume : Measure ℝ³) hli (0 : ℝ)]
    with x hx
  have hδ : Filter.Tendsto (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) Filter.atTop
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ),
      Filter.Eventually.of_forall (fun j => by
        simp only [Set.mem_Ioi]; positivity)⟩
  have hmem : ∀ᶠ j : ℕ in Filter.atTop,
      x ∈ Metric.closedBall x ((0 : ℝ) * (1 / ((j : ℝ) + 1))) := by
    filter_upwards with j
    simp
  exact hx (fun _ : ℕ => x) (fun j => 1 / ((j : ℝ) + 1)) hδ hmem

lemma radial_rep_of_rotation_invariant {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hrot : ∀ A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3), f =ᵐ[MeasureTheory.volume] fun x => f (A x)) (hli : MeasureTheory.LocallyIntegrable f) {R : ℝ} (hsupp : tsupport f ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) : ∃ g : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial g ∧ MeasureTheory.LocallyIntegrable g ∧ f =ᵐ[MeasureTheory.volume] g ∧ tsupport g ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R := by
  obtain ⟨ρ, hρR, hρ⟩ := exists_radius_of_tsupport_subset_ball hsupp
  set H : ℕ → ℝ³ → ℝ :=
    fun j x => ⨍ y in Metric.closedBall x (1 / ((j : ℝ) + 1)), f y with hH
  set G : ℝ³ → ℝ := fun x => limsup (fun j => H j x) Filter.atTop with hG
  have hGinv : ∀ (A : ℝ³ ≃ₗᵢ[ℝ] ℝ³) (u : ℝ³), G (A u) = G u := by
    intro A u
    simp only [hG, hH]
    exact limsup_congr (Filter.Eventually.of_forall
      (fun j => setAverage_closedBall_linearIsometryEquiv (f := f) hrot A u
        (r := 1 / ((j : ℝ) + 1))))
  have hGrad : BoseGases.IsRadial G := by
    intro x y hxy
    obtain ⟨A, hA⟩ := exists_linearIsometryEquiv_of_norm_eq hxy
    rw [← hA]
    exact (hGinv A x).symm
  have hGae : G =ᵐ[MeasureTheory.volume] f := by
    filter_upwards [tendsto_setAverage_closedBall_one_div (f := f) hli] with x hx
    simp only [hG, hH]
    exact hx.limsup_eq
  have hfeq : f =ᵐ[MeasureTheory.volume]
      (fun x : ℝ³ => if ‖x‖ ≤ ρ then G x else 0) := by
    filter_upwards [hGae] with x hx
    by_cases h : ‖x‖ ≤ ρ
    · rw [if_pos h]; exact hx.symm
    · rw [if_neg h]; exact hρ x (lt_of_not_ge h)
  refine ⟨fun x : ℝ³ => if ‖x‖ ≤ ρ then G x else 0, ?_, ?_, hfeq, ?_⟩
  · intro x y hxy
    change (if ‖x‖ ≤ ρ then G x else 0) = (if ‖y‖ ≤ ρ then G y else 0)
    rw [hxy]
    by_cases h : ‖y‖ ≤ ρ
    · simp only [h, if_true]; exact hGrad x y hxy
    · simp only [h, if_false]
  · exact hli.congr hfeq
  · have hsub : Function.support (fun x : ℝ³ => if ‖x‖ ≤ ρ then G x else 0)
        ⊆ Metric.closedBall (0 : ℝ³) ρ := by
      intro x hx
      by_contra hxnot
      have hgt : ¬ ‖x‖ ≤ ρ := by
        intro h
        exact hxnot (by simpa [Metric.mem_closedBall, dist_zero_right] using h)
      change (if ‖x‖ ≤ ρ then G x else 0) ≠ 0 at hx
      rw [if_neg hgt] at hx
      exact hx rfl
    calc tsupport (fun x : ℝ³ => if ‖x‖ ≤ ρ then G x else 0)
        = closure (Function.support (fun x : ℝ³ => if ‖x‖ ≤ ρ then G x else 0)) := rfl
      _ ⊆ closure (Metric.closedBall (0 : ℝ³) ρ) := closure_mono hsub
      _ = Metric.closedBall (0 : ℝ³) ρ := isClosed_closedBall.closure_eq
      _ ⊆ Metric.ball (0 : ℝ³) R := by
          intro z hz
          simp only [Metric.mem_closedBall, dist_zero_right] at hz
          simp only [Metric.mem_ball, dist_zero_right]
          linarith

end Work.SmallBoxA0
