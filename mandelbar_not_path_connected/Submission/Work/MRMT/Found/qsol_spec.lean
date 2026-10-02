import Mathlib
import Submission.Work.MRMT.Found.PrincipalAux
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.hsolA_spec

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

/-! ## The `L²` Neumann series for `qsol`

`qsol μ m hm = Ring.inverse (1 - M_μ ∘ S) (hm.toLp m)`, where `M_μ` is the multiplication
operator `mulL2Canon μ` and `S` is the Beurling transform on `L²(ℂ)`.

We prove the three structural properties of that element for the *inhomogeneous*
Ahlfors–Bers equation `q = m + μ · S q`:

* it solves the equation a.e.;
* its norm is bounded by `(1 - ‖μ‖_∞)⁻¹ ‖m‖₂`, via the Neumann series `∑ Tⁿ`;
* it vanishes a.e. where both `μ` and `m` do (a consequence of the first point).
-/

/-- If `‖μ‖ ≤ k` a.e., then `mulL2 μ hm h1` maps `L²` into `L²` with constant `k`. -/
private lemma mulL2_apply_norm_le_aux {μ : ℂ → ℂ} (hm : AEStronglyMeasurable μ (volume : Measure ℂ))
    (h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1) {k : ℝ}
    (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k) (g : Lp ℂ 2 (volume : Measure ℂ)) :
    ‖mulL2 μ hm h1 g‖ ≤ k * ‖g‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul (c := k) ?_
  filter_upwards [mulL2_apply_ae μ hm h1 g, hb] with z hz hkz
  rw [hz, norm_mul]
  exact mul_le_mul_of_nonneg_right hkz (norm_nonneg _)

theorem qsol_spec {μ m : ℂ → ℂ} (hμ : Work.MRMT.Found.Admissible μ) {k : ℝ} (hk : k < 1)
    (hb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k)
    (hm : MeasureTheory.MemLp m 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) :
    (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      ((Work.MRMT.Found.qsol μ m hm : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z =
        m z + μ z * ((Work.MRMT.beurlingL2 (Work.MRMT.Found.qsol μ m hm) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z) ∧
    ‖Work.MRMT.Found.qsol μ m hm‖ ≤ (1 - k)⁻¹ * ‖hm.toLp m‖ ∧
    (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      z ∉ Function.support μ → z ∉ Function.support m →
        ((Work.MRMT.Found.qsol μ m hm : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z = 0) := by
  -- `hb` forces `0 ≤ k`: if `k < 0` the a.e. bound would hold on the empty set, i.e. the
  -- whole plane would have measure zero.
  have hk0 : 0 ≤ k := by
    by_contra hcon
    rw [not_le] at hcon
    have hnull : (volume : Measure ℂ) {z : ℂ | ¬ (‖μ z‖ ≤ k)} = 0 :=
      MeasureTheory.ae_iff.mp hb
    have huniv : {z : ℂ | ¬ (‖μ z‖ ≤ k)} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, not_le]
      exact lt_of_lt_of_le hcon (norm_nonneg (μ z))
    rw [huniv] at hnull
    simp at hnull
  have h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1 := by
    filter_upwards [hb] with z hz
    exact le_trans hz hk.le
  have hMeq : mulL2Canon μ = mulL2 μ hμ.meas h1 := mulL2Canon_eq μ hμ.meas h1
  -- The Neumann series `(1 - T)⁻¹ = ∑' n, T ^ n`, with `T = M_μ ∘ S` and `‖T‖ ≤ k < 1`.
  set T : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
    (mulL2 μ hμ.meas h1).comp beurlingL2 with hTdef
  have hTbound : ∀ g, ‖T g‖ ≤ k * ‖g‖ := by
    intro g
    have h := mulL2_apply_norm_le_aux hμ.meas h1 hb (beurlingL2 g)
    rw [hTdef]
    simp only [ContinuousLinearMap.comp_apply]
    rwa [norm_beurlingL2] at h
  have hTop : ‖T‖ ≤ k := ContinuousLinearMap.opNorm_le_bound T hk0 hTbound
  have hTlt : ‖T‖ < 1 := lt_of_le_of_lt hTop hk
  have hqdef : qsol μ m hm = Ring.inverse (1 - T) (hm.toLp m) := by
    unfold qsol
    rw [hMeq, hTdef]
  have hinv : Ring.inverse (1 - T) = ∑' n : ℕ, T ^ n := by
    rw [NormedRing.inverse_one_sub T hTlt]
    rfl
  have hnorm : ‖Ring.inverse (1 - T)‖ ≤ (1 - k)⁻¹ := by
    rw [hinv]
    refine le_trans (tsum_geometric_le_of_norm_lt_one T hTlt) ?_
    have h1' : ‖(1 : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    have h2' : (1 - ‖T‖)⁻¹ ≤ (1 - k)⁻¹ := by
      refine inv_anti₀ ?_ ?_ <;> linarith
    linarith
  have hq_eq : qsol μ m hm = (∑' n : ℕ, T ^ n) (hm.toLp m) := by
    rw [hqdef, hinv]
  have hqv : (1 - T) (qsol μ m hm) = hm.toLp m := by
    rw [hq_eq, ← mul_apply_eq_comp, mul_neg_geom_series T hTlt]
    rfl
  have hsplit : qsol μ m hm = hm.toLp m + T (qsol μ m hm) := by
    have h := hqv
    rw [sub_apply, one_apply_eq_self] at h
    exact sub_eq_iff_eq_add.mp h
  have hsplit2 : qsol μ m hm
      = hm.toLp m + mulL2 μ hμ.meas h1 (beurlingL2 (qsol μ m hm)) := by
    nth_rewrite 1 [hsplit]
    rw [hTdef]
    rfl
  have hpoint : ((qsol μ m hm : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[(volume : Measure ℂ)]
      fun z => (hm.toLp m : ℂ → ℂ) z +
        ((mulL2 μ hμ.meas h1 (beurlingL2 (qsol μ m hm)) :
          Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z := by
    nth_rewrite 1 [hsplit2]
    exact Lp.coeFn_add (E := ℂ) _ _
  have hpt : ∀ᵐ z ∂(volume : Measure ℂ),
      ((qsol μ m hm : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z =
        m z + μ z * ((beurlingL2 (qsol μ m hm) :
          Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z := by
    filter_upwards [hpoint, mulL2_apply_ae μ hμ.meas h1 (beurlingL2 (qsol μ m hm)),
      MemLp.coeFn_toLp hm] with z hz1 hz2 hz3
    rw [hz1, hz2, hz3]
  refine ⟨hpt, ?_, ?_⟩
  · rw [hq_eq]
    calc ‖(∑' n : ℕ, T ^ n) (hm.toLp m)‖
        ≤ ‖(∑' n : ℕ, T ^ n)‖ * ‖hm.toLp m‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 - k)⁻¹ * ‖hm.toLp m‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [← hinv]
          exact hnorm
  · filter_upwards [hpt] with z hz hzsμ hzsm
    rw [hz]
    have hzμ0 : μ z = 0 := by
      by_contra hne
      exact hzsμ (Function.mem_support.mpr hne)
    have hzm0 : m z = 0 := by
      by_contra hne
      exact hzsm (Function.mem_support.mpr hne)
    rw [hzμ0, hzm0, zero_mul, add_zero]

end Work.MRMT.Found
