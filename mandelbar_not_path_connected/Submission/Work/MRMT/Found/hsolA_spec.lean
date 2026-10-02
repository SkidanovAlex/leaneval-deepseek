import Mathlib
import Submission.Work.MRMT.Found.Defs

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

/-! ## The `L²` Neumann series for `hsol`

`hsol μ hm h1 hLp` is `Ring.inverse (1 - M_μ ∘ S) (toLp μ)`, where `M_μ` is the
multiplication operator of `mulL2 μ hm h1` and `S` is the Beurling transform on `L²(ℂ)`.

We prove the three structural properties of that element:

* it solves the Ahlfors–Bers equation `h = μ (1 + S h)` a.e.;
* its norm is bounded by `(1 - ‖μ‖_∞)⁻¹ ‖μ‖₂`, via the Neumann series `∑ T^n`;
* it vanishes a.e. where `μ` does (a consequence of the first point).
-/

/-- If `‖μ‖ ≤ k` a.e., then the multiplication operator `mulL2 μ hm h1` maps `L²` into
`L²` with constant `k`: the a.e. description of `mulL2` determines its action on the
classes of `L²`, hence its norms. -/
private lemma mulL2_apply_norm_le {μ : ℂ → ℂ} (hm : AEStronglyMeasurable μ (volume : Measure ℂ))
    (h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1) {k : ℝ}
    (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k) (g : Lp ℂ 2 (volume : Measure ℂ)) :
    ‖mulL2 μ hm h1 g‖ ≤ k * ‖g‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul (c := k) ?_
  filter_upwards [mulL2_apply_ae μ hm h1 g, hb] with z hz hkz
  rw [hz, norm_mul]
  exact mul_le_mul_of_nonneg_right hkz (norm_nonneg _)

/-- The three structural facts about `hsol μ hm h1 hLp`. -/
private theorem hsol_spec_aux {μ : ℂ → ℂ} (hm : AEStronglyMeasurable μ (volume : Measure ℂ))
    (h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1) (hLp : MemLp μ 2 (volume : Measure ℂ))
    {k : ℝ} (hk : k < 1) (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k) :
    (∀ᵐ z ∂(volume : Measure ℂ),
      ((hsol μ hm h1 hLp : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z =
        μ z * (1 + ((beurlingL2 (hsol μ hm h1 hLp) :
          Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z)) ∧
    ‖hsol μ hm h1 hLp‖ ≤ (1 - k)⁻¹ * ‖hLp.toLp μ‖ ∧
    (∀ᵐ z ∂(volume : Measure ℂ), z ∉ Function.support μ →
      ((hsol μ hm h1 hLp : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z = 0) := by
  by_cases hk0 : 0 ≤ k
  · -- Neumann series `(1 - T)⁻¹ = ∑' n, T^n`, with `T = M_μ ∘ S` and `‖T‖ ≤ k < 1`.
    set T : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
      (mulL2 μ hm h1).comp beurlingL2 with hTdef
    have hTbound : ∀ g, ‖T g‖ ≤ k * ‖g‖ := by
      intro g
      have h := mulL2_apply_norm_le hm h1 hb (beurlingL2 g)
      rw [hTdef]
      simp only [ContinuousLinearMap.comp_apply]
      rwa [norm_beurlingL2] at h
    have hTop : ‖T‖ ≤ k := ContinuousLinearMap.opNorm_le_bound T hk0 hTbound
    have hTlt : ‖T‖ < 1 := lt_of_le_of_lt hTop hk
    have hdef : hsol μ hm h1 hLp = Ring.inverse (1 - T) (hLp.toLp μ) := by
      rw [hTdef]
      rfl
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
    have hsol_eq : hsol μ hm h1 hLp = (∑' n : ℕ, T ^ n) (hLp.toLp μ) := by
      rw [hdef, hinv]
    have hsolv : (1 - T) (hsol μ hm h1 hLp) = hLp.toLp μ := by
      rw [hsol_eq, ← mul_apply_eq_comp, mul_neg_geom_series T hTlt]
      rfl
    have hsplit : hsol μ hm h1 hLp = hLp.toLp μ + T (hsol μ hm h1 hLp) := by
      have h := hsolv
      rw [sub_apply, one_apply_eq_self] at h
      exact sub_eq_iff_eq_add.mp h
    have hsplit2 : hsol μ hm h1 hLp
        = hLp.toLp μ + mulL2 μ hm h1 (beurlingL2 (hsol μ hm h1 hLp)) := by
      nth_rewrite 1 [hsplit]
      rw [hTdef]
      rfl
    have hpoint : ((hsol μ hm h1 hLp : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
        =ᵐ[(volume : Measure ℂ)]
        fun z => (hLp.toLp μ : ℂ → ℂ) z +
          ((mulL2 μ hm h1 (beurlingL2 (hsol μ hm h1 hLp)) :
            Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z := by
      nth_rewrite 1 [hsplit2]
      exact Lp.coeFn_add (E := ℂ) _ _
    have hpt : ∀ᵐ z ∂(volume : Measure ℂ),
        ((hsol μ hm h1 hLp : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z =
        μ z * (1 + ((beurlingL2 (hsol μ hm h1 hLp) :
          Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z) := by
      filter_upwards [hpoint, mulL2_apply_ae μ hm h1 (beurlingL2 (hsol μ hm h1 hLp)),
        MemLp.coeFn_toLp hLp] with z hz1 hz2 hz3
      rw [hz1, hz2, hz3]
      ring
    refine ⟨hpt, ?_, ?_⟩
    · rw [hsol_eq]
      calc ‖(∑' n : ℕ, T ^ n) (hLp.toLp μ)‖
          ≤ ‖(∑' n : ℕ, T ^ n)‖ * ‖hLp.toLp μ‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (1 - k)⁻¹ * ‖hLp.toLp μ‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            rw [← hinv]
            exact hnorm
    · filter_upwards [hpt] with z hz hzs
      rw [hz]
      have hz0 : μ z = 0 := by
        by_contra hne
        exact hzs (Function.mem_support.mpr hne)
      rw [hz0, zero_mul]
  · -- `k < 0` forces `μ = 0` a.e., hence `hsol = 0`.
    have hk0' : k < 0 := not_le.mp hk0
    have hMy : mulL2 μ hm h1 (hLp.toLp μ) = 0 := by
      have hle : ‖mulL2 μ hm h1 (hLp.toLp μ)‖ ≤ 0 := by
        refine (mulL2_apply_norm_le hm h1 hb _).trans ?_
        exact mul_nonpos_of_nonpos_of_nonneg hk0'.le (norm_nonneg _)
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    have hμ0 : μ =ᵐ[(volume : Measure ℂ)] 0 := by
      have hy1 : ((mulL2 μ hm h1 (hLp.toLp μ) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
          =ᵐ[(volume : Measure ℂ)] 0 := by
        rw [hMy]
        exact Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)
      filter_upwards [hy1, mulL2_apply_ae μ hm h1 (hLp.toLp μ), MemLp.coeFn_toLp hLp]
        with z hz1 hz2 hz3
      have hzz : μ z * μ z = 0 := by
        calc μ z * μ z = μ z * ((hLp.toLp μ : ℂ → ℂ) z) := by rw [hz3]
          _ = ((mulL2 μ hm h1 (hLp.toLp μ) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z :=
                hz2.symm
          _ = 0 := hz1
      exact (mul_self_eq_zero).mp hzz
    have hy0 : hLp.toLp μ = 0 := by
      rw [Lp.ext_iff]
      filter_upwards [MemLp.coeFn_toLp hLp, hμ0, Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)]
        with z hz1 hz2 hz3
      rw [hz1, hz2, hz3]
    have hzero : hsol μ hm h1 hLp = 0 := by
      unfold hsol
      rw [hy0]
      exact map_zero _
    have hzero' : ((hsol μ hm h1 hLp : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
        =ᵐ[(volume : Measure ℂ)] 0 := by
      rw [hzero]
      exact Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)
    have hshift : ((beurlingL2 (hsol μ hm h1 hLp) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
        =ᵐ[(volume : Measure ℂ)] 0 := by
      rw [hzero, map_zero]
      exact Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [hzero', hμ0, hshift] with z hz1 hz2 hz3
      rw [hz1, hz3, hz2]
      simp
    · rw [hzero, norm_zero, hy0, norm_zero, mul_zero]
    · filter_upwards [hzero'] with z hz1 _
      exact hz1

theorem hsolA_spec {μ : ℂ → ℂ} (hμ : Admissible μ)
    (hLp : MeasureTheory.MemLp μ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    {k : ℝ} (hk : k < 1)
    (hb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k) :
    (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      ((hsolA μ hμ hLp : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z =
        μ z * (1 + ((beurlingL2 (hsolA μ hμ hLp) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z)) ∧
    ‖hsolA μ hμ hLp‖ ≤ (1 - k)⁻¹ * ‖hLp.toLp μ‖ ∧
    (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), z ∉ Function.support μ →
      ((hsolA μ hμ hLp : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z = 0) := by
  unfold hsolA
  exact hsol_spec_aux hμ.meas _ hLp hk hb

end Work.MRMT.Found
