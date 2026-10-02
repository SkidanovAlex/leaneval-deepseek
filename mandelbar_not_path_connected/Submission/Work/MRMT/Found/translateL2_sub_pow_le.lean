/-
# A polynomial-in-`t` bound for `‖(τ_t - 1)^n q‖` for the fixed point of `q = m + μ S q`

Auxiliary definitions and lemmas for the main theorem `translateL2_sub_pow_le`.

* `finiteDiff g t N` — the `N`-th finite difference of `g` in the direction `t`.
* `mulCLM ν hν C hb` — multiplication by `ν` on `L²(ℂ)` as a bounded operator,
  with norm bound `C`; it is built from `mulL2` (which handles the unit bound) by scaling.
-/
import Mathlib
import Submission.Work.MRMT.Found.PrincipalAux
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.beurlingL2_translateL2
import Submission.Work.MRMT.Found.pascal_smul_sum
import Submission.Work.MRMT.Found.translateL2_sub_pow_apply_ae
import Submission.Work.MRMT.Found.sum_alt_binom
import Submission.Work.MRMT.Found.fdiff_sup_le
import Submission.Work.MRMT.Found.fdiff_lp_le

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

/-! ## Finite differences -/

/-- The `N`-th finite difference of `g` in the direction `t`:
`finiteDiff g t N z = ∑_{j ≤ N} (-1)^{N-j} (N choose j) g (z - j t)`. -/
private noncomputable def finiteDiff (g : ℂ → ℂ) (t : ℂ) (N : ℕ) : ℂ → ℂ :=
  fun z => ∑ j ∈ Finset.range (N + 1), (-1 : ℂ) ^ (N - j) * (N.choose j : ℂ) * g (z - (j : ℂ) * t)

private theorem finiteDiff_zero (g : ℂ → ℂ) (t : ℂ) : finiteDiff g t 0 = g := by
  funext z
  simp [finiteDiff]

/-- `Δ^{M+1} = Δ ∘ Δ^M`: the finite difference of order `M+1` is the difference of the
`M`-th finite difference with itself, shifted. -/
private theorem finiteDiff_succ' (g : ℂ → ℂ) (t : ℂ) (M : ℕ) :
    finiteDiff g t (M + 1) = fun w => finiteDiff g t M (w - t) - finiteDiff g t M w := by
  funext w
  simp only [finiteDiff]
  rw [← Finset.sum_sub_distrib]
  rw [sum_alt_binom (fun j => g (w - (j : ℂ) * t)) M]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show (w - ((j + 1 : ℕ) : ℂ) * t) = (w - t - (j : ℂ) * t) by push_cast; ring]
  ring

/-- Shifting the argument of `g` shifts the finite difference. -/
private theorem finiteDiff_shift (g : ℂ → ℂ) (t s : ℂ) (N : ℕ) :
    finiteDiff (fun z => g (z - s)) t N = fun z => finiteDiff g t N (z - s) := by
  funext z
  simp only [finiteDiff]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show (z - s - (j : ℂ) * t) = (z - (j : ℂ) * t - s) by ring]

/-- `finiteDiff μ t M` is continuous when `μ` is. -/
private theorem finiteDiff_continuous {μ : ℂ → ℂ} (hμc : Continuous μ) (M : ℕ) (t : ℂ) :
    Continuous (finiteDiff μ t M) := by
  unfold finiteDiff
  exact continuous_finset_sum _ (fun j _ => continuous_const.mul
    (hμc.comp (continuous_id.sub continuous_const)))

/-- Any translate of a finite difference of a continuous `μ` is a.e. strongly measurable. -/
private theorem finiteDiff_aestronglyMeasurable {μ : ℂ → ℂ} (hμc : Continuous μ) (M : ℕ) (t c : ℂ) :
    AEStronglyMeasurable (fun z : ℂ => finiteDiff μ t M (z - c)) (volume : Measure ℂ) :=
  ((finiteDiff_continuous hμc M t).comp (continuous_id.sub continuous_const)).aestronglyMeasurable

/-- A doubled translate of a finite difference is a.e. strongly measurable. -/
private theorem finiteDiff_aestronglyMeasurable_sub {μ : ℂ → ℂ} (hμc : Continuous μ) (M : ℕ) (t c : ℂ) :
    AEStronglyMeasurable (fun z : ℂ => finiteDiff μ t M (z - t - c)) (volume : Measure ℂ) :=
  (((finiteDiff_continuous hμc M t).comp
    ((continuous_id.sub continuous_const).sub continuous_const))).aestronglyMeasurable

/-! ## Multiplication operators on `L²(ℂ)` -/

private theorem exists_mul_left_L2_gen (ν : ℂ → ℂ) (hν : AEStronglyMeasurable ν (volume : Measure ℂ))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν z‖ ≤ C) :
    ∃ T : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ),
      ‖T‖ ≤ C ∧ ∀ f : Lp ℂ 2 (volume : Measure ℂ),
        ((T f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[(volume : Measure ℂ)]
          fun z => ν z * ((f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z := by
  rcases eq_or_lt_of_le hC with hzero | hpos
  · subst hzero
    refine ⟨0, by simp, fun f => ?_⟩
    filter_upwards [hb] with z hz
    have hz0 : ν z = 0 := norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))
    simp [hz0]
  · set ν' : ℂ → ℂ := fun z => (C : ℂ)⁻¹ * ν z with hν'def
    have hν'asm : AEStronglyMeasurable ν' (volume : Measure ℂ) := hν.const_mul _
    have hnormC : ‖(C : ℂ)‖ = C := by
      simpa [abs_of_nonneg hC] using RCLike.norm_ofReal (K := ℂ) C
    have hν'1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν' z‖ ≤ 1 := by
      filter_upwards [hb] with z hz
      rw [hν'def]
      simp only
      rw [norm_mul, norm_inv, hnormC]
      rw [inv_mul_le_iff₀ hpos]
      simpa using hz
    have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
    refine ⟨(C : ℂ) • mulL2 ν' hν'asm hν'1, ?_, ?_⟩
    · calc ‖(C : ℂ) • mulL2 ν' hν'asm hν'1‖
          ≤ ‖(C : ℂ)‖ * ‖mulL2 ν' hν'asm hν'1‖ :=
            norm_smul_le (C : ℂ) (mulL2 ν' hν'asm hν'1)
        _ = C * ‖mulL2 ν' hν'asm hν'1‖ := by rw [hnormC]
        _ ≤ C * 1 := by
              gcongr
              exact mulL2_norm_le ν' hν'asm hν'1
        _ = C := by ring
    · intro f
      rw [ContinuousLinearMap.smul_apply]
      filter_upwards [Lp.coeFn_smul (C : ℂ) (mulL2 ν' hν'asm hν'1 f),
        mulL2_apply_ae ν' hν'asm hν'1 f] with z h1 h2
      rw [h1]
      simp only [Pi.smul_apply, smul_eq_mul, hν'def]
      rw [h2]
      have hCinv : (C : ℂ) * (C : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hCne
      calc (C : ℂ) * ((C : ℂ)⁻¹ * ν z * ((f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z)
          = ((C : ℂ) * (C : ℂ)⁻¹) * (ν z * ((f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z) := by
            ring
        _ = ν z * ((f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z := by rw [hCinv, one_mul]

/-- Multiplication by an a.e. bounded measurable function on `L²(ℂ)`, as a bounded operator
with norm at most `C`. -/
private noncomputable def mulCLM (ν : ℂ → ℂ) (hν : AEStronglyMeasurable ν (volume : Measure ℂ))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν z‖ ≤ C) :
    Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  Classical.choose (exists_mul_left_L2_gen ν hν C hC hb)

private theorem mulCLM_norm_le (ν : ℂ → ℂ) (hν : AEStronglyMeasurable ν (volume : Measure ℂ))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν z‖ ≤ C) :
    ‖mulCLM ν hν C hC hb‖ ≤ C :=
  (Classical.choose_spec (exists_mul_left_L2_gen ν hν C hC hb)).1

private theorem mulCLM_apply_ae (ν : ℂ → ℂ) (hν : AEStronglyMeasurable ν (volume : Measure ℂ))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν z‖ ≤ C)
    (f : Lp ℂ 2 (volume : Measure ℂ)) :
    ((mulCLM ν hν C hC hb f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[(volume : Measure ℂ)]
      fun z => ν z * ((f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z :=
  (Classical.choose_spec (exists_mul_left_L2_gen ν hν C hC hb)).2 f

/-- Two continuous linear operators on `L²(ℂ)` which agree a.e. on every vector are equal. -/
private theorem CLM_ext_of_ae {S T : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ)}
    (h : ∀ f : Lp ℂ 2 (volume : Measure ℂ),
      ((S f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[(volume : Measure ℂ)]
        ((T f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)) : S = T :=
  ContinuousLinearMap.ext (fun f => Lp.ext (h f))

/-- The a.e. formula for the translation operator. -/
private theorem translateL2_coeFn (t : ℂ) (f : Lp ℂ 2 (volume : Measure ℂ)) :
    ((translateL2 t f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[(volume : Measure ℂ)]
      fun w => ((f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) (w - t) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right (volume : Measure ℂ) t)

/-- Multiplication operators with a.e. equal multipliers agree. -/
private theorem mulCLM_congr {ν ν' : ℂ → ℂ} (h : ν =ᵐ[(volume : Measure ℂ)] ν')
    (hν : AEStronglyMeasurable ν (volume : Measure ℂ))
    (hν' : AEStronglyMeasurable ν' (volume : Measure ℂ))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν z‖ ≤ C)
    (C' : ℝ) (hC' : 0 ≤ C') (hb' : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν' z‖ ≤ C') :
    mulCLM ν hν C hC hb = mulCLM ν' hν' C' hC' hb' := by
  refine CLM_ext_of_ae (fun f => ?_)
  filter_upwards [mulCLM_apply_ae ν hν C hC hb f, mulCLM_apply_ae ν' hν' C' hC' hb' f, h]
    with z h1 h2 h3
  rw [h1, h2, h3]

/-- Difference of two multiplication operators. -/
private theorem mulCLM_sub (ν₁ ν₂ : ℂ → ℂ) (h₁ : AEStronglyMeasurable ν₁ (volume : Measure ℂ))
    (h₂ : AEStronglyMeasurable ν₂ (volume : Measure ℂ))
    (C₁ : ℝ) (hC₁ : 0 ≤ C₁) (hb₁ : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν₁ z‖ ≤ C₁)
    (C₂ : ℝ) (hC₂ : 0 ≤ C₂) (hb₂ : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν₂ z‖ ≤ C₂)
    (hd : AEStronglyMeasurable (ν₁ - ν₂) (volume : Measure ℂ))
    (Cd : ℝ) (hCd : 0 ≤ Cd) (hbd : ∀ᵐ z ∂(volume : Measure ℂ), ‖(ν₁ - ν₂) z‖ ≤ Cd) :
    mulCLM ν₁ h₁ C₁ hC₁ hb₁ - mulCLM ν₂ h₂ C₂ hC₂ hb₂
      = mulCLM (ν₁ - ν₂) hd Cd hCd hbd := by
  refine CLM_ext_of_ae (fun f => ?_)
  rw [ContinuousLinearMap.sub_apply]
  filter_upwards [mulCLM_apply_ae ν₁ h₁ C₁ hC₁ hb₁ f, mulCLM_apply_ae ν₂ h₂ C₂ hC₂ hb₂ f,
    Lp.coeFn_sub (mulCLM ν₁ h₁ C₁ hC₁ hb₁ f) (mulCLM ν₂ h₂ C₂ hC₂ hb₂ f),
    mulCLM_apply_ae (ν₁ - ν₂) hd Cd hCd hbd f] with z h1 h2 h3 h4
  rw [h3]
  simp only [Pi.sub_apply]
  rw [h1, h2, h4]
  simp only [Pi.sub_apply, sub_mul]

/-- Translation interacts with multiplication operators by shifting the multiplier. -/
private theorem translateL2_mulCLM (t : ℂ) (ν : ℂ → ℂ) (hν : AEStronglyMeasurable ν (volume : Measure ℂ))
    (hνt : AEStronglyMeasurable (fun z => ν (z - t)) (volume : Measure ℂ))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν z‖ ≤ C)
    (hbt : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν (z - t)‖ ≤ C)
    (f : Lp ℂ 2 (volume : Measure ℂ)) :
    translateL2 t (mulCLM ν hν C hC hb f)
      = mulCLM (fun z => ν (z - t)) hνt C hC hbt (translateL2 t f) := by
  refine Lp.ext ?_
  have hmul := mulCLM_apply_ae ν hν C hC hb f
  have hmul' : (fun z => ((mulCLM ν hν C hC hb f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) (z - t))
      =ᵐ[(volume : Measure ℂ)]
      (fun z => ν (z - t) * ((f : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) (z - t)) :=
    (measurePreserving_sub_right (volume : Measure ℂ) t).quasiMeasurePreserving.ae_eq_comp hmul
  filter_upwards [translateL2_coeFn t (mulCLM ν hν C hC hb f), hmul',
    mulCLM_apply_ae (fun z => ν (z - t)) hνt C hC hbt (translateL2 t f),
    translateL2_coeFn t f] with z h1 h2 h3 h4
  rw [h1, h3, h2, h4]

/-- The difference operator applied to `M_ν ∘ S`. -/
private theorem D_mulCLM (t : ℂ) (ν : ℂ → ℂ) (hν : AEStronglyMeasurable ν (volume : Measure ℂ))
    (hνt : AEStronglyMeasurable (fun z => ν (z - t)) (volume : Measure ℂ))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν z‖ ≤ C)
    (hbt : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν (z - t)‖ ≤ C)
    (X : Lp ℂ 2 (volume : Measure ℂ)) :
    (translateL2 t - 1) (mulCLM ν hν C hC hb (beurlingL2 X))
      = mulCLM (fun z => ν (z - t) - ν z) (hνt.sub hν) (2 * C) (by linarith)
          (by
            filter_upwards [hbt, hb] with z h1 h2
            calc ‖ν (z - t) - ν z‖ ≤ ‖ν (z - t)‖ + ‖ν z‖ := norm_sub_le _ _
              _ ≤ C + C := add_le_add h1 h2
              _ = 2 * C := by ring)
          (beurlingL2 X)
      + mulCLM (fun z => ν (z - t)) hνt C hC hbt (beurlingL2 ((translateL2 t - 1) X)) := by
  have hX : translateL2 t X = X + (translateL2 t - 1) X := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    abel
  have hsub : mulCLM (fun z => ν (z - t)) hνt C hC hbt - mulCLM ν hν C hC hb
      = mulCLM (fun z => ν (z - t) - ν z) (hνt.sub hν) (2 * C) (by linarith)
          (by
            filter_upwards [hbt, hb] with z h1 h2
            calc ‖ν (z - t) - ν z‖ ≤ ‖ν (z - t)‖ + ‖ν z‖ := norm_sub_le _ _
              _ ≤ C + C := add_le_add h1 h2
              _ = 2 * C := by ring) :=
    mulCLM_sub (fun z => ν (z - t)) ν hνt hν C hC hbt C hC hb (hνt.sub hν) (2 * C)
      (by linarith)
      (by
        filter_upwards [hbt, hb] with z h1 h2
        calc ‖ν (z - t) - ν z‖ ≤ ‖ν (z - t)‖ + ‖ν z‖ := norm_sub_le _ _
          _ ≤ C + C := add_le_add h1 h2
          _ = 2 * C := by ring)
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    translateL2_mulCLM t ν hν hνt C hC hb hbt (beurlingL2 X), ← beurlingL2_translateL2 t X, hX]
  simp only [map_add]
  have hval := congrArg (fun F : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) =>
    F (beurlingL2 X)) hsub
  rw [ContinuousLinearMap.sub_apply] at hval
  rw [← hval]
  abel

/-! ## The target theorem -/

theorem translateL2_sub_pow_le {μ m q : ℂ → ℂ}
    (hμ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ) (hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m)
    (hsμ : HasCompactSupport μ) (hsm : HasCompactSupport m)
    {k : ℝ} (hk : k < 1) (hb : ∀ z : ℂ, ‖μ z‖ ≤ k)
    (hq : MeasureTheory.MemLp q 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (heq : q =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℂ)] fun z => m z + μ z *
      ((Work.MRMT.beurlingL2 (hq.toLp q) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℂ,
      ‖((Work.MRMT.Found.translateL2 t - 1) ^ n) (hq.toLp q)‖ ≤ C * ‖t‖ ^ n := by
  have hk0 : 0 ≤ k := le_trans (norm_nonneg (μ 0)) (hb 0)
  have hmLp : MemLp m 2 (volume : Measure ℂ) := hm.continuous.memLp_of_hasCompactSupport hsm
  have hμ_asm : AEStronglyMeasurable μ (volume : Measure ℂ) := hμ.continuous.aestronglyMeasurable
  have hμ_bd : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k := Eventually.of_forall hb
  -- the fixed point equation, in `L²`
  have hQ : hq.toLp q = MemLp.toLp m hmLp
      + mulCLM μ hμ_asm k hk0 hμ_bd (beurlingL2 (hq.toLp q)) := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp hq, Lp.coeFn_add (MemLp.toLp m hmLp)
        (mulCLM μ hμ_asm k hk0 hμ_bd (beurlingL2 (hq.toLp q))), MemLp.coeFn_toLp hmLp,
      mulCLM_apply_ae μ hμ_asm k hk0 hμ_bd (beurlingL2 (hq.toLp q)), heq] with z h1 h2 h3 h4 h5
    rw [h1, h2]
    simp only [Pi.add_apply]
    rw [h3, h4]
    exact h5
  -- finite-difference bounds
  have hμsup : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t z : ℂ, ‖finiteDiff μ t M z‖ ≤ C * ‖t‖ ^ M :=
    fun M => fdiff_sup_le hμ hsμ M
  have hmlp : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℂ,
      eLpNorm (finiteDiff m t N) 2 (volume : Measure ℂ) ≤ ENNReal.ofReal (C * ‖t‖ ^ N) := by
    intro N
    exact fdiff_lp_le hm hsm N
  let Bc : ℕ → ℝ := fun M => Classical.choose (hμsup M)
  have hBc_nonneg : ∀ M, 0 ≤ Bc M := fun M => (Classical.choose_spec (hμsup M)).1
  have hBc_bound : ∀ M t z, ‖finiteDiff μ t M z‖ ≤ Bc M * ‖t‖ ^ M :=
    fun M t z => (Classical.choose_spec (hμsup M)).2 t z
  let Ac : ℕ → ℝ := fun N => Classical.choose (hmlp N)
  have hAc_nonneg : ∀ N, 0 ≤ Ac N := fun N => (Classical.choose_spec (hmlp N)).1
  have hAc_bound : ∀ (N : ℕ) (t : ℂ), eLpNorm (finiteDiff m t N) 2 (volume : Measure ℂ)
      ≤ ENNReal.ofReal (Ac N * ‖t‖ ^ N) := fun N t => (Classical.choose_spec (hmlp N)).2 t
  -- the source term
  have hsrc : ∀ (N : ℕ) (t : ℂ),
      ‖((translateL2 t - 1) ^ N) (MemLp.toLp m hmLp)‖ ≤ Ac N * ‖t‖ ^ N := by
    intro N t
    have hshift : ∀ j : ℕ,
        (fun z : ℂ => ((MemLp.toLp m hmLp : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) (z - (j : ℂ) * t))
          =ᵐ[(volume : Measure ℂ)] (fun z : ℂ => m (z - (j : ℂ) * t)) := by
      intro j
      have hcmp := (measurePreserving_sub_right (volume : Measure ℂ) ((j : ℂ) * t)).quasiMeasurePreserving
        |>.ae_eq_comp (MemLp.coeFn_toLp hmLp)
      simpa [Function.comp_def] using hcmp
    have hall : ∀ᵐ z ∂(volume : Measure ℂ), ∀ j ∈ Finset.range (N + 1),
        ((MemLp.toLp m hmLp : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) (z - (j : ℂ) * t)
          = m (z - (j : ℂ) * t) := by
      rw [Finset.eventually_all]
      intro j _
      exact hshift j
    have hae : ((((translateL2 t - 1) ^ N) (MemLp.toLp m hmLp) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
        =ᵐ[(volume : Measure ℂ)] finiteDiff m t N := by
      filter_upwards [translateL2_sub_pow_apply_ae N t (MemLp.toLp m hmLp), hall] with z h1 h2
      rw [h1]
      simp only [finiteDiff]
      exact Finset.sum_congr rfl (fun j hj => by rw [h2 j hj])
    have hnorm : ‖((translateL2 t - 1) ^ N) (MemLp.toLp m hmLp)‖
        = (eLpNorm (finiteDiff m t N) 2 (volume : Measure ℂ)).toReal := by
      rw [Lp.norm_def]
      congr 1
      exact eLpNorm_congr_ae hae
    rw [hnorm]
    calc (eLpNorm (finiteDiff m t N) 2 (volume : Measure ℂ)).toReal
        ≤ (ENNReal.ofReal (Ac N * ‖t‖ ^ N)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hAc_bound N t)
      _ = Ac N * ‖t‖ ^ N :=
          ENNReal.toReal_ofReal (mul_nonneg (hAc_nonneg N) (pow_nonneg (norm_nonneg t) N))
  -- the coefficient operators
  have hfd_asm : ∀ (M : ℕ) (t c : ℂ),
      AEStronglyMeasurable (fun z : ℂ => finiteDiff μ t M (z - c)) (volume : Measure ℂ) :=
    fun M t c => finiteDiff_aestronglyMeasurable hμ.continuous M t c
  have hfd_asm' : ∀ (M : ℕ) (t c : ℂ),
      AEStronglyMeasurable (fun z : ℂ => finiteDiff μ t M (z - t - c)) (volume : Measure ℂ) :=
    fun M t c => finiteDiff_aestronglyMeasurable_sub hμ.continuous M t c
  let coeff : ℂ → ℕ → ℕ → (Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ)) :=
    fun t M j => mulCLM (fun z : ℂ => finiteDiff μ t M (z - (j : ℂ) * t)) (hfd_asm M t ((j : ℂ) * t))
      (Bc M * ‖t‖ ^ M) (mul_nonneg (hBc_nonneg M) (pow_nonneg (norm_nonneg t) M))
      (by filter_upwards with z; exact hBc_bound M t (z - (j : ℂ) * t))
  have hcoeff : ∀ (t : ℂ) (M j : ℕ), ‖coeff t M j‖ ≤ Bc M * ‖t‖ ^ M := by
    intro t M j
    dsimp only [coeff]
    exact mulCLM_norm_le _ _ _ _ _
  have hDcoeff : ∀ (t : ℂ) (M j : ℕ) (X : Lp ℂ 2 (volume : Measure ℂ)),
      (translateL2 t - 1) (coeff t M j (beurlingL2 X))
        = coeff t (M + 1) j (beurlingL2 X)
          + coeff t M (j + 1) (beurlingL2 ((translateL2 t - 1) X)) := by
    intro t M j X
    have hD := D_mulCLM t (fun z : ℂ => finiteDiff μ t M (z - (j : ℂ) * t)) (hfd_asm M t ((j : ℂ) * t))
      (hfd_asm' M t ((j : ℂ) * t)) (Bc M * ‖t‖ ^ M)
      (mul_nonneg (hBc_nonneg M) (pow_nonneg (norm_nonneg t) M))
      (by filter_upwards with z; exact hBc_bound M t (z - (j : ℂ) * t))
      (by filter_upwards with z; exact hBc_bound M t (z - t - (j : ℂ) * t)) X
    rw [hD]
    congr 1
    · congr 1
      dsimp only [coeff]
      refine mulCLM_congr ?_ _ _ _ _ _ _ _ _
      filter_upwards with z
      have hfs := congrFun (finiteDiff_succ' μ t M) (z - (j : ℂ) * t)
      rw [hfs, show z - (j : ℂ) * t - t = z - t - (j : ℂ) * t by ring]
    · congr 1
      dsimp only [coeff]
      refine mulCLM_congr ?_ _ _ _ _ _ _ _ _
      filter_upwards with z
      rw [show z - t - (j : ℂ) * t = z - ((j + 1 : ℕ) : ℂ) * t by push_cast; ring]
  -- the recursion identity
  have rec_id : ∀ N : ℕ, ∀ t : ℂ,
      ((translateL2 t - 1) ^ N) (hq.toLp q)
        = ((translateL2 t - 1) ^ N) (MemLp.toLp m hmLp)
          + ∑ j ∈ Finset.range (N + 1), (N.choose j : ℂ) •
              (coeff t (N - j) j (beurlingL2 (((translateL2 t - 1) ^ j) (hq.toLp q)))) := by
    intro N
    induction N with
    | zero =>
      intro t
      have h00 : coeff t 0 0 = mulCLM μ hμ_asm k hk0 hμ_bd := by
        dsimp only [coeff]
        refine mulCLM_congr ?_ _ _ _ _ _ _ _ _
        filter_upwards with z
        rw [finiteDiff_zero]
        simp
      rw [pow_zero, ContinuousLinearMap.one_apply, Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, Nat.choose_self, Nat.cast_one, one_smul, Nat.zero_sub, h00]
      exact hQ
    | succ N ih =>
      intro t
      have hpowsucc : ∀ (j : ℕ) (Y : Lp ℂ 2 (volume : Measure ℂ)),
          ((translateL2 t - 1) ^ (j + 1)) Y = (translateL2 t - 1) (((translateL2 t - 1) ^ j) Y) := by
        intro j Y
        rw [pow_succ']
        rfl
      conv_lhs => rw [hpowsucc N (hq.toLp q)]
      conv_lhs => rw [ih t]
      conv_lhs => rw [map_add]
      conv_lhs => simp only [map_sum, map_smul]
      rw [hpowsucc N (MemLp.toLp m hmLp)]
      simp only [hDcoeff]
      rw [← pascal_smul_sum
        (fun i => coeff t (N + 1 - i) i (beurlingL2 (((translateL2 t - 1) ^ i) (hq.toLp q)))) N]
      congr 1
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [show N - j + 1 = N + 1 - j by omega, show N + 1 - (j + 1) = N - j by omega,
        hpowsucc j (hq.toLp q)]
  -- the inductive norm bound
  have key : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℂ,
      ‖((translateL2 t - 1) ^ N) (hq.toLp q)‖ ≤ C * ‖t‖ ^ N := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      rcases Nat.eq_zero_or_pos N with hNz | hNpos
      · subst hNz
        refine ⟨‖hq.toLp q‖, norm_nonneg _, fun t => ?_⟩
        rw [pow_zero, ContinuousLinearMap.one_apply]
        simp
      · have hCj : ∀ j, j < N → ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℂ,
            ‖((translateL2 t - 1) ^ j) (hq.toLp q)‖ ≤ C * ‖t‖ ^ j := fun j hj => ih j hj
        choose Cj hCj' using hCj
        let Cj' : ℕ → ℝ := fun j => if h : j < N then Cj j h else 0
        have hCj'_nonneg : ∀ j, 0 ≤ Cj' j := by
          intro j
          by_cases h : j < N
          · have hval : Cj' j = Cj j h := by dsimp only [Cj']; rw [dif_pos h]
            rw [hval]
            exact (hCj' j h).1
          · have hval : Cj' j = 0 := by dsimp only [Cj']; rw [dif_neg h]
            rw [hval]
        have hCj'_bound : ∀ (j : ℕ), j < N → ∀ t : ℂ,
            ‖((translateL2 t - 1) ^ j) (hq.toLp q)‖ ≤ Cj' j * ‖t‖ ^ j := by
          intro j hj t
          have hval : Cj' j = Cj j hj := by dsimp only [Cj']; rw [dif_pos hj]
          rw [hval]
          exact (hCj' j hj).2 t
        refine ⟨(1 - k)⁻¹ * (Ac N + ∑ j ∈ Finset.range N, (N.choose j : ℝ) * Bc (N - j) * Cj' j),
          ?_, ?_⟩
        · refine mul_nonneg (le_of_lt (inv_pos.mpr (by linarith))) (add_nonneg (hAc_nonneg N) ?_)
          exact Finset.sum_nonneg (fun j _ =>
            mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hBc_nonneg _)) (hCj'_nonneg j))
        · intro t
          have hterm : ∀ j, j ∈ Finset.range N →
              ‖(N.choose j : ℂ) •
                  (coeff t (N - j) j (beurlingL2 (((translateL2 t - 1) ^ j) (hq.toLp q))))‖
                ≤ ((N.choose j : ℝ) * Bc (N - j) * Cj' j) * ‖t‖ ^ N := by
            intro j hj
            have hjN : j < N := Finset.mem_range.mp hj
            have h1 : ‖coeff t (N - j) j (beurlingL2 (((translateL2 t - 1) ^ j) (hq.toLp q)))‖
                ≤ (Bc (N - j) * ‖t‖ ^ (N - j)) * ‖(((translateL2 t - 1) ^ j) (hq.toLp q))‖ := by
              calc ‖coeff t (N - j) j (beurlingL2 (((translateL2 t - 1) ^ j) (hq.toLp q)))‖
                  ≤ ‖coeff t (N - j) j‖
                      * ‖beurlingL2 (((translateL2 t - 1) ^ j) (hq.toLp q))‖ :=
                    ContinuousLinearMap.le_opNorm _ _
                _ = ‖coeff t (N - j) j‖ * ‖(((translateL2 t - 1) ^ j) (hq.toLp q))‖ := by
                    rw [norm_beurlingL2]
                _ ≤ (Bc (N - j) * ‖t‖ ^ (N - j)) * ‖(((translateL2 t - 1) ^ j) (hq.toLp q))‖ := by
                    gcongr
                    exact hcoeff t (N - j) j
            have hp : ‖t‖ ^ (N - j) * ‖t‖ ^ j = ‖t‖ ^ N := by
              rw [← pow_add, Nat.sub_add_cancel (le_of_lt hjN)]
            calc ‖(N.choose j : ℂ) •
                    (coeff t (N - j) j (beurlingL2 (((translateL2 t - 1) ^ j) (hq.toLp q))))‖
                = (N.choose j : ℝ) *
                    ‖coeff t (N - j) j (beurlingL2 (((translateL2 t - 1) ^ j) (hq.toLp q)))‖ := by
                  rw [norm_smul, Complex.norm_natCast]
              _ ≤ (N.choose j : ℝ) * ((Bc (N - j) * ‖t‖ ^ (N - j))
                    * ‖(((translateL2 t - 1) ^ j) (hq.toLp q))‖) :=
                  mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
              _ ≤ (N.choose j : ℝ) * ((Bc (N - j) * ‖t‖ ^ (N - j)) * (Cj' j * ‖t‖ ^ j)) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left (hCj'_bound j hjN t)
                      (mul_nonneg (hBc_nonneg _) (pow_nonneg (norm_nonneg t) _)))
                    (Nat.cast_nonneg _)
              _ = ((N.choose j : ℝ) * Bc (N - j) * Cj' j) * ‖t‖ ^ N := by
                  calc (N.choose j : ℝ) * ((Bc (N - j) * ‖t‖ ^ (N - j)) * (Cj' j * ‖t‖ ^ j))
                      = ((N.choose j : ℝ) * Bc (N - j) * Cj' j) * (‖t‖ ^ (N - j) * ‖t‖ ^ j) := by
                        ring
                    _ = ((N.choose j : ℝ) * Bc (N - j) * Cj' j) * ‖t‖ ^ N := by rw [hp]
          have hsum_bound : ‖∑ j ∈ Finset.range N, (N.choose j : ℂ) •
                (coeff t (N - j) j (beurlingL2 (((translateL2 t - 1) ^ j) (hq.toLp q))))‖
              ≤ (∑ j ∈ Finset.range N, (N.choose j : ℝ) * Bc (N - j) * Cj' j) * ‖t‖ ^ N := by
            calc ‖∑ j ∈ Finset.range N, (N.choose j : ℂ) •
                  (coeff t (N - j) j (beurlingL2 (((translateL2 t - 1) ^ j) (hq.toLp q))))‖
                ≤ ∑ j ∈ Finset.range N, ‖(N.choose j : ℂ) •
                    (coeff t (N - j) j (beurlingL2 (((translateL2 t - 1) ^ j) (hq.toLp q))))‖ :=
                  norm_sum_le _ _
              _ ≤ ∑ j ∈ Finset.range N, ((N.choose j : ℝ) * Bc (N - j) * Cj' j) * ‖t‖ ^ N :=
                  Finset.sum_le_sum hterm
              _ = (∑ j ∈ Finset.range N, (N.choose j : ℝ) * Bc (N - j) * Cj' j) * ‖t‖ ^ N := by
                  rw [Finset.sum_mul]
          have hμ_asm' : AEStronglyMeasurable (fun z : ℂ => μ (z - (N : ℂ) * t)) (volume : Measure ℂ) :=
            ((hμ.continuous.comp (continuous_id.sub continuous_const))).aestronglyMeasurable
          have hbd : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ (z - (N : ℂ) * t)‖ ≤ k := by
            filter_upwards with z
            exact hb (z - (N : ℂ) * t)
          have h0 : coeff t 0 N = mulCLM (fun z : ℂ => μ (z - (N : ℂ) * t))
              hμ_asm' k hk0 hbd := by
            dsimp only [coeff]
            refine mulCLM_congr ?_ _ _ _ _ _ _ _ _
            filter_upwards with z
            simp [finiteDiff_zero]
          have hXN : ‖coeff t 0 N (beurlingL2 (((translateL2 t - 1) ^ N) (hq.toLp q)))‖
              ≤ k * ‖(((translateL2 t - 1) ^ N) (hq.toLp q))‖ := by
            rw [h0]
            calc ‖mulCLM (fun z : ℂ => μ (z - (N : ℂ) * t)) hμ_asm' k hk0 hbd
                    (beurlingL2 (((translateL2 t - 1) ^ N) (hq.toLp q)))‖
                ≤ ‖mulCLM (fun z : ℂ => μ (z - (N : ℂ) * t)) hμ_asm' k hk0 hbd‖
                    * ‖beurlingL2 (((translateL2 t - 1) ^ N) (hq.toLp q))‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ k * ‖beurlingL2 (((translateL2 t - 1) ^ N) (hq.toLp q))‖ := by
                  gcongr
                  exact mulCLM_norm_le _ _ _ _ _
              _ = k * ‖(((translateL2 t - 1) ^ N) (hq.toLp q))‖ := by rw [norm_beurlingL2]
          have hrec := rec_id N t
          rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_smul, Nat.sub_self] at hrec
          have hsplit : ‖(((translateL2 t - 1) ^ N) (hq.toLp q))‖
              ≤ ‖(((translateL2 t - 1) ^ N) (MemLp.toLp m hmLp))‖
                + (∑ j ∈ Finset.range N, (N.choose j : ℝ) * Bc (N - j) * Cj' j) * ‖t‖ ^ N
                + k * ‖(((translateL2 t - 1) ^ N) (hq.toLp q))‖ := by
            conv_lhs => rw [hrec]
            calc ‖(((translateL2 t - 1) ^ N) (MemLp.toLp m hmLp))
                  + ((∑ j ∈ Finset.range N, (N.choose j : ℂ) •
                      (coeff t (N - j) j (beurlingL2 (((translateL2 t - 1) ^ j) (hq.toLp q)))))
                    + coeff t 0 N (beurlingL2 (((translateL2 t - 1) ^ N) (hq.toLp q))))‖
                ≤ ‖(((translateL2 t - 1) ^ N) (MemLp.toLp m hmLp))‖
                  + ‖(∑ j ∈ Finset.range N, (N.choose j : ℂ) •
                      (coeff t (N - j) j (beurlingL2 (((translateL2 t - 1) ^ j) (hq.toLp q)))))
                    + coeff t 0 N (beurlingL2 (((translateL2 t - 1) ^ N) (hq.toLp q)))‖ :=
                  norm_add_le _ _
              _ ≤ ‖(((translateL2 t - 1) ^ N) (MemLp.toLp m hmLp))‖
                  + ((∑ j ∈ Finset.range N, (N.choose j : ℝ) * Bc (N - j) * Cj' j) * ‖t‖ ^ N
                    + k * ‖(((translateL2 t - 1) ^ N) (hq.toLp q))‖) :=
                  add_le_add le_rfl ((norm_add_le _ _).trans (add_le_add hsum_bound hXN))
              _ = ‖(((translateL2 t - 1) ^ N) (MemLp.toLp m hmLp))‖
                    + (∑ j ∈ Finset.range N, (N.choose j : ℝ) * Bc (N - j) * Cj' j) * ‖t‖ ^ N
                    + k * ‖(((translateL2 t - 1) ^ N) (hq.toLp q))‖ := by ring
          have hfin : (1 - k) * ‖(((translateL2 t - 1) ^ N) (hq.toLp q))‖
              ≤ (Ac N + ∑ j ∈ Finset.range N, (N.choose j : ℝ) * Bc (N - j) * Cj' j) * ‖t‖ ^ N := by
            have hsrc' := hsrc N t
            linarith
          have h1k : 0 < 1 - k := by linarith
          have h1 := mul_le_mul_of_nonneg_left hfin (le_of_lt (inv_pos.mpr h1k))
          have h1' : (1 - k)⁻¹ * ((1 - k) * ‖(((translateL2 t - 1) ^ N) (hq.toLp q))‖)
              = ‖(((translateL2 t - 1) ^ N) (hq.toLp q))‖ := by
            rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt h1k), one_mul]
          have h2' : (1 - k)⁻¹
                * ((Ac N + ∑ j ∈ Finset.range N, (N.choose j : ℝ) * Bc (N - j) * Cj' j) * ‖t‖ ^ N)
              = ((1 - k)⁻¹
                  * (Ac N + ∑ j ∈ Finset.range N, (N.choose j : ℝ) * Bc (N - j) * Cj' j))
                * ‖t‖ ^ N := by rw [mul_assoc]
          rw [h1', h2'] at h1
          exact h1
  exact key n

end Work.MRMT.Found
