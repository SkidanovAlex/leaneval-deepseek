import Mathlib
import Submission.Work.BourgainPlan.Maximal.MtaDefs

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-! ## Auxiliary lemmas for the multiplier identity

The block operator `mtaBlkOp P K ε s` is a finite sum of *dyadic projections*
`dyadicProj dyadTilde (deg·k+s) (ε k · dyadicProj dyadPsi (deg·k+s) (D_k g))`.  Each dyadic
projection is the `L²` Fourier multiplier with its symbol (`dyadicProj_dichotomy`, applied in the
"good" branch since an `L¹` input makes every intermediate integrable here), and the multiplier
calculus (`multiplier_mul`, `multiplier_const_smul`, `multiplier_sum`) turns the finite sum of
compositions into the multiplier with the summed symbol. -/

/-- The curve average `curveSigma P N g` of an integrable `g` is integrable.  This is the `p = 1`
instance of `memLp_curveSigma'`. -/
private lemma curveSigma_integrable_aux (P : Polynomial ℤ) (N : ℕ) {g : ℝ → ℂ}
    (hg1 : MeasureTheory.Integrable g) :
    MeasureTheory.Integrable (curveSigma P N g) := by
  refine MeasureTheory.memLp_one_iff_integrable.mp ?_
  have h1 : MemLp g (ENNReal.ofReal (1:ℝ)) (volume : Measure ℝ) := by
    simpa using (MeasureTheory.memLp_one_iff_integrable.mpr hg1 : MemLp g 1 (volume : Measure ℝ))
  have h := (memLp_curveSigma' P N (le_refl (1:ℝ)) h1).1
  simpa using h

/-- **The `s`-th block operator is the multiplier with the `s`-th block symbol.** -/
private lemma mtaBlkOp_multiplier_ae_block (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (s : ℤ)
    {g : ℝ → ℂ} (hg1 : MeasureTheory.Integrable g)
    (hg2 : MeasureTheory.MemLp g 2 MeasureTheory.volume) :
    (fun x : ℝ => mtaBlkOp P K ε s g x) =ᵐ[(volume : Measure ℝ)]
      ((Commons.Analysis.Fourier.BoundaryLayer.multiplier
        (mtaBlkSym P K ε s) (memLp_mtaBlkSym P K ε s)
        (MeasureTheory.MemLp.toLp g hg2)) : ℝ → ℂ) := by
  classical
  obtain ⟨Bψ, hBψ0, hBψ⟩ := dyadPsi_abs_bound
  obtain ⟨Bt, hBt0, hBt⟩ := dyadTilde_abs_bound
  let L : ℕ → ℤ := fun k => (P.natDegree : ℤ) * (k : ℤ) + s
  let mS : ℕ → ℝ → ℂ := fun k ξ => (dyadPsi ((2:ℝ)^(L k) * ξ) : ℂ)
  let mT : ℕ → ℝ → ℂ := fun k ξ => (dyadTilde ((2:ℝ)^(L k) * ξ) : ℂ)
  let mu : ℕ → ℝ → ℂ := fun k => muSym P k
  let H : Lp ℂ 2 (volume : Measure ℝ) := MeasureTheory.MemLp.toLp g hg2
  let G : ℕ → ℝ → ℂ := fun k => fun y => ε k * dyadicProj dyadPsi (L k) (dyadD P k g) y
  -- ## structural facts
  have hψd : HasCompactSupport dyadPsi := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-2:ℝ)) (b := 2)) ?_
    intro ξ hξ
    obtain ⟨h1, h2⟩ := dyadPsi_support hξ
    exact ⟨by linarith [neg_abs_le ξ], by linarith [le_abs_self ξ]⟩
  have htd : HasCompactSupport dyadTilde := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-4:ℝ)) (b := 4)) ?_
    intro ξ hξ
    have hξ' : ¬ (4 ≤ |ξ|) := fun hh4 => hξ (dyadTilde_zero hh4)
    exact ⟨by linarith [neg_abs_le ξ], by linarith [le_abs_self ξ]⟩
  have hψC : HasCompactSupport (fun η : ℝ => (dyadPsi η : ℂ)) :=
    hψd.comp_left (g := fun η : ℝ => (η : ℂ)) (by simp)
  have htC : HasCompactSupport (fun η : ℝ => (dyadTilde η : ℂ)) :=
    htd.comp_left (g := fun η : ℝ => (η : ℂ)) (by simp)
  have hS_cont : ∀ k, Continuous (mS k) := fun k =>
    Complex.continuous_ofReal.comp (continuous_dyadPsi.comp (continuous_const.mul continuous_id))
  have hT_cont : ∀ k, Continuous (mT k) := fun k =>
    Complex.continuous_ofReal.comp
      ((dyadTheta_spec.1.continuous.comp (continuous_id.div_const 2)).comp
        (continuous_const.mul continuous_id))
  have hS_memLp : ∀ k, MemLp (mS k) ⊤ (volume : Measure ℝ) := fun k =>
    memLp_top_of_bound' (hS_cont k).aestronglyMeasurable Bψ (fun ξ => by
      change ‖(dyadPsi ((2:ℝ)^(L k) * ξ) : ℂ)‖ ≤ Bψ
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hBψ _)
  have hT_memLp : ∀ k, MemLp (mT k) ⊤ (volume : Measure ℝ) := fun k =>
    memLp_top_of_bound' (hT_cont k).aestronglyMeasurable Bt (fun ξ => by
      change ‖(dyadTilde ((2:ℝ)^(L k) * ξ) : ℂ)‖ ≤ Bt
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hBt _)
  have hS_supp : ∀ k, HasCompactSupport (mS k) := fun k =>
    hasCompactSupport_comp_mul_left' hψC (zpow_ne_zero (L k) (by norm_num : (2:ℝ) ≠ 0))
  have hT_supp : ∀ k, HasCompactSupport (mT k) := fun k =>
    hasCompactSupport_comp_mul_left' htC (zpow_ne_zero (L k) (by norm_num : (2:ℝ) ≠ 0))
  have hS_int : ∀ k, Integrable (mS k) := fun k =>
    (hS_cont k).integrable_of_hasCompactSupport (hS_supp k)
  have hT_int : ∀ k, Integrable (mT k) := fun k =>
    (hT_cont k).integrable_of_hasCompactSupport (hT_supp k)
  have hMu_memLp : ∀ k, MemLp (mu k) ⊤ (volume : Measure ℝ) := fun k =>
    (memLp_star_polyProfile P (2^k)).sub (memLp_star_polyProfile P (2^(k+1)))
  have hD_memLp : ∀ k, MemLp (dyadD P k g) 2 (volume : Measure ℝ) := fun k =>
    ((curveSigma_eq_multiplier P (2^k) g hg2).2).sub
      ((curveSigma_eq_multiplier P (2^(k+1)) g hg2).2)
  have hD_int : ∀ k, Integrable (dyadD P k g) := fun k =>
    (curveSigma_integrable_aux P (2^k) hg1).sub (curveSigma_integrable_aux P (2^(k+1)) hg1)
  -- ## `G k` is in `L²` and integrable
  have hG_memLp : ∀ k, MemLp (G k) 2 (volume : Measure ℝ) := by
    intro k
    have hd := (dyadicProj_dichotomy (mS k) (hS_int k) (hS_memLp k) (dyadD P k g)
      (hD_memLp k)).2 (hD_int k)
    have hGae : G k =ᵐ[volume]
        (ε k • (Commons.Analysis.Fourier.BoundaryLayer.multiplier (mS k) (hS_memLp k)
          (MemLp.toLp (dyadD P k g) (hD_memLp k))) : ℝ → ℂ) := by
      show (fun y : ℝ => ε k * dyadicProj dyadPsi (L k) (dyadD P k g) y) =ᵐ[volume]
        (fun y : ℝ => ε k * ((Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (mS k) (hS_memLp k) (MemLp.toLp (dyadD P k g) (hD_memLp k)) : ℝ → ℂ) y))
      exact (Filter.EventuallyEq.of_eq
        (rfl : (fun _ : ℝ => ε k) = (fun _ : ℝ => ε k))).mul hd
    exact MemLp.ae_eq hGae.symm ((Lp.memLp _).const_smul (ε k))
  have hG_int : ∀ k, Integrable (G k) := fun k =>
    (integrable_dyadicProj (m := L k) (hD_int k)).const_mul (ε k)
  -- ## the symbol of `D_k` is `mu k`
  have hDmu : ∀ k, MemLp.toLp (dyadD P k g) (hD_memLp k)
      = Commons.Analysis.Fourier.BoundaryLayer.multiplier (mu k) (hMu_memLp k) H := by
    intro k
    obtain ⟨hmA, hAae⟩ := (curveSigma_eq_multiplier P (2^k) g hg2).1
    obtain ⟨hmB, hBae⟩ := (curveSigma_eq_multiplier P (2^(k+1)) g hg2).1
    have hAB : (curveSigma P (2^k) g - curveSigma P (2^(k+1)) g : ℝ → ℂ) =ᵐ[volume]
        ((Commons.Analysis.Fourier.BoundaryLayer.multiplier
            (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^k) ξ)) hmA H)
          - (Commons.Analysis.Fourier.BoundaryLayer.multiplier
            (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)) hmB H) : ℝ → ℂ) :=
      hAae.sub hBae
    have hsub := multiplier_sub_sym (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^k) ξ))
      (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)) hmA hmB (hMu_memLp k) H
    have hAB1 : dyadD P k g =ᵐ[volume]
        (Commons.Analysis.Fourier.BoundaryLayer.multiplier (mu k) (hMu_memLp k) H : ℝ → ℂ) := by
      refine hAB.trans ?_
      refine (Lp.coeFn_sub _ _).symm.trans ?_
      rw [← hsub]
      exact Filter.EventuallyEq.rfl
    apply Lp.ext (p := 2) (μ := (volume : Measure ℝ))
    filter_upwards [MemLp.coeFn_toLp (hD_memLp k), hAB1] with x e1 e2
    rw [e1, e2]
  -- ## the block symbol and the block identity
  let σ : ℕ → ℝ → ℂ := fun k ξ => ε k * (mS k ξ * mu k ξ)
  have hSmu : ∀ k, MemLp (fun ξ : ℝ => mS k ξ * mu k ξ) ⊤ (volume : Measure ℝ) := fun k =>
    (hS_memLp k).mul (hMu_memLp k)
  have hσc : ∀ k, MemLp (fun ξ : ℝ => ε k * (mS k ξ * mu k ξ)) ⊤ (volume : Measure ℝ) :=
    fun k => (hSmu k).const_smul (ε k)
  have hσ : ∀ k, MemLp (σ k) ⊤ (volume : Measure ℝ) := fun k => hσc k
  have hTS : ∀ k, MemLp (fun ξ : ℝ => mT k ξ * σ k ξ) ⊤ (volume : Measure ℝ) := fun k =>
    (hT_memLp k).mul (hσ k)
  have hBlock : ∀ k, (fun x : ℝ => dyadicProj dyadTilde (L k) (G k) x) =ᵐ[volume]
      (Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ k) (hσ k) H : ℝ → ℂ) := by
    intro k
    have hinner := (dyadicProj_dichotomy (mS k) (hS_int k) (hS_memLp k) (dyadD P k g)
      (hD_memLp k)).2 (hD_int k)
    have hGtoLp : MemLp.toLp (G k) (hG_memLp k)
        = ε k • (Commons.Analysis.Fourier.BoundaryLayer.multiplier (mS k) (hS_memLp k)
            (MemLp.toLp (dyadD P k g) (hD_memLp k))) := by
      have hae : G k =ᵐ[volume]
          (ε k • (Commons.Analysis.Fourier.BoundaryLayer.multiplier (mS k) (hS_memLp k)
            (MemLp.toLp (dyadD P k g) (hD_memLp k)) : ℝ → ℂ)) := by
        show (fun y : ℝ => ε k * dyadicProj dyadPsi (L k) (dyadD P k g) y) =ᵐ[volume]
          (fun y : ℝ => ε k * ((Commons.Analysis.Fourier.BoundaryLayer.multiplier
            (mS k) (hS_memLp k) (MemLp.toLp (dyadD P k g) (hD_memLp k)) : ℝ → ℂ) y))
        exact (Filter.EventuallyEq.of_eq
          (rfl : (fun _ : ℝ => ε k) = (fun _ : ℝ => ε k))).mul hinner
      calc MemLp.toLp (G k) (hG_memLp k)
          = MemLp.toLp (ε k • (Commons.Analysis.Fourier.BoundaryLayer.multiplier
                (mS k) (hS_memLp k) (MemLp.toLp (dyadD P k g) (hD_memLp k)) : ℝ → ℂ))
                ((Lp.memLp _).const_smul (ε k)) :=
            MemLp.toLp_congr (hG_memLp k) ((Lp.memLp _).const_smul (ε k)) hae
        _ = ε k • MemLp.toLp (Commons.Analysis.Fourier.BoundaryLayer.multiplier
                (mS k) (hS_memLp k) (MemLp.toLp (dyadD P k g) (hD_memLp k)) : ℝ → ℂ)
                (Lp.memLp _) :=
            MemLp.toLp_const_smul (ε k) (Lp.memLp _)
        _ = ε k • (Commons.Analysis.Fourier.BoundaryLayer.multiplier (mS k) (hS_memLp k)
                (MemLp.toLp (dyadD P k g) (hD_memLp k))) := by rw [Lp.toLp_coeFn]
    have hGchain : MemLp.toLp (G k) (hG_memLp k)
        = Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ k) (hσ k) H := by
      rw [hGtoLp, hDmu k]
      rw [multiplier_mul (mS k) (mu k) (hS_memLp k) (hMu_memLp k) (hSmu k) H]
      rw [← multiplier_const_smul (ε k) (fun ξ : ℝ => mS k ξ * mu k ξ) (hSmu k) (hσc k) H]
    have houter := (dyadicProj_dichotomy (mT k) (hT_int k) (hT_memLp k) (G k)
      (hG_memLp k)).2 (hG_int k)
    have hstep1 : Commons.Analysis.Fourier.BoundaryLayer.multiplier (mT k) (hT_memLp k)
          (MemLp.toLp (G k) (hG_memLp k))
        = Commons.Analysis.Fourier.BoundaryLayer.multiplier (mT k) (hT_memLp k)
          (Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ k) (hσ k) H) := by rw [hGchain]
    have hstep2 : Commons.Analysis.Fourier.BoundaryLayer.multiplier (mT k) (hT_memLp k)
          (Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ k) (hσ k) H)
        = Commons.Analysis.Fourier.BoundaryLayer.multiplier
            (fun ξ : ℝ => mT k ξ * σ k ξ) (hTS k) H :=
      multiplier_mul (mT k) (σ k) (hT_memLp k) (hσ k) (hTS k) H
    have hstep3 : Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (fun ξ : ℝ => mT k ξ * σ k ξ) (hTS k) H
        = Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ k) (hσ k) H := by
      refine multiplier_congr ?_ (hTS k) (hσ k) H
      funext ξ
      show mT k ξ * (ε k * (mS k ξ * mu k ξ)) = ε k * (mS k ξ * mu k ξ)
      rcases eq_or_ne (mS k ξ) 0 with h0 | hne
      · rw [h0]; ring
      · have h1 : mT k ξ = 1 := by
          have hψne : dyadPsi ((2:ℝ)^(L k) * ξ) ≠ 0 := fun h => hne (by
            change (dyadPsi ((2:ℝ)^(L k) * ξ) : ℂ) = 0; rw [h]; simp)
          have habs := (dyadPsi_support hψne).2
          change (dyadTilde ((2:ℝ)^(L k) * ξ) : ℂ) = 1
          rw [dyadTilde_one habs]; simp
        rw [h1, one_mul]
    refine (Filter.EventuallyEq.of_eq (show (fun x : ℝ => dyadicProj dyadTilde (L k) (G k) x)
        = (fun x : ℝ => FourierTransformInv.fourierInv
            (fun ξ : ℝ => mT k ξ * FourierTransform.fourier (G k) ξ) x) from rfl)).trans ?_
    refine houter.trans ?_
    exact Filter.EventuallyEq.of_eq (congrArg
      (fun Z : Lp ℂ 2 (volume : Measure ℝ) => (Z : ℝ → ℂ))
      (hstep1.trans (hstep2.trans hstep3)))
  -- ## summing over `k`
  have hSumAe : (fun x : ℝ => ∑ k ∈ Finset.range K, dyadicProj dyadTilde (L k) (G k) x)
      =ᵐ[volume]
      (Commons.Analysis.Fourier.BoundaryLayer.multiplier
        (fun ξ : ℝ => ∑ k ∈ Finset.range K, σ k ξ)
        (memLpSum_top (Finset.range K) σ hσ) H : ℝ → ℂ) := by
    have h1 : (fun x : ℝ => ∑ k ∈ Finset.range K, dyadicProj dyadTilde (L k) (G k) x)
        = (∑ k ∈ Finset.range K, (fun x : ℝ => dyadicProj dyadTilde (L k) (G k) x)) := by
      funext x
      exact (Finset.sum_apply x (Finset.range K)
        (fun k => fun x => dyadicProj dyadTilde (L k) (G k) x)).symm
    rw [h1]
    refine (ae_eq_finset_sum (Finset.range K)
      (fun k => fun x : ℝ => dyadicProj dyadTilde (L k) (G k) x)
      (fun k => (Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ k) (hσ k) H : ℝ → ℂ))
      (fun k _ => hBlock k)).trans ?_
    rw [← multiplier_sum (Finset.range K) σ hσ H]
    have h2 : (∑ i ∈ Finset.range K,
          (Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ i) (hσ i) H : ℝ → ℂ))
        = (fun x => ∑ i ∈ Finset.range K,
          (Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ i) (hσ i) H : ℝ → ℂ) x) := by
      funext x
      exact Finset.sum_apply x (Finset.range K)
        (fun i => (Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ i) (hσ i) H : ℝ → ℂ))
    rw [h2]
    exact (Lp.coeFn_fun_finsetSum (Finset.range K)
      (fun k => Commons.Analysis.Fourier.BoundaryLayer.multiplier (σ k) (hσ k) H)).symm
  -- ## identifying the summed symbol with `mtaBlkSym P K ε s`
  have hSymEq : (fun ξ : ℝ => ∑ k ∈ Finset.range K, σ k ξ) = mtaBlkSym P K ε s := by
    funext ξ
    show ∑ k ∈ Finset.range K, ε k * ((dyadPsi ((2:ℝ)^(L k) * ξ) : ℂ) * muSym P k ξ)
      = ∑ k ∈ Finset.range K, ε k *
          (tildeFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ
            * psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ) * muSym P k ξ
    refine Finset.sum_congr rfl (fun k _ => ?_)
    show ε k * ((dyadPsi ((2:ℝ)^(L k) * ξ) : ℂ) * muSym P k ξ)
      = ε k * (tildeFam (L k) ξ * psiFam (L k) ξ) * muSym P k ξ
    rw [show (dyadPsi ((2:ℝ)^(L k) * ξ) : ℂ) = psiFam (L k) ξ from rfl,
      tildeFam_mul_psiFam]
    ring
  have hOP : (fun x : ℝ => mtaBlkOp P K ε s g x)
      = (fun x : ℝ => ∑ k ∈ Finset.range K, dyadicProj dyadTilde (L k) (G k) x) := by
    funext x
    simp only [mtaBlkOp]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rfl
  have hmain : (fun x : ℝ => mtaBlkOp P K ε s g x) =ᵐ[volume]
      (Commons.Analysis.Fourier.BoundaryLayer.multiplier
        (fun ξ : ℝ => ∑ k ∈ Finset.range K, σ k ξ)
        (memLpSum_top (Finset.range K) σ hσ) H : ℝ → ℂ) := by
    rw [hOP]; exact hSumAe
  refine hmain.trans (Filter.EventuallyEq.of_eq ?_)
  exact congrArg (fun Z : Lp ℂ 2 (volume : Measure ℝ) => (Z : ℝ → ℂ))
    (multiplier_congr hSymEq (memLpSum_top (Finset.range K) σ hσ) (memLp_mtaBlkSym P K ε s) H)

/-- **Assembly step.**  If each block operator `mtaBlkOp P K ε s g` is a.e. the `L²` Fourier
multiplier with the block symbol `mtaBlkSym P K ε s`, then the sum over `|s| ≤ S` is a.e. the
multiplier with the summed symbol `mtaBlkSymSum P K ε S`. -/
lemma mtaBlkOpSum_multiplier_ae_of_block (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (S : ℕ)
    {g : ℝ → ℂ} (hg2 : MeasureTheory.MemLp g 2 MeasureTheory.volume)
    (hblock : ∀ s : ℤ, (fun x : ℝ => mtaBlkOp P K ε s g x) =ᵐ[MeasureTheory.volume]
      ((Commons.Analysis.Fourier.BoundaryLayer.multiplier
        (mtaBlkSym P K ε s) (memLp_mtaBlkSym P K ε s)
        (MeasureTheory.MemLp.toLp g hg2)) : ℝ → ℂ)) :
    ∃ hm : MeasureTheory.MemLp (mtaBlkSymSum P K ε S) ⊤ MeasureTheory.volume,
      (fun x : ℝ => ∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), mtaBlkOp P K ε s g x)
        =ᵐ[MeasureTheory.volume]
        ((Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (mtaBlkSymSum P K ε S) hm
          (MeasureTheory.MemLp.toLp g hg2)) : ℝ → ℂ) := by
  classical
  have hmem : ∀ s : ℤ, MemLp (mtaBlkSym P K ε s) ⊤ (volume : Measure ℝ) :=
    fun s => memLp_mtaBlkSym P K ε s
  refine ⟨memLpSum_top (Finset.Icc (-(S : ℤ)) (S : ℤ)) (fun s => mtaBlkSym P K ε s) hmem, ?_⟩
  have hL : (fun x : ℝ => ∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), mtaBlkOp P K ε s g x)
      = ∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), (fun x : ℝ => mtaBlkOp P K ε s g x) := by
    funext x
    exact (Finset.sum_apply x (Finset.Icc (-(S : ℤ)) (S : ℤ))
      (fun s => fun x => mtaBlkOp P K ε s g x)).symm
  rw [hL]
  refine (ae_eq_finset_sum (Finset.Icc (-(S : ℤ)) (S : ℤ))
    (fun s => fun x : ℝ => mtaBlkOp P K ε s g x)
    (fun s => (Commons.Analysis.Fourier.BoundaryLayer.multiplier
      (mtaBlkSym P K ε s) (hmem s) (MeasureTheory.MemLp.toLp g hg2) : ℝ → ℂ))
    (fun s _ => hblock s)).trans ?_
  have hsum_coe : (∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ),
        (Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (mtaBlkSym P K ε s) (hmem s) (MeasureTheory.MemLp.toLp g hg2) : ℝ → ℂ))
      =ᵐ[(volume : Measure ℝ)]
        ((∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ),
          Commons.Analysis.Fourier.BoundaryLayer.multiplier
            (mtaBlkSym P K ε s) (hmem s) (MeasureTheory.MemLp.toLp g hg2) :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    refine (Filter.EventuallyEq.of_eq ?_).trans (Lp.coeFn_fun_finsetSum (Finset.Icc (-(S : ℤ)) (S : ℤ))
      (fun s => Commons.Analysis.Fourier.BoundaryLayer.multiplier
        (mtaBlkSym P K ε s) (hmem s) (MeasureTheory.MemLp.toLp g hg2))).symm
    funext x
    exact Finset.sum_apply x (Finset.Icc (-(S : ℤ)) (S : ℤ))
      (fun s => Commons.Analysis.Fourier.BoundaryLayer.multiplier
        (mtaBlkSym P K ε s) (hmem s) (MeasureTheory.MemLp.toLp g hg2))
  refine hsum_coe.trans ?_
  rw [multiplier_sum (Finset.Icc (-(S : ℤ)) (S : ℤ)) (fun s => mtaBlkSym P K ε s) hmem
    (MeasureTheory.MemLp.toLp g hg2)]
  rfl

theorem mtaBlkOpSum_multiplier_ae (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (S : ℕ) {g : ℝ → ℂ}
    (hg1 : MeasureTheory.Integrable g) (hg2 : MeasureTheory.MemLp g 2 MeasureTheory.volume) :
    ∃ hm : MeasureTheory.MemLp (Work.BourgainPlan.Maximal.mtaBlkSymSum P K ε S) ⊤ MeasureTheory.volume,
      (fun x : ℝ => ∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ),
          Work.BourgainPlan.Maximal.mtaBlkOp P K ε s g x) =ᵐ[MeasureTheory.volume]
        (Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (Work.BourgainPlan.Maximal.mtaBlkSymSum P K ε S) hm
          (MeasureTheory.MemLp.toLp g hg2) : ℝ → ℂ) := by
  exact mtaBlkOpSum_multiplier_ae_of_block P K ε S hg2
    (fun s => mtaBlkOp_multiplier_ae_block P K ε s hg1 hg2)

end

end Work.BourgainPlan.Maximal
