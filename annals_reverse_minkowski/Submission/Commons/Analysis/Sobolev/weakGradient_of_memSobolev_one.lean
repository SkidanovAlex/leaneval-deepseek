import Mathlib
import Submission.Commons.Analysis.Sobolev.memSobolev_one_of_weak_solutionH1
import Submission.Commons.Analysis.Sobolev.integral_mul_eq_neg_integral_fderiv_of_contDiff_two

set_option maxHeartbeats 4000000

namespace Commons.Analysis.Sobolev

open MeasureTheory LineDeriv Filter
open scoped ENNReal ContDiff SchwartzMap Laplacian LineDeriv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Evaluation of the tempered distribution attached to an `L²` complex function. -/
lemma Lp_toTempered_applyC (w : Lp ℂ 2 (volume : Measure E)) (θ : 𝓢(E, ℂ)) :
    (w : TemperedDistribution E ℂ) θ = ∫ x, θ x * w x := by
  have h := Commons.Analysis.Sobolev.Lp_toTemperedDistribution_apply' (f := ⇑w) (Lp.memLp w) θ
  rwa [Lp.toLp_coeFn] at h

/-- The product of an `L²` function with a continuous compactly supported function is integrable. -/
lemma integrable_mul_of_continuous_hasCompactSupport {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} (hf : MemLp f 2 (volume : Measure E))
    {g : E → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => f x * g x) (volume : Measure E) :=
  MemLp.integrable_mul (p := 2) (q := 2) hf (hg.memLp_of_hasCompactSupport (p := 2) hgc)


/-- The `v`-th directional derivative of a compactly supported function is compactly supported. -/
lemma hasCompactSupport_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (h : HasCompactSupport φ) (v : E) :
    HasCompactSupport (fun x => (fderiv ℝ φ x) v) := by
  refine HasCompactSupport.mono' (f := φ) (f' := fun x => (fderiv ℝ φ x) v) h ?_
  intro x hx
  rw [Function.mem_support] at hx
  have h2 : x ∈ Function.support (fderiv ℝ φ) := by
    rw [Function.mem_support]; intro hz; rw [hz] at hx; simp at hx
  exact tsupport_fderiv_subset ℝ (subset_tsupport _ h2)

/-- The gradient of a compactly supported function is compactly supported. -/
lemma hasCompactSupport_grad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {φ : E → ℝ} (h : HasCompactSupport φ) :
    HasCompactSupport (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x)) := by
  refine HasCompactSupport.mono' (f := φ)
    (f' := fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x)) h ?_
  intro x hx
  rw [Function.mem_support] at hx
  have h2 : x ∈ Function.support (fderiv ℝ φ) := by
    rw [Function.mem_support]; intro hz; rw [hz] at hx; simp at hx
  exact tsupport_fderiv_subset ℝ (subset_tsupport _ h2)

/-- If `psi` is in `H^1` and solves the weak weighted equation `Delta psi + div (psi grad f) = 0`
(equivalently `g = psi e^f` has weighted-divergence-free gradient), then `g` has a locally `L^2`
weak gradient `G` satisfying the weighted integration by parts identities. -/
theorem weakGradient_of_memSobolev_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f g ψ : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : MemLp g 2 (volume.withDensity (fun x : E => ENNReal.ofReal (Real.exp (-(f x))))))
    (hψeq : ψ =ᵐ[(volume : Measure E)] fun x => g x * Real.exp (-(f x)))
    (hψ : MemLp (fun x : E => ((ψ x : ℝ) : ℂ)) 2 (volume : Measure E))
    (hspec : TemperedDistribution.MemSobolev 1 2
      (↑(hψ.toLp (fun x : E => ((ψ x : ℝ) : ℂ))) : TemperedDistribution E ℂ))
    (hw : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x : E, ((ψ x : ℝ) : ℂ) * (((Laplacian.laplacian φ x : ℝ) : ℂ)
        - ((inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
              ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x)) : ℝ) : ℂ))) = 0) :
    ∃ G : E → E,
      (∀ K : Set E, IsCompact K → IntegrableOn (fun x => ‖G x‖ ^ 2) K volume) ∧
      (∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∫ x, inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x)) (G x)
          * Real.exp (-(f x)) = 0) ∧
      (∀ (φ : E → ℝ) (v : E), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∫ x, φ x * inner ℝ v (G x) = -∫ x, (fderiv ℝ φ x) v * g x) := by
  classical
  set U : TemperedDistribution E ℂ := ↑(hψ.toLp (fun x : E => ((ψ x : ℝ) : ℂ))) with hUdef
  set b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E with hbdef
  have hUI : ∀ θ : 𝓢(E, ℂ), U θ = ∫ x, θ x * ((ψ x : ℝ) : ℂ) := by
    intro θ
    rw [hUdef]
    exact Lp_toTemperedDistribution_apply' hψ θ
  have hex : ∀ i : Fin (Module.finrank ℝ E), ∃ w : Lp ℂ 2 (volume : Measure E),
      LineDeriv.lineDerivOp (b i) U = (w : TemperedDistribution E ℂ) := fun i => by
    have h : TemperedDistribution.MemSobolev (1 - 1) 2 (LineDeriv.lineDerivOp (b i) U) :=
      hspec.lineDerivOp
    have h0 : TemperedDistribution.MemSobolev (0 : ℝ) 2 (LineDeriv.lineDerivOp (b i) U) := by
      simpa using h
    exact TemperedDistribution.memSobolev_zero_iff.mp h0
  choose wi hwi using hex
  set Wi : Fin (Module.finrank ℝ E) → E → ℝ := fun i x => ((wi i) x).re with hWidef
  have hWimem : ∀ i, MemLp (Wi i) 2 (volume : Measure E) := fun i => by
    simpa [hWidef, RCLike.re_eq_complex_re] using (Lp.memLp (wi i)).re
  set W : E → E := fun x => ∑ i, Wi i x • b i with hWdef
  have hWmem : MemLp W 2 (volume : Measure E) := by
    have hterm : ∀ i : Fin (Module.finrank ℝ E),
        MemLp (fun x => Wi i x • b i) 2 (volume : Measure E) := by
      intro i
      refine (hWimem i).of_le ?_ ?_
      · exact (hWimem i).aestronglyMeasurable.smul_const (b i)
      · filter_upwards with x
        rw [norm_smul, b.orthonormal.norm_eq_one i, mul_one]
    have := memLp_finsetSum (s := Finset.univ) (f := fun i x => Wi i x • b i)
      (fun i _ => hterm i)
    simpa [hWdef] using this
  have hψreal : MemLp ψ 2 (volume : Measure E) := by
    refine hψ.of_le ?_ ?_
    · exact Complex.continuous_re.comp_aestronglyMeasurable hψ.aestronglyMeasurable
    · filter_upwards with x
      simp [Complex.norm_real]
  set gradf : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x) with hgradfdef
  have hgradfcont : Continuous gradf :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hf.continuous_fderiv (by norm_num))
  -- #### KI: the weak derivative identity for Schwartz test functions
  have KI : ∀ (i : Fin (Module.finrank ℝ E)) (χ : 𝓢(E, ℝ)),
      ∫ x, χ x * Wi i x = - ∫ x, (LineDeriv.lineDerivOp (b i) χ) x * ψ x := by
    intro i χ
    have hcomplex : (∫ x, (Commons.Analysis.Sobolev.cplxMap χ) x * wi i x)
        = - ∫ x, (LineDeriv.lineDerivOp (b i) (Commons.Analysis.Sobolev.cplxMap χ)) x
            * ((ψ x : ℝ) : ℂ) := by
      rw [← Lp_toTempered_applyC (wi i) (Commons.Analysis.Sobolev.cplxMap χ),
          ← hwi i, Commons.Analysis.Sobolev.lineDerivOp_apply_tempered]
      congr 1
      exact hUI (LineDeriv.lineDerivOp (b i) (Commons.Analysis.Sobolev.cplxMap χ))
    have h1 : Integrable (fun x => (Commons.Analysis.Sobolev.cplxMap χ) x * wi i x)
        (volume : Measure E) :=
      MemLp.integrable_mul (SchwartzMap.memLp _ 2 volume) (Lp.memLp (wi i))
    have h2 : Integrable (fun x =>
        (LineDeriv.lineDerivOp (b i) (Commons.Analysis.Sobolev.cplxMap χ)) x * ((ψ x : ℝ) : ℂ))
        (volume : Measure E) :=
      MemLp.integrable_mul (SchwartzMap.memLp _ 2 volume) hψ
    have hre := congrArg Complex.reCLM hcomplex
    rw [map_neg, ← Complex.reCLM.integral_comp_comm h1, ← Complex.reCLM.integral_comp_comm h2] at hre
    simp only [Complex.reCLM_apply, Commons.Analysis.Sobolev.cplxMap_apply, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Commons.Analysis.Sobolev.lineDerivOp_cplxMap] at hre
    simpa [hWidef] using hre
  -- #### KI2: extend to `C^2` compactly supported test functions
  have KI2 : ∀ (i : Fin (Module.finrank ℝ E)) (χ : E → ℝ), ContDiff ℝ 2 χ → HasCompactSupport χ →
      ∫ x, χ x * Wi i x = -∫ x, (fderiv ℝ χ x) (b i) * ψ x := by
    intro i χ hχ hχc
    exact integral_mul_eq_neg_integral_fderiv_of_contDiff_two (Wi i) ψ (b i)
      (hWimem i) hψreal (fun χ' => by
        rw [KI i χ']
        rfl) χ hχ hχc
  -- #### the directional derivative in terms of the orthonormal basis
  have hdir : ∀ (χ : E → ℝ) (v x : E),
      (∑ i, inner ℝ v (b i) * (fderiv ℝ χ x) (b i)) = (fderiv ℝ χ x) v := by
    intro χ v x
    conv_rhs => rw [← OrthonormalBasis.sum_repr' b v]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, real_inner_comm, smul_eq_mul]
  have hW_inner : ∀ (x v : E), inner ℝ v (W x) = ∑ i, inner ℝ v (b i) * Wi i x := by
    intro x v
    rw [hWdef]
    simp only [inner_sum, inner_smul_right]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  -- #### the distributional Laplacian identity
  have hLap : ∀ (Φ : 𝓢(E, ℝ)), HasCompactSupport (⇑Φ) →
      ∫ x, ψ x * Laplacian.laplacian (⇑Φ) x
        = -∑ i, ∫ x, (fderiv ℝ (⇑Φ) x) (b i) * Wi i x := by
    intro Φ hΦc
    have hfun : Laplacian.laplacian (⇑Φ)
        = fun x => ∑ i, (LineDeriv.lineDerivOp (b i) (LineDeriv.lineDerivOp (b i) Φ)) x := by
      funext x
      rw [← SchwartzMap.laplacian_apply Φ x, SchwartzMap.laplacian_eq_sum b Φ]
      simp
    have key : ∀ i, ∫ x, ψ x * (LineDeriv.lineDerivOp (b i) (LineDeriv.lineDerivOp (b i) Φ)) x
        = -∫ x, (fderiv ℝ (⇑Φ) x) (b i) * Wi i x := by
      intro i
      have hχsmooth : ContDiff ℝ 2 (fun x => (LineDeriv.lineDerivOp (b i) Φ) x) :=
        ((LineDeriv.lineDerivOp (b i) Φ).smooth 2)
      have hχcpt : HasCompactSupport (fun x => (LineDeriv.lineDerivOp (b i) Φ) x) :=
        hΦc.mono' (fun x hx => SchwartzMap.tsupport_lineDerivOp_subset (b i) Φ (subset_tsupport _ hx))
      have h0 := KI2 i (fun x => (LineDeriv.lineDerivOp (b i) Φ) x) hχsmooth hχcpt
      rw [show (fun x => (fderiv ℝ (fun y => (LineDeriv.lineDerivOp (b i) Φ) y) x) (b i) * ψ x)
            = (fun x => (LineDeriv.lineDerivOp (b i) (LineDeriv.lineDerivOp (b i) Φ)) x * ψ x) from
          funext (fun x => by rw [SchwartzMap.lineDerivOp_apply_eq_fderiv])] at h0
      rw [show (fun x => (fderiv ℝ (⇑Φ) x) (b i) * Wi i x)
            = (fun x => (LineDeriv.lineDerivOp (b i) Φ) x * Wi i x) from
          funext (fun x => by rw [SchwartzMap.lineDerivOp_apply_eq_fderiv])]
      rw [show (fun x => ψ x * (LineDeriv.lineDerivOp (b i) (LineDeriv.lineDerivOp (b i) Φ)) x)
            = (fun x => (LineDeriv.lineDerivOp (b i) (LineDeriv.lineDerivOp (b i) Φ)) x * ψ x) from
          funext (fun x => by ring)]
      rw [h0]; ring
    calc ∫ x, ψ x * Laplacian.laplacian (⇑Φ) x
        = ∫ x, ψ x * (∑ i, (LineDeriv.lineDerivOp (b i) (LineDeriv.lineDerivOp (b i) Φ)) x) := by
          rw [hfun]
      _ = ∫ x, ∑ i, ψ x * (LineDeriv.lineDerivOp (b i) (LineDeriv.lineDerivOp (b i) Φ)) x := by
          refine integral_congr_ae (show
            (fun x => ψ x * (∑ i, (LineDeriv.lineDerivOp (b i) (LineDeriv.lineDerivOp (b i) Φ)) x))
              =ᵐ[(volume : Measure E)]
            (fun x => ∑ i, ψ x * (LineDeriv.lineDerivOp (b i) (LineDeriv.lineDerivOp (b i) Φ)) x) from
            Eventually.of_forall (fun x => by simp only [Finset.mul_sum]))
      _ = ∑ i, ∫ x, ψ x * (LineDeriv.lineDerivOp (b i) (LineDeriv.lineDerivOp (b i) Φ)) x := by
          rw [MeasureTheory.integral_finsetSum]
          intro i _
          exact MemLp.integrable_mul hψreal (SchwartzMap.memLp _ 2 volume)
      _ = -∑ i, ∫ x, (fderiv ℝ (⇑Φ) x) (b i) * Wi i x := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun i _ => key i)
  -- #### the weak derivative identity in an arbitrary direction
  have KI2v : ∀ (χ : E → ℝ), ContDiff ℝ 2 χ → HasCompactSupport χ → ∀ v : E,
      ∫ x, χ x * inner ℝ v (W x) = -∫ x, (fderiv ℝ χ x) v * ψ x := by
    intro χ hχ hχc v
    have hmem : ∀ i, Integrable (fun x => inner ℝ v (b i) * (χ x * Wi i x)) (volume : Measure E) :=
      fun i => ((integrable_mul_of_continuous_hasCompactSupport (hWimem i) hχ.continuous hχc).const_mul _).congr
        (Eventually.of_forall (fun x => by ring))
    rw [show (∫ x, χ x * inner ℝ v (W x))
          = ∫ x, ∑ i, inner ℝ v (b i) * (χ x * Wi i x) from
        integral_congr_ae (show (fun x => χ x * inner ℝ v (W x))
            =ᵐ[(volume : Measure E)] (fun x => ∑ i, inner ℝ v (b i) * (χ x * Wi i x)) from
          Eventually.of_forall (fun x => by
            show χ x * inner ℝ v (W x) = ∑ i, inner ℝ v (b i) * (χ x * Wi i x)
            rw [hW_inner x v]
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ => by ring)))]
    rw [MeasureTheory.integral_finsetSum _ (fun i _ => hmem i)]
    rw [show (∑ i, ∫ x, inner ℝ v (b i) * (χ x * Wi i x))
          = ∑ i, inner ℝ v (b i) * ∫ x, χ x * Wi i x from
        Finset.sum_congr rfl (fun i _ => MeasureTheory.integral_const_mul _ _)]
    rw [show (∑ i, inner ℝ v (b i) * ∫ x, χ x * Wi i x)
          = ∑ i, -(inner ℝ v (b i) * ∫ x, (fderiv ℝ χ x) (b i) * ψ x) from
        Finset.sum_congr rfl (fun i _ => by rw [KI2 i χ hχ hχc, mul_neg])]
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [show (∑ i, inner ℝ v (b i) * ∫ x, (fderiv ℝ χ x) (b i) * ψ x)
          = ∑ i, ∫ x, inner ℝ v (b i) * ((fderiv ℝ χ x) (b i) * ψ x) from
        Finset.sum_congr rfl (fun i _ => (MeasureTheory.integral_const_mul _ _).symm)]
    rw [← MeasureTheory.integral_finsetSum]
    · refine integral_congr_ae (show
          (fun x => ∑ i, inner ℝ v (b i) * ((fderiv ℝ χ x) (b i) * ψ x))
            =ᵐ[(volume : Measure E)] (fun x => (fderiv ℝ χ x) v * ψ x) from
        Eventually.of_forall (fun x => ?_))
      show (∑ i, inner ℝ v (b i) * ((fderiv ℝ χ x) (b i) * ψ x)) = (fderiv ℝ χ x) v * ψ x
      rw [show (∑ i, inner ℝ v (b i) * ((fderiv ℝ χ x) (b i) * ψ x))
            = (∑ i, inner ℝ v (b i) * (fderiv ℝ χ x) (b i)) * ψ x from by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => (mul_assoc _ _ _).symm)]
      rw [hdir χ v x]
    · intro i _
      have hcf0 : MemLp (fun x => (fderiv ℝ χ x) (b i)) 2 (volume : Measure E) :=
        ((hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
          (p := 2) (hasCompactSupport_fderiv_apply hχc (b i))
      have hcf : MemLp (fun x => inner ℝ v (b i) * (fderiv ℝ χ x) (b i)) 2 (volume : Measure E) :=
        hcf0.const_mul _
      have h' := MemLp.integrable_mul (p := 2) (q := 2) hcf hψreal
      rw [show ((fun x => inner ℝ v (b i) * (fderiv ℝ χ x) (b i)) * ψ)
            = (fun x => inner ℝ v (b i) * ((fderiv ℝ χ x) (b i) * ψ x)) from
          funext (fun x => by rw [Pi.mul_apply]; ring)] at h'
      exact h'
  -- #### the candidate weak gradient
  set G : E → E := fun x => Real.exp (f x) • (W x + ψ x • gradf x) with hGdef
  refine ⟨G, ?_, ?_, ?_⟩
  · -- local `L²`
    intro K hK
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun x => Real.exp (f x))
      (Real.continuous_exp.comp hf.continuous).continuousOn
    obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (f := gradf) hgradfcont.continuousOn
    have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
    have hWr : MemLp W 2 (volume.restrict K) := hWmem.restrict K
    have hψr : MemLp ψ 2 (volume.restrict K) := hψreal.restrict K
    have hgradLinf : MemLp gradf ⊤ (volume.restrict K) := by
      refine memLp_top_of_bound hgradfcont.aestronglyMeasurable (max D 0) ?_
      filter_upwards [ae_restrict_mem hKmeas] with x hx
      exact (hD x hx).trans (le_max_left _ _)
    have hefLinf : MemLp (fun x => Real.exp (f x)) ⊤ (volume.restrict K) := by
      refine memLp_top_of_bound (Real.continuous_exp.comp hf.continuous).aestronglyMeasurable
        (max C 0) ?_
      filter_upwards [ae_restrict_mem hKmeas] with x hx
      have h1 : ‖Real.exp (f x)‖ ≤ max C 0 := (hC x hx).trans (le_max_left _ _)
      simpa [Real.norm_of_nonneg (Real.exp_nonneg _)] using h1
    have hGmem : MemLp G 2 (volume.restrict K) := by
      have h3 : MemLp (fun x => W x + ψ x • gradf x) 2 (volume.restrict K) :=
        hWr.add (hgradLinf.smul hψr)
      rw [show G = ((fun x => Real.exp (f x)) • fun x => W x + ψ x • gradf x) from by
        rw [hGdef]
        funext x
        rfl]
      exact MemLp.smul (r := 2) h3 hefLinf
    exact (memLp_two_iff_integrable_sq_norm hGmem.aestronglyMeasurable).mp hGmem
  · -- the weighted integration by parts identity
    intro φ hφ hφc
    set Φ : 𝓢(E, ℝ) := hφc.toSchwartzMap hφ with hΦdef
    have hΦfun : (⇑Φ : E → ℝ) = φ :=
      funext (fun x => HasCompactSupport.toSchwartzMap_toFun hφc hφ x)
    have hΦc : HasCompactSupport (⇑Φ) := by rw [hΦfun]; exact hφc
    set A : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x) with hAdef
    have hAcont : Continuous A :=
      (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hφ.continuous_fderiv (by norm_num))
    have hAcpt : HasCompactSupport A := by
      rw [hAdef]; exact hasCompactSupport_grad hφc
    have hpd : ∀ i, Integrable (fun x => (fderiv ℝ φ x) (b i) * Wi i x) (volume : Measure E) := by
      intro i
      have h' := integrable_mul_of_continuous_hasCompactSupport (hWimem i)
        ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
        (hasCompactSupport_fderiv_apply hφc (b i))
      rw [show (fun x => Wi i x * (fderiv ℝ φ x) (b i))
            = (fun x => (fderiv ℝ φ x) (b i) * Wi i x) from funext (fun x => by ring)] at h'
      exact h'
    have hA2 : Integrable (fun x => ψ x * inner ℝ (gradf x) (A x)) (volume : Measure E) := by
      refine integrable_mul_of_continuous_hasCompactSupport hψreal ?_ ?_
      · exact continuous_inner.comp (hgradfcont.prodMk hAcont)
      · exact hAcpt.mono (fun x hx => by
          simp only [Function.mem_support, ne_eq] at hx ⊢
          intro hz; exact hx (by rw [hz, inner_zero_right]))
    have hA1 : Integrable (fun x => inner ℝ (A x) (W x)) (volume : Measure E) := by
      have hsum : (fun x => inner ℝ (A x) (W x))
          = fun x => ∑ i, (fderiv ℝ φ x) (b i) * Wi i x := by
        funext x
        show inner ℝ (A x) (W x) = ∑ i, (fderiv ℝ φ x) (b i) * Wi i x
        rw [hW_inner x (A x)]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hAdef, InnerProductSpace.toDual_symm_apply]
      rw [hsum]
      exact MeasureTheory.integrable_finsetSum _ (fun i _ => hpd i)
    have hpt : ∀ x, inner ℝ (A x) (G x) * Real.exp (-(f x))
        = inner ℝ (A x) (W x) + ψ x * inner ℝ (gradf x) (A x) := by
      intro x
      rw [hGdef]
      simp only [inner_smul_right, inner_add_right, real_inner_comm (gradf x) (A x)]
      rw [Real.exp_neg]
      field_simp
    have hsplit : (∫ x, inner ℝ (A x) (W x))
        = ∑ i, ∫ x, (fderiv ℝ φ x) (b i) * Wi i x := by
      rw [show (∫ x, inner ℝ (A x) (W x))
            = ∫ x, ∑ i, (fderiv ℝ φ x) (b i) * Wi i x from
          integral_congr_ae (show (fun x => inner ℝ (A x) (W x))
              =ᵐ[(volume : Measure E)] (fun x => ∑ i, (fderiv ℝ φ x) (b i) * Wi i x) from
            Eventually.of_forall (fun x => by
              show inner ℝ (A x) (W x) = ∑ i, (fderiv ℝ φ x) (b i) * Wi i x
              rw [hW_inner x (A x)]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [hAdef, InnerProductSpace.toDual_symm_apply]))]
      rw [MeasureTheory.integral_finsetSum _ (fun i _ => hpd i)]
    have hL : (∑ i, ∫ x, (fderiv ℝ φ x) (b i) * Wi i x)
        = -∫ x, ψ x * Laplacian.laplacian φ x := by
      have h := hLap Φ hΦc
      rw [hΦfun] at h
      rw [h]; ring
    have hpsch : Integrable (fun x => ψ x * Laplacian.laplacian φ x) (volume : Measure E) := by
      have hfunΔ : (fun x => Laplacian.laplacian (⇑Φ) x) = ⇑(Laplacian.laplacian Φ) :=
        funext (fun x => (SchwartzMap.laplacian_apply Φ x).symm)
      have hΔ : MemLp (fun x => Laplacian.laplacian (⇑Φ) x) 2 (volume : Measure E) := by
        rw [hfunΔ]; exact SchwartzMap.memLp _ 2 volume
      have h' : Integrable (fun x => ψ x * Laplacian.laplacian (⇑Φ) x) (volume : Measure E) :=
        MemLp.integrable_mul hψreal hΔ
      rw [hΦfun] at h'
      exact h'
    have hwre : ∫ x, ψ x * Laplacian.laplacian φ x
        = ∫ x, ψ x * inner ℝ (gradf x) (A x) := by
      have h0 := hw φ hφ hφc
      rw [show (fun x => ((ψ x : ℝ) : ℂ) * (((Laplacian.laplacian φ x : ℝ) : ℂ)
            - ((inner ℝ (gradf x) (A x) : ℝ) : ℂ)))
          = fun x => ((ψ x * (Laplacian.laplacian φ x - inner ℝ (gradf x) (A x)) : ℝ) : ℂ) from
        funext (fun x => by push_cast; ring)] at h0
      have hint : Integrable (fun x =>
          ((ψ x * (Laplacian.laplacian φ x - inner ℝ (gradf x) (A x)) : ℝ) : ℂ))
          (volume : Measure E) :=
        ((hpsch.sub hA2).congr (show (fun x => ψ x * Laplacian.laplacian φ x - ψ x * inner ℝ (gradf x) (A x))
            =ᵐ[(volume : Measure E)]
            (fun x => ((ψ x * (Laplacian.laplacian φ x - inner ℝ (gradf x) (A x)) : ℝ))) from
          Eventually.of_forall (fun x => by
            show ψ x * Laplacian.laplacian φ x - ψ x * inner ℝ (gradf x) (A x)
              = ψ x * (Laplacian.laplacian φ x - inner ℝ (gradf x) (A x))
            ring))).ofReal
      have hre := congrArg Complex.reCLM h0
      rw [map_zero, ← Complex.reCLM.integral_comp_comm hint] at hre
      have hEq : (∫ x, ψ x * (Laplacian.laplacian φ x - inner ℝ (gradf x) (A x))) = 0 := by
        simpa [Complex.reCLM_apply] using hre
      rw [show (fun x => ψ x * (Laplacian.laplacian φ x - inner ℝ (gradf x) (A x)))
            = (fun x => ψ x * Laplacian.laplacian φ x - ψ x * inner ℝ (gradf x) (A x)) from
          funext (fun x => by
            show ψ x * (Laplacian.laplacian φ x - inner ℝ (gradf x) (A x))
              = ψ x * Laplacian.laplacian φ x - ψ x * inner ℝ (gradf x) (A x)
            ring)] at hEq
      rw [MeasureTheory.integral_sub hpsch hA2] at hEq
      exact sub_eq_zero.mp hEq
    calc ∫ x, inner ℝ (A x) (G x) * Real.exp (-(f x))
        = ∫ x, (inner ℝ (A x) (W x) + ψ x * inner ℝ (gradf x) (A x)) :=
          integral_congr_ae (Eventually.of_forall hpt)
      _ = (∫ x, inner ℝ (A x) (W x)) + (∫ x, ψ x * inner ℝ (gradf x) (A x)) :=
          MeasureTheory.integral_add hA1 hA2
      _ = (∑ i, ∫ x, (fderiv ℝ φ x) (b i) * Wi i x) + (∫ x, ψ x * inner ℝ (gradf x) (A x)) := by
          rw [hsplit]
      _ = (-(∫ x, ψ x * Laplacian.laplacian φ x)) + (∫ x, ψ x * inner ℝ (gradf x) (A x)) := by
          rw [hL]
      _ = 0 := by rw [hwre]; ring
  · -- the weak gradient identity
    intro φ v hφ hφc
    set χ : E → ℝ := fun x => φ x * Real.exp (f x) with hχdef
    have hχ2 : ContDiff ℝ 2 χ := by
      rw [hχdef]
      exact (hφ.of_le (by norm_cast)).mul (hf.exp)
    have hχc : HasCompactSupport χ := by
      rw [hχdef]; exact hφc.mul_right
    have hχderiv : ∀ x, (fderiv ℝ χ x) v
        = (fderiv ℝ φ x) v * Real.exp (f x) + φ x * Real.exp (f x) * (fderiv ℝ f x) v := by
      intro x
      rw [hχdef, fderiv_fun_mul ((hφ.differentiable (by norm_num)) x)
        ((hf.exp).differentiable (by norm_num) x)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [show (fderiv ℝ (fun y => Real.exp (f y)) x) v = Real.exp (f x) * (fderiv ℝ f x) v from by
        rw [(hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt.exp.fderiv]
        simp]
      ring
    have hgradfv : ∀ x, inner ℝ v (gradf x) = (fderiv ℝ f x) v := by
      intro x
      show inner ℝ v ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) = (fderiv ℝ f x) v
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    have hAint : Integrable (fun x => (fderiv ℝ χ x) v * ψ x) (volume : Measure E) := by
      have hcont : Continuous (fun x => (fderiv ℝ χ x) v) :=
        (hχ2.continuous_fderiv (by norm_num)).clm_apply continuous_const
      have hcpt : HasCompactSupport (fun x => (fderiv ℝ χ x) v) :=
        hasCompactSupport_fderiv_apply hχc v
      have h' := integrable_mul_of_continuous_hasCompactSupport hψreal hcont hcpt
      rw [show (fun x => ψ x * (fderiv ℝ χ x) v) = (fun x => (fderiv ℝ χ x) v * ψ x) from
        funext (fun x => by ring)] at h'
      exact h'
    have hInternal : MemLp (fun x => inner ℝ v (W x)) 2 (volume : Measure E) := by
      refine (hWmem.norm.const_mul ‖v‖).of_le ?_ ?_
      · exact (continuous_inner.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable
          hWmem.aestronglyMeasurable
      · filter_upwards with x
        simpa only [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
          using norm_inner_le_norm v (W x)
    have hInnerW : Integrable (fun x => χ x * inner ℝ v (W x)) (volume : Measure E) := by
      have h' := integrable_mul_of_continuous_hasCompactSupport hInternal hχ2.continuous hχc
      rw [show (fun x => inner ℝ v (W x) * χ x) = (fun x => χ x * inner ℝ v (W x)) from
        funext (fun x => by ring)] at h'
      exact h'
    have hInner2 : Integrable (fun x => (χ x * ψ x) * (fderiv ℝ f x) v) (volume : Measure E) := by
      have hg : Continuous (fun x => χ x * (fderiv ℝ f x) v) :=
        hχ2.continuous.mul ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      have hgc : HasCompactSupport (fun x => χ x * (fderiv ℝ f x) v) := hχc.mul_right
      have h' := integrable_mul_of_continuous_hasCompactSupport hψreal hg hgc
      rw [show (fun x => ψ x * (χ x * (fderiv ℝ f x) v))
            = (fun x => (χ x * ψ x) * (fderiv ℝ f x) v) from
          funext (fun x => by ring)] at h'
      exact h'
    have hgeq : g =ᵐ[(volume : Measure E)] fun x => ψ x * Real.exp (f x) := by
      filter_upwards [hψeq] with x hx
      rw [hx, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    have hpt : ∀ x, φ x * inner ℝ v (G x)
        = χ x * inner ℝ v (W x) + (χ x * ψ x) * (fderiv ℝ f x) v := by
      intro x
      show φ x * inner ℝ v (Real.exp (f x) • (W x + ψ x • gradf x))
          = χ x * inner ℝ v (W x) + (χ x * ψ x) * (fderiv ℝ f x) v
      simp only [inner_smul_right, inner_add_right]
      rw [hgradfv x, hχdef]
      ring
    calc ∫ x, φ x * inner ℝ v (G x)
        = ∫ x, (χ x * inner ℝ v (W x) + (χ x * ψ x) * (fderiv ℝ f x) v) :=
          integral_congr_ae (Eventually.of_forall hpt)
      _ = (∫ x, χ x * inner ℝ v (W x)) + (∫ x, (χ x * ψ x) * (fderiv ℝ f x) v) :=
          MeasureTheory.integral_add hInnerW hInner2
      _ = (-(∫ x, (fderiv ℝ χ x) v * ψ x)) + (∫ x, (χ x * ψ x) * (fderiv ℝ f x) v) := by
          rw [KI2v χ hχ2 hχc v]
      _ = -(∫ x, (fderiv ℝ φ x) v * Real.exp (f x) * ψ x) := by
          have hAneg : Integrable (fun x => -((fderiv ℝ χ x) v * ψ x)) (volume : Measure E) := hAint.neg
          rw [show (-(∫ x, (fderiv ℝ χ x) v * ψ x)) = ∫ x, -((fderiv ℝ χ x) v * ψ x) from
            (integral_neg (fun x => (fderiv ℝ χ x) v * ψ x)).symm]
          rw [← MeasureTheory.integral_add hAneg hInner2]
          rw [show (∫ x, -((fderiv ℝ χ x) v * ψ x) + (χ x * ψ x) * (fderiv ℝ f x) v)
                = ∫ x, -((fderiv ℝ φ x) v * Real.exp (f x) * ψ x) from by
              refine integral_congr_ae (show
                (fun x => -((fderiv ℝ χ x) v * ψ x) + (χ x * ψ x) * (fderiv ℝ f x) v)
                  =ᵐ[(volume : Measure E)]
                (fun x => -((fderiv ℝ φ x) v * Real.exp (f x) * ψ x)) from
                Eventually.of_forall (fun x => ?_))
              show -((fderiv ℝ χ x) v * ψ x) + (χ x * ψ x) * (fderiv ℝ f x) v
                  = -((fderiv ℝ φ x) v * Real.exp (f x) * ψ x)
              rw [hχderiv x]; ring]
          rw [MeasureTheory.integral_neg]
      _ = -(∫ x, (fderiv ℝ φ x) v * g x) := by
          congr 1
          refine integral_congr_ae (show (fun x => (fderiv ℝ φ x) v * Real.exp (f x) * ψ x)
              =ᵐ[(volume : Measure E)] (fun x => (fderiv ℝ φ x) v * g x) from ?_)
          filter_upwards [hgeq] with x hx
          rw [hx]; ring


end Commons.Analysis.Sobolev
