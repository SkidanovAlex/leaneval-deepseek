import Mathlib
import Submission.Work.Drive.N2.roundConfigDefs
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.regularLevelCircles
import Submission.Work.Drive.N2.localInverseContDiffOnNhd
import Submission.Work.Drive.N2.LevelModelAux
import Submission.Work.Drive.N2.exists_contMDiff_bump_tsupport
import Submission.Work.Compat.MFDerivCongrV433

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology

noncomputable section

/-! ## The round picture: the two angle functions -/

/-- The identity `(Fin 3 → ℝ) → ℝ³` as a continuous linear map. -/
def mkCLM : (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem mkCLM_apply (f : Fin 3 → ℝ) : (mkCLM f).ofLp = f := by
  simp [mkCLM]

/-- The velocity `(-sin t, cos t, 0)` of the round picture. -/
def picVel (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  mkCLM ![-Real.sin t, Real.cos t, (0 : ℝ)]

theorem picVel_ofLp (t : ℝ) :
    (picVel t).ofLp = ![-Real.sin t, Real.cos t, (0 : ℝ)] := by
  simp [picVel, mkCLM]

theorem roundPic_eq_mkCLM (t : ℝ) :
    roundPic t = mkCLM (![Real.cos t, Real.sin t, (0 : ℝ)] : Fin 3 → ℝ) := by
  simp [roundPic, mkCLM]

theorem picVel_ne_zero (t : ℝ) : picVel t ≠ 0 := by
  intro h
  have h0 : (-Real.sin t : ℝ) = 0 ∧ Real.cos t = 0 := by
    have := congrArg WithLp.ofLp h
    simpa [picVel_ofLp] using this
  have hs : Real.sin t = 0 := by linarith [h0.1]
  nlinarith [Real.cos_sq_add_sin_sq t, h0.2]

theorem roundPic_add (a b : ℝ) :
    roundPic (a + b) = Real.cos a • roundPic b + Real.sin a • roundPic (b + Real.pi / 2) := by
  refine WithLp.ofLp_injective 2 ?_
  simp only [roundPic, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_toLp]
  funext i
  fin_cases i <;>
    simp [Real.cos_add, Real.sin_add, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two] <;> ring

/-- The round picture at circle-parameter `t`: `roundPic (2 π t)`, run once around as `t` runs
over `[0,1)`. -/
def ang (t : ℝ) : EuclideanSpace ℝ (Fin 3) := roundPic (2 * Real.pi * t)

/-- The quarter turn of `ang`: `roundPic (2 π t + π/2)`. -/
def angPerp (t : ℝ) : EuclideanSpace ℝ (Fin 3) := roundPic (2 * Real.pi * t + Real.pi / 2)

theorem ang_ofLp (t : ℝ) :
    (ang t).ofLp = ![Real.cos (2 * Real.pi * t), Real.sin (2 * Real.pi * t), (0 : ℝ)] := by
  simp [ang, roundPic]

theorem angPerp_ofLp (t : ℝ) :
    (angPerp t).ofLp = ![-Real.sin (2 * Real.pi * t), Real.cos (2 * Real.pi * t), (0 : ℝ)] := by
  simp [angPerp, roundPic, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]

theorem ang_periodic (t : ℝ) : ang (t + 1) = ang t := by
  have h : 2 * Real.pi * (t + 1) = 2 * Real.pi + 2 * Real.pi * t := by ring
  show roundPic (2 * Real.pi * (t + 1)) = roundPic (2 * Real.pi * t)
  rw [h, roundPic_add]
  norm_num [Real.cos_two_pi, Real.sin_two_pi]

theorem angPerp_periodic (t : ℝ) : angPerp (t + 1) = angPerp t := by
  have h : 2 * Real.pi * (t + 1) + Real.pi / 2 =
      2 * Real.pi + (2 * Real.pi * t + Real.pi / 2) := by ring
  show roundPic (2 * Real.pi * (t + 1) + Real.pi / 2) =
    roundPic (2 * Real.pi * t + Real.pi / 2)
  rw [h, roundPic_add]
  norm_num [Real.cos_two_pi, Real.sin_two_pi]

theorem ang_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ang := by
  have h : ang = fun t : ℝ =>
      mkCLM (![Real.cos (2*Real.pi*t), Real.sin (2*Real.pi*t), (0:ℝ)] : Fin 3 → ℝ) := by
    funext t; simp [ang, roundPic_eq_mkCLM]
  rw [h]
  refine mkCLM.contDiff.comp ?_
  rw [contDiff_pi]
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem angPerp_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) angPerp := by
  have h : angPerp = fun t : ℝ =>
      mkCLM (![-Real.sin (2*Real.pi*t), Real.cos (2*Real.pi*t), (0:ℝ)] : Fin 3 → ℝ) := by
    funext t
    show roundPic (2 * Real.pi * t + Real.pi / 2) = _
    rw [roundPic_eq_mkCLM]
    congr 1
    funext i
    fin_cases i <;> simp [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  rw [h]
  refine mkCLM.contDiff.comp ?_
  rw [contDiff_pi]
  intro i
  fin_cases i <;> simp <;> fun_prop


/-! ## Extending a periodic function from a smoothly embedded circle -/

section Extend

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {f : M → ℝ} {b : ℝ} [LevelHyp f b]

/-- An integer translate of a `1`-periodic curve is the curve. -/
theorem periodic_int {X : Type*} {γ : ℝ → X} (hper : Function.Periodic γ 1) (k : ℤ) (x : ℝ) :
    γ (x + k) = γ x := by
  have h := hper.zsmul k
  rw [show (k : ℤ) • (1 : ℝ) = (k : ℝ) by simp] at h
  exact h x

/-- The fractional part of the parameter gives the same point of a `1`-periodic curve. -/
theorem periodic_fract {X : Type*} {γ : ℝ → X} (hper : Function.Periodic γ 1) (t : ℝ) :
    γ (Int.fract t) = γ t := by
  have h := periodic_int hper ⌊t⌋ (Int.fract t)
  rw [← h, Int.fract_add_floor]

/-- **A `1`-periodic curve injective on `[0,1)` is injective modulo the period.** -/
theorem sub_mem_int_of_eq {X : Type*} {γ : ℝ → X} (hper : Function.Periodic γ 1)
    (hinj : Set.InjOn γ (Set.Ico 0 1)) {s t : ℝ} (h : γ s = γ t) :
    ∃ k : ℤ, s - t = k := by
  have hs : γ (Int.fract s) = γ (Int.fract t) := by
    rw [periodic_fract hper s, h, periodic_fract hper t]
  have hf : Int.fract s = Int.fract t :=
    hinj ⟨Int.fract_nonneg s, Int.fract_lt_one s⟩
      ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩ hs
  have hs1 : s = Int.fract s + (⌊s⌋ : ℝ) := (Int.fract_add_floor s).symm
  have ht1 : t = Int.fract t + (⌊t⌋ : ℝ) := (Int.fract_add_floor t).symm
  have hst : s - t = (⌊s⌋ : ℝ) - (⌊t⌋ : ℝ) := by linarith
  refine ⟨⌊s⌋ - ⌊t⌋, ?_⟩
  push_cast
  linarith [hst]

/-- The range of a `1`-periodic curve is the image of `[0,1]`. -/
theorem range_periodic {X : Type*} {γ : ℝ → X} (hper : Function.Periodic γ 1) :
    Set.range γ = γ '' Set.Icc 0 1 := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Int.fract t, ⟨Int.fract_nonneg t, le_of_lt (Int.fract_lt_one t)⟩,
      periodic_fract hper t⟩
  · rintro ⟨t, _, rfl⟩
    exact ⟨t, rfl⟩

/-- The value at an integer translate for a `1`-periodic function. -/
theorem periodic_apply_eq {X : Type*} {A : ℝ → X} (hper : Function.Periodic A 1) {s t : ℝ}
    {k : ℤ} (hk : s = t + k) : A s = A t := by
  rw [hk, periodic_int hper k t]

/-- A nonzero continuous linear functional on `ℝ` is injective. -/
theorem injective_of_apply_one_ne_zero (L : ℝ →L[ℝ] ℝ) (h : L 1 ≠ 0) :
    Function.Injective L := by
  intro x y hxy
  have hsub : L (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hsmul : (x - y) • L 1 = 0 := by
    rw [← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]
    exact hsub
  rcases smul_eq_zero.mp hsmul with h' | h'
  · linarith
  · exact absurd h' h

/-- A continuous linear functional into a real vector space which is nonzero is nonzero at `1`. -/
theorem apply_one_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ →L[ℝ] E) (h : L ≠ 0) : L 1 ≠ 0 := by
  intro h1
  apply h
  refine ContinuousLinearMap.ext fun z => ?_
  calc L z = L (z • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
    _ = z • L 1 := ContinuousLinearMap.map_smul L z 1
    _ = 0 := by rw [h1, smul_zero]

/-- **A smooth periodic function of the circle extends smoothly to the surface.**  If `γ` is a
smooth `1`-periodic immersion of the circle which lies in the regular level set `f ⁻¹' {b}` and is
injective on `[0,1)`, then any smooth `1`-periodic `A` agrees on `γ '' ℝ` with a smooth function on
`M`. -/
theorem exists_contMDiff_extend_of_circle
    (γ : ℝ → M) (hγsm : ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) ∞ γ)
    (hγval : ∀ t, f (γ t) = b) (hγper : Function.Periodic γ 1)
    (hγinj : Set.InjOn γ (Set.Ico 0 1))
    (himm : ∀ t : ℝ, mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t 1 ≠ 0)
    (A : ℝ → EuclideanSpace ℝ (Fin 3)) (hA : ContDiff ℝ ∞ A) (hperA : Function.Periodic A 1) :
    ∃ G : M → EuclideanSpace ℝ (Fin 3),
      ContMDiff (𝓡 2) (𝓘(ℝ,EuclideanSpace ℝ (Fin 3))) ∞ G ∧ ∀ t, G (γ t) = A t := by
  classical
  -- the base point of the level set, the local graph model, and the retained coordinate
  let yp : ℝ → LevelSet f b := fun t => ⟨γ t, hγval t⟩
  let mdl : ∀ t, LevelModel f b (yp t) := fun t => mainModel f b (yp t)
  let co : ∀ t, M → ℝ := fun t x => coordOf f b (yp t) x
  -- the open set of parameters whose curve point lies in the chart neighbourhood of `γ t`
  let blk : ℝ → Set M := fun t => (chartAt E2 (γ t)).source ∩
    (chartAt E2 (γ t)) ⁻¹' (mdl t).V
  let Wr : ℝ → Set ℝ := fun t => γ ⁻¹' (blk t)
  -- the base point of the level set is the curve point
  have yp_coe : ∀ t, (yp t).1 = γ t := fun t => rfl
  have hch_eq : ∀ t, (chartAt E2 (yp t).1) = (chartAt E2 (γ t)) := fun t => rfl
  have hblk_mem : ∀ t, γ t ∈ blk t := by
    intro t
    refine ⟨mem_chart_source E2 (γ t), ?_⟩
    have h := (mdl t).mem_V _ (mdl t).base_mem_T
    rwa [(mdl t).base_eq] at h
  have hblk_open : ∀ t, IsOpen (blk t) := by
    intro t
    have hchart : ContinuousOn (fun x : M => (chartAt E2 (γ t)) x)
        (chartAt E2 (γ t)).source :=
      (contMDiffOn_chart (I := 𝓡 2) (n := ∞) (x := γ t)).continuousOn
    exact ContinuousOn.isOpen_inter_preimage hchart (chartAt E2 (γ t)).open_source
      ((mdl t).isOpen_V)
  have hWr_mem : ∀ t, t ∈ Wr t := fun t => hblk_mem t
  have hWr_open : ∀ t, IsOpen (Wr t) := fun t => (hblk_open t).preimage hγsm.continuous
  have hT_mem : ∀ t, co t (γ t) ∈ (mdl t).T := by
    intro t
    exact coordOf_mem_T f b (yp t) (mem_chart_source E2 (γ t)) (hblk_mem t).2 (hγval t)
  -- the coordinate function is continuous and smooth on the chart neighbourhood
  have hco_cont : ∀ t, ContinuousOn (fun x : M => co t x) (blk t) := by
    intro t
    have hchart : ContinuousOn (fun x : M => (chartAt E2 (γ t)) x) (blk t) :=
      (contMDiffOn_chart (I := 𝓡 2) (n := ∞) (x := γ t)).continuousOn.mono
        (fun x hx => hx.1)
    exact ((levelCoordProj (mdl t).i).continuous.comp_continuousOn hchart)
  have hco_smooth : ∀ t, ContDiffOn ℝ ∞ (fun s : ℝ => co t (γ s)) (Wr t) := by
    intro t
    have hchart : ContMDiffOn (𝓡 2) (𝓘(ℝ,E2)) ∞ (fun x : M => (chartAt E2 (γ t)) x)
        (chartAt E2 (γ t)).source := contMDiffOn_chart
    have h1 : ContMDiffOn 𝓘(ℝ,ℝ) (𝓘(ℝ,E2)) ∞
        (fun s : ℝ => (chartAt E2 (γ t)) (γ s)) (Wr t) :=
      hchart.comp hγsm.contMDiffOn (fun s hs => hs.1)
    have h2 : ContDiffOn ℝ ∞ (fun s : ℝ => (chartAt E2 (γ t)) (γ s)) (Wr t) :=
      contMDiffOn_iff_contDiffOn.mp h1
    have h3 : ContDiffOn ℝ ∞ (fun s : ℝ => levelCoordProj (mdl t).i ((chartAt E2 (γ t)) (γ s)))
        (Wr t) := (levelCoordProj (mdl t).i).contDiff.comp_contDiffOn h2
    have hfun : (fun s : ℝ => co t (γ s))
        = fun s : ℝ => levelCoordProj (mdl t).i ((chartAt E2 (γ t)) (γ s)) := by
      funext s
      simp only [co, coordOf, yp_coe, mdl]
    rw [hfun]
    exact h3
  -- the derivative of the coordinate function along the curve is nonzero
  have hderiv : ∀ t : ℝ, fderiv ℝ (fun s : ℝ => co t (γ s)) t 1 ≠ 0 := by
    intro t
    have hsrc : γ t ∈ (chartAt E2 (γ t)).source := mem_chart_source E2 (γ t)
    have hfun : (fun s : ℝ => co t (γ s))
        = fun s : ℝ => ((chartAt E2 (γ t)) (γ s)).ofLp (mdl t).i := by
      funext s
      simp only [co, coordOf, levelCoordProj_apply, yp_coe, mdl]
    rw [hfun]
    -- the chart representative of the curve is differentiable at `t`
    have hchartrep_at : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2)
        (fun s : ℝ => (chartAt E2 (γ t)) (γ s)) t := by
      have h1 : ContMDiffAt 𝓘(ℝ,ℝ) (𝓡 2) ∞
          (fun s : ℝ => (chartAt E2 (γ t)) (γ s)) t :=
        (contMDiffOn_chart (I := 𝓡 2) (n := ∞) (x := γ t)).contMDiffAt
          ((chartAt E2 (γ t)).open_source.mem_nhds hsrc) |>.comp t hγsm.contMDiffAt
      exact h1.mdifferentiableAt (by simp)
    -- the inverse of the chart is differentiable at the chart point
    have hsymm_at : MDifferentiableAt (𝓡 2) (𝓡 2) (chartAt E2 (γ t)).symm
        ((chartAt E2 (γ t)) (γ t)) := by
      have h1 : ContMDiffAt (𝓡 2) (𝓡 2) ∞ (chartAt E2 (γ t)).symm
          ((chartAt E2 (γ t)) (γ t)) :=
        ((contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := γ t))).contMDiffAt
          ((chartAt E2 (γ t)).open_target.mem_nhds ((chartAt E2 (γ t)).map_source hsrc))
      exact h1.mdifferentiableAt (by simp)
    -- the chart inverse undoes the chart along the curve
    have hcomp_chart : ((chartAt E2 (γ t)).symm ∘
        (fun s : ℝ => (chartAt E2 (γ t)) (γ s))) =ᶠ[𝓝 t] γ := by
      refine Filter.mem_of_superset
        (((chartAt E2 (γ t)).open_source.preimage hγsm.continuous).mem_nhds hsrc)
        (fun s hs => ?_)
      exact (chartAt E2 (γ t)).left_inv hs
    -- (A) the chart representative of the curve has nonzero derivative at `t`
    have hA : fderiv ℝ (fun s : ℝ => (chartAt E2 (γ t)) (γ s)) t 1 ≠ 0 := by
      intro h0
      have h0' : (mfderiv 𝓘(ℝ,ℝ) (𝓡 2)
          (fun s : ℝ => (chartAt E2 (γ t)) (γ s)) t) 1 = 0 := by
        rw [mfderiv_eq_fderiv]
        exact h0
      have hcr : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ t
          = (mfderiv (𝓡 2) (𝓡 2) (chartAt E2 (γ t)).symm
              ((chartAt E2 (γ t)) (γ t))).comp
            (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun s : ℝ => (chartAt E2 (γ t)) (γ s)) t) := by
        rw [← hcomp_chart.mfderiv_eq_v433]
        exact mfderiv_comp (f := fun s : ℝ => (chartAt E2 (γ t)) (γ s))
          (g := (chartAt E2 (γ t)).symm) t hsymm_at hchartrep_at
      have h1 : ((mfderiv (𝓡 2) (𝓡 2) (chartAt E2 (γ t)).symm
            ((chartAt E2 (γ t)) (γ t))).comp
          (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun s : ℝ => (chartAt E2 (γ t)) (γ s)) t)) 1 = 0 := by
        rw [ContinuousLinearMap.comp_apply, h0', ContinuousLinearMap.map_zero]
      exact himm t (hcr ▸ h1)
    -- (B) the chart representative of the curve is the graph over the retained coordinate
    have hceq : (fun s : ℝ => (chartAt E2 (γ t)) (γ s)) =ᶠ[𝓝 t]
        fun s : ℝ => (mdl t).η (((chartAt E2 (γ t)) (γ s)).ofLp (mdl t).i) := by
      refine Filter.mem_of_superset ((hWr_open t).mem_nhds (hWr_mem t)) (fun s hs => ?_)
      have hlev : f ((chartAt E2 (yp t).1).symm ((chartAt E2 (γ t)) (γ s))) = b := by
        rw [hch_eq t, (chartAt E2 (γ t)).left_inv hs.1]
        exact hγval s
      exact ((mdl t).graph ((chartAt E2 (γ t)) (γ s)) hs.2 hlev).symm
    -- (C) differentiate the graph relation
    have hU_eq : (fun s : ℝ => ((chartAt E2 (γ t)) (γ s)).ofLp (mdl t).i)
        = fun s : ℝ => levelCoordProj (mdl t).i ((chartAt E2 (γ t)) (γ s)) := by
      funext s
      rw [levelCoordProj_apply]
    have hU_diff : DifferentiableAt ℝ
        (fun s : ℝ => ((chartAt E2 (γ t)) (γ s)).ofLp (mdl t).i) t := by
      rw [hU_eq]
      exact DifferentiableAt.comp t ((levelCoordProj (mdl t).i).differentiableAt)
        hchartrep_at.differentiableAt
    have hTbase : ((chartAt E2 (γ t)) (γ t)).ofLp (mdl t).i ∈ (mdl t).T := by
      have h1 : co t (γ t) = ((chartAt E2 (γ t)) (γ t)).ofLp (mdl t).i := by
        simp only [co, coordOf, levelCoordProj_apply, yp_coe, mdl]
      rw [← h1]
      exact hT_mem t
    have heta_diff : DifferentiableAt ℝ (mdl t).η
        (((chartAt E2 (γ t)) (γ t)).ofLp (mdl t).i) :=
      ((mdl t).contDiffOn_η.contDiffAt
        ((mdl t).isOpen_T.mem_nhds hTbase)).differentiableAt (by simp)
    have hchain : fderiv ℝ (fun s : ℝ => (chartAt E2 (γ t)) (γ s)) t
        = (fderiv ℝ (mdl t).η (((chartAt E2 (γ t)) (γ t)).ofLp (mdl t).i)).comp
          (fderiv ℝ (fun s : ℝ => ((chartAt E2 (γ t)) (γ s)).ofLp (mdl t).i) t) := by
      rw [hceq.fderiv_eq]
      exact fderiv_comp (f := fun s : ℝ => ((chartAt E2 (γ t)) (γ s)).ofLp (mdl t).i) t
        heta_diff hU_diff
    have hval : fderiv ℝ (fun s : ℝ => (chartAt E2 (γ t)) (γ s)) t 1
        = ((fderiv ℝ (fun s : ℝ => ((chartAt E2 (γ t)) (γ s)).ofLp (mdl t).i) t) 1) •
          (fderiv ℝ (mdl t).η (((chartAt E2 (γ t)) (γ t)).ofLp (mdl t).i) 1) := by
      rw [hchain, ContinuousLinearMap.comp_apply]
      conv_lhs => rw [show
        (fderiv ℝ (fun s : ℝ => ((chartAt E2 (γ t)) (γ s)).ofLp (mdl t).i) t) 1
          = ((fderiv ℝ (fun s : ℝ => ((chartAt E2 (γ t)) (γ s)).ofLp (mdl t).i) t) 1)
              • (1 : ℝ) by simp]
      rw [ContinuousLinearMap.map_smul]
    have hne : fderiv ℝ (fun s : ℝ => ((chartAt E2 (γ t)) (γ s)).ofLp (mdl t).i) t 1
        ≠ 0 := by
      intro h0
      rw [hval, h0, zero_smul] at hA
      exact hA rfl
    exact hne
  -- the local inverse function theorem
  have hIFT : ∀ t : ℝ, ∃ (S V : Set ℝ) (sg : ℝ → ℝ), IsOpen S ∧ IsOpen V ∧ V ⊆ Wr t ∧
      (fun s : ℝ => co t (γ s)) t ∈ S ∧ t ∈ V ∧ ContDiffOn ℝ ∞ sg S ∧
      (∀ u ∈ S, sg u ∈ V) ∧ (∀ u ∈ S, (fun s : ℝ => co t (γ s)) (sg u) = u) ∧
      (∀ x ∈ V, sg ((fun s : ℝ => co t (γ s)) x) = x) := by
    intro t
    exact localInverseContDiffOnNhd (fun s : ℝ => co t (γ s)) (Wr t) (hWr_open t)
      (hco_smooth t) t (hWr_mem t) (injective_of_apply_one_ne_zero _ (hderiv t))
  choose S V sg hSopen hVopen hVsub hSmem hVmem hsg_smooth hsg_mem hsg_left hsg_right using hIFT
  -- the neighbourhoods and the local pieces
  let nb : ℝ → Set M := fun t => blk t ∩ (co t) ⁻¹' (S t)
  have hnb_open : ∀ t, IsOpen (nb t) := fun t =>
    (hco_cont t).isOpen_inter_preimage (hblk_open t) (hSopen t)
  have hnb_mem : ∀ t, γ t ∈ nb t := fun t => ⟨hblk_mem t, hSmem t⟩
  have hpiece : ∀ t, ContMDiffOn (𝓡 2) (𝓘(ℝ,EuclideanSpace ℝ (Fin 3))) ∞
      (fun x : M => A (sg t (co t x))) (nb t) := by
    intro t
    have hco : ContMDiffOn (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun x : M => co t x) (nb t) := by
      have hchart : ContMDiffOn (𝓡 2) (𝓘(ℝ,E2)) ∞ (fun x : M => (chartAt E2 (γ t)) x)
          (chartAt E2 (γ t)).source := contMDiffOn_chart
      have h2 : ContMDiffOn (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun x : M => levelCoordProj (mdl t).i
          ((chartAt E2 (γ t)) x)) (blk t) :=
        (ContMDiff.comp_contMDiffOn (levelCoordProj (mdl t).i).contMDiff hchart).mono
          (fun x hx => hx.1)
      have h3 : ContMDiffOn (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun x : M => levelCoordProj (mdl t).i
          ((chartAt E2 (γ t)) x)) (nb t) := h2.mono (fun x hx => hx.1)
      have hfun : (fun x : M => co t x)
          = fun x : M => levelCoordProj (mdl t).i ((chartAt E2 (γ t)) x) := by
        funext x
        simp only [co, coordOf, yp_coe, mdl]
      rw [hfun]
      exact h3
    have hsg : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (sg t) (S t) :=
      contMDiffOn_iff_contDiffOn.mpr (hsg_smooth t)
    have h1 : ContMDiffOn (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun x : M => sg t (co t x)) (nb t) :=
      hsg.comp hco (fun x hx => hx.2)
    have hA' : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,EuclideanSpace ℝ (Fin 3))) ∞ A :=
      contMDiff_iff_contDiff.mpr hA
    exact hA'.comp_contMDiffOn h1
  -- the partition of unity subordinate to the cover by the `nb t`
  have hclosed : IsClosed (Set.range γ) := by
    rw [range_periodic hγper]
    exact (isCompact_Icc.image hγsm.continuous).isClosed
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡 2) hclosed (fun t : ℝ => nb t)
    hnb_open (fun x hx => by
      obtain ⟨t, rfl⟩ := hx
      exact Set.mem_iUnion.mpr ⟨t, hnb_mem t⟩)
  refine ⟨fun x => ∑ᶠ t : ℝ, ρ t x • A (sg t (co t x)), ?_, ?_⟩
  · refine ρ.contMDiff_finsum_smul (n := ⊤) (g := fun t x => A (sg t (co t x))) ?_
    intro t x hx
    exact (hpiece t).contMDiffAt ((hnb_open t).mem_nhds (hρ t hx))
  · intro t₀
    change (∑ᶠ t : ℝ, ρ t (γ t₀) • A (sg t (co t (γ t₀)))) = A t₀
    have hkey : ∀ t : ℝ, ρ t (γ t₀) • A (sg t (co t (γ t₀))) = ρ t (γ t₀) • A t₀ := by
      intro t
      by_cases h0 : ρ t (γ t₀) = 0
      · rw [h0, zero_smul, zero_smul]
      · have hsupp : γ t₀ ∈ tsupport (ρ t) :=
          subset_closure (by rw [Function.mem_support]; exact h0)
        have hnb : γ t₀ ∈ nb t := hρ t hsupp
        have hS : co t (γ t₀) ∈ S t := hnb.2
        -- the parameter produced by the local inverse returns the same curve point
        have hfix : γ (sg t (co t (γ t₀))) = γ t₀ := by
          have hcoord : levelCoordProj (mdl t).i ((chartAt E2 (γ t)) (γ (sg t (co t (γ t₀)))))
              = levelCoordProj (mdl t).i ((chartAt E2 (γ t)) (γ t₀)) := hsg_left t _ hS
          have hsV : sg t (co t (γ t₀)) ∈ V t := hsg_mem t _ hS
          have hsWr : sg t (co t (γ t₀)) ∈ Wr t := hVsub t hsV
          have hsrc : γ (sg t (co t (γ t₀))) ∈ (chartAt E2 (γ t)).source := hsWr.1
          have hsrc0 : γ t₀ ∈ (chartAt E2 (γ t)).source := hnb.1.1
          have hV : (chartAt E2 (γ t)) (γ (sg t (co t (γ t₀)))) ∈ (mdl t).V := hsWr.2
          have hV0 : (chartAt E2 (γ t)) (γ t₀) ∈ (mdl t).V := hnb.1.2
          have hlev : f ((chartAt E2 (yp t).1).symm
              ((chartAt E2 (γ t)) (γ (sg t (co t (γ t₀)))))) = b := by
            rw [hch_eq t, (chartAt E2 (γ t)).left_inv hsrc]
            exact hγval _
          have hlev0 : f ((chartAt E2 (yp t).1).symm
              ((chartAt E2 (γ t)) (γ t₀))) = b := by
            rw [hch_eq t, (chartAt E2 (γ t)).left_inv hsrc0]
            exact hγval t₀
          have hchart_eq : (chartAt E2 (γ t)) (γ (sg t (co t (γ t₀)))) =
              (chartAt E2 (γ t)) (γ t₀) := by
            rw [← (mdl t).graph ((chartAt E2 (γ t)) (γ (sg t (co t (γ t₀))))) hV hlev,
              ← (mdl t).graph ((chartAt E2 (γ t)) (γ t₀)) hV0 hlev0,
              ← levelCoordProj_apply, ← levelCoordProj_apply, hcoord]
          exact (chartAt E2 (γ t)).injOn hsrc hsrc0 hchart_eq
        obtain ⟨k, hk⟩ := sub_mem_int_of_eq hγper hγinj hfix
        have hk' : sg t (co t (γ t₀)) = t₀ + k := by linarith [hk]
        rw [periodic_apply_eq hperA hk']
    rw [finsum_congr hkey, ← finsum_smul]
    rw [ρ.sum_eq_one (Set.mem_range_self t₀), one_smul]

end Extend
/-! ## The circle maps: the phase formula, the derivative, and the period -/

/-- **The phase formula for the round picture**: the picture at a shifted parameter is the
combination of the two angle functions with the sine and cosine of the shift. -/
theorem roundPic_phase (φ t : ℝ) :
    roundPic (φ + 2 * Real.pi * t) = Real.cos φ • ang t + Real.sin φ • angPerp t := by
  rw [roundPic_add]
  rfl

/-- The point of the `i`-th circle of a configuration at parameter `t` is the point of the round
circle centred at `pos i` with the two angle functions. -/
theorem circle_eq_ang_combo {m : ℕ} (D : RoundConfig m) (i : Fin m) (t : ℝ) :
    D.circle i t = D.pos i + D.rad i •
      (Real.cos (D.phase i) • ang t + Real.sin (D.phase i) • angPerp t) := by
  rw [RoundConfig.circle, roundPic_phase]

/-- **Two round-picture points coincide only for parameters differing by a multiple of `2π`.** -/
theorem roundPic_period {a b : ℝ} (h : roundPic a = roundPic b) :
    ∃ k : ℤ, b = a + k * (2 * Real.pi) := by
  have h0 : (roundPic a).ofLp = (roundPic b).ofLp := by rw [h]
  have hcos : Real.cos a = Real.cos b := by
    have h1 := congrArg (fun v : Fin 3 → ℝ => v 0) h0
    simpa [roundPic] using h1
  have hsin : Real.sin a = Real.sin b := by
    have h1 := congrArg (fun v : Fin 3 → ℝ => v 1) h0
    simpa [roundPic] using h1
  have hexp : Complex.exp (↑a * Complex.I) = Complex.exp (↑b * Complex.I) := by
    rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, hcos, hsin]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  refine ⟨-n, ?_⟩
  have h2 := congrArg Complex.im hn
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im] at h2
  norm_num at h2
  push_cast
  linarith [h2]

/-- **Two points of the same circle of a configuration coincide only for parameters differing by an
integer.** -/
theorem circle_eq_mod_one {m : ℕ} (D : RoundConfig m) (i : Fin m) {t u : ℝ}
    (h : D.circle i t = D.circle i u) : ∃ k : ℤ, t - u = k := by
  obtain ⟨h1, h2⟩ : D.pos i + D.rad i • roundPic (D.phase i + 2 * Real.pi * t) =
      D.pos i + D.rad i • roundPic (D.phase i + 2 * Real.pi * u) ∧ True := ⟨h, trivial⟩
  have h' : D.rad i • roundPic (D.phase i + 2 * Real.pi * t) =
      D.rad i • roundPic (D.phase i + 2 * Real.pi * u) := add_left_cancel h1
  have hsub : D.rad i • (roundPic (D.phase i + 2 * Real.pi * t) -
      roundPic (D.phase i + 2 * Real.pi * u)) = 0 := by
    rw [smul_sub, h', sub_self]
  have h2 : roundPic (D.phase i + 2 * Real.pi * t) =
      roundPic (D.phase i + 2 * Real.pi * u) :=
    sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_left (ne_of_gt (D.hrad i)))
  obtain ⟨k, hk⟩ := roundPic_period h2
  refine ⟨-k, ?_⟩
  have h3 : 2 * Real.pi * u = 2 * Real.pi * t + (k : ℝ) * (2 * Real.pi) := by linarith [hk]
  have h4 : u = t + (k : ℝ) := by
    have hp : (2 * Real.pi) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    have h5 : 2 * Real.pi * u = 2 * Real.pi * (t + (k : ℝ)) := by
      rw [mul_add]
      linarith [h3]
    exact mul_left_cancel₀ hp h5
  push_cast
  linarith [h4]

/-- The derivative of the affine parameter map `t ↦ φ + 2 π t`. -/
theorem hasFDerivAt_affine (φ x : ℝ) :
    HasFDerivAt (fun t : ℝ => φ + 2 * Real.pi * t)
      (ContinuousLinearMap.toSpanSingleton ℝ (2 * Real.pi)) x := by
  have h : HasDerivAt (fun t : ℝ => φ + 2 * Real.pi * t) (2 * Real.pi) x := by
    have h2 : HasDerivAt (fun t : ℝ => 2 * Real.pi * t) (2 * Real.pi) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * Real.pi)
    simpa using h2.const_add φ
  exact h.hasFDerivAt

/-- **The derivative of the round picture at `t` is `1 ↦ (-sin t, cos t, 0)`.** -/
theorem hasFDerivAt_roundPic (t : ℝ) :
    HasFDerivAt roundPic (ContinuousLinearMap.toSpanSingleton ℝ (picVel t)) t := by
  have hround : roundPic =
      fun u : ℝ => mkCLM (![Real.cos u, Real.sin u, (0 : ℝ)] : Fin 3 → ℝ) := by
    funext u; simp [roundPic_eq_mkCLM]
  have hw : HasFDerivAt (fun u : ℝ => ![Real.cos u, Real.sin u, (0 : ℝ)])
      (ContinuousLinearMap.pi fun i : Fin 3 =>
        ContinuousLinearMap.toSpanSingleton ℝ (![-Real.sin t, Real.cos t, (0 : ℝ)] i)) t := by
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    · simpa using (Real.hasDerivAt_cos t).hasFDerivAt
    · simpa using (Real.hasDerivAt_sin t).hasFDerivAt
    · exact hasFDerivAt_const (c := (0 : ℝ)) t
  have hceq : (mkCLM.comp (ContinuousLinearMap.pi fun i : Fin 3 =>
        ContinuousLinearMap.toSpanSingleton ℝ (![-Real.sin t, Real.cos t, (0 : ℝ)] i)))
      = ContinuousLinearMap.toSpanSingleton ℝ (picVel t) := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
    have h1 : (ContinuousLinearMap.pi fun i : Fin 3 =>
        ContinuousLinearMap.toSpanSingleton ℝ (![-Real.sin t, Real.cos t, (0 : ℝ)] i)) v
        = v • ![-Real.sin t, Real.cos t, (0 : ℝ)] := by
      funext i
      simp [ContinuousLinearMap.pi_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [h1, show picVel t = mkCLM ![-Real.sin t, Real.cos t, (0 : ℝ)] from rfl, map_smul]
  rw [hround, ← hceq]
  exact mkCLM.hasFDerivAt.comp t hw

/-- **The derivative of a circle of a configuration at parameter `x`.** -/
theorem hasFDerivAt_circle {m : ℕ} (D : RoundConfig m) (i : Fin m) (x : ℝ) :
    HasFDerivAt (fun t : ℝ => D.circle i t)
      (ContinuousLinearMap.toSpanSingleton ℝ
        ((D.rad i * (2 * Real.pi)) • picVel (D.phase i + 2 * Real.pi * x))) x := by
  have h2 : HasFDerivAt (fun t : ℝ => roundPic (D.phase i + 2 * Real.pi * t))
      ((ContinuousLinearMap.toSpanSingleton ℝ (picVel (D.phase i + 2 * Real.pi * x))).comp
        (ContinuousLinearMap.toSpanSingleton ℝ (2 * Real.pi))) x :=
    HasFDerivAt.comp (f := fun t : ℝ => D.phase i + 2 * Real.pi * t) (g := roundPic) x
      (hasFDerivAt_roundPic (D.phase i + 2 * Real.pi * x)) (hasFDerivAt_affine (D.phase i) x)
  have h3 : HasFDerivAt (fun t : ℝ => D.rad i • roundPic (D.phase i + 2 * Real.pi * t))
      (D.rad i • ((ContinuousLinearMap.toSpanSingleton ℝ
        (picVel (D.phase i + 2 * Real.pi * x))).comp
        (ContinuousLinearMap.toSpanSingleton ℝ (2 * Real.pi)))) x := h2.const_smul (D.rad i)
  have h4 : HasFDerivAt
      (fun t : ℝ => D.pos i + D.rad i • roundPic (D.phase i + 2 * Real.pi * t))
      (D.rad i • ((ContinuousLinearMap.toSpanSingleton ℝ
        (picVel (D.phase i + 2 * Real.pi * x))).comp
        (ContinuousLinearMap.toSpanSingleton ℝ (2 * Real.pi)))) x := h3.const_add (D.pos i)
  convert h4 using 1
  · funext t
    rfl
  · ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smul_apply, smul_smul]
    ring

/-- **The circle map of a configuration is immersive.** -/
theorem circle_deriv_ne_zero {m : ℕ} (D : RoundConfig m) (i : Fin m) (x : ℝ) :
    (fderiv ℝ (fun t : ℝ => D.circle i t) x) 1 ≠ 0 := by
  rw [(hasFDerivAt_circle D i x).fderiv, ContinuousLinearMap.toSpanSingleton_apply]
  intro h
  simp only [one_smul] at h
  exact picVel_ne_zero _ ((smul_eq_zero.mp h).resolve_left
    (mul_ne_zero (ne_of_gt (D.hrad i)) (mul_ne_zero two_ne_zero Real.pi_ne_zero)))

/-- A continuous linear map on `ℝ` vanishing at `1` is zero. -/
theorem eq_zero_of_apply_one_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ →L[ℝ] E) (h : L 1 = 0) : L = 0 := by
  refine ContinuousLinearMap.ext fun z => ?_
  rw [ContinuousLinearMap.zero_apply]
  calc L z = L (z • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
    _ = z • L 1 := ContinuousLinearMap.map_smul L z 1
    _ = 0 := by rw [h, smul_zero]

/-- A nonzero continuous linear map on `ℝ` is injective. -/
theorem injective_of_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ →L[ℝ] E) (h : L ≠ 0) : Function.Injective L := by
  intro x y hxy
  have h1 : L 1 ≠ 0 := apply_one_ne_zero L h
  have hsub : L (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h2 : (x - y) • L 1 = 0 := by
    rw [← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]
    exact hsub
  rcases smul_eq_zero.mp h2 with h' | h'
  · linarith
  · exact absurd h' h1

/-- **A nonzero linear functional on `ℝ²` has a nonzero kernel vector.** -/
theorem exists_ne_zero_ker (A : E2 →L[ℝ] ℝ) : ∃ v : E2, v ≠ 0 ∧ A v = 0 := by
  by_cases h : A (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = 0
  · refine ⟨EuclideanSpace.single (0 : Fin 2) (1 : ℝ), ?_, h⟩
    intro hz
    have h1 := congrArg (fun v : E2 => v.ofLp 0) hz
    simpa using h1
  · refine ⟨EuclideanSpace.single (1 : Fin 2) (1 : ℝ) -
      (A (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) /
        A (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) •
        EuclideanSpace.single (0 : Fin 2) (1 : ℝ), ?_, ?_⟩
    · intro hz
      have h1 := congrArg (fun v : E2 => v.ofLp 1) hz
      simp at h1
    · have h' : (A (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) /
          A (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) •
            A (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
          = A (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) := by
        rw [smul_eq_mul, div_mul_cancel₀ _ h]
      rw [map_sub, map_smul, h', sub_self]



end

theorem roundConfigPicture {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {b : ℝ} {n : ℕ} (γ : Fin n → ℝ → M)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x)
    (hγsm : ∀ i, ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (γ i))
    (hγval : ∀ (i : Fin n) (x : ℝ), f (γ i x) = b)
    (hγper : ∀ i x, γ i (x + 1) = γ i x)
    (hγinj : ∀ i, Set.InjOn (γ i) (Set.Ico 0 1))
    (hγlev : ∀ x : M, f x = b → ∃ (i : Fin n) (t : ℝ), x = γ i t)
    (hγdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i)) (Set.range (γ j)))
    (hγker : ∀ (i : Fin n) (x : ℝ) (v : TangentSpace (𝓡 2) (γ i x)),
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (γ i x) v = 0 →
        ∃ t : ℝ, mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ i) x t = v)
    {D : ℝ → Work.Drive.N2.RoundConfig n} (hD : ∀ s : ℝ, (D s).Disjoint)
    (hDpos : ∀ i : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (D s).pos i))
    (hDrad : ∀ i : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (D s).rad i))
    (hDph : ∀ i : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (D s).phase i)) :
    ∃ P : ℝ → M → EuclideanSpace ℝ (Fin 3),
      (∀ (s : ℝ) (i : Fin n) (x : ℝ), P s (γ i x) = (D s).circle i x) ∧
      (∀ (s : ℝ) (x y : M), (∃ (i : Fin n) (t : ℝ), x = γ i t) →
        (∃ (j : Fin n) (u : ℝ), y = γ j u) → P s x = P s y → x = y) ∧
      (∀ (s : ℝ) (x : M), (∃ (i : Fin n) (t : ℝ), x = γ i t) →
        ∀ v : TangentSpace (𝓡 2) x, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
          mfderiv (𝓡 2) (𝓡 3) (P s) x v = 0 → v = 0) ∧
      (∀ (s : ℝ) (x : M), (∃ (i : Fin n) (t : ℝ), x = γ i t) →
        ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × M => P p.1 p.2) (s, x)) := by  classical
  haveI hLV : LevelHyp f b := ⟨hf, hreg⟩
  -- each curve is an immersion at every parameter
  have himm : ∀ (i : Fin n) (t : ℝ), mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t 1 ≠ 0 := by
    intro i t h1
    obtain ⟨v, hvne, hv0⟩ :=
      exists_ne_zero_ker (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ i t))
    obtain ⟨s, hs⟩ := hγker i t v hv0
    have hsa : s • (1 : TangentSpace 𝓘(ℝ,ℝ) t) = s := by
      show s * 1 = s
      ring
    have hs0 : (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t) s = 0 := by
      conv_lhs => rw [← hsa, ContinuousLinearMap.map_smul]
      rw [h1, smul_zero]
    rw [hs] at hs0
    exact hvne hs0
  -- the two angle functions extend smoothly along each curve
  have hext : ∀ i : Fin n, ∃ (Va Vb : M → EuclideanSpace ℝ (Fin 3)),
      ContMDiff (𝓡 2) (𝓘(ℝ,EuclideanSpace ℝ (Fin 3))) ∞ Va ∧ (∀ t, Va (γ i t) = ang t) ∧
      ContMDiff (𝓡 2) (𝓘(ℝ,EuclideanSpace ℝ (Fin 3))) ∞ Vb ∧
        (∀ t, Vb (γ i t) = angPerp t) := by
    intro i
    obtain ⟨Va, h1, h2⟩ := exists_contMDiff_extend_of_circle (f := f) (b := b) (γ i) (hγsm i)
      (hγval i) (hγper i) (hγinj i) (himm i) ang ang_contDiff ang_periodic
    obtain ⟨Vb, h3, h4⟩ := exists_contMDiff_extend_of_circle (f := f) (b := b) (γ i) (hγsm i)
      (hγval i) (hγper i) (hγinj i) (himm i) angPerp angPerp_contDiff angPerp_periodic
    exact ⟨Va, Vb, h1, h2, h3, h4⟩
  choose Va Vb hVa_sm hVa_val hVb_sm hVb_val using hext
  -- a bump which is `1` on the `i`-th circle and `0` on all the others
  have hbump : ∀ i : Fin n, ∃ χ : M → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ χ ∧
      (∀ t, χ (γ i t) = 1) ∧ (∀ j, j ≠ i → ∀ t, χ (γ j t) = 0) := by
    intro i
    have hKi : IsCompact (Set.range (γ i)) := by
      rw [range_periodic (hγper i)]
      exact isCompact_Icc.image (hγsm i).continuous
    have hKo : IsCompact (⋃ j : {j : Fin n // j ≠ i}, Set.range (γ j.1)) := by
      refine isCompact_iUnion fun j => ?_
      rw [range_periodic (hγper j.1)]
      exact isCompact_Icc.image (hγsm j.1).continuous
    have hdisj : Disjoint (Set.range (γ i))
        (⋃ j : {j : Fin n // j ≠ i}, Set.range (γ j.1)) := by
      rw [Set.disjoint_iUnion_right]
      intro j
      exact hγdisj i j.1 (Ne.symm j.2)
    obtain ⟨U, W, hUo, hWo, hKU, hKW, hUW⟩ :=
      SeparatedNhds.of_isCompact_isCompact hKi hKo hdisj
    obtain ⟨χ, V, hχsm, hχsupp, hVopen, hKV, hχone, _⟩ :=
      exists_contMDiff_bump_tsupport hKi hUo hKU
    refine ⟨χ, hχsm, ?_, ?_⟩
    · intro t
      exact hχone _ (hKV ⟨t, rfl⟩)
    · intro j hj t
      by_contra hne
      have h1 : γ j t ∈ Function.support χ := by rwa [Function.mem_support]
      have h3 : γ j t ∈ U := hχsupp (subset_closure h1)
      have h4 : γ j t ∈ W := hKW (Set.mem_iUnion.mpr ⟨⟨j, hj⟩, ⟨t, rfl⟩⟩)
      exact Set.disjoint_left.mp hUW h3 h4
  choose χ hχsm hχone hχzero using hbump
  -- the picture
  let P : ℝ → M → EuclideanSpace ℝ (Fin 3) := fun s x => ∑ i : Fin n,
      χ i x • ((D s).pos i + (D s).rad i • (Real.cos ((D s).phase i) • Va i x
        + Real.sin ((D s).phase i) • Vb i x))
  have hP1 : ∀ (s : ℝ) (i : Fin n) (t : ℝ), P s (γ i t) = (D s).circle i t := by
    intro s i t
    show (∑ j : Fin n, χ j (γ i t) • ((D s).pos j + (D s).rad j •
        (Real.cos ((D s).phase j) • Va j (γ i t)
          + Real.sin ((D s).phase j) • Vb j (γ i t)))) = (D s).circle i t
    rw [Finset.sum_eq_single i]
    · rw [hχone i t, one_smul, hVa_val i t, hVb_val i t]
      exact (circle_eq_ang_combo (D s) i t).symm
    · intro j _ hj
      rw [hχzero j i (Ne.symm hj) t, zero_smul]
    · intro hmem
      exact absurd (Finset.mem_univ i) hmem
  have hPsm : ∀ s : ℝ, ContMDiff (𝓡 2) (𝓡 3) ∞ (P s) := by
    intro s
    rw [show P s = fun x : M => ∑ i : Fin n, χ i x •
        ((D s).pos i + (D s).rad i • (Real.cos ((D s).phase i) • Va i x
          + Real.sin ((D s).phase i) • Vb i x)) from rfl]
    refine ContMDiff.sum fun i _ => ?_
    have hpos : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun _ : M => (D s).pos i) := contMDiff_const
    have hrad : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun _ : M => (D s).rad i) := contMDiff_const
    have hcos : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun _ : M => Real.cos ((D s).phase i)) :=
      Real.contDiff_cos.contMDiff.comp contMDiff_const
    have hsin : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun _ : M => Real.sin ((D s).phase i)) :=
      Real.contDiff_sin.contMDiff.comp contMDiff_const
    exact (hχsm i).smul (hpos.add (hrad.smul ((hcos.smul (hVa_sm i)).add
      (hsin.smul (hVb_sm i)))))
  have hPsm2 : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 3) ∞ (fun p : ℝ × M => P p.1 p.2) := by
    rw [show (fun p : ℝ × M => P p.1 p.2) = fun p : ℝ × M => ∑ i : Fin n, χ i p.2 •
        ((D p.1).pos i + (D p.1).rad i • (Real.cos ((D p.1).phase i) • Va i p.2
          + Real.sin ((D p.1).phase i) • Vb i p.2)) from rfl]
    refine ContMDiff.sum fun i _ => ?_
    have hχi : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M => χ i p.2) :=
      (hχsm i).comp contMDiff_snd
    have hpos : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 3) ∞ (fun p : ℝ × M => (D p.1).pos i) :=
      (contMDiff_iff_contDiff.mpr (hDpos i)).comp contMDiff_fst
    have hrad : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M => (D p.1).rad i) :=
      (contMDiff_iff_contDiff.mpr (hDrad i)).comp contMDiff_fst
    have hph : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M => (D p.1).phase i) :=
      (contMDiff_iff_contDiff.mpr (hDph i)).comp contMDiff_fst
    have hcos : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × M => Real.cos ((D p.1).phase i)) :=
      Real.contDiff_cos.contMDiff.comp hph
    have hsin : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × M => Real.sin ((D p.1).phase i)) :=
      Real.contDiff_sin.contMDiff.comp hph
    have hVai : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 3) ∞ (fun p : ℝ × M => Va i p.2) :=
      (hVa_sm i).comp contMDiff_snd
    have hVbi : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 3) ∞ (fun p : ℝ × M => Vb i p.2) :=
      (hVb_sm i).comp contMDiff_snd
    exact hχi.smul (hpos.add (hrad.smul ((hcos.smul hVai).add (hsin.smul hVbi))))
  refine ⟨P, hP1, ?_, ?_, ?_⟩
  · -- injectivity on the level set
    intro s x y hx hy hxy
    obtain ⟨i, t, rfl⟩ := hx
    obtain ⟨j, u, rfl⟩ := hy
    rw [hP1 s i t, hP1 s j u] at hxy
    by_cases hij : i = j
    · subst hij
      obtain ⟨k, hk⟩ := circle_eq_mod_one (D s) i hxy
      have hku : u = t + ((-k : ℤ) : ℝ) := by push_cast; linarith [hk]
      rw [hku]
      exact (periodic_int (hγper i) (-k) t).symm
    · exact absurd hxy (hD s i j hij t u)
  · -- immersion on the level set
    intro s x hx v hv h0
    obtain ⟨i, t, rfl⟩ := hx
    obtain ⟨t', ht'⟩ := hγker i t v hv
    have hPdiff : MDifferentiableAt (𝓡 2) (𝓡 3) (P s) (γ i t) :=
      (hPsm s).contMDiffAt.mdifferentiableAt (by simp)
    have hγdiff : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t :=
      (hγsm i).contMDiffAt.mdifferentiableAt (by simp)
    have hfun : ((P s) ∘ (γ i)) = fun u : ℝ => (D s).circle i u := by
      funext u
      exact hP1 s i u
    have hcomp : mfderiv 𝓘(ℝ,ℝ) (𝓡 3) ((P s) ∘ (γ i)) t t'
        = mfderiv (𝓡 2) (𝓡 3) (P s) (γ i t)
            (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t t') := by
      rw [mfderiv_comp (x := t) (f := γ i) (g := P s) hPdiff hγdiff]
      rfl
    have hcirc : mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (fun u : ℝ => (D s).circle i u) t t' = 0 := by
      have h1 : mfderiv (𝓡 2) (𝓡 3) (P s) (γ i t) v = 0 := h0
      rw [← ht'] at h1
      rw [← hcomp, hfun] at h1
      exact h1
    have hne : (mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (fun u : ℝ => (D s).circle i u) t) 1 ≠ 0 := by
      intro hzero
      have h1 : (mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (fun u : ℝ => (D s).circle i u) t :
          ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3)) 1 = 0 := hzero
      rw [mfderiv_eq_fderiv] at h1
      exact circle_deriv_ne_zero (D s) i t h1
    have hta : t' • (1 : TangentSpace 𝓘(ℝ,ℝ) t) = t' := by
      show t' * 1 = t'
      ring
    have hsmul : t' • ((mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (fun u : ℝ => (D s).circle i u) t) 1) = 0 := by
      conv_lhs => rw [← ContinuousLinearMap.map_smul, hta]
      rw [hcirc]
    have hzero : t' = 0 := by
      rcases smul_eq_zero.mp hsmul with h' | h'
      · exact h'
      · exact absurd h' hne
    have hv0 : v = 0 := by
      have hlin : (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t) t'
          = t' • ((mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (γ i) t) 1) := by
        have hta2 : t' • (1 : TangentSpace 𝓘(ℝ,ℝ) t) = t' := by
          show t' * 1 = t'
          ring
        conv_lhs => rw [← hta2, ContinuousLinearMap.map_smul]
      rw [hlin, hzero, zero_smul] at ht'
      exact ht'.symm
    exact hv0
  · -- joint smoothness at the points of the level set
    intro s x hx
    exact hPsm2.contMDiffAt



end Work.Drive.N2
