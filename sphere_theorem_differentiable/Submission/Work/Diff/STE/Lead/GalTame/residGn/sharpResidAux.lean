import Mathlib
import Submission.Work.Diff.STE.Lead.GalTame.residGn.BoxDefs
import Submission.Work.Diff.STE.Lead.GalTame.residGn.assemblyAux
import Submission.Work.Diff.STE.Lead.GalTame.residGn.compEnergy
import Submission.Work.Diff.STE.Lead.GalTame.residPerEnergy
import Submission.Work.Diff.STE.Lead.GalTame.residMatEnergy
import Submission.Work.Diff.STE.Lead.GalTame.residCubeSplit
import Submission.Work.Diff.STE.Lead.GalTame.Level
import Submission.Work.Diff.STE.Lead.GalTame.residIdent
import Submission.Work.Diff.STE.Lead.GalTame.residInnerBasic
import Submission.Work.Diff.STE.Lead.GalTame.residInnerEnergy
import Submission.Work.Diff.STE.Lead.GalTame.residGraphJet
import Submission.Work.Diff.STE.B3.tmGamma_uniform
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.B3.integral_unitCube_eq_centreCube
import Submission.Work.Diff.STE.continuous_pdVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set MeasureTheory Filter

namespace Work.Diff.STE.Lead.GalTame.ResidGn

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

local notation "Idx" => Fin (Module.finrank ℝ E)
local notation "St" => (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ)

/-- **The per-chart, per-level sharp energy bound of the local residual of the DeTurck
transport.** -/
theorem residStep
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (hLC : Submission.Diff.LCSmooth I M)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K) :
    ∃ C : ι₀ → ℕ → ℝ, (∀ j m, 0 ≤ C j m) ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
        (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
        (hjet : ∀ (i : ι₀) (c d r : Idx) (z : Idx → ℝ), ‖z‖ ≤ 2 * D.σ i →
          |Work.Diff.STE.pdR r (D.mat i h c d) z| ≤ K)
        (j : ι₀) (a b : Idx) (m : ℕ) (β : Fin m → Idx),
        ∫ z in Metric.ball (0 : Idx → ℝ) (D.σ j),
          ‖Work.Diff.STE.pdVec m β
            (fun z : Idx → ℝ =>
              ((Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b : ℝ) : ℂ)) z‖ ^ 2
          ≤ C j m * (1 + D.ENormB (m + 1) h) := by
  classical
  -- ## 0. The uniform determinant window
  obtain ⟨δ, mlo, Mhi, cw, Kr, Kr₁, cl, ch, hδpos, hmlopos, hMhipos, hcwpos, hKr0, hKr10,
    hcl, hch, hwin⟩ := Work.Diff.STE.B3.tmGamma_uniform (I := I) (M := M) D lam K hlam hK
  -- ## 1. The separators and the constants
  choose zeta hzsm hz1 hzsupp using fun j : ι₀ =>
    Work.Diff.STE.B3.tms_exists_zeta (I := I) (M := M) D j
  choose Bj hBj0 hBj using fun j : ι₀ =>
    residInnerBasic (I := I) (M := M) D j lam K hlam hK
  choose Dj hDj0 hDj using fun j : ι₀ =>
    residGraphJet (I := I) (M := M) D j cl ch hcl hch (zeta j) (hzsm j) (hzsupp j) (Bj j) (hBj0 j)
  choose Cj hCj0 hCj using fun (j : ι₀) (m : ℕ) => residInnerEnergy (I := I) (M := M) D j m
  choose CE hCE0 hCE using fun (j : ι₀) (m : ℕ) =>
    compositeGnR (Module.finrank ℝ E) m (Dj j m) (Bj j) (hDj0 j m) (hBj0 j)
  refine ⟨fun j m => (2 : ℝ) ^ (Module.finrank ℝ E) * CE j m * (1 + 2 * Cj j m), ?_, ?_⟩
  · intro j m
    have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ (Module.finrank ℝ E) := by positivity
    have h2 : 0 ≤ CE j m := hCE0 j m
    have h3 : 0 ≤ 1 + 2 * Cj j m := by linarith [hCj0 j m]
    positivity
  · intro h hsym hpos hsmooth hell hub hjet j a b m β
    -- ## 2. The data supplied by the four auxiliary lemmas
    have hinner := hBj j h hsym hsmooth hell hub hjet
    have hMsm : ∀ p q : Idx, ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
        (fun z : Idx → ℝ => Mper (I := I) (M := M) D h j z p q) := hinner.1
    have hNsm : ∀ p q r : Idx, ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
        (fun z : Idx → ℝ => Nper (I := I) (M := M) D h j z p q r) := hinner.2.1
    have hMPer : ∀ p q : Idx, Work.Diff.STE.Periodic1
        (fun z : Idx → ℝ => Mper (I := I) (M := M) D h j z p q) := hinner.2.2.1
    have hNPer : ∀ p q r : Idx, Work.Diff.STE.Periodic1
        (fun z : Idx → ℝ => Nper (I := I) (M := M) D h j z p q r) := hinner.2.2.2.1
    have hMb : ∀ z : Idx → ℝ, ∀ p q : Idx,
        |Mper (I := I) (M := M) D h j z p q| ≤ Bj j := hinner.2.2.2.2.1
    have hNb : ∀ z : Idx → ℝ, ∀ p q r : Idx,
        |Nper (I := I) (M := M) D h j z p q r| ≤ Bj j := hinner.2.2.2.2.2.1
    have hIdM : ∀ z : Idx → ℝ, ‖z‖ < D.σ j → ∀ p q : Idx,
        Mper (I := I) (M := M) D h j z p q = D.mat j h p q z := hinner.2.2.2.2.2.2.1
    have hIdN : ∀ z : Idx → ℝ, ‖z‖ < D.σ j → ∀ p q r : Idx,
        Nper (I := I) (M := M) D h j z p q r = Work.Diff.STE.pdR r (D.mat j h p q) z :=
      hinner.2.2.2.2.2.2.2
    have hEB : 0 ≤ D.ENormB (m + 1) h :=
      Work.Diff.STE.B3Data.ENormB_nonneg D (m + 1) h
        (fun i a b => ENormSq_nonnegR (m + 1) (D.Rper i h a b))
    have hwinj : ∀ z : Idx → ℝ, ‖z‖ ≤ 2 * D.σ j →
        cl ≤ (Matrix.of (fun i k : Idx =>
          Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k)).det ∧
        (Matrix.of (fun i k : Idx =>
          Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k)).det ≤ ch :=
      fun z hz => (hwin h hsym hpos hsmooth hell hub hjet j z
        (le_trans hz (by linarith [hδpos]))).2.2.1
    -- ## 3. The outer function and its smoothness
    have hζsm' : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
        (boxZeta (I := I) (M := M) D j (zeta j)) :=
      boxZeta_contDiff (I := I) (M := M) D j (hzsm j)
    have hζsupp' : tsupport (boxZeta (I := I) (M := M) D j (zeta j))
        ⊆ Work.Diff.STE.B3.tmsGood (I := I) (M := M) D j :=
      fun z hz => hzsupp j (boxZeta_tsupport_subset_tsupport (I := I) (M := M) D j (zeta j) hz)
    set Phi : St → ℝ := fun w =>
      boxPhi (I := I) (M := M) D j cl ch hcl hch (zeta j) w a b with hPhidef
    have hPhism : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) Phi := by
      rw [hPhidef]
      have hpsi : ∀ a' b' : Idx, ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
          (fun w : St => Work.Diff.STE.B3.tmPsi (I := I) (M := M) D j cl ch hcl hch
            w.1 w.2.1 w.2.2 a' b')
          (Work.Diff.STE.B3.tmsDom (I := I) (M := M) D j) :=
        fun a' b' => Work.Diff.STE.B3.tmPsi_state_contDiffOn D j cl ch hcl hch a' b'
      have hmain := Work.Diff.STE.B3.tmsPhi_smooth (I := I) (M := M) D j cl ch hcl hch
        (boxZeta (I := I) (M := M) D j (zeta j)) hζsm' hζsupp' hpsi
      exact Work.Diff.STE.B3.tms_contDiff_proj hmain a b
    -- ## 4. The identification of the outer function with the residual on the ball
    have hidfun : ∀ z : Idx → ℝ, ‖z‖ < D.σ j →
        boxPhi (I := I) (M := M) D j cl ch hcl hch (zeta j)
          (z, Mper (I := I) (M := M) D h j z, Nper (I := I) (M := M) D h j z) a b
          = Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b := by
      intro z hz
      have hz2 : ‖z‖ ≤ 2 * D.σ j := le_of_lt (lt_of_lt_of_le hz (by linarith [D.hσ j]))
      have hMz : Mper (I := I) (M := M) D h j z = Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z := by
        funext p q
        exact hIdM z hz p q
      have hNz : Nper (I := I) (M := M) D h j z
          = fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z := by
        funext p q r
        exact hIdN z hz p q r
      have hζ1 : ∀ z : Idx → ℝ, ‖z‖ ≤ 2 * D.σ j →
          boxZeta (I := I) (M := M) D j (zeta j) z = 1 :=
        fun z hz => boxZeta_one (I := I) (M := M) D j (hz1 j) hz
      have htgt : ∀ z : Idx → ℝ, ‖z‖ ≤ 2 * D.σ j →
          Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target :=
        fun z hz => D.htarget j z hz
      have hreg : ∀ z : Idx → ℝ, ‖z‖ ≤ 2 * D.σ j →
          (Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j z)).det ≠ 0 :=
        fun z hz => Work.Diff.STE.B3.det_Ff_ne_zero (I := I) (M := M) D j hz
      have hid1 := Work.Diff.STE.B3.tmsPhi_identity (I := I) (M := M) D j cl ch hcl hch
        (boxZeta (I := I) (M := M) D j (zeta j)) hζ1 (2 * D.σ j) le_rfl htgt hreg h hwinj z hz2 a b
      have hid2 := residIdent (I := I) (M := M) D hLC h hsym hpos hsmooth j cl ch hcl hch
        hwinj z hz2 a b
      have harg : (z, Mper (I := I) (M := M) D h j z, Nper (I := I) (M := M) D h j z)
          = (z, Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z,
              fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z) :=
        Prod.ext rfl (Prod.ext hMz hNz)
      rw [harg]
      exact hid1.trans hid2
    -- ## 5. The functions `G` and the residual function
    set Mf : (Idx → ℝ) → Idx → Idx → ℝ := fun z => Mper (I := I) (M := M) D h j z with hMfdef
    set Nf : (Idx → ℝ) → Idx → Idx → Idx → ℝ :=
      fun z => Nper (I := I) (M := M) D h j z with hNfdef
    set G : (Idx → ℝ) → ℂ := fun z => ((Phi (z, Mf z, Nf z) : ℝ) : ℂ) with hGdef
    set Hres : (Idx → ℝ) → ℂ := fun z =>
      ((Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b : ℝ) : ℂ) with hHresdef
    have hVsm : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
        (fun z : Idx → ℝ => (z, Mf z, Nf z)) := by
      refine ContDiff.prodMk contDiff_id ?_
      refine ContDiff.prodMk ?_ ?_
      · exact contDiff_pi.mpr fun p => contDiff_pi.mpr fun q => hMsm p q
      · exact contDiff_pi.mpr fun p => contDiff_pi.mpr fun q =>
          contDiff_pi.mpr fun r => hNsm p q r
    have hGsm : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) G := by
      have h1 : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
          (fun z : Idx → ℝ => Phi (z, Mf z, Nf z)) := hPhism.comp hVsm
      have h2 := Complex.ofRealCLM.contDiff.comp h1
      rw [hGdef]
      simpa [Function.comp_def, Complex.ofRealCLM_apply] using h2
    -- ## 6. The residual agrees with the outer function on the ball
    have hkey : ∀ z : Idx → ℝ, Phi (z, Mf z, Nf z)
        = boxPhi (I := I) (M := M) D j cl ch hcl hch (zeta j)
            (z, Mper (I := I) (M := M) D h j z, Nper (I := I) (M := M) D h j z) a b := by
      intro z
      simp only [hPhidef, hMfdef, hNfdef]
    have hcongr : ∀ z ∈ Metric.ball (0 : Idx → ℝ) (D.σ j), Hres z = G z := by
      intro z hz
      rw [Metric.mem_ball, dist_zero_right] at hz
      have hid := hidfun z hz
      rw [hHresdef, hGdef]
      show ((Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b : ℝ) : ℂ)
          = ((Phi (z, Mf z, Nf z) : ℝ) : ℂ)
      rw [hkey z, hid]
    have hstep1 : ∫ z in Metric.ball (0 : Idx → ℝ) (D.σ j),
          ‖Work.Diff.STE.pdVec m β Hres z‖ ^ 2
        = ∫ z in Metric.ball (0 : Idx → ℝ) (D.σ j),
          ‖Work.Diff.STE.pdVec m β G z‖ ^ 2 := by
      refine MeasureTheory.setIntegral_congr_fun Metric.isOpen_ball.measurableSet ?_
      intro z hz
      show ‖Work.Diff.STE.pdVec m β Hres z‖ ^ 2 = ‖Work.Diff.STE.pdVec m β G z‖ ^ 2
      have hAB : Work.Diff.STE.pdVec m β Hres z = Work.Diff.STE.pdVec m β G z :=
        pdVec_congr_open β Metric.isOpen_ball (fun y hy => hcongr y hy) hz
      rw [hAB]
    -- ## 7. The integral comparison over the centred cube
    have hcontG : Continuous (fun z : Idx → ℝ => ‖Work.Diff.STE.pdVec m β G z‖ ^ 2) :=
      ((Work.Diff.STE.continuous_pdVec m β G
        (hGsm.of_le (WithTop.coe_le_coe.mpr le_top))).norm).pow 2
    have hsub : Metric.ball (0 : Idx → ℝ) (D.σ j) ⊆ cubeC Idx := by
      intro z hz
      rw [Metric.mem_ball, dist_zero_right] at hz
      rw [cubeC]
      intro i _
      have hi : |z i| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm z i
      have h4 : 2 * D.σ j ≤ 1 / 4 := D.hσ2 j
      have hlt : |z i| < (1 : ℝ) / 2 := by linarith
      exact ⟨(abs_lt.mp hlt).1, le_of_lt (abs_lt.mp hlt).2⟩
    have hGz : ∀ z : Idx → ℝ, boxZeta (I := I) (M := M) D j (zeta j) z = 0 → G z = 0 := by
      intro z hz0
      have h1 : ((boxPhi (I := I) (M := M) D j cl ch hcl hch (zeta j)
          (z, Mper (I := I) (M := M) D h j z, Nper (I := I) (M := M) D h j z) a b : ℝ) : ℂ)
          = 0 := by
        rw [boxPhi_eq_zero_of_boxZeta_eq_zero (I := I) (M := M) D j cl ch hcl hch (zeta j) hz0
          (Mper (I := I) (M := M) D h j z) (Nper (I := I) (M := M) D h j z) a b]
        simp
      simpa [hGdef, hPhidef, hMfdef, hNfdef] using h1
    have hGk : tsupport G ⊆ Metric.closedBall (0 : Idx → ℝ) (3 * D.σ j) := by
      refine (closure_mono ?_).trans (boxZeta_tsupport_subset (I := I) (M := M) D j (zeta j))
      intro z hz
      rw [Function.mem_support] at hz ⊢
      intro h0
      exact hz (hGz z h0)
    have hcsup : HasCompactSupport (fun z : Idx → ℝ => ‖Work.Diff.STE.pdVec m β G z‖ ^ 2) := by
      refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Idx → ℝ) (3 * D.σ j))
        (isClosed_tsupport _) ?_
      have h2 : Function.support (Work.Diff.STE.pdVec m β G)
          ⊆ closure (Function.support G) :=
        Work.Diff.STE.csqp_support_pdList_subset_closure (List.ofFn β) G
      calc tsupport (fun z : Idx → ℝ => ‖Work.Diff.STE.pdVec m β G z‖ ^ 2)
          = closure (Function.support (fun z : Idx → ℝ => ‖Work.Diff.STE.pdVec m β G z‖ ^ 2)) := rfl
        _ ⊆ closure (Function.support (Work.Diff.STE.pdVec m β G)) := by
            refine closure_mono ?_
            intro z hz
            rw [Function.mem_support] at hz ⊢
            intro h0
            exact hz (by rw [h0]; simp)
        _ ⊆ closure (closure (Function.support G)) := closure_mono h2
        _ = closure (Function.support G) := closure_closure
        _ = tsupport G := rfl
        _ ⊆ Metric.closedBall (0 : Idx → ℝ) (3 * D.σ j) := hGk
    have hint2 : IntegrableOn (fun z : Idx → ℝ => ‖Work.Diff.STE.pdVec m β G z‖ ^ 2)
        (cubeC Idx) := (hcontG.integrable_of_hasCompactSupport hcsup).integrableOn
    have hstep2 : ∫ z in Metric.ball (0 : Idx → ℝ) (D.σ j),
          ‖Work.Diff.STE.pdVec m β G z‖ ^ 2
        ≤ ∫ z in cubeC Idx, ‖Work.Diff.STE.pdVec m β G z‖ ^ 2 :=
      MeasureTheory.setIntegral_mono_set hint2
        (Filter.Eventually.of_forall fun z => sq_nonneg _)
        (Filter.Eventually.of_forall hsub)
    have hstep3 : ∫ z in cubeC Idx, ‖Work.Diff.STE.pdVec m β G z‖ ^ 2
        ≤ ∑ ε : Idx → Fin 2,
            ∫ z in Work.Diff.STE.unitCube (ι := Idx),
              ‖Work.Diff.STE.pdVec m β G (z + fun i => (ε i : ℝ) - 1)‖ ^ 2 :=
      residCubeSplit (n := Module.finrank ℝ E)
        (fun z : Idx → ℝ => ‖Work.Diff.STE.pdVec m β G z‖ ^ 2) hcontG
        (fun z => sq_nonneg _)
    -- ## 8. The engine, applied to each of the `2^n` shifts
    have hterm : ∀ ε : Idx → Fin 2,
        ∫ z in Work.Diff.STE.unitCube (ι := Idx),
            ‖Work.Diff.STE.pdVec m β G (z + fun i => (ε i : ℝ) - 1)‖ ^ 2
          ≤ CE j m * (1
              + (∑ p : Idx, ∑ q : Idx,
                  Work.Diff.STE.ENormSq m (fun z : Idx → ℝ => ((Mf z p q : ℝ) : ℂ)))
              + (∑ p : Idx, ∑ q : Idx, ∑ r : Idx,
                  Work.Diff.STE.ENormSq m (fun z : Idx → ℝ => ((Nf z p q r : ℝ) : ℂ)))) := by
      intro ε
      set v : Idx → ℝ := fun i => (ε i : ℝ) - 1 with hvdef
      set kk : Idx → ℤ := fun i => (ε i : ℤ) - 1 with hkdef
      have hveq : (fun i : Idx => (kk i : ℝ)) = v := by
        funext i
        simp only [hvdef, hkdef]
        push_cast
        ring
      have hperMf : ∀ z : Idx → ℝ, Mf (z + v) = Mf z := by
        intro z
        funext p q
        have hh := Work.Diff.STE.B3.Periodic1.add_intVec (hMPer p q) kk z
        rw [hveq, add_comm] at hh
        exact hh
      have hperNf : ∀ z : Idx → ℝ, Nf (z + v) = Nf z := by
        intro z
        funext p q r
        have hh := Work.Diff.STE.B3.Periodic1.add_intVec (hNPer p q r) kk z
        rw [hveq, add_comm] at hh
        exact hh
      set e : St := (v, 0, 0) with hedef
      set Phie : St → ℝ := fun w => Phi (w + e) with hPhiedef
      have hPhie_cont : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) Phie := by
        rw [hPhiedef]
        exact hPhism.comp (contDiff_id.add contDiff_const)
      have hPhie_jet : ∀ (k' : ℕ), k' ≤ m → ∀ z : Idx → ℝ,
          ‖iteratedFDeriv ℝ k' Phie (z, Mf z, Nf z)‖ ≤ Dj j m := by
        intro k' hk' z
        have h1 : iteratedFDeriv ℝ k' Phie (z, Mf z, Nf z)
            = iteratedFDeriv ℝ k' Phi ((z, Mf z, Nf z) + e) := by
          rw [hPhiedef]
          exact iteratedFDeriv_comp_add_right k' e (z, Mf z, Nf z)
        rw [h1]
        have h2 : (z, Mf z, Nf z) + e = (z + v, Mf z, Nf z) := by
          rw [hedef]
          simp only [Prod.mk_add_mk, add_zero]
        rw [h2]
        exact hDj j m k' hk' (z + v) (Mf z) (Nf z) a b
          (fun p q => hMb z p q) (fun p q r => hNb z p q r)
      have hengine := hCE j m Phie Mf Nf β hPhie_cont hMsm hNsm hMPer hNPer hMb hNb hPhie_jet
      have hFeq : (fun z : Idx → ℝ => G (z + v))
          = fun z : Idx → ℝ => ((Phie (z, Mf z, Nf z) : ℝ) : ℂ) := by
        funext z
        rw [hGdef]
        show ((Phi (z + v, Mf (z + v), Nf (z + v)) : ℝ) : ℂ)
            = ((Phie (z, Mf z, Nf z) : ℝ) : ℂ)
        rw [hperMf z, hperNf z]
        simp only [hPhiedef]
        rw [hedef]
        simp only [Prod.mk_add_mk, add_zero]
      have hint_eq : ∫ z in Work.Diff.STE.unitCube (ι := Idx),
            ‖Work.Diff.STE.pdVec m β G (z + v)‖ ^ 2
          = Work.Diff.STE.ENormSq 0
              (Work.Diff.STE.pdVec m β (fun z : Idx → ℝ => ((Phie (z, Mf z, Nf z) : ℝ) : ℂ))) := by
        rw [ENormSq_zero_unitCube]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        show ‖Work.Diff.STE.pdVec m β G (z + v)‖ ^ 2
            = ‖Work.Diff.STE.pdVec m β
                (fun y : Idx → ℝ => ((Phie (y, Mf y, Nf y) : ℝ) : ℂ)) z‖ ^ 2
        have hvv : Work.Diff.STE.pdVec m β G (z + v)
            = Work.Diff.STE.pdVec m β
                (fun y : Idx → ℝ => ((Phie (y, Mf y, Nf y) : ℝ) : ℂ)) z := by
          rw [← congrFun (pdVec_comp_add_right β hGsm v) z, hFeq]
        rw [hvv]
      calc ∫ z in Work.Diff.STE.unitCube (ι := Idx),
            ‖Work.Diff.STE.pdVec m β G (z + v)‖ ^ 2
          = Work.Diff.STE.ENormSq 0
              (Work.Diff.STE.pdVec m β (fun z : Idx → ℝ => ((Phie (z, Mf z, Nf z) : ℝ) : ℂ))) :=
            hint_eq
        _ ≤ CE j m * (1
              + (∑ p : Idx, ∑ q : Idx,
                  Work.Diff.STE.ENormSq m (fun z : Idx → ℝ => ((Mf z p q : ℝ) : ℂ)))
              + (∑ p : Idx, ∑ q : Idx, ∑ r : Idx,
                  Work.Diff.STE.ENormSq m (fun z : Idx → ℝ => ((Nf z p q r : ℝ) : ℂ)))) :=
            hengine
    -- ## 9. The energy inputs
    have hCj1 : (∑ p : Idx, ∑ q : Idx,
          Work.Diff.STE.ENormSq m (fun z : Idx → ℝ => ((Mf z p q : ℝ) : ℂ)))
        ≤ Cj j m * (1 + D.ENormB (m + 1) h) := (hCj j m h hsmooth).1
    have hCj2 : (∑ p : Idx, ∑ q : Idx, ∑ r : Idx,
          Work.Diff.STE.ENormSq m (fun z : Idx → ℝ => ((Nf z p q r : ℝ) : ℂ)))
        ≤ Cj j m * (1 + D.ENormB (m + 1) h) := (hCj j m h hsmooth).2
    have hone : 1
          + (∑ p : Idx, ∑ q : Idx,
              Work.Diff.STE.ENormSq m (fun z : Idx → ℝ => ((Mf z p q : ℝ) : ℂ)))
          + (∑ p : Idx, ∑ q : Idx, ∑ r : Idx,
              Work.Diff.STE.ENormSq m (fun z : Idx → ℝ => ((Nf z p q r : ℝ) : ℂ)))
        ≤ (1 + 2 * Cj j m) * (1 + D.ENormB (m + 1) h) := by
      have h1 := hCj1
      have h2 := hCj2
      have h3 := hEB
      have h4 := hCj0 j m
      nlinarith [h1, h2, h3, h4]
    -- ## 10. The final chain
    have hcard : (Fintype.card (Idx → Fin 2) : ℝ) = (2 : ℝ) ^ (Module.finrank ℝ E) := by
      rw [Fintype.card_fun]
      simp
    calc ∫ z in Metric.ball (0 : Idx → ℝ) (D.σ j),
          ‖Work.Diff.STE.pdVec m β
            (fun z : Idx → ℝ =>
              ((Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b : ℝ) : ℂ)) z‖ ^ 2
        = ∫ z in Metric.ball (0 : Idx → ℝ) (D.σ j),
            ‖Work.Diff.STE.pdVec m β Hres z‖ ^ 2 := rfl
      _ = ∫ z in Metric.ball (0 : Idx → ℝ) (D.σ j),
            ‖Work.Diff.STE.pdVec m β G z‖ ^ 2 := hstep1
      _ ≤ ∫ z in cubeC Idx, ‖Work.Diff.STE.pdVec m β G z‖ ^ 2 := hstep2
      _ ≤ ∑ ε : Idx → Fin 2,
            ∫ z in Work.Diff.STE.unitCube (ι := Idx),
              ‖Work.Diff.STE.pdVec m β G (z + fun i => (ε i : ℝ) - 1)‖ ^ 2 := hstep3
      _ ≤ ∑ _ε : Idx → Fin 2, CE j m * (1
              + (∑ p : Idx, ∑ q : Idx,
                  Work.Diff.STE.ENormSq m (fun z : Idx → ℝ => ((Mf z p q : ℝ) : ℂ)))
              + (∑ p : Idx, ∑ q : Idx, ∑ r : Idx,
                  Work.Diff.STE.ENormSq m (fun z : Idx → ℝ => ((Nf z p q r : ℝ) : ℂ)))) :=
            Finset.sum_le_sum fun ε _ => hterm ε
      _ = (Fintype.card (Idx → Fin 2) : ℝ) * (CE j m * (1
              + (∑ p : Idx, ∑ q : Idx,
                  Work.Diff.STE.ENormSq m (fun z : Idx → ℝ => ((Mf z p q : ℝ) : ℂ)))
              + (∑ p : Idx, ∑ q : Idx, ∑ r : Idx,
                  Work.Diff.STE.ENormSq m (fun z : Idx → ℝ => ((Nf z p q r : ℝ) : ℂ))))) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (Fintype.card (Idx → Fin 2) : ℝ) * (CE j m * ((1 + 2 * Cj j m)
              * (1 + D.ENormB (m + 1) h))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine mul_le_mul_of_nonneg_left ?_ (hCE0 j m)
            have h5 := hone
            linarith [h5]
      _ = (Fintype.card (Idx → Fin 2) : ℝ) * CE j m * (1 + 2 * Cj j m)
            * (1 + D.ENormB (m + 1) h) := by ring
      _ = ((2 : ℝ) ^ (Module.finrank ℝ E) * CE j m * (1 + 2 * Cj j m))
            * (1 + D.ENormB (m + 1) h) := by rw [hcard]

end Work.Diff.STE.Lead.GalTame.ResidGn
