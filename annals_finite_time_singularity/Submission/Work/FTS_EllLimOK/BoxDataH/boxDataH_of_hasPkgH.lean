import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EpsEngine.ClassCStepSlice
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.EpsEngine.RHSDataFepsSix.exists_RHSData_feps_six
import Submission.Work.FTS.EpsEngine.tendsto_mixed_epsIter_limFam_six
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.mul_WlInf6_HkSq
import Submission.Work.FTS.StrongEps.E5G.ExistsLimG_assembly
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.hkSqFepsSub_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.regFromVolterra
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.TransportS.t2SlotGuarded
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.FatouH
import Submission.Work.FTS_EllLimOK.PkgJets.pinMid
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.contDiffOn_two_of_sliceData
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Slice
import Submission.Work.FTS_EllLimOK.ProducerH.pkgMemSqH_helpers
import Submission.Work.FTS_EllLimOK.ProducerH.pkgMemSqH_of_ellClassOk
import Submission.Work.FTS_RegExport.RXR5.R5PiecesF
import Submission.Work.FTS_RegExport.RXVP.NoHdat.velPkgEasy_noHdat
import Submission.Work.FTS_RegExport.RXVP.velPkg_proved
import Submission.Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower
import Submission.Work.FTS_RegExport.Vz7Eslot
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.XBallLimExists =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem XBallLimExists {α C₀ Ce Cs M' Cpt L δ R : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    {h₀ : Work.FTS.Galerkin.Fn}
    (hC₀ : 0 < C₀) (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α (2 * C₀) Φs E)
    (hM : 0 ≤ M')
    (hL : 0 < L) (hδ : 0 < δ) (hδL : δ * Real.sqrt L < 1) (hR : 0 < R)
    (hbd : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.StrongEps.EpsMem α (Work.FTS.EpsEngine.Feps α ρ ε Φs E u) ∧
        Work.FTS.StrongEps.EpsSq α (Work.FTS.EpsEngine.Feps α ρ ε Φs E u) ≤ L)
    (hlip : ∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) v →
      Work.FTS.StrongEps.EpsMem α (fun z θ => u z θ - v z θ) →
      Work.FTS.StrongEps.EpsSq α (fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ
        - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ)
        ≤ L * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ))
    (hCpt : 0 ≤ Cpt)
    (hpt : ∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)))
    (hsmo : Work.FTS.EllipticEst.SmoothOpen h₀) (hmem : Work.Spaces.HkMem α 6 h₀)
    (hM6 : Work.Spaces.HkSq α 6 h₀ ≤ M')
    (hcl : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h₀)))
    (hball : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h₀))
      ≤ C₀ * α ^ 2)
    (hdatmem : Work.FTS.StrongEps.EpsMem α h₀) (hdatsq : Work.FTS.StrongEps.EpsSq α h₀ ≤ R)
    (hiter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀)
        (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ (n + 1)) τ)) :
    (∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀)
        (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ)) ∧
    (∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.Spaces.HkMem α 6
        (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ)) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- ## 0. the numerical set-up of the contraction
  set q : ℝ := δ ^ 2 * L with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q < 1 := by
    rw [hq]
    have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
    have hp : (δ * Real.sqrt L) ^ 2 = δ ^ 2 * L := by rw [mul_pow, Real.sq_sqrt hL.le]
    have h1 : (δ * Real.sqrt L) ^ 2 < 1 := by nlinarith [hδL, mul_nonneg hδ.le hsL]
    rwa [hp] at h1
  set r : ℝ := Real.sqrt q with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg q
  have hrpow : ∀ n : ℕ, Real.sqrt (q ^ n) = r ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Real.sqrt_mul hq0, ← hr, ih, pow_succ']
  have hr1 : r < 1 := by
    have h2 : r ^ 2 = q := by rw [hr]; exact Real.sq_sqrt hq0
    nlinarith [hr0, h2, hq1]
  -- ## 1. the datum in the ball and the gates of the engine
  have hP₀ : Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) h₀ :=
    ⟨hsmo, hdatmem, hdatsq, hcl, le_trans hball (by nlinarith [hC₀.le, sq_nonneg α])⟩
  have hcontF : ∀ u : Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      ContinuousOn (fun q : ℝ × ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E u q.1 q.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun u hu => (Work.FTS.EpsEngine.continuousOn_Feps_of_XBall (Ce := Ce) (Cs := Cs) (R := R)
      (C₀ := 2 * C₀) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := u)
      hα hρ hε hEll hstar hu).1
  have hzeroF : ∀ u : Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u → ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) →
        Work.FTS.EpsEngine.Feps α ρ ε Φs E u q.1 q.2 = 0 :=
    fun u hu => (Work.FTS.EpsEngine.continuousOn_Feps_of_XBall (Ce := Ce) (Cs := Cs) (R := R)
      (C₀ := 2 * C₀) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := u)
      hα hρ hε hEll hstar hu).2
  have hkeepIter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀)
        (fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ,
          Work.FTS.EpsEngine.Feps α ρ ε Φs E
            (slice (Work.FTS.StrongEps.EpsLocalPStar.iter
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s) z θ) := by
    intro n τ hτ
    have h : slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ (n + 1)) τ
        = fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ,
          Work.FTS.EpsEngine.Feps α ρ ε Φs E
            (slice (Work.FTS.StrongEps.EpsLocalPStar.iter
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s) z θ := by
      funext z θ
      simp only [Work.FTS.Galerkin.slice_apply, Work.FTS.StrongEps.EpsLocalPStar.iter_succ]
    rw [← h]
    exact hiter n τ hτ
  -- ## 2. the a-priori bounds of the engine
  obtain ⟨hP, hB0, hBK, hwsq, hwpt⟩ :=
    Work.FTS.EpsEngine.iter_bounds_v4 (α := α)
      (F := Work.FTS.EpsEngine.Feps α ρ ε Φs E) (h₀ := h₀)
      (P := fun u => Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u)
      (Cpt := Cpt) (L := L) (δ := δ) (q := q) (r := r)
      hδ hL hδL hq hr hq0 hq1 hr0 hrpow hCpt hP₀ hbd hlip hpt hcontF hzeroF hkeepIter
  obtain ⟨hcontIter, hmeasIter⟩ :=
    Work.FTS.EpsEngine.iter_cont_meas (α := α) (Cpt := Cpt) (L := L) (δ := δ)
      (F := Work.FTS.EpsEngine.Feps α ρ ε Φs E) (h₀ := h₀)
      (P := fun u => Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u)
      hδ hL.le hCpt hP hcontF hzeroF hbd hpt
  have hEq : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ t : ℝ, t ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s z θ
        - slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) t z θ) ≤ L * (s - t) ^ 2 :=
    fun n => Work.FTS.EpsEngine.EpsSq_iter_sub_sq_le n hδ hL.le hCpt
      (fun m hm τ hτ => hP m τ hτ) hcontF hzeroF hbd hpt
  have hpair : ∀ (n m : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → n ≤ m →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s z θ
        - slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ m) s z θ) ≤ q ^ n :=
    Work.FTS.EpsEngine.epsPair_of_iter_bounds (α := α) (δ := δ) (q := q)
      (F := Work.FTS.EpsEngine.Feps α ρ ε Φs E) (h₀ := h₀) hq0 hq1
      (fun M hM s hs => (hB0 M s hs hM).2) (fun M K hK hKM s hs => (hBK M K hK hKM s hs).2)
  have hFint : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      IntervalIntegrable (fun σ => Work.FTS.EpsEngine.Feps α ρ ε Φs E
        (slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) σ) z θ) volume 0 s := by
    intro n s hs z θ hz hθ
    exact ContinuousOn.intervalIntegrable_of_Icc hs.1
      ((hcontIter n z θ hz hθ.1 hθ.2).mono (Set.Icc_subset_Icc_right hs.2))
  have hconv : ∀ (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun N : ℕ => slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ N) s z θ) Filter.atTop
        (nhds (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) s z θ)) :=
    Work.FTS.EpsEngine.tendsto_slice_iter_limFam (F := Work.FTS.EpsEngine.Feps α ρ ε Φs E)
      (h₀ := h₀) (δ := δ) (Cpt := Cpt) (r := r) hCpt hr0 hr1
      (fun n τ hτ hn z θ hz hθ0 hθ1 => hwpt n τ hτ hn z θ hz hθ0 hθ1)
  have hmoll : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ (n + 1)) s z θ
        = h₀ z θ + Work.FTS.StrongEps.Jeps ρ ε
            (Work.FTS.EpsEngine.epsPsi α ρ ε Φs E h₀ n s) z θ
          - Work.FTS.EpsEngine.epsC α ρ ε Φs E h₀ n s
            * Work.FTS.StrongEps.bump z θ :=
    fun n s hs z θ hz hθ =>
      Work.FTS.EpsEngine.slice_iter_succ_mollForm n hα hρ hε hε1 hEll hstar hml hR.le hL.le
        hsmo (fun σ hσ => hP n σ hσ) (fun σ hσ t ht => hEq n σ hσ t ht)
        (fun τ hτ z' θ' hz' hθ' => hFint n τ hτ z' θ' hz' hθ') hs hz hθ
  -- ## 3. the limit clauses
  have hsmoW : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.EllipticEst.SmoothOpen (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ) := by
    intro τ hτ
    exact Work.FTS.EpsEngine.smoothOpen_limFam_slice_of_iter_bounds (α := α) (C₀ := 2 * C₀)
      (R := R) (Ce := Ce) (Cs := Cs) (Lw := L) (δ := δ) (q := q) (Cpt := Cpt) (ρ := ρ)
      (Φs := Φs) (E := E) (ε := ε) (h₀ := h₀)
      hα hρ hε hε1 hEll hstar hml hR.le hL.le hsmo hq0 hq1 hCpt hP hEq
      (fun M hM s hs => (hB0 M s hs hM).2)
      (fun M K hK hKM s hs => (hBK M K hK hKM s hs).2)
      (fun n s hs hn z θ hz hθ0 hθ1 => by
        rw [← hr]
        exact hwpt n s hs hn z θ hz hθ0 hθ1)
      (fun n s hs z θ hz hθ => hFint n s hs z θ hz hθ) hτ
  have hmet : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsMem α (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ) ∧
      Work.FTS.StrongEps.EpsSq α (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ) ≤ R := by
    intro τ hτ
    exact Work.FTS.EpsEngine.limFam_EpsMem (α := α) (R := R) (δ := δ) hR.le hconv
      (fun n σ hσ => ⟨(hP n σ hσ).mem, (hP n σ hσ).sq_le⟩) τ hτ
  have hmem4₀ : Work.Spaces.HkMem α 4 h₀ :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmo 4 (by norm_num) hmem
  have hmem4W : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → Work.Spaces.HkMem α 4
      (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ) := by
    intro τ hτ
    refine Work.FTS.EpsEngine.HkMem_epsLim_feps (α := α) (C₀ := 2 * C₀) (R := R) (Ce := Ce)
      (Cs := Cs) (Lw := L) (δ := δ) (q := q) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (g₀ := h₀)
      hα hρ hε hε1 hEll hstar hml hR.le hL.le hsmo hmem hδ.le hq0 hq1 hP hEq hpair hmoll hconv
      hτ
  have hclW : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → Work.FTS.ClassC.ClassC α
      (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
        (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ))) := by
    intro τ hτ
    exact Work.FTS.EpsEngine.ThetaFromEps.classC_Pz_Jeps_of_epsMem hρ hα hα1 hε hε1
      (hsmoW τ hτ) (hmem4W τ hτ) (hmet τ hτ).1
      (XBallLimAux.FstarPzJepsSmooth (ρ := ρ) hρ hε hα (hsmoW τ hτ)
        (Work.FTS.OpenPkg.HkMem_mono_open (hsmoW τ hτ) 1 (by norm_num) (hmem4W τ hτ)))
  have hxnW : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → Work.FTS.Nonlin.Xn α
      (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
        (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ))) ≤ 2 * C₀ * α ^ 2 := by
    intro τ hτ
    obtain ⟨B4, hB4pos, hiter4⟩ :=
      Work.FTS.EpsEngine.HkMem_iter_feps (α := α) (C₀ := 2 * C₀) (Ce := Ce) (Cs := Cs)
        (R := R) (Lw := L) (ε := ε) (δ := δ) (τ := τ) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := h₀)
        hρ hα hε hε1 hR.le hL.le hEll hstar hml hsmo hmem4₀ hδ.le hτ.1 hτ.2 hP hEq
    have hmemN4 : ∀ N : ℕ, Work.Spaces.HkMem α 4
        (slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ N) τ) := fun N => (hiter4 N).1
    have htail : ∀ N : ℕ, 1 ≤ N →
        Work.FTS.StrongEps.EpsMem α (fun z θ =>
          slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ
          - slice (Work.FTS.StrongEps.EpsLocalPStar.iter
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ N) τ z θ) ∧
        Work.FTS.StrongEps.EpsSq α (fun z θ =>
          slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ
          - slice (Work.FTS.StrongEps.EpsLocalPStar.iter
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ N) τ z θ) ≤ q ^ N := by
      intro N hN
      obtain ⟨hm, hsq⟩ := Work.FTS.EpsEngine.EpsSq_iter_limFam_le (α := α) (q := q) (δ := δ)
        hq0 hq1 hconv (fun M K hK hKM τ' hτ' => hBK M K hK hKM τ' hτ') N hN τ hτ
      refine ⟨?_, ?_⟩
      · have hfun : (fun z θ => slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ
            - slice (Work.FTS.StrongEps.EpsLocalPStar.iter
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ N) τ z θ)
            = fun z θ => -(slice (Work.FTS.StrongEps.EpsLocalPStar.iter
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ N) τ z θ
            - slice (Work.FTS.StrongEps.EpsLocalPStar.limFam
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ) := by
          funext z θ; ring
        rw [hfun]
        exact Work.FTS.StrongEps.EpsLocalPStar.EpsMem_neg2 hm
      · rw [Work.FTS.StrongEps.EpsLocalPStar.EpsSq_sub_comm]
        exact hsq
    exact Work.FTS.EpsEngine.Xn_PzJeps_limFam_le_of_tail (α := α) (ε := ε) (C₀ := 2 * C₀)
      (q := q) (ρ := ρ) (Φs := Φs) (E := E)
      (F := Work.FTS.EpsEngine.Feps α ρ ε Φs E) (h₀ := h₀) (τ := τ)
      hρ hα hε hε1 hq0 hq1 (fun N => (hP N τ hτ).ball) (fun N hN => htail N hN)
      (fun N => (hP N τ hτ).smoothOpen) (hsmoW τ hτ) hmemN4 (hmem4W τ hτ)
  refine ⟨fun τ hτ => ⟨hsmoW τ hτ, (hmet τ hτ).1, (hmet τ hτ).2, hclW τ hτ, hxnW τ hτ⟩, ?_⟩
  -- ## 4. the `ℋ⁶`-honesty of the limit slice
  intro τ hτ
  have h06 : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 h₀ z θ) ≤ Bz :=
    fun z hz => ⟨_, le_rfl⟩
  have hz6 := Work.FTS.EpsEngine.perz_iter_feps_le_six (α := α) (C₀ := 2 * C₀) (Ce := Ce)
    (Cs := Cs) (R := R) (Lw := L) (ε := ε) (τ := τ) hρ hα hε hε1 hR.le hL.le hτ.1 hEll hstar hml
    (fun n s hs => hP n s ⟨hs.1, le_trans hs.2 hτ.2⟩)
    (fun n s hs t ht => hEq n s ⟨hs.1, le_trans hs.2 hτ.2⟩ t ⟨ht.1, le_trans ht.2 hτ.2⟩) h06
  have hslot6 := Work.FTS.EpsEngine.tendsto_mixed_epsIter_limFam_six (α := α) (C₀ := 2 * C₀)
    (R := R) (Ce := Ce) (Cs := Cs) (Lw := L) (δ := δ) (q := q) (ρ := ρ) (Φs := Φs) (E := E)
    (ε := ε) (h₀ := h₀) hα hρ hε hε1 hEll hstar hml hR.le hL.le hsmo hq0 hq1 hP hEq hpair hmoll
    hconv hτ
  obtain ⟨B6, hB6pos, hRHS6⟩ := Work.FTS.EpsEngine.RHSDataFepsSix.exists_RHSData_feps_six
    (α := α) (C₀ := 2 * C₀) (Ce := Ce) (Cs := Cs) (R := R) (Lw := L) (ε := ε) (T := δ)
    (ρ := ρ) (Φs := Φs) (E := E) (g₀ := h₀) hρ hα hε hε1 hR.le hL.le hδ.le hEll hstar hml
  have hiter6 := Work.FTS.EpsEngine.HkMem_iter_all (α := α) (B := B6)
    (F := Work.FTS.EpsEngine.Feps α ρ ε Φs E) (h₀ := h₀) (k := 6) (T := δ) (τ := τ)
    hτ.1 hτ.2 hδ.le hB6pos.le hsmo hmem (fun n => (hP n τ hτ).smoothOpen)
    (fun n => hRHS6 n (fun s hs => hP n s hs) (fun s hs t ht => hEq n s hs t ht))
  exact (Work.FTS.EpsEngine.HkMem_limFam_of_slot_conv (α := α)
    (B := Work.Spaces.HkNorm α 6 h₀ + B6 * τ) (F := Work.FTS.EpsEngine.Feps α ρ ε Φs E)
    (h₀ := h₀) (k := 6) (τ := τ)
    (fun n => (hiter6 n).1) (fun n => (hiter6 n).2)
    (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hP n τ hτ).smoothOpen 6)
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hsmoW τ hτ) 6)
    (fun j i hji z θ hzq => hslot6 j i hji z θ hzq.1 hzq.2) hz6).1

end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxDataH.boxDataH_of_hasPkgH =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/--
**`BoxDataH` from the honest hypothesis `HasPkgH`.**

Along every `LimSeq4` and on every closed box `cbox a b = [a,b] × [0,π/2]` (`0 < a ≤ b`) the
sequence `E (fn n)` converges pointwise to a limit `Ψ` which is `C²` on the box and vanishes on the
two angular boundary lines.

The proof has three steps.  `ClusterLimitH.clusterLimitH` supplies the limit `Ψ` (with the law, the
two `ℋ⁰`-memberships and the `C²`-regularity on every box, obtained from the `C^{2,β}`
Arzelà–Ascoli crux `contDiffOn_two_of_boxUniform2` fed by `PkgBoxH`), together with the
sub-subsequence convergence on the open quadrant; `Filter.tendsto_of_subseq_tendsto` upgrades the
latter to the convergence of the *whole* sequence on the open quadrant, and the two Dirichlet
clauses of the law give the convergence on the two boundary lines.
-/
theorem boxDataH_of_hasPkgH {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS_EllLimOK.BoxDataH α Ce := by
  intro E hE fn f hL a b ha hab
  obtain ⟨Ψ, hbox, hsol, -, -, hcluster⟩ := clusterLimitH (E := E) hα hα1 hE hL
  -- the box-uniform data of the sequence, on every box
  have hboxdata : ∀ a' b' : ℝ, 0 < a' → a' < b' →
      BoxUniform2 a' b' (fun n z θ => E (fn n) z θ) := by
    intro a' b' ha' hab'
    obtain ⟨K, β, hK, hβ, hb⟩ := hE.box a' b' ha' hab'.le
    obtain ⟨B, hB⟩ := hL.bound
    refine ⟨K * max B 0 + 1, β, hβ, ?_, ?_, ?_⟩
    · intro n
      exact (hb (fn n) (hL.classC n)).1
    · intro n k hk p hp
      have h2 : Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ max B 0 :=
        le_trans (hB n) (le_max_left _ _)
      have hle : K * Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ K * max B 0 :=
        mul_le_mul_of_nonneg_left h2 hK.le
      calc ‖iteratedFDerivWithin ℝ k (Function.uncurry (E (fn n)))
              (Work.FTS_EllLimOK.cbox a' b') p‖
          ≤ K * Work.FTS.StrongGlobal.Xn6 α (fn n) :=
            (hb (fn n) (hL.classC n)).2.1 hab' k hk p hp
        _ ≤ K * max B 0 := hle
        _ ≤ K * max B 0 + 1 := by linarith
    · intro n p hp q hq
      have h2 : Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ max B 0 :=
        le_trans (hB n) (le_max_left _ _)
      have hr : (0 : ℝ) ≤ ‖p - q‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
      have hle : K * Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ K * max B 0 :=
        mul_le_mul_of_nonneg_left h2 hK.le
      calc ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (E (fn n)))
              (Work.FTS_EllLimOK.cbox a' b') p
            - iteratedFDerivWithin ℝ 2 (Function.uncurry (E (fn n)))
              (Work.FTS_EllLimOK.cbox a' b') q‖
          ≤ K * Work.FTS.StrongGlobal.Xn6 α (fn n) * ‖p - q‖ ^ β :=
            (hb (fn n) (hL.classC n)).2.2 hab' p hp q hq
        _ ≤ (K * max B 0) * ‖p - q‖ ^ β := mul_le_mul_of_nonneg_right hle hr
        _ ≤ (K * max B 0 + 1) * ‖p - q‖ ^ β := mul_le_mul_of_nonneg_right (by linarith) hr
  -- the convergence of the whole sequence on the open quadrant
  have hconvQ : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => E (fn n) z θ) Filter.atTop (nhds (Ψ z θ)) := by
    intro z θ hzθ
    refine Filter.tendsto_of_subseq_tendsto (fun ns hns => ?_)
    obtain ⟨τ, hτ⟩ := hcluster ns hns
    exact ⟨τ, hτ z θ hzθ⟩
  -- the pointwise convergence on every box
  have hconvAll : ∀ a' b' : ℝ, 0 < a' → a' < b' → ∀ z ∈ Set.Icc a' b',
      ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      Filter.Tendsto (fun n => E (fn n) z θ) Filter.atTop (nhds (Ψ z θ)) := by
    intro a' b' ha' _ z hz θ hθ
    have hzpos : 0 < z := lt_of_lt_of_le ha' hz.1
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      have hm : (fun n : ℕ => E (fn n) z 0) = fun _ => (0 : ℝ) := by
        funext n
        exact ((hE.toHasPkg (fn n) (hL.classC n)).2.sol).2.1 z hzpos.le
      have hl : Ψ z 0 = 0 := hsol.2.1 z hzpos.le
      rw [hl, hm]
      exact tendsto_const_nhds
    · rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · subst h1
        have hm : (fun n : ℕ => E (fn n) z (Real.pi / 2)) = fun _ => (0 : ℝ) := by
          funext n
          exact ((hE.toHasPkg (fn n) (hL.classC n)).2.sol).2.2.1 z hzpos.le
        have hl : Ψ z (Real.pi / 2) = 0 := hsol.2.2.1 z hzpos.le
        rw [hl, hm]
        exact tendsto_const_nhds
      · exact hconvQ z θ ⟨hzpos, h0, h1⟩
  have hBoxReg : Work.FTS_EllLimOK.BoxReg Ψ :=
    boxReg_of_boxUniform2 (H := fun n z θ => E (fn n) z θ) hboxdata hconvAll
  exact ⟨Ψ, hBoxReg a b ha hab.le, hconvAll a b ha hab, fun z hz =>
    ⟨hsol.2.1 z (le_trans ha.le hz.1), hsol.2.2.1 z (le_trans ha.le hz.1)⟩⟩

end Work.FTS_EllLimOK.BoxDataH
end
end
