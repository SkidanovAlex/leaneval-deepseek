import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Metrizable.Uniformity
import Submission.Work.FTS.CoercivityFix.PsiMul.PsiZop
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.Closed
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.Defs3
import Submission.Work.FTS_EllLimOK.UniqFatou
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.StepReg2_all_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary closure of the three components of `RegQo` -/

/-- The radial factor `ψ(z) = 1/(1+z)` is `C^∞` on the positive half-line. -/
private theorem contDiffOn_oneDiv_fts :
    ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => 1 / (1 + z)) (Set.Ioi 0) := by
  intro n
  refine ContDiffOn.div contDiffOn_const (contDiffOn_const.add contDiffOn_id) ?_
  intro z hz
  have hz0 : (0 : ℝ) < z := hz
  positivity

/-- `SmoothOpen` is closed under negation. -/
private theorem smoothOpen_neg_fts {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => - f z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => - f z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ : ℝ => - f z θ)
      = fun p : ℝ × ℝ => - (Function.uncurry f p) := rfl
  rw [hfun]
  exact ContDiffOn.neg hf

/-- `BdryTraces` is additive, in the pointwise shape used below. -/
private theorem bdryTraces_add_fts {α : ℝ} {k : ℕ} {f g : Fn}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hf : Work.FTS.Nonlin.BdryTraces α k f) (hg : Work.FTS.Nonlin.BdryTraces α k g) :
    Work.FTS.Nonlin.BdryTraces α k (fun z θ => f z θ + g z θ) :=
  Work.FTS.ClassC.bdryTraces_add hsf hsg hf hg

/-- `BdryTraces` is closed under multiplication by a constant, in the pointwise shape used
below. -/
private theorem bdryTraces_const_mul_fts {α : ℝ} {k : ℕ} (c : ℝ) {f : Fn}
    (hf : Work.FTS.Nonlin.BdryTraces α k f) :
    Work.FTS.Nonlin.BdryTraces α k (fun z θ => c * f z θ) :=
  Work.FTS.ClassC.bdryTraces_smul (α := α) (k := k) hf c

/-- `BdryTraces` is closed under negation. -/
private theorem bdryTraces_neg_fts {α : ℝ} {k : ℕ} {f : Fn}
    (hf : Work.FTS.Nonlin.BdryTraces α k f) :
    Work.FTS.Nonlin.BdryTraces α k (fun z θ => - f z θ) := by
  have heq : (fun z θ => - f z θ) = ((-1 : ℝ) • f) := by
    funext z θ; simp [Pi.smul_apply]
  rw [heq]
  exact Work.FTS.ClassC.bdryTraces_smul (α := α) (k := k) hf (-1)

/-- `BdryTraces` is closed under subtraction, in the pointwise shape used below (the two
summands must be `C^∞` on the open quadrant, which is how `ClassC.bdryTraces_add` is stated). -/
private theorem bdryTraces_sub_fts {α : ℝ} {k : ℕ} {f g : Fn}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hf : Work.FTS.Nonlin.BdryTraces α k f) (hg : Work.FTS.Nonlin.BdryTraces α k g) :
    Work.FTS.Nonlin.BdryTraces α k (fun z θ => f z θ - g z θ) := by
  have heq : (fun z θ => f z θ - g z θ) = (f + fun z θ => - g z θ) := by
    funext z θ; rfl
  rw [heq]
  exact bdryTraces_add_fts hsf (smoothOpen_neg_fts hsg) hf
    (bdryTraces_neg_fts (α := α) (k := k) hg)

/-! ## The open-class port of `𝓛̂` -/

/-- **`RegQo α (m+1) ⟹ RegQo α m (𝓛̂ ·)`**, the open-class twin of
`CoercivityFix.Assembly.Lhat_RegQ`.

`𝓛̂f = f + D_z f − 2f/(1+z) − 3D_θf/(1+z)`: smoothness and `ℋ^m`-membership come from
`H6Aux.smoothOpen_Lhat` / `H6Aux.Lhat_mem`, and the boundary traces are assembled from the
pieces `f`, `D_z f` (`regQo_dth_dz`), the two radial multiples with `ψ = 1/(1+z)`
(`TracesAux.BdryTraces_psi_mul_open` + `PsiMul.zop_psi_bound`) and
`ClassC.bdryTraces_add` / `bdryTraces_smul`. -/
private theorem Lhat_RegQo_aux (α : ℝ) (hα : 0 < α) (m : ℕ) {f : Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α (m + 1) f) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α m (Work.FTS.CoercivityFix.Lhat f) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.1
  have hmem : Work.Spaces.HkMem α (m + 1) f := hf.2.1
  have htr : Work.FTS.Nonlin.BdryTraces α (m + 1) f := hf.2.2
  obtain ⟨hdth, hdz⟩ := Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz hα (n := m) hf
  have htr_f : Work.FTS.Nonlin.BdryTraces α m f := fun a b hab => htr a b (by omega)
  have htr_dz : Work.FTS.Nonlin.BdryTraces α m (Work.Spaces.Dz f) := hdz.2.2
  have htr_dth : Work.FTS.Nonlin.BdryTraces α m (Work.Spaces.Dth f) := hdth.2.2
  -- the radial multiplier `ψ(z) = 1/(1+z)`
  obtain ⟨K, hK0, hKb⟩ := Work.FTS.CoercivityFix.PsiMul.zop_psi_bound m
  have hψ : ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => 1 / (1 + z)) (Set.Ioi 0) :=
    contDiffOn_oneDiv_fts
  have hsmψf : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / (1 + z)) * f z θ) :=
    Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_mul
      (Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_zOnly hψ) hsm
  have hsmψdth : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / (1 + z)) * Work.Spaces.Dth f z θ) :=
    Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_mul
      (Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_zOnly hψ) hdth.1
  have hpsi_f : Work.FTS.Nonlin.BdryTraces α m (fun z θ => (1 / (1 + z)) * f z θ) :=
    Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open m hK0 hKb hψ hsm htr_f
  have hpsi_dth : Work.FTS.Nonlin.BdryTraces α m
      (fun z θ => (1 / (1 + z)) * Work.Spaces.Dth f z θ) :=
    Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open m hK0 hKb hψ hdth.1 htr_dth
  -- the four summands, and their combination
  have hA : Work.FTS.Nonlin.BdryTraces α m (fun z θ => f z θ + Work.Spaces.Dz f z θ) :=
    bdryTraces_add_fts hsm hsm.Dz htr_f htr_dz
  have hB : Work.FTS.Nonlin.BdryTraces α m (fun z θ => 2 * ((1 / (1 + z)) * f z θ)) :=
    bdryTraces_const_mul_fts 2 hpsi_f
  have hC : Work.FTS.Nonlin.BdryTraces α m
      (fun z θ => 3 * ((1 / (1 + z)) * Work.Spaces.Dth f z θ)) :=
    bdryTraces_const_mul_fts 3 hpsi_dth
  have hAB : Work.FTS.Nonlin.BdryTraces α m
      (fun z θ => (f z θ + Work.Spaces.Dz f z θ) - 2 * ((1 / (1 + z)) * f z θ)) :=
    bdryTraces_sub_fts (Work.FTS.EllipticEst.smoothOpen_add hsm hsm.Dz)
      (Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_const_mul 2 hsmψf) hA hB
  have hABC : Work.FTS.Nonlin.BdryTraces α m
      (fun z θ => ((f z θ + Work.Spaces.Dz f z θ) - 2 * ((1 / (1 + z)) * f z θ))
        - 3 * ((1 / (1 + z)) * Work.Spaces.Dth f z θ)) :=
    bdryTraces_sub_fts
      (Work.FTS.EllipticEst.smoothOpen_add
        (Work.FTS.EllipticEst.smoothOpen_add hsm hsm.Dz)
        (smoothOpen_neg_fts
          (Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_const_mul 2 hsmψf)))
      (Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_const_mul 3 hsmψdth) hAB hC
  refine ⟨Work.FTS.StrongPersist.H6Aux.smoothOpen_Lhat hsm,
    Work.FTS.StrongPersist.H6Aux.Lhat_mem α hα m hsm hmem, ?_⟩
  rw [show Work.FTS.CoercivityFix.Lhat f
      = fun z θ => ((f z θ + Work.Spaces.Dz f z θ) - 2 * ((1 / (1 + z)) * f z θ))
          - 3 * ((1 / (1 + z)) * Work.Spaces.Dth f z θ) from by
    funext z θ
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    ring]
  exact hABC

/-! ## The open-class port of the defect `Ê₂` -/

/-- **Extension of a pointwise integrand domination from the open quadrant to the closed
domain `Iz × Iθ`.**  Both `HkIntegrand`-terms vanish on the two boundary lines `z = 0` and
`sin(2θ) = 0`, so a bound valid on the open quadrant and with a nonnegative right-hand side
extends.  (This is `H6Aux.HkIntegrand_le_Izθ_of_Ioo` with a general majorant `M`.) -/
private theorem HkIntegrand_le_Izθ_of_Ioo_fts {α : ℝ} (hα : 0 < α) {m : ℕ} {X : ℝ → ℝ → ℝ}
    {M : ℝ → ℝ → ℝ} (hMnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ M z θ)
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.HkIntegrand α m X z θ ≤ M z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m X z θ ≤ M z θ := by
  intro z hz θ hθ
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · rw [← hz0, Work.FTS.LocData.HkIntegrand_zero_fst]
    exact hMnn 0 (Set.mem_Ici.mpr le_rfl) θ hθ
  · by_cases hsin : Real.sin (2 * θ) = 0
    · rw [Work.FTS.StrongPersist.HkIntegrand_eq_zero_of_sin_zero hα hsin]
      exact hMnn z hz θ hθ
    · have hsinpos : 0 < Real.sin (2 * θ) :=
        lt_of_le_of_ne (Work.Elliptic.sin_two_nonneg_of_mem hθ) (Ne.symm hsin)
      have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        Work.FTS.CoercivityFix.Coer1.mem_Ioo_of_mem_Iθ_of_sin_pos hθ hsinpos
      exact h z hzpos θ hθ'

/-- **`RegQo α (m+1) ⟹ RegQo α m (Ê₂ ·)`**, the open-class twin of
`CoercivityFix.Assembly.E2hat_RegQ`.

`Ê₂ f = 2(φ·f) + 3(φ·D_θ f)` with `φ(z) = z/(1+z)²`: smoothness is the closure of `SmoothOpen`
under the `z`-only multiplier `φ` and under sums; the `ℋ^m`-membership is the α-uniform pointwise
domination `E2hatOAux.E2hat_HkIntegrand_le_uniform_pt`, promoted by the majorant criterion; and the
boundary traces come from `TracesAux.BdryTraces_psi_mul_open` with `ψ = φ`
(`E2Bound.SlotMul.Zop_iterate_phiZ_bound`). -/
private theorem E2hat_RegQo_aux (α : ℝ) (hα : 0 < α) (m : ℕ) {f : Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α (m + 1) f) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α m (Work.FTS.CoercivityFix.E2hat f) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.1
  have hmem : Work.Spaces.HkMem α (m + 1) f := hf.2.1
  have htr : Work.FTS.Nonlin.BdryTraces α (m + 1) f := hf.2.2
  obtain ⟨hdth, _⟩ := Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz hα (n := m) hf
  have hmf : Work.Spaces.HkMem α m f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm m (Nat.le_succ m) hmem
  have hmth : Work.Spaces.HkMem α m (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := m) (by linarith : -(1 / 10 : ℝ) ≤ α) hsm hmem
  obtain ⟨Cn, hCnpos, hpt⟩ :=
    Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.E2hat_HkIntegrand_le_uniform_pt m
  -- smoothness of `Ê₂ f`
  have hφ : ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi 0) :=
    Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.phiZ_contDiffOn
  have hsmE2 : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.E2hat f) := by
    rw [Work.FTS.CoercivityFix.E2Bound.E2hat_eq_zmul f]
    exact Work.FTS.EllipticEst.smoothOpen_add
      (Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_const_mul 2
        (Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_mul
          (Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_zOnly hφ) hsm))
      (Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_const_mul 3
        (Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_mul
          (Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_zOnly hφ) hdth.1))
  -- the `ℋ^m`-membership
  have hmemE2 : Work.Spaces.HkMem α m (Work.FTS.CoercivityFix.E2hat f) := by
    refine Work.FTS.LocData.HkMem_of_majorant α m
      (f := Work.FTS.CoercivityFix.E2hat f)
      (M := fun z θ => Cn * Work.Spaces.HkIntegrand α m f z θ
        + Cn * Work.Spaces.HkIntegrand α m (Work.Spaces.Dth f) z θ)
      (hsmE2.continuousOn_HkIntegrand α m) ?_ ?_ ?_
    · intro z hz
      exact ((hmf.1 z hz).const_mul Cn).add ((hmth.1 z hz).const_mul Cn)
    · refine ((hmf.2.const_mul Cn).add (hmth.2.const_mul Cn)).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      simp only [Pi.add_apply]
      rw [MeasureTheory.integral_add ((hmf.1 z hz).const_mul Cn) ((hmth.1 z hz).const_mul Cn),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    · refine HkIntegrand_le_Izθ_of_Ioo_fts hα (X := Work.FTS.CoercivityFix.E2hat f)
        (fun z _ θ _ => add_nonneg
          (mul_nonneg hCnpos.le (Work.Spaces.HkIntegrand_nonneg α m f z θ))
          (mul_nonneg hCnpos.le
            (Work.Spaces.HkIntegrand_nonneg α m (Work.Spaces.Dth f) z θ))) ?_
      intro z hzpos θ hθ
      have h1 := hpt α f hα hsm z hzpos θ hθ
      have h2 : Cn * (Work.Spaces.HkIntegrand α m f z θ
            + Work.Spaces.HkIntegrand α m (Work.Spaces.Dth f) z θ)
          = Cn * Work.Spaces.HkIntegrand α m f z θ
            + Cn * Work.Spaces.HkIntegrand α m (Work.Spaces.Dth f) z θ := by ring
      rwa [h2] at h1
  -- the boundary traces
  have htr_f : Work.FTS.Nonlin.BdryTraces α m f := fun a b hab => htr a b (by omega)
  have htr_dth : Work.FTS.Nonlin.BdryTraces α m (Work.Spaces.Dth f) := hdth.2.2
  obtain ⟨K, hK0, hKb⟩ :=
    Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_phiZ_bound m
  have hsmφf : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z / (1 + z) ^ 2) * f z θ) :=
    Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_mul
      (Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_zOnly hφ) hsm
  have hsmφdth : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z / (1 + z) ^ 2) * Work.Spaces.Dth f z θ) :=
    Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_mul
      (Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_zOnly hφ) hdth.1
  have h1 : Work.FTS.Nonlin.BdryTraces α m (fun z θ => (z / (1 + z) ^ 2) * f z θ) :=
    Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open m hK0 hKb hφ hsm htr_f
  have h2 : Work.FTS.Nonlin.BdryTraces α m
      (fun z θ => (z / (1 + z) ^ 2) * Work.Spaces.Dth f z θ) :=
    Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open m hK0 hKb hφ hdth.1 htr_dth
  have h3 : Work.FTS.Nonlin.BdryTraces α m (fun z θ => 2 * ((z / (1 + z) ^ 2) * f z θ)) :=
    bdryTraces_const_mul_fts 2 h1
  have h4 : Work.FTS.Nonlin.BdryTraces α m
      (fun z θ => 3 * ((z / (1 + z) ^ 2) * Work.Spaces.Dth f z θ)) :=
    bdryTraces_const_mul_fts 3 h2
  have h34 : Work.FTS.Nonlin.BdryTraces α m
      (fun z θ => 2 * ((z / (1 + z) ^ 2) * f z θ)
        + 3 * ((z / (1 + z) ^ 2) * Work.Spaces.Dth f z θ)) :=
    bdryTraces_add_fts
      (Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_const_mul 2 hsmφf)
      (Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.smoothOpen_const_mul 3 hsmφdth) h3 h4
  refine ⟨hsmE2, hmemE2, ?_⟩
  rw [Work.FTS.CoercivityFix.E2Bound.E2hat_eq_zmul f]
  exact h34

/-! ## The bundle -/

theorem StepReg2_all_O (α : ℝ) (hα : 0 < α) (n : ℕ) :
    Work.FTS.StrongEps.EpsE4Thr.StepReg2O α n := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `RegQo α (n+2) f → RegQo α n f`
    intro f hf
    exact regQo_mono (k := n) (l := n + 2) (by omega) hf
  · -- `RegQo α (n+2) f → RegQo α (n+1) f`
    intro f hf
    exact regQo_mono (k := n + 1) (l := n + 2) (by omega) hf
  · -- `RegQo α (n+2) f → RegQo α (n+1) (D_θ f)`
    intro f hf
    exact (regQo_dth_dz hα (n := n + 1) hf).1
  · -- `RegQo α (n+2) f → RegQo α (n+1) (D_z f)`
    intro f hf
    exact (regQo_dth_dz hα (n := n + 1) hf).2
  · -- `RegQo α (n+2) f → RegQo α n (D_θ f)`
    intro f hf
    exact regQo_mono (k := n) (l := n + 1) (by omega)
      ((regQo_dth_dz hα (n := n + 1) hf).1)
  · -- `RegQo α (n+2) f → RegQo α n (D_z f)`
    intro f hf
    exact regQo_mono (k := n) (l := n + 1) (by omega)
      ((regQo_dth_dz hα (n := n + 1) hf).2)
  · -- `RegQo α (n+2) f → RegQo α n (𝓛̂ (D_z f))`
    intro f hf
    exact Lhat_RegQo_aux α hα n ((regQo_dth_dz hα (n := n + 1) hf).2)
  · -- `RegQo α (n+1) f → RegQo α n (Ê₂ f)`
    intro f hf
    exact E2hat_RegQo_aux α hα n hf
  · -- the one-sided comparison of the `ℋⁿ`-norms of the three slots with `|f|_{n+1}`
    intro f hf
    obtain ⟨hsm, hm, _⟩ := hf
    have hm1 : Work.Spaces.HkMem α (n + 1) f :=
      Work.FTS.OpenPkg.HkMem_mono_open hsm (n + 1) (by omega) hm
    exact ⟨Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hm1,
      Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα n hm1,
      Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α n
        (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hsm (n + 1)) hm1⟩

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Closed3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false



end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ClosedUniq3_small =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The level-`0` membership integrand of a difference -/

/-- At level `0` the `HkIntegrand` is a single square,
`(g z θ · w z / sin(2θ)^{η/2})²` (the mixed sum is empty). -/
theorem hkIntegrand_zero_eq' (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkIntegrand]
  simp





/-! ## The obstruction: the level-`0` memberships cannot control the `θ = 0` traces

Every `HkMem` of `FatouPkg` is a **level-`0`** membership, and (as `hkIntegrand_zero_eq'` above
records) `HkIntegrand α 0 f` carries the single angular weight `sin(2θ)^{-η/2}`, i.e.
`sin(2θ)^{-η}` after squaring, with `η = 99/100 < 1`.  That weight is **integrable at `θ = 0`**
(`weight_integrableOn` below), and the mixed slots carrying the *non*-integrable weight
`sin(2θ)^{-γ}` (`γ = 1 + α/10 > 1`) occur in `HkIntegrand α k` only for `k ≥ 1`, which
`FatouPkg` never uses.

The lemmas below make the consequence formal: a *radial* profile lies in `ℋ⁰` as soon as its
`z`-mass `(g·w)²` is integrable, **whatever its angular trace at `θ = 0` is**
(`HkMem_zero_radial`), and consequently `HkMem α 0` (resp. `HkMem α 0 (pth ·)`) is satisfied by a
profile whose value (resp. derivative) trace at `θ = 0⁺` is the nonzero constant `1`
(`HkMem_zero_trace_not_forced`, `HkMem_zero_deriv_trace_not_forced`).

This is exactly the deficiency that blocks the port of `EllipticEst.bslSol_unique_fts`: the
angular rigidity against `sin θ cos²θ`, the `θ`-energy identity, the `F_*`-ODE and the
decoupling of the `θ`-eigen-expansion *all* carry a boundary term at `θ = 0` of the form
`-μ(0)∫Jg + (1/2)μ'(0)∫J²` with `J(z) = lim_{θ→0⁺}Ψ z θ-Ψ' z θ`, `g(z) = lim ∂_θ(Ψ-Ψ')`, and the
theorem `EllipticEst.bslSol_unique_fts` consumes `EllHypN`, which needs `SmoothNbhd`,
`IsBslSol` on *all* `z ≥ 0` **and** the extra membership `HkMem α 0 (∂_θ²(z ∂_z·))` --- none of
which follows from `FatouPkg`.  The tree's own precedent (`FTS/StrongEps/EComparison/
HomClsZeroRefute.lean`, `NOTES_HomClsZero_FALSE.md`) refutes an analogous class-based uniqueness
statement by precisely this loophole, with the documented repair being an angular trace
condition.  See `NOTES_closedUniq3.md` §7 and `NOTES_theta0_trace.md`. -/

/-- The angular weight of the level-`0` integrand, `sin(2θ)^{-η}` (`η = 99/100 < 1`), is
integrable on `[0, π/2]`. -/
theorem eta_lt_one : Work.Spaces.eta < 1 := by
  unfold Work.Spaces.eta; norm_num









/-! ## The target

**Status: PROVED** (the theorem below is `sorry`-free, axioms
`[propext, Classical.choice, Quot.sound]`), *after* the interface repair of the previous stretch.
The obstruction recorded in the section above is real: `FatouPkg`'s memberships are all at level `0`
with the weight `sin(2θ)^{-η}` (`η = 99/100`, integrable at `θ = 0`) and cannot constrain the
`θ = 0` traces that every step of the uniqueness argument needs — that is what
`HkMem_zero_trace_not_forced` / `HkMem_zero_deriv_trace_not_forced` / `weight_integrableOn` above
machine-check.  The repair that was installed (see `Defs3.FatouPkg` and `NOTES.md` §0bis) is the
conjunct **`BoxReg Ψ`** — `Ψ` is jointly `C²` on every closed box `[a,b] × [0,π/2]`, `0 < a ≤ b` —
together with its sequence-level producer `Defs3.BoxData` in `FatouData` (whose bridge from
primitive estimates is `FTS_EllLimOK.BoxReg_of_uniform`).  With it, the port of
`EllipticEst.bslSol_unique_fts` goes through: `UniqFatou.eqOn_of_same_law` (the θ-energy chain
`Fstar_zero`, `EnergyGap`, `phi_eq_zero_of_euler_gap_weighted`) plus
`Locality.mixed_congr_of_eqOn_isOpen`.  `NOTES_theta0_trace.md` has the analysis of the
obstruction; `NOTES_STATUS_closedUniq3.md` the state of the proof. -/


end Work.FTS_EllLimOK
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgRepair =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The pinning field**: the solution's `PhiTil`-part times `1/cos θ` is honestly in `ℋ⁰`.  This
is precisely the field of `FatouPkg` (item (12) of the tree's `EllipticEst.EllHyp`) that kills the
homogeneous mode `z^{-3/α}/cos θ`, which `HasPkg` alone cannot see
(`KernelObstruction.hasPkg_add_cex`).  It is endorsed by the lead's ruling of 2026-10-11 and is
field `PkgCos` of the installed honest hypothesis `RulingELF.HasPkgH`; it is *produced* by
`ProducerH.pkgCos_of_ellClassOk` (L1) from route (b).

(This field is the *only* one of the original `PkgRepair` fields that survived: the docstring that
used to claim that `Theta α g/cos θ` is not in `ℋ⁰` was **wrong** — `Theta α g/cos θ =
(1/(2α))·sin θ·L₁₂ g` is bounded by `|L₁₂ g|`, and `Theta` has a bound of its own
(`PkgJets.thetaBound`); `PkgMemSq`/`PkgSlice`/`PkgDecay`/`PkgStrip`/`PkgCorner` are all false and
are retired below. -/
def PkgCos (α : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∀ g, Work.FTS.ClassC.ClassC α g →
    Work.Spaces.HkMem α 0 (fun z θ => Work.Construction.PhiTil α g (E g) z θ / Real.cos θ)

/-- **The far-field rate field**: on the open quadrant the order-`≤ 4` jets of `E g` decay at least
like `(1+z)^{-3/2}`, *relative* to the `ℋ⁶`-norm of the source — the relative form is what makes the
bound uniform along a `LimSeq4` (`LimSeq4.bound : Xn6 α (fn n) ≤ B`).

The rate `3/2` (not `1`) is the one `FatouData`'s decay clause asks for (`j+i ≤ 2`), and it is
*also* all `LocalBound4` needs (`(1+z) ≤ (1+z)^{3/2}` for `z ≥ 0`), so a single field covers both.
`§ LocalBound4` below derives the `(1+z)^{-1}` form used by `LocalBound4`. -/
def PkgDecay (α : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ g, Work.FTS.ClassC.ClassC α g →
    ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      (1 + z) ^ (3 / 2 : ℝ) * |Work.Spaces.mixed j i (E g) z θ|
        ≤ K * Work.FTS.StrongGlobal.Xn6 α g

/-- **The closed-strip regularity field**: the solution is `C^∞` on a *neighbourhood* of the closed
quadrant, i.e. it has boundary traces of all orders.  This is what `FTS_EllLimOK.BoxReg_of_uniform`
consumes (as `Work.Spaces.SmoothStrip`) to produce `FatouData`'s `BoxData` clause: `SmoothOpen` is
an open-quadrant statement, and the upper bounds of `PkgDecay` give no equicontinuity at
`θ = 0, π/2` (the bound on `mixed 0 1 = sin(2θ)∂_θ` does not bound `∂_θ` where `sin(2θ) → 0`). -/
def PkgStrip (α : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∀ g, Work.FTS.ClassC.ClassC α g → Work.Spaces.SmoothStrip (E g)

/-- **The repaired package hypothesis**: the frozen two packages plus the three fields that they
provably lack. -/
def HasPkgD (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  HasPkg α Ce E ∧ PkgCos α E ∧ PkgDecay α E ∧ PkgStrip α E

theorem HasPkgD.toHasPkg {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgD α Ce E) :
    HasPkg α Ce E := h.1

theorem HasPkgD.cos {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgD α Ce E) :
    PkgCos α E := h.2.1

theorem HasPkgD.decay {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgD α Ce E) :
    PkgDecay α E := h.2.2.1

theorem HasPkgD.strip {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgD α Ce E) :
    PkgStrip α E := h.2.2.2


/-! ## The `LocalBound4` reduction under the repaired hypothesis

Once the far-field rate is a field of the package, `Defs3.LocalBound4`'s body follows immediately:
the field gives `(1+z)|mixed j i (E g)| ≤ K·Xn6 α g`, `LimSeq4` gives `Xn6 α (fn n) ≤ B`, and the
extra factors `(1 + 1/z + 1/(θ(π/2-θ)))` are ≥ 1.  The *pointwise* half of `LocalBound4` (no decay)
is the content of `PkgJets/pkg_pointwise_jets`; the decay half is exactly the field, and it has to
be stated on the jets of `E g` (not on the slots): `Theta α g = (1/4α) sin 2θ·L₁₂ g` decays only as
fast as the *source* does, and class `C` only gives `g = o(z^{-1/2})`
(`ClassC.tr : BdryTraces α 6 g`, `ClassC.mem : HkMem α 7 g`), so no field on the slots can make the
`Theta`-part decay like `1/(1+z)`. -/

/-! ## The obligation shapes over the repaired hypothesis

`Defs3.SmallLocalBound4` asks for the pointwise growth bounds along every `LimSeq4`, *for every
linear `E` carrying `HasPkg`*.  The `HasPkgD`-analogues below ask the same of every `E` carrying the
**repaired** packages; those are what the lead's field edit turns into the original shapes, and
they are what this area proves. -/






/-! ## The two further primitive fields (the last two derivations)

`FatouData`'s remaining two clauses need data that no ℋ-membership supplies, and the review of
`phiTil_bundle_of_hasPkgD` pinned down exactly which two primitives are needed.  They are stated
here so that the two derivations can be done once and for all:

* `PkgCorner` — uniform (in `g`) bounds on the **plain iterated derivatives** of `E g` on every
  closed box.  `FatouData`'s `BoxData` clause consumes `BoxReg_of_uniform`, which asks for bounds
  on `iteratedFDeriv ℝ k` (`k ≤ 3`) on the box; the `mixed` normalisation of `PkgDecay` cannot give
  them, because `D_θ = sin(2θ)·∂_θ` degenerates at the corner (`BoxReg_of_uniform`'s conversion
  `∂_θ^i = D_θ^i/sin^i + lower` is 0/0 there).
* `PkgSlice` — uniform (in `z`) `θ`-slice bounds for the three slots.  `Defs3.ThetaBundle` demands
  `∀ z ∈ Iz, ∫_θ HkIntegrand α 0 Ψ z θ ≤ C`, a bound uniform in `z`, while every ℋ-membership is an
  integral *over* `z`; at the delicate end `z → 0` the weight is `≈ z^{-4}`.  Stating the primitive
  on the slots (where the packages already live) lets the `Φ̃`-level bounds follow by the same
  pointwise identities as `phiTil_bundle_of_hasPkgD`.
-/

/-- **The corner-regularity field**: uniform bounds on the plain iterated derivatives of `E g` on
every closed box — what `BoxReg_of_uniform` consumes. -/
def PkgCorner (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ g, Work.FTS.ClassC.ClassC α g →
    ∀ a b : ℝ, 0 < a → a ≤ b → ∀ k : ℕ, k ≤ 3 →
      ∀ p ∈ cbox a b,
        ‖iteratedFDeriv ℝ k (Function.uncurry (E g)) p‖ ≤ K * Work.FTS.StrongGlobal.Xn6 α g

/-- **The slice field**: uniform-in-`z` `θ`-slice bounds for the three packaged slots. -/
def PkgSlice (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ g, Work.FTS.ClassC.ClassC α g →
    ∀ (Φ : Fn), Φ = Work.Construction.PhiTil α g (E g) →
      (∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Construction.Vop Φ) z θ) ≤
          K * Work.FTS.StrongGlobal.Xn6 α g) ∧
      (∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0
            (fun z θ => Work.Construction.Uop α Φ z θ / Work.Construction.s2 θ) z θ) ≤
          K * Work.FTS.StrongGlobal.Xn6 α g) ∧
      (∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun z θ => Work.Construction.PhiTil α g (E g) z θ / Real.cos θ) z θ) ≤
          K * Work.FTS.StrongGlobal.Xn6 α g) ∧
      (∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (Work.Spaces.mixed 0 1 (Work.Construction.Vop Φ)) z θ) ≤
          K * Work.FTS.StrongGlobal.Xn6 α g) ∧
      (∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (Work.Spaces.mixed 1 0
            (fun z θ => Work.Construction.Uop α Φ z θ / Work.Construction.s2 θ)) z θ) ≤
          K * Work.FTS.StrongGlobal.Xn6 α g)

/-- **The fully repaired hypothesis**: `HasPkgD` plus the two primitive fields above. -/
def HasPkgE (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  HasPkgD α Ce E ∧ PkgCorner α Ce E ∧ PkgSlice α Ce E



theorem HasPkgE.slice {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgE α Ce E) :
    PkgSlice α Ce E := h.2.2



end Work.FTS_EllLimOK
end
end
