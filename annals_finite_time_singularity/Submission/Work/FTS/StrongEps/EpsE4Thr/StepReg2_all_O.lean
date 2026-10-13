/-
Copyright: work module for the Elgindi finite-time singularity project.

# `StepReg2_all_O` — the regularity ports of the open-class coercivity step, in full

`Work.FTS.StrongEps.EpsE4Thr.StepReg2O α n` (`EpsE4Thr/StepDataO.lean`) is the open-class
(`RegQo`-based) analogue of `Work.FTS.CoercivityFix.Assembly.StepReg2 α n`: the bundle of
*regularity ports* consumed by the re-stated step of the open-class re-run of the coercivity
chapter (`StepCoerO.step_coer_O`, `step2_data_ge_O`).  This file supplies the whole bundle.

The table of fields (compare `CoercivityFix/Assembly/StepReg2_all.lean` for the frozen twin):

| field | reason |
|---|---|
| `mono1`, `mono2` | monotonicity of `RegQo` in the order (`OpenClass.regQo_mono`) |
| `dth1`, `dz1` | the two open-class ports `regQo_dth_dz` |
| `dth2`, `dz2` | `dth1`/`dz1` followed by `regQo_mono` down to `n` |
| `ldz` | `regQo_dth_dz` followed by the open-class port of `Lhat` proved below |
| `e2r` | the open-class port of the defect `Ê₂` proved below |
| `normSub` | the `SmoothOpen` versions of `HkSq_mono_le`, `HkSq_Dth_le` and the `D_z`-shift `HkSq_Dz_le_Q0Sm` |

## The two substantive fields

`Lhat_RegQo_aux` and `E2hat_RegQo_aux` (private, since the frozen twins already exist under the
names `CoercivityFix.Assembly.Lhat_RegQ` / `E2hat_RegQ`) are the open-class memberships

  `RegQo α (m+1) f → RegQo α m (𝓛̂ f)`,   `RegQo α (m+1) f → RegQo α m (Ê₂ f)`.

`RegQo α k f = SmoothOpen f ∧ HkMem α k f ∧ BdryTraces α k f`, and each of the three components
is available at general level:

* smoothness: `H6Aux.smoothOpen_Lhat` for `𝓛̂`, and the sum `Ê₂ f = 2(φ·f) + 3(φ·D_θ f)`
  (`φ(z) = z/(1+z)²`) is closed by `E2hatOAux.smoothOpen_{zOnly,mul,const_mul}` and
  `EllipticEst.smoothOpen_add`;
* `ℋ^m`-membership: the *proved* pointwise integrand domination `H6Aux.Lhat_HkIntegrand_le` for
  `𝓛̂`, resp. the α-uniform `E2hatOAux.E2hat_HkIntegrand_le_uniform_pt` for `Ê₂`, promoted to an
  honesty statement by `LocData.HkMem_of_majorant` (the dominating integrand is extended from the
  open quadrant to `Iz × Iθ` by the vanishing of `HkIntegrand` on the two boundary lines);
* boundary traces: `Œ` is `f + D_z f − 2·ψf − 3·ψD_θf` with `ψ(z) = 1/(1+z)`, resp.
  `Ê₂ f = 2(φ·f) + 3(φ·D_θf)`; the two radial multiples are handled by the *open* radial-multiplier
  trace lemma `TracesAux.BdryTraces_psi_mul_open` (with the `Zop`-iterate bounds
  `PsiMul.zop_psi_bound` resp. `E2Bound.SlotMul.Zop_iterate_phiZ_bound`), and the linear
  combinations by `ClassC.bdryTraces_add` / `bdryTraces_smul` on open-quadrant smooth data.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.StepDataO
import Submission.Work.FTS.CoercivityFix.Assembly.StepReg2_all
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dth
import Submission.Work.FTS.CoercivityFix.Assembly.Lhat_RegQ
import Submission.Work.FTS.CoercivityFix.Assembly.E2hat_RegQ
import Submission.Work.FTS.StrongPersist.H6Aux.Facts
import Submission.Work.FTS.StrongPersist.H6Aux.LhatFacts
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.PtBound
import Submission.Work.FTS.CoercivityFix.PsiMul.PsiZop
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_phiZ_bound
import Submission.Work.FTS.CoercivityFix.E2Bound.E2hat_HkIntegrand_le_uniform
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.CoercivityFix.Assembly.RegQAux
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dth_le
import Submission.Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd

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
