import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.Jeps_IP6_transfer_aux
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.SlotSumRadAOpen
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.H6Aux.RStep
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAsm
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0_mem6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkSmooth
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.ProdRadSupO
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.StrongPersist.hasDerivAt_wip_family
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.classCSinRate
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds
import Submission.Work.FTS_RegExport.RXR5L.mubarData
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS_RegExport.RXT.coeff_C2
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.RXT0.RXJets.jetBasic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.FTS_StreamBdry.SB4.Thetapart_dz_bound
import Submission.Work.FTS_StreamBdry.SB4.near0Core
import Submission.Work.FTS_StreamBdry.SB4.slice_L12_c2
import Submission.Work.FTS_StreamBdry.SB6.clauses3
import Submission.Work.FTS_StreamBdry.sb5_barrier_proved
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.JepsIP6Transfer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/JepsIP6Transfer.lean` — OPEN LEAF S1 (research-low)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling.md` §3 S1; REVIEW (b)).
Weighted near-self-adjointness of a symmetric `J_ε` at level six, with NO derivative loss — the
bilinear twin of `HkSq_Jeps_le`.  NOTE: the tree's `HkPair_Jeps_comm` / `IP6_Jeps_diff_le` both
lose a derivative (`k+1`) and are NOT this statement.
Route: in the log coordinates `(s, ζ) = (log z, log tan θ)` `J_ε` is convolution over all of `ℝ²`
with an even kernel (exactly self-adjoint for `ds dζ`), commutes with `D_z = ∂_s`, `D_θ = 2∂_t`
(`Commute.Dz_Jeps`, `Dth_Jeps`), and every weight of `IP6 1…1` times the Jacobian `z·sin2θ/2` is
log-Lipschitz (`HkSqAux.wdiv_shift_le`, `Wt_shift_le`, `logJac_shift_le`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps

set_option autoImplicit false


end Work.FTS.StrongEps.EpsE4Thr.E4R4
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Jeps_mixed_continuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The kernel-side iterates vanish off an open set on which the kernel vanishes -/





/-! ## Continuity of the routed integral on the closed slab -/


/-! ## The routed form of the mixed slots -/


/-! ## The target -/


end Work.FTS.StrongEps.E4R3.Apriori4Proofs
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.L6Ctx_JfamP_proof =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Proofs/L6Ctx_JfamP_proof.lean` — the level-six context at the projected
mollified slices

The seven fields of `StrongPersist.L6Ctx` at `slice (JfamP ρ ε g) τ`, from the `ClassC`-hypothesis
on the slice, the `ℋ⁴`-ball bound, the elliptic package `hEll` and the order-six star package
`StarPkg6`:

* `hreg` — `H6Adm` from `ClassC` (`H6Adm_of_classC_of_eqzero`), the vanishing off the open
  quadrant being inherited from `Pz ∘ J_ε` (`Jeps_eq_zero`, `bump_support`);
* `h7` — `ClassC.mem`;
* `hbdd` — a hypothesis;
* `hell` — `Ell6Ctx_of_classC`;
* `hstar6` — a hypothesis;
* `hrhs` — `dynRHS` sees the families only through their `τ`-slices, so it is the modulation
  right-hand side at `F = F_* + f`, `Φ = Φ_s + E f`, `g = f`; its `C^∞`-regularity is the atom
  assembly of `smoothOpen_N0_gen`/`smoothOpen_N_gen`/`smoothOpen_gRHS_gen` (the all-order
  smoothness of `L₁₂ f` coming from `smoothOpen_L12_radial` and of `FK f` from `ClassC.fsm` via
  `fk_eq_three_Fstar`), and its `ℋ⁶`-honesty comes from the proved pieces (`N0_mem6`,
  `AK6_mem_norm` and the delegated `NMem6Parts`) joined by the `ℋ⁶`-additivity chain;
* `hsplit` — `H6Split_IP6_of_adm`, from `H6LinMem6`, the `C⁶`-smoothness of `linPart`
  (`linPart_contDiffOn_six`) and `hrhs`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The vanishing of the projected mollified profile off the open quadrant -/

/-- `P₀(J_ε h)` vanishes off the open quadrant: `J_ε h` does, and the correction profile `bump`
is supported inside `(1/2,1) × (π/8,π/2) ⊂ Q₀`. -/
theorem Pz_Jeps_eq_zero_of_not_mem_quadrant {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {h : Fn} {z θ : ℝ}
    (hz : ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2))) :
    Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h) z θ = 0 := by
  rw [Work.FTS.StrongEps.Pz_apply]
  have hJ : Work.FTS.StrongEps.Jeps ρ ε h z θ = 0 :=
    Work.FTS.StrongEps.Jeps_eq_zero ρ ε h hz
  have hB : Work.FTS.StrongEps.bump z θ = 0 := by
    by_contra hne
    obtain ⟨hzs, hθs⟩ := Work.FTS.StrongEps.bump_support hne
    exact hz ⟨lt_trans (by norm_num) hzs.1,
      lt_trans (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 8) hθs.1, hθs.2⟩
  rw [hJ, hB, mul_zero, sub_zero]

/-! ## The finite-order smoothness of `linPart` -/

/-- **`linPart α f` is `C⁶` on the open quadrant** as soon as `f` is `C^∞` there and the radial
function `z ↦ L₁₂(f)(z)` is `C^∞` on `(0,∞)`: the finite-order (`n = 6`) instance of
`smoothOpen_linPart`, using `linPart α f = -𝓛_Γ^T f` definitionally. -/
theorem linPart_contDiffOn_six {α : ℝ} {f : Fn}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    (hL12 : ∀ n : ℕ, ContDiffOn ℝ n (Work.Coercivity.L12f f) (Set.Ioi 0)) :
    ContDiffOn ℝ 6 (Function.uncurry (Work.FTS.StrongPersist.linPart α f))
      Work.FTS.EllipticEst.Q0 := by
  have h := Work.FTS.StrongEps.smoothOpen_linPart (α := α) (f := f) hf hL12 6
  show ContDiffOn ℝ 6 (fun p : ℝ × ℝ => -(Work.Coercivity.LGammaT α f p.1 p.2))
    Work.FTS.EllipticEst.Q0
  exact h.neg

/-! ## The level-six context -/

theorem L6Ctx_JfamP_proof :
    ∀ C₀ Ce Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀,
    ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn},
    Work.FTS.StrongEps.IsSmoothKernel ρ →
    (∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs → Work.FTS.StrongEps.MuLamOK α C₀ Φs E →
    ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ (g : Work.FTS.Galerkin.Fam) (τ : ℝ), 0 ≤ τ →
      Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
      Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o) α (C₀ * α ^ 2) Ce Cs E Φs
        (Work.FTS.StrongEps.JfamP ρ ε g) (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ := by
  intro C₀ Ce Cs
  obtain ⟨α20, hα20pos, hα20le, hN0mem6⟩ := Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0_mem6
  obtain ⟨α2L, hα2Lpos, hLmem6⟩ := Work.FTS.StrongPersist.H6LinMem6
  obtain ⟨α2N, hα2Npos, hα2Nle, hNmem6⟩ := NMem6Parts Ce
  obtain ⟨KAK, hKAKpos, hAKnorm⟩ := Work.FTS.StrongPersist.AK6_mem_norm
  refine ⟨min 1 (min α20 (min α2L α2N)),
    lt_min one_pos (lt_min hα20pos (lt_min hα2Lpos hα2Npos)), ?_⟩
  intro α hαIoc
  obtain ⟨hαpos, hαle⟩ := Set.mem_Ioc.mp hαIoc
  have hα1 : α ≤ 1 := le_trans hαle (min_le_left _ _)
  have hα20' : α ≤ α20 := le_trans hαle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hα2L' : α ≤ α2L := le_trans hαle (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hα2N' : α ≤ α2N := le_trans hαle (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_right _ _)))
  intro ρ Φs E hρ hEll hstar6 hMuLam ε hε g τ hτ hclass hbdd
  set F : Fam := Work.FTS.StrongEps.JfamP ρ ε g with hF
  set Φ : Fam := Work.FTS.Nonlin.PsiCan Φs E F with hPhi
  -- ## the standing data at the slice
  have hclassF : Work.FTS.ClassC.ClassC α (slice F τ) := by rw [hF]; exact hclass
  have hbddF : Work.FTS.Nonlin.Xn α (slice F τ) ≤ C₀ * α ^ 2 := by rw [hF]; exact hbdd
  have hEf : Work.FTS.VocabO.EllPkgGo α Ce (slice F τ) (E (slice F τ)) ∧
      Work.FTS.ClassC.EllPkgK α 6 Ce (slice F τ) (E (slice F τ)) :=
    hEll (slice F τ) hclassF
  have hstarPkgo2 : Work.FTS.VocabO2.StarPkgo2 α Cs Φs := hstar6.toStarPkgo2
  have hellCtx : Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs (slice F τ)
      (fun z θ => Φs z θ + E (slice F τ) z θ) :=
    Work.FTS.StrongEps.Ell6Ctx_of_classC hEll hstarPkgo2 hclassF
  have hPhislice : slice Φ τ = (fun z θ => Φs z θ + E (slice F τ) z θ) := by
    rw [hPhi]; rfl
  have hregS : Work.FTS.EllipticEst.SmoothOpen (slice F τ) := hclassF.reg
  have hFtau : Work.Construction.Ftau α F τ = Work.Construction.Ftot α (slice F τ) := by
    funext z θ
    simp only [Work.Construction.Ftau, Work.Construction.Ftot, Work.FTS.Galerkin.slice]
  -- ## the `H6Adm` field
  have hreg : Work.FTS.StrongPersist.H6Adm α (slice F τ) := by
    refine Work.FTS.StrongEps.H6Adm_of_classC_of_eqzero hclassF ?_
    intro z θ hz
    show Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (slice g τ)) z θ = 0
    exact Pz_Jeps_eq_zero_of_not_mem_quadrant hz
  have h7 : Work.Spaces.HkMem α 7 (slice F τ) := hclassF.mem
  have hm6 : Work.Spaces.HkMem α 6 (slice F τ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hregS 6 (by norm_num) h7
  -- ## the smoothness of the modulation right-hand side
  set mu : ℝ := Work.FTS.Galerkin.muDyn α Φ F τ with hmu
  set lam : ℝ := Work.FTS.Galerkin.lamDyn α Φ F τ with hlam
  set mb : ℝ := Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftot α (slice F τ)) (slice F τ))
      (Work.Construction.N α (Work.Construction.Ftot α (slice F τ))
        (fun z θ => Φs z θ + E (slice F τ) z θ)) with hmb
  have hΦsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Φs z θ + E (slice F τ) z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_add hstar6.smooth hEf.1.smooth
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Ftot α (slice F τ)) :=
    Work.FTS.StrongPersist.H6Rows.so_congr
      (Work.FTS.StrongPersist.H6Pair6Aux.so_add
        (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α) hclassF.reg)
      (fun _ _ _ _ _ => rfl)
  have hL12fsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (slice F τ) z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hαpos hEf.1.smooth hEf.1.V.1.1
  have hL12Fsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Ftot α (slice F τ)) z) :=
    Work.FTS.StrongPersist.H6Rows.so_congr
      (Work.FTS.StrongPersist.H6Pair6Aux.so_add
        (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α) hL12fsm)
      (fun z _ hz _ _ => Work.FTS.StrongPersist.L3Rhs.L3RhsL12add α ⟨hαpos, hα1⟩
        (slice F τ) hreg z hz)
  have hFKfstar : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z) := by
    have hrad : ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => α * (2 * z / (1 + z) ^ 2))
        (Set.Ioi 0) := by
      intro n
      refine contDiffOn_const.mul ?_
      exact (contDiffOn_const.mul contDiffOn_id).div
        ((contDiffOn_const.add contDiffOn_id).pow 2)
        (fun z hz => pow_ne_zero 2 (ne_of_gt (by have h := Set.mem_Ioi.mp hz; linarith)))
    refine Work.FTS.StrongPersist.H6Rows.so_congr
      (Work.FTS.NonlinRows.smoothOpen_radial (r := fun z : ℝ => α * (2 * z / (1 + z) ^ 2)) hrad)
      (fun z _ _ _ _ => Work.FTS.Nonlinear.FstarPkg.FK_Fstar hαpos hα1)
  have hFKf : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (slice F τ) z) := by
    have hrad : ∀ n : ℕ, ContDiffOn ℝ n
        (fun z : ℝ => 3 * Work.Elliptic.Fstar (slice F τ) z) (Set.Ioi 0) :=
      fun n => (hclassF.fsm n).const_smul (3 : ℝ)
    refine Work.FTS.StrongPersist.H6Rows.so_congr
      (Work.FTS.NonlinRows.smoothOpen_radial
        (r := fun z : ℝ => 3 * Work.Elliptic.Fstar (slice F τ) z) hrad)
      (fun z _ _ _ _ => congrFun
        (Work.FTS.StrongPersist.L3Rhs.NfkAux.fk_eq_three_Fstar (slice F τ)) z)
  have hFKsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Ftot α (slice F τ)) z) :=
    Work.FTS.StrongPersist.H6Rows.so_congr
      (Work.FTS.StrongPersist.H6Pair6Aux.so_add hFKfstar hFKf)
      (fun z _ hz _ _ => Work.FTS.StrongPersist.L3Rhs.L3RhsFKadd α ⟨hαpos, hα1⟩
        (slice F τ) hreg z hz)
  have hΞsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α (Work.Construction.Ftot α (slice F τ))
        (fun z θ => Φs z θ + E (slice F τ) z θ)) :=
    Work.FTS.StrongPersist.H6Rows.h6rows_so_PhiTil hΦsm hL12Fsm
  have hRsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α
      (Work.Construction.PhiTil α (Work.Construction.Ftot α (slice F τ))
        (fun z θ => Φs z θ + E (slice F τ) z θ))) :=
    Work.FTS.NonlinRows.smoothOpen_Rop hΞsm
  have hUsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Uop α
      (Work.Construction.PhiTil α (Work.Construction.Ftot α (slice F τ))
        (fun z θ => Φs z θ + E (slice F τ) z θ))) :=
    Work.FTS.StrongPersist.H6Rows.h6rows_so_Uop hΞsm
  have hVsmN : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop
      (Work.Construction.PhiTil α (Work.Construction.Ftot α (slice F τ))
        (fun z θ => Φs z θ + E (slice F τ) z θ))) :=
    Work.FTS.StrongPersist.H6Rows.h6rows_so_Vop hΞsm
  have hN0sm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.N0 α (Work.Construction.Ftot α (slice F τ)) (slice F τ)) :=
    Work.FTS.StrongPersist.H6Rows.so_congr
      (Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0 hαpos hclassF.reg hL12fsm)
      (fun _ _ _ _ _ => rfl)
  have hNsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.N α
      (Work.Construction.Ftot α (slice F τ)) (fun z θ => Φs z θ + E (slice F τ) z θ)) :=
    Work.FTS.StrongEps.smoothOpen_N_gen hFsm hFKsm hRsm hUsm hVsmN
  have hNstarsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Nstar mu lam (slice F τ)) :=
    Work.FTS.GalFields.RHS.smoothOpen_Nstar_of hclassF.reg
  have hAKcsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => -mb * Work.Construction.AK α z θ) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (-mb) (Work.FTS.StrongPersist.AK_smoothO α)
  have hgRHSsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.gRHS α mu lam
      (Work.Construction.Ftot α (slice F τ))
      (fun z θ => Φs z θ + E (slice F τ) z θ) (slice F τ)) :=
    Work.FTS.StrongEps.smoothOpen_gRHS_gen hFsm hclassF.reg hL12fsm hFKsm hRsm hUsm hVsmN
  -- ## the `ℋ⁶`-honesty of the modulation right-hand side
  have hAK6 : Work.Spaces.HkMem α 6 (Work.Construction.AK α) := (hAKnorm α hαpos hα1).1
  have hmbm : Work.Spaces.HkMem α 6 (fun z θ => -mb * Work.Construction.AK α z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 (-mb) hAK6
  have hN0m : Work.Spaces.HkMem α 6
      (Work.Construction.N0 α (Work.Construction.Ftot α (slice F τ)) (slice F τ)) := by
    have h := hN0mem6 α ⟨hαpos, hα20'⟩ (slice F τ) hreg h7
    show Work.Spaces.HkMem α 6 (Work.Construction.N0 α
      (fun z θ => Work.Construction.Fstar α z θ + slice F τ z θ) (slice F τ))
    exact h
  have hNm : Work.Spaces.HkMem α 6 (Work.Construction.N α
      (Work.Construction.Ftot α (slice F τ))
      (fun z θ => Φs z θ + E (slice F τ) z θ)) :=
    (hNmem6 α ⟨hαpos, hα2N'⟩ hreg h7 hEf.1.smooth hstar6.smooth hellCtx.hell hstar6).2
  have hNstarm : Work.Spaces.HkMem α 6 (Work.Construction.Nstar mu lam (slice F τ)) := by
    have hDz : Work.Spaces.HkMem α 6 (Work.Spaces.Dz (slice F τ)) :=
      Work.FTS.IPGen.HkMem_Dz_le (k := 6) hregS h7
    have h1 : Work.Spaces.HkMem α 6 (fun z θ => (-mu) * slice F τ z θ) :=
      Work.FTS.LocData.HkMem_const_mul α 6 (-mu) hm6
    have h2 : Work.Spaces.HkMem α 6
        (fun z θ => (-(mu + lam + mu * lam)) * Work.Spaces.Dz (slice F τ) z θ) :=
      Work.FTS.LocData.HkMem_const_mul α 6 (-(mu + lam + mu * lam)) hDz
    have h1s : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (-mu) * slice F τ z θ) :=
      Work.FTS.NonlinRows.smoothOpen_const_mul (-mu) hregS
    have h2s : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(mu + lam + mu * lam)) * Work.Spaces.Dz (slice F τ) z θ) :=
      Work.FTS.NonlinRows.smoothOpen_const_mul _ hregS.Dz
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 6
      (Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 6 h1s h2s h1 h2) ?_
    intro z hz θ hθ
    show (-mu) * slice F τ z θ + (-(mu + lam + mu * lam)) * Work.Spaces.Dz (slice F τ) z θ
      = Work.Construction.Nstar mu lam (slice F τ) z θ
    simp only [Work.Construction.Nstar]
    ring
  have hgRHSm : Work.Spaces.HkMem α 6 (Work.Construction.gRHS α mu lam
      (Work.Construction.Ftot α (slice F τ))
      (fun z θ => Φs z θ + E (slice F τ) z θ) (slice F τ)) := by
    have h12 := Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 6 hAKcsm hN0sm hmbm hN0m
    have h123 := Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 6
      (Work.FTS.EllipticEst.smoothOpen_add hAKcsm hN0sm) hNsm h12 hNm
    have h1234 := Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 6
      (Work.FTS.EllipticEst.smoothOpen_add
        (Work.FTS.EllipticEst.smoothOpen_add hAKcsm hN0sm) hNsm) hNstarsm h123 hNstarm
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 6 h1234 ?_
    intro z hz θ hθ
    show -mb * Work.Construction.AK α z θ
        + Work.Construction.N0 α (Work.Construction.Ftot α (slice F τ)) (slice F τ) z θ
        + Work.Construction.N α (Work.Construction.Ftot α (slice F τ))
            (fun z θ => Φs z θ + E (slice F τ) z θ) z θ
        + Work.Construction.Nstar mu lam (slice F τ) z θ
      = Work.Construction.gRHS α mu lam (Work.Construction.Ftot α (slice F τ))
          (fun z θ => Φs z θ + E (slice F τ) z θ) (slice F τ) z θ
    rw [hmb]
    simp only [Work.Construction.gRHS]
  -- ## the `hrhs` field
  have hr : Work.FTS.VocabO.HQo α 6 (Work.FTS.Galerkin.dynRHS α Φ F τ) := by
    have hdyn : Work.FTS.Galerkin.dynRHS α Φ F τ = Work.Construction.gRHS α mu lam
        (Work.Construction.Ftot α (slice F τ))
        (fun z θ => Φs z θ + E (slice F τ) z θ) (slice F τ) := by
      show Work.Construction.gRHS α (Work.FTS.Galerkin.muDyn α Φ F τ)
          (Work.FTS.Galerkin.lamDyn α Φ F τ) (Work.Construction.Ftau α F τ)
          (slice Φ τ) (slice F τ) = _
      rw [hmu, hlam, hFtau, hPhislice]
    rw [hdyn]
    exact ⟨hgRHSsm, hgRHSm⟩
  -- ## the `hsplit` field
  have hfall : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (slice F τ)) Work.FTS.StrongEps.Quad :=
    fun n => hregS.forall n
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (slice F τ) z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hαpos hEf.1.smooth hEf.1.V.1.1
  have hL12all : ∀ n : ℕ, ContDiffOn ℝ n (Work.Coercivity.L12f (slice F τ)) (Set.Ioi 0) := by
    intro n
    have h := Work.FTS.GalFields.Norm.curry_z_nat_of_smoothOpen hL12sm (θ := Real.pi / 4)
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ n
    show ContDiffOn ℝ n (fun z => Work.FM.L12 Work.Spaces.K (slice F τ) z) (Set.Ioi 0)
    exact h
  have hlc : ContDiffOn ℝ 6 (Function.uncurry (Work.FTS.StrongPersist.linPart α (slice F τ)))
      Work.FTS.EllipticEst.Q0 := linPart_contDiffOn_six hfall hL12all
  have hmlin : Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.linPart α (slice F τ)) :=
    hLmem6 α ⟨hαpos, hα2L'⟩ (slice F τ) hreg h7
  have hsplit : Work.FTS.StrongPersist.H6Split (Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o) α
      (slice F τ) (Work.FTS.Galerkin.dynRHS α Φ F τ) :=
    Work.FTS.StrongPersist.H6Split_IP6_of_adm hαpos hreg hr hlc hmlin
  -- ## the `hell` field
  have hell : Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs (slice F τ) (slice Φ τ) := by
    rw [hPhislice]
    exact hellCtx
  exact ⟨hreg, h7, hbddF, hsplit, hr, hell, hstar6⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem N0_HkSq4_le : ∀ C₀ : ℝ, ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w)
      ≤ K * (1 + Work.Spaces.HkSq α 5 w) := by
  intro C₀
  obtain ⟨K1, hK1pos, hNA1⟩ := NA1_HkSq4_le C₀
  obtain ⟨K3, hK3pos, hNP3⟩ := NP3_HkSq4_le C₀
  obtain ⟨K4a, hK4apos, hNP4a⟩ := NP4a_HkSq4_le C₀
  obtain ⟨K4b, hK4bpos, hNP4b⟩ := NP4b_HkSq4_le C₀
  obtain ⟨K5a, hK5apos, hNP5a⟩ := NP5a_HkSq4_le C₀
  obtain ⟨K56, hK56pos, hNP56⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.NP5b_NP6_HkSq4 C₀
  refine ⟨64 * (K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56)))))) + 1,
    by have h : 0 ≤ K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56))))) :=
         add_nonneg hK1pos.le (add_nonneg hK3pos.le (add_nonneg hK4apos.le
           (add_nonneg hK4bpos.le (add_nonneg hK5apos.le (add_nonneg hK56pos.le hK56pos.le)))))
       nlinarith, ?_⟩
  intro α hαIoc w hw hXw
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hm7 : Work.Spaces.HkMem α 7 w := hw.mem
  have hm6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 6 (by norm_num) hm7
  have hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw
  have hFstar : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hs1 : Work.FTS.EllipticEst.SmoothOpen (NA1 α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA1 α
  have hs2 : Work.FTS.EllipticEst.SmoothOpen (NP3 α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP3 hsmw hL
  have hs3 : Work.FTS.EllipticEst.SmoothOpen (NP4a α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP4a hsmw hL
  have hs4 : Work.FTS.EllipticEst.SmoothOpen (NP4b α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP4b hsmw hL
  have hs5 : Work.FTS.EllipticEst.SmoothOpen (NP5a α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP5a hsmw hL
  have hs6 : Work.FTS.EllipticEst.SmoothOpen (NP5b α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP5b hsmw hL
  have hs7 : Work.FTS.EllipticEst.SmoothOpen (NP6 α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP6 hsmw hL
  obtain ⟨_K12, _hK12, hNA1six⟩ := Work.FTS.StrongPersist.H6Rows.FstarI12H6
  obtain ⟨hNA1mem6, _hNA1bd⟩ := hNA1six α hα hα1
  have hm1 : Work.Spaces.HkMem α 4 (NA1 α) :=
    Work.FTS.OpenPkg.HkMem_mono_open hs1 4 (by norm_num) hNA1mem6
  obtain ⟨hP3, hP4a, hP4b, hP5a, hP5b, hP6⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.hkmem_N0pieces_own hα hα1 hsmw hL hw.l12 hm6 hm7
  have hm2 : Work.Spaces.HkMem α 4 (NP3 α w) :=
    Work.FTS.OpenPkg.HkMem_mono_open hs2 4 (by norm_num) hP3
  have hm3 : Work.Spaces.HkMem α 4 (NP4a α w) :=
    Work.FTS.OpenPkg.HkMem_mono_open hs3 4 (by norm_num) hP4a
  have hm4 : Work.Spaces.HkMem α 4 (NP4b α w) :=
    Work.FTS.OpenPkg.HkMem_mono_open hs4 4 (by norm_num) hP4b
  have hm5 : Work.Spaces.HkMem α 4 (NP5a α w) :=
    Work.FTS.OpenPkg.HkMem_mono_open hs5 4 (by norm_num) hP5a
  have hm6p : Work.Spaces.HkMem α 4 (NP5b α w) :=
    Work.FTS.OpenPkg.HkMem_mono_open hs6 4 (by norm_num) hP5b
  have hm7p : Work.Spaces.HkMem α 4 (NP6 α w) :=
    Work.FTS.OpenPkg.HkMem_mono_open hs7 4 (by norm_num) hP6
  -- the split identity
  have hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w z θ
        = NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ + (NP4b α w z θ
            + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ))))) := by
    intro z θ hz hθ0 hθ1
    exact N0_split_open α hFstar hsmw z θ ⟨hz, hθ0, hθ1⟩
  have hsum := hkSq_sum7_le (α := α) (k := 4) hα hs1 hs2 hs3 hs4 hs5 hs6 hs7
    hm1 hm2 hm3 hm4 hm5 hm6p hm7p
  have hcongr : Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w)
      = Work.Spaces.HkSq α 4 (fun z θ => NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ
          + (NP4b α w z θ + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ)))))) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4 hid
  -- the individual level-`4` bounds
  have h5w : (0 : ℝ) ≤ Work.Spaces.HkSq α 5 w := Work.Spaces.HkSq_nonneg α 5 w
  have hone : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by linarith
  have hb1 : Work.Spaces.HkSq α 4 (NA1 α) ≤ K1 * (1 + Work.Spaces.HkSq α 5 w) :=
    hNA1 α hαIoc w hw hXw
  have hb2 : Work.Spaces.HkSq α 4 (NP3 α w) ≤ K3 * (1 + Work.Spaces.HkSq α 5 w) :=
    hNP3 α hαIoc w hw hXw
  have hb3 : Work.Spaces.HkSq α 4 (NP4a α w) ≤ K4a * (1 + Work.Spaces.HkSq α 5 w) :=
    hNP4a α hαIoc w hw hXw
  have hb4 : Work.Spaces.HkSq α 4 (NP4b α w) ≤ K4b * (1 + Work.Spaces.HkSq α 5 w) :=
    hNP4b α hαIoc w hw hXw
  have hb5 : Work.Spaces.HkSq α 4 (NP5a α w) ≤ K5a * (1 + Work.Spaces.HkSq α 5 w) :=
    hNP5a α hαIoc w hw hXw
  have hb6 : Work.Spaces.HkSq α 4 (NP5b α w) ≤ K56 * (1 + Work.Spaces.HkSq α 5 w) :=
    (hNP56 α hαIoc w hw hXw).1
  have hb7 : Work.Spaces.HkSq α 4 (NP6 α w) ≤ K56 * (1 + Work.Spaces.HkSq α 5 w) :=
    (hNP56 α hαIoc w hw hXw).2
  have hsum2 : Work.Spaces.HkSq α 4 (NA1 α) + Work.Spaces.HkSq α 4 (NP3 α w)
      + Work.Spaces.HkSq α 4 (NP4a α w) + Work.Spaces.HkSq α 4 (NP4b α w)
      + Work.Spaces.HkSq α 4 (NP5a α w) + Work.Spaces.HkSq α 4 (NP5b α w)
      + Work.Spaces.HkSq α 4 (NP6 α w)
      ≤ (K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56)))))) * (1 + Work.Spaces.HkSq α 5 w) := by
    nlinarith [hb1, hb2, hb3, hb4, hb5, hb6, hb7, h5w]
  have hKnn : (0 : ℝ) ≤ K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56))))) :=
    add_nonneg hK1pos.le (add_nonneg hK3pos.le (add_nonneg hK4apos.le
      (add_nonneg hK4bpos.le (add_nonneg hK5apos.le (add_nonneg hK56pos.le hK56pos.le)))))
  have htot : Work.Spaces.HkSq α 4 (fun z θ => NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ
        + (NP4b α w z θ + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ))))))
      ≤ 64 * ((K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56))))))
          * (1 + Work.Spaces.HkSq α 5 w)) :=
    le_trans hsum (mul_le_mul_of_nonneg_left hsum2 (by norm_num))
  have hfin : 64 * ((K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56))))))
        * (1 + Work.Spaces.HkSq α 5 w))
      ≤ (64 * (K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56)))))) + 1)
        * (1 + Work.Spaces.HkSq α 5 w) := by
    nlinarith [h5w, hKnn]
  calc Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w)
      = Work.Spaces.HkSq α 4 (fun z θ => NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ
          + (NP4b α w z θ + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ)))))) := hcongr
    _ ≤ 64 * ((K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56))))))
          * (1 + Work.Spaces.HkSq α 5 w)) := htot
    _ ≤ (64 * (K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56)))))) + 1)
        * (1 + Work.Spaces.HkSq α 5 w) := hfin

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem N0_HkSq6_le : ∀ C₀ : ℝ, ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w)
      ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
  intro C₀
  obtain ⟨K12, hK12pos, hNA1⟩ := Work.FTS.StrongPersist.H6Rows.FstarI12H6
  obtain ⟨Ka, hKapos, hb34⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.NP3_NP4b_HkSq6 C₀
  obtain ⟨Kb, hKbpos, hb56⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.NP5b_NP6_HkSq6 C₀
  obtain ⟨Kc, hKcpos, hb45a⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05a_HkSq6 C₀
  refine ⟨64 * (K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) + 1, by positivity, ?_⟩
  intro α hαIoc w hw hXw
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hm7 : Work.Spaces.HkMem α 7 w := hw.mem
  have hm6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 6 (by norm_num) hm7
  have hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw
  have hFstar : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hs1 : Work.FTS.EllipticEst.SmoothOpen (NA1 α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA1 α
  have hs2 : Work.FTS.EllipticEst.SmoothOpen (NP3 α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP3 hsmw hL
  have hs3 : Work.FTS.EllipticEst.SmoothOpen (NP4a α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP4a hsmw hL
  have hs4 : Work.FTS.EllipticEst.SmoothOpen (NP4b α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP4b hsmw hL
  have hs5 : Work.FTS.EllipticEst.SmoothOpen (NP5a α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP5a hsmw hL
  have hs6 : Work.FTS.EllipticEst.SmoothOpen (NP5b α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP5b hsmw hL
  have hs7 : Work.FTS.EllipticEst.SmoothOpen (NP6 α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP6 hsmw hL
  obtain ⟨hNA1mem, hNA1bd⟩ := hNA1 α hα hα1
  have hm1 : Work.Spaces.HkMem α 6 (NA1 α) := hNA1mem
  obtain ⟨hP3, hP4a, hP4b, hP5a, hP5b, hP6⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.hkmem_N0pieces_own hα hα1 hsmw hL hw.l12 hm6 hm7
  -- the split identity
  have hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w z θ
        = NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ + (NP4b α w z θ
            + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ))))) := by
    intro z θ hz hθ0 hθ1
    exact N0_split_open α hFstar hsmw z θ ⟨hz, hθ0, hθ1⟩
  have hsum := hkSq_sum7_le (α := α) (k := 6) hα hs1 hs2 hs3 hs4 hs5 hs6 hs7
    hm1 hP3 hP4a hP4b hP5a hP5b hP6
  have hcongr : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w)
      = Work.Spaces.HkSq α 6 (fun z θ => NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ
          + (NP4b α w z θ + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ)))))) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 6 hid
  -- the individual level-`6` bounds, all in terms of `1 + HkSq α 7 w`
  have h6w : (0 : ℝ) ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
  have h7w : (0 : ℝ) ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hone : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 7 w := by linarith
  have h67 : Work.Spaces.HkSq α 6 w ≤ Work.Spaces.HkSq α 7 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hm7
  have honenn : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 7 w := by linarith
  have hb1 : Work.Spaces.HkSq α 6 (NA1 α) ≤ K12 ^ 2 * (1 + Work.Spaces.HkSq α 7 w) := by
    have h2 : Work.Spaces.HkSq α 6 (NA1 α) = (Work.Spaces.HkNorm α 6 (NA1 α)) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 (NA1 α))]
    have h3 : (Work.Spaces.HkNorm α 6 (NA1 α)) ^ 2 ≤ (K12 * α ^ 2) ^ 2 :=
      pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 (NA1 α)) hNA1bd 2
    have h4 : (K12 * α ^ 2) ^ 2 ≤ K12 ^ 2 := by
      have h5 : (K12 * α ^ 2) ^ 2 = K12 ^ 2 * (α ^ 2) ^ 2 := by ring
      rw [h5]
      have h6 : α ^ 2 ≤ 1 := by nlinarith [hα, hα1]
      have h7 : (α ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α ^ 2), h6]
      calc K12 ^ 2 * (α ^ 2) ^ 2 ≤ K12 ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left h7 (sq_nonneg K12)
        _ = K12 ^ 2 := by ring
    calc Work.Spaces.HkSq α 6 (NA1 α) ≤ K12 ^ 2 := by rw [h2]; exact le_trans h3 h4
      _ = K12 ^ 2 * 1 := by ring
      _ ≤ K12 ^ 2 * (1 + Work.Spaces.HkSq α 7 w) :=
          mul_le_mul_of_nonneg_left hone (sq_nonneg K12)
  have hb3' : Work.Spaces.HkSq α 6 (NP3 α w) ≤ Ka * (1 + Work.Spaces.HkSq α 7 w) :=
    le_trans (hb34 α hαIoc w hw hXw).1
      (mul_le_mul_of_nonneg_left (by linarith [h67]) hKapos.le)
  have hb4' : Work.Spaces.HkSq α 6 (NP4b α w) ≤ Ka * (1 + Work.Spaces.HkSq α 7 w) :=
    (hb34 α hαIoc w hw hXw).2
  have hb5' : Work.Spaces.HkSq α 6 (NP5b α w) ≤ Kb * (1 + Work.Spaces.HkSq α 7 w) :=
    (hb56 α hαIoc w hw hXw).1
  have hb6' : Work.Spaces.HkSq α 6 (NP6 α w) ≤ Kb * (1 + Work.Spaces.HkSq α 7 w) :=
    (hb56 α hαIoc w hw hXw).2
  have hb4a' : Work.Spaces.HkSq α 6 (NP4a α w) ≤ Kc * (1 + Work.Spaces.HkSq α 7 w) :=
    le_trans (le_trans (hb45a α hαIoc w hw hXw).1
        (mul_le_mul_of_nonneg_left (by linarith [h67]) hKcpos.le))
      (le_of_eq (by ring : Kc * (1 + Work.Spaces.HkSq α 7 w)
        = Kc * (1 + Work.Spaces.HkSq α 7 w)))
  have hb5a' : Work.Spaces.HkSq α 6 (NP5a α w) ≤ Kc * (1 + Work.Spaces.HkSq α 7 w) :=
    le_trans (le_trans (hb45a α hαIoc w hw hXw).2
        (mul_le_mul_of_nonneg_left (by linarith [h67]) hKcpos.le))
      (le_of_eq (by ring : Kc * (1 + Work.Spaces.HkSq α 7 w)
        = Kc * (1 + Work.Spaces.HkSq α 7 w)))
  -- the total
  have hsum2 : Work.Spaces.HkSq α 6 (NA1 α) + Work.Spaces.HkSq α 6 (NP3 α w)
      + Work.Spaces.HkSq α 6 (NP4a α w) + Work.Spaces.HkSq α 6 (NP4b α w)
      + Work.Spaces.HkSq α 6 (NP5a α w) + Work.Spaces.HkSq α 6 (NP5b α w)
      + Work.Spaces.HkSq α 6 (NP6 α w)
      ≤ (K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) * (1 + Work.Spaces.HkSq α 7 w) := by
    linarith [hb1, hb3', hb4a', hb5a', hb4', hb5', hb6']
  have htot : Work.Spaces.HkSq α 6 (fun z θ => NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ
        + (NP4b α w z θ + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ))))))
      ≤ 64 * ((K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) * (1 + Work.Spaces.HkSq α 7 w)) :=
    le_trans hsum (mul_le_mul_of_nonneg_left hsum2 (by norm_num))
  have hfin : 64 * ((K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) * (1 + Work.Spaces.HkSq α 7 w))
      ≤ (64 * (K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) + 1) * (1 + Work.Spaces.HkSq α 7 w)
        + (64 * (K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) + 1) * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
    have h2 : (0 : ℝ) ≤ (1 + Work.Spaces.HkSq α 6 w) ^ 2 := sq_nonneg _
    nlinarith [h7w, h6w, h2]
  calc Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w)
      = Work.Spaces.HkSq α 6 (fun z θ => NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ
          + (NP4b α w z θ + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ)))))) := hcongr
    _ ≤ 64 * ((K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) * (1 + Work.Spaces.HkSq α 7 w)) := htot
    _ ≤ (64 * (K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) + 1) * (1 + Work.Spaces.HkSq α 7 w)
        + (64 * (K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) + 1) * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := hfin

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_BData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks


end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Assembly.near0_of_slot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.Assembly.near0_of_slot` — the near-origin bound for the SB4 producer

For the canonical slice `Ψ = slice (PsiCan Φs E g) τ` of the strong route, the `U`-slot part
`psiP αG Ψ` of the stream function satisfies

`|D_z(psiP αG Ψ)(z,θ)| ≤ K · z · sin 2θ`   for `(z,θ)` in the open quadrant, `z ≤ 1`,

which is what `SB6.rates` needs (`sb6_rates` consumes exactly this `∃K` statement).

## The argument

Write `αG = pExp a = 3a ∈ (0,1]`, `f = slice g τ`.  By the *definitions*
`PhiTs αG Φs = Φs - Θ(F_*)` and `PhiTil αG f (E f) = E f - Θ(f)`, so the slice splits
*algebraically* as

`Ψ = Φ̃_* + Θ(F_*) + Φ̃_E + Θ(f)`,   `Φ̃_* = PhiTs αG Φs`,  `Φ̃_E = PhiTil αG f (E f)`.

The `U`-slot `U'(X) = Uop αG X / sin 2θ` is additive over this splitting, and each summand's
`U'` is Lipschitz in `z` on `(0,1]`, uniformly in `θ`:

* `Φ̃_*`: `((z+1)/z)·U'(Φ̃_*) ∈ 𝒲^{4,∞}` (`StarPkgo2.UszW` through `RXT.starUop`);
* `Θ(F_*)`: explicit, `U'(Θ(F_*)) = -3/(2(1+z)) + αG z/(2(1+z)²)`, Lipschitz constant `2`;
* `Φ̃_E`: from the `ℋ⁴`-slot of `E` on the class-`C` approximants of `LimApprox`;
* `Θ(f)`: from the `L₁₂`/`Qang` estimates of `RegPkg'` (the quotient is *radial*).

`psiP αG Ψ = -(s2θ/αG)∫₀¹ v^{3/αG-1}U'(Ψ)(zv,θ)dv` then inherits the Lipschitz constant
`s2θ·C/(3+αG)`, `abs_deriv_le_of_lipschitzOn_Ioc` bounds `|∂_z psiP|` by it, and the factor `z`
comes from `D_z = z·∂_z`.

## Where each piece lives

The pieces of this argument are worked out in `...SB4.near0Aux` (the fragmentary radial Lipschitz
bounds), `...SB4.Epart_dz_bound` / `...SB4.Thetapart_dz_bound` (the `D_z`-bounds of the elliptic
and `Θ(f)` summands), `...SB4.slice_L12_c2` (the `C²`-regularity of `z ↦ L₁₂(slice g τ)(z)`),
`...SB4.psiP_lipschitz` and `...SB4.abs_deriv_le_of_lipschitzOn_Ioc`; `...SB4.near0Core`
(`near0_core`) is their assembly into the statement of this theorem, and the three producers
below instantiate its remaining hypotheses.
-/

namespace Work.FTS_StreamBdry.Assembly

theorem near0_of_slot {a C₀ Ce Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp a) u →
      Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp a) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp a) 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp a) E)
    (hStar : Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp a) Cs Φs)
    {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp a) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (hreg : ∀ S : ℝ, 0 < S →
      Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ τ : ℝ, 0 ≤ τ → ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.DzIter 1 (Work.FTS.StreamBdryIface.psiP (Work.FTS.Regularity.pExp a)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)) z θ|
        ≤ K * z * Work.Construction.s2 θ := by
  intro τ hτ
  refine Work.FTS_StreamBdry.SB4.near0_core (Φs := Φs) (E := E) (g := g)
    ha ha13 hStar hEL hOK ?_ ?_ ?_ τ hτ
  · -- `C²`-regularity of the `L₁₂`-tail of the slice
    intro τ' hτ' z hz
    exact Work.FTS_StreamBdry.SB4.slice_L12_c2 ha ha13 hOK τ' hτ' z hz
  · -- the `D_z`-bound for the elliptic summand `PhiTil αG f (E f)`
    intro τ' hτ'
    obtain ⟨K, hK0, hKb⟩ := Work.FTS_StreamBdry.SB4.Epart_dz_bound (C₀ := C₀) (Ce := Ce)
      ha ha13 hEll hEL hOK τ' hτ'
    exact ⟨K, hK0, fun z θ hzθ hz1 => by
      simpa only [Work.FTS.StreamBdryIface.Uprime] using hKb z θ hzθ hz1⟩
  · -- the `D_z`-bound for the `Θ`-summand `Theta αG f`
    intro τ' hτ'
    obtain ⟨K, hK0, hKb⟩ := Work.FTS_StreamBdry.SB4.Thetapart_dz_bound (C₀ := C₀)
      ha ha13 hOK hreg hG τ' hτ'
    exact ⟨K, hK0, fun z θ hzθ hz1 => by
      simpa only [Work.FTS.StreamBdryIface.Uprime] using hKb z θ hzθ hz1⟩

end Work.FTS_StreamBdry.Assembly
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Inputs.slice_slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


/-!
# `Work.FTS_StreamBdry.Inputs.slice_slots` — the `SlotBd` half of `slice_inputs`

This module assembles the `SlotBd` conjunct of `Work.FTS_StreamBdry.Inputs.slice_inputs` out of

* `residual_slot_jets` (the order-`≤ 2` jets of the `𝒰/sin 2θ`- and `𝒱`-slots of the residual
  `Φ̃ = v2_PhiT a Φs E g τ`), and
* `theta_part_jets` (the same jets for the singular part `Θ a (Ftau a g τ)`),

using the pointwise splitting of the stream function `Ψ = slice (PsiCan Φs E g) τ` into
`Φ̃ + Θ(F)` on the open quadrant (`PhiTil = id - Theta`, plus `v2_slice_PhiR_eq`) and the
linearity of `Uop`, `Vop` and `mixed`.

## The bridge: the sanitised and the canonical objects agree

`v2_slice_PhiR_eq` (`RXT.velVanish2Aux`) gives `slice (ΦR a Φs E g) τ = Φs + E (slice g τ)` on the
open quadrant, i.e. the *slice of the canonical stream function* `PsiCan Φs E g`; and
`Ftau (pExp a) (GR a g) τ = Fstar + slice (GR a g) τ` agrees there with `Ftau (pExp a) g τ`
(because `GR a g = gS a (tauExt g)` agrees with `g` on `z > 0`, `θ ∈ Iθ`, `τ ≥ 0`), hence the
`L₁₂`-values — and with them `Theta` — agree (`RXR5.L12_congr_of_agreeOnQ`).
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.Inputs

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false

/-- `Ftau` of the sanitised family `GR a g = gS a (tauExt g)` agrees with `Ftau` of `g` on the
open quadrant, for `τ ≥ 0`. -/
theorem agreeOnQ_Ftau_GR {a : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    Work.FTS_RegExport.RXR5.AgreeOnQ
      (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)
      (Work.Construction.Ftau (pExp a) g τ) := by
  intro z θ hz hθ hθ2
  have h1 : Work.FTS.RegExportIface.RXT.GR a g z θ τ = g z θ τ := by
    rw [Work.FTS.RegExportIface.RXT.GR]
    exact (Work.FTS_RegExport.RXR5.SG_apply_of_pos (α := a) (g := g) hz hθ.le hθ2.le).trans
      (Work.FTS.FinalV2.tauExt_of_nonneg g hτ)
  simp only [Work.Construction.Ftau, Work.FTS.Galerkin.slice_apply, h1]

/-- The `L₁₂`-values of the two `Ftau`'s agree for `z ≥ 0`. -/
theorem L12_Ftau_GR_eq {a : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ) z
      = Work.Construction.L12 (Work.Construction.Ftau (pExp a) g τ) z :=
  Work.FTS_RegExport.RXR5.L12_congr_of_agreeOnQ (agreeOnQ_Ftau_GR (a := a) hτ) hz

/-- The singular parts `Θ` of the two `Ftau`'s agree as functions of `θ`, for `z > 0`. -/
theorem Theta_Ftau_GR_eq {a : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) {z : ℝ} (hz : 0 < z) :
    Work.Construction.Theta (pExp a) (Work.Construction.Ftau (pExp a)
        (Work.FTS.RegExportIface.RXT.GR a g) τ) z
      = Work.Construction.Theta (pExp a) (Work.Construction.Ftau (pExp a) g τ) z := by
  funext θ
  simp only [Work.Construction.Theta]
  rw [L12_Ftau_GR_eq (a := a) hτ hz.le]

/-- The slice of the canonical stream function is, on the open quadrant, the slice of the
sanitised `ΦR` (they are the same function there). -/
theorem slice_PsiCan_eq_slice_PhiR {a : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ}
    (hτ : 0 ≤ τ) {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    slice (Work.FTS.Nonlin.PsiCan Φs E g) τ z θ
      = slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ z θ := by
  obtain ⟨hz, hθ, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  rw [Work.FTS_RegExport.RXT.v2_slice_PhiR_eq (αG := a) (Φs := Φs) (E := E) (g := g) hτ z θ
    hz hθ hθ2]
  simp only [Work.FTS.Nonlin.PsiCan, Work.FTS.Galerkin.slice_apply]

/-- On the open quadrant the slice of the sanitised stream function is the residual plus the
singular part: `Ψ = Φ̃ + Θ(F)` (definitional in `PhiTil = id - Theta`). -/
theorem slice_PhiR_eq_resid_add_Theta {a : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ z θ : ℝ} :
    slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ z θ
      = Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ z θ
        + Work.Construction.Theta (pExp a)
          (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ) z θ := by
  simp only [Work.FTS_RegExport.RXT.v2_PhiT, Work.Construction.PhiTil]
  ring


/-! ## The slot functions of the two pieces -/

/-- The `𝒰/sin 2θ`-slot of the residual `Φ̃ = v2_PhiT a Φs E g τ` (= `v2_SlotU a` of it). -/
abbrev Ures (a : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) : Fn :=
  Work.FTS_RegExport.RXT.v2_SlotU a (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ)

/-- The `𝒱`-slot of the residual. -/
abbrev Vres (a : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) : Fn :=
  Work.FTS_RegExport.RXT.v2_SlotV a (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ)

/-- The `𝒰/sin 2θ`-slot of the singular part `Θ` of the **sanitised** source. -/
abbrev UthS (a : ℝ) (g : Fam) (τ : ℝ) : Fn := fun z θ =>
  Work.Construction.Uop (pExp a) (Work.Construction.Theta (pExp a)
    (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)) z θ
    / Real.sin (2 * θ)

/-- The `𝒱`-slot of the singular part `Θ` of the **sanitised** source. -/
abbrev VthS (a : ℝ) (g : Fam) (τ : ℝ) : Fn :=
  Work.Construction.Vop (Work.Construction.Theta (pExp a)
    (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ))

/-- The `𝒰/sin 2θ`-slot of the singular part `Θ` of the **canonical** source. -/
abbrev Uth (a : ℝ) (g : Fam) (τ : ℝ) : Fn := fun z θ =>
  Work.Construction.Uop (pExp a) (Work.Construction.Theta (pExp a)
    (Work.Construction.Ftau (pExp a) g τ)) z θ / Real.sin (2 * θ)

/-- The `𝒱`-slot of the singular part `Θ` of the **canonical** source. -/
abbrev Vth (a : ℝ) (g : Fam) (τ : ℝ) : Fn :=
  Work.Construction.Vop (Work.Construction.Theta (pExp a)
    (Work.Construction.Ftau (pExp a) g τ))

/-! ## The closed form of `Vop` of the singular part -/

/-- `𝓥(Θ αG F)(z,θ) = L₁₂(F)(z)·c2m(θ)/(2αG)` on the open quadrant. -/
theorem Vop_Theta_closed {αG : ℝ} (F : Fn) {z θ : ℝ} (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Construction.Vop (Work.Construction.Theta αG F) z θ
      = Work.Construction.L12 F z * Work.Construction.c2m θ / (2 * αG) := by
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hθ2⟩)
  have hpth : Work.Spaces.pth (Work.Construction.Theta αG F) z θ
      = (1 / (4 * αG)) * (2 * Real.cos (2 * θ)) * Work.Construction.L12 F z := by
    show deriv (fun θ' => Work.Construction.Theta αG F z θ') θ = _
    have h1 : (fun θ' => Work.Construction.Theta αG F z θ')
        = fun θ' => ((1 / (4 * αG)) * Work.Construction.L12 F z) * Real.sin (2 * θ') := by
      funext θ'
      simp only [Work.Construction.Theta, Work.Construction.s2]
      ring
    have h2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
      have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
        (Real.hasDerivAt_sin (2 * θ)).comp θ (hasDerivAt_const_mul (x := θ) (2 : ℝ))
      simpa [mul_comm] using h
    rw [h1, (h2.const_mul _).deriv]
    ring
  simp only [Work.Construction.Vop, hpth, Work.Construction.Theta, Work.Construction.s2,
    Work.Construction.c2m, Real.tan_eq_sin_div_cos]
  rw [Real.sin_two_mul, Real.cos_two_mul']
  field_simp
  ring

/-! ## The pointwise splitting of the stream function into residual and singular part -/

/-- `Uop` of the singular part is the same for the sanitised and the canonical source. -/
theorem Uop_Theta_eq {a : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) {z θ : ℝ} (hz : 0 < z) :
    Work.Construction.Uop (pExp a) (Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)) z θ
      = Work.Construction.Uop (pExp a) (Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) g τ)) z θ := by
  have hev : (fun z' : ℝ => Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ) z' θ)
      =ᶠ[𝓝 z] (fun z' : ℝ => Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) g τ) z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact congrFun (Theta_Ftau_GR_eq (a := a) (g := g) hτ hz') θ
  have hval : Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ) z θ
      = Work.Construction.Theta (pExp a) (Work.Construction.Ftau (pExp a) g τ) z θ :=
    hev.self_of_nhds
  simp only [Work.Construction.Uop, Work.Spaces.pz]
  rw [hev.deriv_eq, hval]

/-- `Vop` of the singular part is the same for the sanitised and the canonical source. -/
theorem Vop_Theta_eq {a : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) {z θ : ℝ} (hz : 0 < z) :
    Work.Construction.Vop (Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)) z θ
      = Work.Construction.Vop (Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) g τ)) z θ := by
  have hfun := Theta_Ftau_GR_eq (a := a) (g := g) hτ hz
  have h1 : deriv (fun θ' : ℝ => Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ) z θ') θ
      = deriv (fun θ' : ℝ => Work.Construction.Theta (pExp a)
        (Work.Construction.Ftau (pExp a) g τ) z θ') θ := by
    rw [hfun]
  have h2 := congrFun hfun θ
  simp only [Work.Construction.Vop, Work.Spaces.pth, h1, h2]

/-- The `Θ`-slots of the sanitised and the canonical source agree on `z > 0`. -/
theorem eqOn_UthS_Uth {a : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    Set.EqOn (Function.uncurry (UthS a g τ)) (Function.uncurry (Uth a g τ))
      (Set.Ioi 0 ×ˢ Set.univ) := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hz0 : 0 < z := hp.1
  simp only [Function.uncurry, UthS, Uth]
  rw [Uop_Theta_eq (a := a) (g := g) hτ hz0]

/-- The `Θ`-slots of the sanitised and the canonical source agree on `z > 0`. -/
theorem eqOn_VthS_Vth {a : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    Set.EqOn (Function.uncurry (VthS a g τ)) (Function.uncurry (Vth a g τ))
      (Set.Ioi 0 ×ˢ Set.univ) := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hz0 : 0 < z := hp.1
  simp only [Function.uncurry, VthS, Vth]
  rw [Vop_Theta_eq (a := a) (g := g) hτ hz0]

/-- The `𝒰/sin 2θ`-slot of the slice of `ΦR` splits as residual plus singular part. -/
theorem eqOn_Uprime_split {a : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ}
    (hSΨ : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ))
      Work.FTS.EllipticEst.Q0)
    (hSΘ : ContDiffOn ℝ 3 (Function.uncurry (Work.Construction.Theta (pExp a)
      (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)))
      Work.FTS.EllipticEst.Q0) :
    Set.EqOn
      (Function.uncurry (Work.FTS.StreamBdryIface.Uprime (pExp a)
        (slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ)))
      (Function.uncurry (Ures a Φs E g τ + UthS a g τ))
      Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ hzθ
  have h1 := Work.FTS_RegExport.RXT.Sys.uop_split_theta (α := a) (Φs := Φs) (E := E) (g := g)
    (τ := τ) hzθ hSΨ hSΘ
  simp only [Function.uncurry, Pi.add_apply, Work.FTS.StreamBdryIface.Uprime, Ures, UthS,
    Work.FTS_RegExport.RXT.v2_SlotU, Work.Construction.s2, h1]
  ring

/-- The `𝒱`-slot of the slice of `ΦR` splits as residual plus singular part. -/
theorem eqOn_Vop_split {a : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ}
    (hSΨ : ContDiffOn ℝ 1 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ))
      Work.FTS.EllipticEst.Q0)
    (hSΘ : ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Theta (pExp a)
      (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)))
      Work.FTS.EllipticEst.Q0) :
    Set.EqOn
      (Function.uncurry (Work.Construction.Vop
        (slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ)))
      (Function.uncurry (Vres a Φs E g τ + VthS a g τ))
      Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ hzθ
  have h1 := Work.FTS_RegExport.RXT.v2_vop_add_at (f := Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ)
    (g := Work.Construction.Theta (pExp a)
      (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ)) hSΨ hSΘ hzθ
  have hfun : slice (Work.FTS.RegExportIface.RXT.ΦR a Φs E g) τ
      = fun z θ => Work.FTS_RegExport.RXT.v2_PhiT a Φs E g τ z θ
          + Work.Construction.Theta (pExp a)
            (Work.Construction.Ftau (pExp a) (Work.FTS.RegExportIface.RXT.GR a g) τ) z θ :=
    funext fun z => funext fun θ => slice_PhiR_eq_resid_add_Theta
  simp only [Function.uncurry, Pi.add_apply, Vres, VthS,
    Work.FTS_RegExport.RXT.v2_SlotV, hfun, h1]

/-- Additivity of `mixed` for a sum of two `C²`-functions on the open quadrant (the `Pi.add`
form of `RXT.Sys.mixed_add_lam`). -/
theorem mixed_add_of {f h : Fn} (hf : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hh : ContDiffOn ℝ 2 (Function.uncurry h) Work.FTS.EllipticEst.Q0) {j i : ℕ}
    (hji : j + i ≤ 2) {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.mixed j i (f + h) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i h z θ :=
  Work.FTS_RegExport.RXT.Sys.mixed_add_lam hf hh hji hzθ
end Work.FTS_StreamBdry.Inputs
end
end
