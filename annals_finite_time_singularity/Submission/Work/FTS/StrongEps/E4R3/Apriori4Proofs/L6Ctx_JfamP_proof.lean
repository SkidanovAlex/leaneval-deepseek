import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.NMem6Parts
import Submission.Work.FTS.StrongEps.EpsGdotThird
import Submission.Work.FTS.StrongPersist.H6SplitIP6
import Submission.Work.FTS.StrongPersist.H6LinMem6
import Submission.Work.FTS.StrongEps.smoothOpen_linPart
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0_mem6
import Submission.Work.FTS.StrongPersist.H6Rows.AK6Row
import Submission.Work.FTS.GalFields.Norm.radLeibniz
import Submission.Work.FTS.CoercivityFix.Assembly.RegQAux
import Submission.Work.FTS.IPGen.Defs
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.NonlinRows.smoothOpen_radA
import Submission.Work.FTS.StrongPersist.H6Rows.piecesC6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongEps.smoothOpen_dynRHS
import Submission.Work.FTS.GalFields.RHS.smoothOpen_atoms_of_gal
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsFKadd
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsL12add
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.Basic
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar

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
