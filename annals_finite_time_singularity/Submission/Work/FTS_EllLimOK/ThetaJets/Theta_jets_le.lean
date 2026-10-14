import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Row6.Basic
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NSplit6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.N6Trans_exists
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.PkgJets.L12jets_classC
import Submission.Work.FTS_EllLimOK.ThetaJets.ClassC_le
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.Pieces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Row6

open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongPersist.H6Rows.Npair6SupAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The twenty pieces of the `N`-row, as a `ℕ`-indexed family (zero off `{0,…,19}`). -/
def pcs (α : ℝ) (f Ef Φs : Fn) : ℕ → Fn
  | 0 => nsP0 α Φs
  | 1 => nsP1 α Φs f
  | 2 => nsP2 α f Ef
  | 3 => nsP3 α f Ef
  | 4 => nsP4 α Φs
  | 5 => nsP5 α Φs f
  | 6 => nsP6 α f Ef
  | 7 => nsP7 α f Ef
  | 8 => nsP8 α Φs
  | 9 => nsP9 α Φs f
  | 10 => nsP10 α f Ef
  | 11 => nsP11 α f Ef
  | 12 => nsP12 α
  | 13 => nsP13 α f
  | 14 => nsP14 α f
  | 15 => nsP15 α f
  | 16 => nsP16 α
  | 17 => nsP17 α f
  | 18 => nsP18 α f
  | 19 => nsP19 α f
  | _ => 0

/-- The twenty pieces sum to `nsum`. -/
theorem pcs_sum (α : ℝ) (f Ef Φs : Fn) :
    nsum α f Ef Φs
      = ∑ k ∈ Finset.range 20, pcs α f Ef Φs k := by
  have h : (∑ k ∈ Finset.range 20, pcs α f Ef Φs k)
      = pcs α f Ef Φs 0 + pcs α f Ef Φs 1 + pcs α f Ef Φs 2 + pcs α f Ef Φs 3
        + pcs α f Ef Φs 4 + pcs α f Ef Φs 5 + pcs α f Ef Φs 6 + pcs α f Ef Φs 7
        + pcs α f Ef Φs 8 + pcs α f Ef Φs 9 + pcs α f Ef Φs 10 + pcs α f Ef Φs 11
        + pcs α f Ef Φs 12 + pcs α f Ef Φs 13 + pcs α f Ef Φs 14 + pcs α f Ef Φs 15
        + pcs α f Ef Φs 16 + pcs α f Ef Φs 17 + pcs α f Ef Φs 18 + pcs α f Ef Φs 19 := by
    simp [Finset.sum_range_succ]
  rw [h]
  funext z θ
  simp only [pcs, nsum, nsP0, nsP1, nsP2, nsP3, nsP4, nsP5, nsP6, nsP7, nsP8, nsP9, nsP10,
    nsP11, nsP12, nsP13, nsP14, nsP15, nsP16, nsP17, nsP18, nsP19, Pi.add_apply]

end Work.FTS.StrongPersist.H6Row6
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.pairing_le_of_slotBoundB =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

/-! ### The free parameter `Ce` of the statement

The requested statement mentions `Ce` (the perturbation constant of `L6Ctx`) without binding it
in its binder list — Lean's `autoImplicit` would bind it as the *implicit* universally
quantified variable `{Ce : ℝ}`, which is exactly what the `variable` declaration below does,
with the statement left character for character as requested. -/
variable {Ce : ℝ}

/-- **The pairing of the `N`-row against the datum, priced by the per-slot bound, at the
finite smoothness order `C⁶`.**

This is the sibling of `Npair6BWork.pairing_le_of_slotBound`, with the hypothesis
`SmoothOpen (nsum α (g τ) (E (g τ)) Φs)` (`C^∞` on the open quadrant) weakened to
`ContDiffOn ℝ 6 (uncurry (nsum …)) Q0`.  The only place where the smoothness order was used is
the level-six unfolding of the coercive recursion, and the finite-order version
`Npair6SupAux.IP6UnfoldCd6` supplies exactly `C⁶`:

  `|IP6 1…1 α u v| ≤ C · SlotSum α 6 u v`   for `u, v` of class `C⁶` on the open quadrant.

The rest of the argument is unchanged: `IP6 1…1` unfolds into the level-six slot sum
(`IP6UnfoldCd6`), which is bounded by `84·B` once every one of the leaf slot pairings is
bounded by `B` (`StrongPersist.SlotSum_six_le`); and the nonlinearity
`N α (F_* + g(τ)) (Φs + E(g(τ)))` is replaced by the twenty-piece sum `nsum` of
`Npair6SupAux` on the open quadrant (`NSplit6`), the equality of the two pairings being the
congruence `IP6_congr` on the (co-null) open quadrant.

The three smoothness facts used are: the datum `g(τ)` is smooth (`L6Ctx.hreg.reg.1`), the
perturbation stream function `E(g(τ))` is smooth (`EllPkgK.smooth` through `Ell6Ctx.hell`) and
the star profile `Φs` is smooth (`StarPkgo.smooth` through `Ell6Ctx.hstar`). -/
theorem pairing_le_of_slotBoundB : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn) (B : ℝ),
      0 ≤ τ →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1)
        α M Ce Cs E Φs g Φ τ →
      ContDiffOn ℝ 6
        (Function.uncurry (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α
          (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ)) Φs))
        Work.FTS.EllipticEst.Q0 →
      0 ≤ B →
      (∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
          |Work.FTS.TransportS.slotPairing ρ a b
            (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α (Work.FTS.Galerkin.slice g τ)
              (E (Work.FTS.Galerkin.slice g τ)) Φs)
            (Work.FTS.Galerkin.slice g τ)| ≤ B) →
      |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
          (Work.Construction.N α (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice Φ τ))
          (Work.FTS.Galerkin.slice g τ)| ≤ C * B := by
  obtain ⟨CIP, hCIPpos, hIP6u⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.IP6UnfoldCd6
  refine ⟨CIP * 84, by nlinarith [hCIPpos], ?_⟩
  intro α hα g Φ τ M Cs E Φs B hτ hctx hsm hB0 hslot
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- smoothness of the three ingredients
  have hfsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice g τ) := hctx.hreg.reg.1
  have hEsm : Work.FTS.EllipticEst.SmoothOpen (E (Work.FTS.Galerkin.slice g τ)) :=
    hctx.hell.hell.smooth
  have hPsm : Work.FTS.EllipticEst.SmoothOpen Φs := hctx.hell.hstar.smooth
  have hfsm6 : ContDiffOn ℝ 6
      (Function.uncurry (Work.FTS.Galerkin.slice g τ)) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.FTS.Galerkin.slice g τ)).mp hfsm 6
  -- the twenty-piece splitting of the nonlinearity
  have hsplit := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NSplit6 hα0 hα1
    (f := Work.FTS.Galerkin.slice g τ) (Ef := E (Work.FTS.Galerkin.slice g τ)) (Φs := Φs)
    hctx.hreg hEsm hPsm
  -- the pairing only sees `nsum` (the two profiles agree on the open quadrant)
  have hgoal :
      Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
          (Work.Construction.N α (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice Φ τ))
          (Work.FTS.Galerkin.slice g τ)
        = Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α (Work.FTS.Galerkin.slice g τ)
              (E (Work.FTS.Galerkin.slice g τ)) Φs) (Work.FTS.Galerkin.slice g τ) := by
    rw [hctx.hell.hsum]
    exact hsplit.2 (Work.FTS.Galerkin.slice g τ)
  -- the level-six unfolding at finite order
  have hIP := hIP6u α
    (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α (Work.FTS.Galerkin.slice g τ)
      (E (Work.FTS.Galerkin.slice g τ)) Φs)
    (Work.FTS.Galerkin.slice g τ) hsm hfsm6
  -- the slot sum
  have hsl := Work.FTS.StrongPersist.SlotSum_six_le α
    (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α (Work.FTS.Galerkin.slice g τ)
      (E (Work.FTS.Galerkin.slice g τ)) Φs)
    (Work.FTS.Galerkin.slice g τ) B hB0 hslot
  calc
    |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
        (Work.Construction.N α (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice Φ τ))
        (Work.FTS.Galerkin.slice g τ)|
        = |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α (Work.FTS.Galerkin.slice g τ)
              (E (Work.FTS.Galerkin.slice g τ)) Φs) (Work.FTS.Galerkin.slice g τ)| := by
          rw [hgoal]
    _ ≤ CIP * Work.FTS.TransportS.SlotSum α 6
            (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α (Work.FTS.Galerkin.slice g τ)
              (E (Work.FTS.Galerkin.slice g τ)) Φs) (Work.FTS.Galerkin.slice g τ) := hIP
    _ ≤ CIP * (84 * B) := by
          refine mul_le_mul_of_nonneg_left hsl ?_
          linarith [hCIPpos]
    _ = (CIP * 84) * B := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ThetaJets.Theta_jets_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ThetaJets

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. The angular factor `A_i = D_θ^i ((1/(4α)) sin 2·)` -/

/-- `DthIter1` is homogeneous in the scalar. -/
theorem DthIter1_const_mul (i : ℕ) (c : ℝ) (b : ℝ → ℝ) :
    Work.FTS_RegExport.RXT.velPertAux.DthIter1 i (fun θ => c * b θ)
      = fun θ => c * Work.FTS_RegExport.RXT.velPertAux.DthIter1 i b θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      funext θ
      have hstep : Work.FTS_RegExport.RXT.velPertAux.DthIter1 (i + 1) (fun θ => c * b θ) θ
          = Real.sin (2 * θ) * deriv (Work.FTS_RegExport.RXT.velPertAux.DthIter1 i
              (fun θ => c * b θ)) θ := rfl
      have hstep2 : Work.FTS_RegExport.RXT.velPertAux.DthIter1 (i + 1) b θ
          = Real.sin (2 * θ)
              * deriv (Work.FTS_RegExport.RXT.velPertAux.DthIter1 i b) θ := rfl
      rw [hstep, hstep2, ih, deriv_const_mul_field]
      ring

/-- `|D_θ^i (sin 2·)| ≤ 384` on `(0,π/2)` for `i ≤ 4`. -/
theorem DthIter1_sin_le (i : ℕ) (hi : i ≤ 4) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.FTS_RegExport.RXT.velPertAux.DthIter1 i (fun θ' => Real.sin (2 * θ')) θ| ≤ 384 := by
  have hmem : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have heq : Work.FTS_RegExport.RXT.velPertAux.DthIter1 i (fun θ' => Real.sin (2 * θ')) θ
      = Work.Spaces.DthIter i Work.FTS.H2.Sfun 0 θ := by
    have h := congrFun (congrFun
      (Work.FTS_RegExport.RXT.velPertAux.DthIter_const i (fun θ' => Real.sin (2 * θ'))) 0) θ
    exact h.symm
  rw [heq]
  have h2 := Work.FTS.H2.abs_DthIter_Sfun_le i hi 0 hmem
  have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsin0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_Iθ hmem
  have hA : Work.FTS.H2.Asin i ≤ 384 := by
    rcases i with _ | _ | _ | _ | i <;> norm_num [Work.FTS.H2.Asin]
  calc |Work.Spaces.DthIter i Work.FTS.H2.Sfun 0 θ|
      ≤ Work.FTS.H2.Asin i * Real.sin (2 * θ) := h2
    _ ≤ 384 * 1 := mul_le_mul hA hsin1 hsin0 (by norm_num)
    _ = 384 := by ring

/-- **The angular-factor bound**: for `i ≤ 4` and `θ ∈ (0,π/2)`,
`|D_θ^i ((1/(4α)) sin 2·)(θ)| ≤ 384/(4α)`. -/
theorem DthIter1_theta_factor (α : ℝ) (hα : 0 < α) (i : ℕ) (hi : i ≤ 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.FTS_RegExport.RXT.velPertAux.DthIter1 i
        (fun θ' => (1 / (4 * α)) * Work.Construction.s2 θ') θ| ≤ 384 / (4 * α) := by
  have hc : (0 : ℝ) < 1 / (4 * α) := by positivity
  have hfun : (fun θ' => (1 / (4 * α)) * Work.Construction.s2 θ')
      = fun θ' => (1 / (4 * α)) * Real.sin (2 * θ') := by
    funext θ'; rw [Work.Construction.s2_eq]
  rw [hfun, DthIter1_const_mul, abs_mul, abs_of_pos hc]
  have h2 := DthIter1_sin_le i hi hθ
  calc (1 / (4 * α)) * |Work.FTS_RegExport.RXT.velPertAux.DthIter1 i
        (fun θ' => Real.sin (2 * θ')) θ|
      ≤ (1 / (4 * α)) * 384 := mul_le_mul_of_nonneg_left h2 hc.le
    _ = 384 / (4 * α) := by ring

/-! ## 2. The decay of the pure `D_z`-iterates at `∞`, from `BdryTraces` -/


/-! ## 3. The `Π`-data of the sibling `integral_Ktheta_dzIter_le`, and its consequences -/


/-- `Ktheta = Spaces.K`. -/
theorem Ktheta_eq_K : Work.Elliptic.Ktheta = Work.Spaces.K := by
  funext θ
  simp only [Work.Elliptic.Ktheta, Work.Spaces.K]




/-! ## 4. The `L₁₂`-bound for `j = 0` (the tail C-S bound of the `GalBasis/cc` chain) -/


/-! ## 6. The target -/

/-- **The angular-factor step of the target.**  Given the radial bound
`|D_z^j (L₁₂ g)(z)| ≤ C |g|_{ℋ⁶}` for `j ≤ 4`, `z > 0` and every `g` of class `ClassC α`, the
separated-product factorisation of `Θ` together with the bound `384/(4α)` on the angular factor
gives the target with the constant `(384/(4α))·C`. -/
theorem Theta_jets_le_of_radial {α : ℝ} (hα : 0 < α) {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ (g : Work.FTS.Galerkin.Fn), Work.FTS.ClassC.ClassC α g →
      ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
        |Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g) :
    ∀ (g : Work.FTS.Galerkin.Fn), Work.FTS.ClassC.ClassC α g →
      ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
        |Work.Spaces.mixed j i (Work.Construction.Theta α g) z θ|
          ≤ (384 / (4 * α)) * C * Work.FTS.StrongGlobal.Xn6 α g := by
  intro g hg j i hji z θ hz hθ
  have hfac : Work.Spaces.mixed j i (Work.Construction.Theta α g) z θ
      = Work.FTS_RegExport.RXT.velPertAux.DthIter1 i
          (fun θ' => (1 / (4 * α)) * Work.Construction.s2 θ') θ
        * Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0 :=
    Work.FTS_RegExport.RXT.velPertAux.theta_mixed_factor α g j i z θ
  rw [hfac, abs_mul]
  have hA := DthIter1_theta_factor α hα i (by omega) hθ
  have hR := hC g hg j (by omega) z hz
  have hAnn : (0 : ℝ) ≤ 384 / (4 * α) := by positivity
  calc |Work.FTS_RegExport.RXT.velPertAux.DthIter1 i
          (fun θ' => (1 / (4 * α)) * Work.Construction.s2 θ') θ|
        * |Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0|
      ≤ (384 / (4 * α)) * (C * Work.FTS.StrongGlobal.Xn6 α g) :=
        mul_le_mul hA hR (abs_nonneg _) hAnn
    _ = (384 / (4 * α)) * C * Work.FTS.StrongGlobal.Xn6 α g := by ring

theorem Theta_jets_le : ∀ (α : ℝ), 0 < α → ∃ C : ℝ, 0 < C ∧ ∀ (g : Work.FTS.Galerkin.Fn),
    Work.FTS.ClassC.ClassC α g →
    ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.mixed j i (Work.Construction.Theta α g) z θ|
        ≤ C * Work.FTS.StrongGlobal.Xn6 α g := by
  intro α hα
  by_cases hα1 : α ≤ 1
  · -- the range `α ≤ 1` is the proved sibling `PkgJets.L12jets_classC`
    obtain ⟨C1, hC1pos, hC1⟩ := Work.FTS_EllLimOK.PkgJets.L12jets_classC (α := α) hα hα1
    refine ⟨(384 / (4 * α)) * C1, by positivity, ?_⟩
    intro g hg j i hji z θ hz hθ
    exact Theta_jets_le_of_radial hα hC1pos hC1 g hg j i hji z θ hz hθ
  · -- the range `α > 1` reduces to the case `α = 1` (`ClassC α g → ClassC 1 g`)
    have hge : 1 ≤ α := le_of_lt (lt_of_not_ge hα1)
    obtain ⟨C1, hC1pos, hC1⟩ := Work.FTS_EllLimOK.PkgJets.L12jets_classC (α := 1) one_pos le_rfl
    have hC1' : ∀ (g : Work.FTS.Galerkin.Fn), Work.FTS.ClassC.ClassC α g →
        ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
          |Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0|
            ≤ C1 * Work.FTS.StrongGlobal.Xn6 α g := by
      intro g hg j hj z hz
      refine le_trans (hC1 g (classC_one_of hge hg) j hj z hz) ?_
      exact mul_le_mul_of_nonneg_left (Xn6_one_le hge hg) hC1pos.le
    refine ⟨(384 / (4 * α)) * C1, by positivity, ?_⟩
    intro g hg j i hji z θ hz hθ
    exact Theta_jets_le_of_radial hα hC1pos hC1' g hg j i hji z θ hz hθ

end Work.FTS_EllLimOK.ThetaJets
end
