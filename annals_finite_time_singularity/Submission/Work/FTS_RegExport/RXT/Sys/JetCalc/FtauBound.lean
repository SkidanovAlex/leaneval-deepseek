import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.loc_sup4
import Submission.Work.FTS_RegExport.RXT.C2Psi
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.OpFacts
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.RHSDefs
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.RHSSmooth
import Submission.Work.FTS.LocDataExt.SepFactor
import Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.JetCalc.FtauBound` — jet bounds for `F(σ) = F_* + gS α (tauExt g)(σ)`

The mixed jets of `F_* = α·(Γ/c)·(2z/(1+z)²)` are the products of the radial jets of
`2z/(1+z)²` (bounded by `FstarJet7`) with the angular jets of `Γ` (bounded by
`LocData6.DthIter_Gam_abs_le6`, `|D_θ^iΓ| ≤ 10⁵Γ ≤ 10⁵`), by the separability identity
`LocDataExt.mixed_sepGam`.  The `g`-part is bounded by `loc_sup4` (the class-`C` interior
trade-off, uniform in the fake time), and the sum by `mixed_add_of_contDiffOn`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **Mixed jet bounds for the reference profile `F_*`.**  If the radial factor `2z/(1+z)²` has
all its `z`-jets of order `≤ 7` bounded by `M` on `z ≥ 0`, then every mixed jet of `F_*` of order
`m ≤ 7` (radial) and `n ≤ 6` (angular) is bounded by `10⁶·M` on `z > 0`, `θ ∈ Iθ`. -/
theorem Fstar_mixed_bound {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {M : ℝ}
    (hM : ∀ j : ℕ, j ≤ 7 → ∀ z : ℝ, 0 ≤ z → |Work.Elliptic.DzdIter j Work.FM.Fstar z| ≤ M)
    {m n : ℕ} (hm : m ≤ 7) (hn : n ≤ 6) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed m n (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
      ≤ 10 ^ 6 * M := by
  have hβ0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hcb := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp α) hβ0 hβ1
  have hcpos : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp α) := by linarith [hcb.1]
  -- `F_*` is separable: `(α/c)·2z/(1+z)² · Γ(θ)`
  set ρ : ℝ → ℝ := fun z =>
    (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α)) * Work.FM.Fstar z
    with hρ
  have hfac : Work.Construction.Fstar (Work.FTS.Regularity.pExp α)
      = fun z θ => ρ z * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ := by
    funext z θ
    simp only [Work.Construction.Fstar, hρ]
    ring
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 (by norm_num) 0 le_rfl)
  rw [hfac, Work.FTS.LocDataExt.mixed_sepGam]
  -- the radial factor
  have hDz : |Work.Spaces.DzIter m (fun z _ => ρ z) z θ| ≤ 10 * M := by
    have h1 : Work.Spaces.DzIter m (fun z _ => ρ z) z θ
        = (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          * Work.Elliptic.DzdIter m Work.FM.Fstar z := by
      rw [hρ]
      have h2 := congrFun (congrFun (Work.FTS_RegExport.RXT.ftau_DzIter_mul_theta
        (fun _ : ℝ => Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        (fun z _ : ℝ => Work.FM.Fstar z) m) z) θ
      rw [h2, Work.Elliptic.DzIter_rad]
    rw [h1, abs_mul]
    have hcoef : |Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α)| ≤ 10 := by
      have hnn : 0 ≤ Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α) :=
        div_nonneg hβ0.le hcpos.le
      rw [abs_of_nonneg hnn, div_le_iff₀ hcpos]
      nlinarith [hβ0, hβ1, hcb.1]
    exact mul_le_mul hcoef (hM m hm z hz.le) (abs_nonneg _) (by norm_num)
  -- the angular factor
  have hDth : |Work.Spaces.DthIter n (fun _ θ' => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ')
      0 θ| ≤ 10 ^ 5 := by
    have h1 := Work.FTS.LocData6.DthIter_Gam_abs_le6 n hn (Work.FTS.Regularity.pExp α) hβ0 hβ1 hθ
    have h2 := (Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α) θ hβ0 hθ).2
    linarith
  calc |Work.Spaces.DzIter m (fun z _ => ρ z) z θ
        * Work.Spaces.DthIter n (fun _ θ' => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ') 0 θ|
      = |Work.Spaces.DzIter m (fun z _ => ρ z) z θ|
        * |Work.Spaces.DthIter n
            (fun _ θ' => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ') 0 θ| := by
        rw [abs_mul]
    _ ≤ (10 * M) * 10 ^ 5 := mul_le_mul hDz hDth (abs_nonneg _) (by linarith)
    _ = 10 ^ 6 * M := by ring

/-- **Uniform jet bounds for `F(σ) = F_* + gS α (tauExt g)(σ)`** on a closed box of the open
quadrant, uniformly in the fake time `σ ∈ (0,S]`, for all mixed jets of total order `≤ 3`. -/
theorem FtauS_mixed_bound {α C₀ S : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) (hd : d < π / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Ioc (0 : ℝ) S, ∀ m n : ℕ, m + n ≤ 3 →
      ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
        |Work.Spaces.mixed m n (FtauS α g σ) z θ| ≤ C := by
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
  obtain ⟨Cg, hCg0, hCg⟩ := Work.FTS_RegExport.RXT.loc_sup4 hα hα13 hOK S hS ha hab hc hcd hd
  have hβ0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  refine ⟨10 ^ 6 * M + Cg, by positivity, ?_⟩
  intro σ hσ m n hmn z hz θ hθ
  -- small arithmetic facts about the orders
  have hm4 : m + n ≤ 4 := le_trans hmn (by norm_num)
  have hn4 : n + m ≤ 4 := by rw [Nat.add_comm]; exact hm4
  have hm7 : m ≤ 7 := le_trans (Nat.le_add_right m n) (le_trans hmn (by norm_num))
  have hn6 : n ≤ 6 := le_trans (Nat.le_add_left n m) (le_trans hmn (by norm_num))
  have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
  have hθpos : 0 < θ := lt_of_lt_of_le hc hθ.1
  have hθlt : θ < Real.pi / 2 := lt_of_le_of_lt hθ.2 hd
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hzpos, hθpos, hθlt⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθpos.le, hθlt.le⟩
  -- additivity of the mixed operators on the two summands of `F(σ)`
  have hF4 : ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.Fstar
      (Work.FTS.Regularity.pExp α))) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_Fstar_Q0 4 hβ0 hβ1
  have hG4 : ContDiffOn ℝ 4 (Function.uncurry
      (Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) σ))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_slice_GR_Q0 hOK le_rfl σ hσ.1.le
  have hadd := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn
    Work.FTS.EllipticEst.isOpen_Q0 hF4 hG4 n m hn4 (z, θ) hp
  have hsplit : Work.Spaces.mixed m n (FtauS α g σ) z θ
      = Work.Spaces.mixed m n (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        + Work.Spaces.mixed m n (Work.FTS.Galerkin.slice
            (Work.FTS.RegExportIface.RXT.GR α g) σ) z θ := by
    have hfun : FtauS α g σ = Work.Construction.Fstar (Work.FTS.Regularity.pExp α)
        + Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) σ := by
      funext z' θ'
      simp only [FtauS_apply, Pi.add_apply, Work.FTS.Galerkin.slice]
    rw [hfun]
    exact hadd
  -- the sanitiser agrees with `g` on the open quadrant
  have hcongr : Work.Spaces.mixed m n (Work.FTS.Galerkin.slice
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z θ
      = Work.Spaces.mixed m n (Work.FTS.Galerkin.slice g σ) z θ := by
    have hEqOn : Set.EqOn (Function.uncurry (Work.FTS.Galerkin.slice
          (Work.FTS.RegExportIface.RXT.GR α g) σ))
        (Function.uncurry (Work.FTS.Galerkin.slice g σ)) Work.FTS.EllipticEst.Q0 :=
      fun p hp => Work.FTS_RegExport.RXT.ftau_slice_GR_eq hσ.1.le hp.1 hp.2.1.le hp.2.2.le
    exact (Work.FTS.RegPkgGal.mixed_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqOn m n) hp
  calc |Work.Spaces.mixed m n (FtauS α g σ) z θ|
      = |Work.Spaces.mixed m n (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.mixed m n (Work.FTS.Galerkin.slice g σ) z θ| := by
        rw [hsplit, hcongr]
    _ ≤ |Work.Spaces.mixed m n (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
          + |Work.Spaces.mixed m n (Work.FTS.Galerkin.slice g σ) z θ| := abs_add_le _ _
    _ ≤ 10 ^ 6 * M + Cg := add_le_add
        (Fstar_mixed_bound hα hα13 hM hm7 hn6 hzpos hθI)
        (hCg σ ⟨hσ.1.le, hσ.2⟩ m n hm4 z hz θ hθ)

end Work.FTS_RegExport.RXT.Sys
