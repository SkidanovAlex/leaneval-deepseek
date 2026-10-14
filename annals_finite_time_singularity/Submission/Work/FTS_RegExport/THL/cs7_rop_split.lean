import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0
import Submission.Work.FTS.StrongEps.H5.HAtoms5
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Slots.v2_paramC2
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_lip_approx
import Submission.Work.FTS_RegExport.RXT.velPert
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.RXT0.SJC.slotJetLipschitzApprox
import Submission.Work.FTS_RegExport.THL.angular_L2_noTrace
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Stability.L12Add
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

/-- **The `N`-block of the scheme's right-hand side is `ℋ⁴`-honest and bounded, for `ClassC`
data of small `ℋ⁴`-size and bounded `ℋ⁶`-size.**

`N α (Ftot α w) (Φs + Φg) = 2·Rop(Φ̃)·F - 2·Uop(Φ̃)·pth F - 2α·Vop(Φ̃)·Dz F
- (1/2)·s2·FK F·pth F - sin²θ·FK F·F`, where `Φ̃ = PhiTil α (Ftot α w) (Φs+Φg)` splits as
`PhiTs α Φs + PhiTil α w Φg` (`Theta α F = (1/(4α))s2·L₁₂ F` is linear in `F`).

Route hints (all tools are on disk and threshold-free):

* `Rop/Uop/Vop` are linear in their argument, so the split of `Φ̃` splits each of them; the
  `PhiTs`-parts are priced by `hstar` (`StarPkgo2.RW`, `VW`, `UsW`, `VzW`) as `𝒲^{4,∞}`-functions,
  the `PhiTil α w Φg`-parts by `hell` (`EllPkgGo.R`, `U`, `V`), which gives
  `HkMem α 4 (Rop …)` and `Xn ≤ Ce·Xn α w ≤ Ce·C₀α²`;
* the pieces whose first factor is the `𝒲`-coefficient `(z+1)/z·Rop(Φ̃_*)` etc. are handled by
  `Work.FTS.OpenPkg.wprod_field_winf` after the identity
  `2·Rop(Φ̃_*)·F = 2·[(z+1)/z·Rop(Φ̃_*)]·[z/(1+z)·F]` (and analogously for `(Uop/s2)·Dth f`,
  where the factor `s2·pth F = Dth F` **everywhere**); the second factor is in `HQo α 4` by
  closure of `ℋ⁴` under a bounded smooth radial factor (`prod_field` with the fixed profiles
  `(z+1)/z`, `z/(1+z)`);
* `FK(F_*+w) = FK(F_*) + FK(w)` (`Work.FTS.GalFields.RHS.FK_add_of_slices`; `FK(F_*)` is the
  explicit `α·2z/(1+z)²`), and `Work.FTS.OpenPkg.fkH_field` bounds `FK(w)` by `Ci·Xn α w`;
* the remaining factors: `F = F_* + w` (additivity), `Dth F`, `Dz F` (`ℋ⁴` via
  `Work.FTS.GalFields.Xn_Dz_le_Xn5` / `Xn_Dth_le_Xn5`, bounded by `HkNorm α 6 w ≤ B`); the
  fixed `F_*`, `Dth F_*`, `Dz F_*` via `Work.FTS.Nonlinear.FstarPkg.{Fstar_W, DthFstar_W,
  DzFstar_W}` (+ `wtoHQ_of_pointwise_open` if a pointwise form is needed);
* sums: `Work.FTS.GalFields.RHS.HkNorm_add_le_open` / `HkNorm_finset_sum_le`;
* the sibling `Work.FTS.StrongEps.ClassCRHS.HkMemXnN0` shows the same bookkeeping for `N₀`.

`K` may depend on `α, C₀, B, Ce, Cs, Φs` but **not** on `w, Φg`.

The proof splits the right-hand side `N α (Ftot α w) (Φs + Φg)` into its twenty §8 pieces
`NBlk α w Φs Φg k` (`HkMemXnNDefs`), each of which is a scalar multiple of a product of two
`ℋ⁴`-honest (or `𝒲^{4,∞}` × `ℋ⁴`-honest) factors, `nb_data` (`HkMemXnNCore`) doing the
bookkeeping and producing a uniform constant `Kbig`; the constants `C1`, `C2` for the
`F_*`-atoms come from `StarAtomsScaled` and `StarAtomsFK`.  The transfer back from the sum to
`N` itself (the pieces agree with `N` on the open quadrant, by `Work.FTS.NonlinRows.Rl1.splitOpen`)
is `HkSumOpenClosure`, and the final norm bound is `HkNorm_finset_sum_le` with
`√(2²⁰) = 1024` and `card (range 20) = 20`. -/
theorem HkMemXnN : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn},
    ∃ K : ℝ, 0 < K ∧ ∀ {w Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      Work.Spaces.HkMem α 4 (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ)) ∧
      Work.FTS.Nonlin.Xn α (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ)) ≤ K := by
  intro α hαmem C₀ B Ce Cs Φs
  obtain ⟨C1, hC1, hs1⟩ := StarAtomsScaled
  obtain ⟨C2, hC2, hs2⟩ := StarAtomsFK
  obtain ⟨Kbig, hKbig, hdata⟩ := nb_data hαmem hC1 hC2 (hs1 α hαmem) (hs2 α hαmem)
  refine ⟨Kbig * (2 ^ 20 * 20) + 1, by positivity, ?_⟩
  intro w Φg hw hXw hB hell hstar
  have hα0 : 0 < α := hαmem.1
  obtain ⟨hsm, hpm, hid⟩ := hdata hw hXw hB hell hstar
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4
      (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ))
      p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand
      (SmoothOpenRHS hα0 hαmem.2 hw hell hstar).2.2.2.2 α 4
  obtain ⟨hmem, hbnd⟩ := HkSumOpenClosure hα0 hcont hsm (fun k hk => (hpm k hk).1)
    (fun z θ hz h1 h2 => hid z θ ⟨hz, h1, h2⟩)
  refine ⟨hmem, ?_⟩
  refine le_trans hbnd ?_
  have h1 : Real.sqrt ((2 : ℝ) ^ 20) = 1024 := by
    rw [show (2 : ℝ) ^ 20 = 1024 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h2 : ∑ k ∈ Finset.range 20, Work.FTS.Nonlin.Xn α (NBlk α w Φs Φg k) ≤ 20 * Kbig := by
    refine le_trans (Finset.sum_le_sum (fun k hk => (hpm k hk).2)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num
  calc Real.sqrt ((2 : ℝ) ^ 20)
        * ∑ k ∈ Finset.range 20, Work.FTS.Nonlin.Xn α (NBlk α w Φs Φg k)
      ≤ 1024 * (20 * Kbig) := by
        rw [h1]
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ ≤ Kbig * (2 ^ 20 * 20) + 1 := by nlinarith [hKbig]

end Work.FTS.StrongEps.ClassCRHS
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNUnif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

/-- **The `N`-block of the scheme's right-hand side is `ℋ⁴`-honest and bounded, for `ClassC`
data of small `ℋ⁴`-size and bounded `ℋ⁶`-size.**

`N α (Ftot α w) (Φs + Φg) = 2·Rop(Φ̃)·F - 2·Uop(Φ̃)·pth F - 2α·Vop(Φ̃)·Dz F
- (1/2)·s2·FK F·pth F - sin²θ·FK F·F`, where `Φ̃ = PhiTil α (Ftot α w) (Φs+Φg)` splits as
`PhiTs α Φs + PhiTil α w Φg` (`Theta α F = (1/(4α))s2·L₁₂ F` is linear in `F`).

Route hints (all tools are on disk and threshold-free):

* `Rop/Uop/Vop` are linear in their argument, so the split of `Φ̃` splits each of them; the
  `PhiTs`-parts are priced by `hstar` (`StarPkgo2.RW`, `VW`, `UsW`, `VzW`) as `𝒲^{4,∞}`-functions,
  the `PhiTil α w Φg`-parts by `hell` (`EllPkgGo.R`, `U`, `V`), which gives
  `HkMem α 4 (Rop …)` and `Xn ≤ Ce·Xn α w ≤ Ce·C₀α²`;
* the pieces whose first factor is the `𝒲`-coefficient `(z+1)/z·Rop(Φ̃_*)` etc. are handled by
  `Work.FTS.OpenPkg.wprod_field_winf` after the identity
  `2·Rop(Φ̃_*)·F = 2·[(z+1)/z·Rop(Φ̃_*)]·[z/(1+z)·F]` (and analogously for `(Uop/s2)·Dth f`,
  where the factor `s2·pth F = Dth F` **everywhere**); the second factor is in `HQo α 4` by
  closure of `ℋ⁴` under a bounded smooth radial factor (`prod_field` with the fixed profiles
  `(z+1)/z`, `z/(1+z)`);
* `FK(F_*+w) = FK(F_*) + FK(w)` (`Work.FTS.GalFields.RHS.FK_add_of_slices`; `FK(F_*)` is the
  explicit `α·2z/(1+z)²`), and `Work.FTS.OpenPkg.fkH_field` bounds `FK(w)` by `Ci·Xn α w`;
* the remaining factors: `F = F_* + w` (additivity), `Dth F`, `Dz F` (`ℋ⁴` via
  `Work.FTS.GalFields.Xn_Dz_le_Xn5` / `Xn_Dth_le_Xn5`, bounded by `HkNorm α 6 w ≤ B`); the
  fixed `F_*`, `Dth F_*`, `Dz F_*` via `Work.FTS.Nonlinear.FstarPkg.{Fstar_W, DthFstar_W,
  DzFstar_W}` (+ `wtoHQ_of_pointwise_open` if a pointwise form is needed);
* sums: `Work.FTS.GalFields.RHS.HkNorm_add_le_open` / `HkNorm_finset_sum_le`;
* the sibling `Work.FTS.StrongEps.ClassCRHS.HkMemXnN0` shows the same bookkeeping for `N₀`.

`K` may depend on `α, C₀, B, Ce, Cs, Φs` but **not** on `w, Φg`.

The proof splits the right-hand side `N α (Ftot α w) (Φs + Φg)` into its twenty §8 pieces
`NBlk α w Φs Φg k` (`HkMemXnNDefs`), each of which is a scalar multiple of a product of two
`ℋ⁴`-honest (or `𝒲^{4,∞}` × `ℋ⁴`-honest) factors, `nb_data` (`HkMemXnNCore`) doing the
bookkeeping and producing a uniform constant `Kbig`; the constants `C1`, `C2` for the
`F_*`-atoms come from `StarAtomsScaled` and `StarAtomsFK`.  The transfer back from the sum to
`N` itself (the pieces agree with `N` on the open quadrant, by `Work.FTS.NonlinRows.Rl1.splitOpen`)
is `HkSumOpenClosure`, and the final norm bound is `HkNorm_finset_sum_le` with
`√(2²⁰) = 1024` and `card (range 20) = 20`. -/
theorem HkMemXnN_unif : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B Ce Cs : ℝ},
    ∃ K : ℝ, 0 < K ∧ ∀ {Φs : Work.FTS.Galerkin.Fn} {w Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      Work.Spaces.HkMem α 4 (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ)) ∧
      Work.FTS.Nonlin.Xn α (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ)) ≤ K := by
  intro α hαmem C₀ B Ce Cs
  obtain ⟨C1, hC1, hs1⟩ := StarAtomsScaled
  obtain ⟨C2, hC2, hs2⟩ := StarAtomsFK
  obtain ⟨Kbig, hKbig, hdata⟩ := nb_data_unifΦ hαmem hC1 hC2 (hs1 α hαmem) (hs2 α hαmem)
  refine ⟨Kbig * (2 ^ 20 * 20) + 1, by positivity, ?_⟩
  intro Φs w Φg hw hXw hB hell hstar
  have hα0 : 0 < α := hαmem.1
  obtain ⟨hsm, hpm, hid⟩ := hdata hw hXw hB hell hstar
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4
      (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ))
      p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand
      (SmoothOpenRHS hα0 hαmem.2 hw hell hstar).2.2.2.2 α 4
  obtain ⟨hmem, hbnd⟩ := HkSumOpenClosure hα0 hcont hsm (fun k hk => (hpm k hk).1)
    (fun z θ hz h1 h2 => hid z θ ⟨hz, h1, h2⟩)
  refine ⟨hmem, ?_⟩
  refine le_trans hbnd ?_
  have h1 : Real.sqrt ((2 : ℝ) ^ 20) = 1024 := by
    rw [show (2 : ℝ) ^ 20 = 1024 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h2 : ∑ k ∈ Finset.range 20, Work.FTS.Nonlin.Xn α (NBlk α w Φs Φg k) ≤ 20 * Kbig := by
    refine le_trans (Finset.sum_le_sum (fun k hk => (hpm k hk).2)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num
  calc Real.sqrt ((2 : ℝ) ^ 20)
        * ∑ k ∈ Finset.range 20, Work.FTS.Nonlin.Xn α (NBlk α w Φs Φg k)
      ≤ 1024 * (20 * Kbig) := by
        rw [h1]
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ ≤ Kbig * (2 ^ 20 * 20) + 1 := by nlinarith [hKbig]

end Work.FTS.StrongEps.ClassCRHS
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.N_b4_ctx =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)
open scoped Real Topology

set_option maxHeartbeats 1600000

theorem N_b4_ctx (C₀ Ce Cs : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.NB4Ctx C C₀ Ce Cs α Φs w Φg := by
  obtain ⟨Cprod, hCprodpos, hprod⟩ := Work.FTS.OpenPkg.prod_field
  obtain ⟨Cw, hCwpos, hwp⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨Cfk, hCfkpos, hfkfield⟩ := Work.FTS.OpenPkg.fkH_field
  obtain ⟨Cphi, hCphipos, hphifield⟩ := Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
  obtain ⟨Csin, hCsinpos, hsinfield⟩ := exists_neg_sinSq_mul
  obtain ⟨CFS, hCFSpos, hFSW⟩ := Work.FTS.Nonlinear.FstarPkg.Fstar_W
  obtain ⟨CDth, hCDthpos, hDthW⟩ := Work.FTS.Nonlinear.FstarPkg.DthFstar_W
  obtain ⟨CDz, hCDzpos, hDzW⟩ := Work.FTS.Nonlinear.FstarPkg.DzFstar_W
  obtain ⟨Catom, hCatompos, hatom⟩ := Work.FTS.StrongEps.ClassCRHS.StarAtomsScaled
  obtain ⟨Cfka, hCfkapos, hfka⟩ := Work.FTS.StrongEps.ClassCRHS.StarAtomsFK
  set C : ℝ := 500 + Cprod + Cw + Cfk + Cphi + Csin + CFS + CDth + CDz + Catom + Cfka
    + max Ce 0 * max C₀ 0 + Cfk * max C₀ 0 + max Cs 0 with hCdef
  have hRnn : (0 : ℝ) ≤ max Ce 0 * max C₀ 0 := by positivity
  have hFknn : (0 : ℝ) ≤ Cfk * max C₀ 0 := by positivity
  have hCsnn : (0 : ℝ) ≤ max Cs 0 := le_max_right _ _
  have hCpos : 0 < C := by rw [hCdef]; linarith
  have hCone : 1 ≤ C := by rw [hCdef]; linarith
  have hCprod_le : Cprod ≤ C := by rw [hCdef]; linarith
  have hCw_le : Cw ≤ C := by rw [hCdef]; linarith
  have hCfk_le : Cfk ≤ C := by rw [hCdef]; linarith
  have hCphi_le : Cphi ≤ C := by rw [hCdef]; linarith
  have hCsin_le : Csin ≤ C := by rw [hCdef]; linarith
  have hCFS_le : CFS ≤ C := by rw [hCdef]; linarith
  have hCDth_le : CDth ≤ C := by rw [hCdef]; linarith
  have hCDz_le : CDz ≤ C := by rw [hCdef]; linarith
  have hCatom_le : Catom ≤ C := by rw [hCdef]; linarith
  have hCfka_le : Cfka ≤ C := by rw [hCdef]; linarith
  have hR_le : max Ce 0 * max C₀ 0 ≤ C := by rw [hCdef]; linarith
  have hFk2_le : Cfk * max C₀ 0 ≤ C := by rw [hCdef]; linarith
  have hCs_le : max Cs 0 ≤ C := by rw [hCdef]; linarith
  have h400 : (400 : ℝ) ≤ C := by rw [hCdef]; linarith
  refine ⟨C, hCpos, ?_⟩
  intro α hαI Φs w Φg hw hXw hell hstar
  obtain ⟨hα0, hα1⟩ := Set.mem_Ioc.mp hαI
  have hsqα : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have hrpow : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  -- ## the two product rules at the single constant `C`
  have hPQo : ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g := by
    intro f g hf hg
    obtain ⟨hm, hb⟩ := hprod α hα0 hα1 f g hf hg
    refine ⟨hm, ?_⟩
    have h1 : Cprod * α ^ (-(1 / 2 : ℝ)) ≤ C * α ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hCprod_le hrpow
    exact le_trans hb (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have hPW : ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g := by
    intro f g hfs hfm hg
    obtain ⟨hm, hb⟩ := hwp α hα0 hα1 f g hfs hfm hg
    refine ⟨hm, ?_⟩
    have hWnn : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hfm
    have h1 : Cw * α ^ (-(1 / 2 : ℝ)) ≤ C * α ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hCw_le hrpow
    exact le_trans hb (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h1 hWnn) (Real.sqrt_nonneg _))
  -- ## the `w`-slots
  have hmem4w : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hmem5w : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 5 (by norm_num) hw.mem
  have hqow : Work.FTS.VocabO.HQo α 4 w := ⟨hw.reg, hmem4w⟩
  have hDthwmem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth w) :=
    Work.FTS.IPGen.HkMem_Dth_le (by linarith) hw.reg hmem5w
  have hDzwmem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w) :=
    Work.FTS.IPGen.HkMem_Dz_le hw.reg hmem5w
  have hqoDthw : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dth w) := ⟨hw.reg.Dth, hDthwmem⟩
  have hqoDzw : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dz w) := ⟨hw.reg.Dz, hDzwmem⟩
  obtain ⟨hwX, hdthwX, hdzwX⟩ := Xn_w_slots_le hα0 hw.reg hmem5w
  -- ## the three `φ = z/(1+z)`-scaled `w`-slots
  have hphiField : ∀ g : Fn, Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => z / (1 + z) * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * g z θ) ≤ Cphi * Work.FTS.Nonlin.Xn α g :=
    fun g hg => hphifield hα0 hα1 hg
  have hphiwD := Work.FTS.StrongEps.ClassCRHS.phi_mul_data hCphipos hphiField hqow hwX
  have hphiDthwD :=
    Work.FTS.StrongEps.ClassCRHS.phi_mul_data hCphipos hphiField hqoDthw hdthwX
  have hphiDzwD := Work.FTS.StrongEps.ClassCRHS.phi_mul_data hCphipos hphiField hqoDzw hdzwX
  have hphiwqo : Work.FTS.VocabO.HQo α 4 (fun z θ => z / (1 + z) * w z θ) :=
    ⟨Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul hw.reg, hphiwD.1⟩
  have hphiDthwqo : Work.FTS.VocabO.HQo α 4 (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) :=
    ⟨Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul hw.reg.Dth, hphiDthwD.1⟩
  have hphiDzwqo : Work.FTS.VocabO.HQo α 4 (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) :=
    ⟨Work.FTS.StrongEps.ClassCRHS.smoothOpen_phi_mul hw.reg.Dz, hphiDzwD.1⟩
  have hphiwX : Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * w z θ)
      ≤ C * (1 + Work.Spaces.HkNorm α 5 w) := by
    refine le_trans hphiwD.2 ?_
    exact mul_le_mul_of_nonneg_right hCphi_le (zero_le_G (α := α) (w := w))
  have hphiDthwX : Work.FTS.Nonlin.Xn α
      (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ)
      ≤ C * (1 + Work.Spaces.HkNorm α 5 w) := by
    refine le_trans hphiDthwD.2 ?_
    exact mul_le_mul_of_nonneg_right hCphi_le (zero_le_G (α := α) (w := w))
  have hphiDzwX : Work.FTS.Nonlin.Xn α
      (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ)
      ≤ C * (1 + Work.Spaces.HkNorm α 5 w) := by
    refine le_trans hphiDzwD.2 ?_
    exact mul_le_mul_of_nonneg_right hCphi_le (zero_le_G (α := α) (w := w))
  -- ## the three perturbed coefficients of `EllPkgGo`
  have hRsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) := hell.R.1.1
  have hRqo : Work.FTS.VocabO.HQo α 4
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) := hell.R.1
  have hRX : Work.FTS.Nonlin.Xn α
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ C * α ^ 2 :=
    le_trans (Work.FTS.StrongEps.ClassCRHS.Xn_Rop_le hw hell hXw)
      (mul_le_mul_of_nonneg_right hR_le hsqα)
  have hUsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) :=
    hell.U.1.1
  have hUqo : Work.FTS.VocabO.HQo α 4 (fun z θ =>
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) :=
    hell.U.1
  have hUX : Work.FTS.Nonlin.Xn α (fun z θ =>
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ)
      ≤ C * α ^ 2 :=
    le_trans (Work.FTS.StrongEps.ClassCRHS.Xn_UopDiv_le hw hell hXw)
      (mul_le_mul_of_nonneg_right hR_le hsqα)
  have hVsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) := hell.V.1.1
  have hVqo : Work.FTS.VocabO.HQo α 4
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) := hell.V.1
  have hVX : Work.FTS.Nonlin.Xn α
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ C * α ^ 2 :=
    le_trans (Work.FTS.StrongEps.ClassCRHS.Xn_Vop_le hw hell hXw)
      (mul_le_mul_of_nonneg_right hR_le hsqα)
  -- ## the `FK w`-atom
  have hFKwsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKw_of_classC hw
  have hFKwD : Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK w z) ∧
      Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK w z) ≤ Cfk * max C₀ 0 * α ^ 2 :=
    Work.FTS.StrongEps.ClassCRHS.FKw_data hXw
      (fun g hg hl => hfkfield α hα0 hα1 g hg hl) hqow hw.l12 hCfkpos
  have hFKwqo : Work.FTS.VocabO.HQo α 4 (fun z _ => Work.Construction.FK w z) :=
    ⟨hFKwsm, hFKwD.1⟩
  have hFKwX : Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK w z) ≤ C * α ^ 2 :=
    le_trans hFKwD.2 (mul_le_mul_of_nonneg_right hFk2_le hsqα)
  -- ## the `-(2α)·hKer`-atom
  have hFKnegsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKneg α
  have hFKnegD := Work.FTS.StrongEps.ClassCRHS.hKerNeg_data α hα0
  have hFKnegWm : Work.Spaces.WlInfMem α 4
      (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) := hFKnegD.1
  have hFKnegW : Work.Spaces.WlInf α 4 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z)
      ≤ C * α := by
    refine le_trans hFKnegD.2 ?_
    rw [show 200 * (2 * α) = 400 * α from by ring]
    exact mul_le_mul_of_nonneg_right h400 hα0.le
  -- ## the star coefficients
  have hstar2 : Work.FTS.VocabO2.StarPkgo2 α Cs Φs := hstar.toStarPkgo2
  have hsw : Work.FTS.VocabO.StarPkgo α Cs Φs := hstar2.toStarPkgo
  have hRssm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_Rs_of_star hα0 hα1 hsw
  have hRsWm : Work.Spaces.WlInfMem α 4
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    hstar2.RW.1
  have hRsW : Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      ≤ C * α :=
    le_trans (Work.FTS.StrongEps.ClassCRHS.WlInf_Rs_le hα0 hstar2)
      (mul_le_mul_of_nonneg_right hCs_le hα0.le)
  have hUssm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_Us_of_star hα0 hα1 hsw
  have hUsWm : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)) :=
    hstar2.UszW.1
  have hUsW : Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ))
      ≤ C * α :=
    le_trans (Work.FTS.StrongEps.ClassCRHS.WlInf_Us_le hα0 hstar2)
      (mul_le_mul_of_nonneg_right hCs_le hα0.le)
  have hVssm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_Vs_of_star hα0 hα1 hsw
  have hVsWm : Work.Spaces.WlInfMem α 4
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    hstar2.VzW.1
  have hVsW : Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      ≤ C * α :=
    le_trans (Work.FTS.StrongEps.ClassCRHS.WlInf_Vs_le hα0 hstar2)
      (mul_le_mul_of_nonneg_right hCs_le hα0.le)
  -- ## the fixed `F_*`-atoms
  have hFWsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.EllipticEst.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hDthFssm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)) := hFWsm.Dth
  have hDzFssm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFWsm.Dz
  obtain ⟨hFWWm, hFWW⟩ := hFSW α hα0 hα1
  obtain ⟨hDthFsWm, hDthFsW⟩ := hDthW α hα0 hα1
  obtain ⟨hDzFsWm, hDzFsW⟩ := hDzW α hα0 hα1
  -- ## the three `φ`-scaled `F_*`-atoms
  obtain ⟨hphiFsqo, hphiFsX0, hphiDthFsqo, hphiDthFsX0, hphiDzFsqo, hphiDzFsX0⟩ :=
    hatom α hαI
  -- ## the two fixed `FK(F_*)`-products
  obtain ⟨hprodFKDthFSqo, hprodFKDthFSX0, hprodFKFSqo, hprodFKFSX0⟩ := hfka α hαI
  -- ## the atom `FK(F_*)` itself
  have hFKFSsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα0 hα1
  have hFKeq : ∀ z : ℝ, -1 < z → ∀ θ : ℝ,
      Work.Construction.FK (Work.Construction.Fstar α) z = (2 * α) * Work.Spaces.hKer z := by
    intro z _ θ
    rw [Work.FTS.Nonlin.FK_Fstar hα0 hα1, Work.Spaces.hKer_apply]
    ring
  have hkerC := Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α (2 * α)
  have hcongr := Work.FTS.Nonlinear.FstarPkg.WlInf_congr
    (f := fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z)
    (g := fun z θ => (2 * α) * Work.Spaces.hKer z) hFKeq α 4
  have hFKFSWm : Work.Spaces.WlInfMem α 4
      (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    hcongr.2.mpr hkerC.1
  have hFKFSW : Work.Spaces.WlInf α 4
      (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) ≤ C * α := by
    rw [hcongr.1]
    refine le_trans hkerC.2 ?_
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * α),
      show 200 * (2 * α) = 400 * α from by ring]
    exact mul_le_mul_of_nonneg_right h400 hα0.le
  -- ## the `-sin²θ`-multiplication
  have hSinMul : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => -(Real.sin θ) ^ 2 * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => -(Real.sin θ) ^ 2 * g z θ)
        ≤ C * Work.FTS.Nonlin.Xn α g := by
    intro g hgs hgm
    obtain ⟨hm, hb⟩ := hsinfield hα0 hα1 hgs hgm
    exact ⟨hm, le_trans hb (mul_le_mul_of_nonneg_right hCsin_le (Real.sqrt_nonneg _))⟩
  exact
    { hα0 := hα0
    , hα1 := hα1
    , hCpos := hCpos
    , hCone := hCone
    , hPQo := hPQo
    , hPW := hPW
    , wqo := hqow
    , dthwqo := hqoDthw
    , dzwqo := hqoDzw
    , wX := hwX
    , dthwX := hdthwX
    , dzwX := hdzwX
    , phiwqo := hphiwqo
    , phiDthwqo := hphiDthwqo
    , phiDzwqo := hphiDzwqo
    , phiwX := hphiwX
    , phiDthwX := hphiDthwX
    , phiDzwX := hphiDzwX
    , Rsm := hRsm
    , Rqo := hRqo
    , RX := hRX
    , Usm := hUsm
    , Uqo := hUqo
    , UX := hUX
    , Vsm := hVsm
    , Vqo := hVqo
    , VX := hVX
    , FKwsm := hFKwsm
    , FKwqo := hFKwqo
    , FKwX := hFKwX
    , FKnegsm := hFKnegsm
    , FKnegWm := hFKnegWm
    , FKnegW := hFKnegW
    , Rssm := hRssm
    , RsWm := hRsWm
    , RsW := hRsW
    , Ussm := hUssm
    , UsWm := hUsWm
    , UsW := hUsW
    , Vssm := hVssm
    , VsWm := hVsWm
    , VsW := hVsW
    , FWsm := hFWsm
    , FWWm := hFWWm
    , FWW := le_trans hFWW (mul_le_mul_of_nonneg_right hCFS_le hα0.le)
    , DthFssm := hDthFssm
    , DthFsWm := hDthFsWm
    , DthFsW := le_trans hDthFsW (mul_le_mul_of_nonneg_right hCDth_le hsqα)
    , DzFssm := hDzFssm
    , DzFsWm := hDzFsWm
    , DzFsW := le_trans hDzFsW (mul_le_mul_of_nonneg_right hCDz_le hα0.le)
    , phiFsqo := hphiFsqo
    , phiFsX := le_trans hphiFsX0 hCatom_le
    , phiDthFsqo := hphiDthFsqo
    , phiDthFsX := le_trans hphiDthFsX0 hCatom_le
    , phiDzFsqo := hphiDzFsqo
    , phiDzFsX := le_trans hphiDzFsX0 hCatom_le
    , FKFSsm := hFKFSsm
    , FKFSWm := hFKFSWm
    , FKFSW := hFKFSW
    , prodFKDthFSqo := hprodFKDthFSqo
    , prodFKDthFSX := le_trans hprodFKDthFSX0 hCfka_le
    , prodFKFSqo := hprodFKFSqo
    , prodFKFSX := le_trans hprodFKFSX0 hCfka_le
    , hSinMul := hSinMul }

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.N_b4_g1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

/-! ## The level-`4` pricing of the five `Z`-pieces `k = 0, 2, 4, 6, 8` of `NBlk`

Each of the five pieces is one product of an `α`-small coefficient with a `w`-slot, so a single
application of `mulQo_absorb` (coefficient `HQo α 4`, priced by `C·α²`) resp. `mulW_absorb`
(coefficient `SmoothOpen`/`WlInfMem`, priced by `C·α`) closes it; see
`NOTES_N_b4_pieces.md` for the table.  The constant `K := 2·|C|³ + 1` dominates every
resulting bound (`2C²G` for the `ℚ`-slots and `2C³G` for the `𝒲`-slots, `G = 1 + HkNorm α 5 w`),
and is unconditionally positive (the context already forces `1 ≤ C`, but `K` must be positive
before any context is available). -/

/-- `2C² ≤ 2|C|³ + 1` for `C ≥ 1`. -/
private theorem two_mul_sq_le (C : ℝ) (hCpos : 0 < C) (hCone : 1 ≤ C) :
    2 * C * C ≤ 2 * |C| ^ 3 + 1 := by
  have habs : |C| = C := abs_of_pos hCpos
  rw [habs]
  nlinarith [hCone, sq_nonneg C, mul_nonneg (sq_nonneg C) (by linarith : (0 : ℝ) ≤ C - 1)]

/-- `2C³·A ≤ (2|C|³ + 1)·A` for `A ≥ 0`. -/
private theorem two_mul_cube_mul_le (C : ℝ) (hCpos : 0 < C) {A : ℝ} (hA : 0 ≤ A) :
    2 * C * C * (C * A) ≤ (2 * |C| ^ 3 + 1) * A := by
  have habs : |C| = C := abs_of_pos hCpos
  rw [habs]
  nlinarith [hA]

theorem N_b4_g1 (C C₀ Ce Cs : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.NB4Ctx C C₀ Ce Cs α Φs w Φg →
    ∀ k ∈ ({0, 2, 4, 6, 8} : Finset ℕ),
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ K * (1 + Work.Spaces.HkNorm α 5 w) := by
  refine ⟨2 * |C| ^ 3 + 1, by positivity, ?_⟩
  intro α hα Φs w Φg ctx k hk
  have hCpos : (0 : ℝ) < C := ctx.hCpos
  have hCone : (1 : ℝ) ≤ C := ctx.hCone
  have hG : (0 : ℝ) ≤ 1 + Work.Spaces.HkNorm α 5 w := zero_le_G
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · -- `k = 0`: `2·(Rop Φ̃_g · w)`
    have h := mulQo_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPQo (c := 2) (s := 2) (by norm_num)
      ctx.hCpos.le zero_le_G ctx.Rqo ctx.wqo ctx.RX ctx.wX
    have hAB : |(2 : ℝ)| * C * C = 2 * C * C := by norm_num
    rw [hAB] at h
    refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
    have h2 : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 0)
        ≤ 2 * C * C * (1 + Work.Spaces.HkNorm α 5 w) := by
      simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2
    exact le_trans h2 (mul_le_mul_of_nonneg_right (two_mul_sq_le C hCpos hCone) hG)
  · -- `k = 2`: `2·(Rs · φw)`
    have hbF : Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z *
        Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) ≤ C * α ^ 1 := by
      simpa only [pow_one] using ctx.RsW
    have hQ : (0 : ℝ) ≤ C * (1 + Work.Spaces.HkNorm α 5 w) := mul_nonneg hCpos.le hG
    have h := mulW_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPW (c := 2) (s := 1) (by norm_num)
      ctx.hCpos.le hQ ctx.Rssm ctx.RsWm ctx.phiwqo hbF ctx.phiwX
    have hAB : |(2 : ℝ)| * C * C * (C * (1 + Work.Spaces.HkNorm α 5 w))
        = 2 * C * C * (C * (1 + Work.Spaces.HkNorm α 5 w)) := by norm_num
    rw [hAB] at h
    refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
    have h2 : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 2)
        ≤ 2 * C * C * (C * (1 + Work.Spaces.HkNorm α 5 w)) := by
      simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2
    exact le_trans h2 (two_mul_cube_mul_le C hCpos hG)
  · -- `k = 4`: `-2·(Uc · D_θw)`
    have h := mulQo_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPQo (c := -2) (s := 2) (by norm_num)
      ctx.hCpos.le zero_le_G ctx.Uqo ctx.dthwqo ctx.UX ctx.dthwX
    have hAB : |(-2 : ℝ)| * C * C = 2 * C * C := by norm_num
    rw [hAB] at h
    refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
    have h2 : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 4)
        ≤ 2 * C * C * (1 + Work.Spaces.HkNorm α 5 w) := by
      simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2
    exact le_trans h2 (mul_le_mul_of_nonneg_right (two_mul_sq_le C hCpos hCone) hG)
  · -- `k = 6`: `-2·(Us · φD_θw)`
    have hbF : Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z *
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
          / Work.Construction.s2 θ)) ≤ C * α ^ 1 := by
      simpa only [pow_one] using ctx.UsW
    have hQ : (0 : ℝ) ≤ C * (1 + Work.Spaces.HkNorm α 5 w) := mul_nonneg hCpos.le hG
    have h := mulW_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPW (c := -2) (s := 1) (by norm_num)
      ctx.hCpos.le hQ ctx.Ussm ctx.UsWm ctx.phiDthwqo hbF ctx.phiDthwX
    have hAB : |(-2 : ℝ)| * C * C * (C * (1 + Work.Spaces.HkNorm α 5 w))
        = 2 * C * C * (C * (1 + Work.Spaces.HkNorm α 5 w)) := by norm_num
    rw [hAB] at h
    refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
    have h2 : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 6)
        ≤ 2 * C * C * (C * (1 + Work.Spaces.HkNorm α 5 w)) := by
      simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2
    exact le_trans h2 (two_mul_cube_mul_le C hCpos hG)
  · -- `k = 8`: `-(2α)·(Vc · D_zw)`
    have h := mulQo_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPQo (c := -(2 * α)) (s := 2)
      (by norm_num) ctx.hCpos.le zero_le_G ctx.Vqo ctx.dzwqo ctx.VX ctx.dzwX
    have hc : |(-(2 * α))| = 2 * α := by
      rw [abs_neg, abs_of_pos (by linarith [ctx.hα0] : (0 : ℝ) < 2 * α)]
    rw [hc] at h
    refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
    have h2 : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 8)
        ≤ 2 * α * C * C * (1 + Work.Spaces.HkNorm α 5 w) := by
      simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2
    have hαle : 2 * α ≤ 2 := by linarith [hα.2]
    have hCG : (0 : ℝ) ≤ C * C * (1 + Work.Spaces.HkNorm α 5 w) :=
      mul_nonneg (mul_nonneg hCpos.le hCpos.le) hG
    have hstep : 2 * α * C * C * (1 + Work.Spaces.HkNorm α 5 w)
        ≤ 2 * C * C * (1 + Work.Spaces.HkNorm α 5 w) := by
      calc 2 * α * C * C * (1 + Work.Spaces.HkNorm α 5 w)
          = 2 * α * (C * C * (1 + Work.Spaces.HkNorm α 5 w)) := by ring
        _ ≤ 2 * (C * C * (1 + Work.Spaces.HkNorm α 5 w)) :=
            mul_le_mul_of_nonneg_right hαle hCG
        _ = 2 * C * C * (1 + Work.Spaces.HkNorm α 5 w) := by ring
    exact le_trans (le_trans h2 hstep)
      (mul_le_mul_of_nonneg_right (two_mul_sq_le C hCpos hCone) hG)

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.N0Term_boundT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C.PairingT

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin
open Work.FTS.VocabO (HQo)
open Work.FTS.StrongEps.E4R3.N4C

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The `N₀` block** (seven pieces), honest version of `Open2.N0Term_bound2`:
`|IP α (N₀ α (F_*+g) g) g| ≤ 7·(K₀(C+1)·Pbd α X)`. -/
theorem N0Term_boundT {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {α₂ Ct K₀ C C₀ α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (h : Work.FTS.StrongEps.E4R3.N4C.BlkCtxO IP α₂ Ct K₀ C C₀ α g Φs Φg) :
    |IP α (Work.Construction.N0 α (Work.Construction.Ftot α g) g) g|
      ≤ 7 * (K₀ * (C + 1) * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α g)) := by
  set N0v := Work.Construction.N0 α (Work.Construction.Ftot α g) g with hN0vdef
  set X := Work.FTS.Nonlin.Xn α g with hXdef
  have hE : N4ExtraH IP α₂ Ct := h.hE
  have hα : 0 < α := h.hα
  have hα1 : α ≤ 1 := h.hα1
  have hαIoc : α ∈ Set.Ioc 0 α₂ := h.hαIoc
  have hCt : 0 < Ct := h.hCt
  have hK₀Ct : Ct ≤ K₀ := h.hK₀Ct
  have hK₀one : 1 ≤ K₀ := h.hK₀one
  have hC : 0 < C := h.hC
  have hR : RowInputsTO IP α C g Φs Φg := h.hR
  have hg4 : HQo α 4 g := BlkCtxO.hg4 h
  have hX0 : 0 ≤ X := by rw [hXdef]; exact Work.Spaces.HkNorm_nonneg α 4 g
  have hPbd0 : 0 ≤ Pbd α X := Pbd_nonneg hα.le hX0
  have g1 : GoodO α (N0fix α) := hR.r1.1
  have g2 : GoodO α (N03g α g) := hR.r2.1
  have g3 : GoodO α (N04aF α g) := hR.r3.1
  have g4 : GoodO α (N04bF α g) := hR.r4.1
  have g5 : GoodO α (N05aF α g) := hR.r5.1
  have g6 : GoodO α (N05bF α g) := hR.r6.1
  have g7 : GoodO α (N06F α g) := hR.r7.1
  have g12' : GoodO α (N0fix α + N03g α g) := goodO_add g1 g2
  have g123' : GoodO α (N0fix α + N03g α g + N04aF α g) := goodO_add g12' g3
  have g1234' : GoodO α (N0fix α + N03g α g + N04aF α g + N04bF α g) := goodO_add g123' g4
  have g12345' : GoodO α (N0fix α + N03g α g + N04aF α g + N04bF α g + N05aF α g) :=
    goodO_add g1234' g5
  have g123456' : GoodO α (N0fix α + N03g α g + N04aF α g + N04bF α g + N05aF α g
      + N05bF α g) := goodO_add g12345' g6
  have gN0sum : GoodO α (N0fix α + N03g α g + N04aF α g + N04bF α g + N05aF α g + N05bF α g
      + N06F α g) := goodO_add g123456' g7
  have hcongr : IP α N0v g = IP α (N0fix α + N03g α g + N04aF α g + N04bF α g
      + N05aF α g + N05bF α g + N06F α g) g := by
    refine hE.congr α hαIoc N0v _ g hR.hkN0 gN0sum hg4 ?_
    intro z θ hzθ
    rw [hN0vdef, hR.hN0 z θ hzθ]
    simp only [Pi.add_apply]
    ring
  have hsum : IP α N0v g = IP α (N0fix α) g + IP α (N03g α g) g + IP α (N04aF α g) g
      + IP α (N04bF α g) g + IP α (N05aF α g) g + IP α (N05bF α g) g
      + IP α (N06F α g) g := by
    rw [hcongr]
    exact IPO_add7 hE hαIoc hg4 g1 g2 g3 g4 g5 g6 g7
      g12' g123' g1234' g12345' g123456'
  have h1 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N0fix α) (α ^ 2) hR.r1.2
    (alpha_sq_mul_le_Pbd hα hX0) hR.r1.1
  have h2 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N03g α g) (α ^ (-(1 : ℝ)) * X ^ 2)
    hR.r2.2 (by
      have he : α ^ (-(1 : ℝ)) * X ^ 2 * X = α ^ (-(1 : ℝ)) * X ^ 3 := by ring
      rw [he]; exact rpow_neg_one_mul_cube_le_Pbd hα hα1 hX0) hR.r2.1
  have h3 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N04aF α g) (Real.sqrt α * X) hR.r3.2
    (by
      have he : Real.sqrt α * X * X = Real.sqrt α * X ^ 2 := by ring
      rw [he]; exact sqrt_mul_sq_le_Pbd hα hX0) hR.r3.1
  have h4 := pieceDirO (N04bF α g) (α ^ (-(3 / 2 : ℝ)) * X ^ 3) hR.r4.2
    (rpow_neg_three_half_mul_cube_le_Pbd hα hX0) hPbd0 hC hK₀one
  have h5 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N05aF α g) (Real.sqrt α * X) hR.r5.2
    (by
      have he : Real.sqrt α * X * X = Real.sqrt α * X ^ 2 := by ring
      rw [he]; exact sqrt_mul_sq_le_Pbd hα hX0) hR.r5.1
  have h6 := pieceDirO (N05bF α g) (α ^ (-(1 / 2 : ℝ)) * X ^ 3) hR.r6.2
    (rpow_neg_half_mul_cube_le_Pbd hα hα1 hX0) hPbd0 hC hK₀one
  have h7 := pieceDirO (N06F α g) (Real.sqrt α * X ^ 2) hR.r7.2
    (sqrt_mul_sq_le_Pbd hα hX0) hPbd0 hC hK₀one
  have htri : |IP α (N0fix α) g + IP α (N03g α g) g + IP α (N04aF α g) g
      + IP α (N04bF α g) g + IP α (N05aF α g) g + IP α (N05bF α g) g
      + IP α (N06F α g) g|
      ≤ |IP α (N0fix α) g| + |IP α (N03g α g) g| + |IP α (N04aF α g) g|
      + |IP α (N04bF α g) g| + |IP α (N05aF α g) g| + |IP α (N05bF α g) g|
      + |IP α (N06F α g) g| := by
    have h8 := abs_add_le (IP α (N0fix α) g + IP α (N03g α g) g + IP α (N04aF α g) g
      + IP α (N04bF α g) g + IP α (N05aF α g) g + IP α (N05bF α g) g)
      (IP α (N06F α g) g)
    have h9 := Work.Construction.abs_sum_le_five (IP α (N0fix α) g) (IP α (N03g α g) g)
      (IP α (N04aF α g) g) (IP α (N04bF α g) g) (IP α (N05aF α g) g)
    have h10 := abs_add_le (IP α (N0fix α) g + IP α (N03g α g) g + IP α (N04aF α g) g
      + IP α (N04bF α g) g + IP α (N05aF α g) g) (IP α (N05bF α g) g)
    linarith [h8, h9, h10]
  rw [hsum]
  linarith [htri, h1, h2, h3, h4, h5, h6, h7,
    abs_nonneg (IP α (N0fix α) g), abs_nonneg (IP α (N03g α g) g),
    abs_nonneg (IP α (N04aF α g) g), abs_nonneg (IP α (N04bF α g) g),
    abs_nonneg (IP α (N05aF α g) g), abs_nonneg (IP α (N05bF α g) g),
    abs_nonneg (IP α (N06F α g) g)]

end Work.FTS.StrongEps.E4R3.N4C.PairingT
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.NTerm_boundT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C.PairingT

open Work.FTS.Galerkin (Fn)
open Work.FTS.VocabO (HQo)
open Work.FTS.Nonlin (Xn Pbd N1gg N1gs N1sg N1ss N2gg N2gs N2sg N2ss N3gg N3gs N3sg
  N3ss N4gg N4gs N4sg N4ss N5gg N5gs N5sg N5ss
  Pbd_nonneg alpha_sq_mul_le_Pbd sqrt_mul_sq_le_Pbd rpow_neg_half_mul_cube_le_Pbd
  rpow_three_half_mul_sq_le_Pbd cube_le_Pbd cube_alpha_mul_le_Pbd)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- `|a + b + c + d| ≤ |a| + |b| + |c| + |d|`. -/
theorem abs_sum_le_fourT (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith [h1, h2, h3, abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg d]

/-- **The `N`-block of the pairing estimate** (twenty pieces): with the honest context
`BlkCtxO`, `|IP α (N α (F_*+g) (Φ_*+Φ_g)) g| ≤ 20·(K₀(C+1)·Pbd α X)`. -/
theorem NTerm_boundT {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {α₂ Ct K₀ C C₀ α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (h : Work.FTS.StrongEps.E4R3.N4C.BlkCtxO IP α₂ Ct K₀ C C₀ α g Φs Φg) :
    |IP α (Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) g|
      ≤ 20 * (K₀ * (C + 1) * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α g)) := by
  set Nv := Work.Construction.N α (Work.Construction.Ftot α g)
    (fun z θ => Φs z θ + Φg z θ) with hNvdef
  set X := Xn α g with hXdef
  have hE : N4ExtraH IP α₂ Ct := h.hE
  have hα : 0 < α := h.hα
  have hα1 : α ≤ 1 := h.hα1
  have hαIoc : α ∈ Set.Ioc 0 α₂ := h.hαIoc
  have hCt : 0 < Ct := h.hCt
  have hK₀Ct : Ct ≤ K₀ := h.hK₀Ct
  have hK₀one : 1 ≤ K₀ := h.hK₀one
  have hK₀pos : 0 < K₀ := h.hK₀pos
  have hC : 0 < C := h.hC
  have hR : RowInputsTO IP α C g Φs Φg := h.hR
  have hg4 : HQo α 4 g := h.hg4
  have hX0 : 0 ≤ X := Work.Spaces.HkNorm_nonneg α 4 g
  have hPbd0 : 0 ≤ Pbd α X := Pbd_nonneg hα.le hX0
  have hconv : K₀ * (C + 1) * Pbd α X ≤ C₀ * C * Pbd α X := by
    have hb := mul_le_mul_of_nonneg_right h.hbigK hPbd0
    linarith [hb]
  -- the `GoodO` witnesses of the nineteen `N₁`--`N₅` pieces
  have g8 : GoodO α (N1gg α g Φg) := hR.r8.1
  have g9 : GoodO α (N1gs α g Φg) := hR.r9.1
  have g10 : GoodO α (N1sg α Φs g) := hR.r10.1
  have g11 : GoodO α (N1ss α Φs) := hR.r11.1
  have g12 : GoodO α (N2gg α g Φg) := hR.r12.1
  have g13 : GoodO α (N2gs α g Φg) := hR.r13.1
  have g14 : GoodO α (N2sg α Φs g) := hR.r14.1
  have g15 : GoodO α (N2ss α Φs) := hR.r15.1
  have g16 : GoodO α (N3gg α g Φg) := hR.r16.1
  have g17 : GoodO α (N3gs α g Φg) := hR.r17.1
  have g18 : GoodO α (N3sg α Φs g) := hR.r18.1
  have g19 : GoodO α (N3ss α Φs) := hR.r19.1
  have g20 : GoodO α (N4gg α g) := hR.r20.1
  have g21 : GoodO α (N4gs α g) := hR.r21.1
  have g22 : GoodO α (N4sg α g) := hR.r22.1
  have g23 : GoodO α (N4ss α) := hR.r23.1
  have g24 : GoodO α (N5gg g) := hR.r24.1
  have g25 : GoodO α (N5gs α g) := hR.r25.1
  have g26 : GoodO α (N5sg α g) := hR.r25.2.1
  have g27 : GoodO α (N5ss α) := hR.r26.1
  -- the five four-term groups, and the whole `N`
  have gG1 : GoodO α (N1gg α g Φg + N1gs α g Φg + N1sg α Φs g + N1ss α Φs) :=
    goodO_add (goodO_add (goodO_add g8 g9) g10) g11
  have gG2 : GoodO α (N2gg α g Φg + N2gs α g Φg + N2sg α Φs g + N2ss α Φs) :=
    goodO_add (goodO_add (goodO_add g12 g13) g14) g15
  have gG3 : GoodO α (N3gg α g Φg + N3gs α g Φg + N3sg α Φs g + N3ss α Φs) :=
    goodO_add (goodO_add (goodO_add g16 g17) g18) g19
  have gG4 : GoodO α (N4gg α g + N4gs α g + N4sg α g + N4ss α) :=
    goodO_add (goodO_add (goodO_add g20 g21) g22) g23
  have gG5 : GoodO α (N5gg g + N5gs α g + N5sg α g + N5ss α) :=
    goodO_add (goodO_add (goodO_add g24 g25) g26) g27
  have gG12 : GoodO α ((N1gg α g Φg + N1gs α g Φg + N1sg α Φs g + N1ss α Φs)
      + (N2gg α g Φg + N2gs α g Φg + N2sg α Φs g + N2ss α Φs)) := goodO_add gG1 gG2
  have gG123 : GoodO α ((N1gg α g Φg + N1gs α g Φg + N1sg α Φs g + N1ss α Φs)
      + (N2gg α g Φg + N2gs α g Φg + N2sg α Φs g + N2ss α Φs)
      + (N3gg α g Φg + N3gs α g Φg + N3sg α Φs g + N3ss α Φs)) := goodO_add gG12 gG3
  have gG1234 : GoodO α ((N1gg α g Φg + N1gs α g Φg + N1sg α Φs g + N1ss α Φs)
      + (N2gg α g Φg + N2gs α g Φg + N2sg α Φs g + N2ss α Φs)
      + (N3gg α g Φg + N3gs α g Φg + N3sg α Φs g + N3ss α Φs)
      + (N4gg α g + N4gs α g + N4sg α g + N4ss α)) := goodO_add gG123 gG4
  have gGsum : GoodO α ((N1gg α g Φg + N1gs α g Φg + N1sg α Φs g + N1ss α Φs)
      + (N2gg α g Φg + N2gs α g Φg + N2sg α Φs g + N2ss α Φs)
      + (N3gg α g Φg + N3gs α g Φg + N3sg α Φs g + N3ss α Φs)
      + (N4gg α g + N4gs α g + N4sg α g + N4ss α)
      + (N5gg g + N5gs α g + N5sg α g + N5ss α)) := goodO_add gG1234 gG5
  have hNv : GoodO α Nv :=
    goodO_of_eqOn_Qd gGsum (fun z θ hzθ => by
      rw [hNvdef, hR.hN z θ hzθ]; simp only [Pi.add_apply])
  -- the block
  set G1 : Fn := N1gg α g Φg + N1gs α g Φg + N1sg α Φs g + N1ss α Φs with hG1def
  set G2 : Fn := N2gg α g Φg + N2gs α g Φg + N2sg α Φs g + N2ss α Φs with hG2def
  set G3 : Fn := N3gg α g Φg + N3gs α g Φg + N3sg α Φs g + N3ss α Φs with hG3def
  set G4 : Fn := N4gg α g + N4gs α g + N4sg α g + N4ss α with hG4def
  set G5 : Fn := N5gg g + N5gs α g + N5sg α g + N5ss α with hG5def
  have hcongr : IP α Nv g = IP α (G1 + G2 + G3 + G4 + G5) g := by
    refine hE.congr α hαIoc Nv _ g hR.hkN ?_ hg4 ?_
    · rw [hG1def, hG2def, hG3def, hG4def, hG5def]
      exact gGsum
    · intro z θ hzθ
      rw [hNvdef, hR.hN z θ hzθ, hG1def, hG2def, hG3def, hG4def, hG5def]
      simp only [Pi.add_apply]
      try ring
  have h1 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N1gg α g Φg)
    (α ^ (-(1 / 2 : ℝ)) * X ^ 2) hR.r8.2 (by
      have he : α ^ (-(1 / 2 : ℝ)) * X ^ 2 * X = α ^ (-(1 / 2 : ℝ)) * X ^ 3 := by ring
      rw [he]; exact rpow_neg_half_mul_cube_le_Pbd hα hα1 hX0) hR.r8.1
  have h2 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N1gs α g Φg)
    (Real.sqrt α * X) hR.r9.2 (by
      have he : Real.sqrt α * X * X = Real.sqrt α * X ^ 2 := by ring
      rw [he]; exact sqrt_mul_sq_le_Pbd hα hX0) hR.r9.1
  have h3 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N1sg α Φs g)
    (Real.sqrt α * X) hR.r10.2 (by
      have he : Real.sqrt α * X * X = Real.sqrt α * X ^ 2 := by ring
      rw [he]; exact sqrt_mul_sq_le_Pbd hα hX0) hR.r10.1
  have h4 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N1ss α Φs)
    (α ^ 2) hR.r11.2 (alpha_sq_mul_le_Pbd hα hX0) hR.r11.1
  have h5 := pieceDirO (N2gg α g Φg) (α ^ (-(1 / 2 : ℝ)) * X ^ 3) hR.r12.2
    (rpow_neg_half_mul_cube_le_Pbd hα hα1 hX0) hPbd0 hC hK₀one
  have h6 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N2gs α g Φg)
    (α ^ (3 / 2 : ℝ) * X) hR.r13.2 (by
      have he : α ^ (3 / 2 : ℝ) * X * X = α ^ (3 / 2 : ℝ) * X ^ 2 := by ring
      rw [he]; exact rpow_three_half_mul_sq_le_Pbd hα hα1 hX0) hR.r13.1
  have h7 := pieceDirO (N2sg α Φs g) (Real.sqrt α * X ^ 2) hR.r14.2
    (sqrt_mul_sq_le_Pbd hα hX0) hPbd0 hC hK₀one
  have h8 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N2ss α Φs)
    (α ^ 2) hR.r15.2 (alpha_sq_mul_le_Pbd hα hX0) hR.r15.1
  -- **row 16 at its actual rate `X³`** (the relaxed rate of the honest row table)
  have h9 := pieceDirO (N3gg α g Φg) (X ^ 3) hR.r16.2
    (cube_le_Pbd hα hα1 hX0) hPbd0 hC hK₀one
  have h10 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N3gs α g Φg)
    (α ^ (3 / 2 : ℝ) * X) hR.r17.2 (by
      have he : α ^ (3 / 2 : ℝ) * X * X = α ^ (3 / 2 : ℝ) * X ^ 2 := by ring
      rw [he]; exact rpow_three_half_mul_sq_le_Pbd hα hα1 hX0) hR.r17.1
  have h11 := pieceDirO (N3sg α Φs g) (α ^ (3 / 2 : ℝ) * X ^ 2) hR.r18.2
    (rpow_three_half_mul_sq_le_Pbd hα hα1 hX0) hPbd0 hC hK₀one
  have h12 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N3ss α Φs)
    (α ^ 3) hR.r19.2 (cube_alpha_mul_le_Pbd hα hα1 hX0) hR.r19.1
  have h13 := pieceDirO (N4gg α g) (α ^ (-(1 / 2 : ℝ)) * X ^ 3) hR.r20.2
    (rpow_neg_half_mul_cube_le_Pbd hα hα1 hX0) hPbd0 hC hK₀one
  have h14 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N4gs α g)
    (α ^ (3 / 2 : ℝ) * X) hR.r21.2 (by
      have he : α ^ (3 / 2 : ℝ) * X * X = α ^ (3 / 2 : ℝ) * X ^ 2 := by ring
      rw [he]; exact rpow_three_half_mul_sq_le_Pbd hα hα1 hX0) hR.r21.1
  have h15 := pieceDirO (N4sg α g) (Real.sqrt α * X ^ 2) hR.r22.2
    (sqrt_mul_sq_le_Pbd hα hX0) hPbd0 hC hK₀one
  have h16 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N4ss α)
    (α ^ 3) hR.r23.2 (cube_alpha_mul_le_Pbd hα hα1 hX0) hR.r23.1
  have h17 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N5gg g)
    (X ^ 2) hR.r24.2 (cube_le_Pbd hα hα1 hX0) hR.r24.1
  have h18 : |IP α (N5gs α g) g| + |IP α (N5sg α g) g| ≤ K₀ * (C + 1) * Pbd α X := by
    have hgs : |IP α (N5gs α g) g| ≤ Ct * Xn α (N5gs α g) * X :=
      hE.cs α hαIoc _ g hR.r25.1 hg4
    have hsg : |IP α (N5sg α g) g| ≤ Ct * Xn α (N5sg α g) * X :=
      hE.cs α hαIoc _ g hR.r25.2.1 hg4
    have hsum : Xn α (N5gs α g) + Xn α (N5sg α g) ≤ C * (Real.sqrt α * X) := hR.r25.2.2
    have hb : Ct * Xn α (N5gs α g) * X + Ct * Xn α (N5sg α g) * X
        ≤ Ct * (C * (Real.sqrt α * X)) * X := by
      have he : Ct * Xn α (N5gs α g) * X + Ct * Xn α (N5sg α g) * X
          = Ct * (Xn α (N5gs α g) + Xn α (N5sg α g)) * X := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hCt.le) hX0
    have hs : Real.sqrt α * X * X = Real.sqrt α * X ^ 2 := by ring
    have hPB : Real.sqrt α * X ^ 2 ≤ Pbd α X := sqrt_mul_sq_le_Pbd hα hX0
    have heq : Ct * (C * (Real.sqrt α * X)) * X = Ct * C * (Real.sqrt α * X * X) := by ring
    have hfin : Ct * C * (Real.sqrt α * X * X) ≤ K₀ * (C + 1) * Pbd α X := by
      rw [hs]
      have h1' : Ct * C * Pbd α X ≤ K₀ * C * Pbd α X :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK₀Ct hC.le) hPbd0
      have h2' : K₀ * C * Pbd α X ≤ K₀ * (C + 1) * Pbd α X := by
        have h := mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) hPbd0
        nlinarith [h, hK₀pos.le, hPbd0]
      exact le_trans (mul_le_mul_of_nonneg_left hPB (by positivity)) (le_trans h1' h2')
    linarith [hgs, hsg, hb, le_of_eq heq, hfin]
  have h19 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N5ss α)
    (α ^ 2) hR.r26.2 (alpha_sq_mul_le_Pbd hα hX0) hR.r26.1
  have hG1 : |IP α G1 g| ≤ 4 * (K₀ * (C + 1) * Pbd α X) := by
    have hsum : IP α G1 g = IP α (N1gg α g Φg) g + IP α (N1gs α g Φg) g
        + IP α (N1sg α Φs g) g + IP α (N1ss α Φs) g := by
      rw [hG1def]
      exact IPO_add4 hE hαIoc hg4 g8 g9 g10 g11 (goodO_add g8 g9)
        (goodO_add (goodO_add g8 g9) g10)
    rw [hsum]
    linarith [abs_sum_le_fourT (IP α (N1gg α g Φg) g)
      (IP α (N1gs α g Φg) g) (IP α (N1sg α Φs g) g) (IP α (N1ss α Φs) g),
      h1, h2, h3, h4, hconv,
      abs_nonneg (IP α (N1gg α g Φg) g), abs_nonneg (IP α (N1gs α g Φg) g),
      abs_nonneg (IP α (N1sg α Φs g) g), abs_nonneg (IP α (N1ss α Φs) g)]
  have hG2 : |IP α G2 g| ≤ 4 * (K₀ * (C + 1) * Pbd α X) := by
    have hsum : IP α G2 g = IP α (N2gg α g Φg) g + IP α (N2gs α g Φg) g
        + IP α (N2sg α Φs g) g + IP α (N2ss α Φs) g := by
      rw [hG2def]
      exact IPO_add4 hE hαIoc hg4 g12 g13 g14 g15 (goodO_add g12 g13)
        (goodO_add (goodO_add g12 g13) g14)
    rw [hsum]
    linarith [abs_sum_le_fourT (IP α (N2gg α g Φg) g)
      (IP α (N2gs α g Φg) g) (IP α (N2sg α Φs g) g) (IP α (N2ss α Φs) g),
      h5, h6, h7, h8, hconv,
      abs_nonneg (IP α (N2gg α g Φg) g), abs_nonneg (IP α (N2gs α g Φg) g),
      abs_nonneg (IP α (N2sg α Φs g) g), abs_nonneg (IP α (N2ss α Φs) g)]
  have hG3 : |IP α G3 g| ≤ 4 * (K₀ * (C + 1) * Pbd α X) := by
    have hsum : IP α G3 g = IP α (N3gg α g Φg) g + IP α (N3gs α g Φg) g
        + IP α (N3sg α Φs g) g + IP α (N3ss α Φs) g := by
      rw [hG3def]
      exact IPO_add4 hE hαIoc hg4 g16 g17 g18 g19 (goodO_add g16 g17)
        (goodO_add (goodO_add g16 g17) g18)
    rw [hsum]
    linarith [abs_sum_le_fourT (IP α (N3gg α g Φg) g)
      (IP α (N3gs α g Φg) g) (IP α (N3sg α Φs g) g) (IP α (N3ss α Φs) g),
      h9, h10, h11, h12, hconv,
      abs_nonneg (IP α (N3gg α g Φg) g), abs_nonneg (IP α (N3gs α g Φg) g),
      abs_nonneg (IP α (N3sg α Φs g) g), abs_nonneg (IP α (N3ss α Φs) g)]
  have hG4 : |IP α G4 g| ≤ 4 * (K₀ * (C + 1) * Pbd α X) := by
    have hsum : IP α G4 g = IP α (N4gg α g) g + IP α (N4gs α g) g
        + IP α (N4sg α g) g + IP α (N4ss α) g := by
      rw [hG4def]
      exact IPO_add4 hE hαIoc hg4 g20 g21 g22 g23 (goodO_add g20 g21)
        (goodO_add (goodO_add g20 g21) g22)
    rw [hsum]
    linarith [abs_sum_le_fourT (IP α (N4gg α g) g) (IP α (N4gs α g) g)
      (IP α (N4sg α g) g) (IP α (N4ss α) g), h13, h14, h15, h16, hconv,
      abs_nonneg (IP α (N4gg α g) g), abs_nonneg (IP α (N4gs α g) g),
      abs_nonneg (IP α (N4sg α g) g), abs_nonneg (IP α (N4ss α) g)]
  have hG5 : |IP α G5 g| ≤ 4 * (K₀ * (C + 1) * Pbd α X) := by
    have hsum : IP α G5 g = IP α (N5gg g) g + IP α (N5gs α g) g
        + IP α (N5sg α g) g + IP α (N5ss α) g := by
      rw [hG5def]
      exact IPO_add4 hE hαIoc hg4 g24 g25 g26 g27 (goodO_add g24 g25)
        (goodO_add (goodO_add g24 g25) g26)
    rw [hsum]
    linarith [abs_sum_le_fourT (IP α (N5gg g) g) (IP α (N5gs α g) g)
      (IP α (N5sg α g) g) (IP α (N5ss α) g), h17, h18, h19, hconv,
      abs_nonneg (IP α (N5gg g) g), abs_nonneg (IP α (N5gs α g) g),
      abs_nonneg (IP α (N5sg α g) g), abs_nonneg (IP α (N5ss α) g)]
  have hsplitN : IP α Nv g = IP α G1 g + IP α G2 g + IP α G3 g + IP α G4 g + IP α G5 g := by
    rw [hcongr]
    exact IPO_add5 hE hαIoc hg4
      (by rw [hG1def]; exact gG1) (by rw [hG2def]; exact gG2)
      (by rw [hG3def]; exact gG3) (by rw [hG4def]; exact gG4)
      (by rw [hG5def]; exact gG5)
      (by rw [hG1def, hG2def]; exact gG12)
      (by rw [hG1def, hG2def, hG3def]; exact gG123)
      (by rw [hG1def, hG2def, hG3def, hG4def]; exact gG1234)
  have htri : |IP α G1 g + IP α G2 g + IP α G3 g + IP α G4 g + IP α G5 g|
      ≤ |IP α G1 g| + |IP α G2 g| + |IP α G3 g| + |IP α G4 g| + |IP α G5 g| := by
    have h8 := abs_add_le (IP α G1 g + IP α G2 g + IP α G3 g + IP α G4 g) (IP α G5 g)
    have h9 := abs_sum_le_fourT (IP α G1 g) (IP α G2 g) (IP α G3 g) (IP α G4 g)
    linarith [h8, h9]
  have h20 : |IP α G1 g| + |IP α G2 g| + |IP α G3 g| + |IP α G4 g| + |IP α G5 g|
      ≤ 20 * (K₀ * (C + 1) * Pbd α X) := by
    linarith [hG1, hG2, hG3, hG4, hG5,
      abs_nonneg (IP α G1 g), abs_nonneg (IP α G2 g), abs_nonneg (IP α G3 g),
      abs_nonneg (IP α G4 g), abs_nonneg (IP α G5 g)]
  rw [hsplitN]
  linarith [htri, h20]

end Work.FTS.StrongEps.E4R3.N4C.PairingT
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.NsTerm_boundT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C.PairingT

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin
open Work.FTS.VocabO (HQo)
open Work.FTS.StrongEps.E4R3.N4C

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The `N_*` term** of the honest §8 assembly: `|IP α (N_* μ (λ μ) g) g| ≤ 24·K₀(C+1)·Pbd α X`. -/
theorem NsTerm_boundT {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {α₂ Ct K₀ C C₀ α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn} {μ : ℝ}
    (h : Work.FTS.StrongEps.E4R3.N4C.BlkCtxO IP α₂ Ct K₀ C C₀ α g Φs Φg) (hμ1 : μ ≠ -1)
    (hμ4 : |μ| ≤ 4 * C * (α + α ^ (-(1 : ℝ)) * Work.FTS.Nonlin.Xn α g
      + α ^ (-(5 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) :
    |IP α (Work.Construction.Nstar μ (Work.Construction.lamfun μ) g) g|
      ≤ 24 * (K₀ * (C + 1) * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α g)) := by
  set X := Work.FTS.Nonlin.Xn α g with hXdef
  have hE : N4ExtraH IP α₂ Ct := h.hE
  have hα : 0 < α := h.hα
  have hα1 : α ≤ 1 := h.hα1
  have hαIoc : α ∈ Set.Ioc 0 α₂ := h.hαIoc
  have hCt : 0 < Ct := h.hCt
  have hK₀Ct : Ct ≤ K₀ := h.hK₀Ct
  have hK₀pos : 0 < K₀ := lt_of_lt_of_le hCt hK₀Ct
  have hC : 0 < C := h.hC
  have hR : RowInputsTO IP α C g Φs Φg := h.hR
  have hg4 : HQo α 4 g := BlkCtxO.hg4 h
  have hkDz : GoodO α (Work.Spaces.Dz g) := hR.hkDz
  have hreg5 := BlkCtxO.hreg5 h
  have hX0 : 0 ≤ X := by rw [hXdef]; exact Work.Spaces.HkNorm_nonneg α 4 g
  have hPbd0 : 0 ≤ Work.FTS.Nonlin.Pbd α X := Pbd_nonneg hα.le hX0
  have hM0 : 0 ≤ α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2 := by
    have h1 : (0 : ℝ) ≤ α ^ (-(1 : ℝ)) * X :=
      mul_nonneg (Real.rpow_nonneg hα.le _) hX0
    have h2 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
    linarith [hα.le]
  have hμ4X : |μ| ≤ 4 * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by
    rw [hXdef]; exact hμ4
  -- ## the collapse `N_* μ (λ μ) g = μ (D_z g - g)`
  have hcollapse : Work.Construction.Nstar μ (Work.Construction.lamfun μ) g = NstarLam μ g := by
    funext z θ
    exact hR.hNs μ hμ1 z θ
  rw [hcollapse]
  have hdecomp : NstarLam μ g = (fun z θ => μ * Work.Spaces.Dz g z θ)
      + (fun z θ => (-μ) * g z θ) := by
    funext z θ
    simp only [NstarLam, Pi.add_apply]
    ring
  have hIPs : IP α (NstarLam μ g) g
      = μ * IP α (Work.Spaces.Dz g) g + (-μ) * IP α g g := by
    rw [hdecomp,
      hE.add α hαIoc (fun z θ => μ * Work.Spaces.Dz g z θ) (fun z θ => (-μ) * g z θ) g
        (goodO_const_mul μ hkDz) (goodO_const_mul (-μ) hg4) hg4,
      hE.smul α hαIoc μ (Work.Spaces.Dz g) g hkDz hg4,
      hE.smul α hαIoc (-μ) g g hg4 hg4]
  have hdz : |IP α (Work.Spaces.Dz g) g| ≤ Ct * X ^ 2 := hE.dz α hαIoc g hreg5
  have hgg : |IP α g g| ≤ Ct * X ^ 2 := by
    have h1 : |IP α g g| ≤ Ct * Work.FTS.Nonlin.Xn α g * Work.FTS.Nonlin.Xn α g :=
      hE.cs α hαIoc g g hg4 hg4
    have h2 : Ct * Work.FTS.Nonlin.Xn α g * Work.FTS.Nonlin.Xn α g = Ct * X ^ 2 := by
      rw [hXdef]; ring
    linarith [h1, h2.le, h2.ge]
  have htri : |IP α (NstarLam μ g) g| ≤ |μ| * (|IP α (Work.Spaces.Dz g) g| + |IP α g g|) := by
    rw [hIPs]
    have he : μ * IP α (Work.Spaces.Dz g) g + (-μ) * IP α g g
        = μ * (IP α (Work.Spaces.Dz g) g - IP α g g) := by ring
    rw [he, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg μ)
    simpa [sub_eq_add_neg] using abs_add_le (IP α (Work.Spaces.Dz g) g) (-(IP α g g))
  -- ## the `μ`-bound, turned into a `Pbd`-bound
  have hmid : |μ| * (|IP α (Work.Spaces.Dz g) g| + |IP α g g|)
      ≤ 8 * K₀ * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2 := by
    have h1 : |IP α (Work.Spaces.Dz g) g| + |IP α g g| ≤ 2 * Ct * X ^ 2 := by
      have h := add_le_add hdz hgg
      linarith [h]
    have h2 : |μ| * (|IP α (Work.Spaces.Dz g) g| + |IP α g g|)
        ≤ (4 * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2))
          * (2 * Ct * X ^ 2) :=
      mul_le_mul hμ4X h1 (by positivity) (by positivity)
    have h3 : (4 * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2))
          * (2 * Ct * X ^ 2)
        ≤ 8 * K₀ * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2 := by
      have h8 : (0 : ℝ) ≤ 4 * C
          * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2 :=
        mul_nonneg (mul_nonneg (by positivity) hM0) (by positivity)
      nlinarith [hK₀Ct, h8, hC.le]
    linarith [h2, h3]
  have hm1 : α * X ^ 2 ≤ Work.FTS.Nonlin.Pbd α X := by
    have hαle_sqrt : α ≤ Real.sqrt α := by
      have hle1 : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
      have hsq : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
      nlinarith [Real.sqrt_nonneg α, hle1, hsq]
    exact le_trans (mul_le_mul_of_nonneg_right hαle_sqrt (by positivity))
      (sqrt_mul_sq_le_Pbd hα hX0)
  have hm2 : α ^ (-(1 : ℝ)) * X ^ 3 ≤ Work.FTS.Nonlin.Pbd α X :=
    rpow_neg_one_mul_cube_le_Pbd hα hα1 hX0
  have hm3 : α ^ (-(5 / 2 : ℝ)) * X ^ 4 ≤ Work.FTS.Nonlin.Pbd α X := by
    rw [Work.FTS.Nonlin.Pbd]
    have h1 : (0 : ℝ) ≤ α ^ 2 * X := mul_nonneg (by positivity) hX0
    have h2 : (0 : ℝ) ≤ Real.sqrt α * X ^ 2 := mul_nonneg (Real.sqrt_nonneg α) (by positivity)
    have h3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 3 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
    linarith
  have hfin : 8 * K₀ * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2
      ≤ 24 * (K₀ * (C + 1) * Work.FTS.Nonlin.Pbd α X) := by
    have hexp : 8 * K₀ * C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) * X ^ 2
        = 8 * K₀ * C * (α * X ^ 2 + α ^ (-(1 : ℝ)) * X ^ 3
            + α ^ (-(5 / 2 : ℝ)) * X ^ 4) := by ring
    have hsum : α * X ^ 2 + α ^ (-(1 : ℝ)) * X ^ 3 + α ^ (-(5 / 2 : ℝ)) * X ^ 4
        ≤ 3 * Work.FTS.Nonlin.Pbd α X := by linarith [hm1, hm2, hm3]
    have hsum' : 8 * K₀ * C * (α * X ^ 2 + α ^ (-(1 : ℝ)) * X ^ 3
          + α ^ (-(5 / 2 : ℝ)) * X ^ 4) ≤ 8 * K₀ * C * (3 * Work.FTS.Nonlin.Pbd α X) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have h3P : 8 * K₀ * C * (3 * Work.FTS.Nonlin.Pbd α X)
        ≤ 24 * (K₀ * (C + 1) * Work.FTS.Nonlin.Pbd α X) := by
      have h1 : 8 * K₀ * C * (3 * Work.FTS.Nonlin.Pbd α X)
          = 24 * K₀ * C * Work.FTS.Nonlin.Pbd α X := by ring
      have h2 : 24 * (K₀ * (C + 1) * Work.FTS.Nonlin.Pbd α X)
          = 24 * K₀ * C * Work.FTS.Nonlin.Pbd α X + 24 * K₀ * Work.FTS.Nonlin.Pbd α X := by
        ring
      have h3 : (0 : ℝ) ≤ 24 * K₀ * Work.FTS.Nonlin.Pbd α X := by positivity
      linarith [h1.le, h1.ge, h2.le, h2.ge, h3]
    linarith [hexp.le, hexp.ge, hsum', h3P]
  exact le_trans htri (le_trans hmid hfin)

end Work.FTS.StrongEps.E4R3.N4C.PairingT
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.NMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsZero.ClassCHk

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)

/-!
# `NMem` : the `N`-block of the scheme's right-hand side is `ℋ⁴`-honest on the class `C`

The target is `Work.Spaces.HkMem α 4 (N α (Ftot α w) (Φs + Φg))` for `w` of the linear class
`ClassC α w`, the elliptic package `EllPkgGo α Ce w Φg` and the star package
`StarPkgo2 α Cs Φs`.

**Route.**  `Work.FTS.NonlinRows.Rl1.splitOpen` splits `N α (F_* + w) (Φ_s + Φ_g)` on the open
quadrant `Qd` into the twenty pieces `N_i^{**}(α, w, Φs, Φg)` (`i = 1..5`, the four index
combinations `gg`, `gs`, `sg`, `ss` of `Work.FTS.Nonlin.Defs`), each of which is `ℋ⁴`-honest and
`C⁴` on the open quadrant (`Work.FTS.OpenPkg.Good`); the twenty `Good`-facts — proved in the
sibling modules `NMemAux` (`N₁`, `N₂`) and `NMemAux2` (`N₃`, `N₄`, `N₅`) — are added with
`Good.add` (through the finite-sum form `NMemAux.good_sum_range`) and the sum is transferred back
to `N` with `Good.of_eqOn_Qd`.

The pieces split into families, each handled by the corresponding product rule of `OpenPkg`:

* `gg` (the perturbation coefficient against `w`, `D_θ w`, `D_z w`): the coefficients
  `Rop (PhiTg α w Φg)`, `Uop (PhiTg α w Φg)/s2`, `Vop (PhiTg α w Φg)` are `HQo α 4`
  (fields of `hell`), and `w`, `D_θ w`, `D_z w` are `HQo α 4` (class + one-level descent);
  use `OpenPkg.prod_field`.
* `gs` / `sg` / `ss` against the fixed atoms `F_*`, `D_θF_*`, `D_zF_*`, `FK(F_*)`: the fixed
  atoms are priced by the `𝒲^{4,∞}`-norm (`FstarPkg.{Fstar_W, DthFstar_W, DzFstar_W,
  hKerConstWlInf}`), so the products are handled by `OpenPkg.wprod_field_winf` with the star
  coefficients written as `((z+1)/z)·coefficient` times `(z/(1+z))·atom` — the factor
  `z/(1+z)` is removed by `NRow10aux.mul_phi_Hk`, the `(z+1)/z`-weighted star coefficients are
  the `WlInfMem` fields `RW`, `UszW`, `VzW` of `StarPkgo2`.
* the pure-star pieces `N_i^{ss}` are the `L3Rhs` "priced rows" `N1ssPriced`, `N2ssPriced`,
  `N3ssPriced`, `N4ssPriced`, `N5ssPriced`.
* the `FK`-family: `FK(F_*) = 2α·hKer` (`FstarPkg.FK_Fstar`, `RNP.hKerConstWlInf`), the
  perturbation moment `FK(w)` is `HQo α 4` (`OpenPkg.fkH_field`, smoothness from
  `ClassC.fsm` through `FK F = 3 F_*(F)`), and the angular profile `-sin²θ` is multiplied in
  with `OpenPkg.angmul_field` (`RNP24.angProfile_sinSq`).
-/

/-- The twenty pieces of the open-quadrant split of `N`, indexed by `ℕ`. -/
private noncomputable def pieces (α : ℝ) (w Φs Φg : Fn) : ℕ → Fn
  | 0 => Work.FTS.Nonlin.N1gg α w Φg
  | 1 => Work.FTS.Nonlin.N1gs α w Φg
  | 2 => Work.FTS.Nonlin.N1sg α Φs w
  | 3 => Work.FTS.Nonlin.N1ss α Φs
  | 4 => Work.FTS.Nonlin.N2gg α w Φg
  | 5 => Work.FTS.Nonlin.N2gs α w Φg
  | 6 => Work.FTS.Nonlin.N2sg α Φs w
  | 7 => Work.FTS.Nonlin.N2ss α Φs
  | 8 => Work.FTS.Nonlin.N3gg α w Φg
  | 9 => Work.FTS.Nonlin.N3gs α w Φg
  | 10 => Work.FTS.Nonlin.N3sg α Φs w
  | 11 => Work.FTS.Nonlin.N3ss α Φs
  | 12 => Work.FTS.Nonlin.N4gg α w
  | 13 => Work.FTS.Nonlin.N4gs α w
  | 14 => Work.FTS.Nonlin.N4sg α w
  | 15 => Work.FTS.Nonlin.N4ss α
  | 16 => Work.FTS.Nonlin.N5gg w
  | 17 => Work.FTS.Nonlin.N5gs α w
  | 18 => Work.FTS.Nonlin.N5sg α w
  | _ => Work.FTS.Nonlin.N5ss α

/-- Every one of the twenty pieces is `Good` (`C⁴` on the open quadrant and `ℋ⁴`-honest). -/
private theorem good_pieces {α Ce Cs : ℝ} {w Φs Φg : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∀ i ∈ Finset.range 20, Work.FTS.OpenPkg.Good α (pieces α w Φs Φg i) := by
  intro i hi
  have hi20 : i < 20 := Finset.mem_range.mp hi
  interval_cases i <;>
    simp only [pieces] <;>
    first
      | exact good_N1gg hα hα1 hw hell
      | exact good_N1gs hα hα1 hw hell
      | exact good_N1sg hα hα1 hw hstar
      | exact good_N1ss hα hα1 hstar
      | exact good_N2gg hα hα1 hw hell
      | exact good_N2gs hα hα1 hell
      | exact good_N2sg hα hα1 hw hstar
      | exact good_N2ss hα hα1 hstar
      | exact good_N3gg hα hα1 hw hell
      | exact good_N3gs hα hα1 hell
      | exact good_N3sg hα hα1 hw hstar
      | exact good_N3ss hα hα1 hstar
      | exact good_N4gg hα hα1 hw
      | exact good_N4gs hα hα1 hw
      | exact good_N4sg hα hα1 hw
      | exact good_N4ss hα hα1
      | exact good_N5gg hα hα1 hw
      | exact good_N5gs hα hα1 hw
      | exact good_N5sg hα hα1 hw
      | exact good_N5ss hα hα1

theorem NMem {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Φs w Φg : Work.FTS.Galerkin.Fn} (hw : Work.FTS.ClassC.ClassC α w)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.Spaces.HkMem α 4 (Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + Φg z θ)) := by
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  -- the moment additivity for the profile `F_* + w`
  have hL : ∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α w) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 w z :=
    fun z hz => Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar hα hα1 hw.reg hmem4 z hz
  have hFK : ∀ z : ℝ, 0 < z → Work.Construction.FK (Work.Construction.Ftot α w) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK w z :=
    fun z hz =>
      Work.FTS.GalFields.RHS.FK_add_of_slices
        (a := Work.Construction.Fstar α) (b := w) (ne_of_gt hz)
        (Work.Stability.integrableOn_slice_Fstar α hα z)
        (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hw.reg hmem4 hz)
  -- `L₁₂(w)` is differentiable in `z` on `(0,∞)`
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  have hL12 : ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (fun z' => Work.Construction.L12 w z') z := by
    intro z hz
    have hθ : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact (hL12sm.hasDerivAt_slice hθ hz).differentiableAt
  refine (Work.FTS.OpenPkg.Good.of_eqOn_Qd
    (good_sum_range 20 (pieces α w Φs Φg)
      (good_pieces hα hα1 hw hell hstar)) ?_).hk
  intro z θ hq
  have hsp := Work.FTS.NonlinRows.Rl1.splitOpen hα hα1 hw.reg hstar.smooth hell.smooth
    hL hFK hL12 z θ hq
  rw [hsp]
  simp only [Finset.sum_range_succ, pieces, add_assoc]
  ring

end Work.FTS.StrongEps.EpsZero.ClassCHk
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.vop_pert_pth_bd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.vop_pert_pth_bd` — the `∂_θ`-slot of `𝒱(Φ̃)` is `O(Ce α^{-1/2} C₀α²)`

For the perturbation residual `Φ̃(τ) = PhiTil (pExp α) (g(τ)) (E (g(τ)))` of the dynamic
modulation, the `∂_θ`-slot of its transport coefficient `𝒱(Φ̃) = ∂_θΦ̃ - tan θ · Φ̃` is
bounded by the *product of the two constants already present in the hypotheses*:

`|∂_θ 𝒱(Φ̃) z θ| ≤ max Ce 0 · α^{-1/2} · (max C₀ 0 · α²)`.

This is precisely the `Vth` field of the elliptic package `EllPkgGo` — which bounds the *flat
angular coefficient norm* `CoefTh 1 (𝒱(Φ̃))` by `Ce · α^{-1/2} · Xn α g(τ)` for a class-`C`
datum — combined with the uniform `ℋ⁴`-smallness `Xn α (g(τ)) ≤ C₀α²` of `DynOK`.

## Route

1. `CoefTh l f = ∑_{b,i} [b+i ≤ l] supAbsO (D_z^bD_θ^i ∂_θf)` is a sum of nonnegative terms,
   so each of its summands is dominated by it (`TransportS.supAbsO_le_coefTh`); the
   `(b,i) = (0,0)` summand is `supAbsO (pth (𝒱(Φ̃)))`.
2. Inside the open quadrant, `|pth (𝒱(Φ̃)) z θ| ≤ supAbsO (pth (𝒱(Φ̃)))`
   (the `CoefThMem 1` half of `Vth` supplies the boundedness making `supAbsO` a genuine
   supremum rather than Lean's junk value).
3. Hence, for the class-`C` approximants `gn` of `LimApprox`,
   `|pth (𝒱(Φ̃_n)) z θ| ≤ CoefTh 1 (𝒱(Φ̃_n)) ≤ Ce · α^{-1/2} · Xn α (slice (gn n) τ)
   ≤ max Ce 0 α^{-1/2} (max C₀ 0 α²)`: the last step is the elementary case analysis on the
   signs of `Ce` and `C₀` (if `Ce ≤ 0` the middle term is `≤ 0`; if `C₀ ≤ 0` then `Xn = 0`
   as `Xn ≥ 0`; the remaining case is monotonicity).
4. The limit is taken with `le_of_tendsto'` and the jet convergence of `𝒱(Φ̃_n)` along the
   class-`C` approximants (`Sys.pth_vop_pert_tendsto`).
-/

namespace Work.FTS_RegExport.RXT.Sys

open Set Filter

set_option autoImplicit false

theorem vop_pert_pth_bd {α Ce C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pth (Work.Construction.Vop (fun z θ => Work.Construction.PhiTil
          (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice g τ)
          (E (Work.FTS.Galerkin.slice g τ)) z θ)) z θ|
        ≤ max Ce 0 * (Work.FTS.Regularity.pExp α) ^ (-(1 / 2 : ℝ))
            * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
  intro S hS τ hτ z θ hz hθ hθ2
  obtain ⟨gn, B, L, hApprox, _hLip, hJet, _hμ⟩ := hOK.2 S hS
  -- the jet convergence of the `∂_θ`-slot of `𝒱(Φ̃)` along the class-`C` approximants
  have hconv : Filter.Tendsto
      (fun n => |Work.Spaces.pth (Work.Construction.Vop (fun z θ => Work.Construction.PhiTil
          (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
          (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)) z θ|)
      Filter.atTop
      (nhds |Work.Spaces.pth (Work.Construction.Vop (fun z θ => Work.Construction.PhiTil
          (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice g τ)
          (E (Work.FTS.Galerkin.slice g τ)) z θ)) z θ|) := by
    exact (Work.FTS_RegExport.RXT.Sys.pth_vop_pert_tendsto hα hα13 hEL3 hOK hS hτ
      hApprox hJet z θ hz hθ hθ2).abs
  refine le_of_tendsto' hconv (fun n => ?_)
  obtain ⟨hCn, hXn, -⟩ := hApprox n τ hτ
  obtain ⟨hGo, _⟩ := hEll _ hCn
  -- ## the `CoefTh` route
  have hstep1 : |Work.Spaces.pth (Work.Construction.Vop (fun z θ => Work.Construction.PhiTil
        (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)) z θ|
      ≤ Work.FTS.H2.supAbsO (Work.Spaces.pth (Work.Construction.Vop (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice (gn n) τ)
            (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ))) := by
    obtain ⟨K, hK⟩ := hGo.Vth.1 0 0 (by norm_num)
    refine le_csSup ⟨K, ?_⟩ ⟨z, hz, θ, hθ, hθ2, rfl⟩
    rintro y ⟨z', hz', θ', hθ', hθ2', rfl⟩
    simpa [Work.Spaces.mixed] using hK z' θ' hz' hθ' hθ2'
  have hstep2 : Work.FTS.H2.supAbsO (Work.Spaces.pth (Work.Construction.Vop (fun z θ =>
        Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice (gn n) τ)
          (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)))
      ≤ Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (fun z θ =>
        Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice (gn n) τ)
          (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)) := by
    have h := Work.FTS.TransportS.supAbsO_le_coefTh (l := 1)
      (f := Work.Construction.Vop (fun z θ => Work.Construction.PhiTil
        (Work.FTS.Regularity.pExp α) (Work.FTS.Galerkin.slice (gn n) τ)
        (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ)) (b := 0) (i := 0) (by norm_num)
    simpa [Work.Spaces.mixed] using h
  -- ## the constant
  have hstep3 : Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (fun z θ =>
        Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice (gn n) τ)
          (E (Work.FTS.Galerkin.slice (gn n) τ)) z θ))
      ≤ max Ce 0 * (Work.FTS.Regularity.pExp α) ^ (-(1 / 2 : ℝ))
          * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
    have hαp : 0 < (Work.FTS.Regularity.pExp α) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_pos_of_pos (Work.FTS.Regularity.pExp_pos hα) _
    have hq : 0 ≤ (Work.FTS.Regularity.pExp α) ^ 2 := sq_nonneg _
    have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ) := Work.Spaces.HkNorm_nonneg _ _ _
    have hXnB : Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice (gn n) τ)
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 :=
      le_trans hXn (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) hq)
    have h0 : 0 ≤ max Ce 0 * (Work.FTS.Regularity.pExp α) ^ (-(1 / 2 : ℝ))
        * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
      mul_nonneg (mul_nonneg (le_max_right Ce 0) hαp.le)
        (mul_nonneg (le_max_right C₀ 0) hq)
    refine le_trans hGo.Vth.2 ?_
    rcases le_or_gt Ce 0 with hCe | hCe
    · have hneg : Ce * (Work.FTS.Regularity.pExp α) ^ (-(1 / 2 : ℝ))
          * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice (gn n) τ) ≤ 0 := by
        rw [mul_assoc]
        exact mul_nonpos_of_nonpos_of_nonneg hCe (mul_nonneg hαp.le hXn0)
      linarith
    · rw [max_eq_left hCe.le]
      exact mul_le_mul_of_nonneg_left hXnB (mul_nonneg hCe.le hαp.le)
  exact le_trans (le_trans hstep1 hstep2) hstep3

end Work.FTS_RegExport.RXT.Sys
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.cs7_rop_split =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.THL

open scoped Real Topology
open Set Filter

open Work.FTS.Galerkin (Fn Fam slice)

/-!
# `cs7_rop_split` — the additive split of the `ℛ`-slot of the modulated residual

On the open quadrant the modulated residual `Φ̃_τ = v2_PhiT α Φs E g τ` splits as the star residual
`Φ̃_* = PhiTs (pExp α) Φs` plus the perturbation residual `PhiTil (slice g τ) (E (slice g τ))`
(`v2_phiTil_split`), and `Rop` is additive on `C¹` pieces (`v2_rop_add_at`).  This is the
`Rop`-half of the clean split; it is what `cs7_theta_holder` (A6) consumes. -/

theorem cs7_rop_split {α C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) z θ
        = Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.FTS.VocabO2.PhiTs (Work.FTS.Regularity.pExp α) Φs) z θ
          + Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ := by
  intro τ hτ z θ hz hθ hθ2
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the star half is `C^∞` on the open quadrant, hence `C¹`
  have hStar3 : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiStar α Φs))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).1.of_le
      (by simp [Work.Stability.smoothOrder])
  have hStar1 : ContDiffOn ℝ 1 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiStar α Φs))
      Work.FTS.EllipticEst.Q0 := hStar3.of_le (by norm_num)
  -- the Θ-part of the modulated stream function
  have hTheta3 : ContDiffOn ℝ 3 (Function.uncurry
      (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ))) Work.FTS.EllipticEst.Q0 := by
    refine Work.FTS_RegExport.RXT.velPert_contDiffOn_Theta (α := Work.FTS.Regularity.pExp α) ?_
    refine Work.FTS_RegExport.RXT.contDiffOn_three_L12 ?_
    obtain ⟨C, _hC0, hCb⟩ := Work.FTS_RegExport.RXT.Ftau_bounds
      (Φs := Φs) (E := E) hα hα13 hOK τ hτ
    exact Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta (φ := Work.Spaces.K)
      Work.FTS_RegExport.RXT.v2_continuousOn_K_Iθ
      (Work.FTS_RegExport.RXT.contDiffOn_Ftau_Q0 (Φs := Φs) (E := E) hα hα13 hOK τ hτ)
      (fun z₁ θ₁ hz₁ hθ₁ hθ₁2 => ⟨(hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).1,
        (hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).2.1, (hCb z₁ θ₁ hz₁ hθ₁ hθ₁2).2.2⟩)
  have hFull3 : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS_RegExport.RXT.contDiffOn_slice_PhiR_Q0 (α := α) (C₀ := C₀) (Cs := Cs)
      hEL3 hStar hOK τ hτ).sub hTheta3
  -- the perturbation residual, as the difference of the two
  have hPert3 : ContDiffOn ℝ 3 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ))
      Work.FTS.EllipticEst.Q0 := by
    refine (hFull3.sub hStar3).congr ?_
    intro p hp
    obtain ⟨z₁, θ₁⟩ := p
    simp only [Function.uncurry]
    linarith [Work.FTS_RegExport.RXT.v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ z₁ θ₁ hp]
  have hPert1 : ContDiffOn ℝ 1 (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ))
      Work.FTS.EllipticEst.Q0 := hPert3.of_le (by norm_num)
  -- the pointwise split, as an `AgreeOnQ`
  have hsplitFun : Work.FTS_RegExport.RXR5.AgreeOnQ (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
      (Work.FTS_RegExport.RXT.v2_PhiStar α Φs + Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) :=
    fun z₁ θ₁ hz₁ hθ₁ hθ₁2 => Work.FTS_RegExport.RXT.v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ
      z₁ θ₁ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz₁, hθ₁, hθ₁2⟩)
  rw [Work.FTS_RegExport.RXR5.Rop_congr_of_agreeOnQ
    (α := Work.FTS.Regularity.pExp α) (h := hsplitFun) hz hθ hθ2]
  exact Work.FTS_RegExport.RXT.v2_rop_add_at hStar1 hPert1 ⟨hz, hθ, hθ2⟩

end Work.FTS_RegExport.THL
end
