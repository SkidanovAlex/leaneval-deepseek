/-
# `Work.FTS.EllSol.PkgK5.tracesK5`

The angular endpoint traces of the radial iterates of the straightened unknown
`X := ellShift α g Φg`, in the *repaired* honesty class: `EllWeakPos α k F X`, one extra level
`HkMem α (k+3) (z²∂_z²X)` of `A`-honesty and one extra level `HkMem α (k+2) F` of source honesty
give the vanishing of `θ ↦ D_z^j X(z,θ)` at both angular endpoints for every `j ≤ k+1` and every
`z > 0`.

## Route

Write `A := z²∂_z²X`, `F := orthSource g`, `u_j := θ ↦ D_z^j X(z,·)`.  For every `j ≤ k+1`:

* `u_j` is `C²` on `(0,π/2)` (`SmoothOpen X`);
* `(u_j'')²·sEta ∈ L¹` (`EllWeakPos.memB` for `j ≤ k`, the diagonal slot `memZPth2` for `j = k+1`);
* `∫ u_j² < ∞` (from boundedness: `abs_le_of_sq_mul_sEta`);
* `(Lzero1 u_j)²·sEta ∈ L¹`: the slice equation
  `Lzero1 u_j = D_z^j F + α²D_z^jA + α(5+α)D_z^{j+1}X` plus the three slot energies
  (`HkMem α (k+2) F`, `HkMem α (k+3) A`, and the recursion `D_z^{b+2}X = D_z^bA + D_z^{b+1}X`
  down to `Ϝ_1 = ∫(z∂_zX)²sEta`, which is `ws_pz_energy_integrable`);
* the moment `∫ Lzero1 u_j·sinθcos²θ = 0`: integrating the slice equation against `sinθcos²θ`
  turns it into `N_j + α²(M_{j+2} - M_{j+1}) + α(5+α)M_{j+1}`, where
  `M_i = F_*(D_z^iX)`, `N_i = F_*(D_z^iF)`; the source moments `N_i` (`i ≤ k+1`) come from the
  radial moment tower `Cert.radIter_bmom_hasDerivAt` applied to `HkMem α (k+2) F`, and the
  solution moments `M_i` (`i ≤ k+3`) are the content of the delegated
  `Work.FTS.EllSol.PkgK5.Fstar_DzIter_le_honest`.

Then `remov.wsSliceLeft` and `remov.sliceTendstoRight_fts` give the two one-sided limits.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi
import Submission.Work.FTS.EllipticEst.Cert.radIter_Bmom_ae
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.Cores.Repair.DzShift
import Submission.Work.FTS.EllSol.PkgK5.tracesK5Aux
import Submission.Work.FTS.EllSol.PkgK5.tracesK5Aux2
import Submission.Work.FTS.EllSol.PkgK5.Fstar_DzIter_le_honest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option maxHeartbeats 3200000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sEta" => Work.FTS.EllipticEst.sEta
local notation "sg" => Work.Elliptic.sinCos2
local notation "Lzero1" => Work.FTS.EllipticEst.Lzero1

/-! ## 7. The endpoint traces, conditionally on the two moment towers -/

theorem traces_of_honest {α : ℝ} {k : ℕ} {F X : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F X)
    (hAh : Work.Spaces.HkMem α (k + 3)
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ))
    (hFmem : Work.Spaces.HkMem α (k + 2) F)
    (hmom : ∀ i : ℕ, i ≤ k + 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter i X) z = 0)
    (hmomF : ∀ i : ℕ, i ≤ k + 1 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter i F) z = 0) :
    ∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j X z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j X z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hXsm : Work.FTS.EllipticEst.SmoothOpen X :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  intro j hj z hz
  have hsm : ContDiffOn ℝ 2 (fun θ : ℝ => Work.Spaces.DzIter j X z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.remov.ws_contDiffOn_slice (hXsm.DzIter j) hz
  have h2 := secondSlot_dzIter (α := α) (k := k) (F := F) (X := X) hk h j hj hz
  have hu : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter j X z θ) ^ 2) Iθ := by
    obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.remov.abs_le_of_sq_mul_sEta hsm h2
    refine MeasureTheory.Integrable.mono'
      (Work.FTS.EllipticEst.remov.ws_sEta_integrableOn.const_mul (C ^ 2))
      ((aesm_slice_dzIter hXsm j hz).pow 2) ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hb' : |Work.Spaces.DzIter j X z θ| ≤ C := (hC θ hθ).2
    have hXs : Work.Spaces.DzIter j X z θ ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb' 2
    have h1 : 1 ≤ sEta θ := Work.FTS.EllipticEst.remov.ws_one_le_sEta hθ
    calc Work.Spaces.DzIter j X z θ ^ 2 ≤ C ^ 2 := hXs
      _ ≤ C ^ 2 * sEta θ := le_mul_of_one_le_right (sq_nonneg C) h1
  have hL := lzero1_energy_dzIter hk h hAh hFmem j hj hz
  have hmoment := lzero1_moment_dzIter hk h hAh hFmem hmom hmomF j hj hz
  exact ⟨Work.FTS.EllipticEst.remov.wsSliceLeft hsm h2 hL hmoment,
    Work.FTS.EllipticEst.remov.sliceTendstoRight_fts hsm h2 hL hu⟩

/-! ## 8. The moment tower of the straightened unknown (delegated)

The vanishing of `M_i = F_*(D_z^iX)`, `i ≤ k+3`, is proved by a colleague in
`Submission/Work/FTS/EllSol/PkgK5/Fstar_DzIter_le_honest.lean` and imported here. -/

/-! ## 9. The target -/

theorem tracesK5 : ∀ k : ℕ, 2 ≤ k →
    ∀ (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.StrongGlobal.IsBslSolPos α g Φg →
      Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α k (Work.Elliptic.orthSource g)
        (Work.FTS.EllSol.ellShift α g Φg) →
      Work.Spaces.HkMem α (k + 3)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ) →
      Work.Spaces.HkMem α (k + 2) (Work.Elliptic.orthSource g) →
      ∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  intro k hk α g Φg hα hα4 hC hsol hsmo hweak hAh hFmem
  refine traces_of_honest (F := Work.Elliptic.orthSource g)
    (X := Work.FTS.EllSol.ellShift α g Φg) hk hweak hAh hFmem ?_ ?_
  · exact Fstar_DzIter_le_honest hk hweak hAh
  · exact fstar_dzIter_source_eq_zero (Work.FTS.EllipticEst.remov.ws_smoothOpen_F hweak)
      hFmem hweak.orthF

end Work.FTS.EllSol.PkgK5
