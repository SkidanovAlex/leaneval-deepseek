import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_MuLipC.Defs
import Submission.Work.FTS_MuLipC.LinQuad
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.LocData.L12_add_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS_MuLipC.Poly0

/-- **Additivity of `L₁₂` on the open class.**  For two data that are `C^∞` on the open quadrant
and honest in `ℋ⁴`, the integral operator `L₁₂` is additive at every `z ≥ 0`.  This is
`Work.FTS.LocData.L12_add_mul` with its four integrability inputs supplied by the `ℋ⁴`-honesty
(`Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem`,
`Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem`). -/
theorem L12_add_of_SmoothOpen_HkMem {α : ℝ} {a b : Work.FTS.Galerkin.Fn}
    (ha : Work.FTS.EllipticEst.SmoothOpen a) (hb : Work.FTS.EllipticEst.SmoothOpen b)
    (hma : Work.Spaces.HkMem α 4 a) (hmb : Work.Spaces.HkMem α 4 b) :
    ∀ z : ℝ, 0 ≤ z →
      Work.Construction.L12 (fun z θ => a z θ + b z θ) z
        = Work.Construction.L12 a z + Work.Construction.L12 b z := by
  intro z hz
  refine (Work.FTS.LocData.L12_add_mul (c := 0) (a := a) (b := b) (z := z) ?_ ?_ ?_ ?_).1
  · exact fun s hs => Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem ha hma
      (lt_of_le_of_lt hz hs)
  · exact fun s hs => Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hb hmb
      (lt_of_le_of_lt hz hs)
  · exact (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem ha hma).mono_set
      (Set.Ioi_subset_Ioi hz)
  · exact (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hb hmb).mono_set
      (Set.Ioi_subset_Ioi hz)

/-- **The `N₀` polynomial structure on the class `C`**: the profile-level additivity
`L₁₂(F_*) + L₁₂(g) = L₁₂(F_*+g)` of `L₁₂` (all that `PhiTil`/`FK` splitting needs), and the two
polarization identities of the quadratic block (`Lin0 α (u+d) = Lin0 α u + Lin0 α d` and
`Quad0 α (u+d) = Quad0 α u + Bil0 α u d + Bil0 α d u + Quad0 α d`), whose definitions and the
companion identity `sn0_eq_sum` are in `Submission/Work/FTS_MuLipC/LinQuad.lean`.  The
hypotheses on `u`, `d` are stated at the class `C` for convenience; only `SmoothOpen` +
`HkMem α 4` are used.  For the first conjunct the integrability inputs of `L₁₂`-additivity
(`Work.FTS.LocData.L12_add_mul`) are those of `Work.FTS.Nonlinear.Pieces.L12FK_add_ge0`
(`Work.Stability.integrableOn_slice_Fstar`,
`Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem`,
`Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem`, and
`Work.FTS.Nonlinear.FstarPkg`/`Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn`
for the `F_*` density); for the last two, `Work.FTS.GalFields.RHS.Sharp.L12_sub_ge0`
(a := `u+d`, b := `d`, d := `u`) and the `pth`/`Dz` additivity
`Work.FTS.NonlinRows.Rl1.openSlice_pth_add` / `openSlice_pz_add` +
`Work.FTS.Nonlinear.Pieces.Dz_add_of_diff` do the job. -/
theorem n0_poly {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {u d : Work.FTS.Galerkin.Fn}
    (hu : Work.FTS.ClassC.ClassC α u) (hd : Work.FTS.ClassC.ClassC α d) :
    (∀ z : ℝ, 0 ≤ z → Work.Construction.L12 (Work.Construction.Ftot α u) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 u z) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS_MuLipC.Lin0 α (fun z' θ' => u z' θ' + d z' θ') z θ
        = (Work.FTS_MuLipC.Lin0 α u + Work.FTS_MuLipC.Lin0 α d) z θ) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS_MuLipC.Quad0 α (fun z' θ' => u z' θ' + d z' θ') z θ
        = (Work.FTS_MuLipC.Quad0 α u + Work.FTS_MuLipC.Bil0 α u d
            + Work.FTS_MuLipC.Bil0 α d u + Work.FTS_MuLipC.Quad0 α d) z θ) := by
  have huS : Work.FTS.EllipticEst.SmoothOpen u := hu.reg
  have hdS : Work.FTS.EllipticEst.SmoothOpen d := hd.reg
  have hu4 : Work.Spaces.HkMem α 4 u := Work.FTS.ClassC.classC_hkMem_four hu
  have hd4 : Work.Spaces.HkMem α 4 d := Work.FTS.ClassC.classC_hkMem_four hd
  refine ⟨?_, ?_, ?_⟩
  · -- the `L₁₂`-additivity over `F_* + u`
    intro z hz
    exact (Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add hα hα1 huS hu4).1 z hz
  · -- `Lin0` is linear in the profile
    intro z θ hz hθ0 hθ1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
    have hL := L12_add_of_SmoothOpen_HkMem huS hdS hu4 hd4 z hz.le
    have hDz := Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
      (Work.FTS.NonlinRows.Rl1.openSlice_pz_add huS hdS hz hθ)
    simp only [Work.FTS_MuLipC.Lin0, Pi.add_apply]
    rw [hL, hDz]
    ring
  · -- the polarization identity of the quadratic block
    intro z θ hz hθ0 hθ1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
    have hL := L12_add_of_SmoothOpen_HkMem huS hdS hu4 hd4 z hz.le
    have hp := Work.FTS.NonlinRows.Rl1.openSlice_pth_add huS hdS hz hθ
    have hDz := Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
      (Work.FTS.NonlinRows.Rl1.openSlice_pz_add huS hdS hz hθ)
    simp only [Work.FTS_MuLipC.Quad0, Work.FTS_MuLipC.Bil0, Pi.add_apply]
    rw [hL, hp, hDz]
    ring

end Work.FTS_MuLipC.Poly0
