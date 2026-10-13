import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.NMemAux
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.NMemAux2
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.Stability.L12Add

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
