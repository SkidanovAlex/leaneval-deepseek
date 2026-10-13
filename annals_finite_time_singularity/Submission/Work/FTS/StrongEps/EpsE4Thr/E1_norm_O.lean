/-
# `EpsE4Thr/E1_norm_O` — the `ℋⁿ`-norm bound for the transfer defect `E1` on the **open** class

`E1 α f = (D_θΓ)·radA α f` is the defect of the transfer identity
`D_θ(𝓛_Γ^T f) = 𝓛̂(D_θf) + E1 α f` (`Transfer/Profiles.lean`), and this file proves the
quantitative statement needed by the induction of `Transfer/stepT` on the *open* coercivity
class `CoerAdmO` (the class of the route's projected slices, cf. `EpsE4Thr/OpenClass.lean`):

  `∃ κ ≥ 0, ∀ α ∈ (0,1], ∀ n ≤ 3, ∀ f ∈ CoerAdmO α,
     |E1 α f|_n ≤ α·κ·(|f|_n + |D_θ f|_n)`.

It is the `SmoothOpen`-class twin of `Work.FTS.CoercivityFix.Transfer.E1_norm` (which needs the
stronger, on the route unreachable, `CoerAdm` = `SmoothQuad` class), assembled in `E1Open/`:

* `E1Open.Qang_sq_w_sq_le_HkSq_O` — the level-`n` angular-moment bound in the open class;
* `E1Open.L12f_slot_le_O_of` — the level-`n` weighted slot bound for `L₁₂ f`, obtained from the
  open `L₁₂`-bundle (`D_z^{k+1} L₁₂ f = -Qang f k`, Hardy) and the angular-moment bound;
* `E1Open.radA_slotSum_le_O` — the level-`n` radial bound for `radA α f`, from the `L₁₂`-slot
  bound, the pointwise Leibniz/majorant expansion `RadBound.radA_iter_sq_le` and the `C₀`-bound
  `C0_sq_le_Ef_O`;
* `E1Open.E1_hkSq_le_O_of` / `E1Open.E1_norm_O_of` — the separation of variables
  (`E1Norm.E1_angRad_le`, class-free) and the square-root assembly.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Transfer.E1_norm
import Submission.Work.FTS.StrongEps.EpsE4Thr.E1Open.Qang_sq_w_sq_le_HkSq_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.E1Open.L12f_slot_le_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.E1Open.radA_slotSum_le_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.E1Open.Assembly_O

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The level-`n` weighted slot bound for `L₁₂ f` in the open class: the `E1Open` version, with
the angular-moment input supplied by `E1Open.Qang_sq_w_sq_le_HkSq_O`. -/
theorem L12f_slot_le_O :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ f : Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Construction.L12 f 0 = 0 → ∀ n : ℕ, n ≤ 3 →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α n f :=
  E1Open.L12f_slot_le_O_of (CQ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
    (MeasureTheory.integral_nonneg (fun θ => sq_nonneg _))
    (fun β m g hβ hβ1 hso hm i hi =>
      E1Open.Qang_sq_w_sq_le_HkSq_O m β g hβ hβ1 hso hm i hi)

/-- The level-`n` radial slot bound for `radA α f` on the open class. -/
theorem radA_slotSum_le :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f → ∀ n : ℕ, n ≤ 3 →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ Cs * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) :=
  E1Open.radA_slotSum_le_O L12f_slot_le_O

/-- The squared `ℋⁿ`-bound for the transfer defect in the open class. -/
theorem E1_hkSq_le_O :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f →
        Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
          ≤ C * α ^ 2 * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) :=
  E1Open.E1_hkSq_le_O_of radA_slotSum_le

theorem E1_norm_O :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f →
        Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
          ≤ α * κ * (Work.Spaces.HkNorm α n f
              + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)) :=
  E1Open.E1_norm_O_of radA_slotSum_le

end Work.FTS.StrongEps.EpsE4Thr
