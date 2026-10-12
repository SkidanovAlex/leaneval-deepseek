import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.BoseFixB1.PerBoxNames
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open scoped ContDiff Topology Real

set_option autoImplicit false

/-- **The corpus small-box cutoff is `C²` in the space variable** (`M ≥ 3`).

`χ_{B(u)}(x) = χ(x/ℓ)·χ_M((ℓd)⁻¹ • x − u)` (`Submission.BoseGases.chiSmallB`): the `ℓ`-scale
factor is the smooth corpus bump `χ(·/ℓ)` (`Submission.BoseGases.chiScale`), and the `(ℓd)`-scale
factor is `Submission.BoseGases.chiSmall M`, which is `C²` for `M ≥ 3` because `ζ^M` is `C²`
for `M ≥ 3` — the `M`-th power kills the derivative jump of the cosine profile `ζ` at the box
faces (`Submission.Work.BoseGases.zeta1d_pow_contDiff_two`) — composed with the smooth affine
map `x ↦ (ℓd)⁻¹ • x − u`.  The product of two `C²` functions is `C²`. -/
theorem chiSmallB_contDiff_two {M : ℕ} (hM : 3 ≤ M) {ℓ d : ℝ}
    (u : EuclideanSpace ℝ (Fin 3)) :
    ContDiff ℝ (2 : ℕ∞) (Submission.BoseGases.chiSmallB M ℓ d u) := by
  -- the `ℓ`-scale factor `χ(·/ℓ)` is smooth (and in particular `C²`)
  have hchi : ContDiff ℝ (2 : ℕ∞) (Submission.BoseGases.chiScale ℓ) := by
    by_cases hℓ : ℓ = 0
    · subst hℓ
      have hconst : Submission.BoseGases.chiScale 0 =
          (fun _ : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chi 0) := by
        funext x
        simp [Submission.BoseGases.chiScale]
      rw [hconst]
      exact contDiff_const
    · exact (Submission.BoseGases.chiScale_contDiff hℓ).of_le (WithTop.coe_le_coe.mpr le_top)
  -- the affine change of variables `x ↦ (ℓd)⁻¹ • x − u` is smooth
  have haff : ContDiff ℝ (2 : ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => (ℓ * d)⁻¹ • x - u) := by
    fun_prop
  -- the `(ℓd)`-scale factor `χ_M((ℓd)⁻¹ • x − u)` is `C²`
  have hsmall : ContDiff ℝ (2 : ℕ∞) (fun x : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) :=
    (Submission.BoseGases.chiSmall_contDiff_two hM).comp haff
  have hprod : ContDiff ℝ (2 : ℕ∞) (fun x : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiScale ℓ x *
        Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) := hchi.mul hsmall
  exact hprod

end Work.BoseFixB1
