import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Submission.Work.SSGRoute.ShapiroSetup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute
namespace Shapiro

open scoped TensorProduct

universe u v w

variable (p : ℕ) (G : Type u) [Group G] (H : Subgroup G) (X : Type w) [MulAction G X]
  (s : X → G) (hsec : ∀ (g : G) (x : X), (s x)⁻¹ * g * s (g⁻¹ • x) ∈ H)
  (x₀ : X) (hbase : s x₀ = 1) (hfix : ∀ h : H, (h : G) • x₀ = x₀)
  (M : Type v) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
  [SMulCommClass G (ZMod p) M]

/-- The canonical identification `M ⊗ 𝔽_p[X] ≃ (X → M)` intertwines the diagonal `G`-action with
the action `(g • φ) x = g • φ (g⁻¹ • x)` on functions. -/
theorem permEquivX_smul [Fintype X] [DecidableEq X] (g : G)
    (z : M ⊗[ZMod p] PermModX p X) :
    permEquivX p X M (g • z) = fun x => g • permEquivX p X M z (g⁻¹ • x) := by
  induction z using TensorProduct.induction_on with
  | zero => ext x; simp
  | tmul m f =>
    ext x
    rw [Work.Shrinking.diagTensor_smul_tmul, permEquivX_tmul, permEquivX_tmul]
    simp only [smul_PermModX_apply]
    rw [SMulCommClass.smul_comm (M := G) (N := ZMod p) g (f (g⁻¹ • x)) m]
  | add z w hz hw =>
    rw [smul_add, map_add, map_add, hz, hw]
    ext x
    simp only [Pi.add_apply, smul_add]

/-- At the base point the function `funCX` reproduces the cochain `c` on pairs from `H`. -/
theorem funCX_base (hbase : s x₀ = 1) (hfix : ∀ h : H, (h : G) • x₀ = x₀)
    (c : H × H → M) (h h' : H) :
    funCX G H X s hsec M c (h : G) (h' : G) x₀ = c (h, h') := by
  have hfix' : (((h : G))⁻¹ • x₀ : X) = x₀ := by simpa using hfix (h⁻¹)
  rw [funCX_apply, hfix', AX_base G H X s hsec x₀ hbase hfix h,
    AX_base G H X s hsec x₀ hbase hfix h', hbase, one_smul]

/-- The pointwise 2-cocycle identity for the function `funCX` attached to a 2-cocycle `c` on `H`. -/
theorem funCX_add_eq (c : H × H → M)
    (hc : ∀ a b e : H, c (a * b, e) + c (a, b) = (a : G) • c (b, e) + c (a, b * e))
    (g g' g'' : G) (x : X) :
    funCX G H X s hsec M c (g * g') g'' x + funCX G H X s hsec M c g g' x
      = g • funCX G H X s hsec M c g' g'' (g⁻¹ • x)
        + funCX G H X s hsec M c g (g' * g'') x := by
  have hsm : ∀ y : X, g'⁻¹ • (g⁻¹ • y) = (g * g')⁻¹ • y := fun y => by
    rw [← mul_smul, mul_inv_rev]
  rw [funCX_apply, funCX_apply, funCX_apply, funCX_apply]
  rw [← mul_smul (x := g) (y := s (g⁻¹ • x)), s_mul_AX G H X s hsec g x, mul_smul]
  rw [AX_mul G H X s hsec g g' x, AX_mul G H X s hsec g' g'' (g⁻¹ • x)]
  simp only [hsm]
  rw [← smul_add, ← smul_add]
  exact congrArg (fun m => (s x : G) • m)
    (hc (AX G H X s hsec g x) (AX G H X s hsec g' (g⁻¹ • x))
      (AX G H X s hsec g'' ((g * g')⁻¹ • x)))

end Shapiro
end Work.SSGRoute
