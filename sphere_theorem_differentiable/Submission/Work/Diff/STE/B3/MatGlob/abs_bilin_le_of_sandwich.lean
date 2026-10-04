import Mathlib
import Submission.Work.Diff.STE.Man.Sect

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold Bundle Topology
open Bundle

namespace Work.Diff.STE.B3.MatGlob

/-- **Off-diagonal bound for a bilinear form sandwiched between `lam • g₀` and `K • g₀`.**

If `h` is a pointwise bilinear form on the tangent bundle which is symmetric and satisfies the
*sandwich* inequalities `lam * g₀(v,v) ≤ h(v,v) ≤ K * g₀(v,v)` on the diagonal (with `lam, K ≥ 0`),
then the off-diagonal values are bounded by

  `|h(u,v)| ≤ K * (g₀(u,u) + g₀(v,v))`.

The proof is the two-point form of the Cauchy–Schwarz/discriminant argument: the diagonal values at
`u + v` and `u - v` are nonnegative (because `lam ≥ 0` and `g₀` is positive semidefinite on the
diagonal), and expanding them by symmetry of `h` gives

  `-2 h(u,v) ≤ h(u,u) + h(v,v)`   and   `2 h(u,v) ≤ h(u,u) + h(v,v)`,

i.e. `2 |h(u,v)| ≤ h(u,u) + h(v,v) ≤ K (g₀(u,u) + g₀(v,v))`. -/
theorem abs_bilin_le_of_sandwich
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {g₀ : Submission.Diff.SMet I M}
    {h : Work.Diff.STE.Bil (I := I) (M := M)} {lam K : ℝ}
    (hlam : 0 ≤ lam) (hK : 0 ≤ K)
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
    (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
    (x : M) (u v : TangentSpace I x) :
    |h x u v| ≤ K * (g₀.inner x u u + g₀.inner x v v) := by
  -- `g₀` is positive semidefinite on the diagonal.
  have hg (w : TangentSpace I x) : 0 ≤ g₀.inner x w w := by
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · exact le_of_lt (g₀.pos x w hw)
  -- hence so is `h`, by the lower half of the sandwich.
  have hnn (w : TangentSpace I x) : 0 ≤ h x w w :=
    le_trans (mul_nonneg hlam (hg w)) (hell x w)
  -- expansion of the diagonal value at `u + v`
  have hpp : h x (u + v) (u + v) = h x u u + 2 * h x u v + h x v v := by
    simp only [map_add, add_apply]
    rw [hsym x v u]; ring
  -- expansion of the diagonal value at `u - v`
  have hmm : h x (u - v) (u - v) = h x u u - 2 * h x u v + h x v v := by
    simp only [map_sub, sub_apply]
    rw [hsym x v u]; ring
  have h1 : -2 * h x u v ≤ h x u u + h x v v := by
    have := hnn (u + v); rw [hpp] at this; linarith
  have h2 : 2 * h x u v ≤ h x u u + h x v v := by
    have := hnn (u - v); rw [hmm] at this; linarith
  have habs : 2 * |h x u v| ≤ h x u u + h x v v := by
    have h3 : |2 * h x u v| ≤ h x u u + h x v v := by
      rw [abs_le]; exact ⟨by linarith, h2⟩
    simpa [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] using h3
  have hS : h x u u + h x v v ≤ K * (g₀.inner x u u + g₀.inner x v v) := by
    have := hub x u; have := hub x v; linarith
  have h0 : 0 ≤ |h x u v| := abs_nonneg _
  linarith

end Work.Diff.STE.B3.MatGlob
