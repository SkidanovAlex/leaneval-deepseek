import Mathlib
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.f_exists
import Submission.Work.RankOneUniqueness.canon_unique
import Submission.Work.ZassenhausSuzuki.twoPoint_inverted_of_zass

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- **The product relation of the (ZT)-functional equation** (Suzuki 1962, Prop. 5 (11) =
HB III XI 11.10 b)(6)).

Write `t x t = β(x) · γ(x) · t · f(x)` with `β(x) ∈ Q`, `γ(x) ∈ D` (unique, since
`H = Q ⋊ D`); here `f(x) = y` is supplied by `FRel H t x y`.  Then for `x₁, x₂` with
`x₁x₂ ≠ 1`, and `π = f(x₁)·β(x₂)`, one has

`f (x₁ x₂) = γ(x₂) · f(π) · γ(x₂)⁻¹ · f(x₂)`.

Proof: expand `t (x₁x₂) t = (t x₁ t)(t x₂ t)`, substitute the two decompositions, move
`γ(x₂)` past `t` using `t γ t = γ⁻¹` (`twoPoint_inverted`), and read off
`t (x₁x₂) t = (m₁ z γ(x₂)) · t · (γ(x₂) z γ(x₂)⁻¹ y₂)`. -/
theorem frel_product {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {x1 x2 y1 y2 : G} (hx1 : x1 * x2 ≠ 1)
    (h1 : Work.RankOneUniqueness.FRel H t x1 y1) (h2r : Work.RankOneUniqueness.FRel H t x2 y2)
    {b2 g2 : G} (hb2 : b2 ∈ Q) (hg2 : g2 ∈ Submission.Blueprint.twoPoint H t)
    (hdec : t * x2 * t = b2 * g2 * (t * y2))
    {pi z : G} (hpi : pi = y1 * b2) (hz : Work.RankOneUniqueness.FRel H t pi z) :
    Work.RankOneUniqueness.FRel H t (x1 * x2) (g2 * z * g2⁻¹ * y2) := by
  obtain ⟨m1, hm1H, hm1⟩ := h1
  obtain ⟨m, hmH, hm⟩ := hz
  have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hsplit
  -- `t` inverts the two-point stabiliser, so in particular `t g2 t = g2⁻¹`
  have hγ0 : t * g2 * t⁻¹ = g2⁻¹ := twoPoint_inverted_of_zass hsplit hzass g2 hg2
  have hγ : t * g2 * t = g2⁻¹ := by rwa [inv_eq_of_mul_eq_one_right ht2] at hγ0
  have hγ' : g2 * t = t * g2⁻¹ := by
    have key : t * (t * g2 * t) = g2 * t := by
      rw [show t * (t * g2 * t) = (t * t) * g2 * t by group, ht2, one_mul]
    rw [← key, hγ]
  have hπ : t * (y1 * b2) * t = m * t * z := by rw [← hpi]; exact hm
  have hg2H : g2 ∈ H := hg2.1
  refine ⟨m1 * m * g2, H.mul_mem (H.mul_mem hm1H hmH) hg2H, ?_⟩
  -- the word computation of the (ZT)-product relation
  calc t * (x1 * x2) * t
      = (t * x1 * t) * (t * x2 * t) := by
        rw [show (t * x1 * t) * (t * x2 * t) = t * x1 * (t * t) * x2 * t by group]
        rw [ht2]; group
    _ = (m1 * t * y1) * (b2 * g2 * (t * y2)) := by rw [hm1, hdec]
    _ = m1 * (t * (y1 * b2) * t) * (t * g2 * t) * y2 := by
        rw [show m1 * (t * (y1 * b2) * t) * (t * g2 * t) * y2 =
            m1 * t * y1 * b2 * (t * t) * g2 * t * y2 by group]
        rw [ht2]; group
    _ = m1 * (m * t * z) * g2⁻¹ * y2 := by rw [hπ, hγ]
    _ = (m1 * m * g2) * t * (g2 * z * g2⁻¹ * y2) := by
        rw [show (m1 * m * g2) * t * (g2 * z * g2⁻¹ * y2) =
            m1 * m * (g2 * t) * (g2 * z * g2⁻¹ * y2) by group]
        rw [hγ']; group

end Work.ZassenhausSuzuki
