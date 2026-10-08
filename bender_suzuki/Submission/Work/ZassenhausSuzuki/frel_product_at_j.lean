import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsAux
import Submission.Work.ZassenhausSuzuki.frel_product

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- **The `f`-relation at the element `j = g²`** (iterated form of the (ZT) product relation).

Assume `t g² t = g t g⁻¹`; then for `f(x₁) = y₁` and `f(y₁ g) = z` one has

`f (x₁ g²) = z g⁻¹`.

Proof (pure word computation, no group theory beyond `t² = 1`): using `t x₁ g² t = (t x₁ t)(t g² t)`,
`t x₁ t = m₁ t y₁`, `t y₁ g t = m t z` and `t g² t = g t g⁻¹` we get

`t x₁ g² t = m₁ (t y₁ g t) g⁻¹ = m₁ m t z g⁻¹ = (m₁ m) t (z g⁻¹)`,

with `m₁ m ∈ H`, which is exactly `FRel H t (x₁ g²) (z g⁻¹)`. -/
theorem frel_product_at_j {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {g : Q} (hg2ne : g ^ 2 ≠ 1)
    (hstruct : t * (((g ^ 2 : Q)) : G) * t = (g : G) * t * (((g⁻¹ : Q)) : G))
    {x1 y1 : G} (h1 : Work.RankOneUniqueness.FRel H t x1 y1)
    {z : Q} (hz : Work.RankOneUniqueness.FRel H t (y1 * (g : G)) (z : G))
    (hne : x1 * (((g ^ 2 : Q)) : G) ≠ 1) :
    Work.RankOneUniqueness.FRel H t (x1 * (((g ^ 2 : Q)) : G)) (((z * g⁻¹ : Q)) : G) := by
  obtain ⟨m1, hm1H, hm1⟩ := h1
  obtain ⟨m, hmH, hm⟩ := hz
  have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hsplit
  refine ⟨m1 * m, H.mul_mem hm1H hmH, ?_⟩
  show t * (x1 * (((g ^ 2 : Q)) : G)) * t = (m1 * m) * t * (((z * g⁻¹ : Q)) : G)
  calc t * (x1 * (((g ^ 2 : Q)) : G)) * t
      = (t * x1 * t) * (t * (((g ^ 2 : Q)) : G) * t) := by
          rw [show (t * x1 * t) * (t * (((g ^ 2 : Q)) : G) * t)
                = t * x1 * (t * t) * (((g ^ 2 : Q)) : G) * t by group, ht2]
          group
    _ = (m1 * t * y1) * ((g : G) * t * (((g⁻¹ : Q)) : G)) := by rw [hm1, hstruct]
    _ = (m1 * m) * t * ((z : G) * (((g⁻¹ : Q)) : G)) := by
          rw [show (m1 * t * y1) * ((g : G) * t * (((g⁻¹ : Q)) : G))
                = m1 * (t * (y1 * (g : G)) * t) * (((g⁻¹ : Q)) : G) by group, hm]
          group
    _ = (m1 * m) * t * (((z * g⁻¹ : Q)) : G) := by push_cast; group

end Work.ZassenhausSuzuki
