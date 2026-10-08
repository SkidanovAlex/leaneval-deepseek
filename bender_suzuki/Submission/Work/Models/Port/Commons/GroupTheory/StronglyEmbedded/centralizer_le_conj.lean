import Mathlib.GroupTheory.OrderOfElement
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.centralizer_le
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.mem_map_conj_iff
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.orderOf_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

/-- The order-2 analogue of `centralizer_le` after conjugation: if the
involution `t` lies in the conjugate `x M x⁻¹`, then its centralizer
`C_G(t)` also lies in `x M x⁻¹`.

Proof: conjugate back.  The element `s := x⁻¹ t x` lies in `M` (by
`mem_map_conj_iff`) and still has order 2 (by `orderOf_conj`), so
`centralizer_le` gives `C_G(s) ≤ M`.  Since conjugation by `x` is an
automorphism it carries `C_G(s)` onto `C_G(x s x⁻¹) = C_G(t)`, and carries
`M` onto `x M x⁻¹`. -/
theorem centralizer_le_conj {G : Type*} [Group G] (M : Subgroup G)
    (hOdd : ∀ g : G, g ∉ M → Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    (x : G) {t : G} (htM : t ∈ M.map (MulAut.conj x).toMonoidHom) (ht : orderOf t = 2) :
    Subgroup.centralizer ({t} : Set G) ≤ M.map (MulAut.conj x).toMonoidHom := by
  let s : G := x⁻¹ * t * x
  have hsM : s ∈ M := by
    dsimp [s]
    exact (mem_map_conj_iff (A := M) (z := x) (u := t)).mp htM
  have hsord : orderOf s = 2 := by
    dsimp [s]
    calc
      orderOf (x⁻¹ * t * x) = orderOf t := by simpa using orderOf_conj x⁻¹ t
      _ = 2 := ht
  -- C_G(s) ≤ M with s = x⁻¹ t x an involution of M.
  have hCleM : Subgroup.centralizer ({s} : Set G) ≤ M :=
    centralizer_le M hOdd (t := s) hsM hsord
  intro c hc
  -- c ∈ M^x  iff  x⁻¹ c x ∈ M; and x⁻¹ c x centralizes s when c centralizes t.
  rw [mem_map_conj_iff (A := M) (z := x) (u := c)]
  exact hCleM (by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : c * t = t * c := (Subgroup.mem_centralizer_singleton_iff.mp hc)
    dsimp [s]
    calc
      (x⁻¹ * c * x) * (x⁻¹ * t * x) = x⁻¹ * (c * t) * x := by group
      _ = x⁻¹ * (t * c) * x := by rw [hcomm]
      _ = (x⁻¹ * t * x) * (x⁻¹ * c * x) := by group)

end Commons.GroupTheory.StronglyEmbedded
