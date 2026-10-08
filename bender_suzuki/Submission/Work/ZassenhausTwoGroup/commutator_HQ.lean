import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.etaStar_data

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.commutator_HQ`

In the split rank-one Zassenhaus set-up `IsSplitRankOne H Q t` with `IsZassenhaus H` the
derived subgroup of `H` lies in the regular normal subgroup `Q`: `[H, H] ≤ Q`.  Equivalently,
`H / Q` is abelian, which is what one needs to know that a linear character of `H` trivial on
`Q` (a character of `H/Q`) extends over the whole of `H`.

The two ingredients are:

* **`t` inverts the two-point stabiliser.**  This is `twoPoint_conj_t_eq_inv`
  (`Submission.Work.ZassenhausTwoGroup.etaStar_data`, from the Zassenhaus condition `V = 1`
  and Burnside's lemma): `t * d * t = d⁻¹` for every `d ∈ D = twoPoint H t`.
* **Inversion is then a homomorphism of `D`**, and a group whose inversion map is a
  homomorphism is abelian: `d e = ((d e)⁻¹)⁻¹ = (d⁻¹ e⁻¹)⁻¹ = e d`
  (`isMulCommutative_of_conj_eq_inv` below).

Since `IsSplitRankOne` gives `Q ≤ H`, `H ≤ N_G(Q)`, `Q ⊓ D = ⊥` and `Q ⊔ D = H`, the quotient
`H/Q` is isomorphic to the (abelian!) complement `D`; the general group-theoretic lemma
`Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top` (applied in the group `↥H`, with
`N = Q.subgroupOf H` and `D.subgroupOf H` its commutative complement) then yields
`_root_.commutator ↥H ≤ Q.subgroupOf H`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open Classical
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

/-- **A subgroup inverted by an element is abelian.**  If `t * d * t = d⁻¹` for every `d` in a
subgroup `D`, then `D` is commutative: the hypothesis at `d = 1` gives `t * t = 1`, so
conjugation by `t` is a homomorphism, whence `(d e)⁻¹ = (t d t)(t e t) = d⁻¹ e⁻¹`, and taking
inverses gives `d e = e d`. -/
theorem isMulCommutative_of_conj_eq_inv {G : Type*} [Group G] {D : Subgroup G} {t : G}
    (h : ∀ d ∈ D, t * d * t = d⁻¹) : IsMulCommutative D := by
  -- `t` is an involution
  have ht : t * t = 1 := by simpa using h 1 D.one_mem
  -- conjugation by `t` is multiplicative
  have hmul : ∀ x y : G, t * (x * y) * t = (t * x * t) * (t * y * t) := by
    intro x y
    have h1 := map_mul (MulAut.conj t).toMonoidHom x y
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_right ht] at h1
    exact h1
  refine IsMulCommutative.of_setLike_mul_comm fun d hd e he => ?_
  have h1 : (d * e)⁻¹ = d⁻¹ * e⁻¹ := by
    rw [← h (d * e) (D.mul_mem hd he), ← h d hd, ← h e he]
    exact hmul d e
  calc d * e = ((d * e)⁻¹)⁻¹ := (inv_inv _).symm
    _ = (d⁻¹ * e⁻¹)⁻¹ := by rw [h1]
    _ = e * d := by rw [mul_inv_rev, inv_inv, inv_inv]

/-- In the split rank-one Zassenhaus set-up the derived subgroup of the point stabiliser `H`
lies in the regular normal subgroup `Q`.

Indeed `t` inverts the two-point stabiliser `D = twoPoint H t`
(`twoPoint_conj_t_eq_inv`), so `D` is abelian (`isMulCommutative_of_conj_eq_inv`), and
`H = Q ⋊ D` with `Q ⊴ H`; hence `H/Q ≅ D` is abelian and `[H, H] ≤ Q`. -/
theorem commutator_HQ {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H) :
    _root_.commutator ↥H ≤ Q.subgroupOf H := by
  -- `t` inverts `D = twoPoint H t`, hence `D` is abelian
  have hDinv : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t → t * d * t = d⁻¹ :=
    twoPoint_conj_t_eq_inv h hZ
  have hcomm : IsMulCommutative (Submission.Blueprint.twoPoint H t) :=
    isMulCommutative_of_conj_eq_inv hDinv
  -- `Q` is normal in `H`
  have hnorm : (Q.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer h.normal
  -- `H = Q · D` in `↥H`
  have hsup : Q.subgroupOf H ⊔ (Submission.Blueprint.twoPoint H t).subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.le (inf_le_left : Submission.Blueprint.twoPoint H t ≤ H),
      h.sup_eq, Subgroup.subgroupOf_self]
  exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance

end Work.ZassenhausTwoGroup
