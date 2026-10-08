import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `maxAbelianOrder` is natural for homomorphisms injective on `P`

If `f : G →* H` is injective on a subgroup `P ≤ G` (equivalently `P ⊓ f.ker = ⊥`), then the
map `P → P.map f` is a bijection, and it induces a bijection between the abelian subgroups of `P`
and those of `P.map f` preserving cardinalities.  Hence the maximal order of an abelian subgroup
is the same for `P` and for its image:

`maxAbelianOrder (P.map f) = maxAbelianOrder P`.

This is the analogue for `maxAbelianOrder` of `thompsonJ_map_of_ker_inf_eq_bot` and
`ZJ_map_of_ker_inf_eq_bot`; it is used to transport computations in the Thompson subgroup along
injective maps (e.g. restriction to a Hall subgroup, or an embedding of a section into `G`).
-/

namespace Work.PGroup

variable {G H : Type*} [Group G] [Group H]

/-- If `f` is injective on `P`, in the form `P ⊓ f.ker = ⊥`, then elements of `P` with the same
image under `f` are equal. -/
lemma eq_of_map_eq_of_ker_inf_eq_bot {f : G →* H} {P : Subgroup G} (hker : P ⊓ f.ker = ⊥)
    {x y : G} (hx : x ∈ P) (hy : y ∈ P) (h : f x = f y) : x = y := by
  have hmem : x * y⁻¹ ∈ P ⊓ f.ker := by
    refine ⟨P.mul_mem hx (P.inv_mem hy), ?_⟩
    show f (x * y⁻¹) = 1
    simp [h]
  rw [hker] at hmem
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)

/-- `f` injective on `P` is injective on every subgroup `A ≤ P`, hence preserves the cardinality
of subgroups: `#(A.map f) = #A`.  (Note that no finiteness is needed, since `Nat.card` of an
infinite type is `0` and the map is a bijection in all cases.) -/
lemma card_map_eq_card_of_ker_inf_eq_bot {f : G →* H} {P : Subgroup G} (hker : P ⊓ f.ker = ⊥)
    {A : Subgroup G} (hA : A ≤ P) : Nat.card (A.map f) = Nat.card A := by
  have key : ∀ a : A,
      Classical.choose (Subgroup.mem_map.mp (Subgroup.mem_map_of_mem f a.2)) = a.1 := by
    intro a
    exact eq_of_map_eq_of_ker_inf_eq_bot hker
      (hA (Classical.choose_spec (Subgroup.mem_map.mp (Subgroup.mem_map_of_mem f a.2))).1)
      (hA a.2)
      (Classical.choose_spec (Subgroup.mem_map.mp (Subgroup.mem_map_of_mem f a.2))).2
  have e : A ≃ (A.map f) :=
    { toFun := fun a => ⟨f a.1, Subgroup.mem_map_of_mem f a.2⟩
      invFun := fun b => ⟨Classical.choose (Subgroup.mem_map.mp b.2),
        (Classical.choose_spec (Subgroup.mem_map.mp b.2)).1⟩
      left_inv := fun a => Subtype.ext (key a)
      right_inv := fun b => Subtype.ext (Classical.choose_spec (Subgroup.mem_map.mp b.2)).2 }
  exact (Nat.card_congr e).symm

/-- For `B ≤ P.map f` with `f` injective on `P`, the preimage of `B` meets `P` in a subgroup of
`P` whose image is exactly `B`. -/
lemma map_inf_comap_eq_of_le_map_of_ker_inf_eq_bot {f : G →* H} {P : Subgroup G}
    (_hker : P ⊓ f.ker = ⊥) {B : Subgroup H} (hB : B ≤ P.map f) :
    (B.comap f ⊓ P).map f = B := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    exact inf_le_left
  · intro b hb
    obtain ⟨p, hpP, hfp⟩ := Subgroup.mem_map.mp (hB hb)
    exact Subgroup.mem_map.mpr ⟨p, ⟨by show f p ∈ B; rw [hfp]; exact hb, hpP⟩, hfp⟩

/-- For `B ≤ P.map f` abelian with `f` injective on `P`, the subgroup `B.comap f ⊓ P` is abelian:
commutators are detected inside `P`, where `f` is injective, and `B` is abelian. -/
lemma isMulCommutative_inf_comap_of_ker_inf_eq_bot {f : G →* H} {P : Subgroup G}
    (hker : P ⊓ f.ker = ⊥) {B : Subgroup H} (hBab : IsMulCommutative B) :
    IsMulCommutative ↥(B.comap f ⊓ P) := by
  refine IsMulCommutative.of_comm fun a b => ?_
  apply Subtype.ext
  refine eq_of_map_eq_of_ker_inf_eq_bot hker
    (P.mul_mem a.2.2 b.2.2) (P.mul_mem b.2.2 a.2.2) ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  have hcomm := congrArg Subtype.val
    (hBab.is_comm.comm ⟨f (a : G), a.2.1⟩ ⟨f (b : G), b.2.1⟩)
  simpa [Subgroup.coe_mul] using hcomm

theorem maxAbelianOrder_map_of_ker_inf_eq_bot {G H : Type*} [Group G] [Group H] (f : G →* H)
    (P : Subgroup G) (hker : P ⊓ f.ker = ⊥) :
    Work.PGroup.maxAbelianOrder (P.map f) = Work.PGroup.maxAbelianOrder P := by
  have hcard : ∀ B : Subgroup H, B ≤ P.map f → IsMulCommutative B →
      Nat.card ↥(B.comap f ⊓ P) = Nat.card ↥B := by
    intro B hB _
    rw [← card_map_eq_card_of_ker_inf_eq_bot hker (A := B.comap f ⊓ P) inf_le_right,
      map_inf_comap_eq_of_le_map_of_ker_inf_eq_bot hker hB]
  have hset : {n : ℕ | ∃ B : Subgroup H, B ≤ P.map f ∧ IsMulCommutative B ∧ Nat.card B = n}
      = {n : ℕ | ∃ A : Subgroup G, A ≤ P ∧ IsMulCommutative A ∧ Nat.card A = n} := by
    ext n
    constructor
    · rintro ⟨B, hB, hBab, hBcard⟩
      exact ⟨B.comap f ⊓ P, inf_le_right,
        isMulCommutative_inf_comap_of_ker_inf_eq_bot hker hBab,
        by rw [hcard B hB hBab, hBcard]⟩
    · rintro ⟨A, hA, hAab, hAcard⟩
      exact ⟨A.map f, Subgroup.map_mono hA, Subgroup.map_isMulCommutative A f,
        by rw [card_map_eq_card_of_ker_inf_eq_bot hker hA, hAcard]⟩
  rw [maxAbelianOrder, maxAbelianOrder, hset]

end Work.PGroup
