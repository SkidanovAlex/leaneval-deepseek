import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.ZJ_characteristic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Z(J(P))` is natural under homomorphisms injective on `P`

If `f : G →* H` is a homomorphism whose kernel meets `P` trivially, then `f` restricts to an
isomorphism `P ≃* P.map f`; consequently every construction of `Work.PGroup` that is phrased in
terms of the subgroups of `P` (their order, commutativity, the closure of the union of the
abelian subgroups of maximal order, and the centre) transports along `f`.

The main result is `Work.PGroup.ZJ_map_of_ker_inf_eq_bot`:

`Z(J(P.map f)) = (Z(J(P))).map f`, i.e. `Z(J(P))` is natural under `f`.

The transport statements for the intermediate constructions are proved here (as private lemmas,
since the same statements are also available as standalone modules):
`maxAbelianOrder (P.map f) = maxAbelianOrder P` and `J(P.map f) = (J(P)).map f`.

The strategy is uniform: the hypothesis `P ⊓ f.ker = ⊥` is exactly the statement that `f` is
injective on `P`, so that
* `A ↦ A.map f` is a bijection between the subgroups of `P` and those of `P.map f`, with inverse
  `B ↦ B.comap f ⊓ P` (`map_comap_inf_eq_self`),
* this bijection preserves commutativity (`isMulCommutative_map_of_le`,
  `isMulCommutative_comap_inf_of_inf_ker_eq_bot`) and cardinality
  (`card_map_eq_of_inf_ker_eq_bot`),
* `Subgroup.map` commutes with closures (`MonoidHom.map_closure`).

The same argument applied to the centre of a subgroup gives
`centerIn (K.map f) = (centerIn K).map f` (`centerIn_map_of_ker_inf_eq_bot`), which is applied to
`K = J(P) ≤ P`, where injectivity of `f` on `K` is inherited from injectivity on `P`.
-/

set_option linter.style.haveILetI false

namespace Work.PGroup

section Transport

variable {G H : Type*} [Group G] [Group H]

/-- If the kernel of `f` meets `P` trivially, then `f` is injective on `P`.  Stated in the form
needed below: two elements of `P` with the same image are equal. -/
private lemma map_eq_of_mem_of_inf_ker_eq_bot {f : G →* H} {P : Subgroup G}
    (hker : P ⊓ f.ker = ⊥) {x y : G} (hx : x ∈ P) (hy : y ∈ P) (h : f x = f y) : x = y := by
  have h1 : x * y⁻¹ ∈ P := P.mul_mem hx (P.inv_mem hy)
  have h2 : x * y⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have h3 : x * y⁻¹ ∈ (⊥ : Subgroup G) := by rw [← hker]; exact ⟨h1, h2⟩
  rw [Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.mp h3

/-- If `f` is injective on `P` (i.e. `P ⊓ f.ker = ⊥`) then `A ↦ A.map f` preserves cardinality
for subgroups `A ≤ P`.  This is the analogue of `Subgroup.card_map_of_injective` with global
injectivity replaced by injectivity on `P`; the two sets are in bijection via `f`. -/
private lemma card_map_eq_of_inf_ker_eq_bot {f : G →* H} {P A : Subgroup G} (hA : A ≤ P)
    (hker : P ⊓ f.ker = ⊥) : Nat.card ↥(A.map f) = Nat.card ↥A := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun a : A => (⟨f a, ⟨a, a.2, rfl⟩⟩ : A.map f)) ⟨?_, ?_⟩)).symm
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    exact Subtype.ext
      (map_eq_of_mem_of_inf_ker_eq_bot hker (hA hx) (hA hy) (congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- The image of an abelian subgroup under a homomorphism is abelian. -/
private lemma isMulCommutative_map_of_le {f : G →* H} {A : Subgroup G}
    (h : IsMulCommutative A) : IsMulCommutative ↥(A.map f) := by
  haveI := h
  exact Subgroup.map_isMulCommutative A f

/-- A subgroup of `P.map f` is abelian as soon as its preimage (intersected with `P`) is; here
the preimage `B.comap f ⊓ P` is abelian when `B` is, by injectivity of `f` on `P`. -/
private lemma isMulCommutative_comap_inf_of_inf_ker_eq_bot {f : G →* H} {P : Subgroup G}
    {B : Subgroup H} (hB : IsMulCommutative B) (hker : P ⊓ f.ker = ⊥) :
    IsMulCommutative ↥(B.comap f ⊓ P) := by
  refine isMulCommutative_iff.mpr fun x y => Subtype.ext ?_
  have hxP : (x : G) ∈ P := (Subgroup.mem_inf.mp x.2).2
  have hyP : (y : G) ∈ P := (Subgroup.mem_inf.mp y.2).2
  have hxB : f (x : G) ∈ B := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp x.2).1
  have hyB : f (y : G) ∈ B := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp y.2).1
  refine map_eq_of_mem_of_inf_ker_eq_bot hker (P.mul_mem hxP hyP) (P.mul_mem hyP hxP) ?_
  show f ((x : G) * (y : G)) = f ((y : G) * (x : G))
  rw [map_mul, map_mul]
  exact congrArg Subtype.val (isMulCommutative_iff.mp hB ⟨_, hxB⟩ ⟨_, hyB⟩)

/-- `B ↦ B.comap f ⊓ P` is inverse to `A ↦ A.map f` on the subgroups of `P` and of `P.map f`:
if `B ≤ P.map f` then `(B.comap f ⊓ P).map f = B`. -/
private lemma map_comap_inf_eq_self {f : G →* H} {P : Subgroup G} {B : Subgroup H}
    (hB : B ≤ P.map f) : (B.comap f ⊓ P).map f = B := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hx).1
  · intro y hy
    obtain ⟨x, hxP, hxy⟩ := Subgroup.mem_map.mp (hB hy)
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_comap.mpr (by rw [hxy]; exact hy), hxP⟩, hxy⟩

/-- `maxAbelianOrder` is natural under homomorphisms that are injective on `P`.  The two sets of
natural numbers whose suprema define `maxAbelianOrder P` and `maxAbelianOrder (P.map f)` are
literally equal, because `A ↦ A.map f` is a bijection between the subgroups of `P` and those of
`P.map f` preserving commutativity and cardinality. -/
private lemma maxAbelianOrder_map_of_ker_inf_eq_bot {f : G →* H} {P : Subgroup G}
    (hker : P ⊓ f.ker = ⊥) : maxAbelianOrder (P.map f) = maxAbelianOrder P := by
  have hset : {n : ℕ | ∃ A : Subgroup G, A ≤ P ∧ IsMulCommutative A ∧ Nat.card A = n}
      = {n : ℕ | ∃ B : Subgroup H, B ≤ P.map f ∧ IsMulCommutative B ∧ Nat.card B = n} := by
    ext n
    constructor
    · rintro ⟨A, hA, hAab, hcard⟩
      refine ⟨A.map f, Subgroup.map_mono hA, isMulCommutative_map_of_le hAab, ?_⟩
      rw [card_map_eq_of_inf_ker_eq_bot hA hker, hcard]
    · rintro ⟨B, hB, hBab, hcard⟩
      refine ⟨B.comap f ⊓ P, inf_le_right,
        isMulCommutative_comap_inf_of_inf_ker_eq_bot hBab hker, ?_⟩
      rw [← card_map_eq_of_inf_ker_eq_bot inf_le_right hker, map_comap_inf_eq_self hB, hcard]
  rw [maxAbelianOrder, maxAbelianOrder, hset]

/-- The Thompson subgroup is natural under homomorphisms that are injective on `P`.  This
generalizes `Work.PGroup.thompsonJ_map_of_injective` (which assumes `f` injective globally):
only injectivity of `f` on `P` is needed, because `J(P)` is generated by the abelian subgroups
of `P` of maximal order, and these are permuted by `A ↦ A.map f`. -/
private lemma thompsonJ_map_of_ker_inf_eq_bot {f : G →* H} {P : Subgroup G}
    (hker : P ⊓ f.ker = ⊥) : thompsonJ (P.map f) = (thompsonJ P).map f := by
  have hS : thompsonJ P = Subgroup.closure {x : G | ∃ A : Subgroup G, A ≤ P ∧
      IsMulCommutative A ∧ Nat.card A = maxAbelianOrder P ∧ x ∈ A} := rfl
  have hT : thompsonJ (P.map f) = Subgroup.closure {y : H | ∃ B : Subgroup H, B ≤ P.map f ∧
      IsMulCommutative B ∧ Nat.card B = maxAbelianOrder (P.map f) ∧ y ∈ B} := rfl
  rw [hT, hS, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨B, hB, hBab, hBcard, hyB⟩
    have hA : (B.comap f ⊓ P) ≤ P := inf_le_right
    have hmem : y ∈ (B.comap f ⊓ P).map f := by
      rw [map_comap_inf_eq_self hB]; exact hyB
    obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp hmem
    have hcard' : Nat.card ↥(B.comap f ⊓ P) = maxAbelianOrder P := by
      rw [← card_map_eq_of_inf_ker_eq_bot hA hker, map_comap_inf_eq_self hB, hBcard,
        maxAbelianOrder_map_of_ker_inf_eq_bot hker]
    exact ⟨x, ⟨B.comap f ⊓ P, hA, isMulCommutative_comap_inf_of_inf_ker_eq_bot hBab hker,
      hcard', hx⟩, hfx⟩
  · rintro ⟨x, ⟨A, hA, hAab, hAcard, hxA⟩, rfl⟩
    refine ⟨A.map f, Subgroup.map_mono hA, isMulCommutative_map_of_le hAab, ?_,
      ⟨x, hxA, rfl⟩⟩
    rw [card_map_eq_of_inf_ker_eq_bot hA hker, hAcard,
      ← maxAbelianOrder_map_of_ker_inf_eq_bot hker]

/-- The centre of a subgroup is natural under homomorphisms that are injective on it: this is the
transport of `Subgroup.center` across the isomorphism `K ≃* K.map f` induced by `f`. -/
private lemma centerIn_map_of_ker_inf_eq_bot {f : G →* H} {K : Subgroup G}
    (hker : K ⊓ f.ker = ⊥) : centerIn (K.map f) = (centerIn K).map f := by
  ext x
  rw [mem_centerIn_iff]
  constructor
  · rintro ⟨hx, hcomm⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨a, ?_, rfl⟩
    rw [mem_centerIn_iff]
    refine ⟨ha, fun c hc => ?_⟩
    refine map_eq_of_mem_of_inf_ker_eq_bot hker (K.mul_mem hc ha) (K.mul_mem ha hc) ?_
    show f (c * a) = f (a * c)
    rw [map_mul, map_mul]
    exact hcomm (f c) ⟨c, hc, rfl⟩
  · rintro hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [mem_centerIn_iff] at ha
    refine ⟨⟨a, ha.1, rfl⟩, fun y hy => ?_⟩
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, ha.2 c hc]

end Transport

/-- `Z(J(P))` is natural under homomorphisms that are injective on `P`: if `P ⊓ f.ker = ⊥`
then `Z(J(P)).map f = Z(J(P.map f))`.  Restricted to `P`, such an `f` is an isomorphism onto
`P.map f`, and both `thompsonJ` and `centerIn` transport across a group isomorphism. -/
theorem ZJ_map_of_ker_inf_eq_bot {G H : Type*} [Group G] [Group H] (f : G →* H)
    (P : Subgroup G) (hker : P ⊓ f.ker = ⊥) :
    Work.PGroup.ZJ (P.map f) = (Work.PGroup.ZJ P).map f := by
  -- `f` is injective on `J(P) ≤ P` as well, since `J(P) ⊓ f.ker ≤ P ⊓ f.ker = ⊥`.
  have hK : thompsonJ P ⊓ f.ker = ⊥ := by
    have h1 : thompsonJ P ⊓ f.ker ≤ P ⊓ f.ker := inf_le_inf_right f.ker (thompsonJ_le P)
    rw [hker] at h1
    exact le_bot_iff.mp h1
  show centerIn (thompsonJ (P.map f)) = (centerIn (thompsonJ P)).map f
  rw [thompsonJ_map_of_ker_inf_eq_bot hker, centerIn_map_of_ker_inf_eq_bot hK]

end Work.PGroup
