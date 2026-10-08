import Mathlib
import Submission.Work.AppXIDickson.card_le_two_of_subgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.AppXIDickson.card_center_le_four`

The center of a finite group of exponent dividing `4` having at most one involution has order
at most `4`.

Let `Z = Z(G)`.  `Z` is commutative and, since `x ^ 4 = 1` on `G`, every `z ∈ Z` satisfies
`z ^ 4 = 1`; hence the squaring map `φ : Z →* Z`, `φ z = z ^ 2`, is a group homomorphism.
Its kernel `Z[2] = {z : z ^ 2 = 1}` has order `≤ 2` because a non-identity element of the
kernel has order exactly `2` in `Z` (hence in `G`), and `G` has at most one such element
(`huniq`); likewise its image `Z ^ 2` has order `≤ 2`, because `(z ^ 2) ^ 2 = z ^ 4 = 1`, so
every non-identity element of `Z ^ 2` again has order `2` in `G`.  By the first isomorphism
theorem `Nat.card Z = Nat.card Z[2] * Nat.card Z ^ 2` (kernel–image index formula), giving
`Nat.card Z ≤ 2 * 2 = 4`.

The abstract counting fact "a subgroup all of whose non-identity elements have order `2`, in a
group with a unique involution, has at most `2` elements" is
`Work.AppXIDickson.card_le_two_of_subgroup`; it is applied here to `φ.ker` and `φ.range`.
-/

set_option linter.style.haveILetI false

namespace Work.AppXIDickson

theorem card_center_le_four {G : Type*} [Group G] [Finite G]
    (hpow : ∀ x : G, x ^ 4 = 1)
    (huniq : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y) :
    Nat.card (Subgroup.center G) ≤ 4 := by
  classical
  let Z := Subgroup.center G
  change Nat.card Z ≤ 4
  -- The center is commutative.
  letI : CommGroup Z :=
    { mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 (a : G)) }
  -- The squaring map on the center, a group homomorphism since `Z` is commutative.
  let sq : Z →* Z :=
    { toFun := fun z => z ^ 2
      map_one' := by simp
      map_mul' := fun a b => by rw [mul_pow] }
  -- Every element of the center satisfies `z ^ 4 = 1`.
  have hz4 : ∀ z : Z, z ^ 4 = 1 := by
    intro z
    apply Subtype.ext
    rw [Subgroup.coe_pow, hpow]
    rfl
  -- Uniqueness of the involution descends to the center.
  have hZ2 : ∀ x y : Z, orderOf x = 2 → orderOf y = 2 → x = y := by
    intro x y hx hy
    refine Subtype.ext (huniq (x : G) (y : G) ?_ ?_)
    · rw [Subgroup.orderOf_coe]; exact hx
    · rw [Subgroup.orderOf_coe]; exact hy
  -- The kernel `Z[2]`: every non-identity element has order `2`.
  have hker : Nat.card sq.ker ≤ 2 :=
    card_le_two_of_subgroup sq.ker
      (fun k hkne => by
        apply orderOf_eq_prime
        · exact MonoidHom.mem_ker.mp k.2
        · intro h; exact hkne (Subtype.ext h))
      hZ2
  -- The image `Z ^ 2`: every non-identity element is an involution, since `(z ^ 2) ^ 2 = z ^ 4`.
  have himg : Nat.card sq.range ≤ 2 :=
    card_le_two_of_subgroup sq.range
      (fun r hrne => by
        apply orderOf_eq_prime
        · obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp r.2
          rw [← hz]
          change (z ^ 2) ^ 2 = 1
          rw [← pow_mul, show (2 * 2 : ℕ) = 4 from rfl, hz4 z]
        · intro h; exact hrne (Subtype.ext h))
      hZ2
  -- Kernel–image cardinality formula: `|Z| = |ker sq| * |range sq|`.
  have hcard : Nat.card Z = Nat.card sq.ker * Nat.card sq.range := by
    rw [← Subgroup.card_mul_index sq.ker, Subgroup.index_ker sq]
  calc Nat.card Z = Nat.card sq.ker * Nat.card sq.range := hcard
    _ ≤ 2 * 2 := Nat.mul_le_mul hker himg
    _ = 4 := by norm_num

end Work.AppXIDickson
