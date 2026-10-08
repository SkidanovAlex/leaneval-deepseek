/-
Copyright (c) 2024. All rights reserved.

# The fibres of the squaring map in a Suzuki 2-group of order `|Z(P)|²`

Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), 79--96 (`REFS/higman_suzuki2groups.md`).
For a Suzuki 2-group `P` with `|P| = |Z(P)|²` every element of the centre is a square and every
fibre of the squaring map `x ↦ x²` over a central element has exactly `|Z(P)|` elements.

Main result: `Work.PSU3.StageA.sq_fiber_card_of_card_sq`.

## Route

Write `Z = Z(P)`, `f_x w = #{y : P | y² = w}` for `w ∈ Z`, and `q = |Z|`.

* `card_eq_sum_card_sqFiber`: the fibres over the elements of `Z` partition `P` (all squares are
  central), so `|P| = Σ_{w ∈ Z} f_x w`.
* `card_sqFiber_one_eq_card_of_iff`: by Higman's clause `Z(P) = {z | z² = 1}` the fibre over `1`
  is exactly `Z`, so `f_x 1 = q`.
* `card_sqFiber_eq_of_map_eq`: if an automorphism `ξ` sends `w` to `w'` then it bijects the fibre
  over `w` onto the fibre over `w'`.  Every `w ∈ Z`, `w ≠ 1` is an involution, and the Suzuki
  automorphism `ξ` of the hypothesis permutes the involutions transitively; hence all the
  `q - 1` fibres over the elements `≠ 1` of `Z` have one common value, namely `f_x z`.
* `|P| = |Z|²` then gives `q² = q + (q - 1) * f_x z`, and `q ≥ 2` forces `f_x z = q`.

Note that neither the classification of the `|P| = |Z|²` case by `A(n,θ)` nor any argument that
the squaring map is a homomorphism is needed: the counting is driven by the transitivity of the
Suzuki automorphism on the involutions.
-/
import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Interface

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.PSU3.StageA

/-- **Automorphisms permute the fibres of squaring.**  If `ξ ^ k` carries `a` to `b`, then the
fibre `{x | x² = a}` is in bijection with the fibre `{x | x² = b}`. -/
theorem card_sqFiber_eq_of_map_eq {P : Type} [Group P]
    (ξ : MulAut P) (k : ℕ) {a b : P} (h : (ξ ^ k) a = b) :
    Nat.card {x : P // x ^ 2 = a} = Nat.card {x : P // x ^ 2 = b} := by
  refine Nat.card_congr
    { toFun := fun x => ⟨(ξ ^ k) x.1, by rw [← map_pow, x.2, h]⟩
      invFun := fun y => ⟨((ξ ^ k)⁻¹) y.1, by
        have h1 : ((ξ ^ k)⁻¹) (y.1 ^ 2) = (((ξ ^ k)⁻¹) y.1) ^ 2 := map_pow _ y.1 2
        rw [← h1, y.2, ← h]
        simp⟩
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp }

/-- If a subgroup `Z` is exactly the set of elements squaring to `1`, then the fibre of squaring
over `1` has `|Z|` elements. -/
theorem card_sqFiber_one_eq_card_of_iff {P : Type} [Group P] (Z : Subgroup P)
    (hZ : ∀ x : P, x ∈ Z ↔ x ^ 2 = 1) :
    Nat.card {x : P // x ^ 2 = 1} = Nat.card ↥Z := by
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1, (hZ x.1).mpr x.2⟩
      invFun := fun z => ⟨z.1, (hZ z.1).mp z.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun z => by ext; rfl }

/-- **The fibres of squaring over a subgroup partition the group.**  If every square lies in `Z`
then `|P| = Σ_{w ∈ Z} #{x | x² = w}`. -/
theorem card_eq_sum_card_sqFiber {P : Type} [Group P] [Finite P] (Z : Subgroup P) [Fintype ↥Z]
    (hZ : ∀ x : P, x ^ 2 ∈ Z) :
    Nat.card P = ∑ w : ↥Z, Nat.card {x : P // x ^ 2 = (w : P)} := by
  have e : (Σ w : ↥Z, {x : P // x ^ 2 = (w : P)}) ≃ P :=
    { toFun := fun s => s.2.1
      invFun := fun x => ⟨⟨x ^ 2, hZ x⟩, ⟨x, rfl⟩⟩
      left_inv := fun s => by
        obtain ⟨w, x, hx⟩ := s
        have hw : w = ⟨x ^ 2, hZ x⟩ := Subtype.ext hx.symm
        subst hw
        rfl
      right_inv := fun x => rfl }
  rw [← Nat.card_congr e, Nat.card_sigma]

/-- **The squaring fibres over the centre of a Suzuki 2-group of order `|Z(P)|²`.**

Higman's clauses `Z(P) = {z | z² = 1}` and `x² ∈ Z(P)` turn the fibres of `x ↦ x²` over the
centre into a partition of `P`; the Suzuki automorphism `ξ` permutes the involutions, hence the
fibres over the `q - 1` non-identity central elements transitively.  Since the fibre over `1` is
the centre itself, `|P| = q²` forces every one of those fibres to have exactly `q` elements. -/
theorem sq_fiber_card_of_card_sq {P : Type} [Group P] [Finite P]
    (hHig : Submission.Blueprint.HigmanProp) (hSuz : Work.Higman.IsSuzuki2Grp P)
    (hcard : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 2)
    {z : P} (hz : z ∈ Subgroup.center P) (hz1 : z ≠ 1) :
    Nat.card {x : P // x ^ 2 = z} = Nat.card ↥(Subgroup.center P) := by
  classical
  haveI : Fintype ↥(Subgroup.center P) := Fintype.ofFinite _
  -- Higman's classification, in the form of the two clauses used below.
  have hsuz2 : Submission.Blueprint.IsSuzukiTwoGroup P :=
    Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp.mpr ⟨hSuz⟩
  obtain ⟨hA1, hA2, -, -, -⟩ := hHig P hsuz2
  -- The fibres over the centre partition `P`.
  have hsum := card_eq_sum_card_sqFiber (Subgroup.center P) hA2
  -- The fibre over `1` is the centre.
  have hF1 : Nat.card {x : P // x ^ 2 = ((1 : ↥(Subgroup.center P)) : P)} =
      Nat.card ↥(Subgroup.center P) :=
    card_sqFiber_one_eq_card_of_iff (Subgroup.center P) hA1
  -- All the fibres over non-identity central elements have the same size.
  have hconst : ∀ w : ↥(Subgroup.center P), w ≠ 1 →
      Nat.card {x : P // x ^ 2 = (w : P)} = Nat.card {x : P // x ^ 2 = z} := by
    intro w hw
    have hw1 : (w : P) ≠ 1 := fun h => hw (Subtype.ext h)
    have hwo : orderOf (w : P) = 2 := by
      rw [orderOf_eq_prime_iff]
      exact ⟨(hA1 (w : P)).mp w.2, hw1⟩
    have hzo : orderOf z = 2 := by
      rw [orderOf_eq_prime_iff]
      exact ⟨(hA1 z).mp hz, hz1⟩
    obtain ⟨k, hk⟩ := hSuz.trans (w : P) z hwo hzo
    exact card_sqFiber_eq_of_map_eq hSuz.xi k hk
  have herase : (∑ w ∈ Finset.univ.erase (1 : ↥(Subgroup.center P)),
        Nat.card {x : P // x ^ 2 = (w : P)}) =
      (Nat.card ↥(Subgroup.center P) - 1) * Nat.card {x : P // x ^ 2 = z} := by
    rw [Finset.sum_congr rfl (fun w hw => hconst w (Finset.mem_erase.mp hw).1), Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ (1 : ↥(Subgroup.center P))), Finset.card_univ,
      ← Nat.card_eq_fintype_card, nsmul_eq_mul, Nat.cast_id]
  have hsplit : (∑ w : ↥(Subgroup.center P), Nat.card {x : P // x ^ 2 = (w : P)})
      = Nat.card ↥(Subgroup.center P) +
        (Nat.card ↥(Subgroup.center P) - 1) * Nat.card {x : P // x ^ 2 = z} := by
    have h1 := Finset.sum_erase_add (Finset.univ : Finset ↥(Subgroup.center P))
      (fun w : ↥(Subgroup.center P) => Nat.card {x : P // x ^ 2 = (w : P)})
      (Finset.mem_univ (1 : ↥(Subgroup.center P)))
    rw [← h1, hF1, herase, Nat.add_comm]
  have hmain : Nat.card ↥(Subgroup.center P) ^ 2
      = Nat.card ↥(Subgroup.center P) +
        (Nat.card ↥(Subgroup.center P) - 1) * Nat.card {x : P // x ^ 2 = z} := by
    rw [← hcard, hsum, hsplit]
  -- The centre has at least two elements (`1` and `z`), so `q - 1 ≠ 0` and we may cancel.
  have hd : Nat.card ↥(Subgroup.center P) - 1 ≠ 0 := by
    have hZne1 : Nat.card ↥(Subgroup.center P) ≠ 1 := by
      intro h
      have hsub : Subsingleton ↥(Subgroup.center P) := (Nat.card_eq_one_iff_unique.mp h).1
      exact hz1 (congrArg Subtype.val
        (Subsingleton.elim (⟨z, hz⟩ : ↥(Subgroup.center P)) ⟨1, Subgroup.one_mem _⟩))
    have hZne0 : Nat.card ↥(Subgroup.center P) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
    omega
  have h3 : (Nat.card ↥(Subgroup.center P) - 1) * Nat.card ↥(Subgroup.center P)
      = Nat.card ↥(Subgroup.center P) ^ 2 - Nat.card ↥(Subgroup.center P) := by
    rw [Nat.sub_mul, one_mul, ← pow_two]
  have h2 : Nat.card ↥(Subgroup.center P) ^ 2
      = (Nat.card ↥(Subgroup.center P) - 1) * Nat.card {x : P // x ^ 2 = z} +
        Nat.card ↥(Subgroup.center P) := by
    rw [hmain, Nat.add_comm]
  have h4 : Nat.card ↥(Subgroup.center P) ^ 2 - Nat.card ↥(Subgroup.center P)
      = (Nat.card ↥(Subgroup.center P) - 1) * Nat.card {x : P // x ^ 2 = z} := by
    rw [h2, Nat.add_sub_cancel]
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hd) (by rw [h3, h4])

end Work.PSU3.StageA
