import Mathlib
import Submission.Work.ThmF.Bender.cardInvertedMulCardCentralizer
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `V = C_D(t) = 1` forces `K = J(D,t) = D`

Peterfalvi II, Ch. VII §1 (the Zassenhaus case): in the split rank-one situation
`H = Q ⋊ D`, `D = H ∩ Hᵗ = twoPoint H t`, with `t ∉ H` an involution, if the centraliser
`V = C_D(t) = centD H t` is trivial then `t` inverts every element of `D`, i.e. the set

`K = J(D,t) = invertedBy (twoPoint H t) t = {x ∈ D | t x t⁻¹ = x⁻¹}`

is all of `D = twoPoint H t`.

The argument is the elementary one.  Since `t` is an involution and `D = H ⊓ Hᵗ`, conjugation
by `t` preserves `D` (it swaps the two factors), and it is an involutive automorphism of `D`.
The hypothesis `C_D(t) = 1` says exactly that this automorphism is fixed point free.  A
fixed-point-free involutive automorphism of a finite group inverts every element: the map

`φ : D → D,  x ↦ x⁻¹ · (t x t⁻¹)`

is injective — if `φ x = φ y`, multiplying the resulting identity on the left by `y` and on the
right by `(t x t⁻¹)⁻¹` gives `y x⁻¹ = (t y t⁻¹)(t x t⁻¹)⁻¹ = t (y x⁻¹) t⁻¹`, so
`y x⁻¹ ∈ C_D(t) = 1` and `x = y` — hence bijective (`D` is finite), and for a preimage `y` of `x`
one computes `t x t⁻¹ = (t y⁻¹ t⁻¹)·t (t y t⁻¹) t⁻¹ = (t y t⁻¹)⁻¹ · y = (y⁻¹ · t y t⁻¹)⁻¹ =
x⁻¹`, using `t² = 1` for `t (t y t⁻¹) t⁻¹ = y`.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs

namespace Work.BSIntegrate.Count

/-- **Fixed-point-free involutive automorphisms invert.**  If the involution `t` normalises a
finite subgroup `D` and `C_D(t) = D ⊓ C_G(t) = ⊥`, then `t x t⁻¹ = x⁻¹` for every `x ∈ D`. -/
theorem conj_eq_inv_of_inf_centralizer_eq_bot {G : Type*} [Group G] [Finite G]
    {D : Subgroup G} {t : G} (htt : t * t = 1)
    (hN : ∀ x ∈ D, t * x * t⁻¹ ∈ D)
    (hC : D ⊓ Subgroup.centralizer ({t} : Set G) = ⊥) :
    ∀ x ∈ D, t * x * t⁻¹ = x⁻¹ := by
  classical
  -- an element of `D` fixed by conjugation by `t` is trivial
  have hfix : ∀ x ∈ D, t * x * t⁻¹ = x → x = 1 := by
    intro x hx hxx
    have h5 : x * t = t * x := by
      have h4 : t * x * t⁻¹ * t = t * x := by group
      have h6 := congrArg (fun z : G => z * t) hxx
      rw [h4] at h6
      exact h6.symm
    have hmem : x ∈ D ⊓ Subgroup.centralizer ({t} : Set G) :=
      ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr h5⟩
    rw [hC] at hmem
    simpa using hmem
  -- `φ x = x⁻¹ * (t x t⁻¹)` is injective on `D`
  have hinj : Function.Injective
      (fun x : ↥D => x⁻¹ * (⟨t * (x : G) * t⁻¹, hN x x.2⟩ : ↥D)) := by
    intro x y hxy
    have h : (x : G)⁻¹ * (t * (x : G) * t⁻¹) = (y : G)⁻¹ * (t * (y : G) * t⁻¹) :=
      congrArg Subtype.val hxy
    have h2 : (y : G) * (x : G)⁻¹
        = (t * (y : G) * t⁻¹) * (t * (x : G) * t⁻¹)⁻¹ := by
      have hy : (y : G) * ((x : G)⁻¹ * (t * (x : G) * t⁻¹)) = t * (y : G) * t⁻¹ := by
        rw [h]; group
      calc (y : G) * (x : G)⁻¹
          = ((y : G) * ((x : G)⁻¹ * (t * (x : G) * t⁻¹))) * (t * (x : G) * t⁻¹)⁻¹ := by
            group
        _ = (t * (y : G) * t⁻¹) * (t * (x : G) * t⁻¹)⁻¹ := by rw [hy]
    have hkey : t * ((y : G) * (x : G)⁻¹) * t⁻¹ = (y : G) * (x : G)⁻¹ := by
      calc t * ((y : G) * (x : G)⁻¹) * t⁻¹
          = (t * (y : G) * t⁻¹) * (t * (x : G) * t⁻¹)⁻¹ := by group
        _ = (y : G) * (x : G)⁻¹ := h2.symm
    have hone : (y : G) * (x : G)⁻¹ = 1 :=
      hfix _ (D.mul_mem y.2 (D.inv_mem x.2)) hkey
    exact Subtype.ext (mul_inv_eq_one.mp hone).symm
  have hsurj : Function.Surjective
      (fun x : ↥D => x⁻¹ * (⟨t * (x : G) * t⁻¹, hN x x.2⟩ : ↥D)) :=
    Finite.surjective_of_injective hinj
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  have hyval : (y : G)⁻¹ * (t * (y : G) * t⁻¹) = x := congrArg Subtype.val hy
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hty : t * (t * (y : G) * t⁻¹) * t⁻¹ = (y : G) := by
    have h1 : t * (t * (y : G) * t⁻¹) * t⁻¹ = (t * t) * (y : G) * (t⁻¹ * t⁻¹) := by group
    rw [h1, htt, hti, htt]
    group
  rw [← hyval]
  calc t * ((y : G)⁻¹ * (t * (y : G) * t⁻¹)) * t⁻¹
      = (t * (y : G)⁻¹ * t⁻¹) * (t * (t * (y : G) * t⁻¹) * t⁻¹) := by group
    _ = (t * (y : G) * t⁻¹)⁻¹ * (y : G) := by
          rw [hty, show t * (y : G)⁻¹ * t⁻¹ = (t * (y : G) * t⁻¹)⁻¹ from by group]
    _ = ((y : G)⁻¹ * (t * (y : G) * t⁻¹))⁻¹ := by group

/-- **`K = D` when `V = 1`.**  In a split rank-one group with `V = C_D(t) = centD H t = ⊥`,
every element of `D = twoPoint H t` is inverted by `t`. -/
theorem Kset_eq_twoPoint_of_centD_eq_bot {G : Type*} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hV : Submission.Blueprint.centD H t = ⊥) :
    Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t
      = (Submission.Blueprint.twoPoint H t : Set G) := by
  classical
  have htt : t * t = 1 := by
    have h2 := pow_orderOf_eq_one t
    rw [h.invol, pow_two] at h2
    exact h2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  -- conjugation by `t` preserves `D = H ⊓ Hᵗ` (it swaps the two factors)
  have hN : ∀ x ∈ Submission.Blueprint.twoPoint H t,
      t * x * t⁻¹ ∈ Submission.Blueprint.twoPoint H t := by
    intro x hx
    have hxH : x ∈ H := (Work.Models.mem_twoPoint_iff.mp hx).1
    have hxtH : t⁻¹ * x * t ∈ H := (Work.Models.mem_twoPoint_iff.mp hx).2
    rw [Work.Models.mem_twoPoint_iff]
    refine ⟨?_, ?_⟩
    · rw [hti] at hxtH; rw [hti]; exact hxtH
    · rw [show t⁻¹ * (t * x * t⁻¹) * t = x from by group]; exact hxH
  have hmain := conj_eq_inv_of_inf_centralizer_eq_bot
    (D := Submission.Blueprint.twoPoint H t) htt hN hV
  ext x
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, hmain x hx⟩⟩

end Work.BSIntegrate.Count
