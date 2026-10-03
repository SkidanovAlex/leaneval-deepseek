/-
# A potential `τ` for a balanced `ℤ`-labelling

Given a balanced labelling `L` of a graph `Γ` (`L (e⁻¹) = -L e`), we build a function
`τ : E(Γ) → ℤ` with

`τ (e⁻¹) = τ e - L e`.

Such a `τ` exists because the reversal involution `e ↦ e⁻¹` is a fixed-point-free
involution, so its orbits are the pairs `{e, e⁻¹}`; choosing a representative `c e` of
each orbit and setting `τ e = 0` on representatives, `τ e = L e` on the others, gives a
function satisfying the relation.  (When `e` is a fixed point of reversal — a possibility
excluded by the hypothesis `hns` — balancedness forces `L e = 0`, so the construction
still works; the hypothesis is not needed for the proof.)
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverGraph

open Classical

namespace Work.ORLocInd.Howie

open Quiver

universe u

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- The orbit relation of the reversal involution: `f` is `e` or its reverse. -/
private def orbRel (e f : Quiver.Total V) : Prop := f = e ∨ f = Quiver.totalReverse e

private theorem orbRel_refl (e : Quiver.Total V) : orbRel e e := Or.inl rfl

private theorem orbRel_symm {e f : Quiver.Total V} (h : orbRel e f) : orbRel f e := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    rw [h, Quiver.totalReverse_involutive]

private theorem orbRel_trans {e f g : Quiver.Total V} (h1 : orbRel e f) (h2 : orbRel f g) :
    orbRel e g := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left;  rw [h2, h1]
  · right; rw [h2, h1]
  · right; rw [h2, h1]
  · left;  rw [h2, h1, Quiver.totalReverse_involutive]

/-- The setoid of orbits of the reversal involution. -/
private def orbSetoid : Setoid (Quiver.Total V) where
  r := orbRel
  iseqv := ⟨orbRel_refl, fun h => orbRel_symm h, fun h1 h2 => orbRel_trans h1 h2⟩

/-- A chosen representative `c e` of the reversal-orbit of `e`. -/
private noncomputable def orbRep (e : Quiver.Total V) : Quiver.Total V :=
  Quotient.out (Quotient.mk orbSetoid e)

/-- The representative lies in the orbit of `e`. -/
private theorem orbRep_mem (e : Quiver.Total V) :
    orbRep e = e ∨ orbRep e = Quiver.totalReverse e := by
  have h : orbRel (orbRep e) e := Quotient.mk_out (s := orbSetoid) e
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    have h' : Quiver.totalReverse e = orbRep e := by
      have hc := congrArg Quiver.totalReverse h
      rwa [Quiver.totalReverse_involutive] at hc
    exact h'.symm

/-- The representative is constant on orbits. -/
private theorem orbRep_totalReverse (e : Quiver.Total V) :
    orbRep (Quiver.totalReverse e) = orbRep e := by
  have h : Quotient.mk orbSetoid (Quiver.totalReverse e) = Quotient.mk orbSetoid e :=
    Quotient.sound (by right; exact (Quiver.totalReverse_involutive e).symm)
  exact congrArg Quotient.out h

/-- A potential `τ` for the labelling `L`: zero on the chosen representatives, `L e` on the
other half of each reversal orbit. -/
private noncomputable def tau (L : Labelling V) (e : Quiver.Total V) : ℤ :=
  if orbRep e = e then 0 else L.toFun e

private theorem tau_totalReverse (L : Labelling V) (e : Quiver.Total V) :
    tau L (Quiver.totalReverse e) = tau L e - L.toFun e := by
  unfold tau
  rw [orbRep_totalReverse]
  by_cases h : orbRep e = e
  · rw [if_pos h, h]
    by_cases he : e = Quiver.totalReverse e
    · rw [if_pos he]
      have hb : L.toFun e = -L.toFun e := by
        have := L.balanced e
        rwa [← he] at this
      omega
    · rw [if_neg he, L.balanced e]
      ring
  · rw [if_neg h]
    rcases orbRep_mem e with hm | hm
    · exact absurd hm h
    · rw [if_pos hm]
      ring

theorem exists_tau {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (L : Work.ORLocInd.Howie.Labelling V)
    (hns : ∀ (a : V) (e : a ⟶ a), Quiver.reverse e ≠ e) :
    ∃ τ : Quiver.Total V → ℤ, ∀ e : Quiver.Total V,
      τ (Quiver.totalReverse e) = τ e - L.toFun e :=
  ⟨tau L, tau_totalReverse L⟩

end Work.ORLocInd.Howie
