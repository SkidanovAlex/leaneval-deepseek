import Mathlib
import Submission.Work.BG.orbitCardAux
import Submission.Work.BG.L33DDefs

/-!
# `Work.BG.ocm.card_inertia_inf_S0_eq`

The `S₀`-part of the inertia group of a class function `a` of `U = O(H)` can be computed
either inside `H₀` (as `I_{H₀}(a) ⊓ S₀`) or inside the Sylow `2`-subgroup `S`
(as `S₀ ⊓ S_a`): the two subgroups have the same cardinality.  This is the elementary
transport between the two models of the same action (the conjugation action of `S₀` on the
class functions of `U`), used to compare the orbit–stabiliser counts in the two groups.

The bridge is `conjBy_eq_compHom_phiS`: for `x ∈ H₀` whose underlying `G`-element lies in
`S`, conjugating a class function of `U ⊆ H₀` by `x` inside `H₀` is the same as composing
with `φS x`, the conjugation action of `S` used to define `sStab`.
-/

namespace Work.BG.ocm

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G]

/-- `S₀ ≤ H₀ = U S₀`, so `S₀` can be viewed inside `H₀`. -/
theorem S0_le_H0 (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C) : D.S0 ≤ C.P.H0 := by
  rw [hDC.H0_eq]
  exact le_sup_right

/-- Conjugation of a class function of `U` by an element `x ∈ H₀` whose underlying
`G`-element lies in `S` agrees with the action `φS` of `S` on `U`. -/
theorem conjBy_eq_compHom_phiS (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (x : ↥C.P.H0) (hx : (x : G) ∈ (D.S : Subgroup G)) (a : ClassFunction ↥(Uin C) ℂ) :
    ClassFunction.conjBy (G := ↥C.P.H0) (H := Uin C) x a
      = ClassFunction.compHom (L33D.phiS D C hDC ⟨(x : G), hx⟩).toMonoidHom a := by
  ext u
  rw [ClassFunction.conjBy_apply, ClassFunction.compHom_apply]
  congr 1

/-- For `x ∈ H₀` with `(x : G) ∈ S`: `x` lies in the inertia group of `a` inside `H₀`
if and only if the corresponding element of `S` lies in the stabilizer `sStab`. -/
theorem mem_inertia_iff_mem_sStab (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (a : ClassFunction ↥(Uin C) ℂ) (x : ↥C.P.H0) (hx : (x : G) ∈ (D.S : Subgroup G)) :
    x ∈ ClassFunction.inertia (G := ↥C.P.H0) (H := Uin C) a ↔
      (⟨(x : G), hx⟩ : ↥(D.S : Subgroup G)) ∈ sStab D C hDC a := by
  rw [ClassFunction.mem_inertia (H := Uin C) (G := ↥C.P.H0) (θ := a) (g := x),
    mem_sStab D C hDC a ⟨(x : G), hx⟩]
  constructor
  · intro h
    exact (conjBy_eq_compHom_phiS D C hDC x hx a).symm.trans h
  · intro h
    exact (conjBy_eq_compHom_phiS D C hDC x hx a).trans h

theorem card_inertia_inf_S0_eq {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hDC : Work.GW2.C16.Compat D C)
    [Fintype ↥C.P.H0] [Fintype ↥(Work.GW2.C16.Uin C)]
    [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) :
    Nat.card ↥(OddOrder.RepresentationTheory.ClassFunction.inertia (G := ↥C.P.H0)
        (H := Work.GW2.C16.Uin C) a ⊓ Work.BG.S0in D C hDC)
      = Nat.card ↥(Work.BG.S0sub D ⊓ Work.BG.sStab D C hDC a) := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun y =>
        ⟨⟨(y.1 : G), D.S0_le ((mem_S0in D C hDC y.1).mp (Subgroup.mem_inf.mp y.2).2)⟩,
          ⟨(mem_S0sub D _).mpr ((mem_S0in D C hDC y.1).mp (Subgroup.mem_inf.mp y.2).2),
            (mem_inertia_iff_mem_sStab D C hDC a y.1
                (D.S0_le ((mem_S0in D C hDC y.1).mp (Subgroup.mem_inf.mp y.2).2))).mp
              (Subgroup.mem_inf.mp y.2).1⟩⟩
      invFun := fun s => by
        let x : ↥C.P.H0 :=
          ⟨(s.1 : G), S0_le_H0 D C hDC ((mem_S0sub D s.1).mp (Subgroup.mem_inf.mp s.2).1)⟩
        have hmem : (s.1 : G) ∈ D.S0 := (mem_S0sub D s.1).mp (Subgroup.mem_inf.mp s.2).1
        have hstab : (⟨(x : G), D.S0_le hmem⟩ : ↥(D.S : Subgroup G)) ∈ sStab D C hDC a := by
          have heq : (⟨(x : G), D.S0_le hmem⟩ : ↥(D.S : Subgroup G)) = s.1 := Subtype.ext rfl
          rw [heq]
          exact (Subgroup.mem_inf.mp s.2).2
        exact ⟨x, ⟨(mem_inertia_iff_mem_sStab D C hDC a x (D.S0_le hmem)).mpr hstab,
          (mem_S0in D C hDC x).mpr hmem⟩⟩
      left_inv := fun y => Subtype.ext (Subtype.ext rfl)
      right_inv := fun s => Subtype.ext (Subtype.ext rfl) }

end Work.BG.ocm
