import Mathlib
import Submission.Work.A7F.Defs

open scoped MatrixGroups

namespace Work.A7F

open Subgroup

/-- The cycle type of the double transposition `(0 1)(2 3)` of `S₇`. -/
theorem cycleType_a7InvolPerm :
    Work.A7.a7InvolPerm.cycleType = ({2, 2} : Multiset ℕ) := by
  have h := Equiv.Perm.cycleType_swap_mul_swap_of_nodup
    (α := Fin 7) (x := 0) (y := 1) (z := 2) (t := 3) (by decide)
  simpa [Work.A7.a7InvolPerm] using h

/-- The centralizer of `(0 1)(2 3)` in `S₇` has order `48`. -/
theorem card_centralizer_a7InvolPerm :
    Nat.card (Subgroup.centralizer ({Work.A7.a7InvolPerm} : Set (Equiv.Perm (Fin 7)))) = 48 := by
  rw [Equiv.Perm.nat_card_centralizer, cycleType_a7InvolPerm]
  decide

/-- The centralizer of `a7Invol` in `A₇` is the `comap` of its centralizer in `S₇` along the
inclusion `A₇ → S₇`. -/
theorem centralizer_a7Invol_eq_comap :
    Subgroup.centralizer ({a7Invol} : Set (alternatingGroup (Fin 7))) =
      (Subgroup.centralizer ({Work.A7.a7InvolPerm} : Set (Equiv.Perm (Fin 7)))).comap
        (alternatingGroup (Fin 7)).subtype := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_comap,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg (Subtype.val) h
    simpa [Work.A7.coe_a7Invol] using h'
  · intro h
    apply Subtype.ext
    simpa [Work.A7.coe_a7Invol] using h

/-- `Nat.card` of the `comap` of the centralizer in `S₇` equals `Nat.card` of the intersection of
that centralizer with `A₇`. -/
theorem card_centralizer_a7Invol_comap :
    Nat.card ↥((Subgroup.centralizer ({Work.A7.a7InvolPerm} : Set (Equiv.Perm (Fin 7)))).comap
        (alternatingGroup (Fin 7)).subtype)
      = Nat.card ↥((alternatingGroup (Fin 7)) ⊓
          Subgroup.centralizer ({Work.A7.a7InvolPerm} : Set (Equiv.Perm (Fin 7)))) := by
  rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective (alternatingGroup (Fin 7)))]
  rw [Subgroup.map_comap_eq, Subgroup.range_subtype]

/-- The intersection of `A₇` with the centralizer of `(0 1)(2 3)` in `S₇` has order `24`. -/
theorem card_inf_centralizer_a7InvolPerm :
    Nat.card ↥((alternatingGroup (Fin 7)) ⊓
        Subgroup.centralizer ({Work.A7.a7InvolPerm} : Set (Equiv.Perm (Fin 7)))) = 24 := by
  have hcard : Nat.card (Subgroup.centralizer ({Work.A7.a7InvolPerm} : Set (Equiv.Perm (Fin 7))))
      = 48 := card_centralizer_a7InvolPerm
  have hrel : (alternatingGroup (Fin 7)).relIndex
      (Subgroup.centralizer ({Work.A7.a7InvolPerm} : Set (Equiv.Perm (Fin 7)))) = 2 := by
    -- The intersection with `A₇` is the kernel of the sign homomorphism restricted to the
    -- centralizer of `(0 1)(2 3)` in `S₇`; the latter contains the odd element `(0 1)`.
    set C : Subgroup (Equiv.Perm (Fin 7)) :=
      Subgroup.centralizer ({Work.A7.a7InvolPerm} : Set (Equiv.Perm (Fin 7))) with hC
    have hker : (alternatingGroup (Fin 7)).subgroupOf C =
        (Equiv.Perm.sign.comp C.subtype).ker := by
      ext x
      simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply,
        Subgroup.coe_subtype, Equiv.Perm.mem_alternatingGroup]
    show ((alternatingGroup (Fin 7)).subgroupOf C).index = 2
    rw [hker, Subgroup.index_ker]
    have hrange : (Equiv.Perm.sign.comp C.subtype).range = ⊤ := by
      rw [eq_top_iff]
      intro u _
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact ⟨1, map_one _⟩
      · refine ⟨⟨Equiv.swap 0 1, ?_⟩, ?_⟩
        · rw [hC, Subgroup.mem_centralizer_singleton_iff]; decide
        · simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
          exact Equiv.Perm.sign_swap (by decide)
    rw [hrange, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have h := Subgroup.relIndex_mul_card (alternatingGroup (Fin 7))
    (Subgroup.centralizer ({Work.A7.a7InvolPerm} : Set (Equiv.Perm (Fin 7))))
  rw [hrel, hcard] at h
  omega

/-- The centralizer of the model involution `(0 1)(2 3)` in `A₇` has order `24`. -/
theorem card_centralizer_a7Invol :
    Nat.card (Subgroup.centralizer ({a7Invol} : Set (alternatingGroup (Fin 7)))) = 24 := by
  rw [centralizer_a7Invol_eq_comap, card_centralizer_a7Invol_comap]
  exact card_inf_centralizer_a7InvolPerm

end Work.A7F
