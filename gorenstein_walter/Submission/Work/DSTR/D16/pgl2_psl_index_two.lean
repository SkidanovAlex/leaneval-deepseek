import Mathlib
import Submission.Work.CORE2A.card_PGL2_eq_two_mul_card_PSL2

/-!
# `[PGL(2,q) : PSL(2,q)] = 2` and `PGL(2,q)' = PSL(2,q)` for odd `q ≥ 5`

Let `F` be a finite field of odd characteristic with `4 ≤ |F|` and put
`G = PGL(2,F)`, `P = SL(2,F)·Z(GL(2,F))/Z(GL(2,F))` (the image of `SL(2,F)`), so that
`P ≅ PSL(2,F)`.

* `MonoidHom.rangeRestrict` realises `P` as a quotient of `SL(2,F)`, whence `P` is perfect
  whenever `SL(2,F)` is, i.e. whenever there is `a ∈ F` with `a ≠ 0` and `a² ≠ 1`
  (Mathlib's `Matrix.SL2.commutator_eq_top`); such an `a` exists as soon as `|F| ≥ 4`.
  Hence `P ≤ ⁅G,G⁆`.
* `|PGL(2,F)| = 2 |PSL(2,F)| = 2 |P|` (`Work.CORE2A.card_PGL2_eq_two_mul_card_PSL2` and the
  isomorphism `P ≅ PSL(2,F)`), so `[G : P] = 2`; a subgroup of index two is normal and contains
  the commutator subgroup, whence `⁅G,G⁆ ≤ P`.

Combining, `P` is a normal subgroup of index two isomorphic to `PSL(2,F)` and equal to the
commutator subgroup of `PGL(2,F)`; specialising to `F = GF(p^k)`, `p` odd, `p^k ≥ 5` gives the
statement needed in the Gorenstein–Walter analysis of the `D₁₆` case.
-/

open scoped MatrixGroups
open Matrix

namespace Work.DSTR.D16

open scoped commutatorElement

section GroupTools

variable {G : Type*} [Group G]

/-- A perfect subgroup of a group is contained in the commutator subgroup. -/
theorem le_commutator_of_isPerfect (H : Subgroup G) [Group.IsPerfect H] : H ≤ commutator G := by
  rw [← Subgroup.commutator_eq_self (H := H)]
  exact Subgroup.commutator_mono le_top le_top

/-- In a group, a subgroup of index two contains the commutator subgroup. -/
theorem commutator_le_of_index_eq_two (H : Subgroup G) (hH : H.index = 2) : commutator G ≤ H := by
  have hN : H.Normal := Subgroup.normal_of_index_eq_two hH
  -- the product of two elements outside `H` lies in `H`
  have hmul : ∀ x y : G, x ∉ H → y ∉ H → x * y ∈ H := fun x y hx hy =>
    (Subgroup.mul_mem_iff_of_index_two hH).mpr (iff_of_false hx hy)
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  -- `⁅a,b⁆ = (a*b) * (b*a)⁻¹` and `a*b`, `b*a` lie in `H` simultaneously
  have key : a * b * (b * a)⁻¹ ∈ H := by
    by_cases hab : a * b ∈ H
    · have hba : b * a ∈ H := by
        have h := hN.conj_mem (a * b) hab a⁻¹
        rwa [show a⁻¹ * (a * b) * a⁻¹⁻¹ = b * a by group] at h
      exact mul_mem hab (inv_mem hba)
    · have hba : b * a ∉ H := fun hconj => hab (by
        have h := hN.conj_mem (b * a) hconj a
        rwa [show a * (b * a) * a⁻¹ = a * b by group] at h)
      exact hmul _ _ hab (fun h => hba ((Subgroup.inv_mem_iff H).mp h))
  rw [commutatorElement_def]
  convert key using 1
  group

end GroupTools

section FieldTools

variable {F : Type*} [Field F]

/-- In a field with at least four elements there is an element `a` with `a ≠ 0` and `a ^ 2 ≠ 1`;
this is the hypothesis needed for `SL(2,F)` to be perfect. -/
theorem exists_ne_zero_sq_ne_one_of_four_le_card (hF : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  have hfin : Finite F := (Nat.card_pos_iff.1 (by omega)).2
  obtain ⟨x, hx⟩ : IsCyclic Fˣ := by infer_instance
  refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
  grw [Nat.card_eq_card_units_add_one F, ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at hF
  omega

end FieldTools

section Main

variable {F : Type*} [Field F] [Fintype F]

/-- The image of `SL(2,F)` in `PGL(2,F)` is isomorphic to `PSL(2,F)` (Noether's first
isomorphism theorem, using that the kernel of `SL(2,F) → PGL(2,F)` is the centre). -/
theorem range_toPGL_mulEquiv_PSL :
    Nonempty ((Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq
      (M := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
      (N := (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).ker)
      Matrix.SpecialLinearGroup.toPGL_ker.symm).trans
    (QuotientGroup.quotientKerEquivRange
      (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)))).symm⟩

/-- The image of `SL(2,F)` in `PGL(2,F)` has index two whenever `ringChar F ≠ 2`. -/
theorem index_range_toPGL (hchar : ringChar F ≠ 2) :
    (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.index = 2 := by
  set P : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F) :=
    (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range with hPdef
  haveI hfin : Finite ↥P := by
    rw [hPdef]
    exact Finite.of_surjective (MonoidHom.rangeRestrict _) (MonoidHom.rangeRestrict_surjective _)
  have hcardN : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = Nat.card ↥P :=
    Nat.card_congr (Classical.choice (range_toPGL_mulEquiv_PSL (F := F))).symm.toEquiv
  have hmain : Nat.card ↥P * P.index = Nat.card (Matrix.ProjGenLinGroup (Fin 2) F) :=
    Subgroup.card_mul_index P
  have hG : Nat.card (Matrix.ProjGenLinGroup (Fin 2) F) =
      2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
    rw [Work.CORE2A.card_PGL2_eq_card_SL2 (F := F),
      Work.CORE2A.card_SL2_eq_two_mul_card_PSL2 (F := F) hchar]
  have hpos : 0 < Nat.card ↥P := Nat.card_pos
  have h2 : Nat.card ↥P * P.index = Nat.card ↥P * 2 := by
    rw [hmain, hG, hcardN, mul_comm 2]
  exact Nat.eq_of_mul_eq_mul_left hpos h2

end Main

section Perfect

variable {F : Type*} [Field F]

/-- The image of `SL(2,F)` in `PGL(2,F)` is perfect when `F` has at least four elements. -/
theorem range_toPGL_le_commutator (hcard : 4 ≤ Nat.card F) :
    (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ≤
      commutator (Matrix.ProjGenLinGroup (Fin 2) F) := by
  obtain ⟨a, ha, ha2⟩ := exists_ne_zero_sq_ne_one_of_four_le_card (F := F) hcard
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨Matrix.SL2.commutator_eq_top ha ha2⟩
  haveI : Group.IsPerfect ↥(Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    Group.IsPerfect.ofSurjective (f := MonoidHom.rangeRestrict _)
      (MonoidHom.rangeRestrict_surjective _)
  exact le_commutator_of_isPerfect _

end Perfect

section Assembly

variable {F : Type*} [Field F] [Fintype F]

/-- The image of `SL(2,F)` in `PGL(2,F)` is the commutator subgroup of `PGL(2,F)`, for `F` a
finite field of odd characteristic with at least four elements. -/
theorem range_toPGL_eq_commutator (hchar : ringChar F ≠ 2) (hcard : 4 ≤ Nat.card F) :
    (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range =
      ⁅(⊤ : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)), ⊤⁆ := by
  refine le_antisymm (range_toPGL_le_commutator hcard) ?_
  simpa only [commutator_def] using
    commutator_le_of_index_eq_two _ (index_range_toPGL (F := F) hchar)

/-- `PGL(2,F)` has a normal subgroup of index two isomorphic to `PSL(2,F)`, namely the commutator
subgroup, for `F` a finite field of odd characteristic with at least four elements. -/
theorem pgl2_psl_index_two_aux (F : Type*) [Field F] [Fintype F] (hchar : ringChar F ≠ 2)
    (hcard : 4 ≤ Nat.card F) :
    ∃ P : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F),
      P.Normal ∧ P.index = 2 ∧
      Nonempty (P ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ∧
      P = ⁅(⊤ : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)), ⊤⁆ :=
  ⟨(Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range,
    Subgroup.normal_of_index_eq_two (index_range_toPGL hchar),
    index_range_toPGL hchar,
    range_toPGL_mulEquiv_PSL,
    range_toPGL_eq_commutator hchar hcard⟩

end Assembly

theorem pgl2_psl_index_two (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k) : ∃ P : Subgroup (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)), P.Normal ∧ P.index = 2 ∧ Nonempty (P ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ∧ P = ⁅(⊤ : Subgroup (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k))), ⊤⁆ := by
  have hk : k ≠ 0 := by
    intro h
    rw [h, pow_zero] at hq
    omega
  letI : Fintype (GaloisField p k) := Fintype.ofFinite _
  refine pgl2_psl_index_two_aux (GaloisField p k) ?_ ?_
  · rw [ringChar.eq (GaloisField p k) p]
    intro h
    obtain ⟨m, hm⟩ := hp
    omega
  · rw [GaloisField.card p k hk]
    omega

end Work.DSTR.D16
