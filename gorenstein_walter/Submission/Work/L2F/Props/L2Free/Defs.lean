/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# An `AUTL2`-free `ℙ¹`-model for the Gorenstein–Walter area

`Work.L2F.L2NormalizesTwoSylowProp` says: for `q = p^k` (`p` an odd prime, `q ≥ 5`), an odd prime
`r ≠ p` and a subgroup `Y ≤ L₂(q) = PSL(2,q)` of order `r`, the number of subgroups `Q ≤ L₂(q)`
of order `q` normalised by `Y` is at most `2`.

The existing proof (`Submission/Work/L2F/Props/L2NormalizesTwoSylow.lean`) goes through a `ℙ¹`
model that lives in `Submission/Work/AUTL2/`, whose `Work.GW2.IsFourGroup` clashes with the core
areas' copies.  This file provides the same model, built on Mathlib's own projectivisation
`ℙ F (Fin 2 → F)` together with the (Mathlib) action of `PSL(2,F)` on it, so that no import of
`Work.AUTL2` is needed.

The ingredients are

* the model itself: `P1 F`, the base point `inf F = [1:0]`, the stabilizer `pslStab x` of a point,
  the fixed-point set `fixSet g` of an element;
* the conjugacy formula `pslStab (g • x) = (pslStab x).map (MulAut.conj g)`;
* the transport of normalizers along automorphisms (`normalizer_map_mulAut`);
* two elementary counting lemmas for finite sets (`Finset.exists_three_mem`,
  `ncard_le_two_of_not_three`);
* the group-theoretical lemma `eq_of_normal_card_eq` (a subgroup of order `p ^ m` of a group whose
  `p`-part is `p ^ m`, containing a normal subgroup of order `p ^ m`, is that subgroup).

The mathematical inputs proved in the files next to this one are

* `Work.L2F.Props.L2Free.pslStab_inf_eq_normalizer`: the stabilizer of `[1:0]` is the Borel, i.e.
  the normalizer of the unipotent subgroup;
* `Work.L2F.Props.L2Free.ncard_fixSet_le_two`: a non-identity element of `PSL(2,F)` fixes at most
  two points of `ℙ¹(F)`;
* `Work.L2F.Props.L2Free.exists_conj_eq_pslUnipotent`: every subgroup of order `p ^ k = |F|` is a
  conjugate of the unipotent subgroup.
-/
import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.PSL2.Basic
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff
import Submission.Work.L2F.PSL.pslUnipotent_card
import Submission.Work.L2F.PSL.normalizer_pslUnipotent_card
import Submission.Work.L2F.PSL.pslMap_mem_normalizer_iff_mem_borel
import Submission.Work.L2F.Conic.mem_borel

open scoped MatrixGroups LinearAlgebra.Projectivization
open Matrix

namespace Work.L2F.Props.L2Free

variable (F : Type*) [Field F]

/-- The projective line over `F`, as the projectivisation of `F²`. -/
abbrev P1 : Type _ := ℙ F (Fin 2 → F)

/-- The point `[1:0]` of `ℙ¹(F)`, the point at infinity for the affine coordinate `x₀/x₁`. -/
def inf : P1 F := Work.PSL2.ptInf F

/-- The stabilizer of a point of the projective line, in `PSL(2,F)`. -/
noncomputable def pslStab (x : P1 F) : Subgroup (PSL(2, F)) :=
  MulAction.stabilizer (PSL(2, F)) x

/-- The set of points of `ℙ¹(F)` fixed by `g`. -/
noncomputable def fixSet (g : PSL(2, F)) : Set (P1 F) := {x | g • x = x}

theorem mem_pslStab_iff {x : P1 F} {g : PSL(2, F)} : g ∈ pslStab F x ↔ g • x = x :=
  MulAction.mem_stabilizer_iff

theorem mem_fixSet_iff {g : PSL(2, F)} {x : P1 F} : x ∈ fixSet F g ↔ g • x = x := Iff.rfl

/-- The action of `π A` (`A ∈ SL(2,F)`) on a point, in terms of the action on the representative. -/
theorem smul_mk_apply (A : SL(2, F)) (v : Fin 2 → F) (hv : v ≠ 0) :
    (A : PSL(2, F)) • Projectivization.mk F v hv
      = Projectivization.mk F (A • v) (smul_ne_zero_iff_ne A |>.mpr hv) := by
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,
    Projectivization.matrixSpecialLinearGroup_smul_def]
  exact Projectivization.smul_mk A hv

/-- The stabilizer of the image point is the conjugate subgroup. -/
theorem pslStab_smul_conj (g : PSL(2, F)) (x : P1 F) :
    pslStab F (g • x) = (pslStab F x).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g x

/-- Conjugating an element reverses the transport of fixed points:
`g h g⁻¹` fixes `x` exactly when `h` fixes `g⁻¹ x`. -/
theorem smul_mem_conj_iff (g h : PSL(2, F)) (x : P1 F) :
    (MulAut.conj g) h • x = x ↔ h • (g⁻¹ • x) = g⁻¹ • x := by
  rw [MulAut.conj_apply, mul_smul, mul_smul]
  constructor
  · intro hh
    have h2 := congrArg (fun z => g⁻¹ • z) hh
    rw [smul_smul, inv_mul_cancel, one_smul] at h2
    exact h2
  · intro hh
    rw [hh, smul_smul, mul_inv_cancel, one_smul]

/-- The normalizer of a subgroup is transported by a group automorphism. -/
theorem normalizer_map_mulAut {G : Type*} [Group G] (Q : Subgroup G) (f : MulAut G) :
    Subgroup.normalizer ((Q.map f.toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.normalizer (Q : Set G)).map f.toMonoidHom := by
  have hker : f.toMonoidHom.ker = ⊥ := by
    rw [MonoidHom.ker_eq_bot_iff]
    exact f.injective
  have hsurj : Function.Surjective f.toMonoidHom := f.surjective
  have h := Subgroup.comap_normalizer_eq_of_surjective (Q.map f.toMonoidHom)
    (f := f.toMonoidHom) hsurj
  rw [Subgroup.comap_map_eq, hker, sup_bot_eq] at h
  have hrange : f.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top_of_surjective _ hsurj
  rw [← h, Subgroup.map_comap_eq, hrange, top_inf_eq]

/-! ## Counting lemmas for finite sets -/

/-- A finset of cardinality at least `3` has three distinct elements. -/
theorem Finset.exists_three_mem {α : Type*} (s : Finset α) (h : 3 ≤ s.card) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
  have h1 : 0 < s.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp h1
  have h2 : 0 < (s.erase a).card := by
    rw [Finset.card_erase_of_mem ha]; omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp h2
  have h3 : 0 < ((s.erase a).erase b).card := by
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]; omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp h3
  have hb' : b ∈ s := Finset.mem_of_mem_erase hb
  have hc' : c ∈ s := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
  have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hc)).1
  exact ⟨a, ha, b, hb', c, hc', hba.symm, hca.symm, hcb.symm⟩

/-- A set with no three distinct elements has at most two elements. -/
theorem ncard_le_two_of_not_three {α : Type*} (s : Set α)
    (h : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ b → a ≠ c → b ≠ c → False) : s.ncard ≤ 2 := by
  classical
  by_cases hfin : s.Finite
  · by_contra hle
    have h3 : 3 ≤ s.ncard := by omega
    have h5 : 3 ≤ hfin.toFinset.card := by
      rw [← Set.ncard_eq_toFinset_card s hfin]
      omega
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.exists_three_mem hfin.toFinset h5
    exact h a (hfin.mem_toFinset.mp ha) b (hfin.mem_toFinset.mp hb) c (hfin.mem_toFinset.mp hc)
      hab hac hbc
  · rw [Set.Infinite.ncard hfin]
    norm_num

/-! ## A subgroup of full `p`-part containing a normal subgroup of the same order -/

/-- A subgroup of order `p ^ m` of a group `N` whose `p`-part is `p ^ m`, containing a normal
subgroup `P` of order `p ^ m`, equals `P`. -/
theorem eq_of_normal_card_eq {G : Type*} [Group G] [Finite G] {p m c : ℕ} [Fact p.Prime]
    {P Q N : Subgroup G} (hPN : P ≤ N) (hQN : Q ≤ N)
    (hnorm : N ≤ Subgroup.normalizer (P : Set G))
    (hPcard : Nat.card P = p ^ m) (hQcard : Nat.card Q = p ^ m)
    (hNcard : Nat.card N = p ^ m * c) (hc : ¬ p ∣ c) : Q = P := by
  have hP : IsPGroup p P := IsPGroup.of_card hPcard
  have hQ : IsPGroup p Q := IsPGroup.of_card hQcard
  have hsup : IsPGroup p (P ⊔ Q : Subgroup G) := hP.to_sup_of_normal_left' hQ (hQN.trans hnorm)
  have hdvdN : Nat.card (P ⊔ Q : Subgroup G) ∣ Nat.card N := by
    have hle : (P ⊔ Q : Subgroup G) ≤ N := sup_le hPN hQN
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact Subgroup.card_subgroup_dvd_card ((P ⊔ Q).subgroupOf N)
  have hle1 : Nat.card P ≤ Nat.card (P ⊔ Q : Subgroup G) :=
    Subgroup.card_le_of_le (le_sup_left : P ≤ P ⊔ Q)
  obtain ⟨j, hj⟩ : ∃ j, Nat.card (P ⊔ Q : Subgroup G) = p ^ j := IsPGroup.iff_card.mp hsup
  have hpm_le : p ^ m ≤ p ^ j := by
    rw [← hPcard, ← hj]
    exact hle1
  have hdvd : p ^ j ∣ p ^ m * c := by
    rw [← hj, ← hNcard]
    exact hdvdN
  have hcop : Nat.Coprime (p ^ j) c :=
    (Nat.Prime.coprime_pow_of_not_dvd (m := j) Fact.out hc).symm
  have hdvd' : p ^ j ∣ p ^ m := hcop.dvd_of_dvd_mul_right hdvd
  have hj_le : j ≤ m := (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hdvd'
  have hjeq : p ^ j = p ^ m := le_antisymm (Nat.pow_le_pow_right (Fact.out : p.Prime).one_le hj_le)
    hpm_le
  have hsup_eq : (P ⊔ Q : Subgroup G) = P := by
    refine (Subgroup.eq_of_le_of_card_ge (H := P) (K := P ⊔ Q) le_sup_left ?_).symm
    rw [hj, hjeq, ← hPcard]
  exact Subgroup.eq_of_le_of_card_ge (H := Q) (K := P)
    (show Q ≤ P from hsup_eq ▸ le_sup_right) (by rw [hQcard, hPcard])

end Work.L2F.Props.L2Free
