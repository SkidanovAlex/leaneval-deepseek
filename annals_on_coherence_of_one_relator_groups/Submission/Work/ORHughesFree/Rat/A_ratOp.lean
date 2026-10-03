import Mathlib
import Submission.Work.ORHughesFree.Rat.exists_source_subgroup_weak
import Submission.Work.ORHughesFree.Rat.exists_source_fg
import Submission.Work.ORHughesFree.RatU.exists_decomp
import Submission.Work.Rat.ofGroup_mem_A
import Submission.Work.Rat.ratOp_eq_mul_group
import Submission.Work.Rat.ratOp_injective

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree

variable {U : Type} [Group U]

/-- `RatU.ratOp` and the field `RatU.rational.ratOp` are the same operation (they are equal by
`rfl`); this bridge is used to pass between the two notations. -/
theorem ratOp_eq_rational (z : RatU U) :
    RatU.ratOp z = (RatU.rational (U := U)).ratOp z := rfl

/-! ## Elementary closure properties of `A V`

`A V = Set.range (RatU.ofSubgroup V)`, and `RatU.ofSubgroup V : RatU ↥V →+* RatU U` is a ring
homomorphism, so `A V` is closed under `+` and `*` and contains the image of `V`. -/

theorem A_add {V : Subgroup U} {x y : RatU U} (hx : x ∈ A V) (hy : y ∈ A V) : x + y ∈ A V := by
  obtain ⟨β, rfl⟩ := hx
  obtain ⟨γ, rfl⟩ := hy
  exact ⟨β + γ, map_add (RatU.ofSubgroup V) β γ⟩

theorem A_mul {V : Subgroup U} {x y : RatU U} (hx : x ∈ A V) (hy : y ∈ A V) : x * y ∈ A V := by
  obtain ⟨β, rfl⟩ := hx
  obtain ⟨γ, rfl⟩ := hy
  exact ⟨β * γ, map_mul (RatU.ofSubgroup V) β γ⟩

theorem A_ofGroup_mem {V : Subgroup U} {u : U} (hu : u ∈ V) : RatU.ofGroup u ∈ A V :=
  ⟨RatU.ofGroup ⟨u, hu⟩, ofSubgroup_ofGroup V ⟨u, hu⟩⟩

/-! ## Two elementary facts about the rational operation -/

/-- A `⋄`-value is never `0` (its complexity is a double root extension). -/
theorem ratOp_ne_zero {z : RatU U} (hz : z ≠ 0) : RatU.ratOp z ≠ 0 := by
  intro h
  have h1 : Rat.treeOfRat U (RatU.ratOp z) = 0 := by rw [h, Rat.treeOfRat_zero]
  rw [ratOp_eq_rational] at h1
  rw [Rat.treeOfRat_rat_rational hz] at h1
  exact Tree.exp_ne_zero _ h1

/-- A `⋄`-value is never `1` (that would make its complexity the one-edge tree). -/
theorem ratOp_ne_one (z : RatU U) : RatU.ratOp z ≠ 1 := by
  intro h
  have h1 : Rat.treeOfRat U (RatU.ratOp z) = 1 := by rw [h, Rat.treeOfRat_one]
  rw [ratOp_eq_rational] at h1
  by_cases hz : z = 0
  · rw [hz, show (RatU.rational (U := U)).ratOp 0 = 0 from RatU.ratOp_zero,
      Rat.treeOfRat_zero] at h1
    exact Tree.one_ne_zero h1.symm
  · rw [Rat.treeOfRat_rat_rational hz] at h1
    have h2 : Tree.exp (Rat.treeOfRat U z) = 0 := (Tree.exp_eq_one_iff _).mp h1
    exact Tree.exp_ne_zero _ h2

/-- **Additive indecomposability of `⋄`**: a `⋄`-value is not a sum of two non-zero elements.
In the DHS04 model `ℕ[U ♮ X]` this is the statement that `⋄z` is a single *word*. -/
theorem ratOp_add_indecomp (z a b : RatU U) (h : RatU.ratOp z = a + b) : a = 0 ∨ b = 0 := by
  by_cases hz : z = 0
  · rw [hz, RatU.ratOp_zero] at h
    have h0 : Rat.treeOfRat U a + Rat.treeOfRat U b = 0 := by
      rw [← Rat.treeOfRat_add, ← h, Rat.treeOfRat_zero]
    obtain ⟨ha, hb⟩ := (Tree.add_eq_zero_iff _ _).mp h0
    exact Or.inl ((Rat.treeOfRat_eq_zero_iff U a).mp ha)
  have h1 : Rat.treeOfRat U (RatU.ratOp z) = Rat.treeOfRat U (a + b) := by rw [h]
  rw [ratOp_eq_rational, Rat.treeOfRat_rat_rational hz, Rat.treeOfRat_add] at h1
  have h2 : Tree.fam (Tree.exp (Tree.exp (Rat.treeOfRat U z)))
      = Tree.fam (Rat.treeOfRat U a) + Tree.fam (Rat.treeOfRat U b) := by
    rw [h1, Tree.fam_add]
  rw [Tree.fam_exp] at h2
  have hc : (Tree.fam (Rat.treeOfRat U a)).card + (Tree.fam (Rat.treeOfRat U b)).card = 1 := by
    have := congrArg Multiset.card h2
    simpa using this.symm
  rcases Nat.add_eq_one_iff.mp hc with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl
      ((Rat.treeOfRat_eq_zero_iff U a).mp (Tree.fam_eq_zero_iff.mp (Multiset.card_eq_zero.mp ha)))
  · exact Or.inr
      ((Rat.treeOfRat_eq_zero_iff U b).mp (Tree.fam_eq_zero_iff.mp (Multiset.card_eq_zero.mp hb)))

/-! ## The structural pieces

These are proved in the parallel files `Submission/Work/Rat/ratOp_eq_mul_group.lean` and
`Submission/Work/Rat/ofGroup_mem_A.lean`, and are re-exported here under local names.

* `ratOp_eq_mul_group` : every factorisation of a `⋄`-value has a group factor;
* `ofGroup_mem_A`      : `ofGroup u ∈ A V → u ∈ V`;
* `ratOp_eq_ratOp_mem_A`: `⋄z = ⋄d` with `d ∈ A V` forces `z ∈ A V`. -/

theorem ratOp_eq_mul_group {x a b : RatU U} (hx : x ≠ 0) (h : RatU.ratOp x = a * b) :
    (∃ u : U, a = RatU.ofGroup u) ∨ (∃ u : U, b = RatU.ofGroup u) :=
  Work.Rat.ratOp_eq_mul_group hx h

theorem ofGroup_mem_A {V : Subgroup U} {u : U} (h : RatU.ofGroup u ∈ A V) : u ∈ V :=
  Work.Rat.ofGroup_mem_A h

theorem ratOp_eq_ratOp_mem_A {V : Subgroup U} {z d : RatU U}
    (h : RatU.ratOp z = RatU.ratOp d) (hd : d ∈ A V) : z ∈ A V := by
  rw [Work.Rat.ratOp_injective z d h]
  exact hd

/-! ## The main induction

Let `s` be a term whose support lies in `V`.  If the class of `s` is a `⋄`-value, then the
argument of that `⋄` lies in `A V`.  This is the term induction of the model `ℕ[U ♮ X]`: `s` is a
group element, a sum, a product, a `⋄`, or one of the two `U`-actions, and each case is settled by
one of the structural facts above (`ratOp_add_indecomp`, `ratOp_eq_mul_group`,
`ratOp_eq_ratOp_mem_A`, together with the absorption identities `RatU.ratOp_mul_ofGroup` and
`RatU.ofGroup_mul_ratOp`). -/

theorem mem_A_of_ratOp_eq (V : Subgroup U) (s : RTerm U)
    (hs : ∀ u ∈ RTerm.supp s, u ∈ V) :
    ∀ z : RatU U, RatU.mk s = RatU.ratOp z → z ∈ A V := by
  induction s with
  | z =>
      intro z hz
      have hz0 : z = 0 := (Rat.ratOp_eq_zero_iff).mp hz.symm
      rw [hz0]
      exact ⟨0, map_zero _⟩
  | o =>
      intro z hz
      exact absurd hz.symm (ratOp_ne_one z)
  | add a b iha ihb =>
      intro z hz
      have h1 : RatU.mk a + RatU.mk b = RatU.ratOp z := by
        rw [← RatU.mk_add]; exact hz
      have hsa : ∀ u ∈ RTerm.supp a, u ∈ V :=
        fun u hu => hs u (by rw [RTerm.supp]; exact Or.inl hu)
      have hsb : ∀ u ∈ RTerm.supp b, u ∈ V :=
        fun u hu => hs u (by rw [RTerm.supp]; exact Or.inr hu)
      rcases ratOp_add_indecomp z (RatU.mk a) (RatU.mk b) h1.symm with ha | hb
      · have hz2 : RatU.mk b = RatU.ratOp z := by rw [← h1, ha, zero_add]
        exact ihb hsb z hz2
      · have hz2 : RatU.mk a = RatU.ratOp z := by rw [← h1, hb, add_zero]
        exact iha hsa z hz2
  | mul a b iha ihb =>
      intro z hz
      by_cases hz0 : z = 0
      · rw [hz0]
        exact ⟨0, map_zero _⟩
      have h1 : RatU.mk a * RatU.mk b = RatU.ratOp z := by
        rw [← RatU.mk_mul]; exact hz
      have hsa : ∀ u ∈ RTerm.supp a, u ∈ V :=
        fun u hu => hs u (by rw [RTerm.supp]; exact Or.inl hu)
      have hsb : ∀ u ∈ RTerm.supp b, u ∈ V :=
        fun u hu => hs u (by rw [RTerm.supp]; exact Or.inr hu)
      have ha : RatU.mk a ∈ A V := (mem_A_iff V (RatU.mk a)).mpr ⟨a, hsa, rfl⟩
      have hb : RatU.mk b ∈ A V := (mem_A_iff V (RatU.mk b)).mpr ⟨b, hsb, rfl⟩
      rcases ratOp_eq_mul_group hz0 h1.symm with ⟨u, hu⟩ | ⟨u, hu⟩
      · -- `mk a = ofGroup u`, hence `u ∈ V` and `mk b = ⋄(z * ofGroup u)`
        have huV : u ∈ V := ofGroup_mem_A (by rw [hu] at ha; exact ha)
        have hb' : RatU.mk b = RatU.ratOp (z * RatU.ofGroup u) := by
          have h2 := RatU.ofGroup_mul_ratOp u⁻¹ z
          rw [inv_inv] at h2
          have h4 : RatU.ofGroup u⁻¹ * (RatU.ofGroup u * RatU.mk b) = RatU.mk b := by
            rw [← mul_assoc, ← RatU.ofGroup_mul, inv_mul_cancel, RatU.ofGroup_one, one_mul]
          have h5 : RatU.ofGroup u * RatU.mk b = RatU.ratOp z := by rw [← hu, h1]
          calc RatU.mk b = RatU.ofGroup u⁻¹ * (RatU.ofGroup u * RatU.mk b) := h4.symm
            _ = RatU.ofGroup u⁻¹ * RatU.ratOp z := by rw [h5]
            _ = (RatU.rational (U := U)).ratOp (z * RatU.ofGroup u) := h2
            _ = RatU.ratOp (z * RatU.ofGroup u) := rfl
        have hz' : z * RatU.ofGroup u ∈ A V := ihb hsb _ hb'
        have hfin := A_mul hz' (A_ofGroup_mem (V := V) (inv_mem huV))
        rwa [mul_assoc, ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one, mul_one] at hfin
      · -- `mk b = ofGroup u`, hence `u ∈ V` and `mk a = ⋄(ofGroup u * z)`
        have huV : u ∈ V := ofGroup_mem_A (by rw [hu] at hb; exact hb)
        have ha' : RatU.mk a = RatU.ratOp (RatU.ofGroup u * z) := by
          have h2 := RatU.ratOp_mul_ofGroup z u⁻¹
          rw [inv_inv] at h2
          have h4 : (RatU.mk a * RatU.ofGroup u) * RatU.ofGroup u⁻¹ = RatU.mk a := by
            rw [mul_assoc, ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one, mul_one]
          have h5 : RatU.mk a * RatU.ofGroup u = RatU.ratOp z := by rw [← hu, h1]
          calc RatU.mk a = (RatU.mk a * RatU.ofGroup u) * RatU.ofGroup u⁻¹ := h4.symm
            _ = RatU.ratOp z * RatU.ofGroup u⁻¹ := by rw [h5]
            _ = (RatU.rational (U := U)).ratOp (RatU.ofGroup u * z) := h2
            _ = RatU.ratOp (RatU.ofGroup u * z) := rfl
        have hz' : RatU.ofGroup u * z ∈ A V := iha hsa _ ha'
        have hfin := A_mul (A_ofGroup_mem (V := V) (inv_mem huV)) hz'
        rwa [← mul_assoc, ← RatU.ofGroup_mul, inv_mul_cancel, RatU.ofGroup_one, one_mul] at hfin
  | rat a _iha =>
      intro z hz
      have hsa : ∀ u ∈ RTerm.supp a, u ∈ V := fun u hu => hs u (by rw [RTerm.supp]; exact hu)
      have hd : RatU.mk a ∈ A V := (mem_A_iff V (RatU.mk a)).mpr ⟨a, hsa, rfl⟩
      have h1 : RatU.ratOp (RatU.mk a) = RatU.ratOp z := by rw [← hz, RatU.mk_rat]
      exact ratOp_eq_ratOp_mem_A h1.symm hd
  | smulL u a iha =>
      intro z hz
      have huV : u ∈ V := hs u (by rw [RTerm.supp]; exact Or.inl rfl)
      have hsa : ∀ v ∈ RTerm.supp a, v ∈ V := fun v hv => hs v (by rw [RTerm.supp]; exact Or.inr hv)
      have h1 : RatU.ofGroup u * RatU.mk a = RatU.ratOp z := by
        rw [← hz, RatU.mk_smulL, RatU.smul_eq_ofGroup_mul]
      have ha' : RatU.mk a = RatU.ratOp (z * RatU.ofGroup u) := by
        have h2 := RatU.ofGroup_mul_ratOp u⁻¹ z
        rw [inv_inv] at h2
        have h4 : RatU.ofGroup u⁻¹ * (RatU.ofGroup u * RatU.mk a) = RatU.mk a := by
          rw [← mul_assoc, ← RatU.ofGroup_mul, inv_mul_cancel, RatU.ofGroup_one, one_mul]
        calc RatU.mk a = RatU.ofGroup u⁻¹ * (RatU.ofGroup u * RatU.mk a) := h4.symm
          _ = RatU.ofGroup u⁻¹ * RatU.ratOp z := by rw [h1]
          _ = (RatU.rational (U := U)).ratOp (z * RatU.ofGroup u) := h2
          _ = RatU.ratOp (z * RatU.ofGroup u) := rfl
      have hz' : z * RatU.ofGroup u ∈ A V := iha hsa _ ha'
      have hfin := A_mul hz' (A_ofGroup_mem (V := V) (inv_mem huV))
      rwa [mul_assoc, ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one, mul_one] at hfin
  | smulR u a iha =>
      intro z hz
      have huV : u ∈ V := hs u (by rw [RTerm.supp]; exact Or.inl rfl)
      have hsa : ∀ v ∈ RTerm.supp a, v ∈ V := fun v hv => hs v (by rw [RTerm.supp]; exact Or.inr hv)
      have h1 : RatU.mk a * RatU.ofGroup u = RatU.ratOp z := by
        rw [← hz, RatU.mk_smulR, RatU.smulRight_eq_mul_ofGroup]
      have ha' : RatU.mk a = RatU.ratOp (RatU.ofGroup u * z) := by
        have h2 := RatU.ratOp_mul_ofGroup z u⁻¹
        rw [inv_inv] at h2
        have h4 : (RatU.mk a * RatU.ofGroup u) * RatU.ofGroup u⁻¹ = RatU.mk a := by
          rw [mul_assoc, ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one, mul_one]
        calc RatU.mk a = (RatU.mk a * RatU.ofGroup u) * RatU.ofGroup u⁻¹ := h4.symm
          _ = RatU.ratOp z * RatU.ofGroup u⁻¹ := by rw [h1]
          _ = (RatU.rational (U := U)).ratOp (RatU.ofGroup u * z) := h2
          _ = RatU.ratOp (RatU.ofGroup u * z) := rfl
      have hz' : RatU.ofGroup u * z ∈ A V := iha hsa _ ha'
      have hfin := A_mul (A_ofGroup_mem (V := V) (inv_mem huV)) hz'
      rwa [← mul_assoc, ← RatU.ofGroup_mul, inv_mul_cancel, RatU.ofGroup_one, one_mul] at hfin

/-- The target statement: the `⋄`-operation does not change the `A V`-membership of an element.
Immediate from the term induction `mem_A_of_ratOp_eq` and the term characterisation
`Rat.mem_A_iff` of `A V`. -/
theorem A_ratOp {U : Type} [Group U] {V : Subgroup U} {x : Work.ORHughesFree.RatU U} :
    Work.ORHughesFree.RatU.ratOp x ∈ Work.ORHughesFree.Rat.A V → x ∈ Work.ORHughesFree.Rat.A V := by
  intro hx
  obtain ⟨s, hs, hsx⟩ := (mem_A_iff V (RatU.ratOp x)).mp hx
  exact mem_A_of_ratOp_eq V s hs x hsx

end Work.ORHughesFree.Rat
