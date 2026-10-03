import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.Weak.SVPart
import Submission.Work.Rat.ratOp_injective
import Submission.Work.Rat.ratOp_eq_mul_group
import Submission.Work.ORHughesFree.RatU.exists_decomp
import Submission.Work.ORHughesFree.Rat.Word

/-!
# `A V` is invariant under the rational operation `⋄` (self-contained copy)

`Rat.A V` is the image of the canonical ring homomorphism `Rat(V) → Rat(U)`
(`RatU.ofSubgroup V`).  This file proves, in the namespace `Work.ORHughesFree.Rat.Weak` and
using only the modules listed in its imports, that `⋄` does not change `A V`-membership:
`RatU.ratOp x ∈ Rat.A V → x ∈ Rat.A V`.

The proof is the term induction of `Rat/A_ratOp.lean`.  Its ingredients are

* `Rat.mem_A_iff` (`Rat/SourceFrame.lean`): `x ∈ A V` iff `x` has a term representative whose
  support lies in `V`;
* `Work.Rat.ratOp_eq_mul_group` (`Work/Rat/ratOp_eq_mul_group.lean`): every factorisation of a
  `⋄`-value has a group-element factor;
* `Work.Rat.ratOp_injective` (`Work/Rat/ratOp_injective.lean`): `⋄` is injective on `Rat(U)`;
* the reverse direction `RatU.ofGroup u ∈ A V → u ∈ V` of the only fact available in the original
  file through a module (`Work/Rat/ofGroup_mem_A.lean`) that imports
  `Rat/exists_source_subgroup_weak.lean` — a cycle for the intended consumer.  It is re-derived
  here from `Rat.treeOfRat_ofSubgroup` (`Rat/Restrict.lean`, pulled in transitively through
  `Rat/WordModel/Defs.lean`) and the injectivity of `RatU.ofGroup`, which is proved here by
  evaluating the universal morphism of `Rat(U)` in the monoid algebra `ℕ[U]` carrying the
  rational `U`-semiring structure with trivial `⋄`.
-/

namespace Work.ORHughesFree.Rat.Weak

open Work.ORHughesFree

variable {U : Type} [Group U]

/-! ## `RatU.ofGroup` is injective, and `ofGroup u ∈ A V` forces `u ∈ V` -/

/-- The monoid algebra `ℕ[U]` carries a rational `U`-semiring structure for which the rational
operation is trivial (`x ⋄ = 0`) and both `U`-actions are multiplication by the image of `U`.  In
this model the group `U` embeds faithfully, with `u` mapping to `single u 1`. -/
noncomputable def monAlgRat (U : Type) [Group U] :
    RationalUSemiring U (MonoidAlgebra ℕ U) where
  ratOp := 0
  ratOp_zero := rfl
  smul u x := MonoidAlgebra.single u 1 * x
  smulRight x u := x * MonoidAlgebra.single u 1
  smul_eq_mul u x := by simp
  smulRight_eq_mul x u := by simp
  smul_mul u v := by simp [MonoidAlgebra.single_mul_single]
  smul_one_one := by rw [mul_one, MonoidAlgebra.one_def]
  smulRight_one_one := by rw [one_mul, MonoidAlgebra.one_def]
  smulRight_one u := by rw [one_mul, mul_one]
  rat_smul u v r := by simp

/-- The universal morphism `Rat(U) → ℕ[U]` sends `ofGroup u` to `single u 1`. -/
theorem lift_monAlgRat_ofGroup (u : U) :
    RatU.lift (MonoidAlgebra ℕ U) (monAlgRat U) (RatU.ofGroup u)
      = MonoidAlgebra.single u 1 := by
  rw [RatU.ofGroup_eq_rational]
  have h := (RatU.lift_isHom (MonoidAlgebra ℕ U) (monAlgRat U)).map_smul u (1 : RatU U)
  rw [h, map_one]
  simp [monAlgRat]

/-- **The group `U` embeds in `Rat(U)`**: the map `u ↦ ofGroup u` is injective. -/
theorem ofGroup_injective_weak : Function.Injective (fun u : U => RatU.ofGroup u) := by
  intro u v h
  have h' := congrArg (RatU.lift (MonoidAlgebra ℕ U) (monAlgRat U)) h
  rw [lift_monAlgRat_ofGroup u, lift_monAlgRat_ofGroup v] at h'
  exact MonoidAlgebra.single_left_injective (r := 1) one_ne_zero h'

/-- **The image of `U` in `Rat(U)` meets `Rat.A V` exactly in `V`**: if `ofGroup u` lies in
`Rat.A V` then `u ∈ V`.

An element of `Rat(V)` whose image in `Rat(U)` is a group element is itself a group element
(compatibility of the complexity map with `Rat(V) ⊆ Rat(U)`, `Rat.treeOfRat_ofSubgroup`, plus
`Rat.treeOfRat_eq_one_iff`), and injectivity of `ofGroup` identifies the two group elements. -/
theorem ofGroup_mem_A_weak {V : Subgroup U} {u : U} (h : RatU.ofGroup u ∈ Rat.A V) : u ∈ V := by
  obtain ⟨β, hβ⟩ := h
  have h1 : Rat.treeOfRat ↥V β = 1 := by
    rw [← Rat.treeOfRat_ofSubgroup V β, hβ, Rat.treeOfRat_ofGroup]
  obtain ⟨v, hv⟩ := (Rat.treeOfRat_eq_one_iff β).mp h1
  have h2 : RatU.ofGroup u = RatU.ofGroup ((v : ↥V) : U) := by
    rw [← hβ, hv, Rat.ofSubgroup_ofGroup]
  have h3 : u = ((v : ↥V) : U) := ofGroup_injective_weak h2
  rw [h3]
  exact v.2

/-! ## Elementary facts about the rational operation -/

/-- `RatU.ratOp` and the field `RatU.rational.ratOp` are the same operation (they are equal by
`rfl`); this bridge is used to pass between the two notations. -/
theorem ratOp_eq_rational_weak (z : RatU U) :
    RatU.ratOp z = (RatU.rational (U := U)).ratOp z := rfl

/-- A `⋄`-value is never `0` for a *non-zero* argument (its complexity is a double root extension;
`⋄ 0 = 0`). -/
theorem ratOp_ne_zero_weak {z : RatU U} (hz : z ≠ 0) : RatU.ratOp z ≠ 0 := by
  intro h
  have h1 : Rat.treeOfRat U (RatU.ratOp z) = 0 := by rw [h, Rat.treeOfRat_zero]
  rw [ratOp_eq_rational_weak] at h1
  rw [Rat.treeOfRat_rat_rational hz] at h1
  exact Tree.exp_ne_zero _ h1

/-- A `⋄`-value is never `1` (that would make its complexity the one-edge tree). -/
theorem ratOp_ne_one_weak (z : RatU U) : RatU.ratOp z ≠ 1 := by
  intro h
  have h1 : Rat.treeOfRat U (RatU.ratOp z) = 1 := by rw [h, Rat.treeOfRat_one]
  rw [ratOp_eq_rational_weak] at h1
  by_cases hz : z = 0
  · rw [hz, show (RatU.rational (U := U)).ratOp 0 = 0 from RatU.ratOp_zero,
      Rat.treeOfRat_zero] at h1
    exact Tree.one_ne_zero h1.symm
  · rw [Rat.treeOfRat_rat_rational hz] at h1
    have h2 : Tree.exp (Rat.treeOfRat U z) = 0 := (Tree.exp_eq_one_iff _).mp h1
    exact Tree.exp_ne_zero _ h2

/-- **Additive indecomposability of `⋄`**: a `⋄`-value is not a sum of two non-zero elements.
In the DHS04 model `ℕ[U ♮ X]` this is the statement that `⋄z` is a single *word*. -/
theorem ratOp_add_indecomp_weak (z a b : RatU U) (h : RatU.ratOp z = a + b) :
    a = 0 ∨ b = 0 := by
  by_cases hz : z = 0
  · rw [hz, RatU.ratOp_zero] at h
    have h0 : Rat.treeOfRat U a + Rat.treeOfRat U b = 0 := by
      rw [← Rat.treeOfRat_add, ← h, Rat.treeOfRat_zero]
    obtain ⟨ha, hb⟩ := (Tree.add_eq_zero_iff _ _).mp h0
    exact Or.inl ((Rat.treeOfRat_eq_zero_iff U a).mp ha)
  have h1 : Rat.treeOfRat U (RatU.ratOp z) = Rat.treeOfRat U (a + b) := by rw [h]
  rw [ratOp_eq_rational_weak, Rat.treeOfRat_rat_rational hz, Rat.treeOfRat_add] at h1
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

`ratOp_eq_mul_group` and `ratOp_injective` are proved in the parallel files
`Submission/Work/Rat/ratOp_eq_mul_group.lean` and `Submission/Work/Rat/ratOp_injective.lean`,
and are re-exported here under local names. -/

theorem ratOp_eq_mul_group_weak {x a b : RatU U} (hx : x ≠ 0) (h : RatU.ratOp x = a * b) :
    (∃ u : U, a = RatU.ofGroup u) ∨ (∃ u : U, b = RatU.ofGroup u) :=
  Work.Rat.ratOp_eq_mul_group hx h

theorem ratOp_eq_ratOp_mem_A_weak {V : Subgroup U} {z d : RatU U}
    (h : RatU.ratOp z = RatU.ratOp d) (hd : d ∈ Rat.A V) : z ∈ Rat.A V := by
  rw [Work.Rat.ratOp_injective z d h]
  exact hd

/-! ## The main induction

Let `s` be a term whose support lies in `V`.  If the class of `s` is a `⋄`-value, then the
argument of that `⋄` lies in `A V`.  This is the term induction of the model `ℕ[U ♮ X]`: `s` is a
group element, a sum, a product, a `⋄`, or one of the two `U`-actions, and each case is settled by
one of the structural facts above (`ratOp_add_indecomp_weak`, `ratOp_eq_mul_group_weak`,
`ratOp_eq_ratOp_mem_A_weak`, together with the absorption identities `RatU.ratOp_mul_ofGroup` and
`RatU.ofGroup_mul_ratOp`). -/

theorem mem_A_of_ratOp_eq_weak (V : Subgroup U) (s : RTerm U)
    (hs : ∀ u ∈ RTerm.supp s, u ∈ V) :
    ∀ z : RatU U, RatU.mk s = RatU.ratOp z → z ∈ Rat.A V := by
  induction s with
  | z =>
      intro z hz
      have hz0 : z = 0 := (Rat.ratOp_eq_zero_iff).mp hz.symm
      rw [hz0]
      exact ⟨0, map_zero _⟩
  | o =>
      intro z hz
      exact absurd hz.symm (ratOp_ne_one_weak z)
  | add a b iha ihb =>
      intro z hz
      have h1 : RatU.mk a + RatU.mk b = RatU.ratOp z := by
        rw [← RatU.mk_add]; exact hz
      have hsa : ∀ u ∈ RTerm.supp a, u ∈ V :=
        fun u hu => hs u (by rw [RTerm.supp]; exact Or.inl hu)
      have hsb : ∀ u ∈ RTerm.supp b, u ∈ V :=
        fun u hu => hs u (by rw [RTerm.supp]; exact Or.inr hu)
      rcases ratOp_add_indecomp_weak z (RatU.mk a) (RatU.mk b) h1.symm with ha | hb
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
      have ha : RatU.mk a ∈ Rat.A V := (Rat.mem_A_iff V (RatU.mk a)).mpr ⟨a, hsa, rfl⟩
      have hb : RatU.mk b ∈ Rat.A V := (Rat.mem_A_iff V (RatU.mk b)).mpr ⟨b, hsb, rfl⟩
      rcases ratOp_eq_mul_group_weak hz0 h1.symm with ⟨u, hu⟩ | ⟨u, hu⟩
      · -- `mk a = ofGroup u`, hence `u ∈ V` and `mk b = ⋄(z * ofGroup u)`
        have huV : u ∈ V := ofGroup_mem_A_weak (by rw [hu] at ha; exact ha)
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
        have hz' : z * RatU.ofGroup u ∈ Rat.A V := ihb hsb _ hb'
        have hfin := (ASub V).mul_mem hz' (A_ofGroup_mem (V := V) (inv_mem huV))
        rwa [mul_assoc, ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one, mul_one] at hfin
      · -- `mk b = ofGroup u`, hence `u ∈ V` and `mk a = ⋄(ofGroup u * z)`
        have huV : u ∈ V := ofGroup_mem_A_weak (by rw [hu] at hb; exact hb)
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
        have hz' : RatU.ofGroup u * z ∈ Rat.A V := iha hsa _ ha'
        have hfin := (ASub V).mul_mem (A_ofGroup_mem (V := V) (inv_mem huV)) hz'
        rwa [← mul_assoc, ← RatU.ofGroup_mul, inv_mul_cancel, RatU.ofGroup_one, one_mul] at hfin
  | rat a _iha =>
      intro z hz
      have hsa : ∀ u ∈ RTerm.supp a, u ∈ V := fun u hu => hs u (by rw [RTerm.supp]; exact hu)
      have hd : RatU.mk a ∈ Rat.A V := (Rat.mem_A_iff V (RatU.mk a)).mpr ⟨a, hsa, rfl⟩
      have h1 : RatU.ratOp (RatU.mk a) = RatU.ratOp z := by
        rw [← RatU.mk_rat a]; exact hz
      exact ratOp_eq_ratOp_mem_A_weak h1.symm hd
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
      have hz' : z * RatU.ofGroup u ∈ Rat.A V := iha hsa _ ha'
      have hfin := (ASub V).mul_mem hz' (A_ofGroup_mem (V := V) (inv_mem huV))
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
      have hz' : RatU.ofGroup u * z ∈ Rat.A V := iha hsa _ ha'
      have hfin := (ASub V).mul_mem (A_ofGroup_mem (V := V) (inv_mem huV)) hz'
      rwa [← mul_assoc, ← RatU.ofGroup_mul, inv_mul_cancel, RatU.ofGroup_one, one_mul] at hfin

/-- Port of `Rat.A_ratOp` (file `Submission/Work/ORHughesFree/Rat/A_ratOp.lean`) into the namespace `Work.ORHughesFree.Rat.Weak`. The original file imports `Rat/exists_source_subgroup_weak.lean`, a cycle for the intended consumer, so the proof has to be reproduced using only `Rat/SourceFrame.lean`, `Rat/Weak/SVPart.lean`, `Work/Rat/ratOp_injective.lean`, `Work/Rat/ratOp_eq_mul_group.lean`, `RatU/exists_decomp.lean` and `Rat/Word.lean`; the original proof may be read for guidance. Note in particular that `Rat.ofGroup_mem_A` (file `Work/Rat/ofGroup_mem_A.lean`, statement `ofGroup u ∈ Rat.A V → u ∈ V`) is not importable here and has to be re-derived inside this file. -/
theorem A_ratOp {U : Type} [Group U] {V : Subgroup U} {x : Work.ORHughesFree.RatU U} :
    Work.ORHughesFree.RatU.ratOp x ∈ Work.ORHughesFree.Rat.A V →
      x ∈ Work.ORHughesFree.Rat.A V := by
  intro hx
  obtain ⟨s, hs, hsx⟩ := (Rat.mem_A_iff V (RatU.ratOp x)).mp hx
  exact mem_A_of_ratOp_eq_weak V s hs x hsx

end Work.ORHughesFree.Rat.Weak
