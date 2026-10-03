import Mathlib
import Submission.Work.ORHughesFree.Rat.Source
import Submission.Work.ORHughesFree.Rat.RTerm
import Submission.Work.ORHughesFree.Rat.OfGroup
import Submission.Work.ORHughesFree.Rat.eval_restrictScalars_map
import Submission.Work.ORHughesFree.Rat.ratComplexity_model

/-!
# The source framework of `Rat(U)` ([DHS04, Theorem 5.7])

[DHS04, Theorem 5.7] attaches to every `α ∈ Rat(U)` a *unique smallest* subgroup
`source(α) ≤ U` with `α ∈ Rat(source(α)) · U`, and shows that it is finitely generated.
This file develops the framework in which the statement is proved for the concrete term model
`RatU U` of `Rat/RTerm.lean`.

* `Rat.A V` : the image of `Rat(V) → Rat(U)`, i.e. `Rat(V)` viewed inside `Rat(U)`;
* `Rat.B V` : `Rat(V) · U`;
* `Rat.BL V` : the left analogue `U · Rat(V)`;
* `Rat.mem_A_iff`, `Rat.mem_B_iff` : the characterizations of `A V` and `B V` by *terms*
  (`x ∈ A V` iff `x` has a term representative with support in `V`);
* `Rat.F α` (and `Rat.FL α`) : the family of subgroups `V` with `α ∈ Rat(V)·U`
  (respectively with `U·α ⊆ Rat(V)·U`).

The definitions and lemmas here are deliberately *free of the target theorem*, so that other
modules (in particular the word-model files) may import them without importing
`Rat/exists_source_subgroup_weak.lean`.
-/

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree

variable {U : Type} [Group U]

/-- `A V` is the image of `Rat(V)` in `Rat(U)`. -/
def A (V : Subgroup U) : Set (RatU U) := Set.range (RatU.ofSubgroup V)

/-- `B V = Rat(V) · U`. -/
def B (V : Subgroup U) : Set (RatU U) :=
  { x | ∃ (β : RatU ↥V) (u : U), RatU.ofSubgroup V β * RatU.ofGroup u = x }

/-- `BL V` is the set of `x` with `φ(u)·x ∈ Rat(V)` for some `u ∈ U`, i.e. the "left" analogue of
`Rat(V)·U`. -/
def BL (V : Subgroup U) : Set (RatU U) :=
  { x | ∃ (β : RatU ↥V) (u : U), RatU.ofGroup u * RatU.ofSubgroup V β = x }

/-- `ofSubgroup V` sends `ofGroup v` to `ofGroup (v : U)`. -/
theorem ofSubgroup_ofGroup (V : Subgroup U) (v : ↥V) :
    RatU.ofSubgroup V (RatU.ofGroup v) = RatU.ofGroup (v : U) :=
  (RatU.ofSubgroup_isHom V).map_smul v (1 : RatU ↥V)

/-- `ofSubgroup V` applied to the class of a term over `V` is the class of the term over `U`. -/
theorem ofSubgroup_mk_map {V : Subgroup U} (τ : RTerm ↥V) :
    RatU.ofSubgroup V (RatU.mk τ) = RatU.mk (RTerm.map (Subtype.val) τ) := by
  dsimp only [RatU.ofSubgroup]
  exact (RatU.lift_apply _ _ τ).trans (eval_restrictScalars_map V τ)

/-- The support of `map f t` is contained in the image of the support of `t`. -/
theorem supp_map_mem {U' : Type} (f : U → U') (t : RTerm U) :
    ∀ {u' : U'}, u' ∈ RTerm.supp (RTerm.map f t) → ∃ u ∈ RTerm.supp t, f u = u' := by
  induction t with
  | z => intro u' h; rw [RTerm.map, RTerm.supp] at h; exact absurd h (by simp)
  | o => intro u' h; rw [RTerm.map, RTerm.supp] at h; exact absurd h (by simp)
  | add a b iha ihb =>
    intro u' h
    rw [RTerm.map, RTerm.supp, Set.mem_union] at h
    rcases h with h | h
    · obtain ⟨u, hu, hfu⟩ := iha h
      exact ⟨u, by rw [RTerm.supp]; exact Or.inl hu, hfu⟩
    · obtain ⟨u, hu, hfu⟩ := ihb h
      exact ⟨u, by rw [RTerm.supp]; exact Or.inr hu, hfu⟩
  | mul a b iha ihb =>
    intro u' h
    rw [RTerm.map, RTerm.supp, Set.mem_union] at h
    rcases h with h | h
    · obtain ⟨u, hu, hfu⟩ := iha h
      exact ⟨u, by rw [RTerm.supp]; exact Or.inl hu, hfu⟩
    · obtain ⟨u, hu, hfu⟩ := ihb h
      exact ⟨u, by rw [RTerm.supp]; exact Or.inr hu, hfu⟩
  | rat a iha =>
    intro u' h
    rw [RTerm.map] at h
    obtain ⟨u, hu, hfu⟩ := iha h
    exact ⟨u, by rw [RTerm.supp]; exact hu, hfu⟩
  | smulL v a iha =>
    intro u' h
    rw [RTerm.map, RTerm.supp, Set.mem_insert_iff] at h
    rcases h with rfl | h
    · exact ⟨v, by rw [RTerm.supp]; exact Or.inl rfl, rfl⟩
    · obtain ⟨u, hu, hfu⟩ := iha h
      exact ⟨u, by rw [RTerm.supp]; exact Or.inr hu, hfu⟩
  | smulR v a iha =>
    intro u' h
    rw [RTerm.map, RTerm.supp, Set.mem_insert_iff] at h
    rcases h with rfl | h
    · exact ⟨v, by rw [RTerm.supp]; exact Or.inl rfl, rfl⟩
    · obtain ⟨u, hu, hfu⟩ := iha h
      exact ⟨u, by rw [RTerm.supp]; exact Or.inr hu, hfu⟩

/-- **Characterization of `A V` by terms**: `x ∈ A V` iff `x` has a term representative whose
support is contained in `V`. -/
theorem mem_A_iff (V : Subgroup U) (x : RatU U) :
    x ∈ A V ↔ ∃ t : RTerm U, (∀ u ∈ RTerm.supp t, u ∈ V) ∧ RatU.mk t = x := by
  constructor
  · rintro ⟨β, rfl⟩
    refine Quotient.inductionOn β ?_
    intro τ
    refine ⟨RTerm.map (Subtype.val) τ, ?_, ?_⟩
    · intro u hu
      obtain ⟨v, -, rfl⟩ := supp_map_mem (Subtype.val) τ hu
      exact v.2
    · exact (ofSubgroup_mk_map τ).symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨RatU.mk (RTerm.map (projSub V) t), ?_⟩
    dsimp only [RatU.ofSubgroup]
    rw [RatU.lift_apply, RTerm.eval_map]
    · exact RTerm.eval_rational_self t
    · intro u hu; exact coe_projSub V (ht u hu)

theorem A_mono {V W : Subgroup U} (h : V ≤ W) : A V ⊆ A W := by
  intro x hx
  rw [mem_A_iff] at hx
  rw [mem_A_iff]
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨t, fun u hu => h (ht u hu), rfl⟩

/-- **Characterization of `B V = Rat(V)·U` by terms**: `x ∈ B V` iff there is a term `t` with
support in `V` and a group element `u` with `[t]·u = x`. -/
theorem mem_B_iff (V : Subgroup U) (x : RatU U) :
    x ∈ B V ↔ ∃ (t : RTerm U) (u : U),
      (∀ v ∈ RTerm.supp t, v ∈ V) ∧
        RatU.mk (RTerm.mul t (RTerm.smulL u RTerm.o)) = x := by
  constructor
  · rintro ⟨β, u, rfl⟩
    refine Quotient.inductionOn β ?_
    intro τ
    refine ⟨RTerm.map (Subtype.val) τ, u, ?_, ?_⟩
    · intro v hv
      obtain ⟨v', -, rfl⟩ := supp_map_mem (Subtype.val) τ hv
      exact v'.2
    · change RatU.mk (RTerm.mul (RTerm.map Subtype.val τ) (RTerm.smulL u RTerm.o))
        = RatU.ofSubgroup V (RatU.mk τ) * RatU.ofGroup u
      rw [ofSubgroup_mk_map τ, RatU.mk_mul]
      rfl
  · rintro ⟨t, u, ht, hx⟩
    refine ⟨RatU.mk (RTerm.map (projSub V) t), u, ?_⟩
    have h1 : RatU.ofSubgroup V (RatU.mk (RTerm.map (projSub V) t)) = RatU.mk t := by
      dsimp only [RatU.ofSubgroup]
      rw [RatU.lift_apply, RTerm.eval_map]
      · exact RTerm.eval_rational_self t
      · intro v hv; exact coe_projSub V (ht v hv)
    rw [h1, ← hx, RatU.mk_mul, RatU.mk_smulL, RatU.mk_one]
    rfl

theorem B_mono {V W : Subgroup U} (h : V ≤ W) : B V ⊆ B W := by
  intro x hx
  rw [mem_B_iff] at hx ⊢
  obtain ⟨t, u, ht, hx⟩ := hx
  exact ⟨t, u, fun v hv => h (ht v hv), hx⟩

theorem B_mul_ofGroup (V : Subgroup U) (x : RatU U) (u : U) (hx : x ∈ B V) :
    x * RatU.ofGroup u ∈ B V := by
  obtain ⟨β, v, rfl⟩ := hx
  exact ⟨β, v * u, by rw [RatU.ofGroup_mul, mul_assoc]⟩

theorem B_mem (V : Subgroup U) (β : RatU ↥V) : RatU.ofSubgroup V β ∈ B V :=
  ⟨β, 1, by rw [RatU.ofGroup_one, mul_one]⟩

theorem B_zero (V : Subgroup U) : (0 : RatU U) ∈ B V :=
  ⟨0, 1, by rw [map_zero, zero_mul]⟩

theorem A_one (V : Subgroup U) : (1 : RatU U) ∈ A V :=
  ⟨1, map_one _⟩

/-- The family of subgroups `V` with `α ∈ Rat(V)·U`. -/
def F (α : RatU U) : Set (Subgroup U) := { V | α ∈ B V }

/-- The family of subgroups `V` with `u·α ∈ Rat(V)` for some `u`, the "left" analogue of `F`. -/
def FL (α : RatU U) : Set (Subgroup U) := { V | α ∈ BL V }

theorem F_mono {α : RatU U} {V W : Subgroup U} (h : V ≤ W) (hV : V ∈ F α) : W ∈ F α :=
  B_mono h hV

theorem mem_F_iff (α : RatU U) (V : Subgroup U) :
    V ∈ F α ↔ ∃ (β : RatU ↥V) (u : U), RatU.ofSubgroup V β * RatU.ofGroup u = α := Iff.rfl

theorem F_mul_ofGroup (α : RatU U) (u : U) : F (α * RatU.ofGroup u) = F α := by
  have hcancel : RatU.ofGroup u * RatU.ofGroup u⁻¹ = 1 := by
    rw [← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one]
  ext V
  rw [mem_F_iff, mem_F_iff]
  constructor
  · rintro ⟨β, v, hv⟩
    refine ⟨β, v * u⁻¹, ?_⟩
    rw [RatU.ofGroup_mul, ← mul_assoc, hv, mul_assoc, hcancel, mul_one]
  · rintro ⟨β, v, hv⟩
    refine ⟨β, v * u, ?_⟩
    rw [RatU.ofGroup_mul, ← mul_assoc, hv]

end Work.ORHughesFree.Rat
