import Mathlib
import Submission.Work.ORHughesFree.Rat.mem_NUV_of_list
import Submission.Work.ORHughesFree.Rat.mem_A_mul_ofGroup_iff
import Submission.Work.ORHughesFree.Rat.mem_ofGroup_mul_A_iff
import Submission.Work.ORHughesFree.Rat.Xgen_mem_closure_iff
import Submission.Work.ORHughesFree.Rat.Ugen_mem_NUV_iff
import Submission.Work.ORHughesFree.Rat.Xgen_mem_NUV_iff
import Submission.Work.ORHughesFree.Rat.A_ratOp
import Submission.Work.ORHughesFree.Rat.Weak.A_add_left

/-!
# Cosets, and the two-sided translate relation `Φ` of `Rat.A V`

For a subgroup `V ≤ U` and an element `x : RatU U` put

  `PhiRel V x g u  ⟺  ofGroup g * x * ofGroup u ∈ Rat.A V`.

The left translates of `x` that lie in `Rat.A V` are the fibre `GSlice V x 1`, and the right
translates are `USlice V x 1`.  `mem_A_mul_ofGroup_iff` and `mem_ofGroup_mul_A_iff` rewrite these
fibres as translate sets of `NUV V` in the free-product monoid `U ♮ X`, and the first-letter
recursion `Xgen_mem_closure_iff` computes them along a word.

This file provides the definitions, the invariance of the fibres under the `V`-action and the
behaviour under the operations of the term algebra (`+`, `⋄`, the two `U`-actions).
-/

set_option autoImplicit false

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree
open Work.ORHughesFree.Rat.FreeProduct

variable {U : Type} [Group U]

/-! ### Cosets -/

/-- The right coset `a · V`. -/
def rc (V : Subgroup U) (a : U) : Set U := {u : U | ∃ s ∈ V, u = a * s}

/-- The left coset `V · a`. -/
def lc (V : Subgroup U) (a : U) : Set U := {u : U | ∃ s ∈ V, u = s * a}

/-- A set which is empty, everything, or a right coset of `V`. -/
def IsRC (V : Subgroup U) (S : Set U) : Prop := S = ∅ ∨ S = Set.univ ∨ ∃ a : U, S = rc V a

/-- A set which is empty, everything, or a left coset of `V`. -/
def IsLC (V : Subgroup U) (S : Set U) : Prop := S = ∅ ∨ S = Set.univ ∨ ∃ a : U, S = lc V a

theorem mem_rc_self (V : Subgroup U) (a : U) : a ∈ rc V a := ⟨1, V.one_mem, (mul_one a).symm⟩

theorem mem_lc_self (V : Subgroup U) (a : U) : a ∈ lc V a := ⟨1, V.one_mem, (one_mul a).symm⟩

theorem rc_eq_of_mem {V : Subgroup U} {a b : U} (h : b ∈ rc V a) : rc V b = rc V a := by
  obtain ⟨s, hs, rfl⟩ := h
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨s * t, V.mul_mem hs ht, by rw [mul_assoc]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨s⁻¹ * t, V.mul_mem (V.inv_mem hs) ht, by group⟩

theorem lc_eq_of_mem {V : Subgroup U} {a b : U} (h : b ∈ lc V a) : lc V b = lc V a := by
  obtain ⟨s, hs, rfl⟩ := h
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t * s, V.mul_mem ht hs, by rw [mul_assoc]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t * s⁻¹, V.mul_mem ht (V.inv_mem hs), by group⟩

theorem rc_inv_eq (V : Subgroup U) (a : U) : {u : U | u⁻¹ ∈ rc V a} = lc V a⁻¹ := by
  ext u
  constructor
  · rintro ⟨s, hs, hsu⟩
    exact ⟨s⁻¹, V.inv_mem hs, by rw [← inv_inv u, hsu, mul_inv_rev]⟩
  · rintro ⟨s, hs, hsu⟩
    exact ⟨s⁻¹, V.inv_mem hs, by rw [hsu, mul_inv_rev, inv_inv]⟩

theorem lc_inv_eq (V : Subgroup U) (a : U) : {u : U | u⁻¹ ∈ lc V a} = rc V a⁻¹ := by
  ext u
  constructor
  · rintro ⟨s, hs, hsu⟩
    exact ⟨s⁻¹, V.inv_mem hs, by rw [← inv_inv u, hsu, mul_inv_rev]⟩
  · rintro ⟨s, hs, hsu⟩
    exact ⟨s⁻¹, V.inv_mem hs, by rw [hsu, mul_inv_rev, inv_inv]⟩

theorem IsRC.inter {V : Subgroup U} {S T : Set U} (hS : IsRC V S) (hT : IsRC V T) :
    IsRC V (S ∩ T) := by
  rcases hS with rfl | rfl | ⟨a, rfl⟩
  · exact Or.inl (Set.empty_inter _)
  · simpa using hT
  · rcases hT with rfl | rfl | ⟨b, rfl⟩
    · exact Or.inl (Set.inter_empty _)
    · exact Or.inr (Or.inr ⟨a, by rw [Set.inter_univ]⟩)
    · by_cases h : b ∈ rc V a
      · exact Or.inr (Or.inr ⟨a, by rw [rc_eq_of_mem h, Set.inter_self]⟩)
      · refine Or.inl ?_
        ext u
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
        intro hu1 hu2
        exact h (by rw [← rc_eq_of_mem hu1, rc_eq_of_mem hu2]; exact mem_rc_self V b)

theorem IsLC.inter {V : Subgroup U} {S T : Set U} (hS : IsLC V S) (hT : IsLC V T) :
    IsLC V (S ∩ T) := by
  rcases hS with rfl | rfl | ⟨a, rfl⟩
  · exact Or.inl (Set.empty_inter _)
  · simpa using hT
  · rcases hT with rfl | rfl | ⟨b, rfl⟩
    · exact Or.inl (Set.inter_empty _)
    · exact Or.inr (Or.inr ⟨a, by rw [Set.inter_univ]⟩)
    · by_cases h : b ∈ lc V a
      · exact Or.inr (Or.inr ⟨a, by rw [lc_eq_of_mem h, Set.inter_self]⟩)
      · refine Or.inl ?_
        ext u
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
        intro hu1 hu2
        exact h (by rw [← lc_eq_of_mem hu1, lc_eq_of_mem hu2]; exact mem_lc_self V b)

/-! ### Elementary facts about `Rat.A V` -/

theorem A_ofGroup_mul_iff {V : Subgroup U} {v : U} (hv : v ∈ V) (y : RatU U) :
    RatU.ofGroup v * y ∈ A V ↔ y ∈ A V := by
  constructor
  · intro h
    have h1 : RatU.ofGroup v⁻¹ * (RatU.ofGroup v * y) ∈ A V :=
      (Weak.ASub V).mul_mem (Weak.A_ofGroup_mem (V := V) (V.inv_mem hv)) h
    rwa [← mul_assoc, ← RatU.ofGroup_mul, inv_mul_cancel, RatU.ofGroup_one, one_mul] at h1
  · intro h
    exact (Weak.ASub V).mul_mem (Weak.A_ofGroup_mem hv) h

theorem A_mul_ofGroup_iff {V : Subgroup U} {v : U} (hv : v ∈ V) (y : RatU U) :
    y * RatU.ofGroup v ∈ A V ↔ y ∈ A V := by
  constructor
  · intro h
    have h1 : (y * RatU.ofGroup v) * RatU.ofGroup v⁻¹ ∈ A V :=
      (Weak.ASub V).mul_mem h (Weak.A_ofGroup_mem (V := V) (V.inv_mem hv))
    rwa [mul_assoc, ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one, mul_one] at h1
  · intro h
    exact (Weak.ASub V).mul_mem h (Weak.A_ofGroup_mem hv)

/-! ### The two-sided translate relation -/

/-- `PhiRel V x g u` says that the two-sided translate `ofGroup g * x * ofGroup u` of `x` lies in
`Rat.A V`. -/
def PhiRel (V : Subgroup U) (x : RatU U) (g u : U) : Prop :=
  RatU.ofGroup g * x * RatU.ofGroup u ∈ A V

/-- The fibre of `PhiRel` at a fixed first coordinate: the admissible right translations. -/
def USlice (V : Subgroup U) (x : RatU U) (g : U) : Set U := {u : U | PhiRel V x g u}

/-- The fibre of `PhiRel` at a fixed second coordinate: the admissible left translations. -/
def GSlice (V : Subgroup U) (x : RatU U) (u : U) : Set U := {g : U | PhiRel V x g u}

/-- The projection of `PhiRel` on the second coordinate. -/
def PJu (V : Subgroup U) (x : RatU U) : Set U := {u : U | ∃ g : U, PhiRel V x g u}

/-- The projection of `PhiRel` on the first coordinate. -/
def PJg (V : Subgroup U) (x : RatU U) : Set U := {g : U | ∃ u : U, PhiRel V x g u}

/-- The four "coset-like" properties of the translate relation of `x`. -/
def Claims (V : Subgroup U) (x : RatU U) : Prop :=
  (∀ g : U, IsRC V (USlice V x g)) ∧ (∀ u : U, IsLC V (GSlice V x u)) ∧
    IsRC V (PJu V x) ∧ IsLC V (PJg V x)

/-! ### Behaviour under the `U`-action -/

theorem PhiRel_mul_left {V : Subgroup U} {x : RatU U} {h g u : U} :
    PhiRel V (RatU.ofGroup h * x) g u ↔ PhiRel V x (g * h) u := by
  show (RatU.ofGroup g * (RatU.ofGroup h * x) * RatU.ofGroup u ∈ A V) ↔
    (RatU.ofGroup (g * h) * x * RatU.ofGroup u ∈ A V)
  have key : RatU.ofGroup g * (RatU.ofGroup h * x) * RatU.ofGroup u
      = RatU.ofGroup (g * h) * x * RatU.ofGroup u := by
    rw [← mul_assoc (RatU.ofGroup g) (RatU.ofGroup h) x, RatU.ofGroup_mul]
  rw [key]

theorem PhiRel_mul_right {V : Subgroup U} {x : RatU U} {h g u : U} :
    PhiRel V (x * RatU.ofGroup h) g u ↔ PhiRel V x g (h * u) := by
  show (RatU.ofGroup g * (x * RatU.ofGroup h) * RatU.ofGroup u ∈ A V) ↔
    (RatU.ofGroup g * x * RatU.ofGroup (h * u) ∈ A V)
  have key : RatU.ofGroup g * (x * RatU.ofGroup h) * RatU.ofGroup u
      = RatU.ofGroup g * x * RatU.ofGroup (h * u) := by
    rw [RatU.ofGroup_mul]
    simp only [mul_assoc]
  rw [key]

theorem PhiRel_smul_left {V : Subgroup U} {x : RatU U} {v : U} (hv : v ∈ V) {g u : U} :
    PhiRel V x (v * g) u ↔ PhiRel V x g u := by
  show (RatU.ofGroup (v * g) * x * RatU.ofGroup u ∈ A V) ↔
    (RatU.ofGroup g * x * RatU.ofGroup u ∈ A V)
  have key : RatU.ofGroup (v * g) * x * RatU.ofGroup u
      = RatU.ofGroup v * (RatU.ofGroup g * x * RatU.ofGroup u) := by
    rw [RatU.ofGroup_mul]
    simp only [mul_assoc]
  rw [key, A_ofGroup_mul_iff hv]

theorem PhiRel_smul_right {V : Subgroup U} {x : RatU U} {v : U} (hv : v ∈ V) {g u : U} :
    PhiRel V x g (u * v) ↔ PhiRel V x g u := by
  show (RatU.ofGroup g * x * RatU.ofGroup (u * v) ∈ A V) ↔
    (RatU.ofGroup g * x * RatU.ofGroup u ∈ A V)
  have key : RatU.ofGroup g * x * RatU.ofGroup (u * v)
      = (RatU.ofGroup g * x * RatU.ofGroup u) * RatU.ofGroup v := by
    rw [RatU.ofGroup_mul]
    simp only [mul_assoc]
  rw [key, A_mul_ofGroup_iff hv]

/-- The fibres at points differing by the `V`-action agree. -/
theorem USlice_smul {V : Subgroup U} {x : RatU U} {v : U} (hv : v ∈ V) (g : U) :
    USlice V x (v * g) = USlice V x g := by
  ext u
  exact PhiRel_smul_left hv

theorem GSlice_smul {V : Subgroup U} {x : RatU U} {v : U} (hv : v ∈ V) (u : U) :
    GSlice V x (u * v) = GSlice V x u := by
  ext g
  exact PhiRel_smul_right hv

/-! ### Behaviour under `+` -/

theorem PhiRel_add {V : Subgroup U} {x y : RatU U} {g u : U} :
    PhiRel V (x + y) g u ↔ PhiRel V x g u ∧ PhiRel V y g u := by
  show (RatU.ofGroup g * (x + y) * RatU.ofGroup u ∈ A V) ↔
    (RatU.ofGroup g * x * RatU.ofGroup u ∈ A V ∧ RatU.ofGroup g * y * RatU.ofGroup u ∈ A V)
  have key : RatU.ofGroup g * (x + y) * RatU.ofGroup u
      = RatU.ofGroup g * x * RatU.ofGroup u + RatU.ofGroup g * y * RatU.ofGroup u := by
    rw [mul_add, add_mul]
  rw [key]
  constructor
  · intro h
    refine ⟨Weak.A_add_left h, ?_⟩
    exact Weak.A_add_left (x := RatU.ofGroup g * y * RatU.ofGroup u)
      (y := RatU.ofGroup g * x * RatU.ofGroup u) (by rwa [add_comm] at h)
  · rintro ⟨h1, h2⟩
    exact (Weak.ASub V).add_mem h1 h2

/-! ### Behaviour under `⋄` -/

theorem Psi_ratOp_mul_eq {x : RatU U} {g u : U} :
    RatU.ofGroup g * RatU.ratOp x * RatU.ofGroup u
      = RatU.ratOp (RatU.ofGroup u⁻¹ * x * RatU.ofGroup g⁻¹) := by
  have hmono : FreeProduct.NU.Ugen g * FreeProduct.NU.Xgen x * FreeProduct.NU.Ugen u
      = FreeProduct.NU.Xgen (RatU.ofGroup u⁻¹ * x * RatU.ofGroup g⁻¹) := by
    rw [FreeProduct.NU.Ugen_mul_Xgen, FreeProduct.NU.Xgen_mul_Ugen]
    congr 1
    simp only [FreeProduct.actL, FreeProduct.actR, mul_assoc]
  by_cases hx : x = 0
  · subst hx
    simp [RatU.ratOp_zero]
  have hx' : RatU.ofGroup u⁻¹ * x * RatU.ofGroup g⁻¹ ≠ 0 := by
    rw [mul_assoc]
    exact fun h => hx ((RatU.ofGroup_mul_eq_zero_iff u⁻¹ g⁻¹ x).mp h)
  apply FreeProduct.Psi_injective
  rw [map_mul, map_mul, FreeProduct.Psi_ofGroup, FreeProduct.Psi_ofGroup,
    FreeProduct.Psi_ratOp hx, FreeProduct.Psi_ratOp hx']
  simp only [MonoidAlgebra.single_mul_single, mul_one]
  exact congrArg (fun p => MonoidAlgebra.single p (1 : ℕ)) hmono

theorem PhiRel_ratOp {V : Subgroup U} {x : RatU U} {g u : U} :
    PhiRel V (RatU.ratOp x) g u ↔ PhiRel V x u⁻¹ g⁻¹ := by
  show (RatU.ofGroup g * RatU.ratOp x * RatU.ofGroup u ∈ A V) ↔
    (RatU.ofGroup u⁻¹ * x * RatU.ofGroup g⁻¹ ∈ A V)
  rw [Psi_ratOp_mul_eq]
  exact ⟨fun h => Rat.A_ratOp h, fun h => Weak.A_ratOp_mem h⟩

/-! ### Auxiliary rewritings of cosets -/

theorem mul_right_lc_mem (V : Subgroup U) (a h : U) :
    {g : U | g * h ∈ lc V a} = lc V (a * h⁻¹) := by
  ext g
  constructor
  · rintro ⟨s, hs, hsg⟩
    refine ⟨s, hs, ?_⟩
    calc g = (g * h) * h⁻¹ := by group
      _ = (s * a) * h⁻¹ := by rw [hsg]
      _ = s * (a * h⁻¹) := by group
  · rintro ⟨s, hs, hsg⟩
    refine ⟨s, hs, ?_⟩
    calc g * h = (s * (a * h⁻¹)) * h := by rw [hsg]
      _ = s * a := by group

theorem mul_left_rc_mem (V : Subgroup U) (a h : U) :
    {u : U | h * u ∈ rc V a} = rc V (h⁻¹ * a) := by
  ext u
  constructor
  · rintro ⟨s, hs, hsu⟩
    refine ⟨s, hs, ?_⟩
    calc u = h⁻¹ * (h * u) := by group
      _ = h⁻¹ * (a * s) := by rw [hsu]
      _ = (h⁻¹ * a) * s := by group
  · rintro ⟨s, hs, hsu⟩
    refine ⟨s, hs, ?_⟩
    calc h * u = h * ((h⁻¹ * a) * s) := by rw [hsu]
      _ = a * s := by group

/-! ### Invariance of the four properties under the `U`-action -/

theorem Claims.ofGroup_mul {V : Subgroup U} {x : RatU U} {h : U} (hx : Claims V x) :
    Claims V (RatU.ofGroup h * x) := by
  have hU : ∀ g : U, USlice V (RatU.ofGroup h * x) g = USlice V x (g * h) := by
    intro g; ext u; exact PhiRel_mul_left
  have hG : ∀ u : U, GSlice V (RatU.ofGroup h * x) u = {g : U | g * h ∈ GSlice V x u} := by
    intro u; ext g; exact PhiRel_mul_left
  have hJ : PJu V (RatU.ofGroup h * x) = PJu V x := by
    ext u
    constructor
    · rintro ⟨g, hg⟩; exact ⟨g * h, (PhiRel_mul_left).mp hg⟩
    · rintro ⟨g', hg'⟩
      exact ⟨g' * h⁻¹, (PhiRel_mul_left).mpr (by rwa [show (g' * h⁻¹) * h = g' from by group])⟩
  have hJg : PJg V (RatU.ofGroup h * x) = {g : U | g * h ∈ PJg V x} := by
    ext g; constructor
    · rintro ⟨u, hu⟩; exact ⟨u, (PhiRel_mul_left).mp hu⟩
    · rintro ⟨u, hu⟩; exact ⟨u, (PhiRel_mul_left).mpr hu⟩
  refine ⟨fun g => ?_, fun u => ?_, ?_, ?_⟩
  · rw [hU g]; exact hx.1 (g * h)
  · rw [hG u]
    rcases hx.2.1 u with h | h | ⟨a, ha⟩
    · exact Or.inl (by rw [h]; ext g; simp)
    · exact Or.inr (Or.inl (by rw [h]; ext g; simp))
    · exact Or.inr (Or.inr ⟨a * h⁻¹, by rw [ha]; exact mul_right_lc_mem V a h⟩)
  · rw [hJ]; exact hx.2.2.1
  · rw [hJg]
    rcases hx.2.2.2 with h | h | ⟨a, ha⟩
    · exact Or.inl (by rw [h]; ext g; simp)
    · exact Or.inr (Or.inl (by rw [h]; ext g; simp))
    · exact Or.inr (Or.inr ⟨a * h⁻¹, by rw [ha]; exact mul_right_lc_mem V a h⟩)

theorem Claims.mul_ofGroup {V : Subgroup U} {x : RatU U} {h : U} (hx : Claims V x) :
    Claims V (x * RatU.ofGroup h) := by
  have hU : ∀ g : U, USlice V (x * RatU.ofGroup h) g = {u : U | h * u ∈ USlice V x g} := by
    intro g; ext u; exact PhiRel_mul_right
  have hG : ∀ u : U, GSlice V (x * RatU.ofGroup h) u = GSlice V x (h * u) := by
    intro u; ext g; exact PhiRel_mul_right
  have hJ : PJu V (x * RatU.ofGroup h) = {u : U | h * u ∈ PJu V x} := by
    ext u; constructor
    · rintro ⟨g, hg⟩; exact ⟨g, (PhiRel_mul_right).mp hg⟩
    · rintro ⟨g, hg⟩; exact ⟨g, (PhiRel_mul_right).mpr hg⟩
  have hJg : PJg V (x * RatU.ofGroup h) = PJg V x := by
    ext g; constructor
    · rintro ⟨u, hu⟩; exact ⟨h * u, (PhiRel_mul_right).mp hu⟩
    · rintro ⟨u', hu'⟩
      exact ⟨h⁻¹ * u', (PhiRel_mul_right).mpr (by rwa [show h * (h⁻¹ * u') = u' from by group])⟩
  refine ⟨fun g => ?_, fun u => ?_, ?_, ?_⟩
  · rw [hU g]
    rcases hx.1 g with h | h | ⟨a, ha⟩
    · exact Or.inl (by rw [h]; ext u; simp)
    · exact Or.inr (Or.inl (by rw [h]; ext u; simp))
    · exact Or.inr (Or.inr ⟨h⁻¹ * a, by rw [ha]; exact mul_left_rc_mem V a h⟩)
  · rw [hG u]; exact hx.2.1 (h * u)
  · rw [hJ]
    rcases hx.2.2.1 with h | h | ⟨a, ha⟩
    · exact Or.inl (by rw [h]; ext u; simp)
    · exact Or.inr (Or.inl (by rw [h]; ext u; simp))
    · exact Or.inr (Or.inr ⟨h⁻¹ * a, by rw [ha]; exact mul_left_rc_mem V a h⟩)
  · rw [hJg]; exact hx.2.2.2

/-! ### The monoid level: words of `X`-letters -/

/-- The product in `U ♮ X` of the `Xgen`'s of a list. -/
noncomputable def wprod (l : List (RatU U)) : FreeProduct.NU U :=
  (l.map FreeProduct.NU.Xgen).prod

@[simp] theorem wprod_nil : wprod ([] : List (RatU U)) = 1 := rfl

@[simp] theorem wprod_cons (x : RatU U) (l : List (RatU U)) :
    wprod (x :: l) = FreeProduct.NU.Xgen x * wprod l := by
  simp [wprod]

theorem wprod_append (l l' : List (RatU U)) : wprod (l ++ l') = wprod l * wprod l' := by
  simp only [wprod, List.map_append, List.prod_append]

theorem Ugen_one : FreeProduct.NU.Ugen (1 : U) = (1 : FreeProduct.NU U) := rfl

/-- The two-sided translate relation of the monoid element `wprod l`. -/
def PhimRel (V : Subgroup U) (l : List (RatU U)) (g u : U) : Prop :=
  FreeProduct.NU.Ugen g * wprod l * FreeProduct.NU.Ugen u ∈ Orbit.NUV V

def USliceW (V : Subgroup U) (l : List (RatU U)) (g : U) : Set U := {u : U | PhimRel V l g u}

def GSliceW (V : Subgroup U) (l : List (RatU U)) (u : U) : Set U := {g : U | PhimRel V l g u}

def PJuW (V : Subgroup U) (l : List (RatU U)) : Set U := {u : U | ∃ g : U, PhimRel V l g u}

def PJgW (V : Subgroup U) (l : List (RatU U)) : Set U := {g : U | ∃ u : U, PhimRel V l g u}

/-- The four "coset-like" properties of the translate relation of a word. -/
def ClaimsW (V : Subgroup U) (l : List (RatU U)) : Prop :=
  (∀ g : U, IsRC V (USliceW V l g)) ∧ (∀ u : U, IsLC V (GSliceW V l u)) ∧
    IsRC V (PJuW V l) ∧ IsLC V (PJgW V l)

/-- **The first-letter recursion** for the translate relation of a word. -/
theorem PhimRel_cons {V : Subgroup U} {x : RatU U} {l : List (RatU U)} {g u : U} :
    PhimRel V (x :: l) g u ↔ ∃ t : U, PhiRel V x t g⁻¹ ∧ PhimRel V l t u := by
  have h1 : FreeProduct.NU.Ugen g * wprod (x :: l) * FreeProduct.NU.Ugen u
      = FreeProduct.NU.Xgen (FreeProduct.actL g x) * (wprod l * FreeProduct.NU.Ugen u) := by
    rw [wprod_cons, ← mul_assoc (FreeProduct.NU.Ugen g) (FreeProduct.NU.Xgen x) (wprod l),
      FreeProduct.NU.Ugen_mul_Xgen]
    simp only [mul_assoc]
  unfold PhimRel
  rw [h1]
  unfold Orbit.NUV
  rw [Xgen_mem_closure_iff]
  constructor
  · rintro ⟨v, hv1, hv2⟩
    refine ⟨v⁻¹, ?_, ?_⟩
    · show RatU.ofGroup v⁻¹ * x * RatU.ofGroup g⁻¹ ∈ A V
      have hEq : FreeProduct.actR v (FreeProduct.actL g x)
          = RatU.ofGroup v⁻¹ * x * RatU.ofGroup g⁻¹ := by
        simp only [FreeProduct.actR, FreeProduct.actL, inv_inv, mul_assoc]
      rwa [hEq] at hv1
    · show FreeProduct.NU.Ugen v⁻¹ * wprod l * FreeProduct.NU.Ugen u ∈ Orbit.NUV V
      rwa [← mul_assoc] at hv2
  · rintro ⟨t, ht1, ht2⟩
    refine ⟨t⁻¹, ?_, ?_⟩
    · show FreeProduct.actR t⁻¹ (FreeProduct.actL g x) ∈ A V
      have hEq : FreeProduct.actR t⁻¹ (FreeProduct.actL g x)
          = RatU.ofGroup t * x * RatU.ofGroup g⁻¹ := by
        simp only [FreeProduct.actR, FreeProduct.actL, inv_inv, mul_assoc]
      rw [hEq]
      exact ht1
    · show FreeProduct.NU.Ugen t⁻¹⁻¹ * (wprod l * FreeProduct.NU.Ugen u) ∈ Orbit.NUV V
      rw [inv_inv, ← mul_assoc]
      exact ht2

/-- The word-level translate relation is invariant under the `V`-action. -/
theorem PhimRel_smul_left {V : Subgroup U} {l : List (RatU U)} {v : U} (hv : v ∈ V)
    {g u : U} : PhimRel V l (v * g) u ↔ PhimRel V l g u := by
  have hmem : FreeProduct.NU.Ugen v ∈ Orbit.NUV V := Orbit.Ugen_mem_NUV hv
  have hmem' : FreeProduct.NU.Ugen v⁻¹ ∈ Orbit.NUV V := Orbit.Ugen_mem_NUV (V.inv_mem hv)
  show (FreeProduct.NU.Ugen (v * g) * wprod l * FreeProduct.NU.Ugen u ∈ Orbit.NUV V) ↔
    (FreeProduct.NU.Ugen g * wprod l * FreeProduct.NU.Ugen u ∈ Orbit.NUV V)
  have key : FreeProduct.NU.Ugen (v * g) * wprod l * FreeProduct.NU.Ugen u
      = FreeProduct.NU.Ugen v * (FreeProduct.NU.Ugen g * wprod l * FreeProduct.NU.Ugen u) := by
    rw [← FreeProduct.NU.Ugen_mul]
    simp only [mul_assoc]
  rw [key]
  constructor
  · intro h
    have h1 : FreeProduct.NU.Ugen v⁻¹ * (FreeProduct.NU.Ugen v
        * (FreeProduct.NU.Ugen g * wprod l * FreeProduct.NU.Ugen u)) ∈ Orbit.NUV V :=
      (Orbit.NUV V).mul_mem hmem' h
    rwa [← mul_assoc, FreeProduct.NU.Ugen_mul, inv_mul_cancel, Ugen_one, one_mul] at h1
  · intro h
    exact (Orbit.NUV V).mul_mem hmem h

theorem PhimRel_smul_right {V : Subgroup U} {l : List (RatU U)} {v : U} (hv : v ∈ V)
    {g u : U} : PhimRel V l g (u * v) ↔ PhimRel V l g u := by
  have hmem : FreeProduct.NU.Ugen v ∈ Orbit.NUV V := Orbit.Ugen_mem_NUV hv
  have hmem' : FreeProduct.NU.Ugen v⁻¹ ∈ Orbit.NUV V := Orbit.Ugen_mem_NUV (V.inv_mem hv)
  show (FreeProduct.NU.Ugen g * wprod l * FreeProduct.NU.Ugen (u * v) ∈ Orbit.NUV V) ↔
    (FreeProduct.NU.Ugen g * wprod l * FreeProduct.NU.Ugen u ∈ Orbit.NUV V)
  have key : FreeProduct.NU.Ugen g * wprod l * FreeProduct.NU.Ugen (u * v)
      = (FreeProduct.NU.Ugen g * wprod l * FreeProduct.NU.Ugen u) * FreeProduct.NU.Ugen v := by
    rw [← FreeProduct.NU.Ugen_mul]
    simp only [mul_assoc]
  rw [key]
  constructor
  · intro h
    have h1 : ((FreeProduct.NU.Ugen g * wprod l * FreeProduct.NU.Ugen u)
        * FreeProduct.NU.Ugen v) * FreeProduct.NU.Ugen v⁻¹ ∈ Orbit.NUV V :=
      (Orbit.NUV V).mul_mem h hmem'
    rwa [mul_assoc, FreeProduct.NU.Ugen_mul, mul_inv_cancel, Ugen_one, mul_one] at h1
  · intro h
    exact (Orbit.NUV V).mul_mem h hmem

theorem USliceW_smul {V : Subgroup U} {l : List (RatU U)} {v : U} (hv : v ∈ V) (g : U) :
    USliceW V l (v * g) = USliceW V l g := by
  ext u
  exact PhimRel_smul_left hv

theorem GSliceW_smul {V : Subgroup U} {l : List (RatU U)} {v : U} (hv : v ∈ V) (u : U) :
    GSliceW V l (u * v) = GSliceW V l u := by
  ext g
  exact PhimRel_smul_right hv

/-! ### The support of `Psi x` -/

theorem supp_Psi_zero : (FreeProduct.Psi (0 : RatU U)).coeff.support = ∅ := by
  rw [map_zero]; exact Finsupp.support_zero

theorem supp_Psi_ratOp (x : RatU U) (hx : x ≠ 0) :
    (FreeProduct.Psi (RatU.ratOp x)).coeff.support = {FreeProduct.NU.Xgen x} := by
  rw [FreeProduct.Psi_ratOp hx]
  ext r
  by_cases h : r = FreeProduct.NU.Xgen x
  · subst h
    simp
  · simp [h]

theorem coeff_mul_single_apply_nat {M : Type} [Monoid M] [DecidableEq M] (p : M)
    (z : MonoidAlgebra ℕ M) (r : M) :
    (z * MonoidAlgebra.single p 1).coeff r =
      ∑ q ∈ z.coeff.support, (if q * p = r then z.coeff q else 0) := by
  classical
  rw [MonoidAlgebra.coeff_mul]
  rw [Finsupp.sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finsupp.sum]
  rw [Finset.sum_eq_single p]
  · simp
  · intro b hb hbp
    rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hbp]
    simp
  · intro hp
    exact absurd (Finsupp.mem_support_iff.mpr (by simp)) hp

theorem sum_ite_ne_zero_iff' {M : Type} [Mul M] [DecidableEq M] (p r : M)
    (z : MonoidAlgebra ℕ M) :
    (∑ q ∈ z.coeff.support, (if q * p = r then z.coeff q else 0)) ≠ 0 ↔
      ∃ q, z.coeff q ≠ 0 ∧ q * p = r := by
  constructor
  · intro h
    by_contra hc
    exact h (Finset.sum_eq_zero fun q hq => by
      by_cases hpq : q * p = r
      · exact absurd hpq fun hp => hc ⟨q, Finsupp.mem_support_iff.mp hq, hp⟩
      · simp [hpq])
  · rintro ⟨q, hq, hpq⟩
    refine ne_of_gt (Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨q, ?_, ?_⟩)
    · exact Finsupp.mem_support_iff.mpr hq
    · rw [if_pos hpq]; exact Nat.pos_of_ne_zero hq

theorem mem_support_mul_single {M : Type} [Monoid M] (z : MonoidAlgebra ℕ M) (p : M) :
    ∀ r : M, r ∈ (z * MonoidAlgebra.single p 1).coeff.support ↔
      ∃ q ∈ z.coeff.support, q * p = r := by
  classical
  intro r
  simp only [Finsupp.mem_support_iff]
  rw [coeff_mul_single_apply_nat]
  exact sum_ite_ne_zero_iff' p r z

/-! ### The assembly: the target statements from `Claims` -/

theorem lc_one (V : Subgroup U) : lc V (1 : U) = (V : Set U) := by
  ext u
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa using hs
  · intro hu
    exact ⟨u, hu, (mul_one u).symm⟩

theorem PhiRel_one_iff {V : Subgroup U} {g u : U} :
    PhiRel V (1 : RatU U) g u ↔ g * u ∈ V := by
  show RatU.ofGroup g * 1 * RatU.ofGroup u ∈ A V ↔ g * u ∈ V
  rw [mul_one, ← RatU.ofGroup_mul]
  exact ⟨fun h => ofGroup_mem_A h, fun h => Weak.A_ofGroup_mem h⟩

theorem USlice_one (V : Subgroup U) (g : U) : USlice V (1 : RatU U) g = rc V g⁻¹ := by
  ext u
  show PhiRel V (1 : RatU U) g u ↔ u ∈ rc V g⁻¹
  rw [PhiRel_one_iff]
  constructor
  · intro h
    exact ⟨g * u, h, by group⟩
  · rintro ⟨s, hs, rfl⟩
    rw [show g * (g⁻¹ * s) = s from by group]
    exact hs

theorem GSlice_one (V : Subgroup U) (u : U) : GSlice V (1 : RatU U) u = lc V u⁻¹ := by
  ext g
  show PhiRel V (1 : RatU U) g u ↔ g ∈ lc V u⁻¹
  rw [PhiRel_one_iff]
  constructor
  · intro h
    exact ⟨g * u, h, by group⟩
  · rintro ⟨s, hs, rfl⟩
    rw [show s * u⁻¹ * u = s from by group]
    exact hs

theorem PJu_one (V : Subgroup U) : PJu V (1 : RatU U) = Set.univ := by
  ext u
  constructor
  · intro _; trivial
  · intro _
    exact ⟨u⁻¹, by rw [PhiRel_one_iff, inv_mul_cancel]; exact V.one_mem⟩

theorem PJg_one (V : Subgroup U) : PJg V (1 : RatU U) = Set.univ := by
  ext g
  constructor
  · intro _; trivial
  · intro _
    exact ⟨g⁻¹, by rw [PhiRel_one_iff, mul_inv_cancel]; exact V.one_mem⟩

theorem Claims.one (V : Subgroup U) : Claims V (1 : RatU U) :=
  ⟨fun g => by rw [USlice_one]; exact Or.inr (Or.inr ⟨g⁻¹, rfl⟩),
   fun u => by rw [GSlice_one]; exact Or.inr (Or.inr ⟨u⁻¹, rfl⟩),
   by rw [PJu_one]; exact Or.inr (Or.inl rfl),
   by rw [PJg_one]; exact Or.inr (Or.inl rfl)⟩

theorem PhiRel_zero {V : Subgroup U} {g u : U} : PhiRel V (0 : RatU U) g u := by
  show RatU.ofGroup g * 0 * RatU.ofGroup u ∈ A V
  rw [mul_zero, zero_mul]
  exact (Weak.ASub V).zero_mem

theorem USlice_zero (V : Subgroup U) (g : U) : USlice V (0 : RatU U) g = Set.univ := by
  ext u; exact ⟨fun _ => trivial, fun _ => PhiRel_zero⟩

theorem GSlice_zero (V : Subgroup U) (u : U) : GSlice V (0 : RatU U) u = Set.univ := by
  ext g; exact ⟨fun _ => trivial, fun _ => PhiRel_zero⟩

theorem PJu_zero (V : Subgroup U) : PJu V (0 : RatU U) = Set.univ := by
  ext u; exact ⟨fun _ => trivial, fun _ => ⟨1, PhiRel_zero⟩⟩

theorem PJg_zero (V : Subgroup U) : PJg V (0 : RatU U) = Set.univ := by
  ext g; exact ⟨fun _ => trivial, fun _ => ⟨1, PhiRel_zero⟩⟩

theorem Claims.zero (V : Subgroup U) : Claims V (0 : RatU U) :=
  ⟨fun g => by rw [USlice_zero]; exact Or.inr (Or.inl rfl),
   fun u => by rw [GSlice_zero]; exact Or.inr (Or.inl rfl),
   by rw [PJu_zero]; exact Or.inr (Or.inl rfl),
   by rw [PJg_zero]; exact Or.inr (Or.inl rfl)⟩

/-- **The target statement for the left translates** (in the form used by the requester) follows
from `Claims`. -/
theorem eq_V_or_univ_of_claims {V : Subgroup U} {b : RatU U} (hb : b ∈ A V)
    (h : Claims V b) :
    {w : U | RatU.ofGroup w * b ∈ A V} = (V : Set U) ∨
      {w : U | RatU.ofGroup w * b ∈ A V} = Set.univ := by
  have h1 : {w : U | RatU.ofGroup w * b ∈ A V} = GSlice V b 1 := by
    ext w
    show RatU.ofGroup w * b ∈ A V ↔ PhiRel V b w 1
    rw [PhiRel, RatU.ofGroup_one, mul_one]
  rw [h1]
  have hmem : (1 : U) ∈ GSlice V b 1 := by
    show PhiRel V b 1 1
    rw [PhiRel, RatU.ofGroup_one, one_mul, mul_one]
    exact hb
  rcases h.2.1 1 with h0 | h0 | ⟨a, ha⟩
  · rw [h0] at hmem
    exact absurd hmem (Set.notMem_empty 1)
  · exact Or.inr h0
  · left
    have hmem' : (1 : U) ∈ lc V a := by rw [← ha]; exact hmem
    have haV : a ∈ V := by
      obtain ⟨s, hs, hs1⟩ := hmem'
      have h1 : a = s⁻¹ := by
        calc a = s⁻¹ * (s * a) := by group
          _ = s⁻¹ * 1 := by rw [hs1]
          _ = s⁻¹ := by simp
      rw [h1]
      exact V.inv_mem hs
    have hlc : lc V a = (V : Set U) := by
      ext u
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact V.mul_mem hs haV
      · intro hu
        exact ⟨u * a⁻¹, V.mul_mem hu (V.inv_mem haV), by group⟩
    rw [ha, hlc]

/-! ### The `⋄` case of the `Claims` closure -/

theorem USlice_ratOp (V : Subgroup U) (x : RatU U) (g : U) :
    USlice V (RatU.ratOp x) g = {u : U | u⁻¹ ∈ GSlice V x g⁻¹} := by
  ext u
  show PhiRel V (RatU.ratOp x) g u ↔ u⁻¹ ∈ GSlice V x g⁻¹
  rw [PhiRel_ratOp]
  rfl

theorem GSlice_ratOp (V : Subgroup U) (x : RatU U) (u : U) :
    GSlice V (RatU.ratOp x) u = {g : U | g⁻¹ ∈ USlice V x u⁻¹} := by
  ext g
  show PhiRel V (RatU.ratOp x) g u ↔ g⁻¹ ∈ USlice V x u⁻¹
  rw [PhiRel_ratOp]
  rfl

theorem PJu_ratOp (V : Subgroup U) (x : RatU U) :
    PJu V (RatU.ratOp x) = {u : U | u⁻¹ ∈ PJg V x} := by
  ext u
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g⁻¹, (PhiRel_ratOp).mp hg⟩
  · rintro ⟨g', hg'⟩
    exact ⟨g'⁻¹, (PhiRel_ratOp).mpr (by simpa using hg')⟩

theorem PJg_ratOp (V : Subgroup U) (x : RatU U) :
    PJg V (RatU.ratOp x) = {g : U | g⁻¹ ∈ PJu V x} := by
  ext g
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u⁻¹, (PhiRel_ratOp).mp hu⟩
  · rintro ⟨u', hu'⟩
    exact ⟨u'⁻¹, (PhiRel_ratOp).mpr (by simpa using hu')⟩

theorem Claims.ratOp {V : Subgroup U} {x : RatU U} (hx : Claims V x) :
    Claims V (RatU.ratOp x) := by
  refine ⟨fun g => ?_, fun u => ?_, ?_, ?_⟩
  · rw [USlice_ratOp]
    rcases hx.2.1 g⁻¹ with h | h | ⟨a, ha⟩
    · exact Or.inl (by rw [h]; ext u; simp)
    · exact Or.inr (Or.inl (by rw [h]; ext u; simp))
    · exact Or.inr (Or.inr ⟨a⁻¹, by rw [ha]; exact lc_inv_eq V a⟩)
  · rw [GSlice_ratOp]
    rcases hx.1 u⁻¹ with h | h | ⟨a, ha⟩
    · exact Or.inl (by rw [h]; ext g; simp)
    · exact Or.inr (Or.inl (by rw [h]; ext g; simp))
    · exact Or.inr (Or.inr ⟨a⁻¹, by rw [ha]; exact rc_inv_eq V a⟩)
  · rw [PJu_ratOp]
    rcases hx.2.2.2 with h | h | ⟨a, ha⟩
    · exact Or.inl (by rw [h]; ext u; simp)
    · exact Or.inr (Or.inl (by rw [h]; ext u; simp))
    · exact Or.inr (Or.inr ⟨a⁻¹, by rw [ha]; exact lc_inv_eq V a⟩)
  · rw [PJg_ratOp]
    rcases hx.2.2.1 with h | h | ⟨a, ha⟩
    · exact Or.inl (by rw [h]; ext g; simp)
    · exact Or.inr (Or.inl (by rw [h]; ext g; simp))
    · exact Or.inr (Or.inr ⟨a⁻¹, by rw [ha]; exact rc_inv_eq V a⟩)

end Work.ORHughesFree.Rat
