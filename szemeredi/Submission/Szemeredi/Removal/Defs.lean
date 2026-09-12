import Mathlib

/-!
# Finite σ-algebras (partitions), conditional expectation and energy

This file sets up the elementary measure-theoretic API used in the proof of the
hypergraph removal lemma (Tao, arXiv:math/0503572): a finite set `Ω` equipped with
a partition `SigAlg Ω` (a "finite σ-algebra"), the uniform average `avg`, the
conditional expectation `condExp`, the energy `energy`, and their basic
identities (Pythagoras, the L²-projection property, and the tower property).
-/

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false

namespace Szemeredi.Removal

/-- A finite partition ("finite σ-algebra") of `Ω`, presented by its blocks:
`P.block x` is the block (atom) containing `x`. -/
structure SigAlg (Ω : Type*) where
  block : Ω → Finset Ω
  mem_block : ∀ x : Ω, x ∈ block x
  block_eq : ∀ {x y : Ω}, y ∈ block x → block y = block x

namespace SigAlg

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem ext {P Q : SigAlg Ω} (h : ∀ x, P.block x = Q.block x) : P = Q := by
  obtain ⟨b, hb1, hb2⟩ := P
  obtain ⟨c, hc1, hc2⟩ := Q
  have hbc : b = c := funext h
  subst hbc
  simp

@[simp] theorem block_self_mem (P : SigAlg Ω) (x : Ω) : x ∈ P.block x := P.mem_block x

theorem block_eq_of_mem {P : SigAlg Ω} {x y : Ω} (h : y ∈ P.block x) : P.block y = P.block x :=
  P.block_eq h

theorem mem_block_iff {P : SigAlg Ω} {x y : Ω} : y ∈ P.block x ↔ P.block y = P.block x :=
  ⟨P.block_eq, fun h => h ▸ P.mem_block y⟩

/-- The trivial (one-block) partition. -/
def triv : SigAlg Ω where
  block := fun _ => Finset.univ
  mem_block := fun _ => Finset.mem_univ _
  block_eq := fun _ => rfl

@[simp] theorem triv_block (x : Ω) : (triv : SigAlg Ω).block x = Finset.univ := rfl

/-- Join (common refinement) of two partitions. -/
def join (P Q : SigAlg Ω) : SigAlg Ω where
  block := fun x => P.block x ∩ Q.block x
  mem_block := fun x => Finset.mem_inter.mpr ⟨P.mem_block x, Q.mem_block x⟩
  block_eq := by
    intro x y hy
    rw [Finset.mem_inter] at hy
    rw [P.block_eq hy.1, Q.block_eq hy.2]

@[simp] theorem join_block (P Q : SigAlg Ω) (x : Ω) :
    (P.join Q).block x = P.block x ∩ Q.block x := rfl

/-- Join of a finite family of partitions, indexed by a finset. -/
def iInf {ι : Type*} (P : ι → SigAlg Ω) (s : Finset ι) : SigAlg Ω where
  block := fun x => s.inf (fun i => (P i).block x)
  mem_block := by
    intro x
    rw [Finset.mem_inf]
    intro i _
    exact (P i).mem_block x
  block_eq := by
    intro x y hy
    change y ∈ s.inf (fun i => (P i).block x) at hy
    rw [Finset.mem_inf] at hy
    refine Finset.inf_congr rfl (fun i hi => ?_)
    exact (P i).block_eq (hy i hi)

@[simp] theorem iInf_block {ι : Type*} (P : ι → SigAlg Ω) (s : Finset ι) (x : Ω) :
    (SigAlg.iInf P s).block x = s.inf (fun i => (P i).block x) := rfl

/-- `P.Refines Q` means that `Q` is finer than `P`: every block of `Q` lies in a
block of `P`. -/
def Refines (P Q : SigAlg Ω) : Prop := ∀ x, Q.block x ⊆ P.block x

theorem Refines.refl (P : SigAlg Ω) : P.Refines P := fun _ => subset_rfl

theorem Refines.trans {P Q R : SigAlg Ω} (h₁ : P.Refines Q) (h₂ : Q.Refines R) : P.Refines R :=
  fun x => Subset.trans (h₂ x) (h₁ x)

theorem Refines.join_left (P Q : SigAlg Ω) : P.Refines (P.join Q) :=
  fun _ => Finset.inter_subset_left

theorem Refines.join_right (P Q : SigAlg Ω) : Q.Refines (P.join Q) :=
  fun _ => Finset.inter_subset_right

theorem Refines.iInf {ι : Type*} (P : ι → SigAlg Ω) (s : Finset ι) (i : ι) (hi : i ∈ s) :
    (P i).Refines (SigAlg.iInf P s) := by
  intro x y hy
  rw [iInf_block, Finset.mem_inf] at hy
  exact hy i hi

/-- A set is measurable for the partition `P` when it is a union of blocks. -/
def IsMeas (P : SigAlg Ω) (E : Finset Ω) : Prop := ∀ x ∈ E, P.block x ⊆ E

theorem isMeas_block (P : SigAlg Ω) (x : Ω) : P.IsMeas (P.block x) := by
  intro y hy z hz
  rw [← P.block_eq hy]
  exact hz

theorem isMeas_univ (P : SigAlg Ω) : P.IsMeas Finset.univ := fun _ _ => subset_univ _

theorem isMeas_empty (P : SigAlg Ω) : P.IsMeas ∅ := fun _ h => absurd h (Finset.notMem_empty _)

theorem IsMeas.union {P : SigAlg Ω} {E F : Finset Ω} (hE : P.IsMeas E) (hF : P.IsMeas F) :
    P.IsMeas (E ∪ F) := by
  intro x hx
  rw [Finset.mem_union] at hx
  exact hx.elim (fun h => Subset.trans (hE x h) Finset.subset_union_left)
    (fun h => Subset.trans (hF x h) Finset.subset_union_right)

theorem IsMeas.inter {P : SigAlg Ω} {E F : Finset Ω} (hE : P.IsMeas E) (hF : P.IsMeas F) :
    P.IsMeas (E ∩ F) := by
  intro x hx
  rw [Finset.mem_inter] at hx
  intro y hy
  exact Finset.mem_inter.mpr ⟨hE x hx.1 hy, hF x hx.2 hy⟩

theorem IsMeas.compl {P : SigAlg Ω} {E : Finset Ω} (hE : P.IsMeas E) : P.IsMeas Eᶜ := by
  intro x hx
  rw [Finset.mem_compl] at hx
  intro y hy
  rw [Finset.mem_compl]
  intro hyE
  exact hx (hE y hyE (by rw [P.block_eq hy]; exact P.mem_block x))

theorem IsMeas.sdiff {P : SigAlg Ω} {E F : Finset Ω} (hE : P.IsMeas E) (hF : P.IsMeas F) :
    P.IsMeas (E \ F) := by
  rw [Finset.sdiff_eq_inter_compl]
  exact hE.inter hF.compl

theorem isMeas_iff (P : SigAlg Ω) (E : Finset Ω) :
    P.IsMeas E ↔ ∀ x y, y ∈ P.block x → (y ∈ E ↔ x ∈ E) := by
  constructor
  · intro h x y hy
    constructor
    · intro hyE
      exact h y hyE (by rw [P.block_eq hy]; exact P.mem_block x)
    · intro hxE
      exact h x hxE hy
  · intro h x hx
    intro y hy
    exact (h x y hy).mpr hx

theorem IsMeas.of_refines {P Q : SigAlg Ω} (h : P.Refines Q) {E : Finset Ω} (hE : P.IsMeas E) :
    Q.IsMeas E := by
  intro x hx y hy
  exact hE x hx (h x hy)

/-- The uniform average of a real-valued function over `Ω`. -/
noncomputable def avg (f : Ω → ℝ) : ℝ := (∑ x, f x) / (Fintype.card Ω : ℝ)

/-- The conditional expectation of `f` with respect to the partition `P`. -/
noncomputable def condExp (P : SigAlg Ω) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => (∑ y ∈ P.block x, f y) / ((P.block x).card : ℝ)

theorem condExp_blockConst (P : SigAlg Ω) (f : Ω → ℝ) :
    ∀ x y, y ∈ P.block x → P.condExp f y = P.condExp f x := by
  intro x y hy
  unfold condExp
  rw [P.block_eq hy]

theorem condExp_of_blockConst {P : SigAlg Ω} {f : Ω → ℝ}
    (h : ∀ x y, y ∈ P.block x → f y = f x) : P.condExp f = f := by
  funext x
  unfold condExp
  have hconst : ∀ y ∈ P.block x, f y = f x := fun y hy => h x y hy
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hpos : (0 : ℝ) < ((P.block x).card : ℝ) := by
    have : 0 < (P.block x).card := Finset.card_pos.mpr ⟨x, P.mem_block x⟩
    exact_mod_cast this
  field_simp

theorem condExp_const (P : SigAlg Ω) (c : ℝ) : P.condExp (fun _ => c) = fun _ => c :=
  condExp_of_blockConst (fun _ _ _ => rfl)

theorem condExp_add (P : SigAlg Ω) (f g : Ω → ℝ) :
    P.condExp (fun x => f x + g x) = fun x => P.condExp f x + P.condExp g x := by
  funext x
  unfold condExp
  rw [Finset.sum_add_distrib, add_div]

theorem condExp_const_mul (P : SigAlg Ω) (c : ℝ) (f : Ω → ℝ) :
    P.condExp (fun x => c * f x) = fun x => c * P.condExp f x := by
  funext x
  unfold condExp
  rw [← Finset.mul_sum, mul_div_assoc]

theorem condExp_idem (P : SigAlg Ω) (f : Ω → ℝ) : P.condExp (P.condExp f) = P.condExp f :=
  condExp_of_blockConst (fun x y hy => condExp_blockConst P f x y hy)

/-- The indicator function of a finite set. -/
noncomputable def indicator (E : Finset Ω) : Ω → ℝ := fun x => if x ∈ E then 1 else 0

theorem condExp_indicator {P : SigAlg Ω} {E : Finset Ω} (hE : P.IsMeas E) :
    P.condExp (indicator E) = indicator E := by
  refine condExp_of_blockConst ?_
  intro x y hy
  have hiff := (isMeas_iff P E).mp hE x y hy
  unfold indicator
  by_cases hx : x ∈ E
  · have hy' : y ∈ E := hiff.mpr hx
    rw [if_pos hy', if_pos hx]
  · have hy' : y ∉ E := fun h => hx (hiff.mp h)
    rw [if_neg hy', if_neg hx]

/-! ## Atoms -/

/-- The set of blocks (atoms) of a partition. -/
noncomputable def atoms (P : SigAlg Ω) : Finset (Finset Ω) := Finset.univ.image P.block

theorem mem_atoms {P : SigAlg Ω} {s : Finset Ω} : s ∈ P.atoms ↔ ∃ x, P.block x = s := by
  simp [atoms]

theorem block_mem_atoms (P : SigAlg Ω) (x : Ω) : P.block x ∈ P.atoms := mem_atoms.mpr ⟨x, rfl⟩

theorem eq_of_mem_atoms {P : SigAlg Ω} {s : Finset Ω} (hs : s ∈ P.atoms) {y : Ω} (hy : y ∈ s) :
    P.block y = s := by
  obtain ⟨x, rfl⟩ := mem_atoms.mp hs
  exact P.block_eq hy

theorem atoms_nonempty {P : SigAlg Ω} {s : Finset Ω} (hs : s ∈ P.atoms) : s.Nonempty := by
  obtain ⟨x, rfl⟩ := mem_atoms.mp hs
  exact ⟨x, P.mem_block x⟩

theorem atoms_pairwiseDisjoint (P : SigAlg Ω) :
    (↑P.atoms : Set (Finset Ω)).PairwiseDisjoint id := by
  intro s hs t ht hst
  change Disjoint s t
  rw [Finset.disjoint_iff_inter_eq_empty]
  ext y
  simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
  intro hys hyt
  exact hst ((eq_of_mem_atoms hs hys).symm.trans (eq_of_mem_atoms ht hyt))

theorem biUnion_atoms (P : SigAlg Ω) : P.atoms.biUnion id = Finset.univ := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
  exact ⟨P.block x, block_mem_atoms P x, P.mem_block x⟩

theorem sum_atoms (P : SigAlg Ω) (f : Ω → ℝ) :
    ∑ s ∈ P.atoms, ∑ x ∈ s, f x = ∑ x, f x := by
  have h := Finset.sum_biUnion (s := P.atoms) (t := id) (f := f) P.atoms_pairwiseDisjoint
  rw [P.biUnion_atoms] at h
  exact h.symm

theorem sum_card_atoms (P : SigAlg Ω) : ∑ s ∈ P.atoms, s.card = Fintype.card Ω := by
  have h := Finset.card_biUnion (s := P.atoms) (t := id) (M := Ω) P.atoms_pairwiseDisjoint
  rw [P.biUnion_atoms, Finset.card_univ] at h
  exact h.symm

/-- The atoms of `Q` inside a fixed atom `t` of a coarser partition `P`. -/
theorem biUnion_filter_atoms {P Q : SigAlg Ω} (h : P.Refines Q) {t : Finset Ω}
    (ht : t ∈ P.atoms) : (Q.atoms.filter (fun s => s ⊆ t)).biUnion id = t := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hs).2 hxs
  · intro hx
    refine Finset.mem_biUnion.mpr
      ⟨Q.block x, Finset.mem_filter.mpr ⟨block_mem_atoms Q x, ?_⟩, Q.mem_block x⟩
    intro y hy
    rw [← eq_of_mem_atoms ht hx]
    exact h x hy

theorem disjoint_filter_atoms {P Q : SigAlg Ω} {t t' : Finset Ω} (ht : t ∈ P.atoms)
    (ht' : t' ∈ P.atoms) (htt' : t ≠ t') :
    Disjoint (Q.atoms.filter (fun s => s ⊆ t)) (Q.atoms.filter (fun s => s ⊆ t')) := by
  change Disjoint (Q.atoms.filter (fun s => s ⊆ t)) (Q.atoms.filter (fun s => s ⊆ t'))
  rw [Finset.disjoint_iff_inter_eq_empty]
  ext s
  constructor
  · intro hs
    rw [Finset.mem_inter] at hs
    obtain ⟨hsQ, hst⟩ := Finset.mem_filter.mp hs.1
    obtain ⟨-, hst'⟩ := Finset.mem_filter.mp hs.2
    obtain ⟨y, hy⟩ := atoms_nonempty hsQ
    exact absurd ((eq_of_mem_atoms ht (hst hy)).symm.trans (eq_of_mem_atoms ht' (hst' hy))) htt'
  · intro hs
    exact absurd hs (Finset.notMem_empty s)

theorem pairwiseDisjoint_filter_atoms (P Q : SigAlg Ω) :
    (↑P.atoms : Set (Finset Ω)).PairwiseDisjoint (fun t => Q.atoms.filter (fun s => s ⊆ t)) :=
  fun t ht t' ht' htt' => disjoint_filter_atoms ht ht' htt'

theorem sum_atoms_eq_sum_filter {P Q : SigAlg Ω} (h : P.Refines Q) (g : Finset Ω → ℝ) :
    ∑ s ∈ Q.atoms, g s = ∑ t ∈ P.atoms, ∑ s ∈ Q.atoms.filter (fun s => s ⊆ t), g s := by
  rw [← Finset.sum_biUnion (s := P.atoms)
    (t := fun t => Q.atoms.filter (fun s => s ⊆ t)) (f := g) (pairwiseDisjoint_filter_atoms P Q)]
  congr 1
  ext s
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := atoms_nonempty hs
    refine Finset.mem_biUnion.mpr ⟨P.block x, block_mem_atoms P x, ?_⟩
    refine Finset.mem_filter.mpr ⟨hs, ?_⟩
    intro y hy
    have hys : Q.block y = s := eq_of_mem_atoms hs hy
    have h1 : x ∈ Q.block y := by rw [hys]; exact hx
    have h2 : x ∈ P.block y := h y h1
    rw [P.block_eq h2]
    exact P.mem_block y
  · intro hs
    obtain ⟨t, _, hst⟩ := Finset.mem_biUnion.mp hs
    exact (Finset.mem_filter.mp hst).1

theorem sum_filter_atoms {P Q : SigAlg Ω} (h : P.Refines Q) {t : Finset Ω} (ht : t ∈ P.atoms)
    (f : Ω → ℝ) :
    ∑ s ∈ Q.atoms.filter (fun s => s ⊆ t), ∑ x ∈ s, f x = ∑ x ∈ t, f x := by
  have hpd : (↑(Q.atoms.filter (fun s => s ⊆ t)) : Set (Finset Ω)).PairwiseDisjoint
      (fun s : Finset Ω => s) := by
    intro s hs s' hs' hss
    exact Q.atoms_pairwiseDisjoint (Finset.mem_of_mem_filter s hs)
      (Finset.mem_of_mem_filter s' hs') hss
  rw [← Finset.sum_biUnion (s := Q.atoms.filter (fun s => s ⊆ t)) (t := fun s : Finset Ω => s)
    (f := f) hpd,
    show (Q.atoms.filter (fun s => s ⊆ t)).biUnion (fun s : Finset Ω => s) = t
      from biUnion_filter_atoms h ht]

theorem card_filter_atoms {P Q : SigAlg Ω} (h : P.Refines Q) {t : Finset Ω} (ht : t ∈ P.atoms) :
    ∑ s ∈ Q.atoms.filter (fun s => s ⊆ t), s.card = t.card := by
  have hpd : (↑(Q.atoms.filter (fun s => s ⊆ t)) : Set (Finset Ω)).PairwiseDisjoint
      (fun s : Finset Ω => s) := by
    intro s hs s' hs' hss
    exact Q.atoms_pairwiseDisjoint (Finset.mem_of_mem_filter s hs)
      (Finset.mem_of_mem_filter s' hs') hss
  rw [← Finset.card_biUnion (s := Q.atoms.filter (fun s => s ⊆ t)) (t := fun s : Finset Ω => s)
    (M := Ω) hpd,
    show (Q.atoms.filter (fun s => s ⊆ t)).biUnion (fun s : Finset Ω => s) = t
      from biUnion_filter_atoms h ht]

end SigAlg

section AvgEnergy

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

namespace SigAlg

theorem card_cast_pos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by
  have h : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr inferInstance
  exact_mod_cast h

theorem card_cast_ne_zero : (Fintype.card Ω : ℝ) ≠ 0 := ne_of_gt card_cast_pos

theorem avg_const (c : ℝ) : avg (fun _ : Ω => c) = c := by
  unfold avg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem avg_add (f g : Ω → ℝ) : avg (fun x => f x + g x) = avg f + avg g := by
  unfold avg
  rw [Finset.sum_add_distrib, add_div]

theorem avg_mul_const (c : ℝ) (f : Ω → ℝ) : avg (fun x => c * f x) = c * avg f := by
  unfold avg
  rw [← Finset.mul_sum]
  ring

theorem avg_nonneg {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ avg f :=
  div_nonneg (Finset.sum_nonneg (fun x _ => hf x)) (le_of_lt card_cast_pos)

theorem avg_le_avg {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : avg f ≤ avg g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (le_of_lt card_cast_pos)

theorem sum_condExp (P : SigAlg Ω) (f : Ω → ℝ) : ∑ x, P.condExp f x = ∑ x, f x := by
  rw [← P.sum_atoms (fun x => P.condExp f x), ← P.sum_atoms f]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  have hconst : ∀ x ∈ s, P.condExp f x = (∑ y ∈ s, f y) / (s.card : ℝ) := by
    intro x hx
    unfold condExp
    rw [eq_of_mem_atoms hs hx]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hc : (s.card : ℝ) ≠ 0 := by
    have h : 0 < s.card := Finset.card_pos.mpr (atoms_nonempty hs)
    exact_mod_cast ne_of_gt h
  field_simp

theorem avg_condExp (P : SigAlg Ω) (f : Ω → ℝ) : avg (P.condExp f) = avg f := by
  unfold avg
  rw [P.sum_condExp]

theorem sum_sub_condExp (P : SigAlg Ω) {s : Finset Ω} (hs : s ∈ P.atoms) (f : Ω → ℝ) :
    ∑ x ∈ s, (f x - P.condExp f x) = 0 := by
  have hconst : ∀ x ∈ s, P.condExp f x = (∑ y ∈ s, f y) / (s.card : ℝ) := by
    intro x hx
    unfold condExp
    rw [eq_of_mem_atoms hs hx]
  rw [Finset.sum_sub_distrib, Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hc : (s.card : ℝ) ≠ 0 := by
    have h : 0 < s.card := Finset.card_pos.mpr (atoms_nonempty hs)
    exact_mod_cast ne_of_gt h
  field_simp
  ring

theorem avg_mul_sub_condExp (P : SigAlg Ω) {g f : Ω → ℝ}
    (hg : ∀ x y, y ∈ P.block x → g y = g x) :
    avg (fun x => g x * (f x - P.condExp f x)) = 0 := by
  unfold avg
  rw [← P.sum_atoms (fun x => g x * (f x - P.condExp f x))]
  have hzero : ∑ s ∈ P.atoms, ∑ x ∈ s, g x * (f x - P.condExp f x) = 0 := by
    refine Finset.sum_eq_zero (fun s hs => ?_)
    obtain ⟨x₀, hx₀⟩ := atoms_nonempty hs
    have hgc : ∀ x ∈ s, g x = g x₀ := by
      intro x hx
      exact hg x₀ x (by rw [eq_of_mem_atoms hs hx₀]; exact hx)
    rw [Finset.sum_congr rfl (fun x hx => by rw [hgc x hx]), ← Finset.mul_sum,
      P.sum_sub_condExp hs f, mul_zero]
  rw [hzero, zero_div]

theorem condExp_tower_apply {P Q : SigAlg Ω} (h : P.Refines Q) (f : Ω → ℝ) (x : Ω) :
    P.condExp (Q.condExp f) x = P.condExp f x := by
  have hsum : ∑ y ∈ P.block x, Q.condExp f y = ∑ y ∈ P.block x, f y := by
    rw [← P.sum_filter_atoms h (block_mem_atoms P x) (Q.condExp f),
      ← P.sum_filter_atoms h (block_mem_atoms P x) f]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    obtain ⟨hsQ, _⟩ := Finset.mem_filter.mp hs
    have hconst : ∀ y ∈ s, Q.condExp f y = (∑ z ∈ s, f z) / (s.card : ℝ) := by
      intro y hy
      unfold condExp
      rw [eq_of_mem_atoms hsQ hy]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hc : (s.card : ℝ) ≠ 0 := by
      have hpos : 0 < s.card := Finset.card_pos.mpr (atoms_nonempty hsQ)
      exact_mod_cast ne_of_gt hpos
    field_simp
  show (∑ y ∈ P.block x, Q.condExp f y) / ((P.block x).card : ℝ)
      = (∑ y ∈ P.block x, f y) / ((P.block x).card : ℝ)
  rw [hsum]

theorem condExp_tower {P Q : SigAlg Ω} (h : P.Refines Q) (f : Ω → ℝ) :
    P.condExp (Q.condExp f) = P.condExp f :=
  funext (condExp_tower_apply h f)

/-- The energy (mean square conditional expectation) of `f` with respect to `P`. -/
noncomputable def energy (P : SigAlg Ω) (f : Ω → ℝ) : ℝ := avg (fun x => (P.condExp f x) ^ 2)

theorem energy_unfold (P : SigAlg Ω) (f : Ω → ℝ) :
    P.energy f
      = (∑ s ∈ P.atoms, ((∑ x ∈ s, f x) ^ 2) / (s.card : ℝ)) / (Fintype.card Ω : ℝ) := by
  unfold energy avg
  rw [← P.sum_atoms (fun x => (P.condExp f x) ^ 2)]
  congr 1
  refine Finset.sum_congr rfl (fun s hs => ?_)
  have hconst : ∀ x ∈ s, (P.condExp f x) ^ 2 = ((∑ y ∈ s, f y) / (s.card : ℝ)) ^ 2 := by
    intro x hx
    unfold condExp
    rw [eq_of_mem_atoms hs hx]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hc : (s.card : ℝ) ≠ 0 := by
    have h : 0 < s.card := Finset.card_pos.mpr (atoms_nonempty hs)
    exact_mod_cast ne_of_gt h
  field_simp

theorem energy_nonneg (P : SigAlg Ω) (f : Ω → ℝ) : 0 ≤ P.energy f := by
  rw [energy_unfold]
  exact div_nonneg (Finset.sum_nonneg (fun s _ => div_nonneg (sq_nonneg _) (by positivity)))
    (le_of_lt card_cast_pos)

theorem energy_le_avg_sq (P : SigAlg Ω) (f : Ω → ℝ) : P.energy f ≤ avg (fun x => (f x) ^ 2) := by
  rw [energy_unfold]
  unfold avg
  refine div_le_div_of_nonneg_right ?_ (le_of_lt card_cast_pos)
  calc ∑ s ∈ P.atoms, ((∑ x ∈ s, f x) ^ 2) / (s.card : ℝ)
      ≤ ∑ s ∈ P.atoms, ∑ x ∈ s, (f x) ^ 2 := by
        refine Finset.sum_le_sum (fun s hs => ?_)
        have hc : (0 : ℝ) < (s.card : ℝ) := by
          have h : 0 < s.card := Finset.card_pos.mpr (atoms_nonempty hs)
          exact_mod_cast h
        rw [div_le_iff₀ hc]
        calc (∑ x ∈ s, f x) ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, f x ^ 2 :=
              sq_sum_le_card_mul_sum_sq (s := s) (f := f)
          _ = (∑ x ∈ s, f x ^ 2) * (s.card : ℝ) := mul_comm _ _
    _ = ∑ x, (f x) ^ 2 := P.sum_atoms (fun x => (f x) ^ 2)

/-- **Pythagoras' identity**: refining a partition increases the energy by the mean
square of the difference of the conditional expectations. -/
theorem energy_eq_energy_add {P Q : SigAlg Ω} (h : P.Refines Q) (f : Ω → ℝ) :
    Q.energy f = P.energy f + avg (fun x => (Q.condExp f x - P.condExp f x) ^ 2) := by
  have hgc : ∀ x y, y ∈ Q.block x → P.condExp f y = P.condExp f x :=
    fun x y hy => condExp_blockConst P f x y (h x hy)
  have horth : avg (fun x => P.condExp f x * (Q.condExp f x - P.condExp f x)) = 0 := by
    have h1 : avg (fun x => P.condExp f x * (Q.condExp f x - P.condExp (Q.condExp f) x)) = 0 :=
      P.avg_mul_sub_condExp (g := P.condExp f) (f := Q.condExp f)
        (fun x y hy => condExp_blockConst P f x y hy)
    rwa [show (fun x => P.condExp f x * (Q.condExp f x - P.condExp (Q.condExp f) x))
        = (fun x => P.condExp f x * (Q.condExp f x - P.condExp f x)) from
      funext (fun x => by rw [condExp_tower_apply h f x])] at h1
  have hpt : ∀ x : Ω, (Q.condExp f x) ^ 2
      = (Q.condExp f x - P.condExp f x) ^ 2
        + 2 * (P.condExp f x * (Q.condExp f x - P.condExp f x)) + (P.condExp f x) ^ 2 := by
    intro x
    ring
  calc Q.energy f = avg (fun x => (Q.condExp f x) ^ 2) := rfl
    _ = avg (fun x => (Q.condExp f x - P.condExp f x) ^ 2
          + 2 * (P.condExp f x * (Q.condExp f x - P.condExp f x)) + (P.condExp f x) ^ 2) := by
        congr 1
        funext x
        exact hpt x
    _ = avg (fun x => (Q.condExp f x - P.condExp f x) ^ 2)
          + avg (fun x => 2 * (P.condExp f x * (Q.condExp f x - P.condExp f x)))
          + avg (fun x => (P.condExp f x) ^ 2) := by
        rw [avg_add, avg_add]
    _ = P.energy f + avg (fun x => (Q.condExp f x - P.condExp f x) ^ 2) := by
        rw [avg_mul_const, horth]
        unfold energy
        ring

/-- Complexity of a partition: the (ceiling of the) logarithm of the number of atoms. -/
noncomputable def complexity (P : SigAlg Ω) : ℕ := Nat.clog 2 P.atoms.card

theorem atoms_card_le_pow_complexity (P : SigAlg Ω) : P.atoms.card ≤ 2 ^ P.complexity :=
  Nat.le_pow_clog (by norm_num) _

theorem complexity_le_of_card_le {P : SigAlg Ω} {m : ℕ} (h : P.atoms.card ≤ 2 ^ m) :
    P.complexity ≤ m :=
  (Nat.clog_le_iff_le_pow (by norm_num)).mpr h

end SigAlg

end AvgEnergy


section AddSet

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace SigAlg

/-- Refine a partition by separating the set `E`: the join of `P` with the
two-block partition `{E, Eᶜ}`. -/
def addSet (P : SigAlg Ω) (E : Finset Ω) : SigAlg Ω where
  block := fun x => if x ∈ E then P.block x ∩ E else P.block x \ E
  mem_block := by
    intro x
    by_cases h : x ∈ E
    · rw [if_pos h]
      exact Finset.mem_inter.mpr ⟨P.mem_block x, h⟩
    · rw [if_neg h]
      exact Finset.mem_sdiff.mpr ⟨P.mem_block x, h⟩
  block_eq := by
    intro x y hy
    by_cases hx : x ∈ E
    · rw [if_pos hx] at hy
      rw [Finset.mem_inter] at hy
      rw [if_pos hx, if_pos hy.2, P.block_eq hy.1]
    · rw [if_neg hx] at hy
      rw [Finset.mem_sdiff] at hy
      rw [if_neg hx, if_neg hy.2, P.block_eq hy.1]

@[simp] theorem addSet_block_of_mem (P : SigAlg Ω) (E : Finset Ω) {x : Ω} (hx : x ∈ E) :
    (P.addSet E).block x = P.block x ∩ E := if_pos hx

@[simp] theorem addSet_block_of_not_mem (P : SigAlg Ω) (E : Finset Ω) {x : Ω} (hx : x ∉ E) :
    (P.addSet E).block x = P.block x \ E := if_neg hx

theorem Refines.addSet (P : SigAlg Ω) (E : Finset Ω) : P.Refines (P.addSet E) := by
  intro x y hy
  by_cases hx : x ∈ E
  · rw [addSet_block_of_mem P E hx] at hy
    exact (Finset.mem_inter.mp hy).1
  · rw [addSet_block_of_not_mem P E hx] at hy
    exact (Finset.mem_sdiff.mp hy).1

/-- If `P` is coarser than `Q` and `E` is `Q`-measurable, then adjoining `E` to `P`
keeps `P.addSet E` coarser than `Q`. -/
theorem Refines.addSet_of_isMeas {P Q : SigAlg Ω} {E : Finset Ω} (h : P.Refines Q)
    (hE : Q.IsMeas E) : (P.addSet E).Refines Q := by
  intro x y hy
  by_cases hx : x ∈ E
  · rw [addSet_block_of_mem P E hx, Finset.mem_inter]
    exact ⟨h x hy, hE x hx hy⟩
  · rw [addSet_block_of_not_mem P E hx, Finset.mem_sdiff]
    refine ⟨h x hy, fun hyE => hx ?_⟩
    have hyx : Q.block y = Q.block x := Q.block_eq hy
    exact hE y hyE (hyx.symm ▸ Q.mem_block x)

theorem isMeas_addSet_self (P : SigAlg Ω) (E : Finset Ω) : (P.addSet E).IsMeas E := by
  intro x hx
  rw [addSet_block_of_mem P E hx]
  exact Finset.inter_subset_right

theorem isMeas_addSet_compl (P : SigAlg Ω) (E : Finset Ω) : (P.addSet E).IsMeas Eᶜ := by
  intro x hx
  rw [Finset.mem_compl] at hx
  rw [addSet_block_of_not_mem P E hx]
  intro y hy
  rw [Finset.mem_compl]
  exact (Finset.mem_sdiff.mp hy).2

theorem atoms_congr {P Q : SigAlg Ω} (h : ∀ x, P.block x = Q.block x) : P.atoms = Q.atoms := by
  rw [atoms, atoms]
  congr 1
  funext x
  exact h x

theorem atoms_addSet_subset (P : SigAlg Ω) (E : Finset Ω) :
    (P.addSet E).atoms ⊆ (P.atoms.image (fun s => s ∩ E)) ∪ (P.atoms.image (fun s => s \ E)) := by
  intro s hs
  obtain ⟨x, rfl⟩ := mem_atoms.mp hs
  by_cases hx : x ∈ E
  · rw [addSet_block_of_mem P E hx]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨P.block x, block_mem_atoms P x, rfl⟩)
  · rw [addSet_block_of_not_mem P E hx]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨P.block x, block_mem_atoms P x, rfl⟩)

theorem atoms_addSet_card_le (P : SigAlg Ω) (E : Finset Ω) :
    (P.addSet E).atoms.card ≤ 2 * P.atoms.card := by
  calc (P.addSet E).atoms.card
      ≤ ((P.atoms.image (fun s => s ∩ E)) ∪ (P.atoms.image (fun s => s \ E))).card :=
        Finset.card_le_card (P.atoms_addSet_subset E)
    _ ≤ (P.atoms.image (fun s => s ∩ E)).card + (P.atoms.image (fun s => s \ E)).card :=
        Finset.card_union_le _ _
    _ ≤ P.atoms.card + P.atoms.card := by
        have h1 : (P.atoms.image (fun s => s ∩ E)).card ≤ P.atoms.card := Finset.card_image_le
        have h2 : (P.atoms.image (fun s => s \ E)).card ≤ P.atoms.card := Finset.card_image_le
        omega
    _ = 2 * P.atoms.card := by ring

theorem complexity_addSet_le (P : SigAlg Ω) (E : Finset Ω) :
    (P.addSet E).complexity ≤ P.complexity + 1 := by
  have hclog2 : Nat.clog 2 2 = 1 := by simpa using Nat.clog_pow 2 1 (by norm_num)
  rw [complexity, complexity]
  have hstep : Nat.clog 2 (2 * P.atoms.card) ≤ Nat.clog 2 2 + Nat.clog 2 P.atoms.card := by
    rw [Nat.clog_le_iff_le_pow (by norm_num), hclog2, pow_add, pow_one]
    exact Nat.mul_le_mul_left 2 (Nat.le_pow_clog (by norm_num) _)
  calc Nat.clog 2 (P.addSet E).atoms.card ≤ Nat.clog 2 (2 * P.atoms.card) :=
        Nat.clog_mono_right 2 (P.atoms_addSet_card_le E)
    _ ≤ Nat.clog 2 2 + Nat.clog 2 P.atoms.card := hstep
    _ = Nat.clog 2 P.atoms.card + 1 := by rw [hclog2, Nat.add_comm]

theorem atoms_join_card_le (P Q : SigAlg Ω) :
    (P.join Q).atoms.card ≤ P.atoms.card * Q.atoms.card := by
  calc (P.join Q).atoms.card
      ≤ ((P.atoms.product Q.atoms).image (fun pq : Finset Ω × Finset Ω => pq.1 ∩ pq.2)).card := by
        apply Finset.card_le_card
        intro s hs
        obtain ⟨x, rfl⟩ := mem_atoms.mp hs
        rw [join_block]
        exact Finset.mem_image.mpr ⟨(P.block x, Q.block x),
          Finset.mem_product.mpr ⟨block_mem_atoms P x, block_mem_atoms Q x⟩, rfl⟩
    _ ≤ (P.atoms.product Q.atoms).card := Finset.card_image_le
    _ = P.atoms.card * Q.atoms.card := Finset.card_product _ _

theorem complexity_join_le (P Q : SigAlg Ω) :
    (P.join Q).complexity ≤ P.complexity + Q.complexity := by
  rw [complexity, complexity, complexity]
  calc Nat.clog 2 (P.join Q).atoms.card
      ≤ Nat.clog 2 (P.atoms.card * Q.atoms.card) :=
        Nat.clog_mono_right 2 (P.atoms_join_card_le Q)
    _ ≤ Nat.clog 2 P.atoms.card + Nat.clog 2 Q.atoms.card := by
        rw [Nat.clog_le_iff_le_pow (by norm_num)]
        calc P.atoms.card * Q.atoms.card
            ≤ 2 ^ Nat.clog 2 P.atoms.card * 2 ^ Nat.clog 2 Q.atoms.card :=
              Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) _) (Nat.le_pow_clog (by norm_num) _)
          _ = 2 ^ (Nat.clog 2 P.atoms.card + Nat.clog 2 Q.atoms.card) := (pow_add _ _ _).symm

theorem atoms_iInf_card_le {κ : Type*} (B : κ → SigAlg Ω) (s : Finset κ) :
    (SigAlg.iInf B s).atoms.card ≤ s.prod (fun i => (B i).atoms.card) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.prod_empty]
      by_cases hΩ : Nonempty Ω
      · have h1 : (SigAlg.iInf B ∅).atoms = {Finset.univ} := by
          ext t
          rw [mem_atoms, Finset.mem_singleton]
          constructor
          · rintro ⟨x, rfl⟩
            rw [iInf_block, Finset.inf_empty]
            rfl
          · intro ht
            exact ⟨hΩ.some, by rw [ht, iInf_block, Finset.inf_empty]; rfl⟩
        rw [h1]
        simp
      · rw [not_nonempty_iff] at hΩ
        haveI := hΩ
        rw [atoms]
        simp
  | cons a s ha ih =>
      rw [Finset.prod_cons ha]
      have hblocks : ∀ x : Ω,
          (SigAlg.iInf B (Finset.cons a s ha)).block x
            = ((B a).join (SigAlg.iInf B s)).block x := by
        intro x
        rw [iInf_block, Finset.inf_cons ha, join_block, iInf_block, Finset.inf_eq_inter]
      rw [atoms_congr hblocks]
      calc ((B a).join (SigAlg.iInf B s)).atoms.card
          ≤ (B a).atoms.card * (SigAlg.iInf B s).atoms.card := atoms_join_card_le _ _
        _ ≤ (B a).atoms.card * s.prod (fun i => (B i).atoms.card) :=
              Nat.mul_le_mul_left _ ih

theorem complexity_iInf_le {κ : Type*} (B : κ → SigAlg Ω) (s : Finset κ) :
    (SigAlg.iInf B s).complexity ≤ ∑ i ∈ s, (B i).complexity := by
  rw [complexity]
  calc Nat.clog 2 (SigAlg.iInf B s).atoms.card
      ≤ Nat.clog 2 (s.prod (fun i => (B i).atoms.card)) :=
        Nat.clog_mono_right 2 (atoms_iInf_card_le B s)
    _ ≤ ∑ i ∈ s, Nat.clog 2 (B i).atoms.card := by
        induction s using Finset.cons_induction with
        | empty => simp
        | cons a s ha ih =>
            rw [Finset.prod_cons ha, Finset.sum_cons ha]
            calc Nat.clog 2 ((B a).atoms.card * s.prod (fun i => (B i).atoms.card))
                ≤ Nat.clog 2 (B a).atoms.card + Nat.clog 2 (s.prod (fun i => (B i).atoms.card)) := by
                  rw [Nat.clog_le_iff_le_pow (by norm_num)]
                  calc (B a).atoms.card * s.prod (fun i => (B i).atoms.card)
                      ≤ 2 ^ Nat.clog 2 (B a).atoms.card *
                        2 ^ Nat.clog 2 (s.prod (fun i => (B i).atoms.card)) :=
                        Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) _)
                          (Nat.le_pow_clog (by norm_num) _)
                    _ = 2 ^ (Nat.clog 2 (B a).atoms.card +
                        Nat.clog 2 (s.prod (fun i => (B i).atoms.card))) := (pow_add _ _ _).symm
              _ ≤ Nat.clog 2 (B a).atoms.card + ∑ i ∈ s, Nat.clog 2 (B i).atoms.card :=
                  Nat.add_le_add_left ih _
    _ = ∑ i ∈ s, (B i).complexity := rfl

end SigAlg

end AddSet


section Extra

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

namespace SigAlg

theorem IsMeas.iInf {κ : Type*} {P : SigAlg Ω} {s : Finset κ} {E : κ → Finset Ω}
    (h : ∀ i ∈ s, P.IsMeas (E i)) : P.IsMeas (s.inf E) := by
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.inf_empty]
      exact P.isMeas_univ
  | cons a s ha ih =>
      rw [Finset.inf_cons ha, Finset.inf_eq_inter]
      exact (h a (Finset.mem_cons_self a s)).inter
        (ih (fun i hi => h i (Finset.mem_cons_of_mem hi)))

theorem avg_mul_sq_le (f g : Ω → ℝ) :
    (avg (fun x => f x * g x)) ^ 2 ≤ avg (fun x => (f x) ^ 2) * avg (fun x => (g x) ^ 2) := by
  have hcs : (∑ x, f x * g x) ^ 2 ≤ (∑ x, (f x) ^ 2) * ∑ x, (g x) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Ω) f g
  have h1 : avg (fun x => (f x) ^ 2) * avg (fun x => (g x) ^ 2)
      = ((∑ x, (f x) ^ 2) * (∑ x, (g x) ^ 2)) / (Fintype.card Ω : ℝ) ^ 2 := by
    simp only [avg]
    rw [div_mul_div_comm]
    ring
  have h2 : (avg (fun x => f x * g x)) ^ 2
      = ((∑ x, f x * g x)) ^ 2 / (Fintype.card Ω : ℝ) ^ 2 := by
    simp only [avg]
    rw [div_pow]
  rw [h1, h2]
  exact div_le_div_of_nonneg_right hcs (by positivity)

theorem avg_sq_le_avg_of_le_one {g : Ω → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    avg (fun x => (g x) ^ 2) ≤ 1 := by
  calc avg (fun x => (g x) ^ 2) ≤ avg (fun _ : Ω => (1 : ℝ)) :=
        avg_le_avg (fun x => by nlinarith [hg0 x, hg1 x])
    _ = 1 := avg_const 1

theorem avg_abs_le_of_le {f : Ω → ℝ} {c : ℝ} (h : ∀ x, |f x| ≤ c) : |avg f| ≤ c := by
  have h1 : avg f ≤ c := by
    calc avg f ≤ avg (fun _ : Ω => c) := avg_le_avg (fun x => (le_abs_self (f x)).trans (h x))
      _ = c := avg_const c
  have h2 : -c ≤ avg f := by
    calc -c = avg (fun _ : Ω => -c) := (avg_const (-c)).symm
      _ ≤ avg f := avg_le_avg (fun x => by
          have := (neg_le_abs (f x)).trans (h x); linarith)
  exact abs_le.mpr ⟨h2, h1⟩

end SigAlg

end Extra


section Extra2

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

namespace SigAlg

theorem Refines.iInf_mono {κ : Type*} {B B' : κ → SigAlg Ω} {s : Finset κ}
    (h : ∀ i ∈ s, (B i).Refines (B' i)) : (SigAlg.iInf B s).Refines (SigAlg.iInf B' s) := by
  intro x y hy
  rw [iInf_block] at hy ⊢
  rw [Finset.mem_inf] at hy ⊢
  intro i hi
  exact h i hi x (hy i hi)

theorem indicator_nonneg (E : Finset Ω) (x : Ω) : 0 ≤ indicator E x := by
  unfold indicator
  split <;> norm_num

theorem indicator_le_one (E : Finset Ω) (x : Ω) : indicator E x ≤ 1 := by
  unfold indicator
  split <;> norm_num

theorem indicator_mul (E F : Finset Ω) (x : Ω) :
    indicator E x * indicator F x = indicator (E ∩ F) x := by
  unfold indicator
  by_cases hE : x ∈ E <;> by_cases hF : x ∈ F <;> simp [hE, hF]

end SigAlg

end Extra2

end Szemeredi.Removal
