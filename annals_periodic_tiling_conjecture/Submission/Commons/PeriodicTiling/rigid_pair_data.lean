import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Mathlib.GroupTheory.Complement
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.RegularLocalRing.Defs

set_option autoImplicit true

/-!
# rigid_pair_data

The lemma `Commons.PeriodicTiling.rigid_pair_data` is the `s = 2` case of the
"rigid tuple of tiles" lemma of BGU (arXiv:2211.07140).  For any additive
subgroup `L` of `(Fin d → ℤ)` there is a dilation `N` and finite tiles
`T,T₁,T₂` with
(a) `T` rigid: the only complement containing `0` is `Nℤ^d` = `NV`,
(b) `Tⱼ + NL = T + NL` for `j = 1,2`,
(c) a pair `(C₁,C₂)` jointly tiles `ℤ^d` with `T₁,T₂` (and `0 ∈ C₁ ∪ C₂`)
    iff `C₁,C₂` is a disjoint partition of `NV` into `NL`-periodic sets.

This file develops the general tiling/complement machinery needed for the
BGU "jigsaw teeth" construction.

## Status (checkpoint)

Done and compiling:
* `V d`, `zimg`, `NV`, `NL`; `NV_subgroup`, `NL_subgroup` with `NL ≤ NV`;
  finiteness of `zimg` of finite sets; set-sum basics (`NV + NL = NV`, ...).
* `fin_family_generates_int_subgroup`: every `L ≤ ℤ^d` has a finite generating
  family of distinct non-zero elements (via Noetherian + `Finset.erase 0` +
  `Fintype.equivFin`).  This is the `w : Fin r → V d` used for the `NL`-teeth.

Next steps (in order):
1. Geometry layer: `box`, `shell` (L∞), translation vectors, `m`, `N = 2m+1`,
   teeth placements with margins; fundamental domain `NV ⊕ T = univ` and
   `Tⱼ = (T ∖ Xⱼ) ∪ (Xⱼ + N·uⱼ)` (moved-cell form) ⇒ `Tⱼ ⊕ NL = T ⊕ NL`.
2. Single-tile forcing theorem: any complement of `T` containing `0` is `NV`
   (the "click" case analysis: dent cells of `c+T` can only be covered by the
   translate at `c − N e_i`, disjointness forcing).
3. Pair forcing theorem: any joint tiling forces each `C_j` to be `NL`-periodic;
   solvability direction; assemble the final iff.
-/

open scoped Pointwise
open Set

namespace Commons
namespace PeriodicTiling

noncomputable section

abbrev V (d : ℕ) := Fin d → ℤ

def zimg {d : ℕ} (N : ℕ) (A : Set (V d)) : Set (V d) :=
  (fun x : V d => (N : ℤ) • x) '' A

lemma mem_zimg {d : ℕ} {N : ℕ} {x : V d} {A : Set (V d)} :
    x ∈ zimg N A ↔ ∃ a ∈ A, x = (N : ℤ) • a := by
  rw [zimg, Set.mem_image]
  constructor <;> rintro ⟨a, ha, h⟩ <;> exact ⟨a, ha, h.symm⟩

def NV (d : ℕ) (N : ℕ) : Set (V d) := zimg N Set.univ

def NL (d : ℕ) (N : ℕ) (L : AddSubgroup (V d)) : Set (V d) := zimg N (L : Set (V d))

lemma smul_add_pointwise {d : ℕ} (n : ℤ) (x y : V d) : n • (x + y) = n • x + n • y := by
  simp [smul_add]

lemma smul_neg_pointwise {d : ℕ} (n : ℤ) (x : V d) : n • (-x) = -(n • x) := by
  simp

lemma mem_zimg_iff_all_dvd {d : ℕ} {N : ℕ} {x : V d} :
    x ∈ NV d N ↔ ∀ i : Fin d, (N : ℤ) ∣ x i := by
  rw [NV, mem_zimg]
  constructor
  · rintro ⟨a, -, rfl⟩ i
    exact ⟨a i, by simp [Pi.smul_apply]⟩
  · intro hx
    refine ⟨fun i => Classical.choose (hx i), by simp, ?_⟩
    ext i
    simpa [Pi.smul_apply] using (Classical.choose_spec (hx i))

 /-- `NV = N·ℤ^d` is exactly the coordinatewise divisibility set: the bridge
between the zimg-based `NV` used in the theorem statement and the
divisibility-based `NV` used throughout the tile geometry. -/
lemma NV_divisibility_eq_zimg {d N : ℕ} :
    NV d N = {x : V d | ∀ i : Fin d, (N : ℤ) ∣ x i} := by
  ext x
  exact mem_zimg_iff_all_dvd (x := x)

def NV_subgroup (d : ℕ) (N : ℕ) : AddSubgroup (V d) where
  carrier := NV d N
  zero_mem' := by
    change (0 : V d) ∈ zimg N Set.univ
    rw [mem_zimg]
    exact ⟨0, by simp, by simp⟩
  add_mem' := by
    intro a b ha hb
    change a ∈ zimg N Set.univ at ha
    change b ∈ zimg N Set.univ at hb
    change a + b ∈ zimg N Set.univ
    rw [mem_zimg] at ha hb ⊢
    rcases ha with ⟨a₀, -, rfl⟩
    rcases hb with ⟨b₀, -, rfl⟩
    refine ⟨a₀ + b₀, by simp, ?_⟩
    simp [smul_add]
  neg_mem' := by
    intro a ha
    change a ∈ zimg N Set.univ at ha
    change -a ∈ zimg N Set.univ
    rw [mem_zimg] at ha ⊢
    rcases ha with ⟨a₀, -, rfl⟩
    refine ⟨-a₀, by simp, ?_⟩
    simp [smul_neg_pointwise]

def NL_subgroup (d : ℕ) (N : ℕ) (L : AddSubgroup (V d)) : AddSubgroup (V d) where
  carrier := NL d N L
  zero_mem' := by
    change (0 : V d) ∈ zimg N (L : Set (V d))
    rw [mem_zimg]
    exact ⟨0, zero_mem L, by simp⟩
  add_mem' := by
    intro a b ha hb
    change a ∈ zimg N (L : Set (V d)) at ha
    change b ∈ zimg N (L : Set (V d)) at hb
    change a + b ∈ zimg N (L : Set (V d))
    rw [mem_zimg] at ha hb ⊢
    rcases ha with ⟨a₀, ha₀, rfl⟩
    rcases hb with ⟨b₀, hb₀, rfl⟩
    refine ⟨a₀ + b₀, add_mem ha₀ hb₀, ?_⟩
    simp [smul_add]
  neg_mem' := by
    intro a ha
    change a ∈ zimg N (L : Set (V d)) at ha
    change -a ∈ zimg N (L : Set (V d))
    rw [mem_zimg] at ha ⊢
    rcases ha with ⟨a₀, ha₀, rfl⟩
    refine ⟨-a₀, neg_mem ha₀, ?_⟩
    simp [smul_neg_pointwise]

lemma NL_subgroup_le_NV (d : ℕ) (N : ℕ) (L : AddSubgroup (V d)) :
    NL_subgroup d N L ≤ NV_subgroup d N := by
  intro x hx
  change x ∈ zimg N (L : Set (V d)) at hx
  change x ∈ zimg N Set.univ
  rw [mem_zimg] at hx ⊢
  rcases hx with ⟨a, ha, rfl⟩
  refine ⟨a, by simp, rfl⟩

/-! ### Finiteness of `zimg` over finite sets, translations -/

lemma zimg_finite {d : ℕ} {N : ℕ} {A : Set (V d)} (hA : A.Finite) : (zimg N A).Finite := by
  change ((fun x : V d => (N : ℤ) • x) '' A).Finite
  exact hA.image (fun x : V d => (N : ℤ) • x)

lemma zimg_empty {d : ℕ} (N : ℕ) : zimg N (∅ : Set (V d)) = ∅ := by
  ext x; simp [zimg]

lemma zimg_univ_eq {d : ℕ} {N : ℕ} (hN : N ≠ 0) : zimg N (Set.univ : Set (V d)) = {x : V d | ∀ i, (N : ℤ) ∣ x i} := by
  ext x
  exact mem_zimg_iff_all_dvd (x := x)

lemma add_empty {d : ℕ} (A : Set (V d)) : A + (∅ : Set (V d)) = ∅ := by
  ext x; simp [Set.mem_add]

/-- `NV + NL = NV` since `NL ≤ NV`. -/
lemma NV_add_NL {d : ℕ} (N : ℕ) (L : AddSubgroup (V d)) :
    (NV d N : Set (V d)) + (NL d N L : Set (V d)) = (NV d N : Set (V d)) := by
  apply le_antisymm
  · intro x hx
    rcases Set.mem_add.mp hx with ⟨a, ha, b, hb, rfl⟩
    exact add_mem ha (NL_subgroup_le_NV d N L hb)
  · intro x hx
    refine Set.mem_add.mpr ⟨x, hx, 0, ?_, by simp⟩
    exact zero_mem (NL_subgroup d N L)

/-! ### Finite generating family for `L` -/

lemma closure_diff_zero {d : ℕ} (S : Set (V d)) :
    AddSubgroup.closure (S \ ({0} : Set (V d))) = AddSubgroup.closure S := by
  apply le_antisymm
  · exact AddSubgroup.closure_mono (by intro x hx; exact hx.1)
  · rw [AddSubgroup.closure_le]
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      exact AddSubgroup.zero_mem (AddSubgroup.closure (S \ ({0} : Set (V d))))
    · exact AddSubgroup.subset_closure ⟨hx, hx0⟩

/-- Every additive subgroup of `ℤ^d` is generated by a finite family of distinct
non-zero elements. -/
lemma fin_family_generates_int_subgroup (d : ℕ) (L : AddSubgroup (V d)) :
    ∃ (r : ℕ) (w : Fin r → V d),
      (∀ i : Fin r, w i ∈ L) ∧
      (∀ i : Fin r, w i ≠ 0) ∧
      Function.Injective w ∧
      L = AddSubgroup.closure (Set.range w) := by
  classical
  have hfg : L.FG := by
    have hNoet : IsNoetherian ℤ (V d) := by infer_instance
    have hfgSub : (AddSubgroup.toIntSubmodule L).FG := IsNoetherian.noetherian (AddSubgroup.toIntSubmodule L)
    exact (Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule L)).mp hfgSub
  rcases (AddSubgroup.fg_iff L).mp hfg with ⟨s, hs_cl, hs_fin⟩
  let F0 : Finset (V d) := hs_fin.toFinset
  let F : Finset (V d) := F0.erase 0
  have hclF : AddSubgroup.closure (F : Set (V d)) = L := by
    calc
      AddSubgroup.closure (F : Set (V d))
          = AddSubgroup.closure ((F0 : Set (V d)) \ ({0} : Set (V d))) := by
            rw [Finset.coe_erase]
      _ = AddSubgroup.closure (F0 : Set (V d)) := by rw [closure_diff_zero]
      _ = AddSubgroup.closure s := by rw [hs_fin.coe_toFinset]
      _ = L := hs_cl
  let α := {x : V d // x ∈ F}
  haveI : Fintype α := by infer_instance
  let r : ℕ := Fintype.card α
  let e : α ≃ Fin r := Fintype.equivFin α
  let w : Fin r → V d := fun i => (e.symm i : α).1
  refine ⟨r, w, ?_, ?_, ?_, ?_⟩
  · intro i
    have hwiF : w i ∈ (F : Set (V d)) := (e.symm i).2
    have hwiL : w i ∈ AddSubgroup.closure (F : Set (V d)) := AddSubgroup.subset_closure hwiF
    rwa [hclF] at hwiL
  · intro i
    have hwiF : w i ∈ (F : Set (V d)) := (e.symm i).2
    rw [Finset.mem_coe] at hwiF
    exact (Finset.mem_erase.mp hwiF).1
  · intro i j hij
    have hiα : (e.symm i : α) = (e.symm j : α) := Subtype.ext hij
    have hij' : e (e.symm i) = e (e.symm j) := congrArg e hiα
    simpa using hij'
  · have hran : Set.range w = (F : Set (V d)) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact (e.symm i).2
      · intro hy
        let a : α := ⟨y, hy⟩
        refine ⟨e a, ?_⟩
        exact congrArg (fun x : α => (x : V d)) (Equiv.symm_apply_apply e a)
    have hclW : AddSubgroup.closure (Set.range w) = L := by
      rw [hran, hclF]
    exact hclW.symm

/-! ### Moved-cell algebra: `Tⱼ ⊕ NL = T ⊕ NL`

A tile `T'` obtained from `T` by deleting cells `X l` (each `X l ⊆ T`) and re-adding
them translated by `p l ∈ S` satisfies `T' + S = T + S`.  Applied with `S = NL` this
is exactly condition (b) of the lemma. -/

lemma add_singleton_mem_subgroup {G : Type*} [AddCommGroup G] {S : AddSubgroup G} {p : G}
    (hp : p ∈ S) : ({p} : Set G) + (S : Set G) = (S : Set G) := by
  apply le_antisymm
  · intro x hx
    rcases Set.mem_add.mp hx with ⟨a, ha, b, hb, hx⟩
    subst a
    exact hx ▸ (add_mem hp hb)
  · intro x hx
    rw [Set.mem_add]
    exact ⟨p, by simp, x - p, sub_mem hx hp, by abel⟩

/-- If `T'` is obtained from `T` by removing each `X l` and re-adding it translated by
`p l ∈ S`, then `T' + S = T + S`. -/
lemma add_moved_cells {G : Type*} [AddCommGroup G] (S : AddSubgroup G) {T : Set G} {ι : Type*}
    (X : ι → Set G) (p : ι → G)
    (hX : ∀ l, X l ⊆ T) (hp : ∀ l, p l ∈ S) :
    (((T \ (⋃ l : ι, X l)) ∪ (⋃ l : ι, (X l + ({p l} : Set G)))) + (S : Set G)) =
      T + (S : Set G) := by
  rw [Set.union_add]
  rw [Set.iUnion_add]
  have hstep : (⋃ l : ι, (X l + ({p l} : Set G)) + (S : Set G)) = ⋃ l : ι, (X l + (S : Set G)) := by
    apply Set.iUnion_congr
    intro l
    rw [add_assoc, add_singleton_mem_subgroup (hp l)]
  rw [hstep]
  have hXeq : (T \ (⋃ l : ι, X l)) ∪ (⋃ l : ι, X l) = T := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx.1
      · rw [Set.mem_iUnion] at hx
        rcases hx with ⟨l, hl⟩
        exact hX l hl
    · intro hx
      by_cases hxX : x ∈ (⋃ l : ι, X l)
      · exact Or.inr hxX
      · exact Or.inl ⟨hx, hxX⟩
  rw [← Set.iUnion_add]
  rw [← Set.union_add]
  rw [hXeq]

/-! The set-sum `A + B` equals `Set.image2 Add.add A B`, so `Tⱼ ⊕ NL = T ⊕ NL` is the
same statement as `Tⱼ + NL = T + NL`. -/
lemma image2_add_eq_add' {d : ℕ} (A B : Set (V d)) :
    Set.image2 (fun x y : V d => x + y) A B = A + B := by
  ext x; rfl

/-! ### Discrete boxes in `ℤ^d` (geometry developed in later stages)

The BGU construction works with `box n := {x | x i ∈ Set.Icc (-n) n for all i}` and teeth
shaped as L∞-shells of distinct radii; the geometry layer will be added here once the
tiling-forcing argument is fully designed.
-/


/-! ### A generating family of size `≤ d`

Every additive subgroup of `ℤ^d` is free of rank `≤ d` (PID structure theorem), so it
is generated by at most `d` of its elements.  This gives `r ≤ d`, which keeps the number
of teeth below `2^(d-1)` in the forcing construction.
-/

lemma submodule_basis_le_rank (d : ℕ) (L : AddSubgroup (V d)) :
    ∃ (n : ℕ) (hn : n ≤ d) (b : Module.Basis (Fin n) ℤ (L.toIntSubmodule : Submodule ℤ (V d))), True := by
  classical
  let b : Module.Basis (Fin d) ℤ (V d) := Pi.basisFun ℤ (Fin d)
  let N : Submodule ℤ (V d) := L.toIntSubmodule
  rcases Submodule.basisOfPid b N with ⟨n, bN⟩
  refine ⟨n, ?_, bN, trivial⟩
  have hN : Module.finrank ℤ N = n := by
    simpa using (Module.finrank_eq_card_basis bN : Module.finrank ℤ N = Fintype.card (Fin n))
  have hle : Module.finrank ℤ N ≤ Module.finrank ℤ (V d) := by
    haveI : Module.Finite ℤ (V d) := by infer_instance
    exact Submodule.finrank_le (R := ℤ) (M := V d) (s := N)
  have hM : Module.finrank ℤ (V d) = d := by
    simpa using (Module.finrank_pi ℤ (Fin d) : Module.finrank ℤ (Fin d → ℤ) = Fintype.card (Fin d))
  omega

lemma small_generating_family_int_subgroup (d : ℕ) (L : AddSubgroup (V d)) :
    ∃ (r : ℕ) (hr : r ≤ d) (w : Fin r → V d),
      (∀ i : Fin r, w i ∈ L) ∧
      (∀ i : Fin r, w i ≠ 0) ∧
      Function.Injective w ∧
      L = AddSubgroup.closure (Set.range w) := by
  classical
  let b : Module.Basis (Fin d) ℤ (V d) := Pi.basisFun ℤ (Fin d)
  let N : Submodule ℤ (V d) := L.toIntSubmodule
  rcases Submodule.basisOfPid b N with ⟨r, bN⟩
  have hr : r ≤ d := by
    have hN : Module.finrank ℤ N = r := by
      simpa using (Module.finrank_eq_card_basis bN : Module.finrank ℤ N = Fintype.card (Fin r))
    have hle : Module.finrank ℤ N ≤ Module.finrank ℤ (V d) := by
      haveI : Module.Finite ℤ (V d) := by infer_instance
      exact Submodule.finrank_le (R := ℤ) (M := V d) (s := N)
    have hM : Module.finrank ℤ (V d) = d := by
      simpa using (Module.finrank_pi ℤ (Fin d) : Module.finrank ℤ (Fin d → ℤ) = Fintype.card (Fin d))
    omega
  let w : Fin r → V d := fun i => ((bN i : N) : V d)
  refine ⟨r, hr, w, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp [w]
    have hmemN : ((bN i : N) : V d) ∈ (N : Set (V d)) := (bN i).2
    have hset : ((N : Submodule ℤ (V d)) : Set (V d)) = (L : Set (V d)) := by
      exact AddSubgroup.coe_toIntSubmodule L
    rwa [hset] at hmemN
  · intro i
    have hne : bN i ≠ 0 := Module.Basis.ne_zero bN i
    intro h
    apply hne
    apply Subtype.ext
    exact h
  · intro i j h
    have hb : bN i = bN j := by
      apply Subtype.ext
      exact h
    exact bN.injective hb
  · have hsetN : ((N : Submodule ℤ (V d)) : Set (V d)) = (L : Set (V d)) := by
      exact AddSubgroup.coe_toIntSubmodule L
    ext x
    constructor
    · intro hxL
      have hxN : x ∈ (N : Set (V d)) := by
        change x ∈ (L : Set (V d)) at hxL
        rw [← hsetN] at hxL
        exact hxL
      have hsumN : (∑ i : Fin r, (bN.repr (⟨x, hxN⟩ : N)) i • (bN i : N)) = (⟨x, hxN⟩ : N) := by
        simpa using (Module.Basis.sum_repr bN (u := (⟨x, hxN⟩ : N)))
      have hsumM : (∑ i : Fin r, (bN.repr ⟨x, hxN⟩) i • w i) = x := by
        have h1 := congrArg (N.subtype) hsumN
        have helper : N.subtype (∑ i : Fin r, (bN.repr ⟨x, hxN⟩) i • (bN i : N)) =
            (∑ i : Fin r, (bN.repr ⟨x, hxN⟩) i • ((bN i : N) : V d)) := by
          simp only [map_sum]
          simp
        rw [helper] at h1
        simpa [w] using h1
      rw [← hsumM]
      apply AddSubgroup.sum_mem (AddSubgroup.closure (Set.range w))
      intro i hi
      apply AddSubgroup.zsmul_mem (AddSubgroup.closure (Set.range w))
      exact AddSubgroup.subset_closure ⟨i, rfl⟩
    · intro hx
      have hle : AddSubgroup.closure (Set.range w) ≤ L := by
        rw [AddSubgroup.closure_le]
        intro y hy
        rcases hy with ⟨i, rfl⟩
        dsimp [w]
        have hmemN : ((bN i : N) : V d) ∈ (N : Set (V d)) := (bN i).2
        rwa [hsetN] at hmemN
      exact hle hx

-- ----------------------------------------------------------------------
-- Port of tile.lean (slice 1): box, rep, quot.
-- ----------------------------------------------------------------------

/-- the half-open box `[0,N)^d` -/
def box (d : ℕ) (N : ℕ) : Set (V d) := {x | ∀ i : Fin d, (0 : ℤ) ≤ x i ∧ x i < (N : ℤ)}

/-- coordinatewise reduction into `[0,N-1]` -/
def rep (N : ℕ) (x : V d) : V d := fun i => x i % (N : ℤ)

/-- coordinatewise integer division by `N` -/
def quot (N : ℕ) (x : V d) : V d := fun i => x i / (N : ℤ)

/-- the reduced representative lies in the box -/
lemma rep_mem_box {d N : ℕ} (hN : 0 < N) (x : V d) : rep N x ∈ box d N := by
  intro i
  have hpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  constructor
  · exact Int.emod_nonneg (x i) (by omega)
  · exact Int.emod_lt_of_pos (x i) hpos

/-- every point decomposes into a lattice part and a box representative -/
lemma x_eq_smul_quot_add_rep {d N : ℕ} (x : V d) :
    x = (N : ℤ) • quot N x + rep N x := by
  apply funext
  intro i
  have h : (N : ℤ) * (x i / (N : ℤ)) + x i % (N : ℤ) = x i := by
    have hdef : x i % (N : ℤ) = x i - (N : ℤ) * (x i / (N : ℤ)) := Int.emod_def (x i) (N : ℤ)
    omega
  simpa [quot, rep, Pi.smul_apply, mul_comm] using h.symm

-- ----------------------------------------------------------------------
-- Port of tile.lean (slice 2): box finiteness, the dented tile, and the
-- rep/quot round-trip lemmas (no NV references — verbatim).
-- ----------------------------------------------------------------------

lemma zero_mem_box {d N : ℕ} (hN : 0 < N) : (0 : V d) ∈ box d N := by
  intro i
  constructor
  · simp
  · simp
    exact_mod_cast hN

lemma box_eq_pi_Icc (d N : ℕ) :
    box d N = {x | ∀ i : Fin d, x i ∈ Set.Icc (0 : ℤ) ((N : ℤ) - 1)} := by
  ext x
  simp [box]

lemma box_finite (d N : ℕ) : (box d N).Finite := by
  classical
  rw [box_eq_pi_Icc]
  exact Set.Finite.pi' (fun i : Fin d => Set.finite_Icc (0 : ℤ) ((N : ℤ) - 1))

/-- the dented tile built from a dent set `D` and bump directions `u` -/
def dentedTile (d : ℕ) (N : ℕ) (D : Finset (V d)) (u : V d → V d) : Set (V d) :=
  (box d N \ (D : Set (V d))) ∪
    ((fun x : V d => x + (N : ℤ) • u x) '' (D : Set (V d)))

lemma dentedTile_finite {d N : ℕ} (D : Finset (V d)) (u : V d → V d) :
    (dentedTile d N D u).Finite := by
  unfold dentedTile
  refine (Set.Finite.union ?_ ?_)
  · exact (box_finite d N).subset (by intro x hx; exact hx.1)
  · exact (Set.Finite.image (fun x : V d => x + (N : ℤ) • u x) (by simpa using D.finite_toSet))

/-- `0` is in the dented tile (provided `0` is not a dent cell). -/
lemma zero_mem_dentedTile {d N : ℕ} (hN : 0 < N) (D : Finset (V d)) (u : V d → V d)
    (h0 : (0 : V d) ∉ (D : Set (V d))) : (0 : V d) ∈ dentedTile d N D u := by
  unfold dentedTile
  exact Or.inl ⟨zero_mem_box hN, h0⟩

lemma rep_eq_self_of_mem_box {d N : ℕ} (hN : 0 < N) {x : V d} (hx : x ∈ box d N) :
    rep N x = x := by
  apply funext
  intro i
  have hxbox := hx i
  have hpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  simp [rep, Int.emod_eq_of_lt hxbox.1 hxbox.2]

lemma rep_mul_smul {d N : ℕ} (z : V d) : rep N ((N : ℤ) • z) = 0 := by
  apply funext
  intro i
  simp [rep, Pi.smul_apply, Int.mul_emod_right]

lemma quot_smul {d N : ℕ} (hN : 0 < N) (z : V d) : quot N ((N : ℤ) • z) = z := by
  apply funext
  intro i
  have hpos : (N : ℤ) ≠ 0 := by omega
  simp [quot, Pi.smul_apply]
  exact Int.ediv_eq_of_eq_mul_left hpos (by ring : (N : ℤ) * z i = (z i) * (N : ℤ))

lemma rep_add_smul {d N : ℕ} (z x : V d) : rep N ((N : ℤ) • z + x) = rep N x := by
  apply funext
  intro i
  have h : ((N : ℤ) * z i + x i) % (N : ℤ) = x i % (N : ℤ) := by
    rw [add_comm]
    simpa [mul_comm] using (Int.add_mul_emod_self_left (x i) (N : ℤ) (z i))
  simpa [rep, Pi.smul_apply, Pi.add_apply] using h

-- ----------------------------------------------------------------------
-- Port of tile.lean (slice 3): the divisibility-NV block, re-pointed to the
-- zimg-based NV through NV_divisibility_eq_zimg.
-- ----------------------------------------------------------------------

/-- membership in `NV` is coordinatewise divisibility by `N` -/
lemma mem_NV_iff {d N : ℕ} {x : V d} : x ∈ NV d N ↔ ∀ i : Fin d, (N : ℤ) ∣ x i :=
  mem_zimg_iff_all_dvd (x := x)

/-- scalar multiples by `N` lie in `NV` -/
lemma smul_mem_NV {d N : ℕ} (z : V d) : (N : ℤ) • z ∈ NV d N := by
  rw [mem_NV_iff]
  intro i
  exact ⟨z i, by simp [Pi.smul_apply, mul_comm]⟩

/-- a lattice point equals `N` times its quotient -/
lemma NV_eq_smul_quot {d N : ℕ} (hN : 0 < N) {a : V d} (ha : a ∈ NV d N) :
    a = (N : ℤ) • quot N a := by
  apply funext
  intro i
  rcases (mem_NV_iff.mp ha) i with ⟨c, hc⟩
  have hpos : (N : ℤ) ≠ 0 := by omega
  have hdiv : a i / (N : ℤ) = c := Int.ediv_eq_of_eq_mul_right hpos hc
  calc
    a i = (N : ℤ) * c := hc
    _ = (N : ℤ) * (quot N a i) := by rw [quot, hdiv]
    _ = ((N : ℤ) • quot N a) i := by simp [Pi.smul_apply]

/-- the bump representative of a box cell is the cell itself -/
lemma bump_rep {d N : ℕ} (hN : 0 < N) {u : V d → V d} {d0 : V d}
    (hd0 : d0 ∈ box d N) : rep N (d0 + (N : ℤ) • u d0) = d0 := by
  calc
    rep N (d0 + (N : ℤ) • u d0) = rep N ((N : ℤ) • u d0 + d0) := by
      apply congrArg (rep N)
      abel
    _ = rep N d0 := rep_add_smul (u d0) d0
    _ = d0 := rep_eq_self_of_mem_box hN hd0

-- ----------------------------------------------------------------------
-- Port of tile.lean (slice 4): dentedTile_isComplement, NV-membership proofs
-- re-pointed with rw [mem_NV_iff].
-- ----------------------------------------------------------------------

/-- any dented tile with dents inside the box and nonzero bump directions is a
fundamental domain for `NV` -/
lemma dentedTile_isComplement {d N : ℕ} (hN : 0 < N) (D : Finset (V d)) (u : V d → V d)
    (hDbox : ∀ x, x ∈ (D : Set (V d)) → x ∈ box d N)
    (hdir0 : ∀ x, x ∈ (D : Set (V d)) → u x ≠ 0) :
    AddSubgroup.IsComplement (NV d N) (dentedTile d N D u) := by
  rw [AddSubgroup.isComplement_iff_existsUnique]
  intro g
  let r : V d := rep N g
  let q : V d := quot N g
  have hsum_g : (N : ℤ) • q + r = g := by
    exact (x_eq_smul_quot_add_rep (N := N) g).symm
  by_cases hD : r ∈ (D : Set (V d))
  · let t : V d := r + (N : ℤ) • u r
    let a : V d := (N : ℤ) • (q - u r)
    have ht : t ∈ dentedTile d N D u := by
      unfold dentedTile
      right
      rw [Set.mem_image]
      exact ⟨r, hD, rfl⟩
    have ha : a ∈ NV d N := by
      rw [mem_NV_iff]
      intro i
      simp [a, Pi.smul_apply]
    have hsum : a + t = g := by
      calc
        a + t = (N : ℤ) • q + r := by
          ext i
          simp [a, t, Pi.smul_apply, Pi.add_apply, sub_eq_add_neg]
          ring
        _ = g := hsum_g
    refine ⟨(⟨a, ha⟩, ⟨t, ht⟩), hsum, ?_⟩
    · intro y hy
      rcases y with ⟨⟨a', ha'⟩, ⟨t', ht'⟩⟩
      have hrep_t' : rep N t' = r := by
        have h1 := congrArg (rep N) hy
        have h3 : rep N (a' + t') = rep N t' := by
          rw [NV_eq_smul_quot hN ha']
          exact rep_add_smul (quot N a') t'
        calc
          rep N t' = rep N (a' + t') := h3.symm
          _ = rep N g := h1
          _ = r := rfl
      unfold dentedTile at ht'
      rw [Set.mem_union] at ht'
      rcases ht' with ht' | ht'
      · rw [Set.mem_diff] at ht'
        have ht'notD : t' ∉ (D : Set (V d)) := ht'.2
        have hrt : r = t' := by
          calc
            r = rep N t' := hrep_t'.symm
            _ = t' := rep_eq_self_of_mem_box hN ht'.1
        exfalso
        exact ht'notD (by simpa [hrt] using hD)
      · rw [Set.mem_image] at ht'
        rcases ht' with ⟨d0, hd0, ht'bump⟩
        have hd0box : d0 ∈ box d N := hDbox d0 hd0
        have hd0eq : d0 = r := by
          calc
            d0 = rep N (d0 + (N : ℤ) • u d0) := (bump_rep hN hd0box).symm
            _ = rep N t' := by rw [← ht'bump]
            _ = r := hrep_t'
        have ht'eq : t' = t := by
          calc
            t' = d0 + (N : ℤ) • u d0 := ht'bump.symm
            _ = r + (N : ℤ) • u r := by rw [hd0eq]
            _ = t := rfl
        have ha'eq : a' = a := by
          have h : a' = g - t' := by
            rw [← hy]
            ext i
            simp [Pi.add_apply, Pi.sub_apply]
          calc
            a' = g - t' := h
            _ = g - t := by rw [ht'eq]
            _ = a := by
              rw [← hsum_g]
              ext i
              all_goals simp [t, a, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, sub_eq_add_neg]
              all_goals ring_nf
        apply Prod.ext
        · apply Subtype.ext
          exact ha'eq
        · apply Subtype.ext
          exact ht'eq
  · let t : V d := r
    let a : V d := (N : ℤ) • q
    have ht : t ∈ dentedTile d N D u := by
      unfold dentedTile
      left
      constructor
      · simpa [t] using (rep_mem_box hN g)
      · exact hD
    have ha : a ∈ NV d N := by
      rw [mem_NV_iff]
      intro i
      simp [a, Pi.smul_apply]
    have hsum : a + t = g := by
      simpa [a, t] using hsum_g
    refine ⟨(⟨a, ha⟩, ⟨t, ht⟩), hsum, ?_⟩
    · intro y hy
      rcases y with ⟨⟨a', ha'⟩, ⟨t', ht'⟩⟩
      have hrep_t' : rep N t' = r := by
        have h1 := congrArg (rep N) hy
        have h3 : rep N (a' + t') = rep N t' := by
          rw [NV_eq_smul_quot hN ha']
          exact rep_add_smul (quot N a') t'
        calc
          rep N t' = rep N (a' + t') := h3.symm
          _ = rep N g := h1
          _ = r := rfl
      unfold dentedTile at ht'
      rw [Set.mem_union] at ht'
      rcases ht' with ht' | ht'
      · rw [Set.mem_diff] at ht'
        have ht'eq : t' = t := by
          calc
            t' = rep N t' := (rep_eq_self_of_mem_box hN ht'.1).symm
            _ = r := hrep_t'
            _ = t := rfl
        have ha'eq : a' = a := by
          have h : a' = g - t' := by
            rw [← hy]
            ext i
            simp [Pi.add_apply, Pi.sub_apply]
          calc
            a' = g - t' := h
            _ = g - t := by rw [ht'eq]
            _ = a := by
              rw [← hsum_g]
              ext i
              all_goals simp [t, a, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, sub_eq_add_neg]
              all_goals ring_nf
        apply Prod.ext
        · apply Subtype.ext
          exact ha'eq
        · apply Subtype.ext
          exact ht'eq
      · rw [Set.mem_image] at ht'
        rcases ht' with ⟨d0, hd0, ht'bump⟩
        have hd0box : d0 ∈ box d N := hDbox d0 hd0
        have hd0eq : d0 = r := by
          calc
            d0 = rep N (d0 + (N : ℤ) • u d0) := (bump_rep hN hd0box).symm
            _ = rep N t' := by rw [← ht'bump]
            _ = r := hrep_t'
        have hrD : r ∈ (D : Set (V d)) := by simpa [← hd0eq] using hd0
        exact False.elim (hD hrD)

-- ----------------------------------------------------------------------
-- Port of g1.lean (slice 1): basis teeth (xhole/eb/Dset/uBump/basisTile) and
-- their basic lemmas (no RigidOverlap dependency).
-- ----------------------------------------------------------------------

/-- hole of the `j`-th basis tooth -/
def xhole {d : ℕ} (j : Fin d) : V d := fun l => if l = j then (2 : ℤ) else (4 : ℤ)

/-- standard basis vector -/
def eb (d : ℕ) (j : Fin d) : V d := fun l => if l = j then (1 : ℤ) else 0

lemma xhole_self {d : ℕ} (j : Fin d) : xhole (d := d) j j = (2 : ℤ) := by
  simp [xhole]

lemma xhole_other {d : ℕ} {j k : Fin d} (h : j ≠ k) : xhole (d := d) j k = (4 : ℤ) := by
  have hkj : k ≠ j := fun hkj => h hkj.symm
  rw [xhole]
  simp [hkj]

lemma xhole_injective {d : ℕ} : Function.Injective (xhole (d := d)) := by
  intro j k h
  by_contra hjk
  have hj := congrFun h j
  have hkj : k ≠ j := fun hkj => hjk hkj.symm
  rw [xhole_self j, xhole_other hkj] at hj
  norm_num at hj

lemma eb_apply {d : ℕ} (j : Fin d) : eb d j j = 1 := by simp [eb]
lemma eb_apply_ne {d : ℕ} {j k : Fin d} (h : j ≠ k) : eb d j k = 0 := by
  have hkj : k ≠ j := fun hkj => h hkj.symm
  rw [eb]
  simp [hkj]

lemma xhole_val {d : ℕ} (j : Fin d) (l : Fin d) : xhole (d := d) j l = 2 ∨ xhole (d := d) j l = 4 := by
  by_cases h : l = j
  · subst h; left; simp [xhole]
  · right; exact xhole_other (fun hjl => h hjl.symm)

/-- the dent set -/
def Dset (d : ℕ) : Finset (V d) := Finset.univ.image (xhole (d := d))

lemma Dset_mem {d : ℕ} {x : V d} : x ∈ (Dset d : Set (V d)) ↔ ∃ j : Fin d, x = xhole (d := d) j := by
  dsimp [Dset]
  constructor
  · intro hx
    rcases (Finset.mem_image.mp hx) with ⟨j, hj, h⟩
    exact ⟨j, h.symm⟩
  · rintro ⟨j, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

lemma Dset_card (d : ℕ) : (Dset d).card = d := by
  dsimp [Dset]
  rw [Finset.card_image_of_injective]
  · simp
  · exact xhole_injective

/-- bump-direction function (maps hole `x j` to `e j`) -/
noncomputable def uBump {d : ℕ} : V d → V d :=
  fun x => if hx : x ∈ (Dset d : Set (V d)) then eb d (Classical.choose (Dset_mem.mp hx)) else 0

lemma uBump_eq {d : ℕ} (j : Fin d) : uBump (xhole (d := d) j) = eb d j := by
  dsimp [uBump]
  rw [dif_pos]
  · congr 1
    exact xhole_injective ((Classical.choose_spec (Dset_mem.mp (Dset_mem.mpr ⟨j, rfl⟩))).symm)
  · exact Dset_mem.mpr ⟨j, rfl⟩

/-- bump directions of dent cells are nonzero -/
lemma uBump_ne_zero {d : ℕ} {x : V d} (hx : x ∈ (Dset d : Set (V d))) : uBump x ≠ 0 := by
  rcases Dset_mem.mp hx with ⟨j, rfl⟩
  rw [uBump_eq]
  intro h
  have hj := congrFun h j
  simp [eb_apply j] at hj

/-- holes lie in the box (margin ≥ 2) -/
lemma xhole_mem_box {d N : ℕ} (hN : 5 ≤ N) (j : Fin d) : xhole (d := d) j ∈ box d N := by
  intro l
  rcases xhole_val j l with h | h <;> rw [h] <;> constructor <;> norm_num
  · omega
  · omega

/-- the basis-tooth dented tile -/
def basisTile (d N : ℕ) : Set (V d) := dentedTile d N (Dset d) uBump

/-- a body cell of the box that is not a hole is in the tile -/
lemma basisTile_body_mem {d N : ℕ} {x : V d} (hx : x ∈ box d N)
    (hxD : x ∉ (Dset d : Set (V d))) : x ∈ basisTile d N := by
  unfold basisTile dentedTile
  exact Or.inl ⟨hx, hxD⟩

/-- NV ⊕ basisTile = ℤ^d -/
lemma NV_IsComplement_basisTile {d N : ℕ} (hN : 5 ≤ N) :
    AddSubgroup.IsComplement (NV d N) (basisTile d N) := by
  unfold basisTile
  apply dentedTile_isComplement (N := N) (D := Dset d) (u := uBump)
  · exact (by omega : 0 < N)
  · intro x hx
    rcases Dset_mem.mp hx with ⟨j, rfl⟩
    exact xhole_mem_box (by omega : 5 ≤ N) j
  · intro x hx
    exact uBump_ne_zero hx

/-- 0 is not a dent cell -/
lemma zero_not_mem_Dset {d : ℕ} : (0 : V d) ∉ (Dset d : Set (V d)) := by
  intro hx
  rcases Dset_mem.mp hx with ⟨j, hj⟩
  have hj0 := congrFun hj j
  rw [xhole_self j] at hj0
  norm_num at hj0

/-- 0 is in the basis tile -/
lemma zero_mem_basisTile {d N : ℕ} (hN : 1 ≤ N) : (0 : V d) ∈ basisTile d N := by
  exact zero_mem_dentedTile (by omega : 0 < N) (Dset d) uBump zero_not_mem_Dset

/-- the basis tile is finite -/
lemma basisTile_finite (d N : ℕ) : (basisTile d N).Finite := by
  unfold basisTile
  exact dentedTile_finite (Dset d) uBump

/-- a hole is not a bump cell -/
lemma xhole_ne_bump {d N : ℕ} (hN : 1 ≤ N) (j k : Fin d) :
    xhole (d := d) j ≠ xhole (d := d) k + (N : ℤ) • eb d k := by
  intro h
  have hj := congrFun h j
  by_cases hjk : j = k
  · subst k
    have hN' : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    have hj' : (xhole (d := d) j + (N : ℤ) • eb d j) j = (N : ℤ) + 2 := by
      simp [Pi.add_apply, Pi.smul_apply, xhole_self j, eb_apply j]
      ring
    rw [xhole_self j, hj'] at hj
    omega
  · have hne : k ≠ j := fun hkj => hjk hkj.symm
    have hj' : (xhole (d := d) k + (N : ℤ) • eb d k) j = 4 := by
      simp [Pi.add_apply, Pi.smul_apply, xhole_other hne, eb_apply_ne hne]
    rw [xhole_self j, hj'] at hj
    norm_num at hj

/-- a hole is not in the tile -/
lemma xhole_not_mem_basisTile {d N : ℕ} (hN : 7 ≤ N) (j : Fin d) :
    xhole (d := d) j ∉ basisTile d N := by
  unfold basisTile dentedTile
  rw [Set.mem_union]
  intro hx
  rcases hx with hx | hx
  · rw [Set.mem_diff] at hx
    exact hx.2 (Dset_mem.mpr ⟨j, rfl⟩)
  · rw [Set.mem_image] at hx
    rcases hx with ⟨d0, hd0, hx⟩
    rcases Dset_mem.mp hd0 with ⟨k, rfl⟩
    have hu : uBump (xhole (d := d) k) = eb d k := uBump_eq k
    exact xhole_ne_bump (by omega : 1 ≤ N) j k (by simpa [hu] using hx.symm)

/-- difference of two hole coordinate values is at most 2 -/
lemma xhole_diff_le_two {d : ℕ} (j k : Fin d) (i : Fin d) :
    |xhole (d := d) j i - xhole (d := d) k i| ≤ (2 : ℤ) := by
  rcases xhole_val j i with hj | hj
  · rcases xhole_val k i with hk | hk
    · rw [hj, hk]
      norm_num
    · rw [hj, hk]
      norm_num
  · rcases xhole_val k i with hk | hk
    · rw [hj, hk]
      norm_num
    · rw [hj, hk]
      norm_num

end
namespace RigidOverlap


abbrev V (d : ℕ) := Fin d → ℤ

/-- the half-open box `[0,N)^d` (a complete residue system mod `N` in each coordinate) -/
def box (d : ℕ) (N : ℕ) : Set (V d) := {x | ∀ i : Fin d, (0 : ℤ) ≤ x i ∧ x i < (N : ℤ)}

/-- strictly interior cells of the box, the only allowed dent positions -/
def core (d : ℕ) (N : ℕ) : Set (V d) :=
  {x | ∀ i : Fin d, (0 : ℤ) < x i ∧ x i < (N - 1 : ℤ)}

lemma mem_box_iff {d : ℕ} {N : ℕ} {x : V d} :
    x ∈ box d N ↔ ∀ i : Fin d, (0 : ℤ) ≤ x i ∧ x i < (N : ℤ) := by rfl

lemma mem_core_iff {d : ℕ} {N : ℕ} {x : V d} :
    x ∈ core d N ↔ ∀ i : Fin d, (0 : ℤ) < x i ∧ x i < (N - 1 : ℤ) := by rfl

lemma core_subset_box {d : ℕ} {N : ℕ} : core d N ⊆ box d N := by
  intro x hx i
  have hxi := (mem_core_iff.mp hx) i
  constructor
  · exact le_of_lt hxi.1
  · exact lt_trans hxi.2 (by omega : (N - 1 : ℤ) < (N : ℤ))

/-- the "far corner" of the overlap of `box` and `δ + box` -/
def corner (d : ℕ) {N : ℕ} (δ : V d) : V d := fun i => if (0 : ℤ) ≤ δ i then (N - 1 : ℤ) else 0

/-- δ-boundedness condition: `|δ i| ≤ N - 1` in every coordinate (as integers) -/
def Bounded (d : ℕ) (N : ℕ) (δ : V d) : Prop := ∀ i : Fin d, |δ i| ≤ (N - 1 : ℤ)

lemma corner_mem_box {d : ℕ} {N : ℕ} (hN : 0 < N) (δ : V d) : corner d (N := N) δ ∈ box d N := by
  intro i
  by_cases h : (0 : ℤ) ≤ δ i
  · simp [corner, h]
    omega
  · simp [corner, h]
    omega

lemma corner_sub_mem_box {d : ℕ} {N : ℕ} {δ : V d} (hδ : Bounded d N δ) :
    corner d (N := N) δ - δ ∈ box d N := by
  intro i
  by_cases h : (0 : ℤ) ≤ δ i
  · have hb := abs_le.mp (hδ i)
    have hle : δ i ≤ (N - 1 : ℤ) := hb.2
    have hge : -(N - 1 : ℤ) ≤ δ i := hb.1
    simp [corner, h]
    omega
  · have hb := abs_le.mp (hδ i)
    have hle : δ i ≤ (N - 1 : ℤ) := hb.2
    have hge : -(N - 1 : ℤ) ≤ δ i := hb.1
    have hlt : δ i < 0 := lt_of_not_ge h
    simp [corner, h]
    omega

/-- the overlap box `{z | z ∈ B ∧ z - δ ∈ B}` (equals `B ∩ (δ + B)`) -/
def overlap (d : ℕ) (N : ℕ) (δ : V d) : Set (V d) :=
  box d N ∩ {z | z - δ ∈ box d N}

lemma corner_mem_overlap {d : ℕ} {N : ℕ} {δ : V d}
    (hN : 0 < N) (hδ : Bounded d N δ) :
    corner d (N := N) δ ∈ overlap d N δ := by
  refine ⟨corner_mem_box hN δ, ?_⟩
  exact corner_sub_mem_box hδ

/-! The corner cell is never a dent (it is on the boundary).  The interesting part is
making sure `corner - δ` is not a dent either; when that fails we look for other cells
of the overlap. -/


/-!
### Main overlap lemma

A dent set `D` of fewer than `2^(d-1)` cells cannot shield two distinct translates:
for `δ ≠ 0` bounded by `N-1` per coordinate, the boxes overlap at a cell `z` with
`z ∉ D` and `z - δ ∉ D`, giving `z ∈ T ∩ (δ + T)` (bumps live outside the box and
never interfere).  Case split:
* if `|δ i| = N-1` for some `i`, then every overlap cell has coordinate `i` equal to
  `0` or `N-1`, so neither it nor its δ-shift can be a dent (dents are strictly
  interior); the corner cell witnesses;
* otherwise all coordinate ranges have size ≥ 2, so the overlap box has at least
  `2^d > 2|D|` cells, and by pigeonhole some cell avoids `D` and `δ + D`.
-/

/-- δ-boundedness with all coordinates strictly inside, so ranges have size ≥ 2 -/
def StrictBounded (d : ℕ) (N : ℕ) (δ : V d) : Prop := ∀ i : Fin d, |δ i| ≤ (N - 2 : ℤ)

lemma Bounded_of_StrictBounded {d : ℕ} {N : ℕ} {δ : V d} (hδ : StrictBounded d N δ) :
    Bounded d N δ := by
  intro i
  have hi := hδ i
  have h : (N - 2 : ℤ) ≤ (N - 1 : ℤ) := by omega
  exact le_trans hi h


lemma int_abs_eq_natAbs (a : ℤ) : (a.natAbs : ℤ) = |a| := by
  by_cases h : (0 : ℤ) ≤ a
  · rw [Int.natAbs_of_nonneg h, abs_of_nonneg h]
  · have hneg : a < 0 := lt_of_not_ge h
    have hna : (Int.natAbs a : ℤ) = -a := by
      have hma : Int.natAbs a = Int.natAbs (-a) := by simp
      rw [hma]
      exact Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ -a)
    rw [hna]
    exact (abs_of_neg hneg).symm

/-- each coordinate factor of the overlap is at least 2 when `|δ i| ≤ N-2` -/
lemma bounded_abs_factor_ge_two {N : ℕ} (hN : 2 ≤ N) (a : ℤ)
    (ha : |a| ≤ (N - 2 : ℤ)) : 2 ≤ (N : ℕ) - (Int.natAbs a : ℕ) := by
  have ha' : (Int.natAbs a : ℤ) ≤ (N - 2 : ℤ) := by
    simpa [int_abs_eq_natAbs a] using ha
  have hna : Int.natAbs a ≤ N - 2 := by exact_mod_cast ha'
  omega

/-- product of `d` factors each at least 2 is at least `2^d` -/
lemma prod_factor_ge_pow {d : ℕ} {f : Fin d → ℕ} (hf : ∀ i : Fin d, 2 ≤ f i) :
    2 ^ d ≤ ∏ i : Fin d, f i := by
  classical
  induction d with
  | zero => simp
  | succ n ih =>
      let f0 : ℕ := f ⟨0, by omega⟩
      have hf0 : 2 ≤ f0 := hf ⟨0, by omega⟩
      have hrest : 2 ^ n ≤ ∏ i : Fin n, f i.succ := ih (fun i => hf i.succ)
      calc
        2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
        _ ≤ f0 * 2 ^ n := Nat.mul_le_mul_right (2 ^ n) hf0
        _ ≤ f0 * (∏ i : Fin n, f i.succ) := Nat.mul_le_mul_left f0 hrest
        _ = ∏ i : Fin (n + 1), f i := (Fin.prod_univ_succ f).symm


/-- per-coordinate number of cells of the overlap interval -/
def cellLen (d : ℕ) (N : ℕ) (δ : V d) (i : Fin d) : ℕ :=
  (N : ℕ) - (Int.natAbs (δ i) : ℕ)

/-- offsets parametrising the overlap box -/
def canon {d : ℕ} {N : ℕ} {δ : V d} (t : (i : Fin d) → Fin (cellLen d N δ i)) : V d :=
  fun i => if (0 : ℤ) ≤ δ i then δ i + (t i : ℤ) else (t i : ℤ)

lemma natAbs_le_of_abs_le {a : ℤ} {n : ℕ} (h : |a| ≤ (n : ℤ)) : Int.natAbs a ≤ n := by
  have hz : (Int.natAbs a : ℤ) ≤ (n : ℤ) := by simpa [int_abs_eq_natAbs a] using h
  exact_mod_cast hz

lemma cellLen_cast_nonneg {d N : ℕ} {δ : V d} (i : Fin d) (hsign : (0 : ℤ) ≤ δ i)
    (hδ : |δ i| ≤ (N - 2 : ℤ)) : (cellLen d N δ i : ℤ) = (N : ℤ) - δ i := by
  have hna : (Int.natAbs (δ i) : ℤ) = δ i := Int.natAbs_of_nonneg hsign
  have hleZ : (Int.natAbs (δ i) : ℤ) ≤ (N : ℤ) := by
    have h1 : |δ i| ≤ (N : ℤ) := le_trans hδ (by omega)
    have h2 : (Int.natAbs (δ i) : ℤ) = |δ i| := int_abs_eq_natAbs (δ i)
    simpa [h2] using h1
  have hle : Int.natAbs (δ i) ≤ N := by exact_mod_cast hleZ
  rw [cellLen, Int.ofNat_sub hle, hna]

lemma cellLen_cast_neg {d N : ℕ} {δ : V d} (i : Fin d) (hneg : (δ i) < 0)
    (hδ : |δ i| ≤ (N - 2 : ℤ)) : (cellLen d N δ i : ℤ) = (N : ℤ) + δ i := by
  have hna : (Int.natAbs (δ i) : ℤ) = -δ i := by
    have hma : Int.natAbs (δ i) = Int.natAbs (-δ i) := by simp
    rw [hma]
    exact Int.natAbs_of_nonneg (by omega)
  have hleZ : (Int.natAbs (δ i) : ℤ) ≤ (N : ℤ) := by
    have h1 : |δ i| ≤ (N : ℤ) := le_trans hδ (by omega)
    have h2 : (Int.natAbs (δ i) : ℤ) = |δ i| := int_abs_eq_natAbs (δ i)
    simpa [h2] using h1
  have hle : Int.natAbs (δ i) ≤ N := by exact_mod_cast hleZ
  rw [cellLen, Int.ofNat_sub hle, hna]
  omega

lemma canon_mem_box_shift {d N : ℕ} (hN : 2 ≤ N) {δ : V d}
    (hδ : ∀ i : Fin d, |δ i| ≤ (N - 2 : ℤ))
    (t : (i : Fin d) → Fin (cellLen d N δ i)) :
    canon t ∈ box d N ∧ canon t - δ ∈ box d N := by
  constructor
  · intro i
    by_cases hsign : (0 : ℤ) ≤ δ i
    · have hti0 : (0 : ℤ) ≤ (t i : ℤ) := by exact_mod_cast (Nat.zero_le (t i : ℕ))
      have htilt : (t i : ℤ) < (cellLen d N δ i : ℤ) := by exact_mod_cast (t i).isLt
      have hL : (cellLen d N δ i : ℤ) = (N : ℤ) - δ i := cellLen_cast_nonneg i hsign (hδ i)
      have hδle : δ i ≤ (N - 2 : ℤ) := (abs_le.mp (hδ i)).2
      simp [canon, hsign]
      omega
    · have hti0 : (0 : ℤ) ≤ (t i : ℤ) := by exact_mod_cast (Nat.zero_le (t i : ℕ))
      have htilt : (t i : ℤ) < (cellLen d N δ i : ℤ) := by exact_mod_cast (t i).isLt
      have hL : (cellLen d N δ i : ℤ) = (N : ℤ) + δ i := cellLen_cast_neg i (lt_of_not_ge hsign) (hδ i)
      have hδge : -(N - 2 : ℤ) ≤ δ i := (abs_le.mp (hδ i)).1
      simp [canon, hsign]
      omega
  · intro i
    by_cases hsign : (0 : ℤ) ≤ δ i
    · have hti0 : (0 : ℤ) ≤ (t i : ℤ) := by exact_mod_cast (Nat.zero_le (t i : ℕ))
      have htilt : (t i : ℤ) < (cellLen d N δ i : ℤ) := by exact_mod_cast (t i).isLt
      have hL : (cellLen d N δ i : ℤ) = (N : ℤ) - δ i := cellLen_cast_nonneg i hsign (hδ i)
      have hδle : δ i ≤ (N - 2 : ℤ) := (abs_le.mp (hδ i)).2
      simp [canon, hsign, sub_eq_add_neg]
      omega
    · have hneg : δ i < 0 := lt_of_not_ge hsign
      have hti0 : (0 : ℤ) ≤ (t i : ℤ) := by exact_mod_cast (Nat.zero_le (t i : ℕ))
      have htilt : (t i : ℤ) < (cellLen d N δ i : ℤ) := by exact_mod_cast (t i).isLt
      have hL : (cellLen d N δ i : ℤ) = (N : ℤ) + δ i := cellLen_cast_neg i hneg (hδ i)
      have hδge : -(N - 2 : ℤ) ≤ δ i := (abs_le.mp (hδ i)).1
      simp [canon, hsign]
      omega

lemma canon_injective {d : ℕ} {N : ℕ} (δ : V d) :
    Function.Injective (fun t : (i : Fin d) → Fin (cellLen d N δ i) => canon t) := by
  intro t u h
  apply funext
  intro i
  by_cases hsign : (0 : ℤ) ≤ δ i
  · have hi := congrFun h i
    simp [canon, hsign] at hi
    have hval : (t i).val = (u i).val := by exact_mod_cast hi
    exact Fin.ext hval
  · have hi := congrFun h i
    simp [canon, hsign] at hi
    have hval : (t i).val = (u i).val := by exact_mod_cast hi
    exact Fin.ext hval


/-- Pigeonhole: an overlap box of more than twice the cardinality of `D` contains a
cell (and its δ-shift) avoiding `D`. -/
lemma overlap_big_box_avoid {d N : ℕ} (hN : 2 ≤ N) (δ : V d) (hδ : StrictBounded d N δ)
    (D : Finset (V d))
    (hbig : (2 : ℕ) * D.card < ∏ i : Fin d, ((N : ℕ) - (Int.natAbs (δ i) : ℕ))) :
    ∃ z : V d,
      (∀ i : Fin d, (0 : ℤ) ≤ z i ∧ z i < (N : ℤ)) ∧
      (∀ i : Fin d, (0 : ℤ) ≤ z i - δ i ∧ z i - δ i < (N : ℤ)) ∧
      z ∉ (D : Set (V d)) ∧ z - δ ∉ (D : Set (V d)) := by
  classical
  let I := Finset.univ.image (fun t : (i : Fin d) → Fin (cellLen d N δ i) => canon (N := N) t)
  have hIcard : I.card = ∏ i : Fin d, cellLen d N δ i := by
    dsimp [I]
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_univ]
      simp [Fintype.card_pi]
    · exact canon_injective (N := N) δ
  let Dδ : Finset (V d) := D.image (fun x : V d => x + δ)
  have hDδcard : Dδ.card = D.card := by
    dsimp [Dδ]
    rw [Finset.card_image_of_injective]
    intro x y h
    have := congrArg (fun z : V d => z - δ) h
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
  let B := D ∪ Dδ
  have hBcard : B.card ≤ 2 * D.card := by
    calc
      B.card ≤ D.card + Dδ.card := Finset.card_union_le D Dδ
      _ = D.card + D.card := by rw [hDδcard]
      _ = 2 * D.card := by omega
  have hBltI : B.card < I.card := by
    rw [hIcard]
    have hbig' : (2 : ℕ) * D.card < ∏ i : Fin d, cellLen d N δ i := by
      simpa [cellLen] using hbig
    exact lt_of_le_of_lt hBcard hbig'
  have hz : ∃ z : V d, z ∈ I ∧ z ∉ B := by
    by_contra h
    have hsub : I ⊆ B := by
      intro x hx
      by_contra hxB
      exact h ⟨x, hx, hxB⟩
    exact (not_lt_of_ge (Finset.card_le_card hsub)) hBltI
  rcases hz with ⟨z, hzI, hzB⟩
  rcases Finset.mem_image.mp hzI with ⟨t, ht, htz⟩
  have hc := canon_mem_box_shift hN hδ t
  have hbox1 : z ∈ box d N := by
    rw [← htz]
    exact hc.1
  have hbox2 : z - δ ∈ box d N := by
    rw [← htz]
    exact hc.2
  have hzD : z ∉ (D : Set (V d)) := by
    intro h
    apply hzB
    exact Finset.mem_union.mpr (Or.inl (by simpa using h))
  have hzδD : z - δ ∉ (D : Set (V d)) := by
    intro h
    apply hzB
    have h2 : z - δ ∈ D := by simpa using h
    have hzDδ : z ∈ Dδ := by
      change z ∈ D.image (fun x : V d => x + δ)
      exact Finset.mem_image.mpr ⟨z - δ, h2, by abel⟩
    exact Finset.mem_union.mpr (Or.inr hzDδ)
  refine ⟨z, ?_, ?_, hzD, hzδD⟩
  · intro i
    exact (mem_box_iff.mp hbox1) i
  · intro i
    exact (mem_box_iff.mp hbox2) i
lemma dented_box_overlap {d N : ℕ} (hd : 0 < d) (hN : 2 ≤ N) (δ : V d) (hδ0 : δ ≠ 0)
    (hδ : Bounded d N δ)
    (D : Finset (V d)) (hD : ∀ z ∈ (D : Set (V d)), z ∈ core d N)
    (hsmall : 2 * D.card < 2 ^ d) :
    ((box d N \ (D : Set (V d))) ∩ {x | x - δ ∈ box d N \ (D : Set (V d))}).Nonempty := by
  classical
  by_cases hboundary : ∃ i : Fin d, |δ i| = (N - 1 : ℤ)
  · rcases hboundary with ⟨i0, hi0⟩
    let z := corner d (N := N) δ
    refine ⟨z, ?_, ?_⟩
    · refine ⟨corner_mem_box (by omega : 0 < N) δ, ?_⟩
      intro hDz
      have hcore : z ∈ core d N := hD z hDz
      have hi := (mem_core_iff.mp hcore) i0
      by_cases hsign : (0 : ℤ) ≤ δ i0
      · have hval : z i0 = (N - 1 : ℤ) := by simp [z, corner, hsign]
        have : (0 : ℤ) < z i0 := hi.1
        omega
      · have hval : z i0 = (0 : ℤ) := by simp [z, corner, hsign]
        have : (0 : ℤ) < z i0 := hi.1
        omega
    · refine ⟨corner_sub_mem_box hδ, ?_⟩
      intro hDz
      have hcore : z - δ ∈ core d N := hD (z - δ) hDz
      have hi := (mem_core_iff.mp hcore) i0
      by_cases hsign : (0 : ℤ) ≤ δ i0
      · have hδval : δ i0 = (N - 1 : ℤ) := by
          rw [abs_of_nonneg hsign] at hi0
          exact hi0
        have hz0 : z i0 = (N - 1 : ℤ) := by simp [z, corner, hsign]
        have hval : (z - δ) i0 = (0 : ℤ) := by
          rw [Pi.sub_apply, hz0, hδval]
          ring
        have : (0 : ℤ) < (z - δ) i0 := hi.1
        omega
      · have hδval : δ i0 = -(N - 1 : ℤ) := by
          have hδneg : δ i0 < 0 := lt_of_not_ge hsign
          rw [abs_of_neg hδneg] at hi0
          omega
        have hz0 : z i0 = (0 : ℤ) := by simp [z, corner, hsign]
        have hval : (z - δ) i0 = (N - 1 : ℤ) := by
          rw [Pi.sub_apply, hz0, hδval]
          ring
        have : (z - δ) i0 < (N - 1 : ℤ) := hi.2
        omega
  · have hstrict : StrictBounded d N δ := by
      intro i
      have hne : |δ i| ≠ (N - 1 : ℤ) := by
        intro h
        exact hboundary ⟨i, h⟩
      have hle : |δ i| ≤ (N - 1 : ℤ) := hδ i
      omega
    have hprod_ge : (2 : ℕ) * D.card < ∏ i : Fin d, ((N : ℕ) - (Int.natAbs (δ i) : ℕ)) := by
      have hfac : ∀ i : Fin d, 2 ≤ (N : ℕ) - (Int.natAbs (δ i) : ℕ) := by
        intro i
        exact bounded_abs_factor_ge_two hN (δ i) (hstrict i)
      have hprod : 2 ^ d ≤ ∏ i : Fin d, ((N : ℕ) - (Int.natAbs (δ i) : ℕ)) :=
        prod_factor_ge_pow hfac
      exact lt_of_lt_of_le hsmall hprod
    rcases overlap_big_box_avoid hN δ hstrict D hprod_ge with ⟨z, hz1, hz2, hzD, hzδD⟩
    refine ⟨z, ?_, ?_⟩
    · refine ⟨mem_box_iff.mpr hz1, hzD⟩
    · refine ⟨mem_box_iff.mpr hz2, hzδD⟩

end RigidOverlap
-- ----------------------------------------------------------------------
-- Port of g1.lean (slice 2): pigeonhole overlap, translate disjointness,
-- basis_click, and single-tile rigidity.
-- ----------------------------------------------------------------------

/-- `2*d < 2^d` for `3 ≤ d` -/
lemma two_mul_lt_two_pow {d : ℕ} (hd : 3 ≤ d) : 2 * d < 2 ^ d := by
  induction d with
  | zero => omega
  | succ d ih =>
      by_cases hd3 : 3 ≤ d
      · have ih' : 2 * d < 2 ^ d := ih hd3
        have hstep : 2 * (d + 1) < 2 * (2 ^ d) := by
          have h2 : 2 * (d + 1) ≤ 2 * (2 * d) := by omega
          exact lt_of_le_of_lt h2 (Nat.mul_lt_mul_of_pos_left ih' (by norm_num))
        simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hstep
      · have hd2 : d = 2 := by omega
        subst d
        norm_num

/-- overlap of two dented-box translates at bounded displacement, avoiding the holes -/
lemma basis_overlap {d N : ℕ} (hd : 3 ≤ d) (hN : 2 ≤ N) (δ : V d) (hδ0 : δ ≠ 0)
    (hδ : RigidOverlap.StrictBounded d N δ) :
    ∃ z : V d, z ∈ box d N ∧ z - δ ∈ box d N ∧
      (∀ j : Fin d, z ≠ xhole (d := d) j) ∧
      (∀ j : Fin d, z - δ ≠ xhole (d := d) j) := by
  classical
  have hfac : ∀ i : Fin d, 2 ≤ (N : ℕ) - (Int.natAbs (δ i) : ℕ) := by
    intro i
    exact RigidOverlap.bounded_abs_factor_ge_two hN (δ i) (hδ i)
  have hprod : (2 : ℕ) * (Dset d).card < ∏ i : Fin d, ((N : ℕ) - (Int.natAbs (δ i) : ℕ)) := by
    rw [Dset_card]
    have hprod2 : 2 ^ d ≤ ∏ i : Fin d, ((N : ℕ) - (Int.natAbs (δ i) : ℕ)) := by
      exact RigidOverlap.prod_factor_ge_pow hfac
    have htwo : 2 * d < 2 ^ d := two_mul_lt_two_pow hd
    exact lt_of_lt_of_le htwo hprod2
  rcases RigidOverlap.overlap_big_box_avoid hN δ hδ (Dset d) hprod with
    ⟨z, hz1, hz2, hzD, hzδD⟩
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hz1 i
  · intro i
    exact hz2 i
  · intro j hj
    apply hzD
    dsimp [Dset]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj.symm⟩
  · intro j hj
    apply hzδD
    dsimp [Dset]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj.symm⟩


/-- `2*d < 3^d` for `1 ≤ d` (low-dimension pigeonhole) -/
lemma two_mul_lt_three_pow {d : ℕ} (hd : 1 ≤ d) : 2 * d < 3 ^ d := by
  induction d with
  | zero => omega
  | succ d ih =>
      by_cases hd1 : 1 ≤ d
      · have ih' : 2 * d < 3 ^ d := ih hd1
        have h2 : 2 * (d + 1) ≤ 3 * (2 * d) := by omega
        have h3 : 3 * (2 * d) < 3 * (3 ^ d) :=
          Nat.mul_lt_mul_of_pos_left ih' (by norm_num)
        have hstep : 2 * (d + 1) < 3 * (3 ^ d) := lt_of_le_of_lt h2 h3
        simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hstep
      · have hd0 : d = 0 := by omega
        subst d
        norm_num

/-- `n+1 < 3^n` for `1 ≤ n` -/
lemma succ_lt_three_pow {n : ℕ} (hn : 1 ≤ n) : n + 1 < 3 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn1 : 1 ≤ n
      · have ih' : n + 1 < 3 ^ n := ih hn1
        have hle : n + 2 ≤ 3 * (n + 1) := by omega
        have hlt : 3 * (n + 1) < 3 * 3 ^ n := Nat.mul_lt_mul_of_pos_left ih' (by norm_num)
        have hpow : 3 ^ (n + 1) = 3 * 3 ^ n := by
          rw [pow_succ]
          ring
        rw [hpow]
        exact lt_of_le_of_lt hle hlt
      · have hn0 : n = 0 := by omega
        subst n
        norm_num

/-- `d < 3^(d-1)` for `2 ≤ d` -/
lemma three_pow_pred_gt {d : ℕ} (hd : 2 ≤ d) : d < 3 ^ (d - 1) := by
  have h := succ_lt_three_pow (by omega : 1 ≤ d - 1)
  have hsub : d - 1 + 1 = d := by omega
  simpa [hsub] using h

/-- a Finset whose factors are all at least 3 has product at least `3^(card)` -/
lemma prod_ge_pow_card {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, 3 ≤ f i) : 3 ^ s.card ≤ s.prod f := by
  classical
  let P : Finset ι → Prop := fun t => (∀ i ∈ t, 3 ≤ f i) → 3 ^ t.card ≤ t.prod f
  have hmain : P s := by
    dsimp [P]
    refine Finset.induction_on s ?_ ?_
    · intro hf0
      simp
    · intro a t hat ih hft
      have hfa : 3 ≤ f a := hft a (Finset.mem_insert_self a t)
      have hih := ih (fun i hi => hft i (Finset.mem_insert_of_mem hi))
      calc
        3 ^ (insert a t).card = 3 ^ (t.card + 1) := by rw [Finset.card_insert_of_notMem hat]
        _ = 3 * 3 ^ t.card := by rw [pow_succ]; ring
        _ ≤ f a * 3 ^ t.card := Nat.mul_le_mul_right (3 ^ t.card) hfa
        _ ≤ f a * t.prod f := Nat.mul_le_mul_left (f a) hih
        _ = (insert a t).prod f := (Finset.prod_insert hat).symm
  exact hmain hf

/-- `N − |a| ≥ 3` when `|a| ≤ N−3` -/
lemma factor_ge_three_of_abs_le {N : ℕ} (hN : 3 ≤ N) (a : ℤ)
    (ha : |a| ≤ (N - 3 : ℤ)) : 3 ≤ (N : ℕ) - (Int.natAbs a : ℕ) := by
  have ha' : (Int.natAbs a : ℤ) ≤ (N - 3 : ℤ) := by
    simpa [RigidOverlap.int_abs_eq_natAbs a] using ha
  have hna : Int.natAbs a ≤ N - 3 := by exact_mod_cast ha'
  omega

/-- `N − |a| ≥ 3` when `|a| ≤ 2` and `N ≥ 5` -/
lemma factor_ge_three_of_abs_le_two {N : ℕ} (hN : 5 ≤ N) (a : ℤ)
    (ha : |a| ≤ (2 : ℤ)) : 3 ≤ (N : ℕ) - (Int.natAbs a : ℕ) := by
  have ha' : (Int.natAbs a : ℤ) ≤ (2 : ℤ) := by
    simpa [RigidOverlap.int_abs_eq_natAbs a] using ha
  have hna : Int.natAbs a ≤ 2 := by exact_mod_cast ha'
  omega

/-- two distinct elements of `Fin d` force `2 ≤ d` -/
lemma two_le_of_exists_ne {d : ℕ} {j k : Fin d} (h : j ≠ k) : 2 ≤ d := by
  classical
  let f : Fin 2 → Fin d := fun i => if (i : ℕ) = 0 then j else k
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [f] at hab ⊢ <;> tauto
  have hle := Fintype.card_le_of_injective f hf
  simpa using hle

/-- dimension-uniform free cell for the basis-tile click (no `d ≥ 3` restriction) -/
lemma basis_overlap_cell {d N : ℕ} (hN : 2 ≤ N) (δ : V d) (hδ0 : δ ≠ 0)
    (hδ : RigidOverlap.StrictBounded d N δ)
    (hbig : (2 : ℕ) * (Dset d).card < ∏ i : Fin d, ((N : ℕ) - (Int.natAbs (δ i) : ℕ))) :
    ∃ z : V d, z ∈ box d N ∧ z - δ ∈ box d N ∧
      (∀ j : Fin d, z ≠ xhole (d := d) j) ∧ (∀ j : Fin d, z - δ ≠ xhole (d := d) j) := by
  classical
  rcases RigidOverlap.overlap_big_box_avoid hN δ hδ (Dset d) hbig with
    ⟨z, hz1, hz2, hzD, hzδD⟩
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hz1 i
  · intro i
    exact hz2 i
  · intro j hj
    apply hzD
    dsimp [Dset]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj.symm⟩
  · intro j hj
    apply hzδD
    dsimp [Dset]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj.symm⟩

lemma inter_empty_of_no_common {α : Type*} {s t : Set α} (h : ∀ x, x ∈ s → x ∈ t → False) :
    s ∩ t = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (h x hx.1 hx.2)
  · intro hx
    exact False.elim (by simpa using hx)

/-- translates at distinct centres of a complement are disjoint -/
lemma complement_translates_disjoint {d : ℕ} {S T : Set (V d)}
    (h : AddSubgroup.IsComplement S T) {a b : V d} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) : ({a} + T) ∩ ({b} + T) = ∅ := by
  refine inter_empty_of_no_common ?_
  intro x hx1 hx2
  rcases Set.mem_add.mp hx1 with ⟨a1, ha1, t1, ht1, h1⟩
  rcases Set.mem_add.mp hx2 with ⟨b1, hb1, t2, ht2, h2⟩
  have haa1 : a1 = a := by simpa using ha1
  have hbb1 : b1 = b := by simpa using hb1
  subst a1
  subst b1
  have hu := h.existsUnique x
  rcases hu with ⟨y, hy, hyu⟩
  have hy1 : ((⟨a, ha⟩, ⟨t1, ht1⟩) : S × T) = y := by
    apply hyu
    simpa [h1]
  have hy2 : ((⟨b, hb⟩, ⟨t2, ht2⟩) : S × T) = y := by
    apply hyu
    simpa [h2]
  have hEq : ((⟨a, ha⟩, ⟨t1, ht1⟩) : S × T) = ((⟨b, hb⟩, ⟨t2, ht2⟩) : S × T) := hy1.trans hy2.symm
  have hEqFst := congrArg (fun z : S × T => (z.1 : V d)) hEq
  have : a = b := by simpa using hEqFst
  exact hab this

-- ----------------------------------------------------------------------
-- basis_click: a dent cell of a complement translate is covered by the
-- translate at distance N·e_j, giving the closure used by rigidity.
-- ----------------------------------------------------------------------

/-- dent cell of translate `c + T` is covered by the translate at `c - N e_j` -/
lemma basis_click {d N : ℕ} (hd : 1 ≤ d) (hN : 7 ≤ N) (A : Set (V d))
    (hTile : AddSubgroup.IsComplement A (basisTile d N))
    (c : V d) (hc : c ∈ A) (j : Fin d) : c - (N : ℤ) • eb d j ∈ A := by
  let p : V d := c + xhole (d := d) j
  have hp_not : p ∉ ({c} + basisTile d N) := by
    intro hp
    rcases Set.mem_add.mp hp with ⟨a, ha, t, ht, hsum⟩
    have ha' : a = c := by simpa using ha
    subst a
    have hx : xhole (d := d) j = t := by
      apply funext
      intro i
      have hi := congrFun hsum i
      simp [Pi.add_apply, p] at hi ⊢
      omega
    exact xhole_not_mem_basisTile hN j (by simpa [hx] using ht)
  have hu := hTile.existsUnique p
  rcases hu with ⟨y, hy, hyu⟩
  let w : V d := (y.1 : V d)
  let t : V d := (y.2 : V d)
  have hwA : w ∈ A := by simpa [w] using y.1.2
  have htT : t ∈ basisTile d N := by simpa [t] using y.2.2
  have hwt : w + t = p := by
    change (y.1 : V d) + (y.2 : V d) = p
    simpa [w, t] using hy
  have hw_ne_c : w ≠ c := by
    intro hwc
    have hp' : p ∈ ({c} + basisTile d N) := by
      rw [← hwc]
      exact Set.mem_add.mpr ⟨w, by simp, t, htT, hwt⟩
    exact hp_not hp'
  unfold basisTile dentedTile at htT
  rw [Set.mem_union] at htT
  rcases htT with htBody | htBump
  · -- t in body: δ = xhole j - t bounded; overlap contradiction
    rw [Set.mem_diff] at htBody
    have htBox : t ∈ box d N := htBody.1
    let δ : V d := xhole (d := d) j - t
    have hδ0 : δ ≠ 0 := by
      intro hδ
      have hδb' : δ = w - c := by
        apply funext
        intro i
        have hi := congrFun hwt i
        simp [p, δ, Pi.add_apply, Pi.sub_apply] at hi ⊢
        omega
      rw [hδ] at hδb'
      have : w = c := by
        apply funext
        intro i
        have hi := congrFun hδb' i
        simp [Pi.sub_apply] at hi
        omega
      exact hw_ne_c this
    have hδN3 : ∀ i, |δ i| ≤ (N : ℤ) - 3 := by
      intro i
      have hx : |xhole (d := d) j i - t i| ≤ (N : ℤ) - 3 := by
        have htlo : (0 : ℤ) ≤ t i := (htBox i).1
        have hthi : t i < (N : ℤ) := (htBox i).2
        rcases xhole_val j i with hv | hv <;> rw [hv]
        · apply abs_le.mpr
          constructor <;> omega
        · apply abs_le.mpr
          constructor <;> omega
      simpa [δ, Pi.sub_apply] using hx
    have hδstr : RigidOverlap.StrictBounded d N δ := by
      intro i
      exact le_trans (hδN3 i) (by omega : (N : ℤ) - 3 ≤ (N : ℤ) - 2)
    have hbig : (2 : ℕ) * (Dset d).card < ∏ i : Fin d, ((N : ℕ) - (Int.natAbs (δ i) : ℕ)) := by
      rw [Dset_card]
      have hfac : ∀ i : Fin d, 3 ≤ (N : ℕ) - (Int.natAbs (δ i) : ℕ) := by
        intro i
        exact factor_ge_three_of_abs_le (by omega : 3 ≤ N) (δ i) (hδN3 i)
      have hp := prod_ge_pow_card (s := (Finset.univ : Finset (Fin d)))
        (fun i : Fin d => (N : ℕ) - (Int.natAbs (δ i) : ℕ)) (by intro i hi; exact hfac i)
      have hprod : 3 ^ d ≤ ∏ i : Fin d, ((N : ℕ) - (Int.natAbs (δ i) : ℕ)) := by
        simpa using hp
      have hlt : 2 * d < 3 ^ d := two_mul_lt_three_pow hd
      exact lt_of_lt_of_le (by simpa using hlt) hprod
    have hδb : δ = w - c := by
      apply funext
      intro i
      have hi := congrFun hwt i
      simp [p, δ, Pi.add_apply, Pi.sub_apply] at hi ⊢
      omega
    rcases basis_overlap_cell (by omega : 2 ≤ N) δ hδ0 hδstr hbig with ⟨z, hz1, hz2, hzn, hzδn⟩
    have hzT : z ∈ basisTile d N := by
      apply basisTile_body_mem hz1
      rw [Dset_mem]
      rintro ⟨m, hm⟩
      exact hzn m hm
    have hzδT : z - δ ∈ basisTile d N := by
      apply basisTile_body_mem hz2
      rw [Dset_mem]
      rintro ⟨m, hm⟩
      exact hzδn m hm
    have hc1 : c + z ∈ ({c} + basisTile d N) := Set.mem_add.mpr ⟨c, by simp, z, hzT, rfl⟩
    have hc2 : c + z ∈ ({w} + basisTile d N) := by
      refine Set.mem_add.mpr ⟨w, by simp, z - δ, hzδT, ?_⟩
      apply funext
      intro i
      have hδi := congrFun hδb i
      simp [Pi.add_apply, Pi.sub_apply] at hδi ⊢
      omega
    have hdisj := complement_translates_disjoint hTile hwA hc hw_ne_c
    have hmem : c + z ∈ ({c} + basisTile d N) ∩ ({w} + basisTile d N) := ⟨hc1, hc2⟩
    have hmem2 : c + z ∈ ({w} + basisTile d N) ∩ ({c} + basisTile d N) := by
      simpa [Set.inter_comm] using hmem
    rw [hdisj] at hmem2
    exact False.elim (by simpa using hmem2)
  · -- t is a bump
    rw [Set.mem_image] at htBump
    rcases htBump with ⟨d0, hd0, htkeq⟩
    rcases Dset_mem.mp hd0 with ⟨k, hd0eq⟩
    have htk : t = xhole (d := d) k + (N : ℤ) • eb d k := by
      calc
        t = d0 + (N : ℤ) • uBump d0 := htkeq.symm
        _ = xhole (d := d) k + (N : ℤ) • eb d k := by rw [hd0eq, uBump_eq k]
    by_cases hjk : k = j
    · subst k
      have hw : w = c - (N : ℤ) • eb d j := by
        apply funext
        intro i
        have hi := congrFun hwt i
        simp [p, t, htk, Pi.add_apply, Pi.sub_apply] at hi ⊢
        omega
      rw [← hw]
      exact hwA
    · -- mismatched bump: δ bounded; overlap contradiction
      let δ : V d := xhole (d := d) j - xhole (d := d) k - (N : ℤ) • eb d k
      have hδ0 : δ ≠ 0 := by
        intro hδ
        have hδk := congrFun hδ k
        have hjk' : j ≠ k := fun hjk2 => hjk hjk2.symm
        have hdk : δ k = (2 : ℤ) - (N : ℤ) := by
          simp [δ, Pi.sub_apply, Pi.smul_apply, xhole_other hjk', xhole_self k, eb_apply k]
        have hk0 : (2 : ℤ) - (N : ℤ) = 0 := by simpa [hdk] using hδk
        have hN7i : (7 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
        omega
      have hδstr : RigidOverlap.StrictBounded d N δ := by
        intro i
        have hN7i : (7 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
        by_cases hik : i = k
        · subst i
          have hjk' : j ≠ k := fun hjk2 => hjk hjk2.symm
          have hv : |xhole (d := d) j k - xhole (d := d) k k - (N : ℤ) * (1 : ℤ)| ≤ (N : ℤ) - 2 := by
            simp [xhole_self k, xhole_other hjk']
            apply abs_le.mpr
            constructor <;> omega
          simpa [δ, Pi.sub_apply, Pi.smul_apply, eb_apply k] using hv
        · have hki : k ≠ i := fun hki2 => hik hki2.symm
          have hle2 : |xhole (d := d) j i - xhole (d := d) k i| ≤ (2 : ℤ) := xhole_diff_le_two j k i
          have hN2 : (2 : ℤ) ≤ (N : ℤ) - 2 := by omega
          have hval : |xhole (d := d) j i - xhole (d := d) k i| ≤ (N : ℤ) - 2 :=
            le_trans hle2 hN2
          have : |δ i| ≤ (N : ℤ) - 2 := by
            simpa [δ, Pi.sub_apply, Pi.smul_apply, eb_apply_ne hki] using hval
          exact this
      have hjk' : j ≠ k := fun hjk2 => hjk hjk2.symm
      have hd2 : 2 ≤ d := two_le_of_exists_ne hjk'
      have hδi_le_two : ∀ i, i ≠ k → |δ i| ≤ (2 : ℤ) := by
        intro i hik
        have hki : k ≠ i := fun h => hik h.symm
        have hval : |xhole (d := d) j i - xhole (d := d) k i| ≤ (2 : ℤ) := xhole_diff_le_two j k i
        have : |δ i| ≤ (2 : ℤ) := by
          simpa [δ, Pi.sub_apply, Pi.smul_apply, eb_apply_ne hki] using hval
        exact this
      have hbig : (2 : ℕ) * (Dset d).card < ∏ i : Fin d, ((N : ℕ) - (Int.natAbs (δ i) : ℕ)) := by
        rw [Dset_card]
        let g : Fin d → ℕ := fun i => (N : ℕ) - (Int.natAbs (δ i) : ℕ)
        have hgk2 : 2 ≤ g k := by
          dsimp [g]
          exact RigidOverlap.bounded_abs_factor_ge_two (by omega : 2 ≤ N) (δ k) (hδstr k)
        have hgi3 : ∀ i, i ≠ k → 3 ≤ g i := by
          intro i hik
          dsimp [g]
          exact factor_ge_three_of_abs_le_two (by omega : 5 ≤ N) (δ i) (hδi_le_two i hik)
        have hpe := prod_ge_pow_card (s := (Finset.univ.erase k : Finset (Fin d))) g
          (by intro i hi; exact hgi3 i (by
            intro hik
            exact (Finset.mem_erase.mp hi).1 hik))
        have hcard : (Finset.univ.erase k).card = d - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ k)]
          simp
        have hprod_erase : 3 ^ (d - 1) ≤ (Finset.univ.erase k).prod g := by
          simpa [hcard] using hpe
        have hprod : 2 * 3 ^ (d - 1) ≤ ∏ i : Fin d, g i := by
          have hsplit : (∏ i : Fin d, g i) = g k * (Finset.univ.erase k).prod g := by
            have h := Finset.prod_erase_mul (s := (Finset.univ : Finset (Fin d))) (f := g)
              (a := k) (Finset.mem_univ k)
            rw [← h]
            simp [mul_comm]
          rw [hsplit]
          exact Nat.mul_le_mul hgk2 hprod_erase
        have hlt : 2 * d < 2 * 3 ^ (d - 1) := by
          have hgt : d < 3 ^ (d - 1) := three_pow_pred_gt hd2
          omega
        exact lt_of_lt_of_le hlt (by simpa [g] using hprod)
      have hδb : δ = w - c := by
        apply funext
        intro i
        have hi := congrFun hwt i
        simp [p, δ, htk, Pi.add_apply, Pi.sub_apply] at hi ⊢
        omega
      rcases basis_overlap_cell (by omega : 2 ≤ N) δ hδ0 hδstr hbig with ⟨z, hz1, hz2, hzn, hzδn⟩
      have hzT : z ∈ basisTile d N := by
        apply basisTile_body_mem hz1
        rw [Dset_mem]
        rintro ⟨m, hm⟩
        exact hzn m hm
      have hzδT : z - δ ∈ basisTile d N := by
        apply basisTile_body_mem hz2
        rw [Dset_mem]
        rintro ⟨m, hm⟩
        exact hzδn m hm
      have hc1 : c + z ∈ ({c} + basisTile d N) := Set.mem_add.mpr ⟨c, by simp, z, hzT, rfl⟩
      have hc2 : c + z ∈ ({w} + basisTile d N) := by
        refine Set.mem_add.mpr ⟨w, by simp, z - δ, hzδT, ?_⟩
        apply funext
        intro i
        have hδi := congrFun hδb i
        simp [Pi.add_apply, Pi.sub_apply] at hδi ⊢
        omega
      have hdisj := complement_translates_disjoint hTile hwA hc hw_ne_c
      have hmem : c + z ∈ ({c} + basisTile d N) ∩ ({w} + basisTile d N) := ⟨hc1, hc2⟩
      have hmem2 : c + z ∈ ({w} + basisTile d N) ∩ ({c} + basisTile d N) := by
        simpa [Set.inter_comm] using hmem
      rw [hdisj] at hmem2
      exact False.elim (by simpa using hmem2)

-- ----------------------------------------------------------------------
-- g1 final: single-tile rigidity of the basis tile (verbatim from g1).
-- ----------------------------------------------------------------------

def NVsub (d N : ℕ) : AddSubgroup (V d) where
  carrier := NV d N
  zero_mem' := by
    rw [mem_NV_iff]
    intro i
    exact ⟨0, by simp⟩
  add_mem' := by
    intro a b ha hb
    rw [mem_NV_iff] at ha hb ⊢
    intro i
    rcases ha i with ⟨ca, hca⟩
    rcases hb i with ⟨cb, hcb⟩
    refine ⟨ca + cb, ?_⟩
    rw [Pi.add_apply]
    rw [hca, hcb]
    ring
  neg_mem' := by
    intro a ha
    rw [mem_NV_iff] at ha ⊢
    intro i
    rcases ha i with ⟨ca, hca⟩
    refine ⟨-ca, ?_⟩
    rw [Pi.neg_apply, hca]
    ring

/-- `(Σ_i q_i • (N e_i)) = N • q` -/
lemma sum_smul_basis_eq_smul {d N : ℕ} (q : V d) :
    (∑ i : Fin d, (q i) • ((N : ℤ) • eb d i)) = (N : ℤ) • q := by
  apply funext
  intro j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp [Pi.smul_apply, eb_apply j, mul_comm, mul_left_comm, mul_assoc]
  · intro i hi hne
    have hne' : j ≠ i := fun hji => hne hji.symm
    simp [Pi.smul_apply, eb_apply_ne hne]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

/-- `Nℤ^d` equals the subgroup generated by the `N e_j` -/
lemma NV_eq_closure_basis {d N : ℕ} (hN : 0 < N) :
    (NV d N : Set (V d)) =
      (AddSubgroup.closure (Set.range (fun j : Fin d => (N : ℤ) • eb d j)) : Set (V d)) := by
  ext x
  constructor
  · intro hx
    have hxq : x = (N : ℤ) • quot N x := NV_eq_smul_quot hN hx
    rw [hxq]
    rw [← sum_smul_basis_eq_smul (quot N x)]
    apply AddSubgroup.sum_mem (AddSubgroup.closure (Set.range (fun j : Fin d => (N : ℤ) • eb d j)))
    intro i hi
    apply AddSubgroup.zsmul_mem (AddSubgroup.closure (Set.range (fun j : Fin d => (N : ℤ) • eb d j)))
    exact AddSubgroup.subset_closure ⟨i, rfl⟩
  · intro hx
    have hle : (AddSubgroup.closure (Set.range (fun j : Fin d => (N : ℤ) • eb d j)) : AddSubgroup (V d)) ≤
        NVsub d N := by
      rw [AddSubgroup.closure_le]
      intro z hz
      rcases hz with ⟨j, rfl⟩
      change (N : ℤ) • eb d j ∈ NV d N
      rw [mem_NV_iff]
      intro i
      by_cases h : i = j
      · rw [h]
        refine ⟨1, ?_⟩
        simp [Pi.smul_apply, eb_apply j]
      · have hji : j ≠ i := fun hji => h hji.symm
        refine ⟨0, ?_⟩
        simp [Pi.smul_apply, eb_apply_ne hji]
    change x ∈ (NVsub d N : Set (V d))
    exact hle hx

/-- `A + {p}` is the translate of `A` by `+p` -/
lemma set_add_singleton_eq_shift {d : ℕ} (p : V d) (A : Set (V d)) :
    A + ({p} : Set (V d)) = (fun x : V d => x + p) '' A := by
  ext x
  constructor
  · rw [Set.mem_add]
    rintro ⟨a, ha, p0, hp0, hsum⟩
    have hp : p0 = p := by simpa using hp0
    subst p0
    rw [Set.mem_image]
    exact ⟨a, ha, hsum⟩
  · rw [Set.mem_add, Set.mem_image]
    rintro ⟨a, ha, hsum⟩
    exact ⟨a, ha, p, by simp, hsum⟩

/-- composing two translations -/
lemma shift_comp {d : ℕ} (h k : V d) (A : Set (V d)) :
    (fun x : V d => x + k) '' ((fun x : V d => x + h) '' A) =
      (fun x : V d => x + (h + k)) '' A := by
  rw [Set.image_image]
  congr 1
  funext x
  abel

/-- translates of a complement are complements -/
lemma IsComplement_vsub_image {d : ℕ} (p : V d) {A T : Set (V d)}
    (h : AddSubgroup.IsComplement A T) :
    AddSubgroup.IsComplement ((fun x : V d => x - p) '' A) T := by
  rw [AddSubgroup.isComplement_iff_existsUnique]
  intro g
  have hu := h.existsUnique (g + p)
  rcases hu with ⟨y, hy, hyu⟩
  have hmem : (y.1 : V d) - p ∈ ((fun x : V d => x - p) '' A) := by
    rw [Set.mem_image]
    exact ⟨(y.1 : V d), y.1.2, rfl⟩
  let wy : ({x : V d // x ∈ (fun x : V d => x - p) '' A}) × {x : V d // x ∈ T} :=
    (⟨(y.1 : V d) - p, hmem⟩, ⟨(y.2 : V d), y.2.2⟩)
  refine ⟨wy, ?_, ?_⟩
  · change ((y.1 : V d) - p) + (y.2 : V d) = g
    apply funext
    intro i
    have hi := congrFun hy i
    simp [Pi.add_apply, Pi.sub_apply] at hi ⊢
    omega
  · intro z hz
    rcases z with ⟨za, zt⟩
    rcases za with ⟨zaV, hza⟩
    rw [Set.mem_image] at hza
    rcases hza with ⟨a, ha, hzaeq⟩
    have hz' : zaV + (zt : V d) = g := by
      change zaV + (zt : V d) = g
      simpa using hz
    have hsumA : a + (zt : V d) = g + p := by
      apply funext
      intro i
      have h1 := congrFun hz' i
      have h2 := congrFun hzaeq i
      simp [Pi.add_apply, Pi.sub_apply] at h1 h2 ⊢
      omega
    have hyuA : ((⟨a, ha⟩, ⟨(zt : V d), zt.2⟩) : A × T) = y := by
      apply hyu
      simpa [hsumA]
    have hfs := congrArg (fun w : A × T => (w.1 : V d)) hyuA
    have hss := congrArg (fun w : A × T => (w.2 : V d)) hyuA
    apply Prod.ext
    · apply Subtype.ext
      apply funext
      intro i
      have h1 := congrFun hfs i
      have h2 := congrFun hzaeq i
      change zaV i = ((y.1 : V d) - p) i
      simp [Pi.sub_apply] at h1 h2 ⊢
      omega
    · apply Subtype.ext
      simpa using hss

lemma complement_subset_eq {d : ℕ} {A A' T : Set (V d)}
    (hA' : AddSubgroup.IsComplement A' T) (hA : AddSubgroup.IsComplement A T)
    (hsub : A' ⊆ A) (h0T : (0 : V d) ∈ T) : A' = A := by
  apply le_antisymm
  · exact hsub
  · intro a ha
    have hu := hA.existsUnique a
    rcases hu with ⟨y, hy, hyu⟩
    let y0 : A × T := (⟨a, ha⟩, ⟨0, h0T⟩)
    have hy0 : (y0.1 : V d) + (y0.2 : V d) = a := by
      change a + 0 = a
      simp
    have hy0' : y0 = y := hyu y0 hy0
    have hcov : a ∈ (A' + T) := by
      rw [hA'.add_eq]
      trivial
    rcases Set.mem_add.mp hcov with ⟨a1, ha1, t1, ht1, hsum⟩
    have hy1 : (((⟨a1, hsub ha1⟩ : A), (⟨t1, ht1⟩ : T)) : A × T) = y := by
      apply hyu
      simpa [hsum]
    have hpair : ((⟨a1, hsub ha1⟩ : A), (⟨t1, ht1⟩ : T)) =
        ((⟨a, ha⟩ : A), (⟨0, h0T⟩ : T)) := hy1.trans hy0'.symm
    have hfst := congrArg (fun w : A × T => (w.1 : V d)) hpair
    have ha1a : a1 = a := by simpa using hfst
    exact ha1a ▸ ha1

/-- single-tile rigidity: the only complement of `basisTile` containing `0` is `NV` -/
theorem basis_rigid {d N : ℕ} (hd : 1 ≤ d) (hN : 7 ≤ N) :
    ∀ A : Set (V d), AddSubgroup.IsComplement A (basisTile d N) →
      (0 : V d) ∈ A → A = NV d N := by
  intro A hA h0A
  let S : AddSubgroup (V d) := {
    carrier := {h : V d | A + ({h} : Set (V d)) = A}
    zero_mem' := by
      change A + ({(0 : V d)} : Set (V d)) = A
      ext x
      simp [Set.mem_add]
    add_mem' := by
      intro h k hh hk
      change A + ({h + k} : Set (V d)) = A
      have hh' : (fun x : V d => x + h) '' A = A := by
        simpa [set_add_singleton_eq_shift] using hh
      have hk' : (fun x : V d => x + k) '' A = A := by
        simpa [set_add_singleton_eq_shift] using hk
      rw [set_add_singleton_eq_shift]
      calc
        (fun x : V d => x + (h + k)) '' A
            = (fun x : V d => x + k) '' ((fun x : V d => x + h) '' A) :=
              (shift_comp h k A).symm
        _ = (fun x : V d => x + k) '' A := by rw [hh']
        _ = A := hk'
    neg_mem' := by
      intro h hh
      change A + ({-h} : Set (V d)) = A
      have hh' : (fun x : V d => x + h) '' A = A := by
        simpa [set_add_singleton_eq_shift] using hh
      rw [set_add_singleton_eq_shift]
      calc
        (fun x : V d => x + (-h)) '' A
            = (fun x : V d => x + (-h)) '' ((fun x : V d => x + h) '' A) := by rw [hh']
        _ = (fun x : V d => x + (h + (-h))) '' A := by
              rw [Set.image_image]
              congr 1
              funext x
              abel
        _ = A := by
              have hid : (fun x : V d => x + (h + (-h))) = id := by
                funext x
                abel
              simp [hid]
  }
  have hgen : ∀ j : Fin d, (N : ℤ) • eb d j ∈ (S : Set (V d)) := by
    intro j
    change A + ({(N : ℤ) • eb d j} : Set (V d)) = A
    let p : V d := (N : ℤ) • eb d j
    have hClick : ∀ c : V d, c ∈ A → c - p ∈ A := by
      intro c hc
      simpa [p] using (basis_click hd hN A hA c hc j)
    have hAp : (fun x : V d => x - p) '' A ⊆ A := by
      intro x hx
      rw [Set.mem_image] at hx
      rcases hx with ⟨c, hc, hx⟩
      rw [← hx]
      exact hClick c hc
    have hApComp : AddSubgroup.IsComplement ((fun x : V d => x - p) '' A) (basisTile d N) :=
      IsComplement_vsub_image p hA
    have hApEq : ((fun x : V d => x - p) '' A) = A :=
      complement_subset_eq hApComp hA hAp (zero_mem_basisTile (by omega : 1 ≤ N))
    rw [set_add_singleton_eq_shift]
    calc
      (fun x : V d => x + p) '' A = (fun x : V d => x + p) '' ((fun x : V d => x - p) '' A) := by
        rw [hApEq]
      _ = A := by
        rw [Set.image_image]
        simp [sub_add_cancel]
  have hle : AddSubgroup.closure (Set.range (fun j : Fin d => (N : ℤ) • eb d j)) ≤ S := by
    rw [AddSubgroup.closure_le]
    intro x hx
    rcases hx with ⟨j, rfl⟩
    exact hgen j
  have hNVS : ∀ h : V d, h ∈ NV d N → A + ({h} : Set (V d)) = A := by
    intro h hh
    have hcl : h ∈ (AddSubgroup.closure (Set.range (fun j : Fin d => (N : ℤ) • eb d j)) : Set (V d)) := by
      rw [← NV_eq_closure_basis (by omega : 0 < N)]
      exact hh
    exact hle hcl
  have hNVsubA : NV d N ⊆ A := by
    intro h hh
    have hshift : A + ({h} : Set (V d)) = A := hNVS h hh
    have hmem : h ∈ A + ({h} : Set (V d)) := by
      refine Set.mem_add.mpr ⟨0, h0A, h, by simp, by simp⟩
    simpa [hshift] using hmem
  have hEq : NV d N = A :=
    complement_subset_eq (NV_IsComplement_basisTile (by omega : 5 ≤ N)) hA hNVsubA
      (zero_mem_basisTile (by omega : 1 ≤ N))
  exact hEq.symm


-- ----------------------------------------------------------------------
-- Port of g1.lean tail: margin overlap and shells (verbatim).
-- ----------------------------------------------------------------------

def marginCore (d : ℕ) (K N : ℕ) : Set (V d) :=
  {x | ∀ i : Fin d, (K : ℤ) ≤ x i ∧ x i ≤ (N : ℤ) - 1 - (K : ℤ)}

/-- the corner cell has a coordinate equal to 0 or N-1, so it avoids the margin
core when `K ≥ 1` -/
lemma corner_not_mem_marginCore {d N K : ℕ} (hd : 0 < d) (hK : 1 ≤ K)
    (δ : V d) : RigidOverlap.corner d (N := N) δ ∉ marginCore d K N := by
  intro hz
  let i0 : Fin d := ⟨0, hd⟩
  have hi := hz i0
  by_cases hsign : (0 : ℤ) ≤ δ i0
  · have hval : RigidOverlap.corner d (N := N) δ i0 = (N : ℤ) - 1 := by
      simp [RigidOverlap.corner, hsign]
    have hKz : (K : ℤ) ≤ RigidOverlap.corner d (N := N) δ i0 := hi.1
    rw [hval] at hKz
    omega
  · have hval : RigidOverlap.corner d (N := N) δ i0 = 0 := by
      simp [RigidOverlap.corner, hsign]
    have hKz : (K : ℤ) ≤ RigidOverlap.corner d (N := N) δ i0 := hi.1
    rw [hval] at hKz
    omega

/-- small coordinate range forces `|δ|` to be near `N` -/
lemma abs_ge_of_cellLen_le {d N K : ℕ} {δ : V d} (i : Fin d)
    (hδ : RigidOverlap.StrictBounded d N δ)
    (hlen : RigidOverlap.cellLen d N δ i ≤ K) : (N : ℤ) - (K : ℤ) ≤ |δ i| := by
  have hnat : Int.natAbs (δ i) ≤ N := by
    have h1 : |δ i| ≤ (N : ℤ) := by
      exact le_trans (hδ i) (by omega)
    exact RigidOverlap.natAbs_le_of_abs_le h1
  have hcast : (RigidOverlap.cellLen d N δ i : ℤ) = (N : ℤ) - |δ i| := by
    rw [RigidOverlap.cellLen]
    rw [Int.ofNat_sub hnat]
    rw [RigidOverlap.int_abs_eq_natAbs (δ i)]
  have hlenZ : (RigidOverlap.cellLen d N δ i : ℤ) ≤ (K : ℤ) := by exact_mod_cast hlen
  rw [hcast] at hlenZ
  omega

/-- `corner - δ` also avoids the margin core when all coordinate ranges are small -/
lemma corner_sub_not_mem_marginCore {d N K : ℕ} (hd : 0 < d) (hK : 1 ≤ K)
    (δ : V d) (hδ : RigidOverlap.StrictBounded d N δ)
    (hsmall : ∀ i : Fin d, RigidOverlap.cellLen d N δ i ≤ K) :
    RigidOverlap.corner d (N := N) δ - δ ∉ marginCore d K N := by
  intro hz
  let i0 : Fin d := ⟨0, hd⟩
  have hi := hz i0
  have habs := abs_ge_of_cellLen_le (N := N) (K := K) i0 hδ (hsmall i0)
  by_cases hsign : (0 : ℤ) ≤ δ i0
  · have hval : (RigidOverlap.corner d (N := N) δ - δ) i0 = (N : ℤ) - 1 - δ i0 := by
      simp [RigidOverlap.corner, hsign, Pi.sub_apply]
    have hlow : (K : ℤ) ≤ (RigidOverlap.corner d (N := N) δ - δ) i0 := hi.1
    rw [hval] at hlow
    have hdge : (N : ℤ) - (K : ℤ) ≤ δ i0 := by
      have h2 : |δ i0| = δ i0 := abs_of_nonneg hsign
      simpa [h2] using habs
    omega
  · have hneg : δ i0 < 0 := lt_of_not_ge hsign
    have hval : (RigidOverlap.corner d (N := N) δ - δ) i0 = -(δ i0) := by
      simp [RigidOverlap.corner, hsign, Pi.sub_apply]
    have hupper : (RigidOverlap.corner d (N := N) δ - δ) i0 ≤ (N : ℤ) - 1 - (K : ℤ) := hi.2
    rw [hval] at hupper
    have h2 : |δ i0| = -δ i0 := abs_of_neg hneg
    have hdge : (N : ℤ) - (K : ℤ) ≤ -(δ i0) := by
      simpa [h2] using habs
    omega

/-- overlap of two dented-box translates at bounded displacement, where all dent
cells lie in the deep interior (margin `K`): a free cell exists -/
lemma margin_overlap {d N K : ℕ} (hd : 0 < d) (hK : 2 ≤ K) (hN2 : 2 ≤ N)
    (D : Finset (V d)) (hDm : ∀ x ∈ (D : Set (V d)), x ∈ marginCore d K N)
    (hDbig : (2 : ℕ) * D.card < (K + 1) * 2 ^ (d - 1))
    (δ : V d) (hδ0 : δ ≠ 0) (hδ : RigidOverlap.StrictBounded d N δ) :
    ∃ z : V d, z ∈ box d N ∧ z - δ ∈ box d N ∧ z ∉ (D : Set (V d)) ∧ z - δ ∉ (D : Set (V d)) := by
  classical
  by_cases hsmall : ∀ i : Fin d, RigidOverlap.cellLen d N δ i ≤ K
  · let z : V d := RigidOverlap.corner d (N := N) δ
    refine ⟨z, ?_, ?_, ?_, ?_⟩
    · exact RigidOverlap.corner_mem_box (by omega : 0 < N) δ
    · exact RigidOverlap.corner_sub_mem_box (RigidOverlap.Bounded_of_StrictBounded hδ)
    · intro hzD
      exact corner_not_mem_marginCore hd (by omega : 1 ≤ K) δ (hDm z hzD)
    · intro hzD
      exact corner_sub_not_mem_marginCore hd (by omega : 1 ≤ K) δ hδ hsmall
        (hDm (z - δ) hzD)
  · have hnotsmall : ∃ i0 : Fin d, K < RigidOverlap.cellLen d N δ i0 := by
      push_neg at hsmall
      rcases hsmall with ⟨i0, hi0⟩
      exact ⟨i0, by omega⟩
    rcases hnotsmall with ⟨i0, hi0⟩
    have hf0 : K + 1 ≤ RigidOverlap.cellLen d N δ i0 := by omega
    have hfac2 : ∀ i : Fin d, 2 ≤ RigidOverlap.cellLen d N δ i := by
      intro i
      exact RigidOverlap.bounded_abs_factor_ge_two hN2 (δ i) (hδ i)
    have hpf := Finset.prod_erase_mul (Finset.univ : Finset (Fin d))
      (fun i : Fin d => RigidOverlap.cellLen d N δ i) (Finset.mem_univ i0)
    have hdpos : 0 < d := by
      have := i0.isLt
      omega
    have hcard : ((Finset.univ : Finset (Fin d)).erase i0).card = d - 1 := by
      have hce := Finset.card_erase_add_one (s := (Finset.univ : Finset (Fin d))) (a := i0) (Finset.mem_univ i0)
      have hfin : Fintype.card (Fin d) = d := by simp
      rw [Finset.card_univ, hfin] at hce
      omega
    have hbig_erase : (2 : ℕ) ^ (d - 1) ≤
        ∏ x ∈ ((Finset.univ : Finset (Fin d)).erase i0), RigidOverlap.cellLen d N δ x := by
      rw [← hcard]
      calc
        (2 : ℕ) ^ (((Finset.univ : Finset (Fin d)).erase i0).card) =
            ∏ x ∈ ((Finset.univ : Finset (Fin d)).erase i0), (2 : ℕ) := by simp
        _ ≤ ∏ x ∈ ((Finset.univ : Finset (Fin d)).erase i0), RigidOverlap.cellLen d N δ x := by
          exact Finset.prod_le_prod (fun x hx => by omega) (fun x hx => hfac2 x)
    have hchain : (K + 1) * 2 ^ (d - 1) ≤ ∏ i : Fin d, RigidOverlap.cellLen d N δ i := by
      rw [← hpf]
      rw [Nat.mul_comm (∏ x ∈ ((Finset.univ : Finset (Fin d)).erase i0), RigidOverlap.cellLen d N δ x)
        (RigidOverlap.cellLen d N δ i0)]
      calc
        (K + 1) * 2 ^ (d - 1) ≤ RigidOverlap.cellLen d N δ i0 * 2 ^ (d - 1) :=
          Nat.mul_le_mul_right (2 ^ (d - 1)) hf0
        _ ≤ RigidOverlap.cellLen d N δ i0 *
            (∏ x ∈ ((Finset.univ : Finset (Fin d)).erase i0), RigidOverlap.cellLen d N δ x) := by
              exact Nat.mul_le_mul_left (RigidOverlap.cellLen d N δ i0) hbig_erase
    have hbig : (2 : ℕ) * D.card < ∏ i : Fin d, RigidOverlap.cellLen d N δ i :=
      lt_of_lt_of_le hDbig hchain
    rcases RigidOverlap.overlap_big_box_avoid hN2 δ hδ D hbig with
      ⟨z, hz1, hz2, hzD, hzδD⟩
    refine ⟨z, ?_, ?_, hzD, hzδD⟩
    · intro i
      exact hz1 i
    · intro i
      exact hz2 i

/-- the L∞-shell of radius `R`: cells whose max coordinate magnitude is exactly `R` -/
def shell (d : ℕ) (R : ℕ) : Set (V d) :=
  {x | (∀ i : Fin d, |x i| ≤ (R : ℤ)) ∧ (∃ i : Fin d, |x i| = (R : ℤ))}

/-- membership in a shell is the max-coordinate condition -/
lemma shell_mem_iff {d R : ℕ} (x : V d) :
    x ∈ shell d R ↔ (∀ i : Fin d, |x i| ≤ (R : ℤ)) ∧ (∃ i : Fin d, |x i| = (R : ℤ)) := by
  rfl

/-- every coordinate of a shell cell is bounded by the radius -/
lemma shell_coord_le {d R : ℕ} {x : V d} (hx : x ∈ shell d R) (i : Fin d) :
    |x i| ≤ (R : ℤ) := hx.1 i

/-- shell cells reach the radius in some coordinate -/
lemma shell_coord_eq {d R : ℕ} {x : V d} (hx : x ∈ shell d R) :
    ∃ i : Fin d, |x i| = (R : ℤ) := hx.2

/-- the extreme cell `R e_i` lies in the shell -/
lemma smul_eb_mem_shell {d R : ℕ} (i : Fin d) : (R : ℤ) • eb d i ∈ shell d R := by
  rw [shell_mem_iff]
  constructor
  · intro j
    have hnonneg : (0 : ℤ) ≤ (R : ℤ) := by exact_mod_cast (Nat.zero_le R)
    by_cases h : j = i
    · rw [h]
      simp [Pi.smul_apply, eb_apply i, abs_mul, abs_of_nonneg hnonneg]
    · have hne : i ≠ j := fun hij => h hij.symm
      simp [Pi.smul_apply, eb_apply_ne hne]
  · exact ⟨i, by
      have hnonneg : (0 : ℤ) ≤ (R : ℤ) := by exact_mod_cast (Nat.zero_le R)
      simp [Pi.smul_apply, eb_apply i, abs_mul, abs_of_nonneg hnonneg]⟩

/-- the origin lies in the shell of radius 0 (when there is a coordinate) -/
lemma shell_zero_mem {d : ℕ} (hd : 0 < d) : (0 : V d) ∈ shell d 0 := by
  rw [shell_mem_iff]
  constructor
  · intro i
    simp
  · exact ⟨⟨0, hd⟩, by simp⟩

/-- shells are centrally symmetric -/
lemma neg_mem_shell {d R : ℕ} {x : V d} (hx : x ∈ shell d R) : -x ∈ shell d R := by
  rw [shell_mem_iff] at hx ⊢
  constructor
  · intro i
    simpa using hx.1 i
  · rcases hx.2 with ⟨i, hi⟩
    exact ⟨i, by simpa using hi⟩

/-- the vector with all coordinates `R` lies in the shell -/
lemma allc_mem_shell {d R : ℕ} (hd : 0 < d) :
    (fun _ : Fin d => (R : ℤ)) ∈ shell d R := by
  rw [shell_mem_iff]
  constructor
  · intro i
    have hnn : (0 : ℤ) ≤ (R : ℤ) := by exact_mod_cast (Nat.zero_le R)
    rw [abs_of_nonneg hnn]
  · exact ⟨⟨0, hd⟩, by
      have hnn : (0 : ℤ) ≤ (R : ℤ) := by exact_mod_cast (Nat.zero_le R)
      rw [abs_of_nonneg hnn]⟩

/-- an element of a translated shell pulls back by `- q` -/
lemma mem_translate_image_sub {d R' : ℕ} {x q : V d}
    (hx : x ∈ ((fun y : V d => q + y) '' shell d R')) : x - q ∈ shell d R' := by
  rw [Set.mem_image] at hx
  rcases hx with ⟨y, hy, hxy⟩
  have : x - q = y := by
    apply funext
    intro i
    have hi := congrFun hxy i
    simp [Pi.add_apply, Pi.sub_apply] at hi ⊢
    omega
  simpa [this] using hy

/-- containment of one shell in a translate of another forces equality of radii
and zero translation (when the smaller radius is positive) -/
lemma shell_subset_translate_imp {d R R' : ℕ} (hd : 0 < d) (hR : 1 ≤ R) (q : V d) :
    shell d R ⊆ (fun x : V d => q + x) '' shell d R' → R = R' ∧ q = 0 := by
  intro hSub
  let e0 : Fin d := ⟨0, hd⟩
  have hRle1 : (1 : ℤ) ≤ (R : ℤ) := by exact_mod_cast hR
  -- pullback: x ∈ S_R → x - q ∈ S_{R'}
  have hpb : ∀ x : V d, x ∈ shell d R → x - q ∈ shell d R' := by
    intro x hx
    exact mem_translate_image_sub (hSub hx)
  -- the all-+R and all--R cells live in S_R
  have hpp : (fun _ : Fin d => (R : ℤ)) ∈ shell d R := allc_mem_shell hd
  have hpm : -(fun _ : Fin d => (R : ℤ)) ∈ shell d R := neg_mem_shell hpp
  -- pointwise bounds on q from those two cells
  have hlow : ∀ j : Fin d, |(R : ℤ) - q j| ≤ (R' : ℤ) := by
    intro j
    have hy : (fun _ : Fin d => (R : ℤ)) - q ∈ shell d R' := hpb _ hpp
    simpa [Pi.sub_apply] using (shell_coord_le hy j)
  have hneg : ∀ j : Fin d, |-(R : ℤ) - q j| ≤ (R' : ℤ) := by
    intro j
    have hy : -(fun _ : Fin d => (R : ℤ)) - q ∈ shell d R' := hpb _ hpm
    have hj := shell_coord_le hy j
    simpa [Pi.sub_apply, Pi.neg_apply] using hj
  -- (R : ℤ) ≤ (R' : ℤ)
  have hRle : (R : ℤ) ≤ (R' : ℤ) := by
    have h1 := abs_le.mp (hlow e0)
    have h2 := abs_le.mp (hneg e0)
    by_cases hq : q e0 ≤ 0
    · have hc : (R : ℤ) ≤ (R : ℤ) - q e0 := by omega
      exact le_trans hc h1.2
    · have hqpos : 0 < q e0 := lt_of_not_ge hq
      have hc' : (R : ℤ) ≤ (R : ℤ) + q e0 := by omega
      have hu : (R : ℤ) + q e0 ≤ (R' : ℤ) := by omega
      exact le_trans hc' hu
  -- |q j| ≤ R' - R for every coordinate j
  have hqbd : ∀ j : Fin d, |q j| ≤ (R' : ℤ) - (R : ℤ) := by
    intro j
    have hj2' : |(R : ℤ) + q j| ≤ (R' : ℤ) := by
      have heq : (R : ℤ) + q j = -(-(R : ℤ) - q j) := by ring
      rw [heq, abs_neg]
      exact hneg j
    by_cases hqj : 0 ≤ q j
    · have hnn : |q j| = q j := abs_of_nonneg hqj
      have hnn' : |(R : ℤ) + q j| = (R : ℤ) + q j := by
        apply abs_of_nonneg
        omega
      rw [hnn]
      have hu : (R : ℤ) + q j ≤ (R' : ℤ) := by
        rwa [hnn'] at hj2'
      omega
    · have hqle : q j ≤ 0 := le_of_lt (lt_of_not_ge hqj)
      have hnn : |q j| = -q j := abs_of_neg (lt_of_not_ge hqj)
      have hnn' : |(R : ℤ) - q j| = (R : ℤ) - q j := by
        apply abs_of_nonneg
        omega
      rw [hnn]
      have hu : (R : ℤ) - q j ≤ (R' : ℤ) := by
        have hj := hlow j
        rwa [hnn'] at hj
      omega
  have hqlt : ∀ j : Fin d, |q j| < (R' : ℤ) := by
    intro j
    have hb := hqbd j
    omega
  -- the cell R e_{e0}: its pullback must reach radius exactly at coordinate e0
  let xe : V d := (R : ℤ) • eb d e0
  have hxe : xe ∈ shell d R := smul_eb_mem_shell e0
  have hye : xe - q ∈ shell d R' := hpb xe hxe
  rcases shell_coord_eq hye with ⟨i0, hi0⟩
  have hi0e : i0 = e0 := by
    by_contra hne
    have hne' : e0 ≠ i0 := fun he => hne he.symm
    have hval : (xe - q) i0 = -q i0 := by
      simp [xe, Pi.sub_apply, Pi.smul_apply, eb_apply_ne hne']
    have hc : |q i0| = (R' : ℤ) := by
      simpa [hval, abs_neg] using hi0
    exact (ne_of_lt (hqlt i0)) hc
  have hmain : |(R : ℤ) - q e0| = (R' : ℤ) := by
    have hxev : xe e0 = (R : ℤ) := by simp [xe, eb_apply e0]
    simpa [hxev, hi0e, Pi.sub_apply] using hi0
  -- the cell -R e_{e0}: same analysis
  let xm : V d := -(xe)
  have hxm : xm ∈ shell d R := neg_mem_shell hxe
  have hym : xm - q ∈ shell d R' := hpb xm hxm
  rcases shell_coord_eq hym with ⟨i1, hi1⟩
  have hi1e : i1 = e0 := by
    by_contra hne
    have hne' : e0 ≠ i1 := fun he => hne he.symm
    have hval : (xm - q) i1 = -q i1 := by
      simp [xm, xe, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, eb_apply_ne hne']
    have hc : |q i1| = (R' : ℤ) := by
      simpa [hval, abs_neg] using hi1
    exact (ne_of_lt (hqlt i1)) hc
  have hmain2 : |-(R : ℤ) - q e0| = (R' : ℤ) := by
    have hxev : xm e0 = -(R : ℤ) := by simp [xm, xe, eb_apply e0]
    simpa [hxev, hi1e, Pi.sub_apply] using hi1
  -- conclusion: R = R' and q = 0
  have hR'ge0 : (0 : ℤ) ≤ (R' : ℤ) := by exact_mod_cast (Nat.zero_le R')
  have hdiff : ((R : ℤ) - q e0) - (-(R : ℤ) - q e0) = (2 : ℤ) * (R : ℤ) := by ring
  have hRz : (R : ℤ) = (R' : ℤ) := by
    rcases (abs_eq hR'ge0).mp hmain with ha | ha
    · rcases (abs_eq hR'ge0).mp hmain2 with hb | hb
      · have hc : ((R : ℤ) - q e0) - (-(R : ℤ) - q e0) = (2 : ℤ) * (R' : ℤ) := by omega
        omega
      · omega
    · rcases (abs_eq hR'ge0).mp hmain2 with hb | hb
      · omega
      · omega
  have hq0 : q = 0 := by
    apply funext
    intro j
    have hb := hqbd j
    rw [hRz] at hb
    have habs : |q j| ≤ (0 : ℤ) := by
      simpa using hb
    have hnn : (0 : ℤ) ≤ |q j| := abs_nonneg (q j)
    have heq : |q j| = 0 := le_antisymm habs hnn
    exact abs_eq_zero.mp heq
  constructor
  · exact_mod_cast hRz
  · exact hq0

/-- shells of different positive radii are translate-incompatible -/
lemma shell_not_subset_translate {d R R' : ℕ} (hd : 0 < d) (hR : 1 ≤ R)
    (hRR' : R ≠ R') (q : V d) :
    ¬ shell d R ⊆ (fun x : V d => q + x) '' shell d R' := by
  intro hSub
  exact hRR' (shell_subset_translate_imp hd hR q hSub).1
-- ----------------------------------------------------------------------
-- Port of g2.lean (slice 1): tooth parameters through the deep-margin band.
-- ----------------------------------------------------------------------

def toothRadius (r : ℕ) (σ : Fin 2) (l : Fin r) : ℕ := σ.val * r + l.val + 1

/-- the index of the tooth (σ,l) among the 2r extra teeth (0-based) -/
def toothIdx (r : ℕ) (σ : Fin 2) (l : Fin r) : ℕ := σ.val * r + l.val

/-- the maximum extra-tooth radius -/
def Rmax (r : ℕ) : ℕ := 2 * r

/-- each extra-tooth radius is positive -/
lemma toothRadius_pos (r : ℕ) (σ : Fin 2) (l : Fin r) : 1 ≤ toothRadius r σ l := by
  dsimp [toothRadius]
  omega

/-- each extra-tooth radius is at most 2r -/
lemma toothRadius_le_Rmax (r : ℕ) (σ : Fin 2) (l : Fin r) : toothRadius r σ l ≤ Rmax r := by
  dsimp [toothRadius, Rmax]
  have hσ : σ.val = 0 ∨ σ.val = 1 := by omega
  have hl : l.val < r := l.isLt
  rcases hσ with hσ | hσ
  · rw [hσ]
    omega
  · rw [hσ]
    omega

/-- the index of a tooth is < 2r (with r = 0 there are no teeth at all) -/
lemma toothIdx_lt {r : ℕ} (hr : 0 < r) (σ : Fin 2) (l : Fin r) : toothIdx r σ l < 2 * r := by
  dsimp [toothIdx]
  have hσ : σ.val = 0 ∨ σ.val = 1 := by omega
  have hl : l.val < r := l.isLt
  rcases hσ with hσ | hσ
  · rw [hσ]
    omega
  · rw [hσ]
    omega

/-- the radius assignment is injective: distinct teeth have distinct radii -/
lemma toothRadius_inj {r : ℕ} (σ₁ σ₂ : Fin 2) (l₁ l₂ : Fin r)
    (h : toothRadius r σ₁ l₁ = toothRadius r σ₂ l₂) : σ₁ = σ₂ ∧ l₁ = l₂ := by
  have hc : σ₁.val * r + l₁.val = σ₂.val * r + l₂.val := by
    dsimp [toothRadius] at h
    omega
  have hσ₁ : σ₁.val = 0 ∨ σ₁.val = 1 := by omega
  have hσ₂ : σ₂.val = 0 ∨ σ₂.val = 1 := by omega
  rcases hσ₁ with hσ₁ | hσ₁ <;> rcases hσ₂ with hσ₂ | hσ₂
  · rw [hσ₁, hσ₂] at hc
    have hl : l₁.val = l₂.val := by simpa using hc
    constructor
    · apply Fin.ext
      omega
    · exact Fin.ext hl
  · rw [hσ₁, hσ₂] at hc
    exfalso
    have hl : l₁.val = l₂.val + r := by simpa [Nat.add_comm] using hc
    omega
  · rw [hσ₁, hσ₂] at hc
    exfalso
    have hl : l₁.val + r = l₂.val := by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hc
    omega
  · rw [hσ₁, hσ₂] at hc
    have hl : l₁.val = l₂.val := by simpa using hc
    constructor
    · apply Fin.ext
      omega
    · exact Fin.ext hl

/-- the index map is injective -/
lemma toothIdx_inj {r : ℕ} (σ₁ σ₂ : Fin 2) (l₁ l₂ : Fin r)
    (h : toothIdx r σ₁ l₁ = toothIdx r σ₂ l₂) : σ₁ = σ₂ ∧ l₁ = l₂ := by
  have hσ₁ : σ₁.val = 0 ∨ σ₁.val = 1 := by omega
  have hσ₂ : σ₂.val = 0 ∨ σ₂.val = 1 := by omega
  rcases hσ₁ with hσ₁ | hσ₁ <;> rcases hσ₂ with hσ₂ | hσ₂
  · have hl : l₁.val = l₂.val := by
      dsimp [toothIdx] at h
      rw [hσ₁, hσ₂] at h
      simpa using h
    constructor
    · apply Fin.ext
      omega
    · exact Fin.ext hl
  · exfalso
    dsimp [toothIdx] at h
    rw [hσ₁, hσ₂] at h
    have hl : l₁.val = l₂.val + r := by simpa [Nat.add_comm] using h
    omega
  · exfalso
    dsimp [toothIdx] at h
    rw [hσ₁, hσ₂] at h
    have hl : l₁.val + r = l₂.val := by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    omega
  · have hl : l₁.val = l₂.val := by
      dsimp [toothIdx] at h
      rw [hσ₁, hσ₂] at h
      simpa using h
    constructor
    · apply Fin.ext
      omega
    · exact Fin.ext hl

/-- tooth positions: the (σ,l)-tooth sits at the point all of whose coordinates
equal `V0 + toothIdx r σ l * sep` (distinct values, spaced by `sep`) -/
def toothPos {d : ℕ} (V0 sep : ℕ) (r : ℕ) (σ : Fin 2) (l : Fin r) : V d :=
  fun _ : Fin d => (V0 + toothIdx r σ l * sep : ℕ)

-- ----------------------------------------------------------------------
-- Concrete parameter values (chosen so that all inequalities used below hold).
-- ----------------------------------------------------------------------

/-- the "overlap margin": large enough that (K0+1)^d exceeds twice the number of
box-dent cells of the two tiles -/
def K0 (d r : ℕ) : ℕ := 2 * (2 * d + 4 * r * (2 * Rmax r + 1) ^ d) + 3

/-- first tooth position value (all coordinates of the 0-th tooth equal this) -/
def V0 (d r : ℕ) : ℕ := K0 d r + 5 * Rmax r + 3

/-- spacing between consecutive tooth positions -/
def sep (r : ℕ) : ℕ := 4 * Rmax r + 2

/-- the box side length (any larger N also works) -/
def N0 (d r : ℕ) : ℕ := V0 d r + 2 * r * sep r + K0 d r + Rmax r + 6

/-- tooth positions are deep: coordinate value ≥ radius for every tooth -/
lemma V0_ge_toothRadius {d r : ℕ} (σ : Fin 2) (l : Fin r) :
    (toothRadius r σ l : ℤ) ≤ (V0 d r : ℤ) := by
  have h1 : toothRadius r σ l ≤ Rmax r := toothRadius_le_Rmax r σ l
  have h2 : Rmax r ≤ V0 d r := by
    dsimp [V0]
    omega
  exact_mod_cast (le_trans h1 h2)

/-- every shell cell has all coordinates in [−R,R] -/
lemma shell_coord_bounds {d R : ℕ} {s : V d} (hs : s ∈ shell d R) (i : Fin d) :
    -((R : ℤ)) ≤ s i ∧ s i ≤ (R : ℤ) := by
  exact abs_le.mp (shell_coord_le hs i)

/-- the translation of a shell by the tooth position: the dent (and bump) cells
of the (σ,l)-tooth -/
def toothDent {d : ℕ} (V0 sep : ℕ) (r : ℕ) (σ : Fin 2) (l : Fin r) : Set (V d) :=
  (fun x : V d => toothPos (d := d) V0 sep r σ l + x) '' shell d (toothRadius r σ l)

-- bound used below: a tooth coordinate plus its radius stays well below N0
lemma toothCoord_bound {d r : ℕ} (hr : 0 < r) (σ : Fin 2) (l : Fin r) :
    V0 d r + toothIdx r σ l * sep r + toothRadius r σ l < N0 d r := by
  have hR : toothRadius r σ l ≤ Rmax r := toothRadius_le_Rmax r σ l
  have hIdx : toothIdx r σ l ≤ 2 * r := by
    have hlt := toothIdx_lt hr σ l
    omega
  have hmul : toothIdx r σ l * sep r ≤ (2 * r) * sep r := Nat.mul_le_mul_right (sep r) hIdx
  dsimp [N0]
  omega

/-- dent cells of a tooth lie in the box (given at least one generator) -/
lemma toothDent_mem_box {d r : ℕ} (hr : 0 < r) (σ : Fin 2) (l : Fin r) (x : V d)
    (hx : x ∈ toothDent (d := d) (V0 d r) (sep r) r σ l) :
    x ∈ box d (N0 d r) := by
  rcases hx with ⟨s, hs, rfl⟩
  intro i
  let R : ℕ := toothRadius r σ l
  have hb : -((R : ℤ)) ≤ s i ∧ s i ≤ (R : ℤ) := by
    simpa [R] using (shell_coord_bounds hs i)
  constructor
  · have hV0 : (V0 d r : ℤ) ≤ (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) i := by
      simp [toothPos]
      have h0 : (0 : ℤ) ≤ (toothIdx r σ l * sep r : ℕ) := by exact_mod_cast (Nat.zero_le _)
      omega
    have hRle : (R : ℤ) ≤ (V0 d r : ℤ) := by
      simpa [R] using (V0_ge_toothRadius (d := d) (r := r) σ l)
    have h1 : (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) i ≥ -((R : ℤ)) := by omega
    have hc : (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) i + s i ≥ (0 : ℤ) := by omega
    simpa [Pi.add_apply] using hc
  · have hup : (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) i + s i ≤
        ((V0 d r + toothIdx r σ l * sep r + toothRadius r σ l : ℕ) : ℤ) := by
      simp [toothPos]
      have hb1 : s i ≤ (R : ℤ) := hb.2
      have hb2 : (R : ℤ) = (toothRadius r σ l : ℤ) := by simp [R]
      rw [hb2]
      have hs0 : (0 : ℤ) ≤ (toothIdx r σ l * sep r : ℕ) := by exact_mod_cast (Nat.zero_le _)
      omega
    have hsmall : ((V0 d r + toothIdx r σ l * sep r + toothRadius r σ l : ℕ) : ℤ) < (N0 d r : ℤ) := by
      exact_mod_cast (toothCoord_bound (d := d) (r := r) hr σ l)
    have hc : (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) i + s i < (N0 d r : ℤ) :=
      lt_of_le_of_lt hup hsmall
    simpa [Pi.add_apply] using hc

-- ----------------------------------------------------------------------
-- Basis-hole disjointness: extra tooth dent cells live far above the corner,
-- so they never coincide with (and are never dented out as) basis holes.
-- ----------------------------------------------------------------------

/-- the parameter K0 is at least 3 -/
lemma K0_pos (d r : ℕ) : 3 ≤ K0 d r := by
  dsimp [K0]
  omega

/-- tooth positions sit far above the maximum tooth radius -/
lemma V0_gt_Rmax_add_five (d r : ℕ) : Rmax r + 5 ≤ V0 d r := by
  dsimp [V0]
  have hK : 3 ≤ K0 d r := K0_pos d r
  omega

/-- the coordinate of a tooth dent cell lies within [v_i − R, v_i + R] -/
lemma toothDent_coord_bounds {d r : ℕ} (σ : Fin 2) (l : Fin r) (x : V d)
    (hx : x ∈ toothDent (d := d) (V0 d r) (sep r) r σ l) (i : Fin d) :
    (toothPos (d := d) (V0 d r) (sep r) r σ l) i - (toothRadius r σ l : ℤ) ≤ x i ∧
    x i ≤ (toothPos (d := d) (V0 d r) (sep r) r σ l) i + (toothRadius r σ l : ℤ) := by
  rcases hx with ⟨s, hs, rfl⟩
  let R : ℕ := toothRadius r σ l
  have hb : -((R : ℤ)) ≤ s i ∧ s i ≤ (R : ℤ) := by
    simpa [R] using (shell_coord_bounds hs i)
  constructor
  · dsimp
    omega
  · dsimp
    omega

/-- every coordinate of a tooth dent cell is at least 5 (well above the basis-hole
coordinate values 2 and 4) -/
lemma toothDent_coord_ge_five {d r : ℕ} (σ : Fin 2) (l : Fin r) (x : V d)
    (hx : x ∈ toothDent (d := d) (V0 d r) (sep r) r σ l) (i : Fin d) :
    (5 : ℤ) ≤ x i := by
  have hb := toothDent_coord_bounds σ l x hx i
  have hV5 : (5 : ℤ) ≤ (toothPos (d := d) (V0 d r) (sep r) r σ l) i - (toothRadius r σ l : ℤ) := by
    simp [toothPos]
    have hV : (toothRadius r σ l : ℤ) + 5 ≤ (V0 d r : ℤ) := by
      have h1 : Rmax r + 5 ≤ V0 d r := V0_gt_Rmax_add_five d r
      have hR : toothRadius r σ l ≤ Rmax r := toothRadius_le_Rmax r σ l
      have hnat : toothRadius r σ l + 5 ≤ V0 d r := by omega
      exact_mod_cast hnat
    have h0 : (0 : ℤ) ≤ (toothIdx r σ l * sep r : ℕ) := by exact_mod_cast (Nat.zero_le _)
    omega
  exact le_trans hV5 hb.1

/-- a tooth dent cell never coincides with a basis hole cell -/
lemma toothDent_ne_xhole {d r : ℕ} (σ : Fin 2) (l : Fin r) (j : Fin d) (x : V d)
    (hx : x ∈ toothDent (d := d) (V0 d r) (sep r) r σ l) : x ≠ xhole (d := d) j := by
  intro hxhole
  have h5 : (5 : ℤ) ≤ x j := toothDent_coord_ge_five σ l x hx j
  have hJ := congrFun hxhole j
  have hx2 : x j = (2 : ℤ) := by
    rw [xhole_self j] at hJ
    exact hJ
  omega

/-- a tooth dent cell is never one of the basis holes of the dented box -/
lemma toothDent_disjoint_basis {d r : ℕ} (σ : Fin 2) (l : Fin r) (x : V d)
    (hx : x ∈ toothDent (d := d) (V0 d r) (sep r) r σ l) : x ∉ (Dset d : Set (V d)) := by
  intro hD
  rcases Dset_mem.mp hD with ⟨j, hj⟩
  exact (toothDent_ne_xhole σ l j x hx) hj

-- ----------------------------------------------------------------------
-- Distinct-teeth disjointness: two different teeth occupy disjoint dent
-- regions (their position values differ by at least `sep` in every
-- coordinate, which exceeds the sum of the two shell radii).
-- ----------------------------------------------------------------------

/-- coordinate value of a tooth position -/
lemma toothPos_val {d : ℕ} {V0 sep : ℕ} (r : ℕ) (σ : Fin 2) (l : Fin r) (i : Fin d) :
    toothPos (d := d) V0 sep r σ l i = (V0 + toothIdx r σ l * sep : ℕ) := by
  rfl

/-- if one tooth index is smaller than another, the second position is at least
`sep` above the first, in every coordinate -/
lemma toothPos_ge_add_sep {d : ℕ} (i : Fin d) {V0 sep r : ℕ} {σ σ' : Fin 2} {l l' : Fin r}
    (h : toothIdx r σ l < toothIdx r σ' l') :
    toothPos (d := d) V0 sep r σ' l' i - toothPos (d := d) V0 sep r σ l i ≥ (sep : ℤ) := by
  let a : ℕ := toothIdx r σ l
  let b : ℕ := toothIdx r σ' l'
  have hlt : a < b := by simpa [a, b] using h
  have hba : b = a + (b - a) := (Nat.add_sub_of_le (le_of_lt hlt)).symm
  have hle : a * sep ≤ b * sep := by
    rw [hba, Nat.add_mul]
    omega
  have hleV : V0 + a * sep ≤ V0 + b * sep := by omega
  rw [toothPos_val r σ' l' i, toothPos_val r σ l i]
  change (↑(V0 + b * sep : ℕ) : ℤ) - (↑(V0 + a * sep : ℕ) : ℤ) ≥ (sep : ℤ)
  rw [← Int.ofNat_sub hleV]
  have hsum : V0 + b * sep = V0 + a * sep + (b - a) * sep := by
    rw [hba, Nat.add_mul, Nat.add_sub_cancel_left, ← Nat.add_assoc]
  have hd : (V0 + b * sep) - (V0 + a * sep) = (b - a) * sep := by
    rw [hsum, Nat.add_sub_cancel_left]
  rw [hd]
  have hc : 1 ≤ b - a := by omega
  have hmul : sep ≤ (b - a) * sep := by
    calc sep = 1 * sep := by simp
      _ ≤ (b - a) * sep := Nat.mul_le_mul_right sep hc
  exact_mod_cast hmul

/-- dent regions of two distinct teeth are disjoint -/
lemma toothDent_disjoint_of_ne {d r : ℕ} (σ σ' : Fin 2) (l l' : Fin r)
    (hne : (σ, l) ≠ (σ', l')) :
    Disjoint (toothDent (d := d) (V0 d r) (sep r) r σ l)
      (toothDent (d := d) (V0 d r) (sep r) r σ' l') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  by_cases hd : 0 < d
  · let i0 : Fin d := ⟨0, hd⟩
    have hxle : x i0 ≤ (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) i0 +
        (toothRadius r σ l : ℤ) := (toothDent_coord_bounds σ l x hx i0).2
    have hxge : (toothPos (d := d) (V0 d r) (sep r) r σ' l' : V d) i0 -
        (toothRadius r σ' l' : ℤ) ≤ x i0 := (toothDent_coord_bounds σ' l' x hx' i0).1
    have hxle' : x i0 ≤ (toothPos (d := d) (V0 d r) (sep r) r σ' l' : V d) i0 +
        (toothRadius r σ' l' : ℤ) := (toothDent_coord_bounds σ' l' x hx' i0).2
    have hxge' : (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) i0 -
        (toothRadius r σ l : ℤ) ≤ x i0 := (toothDent_coord_bounds σ l x hx i0).1
    have hRle : (toothRadius r σ l : ℤ) + (toothRadius r σ' l' : ℤ) + 2 ≤ (sep r : ℤ) := by
      have h1 : toothRadius r σ l ≤ Rmax r := toothRadius_le_Rmax r σ l
      have h2 : toothRadius r σ' l' ≤ Rmax r := toothRadius_le_Rmax r σ' l'
      have hn : toothRadius r σ l + toothRadius r σ' l' + 2 ≤ sep r := by
        dsimp [sep]
        omega
      exact_mod_cast hn
    by_cases hle : toothIdx r σ l < toothIdx r σ' l'
    · have hv : (toothPos (d := d) (V0 d r) (sep r) r σ' l' : V d) i0 -
          (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) i0 ≥ (sep r : ℤ) :=
          toothPos_ge_add_sep (d := d) i0 hle
      omega
    · have hgt : toothIdx r σ' l' < toothIdx r σ l := by
        have hIdx : toothIdx r σ l ≠ toothIdx r σ' l' := by
          intro hIdx
          apply hne
          rcases (toothIdx_inj σ σ' l l' hIdx) with ⟨hσ, hl⟩
          exact Prod.ext hσ hl
        omega
      have hv : (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) i0 -
          (toothPos (d := d) (V0 d r) (sep r) r σ' l' : V d) i0 ≥ (sep r : ℤ) :=
          toothPos_ge_add_sep (d := d) i0 hgt
      omega
  · have hd0 : d = 0 := by omega
    subst d
    rcases hx with ⟨s, hs, _⟩
    rcases hs.2 with ⟨i, _⟩
    exact (Nat.not_lt_zero i.val) i.isLt

-- ----------------------------------------------------------------------
-- Bounded-displacement free cell: when two dented-box translates are shifted
-- by a displacement whose every coordinate leaves an overlap range of length
-- at least K0+1, and the dent set is smaller than (K0+1)^d, the overlap
-- contains a cell that is not a dent of either translate (a "free cell").
-- ----------------------------------------------------------------------

/-- free cell for dented boxes at bounded displacement with large overlap ranges -/
lemma free_cell_of_cellLen {d N K0 : ℕ} (hN : 2 ≤ N) (hK0 : 1 ≤ K0)
    (D : Finset (V d)) (hbig : (2 : ℕ) * D.card < (K0 + 1) ^ d)
    (δ : V d) (hcell : ∀ i : Fin d, K0 + 1 ≤ RigidOverlap.cellLen d N δ i) :
    ∃ z : V d, z ∈ box d N ∧ z - δ ∈ box d N ∧ z ∉ (D : Set (V d)) ∧ z - δ ∉ (D : Set (V d)) := by
  classical
  have hδ : RigidOverlap.StrictBounded d N δ := by
    intro i
    have hci := hcell i
    have hc2 : 2 ≤ RigidOverlap.cellLen d N δ i := by omega
    have hna : Int.natAbs (δ i) ≤ N - 2 := by
      dsimp [RigidOverlap.cellLen] at hc2
      omega
    rw [← RigidOverlap.int_abs_eq_natAbs (δ i)]
    exact_mod_cast hna
  have hprod : (K0 + 1) ^ d ≤ ∏ i : Fin d, RigidOverlap.cellLen d N δ i := by
    calc
      (K0 + 1) ^ d = ∏ i : Fin d, (K0 + 1) := by
        rw [Finset.prod_const, Finset.card_univ]
        simp
      _ ≤ ∏ i : Fin d, RigidOverlap.cellLen d N δ i := by
        exact Finset.prod_le_prod (fun i hi => by omega) (fun i hi => hcell i)
  have hbig' : (2 : ℕ) * D.card < ∏ i : Fin d, RigidOverlap.cellLen d N δ i :=
    lt_of_lt_of_le hbig hprod
  rcases RigidOverlap.overlap_big_box_avoid hN δ hδ D hbig' with ⟨z, hz1, hz2, hzD, hzδD⟩
  refine ⟨z, ?_, ?_, hzD, hzδD⟩
  · intro i
    exact hz1 i
  · intro i
    exact hz2 i

-- ----------------------------------------------------------------------
-- Click-case exclusions, part 1: the covering-derived displacement bounds.
-- If a deep dent cell `c + a` (a = v + s, with every coordinate of `a` between
-- K0+3 and N-1-K0) is covered by a translate whose covering cell `t'` is a BODY
-- cell of the box, or a BASIS-BUMP cell `N·e_i + x_i`, then the displacement
-- `δ := w - c = a - t'` satisfies |δ_k| ≤ N-1-K0 in every coordinate.  This
-- makes `free_cell_of_cellLen` applicable with D = both tiles' box-dents, giving
-- a free cell in the overlap of the two translates (contradiction with tiling
-- disjointness).  (The extra-bump case is excluded separately by double-coverage
-- and `shell_translate_subset_imp`.)
-- ----------------------------------------------------------------------

/-- covering a deep cell by a body cell of the box keeps the displacement within
N-1-K0 in every coordinate -/
lemma body_cover_delta_bound {d N K0 : ℕ} {a δ t' : V d}
    (hmargin : ∀ k : Fin d, (K0 : ℤ) ≤ a k ∧ a k ≤ (N : ℤ) - 1 - (K0 : ℤ))
    (ht'box : ∀ k : Fin d, (0 : ℤ) ≤ t' k ∧ t' k < (N : ℤ))
    (hδ : δ = a - t') : ∀ k : Fin d, |δ k| ≤ (N : ℤ) - 1 - (K0 : ℤ) := by
  intro k
  have hk := congrFun hδ k
  simp [Pi.sub_apply] at hk
  rw [hk]
  apply abs_le.mpr
  constructor
  · have h1 : (0 : ℤ) ≤ t' k := (ht'box k).1
    have h2 : t' k ≤ (N : ℤ) - 1 := by
      have h3 : t' k < (N : ℤ) := (ht'box k).2
      omega
    have h3 : (K0 : ℤ) ≤ a k := (hmargin k).1
    omega
  · have h1 : (0 : ℤ) ≤ t' k := (ht'box k).1
    have h4 : a k ≤ (N : ℤ) - 1 - (K0 : ℤ) := (hmargin k).2
    omega

/-- covering a deep cell by a basis-bump cell `N·e_i + x_i` keeps the displacement
within N-1-K0 in every coordinate -/
lemma basis_bump_cover_delta_bound {d N K0 : ℕ} (hN : K0 + 2 ≤ N) {a δ : V d}
    (i : Fin d)
    (hmargin : ∀ k : Fin d, (K0 : ℤ) + 3 ≤ a k ∧ a k ≤ (N : ℤ) - 1 - (K0 : ℤ))
    (hδ : δ = a - ((N : ℤ) • eb d i + xhole (d := d) i)) :
    ∀ k : Fin d, |δ k| ≤ (N : ℤ) - 1 - (K0 : ℤ) := by
  intro k
  have hk := congrFun hδ k
  simp [Pi.sub_apply] at hk
  rw [hk]
  apply abs_le.mpr
  by_cases hik : k = i
  · subst i
    have hred : a k - ((N : ℤ) * eb d k k + xhole (d := d) k k) = a k - (N : ℤ) - 2 := by
      simp [eb_apply k, xhole_self k]
      ring
    rw [hred]
    constructor
    · have h3 : (K0 : ℤ) + 3 ≤ a k := (hmargin k).1
      omega
    · have h4 : a k ≤ (N : ℤ) - 1 - (K0 : ℤ) := (hmargin k).2
      omega
  · have hne : i ≠ k := fun h => hik h.symm
    have hred : a k - ((N : ℤ) * eb d i k + xhole (d := d) i k) = a k - (4 : ℤ) := by
      simp [eb_apply_ne hne, xhole_other hne]
    rw [hred]
    constructor
    · have h3 : (K0 : ℤ) + 3 ≤ a k := (hmargin k).1
      omega
    · have h4 : a k ≤ (N : ℤ) - 1 - (K0 : ℤ) := (hmargin k).2
      omega

-- ----------------------------------------------------------------------
-- The tiles T1,T2 (parameterised by the tile side σ : Fin 2) and their
-- membership characterisation (basis-body / basis-bump / extra-bump).
-- Tσ := (basisTile ∖ (union of the σ-extra dent shells)) ∪ (their bumps).
-- ----------------------------------------------------------------------

/-- the bump cells of the (σ,l)-extra tooth: N·w_l + (dent shell) -/
def toothBump {d r : ℕ} (w : Fin r → V d) (σ : Fin 2) (l : Fin r) : Set (V d) :=
  (fun x : V d => ((N0 d r : ℤ) • w l) + x) '' toothDent (d := d) (V0 d r) (sep r) r σ l

/-- Tσ: the basis tile with the σ-extra teeth moved by N·w_l -/
def toothTile {d r : ℕ} (w : Fin r → V d) (σ : Fin 2) : Set (V d) :=
  (basisTile d (N0 d r) \ (⋃ l : Fin r, toothDent (d := d) (V0 d r) (sep r) r σ l)) ∪
    (⋃ l : Fin r, toothBump (d := d) w σ l)

/-- cells of the basis tile are box-body cells or basis bumps -/
lemma basisTile_mem_body_or_bump {d N : ℕ} {x : V d} (hx : x ∈ basisTile d N) :
    (x ∈ box d N ∧ x ∉ (Dset d : Set (V d))) ∨
      ∃ i : Fin d, x = (N : ℤ) • eb d i + xhole (d := d) i := by
  unfold basisTile dentedTile at hx
  rw [Set.mem_union] at hx
  rcases hx with hx | hx
  · left
    rw [Set.mem_diff] at hx
    exact hx
  · right
    rw [Set.mem_image] at hx
    rcases hx with ⟨d0, hd0, hxeq⟩
    rcases Dset_mem.mp hd0 with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    calc
      x = d0 + (N : ℤ) • uBump d0 := hxeq.symm
      _ = xhole (d := d) i + (N : ℤ) • uBump (xhole (d := d) i) := by rw [hi]
      _ = (N : ℤ) • eb d i + xhole (d := d) i := by
        rw [uBump_eq i]
        abel

/-- membership in Tσ: a basis-tile cell not among the σ-extra dents, or an
extra-bump cell -/
lemma toothTile_mem_iff {d r : ℕ} (w : Fin r → V d) (σ : Fin 2) (x : V d) :
    x ∈ toothTile w σ ↔
      ((x ∈ basisTile d (N0 d r) ∧
          ∀ l : Fin r, x ∉ toothDent (d := d) (V0 d r) (sep r) r σ l) ∨
        ∃ l : Fin r, x ∈ toothBump (d := d) w σ l) := by
  unfold toothTile
  simp only [Set.mem_union, Set.mem_diff, Set.mem_iUnion]
  constructor
  · intro h
    rcases h with h | ⟨l, hl⟩
    · left
      exact ⟨h.1, by
        intro l hl'
        exact h.2 ⟨l, hl'⟩⟩
    · right
      exact ⟨l, hl⟩
  · intro h
    rcases h with h | ⟨l, hl⟩
    · left
      exact ⟨h.1, by
        rintro ⟨l, hl'⟩
        exact h.2 l hl'⟩
    · right
      exact ⟨l, hl⟩

/-- Tσ splits into basis-box cells, basis bumps, and extra bumps -/
lemma toothTile_mem_cases {d r : ℕ} (w : Fin r → V d) (σ : Fin 2) (x : V d)
    (hx : x ∈ toothTile w σ) :
    (x ∈ box d (N0 d r) ∧
      x ∉ (Dset d : Set (V d)) ∧
      ∀ l : Fin r, x ∉ toothDent (d := d) (V0 d r) (sep r) r σ l) ∨
    (∃ i : Fin d, x = (N0 d r : ℤ) • eb d i + xhole (d := d) i) ∨
    (∃ l : Fin r, x ∈ toothBump (d := d) w σ l) := by
  rcases (toothTile_mem_iff w σ x).mp hx with h | ⟨l, hl⟩
  · rcases h with ⟨hB, hnotX⟩
    rcases (basisTile_mem_body_or_bump hB) with hBody | ⟨i, hi⟩
    · left
      exact ⟨hBody.1, hBody.2, hnotX⟩
    · right
      left
      exact ⟨i, hi⟩
  · right
    right
    exact ⟨l, hl⟩

-- ----------------------------------------------------------------------
-- Free cells are body cells, and a free cell in the overlap makes the two
-- translates share a cell.  This is the geometric heart of every click-case
-- exclusion branch:  the covering translate w' + Tσ' and the original
-- translate c + Tσ are both forced to contain c+z.
--
-- Planned exclusion statement (needs the dent Finset D := Dset ∪ (σ-dents) ∪
-- (σ'-dents), |D| small, δ bounded by N−1−K0 in every coordinate):
--   if c+z is a dent cell of c+Tσ covered by w'+Tσ' via a body or basis-bump
--   cell, then body_cover_delta_bound / basis_bump_cover_delta_bound give the
--   δ-bound, free_cell_of_cellLen yields z avoiding all dents, hence z and z−δ
--   are body cells of the two tiles (box_cell_mem_toothTile) and c+z lies in
--   both translates (translate_overlap_cell) — contradicting translate
--   disjointness in the joint tiling.
-- ----------------------------------------------------------------------

/-- a box cell that is neither a basis hole nor one of the σ-extra dents is a
body cell of Tσ -/
lemma box_cell_mem_toothTile {d r : ℕ} (w : Fin r → V d) (σ : Fin 2) (x : V d)
    (hx1 : x ∈ box d (N0 d r)) (hx2 : x ∉ (Dset d : Set (V d)))
    (hx3 : ∀ l : Fin r, x ∉ toothDent (d := d) (V0 d r) (sep r) r σ l) :
    x ∈ toothTile w σ := by
  apply (toothTile_mem_iff w σ x).mpr
  left
  constructor
  · exact basisTile_body_mem (N := N0 d r) hx1 hx2
  · exact hx3

/-- if z is a cell of Tσ and z−δ a cell of Tσ', then c+z lies in both translates
`c + Tσ` and `(c+δ) + Tσ'` -/
lemma translate_overlap_cell {d r : ℕ} (w : Fin r → V d) (σ σ' : Fin 2)
    (c δ z : V d)
    (hz1 : z ∈ toothTile w σ) (hz2 : z - δ ∈ toothTile w σ') :
    c + z ∈ ({c} + toothTile w σ) ∧ c + z ∈ ({c + δ} + toothTile w σ') := by
  constructor
  · refine Set.mem_add.mpr ⟨c, by simp, z, hz1, ?_⟩
    simp
  · refine Set.mem_add.mpr ⟨c + δ, by simp, z - δ, hz2, ?_⟩
    apply funext
    intro i
    simp [Pi.add_apply, Pi.sub_apply]

/-- a translate-disjointness contradiction from a common body cell -/
lemma overlap_contradiction {d r : ℕ} (w : Fin r → V d) (σ σ' : Fin 2)
    (c δ z : V d)
    (hdisj : ({c} + toothTile w σ) ∩ ({c + δ} + toothTile w σ') = ∅)
    (hz1 : z ∈ toothTile w σ) (hz2 : z - δ ∈ toothTile w σ') : False := by
  have hov := translate_overlap_cell w σ σ' c δ z hz1 hz2
  have hm : c + z ∈ ({c} + toothTile w σ) ∩ ({c + δ} + toothTile w σ') := ⟨hov.1, hov.2⟩
  rw [hdisj] at hm
  simpa using hm

-- ----------------------------------------------------------------------
-- The dent Finset D (all box-dents of the two tiles: basis holes plus the
-- σ- and σ'-extra dent shells) and its finiteness infrastructure.
-- ----------------------------------------------------------------------

/-- shells are finite (cells lie in the box [-R,R]^d) -/
lemma shell_finite {d R : ℕ} : (shell d R).Finite := by
  classical
  let B : Set (V d) := {x : V d | ∀ i : Fin d, x i ∈ Set.Icc (-((R : ℤ))) ((R : ℤ))}
  have hB : B.Finite := by
    dsimp [B]
    exact Set.Finite.pi' (fun i : Fin d => Set.finite_Icc (-(R : ℤ)) ((R : ℤ)))
  have hsub : shell d R ⊆ B := by
    intro x hx i
    exact abs_le.mp (shell_coord_le hx i)
  exact hB.subset hsub

/-- dent shells of a tooth are finite -/
lemma toothDent_finite {d r : ℕ} (σ : Fin 2) (l : Fin r) :
    (toothDent (d := d) (V0 d r) (sep r) r σ l).Finite := by
  unfold toothDent
  exact (shell_finite (R := toothRadius r σ l)).image (fun s : V d =>
    toothPos (d := d) (V0 d r) (sep r) r σ l + s)

/-- the (σ,l)-dent shell as a Finset -/
noncomputable def toothDentFin {d r : ℕ} (σ : Fin 2) (l : Fin r) : Finset (V d) :=
  (toothDent_finite (d := d) σ l).toFinset

/-- membership in the dent-shell Finset is membership in the dent shell -/
lemma toothDentFin_mem {d r : ℕ} (σ : Fin 2) (l : Fin r) (x : V d) :
    x ∈ toothDentFin (d := d) σ l ↔
      x ∈ toothDent (d := d) (V0 d r) (sep r) r σ l := by
  classical
  rw [toothDentFin]
  exact Set.Finite.mem_toFinset (toothDent_finite (d := d) σ l)

/-- the Finset of all box-dents of Tσ and Tσ' (basis holes included) -/
noncomputable def boxDents {d r : ℕ} (σ σ' : Fin 2) : Finset (V d) := by
  classical
  exact (Dset d) ∪
    (Finset.biUnion (Finset.univ : Finset (Fin r)) (toothDentFin (d := d) σ)) ∪
    (Finset.biUnion (Finset.univ : Finset (Fin r)) (toothDentFin (d := d) σ'))

/-- dent cells of Tσ belong to boxDents -/
lemma mem_boxDents_of_toothDent {d r : ℕ} (σ σ' : Fin 2) (l : Fin r)
    (x : V d) (hx : x ∈ toothDent (d := d) (V0 d r) (sep r) r σ l) :
    x ∈ (boxDents (d := d) (r := r) σ σ' : Set (V d)) := by
  classical
  dsimp [boxDents]
  rw [Finset.mem_coe]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [Finset.mem_biUnion]
  refine ⟨l, Finset.mem_univ l, ?_⟩
  exact (toothDentFin_mem (d := d) σ l x).mpr hx

/-- basis holes belong to boxDents -/
lemma mem_boxDents_of_basis {d r : ℕ} (σ σ' : Fin 2) (j : Fin d) :
    xhole (d := d) j ∈ (boxDents (d := d) (r := r) σ σ' : Set (V d)) := by
  classical
  dsimp [boxDents]
  rw [Finset.mem_coe]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  dsimp [Dset]
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

-- ----------------------------------------------------------------------
-- Shell cardinality bound: a tooth dent shell has at most (2R+1)^d cells.
-- ----------------------------------------------------------------------

/-- shift a shell cell (coordinates in [-R,R]) into Fin d → Fin (2R+1) by adding R -/
def shellShift {d R : ℕ} (x : V d) (hx : x ∈ shell d R) : Fin d → Fin (2 * R + 1) :=
  fun i => ⟨(x i + (R : ℤ)).toNat, by
    have hb := abs_le.mp (shell_coord_le hx i)
    have h0 : (0 : ℤ) ≤ x i + (R : ℤ) := by omega
    apply (Int.toNat_lt h0).mpr
    rcases hb with ⟨hlo, hhi⟩
    have hlt : x i + (R : ℤ) < (2 * (R : ℤ) + 1 : ℤ) := by omega
    have hc : (↑(2 * R + 1 : ℕ) : ℤ) = (2 * (R : ℤ) + 1 : ℤ) := by
      norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    rw [hc]
    exact hlt⟩

/-- subtracting the tooth position sends a dent cell back into the shell -/
lemma toothDent_sub_pos_mem_shell {d r : ℕ} (σ : Fin 2) (l : Fin r) (x : V d)
    (hx : x ∈ toothDent (d := d) (V0 d r) (sep r) r σ l) :
    x - toothPos (d := d) (V0 d r) (sep r) r σ l ∈ shell d (toothRadius r σ l) := by
  rcases hx with ⟨s0, hs0, hEq⟩
  have hxveq : x - toothPos (d := d) (V0 d r) (sep r) r σ l = s0 := by
    apply funext
    intro i
    have h := congrFun hEq i
    simp [Pi.sub_apply] at h ⊢
    omega
  simpa [hxveq] using hs0

/-- a tooth's dent shell has at most (2·R+1)^d cells (R = toothRadius) -/
lemma toothDentFin_card_le {d r : ℕ} (σ : Fin 2) (l : Fin r) :
    (toothDentFin (d := d) σ l).card ≤ (2 * toothRadius r σ l + 1) ^ d := by
  classical
  let R : ℕ := toothRadius r σ l
  let s : Finset (V d) := toothDentFin (d := d) σ l
  let t : Finset (Fin d → Fin (2 * R + 1)) := Finset.univ
  have hcard_t : t.card = (2 * R + 1) ^ d := by
    dsimp [t]
    simp [Fintype.card_fun]
  let f : V d → Fin d → Fin (2 * R + 1) := fun x =>
    if hx : x ∈ s then
      shellShift (x - toothPos (d := d) (V0 d r) (sep r) r σ l)
        (by
          have hxS : x ∈ toothDent (d := d) (V0 d r) (sep r) r σ l :=
            (toothDentFin_mem (d := d) σ l x).mp hx
          simpa [R] using (toothDent_sub_pos_mem_shell (d := d) σ l x hxS))
    else fun _ => ⟨0, by omega⟩
  have hmaps : Set.MapsTo f ↑s ↑t := by
    intro x hx
    exact Finset.mem_univ (f x)
  have hinj : Set.InjOn f ↑s := by
    intro x hx y hy hf
    have hxF : x ∈ s := by simpa using hx
    have hyF : y ∈ s := by simpa using hy
    have hxS : x ∈ toothDent (d := d) (V0 d r) (sep r) r σ l :=
      (toothDentFin_mem (d := d) σ l x).mp hxF
    have hyS : y ∈ toothDent (d := d) (V0 d r) (sep r) r σ l :=
      (toothDentFin_mem (d := d) σ l y).mp hyF
    have hxsh : x - toothPos (d := d) (V0 d r) (sep r) r σ l ∈ shell d R := by
      simpa [R] using (toothDent_sub_pos_mem_shell (d := d) σ l x hxS)
    have hysh : y - toothPos (d := d) (V0 d r) (sep r) r σ l ∈ shell d R := by
      simpa [R] using (toothDent_sub_pos_mem_shell (d := d) σ l y hyS)
    have hfx : f x = shellShift (x - toothPos (d := d) (V0 d r) (sep r) r σ l) hxsh := by
      dsimp [f]
      rw [dif_pos hxF]
    have hfy : f y = shellShift (y - toothPos (d := d) (V0 d r) (sep r) r σ l) hysh := by
      dsimp [f]
      rw [dif_pos hyF]
    have hsh : shellShift (x - toothPos (d := d) (V0 d r) (sep r) r σ l) hxsh =
        shellShift (y - toothPos (d := d) (V0 d r) (sep r) r σ l) hysh := by
      rw [← hfx, ← hfy]
      exact hf
    apply funext
    intro i
    have hi := congrFun hsh i
    have hxI := abs_le.mp (shell_coord_le hxsh i)
    have hyI := abs_le.mp (shell_coord_le hysh i)
    have hx0 : (0 : ℤ) ≤ (x - toothPos (d := d) (V0 d r) (sep r) r σ l) i + (R : ℤ) := by omega
    have hy0 : (0 : ℤ) ≤ (y - toothPos (d := d) (V0 d r) (sep r) r σ l) i + (R : ℤ) := by omega
    have hxi : (x - toothPos (d := d) (V0 d r) (sep r) r σ l) i + (R : ℤ) =
        (((x - toothPos (d := d) (V0 d r) (sep r) r σ l) i + (R : ℤ)).toNat : ℤ) :=
      (Int.toNat_of_nonneg hx0).symm
    have hyi : (y - toothPos (d := d) (V0 d r) (sep r) r σ l) i + (R : ℤ) =
        (((y - toothPos (d := d) (V0 d r) (sep r) r σ l) i + (R : ℤ)).toNat : ℤ) :=
      (Int.toNat_of_nonneg hy0).symm
    have htoNat : ((x - toothPos (d := d) (V0 d r) (sep r) r σ l) i + (R : ℤ)).toNat =
        ((y - toothPos (d := d) (V0 d r) (sep r) r σ l) i + (R : ℤ)).toNat := by
      exact congrArg Fin.val hi
    have hxz : (x - toothPos (d := d) (V0 d r) (sep r) r σ l) i + (R : ℤ) =
        (y - toothPos (d := d) (V0 d r) (sep r) r σ l) i + (R : ℤ) := by
      rw [hxi, hyi]
      exact congrArg (fun z : ℕ => (z : ℤ)) htoNat
    simp [Pi.sub_apply] at hxz
    omega
  have hle : s.card ≤ t.card := Finset.card_le_card_of_injOn f hmaps hinj
  rw [hcard_t] at hle
  simpa [s, R, t] using hle

-- ----------------------------------------------------------------------
-- Link (i): cap the per-shell bound by (2·Rmax + 1)^d.
-- ----------------------------------------------------------------------

/-- a tooth's dent shell has at most (2·Rmax r + 1)^d cells -/
lemma toothDentFin_card_le_Rmax {d r : ℕ} (σ : Fin 2) (l : Fin r) :
    (toothDentFin (d := d) σ l).card ≤ (2 * Rmax r + 1) ^ d := by
  exact le_trans (toothDentFin_card_le σ l) (Nat.pow_le_pow_left (by
    have hR : toothRadius r σ l ≤ Rmax r := toothRadius_le_Rmax r σ l
    omega) d)

-- ----------------------------------------------------------------------
-- Links (ii)+(iii): the dent Finset of two tiles is small compared with
-- (K0+1)^d.  (ii) union bound via card_union_le and card_biUnion_le;
-- (iii) the arithmetic against the chosen K0.
-- ----------------------------------------------------------------------

/-- all box-dents of two tiles number at most d + 2r·(2Rmax+1)^d -/
lemma boxDents_card_le {d r : ℕ} (σ σ' : Fin 2) :
    (boxDents (d := d) (r := r) σ σ').card ≤
      d + 2 * r * (2 * Rmax r + 1) ^ d := by
  classical
  let Bσ : Finset (V d) := Finset.biUnion (Finset.univ : Finset (Fin r)) (toothDentFin (d := d) σ)
  let Bσ' : Finset (V d) := Finset.biUnion (Finset.univ : Finset (Fin r)) (toothDentFin (d := d) σ')
  let C : ℕ := (2 * Rmax r + 1) ^ d
  have hBσ : Bσ.card ≤ r * C := by
    dsimp [Bσ, C]
    calc
      (Finset.biUnion (Finset.univ : Finset (Fin r)) (toothDentFin (d := d) σ)).card
          ≤ ∑ a ∈ (Finset.univ : Finset (Fin r)), (toothDentFin (d := d) σ a).card :=
            Finset.card_biUnion_le
      _ ≤ ∑ a ∈ (Finset.univ : Finset (Fin r)), (2 * Rmax r + 1) ^ d := by
            exact Finset.sum_le_sum (fun a ha => toothDentFin_card_le_Rmax σ a)
      _ = r * (2 * Rmax r + 1) ^ d := by
            simp [Finset.sum_const, Finset.card_univ]
  have hBσ' : Bσ'.card ≤ r * C := by
    dsimp [Bσ', C]
    calc
      (Finset.biUnion (Finset.univ : Finset (Fin r)) (toothDentFin (d := d) σ')).card
          ≤ ∑ a ∈ (Finset.univ : Finset (Fin r)), (toothDentFin (d := d) σ' a).card :=
            Finset.card_biUnion_le
      _ ≤ ∑ a ∈ (Finset.univ : Finset (Fin r)), (2 * Rmax r + 1) ^ d := by
            exact Finset.sum_le_sum (fun a ha => toothDentFin_card_le_Rmax σ' a)
      _ = r * (2 * Rmax r + 1) ^ d := by
            simp [Finset.sum_const, Finset.card_univ]
  have hmain : (boxDents (d := d) (r := r) σ σ').card ≤ d + Bσ.card + Bσ'.card := by
    dsimp [boxDents, Bσ, Bσ']
    have hu1 := Finset.card_union_le (Dset d)
      (Finset.biUnion (Finset.univ : Finset (Fin r)) (toothDentFin (d := d) σ))
    have hu2 := Finset.card_union_le
      ((Dset d) ∪ (Finset.biUnion (Finset.univ : Finset (Fin r)) (toothDentFin (d := d) σ)))
      (Finset.biUnion (Finset.univ : Finset (Fin r)) (toothDentFin (d := d) σ'))
    have hD : (Dset d).card = d := Dset_card d
    omega
  calc
    (boxDents (d := d) (r := r) σ σ').card ≤ d + Bσ.card + Bσ'.card := hmain
    _ ≤ d + r * C + r * C := by omega
    _ = d + 2 * (r * C) := by ring
    _ = d + 2 * r * C := by ring
    _ = d + 2 * r * (2 * Rmax r + 1) ^ d := by rfl

/-- 2·|boxDents| < (K0+1)^d : the smallness bound that makes the free-cell
pigeonhole applicable -/
lemma boxDents_card_small {d r : ℕ} (hd : 0 < d) (σ σ' : Fin 2) :
    2 * (boxDents (d := d) (r := r) σ σ').card < (K0 d r + 1) ^ d := by
  classical
  have hle := boxDents_card_le (d := d) (r := r) σ σ'
  have hmid : 2 * (d + 2 * r * (2 * Rmax r + 1) ^ d) < K0 d r + 1 := by
    let Q : ℕ := r * (2 * Rmax r + 1) ^ d
    have hQ : r * (2 * Rmax r + 1) ^ d = Q := rfl
    have hK : K0 d r + 1 = 2 * (2 * d + 4 * Q) + 4 := by
      dsimp [K0]
      rw [mul_assoc, hQ]
    rw [hK]
    rw [mul_assoc, hQ]
    have hlt1 : 2 * (d + 2 * Q) ≤ 2 * (2 * d + 4 * Q) := by omega
    have hlt2 : 2 * (2 * d + 4 * Q) < 2 * (2 * d + 4 * Q) + 4 := by omega
    exact lt_of_le_of_lt hlt1 hlt2
  have h2 : 2 * (boxDents (d := d) (r := r) σ σ').card < K0 d r + 1 := by
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 hle) hmid
  have hK : K0 d r + 1 ≤ (K0 d r + 1) ^ d := by
    have hpow := pow_le_pow_right₀ (a := K0 d r + 1) (m := 1) (n := d)
      (by dsimp [K0]; omega) (by omega)
    simpa using hpow
  exact lt_of_lt_of_le h2 hK

-- ----------------------------------------------------------------------
-- Deep-margin band: every tooth dent cell lies at least K0+3 above the
-- bottom face and at most N0-1-K0 below the top face.  (hmargin for the
-- body-/basis-bump displacement bounds.)
-- ----------------------------------------------------------------------

/-- K0 + 3 ≤ V0 − Rmax : the teeth sit high enough that subtracting the radius
still leaves margin K0 + 3 -/
lemma K0_band_lower {d r : ℕ} (σ : Fin 2) (l : Fin r) :
    (K0 d r : ℤ) + 3 ≤ (V0 d r : ℤ) - (Rmax r : ℤ) := by
  dsimp [V0]
  norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  omega

/-- the deepest tooth position plus the radius stays at least K0+1 below N0 -/
lemma N0_band_upper {d r : ℕ} (hr : 0 < r) :
    V0 d r + (2 * r - 1) * sep r + Rmax r ≤ N0 d r - 1 - K0 d r := by
  have hIdxSep : (2 * r - 1) * sep r ≤ (2 * r) * sep r :=
    Nat.mul_le_mul_right (sep r) (by omega : 2 * r - 1 ≤ 2 * r)
  have h1 : V0 d r + (2 * r - 1) * sep r + Rmax r ≤ V0 d r + (2 * r) * sep r + Rmax r := by omega
  have h2 : V0 d r + (2 * r) * sep r + Rmax r + 5 ≤ N0 d r - 1 - K0 d r := by
    dsimp [N0]
    omega
  omega

/-- tooth dent cells lie in the deep margin band [K0+3, N0-1-K0]^d -/
lemma toothDent_coord_margin_band {d r : ℕ} (hr : 0 < r) (σ : Fin 2) (l : Fin r) (x : V d)
    (hx : x ∈ toothDent (d := d) (V0 d r) (sep r) r σ l) (k : Fin d) :
    (K0 d r : ℤ) + 3 ≤ x k ∧ x k ≤ (N0 d r : ℤ) - 1 - (K0 d r : ℤ) := by
  let R : ℕ := toothRadius r σ l
  have hb := toothDent_coord_bounds σ l x hx k
  have hRmax : (R : ℤ) ≤ (Rmax r : ℤ) := by
    exact_mod_cast (by simpa [R] using (toothRadius_le_Rmax r σ l))
  have hIdx : toothIdx r σ l ≤ 2 * r - 1 := by
    have hlt := toothIdx_lt hr σ l
    omega
  constructor
  · have hv : (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) k ≥ (V0 d r : ℤ) := by
      simp [toothPos]
      have h0 : (0 : ℤ) ≤ (toothIdx r σ l * sep r : ℕ) := by exact_mod_cast (Nat.zero_le _)
      omega
    have h1 : (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) k - (R : ℤ) ≤ x k := hb.1
    have hK : (K0 d r : ℤ) + 3 ≤ (V0 d r : ℤ) - (Rmax r : ℤ) := K0_band_lower σ l
    omega
  · have hvle : (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) k ≤
        (↑(V0 d r + toothIdx r σ l * sep r : ℕ) : ℤ) := by
      rw [toothPos_val r σ l k]
    have hmul : toothIdx r σ l * sep r ≤ (2 * r - 1) * sep r :=
      Nat.mul_le_mul_right (sep r) hIdx
    have hcast1 : (↑(V0 d r + toothIdx r σ l * sep r : ℕ) : ℤ) ≤
        (↑(V0 d r + (2 * r - 1) * sep r : ℕ) : ℤ) := by
      exact_mod_cast (by omega)
    have hcast2 : (↑(V0 d r + (2 * r - 1) * sep r + Rmax r : ℕ) : ℤ) ≤
        ((N0 d r - 1 - K0 d r : ℕ) : ℤ) := by
      exact_mod_cast (N0_band_upper hr)
    have h1 : x k ≤ (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) k + (R : ℤ) := hb.2
    have hmid : x k ≤ (↑(V0 d r + (2 * r - 1) * sep r + Rmax r : ℕ) : ℤ) := by
      have hpos : (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) k ≤
          (↑(V0 d r + (2 * r - 1) * sep r : ℕ) : ℤ) := by
        exact le_trans hvle hcast1
      omega
    have hKle : K0 d r + 1 ≤ N0 d r := by
      dsimp [N0]
      omega
    have hcastN : ((N0 d r - 1 - K0 d r : ℕ) : ℤ) = (N0 d r : ℤ) - 1 - (K0 d r : ℤ) := by
      have hs : N0 d r - 1 - K0 d r = N0 d r - (K0 d r + 1) := by omega
      rw [hs]
      rw [Int.ofNat_sub (by omega : K0 d r + 1 ≤ N0 d r)]
      have hc1 : (↑(K0 d r + 1) : ℤ) = (K0 d r : ℤ) + 1 := by norm_num [Nat.cast_add, Nat.cast_one]
      rw [hc1]
      omega
    rw [← hcastN]
    exact le_trans hmid hcast2

-- ----------------------------------------------------------------------
-- Port of g2.lean (slice 2): click exclusion, separation, matching, extra_click.
-- ----------------------------------------------------------------------

-- ----------------------------------------------------------------------
-- Two helpers for the click-case exclusion:
--   * δ-bounds imply the cellLen lower bound that free_cell_of_cellLen needs;
--   * dent cells of either tile sit in boxDents (both slots).
-- ----------------------------------------------------------------------

/-- |δ k| ≤ N-1-K0 implies cellLen ≥ K0+1 -/
lemma cellLen_of_delta_bound {d N K0 : ℕ} {δ : V d} (k : Fin d)
    (hδk : |δ k| ≤ (N : ℤ) - 1 - (K0 : ℤ)) :
    K0 + 1 ≤ RigidOverlap.cellLen d N δ k := by
  have hna : (Int.natAbs (δ k) : ℤ) ≤ (N : ℤ) - 1 - (K0 : ℤ) := by
    simpa [RigidOverlap.int_abs_eq_natAbs (δ k)] using hδk
  have hz : (K0 : ℤ) + 1 + (Int.natAbs (δ k) : ℤ) ≤ (N : ℤ) := by omega
  have hn : K0 + 1 + Int.natAbs (δ k) ≤ N := by exact_mod_cast hz
  dsimp [RigidOverlap.cellLen]
  omega

/-- dent cells of the σ'-tile also belong to boxDents σ σ' -/
lemma mem_boxDents_of_toothDent' {d r : ℕ} (σ σ' : Fin 2) (l : Fin r)
    (x : V d) (hx : x ∈ toothDent (d := d) (V0 d r) (sep r) r σ' l) :
    x ∈ (boxDents (d := d) (r := r) σ σ' : Set (V d)) := by
  classical
  dsimp [boxDents]
  rw [Finset.mem_coe]
  rw [Finset.mem_union]
  right
  rw [Finset.mem_biUnion]
  refine ⟨l, Finset.mem_univ l, ?_⟩
  exact (toothDentFin_mem (d := d) σ' l x).mpr hx

-- ----------------------------------------------------------------------
-- The click-case exclusion: a dent cell of a translate can never be covered
-- by a translate whose covering cell is a box body cell or a basis bump.
-- ----------------------------------------------------------------------

/-- shared contradiction: a δ bounded by N0-1-K0 in every coordinate gives a free
cell common to both translates, contradicting their disjointness -/
lemma exclusion_core {d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (wgen : Fin r → V d) (σ σ' : Fin 2)
    (c δ : V d)
    (hδb : ∀ k : Fin d, |δ k| ≤ (N0 d r : ℤ) - 1 - (K0 d r : ℤ))
    (hdisj : ({c} + toothTile wgen σ) ∩ ({c + δ} + toothTile wgen σ') = ∅) :
    False := by
  classical
  have hcell : ∀ k : Fin d, K0 d r + 1 ≤ RigidOverlap.cellLen d (N0 d r) δ k := by
    intro k
    exact cellLen_of_delta_bound (d := d) (N := N0 d r) (K0 := K0 d r) k (hδb k)
  have hK : 1 ≤ K0 d r := by
    have := K0_pos d r
    omega
  have hfree := free_cell_of_cellLen (d := d) (N := N0 d r) (K0 := K0 d r)
    (by dsimp [N0]; omega : 2 ≤ N0 d r)
    hK (boxDents (d := d) (r := r) σ σ')
    (boxDents_card_small (d := d) (r := r) hd σ σ') δ hcell
  rcases hfree with ⟨z0, hz0box, hz0δbox, hz0D, hz0δD⟩
  have hz0T : z0 ∈ toothTile wgen σ := by
    apply box_cell_mem_toothTile
    · exact hz0box
    · intro hzD
      rcases Dset_mem.mp hzD with ⟨j, hj⟩
      exact hz0D (by
        have hmem := mem_boxDents_of_basis (d := d) (r := r) σ σ' j
        simpa [hj] using hmem)
    · intro l0 hl0
      exact hz0D (by
        exact mem_boxDents_of_toothDent (d := d) (r := r) σ σ' l0 z0 hl0)
  have hz0δT : z0 - δ ∈ toothTile wgen σ' := by
    apply box_cell_mem_toothTile
    · exact hz0δbox
    · intro hzD
      rcases Dset_mem.mp hzD with ⟨j, hj⟩
      exact hz0δD (by
        have hmem := mem_boxDents_of_basis (d := d) (r := r) σ σ' j
        simpa [hj] using hmem)
    · intro l0 hl0
      exact hz0δD (by
        exact mem_boxDents_of_toothDent' (d := d) (r := r) σ σ' l0 (z0 - δ) hl0)
  exact overlap_contradiction wgen σ σ' c δ z0 hdisj hz0T hz0δT

/-- a body-cell covering of a deep dent cell is impossible -/
lemma click_body_excluded {d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (wgen : Fin r → V d) (σ σ' : Fin 2) (l : Fin r)
    (c z a δ t' : V d)
    (ha_dent : a ∈ toothDent (d := d) (V0 d r) (sep r) r σ l)
    (hδ : δ = a - t')
    (hw' : z - t' = c + δ)
    (ht'body : t' ∈ box d (N0 d r) ∧ t' ∉ (Dset d : Set (V d)) ∧
      ∀ l' : Fin r, t' ∉ toothDent (d := d) (V0 d r) (sep r) r σ' l')
    (hdisj : ({c} + toothTile wgen σ) ∩ ({z - t'} + toothTile wgen σ') = ∅) :
    False := by
  have hm : ∀ k : Fin d, (K0 d r : ℤ) ≤ a k ∧ a k ≤ (N0 d r : ℤ) - 1 - (K0 d r : ℤ) := by
    intro k
    have hb := toothDent_coord_margin_band (d := d) (r := r) hr σ l a ha_dent k
    constructor
    · exact le_trans (by omega : (K0 d r : ℤ) ≤ (K0 d r : ℤ) + 3) hb.1
    · exact hb.2
  have hδb : ∀ k : Fin d, |δ k| ≤ (N0 d r : ℤ) - 1 - (K0 d r : ℤ) :=
    body_cover_delta_bound (K0 := K0 d r) hm ht'body.1 hδ
  exact exclusion_core hd hr wgen σ σ' c δ hδb (by simpa [hw'] using hdisj)

/-- a basis-bump covering of a deep dent cell is impossible -/
lemma click_basis_excluded {d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (wgen : Fin r → V d) (σ σ' : Fin 2) (l : Fin r) (i : Fin d)
    (c z a δ t' : V d)
    (ha_dent : a ∈ toothDent (d := d) (V0 d r) (sep r) r σ l)
    (hδ : δ = a - t')
    (hw' : z - t' = c + δ)
    (ht'bump : t' = (N0 d r : ℤ) • eb d i + xhole (d := d) i)
    (hdisj : ({c} + toothTile wgen σ) ∩ ({z - t'} + toothTile wgen σ') = ∅) :
    False := by
  have hm : ∀ k : Fin d, (K0 d r : ℤ) + 3 ≤ a k ∧ a k ≤ (N0 d r : ℤ) - 1 - (K0 d r : ℤ) := by
    intro k
    exact toothDent_coord_margin_band (d := d) (r := r) hr σ l a ha_dent k
  have hN : K0 d r + 2 ≤ N0 d r := by dsimp [N0]; omega
  have hδ' : δ = a - ((N0 d r : ℤ) • eb d i + xhole (d := d) i) := by
    rw [ht'bump] at hδ
    exact hδ
  have hδb : ∀ k : Fin d, |δ k| ≤ (N0 d r : ℤ) - 1 - (K0 d r : ℤ) := by
    intro k
    have hd1 := basis_bump_cover_delta_bound (d := d) (N := N0 d r) (K0 := K0 d r) hN i hm hδ'
    exact hd1 k
  exact exclusion_core hd hr wgen σ σ' c δ hδb (by simpa [hw'] using hdisj)

-- ----------------------------------------------------------------------
-- Support lemmas for the extra-bump branch: bump cells of a translate live
-- in that translate, and (next) the shift of a dent cell by a bounded shell
-- difference stays inside the box region of the neighbouring translate.
-- ----------------------------------------------------------------------

/-- a bump-shell cell (shell cell shifted by N0·w_l' and the tooth position)
belongs to the corresponding extra bump of Tσ' -/
lemma bump_cell_mem_toothBump {d r : ℕ} (wgen : Fin r → V d) (σ' : Fin 2) (l' : Fin r)
    (s'''' : V d) (hs : s'''' ∈ shell d (toothRadius r σ' l')) :
    ((N0 d r : ℤ) • wgen l' + toothPos (d := d) (V0 d r) (sep r) r σ' l') + s''''
      ∈ toothBump (d := d) wgen σ' l' := by
  rw [toothBump]
  rw [Set.mem_image]
  refine ⟨toothPos (d := d) (V0 d r) (sep r) r σ' l' + s'''', ?_, ?_⟩
  · rw [toothDent]
    rw [Set.mem_image]
    exact ⟨s'''', hs, rfl⟩
  · abel

/-- that bump-shell cell lies inside the translate {w'} + Tσ' -/
lemma bump_cell_mem_translate {d r : ℕ} (wgen : Fin r → V d) (σ' : Fin 2) (l' : Fin r)
    (w' s'''' : V d) (hs : s'''' ∈ shell d (toothRadius r σ' l')) :
    w' + (((N0 d r : ℤ) • wgen l' + toothPos (d := d) (V0 d r) (sep r) r σ' l') + s'''')
      ∈ ({w'} + toothTile wgen σ') := by
  refine Set.mem_add.mpr ⟨w', by simp,
    ((N0 d r : ℤ) • wgen l' + toothPos (d := d) (V0 d r) (sep r) r σ' l') + s'''', ?_, rfl⟩
  apply (toothTile_mem_iff wgen σ'
    (((N0 d r : ℤ) • wgen l' + toothPos (d := d) (V0 d r) (sep r) r σ' l') + s'''')).mpr
  right
  exact ⟨l', bump_cell_mem_toothBump wgen σ' l' s'''' hs⟩

-- ----------------------------------------------------------------------
-- K0 is bigger than 4r+2: the margin slack needed for the band-shift lemma.
-- ----------------------------------------------------------------------

/-- K0 d r ≥ 4r + 2 -/
lemma K0_ge_four_r_add_two {d r : ℕ} : 4 * r + 2 ≤ K0 d r := by
  dsimp [K0]
  have hP : 1 ≤ (2 * Rmax r + 1) ^ d := by
    exact one_le_pow₀ (n := d) (by dsimp [Rmax]; omega)
  have h4 : 4 * r ≤ 4 * r * (2 * Rmax r + 1) ^ d := by
    exact Nat.le_mul_of_pos_right (4 * r) (by have := hP; omega)
  omega

-- ----------------------------------------------------------------------
-- Separation: a point within 3·Rmax of the (σ,l)-tooth position is never a
-- dent cell of another tooth (σ,l0), l0 ≠ l (positions are ≥ sep apart).
-- ----------------------------------------------------------------------

-- ----------------------------------------------------------------------
-- Separation: a point within 3·Rmax of the (σ,l)-tooth position is never a
-- dent cell of another tooth (σ,l0), l0 ≠ l (positions are ≥ sep apart).
-- ----------------------------------------------------------------------

-- ----------------------------------------------------------------------
-- Separation: a point within 3·Rmax of the (σ,l)-tooth position is never a
-- dent cell of another tooth (σ,l0), l0 ≠ l (positions are ≥ sep apart).
-- ----------------------------------------------------------------------

/-- a point within 3·Rmax of toothPos σ l avoids every other tooth's dent -/
lemma sep_away {d r : ℕ} (hd : 0 < d) (hr : 0 < r) (σ : Fin 2) {l l0 : Fin r}
    (hll : l ≠ l0) (x : V d)
    (hclose : ∀ k : Fin d, |x k - (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) k| ≤
      ((3 * Rmax r : ℕ) : ℤ)) :
    x ∉ toothDent (d := d) (V0 d r) (sep r) r σ l0 := by
  intro hx
  rcases hx with ⟨s0, hs0, hEq⟩
  let i0 : Fin d := ⟨0, hd⟩
  have h3c : ((3 * Rmax r : ℕ) : ℤ) = 3 * (Rmax r : ℤ) := by
    norm_num [Nat.cast_mul]
  have hsep4 : (sep r : ℤ) = 4 * (Rmax r : ℤ) + 2 := by
    dsimp [sep]
  have hR0 : (toothRadius r σ l0 : ℤ) ≤ (Rmax r : ℤ) := by
    exact_mod_cast (toothRadius_le_Rmax r σ l0)
  have hs0b := abs_le.mp (shell_coord_le hs0 i0)  -- −R0 ≤ s0 i0 ∧ s0 i0 ≤ R0
  have hEq_i0 : x i0 = (toothPos (d := d) (V0 d r) (sep r) r σ l0 : V d) i0 + s0 i0 := by
    have h := congrFun hEq i0
    simp [Pi.add_apply] at h ⊢
    exact h.symm
  have hIdx : toothIdx r σ l ≠ toothIdx r σ l0 := by
    intro hEqIdx
    apply hll
    exact (toothIdx_inj σ σ l l0 hEqIdx).2
  by_cases hle : toothIdx r σ l < toothIdx r σ l0
  · -- v0 ≥ v + sep ⇒ x ≤ v+3Rmax < v0−R0 ≤ x
    have hsep0 : (toothPos (d := d) (V0 d r) (sep r) r σ l0 : V d) i0 -
        (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) i0 ≥ (sep r : ℤ) :=
      toothPos_ge_add_sep (d := d) i0 hle
    rw [hsep4] at hsep0
    have htop : x i0 ≤ (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) i0 +
        3 * (Rmax r : ℤ) := by
      have hc := abs_le.mp (hclose i0)
      rw [h3c] at hc
      omega
    have hlow : (toothPos (d := d) (V0 d r) (sep r) r σ l0 : V d) i0 -
        (Rmax r : ℤ) ≤ x i0 := by
      rw [hEq_i0]
      omega
    omega
  · have hgt : toothIdx r σ l0 < toothIdx r σ l := by omega
    have hsep0 : (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) i0 -
        (toothPos (d := d) (V0 d r) (sep r) r σ l0 : V d) i0 ≥ (sep r : ℤ) :=
      toothPos_ge_add_sep (d := d) i0 hgt
    rw [hsep4] at hsep0
    have hlow2 : (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) i0 -
        3 * (Rmax r : ℤ) ≤ x i0 := by
      have hc := abs_le.mp (hclose i0)
      rw [h3c] at hc
      omega
    have htop2 : x i0 ≤ (toothPos (d := d) (V0 d r) (sep r) r σ l0 : V d) i0 +
        (Rmax r : ℤ) := by
      rw [hEq_i0]
      omega
    omega

-- ----------------------------------------------------------------------
-- Band-shift: r'' := a + (s'''' − s'), for a a dent cell of tooth (σ,l) and
-- s', s'''' shell cells of radius R' ≤ Rmax, stays in the box, avoids all
-- basis holes, and avoids every other tooth's dent cells.
-- ----------------------------------------------------------------------

-- ----------------------------------------------------------------------
-- Band-shift: r'' := a + (s'''' − s'), for a a dent cell of tooth (σ,l) and
-- s', s'''' shell cells of radius R' ≤ Rmax, stays in the box, avoids all
-- basis holes, and avoids every other tooth's dent cells.
-- ----------------------------------------------------------------------

/-- shifting a dent cell by a bounded shell difference keeps the result in the
box, out of the basis holes, and out of every other tooth's dent -/
lemma shift_band_props {d r : ℕ} (hd : 0 < d) (hr : 0 < r) (σ : Fin 2) (l : Fin r)
    (a s' s'''' : V d) (R' : ℕ)
    (ha_dent : a ∈ toothDent (d := d) (V0 d r) (sep r) r σ l)
    (hs' : s' ∈ shell d R') (hs'''' : s'''' ∈ shell d R') (hR' : R' ≤ Rmax r) :
    (∀ k : Fin d, (5 : ℤ) ≤ (a + (s'''' - s')) k ∧ (a + (s'''' - s')) k < (N0 d r : ℤ)) ∧
    (a + (s'''' - s')) ∉ (Dset d : Set (V d)) ∧
    (∀ l0 : Fin r, l0 ≠ l → (a + (s'''' - s')) ∉ toothDent (d := d) (V0 d r) (sep r) r σ l0) := by
  let y : V d := a + (s'''' - s')
  change (∀ k : Fin d, (5 : ℤ) ≤ y k ∧ y k < (N0 d r : ℤ)) ∧
    y ∉ (Dset d : Set (V d)) ∧
    (∀ l0 : Fin r, l0 ≠ l → y ∉ toothDent (d := d) (V0 d r) (sep r) r σ l0)
  have hK2' : (2 * (Rmax r : ℤ) + 2) ≤ (K0 d r : ℤ) := by
    have h := K0_ge_four_r_add_two (d := d) (r := r)
    dsimp [Rmax] at h ⊢
    omega
  have hRmax' : (R' : ℤ) ≤ (Rmax r : ℤ) := by exact_mod_cast hR'
  have hb : ∀ k : Fin d, (K0 d r : ℤ) + 3 ≤ a k ∧ a k ≤ (N0 d r : ℤ) - 1 - (K0 d r : ℤ) :=
    fun k => toothDent_coord_margin_band (d := d) (r := r) hr σ l a ha_dent k
  have hclose : ∀ k : Fin d, |y k - (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) k| ≤
      ((3 * Rmax r : ℕ) : ℤ) := by
    intro k
    rcases ha_dent with ⟨s, hs, hEq⟩
    have hsb := shell_coord_bounds (d := d) (R := toothRadius r σ l) hs k
    have hsb' := shell_coord_bounds (d := d) (R := R') hs' k
    have hs4 := shell_coord_bounds (d := d) (R := R') hs'''' k
    have hR : (toothRadius r σ l : ℤ) ≤ (Rmax r : ℤ) := by
      exact_mod_cast (toothRadius_le_Rmax r σ l)
    have hyk : y k - (toothPos (d := d) (V0 d r) (sep r) r σ l : V d) k = s k + s'''' k - s' k := by
      have h := congrFun hEq k
      dsimp [y]
      simp [Pi.add_apply] at h ⊢
      omega
    rw [hyk]
    apply abs_le.mpr
    constructor <;> omega
  have hcoord : ∀ k : Fin d, (5 : ℤ) ≤ y k ∧ y k < (N0 d r : ℤ) := by
    intro k
    have hb1 : (K0 d r : ℤ) + 3 ≤ a k := (hb k).1
    have hb2 : a k ≤ (N0 d r : ℤ) - 1 - (K0 d r : ℤ) := (hb k).2
    have hsb' := shell_coord_bounds (d := d) (R := R') hs' k
    have hs4 := shell_coord_bounds (d := d) (R := R') hs'''' k
    constructor
    · have hlow : (5 : ℤ) ≤ a k + s'''' k - s' k := by
        have h4 : (5 : ℤ) ≤ (K0 d r : ℤ) + 3 - 2 * (Rmax r : ℤ) := by omega
        omega
      dsimp [y]
      omega
    · have hup : a k + s'''' k - s' k < (N0 d r : ℤ) := by
        have h4 : (2 * (Rmax r : ℤ) + 2) ≤ (K0 d r : ℤ) := hK2'
        omega
      dsimp [y]
      omega
  have hnotBasis : y ∉ (Dset d : Set (V d)) := by
    intro hyD
    rcases Dset_mem.mp hyD with ⟨j, hj⟩
    have h5 : (5 : ℤ) ≤ y j := (hcoord j).1
    have hJ := congrFun hj j
    have h2 : y j = (2 : ℤ) := by
      rw [xhole_self j] at hJ
      exact hJ
    omega
  have hnotOther : ∀ l0 : Fin r, l0 ≠ l →
      y ∉ toothDent (d := d) (V0 d r) (sep r) r σ l0 := fun l0 hl0 =>
    sep_away (d := d) (r := r) hd hr σ (l := l) (l0 := l0) (by exact fun h => hl0 h.symm) y hclose
  exact ⟨hcoord, hnotBasis, hnotOther⟩

-- ----------------------------------------------------------------------
-- THE CLICK (extra-bump branch): a dent cell of tooth (σ,l) covered by the
-- extra bump of tooth (σ',l') forces σ'=σ, l'=l and displacement −N0·wgen l.
-- ----------------------------------------------------------------------

/-- extra-bump covering of a deep dent cell: double-coverage forces the matching
tooth and the click displacement -/
lemma click_extra_matching {d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (wgen : Fin r → V d) {σ σ' : Fin 2} {l l' : Fin r}
    {c z a δ t' w' : V d}
    (hz : z = c + a)
    (ha_dent : a ∈ toothDent (d := d) (V0 d r) (sep r) r σ l)
    (ht'extra : t' ∈ toothBump (d := d) wgen σ' l')
    (hδ : δ = a - t')
    (hw' : w' = z - t')
    (hdisj : ({c} + toothTile wgen σ) ∩ ({w'} + toothTile wgen σ') = ∅) :
    σ = σ' ∧ l = l' ∧ δ = -(N0 d r : ℤ) • wgen l := by
  classical
  let R : ℕ := toothRadius r σ l
  let R' : ℕ := toothRadius r σ' l'
  have hmem : ∃ s0 : V d, s0 ∈ shell d (toothRadius r σ l) ∧
      (fun x0 : V d => toothPos (d := d) (V0 d r) (sep r) r σ l + x0) s0 = a := by
    rw [toothDent, Set.mem_image] at ha_dent
    simpa using ha_dent
  rcases hmem with ⟨s, hs, hEq_a⟩
  rcases ht'extra with ⟨y, hyT, hEq_t'1⟩
  rcases hyT with ⟨s', hs', hEq_y⟩
  have hyv : y = toothPos (d := d) (V0 d r) (sep r) r σ' l' + s' := by
    exact hEq_y.symm
  have ht'eq : t' = (N0 d r : ℤ) • wgen l' + (toothPos (d := d) (V0 d r) (sep r) r σ' l' + s') := by
    calc
      t' = (N0 d r : ℤ) • wgen l' + y := hEq_t'1.symm
      _ = (N0 d r : ℤ) • wgen l' + (toothPos (d := d) (V0 d r) (sep r) r σ' l' + s') := by rw [hyv]
  have hmain : ∀ s'''' : V d, s'''' ∈ shell d R' → s + s'''' - s' ∈ shell d R := by
    intro s'''' hs''''
    by_cases hown : a + (s'''' - s') ∈ toothDent (d := d) (V0 d r) (sep r) r σ l
    · rcases hown with ⟨u, hu, hEq_u⟩
      have huu : s + s'''' - s' = u := by
        apply funext
        intro i
        have h1 := congrFun hEq_a i
        have h2 := congrFun hEq_u i
        simp [Pi.add_apply, Pi.sub_apply] at h1 h2 ⊢
        omega
      simpa [huu] using hu
    · exfalso
      let y'' : V d := a + (s'''' - s')
      let z'' : V d := w' + (((N0 d r : ℤ) • wgen l' + toothPos (d := d) (V0 d r) (sep r) r σ' l') + s'''')
      have hshift := shift_band_props (d := d) (r := r) hd hr σ l a s' s'''' R'
        ha_dent hs' hs'''' (by simpa [R'] using (toothRadius_le_Rmax r σ' l'))
      have hy''box : y'' ∈ box d (N0 d r) := by
        intro k
        constructor
        · have h5' : (5 : ℤ) ≤ y'' k := by simpa [y''] using (hshift.1 k).1
          omega
        · simpa [y''] using (hshift.1 k).2
      have hy''T : y'' ∈ toothTile wgen σ := by
        apply box_cell_mem_toothTile
        · exact hy''box
        · simpa [y''] using hshift.2.1
        · intro l0 hl0
          by_cases hle : l0 = l
          · subst l0
            exact hown (by simpa [y''] using hl0)
          · exact (hshift.2.2 l0 hle) (by simpa [y''] using hl0)
      have hz''T' : z'' ∈ ({w'} + toothTile wgen σ') := by
        dsimp [z'']
        exact bump_cell_mem_translate (d := d) wgen σ' l' w' s'''' hs''''
      have hz''eq : z'' = z + (s'''' - s') := by
        dsimp [z'']
        rw [hw', ht'eq]
        abel
      have hEqc : c + y'' = z + (s'''' - s') := by
        dsimp [y'']
        rw [hz]
        abel
      have hEqz'' : c + y'' = z'' := by
        exact hEqc.trans hz''eq.symm
      have hm1 : c + y'' ∈ ({c} + toothTile wgen σ) := by
        refine Set.mem_add.mpr ⟨c, by simp, y'', hy''T, ?_⟩
        simp
      have hm2 : c + y'' ∈ ({w'} + toothTile wgen σ') := by
        rw [hEqz'']
        exact hz''T'
      have hm : c + y'' ∈ ({c} + toothTile wgen σ) ∩ ({w'} + toothTile wgen σ') := ⟨hm1, hm2⟩
      rw [hdisj] at hm
      simpa using hm
  have hres : R' = R ∧ s' = s := by
    have hinc : ∀ x : V d, x ∈ shell d R' → x ∈
        (fun x0 : V d => -(s - s') + x0) '' shell d R := by
      intro x hx
      rw [Set.mem_image]
      refine ⟨s + x - s', ?_, ?_⟩
      · exact hmain x hx
      · abel
    have hlemma := shell_subset_translate_imp (d := d) (R := R') (R' := R) hd
      (toothRadius_pos r σ' l') (-(s - s')) hinc
    rcases hlemma with ⟨hRR, hneg⟩
    constructor
    · exact hRR
    · apply funext
      intro i
      have hi := congrFun hneg i
      simp at hi
      omega
  rcases hres with ⟨hRR, hs's⟩
  have hσ : σ = σ' := (toothRadius_inj σ' σ l' l (by simpa [R', R] using hRR)).1.symm
  have hl : l = l' := (toothRadius_inj σ' σ l' l (by simpa [R', R] using hRR)).2.symm
  have hδeq : δ = -(N0 d r : ℤ) • wgen l := by
    have ha' : a = toothPos (d := d) (V0 d r) (sep r) r σ l + s := by
      apply funext
      intro j
      have h := congrFun hEq_a j
      simp [Pi.add_apply] at h ⊢
      exact h.symm
    have ht'' : t' = (N0 d r : ℤ) • wgen l + (toothPos (d := d) (V0 d r) (sep r) r σ l + s) := by
      have h1 := ht'eq
      rw [hσ.symm, hl.symm, hs's] at h1
      exact h1
    apply funext
    intro j
    have h1 := congrFun hδ j
    have h2 := congrFun ha' j
    have h3 := congrFun ht'' j
    simp [Pi.sub_apply, Pi.add_apply, Pi.smul_apply] at h1 h2 h3 ⊢
    omega
  exact ⟨hσ, hl, hδeq⟩

-- ----------------------------------------------------------------------
-- THE GEOMETRIC CLICK: covering a dent cell of tooth (σ,l) of a translate in
-- part σ forces the centre c − N0·wgen l into part σ.
-- ----------------------------------------------------------------------

/-- in a joint tiling (parts `part 0`, `part 1` with tiles toothTile wgen σ),
covering the dent cell c+a (a a dent of tooth (σ,l)) forces c − N0·wgen l
into the same part -/
lemma extra_click {d r : ℕ} (hd : 0 < d) (hr : 0 < r) (wgen : Fin r → V d)
    (part : Fin 2 → Set (V d)) {σ : Fin 2} {l : Fin r}
    (c w' a t' z : V d) {σ' : Fin 2}
    (hc : c ∈ part σ)
    (hz : z = c + a) (ha_dent : a ∈ toothDent (d := d) (V0 d r) (sep r) r σ l)
    (hcov : z = w' + t') (ht' : t' ∈ toothTile wgen σ')
    (hdisj : ({c} + toothTile wgen σ) ∩ ({w'} + toothTile wgen σ') = ∅)
    (hpart' : w' ∈ part σ') :
    c - (N0 d r : ℤ) • wgen l ∈ part σ := by
  let δ : V d := a - t'
  have hδrfl : δ = a - t' := rfl
  have hw'eq : z - t' = w' := by
    rw [hcov]
    abel
  have hdisj' : ({c} + toothTile wgen σ) ∩ ({z - t'} + toothTile wgen σ') = ∅ := by
    rw [hw'eq]
    exact hdisj
  have hw'cδ : z - t' = c + δ := by
    dsimp [δ]
    rw [hz]
    abel
  rcases (toothTile_mem_cases wgen σ' t' ht') with hbody | hbump
  · exfalso
    exact click_body_excluded (d := d) (r := r) hd hr wgen σ σ' l
      c z a δ t' ha_dent hδrfl hw'cδ hbody hdisj'
  · rcases hbump with hbump | hbump
    · exfalso
      rcases hbump with ⟨i, hi⟩
      exact click_basis_excluded (d := d) (r := r) hd hr wgen σ σ' l i
        c z a δ t' ha_dent hδrfl hw'cδ hi hdisj'
    · rcases hbump with ⟨l', ht'extra⟩
      have hres := click_extra_matching (d := d) (r := r) hd hr wgen (σ := σ) (σ' := σ')
        (l := l) (l' := l') hz ha_dent ht'extra hδrfl hw'eq.symm hdisj
      rcases hres with ⟨hσ, hl, hδeq⟩
      -- w' = z − t' = c + a − t' = c + δ ; δ = −N0•wgen l
      have h1 : w' = c + δ := by
        have h2 : w' = c + a - t' := by
          rw [← hw'eq]
          rw [hz]
        calc
          w' = c + a - t' := h2
          _ = c + (a - t') := by abel
          _ = c + δ := by rw [hδrfl]
      have hw'' : w' = c - (N0 d r : ℤ) • wgen l := by
        apply funext
        intro j
        have h1j := congrFun h1 j
        have h2j := congrFun hδeq j
        simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at h1j h2j ⊢
        omega
      rw [← hw'']
      -- σ' = σ: part σ' = part σ
      have hpart'' : w' ∈ part σ := by
        rw [hσ.symm] at hpart'
        exact hpart'
      exact hpart''

-- ----------------------------------------------------------------------
-- Port of meta1.lean (abstract pair layer): joint map, add_eq_of_periodic.
-- (V/NV/NL already exist here with the same meanings; jointSum is new.)
-- ----------------------------------------------------------------------

-- the joint sum map used in the target statement
def jointSum {d : ℕ} (C₁ C₂ T₁ T₂ : Set (V d)) :
    (Sum {p : (V d) × (V d) | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
         {p : (V d) × (V d) | p.1 ∈ C₂ ∧ p.2 ∈ T₂}) → V d
  | Sum.inl p => p.1.1 + p.1.2
  | Sum.inr p => p.1.1 + p.1.2

/-- If `T_j + S = T + S` and `C + S = C` then `C + T_j = C + T`. -/
lemma add_eq_of_eq_add_add {G : Type*} [AddCommGroup G] {S : Set G} {T Tj C : Set G}
    (h0S : (0 : G) ∈ S) (hTjS : Tj + S = T + S) (hCS : C + S = C) : C + Tj = C + T := by
  apply le_antisymm
  · intro x hx
    rcases Set.mem_add.mp hx with ⟨c, hc, tj, htj, rfl⟩
    have htjS : tj ∈ Tj + S := Set.mem_add.mpr ⟨tj, htj, 0, h0S, by simp⟩
    rw [hTjS] at htjS
    rcases Set.mem_add.mp htjS with ⟨t, ht, s, hs, htjs⟩
    refine Set.mem_add.mpr ⟨c + s, ?_, t, ht, ?_⟩
    · have hcS : c + s ∈ C + S := Set.mem_add.mpr ⟨c, hc, s, hs, rfl⟩
      rwa [hCS] at hcS
    · rw [← htjs]
      abel
  · intro x hx
    rcases Set.mem_add.mp hx with ⟨c, hc, t, ht, rfl⟩
    have htS : t ∈ T + S := Set.mem_add.mpr ⟨t, ht, 0, h0S, by simp⟩
    rw [← hTjS] at htS
    rcases Set.mem_add.mp htS with ⟨tj, htj, s, hs, htjs⟩
    refine Set.mem_add.mpr ⟨c + s, ?_, tj, htj, ?_⟩
    · have hcS : c + s ∈ C + S := Set.mem_add.mpr ⟨c, hc, s, hs, rfl⟩
      rwa [hCS] at hcS
    · rw [add_assoc, add_comm s tj, htjs]

lemma zero_mem_NL {d : ℕ} (N : ℕ) (L : AddSubgroup (V d)) : (0 : V d) ∈ NL d N L := by
  rw [NL, mem_zimg]
  exact ⟨0, zero_mem L, by simp⟩

/-- `C_j + NL = C_j` and `T_j + NL = T + NL` gives `C_j + T_j = C_j + T`. -/
lemma add_eq_of_periodic {d : ℕ} (N : ℕ) (L : AddSubgroup (V d)) {T Tj C : Set (V d)}
    (hTjS : Tj + NL d N L = T + NL d N L) (hCS : C + NL d N L = C) :
    C + Tj = C + T := by
  exact add_eq_of_eq_add_add (zero_mem_NL N L) hTjS hCS

/-- the image of the joint map is the union of the two set sums -/
lemma jointSum_image {d : ℕ} {C₁ C₂ T₁ T₂ : Set (V d)} :
    Set.range (jointSum (d := d) C₁ C₂ T₁ T₂) = (C₁ + T₁) ∪ (C₂ + T₂) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    cases z with
    | inl p =>
        left
        exact Set.mem_add.mpr ⟨p.1.1, p.2.1, p.1.2, p.2.2, rfl⟩
    | inr p =>
        right
        exact Set.mem_add.mpr ⟨p.1.1, p.2.1, p.1.2, p.2.2, rfl⟩
  · intro hx
    rcases hx with hx | hx
    · rcases Set.mem_add.mp hx with ⟨c, hc, t, ht, rfl⟩
      refine ⟨Sum.inl ⟨(c, t), ⟨hc, ht⟩⟩, rfl⟩
    · rcases Set.mem_add.mp hx with ⟨c, hc, t, ht, rfl⟩
      refine ⟨Sum.inr ⟨(c, t), ⟨hc, ht⟩⟩, rfl⟩

/-- joint surjectivity is coverage of the two set sums -/
lemma jointSum_surjective_iff {d : ℕ} {C₁ C₂ T₁ T₂ : Set (V d)} :
    Function.Surjective (jointSum (d := d) C₁ C₂ T₁ T₂) ↔
      (C₁ + T₁) ∪ (C₂ + T₂) = Set.univ := by
  constructor
  · intro h
    rw [← jointSum_image]
    exact Function.Surjective.range_eq h
  · intro h x
    have hx : x ∈ (C₁ + T₁) ∪ (C₂ + T₂) := by rw [h]; trivial
    rcases hx with hx | hx
    · rcases Set.mem_add.mp hx with ⟨c, hc, t, ht, rfl⟩
      refine ⟨Sum.inl ⟨(c, t), ⟨hc, ht⟩⟩, rfl⟩
    · rcases Set.mem_add.mp hx with ⟨c, hc, t, ht, rfl⟩
      refine ⟨Sum.inr ⟨(c, t), ⟨hc, ht⟩⟩, rfl⟩



lemma zero_mem_NV {d N : ℕ} : (0 : V d) ∈ NV d N := by
  rw [NV, mem_zimg]
  exact ⟨0, by simp, by simp⟩

lemma NL_subset_NV {d : ℕ} (N : ℕ) (L : AddSubgroup (V d)) : NL d N L ⊆ NV d N := by
  intro x hx
  change x ∈ zimg N (L : Set (V d)) at hx
  rw [mem_zimg] at hx
  change x ∈ zimg N Set.univ
  rw [mem_zimg]
  rcases hx with ⟨a, ha, rfl⟩
  exact ⟨a, by simp, rfl⟩
lemma IsComplement_add_left_unique {G : Type*} [AddCommGroup G] {S T : Set G}
    (h : AddSubgroup.IsComplement S T) {c₁ c₂ t₁ t₂ : G}
    (hc₁ : c₁ ∈ S) (hc₂ : c₂ ∈ S) (ht₁ : t₁ ∈ T) (ht₂ : t₂ ∈ T)
    (hsum : c₁ + t₁ = c₂ + t₂) : c₁ = c₂ ∧ t₁ = t₂ := by
  classical
  have hu := h.existsUnique (c₁ + t₁)
  rcases hu with ⟨y, hy, hyu⟩
  let y₁ : S × T := (⟨c₁, hc₁⟩, ⟨t₁, ht₁⟩)
  let y₂ : S × T := (⟨c₂, hc₂⟩, ⟨t₂, ht₂⟩)
  have hy₁ : (y₁.1 : G) + (y₁.2 : G) = c₁ + t₁ := rfl
  have hy₂ : (y₂.1 : G) + (y₂.2 : G) = c₂ + t₂ := by
    change (c₂ : G) + (t₂ : G) = c₂ + t₂
    rfl
  have h₁ : y₁ = y := hyu y₁ hy₁
  have h₂ : y₂ = y := hyu y₂ (by simpa [hy₂, hsum] using hy₂)
  have h₃ : y₁ = y₂ := by rw [h₁, ← h₂]
  constructor
  · have hc : (y₁.1 : G) = (y₂.1 : G) := by
      have := congrArg (fun z : S × T => (z.1 : G)) h₃
      simpa using this
    simpa [y₁, y₂] using hc
  · have ht : (y₁.2 : G) = (y₂.2 : G) := by
      have := congrArg (fun z : S × T => (z.2 : G)) h₃
      simpa using this
    simpa [y₁, y₂] using ht

lemma jointSum_inl_of {d : ℕ} {C₁ C₂ T₁ T₂ : Set (V d)} {c t : V d}
    (hc : c ∈ C₁) (ht : t ∈ T₁) :
    jointSum (d := d) C₁ C₂ T₁ T₂ (Sum.inl ⟨(c, t), ⟨hc, ht⟩⟩) = c + t := rfl

lemma jointSum_inr_of {d : ℕ} {C₁ C₂ T₁ T₂ : Set (V d)} {c t : V d}
    (hc : c ∈ C₂) (ht : t ∈ T₂) :
    jointSum (d := d) C₁ C₂ T₁ T₂ (Sum.inr ⟨(c, t), ⟨hc, ht⟩⟩) = c + t := rfl

lemma jointSum_disjoint_centers {d : ℕ} {C₁ C₂ T₁ T₂ : Set (V d)}
    (h : Function.Bijective (jointSum (d := d) C₁ C₂ T₁ T₂))
    (h01 : (0 : V d) ∈ T₁) (h02 : (0 : V d) ∈ T₂) : Disjoint C₁ C₂ := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  let a : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
             {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
    Sum.inl ⟨(x, 0), ⟨hx1, h01⟩⟩
  let b : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
             {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
    Sum.inr ⟨(x, 0), ⟨hx2, h02⟩⟩
  have ha : jointSum (d := d) C₁ C₂ T₁ T₂ a = x := by
    dsimp [a, jointSum]
    simp
  have hb : jointSum (d := d) C₁ C₂ T₁ T₂ b = x := by
    dsimp [b, jointSum]
    simp
  have hEq : a = b := h.injective (by rw [ha, hb])
  cases a <;> cases b <;> contradiction

lemma jointSum_injective_of_complements {d N : ℕ} (L : AddSubgroup (V d))
    {T T₁ T₂ C₁ C₂ : Set (V d)}
    (hNV : AddSubgroup.IsComplement (NV d N) T)
    (hNVT1 : AddSubgroup.IsComplement (NV d N) T₁)
    (hNVT2 : AddSubgroup.IsComplement (NV d N) T₂)
    (hT1 : T₁ + NL d N L = T + NL d N L)
    (hT2 : T₂ + NL d N L = T + NL d N L)
    (hUn : C₁ ∪ C₂ = NV d N) (hDisj : Disjoint C₁ C₂)
    (hC1 : C₁ + NL d N L = C₁) (hC2 : C₂ + NL d N L = C₂) :
    Function.Injective (jointSum (d := d) C₁ C₂ T₁ T₂) := by
  have hC1sub : C₁ ⊆ NV d N := by
    intro y hy
    rw [← hUn]
    exact Or.inl hy
  have hC2sub : C₂ ⊆ NV d N := by
    intro y hy
    rw [← hUn]
    exact Or.inr hy
  intro a b hab
  cases a with
  | inl pa =>
      cases b with
      | inl pb =>
          have hsum : (pa : V d × V d).1 + (pa : V d × V d).2 =
              (pb : V d × V d).1 + (pb : V d × V d).2 := by
            simpa [jointSum] using hab
          have hpair := IsComplement_add_left_unique hNVT1 (hC1sub pa.2.1) (hC1sub pb.2.1)
            pa.2.2 pb.2.2 hsum
          apply congrArg Sum.inl
          apply Subtype.ext
          apply Prod.ext
          · simpa using hpair.1
          · simpa using hpair.2
      | inr pb =>
          exfalso
          let x : V d := pa.1.1 + pa.1.2
          have hx1 : x ∈ C₁ + T₁ := Set.mem_add.mpr ⟨pa.1.1, pa.2.1, pa.1.2, pa.2.2, rfl⟩
          have hx2 : x ∈ C₂ + T₂ := by
            exact Set.mem_add.mpr ⟨pb.1.1, pb.2.1, pb.1.2, pb.2.2,
              (by simpa [x, jointSum] using hab.symm)⟩
          have hx1' : x ∈ C₁ + T := by
            rw [add_eq_of_periodic (N := N) L hT1 hC1] at hx1
            exact hx1
          have hx2' : x ∈ C₂ + T := by
            rw [add_eq_of_periodic (N := N) L hT2 hC2] at hx2
            exact hx2
          rcases Set.mem_add.mp hx1' with ⟨c1', hc1', t', ht', hsum1'⟩
          rcases Set.mem_add.mp hx2' with ⟨c2', hc2', t'', ht'', hsum2'⟩
          have hcEq := (IsComplement_add_left_unique hNV (hC1sub hc1') (hC2sub hc2')
            ht' ht'' (by rw [hsum1', hsum2'])).1
          have hc1'C2 : c1' ∈ C₂ := by simpa [hcEq] using hc2'
          exact (Set.disjoint_left.mp hDisj hc1') hc1'C2
  | inr pa =>
      cases b with
      | inl pb =>
          exfalso
          let x : V d := pa.1.1 + pa.1.2
          have hx2 : x ∈ C₂ + T₂ := Set.mem_add.mpr ⟨pa.1.1, pa.2.1, pa.1.2, pa.2.2, rfl⟩
          have hx1 : x ∈ C₁ + T₁ := by
            exact Set.mem_add.mpr ⟨pb.1.1, pb.2.1, pb.1.2, pb.2.2,
              (by simpa [x, jointSum] using hab.symm)⟩
          have hx2' : x ∈ C₂ + T := by
            rw [add_eq_of_periodic (N := N) L hT2 hC2] at hx2
            exact hx2
          have hx1' : x ∈ C₁ + T := by
            rw [add_eq_of_periodic (N := N) L hT1 hC1] at hx1
            exact hx1
          rcases Set.mem_add.mp hx1' with ⟨c1', hc1', t', ht', hsum1'⟩
          rcases Set.mem_add.mp hx2' with ⟨c2', hc2', t'', ht'', hsum2'⟩
          have hcEq := (IsComplement_add_left_unique hNV (hC1sub hc1') (hC2sub hc2')
            ht' ht'' (by rw [hsum1', hsum2'])).1
          have hc2'C1 : c2' ∈ C₁ := by simpa [hcEq] using hc1'
          exact (Set.disjoint_left.mp hDisj hc2'C1) hc2'
      | inr pb =>
          have hsum : (pa : V d × V d).1 + (pa : V d × V d).2 =
              (pb : V d × V d).1 + (pb : V d × V d).2 := by
            simpa [jointSum] using hab
          have hpair := IsComplement_add_left_unique hNVT2 (hC2sub pa.2.1) (hC2sub pb.2.1)
            pa.2.2 pb.2.2 hsum
          apply congrArg Sum.inr
          apply Subtype.ext
          apply Prod.ext
          · simpa using hpair.1
          · simpa using hpair.2

lemma pair_solvable {d N : ℕ} (L : AddSubgroup (V d)) {T T₁ T₂ C₁ C₂ : Set (V d)}
    (hNV : AddSubgroup.IsComplement (NV d N) T)
    (hNVT1 : AddSubgroup.IsComplement (NV d N) T₁)
    (hNVT2 : AddSubgroup.IsComplement (NV d N) T₂)
    (hT1 : T₁ + NL d N L = T + NL d N L)
    (hT2 : T₂ + NL d N L = T + NL d N L)
    (hUn : C₁ ∪ C₂ = NV d N) (hDisj : Disjoint C₁ C₂)
    (hC1 : C₁ + NL d N L = C₁) (hC2 : C₂ + NL d N L = C₂) :
    (0 : V d) ∈ C₁ ∪ C₂ ∧ Function.Bijective (jointSum (d := d) C₁ C₂ T₁ T₂) := by
  constructor
  · rw [hUn]
    exact zero_mem_NV (d := d) (N := N)
  · constructor
    · exact jointSum_injective_of_complements (d := d) (N := N) L hNV hNVT1 hNVT2 hT1 hT2
        hUn hDisj hC1 hC2
    · rw [jointSum_surjective_iff]
      calc
        (C₁ + T₁) ∪ (C₂ + T₂)
            = (C₁ + T) ∪ (C₂ + T) := by
              rw [add_eq_of_periodic (N := N) L hT1 hC1]
              rw [add_eq_of_periodic (N := N) L hT2 hC2]
        _ = (C₁ ∪ C₂) + T := by rw [← Set.union_add]
        _ = NV d N + T := by rw [hUn]
        _ = Set.univ := hNV.add_eq

lemma NV_inter_T_sub_T {d N : ℕ} {T : Set (V d)}
    (hNV : AddSubgroup.IsComplement (NV d N) T) {z : V d}
    (hzNV : z ∈ NV d N) (hzT : z ∈ T - T) : z = 0 := by
  rcases Set.mem_sub.mp hzT with ⟨t₁, ht₁, t₂, ht₂, hz⟩
  have hsum : z + t₂ = (0 : V d) + t₁ := by
    rw [← hz]
    abel
  have hpair := IsComplement_add_left_unique hNV hzNV (zero_mem_NV (d := d) (N := N))
    ht₂ ht₁ hsum
  exact hpair.1

lemma mem_Tj_translate_of_mem_T {d : ℕ} (N : ℕ) (L : AddSubgroup (V d))
    {T Tj : Set (V d)} (hTjS : Tj + NL d N L = T + NL d N L) {c x : V d}
    (hx : x ∈ ({c} + T)) : ∃ n : V d, n ∈ NL d N L ∧ ∃ τ ∈ Tj, x = (c + n) + τ := by
  rcases Set.mem_add.mp hx with ⟨a, ha, t, ht, hxeq⟩
  have hc : a = c := by simpa using ha
  subst a
  have htS : t ∈ T + NL d N L := Set.mem_add.mpr ⟨t, ht, 0, zero_mem_NL N L, by simp⟩
  rw [← hTjS] at htS
  rcases Set.mem_add.mp htS with ⟨τ, hτ, n, hn, htτn⟩
  refine ⟨n, hn, τ, hτ, ?_⟩
  rw [← hxeq]
  rw [← htτn]
  abel

lemma union_add_T_univ {d N : ℕ} (L : AddSubgroup (V d)) {T T₁ T₂ C₁ C₂ : Set (V d)}
    (hT1 : T₁ + NL d N L = T + NL d N L)
    (hT2 : T₂ + NL d N L = T + NL d N L)
    (hC1 : C₁ + NL d N L = C₁) (hC2 : C₂ + NL d N L = C₂)
    (hSurj : Function.Surjective (jointSum (d := d) C₁ C₂ T₁ T₂)) :
    (C₁ ∪ C₂) + T = Set.univ := by
  calc
    (C₁ ∪ C₂) + T = (C₁ + T) ∪ (C₂ + T) := by rw [← Set.union_add]
    _ = (C₁ + T₁) ∪ (C₂ + T₂) := by
      rw [add_eq_of_periodic (N := N) L hT1 hC1]
      rw [add_eq_of_periodic (N := N) L hT2 hC2]
    _ = Set.univ := by
      rw [← jointSum_image]
      exact Function.Surjective.range_eq hSurj

lemma sub_mem_NL_of_mem {d : ℕ} (N : ℕ) (L : AddSubgroup (V d)) {a b : V d}
    (ha : a ∈ NL d N L) (hb : b ∈ NL d N L) : a - b ∈ NL d N L := by
  unfold NL zimg at ha hb
  rw [Set.mem_image] at ha hb
  rcases ha with ⟨a0, ha0, rfl⟩
  rcases hb with ⟨b0, hb0, rfl⟩
  unfold NL zimg
  rw [Set.mem_image]
  refine ⟨a0 - b0, sub_mem ha0 hb0, ?_⟩
  ext i
  simp [Pi.sub_apply, Pi.smul_apply, sub_eq_add_neg]
  ring

lemma add_mem_NL_of_mem {d : ℕ} (N : ℕ) (L : AddSubgroup (V d)) {a b : V d}
    (ha : a ∈ NL d N L) (hb : b ∈ NL d N L) : a + b ∈ NL d N L := by
  unfold NL zimg at ha hb
  rw [Set.mem_image] at ha hb
  rcases ha with ⟨a0, ha0, rfl⟩
  rcases hb with ⟨b0, hb0, rfl⟩
  unfold NL zimg
  rw [Set.mem_image]
  refine ⟨a0 + b0, add_mem ha0 hb0, ?_⟩
  ext i
  simp [Pi.add_apply, Pi.smul_apply]
  ring

lemma inter_empty_iff {α : Type*} {s t : Set α} :
    s ∩ t = ∅ ↔ ∀ x, x ∈ s → x ∈ t → False := by
  constructor
  · intro h x hx1 hx2
    have hx : x ∈ (∅ : Set α) := by rw [← h]; exact ⟨hx1, hx2⟩
    simpa using hx
  · intro h
    ext x
    constructor
    · intro hx
      exact False.elim (h x hx.1 hx.2)
    · intro hx
      exact False.elim (by simpa using hx)

def part1 {d : ℕ} (C₁ T₁ : Set (V d)) : {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁} → V d :=
  fun x => (x : V d × V d).1 + (x : V d × V d).2

def part2 {d : ℕ} (C₂ T₂ : Set (V d)) : {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} → V d :=
  fun x => (x : V d × V d).1 + (x : V d × V d).2

lemma part1_injective_of_jointSum {d : ℕ} {C₁ C₂ T₁ T₂ : Set (V d)}
    (h : Function.Injective (jointSum (d := d) C₁ C₂ T₁ T₂)) :
    Function.Injective (part1 (d := d) C₁ T₁) := by
  intro a b hab
  apply Sum.inl.inj
  exact h hab

lemma part2_injective_of_jointSum {d : ℕ} {C₁ C₂ T₁ T₂ : Set (V d)}
    (h : Function.Injective (jointSum (d := d) C₁ C₂ T₁ T₂)) :
    Function.Injective (part2 (d := d) C₂ T₂) := by
  intro a b hab
  apply Sum.inr.inj
  exact h hab

lemma translate_T_disjoint_same {d N : ℕ} (L : AddSubgroup (V d))
    {T Tj Cj : Set (V d)}
    (hInj : Function.Injective (part1 (d := d) Cj Tj))
    (hNV : AddSubgroup.IsComplement (NV d N) T)
    (hTj : Tj + NL d N L = T + NL d N L)
    (hCj : Cj + NL d N L = Cj)
    {u₁ u₂ : V d} (hu1 : u₁ ∈ Cj) (hu2 : u₂ ∈ Cj) (hne : u₁ ≠ u₂) :
    ({u₁} + T) ∩ ({u₂} + T) = ∅ := by
  rw [inter_empty_iff]
  intro x hx1 hx2
  rcases mem_Tj_translate_of_mem_T (N := N) L hTj hx1 with ⟨n1, hn1, τ1, hτ1, h1⟩
  rcases mem_Tj_translate_of_mem_T (N := N) L hTj hx2 with ⟨n2, hn2, τ2, hτ2, h2⟩
  have hu1n : u₁ + n1 ∈ Cj := by
    rw [← hCj]
    exact Set.mem_add.mpr ⟨u₁, hu1, n1, hn1, rfl⟩
  have hu2n : u₂ + n2 ∈ Cj := by
    rw [← hCj]
    exact Set.mem_add.mpr ⟨u₂, hu2, n2, hn2, rfl⟩
  let a : {p : V d × V d | p.1 ∈ Cj ∧ p.2 ∈ Tj} := ⟨(u₁ + n1, τ1), ⟨hu1n, hτ1⟩⟩
  let b : {p : V d × V d | p.1 ∈ Cj ∧ p.2 ∈ Tj} := ⟨(u₂ + n2, τ2), ⟨hu2n, hτ2⟩⟩
  have hFa : part1 (d := d) Cj Tj a = x := by
    dsimp [a, part1]
    change (u₁ + n1) + τ1 = x
    exact h1.symm
  have hFb : part1 (d := d) Cj Tj b = x := by
    dsimp [b, part1]
    change (u₂ + n2) + τ2 = x
    exact h2.symm
  have hEq : a = b := hInj (hFa.trans hFb.symm)
  have hv := congrArg (fun z : {p : V d × V d | p.1 ∈ Cj ∧ p.2 ∈ Tj} => (z : V d × V d)) hEq
  have hEqc : u₁ + n1 = u₂ + n2 := by
    have hfst := congrArg (fun p : V d × V d => p.1) hv
    simpa using hfst
  have hu2u1_NL : u₂ - u₁ ∈ NL d N L := by
    have hz : u₂ - u₁ = n1 - n2 := by
      apply funext
      intro i
      have hEi := congrFun hEqc i
      simp [Pi.add_apply, Pi.sub_apply] at hEi ⊢
      omega
    rw [hz]
    exact sub_mem_NL_of_mem N L hn1 hn2
  have hu2u1_Tsub : u₂ - u₁ ∈ T - T := by
    rcases Set.mem_add.mp hx1 with ⟨a1, ha1, t1', ht1', hxeq1⟩
    rcases Set.mem_add.mp hx2 with ⟨a2, ha2, t2', ht2', hxeq2⟩
    have ha1' : a1 = u₁ := by simpa using ha1
    have ha2' : a2 = u₂ := by simpa using ha2
    subst a1
    subst a2
    apply Set.mem_sub.mpr
    refine ⟨t1', ht1', t2', ht2', ?_⟩
    have hE : u₁ + t1' = u₂ + t2' := hxeq1.trans hxeq2.symm
    apply funext
    intro i
    have hEi := congrFun hE i
    simp [Pi.add_apply, Pi.sub_apply] at hEi ⊢
    omega
  have hu2u1_NV : u₂ - u₁ ∈ NV d N := NL_subset_NV N L hu2u1_NL
  have hz0 : u₂ - u₁ = 0 := NV_inter_T_sub_T (N := N) (T := T) hNV hu2u1_NV hu2u1_Tsub
  have : u₂ = u₁ := by
    apply funext
    intro i
    have hi := congrFun hz0 i
    simp [Pi.sub_apply] at hi
    omega
  exact hne this.symm

lemma translate_T_disjoint_cross {d N : ℕ} (L : AddSubgroup (V d))
    {T T₁ T₂ C₁ C₂ : Set (V d)}
    (hJoint : Function.Injective (jointSum (d := d) C₁ C₂ T₁ T₂))
    (hT1 : T₁ + NL d N L = T + NL d N L)
    (hT2 : T₂ + NL d N L = T + NL d N L)
    (hC1 : C₁ + NL d N L = C₁) (hC2 : C₂ + NL d N L = C₂)
    {u₁ u₂ : V d} (hu1 : u₁ ∈ C₁) (hu2 : u₂ ∈ C₂) :
    ({u₁} + T) ∩ ({u₂} + T) = ∅ := by
  rw [inter_empty_iff]
  intro x hx1 hx2
  rcases mem_Tj_translate_of_mem_T (N := N) L hT1 hx1 with ⟨n1, hn1, τ1, hτ1, h1⟩
  rcases mem_Tj_translate_of_mem_T (N := N) L hT2 hx2 with ⟨n2, hn2, τ2, hτ2, h2⟩
  have hu1n : u₁ + n1 ∈ C₁ := by
    rw [← hC1]
    exact Set.mem_add.mpr ⟨u₁, hu1, n1, hn1, rfl⟩
  have hu2n : u₂ + n2 ∈ C₂ := by
    rw [← hC2]
    exact Set.mem_add.mpr ⟨u₂, hu2, n2, hn2, rfl⟩
  let a : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
              {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} := Sum.inl ⟨(u₁ + n1, τ1), ⟨hu1n, hτ1⟩⟩
  let b : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
              {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} := Sum.inr ⟨(u₂ + n2, τ2), ⟨hu2n, hτ2⟩⟩
  have hFa : jointSum (d := d) C₁ C₂ T₁ T₂ a = x := by
    dsimp [a, jointSum]
    change (u₁ + n1) + τ1 = x
    exact h1.symm
  have hFb : jointSum (d := d) C₁ C₂ T₁ T₂ b = x := by
    dsimp [b, jointSum]
    change (u₂ + n2) + τ2 = x
    exact h2.symm
  have hEq : a = b := hJoint (hFa.trans hFb.symm)
  cases a <;> cases b <;> contradiction

lemma translate_T_disjoint_union {d N : ℕ} (L : AddSubgroup (V d))
    {T T₁ T₂ C₁ C₂ : Set (V d)}
    (hJoint : Function.Bijective (jointSum (d := d) C₁ C₂ T₁ T₂))
    (hNV : AddSubgroup.IsComplement (NV d N) T)
    (hT1 : T₁ + NL d N L = T + NL d N L)
    (hT2 : T₂ + NL d N L = T + NL d N L)
    (hC1 : C₁ + NL d N L = C₁) (hC2 : C₂ + NL d N L = C₂)
    {u₁ u₂ : V d} (hu1 : u₁ ∈ C₁ ∪ C₂) (hu2 : u₂ ∈ C₁ ∪ C₂) (hne : u₁ ≠ u₂) :
    ({u₁} + T) ∩ ({u₂} + T) = ∅ := by
  rcases hu1 with hu1 | hu1 <;> rcases hu2 with hu2 | hu2
  · exact translate_T_disjoint_same (N := N) L (part1_injective_of_jointSum (d := d) hJoint.1)
      hNV hT1 hC1 hu1 hu2 hne
  · exact translate_T_disjoint_cross (N := N) L hJoint.1 hT1 hT2 hC1 hC2 hu1 hu2
  · rw [Set.inter_comm]
    exact translate_T_disjoint_cross (N := N) L hJoint.1 hT1 hT2 hC1 hC2 hu2 hu1
  · exact translate_T_disjoint_same (N := N) L (part2_injective_of_jointSum (d := d) hJoint.1)
      hNV hT2 hC2 hu1 hu2 hne

lemma IsComplement_union_T {d N : ℕ} (L : AddSubgroup (V d))
    {T T₁ T₂ C₁ C₂ : Set (V d)}
    (hJoint : Function.Bijective (jointSum (d := d) C₁ C₂ T₁ T₂))
    (hNV : AddSubgroup.IsComplement (NV d N) T)
    (hT1 : T₁ + NL d N L = T + NL d N L)
    (hT2 : T₂ + NL d N L = T + NL d N L)
    (hC1 : C₁ + NL d N L = C₁) (hC2 : C₂ + NL d N L = C₂) :
    AddSubgroup.IsComplement (C₁ ∪ C₂) T := by
  rw [AddSubgroup.isComplement_iff_existsUnique]
  intro g
  have hcov : (C₁ ∪ C₂) + T = Set.univ :=
    union_add_T_univ (N := N) L hT1 hT2 hC1 hC2 hJoint.2
  have hg : g ∈ (C₁ ∪ C₂) + T := by rw [hcov]; trivial
  rcases Set.mem_add.mp hg with ⟨u, hu, t, ht, hgut⟩
  refine ⟨(⟨u, hu⟩, ⟨t, ht⟩), hgut, ?_⟩
  intro y hy
  rcases y with ⟨yu, yt⟩
  have hy' : (yu : V d) + (yt : V d) = g := by
    change (yu : V d) + (yt : V d) = g
    simpa using hy
  by_cases hEqU : u = (yu : V d)
  · have htEq : (yt : V d) = t := by
      have hsum1 : u + t = g := hgut
      have hsum2 : (yu : V d) + (yt : V d) = g := hy'
      have hc : u + t = (yu : V d) + (yt : V d) := hsum1.trans hsum2.symm
      exact add_left_cancel (a := (yu : V d)) (by simpa [hEqU] using hc.symm)
    have hyu : yu = (⟨u, hu⟩ : {x : V d // x ∈ C₁ ∪ C₂}) := by
      apply Subtype.ext
      simpa using hEqU.symm
    have hyt : yt = (⟨t, ht⟩ : {x : V d // x ∈ T}) := by
      apply Subtype.ext
      exact htEq
    exact Prod.ext hyu hyt
  · exfalso
    have huU : u ∈ C₁ ∪ C₂ := hu
    have hyuU : (yu : V d) ∈ C₁ ∪ C₂ := yu.2
    have hdisj := translate_T_disjoint_union (N := N) L hJoint hNV hT1 hT2 hC1 hC2
      huU hyuU hEqU
    have hmem1 : g ∈ ({u} + T) := by
      refine Set.mem_add.mpr ⟨u, by simp, t, ht, ?_⟩
      exact hgut
    have hmem2 : g ∈ ({(yu : V d)} + T) := by
      refine Set.mem_add.mpr ⟨(yu : V d), by simp, (yt : V d), yt.2, ?_⟩
      exact hy'
    have hmem : g ∈ ({u} + T) ∩ ({(yu : V d)} + T) := ⟨hmem1, hmem2⟩
    rw [hdisj] at hmem
    exact hmem

lemma pair_forced {d N : ℕ} (L : AddSubgroup (V d)) {T T₁ T₂ C₁ C₂ : Set (V d)}
    (h0C : (0 : V d) ∈ C₁ ∪ C₂)
    (hJoint : Function.Bijective (jointSum (d := d) C₁ C₂ T₁ T₂))
    (hNV : AddSubgroup.IsComplement (NV d N) T)
    (hRig : ∀ A : Set (V d), AddSubgroup.IsComplement A T → (0 : V d) ∈ A → A = NV d N)
    (hT1 : T₁ + NL d N L = T + NL d N L)
    (hT2 : T₂ + NL d N L = T + NL d N L)
    (hC1 : C₁ + NL d N L = C₁) (hC2 : C₂ + NL d N L = C₂)
    (h01 : (0 : V d) ∈ T₁) (h02 : (0 : V d) ∈ T₂) :
    C₁ ∪ C₂ = NV d N ∧ Disjoint C₁ C₂ ∧ C₁ + NL d N L = C₁ ∧ C₂ + NL d N L = C₂ := by
  constructor
  · exact hRig (C₁ ∪ C₂) (IsComplement_union_T (N := N) L hJoint hNV hT1 hT2 hC1 hC2) h0C
  · constructor
    · exact jointSum_disjoint_centers hJoint h01 h02
    · constructor <;> assumption

lemma mem_vsub_iff {d : ℕ} {C : Set (V d)} {v c : V d} :
    c ∈ ((fun x : V d => x - v) '' C) ↔ c + v ∈ C := by
  constructor
  · rintro ⟨c0, hc0, hc0v⟩
    have hc : c = c0 - v := hc0v.symm
    have : c + v = c0 := by
      rw [hc]
      abel
    simpa [this] using hc0
  · intro hcv
    refine ⟨c + v, hcv, ?_⟩
    abel

lemma add_sub_vadd_eq {d : ℕ} (a b v : V d) : (a - v) + b + v = a + b := by
  abel

lemma jointSum_bijective_vsub {d : ℕ} {C₁ C₂ T₁ T₂ : Set (V d)} (v : V d)
    (h : Function.Bijective (jointSum (d := d) C₁ C₂ T₁ T₂)) :
    Function.Bijective (jointSum (d := d) ((fun x : V d => x - v) '' C₁)
        ((fun x : V d => x - v) '' C₂) T₁ T₂) := by
  constructor
  · intro a b hab
    cases a with
    | inl pa =>
        cases b with
        | inl pb =>
            have hpa : (pa : V d × V d).1 + v ∈ C₁ := (mem_vsub_iff.mp pa.2.1)
            have hpb : (pb : V d × V d).1 + v ∈ C₁ := (mem_vsub_iff.mp pb.2.1)
            let a₀ : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                         {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
              Sum.inl ⟨((pa : V d × V d).1 + v, (pa : V d × V d).2), ⟨hpa, pa.2.2⟩⟩
            let b₀ : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                         {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
              Sum.inl ⟨((pb : V d × V d).1 + v, (pb : V d × V d).2), ⟨hpb, pb.2.2⟩⟩
            have hE := congrArg (fun z : V d => z + v) hab
            have hA : ((pa : V d × V d).1 + v) + (pa : V d × V d).2 =
                ((pa : V d × V d).1 + (pa : V d × V d).2) + v := by abel
            have hB : ((pb : V d × V d).1 + v) + (pb : V d × V d).2 =
                ((pb : V d × V d).1 + (pb : V d × V d).2) + v := by abel
            have hE' : ((pa : V d × V d).1 + v) + (pa : V d × V d).2 =
                ((pb : V d × V d).1 + v) + (pb : V d × V d).2 := by
              rw [hA, hB]
              exact hE
            have hEq : a₀ = b₀ := h.1 (by
              dsimp [a₀, b₀, jointSum]
              exact hE')
            dsimp [a₀, b₀] at hEq
            injection hEq with hPairA
            have hvalA := congrArg (fun z : {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁} =>
              (z : V d × V d)) hPairA
            have hfst := congrArg (fun p : V d × V d => p.1) hvalA
            have hsnd := congrArg (fun p : V d × V d => p.2) hvalA
            have hc1 : (pa : V d × V d).1 = (pb : V d × V d).1 := by
              apply funext
              intro i
              have hi := congrFun hfst i
              simp [Pi.add_apply] at hi ⊢
              omega
            have hc2 : (pa : V d × V d).2 = (pb : V d × V d).2 := by
              simpa using hsnd
            apply congrArg Sum.inl
            apply Subtype.ext
            apply Prod.ext
            · simpa [hc1]
            · simpa [hc2]
        | inr pb =>
            exfalso
            have hpa : (pa : V d × V d).1 + v ∈ C₁ := (mem_vsub_iff.mp pa.2.1)
            have hpb : (pb : V d × V d).1 + v ∈ C₂ := (mem_vsub_iff.mp pb.2.1)
            let a₀ : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                         {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
              Sum.inl ⟨((pa : V d × V d).1 + v, (pa : V d × V d).2), ⟨hpa, pa.2.2⟩⟩
            let b₀ : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                         {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
              Sum.inr ⟨((pb : V d × V d).1 + v, (pb : V d × V d).2), ⟨hpb, pb.2.2⟩⟩
            have hE := congrArg (fun z : V d => z + v) hab
            have hA : ((pa : V d × V d).1 + v) + (pa : V d × V d).2 =
                ((pa : V d × V d).1 + (pa : V d × V d).2) + v := by abel
            have hB : ((pb : V d × V d).1 + v) + (pb : V d × V d).2 =
                ((pb : V d × V d).1 + (pb : V d × V d).2) + v := by abel
            have hE' : ((pa : V d × V d).1 + v) + (pa : V d × V d).2 =
                ((pb : V d × V d).1 + v) + (pb : V d × V d).2 := by
              rw [hA, hB]
              exact hE
            have hEq : a₀ = b₀ := h.1 (by
              dsimp [a₀, b₀, jointSum]
              exact hE')
            dsimp [a₀, b₀] at hEq
            cases a₀ <;> cases b₀ <;> contradiction
    | inr pa =>
        cases b with
        | inl pb =>
            exfalso
            have hpa : (pa : V d × V d).1 + v ∈ C₂ := (mem_vsub_iff.mp pa.2.1)
            have hpb : (pb : V d × V d).1 + v ∈ C₁ := (mem_vsub_iff.mp pb.2.1)
            let a₀ : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                         {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
              Sum.inr ⟨((pa : V d × V d).1 + v, (pa : V d × V d).2), ⟨hpa, pa.2.2⟩⟩
            let b₀ : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                         {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
              Sum.inl ⟨((pb : V d × V d).1 + v, (pb : V d × V d).2), ⟨hpb, pb.2.2⟩⟩
            have hE := congrArg (fun z : V d => z + v) hab
            have hA : ((pa : V d × V d).1 + v) + (pa : V d × V d).2 =
                ((pa : V d × V d).1 + (pa : V d × V d).2) + v := by abel
            have hB : ((pb : V d × V d).1 + v) + (pb : V d × V d).2 =
                ((pb : V d × V d).1 + (pb : V d × V d).2) + v := by abel
            have hE' : ((pa : V d × V d).1 + v) + (pa : V d × V d).2 =
                ((pb : V d × V d).1 + v) + (pb : V d × V d).2 := by
              rw [hA, hB]
              exact hE
            have hEq : a₀ = b₀ := h.1 (by
              dsimp [a₀, b₀, jointSum]
              exact hE')
            dsimp [a₀, b₀] at hEq
            cases a₀ <;> cases b₀ <;> contradiction
        | inr pb =>
            have hpa : (pa : V d × V d).1 + v ∈ C₂ := (mem_vsub_iff.mp pa.2.1)
            have hpb : (pb : V d × V d).1 + v ∈ C₂ := (mem_vsub_iff.mp pb.2.1)
            let a₀ : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                         {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
              Sum.inr ⟨((pa : V d × V d).1 + v, (pa : V d × V d).2), ⟨hpa, pa.2.2⟩⟩
            let b₀ : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                         {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
              Sum.inr ⟨((pb : V d × V d).1 + v, (pb : V d × V d).2), ⟨hpb, pb.2.2⟩⟩
            have hE := congrArg (fun z : V d => z + v) hab
            have hA : ((pa : V d × V d).1 + v) + (pa : V d × V d).2 =
                ((pa : V d × V d).1 + (pa : V d × V d).2) + v := by abel
            have hB : ((pb : V d × V d).1 + v) + (pb : V d × V d).2 =
                ((pb : V d × V d).1 + (pb : V d × V d).2) + v := by abel
            have hE' : ((pa : V d × V d).1 + v) + (pa : V d × V d).2 =
                ((pb : V d × V d).1 + v) + (pb : V d × V d).2 := by
              rw [hA, hB]
              exact hE
            have hEq : a₀ = b₀ := h.1 (by
              dsimp [a₀, b₀, jointSum]
              exact hE')
            dsimp [a₀, b₀] at hEq
            injection hEq with hPairA
            have hvalA := congrArg (fun z : {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} =>
              (z : V d × V d)) hPairA
            have hfst := congrArg (fun p : V d × V d => p.1) hvalA
            have hsnd := congrArg (fun p : V d × V d => p.2) hvalA
            have hc1 : (pa : V d × V d).1 = (pb : V d × V d).1 := by
              apply funext
              intro i
              have hi := congrFun hfst i
              simp [Pi.add_apply] at hi ⊢
              omega
            have hc2 : (pa : V d × V d).2 = (pb : V d × V d).2 := by
              simpa using hsnd
            apply congrArg Sum.inr
            apply Subtype.ext
            apply Prod.ext
            · simpa [hc1]
            · simpa [hc2]
  · intro x
    have hx' : x + v ∈ (C₁ + T₁) ∪ (C₂ + T₂) := by
      have hr : Set.range (jointSum (d := d) C₁ C₂ T₁ T₂) = Set.univ :=
        Function.Surjective.range_eq h.2
      rw [jointSum_image] at hr
      rw [hr]
      trivial
    rcases hx' with hx' | hx'
    · rcases Set.mem_add.mp hx' with ⟨c, hc, t, ht, hct⟩
      refine ⟨Sum.inl ⟨(c - v, t), ⟨?_, ht⟩⟩, ?_⟩
      · exact mem_vsub_iff.mpr (by simpa [hct] using hc)
      · dsimp [jointSum]
        apply funext
        intro i
        have hi := congrFun hct i
        simp [Pi.add_apply, Pi.sub_apply] at hi ⊢
        omega
    · rcases Set.mem_add.mp hx' with ⟨c, hc, t, ht, hct⟩
      refine ⟨Sum.inr ⟨(c - v, t), ⟨?_, ht⟩⟩, ?_⟩
      · exact mem_vsub_iff.mpr (by simpa [hct] using hc)
      · dsimp [jointSum]
        apply funext
        intro i
        have hi := congrFun hct i
        simp [Pi.add_apply, Pi.sub_apply] at hi ⊢
        omega

lemma jointSum_subset_eq {d : ℕ} {C₁ C₂ C₁' C₂' T₁ T₂ : Set (V d)}
    (h : Function.Bijective (jointSum (d := d) C₁ C₂ T₁ T₂))
    (h' : Function.Bijective (jointSum (d := d) C₁' C₂' T₁ T₂))
    (h1 : C₁' ⊆ C₁) (h2 : C₂' ⊆ C₂)
    (h01 : (0 : V d) ∈ T₁) (h02 : (0 : V d) ∈ T₂) : C₁' = C₁ ∧ C₂' = C₂ := by
  constructor
  · apply le_antisymm
    · exact h1
    · intro c hc
      rcases h'.2 c with ⟨e', he'⟩
      cases e' with
      | inl z' =>
          let e : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                      {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
            Sum.inl ⟨(z' : V d × V d), ⟨h1 z'.2.1, z'.2.2⟩⟩
          let ec : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                       {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
            Sum.inl ⟨(c, 0), ⟨hc, h01⟩⟩
          have hFe : jointSum (d := d) C₁ C₂ T₁ T₂ e = c := by
            dsimp [e, jointSum]
            -- value = z'.1 + z'.2: equals c by he'
            change (z' : V d × V d).1 + (z' : V d × V d).2 = c
            simpa [jointSum] using he'
          have hFec : jointSum (d := d) C₁ C₂ T₁ T₂ ec = c := by
            dsimp [ec, jointSum]
            simp
          have hEq := h.1 (hFe.trans hFec.symm)
          dsimp [e, ec] at hEq
          injection hEq with hPair
          have hv := congrArg (fun z : {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁} =>
            (z : V d × V d)) hPair
          have hfst := congrArg (fun p : V d × V d => p.1) hv
          have hz : (z' : V d × V d).1 = c := by
            simpa using hfst
          have hz' : c ∈ C₁' := by
            simpa [hz] using z'.2.1
          exact hz'
      | inr z' =>
          exfalso
          let e : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                      {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
            Sum.inr ⟨(z' : V d × V d), ⟨h2 z'.2.1, z'.2.2⟩⟩
          let ec : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                       {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
            Sum.inl ⟨(c, 0), ⟨hc, h01⟩⟩
          have hFe : jointSum (d := d) C₁ C₂ T₁ T₂ e = c := by
            dsimp [e, jointSum]
            change (z' : V d × V d).1 + (z' : V d × V d).2 = c
            simpa [jointSum] using he'
          have hFec : jointSum (d := d) C₁ C₂ T₁ T₂ ec = c := by
            dsimp [ec, jointSum]
            simp
          have hEq := h.1 (hFe.trans hFec.symm)
          dsimp [e, ec] at hEq
          cases e <;> cases ec <;> contradiction
  · apply le_antisymm
    · exact h2
    · intro c hc
      rcases h'.2 c with ⟨e', he'⟩
      cases e' with
      | inl z' =>
          exfalso
          let e : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                      {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
            Sum.inl ⟨(z' : V d × V d), ⟨h1 z'.2.1, z'.2.2⟩⟩
          let ec : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                       {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
            Sum.inr ⟨(c, 0), ⟨hc, h02⟩⟩
          have hFe : jointSum (d := d) C₁ C₂ T₁ T₂ e = c := by
            dsimp [e, jointSum]
            change (z' : V d × V d).1 + (z' : V d × V d).2 = c
            simpa [jointSum] using he'
          have hFec : jointSum (d := d) C₁ C₂ T₁ T₂ ec = c := by
            dsimp [ec, jointSum]
            simp
          have hEq := h.1 (hFe.trans hFec.symm)
          dsimp [e, ec] at hEq
          cases e <;> cases ec <;> contradiction
      | inr z' =>
          let e : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                      {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
            Sum.inr ⟨(z' : V d × V d), ⟨h2 z'.2.1, z'.2.2⟩⟩
          let ec : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                       {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
            Sum.inr ⟨(c, 0), ⟨hc, h02⟩⟩
          have hFe : jointSum (d := d) C₁ C₂ T₁ T₂ e = c := by
            dsimp [e, jointSum]
            change (z' : V d × V d).1 + (z' : V d × V d).2 = c
            simpa [jointSum] using he'
          have hFec : jointSum (d := d) C₁ C₂ T₁ T₂ ec = c := by
            dsimp [ec, jointSum]
            simp
          have hEq := h.1 (hFe.trans hFec.symm)
          dsimp [e, ec] at hEq
          injection hEq with hPair
          have hv := congrArg (fun z : {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} =>
            (z : V d × V d)) hPair
          have hfst := congrArg (fun p : V d × V d => p.1) hv
          have hz : (z' : V d × V d).1 = c := by
            simpa using hfst
          have hz' : c ∈ C₂' := by
            simpa [hz] using z'.2.1
          exact hz'

lemma add_singleton_eq_self_of_vsub_image {d : ℕ} {C : Set (V d)} (p : V d)
    (h : (fun x : V d => x - p) '' C = C) : C + ({p} : Set (V d)) = C := by
  have himg : C + ({p} : Set (V d)) = (fun x : V d => x + p) '' C := by
    ext y
    constructor
    · rintro ⟨c, hc, z, hz, hcz⟩
      have hzp : z = p := by simpa using hz
      subst z
      refine ⟨c, hc, ?_⟩
      exact hcz
    · rintro ⟨c, hc, hcy⟩
      refine Set.mem_add.mpr ⟨c, hc, p, by simp, ?_⟩
      exact hcy
  rw [himg]
  calc
    (fun x : V d => x + p) '' C = (fun x : V d => x + p) '' ((fun x : V d => x - p) '' C) := by
      rw [h]
    _ = C := by
      rw [Set.image_image]
      simp [Function.comp_def, sub_add_cancel]

lemma part_shift_eq_of_clicks {d : ℕ} {C₁ C₂ T₁ T₂ : Set (V d)} (p : V d)
    (hJoint : Function.Bijective (jointSum (d := d) C₁ C₂ T₁ T₂))
    (h01 : (0 : V d) ∈ T₁) (h02 : (0 : V d) ∈ T₂)
    (hClick1 : ∀ c : V d, c ∈ C₁ → c - p ∈ C₁)
    (hClick2 : ∀ c : V d, c ∈ C₂ → c - p ∈ C₂) :
    C₁ + ({p} : Set (V d)) = C₁ ∧ C₂ + ({p} : Set (V d)) = C₂ := by
  let C₁' : Set (V d) := (fun x : V d => x - p) '' C₁
  let C₂' : Set (V d) := (fun x : V d => x - p) '' C₂
  have hB : Function.Bijective (jointSum (d := d) C₁' C₂' T₁ T₂) := by
    simpa [C₁', C₂'] using (jointSum_bijective_vsub (d := d) (v := p) hJoint)
  have hEq := jointSum_subset_eq hJoint hB
    (by intro y hy; rcases hy with ⟨c, hc, rfl⟩; exact hClick1 c hc)
    (by intro y hy; rcases hy with ⟨c, hc, rfl⟩; exact hClick2 c hc) h01 h02
  constructor
  · exact add_singleton_eq_self_of_vsub_image (p := p) (by simpa [C₁'] using hEq.1)
  · exact add_singleton_eq_self_of_vsub_image (p := p) (by simpa [C₂'] using hEq.2)


-- ======================================================================
-- FINAL ASSEMBLY of the rigid-pair theorem (dimension-uniform, d ≥ 1).
-- ======================================================================

/-- `7 ≤ N0 d r`: the tooth-box side is large enough for all constraints -/
lemma N0_ge_seven {d r : ℕ} : 7 ≤ N0 d r := by
  have hK : 3 ≤ K0 d r := K0_pos d r
  have hV : (K0 d r : ℕ) + 3 ≤ V0 d r := by
    dsimp [V0]
    omega
  let A : ℕ := 2 * r * sep r
  have hN0 : N0 d r = V0 d r + A + K0 d r + Rmax r + 6 := by
    dsimp [N0, A]
  omega

/-- every tooth dent set is nonempty -/
lemma toothDent_nonempty {d r : ℕ} (hd : 0 < d) (σ : Fin 2) (l : Fin r) :
    ∃ a : V d, a ∈ toothDent (d := d) (V0 d r) (sep r) r σ l := by
  let R : ℕ := toothRadius r σ l
  let i0 : Fin d := ⟨0, hd⟩
  let s : V d := (R : ℤ) • eb d i0
  refine ⟨toothPos (d := d) (V0 d r) (sep r) r σ l + s, ?_⟩
  rw [toothDent, Set.mem_image]
  refine ⟨s, ?_, rfl⟩
  simpa [s, R] using (smul_eb_mem_shell i0)

/-- basis-bump cells lie outside the box -/
lemma basis_bump_not_mem_box {d N : ℕ} (hN : 1 ≤ N) (i : Fin d) :
    (N : ℤ) • eb d i + xhole (d := d) i ∉ box d N := by
  intro hx
  have hi := (hx i).2
  have hval : ((N : ℤ) • eb d i + xhole (d := d) i) i = (N : ℤ) + 2 := by
    simp [Pi.add_apply, Pi.smul_apply, eb_apply i, xhole_self i]
  rw [hval] at hi
  omega

/-- extra-bump cells lie outside the box -/
lemma toothBump_not_mem_box {d r : ℕ} (hr : 0 < r) (wgen : Fin r → V d)
    (hw : ∀ l : Fin r, wgen l ≠ 0) (σ : Fin 2) (l' : Fin r) (x : V d)
    (hx : x ∈ toothBump (d := d) wgen σ l') : x ∉ box d (N0 d r) := by
  rintro hxbox
  rcases hx with ⟨y, hy, rfl⟩
  have hybox : y ∈ box d (N0 d r) := toothDent_mem_box hr σ l' y hy
  have hwne : ∃ i : Fin d, wgen l' i ≠ 0 := by
    by_contra hn
    apply hw l'
    apply funext
    intro i
    by_contra hz
    exact hn ⟨i, hz⟩
  rcases hwne with ⟨i, hwi⟩
  have hy0 : (0 : ℤ) ≤ y i := (hybox i).1
  have hy1 : y i < (N0 d r : ℤ) := (hybox i).2
  have hxlo : (0 : ℤ) ≤ (((N0 d r : ℤ) • wgen l') + y) i := (hxbox i).1
  have hxhi : (((N0 d r : ℤ) • wgen l') + y) i < (N0 d r : ℤ) := (hxbox i).2
  have hcast : ((N0 d r : ℤ) • wgen l') i = (N0 d r : ℤ) * wgen l' i := by
    simp [Pi.smul_apply]
  rw [Pi.add_apply, hcast] at hxlo hxhi
  have hN0nneg : (0 : ℤ) ≤ (N0 d r : ℤ) := by
    exact_mod_cast (by have h7 := N0_ge_seven (d := d) (r := r); omega : 0 ≤ N0 d r)
  by_cases hpos : 0 < wgen l' i
  · have hmul : (N0 d r : ℤ) ≤ (N0 d r : ℤ) * wgen l' i := by
      have hm := mul_le_mul_of_nonneg_left (a := (N0 d r : ℤ)) (b := (1 : ℤ)) (c := wgen l' i)
        (by omega : (1 : ℤ) ≤ wgen l' i) hN0nneg
      simpa using hm
    have hge : (N0 d r : ℤ) ≤ (((N0 d r : ℤ) * wgen l' i) + y i) := by nlinarith
    exact (lt_irrefl _) (lt_of_lt_of_le hxhi hge)
  · have hneg : wgen l' i ≤ -1 := by omega
    have hmul : (N0 d r : ℤ) * wgen l' i ≤ -(N0 d r : ℤ) := by
      have hm := mul_le_mul_of_nonneg_left (a := (N0 d r : ℤ)) (b := (1 : ℤ)) (c := -wgen l' i)
        (by omega : (1 : ℤ) ≤ -wgen l' i) hN0nneg
      nlinarith
    have hle : (((N0 d r : ℤ) * wgen l' i) + y i) < 0 := by
      have hy1' : y i ≤ (N0 d r : ℤ) - 1 := by omega
      nlinarith
    exact (lt_irrefl _) (lt_of_lt_of_le hle hxlo)

/-- a tooth dent cell is not a cell of its own tile -/
lemma toothDent_not_mem_toothTile {d r : ℕ} (hd : 0 < d) (hr : 0 < r)
    (wgen : Fin r → V d) (hw : ∀ l : Fin r, wgen l ≠ 0)
    (σ : Fin 2) (l : Fin r) (a : V d) (ha : a ∈ toothDent (d := d) (V0 d r) (sep r) r σ l) :
    a ∉ toothTile wgen σ := by
  intro haT
  rcases (toothTile_mem_cases wgen σ a haT) with hbody | hbump | hbump
  · exact (hbody.2.2 l ha)
  · rcases hbump with ⟨i, hi⟩
    have haBox : a ∈ box d (N0 d r) := toothDent_mem_box hr σ l a ha
    rw [hi] at haBox
    exact basis_bump_not_mem_box (by have h7 := N0_ge_seven (d := d) (r := r); omega) i haBox
  · rcases hbump with ⟨l', hl'⟩
    have haBox : a ∈ box d (N0 d r) := toothDent_mem_box hr σ l a ha
    exact toothBump_not_mem_box hr wgen hw σ l' a hl' haBox

/-- `0` is not a tooth dent cell -/
lemma zero_not_mem_toothDent {d r : ℕ} (hd : 0 < d) (σ : Fin 2) (l : Fin r) :
    (0 : V d) ∉ toothDent (d := d) (V0 d r) (sep r) r σ l := by
  intro h0
  let i0 : Fin d := ⟨0, hd⟩
  have h5 : (5 : ℤ) ≤ (0 : V d) i0 := toothDent_coord_ge_five σ l 0 h0 i0
  norm_num at h5

/-- the tooth tile is finite -/
lemma toothTile_finite {d r : ℕ} (w : Fin r → V d) (σ : Fin 2) :
    (toothTile w σ).Finite := by
  unfold toothTile
  refine Set.Finite.union ?_ ?_
  · exact (basisTile_finite d (N0 d r)).subset (by intro x hx; exact hx.1)
  · classical
    let S : Set (Fin r) := Set.univ
    have hS : S.Finite := Set.finite_univ
    have hb : ∀ l ∈ S, (toothBump (d := d) w σ l).Finite := by
      intro l _
      unfold toothBump
      exact (toothDent_finite (d := d) (r := r) σ l).image (fun x : V d => ((N0 d r : ℤ) • w l) + x)
    have hU : (⋃ l ∈ S, toothBump (d := d) w σ l).Finite := Set.Finite.biUnion hS hb
    simpa [S] using hU

/-- `0` is in the tooth tile -/
lemma zero_mem_toothTile {d r : ℕ} (hd : 0 < d) (wgen : Fin r → V d) (σ : Fin 2) :
    (0 : V d) ∈ toothTile wgen σ := by
  unfold toothTile
  left
  constructor
  · exact zero_mem_basisTile (by have h7 := N0_ge_seven (d := d) (r := r); omega)
  · rw [Set.mem_iUnion]
    intro ⟨l, hl⟩
    exact zero_not_mem_toothDent (d := d) (r := r) hd σ l hl

/-- the tooth tile is the basis tile with the dent cells moved by `N·w_l` -/
lemma toothTile_eq {d r : ℕ} (w : Fin r → V d) (σ : Fin 2) :
    toothTile w σ =
      (basisTile d (N0 d r) \ (⋃ l : Fin r, toothDent (d := d) (V0 d r) (sep r) r σ l)) ∪
        (⋃ l : Fin r, (toothDent (d := d) (V0 d r) (sep r) r σ l +
          ({(N0 d r : ℤ) • w l} : Set (V d)))) := by
  unfold toothTile toothBump
  apply congrArg (fun s : Set (V d) =>
    (basisTile d (N0 d r) \ (⋃ l : Fin r, toothDent (d := d) (V0 d r) (sep r) r σ l)) ∪ s)
  apply Set.iUnion_congr
  intro l
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Set.mem_add]
    refine ⟨y, hy, (N0 d r : ℤ) • w l, by simp, ?_⟩
    abel
  · rintro ⟨y, hy, q, hq, hx⟩
    have hq' : q = (N0 d r : ℤ) • w l := by simpa using hq
    subst q
    rw [Set.mem_image]
    refine ⟨y, hy, ?_⟩
    calc
      (N0 d r : ℤ) • w l + y = y + (N0 d r : ℤ) • w l := by abel
      _ = x := hx

/-- dent cells of a tooth are inside the basis tile -/
lemma toothDent_subset_basisTile {d r : ℕ} (hr : 0 < r) (σ : Fin 2) (l : Fin r) :
    toothDent (d := d) (V0 d r) (sep r) r σ l ⊆ basisTile d (N0 d r) := by
  intro x hx
  apply basisTile_body_mem
  · exact toothDent_mem_box hr σ l x hx
  · exact toothDent_disjoint_basis σ l x hx

/-- simultaneous moved-cell transform preserves `IsComplement` -/
lemma IsComplement_moved_family {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    {T : Set G} {ι : Type*} (hT : AddSubgroup.IsComplement (H : Set G) T)
    (X : ι → Set G) (p : ι → G)
    (hX : ∀ l, X l ⊆ T) (hp : ∀ l, p l ∈ H)
    (hXdisj : ∀ ⦃l l' : ι⦄, l ≠ l' → Disjoint (X l) (X l')) :
    AddSubgroup.IsComplement (H : Set G)
      ((T \ (⋃ l : ι, X l)) ∪ (⋃ l : ι, (X l + ({p l} : Set G)))) := by
  classical
  let M : Set G := (T \ (⋃ l : ι, X l)) ∪ (⋃ l : ι, (X l + ({p l} : Set G)))
  rw [AddSubgroup.isComplement_iff_existsUnique]
  intro g
  rcases (hT.existsUnique g) with ⟨y, hy, hyu⟩
  let s : G := (y.1 : G)
  let t : G := (y.2 : G)
  have hsH : s ∈ (H : Set G) := by simpa [s] using y.1.2
  have htT : t ∈ T := by simpa [t] using y.2.2
  have hst : s + t = g := by
    change (y.1 : G) + (y.2 : G) = g
    simpa [s, t] using hy
  by_cases htX : t ∈ (⋃ l : ι, X l)
  · rw [Set.mem_iUnion] at htX
    rcases htX with ⟨l0, htXl0⟩
    have htm : t + p l0 ∈ M := by
      right
      rw [Set.mem_iUnion]
      refine ⟨l0, ?_⟩
      exact Set.mem_add.mpr ⟨t, htXl0, p l0, by simp, rfl⟩
    refine ⟨(⟨s - p l0, sub_mem hsH (hp l0)⟩, ⟨t + p l0, htm⟩), ?sum, ?uniq⟩
    · show (s - p l0) + (t + p l0) = g
      calc
        (s - p l0) + (t + p l0) = s + t := by abel
        _ = g := hst
    · intro y' hy'
      rcases y' with ⟨⟨s', hs'⟩, ⟨t', ht'⟩⟩
      have hsu : (s' : G) + (t' : G) = g := by
        change (s' : G) + (t' : G) = g
        simpa using hy'
      rcases ht' with ht'T | ht'B
      · rw [Set.mem_diff] at ht'T
        have hsum2 : (s' : G) + (t' : G) = s + t := by rw [hst]; exact hsu
        have hpair := IsComplement_add_left_unique hT hs' hsH ht'T.1 htT hsum2
        have ht_eq : (t' : G) = t := hpair.2
        have htm2 : t ∈ (⋃ l : ι, X l) := by
          rw [Set.mem_iUnion]
          exact ⟨l0, htXl0⟩
        exact False.elim (ht'T.2 (by simpa [ht_eq] using htm2))
      · rw [Set.mem_iUnion] at ht'B
        rcases ht'B with ⟨l1, ht'l1⟩
        rcases Set.mem_add.mp ht'l1 with ⟨t1, ht1X, q, hq, ht'eq⟩
        have hq' : q = p l1 := by simpa using hq
        subst q
        have hb1 : (s' + p l1) + t1 = s + t := by
          calc
            (s' + p l1) + t1 = s' + (t1 + p l1) := by abel
            _ = s' + (t' : G) := by rw [ht'eq]
            _ = g := hsu
            _ = s + t := hst.symm
        have hpair := IsComplement_add_left_unique hT
          (show s' + p l1 ∈ (H : Set G) from add_mem hs' (hp l1))
          hsH (hX l1 ht1X) htT hb1
        have ht1eq : t1 = t := hpair.2
        have ht_in_l1 : t ∈ X l1 := by simpa [ht1eq] using ht1X
        have hl_eq : l1 = l0 := by
          by_contra hne
          have h01 : l0 ≠ l1 := fun h => hne h.symm
          have hdj := hXdisj h01
          have hmem : t ∈ (X l0) ∩ (X l1) := ⟨htXl0, ht_in_l1⟩
          exact (Set.disjoint_left.mp hdj) hmem.1 hmem.2
        have hs'eq : (s' : G) = s - p l0 := by
          have h1 : s' + p l0 = s := by simpa [hl_eq] using hpair.1
          apply add_left_cancel (a := p l0)
          have hp : p l0 + (s' : G) = s := by rw [add_comm]; exact h1
          have hgoal : p l0 + (s' : G) = p l0 + (s - p l0) := by rw [hp]; abel
          exact hgoal
        have ht'eq2 : (t' : G) = t + p l0 := by
          calc
            (t' : G) = t1 + p l1 := ht'eq.symm
            _ = t + p l0 := by rw [ht1eq, hl_eq]
        apply Prod.ext
        · apply Subtype.ext
          exact hs'eq
        · apply Subtype.ext
          exact ht'eq2
  · have htm : t ∈ M := by
      left
      exact ⟨htT, htX⟩
    refine ⟨(⟨s, hsH⟩, ⟨t, htm⟩), hst, ?_⟩
    · intro y' hy'
      rcases y' with ⟨⟨s', hs'⟩, ⟨t', ht'⟩⟩
      have hsu : (s' : G) + (t' : G) = g := by
        change (s' : G) + (t' : G) = g
        simpa using hy'
      rcases ht' with ht'T | ht'B
      · rw [Set.mem_diff] at ht'T
        have hsum2 : (s' : G) + (t' : G) = s + t := by rw [hst]; exact hsu
        have hpair := IsComplement_add_left_unique hT hs' hsH ht'T.1 htT hsum2
        have hs_eq : (s' : G) = s := hpair.1
        have ht_eq : (t' : G) = t := hpair.2
        apply Prod.ext
        · apply Subtype.ext
          exact hs_eq
        · apply Subtype.ext
          exact ht_eq
      · rw [Set.mem_iUnion] at ht'B
        rcases ht'B with ⟨l1, ht'l1⟩
        rcases Set.mem_add.mp ht'l1 with ⟨t1, ht1X, q, hq, ht'eq⟩
        have hq' : q = p l1 := by simpa using hq
        subst q
        have hb1 : (s' + p l1) + t1 = s + t := by
          calc
            (s' + p l1) + t1 = s' + (t1 + p l1) := by abel
            _ = s' + (t' : G) := by rw [ht'eq]
            _ = g := hsu
            _ = s + t := hst.symm
        have hpair := IsComplement_add_left_unique hT
          (show s' + p l1 ∈ (H : Set G) from add_mem hs' (hp l1))
          hsH (hX l1 ht1X) htT hb1
        have ht1eq : t1 = t := hpair.2
        have ht_mem : t ∈ (⋃ l : ι, X l) := by
          rw [Set.mem_iUnion]
          refine ⟨l1, ?_⟩
          simpa [ht1eq] using ht1X
        exact False.elim (htX ht_mem)

/-- `NV`-closure of the moved cells: the tooth tile is a fundamental domain -/
lemma IsComplement_NV_toothTile {d r : ℕ} (wgen : Fin r → V d) (σ : Fin 2) :
    AddSubgroup.IsComplement (NV d (N0 d r)) (toothTile wgen σ) := by
  let H : AddSubgroup (V d) := NV_subgroup d (N0 d r)
  have hH : (H : Set (V d)) = NV d (N0 d r) := rfl
  rw [← hH]
  rw [toothTile_eq wgen σ]
  apply IsComplement_moved_family (H := H) (ι := Fin r)
    (X := fun l : Fin r => toothDent (d := d) (V0 d r) (sep r) r σ l)
    (p := fun l : Fin r => (N0 d r : ℤ) • wgen l)
  · rw [hH]
    exact NV_IsComplement_basisTile (by have h7 := N0_ge_seven (d := d) (r := r); omega)
  · intro l
    exact toothDent_subset_basisTile (by
      by_cases hr : 0 < r
      · exact hr
      · exfalso
        exact (hr (by have h := (l.isLt); omega : 0 < r))) σ l
  · intro l
    change (N0 d r : ℤ) • wgen l ∈ (H : Set (V d))
    rw [hH]
    exact smul_mem_NV (wgen l)
  · intro l l' hne
    exact toothDent_disjoint_of_ne σ σ l l' (by intro h; exact hne (congrArg Prod.snd h))

/-- `Tσ + NL = basisTile + NL` (moved-cell equality) -/
lemma toothTile_add_NL {d r : ℕ} (L : AddSubgroup (V d)) (wgen : Fin r → V d)
    (hwL : ∀ l : Fin r, wgen l ∈ L) (σ : Fin 2) :
    (toothTile wgen σ) + NL d (N0 d r) L = basisTile d (N0 d r) + NL d (N0 d r) L := by
  rw [toothTile_eq wgen σ]
  let S : AddSubgroup (V d) := NL_subgroup d (N0 d r) L
  have hS : (S : Set (V d)) = NL d (N0 d r) L := rfl
  rw [← hS]
  apply add_moved_cells (S := S) (ι := Fin r)
    (X := fun l : Fin r => toothDent (d := d) (V0 d r) (sep r) r σ l)
    (p := fun l : Fin r => (N0 d r : ℤ) • wgen l)
  · intro l
    exact toothDent_subset_basisTile (by
      by_cases hr : 0 < r
      · exact hr
      · exfalso
        exact (hr (by have h := (l.isLt); omega : 0 < r))) σ l
  · intro l
    change (N0 d r : ℤ) • wgen l ∈ zimg (N0 d r) (L : Set (V d))
    rw [mem_zimg]
    exact ⟨wgen l, hwL l, rfl⟩



-- ======================================================================
-- FACT A: the joint tiling forces each part to be NL-periodic (per
-- generator), via the extra-tooth click.
-- ======================================================================

/-- injectivity of the joint sum: same-part translates are disjoint (part 1) -/
lemma jointSum_inl_disjoint {d : ℕ} {C₁ C₂ T₁ T₂ : Set (V d)}
    (hInj : Function.Injective (jointSum (d := d) C₁ C₂ T₁ T₂))
    {c w' : V d} (hc : c ∈ C₁) (hw : w' ∈ C₁) (hne : c ≠ w') :
    ({c} + T₁) ∩ ({w'} + T₁) = ∅ := by
  rw [inter_empty_iff]
  intro x hx1 hx2
  rcases Set.mem_add.mp hx1 with ⟨a1, ha1, t1, ht1, h1⟩
  rcases Set.mem_add.mp hx2 with ⟨a2, ha2, t2, ht2, h2⟩
  have ha1' : a1 = c := by simpa using ha1
  have ha2' : a2 = w' := by simpa using ha2
  subst a1
  subst a2
  let u : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
              {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
    Sum.inl ⟨(c, t1), ⟨hc, ht1⟩⟩
  let v : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
              {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
    Sum.inl ⟨(w', t2), ⟨hw, ht2⟩⟩
  have hFu : jointSum (d := d) C₁ C₂ T₁ T₂ u = x := by
    dsimp [u, jointSum]
    exact h1
  have hFv : jointSum (d := d) C₁ C₂ T₁ T₂ v = x := by
    dsimp [v, jointSum]
    exact h2
  have hEq : u = v := hInj (hFu.trans hFv.symm)
  dsimp [u, v] at hEq
  injection hEq with hPair
  have hv := congrArg (fun z : {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁} => (z : V d × V d)) hPair
  have hc' := congrArg (fun p : V d × V d => p.1) hv
  have : c = w' := by simpa using hc'
  exact hne this

/-- injectivity of the joint sum: same-part translates are disjoint (part 2) -/
lemma jointSum_inr_disjoint {d : ℕ} {C₁ C₂ T₁ T₂ : Set (V d)}
    (hInj : Function.Injective (jointSum (d := d) C₁ C₂ T₁ T₂))
    {c w' : V d} (hc : c ∈ C₂) (hw : w' ∈ C₂) (hne : c ≠ w') :
    ({c} + T₂) ∩ ({w'} + T₂) = ∅ := by
  rw [inter_empty_iff]
  intro x hx1 hx2
  rcases Set.mem_add.mp hx1 with ⟨a1, ha1, t1, ht1, h1⟩
  rcases Set.mem_add.mp hx2 with ⟨a2, ha2, t2, ht2, h2⟩
  have ha1' : a1 = c := by simpa using ha1
  have ha2' : a2 = w' := by simpa using ha2
  subst a1
  subst a2
  let u : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
              {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
    Sum.inr ⟨(c, t1), ⟨hc, ht1⟩⟩
  let v : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
              {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
    Sum.inr ⟨(w', t2), ⟨hw, ht2⟩⟩
  have hFu : jointSum (d := d) C₁ C₂ T₁ T₂ u = x := by
    dsimp [u, jointSum]
    exact h1
  have hFv : jointSum (d := d) C₁ C₂ T₁ T₂ v = x := by
    dsimp [v, jointSum]
    exact h2
  have hEq : u = v := hInj (hFu.trans hFv.symm)
  dsimp [u, v] at hEq
  injection hEq with hPair
  have hv := congrArg (fun z : {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} => (z : V d × V d)) hPair
  have hc' := congrArg (fun p : V d × V d => p.1) hv
  have : c = w' := by simpa using hc'
  exact hne this

/-- injectivity of the joint sum: cross-part translates are disjoint -/
lemma jointSum_mix_disjoint {d : ℕ} {C₁ C₂ T₁ T₂ : Set (V d)}
    (hInj : Function.Injective (jointSum (d := d) C₁ C₂ T₁ T₂))
    {c w' : V d} (hc : c ∈ C₁) (hw : w' ∈ C₂) :
    ({c} + T₁) ∩ ({w'} + T₂) = ∅ := by
  rw [inter_empty_iff]
  intro x hx1 hx2
  rcases Set.mem_add.mp hx1 with ⟨a1, ha1, t1, ht1, h1⟩
  rcases Set.mem_add.mp hx2 with ⟨a2, ha2, t2, ht2, h2⟩
  have ha1' : a1 = c := by simpa using ha1
  have ha2' : a2 = w' := by simpa using ha2
  subst a1
  subst a2
  let u : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
              {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
    Sum.inl ⟨(c, t1), ⟨hc, ht1⟩⟩
  let v : Sum {p : V d × V d | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
              {p : V d × V d | p.1 ∈ C₂ ∧ p.2 ∈ T₂} :=
    Sum.inr ⟨(w', t2), ⟨hw, ht2⟩⟩
  have hFu : jointSum (d := d) C₁ C₂ T₁ T₂ u = x := by
    dsimp [u, jointSum]
    exact h1
  have hFv : jointSum (d := d) C₁ C₂ T₁ T₂ v = x := by
    dsimp [v, jointSum]
    exact h2
  have hEq : u = v := hInj (hFu.trans hFv.symm)
  cases u <;> cases v <;> contradiction

/-- a dent cell of part σ, covered by a translate of part σ', forces the click.
Part 1 dent covered from part 1. -/
lemma click_step_00 {d r : ℕ} (hd : 0 < d) (hr : 0 < r) (wgen : Fin r → V d)
    (hw : ∀ l : Fin r, wgen l ≠ 0) (C₁ C₂ : Set (V d))
    (hJoint : Function.Bijective (jointSum (d := d) C₁ C₂ (toothTile wgen 0) (toothTile wgen 1)))
    {l : Fin r} (c : V d) (hc : c ∈ C₁)
    (a t' w' : V d)
    (ha : a ∈ toothDent (d := d) (V0 d r) (sep r) r 0 l)
    (ht' : t' ∈ toothTile wgen 0) (hw' : w' ∈ C₁)
    (hcovz : c + a = w' + t') (hw'ne : w' ≠ c) :
    c - (N0 d r : ℤ) • wgen l ∈ C₁ := by
  let z : V d := c + a
  have hz : z = c + a := rfl
  have hcov : z = w' + t' := by
    dsimp [z]
    exact hcovz
  have hdisj : ({c} + toothTile wgen 0) ∩ ({w'} + toothTile wgen 0) = ∅ :=
    jointSum_inl_disjoint hJoint.1 hc hw' (Ne.symm hw'ne)
  have hres := extra_click (d := d) (r := r) hd hr wgen
    (fun σ0 : Fin 2 => if σ0 = 0 then C₁ else C₂)
    (σ := 0) (l := l) c w' a t' z (σ' := 0)
    (by simp [hc]) hz ha hcov ht' hdisj (by simp [hw'])
  simpa using hres

/-- Part 1 dent covered from part 2. -/
lemma click_step_01 {d r : ℕ} (hd : 0 < d) (hr : 0 < r) (wgen : Fin r → V d)
    (hw : ∀ l : Fin r, wgen l ≠ 0) (C₁ C₂ : Set (V d))
    (hJoint : Function.Bijective (jointSum (d := d) C₁ C₂ (toothTile wgen 0) (toothTile wgen 1)))
    {l : Fin r} (c : V d) (hc : c ∈ C₁)
    (a t' w' : V d)
    (ha : a ∈ toothDent (d := d) (V0 d r) (sep r) r 0 l)
    (ht' : t' ∈ toothTile wgen 1) (hw' : w' ∈ C₂)
    (hcovz : c + a = w' + t') :
    c - (N0 d r : ℤ) • wgen l ∈ C₁ := by
  let z : V d := c + a
  have hz : z = c + a := rfl
  have hcov : z = w' + t' := by
    dsimp [z]
    exact hcovz
  have hdisj : ({c} + toothTile wgen 0) ∩ ({w'} + toothTile wgen 1) = ∅ :=
    jointSum_mix_disjoint hJoint.1 hc hw'
  have hres := extra_click (d := d) (r := r) hd hr wgen
    (fun σ0 : Fin 2 => if σ0 = 0 then C₁ else C₂)
    (σ := 0) (l := l) c w' a t' z (σ' := 1)
    (by simp [hc]) hz ha hcov ht' hdisj (by simp [hw'])
  simpa using hres

/-- Part 2 dent covered from part 1. -/
lemma click_step_10 {d r : ℕ} (hd : 0 < d) (hr : 0 < r) (wgen : Fin r → V d)
    (hw : ∀ l : Fin r, wgen l ≠ 0) (C₁ C₂ : Set (V d))
    (hJoint : Function.Bijective (jointSum (d := d) C₁ C₂ (toothTile wgen 0) (toothTile wgen 1)))
    {l : Fin r} (c : V d) (hc : c ∈ C₂)
    (a t' w' : V d)
    (ha : a ∈ toothDent (d := d) (V0 d r) (sep r) r 1 l)
    (ht' : t' ∈ toothTile wgen 0) (hw' : w' ∈ C₁)
    (hcovz : c + a = w' + t') :
    c - (N0 d r : ℤ) • wgen l ∈ C₂ := by
  let z : V d := c + a
  have hz : z = c + a := rfl
  have hcov : z = w' + t' := by
    dsimp [z]
    exact hcovz
  have hdisj : ({c} + toothTile wgen 1) ∩ ({w'} + toothTile wgen 0) = ∅ := by
    rw [Set.inter_comm]
    exact jointSum_mix_disjoint hJoint.1 hw' hc
  have hres := extra_click (d := d) (r := r) hd hr wgen
    (fun σ0 : Fin 2 => if σ0 = 0 then C₁ else C₂)
    (σ := 1) (l := l) c w' a t' z (σ' := 0)
    (by simp [hc]) hz ha hcov ht' hdisj (by simp [hw'])
  simpa using hres

/-- Part 2 dent covered from part 2. -/
lemma click_step_11 {d r : ℕ} (hd : 0 < d) (hr : 0 < r) (wgen : Fin r → V d)
    (hw : ∀ l : Fin r, wgen l ≠ 0) (C₁ C₂ : Set (V d))
    (hJoint : Function.Bijective (jointSum (d := d) C₁ C₂ (toothTile wgen 0) (toothTile wgen 1)))
    {l : Fin r} (c : V d) (hc : c ∈ C₂)
    (a t' w' : V d)
    (ha : a ∈ toothDent (d := d) (V0 d r) (sep r) r 1 l)
    (ht' : t' ∈ toothTile wgen 1) (hw' : w' ∈ C₂)
    (hcovz : c + a = w' + t') (hw'ne : w' ≠ c) :
    c - (N0 d r : ℤ) • wgen l ∈ C₂ := by
  let z : V d := c + a
  have hz : z = c + a := rfl
  have hcov : z = w' + t' := by
    dsimp [z]
    exact hcovz
  have hdisj : ({c} + toothTile wgen 1) ∩ ({w'} + toothTile wgen 1) = ∅ :=
    jointSum_inr_disjoint hJoint.1 hc hw' (Ne.symm hw'ne)
  have hres := extra_click (d := d) (r := r) hd hr wgen
    (fun σ0 : Fin 2 => if σ0 = 0 then C₁ else C₂)
    (σ := 1) (l := l) c w' a t' z (σ' := 1)
    (by simp [hc]) hz ha hcov ht' hdisj (by simp [hw'])
  simpa using hres


/-- in a joint tiling, every dent cell of a part translate is covered from a
translate whose centre is `c - N·w_l`; hence the part is closed under that shift -/
lemma joint_click {d r : ℕ} (hd : 0 < d) (hr : 0 < r) (wgen : Fin r → V d)
    (hw : ∀ l : Fin r, wgen l ≠ 0) (C₁ C₂ : Set (V d))
    (hJoint : Function.Bijective (jointSum (d := d) C₁ C₂ (toothTile wgen 0) (toothTile wgen 1)))
    (h01 : (0 : V d) ∈ toothTile wgen 0) (h02 : (0 : V d) ∈ toothTile wgen 1)
    {σ : Fin 2} {l : Fin r} (c : V d)
    (hc : c ∈ (if σ = 0 then C₁ else C₂)) :
    c - (N0 d r : ℤ) • wgen l ∈ (if σ = 0 then C₁ else C₂) := by
  fin_cases σ
  · have hc' : c ∈ C₁ := by simpa using hc
    rcases (toothDent_nonempty hd (0 : Fin 2) l) with ⟨a0, ha0⟩
    let z : V d := c + a0
    have hz_not : z ∉ ({c} + toothTile wgen 0) := by
      intro hzz
      rcases Set.mem_add.mp hzz with ⟨u, hu, t, ht, hsum⟩
      have hu' : u = c := by simpa using hu
      subst u
      have ht0 : t = a0 := by
        apply add_left_cancel (a := c)
        calc
          c + t = z := hsum
          _ = c + a0 := rfl
      have haT : a0 ∈ toothTile wgen 0 := by simpa [ht0] using ht
      exact toothDent_not_mem_toothTile hd hr wgen hw 0 l a0 ha0 haT
    rcases (hJoint.2 z) with ⟨e, he⟩
    cases e with
    | inl pa =>
        let w' : V d := (pa : V d × V d).1
        let t' : V d := (pa : V d × V d).2
        have hw' : w' ∈ C₁ := by simpa [w'] using pa.2.1
        have ht' : t' ∈ toothTile wgen 0 := by simpa [t'] using pa.2.2
        have he' : w' + t' = z := by
          change (pa : V d × V d).1 + (pa : V d × V d).2 = z
          simpa [w', t', jointSum] using he
        have hw'ne : w' ≠ c := by
          intro hwc
          have hta : t' = a0 := by
            apply add_left_cancel (a := c)
            calc
              c + t' = w' + t' := by rw [hwc]
              _ = z := he'
              _ = c + a0 := rfl
          have haT : a0 ∈ toothTile wgen 0 := by simpa [hta] using ht'
          exact toothDent_not_mem_toothTile hd hr wgen hw 0 l a0 ha0 haT
        have hcovz : c + a0 = w' + t' := by
          calc
            c + a0 = z := rfl
            _ = w' + t' := he'.symm
        have hres := click_step_00 hd hr wgen hw C₁ C₂ hJoint (l := l) c hc' a0 t' w' ha0 ht' hw' hcovz hw'ne
        simpa using hres
    | inr pa =>
        let w' : V d := (pa : V d × V d).1
        let t' : V d := (pa : V d × V d).2
        have hw' : w' ∈ C₂ := by simpa [w'] using pa.2.1
        have ht' : t' ∈ toothTile wgen 1 := by simpa [t'] using pa.2.2
        have he' : w' + t' = z := by
          change (pa : V d × V d).1 + (pa : V d × V d).2 = z
          simpa [w', t', jointSum] using he
        have hcovz : c + a0 = w' + t' := by
          calc
            c + a0 = z := rfl
            _ = w' + t' := he'.symm
        have hres := click_step_01 hd hr wgen hw C₁ C₂ hJoint (l := l) c hc' a0 t' w' ha0 ht' hw' hcovz
        simpa using hres
  · have hc' : c ∈ C₂ := by simpa using hc
    rcases (toothDent_nonempty hd (1 : Fin 2) l) with ⟨a0, ha0⟩
    let z : V d := c + a0
    have hz_not : z ∉ ({c} + toothTile wgen 1) := by
      intro hzz
      rcases Set.mem_add.mp hzz with ⟨u, hu, t, ht, hsum⟩
      have hu' : u = c := by simpa using hu
      subst u
      have ht0 : t = a0 := by
        apply add_left_cancel (a := c)
        calc
          c + t = z := hsum
          _ = c + a0 := rfl
      have haT : a0 ∈ toothTile wgen 1 := by simpa [ht0] using ht
      exact toothDent_not_mem_toothTile hd hr wgen hw 1 l a0 ha0 haT
    rcases (hJoint.2 z) with ⟨e, he⟩
    cases e with
    | inl pa =>
        let w' : V d := (pa : V d × V d).1
        let t' : V d := (pa : V d × V d).2
        have hw' : w' ∈ C₁ := by simpa [w'] using pa.2.1
        have ht' : t' ∈ toothTile wgen 0 := by simpa [t'] using pa.2.2
        have he' : w' + t' = z := by
          change (pa : V d × V d).1 + (pa : V d × V d).2 = z
          simpa [w', t', jointSum] using he
        have hcovz : c + a0 = w' + t' := by
          calc
            c + a0 = z := rfl
            _ = w' + t' := he'.symm
        have hres := click_step_10 hd hr wgen hw C₁ C₂ hJoint (l := l) c hc' a0 t' w' ha0 ht' hw' hcovz
        simpa using hres
    | inr pa =>
        let w' : V d := (pa : V d × V d).1
        let t' : V d := (pa : V d × V d).2
        have hw' : w' ∈ C₂ := by simpa [w'] using pa.2.1
        have ht' : t' ∈ toothTile wgen 1 := by simpa [t'] using pa.2.2
        have he' : w' + t' = z := by
          change (pa : V d × V d).1 + (pa : V d × V d).2 = z
          simpa [w', t', jointSum] using he
        have hw'ne : w' ≠ c := by
          intro hwc
          have hta : t' = a0 := by
            apply add_left_cancel (a := c)
            calc
              c + t' = w' + t' := by rw [hwc]
              _ = z := he'
              _ = c + a0 := rfl
          have haT : a0 ∈ toothTile wgen 1 := by simpa [hta] using ht'
          exact toothDent_not_mem_toothTile hd hr wgen hw 1 l a0 ha0 haT
        have hcovz : c + a0 = w' + t' := by
          calc
            c + a0 = z := rfl
            _ = w' + t' := he'.symm
        have hres := click_step_11 hd hr wgen hw C₁ C₂ hJoint (l := l) c hc' a0 t' w' ha0 ht' hw' hcovz hw'ne
        simpa using hres

/-- each generator shift stabilises both parts (Fact A per generator) -/
lemma pair_periodic_shift {d r : ℕ} (hd : 0 < d) (hr : 0 < r) (wgen : Fin r → V d)
    (hw : ∀ l : Fin r, wgen l ≠ 0) (C₁ C₂ : Set (V d))
    (hJoint : Function.Bijective (jointSum (d := d) C₁ C₂ (toothTile wgen 0) (toothTile wgen 1)))
    (h01 : (0 : V d) ∈ toothTile wgen 0) (h02 : (0 : V d) ∈ toothTile wgen 1)
    (l : Fin r) :
    C₁ + ({(N0 d r : ℤ) • wgen l} : Set (V d)) = C₁ ∧
    C₂ + ({(N0 d r : ℤ) • wgen l} : Set (V d)) = C₂ := by
  exact part_shift_eq_of_clicks (p := (N0 d r : ℤ) • wgen l) hJoint h01 h02
    (by intro c hc; simpa using (joint_click hd hr wgen hw C₁ C₂ hJoint h01 h02 (σ := 0) (l := l) c (by simp [hc])))
    (by intro c hc; simpa using (joint_click hd hr wgen hw C₁ C₂ hJoint h01 h02 (σ := 1) (l := l) c (by simp [hc])))



-- ======================================================================
-- FACT A (closure): the per-generator stabilisation upgrades to `NL`.
-- ======================================================================

/-- a set shifted by `h` is the image under `+h` -/
lemma set_add_eq_image {G : Type*} [AddCommGroup G] (C : Set G) (h : G) :
    C + ({h} : Set G) = (fun x : G => x + h) '' C := by
  ext y
  constructor
  · rintro ⟨c, hc, h0, hh, hy⟩
    have h0' : h0 = h := by simpa using hh
    subst h0
    refine ⟨c, hc, ?_⟩
    exact hy
  · rintro ⟨c, hc, hy⟩
    refine Set.mem_add.mpr ⟨c, hc, h, by simp, ?_⟩
    exact hy

/-- translations that fix a set form a subgroup -/
def fixed_translation_subgroup {G : Type*} [AddCommGroup G] (C : Set G) : AddSubgroup G where
  carrier := {h : G | (fun x : G => x + h) '' C = C}
  zero_mem' := by
    change (fun x : G => x + 0) '' C = C
    ext y
    constructor
    · rintro ⟨x, hx, hy⟩
      have : y = x := by
        rw [← hy]
        simp
      simpa [this] using hx
    · intro hy
      refine ⟨y, hy, ?_⟩
      simp
  add_mem' := by
    intro h k hh hk
    change (fun x : G => x + (h + k)) '' C = C
    ext y
    constructor
    · rintro ⟨x, hx, hy⟩
      have hx1 : x + h ∈ C := by
        have : x + h ∈ (fun z : G => z + h) '' C := ⟨x, hx, rfl⟩
        rwa [hh] at this
      have hmem : y ∈ (fun z : G => z + k) '' C := by
        refine ⟨x + h, hx1, ?_⟩
        rw [← hy]
        abel
      rwa [hk] at hmem
    · intro hy
      have hk1 : y ∈ (fun z : G => z + k) '' C := by rwa [hk]
      rw [Set.mem_image] at hk1
      rcases hk1 with ⟨c1, hc1, hc1y⟩
      have hh1 : c1 ∈ (fun z : G => z + h) '' C := by rwa [hh]
      rw [Set.mem_image] at hh1
      rcases hh1 with ⟨c, hc, hch⟩
      refine ⟨c, hc, ?_⟩
      calc
        (fun z : G => z + (h + k)) c = c + (h + k) := rfl
        _ = (c + h) + k := by abel
        _ = c1 + k := by rw [hch]
        _ = y := hc1y
  neg_mem' := by
    intro h hh
    change (fun x : G => x + (-h)) '' C = C
    apply le_antisymm
    · intro x hx
      rw [Set.mem_image] at hx
      rcases hx with ⟨c, hc, hx⟩
      have hc1 : c ∈ (fun z : G => z + h) '' C := by rwa [hh]
      rw [Set.mem_image] at hc1
      rcases hc1 with ⟨c1, hc1, hc1c⟩
      have hx' : x = c1 := by
        calc
          x = c + (-h) := hx.symm
          _ = (c1 + h) + (-h) := by rw [hc1c]
          _ = c1 := by abel
      simpa [hx'] using hc1
    · intro y hy
      have hyh : y + h ∈ (fun z : G => z + h) '' C := by
        refine ⟨y, hy, rfl⟩
      have hyh' : y + h ∈ C := by rwa [hh] at hyh
      refine ⟨y + h, hyh', ?_⟩
      abel

/-- subgroup membership via the set-sum form of a translation -/
lemma mem_fixed_translation_subgroup_iff {G : Type*} [AddCommGroup G] (C : Set G) (h : G) :
    h ∈ fixed_translation_subgroup C ↔ C + ({h} : Set G) = C := by
  rw [set_add_eq_image]
  rfl

/-- if `s ∈ S` fixes `C` for every `s`, then `S` fixes `C` -/
lemma set_add_eq_self_of_singletons {G : Type*} [AddCommGroup G] {C S : Set G}
    (hS0 : (0 : G) ∈ S) (h : ∀ s ∈ S, C + ({s} : Set G) = C) : C + S = C := by
  apply le_antisymm
  · intro x hx
    rcases Set.mem_add.mp hx with ⟨c, hc, s, hs, rfl⟩
    have hc1 : c + s ∈ C + ({s} : Set G) := Set.mem_add.mpr ⟨c, hc, s, by simp, rfl⟩
    have : c + s ∈ C := by rwa [h s hs] at hc1
    exact this
  · intro x hx
    refine Set.mem_add.mpr ⟨x, hx, 0, hS0, by simp⟩

/-- pushing the generators through a homomorphism lands in any subgroup that
contains the pushed generators -/
lemma closure_comp_subgroup {G : Type*} [AddCommGroup G] {ι : Type*}
    (φ : G →+ G) (S : AddSubgroup G) (w : ι → G)
    (hw : ∀ i : ι, φ (w i) ∈ S) :
    ∀ x ∈ (AddSubgroup.closure (Set.range w) : Set G), φ x ∈ S := by
  intro x hx
  have hle : AddSubgroup.closure (Set.range w) ≤ S.comap φ := by
    rw [AddSubgroup.closure_le]
    intro y hy
    rcases hy with ⟨i, rfl⟩
    exact hw i
  exact hle hx

/-- stabilisation of `C` by each generator `N·w_l` gives stabilisation by all
of `NL` -/
lemma add_NL_eq_self_of_generators {d N : ℕ} {C : Set (V d)} (L : AddSubgroup (V d))
    {r : ℕ} (wgen : Fin r → V d)
    (hspan : L = AddSubgroup.closure (Set.range wgen))
    (hgen : ∀ l : Fin r, C + ({(N : ℤ) • wgen l} : Set (V d)) = C) :
    C + NL d N L = C := by
  let S : AddSubgroup (V d) := fixed_translation_subgroup C
  have hSgen : ∀ l : Fin r, (N : ℤ) • wgen l ∈ (S : Set (V d)) := by
    intro l
    have hset : (N : ℤ) • wgen l ∈ (fixed_translation_subgroup C : Set (V d)) := by
      change (fun x : V d => x + (N : ℤ) • wgen l) '' C = C
      rw [← set_add_eq_image]
      exact hgen l
    simpa [S] using hset
  let φ : V d →+ V d :=
    { toFun := fun x : V d => (N : ℤ) • x
      map_zero' := by simp
      map_add' := by intro x y; simp [smul_add] }
  have hφ : ∀ x, x ∈ (AddSubgroup.closure (Set.range wgen) : Set (V d)) →
      (N : ℤ) • x ∈ (S : Set (V d)) := by
    intro x hx
    have hcl := closure_comp_subgroup (φ := φ) (S := S) wgen (by intro l; exact hSgen l)
    exact hcl x hx
  apply set_add_eq_self_of_singletons (S := NL d N L) (C := C)
  · exact zero_mem_NL N L
  · intro s hs
    rw [NL, mem_zimg] at hs
    rcases hs with ⟨a, haL, hs⟩
    have haSpan : a ∈ (AddSubgroup.closure (Set.range wgen) : Set (V d)) := by
      rw [← hspan]
      exact haL
    have hSa : (N : ℤ) • a ∈ (S : Set (V d)) := hφ a haSpan
    have hSa' : (N : ℤ) • a ∈ (fixed_translation_subgroup C : Set (V d)) := by simpa [S] using hSa
    have hfix : (fun x : V d => x + (N : ℤ) • a) '' C = C := by
      change (N : ℤ) • a ∈ (fixed_translation_subgroup C : Set (V d))
      exact hSa'
    rw [hs]
    rw [set_add_eq_image]
    exact hfix



/-- `Set.image2 Add.add A B = A + B` (definitional, in the `Add.add` form) -/
lemma image2_add_add_eq {d : ℕ} (A B : Set (V d)) : Set.image2 Add.add A B = A + B := rfl

-- THE PAIR IFF FOR THE CONCRETE CONSTRUCTION, AND THE MAIN THEOREM.
-- ======================================================================

/-- for the concrete tile/tiles, the pair condition is exactly the disjoint
`NL`-periodic partition of `NV` -/
lemma rigid_pair_iff {d r : ℕ} (hd : 0 < d) (wgen : Fin r → V d) (L : AddSubgroup (V d))
    (hwL : ∀ l : Fin r, wgen l ∈ L) (hw0 : ∀ l : Fin r, wgen l ≠ 0)
    (hspan : L = AddSubgroup.closure (Set.range wgen)) (C₁ C₂ : Set (V d)) :
    ((0 : V d) ∈ C₁ ∪ C₂ ∧
      Function.Bijective (jointSum (d := d) C₁ C₂ (toothTile wgen 0) (toothTile wgen 1))) ↔
    (C₁ ∪ C₂ = NV d (N0 d r) ∧ Disjoint C₁ C₂ ∧
      C₁ + NL d (N0 d r) L = C₁ ∧ C₂ + NL d (N0 d r) L = C₂) := by
  let N : ℕ := N0 d r
  let T : Set (V d) := basisTile d N
  let T₁ : Set (V d) := toothTile wgen 0
  let T₂ : Set (V d) := toothTile wgen 1
  have hN7 : 7 ≤ N := by dsimp [N]; exact N0_ge_seven (d := d) (r := r)
  have hN1 : 1 ≤ d := by omega
  have h01 : (0 : V d) ∈ toothTile wgen 0 := zero_mem_toothTile hd wgen 0
  have h02 : (0 : V d) ∈ toothTile wgen 1 := zero_mem_toothTile hd wgen 1
  have hNV : AddSubgroup.IsComplement (NV d N) (basisTile d N) := by
    dsimp [N]
    exact NV_IsComplement_basisTile (by have h7 := N0_ge_seven (d := d) (r := r); omega)
  have hRig : ∀ A : Set (V d), AddSubgroup.IsComplement A (basisTile d N) →
      (0 : V d) ∈ A → A = NV d N := by
    dsimp [N]
    exact basis_rigid hN1 (by have h7 := N0_ge_seven (d := d) (r := r); omega)
  have hT1 : toothTile wgen 0 + NL d N L = basisTile d N + NL d N L := by
    dsimp [N]
    exact toothTile_add_NL L wgen hwL 0
  have hT2 : toothTile wgen 1 + NL d N L = basisTile d N + NL d N L := by
    dsimp [N]
    exact toothTile_add_NL L wgen hwL 1
  have hNVT1 : AddSubgroup.IsComplement (NV d N) (toothTile wgen 0) := by
    dsimp [N]
    exact IsComplement_NV_toothTile (d := d) (r := r) wgen 0
  have hNVT2 : AddSubgroup.IsComplement (NV d N) (toothTile wgen 1) := by
    dsimp [N]
    exact IsComplement_NV_toothTile (d := d) (r := r) wgen 1
  constructor
  · intro h
    rcases h with ⟨h0C, hJoint⟩
    have hsh : ∀ l : Fin r,
        C₁ + ({(N0 d r : ℤ) • wgen l} : Set (V d)) = C₁ ∧
        C₂ + ({(N0 d r : ℤ) • wgen l} : Set (V d)) = C₂ := by
      by_cases hr : 0 < r
      · exact fun l => pair_periodic_shift hd hr wgen hw0 C₁ C₂ hJoint h01 h02 l
      · intro l
        exfalso
        have : r = 0 := by omega
        subst r
        exact Fin.elim0 l
    have hgen1 : ∀ l : Fin r, C₁ + ({(N0 d r : ℤ) • wgen l} : Set (V d)) = C₁ := fun l => (hsh l).1
    have hgen2 : ∀ l : Fin r, C₂ + ({(N0 d r : ℤ) • wgen l} : Set (V d)) = C₂ := fun l => (hsh l).2
    have hC1 : C₁ + NL d (N0 d r) L = C₁ :=
      add_NL_eq_self_of_generators (N := N0 d r) (C := C₁) L wgen hspan hgen1
    have hC2 : C₂ + NL d (N0 d r) L = C₂ :=
      add_NL_eq_self_of_generators (N := N0 d r) (C := C₂) L wgen hspan hgen2
    have hres := pair_forced (N := N0 d r) L h0C hJoint hNV hRig hT1 hT2 hC1 hC2 h01 h02
    exact hres
  · intro h
    rcases h with ⟨hUn, hDisj, hC1, hC2⟩
    exact pair_solvable (N := N0 d r) L hNV hNVT1 hNVT2 hT1 hT2 hUn hDisj hC1 hC2



/-- a function from `Fin 0` is the zero function -/
lemma zero_unique {d : ℕ} (hd : d = 0) (x : Fin d → ℤ) : x = 0 := by
  subst d
  apply funext
  intro i
  exact False.elim ((Nat.not_lt_zero i.val) i.isLt)

/-- in dimension 0 the group is a singleton: `T = {0}` with `N = 1` works -/

lemma rigid_pair_data_zero (L : AddSubgroup (Fin 0 → ℤ)) :
  ∃ (N : ℕ) (T T₁ T₂ : Set (Fin 0 → ℤ)),
    0 < N ∧ T.Finite ∧ T₁.Finite ∧ T₂.Finite ∧
    (0 : Fin 0 → ℤ) ∈ T ∧ (0 : Fin 0 → ℤ) ∈ T₁ ∧ (0 : Fin 0 → ℤ) ∈ T₂ ∧
    let NV : Set (Fin 0 → ℤ) := Set.image (fun x => (N : ℤ) • x) Set.univ
    let NL : Set (Fin 0 → ℤ) := Set.image (fun x => (N : ℤ) • x) (L : Set (Fin 0 → ℤ))
    AddSubgroup.IsComplement NV T ∧
    (∀ A : Set (Fin 0 → ℤ), AddSubgroup.IsComplement A T → (0 : Fin 0 → ℤ) ∈ A → A = NV) ∧
    Set.image2 Add.add T₁ NL = Set.image2 Add.add T NL ∧
    Set.image2 Add.add T₂ NL = Set.image2 Add.add T NL ∧
    ∀ C₁ C₂ : Set (Fin 0 → ℤ),
      ((0 : Fin 0 → ℤ) ∈ C₁ ∪ C₂ ∧
        Function.Bijective
          (fun x : Sum {p : (Fin 0 → ℤ) × (Fin 0 → ℤ) | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                       {p : (Fin 0 → ℤ) × (Fin 0 → ℤ) | p.1 ∈ C₂ ∧ p.2 ∈ T₂} =>
            match x with
            | Sum.inl p => p.1.1 + p.1.2
            | Sum.inr p => p.1.1 + p.1.2)) ↔
      (C₁ ∪ C₂ = NV ∧ Disjoint C₁ C₂ ∧
        Set.image2 Add.add C₁ NL = C₁ ∧ Set.image2 Add.add C₂ NL = C₂) := by

  classical
  have hall0 : ∀ x : Fin 0 → ℤ, x = 0 := fun x => zero_unique rfl x
  have hNVuniv : NV 0 1 = (Set.univ : Set (Fin 0 → ℤ)) := by
    ext x
    constructor
    · intro hx
      trivial
    · intro hx
      rw [mem_NV_iff]
      intro i
      exact False.elim ((Nat.not_lt_zero i.val) i.isLt)
  have hNL0 : NL 0 1 L = ({0} : Set (Fin 0 → ℤ)) := by
    apply le_antisymm
    · intro x hx
      have hx0 : x = 0 := hall0 x
      rw [hx0]
      simp
    · intro x hx
      have hx0 : x = 0 := by simpa using hx
      rw [hx0]
      rw [NL, mem_zimg]
      exact ⟨0, zero_mem L, by simp⟩
  have hcompNV : AddSubgroup.IsComplement (NV 0 1) ({0} : Set (Fin 0 → ℤ)) := by
    rw [AddSubgroup.isComplement_iff_existsUnique]
    intro g
    have hg : g = 0 := hall0 g
    subst g
    refine ⟨(⟨0, by rw [hNVuniv]; trivial⟩, ⟨0, by simp⟩), ?_, ?_⟩
    · change (0 : Fin 0 → ℤ) + 0 = 0
      rw [zero_add]
    · intro y hy
      rcases y with ⟨⟨a, ha⟩, ⟨t, ht⟩⟩
      have ha0 : a = 0 := hall0 a
      have ht0 : t = 0 := by simpa using ht
      apply Prod.ext
      · apply Subtype.ext
        exact ha0
      · apply Subtype.ext
        exact ht0
  have hRigid : ∀ A : Set (Fin 0 → ℤ), AddSubgroup.IsComplement A ({0} : Set (Fin 0 → ℤ)) →
      (0 : Fin 0 → ℤ) ∈ A → A = NV 0 1 := by
    intro A hA h0A
    have hAuniv : A = Set.univ := by
      apply le_antisymm
      · intro x hx
        trivial
      · intro x hx
        rcases (hA.existsUnique x) with ⟨y, hy, hyu⟩
        have hax : (y.1 : Fin 0 → ℤ) = x := by
          rw [hall0 (y.1 : Fin 0 → ℤ), hall0 x]
        rw [← hax]
        exact y.1.2
    rw [hAuniv]
    exact hNVuniv.symm
  have hper : ∀ C : Set (Fin 0 → ℤ), C + NL 0 1 L = C := by
    intro C
    apply le_antisymm
    · intro x hx
      rcases Set.mem_add.mp hx with ⟨c, hc, n, hn, hx⟩
      have hn0 : n = 0 := hall0 n
      have hx0 : x = c := by
        rw [← hx]
        rw [hn0]
        rw [add_zero]
      rw [hx0]
      exact hc
    · intro x hx
      refine Set.mem_add.mpr ⟨x, hx, 0, ?_, ?_⟩
      · rw [hNL0]
        simp
      · rw [add_zero]
  refine ⟨1, ({0} : Set (Fin 0 → ℤ)), ({0} : Set (Fin 0 → ℤ)), ({0} : Set (Fin 0 → ℤ)), ?_⟩
  constructor
  · norm_num
  constructor
  · exact Set.finite_singleton 0
  constructor
  · exact Set.finite_singleton 0
  constructor
  · exact Set.finite_singleton 0
  constructor
  · simp
  constructor
  · simp
  constructor
  · simp
  · dsimp
    constructor
    · exact hcompNV
    constructor
    · intro A hA h0A
      change A = NV 0 1
      exact hRigid A hA h0A
    constructor
    · change ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L = ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L
      rfl
    constructor
    · change ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L = ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L
      rfl
    · intro C₁ C₂
      have h01 : (0 : Fin 0 → ℤ) ∈ ({0} : Set (Fin 0 → ℤ)) := by simp
      have hper1 : C₁ + NL 0 1 L = C₁ := hper C₁
      have hper2 : C₂ + NL 0 1 L = C₂ := hper C₂
      have hT : ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L = ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L := rfl
      constructor
      · intro h
        rcases h with ⟨h0C, hBij⟩
        have hBijJ : Function.Bijective (jointSum (d := 0) C₁ C₂ ({0} : Set (Fin 0 → ℤ)) ({0} : Set (Fin 0 → ℤ))) := by
          convert hBij using 1
        rcases (pair_forced (d := 0) (N := 1) L h0C hBijJ hcompNV hRigid hT hT hper1 hper2 h01 h01)
          with ⟨hUn, hDisj, hC1, hC2⟩
        constructor
        · exact hUn
        constructor
        · exact hDisj
        constructor
        · change C₁ + NL 0 1 L = C₁
          exact hC1
        · change C₂ + NL 0 1 L = C₂
          exact hC2
      · intro h
        rcases h with ⟨hUn, hDisj, hC1, hC2⟩
        have hC1' : C₁ + NL 0 1 L = C₁ := by
          change Set.image2 Add.add C₁ (NL 0 1 L) = C₁
          exact hC1
        have hC2' : C₂ + NL 0 1 L = C₂ := by
          change Set.image2 Add.add C₂ (NL 0 1 L) = C₂
          exact hC2
        have hR := pair_solvable (d := 0) (N := 1) L hcompNV hcompNV hcompNV hT hT hUn hDisj hC1' hC2'
        constructor
        · exact hR.1
        · convert hR.2 using 1



/-- For any subgroup `L ≤ ℤ^d` there are a dilation `N` and finite tiles
`T,T₁,T₂` with `T` rigid (`Tile₀(T) = {Nℤ^d}`), `Tⱼ ⊕ NL = T ⊕ NL`, and the
pair tiling equivalence. -/
lemma rigid_pair_data {d : ℕ} (L : AddSubgroup (Fin d → ℤ)) :
  ∃ (N : ℕ) (T T₁ T₂ : Set (Fin d → ℤ)),
    0 < N ∧ T.Finite ∧ T₁.Finite ∧ T₂.Finite ∧
    (0 : Fin d → ℤ) ∈ T ∧ (0 : Fin d → ℤ) ∈ T₁ ∧ (0 : Fin d → ℤ) ∈ T₂ ∧
    let NV : Set (Fin d → ℤ) := Set.image (fun x => (N : ℤ) • x) Set.univ
    let NL : Set (Fin d → ℤ) := Set.image (fun x => (N : ℤ) • x) (L : Set (Fin d → ℤ))
    AddSubgroup.IsComplement NV T ∧
    (∀ A : Set (Fin d → ℤ), AddSubgroup.IsComplement A T → (0 : Fin d → ℤ) ∈ A → A = NV) ∧
    Set.image2 Add.add T₁ NL = Set.image2 Add.add T NL ∧
    Set.image2 Add.add T₂ NL = Set.image2 Add.add T NL ∧
    ∀ C₁ C₂ : Set (Fin d → ℤ),
      ((0 : Fin d → ℤ) ∈ C₁ ∪ C₂ ∧
        Function.Bijective
          (fun x : Sum {p : (Fin d → ℤ) × (Fin d → ℤ) | p.1 ∈ C₁ ∧ p.2 ∈ T₁}
                       {p : (Fin d → ℤ) × (Fin d → ℤ) | p.1 ∈ C₂ ∧ p.2 ∈ T₂} =>
            match x with
            | Sum.inl p => p.1.1 + p.1.2
            | Sum.inr p => p.1.1 + p.1.2)) ↔
      (C₁ ∪ C₂ = NV ∧ Disjoint C₁ C₂ ∧
        Set.image2 Add.add C₁ NL = C₁ ∧ Set.image2 Add.add C₂ NL = C₂) := by
  classical
  by_cases hd : 1 ≤ d
  · have hd0 : 0 < d := by omega
    rcases (small_generating_family_int_subgroup d L) with ⟨r, hr, wgen, hwL, hw0, hwinj, hspan⟩
    refine ⟨N0 d r, basisTile d (N0 d r), toothTile wgen 0, toothTile wgen 1, ?_⟩
    dsimp
    constructor
    · have h7 := N0_ge_seven (d := d) (r := r)
      omega
    constructor
    · exact basisTile_finite d (N0 d r)
    constructor
    · exact toothTile_finite wgen 0
    constructor
    · exact toothTile_finite wgen 1
    constructor
    · exact zero_mem_basisTile (by have h7 := N0_ge_seven (d := d) (r := r); omega)
    constructor
    · exact zero_mem_toothTile hd0 wgen 0
    constructor
    · exact zero_mem_toothTile hd0 wgen 1
    · constructor
      · exact NV_IsComplement_basisTile (by have h7 := N0_ge_seven (d := d) (r := r); omega)
      constructor
      · exact basis_rigid hd (by have h7 := N0_ge_seven (d := d) (r := r); omega)
      constructor
      · change (toothTile wgen 0) + NL d (N0 d r) L = basisTile d (N0 d r) + NL d (N0 d r) L
        exact toothTile_add_NL L wgen hwL 0
      constructor
      · change (toothTile wgen 1) + NL d (N0 d r) L = basisTile d (N0 d r) + NL d (N0 d r) L
        exact toothTile_add_NL L wgen hwL 1
      · intro C₁ C₂
        have hiff := rigid_pair_iff hd0 wgen L hwL hw0 hspan C₁ C₂
        constructor
        · intro h
          rcases h with ⟨h0C, hBij0⟩
          have hBijJ : Function.Bijective (jointSum (d := d) C₁ C₂ (toothTile wgen 0) (toothTile wgen 1)) := by
            convert hBij0 using 1
            funext x
            cases x <;> rfl
          have hR := hiff.mp ⟨h0C, hBijJ⟩
          rcases hR with ⟨hUn, hDisj, hC1, hC2⟩
          constructor
          · exact hUn
          constructor
          · exact hDisj
          constructor
          · rw [image2_add_add_eq]
            exact hC1
          · rw [image2_add_add_eq]
            exact hC2
        · intro h
          rcases h with ⟨hUn, hDisj, hC1, hC2⟩
          have hC1' : C₁ + NL d (N0 d r) L = C₁ := by
            rw [← image2_add_add_eq]
            exact hC1
          have hC2' : C₂ + NL d (N0 d r) L = C₂ := by
            rw [← image2_add_add_eq]
            exact hC2
          have hL0 := hiff.mpr ⟨hUn, hDisj, hC1', hC2'⟩
          constructor
          · exact hL0.1
          · convert hL0.2 using 1
            funext x
            cases x <;> rfl
  · have hd0 : d = 0 := by omega
    subst d
    classical
    have hall0 : ∀ x : Fin 0 → ℤ, x = 0 := fun x => zero_unique rfl x
    have hNVuniv : NV 0 1 = (Set.univ : Set (Fin 0 → ℤ)) := by
      ext x
      constructor
      · intro hx
        trivial
      · intro hx
        rw [mem_NV_iff]
        intro i
        exact False.elim ((Nat.not_lt_zero i.val) i.isLt)
    have hNL0 : NL 0 1 L = ({0} : Set (Fin 0 → ℤ)) := by
      apply le_antisymm
      · intro x hx
        have hx0 : x = 0 := hall0 x
        rw [hx0]
        simp
      · intro x hx
        have hx0 : x = 0 := by simpa using hx
        rw [hx0]
        rw [NL, mem_zimg]
        exact ⟨0, zero_mem L, by simp⟩
    have hcompNV : AddSubgroup.IsComplement (NV 0 1) ({0} : Set (Fin 0 → ℤ)) := by
      rw [AddSubgroup.isComplement_iff_existsUnique]
      intro g
      have hg : g = 0 := hall0 g
      subst g
      refine ⟨(⟨0, by rw [hNVuniv]; trivial⟩, ⟨0, by simp⟩), ?_, ?_⟩
      · change (0 : Fin 0 → ℤ) + 0 = 0
        rw [zero_add]
      · intro y hy
        rcases y with ⟨⟨a, ha⟩, ⟨t, ht⟩⟩
        have ha0 : a = 0 := hall0 a
        have ht0 : t = 0 := by simpa using ht
        apply Prod.ext
        · apply Subtype.ext
          exact ha0
        · apply Subtype.ext
          exact ht0
    have hRigid : ∀ A : Set (Fin 0 → ℤ), AddSubgroup.IsComplement A ({0} : Set (Fin 0 → ℤ)) →
        (0 : Fin 0 → ℤ) ∈ A → A = NV 0 1 := by
      intro A hA h0A
      have hAuniv : A = Set.univ := by
        apply le_antisymm
        · intro x hx
          trivial
        · intro x hx
          rcases (hA.existsUnique x) with ⟨y, hy, hyu⟩
          have hax : (y.1 : Fin 0 → ℤ) = x := by
            rw [hall0 (y.1 : Fin 0 → ℤ), hall0 x]
          rw [← hax]
          exact y.1.2
      rw [hAuniv]
      exact hNVuniv.symm
    have hper : ∀ C : Set (Fin 0 → ℤ), C + NL 0 1 L = C := by
      intro C
      apply le_antisymm
      · intro x hx
        rcases Set.mem_add.mp hx with ⟨c, hc, n, hn, hx⟩
        have hn0 : n = 0 := hall0 n
        have hx0 : x = c := by
          rw [← hx]
          rw [hn0]
          rw [add_zero]
        rw [hx0]
        exact hc
      · intro x hx
        refine Set.mem_add.mpr ⟨x, hx, 0, ?_, ?_⟩
        · rw [hNL0]
          simp
        · rw [add_zero]
    refine ⟨1, ({0} : Set (Fin 0 → ℤ)), ({0} : Set (Fin 0 → ℤ)), ({0} : Set (Fin 0 → ℤ)), ?_⟩
    constructor
    · norm_num
    constructor
    · exact Set.finite_singleton 0
    constructor
    · exact Set.finite_singleton 0
    constructor
    · exact Set.finite_singleton 0
    constructor
    · simp
    constructor
    · simp
    constructor
    · simp
    · dsimp
      constructor
      · exact hcompNV
      constructor
      · intro A hA h0A
        change A = NV 0 1
        exact hRigid A hA h0A
      constructor
      · change ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L = ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L
        rfl
      constructor
      · change ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L = ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L
        rfl
      · intro C₁ C₂
        have h01 : (0 : Fin 0 → ℤ) ∈ ({0} : Set (Fin 0 → ℤ)) := by simp
        have hper1 : C₁ + NL 0 1 L = C₁ := hper C₁
        have hper2 : C₂ + NL 0 1 L = C₂ := hper C₂
        have hT : ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L = ({0} : Set (Fin 0 → ℤ)) + NL 0 1 L := rfl
        constructor
        · intro h
          rcases h with ⟨h0C, hBij⟩
          have hBijJ : Function.Bijective (jointSum (d := 0) C₁ C₂ ({0} : Set (Fin 0 → ℤ)) ({0} : Set (Fin 0 → ℤ))) := by
            convert hBij using 1
          rcases (pair_forced (d := 0) (N := 1) L h0C hBijJ hcompNV hRigid hT hT hper1 hper2 h01 h01)
            with ⟨hUn, hDisj, hC1, hC2⟩
          constructor
          · exact hUn
          constructor
          · exact hDisj
          constructor
          · change C₁ + NL 0 1 L = C₁
            exact hC1
          · change C₂ + NL 0 1 L = C₂
            exact hC2
        · intro h
          rcases h with ⟨hUn, hDisj, hC1, hC2⟩
          have hC1' : C₁ + NL 0 1 L = C₁ := by
            change Set.image2 Add.add C₁ (NL 0 1 L) = C₁
            exact hC1
          have hC2' : C₂ + NL 0 1 L = C₂ := by
            change Set.image2 Add.add C₂ (NL 0 1 L) = C₂
            exact hC2
          have hR := pair_solvable (d := 0) (N := 1) L hcompNV hcompNV hcompNV hT hT hUn hDisj hC1' hC2'
          constructor
          · exact hR.1
          · convert hR.2 using 1

end PeriodicTiling
end Commons