import Mathlib
import Submission.Commons.Topology.Simplex.sperner_parity_mod2
import Submission.Commons.Topology.Simplex.grid_rainbow_cube

/-!
# Sperner's lemma on the Freudenthal triangulation of the simplex grid

The target `Commons.Topology.Simplex.sperner_grid_nat` is Sperner's lemma for the
standard (Freudenthal) triangulation of the mesh-`m` `d`-simplex: for every
colouring of its lattice points by a coordinate in the support of the point there
is a "rainbow" cell, i.e. a family of `d+1` lattice points carrying all `d+1`
colours and pairwise coordinatewise within `1` of one another.

The proof reduces it to the (strictly stronger) cube-shaped statement
`Commons.Topology.Simplex.grid_rainbow_cube`, which is proved by Sperner's lemma
for the staircase triangulation of the order polytope: from the vertex set `S`
produced there one selects one point per colour to build the required function.

The namespace `Commons.Topology.Simplex.Freudenthal` below contains an independent,
self-contained development of the local combinatorics of the Freudenthal
triangulation of the simplex grid (vertices, validity, the flip across a facet,
and the reconstruction (`recon`) of a cell from any cell sharing all but one of
its facets, together with the incidence property `incidence_le_two` that every
facet lies in one or two cells).  It is not needed for the proof of the target
statement and is kept for reuse.
-/


open Finset
open scoped BigOperators

namespace Commons.Topology.Simplex.Freudenthal

/-- Grid points of the standard `(n-1)`-simplex of mesh `m`: compositions of `m` into `n` parts. -/
abbrev SGP (n m : ℕ) := {x : Fin n → Fin (m + 1) // ∑ j, (x j : ℕ) = m}

/-- `e_i` as an integer vector. -/
def evec (n : ℕ) (i : Fin n) : Fin n → ℤ := Pi.single i (1 : ℤ)

/-- The primitive direction `e_i - e_{i+1}`. -/
def sdir (n : ℕ) (i : Fin (n - 1)) : Fin n → ℤ :=
  evec n ⟨(i : ℕ), by have := i.isLt; omega⟩
    - evec n ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩

/-- Data of a small simplex of the Freudenthal triangulation. -/
abbrev SData (n m : ℕ) := SGP n m × Equiv.Perm (Fin (n - 1))

/-- The transfers already carried out by time `t`. -/
def doneSet {n : ℕ} (t : Fin n) : Finset (Fin (n - 1)) :=
  univ.filter (fun s => (s : ℕ) < (t : ℕ))

/-- The embedding of `Fin (n-1)` into `Fin n` as `t ↦ t+1`. -/
def succF {n : ℕ} (t : Fin (n - 1)) : Fin n := ⟨(t : ℕ) + 1, by have := t.isLt; omega⟩

/-- The embedding of `Fin (n-1)` into `Fin n` as `t ↦ t`. -/
def castF {n : ℕ} (t : Fin (n - 1)) : Fin n := ⟨(t : ℕ), by have := t.isLt; omega⟩

/-- The `t`-th vertex of a small simplex, as an integer vector. -/
def vt {n m : ℕ} (p : SData n m) (t : Fin n) : Fin n → ℤ :=
  fun j => (p.1.1 j : ℤ) + ∑ s ∈ doneSet t, sdir n (p.2 s) j

/-- The linear invariant `Σ_j (n-1-j) v_j`. -/
def Wv (n : ℕ) (v : Fin n → ℤ) : ℤ := ∑ j : Fin n, ((n : ℤ) - 1 - (j : ℤ)) * v j

lemma doneSet_card {n : ℕ} (t : Fin n) : (doneSet t).card = (t : ℕ) := by
  classical
  have htn : (t : ℕ) ≤ n - 1 := by have := t.isLt; omega
  rw [doneSet]
  refine (Finset.card_bij (s := univ.filter (fun s : Fin (n - 1) => (s : ℕ) < (t : ℕ)))
      (t := (univ : Finset (Fin (t : ℕ))))
      (fun (s : Fin (n - 1)) (hs : s ∈ univ.filter fun s : Fin (n-1) => (s : ℕ) < (t : ℕ)) =>
      (⟨(s : ℕ), (Finset.mem_filter.mp hs).2⟩ : Fin (t : ℕ))) ?_ ?_ ?_).trans ?_
  · intro s _; exact Finset.mem_univ _
  · intro s1 h1 s2 h2 he
    exact Fin.ext (by simpa using congrArg Fin.val he)
  · intro b _
    refine ⟨⟨(b : ℕ), by have := b.isLt; omega⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, b.isLt⟩
    · ext; simp
  · simp

lemma Wv_add {n : ℕ} (v w : Fin n → ℤ) :
    Wv n (fun j => v j + w j) = Wv n v + Wv n w := by
  simp only [Wv, mul_add, Finset.sum_add_distrib]

lemma Wv_sub {n : ℕ} (v w : Fin n → ℤ) :
    Wv n (fun j => v j - w j) = Wv n v - Wv n w := by
  simp only [Wv, mul_sub, Finset.sum_sub_distrib]

lemma Wv_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℤ) :
    Wv n (fun j => ∑ i ∈ s, f i j) = ∑ i ∈ s, Wv n (f i) := by
  simp only [Wv, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma Wv_evec {n : ℕ} (a : Fin n) : Wv n (evec n a) = (n : ℤ) - 1 - (a : ℤ) := by
  rw [Wv, evec, Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]; ring
  · intro j _ hj; rw [Pi.single_eq_of_ne hj]; ring
  · intro h; exact absurd (Finset.mem_univ a) h

lemma Wv_sdir {n : ℕ} (i : Fin (n - 1)) : Wv n (sdir n i) = 1 := by
  change Wv n (fun j => evec n ⟨(i : ℕ), by have := i.isLt; omega⟩ j
    - evec n ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩ j) = 1
  rw [Wv_sub, Wv_evec, Wv_evec]
  have h1 : ((⟨(i : ℕ), by have := i.isLt; omega⟩ : Fin n) : ℤ) = (i : ℤ) := by simp
  have h2 : ((⟨(i : ℕ) + 1, by have := i.isLt; omega⟩ : Fin n) : ℤ) = (i : ℤ) + 1 := by simp
  rw [h1, h2]; ring

lemma Wv_vt {n m : ℕ} (p : SData n m) (t : Fin n) :
    Wv n (vt p t) = Wv n (fun j => (p.1.1 j : ℤ)) + (t : ℤ) := by
  have hv : vt p t = fun j => (fun j => (p.1.1 j : ℤ)) j
      + (fun j => ∑ s ∈ doneSet t, sdir n (p.2 s) j) j := rfl
  rw [hv, Wv_add, Wv_sum]
  rw [Finset.sum_congr rfl (fun s _ => Wv_sdir (p.2 s))]
  simp [Finset.sum_const, doneSet_card]

lemma vt_injective {n m : ℕ} (p : SData n m) : Function.Injective (vt p) := by
  intro t t' h
  have h1 := congrArg (Wv n) h
  rw [Wv_vt, Wv_vt] at h1
  have : (t : ℤ) = (t' : ℤ) := by omega
  exact Fin.ext (by exact_mod_cast this)



/-! ## Vertices, validity and cells -/

variable {n m : ℕ}

lemma evec_sum (a : Fin n) : (∑ j : Fin n, evec n a j) = 1 := by
  rw [evec, Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro j _ hj; rw [Pi.single_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ a) h

lemma sdir_sum (i : Fin (n - 1)) : (∑ j : Fin n, sdir n i j) = 0 := by
  change (∑ j : Fin n, (evec n ⟨(i:ℕ), by have := i.isLt; omega⟩ j
    - evec n ⟨(i:ℕ)+1, by have := i.isLt; omega⟩ j)) = 0
  rw [Finset.sum_sub_distrib, evec_sum, evec_sum]; ring

/-- A small simplex is valid when all its vertices are nonnegative coordinatewise. -/
def SValid (p : SData n m) : Prop := ∀ t j, 0 ≤ vt p t j

lemma vt_sum (p : SData n m) (t : Fin n) : (∑ j : Fin n, vt p t j) = m := by
  have hbase : (∑ j : Fin n, (p.1.1 j : ℤ)) = (m : ℤ) := by
    rw [← Nat.cast_sum, p.1.2]
  have hstep : vt p t = fun j => (fun j => (p.1.1 j : ℤ)) j
      + (fun j => ∑ s ∈ doneSet t, sdir n (p.2 s) j) j := rfl
  rw [hstep, Finset.sum_add_distrib, hbase]
  rw [show (∑ j : Fin n, ∑ s ∈ doneSet t, sdir n (p.2 s) j)
      = ∑ s ∈ doneSet t, ∑ j : Fin n, sdir n (p.2 s) j from Finset.sum_comm]
  rw [Finset.sum_eq_zero (fun s _ => sdir_sum (p.2 s))]; ring

lemma vt_le_m (p : SData n m) (hp : SValid p) (t : Fin n) (j : Fin n) :
    vt p t j ≤ (m : ℤ) := by
  have h1 := vt_sum p t
  have h2 : vt p t j ≤ ∑ k : Fin n, vt p t k :=
    Finset.single_le_sum (fun k _ => hp t k) (Finset.mem_univ j)
  omega

/-- The `t`-th vertex as a grid point (for a valid small simplex). -/
def sVert (p : SData n m) (hp : SValid p) (t : Fin n) : SGP n m :=
  ⟨fun j => ⟨(vt p t j).toNat, by
      have h1 := vt_le_m p hp t j
      have h0 := hp t j
      have : (vt p t j).toNat ≤ m := by omega
      omega⟩, by
    have hcast : ((∑ j : Fin n, (vt p t j).toNat : ℕ) : ℤ) = (m : ℤ) := by
      push_cast
      rw [Finset.sum_congr rfl (fun j _ => Int.toNat_of_nonneg (hp t j))]
      exact vt_sum p t
    exact_mod_cast hcast⟩

lemma sVert_val (p : SData n m) (hp : SValid p) (t : Fin n) (j : Fin n) :
    ((sVert p hp t).1 j : ℤ) = vt p t j := by
  rw [sVert, Int.toNat_of_nonneg (hp t j)]

/-- The vertex set of a small simplex, as a finset of grid points. -/
def sCell (p : SData n m) (hp : SValid p) : Finset (SGP n m) :=
  (univ : Finset (Fin n)).image (sVert p hp)

lemma sCell_card (p : SData n m) (hp : SValid p) : (sCell p hp).card = n := by
  rw [sCell, Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
  intro t t' h
  apply vt_injective p
  funext j
  have := congrArg (fun x : SGP n m => ((x.1 j : Fin (m+1)) : ℤ)) h
  rwa [sVert_val, sVert_val] at this

lemma sdir_sum_zero {n : ℕ} (i : Fin (n - 1)) : (∑ j : Fin n, sdir n i j) = 0 := by
  change (∑ j : Fin n, (evec n ⟨(i:ℕ), by have := i.isLt; omega⟩ j
    - evec n ⟨(i:ℕ)+1, by have := i.isLt; omega⟩ j)) = 0
  rw [Finset.sum_sub_distrib, evec_sum, evec_sum]; ring

lemma doneSet_succ {n : ℕ} (t : Fin (n - 1)) :
    doneSet (succF t) = insert t (doneSet (castF t)) := by
  ext s
  simp only [doneSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  have hs : ((succF t : Fin n) : ℕ) = (t : ℕ) + 1 := rfl
  have hc : ((castF t : Fin n) : ℕ) = (t : ℕ) := rfl
  rw [hs, hc]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · exact Or.inr h'
    · exact Or.inl (Fin.ext h')
  · rintro (h | h)
    · rw [h]; omega
    · omega

lemma vt_succ {n m : ℕ} (p : SData n m) (t : Fin (n - 1)) :
    vt p (succF t) = fun j => vt p (castF t) j + sdir n (p.2 t) j := by
  funext j
  have hmem : t ∉ doneSet (castF t) := by
    rw [doneSet, Finset.mem_filter]
    rintro ⟨-, h⟩
    simp only [castF] at h
    omega
  simp only [vt, doneSet_succ, Finset.sum_insert hmem]
  ring

section Flip

variable (hn : 2 ≤ n)

/-- The permutation of the flipped small simplex. -/
def flipσ (p : SData n m) (s : Fin n) : Equiv.Perm (Fin (n - 1)) :=
  if h0 : (s : ℕ) = 0 then (finRotate (n - 1)).trans p.2
  else if hl : (s : ℕ) = n - 1 then (finRotate (n - 1)).symm.trans p.2
  else (Equiv.swap (⟨(s : ℕ) - 1, by omega⟩ : Fin (n - 1))
        (⟨(s : ℕ), by omega⟩ : Fin (n - 1))).trans p.2

/-- The base of the flipped small simplex, as an integer vector. -/
def flipBZ (p : SData n m) (s : Fin n) : Fin n → ℤ :=
  if h0 : (s : ℕ) = 0 then fun j => (p.1.1 j : ℤ) + sdir n (p.2 ⟨0, by omega⟩) j
  else if hl : (s : ℕ) = n - 1 then fun j => (p.1.1 j : ℤ) - sdir n (p.2 ⟨n - 2, by omega⟩) j
  else fun j => (p.1.1 j : ℤ)

lemma flipBZ_sum (p : SData n m) (s : Fin n) : (∑ j : Fin n, flipBZ hn p s j) = (m : ℤ) := by
  have hb : (∑ j : Fin n, (p.1.1 j : ℤ)) = (m : ℤ) := by rw [← Nat.cast_sum, p.1.2]
  unfold flipBZ
  split_ifs with h0 hl
  · rw [Finset.sum_add_distrib, hb, sdir_sum_zero]; ring
  · rw [Finset.sum_sub_distrib, hb, sdir_sum_zero]; ring
  · exact hb

/-- The flip is admissible when its base has nonnegative coordinates. -/
def flipOK (p : SData n m) (s : Fin n) : Prop := ∀ j, 0 ≤ flipBZ hn p s j

/-- The base of the flipped cell as a grid point. -/
def sFlipBase (p : SData n m) (s : Fin n) (h : flipOK hn p s) : SGP n m :=
  ⟨fun j => ⟨(flipBZ hn p s j).toNat, by
      have h0 := h j
      have hle : flipBZ hn p s j ≤ (m : ℤ) := by
        have := flipBZ_sum hn p s
        have := Finset.single_le_sum (f := fun j => flipBZ hn p s j) (fun j _ => h j) (Finset.mem_univ j)
        omega
      omega⟩, by
    have : ((∑ j : Fin n, (flipBZ hn p s j).toNat : ℕ) : ℤ) = (m : ℤ) := by
      push_cast
      rw [Finset.sum_congr rfl (fun j _ => Int.toNat_of_nonneg (h j))]
      exact flipBZ_sum hn p s
    exact_mod_cast this⟩

/-- The flipped cell. -/
def sFlip (p : SData n m) (s : Fin n) (h : flipOK hn p s) : SData n m :=
  (sFlipBase hn p s h, flipσ hn p s)

end Flip

lemma sdir_apply_eq_one {n : ℕ} (i : Fin (n-1)) (j : Fin n) :
    sdir n i j = 1 ↔ (j:ℕ) = (i:ℕ) := by
  rw [sdir]
  simp only [Pi.sub_apply, evec, Pi.single_apply]
  constructor
  · intro h
    by_contra hc
    have h1 : j ≠ (⟨(i:ℕ), by have := i.isLt; omega⟩ : Fin n) := fun hh => hc (by rw [hh])
    rw [if_neg h1] at h
    by_cases h2 : j = (⟨(i:ℕ)+1, by have := i.isLt; omega⟩ : Fin n)
    · rw [if_pos h2] at h; omega
    · rw [if_neg h2] at h; omega
  · intro h
    have h1 : j = (⟨(i:ℕ), by have := i.isLt; omega⟩ : Fin n) := Fin.ext h
    rw [if_pos h1]
    have h2 : ¬ (j = (⟨(i:ℕ)+1, by have := i.isLt; omega⟩ : Fin n)) := by
      intro hh; rw [hh] at h; simp at h
    rw [if_neg h2]; ring

lemma sdir_injective {n : ℕ} {i i' : Fin (n-1)} (h : sdir n i = sdir n i') : i = i' := by
  have h1 : sdir n i ⟨(i:ℕ), by have := i.isLt; omega⟩ = 1 := (sdir_apply_eq_one i _).mpr rfl
  have h2 : sdir n i' ⟨(i:ℕ), by have := i.isLt; omega⟩ = 1 := by rw [← h]; exact h1
  have := (sdir_apply_eq_one i' _).mp h2
  exact Fin.ext this

lemma perm_eq_or_swap {α : Type*} [Fintype α] [DecidableEq α] (σ τ : Equiv.Perm α) {A B : α}
    (hAB : A ≠ B)
    (h : ∀ t, t ≠ A → t ≠ B → σ t = τ t) :
    τ = σ ∨ τ = (Equiv.swap A B).trans σ := by
  have keyA : τ A ∈ ({σ A, σ B} : Finset α) := by
    obtain ⟨y, hy⟩ := σ.surjective (τ A)
    by_cases hyA : y = A
    · rw [Finset.mem_insert]; left; rw [← hy, hyA]
    · by_cases hyB : y = B
      · rw [Finset.mem_insert]; right; rw [Finset.mem_singleton]; rw [← hy, hyB]
      · have h1 : σ y = τ y := h y hyA hyB
        rw [hy] at h1
        exact absurd (τ.injective h1).symm hyA
  have keyB : τ B ∈ ({σ A, σ B} : Finset α) := by
    obtain ⟨y, hy⟩ := σ.surjective (τ B)
    by_cases hyA : y = A
    · rw [Finset.mem_insert]; left; rw [← hy, hyA]
    · by_cases hyB : y = B
      · rw [Finset.mem_insert]; right; rw [Finset.mem_singleton]; rw [← hy, hyB]
      · have h1 : σ y = τ y := h y hyA hyB
        rw [hy] at h1
        exact absurd (τ.injective h1).symm hyB
  rw [Finset.mem_insert, Finset.mem_singleton] at keyA keyB
  by_cases hA : τ A = σ A
  · left
    apply Equiv.ext; intro t
    by_cases htA : t = A
    · rw [htA, hA]
    · by_cases htB : t = B
      · subst htB
        rcases keyB with hh | hh
        · exact absurd (τ.injective (hA.trans hh.symm)) hAB
        · exact hh
      · exact (h t htA htB).symm
  · have hA' : τ A = σ B := by
      rcases keyA with hh | hh
      · exact absurd hh hA
      · exact hh
    right
    apply Equiv.ext; intro t
    by_cases htA : t = A
    · subst htA
      rw [Equiv.trans_apply, Equiv.swap_apply_left, hA']
    · by_cases htB : t = B
      · subst htB
        rw [Equiv.trans_apply, Equiv.swap_apply_right]
        rcases keyB with hh | hh
        · exact hh
        · exact absurd (τ.injective (hA'.trans hh.symm)) hAB
      · rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne htA htB]
        exact (h t htA htB).symm

lemma doneSet_zero {n : ℕ} (hn : 0 < n) : doneSet (⟨0, hn⟩ : Fin n) = ∅ := by
  rw [doneSet]; simp

lemma vt_zero {n m : ℕ} (hn : 0 < n) (p : SData n m) :
    vt p ⟨0, hn⟩ = fun j => (p.1.1 j : ℤ) := by
  funext j; rw [vt, doneSet_zero hn, Finset.sum_empty]; ring

lemma eq_base_of_vt_zero {n m : ℕ} (hn : 0 < n) {p q : SData n m}
    (h : vt p ⟨0, hn⟩ = vt q ⟨0, hn⟩) : p.1 = q.1 := by
  apply Subtype.ext; funext j
  have hh := congrFun h j
  rw [vt_zero hn p, vt_zero hn q] at hh
  simp only at hh
  exact Fin.ext (by exact_mod_cast hh)

lemma sdir_eq_vt_sub {n m : ℕ} (p : SData n m) (t : Fin (n-1)) :
    sdir n (p.2 t) = fun j => vt p (succF t) j - vt p (castF t) j := by
  funext j
  have h : vt p (succF t) j = vt p (castF t) j + sdir n (p.2 t) j := congrFun (vt_succ p t) j
  omega

lemma recon_mid {n m : ℕ} (hn : 0 < n) (p q : SData n m) (s : Fin n)
    (hs0 : (s:ℕ) ≠ 0) (hsn : (s:ℕ) ≠ n-1)
    (H : ∀ t : Fin n, t ≠ s → vt q t = vt p t) :
    q.1 = p.1 ∧ (q.2 = p.2 ∨
      q.2 = (Equiv.swap (⟨(s:ℕ)-1, by omega⟩ : Fin (n-1))
        (⟨(s:ℕ), by omega⟩ : Fin (n-1))).trans p.2) := by
  have hA : (⟨(s:ℕ)-1, by omega⟩ : Fin (n-1)) ≠ (⟨(s:ℕ), by omega⟩ : Fin (n-1)) := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  refine ⟨?_, ?_⟩
  · have h0 : (⟨0, hn⟩ : Fin n) ≠ s := fun h => hs0 (by rw [← h])
    exact eq_base_of_vt_zero hn (by rw [H ⟨0, hn⟩ h0])
  · apply perm_eq_or_swap (p.2) (q.2) hA
    intro t htA htB
    have hsucc : succF t ≠ s := by
      intro hh
      apply htA
      apply Fin.ext
      have := congrArg Fin.val hh
      simp only [succF] at this
      simp only
      omega
    have hcast : castF t ≠ s := by
      intro hh
      apply htB
      apply Fin.ext
      have := congrArg Fin.val hh
      simp only [castF] at this
      simp only
      exact this
    have h1 : sdir n (q.2 t) = sdir n (p.2 t) := by
      rw [sdir_eq_vt_sub (p := q) t, sdir_eq_vt_sub (p := p) t]
      funext j
      rw [H (succF t) hsucc, H (castF t) hcast]
    exact (sdir_injective h1).symm

lemma perm_eq_of_agree_off_single {α : Type*} [Fintype α] [DecidableEq α]
    (σ τ : Equiv.Perm α) (a : α) (h : ∀ t, t ≠ a → σ t = τ t) : σ = τ := by
  apply Equiv.ext; intro t
  by_cases ht : t = a
  · rw [ht]
    obtain ⟨y, hy⟩ := τ.surjective (σ a)
    by_cases hya : y = a
    · rw [hya] at hy; exact hy.symm
    · exact absurd (σ.injective (by rw [← hy]; exact (h y hya).symm)).symm hya
  · exact h t ht

lemma recon_shift (p q : SData n m) (s : Fin n)
    (H : ∀ t : Fin n, t ≠ s → ∃ t', vt q t' = vt p t) :
    ∃ δ : ℤ, ∀ t : Fin n, t ≠ s → ∃ t' : Fin n,
      ((t':ℤ) = δ + (t:ℤ) ∧ vt q t' = vt p t) := by
  refine ⟨Wv n (fun j => (p.1.1 j : ℤ)) - Wv n (fun j => (q.1.1 j : ℤ)), ?_⟩
  intro t ht
  obtain ⟨t', htv⟩ := H t ht
  refine ⟨t', ?_, htv⟩
  have h1 := congrArg (Wv n) htv
  rw [Wv_vt, Wv_vt] at h1
  omega

lemma vt_one {n m : ℕ} (hn : 2 ≤ n) (p : SData n m) :
    vt p ⟨1, by omega⟩ = fun j => vt p ⟨0, by omega⟩ j + sdir n (p.2 ⟨0, by omega⟩) j := by
  have h := vt_succ p (⟨0, by omega⟩ : Fin (n-1))
  rwa [show succF (⟨0, by omega⟩ : Fin (n-1)) = (⟨1, by omega⟩ : Fin n) from rfl,
       show castF (⟨0, by omega⟩ : Fin (n-1)) = (⟨0, by omega⟩ : Fin n) from rfl] at h

lemma flipσ_zero {n m : ℕ} (hn : 2 ≤ n) (p : SData n m) (s : Fin n) (h0 : (s:ℕ) = 0) :
    flipσ hn p s = (finRotate (n-1)).trans p.2 := by
  unfold flipσ; rw [dif_pos h0]

lemma flipσ_last {n m : ℕ} (hn : 2 ≤ n) (p : SData n m) (s : Fin n) (h0 : (s:ℕ) ≠ 0)
    (hl : (s:ℕ) = n-1) : flipσ hn p s = (finRotate (n-1)).symm.trans p.2 := by
  unfold flipσ; rw [dif_neg h0, dif_pos hl]

lemma flipσ_mid {n m : ℕ} (hn : 2 ≤ n) (p : SData n m) (s : Fin n) (h0 : (s:ℕ) ≠ 0)
    (hl : (s:ℕ) ≠ n-1) :
    flipσ hn p s = (Equiv.swap (⟨(s:ℕ)-1, by omega⟩ : Fin (n-1))
        (⟨(s:ℕ), by omega⟩ : Fin (n-1))).trans p.2 := by
  unfold flipσ; rw [dif_neg h0, dif_neg hl]

lemma flipBZ_zero {n m : ℕ} (hn : 2 ≤ n) (p : SData n m) (s : Fin n) (h0 : (s:ℕ) = 0) :
    flipBZ hn p s = fun j => (p.1.1 j : ℤ) + sdir n (p.2 ⟨0, by omega⟩) j := by
  unfold flipBZ; rw [dif_pos h0]

lemma flipBZ_last {n m : ℕ} (hn : 2 ≤ n) (p : SData n m) (s : Fin n) (h0 : (s:ℕ) ≠ 0)
    (hl : (s:ℕ) = n-1) :
    flipBZ hn p s = fun j => (p.1.1 j : ℤ) - sdir n (p.2 ⟨n-2, by omega⟩) j := by
  unfold flipBZ; rw [dif_neg h0, dif_pos hl]

lemma flipBZ_mid {n m : ℕ} (hn : 2 ≤ n) (p : SData n m) (s : Fin n) (h0 : (s:ℕ) ≠ 0)
    (hl : (s:ℕ) ≠ n-1) : flipBZ hn p s = fun j => (p.1.1 j : ℤ) := by
  unfold flipBZ; rw [dif_neg h0, dif_neg hl]

lemma sFlip_snd {n m : ℕ} (hn : 2 ≤ n) (p : SData n m) (s : Fin n) (h : flipOK hn p s) :
    (sFlip hn p s h).2 = flipσ hn p s := rfl

lemma sFlipBase_val {n m : ℕ} (hn : 2 ≤ n) (p : SData n m) (s : Fin n)
    (h : flipOK hn p s) (j : Fin n) :
    ((sFlip hn p s h).1.1 j : ℕ) = (flipBZ hn p s j).toNat := rfl

lemma sFlipBase_cast {n m : ℕ} (hn : 2 ≤ n) (p : SData n m) (s : Fin n)
    (h : flipOK hn p s) (j : Fin n) :
    ((sFlip hn p s h).1.1 j : ℤ) = flipBZ hn p s j := by
  rw [show ((sFlip hn p s h).1.1 j : ℤ) = (((sFlip hn p s h).1.1 j : ℕ) : ℤ) from rfl,
      sFlipBase_val hn p s h j, Int.toNat_of_nonneg (h j)]

lemma vt_zero_apply {n m : ℕ} (hn : 0 < n) (p : SData n m) (j : Fin n) :
    vt p ⟨0, hn⟩ j = (p.1.1 j : ℤ) := by
  rw [vt, doneSet_zero hn, Finset.sum_empty]; ring

lemma vt_one_apply {n m : ℕ} (hn : 2 ≤ n) (p : SData n m) (j : Fin n) :
    vt p ⟨1, by omega⟩ j = vt p ⟨0, by omega⟩ j + sdir n (p.2 ⟨0, by omega⟩) j := by
  have h := congrFun (vt_succ p (⟨0, by omega⟩ : Fin (n-1))) j
  rwa [show succF (⟨0, by omega⟩ : Fin (n-1)) = (⟨1, by omega⟩ : Fin n) from rfl,
       show castF (⟨0, by omega⟩ : Fin (n-1)) = (⟨0, by omega⟩ : Fin n) from rfl] at h

lemma recon_s0_same {n m : ℕ} (hn : 2 ≤ n) (p q : SData n m)
    (H : ∀ t : Fin n, t ≠ (⟨0, by omega⟩ : Fin n) → vt q t = vt p t) : q = p := by
  have hσ : q.2 = p.2 := by
    apply perm_eq_of_agree_off_single _ (a := (⟨0, by omega⟩ : Fin (n-1)))
    intro t ht
    have hsucc : succF t ≠ (⟨0, by omega⟩ : Fin n) := by
      intro hh; apply ht; apply Fin.ext
      have := congrArg Fin.val hh; simp only [succF] at this; simp only; omega
    have hcast : castF t ≠ (⟨0, by omega⟩ : Fin n) := by
      intro hh; apply ht; apply Fin.ext
      have := congrArg Fin.val hh; simp only [castF] at this; simp only; exact this
    have h1 : sdir n (q.2 t) = sdir n (p.2 t) := by
      rw [sdir_eq_vt_sub (p := q) t, sdir_eq_vt_sub (p := p) t]
      funext j; rw [H (succF t) hsucc, H (castF t) hcast]
    exact sdir_injective h1
  have hbase : q.1 = p.1 := by
    have hne1 : (⟨1, by omega⟩ : Fin n) ≠ (⟨0, by omega⟩ : Fin n) := by
      intro hh; have := congrArg Fin.val hh; simp at this
    have h1 : vt q ⟨1, by omega⟩ = vt p ⟨1, by omega⟩ := H _ hne1
    apply Subtype.ext; funext j
    have h2 := congrFun h1 j
    rw [vt_one_apply hn q j, vt_one_apply hn p j, vt_zero_apply (by omega) q,
        vt_zero_apply (by omega) p] at h2
    have h3 : q.2 ⟨0, by omega⟩ = p.2 ⟨0, by omega⟩ := by rw [hσ]
    rw [h3] at h2
    exact Fin.ext (by omega)
  exact Prod.ext hbase hσ

lemma recon_last_same {n m : ℕ} (hn : 2 ≤ n) (p q : SData n m)
    (H : ∀ t : Fin n, t ≠ (⟨n-1, by omega⟩ : Fin n) → vt q t = vt p t) : q = p := by
  have hσ : q.2 = p.2 := by
    apply perm_eq_of_agree_off_single _ (a := (⟨n-2, by omega⟩ : Fin (n-1)))
    intro t ht
    have hsucc : succF t ≠ (⟨n-1, by omega⟩ : Fin n) := by
      intro hh; apply ht; apply Fin.ext
      have := congrArg Fin.val hh; simp only [succF] at this; simp only; omega
    have hcast : castF t ≠ (⟨n-1, by omega⟩ : Fin n) := by
      intro hh; apply ht; apply Fin.ext
      have := congrArg Fin.val hh; simp only [castF] at this; simp only; omega
    have h1 : sdir n (q.2 t) = sdir n (p.2 t) := by
      rw [sdir_eq_vt_sub (p := q) t, sdir_eq_vt_sub (p := p) t]
      funext j; rw [H (succF t) hsucc, H (castF t) hcast]
    exact sdir_injective h1
  have hbase : q.1 = p.1 := by
    have hne0 : (⟨0, by omega⟩ : Fin n) ≠ (⟨n-1, by omega⟩ : Fin n) := by
      intro hh; have := congrArg Fin.val hh; simp at this; omega
    have h1 : vt q ⟨0, by omega⟩ = vt p ⟨0, by omega⟩ := H _ hne0
    exact eq_base_of_vt_zero (by omega) h1
  exact Prod.ext hbase hσ

lemma succF_eq {n : ℕ} (s : Fin (n-1)) : succF s = (⟨(s:ℕ)+1, by have := s.isLt; omega⟩ : Fin n) := rfl
lemma castF_eq {n : ℕ} (s : Fin (n-1)) : castF s = (⟨(s:ℕ), by have := s.isLt; omega⟩ : Fin n) := rfl

lemma fRA {N : ℕ} (hN : 1 ≤ N) (k : Fin N) (hk : (k:ℕ)+1 < N) :
    (finRotate N) k = (⟨(k:ℕ)+1, hk⟩ : Fin N) := by
  have hN2 : 2 ≤ N := by omega
  haveI : NeZero N := ⟨by omega⟩
  rw [finRotate_apply]; apply Fin.ext
  simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < N)]
  rw [Nat.mod_eq_of_lt hk]
lemma fRB {N : ℕ} (hN : 1 ≤ N) (k : Fin N) (hk : (k:ℕ)+1 = N) :
    (finRotate N) k = (⟨0, by omega⟩ : Fin N) := by
  by_cases h1 : N = 1
  · subst h1
    exact Subsingleton.elim _ _
  · have hN2 : 2 ≤ N := by omega
    haveI : NeZero N := ⟨by omega⟩
    rw [finRotate_apply]; apply Fin.ext
    simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < N)]
    rw [hk, Nat.mod_self]
lemma fRC {N : ℕ} (hN : 1 ≤ N) (k : Fin N) (hk : 0 < (k:ℕ)) :
    (finRotate N).symm k = (⟨(k:ℕ)-1, by omega⟩ : Fin N) := by
  have hklt : (k:ℕ) < N := k.isLt
  have hmlt : (k:ℕ)-1 < N := by omega
  have hb : ((k:ℕ)-1)+1 < N := by omega
  have h1 : (finRotate N) (⟨(k:ℕ)-1, hmlt⟩ : Fin N) = k := by
    rw [fRA hN (⟨(k:ℕ)-1, hmlt⟩ : Fin N) hb]
    apply Fin.ext; simp only [Fin.val_mk]; omega
  have h2 : (finRotate N).symm (finRotate N ⟨(k:ℕ)-1, hmlt⟩) = (⟨(k:ℕ)-1, hmlt⟩ : Fin N) :=
    Equiv.symm_apply_apply _ _
  rwa [h1] at h2
lemma fRD {N : ℕ} (hN : 1 ≤ N) (k : Fin N) (hk : (k:ℕ) = 0) :
    (finRotate N).symm k = (⟨N-1, by omega⟩ : Fin N) := by
  have hlt : N-1 < N := by omega
  have hb : ((N-1:ℕ))+1 = N := by omega
  have h1 : (finRotate N) (⟨N-1, hlt⟩ : Fin N) = k := by
    rw [fRB hN (⟨N-1, hlt⟩ : Fin N) (by simp only [Fin.val_mk]; exact hb)]
    apply Fin.ext; simp only [Fin.val_mk, Fin.val_zero]; omega
  have h2 : (finRotate N).symm (finRotate N ⟨N-1, hlt⟩) = (⟨N-1, hlt⟩ : Fin N) :=
    Equiv.symm_apply_apply _ _
  rwa [h1] at h2
lemma recon_down {n m : ℕ} (hn : 2 ≤ n) (p q : SData n m)
    (H : ∀ u : Fin (n-1), vt q (castF u) = vt p (succF u)) :
    ∃ h : flipOK hn p (⟨0, by omega⟩ : Fin n), q = sFlip hn p (⟨0, by omega⟩ : Fin n) h := by
  have hagree : ∀ u : Fin (n-1), (hu : (u:ℕ)+1 < n-1) →
      q.2 u = p.2 ⟨(u:ℕ)+1, hu⟩ := by
    intro u hu
    have h1 : sdir n (q.2 u) = sdir n (p.2 ⟨(u:ℕ)+1, hu⟩) := by
      rw [sdir_eq_vt_sub (p := q) u, sdir_eq_vt_sub (p := p) ⟨(u:ℕ)+1, hu⟩]
      simp only [succF_eq, castF_eq]
      funext j
      have hA := congrFun (H u) j
      have hB := congrFun (H ⟨(u:ℕ)+1, hu⟩) j
      simp only [succF_eq, castF_eq] at hA hB
      rw [hA, hB]
    exact sdir_injective h1
  have hσ : q.2 = (finRotate (n-1)).trans p.2 := by
    apply perm_eq_of_agree_off_single _ (a := (⟨n-2, by omega⟩ : Fin (n-1)))
    intro t ht
    rw [Equiv.trans_apply]
    have htlt : (t:ℕ) < n-1 := t.isLt
    have ht' : (t:ℕ) + 1 < n-1 := by
      by_contra hc
      have h2 : (t:ℕ) + 1 = n-1 := by omega
      exact ht (Fin.ext (by simp only [Fin.val_mk]; omega))
    have h2N : 1 ≤ n-1 := by omega
    rw [fRA h2N t ht', hagree t ht']
  have hbq : ∀ j, flipBZ hn p (⟨0, by omega⟩ : Fin n) j = (q.1.1 j : ℤ) := by
    intro j
    rw [flipBZ_zero hn p _ rfl]
    show (p.1.1 j : ℤ) + sdir n (p.2 ⟨0, by omega⟩) j = (q.1.1 j : ℤ)
    have h1 := congrFun (H (⟨0, by omega⟩ : Fin (n-1))) j
    simp only [succF_eq, castF_eq] at h1
    rw [vt_zero_apply (by omega) q, vt_one_apply hn p, vt_zero_apply (by omega) p] at h1
    omega
  have hOK : flipOK hn p (⟨0, by omega⟩ : Fin n) := by
    intro j; rw [hbq j]; exact Int.natCast_nonneg _
  refine ⟨hOK, ?_⟩
  refine Prod.ext ?_ ?_
  · apply Subtype.ext; funext j; apply Fin.ext
    rw [sFlipBase_val, hbq j, Int.toNat_natCast]
  · rw [sFlip_snd, flipσ_zero hn p _ rfl]; exact hσ

lemma recon_up {n m : ℕ} (hn : 2 ≤ n) (p q : SData n m)
    (H : ∀ u : Fin (n-1), vt q (succF u) = vt p (castF u)) :
    ∃ h : flipOK hn p (⟨n-1, by omega⟩ : Fin n), q = sFlip hn p (⟨n-1, by omega⟩ : Fin n) h := by
  have hagree : ∀ u : Fin (n-1), (hu : 0 < (u:ℕ)) → q.2 u = p.2 ⟨(u:ℕ)-1, by omega⟩ := by
    intro u hu
    have h1 : sdir n (q.2 u) = sdir n (p.2 ⟨(u:ℕ)-1, by omega⟩) := by
      rw [sdir_eq_vt_sub (p := q) u, sdir_eq_vt_sub (p := p) ⟨(u:ℕ)-1, by omega⟩]
      simp only [succF_eq, castF_eq]
      funext j
      have hnorm : (⟨(u:ℕ)-1+1, by have := u.isLt; omega⟩ : Fin n)
          = (⟨(u:ℕ), by have := u.isLt; omega⟩ : Fin n) :=
        Fin.ext (by simp only [Fin.val_mk]; omega)
      rw [hnorm]
      have hA := congrFun (H u) j
      have hB := congrFun (H ⟨(u:ℕ)-1, by omega⟩) j
      simp only [succF_eq, castF_eq] at hA hB
      rw [hnorm] at hB
      rw [hA, hB]
    exact sdir_injective h1
  have hσ : q.2 = (finRotate (n-1)).symm.trans p.2 := by
    apply perm_eq_of_agree_off_single _ (a := (⟨0, by omega⟩ : Fin (n-1)))
    intro t ht
    rw [Equiv.trans_apply]
    have htlt : (t:ℕ) < n-1 := t.isLt
    have ht' : 0 < (t:ℕ) := by
      by_contra hc
      exact ht (Fin.ext (by simp only [Fin.val_zero]; omega))
    have h2N : 1 ≤ n-1 := by omega
    rw [fRC h2N t ht', hagree t ht']
  have hbq : ∀ j, flipBZ hn p (⟨n-1, by omega⟩ : Fin n) j = (q.1.1 j : ℤ) := by
    intro j
    rw [flipBZ_last hn p _ (by simp only [Fin.val_mk]; omega) rfl]
    show (p.1.1 j : ℤ) - sdir n (p.2 ⟨n-2, by omega⟩) j = (q.1.1 j : ℤ)
    have h1 := congrFun (H (⟨0, by omega⟩ : Fin (n-1))) j
    simp only [succF_eq, castF_eq] at h1
    rw [vt_one_apply hn q, vt_zero_apply (by omega) q, vt_zero_apply (by omega) p] at h1
    have h3 : q.2 (⟨0, by omega⟩ : Fin (n-1)) = p.2 ⟨n-2, by omega⟩ := by
      have hh := congrArg (fun e => e ⟨0, by omega⟩) hσ
      rw [Equiv.trans_apply, fRD (by omega : 1 ≤ n-1) _ rfl] at hh
      exact hh
    rw [h3] at h1
    omega
  have hOK : flipOK hn p (⟨n-1, by omega⟩ : Fin n) := by
    intro j; rw [hbq j]; exact Int.natCast_nonneg _
  refine ⟨hOK, ?_⟩
  refine Prod.ext ?_ ?_
  · apply Subtype.ext; funext j; apply Fin.ext
    rw [sFlipBase_val, hbq j, Int.toNat_natCast]
  · rw [sFlip_snd, flipσ_last hn p _ (by simp only [Fin.val_mk]; omega) rfl]; exact hσ

abbrev lastF {N : ℕ} (hN : 0 < N) : Fin N := ⟨N-1, Nat.sub_lt hN (by omega)⟩
abbrev oneF {N : ℕ} (hN : 1 < N) : Fin N := ⟨1, hN⟩
abbrev zeroF {N : ℕ} (hN : 0 < N) : Fin N := ⟨0, hN⟩
abbrev prevF {N : ℕ} (hN : 1 < N) : Fin N := ⟨N-2, by omega⟩

@[simp] lemma lastF_val {N : ℕ} (hN : 0 < N) : (lastF hN : ℕ) = N-1 := rfl
@[simp] lemma oneF_val {N : ℕ} (hN : 1 < N) : (oneF hN : ℕ) = 1 := rfl
@[simp] lemma zeroF_val {N : ℕ} (hN : 0 < N) : (zeroF hN : ℕ) = 0 := rfl
@[simp] lemma prevF_val {N : ℕ} (hN : 1 < N) : (prevF hN : ℕ) = N-2 := rfl

lemma lastZ {n : ℕ} (h : n-1 < n) : (((⟨n-1, h⟩ : Fin n)) : ℤ) = (n:ℤ) - 1 := by
  rw [show (((⟨n-1, h⟩ : Fin n)) : ℤ) = ((n-1 : ℕ) : ℤ) from rfl, Nat.cast_sub (by omega : 1 ≤ n)]
  ring
lemma prevZ {n : ℕ} (hn : 2 ≤ n) (h : n-2 < n) : (((⟨n-2, h⟩ : Fin n)) : ℤ) = (n:ℤ) - 2 := by
  rw [show (((⟨n-2, h⟩ : Fin n)) : ℤ) = ((n-2 : ℕ) : ℤ) from rfl, Nat.cast_sub hn]
  ring
lemma zeroZ {n : ℕ} (h : 0 < n) : (((⟨0, h⟩ : Fin n)) : ℤ) = 0 := rfl
lemma oneZ {n : ℕ} (h : 1 < n) : (((⟨1, h⟩ : Fin n)) : ℤ) = 1 := rfl

lemma shiftElim {n m : ℕ} {p q : SData n m} {s : Fin n} {δ : ℤ}
    (Hδ : ∀ t : Fin n, t ≠ s → ∃ t' : Fin n, ((t':ℤ) = δ + (t:ℤ) ∧ vt q t' = vt p t))
    (t : Fin n) (ht : t ≠ s) : ∃ t' : Fin n, ((t':ℤ) = δ + (t:ℤ) ∧ vt q t' = vt p t) :=
  Hδ t ht

lemma fin_cast_le {N : ℕ} (a : Fin N) : ((a : ℤ)) ≤ (N : ℤ) - 1 := by
  have h := a.isLt
  have h2 : ((a : ℤ)) = ((a : ℕ) : ℤ) := rfl
  omega

lemma fin_cast_nonneg {N : ℕ} (a : Fin N) : (0 : ℤ) ≤ ((a : ℤ)) :=
  Int.natCast_nonneg _

lemma fin_ne_of_val_ne {N : ℕ} {a b : Fin N} (h : (a : ℕ) ≠ (b : ℕ)) : a ≠ b :=
  fun hh => h (congrArg Fin.val hh)

lemma castF_cast {n : ℕ} (u : Fin (n - 1)) : ((castF u : Fin n) : ℤ) = (u : ℤ) := rfl
lemma succF_cast {n : ℕ} (u : Fin (n - 1)) : ((succF u : Fin n) : ℤ) = (u : ℤ) + 1 := rfl
lemma castF_val {n : ℕ} (u : Fin (n - 1)) : ((castF u : Fin n) : ℕ) = (u : ℕ) := rfl
lemma succF_val {n : ℕ} (u : Fin (n - 1)) : ((succF u : Fin n) : ℕ) = (u : ℕ) + 1 := rfl

lemma recon {n m : ℕ} (hn : 2 ≤ n) (p q : SData n m) (s : Fin n)
    (H : ∀ t : Fin n, t ≠ s → ∃ t', vt q t' = vt p t) :
    q = p ∨ ∃ (h : flipOK hn p s), q = sFlip hn p s h := by
  classical
  obtain ⟨δ, Hδ⟩ := recon_shift p q s H
  have hN0 : 0 < n := by omega
  have hN1 : 1 < n := by omega
  rcases Nat.eq_zero_or_pos (s : ℕ) with hs0 | hspos
  · -- s = 0
    have hseq : s = (⟨0, hN0⟩ : Fin n) := Fin.ext (by simpa using hs0)
    subst hseq
    have hle : δ ≤ 0 := by
      obtain ⟨t', ht', _⟩ := Hδ (⟨n - 1, Nat.sub_lt hN0 Nat.one_pos⟩ : Fin n)
        (fin_ne_of_val_ne (by simp only [Fin.val_mk]; omega))
      have h1 : ((t' : ℤ)) = δ + ((n : ℤ) - 1) :=
        ht'.trans (congrArg (fun x => δ + x) (lastZ (Nat.sub_lt hN0 Nat.one_pos)))
      have h2 := fin_cast_le t'; omega
    have hge : -1 ≤ δ := by
      obtain ⟨t', ht', _⟩ := Hδ (⟨1, hN1⟩ : Fin n)
        (fin_ne_of_val_ne (by simp only [Fin.val_mk]; omega))
      have h1 : ((t' : ℤ)) = δ + 1 :=
        ht'.trans (congrArg (fun x => δ + x) (oneZ hN1))
      have h2 := fin_cast_nonneg t'; omega
    rcases eq_or_lt_of_le hge with hδ | hδ
    · -- δ = -1
      have hδm : δ = -1 := hδ.symm
      refine Or.inr (recon_down hn p q ?_)
      intro u
      have htne : succF u ≠ (⟨0, hN0⟩ : Fin n) := by
        apply fin_ne_of_val_ne; simp only [succF_val, Fin.val_mk]; omega
      obtain ⟨t', ht', hv⟩ := Hδ (succF u) htne
      have h1 : ((t' : ℤ)) = δ + ((u : ℤ) + 1) :=
        ht'.trans (congrArg (fun x => δ + x) (succF_cast u))
      have h2 : ((t' : ℤ)) = (u : ℤ) := by rw [h1, hδm]; ring
      have h3 : (t' : ℕ) = (u : ℕ) := by omega
      have h4 : t' = castF u := Fin.ext (by simpa only [castF_val] using h3)
      rw [h4] at hv; exact hv
    · have hδ0 : δ = 0 := by omega
      refine Or.inl (recon_s0_same hn p q ?_)
      intro t ht
      obtain ⟨t', ht', hv⟩ := Hδ t ht
      have h1 : ((t' : ℤ)) = ((t : ℤ)) := by rw [ht', hδ0]; ring
      have h2 : (t' : ℕ) = (t : ℕ) := by omega
      have h3 : t' = t := Fin.ext h2
      rw [h3] at hv; exact hv
  · -- 0 < s
    by_cases hsn : (s : ℕ) = n - 1
    · -- s = n-1
      have hseq : s = (⟨n - 1, Nat.sub_lt hN0 Nat.one_pos⟩ : Fin n) := Fin.ext (by simpa using hsn)
      subst hseq
      have hge : 0 ≤ δ := by
        obtain ⟨t', ht', _⟩ := Hδ (⟨0, hN0⟩ : Fin n)
          (fin_ne_of_val_ne (by simp only [Fin.val_mk]; omega))
        have h1 : ((t' : ℤ)) = δ + 0 :=
          ht'.trans (congrArg (fun x => δ + x) (zeroZ hN0))
        have h2 := fin_cast_nonneg t'; omega
      have hle : δ ≤ 1 := by
        obtain ⟨t', ht', _⟩ := Hδ (⟨n - 2, by omega⟩ : Fin n)
          (fin_ne_of_val_ne (by simp only [Fin.val_mk]; omega))
        have h1 : ((t' : ℤ)) = δ + ((n : ℤ) - 2) :=
          ht'.trans (congrArg (fun x => δ + x) (prevZ hn (by omega)))
        have h2 := fin_cast_le t'; omega
      rcases eq_or_lt_of_le hge with hδ | hδ
      · -- δ = 0
        have hδ0 : δ = 0 := hδ.symm
        refine Or.inl (recon_last_same hn p q ?_)
        intro t ht
        obtain ⟨t', ht', hv⟩ := Hδ t ht
        have h1 : ((t' : ℤ)) = ((t : ℤ)) := by rw [ht', hδ0]; ring
        have h2 : (t' : ℕ) = (t : ℕ) := by omega
        have h3 : t' = t := Fin.ext h2
        rw [h3] at hv; exact hv
      · have hδ1 : δ = 1 := by omega
        refine Or.inr (recon_up hn p q ?_)
        intro u
        have htne : castF u ≠ (⟨n - 1, Nat.sub_lt hN0 Nat.one_pos⟩ : Fin n) := by
          apply fin_ne_of_val_ne; simp only [castF_val, Fin.val_mk]; omega
        obtain ⟨t', ht', hv⟩ := Hδ (castF u) htne
        have h1 : ((t' : ℤ)) = δ + (u : ℤ) :=
          ht'.trans (congrArg (fun x => δ + x) (castF_cast u))
        have h2 : ((t' : ℤ)) = (u : ℤ) + 1 := by rw [h1, hδ1]; ring
        have h3 : (t' : ℕ) = (u : ℕ) + 1 := by omega
        have h4 : t' = succF u := Fin.ext (by simpa only [succF_val] using h3)
        rw [h4] at hv; exact hv
    · -- middle
      have hs0' : (s : ℕ) ≠ 0 := by omega
      have hge : 0 ≤ δ := by
        obtain ⟨t', ht', _⟩ := Hδ (⟨0, hN0⟩ : Fin n)
          (fin_ne_of_val_ne (by simp only [Fin.val_mk]; omega))
        have h1 : ((t' : ℤ)) = δ + 0 := ht'.trans (congrArg (fun x => δ + x) (zeroZ hN0))
        have h2 := fin_cast_nonneg t'; omega
      have hle : δ ≤ 0 := by
        obtain ⟨t', ht', _⟩ := Hδ (⟨n - 1, Nat.sub_lt hN0 Nat.one_pos⟩ : Fin n)
          (fin_ne_of_val_ne (by simp only [Fin.val_mk]; omega))
        have h1 : ((t' : ℤ)) = δ + ((n : ℤ) - 1) :=
          ht'.trans (congrArg (fun x => δ + x) (lastZ (Nat.sub_lt hN0 Nat.one_pos)))
        have h2 := fin_cast_le t'; omega
      have hδ0 : δ = 0 := by omega
      have hH' : ∀ t : Fin n, t ≠ s → vt q t = vt p t := by
        intro t ht
        obtain ⟨t', ht', hv⟩ := Hδ t ht
        have h1 : ((t' : ℤ)) = ((t : ℤ)) := by rw [ht', hδ0]; ring
        have h2 : (t' : ℕ) = (t : ℕ) := by omega
        have h3 : t' = t := Fin.ext h2
        rw [h3] at hv; exact hv
      rcases recon_mid hN0 p q s hs0' hsn hH' with ⟨hb, hσ | hσ⟩
      · exact Or.inl (Prod.ext hb hσ)
      · have hOK : flipOK hn p s := by
          intro j; rw [flipBZ_mid hn p s hs0' hsn]; exact Int.natCast_nonneg _
        refine Or.inr ⟨hOK, ?_⟩
        refine Prod.ext ?_ ?_
        · apply Subtype.ext; funext j; apply Fin.ext
          rw [sFlipBase_val, flipBZ_mid hn p s hs0' hsn, Int.toNat_natCast]
          exact congrArg (fun x => (x.1 j : ℕ)) hb
        · show q.2 = flipσ hn p s
          rw [flipσ_mid hn p s hs0' hsn]
          exact hσ

/-! ## The cell complex of the simplex grid -/

/-- Valid data of a small simplex of the Freudenthal triangulation. -/
abbrev CellD (n m : ℕ) := {p : SData n m // SValid p}

noncomputable instance instCellDFintype {n m : ℕ} : Fintype (CellD n m) := by
  classical exact inferInstance

noncomputable instance instCellDDecEq {n m : ℕ} : DecidableEq (CellD n m) := by
  classical exact inferInstance

/-- The vertex set of a valid small simplex. -/
def cellOf {n m : ℕ} (p : CellD n m) : Finset (SGP n m) := sCell p.1 p.2

lemma cellOf_card {n m : ℕ} (p : CellD n m) : (cellOf p).card = n := sCell_card p.1 p.2

lemma sCell_congr {n m : ℕ} {p : SData n m} (h h' : SValid p) : sCell p h = sCell p h' := by
  rw [Subsingleton.elim h h']

lemma sVert_injective {n m : ℕ} (p : SData n m) (hp : SValid p) :
    Function.Injective (sVert p hp) := by
  intro t t' h
  apply vt_injective p
  funext j
  have hh := congrArg (fun x : SGP n m => ((x.1 j : Fin (m + 1)) : ℤ)) h
  rwa [sVert_val, sVert_val] at hh

/-- All cells of the grid. -/
noncomputable def allCells (n m : ℕ) : Finset (Finset (SGP n m)) :=
  (univ : Finset (CellD n m)).image (fun p => cellOf p)

lemma cellOf_mem {n m : ℕ} (p : CellD n m) : cellOf p ∈ allCells n m :=
  Finset.mem_image_of_mem _ (Finset.mem_univ p)

lemma mem_allCells {n m : ℕ} {C : Finset (SGP n m)} :
    C ∈ allCells n m ↔ ∃ p : CellD n m, cellOf p = C := by
  simp only [allCells, Finset.mem_image, Finset.mem_univ, true_and]

lemma allCells_card {n m : ℕ} {C : Finset (SGP n m)} (hC : C ∈ allCells n m) : C.card = n := by
  obtain ⟨p, rfl⟩ := mem_allCells.mp hC
  exact cellOf_card p

/-- A facet of a cell is obtained by erasing one of its vertices. -/
lemma exists_facet {n m : ℕ} (hn : 1 ≤ n) (p : CellD n m) {f : Finset (SGP n m)}
    (hf : f ⊆ cellOf p) (hcard : f.card = n - 1) :
    ∃ s : Fin n, f = (cellOf p).erase (sVert p.1 p.2 s) := by
  classical
  have hcell : (cellOf p).card = n := cellOf_card p
  have hdiff : ((cellOf p) \ f).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hf, hcell, hcard]
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hdiff
  have hxmem : x ∈ cellOf p := by
    have h1 : x ∈ (cellOf p) \ f := by rw [hx]; exact Finset.mem_singleton_self x
    exact (Finset.mem_sdiff.mp h1).1
  have hximg : x ∈ (Finset.univ : Finset (Fin n)).image (sVert p.1 p.2) := hxmem
  obtain ⟨s, -, hs⟩ := Finset.mem_image.mp hximg
  refine ⟨s, ?_⟩
  rw [Finset.erase_eq, hs, ← hx]
  exact (Finset.sdiff_sdiff_eq_self hf).symm

/-- Any other cell containing a facet of `p` is `p` or the flip of `p` at that facet. -/
lemma cells_through_facet {n m : ℕ} (hn : 2 ≤ n) (p : CellD n m) (s : Fin n)
    {q : CellD n m} (hq : (cellOf p).erase (sVert p.1 p.2 s) ⊆ cellOf q) :
    q.1 = p.1 ∨ ∃ h : flipOK hn p.1 s, q.1 = sFlip hn p.1 s h := by
  have H : ∀ t : Fin n, t ≠ s → ∃ t' : Fin n, vt q.1 t' = vt p.1 t := by
    intro t ht
    have hmem : sVert p.1 p.2 t ∈ (cellOf p).erase (sVert p.1 p.2 s) := by
      rw [Finset.mem_erase]
      exact ⟨fun hh => ht (sVert_injective p.1 p.2 hh),
        Finset.mem_image_of_mem _ (Finset.mem_univ t)⟩
    have hmemq : sVert p.1 p.2 t ∈ (Finset.univ : Finset (Fin n)).image (sVert q.1 q.2) :=
      hq hmem
    obtain ⟨t', -, ht'⟩ := Finset.mem_image.mp hmemq
    refine ⟨t', ?_⟩
    funext j
    rw [← sVert_val q.1 q.2 t' j, ht', sVert_val p.1 p.2 t j]
  rcases recon hn p.1 q.1 s H with h | ⟨h, hh⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, hh⟩

/-- The main incidence property: each facet lies in one or two cells. -/
lemma incidence_le_two {n m : ℕ} (hn : 2 ≤ n) (f : Finset (SGP n m)) (hfcard : f.card = n - 1)
    (hex : ∃ C ∈ allCells n m, f ⊆ C) :
    ((allCells n m).filter (fun C => f ⊆ C)).card = 1 ∨
      ((allCells n m).filter (fun C => f ⊆ C)).card = 2 := by
  classical
  obtain ⟨C0, hC0mem, hfC0⟩ := hex
  obtain ⟨p0, hp0eq⟩ := mem_allCells.mp hC0mem
  subst hp0eq
  obtain ⟨s0, hfs0⟩ := exists_facet (by omega) p0 hfC0 hfcard
  set S : Finset (CellD n m) := (univ : Finset (CellD n m)).filter (fun q => f ⊆ cellOf q)
    with hS
  have hkey : ∀ q ∈ S, q = p0 ∨
      ∃ h : flipOK hn p0.1 s0, q.1 = sFlip hn p0.1 s0 h := by
    intro q hq
    rw [hS, Finset.mem_filter] at hq
    obtain ⟨-, hfq⟩ := hq
    have hfq' : (cellOf p0).erase (sVert p0.1 p0.2 s0) ⊆ cellOf q := by rw [← hfs0]; exact hfq
    rcases cells_through_facet hn p0 s0 hfq' with h | ⟨h, hh⟩
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr ⟨h, hh⟩
  have hcardS : S.card ≤ 2 := by
    by_cases hexfl : ∃ h : flipOK hn p0.1 s0, SValid (sFlip hn p0.1 s0 h)
    · have hsub : S ⊆ ({p0, (⟨sFlip hn p0.1 s0 hexfl.choose, hexfl.choose_spec⟩ : CellD n m)} :
          Finset (CellD n m)) := by
        intro q hq
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases hkey q hq with h | ⟨h, hh⟩
        · left; exact h
        · right
          apply Subtype.ext
          rw [hh, Subsingleton.elim h hexfl.choose]
      calc S.card ≤
          ({p0, (⟨sFlip hn p0.1 s0 hexfl.choose, hexfl.choose_spec⟩ : CellD n m)} :
            Finset (CellD n m)).card := Finset.card_le_card hsub
        _ ≤ 2 := by
            have h2 := Finset.card_insert_le p0
              ({(⟨sFlip hn p0.1 s0 hexfl.choose, hexfl.choose_spec⟩ : CellD n m)} :
                Finset (CellD n m))
            rw [Finset.card_singleton] at h2
            simpa using h2
    · have hsub : S ⊆ {p0} := by
        intro q hq
        rw [Finset.mem_singleton]
        rcases hkey q hq with h | ⟨h, hh⟩
        · exact h
        · exact absurd ⟨h, (by rw [← hh]; exact q.2)⟩ hexfl
      have h1 : S.card ≤ 1 := by
        calc S.card ≤ ({p0} : Finset (CellD n m)).card := Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton _
      omega
  have himg_sub : (allCells n m).filter (fun C => f ⊆ C) ⊆ S.image cellOf := by
    intro C hC
    rw [Finset.mem_filter] at hC
    obtain ⟨hCall, hfC⟩ := hC
    obtain ⟨q, hq⟩ := mem_allCells.mp hCall
    refine Finset.mem_image.mpr ⟨q, ?_, hq⟩
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ q, by rw [hq]; exact hfC⟩
  have hcard_le : ((allCells n m).filter (fun C => f ⊆ C)).card ≤ 2 :=
    calc ((allCells n m).filter (fun C => f ⊆ C)).card ≤ (S.image cellOf).card :=
          Finset.card_le_card himg_sub
      _ ≤ S.card := Finset.card_image_le
      _ ≤ 2 := hcardS
  have hcard_ge : 1 ≤ ((allCells n m).filter (fun C => f ⊆ C)).card := by
    refine Finset.card_pos.mpr ⟨cellOf p0, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨cellOf_mem p0, by rw [hfs0]; exact Finset.erase_subset _ _⟩
  omega

end Commons.Topology.Simplex.Freudenthal

namespace Commons.Topology.Simplex

/-- **Sperner's lemma on the Freudenthal triangulation of the simplex grid.**
A support colouring of the mesh-`m` lattice points of the `d`-simplex admits a rainbow family
of pairwise coordinatewise-`1`-close lattice points. -/
theorem sperner_grid_nat (d m : ℕ) (hm : 0 < m)
    (ℓ : {x : Fin (d + 1) → Fin (m + 1) // ∑ j, (x j : ℕ) = m} → Fin (d + 1))
    (hℓ : ∀ x : {x : Fin (d + 1) → Fin (m + 1) // ∑ j, (x j : ℕ) = m},
        (x.1 (ℓ x) : ℕ) ≠ 0) :
    ∃ v : Fin (d + 1) → {x : Fin (d + 1) → Fin (m + 1) // ∑ j, (x j : ℕ) = m},
      Function.Injective (fun t => ℓ (v t)) ∧
      (∀ s t j, ((v s).1 j : ℕ) ≤ ((v t).1 j : ℕ) + 1) := by
  classical
  obtain ⟨S, _hScard, hSsurj, hSclose⟩ :=
    grid_rainbow_cube (d + 1) m hm (by omega) ℓ hℓ
  choose v hv using hSsurj
  refine ⟨v, ?_, ?_⟩
  · intro s t hst
    change ℓ (v s) = ℓ (v t) at hst
    rw [(hv s).2, (hv t).2] at hst
    exact hst
  · exact fun s t j => hSclose (v s) (hv s).1 (v t) (hv t).1 j

end Commons.Topology.Simplex
