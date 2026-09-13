import Submission.Grassmann.F2Helper3
import Submission.Commons.LinearAlgebra.Matrix.card_rank_poset_interval_le_pow
import Submission.Commons.Analysis.Walsh.chi_symmDiff_fintype
import Submission.Commons.Analysis.Walsh.sum_prod_stdAddChar_mul_fintype
import Submission.Commons.Analysis.Walsh.parseval_fintype
import Submission.Commons.Analysis.Inequalities.bonami_lemma_cube_fintype
import Submission.Commons.Analysis.Walsh.sum_normSq_orthogonal_chi
import Submission.Commons.Analysis.Walsh.stdAddChar_neg_one_pow
import Submission.Commons.LinearAlgebra.Matrix.exists_plLE_pair_of_disjoint_dirSum

/-!
# The `𝓕₁` helper (`lem:F1helper` of arXiv:2209.04243 §4.1)

The `𝓕₁(X)` terms of the Fourier expansion of `f²` (`lem:F1`,
`Submission/Grassmann/FClassification.IsF1_or_IsF2`) are the pairs `(Y,Z)` with `Y + Z = X`
that split as direct sums `Y = Y' ⊕ X'`, `Z = Z' ⊕ X'`, `Y' ⊕ Z' = X`.  The paper bounds their
contribution

  `∑_X (∑_{(Y,Z) ∈ 𝓕₁(X)} |f̂(Y)f̂(Z)|)² ≤ 81 q^{6d²}‖f‖₂⁴`

for `f` of degree `≤ d`, by encoding `f` as the pair of **degree-two** functions

  `f₁ = ∑_{Y'⊕X'} |f̂(Y'⊕X')| x_{(Y',1)}x_{(X',2)}`,
  `f₂ = ∑_{Z'⊕X'} |f̂(Z'⊕X')| x_{(Z',1)}x_{(X',2)}`

on the (Boolean) cube indexed by `B(d) × {1,2}`, where `B(d) = {X : rank X ≤ d}`, and then
applying Bonami's hypercontractive inequality for degree-two functions
(`Commons.Analysis.Inequalities.bonami_lemma_cube`).

This file contains the definitional and counting layer:

* `Bd m n d` — the set `B(d) = {X : rank X ≤ d}`;
* `dirSum` — `A ⊕ B` (`rank (A + B) = rank A + rank B`), `dirSum_comm`, `dirSum_iff_plLE`,
  `dirSum_sub_add`;
* `card_dirSum_fiber_le` — the fibre of `A' ↦ (A', Y - A')` over `Y` has at most `q^{(rank Y)²}`
  elements (the paper's "the number of ways of writing `Y = Y' ⊕ X'` is at most `q^{d²}`");
* `f1Fun`, `f2Fun` — the two encoding functions on the cube `Bd m n d × Fin 2 → ZMod 2`;
* `F1Sum`, `F1Bound` — the left-hand side and the statement of `lem:F1helper`.
-/

open Finset BigOperators Matrix
open Classical
open scoped symmDiff

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-- The paper's `B(d)`: the linear maps `W → V` of rank at most `d`. -/
abbrev Bd (m n d : ℕ) := {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank ≤ d}

/-- `A ⊕ B`: the sum is direct, i.e. the ranks add. -/
def dirSum (A B : Matrix (Fin n) (Fin m) 𝔽₂) : Prop := (A + B).rank = A.rank + B.rank

lemma dirSum_comm (A B : Matrix (Fin n) (Fin m) 𝔽₂) : dirSum A B ↔ dirSum B A := by
  unfold dirSum
  rw [add_comm A B]
  exact ⟨fun h => h.trans (Nat.add_comm A.rank B.rank),
         fun h => h.trans (Nat.add_comm B.rank A.rank)⟩

lemma add_sub_cancel_zmod (A B : Matrix (Fin n) (Fin m) 𝔽₂) : A + B - A = B := by
  rw [sub_eq_add_neg, mtx_neg_eq]
  rw [add_assoc, add_comm B A, ← add_assoc, mtx_add_self, zero_add]

lemma eq_sub_of_add_eq_zmod {A B Y : Matrix (Fin n) (Fin m) 𝔽₂} (h : A + B = Y) :
    B = Y - A := by
  rw [← h, add_sub_cancel_zmod]

lemma plLE_of_add_eq_dirSum {A B Y : Matrix (Fin n) (Fin m) 𝔽₂} (h : A + B = Y)
    (hd : dirSum A B) : plLE A Y := by
  unfold plLE dirSum at *
  rw [← h, add_sub_cancel_zmod]
  exact hd

/-- `dirSum A B` is exactly `plLE A (A + B)`. -/
lemma dirSum_iff_plLE (A B : Matrix (Fin n) (Fin m) 𝔽₂) :
    dirSum A B ↔ plLE A (A + B) := by
  unfold dirSum plLE
  rw [add_sub_cancel_zmod]

/-- The fibre of `A' ↦ (A', Y - A')` over `Y`: the number of ways of writing `Y` as a direct sum
`Y = Y' ⊕ X'` is at most `q^{(rank Y)²}`. -/
lemma card_dirSum_fiber_le (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    Nat.card {p : Matrix (Fin n) (Fin m) 𝔽₂ × Matrix (Fin n) (Fin m) 𝔽₂ //
      p.1 + p.2 = Y ∧ dirSum p.1 p.2} ≤ 2 ^ (Y.rank * Y.rank) := by
  classical
  let g : {p : Matrix (Fin n) (Fin m) 𝔽₂ × Matrix (Fin n) (Fin m) 𝔽₂ //
      p.1 + p.2 = Y ∧ dirSum p.1 p.2} →
      {A' : Matrix (Fin n) (Fin m) 𝔽₂ // plLE A' Y} :=
    fun p => ⟨p.1.1, plLE_of_add_eq_dirSum p.2.1 p.2.2⟩
  have hinj : Function.Injective g := by
    intro p q hpq
    have hp1 : p.1.1 = q.1.1 := Subtype.ext_iff.mp hpq
    have hp2 : p.1.2 = q.1.2 := by
      rw [eq_sub_of_add_eq_zmod p.2.1, eq_sub_of_add_eq_zmod q.2.1, hp1]
    exact Subtype.ext (Prod.ext hp1 hp2)
  exact le_trans (Nat.card_le_card_of_injective g hinj)
    (Commons.LinearAlgebra.Matrix.card_rank_poset_interval_le_pow n m Y)

/-- **The paper's `𝓕₁(X)`** (arXiv:2209.04243 §4): pairs `(Y,Z)` with `Y + Z = X` that admit
`Y' ≤ Y`, `Z' ≤ Z` with `Y' ⊕ Z' = X` a *direct* sum (rank-additive).

Note that the `Submission.Grassmann.IsF1` of `FClassification.lean` omits the direct-sum
condition; without it the predicate is trivially true (`Y' = Y`, `Z' = Z`), which is why this
sharper predicate is the one used for the `𝓕₁` estimate. -/
def IsF1D {m n : ℕ} (X Y Z : Matrix (Fin n) (Fin m) 𝔽₂) : Prop :=
  Y + Z = X ∧ ∃ Y' Z' : Matrix (Fin n) (Fin m) 𝔽₂,
    plLE Y' Y ∧ plLE Z' Z ∧ dirSum Y' Z' ∧ Y' + Z' = X

/-- **`lem:F1` of arXiv:2209.04243, for the *sharp* `𝓕₁`**: every pair `(Y,Z)` with `Y + Z = X`
lies in `𝓕₁(X)` (with the direct-sum condition) or in `𝓕₂(X)`. -/
theorem IsF1D_or_IsF2 {m n : ℕ} (X Y Z : Matrix (Fin n) (Fin m) 𝔽₂) (h : Y + Z = X) :
    IsF1D X Y Z ∨ IsF2 X Y Z := by
  by_cases h1 : LinearMap.range Y.mulVecLin ⊓ LinearMap.range Z.mulVecLin ⊓
      LinearMap.range X.mulVecLin = ⊥
  · by_cases h2 : LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker Z.mulVecLin ⊔
        LinearMap.ker X.mulVecLin = ⊤
    · left
      obtain ⟨Y', Z', hY', hZ', hd, hX⟩ :=
        Commons.LinearAlgebra.Matrix.exists_plLE_pair_of_disjoint_dirSum X Y Z h h1 h2
      exact ⟨h, Y', Z', hY', hZ', hd, hX⟩
    · right; exact ⟨h, Or.inr h2⟩
  · right; exact ⟨h, Or.inl h1⟩

/-- The left-hand side of `lem:F1helper` at `X`: the `𝓕₁(X)` contribution
`∑_{(Y,Z) ∈ 𝓕₁(X)} |f̂(Y) f̂(Z)|`.

The sum is restricted to the linear maps of rank at most `d` (the paper's `B(d)`); for a
function of degree at most `d` the remaining Fourier coefficients vanish, so the restriction
does not change the value. -/
def F1Sum (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : ℝ :=
  ∑ Y : Bd m n d, ∑ Z : Bd m n d,
    if IsF1D X Y.1 Z.1 then ‖fcoeff f Y.1‖ * ‖fcoeff f Z.1‖ else 0

lemma F1Sum_nonneg (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    0 ≤ F1Sum d X f := by
  refine Finset.sum_nonneg (fun Y _ => Finset.sum_nonneg (fun Z _ => ?_))
  by_cases h : IsF1D X Y.1 Z.1
  · rw [if_pos h]; positivity
  · rw [if_neg h]

/-- `A + (B - A) = B`. -/
lemma add_sub_cancel_zmod' (A B : Matrix (Fin n) (Fin m) 𝔽₂) : A + (B - A) = B := by
  rw [sub_eq_add_neg, mtx_neg_eq,
    show A + (B + A) = (A + A) + B from by abel, mtx_add_self, zero_add]

/-- **The splitting of the `𝓕₁` pairs**: every `(Y,Z) ∈ 𝓕₁(X)` is of the form `Y = Y' ⊕ X'`,
`Z = Z' ⊕ X'` with `Y' ⊕ Z' = X`. -/
lemma exists_split_of_isF1 {X Y Z : Matrix (Fin n) (Fin m) 𝔽₂} (h : IsF1D X Y Z) :
    ∃ X' Y' Z' : Matrix (Fin n) (Fin m) 𝔽₂,
      Y = Y' + X' ∧ Z = Z' + X' ∧ Y' + Z' = X ∧ dirSum Y' X' ∧ dirSum Z' X' := by
  obtain ⟨hYZ, Y', Z', hY', hZ', _hd, hX⟩ := h
  have h1 : Y + Z = Y' + Z' := by rw [hYZ, hX]
  have hsub : Y - Y' = Z - Z' := by
    simp only [sub_eq_add_neg, mtx_neg_eq]
    have hkey : Y + Y' + (Z + Z') = 0 := by
      calc Y + Y' + (Z + Z') = (Y + Z) + (Y' + Z') := by abel
        _ = (Y' + Z') + (Y' + Z') := by rw [h1]
        _ = 0 := mtx_add_self _
    rw [add_eq_zero_iff_eq_neg] at hkey
    rw [mtx_neg_eq] at hkey
    exact hkey
  have hZsplit : Z' + (Z - Z') = Z := add_sub_cancel_zmod' Z' Z
  have hZsplit' : Z' + (Y - Y') = Z := by rw [hsub]; exact hZsplit
  refine ⟨Y - Y', Y', Z', ?_, ?_, hX, ?_, ?_⟩
  · exact (add_sub_cancel_zmod' Y' Y).symm
  · exact hZsplit'.symm
  · refine (dirSum_iff_plLE Y' (Y - Y')).mpr ?_
    rw [add_sub_cancel_zmod']
    exact hY'
  · refine (dirSum_iff_plLE Z' (Y - Y')).mpr ?_
    rw [hZsplit']
    exact hZ'

/-- The paper's `f₁`: the degree-two function on the cube `B(d) × {1,2}` whose Fourier
coefficient at `{(Y',1),(X',2)}` is `|f̂(Y' ⊕ X')|`. -/
def f1Fun (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (x : Bd m n d × Fin 3 → ZMod 2) : ℂ :=
  ∑ Y' : Bd m n d, ∑ X' : Bd m n d,
    if dirSum Y'.1 X'.1 then
      ((‖fcoeff f (Y'.1 + X'.1)‖ : ℝ) : ℂ) *
        (ZMod.stdAddChar (x (Y', (0 : Fin 3))) * ZMod.stdAddChar (x (X', (1 : Fin 3))))
    else 0

/-- The paper's `f₂`: the degree-two function on the cube `B(d) × {1,2}` whose Fourier
coefficient at `{(Z',1),(X',2)}` is `|f̂(Z' ⊕ X')|`. -/
def f2Fun (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (x : Bd m n d × Fin 3 → ZMod 2) : ℂ :=
  ∑ Z' : Bd m n d, ∑ X' : Bd m n d,
    if dirSum Z'.1 X'.1 then
      ((‖fcoeff f (Z'.1 + X'.1)‖ : ℝ) : ℂ) *
        (ZMod.stdAddChar (x (Z', (2 : Fin 3))) * ZMod.stdAddChar (x (X', (1 : Fin 3))))
    else 0

/-- The statement of `lem:F1helper`: `∑_X (∑_{(Y,Z) ∈ 𝓕₁(X)} |f̂(Y)f̂(Z)|)² ≤ 81 q^{6d²}‖f‖₂⁴`
for `f` of degree `≤ d`. -/
def F1Bound (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : Prop :=
  (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, F1Sum d X f ^ 2)
    ≤ 81 * (2 : ℝ) ^ (6 * d ^ 2) * (l2sq f) ^ 2

/-- The fibre count for the `𝓕₁` reindexing, with the rank guards of `B(d)`: for fixed `Y`, at
most `q^{(rank Y)²}` pairs `(A,B)` with `A,B` of rank `≤ d` satisfy `A ⊕ B = Y`. -/
lemma card_bd_pair_add_eq_le (d : ℕ) (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    Nat.card {q : Bd m n d × Bd m n d // q.1.1 + q.2.1 = Y ∧ dirSum q.1.1 q.2.1}
      ≤ 2 ^ (Y.rank ^ 2) := by
  classical
  let g : {q : Bd m n d × Bd m n d // q.1.1 + q.2.1 = Y ∧ dirSum q.1.1 q.2.1} →
      {p : Matrix (Fin n) (Fin m) 𝔽₂ × Matrix (Fin n) (Fin m) 𝔽₂ //
        p.1 + p.2 = Y ∧ dirSum p.1 p.2} :=
    fun q => ⟨(q.1.1.1, q.1.2.1), q.2⟩
  have hinj : Function.Injective g := by
    intro q r hqr
    have h1 : q.1.1.1 = r.1.1.1 := congrArg (fun t => t.1.1) hqr
    have h2 : q.1.2.1 = r.1.2.1 := congrArg (fun t => t.1.2) hqr
    exact Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2))
  have h := le_trans (Nat.card_le_card_of_injective g hinj) (card_dirSum_fiber_le Y)
  rw [← pow_two] at h
  exact h

/-- **The `L²` bound for the `𝓕₁` encoding**: the squared norms of the coefficients of the pair
functions `f₁`, `f₂` sum to at most `q^{d²}‖f‖₂²` for `f` of degree `≤ d`. -/
lemma sum_dirSum_normSq_le (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (hf : DegLe d f) :
    (∑ Y' : Bd m n d, ∑ X' : Bd m n d,
      (if dirSum Y'.1 X'.1 then ‖fcoeff f (Y'.1 + X'.1)‖ ^ 2 else 0))
      ≤ (2 : ℝ) ^ (d ^ 2) * l2sq f := by
  classical
  have hprod : (∑ Y' : Bd m n d, ∑ X' : Bd m n d,
      (if dirSum Y'.1 X'.1 then ‖fcoeff f (Y'.1 + X'.1)‖ ^ 2 else 0))
      = ∑ q : Bd m n d × Bd m n d,
          (if dirSum q.1.1 q.2.1 then ‖fcoeff f (q.1.1 + q.2.1)‖ ^ 2 else 0) := by
    rw [← Fintype.sum_prod_type (f := fun q : Bd m n d × Bd m n d =>
      if dirSum q.1.1 q.2.1 then ‖fcoeff f (q.1.1 + q.2.1)‖ ^ 2 else 0)]
  rw [hprod]
  rw [← Fintype.sum_fiberwise (fun q : Bd m n d × Bd m n d => q.1.1 + q.2.1)
    (fun q : Bd m n d × Bd m n d =>
      if dirSum q.1.1 q.2.1 then ‖fcoeff f (q.1.1 + q.2.1)‖ ^ 2 else 0)]
  have hstep : (∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
        ∑ q : {q : Bd m n d × Bd m n d // q.1.1 + q.2.1 = Y},
          (if dirSum q.1.1.1 q.1.2.1 then ‖fcoeff f (q.1.1.1 + q.1.2.1)‖ ^ 2 else 0))
      ≤ ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂, ((2 : ℝ) ^ (d ^ 2) * ‖fcoeff f Y‖ ^ 2) := by
    refine Finset.sum_le_sum (fun Y _ => ?_)
    have hpt : ∀ q : {q : Bd m n d × Bd m n d // q.1.1 + q.2.1 = Y},
        (if dirSum q.1.1.1 q.1.2.1 then ‖fcoeff f (q.1.1.1 + q.1.2.1)‖ ^ 2 else 0)
          = (if dirSum q.1.1.1 q.1.2.1 then ‖fcoeff f Y‖ ^ 2 else 0) := by
      intro q
      rw [q.2]
    have hsum : (∑ q : {q : Bd m n d × Bd m n d // q.1.1 + q.2.1 = Y},
          (if dirSum q.1.1.1 q.1.2.1 then ‖fcoeff f (q.1.1.1 + q.1.2.1)‖ ^ 2 else 0))
        = (Nat.card {q : {q : Bd m n d × Bd m n d // q.1.1 + q.2.1 = Y} //
              dirSum q.1.1.1 q.1.2.1}) • ‖fcoeff f Y‖ ^ 2 := by
      refine (Finset.sum_congr rfl (fun q _ => hpt q)).trans ?_
      rw [← Finset.sum_filter, Finset.sum_const, ← Fintype.card_subtype, Nat.card_eq_fintype_card]
    rw [hsum]
    by_cases hY : fcoeff f Y = 0
    · rw [hY]; simp
    · have hrank : Y.rank ≤ d := by
        by_contra h
        exact hY (fcoeff_eq_zero_of_rank_gt hf (by omega))
      have hc : Nat.card {q : {q : Bd m n d × Bd m n d // q.1.1 + q.2.1 = Y} //
          dirSum q.1.1.1 q.1.2.1} ≤ 2 ^ (d ^ 2) := by
        have h1 : Nat.card {q : {q : Bd m n d × Bd m n d // q.1.1 + q.2.1 = Y} //
            dirSum q.1.1.1 q.1.2.1} ≤ 2 ^ (Y.rank ^ 2) := by
          refine le_trans (Nat.card_le_card_of_injective
            (fun q => (⟨q.1.1, q.1.2, q.2⟩ :
              {w : Bd m n d × Bd m n d // w.1.1 + w.2.1 = Y ∧ dirSum w.1.1 w.2.1})) ?_)
            (card_bd_pair_add_eq_le d Y)
          intro q r hqr
          have hv := congrArg (fun t : {w : Bd m n d × Bd m n d //
              w.1.1 + w.2.1 = Y ∧ dirSum w.1.1 w.2.1} => (t.1 : Bd m n d × Bd m n d)) hqr
          exact Subtype.ext (Subtype.ext hv)
        exact le_trans h1 (pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_left hrank 2))
      calc Nat.card {q : {q : Bd m n d × Bd m n d // q.1.1 + q.2.1 = Y} //
              dirSum q.1.1.1 q.1.2.1} • ‖fcoeff f Y‖ ^ 2
          = ((Nat.card {q : {q : Bd m n d × Bd m n d // q.1.1 + q.2.1 = Y} //
              dirSum q.1.1.1 q.1.2.1} : ℕ) : ℝ) * ‖fcoeff f Y‖ ^ 2 := nsmul_eq_mul _ _
        _ ≤ (2 : ℝ) ^ (d ^ 2) * ‖fcoeff f Y‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
  refine le_trans hstep ?_
  rw [← Finset.mul_sum, sum_normSq_fcoeff]

/-! ## The cube characters of the encoding -/

/-- The cube on which the encoding functions `f₁`, `f₂` live: `B(d) × {1,2}`. -/
abbrev Cube (m n d : ℕ) := Bd m n d × Fin 3

/-- The set of cube coordinates attached to a pair `(Y',X')`. -/
def wset (d : ℕ) (p : Bd m n d × Bd m n d) : Finset (Cube m n d) :=
  {(p.1, (0 : Fin 3)), (p.2, (1 : Fin 3))}

/-- The cube character `x_{(Y',1)} x_{(X',2)}` attached to a pair `(Y',X')`. -/
def wchar (d : ℕ) (p : Bd m n d × Bd m n d) (x : Cube m n d → ZMod 2) : ℂ :=
  ∏ i ∈ wset d p, ZMod.stdAddChar (x i)

/-- The sum of a cube character over the cube: `2^{|ι|}` for the trivial character, else `0`. -/
lemma sum_chi_empty {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) :
    (∑ x : ι → ZMod 2, ∏ i ∈ S, ZMod.stdAddChar (x i))
      = if S = ∅ then (2 : ℂ) ^ Fintype.card ι else 0 := by
  have h := Commons.Analysis.Walsh.sum_prod_stdAddChar_mul_fintype S (∅ : Finset ι)
  simpa using h

lemma wchar_mul_eq (d : ℕ) (p q : Bd m n d × Bd m n d) (x : Cube m n d → ZMod 2) :
    wchar d p x * wchar d q x
      = ∏ i ∈ (wset d p \ wset d q) ∪ (wset d q \ wset d p), ZMod.stdAddChar (x i) :=
  Commons.Analysis.Walsh.chi_symmDiff_fintype _ _ x

lemma wset_ne (d : ℕ) (p : Bd m n d × Bd m n d) :
    (p.1, (0 : Fin 3)) ≠ (p.2, (1 : Fin 3)) := by
  intro h
  exact absurd (congrArg Prod.snd h) (by decide : (0 : Fin 3) ≠ 1)

lemma wset_inj (d : ℕ) (p q : Bd m n d × Bd m n d) : wset d p = wset d q ↔ p = q := by
  constructor
  · intro h
    have h1 : (p.1, (0 : Fin 3)) ∈ wset d q := by rw [← h]; simp [wset]
    have h2 : (p.2, (1 : Fin 3)) ∈ wset d q := by rw [← h]; simp [wset]
    simp only [wset, Finset.mem_insert, Finset.mem_singleton] at h1 h2
    have hp1 : p.1 = q.1 := by
      rcases h1 with h1 | h1
      · exact congrArg (fun t : Bd m n d × Fin 3 => t.1) h1
      · exact absurd (congrArg (fun t : Bd m n d × Fin 3 => t.2) h1)
          (by decide : (0 : Fin 3) ≠ 1)
    have hp2 : p.2 = q.2 := by
      rcases h2 with h2 | h2
      · exact absurd (congrArg (fun t : Bd m n d × Fin 3 => t.2) h2)
          (by decide : (1 : Fin 3) ≠ 0)
      · exact congrArg (fun t : Bd m n d × Fin 3 => t.1) h2
    exact Prod.ext hp1 hp2
  · intro h; rw [h]

lemma wset_symmDiff_eq_empty (d : ℕ) (p q : Bd m n d × Bd m n d) :
    (wset d p \ wset d q) ∪ (wset d q \ wset d p) = ∅ ↔ p = q := by
  constructor
  · intro h
    rw [← wset_inj]
    ext x
    exact ⟨fun hx => by
        by_contra hxq
        have hmem : x ∈ (wset d p \ wset d q) ∪ (wset d q \ wset d p) :=
          Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hx, hxq⟩))
        rw [h] at hmem
        exact absurd hmem (Finset.notMem_empty x),
      fun hx => by
        by_contra hxp
        have hmem : x ∈ (wset d p \ wset d q) ∪ (wset d q \ wset d p) :=
          Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, hxp⟩))
        rw [h] at hmem
        exact absurd hmem (Finset.notMem_empty x)⟩
  · intro h; rw [h]; simp

/-- **Orthogonality of the encoding monomials**: `Σ_x x_{p} x_{q} = 2^{|cube|}` when `p = q`
and `0` otherwise. -/
lemma sum_wchar_mul (d : ℕ) (p q : Bd m n d × Bd m n d) :
    (∑ x : Cube m n d → ZMod 2, wchar d p x * wchar d q x)
      = if p = q then (2 : ℂ) ^ Fintype.card (Cube m n d) else 0 := by
  classical
  have h1 : (∑ x : Cube m n d → ZMod 2, wchar d p x * wchar d q x)
      = ∑ x : Cube m n d → ZMod 2,
          ∏ i ∈ (wset d p \ wset d q) ∪ (wset d q \ wset d p), ZMod.stdAddChar (x i) :=
    Finset.sum_congr rfl (fun x _ => wchar_mul_eq d p q x)
  rw [h1, sum_chi_empty]
  by_cases h : p = q
  · rw [if_pos h, if_pos ((wset_symmDiff_eq_empty d p q).mpr h)]
  · rw [if_neg h, if_neg (fun hh => h ((wset_symmDiff_eq_empty d p q).mp hh))]

/-! ## Normalised norms on the cube and Bonami for degree two -/

/-- The normalised squared `L²` norm on the cube `ι → 𝔽₂`. -/
def l2sqC {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ZMod 2) → ℂ) : ℝ :=
  ((2 : ℝ) ^ Fintype.card ι)⁻¹ * ∑ x : ι → ZMod 2, ‖g x‖ ^ 2

/-- The normalised `L⁴` norm on the cube `ι → 𝔽₂`. -/
def l4qC {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ZMod 2) → ℂ) : ℝ :=
  ((2 : ℝ) ^ Fintype.card ι)⁻¹ * ∑ x : ι → ZMod 2, ‖g x‖ ^ 4

lemma l2sqC_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ZMod 2) → ℂ) :
    0 ≤ l2sqC g :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)

/-- Algebraic form of Bonami: `c⁻¹ A ≤ 81 (c⁻¹ B)²` follows from `c A ≤ 81 B²` for `c > 0`. -/
lemma inv_mul_le_of_mul_le {c A B : ℝ} (hc : 0 < c) (h : c * A ≤ 81 * B ^ 2) :
    c⁻¹ * A ≤ 81 * (c⁻¹ * B) ^ 2 := by
  have h1 : c⁻¹ * A = (c * A) / c ^ 2 := by field_simp
  have h2 : 81 * (c⁻¹ * B) ^ 2 = 81 * B ^ 2 / c ^ 2 := by field_simp; try ring
  rw [h1, h2]
  exact div_le_div_of_nonneg_right h (by positivity)

/-- Bonami's inequality for degree-two functions on the cube, in normalised form. -/
lemma l4qC_le_of_deg_two {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ZMod 2) → ℂ)
    (h : ∀ S : Finset ι, 2 < S.card →
      (∑ x : ι → ZMod 2, g x * ∏ i ∈ S, ((-1 : ℂ) ^ (x i).val)) = 0) :
    l4qC g ≤ 81 * (l2sqC g) ^ 2 := by
  have hc : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι := by positivity
  have hb : (2 : ℝ) ^ Fintype.card ι * ∑ x : ι → ZMod 2, ‖g x‖ ^ 4
      ≤ 81 * (∑ x : ι → ZMod 2, ‖g x‖ ^ 2) ^ 2 := by
    have h0 := Commons.Analysis.Inequalities.bonami_lemma_cube_fintype 2 g h
    norm_num at h0
    exact h0
  simpa only [l4qC, l2sqC] using inv_mul_le_of_mul_le hc hb



/-- The `f₂`-slot character of the encoding cube. -/
def zset (d : ℕ) (p : Bd m n d × Bd m n d) : Finset (Cube m n d) :=
  {(p.1, (2 : Fin 3)), (p.2, (1 : Fin 3))}

/-- The `f₂`-monomial `χ_{(p.1,2)} χ_{(p.2,1)}`. -/
def zchar (d : ℕ) (p : Bd m n d × Bd m n d) (x : Cube m n d → ZMod 2) : ℂ :=
  ∏ i ∈ zset d p, ZMod.stdAddChar (x i)

/-- The Fourier index at which the `𝓕₁`-contribution of the pair `p = (Y',Z')` is read. -/
def encSet (d : ℕ) (p : Bd m n d × Bd m n d) : Finset (Cube m n d) :=
  {(p.1, (0 : Fin 3)), (p.2, (2 : Fin 3))}

/-- The coefficient of the encoding function `f₁` at the pair `p = (Y',X')`. -/
def c1 (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (p : Bd m n d × Bd m n d) : ℂ :=
  if dirSum p.1.1 p.2.1 then ((‖fcoeff f (p.1.1 + p.2.1)‖ : ℝ) : ℂ) else 0

/-- The coefficient of the encoding function `f₂` at the pair `p = (Z',X')`. -/
def c2 (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (p : Bd m n d × Bd m n d) : ℂ :=
  if dirSum p.1.1 p.2.1 then ((‖fcoeff f (p.1.1 + p.2.1)‖ : ℝ) : ℂ) else 0

lemma wchar_apply (d : ℕ) (p : Bd m n d × Bd m n d) (x : Cube m n d → ZMod 2) :
    wchar d p x = ZMod.stdAddChar (x (p.1, (0 : Fin 3))) * ZMod.stdAddChar (x (p.2, (1 : Fin 3))) := by
  unfold wchar wset
  rw [Finset.prod_insert (by simpa using wset_ne d p), Finset.prod_singleton]

lemma zchar_apply (d : ℕ) (p : Bd m n d × Bd m n d) (x : Cube m n d → ZMod 2) :
    zchar d p x = ZMod.stdAddChar (x (p.1, (2 : Fin 3))) * ZMod.stdAddChar (x (p.2, (1 : Fin 3))) := by
  unfold zchar zset
  rw [Finset.prod_insert (by
        simp only [Finset.mem_singleton]
        intro h
        exact absurd (congrArg Prod.snd h) (by decide : (2 : Fin 3) ≠ 1)), Finset.prod_singleton]

lemma f1Fun_eq_sum (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    f1Fun d f = fun x : Cube m n d → ZMod 2 => ∑ p : Bd m n d × Bd m n d, c1 d f p * wchar d p x := by
  funext x
  simp only [f1Fun]
  rw [← Fintype.sum_prod_type (f := fun p : Bd m n d × Bd m n d =>
      (if dirSum p.1.1 p.2.1 then ((‖fcoeff f (p.1.1 + p.2.1)‖ : ℝ) : ℂ) *
        (ZMod.stdAddChar (x (p.1, (0 : Fin 3))) * ZMod.stdAddChar (x (p.2, (1 : Fin 3)))) else 0))]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [c1, wchar_apply]
  by_cases h : dirSum p.1.1 p.2.1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_mul]

lemma f2Fun_eq_sum (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    f2Fun d f = fun x : Cube m n d → ZMod 2 => ∑ p : Bd m n d × Bd m n d, c2 d f p * zchar d p x := by
  funext x
  simp only [f2Fun]
  rw [← Fintype.sum_prod_type (f := fun p : Bd m n d × Bd m n d =>
      (if dirSum p.1.1 p.2.1 then ((‖fcoeff f (p.1.1 + p.2.1)‖ : ℝ) : ℂ) *
        (ZMod.stdAddChar (x (p.1, (2 : Fin 3))) * ZMod.stdAddChar (x (p.2, (1 : Fin 3)))) else 0))]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [c2, zchar_apply]
  by_cases h : dirSum p.1.1 p.2.1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_mul]

lemma sum_normSq_c1 (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    ∑ p : Bd m n d × Bd m n d, ‖c1 d f p‖ ^ 2
      = ∑ Y' : Bd m n d, ∑ X' : Bd m n d,
          (if dirSum Y'.1 X'.1 then ‖fcoeff f (Y'.1 + X'.1)‖ ^ 2 else 0) := by
  rw [Fintype.sum_prod_type (f := fun p : Bd m n d × Bd m n d => ‖c1 d f p‖ ^ 2)]
  refine Finset.sum_congr rfl (fun Y' _ => Finset.sum_congr rfl (fun X' _ => ?_))
  unfold c1
  by_cases h : dirSum Y'.1 X'.1
  · rw [if_pos h, if_pos h, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq]
  · rw [if_neg h, if_neg h]
    simp

lemma sum_normSq_c2 (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    ∑ p : Bd m n d × Bd m n d, ‖c2 d f p‖ ^ 2
      = ∑ Y' : Bd m n d, ∑ X' : Bd m n d,
          (if dirSum Y'.1 X'.1 then ‖fcoeff f (Y'.1 + X'.1)‖ ^ 2 else 0) := by
  rw [Fintype.sum_prod_type (f := fun p : Bd m n d × Bd m n d => ‖c2 d f p‖ ^ 2)]
  refine Finset.sum_congr rfl (fun Y' _ => Finset.sum_congr rfl (fun X' _ => ?_))
  unfold c2
  by_cases h : dirSum Y'.1 X'.1
  · rw [if_pos h, if_pos h, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq]
  · rw [if_neg h, if_neg h]
    simp

lemma zset_inj (d : ℕ) (p q : Bd m n d × Bd m n d) : zset d p = zset d q ↔ p = q := by
  constructor
  · intro h
    have h1 : (p.1, (2 : Fin 3)) ∈ zset d q := by rw [← h]; simp [zset]
    have h2 : (p.2, (1 : Fin 3)) ∈ zset d q := by rw [← h]; simp [zset]
    simp only [zset, Finset.mem_insert, Finset.mem_singleton] at h1 h2
    have hp1 : p.1 = q.1 := by
      rcases h1 with h1 | h1
      · exact congrArg (fun t : Bd m n d × Fin 3 => t.1) h1
      · exact absurd (congrArg (fun t : Bd m n d × Fin 3 => t.2) h1)
          (by decide : (2 : Fin 3) ≠ 1)
    have hp2 : p.2 = q.2 := by
      rcases h2 with h2 | h2
      · exact absurd (congrArg (fun t : Bd m n d × Fin 3 => t.2) h2)
          (by decide : (1 : Fin 3) ≠ 2)
      · exact congrArg (fun t : Bd m n d × Fin 3 => t.1) h2
    exact Prod.ext hp1 hp2
  · intro h; rw [h]

lemma sum_zchar_mul (d : ℕ) (p q : Bd m n d × Bd m n d) :
    (∑ x : Cube m n d → ZMod 2, zchar d p x * zchar d q x)
      = if p = q then (2 : ℂ) ^ Fintype.card (Cube m n d) else 0 := by
  classical
  have h : ∀ x, zchar d p x * zchar d q x
      = (∏ i ∈ zset d p, ZMod.stdAddChar (x i)) *
        (∏ i ∈ zset d q, ZMod.stdAddChar (x i)) := by
    intro x; simp only [zchar]
  rw [Finset.sum_congr rfl (fun x _ => h x),
    Commons.Analysis.Walsh.sum_prod_stdAddChar_mul_fintype]
  by_cases hpq : p = q
  · rw [if_pos hpq, if_pos ((zset_inj d p q).mpr hpq)]
  · rw [if_neg hpq, if_neg (fun hh => hpq ((zset_inj d p q).mp hh))]

lemma sum_wchar_chi (d : ℕ) (p : Bd m n d × Bd m n d) (S : Finset (Cube m n d)) :
    (∑ x : Cube m n d → ZMod 2, wchar d p x * ∏ i ∈ S, ZMod.stdAddChar (x i))
      = if wset d p = S then (2 : ℂ) ^ Fintype.card (Cube m n d) else 0 := by
  classical
  have h : ∀ x, wchar d p x * (∏ i ∈ S, ZMod.stdAddChar (x i))
      = (∏ i ∈ wset d p, ZMod.stdAddChar (x i)) * (∏ i ∈ S, ZMod.stdAddChar (x i)) := by
    intro x; simp only [wchar]
  rw [Finset.sum_congr rfl (fun x _ => h x)]
  exact Commons.Analysis.Walsh.sum_prod_stdAddChar_mul_fintype (wset d p) S

lemma sum_zchar_chi (d : ℕ) (p : Bd m n d × Bd m n d) (S : Finset (Cube m n d)) :
    (∑ x : Cube m n d → ZMod 2, zchar d p x * ∏ i ∈ S, ZMod.stdAddChar (x i))
      = if zset d p = S then (2 : ℂ) ^ Fintype.card (Cube m n d) else 0 := by
  classical
  have h : ∀ x, zchar d p x * (∏ i ∈ S, ZMod.stdAddChar (x i))
      = (∏ i ∈ zset d p, ZMod.stdAddChar (x i)) * (∏ i ∈ S, ZMod.stdAddChar (x i)) := by
    intro x; simp only [zchar]
  rw [Finset.sum_congr rfl (fun x _ => h x)]
  exact Commons.Analysis.Walsh.sum_prod_stdAddChar_mul_fintype (zset d p) S

lemma wset_card_le_two (d : ℕ) (p : Bd m n d × Bd m n d) : (wset d p).card ≤ 2 := by
  unfold wset
  exact le_trans (Finset.card_insert_le _ _) (by simp)

lemma zset_card_le_two (d : ℕ) (p : Bd m n d × Bd m n d) : (zset d p).card ≤ 2 := by
  unfold zset
  exact le_trans (Finset.card_insert_le _ _) (by simp)

lemma l2sqC_f1Fun (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l2sqC (f1Fun d f) = ∑ Y' : Bd m n d, ∑ X' : Bd m n d,
      (if dirSum Y'.1 X'.1 then ‖fcoeff f (Y'.1 + X'.1)‖ ^ 2 else 0) := by
  have h1 : ∀ x : Cube m n d → ZMod 2, f1Fun d f x = ∑ p : Bd m n d × Bd m n d, c1 d f p * wchar d p x :=
    fun x => congrFun (f1Fun_eq_sum d f) x
  have h2 : (∑ x : Cube m n d → ZMod 2, ‖f1Fun d f x‖ ^ 2) =
      (2 : ℝ) ^ Fintype.card (Cube m n d) * ∑ p, ‖c1 d f p‖ ^ 2 := by
    simp only [h1]
    exact Commons.Analysis.Walsh.sum_normSq_orthogonal_chi (fun p x => wchar d p x) (c1 d f)
      (fun p x => by
        rw [wchar_apply, map_mul, Commons.Analysis.Walsh.starRingEnd_stdAddChar_two,
          Commons.Analysis.Walsh.starRingEnd_stdAddChar_two])
      (fun p q => sum_wchar_mul d p q)
  unfold l2sqC
  rw [h2, sum_normSq_c1, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), one_mul]

lemma l2sqC_f2Fun (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l2sqC (f2Fun d f) = ∑ Y' : Bd m n d, ∑ X' : Bd m n d,
      (if dirSum Y'.1 X'.1 then ‖fcoeff f (Y'.1 + X'.1)‖ ^ 2 else 0) := by
  have h1 : ∀ x : Cube m n d → ZMod 2, f2Fun d f x = ∑ p : Bd m n d × Bd m n d, c2 d f p * zchar d p x :=
    fun x => congrFun (f2Fun_eq_sum d f) x
  have h2 : (∑ x : Cube m n d → ZMod 2, ‖f2Fun d f x‖ ^ 2) =
      (2 : ℝ) ^ Fintype.card (Cube m n d) * ∑ p, ‖c2 d f p‖ ^ 2 := by
    simp only [h1]
    exact Commons.Analysis.Walsh.sum_normSq_orthogonal_chi (fun p x => zchar d p x) (c2 d f)
      (fun p x => by
        rw [zchar_apply, map_mul, Commons.Analysis.Walsh.starRingEnd_stdAddChar_two,
          Commons.Analysis.Walsh.starRingEnd_stdAddChar_two])
      (fun p q => sum_zchar_mul d p q)
  unfold l2sqC
  rw [h2, sum_normSq_c2, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), one_mul]

lemma deg_two_f1Fun (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (S : Finset (Cube m n d)) (hS : 2 < S.card) :
    (∑ x : Cube m n d → ZMod 2, f1Fun d f x * ∏ i ∈ S, ((-1 : ℂ) ^ (x i).val)) = 0 := by
  classical
  have hcongr : ∀ x, f1Fun d f x * (∏ i ∈ S, ((-1 : ℂ) ^ (x i).val))
      = f1Fun d f x * ∏ i ∈ S, ZMod.stdAddChar (x i) := by
    intro x
    congr 1
    exact Finset.prod_congr rfl (fun i _ => (Commons.Analysis.Walsh.stdAddChar_neg_one_pow (x i)).symm)
  rw [Finset.sum_congr rfl (fun x _ => hcongr x)]
  have h1 : ∀ x : Cube m n d → ZMod 2, f1Fun d f x = ∑ p, c1 d f p * wchar d p x :=
    fun x => congrFun (f1Fun_eq_sum d f) x
  simp only [h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun p _ => ?_)
  simp only [mul_assoc]
  rw [← Finset.mul_sum, sum_wchar_chi]
  by_cases hw : wset d p = S
  · exfalso
    have hc : (wset d p).card = S.card := by rw [hw]
    have := wset_card_le_two d p
    omega
  · rw [if_neg hw, mul_zero]

lemma deg_two_f2Fun (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (S : Finset (Cube m n d)) (hS : 2 < S.card) :
    (∑ x : Cube m n d → ZMod 2, f2Fun d f x * ∏ i ∈ S, ((-1 : ℂ) ^ (x i).val)) = 0 := by
  classical
  have hcongr : ∀ x, f2Fun d f x * (∏ i ∈ S, ((-1 : ℂ) ^ (x i).val))
      = f2Fun d f x * ∏ i ∈ S, ZMod.stdAddChar (x i) := by
    intro x
    congr 1
    exact Finset.prod_congr rfl (fun i _ => (Commons.Analysis.Walsh.stdAddChar_neg_one_pow (x i)).symm)
  rw [Finset.sum_congr rfl (fun x _ => hcongr x)]
  have h1 : ∀ x : Cube m n d → ZMod 2, f2Fun d f x = ∑ p, c2 d f p * zchar d p x :=
    fun x => congrFun (f2Fun_eq_sum d f) x
  simp only [h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun p _ => ?_)
  simp only [mul_assoc]
  rw [← Finset.mul_sum, sum_zchar_chi]
  by_cases hw : zset d p = S
  · exfalso
    have hc : (zset d p).card = S.card := by rw [hw]
    have := zset_card_le_two d p
    omega
  · rw [if_neg hw, mul_zero]

lemma l4qC_f1Fun_le (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l4qC (f1Fun d f) ≤ 81 * (l2sqC (f1Fun d f)) ^ 2 :=
  l4qC_le_of_deg_two _ (fun S hS => deg_two_f1Fun d f S hS)

lemma l4qC_f2Fun_le (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l4qC (f2Fun d f) ≤ 81 * (l2sqC (f2Fun d f)) ^ 2 :=
  l4qC_le_of_deg_two _ (fun S hS => deg_two_f2Fun d f S hS)

lemma l2sqC_f1Fun_le (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (hf : DegLe d f) :
    l2sqC (f1Fun d f) ≤ (2 : ℝ) ^ (d ^ 2) * l2sq f := by
  rw [l2sqC_f1Fun]; exact sum_dirSum_normSq_le d f hf

lemma l2sqC_f2Fun_le (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (hf : DegLe d f) :
    l2sqC (f2Fun d f) ≤ (2 : ℝ) ^ (d ^ 2) * l2sq f := by
  rw [l2sqC_f2Fun]; exact sum_dirSum_normSq_le d f hf


lemma mem_wset (d : ℕ) (p : Bd m n d × Bd m n d) (z : Cube m n d) :
    z ∈ wset d p ↔ z = (p.1, (0 : Fin 3)) ∨ z = (p.2, (1 : Fin 3)) := by
  simp [wset]

lemma mem_zset (d : ℕ) (p : Bd m n d × Bd m n d) (z : Cube m n d) :
    z ∈ zset d p ↔ z = (p.1, (2 : Fin 3)) ∨ z = (p.2, (1 : Fin 3)) := by
  simp [zset]

lemma mem_encSet (d : ℕ) (p : Bd m n d × Bd m n d) (z : Cube m n d) :
    z ∈ encSet d p ↔ z = (p.1, (0 : Fin 3)) ∨ z = (p.2, (2 : Fin 3)) := by
  simp [encSet]

lemma snd_ne {d : ℕ} {a b : Bd m n d} {i j : Fin 3} (h : i ≠ j) : (a, i) ≠ (b, j) :=
  fun hh => h (congrArg Prod.snd hh)

lemma encSet_inj (d : ℕ) {p q : Bd m n d × Bd m n d} (h : encSet d p = encSet d q) : p = q := by
  have hmem : ∀ z : Cube m n d, z ∈ encSet d p ↔ z ∈ encSet d q := fun z => by rw [h]
  have hp1 : p.1 = q.1 := by
    have h1 : (p.1, (0 : Fin 3)) ∈ encSet d q := (hmem _).mp ((mem_encSet d p _).mpr (Or.inl rfl))
    rcases (mem_encSet d q _).mp h1 with h1 | h1
    · exact congrArg (fun t : Bd m n d × Fin 3 => t.1) h1
    · exact absurd h1 (snd_ne (by decide : (0 : Fin 3) ≠ 2))
  have hp2 : p.2 = q.2 := by
    have h1 : (p.2, (2 : Fin 3)) ∈ encSet d q := (hmem _).mp ((mem_encSet d p _).mpr (Or.inr rfl))
    rcases (mem_encSet d q _).mp h1 with h1 | h1
    · exact absurd h1 (snd_ne (by decide : (2 : Fin 3) ≠ 0))
    · exact congrArg (fun t : Bd m n d × Fin 3 => t.1) h1
  exact Prod.ext hp1 hp2

lemma enc_eq_iff (d : ℕ) (p q r : Bd m n d × Bd m n d) :
    wset d p ∆ zset d q = encSet d r ↔ (p.1 = r.1 ∧ p.2 = q.2 ∧ q.1 = r.2) := by
  constructor
  · intro h
    have hmem : ∀ z : Cube m n d, z ∈ wset d p ∆ zset d q ↔ z ∈ encSet d r := fun z => by rw [h]
    have hA : (r.1, (0 : Fin 3)) ∉ zset d q := by
      rw [mem_zset]; rintro (h1 | h1)
      · exact absurd h1 (snd_ne (by decide : (0 : Fin 3) ≠ 2))
      · exact absurd h1 (snd_ne (by decide : (0 : Fin 3) ≠ 1))
    have hB : (r.2, (2 : Fin 3)) ∉ wset d p := by
      rw [mem_wset]; rintro (h1 | h1)
      · exact absurd h1 (snd_ne (by decide : (2 : Fin 3) ≠ 0))
      · exact absurd h1 (snd_ne (by decide : (2 : Fin 3) ≠ 1))
    refine ⟨?_, ?_, ?_⟩
    · have h1 : (r.1, (0 : Fin 3)) ∈ wset d p ∆ zset d q :=
        (hmem _).mpr ((mem_encSet d r _).mpr (Or.inl rfl))
      rw [Finset.mem_symmDiff] at h1
      rcases h1 with ⟨h1, _⟩ | ⟨h1, h1'⟩
      · rcases (mem_wset d p _).mp h1 with h1 | h1
        · exact (congrArg (fun t : Bd m n d × Fin 3 => t.1) h1).symm
        · exact absurd h1 (snd_ne (by decide : (0 : Fin 3) ≠ 1))
      · exact absurd h1 hA
    · by_contra hne
      have h1 : (p.2, (1 : Fin 3)) ∈ wset d p ∆ zset d q := by
        rw [Finset.mem_symmDiff]
        left
        refine ⟨(mem_wset d p _).mpr (Or.inr rfl), ?_⟩
        rw [mem_zset]
        rintro (h2 | h2)
        · exact absurd h2 (snd_ne (by decide : (1 : Fin 3) ≠ 2))
        · exact hne (congrArg (fun t : Bd m n d × Fin 3 => t.1) h2)
      rw [hmem] at h1
      rcases (mem_encSet d r _).mp h1 with h1 | h1
      · exact absurd h1 (snd_ne (by decide : (1 : Fin 3) ≠ 0))
      · exact absurd h1 (snd_ne (by decide : (1 : Fin 3) ≠ 2))
    · have h1 : (r.2, (2 : Fin 3)) ∈ wset d p ∆ zset d q :=
        (hmem _).mpr ((mem_encSet d r _).mpr (Or.inr rfl))
      rw [Finset.mem_symmDiff] at h1
      rcases h1 with ⟨h1, h1'⟩ | ⟨h1, _⟩
      · exact absurd h1 hB
      · rcases (mem_zset d q _).mp h1 with h1 | h1
        · exact (congrArg (fun t : Bd m n d × Fin 3 => t.1) h1).symm
        · exact absurd h1 (snd_ne (by decide : (2 : Fin 3) ≠ 1))
  · rintro ⟨hp1, hp2, hq1⟩
    ext z
    rw [Finset.mem_symmDiff, mem_wset, mem_zset, mem_encSet, hp1, hp2, hq1]
    have hAB : ¬ (z = (r.1, (0 : Fin 3)) ∧ z = (q.2, (1 : Fin 3))) :=
      fun hh => snd_ne (by decide : (0 : Fin 3) ≠ 1) (hh.1.symm.trans hh.2)
    have hAC : ¬ (z = (r.1, (0 : Fin 3)) ∧ z = (r.2, (2 : Fin 3))) :=
      fun hh => snd_ne (by decide : (0 : Fin 3) ≠ 2) (hh.1.symm.trans hh.2)
    have hBC : ¬ (z = (q.2, (1 : Fin 3)) ∧ z = (r.2, (2 : Fin 3))) :=
      fun hh => snd_ne (by decide : (1 : Fin 3) ≠ 2) (hh.1.symm.trans hh.2)
    tauto

lemma sum_chi3 (d : ℕ) (A B S : Finset (Cube m n d)) :
    (∑ x : Cube m n d → ZMod 2,
      (∏ i ∈ A, ZMod.stdAddChar (x i)) * (∏ i ∈ B, ZMod.stdAddChar (x i)) *
        (∏ i ∈ S, ZMod.stdAddChar (x i)))
      = if (A ∆ B) ∆ S = ∅ then (2 : ℂ) ^ Fintype.card (Cube m n d) else 0 := by
  classical
  have h : ∀ x : Cube m n d → ZMod 2,
      (∏ i ∈ A, ZMod.stdAddChar (x i)) * (∏ i ∈ B, ZMod.stdAddChar (x i)) *
        (∏ i ∈ S, ZMod.stdAddChar (x i))
      = ∏ i ∈ (A ∆ B) ∆ S, ZMod.stdAddChar (x i) := by
    intro x
    rw [show (∏ i ∈ A, ZMod.stdAddChar (x i)) * (∏ i ∈ B, ZMod.stdAddChar (x i))
        = ∏ i ∈ A ∆ B, ZMod.stdAddChar (x i) from
        Commons.Analysis.Walsh.chi_symmDiff_fintype A B x]
    exact Commons.Analysis.Walsh.chi_symmDiff_fintype (A ∆ B) S x
  rw [Finset.sum_congr rfl (fun x _ => h x), sum_chi_empty]

lemma sum_wchar_zchar_chi (d : ℕ) (p q : Bd m n d × Bd m n d) (S : Finset (Cube m n d)) :
    (∑ x : Cube m n d → ZMod 2, wchar d p x * zchar d q x * ∏ i ∈ S, ZMod.stdAddChar (x i))
      = if (wset d p ∆ zset d q) ∆ S = ∅ then (2 : ℂ) ^ Fintype.card (Cube m n d) else 0 := by
  classical
  have h : ∀ x, wchar d p x * zchar d q x * (∏ i ∈ S, ZMod.stdAddChar (x i))
      = (∏ i ∈ wset d p, ZMod.stdAddChar (x i)) * (∏ i ∈ zset d q, ZMod.stdAddChar (x i)) *
          (∏ i ∈ S, ZMod.stdAddChar (x i)) := by
    intro x; simp only [wchar, zchar]
  rw [Finset.sum_congr rfl (fun x _ => h x)]
  exact sum_chi3 d (wset d p) (zset d q) S

lemma wset_sum_condition (d : ℕ) (p q r : Bd m n d × Bd m n d) :
    ((wset d p ∆ zset d q) ∆ encSet d r = ∅) ↔ (p.1 = r.1 ∧ p.2 = q.2 ∧ q.1 = r.2) := by
  rw [Finset.symmDiff_eq_empty]
  exact enc_eq_iff d p q r

lemma sum_prod_expand {ι α : Type*} [Fintype ι] [Fintype α]
    (A : α → ι → ℂ) (B : α → ι → ℂ) (C : ι → ℂ) :
    (∑ x : ι, (∑ p, A p x) * (∑ q, B q x) * C x)
      = ∑ p, ∑ q, ∑ x, A p x * B q x * C x := by
  have h : ∀ x : ι, (∑ p, A p x) * (∑ q, B q x) * C x
      = ∑ p, ∑ q, A p x * B q x * C x := by
    intro x
    have e1 : (∑ p, A p x) * (∑ q, B q x) = ∑ p, ∑ q, A p x * B q x := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun p _ => by rw [Finset.mul_sum])
    rw [e1, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun p _ => by rw [Finset.sum_mul])
  rw [Finset.sum_congr rfl (fun x _ => h x)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  exact Finset.sum_comm

lemma sum4_collapse {α : Type*} [Fintype α] [DecidableEq α]
    (F : α → α → α → α → ℂ) (a₀ b₀ : α) (Z : ℂ) :
    (∑ x₁ : α, ∑ x₂ : α, ∑ y₁ : α, ∑ y₂ : α,
        F x₁ x₂ y₁ y₂ * (if x₁ = a₀ ∧ x₂ = y₂ ∧ y₁ = b₀ then Z else 0))
      = Z * ∑ t : α, F a₀ t b₀ t := by
  classical
  rw [Finset.sum_eq_single a₀]
  · rw [Finset.sum_comm, Finset.sum_eq_single b₀]
    · simp only [eq_self_iff_true, true_and, and_true]
      have h2 : ∀ x₂ y₂ : α, F a₀ x₂ b₀ y₂ * (if x₂ = y₂ then Z else 0)
          = (if x₂ = y₂ then F a₀ x₂ b₀ y₂ * Z else 0) := by
        intro x₂ y₂
        by_cases h : x₂ = y₂ <;> simp [h]
      have h3 : ∀ x₂ : α, (∑ y₂, (if x₂ = y₂ then F a₀ x₂ b₀ y₂ * Z else 0))
          = F a₀ x₂ b₀ x₂ * Z := by
        intro x₂
        rw [Finset.sum_eq_single x₂]
        · rw [if_pos rfl]
        · intro y₂ _ hy; rw [if_neg (Ne.symm hy)]
        · intro h; exact absurd (Finset.mem_univ x₂) h
      simp only [h2, h3]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t _ => mul_comm _ _)
    · intro y₁ _ hy
      refine Finset.sum_eq_zero (fun x₂ _ => Finset.sum_eq_zero (fun y₂ _ => ?_))
      rw [if_neg (fun hh => hy hh.2.2), mul_zero]
    · intro h; exact absurd (Finset.mem_univ b₀) h
  · intro x₁ _ hx
    refine Finset.sum_eq_zero (fun x₂ _ => Finset.sum_eq_zero (fun y₁ _ =>
      Finset.sum_eq_zero (fun y₂ _ => ?_)))
    rw [if_neg (fun hh => hx hh.1), mul_zero]
  · intro h; exact absurd (Finset.mem_univ a₀) h

/-- The normalised Walsh--Fourier coefficient on the encoding cube. -/
def chat (d : ℕ) (g : (Cube m n d → ZMod 2) → ℂ) (S : Finset (Cube m n d)) : ℂ :=
  ((2 : ℂ) ^ Fintype.card (Cube m n d))⁻¹ * ∑ x, g x * ∏ i ∈ S, ZMod.stdAddChar (x i)

lemma sum_normSq_chat (d : ℕ) (g : (Cube m n d → ZMod 2) → ℂ) :
    (∑ S : Finset (Cube m n d), ‖chat d g S‖ ^ 2) = l2sqC g := by
  unfold chat l2sqC
  exact Commons.Analysis.Walsh.parseval_fintype g

lemma chat_f1f2 (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (r : Bd m n d × Bd m n d) :
    chat d (fun x => f1Fun d f x * f2Fun d f x) (encSet d r)
      = ∑ X' : Bd m n d, c1 d f (r.1, X') * c2 d f (r.2, X') := by
  classical
  have h1 : ∀ x : Cube m n d → ZMod 2,
      f1Fun d f x = ∑ p : Bd m n d × Bd m n d, c1 d f p * wchar d p x :=
    fun x => congrFun (f1Fun_eq_sum d f) x
  have h2 : ∀ x : Cube m n d → ZMod 2,
      f2Fun d f x = ∑ q : Bd m n d × Bd m n d, c2 d f q * zchar d q x :=
    fun x => congrFun (f2Fun_eq_sum d f) x
  have step2 : ∀ p q : Bd m n d × Bd m n d,
      (∑ x, wchar d p x * zchar d q x * ∏ i ∈ encSet d r, ZMod.stdAddChar (x i))
        = if p.1 = r.1 ∧ p.2 = q.2 ∧ q.1 = r.2 then
            (2 : ℂ) ^ Fintype.card (Cube m n d) else 0 := by
    intro p q
    rw [sum_wchar_zchar_chi]
    by_cases hc : p.1 = r.1 ∧ p.2 = q.2 ∧ q.1 = r.2
    · rw [if_pos hc, if_pos ((wset_sum_condition d p q r).mpr hc)]
    · rw [if_neg hc, if_neg (fun hh => hc ((wset_sum_condition d p q r).mp hh))]
  have key : (∑ x : Cube m n d → ZMod 2, f1Fun d f x * f2Fun d f x *
        ∏ i ∈ encSet d r, ZMod.stdAddChar (x i))
      = (2 : ℂ) ^ Fintype.card (Cube m n d) *
          ∑ X' : Bd m n d, c1 d f (r.1, X') * c2 d f (r.2, X') := by
    have step1 : (∑ x : Cube m n d → ZMod 2, f1Fun d f x * f2Fun d f x *
          ∏ i ∈ encSet d r, ZMod.stdAddChar (x i))
        = ∑ p : Bd m n d × Bd m n d, ∑ q : Bd m n d × Bd m n d, c1 d f p * c2 d f q *
            (∑ x, wchar d p x * zchar d q x * ∏ i ∈ encSet d r,
              ZMod.stdAddChar (x i)) := by
      have e : (∑ x : Cube m n d → ZMod 2, f1Fun d f x * f2Fun d f x *
            ∏ i ∈ encSet d r, ZMod.stdAddChar (x i))
          = ∑ x, (∑ p, c1 d f p * wchar d p x) * (∑ q, c2 d f q * zchar d q x) *
              (∏ i ∈ encSet d r, ZMod.stdAddChar (x i)) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [h1 x, h2 x]
      rw [e, sum_prod_expand (fun p x => c1 d f p * wchar d p x)
        (fun q x => c2 d f q * zchar d q x)
        (fun x => ∏ i ∈ encSet d r, ZMod.stdAddChar (x i))]
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [step1]
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => by rw [step2 p q]))]
    simp only [Fintype.sum_prod_type]
    exact sum4_collapse (fun x₁ x₂ y₁ y₂ => c1 d f (x₁, x₂) * c2 d f (y₁, y₂)) r.1 r.2
      ((2 : ℂ) ^ Fintype.card (Cube m n d))
  unfold chat
  rw [key, inv_mul_cancel_left₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))]

/-- The contribution of a triple `(Y',Z',X')`: the absolute value of the corresponding term of
`f₁ · f₂`. -/
def W3 (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (t : (Bd m n d × Bd m n d) × Bd m n d) : ℝ :=
  ‖c1 d f (t.1.1, t.2) * c2 d f (t.1.2, t.2)‖

/-- `∑_{X'} ‖c₁(p) ‖c₂(p)‖`: the value of the encoding at the pair `p`. -/
def Tfac (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (p : Bd m n d × Bd m n d) : ℝ :=
  ∑ X' : Bd m n d, W3 d f (p, X')

lemma Tfac_nonneg (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (p : Bd m n d × Bd m n d) :
    0 ≤ Tfac d f p :=
  Finset.sum_nonneg (fun X' _ => norm_nonneg _)

lemma W3_nonneg (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (t : (Bd m n d × Bd m n d) × Bd m n d) : 0 ≤ W3 d f t := norm_nonneg _

lemma c1c2_coe (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (p : Bd m n d × Bd m n d)
    (X' : Bd m n d) :
    c1 d f (p.1, X') * c2 d f (p.2, X')
      = ((‖c1 d f (p.1, X') * c2 d f (p.2, X')‖ : ℝ) : ℂ) := by
  unfold c1 c2
  by_cases h1 : dirSum p.1.1 X'.1
  · by_cases h2 : dirSum p.2.1 X'.1
    · simp only [if_pos h1, if_pos h2]
      rw [← Complex.ofReal_mul]
      rw [Complex.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    · simp only [if_pos h1, if_neg h2, mul_zero, norm_zero, Complex.ofReal_zero]
  · simp only [if_neg h1, zero_mul, norm_zero, Complex.ofReal_zero]

lemma norm_chat_f1f2 (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (p : Bd m n d × Bd m n d) :
    ‖chat d (fun x => f1Fun d f x * f2Fun d f x) (encSet d p)‖ = Tfac d f p := by
  have hsum : (∑ X' : Bd m n d, c1 d f (p.1, X') * c2 d f (p.2, X'))
      = ((∑ X' : Bd m n d, ‖c1 d f (p.1, X') * c2 d f (p.2, X')‖ : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun X' _ => c1c2_coe d f p X'), ← Complex.ofReal_sum]
  rw [chat_f1f2, hsum, Tfac]
  exact Complex.norm_of_nonneg (Finset.sum_nonneg (fun X' _ => norm_nonneg _))

lemma sum_Tfac_sq_le (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (∑ p : Bd m n d × Bd m n d, (Tfac d f p) ^ 2)
      ≤ l2sqC (fun x : Cube m n d → ZMod 2 => f1Fun d f x * f2Fun d f x) := by
  rw [← sum_normSq_chat d (fun x : Cube m n d → ZMod 2 => f1Fun d f x * f2Fun d f x)]
  rw [Finset.sum_congr rfl (fun p _ => by rw [← norm_chat_f1f2 d f p])]
  rw [← Finset.sum_image (s := Finset.univ) (g := encSet d)
    (f := fun S : Finset (Cube m n d) =>
      ‖chat d (fun x : Cube m n d → ZMod 2 => f1Fun d f x * f2Fun d f x) S‖ ^ 2)
    (fun a _ b _ hab => encSet_inj d hab)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun S _ _ => by positivity)

/-- The witness triple for a pair in `𝓕₁(X)`. -/
noncomputable def wit3 (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) (p : Bd m n d × Bd m n d) :
    (Bd m n d × Bd m n d) × Bd m n d :=
  if h : ∃ t : (Bd m n d × Bd m n d) × Bd m n d,
      p.1.1 = t.1.1.1 + t.2.1 ∧ p.2.1 = t.1.2.1 + t.2.1 ∧ t.1.1.1 + t.1.2.1 = X ∧
        dirSum t.1.1.1 t.2.1 ∧ dirSum t.1.2.1 t.2.1 ∧ dirSum t.1.1.1 t.1.2.1
    then Classical.choose h else ((p.1, p.2), p.1)

lemma exists_wit3 {d : ℕ} {X : Matrix (Fin n) (Fin m) 𝔽₂} {p : Bd m n d × Bd m n d}
    (h : IsF1D X p.1.1 p.2.1) :
    ∃ t : (Bd m n d × Bd m n d) × Bd m n d,
      p.1.1 = t.1.1.1 + t.2.1 ∧ p.2.1 = t.1.2.1 + t.2.1 ∧ t.1.1.1 + t.1.2.1 = X ∧
        dirSum t.1.1.1 t.2.1 ∧ dirSum t.1.2.1 t.2.1 ∧ dirSum t.1.1.1 t.1.2.1 := by
  obtain ⟨Y', Z', hY, hZ, hd, hX⟩ := h.2
  have hYr : Y'.rank ≤ d := by
    have h1 : Y'.rank ≤ p.1.1.rank := by rw [hY]; exact Nat.le_add_right _ _
    exact le_trans h1 p.1.2
  have hZr : Z'.rank ≤ d := by
    have h1 : Z'.rank ≤ p.2.1.rank := by rw [hZ]; exact Nat.le_add_right _ _
    exact le_trans h1 p.2.2
  have hXr : (p.1.1 - Y').rank ≤ d := by
    have h1 : (p.1.1 - Y').rank ≤ p.1.1.rank := by rw [hY]; exact Nat.le_add_left _ _
    exact le_trans h1 p.1.2
  have hsub : p.1.1 - Y' = p.2.1 - Z' := by
    simp only [sub_eq_add_neg, mtx_neg_eq]
    have key : (p.1.1 + Y') + (p.2.1 + Z') = 0 := by
      have h0 : (Y' + Z') + (p.1.1 + p.2.1) = 0 := by rw [hX, h.1, mtx_add_self]
      rw [← h0]; abel
    rw [add_eq_zero_iff_eq_neg, mtx_neg_eq] at key
    exact key
  refine ⟨((⟨Y', hYr⟩, ⟨Z', hZr⟩), ⟨p.1.1 - Y', hXr⟩), ?_, ?_, hX, ?_, ?_, hd⟩
  · show p.1.1 = Y' + (p.1.1 - Y')
    rw [add_sub_cancel_zmod']
  · show p.2.1 = Z' + (p.1.1 - Y')
    rw [hsub, add_sub_cancel_zmod']
  · show (Y' + (p.1.1 - Y')).rank = Y'.rank + (p.1.1 - Y').rank
    rw [add_sub_cancel_zmod', hY]
  · show (Z' + (p.1.1 - Y')).rank = Z'.rank + (p.1.1 - Y').rank
    rw [hsub, add_sub_cancel_zmod', hZ]

lemma wit3_spec {d : ℕ} {X : Matrix (Fin n) (Fin m) 𝔽₂} {p : Bd m n d × Bd m n d}
    (h : IsF1D X p.1.1 p.2.1) :
    p.1.1 = (wit3 d X p).1.1.1 + (wit3 d X p).2.1 ∧
      p.2.1 = (wit3 d X p).1.2.1 + (wit3 d X p).2.1 ∧
      (wit3 d X p).1.1.1 + (wit3 d X p).1.2.1 = X ∧
      dirSum (wit3 d X p).1.1.1 (wit3 d X p).2.1 ∧
      dirSum (wit3 d X p).1.2.1 (wit3 d X p).2.1 ∧
      dirSum (wit3 d X p).1.1.1 (wit3 d X p).1.2.1 := by
  have h1 := exists_wit3 h
  unfold wit3
  rw [dif_pos h1]
  exact Classical.choose_spec h1

lemma wit3_inj (d : ℕ) {X : Matrix (Fin n) (Fin m) 𝔽₂} {p q : Bd m n d × Bd m n d}
    (hp : IsF1D X p.1.1 p.2.1) (hq : IsF1D X q.1.1 q.2.1)
    (h : wit3 d X p = wit3 d X q) : p = q := by
  obtain ⟨h1p, h2p, _, _, _, _⟩ := wit3_spec hp
  obtain ⟨h1q, h2q, _, _, _, _⟩ := wit3_spec hq
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [h1p, h1q, h]
  · rw [h2p, h2q, h]

lemma W3_wit3 (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    {X : Matrix (Fin n) (Fin m) 𝔽₂} {p : Bd m n d × Bd m n d} (h : IsF1D X p.1.1 p.2.1) :
    W3 d f (wit3 d X p) = ‖fcoeff f p.1.1‖ * ‖fcoeff f p.2.1‖ := by
  obtain ⟨h1, h2, _, hd1, hd2, _⟩ := wit3_spec h
  have e1 : c1 d f ((wit3 d X p).1.1, (wit3 d X p).2) = ((‖fcoeff f p.1.1‖ : ℝ) : ℂ) := by
    unfold c1
    rw [if_pos hd1, ← h1]
  have e2 : c2 d f ((wit3 d X p).1.2, (wit3 d X p).2) = ((‖fcoeff f p.2.1‖ : ℝ) : ℂ) := by
    unfold c2
    rw [if_pos hd2, ← h2]
  rw [W3, e1, e2, Complex.norm_mul, Complex.norm_of_nonneg (norm_nonneg _),
    Complex.norm_of_nonneg (norm_nonneg _)]

lemma wit3_mem (d : ℕ) {X : Matrix (Fin n) (Fin m) 𝔽₂} {p : Bd m n d × Bd m n d}
    (h : IsF1D X p.1.1 p.2.1) :
    dirSum (wit3 d X p).1.1.1 (wit3 d X p).1.2.1 ∧
      (wit3 d X p).1.1.1 + (wit3 d X p).1.2.1 = X := by
  obtain ⟨_, _, h3, _, _, hd3⟩ := wit3_spec h
  exact ⟨hd3, h3⟩

/-- The set of admissible triples for `X`: `Y' ⊕ Z' = X` in `B(d)`. -/
def Sx (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) : Finset ((Bd m n d × Bd m n d) × Bd m n d) :=
  Finset.univ.filter (fun t => dirSum t.1.1.1 t.1.2.1 ∧ t.1.1.1 + t.1.2.1 = X)

lemma sum_Sx_eq (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    (∑ t ∈ Sx d X, W3 d f t) = ∑ p' : Bd m n d × Bd m n d,
      (if dirSum p'.1.1 p'.2.1 ∧ p'.1.1 + p'.2.1 = X then Tfac d f p' else 0) := by
  rw [Sx, Finset.sum_filter]
  rw [Fintype.sum_prod_type (f := fun t : (Bd m n d × Bd m n d) × Bd m n d =>
    if dirSum t.1.1.1 t.1.2.1 ∧ t.1.1.1 + t.1.2.1 = X then W3 d f t else 0)]
  refine Finset.sum_congr rfl (fun p' _ => ?_)
  by_cases hQ : dirSum p'.1.1 p'.2.1 ∧ p'.1.1 + p'.2.1 = X
  · rw [if_pos hQ]
    simp only [hQ, if_true]
    rfl
  · rw [if_neg hQ]
    exact Finset.sum_eq_zero (fun X' _ => by rw [if_neg hQ])

lemma F1Sum_le (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    F1Sum d X f ≤ ∑ t ∈ Sx d X, W3 d f t := by
  classical
  set Ps := Finset.univ.filter (fun p : Bd m n d × Bd m n d => IsF1D X p.1.1 p.2.1) with hPs
  have step1 : F1Sum d X f = ∑ p ∈ Ps, ‖fcoeff f p.1.1‖ * ‖fcoeff f p.2.1‖ := by
    unfold F1Sum
    rw [← Fintype.sum_prod_type (f := fun p : Bd m n d × Bd m n d =>
      if IsF1D X p.1.1 p.2.1 then ‖fcoeff f p.1.1‖ * ‖fcoeff f p.2.1‖ else 0)]
    rw [← Finset.sum_filter, ← hPs]
  rw [step1]
  have step2 : (∑ p ∈ Ps, ‖fcoeff f p.1.1‖ * ‖fcoeff f p.2.1‖)
      = ∑ p ∈ Ps, W3 d f (wit3 d X p) :=
    Finset.sum_congr rfl (fun p hp => (W3_wit3 d f (Finset.mem_filter.mp hp).2).symm)
  rw [step2]
  have hinj : Set.InjOn (wit3 d X) ↑Ps := fun a ha b hb hab =>
    wit3_inj d (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
  rw [← Finset.sum_image (g := wit3 d X) (f := W3 d f) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun t _ _ => W3_nonneg d f t)
  intro t ht
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, wit3_mem d (Finset.mem_filter.mp hp).2⟩

lemma l4qC_nonneg' {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ZMod 2) → ℂ) :
    0 ≤ l4qC g :=
  mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => by positivity))

/-- Cauchy--Schwarz on the cube: `‖f g‖₂² ≤ ‖f‖₄² ‖g‖₄²`. -/
lemma sq_l2sqC_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι] (g h : (ι → ZMod 2) → ℂ) :
    (l2sqC (fun x => g x * h x)) ^ 2 ≤ l4qC g * l4qC h := by
  have hpq : (∑ x, ‖g x * h x‖ ^ 2) ^ 2 ≤ (∑ x, ‖g x‖ ^ 4) * (∑ x, ‖h x‖ ^ 4) := by
    have h2 : ∀ x, ‖g x * h x‖ ^ 2 = ‖g x‖ ^ 2 * ‖h x‖ ^ 2 := by
      intro x; rw [norm_mul, mul_pow]
    have h3 : ∀ x, (‖g x‖ ^ 2) ^ 2 = ‖g x‖ ^ 4 := fun x => by ring
    have h4 : ∀ x, (‖h x‖ ^ 2) ^ 2 = ‖h x‖ ^ 4 := fun x => by ring
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι → ZMod 2))
      (fun x => ‖g x‖ ^ 2) (fun x => ‖h x‖ ^ 2)
    rw [Finset.sum_congr rfl (fun x _ => h2 x)]
    refine le_trans hCS (le_of_eq ?_)
    rw [Finset.sum_congr rfl (fun x _ => h3 x), Finset.sum_congr rfl (fun x _ => h4 x)]
  unfold l2sqC l4qC
  have hnn : (0:ℝ) ≤ ((2:ℝ) ^ Fintype.card ι)⁻¹ ^ 2 := by positivity
  calc (((2 : ℝ) ^ Fintype.card ι)⁻¹ * ∑ x, ‖g x * h x‖ ^ 2) ^ 2
      = ((2 : ℝ) ^ Fintype.card ι)⁻¹ ^ 2 * (∑ x, ‖g x * h x‖ ^ 2) ^ 2 := by ring
    _ ≤ ((2 : ℝ) ^ Fintype.card ι)⁻¹ ^ 2 *
          ((∑ x, ‖g x‖ ^ 4) * (∑ x, ‖h x‖ ^ 4)) :=
        mul_le_mul_of_nonneg_left hpq hnn
    _ = (((2 : ℝ) ^ Fintype.card ι)⁻¹ * ∑ x, ‖g x‖ ^ 4) *
          (((2 : ℝ) ^ Fintype.card ι)⁻¹ * ∑ x, ‖h x‖ ^ 4) := by ring

lemma l2sqC_g1g2_le (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (hf : DegLe d f) :
    l2sqC (fun x : Cube m n d → ZMod 2 => f1Fun d f x * f2Fun d f x)
      ≤ 81 * (2 : ℝ) ^ (2 * d ^ 2) * (l2sq f) ^ 2 := by
  have h4a := l4qC_f1Fun_le d f
  have h4b := l4qC_f2Fun_le d f
  have h2a := l2sqC_f1Fun_le d f hf
  have h2b := l2sqC_f2Fun_le d f hf
  have h0a : 0 ≤ l2sqC (f1Fun d f) := l2sqC_nonneg _
  have h0b : 0 ≤ l2sqC (f2Fun d f) := l2sqC_nonneg _
  have h0f : 0 ≤ l2sq f := l2sq_nonneg f
  have hsq := sq_l2sqC_mul_le (f1Fun d f) (f2Fun d f)
  have hrhs : l4qC (f1Fun d f) * l4qC (f2Fun d f)
      ≤ (81 * (2 : ℝ) ^ (2 * d ^ 2) * (l2sq f) ^ 2) ^ 2 := by
    have e1 : l4qC (f1Fun d f) ≤ 81 * ((2 : ℝ) ^ (d ^ 2) * l2sq f) ^ 2 := by
      refine le_trans h4a ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0a h2a 2) (by norm_num)
    have e2 : l4qC (f2Fun d f) ≤ 81 * ((2 : ℝ) ^ (d ^ 2) * l2sq f) ^ 2 := by
      refine le_trans h4b ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0b h2b 2) (by norm_num)
    have e3 : ((2 : ℝ) ^ (d ^ 2) * l2sq f) ^ 2
        = (2 : ℝ) ^ (2 * d ^ 2) * (l2sq f) ^ 2 := by
      rw [mul_pow, ← pow_mul, show d ^ 2 * 2 = 2 * d ^ 2 from by ring]
    refine le_trans (mul_le_mul e1 e2 (l4qC_nonneg' _) (by positivity)) ?_
    rw [e3]
    exact le_of_eq (by ring)
  have hmain : (l2sqC (fun x : Cube m n d → ZMod 2 => f1Fun d f x * f2Fun d f x)) ^ 2
      ≤ (81 * (2 : ℝ) ^ (2 * d ^ 2) * (l2sq f) ^ 2) ^ 2 :=
    le_trans hsq hrhs
  have h0l : 0 ≤ l2sqC (fun x : Cube m n d → ZMod 2 => f1Fun d f x * f2Fun d f x) :=
    l2sqC_nonneg _
  have h0r : 0 ≤ 81 * (2 : ℝ) ^ (2 * d ^ 2) * (l2sq f) ^ 2 := by positivity
  nlinarith [hmain, h0l, h0r]

lemma card_Dx_le (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    (Finset.univ.filter (fun p' : Bd m n d × Bd m n d =>
      dirSum p'.1.1 p'.2.1 ∧ p'.1.1 + p'.2.1 = X)).card ≤ 2 ^ (4 * d * d) := by
  classical
  set Dx := Finset.univ.filter (fun p' : Bd m n d × Bd m n d =>
    dirSum p'.1.1 p'.2.1 ∧ p'.1.1 + p'.2.1 = X) with hDx
  by_cases hne : Dx.Nonempty
  · obtain ⟨p0, hp0⟩ := hne
    obtain ⟨-, hdir, hsum⟩ := Finset.mem_filter.mp hp0
    have hrank : X.rank ≤ 2 * d := by
      unfold dirSum at hdir
      rw [← hsum]
      have h1 : p0.1.1.rank ≤ d := p0.1.2
      have h2 : p0.2.1.rank ≤ d := p0.2.2
      omega
    have hcard : Dx.card ≤ Nat.card {q : Bd m n d × Bd m n d //
        q.1.1 + q.2.1 = X ∧ dirSum q.1.1 q.2.1} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      refine Finset.card_le_card ?_
      intro x hx
      obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨h1, h3, h2⟩
    refine le_trans hcard (le_trans (card_bd_pair_add_eq_le d X) ?_)
    refine pow_le_pow_right₀ (by norm_num) ?_
    calc X.rank ^ 2 ≤ (2 * d) ^ 2 := Nat.pow_le_pow_left hrank 2
      _ = 4 * d * d := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

set_option maxHeartbeats 4000000 in
lemma F1Bound_of (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (hf : DegLe d f) :
    F1Bound d f := by
  classical
  unfold F1Bound
  have h1 : ∀ X : Matrix (Fin n) (Fin m) 𝔽₂, (F1Sum d X f) ^ 2 ≤ (2 : ℝ) ^ (4 * d * d) *
      ∑ p' : Bd m n d × Bd m n d,
        (if dirSum p'.1.1 p'.2.1 ∧ p'.1.1 + p'.2.1 = X then (Tfac d f p') ^ 2 else 0) := by
    intro X
    set Dx := Finset.univ.filter (fun p' : Bd m n d × Bd m n d =>
      dirSum p'.1.1 p'.2.1 ∧ p'.1.1 + p'.2.1 = X) with hDx
    have hle : F1Sum d X f ≤ ∑ p' ∈ Dx, Tfac d f p' := by
      have h := F1Sum_le d f X
      have h2 : (∑ t ∈ Sx d X, W3 d f t) = ∑ p' ∈ Dx, Tfac d f p' := by
        rw [sum_Sx_eq d f X, hDx, Finset.sum_filter]
      rwa [h2] at h
    have hsq := sq_sum_le_card_mul_sum_sq (s := Dx) (f := fun p' => Tfac d f p')
    have hcard := card_Dx_le d X
    have hstep : (F1Sum d X f) ^ 2 ≤ Dx.card * ∑ p' ∈ Dx, (Tfac d f p') ^ 2 := by
      refine le_trans (pow_le_pow_left₀ (F1Sum_nonneg d X f) hle 2) ?_
      simpa using hsq
    have hcard' : (Dx.card : ℝ) ≤ (2 : ℝ) ^ (4 * d * d) := by
      have hcx := hcard
      rw [← hDx] at hcx
      exact_mod_cast hcx
    refine le_trans hstep ?_
    have h2 : (0:ℝ) ≤ ∑ p' ∈ Dx, (Tfac d f p') ^ 2 :=
      Finset.sum_nonneg (fun p' _ => by positivity)
    calc (Dx.card : ℝ) * ∑ p' ∈ Dx, (Tfac d f p') ^ 2
        ≤ (2 : ℝ) ^ (4 * d * d) * ∑ p' ∈ Dx, (Tfac d f p') ^ 2 :=
          mul_le_mul_of_nonneg_right hcard' h2
      _ = (2 : ℝ) ^ (4 * d * d) * ∑ p' : Bd m n d × Bd m n d,
            (if dirSum p'.1.1 p'.2.1 ∧ p'.1.1 + p'.2.1 = X then (Tfac d f p') ^ 2 else 0) := by
          congr 1
          rw [hDx, Finset.sum_filter]
  have hle1 : ∀ p' : Bd m n d × Bd m n d,
      (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        (if dirSum p'.1.1 p'.2.1 ∧ p'.1.1 + p'.2.1 = X then (Tfac d f p') ^ 2 else 0))
        ≤ (Tfac d f p') ^ 2 := by
    intro p'
    have hsingle : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        (if dirSum p'.1.1 p'.2.1 ∧ p'.1.1 + p'.2.1 = X then (Tfac d f p') ^ 2 else 0))
        = (if dirSum p'.1.1 p'.2.1 then (Tfac d f p') ^ 2 else 0) := by
      rw [Finset.sum_eq_single (p'.1.1 + p'.2.1)]
      · by_cases hD : dirSum p'.1.1 p'.2.1 <;> simp [hD]
      · intro X _ hX
        rw [if_neg (fun hh => hX hh.2.symm)]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsingle]
    by_cases hD : dirSum p'.1.1 p'.2.1
    · simp only [hD, if_true, le_refl]
    · simp only [hD, if_false]
      positivity
  have h2 : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, (F1Sum d X f) ^ 2)
      ≤ (2 : ℝ) ^ (4 * d * d) * ∑ p' : Bd m n d × Bd m n d, (Tfac d f p') ^ 2 := by
    calc (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, (F1Sum d X f) ^ 2)
        ≤ ∑ X, (2 : ℝ) ^ (4 * d * d) * ∑ p' : Bd m n d × Bd m n d,
            (if dirSum p'.1.1 p'.2.1 ∧ p'.1.1 + p'.2.1 = X then (Tfac d f p') ^ 2 else 0) :=
          Finset.sum_le_sum (fun X _ => h1 X)
      _ = (2 : ℝ) ^ (4 * d * d) * ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
            ∑ p' : Bd m n d × Bd m n d,
              (if dirSum p'.1.1 p'.2.1 ∧ p'.1.1 + p'.2.1 = X then (Tfac d f p') ^ 2 else 0) := by
          rw [Finset.mul_sum]
      _ = (2 : ℝ) ^ (4 * d * d) * ∑ p' : Bd m n d × Bd m n d,
            ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
              (if dirSum p'.1.1 p'.2.1 ∧ p'.1.1 + p'.2.1 = X then (Tfac d f p') ^ 2 else 0) := by
          rw [Finset.sum_comm]
      _ ≤ (2 : ℝ) ^ (4 * d * d) * ∑ p' : Bd m n d × Bd m n d, (Tfac d f p') ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p' _ => hle1 p')) (by positivity)
  refine le_trans h2 ?_
  have h3 : (∑ p' : Bd m n d × Bd m n d, (Tfac d f p') ^ 2)
      ≤ l2sqC (fun x : Cube m n d → ZMod 2 => f1Fun d f x * f2Fun d f x) :=
    sum_Tfac_sq_le d f
  have h4 := l2sqC_g1g2_le d f hf
  have h5 : (0:ℝ) < (2 : ℝ) ^ (4 * d * d) := by positivity
  calc (2 : ℝ) ^ (4 * d * d) * ∑ p' : Bd m n d × Bd m n d, (Tfac d f p') ^ 2
      ≤ (2 : ℝ) ^ (4 * d * d) *
          l2sqC (fun x : Cube m n d → ZMod 2 => f1Fun d f x * f2Fun d f x) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ (2 : ℝ) ^ (4 * d * d) * (81 * (2 : ℝ) ^ (2 * d ^ 2) * (l2sq f) ^ 2) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 81 * (2 : ℝ) ^ (6 * d ^ 2) * (l2sq f) ^ 2 := by
        rw [show (6:ℕ) * d ^ 2 = 4 * d * d + 2 * d ^ 2 from by ring, pow_add]
        ring

end

end Submission.Grassmann
