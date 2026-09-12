import Mathlib
import Submission.GeoBridge

set_option autoImplicit false
set_option linter.style.haveILetI false
open MeasureTheory InnerProductSpace
open scoped BigOperators

noncomputable section

/-!
# Measurable unit normal to the span of the first `n−1` columns

Tikhomirov 2020, proof of Theorem A: the incompressible part of the small-ball
probability is reduced (RV 2007, formula (eq: comp-incomp)) to probabilities
involving a *random unit normal* `Y_n` to the linear span of the first `n−1`
columns of the random matrix.  `Y_n` must be a measurable function of the
first `n−1` columns (so that it is independent of the last column, whose
entries are independent of the rest).

## Target statements

1. *Deterministic Gram–Schmidt extension.*  In a real inner-product space
   `E` of dimension `n`, given columns `c : Fin (n−1) → E` and an orthonormal
   basis `b : Fin n → E` of `E`, the Gram–Schmidt outputs of the concatenated
   family `(c, b)` (Mathlib `gramSchmidtNormed`) that lie in the `b`-positions
   are unit vectors orthogonal to `span (range c)`; their average
   `w := Σ_j g_{n−1+j}` has `‖w‖ ≥ 1` (at least one of them is nonzero since
   `span (range c)` has dimension at most `n−1`), so `Y := w / ‖w‖` is a unit
   vector in the orthogonal complement of `span (range c)`.

2. *Measurability.*  If the columns are measurable functions `c i : Ω → E`,
   then `gramSchmidtNormed` applied to `(c, b)` at any fixed position, and
   hence `Y : Ω → E`, is measurable (proved by induction on the position
   using the explicit formula
   `gramSchmidt f n = f n - Σ i < n, (span {gramSchmidt f i}).starProjection (f n)`
   and `Submodule.starProjection_singleton`).

3. *Geometry.*  For a unit vector `Y ⊥ span (range c)` and any `x : E`,
   `|⟪x, Y⟫| ≤ dist x (span (range c))`; applied to `x := col_n` and the
   columns `c := (col_1, …, col_{n−1})` of a matrix `A`, together with
   `dist col_n V · |f_n| ≤ ‖A f‖` (from the orthogonal decomposition of
   `A f`), this yields the deterministic inclusion used in the paper.
-/

namespace Submission.UnitNormal

namespace GramSchmidtExtension

variable {n : ℕ}

/-- The concatenated family: columns first, then the basis vectors. -/
def extFam {n : ℕ} (E : Type*) [NormedAddCommGroup E] (b : Fin n → E) (c : Fin (n - 1) → E)
    (i : Fin (2 * n - 1)) : E :=
  if hlt : i.val < n - 1 then
    c ⟨i.val, hlt⟩
  else
    b ⟨i.val - (n - 1), by
      have hge : n - 1 ≤ i.val := Nat.le_of_not_gt hlt
      omega⟩

/-- The normalized Gram–Schmidt outputs of the extended family. -/
def gs {n : ℕ} (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Fin n → E) (c : Fin (n - 1) → E) (i : Fin (2 * n - 1)) : E :=
  InnerProductSpace.gramSchmidtNormed ℝ (extFam E b c) i

/-- The position of basis vector `j` in the extended family (at index `n−1+j`). -/
def bpos {n : ℕ} (j : Fin n) : Fin (2 * n - 1) :=
  ⟨n - 1 + j.val, by omega⟩

/-- Sum of the `b`-position outputs (positions `n−1 … 2n−2`). -/
def gsSumB {n : ℕ} (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Fin n → E) (c : Fin (n - 1) → E) : E :=
  ∑ j : Fin n, gs E b c (bpos j)

/-- The candidate unit normal. -/
def unitNormal {n : ℕ} (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Fin n → E) (c : Fin (n - 1) → E) : E :=
  (‖gsSumB E b c‖)⁻¹ • gsSumB E b c



/-- At a basis position the extended family returns the basis vector. -/
lemma extFam_bpos {n : ℕ} (E : Type*) [NormedAddCommGroup E] (b : Fin n → E)
    (c : Fin (n - 1) → E) (j : Fin n) : extFam E b c (bpos j) = b j := by
  dsimp [extFam, bpos]
  by_cases h : n - 1 + j.val < n - 1
  · omega
  · simp [h]

/-- `b j` belongs to the range of the extended family. -/
lemma b_mem_range_extFam {n : ℕ} (E : Type*) [NormedAddCommGroup E] (b : Fin n → E)
    (c : Fin (n - 1) → E) (j : Fin n) : b j ∈ Set.range (extFam E b c) := by
  refine ⟨bpos j, ?_⟩
  exact extFam_bpos E b c j



/-- At a column position the extended family returns the column vector. -/
lemma extFam_col {n : ℕ} (E : Type*) [NormedAddCommGroup E] (b : Fin n → E)
    (c : Fin (n - 1) → E) {i : Fin (2 * n - 1)} (hcol : i.val < n - 1) :
    extFam E b c i = c ⟨i.val, hcol⟩ := by
  dsimp [extFam]
  simp [hcol]

/-- The Gram–Schmidt output at a column position lies in the span of the
columns (which, at a column position, is all that has been seen). -/
lemma gramSchmidt_col_mem_span_col {n : ℕ} (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : Fin n → E) (c : Fin (n - 1) → E)
    {i : Fin (2 * n - 1)} (hcol : i.val < n - 1) :
    InnerProductSpace.gramSchmidt ℝ (extFam E b c) i ∈
      Submodule.span ℝ (Set.range c) := by
  let V : Submodule ℝ E := Submodule.span ℝ (Set.range c)
  have hmem := InnerProductSpace.gramSchmidt_mem_span ℝ (extFam E b c) (j := i) (i := i) le_rfl
  -- hmem : gramSchmidt f i ∈ span (f '' Iic i)
  have hsubimg : extFam E b c '' Set.Iic i ⊆ Set.range c := by
    rintro x ⟨k, hkIic, rfl⟩
    have hkval : k.val ≤ i.val := hkIic
    have hkcol : k.val < n - 1 := lt_of_le_of_lt hkval hcol
    exact ⟨⟨k.val, hkcol⟩, by
      rw [extFam_col E b c hkcol]⟩
  have hmono : Submodule.span ℝ (extFam E b c '' Set.Iic i) ≤ V := by
    exact Submodule.span_mono hsubimg
  exact hmono hmem

/-- The normalized Gram–Schmidt output at a column position lies in the span
of the columns. -/
lemma gs_col_mem_span_col {n : ℕ} (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : Fin n → E) (c : Fin (n - 1) → E)
    {i : Fin (2 * n - 1)} (hcol : i.val < n - 1) :
    gs E b c i ∈ Submodule.span ℝ (Set.range c) := by
  let V : Submodule ℝ E := Submodule.span ℝ (Set.range c)
  have hg := gramSchmidt_col_mem_span_col E b c hcol
  -- gs i = (‖gramSchmidt i‖)⁻¹ • gramSchmidt i
  dsimp [gs]
  exact Submodule.smul_mem V (‖InnerProductSpace.gramSchmidt ℝ (extFam E b c) i‖)⁻¹ hg

/-- If the basis-position outputs all vanish then every output lies in the
span of the columns (each basis vector would then be forced into it). -/
lemma gs_mem_span_col_of_all_zero {n : ℕ} (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : Fin n → E) (c : Fin (n - 1) → E)
    (hzero : ∀ j : Fin n, gs E b c (bpos j) = 0) :
    ∀ i : Fin (2 * n - 1), gs E b c i ∈ Submodule.span ℝ (Set.range c) := by
  intro i
  by_cases hcol : i.val < n - 1
  · exact gs_col_mem_span_col E b c hcol
  · -- i is a basis position
    have hge : n - 1 ≤ i.val := Nat.le_of_not_gt hcol
    let j : Fin n := ⟨i.val - (n - 1), by
      have hltn : i.val < 2 * n - 1 := i.isLt
      omega⟩
    have hpos : i = bpos j := by
      apply Fin.ext
      simp [bpos, j]
      omega
    rw [hpos]
    rw [hzero j]
    exact Submodule.zero_mem _


/-- `bpos` is injective. -/
lemma bpos_injective {n : ℕ} {j k : Fin n} (h : bpos j = bpos k) : j = k := by
  apply Fin.ext
  have hv : (bpos j).val = (bpos k).val := congrArg Fin.val h
  dsimp [bpos] at hv
  omega

/-- The normalized Gram–Schmidt outputs are pairwise orthogonal (zero
outputs included). -/
lemma gs_pair_inner_zero {n : ℕ} (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Fin n → E) (c : Fin (n - 1) → E) {i k : Fin (2 * n - 1)} (hik : i ≠ k) :
    inner ℝ (gs E b c i) (gs E b c k) = 0 := by
  have h := InnerProductSpace.gramSchmidt_orthogonal ℝ (extFam E b c) hik
  -- gs are scalar multiples of orthogonal Gram–Schmidt vectors
  calc
    inner ℝ (gs E b c i) (gs E b c k)
        = inner ℝ ((‖InnerProductSpace.gramSchmidt ℝ (extFam E b c) i‖)⁻¹ •
              InnerProductSpace.gramSchmidt ℝ (extFam E b c) i)
            ((‖InnerProductSpace.gramSchmidt ℝ (extFam E b c) k‖)⁻¹ •
              InnerProductSpace.gramSchmidt ℝ (extFam E b c) k) := by
          rfl
    _ = 0 := by
      rw [inner_smul_left]
      rw [inner_smul_right]
      simp [h]

/-- Some basis-position Gram–Schmidt output is non-zero (the columns span a
space of dimension at most `n−1 < n`, while the extended family spans `E`). -/
lemma exists_ne_zero_bpos {n : ℕ} (hn : 1 ≤ n) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Module.Finite ℝ E] (b : OrthonormalBasis (Fin n) ℝ E)
    (c : Fin (n - 1) → E) : ∃ j : Fin n, gs E (fun j => b j) c (bpos j) ≠ 0 := by
  let β : Fin n → E := fun j => b j
  by_contra h
  have hall : ∀ j : Fin n, gs E β c (bpos j) = 0 := by
    intro j
    by_contra hne
    exact h ⟨j, hne⟩
  let V : Submodule ℝ E := Submodule.span ℝ (Set.range c)
  -- every Gram–Schmidt output lies in the span of the columns
  have hmem : ∀ i : Fin (2 * n - 1), gs E β c i ∈ V := by
    intro i
    by_cases hcol : i.val < n - 1
    · exact gs_col_mem_span_col E β c hcol
    · have hge : n - 1 ≤ i.val := Nat.le_of_not_gt hcol
      let j : Fin n := ⟨i.val - (n - 1), by omega⟩
      have hpos : i = bpos j := by
        apply Fin.ext
        simp [bpos, j]
        omega
      rw [hpos]
      rw [hall j]
      exact Submodule.zero_mem V
  -- the outputs span all of E
  have hspan_ext_top : Submodule.span ℝ (Set.range (extFam E β c)) = ⊤ := by
    apply le_antisymm (le_top)
    have hmono : Submodule.span ℝ (Set.range β) ≤
        Submodule.span ℝ (Set.range (extFam E β c)) := by
      exact Submodule.span_mono (by
        rintro y ⟨j, rfl⟩
        exact b_mem_range_extFam E β c j)
    have htop : Submodule.span ℝ (Set.range β) = ⊤ := by
      simpa [β] using b.toBasis.span_eq
    simpa [htop] using hmono
  have hspan_gs_eq : Submodule.span ℝ (Set.range (gs E β c)) =
      Submodule.span ℝ (Set.range (extFam E β c)) := by
    have hgs : gs E β c = InnerProductSpace.gramSchmidtNormed ℝ (extFam E β c) := by
      funext i
      rfl
    rw [hgs]
    exact (InnerProductSpace.span_gramSchmidtNormed_range (𝕜 := ℝ) (extFam E β c)).trans
      (InnerProductSpace.span_gramSchmidt (𝕜 := ℝ) (extFam E β c))
  have htop_le_V : (⊤ : Submodule ℝ E) ≤ V := by
    have hspan_le_V : Submodule.span ℝ (Set.range (gs E β c)) ≤ V := by
      exact Submodule.span_le.mpr (by
        rintro y ⟨i, rfl⟩
        exact hmem i)
    have : Submodule.span ℝ (Set.range (gs E β c)) = ⊤ := by
      rw [hspan_gs_eq, hspan_ext_top]
    simpa [this] using hspan_le_V
  have hVtop : V = ⊤ := le_antisymm le_top htop_le_V
  -- finrank contradiction: n = finrank E ≤ finrank V ≤ n−1
  have hfinVle : Module.finrank ℝ ↥V ≤ n - 1 := by
    classical
    letI : Fintype (Set.range c) := (Set.finite_range c).fintype
    have h1 := finrank_span_le_card (R := ℝ) (M := E) (s := Set.range c)
    have h2 : (Set.range c).toFinset.card ≤ n - 1 := by
      rw [Set.toFinset_range c]
      exact le_trans (Finset.card_image_le) (by simp)
    exact le_trans h1 h2
  have htop : Module.finrank ℝ ↥(⊤ : Submodule ℝ E) = n := by
    calc
      Module.finrank ℝ ↥(⊤ : Submodule ℝ E) = Module.finrank ℝ E := by
        exact LinearEquiv.finrank_eq (Submodule.topEquiv : ↥(⊤ : Submodule ℝ E) ≃ₗ[ℝ] E)
      _ = n := by
        rw [Module.finrank_eq_card_basis b.toBasis]
        simp
  have hfinV : Module.finrank ℝ ↥V = n := by
    rw [hVtop]
    exact htop
  have hnle : n ≤ n - 1 := by
    rw [hfinV] at hfinVle
    exact hfinVle
  omega

/-- The norm squared of the basis-position sum is the sum of the individual
norm squares (the outputs are pairwise orthogonal). -/
lemma norm_sq_gsSumB {n : ℕ} (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Fin n → E) (c : Fin (n - 1) → E) :
    ‖gsSumB E b c‖ ^ 2 = ∑ j : Fin n, ‖gs E b c (bpos j)‖ ^ 2 := by
  -- ‖Σ_j v_j‖² = ‖Σ v_j‖²
  unfold gsSumB
  -- expand using inner
  have hinner : inner ℝ (∑ j : Fin n, gs E b c (bpos j)) (∑ j : Fin n, gs E b c (bpos j)) =
      ∑ j : Fin n, ‖gs E b c (bpos j)‖ ^ 2 := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro j hj
    rw [inner_sum]
    -- ⟨v_j, Σ_k v_k⟩ = Σ_k ⟨v_j, v_k⟩ = ⟨v_j,v_j⟩
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      exact gs_pair_inner_zero E b c (by
        intro hpos
        exact hkj (bpos_injective hpos.symm))
    · intro hjnot
      exfalso
      exact hjnot (Finset.mem_univ j)
  -- ‖Σ v_j‖² = ⟨Σ v_j, Σ v_j⟩ (over ℝ)
  have hsq : ‖∑ j : Fin n, gs E b c (bpos j)‖ ^ 2 =
      inner ℝ (∑ j : Fin n, gs E b c (bpos j)) (∑ j : Fin n, gs E b c (bpos j)) := by
    simp
  rw [hsq, hinner]

/-- The sum of the basis-position outputs has norm at least one: at least one
of them is non-zero (unit length), and the rest are pairwise orthogonal. -/
theorem norm_gsSumB_ge_one {n : ℕ} (hn : 1 ≤ n) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Module.Finite ℝ E] (b : OrthonormalBasis (Fin n) ℝ E)
    (c : Fin (n - 1) → E) : 1 ≤ ‖gsSumB E (fun j => b j) c‖ := by
  let β : Fin n → E := fun j => b j
  rcases exists_ne_zero_bpos hn E b c with ⟨j0, hj0⟩
  have hunit : ‖gs E β c (bpos j0)‖ = 1 := by
    exact InnerProductSpace.gramSchmidtNormed_unit_length' (𝕜 := ℝ)
      (n := bpos j0) (by simpa [gs, β] using hj0)
  have hterm : 1 ≤ ‖gs E β c (bpos j0)‖ ^ 2 := by nlinarith
  have hle : ‖gs E β c (bpos j0)‖ ^ 2 ≤ ∑ j : Fin n, ‖gs E β c (bpos j)‖ ^ 2 := by
    have hs := Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin n => ‖gs E β c (bpos j)‖ ^ 2)
      (by intro j hj; positivity) (Finset.mem_univ j0)
    -- hs : ‖gs(bpos j0)‖² ≤ ∑ j ∈ univ, ...
    simpa using hs
  have hsq : 1 ≤ ‖gsSumB E β c‖ ^ 2 := by
    rw [norm_sq_gsSumB E β c]
    exact le_trans hterm hle
  -- from 1 ≤ ‖x‖² and ‖x‖ ≥ 0: ‖x‖ ≥ 1
  have hnonneg : 0 ≤ ‖gsSumB E β c‖ := norm_nonneg _
  have habs := (sq_le_sq (a := (1 : ℝ)) (b := ‖gsSumB E β c‖)).mpr (by simpa using hsq)
  -- habs : |1| ≤ |‖gsSumB‖|
  simpa using habs



/-- The candidate normal is a unit vector. -/
lemma unitNormal_unit {n : ℕ} (hn : 1 ≤ n) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Module.Finite ℝ E] (b : OrthonormalBasis (Fin n) ℝ E)
    (c : Fin (n - 1) → E) : ‖unitNormal E (fun j => b j) c‖ = 1 := by
  have hge : 1 ≤ ‖gsSumB E (fun j => b j) c‖ := norm_gsSumB_ge_one hn E b c
  have hne : gsSumB E (fun j => b j) c ≠ 0 := by
    intro h0
    have : 1 ≤ ‖(0 : E)‖ := by simpa [h0] using hge
    norm_num at this
  dsimp [unitNormal]
  exact norm_smul_inv_norm hne



/-- A basis-position output is orthogonal to every column vector (its
Gram–Schmidt vector is orthogonal to all earlier inputs, which include the
columns). -/
lemma gs_bpos_orthogonal_col {n : ℕ} (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : Fin n → E) (c : Fin (n - 1) → E)
    (j : Fin n) (p : Fin (n - 1)) : inner ℝ (gs E b c (bpos j)) (c p) = 0 := by
  -- p sits at a column position strictly before the basis position of j
  let p' : Fin (2 * n - 1) := ⟨p.val, by omega⟩
  have hp'lt : p' < bpos j := by
    apply Fin.lt_def.mpr
    dsimp [p', bpos]
    omega
  have htri := InnerProductSpace.gramSchmidt_inv_triangular ℝ (extFam E b c) hp'lt
  -- htri : ⟪gramSchmidt extFam (bpos j), extFam p'⟫ = 0
  have hp'col : p'.val < n - 1 := p.isLt
  have hext : extFam E b c p' = c p := by
    dsimp [p']
    rw [extFam_col E b c (by simp)]
  -- gs = scalar • gramSchmidt
  calc
    inner ℝ (gs E b c (bpos j)) (c p)
        = inner ℝ ((‖InnerProductSpace.gramSchmidt ℝ (extFam E b c) (bpos j)‖)⁻¹ •
              InnerProductSpace.gramSchmidt ℝ (extFam E b c) (bpos j)) (extFam E b c p') := by
          rw [hext]
          rfl
    _ = 0 := by
      rw [inner_smul_left]
      rw [htri]
      simp

/-- The candidate normal is orthogonal to every column vector. -/
lemma unitNormal_orthogonal_col {n : ℕ} (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : Fin n → E) (c : Fin (n - 1) → E) (p : Fin (n - 1)) :
    inner ℝ (unitNormal E b c) (c p) = 0 := by
  let β : Fin n → E := b
  dsimp [unitNormal]
  rw [inner_smul_left]
  -- ⟪gsSumB, c p⟫ = 0
  have hsum : inner ℝ (gsSumB E β c) (c p) = 0 := by
    unfold gsSumB
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro j hj
    exact gs_bpos_orthogonal_col E β c j p
  rw [hsum]
  simp



/-! ## Measurability of the Gram–Schmidt outputs

If the input family is measurable pointwise, each Gram–Schmidt output (hence
each normalized output) is a measurable function, by induction on the index
using the explicit recurrence (`gramSchmidt_def` plus
`Submodule.starProjection_singleton`). -/

/-- A finite sum over `{i | i < n}` of measurable functions into `E` is
measurable (relative induction, since measurability is only available on the
strict lower set). -/
lemma measurable_sum_Iio {ι : Type*} {Ω : Type*} [MeasurableSpace Ω]
    (E : Type*) [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [LinearOrder ι] [LocallyFiniteOrderBot ι]
    (n : ι) {u : ι → Ω → E} (hu : ∀ i, i < n → Measurable (u i)) :
    Measurable (fun ω => ∑ i < n, u i ω) := by
  classical
  have hmain : ∀ s : Finset ι, s ⊆ Finset.Iio n →
      Measurable (fun ω => ∑ i ∈ s, u i ω) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      have heq0 : (fun ω : Ω => ∑ i ∈ (∅ : Finset ι), u i ω) = fun _ : Ω => (0 : E) := by
        funext ω
        rw [Finset.sum_empty]
      rw [heq0]
      exact measurable_const
    · intro a t hat ih hsub
      have heq : (fun ω : Ω => ∑ i ∈ insert a t, u i ω) = fun ω => u a ω + ∑ i ∈ t, u i ω := by
        funext ω
        rw [Finset.sum_insert hat]
      rw [heq]
      have hu_a : Measurable (u a) := hu a (Finset.mem_Iio.mp (hsub (Finset.mem_insert_self a t)))
      exact hu_a.add (ih (by
        intro i hit
        exact hsub (Finset.mem_insert_of_mem hit)))
  simpa using (hmain (Finset.Iio n) (by intro i hi; exact hi))

/-- The orthogonal projection onto the span of a measurable single vector is
measurable. -/
lemma measurable_starProjection_span {Ω : Type*} [MeasurableSpace Ω]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f v : Ω → E} (hf : Measurable f) (hv : Measurable v) :
    Measurable (fun ω => (Submodule.span ℝ ({v ω} : Set E)).starProjection (f ω)) := by
  have hrewrite : (fun ω : Ω => (Submodule.span ℝ ({v ω} : Set E)).starProjection (f ω)) =
      fun ω => (inner ℝ (v ω) (f ω) / ‖v ω‖ ^ 2) • v ω := by
    funext ω
    exact (Submodule.starProjection_singleton ℝ (w := f ω) (v := v ω))
  rw [hrewrite]
  fun_prop

/-- Each Gram–Schmidt output is measurable in the inputs (strong induction on
the position over the well-founded order). -/
lemma measurable_gramSchmidt_fin (M : ℕ) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Ω : Type*} [MeasurableSpace Ω]
    {v : Fin M → Ω → E} (hv : ∀ i : Fin M, Measurable (v i)) :
    ∀ n : Fin M, Measurable (fun ω => gramSchmidt ℝ (fun i : Fin M => v i ω) n) := by
  intro n
  let motive : Fin M → Prop := fun a => Measurable (fun ω => gramSchmidt ℝ (fun i : Fin M => v i ω) a)
  change motive n
  refine WellFoundedLT.induction (motive := motive) n ?_
  intro n ih
  change Measurable (fun ω => gramSchmidt ℝ (fun i : Fin M => v i ω) n)
  have heq : (fun ω : Ω => gramSchmidt ℝ (fun i : Fin M => v i ω) n) =
      fun ω => (v n) ω - ∑ i < n,
        (ℝ ∙ gramSchmidt ℝ (fun i : Fin M => v i ω) i).starProjection ((v n) ω) := by
    funext ω
    rw [gramSchmidt_def]
  rw [heq]
  have hsub1 : Measurable (fun ω => (v n) ω) := hv n
  have hsub2 : Measurable (fun ω => ∑ i < n,
      (ℝ ∙ gramSchmidt ℝ (fun i : Fin M => v i ω) i).starProjection ((v n) ω)) := by
    exact measurable_sum_Iio (E := E) (n := n)
      (u := fun i ω => (ℝ ∙ gramSchmidt ℝ (fun j : Fin M => v j ω) i).starProjection ((v n) ω)) (by
        intro i hi
        exact measurable_starProjection_span (E := E) (f := fun ω => v n ω)
          (v := fun ω => gramSchmidt ℝ (fun j : Fin M => v j ω) i) (hv n)
          (ih i hi))
  exact hsub1.sub hsub2

/-- Each normalized Gram–Schmidt output is measurable in the inputs. -/
lemma measurable_gramSchmidtNormed_fin (M : ℕ) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Ω : Type*} [MeasurableSpace Ω]
    {v : Fin M → Ω → E} (hv : ∀ i : Fin M, Measurable (v i)) :
    ∀ n : Fin M, Measurable (fun ω => gramSchmidtNormed ℝ (fun i : Fin M => v i ω) n) := by
  intro n
  have hmeas := measurable_gramSchmidt_fin M E hv n
  -- gramSchmidtNormed f n = (‖gramSchmidt f n‖)⁻¹ • gramSchmidt f n
  dsimp [gramSchmidtNormed]
  fun_prop



/-- A finite sum over any finset of measurable functions into `E` is
measurable (unconditional per-index measurability). -/
lemma measurable_finset_sum_of_all {ι : Type*} {Ω : Type*} [MeasurableSpace Ω]
    (E : Type*) [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (s : Finset ι) {u : ι → Ω → E}
    (hu : ∀ i, Measurable (u i)) : Measurable (fun ω => ∑ i ∈ s, u i ω) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · have heq0 : (fun ω : Ω => ∑ i ∈ (∅ : Finset ι), u i ω) = fun _ : Ω => (0 : E) := by
      funext ω
      rw [Finset.sum_empty]
    rw [heq0]
    exact measurable_const
  · intro a t hat ih
    have heq : (fun ω : Ω => ∑ i ∈ insert a t, u i ω) = fun ω => u a ω + ∑ i ∈ t, u i ω := by
      funext ω
      rw [Finset.sum_insert hat]
    rw [heq]
    exact (hu a).add ih

/-- The Gram–Schmidt outputs of a measurable extended family are measurable
(in the columns and the basis vectors). -/
lemma measurable_gs_extFam {n : ℕ} (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Ω : Type*} [MeasurableSpace Ω]
    {β : Fin n → Ω → E} (hβ : ∀ j : Fin n, Measurable (β j))
    {γ : Fin (n - 1) → Ω → E} (hγ : ∀ i : Fin (n - 1), Measurable (γ i)) :
    ∀ i : Fin (2 * n - 1),
      Measurable (fun ω => gs E (fun j => β j ω) (fun i => γ i ω) i) := by
  intro i
  -- the extended family is measurable pointwise
  have hv : ∀ k : Fin (2 * n - 1),
      Measurable (fun ω => extFam E (fun j => β j ω) (fun i => γ i ω) k) := by
    intro k
    by_cases hcol : k.val < n - 1
    · have heq : (fun ω : Ω => extFam E (fun j => β j ω) (fun i => γ i ω) k) =
        fun ω => γ ⟨k.val, hcol⟩ ω := by
        funext ω
        exact extFam_col E (fun j => β j ω) (fun i => γ i ω) hcol
      rw [heq]
      exact hγ ⟨k.val, hcol⟩
    · have hge : n - 1 ≤ k.val := Nat.le_of_not_gt hcol
      let j : Fin n := ⟨k.val - (n - 1), by omega⟩
      have heq : (fun ω : Ω => extFam E (fun j => β j ω) (fun i => γ i ω) k) =
          fun ω => β j ω := by
        funext ω
        dsimp [extFam, j]
        simp [hcol]
      rw [heq]
      exact hβ j
  -- now use the general gramSchmidtNormed measurability
  have hgs := measurable_gramSchmidtNormed_fin (2 * n - 1) E hv i
  -- hgs : Measurable (fun ω => gramSchmidtNormed ℝ (fun k => extFam E (fun j => β j ω)(fun i => γ i ω) k) i)
  simpa [gs] using hgs

/-- The candidate unit normal built from measurable columns and a fixed basis
is measurable. -/
lemma measurable_unitNormal {n : ℕ} (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Ω : Type*} [MeasurableSpace Ω]
    (b : Fin n → E) {γ : Fin (n - 1) → Ω → E} (hγ : ∀ i : Fin (n - 1), Measurable (γ i)) :
    Measurable (fun ω => unitNormal E b (fun i => γ i ω)) := by
  -- gsSumB is measurable (finite sum of measurable gs)
  have hgs : ∀ j : Fin n,
      Measurable (fun ω => gs E b (fun i => γ i ω) (bpos j)) := by
    intro j
    have := measurable_gs_extFam E (β := fun j _ => b j) (γ := γ) (by intro k; fun_prop) hγ
    -- this : ∀ i, Measurable (fun ω => gs E (fun j => b) (fun i => γ i ω) i)
    simpa using (this (bpos j))
  have hsum : Measurable (fun ω => gsSumB E b (fun i => γ i ω)) := by
    have hsum' := measurable_finset_sum_of_all (E := E) (s := Finset.univ) (u := fun j ω => gs E b (fun i => γ i ω) (bpos j)) hgs
    -- hsum' : Measurable (fun ω => ∑ j ∈ univ, gs ... (bpos j) ω)
    simpa [gsSumB] using hsum'
  dsimp [unitNormal]
  fun_prop


end GramSchmidtExtension

end Submission.UnitNormal
