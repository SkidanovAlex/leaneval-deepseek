import Mathlib
import Submission.GeometryOfNumbers.WedgeBlockZero
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_concat_le
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
import Submission.Commons.Analysis.InnerProductSpace.inner_exteriorPower_basis_iMulti_eq_zero_of_support
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal

/-!
# Lemma 5 (first assertion): orthonormal directions with a large contracting block

Coordinate model: `ℝᵈ = EuclideanSpace ℝ (Fin d)` with standard orthonormal basis `(B d)`,
reference plane `x₀ = modelX ℓ = span {(B d) j | j.val < ℓ}` (`ℓ ≤ d`), and `P := modelProj ℓ`
the orthogonal projection onto `x₀`, `Q := 1 - P` its complement.

The block decomposition of `⋀^j ℝᵈ` (module `Submission.ExteriorCoordinates`) labels a
`j`-subset `I ⊆ Fin d` by `|I ∩ {i | ℓ ≤ i.val}|`, the number of "high" (i.e. `x₀ᗮ`)
directions.  **Lemma 5, first assertion**: if `a : Fin j → ℝᵈ` is orthonormal and the
`(j - i)`-block of `ιMulti a` is large (`c ≤ ‖blockElem (ιMulti a) (j - i)‖`), then some
`i`-subfamily of `a` has a large *fully contracting* block:
`‖blockElem (ιMulti (a ∘ f)) 0‖ ≥ c / Nat.choose j i`.

The proof follows the paper (de Saxcé, §3, Lemma 5):
1. multilinear expansion `ιMulti a = Σ_{s : Finset (Fin j)} ιMulti (s.piecewise (P∘a) (Q∘a))`
   (`AlternatingMap.map_add_univ`);
2. each term is supported in the block `j - s.card` (Plücker-coordinate vanishing,
   `Commons.Analysis.InnerProductSpace.inner_exteriorPower_basis_iMulti_eq_zero_of_support`);
3. pigeonhole over the `Nat.choose j i` subsets of size `i`;
4. term bound: after grouping the `P`-slots first (`P`-parts in `x₀`, `Q`-parts in `x₀ᗮ`, so
   the Gram matrix is block diagonal) the norm is at most the norm of the wedge of the
   `P`-parts, upgraded by `‖Q (a t)‖ ≤ 1`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks
open Submission.WedgeBlockZero

namespace Submission.Lemma5General

variable {d : ℕ}

/-- The complementary projection `Q = 1 - P` of a projection `P`. -/
def complProj {d : ℕ} (P : RD d →ₗ[ℝ] RD d) : RD d →ₗ[ℝ] RD d := 1 - P

@[simp] lemma complProj_apply {d : ℕ} (P : RD d →ₗ[ℝ] RD d) (x : RD d) :
    complProj P x = x - P x := by
  simp [complProj]

lemma complProj_add_self {d : ℕ} (P : RD d →ₗ[ℝ] RD d) (x : RD d) :
    P x + complProj P x = x := by
  simp [complProj]

lemma complProj_add_self' {d : ℕ} (P : RD d →ₗ[ℝ] RD d) (x : RD d) :
    complProj P x + P x = x := by
  simp [complProj, add_comm]

/-- The "piecewise" family: `P ∘ a` on the slots in `s`, `Q ∘ a` on the complementary slots. -/
def pieceFam {d : ℕ} (P Q : RD d →ₗ[ℝ] RD d) {j : ℕ} (a : Fin j → RD d)
    (s : Finset (Fin j)) : Fin j → RD d :=
  s.piecewise (fun i => P (a i)) (fun i => Q (a i))

@[simp] lemma pieceFam_apply_mem {d : ℕ} (P Q : RD d →ₗ[ℝ] RD d) {j : ℕ} (a : Fin j → RD d)
    (s : Finset (Fin j)) {t : Fin j} (ht : t ∈ s) : pieceFam P Q a s t = P (a t) := by
  simp [pieceFam, Finset.piecewise, ht]

@[simp] lemma pieceFam_apply_notMem {d : ℕ} (P Q : RD d →ₗ[ℝ] RD d) {j : ℕ} (a : Fin j → RD d)
    (s : Finset (Fin j)) {t : Fin j} (ht : t ∉ s) : pieceFam P Q a s t = Q (a t) := by
  simp [pieceFam, Finset.piecewise, ht]

/-- **Step 1** (multilinear expansion of the wedge along `a = P ∘ a + Q ∘ a`). -/
theorem iMulti_eq_sum_pieceFam {d : ℕ} (P Q : RD d →ₗ[ℝ] RD d) {j : ℕ} (a : Fin j → RD d)
    (h : ∀ x, P x + Q x = x) :
    exteriorPower.ιMulti ℝ j a =
      (Finset.univ : Finset (Finset (Fin j))).sum
        (fun s => exteriorPower.ιMulti ℝ j (pieceFam P Q a s)) := by
  have hm : (fun i : Fin j => P (a i)) + (fun i : Fin j => Q (a i)) = a := by
    funext i
    exact h (a i)
  have key := AlternatingMap.map_add_univ (exteriorPower.ιMulti ℝ j)
    (fun i : Fin j => P (a i)) (fun i : Fin j => Q (a i))
  rw [hm] at key
  simpa [pieceFam] using key

/-- The membership in the `Set.powersetCard` coercion agrees with the `Finset` coercion. -/
lemma mem_coe_iff_mem_coe {d j : ℕ} (I : IDX d j) (i : Fin d) :
    i ∈ (I : Set (Fin d)) ↔ i ∈ (I : Finset (Fin d)) := Iff.rfl

/-- The `ncard` of the intersection with the "high index" set is the cardinality of the
corresponding filtered finset. -/
lemma ncard_inter_high {d j : ℕ} (ℓ : ℕ) (I : IDX d j) :
    ((I : Set (Fin d)) ∩ {i : Fin d | ℓ ≤ i.val}).ncard =
      ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card := by
  classical
  have hset : (I : Set (Fin d)) ∩ {i : Fin d | ℓ ≤ i.val} =
      ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val) : Set (Fin d)) := by
    ext i
    constructor
    · rintro ⟨hiI, hiℓ⟩
      exact Finset.mem_filter.mpr ⟨hiI, hiℓ⟩
    · intro hi
      exact ⟨(Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
  rw [hset, Set.ncard_coe_finset]

lemma modelProj_mem_modelX {d : ℕ} (ℓ : ℕ) (x : RD d) :
    modelProj ℓ x ∈ modelX ℓ := by
  simpa [modelProj] using Submission.WedgeGeneralE1.projMap_mem (modelX ℓ) x

lemma complProj_modelProj_mem_orth {d : ℕ} (ℓ : ℕ) (x : RD d) :
    complProj (modelProj ℓ) x ∈ (modelX ℓ)ᗮ := by
  have h : complProj (modelProj ℓ) x = x - (modelX ℓ).starProjection x := by
    simp [complProj, modelProj, Submission.WedgeGeneralE1.projMap_apply]
  rw [h]
  exact Submodule.sub_starProjection_mem_orthogonal x

lemma modelProj_fixes {d : ℕ} (ℓ : ℕ) {x : RD d} (hx : x ∈ modelX ℓ) :
    modelProj ℓ x = x := by
  simpa [modelProj, Submission.WedgeGeneralE1.projMap_apply] using Submodule.starProjection_eq_self_iff.mpr hx

lemma inner_std_modelProj {d : ℕ} (ℓ : ℕ) (i : Fin d) (x : RD d) :
    inner ℝ ((B d) i) (modelProj ℓ x) = inner ℝ (modelProj ℓ ((B d) i)) x := by
  have h := Submodule.inner_starProjection_left_eq_right (K := modelX ℓ) ((B d) i) x
  simpa [modelProj, Submission.WedgeGeneralE1.projMap_apply] using h.symm

/-- **Step 2** (block support of a piecewise term): the Plücker coordinates of
`ιMulti (pieceFam P Q a s)` vanish outside the block `j - s.card`. -/
lemma wcoord_pieceFam_eq_zero {d j : ℕ} (ℓ : ℕ) (a : Fin j → RD d) (s : Finset (Fin j))
    (I : IDX d j)
    (hcard : ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card ≠ j - s.card) :
    wcoord (d := d) (k := j)
      (exteriorPower.ιMulti ℝ j
        (pieceFam (modelProj ℓ) (complProj (modelProj ℓ)) a s)) I = 0 := by
  classical
  rw [wcoord_eq_inner]
  refine Commons.Analysis.InnerProductSpace.inner_exteriorPower_basis_iMulti_eq_zero_of_support
    (d := d) (j := j) ℓ
    (pieceFam (modelProj ℓ) (complProj (modelProj ℓ)) a s) s I ?_ ?_ ?_
  · intro t ht i hi
    rw [pieceFam_apply_mem _ _ _ _ ht]
    exact (Submodule.mem_orthogonal' (modelX ℓ) ((B d) i)).mp
      (std_mem_modelX_orth ℓ i hi) _ (modelProj_mem_modelX ℓ (a t))
  · intro t ht i hi
    rw [pieceFam_apply_notMem _ _ _ _ ht]
    simp only [complProj_apply]
    rw [inner_sub_right, inner_std_modelProj, modelProj_fixes ℓ (std_mem_modelX ℓ i hi)]
    ring
  · rw [ncard_inter_high]
    exact hcard

/-- Coordinate characterisation of `blockElem`: if all coordinates outside the block vanish,
the block component is the whole vector. -/
lemma blockElem_eq_self_of_wcoord_zero_outside {d k ℓ t : ℕ} (w : WK d k)
    (h : ∀ s : IDX d k, s ∉ blockFinset (d := d) (k := k) (ℓ := ℓ) t →
      wcoord (d := d) (k := k) w s = 0) :
    blockElem (d := d) (k := k) (ℓ := ℓ) w t = w := by
  classical
  apply wk_ext
  intro s
  rw [wcoord_blockElem]
  by_cases hs : s ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) t
  · rw [if_pos hs]
  · rw [if_neg hs, h s hs]

lemma mem_blockFinset_iff {d k ℓ t : ℕ} (I : IDX d k) :
    I ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) t ↔
      ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card = t := by
  simp [blockFinset]

/-- **Step 3a**: a piecewise term whose "high-slot" count already equals the target block
index is a full block element. -/
lemma blockElem_pieceFam_eq_self {d j : ℕ} (ℓ i : ℕ) (a : Fin j → RD d) (s : Finset (Fin j))
    (hs : s.card = i) :
    blockElem (d := d) (k := j) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ j
          (pieceFam (modelProj ℓ) (complProj (modelProj ℓ)) a s)) (j - i) =
      exteriorPower.ιMulti ℝ j
        (pieceFam (modelProj ℓ) (complProj (modelProj ℓ)) a s) := by
  refine blockElem_eq_self_of_wcoord_zero_outside _ ?_
  intro I hI
  refine wcoord_pieceFam_eq_zero ℓ a s I ?_
  intro hcontra
  exact hI (mem_blockFinset_iff (d := d) (k := j) (ℓ := ℓ) (t := j - i) I |>.mpr
    (by rw [← hs]; exact hcontra))

/-- **Step 3b**: a piecewise term with the wrong "high-slot" count has vanishing target
block. -/
lemma blockElem_pieceFam_eq_zero {d j : ℕ} (ℓ i : ℕ) (a : Fin j → RD d) (s : Finset (Fin j))
    (hi : i ≤ j) (hs : s.card ≠ i) :
    blockElem (d := d) (k := j) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ j
          (pieceFam (modelProj ℓ) (complProj (modelProj ℓ)) a s)) (j - i) = 0 := by
  classical
  apply wk_ext
  intro I
  rw [wcoord_blockElem, wcoord_zero]
  by_cases hI : I ∈ blockFinset (d := d) (k := j) (ℓ := ℓ) (j - i)
  · rw [if_pos hI]
    refine wcoord_pieceFam_eq_zero ℓ a s I ?_
    intro hcontra
    have hIj : ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card = j - i :=
      mem_blockFinset_iff (d := d) (k := j) (ℓ := ℓ) (t := j - i) I |>.mp hI
    have hsc : s.card ≤ j := by simpa using s.card_le_univ
    omega
  · rw [if_neg hI]

/-- **Step 3** (the `(j-i)`-block of the wedge is the sum of the terms with `i` low slots). -/
lemma blockElem_iMulti_eq_sum_card {d j : ℕ} (ℓ i : ℕ) (hij : i ≤ j) (a : Fin j → RD d) :
    blockElem (d := d) (k := j) (ℓ := ℓ) (exteriorPower.ιMulti ℝ j a) (j - i) =
      (Finset.univ.filter (fun s : Finset (Fin j) => s.card = i)).sum
        (fun s => exteriorPower.ιMulti ℝ j
          (pieceFam (modelProj ℓ) (complProj (modelProj ℓ)) a s)) := by
  classical
  have hexp := iMulti_eq_sum_pieceFam (modelProj ℓ) (complProj (modelProj ℓ)) a
    (fun x => complProj_add_self (modelProj ℓ) x)
  have hterm : ∀ s : Finset (Fin j),
      blockElem (d := d) (k := j) (ℓ := ℓ)
          (exteriorPower.ιMulti ℝ j
            (pieceFam (modelProj ℓ) (complProj (modelProj ℓ)) a s)) (j - i) =
        if s.card = i then exteriorPower.ιMulti ℝ j
          (pieceFam (modelProj ℓ) (complProj (modelProj ℓ)) a s) else 0 := by
    intro s
    by_cases hsc : s.card = i
    · rw [if_pos hsc]
      exact blockElem_pieceFam_eq_self ℓ i a s hsc
    · rw [if_neg hsc]
      exact blockElem_pieceFam_eq_zero ℓ i a s hij hsc
  rw [hexp]
  have hsum : (∑ s : Finset (Fin j), exteriorPower.ιMulti ℝ j
        (pieceFam (modelProj ℓ) (complProj (modelProj ℓ)) a s)) =
      ∑ s : Finset (Fin j), (1 : ℝ) • exteriorPower.ιMulti ℝ j
        (pieceFam (modelProj ℓ) (complProj (modelProj ℓ)) a s) := by simp
  rw [hsum, blockElem_sum]
  simp only [one_smul]
  rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => hterm s), ← Finset.sum_filter]

/-- The squared norm of an exterior product is the determinant of the Gram matrix. -/
lemma normSq_ιMulti_eq_gram_det {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (v : Fin k → E) :
    ‖exteriorPower.ιMulti ℝ k v‖ ^ 2 = (Matrix.gram ℝ v).det := by
  rw [← exteriorPower.inner_ιMulti_self v]
  exact (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (exteriorPower.ιMulti ℝ k v)).symm

/-- The complementary projection has operator norm at most `1`. -/
lemma norm_complProj_le {d : ℕ} (ℓ : ℕ) (x : RD d) :
    ‖complProj (modelProj ℓ) x‖ ≤ ‖x‖ := by
  have hq : complProj (modelProj ℓ) x = (modelX ℓ)ᗮ.starProjection x := by
    have h := congrArg (fun f : RD d →L[ℝ] RD d => f x)
      (Submodule.starProjection_orthogonal (𝕜 := ℝ) (modelX ℓ))
    simpa [complProj_apply, modelProj, Submission.WedgeGeneralE1.projMap_apply] using h.symm
  have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection x (modelX ℓ)
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [hq, hpy]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- **Step 6a**: a bijection `Fin i ⊕ Fin (j-i) ≃ Fin j` for which the first block lies in `s`
and the second outside of it. -/
lemma exists_block_equiv {j i : ℕ} (hi : i ≤ j) (s : Finset (Fin j)) (hcard : s.card = i) :
    ∃ e : Fin i ⊕ Fin (j - i) ≃ Fin j,
      (∀ r, e (Sum.inl r) ∈ s) ∧ (∀ t, e (Sum.inr t) ∉ s) := by
  classical
  have hcompl : (sᶜ).card = j - i := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  let F : Fin i → Fin j := fun r => ((s.equivFin.symm (Fin.cast hcard.symm r) : ↥s) : Fin j)
  let G : Fin (j - i) → Fin j :=
    fun t => (((sᶜ).equivFin.symm (Fin.cast hcompl.symm t) : ↥(sᶜ)) : Fin j)
  have hFmem : ∀ r, F r ∈ s := fun r => (s.equivFin.symm (Fin.cast hcard.symm r)).2
  have hGmem : ∀ t, G t ∉ s := by
    intro t
    have h : G t ∈ sᶜ := by
      simp only [G]
      exact ((sᶜ).equivFin.symm (Fin.cast hcompl.symm t)).2
    simpa using h
  have hFinj : Function.Injective F := by
    intro r r' hr
    have h1 : s.equivFin.symm (Fin.cast hcard.symm r)
        = s.equivFin.symm (Fin.cast hcard.symm r') := Subtype.ext hr
    exact Fin.cast_injective hcard.symm (s.equivFin.symm.injective h1)
  have hGinj : Function.Injective G := by
    intro t t' ht
    have h1 : (sᶜ).equivFin.symm (Fin.cast hcompl.symm t)
        = (sᶜ).equivFin.symm (Fin.cast hcompl.symm t') := Subtype.ext ht
    exact Fin.cast_injective hcompl.symm ((sᶜ).equivFin.symm.injective h1)
  have hinj : Function.Injective (Sum.elim F G) := by
    rintro (a | b) (c | d) hp
    · simp only [Sum.elim_inl] at hp ⊢
      rw [hFinj hp]
    · exfalso
      simp only [Sum.elim_inl, Sum.elim_inr] at hp
      exact hGmem d (by simpa [hp] using hFmem a)
    · exfalso
      simp only [Sum.elim_inl, Sum.elim_inr] at hp
      exact hGmem b (by simpa [hp] using hFmem c)
    · simp only [Sum.elim_inr] at hp ⊢
      rw [hGinj hp]
  have hbij : Function.Bijective (Sum.elim F G) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    simp only [Fintype.card_sum, Fintype.card_fin]
    exact Nat.add_sub_cancel' hi
  refine ⟨Equiv.ofBijective _ hbij, ?_, ?_⟩
  · intro r
    simp only [Equiv.ofBijective_apply, Sum.elim_inl]
    exact hFmem r
  · intro t
    simp only [Equiv.ofBijective_apply, Sum.elim_inr]
    exact hGmem t

/-- **Step 6b** (term bound): the norm of a piecewise term is at most the norm of the wedge
of its projection parts, when the projection parts are grouped first. -/
lemma norm_pieceFam_le {d j i : ℕ} (ℓ : ℕ) (a : Fin j → RD d) (ha : Orthonormal ℝ a)
    (s : Finset (Fin j))
    (e : Fin i ⊕ Fin (j - i) ≃ Fin j) (heL : ∀ r, e (Sum.inl r) ∈ s)
    (heR : ∀ t, e (Sum.inr t) ∉ s) :
    ‖exteriorPower.ιMulti ℝ j (pieceFam (modelProj ℓ) (complProj (modelProj ℓ)) a s)‖ ≤
      ‖exteriorPower.ιMulti ℝ i (fun r : Fin i => modelProj ℓ (a (e (Sum.inl r))))‖ := by
  classical
  set w : Fin j → RD d := pieceFam (modelProj ℓ) (complProj (modelProj ℓ)) a s with hw
  set pa : Fin i → RD d := fun r => modelProj ℓ (a (e (Sum.inl r))) with hpa
  set qa : Fin (j - i) → RD d := fun t => complProj (modelProj ℓ) (a (e (Sum.inr t))) with hqa
  have hweL : ∀ r, w (e (Sum.inl r)) = pa r := by
    intro r
    simp only [hw, hpa]
    exact pieceFam_apply_mem _ _ _ _ (heL r)
  have hweR : ∀ t, w (e (Sum.inr t)) = qa t := by
    intro t
    simp only [hw, hqa]
    exact pieceFam_apply_notMem _ _ _ _ (heR t)
  have hqmem : ∀ t, qa t ∈ (modelX ℓ)ᗮ := by
    intro t
    simp only [hqa]
    exact complProj_modelProj_mem_orth ℓ (a (e (Sum.inr t)))
  have hpmem : ∀ r, pa r ∈ modelX ℓ := by
    intro r
    simp only [hpa]
    exact modelProj_mem_modelX ℓ (a (e (Sum.inl r)))
  have hblock : (Matrix.gram ℝ w).submatrix (⇑e) (⇑e) =
      Matrix.fromBlocks (Matrix.gram ℝ pa) 0 0 (Matrix.gram ℝ qa) := by
    ext x y
    rcases x with a | b <;> rcases y with c | d
    · simp [Matrix.submatrix_apply, Matrix.gram_apply, hweL]
    · simp only [Matrix.submatrix_apply, Matrix.gram_apply, hweL, hweR,
        Matrix.fromBlocks_apply₁₂ (Matrix.gram ℝ pa) 0 0 (Matrix.gram ℝ qa),
        Matrix.zero_apply]
      exact (Submodule.mem_orthogonal (modelX ℓ) (qa d)).mp (hqmem d) (pa a) (hpmem a)
    · simp only [Matrix.submatrix_apply, Matrix.gram_apply, hweL, hweR,
        Matrix.fromBlocks_apply₂₁ (Matrix.gram ℝ pa) 0 0 (Matrix.gram ℝ qa),
        Matrix.zero_apply]
      exact (Submodule.mem_orthogonal' (modelX ℓ) (qa b)).mp (hqmem b) (pa c) (hpmem c)
    · simp [Matrix.submatrix_apply, Matrix.gram_apply, hweR]
  have hdet : (Matrix.gram ℝ w).det = (Matrix.gram ℝ pa).det * (Matrix.gram ℝ qa).det := by
    rw [← Matrix.det_submatrix_equiv_self e (Matrix.gram ℝ w), hblock,
      Matrix.det_fromBlocks_zero₁₂]
  have hsqL : ‖exteriorPower.ιMulti ℝ j w‖ ^ 2 = (Matrix.gram ℝ w).det :=
    normSq_ιMulti_eq_gram_det w
  have hsqA : ‖exteriorPower.ιMulti ℝ i pa‖ ^ 2 = (Matrix.gram ℝ pa).det :=
    normSq_ιMulti_eq_gram_det pa
  have hsqB : ‖exteriorPower.ιMulti ℝ (j - i) qa‖ ^ 2 = (Matrix.gram ℝ qa).det :=
    normSq_ιMulti_eq_gram_det qa
  have hqnorm : ∀ t, ‖qa t‖ ≤ 1 := by
    intro t
    simp only [hqa]
    calc ‖complProj (modelProj ℓ) (a (e (Sum.inr t)))‖ ≤ ‖a (e (Sum.inr t))‖ :=
          norm_complProj_le ℓ _
      _ = 1 := ha.norm_eq_one (e (Sum.inr t))
  have hdetB : (Matrix.gram ℝ qa).det ≤ 1 := by
    rw [← hsqB]
    have h1 : ‖exteriorPower.ιMulti ℝ (j - i) qa‖ ≤
        ∏ t : Fin (j - i), ‖qa t‖ :=
      Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod qa
    have h2 : ∏ t : Fin (j - i), ‖qa t‖ ≤ 1 :=
      Finset.prod_le_one (fun t _ => norm_nonneg _) (fun t _ => hqnorm t)
    nlinarith [norm_nonneg (exteriorPower.ιMulti ℝ (j - i) qa), h1, h2]
  have hdetA : 0 ≤ (Matrix.gram ℝ pa).det := (Matrix.posSemidef_gram ℝ pa).det_nonneg
  have hfin : ‖exteriorPower.ιMulti ℝ j w‖ ^ 2 ≤ ‖exteriorPower.ιMulti ℝ i pa‖ ^ 2 := by
    rw [hsqL, hsqA, hdet]
    nlinarith
  have hres := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hfin
  simpa [hw, hpa] using hres

/-- The number of `i`-subsets of `Fin j` is `Nat.choose j i`. -/
lemma card_filter_card_eq_choose (j i : ℕ) :
    (Finset.univ.filter (fun s : Finset (Fin j) => s.card = i)).card = Nat.choose j i := by
  have h : (Finset.univ.filter (fun s : Finset (Fin j) => s.card = i)) =
      (Finset.univ : Finset (Fin j)).powersetCard i := by
    ext s
    simp [Finset.mem_powersetCard]
  rw [h, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **Pigeonhole** over a finset of terms. -/
lemma exists_div_le_norm_of_le_norm_sum {ι : Type*} {E : Type*} [SeminormedAddCommGroup E]
    (S : Finset ι) (x : ι → E) {c : ℝ} (hc : 0 < c) (hs : c ≤ ‖∑ i ∈ S, x i‖) :
    ∃ i ∈ S, c / (S.card : ℝ) ≤ ‖x i‖ := by
  classical
  by_contra h
  push_neg at h
  have hne : (∑ i ∈ S, x i) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hs
    linarith
  have hnonempty : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    exact hne (by simp [hemp])
  have hcardpos : 0 < S.card := Finset.card_pos.mpr hnonempty
  have hcast : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hcardpos
  have hlt : ∑ i ∈ S, ‖x i‖ < ∑ _i ∈ S, c / (S.card : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hnonempty (fun i hi => h i hi)
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  have hcancel : (S.card : ℝ) * (c / (S.card : ℝ)) = c := by
    field_simp
  rw [hcancel] at hlt
  have htri : ‖∑ i ∈ S, x i‖ ≤ ∑ i ∈ S, ‖x i‖ := norm_sum_le _ _
  linarith

/-- **Lemma 5, first assertion** (de Saxcé, §3): if the `(j-i)`-block of the wedge of an
orthonormal `j`-family is large, then some `i`-subfamily has a large contracting block. -/
theorem lemma5_first_assertion {d j i : ℕ} (ℓ : ℕ) (hij : i ≤ j) (a : Fin j → RD d)
    (ha : Orthonormal ℝ a) {c : ℝ}
    (hbig : c ≤ ‖blockElem (d := d) (k := j) (ℓ := ℓ)
      (exteriorPower.ιMulti ℝ j a) (j - i)‖) :
    ∃ f : Fin i → Fin j, Function.Injective f ∧
      c / (Nat.choose j i : ℝ) ≤
        ‖blockElem (d := d) (k := i) (ℓ := ℓ)
          (exteriorPower.ιMulti ℝ i (fun r => a (f r))) 0‖ := by
  classical
  set S : Finset (Finset (Fin j)) :=
    Finset.univ.filter (fun s : Finset (Fin j) => s.card = i) with hS
  set T : Finset (Fin j) → WK d j := fun s => exteriorPower.ιMulti ℝ j
    (pieceFam (modelProj ℓ) (complProj (modelProj ℓ)) a s) with hT
  have hcardS : S.card = Nat.choose j i := card_filter_card_eq_choose j i
  by_cases hc : c ≤ 0
  · refine ⟨Fin.castLE hij, Fin.castLE_injective hij, ?_⟩
    have hCpos : (0 : ℝ) < (Nat.choose j i : ℝ) := by
      exact_mod_cast Nat.choose_pos hij
    have h1 : c / (Nat.choose j i : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hc (le_of_lt hCpos)
    exact le_trans h1 (norm_nonneg _)
  · push_neg at hc
    have hsum := blockElem_iMulti_eq_sum_card (d := d) ℓ i hij a
    have hsum' : blockElem (d := d) (k := j) (ℓ := ℓ) (exteriorPower.ιMulti ℝ j a) (j - i)
        = ∑ s ∈ S, T s := by
      rw [hsum]
    rw [hsum'] at hbig
    obtain ⟨s, hs_mem, hs_ge⟩ := exists_div_le_norm_of_le_norm_sum S T hc hbig
    have hscard : s.card = i := (Finset.mem_filter.mp hs_mem).2
    obtain ⟨e, heL, heR⟩ := exists_block_equiv hij s hscard
    have hbound := norm_pieceFam_le (i := i) ℓ a ha s e heL heR
    refine ⟨fun r => e (Sum.inl r), fun x y hxy => Sum.inl_injective (e.injective hxy), ?_⟩
    rw [hcardS] at hs_ge
    have hblk : ‖blockElem (d := d) (k := i) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ i (fun r => a (e (Sum.inl r)))) 0‖ =
        ‖exteriorPower.ιMulti ℝ i (fun r => modelProj ℓ (a (e (Sum.inl r))))‖ := by
      rw [blockElem_zero_ιMulti]
    rw [hblk]
    exact le_trans hs_ge hbound

/-- **Lemma 5, first assertion**, orthonormal-family form. -/
theorem lemma5_first_assertion_orthonormal {d j i : ℕ} (ℓ : ℕ) (hij : i ≤ j)
    (a : Fin j → RD d) (ha : Orthonormal ℝ a) {c : ℝ}
    (hbig : c ≤ ‖blockElem (d := d) (k := j) (ℓ := ℓ)
      (exteriorPower.ιMulti ℝ j a) (j - i)‖) :
    ∃ w : Fin i → RD d, Orthonormal ℝ w ∧
      c / (Nat.choose j i : ℝ) ≤
        ‖blockElem (d := d) (k := i) (ℓ := ℓ) (exteriorPower.ιMulti ℝ i w) 0‖ := by
  obtain ⟨f, hf, hle⟩ := lemma5_first_assertion ℓ hij a ha hbig
  exact ⟨fun r => a (f r), ha.comp f hf, hle⟩

end Submission.Lemma5General
