import Mathlib
import Submission.GeometryOfNumbers.ExteriorCoordinates
import Submission.GeometryOfNumbers.DiagonalFlow
import Submission.Commons.LinearAlgebra.Matrix.det_eq_zero_of_zero_blocks
import Submission.Commons.Analysis.InnerProductSpace.iMulti_sum_swap_expansion
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal
import Submission.Commons.Analysis.InnerProductSpace.normSq_sum_swap_one
import Submission.Bridge.ONGraph

/-!
# Wedge blocks along a coordinate plane: VANISH infrastructure

Coordinate model: `d k ℓ` with `k ≤ ℓ ≤ d`; the reference plane
`x₀ = modelX ℓ = Span { (B d) j | j.val < ℓ }` and its orthogonal complement
`Span { (B d) j | j.val ≥ ℓ }`.

**VANISH** (the load-bearing statement; its proof is assembled once the fleet proves
`Commons.LinearAlgebra.Matrix.det_eq_zero_of_zero_blocks`): if `u : Fin k → ℝᵈ`
has each factor in `x₀ ∪ x₀ᗮ` with exactly `m` factors in `x₀ᗮ`, then
`wcoord (ιMulti u) I = 0` whenever `I` has a different number of indices `≥ ℓ` than
`m`.  Plücker coordinates of a wedge are determinants of mixed Gram matrices
(`wcoord_ιMulti_eq_det`); the Gram matrix has the zero-block structure (rows = the
`x₀ᗮ`-factors, columns = the `≥ ℓ` positions of `I`) that the zero-block
determinant lemma kills.

This module records the infrastructure: standard vectors in `x₀`/`x₀ᗮ`,
inner-product zero conditions across the two sides, and the determinant formula.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow

namespace Submission.WedgeBlocks

variable {d : ℕ}

/-- The reference plane `x₀ = Span { (B d) j | j.val < ℓ }`. -/
def modelX (ℓ : ℕ) : Submodule ℝ (RD d) :=
  Submodule.span ℝ {e : RD d | ∃ i : Fin d, i.val < ℓ ∧ e = (B d) i}

/-- Generic: a vector orthogonal to every generator is in the orthogonal of the span.
(Mathlib-only, copied from the graph-model work.) -/
lemma mem_orthogonal_span_of_inner_zero {s : Set (RD d)} {c : RD d}
    (hc : ∀ u ∈ s, inner ℝ c u = 0) : c ∈ (Submodule.span ℝ s)ᗮ := by
  classical
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hmain : ∀ x : RD d, (∀ hx : x ∈ Submodule.span ℝ s, inner ℝ x c = 0) := by
    intro x
    refine Submodule.span_induction (p := fun x hx => inner ℝ x c = 0) ?_ ?_ ?_ ?_
    · intro e he
      exact (inner_eq_zero_symm.mp (hc e he))
    · simp
    · intro a b ha hb hpa hpb
      simp [inner_add_left, hpa, hpb]
    · intro r a ha hpa
      simp [inner_smul_left, hpa]
  exact hmain u hu

/-- The standard vector with a small index lies in `x₀`. -/
lemma std_mem_modelX (ℓ : ℕ) (i : Fin d) (hi : i.val < ℓ) :
    (B d) i ∈ modelX ℓ := by
  unfold modelX
  exact Submodule.subset_span ⟨i, hi, rfl⟩

/-- The standard vector with a large index lies in `x₀ᗮ`. -/
lemma std_mem_modelX_orth (ℓ : ℕ) (i : Fin d) (hi : ℓ ≤ i.val) :
    (B d) i ∈ (modelX ℓ)ᗮ := by
  unfold modelX
  apply mem_orthogonal_span_of_inner_zero
  rintro e ⟨j, hj, rfl⟩
  exact Orthonormal.inner_eq_zero (B d).orthonormal (by omega)

/-- A vector from `x₀ᗮ` is orthogonal to the low standard vectors. -/
lemma inner_orth_std_low (ℓ : ℕ) (c : RD d) (hc : c ∈ (modelX ℓ)ᗮ)
    (i : Fin d) (hi : i.val < ℓ) : inner ℝ ((B d) i) c = 0 := by
  exact (Submodule.mem_orthogonal (modelX ℓ) c).mp hc ((B d) i) (std_mem_modelX ℓ i hi)

/-- A vector from `x₀` is orthogonal to the high standard vectors. -/
lemma inner_low_std_high (ℓ : ℕ) (e : RD d) (he : e ∈ modelX ℓ)
    (i : Fin d) (hi : ℓ ≤ i.val) : inner ℝ ((B d) i) e = 0 := by
  have hstd : (B d) i ∈ (modelX ℓ)ᗮ := std_mem_modelX_orth ℓ i hi
  exact inner_eq_zero_symm.mp ((Submodule.mem_orthogonal (modelX ℓ) ((B d) i)).mp hstd e he)

/-- Plücker coordinate of a wedge = determinant of the mixed Gram matrix of the family
against the standard basis enumerated at `I`. -/
lemma wcoord_iMulti_eq_det {d k : ℕ} (u : Fin k → RD d) (I : IDX d k) :
    wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k u) I =
      (Matrix.of fun (i j : Fin k) =>
        inner ℝ (((B d) (Set.powersetCard.ofFinEmbEquiv.symm I j)) : RD d) (u i)).det := by
  classical
  rw [wcoord_eq_inner (d := d) (k := k)
    (exteriorPower.ιMulti ℝ k u) I]
  rw [Submission.DiagonalFlow.basisWedge_eq_enumWedge (d := d) (k := k) I]
  rw [exteriorPower.inner_ιMulti_ιMulti]



/-- **VANISH**: the Plücker coordinates of a wedge of a family whose factors are in
`x₀ ∪ x₀ᗮ` (the `c`-factors, indexed by the finset `T`, in `x₀ᗮ`; the
`e`-factors in `x₀`) vanish at any subset `I` whose number of indices `≥ ℓ` differs from
`T.card`. -/
lemma wcoord_wedge_zero_of_block_mismatch {d k : ℕ} (ℓ : ℕ) (e c : Fin k → RD d)
    (he_mem : ∀ r, e r ∈ modelX ℓ) (hc_orth : ∀ r, c r ∈ (modelX ℓ)ᗮ)
    (T : Finset (Fin k)) (I : IDX d k)
    (hneq : T.card ≠
      ((Finset.univ : Finset (Fin k)).filter (fun j : Fin k =>
        ℓ ≤ ((Set.powersetCard.ofFinEmbEquiv.symm I j : Fin d).val))).card) :
    wcoord (d := d) (k := k)
      (exteriorPower.ιMulti ℝ k (fun r : Fin k => if r ∈ T then c r else e r)) I = 0 := by
  classical
  let u : Fin k → RD d := fun r => if r ∈ T then c r else e r
  let Tcols : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter (fun j : Fin k =>
    ℓ ≤ ((Set.powersetCard.ofFinEmbEquiv.symm I j : Fin d).val))
  have hdet : wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k u) I = 0 := by
    rw [wcoord_iMulti_eq_det (d := d) (k := k) u I]
    exact Commons.LinearAlgebra.Matrix.det_eq_zero_of_zero_blocks
      (Matrix.of (fun (i j : Fin k) =>
        inner ℝ (((B d) (Set.powersetCard.ofFinEmbEquiv.symm I j)) : RD d) (u i)))
      T.card Tcols.card rfl rfl hneq
      (by
        intro i hi j hjnotT
        have hlow : ((Set.powersetCard.ofFinEmbEquiv.symm I j : Fin d).val) < ℓ := by
          exact Nat.lt_of_not_ge (by intro hge; exact hjnotT (by simp [Tcols, hge]))
        unfold u
        simp [hi]
        simpa using inner_orth_std_low ℓ (c i) (hc_orth i)
          (Set.powersetCard.ofFinEmbEquiv.symm I j) hlow)
      (by
        intro i hinT j hjT
        have hge : ℓ ≤ ((Set.powersetCard.ofFinEmbEquiv.symm I j : Fin d).val) := by
          simpa [Tcols] using hjT
        unfold u
        simp [hinT]
        simpa using inner_low_std_high ℓ (e i) (he_mem i)
          (Set.powersetCard.ofFinEmbEquiv.symm I j) hge)
  simpa [u] using hdet


lemma card_filter_enum_ge {d k ℓ : ℕ} (I : IDX d k) :
    (((Finset.univ : Finset (Fin k)).filter (fun j : Fin k =>
        ℓ ≤ ((Set.powersetCard.ofFinEmbEquiv.symm I j : Fin d).val))).card) =
      (((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card) := by
  classical
  let σ : Fin k → Fin d := Set.powersetCard.ofFinEmbEquiv.symm I
  let A : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter (fun j : Fin k => ℓ ≤ (σ j).val)
  have hmem : ∀ x : Fin d, x ∈ Set.range σ ↔ x ∈ (I : Finset (Fin d)) := by
    intro x
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem (s := I) (i := x))
  have himg : A.image σ = ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)) := by
    ext y
    rw [Finset.mem_image]
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨j, hj, hjy⟩
      rw [← hjy]
      have hj1 : ℓ ≤ (σ j).val := by simpa [A] using hj
      constructor
      · exact (hmem (σ j)).1 ⟨j, rfl⟩
      · exact hj1
    · intro hy
      rcases hy with ⟨hyI, hyℓ⟩
      rcases (hmem y).2 hyI with ⟨j, hjy⟩
      refine ⟨j, ?_, hjy⟩
      rw [Finset.mem_filter]
      constructor
      · simp
      · rw [hjy]
        exact hyℓ
  calc
    (((Finset.univ : Finset (Fin k)).filter (fun j : Fin k =>
        ℓ ≤ ((Set.powersetCard.ofFinEmbEquiv.symm I j : Fin d).val))).card)
        = (A.image σ).card := by
            change A.card = (A.image σ).card
            exact (Finset.card_image_of_injective A (by simpa [σ] using (Set.powersetCard.ofFinEmbEquiv.symm I).injective)).symm
    _ = (((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card) := by
            rw [himg]


/-- **HC1**: for `e ⊆ x₀`, `c ⊆ x₀ᗮ`, the block-0 coordinate part of the
graph wedge `ιMulti (e + c)` is exactly `ιMulti e`. -/
lemma blockElem_zero_of_graph {d k : ℕ} (ℓ : ℕ) (e c : Fin k → RD d)
    (he_mem : ∀ r, e r ∈ modelX ℓ) (hc_orth : ∀ r, c r ∈ (modelX ℓ)ᗮ) :
    blockElem (d := d) (k := k) (ℓ := ℓ)
      (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) 0 =
      exteriorPower.ιMulti ℝ k e := by
  classical
  apply wk_ext (d := d) (k := k)
  intro I
  let A : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter (fun j : Fin k =>
    ℓ ≤ ((Set.powersetCard.ofFinEmbEquiv.symm I j : Fin d).val))
  have hcI0 : ∀ (hI : I ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) 0),
      A.card = 0 := by
    intro hI
    have hc : (((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card) = 0 := by
      simpa [blockFinset] using hI
    have hb := card_filter_enum_ge (d := d) (k := k) (I := I) (ℓ := ℓ)
    have hb' : A.card = ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card := by
      simpa [A] using hb
    rw [hc] at hb'
    exact hb'
  rw [wcoord_blockElem (d := d) (k := k) (ℓ := ℓ)
    (w := exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) (s := I) (j := 0)]
  by_cases hI : I ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) 0
  · rw [if_pos hI]
    have hA0 : A.card = 0 := hcI0 hI
    rw [Commons.Analysis.InnerProductSpace.iMulti_sum_swap_expansion (k := k) (E := RD d) e c]
    have hwsum : wcoord (d := d) (k := k)
        ((Finset.univ : Finset (Finset (Fin k))).sum (fun T : Finset (Fin k) =>
          exteriorPower.ιMulti ℝ k (fun r : Fin k => if r ∈ T then c r else e r))) I =
        (Finset.univ : Finset (Finset (Fin k))).sum (fun T : Finset (Fin k) =>
          wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
            (fun r : Fin k => if r ∈ T then c r else e r)) I) := by
        simp [wcoord]
    rw [hwsum]
    rw [Finset.sum_eq_single (s := (Finset.univ : Finset (Finset (Fin k))))
      (a := (∅ : Finset (Fin k)))]
    · change wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k e) I =
          wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k e) I
      rfl
    · intro T hT hTne
      have hne : T.card ≠ A.card := by
        intro hEq
        apply hTne
        exact Finset.card_eq_zero.mp (by
          have hz : T.card = 0 := by simpa [hA0] using hEq
          exact hz)
      simpa [A] using (wcoord_wedge_zero_of_block_mismatch (d := d) (k := k) (ℓ := ℓ)
        e c he_mem hc_orth T I hne)
    · intro hnot
      exact False.elim (hnot (by simp))
  · rw [if_neg hI]
    have hc : ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card ≠ 0 := by
      intro hz
      apply hI
      simpa [blockFinset] using hz
    have hb := card_filter_enum_ge (d := d) (k := k) (I := I) (ℓ := ℓ)
    have hb' : A.card = ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card := by
      simpa [A] using hb
    have hAne0 : A.card ≠ 0 := by
      intro h0
      exact hc (by simpa [hb'] using h0)
    have hz := wcoord_wedge_zero_of_block_mismatch (d := d) (k := k) (ℓ := ℓ) e c he_mem hc_orth
      (∅ : Finset (Fin k)) I (by
        intro hzero
        exact hAne0 (by simpa [A] using hzero.symm))
    have hfam : (fun r : Fin k => if r ∈ (∅ : Finset (Fin k)) then c r else e r) = e := by
      funext r
      simp
    rw [hfam] at hz
    exact hz.symm


/-- **HC1, norm**: for orthonormal `e ⊆ x₀`, the block-0 part of the graph wedge is a
unit vector. -/
lemma blockElem_zero_of_graph_norm_one {d k : ℕ} (ℓ : ℕ) (e c : Fin k → RD d)
    (he : Orthonormal ℝ e) (he_mem : ∀ r, e r ∈ modelX ℓ)
    (hc_orth : ∀ r, c r ∈ (modelX ℓ)ᗮ) (hk : 0 < k) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ)
      (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) 0‖ = 1 := by
  rw [blockElem_zero_of_graph (d := d) (k := k) (ℓ := ℓ) e c he_mem hc_orth]
  exact Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal e he hk


variable {d k ℓ : ℕ}

lemma sum_singleton_wcoord_eq_swap (e c : Fin k → RD d) (I : IDX d k) :
    ((Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card = 1)).sum
      (fun T => wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
        (fun r : Fin k => if r ∈ T then c r else e r)) I) =
    (Finset.univ : Finset (Fin k)).sum (fun j : Fin k =>
      wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
        (fun r : Fin k => if r = j then c j else e r)) I) := by
  classical
  let g : Finset (Fin k) → ℝ := fun T => wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
    (fun r : Fin k => if r ∈ T then c r else e r)) I
  let f : Fin k → ℝ := fun j => wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
    (fun r : Fin k => if r = j then c j else e r)) I
  have hfam (j : Fin k) : (fun r : Fin k => if r ∈ ({j} : Finset (Fin k)) then c r else e r) =
      (fun r : Fin k => if r = j then c j else e r) := by
    funext r
    by_cases hr : r = j
    · subst r
      simp
    · simp [hr]
  have hbij : (Finset.univ : Finset (Fin k)).sum f =
      ((Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card = 1)).sum g := by
    refine Finset.sum_bij (s := (Finset.univ : Finset (Fin k)))
      (t := (Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card = 1))
      (f := f) (g := g) (fun (j : Fin k) (_ : j ∈ (Finset.univ : Finset (Fin k))) => ({j} : Finset (Fin k))) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_filter]
      constructor <;> simp
    · intro a ha b hb h
      exact Finset.singleton_inj.mp h
    · intro T hT
      rw [Finset.mem_filter] at hT
      rcases hT with ⟨hTU, hT1⟩
      rcases Finset.card_eq_one.mp hT1 with ⟨j, hTj⟩
      refine ⟨j, by simp, ?_⟩
      exact hTj.symm
    · intro j hj
      dsimp [f, g]
      rw [hfam j]
  change ((Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card = 1)).sum g =
      (Finset.univ : Finset (Fin k)).sum f
  exact hbij.symm

lemma blockElem_one_of_graph {d k : ℕ} (ℓ : ℕ) (e c : Fin k → RD d)
    (he_mem : ∀ r, e r ∈ modelX ℓ) (hc_orth : ∀ r, c r ∈ (modelX ℓ)ᗮ) :
    blockElem (d := d) (k := k) (ℓ := ℓ)
      (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) 1 =
      (Finset.univ : Finset (Fin k)).sum (fun j : Fin k =>
        exteriorPower.ιMulti ℝ k (fun r : Fin k => if r = j then c j else e r)) := by
  classical
  apply wk_ext (d := d) (k := k)
  intro I
  let A : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter (fun j : Fin k =>
    ℓ ≤ ((Set.powersetCard.ofFinEmbEquiv.symm I j : Fin d).val))
  have hcI1 : ∀ (hI : I ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) 1), A.card = 1 := by
    intro hI
    have hc : (((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card) = 1 := by
      simpa [blockFinset] using hI
    have hb := card_filter_enum_ge (d := d) (k := k) (I := I) (ℓ := ℓ)
    have hb' : A.card = ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card := by
      simpa [A] using hb
    rw [hc] at hb'
    exact hb'
  rw [wcoord_blockElem (d := d) (k := k) (ℓ := ℓ)
    (w := exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) (s := I) (j := 1)]
  by_cases hI : I ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) 1
  · rw [if_pos hI]
    have hA1 : A.card = 1 := hcI1 hI
    rw [Commons.Analysis.InnerProductSpace.iMulti_sum_swap_expansion (k := k) (E := RD d) e c]
    have hwsum : wcoord (d := d) (k := k)
        ((Finset.univ : Finset (Finset (Fin k))).sum (fun T : Finset (Fin k) =>
          exteriorPower.ιMulti ℝ k (fun r : Fin k => if r ∈ T then c r else e r))) I =
        (Finset.univ : Finset (Finset (Fin k))).sum (fun T : Finset (Fin k) =>
          wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
            (fun r : Fin k => if r ∈ T then c r else e r)) I) := by
        simp [wcoord]
    rw [hwsum]
    have hpart : (Finset.univ : Finset (Finset (Fin k))).sum
        (fun T : Finset (Fin k) => wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
          (fun r : Fin k => if r ∈ T then c r else e r)) I) =
        ((Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card = 1)).sum
          (fun T : Finset (Fin k) => wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
            (fun r : Fin k => if r ∈ T then c r else e r)) I) := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Finset (Fin k))))
        (p := fun T : Finset (Fin k) => T.card = 1)
        (f := fun T : Finset (Fin k) => wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
          (fun r : Fin k => if r ∈ T then c r else e r)) I)]
      have hz : ((Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card ≠ 1)).sum
          (fun T : Finset (Fin k) => wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
            (fun r : Fin k => if r ∈ T then c r else e r)) I) = 0 := by
        apply Finset.sum_eq_zero
        intro T hT
        have hTne : T.card ≠ 1 := (Finset.mem_filter.mp hT).2
        have hne : T.card ≠ A.card := by
          rw [hA1]
          exact hTne
        exact wcoord_wedge_zero_of_block_mismatch (d := d) (k := k) (ℓ := ℓ) e c he_mem hc_orth T I
          (by simpa [A] using hne)
      rw [hz]
      simp
    rw [hpart]
    rw [sum_singleton_wcoord_eq_swap (d := d) (k := k) e c I]
    have hwsum2 : wcoord (d := d) (k := k)
        ((Finset.univ : Finset (Fin k)).sum (fun j : Fin k =>
          exteriorPower.ιMulti ℝ k (fun r : Fin k => if r = j then c j else e r))) I =
        (Finset.univ : Finset (Fin k)).sum (fun j : Fin k =>
          wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
            (fun r : Fin k => if r = j then c j else e r)) I) := by
        simp [wcoord]
    rw [hwsum2]
  · rw [if_neg hI]
    have hc : ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card ≠ 1 := by
      intro hz
      apply hI
      simpa [blockFinset] using hz
    have hb := card_filter_enum_ge (d := d) (k := k) (I := I) (ℓ := ℓ)
    have hb' : A.card = ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card := by
      simpa [A] using hb
    have hAne1 : A.card ≠ 1 := by
      intro h0
      exact hc (by simpa [hb'] using h0)
    have hzsum : (Finset.univ : Finset (Fin k)).sum (fun j : Fin k =>
        wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
          (fun r : Fin k => if r = j then c j else e r)) I) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hne : ({j} : Finset (Fin k)).card ≠ A.card := by
        intro hEq
        exact hAne1 hEq.symm
      have hfamj : (fun r : Fin k => if r ∈ ({j} : Finset (Fin k)) then c r else e r) =
          (fun r : Fin k => if r = j then c j else e r) := by
        funext r
        by_cases hr : r = j
        · subst r
          simp
        · simp [hr]
      have hv := wcoord_wedge_zero_of_block_mismatch (d := d) (k := k) (ℓ := ℓ) e c he_mem hc_orth
        ({j} : Finset (Fin k)) I (by simpa [A] using hne)
      rw [hfamj] at hv
      exact hv
    have hwsum2 : wcoord (d := d) (k := k)
        ((Finset.univ : Finset (Fin k)).sum (fun j : Fin k =>
          exteriorPower.ιMulti ℝ k (fun r : Fin k => if r = j then c j else e r))) I = 0 := by
      have hwsum' : wcoord (d := d) (k := k)
          ((Finset.univ : Finset (Fin k)).sum (fun j : Fin k =>
            exteriorPower.ιMulti ℝ k (fun r : Fin k => if r = j then c j else e r))) I =
          (Finset.univ : Finset (Fin k)).sum (fun j : Fin k =>
            wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
              (fun r : Fin k => if r = j then c j else e r)) I) := by
          simp [wcoord]
      rw [hwsum', hzsum]
    rw [hwsum2]

/-- **HC2, norm**: for orthonormal `e ⊆ x₀`, the squared norm of the block-1 part of the
graph wedge is `Σ_j ‖c j‖²`. -/
lemma blockElem_one_of_graph_normSq {d k : ℕ} (ℓ : ℕ) (e c : Fin k → RD d)
    (he : Orthonormal ℝ e) (he_mem : ∀ r, e r ∈ modelX ℓ)
    (hc_orth : ∀ r, c r ∈ (modelX ℓ)ᗮ) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ)
      (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) 1‖ ^ 2 =
      (Finset.univ : Finset (Fin k)).sum (fun j : Fin k => ‖c j‖ ^ 2) := by
  classical
  have hec : ∀ i j : Fin k, inner ℝ (e i) (c j) = 0 := by
    intro i j
    exact (Submodule.mem_orthogonal (modelX ℓ) (c j)).mp (hc_orth j) (e i) (he_mem i)
  rw [blockElem_one_of_graph (d := d) (k := k) (ℓ := ℓ) e c he_mem hc_orth]
  exact Commons.Analysis.InnerProductSpace.normSq_sum_swap_one e c he hec



/-- **E1(b) for ON-graph planes (coordinate blocks)**: the distance from the graph subspace
`V = span (range (e + c))` to `x₀` is at most `‖blockElem w 1‖` where
`w = ιMulti (e + c)`.  Coordinate form of Lemma 1(b) for ON-graph planes: ONGraph's
`planeResidual_le_block1` plus HC2 (`blockElem w 1 = block1 e c`). -/
lemma planeResidual_graph_le_blockElem_one {d k : ℕ} (ℓ : ℕ) (hk : 0 < k)
    (e c : Fin k → RD d) (he : Orthonormal ℝ e) (he_mem : ∀ r, e r ∈ modelX ℓ)
    (hc_orth : ∀ r, c r ∈ (modelX ℓ)ᗮ) :
    Submission.ProjectionDistance.planeResidual
      (Submission.Bridge.ONGraph.graphSubspace e c) (modelX ℓ) ≤
      ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) 1‖ := by
  classical
  have hres := Submission.Bridge.ONGraph.planeResidual_le_block1 (x := modelX ℓ) (k := k) (hk := hk)
    e c he he_mem hc_orth
  have hident : blockElem (d := d) (k := k) (ℓ := ℓ)
      (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) 1 =
      Submission.Bridge.ONGraph.block1 e c := by
    rw [blockElem_one_of_graph (d := d) (k := k) (ℓ := ℓ) e c he_mem hc_orth]
    rfl
  rw [hident]
  exact hres

/-- **E1(b), ratio form**: since `‖blockElem w 0‖ = 1`, the graph-plane bound reads
`planeResidual V x₀ ≤ ‖blockElem w 1‖ / ‖blockElem w 0‖`. -/
lemma planeResidual_graph_le_blockRatio {d k : ℕ} (ℓ : ℕ) (hk : 0 < k)
    (e c : Fin k → RD d) (he : Orthonormal ℝ e) (he_mem : ∀ r, e r ∈ modelX ℓ)
    (hc_orth : ∀ r, c r ∈ (modelX ℓ)ᗮ) :
    Submission.ProjectionDistance.planeResidual
      (Submission.Bridge.ONGraph.graphSubspace e c) (modelX ℓ) ≤
      ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) 1‖ /
      ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) 0‖ := by
  classical
  have hmain := planeResidual_graph_le_blockElem_one (d := d) (k := k) (ℓ := ℓ) (hk := hk)
    e c he he_mem hc_orth
  have h0 : ‖blockElem (d := d) (k := k) (ℓ := ℓ)
      (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) 0‖ = 1 :=
    blockElem_zero_of_graph_norm_one (d := d) (k := k) (ℓ := ℓ) e c he he_mem hc_orth hk
  have h1 : ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) 1‖ /
      ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) 0‖ =
      ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) 1‖ := by
    rw [h0]
    simp
  rw [h1]
  exact hmain

end Submission.WedgeBlocks
