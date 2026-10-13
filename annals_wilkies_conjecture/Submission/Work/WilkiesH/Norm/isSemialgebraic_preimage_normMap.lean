import Mathlib
import Submission.Work.WilkiesH.Norm.Defs
import Submission.Work.WilkiesI.Basic

/-!
# `normMap σ` pulls back semialgebraic sets to semialgebraic sets

`normMap σ` acts coordinatewise by one of the four maps `t ↦ t`, `t ↦ -t`, `t ↦ t⁻¹`,
`t ↦ -t⁻¹`.  Each of these is *definable* in the language of rings over `ℝ` (the inverse
only through its graph, `t * y = 1 ∨ (t = 0 ∧ y = 0)`, since the language has no `⁻¹`
symbol).  The graph of `normMap σ` is therefore a definable subset of the `2n`-dimensional
space `(Fin n ⊕ Fin n) → ℝ`, and the preimage of a definable `Y` is obtained from it by
projecting out the second block — a *finite* projection, which preserves definability.

The only real-arithmetic inputs are the two descriptions of Lean's `⁻¹` (with `inv_zero`):
`b = a⁻¹ ↔ (a = 0 ∧ b = 0) ∨ a * b = 1` and its negation-twisted version.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Norm

open WilkiesDesign WilkiesConjecture
open FirstOrder FirstOrder.Language

/-! ## The description of `⁻¹` in the language of rings -/

/-- Lean's inverse on `ℝ` (with `inv_zero`, so `0⁻¹ = 0`) is described by the
polynomial conditions `a * b = 1` and `a = b = 0`. -/
lemma eq_inv_iff_eq_or_mul_eq_one (a b : ℝ) : b = a⁻¹ ↔ (a = 0 ∧ b = 0) ∨ a * b = 1 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · left; exact ⟨ha, by rw [h, ha, inv_zero]⟩
    · right; rw [h, mul_inv_cancel₀ ha]
  · rintro (⟨rfl, rfl⟩ | h)
    · simp
    · exact eq_inv_of_mul_eq_one_right h

/-- The same description for `b = -a⁻¹`. -/
lemma eq_neg_inv_iff_eq_or_mul_eq_neg_one (a b : ℝ) :
    b = -a⁻¹ ↔ (a = 0 ∧ b = 0) ∨ a * b = -1 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · left; exact ⟨ha, by rw [h, ha, inv_zero, neg_zero]⟩
    · right; rw [h]; field_simp
  · rintro (⟨rfl, rfl⟩ | h)
    · simp
    · have h' : a * (-b) = 1 := by linarith
      have h2 := eq_inv_of_mul_eq_one_right h'
      linarith

/-! ## The graph of a shape is definable -/

/-- For any shape `s` and any two coordinates `a b`, the set of `w` with
`w b = shapeMap s (w a)` is definable in the language of rings. -/
lemma definable_shapeGraph {ι : Type*} (s : NormShape) (a b : ι) :
    Set.Definable (Set.univ : Set ℝ) Language.ring {w : ι → ℝ | w b = shapeMap s (w a)} := by
  cases s
  · have h : {w : ι → ℝ | w b = shapeMap NormShape.pos (w a)} =
        {w : ι → ℝ | (MvPolynomial.eval w) (MvPolynomial.X b - MvPolynomial.X a) = 0} := by
      ext w; simp [shapeMap, sub_eq_zero]
    rw [h]; exact Work.WilkiesI.definable_eval_eq _ _
  · have h : {w : ι → ℝ | w b = shapeMap NormShape.neg (w a)} =
        {w : ι → ℝ | (MvPolynomial.eval w) (MvPolynomial.X b + MvPolynomial.X a) = 0} := by
      ext w; simp [shapeMap, eq_neg_iff_add_eq_zero]
    rw [h]; exact Work.WilkiesI.definable_eval_eq _ _
  · have h : {w : ι → ℝ | w b = shapeMap NormShape.big (w a)} =
        ({w : ι → ℝ | (MvPolynomial.eval w) (MvPolynomial.X a) = 0} ∩
          {w : ι → ℝ | (MvPolynomial.eval w) (MvPolynomial.X b) = 0}) ∪
        {w : ι → ℝ | (MvPolynomial.eval w) (MvPolynomial.X a * MvPolynomial.X b) = 1} := by
      ext w
      simp only [shapeMap, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
        MvPolynomial.eval_X, MvPolynomial.eval_mul]
      exact eq_inv_iff_eq_or_mul_eq_one (w a) (w b)
    rw [h]
    exact ((Work.WilkiesI.definable_eval_eq _ _).inter
      (Work.WilkiesI.definable_eval_eq _ _)).union (Work.WilkiesI.definable_eval_eq _ _)
  · have h : {w : ι → ℝ | w b = shapeMap NormShape.bigNeg (w a)} =
        ({w : ι → ℝ | (MvPolynomial.eval w) (MvPolynomial.X a) = 0} ∩
          {w : ι → ℝ | (MvPolynomial.eval w) (MvPolynomial.X b) = 0}) ∪
        {w : ι → ℝ | (MvPolynomial.eval w) (MvPolynomial.X a * MvPolynomial.X b) = -1} := by
      ext w
      simp only [shapeMap, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
        MvPolynomial.eval_X, MvPolynomial.eval_mul]
      exact eq_neg_inv_iff_eq_or_mul_eq_neg_one (w a) (w b)
    rw [h]
    exact ((Work.WilkiesI.definable_eval_eq _ _).inter
      (Work.WilkiesI.definable_eval_eq _ _)).union (Work.WilkiesI.definable_eval_eq _ _)

/-- The graph of `normMap σ`, as a definable subset of `(Fin n ⊕ Fin n) → ℝ`:
the first block is the input, the second block the output. -/
lemma definable_graph_normMap {n : ℕ} (σ : Fin n → NormShape) :
    Set.Definable (Set.univ : Set ℝ) Language.ring
      (⋂ i, {w : (Fin n ⊕ Fin n) → ℝ | w (Sum.inr i) = shapeMap (σ i) (w (Sum.inl i))}) :=
  Set.definable_iInter_of_finite fun i =>
    definable_shapeGraph (σ i) (Sum.inl i) (Sum.inr i)

/-! ## The main result -/

theorem isSemialgebraic_preimage_normMap {n : ℕ} (σ : Fin n → NormShape) {Y : Set (Fin n → ℝ)}
    (hY : WilkiesConjecture.IsSemialgebraic Y) :
    WilkiesConjecture.IsSemialgebraic ((normMap σ) ⁻¹' Y) := by
  -- `S ⊆ (Fin n ⊕ Fin n) → ℝ`: output in `Y`, and output = `normMap σ` of the input.
  set S : Set ((Fin n ⊕ Fin n) → ℝ) :=
    {w | (fun i => w (Sum.inr i)) ∈ Y} ∩
      (⋂ i, {w : (Fin n ⊕ Fin n) → ℝ | w (Sum.inr i) = shapeMap (σ i) (w (Sum.inl i))})
    with hSdef
  have hA : Set.Definable (Set.univ : Set ℝ) Language.ring
      {w : (Fin n ⊕ Fin n) → ℝ | (fun i => w (Sum.inr i)) ∈ Y} := by
    have h := hY.preimage_comp (Sum.inr : Fin n → Fin n ⊕ Fin n)
    convert h using 1
    ext w; rfl
  have hS : Set.Definable (Set.univ : Set ℝ) Language.ring S := by
    rw [hSdef]; exact hA.inter (definable_graph_normMap σ)
  -- Project out the output block (`Fin n` is finite).
  have hproj := Set.Definable.exists_of_finite hS
  have hset : (normMap σ) ⁻¹' Y = {v : Fin n → ℝ | ∃ u : Fin n → ℝ, Sum.elim v u ∈ S} := by
    ext v
    constructor
    · intro hv
      refine ⟨normMap σ v, ?_⟩
      rw [hSdef]
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter,
        Sum.elim_inr, Sum.elim_inl]
      exact ⟨hv, fun i => rfl⟩
    · rintro ⟨u, hu⟩
      rw [hSdef] at hu
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter,
        Sum.elim_inr, Sum.elim_inl] at hu
      obtain ⟨huY, huv⟩ := hu
      have : u = normMap σ v := funext huv
      rw [this] at huY
      exact huY
  rw [hset]
  exact hproj

end Work.WilkiesH.Norm
