import Mathlib
import Submission.Work.Drive.qwCollRow

/-!
# The slot that breaks the rank drop

`Work.Drive.collRowSlotBreak`: given four rows `R i = collRow β γ A i` (`β, γ ∉ {0,1}`, `β ≠ γ`)
whose span has dimension `m - 1` (`1 ≤ m ≤ 4`), there is a slot `k`, an injective enumeration `f`
of `m - 1` of the other three slots whose rows are linearly independent, and a vector `p`, such
that `collRow β γ (Pi.single k p) k ∉ span {R (f i)}`.

The mathematical content is the following.  Writing `Space = ℝ³`, each row of `collRow` is of the
form `a ↦ ((c i) • a, (d i) • a)` with

  `(c, d) 0 = (β - 1, γ - 1)`, `(c, d) 1 = (-β, -γ)`, `(c, d) 2 = (1, 0)`, `(c, d) 3 = (0, 1)`,

and the four pairs `(c i, d i)` are pairwise non-proportional exactly because `β, γ ∉ {0,1}` and
`β ≠ γ`.  Consequently the four row maps `rowL i` have pairwise trivially intersecting ranges and
each is injective.  Since four vectors span a space of dimension `≤ 3`, some row `R k` is a linear
combination of the other three: `span {R i : i ≠ k} = V`.  If the range of `rowL k` were contained
in `V`, then `V = range (rowL k)` (both have dimension `3`); but then `R j ∈ range (rowL k)` for
`j ≠ k` forces `A j = 0` (pairwise trivial intersection), so that `V = span {R j : j ≠ k} = ⊥`,
contradiction.  Hence `rowL k` meets a complement of `V`.  The enumeration `f` is extracted from
`Submodule.exists_fun_fin_finrank_span_eq` applied to the three rows `≠ k`, which span `V` and
contain a basis of `V` of size `dim V = m - 1`.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- The scalar pair `(c, d)` of the `i`-th row map `a ↦ (c • a, d • a)`. -/
def rowAB (β γ : ℝ) : Fin 4 → ℝ × ℝ := ![(β - 1, γ - 1), (-β, -γ), (1, 0), (0, 1)]

/-- The `i`-th row map `Space → Space × Space` of `collRow`. -/
def rowL (β γ : ℝ) (i : Fin 4) : Space →ₗ[ℝ] (Space × Space) :=
  LinearMap.prod ((rowAB β γ i).1 • LinearMap.id) ((rowAB β γ i).2 • LinearMap.id)

lemma rowL_apply (β γ : ℝ) (i : Fin 4) (a : Space) :
    rowL β γ i a = ((rowAB β γ i).1 • a, (rowAB β γ i).2 • a) := rfl

/-- The `i`-th row map applied to the `i`-th transverse vector is the `i`-th row of `collRow`. -/
lemma rowL_eq_collRow (β γ : ℝ) (A : Fin 4 → Space) (i : Fin 4) :
    rowL β γ i (A i) = collRow β γ A i := by
  fin_cases i <;> simp [rowL, rowAB, collRow]

/-- The slot-`k` change direction of `collRow`. -/
lemma collRow_single (β γ : ℝ) (k : Fin 4) (p : Space) :
    collRow β γ (Pi.single k p) k = rowL β γ k p := by
  rw [← rowL_eq_collRow β γ (Pi.single k p) k, Pi.single_eq_same]

/-- The two scalar pairs of two distinct rows are not proportional: the determinant
`d_j c_i - c_j d_i` does not vanish. -/
lemma rowAB_det_ne (β γ : ℝ) (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) (hγ0 : γ ≠ 0) (hγ1 : γ ≠ 1)
    (hβγ : β ≠ γ) {i j : Fin 4} (hij : i ≠ j) :
    (rowAB β γ j).2 * (rowAB β γ i).1 - (rowAB β γ j).1 * (rowAB β γ i).2 ≠ 0 := by
  fin_cases i <;> fin_cases j <;> simp [rowAB] <;>
    (first
      | exact (hij rfl).elim
      | (intro h; exact hβ0 (by nlinarith))
      | (intro h; exact hβ1 (by nlinarith))
      | (intro h; exact hγ0 (by nlinarith))
      | (intro h; exact hγ1 (by nlinarith))
      | (intro h; exact hβγ (by nlinarith)))

/-- The scalar pair of a row is nonzero. -/
lemma rowAB_ne_zero (β γ : ℝ) (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) (i : Fin 4) :
    (rowAB β γ i).1 ≠ 0 ∨ (rowAB β γ i).2 ≠ 0 := by
  fin_cases i
  · exact Or.inl (by simpa [rowAB] using sub_ne_zero.mpr hβ1)
  · exact Or.inl (by simpa [rowAB] using neg_ne_zero.mpr hβ0)
  · exact Or.inl (by simp [rowAB])
  · exact Or.inr (by simp [rowAB])

/-- Each row map is injective. -/
lemma rowL_injective (β γ : ℝ) (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) (_hγ0 : γ ≠ 0) (_hγ1 : γ ≠ 1)
    (i : Fin 4) : Function.Injective (rowL β γ i) := by
  intro a b h
  have h1 : (rowAB β γ i).1 • a = (rowAB β γ i).1 • b := by
    simpa [rowL_apply] using congrArg Prod.fst h
  have h2 : (rowAB β γ i).2 • a = (rowAB β γ i).2 • b := by
    simpa [rowL_apply] using congrArg Prod.snd h
  have ha : (rowAB β γ i).1 • (a - b) = 0 := by rw [smul_sub, h1, sub_self]
  have hb : (rowAB β γ i).2 • (a - b) = 0 := by rw [smul_sub, h2, sub_self]
  have hz : a - b = 0 := by
    rcases rowAB_ne_zero β γ hβ0 hβ1 i with hc | hd
    · exact (smul_eq_zero.mp ha).resolve_left hc
    · exact (smul_eq_zero.mp hb).resolve_left hd
  exact sub_eq_zero.mp hz

/-- Two distinct row maps have trivially intersecting ranges: if `rowL i a = rowL j b` with
`i ≠ j` then `a = 0`. -/
lemma rowL_eq_zero_of_eq (β γ : ℝ) (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) (hγ0 : γ ≠ 0) (hγ1 : γ ≠ 1)
    (hβγ : β ≠ γ) {i j : Fin 4} (hij : i ≠ j) {a b : Space}
    (h : rowL β γ i a = rowL β γ j b) : a = 0 := by
  have h1 : (rowAB β γ i).1 • a = (rowAB β γ j).1 • b := by
    simpa [rowL_apply] using congrArg Prod.fst h
  have h2 : (rowAB β γ i).2 • a = (rowAB β γ j).2 • b := by
    simpa [rowL_apply] using congrArg Prod.snd h
  have hdet := rowAB_det_ne β γ hβ0 hβ1 hγ0 hγ1 hβγ hij
  have hkey :
      ((rowAB β γ j).2 * (rowAB β γ i).1 - (rowAB β γ j).1 * (rowAB β γ i).2) • a = 0 := by
    rw [sub_smul, mul_smul, mul_smul, h1, h2, ← mul_smul, ← mul_smul,
      mul_comm (rowAB β γ j).2 (rowAB β γ j).1, sub_self]
  exact (smul_eq_zero.mp hkey).resolve_left hdet

/-- **A basis of the span, of the prescribed size, taken from a given spanning set.**
(`Submodule.exists_fun_fin_finrank_span_eq` reindexed from `Fin (finrank …)` to `Fin r`.) -/
private lemma exists_fun_fin_span_eq {S : Set (Space × Space)} {r : ℕ}
    (hr : Module.finrank ℝ (Submodule.span ℝ S) = r) :
    ∃ f : Fin r → Space × Space, (∀ i, f i ∈ S) ∧
      Submodule.span ℝ (Set.range f) = Submodule.span ℝ S ∧ LinearIndependent ℝ f := by
  obtain ⟨f, hfmem, hfspan, hfind⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ S
  refine ⟨f ∘ Fin.cast hr.symm, fun i => hfmem _, ?_,
    hfind.comp _ (Fin.cast_injective hr.symm)⟩
  have hrange : Set.range (f ∘ Fin.cast hr.symm) = Set.range f := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hr.symm i, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨Fin.cast hr j, by simp⟩
  rw [hrange, hfspan]

open LeanEval.KnotTheory.Quadrisecant in
/-- **The slot that breaks the rank drop.**  Let `β, γ ∉ {0,1}` with `β ≠ γ`, and let
`A : Fin 4 → Space` be arbitrary (`A i` is the transverse chord–tangent vector `u × (velocity at
slot i)`).  Put `R i = collRow β γ A i` and suppose the span of the four rows has dimension `m - 1`
with `1 ≤ m ≤ 4`.  Then there is a slot `k`, an injective enumeration `f : Fin (m-1) → Fin 4` of
`m - 1` of the other three slots, and a vector `p`, such that the rows `R (f i)` are linearly
independent and `R' k ∉ span {R (f i)}`, where `R' k = collRow β γ (Pi.single k p) k` is the
slot-`k` change direction. -/
theorem collRowSlotBreak {β γ : ℝ} (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) (hγ0 : γ ≠ 0) (hγ1 : γ ≠ 1)
    (hβγ : β ≠ γ) (A : Fin 4 → Space) {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (hrk : Module.finrank ℝ (Submodule.span ℝ (Set.range (Work.Drive.collRow β γ A))) = m - 1) :
    ∃ k : Fin 4, ∃ f : Fin (m - 1) → Fin 4, Function.Injective f ∧ (∀ i, f i ≠ k) ∧
      LinearIndependent ℝ (fun i : Fin (m - 1) => Work.Drive.collRow β γ A (f i)) ∧
      ∃ p : Space, Work.Drive.collRow β γ (Pi.single k p) k ∉
        Submodule.span ℝ (Set.range (fun i : Fin (m - 1) => Work.Drive.collRow β γ A (f i))) := by
  classical
  -- ### Step 1: some row lies in the span of the other three
  have hnot : ¬ LinearIndependent ℝ (collRow β γ A) := by
    intro hind
    have h4 : Module.finrank ℝ (Submodule.span ℝ (Set.range (collRow β γ A))) = 4 := by
      rw [finrank_span_eq_card hind, Fintype.card_fin]
    omega
  obtain ⟨g, hgsum, k, hgk⟩ := Fintype.not_linearIndependent_iff.mp hnot
  have hmem : collRow β γ A k ∈
      Submodule.span ℝ (Set.range (fun j : {j : Fin 4 // j ≠ k} => collRow β γ A j.1)) := by
    have hmem' : (∑ i ∈ Finset.univ.erase k, g i • collRow β γ A i) ∈
        Submodule.span ℝ (Set.range (fun j : {j : Fin 4 // j ≠ k} => collRow β γ A j.1)) := by
      refine Submodule.sum_mem _ ?_
      intro i hi
      refine Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span ⟨⟨i, (Finset.mem_erase.mp hi).1⟩, rfl⟩
    have hsplit : g k • collRow β γ A k =
        -(∑ i ∈ Finset.univ.erase k, g i • collRow β γ A i) := by
      have h1 : (∑ i ∈ Finset.univ.erase k, g i • collRow β γ A i) +
          g k • collRow β γ A k = 0 := by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ k)]
        exact hgsum
      exact eq_neg_of_add_eq_zero_right h1
    have hRk : collRow β γ A k =
        (g k)⁻¹ • (-(∑ i ∈ Finset.univ.erase k, g i • collRow β γ A i)) := by
      rw [← hsplit, ← mul_smul, inv_mul_cancel₀ hgk, one_smul]
    rw [hRk]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _ hmem')
  have hspan_k : Submodule.span ℝ (Set.range (fun j : {j : Fin 4 // j ≠ k} => collRow β γ A j.1))
      = Submodule.span ℝ (Set.range (collRow β γ A)) := by
    refine le_antisymm ?_ ?_
    · refine Submodule.span_le.mpr ?_
      rintro x ⟨j, rfl⟩
      exact Submodule.subset_span ⟨j.1, rfl⟩
    · refine Submodule.span_le.mpr ?_
      rintro x ⟨i, rfl⟩
      by_cases hik : i = k
      · rw [hik]; exact hmem
      · exact Submodule.subset_span ⟨⟨i, hik⟩, rfl⟩
  -- ### Step 2: an independent enumeration of `m - 1` of the other three rows
  have hrk' : Module.finrank ℝ
      (Submodule.span ℝ (Set.range (fun j : {j : Fin 4 // j ≠ k} => collRow β γ A j.1)))
      = m - 1 := by rw [hspan_k]; exact hrk
  obtain ⟨g', hg'mem, hg'span, hg'ind⟩ := exists_fun_fin_span_eq hrk'
  let idx : Fin (m - 1) → {j : Fin 4 // j ≠ k} := fun i => Classical.choose (hg'mem i)
  have hidx : ∀ i, collRow β γ A (idx i).1 = g' i :=
    fun i => Classical.choose_spec (hg'mem i)
  let f : Fin (m - 1) → Fin 4 := fun i => (idx i).1
  have hf_ne : ∀ i, f i ≠ k := fun i => (idx i).2
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hidx_eq : idx i = idx j := Subtype.ext hij
    have h2 : g' i = g' j := by rw [← hidx i, ← hidx j, hidx_eq]
    exact hg'ind.injective h2
  have hf_ind : LinearIndependent ℝ (fun i : Fin (m - 1) => collRow β γ A (f i)) := by
    have h1 : (fun i : Fin (m - 1) => collRow β γ A (f i)) = g' := funext hidx
    rw [h1]; exact hg'ind
  have hspan_f : Submodule.span ℝ (Set.range (fun i : Fin (m - 1) => collRow β γ A (f i)))
      = Submodule.span ℝ (Set.range (collRow β γ A)) := by
    rw [show (fun i : Fin (m - 1) => collRow β γ A (f i)) = g' from funext hidx,
      hg'span, hspan_k]
  -- ### Step 3: the slot-`k` change direction leaves the span
  have hmain : ∃ p : Space, rowL β γ k p ∉ Submodule.span ℝ (Set.range (collRow β γ A)) := by
    by_contra hcon
    push Not at hcon
    have hLle : LinearMap.range (rowL β γ k) ≤
        Submodule.span ℝ (Set.range (collRow β γ A)) := by
      rintro x ⟨p, rfl⟩
      exact hcon p
    have h3 : Module.finrank ℝ (LinearMap.range (rowL β γ k)) = 3 := by
      rw [LinearMap.finrank_range_of_inj (rowL_injective β γ hβ0 hβ1 hγ0 hγ1 k)]
      simp
    have hEq : LinearMap.range (rowL β γ k) =
        Submodule.span ℝ (Set.range (collRow β γ A)) :=
      Submodule.eq_of_le_of_finrank_le hLle (by rw [hrk, h3]; omega)
    have hRj : ∀ j : Fin 4, j ≠ k → collRow β γ A j = 0 := by
      intro j hjk
      have hmemj : collRow β γ A j ∈ LinearMap.range (rowL β γ k) := by
        rw [hEq]
        exact Submodule.subset_span ⟨j, rfl⟩
      obtain ⟨b, hb⟩ := hmemj
      have hzero : A j = 0 :=
        rowL_eq_zero_of_eq β γ hβ0 hβ1 hγ0 hγ1 hβγ hjk (by rw [rowL_eq_collRow, hb])
      rw [← rowL_eq_collRow β γ A j, hzero]
      exact map_zero _
    have hbot : Submodule.span ℝ
        (Set.range (fun j : {j : Fin 4 // j ≠ k} => collRow β γ A j.1)) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro x ⟨⟨j, hjk⟩, rfl⟩
      exact hRj j hjk
    have hzero3 : Module.finrank ℝ (Submodule.span ℝ (Set.range (collRow β γ A))) = 0 := by
      rw [← hspan_k, hbot, finrank_bot]
    have hthree : Module.finrank ℝ (Submodule.span ℝ (Set.range (collRow β γ A))) = 3 := by
      rw [← hEq, h3]
    omega
  obtain ⟨p, hp⟩ := hmain
  refine ⟨k, f, hf_inj, hf_ne, hf_ind, p, ?_⟩
  rw [collRow_single β γ k p, hspan_f]
  exact hp

end

end Work.Drive
