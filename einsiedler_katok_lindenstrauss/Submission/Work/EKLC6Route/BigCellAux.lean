/-
# Auxiliary lemmas for the big-cell decomposition `G = U⁻(t) · G⁰G⁺(t)`

This module collects the pieces of `Work.EKLC6Route.bigcell` (`Submission/Work/EKLC6Route/bigcell.lean`,
lemma `L1 — BIGCELL` of `Submission/Work/EKLComp/C6GEOM_ROUTE_LEAD.md` §3.1) that do not depend on the
order pattern of `t`:

* `VtSet t` is a subgroup of `SL₃(ℝ)` (part 1 of the target statement).  Closure under
  multiplication is entrywise (the `(i,j)`-entry of a product at a position `t i < t j` combines
  the third-index entries, one of which vanishes); closure under inversion uses the cofactor
  formula `adj (A) i j = A i c * A c j - A i j * A c c` for the third index `c`, together with
  `Matrix.SpecialLinearGroup.coe_inv` (`↑g⁻¹ = (↑g).adjugate`, `det g = 1`).
* `Uminus t ∩ VtSet t = {1}` entrywise (from `uminus_entry_facts`), hence the product
  `Uminus t · VtSet t` is direct: part 2 of the target statement.
* the transport of all the vocabulary along a permutation `e` of the coordinates
  (`Work.EKLC6Core.permSL`, `(permSL e g) i j = g (e i) (e j)`), used to reduce an arbitrary
  `t` to the sorted case `t 0 ≤ t 1 ≤ t 2` (`Work.EKLC6Core.exists_sorted`).
-/
import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.contraction_rate_uminus
import Submission.Work.EKLC6Core.mem_uminus_of_entry_form
import Submission.Work.EKLC6Core.ParabolAux

noncomputable section
namespace Work.EKLC6Route

open Work.EKLContract Work.EKLC6Core Work.EKLComp

/-! ## The cofactor of a `3 × 3` matrix at an off-diagonal position -/

/-- For `i ≠ j` and `c` the third index (`c ∉ {i,j}`), the `(i,j)`-cofactor of a `3 × 3`
matrix is `A i c * A c j - A i j * A c c` (expansion of the determinant of `A` with its
`j`-th row replaced by `e_i`). -/
theorem adjugate_fin3_apply {A : Matrix (Fin 3) (Fin 3) ℝ} {i j c : Fin 3}
    (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j) :
    A.adjugate i j = A i c * A c j - A i j * A c c := by
  rw [Matrix.adjugate_apply, Matrix.det_fin_three]
  fin_cases i <;> fin_cases j <;> fin_cases c <;>
    simp_all [Matrix.updateRow_apply] <;> ring

/-- The third index of a pair of distinct elements of `Fin 3`. -/
theorem exists_ne_ne (i j : Fin 3) (hij : i ≠ j) : ∃ c : Fin 3, c ≠ i ∧ c ≠ j := by
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | exact ⟨0, by decide, by decide⟩
    | exact ⟨1, by decide, by decide⟩
    | exact ⟨2, by decide, by decide⟩

/-- The unit matrix has the same entries at `(e i, e j)` as at `(i,j)`. -/
theorem one_apply_equiv (e : Fin 3 ≃ Fin 3) (i j : Fin 3) :
    (1 : Matrix (Fin 3) (Fin 3) ℝ) (e i) (e j) = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
  simp [Matrix.one_apply, e.injective.eq_iff]

/-! ## `VtSet t` is a subgroup -/

theorem VtSet_mul_mem {t : Fin 3 → ℝ} {g h : SL3} (hg : g ∈ VtSet t) (hh : h ∈ VtSet t) :
    g * h ∈ VtSet t := by
  intro i j hlt
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hki : k = i
  · rw [hki, hh i j hlt, mul_zero]
  by_cases hkj : k = j
  · rw [hkj, hg i j hlt, zero_mul]
  by_cases hik : t i < t k
  · by_cases hkj' : t k < t j
    · rw [hh k j hkj', mul_zero]
    · rw [hg i k hik, zero_mul]
  · rw [hh k j (lt_of_le_of_lt (not_lt.mp hik) hlt), mul_zero]

theorem VtSet_inv_mem {t : Fin 3 → ℝ} {g : SL3} (hg : g ∈ VtSet t) : g⁻¹ ∈ VtSet t := by
  intro i j hlt
  have hij : i ≠ j := fun h => absurd hlt (by rw [h]; exact lt_irrefl _)
  obtain ⟨c, hci, hcj⟩ := exists_ne_ne i j hij
  rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin3_apply hci hcj hij]
  rw [hg i j hlt, zero_mul, sub_zero]
  by_cases hic : t i < t c
  · rw [hg i c hic, zero_mul]
  · rw [hg c j (lt_of_le_of_lt (not_lt.mp hic) hlt), mul_zero]

theorem VtSet_one_mem (t : Fin 3 → ℝ) : (1 : SL3) ∈ VtSet t := by
  intro i j hlt
  have hij : i ≠ j := fun h => absurd hlt (by rw [h]; exact lt_irrefl _)
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hij]

/-! ## The product `Uminus t · VtSet t` is direct -/

/-- An element of `Uminus t` lying in `VtSet t` is the identity (entrywise: `Uminus t` forces
the `(i,j)`-entry to vanish whenever `t j ≤ t i`, `VtSet t` whenever `t i < t j`). -/
theorem eq_one_of_mem_uminus_of_mem_VtSet {t : Fin 3 → ℝ} {w : SL3}
    (hu : w ∈ Uminus t) (hk : w ∈ VtSet t) : w = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [(uminus_entry_facts t hu).1 i, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq]
  · by_cases hle : t j ≤ t i
    · rw [(uminus_entry_facts t hu).2 i j hij hle, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_apply_ne hij]
    · rw [hk i j (not_le.mp hle), Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hij]

/-- Part 2 of `bigcell`: the decomposition `g = u · k` with `u ∈ Uminus t` and `k ∈ VtSet t`
is unique. -/
theorem uminus_VtSet_unique {t : Fin 3 → ℝ} {u u' k k' : SL3}
    (hu : u ∈ Uminus t) (hu' : u' ∈ Uminus t) (hk : k ∈ VtSet t) (hk' : k' ∈ VtSet t)
    (h : u * k = u' * k') : u = u' ∧ k = k' := by
  have hw1 : u'⁻¹ * u ∈ Uminus t := Subgroup.mul_mem _ (Subgroup.inv_mem _ hu') hu
  have hw2 : u'⁻¹ * u ∈ VtSet t := by
    have heq : u'⁻¹ * u = k' * k⁻¹ := by
      have := congrArg (fun x => u'⁻¹ * x * k⁻¹) h
      simpa [mul_assoc] using this
    rw [heq]
    exact VtSet_mul_mem hk' (VtSet_inv_mem hk)
  have hw : u'⁻¹ * u = 1 := eq_one_of_mem_uminus_of_mem_VtSet hw1 hw2
  have huv : u' = u := inv_mul_eq_one.mp hw
  refine ⟨huv.symm, ?_⟩
  rw [huv] at h
  exact mul_left_cancel h

/-! ## Transport along a permutation of the coordinates -/

theorem mem_V_permSL_iff {e : Fin 3 ≃ Fin 3} {δ : ℝ} {g : SL3} :
    permSL e g ∈ V δ ↔ g ∈ V δ := by
  constructor
  · intro h i j
    have h1 := h (e.symm i) (e.symm j)
    simpa [permSL, Matrix.submatrix_apply, e.apply_symm_apply, Matrix.one_apply,
      e.symm.injective.eq_iff] using h1
  · intro h i j
    have h1 := h (e i) (e j)
    simpa [permSL, Matrix.submatrix_apply, Matrix.one_apply, e.injective.eq_iff] using h1

theorem mem_VtSet_permSL_iff {e : Fin 3 ≃ Fin 3} {t : Fin 3 → ℝ} {g : SL3} :
    permSL e g ∈ VtSet (t ∘ ⇑e) ↔ g ∈ VtSet t := by
  constructor
  · intro h i j hlt
    have h1 := h (e.symm i) (e.symm j) (by simpa [Function.comp_def] using hlt)
    simpa [permSL, Matrix.submatrix_apply, e.apply_symm_apply] using h1
  · intro h i j hlt
    have h1 := h (e i) (e j) hlt
    simpa [permSL, Matrix.submatrix_apply] using h1

/-- `permSL e` carries `Uminus t` onto `Uminus (t ∘ e)` (both directions, via the entrywise
characterisation of `Uminus`). -/
theorem mem_uminus_permSL_iff {e : Fin 3 ≃ Fin 3} {t : Fin 3 → ℝ} {u : SL3} :
    permSL e u ∈ Uminus (t ∘ ⇑e) ↔ u ∈ Uminus t := by
  constructor
  · intro h
    refine mem_uminus_of_entry_form (fun i => ?_) (fun i j hij hle => ?_)
    · have h1 := (uminus_entry_facts _ h).1 (e.symm i)
      simpa [permSL, Matrix.submatrix_apply, e.apply_symm_apply] using h1
    · have h1 := (uminus_entry_facts _ h).2 (e.symm i) (e.symm j)
        (fun hh => hij (e.symm.injective hh)) (by simpa [Function.comp_def] using hle)
      simpa [permSL, Matrix.submatrix_apply, e.apply_symm_apply] using h1
  · intro h
    refine mem_uminus_of_entry_form (fun i => ?_) (fun i j hij hle => ?_)
    · have h1 := (uminus_entry_facts _ h).1 (e i)
      simpa [permSL, Matrix.submatrix_apply] using h1
    · have h1 := (uminus_entry_facts _ h).2 (e i) (e j) (fun hh => hij (e.injective hh))
        (by simpa [Function.comp_def] using hle)
      simpa [permSL, Matrix.submatrix_apply] using h1

/-- `permSL e` carries the ball `Uball (Uminus t) r` onto `Uball (Uminus (t ∘ e)) r`. -/
theorem mem_Uball_permSL_iff {e : Fin 3 ≃ Fin 3} {t : Fin 3 → ℝ} {r : ℝ} {u : SL3} :
    permSL e u ∈ Uball (Uminus (t ∘ ⇑e)) r ↔ u ∈ Uball (Uminus t) r := by
  constructor
  · intro h
    refine ⟨mem_uminus_permSL_iff.mp h.1, fun i j => ?_⟩
    have h1 := h.2 (e.symm i) (e.symm j)
    simpa [permSL, Matrix.submatrix_apply, e.apply_symm_apply, Matrix.one_apply,
      e.symm.injective.eq_iff] using h1
  · intro h
    refine ⟨mem_uminus_permSL_iff.mpr h.1, fun i j => ?_⟩
    have h1 := h.2 (e i) (e j)
    simpa [permSL, Matrix.submatrix_apply, Matrix.one_apply, e.injective.eq_iff] using h1

/-! ## The constant order type -/

/-- In the constant order type `t 0 = t 1 = t 2` the parabolic `VtSet t` is everything and the
unipotent factor is trivial, so the big-cell decomposition is immediate. -/
theorem bigcell_const (t : Fin 3 → ℝ) (h01 : t 0 = t 1) (h12 : t 1 = t 2) (s : ℝ) (hs : 0 < s)
    (hs1 : s ≤ 1 / 100) (g : SL3) (hg : g ∈ V s) :
    ∃ u ∈ Uball (Uminus t) (40 * s), ∃ k ∈ VtSet t ∩ V (40 * s), g = u * k := by
  have hconst : ∀ i j : Fin 3, t i = t j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp_all
  refine ⟨1, ⟨Subgroup.one_mem _, ?_⟩, g, ⟨?_, ?_⟩, (one_mul g).symm⟩
  · intro i j
    rw [Matrix.SpecialLinearGroup.coe_one, sub_self, abs_zero]
    linarith
  · intro i j hlt
    rw [hconst i j] at hlt
    exact absurd hlt (lt_irrefl _)
  · intro i j
    have h := hg i j
    linarith

end Work.EKLC6Route
