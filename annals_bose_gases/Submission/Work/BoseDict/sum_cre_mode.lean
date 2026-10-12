import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Submission.Work.BoseDict.creAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.sum_cre_mode` — the creation row of the box ↔ model dictionary

The **mode-wise creation identity** for the symmetric mode products of
`Work.BoseDict.Defs`:

`∑_j e_l(x_j) · M_α(x ∖ j) = ((α l + 1 : ℕ) : ℂ) · M_{α+e_l}(x)`,   `M_α = modeProd e d α`.

Informally: `M_{α+e_l}` is the symmetrisation of `M_α` times one further mode-`l`
factor, and each labelling realising `α + e_l` is obtained from exactly
`(α + e_l)(l) = α l + 1` choices of the "extra" particle, whence the occupation-number
factor.

The proof is purely combinatorial (no integrals):

* `prod_insertNth` — the labelling product of `insertNth j l σ` splits off the factor
  `e l (x j)` and the product over the remaining `d` slots;
* `sum_insertNth` — for fixed `j`, summing over `σ : Fin d → Fin m` and inserting `l` at
  `j` is the same as summing over all labellings `τ` with `τ j = l`;
* `sum_sum_ite` + `count_eq_modeMult` — swapping the two sums turns the sum over `j`
  into the occupation number `(modeMult τ) l`;
* the occupation number of `α + e_l` at `l` is `α l + 1`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseDict

set_option linter.unusedVariables false

/-! ## 1. The labelling product under an insertion -/

/-- Inserting the marked occurrence `l` at position `j` in the labelling `σ` splits the
labelling product into the factor `e l (x j)` and the product over the remaining slots. -/
lemma prod_insertNth {m d : ℕ} (e : Fin m → Sp → ℂ) (l : Fin m) (j : Fin (d + 1))
    (σ : Fin d → Fin m) (x : Xn (d + 1)) :
    (∏ i : Fin (d + 1), e ((Fin.insertNth (α := fun _ => Fin m) j l σ) i) (x i))
      = e l (x j) * ∏ i : Fin d, e (σ i) (x (Fin.succAbove j i)) := by
  rw [Fin.prod_univ_succAbove _ j]
  congr 1
  · rw [Fin.insertNth_apply_same]
  · exact Finset.prod_congr rfl (fun i _ => by rw [Fin.insertNth_apply_succAbove])

/-! ## 2. Two elementary summation lemmas -/

/-- For fixed `j`, summing over `σ : Fin d → Fin m` and inserting the marked occurrence
`l` at `j` is the same as summing over all labellings `τ` with `τ j = l`. -/
lemma sum_insertNth {m d : ℕ} (l : Fin m) (j : Fin (d + 1))
    (F : (Fin (d + 1) → Fin m) → ℂ) :
    (∑ σ : Fin d → Fin m, F (Fin.insertNth (α := fun _ => Fin m) j l σ))
      = ∑ τ : Fin (d + 1) → Fin m, (if τ j = l then F τ else 0) := by
  classical
  have h : (∑ σ : Fin d → Fin m, F (Fin.insertNth (α := fun _ => Fin m) j l σ))
      = ∑ τ ∈ Finset.univ.filter (fun τ : Fin (d + 1) → Fin m => τ j = l), F τ := by
    refine Finset.sum_bij (fun σ _ => Fin.insertNth (α := fun _ => Fin m) j l σ) ?_ ?_ ?_ ?_
    · intro σ _
      simp only [Finset.mem_univ, Finset.mem_filter, true_and]
      exact Fin.insertNth_apply_same (α := fun _ => Fin m) j l σ
    · intro σ₁ _ σ₂ _ hh
      funext i
      simpa [Fin.insertNth_apply_succAbove] using congr_fun hh (j.succAbove i)
    · intro τ hτ
      exact ⟨fun i => τ (j.succAbove i), Finset.mem_univ _,
        by rw [Fin.insertNth_eq_iff]; exact ⟨(Finset.mem_filter.mp hτ).2.symm, rfl⟩⟩
    · intro σ _; rfl
  rw [h, Finset.sum_filter]

/-- For each `τ`, the number of `j` with `τ j = l` is the occupation number `modeMult τ l`. -/
lemma count_eq_modeMult {m d : ℕ} (l : Fin m) (τ : Fin (d + 1) → Fin m) :
    (∑ j : Fin (d + 1), (if τ j = l then (1 : ℂ) else 0)) = ((modeMult τ l : ℕ) : ℂ) := by
  rw [Finset.sum_boole, modeMult_apply]

/-- Exchanging the sums over `j` and `τ` in `∑_j ∑_τ [τ j = l] F τ` produces the count
`#{j | τ j = l}` of each `τ` as a scalar factor. -/
lemma sum_sum_ite {m d : ℕ} (l : Fin m) (F : (Fin (d + 1) → Fin m) → ℂ) :
    (∑ j : Fin (d + 1), ∑ τ : Fin (d + 1) → Fin m, (if τ j = l then F τ else 0))
      = ∑ τ : Fin (d + 1) → Fin m,
          (((Finset.univ.filter (fun j : Fin (d + 1) => τ j = l)).card : ℕ) : ℂ) * F τ := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  have h1 : (∑ j : Fin (d + 1), (if τ j = l then F τ else 0))
      = ∑ j : Fin (d + 1), (if τ j = l then (1 : ℂ) else 0) * F τ :=
    Finset.sum_congr rfl (fun j _ => by by_cases h : τ j = l <;> simp [h])
  rw [h1, ← Finset.sum_mul, Finset.sum_boole]

/-! ## 3. The creation identity -/

theorem sum_cre_mode {m d : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ} (l : Fin m) (α : Fin m →₀ ℕ)
    (hα : α.sum (fun _ k => k) = d) (x : Work.BoseDict.Xn (d + 1)) :
    (∑ j : Fin (d + 1), e l (x j) * Work.BoseDict.modeProd e d α (fun i : Fin d => x (Fin.succAbove j i)))
      = ((α l + 1 : ℕ) : ℂ) * Work.BoseDict.modeProd e (d + 1) (α + Work.BoseB4.e m l) x := by
  classical
  set w : (Fin (d + 1) → Fin m) → ℂ := fun τ => ∏ i : Fin (d + 1), e (τ i) (x i) with hw
  set G : (Fin (d + 1) → Fin m) → ℂ :=
    fun τ => (if modeMult τ = α + Work.BoseB4.e m l then (1 : ℂ) else 0) * w τ with hG
  have h1 : (∑ j : Fin (d + 1), e l (x j) * modeProd e d α (fun i : Fin d => x (Fin.succAbove j i)))
      = ∑ j : Fin (d + 1), ∑ σ : Fin d → Fin m, (if modeMult σ = α then (1 : ℂ) else 0) *
          (e l (x j) * ∏ i : Fin d, e (σ i) (x (Fin.succAbove j i))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [modeProd, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun σ _ => by ring)
  have h2 : (∑ j : Fin (d + 1), ∑ σ : Fin d → Fin m, (if modeMult σ = α then (1 : ℂ) else 0) *
          (e l (x j) * ∏ i : Fin d, e (σ i) (x (Fin.succAbove j i))))
      = ∑ j : Fin (d + 1), ∑ σ : Fin d → Fin m, (if modeMult σ = α then (1 : ℂ) else 0) *
          w (Fin.insertNth (α := fun _ => Fin m) j l σ) := by
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun σ _ => ?_))
    simp only [hw]
    rw [prod_insertNth e l j σ x]
  have h3 : (∑ j : Fin (d + 1), ∑ σ : Fin d → Fin m, (if modeMult σ = α then (1 : ℂ) else 0) *
          w (Fin.insertNth (α := fun _ => Fin m) j l σ))
      = ∑ j : Fin (d + 1), ∑ σ : Fin d → Fin m, G (Fin.insertNth (α := fun _ => Fin m) j l σ) := by
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun σ _ => ?_))
    have hp : (modeMult σ = α) ↔
        (modeMult (Fin.insertNth (α := fun _ => Fin m) j l σ) = α + Work.BoseB4.e m l) := by
      rw [modeMult_insertNth]
      simp only [Work.BoseB4.e]
      exact add_right_cancel_iff.symm
    simp only [hG]
    by_cases h : modeMult σ = α
    · rw [if_pos h]
      rw [if_pos (hp.mp h)]
    · rw [if_neg h]
      rw [if_neg (fun hh => h (hp.mpr hh))]
  have h4 : (∑ j : Fin (d + 1), ∑ σ : Fin d → Fin m, G (Fin.insertNth (α := fun _ => Fin m) j l σ))
      = ∑ j : Fin (d + 1), ∑ τ : Fin (d + 1) → Fin m, (if τ j = l then G τ else 0) := by
    refine Finset.sum_congr rfl (fun j _ => sum_insertNth l j G)
  have h5 : (∑ j : Fin (d + 1), ∑ τ : Fin (d + 1) → Fin m, (if τ j = l then G τ else 0))
      = ∑ τ : Fin (d + 1) → Fin m, ((modeMult τ l : ℕ) : ℂ) * G τ := by
    rw [sum_sum_ite l G]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [← modeMult_apply τ l]
  have h6 : (∑ τ : Fin (d + 1) → Fin m, ((modeMult τ l : ℕ) : ℂ) * G τ)
      = ∑ τ : Fin (d + 1) → Fin m, ((α l + 1 : ℕ) : ℂ) * G τ := by
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    by_cases h : modeMult τ = α + Work.BoseB4.e m l
    · have hc : modeMult τ l = α l + 1 := by
        rw [h, Finsupp.add_apply]
        simp [Work.BoseB4.e]
      rw [hc]
    · simp only [hG]
      simp [h]
  have h7 : (∑ τ : Fin (d + 1) → Fin m, ((α l + 1 : ℕ) : ℂ) * G τ)
      = ((α l + 1 : ℕ) : ℂ) * ∑ τ : Fin (d + 1) → Fin m, G τ := by
    rw [Finset.mul_sum]
  have h8 : ((α l + 1 : ℕ) : ℂ) * ∑ τ : Fin (d + 1) → Fin m, G τ
      = ((α l + 1 : ℕ) : ℂ) * modeProd e (d + 1) (α + Work.BoseB4.e m l) x := by
    -- `G` unfolds to the defining summand of `modeProd e (d+1) (α + e_l)` multiplied by `w`,
    -- and `w` is the labelling product: the two sides are definitionally equal.
    congr 1
  calc
    (∑ j : Fin (d + 1), e l (x j) * modeProd e d α (fun i : Fin d => x (Fin.succAbove j i)))
        = ∑ j : Fin (d + 1), ∑ σ : Fin d → Fin m, (if modeMult σ = α then (1 : ℂ) else 0) *
            (e l (x j) * ∏ i : Fin d, e (σ i) (x (Fin.succAbove j i))) := h1
    _ = ∑ j : Fin (d + 1), ∑ σ : Fin d → Fin m, (if modeMult σ = α then (1 : ℂ) else 0) *
            w (Fin.insertNth (α := fun _ => Fin m) j l σ) := h2
    _ = ∑ j : Fin (d + 1), ∑ σ : Fin d → Fin m, G (Fin.insertNth (α := fun _ => Fin m) j l σ) := h3
    _ = ∑ j : Fin (d + 1), ∑ τ : Fin (d + 1) → Fin m, (if τ j = l then G τ else 0) := h4
    _ = ∑ τ : Fin (d + 1) → Fin m, ((modeMult τ l : ℕ) : ℂ) * G τ := h5
    _ = ∑ τ : Fin (d + 1) → Fin m, ((α l + 1 : ℕ) : ℂ) * G τ := h6
    _ = ((α l + 1 : ℕ) : ℂ) * ∑ τ : Fin (d + 1) → Fin m, G τ := h7
    _ = ((α l + 1 : ℕ) : ℂ) * modeProd e (d + 1) (α + Work.BoseB4.e m l) x := h8

end Work.BoseDict
