import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseDict.Defs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.creAux` — helpers for the box ↔ model **creation** dictionary

This module collects the elementary lemmas needed for `Work.BoseDict.boxRealise_cre`
(`boxRealise e (d+1) (cre m l Ψ) = boxCre e l d (boxRealise e d Ψ)`):

* `modeMult_apply`, `modeMult_insertNth` — the occupation multi-index of a labelling
  and its behaviour under inserting one marked occurrence of a mode;
* `sum_add_e` — the degree of `α + e_l`;
* `etaOf_pi_single` — the superposition `η_w` at `w = single l 1` is `e l`;
* `boxCreOf_add`, `boxCreOf_smul`, `boxCreOf_zero` — the linearity of the box creation
  `boxCreOf e w d` in the state (it is defined as a plain function, so linearity is
  proved pointwise).

Everything here is purely combinatorial / pointwise: no integrals are involved.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The occupation multi-index of a labelling -/

/-- The components of the occupation multi-index are the fibre cardinalities. -/
lemma modeMult_apply {m n : ℕ} (σ : Fin n → Fin m) (i : Fin m) :
    modeMult σ i = (Finset.univ.filter fun d => σ d = i).card := by
  rw [modeMult, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    exact Finsupp.single_eq_of_ne (Ne.symm hb)
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **Inserting a marked occurrence of the mode `l`** adds one unit of occupation of `l`:
`modeMult (insertNth j l σ) = modeMult σ + e_l`. -/
lemma modeMult_insertNth {m n : ℕ} (l : Fin m) (j : Fin (n + 1)) (σ : Fin n → Fin m) :
    modeMult (Fin.insertNth j l σ) = modeMult σ + Finsupp.single l 1 := by
  ext i
  rw [Finsupp.add_apply, Finsupp.single_apply, modeMult_apply, modeMult_apply]
  rw [Finset.card_filter, Fin.sum_univ_succAbove _ j, Finset.card_filter]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  exact Nat.add_comm _ _

/-! ## 2. The degree of `α + e_l` -/

/-- The total degree gains `1` when the occupation of `l` is raised by one. -/
lemma sum_add_e {m : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) :
    (α + Work.BoseB4.e m l).sum (fun _ k => k) = α.sum (fun _ k => k) + 1 := by
  rw [Finsupp.sum_add_index']
  · congr 1
    rw [Work.BoseB4.e, Finsupp.sum_single_index]
    rfl
  · intro a
    rfl
  · intro a b₁ b₂
    rfl

/-! ## 3. The superposition at `w = single l 1` -/

/-- `η_{single l 1} = e l`. -/
lemma etaOf_pi_single {m : ℕ} (e : Fin m → Sp → ℂ) (l : Fin m) (z : Sp) :
    etaOf e (Pi.single l (1 : ℝ)) z = e l z := by
  rw [etaOf, Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ l) h

/-! ## 4. Linearity of the box creation in the state -/

/-- `boxCreOf e w d` is additive in the state. -/
lemma boxCreOf_add {m : ℕ} (e : Fin m → Sp → ℂ) (w : Fin m → ℝ) (d : ℕ)
    (Θ Θ' : Xn d → ℂ) :
    boxCreOf e w d (Θ + Θ') = boxCreOf e w d Θ + boxCreOf e w d Θ' := by
  funext x
  simp only [boxCreOf, Pi.add_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum]

/-- `boxCreOf e w d` is homogeneous in the state. -/
lemma boxCreOf_smul {m : ℕ} (e : Fin m → Sp → ℂ) (w : Fin m → ℝ) (d : ℕ)
    (c : ℝ) (Θ : Xn d → ℂ) :
    boxCreOf e w d (c • Θ) = c • boxCreOf e w d Θ := by
  funext x
  simp only [boxCreOf, Pi.smul_apply, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- `boxCreOf` of the zero state is zero. -/
lemma boxCreOf_zero {m : ℕ} (e : Fin m → Sp → ℂ) (w : Fin m → ℝ) (d : ℕ) :
    boxCreOf e w d (0 : Xn d → ℂ) = 0 := by
  funext x
  simp [boxCreOf]

end Work.BoseDict
