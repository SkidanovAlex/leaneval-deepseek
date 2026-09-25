import Mathlib
import Submission.Work.NN.Assemble.flatTwoLossless
import Submission.Work.NN.Core.contDiff_one_bmPotential_of_holder
import Submission.Work.NN.Core.exists_holderNorm_wirtinger_le
import Submission.Work.NN.Core.bmPotential_dCoord_eq
import Submission.Work.CR.Flat.Holder.contDiffOn_succ_of_wirtinger
import Submission.Work.CR.Flat.Cauchy.bmCz.bmPot_dCoord

/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The Bochner–Martinelli potential of compactly supported `C^{N,α}` data is `C^{N+1}`

Let `0 < α < 1` and let `g = (g_j)` be a family of compactly supported functions on `ℂⁿ` whose
components are of class `C^N` and have finite `C^{N,α}`-norm on `ℂⁿ`.  Then the Bochner–Martinelli
potential

  `bmPot g z = Σ_j ∫ x, bmKernel j x · g_j (z + x)`

is of class `C^{N+1}` on all of `ℂⁿ`.  This is the top-order regularity statement of the
`C^{N,α}` Schauder theory for the flat `∂̄`-operator: the data gain exactly one derivative.

The proof is by induction on `N`.

* `N = 0`: the global `C¹` statement for compactly supported `C^{0,α}` data,
  `Work.NN.Core.contDiff_one_bmPotential_of_holder` (via the `C^{1,α}` Schauder estimate
  `bmPot_holder_C0a` and the mollification argument of `bmPotentialHolderContinuous`).

* `N + 1 → N`: given `C^{N+1}` data `g`, the potential `bmPot g` is `C^{N+1}`
  (`bmPotential_contDiff_of_hasCompactSupport`, since the kernel is locally integrable), and both
  families of Wirtinger derivatives of `bmPot g` are again `C^{N+1}`:

  `∂_j (bmPot g) = bmPot (∂_j g)`,   `∂̄_j (bmPot g) = bmPot (∂̄_j g)`,

  pointwise, by `bmPot_dCoord` / `bmPot_dbarCoord` (the derivative of a convolution never touches
  the singular kernel).  The differentiated data `∂_j g`, `∂̄_j g` are `C^N`, compactly supported
  (`HasCompactSupport.fderiv`), and have finite `C^{N,α}`-norm
  (`Work.NN.Core.exists_holderNorm_wirtinger_le`), so the induction hypothesis applies to them.
  The smoothness upgrade `C^{N+1}` + `C^{N+1}` Wirtinger derivatives ⟹ `C^{N+2}` is
  `Work.CR.Flat.Holder.contDiffOn_succ_of_wirtinger` on `Ω = univ`.
-/

namespace Work.NN.Final

open scoped NNReal ENNReal ContDiff
open Set MeasureTheory

/-! ## Auxiliary lemmas -/

/-- A compactly supported function vanishes outside a ball of positive radius. -/
lemma exists_radius_vanishing_of_hasCompactSupport {n : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hc : HasCompactSupport g) : ∃ R : ℝ, 0 < R ∧ ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0 := by
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Fin n → ℂ)
  refine ⟨max r 0 + 1, by positivity, fun x hx => ?_⟩
  by_contra hx0
  have hmem : x ∈ tsupport g := subset_tsupport g (Function.mem_support.mpr hx0)
  have h1 : ‖x‖ ≤ r := by
    have h := hr hmem
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  linarith [le_max_left r 0]

/-- `bmPot = bmPotential`: the Bochner–Martinelli potential with the singularity at the origin
equals the one with the singularity translated to the point (a change of variables). -/
lemma bmPot_eq_bmPotential {n : ℕ} (g : Fin n → (Fin n → ℂ) → ℂ) :
    Work.CR.Flat.Cauchy.bmPot g = Work.CR.Flat.Cauchy.bmPotential g :=
  funext fun z => (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot g z).symm

/-- **The `(1,0)`-Wirtinger derivative of the Bochner–Martinelli potential is the potential of the
differentiated data**: `∂_j (bmPot f) = bmPot (∂_j f)` for `C¹` data with compact support. -/
lemma bmPot_dCoord_eq {n : ℕ} (hn : 0 < n) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ k, ContDiff ℝ 1 (f k)) (hcs : ∀ k, HasCompactSupport (f k)) (j : Fin n) :
    (fun z => Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPot f) z)
      = fun z => Work.CR.Flat.Cauchy.bmPot
          (fun k => fun y => Work.CR.Flat.dCoord j (f k) y) z := by
  have hRj : ∀ k, ∃ R : ℝ, 0 < R ∧ ∀ x : Fin n → ℂ, R ≤ ‖x‖ → f k x = 0 :=
    fun k => exists_radius_vanishing_of_hasCompactSupport (hcs k)
  choose R hRpos hR using hRj
  have hRpos' : 0 < (∑ k, R k) + 1 := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => le_of_lt (hRpos i)); linarith
  refine funext fun z => ?_
  rw [Work.CR.Flat.Cauchy.bmCz.bmPot_dCoord hn hf (R := (∑ k, R k) + 1) hRpos'
    (fun k x hx => hR k x (le_trans ?_ hx)) j z]
  · rw [Work.CR.Flat.Cauchy.bmPot]
  · exact le_trans (Finset.single_le_sum (fun i _ => le_of_lt (hRpos i)) (Finset.mem_univ k))
      (by simp)

/-- **The `(0,1)`-Wirtinger derivative of the Bochner–Martinelli potential is the potential of the
differentiated data**: `∂̄_j (bmPot f) = bmPot (∂̄_j f)` for `C¹` data with compact support. -/
lemma bmPot_dbarCoord_eq {n : ℕ} (hn : 0 < n) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ k, ContDiff ℝ 1 (f k)) (hcs : ∀ k, HasCompactSupport (f k)) (j : Fin n) :
    (fun z => Work.CR.Flat.dbarCoord j (Work.CR.Flat.Cauchy.bmPot f) z)
      = fun z => Work.CR.Flat.Cauchy.bmPot
          (fun k => fun y => Work.CR.Flat.dbarCoord j (f k) y) z := by
  have hRj : ∀ k, ∃ R : ℝ, 0 < R ∧ ∀ x : Fin n → ℂ, R ≤ ‖x‖ → f k x = 0 :=
    fun k => exists_radius_vanishing_of_hasCompactSupport (hcs k)
  choose R hRpos hR using hRj
  have hRpos' : 0 < (∑ k, R k) + 1 := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => le_of_lt (hRpos i)); linarith
  refine funext fun z => ?_
  rw [Work.CR.Flat.Cauchy.bmPot_dbarCoord hn hf (R := (∑ k, R k) + 1) hRpos'
    (fun k x hx => hR k x (le_trans ?_ hx)) j z]
  · rw [Work.CR.Flat.Cauchy.bmPot]
  · exact le_trans (Finset.single_le_sum (fun i _ => le_of_lt (hRpos i)) (Finset.mem_univ k))
      (by simp)

/-! ## The main theorem -/

theorem bmPot_contDiff_succ {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ N : ℕ, ∀ g : Fin n → (Fin n → ℂ) → ℂ,
      (∀ j, ContDiff ℝ N (g j)) → (∀ j, HasCompactSupport (g j)) →
      (∀ j, Work.CR.Flat.holderNorm N α (g j) Set.univ < ⊤) →
      ContDiff ℝ (N + 1) (Work.CR.Flat.Cauchy.bmPot g) := by
  intro N
  induction N with
  | zero =>
    intro g hg hcs hfin
    have h := Work.NN.Core.contDiff_one_bmPotential_of_holder (n := n) hn hα0 hα1 hcs hfin
    simpa [bmPot_eq_bmPotential g] using h
  | succ N ih =>
    intro g hg hcs hfin
    -- every component is at least `C¹`
    have hg1 : ∀ j, ContDiff ℝ 1 (g j) := fun j => (hg j).of_le (by simp)
    -- the potential itself is `C^{N+1}`
    have hbm : ContDiff ℝ (N + 1) (Work.CR.Flat.Cauchy.bmPot g) := by
      have h := Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport (n := n) hn
        (i := N + 1) (f := g) (fun j => hg j) hcs
      simpa [bmPot_eq_bmPotential g] using h
    -- `∂_j (bmPot g) = bmPot (∂_j g)` is `C^{N+1}` by the induction hypothesis
    have hdc : ∀ j, ContDiff ℝ (N + 1)
        (fun z => Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPot g) z) := by
      intro j
      have hdata : ∀ k, ContDiff ℝ N (fun y => Work.CR.Flat.dCoord j (g k) y) := by
        intro k
        rw [Work.NN.Core.dCoord_eq_comp]
        have h : ContDiff ℝ N (fun z => fderiv ℝ (g k) z) := (hg k).fderiv_right (by simp)
        exact (Work.NN.Core.dCoordLin j).contDiff.comp h
      have hcsd : ∀ k, HasCompactSupport (fun y => Work.CR.Flat.dCoord j (g k) y) := by
        intro k
        rw [Work.NN.Core.dCoord_eq_comp]
        exact ((hcs k).fderiv ℝ).comp_left (map_zero _)
      have hfind : ∀ k, Work.CR.Flat.holderNorm N α
          (fun y => Work.CR.Flat.dCoord j (g k) y) Set.univ < ⊤ := by
        intro k
        obtain ⟨C, _hCpos, hC⟩ := Work.NN.Core.exists_holderNorm_wirtinger_le (n := n) N (α := α)
          (Ω := Set.univ) isOpen_univ
        have hg' : ContDiffOn ℝ (↑N + 1) (g k) Set.univ := by simpa using (hg k).contDiffOn
        exact lt_of_le_of_lt (hC (g k) hg' j).2
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin k))
      have h := ih (fun k => fun y => Work.CR.Flat.dCoord j (g k) y) hdata hcsd hfind
      simpa [bmPot_dCoord_eq hn hg1 hcs j] using h
    -- `∂̄_j (bmPot g) = bmPot (∂̄_j g)` is `C^{N+1}` by the induction hypothesis
    have hdbc : ∀ j, ContDiff ℝ (N + 1)
        (fun z => Work.CR.Flat.dbarCoord j (Work.CR.Flat.Cauchy.bmPot g) z) := by
      intro j
      have hdata : ∀ k, ContDiff ℝ N (fun y => Work.CR.Flat.dbarCoord j (g k) y) := by
        intro k
        rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp]
        have h : ContDiff ℝ N (fun z => fderiv ℝ (g k) z) := (hg k).fderiv_right (by simp)
        exact (Work.CR.Flat.Polydisc.dbarCoordPhi j).contDiff.comp h
      have hcsd : ∀ k, HasCompactSupport (fun y => Work.CR.Flat.dbarCoord j (g k) y) := by
        intro k
        rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp]
        exact ((hcs k).fderiv ℝ).comp_left (map_zero _)
      have hfind : ∀ k, Work.CR.Flat.holderNorm N α
          (fun y => Work.CR.Flat.dbarCoord j (g k) y) Set.univ < ⊤ := by
        intro k
        obtain ⟨C, _hCpos, hC⟩ := Work.NN.Core.exists_holderNorm_wirtinger_le (n := n) N (α := α)
          (Ω := Set.univ) isOpen_univ
        have hg' : ContDiffOn ℝ (↑N + 1) (g k) Set.univ := by simpa using (hg k).contDiffOn
        exact lt_of_le_of_lt (hC (g k) hg' j).1
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin k))
      have h := ih (fun k => fun y => Work.CR.Flat.dbarCoord j (g k) y) hdata hcsd hfind
      simpa [bmPot_dbarCoord_eq hn hg1 hcs j] using h
    -- smoothness upgrade via the Wirtinger derivatives
    rw [← contDiffOn_univ]
    refine Work.CR.Flat.Holder.contDiffOn_succ_of_wirtinger (Ω := Set.univ) isOpen_univ ?_ ?_ ?_ ?_
    · exact (hbm.differentiable (by simp)).differentiableOn
    · exact hbm.contDiffOn
    · intro j; exact (hdc j).contDiffOn
    · intro j; exact (hdbc j).contDiffOn

end Work.NN.Final
