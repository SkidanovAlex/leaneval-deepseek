/-
# The `∂̄`-telescoping construction with flexible thresholds

Generic data (a cutoff `χ` with thresholds `a < b`, a transform radius `r ≥ 2b`, a tracking
radius `T > b` and an equation radius `e < a`) for the coordinate-by-coordinate telescoping
construction solving `∂̄u = f` on a polydisc, together with the construction itself.

The point of the flexible thresholds is that the ratio `e / T` — the polydisc on which the
`∂̄`-equation is solved versus the region where the data are read — can be made arbitrarily
close to `1`, which is what the Newlander–Nirenberg small-perturbation argument needs.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.openSolRec
import Submission.Work.CR.Flat.Polydisc.dbarCoord_mul

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set MeasureTheory

namespace Work.NN.Ratio

/-- Any finite smoothness level is below the `C^∞` level `∞`. -/
lemma le_infty (m : ℕ) : (m : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
  exact_mod_cast le_top

/-- The geometric data of the telescoping construction. -/
structure Geom (n : ℕ) where
  a : ℝ
  b : ℝ
  T : ℝ
  r : ℝ
  e : ℝ
  ha : 0 < a
  hab : a < b
  hbT : b < T
  hea : e < a
  hr : 2 * b ≤ r
  hr0 : 0 < r
  χ : ℂ → ℂ
  hχ_smooth : ContDiff ℝ ∞ χ
  hχ_one : ∀ ζ : ℂ, ‖ζ‖ ≤ a → χ ζ = 1
  hχ_zero : ∀ ζ : ℂ, b ≤ ‖ζ‖ → χ ζ = 0
  hχ_le : ∀ ζ : ℂ, ‖χ ζ‖ ≤ 1
  hχbar_in : ∀ ζ : ℂ, ‖ζ‖ ≤ a → Work.CR.Flat.dbarC χ ζ = 0
  hχbar_out : ∀ ζ : ℂ, b ≤ ‖ζ‖ → Work.CR.Flat.dbarC χ ζ = 0
  cχ : ℝ
  hcχ0 : 0 ≤ cχ
  hcχ : ∀ ζ : ℂ, ‖Work.CR.Flat.dbarC χ ζ‖ ≤ cχ
  cχ' : ℝ
  hcχ'0 : 0 ≤ cχ'
  hcχ' : ∀ ζ ζ' : ℂ, ‖Work.CR.Flat.dbarC χ ζ - Work.CR.Flat.dbarC χ ζ'‖ ≤ cχ' * ‖ζ - ζ'‖
  L : ℝ
  hL0 : 0 ≤ L
  hL : ∀ ζ ζ' : ℂ, ‖χ ζ - χ ζ'‖ ≤ L * ‖ζ - ζ'‖

namespace Geom

variable {n : ℕ} (G : Geom n)

/-- The cutoff in the `j`-th coordinate, as a function on `ℂⁿ`. -/
def cutF (j : Fin n) : (Fin n → ℂ) → ℂ := fun y => G.χ (y j)

/-- The `∂̄`-derivative in the `j`-th coordinate of `cutF j`, as a function. -/
def cutFbar (j : Fin n) : (Fin n → ℂ) → ℂ := fun y => Work.CR.Flat.dbarC G.χ (y j)

/-- The region on which the data at stage `j` are tracked. -/
def trackSet : Set (Fin n → ℂ) := {z | ∀ l, ‖z l‖ < G.T}

/-- The region on which the `∂̄`-equation is solved. -/
def solveSet : Set (Fin n → ℂ) := {z | ∀ l, ‖z l‖ < G.e}

/-- One step of the recursion. -/
def stepData (j : Fin n) (F : Fin n → (Fin n → ℂ) → ℂ) : Fin n → (Fin n → ℂ) → ℂ :=
  fun k => Work.CR.Flat.Cauchy.dbarTransform G.r j (fun y => G.cutFbar j y * F k y)

/-- The data at stage `m` of the recursion. -/
def recF (f : Fin n → (Fin n → ℂ) → ℂ) (m : ℕ) : Fin n → (Fin n → ℂ) → ℂ :=
  Nat.rec f (fun m Fprev => if h : m < n then G.stepData ⟨m, h⟩ Fprev else Fprev) m

/-- The explicit solution. -/
def recU (f : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ :=
  ∑ j : Fin n, Work.CR.Flat.Cauchy.dbarTransform G.r j
    (fun y => G.cutF j y * G.recF f (j : ℕ) j y) z

variable {G}

@[simp] lemma cutF_apply {j : Fin n} {y : Fin n → ℂ} : G.cutF j y = G.χ (y j) := rfl

@[simp] lemma cutFbar_apply {j : Fin n} {y : Fin n → ℂ} :
    G.cutFbar j y = Work.CR.Flat.dbarC G.χ (y j) := rfl

@[simp] lemma recF_zero {f : Fin n → (Fin n → ℂ) → ℂ} : G.recF f 0 = f := rfl

@[simp] lemma mem_trackSet {z : Fin n → ℂ} : z ∈ G.trackSet ↔ ∀ l, ‖z l‖ < G.T := Iff.rfl

@[simp] lemma mem_solveSet {z : Fin n → ℂ} : z ∈ G.solveSet ↔ ∀ l, ‖z l‖ < G.e := Iff.rfl

lemma recF_succ {f : Fin n → (Fin n → ℂ) → ℂ} {m : ℕ} :
    G.recF f (m + 1) = if h : m < n then G.stepData ⟨m, h⟩ (G.recF f m) else G.recF f m := rfl

lemma recF_succ_of_lt {f : Fin n → (Fin n → ℂ) → ℂ} {m : ℕ} (h : m < n) :
    G.recF f (m + 1) = G.stepData ⟨m, h⟩ (G.recF f m) := by
  rw [recF_succ]; simp [h]

lemma contDiff_cutF (j : Fin n) : ContDiff ℝ ∞ (G.cutF j) :=
  G.hχ_smooth.comp (contDiff_apply ℝ ℂ j)

lemma contDiff_dbarC_χ : ContDiff ℝ ∞ (fun z : ℂ => Work.CR.Flat.dbarC G.χ z) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ G.χ) := G.hχ_smooth.fderiv_right (m := ∞) le_rfl
  have h1 : ContDiff ℝ ∞ (fun z : ℂ => fderiv ℝ G.χ z 1) := hfd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun z : ℂ => fderiv ℝ G.χ z Complex.I) := hfd.clm_apply contDiff_const
  rw [show Work.CR.Flat.dbarC G.χ = fun z => (1 / 2 : ℂ) *
      ((fderiv ℝ G.χ z) 1 + Complex.I * (fderiv ℝ G.χ z) Complex.I) from rfl]
  exact contDiff_const.mul (h1.add (contDiff_const.mul hI))

lemma contDiff_cutFbar (j : Fin n) : ContDiff ℝ ∞ (G.cutFbar j) :=
  (contDiff_dbarC_χ (G := G)).comp (contDiff_apply ℝ ℂ j)

lemma dbarCoord_cutF (j : Fin n) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord j (G.cutF j) z = G.cutFbar j z := by
  have hfun : (fun w : ℂ => G.cutF j (Function.update z j w)) = G.χ := by
    funext w; simp [cutF]
  have hdiff : DifferentiableAt ℝ (G.cutF j) (Function.update z j (z j)) := by
    rw [Function.update_eq_self]
    exact (Geom.contDiff_cutF (G := G) j).contDiffAt.differentiableAt (by simp)
  have h := Work.CR.Flat.Cauchy.dbarSolution_dbarC_update_eq_dbarCoord j
    (g := G.cutF j) (z := z) (u := z j) hdiff
  rw [Function.update_eq_self, hfun] at h
  exact h.symm

lemma dbarCoord_cutF_eq_zero {j l : Fin n} (h : l ≠ j) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord l (G.cutF j) z = 0 := by
  show Work.CR.Flat.dbarCoord l (fun y => G.χ (y j)) z = 0
  exact Work.CR.Flat.Cauchy.dbarCoord_single h (u := G.χ)
    (G.hχ_smooth.of_le (le_infty 1)) z

lemma cutF_eq_one {j : Fin n} {y : Fin n → ℂ} (h : ‖y j‖ ≤ G.a) : G.cutF j y = 1 :=
  G.hχ_one _ h

lemma cutF_eq_zero {j : Fin n} {y : Fin n → ℂ} (h : G.b ≤ ‖y j‖) : G.cutF j y = 0 :=
  G.hχ_zero _ h

lemma cutFbar_eq_zero_of_le {j : Fin n} {y : Fin n → ℂ} (h : ‖y j‖ ≤ G.a) :
    G.cutFbar j y = 0 := G.hχbar_in _ h

lemma cutFbar_eq_zero_of_ge {j : Fin n} {y : Fin n → ℂ} (h : G.b ≤ ‖y j‖) :
    G.cutFbar j y = 0 := G.hχbar_out _ h

lemma norm_cutF_le_one (j : Fin n) (y : Fin n → ℂ) : ‖G.cutF j y‖ ≤ 1 := G.hχ_le (y j)

lemma norm_cutFbar_le (j : Fin n) (y : Fin n → ℂ) : ‖G.cutFbar j y‖ ≤ G.cχ := G.hcχ (y j)

/-- Changing only the `j`-th coordinate of a point of `trackSet` keeps the point in
`trackSet` as long as the new `j`-th coordinate is still below `T`. -/
lemma trackSet_update {j : Fin n} {a z : Fin n → ℂ} (hz : z ∈ G.trackSet)
    (h : ∀ l, l ≠ j → a l = z l) (haj : ‖a j‖ < G.T) : a ∈ G.trackSet := by
  intro l
  by_cases hl : l = j
  · subst hl; exact haj
  · rw [h l hl]; exact hz l

lemma solveSet_subset_trackSet {z : Fin n → ℂ} (hz : z ∈ G.solveSet) : z ∈ G.trackSet :=
  fun l => lt_trans (hz l) (lt_trans G.hea (lt_trans G.hab G.hbT))

/-- Any function of the `j`-th coordinate alone has vanishing `∂̄_l`-derivative for `l ≠ j`. -/
lemma dbarCoord_cutFbar_eq_zero {j l : Fin n} (h : l ≠ j) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord l (G.cutFbar j) z = 0 := by
  show Work.CR.Flat.dbarCoord l (fun y => Work.CR.Flat.dbarC G.χ (y j)) z = 0
  exact Work.CR.Flat.Cauchy.dbarCoord_single h (u := fun ζ => Work.CR.Flat.dbarC G.χ ζ)
    ((Geom.contDiff_dbarC_χ (G := G)).of_le (le_infty 1)) z

/-- Product rule for the cutoff: `∂̄_l (χ_j · g) = χ_j · ∂̄_l g` for `l ≠ j`. -/
lemma dbarCoord_cutF_mul {j l : Fin n} (h : l ≠ j) {g : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hg : DifferentiableAt ℝ g z) :
    Work.CR.Flat.dbarCoord l (fun y => G.cutF j y * g y) z
      = G.cutF j z * Work.CR.Flat.dbarCoord l g z := by
  have hχ : DifferentiableAt ℝ (G.cutF j) z :=
    (Geom.contDiff_cutF (G := G) j).contDiffAt.differentiableAt (by simp)
  rw [Work.CR.Flat.Polydisc.dbarCoord_mul l _ _ z hχ hg, dbarCoord_cutF_eq_zero (G := G) h z]
  ring

/-- Product rule for `cutFbar`: `∂̄_l (χ̄_j · g) = χ̄_j · ∂̄_l g` for `l ≠ j`. -/
lemma dbarCoord_cutFbar_mul {j l : Fin n} (h : l ≠ j) {g : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hg : DifferentiableAt ℝ g z) :
    Work.CR.Flat.dbarCoord l (fun y => G.cutFbar j y * g y) z
      = G.cutFbar j z * Work.CR.Flat.dbarCoord l g z := by
  have hχ : DifferentiableAt ℝ (G.cutFbar j) z :=
    (Geom.contDiff_cutFbar (G := G) j).contDiffAt.differentiableAt (by simp)
  rw [Work.CR.Flat.Polydisc.dbarCoord_mul l _ _ z hχ hg, dbarCoord_cutFbar_eq_zero (G := G) h z]
  ring

end Geom

end Work.NN.Ratio
