import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxOpA
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxOpGDefs` — one-slot operator notation for `boxOpG` / `boxOpZ`

`Work.BoseFixB1.boxOpG A f h Ψ x = Σ_i 1_A(x_i)·f(x_i)·∫_{z∈A} h z·Ψ(x_{i←z})` is a sum of
*one-slot* operators.  This module fixes the notation used to manipulate them:

* `peel A i h Φ = fun y => ∫ z in A, h z * Φ (y[i:=z])` — the one-slot peel,
* `mulSlot i φ Φ = fun y => φ (y i) * Φ y` — multiplication by a function of one coordinate,

and the four one-slot operators that appear in the box identity

* `Aop A g i = mulSlot i (1_A) ∘ peel i g`   (the `(1_A, g)` summand of `boxOpG A 1 g`),
* `Bop A g i = mulSlot i g ∘ peel i 1`       (the `(g, 1)` summand of `boxOpG A g 1`),
* `Cop A g i = mulSlot i g ∘ peel i g`       (the `(g, g)` summand of `boxOpZ A g g`),
* `Dop A i   = mulSlot i (1_A) ∘ peel i 1`   (the `(1_A, 1)` summand of `boxOpG A 1 1`),

together with the definitional bridges

`boxOpG A 1 g = Σ_i Aop A g i`, `boxOpG A g 1 = boxOpZ A g 1 = Σ_i Bop A g i`,
`boxOpZ A g g = Σ_i Cop A g i`, `boxOpG A 1 1 = Σ_i Dop A i`

(the second needs `tsupport g ⊆ A`, i.e. `1_A(·)·g = g` pointwise).

The point of the notation: with it, the box commutator identity

`boxOpG A 1 g (boxOpG A g 1 Ψ) - boxOpZ A g 1 (boxOpG A 1 g Ψ)
   = (∫_A g²)·boxOpG A 1 1 Ψ - (∫_A 1)·boxOpZ A g g Ψ`

reads `Σ_{i,j} [Aop_i, Bop_j] Ψ = Σ_i (∫g²)·Dop_i Ψ - Σ_i (∫1)·Cop_i Ψ`, the diagonal
`i = j` terms giving the right-hand side and the off-diagonal terms cancelling because
`Aop_i` and `Bop_j` act on *different* slots for `i ≠ j`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false

/-- Abbreviation for `ℝ³`, local to this file. -/
abbrev BoxE3 : Type := EuclideanSpace ℝ (Fin 3)

/-- **The one-slot peel**: `(peel A i h Φ) y = ∫_{z∈A} h z · Φ(y[i:=z])`. -/
noncomputable def peel {M : ℕ} (A : Set BoxE3) (i : Fin M) (h : BoxE3 → ℝ) (Φ : X M → ℝ) :
    X M → ℝ :=
  fun y => ∫ z in A, h z * Φ (Function.update y i z)

/-- **Multiplication by a function of one coordinate**: `(mulSlot i φ Φ) y = φ (y i) · Φ y`. -/
noncomputable def mulSlot {M : ℕ} (i : Fin M) (φ : BoxE3 → ℝ) (Φ : X M → ℝ) : X M → ℝ :=
  fun y => φ (y i) * Φ y

/-- The `(1_A, g)` one-slot operator: the `i`-th summand of `boxOpG A 1 g`. -/
noncomputable def Aop {M : ℕ} (A : Set BoxE3) (g : BoxE3 → ℝ) (i : Fin M) (Φ : X M → ℝ) :
    X M → ℝ :=
  mulSlot i (A.indicator (fun _ => (1 : ℝ))) (peel A i g Φ)

/-- The `(g, 1)` one-slot operator: the `i`-th summand of `boxOpG A g 1` and of `boxOpZ A g 1`. -/
noncomputable def Bop {M : ℕ} (A : Set BoxE3) (g : BoxE3 → ℝ) (i : Fin M) (Φ : X M → ℝ) :
    X M → ℝ :=
  mulSlot i g (peel A i (fun _ => (1 : ℝ)) Φ)

/-- The `(g, g)` one-slot operator: the `i`-th summand of `boxOpZ A g g`. -/
noncomputable def Cop {M : ℕ} (A : Set BoxE3) (g : BoxE3 → ℝ) (i : Fin M) (Φ : X M → ℝ) :
    X M → ℝ :=
  mulSlot i g (peel A i g Φ)

/-- The `(1_A, 1)` one-slot operator: the `i`-th summand of `boxOpG A 1 1`. -/
noncomputable def Dop {M : ℕ} (A : Set BoxE3) (i : Fin M) (Φ : X M → ℝ) : X M → ℝ :=
  mulSlot i (A.indicator (fun _ => (1 : ℝ))) (peel A i (fun _ => (1 : ℝ)) Φ)

@[simp] lemma peel_apply {M : ℕ} (A : Set BoxE3) (i : Fin M) (h : BoxE3 → ℝ) (Φ : X M → ℝ)
    (y : X M) :
    peel A i h Φ y = ∫ z in A, h z * Φ (Function.update y i z) := rfl

@[simp] lemma mulSlot_apply {M : ℕ} (i : Fin M) (φ : BoxE3 → ℝ) (Φ : X M → ℝ) (y : X M) :
    mulSlot i φ Φ y = φ (y i) * Φ y := rfl

@[simp] lemma Aop_apply {M : ℕ} (A : Set BoxE3) (g : BoxE3 → ℝ) (i : Fin M) (Φ : X M → ℝ)
    (y : X M) :
    Aop A g i Φ y
      = A.indicator (fun _ => (1 : ℝ)) (y i) * ∫ z in A, g z * Φ (Function.update y i z) :=
  rfl

@[simp] lemma Bop_apply {M : ℕ} (A : Set BoxE3) (g : BoxE3 → ℝ) (i : Fin M) (Φ : X M → ℝ)
    (y : X M) :
    Bop A g i Φ y
      = g (y i) * ∫ z in A, (1 : ℝ) * Φ (Function.update y i z) :=
  rfl

@[simp] lemma Cop_apply {M : ℕ} (A : Set BoxE3) (g : BoxE3 → ℝ) (i : Fin M) (Φ : X M → ℝ)
    (y : X M) :
    Cop A g i Φ y = g (y i) * ∫ z in A, g z * Φ (Function.update y i z) :=
  rfl

@[simp] lemma Dop_apply {M : ℕ} (A : Set BoxE3) (i : Fin M) (Φ : X M → ℝ) (y : X M) :
    Dop A i Φ y
      = A.indicator (fun _ => (1 : ℝ)) (y i) * ∫ z in A, (1 : ℝ) * Φ (Function.update y i z) :=
  rfl

/-! ## The definitional bridges to `boxOpG` / `boxOpZ` -/

lemma boxOpG_one_g {M : ℕ} (A : Set BoxE3) (g : BoxE3 → ℝ) (Φ : X M → ℝ) :
    boxOpG A (fun _ => (1 : ℝ)) g Φ = ∑ i : Fin M, Aop A g i Φ := by
  funext y
  simp only [boxOpG, Finset.sum_apply, Aop_apply, mul_one]

lemma boxOpG_g_one {M : ℕ} (A : Set BoxE3) (g : BoxE3 → ℝ)
    (hg : ∀ z, A.indicator (fun _ => (1 : ℝ)) z * g z = g z) (Φ : X M → ℝ) :
    boxOpG A g (fun _ => (1 : ℝ)) Φ = ∑ i : Fin M, Bop A g i Φ := by
  funext y
  simp only [boxOpG, Finset.sum_apply, Bop_apply]
  exact Finset.sum_congr rfl (fun i _ => by rw [hg (y i)])

lemma boxOpZ_g_one {M : ℕ} (A : Set BoxE3) (g : BoxE3 → ℝ) (Φ : X M → ℝ) :
    boxOpZ A g (fun _ => (1 : ℝ)) Φ = ∑ i : Fin M, Bop A g i Φ := by
  funext y
  simp only [boxOpZ, Finset.sum_apply, Bop_apply]

lemma boxOpZ_g_g {M : ℕ} (A : Set BoxE3) (g : BoxE3 → ℝ) (Φ : X M → ℝ) :
    boxOpZ A g g Φ = ∑ i : Fin M, Cop A g i Φ := by
  funext y
  simp only [boxOpZ, Finset.sum_apply, Cop_apply]

lemma boxOpG_one_one {M : ℕ} (A : Set BoxE3) (Φ : X M → ℝ) :
    boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Φ = ∑ i : Fin M, Dop A i Φ := by
  funext y
  simp only [boxOpG, Finset.sum_apply, Dop_apply, mul_one]

/-- If `tsupport g ⊆ A` then `1_A · g = g` pointwise (in particular `boxOpG A g 1 = boxOpZ A g 1`). -/
lemma indicator_mul_eq_self_of_tsupport {A : Set BoxE3} {g : BoxE3 → ℝ} (hgs : tsupport g ⊆ A)
    (z : BoxE3) :
    A.indicator (fun _ => (1 : ℝ)) z * g z = g z := by
  by_cases hz : z ∈ A
  · rw [Set.indicator_of_mem hz, one_mul]
  · have hz' : z ∉ Function.support g := fun h => hz (hgs (subset_tsupport g h))
    have h0 : g z = 0 := by
      by_contra hne
      exact hz' (Function.mem_support.mpr hne)
    rw [Set.indicator_of_notMem hz, zero_mul, h0]

/-! ## Small helpers for evaluating the one-slot operators at an updated configuration -/

@[simp] lemma mulSlot_update_self {M : ℕ} (i : Fin M) (φ : BoxE3 → ℝ) (Φ : X M → ℝ)
    (y : X M) (z : BoxE3) :
    mulSlot i φ Φ (Function.update y i z) = φ z * Φ (Function.update y i z) := by
  simp only [mulSlot_apply, Function.update_self]

@[simp] lemma mulSlot_update_of_ne {M : ℕ} (i j : Fin M) (hij : i ≠ j) (φ : BoxE3 → ℝ)
    (Φ : X M → ℝ) (y : X M) (z : BoxE3) :
    mulSlot j φ Φ (Function.update y i z) = φ (y j) * Φ (Function.update y i z) := by
  simp only [mulSlot_apply, Function.update_apply, if_neg (Ne.symm hij)]

end Work.BoseFixB1
