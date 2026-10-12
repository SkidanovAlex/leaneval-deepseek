import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPQw_mass_le
import Submission.Work.BoseFixB1S.fibreSandwichB1
import Submission.Work.BoseFixB1S.n0SlotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.eOneZeroOffB1`

**Off-`A` vanishing of the whole `n₀` functional calculus.**  For a state `Φ : X (n+1) → ℝ`,
every pointwise function `g`, and a slot `i` whose coordinate `x i` lies outside the box `A`,
both `g(n₀)` applied to the mean-free projection `Q_{B,i}Φ` and `g(n₀)` applied to the box
projection `P_{B,i}Φ` vanish at `x`:

  `x i ∉ A ⟹ n0FunOp volA A g (boxQInd volA A i Φ) x = 0`,
  `x i ∉ A ⟹ n0FunOp volA A g (boxPInd volA A i Φ) x = 0`.

## The mathematics

The two FS box projections of `Work.UBBInputs8` both carry the box indicator of slot `i`:

  `(P_{B,i}Ψ)(x) = (1/volA)·(∫_{z∈A} Ψ(x|i↦z) dz) · 1_A(x i)`,
  `(Q_{B,i}Ψ)(x) = 1_A(x i)·Ψ x − (P_{B,i}Ψ)(x)`.

Hence:

* `boxPInd` and `boxQInd` in slot `i` **vanish at every point whose `i`-th coordinate is outside
  `A`** (`boxPInd_eq_zero_of_notMem_self`, `boxQInd_eq_zero_of_notMem_self`) — the indicator
  factor is `0` there;
* and the class `{Ψ | ∀ y, y i ∉ A → Ψ y = 0}` is **stable under every slot operator**
  appearing in the iteration `n0Iter`: applying `boxPInd volA A j` to such a `Ψ` stays in the
  class, because for `j ≠ i` the mean `∫_{z∈A} Ψ(x|j↦z) dz` has an integrand which vanishes on
  `A` (the `i`-th coordinate of `x|j↦z` is still `x i ∉ A`), and for `j = i` the indicator kills
  it (`boxPInd_eq_zero_of_forall_off`).  The pointwise complement `1 − P_{B,j}` of two class
  members is again a class member.

Iterating (`n0Iter_apply_eq_zero`) gives the vanishing of every subset idempotent `n0ProjOp S`,
hence of every Lagrange idempotent `n0LagrangeOp k` (a finite sum), hence of the whole finite
functional calculus `n0FunOp g = Σ_k g k • n0LagrangeOp k`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The projections in their own slot vanish outside `A` -/

/-- The box projection in its own slot vanishes whenever that slot's coordinate lies outside `A`
(the box indicator is `0` there). -/
theorem boxPInd_eq_zero_of_notMem_self {N : ℕ} {volA : ℝ} {A : Set E3} (i : Fin N)
    (Φ : X N → ℝ) : ∀ y, y i ∉ A → Work.UBBInputs8.boxPInd volA A i Φ y = 0 := by
  intro y hy
  simp only [Work.UBBInputs8.boxPInd, Set.indicator_of_notMem hy, mul_zero]

/-- The mean-free box projection `Q_{B,i} = 1_A(·i)·id − P_{B,i}` in its own slot vanishes
whenever that slot's coordinate lies outside `A`. -/
theorem boxQInd_eq_zero_of_notMem_self {N : ℕ} {volA : ℝ} {A : Set E3} (i : Fin N)
    (Φ : X N → ℝ) : ∀ y, y i ∉ A → Work.UBBInputs8.boxQInd volA A i Φ y = 0 := by
  intro y hy
  have hp : Work.UBBInputs8.boxPInd volA A i Φ y = 0 :=
    boxPInd_eq_zero_of_notMem_self i Φ y hy
  simp only [Work.UBBInputs8.boxQInd, Set.indicator_of_notMem hy, zero_mul, hp, sub_zero]

/-! ## 2. Stability of the off-`A` class under the slot projections -/

/-- If `Ψ` vanishes at every point whose `i`-th coordinate is outside `A`, then so does the slot
projection `P_{B,j}Ψ` for **every** slot `j` (`j = i`: the indicator kills it; `j ≠ i`: the mean
has an integrand vanishing on `A`). -/
theorem boxPInd_eq_zero_of_forall_off {N : ℕ} {volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (i j : Fin N) {Ψ : X N → ℝ} (hΨ : ∀ y, y i ∉ A → Ψ y = 0) :
    ∀ y, y i ∉ A → Work.UBBInputs8.boxPInd volA A j Ψ y = 0 := by
  intro y hy
  by_cases hji : j = i
  · rw [hji]
    exact boxPInd_eq_zero_of_notMem_self i Ψ y hy
  · have hint : (∫ z in A, Ψ (Function.update y j z)) = 0 := by
      rw [show (∫ z in A, Ψ (Function.update y j z)) = ∫ _z in A, (0 : ℝ) from
        MeasureTheory.setIntegral_congr_fun hA (fun z hz => ?_)]
      · simp
      · exact hΨ _ (by
          rw [Function.update_apply, if_neg (fun h : i = j => hji h.symm)]
          exact hy)
    simp only [Work.UBBInputs8.boxPInd, hint, mul_zero, zero_mul]

/-! ## 3. The slot iteration, the Lagrange idempotents and the functional calculus -/

/-- **The iteration `n0Iter` preserves the off-`A` class.**  If `Ψ` vanishes at every point whose
`i`-th coordinate is outside `A`, then so does the function obtained by applying the slot-list
iteration (each slot `j` acting either by `P_{B,j}` or by its pointwise complement). -/
theorem n0Iter_apply_eq_zero {N : ℕ} {volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (i : Fin N) (b : Fin N → Bool) (l : List (Fin N)) (Ψ : X N → ℝ)
    (hΨ : ∀ y, y i ∉ A → Ψ y = 0) :
    ∀ x, x i ∉ A → n0Iter volA A b l Ψ x = 0 := by
  induction l generalizing Ψ with
  | nil => intro x hx; exact hΨ x hx
  | cons j l' ih =>
    intro x hx
    rw [show n0Iter volA A b (j :: l') Ψ
        = (if b j then
            n0Iter volA A b l' (fun x => Work.UBBInputs8.boxPInd volA A j Ψ x)
          else
            n0Iter volA A b l' (fun x => Ψ x - Work.UBBInputs8.boxPInd volA A j Ψ x)) from rfl]
    have hP : ∀ y, y i ∉ A → Work.UBBInputs8.boxPInd volA A j Ψ y = 0 :=
      boxPInd_eq_zero_of_forall_off hA i j hΨ
    by_cases hbj : b j
    · rw [if_pos hbj]
      exact ih _ hP x hx
    · rw [if_neg hbj]
      refine ih _ (fun y hy => ?_) x hx
      rw [hΨ y hy, hP y hy, sub_zero]

/-- Every **subset idempotent** `n0ProjOp S = ∏_{i∈S}P_{B,i}·∏_{i∉S}(1−P_{B,i})` vanishes at a
point whose `i`-th coordinate is outside `A`, provided the argument does. -/
theorem n0ProjOp_apply_eq_zero {N : ℕ} {volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (i : Fin N) (S : Finset (Fin N)) (Ψ : X N → ℝ) (hΨ : ∀ y, y i ∉ A → Ψ y = 0) :
    ∀ x, x i ∉ A → n0ProjOp volA A S Ψ x = 0 := by
  intro x hx
  have h := n0Iter_apply_eq_zero (volA := volA) hA i (fun k => decide (k ∈ S))
    (List.ofFn (fun k : Fin N => k)) Ψ hΨ x hx
  simpa only [n0ProjOp] using h

/-- The **Lagrange idempotent** `n0LagrangeOp k` (a finite sum of subset idempotents) vanishes at
a point whose `i`-th coordinate is outside `A`, provided the argument does. -/
theorem n0LagrangeOp_apply_eq_zero {N : ℕ} {volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (i : Fin N) (k : ℕ) (Ψ : X N → ℝ) (hΨ : ∀ y, y i ∉ A → Ψ y = 0) :
    ∀ x, x i ∉ A → n0LagrangeOp volA A k Ψ x = 0 := by
  intro x hx
  simp only [n0LagrangeOp]
  exact Finset.sum_eq_zero (fun S _ => n0ProjOp_apply_eq_zero hA i S Ψ hΨ x hx)

/-- **The functional calculus vanishes off `A`.**  If `Ψ` vanishes at every point whose `i`-th
coordinate is outside `A`, then so does `g(n₀)Ψ = Σ_k g k • n0LagrangeOp k Ψ`. -/
theorem n0FunOp_apply_eq_zero {N : ℕ} {volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (i : Fin N) (g : ℝ → ℝ) (Ψ : X N → ℝ) (hΨ : ∀ y, y i ∉ A → Ψ y = 0) :
    ∀ x, x i ∉ A → n0FunOp volA A g Ψ x = 0 := by
  intro x hx
  simp only [n0FunOp]
  exact Finset.sum_eq_zero (fun k _ => by
    rw [n0LagrangeOp_apply_eq_zero hA i k Ψ hΨ x hx, mul_zero])

/-! ## 4. The requested lemma -/

theorem eOneZeroOffB1 {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin (n + 1)) (g : ℝ → ℝ) (Φ : Submission.BoseGases.X (n + 1) → ℝ) :
    (∀ x : Submission.BoseGases.X (n + 1), x i ∉ A →
        Work.BoseFixB1S.n0FunOp volA A g (Work.UBBInputs8.boxQInd volA A i Φ) x = 0)
      ∧ (∀ x : Submission.BoseGases.X (n + 1), x i ∉ A →
        Work.BoseFixB1S.n0FunOp volA A g (Work.UBBInputs8.boxPInd volA A i Φ) x = 0) := by
  constructor
  · intro x hx
    exact n0FunOp_apply_eq_zero hA i g _ (boxQInd_eq_zero_of_notMem_self i Φ) x hx
  · intro x hx
    exact n0FunOp_apply_eq_zero hA i g _ (boxPInd_eq_zero_of_notMem_self i Φ) x hx

end Work.BoseFixB1S
