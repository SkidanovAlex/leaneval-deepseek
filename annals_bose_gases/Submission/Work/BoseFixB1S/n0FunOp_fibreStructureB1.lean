import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxM1Info
import Submission.Work.BoseFixB1S.boxPInd_boxCompT
import Submission.Work.BoseFixB1S.n0FibPIndPresB1
import Submission.Work.BoseFixB1S.n0FunOp_eq_sum_card
import Submission.Work.BoseFixB1S.n0IterFibPresB1
import Submission.Work.BoseFixB1S.n0IterZeroPresB1
import Submission.Work.BoseFixB1S.n0SpectralAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## 1. The two structure properties -/

/-- **The fibre property at slot `i`** with reference point `c₀`: `F` is, as a function of the
`i`-th coordinate, the box indicator `1_A` times the value at the reference configuration
`x|i↦c₀`.  (For `c₀ ∈ A` this says exactly that `F x = 1_A(x_i) · K(x∖i)` for a function `K` of
the remaining coordinates.) -/
def n0FibProp {N : ℕ} (A : Set E3) (i : Fin N) (c₀ : E3) (F : X N → ℝ) : Prop :=
  ∀ x : X N, F x = A.indicator (fun _ => (1 : ℝ)) (x i) * F (Function.update x i c₀)

/-- **The vanishing property at slot `i`**: `F` vanishes wherever the `i`-th coordinate leaves
the box `A`. -/
def n0ZeroProp {N : ℕ} (A : Set E3) (i : Fin N) (F : X N → ℝ) : Prop :=
  ∀ x : X N, x i ∉ A → F x = 0

/-- The fibre property is stronger than the vanishing property. -/
theorem n0FibProp_zero {N : ℕ} {A : Set E3} {i : Fin N} {c₀ : E3} {F : X N → ℝ}
    (h : n0FibProp A i c₀ F) : n0ZeroProp A i F := by
  intro x hx
  rw [h x, Set.indicator_of_notMem hx, zero_mul]

/-! ## 2. The `P_{B,i}`-side: base case, linearity, preservation -/

/-- **The base case.**  `P_{B,i}Φ = volA⁻¹∫_{z∈A}Φ(x|i↦z)dz · 1_A(x_i)` is fibre-constant, the
mean being unchanged by re-inserting *any* value in slot `i`; at the reference point the
indicator is `1` because `c₀ ∈ A`. -/
theorem n0FibProp_base {N : ℕ} {volA : ℝ} {A : Set E3} {i : Fin N} {c₀ : E3} (hc₀ : c₀ ∈ A)
    (Φ : X N → ℝ) : n0FibProp A i c₀ (UBBInputs8.boxPInd volA A i Φ) := by
  intro x
  simp only [UBBInputs8.boxPInd, Function.update_self]
  rw [Set.indicator_of_mem hc₀, mul_one]
  have hInt : (∫ z in A, Φ (Function.update (Function.update x i c₀) i z))
      = ∫ z in A, Φ (Function.update x i z) := by
    apply integral_congr_ae
    filter_upwards with z
    rw [Function.update_idem]
  rw [hInt]
  ring

/-- The fibre property is preserved by pointwise subtraction. -/
theorem n0FibProp_sub {N : ℕ} {A : Set E3} {i : Fin N} {c₀ : E3} {F G : X N → ℝ}
    (hF : n0FibProp A i c₀ F) (hG : n0FibProp A i c₀ G) : n0FibProp A i c₀ (F - G) := by
  intro x
  rw [Pi.sub_apply, hF x, hG x, Pi.sub_apply]
  ring

/-- The fibre property is preserved by finite linear combinations. -/
theorem n0FibProp_sum {N : ℕ} {A : Set E3} {i : Fin N} {c₀ : E3} {ι : Type*} [Fintype ι]
    {c : ι → ℝ} {F : ι → X N → ℝ} (hF : ∀ S, n0FibProp A i c₀ (F S)) :
    n0FibProp A i c₀ (fun x => ∑ S, c S * F S x) := by
  intro x
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [hF S x]
  ring

/-- The subset idempotent `n0ProjOp` (a slot-wise composition of the `P_{B,j}` and their
single-slot complements) preserves the fibre property. -/
theorem n0FibProp_n0ProjOp {N : ℕ} {volA : ℝ} {A : Set E3} {i : Fin N} {c₀ : E3}
    (hc₀ : c₀ ∈ A) (S : Finset (Fin N)) {Ψ : X N → ℝ} (hΨ : n0FibProp A i c₀ Ψ) :
    n0FibProp A i c₀ (n0ProjOp volA A S Ψ) :=
  n0IterFibPresB1 hc₀ (fun j => decide (j ∈ S)) (List.ofFn (fun j : Fin N => j)) hΨ

/-- **The `P_{B,i}`-side conclusion**: `g(n₀)(P_{B,i}Φ)` is fibre-affine in slot `i`. -/
theorem n0FibProp_n0FunOp {N : ℕ} {volA : ℝ} {A : Set E3} {i : Fin N} {c₀ : E3}
    (hc₀ : c₀ ∈ A) (g : ℝ → ℝ) {Ψ : X N → ℝ} (hΨ : n0FibProp A i c₀ Ψ) :
    n0FibProp A i c₀ (n0FunOp volA A g Ψ) := by
  rw [n0FunOp_eq_sum_card volA A g Ψ]
  exact n0FibProp_sum (fun S => n0FibProp_n0ProjOp hc₀ S hΨ)

/-! ## 3. The `Q_{B,i}`-side: base case, linearity, preservation -/

/-- **The base case for the mean-free projection.**  `Q_{B,i}Φ = 1_A(x_i)Φ − P_{B,i}Φ` vanishes
wherever `x_i ∉ A` (both terms carry the box indicator).  Note that `Q_{B,i}Φ` is *not* fibre
affine — only its vanishing is claimed, and only that is true. -/
theorem n0ZeroProp_base {N : ℕ} {volA : ℝ} {A : Set E3} {i : Fin N} (Φ : X N → ℝ) :
    n0ZeroProp A i (UBBInputs8.boxQInd volA A i Φ) := by
  intro x hx
  simp only [UBBInputs8.boxQInd, UBBInputs8.boxPInd]
  rw [Set.indicator_of_notMem hx]
  ring

/-- The vanishing property is preserved by pointwise subtraction. -/
theorem n0ZeroProp_sub {N : ℕ} {A : Set E3} {i : Fin N} {F G : X N → ℝ}
    (hF : n0ZeroProp A i F) (hG : n0ZeroProp A i G) : n0ZeroProp A i (F - G) := by
  intro x hx
  rw [Pi.sub_apply, hF x hx, hG x hx, sub_zero]

/-- The vanishing property is preserved by finite linear combinations. -/
theorem n0ZeroProp_sum {N : ℕ} {A : Set E3} {i : Fin N} {ι : Type*} [Fintype ι]
    {c : ι → ℝ} {F : ι → X N → ℝ} (hF : ∀ S, n0ZeroProp A i (F S)) :
    n0ZeroProp A i (fun x => ∑ S, c S * F S x) := by
  intro x hx
  apply Finset.sum_eq_zero
  intro S _
  rw [hF S x hx, mul_zero]

/-- The subset idempotent `n0ProjOp` preserves the vanishing property. -/
theorem n0ZeroProp_n0ProjOp {N : ℕ} {volA : ℝ} {A : Set E3} {i : Fin N}
    (S : Finset (Fin N)) {Ψ : X N → ℝ} (hΨ : n0ZeroProp A i Ψ) :
    n0ZeroProp A i (n0ProjOp volA A S Ψ) :=
  n0IterZeroPresB1 (fun j => decide (j ∈ S)) (List.ofFn (fun j : Fin N => j)) hΨ

/-- **The `Q_{B,i}`-side conclusion**: `g(n₀)(Q_{B,i}Φ)` vanishes off `A` in slot `i`. -/
theorem n0ZeroProp_n0FunOp {N : ℕ} {volA : ℝ} {A : Set E3} {i : Fin N} (g : ℝ → ℝ)
    {Ψ : X N → ℝ} (hΨ : n0ZeroProp A i Ψ) : n0ZeroProp A i (n0FunOp volA A g Ψ) := by
  rw [n0FunOp_eq_sum_card volA A g Ψ]
  exact n0ZeroProp_sum (fun S => n0ZeroProp_n0ProjOp S hΨ)

/-! ## 4. The fibre structure of the `n₀` layer at the FS box projection -/

theorem n0FunOp_fibreStructureB1 {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin (n + 1)) {a₀ : EuclideanSpace ℝ (Fin 3)} (ha₀ : a₀ ∈ A) (g : ℝ → ℝ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) :
    (∀ (t : EuclideanSpace ℝ (Fin 3)) (r : Submission.BoseGases.X n),
        Work.BoseFixB1S.n0FunOp volA A g (Work.UBBInputs8.boxPInd volA A i Φ)
            (Submission.BoseGases.kcInsN n i (t, r))
          = A.indicator (fun _ => (1 : ℝ)) t
            * Work.BoseFixB1S.n0FunOp volA A g (Work.UBBInputs8.boxPInd volA A i Φ)
                (Submission.BoseGases.kcInsN n i (a₀, r)))
      ∧ (∀ x : Submission.BoseGases.X (n + 1), x i ∉ A →
          Work.BoseFixB1S.n0FunOp volA A g (Work.UBBInputs8.boxQInd volA A i Φ) x = 0)
      ∧ (∀ x : Submission.BoseGases.X (n + 1), x i ∉ A →
          Work.BoseFixB1S.n0FunOp volA A g (Work.UBBInputs8.boxPInd volA A i Φ) x = 0) := by
  have hFib : n0FibProp A i a₀ (n0FunOp volA A g (UBBInputs8.boxPInd volA A i Φ)) :=
    n0FibProp_n0FunOp ha₀ g (n0FibProp_base ha₀ Φ)
  have hZeroQ : n0ZeroProp A i (n0FunOp volA A g (UBBInputs8.boxQInd volA A i Φ)) :=
    n0ZeroProp_n0FunOp g (n0ZeroProp_base Φ)
  refine ⟨?_, ?_, ?_⟩
  · intro t r
    have h := hFib (kcInsN n i (t, r))
    rw [kc_insN_apply_same, update_kcInsN] at h
    exact h
  · intro x hx
    exact hZeroQ x hx
  · intro x hx
    exact n0FibProp_zero hFib x hx

end Work.BoseFixB1S
