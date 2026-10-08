import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.s02_classSumSquare
import Submission.Work.BG.CharBridge

/-!
# BG X2: Gorenstein 4.2.12 (the class-multiplication identity)

This file proves `Work.GW2.C16.ClassMultProp`: for a finite group `K`, a conjugacy class
`X ∋ x₀` (presented as a `Finset K` with `x ∈ X ↔ IsConj x x₀`) and an arbitrary class
function `θ`,

`∑_{x,y ∈ X} θ(xy) = |X|² · ∑_{χ ∈ Irr(K)} (θ, χ) · χ(x₀)² / χ(1)`.

The route is the one recorded in the BG design notes for leaf X2:

* the per-irreducible case `χ ∈ Irr(K)` is `Work.BG.s02_classSumSquare` (BG Lemma 2.2-a,
  the central-character square identity `χ(1) · ∑_{x,y∈X} χ(xy) = (∑_{x∈X} χ(x))²`)
  combined with the fact that `X` is a single conjugacy class, so `∑_{x∈X} χ(x) = |X| χ(x₀)`
  and `χ(1) ≠ 0`;
* the general case follows from the Fourier expansion
  `θ = ∑_{χ} (θ, χ) · χ` (`OddOrder.RepresentationTheory.sum_inner_irreducibleCharacter_smul`)
  and `ℂ`-linearity of `θ ↦ ∑_{x,y∈X} θ(xy)`, packaged as the linear map `cfMulSum`.

## Main result

* `Work.BG.classMult` — `Work.GW2.C16.ClassMultProp`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- The functional `θ ↦ ∑_{x,y ∈ X} θ (x * y)`, as a `ℂ`-linear map.  Linearity is what lets
us substitute the Fourier expansion of an arbitrary class function in the proof of the
class-multiplication identity. -/
noncomputable def cfMulSum {K : Type} [Group K] (X : Finset K) :
    ClassFunction K ℂ →ₗ[ℂ] ℂ where
  toFun θ := ∑ x ∈ X, ∑ y ∈ X, θ (x * y)
  map_add' θ₁ θ₂ := by
    simp only [ClassFunction.add_apply, Finset.sum_add_distrib]
  map_smul' c θ := by
    simp only [ClassFunction.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

/-- A conjugacy class (as a `Finset`) is invariant under conjugation. -/
theorem classMult_conjInv {K : Type} [Group K] (X : Finset K) (x₀ : K)
    (hX : ∀ x : K, x ∈ X ↔ IsConj x x₀) :
    ∀ g x : K, x ∈ X → g * x * g⁻¹ ∈ X := by
  intro g x hx
  rw [hX, isConj_iff]
  obtain ⟨h, hh⟩ := isConj_iff.mp ((hX x).mp hx)
  exact ⟨h * g⁻¹,
    by rw [show (h * g⁻¹) * (g * x * g⁻¹) * (h * g⁻¹)⁻¹ = h * x * h⁻¹ by group, hh]⟩

/-- Any class function has constant value `φ x₀` on the conjugacy class `X ∋ x₀`, hence
`∑_{x ∈ X} φ x = |X| · φ x₀`. -/
theorem classMult_sumConjClass {K : Type} [Group K] (X : Finset K) (x₀ : K)
    (hX : ∀ x : K, x ∈ X ↔ IsConj x x₀) (φ : ClassFunction K ℂ) :
    ∑ x ∈ X, φ x = (X.card : ℂ) * φ x₀ := by
  rw [Finset.sum_congr rfl (fun x hx => ClassFunction.of_isConj φ ((hX x).mp hx))]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **The class-multiplication identity for an irreducible character `χ`**: the class sum
squared acts on `χ` like `|X|² χ(x₀)²/χ(1)`.  Immediate from `s02_classSumSquare`
(BG Lemma 2.2-a), the constancy of `χ` on the class `X`, and `χ(1) ≠ 0`. -/
theorem classMult_irr {K : Type} [Group K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    (X : Finset K) (x₀ : K) (hX : ∀ x : K, x ∈ X ↔ IsConj x x₀)
    (χ : IrreducibleCharacter K) :
    cfMulSum X (χ : ClassFunction K ℂ) =
      (X.card : ℂ) ^ 2 * ((χ : ClassFunction K ℂ) x₀ ^ 2 / (χ : ClassFunction K ℂ) 1) := by
  have hinv := classMult_conjInv X x₀ hX
  have hsq := s02_classSumSquare X hinv (χ : ClassFunction K ℂ) (Or.inl χ.isIrreducible)
  have hsum := classMult_sumConjClass X x₀ hX (χ : ClassFunction K ℂ)
  have hdeg : (χ : ClassFunction K ℂ) 1 ≠ 0 := by
    obtain ⟨d, hd, hd1⟩ := χ.isIrreducible.exists_apply_one_eq_pos_natCast
    rw [hd1]; exact_mod_cast hd.ne'
  show (∑ x ∈ X, ∑ y ∈ X, (χ : ClassFunction K ℂ) (x * y)) = _
  rw [hsum] at hsq
  rw [← mul_div_assoc, eq_div_iff hdeg]
  rw [mul_comm, hsq]
  ring

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem classMult : Work.GW2.C16.ClassMultProp := by
  intro K _ _ _ _ X x₀ hX θ
  show cfMulSum X θ = (X.card : ℂ) ^ 2 * ∑ χ : IrreducibleCharacter K,
      ClassFunction.inner θ (χ : ClassFunction K ℂ) *
        ((χ : ClassFunction K ℂ) x₀ ^ 2 / (χ : ClassFunction K ℂ) 1)
  have key : ∀ χ : IrreducibleCharacter K,
      cfMulSum X (χ : ClassFunction K ℂ) =
        (X.card : ℂ) ^ 2 * ((χ : ClassFunction K ℂ) x₀ ^ 2 / (χ : ClassFunction K ℂ) 1) :=
    fun χ => classMult_irr X x₀ hX χ
  have hexp := OddOrder.RepresentationTheory.sum_inner_irreducibleCharacter_smul θ
  calc cfMulSum X θ
      = cfMulSum X (∑ χ : IrreducibleCharacter K,
          ClassFunction.inner θ (χ : ClassFunction K ℂ) • (χ : ClassFunction K ℂ)) := by
          rw [hexp]
    _ = ∑ χ : IrreducibleCharacter K, cfMulSum X
          (ClassFunction.inner θ (χ : ClassFunction K ℂ) • (χ : ClassFunction K ℂ)) := by
          rw [map_sum]
    _ = ∑ χ : IrreducibleCharacter K,
          ClassFunction.inner θ (χ : ClassFunction K ℂ) • cfMulSum X (χ : ClassFunction K ℂ) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_); rw [map_smul]
    _ = ∑ χ : IrreducibleCharacter K, ClassFunction.inner θ (χ : ClassFunction K ℂ) *
          ((X.card : ℂ) ^ 2 * ((χ : ClassFunction K ℂ) x₀ ^ 2 / (χ : ClassFunction K ℂ) 1)) := by
          refine Finset.sum_congr rfl (fun χ _ => ?_); rw [key χ, smul_eq_mul]
    _ = (X.card : ℂ) ^ 2 * ∑ χ : IrreducibleCharacter K,
          ClassFunction.inner θ (χ : ClassFunction K ℂ) *
            ((χ : ClassFunction K ℂ) x₀ ^ 2 / (χ : ClassFunction K ℂ) 1) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun χ _ => ?_); ring

end Work.BG
