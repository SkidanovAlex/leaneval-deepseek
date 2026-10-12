import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxD1Pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxPairIntGen.Defs` — vocabulary for the general-`𝒲` box pairing identity

The target `Work.BoseFixB1.boxPairIntGen` identifies the box pairing word
`boxA2 a volA Ac (fun x y => χ x χ y 𝒲(x−y)) Ψ` with the Fourier integral
`(2π)⁻³∫_q pairW 𝒲(q)·volA⁻¹·boxWinModeRGen a volA Ac χ Ψ q dq`.

The proof goes through the *relative-coordinate pair density* `boxPairDensSum` and the
per-momentum identity

    `boxPairDensFourier volA a A χ Ψ q = volA⁻¹ · boxWinModeRGen a volA A χ Ψ q`   (★)

whose `q`-th summand is the per-pair identity

    `∫_{A×A} χ y χ z e^{i⟪q,y−z⟫} boxPairFibreFun … i j y z = conj (volA⁻² · boxContentTerm … i j)`

(`boxContentTerm` below is the `(i,j)`-summand of the expansion of the complex box content
`∫ (boxTauAnnGenC h Ψ) · conj (boxTauDagGenC h Ψ)` at the mode `h = boxWinModeC`).

This module only contains the vocabulary and the elementary facts about it.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The `(i,j)`-summand of the expansion of the complex box content

    `∫_{abox M a} (boxTauAnnGenC h Ψ)(x) · conj ((boxTauDagGenC h Ψ)(x)) dx`

at the mode `h = boxWinModeC volA A χ q`, namely

    `∫ 1_A(x_i) 1_A(x_j) (∫_A h z · Ψ(x_{i←z}) dz) · conj (h (x_j)) · (∫_A Ψ(x_{j←w}) dw) dx`.

(`Ψ` is complex-valued so that the same definition also serves the real-cast state.) -/
noncomputable def boxContentTerm {M : ℕ} (volA a : ℝ) (A : Set E3) (χ : E3 → ℝ) (q : E3)
    (i j : Fin M) (Ψ : X M → ℂ) : ℂ :=
  ∫ x in abox M a,
    A.indicator (fun _ => (1 : ℂ)) (x i) * A.indicator (fun _ => (1 : ℂ)) (x j)
      * (∫ z in A, boxWinModeC volA A χ q z * Ψ (Function.update x i z))
      * star (boxWinModeC volA A χ q (x j))
      * (∫ z in A, Ψ (Function.update x j z))

/-- The `(i,j)`-summand of `boxPairDensFourier`: the `A×A`-integral of `χ(y)χ(z)e^{i⟪q,y−z⟫}`
against the peeled pair fibre `boxPairFibreFun`. -/
noncomputable def boxPairDensFourierTerm {N : ℕ} (volA a : ℝ) (A : Set E3) (χ : E3 → ℝ)
    (Ψ : X (N + 2) → ℝ) (i j : Fin (N + 2)) (q : E3) : ℂ :=
  ∫ y in A, ∫ z in A,
    ((χ y * χ z : ℝ) : ℂ)
      * Complex.exp (Complex.I * ((inner ℝ q (y - z) : ℝ) : ℂ))
      * ((boxPairFibreFun volA a A Ψ i j y z : ℝ) : ℂ)


/-- The slot mean of `boxPInd` (the mean without the box indicator). -/
noncomputable def boxIndMean {M : ℕ} (volA : ℝ) (A : Set E3) (i : Fin M)
    (Ψ : X M → ℝ) (x : X M) : ℝ :=
  (1 / volA) * ∫ z in A, Ψ (Function.update x i z)

/-- `P_i` is the slot mean times the box indicator. -/
theorem boxPInd_eq_mean_mul_indicator {M : ℕ} (volA : ℝ) (A : Set E3) (i : Fin M)
    (Ψ : X M → ℝ) (x : X M) :
    UBBInputs8.boxPInd volA A i Ψ x
      = boxIndMean volA A i Ψ x * A.indicator (fun _ => (1 : ℝ)) (x i) := by
  rw [UBBInputs8.boxPInd, boxIndMean]

/-- `Q_i = 1_A(x_i)·(1 - M_i)`. -/
theorem boxQInd_eq_indicator_mul_sub {M : ℕ} (volA : ℝ) (A : Set E3) (i : Fin M)
    (Ψ : X M → ℝ) (x : X M) :
    UBBInputs8.boxQInd volA A i Ψ x
      = A.indicator (fun _ => (1 : ℝ)) (x i)
          * (Ψ x - boxIndMean volA A i Ψ x) := by
  rw [UBBInputs8.boxQInd, boxPInd_eq_mean_mul_indicator]
  ring

/-- The `(i,j)`-summand of the *unpeeled* pairing word (the `abox`-integral form). -/
noncomputable def unpeeledPairTerm {M : ℕ} (volA : ℝ) (a : ℝ) (A : Set E3)
    (χ : E3 → ℝ) (Ψ : X M → ℝ) (i j : Fin M) (q : E3) : ℂ :=
  ∫ x in abox M a,
    ((χ (x i) * χ (x j) : ℝ) : ℂ)
      * Complex.exp (Complex.I * ((inner ℝ q (x i - x j) : ℝ) : ℂ))
      * (((UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Ψ) x)
          * (UBBInputs8.boxQInd volA A j (UBBInputs8.boxQInd volA A i Ψ) x) : ℝ) : ℂ)

/-- The complex box mode is mean-free over `A` (the defining property of the `Q_A`-projected
windowed exponential). -/
theorem boxWinModeC_integral_zero {volA : ℝ} {A : Set E3} {χ : E3 → ℝ}
    (hA : MeasurableSet A) (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ A → χ z = 0)
    (hvol : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA) (q : E3) :
    ∫ z in A, boxWinModeC volA A χ q z = 0 := by
  set g : E3 → ℂ := fun z => (χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ q z : ℝ) : ℂ)))
    with hg
  set d : ℂ := ((volA⁻¹ : ℝ) : ℂ) * ∫ w in A, (fun z : E3 => (χ z : ℂ) *
    Complex.exp (-(Complex.I * ((inner ℝ q z : ℝ) : ℂ)))) w with hd
  have hpt : ∀ z : E3, boxWinModeC volA A χ q z
      = A.indicator (fun _ => (1 : ℂ)) z * (g z - d) := fun z => rfl
  rw [show (∫ z in A, boxWinModeC volA A χ q z)
      = ∫ z in A, A.indicator (fun _ => (1 : ℂ)) z * (g z - d) from
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [show (∫ z in A, A.indicator (fun _ => (1 : ℂ)) z * (g z - d))
      = ∫ z in A, (g z - d) from
    setIntegral_congr_fun hA (fun z hz => by rw [Set.indicator_of_mem hz, one_mul])]
  have hfin : (MeasureTheory.volume A) ≠ ⊤ := by
    intro h
    rw [h, ENNReal.toReal_top] at hvol
    linarith [hvolpos]
  have hgc : Continuous g :=
    (Complex.continuous_ofReal.comp hχc).mul (Complex.continuous_exp.comp (by fun_prop))
  have hgs : HasCompactSupport g :=
    (hχs.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)).mul_right
      (f' := fun z : E3 => Complex.exp (-(Complex.I * ((inner ℝ q z : ℝ) : ℂ))))
  have hgint : Integrable g volume := hgc.integrable_of_hasCompactSupport hgs
  have hdint : Integrable (fun _ : E3 => d) (MeasureTheory.volume.restrict A) :=
    MeasureTheory.integrableOn_const
  have hsub : (∫ z in A, (g z - d))
      = (∫ z in A, g z) - (∫ z in A, (fun _ : E3 => d) z) :=
    MeasureTheory.integral_sub (hgint.integrableOn) hdint
  rw [hsub]
  have hconstint : (∫ z in A, (fun _ : E3 => d) z)
      = ((MeasureTheory.volume A).toReal : ℂ) * d := by
    rw [MeasureTheory.setIntegral_const]
    exact Complex.real_smul
  rw [hconstint, ← hvol]
  have hswap : (volA : ℂ) * d = ∫ w in A, g w := by
    rw [hd]
    rw [show (volA : ℂ) * (((volA⁻¹ : ℝ) : ℂ) * (∫ w in A, (fun z : E3 => (χ z : ℂ) *
          Complex.exp (-(Complex.I * ((inner ℝ q z : ℝ) : ℂ)))) w))
        = (((volA : ℝ) : ℂ) * ((volA⁻¹ : ℝ) : ℂ)) * (∫ w in A, (fun z : E3 => (χ z : ℂ) *
          Complex.exp (-(Complex.I * ((inner ℝ q z : ℝ) : ℂ)))) w) from by ring]
    rw [show (((volA : ℝ) : ℂ) * ((volA⁻¹ : ℝ) : ℂ)) = (1 : ℂ) from by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hvolpos), Complex.ofReal_one]]
    rw [one_mul]
  rw [hswap]
  rw [show (∫ z in A, g z) = ∫ z, g z from
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [hg]
      simp only
      rw [hχsupp z hz]
      simp)]
  ring

end Work.BoseFixB1
