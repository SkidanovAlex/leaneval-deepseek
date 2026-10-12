import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.L1Tails.DefsC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

set_option linter.unusedVariables false

namespace Work.BoseBoxFock.L1Tails.hPairFubini

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Auxiliary lemmas for the Fubini form of `hPair`

`hPair ℓ H n = ∫_w ∫_y e^{i⟪κ_n, w−y⟫} H w y`.  The hypotheses of the target put the support of
`H` in `boxL ℓ × boxL ℓ` (a compact set) and make `H` smooth, so the joint integrand is continuous
with compact support and the two iterated integrals may be exchanged; the rest is the elementary
splitting `e^{i⟪κ,w−y⟫} = e^{−i⟪κ,y⟫}·e^{i⟪κ,w⟫}` together with
`conj (∫_w e^{−i⟪κ,w⟫} conj (H w y)) = ∫_w e^{i⟪κ,w⟫} H w y`. -/

/-- The support of `uncurry H` is contained in the two copies of the corpus box: this is exactly
the pointwise hypothesis `hHs` of the target. -/
lemma hPair_support_uncurry_subset {ℓ : ℝ} {H : E3 → E3 → ℂ}
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ) :
    Function.support (Function.uncurry H)
      ⊆ Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ := by
  intro p hp
  exact hHs p.1 p.2 hp

/-- The corpus box `boxL ℓ = ℓ • cell` is compact (it is the image of the compact unit cell under
the continuous dilation `x ↦ ℓ • x`). -/
lemma hPair_isCompact_boxL (ℓ : ℝ) : IsCompact (Work.BoseK15.corpusBox.boxL ℓ) := by
  rw [Work.BoseB4.BoxData.boxL]
  exact Work.BoseK15.corpusBox.cell_compact.image (continuous_const_smul ℓ)

/-- The joint integrand `p ↦ e^{i⟪κ,p.1−p.2⟫}H p.1 p.2` is integrable for the product Lebesgue
measure: it is continuous and its support is contained in `boxL ℓ ×ˢ boxL ℓ`. -/
lemma hPair_integrable_uncurry_phase {ℓ : ℝ} {H : E3 → E3 → ℂ} {κ : E3}
    (hHc : Continuous (Function.uncurry H))
    (hsupp : Function.support (Function.uncurry H)
      ⊆ Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) :
    Integrable (Function.uncurry
        (fun w y => Complex.exp (Complex.I * ((inner ℝ κ (w - y) : ℝ) : ℂ)) * H w y))
      ((volume : Measure E3).prod (volume : Measure E3)) := by
  have hK : IsCompact (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) :=
    (hPair_isCompact_boxL ℓ).prod (hPair_isCompact_boxL ℓ)
  have hcont : Continuous (fun p : E3 × E3 =>
      Complex.exp (Complex.I * ((inner ℝ κ (p.1 - p.2) : ℝ) : ℂ)) * H p.1 p.2) := by
    refine (Complex.continuous_exp.comp ?_).mul hHc
    refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
    exact continuous_inner.comp (continuous_const.prodMk (continuous_fst.sub continuous_snd))
  have hsupp' : Function.support (fun p : E3 × E3 =>
      Complex.exp (Complex.I * ((inner ℝ κ (p.1 - p.2) : ℝ) : ℂ)) * H p.1 p.2)
      ⊆ Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ :=
    (Function.support_mul_subset_right _ (Function.uncurry H)).trans hsupp
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact hK hsupp')

/-- Conjugation of the inner kernel: `conj (e^{−i⟪κ,w⟫} conj h) = e^{i⟪κ,w⟫}·h`. -/
lemma hPair_conj_exp (κ w : E3) (h : ℂ) :
    (starRingEnd ℂ) (Complex.exp (-(Complex.I * ((inner ℝ κ w : ℝ) : ℂ))) * (starRingEnd ℂ) h)
      = Complex.exp (Complex.I * ((inner ℝ κ w : ℝ) : ℂ)) * h := by
  have hconj : (starRingEnd ℂ) (-(Complex.I * ((inner ℝ κ w : ℝ) : ℂ)))
      = Complex.I * ((inner ℝ κ w : ℝ) : ℂ) := by
    rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hss : (starRingEnd ℂ) ((starRingEnd ℂ) h) = h := by
    simp only [starRingEnd_apply, star_star]
  rw [map_mul, ← Complex.exp_conj, hss, hconj]

/-- Splitting of the phase: `e^{−i⟪κ,y⟫}·e^{i⟪κ,w⟫} = e^{i⟪κ,w−y⟫}` (the inner product is linear
in its second argument and real, so the exponentials multiply). -/
lemma hPair_exp_add (κ w y : E3) :
    Complex.exp (-(Complex.I * ((inner ℝ κ y : ℝ) : ℂ)))
      * Complex.exp (Complex.I * ((inner ℝ κ w : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((inner ℝ κ (w - y) : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  rw [inner_sub_right, Complex.ofReal_sub]
  ring

/-- The general (`κ`-abstract) form of the Fubini identity. -/
lemma hPair_eq_integral_conjKinFT_gen {ℓ : ℝ} {H : E3 → E3 → ℂ} {κ : E3}
    (hHc : Continuous (Function.uncurry H))
    (hsupp : Function.support (Function.uncurry H)
      ⊆ Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) :
    (∫ w, ∫ y, Complex.exp (Complex.I * ((inner ℝ κ (w - y) : ℝ) : ℂ)) * H w y)
      = ∫ y, Complex.exp (-(Complex.I * ((inner ℝ κ y : ℝ) : ℂ)))
          * (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun w => (starRingEnd ℂ) (H w y)) κ) := by
  have hInt := hPair_integrable_uncurry_phase (ℓ := ℓ) (H := H) (κ := κ) hHc hsupp
  rw [MeasureTheory.integral_integral_swap hInt]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Submission.BoseGases.kinFT]
  rw [Commons.Analysis.Fourier.conj_integral]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only []
  rw [hPair_conj_exp, ← mul_assoc, hPair_exp_add]

/-- Fubini form of the lattice pairing `hPair ℓ H n = ∫_w ∫_y e^{i⟪κ_n, w-y⟫} H w y`: swap the two
integrals (the joint integrand is continuous with compact support, as `hHs` puts it in
`boxL ℓ × boxL ℓ`) and split the exponential, `e^{i⟪κ,w-y⟫} = e^{-i⟪κ,y⟫}·e^{i⟪κ,w⟫}`; the inner
integral is `conj (kinFT (fun w => conj (H w y)) κ_n)` because
`conj (∫_w e^{-i⟪κ,w⟫} conj (H w y)) = ∫_w e^{i⟪κ,w⟫} H w y` (`MeasureTheory.integral_conj`). -/
theorem hPair_eq_integral_conjKinFT {ℓ : ℝ} (hℓ : 0 < ℓ)
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (n : Fin 3 → ℤ) :
    Work.BoseBoxFock.L1Tails.hPair ℓ H n
      = ∫ y : EuclideanSpace ℝ (Fin 3),
          Complex.exp (-(Complex.I * ((inner ℝ (Work.BoseBoxFock.kappaL ℓ n) y : ℝ) : ℂ)))
            * (starRingEnd ℂ) (Submission.BoseGases.kinFT (fun w => (starRingEnd ℂ) (H w y))
                (Work.BoseBoxFock.kappaL ℓ n)) := by
  have hgen := hPair_eq_integral_conjKinFT_gen (ℓ := ℓ) (H := H)
    (κ := Work.BoseBoxFock.kappaL ℓ n) hH.continuous (hPair_support_uncurry_subset hHs)
  unfold Work.BoseBoxFock.L1Tails.hPair
  exact hgen

end Work.BoseBoxFock.L1Tails.hPairFubini
