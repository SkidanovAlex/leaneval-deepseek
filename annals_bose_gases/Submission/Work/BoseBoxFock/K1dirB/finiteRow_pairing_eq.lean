import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.K1dirBDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1dirB.finiteRow_pairing_eq`

An arbitrary **finite** lattice row `∑_{n ∈ S} F n e^{i⟪κ_n, w − y⟫}` (with `κ_n = kmomInt ℓ n`)
pairs against a smooth box-supported kernel `H` as the corresponding finite lattice sum of the
pairings `hPair ℓ H n`:

    ∫_{Λ} ∫_{Λ} (∑_{n ∈ S} F n e^{i⟪κ_n, w−y⟫}) · H w y
      = ∑_{n ∈ S} F n · hPair ℓ H n ,      Λ = boxL ℓ .

This is the finite-row (Finset-indexed) companion of `K1dirB.pinQA_pairing_eq` (which handles the
concrete truncated series `pinQA v μ N c` indexed by `Lab N`) and the elementary input of the
`K1exp − K1lim` pairing bound: the `L¹Tails.kernelTail` development bounds each `hPair ℓ H n`
separately, and this identity is what lets the bound be pulled back to the box pairing of a
truncated series.

The argument is the same as in `pinQA_pairing_eq`:

* expand the finite sum and swap it out of the (iterated, box-restricted) integral — legitimate
  because each summand is continuous on the compact box `Λ × Λ`, hence integrable;
* convert the restricted box integrals into full-space ones — legitimate because `H` is supported
  in `Λ × Λ` (`hHs`), so every summand vanishes identically off the box.

The two conversions are `MeasureTheory.setIntegral_prod` (Fubini on the product measure, here in
the direction *restricted iterated ⟶ product*) and
`MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero` (support restriction), neither of
which needs an a priori integrability hypothesis in that direction beyond compactness of the box.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace Work.BoseBoxFock.K1dirB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Support restriction of a box pairing.**  If `H` is supported in `boxL ℓ × boxL ℓ`, then the
full-space iterated integral `∫_w ∫_y e^{i⟪κ, w−y⟫} H w y` equals its restriction to the box in
both variables.

No integrability is needed: for `y ∉ boxL ℓ` the integrand is identically `0` as a function of
`y`, and for `w ∉ boxL ℓ` the *inner* integral is identically `0`. -/
private lemma boxPair_eq_boxRestrict {ℓ : ℝ} (κ : E3) {H : E3 → E3 → ℂ}
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ) :
    (∫ w, ∫ y, Complex.exp (Complex.I * ((inner ℝ κ (w - y) : ℝ) : ℂ)) * H w y)
      = ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          Complex.exp (Complex.I * ((inner ℝ κ (w - y) : ℝ) : ℂ)) * H w y := by
  have hzoff : ∀ w y, y ∉ Work.BoseK15.corpusBox.boxL ℓ → H w y = 0 := by
    intro w y hy
    by_contra h
    exact hy (hHs w y h).2
  have hwoff : ∀ w, w ∉ Work.BoseK15.corpusBox.boxL ℓ → ∀ y, H w y = 0 := by
    intro w hw y
    by_contra h
    exact hw (hHs w y h).1
  have hinner : ∀ w, (∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        Complex.exp (Complex.I * ((inner ℝ κ (w - y) : ℝ) : ℂ)) * H w y)
      = (∫ y, Complex.exp (Complex.I * ((inner ℝ κ (w - y) : ℝ) : ℂ)) * H w y) := by
    intro w
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [hzoff w y hy, mul_zero])
  have houter : (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          Complex.exp (Complex.I * ((inner ℝ κ (w - y) : ℝ) : ℂ)) * H w y)
      = (∫ w, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          Complex.exp (Complex.I * ((inner ℝ κ (w - y) : ℝ) : ℂ)) * H w y) := by
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => by
      have hz : (fun y => Complex.exp (Complex.I * ((inner ℝ κ (w - y) : ℝ) : ℂ)) * H w y)
          = fun y => 0 := by
        funext y
        rw [hwoff w hw y, mul_zero]
      rw [hz, integral_zero])
  rw [houter]
  exact integral_congr_ae (Eventually.of_forall fun w => (hinner w).symm)

theorem finiteRow_pairing_eq {ℓ : ℝ} (hℓ : 0 < ℓ)
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin 3 → ℤ)) (F : (Fin 3 → ℤ) → ℂ) :
    (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          (∑ n ∈ S, F n * Complex.exp (Complex.I *
              ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) (w - y) : ℝ) : ℂ))) * H w y)
      = ∑ n ∈ S, F n * Work.BoseBoxFock.L1Tails.hPair ℓ H n := by
  classical
  have hHp : Continuous (fun p : E3 × E3 => H p.1 p.2) := hH.continuous
  have hK : IsCompact (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseK15.corpusBox.boxL_compact ℓ
  -- the whole integrand is continuous, hence integrable on the compact box squared
  have hFint : IntegrableOn
      (fun p : E3 × E3 => (∑ n ∈ S, F n * Complex.exp (Complex.I *
        ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) (p.1 - p.2) : ℝ) : ℂ))) * H p.1 p.2)
      (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hcsum : Continuous (fun p : E3 × E3 => ∑ n ∈ S, F n * Complex.exp (Complex.I *
        ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) (p.1 - p.2) : ℝ) : ℂ))) := by
      fun_prop
    exact (hcsum.mul hHp).continuousOn.integrableOn_compact (hK.prod hK)
  -- each single mode pairs to its `hPair`
  have hk : ∀ n : Fin 3 → ℤ,
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ,
        Complex.exp (Complex.I *
          ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) (z.1 - z.2) : ℝ) : ℂ)) * H z.1 z.2
        ∂(MeasureTheory.volume.prod MeasureTheory.volume))
      = Work.BoseBoxFock.L1Tails.hPair ℓ H n := by
    intro n
    have hkint : IntegrableOn
        (fun z : E3 × E3 => Complex.exp (Complex.I *
          ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) (z.1 - z.2) : ℝ) : ℂ)) * H z.1 z.2)
        (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)
        (MeasureTheory.volume.prod MeasureTheory.volume) := by
      have hcont : Continuous (fun z : E3 × E3 => Complex.exp (Complex.I *
          ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) (z.1 - z.2) : ℝ) : ℂ)) * H z.1 z.2) := by
        fun_prop
      exact hcont.continuousOn.integrableOn_compact (hK.prod hK)
    rw [MeasureTheory.setIntegral_prod _ hkint]
    change (∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        Complex.exp (Complex.I *
          ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) (w - y) : ℝ) : ℂ)) * H w y)
      = Work.BoseBoxFock.L1Tails.hPair ℓ H n
    rw [← boxPair_eq_boxRestrict (Work.BoseBoxFock.kmomInt ℓ n) hHs]
    rfl
  -- Fubini: the restricted iterated box integral is the integral over the product box
  rw [← MeasureTheory.setIntegral_prod
    (fun p : E3 × E3 => (∑ n ∈ S, F n * Complex.exp (Complex.I *
      ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) (p.1 - p.2) : ℝ) : ℂ))) * H p.1 p.2) hFint]
  -- expand the finite sum pointwise, swap it out of the integral, identify each term
  trans ∫ z in Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ,
      ∑ n ∈ S, F n * (Complex.exp (Complex.I *
        ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) (z.1 - z.2) : ℝ) : ℂ)) * H z.1 z.2)
      ∂(MeasureTheory.volume.prod MeasureTheory.volume)
  · refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  · rw [MeasureTheory.integral_finsetSum (s := S) (f := fun n (z : E3 × E3) =>
      F n * (Complex.exp (Complex.I *
        ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) (z.1 - z.2) : ℝ) : ℂ)) * H z.1 z.2)) (by
      intro n _
      have hcont : Continuous (fun z : E3 × E3 => F n * (Complex.exp (Complex.I *
          ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) (z.1 - z.2) : ℝ) : ℂ)) * H z.1 z.2)) := by
        fun_prop
      exact hcont.continuousOn.integrableOn_compact (hK.prod hK))]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MeasureTheory.integral_const_mul]
    rw [hk n]

end Work.BoseBoxFock.K1dirB
