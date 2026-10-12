import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.B13Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.G2_eq`

The two-slot fibre identity for the `y`-factor of the Cauchy--Schwarz bound of the block I/III
fibre: with
`G2 p hp A Θ c y = ∫⁻ x' : Fib1 p, ‖A (x' p.1)‖² * (c * ∫⁻ u, ‖Θ (upd2 p y u (res p x'))‖²)`,
one has `∫⁻ y, G2 p hp A Θ c y = c * (NA A * NE Θ)`.

This is the `hG2` input of `Work.BoseBoxFock.ennreal_bound`.

The proof decomposes the pair `(y, x')` of integration variables of the iterated integral into the
independent coordinates `(y, a, x'', u)`, where `a = x' p.1` is the slot-`p.1` coordinate of the
fibre configuration, `x'' = res p x'` the remaining coordinates and `u` the free slot of the `Θ`
insertion, so that `upd2 p y u x''` parametrises the full configuration.  Concretely:

* swap the `y`- and the `x'`-integrals (Tonelli; the joint integrand is a.e.-measurable from
  `hAproj` and the measurability of `Θ`);
* pull the constants `‖A (x' p.1)‖²` and `c` out of the `y`-integral;
* split the fibre `Fib1 p` at the slot `p.1` (`lintegral_fibre_p1`), which produces the outer
  `a`-integral of `NA A`;
* pull the constants out of the `x''`-integral;
* identify `∫⁻ x'' ∫⁻ y ∫⁻ u, ‖Θ (upd2 p y u x'')‖²` with `NE Θ` by the two-slot fibre
  decomposition (`lintegral_fibre_two_p`) and two Tonelli exchanges.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {n : ℕ}

/-! ## Helper measurability lemmas -/

/-- Pointwise measurability of the two-slot insertion `q ↦ upd2 p (φ q) (ψ q) (χ q)`. -/
private lemma upd2_meas_pt (p : Fin n × Fin n) {β : Type*} [MeasurableSpace β]
    {φ ψ : β → E3} {χ : β → Fib2 p} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hχ : Measurable χ) : Measurable (fun q : β => upd2 p (φ q) (ψ q) (χ q)) := by
  refine measurable_pi_iff.mpr (fun k => ?_)
  by_cases h2 : k = p.2
  · simp only [upd2, dif_pos h2]
    exact hψ
  · by_cases h1 : k = p.1
    · simp only [upd2, dif_neg h2, dif_pos h1]
      exact hφ
    · simp only [upd2, dif_neg h2, dif_neg h1]
      exact (measurable_pi_apply (⟨k, h2, h1⟩ : I2 p)).comp hχ

/-- The insertion `(q, u) ↦ upd2 p (φ q) u (χ q)` is measurable. -/
private lemma upd2_meas (p : Fin n × Fin n) {β : Type*} [MeasurableSpace β]
    {φ : β → E3} {χ : β → Fib2 p} (hφ : Measurable φ) (hχ : Measurable χ) :
    Measurable (fun q : β × E3 => upd2 p (φ q.1) q.2 (χ q.1)) :=
  upd2_meas_pt p (hφ.comp measurable_fst) measurable_snd (hχ.comp measurable_fst)

/-- Measurability of the partial integral over the free `u`-slot. -/
private lemma partial_meas (p : Fin n × Fin n)
    {T : (Fin n → E3) → ENNReal} (hT : Measurable T) {β : Type*} [MeasurableSpace β]
    {φ : β → E3} {χ : β → Fib2 p} (hφ : Measurable φ) (hχ : Measurable χ) :
    Measurable (fun q : β => ∫⁻ u : E3, T (upd2 p (φ q) u (χ q))) :=
  (hT.comp (upd2_meas p hφ hχ)).lintegral_prod_right'

/-- Measurability of the partial integral over the `x''`-slot. -/
private lemma partial_meas2 (p : Fin n × Fin n)
    {T : (Fin n → E3) → ENNReal} (hT : Measurable T) {β : Type*} [MeasurableSpace β]
    {φ ψ : β → E3} (hφ : Measurable φ) (hψ : Measurable ψ) :
    Measurable (fun q : β => ∫⁻ x'' : Fib2 p, T (upd2 p (φ q) (ψ q) x'')) :=
  (hT.comp (upd2_meas_pt p (hφ.comp measurable_fst) (hψ.comp measurable_fst)
    measurable_snd)).lintegral_prod_right'

/-! ## The main identity -/

theorem G2_eq {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {A : EuclideanSpace ℝ (Fin 3) → ℂ} {Θ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ} (c : ENNReal) (hΘm : Measurable Θ) (hAproj : AEMeasurable (fun x' : Work.BoseBoxFock.Fib1 p => A (x' ⟨p.1, hp⟩)) MeasureTheory.volume) (hc : c ≠ ⊤) (hNA : Work.BoseBoxFock.NA A ≠ ⊤) (hNE : Work.BoseBoxFock.NE Θ ≠ ⊤) : ∫⁻ y : EuclideanSpace ℝ (Fin 3), Work.BoseBoxFock.G2 p hp A Θ c y = c * (Work.BoseBoxFock.NA A * Work.BoseBoxFock.NE Θ) := by
  classical
  have hTh : Measurable (fun x : Fin n → E3 => ENNReal.ofReal (‖Θ x‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hΘm.norm.pow_const 2)
  have hfl : AEMeasurable (fun x' : Fib1 p => ENNReal.ofReal (‖A (x' ⟨p.1, hp⟩)‖ ^ 2))
      volume := ENNReal.measurable_ofReal.comp_aemeasurable (hAproj.norm.pow_const 2)
  have hresm : Measurable (fun x' : Fib1 p => res p x') := measurable_res p
  have hM4 : Measurable (fun q : Fib2 p × E3 => ∫⁻ u : E3,
      ENNReal.ofReal (‖Θ (upd2 p q.2 u q.1)‖ ^ 2)) :=
    partial_meas p hTh measurable_snd measurable_fst
  have hM1 : Measurable (fun x'' : Fib2 p => ∫⁻ y : E3, ∫⁻ u : E3,
      ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2)) := hM4.lintegral_prod_right'
  have hM3 : AEMeasurable (fun q : Fib1 p × E3 => ∫⁻ u : E3,
      ENNReal.ofReal (‖Θ (upd2 p q.2 u (res p q.1))‖ ^ 2)) (volume.prod volume) :=
    (partial_meas p hTh measurable_snd (hresm.comp measurable_fst)).aemeasurable
  -- ### Step 1: swap the `y`- and the `x'`-integral
  have step1 : (∫⁻ y : E3, ∫⁻ x' : Fib1 p, ENNReal.ofReal (‖A (x' ⟨p.1, hp⟩)‖ ^ 2)
        * (c * ∫⁻ u : E3, ENNReal.ofReal (‖Θ (upd2 p y u (res p x'))‖ ^ 2)))
      = ∫⁻ x' : Fib1 p, ∫⁻ y : E3, ENNReal.ofReal (‖A (x' ⟨p.1, hp⟩)‖ ^ 2)
        * (c * ∫⁻ u : E3, ENNReal.ofReal (‖Θ (upd2 p y u (res p x'))‖ ^ 2)) := by
    refine (lintegral_lintegral_swap (f := fun (x' : Fib1 p) (y : E3) =>
      ENNReal.ofReal (‖A (x' ⟨p.1, hp⟩)‖ ^ 2)
        * (c * ∫⁻ u : E3, ENNReal.ofReal (‖Θ (upd2 p y u (res p x'))‖ ^ 2))) ?_).symm
    exact (hfl.comp_fst).mul (aemeasurable_const.mul hM3)
  -- ### Step 2: pull the constants out of the `y`-integral
  have step2 : (∫⁻ x' : Fib1 p, ∫⁻ y : E3, ENNReal.ofReal (‖A (x' ⟨p.1, hp⟩)‖ ^ 2)
        * (c * ∫⁻ u : E3, ENNReal.ofReal (‖Θ (upd2 p y u (res p x'))‖ ^ 2)))
      = ∫⁻ x' : Fib1 p, ENNReal.ofReal (‖A (x' ⟨p.1, hp⟩)‖ ^ 2)
        * (c * ∫⁻ y : E3, ∫⁻ u : E3, ENNReal.ofReal (‖Θ (upd2 p y u (res p x'))‖ ^ 2)) := by
    refine lintegral_congr fun x' => ?_
    rw [lintegral_const_mul' (ENNReal.ofReal (‖A (x' ⟨p.1, hp⟩)‖ ^ 2))
      (fun y : E3 => c * ∫⁻ u : E3, ENNReal.ofReal (‖Θ (upd2 p y u (res p x'))‖ ^ 2))
      ENNReal.ofReal_ne_top]
    rw [lintegral_const_mul' c (fun y : E3 => ∫⁻ u : E3,
      ENNReal.ofReal (‖Θ (upd2 p y u (res p x'))‖ ^ 2)) hc]
  -- ### Step 3: the fibre decomposition of the `x'`-integral
  have step3 : (∫⁻ x' : Fib1 p, ENNReal.ofReal (‖A (x' ⟨p.1, hp⟩)‖ ^ 2)
        * (c * ∫⁻ y : E3, ∫⁻ u : E3,
            ENNReal.ofReal (‖Θ (upd2 p y u (res p x'))‖ ^ 2)))
      = ∫⁻ a : E3, ∫⁻ x'' : Fib2 p, ENNReal.ofReal (‖A a‖ ^ 2)
        * (c * ∫⁻ y : E3, ∫⁻ u : E3,
            ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2)) := by
    have hF : AEMeasurable (fun x' : Fib1 p => ENNReal.ofReal (‖A (x' ⟨p.1, hp⟩)‖ ^ 2)
        * (c * ∫⁻ y : E3, ∫⁻ u : E3,
            ENNReal.ofReal (‖Θ (upd2 p y u (res p x'))‖ ^ 2))) volume :=
      hfl.mul (aemeasurable_const.mul ((hM1.comp hresm).aemeasurable))
    rw [lintegral_fibre_p1 p hp hF]
    refine lintegral_congr fun a => lintegral_congr fun x'' => ?_
    simp only [upd1_apply_p1, res_upd1]
  -- ### Step 4: pull the constants out of the `x''`-integral
  have step4 : (∫⁻ a : E3, ∫⁻ x'' : Fib2 p, ENNReal.ofReal (‖A a‖ ^ 2)
        * (c * ∫⁻ y : E3, ∫⁻ u : E3, ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2)))
      = ∫⁻ a : E3, ENNReal.ofReal (‖A a‖ ^ 2)
        * (c * ∫⁻ x'' : Fib2 p, ∫⁻ y : E3, ∫⁻ u : E3,
            ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2)) := by
    refine lintegral_congr fun a => ?_
    rw [lintegral_const_mul' (ENNReal.ofReal (‖A a‖ ^ 2))
      (fun x'' : Fib2 p => c * ∫⁻ y : E3, ∫⁻ u : E3,
        ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2)) ENNReal.ofReal_ne_top]
    rw [lintegral_const_mul' c (fun x'' : Fib2 p => ∫⁻ y : E3, ∫⁻ u : E3,
      ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2)) hc]
  -- ### Step 5: the double fibre identity
  have step5 : (∫⁻ x'' : Fib2 p, ∫⁻ y : E3, ∫⁻ u : E3,
        ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2)) = NE Θ := by
    rw [lintegral_lintegral_swap (f := fun (x'' : Fib2 p) (y : E3) => ∫⁻ u : E3,
      ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2)) hM4.aemeasurable]
    have hinner : ∀ y : E3, (∫⁻ x'' : Fib2 p, ∫⁻ u : E3,
          ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2))
        = ∫⁻ u : E3, ∫⁻ x'' : Fib2 p, ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2) := by
      intro y
      refine lintegral_lintegral_swap (f := fun (x'' : Fib2 p) (u : E3) =>
        ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2)) ?_
      exact (hTh.comp
        (upd2_meas_pt p measurable_const measurable_snd measurable_fst)).aemeasurable
    rw [lintegral_congr hinner]
    rw [lintegral_lintegral_swap (f := fun (y : E3) (u : E3) => ∫⁻ x'' : Fib2 p,
      ENNReal.ofReal (‖Θ (upd2 p y u x'')‖ ^ 2))
      ((partial_meas2 p hTh measurable_fst measurable_snd).aemeasurable)]
    exact (lintegral_fibre_two_p p hp hTh.aemeasurable).symm
  show (∫⁻ y : E3, ∫⁻ x' : Fib1 p, ENNReal.ofReal (‖A (x' ⟨p.1, hp⟩)‖ ^ 2)
      * (c * ∫⁻ u : E3, ENNReal.ofReal (‖Θ (upd2 p y u (res p x'))‖ ^ 2)))
    = c * (NA A * NE Θ)
  rw [step1, step2, step3, step4, step5]
  rw [lintegral_mul_const' (c * NE Θ) (fun a : E3 => ENNReal.ofReal (‖A a‖ ^ 2))
    (ENNReal.mul_ne_top hc hNE)]
  rw [show (∫⁻ a : E3, ENNReal.ofReal (‖A a‖ ^ 2)) = NA A from rfl]
  exact mul_left_comm _ _ _

end Work.BoseBoxFock
