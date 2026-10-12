import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.e0_prop_theta
import Submission.Work.BoseDict.Defs3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotCountsComplex` — the **complex** sector counts of the box ↔ model bridge

The BF3b rows of `Submission/Work/BoseBoxFock/BF3B_PLAN_S6.md` §4 are identities of the shape

    `bomb m Ψ (n0 Ψ) = cS1 ℓ Θ`,      `bomb m Ψ ((a0†)²(a0)² Ψ) = cS2 ℓ Θ`,
    `bomb m Ψ (nExc Ψ) = cnPlus ℓ Θ`,

where `Θ = boxRealise e d Ψ` is a **complex**-valued box function
(`Work.BoseDict.boxRealise : RealFock m →ₗ[ℝ] (Xn d → ℂ)`), while the corpus's counts
`Submission.BoseGases.cS1`/`cS2`/`cnPlus` (`Submission/CentredSector.lean`) are stated for
**real** box states.  The plan's shorthand `cS1 ℓ Θ` is therefore a coercion that had never
been fixed (see `FINDING_boxToModel_audit.md` §4), and every child asked to prove a row would
otherwise have had to invent one.

This module fixes the coercion once, by defining the complex counts with the *same* slot-mean
formula as the real ones (not by a real/imaginary decomposition), and proving

* `aPC_ofReal` — on a real state the complex slot mean *is* `aP` (`ℂ`-cast), with no
  integrability hypothesis (the Bochner integral of a cast real function is the cast);
* `cS1C_ofReal`, `cnPlusC_ofReal`, `cS2C_ofReal` — on real states the complex counts **are**
  the corpus's counts, again with no integrability hypothesis (the two integrands agree
  identically, so `integral_congr_ae` suffices): a consumer may freely use `cS1C ℓ Φ` for a
  real `Φ`, or `cS1 ℓ Φ`;
* `aPC_re`, `aPC_im`, `sq_norm_aPC`, `sq_norm_aQC` — the real/imaginary parts of the complex
  slot mean are the real slot means of the real/imaginary parts of the state (here the
  Bochner-integral linearity `integral_re`/`integral_im` *is* used, so the integrability of the
  slot integrand is carried as an explicit hypothesis);
* `cS1C_split`, `cnPlusC_split` — the counts split **additively** over the real/imaginary
  parts, which is what allows a row proved with the *real* projection algebra
  (`Submission.BoseGases.aP_sym_box`, `aP_idem`, `aQ_ortho_box`, `aP_sq_le`, …) to be
  transferred to the complex state `Θ`;
* `cS1C_nonneg`, `cnPlusC_nonneg`, `cS2C_nonneg`.

Everything is `sorry`-free; the analytic inputs are `integral_complex_ofReal`, `integral_re`,
`integral_im`, `MeasureTheory.integral_add`, `MeasureTheory.integral_const_mul` and
`integral_congr_ae`.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. Two elementary Bochner-integral facts on the one-particle space -/

/-- The real part of a `ℂ`-valued Bochner integral is the integral of the real part. -/
theorem setIntegral_re_complex (s : Set (EuclideanSpace ℝ (Fin 3))) (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hf : IntegrableOn f s) : (∫ y in s, f y).re = ∫ y in s, (f y).re := by
  have h := integral_re (𝕜 := ℂ) (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict s)
    (f := f) hf
  simpa using h.symm

/-- The imaginary part of a `ℂ`-valued Bochner integral is the integral of the imaginary
part. -/
theorem setIntegral_im_complex (s : Set (EuclideanSpace ℝ (Fin 3))) (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hf : IntegrableOn f s) : (∫ y in s, f y).im = ∫ y in s, (f y).im := by
  have h := integral_im (𝕜 := ℂ) (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict s)
    (f := f) hf
  simpa using h.symm

/-! ## 1. The definitions -/

/-- The **complex slot mean**: the `ℂ`-linear extension of `Submission.BoseGases.aP` to
complex-valued box states, `aPC ℓ i Ψ x = ℓ⁻³ ∫_{acube ℓ} Ψ (x[i ↦ y]) dy`. -/
noncomputable def aPC (ℓ : ℝ) {N : ℕ} (i : Fin N) (Ψ : Submission.BoseGases.X N → ℂ)
    (x : Submission.BoseGases.X N) : ℂ :=
  ((1 / ℓ ^ 3 : ℝ) : ℂ) *
    ∫ y in Submission.BoseGases.acube ℓ, Ψ (Function.update x i y)

/-- The complementary ("excited") slot of a complex box state: `Ψ − aPC ℓ i Ψ`, the
`ℂ`-linear extension of `Submission.BoseGases.aQ`. -/
noncomputable def aQC (ℓ : ℝ) {N : ℕ} (i : Fin N) (Ψ : Submission.BoseGases.X N → ℂ) :
    Submission.BoseGases.X N → ℂ :=
  fun x => Ψ x - aPC ℓ i Ψ x

/-- The **complex condensate count** `S₁`: the `ℂ`-analogue of `Submission.BoseGases.cS1`. -/
noncomputable def cS1C (ℓ : ℝ) {N : ℕ} (Ψ : Submission.BoseGases.X N → ℂ) : ℝ :=
  ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, ‖aPC ℓ i Ψ x‖ ^ 2

/-- The **complex excited count** `n₊`: the `ℂ`-analogue of `Submission.BoseGases.cnPlus`. -/
noncomputable def cnPlusC (ℓ : ℝ) {N : ℕ} (Ψ : Submission.BoseGases.X N → ℂ) : ℝ :=
  ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, ‖aQC ℓ i Ψ x‖ ^ 2

/-- The **complex pair-condensate count** `S₂`: the `ℂ`-analogue of
`Submission.BoseGases.cS2`. -/
noncomputable def cS2C (ℓ : ℝ) {N : ℕ} (Ψ : Submission.BoseGases.X N → ℂ) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet N,
    ∫ x in Submission.BoseGases.abox N ℓ, ‖aPC ℓ p.1 (aPC ℓ p.2 Ψ) x‖ ^ 2

/-! ## 2. The complex slot mean: linearity, and real/imaginary parts -/

/-- `‖z‖² = z.re² + z.im²` for a complex number. -/
theorem sq_norm_eq_re_sq_add_im_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  have h := Complex.sq_norm_sub_sq_re z
  linarith

/-- The real part of a cast real number is the number itself. -/
@[simp] theorem ofReal_re_cast (r : ℝ) : ((r : ℂ)).re = r := Complex.ofReal_re r

/-- The imaginary part of a cast real number vanishes. -/
@[simp] theorem ofReal_im_cast (r : ℝ) : ((r : ℂ)).im = 0 := Complex.ofReal_im r

/-- **The complex slot mean of a real state is the real slot mean** (`ℂ`-cast): `aP` is the
real counterpart of `aPC`.  No integrability is needed. -/
theorem aPC_ofReal (ℓ : ℝ) {N : ℕ} (i : Fin N) (Φ : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) :
    aPC ℓ i (fun y => ((Φ y : ℝ) : ℂ)) x = ((Submission.BoseGases.aP ℓ i Φ x : ℝ) : ℂ) := by
  unfold aPC Submission.BoseGases.aP
  rw [integral_complex_ofReal, ← Complex.ofReal_mul]

/-- `aPC` is addititive in the state. -/
theorem aPC_add (ℓ : ℝ) {N : ℕ} (i : Fin N) (Ψ Φ : Submission.BoseGases.X N → ℂ)
    (x : Submission.BoseGases.X N)
    (hΨ : IntegrableOn (fun y => Ψ (Function.update x i y)) (Submission.BoseGases.acube ℓ))
    (hΦ : IntegrableOn (fun y => Φ (Function.update x i y)) (Submission.BoseGases.acube ℓ)) :
    aPC ℓ i (fun y => Ψ y + Φ y) x = aPC ℓ i Ψ x + aPC ℓ i Φ x := by
  unfold aPC
  rw [MeasureTheory.integral_add hΨ hΦ]
  ring

/-- `aPC` is `ℝ`-homogeneous in the state. -/
theorem aPC_mul_ofReal (ℓ : ℝ) {N : ℕ} (i : Fin N) (c : ℝ) (Ψ : Submission.BoseGases.X N → ℂ)
    (x : Submission.BoseGases.X N) :
    aPC ℓ i (fun y => (c : ℂ) * Ψ y) x = (c : ℂ) * aPC ℓ i Ψ x := by
  unfold aPC
  rw [MeasureTheory.integral_const_mul]
  ring

/-- **The real part of the complex slot mean is the real slot mean of the real part.** -/
theorem aPC_re (ℓ : ℝ) {N : ℕ} (i : Fin N) (Ψ : Submission.BoseGases.X N → ℂ)
    (x : Submission.BoseGases.X N)
    (h : IntegrableOn (fun y => Ψ (Function.update x i y)) (Submission.BoseGases.acube ℓ)) :
    (aPC ℓ i Ψ x).re = Submission.BoseGases.aP ℓ i (fun y => (Ψ y).re) x := by
  unfold aPC Submission.BoseGases.aP
  rw [Complex.re_ofReal_mul, setIntegral_re_complex (Submission.BoseGases.acube ℓ) _ h]

/-- **The imaginary part of the complex slot mean is the real slot mean of the imaginary
part.** -/
theorem aPC_im (ℓ : ℝ) {N : ℕ} (i : Fin N) (Ψ : Submission.BoseGases.X N → ℂ)
    (x : Submission.BoseGases.X N)
    (h : IntegrableOn (fun y => Ψ (Function.update x i y)) (Submission.BoseGases.acube ℓ)) :
    (aPC ℓ i Ψ x).im = Submission.BoseGases.aP ℓ i (fun y => (Ψ y).im) x := by
  unfold aPC Submission.BoseGases.aP
  rw [Complex.im_ofReal_mul, setIntegral_im_complex (Submission.BoseGases.acube ℓ) _ h]

/-- The complex slot mean of a cast real function is the cast of the real slot mean. -/
theorem aPC_ofReal_re (ℓ : ℝ) {N : ℕ} (i : Fin N) (Φ : Submission.BoseGases.X N → ℝ) :
    aPC ℓ i (fun y => ((Φ y : ℝ) : ℂ))
      = fun x => ((Submission.BoseGases.aP ℓ i Φ x : ℝ) : ℂ) := by
  funext x
  exact aPC_ofReal ℓ i Φ x

/-- The complex slot mean of the state is the cast of the slot mean of its real part plus
`I` times the cast of the slot mean of its imaginary part. -/
theorem aPC_eq_re_add_im (ℓ : ℝ) {N : ℕ} (i : Fin N) (Ψ : Submission.BoseGases.X N → ℂ) :
    aPC ℓ i Ψ = fun x => (((aPC ℓ i Ψ x).re : ℝ) : ℂ)
        + Complex.I * (((aPC ℓ i Ψ x).im : ℝ) : ℂ) := by
  funext x
  exact (by
    rw [mul_comm]
    exact (Complex.re_add_im (aPC ℓ i Ψ x)).symm)

/-- **The squared modulus of the complex slot mean** in terms of the two real slot means. -/
theorem sq_norm_aPC (ℓ : ℝ) {N : ℕ} (i : Fin N) (Ψ : Submission.BoseGases.X N → ℂ)
    (x : Submission.BoseGases.X N)
    (h : IntegrableOn (fun y => Ψ (Function.update x i y)) (Submission.BoseGases.acube ℓ)) :
    ‖aPC ℓ i Ψ x‖ ^ 2
      = (Submission.BoseGases.aP ℓ i (fun y => (Ψ y).re) x) ^ 2
        + (Submission.BoseGases.aP ℓ i (fun y => (Ψ y).im) x) ^ 2 := by
  rw [sq_norm_eq_re_sq_add_im_sq, aPC_re ℓ i Ψ x h, aPC_im ℓ i Ψ x h]

/-! ## 3. The complementary slot `aQC` -/

theorem aQC_apply (ℓ : ℝ) {N : ℕ} (i : Fin N) (Ψ : Submission.BoseGases.X N → ℂ)
    (x : Submission.BoseGases.X N) : aQC ℓ i Ψ x = Ψ x - aPC ℓ i Ψ x := rfl

/-- `aQC` is the `ℂ`-lift of `aQ`: on a real state the complementary slot is the corpus's. -/
theorem aQC_ofReal (ℓ : ℝ) {N : ℕ} (i : Fin N) (Φ : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) :
    aQC ℓ i (fun y => ((Φ y : ℝ) : ℂ)) x
      = ((Submission.BoseGases.aQ ℓ i Φ x : ℝ) : ℂ) := by
  unfold aQC Submission.BoseGases.aQ
  rw [aPC_ofReal]
  push_cast
  ring

/-- The real part of the complementary slot is the complementary slot of the real part. -/
theorem aQC_re (ℓ : ℝ) {N : ℕ} (i : Fin N) (Ψ : Submission.BoseGases.X N → ℂ)
    (x : Submission.BoseGases.X N)
    (h : IntegrableOn (fun y => Ψ (Function.update x i y)) (Submission.BoseGases.acube ℓ)) :
    (aQC ℓ i Ψ x).re = Submission.BoseGases.aQ ℓ i (fun y => (Ψ y).re) x := by
  unfold aQC Submission.BoseGases.aQ
  rw [Complex.sub_re, aPC_re ℓ i Ψ x h]

/-- The imaginary part of the complementary slot is the complementary slot of the imaginary
part. -/
theorem aQC_im (ℓ : ℝ) {N : ℕ} (i : Fin N) (Ψ : Submission.BoseGases.X N → ℂ)
    (x : Submission.BoseGases.X N)
    (h : IntegrableOn (fun y => Ψ (Function.update x i y)) (Submission.BoseGases.acube ℓ)) :
    (aQC ℓ i Ψ x).im = Submission.BoseGases.aQ ℓ i (fun y => (Ψ y).im) x := by
  unfold aQC Submission.BoseGases.aQ
  rw [Complex.sub_im, aPC_im ℓ i Ψ x h]

/-- **The squared modulus of the complementary slot** in terms of the two real
complementary slots. -/
theorem sq_norm_aQC (ℓ : ℝ) {N : ℕ} (i : Fin N) (Ψ : Submission.BoseGases.X N → ℂ)
    (x : Submission.BoseGases.X N)
    (h : IntegrableOn (fun y => Ψ (Function.update x i y)) (Submission.BoseGases.acube ℓ)) :
    ‖aQC ℓ i Ψ x‖ ^ 2
      = (Submission.BoseGases.aQ ℓ i (fun y => (Ψ y).re) x) ^ 2
        + (Submission.BoseGases.aQ ℓ i (fun y => (Ψ y).im) x) ^ 2 := by
  rw [sq_norm_eq_re_sq_add_im_sq, aQC_re ℓ i Ψ x h, aQC_im ℓ i Ψ x h]

/-! ## 4. The complex counts are the corpus's counts on real states

(Each proof is a pointwise identity followed by `integral_congr_ae`, so **no** integrability
hypothesis is needed.) -/

/-- **The complex condensate count is `cS1` on real states.** -/
theorem cS1C_ofReal (ℓ : ℝ) {N : ℕ} (Φ : Submission.BoseGases.X N → ℝ) :
    cS1C ℓ (fun y => ((Φ y : ℝ) : ℂ)) = Submission.BoseGases.cS1 ℓ Φ := by
  unfold cS1C Submission.BoseGases.cS1
  refine Finset.sum_congr rfl fun i _ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [aPC_ofReal, sq_norm_eq_re_sq_add_im_sq, ofReal_re_cast, ofReal_im_cast]
  ring

/-- **The complex excited count is `cnPlus` on real states.** -/
theorem cnPlusC_ofReal (ℓ : ℝ) {N : ℕ} (Φ : Submission.BoseGases.X N → ℝ) :
    cnPlusC ℓ (fun y => ((Φ y : ℝ) : ℂ)) = Submission.BoseGases.cnPlus ℓ Φ := by
  unfold cnPlusC Submission.BoseGases.cnPlus
  refine Finset.sum_congr rfl fun i _ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [aQC_ofReal, sq_norm_eq_re_sq_add_im_sq, ofReal_re_cast, ofReal_im_cast]
  ring

/-- **The complex pair-condensate count is `cS2` on real states.** -/
theorem cS2C_ofReal (ℓ : ℝ) {N : ℕ} (Φ : Submission.BoseGases.X N → ℝ) :
    cS2C ℓ (fun y => ((Φ y : ℝ) : ℂ)) = Submission.BoseGases.cS2 ℓ Φ := by
  unfold cS2C Submission.BoseGases.cS2
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp2 : aPC ℓ p.2 (fun y => ((Φ y : ℝ) : ℂ))
      = fun x => ((Submission.BoseGases.aP ℓ p.2 Φ x : ℝ) : ℂ) :=
    aPC_ofReal_re ℓ p.2 Φ
  rw [hp2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [aPC_ofReal, sq_norm_eq_re_sq_add_im_sq, ofReal_re_cast, ofReal_im_cast]
  ring

/-! ## 5. The counts split over the real/imaginary parts -/

/-- **The complex condensate count splits additively over the real/imaginary parts.** -/
theorem cS1C_split (ℓ : ℝ) {N : ℕ} (Ψ : Submission.BoseGases.X N → ℂ)
    (hre : ∀ i : Fin N, IntegrableOn
      (fun x => (Submission.BoseGases.aP ℓ i (fun y => (Ψ y).re) x) ^ 2)
      (Submission.BoseGases.abox N ℓ))
    (him : ∀ i : Fin N, IntegrableOn
      (fun x => (Submission.BoseGases.aP ℓ i (fun y => (Ψ y).im) x) ^ 2)
      (Submission.BoseGases.abox N ℓ))
    (hpt : ∀ (i : Fin N) (x : Submission.BoseGases.X N),
      IntegrableOn (fun y => Ψ (Function.update x i y)) (Submission.BoseGases.acube ℓ)) :
    cS1C ℓ Ψ = cS1C ℓ (fun y => (((Ψ y).re : ℝ) : ℂ))
      + cS1C ℓ (fun y => (((Ψ y).im : ℝ) : ℂ)) := by
  unfold cS1C
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (∫ x in Submission.BoseGases.abox N ℓ, ‖aPC ℓ i Ψ x‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          ((Submission.BoseGases.aP ℓ i (fun y => (Ψ y).re) x) ^ 2
            + (Submission.BoseGases.aP ℓ i (fun y => (Ψ y).im) x) ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact sq_norm_aPC ℓ i Ψ x (hpt i x)
  have h2 : (∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ i (fun y => (Ψ y).re) x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          ‖aPC ℓ i (fun y => (((Ψ y).re : ℝ) : ℂ)) x‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [aPC_ofReal, sq_norm_eq_re_sq_add_im_sq, ofReal_re_cast, ofReal_im_cast]
    ring
  have h3 : (∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ i (fun y => (Ψ y).im) x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          ‖aPC ℓ i (fun y => (((Ψ y).im : ℝ) : ℂ)) x‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [aPC_ofReal, sq_norm_eq_re_sq_add_im_sq, ofReal_re_cast, ofReal_im_cast]
    ring
  rw [h1, MeasureTheory.integral_add (hre i) (him i), h2, h3]

/-- **The complex excited count splits additively over the real/imaginary parts.** -/
theorem cnPlusC_split (ℓ : ℝ) {N : ℕ} (Ψ : Submission.BoseGases.X N → ℂ)
    (hre : ∀ i : Fin N, IntegrableOn
      (fun x => (Submission.BoseGases.aQ ℓ i (fun y => (Ψ y).re) x) ^ 2)
      (Submission.BoseGases.abox N ℓ))
    (him : ∀ i : Fin N, IntegrableOn
      (fun x => (Submission.BoseGases.aQ ℓ i (fun y => (Ψ y).im) x) ^ 2)
      (Submission.BoseGases.abox N ℓ))
    (hpt : ∀ (i : Fin N) (x : Submission.BoseGases.X N),
      IntegrableOn (fun y => Ψ (Function.update x i y)) (Submission.BoseGases.acube ℓ)) :
    cnPlusC ℓ Ψ = cnPlusC ℓ (fun y => (((Ψ y).re : ℝ) : ℂ))
      + cnPlusC ℓ (fun y => (((Ψ y).im : ℝ) : ℂ)) := by
  unfold cnPlusC
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (∫ x in Submission.BoseGases.abox N ℓ, ‖aQC ℓ i Ψ x‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          ((Submission.BoseGases.aQ ℓ i (fun y => (Ψ y).re) x) ^ 2
            + (Submission.BoseGases.aQ ℓ i (fun y => (Ψ y).im) x) ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact sq_norm_aQC ℓ i Ψ x (hpt i x)
  have h2 : (∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aQ ℓ i (fun y => (Ψ y).re) x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          ‖aQC ℓ i (fun y => (((Ψ y).re : ℝ) : ℂ)) x‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [aQC_ofReal, sq_norm_eq_re_sq_add_im_sq, ofReal_re_cast, ofReal_im_cast]
    ring
  have h3 : (∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aQ ℓ i (fun y => (Ψ y).im) x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          ‖aQC ℓ i (fun y => (((Ψ y).im : ℝ) : ℂ)) x‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [aQC_ofReal, sq_norm_eq_re_sq_add_im_sq, ofReal_re_cast, ofReal_im_cast]
    ring
  rw [h1, MeasureTheory.integral_add (hre i) (him i), h2, h3]

/-! ## 6. Nonnegativity -/

theorem cS1C_nonneg (ℓ : ℝ) {N : ℕ} (Ψ : Submission.BoseGases.X N → ℂ) : 0 ≤ cS1C ℓ Ψ := by
  unfold cS1C
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _

theorem cnPlusC_nonneg (ℓ : ℝ) {N : ℕ} (Ψ : Submission.BoseGases.X N → ℂ) : 0 ≤ cnPlusC ℓ Ψ := by
  unfold cnPlusC
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _

theorem cS2C_nonneg (ℓ : ℝ) {N : ℕ} (Ψ : Submission.BoseGases.X N → ℂ) : 0 ≤ cS2C ℓ Ψ := by
  unfold cS2C
  exact Finset.sum_nonneg fun p _ => integral_nonneg fun x => sq_nonneg _

end Work.BoseBoxFock
