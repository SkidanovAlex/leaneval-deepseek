/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The `L²` bound for `∂ (bmPotential ψ)` for *continuous* compactly supported data

`Work.NN.Core.czB_L2_bounded` controls `‖∂ (bmPotential ψ)‖_{L²}` by `‖ψ‖_{L²}` when `ψ` is `C¹`
with compact support.  Here `ψ` is only assumed *continuous* with compact support, but the
potential `u = bmPotential ψ` is assumed to be `C¹`; the same `L²` bound holds.

The argument is a duality computation.  For a compactly supported `C¹` test field `φ` one has,
by integration by parts for `∂` (`Work.NN.Core.ibp_dCoord`) followed by Fubini and the oddness of
the Bochner–Martinelli kernel (`Work.NN.Core.czB_C0_pairing`),

  `Σ_i ∫ z, ∂_i u z * star (φ_i z) = Σ_l ∫ w, ψ_l w * czV φ w l`

where `czV φ w l = ∫ ζ, bmKernel l (ζ - w) * star (Σ_i ∂̄_i φ_i ζ)` is the adjoint field
(`Work.NN.Core.czB_C0_defs`).  The adjoint is a sum of `∂`-derivatives of potentials of `C¹`
compactly supported data (`Work.NN.Core.czV_eq_sum_dCoord`), so the `C¹` case bound gives
`‖czV φ‖_{L²} ≤ C‖φ‖_{L²}` (`Work.NN.Core.czV_L2_bound`), and Cauchy–Schwarz gives

  `|Σ_i ∫ z, ∂_i u z * star (φ_i z)| ≤ C ‖ψ‖_{L²} ‖φ‖_{L²}`.

Choosing the test field `φ_i` to be a mollified version of `χ · ∂_i u` (a smooth radial cutoff
`χ = cutC R`, mollification by `Work.NN.Core.exists_contDiff_uniform_approx_continuous`), and
letting the mollification parameter tend to `0`, yields
`Σ_i ∫ z, |χ z|² ‖∂_i u z‖² ≤ C² ‖ψ‖_{L²}²`; letting `R → ∞` gives the claim.
-/
import Mathlib
import Submission.Work.NN.Core.czB_L2_bounded
import Submission.Work.NN.Core.czbL2_bound_of_smooth
import Submission.Work.NN.Core.bmPotential_dCoord_eq
import Submission.Work.NN.Core.czB_C0_defs
import Submission.Work.NN.Core.czB_C0_pairing
import Submission.Work.NN.Core.czV_eq_sum_dCoord
import Submission.Work.NN.Core.czV_L2_bound
import Submission.Work.NN.Core.exists_contDiff_uniform_approx_continuous

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace Work.NN.Core

open Work.CR.Flat.Cauchy

variable {n : ℕ}

/-! ## The energy of a family and its description as a lower integral -/

/-- The `L²`-energy `∑ j ∫ z, ‖f j z‖²` of a family `f`. -/
def czEnergy (f : Fin n → (Fin n → ℂ) → ℂ) : ℝ := ∑ j, ∫ z, ‖f j z‖ ^ 2

lemma czEnergy_nonneg (f : Fin n → (Fin n → ℂ) → ℂ) : 0 ≤ czEnergy f :=
  Finset.sum_nonneg fun j _ => integral_nonneg fun z => by positivity

/-- The pointwise identity `∑ j ofReal ‖f j z‖² = ofReal (∑ j ‖f j z‖²)`. -/
lemma sum_ofReal_normSq (f : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    ∑ j, ENNReal.ofReal (‖f j z‖ ^ 2) = ENNReal.ofReal (∑ j, ‖f j z‖ ^ 2) :=
  (ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity).symm

lemma continuous_normSq (f : (Fin n → ℂ) → ℂ) (hf : Continuous f) :
    Continuous (fun z => ‖f z‖ ^ 2) := hf.norm.pow 2

/-- Integrability of `‖f‖²` for continuous compactly supported `f`. -/
lemma integrable_normSq (f : (Fin n → ℂ) → ℂ) (hf : Continuous f)
    (hcs : HasCompactSupport f) : Integrable (fun z => ‖f z‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp
    (hf.memLp_of_hasCompactSupport hcs)

/-- The lower integral of `∑ j ofReal ‖f j‖²` is `ofReal` of the energy. -/
lemma lintegral_sum_ofReal_normSq (f : Fin n → (Fin n → ℂ) → ℂ)
    (hcont : ∀ j, Continuous (f j)) (hcs : ∀ j, HasCompactSupport (f j)) :
    (∫⁻ z : Fin n → ℂ, ∑ j, ENNReal.ofReal (‖f j z‖ ^ 2))
      = ENNReal.ofReal (czEnergy f) := by
  rw [lintegral_finsetSum (s := Finset.univ)
    (f := fun (j : Fin n) (z : Fin n → ℂ) => ENNReal.ofReal (‖f j z‖ ^ 2)) (fun j _ =>
    ENNReal.measurable_ofReal.comp ((continuous_normSq (f j) (hcont j)).measurable))]
  have hsum : (∑ j : Fin n, ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (‖f j z‖ ^ 2))
      = ∑ j : Fin n, ENNReal.ofReal (∫ z : Fin n → ℂ, ‖f j z‖ ^ 2) :=
    Finset.sum_congr rfl fun j _ =>
      (ofReal_integral_eq_lintegral_ofReal (integrable_normSq (f j) (hcont j) (hcs j))
        (Eventually.of_forall fun z => by positivity)).symm
  rw [hsum, ← ENNReal.ofReal_sum_of_nonneg
    (fun j _ => integral_nonneg fun z => by positivity)]
  rfl

/-! ## Continuity of the adjoint field -/

lemma contDiff_starComp {φ : (Fin n → ℂ) → ℂ} (hφ : ContDiff ℝ 1 φ) :
    ContDiff ℝ 1 (fun w => star (φ w)) :=
  Complex.conjCLE.contDiff.comp hφ

/-- `czV φ · l` is continuous for `C¹` compactly supported data. -/
lemma continuous_czV (hn : 0 < n) {φ : Fin n → (Fin n → ℂ) → ℂ}
    (hφ : ∀ i, ContDiff ℝ 1 (φ i)) (hφc : ∀ i, HasCompactSupport (φ i)) (l : Fin n) :
    Continuous (fun z => czV φ z l) := by
  have hfun : (fun z => czV φ z l) = fun z => ∑ i, Work.CR.Flat.dCoord i
      (bmPotential (singleFam l (fun w => star (φ i w)))) z := by
    funext z
    exact czV_eq_sum_dCoord hn hφ hφc z l
  rw [hfun]
  refine continuous_finsetSum _ fun i _ => continuous_dCoord i ?_
  exact contDiff_one_bmPotential hn (contDiff_singleFam (contDiff_starComp (hφ i)))
    (hasCompactSupport_singleFam (hasCompactSupport_star_comp (hφc i)))

/-! ## The `L²` bound for the adjoint field, in real form -/

/-- The lower-integral bound `czV_L2_bound` rewritten with real integrals. -/
lemma czV_energy_bound (hn : 0 < n) {C_V : ℝ}
    (hVb : ∀ (φ : Fin n → (Fin n → ℂ) → ℂ), (∀ i, ContDiff ℝ 1 (φ i)) →
      (∀ i, HasCompactSupport (φ i)) →
      (∫⁻ z : Fin n → ℂ, ∑ l : Fin n, ENNReal.ofReal (‖czV φ z l‖ ^ 2))
        ≤ ENNReal.ofReal (C_V ^ 2) *
          ∫⁻ z : Fin n → ℂ, ∑ i : Fin n, ENNReal.ofReal (‖φ i z‖ ^ 2))
    (φ : Fin n → (Fin n → ℂ) → ℂ) (hφ : ∀ i, ContDiff ℝ 1 (φ i))
    (hφc : ∀ i, HasCompactSupport (φ i)) :
    ∑ l, ∫ z, ‖czV φ z l‖ ^ 2 ≤ C_V ^ 2 * czEnergy φ := by
  have hcont : ∀ l, Continuous (fun z => czV φ z l) := fun l => continuous_czV hn hφ hφc l
  have hR : (∫⁻ z : Fin n → ℂ, ∑ i : Fin n, ENNReal.ofReal (‖φ i z‖ ^ 2))
      = ENNReal.ofReal (czEnergy φ) :=
    lintegral_sum_ofReal_normSq φ (fun i => (hφ i).continuous) hφc
  have hVb' := hVb φ hφ hφc
  rw [hR] at hVb'
  have hC2 : (0 : ℝ) ≤ C_V ^ 2 := sq_nonneg C_V
  rw [← ENNReal.ofReal_mul hC2] at hVb'
  -- integrability of `‖czV φ · l‖²`, from the finiteness of the lower integral
  have hint : ∀ l : Fin n, Integrable (fun z => ‖czV φ z l‖ ^ 2) := by
    intro l
    have hle : (∫⁻ z : Fin n → ℂ, ENNReal.ofReal (‖czV φ z l‖ ^ 2))
        ≤ ∫⁻ z : Fin n → ℂ, ∑ l' : Fin n, ENNReal.ofReal (‖czV φ z l'‖ ^ 2) :=
      lintegral_mono fun z => Finset.single_le_sum
        (f := fun l' : Fin n => ENNReal.ofReal (‖czV φ z l'‖ ^ 2))
        (fun l' _ => bot_le) (Finset.mem_univ l)
    have hlt : (∫⁻ z : Fin n → ℂ, ENNReal.ofReal (‖czV φ z l‖ ^ 2)) < ⊤ :=
      lt_of_le_of_lt hle (lt_of_le_of_lt hVb' ENNReal.ofReal_lt_top)
    exact (lintegral_ofReal_ne_top_iff_integrable
      ((continuous_normSq _ (hcont l)).aestronglyMeasurable)
      (Eventually.of_forall fun z => by positivity)).mp hlt.ne
  have hconv : ENNReal.ofReal (∑ l : Fin n, ∫ z : Fin n → ℂ, ‖czV φ z l‖ ^ 2)
      = ∫⁻ z : Fin n → ℂ, ∑ l : Fin n, ENNReal.ofReal (‖czV φ z l‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => integral_nonneg fun z => by positivity)]
    rw [lintegral_finsetSum (s := Finset.univ)
      (f := fun (l : Fin n) (z : Fin n → ℂ) => ENNReal.ofReal (‖czV φ z l‖ ^ 2))
      (fun l _ => ENNReal.measurable_ofReal.comp ((continuous_normSq _ (hcont l)).measurable))]
    exact Finset.sum_congr rfl fun l _ =>
      (ofReal_integral_eq_lintegral_ofReal (hint l) (Eventually.of_forall fun z => by positivity))
  refine (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC2 (czEnergy_nonneg φ))).mp ?_
  rw [hconv]
  exact hVb'

/-! ## Integrability of the squared modulus of the adjoint field -/

lemma integrable_normSq_czV (hn : 0 < n) {C_V : ℝ}
    (hVb : ∀ (φ : Fin n → (Fin n → ℂ) → ℂ), (∀ i, ContDiff ℝ 1 (φ i)) →
      (∀ i, HasCompactSupport (φ i)) →
      (∫⁻ z : Fin n → ℂ, ∑ l : Fin n, ENNReal.ofReal (‖czV φ z l‖ ^ 2))
        ≤ ENNReal.ofReal (C_V ^ 2) *
          ∫⁻ z : Fin n → ℂ, ∑ i : Fin n, ENNReal.ofReal (‖φ i z‖ ^ 2))
    (φ : Fin n → (Fin n → ℂ) → ℂ) (hφ : ∀ i, ContDiff ℝ 1 (φ i))
    (hφc : ∀ i, HasCompactSupport (φ i)) (l : Fin n) :
    Integrable (fun z => ‖czV φ z l‖ ^ 2) := by
  have hcont : ∀ l, Continuous (fun z => czV φ z l) := fun l => continuous_czV hn hφ hφc l
  have hR : (∫⁻ z : Fin n → ℂ, ∑ i : Fin n, ENNReal.ofReal (‖φ i z‖ ^ 2))
      = ENNReal.ofReal (czEnergy φ) :=
    lintegral_sum_ofReal_normSq φ (fun i => (hφ i).continuous) hφc
  have hVb' := hVb φ hφ hφc
  rw [hR] at hVb'
  rw [← ENNReal.ofReal_mul (sq_nonneg C_V)] at hVb'
  have hle : (∫⁻ z : Fin n → ℂ, ENNReal.ofReal (‖czV φ z l‖ ^ 2))
      ≤ ∫⁻ z : Fin n → ℂ, ∑ l' : Fin n, ENNReal.ofReal (‖czV φ z l'‖ ^ 2) :=
    lintegral_mono fun z => Finset.single_le_sum
      (f := fun l' : Fin n => ENNReal.ofReal (‖czV φ z l'‖ ^ 2))
      (fun l' _ => bot_le) (Finset.mem_univ l)
  have hlt : (∫⁻ z : Fin n → ℂ, ENNReal.ofReal (‖czV φ z l‖ ^ 2)) < ⊤ :=
    lt_of_le_of_lt hle (lt_of_le_of_lt hVb' ENNReal.ofReal_lt_top)
  exact (lintegral_ofReal_ne_top_iff_integrable
    ((continuous_normSq _ (hcont l)).aestronglyMeasurable)
    (Eventually.of_forall fun z => by positivity)).mp hlt.ne

/-! ## The Cauchy–Schwarz estimate for the pairing -/

lemma pairing_bound (hn : 0 < n) {C_V : ℝ}
    (hVb : ∀ (φ : Fin n → (Fin n → ℂ) → ℂ), (∀ i, ContDiff ℝ 1 (φ i)) →
      (∀ i, HasCompactSupport (φ i)) →
      (∫⁻ z : Fin n → ℂ, ∑ l : Fin n, ENNReal.ofReal (‖czV φ z l‖ ^ 2))
        ≤ ENNReal.ofReal (C_V ^ 2) *
          ∫⁻ z : Fin n → ℂ, ∑ i : Fin n, ENNReal.ofReal (‖φ i z‖ ^ 2))
    {ψ : Fin n → (Fin n → ℂ) → ℂ}
    (hψ : ∀ j, Continuous (ψ j)) (hψc : ∀ j, HasCompactSupport (ψ j))
    (hu : ContDiff ℝ 1 (bmPotential ψ))
    {φ : Fin n → (Fin n → ℂ) → ℂ} (hφ : ∀ i, ContDiff ℝ 1 (φ i))
    (hφc : ∀ i, HasCompactSupport (φ i)) :
    ‖∑ i, ∫ z, Work.CR.Flat.dCoord i (bmPotential ψ) z * star (φ i z)‖
      ≤ Real.sqrt (czEnergy ψ) * Real.sqrt (C_V ^ 2 * czEnergy φ) := by
  have hcont : ∀ l, Continuous (fun z => czV φ z l) := fun l => continuous_czV hn hφ hφc l
  rw [czB_C0_pairing hn hψ hψc hu hφ hφc]
  have hmemV : ∀ l, MemLp (fun w => czV φ w l) 2 volume := fun l =>
    (memLp_two_iff_integrable_sq_norm (hcont l).aestronglyMeasurable).mpr
      (integrable_normSq_czV hn hVb φ hφ hφc l)
  have hmemψ : ∀ l, MemLp (fun w => ψ l w) 2 volume := fun l =>
    (hψ l).memLp_of_hasCompactSupport (hψc l)
  have hCS : ∀ l : Fin n, ‖∫ w, ψ l w * czV φ w l‖
      ≤ Real.sqrt (∫ w, ‖ψ l w‖ ^ 2) * Real.sqrt (∫ w, ‖czV φ w l‖ ^ 2) := by
    intro l
    have hCS' := integral_mul_norm_le_Lp_mul_Lq (μ := volume)
      (f := fun w : Fin n → ℂ => ψ l w) (g := fun w : Fin n → ℂ => czV φ w l)
      (p := 2) (q := 2) Real.HolderConjugate.two_two (by simpa using hmemψ l)
      (by simpa using hmemV l)
    calc ‖∫ w, ψ l w * czV φ w l‖
        ≤ ∫ w, ‖ψ l w * czV φ w l‖ := norm_integral_le_integral_norm _
      _ = ∫ w, ‖ψ l w‖ * ‖czV φ w l‖ := by simp_rw [norm_mul]
      _ ≤ (∫ w, ‖ψ l w‖ ^ (2 : ℝ)) ^ (1 / 2)
            * (∫ w, ‖czV φ w l‖ ^ (2 : ℝ)) ^ (1 / 2) := hCS'
      _ = Real.sqrt (∫ w, ‖ψ l w‖ ^ 2) * Real.sqrt (∫ w, ‖czV φ w l‖ ^ 2) := by
          rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
          simp_rw [Real.rpow_ofNat]
  calc ‖∑ l, ∫ w, ψ l w * czV φ w l‖
      ≤ ∑ l, ‖∫ w, ψ l w * czV φ w l‖ := norm_sum_le _ _
    _ ≤ ∑ l, Real.sqrt (∫ w, ‖ψ l w‖ ^ 2) * Real.sqrt (∫ w, ‖czV φ w l‖ ^ 2) :=
        Finset.sum_le_sum fun l _ => hCS l
    _ ≤ Real.sqrt (∑ l, ∫ w, ‖ψ l w‖ ^ 2) * Real.sqrt (∑ l, ∫ w, ‖czV φ w l‖ ^ 2) :=
        Real.sum_sqrt_mul_sqrt_le Finset.univ
          (fun l => integral_nonneg fun z => by positivity)
          (fun l => integral_nonneg fun z => by positivity)
    _ ≤ Real.sqrt (czEnergy ψ) * Real.sqrt (C_V ^ 2 * czEnergy φ) := by
        have hEV : (∑ l, ∫ w : Fin n → ℂ, ‖czV φ w l‖ ^ 2) ≤ C_V ^ 2 * czEnergy φ :=
          czV_energy_bound hn hVb φ hφ hφc
        rw [show (∑ l, ∫ w : Fin n → ℂ, ‖ψ l w‖ ^ 2) = czEnergy ψ from rfl]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hEV) (Real.sqrt_nonneg _)

/-! ## Two elementary points about the cutoff -/

lemma norm_cutC (R : ℝ) (z : Fin n → ℂ) : ‖cutC R z‖ = cutRe R z := by
  rw [cutC_apply, bmCz.norm_ofReal_eq_abs, abs_of_nonneg (cutRe_nonneg R z)]

lemma star_cutC (R : ℝ) (z : Fin n → ℂ) : star (cutC R z) = cutC R z := by
  rw [cutC_apply]; simp

lemma normSq_cutC_mul (R : ℝ) (z : Fin n → ℂ) (w : ℂ) :
    ‖cutC R z * w‖ ^ 2 = cutRe R z ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_mul, mul_pow, norm_cutC]

lemma normSq_cutC (R : ℝ) (z : Fin n → ℂ) : ‖cutC R z‖ ^ 2 = cutRe R z ^ 2 := by
  rw [norm_cutC]

lemma cutRe_sq_le_one (R : ℝ) (z : Fin n → ℂ) : cutRe R z ^ 2 ≤ 1 :=
  pow_le_one₀ (cutRe_nonneg R z) (cutRe_le_one R z)

/-- The product of the cutoff with a continuous function is integrable. -/
lemma integrable_cutC_mul {R : ℝ} (hR : 0 < R) {v : (Fin n → ℂ) → ℂ} (hv : Continuous v) :
    Integrable (fun z => cutC R z * v z) := by
  have hcont : Continuous (fun z : Fin n → ℂ => cutC R z * v z) :=
    (contDiff_cutC R).continuous.mul hv
  have hcs : HasCompactSupport (fun z : Fin n → ℂ => cutC R z * v z) :=
    (hasCompactSupport_cutC hR).mul_right
  exact hcont.integrable_of_hasCompactSupport hcs

/-- The squared modulus of the product of the cutoff with a continuous function is integrable. -/
lemma integrable_normSq_cutC_mul {R : ℝ} (hR : 0 < R) {v : (Fin n → ℂ) → ℂ}
    (hv : Continuous v) : Integrable (fun z => ‖cutC R z * v z‖ ^ 2) := by
  have hcont : Continuous (fun z : Fin n → ℂ => ‖cutC R z * v z‖ ^ 2) :=
    (((contDiff_cutC R).continuous.mul hv).norm).pow 2
  have hcs : HasCompactSupport (fun z : Fin n → ℂ => cutC R z * v z) :=
    (hasCompactSupport_cutC hR).mul_right
  have hcs2 : HasCompactSupport (fun z : Fin n → ℂ => ‖cutC R z * v z‖ ^ 2) :=
    (hcs.norm).comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  exact hcont.integrable_of_hasCompactSupport hcs2

/-- The square of the (real) cutoff is integrable. -/
lemma integrable_cutRe_sq {R : ℝ} (hR : 0 < R) :
    Integrable (fun z : Fin n → ℂ => cutRe R z ^ 2) := by
  have hfun : (fun z : Fin n → ℂ => cutRe R z ^ 2) = fun z => ‖cutC R z * 1‖ ^ 2 := by
    funext z; rw [normSq_cutC_mul R z 1, norm_one, one_pow, mul_one]
  rw [hfun]
  exact integrable_normSq_cutC_mul hR continuous_const

/-! ## The localised energy estimate -/

/-- **The localised energy estimate.**  For a radial cutoff `cutC R`, `0 < R`, the localised
energy of `∂ (bmPotential ψ)` is bounded by `C_V² E(ψ)`, provided the adjoint field obeys the `L²`
bound with constant `C_V` (`hVb`, see `Work.NN.Core.czV_L2_bound`).

The proof mollifies the localised data `g_i = χ ∂_i u`
(`Work.NN.Core.exists_contDiff_uniform_approx_continuous`), applies the pairing bound
`Work.NN.Core.pairing_bound`, and lets the mollification parameter tend to `0`. -/
lemma chi_step (hn : 0 < n) {C_V : ℝ} (hCV : 0 ≤ C_V)
    (hVb : ∀ (φ : Fin n → (Fin n → ℂ) → ℂ), (∀ i, ContDiff ℝ 1 (φ i)) →
      (∀ i, HasCompactSupport (φ i)) →
      (∫⁻ z : Fin n → ℂ, ∑ l : Fin n, ENNReal.ofReal (‖czV φ z l‖ ^ 2))
        ≤ ENNReal.ofReal (C_V ^ 2) *
          ∫⁻ z : Fin n → ℂ, ∑ i : Fin n, ENNReal.ofReal (‖φ i z‖ ^ 2))
    {ψ : Fin n → (Fin n → ℂ) → ℂ}
    (hψ : ∀ j, Continuous (ψ j)) (hψc : ∀ j, HasCompactSupport (ψ j))
    (hu : ContDiff ℝ 1 (bmPotential ψ)) {R : ℝ} (hR : 0 < R) :
    ∑ i, ∫ z, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2
      ≤ C_V ^ 2 * czEnergy ψ := by
  set A : ℝ := ∑ i, ∫ z, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2 with hA
  set B : ℝ := ∑ i, ∫ z, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ with hB
  set Lam : ℝ := ∫ z : Fin n → ℂ, ‖cutC R z‖ ^ 2 with hLam
  set K : ℝ := (n : ℝ) * Lam with hK
  have hAnn : 0 ≤ A := by
    rw [hA]; exact Finset.sum_nonneg fun i _ => integral_nonneg fun z => by positivity
  have hBnn : 0 ≤ B := by
    rw [hB]; exact Finset.sum_nonneg fun i _ => integral_nonneg fun z => by positivity
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  -- the main estimate, for every mollification parameter `ε > 0`
  have hkey : ∀ ε : ℝ, 0 < ε →
      A ≤ C_V * Real.sqrt (czEnergy ψ) * Real.sqrt (A + 2 * ε * B + ε ^ 2 * K) + ε * B := by
    intro ε hε
    have hgcont : ∀ i : Fin n, Continuous
        (fun z => cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z) :=
      fun i => (contDiff_cutC R).continuous.mul (continuous_dCoord i hu)
    have hgcs : ∀ i : Fin n, HasCompactSupport
        (fun z => cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z) :=
      fun i => HasCompactSupport.mul_right (hasCompactSupport_cutC hR)
    -- the smooth approximants of the localised data
    choose w hw using fun i : Fin n =>
      exists_contDiff_uniform_approx_continuous (hgcont i) (hgcs i) hε
    have hw_sm : ∀ i, ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (w i) := fun i => (hw i).1
    have hw_cs : ∀ i, HasCompactSupport (w i) := fun i => (hw i).2.1
    have hw_ap : ∀ i z, ‖w i z - cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ≤ ε :=
      fun i => (hw i).2.2
    have hw_bd : ∀ i z, ‖w i z‖ ≤ ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ + ε := by
      intro i z
      calc ‖w i z‖ = ‖(w i z - cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
              + cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ := by ring_nf
        _ ≤ ‖w i z - cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖
              + ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ := norm_add_le _ _
        _ ≤ ε + ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ := by
              linarith [hw_ap i z,
                norm_nonneg (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)]
        _ = ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ + ε := by ring
    -- the test field and the pairing bound
    have hφd : ∀ i, ContDiff ℝ 1 (fun z => cutC R z * w i z) :=
      fun i => (contDiff_cutC R).mul ((hw_sm i).of_le
        (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤)))
    have hφc : ∀ i, HasCompactSupport (fun z => cutC R z * w i z) :=
      fun i => HasCompactSupport.mul_right (hasCompactSupport_cutC hR)
    have hpb := pairing_bound hn hVb hψ hψc hu hφd hφc
    have hbridge : (∑ i, ∫ z, Work.CR.Flat.dCoord i (bmPotential ψ) z
          * star (cutC R z * w i z))
        = ∑ i, ∫ z, (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z) * star (w i z) := by
      refine Finset.sum_congr rfl fun i _ => integral_congr_ae (Eventually.of_forall fun z => ?_)
      show Work.CR.Flat.dCoord i (bmPotential ψ) z * star (cutC R z * w i z)
          = cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z * star (w i z)
      rw [star_mul, star_cutC]; ring
    rw [hbridge] at hpb
    -- integrability of the auxiliary integrands
    have hInt_gg : ∀ i : Fin n, Integrable (fun z =>
        (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
          * star (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)) := fun i =>
      ((hgcont i).mul ((hgcont i).star)).integrable_of_hasCompactSupport (hgcs i).mul_right
    have hInt_gw : ∀ i : Fin n, Integrable (fun z =>
        (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z) * star (w i z)) := fun i =>
      ((hgcont i).mul ((hw_sm i).continuous.star)).integrable_of_hasCompactSupport
        (hgcs i).mul_right
    have hInt_gd : ∀ i : Fin n, Integrable (fun z =>
        (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
          * star (w i z - cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)) := fun i =>
      ((hgcont i).mul ((hw_sm i).continuous.sub (hgcont i)).star).integrable_of_hasCompactSupport
        (hgcs i).mul_right
    -- (a) the localised energy is the norm of the pairing against itself
    have hAsum : (∑ i, ∫ z, (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
          * star (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)) = ((A : ℝ) : ℂ) := by
      have h1 : ∀ i : Fin n, (∫ z, (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
            * star (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z))
          = ((∫ z, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2 : ℝ) : ℂ) := by
        intro i
        rw [show (fun z => (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
              * star (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z))
            = fun z => ((‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2 : ℝ) : ℂ) from
          funext fun z => by
            simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]]
        exact Complex.ofRealCLM.integral_comp_comm (integrable_normSq_cutC_mul hR (continuous_dCoord i hu))
      rw [Finset.sum_congr rfl fun i _ => h1 i, hA]
      exact (Complex.ofReal_sum Finset.univ
        (fun i : Fin n => ∫ z : Fin n → ℂ, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2)).symm
    -- (b) the pairing against the approximants is close to the energy
    have hlow : A - ε * B ≤ ‖∑ i, ∫ z, (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
        * star (w i z)‖ := by
      set Cc : ℂ := ∑ i, ∫ z, (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
        * star (w i z - cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z) with hCc
      have hper : ∀ i : Fin n, (∫ z, (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z) * star (w i z))
          = (∫ z, (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
                * star (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z))
            + ∫ z, (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
                * star (w i z - cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z) := by
        intro i
        rw [← integral_add (hInt_gg i) (hInt_gd i)]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        show cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z * star (w i z)
            = cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z
                * star (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
              + cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z
                * star (w i z - cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
        rw [star_sub]
        ring
      have hdecomp : (∑ i, ∫ z, (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z) * star (w i z))
          = ((A : ℝ) : ℂ) + Cc := by
        rw [hCc, Finset.sum_congr rfl fun i _ => hper i, Finset.sum_add_distrib, hAsum]
      have hcorr : ‖Cc‖ ≤ ε * B := by
        have h1 : ‖Cc‖ ≤ ∑ i, ∫ z, ‖(cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
            * star (w i z - cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)‖ := by
          rw [hCc]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          exact norm_integral_le_integral_norm _
        have h2 : ∀ i : Fin n, (∫ z, ‖(cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
              * star (w i z - cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)‖)
            ≤ ε * ∫ z, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ := by
          intro i
          have hpt : ∀ z, ‖(cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
              * star (w i z - cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)‖
              ≤ ε * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ := by
            intro z
            calc ‖(cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
                  * star (w i z - cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)‖
                = ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖
                  * ‖w i z - cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ := by
                  rw [norm_mul, norm_star]
              _ ≤ ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ * ε :=
                  mul_le_mul_of_nonneg_left (hw_ap i z) (norm_nonneg _)
              _ = ε * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ := by ring
          have hInt2 : Integrable (fun z =>
              ε * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖) :=
            (integrable_cutC_mul hR (continuous_dCoord i hu)).norm.const_mul ε
          calc (∫ z, ‖(cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
                * star (w i z - cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)‖)
              ≤ ∫ z, ε * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ :=
                integral_mono (hInt_gd i).norm hInt2 (fun z => hpt z)
            _ = ε * ∫ z, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ :=
                integral_const_mul _ _
        calc ‖Cc‖ ≤ ∑ i, ∫ z, ‖(cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
              * star (w i z - cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)‖ := h1
          _ ≤ ∑ i, ε * ∫ z, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ :=
              Finset.sum_le_sum fun i _ => h2 i
          _ = ε * B := by rw [← Finset.mul_sum, hB]
      have hmain : A ≤ ‖∑ i, ∫ z, (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z)
          * star (w i z)‖ + ε * B := by
        calc A = ‖((A : ℝ) : ℂ)‖ := by
              rw [bmCz.norm_ofReal_eq_abs, abs_of_nonneg hAnn]
          _ ≤ ‖((A : ℝ) : ℂ) + Cc‖ + ‖Cc‖ := by
              have h := norm_sub_le (((A : ℝ) : ℂ) + Cc) Cc
              rwa [add_sub_cancel_right] at h
          _ = ‖∑ i, ∫ z, (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z) * star (w i z)‖
                + ‖Cc‖ := by rw [← hdecomp]
          _ ≤ ‖∑ i, ∫ z, (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z) * star (w i z)‖
                + ε * B := add_le_add_right hcorr _
      linarith [hmain]
    -- (c) the energy of the test field
    have hEphi : (∑ i, ∫ z, ‖cutC R z * w i z‖ ^ 2) ≤ A + 2 * ε * B + ε ^ 2 * K := by
      have hterm : ∀ i : Fin n, (∫ z, ‖cutC R z * w i z‖ ^ 2) ≤
          (∫ z, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2)
            + 2 * ε * (∫ z, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖) + ε ^ 2 * Lam := by
        intro i
        have hpt : ∀ z, ‖cutC R z * w i z‖ ^ 2 ≤ ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2
            + 2 * ε * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖
            + ε ^ 2 * cutRe R z ^ 2 := by
          intro z
          have ha := cutRe_nonneg R z
          have ha1 := cutRe_sq_le_one R z
          have h2 : ‖w i z‖ ^ 2 ≤ (‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ + ε) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hw_bd i z) 2
          have h3 : cutRe R z ^ 2 * ‖w i z‖ ^ 2
              ≤ cutRe R z ^ 2 * (‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ + ε) ^ 2 :=
            mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
          have h5 : cutRe R z ^ 2 * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2
              ≤ ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2 := by
            have := mul_le_of_le_one_left (sq_nonneg ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖) ha1
            simpa [mul_comm] using this
          have h6 : cutRe R z ^ 2 * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖
              ≤ ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ :=
            mul_le_of_le_one_left (norm_nonneg _) ha1
          have hexp : cutRe R z ^ 2 * (‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ + ε) ^ 2
              = cutRe R z ^ 2 * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2
                + 2 * ε * (cutRe R z ^ 2 * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖)
                + ε ^ 2 * cutRe R z ^ 2 := by ring
          have h6' : 2 * ε * (cutRe R z ^ 2 * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖)
              ≤ 2 * ε * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ :=
            mul_le_mul_of_nonneg_left h6 (by positivity)
          rw [normSq_cutC_mul]
          calc cutRe R z ^ 2 * ‖w i z‖ ^ 2
              ≤ cutRe R z ^ 2 * (‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ + ε) ^ 2 := h3
            _ = cutRe R z ^ 2 * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2
                + 2 * ε * (cutRe R z ^ 2 * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖)
                + ε ^ 2 * cutRe R z ^ 2 := hexp
            _ ≤ ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2
                + 2 * ε * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖
                + ε ^ 2 * cutRe R z ^ 2 := by linarith [h5, h6']
        have hIntL : Integrable (fun z => ‖cutC R z * w i z‖ ^ 2) :=
          integrable_normSq_cutC_mul hR (hw_sm i).continuous
        have hIntR : Integrable (fun z => ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2
            + 2 * ε * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖
            + ε ^ 2 * cutRe R z ^ 2) := by
          refine ((integrable_normSq_cutC_mul hR (continuous_dCoord i hu)).add ?_).add ?_
          · exact (integrable_cutC_mul hR (continuous_dCoord i hu)).norm.const_mul (2 * ε)
          · exact (integrable_cutRe_sq hR).const_mul _
        have h3 := integral_mono hIntL hIntR (fun z => hpt z)
        calc (∫ z, ‖cutC R z * w i z‖ ^ 2)
            ≤ ∫ z, (‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2
                + 2 * ε * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖
                + ε ^ 2 * cutRe R z ^ 2) := h3
          _ = (∫ z, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2)
              + 2 * ε * (∫ z, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖)
              + ε ^ 2 * Lam := by
              have hI1 : Integrable (fun z => ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2) :=
                integrable_normSq_cutC_mul hR (continuous_dCoord i hu)
              have hI2 : Integrable (fun z => 2 * ε * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖) :=
                (integrable_cutC_mul hR (continuous_dCoord i hu)).norm.const_mul (2 * ε)
              have hI3 : Integrable (fun z : Fin n → ℂ => ε ^ 2 * cutRe R z ^ 2) :=
                (integrable_cutRe_sq hR).const_mul _
              have hLamRe : Lam = ∫ z : Fin n → ℂ, cutRe R z ^ 2 := by
                rw [hLam]
                exact integral_congr_ae (Eventually.of_forall fun z => normSq_cutC R z)
              rw [integral_add (f := fun z => ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2
                      + 2 * ε * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖)
                    (g := fun z => ε ^ 2 * cutRe R z ^ 2) (hI1.add hI2) hI3,
                integral_add (f := fun z => ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2)
                  (g := fun z => 2 * ε * ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖) hI1 hI2,
                integral_const_mul, integral_const_mul, hLamRe]
      calc (∑ i, ∫ z, ‖cutC R z * w i z‖ ^ 2)
          ≤ ∑ i, ((∫ z, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2)
              + 2 * ε * (∫ z, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖) + ε ^ 2 * Lam) :=
            Finset.sum_le_sum fun i _ => hterm i
        _ = A + 2 * ε * B + ε ^ 2 * K := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← hA, ← hB,
              Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hK]
            ring
    -- combine
    have h1 : A ≤ Real.sqrt (czEnergy ψ)
        * Real.sqrt (C_V ^ 2 * (∑ i, ∫ z, ‖cutC R z * w i z‖ ^ 2)) + ε * B := by
      calc A = (A - ε * B) + ε * B := by ring
        _ ≤ ‖∑ i, ∫ z, (cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z) * star (w i z)‖
              + ε * B := add_le_add_left hlow (ε * B)
        _ ≤ Real.sqrt (czEnergy ψ)
              * Real.sqrt (C_V ^ 2 * (∑ i, ∫ z, ‖cutC R z * w i z‖ ^ 2)) + ε * B :=
            add_le_add_left hpb _
    have h2 : Real.sqrt (C_V ^ 2 * (∑ i, ∫ z, ‖cutC R z * w i z‖ ^ 2))
        ≤ C_V * Real.sqrt (A + 2 * ε * B + ε ^ 2 * K) := by
      rw [Real.sqrt_mul (sq_nonneg C_V), Real.sqrt_sq hCV]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hEphi) hCV
    calc A ≤ Real.sqrt (czEnergy ψ)
          * Real.sqrt (C_V ^ 2 * (∑ i, ∫ z, ‖cutC R z * w i z‖ ^ 2)) + ε * B := h1
      _ ≤ Real.sqrt (czEnergy ψ) * (C_V * Real.sqrt (A + 2 * ε * B + ε ^ 2 * K)) + ε * B :=
          add_le_add_left (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)) _
      _ = C_V * Real.sqrt (czEnergy ψ) * Real.sqrt (A + 2 * ε * B + ε ^ 2 * K) + ε * B := by ring
  -- pass to the limit `ε → 0`
  have hlim : A ≤ C_V * Real.sqrt (czEnergy ψ) * Real.sqrt A := by
    have hεs : Tendsto (fun m : ℕ => (1 : ℝ) / (m + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hu_tend : Tendsto (fun m : ℕ => A - ((1 : ℝ) / (m + 1)) * B) atTop (nhds A) := by
      simpa using (tendsto_const_nhds.sub ((hεs.mul tendsto_const_nhds)))

    have hv_tend : Tendsto (fun m : ℕ => C_V * Real.sqrt (czEnergy ψ)
        * Real.sqrt (A + 2 * ((1 : ℝ) / (m + 1)) * B + ((1 : ℝ) / (m + 1)) ^ 2 * K)
        + ((1 : ℝ) / (m + 1)) * B) atTop
        (nhds (C_V * Real.sqrt (czEnergy ψ) * Real.sqrt A)) := by
      have harg : Tendsto (fun m : ℕ => A + 2 * ((1 : ℝ) / (m + 1)) * B
          + ((1 : ℝ) / (m + 1)) ^ 2 * K) atTop (nhds A) := by
        have h1 : Tendsto (fun m : ℕ => ((1 : ℝ) / (m + 1)) ^ 2 * K) atTop (nhds 0) := by
          simpa using (hεs.pow 2).mul tendsto_const_nhds
        have h2 : Tendsto (fun m : ℕ => 2 * ((1 : ℝ) / (m + 1)) * B) atTop (nhds 0) := by
          simpa using (hεs.const_mul 2).mul tendsto_const_nhds
        simpa using ((tendsto_const_nhds.add h2).add h1)
      have hsq : Tendsto (fun m : ℕ => Real.sqrt (A + 2 * ((1 : ℝ) / (m + 1)) * B
          + ((1 : ℝ) / (m + 1)) ^ 2 * K)) atTop (nhds (Real.sqrt A)) :=
        (Real.continuous_sqrt.tendsto A).comp harg
      simpa using ((hsq.const_mul (C_V * Real.sqrt (czEnergy ψ))).add
        (hεs.mul tendsto_const_nhds))
    refine le_of_tendsto_of_tendsto' hu_tend hv_tend fun m => ?_
    have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have h1 := hkey (1 / ((m : ℝ) + 1)) hε
    have h2 : 0 ≤ (1 / ((m : ℝ) + 1)) * B := mul_nonneg (by positivity) hBnn
    linarith
  -- conclude `A ≤ C_V² E(ψ)`
  have hEsqnn : 0 ≤ czEnergy ψ := czEnergy_nonneg ψ
  have hfin : A ≤ C_V ^ 2 * czEnergy ψ := by
    rcases eq_or_lt_of_le hAnn with hA0 | hApos
    · rw [← hA0]; positivity
    · have hspos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hApos
      have h2 : Real.sqrt A ≤ C_V * Real.sqrt (czEnergy ψ) := by
        have h4 : Real.sqrt A * Real.sqrt A ≤ Real.sqrt A * (C_V * Real.sqrt (czEnergy ψ)) := by
          calc Real.sqrt A * Real.sqrt A = A := by rw [← sq, Real.sq_sqrt hAnn]
            _ ≤ C_V * Real.sqrt (czEnergy ψ) * Real.sqrt A := hlim
            _ = Real.sqrt A * (C_V * Real.sqrt (czEnergy ψ)) := by ring
        exact (mul_le_mul_iff_of_pos_left hspos).mp h4
      calc A = Real.sqrt A ^ 2 := (Real.sq_sqrt hAnn).symm
        _ ≤ (C_V * Real.sqrt (czEnergy ψ)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg A) h2 2
        _ = C_V ^ 2 * czEnergy ψ := by rw [mul_pow, Real.sq_sqrt hEsqnn]
  rw [hA]
  exact hfin

theorem czB_L2_bounded_C0 {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, Continuous (ψ j)) → (∀ j, HasCompactSupport (ψ j)) →
      ContDiff ℝ 1 (Work.CR.Flat.Cauchy.bmPotential ψ) →
      (∫⁻ z : Fin n → ℂ, ∑ i : Fin n, ENNReal.ofReal
          ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential ψ) z‖ ^ 2)
        ≤ ENNReal.ofReal (C ^ 2) *
          ∫⁻ z : Fin n → ℂ, ∑ j : Fin n, ENNReal.ofReal ‖ψ j z‖ ^ 2 := by
  obtain ⟨C_V, hCV, hVb⟩ := czV_L2_bound (n := n) hn
  refine ⟨C_V, hCV, fun ψ hψ hψc hu => ?_⟩
  set G : (Fin n → ℂ) → ℝ≥0∞ :=
    fun z => ∑ i, ENNReal.ofReal (‖Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2) with hG
  have hleft : (∫⁻ z : Fin n → ℂ, ∑ i, ENNReal.ofReal
        ‖Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2) = ∫⁻ z, G z := by
    rw [hG]
    refine lintegral_congr fun z => ?_
    exact Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
  have hright : (∫⁻ z : Fin n → ℂ, ∑ j : Fin n, ENNReal.ofReal ‖ψ j z‖ ^ 2)
      = ENNReal.ofReal (czEnergy ψ) := by
    rw [show (fun z : Fin n → ℂ => ∑ j, ENNReal.ofReal ‖ψ j z‖ ^ 2)
        = fun z => ∑ j, ENNReal.ofReal (‖ψ j z‖ ^ 2) from
      funext fun z => Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_pow (norm_nonneg _) 2).symm]
    exact lintegral_sum_ofReal_normSq ψ hψ hψc
  rw [hleft, hright, ← ENNReal.ofReal_mul (sq_nonneg C_V)]
  -- the integral over each ball is bounded
  have hball : ∀ m : ℕ, (∫⁻ z in Metric.closedBall (0 : Fin n → ℂ) (m : ℝ), G z)
      ≤ ENNReal.ofReal (C_V ^ 2 * czEnergy ψ) := by
    intro m
    set R : ℝ := (m : ℝ) * Real.sqrt (2 * n) + 1 with hRd
    have hRpos : 0 < R := by rw [hRd]; positivity
    have hR2 : 2 * (n : ℝ) * (m : ℝ) ^ 2 ≤ R ^ 2 := by
      have h1 : 0 ≤ (m : ℝ) * Real.sqrt (2 * n) := by positivity
      have h2 : ((m : ℝ) * Real.sqrt (2 * n)) ^ 2 = (m : ℝ) ^ 2 * (2 * (n : ℝ)) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      rw [hRd]
      nlinarith [h1, h2, sq_nonneg ((m : ℝ) * Real.sqrt (2 * n) + 1)]
    have hcut : ∀ z ∈ Metric.closedBall (0 : Fin n → ℂ) (m : ℝ), cutRe R z = 1 := by
      intro z hz
      refine cutRe_eq_one ?_
      have hz' : ‖z‖ ≤ (m : ℝ) := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      have hnrm : nrmSq z ≤ (n : ℝ) * ‖z‖ ^ 2 := nrmSq_le_card_mul z
      have hz2 : ‖z‖ ^ 2 ≤ (m : ℝ) ^ 2 := by nlinarith [norm_nonneg z]
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hstep1 : 2 * nrmSq z ≤ 2 * ((n : ℝ) * ‖z‖ ^ 2) := by linarith
      have hstep2 : 2 * ((n : ℝ) * ‖z‖ ^ 2) ≤ 2 * (n : ℝ) * (m : ℝ) ^ 2 := by
        nlinarith [hz2, hn0]
      linarith [hstep1, hstep2, hR2]
    have hpt : ∀ z : Fin n → ℂ,
        Set.indicator (Metric.closedBall (0 : Fin n → ℂ) (m : ℝ)) G z
          ≤ ENNReal.ofReal (cutRe R z ^ 2) * G z := by
      intro z
      by_cases hz : z ∈ Metric.closedBall (0 : Fin n → ℂ) (m : ℝ)
      · rw [Set.indicator_of_mem hz, hcut z hz, one_pow, ENNReal.ofReal_one, one_mul]
      · rw [Set.indicator_of_notMem hz]
        exact bot_le
    have hInt : Integrable (fun z : Fin n → ℂ =>
        cutRe R z ^ 2 * ∑ i, ‖Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2) := by
      have : (fun z : Fin n → ℂ => cutRe R z ^ 2 * ∑ i, ‖Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2)
          = fun z => (∑ i, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2) := by
        funext z
        show cutRe R z ^ 2 * ∑ i, ‖Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2
            = ∑ i, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2
        rw [Finset.mul_sum Finset.univ (fun i => ‖Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2) (cutRe R z ^ 2)]
        exact Finset.sum_congr rfl fun i _ => (normSq_cutC_mul R z _).symm
      rw [this]
      exact integrable_finsetSum _ fun i _ => integrable_normSq_cutC_mul hRpos (continuous_dCoord i hu)
    calc (∫⁻ z in Metric.closedBall (0 : Fin n → ℂ) (m : ℝ), G z)
        = ∫⁻ z, Set.indicator (Metric.closedBall (0 : Fin n → ℂ) (m : ℝ)) G z :=
          (lintegral_indicator measurableSet_closedBall G).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (cutRe R z ^ 2) * G z := lintegral_mono hpt
      _ = ∫⁻ z, ENNReal.ofReal (cutRe R z ^ 2 * ∑ i, ‖Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2) := by
          refine lintegral_congr fun z => ?_
          rw [hG, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      _ = ENNReal.ofReal (∫ z, cutRe R z ^ 2 * ∑ i, ‖Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2) :=
          (ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall fun z => by positivity)).symm
      _ ≤ ENNReal.ofReal (C_V ^ 2 * czEnergy ψ) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [show (∫ z : Fin n → ℂ, cutRe R z ^ 2 * ∑ i, ‖Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2)
              = ∑ i, ∫ z, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2 from by
            rw [← integral_finsetSum Finset.univ (fun i _ =>
              integrable_normSq_cutC_mul hRpos (continuous_dCoord i hu))]
            refine integral_congr_ae (Eventually.of_forall fun z => ?_)
            show cutRe R z ^ 2 * ∑ i, ‖Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2
                = ∑ i, ‖cutC R z * Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2
            rw [Finset.mul_sum Finset.univ (fun i => ‖Work.CR.Flat.dCoord i (bmPotential ψ) z‖ ^ 2) (cutRe R z ^ 2)]
            exact Finset.sum_congr rfl fun i _ => (normSq_cutC_mul R z _).symm]
          exact chi_step hn hCV hVb hψ hψc hu hRpos
  -- monotone convergence in `m`
  have hGmeas : Measurable G :=
    Finset.measurable_sum _ fun i _ =>
      ENNReal.measurable_ofReal.comp ((continuous_dCoord i hu).norm.pow 2).measurable
  have hmeas : ∀ m : ℕ, Measurable (fun z : Fin n → ℂ =>
      Set.indicator (Metric.closedBall (0 : Fin n → ℂ) (m : ℝ)) G z) := fun m =>
    hGmeas.indicator measurableSet_closedBall
  have hmono : Monotone (fun m : ℕ => fun z : Fin n → ℂ =>
      Set.indicator (Metric.closedBall (0 : Fin n → ℂ) (m : ℝ)) G z) := by
    intro m m' hmm'
    intro z
    simp only []
    by_cases hz : z ∈ Metric.closedBall (0 : Fin n → ℂ) (m : ℝ)
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (Metric.closedBall_subset_closedBall
        (by exact_mod_cast hmm') hz)]
    · rw [Set.indicator_of_notMem hz]; exact bot_le
  have hsup := lintegral_iSup (μ := volume) hmeas hmono
  have hcongrL : (fun z : Fin n → ℂ => ⨆ m : ℕ,
      Set.indicator (Metric.closedBall (0 : Fin n → ℂ) (m : ℝ)) G z) = G := by
    funext z
    refine le_antisymm (iSup_le fun m => ?_) ?_
    · by_cases hz : z ∈ Metric.closedBall (0 : Fin n → ℂ) (m : ℝ)
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]; exact bot_le
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, ‖z‖ < (m : ℝ) := by
        obtain ⟨m, hm⟩ := exists_nat_gt ‖z‖
        exact ⟨m, by exact_mod_cast hm⟩
      refine le_iSup_of_le m ?_
      rw [Set.indicator_of_mem (by
        rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hm)]
  have heq1 : (∫⁻ z : Fin n → ℂ, G z)
      = ∫⁻ z, (fun z' : Fin n → ℂ => ⨆ m : ℕ,
          Set.indicator (Metric.closedBall (0 : Fin n → ℂ) (m : ℝ)) G z') z :=
    lintegral_congr fun z => (congrFun hcongrL z).symm
  have hgoal : (∫⁻ z : Fin n → ℂ, G z)
      = ⨆ m : ℕ, (∫⁻ z in Metric.closedBall (0 : Fin n → ℂ) (m : ℝ), G z) :=
    calc (∫⁻ z : Fin n → ℂ, G z)
        = ∫⁻ z, (fun z' : Fin n → ℂ => ⨆ m : ℕ,
            Set.indicator (Metric.closedBall (0 : Fin n → ℂ) (m : ℝ)) G z') z := heq1
      _ = ⨆ m : ℕ, ∫⁻ z, Set.indicator (Metric.closedBall (0 : Fin n → ℂ) (m : ℝ)) G z := hsup
      _ = ⨆ m : ℕ, (∫⁻ z in Metric.closedBall (0 : Fin n → ℂ) (m : ℝ), G z) :=
          iSup_congr fun m => lintegral_indicator measurableSet_closedBall G
  calc (∫⁻ z : Fin n → ℂ, G z)
      = ⨆ m : ℕ, (∫⁻ z in Metric.closedBall (0 : Fin n → ℂ) (m : ℝ), G z) := hgoal
    _ ≤ ENNReal.ofReal (C_V ^ 2 * czEnergy ψ) := iSup_le fun m => hball m

end Work.NN.Core
