import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSquareLpDefs
import Submission.Work.BourgainPlan.Maximal.annulusSqfun_finsetMikhlin
import Submission.Work.BourgainPlan.Maximal.annulusSquareLp_finset
import Submission.Work.BourgainPlan.Maximal.annulusSymbolSmooth_of_dilate

/-!
# The `L^p` bound of the annulus square function, all `1 < p < ∞`

This is MST's `(eq:52)` input 2 — the Littlewood–Paley square-function bound for the annulus
family `K_m = 𝓕⁻ (b m)` — in the form `<∑'_n ‖(K_{j+n} * f)(x)‖²>^{1/2}`:

**`annulusSquareLp`**: for an annulus symbol family `b` (`AnnulusSymbolSmooth b`, each member `C^∞`)
and every `1 < p < ∞` there is `C > 0` with, for every base scale `j ∈ ℤ` and every `f ∈ L^p(ℝ)`,

  `∫⁻ x, (annulusSqfun b j f x) ^ p ≤ C ∫⁻ x, ‖f x‖^p`,

i.e. `AnnulusSquareLp p b`.  The constant is uniform in `j`.

This supersedes the two endpoint/interpolation results already on disk
(`annulusSquare_l2` at `p = 2`, `annulusSquareWeakType` at `p = 1` weak, and
`annulusSquareLp_lt_two` for `1 < p < 2` in the `L¹ ∩ L²` form): the proof here is
Khintchine + the Mikhlin multiplier theorem, and it yields **all** `1 < p < ∞` for `f ∈ L^p`
only (no `L¹` hypothesis).  In particular it supplies the previously missing range `p > 2`
(rung (iv) of the status notes).

The chain is:

* `rademacher_lower_finset` (Khintchine, lower half) — the sign average dominates the ℓ² sum;
* `annulusSymbolSum_mikhlin` — the signed symbol sums are Mikhlin with a constant uniform in the
  base scale, in the finite index set and in the signs;
* `mikhlinConvolutionLp` — the Mikhlin multiplier bound on `L^p` in convolution form;
* `annulusConv_finsetSum_eq` — the signed sum of the annulus convolutions *is* the convolution with
  the signed symbol;
* `annulusSquareLp_finset` — the finite-index-set form;
* `annulusSquareLp_of_finset` — monotone convergence to the full two-sided sum `∑'_n`.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BourgainPlan.Maximal

/-- **The `L^p` bound of the annulus square function, for every `1 < p < ∞`.**  Uniform in the base
scale `j`, and stated for `f ∈ L^p` alone. -/
theorem annulusSquareLp (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) {p : ℝ} (hp : 1 < p) :
    AnnulusSquareLp p b := by
  obtain ⟨C, hC, hfin⟩ := annulusSquareLp_finset b hb hsmooth hp
  refine ⟨C, hC, fun j f hf => ?_⟩
  exact annulusSquareLp_of_finset (lt_trans zero_lt_one hp)
    (fun j F f hf => hfin j F f hf) j f hf


/-- **The sup-in-scale corollary**: the bound of `annulusSquareLp` also holds for the maximal
function `⨆_n ‖(K_{j+n} * f)(x)‖` of the annulus family, since the ℓ² sum dominates the sup. -/
theorem annulusSup_le_annulusSquareLp (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (f : ℝ → ℂ), MemLp f (ENNReal.ofReal p) volume →
      ∫⁻ x, (⨆ n : ℤ, ‖annulusConv b (j + n) f x‖ₑ) ^ p
        ≤ ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ ^ p := by
  obtain ⟨C, hC, h⟩ := annulusSquareLp b hb hsmooth hp
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  refine ⟨C, hC, fun j f hf => ?_⟩
  refine le_trans (MeasureTheory.lintegral_mono (g := fun x : ℝ =>
    (annulusSqfun b j f x) ^ p) ?_) (h j f hf)
  intro x
  refine ENNReal.rpow_le_rpow ?_ hp0.le
  rw [annulusSqfun]
  refine iSup_le (fun n : ℤ => ?_)
  calc ‖annulusConv b (j + n) f x‖ₑ
      = (‖annulusConv b (j + n) f x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
        rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
    _ ≤ (∑' m : ℤ, ‖annulusConv b (j + m) f x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow
          (ENNReal.le_tsum (f := fun m : ℤ => ‖annulusConv b (j + m) f x‖ₑ ^ (2 : ℝ)) n) (by norm_num)


/-- **The canonical instance**: a fixed symbol `ψ` supported in the annulus `2⁻¹ < |ξ| < 2`, with
bounded iterated derivatives and of class `C^∞`, dilated to each dyadic scale
(`b m = ψ (2^m ·)`).  This is the shape in which the applications use the bound
(`annulusSymbolSmooth_of_dilate`). -/
theorem annulusSquareLp_of_dilate (ψ : ℝ → ℂ)
    (hsupp : ∀ ξ : ℝ, ψ ξ ≠ 0 → (2 : ℝ)⁻¹ < |ξ| ∧ |ξ| < 2)
    (hbdd : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, ‖iteratedDeriv k ψ ξ‖ ≤ C)
    (hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) {p : ℝ} (hp : 1 < p) :
    AnnulusSquareLp p (fun m ξ => ψ ((2 : ℝ) ^ m * ξ)) :=
  annulusSquareLp (fun m ξ => ψ ((2 : ℝ) ^ m * ξ))
    (annulusSymbolSmooth_of_dilate ψ hsupp hbdd)
    (fun _ => hsmooth.comp (contDiff_const.mul contDiff_id)) hp

end Work.BourgainPlan.Maximal
