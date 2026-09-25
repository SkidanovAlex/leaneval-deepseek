import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusDiffSqfunDefs
import Submission.Work.BourgainPlan.Maximal.annulusSquareLp
import Submission.Work.BourgainPlan.Maximal.annulusSqfun_add_le
import Submission.Work.BourgainPlan.Maximal.annulusDiffSqfunL2Gain

/-!
# The `L^q` bound of the difference annulus square function, all `1 < q < ∞`

`annulusSqfun b j f = (∑'_n ‖(K_{j+n} * f)‖²)^{1/2}` is `L^q`-bounded uniformly in `j` for every
`1 < q < ∞` (`annulusSquareLp`), for any annulus symbol family `b`.  This module transports that
bound to the *difference* square function

  `annulusDiffSqfun b b' j f = (∑'_n ‖(K'_{j+n} * f) - (K_{j+n} * f)‖²)^{1/2}`

of two annulus symbol families `b`, `b'` — the `L^q` endpoint (`hqbd`) of MST's `(eq:51)`, consumed
by `annulusDiffSqfun_decay`.

The route is the difference family `D m = b' m - b m`:

* `annulusSymbolSmooth_subfun` — `D` is again an annulus symbol family: its support is inherited
  (a point where `b' m - b m ≠ 0` is a point where at least one of them is non-zero) and its
  derivative bounds are `C_k(b') + C_k(b)` (`iteratedDeriv_sub`);
* `annulusDiffSqfun_eq_annulusSqfun_of_memLp` — on `L^q` inputs (`q ≥ 1`) the difference square
  function *is* the square function of `D`, by the additivity `annulusConv_sub_of_memLp` of the
  convolution in the symbol on integrable inputs (`annulusConv` is Mathlib's Bochner integral, which
  is additive only there);
* `eLpNorm_le_of_lintegral_rpow_le_eNN` — the conversion between the `∫⁻ (·)^q ≤ C ∫⁻ ‖·‖^q` shape
  in which `annulusSquareLp` is stated and the `eLpNorm` shape in which the target is stated, for
  `ℝ≥0∞`-valued `g` (`eLpNorm_rpow_self`).

The target then follows with `K_q = C^{1/q}`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- **From an `∫⁻ (·)^q` bound to an `eLpNorm` bound, for `ℝ≥0∞`-valued functions.**  If
`∫⁻ x, g x ^ q ≤ C ∫⁻ x, ‖f x‖^q` with `q > 0` and `0 ≤ C`, then
`‖g‖_{L^q} ≤ C^{1/q} ‖f‖_{L^q}`.  (The `ℝ≥0∞`-valued companion of
`eLpNorm_le_of_lintegral_rpow_le`.) -/
lemma eLpNorm_le_of_lintegral_rpow_le_eNN {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    {g : ℝ → ℝ≥0∞} {f : ℝ → ℂ}
    (h : ∫⁻ x, g x ^ q ≤ ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ ^ q)
    (hg : AEMeasurable g volume) (hf : AEStronglyMeasurable f volume) :
    eLpNorm g (ENNReal.ofReal q) (volume : Measure ℝ)
      ≤ ENNReal.ofReal (C ^ (1 / q)) * eLpNorm f (ENNReal.ofReal q) (volume : Measure ℝ) := by
  rw [← eLpNorm_rpow_self hq hg, ← annulusELpNorm_rpow_eq_lintegral hq hf] at h
  have hCeq : (ENNReal.ofReal (C ^ (1 / q))) ^ q = ENNReal.ofReal C := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hC _) (le_of_lt hq),
      ← Real.rpow_mul hC, one_div, inv_mul_cancel₀ hq.ne', Real.rpow_one]
  rw [← hCeq, ← ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hq)] at h
  exact (ENNReal.rpow_le_rpow_iff hq).mp h

/-- **The difference of two annulus symbol families is an annulus symbol family.**  The support is
inherited (where `b' m - b m` does not vanish at least one of `b' m`, `b m` does not) and the `k`-th
derivative bound is `C_k(b') + C_k(b)`. -/
lemma annulusSymbolSmooth_subfun (b b' : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hb' : AnnulusSymbolSmooth b')
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (hsmooth' : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b' m)) :
    AnnulusSymbolSmooth (fun m ξ => b' m ξ - b m ξ) := by
  refine ⟨?_, ?_⟩
  · intro m ξ hξ
    rw [sub_ne_zero] at hξ
    by_cases h : b' m ξ = 0
    · exact hb.1 m ξ (fun hbm => hξ (by rw [h, hbm]))
    · exact hb'.1 m ξ h
  · intro k
    obtain ⟨Cb, hCb, hbnd⟩ := hb.2 k
    obtain ⟨Cb', hCb', hbnd'⟩ := hb'.2 k
    refine ⟨Cb + Cb', add_nonneg hCb hCb', fun m ξ => ?_⟩
    have hsub : iteratedDeriv k (fun ξ => b' m ξ - b m ξ) ξ
        = iteratedDeriv k (b' m) ξ - iteratedDeriv k (b m) ξ := by
      change iteratedDeriv k (b' m - b m) ξ = iteratedDeriv k (b' m) ξ - iteratedDeriv k (b m) ξ
      rw [iteratedDeriv_sub ((hsmooth' m).contDiffAt.of_le ENat.LEInfty.out)
        ((hsmooth m).contDiffAt.of_le ENat.LEInfty.out)]
    rw [hsub]
    calc ‖iteratedDeriv k (b' m) ξ - iteratedDeriv k (b m) ξ‖
        ≤ ‖iteratedDeriv k (b' m) ξ‖ + ‖iteratedDeriv k (b m) ξ‖ := norm_sub_le _ _
      _ ≤ Cb' * (2 : ℝ) ^ (m * k) + Cb * (2 : ℝ) ^ (m * k) :=
          add_le_add (hbnd' m ξ) (hbnd m ξ)
      _ = (Cb + Cb') * (2 : ℝ) ^ (m * k) := by ring

/-- **On `L^q` inputs (`q ≥ 1`) the difference square function is the square function of the
difference family.**  Pointwise in `x`, the convolution with `K' - K` is the difference of the two
convolutions (`annulusConv_sub_of_memLp`), which needs the integrability supplied by `f ∈ L^q`,
`q ≥ 1`. -/
lemma annulusDiffSqfun_eq_annulusSqfun_of_memLp (b b' : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hb' : AnnulusSymbolSmooth b')
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (hsmooth' : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b' m))
    {q : ℝ} (hq : 1 ≤ q) (j : ℤ) {f : ℝ → ℂ} (hf : MemLp f (ENNReal.ofReal q) volume) :
    annulusDiffSqfun b b' j f = annulusSqfun (fun m ξ => b' m ξ - b m ξ) j f := by
  funext x
  simp only [annulusDiffSqfun, annulusSqfun]
  congr 1
  refine tsum_congr (fun n => ?_)
  rw [annulusConv_sub_of_memLp b b' hb hb' hsmooth hsmooth' (j + n) hq hf x]

/-- **The `L^q` bound of the difference annulus square function** (the `hqbd` hypothesis of
`annulusDiffSqfun_decay`): for two annulus symbol families `b`, `b'` and every `1 < q < ∞`, the
difference square function `annulusDiffSqfun b b' j f = (∑'_n ‖(K'_{j+n}*f) - (K_{j+n}*f)‖²)^{1/2}`
is `L^q`-bounded by the `L^q` norm of `f`, with a constant uniform in the base scale `j`.

Suggested route: `D := b' - b` is again an `AnnulusSymbolSmooth` family of class `C^∞` (support
inherited, derivative bounds `C_k(b') + C_k(b)`), and `annulusConv_sub_of_memLp` gives
`annulusDiffSqfun b b' j f = annulusSqfun D j f` pointwise for `f ∈ L^q`, so `annulusSquareLp`
applies.  Alternatively use the ℓ² triangle inequality plus `annulusSquareLp` for `b` and `b'`.
(`eLpNorm_rpow_self` in `annulusDiffSqfunL2Gain.lean` converts `(eLpNorm g (ofReal q))^q` into
`∫⁻ g^q` for `ℝ≥0∞`-valued `g`.) -/
theorem annulusDiffSqfunLq (b b' : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hb' : AnnulusSymbolSmooth b')
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (hsmooth' : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b' m))
    {q : ℝ} (hq : 1 < q) :
    ∃ Kq : ℝ, 0 < Kq ∧ ∀ (j : ℤ) (f : ℝ → ℂ),
      MeasureTheory.MemLp f (ENNReal.ofReal q) volume →
      MeasureTheory.eLpNorm (annulusDiffSqfun b b' j f) (ENNReal.ofReal q) volume
        ≤ ENNReal.ofReal Kq * MeasureTheory.eLpNorm f (ENNReal.ofReal q) volume := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hq1 : (1 : ℝ) ≤ q := le_of_lt hq
  have hD : AnnulusSymbolSmooth (fun m ξ => b' m ξ - b m ξ) :=
    annulusSymbolSmooth_subfun b b' hb hb' hsmooth hsmooth'
  have hDsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ => b' m ξ - b m ξ) :=
    fun m => (hsmooth' m).sub (hsmooth m)
  obtain ⟨C, hC, hCbd⟩ := annulusSquareLp (fun m ξ => b' m ξ - b m ξ) hD hDsmooth hq
  refine ⟨C ^ (1 / q), Real.rpow_pos_of_pos hC _, fun j f hf => ?_⟩
  rw [annulusDiffSqfun_eq_annulusSqfun_of_memLp b b' hb hb' hsmooth hsmooth' hq1 j hf]
  exact eLpNorm_le_of_lintegral_rpow_le_eNN hqpos hC.le (hCbd j f hf)
    (aemeasurable_annulusSqfun _ j hf.aestronglyMeasurable.aemeasurable) hf.aestronglyMeasurable

end Work.BourgainPlan.Maximal
