/-
# `Work.KMTAreas.A7.fiberVarSamplingCoreG` -- the `G`-side fibre estimate of §8

## The statement

For `l₁ l₂ k₁ k₂ : ℕ` put `L := max (max l₁ l₂) (max k₁ k₂)`,
`m := mStargF P.natDegree (uScale ρ L) = etaCut kmtEta (-(2·P.natDegree·uScale ρ L))` (the narrow
bump of the `g`-side) and `q := arithQ ρ (max l₁ l₂)`, and let
`Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g` be the core-clipped family
`n ↦ Tle ρ l₂ (varphitildeNt P P.natDegree (⌊a n⌋) k₂ t) g`.  The target bounds the `ℓ^p(ℤ)`-norm
of the `ℓ^p`-average over the residues `n₀ < q` of the variational norms of the *fibres*

  `fiberOpP ρ P l₂ m n₀ v = fun x ↦ ∑' j, arithChar ρ l₂ (P.eval n₀ - j) · cw m j · v (x - j)`

applied to the columns of `Gcl`, by `C · lossWeight 2 ρ l₁ l₂ k₁ k₂` times the variational norm of
the columns themselves.

## The structure of the proof (analysis of this session; read before re-attempting)

**(a) The fibre is a *twist* (not a translate).**  Expanding `arithChar ρ l y = ∑_{α ∈ (ℚ/ℤ)_{≤l}}
e(α y)` and using the multiplicativity of the character, the *kernel* of the fibre is

  `j ↦ arithChar ρ l₂ (P.eval n₀ - j) · cw m j
     = ∑_{α ∈ (ℚ/ℤ)_{≤l₂}} fourier (P.eval n₀) α · (fourier (-j) α · cw m j)`

(`arithChar_mul_cw_eq_sum_fourier` below), and `fourier (-j) α · cw m j` is exactly the `j`-th
coefficient of the Ionescu--Wainger symbol of the *singleton* frequency set `{α}` with symbol
`periodize m` (`Work.KMTPlan.A6.IwKernelArithChar.IwKernelArithChar`, proved).  Hence, on the
spectral windows of the input, the fibre is the twisted Ionescu--Wainger projection

  `fiberOpP ρ P l₂ m n₀ = ∑_{α} e(α·P(n₀)) · M_α`,   `M_α` = the multiplier with symbol `m(· - α)`.

The `M_α` have pairwise disjointly supported symbols as soon as the `m`-windows at distinct
arithmetic frequencies are disjoint, which holds outside a `ρ`-dependent range of `L`:
`Work.KMTAreas.A7.nonAliasing_uScale` (proved, in `fiberOpVarSamplingCore.lean`) supplies the
Ionescu--Wainger non-aliasing statement at the scale `-(2·uScale ρ L)` for every `L` with
`Cρ·2^{ρl} ≤ 2·uScale ρ L`.

**(b) The content is the comparison of the twist with the shift.**  Since `M_α` is the multiplier
of the `α`-piece cut by the `m`-window, and the columns of `Gcl` are band-limited to the arcs
`α + ℝ_{≤ 2^{k₂ - d·Log N}}` (`varphitildeNt_support_le` / `varphitildeNt_periodize_support`), the
twist `T_M := ∑_α e(αM) M_α` differs from the *physical translation* `τ_M` (`(τ_M v)(x) = v(x+M)`)
by the slowly varying envelope errors: on each window, `(T_M v)(x) ≈ (τ_M v)(x)` up to the factor
`m̃(ξ - α) ∈ [0,1]` and the phase error `e(-M(ξ-α))` with `|M(ξ-α)| ≤ q·w'`, where `w'` is the band
of the input and `q = arithQ ρ (max l₁ l₂)` its residue modulus.  The *quantitative Shannon
sampling* input of §8 is precisely `q·w' ≪ 1` (`q` is polynomially small compared with the inverse
band of `Gcl`, the latter being `2^{d·Log N}` with `Log N > splitCut ρ L`); it is what turns the
*arithmetic* twist into the *physical* shift.

**(c) The shift is harmless.**  For every fixed shift `M`, the counting measure on `ℤ` is
invariant under `x ↦ x + M`, so the `ℓ^p(x)`-norm of `x ↦ V^r_n(u_n)(x+M)` equals
`‖V^r_n(u_n)‖_{ℓ^p(x)}`.  Averaging over the residues `n₀ < q` (with the weights `q⁻¹`) and using
the same invariance *term by term* gives

  `‖ (q⁻¹ ∑_{n₀<q} |G(x + s n₀)|^p)^{1/p} ‖_{ℓ^p(x)} = ‖G‖_{ℓ^p}`
  (`lintegral_shift_sum` below, for *arbitrary* shifts `s`)

so that the residue average over the `P(n₀)`-translates of a single function is *exactly* the norm
of that function.  This is the `ℤ`-shadow of the Haar invariance of `τ_{(0,y)}` on `L^p(Ẑ)`.

**(d) The remaining gap (p ≠ 2).**  What is left is the comparison of the *twist* average with the
*shift* average *inside* the variational norm: by Khintchine's inequality for the orthonormal
system `{n₀ ↦ e(α n₀)}_{α}` on `ℤ/q` (the system is orthonormal -- the second-order orthogonality
`q⁻¹∑_{n₀<q} e((α-α')n₀) = [α = α']` holds because `arithQ ρ l` kills every `α` -- and, being a
system of group characters, it is *superorthogonal to all orders*, so Tao's superorthogonality
Khintchine inequality, available in the workspace, applies) one gets the square-function bound

  `(q⁻¹ ∑_{n₀<q} |∑_α e(α n₀) M_α u (x)|^p)^{1/p} ≤ C_p (∑_α |M_α u (x)|^2)^{1/2}`,

and for `p = 2` the two sides are *equal* (orthogonality), giving the target with the loss
`C(ρ)`.  For `p ≠ 2` the passage from the square function `(∑_α |M_α u|^2)^{1/2}` to the sum
`∑_α M_α u` is exactly the **Rubio de Francia multi-interval multiplier theorem**
(`‖(∑_α |f_α|²)^{1/2}‖_{L^p} ≤ C_p ‖∑_α f_α‖_{L^p}` for `2 ≤ p < ∞`, and the dual statement for
`1 < p ≤ 2`, where the `f_α` have spectra in disjoint arcs): it is *false* for an individual sign
pattern bounded by any elementary argument (the elementary bounds lose
`#(ℚ/ℤ)_{≤l₂}^{|1/2-1/p|} = 2^{O(l₂)}`, which no `lossWeight A ρ l₁ l₂ k₁ k₂` with `A` fixed
before `p` can absorb when `ρ` is small and `l₂ ≈ L`), and it is *true* with a constant depending
only on `p`.  This theorem (with its vector-valued/variational form, i.e. for `L^p(ℤ; V^r)`-valued
data) is the missing library chapter of this lemma; its loss is `O(1)` (hence absorbable by
`lossWeight`), whereas every elementary substitute loses a power of `#(ℚ/ℤ)_{≤l₂}`.

**(d') The per-window kernel mass (available).**  `Work.A7.exists_cw_mStargF_tsum_le`
(proved, `Submission/Work/A7/exists_cw_mStargF_tsum_le.lean`) gives
`∑'_j ‖cw (mStargF d u) j‖ ≤ C` with an *absolute* constant, so each singleton window
`M_α` of (a) has a kernel of uniformly bounded `ℓ¹`-mass and is therefore a bounded operator on
`ℓ^p(ℤ)` with a constant independent of `α`, `u` and `ρ`; this is the input of the elementary
per-window Young bound.  (It does *not* suffice for the target: summing it over the `α`
reintroduces the `#(ℚ/ℤ)_{≤l₂}` loss of (d).)

**(e) The periodisation identity.**  `Work.KMTAreas.A7.lintegral_range_shift`
(`fiberOpVarSamplingCore.lean`, proved) is the version of (c) with the shifts `s n₀ = n₀`; the
`G`-side needs the *arbitrary-shift* form, `lintegral_shift_sum` below, because the arithmetic
twist of the `G`-side carries the parameter `P(n₀)` and not the residue `n₀`.
-/
import Mathlib
import Submission.Work.A7.exists_cw_mStargF_tsum_le
import Submission.Work.KMTPlan.A6.IwKernelArithChar
import Submission.Work.Analysis.Fourier.fourierCoeff_mul_summable_series
import Submission.Work.Analysis.Fourier.fourierCoeff_summable_series
import Submission.Work.KMTAreas.A7.KmtProjUniform
import Submission.Work.KMTAreas.A7.toLp_tsum_pi
import Submission.Work.KMTAreas.A7.variationalNorm_mul_le
import Submission.Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm
import Submission.Work.KMTAreas.A7.KmtKernelL1Uniform
import Submission.Work.KMTAreas.A7.IwLqGeneral
import Submission.Work.KMTAreas.A7.iwArithFreqs_card_le
import Submission.Work.KMTAreas.A7.cwEtaCutDiffTsumLe
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

set_option maxHeartbeats 1600000

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

noncomputable section

/-- **The twisted Ionescu--Wainger symbol.**  Same translates of `Φ` as in `iwSymbolSet`, but the
translate at `α` carries the coefficient `e(M α)`: `ξ ↦ ∑_{α ∈ A} e(M α) Φ (ξ - α)`.  It is the
symbol of the fibre `fiberOpP` (see `fiberOpP_eq_twistedIwConv`). -/
noncomputable def iwTwist (A : Finset Freq) (Φ : Freq → ℂ) (M : ℤ) : Freq → ℂ :=
  fun ξ => ∑ α ∈ A, fourier (T := 1) M α * Φ (ξ - α)

/-! ## (a) The kernel of the fibre as a twisted sum of singleton windows -/

/-- **The kernel of the twisted fibre, expanded in the arithmetic frequencies.**  The kernel
`j ↦ arithChar ρ l (P.eval n₀ - j) · cw m j` of `fiberOpP` is the sum over the arithmetic
frequencies `α ∈ (ℚ/ℤ)_{≤l}` of the phase `e(α·P(n₀))` times the singleton-window factor
`e(-α j)·cw m j`, which is the kernel of the Ionescu--Wainger multiplier with frequency set `{α}`
and symbol `periodize m` (see `Work.KMTPlan.A6.IwKernelArithChar`, proved).  This is the algebraic
form of the "twist" decomposition of the fibre: the fibre is the arithmetic twist
`∑_α e(α P(n₀)) M_α` of the `α`-windows of the multiplier `m`. -/
theorem arithChar_mul_cw_eq_sum_fourier (ρ : ℝ) (P : Polynomial ℤ) (l : ℕ) (m : ℝ → ℂ)
    (n₀ j : ℤ) :
    arithChar ρ l (P.eval n₀ - j) * cw m j
      = ∑ α ∈ iwArithFreqs ρ l, fourier (T := 1) (P.eval n₀) α *
          (fourier (T := 1) (-j) α * cw m j) := by
  rw [arithChar, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [show P.eval n₀ - j = P.eval n₀ + (-j) by ring]
  rw [fourier_add]
  ring

/-! ## (c) The arbitrary-shift periodisation identity -/

/-- **The residue average of an arbitrary shift family is the norm of the shifted function.**
For `q ≥ 1`, `p > 0`, any `G : ℤ → ℝ≥0∞` and any shift family `s : ℕ → ℤ`, the mean over
`n₀ < q` of the `p`-th powers of the shifts `x ↦ x + s n₀` has the same integral (for the counting
measure on `ℤ`) as `G^p` itself: each of the `q` shifted copies contributes the same integral,
because `x ↦ x + s n₀` is a bijection of `ℤ`, and the normalising factor `q⁻¹` recombines them.

This is `Work.KMTAreas.A7.lintegral_range_shift` (`fiberOpVarSamplingCore.lean`, proved) with the
residues `n₀` replaced by the *arbitrary* shifts `s n₀`.  The `G`-side needs this generality: its
fibre is the arithmetic twist with parameter `P(n₀)`, so the shifts of the comparison family are
`P(n₀)` and not `n₀`. -/
theorem lintegral_shift_sum (q : ℕ) (hq : 1 ≤ q) (p : ℝ) (G : ℤ → ℝ≥0∞) (s : ℕ → ℤ) :
    ∫⁻ x : ℤ, (q : ℝ≥0∞)⁻¹ * ∑ n₀ ∈ Finset.range q, (G (x + s n₀)) ^ p
        ∂Measure.count
      = ∫⁻ x : ℤ, (G x) ^ p ∂Measure.count := by
  rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count, ENNReal.tsum_mul_left]
  have h1 : (∑' x : ℤ, ∑ n₀ ∈ Finset.range q, (G (x + s n₀)) ^ p)
      = ∑ n₀ ∈ Finset.range q, ∑' x : ℤ, (G (x + s n₀)) ^ p := by
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  rw [h1]
  have h2 : ∀ n₀ ∈ Finset.range q, (∑' x : ℤ, (G (x + s n₀)) ^ p)
      = ∑' x : ℤ, (G x) ^ p := fun n₀ _ =>
    (Equiv.addRight (s n₀)).tsum_eq (fun x : ℤ => (G x) ^ p)
  rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
  · have h1 : (1 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by exact_mod_cast hq
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one h1)
  · exact ENNReal.natCast_ne_top q

/-! ## The target -/

theorem fiberVarSamplingCoreG (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (r : NNReal)
    (hr : 2 < r) :
    ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ C : ℝ, 0 < C ∧
        ∀ (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
          MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal
              (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
                  (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
                    (max (max l₁ l₂) (max k₁ k₂)))) n₀
                  (Work.KMTAreas.A7.Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n) y)) x) p
            MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)) p
                MeasureTheory.Measure.count := by sorry




/-! ## (a') The fibre `fiberOpP` as a translated Ionescu--Wainger convolution

The fibre's kernel `j ↦ (∑_{α ∈ A} e((M - j)α)) · cw m j` (with `A = (ℚ/ℤ)_{l₂}` the exact-height
level, `M = P(n₀)` and `cw m` the continuous Fourier transform of the bump `m`) is exactly the
kernel of the *twisted* Ionescu--Wainger symbol
`iwTwist A (periodize m) M = ∑_{α∈A} e(M α) · m̃(· - α)`.  Since
`e(M ξ)·e(-M(ξ-α)) = e(M α)`, that twisted symbol is the character `e(M·)` times the *plain*
IW symbol `iwSymbolSet A (m̃·e(-M·))`, and multiplying a symbol by `e(M·)` translates its kernel
by `M`.  Hence the fibre is a **translate** of an Ionescu--Wainger convolution:

    fiberOpP ρ P l m n₀ = τ_{-P(n₀)} ∘ iwConv (ℚ/ℤ)_l (m̃ · e(-P(n₀)·)) .

This is the discrete form-1 of KMT §8, proved here rather than asserted; it is the first half of
the route to the target of this file (the second half is the band estimate `(Q)` described in
`NOTES_A7_fiberVarSamplingCoreG_SESSION2.md`). -/

/-- `e(n·)` is additive in its argument on the circle. -/
theorem fourier_add_arg (n : ℤ) (x y : Freq) :
    fourier (T := 1) n (x + y) = fourier (T := 1) n x * fourier (T := 1) n y := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- `e(-M·)(-α) = e(M·)(α)`. -/
theorem fourier_neg_neg' (M : ℤ) (α : Freq) :
    fourier (T := 1) (-M) (-α) = fourier (T := 1) M α := by
  rw [fourier_apply, fourier_apply, smul_neg, neg_smul, neg_neg]

/-- Translating the argument of a symbol by `α` multiplies its Fourier coefficients by the
character `e(-jα)`. -/
theorem fourierCoeff_comp_sub' (M : Freq → ℂ) (α : Freq) (j : ℤ) :
    fourierCoeff (fun ξ : Freq => M (ξ - α)) j
      = fourier (T := 1) (-j) α * fourierCoeff M j := by
  have hL : (∫ t : Freq, fourier (T := 1) (-j) t • M (t - α) ∂circleMeasure)
      = ∫ s : Freq, fourier (T := 1) (-j) (s + α) • M s ∂circleMeasure := by
    rw [← MeasureTheory.integral_add_right_eq_self
      (fun t : Freq => fourier (T := 1) (-j) t • M (t - α)) α]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => by simp)
  have hpt : ∀ s : Freq, fourier (T := 1) (-j) (s + α) • M s
      = fourier (T := 1) (-j) α • (fourier (T := 1) (-j) s • M s) := by
    intro s
    rw [fourier_add_arg, mul_smul, smul_comm]
  show (∫ t : Freq, fourier (T := 1) (-j) t • M (t - α) ∂circleMeasure)
      = fourier (T := 1) (-j) α * (∫ t : Freq, fourier (T := 1) (-j) t • M t ∂circleMeasure)
  rw [hL]
  rw [show (∫ s : Freq, fourier (T := 1) (-j) (s + α) • M s ∂circleMeasure)
      = ∫ s : Freq, fourier (T := 1) (-j) α • (fourier (T := 1) (-j) s • M s)
          ∂circleMeasure from integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_smul, smul_eq_mul]

/-- **The kernel of a twisted IW symbol.**  For a finite set `A` of frequencies and an integrable
symbol `Φ`, `iwKernel (iwTwist A Φ M) j = (∑_{α∈A} e((M-j)α)) · fourierCoeff Φ j`. -/
theorem iwKernel_iwTwist (A : Finset Freq) (Φ : Freq → ℂ) (M j : ℤ)
    (hint : ∀ α ∈ A, Integrable (fun ξ : Freq => Φ (ξ - α)) circleMeasure) :
    Work.Analysis.IWMultiplier.iwKernel (iwTwist A Φ M) j
      = (∑ α ∈ A, fourier (T := 1) (M - j) α) * fourierCoeff Φ j := by
  simp only [Work.Analysis.IWMultiplier.iwKernel]
  change fourierCoeff (fun ξ : Freq => ∑ α ∈ A, fourier (T := 1) M α * Φ (ξ - α)) j
      = (∑ α ∈ A, fourier (T := 1) (M - j) α) * fourierCoeff Φ j
  rw [show (fun ξ : Freq => ∑ α ∈ A, fourier (T := 1) M α * Φ (ξ - α))
      = (∑ α ∈ A, fun ξ : Freq => fourier (T := 1) M α * Φ (ξ - α)) from by
        funext ξ; rw [Finset.sum_apply]]
  rw [fourierCoeff.sum A _ (fun α hα => (hint α hα).const_mul _), Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun α _ =>
    fourierCoeff.const_mul (fun ξ : Freq => Φ (ξ - α)) (fourier (T := 1) M α) j)]
  rw [Finset.sum_congr rfl (fun α _ => by rw [fourierCoeff_comp_sub' Φ α j])]
  rw [Finset.sum_congr rfl (fun α _ => (mul_assoc _ _ _).symm), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  have hchar : fourier (T := 1) M α * fourier (T := 1) (-j) α
      = fourier (T := 1) (M - j) α := by
    rw [fourier_apply, fourier_apply, fourier_apply, ← Circle.coe_mul, ← AddCircle.toCircle_add,
      ← add_zsmul, show M + -j = M - j from by ring]
  rw [hchar]

/-- **The twist is a character times a plain IW symbol**: multiplying the twisted symbol by
`e(-M·)` gives the IW symbol of the modulated bump. -/
theorem iwTwist_eq_fourier_mul (A : Finset Freq) (Φ : Freq → ℂ) (M : ℤ) :
    iwTwist A Φ M
      = fun ξ : Freq =>
          fourier (T := 1) M ξ *
            iwSymbolSet A (fun η : Freq => Φ η * fourier (T := 1) (-M) η) ξ := by
  funext ξ
  simp only [iwTwist, iwSymbolSet_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  have h : fourier (T := 1) M ξ * fourier (T := 1) (-M) (ξ - α)
      = fourier (T := 1) M α := by
    rw [sub_eq_add_neg, fourier_add_arg, ← mul_assoc, ← fourier_add,
      show M + -M = (0:ℤ) from by ring, fourier_zero, one_mul]
    exact fourier_neg_neg' M α
  rw [← h]; ring

/-- **Multiplying a symbol by a character shifts its kernel.** -/
theorem iwKernel_fourier_mul (M : ℤ) (σ : Freq → ℂ) (j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel (fun ξ : Freq => fourier (T := 1) M ξ * σ ξ) j
      = Work.Analysis.IWMultiplier.iwKernel σ (j - M) := by
  simp only [Work.Analysis.IWMultiplier.iwKernel, fourierCoeff]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show fourier (T := 1) (-j) t • (fourier (T := 1) M t * σ t)
      = fourier (T := 1) (-(j - M)) t • σ t
  simp only [smul_eq_mul]
  have h : fourier (T := 1) (-j) t * fourier (T := 1) M t
      = fourier (T := 1) (-(j - M)) t := by
    rw [mul_comm, ← fourier_add]
    congr 1
    ring
  rw [← mul_assoc, h]

/-- `fourierCoeff (periodize φ) = cw φ` for an integrable `φ` (Poisson summation on the circle). -/
theorem fourierCoeff_periodize_eq_cw {φ : ℝ → ℂ} (hφ : Integrable φ) (j : ℤ) :
    fourierCoeff (periodize φ) j = cw φ j := by
  have h := Work.KMTPlan.A6.IwKernelArithChar
    (A := ({(0 : Freq)} : Finset Freq)) hφ j
  have hsym : iwSymbolSet ({(0 : Freq)} : Finset Freq) (periodize φ) = periodize φ := by
    funext ξ; simp [iwSymbolSet]
  have hone : (∑ α ∈ ({(0 : Freq)} : Finset Freq), fourier (T := 1) (-j) α) = 1 := by simp
  rw [hsym, hone, one_mul] at h
  simpa [Work.Analysis.IWMultiplier.iwKernel] using h

/-- **The fibre `fiberOpP` is the convolution with the kernel of the twisted IW symbol.** -/
theorem fiberOpP_eq_twistedIwConv (ρ : ℝ) (P : Polynomial ℤ) (l : ℕ) (m : ℝ → ℂ)
    (hm : Integrable m)
    (hint : ∀ α ∈ iwArithFreqsNew ρ l,
      Integrable (fun ξ : Freq => periodize m (ξ - α)) circleMeasure) (n₀ : ℤ) (v : ℤ → ℂ) :
    fiberOpP ρ P l m n₀ v
      = fun x : ℤ => ∑' j : ℤ,
          Work.Analysis.IWMultiplier.iwKernel
            (iwTwist (iwArithFreqsNew ρ l) (periodize m) (P.eval n₀)) j * v (x - j) := by
  funext x
  simp only [fiberOpP]
  refine tsum_congr (fun j => ?_)
  rw [iwKernel_iwTwist (iwArithFreqsNew ρ l) (periodize m) (P.eval n₀) j hint,
    fourierCoeff_periodize_eq_cw hm j]

/-- Reindexing a translate of an IW convolution. -/
theorem iwConv_sub_eq (A : Finset Freq) (Φ : Freq → ℂ) (v : ℤ → ℂ) (x M : ℤ) :
    Work.Analysis.IWMultiplier.iwConv A Φ v (x - M)
      = ∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel (iwSymbolSet A Φ) (j - M) * v (x - j) := by
  simp only [Work.Analysis.IWMultiplier.iwConv_apply, smul_eq_mul]
  rw [← (Equiv.subRight M).tsum_eq
    (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel (iwSymbolSet A Φ) j * v (x - M - j))]
  exact tsum_congr (fun j => by rw [Equiv.subRight_apply]; congr 1; ring)

/-- **The fibre is a translate of an Ionescu--Wainger convolution** (the discrete `form-1`):

  `fiberOpP ρ P l m n₀ v = fun x ↦ (iwConv (ℚ/ℤ)_l (m̃ · e(-P(n₀)·)) v) (x - P(n₀))`. -/
theorem fiberOpP_eq_translate_iwConv (ρ : ℝ) (P : Polynomial ℤ) (l : ℕ) (m : ℝ → ℂ)
    (hm : Integrable m)
    (hint : ∀ α ∈ iwArithFreqsNew ρ l,
      Integrable (fun ξ : Freq => periodize m (ξ - α)) circleMeasure) (n₀ : ℤ) (v : ℤ → ℂ) :
    fiberOpP ρ P l m n₀ v
      = fun x : ℤ => Work.Analysis.IWMultiplier.iwConv (iwArithFreqsNew ρ l)
          (fun η : Freq => periodize m η * fourier (T := 1) (-(P.eval n₀)) η) v
          (x - P.eval n₀) := by
  funext x
  rw [fiberOpP_eq_twistedIwConv ρ P l m hm hint n₀ v, iwTwist_eq_fourier_mul,
    iwConv_sub_eq]
  exact tsum_congr (fun j => by rw [iwKernel_fourier_mul])

/-! ## (a'') Linearity of the IW symbol and kernel

The identity `iwConv A Φ = Id + iwConv A (Φ - c)` (with `c = 1/#A` the constant whose
`iwSymbolSet` is `1`) is what turns `S_M = iwConv A (m̃·e(-M·))` into `S_M - Id = iwConv A χ`
with `χ = m̃·e(-M·) - 1/#A`; the kernel of that operator is `F(j)·\widehatχ(j)` with
`F(j) = ∑_{α∈A} e(-jα)`.  These are the elementary inputs of that rewriting. -/

/-- The constant `1/#A` has IW symbol `1`: `iwSymbolSet A (fun _ ↦ (card A)⁻¹) = 1`. -/
theorem iwSymbolSet_inv_card (A : Finset Freq) (hA : A.Nonempty) :
    iwSymbolSet A (fun _ : Freq => ((A.card : ℂ))⁻¹) = fun _ => 1 := by
  funext ξ
  rw [iwSymbolSet_apply]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [mul_inv_cancel₀]
  obtain ⟨a, ha⟩ := hA
  exact_mod_cast Finset.card_ne_zero_of_mem ha

/-- The kernel of the constant symbol `1` is the Dirac mass at `0`. -/
theorem iwKernel_one (j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel (fun _ : Freq => (1 : ℂ)) j
      = if j = 0 then 1 else 0 := by
  have hconst : (fun _ : Freq => (1 : ℂ)) = fourier (T := 1) 0 := by
    funext ξ; rw [fourier_zero]
  rw [Work.Analysis.IWMultiplier.iwKernel, hconst, fourierCoeff_fourier]
  rw [Pi.single_apply]

/-- **The IW symbol is additive.** -/
theorem iwSymbolSet_sub (A : Finset Freq) (Φ Ψ : Freq → ℂ) :
    iwSymbolSet A (fun ξ => Φ ξ - Ψ ξ) = iwSymbolSet A Φ - iwSymbolSet A Ψ := by
  have h : (fun ξ : Freq => Φ ξ - Ψ ξ) = Φ + (fun ξ => (-1 : ℂ) * Ψ ξ) := by
    funext ξ
    rw [Pi.add_apply]
    ring
  rw [h, iwSymbolSet_add, iwSymbolSet_const_mul]
  funext ξ
  simp only [Pi.add_apply, Pi.sub_apply]
  ring


/-! ## (b) The loss weight is at least `1`

The target's right-hand side carries the factor `lossWeight 2 ρ l₁ l₂ k₁ k₂`; since it is `≥ 1`
it can absorb any *bounded* error, which is what the band estimate `(Q)` of
`NOTES_A7_fiberVarSamplingCoreG_SESSION2.md` produces. -/

theorem one_le_lmaxR (l₁ l₂ k₁ k₂ : ℕ) : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
  rw [lmaxR, Work.Analysis.EndVar.lmax]
  push_cast
  positivity

theorem one_le_lossWeight (ρ : ℝ) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    1 ≤ lossWeight 2 ρ l₁ l₂ k₁ k₂ := by
  have h0 : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := one_le_lmaxR l₁ l₂ k₁ k₂
  have h1 : (1 : ℝ) ≤ 1 + lmaxR l₁ l₂ k₁ k₂ := by linarith
  have h2 : (1 : ℝ) ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ (2 : ℕ) := one_le_pow₀ h1
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ (2 : ℕ) * (2 : ℝ) ^ (2 * ρ * lmaxR l₁ l₂ k₁ k₂) :=
        mul_le_mul h2 h3 (by norm_num) (le_trans zero_le_one h2)
    _ = lossWeight 2 ρ l₁ l₂ k₁ k₂ := by rw [lossWeight]; norm_num


/-! ## (c) Bookkeeping for the residue average

The target's left-hand side is the `ℓ^p(ℤ)`-norm of `residueLp p q W`, the `ℓ^p`-average over the
residues `n₀ < q` of the variational norms of the fibres.  Two bookkeeping facts are needed to
assemble any proof of it:

* the `ℓ^p`-norm is invariant under translation of the spatial variable (`eLpNorm_comp_add_right`),
  which collapses the *shift* `x ↦ x + P(n₀)` produced by `fiberOpP_eq_translate_iwConv` on the
  right-hand side;
* the `ℓ^p`-norm of the residue average is the `ℓ^p`-average of the `ℓ^p`-norms
  (`eLpNorm_residueLp`) — Tonelli's theorem for `Measure.count` — which turns the `n₀`-average of
  the left-hand side into an average of ordinary norms. -/

theorem eLpNorm_comp_add_right (f : ℤ → ENNReal) (p : ENNReal) (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (s : ℤ) :
    eLpNorm (fun x : ℤ => f (x + s)) p Measure.count = eLpNorm f p Measure.count := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpt]
  refine congrArg (fun z : ENNReal => z ^ (1 / p.toReal)) ?_
  simp only [enorm_eq_self]
  rw [lintegral_count, lintegral_count]
  exact (Equiv.addRight s).tsum_eq (fun x : ℤ => f x ^ p.toReal)

theorem eLpNorm_residueLp (p : ℝ) (hp : 0 < p) (q : ℕ) (A : ℤ → ℕ → ENNReal) :
    eLpNorm (fun x : ℤ => residueLp p q A x) (ENNReal.ofReal p) Measure.count
      = (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
          (eLpNorm (fun x : ℤ => A x n₀) (ENNReal.ofReal p) Measure.count) ^ p)
          ^ (1 / p) := by
  have hpne : (ENNReal.ofReal p) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hpt : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hcancel : (1 / p) * p = 1 := by field_simp
  have hinner : ∀ n₀ : ℕ,
      (eLpNorm (fun x : ℤ => A x n₀) (ENNReal.ofReal p) Measure.count) ^ p
        = ∑' x : ℤ, (A x n₀) ^ p := by
    intro n₀
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hpne hpt, htoReal, lintegral_count]
    simp only [enorm_eq_self, ← ENNReal.rpow_mul, hcancel, ENNReal.rpow_one]
  have hptw : ∀ x : ℤ, (residueLp p q A x) ^ p
      = ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q, (A x n₀) ^ p := by
    intro x
    have h1 : residueLp p q A x
        = (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q, (A x n₀) ^ p)
            ^ (1 / p) := rfl
    rw [h1, ← ENNReal.rpow_mul, hcancel, ENNReal.rpow_one]
  have hLHS : eLpNorm (fun x : ℤ => residueLp p q A x) (ENNReal.ofReal p) Measure.count
      = (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
          ∑' x : ℤ, (A x n₀) ^ p) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hpne hpt, htoReal, lintegral_count]
    simp only [enorm_eq_self]
    rw [tsum_congr hptw, ENNReal.tsum_mul_left,
      Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  rw [hLHS, Finset.sum_congr rfl (fun n₀ _ => hinner n₀)]

theorem residueLp_mono (p : ℝ) (hp : 0 < p) (q : ℕ) {A B : ℤ → ℕ → ENNReal}
    (h : ∀ x n₀, A x n₀ ≤ B x n₀) (x : ℤ) :
    residueLp p q A x ≤ residueLp p q B x := by
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  refine mul_le_mul' le_rfl ?_
  exact Finset.sum_le_sum (fun n₀ _ => ENNReal.rpow_le_rpow (h x n₀) hp.le)


/-- **The residue average is assembled from a single-residue bound.**  If every residue `n₀` obeys
the same `ℓ^p`-bound `B`, then the `ℓ^p`-norm of the residue average obeys it too: by
`eLpNorm_residueLp` the two sides differ by `(q⁻¹ ∑_{n₀<q} B^p)^{1/p} = B`.

This is the final step of the target: it is enough to prove the fibre estimate for a *fixed*
residue `n₀`, uniformly in `n₀`. -/
theorem eLpNorm_residueLp_le_of_single {p : ℝ} (hp : 0 < p) {q : ℕ} (hq : 0 < q)
    {A : ℤ → ℕ → ENNReal} {B : ENNReal}
    (h : ∀ n₀ : ℕ, eLpNorm (fun x : ℤ => A x n₀) (ENNReal.ofReal p) Measure.count ≤ B) :
    eLpNorm (fun x : ℤ => residueLp p q A x) (ENNReal.ofReal p) Measure.count ≤ B := by
  have hcancel : (1 / p) * p = 1 := by field_simp
  have hq0 : (q : ENNReal) ≠ 0 := by exact_mod_cast hq.ne'
  have hqt : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
  have hcancel' : p * (1 / p) = 1 := by field_simp
  have hone : ENNReal.rpow (↑q : ENNReal) (-1) * (↑q : ENNReal) = 1 := by
    have hq1 : (↑q : ENNReal) = ENNReal.rpow (↑q : ENNReal) 1 := (ENNReal.rpow_one _).symm
    calc ENNReal.rpow (↑q : ENNReal) (-1) * (↑q : ENNReal)
        = ENNReal.rpow (↑q : ENNReal) (-1) * ENNReal.rpow (↑q : ENNReal) 1 := by
          nth_rw 2 [hq1]
      _ = ENNReal.rpow (↑q : ENNReal) ((-1) + 1) := (ENNReal.rpow_add (-1) 1 hq0 hqt).symm
      _ = ENNReal.rpow (↑q : ENNReal) 0 := by rw [show (-1 : ℝ) + 1 = 0 from by ring]
      _ = 1 := ENNReal.rpow_zero
  have hB : (ENNReal.rpow (q : ENNReal) (-1) * ∑ _n₀ ∈ Finset.range q, B ^ p) ^ (1 / p)
      = B := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, hone, one_mul,
      ← ENNReal.rpow_mul, hcancel', ENNReal.rpow_one]
  rw [eLpNorm_residueLp p hp q A]
  refine (ENNReal.rpow_le_rpow ?_ (by positivity)).trans hB.le
  exact mul_le_mul' le_rfl
    (Finset.sum_le_sum (fun n₀ _ => ENNReal.rpow_le_rpow (h n₀) hp.le))

/-! ## The elementary (Young) bound for the fibre `fiberOpP`

The fibre `fiberOpP ρ P l m n₀` is `fiberOp ρ l m (P.eval n₀)` (`fiberOpP_eq_fiberOp`), so the
variational Young bound is proved here directly (`variationalNorm_fiberOpP_le`, from the local
Young inequality `variationalNorm_tsum_mul_le_local`).  Bounding the arithmetic character by the
cardinality of the frequency set (`norm_fourierSum_le_card'`) makes the weight uniform in `n₀`
(`variationalNorm_fiberOpP_le_card`), and the residue-average then obeys the same bound
(`eLpNorm_residueLp_fiberOpP_le`).  This is the "small `L`"/"small `#(ℚ/ℤ)_{l₂}`" regime of the
fibre estimate, in which the target holds with a constant depending only on `ρ` (and `p, r`). -/

theorem norm_fourierSum_le_card (ρ : ℝ) (l : ℕ) (y : ℤ) :
    ‖∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) y α‖ ≤ ((iwArithFreqsNew ρ l).card : ℝ) := by
  calc ‖∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) y α‖
      ≤ ∑ α ∈ iwArithFreqsNew ρ l, ‖fourier (T := 1) y α‖ := norm_sum_le _ _
    _ = ∑ _α ∈ iwArithFreqsNew ρ l, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun α _ => ?_)
        rw [fourier_apply]
        exact Circle.norm_coe _
    _ = ((iwArithFreqsNew ρ l).card : ℝ) := by simp

theorem fiberOpP_eq_fiberOp (ρ : ℝ) (P : Polynomial ℤ) (l : ℕ) (m : ℝ → ℂ) (n₀ : ℤ) :
    fiberOpP ρ P l m n₀ = fiberOp ρ l m (P.eval n₀) := rfl

/-- Summability is transported by `WithLp.toLp` on a finite coordinate set. -/
private theorem summable_toLp_pi_aux {ι : Type*} (r : NNReal) (J : ℕ) (v : ι → Fin J → ℂ) :
    Summable (fun j => WithLp.toLp r (v j)) ↔ Summable v := by
  constructor
  · intro hv
    have h := hv.map ((PiLp.continuousLinearEquiv r ℂ (fun _ : Fin J => ℂ)).toContinuousLinearMap)
      (by fun_prop)
    exact h.congr (fun j => rfl)
  · intro hv
    have h := hv.map ((PiLp.continuousLinearEquiv r ℂ (fun _ : Fin J => ℂ)).symm.toContinuousLinearMap)
      (by fun_prop)
    exact h.congr (fun j => rfl)

/-- A single scaled term of the variational `ℓ^r`-sum. -/
private theorem enorm_toLp_smul_sub_le {r : NNReal} (hr : 1 ≤ r) [Fact (1 ≤ (r : ℝ≥0∞))]
    {J : ℕ} (a : ℕ → ℂ) (N : ℕ → ℕ) (hN : Monotone N) (c : ℂ) :
    ‖WithLp.toLp r (fun i : Fin J => c * (a (N (i + 1)) - a (N i)))‖ₑ
      ≤ ‖c‖ₑ * Submission.PointwiseErgodicTheorems.varPart r a := by
  rw [← ofReal_norm]
  refine (ofReal_norm_toLp_mul_le r hr (fun _ : Fin J => c)
    (fun i : Fin J => a (N (i + 1)) - a (N i))).trans ?_
  refine mul_le_mul' (iSup_le fun i => le_rfl) ?_
  exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))

/-- **Young's inequality for the variational norm.**  If every column `j ↦ k j * w j n` is
summable, the variational norm of the family `n ↦ ∑'_j k j * w j n` is bounded by the `ℓ¹`-weighted
sum of the variational norms of the columns. -/
private theorem variationalNorm_tsum_mul_le_local {ι : Type*} (r : NNReal) (hr : 1 ≤ r)
    (k : ι → ℂ) (w : ι → ℕ → ℂ) (hsum : ∀ n, Summable (fun j => k j * w j n)) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => ∑' j, k j * w j n)
      ≤ ∑' j, ‖k j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j) := by
  letI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  by_cases htop : (∑' j, ‖k j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j)) = ⊤
  · rw [htop]
    exact le_top
  · have hfin : (∑' j, ‖k j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j)) < ⊤ :=
      lt_top_iff_ne_top.mpr htop
    have hsup : (⨆ n, ‖∑' j, k j * w j n‖ₑ) ≤ ∑' j, ‖k j‖ₑ * (⨆ n, ‖w j n‖ₑ) := by
      refine iSup_le fun n => ?_
      refine (enorm_tsum_le_tsum_enorm).trans ?_
      refine ENNReal.tsum_le_tsum fun j => ?_
      rw [enorm_mul]
      exact mul_le_mul' le_rfl (le_iSup (fun n => ‖w j n‖ₑ) n)
    have hvar : Submission.PointwiseErgodicTheorems.varPart r (fun n => ∑' j, k j * w j n)
        ≤ ∑' j, ‖k j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j) := by
      refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
      set v : ι → Fin J → ℂ := fun j i => k j * w j (N (i + 1)) - k j * w j (N i) with hv
      have hpoint : ∀ i : Fin J,
          (∑' j, k j * w j (N (i + 1))) - (∑' j, k j * w j (N i)) = ∑' j, v j i := by
        intro i
        refine (Summable.tsum_sub (hsum (N (i + 1))) (hsum (N i))).symm.trans
          (tsum_congr fun j => ?_)
        simp only [hv]
      have hbdd : ∀ j, ‖WithLp.toLp r (v j)‖ₑ
          ≤ ‖k j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j) := by
        intro j
        have hvj : v j = fun i : Fin J => k j * (w j (N (i + 1)) - w j (N i)) := by
          funext i
          simp only [hv]
          ring
        rw [hvj]
        exact enorm_toLp_smul_sub_le hr (w j) N hN (k j)
      have hsu : (∑' j, ‖WithLp.toLp r (v j)‖ₑ) < ⊤ := by
        refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hbdd) ?_
        refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun j => ?_) hfin
        calc ‖k j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j)
            ≤ ‖k j‖ₑ * ((⨆ n, ‖w j n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r (w j)) :=
              mul_le_mul' le_rfl le_add_self
          _ = ‖k j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j) := by
              rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
      have hvS : Summable v :=
        (summable_toLp_pi_aux r J v).mp
          (Summable.of_norm (tsum_enorm_ne_top_iff_summable_norm.mp (ne_of_lt hsu)))
      have hF : (fun i : Fin J => (∑' j, k j * w j (N (i + 1))) - (∑' j, k j * w j (N i)))
          = ∑' j, v j := by
        funext i
        rw [Pi.tsum_apply hvS]
        exact hpoint i
      calc ENNReal.ofReal ‖WithLp.toLp r
            (fun i : Fin J => (∑' j, k j * w j (N (i + 1))) - (∑' j, k j * w j (N i)))‖
          = ‖∑' j, WithLp.toLp r (v j)‖ₑ := by
              rw [hF, toLp_tsum_pi r J v hvS, ofReal_norm]
        _ ≤ ∑' j, ‖WithLp.toLp r (v j)‖ₑ := enorm_tsum_le_tsum_enorm
        _ ≤ ∑' j, ‖k j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j) :=
            ENNReal.tsum_le_tsum hbdd
    have hR : (∑' j, ‖k j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j))
        = (∑' j, ‖k j‖ₑ * (⨆ n, ‖w j n‖ₑ))
          + (∑' j, ‖k j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j)) := by
      rw [← ENNReal.tsum_add]
      exact tsum_congr fun j => by
        simp only [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add, mul_add]
    rw [hR, Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
    exact add_le_add hsup hvar

theorem variationalNorm_fiberOpP_le (ρ : ℝ) (P : Polynomial ℤ) (l : ℕ) (m : ℝ → ℂ) (n₀ : ℤ)
    (u : ℕ → ℤ → ℂ) (r : NNReal) (hr : 1 ≤ r) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => fiberOpP ρ P l m n₀ (u n) x)
      ≤ ∑' j : ℤ, ‖(∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (P.eval n₀ - j) α)
            * cw m j‖ₑ *
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n (x - j)) := by
  simp only [fiberOpP]
  by_cases htop : (∑' j : ℤ,
      ‖(∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (P.eval n₀ - j) α) * cw m j‖ₑ *
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n (x - j))) = ⊤
  · rw [htop]
    exact le_top
  · have hfin : (∑' j : ℤ,
        ‖(∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (P.eval n₀ - j) α) * cw m j‖ₑ *
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n (x - j))) < ⊤ :=
      lt_top_iff_ne_top.mpr htop
    have hsum : ∀ n : ℕ, Summable (fun j : ℤ =>
        ((∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (P.eval n₀ - j) α) * cw m j)
          * u n (x - j)) := by
      intro n
      refine Summable.of_norm (tsum_enorm_ne_top_iff_summable_norm.mp (ne_of_lt ?_))
      refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun j => ?_) hfin
      rw [enorm_mul]
      exact mul_le_mul' le_rfl
        (enorm_apply_le_variationalNorm (r := r) (fun n : ℕ => u n (x - j)) n)
    exact variationalNorm_tsum_mul_le_local r hr
      (fun j : ℤ => (∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (P.eval n₀ - j) α) * cw m j)
      (fun j n => u n (x - j)) hsum
theorem variationalNorm_fiberOpP_le_card (ρ : ℝ) (P : Polynomial ℤ) (l d u : ℕ) (n₀ : ℤ)
    (v : ℕ → ℤ → ℂ) (r : NNReal) (hr : 1 ≤ r) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => fiberOpP ρ P l (mStargF d u) n₀ (v n) x)
      ≤ ((iwArithFreqsNew ρ l).card : ℝ≥0∞) *
          ∑' j : ℤ, ‖cw (mStargF d u) j‖ₑ *
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => v n (x - j)) := by
  refine (variationalNorm_fiberOpP_le ρ P l (mStargF d u) n₀ v r hr x).trans ?_
  conv_rhs => rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum (fun j => ?_)
  have hK : ‖∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (P.eval n₀ - j) α‖ₑ
      ≤ ((iwArithFreqsNew ρ l).card : ℝ≥0∞) := by
    rw [← ofReal_norm]
    simpa using ENNReal.ofReal_le_ofReal
      (norm_fourierSum_le_card ρ l (P.eval n₀ - j))
  calc ‖(∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (P.eval n₀ - j) α)
          * cw (mStargF d u) j‖ₑ *
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => v n (x - j))
      = (‖∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (P.eval n₀ - j) α‖ₑ
            * ‖cw (mStargF d u) j‖ₑ) *
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => v n (x - j)) := by
        rw [enorm_mul]
    _ ≤ ((iwArithFreqsNew ρ l).card : ℝ≥0∞) * (‖cw (mStargF d u) j‖ₑ *
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => v n (x - j))) := by
        refine (mul_le_mul_left (mul_le_mul_left hK _) _).trans (le_of_eq ?_)
        rw [mul_assoc]

/-! ### The `ℝ≥0∞`-valued `eLpNorm` on `ℤ` (local API) -/

private lemma eLpNorm_ennreal_lintegral (p : ℝ) (hp : 0 < p) (F : ℤ → ℝ≥0∞) :
    eLpNorm F (ENNReal.ofReal p) Measure.count
      = (∫⁻ x : ℤ, (F x) ^ p ∂Measure.count) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (ENNReal.ofReal_ne_zero_iff.mpr hp)
    ENNReal.ofReal_ne_top]
  simp only [enorm_eq_self, ENNReal.toReal_ofReal hp.le]

private lemma eLpNorm_ennreal_mono {p : ℝ} (hp : 0 < p) {F G : ℤ → ℝ≥0∞}
    (h : ∀ x : ℤ, F x ≤ G x) :
    eLpNorm F (ENNReal.ofReal p) Measure.count ≤ eLpNorm G (ENNReal.ofReal p) Measure.count := by
  rw [eLpNorm_ennreal_lintegral p hp F, eLpNorm_ennreal_lintegral p hp G]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  exact lintegral_mono (fun x => ENNReal.rpow_le_rpow (h x) hp.le)

private lemma eLpNorm_ennreal_const_mul {p : ℝ} (hp : 0 < p) (c : ℝ≥0∞) (G : ℤ → ℝ≥0∞) :
    eLpNorm (fun x : ℤ => c * G x) (ENNReal.ofReal p) Measure.count
      = c * eLpNorm G (ENNReal.ofReal p) Measure.count := by
  rw [eLpNorm_ennreal_lintegral p hp (fun x : ℤ => c * G x),
    eLpNorm_ennreal_lintegral p hp G]
  rw [show (∫⁻ x : ℤ, (c * G x) ^ p ∂Measure.count)
      = ∫⁻ x : ℤ, c ^ p * (G x) ^ p ∂Measure.count from
    lintegral_congr (fun x => ENNReal.mul_rpow_of_nonneg c (G x) hp.le)]
  rw [lintegral_const_mul (c ^ p) (measurable_of_countable _)]
  rw [ENNReal.mul_rpow_of_nonneg (c ^ p) _ (by positivity)]
  rw [show (c ^ p) ^ (1 / p) = c by
    rw [← ENNReal.rpow_mul, mul_one_div, div_self hp.ne', ENNReal.rpow_one]]

private lemma eLpNorm_ennreal_comp_sub (p : ℝ) (hp : 0 < p) (j : ℤ) (G : ℤ → ℝ≥0∞) :
    eLpNorm (fun x : ℤ => G (x - j)) (ENNReal.ofReal p) Measure.count
      = eLpNorm G (ENNReal.ofReal p) Measure.count := by
  rw [eLpNorm_ennreal_lintegral p hp (fun x : ℤ => G (x - j)),
    eLpNorm_ennreal_lintegral p hp G]
  have h : (∫⁻ x : ℤ, (G (x - j)) ^ p ∂Measure.count)
      = ∫⁻ x : ℤ, (G x) ^ p ∂Measure.count := by
    rw [lintegral_count, lintegral_count]
    have h1 := (Equiv.addRight (-j)).tsum_eq (fun x : ℤ => (G x) ^ p)
    simpa [sub_eq_add_neg, Function.comp_def] using h1
  rw [h]

theorem eLpNorm_residueLp_fiberOpP_le (ρ : ℝ) (P : Polynomial ℤ) (l d u q : ℕ) (hq : 0 < q)
    (p : ℝ) (hp : 1 ≤ p) (v : ℕ → ℤ → ℂ) (r : NNReal) (hr : 1 ≤ r) :
    MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p q
        (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l
            (Work.KMTAreas.A7.mStargF d u) (n₀ : ℤ) (v n) y)) x) (ENNReal.ofReal p)
        MeasureTheory.Measure.count
      ≤ ((iwArithFreqsNew ρ l).card : ℝ≥0∞) *
          (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d u) j‖ₑ) *
          MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => v n x))
            (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  set G : ℤ → ℝ≥0∞ := fun x => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => v n x)
    with hG
  set c : ℤ → ℝ≥0∞ := fun j => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d u) j‖ₑ with hc
  set Z : ℤ → ℝ≥0∞ := fun x => ∑' j : ℤ, c j * G (x - j) with hZ
  -- `eLpNorm Z ≤ (∑ c) * eLpNorm G`
  have hZb : eLpNorm Z (ENNReal.ofReal p) Measure.count
      ≤ (∑' j : ℤ, c j) * eLpNorm G (ENNReal.ofReal p) Measure.count := by
    have h1 : eLpNorm (fun x : ℤ => ∑' j : ℤ, c j * G (x - j)) (ENNReal.ofReal p)
          Measure.count
        ≤ ∑' j : ℤ, eLpNorm (fun x : ℤ => c j * G (x - j))
            (ENNReal.ofReal p) Measure.count :=
      Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm (p := ENNReal.ofReal p) hp1
        (fun j => (measurable_of_countable _).aemeasurable)
    have h2 : (∑' j : ℤ, eLpNorm (fun x : ℤ => c j * G (x - j)) (ENNReal.ofReal p)
            Measure.count)
        = (∑' j : ℤ, c j) * eLpNorm G (ENNReal.ofReal p) Measure.count := by
      have h3 : ∀ j : ℤ, eLpNorm (fun x : ℤ => c j * G (x - j)) (ENNReal.ofReal p) Measure.count
          = c j * eLpNorm G (ENNReal.ofReal p) Measure.count := fun j =>
        (eLpNorm_ennreal_const_mul hp0 (c j) (fun x : ℤ => G (x - j))).trans
          (by rw [eLpNorm_ennreal_comp_sub p hp0 j G])
      rw [tsum_congr h3, ENNReal.tsum_mul_right]
    rw [hZ]
    exact h1.trans (le_of_eq h2)
  -- pointwise bound, uniform in `n₀`
  have hpt : ∀ (n₀ : ℤ) (x : ℤ),
      PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l (Work.KMTAreas.A7.mStargF d u)
          n₀ (v n) x)
        ≤ ((iwArithFreqsNew ρ l).card : ℝ≥0∞) * Z x := by
    intro n₀ x
    rw [hZ, hc]
    exact variationalNorm_fiberOpP_le_card ρ P l d u n₀ v r hr x
  -- single-residue bound
  have hsingle : ∀ n₀ : ℕ, eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l (Work.KMTAreas.A7.mStargF d u)
            (n₀ : ℤ) (v n) x)) (ENNReal.ofReal p) Measure.count
      ≤ ((iwArithFreqsNew ρ l).card : ℝ≥0∞) * eLpNorm Z (ENNReal.ofReal p) Measure.count := by
    intro n₀
    have h1 := eLpNorm_ennreal_mono hp0
      (F := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l (Work.KMTAreas.A7.mStargF d u)
          (n₀ : ℤ) (v n) x))
      (G := fun x : ℤ => ((iwArithFreqsNew ρ l).card : ℝ≥0∞) * Z x)
      (fun x => hpt (n₀ : ℤ) x)
    rwa [eLpNorm_ennreal_const_mul hp0 _ Z] at h1
  have hres := eLpNorm_residueLp_le_of_single (p := p) hp0 (q := q) hq
    (A := fun x n₀ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l (Work.KMTAreas.A7.mStargF d u)
        (n₀ : ℤ) (v n) x))
    (B := ((iwArithFreqsNew ρ l).card : ℝ≥0∞) * eLpNorm Z (ENNReal.ofReal p) Measure.count)
    hsingle
  refine (hres.trans (mul_le_mul_right hZb _)).trans (le_of_eq ?_)
  rw [mul_assoc]

/-! ## The symbol decomposition `Ψ = e(M·)·Σ − E₂` and the kernel of `E₂`

This is the algebraic core of the "twist = shift + small error" comparison of §8.  With
`A` a finite set of arithmetic frequencies, `Φ` a symbol and `M : ℤ`,

  `iwTwist A Φ M = (e(M·))·(iwSymbolSet A Φ) − ∑_{α∈A} (e(M·) − e(Mα))·Φ(·−α)`

(`iwTwist_eq_shift_sub_error`, pure finite-sum algebra), and the `j`-th Fourier coefficient of the
error symbol is `(∑_{α∈A} e((M−j)α))·(\hatΦ(j−M) − \hatΦ(j))` (`fourierCoeff_iwTwist_error`).
Its `ℓ¹`-mass is bounded by `#A` times the `ℓ¹`-mass of `\hatΦ(·−M) − \hatΦ`
(`tsum_enorm_fourierCoeff_iwTwist_error_le`); for `Φ = periodize (mStargF d u)` the latter is
exactly what the per-arc kernel lemma `Work.KMTAreas.A7.iwTwistErrorKernelLe` estimates. -/

theorem norm_fourierSum_le_card' (A : Finset Freq) (y : ℤ) :
    ‖∑ α ∈ A, fourier (T := 1) y α‖ ≤ (A.card : ℝ) := by
  calc ‖∑ α ∈ A, fourier (T := 1) y α‖
      ≤ ∑ α ∈ A, ‖fourier (T := 1) y α‖ := norm_sum_le _ _
    _ = ∑ _α ∈ A, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun α _ => ?_)
        rw [fourier_apply]
        exact Circle.norm_coe _
    _ = (A.card : ℝ) := by simp

theorem iwTwist_eq_shift_sub_error (A : Finset Freq) (Φ : Freq → ℂ) (M : ℤ) :
    iwTwist A Φ M = fun ξ : Freq =>
      fourier (T := 1) M ξ * iwSymbolSet A Φ ξ
        - ∑ α ∈ A, (fourier (T := 1) M ξ - fourier (T := 1) M α) * Φ (ξ - α) := by
  funext ξ
  rw [iwTwist, iwSymbolSet_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  ring

theorem fourierCoeff_iwTwist_error (A : Finset Freq) (Φ : Freq → ℂ) (M j : ℤ)
    (hint : ∀ α ∈ A, Integrable (fun ξ : Freq => Φ (ξ - α)) circleMeasure) :
    fourierCoeff (fun ξ : Freq => ∑ α ∈ A,
        (fourier (T := 1) M ξ - fourier (T := 1) M α) * Φ (ξ - α)) j
      = (∑ α ∈ A, fourier (T := 1) (M - j) α)
          * (fourierCoeff Φ (j - M) - fourierCoeff Φ j) := by
  have hpt : ∀ α : Freq, (fun ξ : Freq =>
        (fourier (T := 1) M ξ - fourier (T := 1) M α) * Φ (ξ - α))
      = (fun ξ : Freq => fourier (T := 1) M ξ * Φ (ξ - α))
        + fun ξ : Freq => (-1 : ℂ) * (fourier (T := 1) M α * Φ (ξ - α)) := by
    intro α; funext ξ; simp only [Pi.add_apply]; ring
  have int₁ : ∀ α ∈ A,
      Integrable (fun ξ : Freq => fourier (T := 1) M ξ * Φ (ξ - α)) circleMeasure := by
    intro α hα
    exact (hint α hα).bdd_mul (c := 1) (f := fun ξ : Freq => fourier (T := 1) M ξ)
      (map_continuous _).aestronglyMeasurable
      (by filter_upwards with ξ; rw [fourier_apply]; exact le_of_eq (Circle.norm_coe _))
  have int₂ : ∀ α ∈ A,
      Integrable (fun ξ : Freq => (-1 : ℂ) * (fourier (T := 1) M α * Φ (ξ - α)))
        circleMeasure := fun α hα => ((hint α hα).const_mul _).const_mul _
  have intf : ∀ α ∈ A, Integrable (fun ξ : Freq =>
      (fourier (T := 1) M ξ - fourier (T := 1) M α) * Φ (ξ - α)) circleMeasure := by
    intro α hα
    rw [hpt α]; exact (int₁ α hα).add (int₂ α hα)
  rw [show (fun ξ : Freq => ∑ α ∈ A,
        (fourier (T := 1) M ξ - fourier (T := 1) M α) * Φ (ξ - α))
      = (∑ α ∈ A, fun ξ : Freq =>
          (fourier (T := 1) M ξ - fourier (T := 1) M α) * Φ (ξ - α)) from by
        funext ξ; rw [Finset.sum_apply]]
  rw [fourierCoeff.sum A _ intf, Finset.sum_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  have hA1 : fourierCoeff (fun ξ : Freq => fourier (T := 1) M ξ * Φ (ξ - α)) j
      = fourier (T := 1) (-(j - M)) α * fourierCoeff Φ (j - M) := by
    rw [show fourierCoeff (fun ξ : Freq => fourier (T := 1) M ξ * Φ (ξ - α)) j
        = Work.Analysis.IWMultiplier.iwKernel
            (fun ξ : Freq => fourier (T := 1) M ξ * Φ (ξ - α)) j from rfl,
      iwKernel_fourier_mul (M := M) (σ := fun ξ : Freq => Φ (ξ - α)) (j := j)]
    exact fourierCoeff_comp_sub' Φ α (j - M)
  have hA2 : fourierCoeff (fun ξ : Freq =>
        (-1 : ℂ) * (fourier (T := 1) M α * Φ (ξ - α))) j
      = (-1 : ℂ) * (fourier (T := 1) M α *
          (fourier (T := 1) (-j) α * fourierCoeff Φ j)) := by
    rw [fourierCoeff.const_mul (fun ξ : Freq => fourier (T := 1) M α * Φ (ξ - α)) (-1) j,
      fourierCoeff.const_mul (fun ξ : Freq => Φ (ξ - α)) (fourier (T := 1) M α) j,
      fourierCoeff_comp_sub' Φ α j]
  rw [hpt α, fourierCoeff.add (int₁ α hα) (int₂ α hα), Pi.add_apply, hA1, hA2]
  rw [
    show fourier (T := 1) (-(j - M)) α = fourier (T := 1) (M - j) α from by
      rw [fourier_apply, fourier_apply]; congr 2; push_cast; ring,
    show (-1 : ℂ) * (fourier (T := 1) M α * (fourier (T := 1) (-j) α * fourierCoeff Φ j))
        = (-1) * ((fourier (T := 1) M α * fourier (T := 1) (-j) α) * fourierCoeff Φ j) from by
      ring,
    show fourier (T := 1) M α * fourier (T := 1) (-j) α = fourier (T := 1) (M - j) α from by
      rw [fourier_apply, fourier_apply, fourier_apply, ← Circle.coe_mul,
        ← AddCircle.toCircle_add, ← add_zsmul, show M + -j = M - j from by ring]]
  ring

theorem tsum_enorm_fourierCoeff_iwTwist_error_le (A : Finset Freq) (Φ : Freq → ℂ) (M : ℤ)
    (hint : ∀ α ∈ A, Integrable (fun ξ : Freq => Φ (ξ - α)) circleMeasure) :
    (∑' j : ℤ, ‖fourierCoeff (fun ξ : Freq => ∑ α ∈ A,
        (fourier (T := 1) M ξ - fourier (T := 1) M α) * Φ (ξ - α)) j‖ₑ)
      ≤ (A.card : ℝ≥0∞) * (∑' j : ℤ,
          ‖fourierCoeff Φ (j - M) - fourierCoeff Φ j‖ₑ) := by
  conv_rhs => rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum (fun j => ?_)
  rw [fourierCoeff_iwTwist_error A Φ M j hint, enorm_mul]
  refine mul_le_mul' ?_ le_rfl
  rw [← ofReal_norm]
  simpa using ENNReal.ofReal_le_ofReal (norm_fourierSum_le_card' A (M - j))

/-- **The residue-averaged fibre estimate for the concrete family `Gcl`.**  This is
`eLpNorm_residueLp_fiberOpP_le` with `v` the `Gcl`-family and the parameters of the target, i.e.
the *target's* left-hand side bounded by `#(ℚ/ℤ)_{l₂} · ∑_j ‖cw m j‖` times the target's
right-hand side without the constant.  In the regime `l₂ ≤ B(ρ)` the cardinality factor is
bounded by a constant depending only on `ρ`, so this is the target there. -/
theorem eLpNorm_residueLp_fiberOpP_Gcl_le (ρ : ℝ) (hρ : 0 < ρ) (P : Polynomial ℤ)
    (d : ℕ) (hd : 1 ≤ d) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (r : NNReal) (hr : 1 ≤ r) :
    MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal
        (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
        (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
            (Work.KMTAreas.A7.mStargF d (Work.KMTAreas.A7.uScale ρ
              (max (max l₁ l₂) (max k₁ k₂)))) n₀
            (Work.KMTAreas.A7.Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n) y)) x) p
      MeasureTheory.Measure.count
    ≤ ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ℝ≥0∞) *
        (∑' j : ℤ, ‖Work.KMTAreas.A7.cw
          (Work.KMTAreas.A7.mStargF d (Work.KMTAreas.A7.uScale ρ
            (max (max l₁ l₂) (max k₁ k₂)))) j‖ₑ) *
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)) p
          MeasureTheory.Measure.count := by
  have hp1 : (1 : ℝ) ≤ p.toReal := by
    have h1 : ((1 : ENNReal)).toReal ≤ p.toReal :=
      ENNReal.toReal_mono (ne_of_lt hptop) (le_of_lt hp)
    simpa using h1
  have hp0 : (0 : ℝ) < p.toReal := lt_of_lt_of_le zero_lt_one hp1
  have hpeq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal (ne_of_lt hptop)
  have h := eLpNorm_residueLp_fiberOpP_le (ρ := ρ) (P := P) (l := l₂) (d := d)
    (u := Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))
    (q := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) (Work.KMTAreas.A7.arithQ_pos ρ _)
    p.toReal hp1 (Work.KMTAreas.A7.Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g) r hr
  rwa [hpeq] at h

/-- Summability of the `cw`-coefficients of `mStargF d u` (quadratic decay). -/
theorem summable_cw_mStargF (d u : ℕ) : Summable (fun j : ℤ => ‖cw (mStargF d u) j‖) := by
  obtain ⟨C, hCpos, hC⟩ := cw_etaCut_decay (-((d : ℤ) * 2 * (u : ℤ)))
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left C)
  rw [norm_kmtKernWeight]
  simpa only [mStargF, div_eq_mul_inv, one_mul] using hC j

/-! ## (f) The twist-vs-shift assembly of the fibre estimate

The paper's `form-1` reduces the fibre estimate to the comparison of the *twist* `fiberOpP` with the
*physical translation* `x ↦ x - P(n₀)`.  The two lemmas below are that reduction in the form in
which the target consumes it:

* `eLpNorm_residueLp_comp_sub`: the exact shift identity — the residue average of a *shifted* single
  function has the same `ℓ^p`-norm as the function (`Work.KMTAreas.A7Hi.residueLpVariationalShift`
  is the family-valued version of the same identity);
* `eLpNorm_residueLp_le_of_shiftError`: if, pointwise in `x` and for every residue `n₀`, the fibre
  is at most the shift plus an error family `E`, then the residue-averaged `ℓ^p`-norm of the fibre
  is at most `‖V^r u‖_{ℓ^p}` *plus* the residue-averaged `ℓ^p`-norm of the error.  With an error of
  relative size `ε` this gives the target with the constant `C(1 + ε)`.

So the whole content of the target is concentrated in the error estimate (the `V^r`-valued
multiplier/Shannon estimate of §8), as it should be.
-/

/-- **The exact shift identity for the residue average.**  For `p > 0`, `q ≥ 1`, any `G : ℤ → ℝ≥0∞`
and any shifts `s : ℕ → ℤ`, the `ℓ^p(ℤ)`-norm of `x ↦ (q⁻¹ ∑_{n₀<q} G (x - s n₀)^p)^{1/p}` is
`‖G‖_{ℓ^p}`: each `x ↦ x - s n₀` is a bijection of `ℤ` (counting measure), and the `n₀`-average of
a constant is the constant. -/
theorem eLpNorm_residueLp_comp_sub {p : ℝ} (hp : 0 < p) {q : ℕ} (hq : 0 < q)
    (G : ℤ → ℝ≥0∞) (s : ℕ → ℤ) :
    eLpNorm (fun x : ℤ => residueLp p q (fun y n₀ => G (y - s n₀)) x)
        (ENNReal.ofReal p) Measure.count
      = eLpNorm G (ENNReal.ofReal p) Measure.count := by
  have hcancel : (1 / p) * p = 1 := by field_simp
  have hqr : ENNReal.rpow (q : ℝ≥0∞) (-1) = (q : ℝ≥0∞)⁻¹ := by
    simpa using ENNReal.rpow_neg (q : ℝ≥0∞) (1 : ℝ)
  have hpt : ∀ x : ℤ, residueLp p q (fun y n₀ => G (y - s n₀)) x ^ p
      = ENNReal.rpow (q : ℝ≥0∞) (-1) * ∑ n₀ ∈ Finset.range q, G (x - s n₀) ^ p := by
    intro x
    have h1 : residueLp p q (fun y n₀ => G (y - s n₀)) x
        = (ENNReal.rpow (q : ℝ≥0∞) (-1)
            * ∑ n₀ ∈ Finset.range q, G (x - s n₀) ^ p) ^ (1 / p) := rfl
    rw [h1, ← ENNReal.rpow_mul, hcancel, ENNReal.rpow_one]
  have hS : ∀ x : ℤ, ENNReal.rpow (q : ℝ≥0∞) (-1) * ∑ n₀ ∈ Finset.range q, G (x - s n₀) ^ p
      = (q : ℝ≥0∞)⁻¹ * ∑ n₀ ∈ Finset.range q, G (x + (-s n₀)) ^ p := by
    intro x
    simp only [hqr, sub_eq_add_neg]
  rw [eLpNorm_ennreal_lintegral p hp (fun x : ℤ => residueLp p q (fun y n₀ => G (y - s n₀)) x),
    eLpNorm_ennreal_lintegral p hp G]
  refine congrArg (fun z : ℝ≥0∞ => z ^ (1 / p)) ?_
  rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt),
      lintegral_congr_ae (Filter.Eventually.of_forall hS)]
  exact lintegral_shift_sum q hq p G (fun n₀ => -s n₀)

/-- **The target in the regime `l₂ ≤ B`.**  For every fixed `B > 0`, the target's estimate holds
(with a constant depending on `ρ`, `p`, `r`, `P` and `B`) for all quadruples of scales with
`l₂ ≤ B`: the two factors `#(ℚ/ℤ)_{l₂}` and `∑_j ‖cw m j‖` are then bounded by constants. -/
theorem fiberVarSamplingCoreG_smallL₂ (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree)
    (r : NNReal) (hr : 2 < r) (B : ℝ) (hB : 0 < B) :
    ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ C : ℝ, 0 < C ∧
        ∀ (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
          (l₂ : ℝ) ≤ B →
          MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal
              (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
                  (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
                    (max (max l₁ l₂) (max k₁ k₂)))) n₀
                  (Work.KMTAreas.A7.Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n) y)) x) p
            MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)) p
                MeasureTheory.Measure.count := by
  intro ρ hρ hρ1 p hp hptop
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.KMTAreas.A7.iwArithFreqs_card_le ρ hρ hρ1
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Work.A7.exists_cw_mStargF_tsum_le P.natDegree (by omega)
  refine ⟨(2 : ℝ) ^ (C₁ * 2 ^ (ρ * B)) * C₂, by positivity,
    fun C₀ a l₁ l₂ k₁ k₂ t g hBl₂ => ?_⟩
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1 : NNReal) ≤ 2) (le_of_lt hr)
  set RHS : ℝ≥0∞ := MeasureTheory.eLpNorm (fun x : ℤ =>
    PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.KMTAreas.A7.Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)) p
    MeasureTheory.Measure.count with hRHS
  have hmain := Work.KMTAreas.A7.eLpNorm_residueLp_fiberOpP_Gcl_le ρ hρ P P.natDegree (by omega)
    C₀ a l₁ l₂ k₁ k₂ t g p hp hptop r hr1
  refine hmain.trans ?_
  -- the two constant factors
  have hcard : ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ℝ≥0∞)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (C₁ * 2 ^ (ρ * B))) := by
    have h₁ : ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ℝ)
        ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (Finset.sdiff_subset : (iwArithFreqs ρ l₂ \ iwArithFreqs ρ (l₂ - 1)) ⊆ iwArithFreqs ρ l₂)
    have h₃ : (2 : ℝ) ^ (C₁ * 2 ^ (ρ * (l₂ : ℝ))) ≤ (2 : ℝ) ^ (C₁ * 2 ^ (ρ * B)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hmono : (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤ (2 : ℝ) ^ (ρ * B) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hρ.le, hBl₂])
      nlinarith [hC₁pos.le, hmono]
    rw [show ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ℝ≥0∞)
        = ENNReal.ofReal (((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ℝ)) from
      (ENNReal.ofReal_natCast _).symm]
    exact ENNReal.ofReal_le_ofReal (le_trans h₁ (le_trans (hC₁ l₂) h₃))
  have hcw : (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree
        (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) j‖ₑ)
      ≤ ENNReal.ofReal C₂ := by
    have h1 : ENNReal.ofReal (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF
          P.natDegree (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) j‖)
        ≤ ENNReal.ofReal C₂ := ENNReal.ofReal_le_ofReal (hC₂ _)
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _)
      (Work.KMTAreas.A7.summable_cw_mStargF P.natDegree _)] at h1
    simpa only [ofReal_norm] using h1
  have hloss : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Work.KMTAreas.A7.one_le_lossWeight ρ hρ.le l₁ l₂ k₁ k₂)
  calc ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ℝ≥0∞) *
        (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree
          (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) j‖ₑ) * RHS
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (C₁ * 2 ^ (ρ * B))) * ENNReal.ofReal C₂ * RHS := by
        gcongr
    _ = ENNReal.ofReal ((2 : ℝ) ^ (C₁ * 2 ^ (ρ * B)) * C₂) * RHS := by
        rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (((2 : ℝ) ^ (C₁ * 2 ^ (ρ * B)) * C₂)
          * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂) * RHS := by
        refine mul_le_mul_left ?_ _
        refine ENNReal.ofReal_le_ofReal ?_
        refine le_mul_of_one_le_right (mul_nonneg (by positivity) hC₂pos.le) ?_
        exact Work.KMTAreas.A7.one_le_lossWeight ρ hρ.le l₁ l₂ k₁ k₂
    _ = ENNReal.ofReal ((2 : ℝ) ^ (C₁ * 2 ^ (ρ * B)) * C₂
          * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂) * RHS := by
        rw [mul_assoc]


/-- The scale `l₂` is at most `Lnat`. -/
theorem le_Lnat_l₂ (l₁ l₂ k₁ k₂ : ℕ) : l₂ ≤ Lnat l₁ l₂ k₁ k₂ := by
  unfold Lnat; omega

/-- **The target in the regime `Lnat l₁ l₂ k₁ k₂ ≤ B`.**  This is
`fiberVarSamplingCoreG_smallL₂` with the sharper hypothesis `Lnat ≤ B` (which implies `l₂ ≤ B`
by `le_Lnat_l₂`): the crude Young/kernel bound `eLpNorm_residueLp_fiberOpP_Gcl_le` loses the
cardinality `#(iwArithFreqsNew ρ l₂)` and the kernel mass `∑_j ‖cw m j‖`, and both are bounded by
a `ρ`-dependent constant once `l₂ ≤ B` (`A7/iwArithFreqs_card_le`,
`Work.A7.exists_cw_mStargF_tsum_le`).  Hence the whole content of the target sits in the
*large-scale* regime `Lnat > B`, where the `lossWeight` cannot be dispensed with. -/
theorem fiberVarSamplingCoreG_smallLnat (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree)
    (r : NNReal) (hr : 2 < r) (B : ℝ) (hB : 0 < B) :
    ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ C : ℝ, 0 < C ∧
        ∀ (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
          (Work.KMTAreas.A7.Lnat l₁ l₂ k₁ k₂ : ℝ) ≤ B →
          MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal
              (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
                  (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
                    (max (max l₁ l₂) (max k₁ k₂)))) n₀
                  (Work.KMTAreas.A7.Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n) y)) x) p
            MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)) p
                MeasureTheory.Measure.count := by
  intro ρ hρ hρ1 p hp hptop
  obtain ⟨C, hC, h⟩ :=
    Work.KMTAreas.A7.fiberVarSamplingCoreG_smallL₂ P hdeg r hr B hB ρ hρ hρ1 p hp hptop
  refine ⟨C, hC, ?_⟩
  intro C₀ a l₁ l₂ k₁ k₂ t g hBL
  exact h C₀ a l₁ l₂ k₁ k₂ t g
    (le_trans (by exact_mod_cast le_Lnat_l₂ l₁ l₂ k₁ k₂) hBL)


/-- The left-hand side of the target, at a fixed residue `n₀`: the variational norm over the
scale index `n` of the fibre `fiberOpP` applied to the concrete `Gcl`-family. -/
noncomputable def fiberLHS (ρ : ℝ) (P : Polynomial ℤ) (l₂ C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (n₀ : ℕ) (r : NNReal) (x : ℤ) : ENNReal :=
  PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ =>
      Work.KMTAreas.A7.fiberOpP ρ P l₂
        (Work.KMTAreas.A7.mStargF P.natDegree
          (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
        n₀
        (Work.KMTAreas.A7.Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n) x)

/-- The right-hand side of the target (without the constant), i.e. the variational norm over `n` of
the concrete `Gcl`-family. -/
noncomputable def fiberRHS (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (r : NNReal) (x : ℤ) : ENNReal :=
  PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => Work.KMTAreas.A7.Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)

/-- **The target follows from the per-residue fibre estimate with the shift on the right.**

The hypothesis is the *cut/gate* form of the fibre bound: for every residue `n₀` (uniformly — for
every `n₀ : ℕ`, not only `n₀ < q`; this is the form in which the abstract cut bound
`Work.KMTAreas.A7Hi.FiberOpCutVarBound` is available, since it is uniform in the rephasing
parameter `M`) the fibre applied to the concrete family `Gcl` is bounded by `C·lossWeight` times
the `ℓ^p`-norm of the *shifted* reference family `Gcl (· - P(n₀))`.

The reduction itself is elementary and uses only PROVED lemmas: the shift identity
`eLpNorm_comp_add_right` (translation invariance of the counting measure) makes the right-hand side
of every residue the *same* number `‖Vʳ_n(Gcl n)‖_{ℓ^p}`, so `eLpNorm_residueLp_le_of_single`
(a Tonelli/Minkowski identity for `residueLp`) turns the uniform per-residue bound into the
residue-averaged bound.  Hence the whole content of the target is the per-residue cut bound — the
paper's `form-1` plus the Shannon/multiplier comparison; see
`NOTES_A7_fiberVarSamplingCoreG_SESSION7.md` §2–§3. -/
theorem fiberVarSamplingCoreG_of_perResidue (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree)
    (r : NNReal) (hr : 2 < r)
    (h : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ C : ℝ, 0 < C ∧
        ∀ (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (n₀ : ℕ),
          MeasureTheory.eLpNorm (fiberLHS ρ P l₂ C₀ a l₁ k₁ k₂ t g n₀ r) p
              MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm
                  (fun x : ℤ => fiberRHS ρ P C₀ a l₁ l₂ k₁ k₂ t g r (x - P.eval (n₀ : ℤ)))
                  p MeasureTheory.Measure.count) :
    ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ C : ℝ, 0 < C ∧
        ∀ (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
          MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal
              (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (fun y n₀ => fiberLHS ρ P l₂ C₀ a l₁ k₁ k₂ t g n₀ r y) x) p
            MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm (fiberRHS ρ P C₀ a l₁ l₂ k₁ k₂ t g r) p
                MeasureTheory.Measure.count := by
  intro ρ hρ hρ1 p hp hptop
  obtain ⟨C, hC, hper⟩ := h ρ hρ hρ1 p hp hptop
  refine ⟨C, hC, ?_⟩
  intro C₀ a l₁ l₂ k₁ k₂ t g
  have hpne : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hptop' : p ≠ ⊤ := ne_of_lt hptop
  have hpR : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hpne hptop'
  have hq : 0 < Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) := Work.KMTAreas.A7.arithQ_pos ρ _
  have hof : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hptop'
  have h0 : ENNReal.ofReal p.toReal ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hpR
  have htop : ENNReal.ofReal p.toReal ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the per-residue bound at the exponent `ofReal p.toReal`, with the shift removed by the
  -- translation invariance of the counting measure (`eLpNorm_comp_add_right`)
  have hsingle : ∀ n₀ : ℕ, MeasureTheory.eLpNorm
      (fun x : ℤ => fiberLHS ρ P l₂ C₀ a l₁ k₁ k₂ t g n₀ r x)
      (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm (fiberRHS ρ P C₀ a l₁ l₂ k₁ k₂ t g r)
            (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count := by
    intro n₀
    have h1 := hof.symm ▸ hper C₀ a l₁ l₂ k₁ k₂ t g n₀
    simp only [sub_eq_add_neg] at h1
    rw [Work.KMTAreas.A7.eLpNorm_comp_add_right (fiberRHS ρ P C₀ a l₁ l₂ k₁ k₂ t g r)
      (ENNReal.ofReal p.toReal) h0 htop (-(P.eval (n₀ : ℤ)))] at h1
    exact h1
  have hmain := Work.KMTAreas.A7.eLpNorm_residueLp_le_of_single (p := p.toReal) hpR hq
    (A := fun x n₀ => fiberLHS ρ P l₂ C₀ a l₁ k₁ k₂ t g n₀ r x)
    (B := ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂) *
      MeasureTheory.eLpNorm (fiberRHS ρ P C₀ a l₁ l₂ k₁ k₂ t g r)
        (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count) hsingle
  have hA : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal
        (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
        (fun y n₀ => fiberLHS ρ P l₂ C₀ a l₁ k₁ k₂ t g n₀ r y) x)
        (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal
        (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
        (fun y n₀ => fiberLHS ρ P l₂ C₀ a l₁ k₁ k₂ t g n₀ r y) x) p
        MeasureTheory.Measure.count := by rw [hof]
  have hB : ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂) *
        MeasureTheory.eLpNorm (fiberRHS ρ P C₀ a l₁ l₂ k₁ k₂ t g r)
          (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
      = ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂) *
        MeasureTheory.eLpNorm (fiberRHS ρ P C₀ a l₁ l₂ k₁ k₂ t g r) p
          MeasureTheory.Measure.count := by rw [hof]
  exact le_of_eq_of_le hA.symm (le_of_le_of_eq hmain hB)



/-! ## The kernel mass of the packet-matched gated Ionescu--Wainger multiplier

The correction of the gate decomposition (`Work.KMTAreas.A7.iwConv_gate_comp_v2`) is the
Ionescu--Wainger multiplier with profile `periodize ψ`, `ψ = etaCut kmtEta k · (1 − e(−M·))`, a bump
of width `2^k` and height `≤ 2π|M|2^k`.  The lemmas below give the `ℓ¹`-mass of its kernel, so that
Young's inequality for the variational norm
(`Work.KMTAreas.A7.variationalNorm_tsum_conv`) bounds the correction by that constant.  See
`NOTES_A7_fiberVarSamplingCoreG_SESSION7.md` §7–§9. -/

/-- `ee x = e^{2πix}` has unit modulus. -/
theorem enorm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  rw [ee, show (2 : ℂ) * ↑Real.pi * Complex.I * ↑x = ↑(2 * Real.pi * x) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `ee` is continuous.  (Integration note, owner of area A6, H61: this copy is `private`, as
recommended by `A7/NOTES_to_H61.md` — the public name is already provided by
`Submission/Work/KMTAreas/A7/theta_double_cw.lean`, and modules whose closure contains both files,
e.g. `A6/PieceBoundedH/heightZeroBound` and hence A6's low case, could not be built.) -/
private theorem continuous_ee : Continuous (fun x : ℝ => ee x) := by
  unfold ee
  fun_prop

/-- `ee` is multiplicative in the additive structure of `ℝ`. -/
theorem ee_add' (a b : ℝ) : ee (a + b) = ee a * ee b := by
  unfold ee
  rw [show (2 : ℂ) * ↑Real.pi * Complex.I * ↑(a + b)
      = (2 : ℂ) * ↑Real.pi * Complex.I * ↑a + (2 : ℂ) * ↑Real.pi * Complex.I * ↑b by
    push_cast; ring]
  exact Complex.exp_add _ _

/-- The product of the rescaled cutoff with a character is integrable. -/
theorem integrable_etaCut_mul_ee (k j : ℤ) :
    Integrable (fun θ : ℝ =>
      Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ * ee (-(j : ℝ) * θ)) :=
  ((Work.KMTAreas.A7.contDiff_etaCut k).continuous.mul
      (continuous_ee.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
    ((Work.KMTAreas.A7.hasCompactSupport_etaCut k).mul_right)

/-- The gated small modulation `etaCut kmtEta k · (1 − e(−M·))` is integrable. -/
theorem integrable_etaCut_one_sub_ee (k M : ℤ) :
    Integrable (fun θ : ℝ => Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ
        * (1 - ee (-(M : ℝ) * θ))) := by
  have hcont : Continuous (fun θ : ℝ =>
      Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ
        * (1 - ee (-(M : ℝ) * θ))) :=
    ((Work.KMTAreas.A7.contDiff_etaCut k).continuous).mul
      (continuous_const.sub (continuous_ee.comp (continuous_const.mul continuous_id)))
  exact hcont.integrable_of_hasCompactSupport
    (Work.KMTAreas.A7.hasCompactSupport_etaCut k).mul_right

/-- **The Fourier coefficients of the gated small modulation.**  For the rescaled cutoff
`η := etaCut kmtEta k`, `cw (η · (1 − e(−M·))) j = cw η j − cw η (j + M)`. -/
theorem cw_etaCut_one_sub_ee (k M j : ℤ) :
    cw (fun θ : ℝ => Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ
        * (1 - ee (-(M : ℝ) * θ))) j
      = cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) j
        - cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) (j + M) := by
  have hpt : ∀ θ : ℝ, (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ
        * (1 - ee (-(M : ℝ) * θ))) * ee (-(j : ℝ) * θ)
      = Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ * ee (-(j : ℝ) * θ)
        - Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ
            * ee (-(((j + M : ℤ)) : ℝ) * θ) := by
    intro θ
    have hee : ee (-(M : ℝ) * θ) * ee (-(j : ℝ) * θ) = ee (-(((j + M : ℤ)) : ℝ) * θ) := by
      rw [← ee_add']
      congr 1
      push_cast
      ring
    calc (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ
            * (1 - ee (-(M : ℝ) * θ))) * ee (-(j : ℝ) * θ)
        = Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ * ee (-(j : ℝ) * θ)
          - (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ
              * ee (-(M : ℝ) * θ)) * ee (-(j : ℝ) * θ) := by ring
      _ = Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ * ee (-(j : ℝ) * θ)
          - Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ
              * ee (-(((j + M : ℤ)) : ℝ) * θ) := by rw [mul_assoc, hee]
  simp only [cw]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact integral_sub (integrable_etaCut_mul_ee k j) (integrable_etaCut_mul_ee k (j + M))

/-- Summability of the coefficients of the rescaled cutoff (quadratic decay,
`Work.KMTAreas.A7.cw_etaCut_decay`). -/
theorem summable_cw_etaCut_local (k : ℤ) :
    Summable (fun j : ℤ =>
      ‖cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) j‖) := by
  obtain ⟨C, _hCpos, hC⟩ := Work.KMTAreas.A7.cw_etaCut_decay k
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left C)
  rw [norm_kmtKernWeight]
  simpa only [div_eq_mul_inv, one_mul] using hC j

/-- Summability of the coefficients of the gated small modulation. -/
theorem summable_cw_etaCut_one_sub_ee (k M : ℤ) :
    Summable (fun j : ℤ => ‖cw (fun θ : ℝ =>
      Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ
        * (1 - ee (-(M : ℝ) * θ))) j‖) := by
  have hshift : Summable (fun j : ℤ => ‖cw
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) (j + M)‖) :=
    (Equiv.addRight M).summable_iff.mpr (summable_cw_etaCut_local k)
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    ((summable_cw_etaCut_local k).add hshift)
  rw [cw_etaCut_one_sub_ee k M j]
  exact norm_sub_le _ _

/-- **The pointwise kernel bound.**  The `j`-th kernel coefficient of `iwConv A (periodize ψ)` is
`(∑_{α∈A} fourier (−j) α) · cw ψ j` (`iwKernel_iwTwist` with `M = 0`, the identity
`iwSymbolSet A Ψ = iwTwist A Ψ 0`, and `fourierCoeff_periodize_eq_cw`), so its norm is at most
`#A · ‖cw ψ j‖`. -/
theorem enorm_iwKernel_le_card_mul_cw {A : Finset Freq} {ψ : ℝ → ℂ}
    (hψ : Integrable ψ)
    (hint : ∀ α ∈ A, Integrable (fun ξ : Freq => periodize ψ (ξ - α)) circleMeasure) (j : ℤ) :
    ‖Work.Analysis.IWMultiplier.iwKernel (iwSymbolSet A (periodize ψ)) j‖
      ≤ (A.card : ℝ) * ‖cw ψ j‖ := by
  have hsym : iwSymbolSet A (periodize ψ) = iwTwist A (periodize ψ) 0 := by
    funext ξ
    simp only [iwSymbolSet_apply, iwTwist]
    exact Finset.sum_congr rfl (fun α _ => by rw [fourier_zero, one_mul])
  have hcoeff : Work.Analysis.IWMultiplier.iwKernel (iwSymbolSet A (periodize ψ)) j
      = (∑ α ∈ A, fourier (T := 1) (-j) α) * cw ψ j := by
    rw [hsym, iwKernel_iwTwist A (periodize ψ) 0 j hint, fourierCoeff_periodize_eq_cw hψ j]
    simp only [zero_sub]
  rw [hcoeff, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_fourierSum_le_card' A (-j)) (norm_nonneg _)

/-- **Summability of the kernel of an Ionescu--Wainger multiplier.** -/
theorem summable_iwKernel_of_summable_cw {A : Finset Freq} {ψ : ℝ → ℂ}
    (hψ : Integrable ψ)
    (hint : ∀ α ∈ A, Integrable (fun ξ : Freq => periodize ψ (ξ - α)) circleMeasure)
    (hsum : Summable (fun j : ℤ => ‖cw ψ j‖)) :
    Summable (fun j : ℤ =>
      ‖Work.Analysis.IWMultiplier.iwKernel (iwSymbolSet A (periodize ψ)) j‖) :=
  Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => enorm_iwKernel_le_card_mul_cw hψ hint j) (hsum.mul_left _)

/-- **The kernel mass of an Ionescu--Wainger multiplier, at the level of the profile's Fourier
coefficients.** -/
theorem tsum_iwKernel_le_card_mul_cw {A : Finset Freq} {ψ : ℝ → ℂ}
    (hψ : Integrable ψ)
    (hint : ∀ α ∈ A, Integrable (fun ξ : Freq => periodize ψ (ξ - α)) circleMeasure)
    (hsum : Summable (fun j : ℤ => ‖cw ψ j‖)) :
    (∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel (iwSymbolSet A (periodize ψ)) j‖)
      ≤ (A.card : ℝ) * (∑' j : ℤ, ‖cw ψ j‖) := by
  have hsum' : Summable (fun j : ℤ => (A.card : ℝ) * ‖cw ψ j‖) := hsum.mul_left _
  calc (∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel (iwSymbolSet A (periodize ψ)) j‖)
      ≤ ∑' j : ℤ, (A.card : ℝ) * ‖cw ψ j‖ :=
        Summable.tsum_le_tsum (fun j => enorm_iwKernel_le_card_mul_cw hψ hint j)
          (summable_iwKernel_of_summable_cw hψ hint hsum) hsum'
    _ = (A.card : ℝ) * (∑' j : ℤ, ‖cw ψ j‖) := tsum_mul_left

end

end Work.KMTAreas.A7
