/-
# The func-calculus identity of the §5 pieces: the requested form is FALSE, the corrected form
# (bounded `f`) is proved below.

## The statement as requested -- REFUTED

    theorem FpieceEqTm {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l s N : ℕ) (f : ℤ → ℂ) :
        Work.Analysis.EndVar.Fpiece (Work.KMTContract.kmtPj ρ) 0 l (s : ℤ) N f
          = Work.KMTAreas.A7.Tm ρ l (Work.KMTAreas.A7.pieceSymF s N) f

is **false** as written, i.e. for arbitrary `f : ℤ → ℂ`.  The intended proof (recorded in
`Submission/Work/KMTAreas/A7/NOTES.md`: "the identity is the additivity of `iwSymbolSet` in its
frequency set", with `hTm_add`/`hTm_smul` "from the linearity of `tsum`") only establishes a
*pointwise* relation between the summands, and that is not enough:

* both sides are defined through *unconditional* `tsum`s,
  `iwConv A Φ f n = ∑' j, iwKernel (iwSymbolSet A Φ) j • f (n - j)`, and the Mathlib `tsum` is
  `if Summable ... then ... else 0` (`tsum_eq_zero_of_not_summable`);
* the left side is a difference of **four** such `tsum`s (`piExact` is defined as the difference of
  the projections `Π_{≤l}` and `Π_{≤l-1}`), the right side is a **single** `tsum`;
* symbol algebra gives `κ₁ = κ₂ + κ₃` etc. *pointwise* for the five kernels, but `tsum` is not
  additive on non-summable families, so the "junk zeros" `0` produced by the non-summable families
  need not be consistent between the two sides.

For unbounded `f` the families `j ↦ κ(j) • f (n - j)` are genuinely non-summable, and the two sides
disagree.  Explicitly, take `ρ ∈ (0,1]`, `l = 2`, `s = 1` and `N ≥ 16` (so that
`a := 1 - logN N ≤ -3`, `b := a - 1`), and let `f` be such that `z j := f (0 - j)` is supported on
the *odd* integers (plus the single point `j = 0`) with `|z j|` growing along three infinite subsets
of the odd integers on which respectively `ĉ_a(j) := 2^a ηhat(j 2^a)`, `ĉ_b(j) := 2^b ηhat(j 2^b)`
and `ĉ_a(j) - ĉ_b(j)` do not vanish, where `ηhat(y) := ∫_ℝ kmtEta(u) e(-y u) du`.  (The `j`-th
Fourier coefficient of `periodize (etaCut kmtEta c)` is `ĉ_c(j) = 2^c ηhat(j 2^c)`.)

Why those three sets are infinite (all but finitely many odd coefficients cannot vanish):
`g_c := periodize (etaCut kmtEta c)` vanishes on the interval `J_c := (2^c, 1 - 2^c)` (as
`etaCut kmtEta c` is supported in `[-2^c, 2^c]`), while `g_c(0) = kmtEta(0) = 1 ≠ 0 = g_c(1/2)`, so
`g_c` is not `1/2`-periodic.  Write `g_c = h + p` with `h(x) := (g_c(x) + g_c(x+1/2))/2` (which is
`1/2`-periodic) and `p(x) := (g_c(x) - g_c(x+1/2))/2` (the "odd" part): `p` is a trigonometric
polynomial exactly when only finitely many odd Fourier coefficients of `g_c` are nonzero.  If that
happened, then `h = -p` on `J_c`, so by the `1/2`-periodicity of `h` we get `p(x) = p(x - 1/2)` for
`x ∈ J_c + 1/2`; hence `x ↦ p(x) - p(x-1/2)` is a trigonometric polynomial vanishing on the
nondegenerate interval `J_c ∩ (J_c + 1/2)` (nonempty for `c ≤ -3`), so it vanishes identically, and
a trigonometric polynomial which is `1/2`-periodic has only even frequencies, giving `p = 0`.  Then
`g_c = h` would be `1/2`-periodic, contradiction.

With `(ℚ/ℤ)_{≤1} = {0, 1/2}` and `(ℚ/ℤ)_{≤2} = {0, 1/2, 1/3, 2/3, 1/4, 3/4}` one computes
`σ_{≤1}(j) := ∑_{α ∈ (ℚ/ℤ)_{≤1}} e(-j α) = 1 + (-1)^j` (vanishing exactly for odd `j`) and
`σ_{≤2}(j) = σ_{≤1}(j) + 2 cos(2πj/3) = 2 cos(2πj/3) ∈ {-1, 2}` for odd `j`, while
`σ_{≤2\≤1}(j) = σ_{≤2}(j) - σ_{≤1}(j) = σ_{≤2}(j)` for odd `j`.  On the odd `j` the four kernels of
the left side and the kernel of the right side are therefore
`ĉ_a σ_{≤2}`, `ĉ_a σ_{≤1} = 0`, `ĉ_b σ_{≤2}`, `ĉ_b σ_{≤1} = 0` and
`(ĉ_a - ĉ_b) σ_{≤2\≤1} = (ĉ_a - ĉ_b) σ_{≤2}`, so with the above choice of `z`:
* the first, third and fifth families are non-summable, hence their `tsum`s are `0`;
* the second and fourth families are supported in `{0}`, hence their `tsum`s are the genuine values
  `β(0) z 0 = 2 ηhat(0) 2^a z 0` and `δ(0) z 0 = 2 ηhat(0) 2^b z 0` (the `0`-th coefficient of
  `etaCut kmtEta c` is `2^c ηhat(0) = 2^c ∫ kmtEta ≠ 0`).
Hence the left side equals `2 ηhat(0) z 0 (2^b - 2^a) ≠ 0` while the right side is `0`.

(A machine-checked counterexample would need the "all but finitely many odd Fourier coefficients of
`periodize (etaCut kmtEta c)` cannot vanish" fact above, i.e. the trigonometric-polynomial argument;
that is why the refutation is documented here and not a Lean term.)

## The corrected statement -- true, and proved below

The identity becomes correct as soon as the five families are *summable*, e.g. when `f` is bounded:
every kernel occurring in it lies in `ℓ¹(ℤ)` by `Work.KMTContract.kmtKernel_decay` (the cutoff is
smooth with compact support, so the kernel decays like `j^{-2}`), and a bounded function times an
`ℓ¹` kernel is summable.  Boundedness is automatic in the §5 assembly, whose inputs lie in `ℓ^{p}`,
`p < ∞`.

The corrected statement is `FpieceEqTm_of_bounded` at the end of this file; its proof uses only
*summability* (`Summable.tsum_sub`) and the pointwise symbol algebra (`iwSymbolSet_sdiff`,
`periodize_sub_etaCut`, `iwKernel_iwSymbolSet_sdiff/_sub`).

**The same repair is needed for every other unconditional `Tm` identity of the §5 assembly.**
`hTm_add`/`hTm_smul` (linearity of `Tm` in the symbol, needed by the Rademacher--Menshov step
`smallScale_variational_le_Vr`) hold only with the *same* boundedness hypothesis on `f`: for bounded
`f` one has `periodize (φ + ψ) = periodize φ + periodize ψ` (from `Summable.tsum_add`, needing
`∀ x, Summable (fun j => φ (x + j))` and the same for `ψ` -- automatic for the `etaCut`-type symbols
used here), the additive/scalar counterparts of `iwConv_sub_of_bounded` below, and hence
`Tm ρ l (φ + ψ) f = Tm ρ l φ f + Tm ρ l ψ f` and `Tm ρ l (fun ξ => c * φ ξ) f = c • Tm ρ l φ f`;
the unconditional forms over all `f` are false for the same reason as `FpieceEqTm`.

## Contents

* `periodize_sub_etaCut`, `memLp_periodize_etaCut` -- the periodisation of the rescaled cutoffs;
* `fourierCoeff_sub'`, `iwKernel_iwSymbolSet_sdiff`, `iwKernel_iwSymbolSet_sub` -- linearity of the
  kernels in the frequency set and in the symbol;
* `summable_iwKernel_etaCut`, `summable_iwKernel_diffFreqs`, `summable_mul_of_bounded` -- the `ℓ¹`
  facts;
* `iwConv_sub_of_bounded`, `iwConv_add_of_bounded`, `iwConv_const_mul` -- linearity of `iwConv` in
  the symbol (bounded input; the scalar form holds unconditionally);
* `piExact_eq_iwConv_diffFreqs`, `FpieceEqTm_of_bounded` -- the corrected func-calculus identity;
* `Tm_add_of_bounded`, `Tm_const_mul` -- linearity of `Tm` in the symbol, i.e. the corrected
  `hTm_add`/`hTm_smul` of the Rademacher--Menshov step (of which only the additive form needs the
  boundedness hypothesis).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelOps
import Submission.Work.KMTAreas.A7.Basic
import Submission.Work.KMTContract.kmtKernel_decay
import Submission.Work.KMTContract.kernel_l1_of_decay

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier
open Work.Analysis.EndVar
open Work.KMTContract
open Work.Analysis.Paraproduct (IWProjections)

noncomputable section

/-! ## §1. The periodisation of a difference of rescaled cutoffs -/

/-- Additivity of the periodisation `periodize φ ξ = ∑'_k φ (x + k)` on differences of the rescaled
cutoffs `etaCut kmtEta c` (each of which has compactly supported translates). -/
theorem periodize_sub_etaCut (a b : ℤ) :
    periodize (fun θ : ℝ => etaCut kmtEta a θ - etaCut kmtEta b θ)
      = periodize (etaCut kmtEta a) - periodize (etaCut kmtEta b) := by
  funext ξ
  simp only [periodize, Pi.sub_apply]
  exact (summable_etaCut_shift a _).tsum_sub (summable_etaCut_shift b _)

/-- The periodisation of a rescaled cutoff is bounded, hence (on the probability circle)
integrable. -/
theorem memLp_periodize_etaCut (c : ℤ) :
    MemLp (periodize (etaCut kmtEta c)) ⊤ circleMeasure :=
  memLp_periodize (contDiff_etaCut c).continuous.measurable
    (R := (2 : ℝ) ^ c) (C := 1) (by positivity)
    (fun x hx => etaCut_eq_zero_of_le (le_of_lt hx)) (fun x => norm_etaCut_le_one c x)

/-! ## §2. Linearity of the Fourier coefficients and of the kernels -/

/-- Linearity of the Fourier coefficients in the function, for integrable functions. -/
theorem fourierCoeff_sub' {F G : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hF : Integrable F circleMeasure) (hG : Integrable G circleMeasure) (n : ℤ) :
    fourierCoeff (F - G) n = fourierCoeff F n - fourierCoeff G n := by
  have h := integral_sub (hF.fourier_smul (-n)) (hG.fourier_smul (-n))
  simpa [fourierCoeff, Pi.sub_apply, mul_sub] using h

/-- The kernel of the `iwSymbolSet` of a difference of two symbols is the difference of the
kernels. -/
theorem iwKernel_iwSymbolSet_sub {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ Ψ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hΦ : Integrable (iwSymbolSet A Φ) circleMeasure)
    (hΨ : Integrable (iwSymbolSet A Ψ) circleMeasure) (j : ℤ) :
    iwKernel (iwSymbolSet A (Φ - Ψ)) j
      = iwKernel (iwSymbolSet A Φ) j - iwKernel (iwSymbolSet A Ψ) j := by
  have hsym : iwSymbolSet A (Φ - Ψ) = iwSymbolSet A Φ - iwSymbolSet A Ψ := by
    funext ξ
    simp only [iwSymbolSet, Pi.sub_apply]
    rw [Finset.sum_sub_distrib]
  have hlin : fourierCoeff (iwSymbolSet A Φ - iwSymbolSet A Ψ) j
      = fourierCoeff (iwSymbolSet A Φ) j - fourierCoeff (iwSymbolSet A Ψ) j := by
    have h := integral_sub (hΦ.fourier_smul (-j)) (hΨ.fourier_smul (-j))
    simpa [fourierCoeff, Pi.sub_apply, mul_sub] using h
  simp only [iwKernel]
  rw [hsym, hlin]

/-- Additivity of the kernel in the frequency set: for `B ⊆ A` the kernel of the `iwSymbolSet` of
the complement `A \ B` is the difference of the kernels (`iwSymbolSet_sdiff` at the level of the
Fourier coefficients). -/
theorem iwKernel_iwSymbolSet_sdiff {A B : Finset Work.Analysis.IonescuWainger.Circle}
    (hBA : B ⊆ A) {Φ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hA : Integrable (iwSymbolSet A Φ) circleMeasure)
    (hB : Integrable (iwSymbolSet B Φ) circleMeasure) (j : ℤ) :
    iwKernel (iwSymbolSet (A \ B) Φ) j
      = iwKernel (iwSymbolSet A Φ) j - iwKernel (iwSymbolSet B Φ) j := by
  have hsym : iwSymbolSet (A \ B) Φ = iwSymbolSet A Φ - iwSymbolSet B Φ := by
    rw [iwSymbolSet_sdiff A B hBA Φ]
    abel
  have hlin : fourierCoeff (iwSymbolSet A Φ - iwSymbolSet B Φ) j
      = fourierCoeff (iwSymbolSet A Φ) j - fourierCoeff (iwSymbolSet B Φ) j := by
    have h := integral_sub (hA.fourier_smul (-j)) (hB.fourier_smul (-j))
    simpa [fourierCoeff, Pi.sub_apply, mul_sub] using h
  simp only [iwKernel]
  rw [hsym, hlin]

/-! ## §3. The `ℓ¹` facts -/

/-- The kernel of the IW projection `Π_{≤ l, ≤ c}` is in `ℓ¹` (`kmtKernel_decay`: it decays like
`j^{-2}`). -/
theorem summable_iwKernel_etaCut (ρ : ℝ) (l : ℕ) (c : ℤ) :
    Summable (fun j : ℤ =>
      ‖iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta c))) j‖) := by
  obtain ⟨C, _hC, hdec⟩ := kmtKernel_decay ρ l c
  exact kernel_l1_of_decay (C := C) hdec

/-- The kernel of the *exact height* piece `Π_{l,≤c} = Π_{≤l,≤c} - Π_{≤l-1,≤c}` is in `ℓ¹`, by the
additivity of the kernel in the frequency set. -/
theorem summable_iwKernel_diffFreqs (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) (c : ℤ) :
    Summable (fun j : ℤ =>
      ‖iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize (etaCut kmtEta c))) j‖) := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    rw [diffFreqs, if_pos rfl]
    exact summable_iwKernel_etaCut ρ 0 c
  · have hne : l ≠ 0 := Nat.pos_iff_ne_zero.mp hl
    have hsub : iwArithFreqs ρ (l - 1) ⊆ iwArithFreqs ρ l :=
      iwArithFreqs_mono hρ hρ1 (Nat.pred_le l)
    rw [diffFreqs, if_neg hne]
    have hIntA : Integrable (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta c)))
        circleMeasure :=
      (memLp_iwSymbolSet _ (memLp_periodize_etaCut c)).integrable le_top
    have hIntB : Integrable (iwSymbolSet (iwArithFreqs ρ (l - 1)) (periodize (etaCut kmtEta c)))
        circleMeasure :=
      (memLp_iwSymbolSet _ (memLp_periodize_etaCut c)).integrable le_top
    have hsplit : ∀ j : ℤ,
        iwKernel (iwSymbolSet (iwArithFreqs ρ l \ iwArithFreqs ρ (l - 1))
            (periodize (etaCut kmtEta c))) j
          = iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta c))) j
            - iwKernel (iwSymbolSet (iwArithFreqs ρ (l - 1)) (periodize (etaCut kmtEta c))) j :=
      fun j => iwKernel_iwSymbolSet_sdiff hsub hIntA hIntB j
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      ((summable_iwKernel_etaCut ρ l c).add (summable_iwKernel_etaCut ρ (l - 1) c))
    rw [hsplit j]
    exact norm_sub_le _ _

/-- A bounded function times an `ℓ¹` kernel is summable. -/
theorem summable_mul_of_bounded {κ z : ℤ → ℂ} {B : ℝ}
    (hκ : Summable fun j : ℤ => ‖κ j‖) (hz : ∀ j : ℤ, ‖z j‖ ≤ B) :
    Summable fun j : ℤ => κ j * z j := by
  refine Summable.of_norm_bounded (hκ.mul_left (max B 0)) (fun j => ?_)
  rw [norm_mul]
  calc ‖κ j‖ * ‖z j‖ ≤ ‖κ j‖ * max B 0 :=
        mul_le_mul_of_nonneg_left ((hz j).trans (le_max_left _ _)) (norm_nonneg _)
    _ = max B 0 * ‖κ j‖ := by ring

/-! ## §4. Linearity of `iwConv` in the symbol, for bounded inputs -/

/-- **Linearity of the Ionescu--Wainger convolution in its symbol**, for bounded input: the only
hypotheses are the `ℓ¹`-ness of the two kernels and the integrability of the two symbols.  (The
unconditional form for arbitrary `f` is false: see the header.) -/
theorem iwConv_sub_of_bounded {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ Ψ : Work.Analysis.IonescuWainger.Circle → ℂ} {f : ℤ → ℂ} {B : ℝ}
    (hB : ∀ m : ℤ, ‖f m‖ ≤ B)
    (hΦ : Integrable (iwSymbolSet A Φ) circleMeasure)
    (hΨ : Integrable (iwSymbolSet A Ψ) circleMeasure)
    (hκΦ : Summable fun j : ℤ => ‖iwKernel (iwSymbolSet A Φ) j‖)
    (hκΨ : Summable fun j : ℤ => ‖iwKernel (iwSymbolSet A Ψ) j‖) :
    iwConv A (Φ - Ψ) f = iwConv A Φ f - iwConv A Ψ f := by
  funext n
  rw [Pi.sub_apply, iwConv_apply, iwConv_apply, iwConv_apply]
  have hz : ∀ j : ℤ, ‖f (n - j)‖ ≤ B := fun j => hB _
  have hs1 : Summable fun j : ℤ => iwKernel (iwSymbolSet A Φ) j • f (n - j) := by
    simpa only [smul_eq_mul] using summable_mul_of_bounded hκΦ hz
  have hs2 : Summable fun j : ℤ => iwKernel (iwSymbolSet A Ψ) j • f (n - j) := by
    simpa only [smul_eq_mul] using summable_mul_of_bounded hκΨ hz
  rw [← hs1.tsum_sub hs2]
  refine tsum_congr (fun j => ?_)
  rw [iwKernel_iwSymbolSet_sub hΦ hΨ j, sub_smul]

/-! ## §4b. Additivity and scalar linearity of `iwConv` in the symbol -/

/-- Additivity of the periodisation on a sum of symbols with summable translates. -/
theorem periodize_add {φ ψ : ℝ → ℂ} (hφ : ∀ x : ℝ, Summable fun j : ℤ => φ (x + j))
    (hψ : ∀ x : ℝ, Summable fun j : ℤ => ψ (x + j)) :
    periodize (φ + ψ) = periodize φ + periodize ψ := by
  funext ξ
  simp only [periodize, Pi.add_apply]
  exact (hφ _).tsum_add (hψ _)

/-- Additivity of the kernel in the symbol. -/
theorem iwKernel_iwSymbolSet_add {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ Ψ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hΦ : Integrable (iwSymbolSet A Φ) circleMeasure)
    (hΨ : Integrable (iwSymbolSet A Ψ) circleMeasure) (j : ℤ) :
    iwKernel (iwSymbolSet A (Φ + Ψ)) j
      = iwKernel (iwSymbolSet A Φ) j + iwKernel (iwSymbolSet A Ψ) j := by
  have hsym : iwSymbolSet A (Φ + Ψ) = iwSymbolSet A Φ + iwSymbolSet A Ψ := iwSymbolSet_add A Φ Ψ
  have hlin : fourierCoeff (iwSymbolSet A Φ + iwSymbolSet A Ψ) j
      = fourierCoeff (iwSymbolSet A Φ) j + fourierCoeff (iwSymbolSet A Ψ) j :=
    congrFun (fourierCoeff.add hΦ hΨ) j
  simp only [iwKernel]
  rw [hsym, hlin]

/-- Scalar linearity of the kernel in the symbol (no integrability needed). -/
theorem iwKernel_iwSymbolSet_const_mul (A : Finset Work.Analysis.IonescuWainger.Circle) (c : ℂ)
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} (j : ℤ) :
    iwKernel (iwSymbolSet A (fun ξ => c * Φ ξ)) j = c * iwKernel (iwSymbolSet A Φ) j := by
  have hsym : iwSymbolSet A (fun ξ => c * Φ ξ) = fun ξ => c * iwSymbolSet A Φ ξ :=
    iwSymbolSet_const_mul A c Φ
  simp only [iwKernel]
  rw [hsym, fourierCoeff.const_mul]

/-- Additivity of `iwConv` in the symbol, for bounded input. -/
theorem iwConv_add_of_bounded {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ Ψ : Work.Analysis.IonescuWainger.Circle → ℂ} {f : ℤ → ℂ} {B : ℝ}
    (hB : ∀ m : ℤ, ‖f m‖ ≤ B)
    (hΦ : Integrable (iwSymbolSet A Φ) circleMeasure)
    (hΨ : Integrable (iwSymbolSet A Ψ) circleMeasure)
    (hκΦ : Summable fun j : ℤ => ‖iwKernel (iwSymbolSet A Φ) j‖)
    (hκΨ : Summable fun j : ℤ => ‖iwKernel (iwSymbolSet A Ψ) j‖) :
    iwConv A (Φ + Ψ) f = iwConv A Φ f + iwConv A Ψ f := by
  funext n
  rw [Pi.add_apply, iwConv_apply, iwConv_apply, iwConv_apply]
  have hz : ∀ j : ℤ, ‖f (n - j)‖ ≤ B := fun j => hB _
  have hs1 : Summable fun j : ℤ => iwKernel (iwSymbolSet A Φ) j • f (n - j) := by
    simpa only [smul_eq_mul] using summable_mul_of_bounded hκΦ hz
  have hs2 : Summable fun j : ℤ => iwKernel (iwSymbolSet A Ψ) j • f (n - j) := by
    simpa only [smul_eq_mul] using summable_mul_of_bounded hκΨ hz
  rw [← hs1.tsum_add hs2]
  refine tsum_congr (fun j => ?_)
  rw [iwKernel_iwSymbolSet_add hΦ hΨ j, add_smul]

/-- **Scalar linearity of `iwConv` in the symbol**: this one holds for *every* `f` (scalar
multiplication commutes with the unconditional `tsum`, `tsum_mul_left`), unlike the additive and
difference forms, which need the families to be summable. -/
theorem iwConv_const_mul {A : Finset Work.Analysis.IonescuWainger.Circle} (c : ℂ)
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} {f : ℤ → ℂ} :
    iwConv A (fun ξ => c * Φ ξ) f = fun n : ℤ => c * iwConv A Φ f n := by
  funext n
  rw [iwConv_apply, iwConv_apply]
  have key : (∑' j : ℤ, iwKernel (iwSymbolSet A (fun ξ => c * Φ ξ)) j • f (n - j))
      = ∑' j : ℤ, c * (iwKernel (iwSymbolSet A Φ) j • f (n - j)) := by
    refine tsum_congr (fun j => ?_)
    rw [iwKernel_iwSymbolSet_const_mul A c j, smul_eq_mul]
    ring
  rw [key, tsum_mul_left]

/-! ## §5. The exact-height piece is the `diffFreqs` multiplier -/

/-- The exact-height IW piece `Π_{l,≤c} = Π_{≤l,≤c} - Π_{≤l-1,≤c}` of the contract is the
`diffFreqs` multiplier `iwConv (diffFreqs ρ l) (periodize (etaCut kmtEta c))`, for bounded input. -/
theorem piExact_eq_iwConv_diffFreqs (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) (c : ℤ)
    (f : ℤ → ℂ) {B : ℝ} (hB : ∀ m : ℤ, ‖f m‖ ≤ B) :
    piExact (kmtPj ρ) l c f = iwConv (diffFreqs ρ l) (periodize (etaCut kmtEta c)) f := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    rfl
  · have hne : l ≠ 0 := Nat.pos_iff_ne_zero.mp hl
    rw [diffFreqs, if_neg hne]
    have hsub : iwArithFreqs ρ (l - 1) ⊆ iwArithFreqs ρ l :=
      iwArithFreqs_mono hρ hρ1 (Nat.pred_le l)
    have hIntA : Integrable (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta c)))
        circleMeasure :=
      (memLp_iwSymbolSet _ (memLp_periodize_etaCut c)).integrable le_top
    have hIntB : Integrable (iwSymbolSet (iwArithFreqs ρ (l - 1)) (periodize (etaCut kmtEta c)))
        circleMeasure :=
      (memLp_iwSymbolSet _ (memLp_periodize_etaCut c)).integrable le_top
    funext n
    have hL : piExact (kmtPj ρ) l c f n = kmtProj ρ l c f n - kmtProj ρ (l - 1) c f n := by
      simp only [piExact, if_neg hne, kmtPj_proj, Pi.sub_apply]
    rw [hL, kmtProj_apply ρ l c f n, kmtProj_apply ρ (l - 1) c f n]
    have hs1 : Summable fun j : ℤ =>
        iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta c))) j * f (n - j) :=
      summable_mul_of_bounded (summable_iwKernel_etaCut ρ l c) (fun j => hB _)
    have hs2 : Summable fun j : ℤ =>
        iwKernel (iwSymbolSet (iwArithFreqs ρ (l - 1)) (periodize (etaCut kmtEta c))) j
          * f (n - j) :=
      summable_mul_of_bounded (summable_iwKernel_etaCut ρ (l - 1) c) (fun j => hB _)
    rw [← hs1.tsum_sub hs2, iwConv_apply]
    refine tsum_congr (fun j => ?_)
    rw [iwKernel_iwSymbolSet_sdiff hsub hIntA hIntB j, sub_smul]
    simp only [smul_eq_mul]

/-! ## §6. The func-calculus identity, corrected -/

/-- **The func-calculus identity of the §5 pieces**, in the form in which it is true (and in which
the §5 assembly uses it: its inputs lie in `ℓ^p`, `p < ∞`, hence are bounded).

For the requested *unconditional* form over all `f : ℤ → ℂ` see the counterexample in the header of
this file: it is false, because both sides are `tsum`-level expressions and `tsum` is `0` on
non-summable families, so pointwise symbol algebra does not compare them. -/
theorem FpieceEqTm_of_bounded {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l s N : ℕ) (f : ℤ → ℂ)
    {B : ℝ} (hB : ∀ m : ℤ, ‖f m‖ ≤ B) :
    Fpiece (kmtPj ρ) 0 l (s : ℤ) N f = Tm ρ l (pieceSymF s N) f := by
  rcases eq_or_ne s 0 with hs | hs
  · subst hs
    have hL : Fpiece (kmtPj ρ) 0 l (((0 : ℕ) : ℤ)) N f
        = piExact (kmtPj ρ) l (-(logN N)) f := by
      simp only [Fpiece, piece]
      split_ifs with h
      · simp
      · exact absurd (by simp) h
    have hR : pieceSymF 0 N = etaCut kmtEta (-(logN N)) := by
      funext ξ
      simp only [pieceSymF]
      simp
    have hTm : Tm ρ l (pieceSymF 0 N) f
        = iwConv (diffFreqs ρ l) (periodize (etaCut kmtEta (-(logN N)))) f := by
      simp only [Tm, hR]
    rw [hL, hTm]
    exact piExact_eq_iwConv_diffFreqs ρ hρ hρ1 l (-(logN N)) f hB
  · have hne : (s : ℤ) ≠ -(0 : ℤ) := by
      simp only [neg_zero]
      exact_mod_cast hs
    have hL : Fpiece (kmtPj ρ) 0 l (s : ℤ) N f
        = piExact (kmtPj ρ) l (-(logN N) + (s : ℤ)) f
          - piExact (kmtPj ρ) l (-(logN N) + ((s : ℤ) - 1)) f := by
      simp only [Fpiece, piece]
      split_ifs with h
      · exact absurd (by simpa using h) hs
      · rfl
    have hsym : periodize (pieceSymF s N)
        = periodize (etaCut kmtEta (-(logN N) + (s : ℤ)))
          - periodize (etaCut kmtEta (-(logN N) + ((s : ℤ) - 1))) := by
      have h1 : pieceSymF s N
          = fun θ : ℝ => etaCut kmtEta (-(logN N) + (s : ℤ)) θ
              - etaCut kmtEta (-(logN N) + ((s : ℤ) - 1)) θ := by
        funext θ
        simp only [pieceSymF, if_neg hs]
        ring_nf
      rw [h1, periodize_sub_etaCut]
    have hI : Integrable (iwSymbolSet (diffFreqs ρ l)
        (periodize (etaCut kmtEta (-(logN N) + (s : ℤ))))) circleMeasure :=
      (memLp_iwSymbolSet _ (memLp_periodize_etaCut _)).integrable le_top
    have hI2 : Integrable (iwSymbolSet (diffFreqs ρ l)
        (periodize (etaCut kmtEta (-(logN N) + ((s : ℤ) - 1))))) circleMeasure :=
      (memLp_iwSymbolSet _ (memLp_periodize_etaCut _)).integrable le_top
    have hsub : iwConv (diffFreqs ρ l)
          (periodize (etaCut kmtEta (-(logN N) + (s : ℤ)))
            - periodize (etaCut kmtEta (-(logN N) + ((s : ℤ) - 1)))) f
        = iwConv (diffFreqs ρ l) (periodize (etaCut kmtEta (-(logN N) + (s : ℤ)))) f
          - iwConv (diffFreqs ρ l)
              (periodize (etaCut kmtEta (-(logN N) + ((s : ℤ) - 1)))) f :=
      iwConv_sub_of_bounded hB hI hI2
        (summable_iwKernel_diffFreqs ρ hρ hρ1 l (-(logN N) + (s : ℤ)))
        (summable_iwKernel_diffFreqs ρ hρ hρ1 l (-(logN N) + ((s : ℤ) - 1)))
    have hTm : Tm ρ l (pieceSymF s N) f
        = piExact (kmtPj ρ) l (-(logN N) + (s : ℤ)) f
          - piExact (kmtPj ρ) l (-(logN N) + ((s : ℤ) - 1)) f := by
      simp only [Tm]
      rw [hsym, hsub]
      rw [← piExact_eq_iwConv_diffFreqs ρ hρ hρ1 l (-(logN N) + (s : ℤ)) f hB,
        ← piExact_eq_iwConv_diffFreqs ρ hρ hρ1 l (-(logN N) + ((s : ℤ) - 1)) f hB]
    exact hL.trans hTm.symm

/-! ## §7. Linearity of the multiplier family `Tm` in the symbol, for bounded inputs -/

/-- Additivity of `Tm` in the symbol, for bounded input.  This is the form of `hTm_add` that the
Rademacher--Menshov step of the §5 assembly can use; the unconditional form over all `f` is false
for the same reason as the requested `FpieceEqTm` (see the header of this file). -/
theorem Tm_add_of_bounded {ρ : ℝ} (l : ℕ) {φ ψ : ℝ → ℂ} {f : ℤ → ℂ} {B : ℝ}
    (hB : ∀ m : ℤ, ‖f m‖ ≤ B)
    (hφ : ∀ x : ℝ, Summable fun j : ℤ => φ (x + j))
    (hψ : ∀ x : ℝ, Summable fun j : ℤ => ψ (x + j))
    (hIφ : Integrable (iwSymbolSet (diffFreqs ρ l) (periodize φ)) circleMeasure)
    (hIψ : Integrable (iwSymbolSet (diffFreqs ρ l) (periodize ψ)) circleMeasure)
    (hκφ : Summable fun j : ℤ => ‖iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize φ)) j‖)
    (hκψ : Summable fun j : ℤ => ‖iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize ψ)) j‖) :
    Tm ρ l (φ + ψ) f = Tm ρ l φ f + Tm ρ l ψ f := by
  have hp : periodize (φ + ψ) = periodize φ + periodize ψ := periodize_add hφ hψ
  simp only [Tm]
  rw [hp, iwConv_add_of_bounded hB hIφ hIψ hκφ hκψ]

/-- Scalar linearity of `Tm` in the symbol; unlike the additive form this needs no boundedness of
`f` (nor any summability of the translates of `φ`). -/
theorem Tm_const_mul {ρ : ℝ} (l : ℕ) (c : ℂ) {φ : ℝ → ℂ} {f : ℤ → ℂ} :
    Tm ρ l (fun ξ => c * φ ξ) f = fun n : ℤ => c * Tm ρ l φ f n := by
  have hp : periodize (fun ξ => c * φ ξ) = fun ξ => c * periodize φ ξ := by
    funext ξ
    simp only [periodize]
    exact tsum_mul_left
  simp only [Tm]
  rw [hp, iwConv_const_mul]

end

end Work.KMTAreas.A7
