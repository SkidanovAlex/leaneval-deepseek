/-
# Self-adjointness of the Ionescu--Wainger projection `Π_{≤l,≤k}`

The Ionescu--Wainger projection `kmtProj ρ l k = Π_{≤l,≤k}` of Krause--Mirek--Tao §5 is the
convolution with the Fourier coefficients

`K j = iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) j`

of the IW symbol `σ_{l,k}(ξ) = ∑_{α ∈ (ℚ/ℤ)_{≤l}} η_{≤k}(ξ - α)`; that is,
`kmtProj ρ l k f n = ∑'_j K j * f (n - j)` (`kmtProj_apply`).

Two structural facts about the kernel `K` are available in the workspace:

* `K` is **even**, `K (-j) = K j` (`iwKernel_even_of_even` applied to the evenness of the symbol
  `iwSymbolSetNegEq`: the frequency set `(ℚ/ℤ)_{≤l}` is invariant under `α ↦ -α` and the cutoff
  `η_{≤k}` is even);
* `K` is **summable**, with `‖K j‖ ≤ C/(1+|j|)²` (`kmtKernel_decay` + `kernel_l1_of_decay`).

For such a kernel the convolution operator is symmetric in the bilinear pairing
`⟨a,b⟩ = ∑_x a x · b x` on `ℓ²(ℤ)`:

  `∑_x (K * u) x · f x = ∑_x u x · (K * f) x`.

Indeed the double family `(x,j) ↦ K j · u (x-j) · f x` is absolutely summable — by AM--GM,
`|K j| |u (x-j)| |f x| ≤ |K j| (|u (x-j)|² + |f x|²)/2`, and each of the two summands is a summable
product family because `K ∈ ℓ¹` and `u, f ∈ ℓ²` — so the two iterated sums may be exchanged
(`Summable.tsum_comm`), after which only the reindexings `j ↦ -j` (using the evenness of `K`) and
`x ↦ x - j` remain.

## Main result

* `Work.KMTAreas.A4.kmtProjSelfAdjoint`
-/
import Mathlib
import Submission.Work.KMTAreas.A4.Struct
import Submission.Work.KMTAreas.A4.kmtProj_reflect
import Submission.Work.KMTContract.kmtKernel_decay
import Submission.Work.KMTContract.kernel_l1_of_decay
import Submission.Commons.Analysis.DiscreteCZ.adjoint_l2_bound
import Submission.Work.KMTAreas.A4.symbolOfReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier

/-! ## Elementary bounds and reindexings -/

/-- AM--GM with a weight: `a x y ≤ (a x² + a y²)/2` for `a ≥ 0`. -/
private lemma mul_mul_le_avg_sq (a x y : ℝ) (ha : 0 ≤ a) :
    a * x * y ≤ (a * x ^ 2 + a * y ^ 2) / 2 := by
  have h : 2 * x * y ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (x - y)]
  have h2 : a * (2 * x * y) ≤ a * (x ^ 2 + y ^ 2) := mul_le_mul_of_nonneg_left h ha
  linarith

/-- The same with the two outer factors interchanged. -/
private lemma mul_mul_le_avg_sq' (x a y : ℝ) (ha : 0 ≤ a) :
    x * a * y ≤ (a * x ^ 2 + a * y ^ 2) / 2 := by
  have h := mul_mul_le_avg_sq a x y ha
  nlinarith [h]

/-- An `ℓ¹` kernel against an `ℓ²` sequence, as a family on the product index. -/
private lemma summable_prod_absK_mul_sq {K g : ℤ → ℂ}
    (hK : Summable fun j : ℤ => ‖K j‖) (hg : Summable fun y : ℤ => ‖g y‖ ^ 2) :
    Summable fun p : ℤ × ℤ => ‖K p.2‖ * ‖g p.1‖ ^ 2 := by
  have h := Summable.mul_of_nonneg hK hg (fun _ => norm_nonneg _) (fun _ => by positivity)
  have hφ : Function.Injective fun p : ℤ × ℤ => (p.2, p.1) := by
    intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext hpq.2 hpq.1
  exact (h.comp_injective hφ).congr fun p => rfl

/-- The shifted form of the preceding majorant: `(x,j) ↦ ‖K j‖ ‖g (x-j)‖²`. -/
private lemma summable_prod_absK_mul_sq_sub {K g : ℤ → ℂ}
    (hK : Summable fun j : ℤ => ‖K j‖) (hg : Summable fun y : ℤ => ‖g y‖ ^ 2) :
    Summable fun p : ℤ × ℤ => ‖K p.2‖ * ‖g (p.1 - p.2)‖ ^ 2 := by
  have hφ : Function.Injective fun p : ℤ × ℤ => (p.1 - p.2, p.2) := by
    intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext (by omega) hpq.2
  exact ((summable_prod_absK_mul_sq hK hg).comp_injective hφ).congr fun p => rfl

/-- Substituting `x ↦ x + c` in a sum over `ℤ`. -/
private lemma tsum_add_shift (g : ℤ → ℂ) (c : ℤ) :
    (∑' x : ℤ, g x) = ∑' x : ℤ, g (x + c) := by
  rw [← (Equiv.addRight c).tsum_eq]
  exact tsum_congr fun x => by simp

/-- Substituting `j ↦ -j` in a sum over `ℤ`. -/
private lemma tsum_neg_shift (g : ℤ → ℂ) :
    (∑' j : ℤ, g j) = ∑' j : ℤ, g (-j) := by
  rw [← (Equiv.neg ℤ).tsum_eq]
  exact tsum_congr fun j => by simp [Equiv.neg_apply]

/-! ## Self-adjointness of an even summable convolution kernel -/

/-- **Self-adjointness of an even `ℓ¹` convolution kernel on `ℓ²`.**  For a summable kernel `K`
with `K (-j) = K j` and `ℓ²` sequences `u, f` (in the sense that the squared norms are summable),

`∑_x (∑_j K_j u (x-j)) f x = ∑_x u x (∑_j K_j f (x-j))`. -/
private theorem tsum_selfAdjoint_conv (K : ℤ → ℂ) (hK : Summable fun j : ℤ => ‖K j‖)
    (hKeven : ∀ j : ℤ, K (-j) = K j) {u f : ℤ → ℂ}
    (hu : Summable fun x : ℤ => ‖u x‖ ^ 2) (hf : Summable fun x : ℤ => ‖f x‖ ^ 2) :
    (∑' x : ℤ, (∑' j : ℤ, K j * u (x - j)) * f x)
      = ∑' x : ℤ, u x * (∑' j : ℤ, K j * f (x - j)) := by
  -- The two double families are absolutely summable (AM--GM + Tonelli).
  have hsumF : Summable fun p : ℤ × ℤ => K p.2 * u (p.1 - p.2) * f p.1 :=
    Summable.of_norm_bounded
      (((summable_prod_absK_mul_sq_sub hK hu).add (summable_prod_absK_mul_sq hK hf)).div_const 2)
      fun p => by
        rw [norm_mul, norm_mul]
        exact mul_mul_le_avg_sq _ _ _ (norm_nonneg _)
  have hsumG : Summable fun p : ℤ × ℤ => u p.1 * K p.2 * f (p.1 - p.2) :=
    Summable.of_norm_bounded
      (((summable_prod_absK_mul_sq hK hu).add (summable_prod_absK_mul_sq_sub hK hf)).div_const 2)
      fun p => by
        rw [norm_mul, norm_mul]
        exact mul_mul_le_avg_sq' _ _ _ (norm_nonneg _)
  -- The two iterated sums.
  have hL1 : (∑' x : ℤ, (∑' j : ℤ, K j * u (x - j)) * f x)
      = ∑' x : ℤ, ∑' j : ℤ, K j * u (x - j) * f x :=
    tsum_congr fun x =>
      (tsum_mul_right (f := fun j : ℤ => K j * u (x - j)) (a := f x)).symm
  have hL2 : (∑' x : ℤ, ∑' j : ℤ, K j * u (x - j) * f x)
      = ∑' j : ℤ, ∑' x : ℤ, K j * u (x - j) * f x :=
    (Summable.tsum_comm (f := fun x j : ℤ => K j * u (x - j) * f x) hsumF).symm
  have hL3 : (∑' j : ℤ, ∑' x : ℤ, K j * u (x - j) * f x)
      = ∑' j : ℤ, K j * ∑' x : ℤ, u (x - j) * f x := by
    refine tsum_congr fun j => ?_
    rw [← tsum_mul_left]
    exact tsum_congr fun x => by ring
  have hR1 : (∑' x : ℤ, u x * (∑' j : ℤ, K j * f (x - j)))
      = ∑' x : ℤ, ∑' j : ℤ, u x * K j * f (x - j) := by
    refine tsum_congr fun x => ?_
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring
  have hR2 : (∑' x : ℤ, ∑' j : ℤ, u x * K j * f (x - j))
      = ∑' j : ℤ, ∑' x : ℤ, u x * K j * f (x - j) :=
    (Summable.tsum_comm (f := fun x j : ℤ => u x * K j * f (x - j)) hsumG).symm
  have hR3 : (∑' j : ℤ, ∑' x : ℤ, u x * K j * f (x - j))
      = ∑' j : ℤ, K j * ∑' x : ℤ, u x * f (x - j) := by
    refine tsum_congr fun j => ?_
    rw [← tsum_mul_left]
    exact tsum_congr fun x => by ring
  -- The reindexing: `x ↦ x + j` inside, `j ↦ -j` outside, using the evenness of `K`.
  have hshift : ∀ j : ℤ, (∑' x : ℤ, u x * f (x - j)) = ∑' x : ℤ, u (x + j) * f x := by
    intro j
    rw [tsum_add_shift (fun x : ℤ => u x * f (x - j)) j]
    refine tsum_congr fun x => ?_
    have h1 : x + j - j = x := by ring
    rw [h1]
  have hfinal : (∑' j : ℤ, K j * ∑' x : ℤ, u x * f (x - j))
      = ∑' j : ℤ, K j * ∑' x : ℤ, u (x - j) * f x := by
    have e1 : (∑' j : ℤ, K j * ∑' x : ℤ, u x * f (x - j))
        = ∑' j : ℤ, K j * ∑' x : ℤ, u (x + j) * f x :=
      tsum_congr fun j => by rw [hshift j]
    have e2 : (∑' j : ℤ, K j * ∑' x : ℤ, u (x + j) * f x)
        = ∑' j : ℤ, K (-j) * ∑' x : ℤ, u (x + (-j)) * f x :=
      tsum_neg_shift (fun j : ℤ => K j * ∑' x : ℤ, u (x + j) * f x)
    have e3 : (∑' j : ℤ, K (-j) * ∑' x : ℤ, u (x + (-j)) * f x)
        = ∑' j : ℤ, K j * ∑' x : ℤ, u (x - j) * f x := by
      refine tsum_congr fun j => ?_
      have hinner : (∑' x : ℤ, u (x + (-j)) * f x) = ∑' x : ℤ, u (x - j) * f x :=
        tsum_congr fun x => by rw [sub_eq_add_neg]
      rw [hKeven j, hinner]
    exact e1.trans (e2.trans e3)
  exact hL1.trans (hL2.trans (hL3.trans (hfinal.symm.trans
    (hR3.symm.trans (hR2.symm.trans hR1.symm)))))

/-! ## The Ionescu--Wainger projection -/

/-- **Self-adjointness of the Ionescu--Wainger projection `Π_{≤l,≤k}` on `ℓ²(ℤ)`.**

For `u, f ∈ ℓ²(ℤ)` (with respect to the counting measure), the bilinear pairing
`⟨a,b⟩ = ∑_x a x · b x` satisfies `⟨Π_{≤l,≤k} u, f⟩ = ⟨u, Π_{≤l,≤k} f⟩`.  This is the
`L²`-self-adjointness of the projection, i.e. the reality of the IW symbol
`σ_{l,k}(ξ) = ∑_{α ∈ (ℚ/ℤ)_{≤l}} η_{≤k}(ξ - α)` at the level of the convolution kernel. -/
theorem kmtProjSelfAdjoint (ρ : ℝ) (l : ℕ) (k : ℤ) {u f : ℤ → ℂ}
    (hu : MeasureTheory.MemLp u 2 MeasureTheory.Measure.count)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) :
    (∑' x : ℤ, Work.KMTContract.kmtProj ρ l k u x * f x)
      = ∑' x : ℤ, u x * Work.KMTContract.kmtProj ρ l k f x := by
  -- The kernel, its summability and its evenness.
  obtain ⟨C, _hC, hdec⟩ := Work.KMTContract.kmtKernel_decay ρ l k
  have hK : Summable fun j : ℤ => ‖iwKernel (iwSymbolSet (iwArithFreqs ρ l)
      (periodize (etaCut Work.KMTContract.kmtEta k))) j‖ :=
    Work.KMTContract.kernel_l1_of_decay
      (c := fun j : ℤ => iwKernel (iwSymbolSet (iwArithFreqs ρ l)
        (periodize (etaCut Work.KMTContract.kmtEta k))) j) hdec
  have hKeven : ∀ j : ℤ, iwKernel (iwSymbolSet (iwArithFreqs ρ l)
      (periodize (etaCut Work.KMTContract.kmtEta k))) (-j)
      = iwKernel (iwSymbolSet (iwArithFreqs ρ l)
        (periodize (etaCut Work.KMTContract.kmtEta k))) j :=
    fun j => iwKernel_even_of_even (fun ξ => iwSymbolSetNegEq ρ l k ξ) j
  -- `ℓ²` membership of `u` and `f`.
  have hu2 : Summable fun x : ℤ => ‖u x‖ ^ 2 :=
    (Commons.Analysis.DiscreteCZ.eLpNorm_two_count_lt_top_iff u).mp hu.eLpNorm_lt_top
  have hf2 : Summable fun x : ℤ => ‖f x‖ ^ 2 :=
    (Commons.Analysis.DiscreteCZ.eLpNorm_two_count_lt_top_iff f).mp hf.eLpNorm_lt_top
  -- `kmtProj` is by definition the convolution with the kernel, so the goal is the general
  -- `tsum_selfAdjoint_conv` with that kernel.
  show (∑' x : ℤ, (∑' j : ℤ, iwKernel (iwSymbolSet (iwArithFreqs ρ l)
        (periodize (etaCut Work.KMTContract.kmtEta k))) j * u (x - j)) * f x)
      = ∑' x : ℤ, u x * (∑' j : ℤ, iwKernel (iwSymbolSet (iwArithFreqs ρ l)
        (periodize (etaCut Work.KMTContract.kmtEta k))) j * f (x - j))
  exact tsum_selfAdjoint_conv _ hK hKeven hu2 hf2

end Work.KMTAreas.A4
