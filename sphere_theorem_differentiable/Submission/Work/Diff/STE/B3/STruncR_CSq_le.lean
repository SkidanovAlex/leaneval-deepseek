import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.CSq_trunc_le
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Friedrichs truncation does not increase the Sobolev norm `CSq s` of a real periodization

Let `f : (ι → ℝ) → ℝ` be smooth and supported in the open unit cube `(-1/2,1/2)^ι`, and let

`g y = ∑' m : ι → ℤ, f (y + m)`

be its periodization (a smooth `1`-periodic function, `periodization_contDiff_periodic`).  Write
`c = fourierCoeff g` for its Fourier coefficients, `D = trunc ρ ε c` for the Friedrichs truncation
(coefficients multiplied by the *real* factor `ρ (ε • m)`, `‖ρ‖ ≤ 1`), and `S := seriesFun D` for
the associated Fourier series.  The claim of this file is

  `CSq s (fourierCoeff (ofReal ∘ re ∘ S)) ≤ CSq s c`,

i.e. *passing to the real part and then truncating never increases the weighted `ℓ²` norm
`CSq s = ∑' k, ⟨k⟩^{2s} ‖·(k)‖²`*.

The mathematics is completely elementary, and takes place on the coefficient side:

* `S` is an absolutely convergent Fourier series with coefficients `D`; the real part of `S` is the
  series with the *symmetrized* coefficients `E k = (D k + conj (D (-k)))/2` (this is
  `re_seriesFun_eq_seriesFun_symm`, an instance of `conj (∑' k, a k e_k) = ∑' k, conj (a k) e_{-k}`
  followed by the reindexing `k ↦ -k`);
* hence (Fourier inversion for absolutely convergent series, `fourierCoeff_seriesFun`)
  `fourierCoeff (ofReal ∘ re ∘ S) = E`;
* `‖E k‖ ≤ (‖D k‖ + ‖D (-k)‖)/2`, and since the weight `⟨k⟩² = wt k` is even, the sum over `k` of
  `wt k^s ‖E k‖²` is at most the sum of `wt k^s ‖D k‖²` (`CSq_symm_le`, using `((a+b)/2)² ≤
  (a²+b²)/2` and the reindexing `k ↦ -k`);
* `CSq s D ≤ CSq s c` is `CSq_trunc_le`.

Summability of everything is supplied by the smoothness of `f`: the periodization of a smooth
compactly supported function is smooth and periodic, so `summable_weighted_fourierCoeff_of_contDiff`
gives the weighted `ℓ²` summability of `c`, `summable_norm_of_CSq` upgrades it to `ℓ¹`, and
monotonicity (`‖D k‖ ≤ ‖c k‖`) transfers it downwards.
-/

noncomputable section

namespace Work.Diff.STE.B3

open MeasureTheory BigOperators
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `ofReal (re w) = (w + star w)/2`: the real part of a complex number, as a complex number. -/
lemma ofReal_re_eq (w : ℂ) : ((w.re : ℂ)) = (w + star w) / 2 := by
  rw [Complex.star_def]
  rw [show w + starRingEnd ℂ w = ↑(2 * w.re) from Complex.add_conj w]
  push_cast; ring

omit [DecidableEq ι] in
/-- The weight `⟨k⟩² = 1 + ∑ᵢ kᵢ²` is even. -/
lemma wt_neg (k : ι → ℤ) : Work.Diff.STE.wt (-k) = Work.Diff.STE.wt k := by
  simp only [Work.Diff.STE.wt]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- The conjugate of an absolutely convergent Fourier series is the series of the conjugated
(reversed) coefficients: `conj (∑' k, a k · e_k z) = ∑' k, conj (a (-k)) · e_k z`. -/
lemma star_seriesFun (D : (ι → ℤ) → ℂ) (hD : Summable (fun k => ‖D k‖)) (z : ι → ℝ) :
    star (Work.Diff.STE.seriesFun D z)
      = Work.Diff.STE.seriesFun (fun k => star (D (-k))) z := by
  have hsum : Summable (fun k : ι → ℤ => D k * Work.Diff.STE.fourierExp k z) := by
    refine Summable.of_norm ?_
    have hEq : (fun k : ι → ℤ => ‖D k * Work.Diff.STE.fourierExp k z‖) = (fun k => ‖D k‖) := by
      funext k; rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one]
    rw [hEq]; exact hD
  have h1 : star (Work.Diff.STE.seriesFun D z)
      = ∑' k : ι → ℤ, star (D k * Work.Diff.STE.fourierExp k z) := by
    rw [Work.Diff.STE.seriesFun]
    exact ContinuousLinearMap.map_tsum (Complex.conjCLE : ℂ →L[ℝ] ℂ) hsum
  have key : star (Work.Diff.STE.seriesFun D z)
      = ∑' k : ι → ℤ, star (D (-k)) * Work.Diff.STE.fourierExp k z := by
    rw [h1, tsum_congr (fun k => by
      rw [star_mul, Work.Diff.STE.BesselCont.star_fourierExp_char])]
    rw [← Equiv.tsum_eq (Equiv.neg (ι → ℤ))
          (fun j : ι → ℤ => Work.Diff.STE.fourierExp (-j) z * star (D j))]
    refine tsum_congr fun k => ?_
    simp only [Equiv.neg_apply]
    rw [neg_neg, mul_comm]
  rw [key, Work.Diff.STE.seriesFun]

omit [DecidableEq ι] in
/-- Reindexing `k ↦ -k` of the weighted `ℓ²` sum, using the evenness of the weight. -/
lemma tsum_wt_norm_neg (D : (ι → ℤ) → ℂ) (s : ℕ) :
    (∑' k : ι → ℤ, Work.Diff.STE.wt k ^ s * ‖D (-k)‖ ^ 2)
      = ∑' k : ι → ℤ, Work.Diff.STE.wt k ^ s * ‖D k‖ ^ 2 := by
  rw [← Equiv.tsum_eq (Equiv.neg (ι → ℤ))
        (fun k => Work.Diff.STE.wt k ^ s * ‖D k‖ ^ 2)]
  refine tsum_congr fun k => ?_
  simp only [Equiv.neg_apply, wt_neg]

omit [DecidableEq ι] in
/-- The arithmetic mean of two squares dominates the square of the mean. -/
lemma sq_half_add_le (a b : ℝ) : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- **Symmetrization does not increase the weighted `ℓ²` norm.**  For a coefficient family `D`
whose weighted `ℓ²` sum converges, the symmetrized family `k ↦ (D k + conj (D (-k)))/2` (the
Fourier coefficients of the real part of the associated series) has no larger `CSq s`. -/
lemma CSq_symm_le (D : (ι → ℤ) → ℂ) (s : ℕ)
    (hDw : Summable (fun k => Work.Diff.STE.wt k ^ s * ‖D k‖ ^ 2)) :
    Work.Diff.STE.CSq s (fun k => (D k + star (D (-k))) / 2) ≤ Work.Diff.STE.CSq s D := by
  have hDnegw : Summable (fun k => Work.Diff.STE.wt k ^ s * ‖D (-k)‖ ^ 2) := by
    refine (hDw.comp_injective (Equiv.neg (ι → ℤ)).injective).congr fun k => ?_
    simp only [Function.comp_apply, Equiv.neg_apply, wt_neg]
  have hmid : Summable (fun k => Work.Diff.STE.wt k ^ s * (‖D k‖ ^ 2 + ‖D (-k)‖ ^ 2)) := by
    refine (hDw.add hDnegw).congr fun k => ?_
    rw [mul_add]
  have hhalf : Summable (fun k => Work.Diff.STE.wt k ^ s * ((‖D k‖ ^ 2 + ‖D (-k)‖ ^ 2) / 2)) := by
    refine (hmid.mul_left (1 / 2 : ℝ)).congr fun k => ?_
    ring
  have hbound : ∀ k : ι → ℤ, Work.Diff.STE.wt k ^ s * ‖(D k + star (D (-k))) / 2‖ ^ 2
      ≤ Work.Diff.STE.wt k ^ s * ((‖D k‖ ^ 2 + ‖D (-k)‖ ^ 2) / 2) := by
    intro k
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s)
    have hn : ‖(D k + star (D (-k))) / 2‖ ≤ (‖D k‖ + ‖D (-k)‖) / 2 := by
      rw [norm_div]
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2]
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      calc ‖D k + star (D (-k))‖ ≤ ‖D k‖ + ‖star (D (-k))‖ := norm_add_le _ _
        _ = ‖D k‖ + ‖D (-k)‖ := by rw [norm_star]
    calc ‖(D k + star (D (-k))) / 2‖ ^ 2
        ≤ ((‖D k‖ + ‖D (-k)‖) / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ (‖D k‖ ^ 2 + ‖D (-k)‖ ^ 2) / 2 := sq_half_add_le _ _
  have hEfam : Summable (fun k => Work.Diff.STE.wt k ^ s * ‖(D k + star (D (-k))) / 2‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s) (sq_nonneg _))
      hbound hhalf
  have hscale : (∑' k : ι → ℤ,
        Work.Diff.STE.wt k ^ s * ((‖D k‖ ^ 2 + ‖D (-k)‖ ^ 2) / 2))
      = (1 / 2) * ∑' k : ι → ℤ, Work.Diff.STE.wt k ^ s * (‖D k‖ ^ 2 + ‖D (-k)‖ ^ 2) := by
    rw [← Summable.tsum_mul_left (1 / 2 : ℝ) hmid]
    exact tsum_congr fun k => by ring
  have hsplit : (∑' k : ι → ℤ, Work.Diff.STE.wt k ^ s * (‖D k‖ ^ 2 + ‖D (-k)‖ ^ 2))
      = (∑' k : ι → ℤ, Work.Diff.STE.wt k ^ s * ‖D k‖ ^ 2)
        + ∑' k : ι → ℤ, Work.Diff.STE.wt k ^ s * ‖D (-k)‖ ^ 2 := by
    rw [← Summable.tsum_add hDw hDnegw]
    exact tsum_congr fun k => by ring
  calc Work.Diff.STE.CSq s (fun k => (D k + star (D (-k))) / 2)
      = ∑' k : ι → ℤ, Work.Diff.STE.wt k ^ s * ‖(D k + star (D (-k))) / 2‖ ^ 2 := rfl
    _ ≤ ∑' k : ι → ℤ, Work.Diff.STE.wt k ^ s * ((‖D k‖ ^ 2 + ‖D (-k)‖ ^ 2) / 2) :=
        Summable.tsum_le_tsum hbound hEfam hhalf
    _ = (1 / 2) * ∑' k : ι → ℤ, Work.Diff.STE.wt k ^ s * (‖D k‖ ^ 2 + ‖D (-k)‖ ^ 2) := hscale
    _ = (1 / 2) * ((∑' k : ι → ℤ, Work.Diff.STE.wt k ^ s * ‖D k‖ ^ 2)
          + ∑' k : ι → ℤ, Work.Diff.STE.wt k ^ s * ‖D (-k)‖ ^ 2) := by rw [hsplit]
    _ = Work.Diff.STE.CSq s D := by rw [tsum_wt_norm_neg, Work.Diff.STE.CSq]; ring

/-- **The real part of an absolutely convergent Fourier series** is the series with the symmetrized
coefficients `k ↦ (D k + conj (D (-k)))/2`. -/
lemma re_seriesFun_eq_seriesFun_symm (D : (ι → ℤ) → ℂ) (hD : Summable (fun k => ‖D k‖))
    (z : ι → ℝ) :
    ((Work.Diff.STE.seriesFun D z).re : ℂ)
      = Work.Diff.STE.seriesFun (fun k => (D k + star (D (-k))) / 2) z := by
  have hsumD : Summable (fun k : ι → ℤ => D k * Work.Diff.STE.fourierExp k z) := by
    refine Summable.of_norm ?_
    have hEq : (fun k : ι → ℤ => ‖D k * Work.Diff.STE.fourierExp k z‖) = (fun k => ‖D k‖) := by
      funext k; rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one]
    rw [hEq]; exact hD
  have hDneg : Summable (fun k : ι → ℤ => ‖D (-k)‖) :=
    hD.comp_injective (Equiv.neg (ι → ℤ)).injective
  have hsumT : Summable (fun k : ι → ℤ => star (D (-k)) * Work.Diff.STE.fourierExp k z) := by
    refine Summable.of_norm ?_
    have hEq : (fun k : ι → ℤ => ‖star (D (-k)) * Work.Diff.STE.fourierExp k z‖)
        = (fun k => ‖D (-k)‖) := by
      funext k; rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one, norm_star]
    rw [hEq]; exact hDneg
  have hgoal : ∀ k : ι → ℤ, ((D k + star (D (-k))) / 2) * Work.Diff.STE.fourierExp k z
      = (1 / 2) * (D k * Work.Diff.STE.fourierExp k z)
        + (1 / 2) * (star (D (-k)) * Work.Diff.STE.fourierExp k z) := fun k => by ring
  have hAB : (∑' k : ι → ℤ, ((1 / 2) * (D k * Work.Diff.STE.fourierExp k z)
        + (1 / 2) * (star (D (-k)) * Work.Diff.STE.fourierExp k z)))
      = (∑' k : ι → ℤ, (1 / 2) * (D k * Work.Diff.STE.fourierExp k z))
        + ∑' k : ι → ℤ, (1 / 2) * (star (D (-k)) * Work.Diff.STE.fourierExp k z) :=
    Summable.tsum_add (hsumD.mul_left _) (hsumT.mul_left _)
  have hA : (∑' k : ι → ℤ, (1 / 2) * (D k * Work.Diff.STE.fourierExp k z))
      = (1 / 2) * ∑' k : ι → ℤ, D k * Work.Diff.STE.fourierExp k z :=
    Summable.tsum_mul_left _ hsumD
  have hB : (∑' k : ι → ℤ, (1 / 2) * (star (D (-k)) * Work.Diff.STE.fourierExp k z))
      = (1 / 2) * ∑' k : ι → ℤ, star (D (-k)) * Work.Diff.STE.fourierExp k z :=
    Summable.tsum_mul_left _ hsumT
  have hS : Work.Diff.STE.seriesFun D z
      = ∑' k : ι → ℤ, D k * Work.Diff.STE.fourierExp k z := rfl
  have hT : Work.Diff.STE.seriesFun (fun k => star (D (-k))) z
      = ∑' k : ι → ℤ, star (D (-k)) * Work.Diff.STE.fourierExp k z := rfl
  have hE0 : Work.Diff.STE.seriesFun (fun k => (D k + star (D (-k))) / 2) z
      = ∑' k : ι → ℤ, ((D k + star (D (-k))) / 2) * Work.Diff.STE.fourierExp k z := rfl
  rw [ofReal_re_eq, star_seriesFun D hD z, hS, hT, hE0, tsum_congr hgoal, hAB, hA, hB]
  ring

theorem STruncR_CSq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (ε : ℝ) (s : ℕ) (f : (ι → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfsupp : Function.support f ⊆
      Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :
    Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z : ι → ℝ => Complex.ofReal
        (Complex.re (Work.Diff.STE.seriesFun (Work.Diff.STE.trunc ρ ε
          (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ =>
            ∑' m : ι → ℤ, Complex.ofReal (f (y + Work.Diff.STE.iVec m))))) z))))
      ≤ Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z : ι → ℝ =>
          ∑' m : ι → ℤ, Complex.ofReal (f (z + Work.Diff.STE.iVec m)))) := by
  classical
  set g : (ι → ℝ) → ℂ := fun y => ∑' m : ι → ℤ, Complex.ofReal (f (y + Work.Diff.STE.iVec m))
    with hgdef
  set c : (ι → ℤ) → ℂ := Work.Diff.STE.fourierCoeff g with hcdef
  set D : (ι → ℤ) → ℂ := Work.Diff.STE.trunc ρ ε c with hDdef
  have hfc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => (f y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hf
  have hsuppc : Function.support (fun y : ι → ℝ => (f y : ℂ)) ⊆
      Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro y hy
    exact hfsupp (by simpa [Function.mem_support] using hy)
  have hper := periodization_contDiff_periodic (fun y : ι → ℝ => (f y : ℂ)) hfc hsuppc
  have hgcd : ContDiff ℝ (⊤ : ℕ∞) g := by
    rw [hgdef]; exact hper.1
  have hgper : Work.Diff.STE.Periodic1 g := by
    rw [hgdef]; exact hper.2.1
  have hCsq : Summable (fun k : ι → ℤ => Work.Diff.STE.wt k ^ s * ‖c k‖ ^ 2) := by
    rw [hcdef]
    exact Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff g hgcd hgper s
  obtain ⟨s', hs'⟩ : ∃ s' : ℕ, Fintype.card ι < 2 * s' := ⟨Fintype.card ι + 1, by omega⟩
  have hcsumm : Summable (fun k : ι → ℤ => ‖c k‖) := by
    rw [hcdef]
    exact Work.Diff.STE.summable_norm_of_CSq s' hs' (Work.Diff.STE.fourierCoeff g)
      (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff g hgcd hgper s')
  have hDle : ∀ k : ι → ℤ, ‖D k‖ ≤ ‖c k‖ := by
    intro k
    have hk := hρ (ε • fun i => (k i : ℝ))
    have hval : D k = (ρ (ε • fun i => (k i : ℝ)) : ℂ) * c k := by
      rw [hDdef]; rfl
    have hnorm : ‖(ρ (ε • fun i => (k i : ℝ)) : ℂ)‖ = ‖ρ (ε • fun i => (k i : ℝ))‖ := by
      simp
    rw [hval, norm_mul, hnorm]
    calc ‖ρ (ε • fun i => (k i : ℝ))‖ * ‖c k‖ ≤ 1 * ‖c k‖ :=
          mul_le_mul_of_nonneg_right hk (norm_nonneg _)
      _ = ‖c k‖ := one_mul _
  have hDsumm : Summable (fun k : ι → ℤ => ‖D k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hDle hcsumm
  have hDwt : Summable (fun k : ι → ℤ => Work.Diff.STE.wt k ^ s * ‖D k‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s) (sq_nonneg _))
      (fun k => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hDle k) 2)
        (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s))
      hCsq
  have hEfun : (fun z : ι → ℝ => ((Work.Diff.STE.seriesFun D z).re : ℂ))
      = Work.Diff.STE.seriesFun (fun k => (D k + star (D (-k))) / 2) :=
    funext fun z => re_seriesFun_eq_seriesFun_symm D hDsumm z
  have hnegs : Summable (fun k : ι → ℤ => ‖D (-k)‖) :=
    hDsumm.comp_injective (Equiv.neg (ι → ℤ)).injective
  have hEsumm : Summable (fun k : ι → ℤ => ‖(D k + star (D (-k))) / 2‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      ((hDsumm.add hnegs).mul_left (1 / 2 : ℝ))
    calc ‖(D k + star (D (-k))) / 2‖ = ‖D k + star (D (-k))‖ / 2 := by
          rw [norm_div]; norm_num
      _ ≤ (‖D k‖ + ‖D (-k)‖) / 2 := by
          refine div_le_div_of_nonneg_right ?_ (by norm_num)
          calc ‖D k + star (D (-k))‖ ≤ ‖D k‖ + ‖star (D (-k))‖ := norm_add_le _ _
            _ = ‖D k‖ + ‖D (-k)‖ := by rw [norm_star]
      _ = (1 / 2) * (‖D k‖ + ‖D (-k)‖) := by ring
  have hcoef : Work.Diff.STE.fourierCoeff
        (Work.Diff.STE.seriesFun (fun k => (D k + star (D (-k))) / 2))
      = fun k => (D k + star (D (-k))) / 2 :=
    funext fun k => Work.Diff.STE.flat.fourierCoeff_seriesFun _ hEsumm k
  show Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z : ι → ℝ =>
        ((Work.Diff.STE.seriesFun D z).re : ℂ))) ≤ Work.Diff.STE.CSq s c
  calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z : ι → ℝ =>
          ((Work.Diff.STE.seriesFun D z).re : ℂ)))
      = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
          (Work.Diff.STE.seriesFun (fun k => (D k + star (D (-k))) / 2))) := by rw [hEfun]
    _ = Work.Diff.STE.CSq s (fun k => (D k + star (D (-k))) / 2) := by rw [hcoef]
    _ ≤ Work.Diff.STE.CSq s D := CSq_symm_le D s hDwt
    _ ≤ Work.Diff.STE.CSq s c := by
        rw [hDdef]
        exact Work.Diff.STE.CSq_trunc_le ρ hρ ε s c hCsq

end Work.Diff.STE.B3
