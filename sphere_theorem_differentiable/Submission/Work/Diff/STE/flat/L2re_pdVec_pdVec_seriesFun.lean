import Mathlib
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.integral_seriesFun_mul_conj
import Submission.Work.Diff.STE.fourierCoeff_pdVec
import Submission.Work.Diff.STE.pdVec_contDiff_periodic
import Submission.Work.Diff.STE.summable_norm_of_CSq
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `L²` pairing of an iterated derivative with an iterated derivative of a finite
Fourier sum

Let `f` be a smooth (`C^∞`) `1`-periodic function on the flat torus `(ι → ℝ)` and let `d` be a
coefficient family supported in a finite set `s` (`d m = 0` for `m ∉ s`).  Then the `L²` pairing of
the iterated derivative `∂^l f` with the iterated derivative `∂^l (seriesFun d)` of the finite
Fourier sum `seriesFun d = Σ_m d m · exp(2πi m·x)` is

  `L2re (∂^l f) (∂^l (seriesFun d)) = Σ_{m ∈ s} (dmulV l (fourierCoeff f) m · conj (dmulV l d m)).re`,

i.e. the (real part of the) termwise product of the corresponding Fourier multipliers.

The ingredients are the ones already in the Layer A toolkit:

* `pdList_seriesFun`: term by term differentiation of a rapidly decaying Fourier series,
  `∂^l (seriesFun c) = seriesFun (dmulV l c)`, applicable because a finitely supported family
  satisfies every weighted `ℓ¹` summability hypothesis (a local lemma);
* `seriesFun c = Σ_{m ∈ s} c m · fourierExp m` for a family vanishing off `s`: the `tsum` collapses
  to a finite sum, so the pairing is the finite sum of the pairings with the individual characters;
* orthogonality of the characters in the form `fourierCoeff g m = ∫_{unitCube} fourierExp (-m)·g`
  together with `star (fourierExp m x) = fourierExp (-m) x` and the commutativity of `ℂ`;
* `fourierCoeff_pdVec`: `(∂^l f)^(m) = ∏_i 2πi m_{l i} · f̂(m)`, which identifies the coefficient
  family with `dmulV (List.ofFn l) (fourierCoeff f)`.
-/

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

noncomputable section

/-! ## A finitely supported Fourier series is a finite sum -/

private lemma seriesFun_eq_sum_of_support {ι : Type*} [Fintype ι] (c : (ι → ℤ) → ℂ)
    (s : Finset (ι → ℤ)) (hc : ∀ m : ι → ℤ, m ∉ s → c m = 0) (x : ι → ℝ) :
    Work.Diff.STE.seriesFun c x = ∑ m ∈ s, c m * Work.Diff.STE.fourierExp m x := by
  rw [Work.Diff.STE.seriesFun]
  exact tsum_eq_sum (fun m hm => by rw [hc m hm, zero_mul])

/-- A family vanishing off a finite set satisfies every weighted `ℓ¹` summability hypothesis. -/
private lemma summable_weighted_of_support {ι : Type*} [Fintype ι] (c : (ι → ℤ) → ℂ)
    (s : Finset (ι → ℤ)) (hc : ∀ m : ι → ℤ, m ∉ s → c m = 0) (N : ℕ) :
    Summable (fun k : ι → ℤ => Work.Diff.STE.wt k ^ N * ‖c k‖) :=
  summable_of_ne_finset_zero (s := s) (fun k hk => by rw [hc k hk, norm_zero, mul_zero])

/-- Term by term differentiation of a finitely supported Fourier series. -/
private lemma pdVec_seriesFun_of_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ℕ) (l : Fin j → ι) (d : (ι → ℤ) → ℂ) (s : Finset (ι → ℤ))
    (hd : ∀ m : ι → ℤ, m ∉ s → d m = 0) (x : ι → ℝ) :
    Work.Diff.STE.pdVec j l (Work.Diff.STE.seriesFun d) x
      = Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV (List.ofFn l) d) x :=
  Work.Diff.STE.pdList_seriesFun (List.ofFn l) d
    (fun N => summable_weighted_of_support d s hd N) x

/-- The iterated Fourier multiplier of the list `List.ofFn l`, written as a product over `Fin j`. -/
private lemma dmulV_ofFn {ι : Type*} (j : ℕ) (l : Fin j → ι) (c : (ι → ℤ) → ℂ)
    (m : ι → ℤ) :
    Work.Diff.STE.dmulV (List.ofFn l) c m
      = (∏ i : Fin j, (2 * Real.pi * Complex.I * (m (l i) : ℂ))) * c m := by
  rw [Work.Diff.STE.dmulV, List.map_ofFn, List.prod_ofFn]
  rfl

/-! ## The `L²` pairing with a finite Fourier sum -/

/-- **Pairing with a finitely supported Fourier series.**  For a continuous `g` and a coefficient
family `c` vanishing off the finite set `s`, the `L²` pairing of `g` with the Fourier series of `c`
is the finite sum of the pairings with the individual characters
`∫_{unitCube} g · conj (fourierExp m) = fourierCoeff g m`. -/
private lemma L2re_seriesFun_of_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ℝ) → ℂ) (hg : Continuous g)
    (c : (ι → ℤ) → ℂ) (s : Finset (ι → ℤ)) (hc : ∀ m : ι → ℤ, m ∉ s → c m = 0) :
    Work.Diff.STE.L2re g (Work.Diff.STE.seriesFun c)
      = ∑ m ∈ s, (Work.Diff.STE.fourierCoeff g m * star (c m)).re := by
  -- Conjugate the series, expand the finite sum, and conjugate each term.
  have hcongr : (∫ x in Work.Diff.STE.unitCube, g x * star (Work.Diff.STE.seriesFun c x))
      = ∫ x in Work.Diff.STE.unitCube,
          ∑ m ∈ s, star (c m) * (Work.Diff.STE.fourierExp (-m) x * g x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show g x * star (Work.Diff.STE.seriesFun c x)
        = ∑ m ∈ s, star (c m) * (Work.Diff.STE.fourierExp (-m) x * g x)
    rw [seriesFun_eq_sum_of_support c s hc x, star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [star_mul, Work.Diff.STE.star_fourierExp]
    ring
  -- Integrate the finite sum term by term and pull out the constants.
  have hinteg : ∀ m ∈ s, Integrable
      (fun x : ι → ℝ => star (c m) * (Work.Diff.STE.fourierExp (-m) x * g x))
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
    intro m _
    refine Work.Diff.STE.integrableOn_unitCube_of_continuous_cplx ?_
    exact continuous_const.mul ((Work.Diff.STE.continuous_fourierExp (-m)).mul hg)
  simp only [Work.Diff.STE.L2re]
  rw [hcongr, MeasureTheory.integral_finsetSum s hinteg]
  simp_rw [MeasureTheory.integral_const_mul]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show (∫ (x : ι → ℝ) in Work.Diff.STE.unitCube,
        Work.Diff.STE.fourierExp (-m) x * g x) = Work.Diff.STE.fourierCoeff g m from rfl]
  exact congrArg Complex.re (mul_comm _ _)

/-! ## The target -/

theorem L2re_pdVec_pdVec_seriesFun {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ℕ) (l : Fin j → ι) (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : Work.Diff.STE.Periodic1 f)
    (d : (ι → ℤ) → ℂ) (s : Finset (ι → ℤ)) (hd : ∀ m : ι → ℤ, m ∉ s → d m = 0) :
    Work.Diff.STE.L2re (Work.Diff.STE.pdVec j l f)
        (Work.Diff.STE.pdVec j l (Work.Diff.STE.seriesFun d))
      = ∑ m ∈ s,
          (Work.Diff.STE.dmulV (List.ofFn l) (Work.Diff.STE.fourierCoeff f) m
            * star (Work.Diff.STE.dmulV (List.ofFn l) d m)).re := by
  have hf' : ContDiff ℝ (j : WithTop ℕ∞) f := hf.of_le (by simp)
  -- The iterated derivative of `f` is continuous.
  have hcont : Continuous (Work.Diff.STE.pdVec j l f) :=
    (Work.Diff.STE.pdVec_contDiff_periodic j j le_rfl l f hf' hper).1.continuous
  -- The multiplier family is supported in `s`.
  have hdmul_supp : ∀ m : ι → ℤ, m ∉ s → Work.Diff.STE.dmulV (List.ofFn l) d m = 0 := by
    intro m hm
    rw [Work.Diff.STE.dmulV, hd m hm, mul_zero]
  -- Pairing with the finite Fourier sum.
  have hpair := L2re_seriesFun_of_support (Work.Diff.STE.pdVec j l f) hcont
      (Work.Diff.STE.dmulV (List.ofFn l) d) s hdmul_supp
  -- The iterated derivative of the finite Fourier sum is the Fourier series of the multiplier.
  have hser : Work.Diff.STE.pdVec j l (Work.Diff.STE.seriesFun d)
      = Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV (List.ofFn l) d) :=
    funext (pdVec_seriesFun_of_support j l d s hd)
  rw [hser, hpair]
  -- Identify the Fourier coefficients of the iterated derivative with the multiplier family.
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Work.Diff.STE.fourierCoeff_pdVec j l f hf' hper m,
    dmulV_ofFn j l (Work.Diff.STE.fourierCoeff f) m]

end

end Work.Diff.STE.flat
