import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.star_seriesFun

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the Friedrichs truncation `STruncR` -- finite support, expansion, continuity

`Work.Diff.STE.B3Data.STruncR ρ ε f` is the Friedrichs truncation of a coefficient function `f`:
the (real part of the) Fourier series whose `m`-th coefficient is `ρ (ε • m)` times the `m`-th
Fourier coefficient of the *periodisation* `Σ_k f (· + k)` of `f` (that coefficient family is
`Work.Diff.STE.B3.perCoeff f`).

This file collects the elementary facts about it which do not use any manifold structure and are
used by the B3 layer (`BPair_J_self` and the delegated `B3/STruncR_selfadjoint`):

* `truncBox ε`: the finite box `∏ᵢ [-⌈√2/ε⌉, ⌈√2/ε⌉]` of integer frequencies;
* `trunc_eq_zero_of_notMem_truncBox`: if `ρ y = 0` for `2 < ∑ᵢ yᵢ²` and `ε > 0`, then
  `Work.Diff.STE.trunc ρ ε c m = 0` off `truncBox ε`;
* `STruncR_eq_sum`: consequently `STruncR ρ ε f` is the finite sum over `truncBox ε` of the
  characters weighted by `trunc ρ ε (perCoeff f)`;
* `continuous_STruncR`: hence `STruncR ρ ε f` is continuous;
* `star_fourierCoeff_per`: for a real `g` the coefficients of the periodisation of `g` satisfy
  `conj (ĉ m) = ĉ (-m)` (the periodisation of a real function is real).
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. The truncation is finitely supported -/

/-- The box `∏ᵢ [-⌈√2/ε⌉, ⌈√2/ε⌉]` of integer frequencies. -/
def truncBox {n : ℕ} (ε : ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ : Fin n => Finset.Icc (-⌈Real.sqrt 2 / ε⌉) ⌈Real.sqrt 2 / ε⌉)

@[simp] lemma mem_truncBox {n : ℕ} {ε : ℝ} {m : Fin n → ℤ} :
    m ∈ truncBox (n := n) ε ↔
      ∀ i : Fin n, -⌈Real.sqrt 2 / ε⌉ ≤ m i ∧ m i ≤ ⌈Real.sqrt 2 / ε⌉ := by
  simp only [truncBox, Fintype.mem_piFinset, Finset.mem_Icc]

/-- **`trunc ρ ε c` vanishes off `truncBox ε`.**  If `ρ y = 0` for `2 < ∑ᵢ yᵢ²` and `ε > 0`, then
`trunc ρ ε c m = 0` for every frequency `m` outside the finite box `truncBox ε`. -/
theorem trunc_eq_zero_of_notMem_truncBox {n : ℕ}
    (ρ : (Fin n → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin n → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (c : (Fin n → ℤ) → ℂ) :
    ∀ m ∉ truncBox (n := n) ε, Work.Diff.STE.trunc ρ ε c m = 0 := by
  intro m hm
  rw [Work.Diff.STE.trunc]
  have hNle : Real.sqrt 2 / ε ≤ ((⌈Real.sqrt 2 / ε⌉ : ℤ) : ℝ) := Int.le_ceil _
  have hcoord : ρ (ε • fun i => (m i : ℝ)) ≠ 0 →
      ∀ i : Fin n, |(m i : ℝ)| ≤ ((⌈Real.sqrt 2 / ε⌉ : ℤ) : ℝ) := by
    intro hne i
    have hsum : (∑ j, ((ε • fun j => (m j : ℝ)) j) ^ 2) ≤ 2 := by
      by_contra hgt
      push Not at hgt
      exact hne (hρ0 _ hgt)
    have hterm : ((ε • fun j => (m j : ℝ)) i) ^ 2 ≤ 2 :=
      le_trans (Finset.single_le_sum
        (f := fun j : Fin n => ((ε • fun j => (m j : ℝ)) j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)) hsum
    have h3 : (|ε * (m i : ℝ)|) ^ 2 ≤ (Real.sqrt 2) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sq_abs]
      simpa only [Pi.smul_apply, smul_eq_mul] using hterm
    have h4 : |ε * (m i : ℝ)| ≤ Real.sqrt 2 := by
      have h := sq_le_sq.mp h3
      simpa only [abs_of_nonneg (Real.sqrt_nonneg 2), abs_abs] using h
    rw [abs_mul, abs_of_pos hε] at h4
    have h5 : |(m i : ℝ)| ≤ Real.sqrt 2 / ε := by
      rw [le_div_iff₀ hε]; linarith
    exact le_trans h5 hNle
  have hρ : ρ (ε • fun i => (m i : ℝ)) = 0 := by
    by_contra hne
    refine hm ((mem_truncBox (n := n) (ε := ε)).mpr fun i => ?_)
    have hi := hcoord hne i
    have hlow : ((-⌈Real.sqrt 2 / ε⌉ : ℤ) : ℝ) ≤ (m i : ℝ) := by
      have := (abs_le.mp hi).1; push_cast; linarith
    have hup : (m i : ℝ) ≤ ((⌈Real.sqrt 2 / ε⌉ : ℤ) : ℝ) := (abs_le.mp hi).2
    exact ⟨Int.cast_le.mp hlow, Int.cast_le.mp hup⟩
  rw [hρ, Complex.ofReal_zero, zero_mul]

/-- **`trunc ρ ε c` is finitely supported.** -/
theorem exists_finset_trunc_eq_zero {n : ℕ}
    (ρ : (Fin n → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin n → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (c : (Fin n → ℤ) → ℂ) :
    ∃ S : Finset (Fin n → ℤ), ∀ m ∉ S, Work.Diff.STE.trunc ρ ε c m = 0 :=
  ⟨truncBox ε, trunc_eq_zero_of_notMem_truncBox ρ ε hε hρ0 c⟩

/-! ## 2. `STruncR` as a finite sum of characters -/

/-- The Fourier coefficients of the *periodisation* `Σ_k f (· + k)` of `f`. -/
def perCoeff (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) : (Fin (Module.finrank ℝ E) → ℤ) → ℂ :=
  Work.Diff.STE.fourierCoeff fun y =>
    ∑' k : Fin (Module.finrank ℝ E) → ℤ, ((f (y + Work.Diff.STE.iVec k) : ℝ) : ℂ)

/-- **`STruncR` is a finite sum of characters.** -/
theorem STruncR_eq_sum
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) :
    ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      Work.Diff.STE.B3Data.STruncR ρ ε f z
        = ∑ m ∈ truncBox (n := Module.finrank ℝ E) ε,
            (Work.Diff.STE.trunc ρ ε (perCoeff f) m
              * Work.Diff.STE.fourierExp m z).re := by
  intro z
  have hS := trunc_eq_zero_of_notMem_truncBox (n := Module.finrank ℝ E) ρ ε hε hρ0 (perCoeff f)
  have h1 : Work.Diff.STE.B3Data.STruncR ρ ε f z
      = (∑' m : Fin (Module.finrank ℝ E) → ℤ,
          Work.Diff.STE.trunc ρ ε (perCoeff f) m * Work.Diff.STE.fourierExp m z).re := rfl
  rw [h1, tsum_eq_sum (s := truncBox (n := Module.finrank ℝ E) ε)
      (f := fun m => Work.Diff.STE.trunc ρ ε (perCoeff f) m
        * Work.Diff.STE.fourierExp m z) (fun m hm => by rw [hS m hm, zero_mul]),
    Complex.re_sum]

/-! ## 3. Continuity of `STruncR` -/

lemma continuous_fourierExp (m : Fin (Module.finrank ℝ E) → ℤ) :
    Continuous (Work.Diff.STE.fourierExp m) := by
  unfold Work.Diff.STE.fourierExp
  fun_prop

/-- **`STruncR ρ ε f` is continuous** (it is a finite sum of characters). -/
theorem continuous_STruncR
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) :
    Continuous (Work.Diff.STE.B3Data.STruncR ρ ε f) := by
  refine Continuous.congr ?_ fun z => (STruncR_eq_sum ρ ε hε hρ0 f z).symm
  refine continuous_finsetSum (truncBox (n := Module.finrank ℝ E) ε) fun m _ => ?_
  have hc : Continuous fun z : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.trunc ρ ε (perCoeff f) m * Work.Diff.STE.fourierExp m z :=
    continuous_const.mul (continuous_fourierExp m)
  exact Complex.continuous_re.comp hc

/-! ## 4. Reality of the Fourier coefficients of a periodisation -/

/-- **The periodisation of a real function has conjugate-symmetric Fourier coefficients.**
Conjugating the `m`-th Fourier coefficient of the periodisation of a real `g` gives the `(-m)`-th
coefficient, because the periodisation itself is real-valued. -/
theorem star_fourierCoeff_per {n : ℕ} (g : (Fin n → ℝ) → ℝ) (m : Fin n → ℤ) :
    star (Work.Diff.STE.fourierCoeff (fun y => ∑' k : Fin n → ℤ,
        ((g (y + Work.Diff.STE.iVec k) : ℝ) : ℂ)) m)
      = Work.Diff.STE.fourierCoeff (fun y => ∑' k : Fin n → ℤ,
        ((g (y + Work.Diff.STE.iVec k) : ℝ) : ℂ)) (-m) := by
  have hreal : ∀ y : Fin n → ℝ,
      star (∑' k : Fin n → ℤ, ((g (y + Work.Diff.STE.iVec k) : ℝ) : ℂ))
        = ∑' k : Fin n → ℤ, ((g (y + Work.Diff.STE.iVec k) : ℝ) : ℂ) := by
    intro y
    rw [tsum_star]
    exact tsum_congr fun k => Complex.conj_ofReal _
  rw [Work.Diff.STE.fourierCoeff, Work.Diff.STE.fourierCoeff]
  rw [show star (∫ x in Work.Diff.STE.unitCube (ι := Fin n), Work.Diff.STE.fourierExp (-m) x *
        (∑' k : Fin n → ℤ, ((g (x + Work.Diff.STE.iVec k) : ℝ) : ℂ)))
      = (starRingEnd ℂ) (∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          Work.Diff.STE.fourierExp (-m) x *
            (∑' k : Fin n → ℤ, ((g (x + Work.Diff.STE.iVec k) : ℝ) : ℂ))) from rfl,
    ← integral_conj (μ := volume.restrict (Work.Diff.STE.unitCube (ι := Fin n)))
      (f := fun x : Fin n → ℝ => Work.Diff.STE.fourierExp (-m) x *
        (∑' k : Fin n → ℤ, ((g (x + Work.Diff.STE.iVec k) : ℝ) : ℂ)))]
  apply integral_congr_ae
  filter_upwards with x
  change star (Work.Diff.STE.fourierExp (-m) x *
      (∑' k : Fin n → ℤ, ((g (x + Work.Diff.STE.iVec k) : ℝ) : ℂ)))
    = Work.Diff.STE.fourierExp (-(-m)) x *
      (∑' k : Fin n → ℤ, ((g (x + Work.Diff.STE.iVec k) : ℝ) : ℂ))
  rw [star_mul, Work.Diff.STE.star_fourierExp, hreal x, neg_neg, mul_comm]

end Work.Diff.STE.B3
