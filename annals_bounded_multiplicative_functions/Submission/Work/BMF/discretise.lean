import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.exists_grid_shift
import Submission.Work.BMF.level_set_measure

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Discretisation of the local Gowers norm hypothesis

This file proves MRT (Fourier) Lemma 2.1 in the polynomial-phase setting of MRTTZ:
from the hypothesis `∫_X^{2X} ‖f‖_{u^{k+1}[x,x+H]} ≥ ηX` one extracts a large `(X,H)`-family
of intervals, each carrying a degree-`≤ k` polynomial phase with which `f` correlates.

It also contains the elementary alignment lemmas identifying the challenge's
`weakGowersUniformityNorm k x H f.intExtension` with the `corr`-based supremum used by the
downstream nodes.
-/

open Classical
open Polynomial Finset Real Complex MeasureTheory
open BoundedMultiplicativeFunctions

namespace Work.BMF

/-! ## Alignment of the challenge integrand with `corr` -/

lemma sum_Icc_eq_natIcc (f : ℕ → ℂ) (g : ℤ → ℂ) (hg : ∀ n : ℤ, 0 ≤ n → g n = f n.toNat)
    (w : ℤ → ℂ) (x H : ℝ) (hx : 0 ≤ x) (hH : 0 ≤ H) :
    (∑ n ∈ Finset.Icc ⌈x⌉ ⌊x + H⌋, g n * w n) = ∑ m ∈ natIcc x (x + H), f m * w (m : ℤ) := by
  rw [natIcc]
  refine Finset.sum_bij' (fun n _ => n.toNat) (fun m _ => (m : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · rw [← Int.ceil_toNat x]
      exact Int.toNat_le_toNat h1
    · rw [← Int.floor_toNat (x + H)]
      exact Int.toNat_le_toNat h2
  · intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
    have hxH : 0 ≤ x + H := add_nonneg hx hH
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · rw [← Int.natCast_ceil_eq_ceil hx]
      exact_mod_cast h1
    · rw [← Int.natCast_floor_eq_floor hxH]
      exact_mod_cast h2
  · intro n hn
    obtain ⟨h1, _⟩ := Finset.mem_Icc.mp hn
    exact Int.toNat_of_nonneg (le_trans (Int.ceil_nonneg hx) h1)
  · intro m hm
    exact Int.toNat_natCast m
  · intro n hn
    obtain ⟨h1, _⟩ := Finset.mem_Icc.mp hn
    have h0n : 0 ≤ n := le_trans (Int.ceil_nonneg hx) h1
    rw [hg n h0n]
    exact congrArg (fun z => f n.toNat * w z) (Int.toNat_of_nonneg h0n).symm

/-- The challenge's `u^{k+1}`-norm is the supremum of the `corr`-correlations over degree-`≤ k`
polynomial phases, for `x ≥ 0`. -/
theorem weakGowers_eq_iSup_corr (k : ℕ) (f : ℕ → ℂ) (g : ℤ → ℂ)
    (hg : ∀ n : ℤ, 0 ≤ n → g n = f n.toNat)
    (x H : ℝ) (hx : 0 ≤ x) (hH : 0 ≤ H) :
    weakGowersUniformityNorm k x H g = ⨆ P ∈ degreeLE ℝ (k : WithBot ℕ), 1 / H * ‖corr f P x H‖ := by
  have key : ∀ P : ℝ[X], corr f P x H
      = ∑ n ∈ Finset.Icc ⌈x⌉ ⌊x + H⌋, g n * eC (-(P.eval (n : ℝ))) :=
    fun P => (sum_Icc_eq_natIcc f g hg (fun n => eC (-(P.eval (n : ℝ)))) x H hx hH).symm
  unfold weakGowersUniformityNorm
  refine iSup_congr (fun P => iSup_congr (fun _ => ?_))
  rw [key P]
  simp only [eC, Complex.ofReal_neg]

/-! ## The norm is measurable and depends on `(⌈x⌉, ⌊x+H⌋)` only -/

/-- The norm depends on `x` only through `(⌈x⌉, ⌊x+H⌋)`. -/
noncomputable def wguStep (k : ℕ) (H : ℝ) (g : ℤ → ℂ) (ab : ℤ × ℤ) : ℝ :=
  ⨆ P ∈ degreeLE ℝ (k : WithBot ℕ),
    1 / H * ‖∑ n ∈ Finset.Icc ab.1 ab.2, g n * eC (-(P.eval (n : ℝ)))‖

theorem weakGowers_eq_wguStep (k : ℕ) (H : ℝ) (g : ℤ → ℂ) (x : ℝ) :
    weakGowersUniformityNorm k x H g = wguStep k H g (⌈x⌉, ⌊x + H⌋) := by
  simp only [weakGowersUniformityNorm, wguStep, eC, Complex.ofReal_neg]

lemma measurable_wguStep (k : ℕ) (H : ℝ) (g : ℤ → ℂ) : Measurable (wguStep k H g) :=
  measurable_of_countable _

lemma measurable_weakGowers (k : ℕ) (H : ℝ) (g : ℤ → ℂ) :
    Measurable (fun x : ℝ => weakGowersUniformityNorm k x H g) := by
  have h : Measurable (fun x : ℝ => (wguStep k H g) (⌈x⌉, ⌊x + H⌋)) :=
    (measurable_wguStep k H g).comp
      (Measurable.prodMk Int.measurable_ceil
        (Int.measurable_floor.comp (measurable_id.add measurable_const)))
  simpa only [weakGowers_eq_wguStep] using h

/-! ## Supremum lemmas over `degreeLE` -/

lemma iSup_Poly_le {k : ℕ} {v : ℝ[X] → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ P ∈ degreeLE ℝ (k : WithBot ℕ), v P ≤ c) :
    (⨆ P ∈ degreeLE ℝ (k : WithBot ℕ), v P) ≤ c := by
  apply ciSup_le
  intro P
  by_cases hP : P ∈ degreeLE ℝ (k : WithBot ℕ)
  · rw [ciSup_pos hP]; exact h P hP
  · rw [ciSup_neg hP, Real.sSup_empty]; exact hc

lemma exists_of_lt_iSup_Poly {k : ℕ} {v : ℝ[X] → ℝ} {a : ℝ} (hv : ∀ P, 0 ≤ v P)
    (h : a < ⨆ P ∈ degreeLE ℝ (k : WithBot ℕ), v P) :
    ∃ P ∈ degreeLE ℝ (k : WithBot ℕ), a < v P := by
  by_cases ha : a < 0
  · exact ⟨0, Submodule.zero_mem _, lt_of_lt_of_le ha (hv 0)⟩
  · push Not at ha
    by_contra hc
    push Not at hc
    have h2 : (⨆ P ∈ degreeLE ℝ (k : WithBot ℕ), v P) ≤ a := iSup_Poly_le ha hc
    exact absurd (lt_of_lt_of_le h h2) (lt_irrefl a)

lemma le_iSup_Poly {k : ℕ} {v : ℝ[X] → ℝ} {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ P ∈ degreeLE ℝ (k : WithBot ℕ), v P ≤ c) (P₀ : ℝ[X])
    (hP₀ : P₀ ∈ degreeLE ℝ (k : WithBot ℕ)) :
    v P₀ ≤ ⨆ P ∈ degreeLE ℝ (k : WithBot ℕ), v P := by
  have hbdd : BddAbove (Set.range
      (fun P : ℝ[X] => ⨆ (_ : P ∈ degreeLE ℝ (k : WithBot ℕ)), v P)) := by
    refine ⟨c, ?_⟩
    rintro y ⟨P, rfl⟩
    dsimp only
    by_cases hP : P ∈ degreeLE ℝ (k : WithBot ℕ)
    · rw [ciSup_pos hP]; exact hc P hP
    · rw [ciSup_neg hP, Real.sSup_empty]; exact hc0
  have h1 : (⨆ (_ : P₀ ∈ degreeLE ℝ (k : WithBot ℕ)), v P₀) = v P₀ := ciSup_pos hP₀
  calc v P₀ = ⨆ (_ : P₀ ∈ degreeLE ℝ (k : WithBot ℕ)), v P₀ := h1.symm
    _ ≤ ⨆ P, ⨆ (_ : P ∈ degreeLE ℝ (k : WithBot ℕ)), v P := le_ciSup hbdd P₀

/-! ## Elementary bounds -/

/-- The correlation is bounded by the number of terms. -/
lemma norm_corr_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (P : ℝ[X]) (x L : ℝ)
    (hx : 0 ≤ x) (hL : 0 ≤ L) : ‖corr f P x L‖ ≤ L + 2 := by
  have hcard : ((natIcc x (x + L)).card : ℝ) ≤ L + 2 := by
    have hb_le : ((⌊x + L⌋₊ : ℕ) : ℝ) ≤ (⌈x⌉₊ : ℝ) + L := by
      have h1 : ((⌊x + L⌋₊ : ℕ) : ℝ) ≤ x + L := Nat.floor_le (by linarith)
      have h2 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
      linarith
    have h : ((natIcc x (x + L)).card : ℝ) ≤ L + 1 := by
      rw [natIcc, Nat.card_Icc]
      by_cases hc : (⌈x⌉₊ : ℕ) ≤ ⌊x + L⌋₊ + 1
      · rw [Nat.cast_sub hc]; push_cast; linarith
      · rw [Nat.sub_eq_zero_of_le (by omega)]; simp; linarith
    linarith
  rw [corr]
  calc ‖∑ n ∈ natIcc x (x + L), f n * eC (-(P.eval (n : ℝ)))‖
      ≤ ∑ n ∈ natIcc x (x + L), ‖f n * eC (-(P.eval (n : ℝ)))‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ natIcc x (x + L), (1 : ℝ) := by
        refine sum_le_sum (fun n _ => ?_)
        rw [norm_mul]
        have h1 : ‖eC (-(P.eval (n : ℝ)))‖ = 1 := by
          simp only [eC, Complex.norm_exp]; simp
        rw [h1, mul_one]
        exact hf n
    _ = ((natIcc x (x + L)).card : ℝ) := by simp
    _ ≤ L + 2 := hcard

/-- The number of integers in `[⌈x⌉, ⌊x+H⌋]` is at most `H + 2`. -/
lemma card_Icc_ceil_floor_le (x H : ℝ) (hH : 0 ≤ H) :
    ((Finset.Icc ⌈x⌉ ⌊x + H⌋).card : ℝ) ≤ H + 2 := by
  have h1 : ((⌊x + H⌋ : ℤ) : ℝ) ≤ x + H := Int.floor_le _
  have h2 : x ≤ ((⌈x⌉ : ℤ) : ℝ) := Int.le_ceil x
  have h4 : ((⌈H⌉₊ : ℕ) : ℝ) ≥ H := Nat.le_ceil H
  have h3 : (⌊x + H⌋ : ℤ) < ⌈x⌉ + (⌈H⌉₊ : ℤ) + 1 := by
    rw [← Int.cast_lt (R := ℝ)]; push_cast; linarith
  have h5 : (⌊x + H⌋ : ℤ) ≤ ⌈x⌉ + (⌈H⌉₊ : ℤ) := Int.le_of_lt_add_one h3
  have h6 : (⌊x + H⌋ + 1 - ⌈x⌉ : ℤ) ≤ ((⌈H⌉₊ : ℕ) : ℤ) + 1 := by omega
  calc (((Finset.Icc ⌈x⌉ ⌊x + H⌋).card : ℕ) : ℝ)
      = (((⌊x + H⌋ + 1 - ⌈x⌉ : ℤ).toNat : ℕ) : ℝ) := by rw [Int.card_Icc]
    _ ≤ (((⌈H⌉₊ : ℕ) + 1 : ℕ) : ℝ) := by
        have := Int.toNat_le.mpr h6; exact_mod_cast this
    _ ≤ H + 2 := by
        have := Nat.ceil_lt_add_one hH
        push_cast; linarith

/-- A single polynomial exponential sum is bounded by the number of terms. -/
lemma norm_sum_cexp_le_card (g : ℤ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (P : ℝ[X]) (a b : ℤ) :
    ‖∑ n ∈ Finset.Icc a b, g n * cexp (2 * π * I * -P.eval (n : ℝ))‖
      ≤ ((Finset.Icc a b).card : ℝ) := by
  calc ‖∑ n ∈ Finset.Icc a b, g n * cexp (2 * π * I * -P.eval (n : ℝ))‖
      ≤ ∑ n ∈ Finset.Icc a b, ‖g n * cexp (2 * π * I * -P.eval (n : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc a b, (1 : ℝ) := by
        refine sum_le_sum (fun n _ => ?_)
        rw [norm_mul]
        have h : ‖cexp (2 * π * I * -P.eval (n : ℝ))‖ = 1 := by
          rw [Complex.norm_exp]
          have hh : (2 * (π:ℂ) * I * -(P.eval (n:ℝ))).re = 0 := by
            simp [Complex.mul_re, Complex.mul_im]
          rw [hh, Real.exp_zero]
        rw [h, mul_one]
        exact hg n
    _ = ((Finset.Icc a b).card : ℝ) := by simp

/-- The `u^{k+1}`-norm of a 1-bounded sequence is at most `3` for `H ≥ 1`. -/
lemma weakGowers_le_three (k : ℕ) (H : ℝ) (hH : 1 ≤ H) (g : ℤ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (x : ℝ) : weakGowersUniformityNorm k x H g ≤ 3 := by
  have hH0 : (0:ℝ) < H := by linarith
  unfold weakGowersUniformityNorm
  apply ciSup_le
  intro P
  by_cases hP : P ∈ degreeLE ℝ (k : WithBot ℕ)
  · rw [ciSup_pos hP]
    have h1 := norm_sum_cexp_le_card g hg P ⌈x⌉ ⌊x + H⌋
    have h2 := card_Icc_ceil_floor_le x H (le_of_lt hH0)
    calc 1 / H * ‖∑ n ∈ Finset.Icc ⌈x⌉ ⌊x + H⌋, g n * cexp (2 * π * I * -P.eval (n : ℝ))‖
        ≤ 1 / H * ((Finset.Icc ⌈x⌉ ⌊x + H⌋).card : ℝ) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 3 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hH0]; linarith
  · rw [ciSup_neg hP, Real.sSup_empty]; norm_num

/-- The `u^{k+1}`-norm of a 1-bounded sequence is nonnegative for `H > 0`. -/
lemma weakGowers_nonneg (k : ℕ) (H : ℝ) (hH : 0 < H) (g : ℤ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (x : ℝ) : 0 ≤ weakGowersUniformityNorm k x H g := by
  have hval : ∀ P ∈ degreeLE ℝ (k : WithBot ℕ),
      1 / H * ‖∑ n ∈ Finset.Icc ⌈x⌉ ⌊x + H⌋, g n * cexp (2 * π * I * -P.eval (n : ℝ))‖ ≤ (H + 2) / H := by
    intro P _
    have h1 := norm_sum_cexp_le_card g hg P ⌈x⌉ ⌊x + H⌋
    have h2 := card_Icc_ceil_floor_le x H (le_of_lt hH)
    calc 1 / H * ‖∑ n ∈ Finset.Icc ⌈x⌉ ⌊x + H⌋, g n * cexp (2 * π * I * -P.eval (n : ℝ))‖
        ≤ 1 / H * ((Finset.Icc ⌈x⌉ ⌊x + H⌋).card : ℝ) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (H + 2) / H := by
          rw [div_mul_eq_mul_div, one_mul]
          exact div_le_div_of_nonneg_right h2 (le_of_lt hH)
  have hb := le_iSup_Poly (k := k)
    (v := fun P : ℝ[X] => 1 / H * ‖∑ n ∈ Finset.Icc ⌈x⌉ ⌊x + H⌋, g n * cexp (2 * π * I * -P.eval (n : ℝ))‖)
    (c := (H + 2) / H) (by positivity) hval (0 : ℝ[X]) (Submodule.zero_mem _)
  have h0 : (0:ℝ) ≤ 1 / H * ‖∑ n ∈ Finset.Icc ⌈x⌉ ⌊x + H⌋, g n * cexp (2 * π * I * -(0 : ℝ[X]).eval (n : ℝ))‖ := by
    positivity
  calc (0:ℝ) ≤ _ := h0
    _ ≤ _ := hb
    _ = weakGowersUniformityNorm k x H g := by rw [weakGowersUniformityNorm]

/-! ## Discretisation -/

/-- **Discretisation (MRT Fourier, Lemma 2.1, polynomial-phase form).** From
`∫_X^{2X} ‖f‖_{u^{k+1}[x,x+H]} ≥ ηX` with `H ≥ X^θ` one extracts a family `S` of left endpoints
in `[X, 2X]`, `500H`-separated, of cardinality `≫ X/H`, each carrying a degree-`≤ k` phase
correlating with `f` at the scale `H`. -/
theorem discretise (k : ℕ) (θ η : ℝ) (hθ : 0 < θ) (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∀ (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (X H : ℝ),
      1 ≤ X → 1 ≤ H → X ^ θ ≤ H → H ≤ X →
      η * X ≤ ∫ x in X..(2 * X), weakGowersUniformityNorm k x H (fun z : ℤ ↦ f ⌊z⌋₊) →
      ∃ S : Finset ℝ, (∀ x ∈ S, X ≤ x ∧ x ≤ 2 * X) ∧
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 500 * H ≤ |x - y|) ∧
        c * (X / H) ≤ (S.card : ℝ) ∧
        ∀ x ∈ S, ∃ P : ℝ[X], P ∈ degreeLE ℝ (k : WithBot ℕ) ∧ c * H ≤ ‖corr f P x H‖ := by
  refine ⟨η / 20000, by positivity, ?_⟩
  intro f hf X H hX hH hXθ hHX hint
  have hX0 : (0:ℝ) ≤ X := by linarith
  have hH0 : (0:ℝ) < H := by linarith
  have hmeas : Measurable (fun x : ℝ => weakGowersUniformityNorm k x H (fun z : ℤ ↦ f ⌊z⌋₊)) :=
    measurable_weakGowers k H _
  have hg1 : ∀ n : ℤ, ‖(fun z : ℤ ↦ f ⌊z⌋₊) n‖ ≤ 1 := by
    intro n
    show ‖f ⌊n⌋₊‖ ≤ 1
    rw [← Int.floor_toNat n]
    exact hf n.toNat
  have hle3 : ∀ x, weakGowersUniformityNorm k x H (fun z : ℤ ↦ f ⌊z⌋₊) ≤ 3 :=
    fun x => weakGowers_le_three k H hH _ hg1 x
  have hnn : ∀ x, 0 ≤ weakGowersUniformityNorm k x H (fun z : ℤ ↦ f ⌊z⌋₊) :=
    fun x => weakGowers_nonneg k H hH0 _ hg1 x
  set A : Set ℝ := {x : ℝ | η / 2 ≤ weakGowersUniformityNorm k x H (fun z : ℤ ↦ f ⌊z⌋₊)}
    ∩ Set.Ioc X (2 * X) with hA
  have hvol : η * X / 6 ≤ (volume A).toReal := by
    rw [hA]
    exact level_set_measure _ η X hmeas hη hX0 hnn hle3 hint
  have hAmeas : MeasurableSet A := by
    rw [hA]; exact (measurableSet_le measurable_const hmeas).inter measurableSet_Ioc
  have hAsub : A ⊆ Set.Ioc X (2 * X) := by rw [hA]; exact Set.inter_subset_right
  set N : ℕ := ⌈2 * X / (500 * H)⌉₊ + 1 with hN
  have hAsubN : ∀ x ∈ A, 0 ≤ x ∧ x < N * (500 * H) := by
    intro x hx
    have hx' : x ∈ Set.Ioc X (2 * X) := hAsub hx
    have h2 : (0:ℝ) < 500 * H := by linarith
    have hNge : (2 * X / (500 * H)) < (N : ℝ) := by
      rw [hN]; push_cast
      have := Nat.le_ceil (2 * X / (500 * H))
      linarith
    have h3 : (2 * X / (500 * H)) * (500 * H) = 2 * X := by field_simp
    have h4 : 2 * X < (N : ℝ) * (500 * H) := by
      have := mul_lt_mul_of_pos_right hNge h2
      rwa [h3] at this
    exact ⟨by linarith [hx'.1, hX], by linarith [hx'.2, h4]⟩
  obtain ⟨y, hyI, hyineq⟩ := exists_grid_shift A (500 * H) (by linarith) hAmeas N hAsubN
  refine ⟨((Finset.range N).filter (fun ℓ : ℕ => ((ℓ : ℝ) * (500 * H) + y) ∈ A)).image
      (fun ℓ : ℕ => (ℓ : ℝ) * (500 * H) + y), ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp hx
    have hxA := (Finset.mem_filter.mp hℓ).2
    exact ⟨le_of_lt (hAsub hxA).1, (hAsub hxA).2⟩
  · intro x hx z hz hxz
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨m, hm, hmz⟩ := Finset.mem_image.mp hz
    have hne : ℓ ≠ m := by
      intro h; exact hxz (by rw [h, hmz])
    have h500 : (0:ℝ) < 500 * H := by linarith
    have habs : (1:ℝ) ≤ |(ℓ:ℝ) - (m:ℝ)| := by
      rcases lt_or_gt_of_ne hne with h | h
      · have h' : ((m:ℝ)) ≥ (ℓ:ℝ) + 1 := by
          have : ℓ + 1 ≤ m := h; exact_mod_cast this
        rw [abs_of_nonpos (by linarith)]; linarith
      · have h' : ((ℓ:ℝ)) ≥ (m:ℝ) + 1 := by
          have : m + 1 ≤ ℓ := h; exact_mod_cast this
        rw [abs_of_nonneg (by linarith)]; linarith
    rw [← hmz]
    have hrw : (ℓ:ℝ) * (500*H) + y - ((m:ℝ) * (500*H) + y) = ((ℓ:ℝ) - (m:ℝ)) * (500*H) := by
      ring
    rw [hrw, abs_mul]
    have h2 : |(500:ℝ) * H| = 500 * H := abs_of_nonneg (by linarith)
    rw [h2]
    nlinarith [abs_nonneg ((ℓ:ℝ) - (m:ℝ))]
  · have hcardT : (↑((Finset.range N).filter (fun ℓ : ℕ => ((ℓ:ℝ)*(500*H) + y) ∈ A)).card : ℝ)
        = ∑ ℓ ∈ Finset.range N, A.indicator (fun _ => (1:ℝ)) ((ℓ:ℝ)*(500*H) + y) := by
      rw [Finset.card_filter]; push_cast
      refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      by_cases hh : ((ℓ:ℝ)*(500*H) + y) ∈ A
      · rw [Set.indicator_of_mem hh]; simp [hh]
      · rw [Set.indicator_of_notMem hh]; simp [hh]
    have hcardS : (↑(((Finset.range N).filter (fun ℓ : ℕ => ((ℓ:ℝ)*(500*H) + y) ∈ A)).image
          (fun ℓ : ℕ => (ℓ : ℝ) * (500 * H) + y)).card : ℝ)
        = ↑((Finset.range N).filter (fun ℓ : ℕ => ((ℓ:ℝ)*(500*H) + y) ∈ A)).card := by
      rw [Finset.card_image_of_injective]
      intro a b hab
      have h500 : (0:ℝ) < 500 * H := by linarith
      have h1 : (a:ℝ) * (500*H) = (b:ℝ) * (500*H) := by linarith
      have h2 : (a:ℝ) = (b:ℝ) := mul_right_cancel₀ (ne_of_gt h500) h1
      exact_mod_cast h2
    rw [hcardS, hcardT]
    have hstep : η * X / 6 / (500 * H)
        ≤ ∑ ℓ ∈ Finset.range N, A.indicator (fun _ => (1:ℝ)) ((ℓ:ℝ)*(500*H) + y) :=
      le_trans (div_le_div_of_nonneg_right hvol (by linarith)) hyineq
    have htarget : η / 20000 * (X / H) ≤ η * X / 6 / (500 * H) := by
      have e1 : η / 20000 * (X / H) = η * X / (20000 * H) := by ring
      have e2 : η * X / 6 / (500 * H) = η * X / (3000 * H) := by ring
      rw [e1, e2]
      apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
    linarith
  · intro x hx
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp hx
    have hxA := (Finset.mem_filter.mp hℓ).2
    have hxF : η / 2 ≤ weakGowersUniformityNorm k ((ℓ:ℝ)*(500*H) + y) H (fun z : ℤ ↦ f ⌊z⌋₊) :=
      hxA.1
    have hx0 : (0:ℝ) ≤ (ℓ:ℝ)*(500*H) + y := le_trans hX0 (le_of_lt (hAsub hxA).1)
    have hrew := weakGowers_eq_iSup_corr k f (fun z : ℤ ↦ f ⌊z⌋₊) (fun n _ => by rw [← Int.floor_toNat n]; simp)
      ((ℓ:ℝ)*(500*H) + y) H hx0 (le_of_lt hH0)
    rw [hrew] at hxF
    obtain ⟨P, hP, hPv⟩ := exists_of_lt_iSup_Poly (k := k)
      (v := fun P : ℝ[X] => 1 / H * ‖corr f P ((ℓ:ℝ)*(500*H) + y) H‖)
      (a := η / 4) (fun P => by positivity) (by linarith)
    refine ⟨P, hP, ?_⟩
    have hv' : η / 4 * H < ‖corr f P ((ℓ:ℝ)*(500*H) + y) H‖ := by
      rw [show (1:ℝ)/H * ‖corr f P ((ℓ:ℝ)*(500*H) + y) H‖
            = ‖corr f P ((ℓ:ℝ)*(500*H) + y) H‖ / H from by ring, lt_div_iff₀ hH0] at hPv
      linarith
    calc η / 20000 * H ≤ η / 4 * H := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hH0)
          apply div_le_div_of_nonneg_left (le_of_lt hη) (by norm_num) (by norm_num)
      _ ≤ ‖corr f P ((ℓ:ℝ)*(500*H) + y) H‖ := le_of_lt hv'

end Work.BMF

namespace Work.BMF

/-- The output of `discretise` is a `PhaseFamily`: the extracted intervals lie in `[X, 2X]` and
are `500H`-separated, so they form an `(X,H)`-family. -/
lemma phaseFamily_of_discretise (k : ℕ) (f : ℕ → ℂ) (c X H : ℝ) (S : Finset ℝ)
    (pol : ℝ → ℝ[X]) (hX : 1 ≤ X) (hH : 1 ≤ H) (hHX : H ≤ X)
    (h1 : ∀ x ∈ S, X ≤ x ∧ x ≤ 2 * X)
    (h2 : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 500 * H ≤ |x - y|)
    (h3 : c * (X / H) ≤ (S.card : ℝ))
    (h4 : ∀ x ∈ S, pol x ∈ degreeLE ℝ (k : WithBot ℕ))
    (h5 : ∀ x ∈ S, c * H ≤ ‖corr f (pol x) x H‖) :
    ∃ F : PhaseFamily k f c X H, F.fam = S := by
  refine ⟨⟨S, pol, ?_, h3, h4, h5⟩, rfl⟩
  refine ⟨fun x hx => ⟨?_, ?_⟩, h2⟩
  · have := (h1 x hx).1; linarith
  · have := (h1 x hx).2
    have hH0 : 0 ≤ H := by linarith
    have hHX0 : H ≤ X := by linarith
    linarith

/-- `discretise` produces, for each extracted interval, *some* degree-`≤ k` phase; choose one for
each. -/
lemma phaseFamily_of_discretise_exists (k : ℕ) (f : ℕ → ℂ) (c X H : ℝ) (S : Finset ℝ)
    (hX : 1 ≤ X) (hH : 1 ≤ H) (hHX : H ≤ X)
    (h1 : ∀ x ∈ S, X ≤ x ∧ x ≤ 2 * X)
    (h2 : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 500 * H ≤ |x - y|)
    (h3 : c * (X / H) ≤ (S.card : ℝ))
    (h4 : ∀ x ∈ S, ∃ P ∈ degreeLE ℝ (k : WithBot ℕ), c * H ≤ ‖corr f P x H‖) :
    ∃ F : PhaseFamily k f c X H, F.fam = S := by
  classical
  choose pol hpol using h4
  refine phaseFamily_of_discretise k f c X H S
    (fun x => if hx : x ∈ S then pol x hx else 0) hX hH hHX h1 h2 h3 ?_ ?_
  · intro x hx
    rw [dif_pos hx]
    exact (hpol x hx).1
  · intro x hx
    rw [dif_pos hx]
    exact (hpol x hx).2

end Work.BMF
