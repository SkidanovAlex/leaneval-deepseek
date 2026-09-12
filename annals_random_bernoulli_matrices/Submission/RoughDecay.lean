import Mathlib
import Submission.IntFun
import Submission.Sec3Core
import Submission.Sec3Tower
import Submission.AuxSimpleAc

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Section 3: Proposition p:rough decay (union-bound layer)

Tikhomirov 2020, Section 3, Proposition `p: rough decay`.  On top of
`Submission.Sec3Tower` (the deterministic descendant containment
`descendant_nondecay`, Lemma l:aux 09019847294) this module develops the
probabilistic layer: a counting bound over the uniform product family
`x ∈ A₁ × … × A_ℓ` of the event that the averaged function
`f_{A,p,ℓ} = avgF f p ℓ x` is large.

Content (in order):
- counting: points where a mass-≤1 nonnegative summable function exceeds a
  threshold, and the product/sumset cardinality bounds that bound the number
  of descendant starting points `D`;
- `aux_simple_ac2`: the second (interval ≥ N) form of Lemma l:aux simple ac;
- the deterministic per-step Markov bound (a step that is not a "decay" is
  unlikely);
- the union bound over descendants and subsets `I` of levels, giving
  Proposition p:rough decay (counting form).
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Measure

namespace Submission.RoughDecay

attribute [local instance] Classical.propDecidable

open Submission.IntFun
open Submission.Sec3
open Submission.Sec3Tower
open Submission.AuxSimpleAc

/-! ## 1. Counting points above a threshold -/

/-- The set of points where a nonnegative summable function exceeds a positive
level is finite. -/
lemma finite_above {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f) {θ : ℝ}
    (hθ : 0 < θ) : Set.Finite {t : ℤ | θ < f t} := by
  classical
  by_contra hnot
  let s : Set ℤ := {t : ℤ | θ < f t}
  have hinf : s.Infinite := hnot
  rcases Set.Infinite.exists_subset_card_eq hinf (⌊norm₁ f / θ⌋₊ + 1) with ⟨F, hFs, hFcard⟩
  have hbig : θ * (F.card : ℝ) > norm₁ f := by
    have hFc : (F.card : ℝ) = (⌊norm₁ f / θ⌋₊ : ℝ) + 1 := by
      rw [hFcard]
      norm_num
    rw [hFc]
    have hlt : norm₁ f / θ < (⌊norm₁ f / θ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (a := norm₁ f / θ)
    have hθnz : θ ≠ 0 := ne_of_gt hθ
    have hmul : norm₁ f < θ * ((⌊norm₁ f / θ⌋₊ : ℝ) + 1) := by
      calc
        norm₁ f = θ * (norm₁ f / θ) := by field_simp [hθnz]
        _ < θ * ((⌊norm₁ f / θ⌋₊ : ℝ) + 1) := mul_lt_mul_of_pos_left hlt hθ
    linarith
  have hsum_ge : θ * (F.card : ℝ) ≤ (∑ t ∈ F, f t) := by
    have hc : (∑ t ∈ F, θ) = θ * (F.card : ℝ) := by
      rw [Finset.sum_const]
      rw [nsmul_eq_mul]
      ring
    rw [← hc]
    apply Finset.sum_le_sum
    intro t ht
    have htm : t ∈ s := by exact (hFs ht)
    dsimp [s] at htm
    exact le_of_lt htm
  have hsum_le : (∑ t ∈ F, f t) ≤ norm₁ f := Finset_sum_le_norm₁ hfpos hf F
  nlinarith

/-- The count of points above the level `θ` is at most `‖f‖₁/θ`. -/
lemma ncard_above_le {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hf : Summable f) {θ : ℝ}
    (hθ : 0 < θ) : ((({t : ℤ | θ < f t}).ncard : ℝ) ≤ norm₁ f / θ) := by
  classical
  let s : Set ℤ := {t : ℤ | θ < f t}
  have hfin : s.Finite := finite_above hfpos hf hθ
  let F : Finset ℤ := hfin.toFinset
  have hmem : ∀ t : ℤ, t ∈ F ↔ t ∈ s := by
    intro t
    exact Set.Finite.mem_toFinset hfin
  have hcard : (s.ncard : ℝ) = (F.card : ℝ) := by
    rw [Set.ncard_eq_toFinset_card s hfin]
  have hsum_ge : θ * (F.card : ℝ) ≤ (∑ t ∈ F, f t) := by
    have hc : (∑ t ∈ F, θ) = θ * (F.card : ℝ) := by
      rw [Finset.sum_const]
      rw [nsmul_eq_mul]
      ring
    rw [← hc]
    apply Finset.sum_le_sum
    intro t ht
    have htm : t ∈ s := (hmem t).1 ht
    dsimp [s] at htm
    exact le_of_lt htm
  have hsum_le : (∑ t ∈ F, f t) ≤ norm₁ f := Finset_sum_le_norm₁ hfpos hf F
  calc
    (s.ncard : ℝ) = (F.card : ℝ) := hcard
    _ ≤ norm₁ f / θ := by
      have hstep : (F.card : ℝ) * θ ≤ (∑ t ∈ F, f t) := by simpa [mul_comm] using hsum_ge
      calc
        (F.card : ℝ) ≤ ((∑ t ∈ F, f t) / θ) := (le_div_iff₀ hθ).2 hstep
        _ ≤ norm₁ f / θ := div_le_div_of_nonneg_right hsum_le hθ.le


def win (a : ℤ) (N : ℕ) (k : ℕ) : Finset ℤ :=
  Finset.Icc (a + (k : ℤ) * (N : ℤ)) (a + (k : ℤ) * (N : ℤ) + (N : ℤ) - 1)

/-- Splitting an interval at `b`: `[a, d] = [a, b] ∪ [b+1, d]` when the pieces
are adjacent (`a ≤ b + 1` and `b + 1 ≤ d`). -/
lemma split_sum (F : ℤ → ℝ) (a b d : ℤ) (hab : a ≤ b + 1) (hbd : b + 1 ≤ d) :
    (∑ t ∈ Finset.Icc a d, F t) = (∑ t ∈ Finset.Icc a b, F t) + (∑ t ∈ Finset.Icc (b + 1) d, F t) := by
  classical
  have hunion : Finset.Icc a d = Finset.Icc a b ∪ Finset.Icc (b + 1) d := by
    ext t
    constructor
    · intro ht
      rcases Finset.mem_Icc.mp ht with ⟨h1, h2⟩
      by_cases htb : t ≤ b
      · simp [Finset.mem_union, Finset.mem_Icc, h1, htb]
      · simp [Finset.mem_union, Finset.mem_Icc, h1, htb]
        omega
    · intro ht
      rw [Finset.mem_union] at ht
      rcases ht with ht | ht
      · rcases Finset.mem_Icc.mp ht with ⟨h1, h2⟩
        exact Finset.mem_Icc.mpr ⟨h1, le_trans h2 (by omega)⟩
      · rcases Finset.mem_Icc.mp ht with ⟨h1, h2⟩
        exact Finset.mem_Icc.mpr ⟨by omega, h2⟩
  have hdisj : Disjoint (Finset.Icc a b) (Finset.Icc (b + 1) d) := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    have h1 : t ≤ b := (Finset.mem_Icc.mp ht1).2
    have h2 : b + 1 ≤ t := (Finset.mem_Icc.mp ht2).1
    omega
  rw [hunion]
  exact Finset.sum_union hdisj

lemma sum_Icc_windows {F : ℤ → ℝ} {C : ℝ} (c : ℤ) (N K : ℕ) (hN : 1 ≤ N)
    (hwin : ∀ k : ℕ, k < K → (∑ t ∈ win c N k, F t) ≤ C) :
    (∑ t ∈ Finset.Icc c (c + (K : ℤ) * (N : ℤ) - 1), F t) ≤ (K : ℝ) * C := by
  classical
  induction K with
  | zero =>
      simp
  | succ K ih =>
      let e : ℤ := c + (K : ℤ) * (N : ℤ) - 1
      have htarget : c + (K + 1 : ℕ) * (N : ℤ) - 1 = e + (N : ℤ) := by
        dsimp [e]
        norm_num
        ring
      have hprod : 0 ≤ (K : ℤ) * (N : ℤ) := by positivity
      have hsplit : (∑ t ∈ Finset.Icc c (e + (N : ℤ)), F t) =
            (∑ t ∈ Finset.Icc c e, F t) + (∑ t ∈ Finset.Icc (e + 1) (e + (N : ℤ)), F t) := by
        exact split_sum F c e (e + (N : ℤ)) (by
          have hprod : 0 ≤ (K : ℤ) * (N : ℤ) := by positivity
          dsimp [e]
          nlinarith) (by
          have hnz : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
          dsimp [e]
          nlinarith)
      have hwinlast : (∑ t ∈ Finset.Icc (e + 1) (e + (N : ℤ)), F t) ≤ C := by
        have hwin' : (∑ t ∈ win c N K, F t) ≤ C := hwin K (Nat.lt_succ_self K)
        have hident : Finset.Icc (e + 1) (e + (N : ℤ)) = win c N K := by
          ext t
          simp [win, e, Finset.mem_Icc]
          omega
        simpa [hident] using hwin'
      calc
        (∑ t ∈ Finset.Icc c (c + (K + 1 : ℕ) * (N : ℤ) - 1), F t)
            = (∑ t ∈ Finset.Icc c (e + (N : ℤ)), F t) := by rw [htarget]
        _ = (∑ t ∈ Finset.Icc c e, F t) + (∑ t ∈ Finset.Icc (e + 1) (e + (N : ℤ)), F t) := hsplit
        _ ≤ (K : ℝ) * C + C := by
            have ih' : (∑ t ∈ Finset.Icc c e, F t) ≤ (K : ℝ) * C := by
              have hident : Finset.Icc c e = Finset.Icc c (c + (K : ℤ) * (N : ℤ) - 1) := by
                rfl
              rw [hident]
              exact ih (fun k hk => hwin k (Nat.lt_trans hk (Nat.lt_succ_self K)))
            exact add_le_add ih' hwinlast
        _ = ((K + 1 : ℕ) : ℝ) * C := by
            rw [Nat.cast_succ]
            ring


/-- Second form of Lemma l:aux simple ac: an interval of length at least `N`
carries mass `O(|J|·N^{-1}·(δ₀np)^{-1/2})`.  `C₂` is universal. -/
theorem aux_simple_ac2 : ∃ C₂ : ℝ, 0 < C₂ ∧
    ∀ {n : ℕ} (hn1 : 1 ≤ n) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {p : unitInterval}
      (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2),
      ∀ {N : ℕ} (hN1 : 1 ≤ N) {ℓ : ℕ},
        ∀ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
          (hfmass : norm₁ f ≤ 1),
        ∀ (x : Fin ℓ → ℤ) (S : Finset (Fin ℓ))
          (hScard : δ₀ * (n : ℝ) ≤ (S.card : ℝ))
          (hSbig : ∀ j : Fin ℓ, j ∈ S → (N : ℝ) < |(x j : ℝ)|),
          ∀ (a b : ℤ) (hlen : (N : ℤ) ≤ (b : ℤ) - a + 1),
            (∑ t ∈ Finset.Icc a b, avgF f p ℓ x t) ≤
              C₂ * (((b : ℝ) - (a : ℝ) + 1) / (N : ℝ)) /
                Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by
  rcases aux_simple_ac with ⟨C₀, hC₀pos, hC₀⟩
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro n hn1 δ₀ hδ₀ p hp₀ hp₁ N hN1 ℓ f hfpos hfsum hfmass x S hScard hSbig a b hlen
  let c₀ : ℝ := C₀ / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ))
  have hc₀pos : 0 ≤ c₀ := by
    dsimp [c₀]
    positivity
  let w : ℝ := (b : ℝ) - (a : ℝ) + 1
  have hwpos : 0 < w := by
    dsimp [w]
    have hwint : (0 : ℤ) < (b : ℤ) - a + 1 := by omega  -- hlen: N ≤ b - a + 1, N ≥ 1
    exact_mod_cast hwint
  have hNℝ : 0 < (N : ℝ) := by exact_mod_cast hN1
  let K : ℕ := Nat.ceil (w / (N : ℝ))
  have hKge : w / (N : ℝ) ≤ (K : ℝ) := Nat.le_ceil (w / (N : ℝ))
  have hw_le_KN : w ≤ (K : ℝ) * (N : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hKge hNℝ.le
    simpa [div_mul_cancel₀, hNℝ.ne'] using hmul
  have hb : b ≤ a + (K : ℤ) * (N : ℤ) - 1 := by
    -- from real w ≤ K·N
    have hr : (b : ℝ) - (a : ℝ) + 1 ≤ (K : ℝ) * (N : ℝ) := by
      simpa [w] using hw_le_KN
    have hint : (b : ℤ) - a + 1 ≤ (K : ℤ) * (N : ℤ) := by
      exact_mod_cast hr
    omega
  have hcover : (∑ t ∈ Finset.Icc a b, avgF f p ℓ x t) ≤
      ∑ t ∈ Finset.Icc a (a + (K : ℤ) * (N : ℤ) - 1), avgF f p ℓ x t := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (by
      intro t ht
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht).1, le_trans (Finset.mem_Icc.mp ht).2 (by omega)⟩)
      (by intro t ht hgt; exact avgF_nonneg hfpos t)
  have hwinbound : ∀ k : ℕ, k < K →
      (∑ t ∈ win a N k, avgF f p ℓ x t) ≤ c₀ := by
    intro k hk
    dsimp [c₀]
    exact hC₀ hn1 hδ₀ hp₀ hp₁ hN1 hfpos hfsum hfmass x S hScard hSbig
      (a + (k : ℤ) * (N : ℤ)) (a + (k : ℤ) * (N : ℤ) + (N : ℤ) - 1) (by omega)
  have hKsum : (∑ t ∈ Finset.Icc a (a + (K : ℤ) * (N : ℤ) - 1), avgF f p ℓ x t) ≤ (K : ℝ) * c₀ :=
    sum_Icc_windows (F := avgF f p ℓ x) a N K hN1 hwinbound
  have hKsmall : (K : ℝ) ≤ 2 * w / (N : ℝ) := by
    have hceil : (K : ℝ) < w / (N : ℝ) + 1 := by
      exact Nat.ceil_lt_add_one (by positivity : 0 ≤ w / (N : ℝ))
    have h1 : w / (N : ℝ) ≥ 1 := by
      have hwN : (N : ℝ) ≤ w := by
        have hwint : ((N : ℤ) : ℝ) ≤ (b : ℝ) - (a : ℝ) + 1 := by
          exact_mod_cast hlen
        simpa [w] using hwint
      have : (N : ℝ) / (N : ℝ) ≤ w / (N : ℝ) :=
        div_le_div_of_nonneg_right hwN hNℝ.le
      simpa [div_self hNℝ.ne'] using this
    have hK' : (K : ℝ) ≤ w / (N : ℝ) + 1 := le_of_lt hceil
    calc
      (K : ℝ) ≤ w / (N : ℝ) + 1 := hK'
      _ ≤ w / (N : ℝ) + w / (N : ℝ) := by nlinarith [h1]
      _ = 2 * w / (N : ℝ) := by ring
  calc
    (∑ t ∈ Finset.Icc a b, avgF f p ℓ x t)
        ≤ (∑ t ∈ Finset.Icc a (a + (K : ℤ) * (N : ℤ) - 1), avgF f p ℓ x t) := hcover
    _ ≤ (K : ℝ) * c₀ := hKsum
    _ ≤ (2 * w / (N : ℝ)) * c₀ := mul_le_mul_of_nonneg_right hKsmall hc₀pos
    _ = (2 * C₀) * (w / (N : ℝ)) / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by
        dsimp [c₀]
        field_simp [show Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) ≠ 0 by positivity]
    _ = (2 * C₀) * (((b : ℝ) - (a : ℝ) + 1) / (N : ℝ)) /
          Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by rfl


/-- Markov-style counting: #{d ∈ A : T < g d} ≤ (Σ_{d∈A} g d)/T for nonneg g. -/
lemma count_gt_le_sum_div {g : ℤ → ℝ} (A : Finset ℤ) {T : ℝ} (hT : 0 < T)
    (hg : ∀ d ∈ A, 0 ≤ g d) :
    (((A.filter (fun d => T < g d)).card : ℝ) ≤ (∑ d ∈ A, g d) / T) := by
  classical
  have hsum_ge : T * ((A.filter (fun d => T < g d)).card : ℝ) ≤
      (∑ d ∈ A.filter (fun d => T < g d), g d) := by
    calc
      T * ((A.filter (fun d => T < g d)).card : ℝ) = ∑ d ∈ A.filter (fun d => T < g d), T := by
        rw [Finset.sum_const]
        rw [nsmul_eq_mul]
        ring
      _ ≤ ∑ d ∈ A.filter (fun d => T < g d), g d := by
        apply Finset.sum_le_sum
        intro d hd
        exact le_of_lt (Finset.mem_filter.mp hd).2
  calc
    ((A.filter (fun d => T < g d)).card : ℝ)
        ≤ (∑ d ∈ A.filter (fun d => T < g d), g d) / T := by
            exact (le_div_iff₀ hT).2 (by simpa [mul_comm] using hsum_ge)
    _ ≤ (∑ d ∈ A, g d) / T := by
        apply div_le_div_of_nonneg_right _ hT.le
        exact Finset.sum_le_sum_of_subset_of_nonneg (by
          intro d hd
          exact (Finset.mem_filter.mp hd).1) (by
          intro d hd1 hd2
          exact hg d hd1)

/-- count of points where at least one of F(u+d), F(u−d) exceeds T. -/
lemma count_or_gt_le {F : ℤ → ℝ} (A : Finset ℤ) {u : ℤ} {T : ℝ} (hT : 0 < T)
    (hF : ∀ d ∈ A, 0 ≤ F (u + d)) (hF2 : ∀ d ∈ A, 0 ≤ F (u - d)) :
    (((A.filter (fun d => T < F (u + d) ∨ T < F (u - d))).card : ℝ)
        ≤ ((∑ d ∈ A, F (u + d)) + (∑ d ∈ A, F (u - d))) / T) := by
  classical
  have h1 : ((A.filter (fun d => T < F (u + d))).card : ℝ) ≤ (∑ d ∈ A, F (u + d)) / T :=
    count_gt_le_sum_div (g := fun d => F (u + d)) A hT hF
  have h2 : ((A.filter (fun d => T < F (u - d))).card : ℝ) ≤ (∑ d ∈ A, F (u - d)) / T :=
    count_gt_le_sum_div (g := fun d => F (u - d)) A hT hF2
  have hsub : A.filter (fun d => T < F (u + d) ∨ T < F (u - d)) ⊆
      A.filter (fun d => T < F (u + d)) ∪ A.filter (fun d => T < F (u - d)) := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdA, hdisj⟩
    rw [Finset.mem_union]
    rcases hdisj with hl | hr
    · left; exact Finset.mem_filter.mpr ⟨hdA, hl⟩
    · right; exact Finset.mem_filter.mpr ⟨hdA, hr⟩
  have hcard : ((A.filter (fun d => T < F (u + d) ∨ T < F (u - d))).card : ℝ) ≤
      ((A.filter (fun d => T < F (u + d))).card : ℝ) + ((A.filter (fun d => T < F (u - d))).card : ℝ) := by
    have hc1 : (A.filter (fun d => T < F (u + d) ∨ T < F (u - d))).card ≤
        (A.filter (fun d => T < F (u + d))).card + (A.filter (fun d => T < F (u - d))).card := by
      exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le (A.filter (fun d => T < F (u + d))) (A.filter (fun d => T < F (u - d))))
    exact_mod_cast hc1
  calc
    ((A.filter (fun d => T < F (u + d) ∨ T < F (u - d))).card : ℝ)
        ≤ ((A.filter (fun d => T < F (u + d))).card : ℝ) + ((A.filter (fun d => T < F (u - d))).card : ℝ) := hcard
    _ ≤ (∑ d ∈ A, F (u + d)) / T + (∑ d ∈ A, F (u - d)) / T := add_le_add h1 h2
    _ = ((∑ d ∈ A, F (u + d)) + (∑ d ∈ A, F (u - d))) / T := by rw [add_div]



/-- Sum over an interval of `F (u + t)` equals the sum over the translated
interval of `F`. -/
lemma sum_translate_Icc {F : ℤ → ℝ} (u c d : ℤ) :
    (∑ t ∈ Finset.Icc c d, F (u + t)) = ∑ s ∈ Finset.Icc (u + c) (u + d), F s := by
  classical
  let g : ℤ → ℤ := fun t => u + t
  have hg : Function.Injective g := by
    intro a b hab
    dsimp [g] at hab
    omega
  have him : (Finset.Icc c d).image g = Finset.Icc (u + c) (u + d) := by
    ext s
    constructor
    · intro hs
      rcases Finset.mem_image.mp hs with ⟨t, ht, hts⟩
      dsimp [g] at hts
      rw [← hts]
      rcases Finset.mem_Icc.mp ht with ⟨h1, h2⟩
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro hs
      rcases Finset.mem_Icc.mp hs with ⟨h1, h2⟩
      refine Finset.mem_image.mpr ⟨s - u, ?_, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · dsimp [g]
        omega
  calc
    (∑ t ∈ Finset.Icc c d, F (u + t)) = ∑ t ∈ Finset.Icc c d, F (g t) := by rfl
    _ = ∑ s ∈ (Finset.Icc c d).image g, F s := by
        exact (Finset.sum_image (f := F) (s := Finset.Icc c d) (g := g) hg.injOn).symm
    _ = ∑ s ∈ Finset.Icc (u + c) (u + d), F s := by rw [him]

/-- Sum over an interval of `F (u − t)`. -/
lemma sum_translate_Icc_neg {F : ℤ → ℝ} (u c d : ℤ) :
    (∑ t ∈ Finset.Icc c d, F (u - t)) = ∑ s ∈ Finset.Icc (u - d) (u - c), F s := by
  classical
  let g : ℤ → ℤ := fun t => u - t
  have hg : Function.Injective g := by
    intro a b hab
    dsimp [g] at hab
    omega
  have him : (Finset.Icc c d).image g = Finset.Icc (u - d) (u - c) := by
    ext s
    constructor
    · intro hs
      rcases Finset.mem_image.mp hs with ⟨t, ht, hts⟩
      dsimp [g] at hts
      rw [← hts]
      rcases Finset.mem_Icc.mp ht with ⟨h1, h2⟩
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro hs
      rcases Finset.mem_Icc.mp hs with ⟨h1, h2⟩
      refine Finset.mem_image.mpr ⟨u - s, ?_, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · dsimp [g]
        omega
  calc
    (∑ t ∈ Finset.Icc c d, F (u - t)) = ∑ t ∈ Finset.Icc c d, F (g t) := by rfl
    _ = ∑ s ∈ (Finset.Icc c d).image g, F s := by
        exact (Finset.sum_image (f := F) (s := Finset.Icc c d) (g := g) hg.injOn).symm
    _ = ∑ s ∈ Finset.Icc (u - d) (u - c), F s := by rw [him]

/-- Per-step expectation bound: for a prefix `z` (of length `m`) with at least
`δ₀·n` big coordinates, and a coordinate set that is a single integer interval
of length at least `N`, the mass of the averaged function over the translated
interval `u + Icc c d` is `O(|Icc c d|/(N√(δ₀np)))`.  Universal constant. -/
theorem interval_step_sum_le : ∃ C₂ : ℝ, 0 < C₂ ∧
    ∀ {n : ℕ} (hn1 : 1 ≤ n) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {p : unitInterval}
      (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2),
      ∀ {N : ℕ} (hN1 : 1 ≤ N) {m : ℕ},
        ∀ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
          (hfmass : norm₁ f ≤ 1),
        ∀ (z : Fin m → ℤ) (S : Finset (Fin m))
          (hScard : δ₀ * (n : ℝ) ≤ (S.card : ℝ))
          (hSbig : ∀ j : Fin m, j ∈ S → (N : ℝ) < |(z j : ℝ)|),
          ∀ (c d u : ℤ) (hlen : (N : ℤ) ≤ (d : ℤ) - c + 1),
            (∑ t ∈ Finset.Icc c d, avgF f p m z (u + t)) ≤
              C₂ * (((d : ℝ) - (c : ℝ) + 1) / (N : ℝ)) /
                Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by
  rcases aux_simple_ac2 with ⟨C₂', hC₂pos, hC₂⟩
  refine ⟨2 * C₂', by positivity, ?_⟩
  intro n hn1 δ₀ hδ₀ p hp₀ hp₁ N hN1 m f hfpos hfsum hfmass z S hScard hSbig c d u hlen
  have hmain := hC₂ hn1 hδ₀ hp₀ hp₁ hN1 hfpos hfsum hfmass z S hScard hSbig
    (u + c) (u + d) (by omega)
  have hnum : (↑(u + d : ℤ) : ℝ) - (↑(u + c : ℤ) : ℝ) + 1 = (d : ℝ) - (c : ℝ) + 1 := by
    rw [Int.cast_add, Int.cast_add]
    ring
  rw [hnum] at hmain
  have htrans : (∑ t ∈ Finset.Icc c d, avgF f p m z (u + t)) =
      ∑ s ∈ Finset.Icc (u + c) (u + d), avgF f p m z s := by
    exact sum_translate_Icc (F := avgF f p m z) u c d
  calc
    (∑ t ∈ Finset.Icc c d, avgF f p m z (u + t))
        = ∑ s ∈ Finset.Icc (u + c) (u + d), avgF f p m z s := htrans
    _ ≤ C₂' * (((d : ℝ) - (c : ℝ) + 1) / (N : ℝ)) /
          Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := hmain
    _ ≤ (2 * C₂') * (((d : ℝ) - (c : ℝ) + 1) / (N : ℝ)) /
          Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by
            have hw0 : 0 ≤ (d : ℝ) - (c : ℝ) + 1 := by
              have hz : (0 : ℤ) ≤ d - c + 1 := by omega
              exact_mod_cast hz
            have hden0 : 0 < Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by
              apply Real.sqrt_pos.2
              have hnR : 0 < (n : ℝ) := by exact_mod_cast hn1
              positivity
            have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN1
            have hposY : 0 ≤ (((d : ℝ) - (c : ℝ) + 1) / (N : ℝ)) := by
              exact div_nonneg hw0 (le_of_lt hNpos)
            have hmul : C₂' * (((d : ℝ) - (c : ℝ) + 1) / (N : ℝ)) ≤
                (2 * C₂') * (((d : ℝ) - (c : ℝ) + 1) / (N : ℝ)) := by
              have hprod2 := mul_nonneg hC₂pos.le hposY
              nlinarith
            exact div_le_div_of_nonneg_right hmul hden0.le

/-- Per-step count bound: for a coordinate set `A₀ = Icc c d` (interval of
length ≥ N) and prefix with ≥ δ₀n big coords, the number of `t ∈ A₀` at which
the level-`m` point `u` does not decay (with threshold `T`) is at most
`O(|A₀|/(N·√(δ₀np)·T))`.  Universal constant. -/
theorem step_nondecay_count_le : ∃ Cq : ℝ, 0 < Cq ∧
    ∀ {n : ℕ} (hn1 : 1 ≤ n) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {p : unitInterval}
      (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2),
      ∀ {N : ℕ} (hN1 : 1 ≤ N) {m : ℕ},
        ∀ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
          (hfmass : norm₁ f ≤ 1),
        ∀ (z : Fin m → ℤ) (S : Finset (Fin m))
          (hScard : δ₀ * (n : ℝ) ≤ (S.card : ℝ))
          (hSbig : ∀ j : Fin m, j ∈ S → (N : ℝ) < |(z j : ℝ)|),
          ∀ (c d u : ℤ) (hlen : (N : ℤ) ≤ (d : ℤ) - c + 1) {T : ℝ} (hT : 0 < T),
            (((Finset.Icc c d).filter (fun t => ¬ decaysAt (avgF f p m z) t T u)).card : ℝ) ≤
              Cq * (((d : ℝ) - (c : ℝ) + 1) / (N : ℝ)) /
                (Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) * T) := by
  classical
  rcases interval_step_sum_le with ⟨C₂, hC₂pos, hC₂⟩
  refine ⟨2 * C₂, by positivity, ?_⟩
  intro n hn1 δ₀ hδ₀ p hp₀ hp₁ N hN1 m f hfpos hfsum hfmass z S hScard hSbig c d u hlen T hT
  let F : ℤ → ℝ := avgF f p m z
  have hpos1 : ∀ t ∈ Finset.Icc c d, 0 ≤ F (u + t) := by
    intro t ht
    exact avgF_nonneg hfpos (u + t)
  have hpos2 : ∀ t ∈ Finset.Icc c d, 0 ≤ F (u - t) := by
    intro t ht
    exact avgF_nonneg hfpos (u - t)
  have hnd : ∀ t : ℤ, ¬ decaysAt F t T u ↔ T < F (u + t) ∨ T < F (u - t) := by
    intro t
    rw [decaysAt]
    constructor
    · intro h
      by_contra hbad
      rw [not_or] at hbad
      exact h ⟨le_of_not_gt hbad.1, le_of_not_gt hbad.2⟩
    · intro h hdec
      rcases hdec with ⟨h1, h2⟩
      rcases h with hl | hr
      · exact (not_le_of_gt hl) h1
      · exact (not_le_of_gt hr) h2
  have hfilter : (Finset.Icc c d).filter (fun t => ¬ decaysAt F t T u) =
      (Finset.Icc c d).filter (fun t => T < F (u + t) ∨ T < F (u - t)) := by
    ext t
    constructor
    · intro ht
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1, (hnd t).1 (Finset.mem_filter.mp ht).2⟩
    · intro ht
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1, (hnd t).2 (Finset.mem_filter.mp ht).2⟩
  have hcount := count_or_gt_le (F := F) (A := Finset.Icc c d) (u := u) hT hpos1 hpos2
  have hS1 : (∑ t ∈ Finset.Icc c d, F (u + t)) ≤
      C₂ * (((d : ℝ) - (c : ℝ) + 1) / (N : ℝ)) / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) :=
    hC₂ hn1 hδ₀ hp₀ hp₁ hN1 hfpos hfsum hfmass z S hScard hSbig c d u hlen
  have hS2b := hC₂ hn1 hδ₀ hp₀ hp₁ hN1 hfpos hfsum hfmass z S hScard hSbig (u - d) (u - c) (0 : ℤ) (by omega)
  have hnum2 : (↑(u - c : ℤ) : ℝ) - (↑(u - d : ℤ) : ℝ) + 1 = (d : ℝ) - (c : ℝ) + 1 := by
    rw [Int.cast_sub, Int.cast_sub]
    ring
  rw [hnum2] at hS2b
  have hzero : (∑ t ∈ Finset.Icc (u - d) (u - c), F (0 + t)) =
      ∑ s ∈ Finset.Icc (u - d) (u - c), F s := by
    apply Finset.sum_congr rfl
    intro t ht
    simp
  have hS2b' : (∑ s ∈ Finset.Icc (u - d) (u - c), F s) ≤
      C₂ * (((d : ℝ) - (c : ℝ) + 1) / (N : ℝ)) / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by
    rw [← hzero]
    exact hS2b
  have hS2 : (∑ t ∈ Finset.Icc c d, F (u - t)) ≤
      C₂ * (((d : ℝ) - (c : ℝ) + 1) / (N : ℝ)) / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := by
    calc
      (∑ t ∈ Finset.Icc c d, F (u - t)) = ∑ s ∈ Finset.Icc (u - d) (u - c), F s := by
          exact sum_translate_Icc_neg (F := F) u c d
      _ ≤ C₂ * (((d : ℝ) - (c : ℝ) + 1) / (N : ℝ)) /
            Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) := hS2b'
  have hS : (∑ t ∈ Finset.Icc c d, F (u + t)) + (∑ t ∈ Finset.Icc c d, F (u - t)) ≤
      2 * (C₂ * (((d : ℝ) - (c : ℝ) + 1) / (N : ℝ)) / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ))) := by
    have hsum := add_le_add hS1 hS2
    exact le_trans hsum (le_of_eq (two_mul (C₂ * (((d : ℝ) - (c : ℝ) + 1) / (N : ℝ)) / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)))).symm)
  have hcount' : (((Finset.Icc c d).filter (fun t => ¬ decaysAt F t T u)).card : ℝ) ≤
      ((∑ t ∈ Finset.Icc c d, F (u + t)) + (∑ t ∈ Finset.Icc c d, F (u - t))) / T := by
    rw [hfilter]
    exact hcount
  calc
    (((Finset.Icc c d).filter (fun t => ¬ decaysAt F t T u)).card : ℝ)
        ≤ ((∑ t ∈ Finset.Icc c d, F (u + t)) + (∑ t ∈ Finset.Icc c d, F (u - t))) / T := hcount'
    _ ≤ (2 * (C₂ * (((d : ℝ) - (c : ℝ) + 1) / (N : ℝ)) / Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)))) / T := by
        exact (div_le_div_of_nonneg_right hS hT.le)
    _ = (2 * C₂) * (((d : ℝ) - (c : ℝ) + 1) / (N : ℝ)) /
          (Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) * T) := by
        field_simp [show Real.sqrt (δ₀ * (n : ℝ) * (p : ℝ)) ≠ 0 by positivity,
          show T ≠ 0 by positivity]

end Submission.RoughDecay
