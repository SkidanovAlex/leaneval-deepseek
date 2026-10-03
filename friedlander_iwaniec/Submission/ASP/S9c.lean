/-
  Companion paper, §9: the assembly of the remainder hypothesis `(9.7)` for the modified
  remainder function

      `r̃_d(t) = ∑_{ν ≤ t} μ(ν)·(r_{[ν²,d]}(t) − g̃(d)·r_{ν²}(t))`      (9.11)

  (proved as an identity in `S9a.AtilAd_eq_gtil_mul_add`).  The companion bounds

      `R(t,D) = ∑♭_{d ≤ D} |r̃_d(t)| ≪ A(x)(log x)^{-2^22}`      (9.7)

  by splitting the sum over `ν` at `ν = L`: the part `E₁` with `ν ≤ L` is controlled by `(R′₃)`
  (`S9b.E1_le`), the part `E₂` with `ν > L` is the estimate (9.12) (carried here as the explicit
  quantity `Etwo`), and the `g̃`-tail is an elementary factor.  What is proved here is the *exact*
  assembly
      `∑♭_{d ≤ D} |r̃_d(t)| ≤ E₁ + E₂ + (∑♭_{d ≤ D} |g̃(d)|)·(∑_{ν ≤ t} |r_{ν²}(t)|)`,
  so that (9.7) reduces to the two estimates (9.11) and (9.12) plus a bound for the last factor.
-/
import Mathlib
import Submission.ASP.S9a
import Submission.ASP.S9b

namespace Submission.ASP

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- `r̃_d(t)` — the companion's (9.11). -/
def rtilde (r : ℕ → ℕ → ℝ) (gtil : ℕ → ℝ) (d t : ℕ) : ℝ :=
  ∑ ν ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius ν : ℝ)
    * (r (Nat.lcm (ν ^ 2) d) t - gtil d * r (ν ^ 2) t)

/-- The `E₁`-part of the companion's §9 error term: the terms with `ν ≤ L`. -/
def Eone (r : ℕ → ℕ → ℝ) (t D L : ℕ) : ℝ :=
  ∑ ν ∈ (Finset.Icc 1 L).filter Squarefree,
    ∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |r (Nat.lcm (ν ^ 2) d) t|

/-- The `E₂`-part of the companion's §9 error term (its (9.12)): the terms with `ν > L`. -/
def Etwo (a g : ℕ → ℝ) (t D L : ℕ) : ℝ :=
  ∑ ν ∈ (Finset.Icc (L + 1) t).filter Squarefree,
    ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
      (Ad a (Nat.lcm (ν ^ 2) d) t + g (Nat.lcm (ν ^ 2) d) * Acount a t)

/-- `|r_d(t)| ≤ A_d(t) + g(d)·A(t)`: the companion's (1.7) for a nonnegative sequence. -/
lemma abs_r_le (a g : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (t : ℕ)
    (ha : ∀ n, 0 ≤ a n) (hg : ∀ n, 0 ≤ g n) (happ : Approx a g r (t : ℝ)) (d : ℕ) :
    |r d t| ≤ Ad a d t + g d * Acount a t := by
  have hAd : 0 ≤ Ad a d t := Finset.sum_nonneg (fun n _ => ha n)
  have hA : 0 ≤ Acount a t := Finset.sum_nonneg (fun n _ => ha n)
  have hr : r d t = Ad a d t - g d * Acount a t := by
    rw [happ d t]
    ring
  rw [hr]
  refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;> linarith [mul_nonneg (hg d) hA]

/-- The pointwise bound for `|r̃_d(t)|` by a squarefree-restricted `ν`-sum. -/
lemma rtilde_abs_le (r : ℕ → ℕ → ℝ) (gtil : ℕ → ℝ) (d t : ℕ) :
    |rtilde r gtil d t| ≤ ∑ ν ∈ (Finset.Icc 1 t).filter Squarefree,
      (|r (Nat.lcm (ν ^ 2) d) t| + |gtil d| * |r (ν ^ 2) t|) := by
  have hzero : (∑ ν ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius ν : ℝ)
        * (r (Nat.lcm (ν ^ 2) d) t - gtil d * r (ν ^ 2) t))
      = ∑ ν ∈ (Finset.Icc 1 t).filter Squarefree, (ArithmeticFunction.moebius ν : ℝ)
          * (r (Nat.lcm (ν ^ 2) d) t - gtil d * r (ν ^ 2) t) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    by_cases h : Squarefree ν
    · rw [if_pos h]
    · rw [if_neg h]
      have : ArithmeticFunction.moebius ν = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree h
      rw [this]
      simp
  rw [rtilde, hzero]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun ν hν => ?_))
  have hsf : Squarefree ν := (Finset.mem_filter.mp hν).2
  have hmu : |(ArithmeticFunction.moebius ν : ℝ)| = 1 := by
    rw [← Int.cast_abs]
    norm_num [ArithmeticFunction.abs_moebius_eq_one_of_squarefree hsf]
  have h1 : |(ArithmeticFunction.moebius ν : ℝ)
      * (r (Nat.lcm (ν ^ 2) d) t - gtil d * r (ν ^ 2) t)|
      = |r (Nat.lcm (ν ^ 2) d) t - gtil d * r (ν ^ 2) t| := by
    rw [abs_mul, hmu, one_mul]
  rw [h1]
  calc |r (Nat.lcm (ν ^ 2) d) t - gtil d * r (ν ^ 2) t|
      ≤ |r (Nat.lcm (ν ^ 2) d) t| + |gtil d * r (ν ^ 2) t| := abs_sub _ _
    _ = |r (Nat.lcm (ν ^ 2) d) t| + |gtil d| * |r (ν ^ 2) t| := by rw [abs_mul]

/-- **Companion §9, the assembly of (9.7)**: the `ν`-sum in `r̃_d` is split at `ν = L`, giving
`E₁` (the terms `ν ≤ L`), `E₂` (the terms `ν > L`, bounded by `(1.7)`) and the `g̃`-tail. -/
theorem Rtilde_sum_le (a g : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (gtil : ℕ → ℝ) (t D L : ℕ)
    (hLt : L ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hg : ∀ n, 0 ≤ g n) (happ : Approx a g r (t : ℝ)) :
    (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |rtilde r gtil d t|)
      ≤ Eone r t D L + Etwo a g t D L
        + (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |gtil d|)
            * (∑ ν ∈ Finset.Icc 1 t, |r (ν ^ 2) t|) := by
  classical
  set G : ℝ := ∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |gtil d| with hG
  -- Step 1: bound each `|r̃_d|` and swap the `(d,ν)`-sums
  have h1 : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |rtilde r gtil d t|)
      ≤ ∑ ν ∈ (Finset.Icc 1 t).filter Squarefree,
          ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
            (|r (Nat.lcm (ν ^ 2) d) t| + |gtil d| * |r (ν ^ 2) t|) := by
    refine (Finset.sum_le_sum (fun d _ => rtilde_abs_le r gtil d t)).trans (le_of_eq ?_)
    exact Finset.sum_comm
  -- Step 2: split the `ν`-range at `L`
  have hsplit : (∑ ν ∈ (Finset.Icc 1 t).filter Squarefree,
        ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          (|r (Nat.lcm (ν ^ 2) d) t| + |gtil d| * |r (ν ^ 2) t|))
      = (∑ ν ∈ (Finset.Icc 1 L).filter Squarefree,
          ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
            (|r (Nat.lcm (ν ^ 2) d) t| + |gtil d| * |r (ν ^ 2) t|))
        + (∑ ν ∈ (Finset.Icc (L + 1) t).filter Squarefree,
            ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
              (|r (Nat.lcm (ν ^ 2) d) t| + |gtil d| * |r (ν ^ 2) t|)) := by
    rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 t).filter Squarefree)
      (fun ν => ν ≤ L)]
    congr 1
    · congr 1
      ext ν
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨h1, -⟩, hsf⟩, h3⟩
        exact ⟨⟨h1, h3⟩, hsf⟩
      · rintro ⟨⟨h1, h3⟩, hsf⟩
        exact ⟨⟨⟨h1, le_trans h3 hLt⟩, hsf⟩, h3⟩
    · congr 1
      ext ν
      simp only [Finset.mem_filter, Finset.mem_Icc, not_le]
      constructor
      · rintro ⟨⟨⟨-, h2⟩, hsf⟩, h3⟩
        exact ⟨⟨by omega, h2⟩, hsf⟩
      · rintro ⟨⟨h3, h2⟩, hsf⟩
        exact ⟨⟨⟨by omega, h2⟩, hsf⟩, h3⟩
  -- Step 3: the three pieces
  have hinner : ∀ ν : ℕ, (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        (|r (Nat.lcm (ν ^ 2) d) t| + |gtil d| * |r (ν ^ 2) t|))
      = (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |r (Nat.lcm (ν ^ 2) d) t|)
        + G * |r (ν ^ 2) t| := by
    intro ν
    rw [Finset.sum_add_distrib, hG, Finset.sum_mul]
  have hE1 : (∑ ν ∈ (Finset.Icc 1 L).filter Squarefree,
        ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          (|r (Nat.lcm (ν ^ 2) d) t| + |gtil d| * |r (ν ^ 2) t|))
      = Eone r t D L
        + G * (∑ ν ∈ (Finset.Icc 1 L).filter Squarefree, |r (ν ^ 2) t|) := by
    rw [Finset.sum_congr rfl (fun ν _ => hinner ν), Finset.sum_add_distrib, Eone,
      Finset.mul_sum]
  have hE2 : (∑ ν ∈ (Finset.Icc (L + 1) t).filter Squarefree,
        ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          (|r (Nat.lcm (ν ^ 2) d) t| + |gtil d| * |r (ν ^ 2) t|))
      ≤ Etwo a g t D L
        + G * (∑ ν ∈ (Finset.Icc (L + 1) t).filter Squarefree, |r (ν ^ 2) t|) := by
    rw [Finset.sum_congr rfl (fun ν _ => hinner ν), Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · rw [Etwo]
      exact Finset.sum_le_sum (fun ν _ => Finset.sum_le_sum (fun d _ =>
        abs_r_le a g r t ha hg happ (Nat.lcm (ν ^ 2) d)))
    · rw [Finset.mul_sum]
  have hGnn : 0 ≤ G := by
    rw [hG]
    exact Finset.sum_nonneg (fun d _ => abs_nonneg _)
  have htail : G * (∑ ν ∈ (Finset.Icc 1 L).filter Squarefree, |r (ν ^ 2) t|)
      + G * (∑ ν ∈ (Finset.Icc (L + 1) t).filter Squarefree, |r (ν ^ 2) t|)
      ≤ G * (∑ ν ∈ Finset.Icc 1 t, |r (ν ^ 2) t|) := by
    have hle_t : (∑ ν ∈ (Finset.Icc 1 t).filter Squarefree, |r (ν ^ 2) t|)
        ≤ ∑ ν ∈ Finset.Icc 1 t, |r (ν ^ 2) t| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => abs_nonneg _)
    have hdisj : Disjoint ((Finset.Icc 1 L).filter Squarefree)
        ((Finset.Icc (L + 1) t).filter Squarefree) := by
      rw [Finset.disjoint_left]
      intro ν h1 h2
      rw [Finset.mem_filter, Finset.mem_Icc] at h1 h2
      omega
    have hunion : ((Finset.Icc 1 L).filter Squarefree)
        ∪ ((Finset.Icc (L + 1) t).filter Squarefree)
        ⊆ (Finset.Icc 1 t).filter Squarefree := by
      intro ν hν
      rcases Finset.mem_union.mp hν with h | h
      · rw [Finset.mem_filter, Finset.mem_Icc] at h ⊢
        exact ⟨⟨h.1.1, le_trans h.1.2 hLt⟩, h.2⟩
      · rw [Finset.mem_filter, Finset.mem_Icc] at h ⊢
        exact ⟨⟨by omega, h.1.2⟩, h.2⟩
    have hsum : (∑ ν ∈ (Finset.Icc 1 L).filter Squarefree, |r (ν ^ 2) t|)
        + (∑ ν ∈ (Finset.Icc (L + 1) t).filter Squarefree, |r (ν ^ 2) t|)
        ≤ ∑ ν ∈ (Finset.Icc 1 t).filter Squarefree, |r (ν ^ 2) t| := by
      rw [← Finset.sum_union hdisj]
      exact Finset.sum_le_sum_of_subset_of_nonneg hunion (fun _ _ _ => abs_nonneg _)
    calc G * (∑ ν ∈ (Finset.Icc 1 L).filter Squarefree, |r (ν ^ 2) t|)
          + G * (∑ ν ∈ (Finset.Icc (L + 1) t).filter Squarefree, |r (ν ^ 2) t|)
        = G * ((∑ ν ∈ (Finset.Icc 1 L).filter Squarefree, |r (ν ^ 2) t|)
            + (∑ ν ∈ (Finset.Icc (L + 1) t).filter Squarefree, |r (ν ^ 2) t|)) := by ring
      _ ≤ G * (∑ ν ∈ (Finset.Icc 1 t).filter Squarefree, |r (ν ^ 2) t|) :=
          mul_le_mul_of_nonneg_left hsum hGnn
      _ ≤ G * (∑ ν ∈ Finset.Icc 1 t, |r (ν ^ 2) t|) :=
          mul_le_mul_of_nonneg_left hle_t hGnn
  refine le_trans h1 ?_
  rw [hsplit]
  refine le_trans (add_le_add (le_of_eq hE1) hE2) ?_
  linarith [htail]

end

end Submission.ASP
