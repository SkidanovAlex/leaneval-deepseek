import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.friedrichs_commutator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep1

/-
PORT REQUEST (mechanical).  The file Submission/Work/Diff/STE/friedrichs_commutator.lean proves the
statement below *with one extra hypothesis*, `hρ1 : ∀ y, (∑ i, (y i)^2) ≤ 1 → ρ y = 1`.  That extra
hypothesis is used in exactly one place, namely to invoke `Work.Diff.STE.friedrichs_pointwise`
(Submission/Work/Diff/STE/friedrichs_pointwise.lean), and the proof of that auxiliary claim never
uses `hρ1` either: its own file records "ρ equals 1 on the unit ball; recorded for completeness (it
is not needed below, the support hypothesis hρ0 together with the Lipschitz bound suffices)".
Concretely, in `friedrichs_pointwise` the case analysis is on `ε² Σ mᵢ² ≤ 2` (only the Lipschitz
bound and `hρb` are used), on `ε² Σ kᵢ² ≤ 2` (same), and otherwise both points `ε•m`, `ε•k` satisfy
`2 < Σ yᵢ²`, so `ρ` vanishes at both and the difference is `0`.  Hence the statement requested here
is TRUE, and its proof is the proof of `Work.Diff.STE.friedrichs_commutator` with `hρ1` deleted
throughout (`CSq_succ_commutator_le` and the pointwise estimate must be re-proved without `hρ1` in
the same file; they may be `private`).

Purpose: this is the coefficient-level estimate "commutator with a Fourier cutoff gains one order",
uniformly in the cutoff scale `ε ∈ (0,1]`, under the support-only profile hypothesis that the
downstream symbol-calculus layer actually provides (it is consumed by
`Work.Diff.STE.B3.SymCalcStep1.firstOrder_comm_trunc_le`).
-/
/-- The sup norm on `ι → ℝ` is bounded by the Euclidean norm. -/
private lemma norm_le_sqrt_sum_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ‖v‖ ≤ Real.sqrt (∑ i, (v i)^2) := by
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- The scalar core of `friedrichs_pointwise`.  `s` stands for the square of the
multiplier difference, `P` for `Σ mᵢ²`, `R` for `Σ (mᵢ - kᵢ)²`, `e` for `ε`, and
`h1P` is the case-dependent bound on `(1 + P) * ε²` obtained from the support of `ρ`. -/
private lemma wt_arith {P s L R e : ℝ} (hR : 0 ≤ R) (he : 0 < e) (he1 : e ≤ 1)
    (hP : 0 ≤ P) (h1P : (1 + P) * e^2 ≤ 4 + e^2 + 2*e^2*R) (hs4 : s ≤ 4)
    (hsL : s ≤ L^2*e^2*R) : (1+P)*s ≤ 64*(1+L^2)*(1+R) := by
  have he2 : 0 < e^2 := by positivity
  have he2le1 : e^2 ≤ 1 := by nlinarith
  have hPn : (0:ℝ) ≤ 1 + P := by linarith
  have hLRn : 0 ≤ L^2*R := mul_nonneg (sq_nonneg L) hR
  by_cases h : L^2*e^2*R ≤ 4
  · have h1 : (1+P)*s ≤ (1+P)*(L^2*e^2*R) := mul_le_mul_of_nonneg_left hsL hPn
    have h2 : (1+P)*(L^2*e^2*R) = ((1+P)*e^2)*(L^2*R) := by ring
    have h3 : ((1+P)*e^2)*(L^2*R) ≤ (4 + e^2 + 2*e^2*R)*(L^2*R) :=
      mul_le_mul_of_nonneg_right h1P hLRn
    have h4 : (4 + e^2 + 2*e^2*R)*(L^2*R) ≤ 5*L^2*R + 8*R := by
      have ha : e^2*(L^2*R) ≤ L^2*R := by
        have := mul_le_mul_of_nonneg_right he2le1 hLRn; simpa using this
      have hb : R*(L^2*e^2*R) ≤ R*4 := mul_le_mul_of_nonneg_left h hR
      nlinarith [ha, hb]
    have h5 : (5:ℝ)*L^2*R + 8*R ≤ 64*(1+L^2)*(1+R) := by nlinarith [hR]
    linarith
  · push Not at h
    have h16 : (16:ℝ) ≤ 4*(L^2*e^2*R) := by nlinarith [h]
    have hmul : (1+P)*e^2 * 4 ≤ (4 + e^2 + 2*e^2*R)*4 :=
      mul_le_mul_of_nonneg_right h1P (by norm_num)
    have hkey : (4*(1+P)) * e^2 ≤ (4*L^2*R + 4 + 8*R) * e^2 := by
      nlinarith [hmul, h16, hR]
    have h4 : 4*(1+P) ≤ 4*L^2*R + 4 + 8*R := le_of_mul_le_mul_right hkey he2
    have h5 : (1+P)*s ≤ 4*(1+P) := by
      have := mul_le_mul_of_nonneg_left hs4 hPn; linarith
    have h6 : 4*L^2*R + 4 + 8*R ≤ 64*(1+L^2)*(1+R) := by nlinarith [hR]
    linarith

private theorem friedrichs_pointwise_supp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : ι → ℝ, 2 < (∑ i, (y i) ^ 2) → ρ y = 0)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (k m : ι → ℤ) :
    Work.Diff.STE.wt m * (ρ (ε • (fun i => (m i : ℝ))) - ρ (ε • (fun i => (k i : ℝ)))) ^ 2
      ≤ 64 * (1 + L ^ 2) * Work.Diff.STE.wt (k - m) := by
  set a : ι → ℝ := ε • (fun i => (m i : ℝ)) with ha
  set b : ι → ℝ := ε • (fun i => (k i : ℝ)) with hb
  set P : ℝ := ∑ i, ((m i : ℝ))^2 with hP
  set Q : ℝ := ∑ i, ((k i : ℝ))^2 with hQ
  set R : ℝ := ∑ i, ((k i : ℝ) - (m i : ℝ))^2 with hR
  set A : ℝ := ∑ i, (a i)^2 with hA
  set B : ℝ := ∑ i, (b i)^2 with hB
  set D : ℝ := ∑ i, (a i - b i)^2 with hD
  have hPnn : 0 ≤ P := by rw [hP]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hQnn : 0 ≤ Q := by rw [hQ]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hRnn : 0 ≤ R := by rw [hR]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hDnn : 0 ≤ D := by rw [hD]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hA' : A = ε^2 * P := by
    rw [hA, hP]; simp only [ha, Pi.smul_apply, smul_eq_mul]; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hB' : B = ε^2 * Q := by
    rw [hB, hQ]; simp only [hb, Pi.smul_apply, smul_eq_mul]; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hD' : D = ε^2 * R := by
    rw [hD, hR]; simp only [ha, hb, Pi.smul_apply, smul_eq_mul]
    have : ∀ i, (ε * (m i : ℝ) - ε * (k i : ℝ))^2 = ε^2 * ((k i : ℝ) - (m i : ℝ))^2 :=
      fun i => by ring
    simp only [this]; rw [Finset.mul_sum]
  have hε2pos : 0 < ε^2 := by positivity
  have habsa : |ρ a| ≤ 1 := by have := hρb a; rwa [Real.norm_eq_abs] at this
  have habsb : |ρ b| ≤ 1 := by have := hρb b; rwa [Real.norm_eq_abs] at this
  have hnorm : ‖a - b‖ ≤ Real.sqrt D := by
    rw [hD]; exact norm_le_sqrt_sum_sq (a - b)
  have hlip : |ρ a - ρ b| ≤ L * Real.sqrt D := by
    rw [← Real.norm_eq_abs]
    exact le_trans (hρlip a b) (mul_le_mul_of_nonneg_left hnorm hL)
  have hsqD : (ρ a - ρ b)^2 ≤ L^2 * D := by
    have h3 := pow_le_pow_left₀ (abs_nonneg (ρ a - ρ b)) hlip 2
    rw [sq_abs, mul_pow, Real.sq_sqrt hDnn] at h3
    exact h3
  have hsL : (ρ a - ρ b)^2 ≤ L^2 * ε^2 * R := by
    rw [hD'] at hsqD
    linarith
  have hs4 : (ρ a - ρ b)^2 ≤ 4 := by
    have h3 : |ρ a - ρ b| ≤ 2 := by rw [abs_le] at habsa habsb ⊢; constructor <;> linarith
    have h2 := pow_le_pow_left₀ (abs_nonneg (ρ a - ρ b)) h3 2
    rw [sq_abs] at h2; norm_num at h2; exact h2
  -- the support hypothesis `hρ0` together with the Lipschitz bound suffices throughout
  -- the coordinatewise elementary inequality `(mᵢ)² ≤ 2 (kᵢ)² + 2 (mᵢ - kᵢ)²`
  have hQP : P ≤ 2*Q + 2*R := by
    rw [hP, hQ, hR, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (2*(k i : ℝ) - (m i : ℝ))]
  have hmain : (1+P) * (ρ a - ρ b)^2 ≤ 64 * (1+L^2) * (1+R) := by
    by_cases hAc : A ≤ 2
    · -- `ε² * Σ mᵢ² ≤ 2`: the weight is at most `2/ε²`
      have hAP : ε^2 * P ≤ 2 := by linarith [hA', hAc]
      have h1P : (1+P)*ε^2 ≤ 4 + ε^2 + 2*ε^2*R := by
        nlinarith [hAP, hRnn, hε2pos, mul_nonneg hε2pos.le hRnn]
      exact wt_arith hRnn hε hε1 hPnn h1P hs4 hsL
    · push Not at hAc
      by_cases hBc : B ≤ 2
      · -- `ε² * Σ kᵢ² ≤ 2`: use `‖m‖² ≤ 2‖k‖² + 2‖m - k‖²`
        have hQle : ε^2 * Q ≤ 2 := by linarith [hB', hBc]
        have hQP' : P * ε^2 ≤ (2*Q + 2*R) * ε^2 := mul_le_mul_of_nonneg_right hQP hε2pos.le
        have h1P : (1+P)*ε^2 ≤ 4 + ε^2 + 2*ε^2*R := by
          nlinarith [hQP', hQle, hRnn, hε2pos]
        exact wt_arith hRnn hε hε1 hPnn h1P hs4 hsL
      · -- both `ε • m` and `ε • k` lie outside the ball of radius `√2`
        push Not at hBc
        have ha0 : ρ a = 0 := hρ0 a (by rw [← hA]; exact hAc)
        have hb0 : ρ b = 0 := hρ0 b (by rw [← hB]; exact hBc)
        rw [ha0, hb0, sub_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero]
        positivity
  rw [Work.Diff.STE.wt, Work.Diff.STE.wt]
  simp only [Pi.sub_apply, Int.cast_sub]
  exact hmain

private lemma wt_neg {ι : Type*} [Fintype ι] (l : ι → ℤ) :
    Work.Diff.STE.wt (-l) = Work.Diff.STE.wt l := by
  unfold Work.Diff.STE.wt
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Pi.neg_apply, Int.cast_neg, neg_sq]

/-- The two-sided form of the slowly varying inequality for `wt`. -/
private lemma wt_sub_le {ι : Type*} [Fintype ι] (k l : ι → ℤ) :
    Work.Diff.STE.wt (k - l) ≤ 2 * (Work.Diff.STE.wt k * Work.Diff.STE.wt l) := by
  have h := wt_le_two_mul (k - l) k
  have hkk : (k - l) - k = -l := by abel
  rw [hkk, wt_neg] at h
  linarith

/-- Cauchy–Schwarz for `tsum` in the form `(Σ F G)² ≤ (Σ F²)(Σ G²)`. -/
private lemma tsum_mul_sq_le' {α : Type*} (F G : α → ℝ) (hF : ∀ l, 0 ≤ F l)
    (hG : ∀ l, 0 ≤ G l) (hFs : Summable (fun l => F l ^ 2))
    (hGs : Summable (fun l => G l ^ 2)) :
    (∑' l, F l * G l) ^ 2 ≤ (∑' l, F l ^ 2) * (∑' l, G l ^ 2) := by
  have hFG : Summable (fun l => F l * G l) := by
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (hF l) (hG l)) (fun l => ?_)
      (hFs.add hGs)
    nlinarith [hF l, hG l, sq_nonneg (F l - G l)]
  have key : ∀ t : Finset α, (∑ l ∈ t, F l * G l) ^ 2
      ≤ (∑' l, F l ^ 2) * (∑' l, G l ^ 2) := by
    intro t
    have h1 : (∑ l ∈ t, F l * G l) ^ 2
        ≤ (∑ l ∈ t, F l ^ 2) * (∑ l ∈ t, G l ^ 2) :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul t (fun l _ => sq_nonneg (F l))
        (fun l _ => sq_nonneg (G l)) (fun l _ => le_of_eq (by ring))
    calc (∑ l ∈ t, F l * G l) ^ 2
        ≤ (∑ l ∈ t, F l ^ 2) * (∑ l ∈ t, G l ^ 2) := h1
      _ ≤ (∑' l, F l ^ 2) * (∑' l, G l ^ 2) := by
          refine mul_le_mul (Summable.sum_le_tsum t (fun l _ => sq_nonneg _) hFs)
            (Summable.sum_le_tsum t (fun l _ => sq_nonneg _) hGs)
            (Finset.sum_nonneg (fun l _ => sq_nonneg _)) (tsum_nonneg fun l => sq_nonneg _)
  have hlim : Filter.Tendsto (fun t : Finset α => (∑ l ∈ t, F l * G l) ^ 2) Filter.atTop
      (nhds ((∑' l, F l * G l) ^ 2)) := by
    have hh := hFG.hasSum
    simp only [HasSum, SummationFilter.unconditional_filter] at hh
    exact hh.pow 2
  exact le_of_tendsto' hlim key

/-- Summability is invariant under the reflection `l ↦ k - l`. -/
private lemma summable_sub_le {α : Type*} [AddCommGroup α] {f : α → ℝ} (k : α)
    (hf : Summable f) : Summable (fun l => f (k - l)) := by
  refine hf.comp_injective (i := fun l : α => k - l) ?_
  intro a b hab
  have h0 : k - a = k - b := hab
  have h1 : -(k - a) = -(k - b) := by rw [h0]
  rw [neg_sub, neg_sub, sub_eq_add_neg, sub_eq_add_neg] at h1
  exact add_right_cancel h1

/-- If `u` has all weighted `ℓ¹` norms finite and `v ∈ ℓ²`, then
`l ↦ ‖u l‖ * ⟨k-l⟩ * ‖v (k-l)‖` is summable. -/
private lemma summable_norm_wt_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : (ι → ℤ) → ℂ)
    (hu : ∀ N : ℕ, Summable (fun l : ι → ℤ => (Work.Diff.STE.wt l) ^ N * ‖u l‖))
    (hv : Summable (fun m : ι → ℤ => ‖v m‖ ^ 2)) (k : ι → ℤ) :
    Summable (fun l : ι → ℤ => ‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖) := by
  have hu0 : Summable (fun l : ι → ℤ => ‖u l‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_) (hu 0)
    simp
  have hB : ∀ l, ‖u l‖ ≤ ∑' m, ‖u m‖ := fun l => hu0.le_tsum l (fun j _ => norm_nonneg _)
  have hBnn : (0 : ℝ) ≤ ∑' m, ‖u m‖ := tsum_nonneg fun _ => norm_nonneg _
  have hX : Summable (fun l => ‖u l‖ ^ 2 * Work.Diff.STE.wt (k - l) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun l => ?_) ((hu 2).mul_right (4 * Work.Diff.STE.wt k ^ 2 * (∑' m, ‖u m‖)))
    have h1 := wt_sub_le k l
    have h2 : Work.Diff.STE.wt (k - l) ^ 2
        ≤ (2 * (Work.Diff.STE.wt k * Work.Diff.STE.wt l)) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt (Work.Diff.STE.wt_pos _)) h1 2
    have h3 : ‖u l‖ ^ 2 ≤ (∑' m, ‖u m‖) * ‖u l‖ := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (hB l) (norm_nonneg _)
    calc ‖u l‖ ^ 2 * Work.Diff.STE.wt (k - l) ^ 2
        ≤ ‖u l‖ ^ 2 * (2 * (Work.Diff.STE.wt k * Work.Diff.STE.wt l)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = 4 * Work.Diff.STE.wt k ^ 2 * Work.Diff.STE.wt l ^ 2 * ‖u l‖ ^ 2 := by ring
      _ ≤ 4 * Work.Diff.STE.wt k ^ 2 * Work.Diff.STE.wt l ^ 2
            * ((∑' m, ‖u m‖) * ‖u l‖) :=
          mul_le_mul_of_nonneg_left h3
            (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _))
      _ = (Work.Diff.STE.wt l ^ 2 * ‖u l‖) * (4 * Work.Diff.STE.wt k ^ 2 * (∑' m, ‖u m‖)) :=
          by ring
  have hY : Summable (fun l => ‖v (k - l)‖ ^ 2) := summable_sub_le k hv
  refine Summable.of_nonneg_of_le
    (fun l => mul_nonneg (mul_nonneg (norm_nonneg _) (le_of_lt (Work.Diff.STE.wt_pos _)))
      (norm_nonneg _)) (fun l => ?_) (hX.add hY)
  nlinarith [sq_nonneg (‖u l‖ * Work.Diff.STE.wt (k - l) - ‖v (k - l)‖), norm_nonneg (u l),
    norm_nonneg (v (k - l)), le_of_lt (Work.Diff.STE.wt_pos (k - l))]

/-- The basic commutation identity for a Fourier multiplier `φ` (applied to the
`l`-variable) with the convolution operator `conv a`: writing the multiplier as a
coefficient family, the commutator applied to a family `ψ` produces the family with
the multiplier difference `φ (k-l) - φ k`. -/
private lemma tsum_diff_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a φ ψ : (ι → ℤ) → ℂ) (k : ι → ℤ)
    (h1 : Summable (fun l => a l * (φ (k - l) * ψ (k - l))))
    (h2 : Summable (fun l => a l * ψ (k - l))) :
    (∑' l, a l * (φ (k - l) * ψ (k - l))) - φ k * (∑' l, a l * ψ (k - l))
      = ∑' l, a l * ((φ (k - l) - φ k) * ψ (k - l)) := by
  rw [← tsum_mul_left]
  rw [← Summable.tsum_sub h1 (h2.mul_left (φ k))]
  exact tsum_congr fun l => by ring


private lemma norm_mul_mul (a X b : ℂ) : ‖a * (X * b)‖ = ‖a‖ * (‖X‖ * ‖b‖) := by
  rw [norm_mul, norm_mul]

private lemma norm_two_pi_I_mul (z : ℂ) :
    ‖(2 * (Real.pi : ℂ) * Complex.I) * z‖ = 2 * Real.pi * ‖z‖ := by
  calc ‖(2 * (Real.pi : ℂ) * Complex.I) * z‖
      = ‖(2 * (Real.pi : ℂ) * Complex.I)‖ * ‖z‖ := norm_mul _ _
    _ = 2 * Real.pi * ‖z‖ := by
        congr 1
        have hcast : (2 * (Real.pi : ℂ) * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [hcast]
        calc ‖((2 * Real.pi : ℝ) : ℂ) * Complex.I‖
            = ‖((2 * Real.pi : ℝ) : ℂ)‖ * ‖Complex.I‖ := norm_mul _ _
          _ = |2 * Real.pi| * 1 := by rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]
          _ = 2 * Real.pi := by rw [abs_of_pos (by positivity), mul_one]

private lemma norm_two_pi_I : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
  simpa using norm_two_pi_I_mul (1 : ℂ)

private lemma sq_sub_le_two (x y : ℝ) : (x - y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x + y)]

private lemma sq_add_le_two (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

/-- Summability of `l ↦ u l * (φ (k-l) * v (k-l))` for a bounded multiplier `φ`. -/
private lemma summable_mul_bdd {ι : Type*} [Fintype ι] [DecidableEq ι] (C : ℝ) (hC : 0 ≤ C)
    (φ : (ι → ℤ) → ℂ) (hφ : ∀ m, ‖φ m‖ ≤ C) (u v : (ι → ℤ) → ℂ)
    (hmaj : ∀ k : ι → ℤ,
      Summable (fun l : ι → ℤ => ‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖))
    (k : ι → ℤ) :
    Summable (fun l : ι → ℤ => u l * (φ (k - l) * v (k - l))) := by
  refine Summable.of_norm_bounded ((hmaj k).mul_left C) (fun l => ?_)
  calc ‖u l * (φ (k - l) * v (k - l))‖ = ‖u l‖ * (‖φ (k - l)‖ * ‖v (k - l)‖) :=
        norm_mul_mul _ _ _
    _ ≤ ‖u l‖ * (C * ‖v (k - l)‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hφ _) (norm_nonneg _)) (norm_nonneg _)
    _ = C * (‖u l‖ * ‖v (k - l)‖) := by ring
    _ ≤ C * (‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        calc ‖u l‖ * ‖v (k - l)‖ = (‖u l‖ * 1) * ‖v (k - l)‖ := by ring
          _ ≤ (‖u l‖ * Work.Diff.STE.wt (k - l)) * ‖v (k - l)‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (wt_one_le _) (norm_nonneg _)) (norm_nonneg _)
          _ = ‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖ := by ring

/-- Summability of `l ↦ u l * ((2πi (k-l)_i) * v (k-l))`, the family obtained by applying the
Fourier multiplier of `∂ᵢ` to `v`. -/
private lemma summable_mul_dmul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : (ι → ℤ) → ℂ)
    (hmaj : ∀ k : ι → ℤ,
      Summable (fun l : ι → ℤ => ‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖))
    (i : ι) (k : ι → ℤ) :
    Summable (fun l : ι → ℤ =>
      u l * ((2 * Real.pi * Complex.I * (((k - l) i : ℤ) : ℂ)) * v (k - l))) := by
  have hidx : ∀ l : ι → ℤ, ‖((((k - l) i : ℤ)) : ℂ)‖ ≤ Work.Diff.STE.wt (k - l) := by
    intro l
    rw [Complex.norm_intCast]
    have hsum : ((((k - l) i : ℤ) : ℝ)) ^ 2
        ≤ ∑ j : ι, ((((k - l) j : ℤ) : ℝ)) ^ 2 :=
      Finset.single_le_sum (f := fun j : ι => ((((k - l) j : ℤ) : ℝ)) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    simp only [Work.Diff.STE.wt]
    nlinarith [abs_nonneg ((((k - l) i : ℤ) : ℝ)), sq_abs ((((k - l) i : ℤ) : ℝ)),
      sq_nonneg (|((((k - l) i : ℤ) : ℝ))| - 1)]
  refine Summable.of_norm_bounded ((hmaj k).mul_left (2 * Real.pi)) (fun l => ?_)
  calc ‖u l * ((2 * Real.pi * Complex.I * (((k - l) i : ℤ) : ℂ)) * v (k - l))‖
      = ‖u l‖ * (‖(2 * Real.pi * Complex.I) * ((((k - l) i : ℤ)) : ℂ)‖ * ‖v (k - l)‖) :=
        norm_mul_mul _ _ _
    _ = ‖u l‖ * ((2 * Real.pi * ‖((((k - l) i : ℤ)) : ℂ)‖) * ‖v (k - l)‖) := by
        rw [norm_two_pi_I_mul]
    _ ≤ ‖u l‖ * ((2 * Real.pi * Work.Diff.STE.wt (k - l)) * ‖v (k - l)‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hidx l) (by positivity))
            (norm_nonneg _)) (norm_nonneg _)
    _ = (2 * Real.pi) * (‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖) := by ring

/-- Summability of the commutator summands: the multiplier difference against `v`. -/
private lemma summable_delta_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (u v : (ι → ℤ) → ℂ) (k : ι → ℤ)
    (hmaj : Summable (fun l : ι → ℤ =>
      ‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖)) :
    Summable (fun l : ι → ℤ =>
      u l * ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
            - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * v (k - l))) := by
  have hφ : ∀ m : ι → ℤ,
      ‖(((ρ (ε • (fun j => (m j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))) : ℝ) : ℂ)‖ ≤ 2 := by
    intro m
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 : |ρ (ε • (fun j => (m j : ℝ)))| ≤ 1 := by
      have h := hρb (ε • (fun j => (m j : ℝ)))
      rwa [Real.norm_eq_abs] at h
    have h2 : |ρ (ε • (fun j => (k j : ℝ)))| ≤ 1 := by
      have h := hρb (ε • (fun j => (k j : ℝ)))
      rwa [Real.norm_eq_abs] at h
    have hx := abs_le.mp h1
    have hy := abs_le.mp h2
    exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  refine Summable.of_norm_bounded (hmaj.mul_left 2) (fun l => ?_)
  rw [norm_mul_mul]
  have h1 : ‖((ρ (ε • (fun j => ((k - l) j : ℝ))) : ℝ) : ℂ)
      - (((ρ (ε • (fun j => (k j : ℝ))) : ℝ) : ℂ))‖ ≤ 2 := by
    rw [← Complex.ofReal_sub]
    exact hφ (k - l)
  calc ‖u l‖ * (‖((ρ (ε • (fun j => ((k - l) j : ℝ))) : ℝ) : ℂ)
        - (((ρ (ε • (fun j => (k j : ℝ))) : ℝ) : ℂ))‖ * ‖v (k - l)‖)
      ≤ ‖u l‖ * (2 * ‖v (k - l)‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) (norm_nonneg _)
    _ = 2 * (‖u l‖ * ‖v (k - l)‖) := by ring
    _ ≤ 2 * (‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        calc ‖u l‖ * ‖v (k - l)‖ = (‖u l‖ * 1) * ‖v (k - l)‖ := by ring
          _ ≤ (‖u l‖ * Work.Diff.STE.wt (k - l)) * ‖v (k - l)‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (wt_one_le _) (norm_nonneg _)) (norm_nonneg _)
          _ = ‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖ := by ring

/-- The commutation identity underlying the Friedrichs commutator estimate. -/
private lemma comm_eq_tsum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ) (u v : (ι → ℤ) → ℂ)
    (hmaj : ∀ k : ι → ℤ,
      Summable (fun l : ι → ℤ => ‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖))
    (k : ι → ℤ) :
    Work.Diff.STE.conv u (Work.Diff.STE.trunc ρ ε v) k
        - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv u v) k
      = ∑' l, u l * ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
            - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * v (k - l)) := by
  have hφ : ∀ m : ι → ℤ, ‖((ρ (ε • (fun j => (m j : ℝ))) : ℝ) : ℂ)‖ ≤ 2 := by
    intro m
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h := hρb (ε • (fun j => (m j : ℝ)))
    rw [Real.norm_eq_abs] at h
    linarith
  have h1 : Summable (fun l => u l * ((((ρ (ε • (fun j => ((k - l) j : ℝ))) : ℝ)) : ℂ) * v (k - l))) :=
    summable_mul_bdd 2 (by norm_num) _ hφ u v hmaj k
  have h2 : Summable (fun l => u l * v (k - l)) := by
    refine Summable.of_norm_bounded (hmaj k) (fun l => ?_)
    calc ‖u l * v (k - l)‖ = ‖u l‖ * ‖v (k - l)‖ := norm_mul _ _
      _ ≤ ‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖ := by
          calc ‖u l‖ * ‖v (k - l)‖ = (‖u l‖ * 1) * ‖v (k - l)‖ := by ring
            _ ≤ (‖u l‖ * Work.Diff.STE.wt (k - l)) * ‖v (k - l)‖ :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (wt_one_le _) (norm_nonneg _)) (norm_nonneg _)
            _ = ‖u l‖ * Work.Diff.STE.wt (k - l) * ‖v (k - l)‖ := by ring
  have hdiff := tsum_diff_mul u (fun m => (((ρ (ε • (fun j => (m j : ℝ))) : ℝ)) : ℂ)) v k h1 h2
  simpa [Work.Diff.STE.conv, Work.Diff.STE.trunc, Complex.ofReal_sub] using hdiff


/-- **Friedrichs commutator, gain of one derivative.**  For a coefficient family `a` all of whose
weighted `ℓ¹` norms are finite and any Friedrichs profile `ρ`, the commutator of the convolution
with `a` and the mollifier `trunc ρ ε` maps the weighted `ℓ²` space of order `s` into the one of
order `s+1`, with a bound that is uniform in `ε ∈ (0,1]`. -/
private theorem CSq_succ_commutator_le_supp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : ι → ℝ, 2 < (∑ i, (y i) ^ 2) → ρ y = 0)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (a : (ι → ℤ) → ℂ)
    (ha : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖a k‖))
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ c : (ι → ℤ) → ℂ,
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2) →
      Summable (fun k : ι → ℤ =>
          (Work.Diff.STE.wt k) ^ (s + 1)
            * ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
                - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖ ^ 2) ∧
      Work.Diff.STE.CSq (s + 1)
          (fun k => Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
            - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k)
        ≤ C * Work.Diff.STE.CSq s c := by
  classical
  set K : ℝ := 64 * (1 + L ^ 2) with hK
  set A2 : ℝ := ∑' l : ι → ℤ, (Work.Diff.STE.wt l) ^ (2 * s + 2) * ‖a l‖ with hA2
  set As : ℝ := ∑' l : ι → ℤ, (Work.Diff.STE.wt l) ^ s * ‖a l‖ with hAs
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  have hA2nn : 0 ≤ A2 :=
    tsum_nonneg fun l => mul_nonneg (pow_nonneg (le_of_lt (wt_pos l)) _) (norm_nonneg _)
  have hAsnn : 0 ≤ As :=
    tsum_nonneg fun l => mul_nonneg (pow_nonneg (le_of_lt (wt_pos l)) _) (norm_nonneg _)
  refine ⟨2 ^ (3 * s + 1) * K * A2 * As, by positivity, ?_⟩
  intro ε hε hε1 c hc
  have ha0 : Summable (fun l : ι → ℤ => ‖a l‖) := by simpa using ha 0
  have hc2 : Summable (fun m : ι → ℤ => ‖c m‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun m => sq_nonneg _) (fun m => ?_) hc
    have h1 : (1 : ℝ) ≤ Work.Diff.STE.wt m ^ s := by
      calc (1 : ℝ) = 1 ^ s := (one_pow s).symm
        _ ≤ Work.Diff.STE.wt m ^ s := pow_le_pow_left₀ (by norm_num) (wt_one_le m) s
    exact le_mul_of_one_le_left (sq_nonneg _) h1
  have hA2sum : Summable (fun l : ι → ℤ => (Work.Diff.STE.wt l) ^ (2 * s + 2) * ‖a l‖) :=
    ha (2 * s + 2)
  have hAssum : Summable (fun l : ι → ℤ => (Work.Diff.STE.wt l) ^ s * ‖a l‖) := ha s
  have hmaj : ∀ k : ι → ℤ,
      Summable (fun l : ι → ℤ => ‖a l‖ * Work.Diff.STE.wt (k - l) * ‖c (k - l)‖) :=
    fun k => summable_norm_wt_mul a c ha hc2 k
  -- the explicit form of the commutator
  have hQeq : ∀ k : ι → ℤ,
      Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k
        = ∑' l, a l * ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
              - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * c (k - l)) :=
    fun k => comm_eq_tsum ρ hρb ε a c hmaj k
  -- the norm bound
  have hnorm : ∀ k : ι → ℤ,
      ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖
        ≤ ∑' l, ‖a l‖
            * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| * ‖c (k - l)‖ := by
    intro k
    rw [hQeq k]
    have hsum : Summable (fun l : ι → ℤ =>
        ‖a l * ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
              - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * c (k - l))‖) := by
      refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_)
        ((hmaj k).mul_left 2)
      rw [norm_mul_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hδb : |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ≤ 2 := by
        have h1 : |ρ (ε • (fun j => ((k - l) j : ℝ)))| ≤ 1 := by
          have h := hρb (ε • (fun j => ((k - l) j : ℝ)))
          rwa [Real.norm_eq_abs] at h
        have h2 : |ρ (ε • (fun j => (k j : ℝ)))| ≤ 1 := by
          have h := hρb (ε • (fun j => (k j : ℝ)))
          rwa [Real.norm_eq_abs] at h
        have hx := abs_le.mp h1
        have hy := abs_le.mp h2
        exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
      calc ‖a l‖ * (|ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| * ‖c (k - l)‖)
          ≤ ‖a l‖ * (2 * ‖c (k - l)‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hδb (norm_nonneg _)) (norm_nonneg _)
        _ = 2 * (‖a l‖ * ‖c (k - l)‖) := by ring
        _ ≤ 2 * (‖a l‖ * Work.Diff.STE.wt (k - l) * ‖c (k - l)‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            calc ‖a l‖ * ‖c (k - l)‖ = (‖a l‖ * 1) * ‖c (k - l)‖ := by ring
              _ ≤ (‖a l‖ * Work.Diff.STE.wt (k - l)) * ‖c (k - l)‖ :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left (wt_one_le _) (norm_nonneg _)) (norm_nonneg _)
              _ = ‖a l‖ * Work.Diff.STE.wt (k - l) * ‖c (k - l)‖ := by ring
    calc ‖∑' l, a l * ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
            - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * c (k - l))‖
        ≤ ∑' l, ‖a l * ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
            - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * c (k - l))‖ :=
          norm_tsum_le_tsum_norm hsum
      _ = ∑' l, ‖a l‖
            * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| * ‖c (k - l)‖ :=
          tsum_congr fun l => by
            rw [norm_mul_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
            ring
  -- summability of the two Cauchy–Schwarz factors
  have hPsi : ∀ k : ι → ℤ,
      Summable (fun l : ι → ℤ =>
        ‖a l‖ * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2) := by
    intro k
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun l => ?_) (ha0.mul_left 4)
    have hb : |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2 ≤ 4 := by
      have h1 : |ρ (ε • (fun j => ((k - l) j : ℝ)))| ≤ 1 := by
        have h := hρb (ε • (fun j => ((k - l) j : ℝ)))
        rwa [Real.norm_eq_abs] at h
      have h2 : |ρ (ε • (fun j => (k j : ℝ)))| ≤ 1 := by
        have h := hρb (ε • (fun j => (k j : ℝ)))
        rwa [Real.norm_eq_abs] at h
      have hx := abs_le.mp h1
      have hy := abs_le.mp h2
      have hxy : |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ≤ 2 :=
        abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
      nlinarith [hxy, abs_nonneg (ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ))))]
    calc ‖a l‖ * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2
        ≤ ‖a l‖ * 4 := mul_le_mul_of_nonneg_left hb (norm_nonneg (a l))
      _ = 4 * ‖a l‖ := by ring
  have hGamma : ∀ k : ι → ℤ,
      Summable (fun l : ι → ℤ => ‖a l‖ * ‖c (k - l)‖ ^ 2) := by
    intro k
    have hb : ∀ m : ι → ℤ, ‖c m‖ ^ 2 ≤ ∑' m : ι → ℤ, ‖c m‖ ^ 2 :=
      fun m => hc2.le_tsum m (fun j _ => sq_nonneg _)
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun l => mul_le_mul_of_nonneg_left (hb (k - l)) (norm_nonneg _)) (ha0.mul_right _)
  -- Cauchy–Schwarz at each frequency
  have hCS : ∀ k : ι → ℤ,
      (∑' l, ‖a l‖
          * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| * ‖c (k - l)‖) ^ 2
        ≤ (∑' l, ‖a l‖
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2)
          * (∑' l, ‖a l‖ * ‖c (k - l)‖ ^ 2) := by
    intro k
    have hFnn : ∀ l : ι → ℤ, 0 ≤ Real.sqrt (‖a l‖)
        * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| :=
      fun l => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
    have hGnn : ∀ l : ι → ℤ, 0 ≤ Real.sqrt (‖a l‖) * ‖c (k - l)‖ :=
      fun l => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hF2 : Summable (fun l : ι → ℤ => (Real.sqrt (‖a l‖)
        * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))|) ^ 2) := by
      refine (hPsi k).congr fun l => ?_
      rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
    have hG2 : Summable (fun l : ι → ℤ => (Real.sqrt (‖a l‖) * ‖c (k - l)‖) ^ 2) := by
      refine (hGamma k).congr fun l => ?_
      rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
    have hmain := tsum_mul_sq_le' (fun l : ι → ℤ => Real.sqrt (‖a l‖)
        * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))|)
      (fun l : ι → ℤ => Real.sqrt (‖a l‖) * ‖c (k - l)‖) hFnn hGnn hF2 hG2
    calc (∑' l, ‖a l‖
            * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| * ‖c (k - l)‖) ^ 2
        = (∑' l, (Real.sqrt (‖a l‖)
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))|)
            * (Real.sqrt (‖a l‖) * ‖c (k - l)‖)) ^ 2 := by
          congr 1
          refine tsum_congr fun l => ?_
          rw [show (Real.sqrt (‖a l‖)
                * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))|)
              * (Real.sqrt (‖a l‖) * ‖c (k - l)‖)
            = (Real.sqrt (‖a l‖) * Real.sqrt (‖a l‖))
              * (|ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| * ‖c (k - l)‖)
            from by ring,
            Real.mul_self_sqrt (norm_nonneg _)]
          ring
      _ ≤ (∑' l, (Real.sqrt (‖a l‖)
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))|) ^ 2)
          * (∑' l, (Real.sqrt (‖a l‖) * ‖c (k - l)‖) ^ 2) := hmain
      _ = (∑' l, ‖a l‖
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2)
          * (∑' l, ‖a l‖ * ‖c (k - l)‖ ^ 2) := by
          congr 1
          · exact tsum_congr fun l => by rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
          · exact tsum_congr fun l => by rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
  -- the first Cauchy–Schwarz factor, bounded
  have hPsiBound : ∀ k : ι → ℤ,
      (Work.Diff.STE.wt k) ^ (s + 1)
          * (∑' l, ‖a l‖
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2)
        ≤ (2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s) * A2 := by
    intro k
    have hpt : ∀ l : ι → ℤ,
        (Work.Diff.STE.wt k) ^ (s + 1) * (‖a l‖
            * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2)
          ≤ (2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s)
            * ((Work.Diff.STE.wt l) ^ (2 * s + 2) * ‖a l‖) := by
      intro l
      have hD1 : Work.Diff.STE.wt (k - l)
          * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2
            ≤ K * Work.Diff.STE.wt l := by
        have h := friedrichs_pointwise_supp ρ hρb hρ0 L hL hρlip ε hε hε1 k (k - l)
        rw [sub_sub_self] at h
        rw [hK]
        rw [sq_abs]
        exact h
      have hZnn : (0 : ℝ) ≤ (Work.Diff.STE.wt (k - l)) ^ s :=
        pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos _)) s
      have hp1 := wt_pow_le (s + 1) k l
      have hp2 : (Work.Diff.STE.wt (k - l)) ^ s
          ≤ 2 ^ s * ((Work.Diff.STE.wt k) ^ s * (Work.Diff.STE.wt l) ^ s) := by
        have h := wt_sub_le k l
        calc (Work.Diff.STE.wt (k - l)) ^ s
            ≤ (2 * (Work.Diff.STE.wt k * Work.Diff.STE.wt l)) ^ s :=
              pow_le_pow_left₀ (le_of_lt (Work.Diff.STE.wt_pos _)) h s
          _ = 2 ^ s * ((Work.Diff.STE.wt k) ^ s * (Work.Diff.STE.wt l) ^ s) := by
              rw [mul_pow, mul_pow]
      have h2 : (Work.Diff.STE.wt (k - l)) ^ (s + 1)
          * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2
            ≤ (Work.Diff.STE.wt (k - l)) ^ s * (K * Work.Diff.STE.wt l) := by
        calc (Work.Diff.STE.wt (k - l)) ^ (s + 1)
            * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2
            = (Work.Diff.STE.wt (k - l)) ^ s
              * (Work.Diff.STE.wt (k - l)
                * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2) := by
              ring
          _ ≤ (Work.Diff.STE.wt (k - l)) ^ s * (K * Work.Diff.STE.wt l) :=
              mul_le_mul_of_nonneg_left hD1 hZnn
      have hstep : (Work.Diff.STE.wt k) ^ (s + 1)
          * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2
            ≤ 2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s * (Work.Diff.STE.wt l) ^ (2 * s + 2) := by
        calc (Work.Diff.STE.wt k) ^ (s + 1)
            * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2
            ≤ (2 ^ (s + 1) * ((Work.Diff.STE.wt l) ^ (s + 1)
                * (Work.Diff.STE.wt (k - l)) ^ (s + 1)))
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2 :=
              mul_le_mul_of_nonneg_right hp1 (sq_nonneg _)
          _ = 2 ^ (s + 1) * (Work.Diff.STE.wt l) ^ (s + 1)
              * ((Work.Diff.STE.wt (k - l)) ^ (s + 1)
                * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2) := by
              ring
          _ ≤ 2 ^ (s + 1) * (Work.Diff.STE.wt l) ^ (s + 1)
              * ((Work.Diff.STE.wt (k - l)) ^ s * (K * Work.Diff.STE.wt l)) :=
              mul_le_mul_of_nonneg_left h2
                (mul_nonneg (by positivity) (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) _))
          _ ≤ 2 ^ (s + 1) * (Work.Diff.STE.wt l) ^ (s + 1)
              * ((2 ^ s * ((Work.Diff.STE.wt k) ^ s * (Work.Diff.STE.wt l) ^ s))
                * (K * Work.Diff.STE.wt l)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hp2
                  (mul_nonneg hKnn (le_of_lt (Work.Diff.STE.wt_pos l))))
                (mul_nonneg (by positivity) (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) _))
          _ = 2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s * (Work.Diff.STE.wt l) ^ (2 * s + 2) := by
              ring
      calc (Work.Diff.STE.wt k) ^ (s + 1) * (‖a l‖
            * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2)
          = ‖a l‖ * ((Work.Diff.STE.wt k) ^ (s + 1)
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2) := by
            ring
        _ ≤ ‖a l‖ * (2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s
              * (Work.Diff.STE.wt l) ^ (2 * s + 2)) :=
            mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
        _ = (2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s)
            * ((Work.Diff.STE.wt l) ^ (2 * s + 2) * ‖a l‖) := by ring
    calc (Work.Diff.STE.wt k) ^ (s + 1)
          * (∑' l, ‖a l‖
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2)
        = ∑' l, (Work.Diff.STE.wt k) ^ (s + 1) * (‖a l‖
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2) := by
          rw [tsum_mul_left]
      _ ≤ ∑' l, (2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s)
            * ((Work.Diff.STE.wt l) ^ (2 * s + 2) * ‖a l‖) :=
          Summable.tsum_le_tsum hpt ((hPsi k).mul_left _) (hA2sum.mul_left _)
      _ = (2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s) * A2 := by
          rw [tsum_mul_left, ← hA2]
  -- the second factor, summed over the frequency
  have hreindex : ∀ k : ι → ℤ,
      (∑' l : ι → ℤ, ‖a l‖ * ‖c (k - l)‖ ^ 2)
        = ∑' m : ι → ℤ, ‖a (k - m)‖ * ‖c m‖ ^ 2 := by
    intro k
    let e : (ι → ℤ) ≃ (ι → ℤ) :=
      { toFun := fun l => k - l
        invFun := fun l => k - l
        left_inv := fun l => sub_sub_self k l
        right_inv := fun l => sub_sub_self k l }
    have h := Equiv.tsum_eq e (fun l : ι → ℤ => ‖a l‖ * ‖c (k - l)‖ ^ 2)
    simpa [e, sub_sub_self] using h.symm
  have hGammasumm : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s
      * (∑' l : ι → ℤ, ‖a l‖ * ‖c (k - l)‖ ^ 2)) := by
    refine ((wt_shift_conv_tsum a c s hAssum hc).1).congr fun k => ?_
    rw [hreindex k]
  have hGammaLe : (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s
      * (∑' l : ι → ℤ, ‖a l‖ * ‖c (k - l)‖ ^ 2)) ≤ 2 ^ s * As * Work.Diff.STE.CSq s c := by
    have h := (wt_shift_conv_tsum a c s hAssum hc).2
    calc (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s
          * (∑' l : ι → ℤ, ‖a l‖ * ‖c (k - l)‖ ^ 2))
        = ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s
            * (∑' m : ι → ℤ, ‖a (k - m)‖ * ‖c m‖ ^ 2) :=
          tsum_congr fun k => by rw [hreindex k]
      _ ≤ 2 ^ s * As * Work.Diff.STE.CSq s c := by
          refine h.trans_eq ?_
          rw [← hAs]
          rfl
  -- the pointwise bound for the commutator, weighted
  have hQbound : ∀ k : ι → ℤ, (Work.Diff.STE.wt k) ^ (s + 1)
        * ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
            - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖ ^ 2
      ≤ 2 ^ (2 * s + 1) * K * A2 * ((Work.Diff.STE.wt k) ^ s
          * (∑' l : ι → ℤ, ‖a l‖ * ‖c (k - l)‖ ^ 2)) := by
    intro k
    calc (Work.Diff.STE.wt k) ^ (s + 1)
          * ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
              - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖ ^ 2
        ≤ (Work.Diff.STE.wt k) ^ (s + 1)
            * (∑' l, ‖a l‖
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| * ‖c (k - l)‖) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hnorm k) 2)
            (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _)
      _ ≤ (Work.Diff.STE.wt k) ^ (s + 1)
            * ((∑' l, ‖a l‖
                * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2)
              * (∑' l, ‖a l‖ * ‖c (k - l)‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (hCS k) (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _)
      _ = ((Work.Diff.STE.wt k) ^ (s + 1)
            * (∑' l, ‖a l‖
              * |ρ (ε • (fun j => ((k - l) j : ℝ))) - ρ (ε • (fun j => (k j : ℝ)))| ^ 2))
          * (∑' l, ‖a l‖ * ‖c (k - l)‖ ^ 2) := by ring
      _ ≤ (2 ^ (2 * s + 1) * K * (Work.Diff.STE.wt k) ^ s * A2)
          * (∑' l, ‖a l‖ * ‖c (k - l)‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (hPsiBound k)
            (tsum_nonneg fun l => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      _ = 2 ^ (2 * s + 1) * K * A2 * ((Work.Diff.STE.wt k) ^ s
          * (∑' l, ‖a l‖ * ‖c (k - l)‖ ^ 2)) := by ring
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _) (sq_nonneg _))
      hQbound (hGammasumm.mul_left _)
  · have hsumm : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (s + 1)
        * ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
            - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖ ^ 2) :=
      Summable.of_nonneg_of_le
        (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _) (sq_nonneg _))
        hQbound (hGammasumm.mul_left _)
    calc Work.Diff.STE.CSq (s + 1)
          (fun k => Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
            - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k)
        = ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ (s + 1)
            * ‖Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
                - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k‖ ^ 2 := rfl
      _ ≤ ∑' k : ι → ℤ, 2 ^ (2 * s + 1) * K * A2 * ((Work.Diff.STE.wt k) ^ s
            * (∑' l : ι → ℤ, ‖a l‖ * ‖c (k - l)‖ ^ 2)) :=
          Summable.tsum_le_tsum hQbound hsumm (hGammasumm.mul_left _)
      _ = 2 ^ (2 * s + 1) * K * A2 * (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s
            * (∑' l : ι → ℤ, ‖a l‖ * ‖c (k - l)‖ ^ 2)) := by
          rw [tsum_mul_left]
      _ ≤ 2 ^ (2 * s + 1) * K * A2 * (2 ^ s * As * Work.Diff.STE.CSq s c) :=
          mul_le_mul_of_nonneg_left hGammaLe (by positivity)
      _ = (2 ^ (3 * s + 1) * K * A2 * As) * Work.Diff.STE.CSq s c := by ring

/-- The weight controls the coordinate of a lattice point. -/
private lemma norm_intCast_le_wt {ι : Type*} [Fintype ι] (m : ι → ℤ) (i : ι) :
    ‖(((m i : ℤ)) : ℂ)‖ ≤ Work.Diff.STE.wt m := by
  rw [Complex.norm_intCast]
  have hsum : (((m i : ℤ) : ℝ)) ^ 2 ≤ ∑ j : ι, (((m j : ℤ) : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun j : ι => (((m j : ℤ) : ℝ)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  simp only [Work.Diff.STE.wt]
  nlinarith [abs_nonneg (((m i : ℤ) : ℝ)), sq_abs (((m i : ℤ) : ℝ)),
    sq_nonneg (|(((m i : ℤ) : ℝ))| - 1)]

private lemma sq_intCast_coord_le_wt {ι : Type*} [Fintype ι] (m : ι → ℤ) (i : ι) :
    (((m i : ℤ) : ℝ)) ^ 2 ≤ Work.Diff.STE.wt m := by
  have hsum : (((m i : ℤ) : ℝ)) ^ 2 ≤ ∑ j : ι, (((m j : ℤ) : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun j : ι => (((m j : ℤ) : ℝ)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  simp only [Work.Diff.STE.wt]
  linarith

/-- The Fourier-side derivative `dmul i` costs one weight: `‖dmul i c m‖ ≤ 2π ⟨m⟩ ‖c m‖`. -/
private lemma norm_dmul_le {ι : Type*} [Fintype ι] (i : ι) (c : (ι → ℤ) → ℂ) (m : ι → ℤ) :
    ‖Work.Diff.STE.dmul i c m‖ ≤ 2 * Real.pi * (Work.Diff.STE.wt m * ‖c m‖) := by
  have hA : ‖(2 * Real.pi * Complex.I * (((m i : ℤ)) : ℂ))‖
      = 2 * Real.pi * ‖((((m i : ℤ)) : ℂ))‖ := norm_two_pi_I_mul _
  calc ‖Work.Diff.STE.dmul i c m‖
      = ‖(2 * Real.pi * Complex.I * (((m i : ℤ)) : ℂ))‖ * ‖c m‖ := by
        rw [Work.Diff.STE.dmul, norm_mul]
    _ = (2 * Real.pi * ‖((((m i : ℤ)) : ℂ))‖) * ‖c m‖ := by rw [hA]
    _ ≤ (2 * Real.pi * Work.Diff.STE.wt m) * ‖c m‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (norm_intCast_le_wt m i) (by positivity)
    _ = 2 * Real.pi * (Work.Diff.STE.wt m * ‖c m‖) := by ring

theorem friedrichs_commutator_supp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (a : (ι → ℤ) → ℂ)
    (ha : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖a k‖))
    (s : ℕ) (i : ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ c : (ι → ℤ) → ℂ,
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2) →
      Work.Diff.STE.CSq s
          (fun k => Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
            - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a (Work.Diff.STE.dmul i c)) k)
        ≤ C * Work.Diff.STE.CSq s c := by
  classical
  obtain ⟨C1, hC1nn, hC1⟩ := CSq_succ_commutator_le_supp ρ hρb hdiam L hL hρlip a ha s
  have hb : ∀ N : ℕ, Summable (fun l : ι → ℤ =>
      (Work.Diff.STE.wt l) ^ N * ‖a l * (((l i : ℤ)) : ℂ)‖) := by
    intro N
    refine Summable.of_nonneg_of_le
      (fun l => mul_nonneg (pow_nonneg (le_of_lt (wt_pos l)) _) (norm_nonneg _)) (fun l => ?_)
      (ha (N + 1))
    calc (Work.Diff.STE.wt l) ^ N * ‖a l * (((l i : ℤ)) : ℂ)‖
        = (Work.Diff.STE.wt l) ^ N * (‖a l‖ * ‖((((l i : ℤ)) : ℂ))‖) := by rw [norm_mul]
      _ ≤ (Work.Diff.STE.wt l) ^ N * (‖a l‖ * Work.Diff.STE.wt l) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (norm_intCast_le_wt l i) (norm_nonneg _))
            (pow_nonneg (le_of_lt (wt_pos l)) _)
      _ = (Work.Diff.STE.wt l) ^ (N + 1) * ‖a l‖ := by ring
  obtain ⟨C2, hC2nn, hC2⟩ := CSq_succ_commutator_le_supp ρ hρb hdiam L hL hρlip
    (fun l => a l * (((l i : ℤ)) : ℂ)) hb s
  refine ⟨8 * Real.pi ^ 2 * (C1 + C2), by positivity, ?_⟩
  intro ε hε hε1 c hc
  let Q : (ι → ℤ) → ℂ := fun k => Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε c) k
    - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a c) k
  let R : (ι → ℤ) → ℂ := fun k =>
    Work.Diff.STE.conv (fun l => a l * (((l i : ℤ)) : ℂ)) (Work.Diff.STE.trunc ρ ε c) k
      - Work.Diff.STE.trunc ρ ε
          (Work.Diff.STE.conv (fun l => a l * (((l i : ℤ)) : ℂ)) c) k
  let P : (ι → ℤ) → ℂ := fun k =>
    Work.Diff.STE.conv a (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.dmul i c)) k
      - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv a (Work.Diff.STE.dmul i c)) k
  have ha0 : Summable (fun l : ι → ℤ => ‖a l‖) := by simpa using ha 0
  have hc2 : Summable (fun m : ι → ℤ => ‖c m‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun m => sq_nonneg _) (fun m => ?_) hc
    have h1 : (1 : ℝ) ≤ Work.Diff.STE.wt m ^ s := by
      calc (1 : ℝ) = 1 ^ s := (one_pow s).symm
        _ ≤ Work.Diff.STE.wt m ^ s := pow_le_pow_left₀ (by norm_num) (wt_one_le m) s
    exact le_mul_of_one_le_left (sq_nonneg _) h1
  have hBc : (0 : ℝ) ≤ Real.sqrt (∑' m : ι → ℤ, ‖c m‖ ^ 2) := Real.sqrt_nonneg _
  have hcb : ∀ m : ι → ℤ, ‖c m‖ ≤ Real.sqrt (∑' m : ι → ℤ, ‖c m‖ ^ 2) :=
    fun m => Real.le_sqrt_of_sq_le (hc2.le_tsum m (fun j _ => sq_nonneg _))
  have hmajac : ∀ k : ι → ℤ,
      Summable (fun l : ι → ℤ => ‖a l‖ * Work.Diff.STE.wt (k - l) * ‖c (k - l)‖) :=
    fun k => summable_norm_wt_mul a c ha hc2 k
  have hmajbc : ∀ k : ι → ℤ, Summable (fun l : ι → ℤ =>
      ‖a l * (((l i : ℤ)) : ℂ)‖ * Work.Diff.STE.wt (k - l) * ‖c (k - l)‖) :=
    fun k => summable_norm_wt_mul (fun l => a l * (((l i : ℤ)) : ℂ)) c hb hc2 k
  have hwt2 : ∀ k : ι → ℤ, Summable (fun l : ι → ℤ =>
      ‖a l‖ * Work.Diff.STE.wt (k - l) ^ 2) := by
    intro k
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun l => ?_) ((ha 2).mul_right (4 * Work.Diff.STE.wt k ^ 2))
    have h := wt_sub_le k l
    have h2 : Work.Diff.STE.wt (k - l) ^ 2
        ≤ (2 * (Work.Diff.STE.wt k * Work.Diff.STE.wt l)) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt (Work.Diff.STE.wt_pos _)) h 2
    calc ‖a l‖ * Work.Diff.STE.wt (k - l) ^ 2
        ≤ ‖a l‖ * (2 * (Work.Diff.STE.wt k * Work.Diff.STE.wt l)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = (Work.Diff.STE.wt l ^ 2 * ‖a l‖) * (4 * Work.Diff.STE.wt k ^ 2) := by ring
  have hmajP : ∀ k : ι → ℤ, Summable (fun l : ι → ℤ =>
      ‖a l‖ * Work.Diff.STE.wt (k - l) * ‖Work.Diff.STE.dmul i c (k - l)‖) := by
    intro k
    refine Summable.of_nonneg_of_le
      (fun l => mul_nonneg (mul_nonneg (norm_nonneg _) (le_of_lt (wt_pos _))) (norm_nonneg _))
      (fun l => ?_)
      ((hwt2 k).mul_left (2 * Real.pi * Real.sqrt (∑' m : ι → ℤ, ‖c m‖ ^ 2)))
    calc ‖a l‖ * Work.Diff.STE.wt (k - l) * ‖Work.Diff.STE.dmul i c (k - l)‖
        ≤ ‖a l‖ * Work.Diff.STE.wt (k - l)
            * (2 * Real.pi * (Work.Diff.STE.wt (k - l) * ‖c (k - l)‖)) :=
          mul_le_mul_of_nonneg_left (norm_dmul_le i c (k - l))
            (mul_nonneg (norm_nonneg _) (le_of_lt (wt_pos _)))
      _ ≤ ‖a l‖ * Work.Diff.STE.wt (k - l)
            * (2 * Real.pi * (Work.Diff.STE.wt (k - l)
              * Real.sqrt (∑' m : ι → ℤ, ‖c m‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hcb (k - l)) (le_of_lt (wt_pos _)))
              (by positivity)) (mul_nonneg (norm_nonneg _) (le_of_lt (wt_pos _)))
      _ = (2 * Real.pi * Real.sqrt (∑' m : ι → ℤ, ‖c m‖ ^ 2))
            * (‖a l‖ * Work.Diff.STE.wt (k - l) ^ 2) := by ring
  have hsumδ : ∀ k : ι → ℤ, Summable (fun l : ι → ℤ =>
      a l * ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
            - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * c (k - l))) :=
    fun k => summable_delta_mul ρ hρb ε a c k (hmajac k)
  have hsumδb : ∀ k : ι → ℤ, Summable (fun l : ι → ℤ =>
      (a l * (((l i : ℤ)) : ℂ)) * ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
            - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * c (k - l))) :=
    fun k => summable_delta_mul ρ hρb ε (fun l => a l * (((l i : ℤ)) : ℂ)) c k (hmajbc k)
  have hPsum : ∀ k : ι → ℤ, P k
      = ∑' l, a l * ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
            - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * Work.Diff.STE.dmul i c (k - l)) := by
    intro k
    exact comm_eq_tsum ρ hρb ε a (Work.Diff.STE.dmul i c) hmajP k
  have hQsum : ∀ k : ι → ℤ, Q k
      = ∑' l, a l * ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
            - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * c (k - l)) := by
    intro k
    exact comm_eq_tsum ρ hρb ε a c hmajac k
  have hRsum : ∀ k : ι → ℤ, R k
      = ∑' l, (a l * (((l i : ℤ)) : ℂ)) * ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
            - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * c (k - l)) := by
    intro k
    exact comm_eq_tsum ρ hρb ε (fun l => a l * (((l i : ℤ)) : ℂ)) c hmajbc k
  have hsplit : ∀ k : ι → ℤ,
      P k = 2 * Real.pi * Complex.I * (((k i : ℤ)) : ℂ) * Q k - 2 * Real.pi * Complex.I * R k := by
    intro k
    rw [hPsum k, hQsum k, hRsum k]
    have h1 : Summable (fun l : ι → ℤ =>
        (2 * Real.pi * Complex.I * (((k i : ℤ)) : ℂ)) * (a l *
          ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
            - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * c (k - l)))) :=
      (hsumδ k).mul_left _
    have h2 : Summable (fun l : ι → ℤ =>
        (2 * Real.pi * Complex.I) * ((a l * (((l i : ℤ)) : ℂ)) *
          ((((ρ (ε • (fun j => ((k - l) j : ℝ))))
            - ρ (ε • (fun j => (k j : ℝ)))) : ℂ) * c (k - l)))) :=
      (hsumδb k).mul_left _
    rw [← tsum_mul_left, ← tsum_mul_left]
    rw [← Summable.tsum_sub h1 h2]
    refine tsum_congr fun l => ?_
    simp only [Work.Diff.STE.dmul, Pi.sub_apply]
    push_cast
    ring
  have hki2 : ∀ k : ι → ℤ, ‖((((k i : ℤ)) : ℂ))‖ ^ 2 ≤ Work.Diff.STE.wt k := by
    intro k
    have h := sq_intCast_coord_le_wt k i
    have h2 : ‖((((k i : ℤ)) : ℂ))‖ = |(((k i : ℤ) : ℝ))| := Complex.norm_intCast (k i)
    rw [h2]
    nlinarith [sq_abs (((k i : ℤ) : ℝ)), h]
  have hnormP : ∀ k : ι → ℤ, (Work.Diff.STE.wt k) ^ s * ‖P k‖ ^ 2
      ≤ 8 * Real.pi ^ 2 * ((Work.Diff.STE.wt k) ^ (s + 1) * ‖Q k‖ ^ 2
          + (Work.Diff.STE.wt k) ^ s * ‖R k‖ ^ 2) := by
    intro k
    have hA : ‖(2 * Real.pi * Complex.I * (((k i : ℤ)) : ℂ)) * Q k‖
        = 2 * Real.pi * ‖((((k i : ℤ)) : ℂ))‖ * ‖Q k‖ := by
      calc ‖(2 * Real.pi * Complex.I * (((k i : ℤ)) : ℂ)) * Q k‖
          = ‖(2 * Real.pi * Complex.I * (((k i : ℤ)) : ℂ))‖ * ‖Q k‖ := norm_mul _ _
        _ = (2 * Real.pi * ‖((((k i : ℤ)) : ℂ))‖) * ‖Q k‖ := by rw [norm_two_pi_I_mul]
    have hB : ‖(2 * Real.pi * Complex.I) * R k‖ = 2 * Real.pi * ‖R k‖ := by
      calc ‖(2 * Real.pi * Complex.I) * R k‖
          = ‖(2 * Real.pi * Complex.I)‖ * ‖R k‖ := norm_mul _ _
        _ = 2 * Real.pi * ‖R k‖ := by rw [norm_two_pi_I]
    have hbr : 2 * (2 * Real.pi * ‖((((k i : ℤ)) : ℂ))‖ * ‖Q k‖) ^ 2
          + 2 * (2 * Real.pi * ‖R k‖) ^ 2
        ≤ 8 * Real.pi ^ 2 * (Work.Diff.STE.wt k * ‖Q k‖ ^ 2 + ‖R k‖ ^ 2) := by
      have e1 : 2 * (2 * Real.pi * ‖((((k i : ℤ)) : ℂ))‖ * ‖Q k‖) ^ 2
          = 8 * Real.pi ^ 2 * (‖((((k i : ℤ)) : ℂ))‖ ^ 2 * ‖Q k‖ ^ 2) := by ring
      have e2 : 2 * (2 * Real.pi * ‖R k‖) ^ 2 = 8 * Real.pi ^ 2 * ‖R k‖ ^ 2 := by ring
      rw [e1, e2]
      have h3 : ‖((((k i : ℤ)) : ℂ))‖ ^ 2 * ‖Q k‖ ^ 2 ≤ Work.Diff.STE.wt k * ‖Q k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hki2 k) (sq_nonneg _)
      nlinarith [h3]
    rw [hsplit k]
    have hsub : ‖(2 * Real.pi * Complex.I * (((k i : ℤ)) : ℂ)) * Q k
          - (2 * Real.pi * Complex.I) * R k‖
        ≤ 2 * Real.pi * ‖((((k i : ℤ)) : ℂ))‖ * ‖Q k‖ + 2 * Real.pi * ‖R k‖ :=
      (norm_sub_le _ _).trans (le_of_eq (by rw [hA, hB]))
    have hstep : ‖(2 * Real.pi * Complex.I * (((k i : ℤ)) : ℂ)) * Q k
          - (2 * Real.pi * Complex.I) * R k‖ ^ 2
        ≤ 2 * (2 * Real.pi * ‖((((k i : ℤ)) : ℂ))‖ * ‖Q k‖) ^ 2
          + 2 * (2 * Real.pi * ‖R k‖) ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) hsub 2).trans (sq_add_le_two _ _)
    calc (Work.Diff.STE.wt k) ^ s
          * ‖(2 * Real.pi * Complex.I * (((k i : ℤ)) : ℂ)) * Q k
              - (2 * Real.pi * Complex.I) * R k‖ ^ 2
        ≤ (Work.Diff.STE.wt k) ^ s * (2 * (2 * Real.pi * ‖((((k i : ℤ)) : ℂ))‖ * ‖Q k‖) ^ 2
            + 2 * (2 * Real.pi * ‖R k‖) ^ 2) :=
          mul_le_mul_of_nonneg_left hstep (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _)
      _ ≤ (Work.Diff.STE.wt k) ^ s
            * (8 * Real.pi ^ 2 * (Work.Diff.STE.wt k * ‖Q k‖ ^ 2 + ‖R k‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hbr (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _)
      _ = 8 * Real.pi ^ 2 * ((Work.Diff.STE.wt k) ^ (s + 1) * ‖Q k‖ ^ 2
            + (Work.Diff.STE.wt k) ^ s * ‖R k‖ ^ 2) := by
          rw [pow_succ]
          ring
  have hQ1 : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (s + 1) * ‖Q k‖ ^ 2)
      ∧ Work.Diff.STE.CSq (s + 1) Q ≤ C1 * Work.Diff.STE.CSq s c := hC1 ε hε hε1 c hc
  have hR1 : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (s + 1) * ‖R k‖ ^ 2)
      ∧ Work.Diff.STE.CSq (s + 1) R ≤ C2 * Work.Diff.STE.CSq s c := hC2 ε hε hε1 c hc
  have hRs : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖R k‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _) (sq_nonneg _))
      (fun k => mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (wt_one_le k) (Nat.le_succ s)) (sq_nonneg _)) hR1.1
  have hRmono : Work.Diff.STE.CSq s R ≤ C2 * Work.Diff.STE.CSq s c :=
    (Summable.tsum_le_tsum
      (fun k => mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (wt_one_le k) (Nat.le_succ s)) (sq_nonneg _)) hRs hR1.1).trans hR1.2
  have hPSumm : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖P k‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) _) (sq_nonneg _))
      hnormP ((hQ1.1.add hRs).mul_left (8 * Real.pi ^ 2))
  calc Work.Diff.STE.CSq s P
      = ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s * ‖P k‖ ^ 2 := rfl
    _ ≤ ∑' k : ι → ℤ, 8 * Real.pi ^ 2 * ((Work.Diff.STE.wt k) ^ (s + 1) * ‖Q k‖ ^ 2
          + (Work.Diff.STE.wt k) ^ s * ‖R k‖ ^ 2) :=
        Summable.tsum_le_tsum hnormP hPSumm ((hQ1.1.add hRs).mul_left _)
    _ = 8 * Real.pi ^ 2 * ((∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ (s + 1) * ‖Q k‖ ^ 2)
          + ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s * ‖R k‖ ^ 2) := by
        rw [tsum_mul_left, Summable.tsum_add hQ1.1 hRs]
    _ ≤ 8 * Real.pi ^ 2 * (C1 * Work.Diff.STE.CSq s c + C2 * Work.Diff.STE.CSq s c) := by
        refine mul_le_mul_of_nonneg_left (add_le_add hQ1.2 ?_) (by positivity)
        exact hRmono
    _ = (8 * Real.pi ^ 2 * (C1 + C2)) * Work.Diff.STE.CSq s c := by ring

end Work.Diff.STE.B3.SymCalcStep1
