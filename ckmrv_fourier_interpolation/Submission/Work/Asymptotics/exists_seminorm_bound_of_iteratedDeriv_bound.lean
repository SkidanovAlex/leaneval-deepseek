import Mathlib
import Submission.Work.Asymptotics.TailIntegral
import Submission.Work.Asymptotics.layerTrunc_seminorm

noncomputable section

open MeasureTheory Filter Topology
open scoped Topology ContDiff

namespace Work.Asymptotics

/-- **Chain rule / composition estimate for the regularised layer.**  If `F` is `l` times
differentiable on `(-1,∞)` and its iterated derivatives of order `m ≤ l` satisfy
`‖∂^m F x‖ ≤ K e^{-πx}` for all `x ≥ 0`, then `|r|^k · ∂_r^l ((2 - 2cos(πr²))·F(r²))` is bounded by
a constant depending only on `k` and `l`, times `K`; the constant must not depend on `F` or `K`
(they are quantified inside the existential), and `K ≥ 0` is needed to pull out `K`.
A proof can follow the chain-rule block of `Work.Asymptotics.layerTrunc_seminorm` verbatim, with the
bound `‖∂^{j}(tailIntegral h) x‖ ≤ (C S^N)π^j tailDecay M j e^{-πx}` replaced by `K e^{-πx}`. -/
theorem exists_seminorm_bound_of_iteratedDeriv_bound (k l : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (F : ℝ → ℂ) (K : ℝ), 0 ≤ K →
      ContDiffOn ℝ (l : WithTop ℕ∞) F (Set.Ioi (-1)) →
      (∀ m : ℕ, m ≤ l → ∀ x : ℝ, 0 ≤ x →
        ‖iteratedDeriv m F x‖ ≤ K * Real.exp (-(Real.pi * x))) →
      ∀ r : ℝ, (|r| ^ k) * ‖iteratedDeriv l
        (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * F (s ^ 2)) r‖ ≤ c * K := by
  obtain ⟨W, hW0, hW⟩ := exists_bound_abs_pow_mul_exp_neg_sq k l
  refine ⟨(l.factorial : ℝ) * (4 * (2 * Real.pi) ^ l) * W, by positivity, ?_⟩
  intro F K hK hFdiff hFbound r
  -- the regularising factor `x ↦ 2 - 2cos(πx)` is smooth
  have hcont_cos : ContDiffOn ℝ (l : ℕ∞ω)
      (fun x : ℝ => (2 - 2 * Real.cos (Real.pi * x) : ℂ)) (Set.Ioi (-1)) := by
    have h1 : ContDiff ℝ (l : ℕ∞ω) (fun x : ℝ => (2 - 2 * Real.cos (Real.pi * x))) := by
      fun_prop
    have h2 := Complex.ofRealCLM.contDiff.comp h1
    refine h2.contDiffOn.congr (fun x _ => ?_)
    show (2 - 2 * (Real.cos (Real.pi * x) : ℂ)) = ((2 - 2 * Real.cos (Real.pi * x) : ℝ) : ℂ)
    push_cast
    ring
  have hfcont : ContDiffOn ℝ (l : ℕ∞ω) (fun r : ℝ => r ^ 2) Set.univ :=
    ((contDiff_id (𝕜 := ℝ)).pow 2).contDiffOn
  -- the product bound for the iterated derivatives of `λ ↦ (2 - 2cos (πλ)) * F λ`
  have hbnd : ∀ i ≤ l, ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv i (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * F y) x‖
        ≤ K * Real.exp (-(Real.pi * x)) * (4 * (2 * Real.pi) ^ l) := by
    intro i hi x hx
    have hxmem : x ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; linarith
    have hmul := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (s := Set.Ioi (-1))
      (f := fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ)) (g := F) (N := (l : ℕ∞ω))
      hcont_cos hFdiff (uniqueDiffOn_Ioi (-1)) hxmem
      (show (i : ℕ∞ω) ≤ (l : ℕ∞ω) from by exact_mod_cast hi)
    have hL : ‖iteratedFDerivWithin ℝ i
          (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * F y) (Set.Ioi (-1)) x‖
        = ‖iteratedDeriv i (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * F y) x‖ :=
      norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hxmem i _
    rw [hL] at hmul
    have hstep : ∀ j ∈ Finset.range (i + 1),
        (i.choose j : ℝ) *
          ‖iteratedFDerivWithin ℝ j (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ))
            (Set.Ioi (-1)) x‖ *
          ‖iteratedFDerivWithin ℝ (i - j) F (Set.Ioi (-1)) x‖
        ≤ (i.choose j : ℝ) * (4 * Real.pi ^ j) * (K * Real.exp (-(Real.pi * x))) := by
      intro j hj
      have hc : ‖iteratedFDerivWithin ℝ j
            (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ)) (Set.Ioi (-1)) x‖
          ≤ 4 * Real.pi ^ j := by
        rw [norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hxmem j]
        exact norm_iteratedDeriv_two_sub_two_cos j x
      have ht : ‖iteratedFDerivWithin ℝ (i - j) F (Set.Ioi (-1)) x‖
          ≤ K * Real.exp (-(Real.pi * x)) := by
        rw [norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hxmem (i - j)]
        exact hFbound (i - j) (le_trans (Nat.sub_le i j) hi) x hx
      exact mul_le_mul (mul_le_mul_of_nonneg_left hc (by positivity)) ht
        (by positivity) (by positivity)
    have hsum2 : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ j))
        ≤ 4 * (2 * Real.pi) ^ l := by
      have hbin : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) = 2 ^ i := by
        have hh := add_pow (1 : ℝ) 1 i
        rw [one_add_one_eq_two] at hh
        rw [hh]
        apply Finset.sum_congr rfl
        intro j hj
        rw [one_pow, one_pow]
        ring
      calc (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ j))
          ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ l) := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            have hjle : j ≤ l := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hi
            have hpi : Real.pi ^ j ≤ Real.pi ^ l :=
              pow_le_pow_right₀ (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi) hjle
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpi (by norm_num))
              (by positivity)
        _ = (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) * (4 * Real.pi ^ l) := by
            rw [Finset.sum_mul]
        _ = 2 ^ i * (4 * Real.pi ^ l) := by rw [hbin]
        _ ≤ 4 * (2 * Real.pi) ^ l := by
            have h2 : (2 : ℝ) ^ i ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hi
            have h3 : (2 : ℝ) ^ i * (4 * Real.pi ^ l) ≤ 2 ^ l * (4 * Real.pi ^ l) :=
              mul_le_mul_of_nonneg_right h2 (by positivity)
            refine h3.trans_eq ?_
            rw [mul_pow]
            ring
    calc ‖iteratedDeriv i (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * F y) x‖
        ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
            ‖iteratedFDerivWithin ℝ j (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ))
              (Set.Ioi (-1)) x‖ *
            ‖iteratedFDerivWithin ℝ (i - j) F (Set.Ioi (-1)) x‖ := hmul
      _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ j) *
            (K * Real.exp (-(Real.pi * x))) := Finset.sum_le_sum hstep
      _ = (K * Real.exp (-(Real.pi * x))) *
            (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ j)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ ≤ (K * Real.exp (-(Real.pi * x))) * (4 * (2 * Real.pi) ^ l) :=
            mul_le_mul_of_nonneg_left hsum2 (by positivity)
      _ = K * Real.exp (-(Real.pi * x)) * (4 * (2 * Real.pi) ^ l) := by ring
  have hCbound : ∀ i, i ≤ l → ‖iteratedFDerivWithin ℝ i
        (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * F y)
        (Set.Ioi (-1)) (r ^ 2)‖ ≤ K * Real.exp (-(Real.pi * r ^ 2)) * (4 * (2 * Real.pi) ^ l) := by
    intro i hi
    have hr2 : r ^ 2 ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; nlinarith [sq_nonneg r]
    rw [norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hr2]
    exact hbnd i hi (r ^ 2) (sq_nonneg r)
  have hDbound : ∀ i, 1 ≤ i → i ≤ l →
      ‖iteratedFDerivWithin ℝ i (fun r : ℝ => r ^ 2) Set.univ r‖ ≤ (2 * |r| + 2) ^ i := by
    intro i hi _
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact norm_iteratedDeriv_sq_le hi r
  have hcomp := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ)
    (g := fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * F y)
    (f := fun r : ℝ => r ^ 2) (n := l) (s := Set.univ) (t := Set.Ioi (-1))
    (x := r) (N := (l : ℕ∞ω)) (hcont_cos.mul hFdiff) hfcont le_rfl
    (uniqueDiffOn_Ioi (-1)) uniqueDiffOn_univ
    (by intro x _; rw [Set.mem_Ioi]; nlinarith [sq_nonneg x]) (Set.mem_univ r) hCbound hDbound
  have hcomp' : ‖iteratedDeriv l
        (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * F (s ^ 2)) r‖
      ≤ (l.factorial : ℝ) * (K * Real.exp (-(Real.pi * r ^ 2)) * (4 * (2 * Real.pi) ^ l))
        * (2 * |r| + 2) ^ l := by
    have heq : (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * F (s ^ 2))
        = (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * F y)
          ∘ (fun r : ℝ => r ^ 2) := rfl
    rw [heq, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedFDerivWithin_univ]
    exact hcomp
  calc (|r| ^ k) * ‖iteratedDeriv l
        (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * F (s ^ 2)) r‖
      ≤ |r| ^ k * ((l.factorial : ℝ) * (K * Real.exp (-(Real.pi * r ^ 2))
          * (4 * (2 * Real.pi) ^ l)) * (2 * |r| + 2) ^ l) :=
        mul_le_mul_of_nonneg_left hcomp' (by positivity)
    _ = (l.factorial : ℝ) * (4 * (2 * Real.pi) ^ l) * K
          * (|r| ^ k * (2 * |r| + 2) ^ l * Real.exp (-(Real.pi * r ^ 2))) := by ring
    _ ≤ (l.factorial : ℝ) * (4 * (2 * Real.pi) ^ l) * K * W := by
        have h1 : (0 : ℝ) ≤ (l.factorial : ℝ) * (4 * (2 * Real.pi) ^ l) * K := by positivity
        exact mul_le_mul_of_nonneg_left (hW r) h1
    _ = ((l.factorial : ℝ) * (4 * (2 * Real.pi) ^ l) * W) * K := by ring

end Work.Asymptotics
