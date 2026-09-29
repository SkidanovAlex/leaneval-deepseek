import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.lemma_9_2
import Submission.Work.TMC16Core.Basic.lemma_9_2_win
import Submission.Work.TMC16Core.Basic.pd_upper
import Submission.Work.TMC16Core.Core.windows
import Submission.Work.TMC16Core.Core.setup

/-!
# The `A`-window from the singularity of `0` (AJ Lemma 9.2)

The singularity of `0` at rate `L/2` forces the continuants on the interval
`[-(13/16)K, -(3/16)K]` to be exponentially small with rate `29L/32 + ε₁`: exactly the input
`hA` of the non-generation step.  The constant `3/16` is `δ` in AJ Lemma 9.2 (the deficit is
`(L/2)·(3/16) = 3L/32`, comfortably below the `9L/32` needed for the final rate `23L/32`).
-/

noncomputable section

namespace Work.TMC16Core.Core

open Work.TMC16Core

/-- A crude a-priori bound for the continuants, valid at every scale: with
`C = ‖E‖ + 2|λ| + 2 ≥ 1`, `‖P_n(x)‖ ≤ C^n`. -/
theorem pd_le_geom (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    ‖pd α lam x E (n + 1)‖ ≤ (‖E‖ + 2 * |lam| + 2) ^ n := by
  set C : ℝ := ‖E‖ + 2 * |lam| + 2 with hC
  have hC2 : 2 ≤ C := by
    rw [hC]; have h1 := norm_nonneg E; have h2 := abs_nonneg lam; linarith
  have hpot : ∀ (φ : ℝ) (j : ℤ), ‖(((amoPot α lam φ j : ℝ)) : ℂ)‖ ≤ 2 * |lam| := by
    intro φ j
    rw [Complex.norm_real, Real.norm_eq_abs, amoPot, abs_mul, abs_mul]
    have h2 : |(2:ℝ)| = 2 := abs_of_pos (by norm_num)
    rw [h2]
    nlinarith [Real.abs_cos_le_one (2 * Real.pi * (φ + (j : ℝ) * α)), abs_nonneg lam]
  have key : ∀ n : ℕ, ‖pd α lam x E (n + 1)‖ ≤ C ^ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n with
      | 0 => simp [pd]
      | 1 =>
        have h2 : pd α lam x E (1 + 1) = E - (((amoPot α lam x ((0:ℕ):ℤ) : ℝ)) : ℂ) := by
          rw [show (1:ℕ) + 1 = (0:ℕ) + 2 from rfl]; simp [pd]
        rw [h2, pow_one]
        calc ‖E - (((amoPot α lam x ((0:ℕ):ℤ) : ℝ)) : ℂ)‖
            ≤ ‖E‖ + ‖(((amoPot α lam x ((0:ℕ):ℤ) : ℝ)) : ℂ)‖ := norm_sub_le _ _
          _ ≤ ‖E‖ + 2 * |lam| := by have h := hpot x ((0:ℕ):ℤ); linarith
          _ ≤ C := by rw [hC]; linarith
      | k + 2 =>
        have h1 := ih (k + 1) (by omega)
        have h0 := ih k (by omega)
        have hrec : pd α lam x E ((k + 2) + 1) =
            (E - (((amoPot α lam x ((k + 1 : ℕ) : ℤ) : ℝ)) : ℂ)) * pd α lam x E (k + 2)
              - pd α lam x E (k + 1) := by
          rw [show (k + 2) + 1 = (k + 1) + 2 from by omega, pd]
        rw [hrec]
        have hstep : ‖(E - (((amoPot α lam x ((k + 1 : ℕ) : ℤ) : ℝ)) : ℂ)) * pd α lam x E (k + 2)
              - pd α lam x E (k + 1)‖
            ≤ (‖E‖ + 2 * |lam|) * C ^ (k + 1) + C ^ k := by
          refine le_trans (norm_sub_le _ _) ?_
          have hb : ‖E - (((amoPot α lam x ((k + 1 : ℕ) : ℤ) : ℝ)) : ℂ)‖ ≤ ‖E‖ + 2 * |lam| :=
            le_trans (norm_sub_le _ _) (by linarith [hpot x ((k + 1 : ℕ) : ℤ)])
          have hmul : ‖(E - (((amoPot α lam x ((k + 1 : ℕ) : ℤ) : ℝ)) : ℂ)) * pd α lam x E (k + 2)‖
              ≤ (‖E‖ + 2 * |lam|) * C ^ (k + 1) := by
            rw [norm_mul]
            exact mul_le_mul hb h1 (norm_nonneg _) (by positivity)
          linarith
        refine le_trans hstep ?_
        have hCnn : (0:ℝ) ≤ C ^ k := by positivity
        have hbase : (‖E‖ + 2 * |lam|) * C + 1 ≤ C * C := by
          have hE0 := norm_nonneg E; have hl0 := abs_nonneg lam
          rw [hC]; nlinarith
        have hmul := mul_le_mul_of_nonneg_right hbase hCnn
        calc (‖E‖ + 2 * |lam|) * C ^ (k + 1) + C ^ k
            = ((‖E‖ + 2 * |lam|) * C + 1) * C ^ k := by ring
          _ ≤ (C * C) * C ^ k := hmul
          _ = C ^ (k + 2) := by ring
  exact key n

/-- The locally uniform bound for the continuants, valid at *every* scale (the form required
by AJ Lemma 9.2, which needs it for all `n ≤ k`). -/
theorem pd_bound_all (h4 : Work.TMC16Core.P_LEBasics) (h7 : Work.TMC16Core.P_BJ)
    {α b₀ lam : ℝ} (hα : Irrational α) (hb₀ : 0 ≤ b₀)
    (hlam : Real.exp (16 * b₀ / 9) < lam) {E : ℝ} (hE : E ∈ amoSpec α lam) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε ≤ ε₁ ∧ ∀ n : ℕ, ∀ ζ : ℝ,
      ‖pd α lam ζ (E : ℂ) (n + 1)‖ ≤ Real.exp ((n : ℝ) * (Real.log lam + ε₁)) := by
  have hlam1 : 1 < lam := Work.TMC16Core.Core.one_lt_lam hb₀ hlam
  have hlogpos : 0 < Real.log lam := Real.log_pos hlam1
  obtain ⟨n₀, hn₀⟩ := Work.TMC16Core.Basic.pd_upper h4 hα (E : ℂ) ε hε
  set C : ℝ := ‖((E:ℂ))‖ + 2 * |lam| + 2 with hC
  have hC1 : 1 ≤ C := by
    rw [hC]; have h1 := norm_nonneg (E:ℂ); have h2 := abs_nonneg lam; linarith
  set D : ℝ := max 0 (Real.log C) with hD
  have hD0 : 0 ≤ D := le_max_left _ _
  have hCD : Real.log C ≤ D := le_max_right _ _
  refine ⟨ε + D + 1, by positivity, by linarith, ?_⟩
  intro n ζ
  by_cases hn : n ≤ n₀
  · have hgeom : ‖pd α lam ζ (E : ℂ) (n + 1)‖ ≤ C ^ n := by
      have h := pd_le_geom α lam (E : ℂ) n ζ
      rw [← hC] at h
      exact h
    have hkey : C ^ n ≤ Real.exp ((n : ℝ) * (Real.log lam + (ε + D + 1))) := by
      have hClog : Real.log C ≤ Real.log lam + (ε + D + 1) := by linarith
      rw [← Real.exp_log (x := C) (by linarith), ← Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hClog (Nat.cast_nonneg n))
    exact le_trans hgeom hkey
  · push Not at hn
    refine le_trans (hn₀ n hn.le ζ) ?_
    apply Real.exp_le_exp.mpr
    have hεε₁ : ε ≤ ε + D + 1 := by linarith
    have hL : lyap α lam (E : ℂ) = Real.log lam := Work.TMC16Core.Core.lyap_eq_log h7 hα hb₀ hlam hE
    rw [hL]
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)

/-- **The `A`-window from the singularity of `0`.**  If `0` is `(L/2, K)`-singular and the
continuants obey the uniform bound with slack `ε₁`, then every `x ∈ I₁` has
`‖P_K(θ+xα)‖ ≤ exp((K+1)(L - 3L/32 + ε₁))`. -/
theorem Ablock_of_sing {α lam : ℝ} {E : ℂ} {θ L ε₁ : ℝ} {K : ℕ}
    (hL : 0 < L) (hε₁ : 0 < ε₁) (hK : 240 ≤ K)
    (hbd : ∀ n : ℕ, n ≤ K → ∀ ζ : ℝ,
      ‖pd α lam ζ E (n + 1)‖ ≤ Real.exp ((n : ℝ) * (L + ε₁)))
    (hs : IsSingular α lam θ E (L - L / 2) K 0) :
    ∀ x ∈ I1set K,
      ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ ≤
        Real.exp (((K : ℝ) + 1) * (L - (L / 2) * (3 / 16) + ε₁)) := by
  intro x hx
  have hsub := I1set_subset_A2blk hK hx
  simp only [A2blk, Finset.mem_Icc] at hsub
  obtain ⟨h1, h2⟩ := hsub
  have hb1316 : ((b1316 K : ℤ) : ℝ) ≤ (13 : ℝ) * (K : ℝ) / 16 := Int.floor_le _
  have hb316 : (3 : ℝ) * (K : ℝ) / 16 ≤ ((b316 K : ℤ) : ℝ) := Int.le_ceil _
  have hx1 : ((0:ℤ) : ℝ) - (1 - 3 / 16) * (K : ℝ) ≤ (x : ℝ) := by
    have hx1a : ((x : ℤ) : ℝ) ≥ -((b1316 K : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at hx1a ⊢
    nlinarith
  have hx2 : (x : ℝ) ≤ ((0:ℤ) : ℝ) - 3 / 16 * (K : ℝ) := by
    have hx2a : ((x : ℤ) : ℝ) ≤ -((b316 K : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at hx2a ⊢
    nlinarith
  have hk40 : 40 ≤ K := by omega
  have hkδ : 1 ≤ (K : ℝ) * (3 / 16 - 1 / 40) := by
    have hK' : (240 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    nlinarith
  have hL2 : 0 < L / 2 := by linarith
  have hmem := Work.TMC16Core.Basic.lemma_9_2 (α := α) (lam := lam) (E := E) (θ := θ)
    (L := L) (ε := L / 2) (ε₁ := ε₁) (δ := 3 / 16) (k := K) (y := 0)
    hL.le (by linarith) hL2 hε₁ (by norm_num) (by norm_num) hk40 hkδ hbd hs x hx1 hx2
  have heq : θ + ((x : ℝ) + (((K : ℝ) - 1) / 2)) * α - (((K : ℝ) - 1) / 2) * α
      = θ + (x : ℝ) * α := by ring
  simpa only [AkSet, Set.mem_ofPred_eq, heq] using hmem

end Work.TMC16Core.Core

namespace Work.TMC16Core.Core

/-- **The `A`-window bound for an arbitrary sub-window of `A2blk`** (generalized
`Ablock_of_sing`): the singularity of `0` at rate `m` forces the continuants on any
`I₁ ⊆ A2blk K` below `e^{(K+1)(L - m·(3/16) + ε₁)}`.  The bound on the continuants is only
needed for the scales `n ≥ K/40` actually used (that is the weakened hypothesis
`lemma_9_2_win` was proved for), which is what allows the slack `ε₁` to be small. -/
theorem Ablock_of_sing_gen {α lam : ℝ} {E : ℂ} {θ L ε₁ m : ℝ} {K : ℕ} {I₁ : Finset ℤ}
    (hL : 0 < L) (hε₁ : 0 < ε₁) (hm : 0 < m) (hmL : m < L) (hK : 240 ≤ K)
    (hbd : ∀ n : ℕ, K / 40 ≤ n → n ≤ K → ∀ ζ : ℝ,
      ‖pd α lam ζ E (n + 1)‖ ≤ Real.exp ((n : ℝ) * (L + ε₁)))
    (hsub : I₁ ⊆ A2blk K)
    (hs : IsSingular α lam θ E m K 0) :
    ∀ x ∈ I₁,
      ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ ≤
        Real.exp (((K : ℝ) + 1) * (L - (3 / 16) * (L - m) + ε₁)) := by
  intro x hx
  have hsub' := hsub hx
  simp only [A2blk, Finset.mem_Icc] at hsub'
  obtain ⟨h1, h2⟩ := hsub'
  have hb1316 : ((b1316 K : ℤ) : ℝ) ≤ (13 : ℝ) * (K : ℝ) / 16 := Int.floor_le _
  have hb316 : (3 : ℝ) * (K : ℝ) / 16 ≤ ((b316 K : ℤ) : ℝ) := Int.le_ceil _
  have hx1 : ((0 : ℤ) : ℝ) - (1 - 3 / 16) * (K : ℝ) ≤ (x : ℝ) := by
    have hx1a : ((x : ℤ) : ℝ) ≥ -((b1316 K : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at hx1a ⊢
    nlinarith
  have hx2 : (x : ℝ) ≤ ((0 : ℤ) : ℝ) - 3 / 16 * (K : ℝ) := by
    have hx2a : ((x : ℤ) : ℝ) ≤ -((b316 K : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at hx2a ⊢
    nlinarith
  have hk40 : 40 ≤ K := by omega
  have hkδ : 1 ≤ (K : ℝ) * (3 / 16 - 1 / 40) := by
    have hK' : (240 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    nlinarith
  have hεL : L - m ≤ L := by linarith
  have hεpos : 0 < L - m := by linarith
  have hs' : IsSingular α lam θ E (L - (L - m)) K 0 := by
    have h : L - (L - m) = m := by ring
    rwa [h]
  have hmem := Work.TMC16Core.Basic.lemma_9_2_win (α := α) (lam := lam) (E := E) (θ := θ)
    (L := L) (ε := L - m) (ε₁ := ε₁) (δ := 3 / 16) (k := K) (y := 0)
    hL.le hεL hεpos hε₁ (by norm_num) (by norm_num) hk40 hkδ hbd hs' x hx1 hx2
  have heq : θ + ((x : ℝ) + (((K : ℝ) - 1) / 2)) * α - (((K : ℝ) - 1) / 2) * α
      = θ + (x : ℝ) * α := by ring
  have hrate : L - (L - m) * (3 / 16) + ε₁ = L - (3 / 16) * (L - m) + ε₁ := by ring
  simpa only [AkSet, Set.mem_ofPred_eq, heq, hrate] using hmem

end Work.TMC16Core.Core
