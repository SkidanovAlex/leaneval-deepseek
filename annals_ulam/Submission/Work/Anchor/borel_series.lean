import Mathlib

namespace Work.Anchor

open Finset Filter Function
open scoped Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## A smooth bump function and bounds on its derivatives -/

/-- The standard smooth bump: equal to `1` on `[-1,1]` and supported in the ball of radius `2`. -/
def bumpC : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The bump as a plain function. -/
def bumpFun : ℝ → ℝ := bumpC

lemma bumpFun_contDiff : ContDiff ℝ (⊤ : ℕ∞) bumpFun := bumpC.contDiff

lemma bumpFun_hasCompactSupport : HasCompactSupport bumpFun := bumpC.hasCompactSupport

lemma bumpFun_one (y : ℝ) (hy : |y| ≤ 1) : bumpFun y = 1 :=
  ContDiffBump.one_of_mem_closedBall (f := bumpC) (by
    rw [Metric.mem_closedBall]
    simpa [bumpC, Real.dist_eq] using hy)

lemma bumpFun_zero (y : ℝ) (hy : 2 ≤ |y|) : bumpFun y = 0 :=
  ContDiffBump.zero_of_le_dist (f := bumpC) (by
    rw [Real.dist_eq]
    simpa [bumpC] using hy)

/-- The order `k : ℕ` is below the smooth order `⊤ : ℕ∞` (seen in `WithTop ℕ∞`). -/
lemma natCast_le_topE (k : ℕ) : (k : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
  WithTop.coe_le_coe.mpr (le_top : (k : ℕ∞) ≤ ⊤)

lemma natCast_lt_topE (k : ℕ) : (k : WithTop ℕ∞) < ↑(⊤ : ℕ∞) :=
  WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top k)

lemma iteratedDeriv_zero_fun (k : ℕ) (z : ℝ) : iteratedDeriv k (0 : ℝ → ℝ) z = 0 := by
  rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
  split_ifs <;> rfl

/-- A `C^∞` function with compact support has bounded iterated derivatives. -/
lemma exists_bound_iteratedDeriv_hasCompactSupport
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |iteratedDeriv m f x| ≤ C := by
  have hcont : Continuous (iteratedDeriv m f) := hf.continuous_iteratedDeriv m (natCast_le_topE m)
  obtain ⟨C₀, hC₀⟩ := hc.isCompact.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C₀ 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · have h := hC₀ x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · have h0 : f =ᶠ[𝓝 x] 0 := by
      have hmem : (tsupport f)ᶜ ∈ 𝓝 x := (isClosed_tsupport f).isOpen_compl.mem_nhds hx
      filter_upwards [hmem] with y hy
      by_contra hfy
      exact hy (subset_closure (by simpa [Function.mem_support] using hfy))
    have hzero : iteratedDeriv m f x = 0 := by
      rw [Filter.EventuallyEq.iteratedDeriv_eq m h0]
      exact iteratedDeriv_zero_fun m x
    rw [hzero, abs_zero]
    exact le_max_right _ _

/-! ## Derivative bounds for `z ↦ z^n * φ z` and its rescalings -/

/-- Pointwise bound for the iterated derivatives of `z ↦ z^n * φ z`, where `φ` is a smooth
function with `|iteratedDeriv j φ| ≤ C j` and vanishing for `|z| ≥ 2`. -/
lemma pow_mul_self_bound {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {C : ℕ → ℝ}
    (hC : ∀ j y, |iteratedDeriv j φ y| ≤ C j)
    (hz : ∀ y : ℝ, 2 ≤ |y| → φ y = 0) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (z : ℝ) :
    |iteratedDeriv k (fun z : ℝ => z ^ n * φ z) z| ≤
      (2 : ℝ) ^ n * (n : ℝ) ^ k *
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C (k - i) := by
  have hCnn : ∀ j, 0 ≤ C j := fun j => le_trans (abs_nonneg _) (hC j 0)
  by_cases hz2 : |z| ≤ 2
  · have hφk : ContDiffAt ℝ (k : ℕ∞) φ z := (hφ.of_le (natCast_le_topE k)).contDiffAt
    have hpk : ContDiffAt ℝ (k : ℕ∞) (fun z : ℝ => z ^ n) z :=
      ((contDiff_id (𝕜 := ℝ) (n := (k : ℕ∞))).pow n).contDiffAt
    rw [show (fun z : ℝ => z ^ n * φ z) = (fun z : ℝ => z ^ n) * φ from rfl,
      iteratedDeriv_mul hpk hφk]
    calc |∑ i ∈ Finset.range (k + 1),
            (k.choose i : ℝ) * iteratedDeriv i (fun z : ℝ => z ^ n) z *
              iteratedDeriv (k - i) φ z|
        ≤ ∑ i ∈ Finset.range (k + 1),
            (k.choose i : ℝ) * (n.descFactorial i : ℝ) * (2 : ℝ) ^ (n - i) * C (k - i) := by
          refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
          intro i hi
          have h1 : |iteratedDeriv i (fun z : ℝ => z ^ n) z| =
              (n.descFactorial i : ℝ) * |z| ^ (n - i) := by
            rw [iteratedDeriv_pow, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow]
          have hc0 : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
          have hX : |iteratedDeriv i (fun z : ℝ => z ^ n) z| ≤
              (n.descFactorial i : ℝ) * (2 : ℝ) ^ (n - i) := by
            rw [h1]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg z) hz2 _)
              (Nat.cast_nonneg _)
          have hY : |iteratedDeriv (k - i) φ z| ≤ C (k - i) := hC (k - i) z
          calc |(k.choose i : ℝ) * iteratedDeriv i (fun z : ℝ => z ^ n) z *
                  iteratedDeriv (k - i) φ z|
              = (k.choose i : ℝ) * |iteratedDeriv i (fun z : ℝ => z ^ n) z| *
                  |iteratedDeriv (k - i) φ z| := by
                simp only [abs_mul, abs_of_nonneg hc0]
            _ ≤ (k.choose i : ℝ) * ((n.descFactorial i : ℝ) * (2 : ℝ) ^ (n - i)) *
                  C (k - i) := by
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_left hX hc0
                · exact hY
                · exact abs_nonneg _
                · exact mul_nonneg hc0 (mul_nonneg (Nat.cast_nonneg _) (by positivity))
            _ = (k.choose i : ℝ) * (n.descFactorial i : ℝ) * (2 : ℝ) ^ (n - i) *
                  C (k - i) := by ring
      _ ≤ (2 : ℝ) ^ n * (n : ℝ) ^ k *
            ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C (k - i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i hi
          have hi_le_k : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have h1 : (n.descFactorial i : ℝ) ≤ (n : ℝ) ^ k := by
            calc (n.descFactorial i : ℝ) ≤ (n : ℝ) ^ i := by
                  exact_mod_cast Nat.descFactorial_le_pow n i
              _ ≤ (n : ℝ) ^ k := pow_le_pow_right₀ (by exact_mod_cast hn) hi_le_k
          have h2 : (2 : ℝ) ^ (n - i) ≤ (2 : ℝ) ^ n :=
            pow_le_pow_right₀ (by norm_num) (Nat.sub_le n i)
          have hci : 0 ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
          have hCi : 0 ≤ C (k - i) := hCnn _
          have hstep : (n.descFactorial i : ℝ) * (2 : ℝ) ^ (n - i) ≤
              (n : ℝ) ^ k * (2 : ℝ) ^ n :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
          calc (k.choose i : ℝ) * (n.descFactorial i : ℝ) * (2 : ℝ) ^ (n - i) * C (k - i)
              = ((k.choose i : ℝ) * C (k - i)) *
                  ((n.descFactorial i : ℝ) * (2 : ℝ) ^ (n - i)) := by ring
            _ ≤ ((k.choose i : ℝ) * C (k - i)) * ((n : ℝ) ^ k * (2 : ℝ) ^ n) :=
                mul_le_mul_of_nonneg_left hstep (mul_nonneg hci hCi)
            _ = (2 : ℝ) ^ n * (n : ℝ) ^ k * ((k.choose i : ℝ) * C (k - i)) := by ring
  · rw [not_le] at hz2
    have h0 : (fun z : ℝ => z ^ n * φ z) =ᶠ[𝓝 z] 0 := by
      have hφ0 : φ =ᶠ[𝓝 z] 0 := by
        have hopen : {y : ℝ | 2 < |y|} ∈ 𝓝 z :=
          IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) hz2
        filter_upwards [hopen] with y hy using hz y (le_of_lt hy)
      filter_upwards [hφ0] with y hy
      simp [hy]
    have hz0 : iteratedDeriv k (fun z : ℝ => z ^ n * φ z) z = 0 := by
      rw [Filter.EventuallyEq.iteratedDeriv_eq k h0]
      exact iteratedDeriv_zero_fun k z
    rw [hz0, abs_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (Nat.cast_nonneg n) k))
      (Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hCnn _)))

/-- The rescaled version: derivative bound for `x ↦ x^n * φ (a x)`. -/
lemma pow_mul_comp_bound {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {C : ℕ → ℝ}
    (hC : ∀ j y, |iteratedDeriv j φ y| ≤ C j) (hz : ∀ y : ℝ, 2 ≤ |y| → φ y = 0)
    {a : ℝ} (ha : 1 ≤ a) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (y : ℝ) :
    |iteratedDeriv k (fun x : ℝ => x ^ n * φ (a * x)) y| ≤
      (a ^ k / a ^ n) * (2 : ℝ) ^ n * (n : ℝ) ^ k *
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C (k - i) := by
  have ha_pos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hpowk_pos : (0 : ℝ) < a ^ k := pow_pos ha_pos k
  have hpown_pos : (0 : ℝ) < a ^ n := pow_pos ha_pos n
  have hGcd : ContDiff ℝ (k : ℕ∞) (fun z : ℝ => z ^ n * φ z) :=
    ((contDiff_id (𝕜 := ℝ) (n := (k : ℕ∞))).pow n).mul (hφ.of_le (natCast_le_topE k))
  have hscale : (fun x : ℝ => x ^ n * φ (a * x)) =
      fun x : ℝ => (a ^ n)⁻¹ * ((fun z : ℝ => z ^ n * φ z) (a * x)) := by
    funext x
    show x ^ n * φ (a * x) = (a ^ n)⁻¹ * ((a * x) ^ n * φ (a * x))
    field_simp
    ring
  have hcomp : ContDiffAt ℝ (k : ℕ∞) (fun x : ℝ => (fun z : ℝ => z ^ n * φ z) (a * x)) y :=
    hGcd.contDiffAt.comp y (contDiffAt_const.mul contDiffAt_id)
  have hb := pow_mul_self_bound hφ hC hz hn k (a * y)
  calc |iteratedDeriv k (fun x : ℝ => x ^ n * φ (a * x)) y|
      = |(a ^ n)⁻¹| * |a ^ k * iteratedDeriv k (fun z : ℝ => z ^ n * φ z) (a * y)| := by
        rw [hscale, iteratedDeriv_const_mul _ hcomp,
          congrFun (iteratedDeriv_comp_const_mul hGcd a) y, abs_mul]
    _ = (a ^ k / a ^ n) * |iteratedDeriv k (fun z : ℝ => z ^ n * φ z) (a * y)| := by
        rw [abs_of_nonneg (inv_nonneg.mpr hpown_pos.le), abs_mul,
          abs_of_nonneg hpowk_pos.le]
        ring
    _ ≤ (a ^ k / a ^ n) * ((2 : ℝ) ^ n * (n : ℝ) ^ k *
          ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C (k - i)) :=
        mul_le_mul_of_nonneg_left hb (div_nonneg hpowk_pos.le hpown_pos.le)
    _ = (a ^ k / a ^ n) * (2 : ℝ) ^ n * (n : ℝ) ^ k *
          ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C (k - i) := by ring

/-- `iteratedDeriv` of `x ↦ x^n * φ (a x)` at the origin: the jet is that of `x ↦ x^n`. -/
lemma pow_mul_comp_zero {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ1 : ∀ y : ℝ, |y| ≤ 1 → φ y = 1) {a : ℝ} (ha : 0 < a) (n k : ℕ) :
    iteratedDeriv k (fun x : ℝ => x ^ n * φ (a * x)) 0 =
      if k = n then (n.factorial : ℝ) else 0 := by
  have hS : {x : ℝ | |a * x| ≤ 1} ∈ 𝓝 (0 : ℝ) := by
    have hsub : Metric.ball (0 : ℝ) (1 / (2 * a)) ⊆ {x : ℝ | |a * x| ≤ 1} := by
      intro x hx
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
      have h2a : (0 : ℝ) < 2 * a := by positivity
      rw [lt_div_iff₀ h2a] at hx
      rw [Set.mem_ofPred_eq, abs_mul, abs_of_pos ha]
      nlinarith [hx, abs_nonneg x]
    exact Filter.mem_of_superset
      (Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < 1 / (2 * a))) hsub
  have heq : (fun x : ℝ => x ^ n * φ (a * x)) =ᶠ[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ n) := by
    filter_upwards [hS] with x hx
    rw [hφ1 (a * x) hx, mul_one]
  rw [Filter.EventuallyEq.iteratedDeriv_eq k heq, iteratedDeriv_fun_pow_zero]
  by_cases h : k = n
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    simp

/-! ## The construction -/

/-- A uniform bound for `|iteratedDeriv m bumpFun|`. -/
def Cb (m : ℕ) : ℝ :=
  Classical.choose (exists_bound_iteratedDeriv_hasCompactSupport bumpFun_contDiff
    bumpFun_hasCompactSupport m)

lemma Cb_nonneg (m : ℕ) : 0 ≤ Cb m :=
  (Classical.choose_spec (exists_bound_iteratedDeriv_hasCompactSupport bumpFun_contDiff
    bumpFun_hasCompactSupport m)).1

lemma Cb_bound (m : ℕ) (y : ℝ) : |iteratedDeriv m bumpFun y| ≤ Cb m :=
  (Classical.choose_spec (exists_bound_iteratedDeriv_hasCompactSupport bumpFun_contDiff
    bumpFun_hasCompactSupport m)).2 y

/-- The Leibniz-type combinatorial factor. -/
def Fb (k : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Cb (k - i)

lemma Fb_nonneg (k : ℕ) : 0 ≤ Fb k :=
  Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (Cb_nonneg _)

/-- The auxiliary sum controlling the growth of the cutoff constants. -/
def Gsum (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n + 1), (n : ℝ) ^ k * Fb k

lemma Gsum_nonneg (n : ℕ) : 0 ≤ Gsum n :=
  Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg (Nat.cast_nonneg n) k) (Fb_nonneg k)

lemma le_Gsum {k n : ℕ} (hk : k ≤ n) : (n : ℝ) ^ k * Fb k ≤ Gsum n := by
  refine Finset.single_le_sum (f := fun k => (n : ℝ) ^ k * Fb k) (fun i _ => ?_) ?_
  · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg n) i) (Fb_nonneg i)
  · rw [Finset.mem_range]; omega

/-- The cutoff constant of the `n`-th term. -/
def aa (e : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  max 1 (|e n| * (4 : ℝ) ^ n * 4 * Gsum n / ε)

/-- The `n`-th term of the Borel-type series. -/
def term (e : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun y => (e n / (n.factorial : ℝ)) * (y ^ n * bumpFun (aa e ε n * y))

/-- The uniform bound on the `k`-th derivative of the `n`-th term. -/
def vv (e : ℕ → ℝ) (ε : ℝ) (k n : ℕ) : ℝ :=
  (|e n| / (n.factorial : ℝ)) *
    ((aa e ε n) ^ k / (aa e ε n) ^ n * ((2 : ℝ) ^ n * ((n : ℝ) ^ k * Fb k)))

lemma one_le_aa (e : ℕ → ℝ) (ε : ℝ) (n : ℕ) : 1 ≤ aa e ε n := le_max_left _ _

lemma aa_pos (e : ℕ → ℝ) (ε : ℝ) (n : ℕ) : 0 < aa e ε n :=
  lt_of_lt_of_le zero_lt_one (one_le_aa e ε n)

lemma aa_ge (e : ℕ → ℝ) (ε : ℝ) (n : ℕ) :
    |e n| * (4 : ℝ) ^ n * 4 * Gsum n / ε ≤ aa e ε n := le_max_right _ _

lemma vv_nonneg (e : ℕ → ℝ) (ε : ℝ) (k n : ℕ) : 0 ≤ vv e ε k n := by
  have apos : (0 : ℝ) ≤ aa e ε n := (aa_pos e ε n).le
  rw [vv]
  refine mul_nonneg (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) ?_
  refine mul_nonneg (div_nonneg (pow_nonneg apos k) (pow_nonneg apos n)) ?_
  refine mul_nonneg (pow_nonneg (by norm_num) n) ?_
  exact mul_nonneg (pow_nonneg (Nat.cast_nonneg n) k) (Fb_nonneg k)

lemma term_contDiff (e : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (term e ε n) :=
  ContDiff.mul contDiff_const <|
    (contDiff_id.pow n).mul (bumpFun_contDiff.comp (contDiff_const.mul contDiff_id))

lemma inner_contDiff (e : ℕ → ℝ) (ε : ℝ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => y ^ n * bumpFun (aa e ε n * y)) :=
  (contDiff_id.pow n).mul (bumpFun_contDiff.comp (contDiff_const.mul contDiff_id))

lemma inner_bound (e : ℕ → ℝ) (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (y : ℝ) :
    |iteratedDeriv k (fun y : ℝ => y ^ n * bumpFun (aa e ε n * y)) y| ≤
      (aa e ε n) ^ k / (aa e ε n) ^ n * (2 : ℝ) ^ n * (n : ℝ) ^ k * Fb k :=
  pow_mul_comp_bound bumpFun_contDiff Cb_bound bumpFun_zero (one_le_aa e ε n) hn k y

lemma term_bound (e : ℕ → ℝ) (he : ∀ k : ℕ, k ≤ 2 → e k = 0) (ε : ℝ) (hε : 0 < ε)
    (k n : ℕ) (y : ℝ) : ‖iteratedFDeriv ℝ k (term e ε n) y‖ ≤ vv e ε k n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have he0 : e 0 = 0 := he 0 (by norm_num)
    have hterm : term e ε 0 = 0 := by
      funext y
      simp [term, he0]
    have hvv : vv e ε k 0 = 0 := by
      simp [vv, he0]
    rw [hterm, hvv, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero_fun k y]
    simp
  · have hn1 : 1 ≤ n := hn
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    unfold term
    have hcd : ContDiffAt ℝ (k : ℕ∞)
        (fun y : ℝ => y ^ n * bumpFun (aa e ε n * y)) y :=
      (inner_contDiff e ε n).of_le (natCast_le_topE k) |>.contDiffAt
    have hfac : |((n.factorial : ℕ) : ℝ)| = (n.factorial : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    rw [iteratedDeriv_const_mul _ hcd, abs_mul, abs_div, hfac]
    calc |e n| / ↑n.factorial *
          |iteratedDeriv k (fun y : ℝ => y ^ n * bumpFun (aa e ε n * y)) y|
        ≤ |e n| / ↑n.factorial *
            ((aa e ε n) ^ k / (aa e ε n) ^ n * (2 : ℝ) ^ n * (n : ℝ) ^ k * Fb k) :=
          mul_le_mul_of_nonneg_left (inner_bound e ε hn1 k y)
            (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      _ = vv e ε k n := by rw [vv]; ring

/-- For `k < n` the `k`-th summand is bounded by `ε / (4 * 2^n)`. -/
lemma vv_le (e : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) {k n : ℕ} (hk : k < n) :
    vv e ε k n ≤ ε / ((2 : ℝ) ^ n * 4) := by
  have hkl : k ≤ n := le_of_lt hk
  have haa1 : 1 ≤ aa e ε n := one_le_aa e ε n
  have haapos : 0 < aa e ε n := aa_pos e ε n
  have hA : 0 ≤ |e n| * (2 : ℝ) ^ n * (n : ℝ) ^ k * Fb k :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (by positivity))
      (pow_nonneg (Nat.cast_nonneg n) k)) (Fb_nonneg k)
  have hQ : |e n| * (4 : ℝ) ^ n * 4 * ((n : ℝ) ^ k * Fb k) / ε ≤ (aa e ε n) ^ (n - k) := by
    have h1 : |e n| * (4 : ℝ) ^ n * 4 * ((n : ℝ) ^ k * Fb k) ≤
        |e n| * (4 : ℝ) ^ n * 4 * Gsum n :=
      mul_le_mul_of_nonneg_left (le_Gsum hkl) (by positivity)
    refine (div_le_div_of_nonneg_right h1 hε.le).trans ?_
    exact (aa_ge e ε n).trans (le_self_pow₀ haa1 (by omega))
  have hQeq : (aa e ε n) ^ k / (aa e ε n) ^ n = 1 / (aa e ε n) ^ (n - k) := by
    rw [pow_sub₀ (aa e ε n) (ne_of_gt haapos) hkl, div_eq_mul_inv, one_div, mul_inv, inv_inv]
    ring
  have hvv : vv e ε k n =
      |e n| * (2 : ℝ) ^ n * (n : ℝ) ^ k * Fb k /
        ((n.factorial : ℝ) * (aa e ε n) ^ (n - k)) := by
    rw [vv, hQeq]
    field_simp
  rw [hvv]
  have hstep1 : |e n| * (2 : ℝ) ^ n * (n : ℝ) ^ k * Fb k /
        ((n.factorial : ℝ) * (aa e ε n) ^ (n - k)) ≤
      |e n| * (2 : ℝ) ^ n * (n : ℝ) ^ k * Fb k / (aa e ε n) ^ (n - k) := by
    apply div_le_div_of_nonneg_left hA (pow_pos haapos _)
    have hf1 : (1 : ℝ) ≤ (n.factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
    calc (aa e ε n) ^ (n - k) = 1 * (aa e ε n) ^ (n - k) := by ring
      _ ≤ (n.factorial : ℝ) * (aa e ε n) ^ (n - k) :=
          mul_le_mul_of_nonneg_right hf1 (by positivity)
  refine hstep1.trans ?_
  rw [div_le_iff₀ (pow_pos haapos _)]
  calc |e n| * (2 : ℝ) ^ n * (n : ℝ) ^ k * Fb k
      = ε / ((2 : ℝ) ^ n * 4) *
          (|e n| * (4 : ℝ) ^ n * 4 * ((n : ℝ) ^ k * Fb k) / ε) := by
        have h4 : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
          rw [show (4 : ℝ) = 2 * 2 from by norm_num, mul_pow]
        rw [h4]
        field_simp
    _ ≤ ε / ((2 : ℝ) ^ n * 4) * (aa e ε n) ^ (n - k) :=
        mul_le_mul_of_nonneg_left hQ (by positivity)

lemma vv_summable (e : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    Summable (fun n => vv e ε k n) := by
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℕ => ε / ((2 : ℝ) ^ n * 4)) ?hg ?h
  · have hgeo : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have h := hgeo.mul_left (ε / 4)
    rwa [show (fun n : ℕ => ε / 4 * (1 / 2 : ℝ) ^ n) =
        fun n : ℕ => ε / ((2 : ℝ) ^ n * 4) from by
      funext n
      rw [div_pow, one_pow]
      ring] at h
  · filter_upwards [show ∀ᶠ n in cofinite, k < n from by
        rw [Nat.cofinite_eq_atTop]; exact eventually_gt_atTop k] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg (vv_nonneg e ε k n)]
    exact vv_le e ε hε hn

/-- The total contribution of the `j`-th derivative series is at most `ε`, for `j ≤ 2`. -/
lemma vv_sum_le (e : ℕ → ℝ) (he : ∀ k : ℕ, k ≤ 2 → e k = 0) (ε : ℝ) (hε : 0 < ε)
    {j : ℕ} (hj : j ≤ 2) : ∑' n, vv e ε j n ≤ ε := by
  have hbd : ∀ n, vv e ε j n ≤ ε / ((2 : ℝ) ^ n * 4) := by
    intro n
    by_cases hn : n ≤ 2
    · have hen : e n = 0 := he n hn
      have hz : vv e ε j n = 0 := by simp [vv, hen]
      rw [hz]
      positivity
    · rw [not_le] at hn
      exact vv_le e ε hε (lt_of_le_of_lt hj hn)
  have hsum1 : Summable (fun n => vv e ε j n) := vv_summable e ε hε j
  have hsum2 : Summable (fun n : ℕ => ε / ((2 : ℝ) ^ n * 4)) := by
    have hgeo : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have h := hgeo.mul_left (ε / 4)
    rwa [show (fun n : ℕ => ε / 4 * (1 / 2 : ℝ) ^ n) =
        fun n : ℕ => ε / ((2 : ℝ) ^ n * 4) from by
      funext n
      rw [div_pow, one_pow]
      ring] at h
  have hle := Summable.tsum_le_tsum hbd hsum1 hsum2
  have hval : ∑' n : ℕ, ε / ((2 : ℝ) ^ n * 4) = ε / 2 := by
    have h1 : (fun n : ℕ => ε / ((2 : ℝ) ^ n * 4)) =
        fun n : ℕ => ε / 4 * (1 / 2 : ℝ) ^ n := by
      funext n
      rw [div_pow, one_pow]
      ring
    rw [h1, tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
    ring
  rw [hval] at hle
  linarith

lemma term_jet (e : ℕ → ℝ) (he : ∀ k : ℕ, k ≤ 2 → e k = 0) (ε : ℝ) (hε : 0 < ε)
    (n k : ℕ) : iteratedDeriv k (term e ε n) 0 = if n = k then e k else 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have he0 : e 0 = 0 := he 0 (by norm_num)
    have hterm : term e ε 0 = 0 := by
      funext y
      simp [term, he0]
    have hL : iteratedDeriv k (term e ε 0) 0 = 0 := by
      rw [hterm]
      exact iteratedDeriv_zero_fun k 0
    have hR : (if 0 = k then e k else 0) = 0 := by
      by_cases h : 0 = k
      · rw [if_pos h, ← h]
        exact he 0 (by norm_num)
      · exact if_neg h
    rw [hL, hR]
  · have hn1 : 1 ≤ n := hn
    have haapos : 0 < aa e ε n := aa_pos e ε n
    unfold term
    rw [iteratedDeriv_const_mul _ ((inner_contDiff e ε n).of_le (natCast_le_topE k) |>.contDiffAt),
      pow_mul_comp_zero bumpFun_contDiff bumpFun_one haapos n k]
    by_cases h : k = n
    · rw [if_pos h, if_pos h.symm, h]
      exact div_mul_cancel₀ (e n) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
    · rw [if_neg h, if_neg (fun hh => h hh.symm), mul_zero]

/-! ## Assembly -/

/-- **Borel-type series with small first two derivatives.**  For every sequence `e : ℕ → ℝ` which
vanishes in the orders `0,1,2`, and every `ε > 0`, there is a `C^∞` function `S : ℝ → ℝ` whose
`k`-th derivative at `0` is `e k` for every `k`, and whose first two derivatives are bounded by `ε`
on the negative half-line `(-∞,0]`. -/
theorem borel_series (e : ℕ → ℝ)
    (he : ∀ k : ℕ, k ≤ 2 → e k = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ S : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) S ∧ (∀ k : ℕ, iteratedDeriv k S 0 = e k) ∧
      (∀ u : ℝ, u ≤ 0 → |S u| ≤ ε) ∧
      (∀ u : ℝ, u ≤ 0 → |deriv S u| ≤ ε) ∧
      (∀ u : ℝ, u ≤ 0 → |deriv (deriv S) u| ≤ ε) := by
  have hsum0 : Summable (fun n => vv e ε 0 n) := vv_summable e ε hε 0
  have hsum1 : Summable (fun n => vv e ε 1 n) := vv_summable e ε hε 1
  have hsum2 : Summable (fun n => vv e ε 2 n) := vv_summable e ε hε 2
  have hpt : ∀ y : ℝ, Summable (fun n => term e ε n y) := by
    intro y
    refine Summable.of_norm_bounded hsum0 (fun n => ?_)
    simpa [Real.norm_eq_abs] using term_bound e he ε hε 0 n y
  have hpt1 : Summable (fun n => deriv (term e ε n) 0) := by
    refine Summable.of_norm_bounded hsum1 (fun n => ?_)
    have h := term_bound e he ε hε 1 n 0
    simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      ← iteratedDeriv_one] using h
  have hderivS : deriv (fun x : ℝ => ∑' n, term e ε n x) =
      fun y => ∑' n, deriv (term e ε n) y :=
    deriv_tsum (u := fun n => vv e ε 1 n) hsum1
      (fun n => (term_contDiff e ε n).differentiable (by simp))
      (fun n y => by
        have h := term_bound e he ε hε 1 n y
        simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
          ← iteratedDeriv_one] using h)
      (hpt 0)
  have hderiv2 : deriv (deriv (fun x : ℝ => ∑' n, term e ε n x)) =
      fun y => ∑' n, deriv (deriv (term e ε n)) y := by
    rw [hderivS]
    exact deriv_tsum (u := fun n => vv e ε 2 n) hsum2
      (fun n => by
        rw [← iteratedDeriv_one]
        exact (term_contDiff e ε n).differentiable_iteratedDeriv 1 (natCast_lt_topE 1))
      (fun n y => by
        have h := term_bound e he ε hε 2 n y
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at h
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h
        exact h)
      hpt1
  refine ⟨fun x => ∑' n, term e ε n x, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_tsum (𝕜 := ℝ) (N := ⊤) (f := fun n => term e ε n)
      (v := fun m n => vv e ε m n)
      (fun n => term_contDiff e ε n)
      (fun m _ => vv_summable e ε hε m)
      (fun m n x _ => term_bound e he ε hε m n x)
  · intro k
    have hjet : iteratedDeriv k (fun x : ℝ => ∑' n, term e ε n x) 0 =
        ∑' n, iteratedDeriv k (term e ε n) 0 := by
      have h := iteratedDerivWithin_tsum (f := fun n => term e ε n) k isOpen_univ
        (Set.mem_univ (0 : ℝ)) (fun t _ => hpt t)
        (fun j _ _ => SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
          (fun K _ _ => ⟨fun n => vv e ε j n, vv_summable e ε hε j,
            fun n r _ => by
              rw [iteratedDerivWithin_univ, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
              exact term_bound e he ε hε j n r⟩))
        (fun n j r _ _ => by
          rw [iteratedDerivWithin_univ]
          exact ((term_contDiff e ε n).differentiable_iteratedDeriv j (natCast_lt_topE j)).differentiableAt)
      rw [iteratedDerivWithin_univ] at h
      simpa using h
    rw [hjet, tsum_congr (fun n => term_jet e he ε hε n k)]
    simpa using tsum_eq_single k (fun n hn => if_neg hn)
  · intro u hu
    have hterm0 : ∀ n, |term e ε n u| ≤ vv e ε 0 n := by
      intro n
      have h := term_bound e he ε hε 0 n u
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
      exact h
    have hsumAbs : Summable (fun n => |term e ε n u|) :=
      Summable.of_nonneg_of_le (fun n => abs_nonneg _) hterm0 hsum0
    have h1 : |∑' n, term e ε n u| ≤ ∑' n, |term e ε n u| := by
      have h := norm_tsum_le_tsum_norm (f := fun n => term e ε n u)
        (by simpa [Real.norm_eq_abs] using hsumAbs)
      simpa [Real.norm_eq_abs] using h
    have h2 : ∑' n, |term e ε n u| ≤ ∑' n, vv e ε 0 n :=
      Summable.tsum_le_tsum hterm0 hsumAbs hsum0
    have h3 : ∑' n, vv e ε 0 n ≤ ε := vv_sum_le e he ε hε (by norm_num : (0 : ℕ) ≤ 2)
    calc |(fun x : ℝ => ∑' n, term e ε n x) u|
        = |∑' n, term e ε n u| := rfl
      _ ≤ ∑' n, vv e ε 0 n := h1.trans h2
      _ ≤ ε := h3
  · intro u hu
    rw [hderivS]
    have hterm1 : ∀ n, |deriv (term e ε n) u| ≤ vv e ε 1 n := by
      intro n
      have h := term_bound e he ε hε 1 n u
      simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
        ← iteratedDeriv_one] using h
    have hsumAbs : Summable (fun n => |deriv (term e ε n) u|) :=
      Summable.of_nonneg_of_le (fun n => abs_nonneg _) hterm1 hsum1
    have h1 : |∑' n, deriv (term e ε n) u| ≤ ∑' n, |deriv (term e ε n) u| := by
      have h := norm_tsum_le_tsum_norm (f := fun n => deriv (term e ε n) u)
        (by simpa [Real.norm_eq_abs] using hsumAbs)
      simpa [Real.norm_eq_abs] using h
    have h2 : ∑' n, |deriv (term e ε n) u| ≤ ∑' n, vv e ε 1 n :=
      Summable.tsum_le_tsum hterm1 hsumAbs hsum1
    have h3 : ∑' n, vv e ε 1 n ≤ ε := vv_sum_le e he ε hε (by norm_num : (1 : ℕ) ≤ 2)
    exact h1.trans (h2.trans h3)
  · intro u hu
    rw [hderiv2]
    have hterm2 : ∀ n, |deriv (deriv (term e ε n)) u| ≤ vv e ε 2 n := by
      intro n
      have h := term_bound e he ε hε 2 n u
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at h
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h
      exact h
    have hsumAbs : Summable (fun n => |deriv (deriv (term e ε n)) u|) :=
      Summable.of_nonneg_of_le (fun n => abs_nonneg _) hterm2 hsum2
    have h1 : |∑' n, deriv (deriv (term e ε n)) u| ≤
        ∑' n, |deriv (deriv (term e ε n)) u| := by
      have h := norm_tsum_le_tsum_norm (f := fun n => deriv (deriv (term e ε n)) u)
        (by simpa [Real.norm_eq_abs] using hsumAbs)
      simpa [Real.norm_eq_abs] using h
    have h2 : ∑' n, |deriv (deriv (term e ε n)) u| ≤ ∑' n, vv e ε 2 n :=
      Summable.tsum_le_tsum hterm2 hsumAbs hsum2
    have h3 : ∑' n, vv e ε 2 n ≤ ε := vv_sum_le e he ε hε (by norm_num : (2 : ℕ) ≤ 2)
    exact h1.trans (h2.trans h3)

end

end Work.Anchor
