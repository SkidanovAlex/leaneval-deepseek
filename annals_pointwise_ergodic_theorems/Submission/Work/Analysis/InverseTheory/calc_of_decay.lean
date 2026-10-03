import Mathlib
import Submission.Work.Analysis.InverseTheory.poisson_approx

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators
open MeasureTheory

namespace Work.Analysis.InverseTheory

/-- The summand `ε ψ(ε (x - y))` of Lemma `calc`. -/
noncomputable def calcS (ψ : ℝ → ℂ) (ε : ℝ) (x y : ℤ) : ℂ :=
  (ε : ℂ) * ψ (ε * ((x : ℝ) - (y : ℝ)))

section Aux

variable {ψ : ℝ → ℂ} {C : ℝ} {ε : ℝ} {x : ℤ}

/-! ## Elementary properties of `jbDecay` -/

lemma jbDecay_neg (n : ℕ) (t : ℝ) : jbDecay n (-t) = jbDecay n t := by
  rw [jbDecay, jbDecay, jb_neg]

lemma jbDecay_le_of_abs_le {n : ℕ} {s t : ℝ} (h : |t| ≤ |s|) : jbDecay n s ≤ jbDecay n t := by
  have h1 : jb t ≤ jb s := jb_le_jb_iff.mpr h
  have h2 : (jb s)⁻¹ ≤ (jb t)⁻¹ := (inv_le_inv₀ (jb_pos s) (jb_pos t)).mpr h1
  exact pow_le_pow_left₀ (jb_inv_nonneg s) h2 n

/-! ## Summability of the scalar Riemann majorant

This is the analytic input that makes every series below summable: the family
`j ↦ ε ⟨ε (c + j)⟩^{-12}` is bounded by a constant times the summable family `(j+1)^{-12}`. -/

lemma summable_eps_jbDecay_shift (hε0 : 0 < ε) (c : ℝ) :
    Summable (fun j : ℕ => ε * jbDecay 12 (ε * (c + (j : ℝ)))) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |c| ≤ (N : ℝ) := ⟨⌈|c|⌉₊, Nat.le_ceil |c|⟩
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  set K : ℝ := ε * (2 * (N : ℝ) + 1) ^ 12 + 2 ^ 24 * ε⁻¹ ^ 11 with hK
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  have h2N : (0 : ℝ) < 2 * (N : ℝ) + 1 := by linarith
  have hG : Summable (fun j : ℕ => K * (((j : ℝ) + 1)⁻¹) ^ 12) := by
    have h2 : Summable (fun j : ℕ => (((j : ℝ) + 1)⁻¹) ^ 12) := by
      refine summable_inv_pow_succ.congr (fun j => ?_)
      push_cast
      ring
    simpa only [mul_comm] using h2.mul_left K
  refine Summable.of_nonneg_of_le (f := fun j : ℕ => K * (((j : ℝ) + 1)⁻¹) ^ 12)
    (g := fun j : ℕ => ε * jbDecay 12 (ε * (c + (j : ℝ)))) (fun j => ?_) (fun j => ?_) hG
  · exact mul_nonneg hε0.le (jbDecay_nonneg 12 _)
  · by_cases hj : (j : ℝ) ≤ 2 * N
    · have hjle : (j : ℝ) + 1 ≤ 2 * N + 1 := by linarith
      have hpos : 0 < (j : ℝ) + 1 := by positivity
      have hmono : ((2 * (N : ℝ) + 1)⁻¹) ^ 12 ≤ (((j : ℝ) + 1)⁻¹) ^ 12 := by
        refine pow_le_pow_left₀ (by positivity) ?_ 12
        exact (inv_le_inv₀ h2N hpos).mpr hjle
      have hKge : ε * (2 * (N : ℝ) + 1) ^ 12 ≤ K := by
        rw [hK]
        have : (0 : ℝ) ≤ 2 ^ 24 * ε⁻¹ ^ 11 := by positivity
        linarith
      have hkey : ε ≤ K * (((j : ℝ) + 1)⁻¹) ^ 12 := by
        have h1 : ε * (2 * (N : ℝ) + 1) ^ 12 * ((2 * (N : ℝ) + 1)⁻¹) ^ 12 = ε := by
          rw [mul_assoc, inv_pow, mul_inv_cancel₀ (by positivity), mul_one]
        rw [← h1]
        exact mul_le_mul hKge hmono (by positivity) hKnn
      calc ε * jbDecay 12 (ε * (c + (j : ℝ))) ≤ ε * 1 :=
            mul_le_mul_of_nonneg_left (jbDecay_le_one 12 _) hε0.le
        _ = ε := mul_one ε
        _ ≤ K * (((j : ℝ) + 1)⁻¹) ^ 12 := hkey
    · have hj2 : 2 * (N : ℝ) < (j : ℝ) := not_le.mp hj
      have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
        have hjne0 : j ≠ 0 := by rintro rfl; simp at hjpos
        exact_mod_cast (show 1 ≤ j by omega)
      have habs : (j : ℝ) / 2 ≤ |c + (j : ℝ)| := by
        have h1 : (j : ℝ) ≤ |c + (j : ℝ)| + |c| := by
          calc (j : ℝ) = (c + (j : ℝ)) + (-c) := by ring
            _ ≤ |(c + (j : ℝ)) + (-c)| := le_abs_self _
            _ ≤ |c + (j : ℝ)| + |(-c)| := abs_add_le _ _
            _ = |c + (j : ℝ)| + |c| := by rw [abs_neg]
        have h3 : |c| ≤ (N : ℝ) := hN
        linarith
      have hjb : ε * ((j : ℝ) / 2) ≤ jb (ε * (c + (j : ℝ))) := by
        have h1 : ε * ((j : ℝ) / 2) ≤ |ε * (c + (j : ℝ))| := by
          rw [abs_mul, abs_of_pos hε0]
          exact mul_le_mul_of_nonneg_left habs hε0.le
        exact h1.trans (abs_le_jb _)
      have h3 : jbDecay 12 (ε * (c + (j : ℝ))) ≤ ((ε * ((j : ℝ) / 2))⁻¹) ^ 12 := by
        rw [jbDecay]
        refine pow_le_pow_left₀ (jb_inv_nonneg _) ?_ 12
        exact (inv_le_inv₀ (jb_pos _) (by positivity)).mpr hjb
      have hjne : (j : ℝ) ≠ 0 := ne_of_gt hjpos
      have hstep : ε * ((ε * ((j : ℝ) / 2))⁻¹) ^ 12
          = 2 ^ 12 * ε⁻¹ ^ 11 * ((j : ℝ)⁻¹) ^ 12 := by
        field_simp
      have hmono : ((j : ℝ)⁻¹) ^ 12 ≤ 2 ^ 12 * (((j : ℝ) + 1)⁻¹) ^ 12 := by
        have h2 : (2 * (j : ℝ))⁻¹ ≤ ((j : ℝ) + 1)⁻¹ := by
          rw [inv_le_inv₀ (by linarith) (by linarith)]
          linarith
        have h3 : ((2 * (j : ℝ))⁻¹) ^ 12 ≤ (((j : ℝ) + 1)⁻¹) ^ 12 :=
          pow_le_pow_left₀ (by positivity) h2 12
        have h4 : (2 : ℝ) ^ 12 * ((2 * (j : ℝ))⁻¹) ^ 12 = ((j : ℝ)⁻¹) ^ 12 := by
          rw [mul_inv, mul_pow, ← mul_assoc, ← mul_pow,
            mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow, one_mul]
        calc ((j : ℝ)⁻¹) ^ 12 = 2 ^ 12 * ((2 * (j : ℝ))⁻¹) ^ 12 := h4.symm
          _ ≤ 2 ^ 12 * (((j : ℝ) + 1)⁻¹) ^ 12 :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
      have hKge : 2 ^ 24 * ε⁻¹ ^ 11 ≤ K := by
        rw [hK]
        have : (0 : ℝ) ≤ ε * (2 * (N : ℝ) + 1) ^ 12 := by positivity
        linarith
      calc ε * jbDecay 12 (ε * (c + (j : ℝ)))
          ≤ ε * ((ε * ((j : ℝ) / 2))⁻¹) ^ 12 := mul_le_mul_of_nonneg_left h3 hε0.le
        _ = 2 ^ 12 * ε⁻¹ ^ 11 * ((j : ℝ)⁻¹) ^ 12 := hstep
        _ ≤ 2 ^ 12 * ε⁻¹ ^ 11 * (2 ^ 12 * (((j : ℝ) + 1)⁻¹) ^ 12) :=
              mul_le_mul_of_nonneg_left hmono (by positivity)
        _ = 2 ^ 24 * ε⁻¹ ^ 11 * (((j : ℝ) + 1)⁻¹) ^ 12 := by ring
        _ ≤ K * (((j : ℝ) + 1)⁻¹) ^ 12 :=
              mul_le_mul_of_nonneg_right hKge (by positivity)

/-! ## The pointwise bound and the two one-sided summability statements -/

lemma norm_calcS_le (hdecay : ∀ t : ℝ, ‖ψ t‖ ≤ C * jbDecay 12 t) (hε0 : 0 < ε) (y : ℤ) :
    ‖calcS ψ ε x y‖ ≤ C * (ε * jbDecay 12 (ε * ((x : ℝ) - (y : ℝ)))) := by
  rw [calcS, norm_mul, Complex.norm_of_nonneg hε0.le]
  calc ε * ‖ψ (ε * ((x : ℝ) - (y : ℝ)))‖
      ≤ ε * (C * jbDecay 12 (ε * ((x : ℝ) - (y : ℝ)))) :=
        mul_le_mul_of_nonneg_left (hdecay _) hε0.le
    _ = C * (ε * jbDecay 12 (ε * ((x : ℝ) - (y : ℝ)))) := by ring

lemma summable_calcS_right (hdecay : ∀ t : ℝ, ‖ψ t‖ ≤ C * jbDecay 12 t) (hC0 : 0 ≤ C)
    (hε0 : 0 < ε) (k : ℤ) :
    Summable (fun j : ℕ => calcS ψ ε x (k + (j : ℤ))) := by
  refine Summable.of_norm_bounded
    (g := fun j : ℕ => C * (ε * jbDecay 12 (ε * (((k : ℝ) - (x : ℝ)) + (j : ℝ))))) ?_ ?_
  · exact (summable_eps_jbDecay_shift hε0 (((k : ℝ) - (x : ℝ)))).mul_left C
  · intro j
    refine (norm_calcS_le hdecay hε0 (k + (j : ℤ))).trans ?_
    have h2 : ε * ((x : ℝ) - (((k + (j : ℤ) : ℤ)) : ℝ))
        = -(ε * (((k : ℝ) - (x : ℝ)) + (j : ℝ))) := by
      push_cast; ring
    rw [h2, jbDecay_neg]

lemma summable_calcS_left (hdecay : ∀ t : ℝ, ‖ψ t‖ ≤ C * jbDecay 12 t) (hC0 : 0 ≤ C)
    (hε0 : 0 < ε) (k : ℤ) :
    Summable (fun j : ℕ => calcS ψ ε x (k - (j : ℤ))) := by
  refine Summable.of_norm_bounded
    (g := fun j : ℕ => C * (ε * jbDecay 12 (ε * (((x : ℝ) - (k : ℝ)) + (j : ℝ))))) ?_ ?_
  · exact (summable_eps_jbDecay_shift hε0 (((x : ℝ) - (k : ℝ)))).mul_left C
  · intro j
    refine (norm_calcS_le hdecay hε0 (k - (j : ℤ))).trans ?_
    have h2 : ε * ((x : ℝ) - (((k - (j : ℤ) : ℤ)) : ℝ))
        = ε * (((x : ℝ) - (k : ℝ)) + (j : ℝ)) := by
      push_cast; ring
    rw [h2]

/-! ## The two one-sided quantitative bounds (Riemann-sum comparison) -/

lemma norm_tsum_calcS_right (hdecay : ∀ t : ℝ, ‖ψ t‖ ≤ C * jbDecay 12 t) (hC0 : 0 ≤ C)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (k : ℤ) (hk : (x : ℝ) ≤ (k : ℝ)) :
    ‖∑' j : ℕ, calcS ψ ε x (k + (j : ℤ))‖
      ≤ C * 2 ^ 60 * jbDecay 10 (ε * ((k : ℝ) - (x : ℝ))) := by
  have ht : 0 ≤ ε * ((k : ℝ) - (x : ℝ)) := mul_nonneg hε0.le (sub_nonneg.mpr hk)
  have hmajor : Summable
      (fun j : ℕ => C * (ε * jbDecay 12 (ε * (((k : ℝ) - (x : ℝ)) + (j : ℝ))))) :=
    (summable_eps_jbDecay_shift hε0 ((k : ℝ) - (x : ℝ))).mul_left C
  have hbdd : ‖∑' j : ℕ, calcS ψ ε x (k + (j : ℤ))‖
      ≤ ∑' j : ℕ, C * (ε * jbDecay 12 (ε * (((k : ℝ) - (x : ℝ)) + (j : ℝ)))) := by
    refine tsum_of_norm_bounded hmajor.hasSum fun j => ?_
    refine (norm_calcS_le hdecay hε0 (k + (j : ℤ))).trans ?_
    have h2 : ε * ((x : ℝ) - (((k + (j : ℤ) : ℤ)) : ℝ))
        = -(ε * (((k : ℝ) - (x : ℝ)) + (j : ℝ))) := by
      push_cast; ring
    rw [h2, jbDecay_neg]
  calc ‖∑' j : ℕ, calcS ψ ε x (k + (j : ℤ))‖
      ≤ ∑' j : ℕ, C * (ε * jbDecay 12 (ε * (((k : ℝ) - (x : ℝ)) + (j : ℝ)))) := hbdd
    _ = C * ∑' j : ℕ, ε * jbDecay 12 (ε * (((k : ℝ) - (x : ℝ)) + (j : ℝ))) := by
        rw [tsum_mul_left]
    _ ≤ C * (2 ^ 60 * jbDecay 11 (ε * ((k : ℝ) - (x : ℝ)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        have hcongr : (fun j : ℕ => ε * jbDecay 12 (ε * (((k : ℝ) - (x : ℝ)) + (j : ℝ))))
            = fun j : ℕ => ε * jbDecay 12 (ε * ((k : ℝ) - (x : ℝ)) + ε * (j : ℝ)) := by
          funext j; congr 2; ring
        rw [hcongr]
        exact riemann_shift 11 (by norm_num) hε0 hε1 ht
    _ = C * 2 ^ 60 * jbDecay 11 (ε * ((k : ℝ) - (x : ℝ))) := by ring
    _ ≤ C * 2 ^ 60 * jbDecay 10 (ε * ((k : ℝ) - (x : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact jbDecay_anti (by norm_num : 10 ≤ 11) _

lemma norm_tsum_calcS_left (hdecay : ∀ t : ℝ, ‖ψ t‖ ≤ C * jbDecay 12 t) (hC0 : 0 ≤ C)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (k : ℤ) (hk : (k : ℝ) ≤ (x : ℝ)) :
    ‖∑' j : ℕ, calcS ψ ε x (k - (j : ℤ))‖
      ≤ C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - (k : ℝ))) := by
  have ht : 0 ≤ ε * ((x : ℝ) - (k : ℝ)) := mul_nonneg hε0.le (sub_nonneg.mpr hk)
  have hmajor : Summable
      (fun j : ℕ => C * (ε * jbDecay 12 (ε * (((x : ℝ) - (k : ℝ)) + (j : ℝ))))) :=
    (summable_eps_jbDecay_shift hε0 ((x : ℝ) - (k : ℝ))).mul_left C
  have hbdd : ‖∑' j : ℕ, calcS ψ ε x (k - (j : ℤ))‖
      ≤ ∑' j : ℕ, C * (ε * jbDecay 12 (ε * (((x : ℝ) - (k : ℝ)) + (j : ℝ)))) := by
    refine tsum_of_norm_bounded hmajor.hasSum fun j => ?_
    refine (norm_calcS_le hdecay hε0 (k - (j : ℤ))).trans ?_
    have h2 : ε * ((x : ℝ) - (((k - (j : ℤ) : ℤ)) : ℝ))
        = ε * (((x : ℝ) - (k : ℝ)) + (j : ℝ)) := by
      push_cast; ring
    rw [h2]
  calc ‖∑' j : ℕ, calcS ψ ε x (k - (j : ℤ))‖
      ≤ ∑' j : ℕ, C * (ε * jbDecay 12 (ε * (((x : ℝ) - (k : ℝ)) + (j : ℝ)))) := hbdd
    _ = C * ∑' j : ℕ, ε * jbDecay 12 (ε * (((x : ℝ) - (k : ℝ)) + (j : ℝ))) := by
        rw [tsum_mul_left]
    _ ≤ C * (2 ^ 60 * jbDecay 11 (ε * ((x : ℝ) - (k : ℝ)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        have hcongr : (fun j : ℕ => ε * jbDecay 12 (ε * (((x : ℝ) - (k : ℝ)) + (j : ℝ))))
            = fun j : ℕ => ε * jbDecay 12 (ε * ((x : ℝ) - (k : ℝ)) + ε * (j : ℝ)) := by
          funext j; congr 2; ring
        rw [hcongr]
        exact riemann_shift 11 (by norm_num) hε0 hε1 ht
    _ = C * 2 ^ 60 * jbDecay 11 (ε * ((x : ℝ) - (k : ℝ))) := by ring
    _ ≤ C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - (k : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact jbDecay_anti (by norm_num : 10 ≤ 11) _

/-! ## Splittings of the full line and of the interval -/

/-- The full line splits at `k` into the right tail (from `k`) and the left tail (up to `k-1`). -/
lemma tsum_calcS_eq_right_add_left (hdecay : ∀ t : ℝ, ‖ψ t‖ ≤ C * jbDecay 12 t)
    (hC0 : 0 ≤ C) (hε0 : 0 < ε) (k : ℤ) :
    (∑' y : ℤ, calcS ψ ε x y)
      = (∑' j : ℕ, calcS ψ ε x (k + (j : ℤ)))
        + (∑' j : ℕ, calcS ψ ε x (k - 1 - (j : ℤ))) := by
  have h1 : Summable (fun j : ℕ => calcS ψ ε x ((j : ℤ) + 1 + k)) := by
    have h : Summable (fun j : ℕ => calcS ψ ε x ((k + 1) + (j : ℤ))) :=
      summable_calcS_right hdecay hC0 hε0 (k + 1)
    exact h.congr (fun j => by congr 1; ring)
  have h2 : Summable (fun j : ℕ => calcS ψ ε x (-((j : ℤ) + 1) + k)) := by
    have h : Summable (fun j : ℕ => calcS ψ ε x ((k - 1) - (j : ℤ))) :=
      summable_calcS_left hdecay hC0 hε0 (k - 1)
    exact h.congr (fun j => by congr 1; ring)
  have hsplit := tsum_of_add_one_of_neg_add_one (f := fun z : ℤ => calcS ψ ε x (z + k)) h1 h2
  have htrans : (∑' n : ℤ, calcS ψ ε x (n + k)) = ∑' y : ℤ, calcS ψ ε x y :=
    Equiv.tsum_eq (Equiv.addRight k) (calcS ψ ε x)
  rw [htrans] at hsplit
  have h0 : calcS ψ ε x (0 + k) = calcS ψ ε x k := by rw [zero_add]
  have hz2 : (∑' j : ℕ, calcS ψ ε x ((j : ℤ) + 1 + k)) + calcS ψ ε x k
      = ∑' j : ℕ, calcS ψ ε x (k + (j : ℤ)) := by
    have hz : (∑' j : ℕ, calcS ψ ε x (k + (j : ℤ)))
        = calcS ψ ε x k + ∑' j : ℕ, calcS ψ ε x ((j : ℤ) + 1 + k) := by
      have hzz : (∑' j : ℕ, calcS ψ ε x (k + (j : ℤ)))
          = calcS ψ ε x (k + (((0 : ℕ)) : ℤ))
            + ∑' b : ℕ, calcS ψ ε x (k + ((b + 1 : ℕ) : ℤ)) :=
        (summable_calcS_right hdecay hC0 hε0 k).tsum_eq_zero_add
      have hz0 : calcS ψ ε x (k + (((0 : ℕ)) : ℤ)) = calcS ψ ε x k := by norm_num
      have hz1 : (∑' b : ℕ, calcS ψ ε x (k + ((b + 1 : ℕ) : ℤ)))
          = ∑' j : ℕ, calcS ψ ε x ((j : ℤ) + 1 + k) := by
        refine tsum_congr fun b => ?_
        congr 1
        push_cast
        ring
      rw [hz0, hz1] at hzz
      exact hzz
    rw [hz]
    ring
  have h3 : (∑' j : ℕ, calcS ψ ε x (-((j : ℤ) + 1) + k))
      = ∑' j : ℕ, calcS ψ ε x (k - 1 - (j : ℤ)) := by
    refine tsum_congr fun j => ?_
    congr 1
    ring
  rw [h0, hz2, h3] at hsplit
  exact hsplit

/-- A right tail from `n` splits into the finite interval sum over `[n,m]` and the right tail
from `m+1`. -/
lemma tsum_calcS_eq_sum_Icc_add (hdecay : ∀ t : ℝ, ‖ψ t‖ ≤ C * jbDecay 12 t)
    (hC0 : 0 ≤ C) (hε0 : 0 < ε) {n m : ℤ} (hnm : n ≤ m) :
    (∑' j : ℕ, calcS ψ ε x (n + (j : ℤ)))
      = (∑ y ∈ Finset.Icc n m, calcS ψ ε x y)
        + (∑' j : ℕ, calcS ψ ε x (m + 1 + (j : ℤ))) := by
  have hsum : Summable (fun j : ℕ => calcS ψ ε x (n + (j : ℤ))) :=
    summable_calcS_right hdecay hC0 hε0 n
  set K : ℕ := (m + 1 - n).toNat with hK
  have hK' : ((K : ℕ) : ℤ) = m + 1 - n := by
    rw [hK]
    exact Int.toNat_of_nonneg (by omega)
  have hmain := hsum.sum_add_tsum_nat_add K
  have htail : (∑' i : ℕ, calcS ψ ε x (n + ((i + K : ℕ) : ℤ)))
      = ∑' j : ℕ, calcS ψ ε x (m + 1 + (j : ℤ)) := by
    refine tsum_congr fun i => ?_
    congr 1
    push_cast [hK']
    ring
  have hmap : (Finset.range K).image (fun i : ℕ => n + (i : ℤ)) = Finset.Icc n m := by
    apply Finset.ext
    intro y
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hj' : (j : ℤ) < (K : ℤ) := by exact_mod_cast hj
      constructor <;> omega
    · intro hy
      have hy0 : (0 : ℤ) ≤ y - n := by omega
      have hylt : (y - n).toNat < K := by
        have h1 : ((y - n).toNat : ℤ) < (K : ℤ) := by
          rw [Int.toNat_of_nonneg hy0, hK']
          omega
        exact_mod_cast h1
      refine ⟨(y - n).toNat, hylt, ?_⟩
      rw [Int.toNat_of_nonneg hy0]
      ring
  have hhead : (∑ i ∈ Finset.range K, calcS ψ ε x (n + (i : ℤ)))
      = ∑ y ∈ Finset.Icc n m, calcS ψ ε x y := by
    rw [← Finset.sum_image (f := fun y : ℤ => calcS ψ ε x y) (s := Finset.range K)
      (g := fun i : ℕ => n + (i : ℤ))
      (fun a _ b _ hab => Int.ofNat_inj.mp (add_left_cancel hab))]
    rw [hmap]
  rw [htail, hhead] at hmain
  exact hmain.symm

end Aux

/-! ## Lemma `calc`

The smoothing identity: `∑_{y ∈ [a,b]∩ℤ} ε ψ(ε(x-y))` approximates the indicator of `[a,b]`
with error `2^60 C²(ε^10 + ⟨ε(x-a)⟩^{-10} + ⟨ε(x-b)⟩^{-10})`. -/
theorem calc_of_decay (ψ : ℝ → ℂ) (hcont : Continuous ψ) (C : ℝ) (hC : 1 ≤ C)
    (hint : ∫ t, ψ t = 1)
    (hdecay : ∀ t : ℝ, ‖ψ t‖ ≤ C * jbDecay 12 t)
    (hFdecay : ∀ t : ℝ, ‖realFourier ψ t‖ ≤ C * jbDecay 12 t)
    (a b : ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (x : ℤ) :
    ‖(∑ y ∈ Finset.Icc ⌈a⌉ ⌊b⌋, (ε : ℂ) * ψ (ε * ((x : ℝ) - y)))
        - (if a ≤ (x : ℝ) ∧ (x : ℝ) ≤ b then (1 : ℂ) else 0)‖
      ≤ (2 : ℝ) ^ 60 * C ^ 2 * (ε ^ 10 + jbDecay 10 (ε * ((x : ℝ) - a))
          + jbDecay 10 (ε * ((x : ℝ) - b))) := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  change ‖(∑ y ∈ Finset.Icc ⌈a⌉ ⌊b⌋, calcS ψ ε x y)
      - (if a ≤ (x : ℝ) ∧ (x : ℝ) ≤ b then (1 : ℂ) else 0)‖
    ≤ (2 : ℝ) ^ 60 * C ^ 2 * (ε ^ 10 + jbDecay 10 (ε * ((x : ℝ) - a))
        + jbDecay 10 (ε * ((x : ℝ) - b)))
  by_cases hnm : ⌈a⌉ ≤ ⌊b⌋
  · have hceil : a ≤ ((⌈a⌉ : ℤ) : ℝ) := Int.le_ceil a
    have hfloor : ((⌊b⌋ : ℤ) : ℝ) ≤ b := Int.floor_le b
    have hnmR : ((⌈a⌉ : ℤ) : ℝ) ≤ ((⌊b⌋ : ℤ) : ℝ) := by exact_mod_cast hnm
    have hab : a ≤ b := hceil.trans (hnmR.trans hfloor)
    have hceil' : ((⌈a⌉ : ℤ) : ℝ) - 1 < a := by
      have h := (Int.lt_ceil (z := ⌈a⌉ - 1)).mp (by omega : (⌈a⌉ - 1 : ℤ) < ⌈a⌉)
      push_cast at h
      linarith
    have hfloor' : b < ((⌊b⌋ : ℤ) : ℝ) + 1 := by
      have h := (Int.floor_lt (z := ⌊b⌋ + 1)).mp (by omega : ⌊b⌋ < ⌊b⌋ + 1)
      push_cast at h
      linarith
    -- the three identities
    have hFn : (∑' y : ℤ, calcS ψ ε x y)
        = (∑' j : ℕ, calcS ψ ε x (⌈a⌉ + (j : ℤ)))
          + (∑' j : ℕ, calcS ψ ε x (⌈a⌉ - 1 - (j : ℤ))) :=
      tsum_calcS_eq_right_add_left hdecay hC0 hε0 ⌈a⌉
    have hFm : (∑' y : ℤ, calcS ψ ε x y)
        = (∑' j : ℕ, calcS ψ ε x (⌊b⌋ + 1 + (j : ℤ)))
          + (∑' j : ℕ, calcS ψ ε x (⌊b⌋ - (j : ℤ))) := by
      have h : (∑' y : ℤ, calcS ψ ε x y)
          = (∑' j : ℕ, calcS ψ ε x ((⌊b⌋ + 1) + (j : ℤ)))
            + (∑' j : ℕ, calcS ψ ε x ((⌊b⌋ + 1) - 1 - (j : ℤ))) :=
        tsum_calcS_eq_right_add_left hdecay hC0 hε0 (⌊b⌋ + 1)
      have hL : (∑' j : ℕ, calcS ψ ε x (⌊b⌋ + 1 - 1 - (j : ℤ)))
          = ∑' j : ℕ, calcS ψ ε x (⌊b⌋ - (j : ℤ)) := by
        refine tsum_congr fun j => ?_
        congr 1
        ring
      rw [hL] at h
      exact h
    have hnat : (∑' j : ℕ, calcS ψ ε x (⌈a⌉ + (j : ℤ)))
        = (∑ y ∈ Finset.Icc ⌈a⌉ ⌊b⌋, calcS ψ ε x y)
          + (∑' j : ℕ, calcS ψ ε x (⌊b⌋ + 1 + (j : ℤ))) :=
      tsum_calcS_eq_sum_Icc_add hdecay hC0 hε0 hnm
    -- indicator decomposition
    set PA : ℂ := if a ≤ (x : ℝ) then 1 else 0 with hPA
    set QB : ℂ := if b < (x : ℝ) then 1 else 0 with hQB
    have hind : (if a ≤ (x : ℝ) ∧ (x : ℝ) ≤ b then (1 : ℂ) else 0) = PA - QB := by
      by_cases h1 : a ≤ (x : ℝ)
      · by_cases h2 : (x : ℝ) ≤ b
        · have h3 : ¬ (b < (x : ℝ)) := not_lt.mpr h2
          simp [hPA, hQB, h1, h2, h3]
        · have h3 : b < (x : ℝ) := not_le.mp h2
          simp [hPA, hQB, h1, h2, h3]
      · have h4 : ¬ (a ≤ (x : ℝ) ∧ (x : ℝ) ≤ b) := fun ⟨h, _⟩ => h1 h
        have h5 : ¬ (b < (x : ℝ)) := fun hb => h1 (hab.trans hb.le)
        simp [hPA, hQB, h1, h4, h5]
    -- master identity
    have hI : (∑ y ∈ Finset.Icc ⌈a⌉ ⌊b⌋, calcS ψ ε x y)
        = (∑' y : ℤ, calcS ψ ε x y) - (∑' j : ℕ, calcS ψ ε x (⌈a⌉ - 1 - (j : ℤ)))
          - (∑' j : ℕ, calcS ψ ε x (⌊b⌋ + 1 + (j : ℤ))) := by
      rw [hFn, hnat]
      ring
    have hkey : (∑ y ∈ Finset.Icc ⌈a⌉ ⌊b⌋, calcS ψ ε x y)
        - (if a ≤ (x : ℝ) ∧ (x : ℝ) ≤ b then (1 : ℂ) else 0)
        = ((∑' y : ℤ, calcS ψ ε x y) - 1)
          - ((∑' j : ℕ, calcS ψ ε x (⌈a⌉ - 1 - (j : ℤ))) - (1 - PA))
          - ((∑' j : ℕ, calcS ψ ε x (⌊b⌋ + 1 + (j : ℤ))) - QB) := by
      rw [hind, hI]
      ring
    rw [hkey]
    -- the three bounds
    have hA : ‖(∑' y : ℤ, calcS ψ ε x y) - 1‖ ≤ 2 ^ 30 * C ^ 2 * ε ^ 10 := by
      have h := poisson_approx ψ hcont C hC hint hdecay hFdecay hε0 hε1 x
      simpa only [calcS] using h
    have hB1 : ‖(∑' j : ℕ, calcS ψ ε x (⌈a⌉ - 1 - (j : ℤ))) - (1 - PA)‖
        ≤ 2 ^ 30 * C ^ 2 * ε ^ 10 + C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - a)) := by
      by_cases hPA' : a ≤ (x : ℝ)
      · have hPA1 : PA = 1 := by rw [hPA]; simp only [hPA', if_true]
        rw [hPA1, sub_self, sub_zero]
        have hxceil : ((⌈a⌉ : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast (Int.ceil_le).mpr hPA'
        have h1 : ‖∑' j : ℕ, calcS ψ ε x (⌈a⌉ - 1 - (j : ℤ))‖
            ≤ C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - (((⌈a⌉ : ℤ)) - 1 : ℤ))) :=
          norm_tsum_calcS_left hdecay hC0 hε0 hε1 (⌈a⌉ - 1) (by push_cast; linarith [hxceil])
        have h2 : jbDecay 10 (ε * ((x : ℝ) - (((⌈a⌉ : ℤ)) - 1 : ℤ))) ≤ jbDecay 10 (ε * ((x : ℝ) - a)) := by
          refine jbDecay_le_of_abs_le ?_
          rw [abs_mul, abs_mul, abs_of_pos hε0]
          refine mul_le_mul_of_nonneg_left ?_ hε0.le
          rw [abs_of_nonneg (by linarith [hxceil] : 0 ≤ (x : ℝ) - a),
            abs_of_nonneg (by push_cast; linarith [hxceil] : 0 ≤ (x : ℝ) - (((⌈a⌉ : ℤ)) - 1 : ℤ))]
          push_cast
          linarith [hceil']
        have h1' : ‖∑' j : ℕ, calcS ψ ε x (⌈a⌉ - 1 - (j : ℤ))‖
            ≤ C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - a)) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (mul_nonneg hC0 (by norm_num)))
        have h3 : (0 : ℝ) ≤ 2 ^ 30 * C ^ 2 * ε ^ 10 := by positivity
        linarith [h1', h3]
      · have hPA0 : PA = 0 := by rw [hPA]; simp only [hPA', if_false]
        rw [hPA0, sub_zero]
        have hxa : (x : ℝ) < a := not_le.mp hPA'
        have hxceil : (x : ℝ) ≤ ((⌈a⌉ : ℤ) : ℝ) := le_of_lt (hxa.trans_le hceil)
        have hId : (∑' j : ℕ, calcS ψ ε x (⌈a⌉ - 1 - (j : ℤ))) - 1
            = ((∑' y : ℤ, calcS ψ ε x y) - 1) - (∑' j : ℕ, calcS ψ ε x (⌈a⌉ + (j : ℤ))) := by
          rw [hFn]
          ring
        rw [hId]
        have h1 : ‖∑' j : ℕ, calcS ψ ε x (⌈a⌉ + (j : ℤ))‖
            ≤ C * 2 ^ 60 * jbDecay 10 (ε * (((⌈a⌉ : ℤ) : ℝ) - (x : ℝ))) :=
          norm_tsum_calcS_right hdecay hC0 hε0 hε1 ⌈a⌉ hxceil
        have h2 : jbDecay 10 (ε * (((⌈a⌉ : ℤ) : ℝ) - (x : ℝ))) ≤ jbDecay 10 (ε * ((x : ℝ) - a)) := by
          refine jbDecay_le_of_abs_le ?_
          rw [abs_mul, abs_mul, abs_of_pos hε0]
          refine mul_le_mul_of_nonneg_left ?_ hε0.le
          rw [abs_of_neg (by linarith [hxa] : (x : ℝ) - a < 0),
            abs_of_nonneg (by linarith [hxceil] : 0 ≤ ((⌈a⌉ : ℤ) : ℝ) - (x : ℝ))]
          linarith [hceil]
        have h1' : ‖∑' j : ℕ, calcS ψ ε x (⌈a⌉ + (j : ℤ))‖
            ≤ C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - a)) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (mul_nonneg hC0 (by norm_num)))
        calc ‖((∑' y : ℤ, calcS ψ ε x y) - 1) - (∑' j : ℕ, calcS ψ ε x (⌈a⌉ + (j : ℤ)))‖
            ≤ ‖(∑' y : ℤ, calcS ψ ε x y) - 1‖ + ‖∑' j : ℕ, calcS ψ ε x (⌈a⌉ + (j : ℤ))‖ :=
              norm_sub_le _ _
          _ ≤ 2 ^ 30 * C ^ 2 * ε ^ 10 + C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - a)) := by
              linarith [hA, h1']
    have hB2 : ‖(∑' j : ℕ, calcS ψ ε x (⌊b⌋ + 1 + (j : ℤ))) - QB‖
        ≤ 2 ^ 30 * C ^ 2 * ε ^ 10 + C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - b)) := by
      by_cases hQB' : b < (x : ℝ)
      · have hQB1 : QB = 1 := by rw [hQB]; simp only [hQB', if_true]
        rw [hQB1]
        have hxb : b < (x : ℝ) := hQB'
        have hId : (∑' j : ℕ, calcS ψ ε x (⌊b⌋ + 1 + (j : ℤ))) - 1
            = ((∑' y : ℤ, calcS ψ ε x y) - 1) - (∑' j : ℕ, calcS ψ ε x (⌊b⌋ - (j : ℤ))) := by
          rw [hFm]
          ring
        rw [hId]
        have h1 : ‖∑' j : ℕ, calcS ψ ε x (⌊b⌋ - (j : ℤ))‖
            ≤ C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - ((⌊b⌋ : ℤ) : ℝ))) :=
          norm_tsum_calcS_left hdecay hC0 hε0 hε1 ⌊b⌋ (by linarith [hxb, hfloor])
        have h2 : jbDecay 10 (ε * ((x : ℝ) - ((⌊b⌋ : ℤ) : ℝ))) ≤ jbDecay 10 (ε * ((x : ℝ) - b)) := by
          refine jbDecay_le_of_abs_le ?_
          rw [abs_mul, abs_mul, abs_of_pos hε0]
          refine mul_le_mul_of_nonneg_left ?_ hε0.le
          rw [abs_of_nonneg (by linarith [hxb] : 0 ≤ (x : ℝ) - b),
            abs_of_nonneg (by linarith [hxb] : 0 ≤ (x : ℝ) - ((⌊b⌋ : ℤ) : ℝ))]
          linarith [hfloor]
        have h1' : ‖∑' j : ℕ, calcS ψ ε x (⌊b⌋ - (j : ℤ))‖
            ≤ C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - b)) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (mul_nonneg hC0 (by norm_num)))
        calc ‖((∑' y : ℤ, calcS ψ ε x y) - 1) - (∑' j : ℕ, calcS ψ ε x (⌊b⌋ - (j : ℤ)))‖
            ≤ ‖(∑' y : ℤ, calcS ψ ε x y) - 1‖ + ‖∑' j : ℕ, calcS ψ ε x (⌊b⌋ - (j : ℤ))‖ :=
              norm_sub_le _ _
          _ ≤ 2 ^ 30 * C ^ 2 * ε ^ 10 + C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - b)) := by
              linarith [hA, h1']
      · have hQB0 : QB = 0 := by rw [hQB]; simp only [hQB', if_false]
        rw [hQB0, sub_zero]
        have hxb : (x : ℝ) ≤ b := not_lt.mp hQB'
        have hxfloor : (x : ℝ) ≤ ((⌊b⌋ : ℤ) : ℝ) + 1 := by linarith [hxb, hfloor']
        have hk : (x : ℝ) ≤ ((⌊b⌋ + 1 : ℤ) : ℝ) := by push_cast; linarith [hxfloor]
        have h1 : ‖∑' j : ℕ, calcS ψ ε x (⌊b⌋ + 1 + (j : ℤ))‖
            ≤ C * 2 ^ 60 * jbDecay 10 (ε * (((⌊b⌋ + 1 : ℤ) : ℝ) - (x : ℝ))) :=
          norm_tsum_calcS_right hdecay hC0 hε0 hε1 (⌊b⌋ + 1) hk
        have h2 : jbDecay 10 (ε * (((⌊b⌋ + 1 : ℤ) : ℝ) - (x : ℝ)))
            ≤ jbDecay 10 (ε * ((x : ℝ) - b)) := by
          refine jbDecay_le_of_abs_le ?_
          rw [abs_mul, abs_mul, abs_of_pos hε0]
          refine mul_le_mul_of_nonneg_left ?_ hε0.le
          rw [abs_of_nonpos (by linarith [hxb] : (x : ℝ) - b ≤ 0),
            abs_of_nonneg (by push_cast; linarith [hxfloor] : 0 ≤ (((⌊b⌋ + 1 : ℤ) : ℝ) - (x : ℝ)))]
          push_cast
          linarith [hfloor']
        calc ‖∑' j : ℕ, calcS ψ ε x (⌊b⌋ + 1 + (j : ℤ))‖
            ≤ C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - b)) :=
              h1.trans (mul_le_mul_of_nonneg_left h2 (mul_nonneg hC0 (by norm_num)))
          _ ≤ 2 ^ 30 * C ^ 2 * ε ^ 10 + C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - b)) := by
              have h3 : (0 : ℝ) ≤ 2 ^ 30 * C ^ 2 * ε ^ 10 := by positivity
              linarith [h3]
    calc ‖((∑' y : ℤ, calcS ψ ε x y) - 1)
            - ((∑' j : ℕ, calcS ψ ε x (⌈a⌉ - 1 - (j : ℤ))) - (1 - PA))
            - ((∑' j : ℕ, calcS ψ ε x (⌊b⌋ + 1 + (j : ℤ))) - QB)‖
        ≤ ‖((∑' y : ℤ, calcS ψ ε x y) - 1)
            - ((∑' j : ℕ, calcS ψ ε x (⌈a⌉ - 1 - (j : ℤ))) - (1 - PA))‖
          + ‖(∑' j : ℕ, calcS ψ ε x (⌊b⌋ + 1 + (j : ℤ))) - QB‖ := norm_sub_le _ _
      _ ≤ (‖(∑' y : ℤ, calcS ψ ε x y) - 1‖
            + ‖(∑' j : ℕ, calcS ψ ε x (⌈a⌉ - 1 - (j : ℤ))) - (1 - PA)‖)
          + ‖(∑' j : ℕ, calcS ψ ε x (⌊b⌋ + 1 + (j : ℤ))) - QB‖ := by
              have := norm_sub_le ((∑' y : ℤ, calcS ψ ε x y) - 1)
                ((∑' j : ℕ, calcS ψ ε x (⌈a⌉ - 1 - (j : ℤ))) - (1 - PA))
              linarith
      _ ≤ (2 ^ 30 * C ^ 2 * ε ^ 10
            + (2 ^ 30 * C ^ 2 * ε ^ 10 + C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - a))))
          + (2 ^ 30 * C ^ 2 * ε ^ 10 + C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - b))) := by
              linarith [hA, hB1, hB2]
      _ ≤ 2 ^ 60 * C ^ 2 * (ε ^ 10 + jbDecay 10 (ε * ((x : ℝ) - a))
            + jbDecay 10 (ε * ((x : ℝ) - b))) := by
              have hCsq : C ≤ C ^ 2 := by nlinarith [hC, sq_nonneg C]
              have h1 : (0 : ℝ) ≤ ε ^ 10 := by positivity
              have h2 : (0 : ℝ) ≤ jbDecay 10 (ε * ((x : ℝ) - a)) := jbDecay_nonneg 10 _
              have h3 : (0 : ℝ) ≤ jbDecay 10 (ε * ((x : ℝ) - b)) := jbDecay_nonneg 10 _
              have hC2 : (0 : ℝ) ≤ C ^ 2 := sq_nonneg C
              have e1 : 3 * (2 ^ 30 * C ^ 2 * ε ^ 10) ≤ 2 ^ 60 * C ^ 2 * ε ^ 10 := by
                have h30 : (3 : ℝ) * 2 ^ 30 ≤ 2 ^ 60 := by norm_num
                calc 3 * (2 ^ 30 * C ^ 2 * ε ^ 10) = ((3 : ℝ) * 2 ^ 30) * (C ^ 2 * ε ^ 10) := by ring
                  _ ≤ 2 ^ 60 * (C ^ 2 * ε ^ 10) := mul_le_mul_of_nonneg_right h30 (mul_nonneg hC2 h1)
                  _ = 2 ^ 60 * C ^ 2 * ε ^ 10 := by ring
              have e2 : C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - a)) ≤ C ^ 2 * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - a)) := by
                refine mul_le_mul_of_nonneg_right ?_ h2
                exact mul_le_mul_of_nonneg_right hCsq (by positivity)
              have e3 : C * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - b)) ≤ C ^ 2 * 2 ^ 60 * jbDecay 10 (ε * ((x : ℝ) - b)) := by
                refine mul_le_mul_of_nonneg_right ?_ h3
                exact mul_le_mul_of_nonneg_right hCsq (by positivity)
              linarith [e1, e2, e3]
  · -- the interval contains no integer strictly (empty sum, zero indicator)
    have hemp : Finset.Icc ⌈a⌉ ⌊b⌋ = ∅ := Finset.Icc_eq_empty hnm
    rw [hemp, Finset.sum_empty]
    have hind0 : ¬ (a ≤ (x : ℝ) ∧ (x : ℝ) ≤ b) := by
      rintro ⟨h1, h2⟩
      have h3 : ⌈a⌉ ≤ x := (Int.ceil_le).mpr h1
      have h4 : x ≤ ⌊b⌋ := (Int.le_floor).mpr h2
      omega
    rw [if_neg hind0]
    simp only [sub_zero, norm_zero]
    have h1 : (0 : ℝ) ≤ ε ^ 10 := by positivity
    have h2 : (0 : ℝ) ≤ jbDecay 10 (ε * ((x : ℝ) - a)) := jbDecay_nonneg 10 _
    have h3 : (0 : ℝ) ≤ jbDecay 10 (ε * ((x : ℝ) - b)) := jbDecay_nonneg 10 _
    have h4 : (0 : ℝ) ≤ C ^ 2 := sq_nonneg C
    positivity

end Work.Analysis.InverseTheory
