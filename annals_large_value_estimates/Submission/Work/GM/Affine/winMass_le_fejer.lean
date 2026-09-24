import Mathlib
import Submission.Work.GM.Affine.WinMass_fejer_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.WinMass_ge_hprof

/-!
# The Fejér majorant for `WinMass` (`WINMASS_ROUTE.md`, L0 + L2)

`WinMass f M₂ M₃ = M₃ · Σ_ℓ ∫_{Iwin M₃ ℓ} ‖Bsum f M₂‖²` (`WinMass_eq_window_sum`), where
`Iwin M₃ ℓ = [ℓ - 2/M₃, ℓ + 2/M₃]`.  The Fejér kernel `fejerK M₃` of order
`fejerN M₃ = max 1 ⌊M₃/8⌋`

* is non-negative everywhere (`fejerK_nonneg`), and
* is `≥ M₃/64` on every window `Iwin M₃ ℓ` when `M₃ ≥ 8` (`fejerK_ge_on_window`).

Consequently, at every point `x`, `M₃ · (Σ_{ℓ∈s} 1_{Iwin M₃ ℓ}(x)) ≤ 64 · fejerK M₃ x`
(`M₃_mul_ind_le_fejer`), and integrating against `‖Bsum f M₂‖² ≥ 0` gives the result.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-! ## Elementary trigonometric sums -/

/-- Reindexing `∑_{k=1}^{n} f k = ∑_{j<n} f (j+1)`. -/
lemma sum_Icc_one_eq_sum_range (n : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 n, f k) = ∑ j ∈ Finset.range n, f (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Finset.sum_range_succ]

/-- The reflection `j ↦ N - j` of `range N` for the cosine sum. -/
lemma sum_cos_reflect (N : ℕ) (x : ℝ) :
    (∑ j ∈ Finset.range N, Real.cos (2 * Real.pi * ((N : ℝ) - (j : ℝ)) * x))
      = ∑ j ∈ Finset.range N, Real.cos (2 * Real.pi * ((j : ℝ) + 1) * x) := by
  have h := Finset.sum_range_reflect (fun m : ℕ => Real.cos (2 * Real.pi * ((m : ℝ) + 1) * x)) N
  rw [← h]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  have this : ((N - 1 - j : ℕ) : ℝ) + 1 = (N : ℝ) - (j : ℝ) := by
    rw [Nat.cast_sub (by omega : j ≤ N - 1), Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
    ring
  rw [this]

/-- The Fejér kernel is the squared modulus of a Dirichlet sum (in real form):
`N + 2∑_{k<N}(N-(k+1))cos(2π(k+1)x) = (∑_{j<N}cos(2πjx))² + (∑_{j<N}sin(2πjx))²`. -/
lemma fejer_range_identity (N : ℕ) (x : ℝ) :
    (N : ℝ) + 2 * (∑ k ∈ Finset.range N,
        ((N : ℝ) - ((k : ℝ) + 1)) * Real.cos (2 * Real.pi * ((k : ℝ) + 1) * x))
      = (∑ j ∈ Finset.range N, Real.cos (2 * Real.pi * (j : ℝ) * x)) ^ 2
        + (∑ j ∈ Finset.range N, Real.sin (2 * Real.pi * (j : ℝ) * x)) ^ 2 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    push_cast
    have hterm : ((↑n : ℝ) + 1 - ((↑n : ℝ) + 1)) * Real.cos (2 * Real.pi * ((↑n : ℝ) + 1) * x) = 0 := by
      ring
    rw [hterm, add_zero]
    have hsum : (∑ x_1 ∈ Finset.range n, (↑n + 1 - (↑x_1 + 1)) * Real.cos (2 * Real.pi * (↑x_1 + 1) * x))
        = (∑ x_1 ∈ Finset.range n, (↑n - (↑x_1 + 1)) * Real.cos (2 * Real.pi * (↑x_1 + 1) * x))
          + (∑ x_1 ∈ Finset.range n, Real.cos (2 * Real.pi * (↑x_1 + 1) * x)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      ring_nf
    rw [hsum]
    have hR : ((∑ j ∈ Finset.range n, Real.cos (2 * Real.pi * (↑j : ℝ) * x))
          + Real.cos (2 * Real.pi * (↑n : ℝ) * x)) ^ 2
        + ((∑ j ∈ Finset.range n, Real.sin (2 * Real.pi * (↑j : ℝ) * x))
          + Real.sin (2 * Real.pi * (↑n : ℝ) * x)) ^ 2
        = (∑ j ∈ Finset.range n, Real.cos (2 * Real.pi * (↑j : ℝ) * x)) ^ 2
          + (∑ j ∈ Finset.range n, Real.sin (2 * Real.pi * (↑j : ℝ) * x)) ^ 2
          + 2 * (∑ j ∈ Finset.range n, Real.cos (2 * Real.pi * ((↑n : ℝ) - (↑j : ℝ)) * x)) + 1 := by
      have h1 : Real.cos (2 * Real.pi * (↑n : ℝ) * x) ^ 2
          + Real.sin (2 * Real.pi * (↑n : ℝ) * x) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
      have key : (∑ j ∈ Finset.range n, Real.cos (2 * Real.pi * (↑j : ℝ) * x))
            * Real.cos (2 * Real.pi * (↑n : ℝ) * x)
          + (∑ j ∈ Finset.range n, Real.sin (2 * Real.pi * (↑j : ℝ) * x))
            * Real.sin (2 * Real.pi * (↑n : ℝ) * x)
          = ∑ j ∈ Finset.range n, Real.cos (2 * Real.pi * ((↑n : ℝ) - (↑j : ℝ)) * x) := by
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [show 2 * Real.pi * ((↑n : ℝ) - (↑j : ℝ)) * x
              = 2 * Real.pi * (↑n : ℝ) * x - 2 * Real.pi * (↑j : ℝ) * x from by ring,
          Real.cos_sub]
        ring
      nlinarith [h1, key]
    rw [hR]
    rw [sum_cos_reflect]
    linarith [ih]

/-- `fejerN M₃`-form of `fejer_range_identity`, expressed with the `Icc`-sum used in `fejerK`. -/
lemma fejer_Icc_eq_range (N : ℕ) (hN : 1 ≤ N) (x : ℝ) :
    (N : ℝ) + 2 * (∑ k ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - (k : ℝ)) * Real.cos (2 * Real.pi * (k : ℝ) * x))
      = (∑ j ∈ Finset.range N, Real.cos (2 * Real.pi * (j : ℝ) * x)) ^ 2
        + (∑ j ∈ Finset.range N, Real.sin (2 * Real.pi * (j : ℝ) * x)) ^ 2 := by
  have h1 := sum_Icc_one_eq_sum_range (N - 1)
    (fun k => ((N : ℝ) - (k : ℝ)) * Real.cos (2 * Real.pi * (k : ℝ) * x))
  have hg0 : ((N : ℝ) - (((N - 1 : ℕ) : ℝ) + 1))
      * Real.cos (2 * Real.pi * (((N - 1 : ℕ) : ℝ) + 1) * x) = 0 := by
    have hcast : (((N - 1 : ℕ) : ℝ)) + 1 = (N : ℝ) := by
      rw [Nat.cast_sub hN]; norm_num
    rw [hcast]; ring
  have h3 : (∑ j ∈ Finset.range N, ((N : ℝ) - ((j : ℝ) + 1)) * Real.cos (2 * Real.pi * ((j : ℝ) + 1) * x))
      = (∑ j ∈ Finset.range (N - 1),
          ((N : ℝ) - ((j : ℝ) + 1)) * Real.cos (2 * Real.pi * ((j : ℝ) + 1) * x)) := by
    have hNr : Finset.range (N - 1 + 1) = Finset.range N := by rw [Nat.sub_add_cancel hN]
    rw [← hNr, Finset.sum_range_succ]
    rw [show ((N : ℝ) - (((N - 1 : ℕ) : ℝ) + 1))
        * Real.cos (2 * Real.pi * (((N - 1 : ℕ) : ℝ) + 1) * x) = 0 from hg0, add_zero]
  rw [h1]; push_cast
  rw [← h3]
  exact fejer_range_identity N x

/-- `fejerN M₃ * fejerK M₃ x` written as an `Icc`-sum with coefficients `N - k`. -/
lemma fejerN_mul_fejerK (M₃ x : ℝ) :
    (fejerN M₃ : ℝ) * fejerK M₃ x
      = (fejerN M₃ : ℝ) + 2 * (∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1),
          ((fejerN M₃ : ℝ) - (k : ℝ)) * Real.cos (2 * Real.pi * (k : ℝ) * x)) := by
  have hN : (fejerN M₃ : ℝ) ≠ 0 := by
    have h := one_le_fejerN M₃; linarith
  unfold fejerK
  rw [mul_add, mul_one]
  congr 1
  rw [show (fejerN M₃ : ℝ) * (2 * ∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1),
        (1 - (k : ℝ) / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x))
      = 2 * ((fejerN M₃ : ℝ) * ∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1),
        (1 - (k : ℝ) / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)) from by ring]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  field_simp

/-- The Fejér kernel is non-negative. -/
theorem fejerK_nonneg (M₃ x : ℝ) : 0 ≤ fejerK M₃ x := by
  have hNpos : (0:ℝ) < (fejerN M₃ : ℝ) := by
    have h := one_le_fejerN M₃; linarith
  have hkey := fejerN_mul_fejerK M₃ x
  have hid := fejer_Icc_eq_range (fejerN M₃) (fejerN_pos M₃) x
  have hsq : 0 ≤ (fejerN M₃ : ℝ) * fejerK M₃ x := by
    rw [hkey, hid]
    nlinarith [sq_nonneg (∑ j ∈ Finset.range (fejerN M₃), Real.cos (2 * Real.pi * (j : ℝ) * x)),
               sq_nonneg (∑ j ∈ Finset.range (fejerN M₃), Real.sin (2 * Real.pi * (j : ℝ) * x))]
  exact (mul_nonneg_iff_of_pos_left hNpos).mp hsq

/-- For `M₃ < 8` the kernel is identically `1`. -/
lemma fejerK_eq_one_of_lt_eight {M₃ x : ℝ} (h : M₃ < 8) : fejerK M₃ x = 1 := by
  unfold fejerK fejerN
  have h1 : ⌊M₃ / 8⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
  rw [h1]
  simp

/-- The Fejér kernel is continuous. -/
lemma continuous_fejerK (M₃ : ℝ) : Continuous (fejerK M₃) := by
  unfold fejerK
  refine continuous_const.add (continuous_const.mul ?_)
  refine continuous_finsetSum _ (fun k _ => ?_)
  refine continuous_const.mul (Real.continuous_cos.comp ?_)
  fun_prop

/-! ## The lower bound for the kernel on the windows -/

/-- `∑_{j<N} j² ≤ N³/3`. -/
lemma sum_range_sq_le (N : ℕ) : (∑ j ∈ Finset.range N, ((j:ℝ))^2) ≤ (N:ℝ)^3/3 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    push_cast
    nlinarith [ih, hn]

/-- If `y² ≤ 1/(16N²)` then the cosine sum `∑_{j<N}cos(2πjy)` is at least `N/2`. -/
lemma cos_sum_lower {N : ℕ} (hN1 : 1 ≤ N) {y : ℝ} (hy : y^2 ≤ 1/(16*(N:ℝ)^2)) :
    (N:ℝ)/2 ≤ ∑ j ∈ Finset.range N, Real.cos (2*Real.pi*(j:ℝ)*y) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  have h1 : (∑ j ∈ Finset.range N, (1 - (2*Real.pi*(j:ℝ)*y)^2/2))
      ≤ ∑ j ∈ Finset.range N, Real.cos (2*Real.pi*(j:ℝ)*y) :=
    Finset.sum_le_sum (fun j _ => Real.one_sub_sq_div_two_le_cos)
  have h2 : (∑ j ∈ Finset.range N, (1 - (2*Real.pi*(j:ℝ)*y)^2/2))
      = (N:ℝ) - 2*Real.pi^2 * y^2 * (∑ j ∈ Finset.range N, ((j:ℝ))^2) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_); ring
  have hpi2 : Real.pi^2 ≤ 12 := by
    have h := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  have h4 : y^2 * (N:ℝ)^2 ≤ 1/16 := by
    have hpos : (0:ℝ) < 16*(N:ℝ)^2 := by positivity
    have h := hy
    rw [le_div_iff₀ hpos] at h
    nlinarith [h]
  have h3 : 2*Real.pi^2 * y^2 * (∑ j ∈ Finset.range N, ((j:ℝ))^2) ≤ (N:ℝ)/2 := by
    have hsq := sum_range_sq_le N
    have hnn : 0 ≤ 2*Real.pi^2 * y^2 := by positivity
    have step1 : 2*Real.pi^2 * y^2 * (∑ j ∈ Finset.range N, ((j:ℝ))^2)
        ≤ 2*Real.pi^2 * y^2 * ((N:ℝ)^3/3) := mul_le_mul_of_nonneg_left hsq hnn
    have step2 : 2*Real.pi^2 * y^2 * ((N:ℝ)^3/3) = (2*Real.pi^2*(N:ℝ)/3) * (y^2*(N:ℝ)^2) := by ring
    have step3 : (2*Real.pi^2*(N:ℝ)/3) * (y^2*(N:ℝ)^2) ≤ (2*Real.pi^2*(N:ℝ)/3) * (1/16) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have step4 : (2*Real.pi^2*(N:ℝ)/3) * (1/16) ≤ (N:ℝ)/2 := by nlinarith [hpi2, hNpos]
    linarith [step1, step3, step4]
  linarith [h1, h2, h3]

/-- For `M₃ ≥ 8`, `fejerN M₃ = ⌊M₃/8⌋₊`. -/
lemma floor_fejerN {M₃ : ℝ} (hM₃ : 8 ≤ M₃) :
    (fejerN M₃ : ℝ) = (⌊M₃/8⌋₊ : ℝ) := by
  unfold fejerN
  rw [max_eq_right]
  exact Nat.le_floor (by push_cast; linarith)

/-- The kernel is `≥ M₃/64` on every window `Iwin M₃ ℓ` (`M₃ ≥ 8`). -/
theorem fejerK_ge_on_window {M₃ : ℝ} (hM₃ : 8 ≤ M₃) (ℓ : ℤ) {x : ℝ}
    (hx : x ∈ Iwin M₃ ℓ) : M₃ / 64 ≤ fejerK M₃ x := by
  have hM₃pos : 0 < M₃ := by linarith
  have hN1 : 1 ≤ fejerN M₃ := fejerN_pos M₃
  have hNpos : (0:ℝ) < (fejerN M₃ : ℝ) := by exact_mod_cast hN1
  have hNge : M₃/16 ≤ (fejerN M₃ : ℝ) := by
    have hfloor := floor_fejerN hM₃
    have h1 : (1:ℝ) ≤ (fejerN M₃ : ℝ) := one_le_fejerN M₃
    have h2 : M₃/8 < (fejerN M₃ : ℝ) + 1 := by
      rw [hfloor]
      have := Nat.lt_floor_add_one (M₃/8)
      linarith
    linarith
  have hNle : (fejerN M₃ : ℝ) ≤ M₃/8 := by
    rw [floor_fejerN hM₃]
    have := Nat.floor_le (a := M₃/8) (by linarith : (0:ℝ) ≤ M₃/8)
    linarith
  have hkey : (fejerN M₃ : ℝ) * fejerK M₃ x
      = (∑ j ∈ Finset.range (fejerN M₃), Real.cos (2*Real.pi*(j:ℝ)*x))^2
        + (∑ j ∈ Finset.range (fejerN M₃), Real.sin (2*Real.pi*(j:ℝ)*x))^2 := by
    rw [fejerN_mul_fejerK M₃ x, fejer_Icc_eq_range (fejerN M₃) hN1 x]
  set y : ℝ := x - (ℓ:ℝ) with hydef
  have hyabs : |y| ≤ 2/M₃ := by rw [hydef]; exact mem_Iwin.mp hx
  have hy1 : 2/M₃ ≤ 1/(4*(fejerN M₃ : ℝ)) := by
    have h4N : (0:ℝ) < 4*(fejerN M₃ : ℝ) := by positivity
    rw [div_le_iff₀ hM₃pos, div_mul_eq_mul_div, le_div_iff₀ h4N]
    linarith [hNle]
  have hy2 : y^2 ≤ 1/(16*(fejerN M₃ : ℝ)^2) := by
    have hy20 : |y| ≤ 1/(4*(fejerN M₃ : ℝ)) := le_trans hyabs hy1
    have hc : (0:ℝ) ≤ 1/(4*(fejerN M₃ : ℝ)) := by positivity
    have h : |y|^2 ≤ (1/(4*(fejerN M₃ : ℝ)))^2 := pow_le_pow_left₀ (abs_nonneg y) hy20 2
    rw [sq_abs] at h
    have : (1/(4*(fejerN M₃ : ℝ)))^2 = 1/(16*(fejerN M₃ : ℝ)^2) := by ring
    rwa [this] at h
  have hcs : ∀ j : ℕ, Real.cos (2*Real.pi*(j:ℝ)*x) = Real.cos (2*Real.pi*(j:ℝ)*y) := by
    intro j
    have harg : 2*Real.pi*(j:ℝ)*x
        = (2*Real.pi*(j:ℝ)*y) + ((((j:ℤ) * ℓ : ℤ) : ℝ) * (2*Real.pi)) := by
      rw [hydef]; push_cast; ring
    rw [harg, Real.cos_add_int_mul_two_pi]
  have hA : (fejerN M₃ : ℝ)/2 ≤ ∑ j ∈ Finset.range (fejerN M₃), Real.cos (2*Real.pi*(j:ℝ)*x) := by
    rw [Finset.sum_congr rfl (fun j _ => hcs j)]
    exact cos_sum_lower hN1 hy2
  have hBnn : 0 ≤ (∑ j ∈ Finset.range (fejerN M₃), Real.sin (2*Real.pi*(j:ℝ)*x))^2 := sq_nonneg _
  have hfejer : fejerK M₃ x = ((∑ j ∈ Finset.range (fejerN M₃), Real.cos (2*Real.pi*(j:ℝ)*x))^2
        + (∑ j ∈ Finset.range (fejerN M₃), Real.sin (2*Real.pi*(j:ℝ)*x))^2) / (fejerN M₃ : ℝ) := by
    rw [eq_div_iff (ne_of_gt hNpos), mul_comm]
    exact hkey
  rw [hfejer, le_div_iff₀ hNpos]
  nlinarith [hA, hBnn, hNge, hNpos]

/-! ## The pointwise domination by the kernel -/

/-- For `M₃ ≥ 8` the windows are disjoint, so each point lies in at most one of them. -/
lemma ind_sum_Iwin_le_one {M₃ : ℝ} (hM₃ : 8 ≤ M₃) (s : Finset ℤ) (x : ℝ) :
    (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x) ≤ 1 := by
  classical
  set T : Finset ℤ := s.filter (fun ℓ => x ∈ Iwin M₃ ℓ) with hT
  have h1 : (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x) = (T.card : ℝ) := by
    rw [show (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x)
        = ∑ ℓ ∈ s, (if x ∈ Iwin M₃ ℓ then (1:ℝ) else 0) from by
      refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      rw [Set.indicator_apply]]
    rw [Finset.sum_boole, hT]
  rw [h1]
  have hcard : T.card ≤ 1 := by
    refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
    rw [hT, Finset.mem_filter] at ha hb
    have ha' : |x - (a:ℝ)| ≤ 2/M₃ := mem_Iwin.mp ha.2
    have hb' : |x - (b:ℝ)| ≤ 2/M₃ := mem_Iwin.mp hb.2
    have h2M : 4/M₃ ≤ 1/2 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < M₃)]
      linarith
    have hsub : |(a:ℝ) - (b:ℝ)| ≤ 4/M₃ := by
      have h := abs_sub_le (a:ℝ) x (b:ℝ)
      have h1 : |(a:ℝ) - x| ≤ 2/M₃ := by rw [abs_sub_comm]; exact ha'
      have h2 : |(a:ℝ) - (b:ℝ)| ≤ 2/M₃ + 2/M₃ := by linarith
      have h3 : (2:ℝ)/M₃ + 2/M₃ = 4/M₃ := by ring
      linarith [h2, le_of_eq h3]
    have hsub2 : |(a:ℝ) - (b:ℝ)| ≤ 1/2 := le_trans hsub h2M
    have hreal : ((|a - b| : ℤ) : ℝ) ≤ 1/2 := by
      rw [Int.cast_abs]
      rw [show ((a - b : ℤ) : ℝ) = (a:ℝ) - (b:ℝ) from by push_cast; ring]
      exact hsub2
    have hzero : (|a - b| : ℤ) = 0 := by
      have hlt : ((|a - b| : ℤ) : ℝ) < 1 := lt_of_le_of_lt hreal (by norm_num)
      have hlt' : (|a - b| : ℤ) < 1 := by exact_mod_cast hlt
      have hnn : (0:ℤ) ≤ |a - b| := abs_nonneg _
      omega
    have : a - b = 0 := abs_eq_zero.mp hzero
    omega
  exact_mod_cast hcard

/-- Pointwise domination: `M₃ · Σ_{ℓ∈s} 1_{Iwin M₃ ℓ}(x) ≤ 64 · fejerK M₃ x`. -/
lemma M₃_mul_ind_le_fejer {M₃ : ℝ} (hM₃ : 1 ≤ M₃) (s : Finset ℤ) (x : ℝ) :
    M₃ * (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x) ≤ 64 * fejerK M₃ x := by
  have hM₃pos : (0:ℝ) < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  by_cases h8 : 8 ≤ M₃
  · by_cases hx : ∃ ℓ ∈ s, x ∈ Iwin M₃ ℓ
    · obtain ⟨ℓ, hℓs, hℓx⟩ := hx
      have hle : (∑ ℓ' ∈ s, (Iwin M₃ ℓ').indicator (fun _ => (1:ℝ)) x) ≤ 1 :=
        ind_sum_Iwin_le_one h8 s x
      have h1 : M₃ * (∑ ℓ' ∈ s, (Iwin M₃ ℓ').indicator (fun _ => (1:ℝ)) x) ≤ M₃ := by
        have := mul_le_mul_of_nonneg_left hle hM₃pos.le
        rwa [mul_one] at this
      have h2 := fejerK_ge_on_window h8 ℓ hℓx
      linarith
    · have hz : (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x) = 0 := by
        refine Finset.sum_eq_zero (fun ℓ hℓ => ?_)
        rw [Set.indicator_of_notMem]
        intro hmem
        exact hx ⟨ℓ, hℓ, hmem⟩
      rw [hz, mul_zero]
      have hnn := fejerK_nonneg M₃ x
      linarith
  · have h8' : M₃ < 8 := not_le.mp h8
    have hsum : (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x) ≤ 1 + 4/M₃ :=
      finset_sum_indicator_Iwin_le hM₃pos x s
    have hK : fejerK M₃ x = 1 := fejerK_eq_one_of_lt_eight h8'
    rw [hK]
    have h1 : M₃ * (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x) ≤ M₃ * (1 + 4/M₃) :=
      mul_le_mul_of_nonneg_left hsum hM₃pos.le
    have h2 : M₃ * (1 + 4/M₃) = M₃ + 4 := by field_simp
    linarith [h1, le_of_eq h2]

/-- The kernel is bounded by `2·fejerN M₃`. -/
lemma fejerK_abs_le (M₃ x : ℝ) : |fejerK M₃ x| ≤ 2 * (fejerN M₃ : ℝ) := by
  have hN1 : 1 ≤ fejerN M₃ := fejerN_pos M₃
  have hNpos : (0:ℝ) < (fejerN M₃ : ℝ) := by exact_mod_cast hN1
  have hkey : (fejerN M₃ : ℝ) * fejerK M₃ x
      = (∑ j ∈ Finset.range (fejerN M₃), Real.cos (2*Real.pi*(j:ℝ)*x))^2
        + (∑ j ∈ Finset.range (fejerN M₃), Real.sin (2*Real.pi*(j:ℝ)*x))^2 := by
    rw [fejerN_mul_fejerK M₃ x, fejer_Icc_eq_range (fejerN M₃) hN1 x]
  have hAnn : |∑ j ∈ Finset.range (fejerN M₃), Real.cos (2*Real.pi*(j:ℝ)*x)|
      ≤ (fejerN M₃ : ℝ) := by
    calc |∑ j ∈ Finset.range (fejerN M₃), Real.cos (2*Real.pi*(j:ℝ)*x)|
        ≤ ∑ j ∈ Finset.range (fejerN M₃), |Real.cos (2*Real.pi*(j:ℝ)*x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range (fejerN M₃), (1:ℝ) :=
          Finset.sum_le_sum (fun j _ => Real.abs_cos_le_one _)
      _ = (fejerN M₃ : ℝ) := by simp
  have hBnn : |∑ j ∈ Finset.range (fejerN M₃), Real.sin (2*Real.pi*(j:ℝ)*x)|
      ≤ (fejerN M₃ : ℝ) := by
    calc |∑ j ∈ Finset.range (fejerN M₃), Real.sin (2*Real.pi*(j:ℝ)*x)|
        ≤ ∑ j ∈ Finset.range (fejerN M₃), |Real.sin (2*Real.pi*(j:ℝ)*x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range (fejerN M₃), (1:ℝ) :=
          Finset.sum_le_sum (fun j _ => Real.abs_sin_le_one _)
      _ = (fejerN M₃ : ℝ) := by simp
  have hA2 : (∑ j ∈ Finset.range (fejerN M₃), Real.cos (2*Real.pi*(j:ℝ)*x))^2
      ≤ (fejerN M₃ : ℝ)^2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hAnn 2
  have hB2 : (∑ j ∈ Finset.range (fejerN M₃), Real.sin (2*Real.pi*(j:ℝ)*x))^2
      ≤ (fejerN M₃ : ℝ)^2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hBnn 2
  have hsq : (∑ j ∈ Finset.range (fejerN M₃), Real.cos (2*Real.pi*(j:ℝ)*x))^2
      + (∑ j ∈ Finset.range (fejerN M₃), Real.sin (2*Real.pi*(j:ℝ)*x))^2
      ≤ 2 * (fejerN M₃ : ℝ)^2 := by linarith
  have hfejer : fejerK M₃ x
      = ((∑ j ∈ Finset.range (fejerN M₃), Real.cos (2*Real.pi*(j:ℝ)*x))^2
        + (∑ j ∈ Finset.range (fejerN M₃), Real.sin (2*Real.pi*(j:ℝ)*x))^2)
        / (fejerN M₃ : ℝ) := by
    rw [eq_div_iff (ne_of_gt hNpos), mul_comm]
    exact hkey
  have hnn2 : 0 ≤ (∑ j ∈ Finset.range (fejerN M₃), Real.cos (2*Real.pi*(j:ℝ)*x))^2
      + (∑ j ∈ Finset.range (fejerN M₃), Real.sin (2*Real.pi*(j:ℝ)*x))^2 := by positivity
  rw [hfejer, abs_of_nonneg (div_nonneg hnn2 hNpos.le), div_le_iff₀ hNpos]
  nlinarith [hsq]

/-! ## The main theorem -/

theorem winMass_le_fejer {C₀ : ℝ} (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ M₂ : ℝ, 0 ≤ M₂ → ∀ M₃ : ℝ, 1 ≤ M₃ →
          WinMass f M₂ M₃ ≤ C * ∫ x : ℝ, ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x := by
  refine ⟨64, by norm_num, ?_⟩
  intro f hf hfnn hsup M₂ hM₂ M₃ hM₃
  have hM₃pos : (0:ℝ) < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  rcases eq_or_lt_of_le hM₂ with hM₂0 | hM₂pos
  · subst hM₂0
    have hR2 : R2 (0:ℝ) = ∅ := by unfold R2; simp [Nat.floor_zero]
    have hB : ∀ u : ℝ, Bsum f 0 u = 0 := by intro u; simp [Bsum, hR2]
    have hWM : WinMass f 0 M₃ = 0 := by
      simp [WinMass, Hfun_eq_Bsum, hB]
    have hz : (∫ x : ℝ, ‖Bsum f 0 x‖ ^ 2 * fejerK M₃ x) = 0 := by
      simp [hB]
    rw [hWM, hz]
    norm_num
  · set g : ℝ → ℝ := fun x => ‖Bsum f M₂ x‖ ^ 2 with hgdef
    have hgnn : ∀ x, 0 ≤ g x := fun x => sq_nonneg _
    -- integrability of `g`
    have hHcont : Continuous (Hprof f M₂) := Hprof_continuous hf M₂
    have hHcs : HasCompactSupport (Hprof f M₂) := Hprof_hasCompactSupport hsup hC₀ hM₂
    have hcontC : Continuous (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hHcont
    have hcsC : HasCompactSupport (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) :=
      hHcs.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)
    have hgint : Integrable g := by
      have h := integrable_fourier_sq_of_continuous_hasCompactSupport hcontC hcsC
      refine h.congr ?_
      filter_upwards with x
      show ‖FourierTransform.fourier (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) x‖ ^ 2 = g x
      rw [show FourierTransform.fourier (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ))
          = fun x => Fhat (Hprof f M₂) x from rfl]
      show ‖Fhat (Hprof f M₂) x‖ ^ 2 = ‖Bsum f M₂ x‖ ^ 2
      rw [Bsum_eq_Fhat_Hprof hf hsup hC₀ hM₂pos x]
    -- integrability of `fejerK M₃ * g`
    have hKint : Integrable (fun x => fejerK M₃ x * g x) :=
      hgint.bdd_mul (continuous_fejerK M₃).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs]; exact fejerK_abs_le M₃ x))
    -- `WinMass` is the `M₃`-multiple of the window sum of `g`
    have hWM : WinMass f M₂ M₃ = M₃ * ∑' ℓ : ℤ, ∫ x in Iwin M₃ ℓ, g x :=
      WinMass_eq_window_sum f hM₃pos
    -- finite window bounds
    have hfin : ∀ s : Finset ℤ,
        (∑ ℓ ∈ s, ∫ x in Iwin M₃ ℓ, g x) ≤ (64/M₃) * ∫ x, g x * fejerK M₃ x := by
      intro s
      have h1 : (∑ ℓ ∈ s, ∫ x in Iwin M₃ ℓ, g x)
          = ∫ x, g x * (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x) := by
        have hpt : ∀ ℓ ∈ s, (∫ x in Iwin M₃ ℓ, g x)
            = ∫ x, g x * (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x := by
          intro ℓ _
          rw [(MeasureTheory.integral_indicator (μ := (volume : Measure ℝ)) (f := g)
            (s := Iwin M₃ ℓ) measurableSet_Icc).symm]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          by_cases hx : x ∈ Iwin M₃ ℓ
          · simp only [Set.indicator_of_mem hx, mul_one]
          · simp only [Set.indicator_of_notMem hx, mul_zero]
        rw [Finset.sum_congr rfl hpt]
        rw [← MeasureTheory.integral_finsetSum]
        · refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          show (∑ i ∈ s, g x * (Iwin M₃ i).indicator (fun _ => (1:ℝ)) x)
              = g x * (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x)
          rw [Finset.mul_sum]
        · intro ℓ _
          refine (hgint.indicator (Iwin_measurable M₃ ℓ)).congr ?_
          filter_upwards with x
          by_cases hx : x ∈ Iwin M₃ ℓ
          · simp only [Set.indicator_of_mem hx, mul_one]
          · simp only [Set.indicator_of_notMem hx, mul_zero]
      have h2 : M₃ * (∫ x, g x * (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x))
          = ∫ x, (M₃ * (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x)) * g x := by
        rw [← MeasureTheory.integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        ring
      have h3 : (∫ x, (M₃ * (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x)) * g x)
          ≤ ∫ x, (64 * fejerK M₃ x) * g x := by
        refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => ?_))
          ?_ (Filter.Eventually.of_forall (fun x => ?_))
        · exact mul_nonneg (mul_nonneg hM₃pos.le
            (Finset.sum_nonneg (fun ℓ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x)))
            (hgnn x)
        · refine (hKint.const_mul 64).congr (Filter.Eventually.of_forall (fun x => ?_))
          ring
        · exact mul_le_mul_of_nonneg_right (M₃_mul_ind_le_fejer hM₃ s x) (hgnn x)
      have h4 : (∫ x, (64 * fejerK M₃ x) * g x) = 64 * ∫ x, g x * fejerK M₃ x := by
        rw [show (∫ x, (64 * fejerK M₃ x) * g x) = ∫ x, 64 * (fejerK M₃ x * g x) from
          integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))]
        rw [MeasureTheory.integral_const_mul]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        ring
      have hkey : M₃ * (∑ ℓ ∈ s, ∫ x in Iwin M₃ ℓ, g x) ≤ 64 * ∫ x, g x * fejerK M₃ x := by
        rw [h1, h2]
        exact h3.trans (le_of_eq h4)
      rw [show (64/M₃) * (∫ x, g x * fejerK M₃ x) = (64 * ∫ x, g x * fejerK M₃ x)/M₃ from by
        ring]
      rw [le_div_iff₀ hM₃pos]
      linarith [hkey]
    have hsumm : Summable (fun ℓ : ℤ => ∫ x in Iwin M₃ ℓ, g x) :=
      summable_of_sum_le (fun ℓ => integral_nonneg (fun x => hgnn x)) hfin
    have htsum : (∑' ℓ : ℤ, ∫ x in Iwin M₃ ℓ, g x) ≤ (64/M₃) * ∫ x, g x * fejerK M₃ x :=
      le_of_tendsto hsumm.hasSum (Filter.Eventually.of_forall hfin)
    rw [hWM]
    calc M₃ * (∑' ℓ : ℤ, ∫ x in Iwin M₃ ℓ, g x)
        ≤ M₃ * ((64/M₃) * ∫ x, g x * fejerK M₃ x) := mul_le_mul_of_nonneg_left htsum hM₃pos.le
      _ = 64 * (∫ x, g x * fejerK M₃ x) := by field_simp
      _ = 64 * (∫ x : ℝ, ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x) := by rw [hgdef]

end

end Work.GM.Affine
