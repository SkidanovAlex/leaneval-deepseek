import Mathlib
import Submission.Commons.Analysis.Complex.analyticAt_of_differentiableOn_closedBall
import Submission.Commons.Analysis.Calculus.iteratedDeriv_comp_smul_eq_iteratedFDeriv
import Submission.Commons.Analysis.Complex.kovrijkine_d

set_option maxHeartbeats 1000000

open Classical MeasureTheory Metric
open scoped BigOperators ENNReal

namespace Commons.Analysis.Fourier.LogvinenkoSereda

/-!
# The `d`-dimensional band-limited assembly (Logvinenko–Sereda, entire-function form)

Main result: `bandlimited_assembly_d2`, Cohen, *Fractal uncertainty in higher dimensions*,
Annals of Math. 202 (2025).
-/



section D2GridBoxes
/-!
## Auxiliary lemmas for the `d`-dimensional band-limited assembly

We work with `Fin d → ℝ` (identified with `EuclideanSpace ℝ (Fin d)` via `PiLp.toLp`, which is
measure preserving) and the grid of half-open boxes of side `2`
`xᵢ ∈ [2 nᵢ + γᵢ, 2 nᵢ + γᵢ + 2)`.
-/

/-- The half-open grid boxes of side `2` tile `ℝᵈ` and the integrals over them sum to the
full integral. -/
theorem d2_hasSum_setIntegral_gridBoxIco {d : ℕ} (γ : Fin d → ℝ) (g : (Fin d → ℝ) → ℝ)
    (hg : Integrable g) :
    HasSum (fun n : Fin d → ℤ => ∫ x in {x : Fin d → ℝ | ∀ i : Fin d,
        2 * (n i : ℝ) + γ i ≤ x i ∧ x i < 2 * (n i : ℝ) + γ i + 2}, g x) (∫ x, g x) := by
  set box : (Fin d → ℤ) → Set (Fin d → ℝ) := fun n =>
    Set.pi Set.univ (fun i : Fin d => Set.Ico (2 * (n i : ℝ) + γ i) (2 * (n i : ℝ) + γ i + 2))
    with hbox
  have hboxmem : ∀ (n : Fin d → ℤ) (x : Fin d → ℝ),
      x ∈ box n ↔ ∀ i : Fin d, 2 * (n i : ℝ) + γ i ≤ x i ∧ x i < 2 * (n i : ℝ) + γ i + 2 := by
    intro n x; rw [hbox]; exact ⟨fun h i => h i (Set.mem_univ i), fun h i _ => h i⟩
  have hmeas : ∀ n, MeasurableSet (box n) := by
    intro n
    rw [hbox]
    exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Ico)
  have hdisj : Pairwise (Function.onFun Disjoint box) := by
    intro n m hnm
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    rw [hboxmem] at hx hx'
    apply hnm
    funext i
    have h1 : 2 * (n i : ℝ) + γ i ≤ x i := (hx i).1
    have h2 : x i < 2 * (n i : ℝ) + γ i + 2 := (hx i).2
    have h3 : 2 * (m i : ℝ) + γ i ≤ x i := (hx' i).1
    have h4 : x i < 2 * (m i : ℝ) + γ i + 2 := (hx' i).2
    have hR : (n i : ℝ) = (m i : ℝ) := by
      by_contra hc
      rcases lt_or_gt_of_ne hc with h | h
      · have hZ : n i < m i := by exact_mod_cast h
        have hZ' : n i + 1 ≤ m i := Int.lt_iff_add_one_le.mp hZ
        have hR' : (n i : ℝ) + 1 ≤ (m i : ℝ) := by exact_mod_cast hZ'
        linarith
      · have hZ : m i < n i := by exact_mod_cast h
        have hZ' : m i + 1 ≤ n i := Int.lt_iff_add_one_le.mp hZ
        have hR' : (m i : ℝ) + 1 ≤ (n i : ℝ) := by exact_mod_cast hZ'
        linarith
    exact_mod_cast hR
  have hunion : (⋃ n, box n) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨fun i => ⌊(x i - γ i) / 2⌋, ?_⟩
    rw [hboxmem]
    intro i
    constructor
    · have h := Int.floor_le ((x i - γ i) / 2)
      linarith
    · have h := Int.lt_floor_add_one ((x i - γ i) / 2)
      linarith
  have h := MeasureTheory.hasSum_integral_iUnion hmeas hdisj
    (hg.integrableOn (s := ⋃ n, box n))
  rw [hunion, MeasureTheory.setIntegral_univ] at h
  have hset : ∀ n : Fin d → ℤ, box n = {x : Fin d → ℝ | ∀ i : Fin d,
      2 * (n i : ℝ) + γ i ≤ x i ∧ x i < 2 * (n i : ℝ) + γ i + 2} :=
    fun n => Set.ext (fun x => hboxmem n x)
  refine h.congr_fun (fun n => ?_)
  rw [hset n]

/-- Shorthand for the `L²` mass of `F` restricted to the real points of a box. -/
abbrev d2_upperBox {d : ℕ} (n : Fin d → ℤ) (γ : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x : Fin d → ℝ | ∀ i : Fin d, 2 * (n i : ℝ) + γ i ≤ x i ∧ x i < 2 * (n i : ℝ) + γ i + 2}

lemma d2_upperBox_eq {d : ℕ} (n : Fin d → ℤ) (γ : Fin d → ℝ) :
    d2_upperBox n γ = {x : Fin d → ℝ | ∀ i : Fin d,
      2 * (n i : ℝ) + γ i ≤ x i ∧ x i < 2 * (n i : ℝ) + γ i + 2} := rfl

lemma d2_upperBox_eq_pi {d : ℕ} (n : Fin d → ℤ) (γ : Fin d → ℝ) :
    d2_upperBox n γ = Set.pi Set.univ (fun i : Fin d =>
      Set.Ico (2 * (n i : ℝ) + γ i) (2 * (n i : ℝ) + γ i + 2)) := by
  ext x
  exact ⟨fun h i _ => h i, fun h i => h i (Set.mem_univ i)⟩

lemma d2_measurableSet_upperBox {d : ℕ} (n : Fin d → ℤ) (γ : Fin d → ℝ) :
    MeasurableSet (d2_upperBox n γ) := by
  rw [d2_upperBox_eq_pi]
  exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Ico)

/-- **Bad boxes carry at most half of the total mass.**  If the derivatives of `F` on the real
subspace satisfy the global Bernstein bounds `∫ ≤ (2πσ)^{2m} ∫ ‖F‖²`, then the boxes on which
some derivative fails the local "good" bound carry at most half of the total mass. -/
theorem d2_bad_boxes_mass_d {d : ℕ} (σ : ℝ) (hσ : 1 ≤ σ) (F : (Fin d → ℂ) → ℂ)
    (γ : Fin d → ℝ)
    (hint0 : Integrable (fun x : Fin d → ℝ => ‖F (fun i => (x i : ℂ))‖ ^ 2))
    (hintn : ∀ m : ℕ, 1 ≤ m → Integrable (fun x : Fin d → ℝ =>
      ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2))
    (hglob : ∀ m : ℕ, 1 ≤ m → (∫ x : Fin d → ℝ,
        ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2)
      ≤ (2*Real.pi*σ)^(2*m) * (∫ x : Fin d → ℝ, ‖F (fun i => (x i : ℂ))‖ ^ 2)) :
    (∑' n : Fin d → ℤ, if (∀ m : ℕ, 1 ≤ m → (∫ x in d2_upperBox n γ,
          ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2)
        ≤ (2*(3*2*Real.pi*σ)^m)^2 * (∫ x in d2_upperBox n γ,
          ‖F (fun i => (x i : ℂ))‖ ^ 2))
      then 0 else (∫ x in d2_upperBox n γ, ‖F (fun i => (x i : ℂ))‖ ^ 2))
      ≤ (1/2) * (∫ x : Fin d → ℝ, ‖F (fun i => (x i : ℂ))‖ ^ 2) := by
  classical
  let m : (Fin d → ℤ) → ℝ := fun n =>
    ∫ x in d2_upperBox n γ, ‖F (fun i => (x i : ℂ))‖ ^ 2
  let dd : ℕ → (Fin d → ℤ) → ℝ := fun k n =>
    ∫ x in d2_upperBox n γ, ‖iteratedFDeriv ℝ k F (fun i => (x i : ℂ))‖ ^ 2
  let T : ℝ := ∫ x : Fin d → ℝ, ‖F (fun i => (x i : ℂ))‖ ^ 2
  let c : ℕ → ℝ := fun k => (2*(3*2*Real.pi*σ)^k)^2
  change (∑' n : Fin d → ℤ, if (∀ k : ℕ, 1 ≤ k → dd k n ≤ c k * m n) then 0 else m n)
      ≤ (1/2) * T
  have hm0 : ∀ n, 0 ≤ m n := fun n => setIntegral_nonneg (d2_measurableSet_upperBox n γ)
    (fun x _ => by positivity)
  have hd0 : ∀ k, ∀ n, 0 ≤ dd k n := fun k n => setIntegral_nonneg (d2_measurableSet_upperBox n γ)
    (fun x _ => by positivity)
  have hT0 : 0 ≤ T := integral_nonneg (fun x => by positivity)
  have hmSumm : Summable m := by
    have h := d2_hasSum_setIntegral_gridBoxIco γ _ hint0
    have : m = fun n : Fin d → ℤ => ∫ x in {x : Fin d → ℝ | ∀ i : Fin d,
        2 * (n i : ℝ) + γ i ≤ x i ∧ x i < 2 * (n i : ℝ) + γ i + 2},
        ‖F (fun i => (x i : ℂ))‖ ^ 2 := rfl
    rw [this]; exact h.summable
  have hdSumm : ∀ k, 1 ≤ k → Summable (dd k) := by
    intro k hk
    have h := d2_hasSum_setIntegral_gridBoxIco γ _ (hintn k hk)
    have : dd k = fun n : Fin d → ℤ => ∫ x in {x : Fin d → ℝ | ∀ i : Fin d,
        2 * (n i : ℝ) + γ i ≤ x i ∧ x i < 2 * (n i : ℝ) + γ i + 2},
        ‖iteratedFDeriv ℝ k F (fun i => (x i : ℂ))‖ ^ 2 := rfl
    rw [this]; exact h.summable
  have hdTsum : ∀ k, 1 ≤ k → ∑' n : Fin d → ℤ, dd k n = ∫ x : Fin d → ℝ,
      ‖iteratedFDeriv ℝ k F (fun i => (x i : ℂ))‖ ^ 2 := by
    intro k hk
    have h := d2_hasSum_setIntegral_gridBoxIco γ _ (hintn k hk)
    have : dd k = fun n : Fin d → ℤ => ∫ x in {x : Fin d → ℝ | ∀ i : Fin d,
        2 * (n i : ℝ) + γ i ≤ x i ∧ x i < 2 * (n i : ℝ) + γ i + 2},
        ‖iteratedFDeriv ℝ k F (fun i => (x i : ℂ))‖ ^ 2 := rfl
    rw [this]; exact h.tsum_eq
  have hc_pos : ∀ k : ℕ, 0 < c k := by
    intro k; show 0 < (2*(3*2*Real.pi*σ)^k)^2
    have h : (0:ℝ) < 3*2*Real.pi*σ := by positivity
    positivity
  have hc_eq : ∀ k : ℕ, c k = 4 * 9^k * (2*Real.pi*σ)^(2*k) := by
    intro k
    have h1 : (3:ℝ)*2*Real.pi*σ = 3*(2*Real.pi*σ) := by ring
    have hpow : (3*2*Real.pi*σ)^k = (3:ℝ)^k * (2*Real.pi*σ)^k := by rw [h1, mul_pow]
    have hsq : (2 * ((3:ℝ)^k * (2*Real.pi*σ)^k))^2
        = 4 * ((3:ℝ)^k)^2 * ((2*Real.pi*σ)^k)^2 := by ring
    have hA : ((3:ℝ)^k)^2 = (3:ℝ)^(2*k) := by rw [← pow_mul]; rw [show k*2 = 2*k by omega]
    have hB : ((2*Real.pi*σ)^k)^2 = (2*Real.pi*σ)^(2*k) := by rw [← pow_mul]; rw [show k*2 = 2*k by omega]
    have h9 : (3:ℝ)^(2*k) = 9^k := by rw [show (9:ℝ) = 3^2 by norm_num, ← pow_mul]
    show (2*(3*2*Real.pi*σ)^k)^2 = 4*9^k*(2*Real.pi*σ)^(2*k)
    rw [hpow, hsq, hA, hB, h9]
  let B : ℕ → (Fin d → ℤ) → Prop := fun k n => 1 ≤ k ∧ c k * m n < dd k n
  let M : (Fin d → ℤ) → ℝ≥0∞ := fun n => ENNReal.ofReal (m n)
  have hpern : ∀ k : ℕ, (∑' n : Fin d → ℤ, (if B k n then M n else 0))
      ≤ ENNReal.ofReal (T / (4*9^k)) := by
    intro k
    by_cases hk : 1 ≤ k
    · have hden : 0 < 4*9^k*(2*Real.pi*σ)^(2*k) := by
        have hp : (0:ℝ) < 2*Real.pi*σ := by positivity
        positivity
      have hB0 : ∀ n, 0 ≤ (if B k n then m n else 0) := by
        intro n; by_cases hn : B k n
        · rw [if_pos hn]; exact hm0 n
        · rw [if_neg hn]
      have hBle : ∀ n, (if B k n then m n else 0) ≤ m n := by
        intro n; by_cases hn : B k n
        · rw [if_pos hn]
        · rw [if_neg hn]; exact hm0 n
      have hBs : Summable (fun n : Fin d → ℤ => (if B k n then m n else 0)) :=
        Summable.of_nonneg_of_le hB0 hBle hmSumm
      have hpt : ∀ n : Fin d → ℤ, (if B k n then m n else 0)
          ≤ dd k n / (4*9^k*(2*Real.pi*σ)^(2*k)) := by
        intro n
        by_cases hn : B k n
        · rw [if_pos hn]
          have hcm : c k * m n < dd k n := hn.2
          rw [hc_eq k] at hcm
          rw [le_div_iff₀ hden]
          exact le_of_lt (by rw [mul_comm]; exact hcm)
        · rw [if_neg hn]; exact div_nonneg (hd0 k n) hden.le
      have hRs : Summable (fun n : Fin d → ℤ => dd k n / (4*9^k*(2*Real.pi*σ)^(2*k))) := by
        have h2 := (hdSumm k hk).mul_right ((4*9^k*(2*Real.pi*σ)^(2*k))⁻¹)
        simpa only [div_eq_mul_inv] using h2
      have hBL : (∑' n : Fin d → ℤ, (if B k n then m n else 0)) ≤ T / (4*9^k) := by
        calc (∑' n : Fin d → ℤ, (if B k n then m n else 0))
            ≤ ∑' n : Fin d → ℤ, dd k n / (4*9^k*(2*Real.pi*σ)^(2*k)) :=
              Summable.tsum_le_tsum hpt hBs hRs
          _ = (∑' n : Fin d → ℤ, dd k n) * (4*9^k*(2*Real.pi*σ)^(2*k))⁻¹ := by
              rw [show (∑' n : Fin d → ℤ, dd k n / (4*9^k*(2*Real.pi*σ)^(2*k)))
                   = ∑' n : Fin d → ℤ, dd k n * (4*9^k*(2*Real.pi*σ)^(2*k))⁻¹ by
                    apply tsum_congr; intro n; rw [div_eq_mul_inv]]
              exact Summable.tsum_mul_right _ (hdSumm k hk)
          _ ≤ ((2*Real.pi*σ)^(2*k) * T) * (4*9^k*(2*Real.pi*σ)^(2*k))⁻¹ := by
              apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hden.le)
              rw [hdTsum k hk]; exact hglob k hk
          _ = T / (4*9^k) := by
              have h4 : (4:ℝ)*9^k ≠ 0 := by positivity
              have ha : (2*Real.pi*σ)^(2*k) ≠ 0 := by positivity
              rw [div_eq_mul_inv, mul_inv]
              field_simp
      have hMpt : ∀ n : Fin d → ℤ, ENNReal.ofReal (if B k n then m n else 0)
          = (if B k n then M n else 0) := by
        intro n; by_cases hn : B k n
        · rw [if_pos hn, if_pos hn]
        · rw [if_neg hn, if_neg hn]; exact ENNReal.ofReal_zero
      calc (∑' n : Fin d → ℤ, (if B k n then M n else 0))
          = ENNReal.ofReal (∑' n : Fin d → ℤ, (if B k n then m n else 0)) := by
            rw [ENNReal.ofReal_tsum_of_nonneg hB0 hBs]
            exact (tsum_congr hMpt).symm
        _ ≤ ENNReal.ofReal (T / (4*9^k)) := ENNReal.ofReal_le_ofReal hBL
    · have hzero : (∑' n : Fin d → ℤ, (if B k n then M n else 0)) = 0 := by
        have hh : ∀ n : Fin d → ℤ, (if B k n then M n else 0) = 0 := by
          intro n; by_cases hn : B k n
          · exact absurd hn.1 hk
          · rw [if_neg hn]
        rw [tsum_congr hh, tsum_zero]
      rw [hzero]; exact zero_le
  have h3 : (∑' k : ℕ, ENNReal.ofReal (T / (4*9^k))) = ENNReal.ofReal (9*T/32) := by
    have hnn : ∀ k : ℕ, 0 ≤ T / (4*9^k) := fun k => div_nonneg hT0 (by positivity)
    have heq : ∀ k : ℕ, T / (4*9^k) = (T/4) * (1/9:ℝ)^k := by
      intro k
      rw [show (1/9:ℝ) = 9⁻¹ by norm_num, inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
      ring
    have hsumm : Summable (fun k : ℕ => T / (4*9^k)) := by
      have h0 : Summable (fun k : ℕ => (T/4) * (1/9:ℝ)^k) :=
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (T/4)
      exact h0.congr (fun k => (heq k).symm)
    have hval : (∑' k : ℕ, T / (4*9^k)) = 9*T/32 := by
      rw [show (∑' k : ℕ, T / (4*9^k)) = ∑' k : ℕ, (T/4) * (1/9:ℝ)^k from tsum_congr heq]
      rw [Summable.tsum_mul_left (T/4) (summable_geometric_of_lt_one (by norm_num) (by norm_num)),
          tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
      ring
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsumm, hval]
  have h4 : ENNReal.ofReal (9*T/32) ≤ ENNReal.ofReal (T/2) := by
    apply ENNReal.ofReal_le_ofReal
    linarith [hT0]
  have hU : (∑' n : Fin d → ℤ, (if (∃ k, B k n) then M n else 0)) ≤ ENNReal.ofReal (T/2) := by
    have hU1 : (∑' n : Fin d → ℤ, (if (∃ k, B k n) then M n else 0))
        ≤ ∑' k : ℕ, ∑' n : Fin d → ℤ, (if B k n then M n else 0) := by
      rw [ENNReal.tsum_comm]
      refine ENNReal.tsum_le_tsum (fun n => ?_)
      by_cases h : ∃ k, B k n
      · rw [if_pos h]
        obtain ⟨k, hk⟩ := h
        calc M n = (if B k n then M n else 0) := (if_pos hk).symm
          _ ≤ ∑' a : ℕ, (if B a n then M n else 0) := ENNReal.le_tsum k
      · rw [if_neg h]; exact zero_le
    calc (∑' n : Fin d → ℤ, (if (∃ k, B k n) then M n else 0))
        ≤ ∑' k : ℕ, ∑' n : Fin d → ℤ, (if B k n then M n else 0) := hU1
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (T / (4*9^k)) := ENNReal.tsum_le_tsum hpern
      _ = ENNReal.ofReal (9*T/32) := h3
      _ ≤ ENNReal.ofReal (T/2) := h4
  have hLHS_eq : ENNReal.ofReal (∑' n : Fin d → ℤ,
        (if (¬ (∀ k : ℕ, 1 ≤ k → dd k n ≤ c k * m n)) then m n else 0))
      = ∑' n : Fin d → ℤ, (if (∃ k, B k n) then M n else 0) := by
    have hnn : ∀ n : Fin d → ℤ, 0 ≤ (if (¬ (∀ k : ℕ, 1 ≤ k → dd k n ≤ c k * m n)) then m n else 0) := by
      intro n; by_cases hn : (¬ (∀ k : ℕ, 1 ≤ k → dd k n ≤ c k * m n))
      · rw [if_pos hn]; exact hm0 n
      · rw [if_neg hn]
    have hle : ∀ n : Fin d → ℤ, (if (¬ (∀ k : ℕ, 1 ≤ k → dd k n ≤ c k * m n)) then m n else 0) ≤ m n := by
      intro n; by_cases hn : (¬ (∀ k : ℕ, 1 ≤ k → dd k n ≤ c k * m n))
      · rw [if_pos hn]
      · rw [if_neg hn]; exact hm0 n
    have hs : Summable (fun n : Fin d → ℤ => (if (¬ (∀ k : ℕ, 1 ≤ k → dd k n ≤ c k * m n)) then m n else 0)) :=
      Summable.of_nonneg_of_le hnn hle hmSumm
    have hiff : ∀ n : Fin d → ℤ, (¬ (∀ k : ℕ, 1 ≤ k → dd k n ≤ c k * m n)) ↔ (∃ k, B k n) := by
      intro n
      constructor
      · intro h
        push_neg at h
        obtain ⟨k, hk1, hk2⟩ := h
        exact ⟨k, hk1, hk2⟩
      · rintro ⟨k, hk1, hk2⟩ hc
        exact absurd (hc k hk1) (not_le.mpr hk2)
    have hpt : ∀ n : Fin d → ℤ, ENNReal.ofReal (if (¬ (∀ k : ℕ, 1 ≤ k → dd k n ≤ c k * m n)) then m n else 0)
        = (if (∃ k, B k n) then M n else 0) := by
      intro n
      by_cases hn : (∃ k, B k n)
      · rw [if_pos (hiff n |>.mpr hn), if_pos hn]
      · rw [if_neg (fun h => hn ((hiff n).mp h)), if_neg hn]; exact ENNReal.ofReal_zero
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hs]
    exact tsum_congr hpt
  have hmain : (∑' n : Fin d → ℤ, (if (∃ k, B k n) then M n else 0))
      ≤ ENNReal.ofReal ((1/2) * T) := by
    refine hU.trans ?_
    rw [show (1/2:ℝ) * T = T/2 by ring]
  have hfin : (∑' n : Fin d → ℤ,
        (if (¬ (∀ k : ℕ, 1 ≤ k → dd k n ≤ c k * m n)) then m n else 0)) ≤ (1/2) * T := by
    have h5 : ENNReal.ofReal (∑' n : Fin d → ℤ,
        (if (¬ (∀ k : ℕ, 1 ≤ k → dd k n ≤ c k * m n)) then m n else 0))
        ≤ ENNReal.ofReal ((1/2) * T) := by rw [hLHS_eq]; exact hmain
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith [hT0])).mp h5
  have hconv : (∑' n : Fin d → ℤ,
        (if (∀ k : ℕ, 1 ≤ k → dd k n ≤ c k * m n) then 0 else m n))
      = ∑' n : Fin d → ℤ,
        (if (¬ (∀ k : ℕ, 1 ≤ k → dd k n ≤ c k * m n)) then m n else 0) := by
    apply tsum_congr; intro n
    by_cases h : (∀ k : ℕ, 1 ≤ k → dd k n ≤ c k * m n)
    · rw [if_pos h, if_neg (fun hh => hh h)]
    · rw [if_neg h, if_pos h]
  rw [hconv]; exact hfin

/-- **Pointwise derivative bound on a good box.**  If the global Bernstein bounds
`∫ ‖Dᵐ F‖² ≤ (2πσ)^{2m} ∫ ‖F‖²` hold and on `Q` the derivatives satisfy the stronger good
bounds `∫_Q ‖Dᵐ F‖² ≤ (2 (3·2πσ)^m)² ∫_Q ‖F‖²` for all `m ≥ 1`, with `∫_Q ‖F‖² > 0`, then `Q`
contains a point `x₀` where all derivatives are pointwise bounded by
`2 (100·2πσ)^m √(∫_Q ‖F‖²)`. -/
theorem d2_exists_pointwise_deriv_bound_of_good {d : ℕ} (σ : ℝ) (hσ : 1 ≤ σ)
    (F : (Fin d → ℂ) → ℂ)
    (hint : ∀ m : ℕ, Integrable (fun x : Fin d → ℝ =>
      ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2))
    (hglob : ∀ m : ℕ, (∫ x : Fin d → ℝ,
        ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2)
      ≤ (2 * Real.pi * σ) ^ (2 * m) * (∫ x : Fin d → ℝ, ‖F (fun i => (x i : ℂ))‖ ^ 2))
    (Q : Set (Fin d → ℝ)) (hQmeas : MeasurableSet Q) (hQvol : 1 ≤ (volume Q).toReal)
    (hgood : ∀ m : ℕ, 1 ≤ m → (∫ x in Q,
        ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2)
      ≤ (2 * (3 * 2 * Real.pi * σ) ^ m) ^ 2 * (∫ x in Q, ‖F (fun i => (x i : ℂ))‖ ^ 2))
    (hQpos : 0 < ∫ x in Q, ‖F (fun i => (x i : ℂ))‖ ^ 2) :
    ∃ x0 ∈ Q, ∀ m : ℕ, ‖iteratedFDeriv ℝ m F (fun i => (x0 i : ℂ))‖
      ≤ 2 * (1000 * 2 * Real.pi * σ) ^ m
        * Real.sqrt (∫ x in Q, ‖F (fun i => (x i : ℂ))‖ ^ 2) := by
  classical
  by_contra hcon
  push_neg at hcon
  set M : ℝ := ∫ x in Q, ‖F (fun i => (x i : ℂ))‖ ^ 2 with hMdef
  have hMpos : 0 < M := hQpos
  set base : ℝ := 1000 * 2 * Real.pi * σ with hbasedef
  have hbasepos : 0 < base := by rw [hbasedef]; positivity
  set Φ : (Fin d → ℝ) → ℝ≥0∞ := fun x =>
    ∑' m : ℕ, ENNReal.ofReal ((base ^ (2 * m))⁻¹ *
      ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) with hΦdef
  have hlow : ∀ (x : Fin d → ℝ) (m : ℕ),
      2 * base ^ m * Real.sqrt M < ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ →
      4 * M < (base ^ (2 * m))⁻¹ * ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2 := by
    intro x m hm
    have hsq : 4 * (base ^ (2 * m)) * M < ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2 := by
      have hs : (2 * base ^ m * Real.sqrt M) ^ 2 = 4 * (base ^ (2*m)) * M := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hMpos.le]
        have : (base ^ m) ^ 2 = base ^ (2*m) := by rw [← pow_mul]; congr 1; omega
        rw [this]; ring
      have h2 : 0 ≤ 2 * base ^ m * Real.sqrt M := by positivity
      have := pow_lt_pow_left₀ hm h2 (by norm_num : (2:ℕ) ≠ 0)
      rwa [hs] at this
    have h4 : (base ^ (2*m))⁻¹ * (4 * (base ^ (2*m)) * M)
        < (base ^ (2*m))⁻¹ * ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2 :=
      mul_lt_mul_of_pos_left hsq (by positivity)
    have h5 : (base ^ (2*m))⁻¹ * (4 * (base ^ (2*m)) * M) = 4 * M := by
      field_simp
    linarith [h4, h5.le, h5.ge]
  have hpt : ∀ x ∈ Q, ENNReal.ofReal (4 * M) ≤ Φ x := by
    intro x hx
    obtain ⟨m, hm⟩ := hcon x hx
    have h4M := hlow x m hm
    have hterm : ENNReal.ofReal (4 * M) < ENNReal.ofReal ((base ^ (2 * m))⁻¹ *
        ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr h4M
    calc ENNReal.ofReal (4 * M) ≤ ENNReal.ofReal ((base ^ (2 * m))⁻¹ *
          ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) := le_of_lt hterm
      _ ≤ Φ x := by
          rw [hΦdef]
          exact ENNReal.le_tsum m
  have hA_meas : ∀ m : ℕ, AEMeasurable (fun x : Fin d → ℝ =>
      ENNReal.ofReal ((base ^ (2 * m))⁻¹ *
        ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2)) (volume.restrict Q) := by
    intro m
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (((hint m).aestronglyMeasurable.restrict).const_mul _).aemeasurable
  have hΦlin : ∫⁻ x in Q, Φ x = ∑' m : ℕ, ENNReal.ofReal ((base ^ (2*m))⁻¹ *
      (∫ x in Q, ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2)) := by
    rw [hΦdef, lintegral_tsum hA_meas]
    apply tsum_congr; intro m
    have hfi : Integrable (fun x : Fin d → ℝ =>
        (base ^ (2*m))⁻¹ * ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2)
        (volume.restrict Q) := ((hint m).restrict).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall (fun x => by positivity))]
    congr 1
    rw [integral_const_mul]
  have hterm_le : ∀ m : ℕ, ENNReal.ofReal ((base ^ (2*m))⁻¹ *
      (∫ x in Q, ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2))
      ≤ ENNReal.ofReal ((if m = 0 then 1 else (4 : ℝ) * (3/1000) ^ (2*m)) * M) := by
    intro m
    apply ENNReal.ofReal_le_ofReal
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      rw [hMdef]
      simp only [Nat.mul_zero, pow_zero, inv_one, one_mul]
      rw [if_pos trivial, one_mul]
      apply le_of_eq
      apply setIntegral_congr_fun hQmeas
      intro x _
      simp
    · simp only [if_neg (Nat.pos_iff_ne_zero.mp hmpos)]
      have hgb' : (∫ x in Q, ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2)
          ≤ (2 * (3 * 2 * Real.pi * σ) ^ m) ^ 2 * M := by
        rw [hMdef]; exact hgood m hmpos
      have hb : base = (1000:ℝ) * (2*Real.pi*σ) := by rw [hbasedef]; ring
      calc (base ^ (2*m))⁻¹ * (∫ x in Q, ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2)
          ≤ (base ^ (2*m))⁻¹ * ((2 * (3 * 2 * Real.pi * σ) ^ m) ^ 2 * M) :=
            mul_le_mul_of_nonneg_left hgb' (by positivity)
        _ = (4 * (3/1000) ^ (2*m)) * M := by
            rw [hb]
            have h1 : (2 * (3 * (2 * Real.pi * σ)) ^ m) ^ 2
                = 4 * 3^(2*m) * (2*Real.pi*σ)^(2*m) := by
              rw [mul_pow, ← pow_mul]
              rw [show (3 * (2*Real.pi*σ)) ^ (m*2) = 3^(m*2) * (2*Real.pi*σ)^(m*2) by rw [mul_pow]]
              rw [show m*2 = 2*m by omega]
              ring
            have h2 : ((1000:ℝ) * (2*Real.pi*σ)) ^ (2*m)
                = 1000^(2*m) * (2*Real.pi*σ)^(2*m) := by rw [mul_pow]
            have h3 : (3/1000 : ℝ)^(2*m) = 3^(2*m)/1000^(2*m) := by rw [div_pow]
            rw [show (3 * 2 * Real.pi * σ) = 3 * (2*Real.pi*σ) by ring]
            rw [h1, h2, h3]
            have h100 : (1000:ℝ)^(2*m) ≠ 0 := by positivity
            have hp : (2*Real.pi*σ)^(2*m) ≠ 0 := by positivity
            field_simp
  have hw_bound : ∀ m : ℕ, (if m = 0 then (1:ℝ) else 4 * (3/1000) ^ (2*m)) ≤ (1/2 : ℝ)^m := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; simp only [if_pos, pow_zero]; norm_num
    · simp only [if_neg (Nat.pos_iff_ne_zero.mp hmpos)]
      have he : (3/1000 : ℝ) ^ (2*m) = ((3/1000)^2)^m := pow_mul (3/1000) 2 m
      rw [he]
      have h2 : ((3/1000:ℝ)^2) = 9/1000000 := by norm_num
      rw [h2]
      -- 4 * (9/10^6)^m ≤ (1/2)^m  <=>  4 * 18^m ≤ 10^(6m)
      have hpow : (9/1000000 : ℝ)^m = 9^m / 1000000^m := by rw [div_pow]
      rw [hpow]
      rw [div_pow, show (1000000:ℝ) = 10^6 by norm_num, ← pow_mul]
      have h18 : (4:ℝ) * (18:ℝ)^m ≤ (10:ℝ)^(6*m) := by
        have h72 : (72:ℝ)^m ≤ (10:ℝ)^(6*m) := by
          rw [show (10:ℝ)^(6*m) = (10^6)^m by rw [pow_mul]]
          exact pow_le_pow_left₀ (by norm_num) (by norm_num) m
        have h4 : (4:ℝ) * (18:ℝ)^m ≤ (72:ℝ)^m := by
          rw [show (72:ℝ) = 4*18 by norm_num, mul_pow]
          have : (4:ℝ) ≤ (4:ℝ)^m := le_self_pow₀ (by norm_num) (Nat.pos_iff_ne_zero.mp hmpos)
          nlinarith [pow_pos (by norm_num : (0:ℝ) < 18) m]
        linarith
      rw [one_pow, ← mul_div_assoc]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hgoal : (4:ℝ) * 9^m * 2^m = 4 * 18^m := by
        rw [show (4:ℝ) * 9^m * 2^m = 4 * (9^m * 2^m) by ring,
          show (9:ℝ)^m * 2^m = 18^m by rw [← mul_pow]; norm_num]
      rw [hgoal]
      linarith [h18]
  have hsumm_f : Summable (fun m : ℕ => (if m = 0 then (1:ℝ) else 4 * (3/1000) ^ (2*m))) :=
    Summable.of_nonneg_of_le
      (fun m => by
        by_cases hm : m = 0
        · rw [if_pos hm]; norm_num
        · rw [if_neg hm]; positivity)
      (fun m => hw_bound m)
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1))
  have hsumm_half : Summable (fun m : ℕ => (1/2:ℝ) ^ m) :=
    summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
  have hsumm_bound : Summable (fun m : ℕ => (if m = 0 then (1:ℝ) else 4 * (3/1000) ^ (2*m)) * M) :=
    hsumm_f.mul_right M
  have hupper : ∫⁻ x in Q, Φ x ≤ ENNReal.ofReal (2 * M) := by
    have hmid : (∑' m : ℕ, ENNReal.ofReal ((if m = 0 then (1:ℝ) else 4 * (3/1000) ^ (2*m)) * M))
        = ENNReal.ofReal (∑' m : ℕ, (if m = 0 then (1:ℝ) else 4 * (3/1000) ^ (2*m)) * M) := by
      rw [ENNReal.ofReal_tsum_of_nonneg]
      · intro m; by_cases hm : m = 0
        · rw [if_pos hm]; positivity
        · rw [if_neg hm]; positivity
      · exact hsumm_bound
    have hsum_val : (∑' m : ℕ, (if m = 0 then (1:ℝ) else 4 * (3/1000) ^ (2*m)) * M)
        ≤ (∑' m : ℕ, (1/2:ℝ) ^ m) * M := by
      rw [Summable.tsum_mul_right M hsumm_f]
      exact mul_le_mul_of_nonneg_right
        (Summable.tsum_le_tsum (fun m => hw_bound m) hsumm_f hsumm_half) hMpos.le
    have hval : (∑' m : ℕ, (1/2:ℝ) ^ m) = 2 := by
      rw [tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)]
      norm_num
    rw [hΦlin]
    calc ∑' m : ℕ, ENNReal.ofReal ((base ^ (2*m))⁻¹ *
          (∫ x in Q, ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2))
        ≤ ∑' m : ℕ, ENNReal.ofReal ((if m = 0 then (1:ℝ) else 4 * (3/1000) ^ (2*m)) * M) :=
          ENNReal.tsum_le_tsum hterm_le
      _ = ENNReal.ofReal (∑' m : ℕ, (if m = 0 then (1:ℝ) else 4 * (3/1000) ^ (2*m)) * M) := hmid
      _ ≤ ENNReal.ofReal (2 * M) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hval] at hsum_val
          linarith
  have hvol1 : (1 : ℝ≥0∞) ≤ volume Q := by
    by_cases hQ : volume Q = ⊤
    · simp [hQ]
    · rw [← ENNReal.ofReal_toReal hQ, show (1:ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mpr hQvol
  have hlower : ENNReal.ofReal (4 * M) ≤ ∫⁻ x in Q, Φ x := by
    calc ENNReal.ofReal (4 * M) = ENNReal.ofReal (4 * M) * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal (4 * M) * volume Q := by
          exact mul_le_mul_of_nonneg_left hvol1 (by positivity)
      _ = ∫⁻ _x in Q, ENNReal.ofReal (4 * M) := by
          rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ x in Q, Φ x :=
          lintegral_mono_ae ((ae_restrict_mem hQmeas).mono (fun x hx => hpt x hx))
  have hfin : ENNReal.ofReal (4 * M) ≤ ENNReal.ofReal (2 * M) := hlower.trans hupper
  have := (ENNReal.ofReal_le_ofReal_iff (by linarith [hMpos] : (0:ℝ) ≤ 2 * M)).mp hfin
  linarith [hMpos]


/-- Chain rule for the `n`-th derivative of `t ↦ F (x₀ + t • W)`. -/
lemma d2_iteratedDeriv_comp_affine {d : ℕ} (F : (Fin d → ℂ) → ℂ)
    (hF : AnalyticOnNhd ℂ F Set.univ) (x0 W : Fin d → ℂ) (n : ℕ) :
    iteratedDeriv n (fun t : ℂ => F (x0 + t • W)) 0
      = iteratedFDeriv ℝ n F x0 (fun _ => W) := by
  have hcont : ContDiff ℂ (n : ℕ∞) F := hF.contDiff
  have hshift : ContDiff ℂ (n : ℕ∞) (fun w : Fin d → ℂ => F (x0 + w)) :=
    hcont.comp (by fun_prop)
  have h1 := Commons.Analysis.Calculus.iteratedDeriv_comp_smul_eq_iteratedFDeriv
    (fun w : Fin d → ℂ => F (x0 + w)) W hshift
  have htrans : iteratedFDeriv ℂ n (fun w : Fin d → ℂ => F (x0 + w)) 0
      = iteratedFDeriv ℂ n F x0 := by
    have h := iteratedFDeriv_comp_add_right (𝕜 := ℂ) (n := n) (a := x0)
      (x := (0 : Fin d → ℂ)) (f := F)
    simp only [zero_add] at h
    convert h using 2
    ext w; ring
  rw [htrans] at h1
  have hcta : ContDiffAt ℂ (n : ℕ∞) F x0 := hcont.contDiffAt
  have hrestrict := hcta.restrictScalars_iteratedFDeriv (𝕜 := ℝ)
  have hval : iteratedFDeriv ℂ n F x0 (fun _ => W) = iteratedFDeriv ℝ n F x0 (fun _ => W) := by
    have h2 := congrArg (fun T => T (fun _ => W)) hrestrict
    simpa using h2
  rwa [hval] at h1

/-- **Entire functions with pointwise derivative bounds at `x₀` are bounded by `c e^{B‖W‖}`.**
This is the several-variable Taylor expansion at `x₀` together with the bound on the
coefficients. -/
theorem d2_norm_le_exp_of_iteratedFDeriv_bound {d : ℕ} (F : (Fin d → ℂ) → ℂ)
    (hF : AnalyticOnNhd ℂ F Set.univ) (x0 : Fin d → ℂ) (c B : ℝ) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (h : ∀ m : ℕ, ‖iteratedFDeriv ℝ m F x0‖ ≤ c * B ^ m) :
    ∀ W : Fin d → ℂ, ‖F (x0 + W)‖ ≤ c * Real.exp (B * ‖W‖) := by
  intro W
  set G : ℂ → ℂ := fun t => F (x0 + t • W) with hGdef
  have hGdiff : Differentiable ℂ G := by
    have hFdiff : Differentiable ℂ F := fun z => (hF z (Set.mem_univ z)).differentiableAt
    rw [hGdef]
    exact hFdiff.comp (by fun_prop)
  have hG1 : G 1 = F (x0 + W) := by simp [hGdef]
  have hT := Complex.hasSum_taylorSeries_of_entire hGdiff (0 : ℂ) (1 : ℂ)
  have hcoeff : ∀ m : ℕ,
      ‖((m.factorial : ℂ))⁻¹ • (1 - 0 : ℂ) ^ m • iteratedDeriv m G 0‖
        ≤ c * ((B * ‖W‖) ^ m / m.factorial) := by
    intro m
    have hb : ‖iteratedDeriv m G 0‖ ≤ c * B ^ m * ‖W‖ ^ m := by
      rw [d2_iteratedDeriv_comp_affine F hF x0 W m]
      calc ‖iteratedFDeriv ℝ m F x0 (fun _ => W)‖
          ≤ ‖iteratedFDeriv ℝ m F x0‖ * ∏ _ : Fin m, ‖W‖ :=
            ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖iteratedFDeriv ℝ m F x0‖ * ‖W‖ ^ m := by simp
        _ ≤ (c * B ^ m) * ‖W‖ ^ m := by
            apply mul_le_mul_of_nonneg_right (h m) (by positivity)
        _ = c * B ^ m * ‖W‖ ^ m := by ring
    simp only [sub_zero, one_pow, norm_smul, norm_inv, Complex.norm_natCast, norm_one, one_mul]
    have hfac : (0:ℝ) < m.factorial := by positivity
    calc (m.factorial : ℝ)⁻¹ * ‖iteratedDeriv m G 0‖
        ≤ (m.factorial : ℝ)⁻¹ * (c * B ^ m * ‖W‖ ^ m) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = c * ((B * ‖W‖) ^ m / m.factorial) := by
          rw [mul_pow, div_eq_mul_inv]; ring
  have hg : HasSum (fun m : ℕ => c * ((B * ‖W‖) ^ m / m.factorial))
      (c * Real.exp (B * ‖W‖)) := by
    have hexp0 : HasSum (fun m : ℕ => (B * ‖W‖)^m / m.factorial)
        (Real.exp (B * ‖W‖)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp _
    simpa using hexp0.mul_left c
  have hbound := hT.norm_le_of_bounded hg hcoeff
  rw [hG1] at hbound
  exact hbound


open MeasureTheory Metric
open scoped ENNReal
end D2GridBoxes

section D2LocalEstimates
theorem d2_volume_unit_cube {m : ℕ} :
    volume {z : Fin m → ℝ | ∀ i, 0 ≤ z i ∧ z i ≤ 1} = 1 := by
  have hset : {z : Fin m → ℝ | ∀ i, 0 ≤ z i ∧ z i ≤ 1}
      = Set.pi Set.univ (fun i : Fin m => Set.Icc (0:ℝ) 1) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  rw [hset, volume_pi, Measure.pi_pi]
  simp [Real.volume_Icc]

theorem d2_volume_image_affine_diag {m : ℕ} (c : Fin m → ℝ) (p : Fin m → ℝ) (A : Set (Fin m → ℝ)) :
    volume ((fun z : Fin m → ℝ => fun i => p i + c i * z i) '' A)
      = ENNReal.ofReal (∏ i, |c i|) * volume A := by
  have hfun : (fun z : Fin m → ℝ => fun i => c i * z i)
      = (Matrix.toLin' (Matrix.diagonal c) : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) := by
    funext z i
    rw [Matrix.toLin'_apply]
    simp [Matrix.diagonal, Matrix.mulVec, dotProduct]
  have hdiag : volume ((fun z : Fin m → ℝ => fun i => c i * z i) '' A)
      = ENNReal.ofReal (∏ i, |c i|) * volume A := by
    rw [hfun, Measure.addHaar_image_linearMap volume _ A,
      show LinearMap.det (Matrix.toLin' (Matrix.diagonal c) : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
        = ∏ i, c i from by rw [LinearMap.det_toLin', Matrix.det_diagonal]]
    rw [← Finset.abs_prod]
  set S : Set (Fin m → ℝ) := (fun z : Fin m → ℝ => fun i => c i * z i) '' A with hS
  have himg : volume ((fun y : Fin m → ℝ => p + y) '' S) = volume S := by
    have h2 : (fun y : Fin m → ℝ => p + y) '' S = (fun y : Fin m → ℝ => y + (-p)) ⁻¹' S := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩; simpa using hx
      · intro hy; exact ⟨y - p, hy, by simp⟩
    rw [h2]
    exact MeasureTheory.measure_preimage_add_right volume (-p) S
  have hcomp : (fun z : Fin m → ℝ => fun i => p i + c i * z i)
      = (fun y : Fin m → ℝ => p + y) ∘ (fun z : Fin m → ℝ => fun i => c i * z i) := by
    funext z i; simp [Pi.add_apply]
  rw [hcomp, Set.image_comp, himg, hdiag]

theorem d2_box_cover {m : ℕ} (L p : Fin m → ℝ) (hLp : ∀ i, L i ≤ p i) (hpR : ∀ i, p i ≤ L i + 2)
    (x : Fin m → ℝ) (hx : ∀ i, L i ≤ x i ∧ x i ≤ L i + 2) :
    ∃ (ε : Fin m → Bool) (z : Fin m → ℝ), (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧
      (∀ i, x i = p i + (if ε i then L i + 2 - p i else L i - p i) * z i) := by
  classical
  refine ⟨fun i => decide (p i ≤ x i),
    fun i => if p i ≤ x i then (x i - p i) / (L i + 2 - p i) else (x i - p i) / (L i - p i),
    ?_, ?_⟩
  · intro i
    beta_reduce
    have h1 := (hx i).1
    have h2 := (hx i).2
    by_cases h : p i ≤ x i
    · rw [if_pos h]
      have hc : 0 ≤ L i + 2 - p i := by linarith
      refine ⟨div_nonneg (by linarith) hc, ?_⟩
      rcases eq_or_lt_of_le hc with hc0 | hcpos
      · rw [← hc0, div_zero]; norm_num
      · exact (div_le_one hcpos).mpr (by linarith)
    · rw [if_neg h]
      push_neg at h
      have hc : L i - p i ≤ 0 := by linarith
      refine ⟨div_nonneg_iff.mpr (Or.inr ⟨by linarith, hc⟩), ?_⟩
      rcases eq_or_lt_of_le hc with hc0 | hcneg
      · rw [hc0, div_zero]; norm_num
      · exact (div_le_one_of_neg hcneg).mpr (by linarith)
  · intro i
    beta_reduce
    have h1 := (hx i).1
    have h2 := (hx i).2
    by_cases h : p i ≤ x i
    · rw [if_pos h, if_pos (decide_eq_true_iff.mpr h)]
      have hc : 0 ≤ L i + 2 - p i := by linarith
      rcases eq_or_lt_of_le hc with hc0 | hcpos
      · have hxi : x i = p i := by linarith
        rw [← hc0, div_zero, zero_mul, add_zero]; exact hxi
      · rw [mul_div_cancel₀ _ (ne_of_gt hcpos)]; ring
    · rw [if_neg h, if_neg (fun hh => h (decide_eq_true_iff.mp hh))]
      push_neg at h
      have hc : L i - p i < 0 := by linarith
      rw [mul_div_cancel₀ _ (ne_of_lt hc)]; ring

theorem d2_mul_rpow_extract {K b a : ℝ} (hK0 : 0 < K) (hb : 0 < b) (ha : 0 < a) {e : ℝ} (he : 0 < e)
    (h : 1 ≤ (K / b) ^ e * a) : b ≤ K * a ^ (1 / e) := by
  have h1 : (b / K) ^ e * (K / b) ^ e = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have h2 : (b / K) * (K / b) = 1 := by field_simp
    rw [h2, Real.one_rpow]
  have h2 : (b / K) ^ e ≤ a := by
    have hbK : (0:ℝ) ≤ (b/K)^e := Real.rpow_nonneg (by positivity) _
    calc (b / K) ^ e = (b/K)^e * 1 := by ring
      _ ≤ (b/K)^e * ((K/b)^e * a) := mul_le_mul_of_nonneg_left h hbK
      _ = ((b/K)^e * (K/b)^e) * a := by ring
      _ = a := by rw [h1, one_mul]
  have h3 : b / K ≤ a ^ (1 / e) := by
    have h4 := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ b/K) e) h2
      (by positivity : (0:ℝ) ≤ 1/e)
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ b/K), mul_one_div, div_self (ne_of_gt he),
      Real.rpow_one] at h4
    exact h4
  rw [div_le_iff₀ hK0] at h3
  linarith

/-- Kovrijkine's lemma at the origin, in `Fin d → ℝ` coordinates for the set. -/
theorem d2_kovrijkine_at_zero {d : ℕ} (K : ℝ)
    (hKov : ∀ (F : (Fin d → ℂ) → ℂ) (M a : ℝ), 1 ≤ M → 0 ≤ a → Differentiable ℂ F →
      (∀ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 4) → ‖F z‖ ≤ M) → 1 ≤ ‖F 0‖ →
      ∀ (E : Set (EuclideanSpace ℝ (Fin d))), MeasurableSet E →
        E ⊆ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} →
        0 < (volume E).toReal → (∀ x ∈ E, ‖F (fun i => (x i : ℂ))‖ ≤ a) →
        ∀ x ∈ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1},
          ‖F (fun i => (x i : ℂ))‖ ≤ (K / (volume E).toReal) ^ (K * Real.log M) * a)
    (Ψ : (Fin d → ℂ) → ℂ) (M a : ℝ) (hM : 1 ≤ M) (ha : 0 ≤ a)
    (hΨ : Differentiable ℂ Ψ)
    (hb : ∀ w : Fin d → ℂ, (∀ i, ‖w i‖ ≤ 4) → ‖Ψ w‖ ≤ M) (h0 : 1 ≤ ‖Ψ 0‖)
    (B : Set (Fin d → ℝ)) (hBmeas : MeasurableSet B)
    (hBsub : B ⊆ {z : Fin d → ℝ | ∀ i, 0 ≤ z i ∧ z i ≤ 1})
    (hBpos : 0 < (volume B).toReal)
    (haB : ∀ z ∈ B, ‖Ψ (fun i => (z i : ℂ))‖ ≤ a) :
    ‖Ψ 0‖ ≤ (K / (volume B).toReal) ^ (K * Real.log M) * a := by
  set E : Set (EuclideanSpace ℝ (Fin d)) := (fun x : EuclideanSpace ℝ (Fin d) => x.ofLp) ⁻¹' B with hE
  have hEmeas : MeasurableSet E := hBmeas.preimage (by fun_prop)
  have hEsub : E ⊆ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := by
    intro x hx i
    have h1 := hBsub hx i
    simpa using h1
  have hEvol : volume E = volume B := by
    have hmp : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin d) => x.ofLp) volume volume := by
      simpa using (PiLp.volume_preserving_ofLp (Fin d))
    rw [hE]
    exact hmp.measure_preimage hBmeas.nullMeasurableSet
  have hEpos : 0 < (volume E).toReal := by rw [hEvol]; exact hBpos
  have haE : ∀ x ∈ E, ‖Ψ (fun i => (x i : ℂ))‖ ≤ a := by
    intro x hx
    have h1 := haB x.ofLp hx
    simpa using h1
  have hconcl := hKov Ψ M a hM ha hΨ hb h0 E hEmeas hEsub hEpos haE
  have h0mem : (0 : EuclideanSpace ℝ (Fin d)) ∈
      {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := fun i => by simp
  have hx := hconcl 0 h0mem
  rw [hEvol] at hx
  have harg : (fun i : Fin d => ((0 : EuclideanSpace ℝ (Fin d)) i : ℂ)) = 0 := by
    ext j; simp
  rw [harg] at hx
  exact hx

/-- **Sublevel estimate.** -/
theorem d2_sublevel_bound {d : ℕ} (K : ℝ) (hK1 : 1 ≤ K)
    (hKov : ∀ (F : (Fin d → ℂ) → ℂ) (M a : ℝ), 1 ≤ M → 0 ≤ a → Differentiable ℂ F →
      (∀ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 4) → ‖F z‖ ≤ M) → 1 ≤ ‖F 0‖ →
      ∀ (E : Set (EuclideanSpace ℝ (Fin d))), MeasurableSet E →
        E ⊆ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} →
        0 < (volume E).toReal → (∀ x ∈ E, ‖F (fun i => (x i : ℂ))‖ ≤ a) →
        ∀ x ∈ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1},
          ‖F (fun i => (x i : ℂ))‖ ≤ (K / (volume E).toReal) ^ (K * Real.log M) * a)
    (F : (Fin d → ℂ) → ℂ) (hF : Differentiable ℂ F)
    (L p : Fin d → ℝ) (hLp : ∀ i, L i ≤ p i) (hpR : ∀ i, p i ≤ L i + 2)
    (μ M t : ℝ) (hμpos : 0 < μ) (hμval : ‖F (fun i => (p i : ℂ))‖ = μ)
    (hM : 1 ≤ M)
    (hMb : ∀ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 8) → ‖F ((fun i => (p i : ℂ)) + z)‖ ≤ μ * M)
    (ht : 0 < t) (htμ : t < μ) :
    (volume {x : Fin d → ℝ | (∀ i, L i ≤ x i ∧ x i ≤ L i + 2) ∧
        ‖F (fun i => (x i : ℂ))‖ ≤ t}).toReal
      ≤ 4 ^ d * K * (t / μ) ^ (1 / (K * Real.log M)) := by
  classical
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  set A : Set (Fin d → ℝ) :=
    {x | (∀ i, L i ≤ x i ∧ x i ≤ L i + 2) ∧ ‖F (fun i => (x i : ℂ))‖ ≤ t} with hA
  have hboxmeas : MeasurableSet {x : Fin d → ℝ | ∀ i, L i ≤ x i ∧ x i ≤ L i + 2} := by
    have h : {x : Fin d → ℝ | ∀ i, L i ≤ x i ∧ x i ≤ L i + 2}
        = Set.pi Set.univ (fun i : Fin d => Set.Icc (L i) (L i + 2)) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    rw [h]
    exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc)
  have hAmeas : MeasurableSet A := by
    rw [hA, Set.setOf_and]
    refine hboxmeas.inter ?_
    exact (isClosed_le (continuous_norm.comp (hF.continuous.comp (by fun_prop)))
      continuous_const).measurableSet
  set cf : (Fin d → Bool) → Fin d → ℝ :=
    fun ε i => if ε i then L i + 2 - p i else L i - p i with hcf
  have hcf2 : ∀ (ε : Fin d → Bool) (i : Fin d), |cf ε i| ≤ 2 := by
    intro ε i
    by_cases h : ε i = true
    · have h1 : cf ε i = L i + 2 - p i := by simp [hcf, h]
      rw [h1, abs_of_nonneg (by linarith [hpR i])]
      linarith [hLp i]
    · have h1 : cf ε i = L i - p i := by simp [hcf, h]
      rw [h1, abs_of_nonpos (by linarith [hLp i])]
      linarith [hpR i]
  set S : (Fin d → Bool) → Set (Fin d → ℝ) :=
    fun ε => (fun z : Fin d → ℝ => fun i => p i + cf ε i * z i) ''
      {z | ∀ i, 0 ≤ z i ∧ z i ≤ 1} with hS
  set B : (Fin d → Bool) → Set (Fin d → ℝ) :=
    fun ε => {z | (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ (fun i => p i + cf ε i * z i) ∈ A} with hB
  have hcover : A ⊆ ⋃ ε : Fin d → Bool, A ∩ S ε := by
    rintro x ⟨hx, hxt⟩
    obtain ⟨ε, z, hz, hxz⟩ := d2_box_cover L p hLp hpR x hx
    refine Set.mem_iUnion.mpr ⟨ε, ⟨⟨hx, hxt⟩, z, hz, ?_⟩⟩
    ext i
    simp only [hcf]
    exact (hxz i).symm
  have hSfin : ∀ ε, volume (S ε) ≠ ⊤ := by
    intro ε
    have h : volume (S ε) = ENNReal.ofReal (∏ i, |cf ε i|) *
        volume {z : Fin d → ℝ | ∀ i, 0 ≤ z i ∧ z i ≤ 1} := by
      rw [hS]; exact d2_volume_image_affine_diag (cf ε) p _
    rw [h, d2_volume_unit_cube, mul_one]
    exact ENNReal.ofReal_ne_top
  have hfin : ∀ ε, volume (A ∩ S ε) ≠ ⊤ :=
    fun ε => ne_top_of_le_ne_top (hSfin ε) (measure_mono Set.inter_subset_right)
  have h1 : volume A ≤ ∑ ε : Fin d → Bool, volume (A ∩ S ε) := by
    calc volume A ≤ volume (⋃ ε : Fin d → Bool, A ∩ S ε) := measure_mono hcover
      _ ≤ ∑ ε : Fin d → Bool, volume (A ∩ S ε) := by
          rw [show (⋃ ε : Fin d → Bool, A ∩ S ε)
              = ⋃ ε ∈ (Finset.univ : Finset (Fin d → Bool)), A ∩ S ε from by simp]
          exact measure_biUnion_finset_le _ _
  have h3 : ∀ ε, (volume (A ∩ S ε)).toReal
      ≤ 2 ^ d * (K * (t / μ) ^ (1 / (K * Real.log M))) := by
    intro ε
    have hscale : volume (A ∩ S ε) = ENNReal.ofReal (∏ i, |cf ε i|) * volume (B ε) := by
      rw [hS, hB]
      have heq : A ∩ (fun z : Fin d → ℝ => fun i => p i + cf ε i * z i) ''
            {z | ∀ i, 0 ≤ z i ∧ z i ≤ 1}
          = (fun z : Fin d → ℝ => fun i => p i + cf ε i * z i) ''
            {z | (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ (fun i => p i + cf ε i * z i) ∈ A} := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq]
        constructor
        · rintro ⟨hyA, z, hz, rfl⟩; exact ⟨z, ⟨hz, hyA⟩, rfl⟩
        · rintro ⟨z, ⟨hz, hzA⟩, rfl⟩; exact ⟨hzA, z, hz, rfl⟩
      rw [heq, d2_volume_image_affine_diag]
    have hBsub : B ε ⊆ {z : Fin d → ℝ | ∀ i, 0 ≤ z i ∧ z i ≤ 1} := fun z hz => hz.1
    have hBmeas : MeasurableSet (B ε) := by
      have hset : B ε = {z : Fin d → ℝ | ∀ i, 0 ≤ z i ∧ z i ≤ 1} ∩
          {z : Fin d → ℝ | (fun i => p i + cf ε i * z i) ∈ A} := by
        rw [hB]
        ext z; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      rw [hset]
      refine MeasurableSet.inter ?_ ?_
      · have h : {z : Fin d → ℝ | ∀ i, 0 ≤ z i ∧ z i ≤ 1}
            = Set.pi Set.univ (fun i : Fin d => Set.Icc (0:ℝ) 1) := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
        rw [h]
        exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc)
      · exact hAmeas.preimage (by fun_prop)
    have hBle : (volume (B ε)).toReal ≤ K * (t / μ) ^ (1 / (K * Real.log M)) := by
      by_cases hB0 : (volume (B ε)).toReal = 0
      · rw [hB0]; positivity
      · have hBpos : 0 < (volume (B ε)).toReal :=
          lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hB0)
        set Ψ : (Fin d → ℂ) → ℂ :=
          fun w => F ((fun i => (p i : ℂ)) + fun i => (cf ε i : ℂ) * w i) / (μ : ℂ) with hΨ
        have hΨdiff : Differentiable ℂ Ψ := by
          rw [hΨ]
          fun_prop
        have hΨb : ∀ w : Fin d → ℂ, (∀ i, ‖w i‖ ≤ 4) → ‖Ψ w‖ ≤ M := by
          intro w hw
          rw [hΨ, norm_div, Complex.norm_of_nonneg hμpos.le, div_le_iff₀ hμpos]
          have h2 : ‖F ((fun i => (p i : ℂ)) + fun i => (cf ε i : ℂ) * w i)‖ ≤ μ * M := by
            refine hMb _ (fun i => ?_)
            beta_reduce
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            calc |cf ε i| * ‖w i‖ ≤ 2 * 4 :=
                  mul_le_mul (hcf2 ε i) (hw i) (norm_nonneg _) (by norm_num)
              _ = 8 := by norm_num
          linarith
        have hΨ0 : 1 ≤ ‖Ψ 0‖ := by
          rw [hΨ, norm_div, Complex.norm_of_nonneg hμpos.le]
          have harg : ((fun i => (p i : ℂ)) + fun i => (cf ε i : ℂ) * (0 : Fin d → ℂ) i)
              = (fun i => (p i : ℂ)) := by
            funext j
            simp
          rw [harg, hμval, div_self (ne_of_gt hμpos)]
        have haB : ∀ z ∈ B ε, ‖Ψ (fun i => (z i : ℂ))‖ ≤ t / μ := by
          intro z hz
          have hz2 := hz.2
          rw [hA] at hz2
          have hzA : ‖F (fun i => ((p i + cf ε i * z i : ℝ) : ℂ))‖ ≤ t := by
            have := hz2.2
            simpa using this
          have harg : (fun i : Fin d => ((p i + cf ε i * z i : ℝ) : ℂ))
              = (fun i => (p i : ℂ)) + fun i => (cf ε i : ℂ) * (z i : ℂ) := by
            ext j; simp [Pi.add_apply]
          rw [hΨ]
          beta_reduce
          rw [← harg, norm_div, Complex.norm_of_nonneg hμpos.le, div_le_div_iff_of_pos_right hμpos]
          exact hzA
        have hconcl := d2_kovrijkine_at_zero K hKov Ψ M (t / μ) hM (by positivity) hΨdiff hΨb hΨ0
          (B ε) hBmeas hBsub hBpos haB
        have h1 : 1 ≤ (K / (volume (B ε)).toReal) ^ (K * Real.log M) * (t / μ) :=
          le_trans hΨ0 hconcl
        have he : 0 ≤ K * Real.log M := mul_nonneg hKpos.le (Real.log_nonneg hM)
        rcases eq_or_lt_of_le he with he0 | hepos
        · have hb1 : (volume (B ε)).toReal ≤ 1 := by
            calc (volume (B ε)).toReal
                ≤ (volume {z : Fin d → ℝ | ∀ i, 0 ≤ z i ∧ z i ≤ 1}).toReal :=
                  ENNReal.toReal_mono (by rw [d2_volume_unit_cube]; exact ENNReal.one_ne_top)
                    (measure_mono hBsub)
              _ = 1 := by rw [d2_volume_unit_cube, ENNReal.toReal_one]
          rw [← he0]
          simp only [one_div, inv_zero, Real.rpow_zero, mul_one]
          linarith
        · exact d2_mul_rpow_extract hKpos hBpos (div_pos ht hμpos) hepos h1
    have hprod : (∏ i : Fin d, |cf ε i|) ≤ 2 ^ d := by
      calc (∏ i : Fin d, |cf ε i|) ≤ ∏ _i : Fin d, (2:ℝ) :=
            Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hcf2 ε i)
        _ = 2 ^ d := by simp [Finset.prod_const, Fintype.card_fin]
    calc (volume (A ∩ S ε)).toReal
        = (∏ i : Fin d, |cf ε i|) * (volume (B ε)).toReal := by
          rw [hscale, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ => abs_nonneg _))]
      _ ≤ 2 ^ d * (K * (t / μ) ^ (1 / (K * Real.log M))) :=
          mul_le_mul hprod hBle ENNReal.toReal_nonneg (by positivity)
  calc (volume A).toReal
      ≤ (∑ ε : Fin d → Bool, volume (A ∩ S ε)).toReal :=
        ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun ε _ => hfin ε)) h1
    _ = ∑ ε : Fin d → Bool, (volume (A ∩ S ε)).toReal :=
        ENNReal.toReal_sum (fun ε _ => hfin ε)
    _ ≤ ∑ _ε : Fin d → Bool, 2 ^ d * (K * (t / μ) ^ (1 / (K * Real.log M))) :=
        Finset.sum_le_sum (fun ε _ => h3 ε)
    _ = 4 ^ d * K * (t / μ) ^ (1 / (K * Real.log M)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_bool, nsmul_eq_mul]
        push_cast
        have h : (2:ℝ)^d * 2^d = 4^d := by rw [← mul_pow]; norm_num
        rw [← h]; ring

theorem d2_div_two_pow_le {d : ℕ} {l : ℝ} (hl : 0 ≤ l) :
    l / (2:ℝ)^(d+1) ≤ l * (2:ℝ)^d / 2 := by
  have h2 : (0:ℝ) < (2:ℝ)^(d+1) := by positivity
  rw [div_le_iff₀ h2]
  have hpow : (2:ℝ)^(d+1) * ((2:ℝ)^d / 2) = (2:ℝ)^(2*d) := by
    rw [← mul_div_assoc, ← pow_add, show d + 1 + d = 2 * d + 1 by ring, pow_succ,
      mul_div_cancel_right₀ _ (by norm_num : (2:ℝ) ≠ 0)]
  have h3 : (l * (2:ℝ)^d / 2) * (2:ℝ)^(d+1) = l * (2:ℝ)^(2*d) := by
    rw [mul_div_assoc, mul_assoc, mul_comm ((2:ℝ)^d / 2) ((2:ℝ)^(d+1)), hpow]
  rw [h3]
  have h1 : (1:ℝ) ≤ (2:ℝ)^(2*d) := one_le_pow₀ (by norm_num)
  nlinarith

end D2LocalEstimates

section D2Summation
theorem d2_absorb {A V S k : ℝ} (hA : 1 ≤ A) (hV : 1 ≤ V) (hS : 0 ≤ S) (hk : 0 ≤ k) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (lam sig : ℝ), 0 < lam → lam ≤ 1 → 1 ≤ sig →
      A * (V / lam) ^ (S * sig + k) ≤ (C / lam) ^ (C * sig) := by
  refine ⟨max (S + k + 1) (A * V + 1), ?_, ?_⟩
  · have h : (1:ℝ) ≤ S + k + 1 := by linarith
    exact h.trans (le_max_left _ _)
  intro lam sig hlam0 hlam1 hsig
  have hC1 : (1:ℝ) ≤ max (S + k + 1) (A * V + 1) := by
    have h : (1:ℝ) ≤ S + k + 1 := by linarith
    exact h.trans (le_max_left _ _)
  have hCS : S + k + 1 ≤ max (S + k + 1) (A * V + 1) := le_max_left _ _
  have hCAV : A * V + 1 ≤ max (S + k + 1) (A * V + 1) := le_max_right _ _
  set C : ℝ := max (S + k + 1) (A * V + 1) with hCdef
  have hbase : 1 ≤ V / lam := by rw [le_div_iff₀ hlam0]; linarith
  have hexp : S * sig + k ≤ C * sig := by
    have h1 : S * sig + k ≤ (S + k + 1) * sig := by nlinarith [hS, hk, hsig]
    have h2 : (S + k + 1) * sig ≤ C * sig := mul_le_mul_of_nonneg_right hCS (by linarith)
    linarith
  have hstep1 : (V / lam) ^ (S * sig + k) ≤ (V / lam) ^ (C * sig) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hstep2 : A * (V / lam) ^ (C * sig) ≤ (C / lam) ^ (C * sig) := by
    have h1 : (C / lam) ^ (C * sig) = (C / V) ^ (C * sig) * (V / lam) ^ (C * sig) := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      field_simp
    have hCV : A ≤ C / V := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have h2 : A ≤ (C / V) ^ (C * sig) := by
      calc A ≤ C / V := hCV
        _ = (C / V) ^ (1:ℝ) := (Real.rpow_one _).symm
        _ ≤ (C / V) ^ (C * sig) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ C / V) (by nlinarith [hC1, hsig])
    rw [h1]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  calc A * (V / lam) ^ (S * sig + k) ≤ A * (V / lam) ^ (C * sig) :=
        mul_le_mul_of_nonneg_left hstep1 (by linarith)
    _ ≤ (C / lam) ^ (C * sig) := hstep2

/-- Abstract summation bookkeeping over an arbitrary finite index type. -/
theorem d2_sum_le_of_per_box {ι : Type*} (m r : ι → ℝ) (T R : ℝ) (Gd : ι → Prop)
    (hm : ∀ k, 0 ≤ m k) (hr : ∀ k, 0 ≤ r k)
    (hTsum : HasSum m T) (hRsum : HasSum r R)
    (hbad : (∑' k, if Gd k then 0 else m k) ≤ (1/2) * T)
    (K0 : ℝ) (hK0 : 0 < K0)
    (hper : ∀ k, Gd k → m k ≤ K0 * r k) :
    T ≤ 2 * K0 * R := by
  classical
  have hmSumm : Summable m := hTsum.summable
  have hrSumm : Summable r := hRsum.summable
  set a1 : ι → ℝ := fun k => if Gd k then m k else 0 with ha1
  set a2 : ι → ℝ := fun k => if Gd k then 0 else m k with ha2
  have ha1nn : ∀ k, 0 ≤ a1 k := by
    intro k; simp only [ha1]
    by_cases h : Gd k
    · rw [if_pos h]; exact hm k
    · rw [if_neg h]
  have ha2nn : ∀ k, 0 ≤ a2 k := by
    intro k; simp only [ha2]
    by_cases h : Gd k
    · rw [if_pos h]
    · rw [if_neg h]; exact hm k
  have ha1le : ∀ k, a1 k ≤ m k := by
    intro k; simp only [ha1]
    by_cases h : Gd k
    · rw [if_pos h]
    · rw [if_neg h]; exact hm k
  have ha2le : ∀ k, a2 k ≤ m k := by
    intro k; simp only [ha2]
    by_cases h : Gd k
    · rw [if_pos h]; exact hm k
    · rw [if_neg h]
  have ha1s : Summable a1 := Summable.of_nonneg_of_le ha1nn ha1le hmSumm
  have ha2s : Summable a2 := Summable.of_nonneg_of_le ha2nn ha2le hmSumm
  have hsum : a1 + a2 = m := by
    funext k
    simp only [ha1, ha2, Pi.add_apply]
    by_cases h : Gd k <;> simp [h]
  have hT_eq : T = (∑' k, a1 k) + (∑' k, a2 k) := by
    rw [← hTsum.tsum_eq, ← ha1s.tsum_add ha2s]
    apply tsum_congr
    intro k
    have h := congrFun hsum k
    simp only [Pi.add_apply] at h
    exact h.symm
  have hbad' : (∑' k, a2 k) ≤ (1/2) * T := by
    have hEq : (∑' k, a2 k) = (∑' k, if Gd k then 0 else m k) := by
      apply tsum_congr; intro k; simp only [ha2]
    rw [hEq]; exact hbad
  have h1le : (∑' k, a1 k) ≤ K0 * R := by
    have hle := Summable.tsum_le_tsum (f := a1) (g := fun k => K0 * r k) ?_ ha1s (hrSumm.mul_left K0)
    · rw [tsum_mul_left, hRsum.tsum_eq] at hle; exact hle
    · intro k
      simp only [ha1]
      by_cases h : Gd k
      · rw [if_pos h]; exact hper k h
      · rw [if_neg h]; exact mul_nonneg hK0.le (hr k)
  rw [hT_eq]
  linarith

/-- A coordinate hyperplane has measure zero. -/
theorem d2_volume_coord_eq_zero {d : ℕ} (i : Fin d) (a : ℝ) :
    volume {x : Fin d → ℝ | x i = a} = 0 := by
  have hset : {x : Fin d → ℝ | x i = a}
      = Set.pi Set.univ (fun j => if j = i then ({a} : Set ℝ) else Set.univ) := by
    ext x; simp [Set.mem_pi]
  rw [hset, volume_pi, Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem d2_volume_closedDiff_halfopen {d : ℕ} (L : Fin d → ℝ) :
    volume ({x : Fin d → ℝ | ∀ i, L i ≤ x i ∧ x i ≤ L i + 2} \
      {x : Fin d → ℝ | ∀ i, L i ≤ x i ∧ x i < L i + 2}) = 0 := by
  have hsub : ({x : Fin d → ℝ | ∀ i, L i ≤ x i ∧ x i ≤ L i + 2} \
      {x : Fin d → ℝ | ∀ i, L i ≤ x i ∧ x i < L i + 2}) ⊆
      ⋃ i : Fin d, {x : Fin d → ℝ | x i = L i + 2} := by
    intro x hx
    rw [Set.mem_diff] at hx
    obtain ⟨hx1, hx2⟩ := hx
    simp only [Set.mem_ofPred_eq] at hx1 hx2
    obtain ⟨i, hi⟩ := not_forall.mp hx2
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    simp only [Set.mem_ofPred_eq]
    have h1 := hx1 i
    rcases lt_or_eq_of_le h1.2 with hlt | heq
    · exfalso
      exact hi ⟨h1.1, hlt⟩
    · exact heq
  exact measure_mono_null hsub (measure_iUnion_null (fun i => d2_volume_coord_eq_zero i (L i + 2)))

theorem d2_setIntegral_eq_of_subset_diff_null {d : ℕ} {f : (Fin d → ℝ) → ℝ} {A B : Set (Fin d → ℝ)}
    (hBA : B ⊆ A) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : volume (A \ B) = 0) (hint : IntegrableOn f A) : ∫ x in A, f x = ∫ x in B, f x := by
  have hdisj : Disjoint B (A \ B) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx'.2 hx
  have hunion : B ∪ (A \ B) = A := by
    ext x
    constructor
    · rintro (hx | ⟨hx, -⟩)
      · exact hBA hx
      · exact hx
    · intro hx
      by_cases h : x ∈ B
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
  have hIntB : IntegrableOn f B := hint.mono_set hBA
  have hIntD : IntegrableOn f (A \ B) := hint.mono_set Set.diff_subset
  rw [← hunion, setIntegral_union hdisj (hA.diff hB) hIntB hIntD,
    setIntegral_measure_zero _ h, add_zero]

end D2Summation

section D2BoxMass
theorem d2_box_mass_bound {d : ℕ} (K D D₂ : ℝ) (hK1 : 1 ≤ K) (hD : 1 ≤ D) (hD₂ : 0 ≤ D₂)
    (hKov : ∀ (F : (Fin d → ℂ) → ℂ) (M a : ℝ), 1 ≤ M → 0 ≤ a → Differentiable ℂ F →
      (∀ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 4) → ‖F z‖ ≤ M) → 1 ≤ ‖F 0‖ →
      ∀ (E : Set (EuclideanSpace ℝ (Fin d))), MeasurableSet E →
        E ⊆ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} →
        0 < (volume E).toReal → (∀ x ∈ E, ‖F (fun i => (x i : ℂ))‖ ≤ a) →
        ∀ x ∈ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1},
          ‖F (fun i => (x i : ℂ))‖ ≤ (K / (volume E).toReal) ^ (K * Real.log M) * a) :
    ∃ A V S k : ℝ, 1 ≤ A ∧ 1 ≤ V ∧ 0 ≤ S ∧ 0 ≤ k ∧
      ∀ (F : (Fin d → ℂ) → ℂ) (hF : Differentiable ℂ F)
        (L p : Fin d → ℝ) (hLp : ∀ i, L i ≤ p i) (hpR : ∀ i, p i ≤ L i + 2)
        (μ ν B : ℝ) (hμpos : 0 < μ) (hμval : ‖F (fun i => (p i : ℂ))‖ = μ)
        (hνpos : 0 < ν) (hνμ : ν ≤ μ * D * Real.exp (D₂ * B)) (hB0 : 0 ≤ B)
        (hexp : ∀ W : Fin d → ℂ, ‖F ((fun i => (p i : ℂ)) + W)‖ ≤ ν * Real.exp (B * ‖W‖))
        (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
        (E : Set (Fin d → ℝ)) (hEmeas : MeasurableSet E)
        (hEsub : E ⊆ {x : Fin d → ℝ | ∀ i, L i ≤ x i ∧ x i ≤ L i + 2})
        (hEvol : lam * 2 ^ d ≤ (volume E).toReal)
        (hμb : ∀ x : Fin d → ℝ, (∀ i, L i ≤ x i ∧ x i ≤ L i + 2) →
          ‖F (fun i => (x i : ℂ))‖ ≤ μ),
        ∫ x in {x : Fin d → ℝ | ∀ i, L i ≤ x i ∧ x i ≤ L i + 2}, ‖F (fun i => (x i : ℂ))‖ ^ 2
          ≤ A * (V / lam) ^ (S * B + k) * ∫ x in E, ‖F (fun i => (x i : ℂ))‖ ^ 2 := by
  refine ⟨2, 2 ^ (d+1) * 4 ^ d * K, K * (16 + 2 * D₂), 1 + 2 * K * (Real.log 2 + Real.log D),
    ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · have h1 : (1:ℝ) ≤ 2 ^ (d+1) := one_le_pow₀ (by norm_num)
    have h2 : (1:ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
    calc (1:ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ 2 ^ (d+1) * 4 ^ d * K :=
          mul_le_mul (mul_le_mul h1 h2 zero_le_one (by positivity)) hK1 (by norm_num) (by positivity)
  · exact mul_nonneg (by linarith) (by linarith)
  · have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : (0:ℝ) ≤ Real.log D := Real.log_nonneg hD
    nlinarith [h2, h3, hK1]
  · intro F hF L p hLp hpR μ ν B hμpos hμval hνpos hνμ hB0 hexp lam hlam0 hlam1 E hEmeas hEsub hEvol hμb
    classical
    set Box : Set (Fin d → ℝ) := {x : Fin d → ℝ | ∀ i, L i ≤ x i ∧ x i ≤ L i + 2} with hBox
    have hBoxIcc : Box = Set.Icc L (L + 2) := by
      rw [hBox]
      ext z
      constructor
      · intro h
        exact ⟨fun i => (h i).1, fun i => (h i).2⟩
      · intro h i
        exact ⟨h.1 i, h.2 i⟩
    have hBoxmeas : MeasurableSet Box := by
      rw [hBox]
      have h : {x : Fin d → ℝ | ∀ i, L i ≤ x i ∧ x i ≤ L i + 2}
          = Set.pi Set.univ (fun i : Fin d => Set.Icc (L i) (L i + 2)) := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
      rw [h]
      exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc)
    have hBoxcompact : IsCompact Box := by rw [hBoxIcc]; exact isCompact_Icc
    have hBoxvolE : volume Box = ENNReal.ofReal ((2:ℝ) ^ d) := by
      rw [hBoxIcc, Real.volume_Icc_pi]
      have h2 : ∀ i : Fin d, (L + 2) i - L i = 2 := by intro i; simp
      simp only [h2]
      rw [show (∏ i : Fin d, ENNReal.ofReal (2:ℝ)) = ENNReal.ofReal ((2:ℝ) ^ d) from by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2) d]]
    have hBoxvol : (volume Box).toReal = (2:ℝ) ^ d := by
      rw [hBoxvolE, ENNReal.toReal_ofReal (by positivity)]
    have hBoxfin : volume Box ≠ ⊤ := by rw [hBoxvolE]; exact ENNReal.ofReal_ne_top
    have hFcont : Continuous (fun x : Fin d → ℝ => F (fun i => (x i : ℂ))) :=
      hF.continuous.comp (by fun_prop)
    have hcont2 : Continuous (fun x : Fin d → ℝ => ‖F (fun i => (x i : ℂ))‖ ^ 2) :=
      (hFcont.norm).pow 2
    have hIntBox : IntegrableOn (fun x : Fin d → ℝ => ‖F (fun i => (x i : ℂ))‖ ^ 2) Box :=
      hcont2.continuousOn.integrableOn_compact hBoxcompact
    have hIntE : IntegrableOn (fun x : Fin d → ℝ => ‖F (fun i => (x i : ℂ))‖ ^ 2) E :=
      hIntBox.mono_set hEsub
    set M : ℝ := max 2 (ν * Real.exp (8 * B) / μ) with hM
    have hM2 : 2 ≤ M := le_max_left _ _
    have hM1 : 1 ≤ M := by linarith
    have hMlog : Real.log M ≤ Real.log 2 + (Real.log D + D₂ * B) + 8 * B := by
      have h1 : Real.log (ν * Real.exp (8*B) / μ) ≤ Real.log D + D₂ * B + 8 * B := by
        rw [Real.log_div (by positivity) (ne_of_gt hμpos),
          Real.log_mul (ne_of_gt hνpos) (Real.exp_ne_zero _), Real.log_exp]
        have h3 : ν / μ ≤ D * Real.exp (D₂ * B) := by rw [div_le_iff₀ hμpos]; linarith
        have h4 := Real.log_le_log (by positivity) h3
        rw [Real.log_div (ne_of_gt hνpos) (ne_of_gt hμpos),
          Real.log_mul (ne_of_gt (by linarith : (0:ℝ) < D)) (Real.exp_ne_zero _), Real.log_exp] at h4
        linarith
      rcases le_total (ν * Real.exp (8*B) / μ) 2 with h | h
      · rw [hM, max_eq_left h]
        have h5 : (0:ℝ) ≤ D₂ * B := mul_nonneg hD₂ hB0
        linarith [Real.log_nonneg hD, hB0, Real.log_pos (by norm_num : (1:ℝ) < 2)]
      · rw [hM, max_eq_right h]
        linarith [h1, Real.log_pos (by norm_num : (1:ℝ) < 2)]
    have hMb : ∀ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 8) →
        ‖F ((fun i => (p i : ℂ)) + z)‖ ≤ μ * M := by
      intro z hz
      have hz8 : ‖z‖ ≤ 8 := by
        rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 8)]
        exact hz
      have h1 := hexp z
      have h2 : ν * Real.exp (B * ‖z‖) ≤ ν * Real.exp (8 * B) := by
        apply mul_le_mul_of_nonneg_left _ hνpos.le
        apply Real.exp_le_exp.mpr
        nlinarith [hB0, hz8]
      have h3 : ν * Real.exp (8*B) ≤ μ * M := by
        have h4 : ν * Real.exp (8*B) / μ ≤ M := by
          rw [hM]; exact le_max_right _ _
        rw [div_le_iff₀ hμpos] at h4
        linarith
      linarith
    set W : ℝ := 2 ^ (d+1) * 4 ^ d * K with hW
    have hW1 : 1 ≤ W := by
      rw [hW]
      have h1 : (1:ℝ) ≤ 2 ^ (d+1) := one_le_pow₀ (by norm_num)
      have h2 : (1:ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
      calc (1:ℝ) = 1 * 1 * 1 := by norm_num
        _ ≤ 2 ^ (d+1) * 4 ^ d * K :=
            mul_le_mul (mul_le_mul h1 h2 zero_le_one (by positivity)) hK1 (by norm_num) (by positivity)
    have hW2 : 1 < W := by
      rw [hW, pow_succ]
      have h2d : (1:ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
      have h4d : (1:ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
      have hpos : (0:ℝ) < 2 ^ d * 4 ^ d := by positivity
      nlinarith [h2d, h4d, hK1, hpos]
    set e : ℝ := K * Real.log M with he
    have hepos : 0 < e := by rw [he]; exact mul_pos (by linarith) (Real.log_pos (by linarith))
    set ρ : ℝ := lam / W with hρ
    have hρpos : 0 < ρ := by rw [hρ]; positivity
    have hρlt1 : ρ < 1 := by
      rw [hρ, div_lt_one (by positivity)]
      linarith [hW2, hlam1]
    set s : ℝ := μ * ρ ^ e with hs
    have hspos : 0 < s := by rw [hs]; positivity
    have hslt : s < μ := by
      rw [hs]
      have h1 : ρ ^ e < 1 := Real.rpow_lt_one hρpos.le hρlt1 hepos
      nlinarith
    have hT1' : 1 ≤ W / lam := (le_div_iff₀ hlam0).mpr (by linarith [hW1, hlam1])
    have hρT : ρ = (W / lam)⁻¹ := by rw [hρ, inv_div]
    have hsub := d2_sublevel_bound K hK1 hKov F hF L p hLp hpR μ M s hμpos hμval hM1 hMb hspos hslt
    have hratio : (s / μ) ^ (1 / (K * Real.log M)) = ρ := by
      rw [hs, mul_div_cancel_left₀ _ (ne_of_gt hμpos), ← Real.rpow_mul hρpos.le, he,
        mul_one_div, div_self (ne_of_gt hepos), Real.rpow_one]
    rw [hratio] at hsub
    set A : Set (Fin d → ℝ) := {x | (∀ i, L i ≤ x i ∧ x i ≤ L i + 2) ∧
      ‖F (fun i => (x i : ℂ))‖ ≤ s} with hA
    have hAmeas : MeasurableSet A := by
      rw [hA, Set.setOf_and]
      exact hBoxmeas.inter
        ((isClosed_le (continuous_norm.comp hFcont) continuous_const).measurableSet)
    have hAfin : volume A ≠ ⊤ :=
      ne_top_of_le_ne_top hBoxfin (measure_mono (fun x hx => hx.1))
    have hsubA : (volume A).toReal ≤ 4 ^ d * K * ρ := by
      rw [hA]; exact hsub
    have hAvol : (volume A).toReal ≤ lam * (2:ℝ)^d / 2 := by
      refine hsubA.trans ?_
      rw [hρ, hW]
      rw [show (4:ℝ)^d * K * (lam / (2 ^ (d+1) * 4 ^ d * K)) = lam / 2 ^ (d+1) from by
        field_simp]
      exact d2_div_two_pow_le hlam0.le
    have hEAmeas : MeasurableSet (E \ A) := hEmeas.diff hAmeas
    have hdisj : Disjoint (E \ A) (E ∩ A) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact hx.2 hx'.2
    have hunion : (E \ A) ∪ (E ∩ A) = E := by
      ext x
      constructor
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
      · intro hx
        by_cases h : x ∈ A
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl ⟨hx, h⟩
    have hfin1 : volume (E \ A) ≠ ⊤ :=
      ne_top_of_le_ne_top hBoxfin (measure_mono (fun x hx => hEsub hx.1))
    have hEMvol : lam * (2:ℝ)^d / 2 ≤ (volume (E \ A)).toReal := by
      have hfin2 : volume (E ∩ A) ≠ ⊤ :=
        ne_top_of_le_ne_top hAfin (measure_mono Set.inter_subset_right)
      have hEfin : volume E ≠ ⊤ := ne_top_of_le_ne_top hBoxfin (measure_mono hEsub)
      have hsum : (volume (E \ A)).toReal + (volume (E ∩ A)).toReal = (volume E).toReal := by
        rw [← ENNReal.toReal_add hfin1 hfin2, ← measure_union hdisj (hEmeas.inter hAmeas), hunion]
      have hA2 : (volume (E ∩ A)).toReal ≤ lam * (2:ℝ)^d / 2 :=
        le_trans (ENNReal.toReal_mono hAfin (measure_mono Set.inter_subset_right)) hAvol
      linarith
    have hEmass : s^2 * (lam * (2:ℝ)^d / 2) ≤ ∫ x in E, ‖F (fun i => (x i : ℂ))‖ ^ 2 := by
      have hgt : ∀ x ∈ E \ A, s^2 ≤ ‖F (fun i => (x i : ℂ))‖ ^ 2 := by
        intro x hx
        have hxBox : x ∈ Box := hEsub hx.1
        have hxA : x ∉ A := hx.2
        have hle : s ≤ ‖F (fun i => (x i : ℂ))‖ := by
          by_contra hcon
          push_neg at hcon
          exact hxA (by rw [hA]; exact ⟨hxBox, hcon.le⟩)
        nlinarith [hspos.le]
      have hIntEA : IntegrableOn (fun x : Fin d → ℝ => ‖F (fun i => (x i : ℂ))‖ ^ 2) (E \ A) :=
        hIntE.mono_set Set.diff_subset
      have hIntEA2 : IntegrableOn (fun x : Fin d → ℝ => ‖F (fun i => (x i : ℂ))‖ ^ 2) (E ∩ A) :=
        hIntE.mono_set Set.inter_subset_left
      calc s^2 * (lam * (2:ℝ)^d / 2)
          ≤ s^2 * (volume (E \ A)).toReal := mul_le_mul_of_nonneg_left hEMvol (by positivity)
        _ = ∫ x in E \ A, s^2 := by rw [setIntegral_const, measureReal_def, smul_eq_mul]; ring
        _ ≤ ∫ x in E \ A, ‖F (fun i => (x i : ℂ))‖ ^ 2 :=
            setIntegral_mono_on (integrableOn_const hfin1) hIntEA hEAmeas hgt
        _ ≤ ∫ x in E, ‖F (fun i => (x i : ℂ))‖ ^ 2 := by
            conv_rhs => rw [← hunion]
            rw [setIntegral_union hdisj (hEmeas.inter hAmeas) hIntEA hIntEA2]
            have : (0:ℝ) ≤ ∫ x in E ∩ A, ‖F (fun i => (x i : ℂ))‖ ^ 2 :=
              integral_nonneg (fun x => by positivity)
            linarith
    have hboxmass : ∫ x in Box, ‖F (fun i => (x i : ℂ))‖ ^ 2 ≤ μ^2 * (2:ℝ)^d := by
      have h1 : ∫ x in Box, ‖F (fun i => (x i : ℂ))‖ ^ 2 ≤ ∫ x in Box, μ^2 := by
        apply setIntegral_mono_on hIntBox (integrableOn_const hBoxfin) hBoxmeas
        intro x hx
        have h2 := hμb x hx
        nlinarith [norm_nonneg (F (fun i => (x i : ℂ)))]
      rw [setIntegral_const, measureReal_def, hBoxvol, smul_eq_mul] at h1
      linarith
    have he_le : 2 * e ≤ K * (16 + 2 * D₂) * B + 2 * K * (Real.log 2 + Real.log D) := by
      rw [he]
      have h1 : K * Real.log M ≤ K * (Real.log 2 + (Real.log D + D₂ * B) + 8 * B) :=
        mul_le_mul_of_nonneg_left hMlog (by linarith)
      have h2 : K * (Real.log 2 + (Real.log D + D₂ * B) + 8 * B)
          ≤ K * (16 + 2 * D₂) * B + 2 * K * (Real.log 2 + Real.log D) := by
        have h3 : K * (Real.log 2 + (Real.log D + D₂ * B) + 8 * B)
            = K * (Real.log 2 + Real.log D) + K * D₂ * B + 8 * K * B := by ring
        rw [h3]
        have h4 : (0:ℝ) ≤ K * D₂ * B := mul_nonneg (mul_nonneg (by linarith) hD₂) hB0
        have h5 : (0:ℝ) ≤ 8 * K * B := mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hB0
        nlinarith [h4, h5, hK1, hB0]
      linarith
    have hρeq : ρ ^ e = (W / lam) ^ (-e) := by
      rw [hρ, show lam / W = (W / lam)⁻¹ by rw [inv_div],
        Real.inv_rpow (by positivity : (0:ℝ) ≤ W/lam),
        ← Real.rpow_neg (by positivity : (0:ℝ) ≤ W/lam)]
    have hsl : s ^ 2 = μ ^ 2 * (W / lam) ^ (-(2*e)) := by
      have hp : ((W/lam) ^ (-e)) ^ (2:ℕ) = (W/lam) ^ (-(2*e)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ W/lam)]
        congr 1; ring
      rw [hs, mul_pow, hρeq, hp]
    set X : ℝ := K * (16 + 2 * D₂) * B + (1 + 2 * K * (Real.log 2 + Real.log D)) with hX
    have hq1 : 1 ≤ W / lam := hT1'
    have hmain : μ ^ 2 * (2:ℝ)^d ≤ 2 * (W / lam)^X * (s^2 * (lam * (2:ℝ)^d / 2)) := by
      rw [hsl]
      have hqq : (W / lam) ^ (1:ℝ) ≤ (W / lam) ^ (X - 2*e) :=
        Real.rpow_le_rpow_of_exponent_le hq1 (by rw [hX]; linarith [he_le])
      rw [Real.rpow_one] at hqq
      have h2 : (W / lam) * lam = W := by field_simp
      have h1 : (1:ℝ) ≤ (W / lam) ^ (X - 2*e) * lam := by nlinarith [hqq, h2, hW1, hlam0, hq1]
      have h3 : 2 * (W / lam)^X * (μ^2 * (W / lam)^(-(2*e)) * (lam * (2:ℝ)^d / 2))
          = μ^2 * (2:ℝ)^d * ((W/lam)^X * (W/lam)^(-(2*e)) * lam) := by ring
      rw [h3, ← Real.rpow_add (by positivity : (0:ℝ) < W / lam),
        show X + -(2*e) = X - 2*e by ring]
      have h4 : (0:ℝ) ≤ μ^2 * (2:ℝ)^d := by positivity
      nlinarith [h1, h4]
    show ∫ x in Box, ‖F (fun i => (x i : ℂ))‖ ^ 2 ≤
      2 * (W / lam) ^ (K * (16 + 2 * D₂) * B + (1 + 2 * K * (Real.log 2 + Real.log D))) *
        ∫ x in E, ‖F (fun i => (x i : ℂ))‖ ^ 2
    calc ∫ x in Box, ‖F (fun i => (x i : ℂ))‖ ^ 2 ≤ μ^2 * (2:ℝ)^d := hboxmass
      _ ≤ 2 * (W / lam)^X * (s^2 * (lam * (2:ℝ)^d / 2)) := hmain
      _ ≤ 2 * (W / lam)^X * ∫ x in E, ‖F (fun i => (x i : ℂ))‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hEmass (by positivity)

end D2BoxMass



/-! ## Volumes of the grid boxes -/

theorem d2v_volume_upperBox {d : ℕ} (n : Fin d → ℤ) (γ : Fin d → ℝ) :
    volume (d2_upperBox n γ) = ENNReal.ofReal ((2:ℝ)^d) := by
  rw [d2_upperBox_eq_pi, MeasureTheory.volume_pi, Measure.pi_pi]
  have h : ∀ i : Fin d, volume (Set.Ico (2 * (n i : ℝ) + γ i) (2 * (n i : ℝ) + γ i + 2))
      = ENNReal.ofReal 2 := by
    intro i
    rw [Real.volume_Ico]
    congr 1
    ring
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]

theorem d2v_volume_upperBox_toReal {d : ℕ} (n : Fin d → ℤ) (γ : Fin d → ℝ) :
    (volume (d2_upperBox n γ)).toReal = (2:ℝ)^d := by
  rw [d2v_volume_upperBox, ENNReal.toReal_ofReal (by positivity)]

theorem d2v_volume_closedBox {d : ℕ} (L : Fin d → ℝ) :
    volume {x : Fin d → ℝ | ∀ i, L i ≤ x i ∧ x i ≤ L i + 2} = ENNReal.ofReal ((2:ℝ)^d) := by
  have hIcc : {x : Fin d → ℝ | ∀ i, L i ≤ x i ∧ x i ≤ L i + 2} = Set.Icc L (L + 2) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def, Pi.add_apply]
    exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩
  rw [hIcc, Real.volume_Icc_pi]
  have h : ∀ i : Fin d, ENNReal.ofReal ((L + 2) i - L i) = ENNReal.ofReal 2 := by
    intro i
    congr 1
    simp
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]

theorem d2v_volume_closedBox_toReal {d : ℕ} (L : Fin d → ℝ) :
    (volume {x : Fin d → ℝ | ∀ i, L i ≤ x i ∧ x i ≤ L i + 2}).toReal = (2:ℝ)^d := by
  rw [d2v_volume_closedBox, ENNReal.toReal_ofReal (by positivity)]

/-- Monotonicity of the Kovrijkine bound in the constant, for `v ≤ 1`. -/
theorem d2v_rpow_mono_const {C K v t a b : ℝ} (hC : 0 < C) (hCK : C ≤ K) (hK1 : 1 ≤ K)
    (hv0 : 0 < v) (hv1 : v ≤ 1) (ht : 0 ≤ t) (ha : 0 ≤ a)
    (h : b ≤ (C / v) ^ (C * t) * a) : b ≤ (K / v) ^ (K * t) * a := by
  have hKv : 1 ≤ K / v := by
    rw [le_div_iff₀ hv0]
    linarith
  have h1 : (C / v) ^ (C * t) ≤ (K / v) ^ (C * t) :=
    Real.rpow_le_rpow (by positivity) (by rw [div_le_div_iff_of_pos_right hv0]; exact hCK)
      (by positivity)
  have h2 : (K / v) ^ (C * t) ≤ (K / v) ^ (K * t) :=
    Real.rpow_le_rpow_of_exponent_le hKv (by nlinarith [hC, ht, hCK])
  calc b ≤ (C / v) ^ (C * t) * a := h
    _ ≤ (K / v) ^ (K * t) * a := mul_le_mul_of_nonneg_right (h1.trans h2) ha

/-- The unit cube in `EuclideanSpace ℝ (Fin d)` has volume `1`. -/
theorem d2v_volume_unitCube_euclid (d : ℕ) :
    volume {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} = 1 := by
  have hset : {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
      = (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)) ⁻¹'
          {z : Fin d → ℝ | ∀ i, 0 ≤ z i ∧ z i ≤ 1} := by
    ext x
    simp
  have hcube : ({z : Fin d → ℝ | ∀ i, 0 ≤ z i ∧ z i ≤ 1})
      = Set.pi Set.univ (fun _ : Fin d => Set.Icc (0:ℝ) 1) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  have hmeas : MeasurableSet ({z : Fin d → ℝ | ∀ i, 0 ≤ z i ∧ z i ≤ 1}) := by
    rw [hcube]
    exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc)
  have hmp : MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ))
      volume volume := PiLp.volume_preserving_ofLp (Fin d)
  rw [hset, hmp.measure_preimage hmeas.nullMeasurableSet]
  exact d2_volume_unit_cube


section Aux

/-- The `d`-dimensional assembly in coordinates `Fin d → ℝ`. -/
theorem d2_bandlimited_assembly_aux (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ lam : ℝ) (hσ : 1 ≤ σ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
      (γ : Fin d → ℝ)
      (F : (Fin d → ℂ) → ℂ) (hF : Differentiable ℂ F)
      (hL2 : ∀ (m : ℕ), Integrable (fun x : Fin d → ℝ =>
          ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) ∧
        (∫ x : Fin d → ℝ, ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) ≤
          (2*Real.pi*σ)^(2*m) * (∫ x : Fin d → ℝ, ‖F (fun i => (x i : ℂ))‖^2))
      (E : Set (Fin d → ℝ)) (hE : MeasurableSet E)
      (hEm : ∀ n : Fin d → ℤ, lam * 2^d ≤
        (volume (E ∩ {x : Fin d → ℝ | ∀ i : Fin d, 2*(n i:ℝ)+γ i ≤ x i ∧ x i ≤ 2*(n i:ℝ)+γ i+2})).toReal),
      (∫ x : Fin d → ℝ, ‖F (fun i => (x i : ℂ))‖^2) ≤
        (C/lam)^(C*σ) * (∫ x in E, ‖F (fun i => (x i : ℂ))‖^2) := by
  classical
  obtain ⟨C₀, hC₀pos, hKov₀⟩ := Commons.Analysis.Complex.kovrijkine_d d
  let K : ℝ := max C₀ 1
  have hK1 : 1 ≤ K := le_max_right _ _
  have hKC : C₀ ≤ K := le_max_left _ _
  have hKov : ∀ (F : (Fin d → ℂ) → ℂ) (M a : ℝ), 1 ≤ M → 0 ≤ a → Differentiable ℂ F →
      (∀ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 4) → ‖F z‖ ≤ M) → 1 ≤ ‖F 0‖ →
      ∀ (E : Set (EuclideanSpace ℝ (Fin d))), MeasurableSet E →
        E ⊆ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} →
        0 < (volume E).toReal → (∀ x ∈ E, ‖F (fun i => (x i : ℂ))‖ ≤ a) →
        ∀ x ∈ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1},
          ‖F (fun i => (x i : ℂ))‖ ≤ (K / (volume E).toReal) ^ (K * Real.log M) * a := by
    intro F₁ M a hM ha hFd hb h0 E₁ hE₁meas hE₁sub hE₁pos haE x hx
    have h1 := hKov₀ F₁ M a hM ha hFd hb h0 E₁ hE₁meas hE₁sub hE₁pos haE x hx
    have hv1 : (volume E₁).toReal ≤ 1 := by
      calc (volume E₁).toReal
          ≤ (volume {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1}).toReal :=
            ENNReal.toReal_mono (by rw [d2v_volume_unitCube_euclid]; exact ENNReal.one_ne_top)
              (measure_mono hE₁sub)
        _ = 1 := by rw [d2v_volume_unitCube_euclid, ENNReal.toReal_one]
    exact d2v_rpow_mono_const hC₀pos hKC hK1 hE₁pos hv1 (Real.log_nonneg hM) ha h1
  let D : ℝ := (2:ℝ)^(d+1)
  have hD1 : 1 ≤ D := one_le_pow₀ (by norm_num)
  let D₂ : ℝ := 2 * Real.sqrt d
  have hD₂0 : 0 ≤ D₂ := by positivity
  obtain ⟨A, V, S, k, hA1, hV1, hS0, hk0, hbox⟩ := d2_box_mass_bound K D D₂ hK1 hD1 hD₂0 hKov
  obtain ⟨C, hC1, hCabs⟩ := d2_absorb (A := 2*A) (V := V)
    (S := S * (1000 * 2 * Real.pi)) (k := k) (by linarith) hV1 (by positivity) hk0
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC1, ?_⟩
  intro σ lam hσ hlam hlam1 γ F hF hL2 E hE hEm
  let g : (Fin d → ℝ) → ℝ := fun x => ‖F (fun i => (x i : ℂ))‖^2
  have hgint : Integrable g := by
    have h := (hL2 0).1
    simpa using h
  have hint : ∀ m : ℕ, Integrable (fun x : Fin d → ℝ =>
      ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) := fun m => (hL2 m).1
  have hglob : ∀ m : ℕ, (∫ x : Fin d → ℝ,
        ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) ≤
      (2*Real.pi*σ)^(2*m) * (∫ x : Fin d → ℝ, g x) := fun m => (hL2 m).2
  let T : ℝ := ∫ x : Fin d → ℝ, g x
  let R : ℝ := ∫ x in E, g x
  let m : (Fin d → ℤ) → ℝ := fun n => ∫ x in d2_upperBox n γ, g x
  let r : (Fin d → ℤ) → ℝ := fun n => ∫ x in E ∩ d2_upperBox n γ, g x
  let Gd : (Fin d → ℤ) → Prop := fun n => ∀ q : ℕ, 1 ≤ q →
      (∫ x in d2_upperBox n γ, ‖iteratedFDeriv ℝ q F (fun i => (x i : ℂ))‖^2) ≤
        (2*(3*2*Real.pi*σ)^q)^2 * (∫ x in d2_upperBox n γ, g x)
  have hmnn : ∀ n : Fin d → ℤ, 0 ≤ m n := fun n =>
    setIntegral_nonneg (d2_measurableSet_upperBox n γ) (fun x _ => by positivity)
  have hrnn : ∀ n : Fin d → ℤ, 0 ≤ r n := fun n =>
    setIntegral_nonneg (hE.inter (d2_measurableSet_upperBox n γ)) (fun x _ => by positivity)
  have hTsum : HasSum m T := d2_hasSum_setIntegral_gridBoxIco γ g hgint
  have hRsum : HasSum r R := by
    have h := d2_hasSum_setIntegral_gridBoxIco γ (E.indicator g) (hgint.indicator hE)
    have h2 : (∫ x, E.indicator g x) = ∫ x in E, g x := integral_indicator hE
    rw [h2] at h
    refine h.congr_fun (fun n => ?_)
    rw [setIntegral_indicator hE, Set.inter_comm]
  have hbad : (∑' n : Fin d → ℤ, (if Gd n then 0 else m n)) ≤ (1/2) * T :=
    d2_bad_boxes_mass_d σ hσ F γ hgint (fun q _ => hint q) (fun q _ => hglob q)
  let K0 : ℝ := A * (V / lam) ^ (S * (1000 * 2 * Real.pi * σ) + k)
  have hK0pos : 0 < K0 := by
    apply mul_pos (by linarith)
    exact Real.rpow_pos_of_pos (by positivity) _
  have hper : ∀ n : Fin d → ℤ, Gd n → m n ≤ K0 * r n := by
    intro n hn
    by_cases hpos : 0 < m n
    · have hQvol : 1 ≤ (volume (d2_upperBox n γ)).toReal := by
        rw [d2v_volume_upperBox_toReal]
        exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
      obtain ⟨x0, hx0, hderiv⟩ := d2_exists_pointwise_deriv_bound_of_good σ hσ F hint hglob
        (d2_upperBox n γ) (d2_measurableSet_upperBox n γ) hQvol hn hpos
      let L : Fin d → ℝ := fun i => 2 * (n i : ℝ) + γ i
      let BC : Set (Fin d → ℝ) := {x : Fin d → ℝ | ∀ i, L i ≤ x i ∧ x i ≤ L i + 2}
      have hBCmeas : MeasurableSet BC := by
        have h : BC = Set.pi Set.univ (fun i : Fin d => Set.Icc (L i) (L i + 2)) := by
          ext x
          simp only [BC, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
        rw [h]
        exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc)
      have hsub : d2_upperBox n γ ⊆ BC := by
        intro x hx i
        exact ⟨(hx i).1, le_of_lt (hx i).2⟩
      have hCeq : ∫ x in BC, g x = m n :=
        d2_setIntegral_eq_of_subset_diff_null hsub hBCmeas (d2_measurableSet_upperBox n γ)
          (d2_volume_closedDiff_halfopen L) hgint.integrableOn
      have hmBCpos : 0 < ∫ x in BC, g x := by rw [hCeq]; exact hpos
      have hBCcomp : IsCompact BC := by
        have h : BC = Set.Icc L (L + 2) := by
          ext x
          simp only [BC, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def, Pi.add_apply]
          exact ⟨fun hh => ⟨fun i => (hh i).1, fun i => (hh i).2⟩,
            fun hh i => ⟨hh.1 i, hh.2 i⟩⟩
        rw [h]; exact isCompact_Icc
      have hBCne : BC.Nonempty := ⟨L, fun i => ⟨le_refl _, by linarith⟩⟩
      have hcont : ContinuousOn (fun x : Fin d → ℝ => ‖F (fun i => (x i : ℂ))‖) BC :=
        (((hF.continuous.comp
          (by fun_prop : Continuous fun x : Fin d → ℝ => fun i => (x i : ℂ)))).norm).continuousOn
      obtain ⟨p, hpBC, hpmax⟩ := hBCcomp.exists_isMaxOn hBCne hcont
      let μ : ℝ := ‖F (fun i => (p i : ℂ))‖
      have hμub : ∀ x ∈ BC, ‖F (fun i => (x i : ℂ))‖ ≤ μ := fun x hx => hpmax hx
      have hμpos : 0 < μ := by
        by_contra hcon
        have hle : μ ≤ 0 := not_lt.mp hcon
        have hzero : ∀ x ∈ BC, g x = 0 := by
          intro x hx
          have h1 : ‖F (fun i => (x i : ℂ))‖ ≤ μ := hμub x hx
          have h2 : ‖F (fun i => (x i : ℂ))‖ = 0 := le_antisymm (h1.trans hle) (norm_nonneg _)
          simp [g, h2]
        have hzero2 : ∫ x in BC, g x = 0 := by
          rw [show (0:ℝ) = ∫ x in BC, (0:ℝ) by simp]
          exact setIntegral_congr_fun hBCmeas hzero
        linarith [hmBCpos, hzero2]
      have hF_an : AnalyticOnNhd ℂ F Set.univ := fun z _ =>
        Commons.Analysis.Complex.analyticAt_of_differentiableOn_closedBall (f := F) (c := z)
          (R := 1) (by norm_num) (hF.differentiableOn.mono (Set.subset_univ _))
      have hbase : 0 < 1000 * 2 * Real.pi * σ := by positivity
      have hexp0 := d2_norm_le_exp_of_iteratedFDeriv_bound F hF_an (fun i => (x0 i : ℂ))
        (2 * Real.sqrt (m n)) (1000 * 2 * Real.pi * σ) (by positivity) hbase.le (fun q => by
          refine (hderiv q).trans (le_of_eq ?_)
          ring)
      have hx0BC : x0 ∈ BC := hsub hx0
      have hdist : ‖(fun i => (p i : ℂ)) - (fun i => (x0 i : ℂ))‖ ≤ 2 * Real.sqrt d := by
        rw [pi_norm_le_iff_of_nonneg (by positivity)]
        intro i
        simp only [Pi.sub_apply]
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        have h1 : |p i - x0 i| ≤ 2 := by
          have hp1 := (hpBC i).1
          have hp2 := (hpBC i).2
          have hq1 := (hx0BC i).1
          have hq2 := (hx0BC i).2
          rw [abs_sub_le_iff]
          exact ⟨by linarith, by linarith⟩
        calc |p i - x0 i| ≤ 2 := h1
          _ ≤ 2 * Real.sqrt d := by
              have hd1 : (1:ℝ) ≤ d := by
                have := i.isLt
                exact_mod_cast (by omega : 1 ≤ d)
              have := Real.one_le_sqrt.mpr hd1
              linarith
      let B : ℝ := 1000 * 2 * Real.pi * σ
      let ν : ℝ := 2 * Real.sqrt (m n) * Real.exp (B * (2 * Real.sqrt d))
      have hB0 : 0 ≤ B := hbase.le
      have hνpos : 0 < ν := by
        apply mul_pos
        · exact mul_pos (by norm_num) (Real.sqrt_pos.mpr hpos)
        · exact Real.exp_pos _
      have hexp : ∀ W : Fin d → ℂ, ‖F ((fun i => (p i : ℂ)) + W)‖ ≤ ν * Real.exp (B * ‖W‖) := by
        intro W
        have hvec : (fun i => (x0 i : ℂ)) + (((fun i => (p i : ℂ)) - (fun i => (x0 i : ℂ))) + W)
            = (fun i => (p i : ℂ)) + W := by
          ext i
          simp only [Pi.add_apply, Pi.sub_apply]
          ring
        have h1 := hexp0 (((fun i => (p i : ℂ)) - (fun i => (x0 i : ℂ))) + W)
        rw [hvec] at h1
        have h3 : B * ‖((fun i => (p i : ℂ)) - (fun i => (x0 i : ℂ))) + W‖
            ≤ B * (2 * Real.sqrt d + ‖W‖) := by
          apply mul_le_mul_of_nonneg_left _ hB0
          calc ‖((fun i => (p i : ℂ)) - (fun i => (x0 i : ℂ))) + W‖
              ≤ ‖(fun i => (p i : ℂ)) - (fun i => (x0 i : ℂ))‖ + ‖W‖ := norm_add_le _ _
            _ ≤ 2 * Real.sqrt d + ‖W‖ := by linarith [hdist]
        calc ‖F ((fun i => (p i : ℂ)) + W)‖
            ≤ 2 * Real.sqrt (m n) * Real.exp
                (B * ‖((fun i => (p i : ℂ)) - (fun i => (x0 i : ℂ))) + W‖) := h1
          _ ≤ 2 * Real.sqrt (m n) * Real.exp (B * (2 * Real.sqrt d + ‖W‖)) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h3) (by positivity)
          _ = ν * Real.exp (B * ‖W‖) := by
              rw [show B * (2 * Real.sqrt d + ‖W‖) = B * (2 * Real.sqrt d) + B * ‖W‖ by ring,
                Real.exp_add]
              ring
      have hMle : m n ≤ μ^2 * (2:ℝ)^d := by
        rw [← hCeq]
        calc ∫ x in BC, g x ≤ ∫ x in BC, μ^2 := by
              apply setIntegral_mono_on hgint.integrableOn
                (integrableOn_const (by rw [d2v_volume_closedBox]; exact ENNReal.ofReal_ne_top))
                hBCmeas
              intro x hx
              have h1 := hμub x hx
              nlinarith [norm_nonneg (F (fun i => (x i : ℂ)))]
          _ = μ^2 * (volume BC).toReal := by
              rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_comm]
          _ = μ^2 * (2:ℝ)^d := by rw [d2v_volume_closedBox_toReal]
      have hsqrt : Real.sqrt (m n) ≤ μ * (2:ℝ)^d := by
        have h2d : (1:ℝ) ≤ (2:ℝ)^d := one_le_pow₀ (by norm_num)
        have h2dpos : (0:ℝ) < (2:ℝ)^d := by positivity
        rw [Real.sqrt_le_left (by positivity)]
        have h2d2 : (2:ℝ)^d ≤ ((2:ℝ)^d)^2 := by
          simpa [sq] using le_mul_of_one_le_right h2dpos.le h2d
        calc m n ≤ μ^2 * (2:ℝ)^d := hMle
          _ ≤ μ^2 * ((2:ℝ)^d)^2 := mul_le_mul_of_nonneg_left h2d2 (sq_nonneg μ)
          _ = (μ * (2:ℝ)^d)^2 := by ring
      have h2sqrt : 2 * Real.sqrt (m n) ≤ μ * D := by
        have hDval : D = 2 * (2:ℝ)^d := by
          simp only [D]
          rw [pow_succ]
          ring
        rw [hDval]
        nlinarith [hsqrt]
      have hνμ : ν ≤ μ * D * Real.exp (D₂ * B) := by
        have hexpval : Real.exp (D₂ * B) = Real.exp (B * (2 * Real.sqrt d)) := by
          simp only [D₂]
          ring_nf
        have h2sqrt' : 2 * Real.sqrt (m n) * Real.exp (B * (2 * Real.sqrt d))
            ≤ μ * D * Real.exp (B * (2 * Real.sqrt d)) :=
          mul_le_mul_of_nonneg_right h2sqrt (Real.exp_pos _).le
        rw [hexpval]
        exact h2sqrt'
      have hEvol : lam * 2^d ≤ (volume (E ∩ BC)).toReal := hEm n
      have hboxapp := hbox F hF L p (fun i => (hpBC i).1) (fun i => (hpBC i).2) μ ν B hμpos rfl
        hνpos hνμ hB0 hexp lam hlam hlam1 (E ∩ BC) (hE.inter hBCmeas)
        (fun x hx => hx.2) hEvol (fun x hx => hμub x hx)
      have hEC : ∫ x in E ∩ BC, g x = r n := by
        refine d2_setIntegral_eq_of_subset_diff_null ?_ (hE.inter hBCmeas)
          (hE.inter (d2_measurableSet_upperBox n γ)) ?_ hgint.integrableOn
        · intro x hx
          exact ⟨hx.1, hsub hx.2⟩
        · refine measure_mono_null (fun x hx => ?_) (d2_volume_closedDiff_halfopen L)
          rw [Set.mem_diff] at hx ⊢
          exact ⟨hx.1.2, fun hh => hx.2 ⟨hx.1.1, hh⟩⟩
      show m n ≤ K0 * r n
      calc m n = ∫ x in BC, g x := hCeq.symm
        _ ≤ A * (V / lam) ^ (S * B + k) * ∫ x in E ∩ BC, g x := hboxapp
        _ = A * (V / lam) ^ (S * B + k) * r n := by rw [hEC]
    · push_neg at hpos
      have hz : m n = 0 := le_antisymm hpos (hmnn n)
      rw [hz]
      exact mul_nonneg (le_of_lt hK0pos) (hrnn n)
  have hTR := d2_sum_le_of_per_box m r T R Gd hmnn hrnn hTsum hRsum hbad K0 hK0pos hper
  have hTR' : T ≤ (2 * A) * (V / lam) ^ (S * (1000 * 2 * Real.pi) * σ + k) * R := by
    refine hTR.trans ?_
    have he : 2 * (A * (V / lam) ^ (S * (1000 * 2 * Real.pi * σ) + k))
        = (2 * A) * (V / lam) ^ (S * (1000 * 2 * Real.pi) * σ + k) := by
      rw [show S * (1000 * 2 * Real.pi * σ) + k = S * (1000 * 2 * Real.pi) * σ + k by ring]
      ring
    rw [← he]
  exact hTR'.trans (mul_le_mul_of_nonneg_right (hCabs lam σ hlam hlam1 hσ)
    (integral_nonneg (fun x => by positivity)))

end Aux




section Main

/-- The coordinate change `Fin d → ℝ → EuclideanSpace ℝ (Fin d)`, as a measure preserving
map. -/
abbrev d2toLp (d : ℕ) : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d) :=
  MeasurableEquiv.toLp 2 (Fin d → ℝ)

/-- **Cohen's band-limited assembly in `d` dimensions** — the `d`-dimensional Logvinenko–Sereda
concentration estimate in the entire-function form. -/
theorem bandlimited_assembly_d2 (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ lam : ℝ) (hσ : 1 ≤ σ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
      (γ : EuclideanSpace ℝ (Fin d))
      (F : (Fin d → ℂ) → ℂ) (hF : Differentiable ℂ F)
      (hL2 : ∀ (m : ℕ), Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
          ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) ∧
        (∫ x : EuclideanSpace ℝ (Fin d), ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) ≤
          (2*Real.pi*σ)^(2*m) * (∫ x : EuclideanSpace ℝ (Fin d), ‖F (fun i => (x i : ℂ))‖^2))
      (E : Set (EuclideanSpace ℝ (Fin d))) (hE : MeasurableSet E)
      (hEm : ∀ n : Fin d → ℤ, lam * 2^d ≤
        (volume (E ∩ {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, 2*(n i:ℝ)+γ i ≤ x i ∧ x i ≤ 2*(n i:ℝ)+γ i+2})).toReal),
      (∫ x : EuclideanSpace ℝ (Fin d), ‖F (fun i => (x i : ℂ))‖^2) ≤
        (C/lam)^(C*σ) * (∫ x in E, ‖F (fun i => (x i : ℂ))‖^2) := by
  obtain ⟨C, hCpos, hmain⟩ := d2_bandlimited_assembly_aux d
  refine ⟨C, hCpos, ?_⟩
  intro σ lam hσ hlam hlam1 γ F hF hL2 E hE hEm
  have hmp : MeasurePreserving (d2toLp d) volume volume := PiLp.volume_preserving_toLp (Fin d)
  have hemb : MeasurableEmbedding (d2toLp d) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
  let γ' : Fin d → ℝ := fun i => γ i
  let E' : Set (Fin d → ℝ) := d2toLp d ⁻¹' E
  let G : EuclideanSpace ℝ (Fin d) → ℝ := fun y => ‖F (fun i => (y i : ℂ))‖^2
  let g : (Fin d → ℝ) → ℝ := fun x => ‖F (fun i => (x i : ℂ))‖^2
  have hE' : MeasurableSet E' :=
    hE.preimage (WithLp.measurable_toLp 2 (Fin d → ℝ))
  have hL2' : ∀ (m : ℕ), Integrable (fun x : Fin d → ℝ =>
        ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) ∧
      (∫ x : Fin d → ℝ, ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) ≤
        (2*Real.pi*σ)^(2*m) * (∫ x : Fin d → ℝ, ‖F (fun i => (x i : ℂ))‖^2) := by
    intro m
    obtain ⟨hint, hbound⟩ := hL2 m
    constructor
    · have hcomp : ((fun y : EuclideanSpace ℝ (Fin d) =>
            ‖iteratedFDeriv ℝ m F (fun i => (y i : ℂ))‖ ^ 2) ∘ (d2toLp d))
          = (fun x : Fin d → ℝ => ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) := by
        ext x; rfl
      have h1 : IntegrableOn ((fun y : EuclideanSpace ℝ (Fin d) =>
            ‖iteratedFDeriv ℝ m F (fun i => (y i : ℂ))‖ ^ 2) ∘ (d2toLp d)) Set.univ volume :=
        (hmp.integrableOn_comp_preimage (s := Set.univ) hemb).mpr (by simpa using hint)
      rw [hcomp] at h1
      simpa only [IntegrableOn, Measure.restrict_univ] using h1
    · have h1 : (∫ y : EuclideanSpace ℝ (Fin d),
            ‖iteratedFDeriv ℝ m F (fun i => (y i : ℂ))‖ ^ 2)
          = ∫ x : Fin d → ℝ, ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2 :=
        (hmp.integral_comp hemb
          (fun y : EuclideanSpace ℝ (Fin d) =>
            ‖iteratedFDeriv ℝ m F (fun i => (y i : ℂ))‖ ^ 2)).symm
      have h2 : (∫ y : EuclideanSpace ℝ (Fin d), ‖F (fun i => (y i : ℂ))‖ ^ 2)
          = ∫ x : Fin d → ℝ, ‖F (fun i => (x i : ℂ))‖ ^ 2 :=
        (hmp.integral_comp hemb
          (fun y : EuclideanSpace ℝ (Fin d) => ‖F (fun i => (y i : ℂ))‖ ^ 2)).symm
      calc (∫ x : Fin d → ℝ, ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2)
          = (∫ y : EuclideanSpace ℝ (Fin d),
              ‖iteratedFDeriv ℝ m F (fun i => (y i : ℂ))‖ ^ 2) := h1.symm
        _ ≤ (2*Real.pi*σ)^(2*m) *
              (∫ y : EuclideanSpace ℝ (Fin d), ‖F (fun i => (y i : ℂ))‖^2) := hbound
        _ = (2*Real.pi*σ)^(2*m) * (∫ x : Fin d → ℝ, ‖F (fun i => (x i : ℂ))‖^2) := by rw [h2]
  have hEm' : ∀ n : Fin d → ℤ, lam * 2^d ≤
      (volume (E' ∩ {x : Fin d → ℝ |
        ∀ i : Fin d, 2*(n i:ℝ)+γ' i ≤ x i ∧ x i ≤ 2*(n i:ℝ)+γ' i+2})).toReal := by
    intro n
    have hboxmeas : MeasurableSet {y : EuclideanSpace ℝ (Fin d) |
        ∀ i : Fin d, 2*(n i:ℝ)+γ i ≤ y i ∧ y i ≤ 2*(n i:ℝ)+γ i+2} := by
      have hcoef : MeasurableSet {z : Fin d → ℝ | ∀ i : Fin d,
          2*(n i:ℝ)+γ i ≤ z i ∧ z i ≤ 2*(n i:ℝ)+γ i+2} := by
        have h2 : {z : Fin d → ℝ | ∀ i : Fin d,
            2*(n i:ℝ)+γ i ≤ z i ∧ z i ≤ 2*(n i:ℝ)+γ i+2}
            = Set.pi Set.univ (fun i : Fin d =>
                Set.Icc (2*(n i:ℝ)+γ i) (2*(n i:ℝ)+γ i+2)) := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
        rw [h2]
        exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc)
      have hpre : {y : EuclideanSpace ℝ (Fin d) |
          ∀ i : Fin d, 2*(n i:ℝ)+γ i ≤ y i ∧ y i ≤ 2*(n i:ℝ)+γ i+2}
          = (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)) ⁻¹'
            {z : Fin d → ℝ | ∀ i : Fin d,
              2*(n i:ℝ)+γ i ≤ z i ∧ z i ≤ 2*(n i:ℝ)+γ i+2} := by
        ext y
        simp
      rw [hpre]
      exact hcoef.preimage (WithLp.measurable_ofLp 2 (Fin d → ℝ))
    have hset : E' ∩ {x : Fin d → ℝ |
        ∀ i : Fin d, 2*(n i:ℝ)+γ' i ≤ x i ∧ x i ≤ 2*(n i:ℝ)+γ' i+2}
        = d2toLp d ⁻¹' (E ∩ {y : EuclideanSpace ℝ (Fin d) |
            ∀ i : Fin d, 2*(n i:ℝ)+γ i ≤ y i ∧ y i ≤ 2*(n i:ℝ)+γ i+2}) := rfl
    rw [hset, hmp.measure_preimage (hE.inter hboxmeas).nullMeasurableSet]
    exact hEm n
  have hmain' := hmain σ lam hσ hlam hlam1 γ' F hF hL2' E' hE' hEm'
  have hInt1 : (∫ y : EuclideanSpace ℝ (Fin d), G y) = ∫ x : Fin d → ℝ, g x :=
    (hmp.integral_comp hemb G).symm
  have hInt2 : (∫ x in E', g x) = ∫ y in E, G y :=
    hmp.setIntegral_preimage_emb hemb G E
  calc (∫ y : EuclideanSpace ℝ (Fin d), G y) = ∫ x : Fin d → ℝ, g x := hInt1
    _ ≤ (C/lam)^(C*σ) * ∫ x in E', g x := hmain'
    _ = (C/lam)^(C*σ) * ∫ y in E, G y := by rw [hInt2]

end Main

end Commons.Analysis.Fourier.LogvinenkoSereda
