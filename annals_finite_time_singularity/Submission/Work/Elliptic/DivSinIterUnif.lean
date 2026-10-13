import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.DivSinRec
import Submission.Work.Elliptic.DivSinSliceBddEst
import Submission.Work.Elliptic.DivSinIdentityA
import Submission.Work.Elliptic.DivSinIdentityB
import Submission.Work.Elliptic.DivSinL2Est
import Submission.Work.Elliptic.DivSinSmoothBounds
import Submission.Work.Elliptic.DivSinDthDerivBound
import Submission.Work.Elliptic.DivSinPhiBound
import Submission.Work.Elliptic.DivSinL2EstUnif
import Submission.Work.Elliptic.DivSinIBPWeight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## 1. Elementary properties of the weight `σ(θ) = sin(2θ)` on `Iθ` -/

/-- `σ = sin(2θ)` is nonnegative on `Iθ = [0, π/2]`. -/
private lemma sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `σ = sin(2θ)` is positive on the open interval `(0, π/2)`. -/
private lemma dsi_sin2_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `σ ≤ 1`. -/
private lemma sin_two_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- `σ ^ 2 ≤ 1`. -/
private lemma sin_two_sq_le_one (θ : ℝ) : Real.sin (2 * θ) ^ 2 ≤ 1 := by
  nlinarith [Real.sin_le_one (2 * θ), Real.neg_one_le_sin (2 * θ), sq_nonneg (Real.sin (2 * θ))]

/-- `x ^ 2 / x ^ r = x ^ (2 - r)` for `0 ≤ x` and `r ≠ 2`. -/
private lemma sq_div_rpow {x : ℝ} (hx : 0 ≤ x) (r : ℝ) (hr : r ≠ 2) :
    x ^ 2 / x ^ r = x ^ (2 - r) := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    rw [Real.zero_rpow (sub_ne_zero.mpr hr.symm)]
    norm_num
  · rw [Real.rpow_sub h (2 : ℝ) r]
    norm_num

/-- For `0 ≤ x ≤ 1` the map `r ↦ x ^ r` is antitone. -/
private lemma rpow_le_rpow_of_le_one {x a b : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ha : 0 < a)
    (hab : a ≤ b) : x ^ b ≤ x ^ a := by
  rcases eq_or_lt_of_le hx0 with h | h
  · subst h
    rw [Real.zero_rpow (ne_of_gt ha), Real.zero_rpow (ne_of_gt (lt_of_lt_of_le ha hab))]
  · exact Real.rpow_le_rpow_of_exponent_ge h hx1 hab

/-- `0 < 2 - γ`. -/
private lemma two_sub_gam_pos {α : ℝ} (hα1 : α ≤ 1) : 0 < 2 - Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

/-- `0 < γ`. -/
private lemma gam_pos {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α :=
  lt_trans zero_lt_one (Work.Spaces.one_lt_gam hα)

/-- `σ ^ (2 - γ) ≤ 1` on `Iθ`. -/
private lemma sin_two_rpow_le_one {α θ : ℝ} (hα1 : α ≤ 1) (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) ≤ 1 :=
  Real.rpow_le_one (sin_two_nonneg hθ) (sin_two_le_one θ) (le_of_lt (two_sub_gam_pos hα1))

/-- `σ ^ 2 * σ ^ (2 - γ) ≤ 1` on `Iθ`. -/
private lemma sin_two_sq_mul_rpow_le_one {α θ : ℝ} (hα1 : α ≤ 1) (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) ≤ 1 :=
  calc Real.sin (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
      ≤ 1 * 1 := mul_le_mul (sin_two_sq_le_one θ) (sin_two_rpow_le_one hα1 hθ)
          (Real.rpow_nonneg (sin_two_nonneg hθ) _) (by norm_num)
    _ = 1 := mul_one 1

/-! ## 2. The two functionals of the statement -/

/-- The left hand side of `DivSinIter`: `∫ (D_θ^i (h/sin 2θ))² / sin(2θ)^γ`. -/
private def LHS (α : ℝ) (i : ℕ) (h : ℝ → ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ,
    (Dth1Iter i (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)

/-- The right hand side of `DivSinIter`
(`∫ (h')²/sin(2θ)^η + ∑_{m=1}^{i} ∫ (D_θ^m h')² / sin(2θ)^γ`). -/
private def RHS (α : ℝ) (i : ℕ) (h : ℝ → ℝ) : ℝ :=
  (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta)
    + ∑ m ∈ Finset.Icc 1 i,
        ∫ θ in Work.Spaces.Iθ,
          (Dth1Iter m (deriv h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)

/-- The integrand of `LHS` is nonnegative on `Iθ`. -/
private lemma LHS_integrand_nonneg (α : ℝ) (i : ℕ) (h : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Dth1Iter i (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) :=
  div_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _)

/-- Each summand of `RHS` is nonnegative. -/
private lemma RHS_summand_nonneg (α : ℝ) (m : ℕ) (h : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Dth1Iter m (deriv h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) :=
  div_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _)

private lemma eta_integrand_nonneg (h : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta :=
  div_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _)

private lemma Iθ_measurable : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc

/-- Each summand of `RHS` is nonnegative, so `RHS` dominates its first term. -/
private lemma le_RHS_first (α : ℝ) (i : ℕ) (h : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta)
      ≤ RHS α i h := by
  rw [RHS]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun m _ =>
    setIntegral_nonneg Iθ_measurable fun θ hθ => RHS_summand_nonneg α m h hθ)

/-- `RHS` dominates each of its summands. -/
private lemma le_RHS_term (α : ℝ) (i m : ℕ) (h : ℝ → ℝ) (hm : m ∈ Finset.Icc 1 i) :
    (∫ θ in Work.Spaces.Iθ,
        (Dth1Iter m (deriv h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))
      ≤ RHS α i h := by
  have h1 : (∫ θ in Work.Spaces.Iθ,
      (Dth1Iter m (deriv h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))
      ≤ ∑ k ∈ Finset.Icc 1 i,
        ∫ θ in Work.Spaces.Iθ,
          (Dth1Iter k (deriv h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) :=
    Finset.single_le_sum (s := Finset.Icc 1 i) (a := m)
      (f := fun k => ∫ θ in Work.Spaces.Iθ,
        (Dth1Iter k (deriv h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))
      (fun k _ => setIntegral_nonneg Iθ_measurable fun θ hθ => RHS_summand_nonneg α k h hθ) hm
  rw [RHS]
  exact le_trans h1 (le_add_of_nonneg_left
    (setIntegral_nonneg Iθ_measurable fun θ hθ => eta_integrand_nonneg h hθ))

/-- The first term of `RHS` is nonnegative. -/
private lemma RHS_nonneg (α : ℝ) (i : ℕ) (h : ℝ → ℝ) : 0 ≤ RHS α i h := by
  rw [RHS]
  exact add_nonneg
    (setIntegral_nonneg Iθ_measurable fun θ hθ => eta_integrand_nonneg h hθ)
    (Finset.sum_nonneg fun m _ =>
      setIntegral_nonneg Iθ_measurable fun θ hθ => RHS_summand_nonneg α m h hθ)

/-- `RHS` is monotone in the index. -/
private lemma RHS_mono (α : ℝ) (h : ℝ → ℝ) {k n : ℕ} (hkn : k ≤ n) :
    RHS α k h ≤ RHS α n h := by
  have hsub : Finset.Icc 1 k ⊆ Finset.Icc 1 n := fun m hm => by
    rw [Finset.mem_Icc] at hm ⊢; exact ⟨hm.1, le_trans hm.2 hkn⟩
  rw [RHS, RHS, add_le_add_iff_left]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ =>
    setIntegral_nonneg Iθ_measurable fun θ hθ => RHS_summand_nonneg α m h hθ)


/-! ## 4. The iterated `D_θ`-derivatives of `SinQ h` are `O(σ)` -/

private lemma dth_iter_le (h : ℝ → ℝ) (hsm : SmoothSlice h) (h0 : h 0 = 0)
    (hπ : h (Real.pi / 2) = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ i ∈ Finset.Icc 1 4,
      |Dth1Iter i (SinQ h) θ| ≤ K * Real.sin (2 * θ) := by
  classical
  obtain ⟨Cs, hCspos, hCsσ, hCs1, hCsg, hCsg'⟩ := DivSinSmoothBounds h hsm h0 hπ
  obtain ⟨M, hMpos, hM0, hMk⟩ := DivSinPhiBound
  obtain ⟨Kd, hKdpos, hKd⟩ := DivSinDthDerivBound h hsm h0 hπ
  have hphi : ∀ j ∈ Finset.Icc 0 3, ∀ θ : ℝ,
      |Dth1Iter j (fun t : ℝ => 2 * Real.cos (2 * t)) θ| ≤ M := by
    intro j hj θ
    rcases eq_or_lt_of_le (Finset.mem_Icc.mp hj).1 with h0j | h1j
    · rw [← h0j]
      simp only [Dth1Iter_zero]
      exact hM0 θ
    · have hmem : j ∈ Finset.Icc 1 3 := Finset.mem_Icc.mpr ⟨h1j, (Finset.mem_Icc.mp hj).2⟩
      have hh := hMk j hmem θ
      have hσ2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := sin_two_sq_le_one θ
      have hMnn : 0 ≤ M := hMpos.le
      have habs : 0 ≤ |Dth1Iter j (fun t : ℝ => 2 * Real.cos (2 * t)) θ| := abs_nonneg _
      nlinarith [hh, hσ2, hMnn, habs]
  have key : ∀ n, 1 ≤ n → n ≤ 4 → ∃ K : ℝ, 0 < K ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Dth1Iter n (SinQ h) θ| ≤ K * Real.sin (2 * θ) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih hn1 hn4
    rcases eq_or_lt_of_le hn1 with h1 | h2
    · rw [← h1]
      refine ⟨Cs, hCspos, ?_⟩
      intro θ hθ
      have hσ := dsi_sin2_pos hθ
      show |Real.sin (2 * θ) * deriv (SinQ h) θ| ≤ Cs * Real.sin (2 * θ)
      have hgoal : |deriv (SinQ h) θ| * Real.sin (2 * θ) ≤ Cs * Real.sin (2 * θ) :=
        mul_le_mul_of_nonneg_right (hCsg' θ hθ) hσ.le
      rw [abs_mul, abs_of_pos hσ]
      linarith [hgoal]
    · have hex : ∀ k, k ∈ Finset.Icc 1 (n - 1) → ∃ K : ℝ, 0 < K ∧
          ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |Dth1Iter k (SinQ h) θ| ≤ K * Real.sin (2 * θ) := by
        intro k hk
        obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
        exact ih k (by omega) hk1 (by omega)
      set Kk : ℕ → ℝ := fun k =>
        (if hk : k ∈ Finset.Icc 1 (n - 1) then (hex k hk).choose else Cs) with hKkdef
      have hKk : ∀ k (hk : k ∈ Finset.Icc 1 (n - 1)), 0 < Kk k ∧
          ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |Dth1Iter k (SinQ h) θ| ≤ Kk k * Real.sin (2 * θ) := by
        intro k hk
        have hk' : Kk k = (hex k hk).choose := by rw [hKkdef]; exact dif_pos hk
        rw [hk']
        exact (hex k hk).choose_spec
      have hKknn : ∀ k, 0 ≤ Kk k := by
        intro k
        by_cases hk : k ∈ Finset.Icc 1 (n - 1)
        · exact le_of_lt (hKk k hk).1
        · have hCs : Kk k = Cs := by rw [hKkdef]; exact dif_neg hk
          rw [hCs]; exact le_of_lt hCspos
      refine ⟨Kd + M * ∑ k ∈ Finset.range n,
          (Nat.choose (n - 1) k : ℝ) * (Cs + Kk k), ?_, ?_⟩
      · have hsum : 0 ≤ ∑ k ∈ Finset.range n,
            (Nat.choose (n - 1) k : ℝ) * (Cs + Kk k) :=
          Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (by linarith [hKknn k])
        have hmul : 0 ≤ M * ∑ k ∈ Finset.range n,
            (Nat.choose (n - 1) k : ℝ) * (Cs + Kk k) := mul_nonneg hMpos.le hsum
        linarith [hmul]
      · intro θ hθ
        have hσp := dsi_sin2_pos hθ
        have hσ1 := sin_two_le_one θ
        have hrec := DivSinRec n h (by omega) hsm h0 hπ θ hθ
        have hA : |Dth1Iter (n - 1) (deriv h) θ| ≤ Kd * Real.sin (2 * θ) :=
          hKd θ hθ (n - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        have hterm : ∀ k ∈ Finset.range n,
            |(Nat.choose (n - 1) k : ℝ)
              * Dth1Iter (n - 1 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
              * Dth1Iter k (SinQ h) θ|
            ≤ M * (Nat.choose (n - 1) k : ℝ) * (Cs + Kk k) * Real.sin (2 * θ) := by
          intro k hk
          rw [Finset.mem_range] at hk
          have hc : (0:ℝ) ≤ (Nat.choose (n - 1) k : ℝ) := Nat.cast_nonneg _
          rw [abs_mul, abs_mul, abs_of_nonneg hc]
          by_cases hk0 : k = 0
          · rw [hk0, Nat.sub_zero]
            have hch : (Nat.choose (n - 1) 0 : ℝ) = 1 := by simp
            rw [hch]
            simp only [one_mul, Dth1Iter_zero]
            have hφ : |Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ|
                ≤ M * Real.sin (2 * θ) ^ 2 :=
              hMk (n - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) θ
            have hg : |SinQ h θ| ≤ Cs := hCsg θ hθ
            have h1 : |Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ| * |SinQ h θ|
                ≤ (M * Real.sin (2*θ) ^ 2) * Cs :=
              mul_le_mul hφ hg (abs_nonneg _) (by positivity)
            have h2 : (M * Real.sin (2*θ) ^ 2) * Cs ≤ (M * Cs) * Real.sin (2*θ) := by
              have hσsq : Real.sin (2*θ) ^ 2 ≤ Real.sin (2*θ) := by nlinarith [hσp, hσ1]
              have hMC : 0 ≤ M * Cs := by positivity
              calc (M * Real.sin (2*θ) ^ 2) * Cs = (M * Cs) * Real.sin (2*θ) ^ 2 := by ring
                _ ≤ (M * Cs) * Real.sin (2*θ) := mul_le_mul_of_nonneg_left hσsq hMC
            have h3 : (M * Cs) * Real.sin (2*θ) ≤ (M * (Cs + Kk 0)) * Real.sin (2*θ) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (by linarith [hKknn 0]) hMpos.le) hσp.le
            linarith [h1, h2, h3]
          · have hk1 : 1 ≤ k := by omega
            have hmem : k ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.mpr ⟨hk1, by omega⟩
            have hφ : |Dth1Iter (n - 1 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ| ≤ M :=
              hphi (n - 1 - k) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) θ
            have hg : |Dth1Iter k (SinQ h) θ| ≤ Kk k * Real.sin (2 * θ) := (hKk k hmem).2 θ hθ
            have h1 : |Dth1Iter (n - 1 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ|
                  * |Dth1Iter k (SinQ h) θ| ≤ M * (Kk k * Real.sin (2*θ)) :=
              mul_le_mul hφ hg (abs_nonneg _) hMpos.le
            have h2 : M * (Kk k * Real.sin (2*θ)) ≤ (M * (Cs + Kk k)) * Real.sin (2*θ) := by
              calc M * (Kk k * Real.sin (2*θ)) = (M * Kk k) * Real.sin (2*θ) := by ring
                _ ≤ (M * (Cs + Kk k)) * Real.sin (2*θ) :=
                    mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left (by linarith [hCspos]) hMpos.le) hσp.le
            calc (Nat.choose (n - 1) k : ℝ)
                  * |Dth1Iter (n - 1 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ|
                  * |Dth1Iter k (SinQ h) θ|
                = (Nat.choose (n - 1) k : ℝ)
                  * (|Dth1Iter (n - 1 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ|
                    * |Dth1Iter k (SinQ h) θ|) := by ring
              _ ≤ (Nat.choose (n - 1) k : ℝ) * (M * (Cs + Kk k) * Real.sin (2*θ)) :=
                  mul_le_mul_of_nonneg_left (le_trans h1 (le_trans h2 (le_of_eq rfl))) hc
              _ = M * (Nat.choose (n - 1) k : ℝ) * (Cs + Kk k) * Real.sin (2*θ) := by ring
        have hsum : |∑ k ∈ Finset.range n,
              (Nat.choose (n - 1) k : ℝ)
                * Dth1Iter (n - 1 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
                * Dth1Iter k (SinQ h) θ|
            ≤ M * (∑ k ∈ Finset.range n, (Nat.choose (n - 1) k : ℝ) * (Cs + Kk k))
              * Real.sin (2 * θ) := by
          calc |∑ k ∈ Finset.range n,
                (Nat.choose (n - 1) k : ℝ)
                  * Dth1Iter (n - 1 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
                  * Dth1Iter k (SinQ h) θ|
              ≤ ∑ k ∈ Finset.range n, |(Nat.choose (n - 1) k : ℝ)
                  * Dth1Iter (n - 1 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
                  * Dth1Iter k (SinQ h) θ| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ k ∈ Finset.range n, M * (Nat.choose (n - 1) k : ℝ) * (Cs + Kk k)
                  * Real.sin (2 * θ) := Finset.sum_le_sum hterm
            _ = M * (∑ k ∈ Finset.range n, (Nat.choose (n - 1) k : ℝ) * (Cs + Kk k))
                  * Real.sin (2 * θ) := by
                rw [Finset.mul_sum, Finset.sum_mul]
                exact Finset.sum_congr rfl fun x _ => by ring
        have hsub : |Dth1Iter (n - 1) (deriv h) θ - ∑ k ∈ Finset.range n,
              (Nat.choose (n - 1) k : ℝ)
                * Dth1Iter (n - 1 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
                * Dth1Iter k (SinQ h) θ|
            ≤ Kd * Real.sin (2 * θ)
              + M * (∑ k ∈ Finset.range n, (Nat.choose (n - 1) k : ℝ) * (Cs + Kk k))
                * Real.sin (2 * θ) := by
          have h1 : |Dth1Iter (n - 1) (deriv h) θ - ∑ k ∈ Finset.range n,
                (Nat.choose (n - 1) k : ℝ)
                  * Dth1Iter (n - 1 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
                  * Dth1Iter k (SinQ h) θ|
              ≤ |Dth1Iter (n - 1) (deriv h) θ|
                + |∑ k ∈ Finset.range n,
                    (Nat.choose (n - 1) k : ℝ)
                      * Dth1Iter (n - 1 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
                      * Dth1Iter k (SinQ h) θ| := by
            simpa [sub_eq_add_neg, abs_neg] using abs_add_le (Dth1Iter (n - 1) (deriv h) θ)
              (-(∑ k ∈ Finset.range n, (Nat.choose (n - 1) k : ℝ)
                * Dth1Iter (n - 1 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
                * Dth1Iter k (SinQ h) θ))
          linarith [h1, hA, hsum]
        rw [hrec]
        calc |Dth1Iter (n - 1) (deriv h) θ - ∑ k ∈ Finset.range n,
              (Nat.choose (n - 1) k : ℝ)
                * Dth1Iter (n - 1 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
                * Dth1Iter k (SinQ h) θ|
            ≤ Kd * Real.sin (2 * θ)
              + M * (∑ k ∈ Finset.range n, (Nat.choose (n - 1) k : ℝ) * (Cs + Kk k))
                * Real.sin (2 * θ) := hsub
          _ = (Kd + M * ∑ k ∈ Finset.range n, (Nat.choose (n - 1) k : ℝ) * (Cs + Kk k))
                * Real.sin (2 * θ) := by ring
  obtain ⟨K1, hK1pos, hK1⟩ := key 1 le_rfl (by norm_num)
  obtain ⟨K2, hK2pos, hK2⟩ := key 2 (by norm_num) (by norm_num)
  obtain ⟨K3, hK3pos, hK3⟩ := key 3 (by norm_num) (by norm_num)
  obtain ⟨K4, hK4pos, hK4⟩ := key 4 (by norm_num) (by norm_num)
  refine ⟨K1 + K2 + K3 + K4, by linarith, ?_⟩
  intro θ hθ i hi
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hσnn : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθI
  obtain ⟨hi1, hi4⟩ := Finset.mem_Icc.mp hi
  interval_cases i
  · exact le_trans (hK1 θ hθ) (mul_le_mul_of_nonneg_right (by linarith) hσnn)
  · exact le_trans (hK2 θ hθ) (mul_le_mul_of_nonneg_right (by linarith) hσnn)
  · exact le_trans (hK3 θ hθ) (mul_le_mul_of_nonneg_right (by linarith) hσnn)
  · exact le_trans (hK4 θ hθ) (mul_le_mul_of_nonneg_right (by linarith) hσnn)


/-! ## 5. Algebraic helpers for the induction step -/

/-- For `0 ≤ x ≤ 1` and `|a| ≤ K x`, the weighted square `a²/x^γ` is bounded by `K²`. -/
private lemma bound_sq_div_rpow {a K x γ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hK : 0 ≤ K)
    (ha : |a| ≤ K * x) (hγ : γ ≠ 2) (hγ2 : 0 ≤ 2 - γ) : a ^ 2 / x ^ γ ≤ K ^ 2 := by
  have h1 : a ^ 2 ≤ (K * x) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg (mul_nonneg hK hx0)]
    exact ha
  have h2 : a ^ 2 / x ^ γ ≤ (K * x) ^ 2 / x ^ γ :=
    div_le_div_of_nonneg_right h1 (Real.rpow_nonneg hx0 γ)
  have h3 : (K * x) ^ 2 / x ^ γ ≤ K ^ 2 := by
    rw [mul_pow, mul_div_assoc, sq_div_rpow hx0 γ hγ]
    have h4 : x ^ (2 - γ) ≤ 1 := Real.rpow_le_one hx0 hx1 hγ2
    calc K ^ 2 * x ^ (2 - γ) ≤ K ^ 2 * 1 := mul_le_mul_of_nonneg_left h4 (sq_nonneg K)
      _ = K ^ 2 := mul_one _
  linarith [h2, h3]

/-- `σ ^ 4 * (h/σ)² = h² σ²` (both sides vanish at `σ = 0`). -/
private lemma sin_two_pow4_mul_sinq_sq (h : ℝ → ℝ) (θ : ℝ) :
    (Real.sin (2 * θ)) ^ 4 * (SinQ h θ) ^ 2 = (h θ) ^ 2 * (Real.sin (2 * θ)) ^ 2 := by
  by_cases hs : Real.sin (2 * θ) = 0
  · simp [hs, SinQ]
  · rw [SinQ, div_pow]
    field_simp

/-- `K² * x² * x^(2-γ) ≤ K²` for `0 ≤ x ≤ 1`. -/
private lemma sq_mul_rpow_le {K x γ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hγ2 : 0 ≤ 2 - γ) :
    K ^ 2 * x ^ 2 * x ^ (2 - γ) ≤ K ^ 2 := by
  have h : x ^ 2 * x ^ (2 - γ) ≤ 1 := by
    calc x ^ 2 * x ^ (2 - γ) ≤ 1 * 1 :=
          mul_le_mul (by nlinarith [sq_nonneg x, hx1]) (Real.rpow_le_one hx0 hx1 hγ2)
            (Real.rpow_nonneg hx0 _) (by norm_num)
      _ = 1 := mul_one 1
  calc K ^ 2 * x ^ 2 * x ^ (2 - γ) = K ^ 2 * (x ^ 2 * x ^ (2 - γ)) := by ring
    _ ≤ K ^ 2 * 1 := mul_le_mul_of_nonneg_left h (sq_nonneg K)
    _ = K ^ 2 := mul_one _


/-! ## 6. The pointwise bound of the induction step -/

private lemma step_pointwise (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (M : ℝ) (hM : 0 < M)
    (hM0 : ∀ θ : ℝ, |2 * Real.cos (2 * θ)| ≤ M)
    (hMk : ∀ k ∈ Finset.Icc 1 3, ∀ θ : ℝ,
        |Dth1Iter k (fun t : ℝ => 2 * Real.cos (2 * t)) θ| ≤ M * (Real.sin (2 * θ)) ^ 2)
    (n : ℕ) (hn2 : 2 ≤ n) (hn4 : n ≤ 4) (h : ℝ → ℝ) (hsm : SmoothSlice h)
    (h0 : h 0 = 0) (hp : h (Real.pi / 2) = 0) :
    ∀ θ ∈ Work.Spaces.Iθ,
      (Dth1Iter n (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)
        ≤ 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))
          + 2 * (n : ℝ) * M ^ 2 * ((h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + 2 * (n : ℝ) * ∑ k ∈ Finset.Icc 1 (n - 1),
              ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
                * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)) := by
  have hgam2 : Work.Spaces.gam α ≠ 2 := by have := two_sub_gam_pos hα1; linarith
  have hphi : ∀ j ∈ Finset.Icc 0 3, ∀ θ : ℝ,
      |Dth1Iter j (fun t : ℝ => 2 * Real.cos (2 * t)) θ| ≤ M := by
    intro j hj θ
    rcases eq_or_lt_of_le (Finset.mem_Icc.mp hj).1 with h0j | h1j
    · rw [← h0j]
      simp only [Dth1Iter_zero]
      exact hM0 θ
    · have hmem : j ∈ Finset.Icc 1 3 := Finset.mem_Icc.mpr ⟨h1j, (Finset.mem_Icc.mp hj).2⟩
      have hh := hMk j hmem θ
      have hσ2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := sin_two_sq_le_one θ
      have hMnn : 0 ≤ M := hM.le
      have habs : 0 ≤ |Dth1Iter j (fun t : ℝ => 2 * Real.cos (2 * t)) θ| := abs_nonneg _
      nlinarith [hh, hσ2, hMnn, habs]
  intro θ hθ
  by_cases hσ0 : Real.sin (2 * θ) = 0
  · have hz : (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) = 0 := by
      rw [hσ0, Real.zero_rpow (ne_of_gt (gam_pos hα))]
    have hz2 : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) = 0 := by
      rw [hσ0, Real.zero_rpow (ne_of_gt (two_sub_gam_pos hα1))]
    rw [hz, hz2]
    simp only [div_zero, mul_zero, Finset.sum_const_zero, add_zero]
    norm_num
  · have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
      refine ⟨?_, ?_⟩
      · rcases eq_or_lt_of_le hθ.1 with hh | hh
        · exfalso
          apply hσ0
          rw [← hh]
          show Real.sin (2 * 0) = 0
          rw [mul_zero, Real.sin_zero]
        · exact hh
      · rcases eq_or_lt_of_le hθ.2 with hh | hh
        · exfalso
          apply hσ0
          rw [hh]
          show Real.sin (2 * (Real.pi / 2)) = 0
          rw [show (2:ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        · exact hh
    have hσp : 0 < Real.sin (2 * θ) := dsi_sin2_pos hθ'
    have hσnn : 0 ≤ Real.sin (2 * θ) := hσp.le
    have hrec := DivSinRec n h (by omega) hsm h0 hp θ hθ'
    set sg : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) with hsg
    set sg2 : ℝ := (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hsg2
    set f : ℕ → ℝ := fun k => (Nat.choose (n - 1) k : ℝ)
        * Dth1Iter (n - 1 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
        * Dth1Iter k (SinQ h) θ with hf
    set S : ℝ := ∑ k ∈ Finset.range n, f k with hS
    have hsg_nn : 0 ≤ sg := by rw [hsg]; exact Real.rpow_nonneg hσnn _
    have hrec' : Dth1Iter n (SinQ h) θ = Dth1Iter (n - 1) (deriv h) θ - S := by
      rw [hS, hf]
      exact hrec
    have hsq : (Dth1Iter n (SinQ h) θ) ^ 2
        ≤ 2 * (Dth1Iter (n - 1) (deriv h) θ) ^ 2 + 2 * S ^ 2 := by
      rw [hrec']
      nlinarith [sq_nonneg (Dth1Iter (n - 1) (deriv h) θ + S)]
    have hcs : S ^ 2 ≤ (n : ℝ) * ∑ k ∈ Finset.range n, (f k) ^ 2 := by
      rw [hS]
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n) (fun k => f k) (fun _ => (1 : ℝ))
      simp only [mul_one, one_pow] at h
      have hcard : (∑ _k ∈ Finset.range n, (1 : ℝ)) = (n : ℝ) := by
        simp [Finset.sum_const, Finset.card_range]
      rw [hcard] at h
      simpa only [mul_comm] using h
    have hstep1 : (Dth1Iter n (SinQ h) θ) ^ 2 / sg
        ≤ 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg)
          + 2 * (n : ℝ) * (∑ k ∈ Finset.range n, (f k) ^ 2 / sg) := by
      have h1 : (Dth1Iter n (SinQ h) θ) ^ 2 / sg
          ≤ (2 * (Dth1Iter (n - 1) (deriv h) θ) ^ 2 + 2 * S ^ 2) / sg :=
        div_le_div_of_nonneg_right hsq hsg_nn
      have h2 : (2 * (Dth1Iter (n - 1) (deriv h) θ) ^ 2 + 2 * S ^ 2) / sg
          = 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg) + 2 * (S ^ 2 / sg) := by ring
      have h3 : S ^ 2 / sg ≤ (n : ℝ) * (∑ k ∈ Finset.range n, (f k) ^ 2 / sg) := by
        have h4 : S ^ 2 / sg ≤ ((n : ℝ) * ∑ k ∈ Finset.range n, (f k) ^ 2) / sg :=
          div_le_div_of_nonneg_right hcs hsg_nn
        rw [mul_div_assoc, Finset.sum_div] at h4
        exact h4
      calc (Dth1Iter n (SinQ h) θ) ^ 2 / sg
          ≤ (2 * (Dth1Iter (n - 1) (deriv h) θ) ^ 2 + 2 * S ^ 2) / sg := h1
        _ = 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg) + 2 * (S ^ 2 / sg) := h2
        _ ≤ 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg)
            + 2 * ((n : ℝ) * (∑ k ∈ Finset.range n, (f k) ^ 2 / sg)) := by linarith [h3]
        _ = 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg)
            + 2 * (n : ℝ) * (∑ k ∈ Finset.range n, (f k) ^ 2 / sg) := by ring
    have hsplit : (∑ k ∈ Finset.range n, (f k) ^ 2 / sg)
        = (∑ k ∈ Finset.range (n - 1), (f (k + 1)) ^ 2 / sg) + (f 0) ^ 2 / sg := by
      have hn : n = (n - 1) + 1 := by omega
      conv_lhs => rw [hn]
      rw [Finset.sum_range_succ']
    have hterm0 : (f 0) ^ 2 / sg ≤ M ^ 2 * ((h θ) ^ 2 * sg2) := by
      have hch : (Nat.choose (n - 1) 0 : ℝ) = 1 := by simp
      have hφ : |Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ|
          ≤ M * (Real.sin (2 * θ)) ^ 2 :=
        hMk (n - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) θ
      have hφ2 : (Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ) ^ 2
          ≤ M ^ 2 * (Real.sin (2 * θ)) ^ 4 := by
        have hsq2 : (M * (Real.sin (2 * θ)) ^ 2) ^ 2 = M ^ 2 * (Real.sin (2 * θ)) ^ 4 := by ring
        calc (Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ) ^ 2
            = |Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ| ^ 2 := (sq_abs _).symm
          _ ≤ (M * (Real.sin (2 * θ)) ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hφ 2
          _ = M ^ 2 * (Real.sin (2 * θ)) ^ 4 := hsq2
      have hmul : (Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ) ^ 2
            * (SinQ h θ) ^ 2
          ≤ M ^ 2 * ((h θ) ^ 2 * (Real.sin (2 * θ)) ^ 2) := by
        calc (Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ) ^ 2 * (SinQ h θ) ^ 2
            ≤ (M ^ 2 * (Real.sin (2 * θ)) ^ 4) * (SinQ h θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hφ2 (sq_nonneg _)
          _ = M ^ 2 * ((Real.sin (2 * θ)) ^ 4 * (SinQ h θ) ^ 2) := by ring
          _ = M ^ 2 * ((h θ) ^ 2 * (Real.sin (2 * θ)) ^ 2) := by rw [sin_two_pow4_mul_sinq_sq]
      have heq1 : (Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ * SinQ h θ) ^ 2
          = (Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ) ^ 2 * (SinQ h θ) ^ 2 :=
        mul_pow _ _ 2
      have hdiv : (Dth1Iter (n - 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ * SinQ h θ) ^ 2 / sg
          ≤ M ^ 2 * ((h θ) ^ 2 * (Real.sin (2 * θ)) ^ 2) / sg := by
        rw [heq1]
        exact div_le_div_of_nonneg_right hmul hsg_nn
      have heq2 : M ^ 2 * ((h θ) ^ 2 * (Real.sin (2 * θ)) ^ 2) / sg
          = M ^ 2 * ((h θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 / sg)) := by ring
      have heq3 : (Real.sin (2 * θ)) ^ 2 / sg = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
        rw [hsg]; exact sq_div_rpow hσnn (Work.Spaces.gam α) hgam2
      rw [heq2, heq3] at hdiv
      rw [hf]
      simp only [Dth1Iter_zero, hch, one_mul]
      rw [hsg2]
      exact hdiv
    have htermk : ∀ k ∈ Finset.range (n - 1),
        (f (k + 1)) ^ 2 / sg ≤ ((Nat.choose (n - 1) (k + 1) : ℝ) * M) ^ 2
          * ((Dth1Iter (k + 1) (SinQ h) θ) ^ 2 / sg) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hj : n - 1 - (k + 1) = n - 2 - k := by omega
      have hφ : |Dth1Iter (n - 2 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ| ≤ M :=
        hphi (n - 2 - k) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) θ
      have hc : (0 : ℝ) ≤ (Nat.choose (n - 1) (k + 1) : ℝ) := Nat.cast_nonneg _
      have h1 : |(Nat.choose (n - 1) (k + 1) : ℝ)
            * Dth1Iter (n - 2 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
            * Dth1Iter (k + 1) (SinQ h) θ|
          ≤ (Nat.choose (n - 1) (k + 1) : ℝ) * M * |Dth1Iter (k + 1) (SinQ h) θ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hφ hc) (abs_nonneg _)
      have h2 : ((Nat.choose (n - 1) (k + 1) : ℝ)
            * Dth1Iter (n - 2 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
            * Dth1Iter (k + 1) (SinQ h) θ) ^ 2
          ≤ ((Nat.choose (n - 1) (k + 1) : ℝ) * M * |Dth1Iter (k + 1) (SinQ h) θ|) ^ 2 := by
        rw [← sq_abs ((Nat.choose (n - 1) (k + 1) : ℝ)
            * Dth1Iter (n - 2 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
            * Dth1Iter (k + 1) (SinQ h) θ)]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have h3 : ((Nat.choose (n - 1) (k + 1) : ℝ) * M * |Dth1Iter (k + 1) (SinQ h) θ|) ^ 2
          = ((Nat.choose (n - 1) (k + 1) : ℝ) * M) ^ 2
              * (Dth1Iter (k + 1) (SinQ h) θ) ^ 2 := by
        rw [mul_pow, sq_abs]
      have hmain : ((Nat.choose (n - 1) (k + 1) : ℝ)
            * Dth1Iter (n - 2 - k) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
            * Dth1Iter (k + 1) (SinQ h) θ) ^ 2 / sg
          ≤ (((Nat.choose (n - 1) (k + 1) : ℝ) * M) ^ 2
              * (Dth1Iter (k + 1) (SinQ h) θ) ^ 2) / sg :=
        div_le_div_of_nonneg_right (h2.trans (le_of_eq h3)) hsg_nn
      rw [hf]
      simp only [hj]
      simpa only [mul_div_assoc] using hmain
    have hreindex : (∑ k ∈ Finset.range (n - 1),
          ((Nat.choose (n - 1) (k + 1) : ℝ) * M) ^ 2 * ((Dth1Iter (k + 1) (SinQ h) θ) ^ 2 / sg))
        = ∑ k ∈ Finset.Icc 1 (n - 1),
            ((Nat.choose (n - 1) k : ℝ) * M) ^ 2 * ((Dth1Iter k (SinQ h) θ) ^ 2 / sg) := by
      have hIcc : Finset.Icc 1 (n - 1) = Finset.Ico 1 n := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
      exact Finset.sum_congr rfl fun k _ => by rw [add_comm]
    have hnn : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
    have hb2 : (∑ k ∈ Finset.range (n - 1), (f (k + 1)) ^ 2 / sg)
        ≤ ∑ k ∈ Finset.Icc 1 (n - 1),
            ((Nat.choose (n - 1) k : ℝ) * M) ^ 2 * ((Dth1Iter k (SinQ h) θ) ^ 2 / sg) :=
      (Finset.sum_le_sum htermk).trans (le_of_eq hreindex)
    have hcomb : 2 * (n : ℝ) * ((∑ k ∈ Finset.range (n - 1), (f (k + 1)) ^ 2 / sg)
          + (f 0) ^ 2 / sg)
        ≤ 2 * (n : ℝ) * (M ^ 2 * ((h θ) ^ 2 * sg2)
          + ∑ k ∈ Finset.Icc 1 (n - 1),
              ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
                * ((Dth1Iter k (SinQ h) θ) ^ 2 / sg)) :=
      mul_le_mul_of_nonneg_left
        (by simpa [add_comm] using add_le_add hb2 hterm0) hnn
    calc (Dth1Iter n (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)
        = (Dth1Iter n (SinQ h) θ) ^ 2 / sg := by rw [hsg]
      _ ≤ 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg)
            + 2 * (n : ℝ) * (∑ k ∈ Finset.range n, (f k) ^ 2 / sg) := hstep1
      _ = 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg)
            + 2 * (n : ℝ) * ((∑ k ∈ Finset.range (n - 1), (f (k + 1)) ^ 2 / sg)
              + (f 0) ^ 2 / sg) := by rw [hsplit]
      _ ≤ 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg)
            + 2 * (n : ℝ) * (M ^ 2 * ((h θ) ^ 2 * sg2)
              + ∑ k ∈ Finset.Icc 1 (n - 1),
                  ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
                    * ((Dth1Iter k (SinQ h) θ) ^ 2 / sg)) :=
          add_le_add_right hcomb _
      _ = 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / sg)
            + 2 * (n : ℝ) * M ^ 2 * ((h θ) ^ 2 * sg2)
            + 2 * (n : ℝ) * ∑ k ∈ Finset.Icc 1 (n - 1),
                ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
                  * ((Dth1Iter k (SinQ h) θ) ^ 2 / sg) := by ring
      _ = 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))
            + 2 * (n : ℝ) * M ^ 2 * ((h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            + 2 * (n : ℝ) * ∑ k ∈ Finset.Icc 1 (n - 1),
                ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
                  * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)) := by
          rw [hsg, hsg2]

/-! ## 7. Measurability helpers -/

private lemma measurable_sin_two_rpow (r : ℝ) (hr : 0 ≤ r) :
    Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ r) := by
  have hc : Continuous (fun x : ℝ => x ^ r) := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases eq_or_ne x 0 with h | h
    · subst h; exact Real.continuousAt_rpow_const 0 r (Or.inr hr)
    · exact Real.continuousAt_rpow_const x r (Or.inl h)
  exact hc.measurable.comp (by fun_prop)

private lemma aemeasurable_dth1 (f : ℝ → ℝ)
    (hf : AEMeasurable f (volume.restrict Work.Spaces.Iθ)) :
    AEMeasurable (Dth1 f) (volume.restrict Work.Spaces.Iθ) := by
  have hσ : AEMeasurable (fun θ : ℝ => Real.sin (2 * θ))
      (volume.restrict Work.Spaces.Iθ) :=
    ((by fun_prop : Continuous fun θ : ℝ => Real.sin (2 * θ))).measurable.aemeasurable
  have hd : AEMeasurable (deriv f) (volume.restrict Work.Spaces.Iθ) :=
    (measurable_deriv f).aemeasurable
  have h := hσ.mul hd
  rwa [show Dth1 f = (fun θ : ℝ => Real.sin (2 * θ)) * deriv f from rfl]

private lemma aemeasurable_dth1Iter (f : ℝ → ℝ)
    (hf : AEMeasurable f (volume.restrict Work.Spaces.Iθ)) (m : ℕ) :
    AEMeasurable (Dth1Iter m f) (volume.restrict Work.Spaces.Iθ) := by
  induction m with
  | zero => simpa only [Dth1Iter_zero] using hf
  | succ k ih => simpa only [Dth1Iter_succ] using aemeasurable_dth1 (Dth1Iter k f) ih

private lemma aemeasurable_h (h : ℝ → ℝ) (hsm : SmoothSlice h) :
    AEMeasurable h (volume.restrict Work.Spaces.Iθ) :=
  (hsm.continuousOn.mono (by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩)).aemeasurable Iθ_measurable

private lemma aemeasurable_sin_two : AEMeasurable (fun θ : ℝ => Real.sin (2 * θ))
    (volume.restrict Work.Spaces.Iθ) :=
  ((by fun_prop : Continuous fun θ : ℝ => Real.sin (2 * θ))).measurable.aemeasurable

private lemma ae_mem_Ioo : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hnull : (volume : Measure ℝ) ({0, Real.pi / 2} : Set ℝ) = 0 := by
    have hset2 : ({0, Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    simpa only [hset2] using MeasureTheory.measure_union_null
      (MeasureTheory.measure_singleton (0 : ℝ)) (MeasureTheory.measure_singleton (Real.pi / 2))
  have hset : {a : ℝ | ¬ a ∉ ({0, Real.pi / 2} : Set ℝ)} = ({0, Real.pi / 2} : Set ℝ) := by
    ext x
    simp only [Set.mem_setOf_eq, not_not, Set.mem_insert_iff, Set.mem_singleton_iff]
  have h1 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({0, Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff, hset]; exact hnull
  rw [MeasureTheory.ae_restrict_iff' Iθ_measurable]
  filter_upwards [h1] with θ hθ hI
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hθ
  exact ⟨lt_of_le_of_ne hI.1 (Ne.symm hθ.1), lt_of_le_of_ne hI.2 hθ.2⟩

private lemma integral_three (f g h : ℝ → ℝ) (μ : Measure ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (hh : Integrable h μ) :
    ∫ x, f x + g x + h x ∂μ = (∫ x, f x ∂μ) + (∫ x, g x ∂μ) + (∫ x, h x ∂μ) := by
  have h1 : ∫ x, f x + g x ∂μ = (∫ x, f x ∂μ) + (∫ x, g x ∂μ) := integral_add hf hg
  have h2 : ∫ x, (f x + g x) + h x ∂μ = (∫ x, f x + g x ∂μ) + (∫ x, h x ∂μ) :=
    integral_add (hf.add hg) hh
  rw [h2, h1]

/-! ## 8. The induction step -/

private lemma step_lemma (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (M CL : ℝ)
    (hM : 0 < M) (hCL : 0 < CL)
    (hM0 : ∀ θ : ℝ, |2 * Real.cos (2 * θ)| ≤ M)
    (hMk : ∀ k ∈ Finset.Icc 1 3, ∀ θ : ℝ,
        |Dth1Iter k (fun t : ℝ => 2 * Real.cos (2 * t)) θ| ≤ M * (Real.sin (2 * θ)) ^ 2)
    (hCL2 : ∀ h : ℝ → ℝ, SmoothSlice h → h 0 = 0 → h (Real.pi / 2) = 0 →
        (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          ≤ CL * ∫ θ in Work.Spaces.Iθ,
              (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta)
    (n : ℕ) (hn2 : 2 ≤ n) (hn4 : n ≤ 4) (Ck : ℕ → ℝ)
    (hCkpos : ∀ k ∈ Finset.Icc 1 (n - 1), 0 < Ck k)
    (hIH : ∀ k ∈ Finset.Icc 1 (n - 1), ∀ h : ℝ → ℝ, SmoothSlice h → h 0 = 0 →
        h (Real.pi / 2) = 0 → LHS α k h ≤ Ck k * RHS α k h) :
    ∀ h : ℝ → ℝ, SmoothSlice h → h 0 = 0 → h (Real.pi / 2) = 0 →
      LHS α n h ≤ (2 + 2 * (n : ℝ) * M ^ 2 *
        (CL + ∑ k ∈ Finset.Icc 1 (n - 1), (Nat.choose (n - 1) k : ℝ) ^ 2 * Ck k)) * RHS α n h := by
  intro h hsm h0 hp
  obtain ⟨Cs, hCspos, hCsσ, hCs1, hCsg, hCsg'⟩ := DivSinSmoothBounds h hsm h0 hp
  obtain ⟨Kd, hKdpos, hKd⟩ := DivSinDthDerivBound h hsm h0 hp
  obtain ⟨Kg, hKgpos, hKg⟩ := dth_iter_le h hsm h0 hp
  have hgamnn : 0 ≤ Work.Spaces.gam α := (gam_pos hα).le
  have h2gamnn : 0 ≤ 2 - Work.Spaces.gam α := (two_sub_gam_pos hα1).le
  have hσrpow : AEMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))
      (volume.restrict Work.Spaces.Iθ) :=
    (measurable_sin_two_rpow _ hgamnn).aemeasurable
  have hσ2rpow : AEMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (volume.restrict Work.Spaces.Iθ) :=
    (measurable_sin_two_rpow _ h2gamnn).aemeasurable
  have hSm : AEMeasurable (SinQ h) (volume.restrict Work.Spaces.Iθ) :=
    (aemeasurable_h h hsm).div aemeasurable_sin_two
  -- integrability of the three pieces
  have hAint : IntegrableOn (fun θ : ℝ => (Dth1Iter (n - 1) (deriv h) θ) ^ 2
      / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)) Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ (Kd ^ 2) ?_
    · rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    · exact ((((aemeasurable_dth1Iter (deriv h) (measurable_deriv h).aemeasurable (n - 1)).pow
        aemeasurable_const).div hσrpow)).aestronglyMeasurable
    · filter_upwards [ae_mem_Ioo] with θ hθ
      have hσp := dsi_sin2_pos hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (Real.rpow_nonneg hσp.le _))]
      exact bound_sq_div_rpow hσp.le (sin_two_le_one θ) hKdpos.le
        (hKd θ hθ (n - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
        (by have := two_sub_gam_pos hα1; linarith) h2gamnn
  have hBint : IntegrableOn (fun θ : ℝ => (h θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ (Cs ^ 2) ?_
    · rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    · exact ((((aemeasurable_h h hsm).pow aemeasurable_const).mul hσ2rpow)).aestronglyMeasurable
    · filter_upwards [ae_mem_Ioo] with θ hθ
      have hσp := dsi_sin2_pos hθ
      have h1 : (h θ) ^ 2 ≤ (Cs * Real.sin (2 * θ)) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg (mul_nonneg hCspos.le hσp.le)]
        exact hCsσ θ hθ
      have h2 : (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          ≤ (Cs * Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hσp.le _)
      have h3 : (Cs * Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          ≤ Cs ^ 2 := by
        rw [mul_pow]
        exact sq_mul_rpow_le hσp.le (sin_two_le_one θ) h2gamnn
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hσp.le _))]
      exact h2.trans h3
  have hCint : ∀ k ∈ Finset.Icc 1 (n - 1), IntegrableOn (fun θ : ℝ =>
      ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
        * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)))
      Work.Spaces.Iθ := by
    intro k hk
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_
      (((Nat.choose (n - 1) k : ℝ) * M) ^ 2 * Kg ^ 2) ?_
    · rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    · refine AEMeasurable.const_mul ?_ _ |>.aestronglyMeasurable
      exact (((aemeasurable_dth1Iter (SinQ h) hSm k).pow aemeasurable_const).div hσrpow)
    · filter_upwards [ae_mem_Ioo] with θ hθ
      have hσp := dsi_sin2_pos hθ
      have h1 : (Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) ≤ Kg ^ 2 :=
        bound_sq_div_rpow hσp.le (sin_two_le_one θ) hKgpos.le
          (hKg θ hθ k (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
            by have := (Finset.mem_Icc.mp hk).2; omega⟩))
          (by have := two_sub_gam_pos hα1; linarith) h2gamnn
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (div_nonneg (sq_nonneg _) (Real.rpow_nonneg hσp.le _)))]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have hSint : IntegrableOn (fun θ : ℝ => ∑ k ∈ Finset.Icc 1 (n - 1),
      ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
        * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)))
      Work.Spaces.Iθ :=
    MeasureTheory.integrable_finsetSum _ fun k hk => hCint k hk
  -- the dominating function
  set G : ℝ → ℝ := fun θ => 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2
            / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))
        + 2 * (n : ℝ) * M ^ 2 * ((h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        + 2 * (n : ℝ) * ∑ k ∈ Finset.Icc 1 (n - 1),
            ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
              * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)) with hG
  have hGint : IntegrableOn G Work.Spaces.Iθ := by
    have h1 : Integrable (fun θ : ℝ => 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2
        / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ) :=
      hAint.integrable.const_mul 2
    have h2 : Integrable (fun θ : ℝ => 2 * (n : ℝ) * M ^ 2 * ((h θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ) :=
      hBint.integrable.const_mul (2 * (n : ℝ) * M ^ 2)
    have h3 : Integrable (fun θ : ℝ => 2 * (n : ℝ) * ∑ k ∈ Finset.Icc 1 (n - 1),
        ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
          * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)))
        (volume.restrict Work.Spaces.Iθ) :=
      hSint.integrable.const_mul (2 * (n : ℝ))
    rw [hG]
    exact (h1.add h2).add h3
  -- the pointwise bound
  have hpt := step_pointwise α hα hα1 M hM hM0 hMk n hn2 hn4 h hsm h0 hp
  -- the integral comparison
  have hmono : LHS α n h ≤ ∫ θ in Work.Spaces.Iθ, G θ := by
    rw [LHS]
    refine integral_mono_of_nonneg ?_ hGint ?_
    · filter_upwards [ae_mem_Ioo] with θ hθ
      exact LHS_integrand_nonneg α n h ⟨hθ.1.le, hθ.2.le⟩
    · filter_upwards [ae_mem_Ioo] with θ hθ
      rw [hG]
      exact hpt θ ⟨hθ.1.le, hθ.2.le⟩
  -- the value of the integral of `G`
  have h1i : Integrable (fun θ : ℝ => 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2
      / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ) :=
    hAint.integrable.const_mul 2
  have h2i : Integrable (fun θ : ℝ => 2 * (n : ℝ) * M ^ 2 * ((h θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ) :=
    hBint.integrable.const_mul (2 * (n : ℝ) * M ^ 2)
  have h3i : Integrable (fun θ : ℝ => 2 * (n : ℝ) * ∑ k ∈ Finset.Icc 1 (n - 1),
      ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
        * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)))
      (volume.restrict Work.Spaces.Iθ) :=
    hSint.integrable.const_mul (2 * (n : ℝ))
  have hsumval : (∫ θ in Work.Spaces.Iθ, ∑ k ∈ Finset.Icc 1 (n - 1),
        ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
          * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)))
      = ∑ k ∈ Finset.Icc 1 (n - 1), ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Dth1Iter k (SinQ h) θ) ^ 2
              / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)) := by
    rw [MeasureTheory.integral_finsetSum (s := Finset.Icc 1 (n - 1))
      (fun k hk => (hCint k hk).integrable)]
    exact Finset.sum_congr rfl fun k _ => MeasureTheory.integral_const_mul _ _
  have eGval : (∫ θ in Work.Spaces.Iθ, G θ)
      = ∫ x, (fun θ : ℝ => 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2
              / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))) x
          + (fun θ : ℝ => 2 * (n : ℝ) * M ^ 2 * ((h θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) x
          + (fun θ : ℝ => 2 * (n : ℝ) * ∑ k ∈ Finset.Icc 1 (n - 1),
              ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
                * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))) x
        ∂(volume.restrict Work.Spaces.Iθ) := by
    rw [hG]
  have hthree := integral_three
    (fun θ : ℝ => 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2
      / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)))
    (fun θ : ℝ => 2 * (n : ℝ) * M ^ 2 * ((h θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
    (fun θ : ℝ => 2 * (n : ℝ) * ∑ k ∈ Finset.Icc 1 (n - 1),
      ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
        * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)))
    (volume.restrict Work.Spaces.Iθ) h1i h2i h3i
  have hcA : (∫ x, (fun θ : ℝ => 2 * ((Dth1Iter (n - 1) (deriv h) θ) ^ 2
        / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))) x ∂(volume.restrict Work.Spaces.Iθ))
      = 2 * (∫ θ in Work.Spaces.Iθ, (Dth1Iter (n - 1) (deriv h) θ) ^ 2
          / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)) :=
    MeasureTheory.integral_const_mul 2 _
  have hcB : (∫ x, (fun θ : ℝ => 2 * (n : ℝ) * M ^ 2 * ((h θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) x ∂(volume.restrict Work.Spaces.Iθ))
      = 2 * (n : ℝ) * M ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
    MeasureTheory.integral_const_mul (2 * (n : ℝ) * M ^ 2) _
  have hcC : (∫ x, (fun θ : ℝ => 2 * (n : ℝ) * ∑ k ∈ Finset.Icc 1 (n - 1),
        ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
          * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))) x
        ∂(volume.restrict Work.Spaces.Iθ))
      = 2 * (n : ℝ) * (∫ θ in Work.Spaces.Iθ, ∑ k ∈ Finset.Icc 1 (n - 1),
          ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
            * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))) :=
    MeasureTheory.integral_const_mul (2 * (n : ℝ)) _
  have hval : ∫ θ in Work.Spaces.Iθ, G θ
      = 2 * (∫ θ in Work.Spaces.Iθ, (Dth1Iter (n - 1) (deriv h) θ) ^ 2
            / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))
        + 2 * (n : ℝ) * M ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        + 2 * (n : ℝ) * (∫ θ in Work.Spaces.Iθ, ∑ k ∈ Finset.Icc 1 (n - 1),
            ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
              * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))) := by
    rw [eGval, hthree, hcA, hcB, hcC]
  -- bound the three terms of the right hand side
  have hsumid : (∑ k ∈ Finset.Icc 1 (n - 1), ((Nat.choose (n - 1) k : ℝ) * M) ^ 2 * Ck k)
      = M ^ 2 * ∑ k ∈ Finset.Icc 1 (n - 1), (Nat.choose (n - 1) k : ℝ) ^ 2 * Ck k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hb1 : 2 * (∫ θ in Work.Spaces.Iθ, (Dth1Iter (n - 1) (deriv h) θ) ^ 2
      / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)) ≤ 2 * RHS α n h := by
    have hh := le_RHS_term α n (n - 1) h (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    linarith
  have hb2 : 2 * (n : ℝ) * M ^ 2 * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ 2 * (n : ℝ) * M ^ 2 * CL * RHS α n h := by
    have hb := hCL2 h hsm h0 hp
    have hf := le_RHS_first α n h
    have h2 : (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ CL * RHS α n h := hb.trans (mul_le_mul_of_nonneg_left hf hCL.le)
    have hnn : 0 ≤ 2 * (n : ℝ) * M ^ 2 := by positivity
    calc 2 * (n : ℝ) * M ^ 2 * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ 2 * (n : ℝ) * M ^ 2 * (CL * RHS α n h) := mul_le_mul_of_nonneg_left h2 hnn
      _ = 2 * (n : ℝ) * M ^ 2 * CL * RHS α n h := by ring
  have hb3 : 2 * (n : ℝ) * (∫ θ in Work.Spaces.Iθ, ∑ k ∈ Finset.Icc 1 (n - 1),
        ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
          * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)))
      ≤ 2 * (n : ℝ) * M ^ 2
          * (∑ k ∈ Finset.Icc 1 (n - 1), (Nat.choose (n - 1) k : ℝ) ^ 2 * Ck k)
          * RHS α n h := by
    rw [hsumval]
    have hsum : (∑ k ∈ Finset.Icc 1 (n - 1),
          ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Dth1Iter k (SinQ h) θ) ^ 2
                / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)))
        ≤ (∑ k ∈ Finset.Icc 1 (n - 1), ((Nat.choose (n - 1) k : ℝ) * M) ^ 2 * Ck k)
            * RHS α n h := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk1 := hIH k hk h hsm h0 hp
      have hk2 : k ≤ n - 1 := (Finset.mem_Icc.mp hk).2
      have hknn : 0 ≤ ((Nat.choose (n - 1) k : ℝ) * M) ^ 2 := sq_nonneg _
      have hRk : RHS α k h ≤ RHS α n h := RHS_mono α h (by omega)
      calc ((Nat.choose (n - 1) k : ℝ) * M) ^ 2 * (LHS α k h)
          ≤ ((Nat.choose (n - 1) k : ℝ) * M) ^ 2 * (Ck k * RHS α k h) :=
            mul_le_mul_of_nonneg_left hk1 hknn
        _ ≤ ((Nat.choose (n - 1) k : ℝ) * M) ^ 2 * (Ck k * RHS α n h) := by
            refine mul_le_mul_of_nonneg_left ?_ hknn
            exact mul_le_mul_of_nonneg_left hRk (le_of_lt (hCkpos k hk))
        _ = ((Nat.choose (n - 1) k : ℝ) * M) ^ 2 * Ck k * RHS α n h := by ring
    have hnn : 0 ≤ 2 * (n : ℝ) := by positivity
    calc 2 * (n : ℝ) * (∑ k ∈ Finset.Icc 1 (n - 1),
          ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Dth1Iter k (SinQ h) θ) ^ 2
                / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)))
        ≤ 2 * (n : ℝ) * ((∑ k ∈ Finset.Icc 1 (n - 1),
            ((Nat.choose (n - 1) k : ℝ) * M) ^ 2 * Ck k) * RHS α n h) :=
          mul_le_mul_of_nonneg_left hsum hnn
      _ = 2 * (n : ℝ) * M ^ 2
            * (∑ k ∈ Finset.Icc 1 (n - 1), (Nat.choose (n - 1) k : ℝ) ^ 2 * Ck k)
            * RHS α n h := by rw [hsumid]; ring
  calc LHS α n h
      ≤ ∫ θ in Work.Spaces.Iθ, G θ := hmono
    _ = 2 * (∫ θ in Work.Spaces.Iθ, (Dth1Iter (n - 1) (deriv h) θ) ^ 2
              / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))
          + 2 * (n : ℝ) * M ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + 2 * (n : ℝ) * (∫ θ in Work.Spaces.Iθ, ∑ k ∈ Finset.Icc 1 (n - 1),
              ((Nat.choose (n - 1) k : ℝ) * M) ^ 2
                * ((Dth1Iter k (SinQ h) θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))) := hval
    _ ≤ (2 + 2 * (n : ℝ) * M ^ 2 *
          (CL + ∑ k ∈ Finset.Icc 1 (n - 1), (Nat.choose (n - 1) k : ℝ) ^ 2 * Ck k)) * RHS α n h := by
        linarith [hb1, hb2, hb3]



private lemma integral_mul_sq_le {F G : ℝ → ℝ}
    (hFnn : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ F θ)
    (hGnn : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ G θ)
    (hFint : Integrable (fun θ => F θ ^ 2) (volume.restrict Work.Spaces.Iθ))
    (hGint : Integrable (fun θ => G θ ^ 2) (volume.restrict Work.Spaces.Iθ))
    (hFmeas : AEStronglyMeasurable F (volume.restrict Work.Spaces.Iθ))
    (hGmeas : AEStronglyMeasurable G (volume.restrict Work.Spaces.Iθ)) :
    (∫ θ in Work.Spaces.Iθ, F θ * G θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, F θ ^ 2) * (∫ θ in Work.Spaces.Iθ, G θ ^ 2) := by
  have hpq : (2:ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hF2 : MemLp F (ENNReal.ofReal 2) (volume.restrict Work.Spaces.Iθ) := by
    rw [ENNReal.ofReal_ofNat]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hFmeas).mpr hFint
  have hG2 : MemLp G (ENNReal.ofReal 2) (volume.restrict Work.Spaces.Iθ) := by
    rw [ENNReal.ofReal_ofNat]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hGmeas).mpr hGint
  have h := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict Work.Spaces.Iθ)
      (p := 2) (q := 2) hpq hFnn hGnn hF2 hG2
  have h' : (∫ θ in Work.Spaces.Iθ, F θ * G θ) ≤
      (∫ θ in Work.Spaces.Iθ, F θ ^ 2) ^ (1/2:ℝ) *
        (∫ θ in Work.Spaces.Iθ, G θ ^ 2) ^ (1/2:ℝ) := by
    have h1 : (∫ θ in Work.Spaces.Iθ, F θ ^ (2:ℝ)) = (∫ θ in Work.Spaces.Iθ, F θ ^ 2) := by
      refine setIntegral_congr_fun Iθ_measurable fun θ _ => ?_
      rw [Real.rpow_ofNat]
    have h2 : (∫ θ in Work.Spaces.Iθ, G θ ^ (2:ℝ)) = (∫ θ in Work.Spaces.Iθ, G θ ^ 2) := by
      refine setIntegral_congr_fun Iθ_measurable fun θ _ => ?_
      rw [Real.rpow_ofNat]
    rw [h1, h2] at h
    exact h
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, F θ * G θ := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [hFnn, hGnn] with θ h1 h2
    exact mul_nonneg h1 h2
  have hA : 0 ≤ (∫ θ in Work.Spaces.Iθ, F θ ^ 2) :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hB : 0 ≤ (∫ θ in Work.Spaces.Iθ, G θ ^ 2) :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hsqrt : ((∫ θ in Work.Spaces.Iθ, F θ ^ 2) ^ (1/2:ℝ) *
        (∫ θ in Work.Spaces.Iθ, G θ ^ 2) ^ (1/2:ℝ)) ^ 2
      = (∫ θ in Work.Spaces.Iθ, F θ ^ 2) * (∫ θ in Work.Spaces.Iθ, G θ ^ 2) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
  have hmono : (∫ θ in Work.Spaces.Iθ, F θ * G θ) ^ 2
      ≤ ((∫ θ in Work.Spaces.Iθ, F θ ^ 2) ^ (1/2:ℝ) *
        (∫ θ in Work.Spaces.Iθ, G θ ^ 2) ^ (1/2:ℝ)) ^ 2 :=
    pow_le_pow_left₀ hnn h' 2
  rwa [hsqrt] at hmono

private lemma arith_key (p a b j : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hj : 0 ≤ j) (hp1 : p ≤ 1)
    (hcs : ((p+1)*a - b)^2 ≤ a*j) : 4*(a+b) ≤ j + 8*(1-p)*a + 16*b := by
  rcases eq_or_lt_of_le ha with ha' | ha'
  · subst ha'
    have hb' : b = 0 := by nlinarith [hcs, sq_nonneg b]
    subst hb'
    linarith
  · have hdiv : ((p+1)*a - b)^2 / a ≤ j := by
      rw [div_le_iff₀ ha']; linarith [hcs]
    have hmain : 4*(a+b) ≤ ((p+1)*a - b)^2/a + 8*(1-p)*a + 16*b := by
      have h2 : (((p+1)*a - b)^2/a + 8*(1-p)*a + 16*b) - 4*(a+b)
          = (b^2 + (1-p)*(5-p)*a^2 + (10-2*p)*a*b)/a := by
        field_simp
        ring
      have h3 : 0 ≤ (b^2 + (1-p)*(5-p)*a^2 + (10-2*p)*a*b)/a := by
        refine div_nonneg ?_ ha'.le
        have h4 : 0 ≤ (1-p)*(5-p)*a^2 :=
          mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg a)
        have h5 : 0 ≤ (10-2*p)*(a*b) := mul_nonneg (by linarith) (mul_nonneg ha hb)
        nlinarith [sq_nonneg b, h4, h5]
      linarith
    linarith [hmain, hdiv]

private theorem baseEstU :
    ∃ Cb : ℝ, 0 < Cb ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
      ∀ (h : ℝ → ℝ), SmoothSlice h → h 0 = 0 → h (Real.pi / 2) = 0 →
        LHS α 1 h ≤ Cb * RHS α 1 h := by
  refine ⟨3, by norm_num, ?_⟩
  intro α hα hα1 h hsm h0 hπ
  set γ : ℝ := Work.Spaces.gam α with hγdef
  have hγ1 : 1 < γ := by rw [hγdef]; exact Work.Spaces.one_lt_gam hα
  have hγle : γ ≤ 11/10 := by rw [hγdef, Work.Spaces.gam]; linarith
  have hγ2 : γ < 2 := by linarith
  have hγne : γ ≠ 2 := ne_of_lt hγ2
  have hgamne : Work.Spaces.gam α ≠ 2 := by rw [← hγdef]; exact hγne
  have hp0 : 0 ≤ 2 - γ := by linarith
  have hp1 : 2 - γ ≤ 1 := by linarith
  have hη0 : 0 < Work.Spaces.eta := Work.Spaces.eta_pos
  have hb : SliceBdd h := DivSinSliceBddEst h hsm h0 hπ
  obtain ⟨hIdA, hIA, hJA, hKA⟩ := DivSinIdentityA h hsm h0 hπ hb
  obtain ⟨hIdB, hB1, hB2, hB3, hB4, hB5, hB6, hB7⟩ := DivSinIdentityB α hα hα1 h hsm h0 hπ hb
  obtain hIBP := DivSinIBPWeight γ h hγ1 hγle hsm h0 hπ hb
  rw [← hγdef] at hIdB hB1 hB2 hB3 hB4 hB5 hB6 hB7
  have hLHS : LHS α 1 h = ∫ θ in Work.Spaces.Iθ,
      (deriv (SinQ h) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) := by
    rw [LHS]
    refine setIntegral_congr_fun Iθ_measurable fun θ hθ => ?_
    have hσnn : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
    simp only [Dth1Iter_succ, Dth1Iter_zero, Dth1]
    rw [mul_pow,
      show Real.sin (2 * θ) ^ 2 * (deriv (SinQ h) θ) ^ 2
          / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)
          = (deriv (SinQ h) θ) ^ 2
            * (Real.sin (2 * θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)) by ring,
      sq_div_rpow hσnn (Work.Spaces.gam α) hgamne]
  have hRHS1 : RHS α 1 h =
      (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta)
        + (∫ θ in Work.Spaces.Iθ,
            (deriv (deriv h) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) := by
    rw [RHS]
    congr 1
    rw [Finset.Icc_self, Finset.sum_singleton]
    refine setIntegral_congr_fun Iθ_measurable fun θ hθ => ?_
    have hσnn : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
    simp only [Dth1Iter_succ, Dth1Iter_zero, Dth1]
    rw [mul_pow,
      show Real.sin (2 * θ) ^ 2 * (deriv (deriv h) θ) ^ 2
          / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)
          = (deriv (deriv h) θ) ^ 2
            * (Real.sin (2 * θ) ^ 2 / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)) by ring,
      sq_div_rpow hσnn (Work.Spaces.gam α) hgamne]
  rw [hLHS, hRHS1]
  set A : ℝ := ∫ θ in Work.Spaces.Iθ,
      (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) * (deriv (SinQ h) θ) ^ 2 with hAdef
  set B : ℝ := ∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (4 - γ) * (deriv (SinQ h) θ) ^ 2 with hBdef
  set J : ℝ := ∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (4 - γ) * (deriv (deriv (SinQ h)) θ) ^ 2 with hJdef
  set Cc : ℝ := ∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (4 - γ) * (SinQ h θ) ^ 2 with hCcdef
  set Dq : ℝ := ∫ θ in Work.Spaces.Iθ,
      (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) * (SinQ h θ) ^ 2 with hDqdef
  set E : ℝ := ∫ θ in Work.Spaces.Iθ,
      (Real.cos (2 * θ)) ^ 2 * (SinQ h θ) ^ 2 * (Real.sin (2 * θ)) ^ (- Work.Spaces.eta) with hEdef
  set R1 : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta with hR1def
  set R1' : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (- Work.Spaces.eta) with hR1'def
  set R2 : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (deriv h) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) with hR2def
  set IA : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (SinQ h) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) with hIAdef
  set KA : ℝ := ∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) * (SinQ h θ) ^ 2 with hKAdef
  have hsplit : ∀ θ ∈ Work.Spaces.Iθ,
      (deriv (SinQ h) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
        = (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) * (deriv (SinQ h) θ) ^ 2
          + (Real.sin (2 * θ)) ^ (4 - γ) * (deriv (SinQ h) θ) ^ 2 := by
    intro θ hθ
    have hσ0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
    rcases eq_or_lt_of_le hσ0 with hh | hh
    · rw [← hh, Real.zero_rpow (show 2 - γ ≠ 0 by linarith),
        Real.zero_rpow (show 4 - γ ≠ 0 by linarith)]
      ring
    · have hs4 : (Real.sin (2 * θ)) ^ (4 - γ)
          = (Real.sin (2 * θ)) ^ (2:ℝ) * (Real.sin (2 * θ)) ^ (2 - γ) := by
        rw [show 4 - γ = 2 + (2 - γ) by ring, Real.rpow_add hh]
      have hcs : (Real.sin (2 * θ)) ^ 2 + (Real.cos (2 * θ)) ^ 2 = 1 :=
        Real.sin_sq_add_cos_sq (2 * θ)
      rw [hs4, Real.rpow_two]
      linear_combination (-((deriv (SinQ h) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))) * hcs
  have hAB : (∫ θ in Work.Spaces.Iθ,
        (deriv (SinQ h) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) = A + B := by
    rw [hAdef, hBdef, setIntegral_congr_fun Iθ_measurable hsplit]
    exact integral_add hB3 hB4
  have hIAn : 0 ≤ IA := by
    rw [hIAdef]
    exact setIntegral_nonneg Iθ_measurable fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _)
  have hKAn : 0 ≤ KA := by
    rw [hKAdef]
    exact setIntegral_nonneg Iθ_measurable fun θ hθ =>
      mul_nonneg (Real.rpow_nonneg (sin_two_nonneg hθ) _) (sq_nonneg _)
  have hAn : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg Iθ_measurable fun θ hθ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _)) (sq_nonneg _)
  have hBn : 0 ≤ B := by
    rw [hBdef]
    exact setIntegral_nonneg Iθ_measurable fun θ hθ =>
      mul_nonneg (Real.rpow_nonneg (sin_two_nonneg hθ) _) (sq_nonneg _)
  have hJn : 0 ≤ J := by
    rw [hJdef]
    exact setIntegral_nonneg Iθ_measurable fun θ hθ =>
      mul_nonneg (Real.rpow_nonneg (sin_two_nonneg hθ) _) (sq_nonneg _)
  have hCcn : 0 ≤ Cc := by
    rw [hCcdef]
    exact setIntegral_nonneg Iθ_measurable fun θ hθ =>
      mul_nonneg (Real.rpow_nonneg (sin_two_nonneg hθ) _) (sq_nonneg _)
  have hR1'n : 0 ≤ R1' := by
    rw [hR1'def]
    exact setIntegral_nonneg Iθ_measurable fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _)
  have hR2n : 0 ≤ R2 := by
    rw [hR2def]
    exact setIntegral_nonneg Iθ_measurable fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _)
  have hR1eq : R1 = R1' := by
    rw [hR1def, hR1'def]
    refine setIntegral_congr_fun Iθ_measurable fun θ hθ => ?_
    rw [div_eq_mul_inv, ← Real.rpow_neg (sin_two_nonneg hθ) Work.Spaces.eta]
  have h4ηE : 4 * Work.Spaces.eta * E ≤ R1' := by linarith [hIdA, hIAn, hKAn]
  have hDqE : Dq ≤ E := by
    rw [hDqdef, hEdef]
    refine integral_mono_of_nonneg ?_ hJA ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _))
        (sq_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      have hσ0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
      have hle : (Real.sin (2 * θ)) ^ (2 - γ) ≤ (Real.sin (2 * θ)) ^ (- Work.Spaces.eta) := by
        rcases eq_or_lt_of_le hσ0 with hh | hh
        · rw [← hh, Real.zero_rpow (show 2 - γ ≠ 0 by linarith),
            Real.zero_rpow (show -Work.Spaces.eta ≠ 0 by linarith)]
        · exact Real.rpow_le_rpow_of_exponent_ge hh (Real.sin_le_one _) (by linarith)
      calc (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) * (SinQ h θ) ^ 2
          = ((Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) * (SinQ h θ) ^ 2 := by ring
        _ ≤ ((Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (- Work.Spaces.eta)) * (SinQ h θ) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (sq_nonneg _)) (sq_nonneg _)
        _ = (Real.cos (2 * θ)) ^ 2 * (SinQ h θ) ^ 2 * (Real.sin (2 * θ)) ^ (- Work.Spaces.eta) := by
            ring
  have hJbound : J + 8 * (1 - (2 - γ)) * A + 16 * B ≤ R2 + 16 * (2 - γ) * (3 - γ) * E := by
    have h3γ : 0 ≤ 3 - γ := by linarith
    have hc1 : 0 ≤ 16 * (3 - γ) * Cc := by nlinarith [hCcn, h3γ]
    have hc2 : 0 ≤ 16 * (2 - γ) * (3 - γ) * (E - Dq) := by
      have hh := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) hp0) h3γ)
        (sub_nonneg.mpr hDqE)
      linarith [hh]
    have hgg : 8 * (γ - 1) * A = 8 * (1 - (2 - γ)) * A := by ring
    linarith [hIdB, hc1, hc2, hgg]
  -- Cauchy–Schwarz
  have hCS : ((3 - γ) * A - B) ^ 2 ≤ A * J := by
    set F : ℝ → ℝ := fun θ => |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ ((2 - γ) / 2)
      * |deriv (SinQ h) θ| with hF
    set G : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ ((2 - γ) / 2 + 1)
      * |deriv (deriv (SinQ h)) θ| with hG
    have hFnn : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ F θ := by
      filter_upwards [ae_restrict_mem Iθ_measurable] with θ hθ
      rw [hF]
      exact mul_nonneg (mul_nonneg (abs_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg hθ) _)) (abs_nonneg _)
    have hGnn : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ G θ := by
      filter_upwards [ae_restrict_mem Iθ_measurable] with θ hθ
      rw [hG]
      exact mul_nonneg (Real.rpow_nonneg (sin_two_nonneg hθ) _) (abs_nonneg _)
    have hFmeas : AEStronglyMeasurable F (volume.restrict Work.Spaces.Iθ) := by
      rw [hF]
      exact (((Real.continuous_cos.comp (by fun_prop : Continuous fun θ : ℝ => 2 * θ)).abs.measurable.mul
        (measurable_sin_two_rpow ((2 - γ) / 2) (by linarith))).mul
          (measurable_deriv (SinQ h)).abs).aestronglyMeasurable
    have hGmeas : AEStronglyMeasurable G (volume.restrict Work.Spaces.Iθ) := by
      rw [hG]
      exact ((measurable_sin_two_rpow ((2 - γ) / 2 + 1) (by linarith)).mul
        (measurable_deriv (deriv (SinQ h))).abs).aestronglyMeasurable
    have hsq1 : ∀ θ ∈ Work.Spaces.Iθ, (Real.sin (2 * θ) ^ ((2 - γ) / 2)) ^ 2
        = Real.sin (2 * θ) ^ (2 - γ) := by
      intro θ hθ
      rcases eq_or_lt_of_le (sin_two_nonneg hθ) with hh | hh
      · rw [← hh, Real.zero_rpow (show (2 - γ) / 2 ≠ 0 by linarith),
          Real.zero_rpow (show 2 - γ ≠ 0 by linarith)]
        norm_num
      · rw [sq, ← Real.rpow_add hh ((2 - γ) / 2) ((2 - γ) / 2)]
        congr 1; ring
    have hsq2 : ∀ θ ∈ Work.Spaces.Iθ, (Real.sin (2 * θ) ^ ((2 - γ) / 2 + 1)) ^ 2
        = Real.sin (2 * θ) ^ (4 - γ) := by
      intro θ hθ
      rcases eq_or_lt_of_le (sin_two_nonneg hθ) with hh | hh
      · rw [← hh, Real.zero_rpow (show (2 - γ) / 2 + 1 ≠ 0 by linarith),
          Real.zero_rpow (show 4 - γ ≠ 0 by linarith)]
        norm_num
      · rw [sq, ← Real.rpow_add hh ((2 - γ) / 2 + 1) ((2 - γ) / 2 + 1)]
        congr 1; ring
    have hprod : ∀ θ ∈ Work.Spaces.Iθ,
        Real.sin (2 * θ) ^ ((2 - γ) / 2) * Real.sin (2 * θ) ^ ((2 - γ) / 2 + 1)
        = Real.sin (2 * θ) ^ (3 - γ) := by
      intro θ hθ
      rcases eq_or_lt_of_le (sin_two_nonneg hθ) with hh | hh
      · rw [← hh, Real.zero_rpow (show (2 - γ) / 2 ≠ 0 by linarith),
          Real.zero_rpow (show (2 - γ) / 2 + 1 ≠ 0 by linarith),
          Real.zero_rpow (show 3 - γ ≠ 0 by linarith)]
        norm_num
      · rw [← Real.rpow_add hh ((2 - γ) / 2) ((2 - γ) / 2 + 1)]
        congr 1; ring
    have hpe1 : ∀ θ ∈ Work.Spaces.Iθ, F θ ^ 2
        = (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) * (deriv (SinQ h) θ) ^ 2 := by
      intro θ hθ
      have h2 := hsq1 θ hθ
      rw [hF, show (|Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ ((2 - γ) / 2)
            * |deriv (SinQ h) θ|) ^ 2
          = |Real.cos (2 * θ)| ^ 2 * ((Real.sin (2 * θ)) ^ ((2 - γ) / 2)) ^ 2
            * |deriv (SinQ h) θ| ^ 2 by ring, h2, sq_abs, sq_abs]
    have hpe2 : ∀ θ ∈ Work.Spaces.Iθ, G θ ^ 2
        = (Real.sin (2 * θ)) ^ (4 - γ) * (deriv (deriv (SinQ h)) θ) ^ 2 := by
      intro θ hθ
      have h2 := hsq2 θ hθ
      rw [hG, show ((Real.sin (2 * θ)) ^ ((2 - γ) / 2 + 1) * |deriv (deriv (SinQ h)) θ|) ^ 2
          = ((Real.sin (2 * θ)) ^ ((2 - γ) / 2 + 1)) ^ 2 * |deriv (deriv (SinQ h)) θ| ^ 2 by ring,
          h2, sq_abs]
    have hpe3 : ∀ θ ∈ Work.Spaces.Iθ, F θ * G θ
        = |Real.sin (2 * θ) ^ (3 - γ) * Real.cos (2 * θ) * deriv (SinQ h) θ
            * deriv (deriv (SinQ h)) θ| := by
      intro θ hθ
      have h2 := hprod θ hθ
      have habs : |Real.sin (2 * θ) ^ (3 - γ) * Real.cos (2 * θ) * deriv (SinQ h) θ
            * deriv (deriv (SinQ h)) θ|
          = Real.sin (2 * θ) ^ (3 - γ) * |Real.cos (2 * θ)| * |deriv (SinQ h) θ|
            * |deriv (deriv (SinQ h)) θ| := by
        rw [show Real.sin (2 * θ) ^ (3 - γ) * Real.cos (2 * θ) * deriv (SinQ h) θ
              * deriv (deriv (SinQ h)) θ
            = Real.sin (2 * θ) ^ (3 - γ) * (Real.cos (2 * θ)
                * (deriv (SinQ h) θ * deriv (deriv (SinQ h)) θ)) by ring,
          abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (sin_two_nonneg hθ) (3 - γ))]
        ring
      rw [hF, hG, habs, show |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ ((2 - γ) / 2)
            * |deriv (SinQ h) θ| * ((Real.sin (2 * θ)) ^ ((2 - γ) / 2 + 1)
              * |deriv (deriv (SinQ h)) θ|)
          = (Real.sin (2 * θ) ^ ((2 - γ) / 2) * Real.sin (2 * θ) ^ ((2 - γ) / 2 + 1))
            * (|Real.cos (2 * θ)| * (|deriv (SinQ h) θ| * |deriv (deriv (SinQ h)) θ|)) by ring,
          h2]
      ring
    have hFint : Integrable (fun θ => F θ ^ 2) (volume.restrict Work.Spaces.Iθ) :=
      (hB3.congr_fun (fun θ hθ => (hpe1 θ hθ).symm) Iθ_measurable).integrable
    have hGint : Integrable (fun θ => G θ ^ 2) (volume.restrict Work.Spaces.Iθ) :=
      (hB2.congr_fun (fun θ hθ => (hpe2 θ hθ).symm) Iθ_measurable).integrable
    have hmain := integral_mul_sq_le hFnn hGnn hFint hGint hFmeas hGmeas
    have hIF2 : (∫ θ in Work.Spaces.Iθ, F θ ^ 2) = A :=
      (setIntegral_congr_fun Iθ_measurable hpe1).trans hAdef.symm
    have hIG2 : (∫ θ in Work.Spaces.Iθ, G θ ^ 2) = J :=
      (setIntegral_congr_fun Iθ_measurable hpe2).trans hJdef.symm
    rw [hIF2, hIG2] at hmain
    -- integrability of `F * G` (hence of `|f|`)
    have hFGint : Integrable (fun θ => F θ * G θ) (volume.restrict Work.Spaces.Iθ) := by
      have hpt : ∀ θ, F θ * G θ ≤ (1/2) * (F θ ^ 2 + G θ ^ 2) := by
        intro θ
        have h2' := two_mul_le_add_sq (F θ) (G θ)
        linarith
      refine Integrable.mono' ((hFint.add hGint).const_mul (1/2)) (hFmeas.mul hGmeas) ?_
      filter_upwards [hFnn, hGnn] with θ h1 h2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2)]
      exact hpt θ
    -- the two sides of the IBP identity
    have hIBP' : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (3 - γ) * Real.cos (2 * θ)
        * deriv (SinQ h) θ * deriv (deriv (SinQ h)) θ) = B - (3 - γ) * A := by
      rw [hIBP]; ring
    have hleabs : (∫ θ in Work.Spaces.Iθ, |(Real.sin (2 * θ)) ^ (3 - γ) * Real.cos (2 * θ)
        * deriv (SinQ h) θ * deriv (deriv (SinQ h)) θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, F θ * G θ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => abs_nonneg _) hFGint ?_
      filter_upwards [ae_restrict_mem Iθ_measurable] with θ hθ
      rw [hpe3 θ hθ]
    have hsq : ((3 - γ) * A - B) ^ 2 ≤ (∫ θ in Work.Spaces.Iθ, F θ * G θ) ^ 2 := by
      have h1 : |(3 - γ) * A - B| = |∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (3 - γ)
          * Real.cos (2 * θ) * deriv (SinQ h) θ * deriv (deriv (SinQ h)) θ| := by
        rw [hIBP', abs_sub_comm]
      have h2 : |(3 - γ) * A - B| ≤ ∫ θ in Work.Spaces.Iθ, F θ * G θ := by
        rw [h1]
        exact le_trans MeasureTheory.abs_integral_le_integral_abs hleabs
      have h3 : ((3 - γ) * A - B) ^ 2 = |(3 - γ) * A - B| ^ 2 := (sq_abs _).symm
      rw [h3]
      exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    exact le_trans hsq hmain
  -- the arithmetic
  have harith : 4 * (A + B) ≤ J + 8 * (1 - (2 - γ)) * A + 16 * B := by
    refine arith_key (2 - γ) A B J hAn hBn hJn hp1 ?_
    rw [show (2 - γ) + 1 = 3 - γ by ring]
    exact hCS
  -- the weights
  have hEbound : E ≤ R1' / (4 * Work.Spaces.eta) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * Work.Spaces.eta)]
    linarith [h4ηE]
  have hcoef : (2 - γ) * (3 - γ) / Work.Spaces.eta ≤ 3 := by
    have h1 : (2 - γ) * (3 - γ) ≤ 2 := by nlinarith [hp0, hp1]
    have h2 : (2 - γ) * (3 - γ) / Work.Spaces.eta ≤ 2 / Work.Spaces.eta :=
      div_le_div_of_nonneg_right h1 hη0.le
    have h3 : 2 / Work.Spaces.eta ≤ 3 := by
      rw [div_le_iff₀ hη0]
      norm_num [Work.Spaces.eta]
    linarith
  have hcoef0 : 0 ≤ 4 * ((2 - γ) * (3 - γ)) := by nlinarith [hp0]
  have hfinal : A + B ≤ 3 * (R1' + R2) := by
    have h42 : A + B ≤ (R2 + 16 * (2 - γ) * (3 - γ) * E) / 4 := by
      have := le_trans harith hJbound
      linarith [this]
    have hstep : (R2 + 16 * (2 - γ) * (3 - γ) * E) / 4
        ≤ R2 / 4 + ((2 - γ) * (3 - γ) / Work.Spaces.eta) * R1' := by
      have hE' : 4 * ((2 - γ) * (3 - γ)) * E ≤ 4 * ((2 - γ) * (3 - γ)) * (R1' / (4 * Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_left hEbound (by positivity : (0:ℝ) ≤ 4 * ((2 - γ) * (3 - γ)))
      have hrw1 : (R2 + 16 * (2 - γ) * (3 - γ) * E) / 4
          = R2 / 4 + 4 * ((2 - γ) * (3 - γ)) * E := by ring
      have hrw2 : 4 * ((2 - γ) * (3 - γ)) * (R1' / (4 * Work.Spaces.eta))
          = ((2 - γ) * (3 - γ) / Work.Spaces.eta) * R1' := by field_simp
      rw [hrw1, ← hrw2]
      linarith [hE']
    have hstep2 : R2 / 4 + ((2 - γ) * (3 - γ) / Work.Spaces.eta) * R1' ≤ 3 * (R1' + R2) := by
      have hcoefR : ((2 - γ) * (3 - γ) / Work.Spaces.eta) * R1' ≤ 3 * R1' :=
        mul_le_mul_of_nonneg_right hcoef hR1'n
      nlinarith [hcoefR, hR1'n, hR2n]
    linarith [h42, hstep, hstep2]
  rw [hAB, hR1eq]
  exact hfinal



/-! ## 9b. The induction constants (independent of `α`) and the assembly -/

/-- The four constants of the induction.  They are explicit expressions in the uniform base
constant `Cb`, the `L²`-constant `CL` and the angular bound `M`, hence independent of `α`. -/
private def KC1 (Cb : ℝ) : ℝ := Cb

/-- `C_2`. -/
private def KC2 (Cb CL M : ℝ) : ℝ := 2 + 2 * (2 : ℝ) * M ^ 2 * (CL + KC1 Cb)

/-- `C_3`. -/
private def KC3 (Cb CL M : ℝ) : ℝ := 2 + 2 * (3 : ℝ) * M ^ 2 * (CL + 4 * KC1 Cb + KC2 Cb CL M)

/-- `C_4`. -/
private def KC4 (Cb CL M : ℝ) : ℝ :=
  2 + 2 * (4 : ℝ) * M ^ 2 * (CL + 9 * KC1 Cb + 9 * KC2 Cb CL M + KC3 Cb CL M)

/-- The sequence `C_1, C_2, C_3, C_4` (and `0` elsewhere). -/
private def CkFn (Cb CL M : ℝ) : ℕ → ℝ
  | 1 => KC1 Cb
  | 2 => KC2 Cb CL M
  | 3 => KC3 Cb CL M
  | 4 => KC4 Cb CL M
  | _ => 0

private theorem iter_bound_unif :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ),
      SmoothSlice h → h 0 = 0 → h (Real.pi / 2) = 0 →
        ∀ i ∈ Finset.Icc 1 4, LHS α i h ≤ C * RHS α i h := by
  classical
  obtain ⟨Cb, hCbpos, hCb⟩ := baseEstU
  obtain ⟨CL, hCLpos, hCL⟩ := DivSinL2EstUnif
  obtain ⟨M, hMpos, hM0, hMk⟩ := DivSinPhiBound
  have hK1pos : 0 < KC1 Cb := hCbpos
  have hK2pos : 0 < KC2 Cb CL M := by
    rw [KC2, KC1]
    have hh : 0 < 2 * (2 : ℝ) * M ^ 2 * (CL + Cb) := by positivity
    linarith
  have hK3pos : 0 < KC3 Cb CL M := by
    rw [KC3]
    have hh : 0 < 2 * (3 : ℝ) * M ^ 2 * (CL + 4 * KC1 Cb + KC2 Cb CL M) := by positivity
    linarith
  have hK4pos : 0 < KC4 Cb CL M := by
    rw [KC4]
    have hh : 0 < 2 * (4 : ℝ) * M ^ 2 * (CL + 9 * KC1 Cb + 9 * KC2 Cb CL M + KC3 Cb CL M) := by
      positivity
    linarith
  refine ⟨KC1 Cb + KC2 Cb CL M + KC3 Cb CL M + KC4 Cb CL M, by linarith, ?_⟩
  intro α hα hα1 h hsm h0 hπ i hi
  have key : ∀ n, 1 ≤ n → n ≤ 4 → ∀ (h : ℝ → ℝ), SmoothSlice h → h 0 = 0 →
      h (Real.pi / 2) = 0 → LHS α n h ≤ CkFn Cb CL M n * RHS α n h := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih hn1 hn4 h hsm h0 hπ
    rcases eq_or_lt_of_le hn1 with h1 | h2
    · rw [← h1]
      have hCk1 : CkFn Cb CL M 1 = KC1 Cb := rfl
      rw [hCk1]
      exact hCb α hα hα1 h hsm h0 hπ
    · have hCkpos : ∀ k ∈ Finset.Icc 1 (n - 1), 0 < CkFn Cb CL M k := by
        intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hk2 : k ≤ n - 1 := (Finset.mem_Icc.mp hk).2
        have hk3 : k ≤ 3 := by omega
        interval_cases k
        · exact hK1pos
        · exact hK2pos
        · exact hK3pos
      have hIH : ∀ k ∈ Finset.Icc 1 (n - 1), ∀ h : ℝ → ℝ, SmoothSlice h → h 0 = 0 →
          h (Real.pi / 2) = 0 → LHS α k h ≤ CkFn Cb CL M k * RHS α k h := by
        intro k hk h' hsm' h0' hπ'
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hk2 : k ≤ n - 1 := (Finset.mem_Icc.mp hk).2
        exact ih k (by omega) hk1 (by omega) h' hsm' h0' hπ'
      have hstep := step_lemma α hα hα1 M CL hMpos hCLpos hM0 hMk (hCL α hα hα1) n h2 hn4
        (CkFn Cb CL M) hCkpos hIH h hsm h0 hπ
      have hCkn : CkFn Cb CL M n = 2 + 2 * (n : ℝ) * M ^ 2 *
          (CL + ∑ k ∈ Finset.Icc 1 (n - 1), (Nat.choose (n - 1) k : ℝ) ^ 2 * CkFn Cb CL M k) := by
        interval_cases n
        · rw [Finset.Icc_self, Finset.sum_singleton]
          simp only [CkFn, KC2, KC1, Nat.choose_self, Nat.cast_one, one_pow, one_mul]
          ring
        · rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 1 + 1), Finset.Icc_self,
              Finset.sum_singleton]
          simp only [CkFn, KC3, KC2, KC1, Nat.choose_self, Nat.cast_one, one_pow, one_mul,
            Nat.choose_one_right]
          ring_nf
        · rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 2 + 1),
              Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 1 + 1), Finset.Icc_self,
              Finset.sum_singleton]
          have hc : (Nat.choose 3 2 : ℝ) = 3 := by norm_num
          simp only [CkFn, KC4, KC3, KC2, KC1, hc, Nat.choose_self, Nat.cast_one, one_pow,
            one_mul, Nat.choose_one_right]
          ring
      rw [hCkn]
      exact hstep
  rcases Finset.mem_Icc.mp hi with ⟨hi1, hi4⟩
  refine le_trans (key i hi1 hi4 h hsm h0 hπ)
    (mul_le_mul_of_nonneg_right ?_ (RHS_nonneg α i h))
  interval_cases i
  · simp only [CkFn]; linarith
  · simp only [CkFn]; linarith
  · simp only [CkFn]; linarith
  · simp only [CkFn]; linarith


theorem DivSinIterUnif :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
      ∀ (h : ℝ → ℝ), Work.Elliptic.SmoothSlice h → h 0 = 0 → h (Real.pi / 2) = 0 →
        ∀ i ∈ Finset.Icc 1 4,
          (∫ θ in Work.Spaces.Iθ,
              (Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ) ^ 2
                / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))
            ≤ C * ((∫ θ in Work.Spaces.Iθ,
                      (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta)
              + ∑ m ∈ Finset.Icc 1 i,
                  (∫ θ in Work.Spaces.Iθ,
                    (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                      / (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))) := by
  obtain ⟨C, hCpos, hC⟩ := iter_bound_unif
  exact ⟨C, hCpos, fun α hα hα1 h hsm h0 hπ i hi => hC α hα hα1 h hsm h0 hπ i hi⟩

end Work.Elliptic
