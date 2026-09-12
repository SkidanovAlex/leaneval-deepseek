import Mathlib
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.poels_dio_main
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.poels_opt_lower

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open NNReal ENNReal
open scoped Real

set_option autoImplicit false

noncomputable section

/-- The naive height appearing in the statement: maximal absolute value of an integer
coefficient of the primitive integer polynomial obtained from the minimal polynomial
over `ℚ` by clearing denominators. -/
def poelsHeight (α : ℂ) : ℕ :=
  let p := minpoly ℚ α
  let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val)
  Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs)

/-- `n / (2 - log 2)` written as in the statement. -/
def poelsLam (n : ℕ) : ℝ := (1 / (2 - Real.log 2)) * n

/-- The approximating set from the statement (with `poelsHeight` in place of the inline
expression). -/
def poelsSet (n : ℕ) (ξ : ℝ) (ω : ℝ) : Set ℂ :=
  {α : ℂ | IsAlgebraic ℚ α ∧ Polynomial.natDegree (minpoly ℚ α) ≤ n ∧
      0 < ‖(ξ : ℂ) - α‖ ∧
      ‖(ξ : ℂ) - α‖ ≤ ((poelsHeight α : ℕ) : ℝ) ^ (-ω - 1)}

/-- Any algebraic number has height at least `1`. -/
lemma poelsHeight_one_le (α : ℂ) (hα : IsAlgebraic ℚ α) : 1 ≤ poelsHeight α := by
  classical
  let p : Polynomial ℚ := minpoly ℚ α
  let D : ℕ := Multiset.lcm (Multiset.map (fun j ↦ (p.coeff j).den) p.support.val)
  change 1 ≤ Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs)
  have hInt : IsIntegral ℚ α := by
    exact (isAlgebraic_iff_isIntegral).1 hα
  have hp_ne : p ≠ 0 := by
    dsimp [p]
    exact minpoly.ne_zero hInt
  have hs : p.support.Nonempty := Polynomial.support_nonempty.2 hp_ne
  rcases hs with ⟨i, hi⟩
  have hD_ne0 : D ≠ 0 := by
    dsimp [D]
    have hnot : (0 : ℕ) ∉ Multiset.map (fun j ↦ (p.coeff j).den) p.support.val := by
      intro hz
      rw [Multiset.mem_map] at hz
      rcases hz with ⟨j, hj, hj0⟩
      have hd : 0 < (p.coeff j).den := Rat.den_pos (p.coeff j)
      omega
    exact (Multiset.lcm_ne_zero_iff _).2 hnot
  have hci : p.coeff i ≠ 0 := (Polynomial.mem_support_iff).mp hi
  have hprod_ne : (D * p.coeff i : ℚ) ≠ 0 := by
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD_ne0
    exact mul_ne_zero hDq hci
  have hnum : (D * p.coeff i).num ≠ 0 := Rat.num_ne_zero.mpr hprod_ne
  have hf : 1 ≤ (D * p.coeff i).num.natAbs := by
    have hpos : 0 < (D * p.coeff i).num.natAbs := Int.natAbs_pos.mpr hnum
    omega
  have hle : (D * p.coeff i).num.natAbs ≤
      Finset.sup p.support (fun j ↦ (D * p.coeff j).num.natAbs) := by
    exact Finset.le_sup (f := fun j ↦ (D * p.coeff j).num.natAbs) hi
  exact le_trans hf hle

/-- If arbitrarily large heights occur among elements of `poelsSet`, then `poelsSet` is infinite
(because an infinite family cannot... a finite set has bounded heights). -/
lemma poelsUnboundedInfinite {n : ℕ} {ξ : ℝ} {ω : ℝ}
    (h : ∀ N : ℕ, ∃ α : ℂ, α ∈ poelsSet n ξ ω ∧ N ≤ poelsHeight α) : (poelsSet n ξ ω).Infinite := by
  classical
  rw [Set.Infinite]
  intro hfin
  let F : Finset ℂ := hfin.toFinset
  let M : ℕ := F.sup (fun α => poelsHeight α)
  have hmemF : ∀ ⦃α : ℂ⦄, α ∈ poelsSet n ξ ω → α ∈ F := by
    intro α hα
    dsimp [F]
    exact hfin.mem_toFinset.mpr hα
  have hle : ∀ ⦃α : ℂ⦄, α ∈ poelsSet n ξ ω → poelsHeight α ≤ M := by
    intro α hα
    dsimp [M]
    exact Finset.le_sup (f := fun α => poelsHeight α) (hmemF hα)
  obtain ⟨α, hα, hN⟩ := h (M + 1)
  have hM : poelsHeight α ≤ M := hle hα
  omega

/-- The assembly: given the two main ingredients (`poels_dio_main`, the Sections 3-6
construction, and `poels_opt_lower`, the Sections 7-8 optimization lower bound), every
`ω < (1 / (2 - log 2)) * n` admits infinitely many good approximations. -/
lemma poels_exists_infinite (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ)
    (ω : ℝ) (hω0 : 0 < ω) (hω : ω < (1 / (2 - Real.log 2)) * n) :
    {α : ℂ | IsAlgebraic ℚ α ∧ Polynomial.natDegree (minpoly ℚ α) ≤ n ∧
      0 < ‖(ξ : ℂ) - α‖ ∧
      ‖(ξ : ℂ) - α‖ ≤
        ((let p := minpoly ℚ α;
          let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
          Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ) ^ (- ω - 1)}.Infinite := by
  classical
  have _hω0pos : 0 < ω := hω0
  have hω' : ω < poelsLam n := by
    simpa [poelsLam] using hω
  -- pick η = (poelsLam n - ω)/2 > 0, then ε := η/2
  let η : ℝ := (poelsLam n - ω) / 2
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (sub_pos.mpr hω') (by norm_num)
  let ε : ℝ := η / 2
  have hε : 0 < ε := by
    dsimp [ε, η]
    positivity
  obtain ⟨C, hC1, hC⟩ := poels_dio_main n hn ξ hξ ε hε
  let d : ℝ := poelsLam n - η - ω
  have hd : 0 < d := by
    dsimp [d, η]
    have hsub : 0 < poelsLam n - ω := sub_pos.mpr hω'
    linarith
  have hCnonneg : 0 ≤ C := le_trans zero_le_one hC1
  -- unbounded heights inside poelsSet
  have hUnb : ∀ N0 : ℕ, ∃ α : ℂ, α ∈ poelsSet n ξ ω ∧ N0 ≤ poelsHeight α := by
    intro N0
    let Hc : ℝ := C ^ (1 / d)
    let Nt : ℕ := Nat.ceil Hc
    let h1 : ℕ := max N0 Nt
    obtain ⟨x, a, α, hxn, hA, hAlg, hDeg, hpos, hH, hBnd⟩ := hC h1
    let F : ℝ :=
        (if h : (Finset.Icc 2 (n + 1)).Nonempty then
           (Finset.Icc 2 (n + 1)).sup' h (fun k =>
             (2 * x - 2 * (n - k + 1) - (∑ i ∈ Finset.Icc 2 k, a i)) / a k)
         else 0)
    have hF : poelsLam n ≤ F := by
      dsimp [F]
      exact poels_opt_lower n hn x hxn a hA
    let H : ℝ := (poelsHeight α : ℝ)
    have hHge1 : 1 ≤ H := by
      dsimp [H]
      exact_mod_cast poelsHeight_one_le α hAlg
    have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hHge1
    have hHc_le_H : Hc ≤ H := by
      have hNt : Hc ≤ (Nt : ℝ) := by exact_mod_cast Nat.le_ceil Hc
      have hNt_le_h1 : (Nt : ℝ) ≤ (h1 : ℝ) := by
        dsimp [h1]
        exact_mod_cast le_max_right N0 Nt
      have hh1_le_H : (h1 : ℝ) ≤ H := by
        dsimp [H]
        exact hH
      exact le_trans hNt (le_trans hNt_le_h1 hh1_le_H)
    have hC_le_Hd : C ≤ H ^ d := by
      have hpow1 : (Hc ^ d : ℝ) ≤ H ^ d := by
        refine Real.rpow_le_rpow ?_ hHc_le_H hd.le
        dsimp [Hc]
        exact Real.rpow_nonneg hCnonneg (1 / d)
      have hpow2 : Hc ^ d = C := by
        dsimp [Hc]
        calc
          (C ^ (1 / d)) ^ d = C ^ ((1 / d) * d) := by rw [Real.rpow_mul hCnonneg]
          _ = C ^ (1 : ℝ) := by
            congr 1
            have hdne : d ≠ 0 := ne_of_gt hd
            field_simp [hdne]
          _ = C := by rw [Real.rpow_one]
      rwa [hpow2] at hpow1
    have hBnd2 : ‖(ξ : ℂ) - α‖ ≤ (poelsHeight α : ℝ) ^ (-ω - 1) := by
      calc
        ‖(ξ : ℂ) - α‖ ≤ C * (poelsHeight α : ℝ) ^ (-F - 1 + 2 * ε) := by
          simpa [F, poelsHeight] using hBnd
        _ = C * H ^ (-F - 1 + 2 * ε) := by
          dsimp [H]
        _ ≤ C * H ^ (-(poelsLam n) - 1 + η) := by
          apply mul_le_mul_of_nonneg_left ?_ hCnonneg
          apply Real.rpow_le_rpow_of_exponent_le hHge1
          have h2e : 2 * ε = η := by
            dsimp [ε, η]
            ring
          have hFle : poelsLam n ≤ F := hF
          linarith
        _ = C * H ^ (-(poelsLam n - η) - 1) := by
          congr 1
          congr 1
          ring
        _ ≤ H ^ (-ω - 1) := by
          have hmul : C * H ^ (-(poelsLam n - η) - 1) ≤ (H ^ d) * H ^ (-(poelsLam n - η) - 1) := by
            exact mul_le_mul_of_nonneg_right hC_le_Hd
              (Real.rpow_nonneg (le_of_lt hHpos) (-(poelsLam n - η) - 1))
          calc
            C * H ^ (-(poelsLam n - η) - 1) ≤ (H ^ d) * H ^ (-(poelsLam n - η) - 1) := hmul
            _ = H ^ (d + (-(poelsLam n - η) - 1)) := by rw [Real.rpow_add hHpos]
            _ = H ^ (-ω - 1) := by
              congr 1
              dsimp [d, η]
              ring
    have hN0_le_H : (N0 : ℝ) ≤ H := by
      have hN0_le_h1 : (N0 : ℝ) ≤ (h1 : ℝ) := by
        dsimp [h1]
        exact_mod_cast le_max_left N0 Nt
      exact le_trans hN0_le_h1 hH
    have hN0_le : N0 ≤ poelsHeight α := by
      dsimp [H] at hN0_le_H
      exact_mod_cast hN0_le_H
    refine ⟨α, ?_, ?_⟩
    · exact ⟨hAlg, hDeg, hpos, hBnd2⟩
    · exact hN0_le
  -- convert from poelsSet (with poelsHeight) to the set in the statement
  have hInf : (poelsSet n ξ ω).Infinite := poelsUnboundedInfinite hUnb
  simpa [poelsSet, poelsHeight] using hInf

end

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree
