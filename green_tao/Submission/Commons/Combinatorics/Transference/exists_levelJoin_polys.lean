import Mathlib
import Submission.Commons.Analysis.Approximation.exists_poly_weight_family
import Submission.Commons.Combinatorics.Transference.poly_lemma_abstract
import Submission.Commons.Combinatorics.Transference.floor_levIdx_mem_Icc

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-! ## The fixed trapezoid profile `ψ`

`ψ_η u = min 1 (max 0 (u/η + 1)) * min 1 (max 0 ((1 + η - u)/η))` equals `1` on `[0,1]`,
vanishes outside `[-η, 1+η]`, is continuous and takes values in `[0,1]`.  It is the common
shape of all the level-profile bumps: with `u = (t - α - ε·n)/ε` it is the function used to
approximate the indicator of the level set with index `n`. -/

noncomputable def levelJoinPsi (η : ℝ) (u : ℝ) : ℝ :=
  min 1 (max 0 ((u + η) / η)) * min 1 (max 0 ((1 + η - u) / η))

private lemma continuous_levelJoinPsi (η : ℝ) : Continuous (levelJoinPsi η) := by
  unfold levelJoinPsi
  apply Continuous.mul
  · exact Continuous.min continuous_const
      (Continuous.max continuous_const ((continuous_id.add continuous_const).div_const η))
  · exact Continuous.min continuous_const
      (Continuous.max continuous_const
        (((continuous_const.add continuous_const).sub continuous_id).div_const η))

private lemma levelJoinPsi_nonneg (η u : ℝ) : 0 ≤ levelJoinPsi η u := by
  unfold levelJoinPsi
  exact mul_nonneg (le_min zero_le_one (le_max_left 0 _))
    (le_min zero_le_one (le_max_left 0 _))

private lemma levelJoinPsi_le_one (η u : ℝ) : levelJoinPsi η u ≤ 1 := by
  unfold levelJoinPsi
  have h1 : min 1 (max 0 ((u + η) / η)) ≤ 1 := min_le_left _ _
  have h2 : min 1 (max 0 ((1 + η - u) / η)) ≤ 1 := min_le_left _ _
  have h2' : 0 ≤ min 1 (max 0 ((1 + η - u) / η)) := le_min zero_le_one (le_max_left 0 _)
  calc min 1 (max 0 ((u + η) / η)) * min 1 (max 0 ((1 + η - u) / η))
      ≤ 1 * 1 := mul_le_mul h1 h2 h2' zero_le_one
    _ = 1 := by norm_num

private lemma levelJoinPsi_eq_one {η u : ℝ} (hη : 0 < η) (h1 : 0 ≤ u) (h2 : u ≤ 1) :
    levelJoinPsi η u = 1 := by
  have hx : 1 ≤ (u + η) / η := by rw [le_div_iff₀ hη]; linarith
  have hy : 1 ≤ (1 + η - u) / η := by rw [le_div_iff₀ hη]; linarith
  unfold levelJoinPsi
  rw [max_eq_right (le_trans zero_le_one hx), min_eq_left hx,
    max_eq_right (le_trans zero_le_one hy), min_eq_left hy, mul_one]

private lemma levelJoinPsi_eq_zero_of_le {η u : ℝ} (hη : 0 < η) (h : u ≤ -η) :
    levelJoinPsi η u = 0 := by
  have h1 : (u + η) / η ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le
  unfold levelJoinPsi
  rw [max_eq_left h1, min_eq_right zero_le_one, zero_mul]

private lemma levelJoinPsi_eq_zero_of_ge {η u : ℝ} (hη : 0 < η) (h : 1 + η ≤ u) :
    levelJoinPsi η u = 0 := by
  have h1 : (1 + η - u) / η ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le
  unfold levelJoinPsi
  rw [max_eq_left h1, min_eq_right zero_le_one, mul_zero]

/-! ## Weighted level-part approximation -/

/-- Core approximation step, with an *arbitrary nonnegative weight* `w`: for a target point
whose level index is passed as a real `c`, the fixed profile `levelJoinPsi η` evaluated at the
rescaled deviation `(G y - α - ε·n)/ε` approximates the indicator of the level set with
index `n = ⌊(c - α)/ε⌋`, in the weighted `ℓ¹` sense, up to the contribution of the
exceptional set `T`. -/
lemma levelJoinPsi_approx_weighted {X : Type*} [Fintype X] [DecidableEq X]
    (G : X → ℝ) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    {α : ℝ} {T : Finset X}
    (hT : ∀ y, (∃ n : ℤ, |(G y - α) / ε - n| ≤ η) → y ∈ T) (c : ℝ) :
    ∑ y, w y * |(if ⌊(G y - α) / ε⌋ = ⌊(c - α) / ε⌋ then (1 : ℝ) else 0)
        - levelJoinPsi η ((G y - α - ε * ((⌊(c - α) / ε⌋ : ℤ) : ℝ)) / ε)|
      ≤ ∑ y ∈ T, w y := by
  set k : ℤ := ⌊(c - α) / ε⌋ with hk
  have hT_off : ∀ y, y ∉ T → ∀ n : ℤ, η < |(G y - α) / ε - n| := by
    intro y hy n
    exact lt_of_not_ge (fun h => hy (hT y ⟨n, h⟩))
  have hon : ∀ y, ⌊(G y - α) / ε⌋ = k →
      levelJoinPsi η ((G y - α - ε * (k : ℝ)) / ε) = 1 := by
    intro y hyk
    apply levelJoinPsi_eq_one hη
    · apply div_nonneg _ hε.le
      have h := Int.floor_le ((G y - α) / ε)
      rw [hyk] at h
      have h' : (k : ℝ) * ε ≤ G y - α := (le_div_iff₀ hε).mp h
      linarith
    · have h := Int.lt_floor_add_one ((G y - α) / ε)
      rw [hyk] at h
      have h' : G y - α < ((k : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp h
      rw [div_le_iff₀ hε]
      linarith
  have hoff : ∀ y, y ∉ T →
      levelJoinPsi η ((G y - α - ε * (k : ℝ)) / ε)
        = (if ⌊(G y - α) / ε⌋ = k then (1 : ℝ) else 0) := by
    intro y hyT
    by_cases hyk : ⌊(G y - α) / ε⌋ = k
    · rw [if_pos hyk]; exact hon y hyk
    · rw [if_neg hyk]
      rcases lt_or_gt_of_ne hyk with hlt | hgt
      · apply levelJoinPsi_eq_zero_of_le hη
        have hτ : (G y - α) / ε < (k : ℝ) := by
          have := Int.lt_floor_add_one ((G y - α) / ε)
          have hk1 : (⌊(G y - α) / ε⌋ : ℤ) + 1 ≤ k := by omega
          have hk1' : ((⌊(G y - α) / ε⌋ : ℤ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk1
          linarith
        have hk' : (G y - α) / ε < (k : ℝ) - η := by
          have h := hT_off y hyT k
          rw [abs_of_neg (by linarith)] at h
          linarith
        have h2 : (G y - α) < ((k : ℝ) - η) * ε := (div_lt_iff₀ hε).mp hk'
        rw [div_le_iff₀ hε]
        nlinarith
      · apply levelJoinPsi_eq_zero_of_ge hη
        have hτ : (k : ℝ) + 1 ≤ (G y - α) / ε := by
          have hfloor := Int.floor_le ((G y - α) / ε)
          have hk1 : k + 1 ≤ ⌊(G y - α) / ε⌋ := by omega
          have hk1' : (k : ℝ) + 1 ≤ ((⌊(G y - α) / ε⌋ : ℤ) : ℝ) := by exact_mod_cast hk1
          linarith
        have hk' : (k : ℝ) + 1 + η < (G y - α) / ε := by
          have h := hT_off y hyT (k + 1)
          push_cast at h
          rw [abs_of_nonneg (by linarith)] at h
          linarith
        have h2 : ((k : ℝ) + 1 + η) * ε < G y - α := (lt_div_iff₀ hε).mp hk'
        rw [le_div_iff₀ hε]
        nlinarith
  have hle : ∀ y, w y * |(if ⌊(G y - α) / ε⌋ = k then (1 : ℝ) else 0)
      - levelJoinPsi η ((G y - α - ε * (k : ℝ)) / ε)| ≤ (if y ∈ T then w y else 0) := by
    intro y
    by_cases hy : y ∈ T
    · rw [if_pos hy]
      apply mul_le_of_le_one_right (hw y)
      have h1 : (0 : ℝ) ≤ levelJoinPsi η ((G y - α - ε * (k : ℝ)) / ε) := levelJoinPsi_nonneg _ _
      have h2 : levelJoinPsi η ((G y - α - ε * (k : ℝ)) / ε) ≤ 1 := levelJoinPsi_le_one _ _
      by_cases hyk : ⌊(G y - α) / ε⌋ = k
      · rw [if_pos hyk, abs_of_nonneg (by linarith)]
        linarith
      · rw [if_neg hyk, zero_sub, abs_neg, abs_of_nonneg h1]
        exact h2
    · rw [if_neg hy, hoff y hy, sub_self, abs_zero, mul_zero]
  calc ∑ y, w y * |(if ⌊(G y - α) / ε⌋ = k then (1 : ℝ) else 0)
        - levelJoinPsi η ((G y - α - ε * (k : ℝ)) / ε)|
      ≤ ∑ y, (if y ∈ T then w y else 0) := Finset.sum_le_sum (fun y _ => hle y)
    _ = ∑ y ∈ T, w y := by
        rw [Finset.sum_ite_mem]
        simp

/-- Weighted level-part approximation in the `Finset.filter` form used by the target
statement. -/
private lemma approx_levelPart_levelJoinPsi_filter {X : Type*} [Fintype X] [DecidableEq X]
    (G : X → ℝ) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    {α : ℝ} {T : Finset X}
    (hT : ∀ y, (∃ n : ℤ, |(G y - α) / ε - n| ≤ η) → y ∈ T) (x : X) :
    ∑ y, w y * |(if y ∈ Finset.univ.filter
          (fun y => ⌊(G y - α) / ε⌋ = ⌊(G x - α) / ε⌋) then (1 : ℝ) else 0)
        - levelJoinPsi η ((G y - α - ε * ((⌊(G x - α) / ε⌋ : ℤ) : ℝ)) / ε)|
      ≤ ∑ y ∈ T, w y := by
  calc ∑ y, w y * |(if y ∈ Finset.univ.filter
          (fun y => ⌊(G y - α) / ε⌋ = ⌊(G x - α) / ε⌋) then (1 : ℝ) else 0)
        - levelJoinPsi η ((G y - α - ε * ((⌊(G x - α) / ε⌋ : ℤ) : ℝ)) / ε)|
      = ∑ y, w y * |(if ⌊(G y - α) / ε⌋ = ⌊(G x - α) / ε⌋ then (1 : ℝ) else 0)
        - levelJoinPsi η ((G y - α - ε * ((⌊(G x - α) / ε⌋ : ℤ) : ℝ)) / ε)| := by
        apply Finset.sum_congr rfl
        intro y _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    _ ≤ ∑ y ∈ T, w y := levelJoinPsi_approx_weighted G w hw hε hη hT (G x)

/-! ## The shift is bounded by `M + ε` -/

/-- The level index `n = ⌊(g - α)/ε⌋` translates into a shift `α + ε·n` of size at most
`M + ε` whenever `|g| ≤ M`. -/
private lemma abs_shift_le {g α M ε : ℝ} (hε : 0 < ε) (h : |g| ≤ M) :
    |α + ε * ((⌊(g - α) / ε⌋ : ℤ) : ℝ)| ≤ M + ε := by
  set n : ℤ := ⌊(g - α) / ε⌋ with hn
  have h1 : (n : ℝ) ≤ (g - α) / ε := by rw [hn]; exact Int.floor_le _
  have h2 : (g - α) / ε < (n : ℝ) + 1 := by rw [hn]; exact Int.lt_floor_add_one _
  have h3 : (n : ℝ) * ε ≤ g - α := (le_div_iff₀ hε).mp h1
  have h4 : g - α < ((n : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp h2
  have hg := abs_le.mp h
  rw [abs_le]
  constructor <;> linarith

/-- **The Weierstrass data attached to a join of level-set σ-algebras (Green–Tao §7).**

For generators `F j` whose dual functions `davg d (F j)` are bounded by `M` and whose level
grid at resolution `ε` with shift `α j` is covered by `T j`, there is a single constant `E₀ ≥ 0`,
a family of continuous `[0,1]`-valued profiles `φ j x : ℝ → ℝ` (one for each generator and each
point `x`, approximating the indicator of the level set of `x` in the `((ν+1)/2+1)`-weighted
sense) and, for every `x`, a polynomial `P x` in `K` variables with coefficient mass `≤ E₀` which
approximates `t ↦ ∏ j, φ j x (t j)` on the box `[-M,M]^K` within `η'`.

The proof uses the explicit profile
`ψ u = min 1 (max 0 (u/η + 1)) * min 1 (max 0 ((1 + η - u)/η))`
and `φ j x t = ψ ((t - α j - ε·n) / ε)`, `n = ⌊(davg d (F j) x - α j)/ε⌋`; the shift bound
`|α j + ε·n| ≤ M + 2ε` comes from `floor_levIdx_mem_Icc`, and the polynomial with the uniform
coefficient-mass bound comes from `exists_poly_weight_family`. -/
theorem exists_levelJoin_polys {p : ℕ} [Fact p.Prime] {d K : ℕ}
    (F : Fin K → ZMod p → ℝ) (ν : ZMod p → ℝ)
    {ε η M η' : ℝ} (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1 / 4) (hν : ∀ x, 0 ≤ ν x)
    (hη' : 0 < η') (hM : 0 ≤ M)
    (α : Fin K → ℝ) (hα0 : ∀ j, 0 ≤ α j) (hαε : ∀ j, α j < ε)
    (T : Fin K → Finset (ZMod p))
    (hT : ∀ (j : Fin K) (y : ZMod p),
      (∃ n : ℤ, |(davg d (F j) y - α j) / ε - n| ≤ η) → y ∈ T j)
    (hMbound : ∀ (j : Fin K) (y : ZMod p), |davg d (F j) y| ≤ M) :
    ∃ E₀ : ℝ, 0 ≤ E₀ ∧ ∃ φ : Fin K → ZMod p → ℝ → ℝ,
      (∀ (j : Fin K) (x : ZMod p), Continuous (φ j x)) ∧
      (∀ (j : Fin K) (x : ZMod p) (t : ℝ), 0 ≤ φ j x t) ∧
      (∀ (j : Fin K) (x : ZMod p) (t : ℝ), φ j x t ≤ 1) ∧
      (∀ (j : Fin K) (x : ZMod p),
        ∑ y : ZMod p, ((ν y + 1) / 2 + 1) *
          |(if y ∈ Finset.univ.filter
              (fun y => ⌊(davg d (F j) y - α j) / ε⌋ = ⌊(davg d (F j) x - α j) / ε⌋)
              then (1 : ℝ) else 0) - φ j x (davg d (F j) y)|
        ≤ ∑ y ∈ T j, ((ν y + 1) / 2 + 1)) ∧
      (∀ x : ZMod p, ∃ P : MvPolynomial (Fin K) ℝ,
        (∀ t ∈ Set.pi Set.univ (fun _ : Fin K => Set.Icc (-M) M),
          |∏ j : Fin K, φ j x (t j) - MvPolynomial.eval t P| ≤ η') ∧
        (∑ m ∈ P.support, |P.coeff m|) ≤ E₀) := by
  classical
  -- the polynomial family, with the shift bound `C = M + ε`
  have hCM : 0 ≤ M + ε := by linarith
  obtain ⟨E₀, hE₀, hpoly⟩ :=
    Commons.Analysis.Approximation.exists_poly_weight_family (K := K) (M := M) (ε := ε) (C := M + ε) (η' := η')
      hM hε hCM hη' (ψ := levelJoinPsi η) (continuous_levelJoinPsi η).continuousOn
      (fun u _ => ⟨levelJoinPsi_nonneg η u, levelJoinPsi_le_one η u⟩)
  refine ⟨E₀, hE₀,
    fun j x t => levelJoinPsi η ((t - α j - ε * ((⌊(davg d (F j) x - α j) / ε⌋ : ℤ) : ℝ)) / ε),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j x
    exact (continuous_levelJoinPsi η).comp
      (((continuous_id.sub continuous_const).sub continuous_const).div_const ε)
  · intro j x t
    exact levelJoinPsi_nonneg η _
  · intro j x t
    exact levelJoinPsi_le_one η _
  · intro j x
    exact approx_levelPart_levelJoinPsi_filter (davg d (F j)) (fun y : ZMod p => (ν y + 1) / 2 + 1)
      (fun y => by have h := hν y; linarith) hε hη (hT j) x
  · intro x
    obtain ⟨P, hP, hmass⟩ := hpoly
      (fun j => α j + ε * ((⌊(davg d (F j) x - α j) / ε⌋ : ℤ) : ℝ))
      (fun j => abs_shift_le hε (hMbound j x))
    refine ⟨P, ?_, hmass⟩
    intro t ht
    have hprod : ∏ j : Fin K,
          levelJoinPsi η ((t j - α j - ε * ((⌊(davg d (F j) x - α j) / ε⌋ : ℤ) : ℝ)) / ε)
        = ∏ j : Fin K,
          levelJoinPsi η ((t j - (α j + ε * ((⌊(davg d (F j) x - α j) / ε⌋ : ℤ) : ℝ))) / ε) := by
      apply Finset.prod_congr rfl
      intro j _
      congr 1
      ring
    rw [hprod]
    exact hP t ht

end Commons.Combinatorics.Transference
