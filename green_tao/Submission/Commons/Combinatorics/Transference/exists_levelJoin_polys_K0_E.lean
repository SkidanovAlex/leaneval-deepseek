import Mathlib
import Submission.Commons.Combinatorics.Transference.exists_levelJoin_polys_K0
import Submission.Commons.Analysis.Approximation.exists_poly_weight_family_deg_K0

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-! ## The level-join polynomial data with prescribed coefficient mass and degree

`exists_levelJoin_polys_K0` / `exists_levelJoin_polys_deg` produce *some* coefficient mass `E₀`
and degree bound `D₀`.  Here we assume instead that the approximating polynomials of the
product `∏ j, levelJoinPsi η ((t j - c j)/ε)` are supplied together with *prescribed* bounds
`E`, `D` (hypothesis `hpoly`), and show that the Weierstrass profiles `φ j x` can be built so
that the product approximation also respects those prescribed `E` and `D`.

The construction of `φ` is the same one used throughout the transference section:
`φ j x t = levelJoinPsi η ((t - α j - ε · ⌊(davg d (F j) x - α j)/ε⌋) / ε)`. -/

private lemma continuous_levelJoinPsi_aux (η : ℝ) : Continuous (levelJoinPsi η) := by
  unfold levelJoinPsi
  apply Continuous.mul
  · exact Continuous.min continuous_const
      (Continuous.max continuous_const ((continuous_id.add continuous_const).div_const η))
  · exact Continuous.min continuous_const
      (Continuous.max continuous_const
        (((continuous_const.add continuous_const).sub continuous_id).div_const η))

private lemma levelJoinPsi_nonneg_aux (η u : ℝ) : 0 ≤ levelJoinPsi η u := by
  unfold levelJoinPsi
  exact mul_nonneg (le_min zero_le_one (le_max_left 0 _))
    (le_min zero_le_one (le_max_left 0 _))

private lemma levelJoinPsi_le_one_aux (η u : ℝ) : levelJoinPsi η u ≤ 1 := by
  unfold levelJoinPsi
  have h1 : min 1 (max 0 ((u + η) / η)) ≤ 1 := min_le_left _ _
  have h2 : min 1 (max 0 ((1 + η - u) / η)) ≤ 1 := min_le_left _ _
  have h2' : 0 ≤ min 1 (max 0 ((1 + η - u) / η)) := le_min zero_le_one (le_max_left 0 _)
  calc min 1 (max 0 ((u + η) / η)) * min 1 (max 0 ((1 + η - u) / η))
      ≤ 1 * 1 := mul_le_mul h1 h2 h2' zero_le_one
    _ = 1 := by norm_num

/-- The level index `n = ⌊(g - α)/ε⌋` translates into a shift `α + ε·n` of size at most
`M + ε` whenever `|g| ≤ M`. -/
private lemma abs_shift_le_aux {g α M ε : ℝ} (hε : 0 < ε) (h : |g| ≤ M) :
    |α + ε * ((⌊(g - α) / ε⌋ : ℤ) : ℝ)| ≤ M + ε := by
  set n : ℤ := ⌊(g - α) / ε⌋ with hn
  have h1 : (n : ℝ) ≤ (g - α) / ε := by rw [hn]; exact Int.floor_le _
  have h2 : (g - α) / ε < (n : ℝ) + 1 := by rw [hn]; exact Int.lt_floor_add_one _
  have h3 : (n : ℝ) * ε ≤ g - α := (le_div_iff₀ hε).mp h1
  have h4 : g - α < ((n : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp h2
  have hg := abs_le.mp h
  rw [abs_le]
  constructor <;> linarith

theorem exists_levelJoin_polys_K0_E {p : ℕ} [Fact p.Prime] {d K₀ K : ℕ} (hKK₀ : K ≤ K₀)
    (F : Fin K → ZMod p → ℝ) (ν : ZMod p → ℝ)
    {ε η M η' : ℝ} (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1 / 4) (hν : ∀ x, 0 ≤ ν x)
    (hη' : 0 < η') (hM : 0 ≤ M)
    (α : Fin K → ℝ) (hα0 : ∀ j, 0 ≤ α j) (hαε : ∀ j, α j < ε)
    (T : Fin K → Finset (ZMod p))
    (hT : ∀ (j : Fin K) (y : ZMod p),
      (∃ n : ℤ, |(davg d (F j) y - α j) / ε - n| ≤ η) → y ∈ T j)
    (hMbound : ∀ (j : Fin K) (y : ZMod p), |davg d (F j) y| ≤ M)
    {E : ℝ} (hE : 0 ≤ E) {D : ℕ}
    (hpoly : ∀ (K' : ℕ) (hK' : K' ≤ K₀) (c : Fin K' → ℝ), (∀ j, |c j| ≤ M + ε) →
      ∃ P : MvPolynomial (Fin K') ℝ,
        (∀ t ∈ Set.pi Set.univ (fun _ : Fin K' => Set.Icc (-M) M),
          |∏ j, Commons.Combinatorics.Transference.levelJoinPsi η ((t j - c j) / ε)
            - MvPolynomial.eval t P| ≤ η') ∧
        (∑ m ∈ P.support, |P.coeff m|) ≤ E ∧
        P.totalDegree ≤ D) :
    ∃ φ : Fin K → ZMod p → ℝ → ℝ,
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
        (∑ m ∈ P.support, |P.coeff m|) ≤ E ∧
        P.totalDegree ≤ D) := by
  classical
  let φ : Fin K → ZMod p → ℝ → ℝ :=
    fun j x t => levelJoinPsi η ((t - α j - ε * ((⌊(davg d (F j) x - α j) / ε⌋ : ℤ) : ℝ)) / ε)
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x
    exact (continuous_levelJoinPsi_aux η).comp
      (((continuous_id.sub continuous_const).sub continuous_const).div_const ε)
  · intro j x t
    exact levelJoinPsi_nonneg_aux η _
  · intro j x t
    exact levelJoinPsi_le_one_aux η _
  · intro j x
    simp only [φ]
    calc ∑ y : ZMod p, ((ν y + 1) / 2 + 1) *
          |(if y ∈ Finset.univ.filter
              (fun y => ⌊(davg d (F j) y - α j) / ε⌋ = ⌊(davg d (F j) x - α j) / ε⌋)
              then (1 : ℝ) else 0)
            - levelJoinPsi η ((davg d (F j) y - α j - ε * ((⌊(davg d (F j) x - α j) / ε⌋ : ℤ) : ℝ)) / ε)|
        = ∑ y : ZMod p, ((ν y + 1) / 2 + 1) *
          |(if ⌊(davg d (F j) y - α j) / ε⌋ = ⌊(davg d (F j) x - α j) / ε⌋ then (1 : ℝ) else 0)
            - levelJoinPsi η ((davg d (F j) y - α j - ε * ((⌊(davg d (F j) x - α j) / ε⌋ : ℤ) : ℝ)) / ε)| := by
          apply Finset.sum_congr rfl
          intro y _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      _ ≤ ∑ y ∈ T j, ((ν y + 1) / 2 + 1) :=
          levelJoinPsi_approx_weighted (davg d (F j)) (fun y : ZMod p => (ν y + 1) / 2 + 1)
            (fun y => by have h := hν y; linarith) hε hη (hT j) (davg d (F j) x)
  · intro x
    obtain ⟨P, hP, hmass, hdeg⟩ := hpoly K hKK₀
      (fun j => α j + ε * ((⌊(davg d (F j) x - α j) / ε⌋ : ℤ) : ℝ))
      (fun j => abs_shift_le_aux hε (hMbound j x))
    refine ⟨P, ?_, hmass, hdeg⟩
    intro t ht
    have hprod : ∏ j : Fin K, φ j x (t j)
        = ∏ j : Fin K,
          levelJoinPsi η ((t j - (α j + ε * ((⌊(davg d (F j) x - α j) / ε⌋ : ℤ) : ℝ))) / ε) := by
      simp only [φ]
      apply Finset.prod_congr rfl
      intro j _
      congr 1
      ring
    rw [hprod]
    exact hP t ht

end Commons.Combinatorics.Transference
