import Mathlib
import Submission.Commons.Analysis.Approximation.exists_poly_weight_family_deg
import Submission.Commons.Combinatorics.Transference.exists_levelJoin_polys

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-! ## Degree-bounded version of the level-join Weierstrass data

This file repackages the construction of `exists_levelJoin_polys` on top of the
degree-bounded polynomial family `exists_poly_weight_family_deg`, so that besides the
coefficient-mass bound `E` one also obtains a uniform total-degree bound `D` for the
approximating polynomials.  The profile `levelJoinPsi` and its basic properties are
re-exported here as local (private) lemmas so that this file is self-contained with
respect to the public interface of `exists_levelJoin_polys`. -/

private lemma continuous_levelJoinPsi' (η : ℝ) : Continuous (levelJoinPsi η) := by
  unfold levelJoinPsi
  apply Continuous.mul
  · exact Continuous.min continuous_const
      (Continuous.max continuous_const ((continuous_id.add continuous_const).div_const η))
  · exact Continuous.min continuous_const
      (Continuous.max continuous_const
        (((continuous_const.add continuous_const).sub continuous_id).div_const η))

private lemma levelJoinPsi_nonneg' (η u : ℝ) : 0 ≤ levelJoinPsi η u := by
  unfold levelJoinPsi
  exact mul_nonneg (le_min zero_le_one (le_max_left 0 _))
    (le_min zero_le_one (le_max_left 0 _))

private lemma levelJoinPsi_le_one' (η u : ℝ) : levelJoinPsi η u ≤ 1 := by
  unfold levelJoinPsi
  have h1 : min 1 (max 0 ((u + η) / η)) ≤ 1 := min_le_left _ _
  have h2 : min 1 (max 0 ((1 + η - u) / η)) ≤ 1 := min_le_left _ _
  have h2' : 0 ≤ min 1 (max 0 ((1 + η - u) / η)) := le_min zero_le_one (le_max_left 0 _)
  calc min 1 (max 0 ((u + η) / η)) * min 1 (max 0 ((1 + η - u) / η))
      ≤ 1 * 1 := mul_le_mul h1 h2 h2' zero_le_one
    _ = 1 := by norm_num

/-- Weighted level-part approximation in the `Finset.filter` form used by the target
statement, on top of the public `levelJoinPsi_approx_weighted`. -/
private lemma approx_levelPart_levelJoinPsi_filter' {X : Type*} [Fintype X] [DecidableEq X]
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

/-- The level index `n = ⌊(g - α)/ε⌋` translates into a shift `α + ε·n` of size at most
`M + ε` whenever `|g| ≤ M`. -/
private lemma abs_shift_le' {g α M ε : ℝ} (hε : 0 < ε) (h : |g| ≤ M) :
    |α + ε * ((⌊(g - α) / ε⌋ : ℤ) : ℝ)| ≤ M + ε := by
  set n : ℤ := ⌊(g - α) / ε⌋ with hn
  have h1 : (n : ℝ) ≤ (g - α) / ε := by rw [hn]; exact Int.floor_le _
  have h2 : (g - α) / ε < (n : ℝ) + 1 := by rw [hn]; exact Int.lt_floor_add_one _
  have h3 : (n : ℝ) * ε ≤ g - α := (le_div_iff₀ hε).mp h1
  have h4 : g - α < ((n : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp h2
  have hg := abs_le.mp h
  rw [abs_le]
  constructor <;> linarith

/-- **Degree-bounded Weierstrass data attached to a join of level-set σ-algebras.**

Same conclusion as `exists_levelJoin_polys`, but the approximating polynomials are
additionally required to satisfy a uniform total-degree bound `D`. -/
theorem exists_levelJoin_polys_deg {p : ℕ} [Fact p.Prime] {d K : ℕ}
    (F : Fin K → ZMod p → ℝ) (ν : ZMod p → ℝ)
    {ε η M η' : ℝ} (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1 / 4) (hν : ∀ x, 0 ≤ ν x)
    (hη' : 0 < η') (hM : 0 ≤ M)
    (α : Fin K → ℝ) (hα0 : ∀ j, 0 ≤ α j) (hαε : ∀ j, α j < ε)
    (T : Fin K → Finset (ZMod p))
    (hT : ∀ (j : Fin K) (y : ZMod p),
      (∃ n : ℤ, |(davg d (F j) y - α j) / ε - n| ≤ η) → y ∈ T j)
    (hMbound : ∀ (j : Fin K) (y : ZMod p), |davg d (F j) y| ≤ M) :
    ∃ (E : ℝ) (D : ℕ), 0 ≤ E ∧ ∃ φ : Fin K → ZMod p → ℝ → ℝ,
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
  have hCM : 0 ≤ M + ε := by linarith
  obtain ⟨E, D, hE, hpoly⟩ :=
    Commons.Analysis.Approximation.exists_poly_weight_family_deg (K := K) (M := M) (ε := ε)
      (C := M + ε) (η' := η') hM hε hCM hη' (ψ := levelJoinPsi η)
      (continuous_levelJoinPsi' η).continuousOn
      (fun u _ => ⟨levelJoinPsi_nonneg' η u, levelJoinPsi_le_one' η u⟩)
  refine ⟨E, D, hE,
    fun j x t => levelJoinPsi η ((t - α j - ε * ((⌊(davg d (F j) x - α j) / ε⌋ : ℤ) : ℝ)) / ε),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j x
    exact (continuous_levelJoinPsi' η).comp
      (((continuous_id.sub continuous_const).sub continuous_const).div_const ε)
  · intro j x t
    exact levelJoinPsi_nonneg' η _
  · intro j x t
    exact levelJoinPsi_le_one' η _
  · intro j x
    exact approx_levelPart_levelJoinPsi_filter' (davg d (F j)) (fun y : ZMod p => (ν y + 1) / 2 + 1)
      (fun y => by have h := hν y; linarith) hε hη (hT j) x
  · intro x
    obtain ⟨P, hP, hmass, hdeg⟩ := hpoly
      (fun j => α j + ε * ((⌊(davg d (F j) x - α j) / ε⌋ : ℤ) : ℝ))
      (fun j => abs_shift_le' hε (hMbound j x))
    refine ⟨P, ?_, hmass, hdeg⟩
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
