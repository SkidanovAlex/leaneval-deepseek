import Mathlib
import Submission.Commons.Analysis.Approximation.exists_poly_weight_family_deg_K0
import Submission.Commons.Combinatorics.Transference.exists_levelJoin_polys_deg

namespace Commons.Combinatorics.Transference

theorem exists_levelJoin_polys_K0 {p : ℕ} [Fact p.Prime] {d K₀ K : ℕ} (hKK₀ : K ≤ K₀)
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
        P.totalDegree ≤ D) :=
  exists_levelJoin_polys_deg (d := d) (K := K) F ν hε hη hη1 hν hη' hM α hα0 hαε T hT hMbound

end Commons.Combinatorics.Transference
