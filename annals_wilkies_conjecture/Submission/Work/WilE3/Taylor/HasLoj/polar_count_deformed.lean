import Mathlib
import Submission.Work.WilE3.Loj.multBound_converging
import Submission.Work.WilE3.Taylor.HasLoj.PolarCount

namespace Work.WilE3.Taylor.HasLoj

open Classical

/-- **The deformed polar-system count in degree form.**  Same as `radialPolar_count`, but for the
system obtained from `P` by translating one row by `-ε` (the deformation of Gabrielov's multiplicity
bound with `g = -e_{i₀}`, a *constant* deformation, whose symbolic derivative `eaD` vanishes and
whose `atomDeg` is `1`).  Since the deformation is constant, the deformed system is exactly a
system `f + ε g` in the sense of `MultiplicityBound`, and its nondegenerate zeros are counted by the
same multiplicity bound; the degree bookkeeping is identical to `radialPolar_count`. -/
theorem polar_count_deformed (hMB : Work.WilE3.MultiplicityBound) (F : ℕ) :
    ∃ M : Polynomial ℕ, ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r) (Φ : WilkiesDesign.E.EAPoly k r)
      (P : Fin k → WilkiesDesign.E.EAPoly k r) (i₀ : Fin k) (x : Fin k → ℂ),
      k + r ≤ F → (∀ i, Work.WilE3.eaEvalC c (P i) x = 0) →
      (∀ i, WilkiesDesign.E.atomDeg (P i) ≤ 3 * WilkiesDesign.E.atomDeg Φ + 3) →
      ∀ ρ : ℂ → ℝ, (∀ ε, 0 < ρ ε) →
      Filter.Tendsto ρ (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds 0) →
      ∀ᶠ ε in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, ∀ s : Finset (Fin k → ℂ),
        (∀ z ∈ s, (∀ i, Work.WilE3.eaEvalC c (P i) z + ε * (if i = i₀ then (-1 : ℂ) else 0) = 0) ∧
          (Matrix.of fun i j => Work.WilE3.eaEvalC c (WilkiesDesign.E.eaD c j (P i)) z).det ≠ 0) →
        (∀ z ∈ s, ‖z - x‖ < ρ ε) → s.card ≤ M.eval (WilkiesDesign.E.atomDeg Φ) := by
  obtain ⟨M0, hM0⟩ := hMB F
  refine ⟨M0.comp (Polynomial.C F * (Polynomial.C 3 * Polynomial.X + Polynomial.C 3)
    + Polynomial.C F), ?_⟩
  intro k r c Φ P i₀ x hkr hPx hdeg ρ hρpos hρtend
  -- The constant deformation `g = -e_{i₀}` (as an EA polynomial it is `-1` on row `i₀`, `0` else).
  let g : Fin k → WilkiesDesign.E.EAPoly k r :=
    fun i => if i = i₀ then MvPolynomial.C (-1 : ℝ) else 0
  -- Its evaluation is the constant `-e_{i₀}`.
  have hg_eval : ∀ (i : Fin k) (z : Fin k → ℂ),
      Work.WilE3.eaEvalC c (g i) z = (if i = i₀ then (-1 : ℂ) else 0) := by
    intro i z
    by_cases h : i = i₀ <;>
      simp [g, h, Work.WilE3.eaEvalC, MvPolynomial.eval₂_zero]
  -- Its symbolic derivative vanishes (constant deformation).
  have hg_deriv : ∀ (i j : Fin k), WilkiesDesign.E.eaD c j (g i) = 0 := by
    intro i j
    by_cases h : i = i₀ <;> simp [g, h, WilkiesDesign.E.eaD]
  filter_upwards [hM0 k r c P g x ρ hkr hPx hρpos hρtend] with ε hε
  intro s hs hball
  refine le_trans (hε s ?_ hball) ?_
  · -- The nondegenerate zeros of the deformed system are zeros of `P + ε g`.
    intro z hz
    refine ⟨fun i => ?_, ?_⟩
    · rw [hg_eval i z]; exact (hs z hz).1 i
    · have hmat : (Matrix.of fun i j => Work.WilE3.eaEvalC c (WilkiesDesign.E.eaD c j (P i)) z +
            ε * Work.WilE3.eaEvalC c (WilkiesDesign.E.eaD c j (g i)) z)
          = Matrix.of (fun i j => Work.WilE3.eaEvalC c (WilkiesDesign.E.eaD c j (P i)) z) := by
        ext i j
        simp only [Matrix.of_apply]
        rw [hg_deriv i j, Work.WilE3.Loj.eaEvalC_zeroL, mul_zero, add_zero]
      rw [hmat]
      exact (hs z hz).2
  · -- Degree bookkeeping: `∑ atomDeg P + ∑ atomDeg g ≤ F * (3 * atomDeg Φ + 3) + F`.
    have hkF : k ≤ F := by omega
    have hsumP : (∑ i : Fin k, WilkiesDesign.E.atomDeg (P i))
        ≤ F * (3 * WilkiesDesign.E.atomDeg Φ + 3) := by
      calc (∑ i : Fin k, WilkiesDesign.E.atomDeg (P i))
            ≤ ∑ _i : Fin k, (3 * WilkiesDesign.E.atomDeg Φ + 3) :=
              Finset.sum_le_sum fun i _ => hdeg i
        _ = k * (3 * WilkiesDesign.E.atomDeg Φ + 3) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        _ ≤ F * (3 * WilkiesDesign.E.atomDeg Φ + 3) :=
              Nat.mul_le_mul_right _ hkF
    have hsumg : (∑ i : Fin k, WilkiesDesign.E.atomDeg (g i)) = k := by
      have hone : (∑ i : Fin k, WilkiesDesign.E.atomDeg (g i)) = ∑ _i : Fin k, 1 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : i = i₀ <;>
          simp [g, h, WilkiesDesign.E.atomDeg, MvPolynomial.totalDegree_zero]
      rw [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    have htot : (∑ i : Fin k, WilkiesDesign.E.atomDeg (P i))
        + (∑ i : Fin k, WilkiesDesign.E.atomDeg (g i))
        ≤ F * (3 * WilkiesDesign.E.atomDeg Φ + 3) + F := by
      rw [hsumg]; omega
    rw [Polynomial.eval_comp]
    have hp : (Polynomial.C F * (Polynomial.C 3 * Polynomial.X + Polynomial.C 3)
        + Polynomial.C F).eval (WilkiesDesign.E.atomDeg Φ)
        = F * (3 * WilkiesDesign.E.atomDeg Φ + 3) + F := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [hp]
    exact Work.WilE3.Loj.polynomial_eval_le_eval htot

end Work.WilE3.Taylor.HasLoj
