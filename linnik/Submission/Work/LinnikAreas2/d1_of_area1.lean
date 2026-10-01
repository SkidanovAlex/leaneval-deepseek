import Mathlib
import Submission.Work.LinnikContract2.Areas
import Submission.Work.LinnikContract2.API
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas2.PsiDefs2
import Submission.Work.LinnikAreas.Density4.zeroDetAux
import Submission.Work.LinnikAreas.Density4.det_split
import Submission.Work.LinnikAreas.Density4.zero_detector
import Submission.Work.LinnikAreas.Density4.theta_diag_eval
import Submission.Work.LinnikAreas.Density4.duality_principle

namespace Work.LinnikAreas2

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-! ## HB §11 (11.11), (11.12): the two coefficient families -/

/-- `wt_n = e^{-n/q^x} - e^{-n(𝓛)²/q^u}` (the common weight of the detector and of `b_n`). -/
abbrev WT (q : ℕ) (u x : ℝ) (n : ℕ) : ℝ :=
  Work.LinnikAreas2.wt (Real.log q) ((q:ℝ)^u) ((q:ℝ)^x) n

/-- HB (11.12): `b_n = (Σ_{d|n}ψ_d) n^{-1/2} wt_n^{1/2}`. -/
def bcoef (q : ℕ) [NeZero q] (u v x : ℝ) (n : ℕ) : ℂ :=
  ((Work.LinnikAreas.Density4.psiS ((q:ℝ)^u) ((q:ℝ)^v) n : ℝ) : ℂ)
    * ((n : ℂ) ^ (-(1/2 : ℂ)))
    * ((Real.sqrt (WT q u x n) : ℝ) : ℂ)

/-- HB (11.11): `a_n = w_χ^{1/2} (Σ_{d|n}θ_d) χ(n) n^{1/2-ρ} wt_n^{1/2}`. -/
def acoef (q : ℕ) [NeZero q] (u w x : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (wc : ℝ) (n : ℕ) : ℂ :=
  ((Real.sqrt wc : ℝ) : ℂ)
    * ((Work.LinnikAreas.Density4.thetaS ((q:ℝ)^w) n : ℝ) : ℂ)
    * χ (n : ZMod q)
    * ((n : ℂ) ^ ((1/2 : ℂ) - ρ))
    * ((Real.sqrt (WT q u x n) : ℝ) : ℂ)

lemma bcoef_zero (q : ℕ) [NeZero q] (u v x : ℝ) : bcoef q u v x 0 = 0 := by
  simp [bcoef, Work.LinnikAreas.Density4.psiS_zero]

lemma acoef_zero (q : ℕ) [NeZero q] (u w x : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (wc : ℝ) : acoef q u w x χ ρ wc 0 = 0 := by
  simp [acoef, Work.LinnikAreas.Density4.thetaS_zero]

/-- **HB (11.11)–(11.12): the inner product of the two families is `w_χ^{1/2}` times the
zero detector.** -/
theorem tsum_acoef_mul_bcoef (q : ℕ) [NeZero q] (u v w x : ℝ) (χ : DirichletCharacter ℂ q)
    (ρ : ℂ) (wc : ℝ) (hwt : ∀ n, 0 ≤ WT q u x n) :
    (∑' n : ℕ, acoef q u w x χ ρ wc n * bcoef q u v x n)
      = ((Real.sqrt wc : ℝ) : ℂ)
          * Work.LinnikAreas.Density4.detSum q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) ((q:ℝ)^x)
              (Real.log q) χ ρ := by
  have hterm : ∀ n : ℕ,
      acoef q u w x χ ρ wc n * bcoef q u v x n
        = ((Real.sqrt wc : ℝ) : ℂ)
            * (Work.LinnikAreas.Density4.detCoeff q ((q:ℝ)^u) ((q:ℝ)^v) ((q:ℝ)^w) χ ρ n
                * ((WT q u x n : ℝ) : ℂ)) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [acoef, bcoef, Work.LinnikAreas.Density4.detCoeff,
        Work.LinnikAreas.Density4.psiS_zero, Work.LinnikAreas.Density4.thetaS_zero]
    · have hnne : (n : ℂ) ≠ 0 := by
        simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hn
      have hsq : ((Real.sqrt (WT q u x n) : ℝ) : ℂ) * ((Real.sqrt (WT q u x n) : ℝ) : ℂ)
          = ((WT q u x n : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hwt n)]
      have e1 : (n : ℂ) ^ ((1/2 : ℂ) - ρ)
          = (n : ℂ) ^ (-ρ) * (n : ℂ) ^ (1/2 : ℂ) := by
        rw [← Complex.cpow_add _ _ hnne]; congr 1; ring
      have e2 : (n : ℂ) ^ (1/2 : ℂ) * (n : ℂ) ^ (-(1/2 : ℂ)) = 1 := by
        rw [← Complex.cpow_add _ _ hnne]; simp
      simp only [acoef, bcoef, Work.LinnikAreas.Density4.detCoeff]
      calc ((Real.sqrt wc : ℝ) : ℂ)
              * ((Work.LinnikAreas.Density4.thetaS ((q:ℝ)^w) n : ℝ) : ℂ) * χ (n : ZMod q)
              * ((n : ℂ) ^ ((1/2 : ℂ) - ρ)) * ((Real.sqrt (WT q u x n) : ℝ) : ℂ)
            * (((Work.LinnikAreas.Density4.psiS ((q:ℝ)^u) ((q:ℝ)^v) n : ℝ) : ℂ)
                * (n : ℂ) ^ (-(1/2 : ℂ)) * ((Real.sqrt (WT q u x n) : ℝ) : ℂ))
          = ((Real.sqrt wc : ℝ) : ℂ)
              * ((Work.LinnikAreas.Density4.thetaS ((q:ℝ)^w) n : ℝ) : ℂ) * χ (n : ZMod q)
              * ((n : ℂ) ^ (-ρ) * (n : ℂ) ^ (1/2 : ℂ))
              * ((Real.sqrt (WT q u x n) : ℝ) : ℂ)
            * (((Work.LinnikAreas.Density4.psiS ((q:ℝ)^u) ((q:ℝ)^v) n : ℝ) : ℂ)
                * (n : ℂ) ^ (-(1/2 : ℂ)) * ((Real.sqrt (WT q u x n) : ℝ) : ℂ)) := by
              rw [e1]
        _ = ((Real.sqrt wc : ℝ) : ℂ)
              * ((Work.LinnikAreas.Density4.psiS ((q:ℝ)^u) ((q:ℝ)^v) n : ℝ) : ℂ)
              * ((Work.LinnikAreas.Density4.thetaS ((q:ℝ)^w) n : ℝ) : ℂ) * χ (n : ZMod q)
              * (n : ℂ) ^ (-ρ) * ((n : ℂ) ^ (1/2 : ℂ) * (n : ℂ) ^ (-(1/2 : ℂ)))
              * (((Real.sqrt (WT q u x n) : ℝ) : ℂ) * ((Real.sqrt (WT q u x n) : ℝ) : ℂ)) := by
              ring
        _ = ((Real.sqrt wc : ℝ) : ℂ)
              * ((Work.LinnikAreas.Density4.psiS ((q:ℝ)^u) ((q:ℝ)^v) n : ℝ) : ℂ)
              * ((Work.LinnikAreas.Density4.thetaS ((q:ℝ)^w) n : ℝ) : ℂ) * χ (n : ZMod q)
              * (n : ℂ) ^ (-ρ) * 1
              * (((Real.sqrt (WT q u x n) : ℝ) : ℂ) * ((Real.sqrt (WT q u x n) : ℝ) : ℂ)) := by
              rw [e2]
        _ = ((Real.sqrt wc : ℝ) : ℂ)
              * ((Work.LinnikAreas.Density4.psiS ((q:ℝ)^u) ((q:ℝ)^v) n : ℝ) : ℂ)
              * ((Work.LinnikAreas.Density4.thetaS ((q:ℝ)^w) n : ℝ) : ℂ) * χ (n : ZMod q)
              * (n : ℂ) ^ (-ρ) * ((WT q u x n : ℝ) : ℂ) := by
              rw [hsq]; ring
        _ = ((Real.sqrt wc : ℝ) : ℂ)
              * (((Work.LinnikAreas.Density4.psiS ((q:ℝ)^u) ((q:ℝ)^v) n : ℝ) : ℂ)
                  * ((Work.LinnikAreas.Density4.thetaS ((q:ℝ)^w) n : ℝ) : ℂ) * χ (n : ZMod q)
                  * (n : ℂ) ^ (-ρ) * ((WT q u x n : ℝ) : ℂ)) := by
              ring
  rw [tsum_congr hterm, tsum_mul_left]
  congr 1


/-- **The closing step of HB §11.**  If the *weighted* zero-density sum with the HB weight
`2λ w/(e^{73λ/30} - e^{16λ/15})`, `w = 1/10 - δ`, is bounded by `2w(67/6+ε)`, then the
contract's `D1` (the `wHB`-weighted sum) is bounded by `67/6 + ε`. -/
theorem d1_of_weighted (ε : ℝ) (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1/10)
    (h : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q],
      (∑ χ ∈ Finset.univ.filter
          (fun χ : DirichletCharacter ℂ q =>
            ∃ ρ, Work.LinnikContract2.IsZ χ ρ ∧
              Work.LinnikContract2.lamOf q ρ ≤ Work.LinnikContract2.lamMax q),
        2 * Work.LinnikContract2.lamChar χ * (1/10 - δ)
          / (Real.exp (73/30 * Work.LinnikContract2.lamChar χ)
              - Real.exp (16/15 * Work.LinnikContract2.lamChar χ)))
        ≤ 2 * (1/10 - δ) * (67/6 + ε)) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q],
      (∑ χ ∈ Finset.univ.filter
          (fun χ : DirichletCharacter ℂ q =>
            ∃ ρ, Work.LinnikContract2.IsZ χ ρ ∧
              Work.LinnikContract2.lamOf q ρ ≤ Work.LinnikContract2.lamMax q),
        Work.LinnikContract2.wHB (Work.LinnikContract2.lamChar χ)) ≤ 67/6 + ε := by
  obtain ⟨q₀, hq₀⟩ := h
  refine ⟨q₀, fun q hq _ => ?_⟩
  have hw : 0 < 1/10 - δ := by linarith
  have hmain := hq₀ q hq
  have hstep : (∑ χ ∈ Finset.univ.filter
        (fun χ : DirichletCharacter ℂ q =>
          ∃ ρ, Work.LinnikContract2.IsZ χ ρ ∧
            Work.LinnikContract2.lamOf q ρ ≤ Work.LinnikContract2.lamMax q),
        2 * Work.LinnikContract2.lamChar χ * (1/10 - δ)
          / (Real.exp (73/30 * Work.LinnikContract2.lamChar χ)
              - Real.exp (16/15 * Work.LinnikContract2.lamChar χ)))
      = 2 * (1/10 - δ) * (∑ χ ∈ Finset.univ.filter
        (fun χ : DirichletCharacter ℂ q =>
          ∃ ρ, Work.LinnikContract2.IsZ χ ρ ∧
            Work.LinnikContract2.lamOf q ρ ≤ Work.LinnikContract2.lamMax q),
        Work.LinnikContract2.wHB (Work.LinnikContract2.lamChar χ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    rw [Work.LinnikContract2.wHB]
    ring
  rw [hstep] at hmain
  exact le_of_mul_le_mul_left hmain (by positivity)

end
end Work.LinnikAreas2
