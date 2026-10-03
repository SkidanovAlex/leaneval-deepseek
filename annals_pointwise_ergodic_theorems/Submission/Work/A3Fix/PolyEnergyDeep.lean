import Mathlib
import Submission.Work.A3.majorArc_bound_of_split
import Submission.Work.A3.largeArc_energy_contribution
import Submission.Work.A3.deepArc_energy_contribution
import Submission.Work.A3.transitionArc_energy_contribution
import Submission.Work.A3Fix.Assembly

/-!
# `PolyEnergyBound` from the transition bound and the deep-shoulder input (Area A3)

This module assembles **everything** on the circle-method route to `Work.A3.PolyEnergyBound`
except two inputs:

* **(transition)** the pointwise "sharp Fresnel" bound on the coherent/transition region
  `|β| N^d ≤ (N/q)^{d/(d+1)}/100` (the target of `A3/transitionArc_bound`), and
* **(DEEP')** the *power saving* on the deep shoulder `(N/q)^{d/(d+1)}/100 ≤ |β|N^d ≤ 1/(qN^{d/2})`
  — the genuine arithmetic gap of `NOTES_A3_deepShoulder_SESSION.md` §3.

Everything else is proved: Weyl's inequality (`A3/weyl_poly`), the complete-sum saving, the
minor arcs (`minorArc_contribution_q`), the large-denominator arcs
(`largeArc_energy_contribution`), the transition energy estimate
(`transitionArc_energy_contribution`), the deep-shoulder energy estimate
(`deepArc_energy_contribution`), and the subadditive assembly `majorArc_bound_of_split`.

The parameter choice is `η = 1/2`, `γ = 1/4`, `ε = σ/8` with `σ = 2^{-(deg Q - 1)}` (the Weyl
saving), and `s` large enough for `sδ > 1`, `2s > deg Q`, the minor-arc inequality, the
large-denominator inequality `(d-1) ≤ (2s-2)σ/8` and the deep-shoulder inequality
`1/2 + d/2 ≤ 2sθ₀`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **The circle-method assembly with the two remaining inputs as hypotheses.** -/
theorem polyEnergy_bound_of_transition_and_deep (Q : Polynomial ℤ) (hd : 2 ≤ Q.natDegree)
    {δ C₁ : ℝ} (hδ : 0 < δ) (hC₁ : 0 < C₁)
    (hc : ∀ (q : ℕ) (a : ℤ), 1 ≤ q → IsCoprime a (q : ℤ) →
      ‖completeSum Q a q‖ ≤ C₁ * (q : ℝ) ^ (1 - δ))
    (hps : ∀ (q : ℕ) (a : ℤ) (t : ℕ), 1 ≤ q → IsCoprime a (q : ℤ) → t ≤ q →
      ‖∑ r ∈ Finset.range t,
        Complex.exp (-(2 * Real.pi * Complex.I *
          ((a : ℝ) * (((Q.eval (r : ℤ)) : ℤ) : ℝ) / (q : ℝ))))‖
      ≤ C₁ * (q : ℝ) ^ (1 - δ))
    {θ₀ C₀ : ℝ} (hθ₀ : 0 < θ₀) (hC₀ : 0 < C₀)
    (hdeep : ∀ (N : ℕ) (a q : ℤ) (β : ℝ), 1 ≤ N → 1 ≤ q → IsCoprime a (q : ℤ) →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) →
      ((N : ℝ) / (q : ℝ)) ^ ((Q.natDegree : ℝ) / (Q.natDegree + 1)) / 100
        ≤ |β| * (N : ℝ) ^ Q.natDegree →
      |β| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ ((Q.natDegree : ℝ) / 2)) →
      ‖expSum Q N ((a : ℝ) / (q : ℝ) + β)‖ ≤ C₀ * (N : ℝ) ^ (1 - θ₀))
    {Ctr : ℝ} (hCtr : 0 < Ctr)
    (htrans : ∀ (N : ℕ) (a q : ℤ) (β : ℝ), 1 ≤ N → 1 ≤ q → IsCoprime a (q : ℤ) →
      (q : ℝ) ≤ (N : ℝ) →
      |β| * (N : ℝ) ^ Q.natDegree
        ≤ ((N : ℝ) / (q : ℝ)) ^ ((Q.natDegree : ℝ) / (Q.natDegree + 1)) / 100 →
      ‖expSum Q N ((a : ℝ) / (q : ℝ) + β)‖
        ≤ Ctr * (q : ℝ) ^ (-δ) * mArcKernel N Q.natDegree β) :
    PolyEnergyBound Q := by
  set σ : ℝ := 1 / (2 : ℝ) ^ (Q.natDegree - 1) with hσ
  have hσpos : 0 < σ := by rw [hσ]; positivity
  have hε : (0 : ℝ) < σ / 4 := by positivity
  have hσmul : (2 : ℝ) ^ (Q.natDegree - 1) * σ = 1 := by rw [hσ]; field_simp
  have hhalf : (1 / 2 : ℝ) / (2 : ℝ) ^ (Q.natDegree - 1) = (1 / 2) * σ := by
    rw [hσ, mul_one_div]
  have hweyl : ∀ (ε : ℝ), 0 < ε → ∃ CW : ℝ, 0 < CW ∧
      ∀ (M : ℕ) (a q : ℤ) (θ : ℝ), 1 ≤ M → 1 ≤ q → IsCoprime a q →
        |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) ^ 2) →
        ‖expSum Q M θ‖ ≤ CW * (M : ℝ) ^ (1 + ε) *
          (((q : ℝ)⁻¹ + (M : ℝ)⁻¹ + (q : ℝ) * (M : ℝ) ^ (-((Q.natDegree : ℤ))))
            ^ ((1 : ℝ) / (2 : ℝ) ^ (Q.natDegree - 1))) :=
    fun ε hε => weyl_poly Q hd hε
  obtain ⟨s₁, hs₁⟩ := exists_nat_gt (1 / δ)
  obtain ⟨s₂, hs₂⟩ := exists_nat_gt (4 * ((Q.natDegree : ℝ) - 1) * (2 : ℝ) ^ (Q.natDegree - 1) + 1)
  obtain ⟨s₃, hs₃⟩ := exists_nat_gt ((1 + (Q.natDegree : ℝ) / 2) / (2 * θ₀))
  set s : ℕ := max 2 (max (s₁ + 1) (max (2 * Q.natDegree + 1) (max s₂ s₃))) with hsdef
  have hs1 : 1 ≤ s := by omega
  have hs2 : 2 ≤ s := by omega
  have hds : Q.natDegree < 2 * s := by omega
  have hds' : Q.natDegree ≤ 2 * s := by omega
  have hsδ : 1 < (s : ℝ) * δ := by
    have h1 : (1 : ℝ) / δ < (s : ℝ) :=
      lt_of_lt_of_le hs₁ (by exact_mod_cast (by omega : s₁ ≤ s))
    rw [div_lt_iff₀ hδ] at h1
    linarith
  have hs₂' : 4 * ((Q.natDegree : ℝ) - 1) * (2 : ℝ) ^ (Q.natDegree - 1) + 1 < (s : ℝ) :=
    lt_of_lt_of_le hs₂ (by exact_mod_cast (by omega : s₂ ≤ s))
  have hfac : (1 / 2 : ℝ) * σ - σ / 4 = σ / 4 := by ring
  have hkey : ((Q.natDegree : ℝ) - 1) ≤ (2 * (s : ℝ) - 2) * (σ / 4) := by
    have h2s : 4 * ((Q.natDegree : ℝ) - 1) * (2 : ℝ) ^ (Q.natDegree - 1)
        ≤ (2 * (s : ℝ) - 2) := by
      have hs1R : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
      have h2pow : (0 : ℝ) < (2 : ℝ) ^ (Q.natDegree - 1) := by positivity
      nlinarith [hs₂', hs1R, h2pow]
    have hstep := mul_le_mul_of_nonneg_right h2s (by positivity : (0 : ℝ) ≤ σ / 4)
    have hleft : 4 * ((Q.natDegree : ℝ) - 1) * (2 : ℝ) ^ (Q.natDegree - 1) * (σ / 4)
        = (Q.natDegree : ℝ) - 1 := by
      rw [show 4 * ((Q.natDegree : ℝ) - 1) * (2 : ℝ) ^ (Q.natDegree - 1) * (σ / 4)
          = ((Q.natDegree : ℝ) - 1) * ((2 : ℝ) ^ (Q.natDegree - 1) * σ) by ring,
        hσmul]
      ring
    calc ((Q.natDegree : ℝ) - 1)
        = 4 * ((Q.natDegree : ℝ) - 1) * (2 : ℝ) ^ (Q.natDegree - 1) * (σ / 4) := hleft.symm
      _ ≤ (2 * (s : ℝ) - 2) * (σ / 4) := hstep
  have hsz : (Q.natDegree - 1 : ℝ) ≤ (2 * s - 2 : ℝ) * ((1 / 2) * σ - σ / 4) := by
    rw [hfac]
    exact hkey
  have hcondLarge : (Q.natDegree : ℝ) - 1 ≤
      (2 * (s : ℝ) - 2) * ((1 / 2 : ℝ) / (2 : ℝ) ^ (Q.natDegree - 1) - σ / 4) := by
    rw [hhalf, hfac]
    exact hkey
  have hcondDeep : 2 * (1 / 2 : ℝ) + (Q.natDegree : ℝ) / 2 ≤ 2 * (s : ℝ) * θ₀ := by
    have hs₃' : ((1 + (Q.natDegree : ℝ) / 2) / (2 * θ₀)) < (s : ℝ) :=
      lt_of_lt_of_le hs₃ (by exact_mod_cast (by omega : s₃ ≤ s))
    have h2θ : (0 : ℝ) < 2 * θ₀ := by linarith
    rw [div_lt_iff₀ h2θ] at hs₃'
    linarith
  obtain ⟨CL, hCL, hLarge⟩ := largeArc_energy_contribution Q hd hε (by norm_num : (1:ℝ)/2 ≤ 1)
    (s := s) hs2 hds' hcondLarge
  obtain ⟨CT, hCT, hTrans⟩ := transitionArc_energy_contribution Q hd (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 ≤ 1) hδ hCtr (s := s) hs1 hsδ hds htrans
  obtain ⟨CD, hCD, hDeep⟩ := deepArc_energy_contribution Q hd (by norm_num : (0:ℝ) ≤ 1/2) hθ₀ hC₀
    (s := s) hs1 hcondDeep hdeep
  have hmaj : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ θ in majorArcSet Q N (1 / 2) ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s) ≤
        C ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree) :=
    majorArc_bound_of_split Q hd (by norm_num : (1:ℝ)/2 ≤ 1/2) hs1
      ⟨CL, hCL, hLarge⟩ ⟨CT, hCT, hTrans⟩ ⟨CD, hCD, hDeep⟩
  obtain ⟨CW, hCW, hweyl'⟩ := hweyl (σ / 4) hε
  have hmin : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ θ in (majorArcSet Q N (1 / 2))ᶜ ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s) ≤
        C ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree) :=
    minorArc_contribution Q hd hCW hε hweyl' hs2 (le_of_lt hds) (by norm_num) (by norm_num)
      (by simpa only [hσ] using hsz)
  obtain ⟨C, hC, hbound⟩ := polyEnergy_bound_of_arc_bounds Q hd hs2 hmaj hmin
  refine ⟨s, hs2, Real.toNNReal C, Real.toNNReal_pos.mpr hC, ?_⟩
  intro N hN
  have hcoe : ((Real.toNNReal C : ℝ≥0) : ℝ) = C := Real.coe_toNNReal C (le_of_lt hC)
  rw [hcoe]
  exact hbound N hN

end

end Work.A3
