import Mathlib
import Submission.Work.ZeroDensity.LogFree.PoleDefs
import Submission.Commons.NumberTheory.Sieve.selberg_diagonalization_sigma

/-!
# `Work.ZeroDensity.LogFree.poleResidue_mul_log_sq`

The Selberg diagonalization of the pole residue: with `z = ⌈W⌉₊`,

  `poleResidue W · (log W)^2 = Σ_{l ≤ z} φ(l) · (Σ_{l ∣ d ≤ z} thetaL W d / d)^2`,

where `thetaL W d = log W · thetaM W d`.  The proof is the classical identity
`1/[d,e] = gcd(d,e)/(de)` followed by the diagonalization
`Σ_{d,e} a_d a_e gcd(d,e) = Σ_l φ(l)(Σ_{l∣d} a_d)^2` with `a_d = thetaM W d / d`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity.LogFree

open Work.LinnikContract

theorem poleResidue_mul_log_sq (W : ℝ) (hW : 1 < W) :
    poleResidue W * (Real.log W) ^ 2 = poleDiag W := by
  have hWpos : 0 < W := by linarith
  have hlog : Real.log W ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hWpos (ne_of_gt hW)
  -- the diagonalization with `T = Icc 1 ⌈W⌉₊`, `σ = 1`, `c = φ`, `a d = thetaM W d / d`
  have hdiag := Commons.NumberTheory.Sieve.sum_gcd_rpow_diagonalization
    (Finset.Icc 1 ⌈W⌉₊)
    (fun d hd => by have := (Finset.mem_Icc.mp hd).1; omega)
    (fun {l d} hld hd => by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hd
      have hdpos : 0 < d := by omega
      exact Finset.mem_Icc.mpr
        ⟨Nat.pos_of_dvd_of_pos hld hdpos, le_trans (Nat.le_of_dvd hdpos hld) h2⟩)
    1 (fun n => (Nat.totient n : ℝ))
    (fun n _ => by rw [← Nat.cast_sum, Nat.sum_totient, Real.rpow_one])
    (fun d => Work.LinnikAreas.Density4.thetaM W d / (d : ℝ))
  -- the left-hand side of the diagonalization is the pole residue
  have hLHS : (∑ d ∈ Finset.Icc 1 ⌈W⌉₊, ∑ e ∈ Finset.Icc 1 ⌈W⌉₊,
        Work.LinnikAreas.Density4.thetaM W d / (d : ℝ)
          * (Work.LinnikAreas.Density4.thetaM W e / (e : ℝ))
          * (Nat.gcd d e : ℝ) ^ (1 : ℝ)) = poleResidue W := by
    rw [poleResidue]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    have hd0 : d ≠ 0 := by have := (Finset.mem_Icc.mp hd).1; omega
    have he0 : e ≠ 0 := by have := (Finset.mem_Icc.mp he).1; omega
    rw [Real.rpow_one, eq_comm]
    exact Commons.NumberTheory.Sieve.lcm_term (Work.LinnikAreas.Density4.thetaM W) hd0 he0
  -- rewrite `thetaM` in terms of `thetaL`
  have hscale : ∀ l : ℕ,
      (∑ d ∈ (Finset.Icc 1 ⌈W⌉₊).filter (fun d => l ∣ d),
          Work.LinnikAreas.Density4.thetaM W d / (d : ℝ))
        = (∑ d ∈ (Finset.Icc 1 ⌈W⌉₊).filter (fun d => l ∣ d), thetaL W d / (d : ℝ))
            / Real.log W := by
    intro l
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    rw [thetaM_eq_thetaL_div hW d]
    ring
  have hdiag2 : poleResidue W
      = (∑ l ∈ Finset.Icc 1 ⌈W⌉₊, (Nat.totient l : ℝ)
          * (∑ d ∈ (Finset.Icc 1 ⌈W⌉₊).filter (fun d => l ∣ d), thetaL W d / (d : ℝ)) ^ 2)
        / (Real.log W) ^ 2 := by
    rw [hLHS] at hdiag
    rw [hdiag]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l _
    rw [hscale l, div_pow]
    ring
  have hdiagSum : poleDiag W
      = ∑ l ∈ Finset.Icc 1 ⌈W⌉₊, (Nat.totient l : ℝ)
          * (∑ d ∈ (Finset.Icc 1 ⌈W⌉₊).filter (fun d => l ∣ d), thetaL W d / (d : ℝ)) ^ 2 := by
    rw [poleDiag]
    rfl
  rw [hdiag2, hdiagSum]
  exact div_mul_cancel₀ _ (pow_ne_zero 2 hlog)

end Work.ZeroDensity.LogFree
