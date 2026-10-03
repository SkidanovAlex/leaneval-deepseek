import Mathlib
import Submission.Work.FIArea6Hecke.R.HeckeCompletionAll
import Submission.Work.FIArea5.S16Hecke.heckeFE_of_theta
import Submission.Work.FIArea5.S16Hecke.thetaHol_exp_decay
import Submission.Work.FIArea6Hecke.R.LamRightHalf.Defs
import Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaHol_one_div_dual
import Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaDualM_continuous
import Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaDualM_decay
import Submission.Work.FIArea6Hecke.R.LamRightHalf.estimates
import Submission.Work.FIArea6Hecke.R.LamRightHalf.completion_growth
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_conj

namespace Work.FIArea6Hecke.R

/-- Conjugating the character relates the two weights: `ψ_{χ̄,k} = conj ψ_{χ,-k}`. -/
private lemma psi_conj_neg (chi : GaussianInt → ℂ) (k : ℕ) (z : GaussianInt) :
    star (Work.FIArea5.S16Hecke.psi chi (-(k : ℤ)) z)
      = Work.FIArea5.S16Hecke.psi (fun z : GaussianInt => star (chi z)) (k : ℤ) z := by
  have h := Work.FIArea5.S16Hecke.psi_conj (fun z : GaussianInt => star (chi z)) k z
  rw [show (fun z : GaussianInt => star (star (chi z))) = chi from
    funext (fun z => star_star (chi z))] at h
  rw [h, star_star]

/-- Conjugating the `L`-function relates the two weights:
`conj L(conj s, ψ_{χ,-k}) = L(s, ψ_{χ̄,k})`. -/
private lemma heckeLSeries_conj_neg (chi : GaussianInt → ℂ) (k : ℕ) (s : ℂ) :
    star (Work.FIArea5.S16Hecke.heckeLSeries chi (-(k : ℤ)) (star s))
      = Work.FIArea5.S16Hecke.heckeLSeries (fun z : GaussianInt => star (chi z)) (k : ℤ) s := by
  have h := Work.FIArea5.S16Hecke.heckeLSeries_conj (fun z : GaussianInt => star (chi z)) k (star s)
  rw [show (fun z : GaussianInt => star (star (chi z))) = chi from
    funext (fun z => star_star (chi z)), star_star] at h
  rw [h, star_star]

theorem lamRightHalf_strict (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ)
    (hd : 1 ≤ d) (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hne : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
      Work.FIArea5.S16Hecke.psi chi m z ≠ 1)
    (hAn : AnalyticOn ℂ Lam Set.univ)
    (hagr : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d m s * Work.FIArea5.S16Hecke.heckeLSeries chi m s) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ w : ℂ, (1 / 2 : ℝ) ≤ w.re →
      Real.log ‖Lam w‖ ≤ c * (‖w‖ + 3) * (Real.log (‖w‖ + 5) + K) := by
  by_cases hm : (0 : ℤ) ≤ m
  · -- non-negative weight: `completion_growth_nat`
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = (k : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
    have hne' : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
        Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
        Work.FIArea5.S16Hecke.psi chi (k : ℤ) z ≠ 1 := hne
    obtain ⟨c, K, hc, hK, hbound⟩ := completion_growth_nat d hd chi k hchi hne'
    refine ⟨c, K, hc, hK, fun w hw => ?_⟩
    refine hbound Lam hAn ?_ w hw
    intro s hs
    apply hagr s
    have habs : |((k : ℤ) : ℝ)| = (k : ℝ) := by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k : ℤ) : ℝ)), Int.cast_natCast]
    rw [habs]
    exact hs
  · -- negative weight: conjugate to the positive weight `k = -m` of the conjugate character
    push_neg at hm
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -((k : ℕ) : ℤ) := ⟨m.natAbs, by omega⟩
    have hchi_c : Work.FIArea5.S16Hecke.IsCharMod4dStrict d (fun z : GaussianInt => star (chi z)) :=
      isCharMod4dStrict_conj hchi
    have hne_c : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
        Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
        Work.FIArea5.S16Hecke.psi (fun z : GaussianInt => star (chi z)) (k : ℤ) z ≠ 1 := by
      obtain ⟨z, hz1, hz2, hz3⟩ := hne
      refine ⟨z, hz1, hz2, ?_⟩
      intro hc
      apply hz3
      have h3 : star (Work.FIArea5.S16Hecke.psi chi (-(k : ℤ)) z) = (1 : ℂ) := by
        rw [psi_conj_neg chi k z]
        exact hc
      have h4 := congrArg star h3
      simpa using h4
    obtain ⟨c, K, hc, hK, hbound⟩ :=
      completion_growth_nat d hd (fun z : GaussianInt => star (chi z)) k hchi_c hne_c
    have hΛ_an : AnalyticOn ℂ (fun s : ℂ => star (Lam (star s))) Set.univ := by
      refine DifferentiableOn.analyticOn ?_ isOpen_univ
      intro z _
      have h1 : DifferentiableAt ℂ Lam (star z) := (hAn.analyticAt Filter.univ_mem).differentiableAt
      have h3 := DifferentiableAt.conj_conj (f := Lam) (x := star z) h1
      have h3' : DifferentiableAt ℂ (fun s : ℂ => star (Lam (star s))) (star (star z)) := h3
      rw [star_star] at h3'
      exact h3'.differentiableWithinAt
    have hΛ_agr : ∀ s : ℂ, 1 + (k : ℝ) / 2 < s.re →
        star (Lam (star s)) = Work.FITop4.Bridge.heckeArch d (k : ℤ) s *
          Work.FIArea5.S16Hecke.heckeLSeries (fun z : GaussianInt => star (chi z)) (k : ℤ) s := by
      intro s hs
      have hs' : 1 + |((-(k : ℕ) : ℤ) : ℝ)| / 2 < (star s).re := by
        rw [Complex.star_def, Complex.conj_re]
        have habs : |((-(k : ℕ) : ℤ) : ℝ)| = (k : ℝ) := by
          rw [show ((-(k : ℕ) : ℤ) : ℝ) = -((k : ℤ) : ℝ) by push_cast; ring, abs_neg,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k : ℤ) : ℝ)), Int.cast_natCast]
        rw [habs]
        exact hs
      have hAconj : star (Work.FITop4.Bridge.heckeArch d (-(k : ℤ)) (star s))
          = Work.FITop4.Bridge.heckeArch d (k : ℤ) s := by
        have h := star_heckeArch d (-(k : ℤ)) s hd
        simpa using h
      rw [hagr (star s) hs', star_mul, hAconj, heckeLSeries_conj_neg chi k s]
      ring
    refine ⟨c, K, hc, hK, fun w hw => ?_⟩
    have hb := hbound (fun s : ℂ => star (Lam (star s))) hΛ_an hΛ_agr (star w) (by
      rw [Complex.star_def, Complex.conj_re]
      exact hw)
    simpa using hb

end Work.FIArea6Hecke.R
