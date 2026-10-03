import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Work.FIArea5.S16Hecke.isPrimary_iff_coset
import Submission.Work.FIArea6Hecke.area5_6_of_S16Core
import Submission.Work.FIArea6Hecke.R.HeckeDiscRed
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea5.HeckeZFR.LSeriesBound
import Submission.Work.FIArea6Hecke.R.heckeArch_facts
import Submission.Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_lower_bound_near_one
import Submission.Work.FIArea6Hecke.R.axisBadPoly_lower_bound
import Submission.Work.FIArea6Hecke.R.riemannZeta_lower_bound_near_one

namespace Work.FIArea6Hecke.R

/-- **No entire completion exists for the principal strict character.**  The Hecke `L`-series of
`principalStrict d` (the indicator of the units mod `4d`, extended by zero) has a pole at `s = 1`:
its coefficients `heckeLam (principalStrict d) 0 n` are `#{primary z : |z|² = n, z unit mod 4d} ≥ 0`
and their partial sums satisfy `Σ_{n≤X} heckeLam (principalStrict d) 0 n = #(unitBox d X) ≫ X`
(`Work.FIArea6Hecke.R.disc_card_growth`, sorry-free).  Abel summation then gives
`‖heckeLSeries (principalStrict d) 0 σ‖ → ∞` as `σ → 1⁺`, so `heckeArch d 0 s · heckeLSeries
(principalStrict d) 0 s` cannot extend to a function analytic on all of `ℂ` (a witness would be
continuous at `s = 1` while `heckeArch d 0 1 = 4d/π ≠ 0`).

Do not use `Work.FIArea6Hecke.R.noCompletion_of_primaryTrivial` or anything from
`Submission/Work/FIArea6Hecke/RC/` (they are proved by `sorry`); prove the divergence directly. -/
theorem noCompletion_principalStrict (d : ℕ) (hd : 1 ≤ d) :
    ¬ ∃ Lam : ℂ → ℂ, AnalyticOn ℂ Lam Set.univ ∧
      ∀ s : ℂ, 1 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
          Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 s := by
  -- Route (no use of `noCompletion_of_primaryTrivial` nor of `Submission/Work/FIArea6Hecke/RC/`):
  -- the classical Euler-product factorisation `L(s, principalStrict d) = ζ(s)·L(s,χ₄)·G_d(s)`
  -- on `re s > 1` (`heckeLSeries_principalStrict_eq`), together with the *pole of ζ at 1*
  -- (`riemannZeta_lower_bound_near_one`) and the lower bounds for the two remaining factors
  -- (`axisChi4_LSeries_lower_bound_near_one`, `axisBadPoly_lower_bound`), shows that the norm of
  -- the Hecke `L`-series of `principalStrict d` tends to infinity as `σ → 1⁺`.  On the other hand
  -- `heckeArch d 0` is holomorphic and non-vanishing on `re s > 0` (`heckeArch_facts`), so
  -- `Lam / heckeArch d 0` is analytic — hence locally bounded — at `s = 1`, and the two facts
  -- contradict each other on the real axis.
  classical
  rintro ⟨Lam, hAnal, hagr⟩
  -- `heckeArch d 0` is holomorphic and non-vanishing on `re s > 0`
  obtain ⟨hArch_ne, hArch_an⟩ := heckeArch_facts hd
  -- the quotient `Lam / heckeArch d 0` is analytic at `s = 1`
  have hF : AnalyticAt ℂ (fun s : ℂ => Lam s / Work.FITop4.Bridge.heckeArch d 0 s) 1 :=
    (hAnal.analyticAt (s := Set.univ) (by simp)).div (hArch_an 1 (by norm_num))
      (hArch_ne 1 (by norm_num))
  have hcont : ContinuousAt
      (fun σ : ℝ => Lam (σ : ℂ) / Work.FITop4.Bridge.heckeArch d 0 (σ : ℂ)) 1 :=
    ContinuousAt.comp (x := (1 : ℝ)) (f := Complex.ofReal)
      (g := fun s : ℂ => Lam s / Work.FITop4.Bridge.heckeArch d 0 s)
      hF.continuousAt Complex.continuous_ofReal.continuousAt
  -- hence it is bounded on a real neighbourhood of `1`
  obtain ⟨δE, hδEpos, hδE⟩ := (Metric.continuousAt_iff.mp hcont) 1 one_pos
  -- on the real axis it is `ζ(σ)·L(σ,χ₄)·G_d(σ)`
  have hagr' : ∀ σ : ℝ, 1 < σ →
      Lam (σ : ℂ) / Work.FITop4.Bridge.heckeArch d 0 (σ : ℂ)
        = riemannZeta (σ : ℂ) * LSeries axisChi4 (σ : ℂ) * axisBadPoly d (σ : ℂ) := by
    intro σ hσ
    have hσ' : 1 < (σ : ℂ).re := by simpa using hσ
    have hne : Work.FITop4.Bridge.heckeArch d 0 (σ : ℂ) ≠ 0 := hArch_ne _ (by linarith)
    rw [hagr (σ : ℂ) hσ', heckeLSeries_principalStrict_eq d hd hσ']
    exact mul_div_cancel_left₀ _ hne
  have hbound : ∀ σ : ℝ, |σ - 1| < δE →
      ‖Lam (σ : ℂ) / Work.FITop4.Bridge.heckeArch d 0 (σ : ℂ)‖
        < ‖Lam (1 : ℂ) / Work.FITop4.Bridge.heckeArch d 0 1‖ + 1 := by
    intro σ hσ
    have h : ‖Lam (σ : ℂ) / Work.FITop4.Bridge.heckeArch d 0 (σ : ℂ)
        - Lam (1 : ℂ) / Work.FITop4.Bridge.heckeArch d 0 1‖ < 1 := by
      have h' := hδE (by simpa [Real.dist_eq] using hσ)
      rw [dist_eq_norm] at h'
      simpa using h'
    calc ‖Lam (σ : ℂ) / Work.FITop4.Bridge.heckeArch d 0 (σ : ℂ)‖
        = ‖(Lam (σ : ℂ) / Work.FITop4.Bridge.heckeArch d 0 (σ : ℂ)
            - Lam (1 : ℂ) / Work.FITop4.Bridge.heckeArch d 0 1)
            + Lam (1 : ℂ) / Work.FITop4.Bridge.heckeArch d 0 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖Lam (σ : ℂ) / Work.FITop4.Bridge.heckeArch d 0 (σ : ℂ)
            - Lam (1 : ℂ) / Work.FITop4.Bridge.heckeArch d 0 1‖
          + ‖Lam (1 : ℂ) / Work.FITop4.Bridge.heckeArch d 0 1‖ := norm_add_le _ _
      _ < 1 + ‖Lam (1 : ℂ) / Work.FITop4.Bridge.heckeArch d 0 1‖ := by linarith
      _ = ‖Lam (1 : ℂ) / Work.FITop4.Bridge.heckeArch d 0 1‖ + 1 := by ring
  -- the three lower bounds for the factors `ζ`, `L(·,χ₄)` and `G_d` near `σ = 1`
  obtain ⟨cA, δA, hcA, hδA, hA⟩ := axisChi4_LSeries_lower_bound_near_one
  obtain ⟨δC, hδC, hC⟩ := riemannZeta_lower_bound_near_one
  obtain ⟨cD, hcD, hD⟩ := axisBadPoly_lower_bound d hd
  set B : ℝ := ‖Lam (1 : ℂ) / Work.FITop4.Bridge.heckeArch d 0 1‖ + 1 with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  set m : ℝ := min δE (min δA (min δC 1)) with hm
  have hmpos : 0 < m := by
    rw [hm]; exact lt_min hδEpos (lt_min hδA (lt_min hδC one_pos))
  set η : ℝ := min (m / 2) (cA * cD / (8 * B)) with hη
  have hηpos : 0 < η := by rw [hη]; exact lt_min (by linarith) (by positivity)
  have hηm : η < m := by rw [hη]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hηδE : η < δE := lt_of_lt_of_le hηm (min_le_left _ _)
  have hη1 : η < 1 :=
    lt_of_lt_of_le hηm (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hηδA : η < δA := lt_of_lt_of_le hηm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hηδC : η < δC :=
    lt_of_lt_of_le hηm (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hηP : η ≤ cA * cD / (8 * B) := by rw [hη]; exact min_le_right _ _
  have hP : 0 < cA * cD := by positivity
  have hsmall : B * (2 * η) < cA * cD := by
    have h1 : B * η ≤ B * (cA * cD / (8 * B)) := mul_le_mul_of_nonneg_left hηP (le_of_lt hBpos)
    have h2 : B * (cA * cD / (8 * B)) = cA * cD / 8 := by field_simp
    nlinarith [h1, h2, hP]
  have hbig : B < cA * cD / (2 * η) := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * η)]
    linarith [hsmall]
  -- the witness `σ = 1 + η`
  set σ : ℝ := 1 + η with hσdef
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ2 : σ ≤ 2 := by rw [hσdef]; linarith
  have hσA : σ < 1 + δA := by rw [hσdef]; linarith
  have hσC : σ < 1 + δC := by rw [hσdef]; linarith
  have hsub : (2 : ℝ) * (σ - 1) = 2 * η := by rw [hσdef]; ring
  have hupper : ‖Lam (σ : ℂ) / Work.FITop4.Bridge.heckeArch d 0 (σ : ℂ)‖ < B := by
    have h := hbound σ (by rw [hσdef, add_sub_cancel_left, abs_of_pos hηpos]; exact hηδE)
    rw [hB]; exact h
  have hlower : cA * cD / (2 * η) ≤ ‖Lam (σ : ℂ) / Work.FITop4.Bridge.heckeArch d 0 (σ : ℂ)‖ := by
    rw [hagr' σ hσ1, norm_mul, norm_mul]
    have h1 : 1 / (2 * η) ≤ ‖riemannZeta (σ : ℂ)‖ := by
      have := hC σ hσ1 hσC
      rwa [hsub] at this
    have h2 : cA ≤ ‖LSeries axisChi4 (σ : ℂ)‖ := hA σ hσ1 hσA
    have h3 : cD ≤ ‖axisBadPoly d (σ : ℂ)‖ := hD σ hσ1 hσ2
    have h12 : (1 / (2 * η)) * cA ≤ ‖riemannZeta (σ : ℂ)‖ * ‖LSeries axisChi4 (σ : ℂ)‖ :=
      mul_le_mul h1 h2 (le_of_lt hcA) (by positivity)
    have h123 : ((1 / (2 * η)) * cA) * cD
        ≤ (‖riemannZeta (σ : ℂ)‖ * ‖LSeries axisChi4 (σ : ℂ)‖) * ‖axisBadPoly d (σ : ℂ)‖ :=
      mul_le_mul h12 h3 (le_of_lt hcD) (by positivity)
    have heq : cA * cD / (2 * η) = ((1 / (2 * η)) * cA) * cD := by ring
    rw [heq]
    exact h123
  linarith [hupper, hbig, hlower]

end Work.FIArea6Hecke.R
