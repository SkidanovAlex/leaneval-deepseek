import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.NN.Core.TelTwoDF.bumpFlatAux
import Submission.Work.NN.Core.TelTwoDF.bumpMul_le_dist_of_flat
import Submission.Work.NN.Core.TelTwoDF.iteratedFDeriv_eq_zero_of_vanishing_on_exterior

namespace Work.NN.Core.TelTwoDF

open scoped NNReal ENNReal
open Set

/-- **Multiplication by a bump supported in a polydisc is bounded on the `C^{k,α}` scale.**

If `χ : ℂⁿ → ℂ` is `C^{k+1}` with compact support and vanishes outside the open polydisc
`polydisc 0 ρ` (`ρ j > 0`), then multiplying by `χ` is a bounded operator on `C^{k,α}` as soon as
the data are `C^k` merely *on the polydisc*: there is `C > 0` with

  `‖χ · u‖_{C^{k,α}(ℂⁿ)} ≤ C ‖u‖_{C^{k,α}(polydisc 0 ρ)}`

for every `u` which is `C^k` on the polydisc.  The point is that `χ` is flat on the closed
complement of the polydisc (it is `C^{k+1}` and vanishes there), so that `χ · u` is flat there as
well, and the Leibniz rule on the polydisc controls everything else. -/
theorem holderNorm_bump_mul_le {n : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (k : ℕ)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (χ : (Fin n → ℂ) → ℂ) (hχ : ContDiff ℝ (k + 1) χ)
    (hχs : HasCompactSupport χ) (hχsub : ∀ z : Fin n → ℂ, (∃ j, ρ j ≤ ‖z j‖) → χ z = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin n → ℂ) → ℂ,
      ContDiffOn ℝ (k : ℕ∞) u (Work.CR.Flat.polydisc 0 ρ) →
      Work.CR.Flat.holderNorm k α (fun z => χ z * u z) Set.univ
        ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm k α u (Work.CR.Flat.polydisc 0 ρ) := by
  set P : Set (Fin n → ℂ) := Work.CR.Flat.polydisc 0 ρ with hP
  have hPopen : IsOpen P := by rw [hP]; exact Work.CR.Flat.isOpen_polydisc 0 ρ
  have hPud : UniqueDiffOn ℝ P := hPopen.uniqueDiffOn
  -- the product estimate on the polydisc
  obtain ⟨A, hApos, hA⟩ :=
    Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport (n := n) (Ω := P) hPud hα0 hα1
      hχ hχs
  -- flatness and decay of the derivatives of `χ` at the closed exterior
  obtain ⟨L, hLpos, hLbound, hflatχ, hlipχ, hsqχ⟩ :=
    bumpFlat_facts (n := n) (k := k) hρ hχ hχs hχsub
  -- the constant
  set C₀ : ℝ := (A + 1) * (L + 1) * 2 ^ (k + 2) with hC0def
  have hC0pos : 0 < C₀ := by rw [hC0def]; positivity
  have hC0A : A ≤ C₀ := by
    have h1 : A + 1 ≤ C₀ := by
      rw [hC0def]
      have hL1 : (1 : ℝ) ≤ L + 1 := by linarith
      have hpow : (1 : ℝ) ≤ 2 ^ (k + 2) := one_le_pow₀ (by norm_num)
      have hA1 : (0 : ℝ) ≤ A + 1 := by linarith [hApos]
      have h4 : (0 : ℝ) ≤ (A + 1) * (L + 1) := mul_nonneg hA1 (by linarith : (0 : ℝ) ≤ L + 1)
      calc A + 1 = (A + 1) * 1 := by ring
        _ ≤ (A + 1) * (L + 1) := mul_le_mul_of_nonneg_left hL1 hA1
        _ = (A + 1) * (L + 1) * 1 := by ring
        _ ≤ (A + 1) * (L + 1) * 2 ^ (k + 2) := mul_le_mul_of_nonneg_left hpow h4
    linarith
  have hC0pow : ∀ m ≤ k, 2 ^ m * L ≤ C₀ := by
    intro m hm
    rw [hC0def]
    have hp : (2 : ℝ) ^ m ≤ 2 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : L ≤ L + 1 := by linarith
    have h3 : (1 : ℝ) ≤ A + 1 := by linarith [hApos]
    have h5 : (0 : ℝ) ≤ 2 ^ (k + 2) * (L + 1) := by positivity
    calc (2 : ℝ) ^ m * L ≤ 2 ^ (k + 2) * L := mul_le_mul_of_nonneg_right hp hLpos.le
      _ ≤ 2 ^ (k + 2) * (L + 1) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 ^ (k + 2) * (L + 1) * 1 := by ring
      _ ≤ 2 ^ (k + 2) * (L + 1) * (A + 1) := mul_le_mul_of_nonneg_left h3 h5
      _ = (A + 1) * (L + 1) * 2 ^ (k + 2) := by ring
  refine ⟨((k : ℝ) + 2) * (8 * C₀), by positivity, ?_⟩
  intro u hu
  set Hu : ℝ≥0∞ := Work.CR.Flat.holderNorm k α u P with hHudef
  by_cases hHutop : Hu = ⊤
  · rw [hHutop, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))]
    exact le_top
  set Mu : ℝ := Hu.toReal with hMudef
  have hMu_nn : 0 ≤ Mu := ENNReal.toReal_nonneg
  have hHu_ofReal : Hu = ENNReal.ofReal Mu := (ENNReal.ofReal_toReal hHutop).symm
  set f : (Fin n → ℂ) → ℂ := fun z => χ z * u z with hfdef
  have hprod0 : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → f z = 0 := fun z hz => by
    change χ z * u z = 0
    rw [hχsub z hz, zero_mul]
  -- bounds on the within-derivatives of `u`
  have hu_bd : ∀ j ≤ k, ∀ x ∈ P, ‖iteratedFDerivWithin ℝ j u P x‖ ≤ Mu := by
    intro j hj x hx
    have h1 : ENNReal.ofReal ‖iteratedFDerivWithin ℝ j u P x‖ ≤ ENNReal.ofReal Mu := by
      rw [← hHu_ofReal]
      exact le_trans (Work.CR.Flat.le_iterDerivNorm j u P hx)
        (Work.CR.Flat.iterDerivNorm_le_holderNorm k α u P hj)
    exact (ENNReal.ofReal_le_ofReal_iff hMu_nn).mp h1
  -- the product estimate on `P`, in terms of `Hu`
  have hfP : Work.CR.Flat.holderNorm k α f P ≤ ENNReal.ofReal C₀ * Hu := by
    have h := hA u hu
    rw [← hfdef] at h
    rw [← hHudef] at h
    exact h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hC0A) Hu)
  -- the absolute bound on the derivatives of the product
  have hPm : ∀ (m : ℕ), m ≤ k → ∀ x ∈ P, ‖iteratedFDeriv ℝ m f x‖ ≤ C₀ * Mu := by
    intro m hm x hx
    have h1 : ENNReal.ofReal ‖iteratedFDeriv ℝ m f x‖ ≤ ENNReal.ofReal C₀ * Hu := by
      rw [← (iteratedFDerivWithin_of_isOpen (s := P) m hPopen) hx]
      exact le_trans (Work.CR.Flat.le_iterDerivNorm m f P hx)
        (le_trans (Work.CR.Flat.iterDerivNorm_le_holderNorm k α f P hm) hfP)
    rw [hHu_ofReal, ← ENNReal.ofReal_mul hC0pos.le] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0pos.le hMu_nn)).mp h1
  have hAllm : ∀ (m : ℕ), m ≤ k → ∀ z, ‖iteratedFDeriv ℝ m f z‖ ≤ C₀ * Mu := by
    intro m hm z
    by_cases hzE : ∃ j, ρ j ≤ ‖z j‖
    · rw [iteratedFDeriv_eq_zero_of_vanishing_on_exterior hρ hprod0 m hzE]
      have h0 : (0 : ℝ) ≤ C₀ * Mu := mul_nonneg hC0pos.le hMu_nn
      simpa only [norm_zero] using h0
    · refine hPm m hm z ?_
      rw [hP, Work.CR.Flat.mem_polydisc]
      intro j
      exact lt_of_not_ge fun hle => hzE ⟨j, by simpa using hle⟩
  -- the mixed case: `x` inside the polydisc, `y` in the closed exterior
  have hmixed : ∀ (m : ℕ), m ≤ k → ∀ x ∈ P, ∀ y, (∃ j, ρ j ≤ ‖y j‖) → x ≠ y →
      ‖x - y‖ ≤ 1 →
      ENNReal.ofReal (‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal (4 * C₀) * Hu := by
    intro m hm x hxP y hyE hxy hclose
    rw [iteratedFDeriv_eq_zero_of_vanishing_on_exterior hρ hprod0 m hyE, sub_zero]
    have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hbd : ‖iteratedFDeriv ℝ m f x‖ ≤ 2 ^ m * L * Mu * ‖x - y‖ :=
      bumpMul_le_dist_of_flat hρ hχ hχsub hLbound hu hu_bd hm x hxP y hyE
    have hreal : ‖iteratedFDeriv ℝ m f x‖ / ‖x - y‖ ^ α ≤ C₀ * Mu := by
      calc ‖iteratedFDeriv ℝ m f x‖ / ‖x - y‖ ^ α
          ≤ (2 ^ m * L * Mu * ‖x - y‖) / ‖x - y‖ ^ α :=
            div_le_div_of_nonneg_right hbd (Real.rpow_nonneg hr.le α)
        _ = 2 ^ m * L * Mu * (‖x - y‖ / ‖x - y‖ ^ α) := by ring
        _ = 2 ^ m * L * Mu * ‖x - y‖ ^ (1 - α) := by
            have hdiv : ‖x - y‖ / ‖x - y‖ ^ α = ‖x - y‖ ^ (1 - α) := by
              have h := Real.rpow_sub hr (1 : ℝ) α
              rw [Real.rpow_one] at h
              exact h.symm
            rw [hdiv]
        _ ≤ 2 ^ m * L * Mu * 1 :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_one hr.le hclose (by linarith)) (by positivity)
        _ = 2 ^ m * L * Mu := by ring
        _ ≤ C₀ * Mu := mul_le_mul_of_nonneg_right (hC0pow m hm) hMu_nn
    refine le_trans (ENNReal.ofReal_le_ofReal hreal) ?_
    rw [ENNReal.ofReal_mul hC0pos.le, hHu_ofReal]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith [hC0pos] : C₀ ≤ 4 * C₀)) _
  -- the per-order bound
  have key : ∀ m ≤ k, Work.CR.Flat.iterDerivNorm m f Set.univ
      + Work.CR.Flat.holderSeminorm m α f Set.univ ≤ ENNReal.ofReal (8 * C₀) * Hu := by
    intro m hm
    have hI : Work.CR.Flat.iterDerivNorm m f Set.univ ≤ ENNReal.ofReal C₀ * Hu := by
      rw [Work.CR.Flat.iterDerivNorm]
      refine iSup₂_le fun x _ => ?_
      rw [iteratedFDerivWithin_univ]
      calc ENNReal.ofReal ‖iteratedFDeriv ℝ m f x‖ ≤ ENNReal.ofReal (C₀ * Mu) :=
            ENNReal.ofReal_le_ofReal (hAllm m hm x)
        _ = ENNReal.ofReal C₀ * Hu := by rw [ENNReal.ofReal_mul hC0pos.le, hHu_ofReal]
    have hH : Work.CR.Flat.holderSeminorm m α f Set.univ ≤ ENNReal.ofReal (4 * C₀) * Hu := by
      rw [Work.CR.Flat.holderSeminorm]
      refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
      simp only [iteratedFDerivWithin_univ]
      by_cases hfar : 1 < ‖x - y‖
      · -- far apart: only the absolute bounds are needed
        have hge : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow hfar.le hα0
        have hreal : ‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ / ‖x - y‖ ^ α
            ≤ 2 * (C₀ * Mu) := by
          have h1 : ‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ ≤ 2 * (C₀ * Mu) := by
            have h2 := norm_sub_le (iteratedFDeriv ℝ m f x) (iteratedFDeriv ℝ m f y)
            linarith [hAllm m hm x, hAllm m hm y]
          exact le_trans (div_le_self (norm_nonneg _) hge) h1
        refine le_trans (ENNReal.ofReal_le_ofReal hreal) ?_
        rw [show 2 * (C₀ * Mu) = (2 * C₀) * Mu by ring,
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * C₀), hHu_ofReal]
        exact mul_le_mul_left
          (ENNReal.ofReal_le_ofReal (by linarith [hC0pos] : 2 * C₀ ≤ 4 * C₀)) _
      · push_neg at hfar
        by_cases hxP : x ∈ P
        · by_cases hyP : y ∈ P
          · -- both points in the polydisc: use the norm on `P`
            rw [← (iteratedFDerivWithin_of_isOpen (s := P) m hPopen) hxP,
              ← (iteratedFDerivWithin_of_isOpen (s := P) m hPopen) hyP]
            refine le_trans (Work.CR.Flat.le_holderSeminorm m α f P hxP hyP hxy)
              (le_trans (Work.CR.Flat.holderSeminorm_le_holderNorm k α f P hm) ?_)
            exact hfP.trans
              (mul_le_mul_left
                (ENNReal.ofReal_le_ofReal (by linarith [hC0pos] : C₀ ≤ 4 * C₀)) Hu)
          · -- `x` inside, `y` in the closed exterior
            have hyE : ∃ j, ρ j ≤ ‖y j‖ := by
              by_contra hcon
              push_neg at hcon
              exact hyP (by
                rw [hP, Work.CR.Flat.mem_polydisc]
                exact fun j => by simpa using hcon j)
            exact hmixed m hm x hxP y hyE hxy hfar
        · -- `x` in the closed exterior
          have hxE : ∃ j, ρ j ≤ ‖x j‖ := by
            by_contra hcon
            push_neg at hcon
            exact hxP (by
              rw [hP, Work.CR.Flat.mem_polydisc]
              exact fun j => by simpa using hcon j)
          by_cases hyP : y ∈ P
          · rw [norm_sub_rev (iteratedFDeriv ℝ m f x) (iteratedFDeriv ℝ m f y),
              norm_sub_rev x y]
            exact hmixed m hm y hyP x hxE (Ne.symm hxy) (by rw [norm_sub_rev]; exact hfar)
          · have hyE : ∃ j, ρ j ≤ ‖y j‖ := by
              by_contra hcon
              push_neg at hcon
              exact hyP (by
                rw [hP, Work.CR.Flat.mem_polydisc]
                exact fun j => by simpa using hcon j)
            rw [iteratedFDeriv_eq_zero_of_vanishing_on_exterior hρ hprod0 m hxE,
              iteratedFDeriv_eq_zero_of_vanishing_on_exterior hρ hprod0 m hyE]
            simp
    calc Work.CR.Flat.iterDerivNorm m f Set.univ + Work.CR.Flat.holderSeminorm m α f Set.univ
        ≤ ENNReal.ofReal C₀ * Hu + ENNReal.ofReal (4 * C₀) * Hu := add_le_add hI hH
      _ = ENNReal.ofReal (5 * C₀) * Hu := by
          rw [← add_mul, ← ENNReal.ofReal_add hC0pos.le (by positivity : (0 : ℝ) ≤ 4 * C₀)]
          congr 1
          ring_nf
      _ ≤ ENNReal.ofReal (8 * C₀) * Hu :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith [hC0pos] : 5 * C₀ ≤ 8 * C₀)) _
  have hsum : Work.CR.Flat.holderNorm k α f Set.univ
      ≤ ENNReal.ofReal (((k : ℝ) + 2) * (8 * C₀)) * Hu := by
    rw [Work.CR.Flat.holderNorm]
    calc ∑ m ∈ Finset.range (k + 1),
            (Work.CR.Flat.iterDerivNorm m f Set.univ + Work.CR.Flat.holderSeminorm m α f Set.univ)
        ≤ ∑ m ∈ Finset.range (k + 1), ENNReal.ofReal (8 * C₀) * Hu :=
          Finset.sum_le_sum fun m hm' => key m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm'))
      _ = ((k + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (8 * C₀) * Hu) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal ((k : ℝ) + 2) * (ENNReal.ofReal (8 * C₀) * Hu) :=
          mul_le_mul_left (by
            rw [← ENNReal.ofReal_natCast (k + 1)]
            exact ENNReal.ofReal_le_ofReal (by push_cast; linarith)) _
      _ = ENNReal.ofReal (((k : ℝ) + 2) * (8 * C₀)) * Hu := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (k : ℝ) + 2)]
  exact hsum

end Work.NN.Core.TelTwoDF
