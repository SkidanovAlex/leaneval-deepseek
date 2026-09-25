import Mathlib
import Submission.Work.NN.Core.bmRow
import Submission.Work.NN.Core.bmPotential_holder
import Submission.Work.NN.Core.bmPot_holder_C0a
import Submission.Work.NN.Core.bmPot_riesz_Ck
import Submission.Work.NN.Core.contDiff_flatMul
import Submission.Work.NN.Core.holderNorm_bmH_le
import Submission.Work.NN.Core.holderNorm_bmH_le_uniform
import Submission.Work.NN.Core.holderNorm_const_mul_le
import Submission.Work.NN.Core.fderiv_eq_zero_of_vanishing_off_polydisc
import Submission.Work.CR.Flat.Holder.holderNorm_add_le

namespace Work.NN.Core

open scoped NNReal ENNReal Topology ContDiff
open Set Filter
open Work.CR.Flat
open Work.CR.Flat.Cauchy

noncomputable section

variable {n : ℕ}

/-- `∂̄_j χ` is smooth when `χ` is. -/
lemma contDiff_dbarCoord {j : Fin n} {χ : Cn n → ℂ} (hχ : ContDiff ℝ ⊤ χ) :
    ContDiff ℝ ∞ (fun z => dbarCoord j χ z) := by
  have hχ' : ContDiff ℝ ∞ χ := hχ.of_le le_top
  have hfd : ContDiff ℝ ∞ (fderiv ℝ χ) := (contDiff_infty_iff_fderiv.mp hχ').2
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ χ z (Pi.single j (1 : ℂ))) :=
    hfd.clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun z => fderiv ℝ χ z (Pi.single j (Complex.I : ℂ))) :=
    hfd.clm_apply contDiff_const
  have h3 : ContDiff ℝ ∞
      (fun z => (1 / 2 : ℂ) * (fderiv ℝ χ z (Pi.single j (1 : ℂ))
        + Complex.I * fderiv ℝ χ z (Pi.single j (Complex.I : ℂ)))) :=
    contDiff_const.mul (h1.add (contDiff_const.mul h2))
  simpa only [dbarCoord] using h3

/-- `∂̄_j χ` vanishes on the closed complement of the open polydisc. -/
lemma dbarCoord_eq_zero_of_vanishing_off_polydisc {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {χ : Cn n → ℂ} (hχ : ContDiff ℝ 1 χ)
    (hχsub : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → χ z = 0) :
    ∀ (j : Fin n) z, (∃ i, ρ i ≤ ‖z i‖) → dbarCoord j χ z = 0 := by
  intro j z hz
  have h := fderiv_eq_zero_of_vanishing_off_polydisc hρ hχ hχsub z hz
  simp [dbarCoord, h]

/-- Congruence of `holderNorm` on a set. -/
lemma holderNorm_congr_on {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {α : ℝ} {Ω : Set X} {f g : X → ℂ} (h : ∀ x ∈ Ω, f x = g x) :
    holderNorm k α f Ω = holderNorm k α g Ω := by
  rw [holderNorm, holderNorm]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  · rw [iterDerivNorm, iterDerivNorm]
    refine iSup_congr fun x => iSup_congr fun hx => ?_
    rw [iteratedFDerivWithin_congr (fun y hy => (h y hy).symm) hx i]
  · rw [holderSeminorm, holderSeminorm]
    refine iSup_congr fun x => iSup_congr fun hx => iSup_congr fun y => iSup_congr fun hy => ?_
    rw [iteratedFDerivWithin_congr (fun w hw => (h w hw).symm) hx i,
      iteratedFDerivWithin_congr (fun w hw => (h w hw).symm) hy i]

/-- The `(0,2)`-form `bmH χ ζ j m` as an explicit sum of three flat products. -/
lemma bmH_eq (χ : Cn n → ℂ) (ζ : Fin n → Fin n → Cn n → ℂ)
    (j m l : Fin n) :
    bmH χ ζ j m l = fun z => dbarCoord l χ z * ζ j m z
      + dbarCoord j χ z * ζ m l z - dbarCoord m χ z * ζ j l z := by
  funext z
  simp only [bmH]

/-- **The defect of one Bochner–Martinelli step gains one derivative where the cut-off is `1`.** -/
theorem bmDefect_gain {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) (hlt : ∀ j, ρ' j < ρ j)
    (χ : Work.NN.Core.Cn n → ℂ) (hχ : ContDiff ℝ ⊤ χ) (hχcs : HasCompactSupport χ)
    (hχsub : ∀ z, (∃ j, ρ j ≤ ‖z j‖) → χ z = 0)
    (hχone : ∀ z, z ∈ Work.CR.Flat.polydisc 0 ρ' → χ z = 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ζ : Fin n → Fin n → Work.NN.Core.Cn n → ℂ,
      (∀ i l, ContDiffOn ℝ (k + 1) (ζ i l) (Work.CR.Flat.polydisc 0 ρ)) →
      ∀ j m, Work.CR.Flat.holderNorm (k + 1) α (Work.NN.Core.bmDefect χ ζ j m)
          (Work.CR.Flat.polydisc 0 ρ')
        ≤ ENNReal.ofReal C * ∑ i, ∑ l,
            Work.CR.Flat.holderNorm k α (ζ i l) (Work.CR.Flat.polydisc 0 ρ) := by
  classical
  -- the two Schauder inputs, with the outer radii `2ρ`
  obtain ⟨CD, hCDpos, hCD⟩ := bmPot_riesz_Ck (n := n) hn (c := 0)
    (r := fun j => 2 * ρ j) hα hα1 (fun j => by linarith [hρ j]) k
  obtain ⟨CE, hCEpos, hCE⟩ := holderNorm_bmH_le_uniform (n := n) hn hα hα1 hρ χ hχ hχsub
  refine ⟨‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖ * CD * ((n : ℝ) * CE + 1) + 1,
    by positivity, ?_⟩
  intro ζ hζ j m
  set M : ℝ≥0∞ := ∑ i, ∑ l, holderNorm k α (ζ i l) (polydisc 0 ρ) with hMdef
  by_cases hMtop : M = ⊤
  · rw [hMtop, ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  · have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by simp)
    have hdbar_smooth : ∀ (i : Fin n), ContDiff ℝ ∞ (fun z => dbarCoord i χ z) :=
      fun i => contDiff_dbarCoord hχ
    have hdbar_zero : ∀ (i : Fin n) z, (∃ t, ρ t ≤ ‖z t‖) → dbarCoord i χ z = 0 :=
      fun i => dbarCoord_eq_zero_of_vanishing_off_polydisc hρ hχ1 hχsub i
    have hζfin : ∀ i l, holderNorm k α (ζ i l) (polydisc 0 ρ) ≠ ⊤ := by
      intro i l
      refine ne_top_of_le_ne_top hMtop ?_
      rw [hMdef]
      exact le_trans
        (Finset.single_le_sum (f := fun l' => holderNorm k α (ζ i l') (polydisc 0 ρ))
          (fun l' _ => bot_le) (Finset.mem_univ l))
        (Finset.single_le_sum (f := fun i' => ∑ l',
            holderNorm k α (ζ i' l') (polydisc 0 ρ))
          (fun i' _ => bot_le) (Finset.mem_univ i))
    set G : Fin n → Cn n → ℂ := fun l => bmH χ ζ j m l with hGdef
    -- `(B)`: the components of `bmH` are `C^k`
    have hGcont : ∀ l, ContDiff ℝ k (G l) := by
      intro l
      rw [hGdef]
      beta_reduce
      rw [bmH_eq]
      have t1 : ContDiff ℝ k (fun z => dbarCoord l χ z * ζ j m z) :=
        contDiff_flatMul_of_smooth hρ (hdbar_smooth l) (hdbar_zero l) (show ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞) (ζ j m) (polydisc 0 ρ) from hζ j m) (hζfin j m)
      have t2 : ContDiff ℝ k (fun z => dbarCoord j χ z * ζ m l z) :=
        contDiff_flatMul_of_smooth hρ (hdbar_smooth j) (hdbar_zero j) (show ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞) (ζ m l) (polydisc 0 ρ) from hζ m l) (hζfin m l)
      have t3 : ContDiff ℝ k (fun z => dbarCoord m χ z * ζ j l z) :=
        contDiff_flatMul_of_smooth hρ (hdbar_smooth m) (hdbar_zero m) (show ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞) (ζ j l) (polydisc 0 ρ) from hζ j l) (hζfin j l)
      simpa using (t1.add t2).sub t3
    -- `(E1)`: the components are bounded in `C^{k,α}` on all of `ℂⁿ`
    have hGfin : ∀ l, holderNorm k α (G l) Set.univ < ⊤ := by
      intro l
      have h := hCE ζ hζ hζfin j m l
      rw [hGdef]
      refine lt_of_le_of_lt h ?_
      exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
        (lt_top_iff_ne_top.mpr hMtop)
    -- they vanish off the polydisc `polydisc 0 (2ρ)`
    have hGsupp : ∀ l z, (∃ i, (fun j => 2 * ρ j) i / 2 ≤ ‖z i‖) → G l z = 0 := by
      intro l z hz
      obtain ⟨i, hi⟩ := hz
      have hi' : ρ i ≤ ‖z i‖ := by
        rw [show (fun j => 2 * ρ j) i / 2 = ρ i from by ring] at hi; exact hi
      rw [hGdef]
      simp only [bmH, hdbar_zero l z ⟨i, hi'⟩, hdbar_zero j z ⟨i, hi'⟩,
        hdbar_zero m z ⟨i, hi'⟩, zero_mul, add_zero, sub_zero]
    -- the Schauder estimate on `polydisc 0 ρ`
    have hD := hCD G hGcont hGfin (fun l z hz => hGsupp l z (by simpa using hz))
    rw [← show (fun z => bmPot G z) = bmPotential G from
      funext (fun z => (bmPotential_eq_bmPot G z).symm)] at hD
    have hpol : polydisc (0 : Cn n) (fun j => 2 * ρ j / 2) = polydisc 0 ρ := by
      congr 1; funext j; ring
    rw [hpol] at hD
    -- restrict to `polydisc 0 ρ'`
    have hmono : holderNorm (k + 1) α (fun z => bmPot G z) (polydisc 0 ρ')
        ≤ holderNorm (k + 1) α (fun z => bmPot G z) (polydisc 0 ρ) :=
      holderNorm_mono_set (isOpen_polydisc 0 ρ) (isOpen_polydisc 0 ρ')
        (polydisc_mono (fun j => le_of_lt (hlt j))) (k + 1) α _
    have hD' : holderNorm (k + 1) α (fun z => bmPot G z) (polydisc 0 ρ')
        ≤ ENNReal.ofReal CD * ∑ l, holderNorm k α (G l) Set.univ :=
      hmono.trans hD
    -- bound the sum of the data norms
    have hsum_le : ∑ l, holderNorm k α (G l) Set.univ
        ≤ ENNReal.ofReal ((n : ℝ) * CE) * M := by
      have hstep : ∀ l ∈ Finset.univ, holderNorm k α (G l) Set.univ
          ≤ ENNReal.ofReal CE * M := by
        intro l _
        have h := hCE ζ hζ hζfin j m l
        rw [hGdef]
        exact h
      calc ∑ l, holderNorm k α (G l) Set.univ
          ≤ ∑ _l : Fin n, (ENNReal.ofReal CE * M) := Finset.sum_le_sum hstep
        _ = (n : ℝ≥0∞) * (ENNReal.ofReal CE * M) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = ENNReal.ofReal ((n : ℝ) * CE) * M := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
    have hD'' : holderNorm (k + 1) α (fun z => bmPot G z) (polydisc 0 ρ')
        ≤ ENNReal.ofReal (CD * ((n : ℝ) * CE)) * M := by
      refine hD'.trans ?_
      calc ENNReal.ofReal CD * ∑ l, holderNorm k α (G l) Set.univ
          ≤ ENNReal.ofReal CD * (ENNReal.ofReal ((n : ℝ) * CE) * M) :=
            mul_le_mul_right hsum_le _
        _ = ENNReal.ofReal (CD * ((n : ℝ) * CE)) * M := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hCDpos.le]
    -- `bmDefect` agrees with `-γ⁻¹ • bmPot G` on `polydisc 0 ρ'`
    have hcongr : holderNorm (k + 1) α (bmDefect χ ζ j m) (polydisc 0 ρ')
        = holderNorm (k + 1) α
            (fun z => -(((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)) * bmPot G z) (polydisc 0 ρ') :=
      holderNorm_congr_on fun z hz => by
        rw [bmDefect_apply]
        have h1 : χ z = 1 := hχone z hz
        rw [h1]
        ring
    rw [hcongr]
    -- pull out the constant
    have hscale : holderNorm (k + 1) α
        (fun z => -(((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)) * bmPot G z) (polydisc 0 ρ')
        ≤ ENNReal.ofReal ‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖
          * holderNorm (k + 1) α (fun z => bmPot G z) (polydisc 0 ρ') :=
      by simpa only [norm_neg] using
        (holderNorm_const_mul_le (isOpen_polydisc 0 ρ').uniqueDiffOn
          (-(((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))) (fun z => bmPot G z))
    refine hscale.trans ?_
    calc ENNReal.ofReal ‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖
          * holderNorm (k + 1) α (fun z => bmPot G z) (polydisc 0 ρ')
        ≤ ENNReal.ofReal ‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖
            * (ENNReal.ofReal (CD * ((n : ℝ) * CE)) * M) := mul_le_mul_right hD'' _
      _ = ENNReal.ofReal (‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖ * (CD * ((n : ℝ) * CE))) * M := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖ * CD * ((n : ℝ) * CE + 1) + 1) * M := by
            refine mul_le_mul_left ?_ M
            apply ENNReal.ofReal_le_ofReal
            have h1 : (0:ℝ) ≤ ‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖ * CD :=
              mul_nonneg (norm_nonneg _) hCDpos.le
            have h2 : (0:ℝ) ≤ (n : ℝ) * CE := mul_nonneg (Nat.cast_nonneg n) hCEpos.le
            nlinarith [h1, h2]
      _ = ENNReal.ofReal (‖((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)‖ * CD * ((n : ℝ) * CE + 1) + 1)
            * ∑ i, ∑ l, holderNorm k α (ζ i l) (polydisc 0 ρ) := by rw [hMdef]

end

end Work.NN.Core
