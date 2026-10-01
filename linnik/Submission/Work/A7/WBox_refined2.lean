import Mathlib
import Submission.Work.LinnikAreas.A7.Aref2
import Submission.Work.LinnikAreas.A7.WBox
import Submission.Work.A7.zeroMult_conj_inv
import Submission.Work.A7.F2_norm_ofReal
import Submission.Work.A7.zeroMult_conj_sq_one
import Submission.Work.A7.bfun_le_F2r

noncomputable section

namespace Work.A7

open DirichletCharacter Complex
open scoped Classical BigOperators
open Work.LinnikContract
open Work.LinnikAreas.A7

/-- The `WBox` integrand is the `boxAbs` integrand weighted by `e^{-aλ(ρ)}`. -/
private lemma wfun_eq_exp_mul_bfun {q : ℕ} [NeZero q] (K R : ℝ)
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    wfun q K R χ ρ = Real.exp (-(ac * lamOf q ρ)) * bfun q K R χ ρ := by
  simp only [wfun, bfun]
  split_ifs <;> ring

/-- The `boxAbs` integrand is non-negative. -/
private lemma bfun_nonneg' {q : ℕ} [NeZero q] (K R : ℝ)
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) : 0 ≤ bfun q K R χ ρ := by
  simp only [bfun]
  split_ifs with h
  · positivity
  · exact le_refl 0

theorem WBox_refined2 {q : ℕ} [NeZero q] {R lam c η : ℝ} {χ : DirichletCharacter ℂ q} {ρs : ℂ}
    (hbox : Work.LinnikContract.InBox q R ρs) (hboxc : Work.LinnikContract.InBox q R ((starRingEnd ℂ) ρs))
    (hχ : χ ^ 2 = 1) (hmult : Work.LinnikContract.zeroMult χ ρs = 1) (hne : (starRingEnd ℂ) ρs ≠ ρs)
    (hlam : Work.LinnikContract.lamOf q ρs = lam) (hlam0 : 0 < lam) (hlamc : lam ≤ c)
    (hsecond : ∀ ρ : ℂ, Work.LinnikContract.InBox q R ρ → Work.LinnikContract.zeroMult χ ρ ≠ 0 → ρ ≠ ρs → ρ ≠ (starRingEnd ℂ) ρs → c ≤ Work.LinnikContract.lamOf q ρ)
    (hcert : Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η)) :
    Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi lam - Work.LinnikAreas.A7.Aref2 c lam) + ((9:ℝ)/100) * Real.exp (-(Work.LinnikAreas.A7.ac * c)) * η := by
  -- the conjugate zero is simple and has the same parameter
  have hmultc : zeroMult χ ((starRingEnd ℂ) ρs) = 1 := by
    rw [zeroMult_conj_sq_one χ hχ ρs, hmult]
  have hlamc' : lamOf q ((starRingEnd ℂ) ρs) = lam := by
    have h : lamOf q ((starRingEnd ℂ) ρs) = lamOf q ρs := by simp [lamOf]
    rw [h, hlam]
  -- each of the two conjugate simple zeros contributes at most the real-axis value
  have hbfun_rho : bfun q ((3:ℝ)/10) R χ ρs
      ≤ ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 :=
    bfun_le_F2r hbox hmult hlam hlam0
  have hbfun_crho : bfun q ((3:ℝ)/10) R χ ((starRingEnd ℂ) ρs)
      ≤ ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 :=
    bfun_le_F2r hboxc hmultc hlamc' hlam0
  -- constants
  have hE12 : Real.exp (-(ac * c)) ≤ Real.exp (-(ac * lam)) := by
    rw [Real.exp_le_exp]; nlinarith [ac_pos, hlamc]
  have hE2nn : 0 ≤ Real.exp (-(ac * c)) := Real.exp_nonneg _
  have hDnn : 0 ≤ Real.exp (-(ac * lam)) - Real.exp (-(ac * c)) := sub_nonneg.mpr hE12
  have hCnn : 0 ≤ (Real.exp (-(ac * lam)) - Real.exp (-(ac * c)))
      * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 := mul_nonneg hDnn (sq_nonneg _)
  -- pointwise domination of the WBox integrand
  have hpt : ∀ ρ : ℂ, wfun q ((3:ℝ)/10) R χ ρ ≤
      Real.exp (-(ac*c)) * bfun q ((3:ℝ)/10) R χ ρ
        + (if ρ = ρs then (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
              * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 else 0)
        + (if ρ = (starRingEnd ℂ) ρs then (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
              * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 else 0) := by
    intro ρ
    rw [wfun_eq_exp_mul_bfun]
    by_cases h1 : ρ = ρs
    · rw [h1]
      rw [if_pos rfl, if_neg (fun h => hne h.symm), hlam, add_zero]
      calc Real.exp (-(ac*lam)) * bfun q ((3:ℝ)/10) R χ ρs
          = Real.exp (-(ac*c)) * bfun q ((3:ℝ)/10) R χ ρs
            + (Real.exp (-(ac*lam)) - Real.exp (-(ac*c))) * bfun q ((3:ℝ)/10) R χ ρs := by ring
        _ ≤ Real.exp (-(ac*c)) * bfun q ((3:ℝ)/10) R χ ρs
            + (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
              * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 :=
            add_le_add_right (mul_le_mul_of_nonneg_left hbfun_rho hDnn) _
    · by_cases h2 : ρ = (starRingEnd ℂ) ρs
      · rw [h2]
        rw [if_neg hne, if_pos rfl, hlamc', add_zero]
        calc Real.exp (-(ac*lam)) * bfun q ((3:ℝ)/10) R χ ((starRingEnd ℂ) ρs)
            = Real.exp (-(ac*c)) * bfun q ((3:ℝ)/10) R χ ((starRingEnd ℂ) ρs)
              + (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
                * bfun q ((3:ℝ)/10) R χ ((starRingEnd ℂ) ρs) := by ring
          _ ≤ Real.exp (-(ac*c)) * bfun q ((3:ℝ)/10) R χ ((starRingEnd ℂ) ρs)
              + (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
                * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 :=
              add_le_add_right (mul_le_mul_of_nonneg_left hbfun_crho hDnn) _
      · rw [if_neg h1, if_neg h2, add_zero, add_zero]
        by_cases hb : bfun q ((3:ℝ)/10) R χ ρ = 0
        · rw [hb, mul_zero, mul_zero]
        · have hInB : InBox q R ρ := by
            by_contra h; exact hb (by rw [bfun, if_neg h])
          have hmul : zeroMult χ ρ ≠ 0 := by
            intro hz; exact hb (by simp [bfun, hInB, hz])
          have hc_le : c ≤ lamOf q ρ := hsecond ρ hInB hmul h1 h2
          have hE : Real.exp (-(ac * lamOf q ρ)) ≤ Real.exp (-(ac * c)) := by
            rw [Real.exp_le_exp]; nlinarith [ac_pos, hc_le]
          exact mul_le_mul_of_nonneg_right hE (bfun_nonneg' _ _ _ _)
  -- algebraic form of the target
  have hkey : ((9:ℝ)/100) * (Phi lam - Aref2 c lam) + ((9:ℝ)/100) * Real.exp (-(ac * c)) * η
      = Real.exp (-(ac*c)) * (((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam + η))
        + 2 * ((Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
            * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) := by
    rw [Phi, Aref2]
    simp only [Kc, K2]
    field_simp
    ring
  by_cases hfin : Function.HasFiniteSupport (bfun q ((3:ℝ)/10) R χ)
  · have hfin' : (Function.support (bfun q ((3:ℝ)/10) R χ)).Finite := hfin
    have hsubf : Function.support (bfun q ((3:ℝ)/10) R χ)
        ⊆ ((hfin'.toFinset : Finset ℂ) : Set ℂ) :=
      fun i hi => by simpa using hfin'.mem_toFinset.mpr hi
    have hsubw : Function.support (wfun q ((3:ℝ)/10) R χ)
        ⊆ ((hfin'.toFinset : Finset ℂ) : Set ℂ) := by
      rw [support_wfun_eq_bfun]; exact hsubf
    have hW : WBox q ((3:ℝ)/10) R χ = ∑ ρ ∈ hfin'.toFinset, wfun q ((3:ℝ)/10) R χ ρ := by
      rw [WBox_eq_finsum, finsum_eq_sum_of_support_subset _ hsubw]
    have hB : boxAbs q ((3:ℝ)/10) R χ = ∑ ρ ∈ hfin'.toFinset, bfun q ((3:ℝ)/10) R χ ρ := by
      rw [show boxAbs q ((3:ℝ)/10) R χ = ∑ᶠ ρ : ℂ, bfun q ((3:ℝ)/10) R χ ρ from rfl,
          finsum_eq_sum_of_support_subset _ hsubf]
    have hsum_eq : (∑ ρ ∈ hfin'.toFinset,
          (Real.exp (-(ac*c)) * bfun q ((3:ℝ)/10) R χ ρ
            + (if ρ = ρs then (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
                  * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 else 0)
            + (if ρ = (starRingEnd ℂ) ρs then (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
                  * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 else 0)))
        = Real.exp (-(ac*c)) * (∑ ρ ∈ hfin'.toFinset, bfun q ((3:ℝ)/10) R χ ρ)
          + (if ρs ∈ hfin'.toFinset then (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
                * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 else 0)
          + (if (starRingEnd ℂ) ρs ∈ hfin'.toFinset then (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
                * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 else 0) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
          ← Finset.mul_sum]
    have hmain : WBox q ((3:ℝ)/10) R χ ≤
        Real.exp (-(ac*c)) * boxAbs q ((3:ℝ)/10) R χ
          + 2 * ((Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
              * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) := by
      rw [hW, hB]
      refine le_trans (Finset.sum_le_sum (fun ρ _ => hpt ρ)) ?_
      rw [hsum_eq]
      have h1 : (if ρs ∈ hfin'.toFinset then (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
            * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 else 0)
          ≤ (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
            * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 := by
        split_ifs with h
        · exact le_rfl
        · exact hCnn
      have h2 : (if (starRingEnd ℂ) ρs ∈ hfin'.toFinset then (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
            * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 else 0)
          ≤ (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
            * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 := by
        split_ifs with h
        · exact le_rfl
        · exact hCnn
      have hsum2 : (if ρs ∈ hfin'.toFinset then (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
              * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 else 0)
            + (if (starRingEnd ℂ) ρs ∈ hfin'.toFinset then (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
              * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 else 0)
          ≤ 2 * ((Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
              * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) := by
        calc (if ρs ∈ hfin'.toFinset then (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
                * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 else 0)
              + (if (starRingEnd ℂ) ρs ∈ hfin'.toFinset then (Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
                * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 else 0)
            ≤ (Real.exp (-(ac*lam)) - Real.exp (-(ac*c))) * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2
              + (Real.exp (-(ac*lam)) - Real.exp (-(ac*c))) * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2 :=
              add_le_add h1 h2
          _ = 2 * ((Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
                * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) := by ring
      rw [add_assoc]
      exact add_le_add_right hsum2 _
    calc WBox q ((3:ℝ)/10) R χ
        ≤ Real.exp (-(ac*c)) * boxAbs q ((3:ℝ)/10) R χ
          + 2 * ((Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
              * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) := hmain
      _ ≤ Real.exp (-(ac*c)) * (((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam + η))
          + 2 * ((Real.exp (-(ac*lam)) - Real.exp (-(ac*c)))
              * ((1 - Real.exp (-(((3:ℝ)/10) * lam)))/lam)^2) :=
            add_le_add (mul_le_mul_of_nonneg_left hcert hE2nn) (le_refl _)
      _ = ((9:ℝ)/100) * (Phi lam - Aref2 c lam) + ((9:ℝ)/100) * Real.exp (-(ac * c)) * η :=
            hkey.symm
  · have hwf : ¬ Function.HasFiniteSupport (wfun q ((3:ℝ)/10) R χ) := by
      intro h
      apply hfin
      have h' : (Function.support (wfun q ((3:ℝ)/10) R χ)).Finite := h
      have h'' : Function.HasFiniteSupport (bfun q ((3:ℝ)/10) R χ) := by
        change (Function.support (bfun q ((3:ℝ)/10) R χ)).Finite
        rwa [support_wfun_eq_bfun ((3:ℝ)/10) R χ] at h'
      exact h''
    have hboxAbs0 : boxAbs q ((3:ℝ)/10) R χ = 0 := by
      rw [show boxAbs q ((3:ℝ)/10) R χ = ∑ᶠ ρ : ℂ, bfun q ((3:ℝ)/10) R χ ρ from rfl,
          finsum_of_not_hasFiniteSupport hfin]
    have hW0 : WBox q ((3:ℝ)/10) R χ = 0 := by
      rw [WBox_eq_finsum, finsum_of_not_hasFiniteSupport hwf]
    have hBh : 0 ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam + η) := by simpa [hboxAbs0] using hcert
    rw [hW0, hkey]
    exact add_nonneg (mul_nonneg (Real.exp_nonneg _) hBh) (mul_nonneg (by norm_num) hCnn)

end Work.A7
