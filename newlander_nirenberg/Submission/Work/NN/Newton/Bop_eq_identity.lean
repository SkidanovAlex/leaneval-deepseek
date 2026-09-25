import Mathlib
import Submission.Work.NN.Newton.pushforward_setup
import Submission.Work.NN.Newton.clm_apply_decomp
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.DbarCnPertAux

noncomputable section
open scoped ContDiff
open Work.NN.Core

namespace Work.NN.Newton

variable {n : ℕ}

/-! ## Elementary helpers -/

private lemma conjCLE_eq_starRingEnd (z : ℂ) : Complex.conjCLE z = starRingEnd ℂ z := by
  rw [Complex.conjCLE_apply, starRingEnd_apply, RCLike.star_def]

private lemma conjCLE_I_mul (z : ℂ) :
    Complex.conjCLE (Complex.I * z) = -Complex.I * Complex.conjCLE z := by
  rw [conjCLE_eq_starRingEnd, conjCLE_eq_starRingEnd, map_mul]
  congr 1
  rw [starRingEnd_apply, RCLike.star_def]
  exact Complex.conj_I

private lemma I_mul_neg_I_mul (x : ℂ) : Complex.I * (-Complex.I * x) = x := by
  rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]

private lemma twoI_mul_halfI : (2 * Complex.I) * (Complex.I / 2) = (-1 : ℂ) := by
  rw [mul_div_assoc', mul_assoc, Complex.I_mul_I]; norm_num

private lemma I_mul_halfI : Complex.I * (Complex.I / 2) = -(1 / 2 : ℂ) := by
  rw [mul_div_assoc', Complex.I_mul_I]; norm_num

private lemma negI_mul_halfI : (-Complex.I) * (Complex.I / 2) = (1 / 2 : ℂ) := by
  rw [mul_div_assoc', neg_mul, Complex.I_mul_I]; norm_num

private lemma negI_smul_sub (X Y : Cn n) :
    -Complex.I • (X - (Complex.I / 2) • Y) = (-Complex.I) • X - (1 / 2 : ℂ) • Y := by
  rw [smul_sub, smul_smul, negI_mul_halfI]

private lemma neg_sum_sub (X Y : Cn n) :
    -(Complex.I • X + Y) - (-(1 / 2 : ℂ)) • Y = (-Complex.I) • X - (1 / 2 : ℂ) • Y := by
  module

private lemma smulRight_sub (c : Cn n →L[ℝ] ℂ) (x y : Cn n) :
    c.smulRight (x - y) = c.smulRight x - c.smulRight y := by
  ext u
  simp only [sub_apply, ContinuousLinearMap.smulRight_apply, smul_sub]

private lemma smulRight_smul (c : Cn n →L[ℝ] ℂ) (a : ℂ) (x : Cn n) :
    c.smulRight (a • x) = a • c.smulRight x := by
  ext u
  rw [smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
    smul_smul, smul_smul, mul_comm]

/-! ## Algebra from the almost-complexity hypothesis -/

private lemma hAC_pw (A : Cn n → Cn n →L[ℝ] Cn n) (z : Cn n)
    (hAC : ∀ u, (JstdCn n + A) z ((JstdCn n + A) z u) = -u) (u : Cn n) :
    A z (JstdCn n z u) + JstdCn n z (A z u) + A z (A z u) = 0 := by
  have h := hAC u
  simp only [Pi.add_apply, add_apply, map_add] at h
  rw [JstdCn_sq] at h
  linear_combination h

private lemma A2_comm_J_pw (A : Cn n → Cn n →L[ℝ] Cn n) (z : Cn n)
    (hAC : ∀ u, (JstdCn n + A) z ((JstdCn n + A) z u) = -u) (u : Cn n) :
    A z (A z (JstdCn n z u)) = JstdCn n z (A z (A z u)) := by
  have h1 := hAC_pw A z hAC u
  have h2 := hAC_pw A z hAC (JstdCn n z u)
  rw [JstdCn_sq, map_neg] at h2
  have h1' := congrArg (JstdCn n z) h1
  simp only [map_add, map_zero] at h1'
  rw [JstdCn_sq] at h1'
  linear_combination h2 - h1'

private lemma Alin_apply_J (A : Cn n → Cn n →L[ℝ] Cn n) (z : Cn n)
    (hAC : ∀ u, (JstdCn n + A) z ((JstdCn n + A) z u) = -u) (u : Cn n) :
    Alin A z (JstdCn n z u) = JstdCn n z (Alin A z u) := by
  have h := A2_comm_J_pw A z hAC u
  simp only [Alin, smul_apply, ContinuousLinearMap.comp_apply]
  rw [h, JstdCn_apply, JstdCn_apply, smul_smul, smul_smul, mul_comm (Complex.I / 2) Complex.I]

private lemma A_sub_Alin_antilinear (A : Cn n → Cn n →L[ℝ] Cn n) (z : Cn n)
    (hAC : ∀ u, (JstdCn n + A) z ((JstdCn n + A) z u) = -u) (u : Cn n) :
    (A z - Alin A z) (Complex.I • u) = -Complex.I • ((A z - Alin A z) u) := by
  have hAI0 : A z (Complex.I • u) + Complex.I • (A z u) + A z (A z u) = 0 := by
    have h := hAC_pw A z hAC u
    simp only [JstdCn_apply] at h
    linear_combination h
  have hAI : A z (Complex.I • u) = -(Complex.I • (A z u) + A z (A z u)) := by
    linear_combination hAI0
  have hAJ : Alin A z (Complex.I • u) = Complex.I • Alin A z u := by
    rw [show Complex.I • u = JstdCn n z u from (JstdCn_apply n z u).symm,
      Alin_apply_J A z hAC u, JstdCn_apply]
  have hAlin : ∀ w : Cn n, Alin A z w = (Complex.I / 2) • (A z (A z w)) := by
    intro w
    simp only [Alin, smul_apply, ContinuousLinearMap.comp_apply]
  have hhalf : ∀ Z : Cn n, Complex.I • ((Complex.I / 2) • Z) = -(1 / 2 : ℂ) • Z := by
    intro Z
    rw [smul_smul, I_mul_halfI]
  simp only [sub_apply, hAJ, hAlin, hhalf, hAI]
  rw [neg_sum_sub (A z u) (A z (A z u)), negI_smul_sub (A z u) (A z (A z u))]

/-! ## Antilinear maps and the conjugate-coordinate functionals -/

private lemma antilinear_eq_sum_pt (B : Cn n →L[ℝ] Cn n)
    (hB : ∀ u, B (Complex.I • u) = -Complex.I • B u) (u : Cn n) :
    B u = ∑ k : Fin n, Complex.conjCLE (u k) • B (Pi.single k (1 : ℂ)) := by
  funext j
  rw [clm_apply_decomp B u j]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  have h1 : B (Pi.single p (Complex.I : ℂ)) = -Complex.I • B (Pi.single p (1 : ℂ)) := by
    rw [← smul_single_I p, hB]
  rw [h1]
  simp only [Pi.smul_apply, smul_eq_mul, I_mul_neg_I_mul]
  ring

private lemma eq_sum_conjC_smulRight (B : Cn n →L[ℝ] Cn n)
    (hB : ∀ u, B (Complex.I • u) = -Complex.I • B u) :
    B = ∑ k : Fin n, (conjC n k).smulRight (B (Pi.single k (1 : ℂ))) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [antilinear_eq_sum_pt B hB u]
  rw [sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.smulRight_apply, conjC_apply]

/-! ## The `DvCLM`/`Jstd` commutator -/

private lemma JD_sub_DJ (v : Fin n → Cn n → ℂ) (z : Cn n) :
    (JstdCn n z).comp (DvCLM v z) - (DvCLM v z).comp (JstdCn n z)
      = (2 * Complex.I) • (∑ k : Fin n, (conjC n k).smulRight
          (fun j => Work.CR.Flat.dbarCoord k (v j) z)) := by
  apply ContinuousLinearMap.ext
  intro h
  funext j
  have hstar : ∀ w : ℂ, starRingEnd ℂ (Complex.I * w) = -Complex.I * starRingEnd ℂ w := by
    intro w
    rw [map_mul]
    congr 1
    rw [starRingEnd_apply, RCLike.star_def]
    exact Complex.conj_I
  have hL : (((JstdCn n z).comp (DvCLM v z) - (DvCLM v z).comp (JstdCn n z)) h) j
      = Complex.I * fderiv ℝ (v j) z h - fderiv ℝ (v j) z (Complex.I • h) := by
    simp only [sub_apply, ContinuousLinearMap.comp_apply, Pi.sub_apply, JstdCn_apply,
      Pi.smul_apply, smul_eq_mul, DvCLM_apply]
  have hR : (((2 * Complex.I) • (∑ k : Fin n, (conjC n k).smulRight
      (fun j => Work.CR.Flat.dbarCoord k (v j) z))) h) j
      = (2 * Complex.I) * ∑ k : Fin n,
          Complex.conjCLE (h k) * Work.CR.Flat.dbarCoord k (v j) z := by
    rw [ContinuousLinearMap.smul_apply]
    rw [Pi.smul_apply, smul_eq_mul]
    congr 1
    rw [sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousLinearMap.smulRight_apply, Pi.smul_apply, smul_eq_mul, conjC_apply]
  rw [hL, hR]
  rw [Work.NN.Core.fderiv_eq_sum_dCoord_dbarCoord (v j) z h,
      Work.NN.Core.fderiv_eq_sum_dCoord_dbarCoord (v j) z (Complex.I • h)]
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, hstar, conjCLE_eq_starRingEnd]
  ring

/-! ## `EVec` in terms of `A` -/

private lemma EVec_eq_pw (A : Cn n → Cn n →L[ℝ] Cn n) (v : Fin n → Cn n → ℂ)
    (k : Fin n) (z : Cn n) :
    EVec A v k z = (Complex.I / 2) • (A z (Pi.single k (1 : ℂ)))
      - (fun j => Work.CR.Flat.dbarCoord k (v j) z) := by
  funext j
  simp only [EVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Lcoef]
  have hfd : fderiv ℝ (fun y : Cn n => y j) z = (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ) := by
    have hcoe : (fun y : Cn n => y j) = ⇑(ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ) := by
      funext y
      exact (ContinuousLinearMap.proj_apply j y).symm
    rw [hcoe]
    exact (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ).fderiv
  rw [hfd, ContinuousLinearMap.proj_apply]

/-! ## Expansion of `Bop` -/

private lemma Bop_expand (A : Cn n → Cn n →L[ℝ] Cn n) (v : Fin n → Cn n → ℂ) (z : Cn n) :
    Bop A v z = A z
      + ((JstdCn n z).comp (DvCLM v z) - (DvCLM v z).comp (JstdCn n z))
      - (DvCLM v z).comp (A z) := by
  simp only [Bop, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  abel

/-! ## The main identity -/

theorem Bop_eq_identity {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (v : Fin n → Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n)
    (hAC : ∀ u : Work.NN.Core.Cn n,
      (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z u) = -u) :
    Work.NN.Newton.Bop A v z
      = Work.NN.Newton.Alin A z
        - ∑ k : Fin n, (Work.NN.Newton.conjC n k).smulRight (Work.NN.Newton.Alin A z (Pi.single k 1))
        - (2 * Complex.I) • (∑ k : Fin n,
            (Work.NN.Newton.conjC n k).smulRight (Work.NN.Newton.EVec A v k z))
        - (Work.NN.Newton.DvCLM v z).comp (A z) := by
  have hE : ∀ k : Fin n, EVec A v k z
      = (Complex.I / 2) • (A z (Pi.single k (1 : ℂ)))
        - (fun j => Work.CR.Flat.dbarCoord k (v j) z) := fun k => EVec_eq_pw A v k z
  have hsum : (∑ k : Fin n, (conjC n k).smulRight (fun j => Work.CR.Flat.dbarCoord k (v j) z))
      = (Complex.I / 2) • (∑ k : Fin n, (conjC n k).smulRight (A z (Pi.single k (1 : ℂ))))
        - ∑ k : Fin n, (conjC n k).smulRight (EVec A v k z) := by
    have hsm : ∀ k : Fin n, (conjC n k).smulRight (fun j => Work.CR.Flat.dbarCoord k (v j) z)
        = (Complex.I / 2) • (conjC n k).smulRight (A z (Pi.single k (1 : ℂ)))
          - (conjC n k).smulRight (EVec A v k z) := by
      intro k
      rw [← smulRight_smul, ← smulRight_sub]
      congr 1
      rw [hE k]
      abel
    rw [Finset.sum_congr rfl (fun k _ => hsm k)]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum]
  have hkey : A z - Alin A z
      = (∑ k : Fin n, (conjC n k).smulRight (A z (Pi.single k (1 : ℂ))))
        - ∑ k : Fin n, (conjC n k).smulRight (Alin A z (Pi.single k (1 : ℂ))) := by
    rw [eq_sum_conjC_smulRight (A z - Alin A z) (A_sub_Alin_antilinear A z hAC)]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← smulRight_sub]
    rfl
  have hfin : A z - (∑ k : Fin n, (conjC n k).smulRight (A z (Pi.single k (1 : ℂ))))
      = Alin A z
        - ∑ k : Fin n, (conjC n k).smulRight (Alin A z (Pi.single k (1 : ℂ))) := by
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact hkey
  have hsm2 : (2 * Complex.I) • ((Complex.I / 2) •
        (∑ k : Fin n, (conjC n k).smulRight (A z (Pi.single k (1 : ℂ)))))
      = -(∑ k : Fin n, (conjC n k).smulRight (A z (Pi.single k (1 : ℂ)))) := by
    rw [smul_smul, twoI_mul_halfI]
    exact neg_one_smul (R := ℂ)
      (∑ k : Fin n, (conjC n k).smulRight (A z (Pi.single k (1 : ℂ))))
  have hstep : A z + (-(∑ k : Fin n, (conjC n k).smulRight (A z (Pi.single k (1 : ℂ))))
        - (2 * Complex.I) • (∑ k : Fin n, (conjC n k).smulRight (EVec A v k z)))
        - (DvCLM v z).comp (A z)
      = (A z - (∑ k : Fin n, (conjC n k).smulRight (A z (Pi.single k (1 : ℂ)))))
        - (2 * Complex.I) • (∑ k : Fin n, (conjC n k).smulRight (EVec A v k z))
        - (DvCLM v z).comp (A z) := by abel
  rw [Bop_expand, JD_sub_DJ v z, hsum, smul_sub, hsm2, hstep, hfin]

end Work.NN.Newton
