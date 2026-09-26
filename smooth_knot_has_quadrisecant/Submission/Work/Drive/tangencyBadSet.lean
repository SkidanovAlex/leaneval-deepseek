import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.knotPerturbDefs
import Submission.Work.Drive.tangencyRank

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- The coefficient space of the perturbation family. -/
abbrev Coeff := PiLp 2 (fun _ : Fin 9 => Space)

/-- The configuration space `(lam, mu, a, b, m)`. -/
abbrev Cfg := EuclideanSpace ℝ (Fin 5)

/-- The target space `Space × Space`, seen as `ℝ⁶`. -/
abbrev Tgt := EuclideanSpace ℝ (Fin 6)

/-- Identification of the coefficient space with the sup-normed `Fin 9 → Space`. -/
def eCoeff : Coeff ≃L[ℝ] (Fin 9 → Space) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 9 => Space)

/-- Identification of `Space × Space` with `ℝ⁶`. -/
def eTgt : (Space × Space) ≃L[ℝ] Tgt :=
  (LinearEquiv.ofFinrankEq (Space × Space) (EuclideanSpace ℝ (Fin 6))
    (by simp [Module.finrank_prod])).toContinuousLinearEquiv

/-- The first component of `eTgt`, as a continuous linear map of `Space`. -/
def eT1 : Space →L[ℝ] Tgt := eTgt.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ Space Space)

/-- The second component of `eTgt`, as a continuous linear map of `Space`. -/
def eT2 : Space →L[ℝ] Tgt := eTgt.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ Space Space)

lemma eT1_add_eT2 (u v : Space) : eT1 u + eT2 v = eTgt (u, v) := by
  have h1 : eT1 u = eTgt (u, 0) := rfl
  have h2 : eT2 v = eTgt (0, v) := rfl
  rw [h1, h2, ← map_add]
  simp

lemma eTgt_eq_zero_iff {u v : Space} : eTgt (u, v) = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have h2 : (u, v) = 0 := eTgt.injective (by simpa using h)
    exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
  · rintro ⟨rfl, rfl⟩; simp

/-! ## The configuration coordinates -/

/-- The `i`-th coordinate of the configuration, as a continuous linear map. -/
def cfgLin (i : Fin 5) : Cfg →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 5 => ℝ)).toContinuousLinearMap)

/-- The multiplier on the first chord. -/
def cfgLam (w : Cfg) : ℝ := w.ofLp 0
/-- The multiplier on the second chord. -/
def cfgMu (w : Cfg) : ℝ := w.ofLp 1
/-- The first parameter. -/
def cfgA (w : Cfg) : ℝ := w.ofLp 2
/-- The second parameter. -/
def cfgB (w : Cfg) : ℝ := w.ofLp 3
/-- The third parameter. -/
def cfgM (w : Cfg) : ℝ := w.ofLp 4

lemma cfgLam_eq : cfgLam = ⇑(cfgLin 0) := by funext w; rfl
lemma cfgMu_eq : cfgMu = ⇑(cfgLin 1) := by funext w; rfl
lemma cfgA_eq : cfgA = ⇑(cfgLin 2) := by funext w; rfl
lemma cfgB_eq : cfgB = ⇑(cfgLin 3) := by funext w; rfl
lemma cfgM_eq : cfgM = ⇑(cfgLin 4) := by funext w; rfl

theorem contDiff_cfgLam : ContDiff ℝ ⊤ cfgLam := cfgLam_eq ▸ (cfgLin 0).contDiff
theorem contDiff_cfgMu : ContDiff ℝ ⊤ cfgMu := cfgMu_eq ▸ (cfgLin 1).contDiff
theorem contDiff_cfgA : ContDiff ℝ ⊤ cfgA := cfgA_eq ▸ (cfgLin 2).contDiff
theorem contDiff_cfgB : ContDiff ℝ ⊤ cfgB := cfgB_eq ▸ (cfgLin 3).contDiff
theorem contDiff_cfgM : ContDiff ℝ ⊤ cfgM := cfgM_eq ▸ (cfgLin 4).contDiff

/-! ## The perturbed curve and the joint smoothness -/

/-- The perturbed curve, indexed by the coefficient space. -/
def pertV (r : ℝ → Space) (c : Coeff) : ℝ → Space := perturb r (eCoeff c)

/-- The velocity of the perturbed curve. -/
def pertVelV (r : ℝ → Space) (c : Coeff) : ℝ → Space := perturbVel r (eCoeff c)

/-- The `j`-th coefficient projection. -/
def coeffProj (j : Fin 9) : Coeff →L[ℝ] Space :=
  (ContinuousLinearMap.proj j).comp (eCoeff : Coeff →L[ℝ] (Fin 9 → Space))

@[simp] lemma coeffProj_apply (j : Fin 9) (c : Coeff) : coeffProj j c = (eCoeff c) j := by
  simp [coeffProj, ContinuousLinearMap.proj_apply]

lemma periodic_deriv' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {c : ℝ} (h : Function.Periodic f c) :
    Function.Periodic (deriv f) c := by
  intro x
  have hx : deriv (fun y : ℝ => f (y + c)) x = deriv f x := by
    rw [show (fun y : ℝ => f (y + c)) = f from funext h]
  rwa [deriv_comp_add_const f c x] at hx

theorem periodic_trigBasisD (j : Fin 9) : Function.Periodic (trigBasisD j) (2 * Real.pi) := by
  rw [← deriv_trigBasis j]
  exact periodic_deriv' (f := trigBasis j) (c := 2 * Real.pi) (periodic_trigBasis j)

theorem contDiff_trigBasisD (j : Fin 9) : ContDiff ℝ ⊤ (trigBasisD j) := by
  rw [← deriv_trigBasis j]
  exact ContDiff.deriv' (n := ⊤) (by simpa using contDiff_trigBasis j)

theorem contDiff_pertV_joint {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) :
    ContDiff ℝ ⊤ (fun z : Coeff × ℝ => pertV r z.1 z.2) := by
  have hfun : (fun z : Coeff × ℝ => pertV r z.1 z.2)
      = (fun z : Coeff × ℝ => r z.2 + ∑ j : Fin 9, (trigBasis j z.2) • coeffProj j z.1) := by
    funext z
    simp [pertV, perturb, perturbCorr, coeffProj_apply]
  rw [hfun]
  refine ContDiff.add (hr.comp contDiff_snd) ?_
  refine ContDiff.sum fun j _ => ?_
  exact ContDiff.smul ((contDiff_trigBasis j).comp contDiff_snd)
    (((coeffProj j).contDiff).comp contDiff_fst)

theorem contDiff_pertVelV_joint {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) :
    ContDiff ℝ ⊤ (fun z : Coeff × ℝ => pertVelV r z.1 z.2) := by
  have hfun : (fun z : Coeff × ℝ => pertVelV r z.1 z.2)
      = (fun z : Coeff × ℝ => velocity r z.2 + ∑ j : Fin 9, (trigBasisD j z.2) • coeffProj j z.1) := by
    funext z
    simp [pertVelV, perturbVel, perturbVelCorr, coeffProj_apply]
  rw [hfun]
  have hvel : ContDiff ℝ ⊤ (fun z : Coeff × ℝ => velocity r z.2) := by
    have h1 : ContDiff ℝ ⊤ (deriv r) := hr.deriv' (n := ⊤)
    have h2 : ContDiff ℝ ⊤ (fun z : Coeff × ℝ => deriv r z.2) := h1.comp contDiff_snd
    exact h2
  refine ContDiff.add hvel ?_
  refine ContDiff.sum fun j _ => ?_
  exact ContDiff.smul ((contDiff_trigBasisD j).comp contDiff_snd)
    (((coeffProj j).contDiff).comp contDiff_fst)

/-! ## The bad map and its smoothness -/

/-- **The bad-configuration map.**  `X` selects the tangency slot. -/
def PsiGen (r : ℝ → Space) (X : Cfg → ℝ) (z : Coeff × Cfg) : Tgt :=
  eT1 ((pertVelV r z.1 (X z.2)) -
      (cfgLam z.2) • (pertV r z.1 (cfgA z.2) - pertV r z.1 (cfgB z.2)))
  + eT2 ((pertVelV r z.1 (X z.2)) -
      (cfgMu z.2) • (pertV r z.1 (cfgA z.2) - pertV r z.1 (cfgM z.2)))

theorem contDiff_PsiGen {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) {X : Cfg → ℝ}
    (hX : ContDiff ℝ ⊤ X) : ContDiff ℝ 1 (PsiGen r X) := by
  have h1 : ContDiff ℝ ⊤ (fun z : Coeff × Cfg => pertVelV r z.1 (X z.2)) :=
    (contDiff_pertVelV_joint hr).comp (contDiff_fst.prodMk (hX.comp contDiff_snd))
  have h2 : ContDiff ℝ ⊤
      (fun z : Coeff × Cfg => pertV r z.1 (cfgA z.2) - pertV r z.1 (cfgB z.2)) :=
    ((contDiff_pertV_joint hr).comp (contDiff_fst.prodMk (contDiff_cfgA.comp contDiff_snd))).sub
      ((contDiff_pertV_joint hr).comp (contDiff_fst.prodMk (contDiff_cfgB.comp contDiff_snd)))
  have h3 : ContDiff ℝ ⊤
      (fun z : Coeff × Cfg => pertV r z.1 (cfgA z.2) - pertV r z.1 (cfgM z.2)) :=
    ((contDiff_pertV_joint hr).comp (contDiff_fst.prodMk (contDiff_cfgA.comp contDiff_snd))).sub
      ((contDiff_pertV_joint hr).comp (contDiff_fst.prodMk (contDiff_cfgM.comp contDiff_snd)))
  have h4 : ContDiff ℝ ⊤ (fun z : Coeff × Cfg => cfgLam z.2) :=
    contDiff_cfgLam.comp contDiff_snd
  have h5 : ContDiff ℝ ⊤ (fun z : Coeff × Cfg => cfgMu z.2) :=
    contDiff_cfgMu.comp contDiff_snd
  have h6 : ContDiff ℝ ⊤ (fun z : Coeff × Cfg => PsiGen r X z) := by
    simp only [PsiGen]
    exact (eT1.contDiff.comp (h1.sub (h4.smul h2))).add (eT2.contDiff.comp (h1.sub (h5.smul h3)))
  exact h6.of_le le_top

/-! ## The partial derivative in the coefficient variable -/

/-- A finite linear combination of coefficient projections. -/
def linSum (D : Fin 9 → ℝ) : Coeff →L[ℝ] Space :=
  ∑ j : Fin 9, D j • coeffProj j

lemma linSum_apply (D : Fin 9 → ℝ) (c : Coeff) :
    linSum D c = ∑ j : Fin 9, D j • coeffProj j c := by
  simp only [linSum, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]

/-- The coefficientwise tangency functional (first chord). -/
def linCoeff (x a b lam : ℝ) : Coeff →L[ℝ] Space :=
  linSum (fun j => ellCoeff x a b lam j)

/-- The coefficientwise tangency functional (second chord). -/
def linCoeff' (x a m mu : ℝ) : Coeff →L[ℝ] Space :=
  linSum (fun j => ellCoeff' x a m mu j)

lemma linSum_sub (D E : Fin 9 → ℝ) :
    linSum D - linSum E = linSum (fun j => D j - E j) := by
  apply ContinuousLinearMap.ext
  intro c
  rw [ContinuousLinearMap.sub_apply, linSum_apply, linSum_apply, linSum_apply,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [sub_smul]

theorem hasFDerivAt_pertV_slice (r : ℝ → Space) (a : ℝ) (c₀ : Coeff) :
    HasFDerivAt (fun c : Coeff => pertV r c a) (linSum (fun j => trigBasis j a)) c₀ := by
  have h := (hasFDerivAt_const (r a) c₀).add
    ((linSum (fun j => trigBasis j a)).hasFDerivAt (x := c₀))
  rw [zero_add] at h
  refine h.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun c => by
    simp [pertV, perturb, perturbCorr, linSum_apply, coeffProj_apply]

theorem hasFDerivAt_pertVelV_slice (r : ℝ → Space) (x : ℝ) (c₀ : Coeff) :
    HasFDerivAt (fun c : Coeff => pertVelV r c x) (linSum (fun j => trigBasisD j x)) c₀ := by
  have h := (hasFDerivAt_const (velocity r x) c₀).add
    ((linSum (fun j => trigBasisD j x)).hasFDerivAt (x := c₀))
  rw [zero_add] at h
  refine h.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun c => by
    simp [pertVelV, perturbVel, perturbVelCorr, linSum_apply, coeffProj_apply]

theorem hasFDerivAt_pertV_sub_slice (r : ℝ → Space) (a b : ℝ) (c₀ : Coeff) :
    HasFDerivAt (fun c : Coeff => pertV r c a - pertV r c b)
      (linSum (fun j => trigBasis j a - trigBasis j b)) c₀ := by
  have h := (hasFDerivAt_pertV_slice r a c₀).sub (hasFDerivAt_pertV_slice r b c₀)
  rw [linSum_sub (fun j => trigBasis j a) (fun j => trigBasis j b)] at h
  exact h

/-! ## The partial derivative of the bad map in the coefficient variable -/

lemma linSum_smul_sub (D E : Fin 9 → ℝ) (lam : ℝ) :
    linSum D - lam • linSum E = linSum (fun j => D j - lam * E j) := by
  apply ContinuousLinearMap.ext
  intro c
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, linSum_apply, linSum_apply,
    linSum_apply, Finset.smul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [sub_smul, mul_smul]

/-- The partial derivative of `PsiGen` in the coefficient variable. -/
def PsiDeriv (X : Cfg → ℝ) (w : Cfg) : Coeff →L[ℝ] Tgt :=
  eT1.comp (linCoeff (X w) (cfgA w) (cfgB w) (cfgLam w))
    + eT2.comp (linCoeff' (X w) (cfgA w) (cfgM w) (cfgMu w))

lemma PsiDeriv_apply (X : Cfg → ℝ) (w : Cfg) (c : Coeff) :
    PsiDeriv X w c = eTgt ((linCoeff (X w) (cfgA w) (cfgB w) (cfgLam w)) c,
      (linCoeff' (X w) (cfgA w) (cfgM w) (cfgMu w)) c) := by
  rw [PsiDeriv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  exact eT1_add_eT2 _ _

theorem hasFDerivAt_PsiGen_slice (r : ℝ → Space) (X : Cfg → ℝ) (c₀ : Coeff) (w : Cfg) :
    HasFDerivAt (fun c : Coeff => PsiGen r X (c, w)) (PsiDeriv X w) c₀ := by
  have h1 : HasFDerivAt (fun c : Coeff => pertVelV r c (X w))
      (linSum (fun j => trigBasisD j (X w))) c₀ := hasFDerivAt_pertVelV_slice r (X w) c₀
  have h2 : HasFDerivAt (fun c : Coeff => pertV r c (cfgA w) - pertV r c (cfgB w))
      (linSum (fun j => trigBasis j (cfgA w) - trigBasis j (cfgB w))) c₀ :=
    hasFDerivAt_pertV_sub_slice r (cfgA w) (cfgB w) c₀
  have h3 : HasFDerivAt (fun c : Coeff => pertV r c (cfgA w) - pertV r c (cfgM w))
      (linSum (fun j => trigBasis j (cfgA w) - trigBasis j (cfgM w))) c₀ :=
    hasFDerivAt_pertV_sub_slice r (cfgA w) (cfgM w) c₀
  have hA : HasFDerivAt (fun c : Coeff => pertVelV r c (X w)
      - (cfgLam w) • (pertV r c (cfgA w) - pertV r c (cfgB w)))
      (linCoeff (X w) (cfgA w) (cfgB w) (cfgLam w)) c₀ := by
    have h := h1.sub (h2.const_smul (cfgLam w))
    have he : linSum (fun j => trigBasisD j (X w))
        - (cfgLam w) • linSum (fun j => trigBasis j (cfgA w) - trigBasis j (cfgB w))
        = linCoeff (X w) (cfgA w) (cfgB w) (cfgLam w) :=
      linSum_smul_sub (fun j => trigBasisD j (X w))
        (fun j => trigBasis j (cfgA w) - trigBasis j (cfgB w)) (cfgLam w)
    rw [he] at h
    exact h
  have hB : HasFDerivAt (fun c : Coeff => pertVelV r c (X w)
      - (cfgMu w) • (pertV r c (cfgA w) - pertV r c (cfgM w)))
      (linCoeff' (X w) (cfgA w) (cfgM w) (cfgMu w)) c₀ := by
    have h := h1.sub (h3.const_smul (cfgMu w))
    have he : linSum (fun j => trigBasisD j (X w))
        - (cfgMu w) • linSum (fun j => trigBasis j (cfgA w) - trigBasis j (cfgM w))
        = linCoeff' (X w) (cfgA w) (cfgM w) (cfgMu w) :=
      linSum_smul_sub (fun j => trigBasisD j (X w))
        (fun j => trigBasis j (cfgA w) - trigBasis j (cfgM w)) (cfgMu w)
    rw [he] at h
    exact h
  have hA1 : HasFDerivAt (fun c : Coeff => eT1 (pertVelV r c (X w)
      - (cfgLam w) • (pertV r c (cfgA w) - pertV r c (cfgB w))))
      (eT1.comp (linCoeff (X w) (cfgA w) (cfgB w) (cfgLam w))) c₀ :=
    HasFDerivAt.comp c₀ eT1.hasFDerivAt hA
  have hB1 : HasFDerivAt (fun c : Coeff => eT2 (pertVelV r c (X w)
      - (cfgMu w) • (pertV r c (cfgA w) - pertV r c (cfgM w))))
      (eT2.comp (linCoeff' (X w) (cfgA w) (cfgM w) (cfgMu w))) c₀ :=
    HasFDerivAt.comp c₀ eT2.hasFDerivAt hB
  have hsum : HasFDerivAt (fun c : Coeff => eT1 (pertVelV r c (X w)
      - (cfgLam w) • (pertV r c (cfgA w) - pertV r c (cfgB w)))
      + eT2 (pertVelV r c (X w) - (cfgMu w) • (pertV r c (cfgA w) - pertV r c (cfgM w))))
      (PsiDeriv X w) c₀ := hA1.add hB1
  refine hsum.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun c => by simp [PsiGen]

/-! ## Reduction of parameters to `[0, 2π)` and the circular separation -/

/-- Reduction of a parameter to the representative in `[0, 2π)`. -/
def red (t : ℝ) : ℝ := if t = 2 * Real.pi then 0 else t

/-- The circular separation of two parameters. -/
def csep (s t : ℝ) : ℝ := min |s - t| (2 * Real.pi - |s - t|)

lemma red_mem_Ico {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * Real.pi)) :
    red t ∈ Set.Ico 0 (2 * Real.pi) := by
  by_cases h : t = 2 * Real.pi
  · rw [red, if_pos h]; exact ⟨le_rfl, by positivity⟩
  · rw [red, if_neg h]; exact ⟨ht.1, lt_of_le_of_ne ht.2 h⟩

lemma trigBasis_red (j : Fin 9) {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * Real.pi)) :
    trigBasis j (red t) = trigBasis j t := by
  by_cases h : t = 2 * Real.pi
  · rw [red, if_pos h, h]
    simpa using ((periodic_trigBasis j) 0).symm
  · rw [red, if_neg h]

lemma trigBasisD_red (j : Fin 9) {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * Real.pi)) :
    trigBasisD j (red t) = trigBasisD j t := by
  by_cases h : t = 2 * Real.pi
  · rw [red, if_pos h, h]
    simpa using ((periodic_trigBasisD j) 0).symm
  · rw [red, if_neg h]

lemma sub_eq_zero_or_two_pi {s t : ℝ} (hs : s ∈ Set.Icc 0 (2 * Real.pi))
    (ht : t ∈ Set.Icc 0 (2 * Real.pi)) (h : red s = red t) :
    s - t = 0 ∨ s - t = 2 * Real.pi ∨ s - t = -(2 * Real.pi) := by
  by_cases hs2 : s = 2 * Real.pi
  · have h1 : red s = 0 := by rw [red, if_pos hs2]
    by_cases ht2 : t = 2 * Real.pi
    · left; rw [hs2, ht2]; ring
    · have h2 : red t = t := by rw [red, if_neg ht2]
      have h3 : t = 0 := by rw [h1, h2] at h; exact h.symm
      right; left; rw [hs2, h3]; ring
  · have h1 : red s = s := by rw [red, if_neg hs2]
    by_cases ht2 : t = 2 * Real.pi
    · have h2 : red t = 0 := by rw [red, if_pos ht2]
      have h3 : s = 0 := by rw [h1, h2] at h; exact h
      right; right; rw [h3, ht2]; ring
    · have h2 : red t = t := by rw [red, if_neg ht2]
      left; rw [h1, h2] at h; exact sub_eq_zero.mpr h

lemma csep_eq_zero_of_red_eq {s t : ℝ} (hs : s ∈ Set.Icc 0 (2 * Real.pi))
    (ht : t ∈ Set.Icc 0 (2 * Real.pi)) (h : red s = red t) : csep s t = 0 := by
  rcases sub_eq_zero_or_two_pi hs ht h with h' | h' | h'
  · rw [csep, h', abs_zero, sub_zero, min_eq_left]
    positivity
  · rw [csep, h', abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi), sub_self, min_eq_right]
    positivity
  · rw [csep, h', abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi), sub_self,
      min_eq_right]
    positivity

lemma red_ne_of_csep_pos {s t : ℝ} (hs : s ∈ Set.Icc 0 (2 * Real.pi))
    (ht : t ∈ Set.Icc 0 (2 * Real.pi)) (h : 0 < csep s t) : red s ≠ red t :=
  fun hc => absurd (csep_eq_zero_of_red_eq hs ht hc) (ne_of_gt h)

/-! ## Surjectivity of the derivative -/

theorem surjective_linCoeff_pair {x a b m lam mu : ℝ}
    (ha : a ∈ Set.Ico 0 (2 * Real.pi)) (hb : b ∈ Set.Ico 0 (2 * Real.pi))
    (hm : m ∈ Set.Ico 0 (2 * Real.pi)) (hab : a ≠ b) (ham : a ≠ m) (hbm : b ≠ m)
    (hx : x = a ∨ x = b ∨ x = m) (hlam : lam ≠ 0) (hmu : mu ≠ 0) :
    Function.Surjective (fun c : Coeff =>
      ((linCoeff x a b lam) c, (linCoeff' x a m mu) c)) := by
  intro q
  obtain ⟨c, hc⟩ := surjective_tangency x a b m ha hb hm hab ham hbm hx lam mu hlam hmu q
  refine ⟨eCoeff.symm c, ?_⟩
  have h1 : linCoeff x a b lam (eCoeff.symm c) = ∑ j, ellCoeff x a b lam j • c j := by
    simp only [linCoeff, linSum_apply, coeffProj_apply, ContinuousLinearEquiv.apply_symm_apply]
  have h2 : linCoeff' x a m mu (eCoeff.symm c) = ∑ j, ellCoeff' x a m mu j • c j := by
    simp only [linCoeff', linSum_apply, coeffProj_apply, ContinuousLinearEquiv.apply_symm_apply]
  refine Prod.ext ?_ ?_
  · show (linCoeff x a b lam) (eCoeff.symm c) = q.1
    rw [h1]; exact congrArg Prod.fst hc
  · show (linCoeff' x a m mu) (eCoeff.symm c) = q.2
    rw [h2]; exact congrArg Prod.snd hc

theorem linCoeff_red (x a b lam : ℝ) (hx : x ∈ Set.Icc 0 (2 * Real.pi))
    (ha : a ∈ Set.Icc 0 (2 * Real.pi)) (hb : b ∈ Set.Icc 0 (2 * Real.pi)) :
    linCoeff x a b lam = linCoeff (red x) (red a) (red b) lam := by
  apply ContinuousLinearMap.ext
  intro c
  rw [linCoeff, linCoeff, linSum_apply, linSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [coeffProj_apply]
  rw [ellCoeff, ellCoeff, trigBasisD_red j hx, trigBasis_red j ha, trigBasis_red j hb]

theorem linCoeff'_red (x a m mu : ℝ) (hx : x ∈ Set.Icc 0 (2 * Real.pi))
    (ha : a ∈ Set.Icc 0 (2 * Real.pi)) (hm : m ∈ Set.Icc 0 (2 * Real.pi)) :
    linCoeff' x a m mu = linCoeff' (red x) (red a) (red m) mu := by
  apply ContinuousLinearMap.ext
  intro c
  rw [linCoeff', linCoeff', linSum_apply, linSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [coeffProj_apply]
  rw [ellCoeff', ellCoeff', trigBasisD_red j hx, trigBasis_red j ha, trigBasis_red j hm]

theorem surjective_PsiDeriv {X : Cfg → ℝ} {w : Cfg}
    (hX : X = cfgA ∨ X = cfgB ∨ X = cfgM)
    (ha : cfgA w ∈ Set.Icc 0 (2 * Real.pi)) (hb : cfgB w ∈ Set.Icc 0 (2 * Real.pi))
    (hm : cfgM w ∈ Set.Icc 0 (2 * Real.pi))
    (hab : 0 < csep (cfgA w) (cfgB w)) (ham : 0 < csep (cfgA w) (cfgM w))
    (hbm : 0 < csep (cfgB w) (cfgM w))
    (hlam : cfgLam w ≠ 0) (hmu : cfgMu w ≠ 0) :
    Function.Surjective (PsiDeriv X w) := by
  have hxw : X w ∈ Set.Icc 0 (2 * Real.pi) := by
    rcases hX with h | h | h
    · rw [h]; exact ha
    · rw [h]; exact hb
    · rw [h]; exact hm
  have hx : red (X w) = red (cfgA w) ∨ red (X w) = red (cfgB w) ∨
      red (X w) = red (cfgM w) := by
    rcases hX with h | h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (by rw [h]))
  have hAeq := linCoeff_red (X w) (cfgA w) (cfgB w) (cfgLam w) hxw ha hb
  have hBeq := linCoeff'_red (X w) (cfgA w) (cfgM w) (cfgMu w) hxw ha hm
  intro q
  obtain ⟨c, hc⟩ := surjective_linCoeff_pair (x := red (X w)) (a := red (cfgA w))
    (b := red (cfgB w)) (m := red (cfgM w)) (lam := cfgLam w) (mu := cfgMu w)
    (red_mem_Ico ha) (red_mem_Ico hb) (red_mem_Ico hm)
    (red_ne_of_csep_pos ha hb hab) (red_ne_of_csep_pos ha hm ham)
    (red_ne_of_csep_pos hb hm hbm) hx hlam hmu (eTgt.symm q)
  refine ⟨c, ?_⟩
  rw [PsiDeriv_apply]
  have h1 : (linCoeff (X w) (cfgA w) (cfgB w) (cfgLam w)) c
      = (linCoeff (red (X w)) (red (cfgA w)) (red (cfgB w)) (cfgLam w)) c := by
    rw [hAeq]
  have h2 : (linCoeff' (X w) (cfgA w) (cfgM w) (cfgMu w)) c
      = (linCoeff' (red (X w)) (red (cfgA w)) (red (cfgM w)) (cfgMu w)) c := by
    rw [hBeq]
  rw [h1, h2]
  have hc' : ((linCoeff (red (X w)) (red (cfgA w)) (red (cfgB w)) (cfgLam w)) c,
      (linCoeff' (red (X w)) (red (cfgA w)) (red (cfgM w)) (cfgMu w)) c) = eTgt.symm q := hc
  rw [hc']
  simp [ContinuousLinearEquiv.apply_symm_apply]

/-! ## Compact configuration families -/

/-- The configuration space identified with `ℝ⁵`. -/
def cfgHomeo : Cfg ≃ₜ (Fin 5 → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 5 => ℝ)).toHomeomorph

lemma cfgHomeo_apply (w : Cfg) (i : Fin 5) : cfgHomeo w i = cfgLin i w := rfl

lemma cfgLam_homeo (w : Cfg) : cfgLam w = cfgHomeo w 0 := rfl
lemma cfgMu_homeo (w : Cfg) : cfgMu w = cfgHomeo w 1 := rfl
lemma cfgA_homeo (w : Cfg) : cfgA w = cfgHomeo w 2 := rfl
lemma cfgB_homeo (w : Cfg) : cfgB w = cfgHomeo w 3 := rfl
lemma cfgM_homeo (w : Cfg) : cfgM w = cfgHomeo w 4 := rfl

/-- The compact ball of coefficients. -/
def Kv (r₀ : ℝ) : Set Coeff := Metric.closedBall 0 r₀

theorem isCompact_Kv (r₀ : ℝ) : IsCompact (Kv r₀) := isCompact_closedBall 0 r₀

lemma continuous_csep : Continuous (fun p : ℝ × ℝ => csep p.1 p.2) := by
  unfold csep
  exact (continuous_fst.sub continuous_snd).abs.min
    (continuous_const.sub ((continuous_fst.sub continuous_snd).abs))

/-- The compact set of separated triples of parameters in `[0, 2π]³`. -/
def tripleSet (k : ℕ) : Set (ℝ × ℝ × ℝ) :=
  {q | q.1 ∈ Set.Icc 0 (2 * Real.pi) ∧ q.2.1 ∈ Set.Icc 0 (2 * Real.pi) ∧
       q.2.2 ∈ Set.Icc 0 (2 * Real.pi) ∧
       (1:ℝ)/(k+1) ≤ csep q.1 q.2.1 ∧ (1:ℝ)/(k+1) ≤ csep q.1 q.2.2 ∧
       (1:ℝ)/(k+1) ≤ csep q.2.1 q.2.2}

theorem isCompact_tripleSet (k : ℕ) : IsCompact (tripleSet k) := by
  have hA : IsClosed {q : ℝ × ℝ × ℝ | (1:ℝ)/(k+1) ≤ csep q.1 q.2.1} := by
    have hc : Continuous (fun q : ℝ × ℝ × ℝ => csep q.1 q.2.1) :=
      continuous_csep.comp (continuous_fst.prodMk continuous_snd.fst)
    exact isClosed_Ici.preimage hc
  have hB : IsClosed {q : ℝ × ℝ × ℝ | (1:ℝ)/(k+1) ≤ csep q.1 q.2.2} := by
    have hc : Continuous (fun q : ℝ × ℝ × ℝ => csep q.1 q.2.2) :=
      continuous_csep.comp (continuous_fst.prodMk continuous_snd.snd)
    exact isClosed_Ici.preimage hc
  have hC : IsClosed {q : ℝ × ℝ × ℝ | (1:ℝ)/(k+1) ≤ csep q.2.1 q.2.2} := by
    have hc : Continuous (fun q : ℝ × ℝ × ℝ => csep q.2.1 q.2.2) :=
      continuous_csep.comp (continuous_snd.fst.prodMk continuous_snd.snd)
    exact isClosed_Ici.preimage hc
  have heq : tripleSet k = {q : ℝ × ℝ × ℝ | (1:ℝ)/(k+1) ≤ csep q.1 q.2.1} ∩
      {q : ℝ × ℝ × ℝ | (1:ℝ)/(k+1) ≤ csep q.1 q.2.2} ∩
      {q : ℝ × ℝ × ℝ | (1:ℝ)/(k+1) ≤ csep q.2.1 q.2.2} ∩
      (Set.Icc (0:ℝ) (2*Real.pi) ×ˢ
        (Set.Icc (0:ℝ) (2*Real.pi) ×ˢ Set.Icc (0:ℝ) (2*Real.pi))) := by
    ext q
    simp only [tripleSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc]
    tauto
  have hI : IsCompact (Set.Icc (0:ℝ) (2*Real.pi)) := isCompact_Icc
  have hclosed : IsClosed (tripleSet k) := by
    rw [heq]
    exact ((hA.inter hB).inter hC).inter (isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc))
  refine (hI.prod (hI.prod hI)).of_isClosed_subset hclosed ?_
  intro q hq
  exact ⟨hq.1, hq.2.1, hq.2.2.1⟩

lemma tripleSet_mem_witness (k : ℕ) :
    (0, (2 * Real.pi / 3, 4 * Real.pi / 3)) ∈ tripleSet k := by
  have hk : (1:ℝ)/(k+1) ≤ 1 := by
    rw [div_le_one (by positivity : (0:ℝ) < (k:ℝ) + 1)]
    have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have hπ : (1:ℝ) ≤ 2 * Real.pi / 3 := by linarith [Real.pi_gt_three]
  simp only [tripleSet, csep, Set.mem_setOf_eq, Set.mem_Icc]
  refine ⟨⟨le_rfl, by positivity⟩, ⟨by positivity, by linarith [Real.pi_pos]⟩,
    ⟨by positivity, by linarith [Real.pi_pos]⟩, ?_, ?_, ?_⟩
  · rw [zero_sub, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi / 3),
      min_eq_left (by linarith [Real.pi_pos])]
    linarith
  · rw [zero_sub, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 4 * Real.pi / 3),
      min_eq_right (by linarith [Real.pi_pos])]
    linarith
  · rw [show 2 * Real.pi / 3 - 4 * Real.pi / 3 = -(2 * Real.pi / 3) by ring, abs_neg,
      abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi / 3),
      min_eq_left (by linarith [Real.pi_pos])]
    linarith

lemma pertV_red {r : ℝ → Space} {c : Coeff}
    (hper : Function.Periodic (pertV r c) (2 * Real.pi)) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (2 * Real.pi)) : pertV r c (red t) = pertV r c t := by
  by_cases h : t = 2 * Real.pi
  · rw [red, if_pos h, h]
    simpa using (hper 0).symm
  · rw [red, if_neg h]

theorem exists_delta {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) {r₀ : ℝ} (hr₀ : 0 ≤ r₀)
    (hS : ∀ c ∈ Kv r₀, IsSmoothKnot (pertV r c))
    (hper : ∀ c : Coeff, Function.Periodic (pertV r c) (2 * Real.pi)) (k : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c ∈ Kv r₀, ∀ a b m : ℝ, (a, (b, m)) ∈ tripleSet k →
      δ ≤ ‖pertV r c a - pertV r c b‖ ∧ δ ≤ ‖pertV r c a - pertV r c m‖ := by
  have hjoint : Continuous (fun z : Coeff × ℝ => pertV r z.1 z.2) :=
    (contDiff_pertV_joint hr).continuous
  set φ₁ : Coeff × (ℝ × ℝ × ℝ) → ℝ :=
    fun q => ‖pertV r q.1 q.2.1 - pertV r q.1 q.2.2.1‖ with hφ₁
  set φ₂ : Coeff × (ℝ × ℝ × ℝ) → ℝ :=
    fun q => ‖pertV r q.1 q.2.1 - pertV r q.1 q.2.2.2‖ with hφ₂
  have hcont₁ : Continuous φ₁ := by
    rw [hφ₁]
    exact ((hjoint.comp (continuous_fst.prodMk continuous_snd.fst)).sub
      (hjoint.comp (continuous_fst.prodMk continuous_snd.snd.fst))).norm
  have hcont₂ : Continuous φ₂ := by
    rw [hφ₂]
    exact ((hjoint.comp (continuous_fst.prodMk continuous_snd.fst)).sub
      (hjoint.comp (continuous_fst.prodMk continuous_snd.snd.snd))).norm
  have hpos1 : ∀ q ∈ Kv r₀ ×ˢ tripleSet k, pertV r q.1 q.2.1 ≠ pertV r q.1 q.2.2.1 := by
    intro q hq hcon
    obtain ⟨hc, ha, hb, -, hab, -, -⟩ := hq
    have hsep : 0 < csep q.2.1 q.2.2.1 :=
      lt_of_lt_of_le (by positivity : (0:ℝ) < 1/(k+1)) hab
    have hra := red_ne_of_csep_pos ha hb hsep
    have h1 : pertV r q.1 q.2.1 = pertV r q.1 (red q.2.1) := (pertV_red (hper q.1) ha).symm
    have h2 : pertV r q.1 q.2.2.1 = pertV r q.1 (red q.2.2.1) := (pertV_red (hper q.1) hb).symm
    exact hra ((hS q.1 hc).injective_on_period (red_mem_Ico ha) (red_mem_Ico hb)
      (by rw [← h1, ← h2, hcon]))
  have hpos2 : ∀ q ∈ Kv r₀ ×ˢ tripleSet k, pertV r q.1 q.2.1 ≠ pertV r q.1 q.2.2.2 := by
    intro q hq hcon
    obtain ⟨hc, ha, hb, hm, -, ham, -⟩ := hq
    have hsep : 0 < csep q.2.1 q.2.2.2 :=
      lt_of_lt_of_le (by positivity : (0:ℝ) < 1/(k+1)) ham
    have hra := red_ne_of_csep_pos ha hm hsep
    have h1 : pertV r q.1 q.2.1 = pertV r q.1 (red q.2.1) := (pertV_red (hper q.1) ha).symm
    have h2 : pertV r q.1 q.2.2.2 = pertV r q.1 (red q.2.2.2) := (pertV_red (hper q.1) hm).symm
    exact hra ((hS q.1 hc).injective_on_period (red_mem_Ico ha) (red_mem_Ico hm)
      (by rw [← h1, ← h2, hcon]))
  have hne : (Kv r₀ ×ˢ tripleSet k).Nonempty :=
    ⟨(0, (0, (2 * Real.pi / 3, 4 * Real.pi / 3))),
      Metric.mem_closedBall_self hr₀, tripleSet_mem_witness k⟩
  obtain ⟨q₁, hq₁, hmin₁⟩ := (isCompact_Kv r₀).prod (isCompact_tripleSet k) |>.exists_isMinOn
    hne hcont₁.continuousOn
  obtain ⟨q₂, hq₂, hmin₂⟩ := (isCompact_Kv r₀).prod (isCompact_tripleSet k) |>.exists_isMinOn
    hne hcont₂.continuousOn
  have hp₁ : 0 < φ₁ q₁ := by
    rw [hφ₁]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (hpos1 q₁ hq₁))
  have hp₂ : 0 < φ₂ q₂ := by
    rw [hφ₂]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (hpos2 q₂ hq₂))
  refine ⟨min (φ₁ q₁) (φ₂ q₂), lt_min hp₁ hp₂, ?_⟩
  intro c hc a b m hq
  have hqa : (c, (a, (b, m))) ∈ Kv r₀ ×ˢ tripleSet k := ⟨hc, hq⟩
  have hb1 : φ₁ q₁ ≤ φ₁ (c, (a, (b, m))) := hmin₁ hqa
  have hb2 : φ₂ q₂ ≤ φ₂ (c, (a, (b, m))) := hmin₂ hqa
  refine ⟨?_, ?_⟩
  · exact le_trans (min_le_left _ _) (by simpa [hφ₁] using hb1)
  · exact le_trans (min_le_right _ _) (by simpa [hφ₂] using hb2)

/-! ## The configuration constructor and the compact sets `Kn` -/

/-- The configuration with the given coordinates. -/
def mkCfg (l mu a b m : ℝ) : Cfg := WithLp.toLp 2 ![l, mu, a, b, m]

lemma mkCfg_ofLp (l mu a b m : ℝ) (i : Fin 5) :
    (mkCfg l mu a b m).ofLp i = ![l, mu, a, b, m] i := by
  simp [mkCfg]

lemma cfgLam_mkCfg (l mu a b m : ℝ) : cfgLam (mkCfg l mu a b m) = l := by
  simp [cfgLam, mkCfg]
lemma cfgMu_mkCfg (l mu a b m : ℝ) : cfgMu (mkCfg l mu a b m) = mu := by
  simp [cfgMu, mkCfg]
lemma cfgA_mkCfg (l mu a b m : ℝ) : cfgA (mkCfg l mu a b m) = a := by
  simp [cfgA, mkCfg]
lemma cfgB_mkCfg (l mu a b m : ℝ) : cfgB (mkCfg l mu a b m) = b := by
  simp [cfgB, mkCfg]
lemma cfgM_mkCfg (l mu a b m : ℝ) : cfgM (mkCfg l mu a b m) = m := by
  simp [cfgM, mkCfg]

/-- The coordinate box of a compact family of configurations. -/
def boxPi (Λ : ℝ) : Set (Fin 5 → ℝ) :=
  Set.univ.pi fun i => if (i : ℕ) = 0 ∨ (i : ℕ) = 1 then Set.Icc (-Λ) Λ
    else Set.Icc (0 : ℝ) (2 * Real.pi)

/-- The separation conditions on the three parameters. -/
def sepSet (k : ℕ) : Set (Fin 5 → ℝ) :=
  ((fun v : Fin 5 → ℝ => csep (v 2) (v 3)) ⁻¹' Set.Ici ((1:ℝ)/(k+1))) ∩
    (((fun v : Fin 5 → ℝ => csep (v 2) (v 4)) ⁻¹' Set.Ici ((1:ℝ)/(k+1))) ∩
     ((fun v : Fin 5 → ℝ => csep (v 3) (v 4)) ⁻¹' Set.Ici ((1:ℝ)/(k+1))))

/-- The compact family of configurations at separation scale `k` with multipliers
bounded by `Λ`. -/
def Kn (k : ℕ) (Λ : ℝ) : Set Cfg := cfgHomeo ⁻¹' (boxPi Λ ∩ sepSet k)

theorem isCompact_boxPi (Λ : ℝ) : IsCompact (boxPi Λ) := by
  refine isCompact_univ_pi fun i => ?_
  by_cases h : (i : ℕ) = 0 ∨ (i : ℕ) = 1
  · rw [if_pos h]; exact isCompact_Icc
  · rw [if_neg h]; exact isCompact_Icc

theorem isClosed_sepSet (k : ℕ) : IsClosed (sepSet k) := by
  have h2 : Continuous (fun v : Fin 5 → ℝ => csep (v 2) (v 3)) := by
    unfold csep
    exact (((continuous_apply 2).sub (continuous_apply 3)).abs).min
      (continuous_const.sub (((continuous_apply 2).sub (continuous_apply 3)).abs))
  have h3 : Continuous (fun v : Fin 5 → ℝ => csep (v 2) (v 4)) := by
    unfold csep
    exact (((continuous_apply 2).sub (continuous_apply 4)).abs).min
      (continuous_const.sub (((continuous_apply 2).sub (continuous_apply 4)).abs))
  have h4 : Continuous (fun v : Fin 5 → ℝ => csep (v 3) (v 4)) := by
    unfold csep
    exact (((continuous_apply 3).sub (continuous_apply 4)).abs).min
      (continuous_const.sub (((continuous_apply 3).sub (continuous_apply 4)).abs))
  have h2c : IsClosed ((fun v : Fin 5 → ℝ => csep (v 2) (v 3)) ⁻¹'
      Set.Ici ((1:ℝ)/(k+1))) := isClosed_Ici.preimage h2
  have h3c : IsClosed ((fun v : Fin 5 → ℝ => csep (v 2) (v 4)) ⁻¹'
      Set.Ici ((1:ℝ)/(k+1))) := isClosed_Ici.preimage h3
  have h4c : IsClosed ((fun v : Fin 5 → ℝ => csep (v 3) (v 4)) ⁻¹'
      Set.Ici ((1:ℝ)/(k+1))) := isClosed_Ici.preimage h4
  rw [sepSet]
  exact h2c.inter (h3c.inter h4c)

theorem isCompact_Kn (k : ℕ) (Λ : ℝ) : IsCompact (Kn k Λ) := by
  have h : IsCompact (boxPi Λ ∩ sepSet k) := (isCompact_boxPi Λ).inter_right (isClosed_sepSet k)
  have himg : cfgHomeo.symm '' (boxPi Λ ∩ sepSet k) = Kn k Λ := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa [Kn] using hv
    · intro hw
      exact ⟨cfgHomeo w, hw, cfgHomeo.symm_apply_apply w⟩
  rw [← himg]
  exact h.image cfgHomeo.symm.continuous

lemma Kn_spec (k : ℕ) (Λ : ℝ) {w : Cfg} (hw : w ∈ Kn k Λ) :
    |cfgLam w| ≤ Λ ∧ |cfgMu w| ≤ Λ ∧ cfgA w ∈ Set.Icc 0 (2 * Real.pi) ∧
      cfgB w ∈ Set.Icc 0 (2 * Real.pi) ∧ cfgM w ∈ Set.Icc 0 (2 * Real.pi) ∧
      (1:ℝ)/(k+1) ≤ csep (cfgA w) (cfgB w) ∧ (1:ℝ)/(k+1) ≤ csep (cfgA w) (cfgM w) ∧
      (1:ℝ)/(k+1) ≤ csep (cfgB w) (cfgM w) := by
  have hp : ∀ i : Fin 5, cfgHomeo w i ∈ (if ((i : ℕ) = 0 ∨ (i : ℕ) = 1) then
      Set.Icc (-Λ) Λ else Set.Icc (0 : ℝ) (2 * Real.pi)) := by
    intro i
    have := Set.mem_pi.mp hw.1 i (Set.mem_univ i)
    simpa [boxPi] using this
  have hs := hw.2
  simp only [sepSet, Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ici] at hs
  rw [← cfgA_homeo w, ← cfgB_homeo w, ← cfgM_homeo w] at hs
  refine ⟨?_, ?_, ?_, ?_, ?_, hs.1, hs.2.1, hs.2.2⟩
  · have h := hp 0
    rw [if_pos (Or.inl (show (((0 : Fin 5) : ℕ)) = 0 from rfl))] at h
    rw [cfgLam_homeo w]
    exact abs_le.mpr (Set.mem_Icc.mp h)
  · have h := hp 1
    rw [if_pos (Or.inr (show (((1 : Fin 5) : ℕ)) = 1 from rfl))] at h
    rw [cfgMu_homeo w]
    exact abs_le.mpr (Set.mem_Icc.mp h)
  · have h := hp 2
    rw [if_neg (by decide : ¬ ((((2 : Fin 5) : ℕ)) = 0 ∨ (((2 : Fin 5) : ℕ)) = 1))] at h
    rwa [cfgA_homeo w]
  · have h := hp 3
    rw [if_neg (by decide : ¬ ((((3 : Fin 5) : ℕ)) = 0 ∨ (((3 : Fin 5) : ℕ)) = 1))] at h
    rwa [cfgB_homeo w]
  · have h := hp 4
    rw [if_neg (by decide : ¬ ((((4 : Fin 5) : ℕ)) = 0 ∨ (((4 : Fin 5) : ℕ)) = 1))] at h
    rwa [cfgM_homeo w]

lemma mem_Kn_mkCfg {k : ℕ} {Λ lam mu a b m : ℝ} (hl : |lam| ≤ Λ) (hmu : |mu| ≤ Λ)
    (ha : a ∈ Set.Icc 0 (2 * Real.pi)) (hb : b ∈ Set.Icc 0 (2 * Real.pi))
    (hm : m ∈ Set.Icc 0 (2 * Real.pi))
    (hab : (1:ℝ)/(k+1) ≤ csep a b) (ham : (1:ℝ)/(k+1) ≤ csep a m)
    (hbm : (1:ℝ)/(k+1) ≤ csep b m) : mkCfg lam mu a b m ∈ Kn k Λ := by
  have hcoord : cfgHomeo (mkCfg lam mu a b m) = ![lam, mu, a, b, m] := by
    funext i
    rw [cfgHomeo_apply]
    exact mkCfg_ofLp lam mu a b m i
  constructor
  · rw [hcoord, boxPi]
    intro i _
    fin_cases i <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
        Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, if_true, if_false, ↓reduceIte,
        Set.mem_Icc]
    · exact abs_le.mp hl
    · exact abs_le.mp hmu
    · exact ha
    · exact hb
    · exact hm
  · rw [hcoord, sepSet]
    exact ⟨hab, ham, hbm⟩

/-! ## Speed bounds and the separation constants -/

theorem exists_speedBound {r : ℝ → Space} (hr : IsSmoothKnot r) (r₀ : ℝ) :
    ∃ M : ℝ, ∀ c ∈ Kv r₀, ∀ t ∈ Set.Icc 0 (2 * Real.pi), ‖pertVelV r c t‖ ≤ M := by
  have hvc : Continuous (velocity r) := by
    show Continuous (deriv r)
    exact hr.smooth.continuous_deriv le_top
  obtain ⟨t₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (⟨0, le_rfl, by positivity⟩ : (Set.Icc (0:ℝ) (2*Real.pi)).Nonempty) hvc.norm.continuousOn
  refine ⟨‖velocity r t₀‖ + 36 * (max ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ 1) * max r₀ 0, ?_⟩
  intro c hc t ht
  have hcn : ‖c‖ ≤ max r₀ 0 := by
    rw [Kv, Metric.mem_closedBall, dist_zero_right] at hc
    exact hc.trans (le_max_left r₀ 0)
  have hop : ‖eCoeff c‖ ≤ ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ * ‖c‖ :=
    ContinuousLinearMap.le_opNorm (eCoeff : Coeff →L[ℝ] (Fin 9 → Space)) c
  have hkey : ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ * ‖c‖
      ≤ (max ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ 1) * max r₀ 0 :=
    mul_le_mul (le_max_left _ _) hcn (norm_nonneg c)
      (le_trans (norm_nonneg _) (le_max_left _ _))
  have h1 : ‖eCoeff c‖ ≤ (max ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ 1) * max r₀ 0 :=
    le_trans hop hkey
  have h2 : ‖pertVelV r c t‖ ≤ ‖velocity r t‖ + ‖perturbVelCorr (eCoeff c) t‖ := by
    rw [pertVelV, perturbVel]
    exact norm_add_le _ _
  have h3 : ‖perturbVelCorr (eCoeff c) t‖ ≤ 36 * ‖eCoeff c‖ := norm_perturbVelCorr_le _ _
  have h4 : ‖velocity r t‖ ≤ ‖velocity r t₀‖ := hmax ht
  nlinarith [h1, h2, h3, h4]

/-- A bound for the speed of the perturbed curve on `Kv r₀`. -/
noncomputable def speedBound (r : ℝ → Space) (hr : IsSmoothKnot r) (r₀ : ℝ) : ℝ :=
  Classical.choose (exists_speedBound hr r₀)

lemma speedBound_spec {r : ℝ → Space} (hr : IsSmoothKnot r) (r₀ : ℝ) :
    ∀ c ∈ Kv r₀, ∀ t ∈ Set.Icc 0 (2 * Real.pi), ‖pertVelV r c t‖ ≤ speedBound r hr r₀ :=
  Classical.choose_spec (exists_speedBound hr r₀)

/-- The separation constant at scale `k`. -/
noncomputable def deltaN (r : ℝ → Space) (hr : ContDiff ℝ ⊤ r) (r₀ : ℝ) (hr₀ : 0 ≤ r₀)
    (hS : ∀ c ∈ Kv r₀, IsSmoothKnot (pertV r c))
    (hper : ∀ c : Coeff, Function.Periodic (pertV r c) (2 * Real.pi)) (k : ℕ) : ℝ :=
  Classical.choose (exists_delta hr hr₀ hS hper k)

lemma deltaN_pos {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) {r₀ : ℝ} (hr₀ : 0 ≤ r₀)
    {hS : ∀ c ∈ Kv r₀, IsSmoothKnot (pertV r c)}
    {hper : ∀ c : Coeff, Function.Periodic (pertV r c) (2 * Real.pi)} (k : ℕ) :
    0 < deltaN r hr r₀ hr₀ hS hper k :=
  (Classical.choose_spec (exists_delta hr hr₀ hS hper k)).1

lemma deltaN_le {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) {r₀ : ℝ} (hr₀ : 0 ≤ r₀)
    {hS : ∀ c ∈ Kv r₀, IsSmoothKnot (pertV r c)}
    {hper : ∀ c : Coeff, Function.Periodic (pertV r c) (2 * Real.pi)} (k : ℕ)
    {c : Coeff} (hc : c ∈ Kv r₀) (a b m : ℝ) (hq : (a, (b, m)) ∈ tripleSet k) :
    deltaN r hr r₀ hr₀ hS hper k ≤ ‖pertV r c a - pertV r c b‖ ∧
      deltaN r hr r₀ hr₀ hS hper k ≤ ‖pertV r c a - pertV r c m‖ :=
  (Classical.choose_spec (exists_delta hr hr₀ hS hper k)).2 c hc a b m hq

lemma velocity_pertV {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) (c : Coeff) (t : ℝ) :
    velocity (pertV r c) t = pertVelV r c t := by
  have h := congrFun (deriv_perturb hr (eCoeff c)) t
  simpa [velocity, pertV, pertVelV] using h

lemma pertV_periodic {r : ℝ → Space} (hr : IsSmoothKnot r) (c : Coeff) :
    Function.Periodic (pertV r c) period := by
  have hper2 : Function.Periodic (perturbCorr (eCoeff c)) period := periodic_perturbCorr (eCoeff c)
  intro t
  simp only [pertV, perturb]
  rw [hr.periodic t, hper2 t]

theorem isSmoothKnot_pertV {r : ℝ → Space} (hr : IsSmoothKnot r) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hsm : ∀ w : ℝ → Space, ContDiff ℝ ⊤ w → Function.Periodic w period →
      (∀ t, ‖w t‖ < ε₀ ∧ ‖velocity w t‖ < ε₀) → IsSmoothKnot (fun t => r t + w t))
    {c : Coeff} (hc : ‖eCoeff c‖ < ε₀ / 36) : IsSmoothKnot (pertV r c) := by
  have h1 : ∀ t, ‖perturbCorr (eCoeff c) t‖ < ε₀ := by
    intro t
    have h := norm_perturbCorr_le (eCoeff c) t
    have h2 : 9 * ‖eCoeff c‖ < ε₀ := by linarith
    linarith
  have h2 : ∀ t, ‖velocity (perturbCorr (eCoeff c)) t‖ < ε₀ := by
    intro t
    have h := norm_perturbVelCorr_le (eCoeff c) t
    have h3 : 36 * ‖eCoeff c‖ < ε₀ := by linarith
    rw [velocity, deriv_perturbCorr]
    linarith
  exact hsm (perturbCorr (eCoeff c)) (contDiff_perturbCorr _)
    (periodic_perturbCorr _) (fun t => ⟨h1 t, h2 t⟩)

/-- The multiplier bound at separation scale `k`. -/
noncomputable def lambdaN (r : ℝ → Space) (hr : IsSmoothKnot r) (r₀ : ℝ) (hr₀ : 0 ≤ r₀)
    (hS : ∀ c ∈ Kv r₀, IsSmoothKnot (pertV r c))
    (hper : ∀ c : Coeff, Function.Periodic (pertV r c) (2 * Real.pi)) (k : ℕ) : ℝ :=
  speedBound r hr r₀ / deltaN r hr.smooth r₀ hr₀ hS hper k

end

end Work.Drive
