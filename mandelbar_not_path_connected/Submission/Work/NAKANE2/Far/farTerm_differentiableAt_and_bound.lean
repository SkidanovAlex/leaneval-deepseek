import Mathlib
import Submission.Work.NAKANE2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1600000

namespace Work.NAKANE2.Far

open scoped Topology ComplexConjugate

/-! ## The critical orbit in the parameter: continuity and differentiability -/

lemma dtbContinuous_critZ (k : ℕ) : Continuous (fun c : ℂ => critZ c k) := by
  induction k with
  | zero => exact continuous_id
  | succ k ih =>
    have h : (fun c : ℂ => critZ c (k+1)) =
        fun c => ((critZ c k)^2 + (starRingEnd ℂ) c)^2 + c := by
      funext c
      rw [critZ_succ, Work.Bottcher.pMap_apply]
    rw [h]
    fun_prop

lemma differentiableAt_critZ (k : ℕ) (c : ℂ) :
    DifferentiableAt ℝ (fun c : ℂ => critZ c k) c := by
  induction k with
  | zero => simpa using differentiableAt_id (𝕜 := ℝ)
  | succ k ih =>
    have h : (fun c : ℂ => critZ c (k+1)) =
        fun c => ((critZ c k)^2 + (starRingEnd ℂ) c)^2 + c := by
      funext c
      rw [critZ_succ, Work.Bottcher.pMap_apply]
    rw [h]
    fun_prop

/-! ## Complex conjugation as a real-linear map -/

noncomputable def dtbConjCLM : ℂ →L[ℝ] ℂ where
  toFun := starRingEnd ℂ
  map_add' x y := by simp
  map_smul' a x := by simp
  cont := continuous_star

lemma dtbConjCLM_apply (x : ℂ) : dtbConjCLM x = (starRingEnd ℂ) x := rfl

lemma dtbHasFDerivAt_conj (c : ℂ) : HasFDerivAt (fun u : ℂ => (starRingEnd ℂ) u) dtbConjCLM c :=
  dtbConjCLM.hasFDerivAt

lemma dtbNorm_conjCLM : ‖dtbConjCLM‖ = 1 := by
  refine le_antisymm ?_ ?_
  · rw [ContinuousLinearMap.opNorm_le_iff zero_le_one]
    intro x
    rw [dtbConjCLM_apply]
    simp
  · have h := ContinuousLinearMap.le_opNorm dtbConjCLM (1 : ℂ)
    rw [dtbConjCLM_apply, map_one, norm_one, mul_one] at h
    exact h

/-! ## The parameter-derivative of the critical orbit -/

noncomputable def dCritZ (c : ℂ) : ℕ → (ℂ →L[ℝ] ℂ)
  | 0 => 1
  | (k + 1) =>
      (2 * (critZ c k ^ 2 + (starRingEnd ℂ) c)) •
        ((2 * critZ c k) • dCritZ c k + dtbConjCLM) + 1

@[simp]
lemma dCritZ_zero (c : ℂ) : dCritZ c 0 = 1 := rfl

lemma dCritZ_succ (c : ℂ) (k : ℕ) :
    dCritZ c (k + 1) =
      (2 * (critZ c k ^ 2 + (starRingEnd ℂ) c)) •
        ((2 * critZ c k) • dCritZ c k + dtbConjCLM) + 1 := rfl

/-- The `n`-fold power rule in the normalised form used below. -/
lemma hasFDerivAt_pow_two {f : ℂ → ℂ} {f' : ℂ →L[ℝ] ℂ} {x : ℂ}
    (h : HasFDerivAt f f' x) :
    HasFDerivAt (fun y : ℂ => f y ^ 2) ((2 * f x) • f') x := by
  have hh := h.pow 2
  simp only [nsmul_eq_mul, Nat.reduceSub, pow_one] at hh
  exact hh

lemma dtbHasFDerivAt_critZ (c : ℂ) (k : ℕ) :
    HasFDerivAt (fun w : ℂ => critZ w k) (dCritZ c k) c := by
  induction k with
  | zero =>
    have h : (fun w : ℂ => critZ w 0) = (fun w : ℂ => w) := rfl
    rw [h, dCritZ_zero]
    exact hasFDerivAt_id (𝕜 := ℝ) c
  | succ k ih =>
    have key : (fun w : ℂ => critZ w (k + 1)) =
        fun w => (critZ w k ^ 2 + (starRingEnd ℂ) w) ^ 2 + w := by
      funext w
      rw [critZ_succ, Work.Bottcher.pMap_apply]
    rw [key]
    have h1 : HasFDerivAt (fun w : ℂ => critZ w k ^ 2) ((2 * critZ c k) • dCritZ c k) c :=
      (hasFDerivAt_pow_two ih)
    have h2 : HasFDerivAt (fun w : ℂ => critZ w k ^ 2 + (starRingEnd ℂ) w)
        ((2 * critZ c k) • dCritZ c k + dtbConjCLM) c :=
      h1.add (dtbHasFDerivAt_conj c)
    have h3 : HasFDerivAt (fun w : ℂ => (critZ w k ^ 2 + (starRingEnd ℂ) w) ^ 2)
        ((2 * (critZ c k ^ 2 + (starRingEnd ℂ) c)) •
          ((2 * critZ c k) • dCritZ c k + dtbConjCLM)) c :=
      (hasFDerivAt_pow_two h2)
    have h4 : HasFDerivAt (fun w : ℂ => (critZ w k ^ 2 + (starRingEnd ℂ) w) ^ 2 + w)
        ((2 * (critZ c k ^ 2 + (starRingEnd ℂ) c)) •
          ((2 * critZ c k) • dCritZ c k + dtbConjCLM) + 1) c :=
      h3.add (hasFDerivAt_id (𝕜 := ℝ) c)
    rw [dCritZ_succ]
    exact h4

/-! ## The two partial derivatives of `normFactor` -/

noncomputable def dcnf (c v : ℂ) : ℂ →L[ℝ] ℂ :=
  (v ^ 4)⁻¹ •
    ((2 * (v ^ 2 + (starRingEnd ℂ) c)) • dtbConjCLM + 1)

lemma dcnf_apply (c v x : ℂ) : dcnf c v x =
    (v ^ 4)⁻¹ * ((2 * (v ^ 2 + (starRingEnd ℂ) c)) * (starRingEnd ℂ) x + x) := by
  simp only [dcnf, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, dtbConjCLM_apply]
  ring

noncomputable def dznf (c v : ℂ) : ℂ →L[ℝ] ℂ :=
  (Work.Bottcher.Core.dnf c v) • (1 : ℂ →L[ℝ] ℂ)

lemma dznf_apply (c v x : ℂ) : dznf c v x = Work.Bottcher.Core.dnf c v * x := by
  simp only [dznf, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    smul_eq_mul]


lemma hasFDerivAt_normFactor_fst (c v : ℂ) :
    HasFDerivAt (fun u : ℂ => Work.Bottcher.normFactor u v) (dcnf c v) c := by
  have h1 : HasFDerivAt (fun u : ℂ => v ^ 2 + (starRingEnd ℂ) u) dtbConjCLM c := by
    have hh := (hasFDerivAt_const (v ^ 2) c).add (dtbHasFDerivAt_conj c)
    rw [zero_add] at hh
    exact hh
  have h2 : HasFDerivAt (fun u : ℂ => (v ^ 2 + (starRingEnd ℂ) u) ^ 2)
      ((2 * (v ^ 2 + (starRingEnd ℂ) c)) • dtbConjCLM) c :=
    (hasFDerivAt_pow_two h1)
  have h3 : HasFDerivAt (fun u : ℂ => (v ^ 2 + (starRingEnd ℂ) u) ^ 2 + u)
      ((2 * (v ^ 2 + (starRingEnd ℂ) c)) • dtbConjCLM + 1) c := by
    have hh := h2.add (hasFDerivAt_id (𝕜 := ℝ) c)
    rw [← ContinuousLinearMap.one_def] at hh
    exact hh
  have h4 : HasFDerivAt (fun y : ℂ => ((v ^ 2 + (starRingEnd ℂ) y) ^ 2 + y) * (v ^ 4)⁻¹)
      (dcnf c v) c :=
    h3.mul_const ((v ^ 4)⁻¹)
  convert h4 using 1
  · ext u
    simp only [Work.Bottcher.normFactor, Work.Bottcher.pMap_apply, div_eq_mul_inv]

lemma hasFDerivAt_normFactor_snd (c v : ℂ) (hv : 1 + ‖c‖ ≤ ‖v‖) :
    HasFDerivAt (fun z : ℂ => Work.Bottcher.normFactor c z) (dznf c v) v := by
  have hv0 : v ≠ 0 := Work.Bottcher.Core.ne_zero_of_one_add_le_norm c v hv
  have h := ((Work.Bottcher.Core.hasDerivAt_normFactor c v hv0).hasFDerivAt).restrictScalars ℝ
  convert h using 1
  ext z : 1
  simp only [dznf, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_restrictScalars',
    smul_eq_mul]
  ring

lemma norm_smul_clm_le (a : ℂ) (L : ℂ →L[ℝ] ℂ) : ‖a • L‖ ≤ ‖a‖ * ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [ContinuousLinearMap.smul_apply, norm_smul]
  calc ‖a‖ * ‖L x‖ ≤ ‖a‖ * (‖L‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm L x) (norm_nonneg a)
    _ = ‖a‖ * ‖L‖ * ‖x‖ := by ring

lemma norm_one_clm : ‖(1 : ℂ →L[ℝ] ℂ)‖ = 1 := by
  refine le_antisymm ?_ ?_
  · rw [ContinuousLinearMap.opNorm_le_iff zero_le_one]
    intro x
    rw [ContinuousLinearMap.one_apply, one_mul]
  · have h := ContinuousLinearMap.le_opNorm (1 : ℂ →L[ℝ] ℂ) (1 : ℂ)
    rw [ContinuousLinearMap.one_apply, norm_one, mul_one] at h
    exact h

lemma norm_dcnf_le (c v : ℂ) (hv : 1 + ‖c‖ ≤ ‖v‖) : ‖dcnf c v‖ ≤ 5 / ‖v‖ ^ 2 := by
  have hv1 : (1 : ℝ) ≤ ‖v‖ := by linarith [norm_nonneg c]
  have hvpos : (0 : ℝ) < ‖v‖ := by linarith
  have hconjx : ∀ x : ℂ, ‖(starRingEnd ℂ) x‖ = ‖x‖ := fun x => Complex.norm_conj x
  have hcoef : ‖2 * (v ^ 2 + (starRingEnd ℂ) c)‖ ≤ 2 * (‖v‖ ^ 2 + ‖c‖) := by
    rw [norm_mul]
    have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hnorm2]
    have h2 : ‖v ^ 2 + (starRingEnd ℂ) c‖ ≤ ‖v‖ ^ 2 + ‖c‖ := by
      calc ‖v ^ 2 + (starRingEnd ℂ) c‖ ≤ ‖v ^ 2‖ + ‖(starRingEnd ℂ) c‖ := norm_add_le _ _
        _ = ‖v‖ ^ 2 + ‖c‖ := by rw [norm_pow, Complex.norm_conj]
    linarith
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [dcnf_apply]
  have hnum : ‖(2 * (v ^ 2 + (starRingEnd ℂ) c)) * (starRingEnd ℂ) x + x‖
      ≤ (2 * (‖v‖ ^ 2 + ‖c‖) + 1) * ‖x‖ := by
    calc ‖(2 * (v ^ 2 + (starRingEnd ℂ) c)) * (starRingEnd ℂ) x + x‖
        ≤ ‖(2 * (v ^ 2 + (starRingEnd ℂ) c)) * (starRingEnd ℂ) x‖ + ‖x‖ := norm_add_le _ _
      _ = ‖2 * (v ^ 2 + (starRingEnd ℂ) c)‖ * ‖x‖ + ‖x‖ := by rw [norm_mul, hconjx]
      _ ≤ (2 * (‖v‖ ^ 2 + ‖c‖)) * ‖x‖ + ‖x‖ := by
          have hh := mul_le_mul_of_nonneg_right hcoef (norm_nonneg x)
          linarith
      _ = (2 * (‖v‖ ^ 2 + ‖c‖) + 1) * ‖x‖ := by ring
  have h1 : (2 * (‖v‖ ^ 2 + ‖c‖) + 1) ≤ 5 * ‖v‖ ^ 2 := by
    have h2 : ‖c‖ ≤ ‖v‖ := by linarith
    nlinarith [hv1, h2, sq_nonneg (‖v‖ - 1)]
  calc ‖(v ^ 4)⁻¹ * ((2 * (v ^ 2 + (starRingEnd ℂ) c)) * (starRingEnd ℂ) x + x)‖
      = ‖(v ^ 4)⁻¹‖ * ‖(2 * (v ^ 2 + (starRingEnd ℂ) c)) * (starRingEnd ℂ) x + x‖ :=
        norm_mul _ _
    _ = (1 / ‖v‖ ^ 4) * ‖(2 * (v ^ 2 + (starRingEnd ℂ) c)) * (starRingEnd ℂ) x + x‖ := by
        rw [norm_inv, norm_pow, one_div]
    _ ≤ (1 / ‖v‖ ^ 4) * ((2 * (‖v‖ ^ 2 + ‖c‖) + 1) * ‖x‖) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
    _ ≤ (1 / ‖v‖ ^ 4) * ((5 * ‖v‖ ^ 2) * ‖x‖) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right h1 (norm_nonneg x)
    _ = (5 / ‖v‖ ^ 2) * ‖x‖ := by field_simp

lemma norm_dznf_le (c v : ℂ) (hv : 1 + ‖c‖ ≤ ‖v‖) :
    ‖dznf c v‖ ≤ (8 * ‖c‖ + 8) / ‖v‖ ^ 3 := by
  have h : ‖dznf c v‖ ≤ ‖Work.Bottcher.Core.dnf c v‖ * 1 := by
    rw [dznf]
    calc ‖(Work.Bottcher.Core.dnf c v) • (1 : ℂ →L[ℝ] ℂ)‖
        ≤ ‖Work.Bottcher.Core.dnf c v‖ * ‖(1 : ℂ →L[ℝ] ℂ)‖ := norm_smul_clm_le _ _
      _ = ‖Work.Bottcher.Core.dnf c v‖ * 1 := by rw [norm_one_clm]
  rw [mul_one] at h
  exact h.trans (Work.Bottcher.Core.norm_dnf_le c v hv)

/-! ## The pair map `(c,z) ↦ normFactor c z` -/

lemma differentiableAt_normFactor_pair (c z : ℂ) (hz : 1 + ‖c‖ ≤ ‖z‖) :
    DifferentiableAt ℝ (fun p : ℂ × ℂ => Work.Bottcher.normFactor p.1 p.2) (c, z) := by
  have hz0 : z ≠ 0 := Work.Bottcher.Core.ne_zero_of_one_add_le_norm c z hz
  have hfun : (fun p : ℂ × ℂ => ((p.2 ^ 2 + (starRingEnd ℂ) p.1) ^ 2 + p.1) * (p.2 ^ 4)⁻¹)
      = fun p : ℂ × ℂ => Work.Bottcher.normFactor p.1 p.2 := by
    funext p
    simp only [Work.Bottcher.normFactor, Work.Bottcher.pMap_apply, div_eq_mul_inv]
  rw [← hfun]
  have h1 : DifferentiableAt ℝ (fun p : ℂ × ℂ => p.2 ^ 2 + (starRingEnd ℂ) p.1) (c, z) :=
    ((differentiableAt_snd (𝕜 := ℝ) (p := (c, z))).pow 2).add
      ((Complex.differentiable_conj.differentiableAt).comp (c, z) differentiableAt_fst)
  have h2 : DifferentiableAt ℝ (fun p : ℂ × ℂ => (p.2 ^ 2 + (starRingEnd ℂ) p.1) ^ 2 + p.1)
      (c, z) := (h1.pow 2).add differentiableAt_fst
  have h3 : DifferentiableAt ℝ (fun p : ℂ × ℂ => (p.2 ^ 4)⁻¹) (c, z) :=
    ((differentiableAt_snd (𝕜 := ℝ) (p := (c, z))).pow 4).inv (pow_ne_zero 4 hz0)
  exact h2.mul h3

lemma coprod_comp_inl_inr (L : ℂ × ℂ →L[ℝ] ℂ) :
    (L.comp (ContinuousLinearMap.inl ℝ ℂ ℂ)).coprod
      (L.comp (ContinuousLinearMap.inr ℝ ℂ ℂ)) = L := by
  refine ContinuousLinearMap.ext fun w => ?_
  obtain ⟨a, b⟩ := w
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  rw [← map_add]
  congr 1
  simp

lemma fderiv_comp_inl {g : ℂ × ℂ → ℂ} {c z : ℂ} (hg : DifferentiableAt ℝ g (c, z)) :
    (fderiv ℝ g (c, z)).comp (ContinuousLinearMap.inl ℝ ℂ ℂ) =
      fderiv ℝ (fun u : ℂ => g (u, z)) c := by
  have h1 : DifferentiableAt ℝ (fun u : ℂ => (u, z)) c :=
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) c z).differentiableAt
  have h2 := fderiv_comp (g := g) (f := fun u : ℂ => (u, z)) (x := c) hg h1
  rw [(hasFDerivAt_prodMk_left (𝕜 := ℝ) c z).fderiv] at h2
  exact h2.symm

lemma fderiv_comp_inr {g : ℂ × ℂ → ℂ} {c z : ℂ} (hg : DifferentiableAt ℝ g (c, z)) :
    (fderiv ℝ g (c, z)).comp (ContinuousLinearMap.inr ℝ ℂ ℂ) =
      fderiv ℝ (fun t : ℂ => g (c, t)) z := by
  have h1 : DifferentiableAt ℝ (fun t : ℂ => (c, t)) z :=
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) c z).differentiableAt
  have h2 := fderiv_comp (g := g) (f := fun t : ℂ => (c, t)) (x := z) hg h1
  rw [(hasFDerivAt_prodMk_right (𝕜 := ℝ) c z).fderiv] at h2
  exact h2.symm

lemma fderiv_pair_eq_coprod {g : ℂ × ℂ → ℂ} {c z : ℂ} (hg : DifferentiableAt ℝ g (c, z)) :
    fderiv ℝ g (c, z) =
      (fderiv ℝ (fun u : ℂ => g (u, z)) c).coprod (fderiv ℝ (fun t : ℂ => g (c, t)) z) := by
  have h := coprod_comp_inl_inr (fderiv ℝ g (c, z))
  rw [fderiv_comp_inl hg, fderiv_comp_inr hg] at h
  exact h.symm

lemma hasFDerivAt_normFactor_pair (c z : ℂ) (hz : 1 + ‖c‖ ≤ ‖z‖) :
    HasFDerivAt (fun p : ℂ × ℂ => Work.Bottcher.normFactor p.1 p.2)
      ((dcnf c z).coprod (dznf c z)) (c, z) := by
  have hgdiff : DifferentiableAt ℝ (fun p : ℂ × ℂ => Work.Bottcher.normFactor p.1 p.2) (c, z) :=
    differentiableAt_normFactor_pair c z hz
  have h := hgdiff.hasFDerivAt
  rw [fderiv_pair_eq_coprod hgdiff] at h
  rw [show fderiv ℝ (fun u : ℂ => (fun p : ℂ × ℂ => Work.Bottcher.normFactor p.1 p.2) (u, z)) c
        = dcnf c z from (hasFDerivAt_normFactor_fst c z).fderiv,
      show fderiv ℝ (fun t : ℂ => (fun p : ℂ × ℂ => Work.Bottcher.normFactor p.1 p.2) (c, t)) z
        = dznf c z from (hasFDerivAt_normFactor_snd c z hz).fderiv] at h
  exact h


/-! ## The composite derivative and the term bound -/

lemma coprod_comp_prod (A B D : ℂ →L[ℝ] ℂ) :
    (A.coprod B).comp ((1 : ℂ →L[ℝ] ℂ).prod D) = A + B.comp D := by
  ext x : 1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.add_apply]

lemma norm_fderiv_farTerm_le {N n : ℕ} {c : ℂ} {R Cdz : ℝ}
    (hR : 0 < R) (hCdz : 0 ≤ Cdz)
    (hZ1 : 1 + ‖c‖ ≤ ‖critZ c (N + n)‖)
    (hZR : R ≤ ‖critZ c (N + n)‖)
    (hDZ : ‖dCritZ c (N + n)‖ ≤ Cdz * ‖critZ c (N + n)‖ ^ 2) :
    DifferentiableAt ℝ (fun w : ℂ => farTerm N w n) c ∧
      ‖fderiv ℝ (fun w : ℂ => farTerm N w n) c‖
        ≤ (5 / R ^ 2 + (8 * ‖c‖ + 8) * Cdz / R) * (1 / 4 : ℝ) ^ n := by
  have hstep : HasFDerivAt (fun w : ℂ => Work.Bottcher.normFactor w (critZ w (N + n)))
      (dcnf c (critZ c (N + n)) +
        (dznf c (critZ c (N + n))).comp (dCritZ c (N + n))) c := by
    have hpair := hasFDerivAt_normFactor_pair c (critZ c (N + n)) hZ1
    have hΨ : HasFDerivAt (fun w : ℂ => (w, critZ w (N + n)))
        ((1 : ℂ →L[ℝ] ℂ).prod (dCritZ c (N + n))) c :=
      (hasFDerivAt_id (𝕜 := ℝ) c).prodMk (dtbHasFDerivAt_critZ c (N + n))
    have hcomp := hpair.comp c hΨ
    rw [coprod_comp_prod] at hcomp
    exact hcomp
  have hnormstep : ‖dcnf c (critZ c (N + n)) +
        (dznf c (critZ c (N + n))).comp (dCritZ c (N + n))‖
      ≤ 5 / R ^ 2 + (8 * ‖c‖ + 8) * Cdz / R := by
    have ha : ‖dcnf c (critZ c (N + n))‖ ≤ 5 / ‖critZ c (N + n)‖ ^ 2 :=
      norm_dcnf_le c _ hZ1
    have ha' : 5 / ‖critZ c (N + n)‖ ^ 2 ≤ 5 / R ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity : (0 : ℝ) < R ^ 2)
        (pow_le_pow_left₀ hR.le hZR 2)
    have hb : ‖(dznf c (critZ c (N + n))).comp (dCritZ c (N + n))‖
        ≤ ‖dznf c (critZ c (N + n))‖ * ‖dCritZ c (N + n)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    have hc : ‖dznf c (critZ c (N + n))‖ ≤ (8 * ‖c‖ + 8) / ‖critZ c (N + n)‖ ^ 3 :=
      norm_dznf_le c _ hZ1
    have hc0 : (0 : ℝ) ≤ (8 * ‖c‖ + 8) / ‖critZ c (N + n)‖ ^ 3 := by positivity
    have hd : ‖dznf c (critZ c (N + n))‖ * ‖dCritZ c (N + n)‖
        ≤ ((8 * ‖c‖ + 8) / ‖critZ c (N + n)‖ ^ 3) * (Cdz * ‖critZ c (N + n)‖ ^ 2) :=
      mul_le_mul hc hDZ (norm_nonneg _) hc0
    have he : ((8 * ‖c‖ + 8) / ‖critZ c (N + n)‖ ^ 3) * (Cdz * ‖critZ c (N + n)‖ ^ 2)
        = (8 * ‖c‖ + 8) * Cdz / ‖critZ c (N + n)‖ := by
      field_simp
    have hf : (8 * ‖c‖ + 8) * Cdz / ‖critZ c (N + n)‖ ≤ (8 * ‖c‖ + 8) * Cdz / R :=
      div_le_div_of_nonneg_left (by positivity) hR hZR
    have h1 : ‖(dznf c (critZ c (N + n))).comp (dCritZ c (N + n))‖
        ≤ (8 * ‖c‖ + 8) * Cdz / R := (hb.trans (hd.trans he.le)).trans hf
    calc ‖dcnf c (critZ c (N + n)) +
          (dznf c (critZ c (N + n))).comp (dCritZ c (N + n))‖
        ≤ ‖dcnf c (critZ c (N + n))‖ +
          ‖(dznf c (critZ c (N + n))).comp (dCritZ c (N + n))‖ := norm_add_le _ _
      _ ≤ 5 / R ^ 2 + (8 * ‖c‖ + 8) * Cdz / R := by linarith
  have hnfslit : Work.Bottcher.normFactor c (critZ c (N + n)) ∈ Complex.slitPlane :=
    Work.Bottcher.Core.normFactor_mem_slitPlane c _ hZ1
  have hnfge : (1 : ℝ) / 4 ≤ ‖Work.Bottcher.normFactor c (critZ c (N + n))‖ :=
    Work.Bottcher.Core.norm_normFactor_ge c _ hZ1
  have hLOGD : HasFDerivAt Complex.log
      ((ContinuousLinearMap.toSpanSingleton ℂ
          ((Work.Bottcher.normFactor c (critZ c (N + n)))⁻¹)).restrictScalars ℝ)
      (Work.Bottcher.normFactor c (critZ c (N + n))) :=
    ((Complex.hasStrictDerivAt_log hnfslit).hasDerivAt.hasFDerivAt).restrictScalars ℝ
  have hlog : HasFDerivAt
      (fun w : ℂ => Complex.log (Work.Bottcher.normFactor w (critZ w (N + n))))
      (((ContinuousLinearMap.toSpanSingleton ℂ
          ((Work.Bottcher.normFactor c (critZ c (N + n)))⁻¹)).restrictScalars ℝ).comp
        (dcnf c (critZ c (N + n)) +
          (dznf c (critZ c (N + n))).comp (dCritZ c (N + n)))) c := by
    have h := hLOGD.comp c hstep
    exact h
  have hinv : ‖(Work.Bottcher.normFactor c (critZ c (N + n)))⁻¹‖ ≤ 4 := by
    rw [norm_inv, inv_le_comm₀ (by positivity) (by norm_num), ← one_div]
    exact hnfge
  have hLOGDcomp : ‖((ContinuousLinearMap.toSpanSingleton ℂ
          ((Work.Bottcher.normFactor c (critZ c (N + n)))⁻¹)).restrictScalars ℝ).comp
        (dcnf c (critZ c (N + n)) +
          (dznf c (critZ c (N + n))).comp (dCritZ c (N + n)))‖
      ≤ 4 * (5 / R ^ 2 + (8 * ‖c‖ + 8) * Cdz / R) := by
    calc ‖((ContinuousLinearMap.toSpanSingleton ℂ
            ((Work.Bottcher.normFactor c (critZ c (N + n)))⁻¹)).restrictScalars ℝ).comp
            (dcnf c (critZ c (N + n)) +
              (dznf c (critZ c (N + n))).comp (dCritZ c (N + n)))‖
        ≤ ‖((ContinuousLinearMap.toSpanSingleton ℂ
            ((Work.Bottcher.normFactor c (critZ c (N + n)))⁻¹)).restrictScalars ℝ)‖ *
            ‖dcnf c (critZ c (N + n)) +
              (dznf c (critZ c (N + n))).comp (dCritZ c (N + n))‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖(Work.Bottcher.normFactor c (critZ c (N + n)))⁻¹‖ *
            ‖dcnf c (critZ c (N + n)) +
              (dznf c (critZ c (N + n))).comp (dCritZ c (N + n))‖ := by
          rw [ContinuousLinearMap.norm_restrictScalars, ContinuousLinearMap.norm_toSpanSingleton]
      _ ≤ 4 * (5 / R ^ 2 + (8 * ‖c‖ + 8) * Cdz / R) :=
          mul_le_mul hinv hnormstep (by positivity) (by norm_num)
  have hlogbound : ‖fderiv ℝ (fun w : ℂ => Complex.log
        (Work.Bottcher.normFactor w (critZ w (N + n)))) c‖
      ≤ 4 * (5 / R ^ 2 + (8 * ‖c‖ + 8) * Cdz / R) := by
    rw [hlog.fderiv]
    exact hLOGDcomp
  have hterm : (fun w : ℂ => farTerm N w n) =
      fun w : ℂ => ((1 / 4 : ℝ) ^ (n + 1) : ℂ) *
        Complex.log (Work.Bottcher.normFactor w (critZ w (N + n))) := by
    funext w
    simp only [farTerm, Work.Bottcher.bottcherTerm, pMap_iterate_critZ]
  have hF : HasFDerivAt (fun w : ℂ => farTerm N w n)
      ((((1 / 4 : ℝ) ^ (n + 1) : ℂ)) • ((((ContinuousLinearMap.toSpanSingleton ℂ
          ((Work.Bottcher.normFactor c (critZ c (N + n)))⁻¹)).restrictScalars ℝ)).comp
        (dcnf c (critZ c (N + n)) +
          (dznf c (critZ c (N + n))).comp (dCritZ c (N + n))))) c := by
    rw [hterm]
    exact hlog.const_mul _
  refine ⟨hF.differentiableAt, ?_⟩
  rw [hF.fderiv]
  calc ‖(((1 / 4 : ℝ) ^ (n + 1) : ℂ)) • ((((ContinuousLinearMap.toSpanSingleton ℂ
          ((Work.Bottcher.normFactor c (critZ c (N + n)))⁻¹)).restrictScalars ℝ)).comp
        (dcnf c (critZ c (N + n)) +
          (dznf c (critZ c (N + n))).comp (dCritZ c (N + n))))‖
      ≤ ‖(((1 / 4 : ℝ) ^ (n + 1) : ℂ))‖ * ‖((((ContinuousLinearMap.toSpanSingleton ℂ
          ((Work.Bottcher.normFactor c (critZ c (N + n)))⁻¹)).restrictScalars ℝ)).comp
        (dcnf c (critZ c (N + n)) +
          (dznf c (critZ c (N + n))).comp (dCritZ c (N + n))))‖ := norm_smul_clm_le _ _
    _ = (1 / 4 : ℝ) ^ (n + 1) * ‖((((ContinuousLinearMap.toSpanSingleton ℂ
          ((Work.Bottcher.normFactor c (critZ c (N + n)))⁻¹)).restrictScalars ℝ)).comp
        (dcnf c (critZ c (N + n)) +
          (dznf c (critZ c (N + n))).comp (dCritZ c (N + n))))‖ := by
        congr 1
        rw [norm_pow, Complex.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    _ ≤ (1 / 4 : ℝ) ^ (n + 1) * (4 * (5 / R ^ 2 + (8 * ‖c‖ + 8) * Cdz / R)) :=
        mul_le_mul_of_nonneg_left hLOGDcomp (by positivity)
    _ = (5 / R ^ 2 + (8 * ‖c‖ + 8) * Cdz / R) * (1 / 4 : ℝ) ^ n := by
        rw [pow_succ]
        ring


/-- Route: `farTerm N c n = 4^{-(n+1)} * log (normFactor c (critZ c (N+n)))`.  Its derivative is
`4^{-(n+1)} * (∂_c logNormFactor + ∂_w logNormFactor * fderiv (critZ · (N+n)) c)`, with
`∂_c logNormFactor = O(1/‖critZ‖^2)` and `∂_w logNormFactor = dnf/normFactor = O(‖c‖/‖critZ‖^3)`
(`Work.Bottcher.Core.norm_dnf_le`).  Combine the bounds `‖fderiv critZ‖ ≤ M 4^k ‖Z‖` and
`1/‖Z‖^2 ≤ M' 4^{-n}`; differentiability uses `normFactor_mem_slitPlane` and
`Complex.log` being `ℝ`-differentiable there. -/
theorem farTerm_differentiableAt_and_bound (N : ℕ) {c₀ : ℂ}
    (hfar : Work.NAKANE.farRadius (‖c₀‖ + 1) < ‖Work.NAKANE2.critZ c₀ N‖) :
    ∃ δ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ c : ℂ, ‖c - c₀‖ < δ →
      DifferentiableAt ℝ (fun w : ℂ => Work.NAKANE2.farTerm N w n) c ∧
      ‖fderiv ℝ (fun w : ℂ => Work.NAKANE2.farTerm N w n) c‖ ≤ C * (1 / 4 : ℝ) ^ n := by
  classical
  set B : ℝ := ‖c₀‖ + 1 with hBdef
  set R : ℝ := Work.NAKANE.farRadius B with hRdef
  have hfar' : R < ‖critZ c₀ N‖ := by rw [hRdef, hBdef]; exact hfar
  have hRform : R = 2 * (max 2 (1 + B)) ^ 2 + 2 := by
    rw [hRdef, hBdef]
    rfl
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hRpos : 0 < R := by rw [hRform]; positivity
  have hR10 : 10 ≤ R := by
    rw [hRform]
    have h1 : (2 : ℝ) ≤ max 2 (1 + B) := le_max_left _ _
    have h2 : (0 : ℝ) ≤ max 2 (1 + B) := by linarith
    nlinarith [sq_nonneg (max 2 (1 + B))]
  have hRB : B + 2 ≤ R := by
    rw [hRform]
    have h1 : (1 + B) ≤ max 2 (1 + B) := le_max_right _ _
    have h2 : (0 : ℝ) ≤ max 2 (1 + B) := by linarith
    nlinarith [sq_nonneg (max 2 (1 + B)), sq_nonneg (1 + B)]
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuousAt_iff.mp
    (dtbContinuous_critZ N).continuousAt (‖critZ c₀ N‖ - R) (by linarith)
  have hδ₁' : ∀ c : ℂ, ‖c - c₀‖ < δ₁ → R ≤ ‖critZ c N‖ := by
    intro c hc
    have h := hδ₁ (x := c) (by rw [dist_eq_norm]; exact hc)
    rw [dist_eq_norm] at h
    have h2 : ‖critZ c₀ N‖ ≤ ‖critZ c N - critZ c₀ N‖ + ‖critZ c N‖ := by
      have hh := norm_add_le (critZ c₀ N - critZ c N) (critZ c N)
      rw [sub_add_cancel] at hh
      rwa [norm_sub_rev] at hh
    linarith
  let bseq : ℕ → ℝ := Nat.rec B (fun _ b => (b ^ 2 + B) ^ 2 + B)
  let Aseq : ℕ → ℝ := Nat.rec 1 (fun k A => 2 * (bseq k ^ 2 + B) * (2 * bseq k * A + 1) + 1)
  have hbseq0 : bseq 0 = B := rfl
  have hbseqS : ∀ k, bseq (k + 1) = (bseq k ^ 2 + B) ^ 2 + B := fun k => rfl
  have hAseq0 : Aseq 0 = 1 := rfl
  have hAseqS : ∀ k, Aseq (k + 1) = 2 * (bseq k ^ 2 + B) * (2 * bseq k * Aseq k + 1) + 1 :=
    fun k => rfl
  have hbseqnn : ∀ k, 0 ≤ bseq k := by
    intro k
    induction k with
    | zero => rw [hbseq0]; exact hB0
    | succ k ih => rw [hbseqS]; positivity
  have hAseq1 : ∀ k, 1 ≤ Aseq k := by
    intro k
    induction k with
    | zero => rw [hAseq0]
    | succ k ih =>
      rw [hAseqS]
      have h2 : 0 ≤ 2 * bseq k * Aseq k + 1 := by nlinarith [hbseqnn k, ih]
      have h3 : 0 ≤ 2 * (bseq k ^ 2 + B) := by nlinarith [sq_nonneg (bseq k), hB0]
      nlinarith [mul_nonneg h3 h2]
  have hmain : ∀ k, (∀ c : ℂ, ‖c‖ ≤ B → ‖critZ c k‖ ≤ bseq k) ∧
      (∀ c : ℂ, ‖c‖ ≤ B → ‖critZ c k ^ 2 + (starRingEnd ℂ) c‖ ≤ bseq k ^ 2 + B) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · rw [critZ_zero, hbseq0]; exact hc
      · rw [critZ_zero, hbseq0]
        calc ‖c ^ 2 + (starRingEnd ℂ) c‖ ≤ ‖c ^ 2‖ + ‖(starRingEnd ℂ) c‖ := norm_add_le _ _
          _ = ‖c‖ ^ 2 + ‖c‖ := by rw [norm_pow, Complex.norm_conj]
          _ ≤ B ^ 2 + B := by nlinarith [hc, norm_nonneg c]
    | succ k ih =>
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · have h2 := ih.2 c hc
        have h4 := pow_le_pow_left₀ (norm_nonneg _) h2 2
        calc ‖critZ c (k + 1)‖ = ‖(critZ c k ^ 2 + (starRingEnd ℂ) c) ^ 2 + c‖ := by
              rw [critZ_succ, Work.Bottcher.pMap_apply]
          _ ≤ ‖(critZ c k ^ 2 + (starRingEnd ℂ) c) ^ 2‖ + ‖c‖ := norm_add_le _ _
          _ = ‖critZ c k ^ 2 + (starRingEnd ℂ) c‖ ^ 2 + ‖c‖ := by rw [norm_pow]
          _ ≤ (bseq k ^ 2 + B) ^ 2 + B := by linarith
          _ = bseq (k + 1) := by rw [hbseqS]
      · have hzk := ih.1 c hc
        calc ‖critZ c (k + 1) ^ 2 + (starRingEnd ℂ) c‖
            ≤ ‖critZ c (k + 1) ^ 2‖ + ‖(starRingEnd ℂ) c‖ := norm_add_le _ _
          _ = ‖critZ c (k + 1)‖ ^ 2 + ‖c‖ := by rw [norm_pow, Complex.norm_conj]
          _ ≤ bseq (k + 1) ^ 2 + B := by
              have h1 : ‖critZ c (k + 1)‖ ≤ bseq (k + 1) := by
                have h2 := ih.2 c hc
                have h4 := pow_le_pow_left₀ (norm_nonneg _) h2 2
                calc ‖critZ c (k + 1)‖ = ‖(critZ c k ^ 2 + (starRingEnd ℂ) c) ^ 2 + c‖ := by
                      rw [critZ_succ, Work.Bottcher.pMap_apply]
                  _ ≤ ‖(critZ c k ^ 2 + (starRingEnd ℂ) c) ^ 2‖ + ‖c‖ := norm_add_le _ _
                  _ = ‖critZ c k ^ 2 + (starRingEnd ℂ) c‖ ^ 2 + ‖c‖ := by rw [norm_pow]
                  _ ≤ (bseq k ^ 2 + B) ^ 2 + B := by linarith
                  _ = bseq (k + 1) := by rw [hbseqS]
              nlinarith [h1, hc, norm_nonneg (critZ c (k + 1))]
  have hcritZ_bound : ∀ k (c : ℂ), ‖c‖ ≤ B → ‖critZ c k‖ ≤ bseq k := fun k => (hmain k).1
  have hZsum : ∀ k (c : ℂ), ‖c‖ ≤ B →
      ‖critZ c k ^ 2 + (starRingEnd ℂ) c‖ ≤ bseq k ^ 2 + B := fun k => (hmain k).2
  have hdCritZ_bound : ∀ k (c : ℂ), ‖c‖ ≤ B → ‖dCritZ c k‖ ≤ Aseq k := by
    intro k
    induction k with
    | zero => intro c hc; rw [dCritZ_zero, hAseq0]; exact norm_one_clm.le
    | succ k ih =>
      intro c hc
      have hAk := ih c hc
      have hZsumk := hZsum k c hc
      have hcritZk := hcritZ_bound k c hc
      have h1 : ‖2 * (critZ c k ^ 2 + (starRingEnd ℂ) c)‖ ≤ 2 * (bseq k ^ 2 + B) := by
        rw [norm_mul]
        have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [hnorm2]
        linarith
      have h2 : ‖(2 * critZ c k) • dCritZ c k + dtbConjCLM‖ ≤ 2 * bseq k * Aseq k + 1 := by
        calc ‖(2 * critZ c k) • dCritZ c k + dtbConjCLM‖
            ≤ ‖(2 * critZ c k) • dCritZ c k‖ + ‖dtbConjCLM‖ := norm_add_le _ _
          _ ≤ ‖2 * critZ c k‖ * ‖dCritZ c k‖ + 1 := by
              rw [dtbNorm_conjCLM]
              linarith [norm_smul_clm_le (2 * critZ c k) (dCritZ c k)]
          _ ≤ 2 * bseq k * Aseq k + 1 := by
              have h5 : ‖2 * critZ c k‖ ≤ 2 * bseq k := by
                rw [norm_mul]
                have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
                rw [hnorm2]; linarith
              have h6 : (0 : ℝ) ≤ 2 * bseq k := by linarith [hbseqnn k]
              have h7 : 2 * bseq k * ‖dCritZ c k‖ ≤ 2 * bseq k * Aseq k :=
                mul_le_mul_of_nonneg_left hAk h6
              have h8 : ‖2 * critZ c k‖ * ‖dCritZ c k‖ ≤ 2 * bseq k * Aseq k :=
                (mul_le_mul_of_nonneg_right h5 (norm_nonneg _)).trans h7
              linarith
      calc ‖dCritZ c (k + 1)‖
          = ‖(2 * (critZ c k ^ 2 + (starRingEnd ℂ) c)) •
              ((2 * critZ c k) • dCritZ c k + dtbConjCLM) + 1‖ := by rw [dCritZ_succ]
        _ ≤ ‖(2 * (critZ c k ^ 2 + (starRingEnd ℂ) c)) •
              ((2 * critZ c k) • dCritZ c k + dtbConjCLM)‖ + ‖(1 : ℂ →L[ℝ] ℂ)‖ := norm_add_le _ _
        _ ≤ 2 * (bseq k ^ 2 + B) * (2 * bseq k * Aseq k + 1) + 1 := by
            rw [norm_one_clm]
            have h3 : ‖(2 * (critZ c k ^ 2 + (starRingEnd ℂ) c)) •
                ((2 * critZ c k) • dCritZ c k + dtbConjCLM)‖
                ≤ 2 * (bseq k ^ 2 + B) * (2 * bseq k * Aseq k + 1) := by
              calc ‖(2 * (critZ c k ^ 2 + (starRingEnd ℂ) c)) •
                    ((2 * critZ c k) • dCritZ c k + dtbConjCLM)‖
                  ≤ ‖2 * (critZ c k ^ 2 + (starRingEnd ℂ) c)‖ *
                      ‖(2 * critZ c k) • dCritZ c k + dtbConjCLM‖ := norm_smul_clm_le _ _
                _ ≤ 2 * (bseq k ^ 2 + B) * (2 * bseq k * Aseq k + 1) :=
                    mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
            linarith
        _ = Aseq (k + 1) := by rw [hAseqS]
  set Cdz : ℝ := max 1 (Aseq N / R ^ 2) with hCdzdef
  have hCdz0 : 0 ≤ Cdz := by rw [hCdzdef]; exact le_trans zero_le_one (le_max_left _ _)
  have hCdz1 : 1 ≤ Cdz := by rw [hCdzdef]; exact le_max_left _ _
  have hkn : Aseq N / R ^ 2 ≤ Cdz := by rw [hCdzdef]; exact le_max_right _ _
  have hcB_of : ∀ c : ℂ, ‖c - c₀‖ < 1 → ‖c‖ ≤ B := by
    intro c hc1
    have h1 : ‖c‖ ≤ ‖c - c₀‖ + ‖c₀‖ := by
      have hh := norm_add_le (c - c₀) c₀
      rw [sub_add_cancel] at hh
      exact hh
    have h2 : ‖c₀‖ + 1 = B := hBdef
    linarith
  have hgrowth : ∀ c : ℂ, ‖c - c₀‖ < min δ₁ 1 → ∀ n : ℕ,
      R ≤ ‖critZ c (N + n)‖ ∧ 1 + ‖c‖ ≤ ‖critZ c (N + n)‖ := by
    intro c hc n
    have hcδ₁ : ‖c - c₀‖ < δ₁ := lt_of_lt_of_le hc (min_le_left _ _)
    have hc1 : ‖c - c₀‖ < 1 := lt_of_lt_of_le hc (min_le_right _ _)
    have hZN : R ≤ ‖critZ c N‖ := hδ₁' c hcδ₁
    have hR2 : 2 + ‖c‖ ≤ R := by have := hcB_of c hc1; linarith
    have hstep : ∀ w : ℂ, R ≤ ‖w‖ →
        R ≤ ‖Work.Bottcher.pMap c w‖ ∧ ‖w‖ ≤ ‖Work.Bottcher.pMap c w‖ := by
      intro w hw
      have hws : 2 + ‖c‖ ≤ ‖w‖ := le_trans hR2 hw
      obtain ⟨h1, _, _⟩ := Work.Bottcher.Core.pMap_norm_step c w hws
      exact ⟨le_trans hw h1, h1⟩
    have hh := Work.Bottcher.Core.norm_iterate_pMap_ge c R hstep (critZ c N) hZN n
    rw [pMap_iterate_critZ] at hh
    have h1c : 1 + ‖c‖ ≤ R := by linarith
    exact ⟨hh.1, le_trans h1c hh.1⟩
  have hcrude : ∀ n : ℕ, ∀ c : ℂ, ‖c - c₀‖ < min δ₁ 1 →
      ‖dCritZ c (N + n)‖ ≤ Cdz * ‖critZ c (N + n)‖ ^ 2 := by
    intro n
    induction n with
    | zero =>
      intro c hc
      have hcδ₁ : ‖c - c₀‖ < δ₁ := lt_of_lt_of_le hc (min_le_left _ _)
      have hc1 : ‖c - c₀‖ < 1 := lt_of_lt_of_le hc (min_le_right _ _)
      have hcB : ‖c‖ ≤ B := hcB_of c hc1
      have hZN : R ≤ ‖critZ c N‖ := hδ₁' c hcδ₁
      have hA : ‖dCritZ c N‖ ≤ Aseq N := hdCritZ_bound N c hcB
      have hR2 : R ^ 2 ≤ ‖critZ c N‖ ^ 2 := pow_le_pow_left₀ hRpos.le hZN 2
      have hAR : (0 : ℝ) ≤ Aseq N / R ^ 2 :=
        div_nonneg (le_trans zero_le_one (hAseq1 N)) (by positivity)
      calc ‖dCritZ c N‖ ≤ Aseq N := hA
        _ = (Aseq N / R ^ 2) * R ^ 2 := by field_simp
        _ ≤ Cdz * ‖critZ c N‖ ^ 2 := by nlinarith [hkn, hR2, hAR]
    | succ n ih =>
      intro c hc
      have hgn := hgrowth c hc n
      have hDZ := ih c hc
      have hc1 : ‖c - c₀‖ < 1 := lt_of_lt_of_le hc (min_le_right _ _)
      have hcB : ‖c‖ ≤ B := hcB_of c hc1
      have h2c : 2 + ‖c‖ ≤ ‖critZ c (N + n)‖ := by linarith [hRB, hcB, hgn.1]
      have hZ4 : (4 : ℝ) ≤ ‖critZ c (N + n)‖ := by linarith [hgn.1]
      have hs : ‖c‖ ≤ ‖critZ c (N + n)‖ := by linarith [hgn.2]
      have hsucc : critZ c (N + (n + 1)) = Work.Bottcher.pMap c (critZ c (N + n)) := by
        rw [show N + (n + 1) = (N + n) + 1 by omega, critZ_succ]
      have hnorm' : ‖critZ c (N + n)‖ ^ 4 / 2 ≤ ‖critZ c (N + (n + 1))‖ := by
        rw [hsucc]
        exact (Work.Bottcher.Core.pMap_norm_step c _ h2c).2.1
      have hstep : ‖dCritZ c (N + (n + 1))‖
          ≤ 2 * (‖critZ c (N + n)‖ ^ 2 + ‖c‖) *
              (2 * ‖critZ c (N + n)‖ * (Cdz * ‖critZ c (N + n)‖ ^ 2) + 1) + 1 := by
        rw [show N + (n + 1) = (N + n) + 1 by omega, dCritZ_succ]
        calc ‖(2 * (critZ c (N + n) ^ 2 + (starRingEnd ℂ) c)) •
              ((2 * critZ c (N + n)) • dCritZ c (N + n) + dtbConjCLM) + 1‖
            ≤ ‖(2 * (critZ c (N + n) ^ 2 + (starRingEnd ℂ) c)) •
              ((2 * critZ c (N + n)) • dCritZ c (N + n) + dtbConjCLM)‖ +
              ‖(1 : ℂ →L[ℝ] ℂ)‖ := norm_add_le _ _
          _ ≤ 2 * (‖critZ c (N + n)‖ ^ 2 + ‖c‖) *
              (2 * ‖critZ c (N + n)‖ * (Cdz * ‖critZ c (N + n)‖ ^ 2) + 1) + 1 := by
              rw [norm_one_clm]
              have hX : ‖2 * (critZ c (N + n) ^ 2 + (starRingEnd ℂ) c)‖
                  ≤ 2 * (‖critZ c (N + n)‖ ^ 2 + ‖c‖) := by
                rw [norm_mul]
                have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
                rw [hnorm2]
                have hZs : ‖critZ c (N + n) ^ 2 + (starRingEnd ℂ) c‖
                    ≤ ‖critZ c (N + n)‖ ^ 2 + ‖c‖ := by
                  calc ‖critZ c (N + n) ^ 2 + (starRingEnd ℂ) c‖
                      ≤ ‖critZ c (N + n) ^ 2‖ + ‖(starRingEnd ℂ) c‖ := norm_add_le _ _
                    _ = ‖critZ c (N + n)‖ ^ 2 + ‖c‖ := by rw [norm_pow, Complex.norm_conj]
                linarith
              have hY : ‖(2 * critZ c (N + n)) • dCritZ c (N + n) + dtbConjCLM‖
                  ≤ 2 * ‖critZ c (N + n)‖ * (Cdz * ‖critZ c (N + n)‖ ^ 2) + 1 := by
                calc ‖(2 * critZ c (N + n)) • dCritZ c (N + n) + dtbConjCLM‖
                    ≤ ‖(2 * critZ c (N + n)) • dCritZ c (N + n)‖ + ‖dtbConjCLM‖ := norm_add_le _ _
                  _ ≤ ‖2 * critZ c (N + n)‖ * ‖dCritZ c (N + n)‖ + 1 := by
                      rw [dtbNorm_conjCLM]
                      linarith [norm_smul_clm_le (2 * critZ c (N + n)) (dCritZ c (N + n))]
                  _ ≤ 2 * ‖critZ c (N + n)‖ * (Cdz * ‖critZ c (N + n)‖ ^ 2) + 1 := by
                      have h5 : ‖2 * critZ c (N + n)‖ ≤ 2 * ‖critZ c (N + n)‖ := by
                        rw [norm_mul]
                        have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
                        rw [hnorm2]
                      have h6 : (0 : ℝ) ≤ 2 * ‖critZ c (N + n)‖ := by positivity
                      have h7 := mul_le_mul_of_nonneg_left hDZ h6
                      have h8 : ‖2 * critZ c (N + n)‖ * ‖dCritZ c (N + n)‖
                          ≤ 2 * ‖critZ c (N + n)‖ * (Cdz * ‖critZ c (N + n)‖ ^ 2) :=
                        (mul_le_mul_of_nonneg_right h5 (norm_nonneg _)).trans h7
                      linarith
              have h3 := norm_smul_clm_le (2 * (critZ c (N + n) ^ 2 + (starRingEnd ℂ) c))
                ((2 * critZ c (N + n)) • dCritZ c (N + n) + dtbConjCLM)
              linarith [mul_le_mul hX hY (norm_nonneg _) (by positivity)]
      have hfin : 2 * (‖critZ c (N + n)‖ ^ 2 + ‖c‖) *
              (2 * ‖critZ c (N + n)‖ * (Cdz * ‖critZ c (N + n)‖ ^ 2) + 1) + 1
          ≤ Cdz * ‖critZ c (N + (n + 1))‖ ^ 2 := by
        set t : ℝ := ‖critZ c (N + n)‖ with htdef
        have ht4 : (4 : ℝ) ≤ t := htdef ▸ hZ4
        have hts : ‖c‖ ≤ t := htdef ▸ hs
        have ht1 : (1 : ℝ) ≤ t := by linarith
        have ht8 : (8 : ℝ) ≤ t ^ 8 := by
          have h1 : (1 : ℝ) ≤ t ^ 7 := by
            have h0 : (1 : ℝ) ≤ t ^ 7 := one_le_pow₀ ht1 (n := 7)
            exact h0
          have h2 : t * 1 ≤ t * t ^ 7 := mul_le_mul_of_nonneg_left h1 (by linarith)
          have h3 : t * t ^ 7 = t ^ 8 := by ring
          linarith
        have hA2 : 2 * (t ^ 2 + ‖c‖) ≤ 4 * t ^ 2 := by nlinarith [hts, ht1, sq_nonneg t]
        have hB2 : 2 * t * (Cdz * t ^ 2) + 1 ≤ 3 * Cdz * t ^ 3 := by
          have ht3 : (1 : ℝ) ≤ t ^ 3 := by
            have h0 : (1 : ℝ) ≤ t ^ 3 := one_le_pow₀ ht1 (n := 3)
            exact h0
          have h1 : 1 ≤ Cdz * t ^ 3 := by nlinarith [hCdz1, ht3]
          nlinarith [h1]
        have h12 : 2 * (t ^ 2 + ‖c‖) * (2 * t * (Cdz * t ^ 2) + 1) + 1
            ≤ 12 * Cdz * t ^ 5 + 1 := by
          have hc' : (0 : ℝ) ≤ 2 * t * (Cdz * t ^ 2) + 1 := by positivity
          have hb' : (0 : ℝ) ≤ 4 * t ^ 2 := by positivity
          have hmid := mul_le_mul hA2 hB2 hc' hb'
          have heq : (4 * t ^ 2) * (3 * Cdz * t ^ 3) = 12 * Cdz * t ^ 5 := by ring
          linarith [hmid, heq.le]
        have h3 : 12 * Cdz * t ^ 5 ≤ Cdz * t ^ 8 / 8 := by
          have ht3 : (96 : ℝ) ≤ t ^ 3 := by nlinarith [ht4]
          have hmul := mul_le_mul_of_nonneg_left ht3 (by positivity : (0 : ℝ) ≤ Cdz * t ^ 5)
          have heq : Cdz * t ^ 5 * t ^ 3 = Cdz * t ^ 8 := by ring
          rw [heq] at hmul
          nlinarith [hmul]
        have h4 : 1 ≤ Cdz * t ^ 8 / 8 := by nlinarith [ht8, hCdz0]
        have hsq : t ^ 8 / 4 ≤ ‖critZ c (N + (n + 1))‖ ^ 2 := by
          have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ t ^ 4 / 2) (htdef ▸ hnorm') 2
          nlinarith [h]
        calc 2 * (t ^ 2 + ‖c‖) * (2 * t * (Cdz * t ^ 2) + 1) + 1
            ≤ 12 * Cdz * t ^ 5 + 1 := h12
          _ ≤ Cdz * t ^ 8 / 4 := by linarith
          _ ≤ Cdz * ‖critZ c (N + (n + 1))‖ ^ 2 := by nlinarith [hsq, hCdz0]
      exact hstep.trans hfin
  refine ⟨min δ₁ 1, lt_min hδ₁pos one_pos, 5 / R ^ 2 + (8 * B + 8) * Cdz / R, ?_, ?_⟩
  · positivity
  · intro n c hc
    have hgn := hgrowth c hc n
    have hDZ := hcrude n c hc
    have hres := norm_fderiv_farTerm_le (N := N) (n := n) (c := c) (R := R) (Cdz := Cdz)
      hRpos hCdz0 hgn.2 hgn.1 hDZ
    refine ⟨hres.1, ?_⟩
    refine hres.2.trans ?_
    have hc1 : ‖c - c₀‖ < 1 := lt_of_lt_of_le hc (min_le_right _ _)
    have hcB : ‖c‖ ≤ B := hcB_of c hc1
    have h1 : (8 * ‖c‖ + 8) ≤ (8 * B + 8) := by linarith
    have h2 : (8 * ‖c‖ + 8) * Cdz / R ≤ (8 * B + 8) * Cdz / R := by
      apply div_le_div_of_nonneg_right _ hRpos.le
      exact mul_le_mul_of_nonneg_right h1 hCdz0
    have h3 : 5 / R ^ 2 + (8 * ‖c‖ + 8) * Cdz / R ≤ 5 / R ^ 2 + (8 * B + 8) * Cdz / R :=
      by linarith
    exact mul_le_mul_of_nonneg_right h3 (by positivity)

end Work.NAKANE2.Far
