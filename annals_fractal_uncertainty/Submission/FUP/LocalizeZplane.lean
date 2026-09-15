import Submission.FUP.LocalizeLens

open MeasureTheory Metric Set Complex Filter
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The per-cell z-plane estimate (`prop:locddim`, one cell)

Assembles `Submission.FUP.cell_cartan_exp` with the change-of-variables calculus of
`Submission.FUP.LocalizeLens` into the per-cell bound
`∫_{c + η·Φ([-τ,τ]^d)} ‖F‖² ≤ C₀ · S^{2(1-κ)} · (∫_{I} ‖F‖²)^κ`.
-/

namespace Submission.FUP

variable {d : ℕ}

/-- The coordinatewise lens map sends the box `[-τ,τ]^d` onto the box `[-φ(τ),φ(τ)]^d`. -/
lemma PhiLens_image_cbox {q ε τ : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    PhiLens (d := d) q ε '' cbox d τ = cbox d (phiLens q ε τ) := by
  have hneg : phiLens q ε (-τ) = -phiLens q ε τ :=
    phiLens_neg hε0 hε1 (by rw [abs_of_nonneg hτ0]; linarith)
  have himg : phiLens q ε '' Set.Icc (-τ) τ
      = Set.Icc (phiLens q ε (-τ)) (phiLens q ε τ) :=
    image_phiLens_Icc (q := q) (ε := ε) hq hε0 hε1 (a := -τ) (b := τ)
      (by linarith) (by linarith) (by linarith)
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_cbox] at hw ⊢
    intro j
    have h2 : w j ∈ Set.Icc (-τ) τ := by rw [Set.mem_Icc, ← abs_le]; exact hw j
    have h3 : phiLens q ε (w j) ∈ phiLens q ε '' Set.Icc (-τ) τ := ⟨w j, h2, rfl⟩
    rw [himg, hneg, Set.mem_Icc] at h3
    simpa only [PhiLens] using abs_le.mpr h3
  · intro hz
    rw [mem_cbox] at hz
    choose w hw using fun j =>
      exists_phiLens_eq (q := q) (ε := ε) hq hε0 hε1 hτ0 hτ1 (hz j)
    refine ⟨w, ?_, ?_⟩
    · rw [mem_cbox]; exact fun j => abs_le.mpr (hw j).1
    · funext j; simp only [PhiLens]; exact (hw j).2

/-- The scaled per-cell lens map sends `[-τ,τ]^d` onto the box `c + [-ηφ(τ),ηφ(τ)]^d`. -/
lemma PsiR_image_cbox {q ε η τ : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hη : 0 < η) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (c : Fin d → ℝ) :
    PsiR (d := d) q ε η c '' cbox d τ
      = {y : Fin d → ℝ | ∀ j, |y j - c j| ≤ η * phiLens q ε τ} := by
  have hneg : phiLens q ε (-τ) = -phiLens q ε τ :=
    phiLens_neg hε0 hε1 (by rw [abs_of_nonneg hτ0]; linarith)
  have himg : phiLens q ε '' Set.Icc (-τ) τ
      = Set.Icc (phiLens q ε (-τ)) (phiLens q ε τ) :=
    image_phiLens_Icc (q := q) (ε := ε) hq hε0 hε1 (a := -τ) (b := τ)
      (by linarith) (by linarith) (by linarith)
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_cbox] at hw
    intro j
    have h2 : w j ∈ Set.Icc (-τ) τ := by rw [Set.mem_Icc, ← abs_le]; exact hw j
    have h3 : phiLens q ε (w j) ∈ phiLens q ε '' Set.Icc (-τ) τ := ⟨w j, h2, rfl⟩
    rw [himg, hneg, Set.mem_Icc] at h3
    have h4 : |phiLens q ε (w j)| ≤ phiLens q ε τ := abs_le.mpr h3
    simp only [PsiR]
    rw [show c j + η * phiLens q ε (w j) - c j = η * phiLens q ε (w j) by ring,
      abs_mul, abs_of_pos hη]
    exact mul_le_mul_of_nonneg_left h4 (le_of_lt hη)
  · intro hy
    have hz : ∀ j, |(y j - c j) / η| ≤ phiLens q ε τ := by
      intro j
      rw [abs_div, abs_of_pos hη, div_le_iff₀ hη]
      exact le_trans (hy j) (le_of_eq (mul_comm _ _))
    choose w hw using fun j =>
      exists_phiLens_eq (q := q) (ε := ε) hq hε0 hε1 hτ0 hτ1 (hz j)
    refine ⟨w, ?_, ?_⟩
    · rw [mem_cbox]; exact fun j => abs_le.mpr (hw j).1
    · funext j
      have h2 := (hw j).2
      have h3 : c j + η * ((y j - c j) / η) = y j := by field_simp; ring
      simp only [PsiR]
      rw [h2]
      exact h3

/-! ## Volumes of the boxes, measurability of the lens map -/

lemma volume_cbox_eq (d : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    volume (cbox d c) = ENNReal.ofReal ((2*c)^d) := by
  rw [cbox, Set.pi_univ_Icc (x := fun _ : Fin d => -c) (y := fun _ : Fin d => c),
    Real.volume_Icc_pi]
  have hprod : ∏ i : Fin d, ENNReal.ofReal (c - -c) = (ENNReal.ofReal (2*c)) ^ d := by
    rw [Finset.prod_congr rfl (fun i _ => by
        rw [show c - -c = 2*c from by ring]),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod, ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ 2*c)]

lemma measurable_phiLens (q ε : ℝ) : Measurable (phiLens q ε) := by
  rw [show phiLens q ε = fun x : ℝ =>
      (2*q/Real.pi) * Real.log ((1 + (1-ε) * x) / (1 - (1-ε) * x)) from rfl]
  exact measurable_const.mul (Real.measurable_log.comp (by fun_prop))

lemma volume_Icube (l : Fin d → ℝ) {c₁ : ℝ} (hc₁ : 0 ≤ c₁) :
    volume (Set.pi Set.univ (fun j => Set.Icc (l j - c₁) (l j + c₁)))
      = ENNReal.ofReal ((2*c₁)^d) := by
  rw [Set.pi_univ_Icc (x := fun j : Fin d => l j - c₁) (y := fun j : Fin d => l j + c₁),
    Real.volume_Icc_pi]
  have hprod : ∏ i : Fin d, ENNReal.ofReal (l i + c₁ - (l i - c₁))
      = (ENNReal.ofReal (2*c₁)) ^ d := by
    rw [Finset.prod_congr rfl (fun i _ => by
        rw [show l i + c₁ - (l i - c₁) = 2*c₁ from by ring]),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod, ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ 2*c₁)]

lemma phiLens_pos_of_pos {q ε x : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hx0 : 0 < x) (hx1 : x < 1) : 0 < phiLens q ε x := by
  have h := phiLens_strictMonoOn hq hε0 hε1 (show (0:ℝ) ∈ Set.Icc (-1) 1 by
      rw [Set.mem_Icc]; norm_num) (show x ∈ Set.Icc (-1:ℝ) 1 by
      rw [Set.mem_Icc]; exact ⟨by linarith, le_of_lt hx1⟩) hx0
  rwa [phiLens_zero] at h

/-! ## The mean-square functional: elementary lemmas -/

lemma meanSq_congr {S : Set (Fin d → ℝ)} {f g : (Fin d → ℝ) → ℝ}
    (hS : MeasurableSet S) (h : ∀ x ∈ S, f x = g x) : meanSq d S f = meanSq d S g := by
  rw [meanSq, meanSq, setIntegral_congr_fun hS (fun x hx => h x hx)]

lemma meanSq_const_mul {S : Set (Fin d → ℝ)} (c : ℝ) (f : (Fin d → ℝ) → ℝ) :
    meanSq d S (fun x => c * f x) = c * meanSq d S f := by
  rw [meanSq, meanSq, integral_const_mul]; ring

lemma vol_mul_meanSq {S : Set (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ}
    (h : (volume S).toReal ≠ 0) :
    (volume S).toReal * meanSq d S f = ∫ x in S, f x := by
  rw [meanSq]; field_simp

lemma meanSq_le_of_le {S : Set (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ} {c : ℝ}
    (hS : MeasurableSet S) (hSne : (volume S).toReal ≠ 0) (hSfin : volume S ≠ ⊤)
    (hint : IntegrableOn f S volume) (h : ∀ x ∈ S, f x ≤ c) :
    meanSq d S f ≤ c := by
  have hconst : IntegrableOn (fun _ : Fin d → ℝ => c) S volume :=
    integrableOn_const (α := Fin d → ℝ) (μ := volume) (s := S) (C := c) hSfin
  have h1 : ∫ x in S, f x ≤ c * (volume S).toReal := by
    calc ∫ x in S, f x ≤ ∫ _x in S, c :=
          setIntegral_mono_on hint hconst hS h
      _ = volume.real S • c := setIntegral_const c
      _ = c * (volume S).toReal := by
          rw [Measure.real_def, smul_eq_mul, mul_comm]
  have h2 : ((volume S).toReal)⁻¹ * (c * (volume S).toReal) = c := by
    field_simp
  rw [meanSq]
  calc ((volume S).toReal)⁻¹ * ∫ x in S, f x
      ≤ ((volume S).toReal)⁻¹ * (c * (volume S).toReal) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ = c := h2

/-- Continuity of `w ↦ G (c + η·Φ(w))` on the box `[-τ,τ]^d`. -/
lemma continuousOn_psiR_comp {q ε η τ : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hτ1 : τ < 1) {c : Fin d → ℝ} {G : (Fin d → ℂ) → ℝ} (hG : Continuous G) :
    ContinuousOn (fun w : Fin d → ℝ => G (fun j => ((PsiR q ε η c w j : ℝ) : ℂ)))
      (cbox d τ) := by
  have h1 : ContinuousOn (fun w : Fin d → ℝ => fun j => phiLens q ε (w j)) (cbox d τ) := by
    rw [continuousOn_pi]
    intro j
    refine ContinuousOn.comp (g := phiLens q ε) (t := Set.Icc (-τ) τ)
      (continuousOn_phiLens hq hε0 hε1 (a := -τ) (b := τ)
        (by linarith) (by linarith)) (continuous_apply j).continuousOn ?_
    intro w hw
    rw [mem_cbox] at hw
    rw [Set.mem_Icc, ← abs_le]
    exact hw j
  have h2 : ContinuousOn (fun w : Fin d → ℝ =>
      fun j => ((c j + η * phiLens q ε (w j) : ℝ) : ℂ)) (cbox d τ) := by
    rw [continuousOn_pi]
    intro j
    have hj := (continuousOn_pi.mp h1) j
    have h3 : ContinuousOn (fun w : Fin d → ℝ => (c j + η * phiLens q ε (w j) : ℝ)) (cbox d τ) :=
      (hj.const_mul η).const_add (c j)
    exact Complex.continuous_ofReal.comp_continuousOn h3
  exact hG.comp_continuousOn h2

/-- The real-algebra step of the per-cell Cartan estimate. -/
lemma zplane_cartan_algebra {κ S M B : ℝ} (hS : 0 < S) (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (h : (S^2)⁻¹ * M ≤ (2 * ((S⁻¹)^2 * B))^κ) :
    M ≤ (2:ℝ)^κ * S ^ (2 - 2*κ) * B^κ := by
  have hS2 : (0:ℝ) < S^2 := by positivity
  have h2 : (2 * ((S⁻¹)^2 * B))^κ = (2:ℝ)^κ * ((S⁻¹)^2 * B)^κ :=
    Real.mul_rpow (by norm_num) (by positivity)
  have h3 : ((S⁻¹)^2 * B)^κ = ((S⁻¹)^2)^κ * B^κ := Real.mul_rpow (by positivity) hB
  have h4 : ((S⁻¹)^2)^κ = S^(-(2*κ)) := by
    rw [show (S⁻¹)^2 = (S⁻¹)^(2:ℝ) from (Real.rpow_natCast S⁻¹ 2).symm,
      ← Real.rpow_mul (by positivity : (0:ℝ) ≤ S⁻¹) 2 κ, Real.inv_rpow hS.le (2*κ),
      ← Real.rpow_neg hS.le (2*κ)]
  have h' : (S^2)⁻¹ * M ≤ (2:ℝ)^κ * S^(-(2*κ)) * B^κ := by
    rw [h2, h3, h4] at h
    simpa only [mul_assoc] using h
  calc M = S^2 * ((S^2)⁻¹ * M) := by field_simp
    _ ≤ S^2 * ((2:ℝ)^κ * S^(-(2*κ)) * B^κ) := mul_le_mul_of_nonneg_left h' (by positivity)
    _ = (2:ℝ)^κ * S ^ (2 - 2*κ) * B^κ := by
        have hcomb : S^((2:ℕ):ℝ) * S^(-(2*κ)) = S^(2 - 2*κ) := by
          rw [← Real.rpow_add hS]
          congr 1
        rw [show (S:ℝ)^2 = S^((2:ℕ):ℝ) from (Real.rpow_natCast S 2).symm,
          show S^((2:ℕ):ℝ) * ((2:ℝ)^κ * S^(-(2*κ)) * B^κ)
              = (2:ℝ)^κ * (S^((2:ℕ):ℝ) * S^(-(2*κ))) * B^κ from by ring,
          hcomb]

end Submission.FUP

namespace Submission.FUP

variable {d : ℕ}

/-- The distortion constants of the lens map. -/
noncomputable def zpLamMax (q ε : ℝ) : ℝ := 4*q/(Real.pi*ε)
noncomputable def zpLamMin (q ε : ℝ) : ℝ := (1-ε)*q/Real.pi

/-- The interpolation exponent `κ` of the per-cell estimate. -/
noncomputable def zpKappa (δ H : ℝ) (d : ℕ) : ℝ := twoConstKappa δ H ^ d

/-- The pure constant of the per-cell z-plane estimate. -/
noncomputable def cellZConst (q ε δ H η c₁ : ℝ) (d : ℕ) : ℝ :=
  (η * zpLamMax q ε)^d * (2*(1-3*δ))^d * (2:ℝ) ^ zpKappa δ H d
    * ((η * zpLamMin q ε) ^ (-(d:ℝ)) * (η * zpLamMax q ε)^d / (2*c₁)^d)
        ^ zpKappa δ H d

lemma measurable_det_dPsiR (q ε η : ℝ) (c : Fin d → ℝ) :
    Measurable (fun w : Fin d → ℝ => (dPsiR (d := d) q ε η c w).det) := by
  rw [show (fun w : Fin d → ℝ => (dPsiR (d := d) q ε η c w).det)
      = fun w => η^d * ∏ j : Fin d,
          ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(w j))^2))) from
    funext fun w => det_dPsiR q ε η c w]
  refine measurable_const.mul ?_
  refine Finset.measurable_prod _ (fun j _ => ?_)
  fun_prop

lemma cellZConst_pos (q ε δ H η c₁ : ℝ) (d : ℕ) (hδ0 : 0 < δ) (hδ3 : δ < 1/3)
    (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1/2) (hη0 : 0 < η) (hc₁ : 0 < c₁) :
    0 < cellZConst q ε δ H η c₁ d := by
  rw [cellZConst]
  have h1 : (0:ℝ) < 2*(1-3*δ) := by linarith
  have h2 : (0:ℝ) < 1 - ε := by linarith
  have h3 : (0:ℝ) < zpLamMax q ε := by
    rw [zpLamMax]; exact div_pos (mul_pos (by norm_num) hq) (mul_pos Real.pi_pos hε0)
  have h4 : (0:ℝ) < zpLamMin q ε := by
    rw [zpLamMin]; exact div_pos (mul_pos h2 hq) Real.pi_pos
  have hη1 : (0:ℝ) < η * zpLamMax q ε := mul_pos hη0 h3
  have hη2 : (0:ℝ) < η * zpLamMin q ε := mul_pos hη0 h4
  have h5 : (0:ℝ) < (η * zpLamMin q ε) ^ (-(d:ℝ)) * (η * zpLamMax q ε)^d / (2*c₁)^d :=
    div_pos (mul_pos (Real.rpow_pos_of_pos hη2 _) (pow_pos hη1 d))
      (pow_pos (by linarith : (0:ℝ) < 2*c₁) d)
  exact mul_pos (mul_pos (mul_pos (pow_pos hη1 d) (pow_pos h1 d))
    (Real.rpow_pos_of_pos (by norm_num) _)) (Real.rpow_pos_of_pos h5 _)

end Submission.FUP

namespace Submission.FUP

variable {d : ℕ}

/-- **The per-cell z-plane estimate** (Han–Schlag `prop:locddim`, one cell). -/
theorem cell_zplane {q ε δ H η : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1/2)
    (hδ0 : 0 < δ) (hδ3 : δ < 1/3) (hH0 : 0 < H) (hH1 : H ≤ 1)
    (hη0 : 0 < η) (hηφ : 1 ≤ η * phiLens q ε (1 - 3*δ))
    (d : ℕ) (hd : 1 ≤ d) {F : (Fin d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ)
    {c l : Fin d → ℝ} {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hl : ∀ j, |l j - c j| ≤ 1 - c₁)
    (hbig : ENNReal.ofReal ((η * zpLamMax q ε)^d * (2 * (20^d * H)))
      ≤ volume (Set.pi Set.univ (fun j => Set.Icc (l j - c₁) (l j + c₁)))) :
    ∫ y in PsiR (d := d) q ε η c '' cbox d (1 - 3*δ), ‖F (fun j => (y j : ℂ))‖^2
      ≤ cellZConst q ε δ H η c₁ d
        * (sSup ((fun z : Fin d → ℂ => ‖F (PsiCLens q ε η c z)‖) '' Metric.closedBall 0 1))
            ^ (2 * (1 - zpKappa δ H d))
        * (∫ y in Set.pi Set.univ (fun j => Set.Icc (l j - c₁) (l j + c₁)),
            ‖F (fun j => (y j : ℂ))‖^2) ^ (zpKappa δ H d) := by
  classical
  have hε1' : ε < 1 := by linarith
  have hτ0 : 0 ≤ 1 - 3*δ := by linarith
  have hτ1 : 1 - 3*δ < 1 := by linarith
  have hτpos : 0 < 1 - 3*δ := by linarith
  have hηφ' : 1/η ≤ phiLens q ε (1 - 3*δ) := by
    rw [div_le_iff₀ hη0]; linarith [hηφ]
  have hlamxpos : 0 < zpLamMax q ε := by
    rw [zpLamMax]
    exact div_pos (mul_pos (by norm_num) hq) (mul_pos Real.pi_pos hε0)
  have hlaminpos : 0 < zpLamMin q ε := by
    rw [zpLamMin]
    exact div_pos (mul_pos (by linarith : (0:ℝ) < 1 - ε) hq) Real.pi_pos
  obtain ⟨hκ0, hκ1⟩ := twoConstKappa_mem hδ0 hδ3 hH0 hH1
  have hκd0 : 0 < twoConstKappa δ H ^ d := pow_pos hκ0 d
  have htwoKpos : 0 < twoConstK δ H := by
    rw [twoConstK]
    have h1 : 0 < 2 * δ⁻¹ ^ 3 * Real.log (2 / δ) := by
      have := Real.log_pos (show (1:ℝ) < 2/δ by rw [one_lt_div hδ0]; linarith)
      positivity
    have h2 : 0 ≤ δ⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / H) := by
      have hlog : 0 ≤ Real.log (2 * Real.exp 1 / H) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ hH0]
        nlinarith [Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)]
      positivity
    linarith
  have hκdlt1 : twoConstKappa δ H ^ d < 1 :=
    pow_lt_one₀ (le_of_lt hκ0)
      (by rw [twoConstKappa]; exact inv_lt_one_of_one_lt₀ (by linarith)) (by omega)
  have hκexpo : 2 * (1 - zpKappa δ H d) ≠ 0 := by
    rw [zpKappa]
    have : 1 - twoConstKappa δ H ^ d ≠ 0 := by linarith
    positivity
  -- the two boxes
  set mid : Set (Fin d → ℝ) := cbox d (1 - 3*δ) with hmiddef
  have hvolmid : volume mid = ENNReal.ofReal ((2*(1 - 3*δ))^d) := by
    rw [hmiddef]; exact volume_cbox_eq d (by linarith)
  have hmidlt : volume mid < ⊤ := by rw [hvolmid]; exact ENNReal.ofReal_lt_top
  have hmidfin : volume mid ≠ ⊤ := ne_of_lt hmidlt
  have hvolmidre : (volume mid).toReal = (2*(1 - 3*δ))^d := by
    rw [hvolmid, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (2*(1-3*δ))^d)]
  have hmidpos : 0 < (volume mid).toReal := by rw [hvolmidre]; positivity
  set Icube : Set (Fin d → ℝ) := Set.pi Set.univ (fun j => Set.Icc (l j - c₁) (l j + c₁))
    with hIdef
  have hIvol : volume Icube = ENNReal.ofReal ((2*c₁)^d) := by
    rw [hIdef]; exact volume_Icube l (le_of_lt hc₁)
  set S : ℝ := sSup ((fun z : Fin d → ℂ => ‖F (PsiCLens q ε η c z)‖) '' Metric.closedBall 0 1)
    with hSdef
  set A : ℝ := ∫ y in Icube, ‖F (fun j => (y j : ℂ))‖^2 with hAdef
  have hFcont : Continuous F := continuousOn_univ.mp hF.continuousOn
  have hcontPsiC : ContinuousOn (fun z : Fin d → ℂ => F (PsiCLens q ε η c z))
      (Metric.closedBall 0 1) := (analyticOnNhd_PsiC_comp (d := d) hε0 hε1' hF c).continuousOn
  have hbddS : BddAbove ((fun z : Fin d → ℂ => ‖F (PsiCLens q ε η c z)‖) '' Metric.closedBall 0 1) :=
    (isCompact_closedBall (0 : Fin d → ℂ) 1).bddAbove_image hcontPsiC.norm
  have hSle : ∀ z : Fin d → ℂ, z ∈ Metric.closedBall 0 1 → ‖F (PsiCLens q ε η c z)‖ ≤ S :=
    fun z hz => le_csSup hbddS ⟨z, hz, rfl⟩
  have hSb : ∀ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 1) → ‖F (PsiCLens q ε η c z)‖ ≤ S := by
    intro z hz
    refine hSle z ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
    exact hz
  have hSnn : 0 ≤ S := le_trans (norm_nonneg _) (hSle 0 (Metric.mem_closedBall_self (by norm_num)))
  -- (i) the upper change of variables on the mid box
  have hfr_cont : ContinuousOn (fun w : Fin d → ℝ =>
      ‖F (fun j => (PsiR q ε η c w j : ℂ))‖^2) (cbox d (1 - 3*δ)) :=
    continuousOn_psiR_comp (d := d) hq hε0 hε1' hτ1 (c := c)
      (G := fun z : Fin d → ℂ => ‖F z‖^2) ((hFcont.norm).pow 2)
  have hI1 : ∫ y in PsiR (d := d) q ε η c '' cbox d (1 - 3*δ), ‖F (fun j => (y j : ℂ))‖^2
      ≤ (η * zpLamMax q ε)^d * ∫ w in cbox d (1 - 3*δ),
          ‖F (fun j => (PsiR q ε η c w j : ℂ))‖^2 := by
    have h := integral_image_PsiR_le (d := d) hq hε0 hε1 hη0
      (E := cbox d (1 - 3*δ)) (measurableSet_cbox d _)
      (fun x hx j _ => by
        rw [mem_cbox] at hx
        have h2 := abs_le.mp (hx j)
        rw [Set.mem_Ioo]
        exact ⟨by linarith [h2.1], by linarith [h2.2]⟩)
      (G := fun y : Fin d → ℝ => ‖F (fun j => (y j : ℂ))‖^2) (fun y => by positivity)
      (hfr_cont.integrableOn_compact (isCompact_cbox d _))
    simpa only [zpLamMax] using h
  rcases eq_or_lt_of_le hSnn with hS0 | hSpos
  · have hFz : ∀ w : Fin d → ℝ, w ∈ mid →
        F (fun j => (PsiR q ε η c w j : ℂ)) = 0 := by
      intro w hw
      have hwlt : ∀ j, |w j| < 1 := by
        intro j
        rw [hmiddef, mem_cbox] at hw
        exact lt_of_le_of_lt (hw j) hτ1
      have h1 : ‖F (PsiCLens q ε η c (fun j => (w j : ℂ)))‖ ≤ 0 := by
        have h2 := hSb (fun j => (w j : ℂ)) (fun j => by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact le_of_lt (hwlt j))
        simpa [hS0.symm] using h2
      rw [PsiC_ofReal hε0 (le_of_lt hε1') hwlt] at h1
      exact norm_eq_zero.mp (le_antisymm h1 (norm_nonneg _))
    have hzero : ∫ w in mid, ‖F (fun j => (PsiR q ε η c w j : ℂ))‖^2 = 0 := by
      have h1 : ∫ w in mid, ‖F (fun j => (PsiR q ε η c w j : ℂ))‖^2
          = ∫ _w in mid, (0:ℝ) :=
        setIntegral_congr_fun (by rw [hmiddef]; exact measurableSet_cbox d (1-3*δ))
          (fun w hw => by rw [hFz w hw]; simp)
      rw [h1, integral_zero]
    have hLHS0 : ∫ y in PsiR (d := d) q ε η c '' mid, ‖F (fun j => (y j : ℂ))‖^2 = 0 := by
      have hnn : 0 ≤ ∫ y in PsiR (d := d) q ε η c '' mid, ‖F (fun j => (y j : ℂ))‖^2 :=
        integral_nonneg (fun y => by positivity)
      have h := hI1
      rw [← hmiddef, hzero, mul_zero] at h
      linarith
    rw [hLHS0]
    have hzero_pow : S ^ (2 * (1 - zpKappa δ H d)) = 0 := by
      rw [hS0.symm]; exact Real.zero_rpow hκexpo
    rw [hzero_pow, mul_comm (cellZConst q ε δ H η c₁ d), zero_mul]
    simp
  · -- S > 0
    set E0 : Set (Fin d → ℝ) := (fun z : Fin d → ℝ => c + η • z) ⁻¹' Icube with hE0def
    set E : Set (Fin d → ℝ) :=
      (fun w : Fin d → ℝ => fun j => phiLens q ε (w j)) ⁻¹' E0 ∩ mid with hEdef
    set fr : (Fin d → ℝ) → ℝ :=
      fun w => ‖F (fun j => (PsiR q ε η c w j : ℂ))‖^2 with hfrdef
    set f0 : (Fin d → ℝ) → ℝ :=
      fun w => ‖((S⁻¹:ℝ):ℂ) * F (fun j => (PsiR q ε η c w j : ℂ))‖^2 with hf0def
    set B : ℝ := meanSq d E fr with hBdef
    set Mmid : ℝ := meanSq d mid fr with hMmiddef
    have hfr_eq : fr = fun w => S^2 * f0 w := by
      funext w
      have h1 : f0 w = (S⁻¹)^2 * fr w := by
        simp only [hf0def, hfrdef]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [h1, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hSpos), one_pow, one_mul]
    have hfr_int_mid : IntegrableOn fr mid volume := by
      rw [hmiddef]
      exact hfr_cont.integrableOn_compact (isCompact_cbox d (1 - 3*δ))
    -- ### The localisation cube preimage
    have hEeq : E = {w : Fin d → ℝ | ∀ j, l j - c₁ ≤ c j + η * phiLens q ε (w j) ∧
        c j + η * phiLens q ε (w j) ≤ l j + c₁} ∩ mid := by
      rw [hEdef, hE0def, hIdef, hmiddef]
      ext w
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_Icc, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Set.mem_setOf_eq, PhiLens]
    have hEmeas : MeasurableSet E := by
      rw [hEeq]
      refine MeasurableSet.inter ?_ (by rw [hmiddef]; exact measurableSet_cbox d (1-3*δ))
      rw [Set.ofPred_forall]
      refine MeasurableSet.iInter (fun j => MeasurableSet.inter ?_ ?_)
      · exact measurableSet_le measurable_const (measurable_const.add (measurable_const.mul
          ((measurable_phiLens q ε).comp (measurable_pi_apply j))))
      · exact measurableSet_le (measurable_const.add (measurable_const.mul
          ((measurable_phiLens q ε).comp (measurable_pi_apply j)))) measurable_const
    have hEsub_mid : E ⊆ mid := by rw [hEdef]; exact Set.inter_subset_right
    have hEfin : volume E ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono hEsub_mid) hmidlt)
    have hEsub_open : E ⊆ Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-1:ℝ) 1) := by
      intro w hw j _
      have h1 : |w j| ≤ 1 - 3*δ := by
        have h2 := hEsub_mid hw
        rw [hmiddef, mem_cbox] at h2
        exact h2 j
      have h2 := abs_le.mp h1
      rw [Set.mem_Ioo]
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    have hEint : IntegrableOn fr E volume := hfr_int_mid.mono_set hEsub_mid
    have hltE : ∀ w ∈ E, ∀ j, |w j| < 1 := by
      intro w hw j
      have h2 := hEsub_mid hw
      rw [hmiddef, mem_cbox] at h2
      exact lt_of_le_of_lt (h2 j) hτ1
    have hE0mem : ∀ z ∈ E0, ∀ j, l j - c₁ ≤ c j + η * z j ∧ c j + η * z j ≤ l j + c₁ := by
      intro z hz j
      have h2 : (c + η • z) ∈ Icube := hz
      rw [hIdef] at h2
      have h3 := h2 j (Set.mem_univ j)
      simpa only [Set.mem_Icc, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h3
    have hE0sub : E0 ⊆ cbox d (phiLens q ε (1 - 3*δ)) := by
      intro z hz
      rw [mem_cbox]
      intro j
      obtain ⟨h1, h2⟩ := hE0mem z hz j
      obtain ⟨ha, hb⟩ := abs_le.mp (hl j)
      have h3 : -(1:ℝ) ≤ η * z j ∧ η * z j ≤ 1 := by
        constructor
        · linarith [ha, h1]
        · linarith [hb, h2]
      have h4 : |η * z j| ≤ 1 := abs_le.mpr h3
      rw [abs_mul, abs_of_pos hη0] at h4
      have h5 : |z j| ≤ 1/η := by rw [le_div_iff₀ hη0]; linarith
      exact le_trans h5 hηφ'
    have hE01 : (fun w : Fin d → ℝ => fun j => phiLens q ε (w j)) '' E = E0 := by
      have hmid_img :
          (fun w : Fin d → ℝ => fun j => phiLens q ε (w j)) '' mid
            = cbox d (phiLens q ε (1 - 3*δ)) := by
        rw [hmiddef]
        exact PhiLens_image_cbox hq hε0 hε1' hτ0 hτ1
      rw [hEdef]
      ext z
      constructor
      · rintro ⟨w, ⟨hw1, _⟩, rfl⟩
        exact hw1
      · intro hz
        obtain ⟨w, hwm, hwz⟩ :=
          (show z ∈ (fun w : Fin d → ℝ => fun j => phiLens q ε (w j)) '' mid
            from by rw [hmid_img]; exact hE0sub hz)
        refine ⟨w, ⟨?_, hwm⟩, hwz⟩
        simp only [Set.mem_preimage]
        have h2 : (fun j => phiLens q ε (w j)) = z := hwz
        rw [h2]; exact hz
    have hPE : PsiR (d := d) q ε η c '' E = Icube := by
      have hcomp : PsiR (d := d) q ε η c '' E
          = (fun z : Fin d → ℝ => c + η • z)
              '' ((fun w : Fin d → ℝ => fun j => phiLens q ε (w j)) '' E) := by
        rw [Set.image_image]
        rfl
      rw [hcomp, hE01]
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩; exact hz
      · intro hy
        have hcy : c + η • (η⁻¹ • (y - c)) = y := by
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hη0), one_smul]
          abel
        exact ⟨η⁻¹ • (y - c), by show c + η • (η⁻¹ • (y - c)) ∈ Icube; rw [hcy]; exact hy, hcy⟩
    have hE0vol : volume E0 = ENNReal.ofReal ((2*c₁/η)^d) := by
      have hbox : E0 = Set.pi Set.univ
          (fun j => Set.Icc ((l j - c₁ - c j)/η) ((l j + c₁ - c j)/η)) := by
        rw [hE0def, hIdef]
        ext z
        simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
          Pi.smul_apply, smul_eq_mul, Pi.add_apply]
        constructor
        · intro h j
          obtain ⟨h1, h2⟩ := h j
          exact ⟨by rw [div_le_iff₀ hη0]; linarith, by rw [le_div_iff₀ hη0]; linarith⟩
        · intro h j
          obtain ⟨h1, h2⟩ := h j
          exact ⟨by have := (div_le_iff₀ hη0).mp h1; linarith,
                 by have := (le_div_iff₀ hη0).mp h2; linarith⟩
      rw [hbox, Set.pi_univ_Icc (x := fun j : Fin d => (l j - c₁ - c j)/η)
          (y := fun j : Fin d => (l j + c₁ - c j)/η), Real.volume_Icc_pi]
      have hprod : ∏ j : Fin d, ENNReal.ofReal ((l j + c₁ - c j)/η - (l j - c₁ - c j)/η)
          = (ENNReal.ofReal (2*c₁/η)) ^ d := by
        rw [Finset.prod_congr rfl (fun j _ => by
            rw [show (l j + c₁ - c j)/η - (l j - c₁ - c j)/η = 2*c₁/η from by
              field_simp; ring]),
          Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [hprod, ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ 2*c₁/η)]
    have hEvolre : (2*c₁/η)^d / (zpLamMax q ε)^d ≤ (volume E).toReal := by
      have h1 : volume ((fun y : Fin d → ℝ => fun j => phiLens q ε (y j)) '' E)
          ≤ ENNReal.ofReal ((zpLamMax q ε)^d) * volume E := by
        have h := volume_image_PhiLens_le_set (d := d) hq hε0 hε1 hEmeas hEsub_open
        simpa only [zpLamMax] using h
      rw [hE01, hE0vol] at h1
      have h2 : (2*c₁/η)^d ≤ (zpLamMax q ε)^d * (volume E).toReal := by
        have h3 := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEfin)).mpr h1
        rwa [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (2*c₁/η)^d),
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (zpLamMax q ε)^d)]
          at h3
      rw [div_le_iff₀ (pow_pos hlamxpos d)]
      linarith [h2]
    have hJbig2 : (η * zpLamMax q ε)^d * (2 * (20^d * H)) ≤ (2*c₁)^d := by
      have h2 : ENNReal.ofReal ((η * zpLamMax q ε)^d * (2 * (20^d * H)))
          ≤ ENNReal.ofReal ((2*c₁)^d) := by
        rw [← hIvol]; exact hbig
      have h3 := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top).mpr h2
      rwa [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at h3
    have hJbig : ENNReal.ofReal (2 * (20^d * H)) ≤ volume E := by
      have hetal : (0:ℝ) < (η * zpLamMax q ε)^d := by positivity
      have h4 : 2 * (20^d * H) ≤ (2*c₁)^d / (η * zpLamMax q ε)^d := by
        rw [le_div_iff₀ hetal]; linarith [hJbig2]
      have h5 : (2*c₁)^d / (η * zpLamMax q ε)^d = (2*c₁/η)^d / (zpLamMax q ε)^d := by
        rw [mul_pow, div_pow]
        ring
      have h6 : 2 * (20^d * H) ≤ (volume E).toReal := by
        rw [h5] at h4; linarith [h4, hEvolre]
      calc ENNReal.ofReal (2 * (20^d * H)) ≤ ENNReal.ofReal ((volume E).toReal) :=
            ENNReal.ofReal_le_ofReal h6
        _ = volume E := ENNReal.ofReal_toReal hEfin
    -- ### (ii) the lower change of variables on the localisation cube
    have hdetb : ∀ w ∈ E, |(dPsiR (d := d) q ε η c w).det| ≤ (η * zpLamMax q ε)^d := by
      intro w hw
      have hc : ∀ j : Fin d, 0 ≤ (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(w j))^2)) :=
        fun j => le_of_lt (phiLens_deriv_pos hq hε0 hε1' (hltE w hw j))
      have hc' : ∀ j : Fin d,
          (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(w j))^2)) ≤ 4*q/(Real.pi*ε) :=
        fun j => (phiLens_deriv_bounds hq hε0 hε1 (hltE w hw j)).2
      have hprod : (∏ j : Fin d, ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(w j))^2))))
          ≤ (4*q/(Real.pi*ε))^d := by
        calc (∏ j : Fin d, ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(w j))^2))))
            ≤ ∏ _j : Fin d, (4*q/(Real.pi*ε)) :=
              Finset.prod_le_prod (fun j _ => hc j) (fun j _ => hc' j)
          _ = (4*q/(Real.pi*ε))^d := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [det_dPsiR, abs_of_nonneg (mul_nonneg (by positivity)
        (Finset.prod_nonneg (fun j _ => hc j)))]
      calc η^d * (∏ j : Fin d, ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*(w j))^2))))
          ≤ η^d * (4*q/(Real.pi*ε))^d := mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = (η * (4*q/(Real.pi*ε)))^d := by rw [mul_pow]
        _ = (η * zpLamMax q ε)^d := by rw [zpLamMax]
    have hdet_int : IntegrableOn (fun w : Fin d → ℝ =>
        |(dPsiR (d := d) q ε η c w).det| • fr w) E volume := by
      have hdom : IntegrableOn (fun w : Fin d → ℝ => (η * zpLamMax q ε)^d * fr w) E volume :=
        hEint.const_mul _
      refine hdom.mono' ?_ ?_
      · exact ((measurable_det_dPsiR (d := d) q ε η c).abs.aestronglyMeasurable).smul
          hEint.aestronglyMeasurable
      · filter_upwards [ae_restrict_of_forall_mem hEmeas (fun w hw => hdetb w hw)] with w hw
        rw [Real.norm_of_nonneg (by positivity), smul_eq_mul]
        exact mul_le_mul_of_nonneg_right hw (by positivity)
    have hIntEge : (η * zpLamMin q ε)^d * ∫ w in E, fr w ≤ A := by
      have h := integral_image_PsiR_ge (d := d) hq hε0 hε1 hη0 (E := E) hEmeas hEsub_open
        (G := fun y : Fin d → ℝ => ‖F (fun j => (y j : ℂ))‖^2) (fun y => by positivity)
        hdet_int hEint
      rw [hPE] at h
      rw [show (η * ((1-ε)*q/Real.pi))^d = (η * zpLamMin q ε)^d from by rw [zpLamMin]] at h
      simpa only [hAdef] using h
    have hEpos : 0 < (volume E).toReal := by
      have h1 : 0 < (2*c₁/η)^d / (zpLamMax q ε)^d := by positivity
      linarith [hEvolre]
    have hB0 : 0 ≤ B := meanSq_nonneg hEpos (fun w => by positivity)
    have hA0 : 0 ≤ A := integral_nonneg (fun y => by positivity)
    have hI2' : ∫ w in E, fr w ≤ (η * zpLamMin q ε)^(-(d:ℝ)) * A := by
      have hetamin : (0:ℝ) < (η * zpLamMin q ε)^d := by
        rw [zpLamMin]
        exact pow_pos (mul_pos hη0 (div_pos (mul_pos (by linarith : (0:ℝ) < 1-ε) hq)
          Real.pi_pos)) d
      have h2 : ((η * zpLamMin q ε)^d)⁻¹ * ((η * zpLamMin q ε)^d * ∫ w in E, fr w)
          = ∫ w in E, fr w := inv_mul_cancel_left₀ (ne_of_gt hetamin) _
      calc ∫ w in E, fr w
          = ((η * zpLamMin q ε)^d)⁻¹ * ((η * zpLamMin q ε)^d * ∫ w in E, fr w) := h2.symm
        _ ≤ ((η * zpLamMin q ε)^d)⁻¹ * A := mul_le_mul_of_nonneg_left hIntEge (by positivity)
        _ = (η * zpLamMin q ε)^(-(d:ℝ)) * A := by
            rw [Real.rpow_neg (le_of_lt (mul_pos hη0 hlaminpos)) (d:ℝ), Real.rpow_natCast]
    have hEinv : ((volume E).toReal)⁻¹ ≤ (η * zpLamMax q ε)^d / (2*c₁)^d := by
      have hpos1 : 0 < (2*c₁/η)^d / (zpLamMax q ε)^d := by positivity
      have haux : ((2*c₁/η)^d / (zpLamMax q ε)^d)⁻¹ = (zpLamMax q ε)^d / (2*c₁/η)^d := by
        rw [inv_div]
      have haux2 : (zpLamMax q ε)^d / (2*c₁/η)^d = (η * zpLamMax q ε)^d / (2*c₁)^d := by
        rw [mul_pow, div_pow, div_div_eq_mul_div]
        ring
      calc ((volume E).toReal)⁻¹ ≤ ((2*c₁/η)^d / (zpLamMax q ε)^d)⁻¹ :=
            (inv_le_inv₀ hEpos hpos1).mpr hEvolre
        _ = (zpLamMax q ε)^d / (2*c₁/η)^d := haux
        _ = (η * zpLamMax q ε)^d / (2*c₁)^d := haux2
    have hBle : B ≤ ((η * zpLamMin q ε)^(-(d:ℝ)) * (η * zpLamMax q ε)^d / (2*c₁)^d) * A := by
      have h1 : ((volume E).toReal)⁻¹ * ∫ w in E, fr w
          ≤ ((η * zpLamMax q ε)^d / (2*c₁)^d) * ((η * zpLamMin q ε)^(-(d:ℝ)) * A) :=
        mul_le_mul hEinv hI2' (integral_nonneg (fun w => by positivity)) (by positivity)
      rw [hBdef, meanSq]
      calc ((volume E).toReal)⁻¹ * ∫ w in E, fr w
          ≤ ((η * zpLamMax q ε)^d / (2*c₁)^d) * ((η * zpLamMin q ε)^(-(d:ℝ)) * A) := h1
        _ = ((η * zpLamMin q ε)^(-(d:ℝ)) * (η * zpLamMax q ε)^d / (2*c₁)^d) * A := by ring
    have hmidle : ∫ w in mid, fr w = (volume mid).toReal * Mmid :=
      (vol_mul_meanSq hmidpos.ne' (f := fr)).symm
    have hMmid0 : 0 ≤ Mmid := meanSq_nonneg hmidpos (fun w => by positivity)
    rcases eq_or_lt_of_le hMmid0 with hMmidz | hMmidpos
    · have hzero : ∫ w in mid, fr w = 0 := by rw [hmidle, hMmidz.symm, mul_zero]
      refine le_trans hI1 ?_
      rw [hzero, mul_zero]
      exact mul_nonneg (mul_nonneg
        (le_of_lt (cellZConst_pos q ε δ H η c₁ d hδ0 hδ3 hq hε0 hε1 hη0 hc₁))
        (Real.rpow_nonneg hSnn _)) (Real.rpow_nonneg hA0 _)
    · -- main case
      have hf0_cont : ContinuousOn f0 (cbox d (1 - 3*δ)) := by
        rw [hf0def]
        exact continuousOn_psiR_comp (d := d) hq hε0 hε1' hτ1 (c := c)
          (G := fun z : Fin d → ℂ => ‖((S⁻¹:ℝ):ℂ) * F z‖^2) (by fun_prop)
      obtain ⟨x0, hx0mid, hx0max⟩ := (isCompact_cbox d (1 - 3*δ)).exists_isMaxOn
        ⟨0, by rw [mem_cbox]; intro j; simp only [Pi.zero_apply, abs_zero]; linarith⟩ hf0_cont
      have hMmid_le : Mmid ≤ S^2 * f0 x0 := by
        rw [hMmiddef, hfr_eq, meanSq_const_mul]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [show mid = cbox d (1 - 3*δ) from hmiddef]
        exact meanSq_le_of_le (measurableSet_cbox d (1-3*δ))
          (by rw [← hmiddef]; exact hmidpos.ne') (by rw [← hmiddef]; exact hmidfin)
          (hf0_cont.integrableOn_compact (isCompact_cbox d (1-3*δ))) hx0max
      have hfx0 : 0 < f0 x0 := by
        have h1 : 0 < S^2 * f0 x0 := lt_of_lt_of_le hMmidpos hMmid_le
        have h2 : 0 < S^2 := by positivity
        nlinarith [h1, h2]
      have hzw : ∀ j, |x0 j| < 1 := fun j => by
        rw [mem_cbox] at hx0mid; exact lt_of_le_of_lt (hx0mid j) hτ1
      have hfnz : F (fun j => (PsiR q ε η c x0 j : ℂ)) ≠ 0 := by
        intro h
        have hz : f0 x0 = 0 := by
          simp only [hf0def]
          rw [h, mul_zero, norm_zero]
          simp
        linarith [hfx0]
      have hm : ∃ z : Fin d → ℂ, (∀ i, ‖z i‖ ≤ 1 - 3*δ) ∧
          ((S⁻¹ : ℝ) : ℂ) * F (PsiCLens q ε η c z) ≠ 0 ∧
          (1/2) * Real.log ((S^2)⁻¹ * Mmid)
            ≤ Real.log ‖((S⁻¹ : ℝ) : ℂ) * F (PsiCLens q ε η c z)‖ := by
        refine ⟨fun j => (x0 j : ℂ), ?_, ?_, ?_⟩
        · intro j
          rw [Complex.norm_real, Real.norm_eq_abs]
          rw [mem_cbox] at hx0mid
          exact hx0mid j
        · rw [PsiC_ofReal hε0 (le_of_lt hε1') hzw]
          refine mul_ne_zero ?_ hfnz
          simp only [ne_eq, Complex.ofReal_eq_zero]
          exact inv_ne_zero (ne_of_gt hSpos)
        · rw [PsiC_ofReal hε0 (le_of_lt hε1') hzw]
          have h1 : (S^2)⁻¹ * Mmid
              ≤ ‖((S⁻¹:ℝ):ℂ) * F (fun j => (PsiR q ε η c x0 j : ℂ))‖^2 := by
            refine le_trans (mul_le_mul_of_nonneg_left hMmid_le (by positivity)) (le_of_eq ?_)
            rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (S:ℝ)^2 ≠ 0), one_mul]
          have h2 := Real.log_le_log (by positivity) h1
          rw [Real.log_pow] at h2
          linarith
      have hintJ : IntegrableOn (fun x : Fin d → ℝ =>
          ‖((S⁻¹:ℝ):ℂ) * F (PsiCLens q ε η c (fun i => (x i : ℂ)))‖^2) E volume := by
        have hEintf0 : IntegrableOn f0 E volume :=
          (hf0_cont.integrableOn_compact (isCompact_cbox d (1-3*δ))).mono_set
            (fun w hw => by rw [← hmiddef]; exact hEsub_mid hw)
        have hae : f0 =ᵐ[volume.restrict E] (fun x : Fin d → ℝ =>
            ‖((S⁻¹:ℝ):ℂ) * F (PsiCLens q ε η c (fun i => (x i : ℂ)))‖^2) := by
          refine ae_restrict_of_forall_mem hEmeas (fun x hx => ?_)
          simp only [hf0def]
          rw [PsiC_ofReal hε0 (le_of_lt hε1') (hltE x hx)]
        exact hEintf0.congr hae
      have hCartan := cell_cartan_exp (δ := δ) (H := H) (S := S)
        (m := (1/2) * Real.log ((S^2)⁻¹ * Mmid)) hδ0 hδ3 hH0 hH1 hSpos d hd
        (fun z : Fin d → ℂ => F (PsiCLens q ε η c z))
        (analyticOnNhd_PsiC_comp (d := d) hε0 hε1' hF c) hSb hEmeas
        (fun x hx i => by
          have h1 := hEsub_mid hx
          rw [hmiddef, mem_cbox] at h1
          exact le_trans (h1 i) (by linarith))
        hJbig hm hintJ
      rw [show Real.exp (2 * ((1/2) * Real.log ((S^2)⁻¹ * Mmid))) = (S^2)⁻¹ * Mmid from by
        rw [show (2:ℝ) * ((1/2) * Real.log ((S^2)⁻¹ * Mmid)) = Real.log ((S^2)⁻¹ * Mmid)
          from by ring, Real.exp_log (by positivity)]] at hCartan
      have hBt : meanSq d E (fun x : Fin d → ℝ =>
          ‖((S⁻¹:ℝ):ℂ) * F (PsiCLens q ε η c (fun i => (x i : ℂ)))‖^2) = (S⁻¹)^2 * B := by
        have hcongr : ∀ x ∈ E, ‖((S⁻¹:ℝ):ℂ) * F (PsiCLens q ε η c (fun i => (x i : ℂ)))‖^2 = f0 x := by
          intro x hx
          simp only [hf0def]
          rw [PsiC_ofReal hε0 (le_of_lt hε1') (hltE x hx)]
        rw [meanSq_congr hEmeas hcongr]
        have h1 : meanSq d E fr = S^2 * meanSq d E f0 := by rw [hfr_eq, meanSq_const_mul]
        rw [← hBdef] at h1
        have h3 : (S⁻¹)^2 * B = meanSq d E f0 := by
          rw [h1, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hSpos), one_pow, one_mul]
        exact h3.symm
      rw [hBt] at hCartan
      have halg := zplane_cartan_algebra (S := S) (B := B) (κ := twoConstKappa δ H ^ d)
        (M := Mmid) hSpos hB0 hκd0.le hCartan
      have hBκ : B ^ (twoConstKappa δ H ^ d)
          ≤ ((η * zpLamMin q ε)^(-(d:ℝ)) * (η * zpLamMax q ε)^d / (2*c₁)^d)
              ^ (twoConstKappa δ H ^ d) * A ^ (twoConstKappa δ H ^ d) := by
        rw [← Real.mul_rpow (by positivity) hA0]
        exact Real.rpow_le_rpow hB0 hBle hκd0.le
      have hfin : ∫ w in mid, fr w ≤ (2*(1-3*δ))^d * ((2:ℝ)^(twoConstKappa δ H ^ d)
          * S ^ (2 - 2*(twoConstKappa δ H ^ d)) * B ^ (twoConstKappa δ H ^ d)) := by
        rw [hmidle, hvolmidre]
        exact mul_le_mul_of_nonneg_left halg (by positivity)
      refine le_trans hI1 ?_
      calc (η * zpLamMax q ε)^d * ∫ w in mid, fr w
          ≤ (η * zpLamMax q ε)^d * ((2*(1-3*δ))^d * ((2:ℝ)^(twoConstKappa δ H ^ d)
              * S ^ (2 - 2*(twoConstKappa δ H ^ d)) * B ^ (twoConstKappa δ H ^ d))) :=
            mul_le_mul_of_nonneg_left hfin (by positivity)
        _ ≤ (η * zpLamMax q ε)^d * ((2*(1-3*δ))^d * ((2:ℝ)^(twoConstKappa δ H ^ d)
              * S ^ (2 - 2*(twoConstKappa δ H ^ d))
              * (((η * zpLamMin q ε)^(-(d:ℝ)) * (η * zpLamMax q ε)^d / (2*c₁)^d)
                  ^ (twoConstKappa δ H ^ d) * A ^ (twoConstKappa δ H ^ d)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hBκ (by positivity)) (by positivity)) (by positivity)
        _ = cellZConst q ε δ H η c₁ d * S ^ (2 * (1 - zpKappa δ H d))
              * A ^ (zpKappa δ H d) := by
            rw [cellZConst, zpKappa,
              show (2:ℝ) - 2 * (twoConstKappa δ H ^ d)
                = 2 * (1 - twoConstKappa δ H ^ d) from by ring]
            ring

end Submission.FUP
