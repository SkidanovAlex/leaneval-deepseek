import Mathlib
import Submission.Work.NN.Final.PolarRegions
import Submission.Work.NN.Final.ChartComp.holderNorm_comp_chartPoint
import Submission.Work.CR.Flat.Holder.holderNorm_comp_le_of_contDiffOn

noncomputable section

set_option maxHeartbeats 2000000

open scoped NNReal ENNReal ContDiff
open Set Filter

namespace Work.NN.Final

/-! ## The globally smooth model of the flat fibre map

`flatPoint n ρ j p` replaces the `j`-th coordinate of `p.1` by the point of modulus
`ρ j * exp (-p.2)` on the ray of `p.1 j`.  The only non-smooth feature is the direction
`p.1 j / ‖p.1 j‖`, which is singular at `p.1 j = 0`.  On the region where the map is used,
`ε < ‖p.1 j‖`, and we obtain a globally smooth model by replacing this direction by the
already available clamped direction `ChartComp.u0` with parameter `3 ε`, which equals
`p.1 j / ‖p.1 j‖` as soon as `ε ≤ ‖p.1 j‖`. -/

/-- A globally smooth model of the flat fibre map: it agrees with `flatPoint n ρ j` on the
region `flatRegion n ρ j ε ×ˢ {t | 0 < t}` on which the latter is used. -/
def flatGlob (n : ℕ) (ρ : Fin n → ℝ) (j : Fin n) (ε : ℝ)
    (p : (Fin n → ℂ) × ℝ) : Fin n → ℂ :=
  Function.update p.1 j (((ρ j * Real.exp (-p.2) : ℝ) : ℂ) *
    ChartComp.u0 (fun _ : Fin n => 3 * ε) j (p.1 j))

/-- The radius of the auxiliary ball containing the flat region. -/
def flatRad (n : ℕ) (ρ : Fin n → ℝ) : ℝ := 3 * (∑ i, ρ i) + 1

/-- The auxiliary convex region on which the global model has bounded derivatives: a ball in
`ℂⁿ` (large enough to contain `flatRegion`) times the half line `{t | 0 < t}`. -/
def flatS (n : ℕ) (ρ : Fin n → ℝ) : Set ((Fin n → ℂ) × ℝ) :=
  Metric.ball (0 : Fin n → ℂ) (flatRad n ρ) ×ˢ Set.Ioi (0 : ℝ)

lemma flatRad_pos {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) : 0 < flatRad n ρ := by
  have hsum : 0 ≤ ∑ i, ρ i := Finset.sum_nonneg fun i _ => le_of_lt (hρ i)
  rw [flatRad]; linarith

lemma isOpen_flatS (n : ℕ) (ρ : Fin n → ℝ) : IsOpen (flatS n ρ) :=
  Metric.isOpen_ball.prod isOpen_Ioi

lemma convex_flatS (n : ℕ) (ρ : Fin n → ℝ) : Convex ℝ (flatS n ρ) :=
  (convex_ball 0 (flatRad n ρ)).prod (convex_Ioi 0)

lemma flatRegion_subset_flatS {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (j : Fin n) (ε : ℝ) :
    flatRegion n ρ j ε ×ˢ {t : ℝ | 0 < t} ⊆ flatS n ρ := by
  intro p hp
  obtain ⟨hpw, hpt⟩ := Set.mem_prod.mp hp
  rw [mem_flatRegion] at hpw
  obtain ⟨h1, ⟨hεw, hw3⟩, h3⟩ := hpw
  refine Set.mem_prod.mpr ⟨?_, hpt⟩
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  have hsum : 0 ≤ ∑ i, ρ i := Finset.sum_nonneg fun i _ => le_of_lt (hρ i)
  have hb : ‖p.1‖ ≤ 3 * ∑ i, ρ i :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hsum)).mpr fun i => by
      have hi : ‖p.1 i‖ < 3 * ρ i := by
        rcases lt_trichotomy i j with h | h | h
        · have := h1 i h; linarith [hρ i]
        · subst h; linarith
        · have := h3 i h; linarith [hρ i]
      have hle : ρ i ≤ ∑ k, ρ k :=
        Finset.single_le_sum (fun k _ => le_of_lt (hρ k)) (Finset.mem_univ i)
      linarith
  rw [flatRad]; linarith

/-- The global model agrees with `flatPoint` on the flat region. -/
lemma flatGlob_eq_flatPoint {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ} (hε : 0 < ε)
    {p : (Fin n → ℂ) × ℝ} (hp : p ∈ flatRegion n ρ j ε ×ˢ {t : ℝ | 0 < t}) :
    flatGlob n ρ j ε p = flatPoint n ρ j p := by
  obtain ⟨hpw, hpt⟩ := Set.mem_prod.mp hp
  rw [mem_flatRegion] at hpw
  obtain ⟨h1, ⟨hεw, hw3⟩, h3⟩ := hpw
  rw [flatGlob, flatPoint]
  congr 1
  have hstep : Work.NN.Final.radialStep ((3 * ε) / 8) ((3 * ε) / 3) ‖p.1 j‖ = 1 := by
    refine Work.NN.Final.radialStep_of_ge (by linarith) ?_
    linarith
  rw [ChartComp.u0, hstep, Complex.ofReal_one, one_mul, ChartComp.dirn, Complex.ofReal_div]
  ring

/-- The global model is smooth. -/
lemma contDiff_flatGlob {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (flatGlob n ρ j ε) := by
  have h3ε : (0 : ℝ) < 3 * ε := by linarith
  have hu0c : ContDiff ℝ (⊤ : ℕ∞) (ChartComp.u0 (fun _ : Fin n => 3 * ε) j) :=
    ChartComp.contDiff_u0 h3ε
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin n → ℂ) × ℝ =>
      ((ρ j * Real.exp (-p.2) : ℝ) : ℂ) *
        ChartComp.u0 (fun _ : Fin n => 3 * ε) j (p.1 j)) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (Fin n → ℂ) × ℝ => ((ρ j * Real.exp (-p.2) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp
        (contDiff_const.mul (Real.contDiff_exp.comp contDiff_snd.neg))
    have h2 : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (Fin n → ℂ) × ℝ => ChartComp.u0 (fun _ : Fin n => 3 * ε) j (p.1 j)) :=
      hu0c.comp_continuousLinearMap (g := (ContinuousLinearMap.proj (R := ℝ) j).comp
          (ContinuousLinearMap.fst ℝ (Fin n → ℂ) ℝ))
    exact h1.mul h2
  exact ChartSmooth.contDiff_update_comp j contDiff_fst hv

/-- The fibre map sends the flat region into the region where the input of the extension is
evaluated. -/
lemma mapsTo_flatPoint {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) (j : Fin n) {ε : ℝ}
    (hε : 0 < ε) :
    Set.MapsTo (flatPoint n ρ j) (flatRegion n ρ j ε ×ˢ {t : ℝ | 0 < t}) (inRegion n ρ j) := by
  intro p hp
  obtain ⟨hpw, hpt⟩ := Set.mem_prod.mp hp
  rw [mem_flatRegion] at hpw
  obtain ⟨h1, ⟨hεw, hw3⟩, h3⟩ := hpw
  rw [mem_inRegion]
  refine ⟨?_, ?_, ?_⟩
  · intro i hij
    rw [flatPoint, Function.update_apply, if_neg (ne_of_lt hij)]
    exact h1 i hij
  · rw [flatPoint, Function.update_self]
    have hp2 : 0 < p.2 := hpt
    have hwpos : 0 < ‖p.1 j‖ := lt_trans hε hεw
    have hnorm : ‖((ρ j * Real.exp (-p.2) / ‖p.1 j‖ : ℝ) : ℂ) * p.1 j‖
        = ρ j * Real.exp (-p.2) := by
      rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
        abs_of_pos (mul_pos (hρ j) (Real.exp_pos _)), abs_of_pos hwpos,
        div_mul_cancel₀ _ (ne_of_gt hwpos)]
    rw [hnorm]
    have hexp : Real.exp (-p.2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    nlinarith [hρ j]
  · intro i hji
    rw [flatPoint, Function.update_apply, if_neg (ne_of_gt hji)]
    exact h3 i hji

/-! ## Bounds for the elementary pieces -/

/-- The derivative bound for the `ℝ`-valued exponential factor. -/
lemma norm_iteratedFDerivWithin_expc_le {n : ℕ} (ρ : Fin n → ℝ) :
    ∀ (m : ℕ) (p : (Fin n → ℂ) × ℝ), p ∈ flatS n ρ →
      ‖iteratedFDerivWithin ℝ m
        (fun p : (Fin n → ℂ) × ℝ => ((Real.exp (-p.2) : ℝ) : ℂ)) (flatS n ρ) p‖ ≤ 1 := by
  intro m p hp
  have hp2 : 0 < p.2 := hp.2
  have hSopen : IsOpen (flatS n ρ) := isOpen_flatS n ρ
  rw [iteratedFDerivWithin_of_isOpen m hSopen hp]
  have hinner : ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin n → ℂ) × ℝ => Real.exp (-p.2)) :=
    Real.contDiff_exp.comp contDiff_snd.neg
  have hfun : (fun p : (Fin n → ℂ) × ℝ => ((Real.exp (-p.2) : ℝ) : ℂ))
      = Complex.ofRealCLM ∘ (fun p : (Fin n → ℂ) × ℝ => Real.exp (-p.2)) := rfl
  rw [hfun]
  have h1d : ‖iteratedFDeriv ℝ m (fun t : ℝ => Real.exp (-t)) (p.2)‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hfun2 : (fun t : ℝ => Real.exp (-t)) = (fun s : ℝ => Real.exp ((-1) * s)) := by
      funext t; rw [neg_eq_neg_one_mul]
    rw [hfun2, iteratedDeriv_exp_const_mul m (-1)]
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  calc ‖iteratedFDeriv ℝ m
        (Complex.ofRealCLM ∘ (fun p : (Fin n → ℂ) × ℝ => Real.exp (-p.2))) p‖
      ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ m
          (fun p : (Fin n → ℂ) × ℝ => Real.exp (-p.2)) p‖ :=
        ChartComp.norm_iteratedFDeriv_comp_clm_left _ hinner m p
    _ = ‖iteratedFDeriv ℝ m (fun p : (Fin n → ℂ) × ℝ => Real.exp (-p.2)) p‖ := by
        rw [Complex.ofRealCLM_norm, one_mul]
    _ = ‖iteratedFDeriv ℝ m ((fun t : ℝ => Real.exp (-t)) ∘
          (ContinuousLinearMap.snd ℝ (Fin n → ℂ) ℝ)) p‖ := rfl
    _ ≤ ‖iteratedFDeriv ℝ m (fun t : ℝ => Real.exp (-t))
          ((ContinuousLinearMap.snd ℝ (Fin n → ℂ) ℝ) p)‖ *
          ‖ContinuousLinearMap.snd ℝ (Fin n → ℂ) ℝ‖ ^ m :=
        ChartComp.norm_iteratedFDeriv_comp_clm_right _ (Real.contDiff_exp.comp contDiff_neg) m p
    _ ≤ 1 * 1 := by
        refine mul_le_mul h1d ?_ (pow_nonneg (norm_nonneg _) _) (by norm_num)
        exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ (Fin n → ℂ) ℝ)
    _ = 1 := one_mul 1

/-- Derivative bounds for the clamped fibre direction `u0 (3 ε) j` composed with the
projection. -/
lemma exists_bound_u0b {n : ℕ} (ρ : Fin n → ℝ) (j : Fin n) {ε : ℝ} (hε : 0 < ε) :
    ∃ Cu : ℕ → ℝ, (∀ m, 0 ≤ Cu m) ∧ ∀ (m : ℕ) (p : (Fin n → ℂ) × ℝ),
      ‖iteratedFDeriv ℝ m (fun p : (Fin n → ℂ) × ℝ =>
        ChartComp.u0 (fun _ : Fin n => 3 * ε) j (p.1 j)) p‖ ≤ Cu m := by
  have h3ε : (0 : ℝ) < 3 * ε := by linarith
  obtain ⟨Du, hDu⟩ := ChartComp.exists_bound_u0 (ρ := fun _ : Fin n => 3 * ε) (i := j) h3ε
  have hDu0 : ∀ m, 1 ≤ m → 0 ≤ Du m := fun m hm => le_trans (norm_nonneg _) (hDu m hm 0)
  have hu0c : ContDiff ℝ (⊤ : ℕ∞) (ChartComp.u0 (fun _ : Fin n => 3 * ε) j) :=
    ChartComp.contDiff_u0 h3ε
  refine ⟨fun m => if m = 0 then 1 else Du m, ?_, ?_⟩
  · intro m
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, if_false]; exact hDu0 m (Nat.pos_of_ne_zero hm)
  · intro m p
    by_cases hm : m = 0
    · subst hm
      show ‖iteratedFDeriv ℝ 0 (fun p : (Fin n → ℂ) × ℝ =>
        ChartComp.u0 (fun _ : Fin n => 3 * ε) j (p.1 j)) p‖ ≤ 1
      rw [norm_iteratedFDeriv_zero]
      rw [ChartComp.u0]
      refine le_trans (norm_mul_le _ _) ?_
      refine le_trans (mul_le_mul (ChartComp.norm_radialStep_cast_le _ _ _)
        (ChartComp.norm_dirn_le _) (norm_nonneg _) (by norm_num)) ?_
      norm_num
    · have hm' : (fun m => if m = 0 then (1:ℝ) else Du m) m = Du m := by simp [hm]
      rw [hm']
      have hA : ∀ z : Fin n → ℂ,
          ‖iteratedFDeriv ℝ m ((ChartComp.u0 (fun _ : Fin n => 3 * ε) j) ∘
            (ContinuousLinearMap.proj (R := ℝ) j)) z‖ ≤ Du m := by
        intro z
        refine le_trans (ChartComp.norm_iteratedFDeriv_comp_clm_right _ hu0c m z) ?_
        have hproj : ‖(ContinuousLinearMap.proj (R := ℝ) j : (Fin n → ℂ) →L[ℝ] ℂ)‖ ^ m ≤ 1 :=
          pow_le_one₀ (norm_nonneg _) (ChartComp.norm_proj_le j)
        refine le_trans (mul_le_mul_of_nonneg_left hproj (norm_nonneg _)) ?_
        rw [mul_one]
        exact hDu m (Nat.pos_of_ne_zero hm) ((ContinuousLinearMap.proj (R := ℝ) j) z)
      have hinner2 : ContDiff ℝ (⊤ : ℕ∞)
          ((ChartComp.u0 (fun _ : Fin n => 3 * ε) j) ∘
            (ContinuousLinearMap.proj (R := ℝ) j : (Fin n → ℂ) →L[ℝ] ℂ)) :=
        hu0c.comp_continuousLinearMap (g := (ContinuousLinearMap.proj (R := ℝ) j : (Fin n → ℂ) →L[ℝ] ℂ))
      have hfun3 : (fun p : (Fin n → ℂ) × ℝ =>
            ChartComp.u0 (fun _ : Fin n => 3 * ε) j (p.1 j))
          = ((ChartComp.u0 (fun _ : Fin n => 3 * ε) j) ∘
              (ContinuousLinearMap.proj (R := ℝ) j : (Fin n → ℂ) →L[ℝ] ℂ)) ∘
              (ContinuousLinearMap.fst ℝ (Fin n → ℂ) ℝ) := rfl
      rw [hfun3]
      refine le_trans (ChartComp.norm_iteratedFDeriv_comp_clm_right _ hinner2 m p) ?_
      have hfst : ‖(ContinuousLinearMap.fst ℝ (Fin n → ℂ) ℝ)‖ ^ m ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ (Fin n → ℂ) ℝ)
      refine le_trans (mul_le_mul_of_nonneg_left hfst (norm_nonneg _)) ?_
      rw [mul_one]
      exact hA _

/-- Derivative bounds for the product appearing in the model. -/
lemma exists_bound_c {n : ℕ} (ρ : Fin n → ℝ) (j : Fin n) {ε : ℝ} (hε : 0 < ε) :
    ∃ Cc : ℕ → ℝ, (∀ m, 0 ≤ Cc m) ∧ ∀ (m : ℕ) (p : (Fin n → ℂ) × ℝ), p ∈ flatS n ρ →
      ‖iteratedFDerivWithin ℝ m
        (fun p : (Fin n → ℂ) × ℝ => ((ρ j * Real.exp (-p.2) : ℝ) : ℂ) *
          ChartComp.u0 (fun _ : Fin n => 3 * ε) j (p.1 j)) (flatS n ρ) p‖ ≤ Cc m := by
  obtain ⟨Cu, hCu0, hCu⟩ := exists_bound_u0b (n := n) ρ j hε
  have h3ε : (0 : ℝ) < 3 * ε := by linarith
  have hu0c : ContDiff ℝ (⊤ : ℕ∞) (ChartComp.u0 (fun _ : Fin n => 3 * ε) j) :=
    ChartComp.contDiff_u0 h3ε
  set c1 : (Fin n → ℂ) × ℝ → ℂ := fun p => ((Real.exp (-p.2) : ℝ) : ℂ) with hc1
  set c2 : (Fin n → ℂ) × ℝ → ℂ := fun p =>
    ChartComp.u0 (fun _ : Fin n => 3 * ε) j (p.1 j) with hc2
  have hc1s : ContDiffOn ℝ (⊤ : ℕ∞) c1 (flatS n ρ) := by
    rw [hc1]
    have : (fun p : (Fin n → ℂ) × ℝ => ((Real.exp (-p.2) : ℝ) : ℂ))
        = Complex.ofRealCLM ∘ (fun p : (Fin n → ℂ) × ℝ => Real.exp (-p.2)) := rfl
    rw [this]
    exact (Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp contDiff_snd.neg)).contDiffOn
  have hc2s : ContDiffOn ℝ (⊤ : ℕ∞) c2 (flatS n ρ) := by
    rw [hc2]
    exact (hu0c.comp_continuousLinearMap (g := (ContinuousLinearMap.proj (R := ℝ) j).comp
      (ContinuousLinearMap.fst ℝ (Fin n → ℂ) ℝ))).contDiffOn
  refine ⟨fun m => |ρ j| * (∑ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * 1 * Cu (m - i)), ?_, ?_⟩
  · intro m
    refine mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => ?_)
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by norm_num)) (hCu0 (m - i))
  · intro m p hp
    have hSopen : IsOpen (flatS n ρ) := isOpen_flatS n ρ
    have heq : (fun p : (Fin n → ℂ) × ℝ => ((ρ j * Real.exp (-p.2) : ℝ) : ℂ) *
          ChartComp.u0 (fun _ : Fin n => 3 * ε) j (p.1 j))
        = (ρ j : ℝ) • (fun q => c1 q * c2 q) := by
      funext q
      simp only [Pi.smul_apply, hc1, hc2, Complex.real_smul, Complex.ofReal_mul]
      ring
    rw [heq, iteratedFDerivWithin_const_smul_apply (𝕜 := ℝ) (i := m) (s := flatS n ρ) (x := p)
      (a := (ρ j : ℝ)) (f := fun q => c1 q * c2 q)
      (((hc1s.mul hc2s).of_le (ChartComp.natCast_le_top_nat m)).contDiffWithinAt hp)
      hSopen.uniqueDiffOn hp, norm_smul]
    simp only [Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine le_trans (norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (s := flatS n ρ)
      (f := c1) (g := c2) hc1s hc2s hSopen.uniqueDiffOn hp
      (ChartComp.natCast_le_top_nat m)) ?_
    refine Finset.sum_le_sum fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : ‖iteratedFDerivWithin ℝ i c1 (flatS n ρ) p‖ ≤ 1 := by
      rw [hc1]; exact norm_iteratedFDerivWithin_expc_le ρ i p hp
    have h2 : ‖iteratedFDerivWithin ℝ (m - i) c2 (flatS n ρ) p‖ ≤ Cu (m - i) := by
      rw [hc2, iteratedFDerivWithin_of_isOpen _ hSopen hp]
      exact hCu (m - i) p
    have step1 : (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i c1 (flatS n ρ) p‖
        ≤ (m.choose i : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    have step2 : ((m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i c1 (flatS n ρ) p‖) *
          ‖iteratedFDerivWithin ℝ (m - i) c2 (flatS n ρ) p‖
        ≤ ((m.choose i : ℝ) * 1) * Cu (m - i) :=
      mul_le_mul step1 h2 (norm_nonneg _) (by positivity)
    simpa using step2

/-- Derivative bounds for the global model on the auxiliary region. -/
lemma exists_bound_flatGlob {n : ℕ} (ρ : Fin n → ℝ) (j : Fin n) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧ ∀ (m : ℕ) (p : (Fin n → ℂ) × ℝ), p ∈ flatS n ρ →
      ‖iteratedFDerivWithin ℝ m (flatGlob n ρ j ε) (flatS n ρ) p‖ ≤ D m := by
  obtain ⟨Cc, hCc0, hCc⟩ := exists_bound_c (n := n) ρ j hε
  have h3ε : (0 : ℝ) < 3 * ε := by linarith
  have hu0c : ContDiff ℝ (⊤ : ℕ∞) (ChartComp.u0 (fun _ : Fin n => 3 * ε) j) :=
    ChartComp.contDiff_u0 h3ε
  refine ⟨fun m => 1 + (if m = 0 then |flatRad n ρ| else 1) + Cc m, ?_, ?_⟩
  · intro m
    have h1 : 0 ≤ (if m = 0 then |flatRad n ρ| else (1:ℝ)) := by
      split
      · exact abs_nonneg _
      · norm_num
    linarith [hCc0 m]
  · intro m p hp
    have hSopen : IsOpen (flatS n ρ) := isOpen_flatS n ρ
    set c : (Fin n → ℂ) × ℝ → ℂ := fun q => ((ρ j * Real.exp (-q.2) : ℝ) : ℂ) *
      ChartComp.u0 (fun _ : Fin n => 3 * ε) j (q.1 j) with hcdef
    set P : (Fin n → ℂ) × ℝ → (Fin n → ℂ) × ℂ := fun q => (q.1, c q) with hPdef
    have hc_smooth : ContDiff ℝ (⊤ : ℕ∞) c := by
      rw [hcdef]
      have h1 : ContDiff ℝ (⊤ : ℕ∞)
          (fun p : (Fin n → ℂ) × ℝ => ((ρ j * Real.exp (-p.2) : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp
          (contDiff_const.mul (Real.contDiff_exp.comp contDiff_snd.neg))
      have h2 : ContDiff ℝ (⊤ : ℕ∞)
          (fun p : (Fin n → ℂ) × ℝ => ChartComp.u0 (fun _ : Fin n => 3 * ε) j (p.1 j)) :=
        hu0c.comp_continuousLinearMap (g := (ContinuousLinearMap.proj (R := ℝ) j).comp
          (ContinuousLinearMap.fst ℝ (Fin n → ℂ) ℝ))
      exact h1.mul h2
    have hP_smooth : ContDiff ℝ (⊤ : ℕ∞) P := by
      rw [hPdef]
      exact contDiff_fst.prodMk hc_smooth
    have hglob : flatGlob n ρ j ε = ChartComp.updCLM j ∘ P := by
      funext q
      simp only [Function.comp_apply, hPdef, ChartComp.updCLM_apply, hcdef, flatGlob]
    have hPbound : ‖iteratedFDerivWithin ℝ m P (flatS n ρ) p‖ ≤
        (if m = 0 then |flatRad n ρ| else 1) + Cc m := by
      have hpdm := iteratedFDerivWithin_prodMk (s := flatS n ρ) (x := p)
        (f := fun q : (Fin n → ℂ) × ℝ => q.1) (g := c)
        ((contDiff_fst : ContDiff ℝ (⊤ : ℕ∞)
          (fun q : (Fin n → ℂ) × ℝ => q.1)).contDiffWithinAt)
        (hc_smooth.contDiffWithinAt) hSopen.uniqueDiffOn hp (ChartComp.natCast_le_top_nat m)
      rw [hPdef, hpdm]
      refine le_trans (ChartComp.norm_prod_le _ _) ?_
      have hf : ‖iteratedFDerivWithin ℝ m (fun q : (Fin n → ℂ) × ℝ => q.1) (flatS n ρ) p‖
          ≤ (if m = 0 then |flatRad n ρ| else 1) := by
        by_cases hm : m = 0
        · subst hm
          rw [norm_iteratedFDerivWithin_zero]
          simp only [if_pos rfl]
          exact le_trans (le_of_lt (by simpa [dist_eq_norm] using Metric.mem_ball.mp hp.1))
            (le_abs_self _)
        · rw [if_neg hm, iteratedFDerivWithin_of_isOpen m hSopen hp]
          refine le_trans (ChartComp.norm_iteratedFDeriv_clm_le
            (ContinuousLinearMap.fst ℝ (Fin n → ℂ) ℝ) m (Nat.pos_of_ne_zero hm) p) ?_
          exact ContinuousLinearMap.norm_fst_le ℝ (Fin n → ℂ) ℝ
      have hc : ‖iteratedFDerivWithin ℝ m c (flatS n ρ) p‖ ≤ Cc m := by
        rw [hcdef]; exact hCc m p hp
      linarith [hf, hc]
    rw [hglob]
    refine le_trans (ContinuousLinearMap.norm_iteratedFDerivWithin_comp_left
      (ChartComp.updCLM j) (f := P) hP_smooth.contDiffWithinAt hSopen.uniqueDiffOn hp
      (ChartComp.natCast_le_top_nat m)) ?_
    refine le_trans (mul_le_mul (ChartComp.norm_updCLM_le j) hPbound (norm_nonneg _)
      (by norm_num)) ?_
    change 1 * ((if m = 0 then |flatRad n ρ| else 1) + Cc m) ≤
      1 + (if m = 0 then |flatRad n ρ| else 1) + Cc m
    linarith

/-- The global model is Lipschitz on the auxiliary convex region. -/
lemma exists_lipschitz_flatGlob {n : ℕ} (ρ : Fin n → ℝ) (j : Fin n) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ flatS n ρ, ∀ y ∈ flatS n ρ,
      ‖flatGlob n ρ j ε x - flatGlob n ρ j ε y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨D, hD0, hD⟩ := exists_bound_flatGlob (n := n) ρ j hε
  have hc : ContDiff ℝ (⊤ : ℕ∞) (flatGlob n ρ j ε) := contDiff_flatGlob hε
  refine ⟨max (D 1) 0, le_max_right _ _, fun x hx y hy => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (s := flatS n ρ) (C := max (D 1) 0)
    (f := flatGlob n ρ j ε) (x := y) (y := x)
    (fun z _ => (hc.differentiable (by simp)).differentiableAt) (fun z hz => ?_)
    (convex_flatS n ρ) hy hx
  · simpa only [norm_sub_rev] using h
  · rw [← norm_iteratedFDeriv_one (flatGlob n ρ j ε),
      ← iteratedFDerivWithin_of_isOpen 1 (isOpen_flatS n ρ) hz]
    exact le_trans (hD 1 z hz) (le_max_left _ _)

/-- Every iterated derivative of the global model is Hölder of exponent `α < 1` on the
auxiliary convex region. -/
lemma exists_holderE_flatGlob {n : ℕ} (ρ : Fin n → ℝ) (j : Fin n) {ε : ℝ} (hε : 0 < ε)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ E : ℕ → ℝ, ∀ (k : ℕ) (x : (Fin n → ℂ) × ℝ), x ∈ flatS n ρ →
      ∀ y ∈ flatS n ρ,
      ‖iteratedFDeriv ℝ k (flatGlob n ρ j ε) x - iteratedFDeriv ℝ k (flatGlob n ρ j ε) y‖
        ≤ E k * ‖x - y‖ ^ α := by
  obtain ⟨D, hD0, hD⟩ := exists_bound_flatGlob (n := n) ρ j hε
  have hc : ContDiff ℝ (⊤ : ℕ∞) (flatGlob n ρ j ε) := contDiff_flatGlob hε
  refine ⟨fun k => max (D (k + 1)) (2 * D k), fun k x hx y hy => ?_⟩
  have hDk : 0 ≤ D k := hD0 k
  have hDk1 : 0 ≤ D (k + 1) := hD0 (k + 1)
  rcases eq_or_ne x y with rfl | hne
  · simp [Real.zero_rpow hα0.ne']
  · have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    rcases lt_or_ge (1 : ℝ) ‖x - y‖ with hxy | hxy
    · have hone : (1 : ℝ) ≤ ‖x - y‖ ^ α := Real.one_le_rpow hxy.le hα0.le
      calc ‖iteratedFDeriv ℝ k (flatGlob n ρ j ε) x
              - iteratedFDeriv ℝ k (flatGlob n ρ j ε) y‖
          ≤ ‖iteratedFDeriv ℝ k (flatGlob n ρ j ε) x‖
            + ‖iteratedFDeriv ℝ k (flatGlob n ρ j ε) y‖ := norm_sub_le _ _
        _ ≤ D k + D k := by
            refine add_le_add ?_ ?_
            · rw [← iteratedFDerivWithin_of_isOpen k (isOpen_flatS n ρ) hx]
              exact hD k x hx
            · rw [← iteratedFDerivWithin_of_isOpen k (isOpen_flatS n ρ) hy]
              exact hD k y hy
        _ = 2 * D k := by ring
        _ ≤ 2 * D k * ‖x - y‖ ^ α := le_mul_of_one_le_right (by linarith) hone
        _ ≤ max (D (k + 1)) (2 * D k) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) α)
    · have hle : ‖x - y‖ ≤ ‖x - y‖ ^ α := by
        have h1 : ‖x - y‖ ^ α * ‖x - y‖ ^ (1 - α) = ‖x - y‖ := by
          rw [← Real.rpow_add hpos, show α + (1 - α) = 1 by ring, Real.rpow_one]
        have h2 : ‖x - y‖ ^ (1 - α) ≤ 1 :=
          Real.rpow_le_one (norm_nonneg _) hxy (sub_nonneg.mpr hα1.le)
        calc ‖x - y‖ = ‖x - y‖ ^ α * ‖x - y‖ ^ (1 - α) := h1.symm
          _ ≤ ‖x - y‖ ^ α * 1 :=
              mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (norm_nonneg _) α)
          _ = ‖x - y‖ ^ α := mul_one _
      have hdiff : ∀ z : (Fin n → ℂ) × ℝ, DifferentiableAt ℝ
          (fun w => iteratedFDeriv ℝ k (flatGlob n ρ j ε) w) z := by
        intro z
        have h1 : ContDiff ℝ (1 : WithTop ℕ∞)
            (fun w => iteratedFDeriv ℝ k (flatGlob n ρ j ε) w) :=
          hc.iteratedFDeriv_right (i := k) (WithTop.coe_le_coe.mpr le_top)
        exact (h1.differentiable (by simp)).differentiableAt
      have hbound : ∀ z ∈ flatS n ρ,
          ‖fderiv ℝ (fun w => iteratedFDeriv ℝ k (flatGlob n ρ j ε) w) z‖ ≤ D (k + 1) := by
        intro z hz
        rw [norm_fderiv_iteratedFDeriv (f := flatGlob n ρ j ε) (n := k) (x := z),
          ← iteratedFDerivWithin_of_isOpen (k + 1) (isOpen_flatS n ρ) hz]
        exact hD (k + 1) z hz
      have hmvt : ‖iteratedFDeriv ℝ k (flatGlob n ρ j ε) x
          - iteratedFDeriv ℝ k (flatGlob n ρ j ε) y‖ ≤ D (k + 1) * ‖x - y‖ := by
        have h := Convex.norm_image_sub_le_of_norm_fderiv_le (s := flatS n ρ)
          (f := fun w => iteratedFDeriv ℝ k (flatGlob n ρ j ε) w) (C := D (k + 1))
          (x := y) (y := x) (fun z _ => hdiff z) (fun z hz => hbound z hz)
          (convex_flatS n ρ) hy hx
        simpa only [norm_sub_rev] using h
      refine le_trans hmvt ?_
      calc D (k + 1) * ‖x - y‖ ≤ D (k + 1) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_left hle hDk1
        _ ≤ max (D (k + 1)) (2 * D k) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) α)

/-! ## The composition estimate -/

theorem holderNorm_comp_flatPoint {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (j : Fin n) {ε : ℝ} (hε : 0 < ε) (hερ : ε < 3 * ρ j) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ (k : ℕ) (G : (Fin n → ℂ) → ℂ),
      ContDiffOn ℝ (k : WithTop ENat) G (Work.NN.Final.inRegion n ρ j) →
      Work.CR.Flat.holderNorm k α (Work.NN.Final.flatPull n ρ j G)
          (Work.NN.Final.flatRegion n ρ j ε ×ˢ {t : ℝ | 0 < t})
        ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α G (Work.NN.Final.inRegion n ρ j) := by
  classical
  set s : Set ((Fin n → ℂ) × ℝ) := flatRegion n ρ j ε ×ˢ {t : ℝ | 0 < t} with hs
  obtain ⟨D, hD0, hDb⟩ := exists_bound_flatGlob (n := n) ρ j hε
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_flatGlob (n := n) ρ j hε
  obtain ⟨E, hE⟩ := exists_holderE_flatGlob (n := n) ρ j hε hα0 hα1
  have hsopen : IsOpen s := (isOpen_flatRegion n (hρ := hρ) j ε).prod isOpen_Ioi
  have htopen : IsOpen (inRegion n ρ j) := isOpen_inRegion n (hρ := hρ) j
  have hsub : s ⊆ flatS n ρ := flatRegion_subset_flatS hρ j ε
  have hglob_eq : ∀ p ∈ s, flatPoint n ρ j p = flatGlob n ρ j ε p :=
    fun p hp => (flatGlob_eq_flatPoint (n := n) (ρ := ρ) (j := j) hε hp).symm
  have hΦ : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) (flatPoint n ρ j) s := by
    intro m
    have h1 : ContDiffOn ℝ (m : WithTop ENat) (flatGlob n ρ j ε) s :=
      (contDiff_flatGlob (n := n) (ρ := ρ) (j := j) hε).contDiffOn.of_le
        (ChartComp.natCast_le_top_nat m)
    exact h1.congr (fun p hp => (hglob_eq p hp))
  have hst : Set.MapsTo (flatPoint n ρ j) s (inRegion n ρ j) :=
    mapsTo_flatPoint hρ j hε
  have hL' : ∀ x ∈ s, ∀ y ∈ s, ‖flatPoint n ρ j x - flatPoint n ρ j y‖ ≤ L * ‖x - y‖ := by
    intro x hx y hy
    rw [hglob_eq x hx, hglob_eq y hy]
    exact hL x (hsub hx) y (hsub hy)
  have hkey : ∀ (k : ℕ) (x : (Fin n → ℂ) × ℝ), x ∈ s →
      iteratedFDerivWithin ℝ k (flatPoint n ρ j) s x
        = iteratedFDerivWithin ℝ k (flatGlob n ρ j ε) (flatS n ρ) x := by
    intro k x hx
    have h1 : iteratedFDerivWithin ℝ k (flatPoint n ρ j) s x
        = iteratedFDerivWithin ℝ k (flatGlob n ρ j ε) s x :=
      iteratedFDerivWithin_congr (fun z hz => hglob_eq z hz) hx k
    have h2 : iteratedFDerivWithin ℝ k (flatGlob n ρ j ε) s x
        = iteratedFDerivWithin ℝ k (flatGlob n ρ j ε) (flatS n ρ) x := by
      rw [iteratedFDerivWithin_of_isOpen k hsopen hx,
        iteratedFDerivWithin_of_isOpen k (isOpen_flatS n ρ) (hsub hx)]
    rw [h1, h2]
  have hD' : ∀ (k : ℕ) (x : (Fin n → ℂ) × ℝ), x ∈ s →
      ‖iteratedFDerivWithin ℝ k (flatPoint n ρ j) s x‖ ≤ D k := by
    intro k x hx
    rw [hkey k x hx]
    exact hDb k x (hsub hx)
  have hE' : ∀ (k : ℕ) (x : (Fin n → ℂ) × ℝ), x ∈ s → ∀ y ∈ s,
      ‖iteratedFDerivWithin ℝ k (flatPoint n ρ j) s x
        - iteratedFDerivWithin ℝ k (flatPoint n ρ j) s y‖ ≤ E k * ‖x - y‖ ^ α := by
    intro k x hx y hy
    rw [hkey k x hx, hkey k y hy,
      iteratedFDerivWithin_of_isOpen k (isOpen_flatS n ρ) (hsub hx),
      iteratedFDerivWithin_of_isOpen k (isOpen_flatS n ρ) (hsub hy)]
    exact hE k x (hsub hx) y (hsub hy)
  obtain ⟨C, hC0, hC⟩ := Work.CR.Flat.Holder.holderNorm_comp_le_of_contDiffOn
    (Φ := flatPoint n ρ j) (s := s) (t := inRegion n ρ j) hst hΦ hsopen htopen L hL'
    α hα0 D hD' E hE'
  refine ⟨C, hC0, fun k G hG => ?_⟩
  have h := hC k G hG
  have hfun : flatPull n ρ j G = G ∘ flatPoint n ρ j := rfl
  rw [hfun]
  exact h

end Work.NN.Final
