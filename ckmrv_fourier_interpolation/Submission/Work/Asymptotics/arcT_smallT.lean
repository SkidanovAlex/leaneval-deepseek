/-
# The boundedness of the kernel on the tangency-arc region, `1 ≤ t ≤ T`

The analytic core of `Work.Asymptotics.arcT_tail`: the CKMRV kernel differs from its
non-decaying cusp part `Aexp` by a *bounded* function on `arcT × [1,T]`.

The contour points `τ ∈ arcT ⊆ 𝒟` never meet the pole divisor `j τ = j(it)` of
`z ↦ K^{(d)}(τ,z)` (`Work.Asymptotics.arcT` has `Re τ ≠ 0` on its closure, and the orbit of a
point of `𝒟` meets the imaginary axis only for `Re = 0`); only the *closure* of `arcT` meets the
divisor, along the two tangency arcs.  The bound is therefore obtained by a compactness
argument on `closure arcT × [1,T]`: away from the coincidence set the kernel is continuous
(`Work.Asymptotics.continuousOn_Kfun_clean`), while at the coincidence points of the closure
the pole is removable and the local bounds are supplied by

* `Work.Asymptotics.Graze.key_bound_arc'` at the two tangency points (`t = 1`),
* `Work.Asymptotics.graze_branch_bound` along the two grazing branches (`t ≠ 1`),

the relevant grazing elements being classified by
`Work.Asymptotics.arcT_orbit_classification_ge`.
-/
import Mathlib
import Submission.Work.Asymptotics.arcRegion
import Submission.Work.Asymptotics.arcT_classify_ge
import Submission.Work.Asymptotics.arcT_branch_bound
import Submission.Work.Asymptotics.arcT_key_bound
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.Kfun_principal_part_z_lip

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups Manifold Topology

namespace Work.Asymptotics

/-! ## Compactness of the region -/

/-- The closed, bounded hull `{1/10 ≤ Im} ∩ {‖·‖ ≤ 3}` of `arcT`. -/
def arcHull : Set ℍ :=
  {z | (1 : ℝ) / 10 ≤ z.im ∧ ‖(z : ℂ)‖ ≤ 3}

lemma isClosed_arcHull : IsClosed arcHull :=
  (isClosed_le continuous_const UpperHalfPlane.continuous_im).inter
    (isClosed_le continuous_coe.norm continuous_const)

/-- The same set, as the `ofComplex`-image of a compact set of `ℂ`. -/
private def arcHullC : Set ℂ :=
  Metric.closedBall (0 : ℂ) 3 ∩ {w : ℂ | (1 : ℝ) / 10 ≤ w.im}

private lemma isCompact_arcHullC : IsCompact arcHullC :=
  (isCompact_closedBall (0 : ℂ) 3).inter_right
    (isClosed_le continuous_const Complex.continuous_im)

private lemma arcHull_eq_image : arcHull = UpperHalfPlane.ofComplex '' arcHullC := by
  ext z
  constructor
  · intro hz
    refine ⟨(z : ℂ), ?_, UpperHalfPlane.ofComplex_apply z⟩
    refine ⟨?_, hz.1⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hz.2
  · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
    have hwpos : 0 < w.im := lt_of_lt_of_le (by norm_num) hw2
    have hw3 : ‖w‖ ≤ 3 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hw1
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hwpos]
    exact ⟨by simpa [UpperHalfPlane.coe_im, UpperHalfPlane.coe_mk] using hw2,
      by simpa [UpperHalfPlane.coe_mk] using hw3⟩

lemma isCompact_arcHull : IsCompact arcHull := by
  rw [arcHull_eq_image]
  refine IsCompact.image_of_continuousOn isCompact_arcHullC ?_
  refine continuousOn_ofComplex_im_pos.mono ?_
  intro w hw
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/10) hw.2

lemma closure_arcT_subset_arcHull : closure (arcT : Set ℍ) ⊆ arcHull := by
  refine closure_minimal ?_ isClosed_arcHull
  intro w hw
  exact ⟨le_of_lt (arcT_im_gt hw), arcT_norm_le hw⟩

lemma isCompact_closure_arcT' : IsCompact (closure (arcT : Set ℍ)) :=
  isCompact_arcHull.of_isClosed_subset isClosed_closure closure_arcT_subset_arcHull


/-! ## The contour point as a total, globally continuous function of `t` -/

/-- The contour point `i t`, written as a total function of `t` and clamped at level `1/2`
(this makes it continuous everywhere; on `{t ≥ 1/2}` it is the genuine contour point). -/
def zz (t : ℝ) : ℍ :=
  UpperHalfPlane.ofComplex (Complex.I * ((max t (1 / 2) : ℝ) : ℂ))

lemma continuous_zz : Continuous zz := by
  have h1 : Continuous (fun t : ℝ => (max t (1 / 2) : ℝ)) :=
    continuous_id.max continuous_const
  have h2 : ∀ t : ℝ, (max t (1 / 2) : ℝ) ∈ Set.Ioi (0 : ℝ) :=
    fun t => lt_of_lt_of_le (by norm_num) (le_max_right t (1 / 2))
  have h : Continuous ((fun u : ℝ => UpperHalfPlane.ofComplex (Complex.I * (u : ℂ))) ∘
      fun t : ℝ => max t (1 / 2)) :=
    (continuousOn_ofComplex_I_mul).comp_continuous h1 h2
  first
    | exact h
    | (convert h using 1 with t; simp [zz, Function.comp_apply])

lemma zz_coe {t : ℝ} (ht : (1 : ℝ) / 2 ≤ t) : ((zz t : ℍ) : ℂ) = (t : ℂ) * Complex.I := by
  have hpos : 0 < ((t : ℂ) * Complex.I).im := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_one, add_zero]
    linarith
  rw [zz, max_eq_left ht, mul_comm Complex.I ((t : ℂ))]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hpos]

lemma zz_sub {s t : ℝ} (hs : (1 : ℝ) / 2 ≤ s) (ht : (1 : ℝ) / 2 ≤ t) :
    ‖((zz s : ℍ) : ℂ) - ((zz t : ℍ) : ℂ)‖ = |s - t| := by
  rw [zz_coe hs, zz_coe ht,
    show (s : ℂ) * Complex.I - (t : ℂ) * Complex.I = ((s - t : ℝ) : ℂ) * Complex.I by
      push_cast; ring,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

lemma zz_eq_imagAxis {t : ℝ} (ht0 : 0 < t) (ht : (1 : ℝ) / 2 ≤ t) :
    zz t = Work.Kernels.imagAxis t ht0 := by
  apply UpperHalfPlane.ext
  rw [zz_coe ht]
  rfl

lemma zz_one : zz 1 = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [zz_coe (by norm_num : (1 : ℝ) / 2 ≤ 1), UpperHalfPlane.coe_I]
  norm_num

lemma Kaxis_eq_Kfun_zz {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} {t : ℝ} (ht0 : 0 < t)
    (ht : (1 : ℝ) / 2 ≤ t) (τ : ℍ) :
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t = Work.Kernels.Kfun ℓ d τ (zz t) := by
  rw [Work.Kernels.Kaxis, dif_pos ht0]
  congr 1
  exact (zz_eq_imagAxis ht0 ht).symm

/-! ## The non-decaying part is bounded -/

theorem arcT_Aexp_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (t : ℝ), τ ∈ arcT → 1 ≤ t → t ≤ T →
      ‖Aexp (Gcusp ℓ d) τ t‖ ≤ C := by
  have hGb : ∀ i j : Fin 2, ∃ B : ℝ, 0 ≤ B ∧ ∀ τ ∈ arcT, ‖Gcusp ℓ d i j τ‖ ≤ B := by
    intro i j
    obtain ⟨α, N, hα, hN, hmod⟩ :=
      (Work.Kernels.moderateGrowthOn_iff_scale DomainD (Gcusp ℓ d i j)).mp
        (GcuspInP ℓ d i j)
    refine ⟨α * (14 : ℝ) ^ N, by positivity, fun τ hτ => ?_⟩
    refine le_trans (hmod τ (arcT_subset_DomainD hτ)) ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Work.Kernels.scale_pos τ).le (arcT_scale_le hτ) hN) hα
  obtain ⟨B00, hB00, hb00⟩ := hGb 0 0
  obtain ⟨B01, hB01, hb01⟩ := hGb 0 1
  obtain ⟨B10, hB10, hb10⟩ := hGb 1 0
  obtain ⟨B11, hB11, hb11⟩ := hGb 1 1
  have hCnn : 0 ≤ B00 + (|T| + 1) * B01 + Real.exp (2 * Real.pi * (|T| + 1))
      * (B10 + (|T| + 1) * B11) + 1 := by
    have h1 : 0 ≤ (|T| + 1) * B01 := mul_nonneg (by positivity) hB01
    have h2 : 0 ≤ (|T| + 1) * B11 := mul_nonneg (by positivity) hB11
    have h3 : 0 ≤ Real.exp (2 * Real.pi * (|T| + 1)) := (Real.exp_pos _).le
    have h4 : 0 ≤ B10 + (|T| + 1) * B11 := by linarith
    have h5 : 0 ≤ Real.exp (2 * Real.pi * (|T| + 1)) * (B10 + (|T| + 1) * B11) :=
      mul_nonneg h3 h4
    linarith
  refine ⟨B00 + (|T| + 1) * B01 + Real.exp (2 * Real.pi * (|T| + 1))
    * (B10 + (|T| + 1) * B11) + 1, hCnn, fun τ t hτ ht1 htT => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have htabs : ‖(t : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have hI' : ‖((t : ℂ) * Complex.I)‖ = t := by
    rw [norm_mul, Complex.norm_I, mul_one, htabs]
  have hexp : ‖Complex.exp (2 * Real.pi * t)‖ = Real.exp (2 * Real.pi * t) := by
    rw [Complex.norm_exp]
    simp
  have htT' : t ≤ |T| + 1 := by
    have := le_abs_self T
    linarith
  have hexp_le : Real.exp (2 * Real.pi * t) ≤ Real.exp (2 * Real.pi * (|T| + 1)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  rw [Aexp]
  calc ‖Gcusp ℓ d 0 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 τ
        + Complex.exp (2 * Real.pi * t) * (Gcusp ℓ d 1 0 τ + ((t : ℂ) * Complex.I)
            * Gcusp ℓ d 1 1 τ)‖
      ≤ ‖Gcusp ℓ d 0 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 τ‖
        + ‖Complex.exp (2 * Real.pi * t) * (Gcusp ℓ d 1 0 τ + ((t : ℂ) * Complex.I)
            * Gcusp ℓ d 1 1 τ)‖ := norm_add_le _ _
    _ ≤ (B00 + t * B01) + Real.exp (2 * Real.pi * t) * (B10 + t * B11) := by
        refine add_le_add ?_ ?_
        · calc ‖Gcusp ℓ d 0 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 τ‖
              ≤ ‖Gcusp ℓ d 0 0 τ‖ + ‖((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 τ‖ :=
                norm_add_le _ _
            _ ≤ B00 + t * B01 := by
                refine add_le_add (hb00 τ hτ) ?_
                rw [norm_mul, hI']
                exact mul_le_mul_of_nonneg_left (hb01 τ hτ) ht0.le
        · rw [norm_mul, hexp]
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          calc ‖Gcusp ℓ d 1 0 τ + ((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 τ‖
              ≤ ‖Gcusp ℓ d 1 0 τ‖ + ‖((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 τ‖ :=
                norm_add_le _ _
            _ ≤ B10 + t * B11 := by
                refine add_le_add (hb10 τ hτ) ?_
                rw [norm_mul, hI']
                exact mul_le_mul_of_nonneg_left (hb11 τ hτ) ht0.le
    _ ≤ B00 + (|T| + 1) * B01
          + Real.exp (2 * Real.pi * (|T| + 1)) * (B10 + (|T| + 1) * B11) := by
        have h2 : t * B01 ≤ (|T| + 1) * B01 := mul_le_mul_of_nonneg_right htT' hB01
        have h3 : t * B11 ≤ (|T| + 1) * B11 := mul_le_mul_of_nonneg_right htT' hB11
        have h5 : B10 + t * B11 ≤ B10 + (|T| + 1) * B11 := by linarith
        have h6 : Real.exp (2 * Real.pi * t) * (B10 + t * B11)
            ≤ Real.exp (2 * Real.pi * (|T| + 1)) * (B10 + (|T| + 1) * B11) :=
          mul_le_mul hexp_le h5 (by positivity) (Real.exp_pos _).le
        linarith
    _ ≤ B00 + (|T| + 1) * B01
          + Real.exp (2 * Real.pi * (|T| + 1)) * (B10 + (|T| + 1) * B11) + 1 :=
        le_add_of_nonneg_right zero_le_one

/-! ## The coincidence locus of the region -/

/-- The parameter points of `closure arcT × [1,T]` at which the slice `z ↦ K^{(d)}(τ,z)` has a
pole on the contour. -/
def BadCoinc (T : ℝ) : Set (ℍ × ℝ) :=
  {p | p.1 ∈ closure arcT ∧ 1 ≤ p.2 ∧ p.2 ≤ T ∧
    Work.Kernels.jInvariantFun p.1 = Work.Kernels.jInvariantFun (zz p.2)}

lemma isClosed_BadCoinc (T : ℝ) : IsClosed (BadCoinc T) :=
  IsClosed.inter (isClosed_closure.preimage continuous_fst)
    (IsClosed.inter (isClosed_le continuous_const continuous_snd)
      (IsClosed.inter (isClosed_le continuous_snd continuous_const)
        (isClosed_eq (continuous_jInvariantFun'.comp continuous_fst)
          (continuous_jInvariantFun'.comp (continuous_zz.comp continuous_snd)))))

lemma isCompact_BadCoinc {T : ℝ} (hT : 1 ≤ T) : IsCompact (BadCoinc T) :=
  (isCompact_closure_arcT'.prod isCompact_Icc).of_isClosed_subset (isClosed_BadCoinc T)
    (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)

/-- Every of the eight grazing elements of `Work.Asymptotics.ArcClassify` has the same Möbius
action as one of the four `Work.Asymptotics.Graze.GrazeElem`. -/
lemma isGrazeElem_exists' (γ : SL(2, ℤ)) (h : ArcClassify.isGrazeElem γ) :
    ∃ δ : SL(2, ℤ), Graze.GrazeElem δ ∧ ∀ z : ℍ, δ • z = γ • z := by
  simp only [ArcClassify.isGrazeElem] at h
  rcases h with h | h | h | h | h | h | h | h
  · exact ⟨_, Or.inl h, fun z => by rw [h]⟩
  · exact ⟨ModularGroup.T * ModularGroup.S * ModularGroup.T, Or.inl rfl,
      fun z => by rw [h, ModularGroup.SL_neg_smul]⟩
  · exact ⟨_, Or.inr (Or.inl h), fun z => by rw [h]⟩
  · exact ⟨(ModularGroup.T * ModularGroup.S)⁻¹, Or.inr (Or.inl rfl),
      fun z => by rw [h, ModularGroup.SL_neg_smul]⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inr h)), fun z => by rw [h]⟩
  · exact ⟨(ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹, Or.inr (Or.inr (Or.inr rfl)),
      fun z => by rw [h, ModularGroup.SL_neg_smul]⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inl h)), fun z => by rw [h]⟩
  · exact ⟨ModularGroup.S * ModularGroup.T, Or.inr (Or.inr (Or.inl rfl)),
      fun z => by rw [h, ModularGroup.SL_neg_smul]⟩

/-- The `i`-images of the four `GrazeElem`s are the two tangency points. -/
lemma graze_I_eq' (δ : SL(2, ℤ)) (hδ : Graze.GrazeElem δ) :
    δ • UpperHalfPlane.I = Graze.cR ∨ δ • UpperHalfPlane.I = Graze.cL := by
  have hne : ((1 : ℂ) - Complex.I) ≠ 0 := by
    intro hh; have := congrArg Complex.im hh; simp at this
  rcases hδ with h | h | h | h <;> subst h
  · exact Or.inl rfl
  · refine Or.inl ?_
    apply UpperHalfPlane.ext
    rw [Graze.coe_TS_inv_smul, Graze.cR_coe, UpperHalfPlane.coe_I]
    rw [div_eq_div_iff hne (by norm_num)]
    ring_nf
    rw [Complex.I_sq]
    ring
  · exact Or.inr rfl
  · refine Or.inr ?_
    apply UpperHalfPlane.ext
    rw [Graze.coe_TST_inv_smul, Graze.cL_coe, UpperHalfPlane.coe_I]
    rw [div_eq_div_iff hne (by norm_num)]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- **Local boundedness at a coincidence point of the region.**  At a parameter point `p` of the
coincidence locus the slice `z ↦ K(τ,z)` has a removable pole on the contour, so `K` is bounded
near `(p.1, zz p.2)`; the branch is either a tangency point (`p.2 = 1`) or a grazing branch. -/
lemma exists_local_bound_bad (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {T : ℝ} (hT : 1 ≤ T) (p : BadCoinc T) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ (τ : ℍ) (t : ℝ),
      ‖(τ : ℂ) - (((p : ℍ × ℝ).1) : ℂ)‖ < ρ → |t - (p : ℍ × ℝ).2| < ρ →
      (1 : ℝ) / 2 < t → ‖Work.Kernels.Kfun ℓ d τ (zz t)‖ ≤ C := by
  obtain ⟨hτcl, ht1, -, hcoin⟩ := p.2
  have ht₀pos : 0 < (p : ℍ × ℝ).2 := lt_of_lt_of_le zero_lt_one ht1
  have ht₀half : (1 : ℝ) / 2 ≤ (p : ℍ × ℝ).2 := by linarith
  obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq hcoin
  have hcl : γ • Work.Kernels.imagAxis (p : ℍ × ℝ).2 ht₀pos ∈ closure arcT := by
    rw [← zz_eq_imagAxis ht₀pos ht₀half, hγ]; exact hτcl
  have hg : ArcClassify.isGrazeElem γ :=
    arcT_orbit_classification_ge γ (p : ℍ × ℝ).2 ht₀pos ht1 hcl
  obtain ⟨δ, hδ, hδact⟩ := isGrazeElem_exists' γ hg
  have hδp : δ • (zz (p : ℍ × ℝ).2) = (p : ℍ × ℝ).1 := by rw [hδact]; exact hγ
  by_cases ht1' : (p : ℍ × ℝ).2 = 1
  · -- the tangency point
    have h2 : δ • (zz 1) = (p : ℍ × ℝ).1 := by rw [← ht1']; exact hδp
    rw [zz_one] at h2
    rcases graze_I_eq' δ hδ with hR | hL
    · obtain ⟨ρ, C, hρ, hC, hb⟩ := Graze.key_bound_arc' ℓ d hd
        (ModularGroup.T * ModularGroup.S * ModularGroup.T) (Or.inl rfl)
      have hA : (ModularGroup.T * ModularGroup.S * ModularGroup.T) • (UpperHalfPlane.I : ℍ)
          = (p : ℍ × ℝ).1 := by
        rw [show ((ModularGroup.T * ModularGroup.S * ModularGroup.T) • (UpperHalfPlane.I : ℍ))
          = Graze.cR from rfl, ← hR]
        exact h2
      refine ⟨min ρ 1, C, lt_min hρ one_pos, hC, fun τ t hτ ht ht2 => ?_⟩
      refine hb τ (zz t) ?_ ?_
      · rw [hA]
        exact lt_of_lt_of_le hτ (min_le_left _ _)
      · have hzi : Complex.I = ((zz (p : ℍ × ℝ).2 : ℍ) : ℂ) := by
          rw [show Complex.I = ((UpperHalfPlane.I : ℍ) : ℂ) from UpperHalfPlane.coe_I.symm,
            ht1', zz_one]
        rw [hzi, zz_sub (le_of_lt ht2) ht₀half]
        exact lt_of_lt_of_le ht (min_le_left _ _)
    · obtain ⟨ρ, C, hρ, hC, hb⟩ := Graze.key_bound_arc' ℓ d hd
        (ModularGroup.S * ModularGroup.T) (Or.inr rfl)
      have hA : (ModularGroup.S * ModularGroup.T) • (UpperHalfPlane.I : ℍ)
          = (p : ℍ × ℝ).1 := by
        rw [show ((ModularGroup.S * ModularGroup.T) • (UpperHalfPlane.I : ℍ))
          = Graze.cL from rfl, ← hL]
        exact h2
      refine ⟨min ρ 1, C, lt_min hρ one_pos, hC, fun τ t hτ ht ht2 => ?_⟩
      refine hb τ (zz t) ?_ ?_
      · rw [hA]
        exact lt_of_lt_of_le hτ (min_le_left _ _)
      · have hzi : Complex.I = ((zz (p : ℍ × ℝ).2 : ℍ) : ℂ) := by
          rw [show Complex.I = ((UpperHalfPlane.I : ℍ) : ℂ) from UpperHalfPlane.coe_I.symm,
            ht1', zz_one]
        rw [hzi, zz_sub (le_of_lt ht2) ht₀half]
        exact lt_of_lt_of_le ht (min_le_left _ _)
  · -- a grazing branch
    obtain ⟨ρ, C, hρ, hC, hb⟩ := graze_branch_bound ℓ d hd δ hδ ht₀pos ht1'
    refine ⟨min ρ 1, C, lt_min hρ one_pos, hC, fun τ t hτ ht ht2 => ?_⟩
    refine hb τ (zz t) ?_ ?_
    · rw [← zz_eq_imagAxis ht₀pos ht₀half, hδp]
      exact lt_of_lt_of_le hτ (min_le_left _ _)
    · rw [← zz_eq_imagAxis ht₀pos ht₀half, zz_sub (le_of_lt ht2) ht₀half]
      exact lt_of_lt_of_le ht (min_le_left _ _)

/-! ## The kernel is bounded on `arcT × [1,T]` -/

theorem arcT_Kaxis_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (T : ℝ) (hT : 1 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (t : ℝ), τ ∈ arcT → 1 ≤ t → t ≤ T →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  classical
  have hloc : ∀ p : BadCoinc T, ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ (τ : ℍ) (t : ℝ),
      ‖(τ : ℂ) - (((p : ℍ × ℝ).1) : ℂ)‖ < ρ → |t - (p : ℍ × ℝ).2| < ρ →
      (1 : ℝ) / 2 < t → ‖Work.Kernels.Kfun ℓ d τ (zz t)‖ ≤ C :=
    fun p => exists_local_bound_bad ℓ d hd hT p
  choose ρf Cf hrest using hloc
  have hρf : ∀ p : BadCoinc T, 0 < ρf p := fun p => (hrest p).1
  have hCf : ∀ p : BadCoinc T, 0 ≤ Cf p := fun p => (hrest p).2.1
  have hbound : ∀ (p : BadCoinc T) (τ : ℍ) (t : ℝ),
      ‖(τ : ℂ) - (((p : ℍ × ℝ).1) : ℂ)‖ < ρf p → |t - (p : ℍ × ℝ).2| < ρf p →
      (1 : ℝ) / 2 < t → ‖Work.Kernels.Kfun ℓ d τ (zz t)‖ ≤ Cf p :=
    fun p => (hrest p).2.2
  have hVopen : ∀ p : BadCoinc T, IsOpen {q : ℍ × ℝ |
      ‖(q.1 : ℂ) - (((p : ℍ × ℝ).1) : ℂ)‖ < ρf p ∧ |q.2 - (p : ℍ × ℝ).2| < ρf p
        ∧ (1 : ℝ) / 2 < q.2} := by
    intro p
    exact IsOpen.inter
      (isOpen_lt (continuous_norm.comp ((UpperHalfPlane.continuous_coe.comp continuous_fst).sub
        continuous_const)) continuous_const)
      (IsOpen.inter (isOpen_lt (continuous_snd.sub continuous_const).abs continuous_const)
        (isOpen_lt continuous_const continuous_snd))
  have hVmem : ∀ p : BadCoinc T, (p : ℍ × ℝ) ∈ {q : ℍ × ℝ |
      ‖(q.1 : ℂ) - (((p : ℍ × ℝ).1) : ℂ)‖ < ρf p ∧ |q.2 - (p : ℍ × ℝ).2| < ρf p
        ∧ (1 : ℝ) / 2 < q.2} := by
    intro p
    exact ⟨by rw [sub_self, norm_zero]; exact hρf p,
      by rw [sub_self, abs_zero]; exact hρf p, by have := p.2.2.1; linarith⟩
  obtain ⟨s, hs⟩ := (isCompact_BadCoinc hT).elim_finite_subcover
    (fun p : BadCoinc T => {q : ℍ × ℝ |
      ‖(q.1 : ℂ) - (((p : ℍ × ℝ).1) : ℂ)‖ < ρf p ∧ |q.2 - (p : ℍ × ℝ).2| < ρf p
        ∧ (1 : ℝ) / 2 < q.2})
    hVopen (fun q hq => Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hVmem ⟨q, hq⟩⟩)
  set U : Set (ℍ × ℝ) := ⋃ p ∈ s, {q : ℍ × ℝ |
      ‖(q.1 : ℂ) - (((p : ℍ × ℝ).1) : ℂ)‖ < ρf p ∧ |q.2 - (p : ℍ × ℝ).2| < ρf p
        ∧ (1 : ℝ) / 2 < q.2} with hU
  have hUopen : IsOpen U := isOpen_biUnion fun p _ => hVopen p
  have hBadsU : BadCoinc T ⊆ U := hs
  have hUbound : ∀ q ∈ U, ‖Work.Kernels.Kfun ℓ d q.1 (zz q.2)‖ ≤ (∑ p ∈ s, Cf p) + 1 := by
    intro q hq
    rw [hU, Set.mem_iUnion₂] at hq
    obtain ⟨p, hps, h1, h2, h3⟩ := hq
    have hb := hbound p q.1 q.2 h1 h2 h3
    have hle : Cf p ≤ ∑ p ∈ s, Cf p := Finset.single_le_sum (fun x _ => hCf x) hps
    linarith
  have hK : IsCompact (closure (arcT : Set ℍ) ×ˢ Set.Icc (1 : ℝ) T) :=
    isCompact_closure_arcT'.prod isCompact_Icc
  have hKc : IsCompact ((closure (arcT : Set ℍ) ×ˢ Set.Icc (1 : ℝ) T) \ U) :=
    hK.inter_right hUopen.isClosed_compl
  have hcontOn : ContinuousOn (fun q : ℍ × ℝ => Work.Kernels.Kfun ℓ d q.1 (zz q.2))
      ((closure (arcT : Set ℍ) ×ˢ Set.Icc (1 : ℝ) T) \ U) := by
    intro q hq
    have hq1 : q.1 ∈ closure arcT := hq.1.1
    have hq2 : q.2 ∈ Set.Icc (1 : ℝ) T := hq.1.2
    have hclean : Work.Kernels.jInvariantFun q.1 ≠ Work.Kernels.jInvariantFun (zz q.2) := by
      intro hc
      exact hq.2 (hBadsU ⟨hq1, hq2.1, hq2.2, hc⟩)
    have hΦ : ContinuousAt (fun q' : ℍ × ℝ => (q'.1, zz q'.2)) q :=
      ContinuousAt.prodMk continuousAt_fst (continuous_zz.comp continuous_snd).continuousAt
    have hKfun : ContinuousAt (fun p : ℍ × ℍ => Work.Kernels.Kfun ℓ d p.1 p.2) (q.1, zz q.2) :=
      continuousAt_Kfun_of_clean hd hclean
    exact (hKfun.comp (x := q) hΦ).continuousWithinAt
  obtain ⟨B₂, hB₂⟩ := hKc.exists_bound_of_continuousOn hcontOn
  refine ⟨max (max ((∑ p ∈ s, Cf p) + 1) B₂) 0, le_max_right _ _, fun τ t hτ ht1 htT => ?_⟩
  have hsum : (∑ p ∈ s, Cf p) + 1 ≤ max (max ((∑ p ∈ s, Cf p) + 1) B₂) 0 :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hB₂' : B₂ ≤ max (max ((∑ p ∈ s, Cf p) + 1) B₂) 0 :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hτhalf : (1 : ℝ) / 2 ≤ t := by linarith
  have hτpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  rw [Kaxis_eq_Kfun_zz hτpos hτhalf τ]
  by_cases hUq : (τ, t) ∈ U
  · exact le_trans (hUbound (τ, t) hUq) hsum
  · exact le_trans (hB₂ (τ, t) ⟨⟨subset_closure hτ, ht1, htT⟩, hUq⟩) hB₂'

/-! ## The difference with the non-decaying part -/

/-- **Boundedness of `Kaxis - Aexp` on `arcT × [1,T]`.** -/
theorem arcT_smallT (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (T : ℝ) (hT : 1 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ : ℍ) (t : ℝ), τ ∈ arcT → 1 ≤ t → t ≤ T →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Aexp (Gcusp ℓ d) τ t‖ ≤ B := by
  obtain ⟨C₁, hC₁, hb₁⟩ := arcT_Kaxis_bound ℓ d hd T hT
  obtain ⟨C₂, hC₂, hb₂⟩ := arcT_Aexp_bound ℓ d hd T
  refine ⟨C₁ + C₂ + 1, by positivity, fun τ t hτ ht1 htT => ?_⟩
  refine le_trans (norm_sub_le _ _) (le_trans (add_le_add (hb₁ τ t hτ ht1 htT)
    (hb₂ τ t hτ ht1 htT)) (by linarith))

end Work.Asymptotics
