import Mathlib
import Submission.Work.Asymptotics.TSasm.layerSemi_lowHalfFunnelNegRe
import Submission.Work.Asymptotics.TSasm.layerSemi_Tregion
import Submission.Work.Asymptotics.TSasm.LayerSemiBlLowTS
import Submission.Work.Asymptotics.TSasm.paperLayer_vadd_shift
import Submission.Work.Asymptotics.Kcomp_isCompact_subset

/-!
# The `r`-seminorm bound of the CKMRV layer on the low strip `{1/2 ≤ Im τ ≤ 2} ∩ 𝒟`

The paper's layer `F₂` (`Work.Asymptotics.layer (Gcusp ℓ d) ℓ d τ ·`) has `τ`-uniformly bounded
weighted `r`-seminorms `|r|^k ∂_r^l` on the low strip of `𝒟`.  This is a piece of the input (f1)
of `Submission/Work/CKFinal/DESIGN.md` (the `𝒟`-input `paperLayer_seminorm_DomainD`).

The strip `S = {τ ∈ 𝒟 : 1/2 ≤ Im τ ≤ 2}` is *not* relatively compact in `𝒟` (the bad lines
`Re τ = ±1` and the tangency points `±1/2 + i/2` of `∂𝒟` are in its closure), so it is split into
three pieces:

* `|Re τ| > 3/4`: the low bad-line region `HalfFunnel.lowBadSet`, where the layer agrees
  pointwise with the translate-pole layer `blLowF2` — `Work.Asymptotics.layer_lowBadSet_seminorm`;
* `|Re τ| ≤ 3/4`, `Im τ ≤ 3/2`: here `Re τ² + (Im τ - 1)² ≤ 13/16 < 1`, so `Im (S • τ) ≥ 1/2`
  and `τ` lies in the cusp-`0` half tile `Tregion` — `Work.Asymptotics.layerSemi_Tregion`;
* `|Re τ| ≤ 3/4`, `3/2 ≤ Im τ ≤ 2`: the compact box `lowStripK`, which lies in `𝒟` with margin
  (`Im τ ≥ 3/2`), so the compact bound `Work.Asymptotics.layer_seminorm_on_compact` applies.

Each piece carries a bound with a constant *independent of `τ`*; taking `N = 0` in the
`C · (scale τ)^N` formulation gives the statement.
-/

namespace Work.CKFinal

open UpperHalfPlane

/-- The compact top piece of the low strip: `|Re τ| ≤ 3/4` and `3/2 ≤ Im τ ≤ 2`.  It lies in `𝒟`
because `Im τ ≥ 3/2` forces `‖τ ∓ 1/2‖ ≥ 3/2 > 1/2`. -/
def lowStripK : Set ℍ :=
  {τ : ℍ | |τ.re| ≤ 3 / 4 ∧ (3 : ℝ) / 2 ≤ τ.im ∧ τ.im ≤ 2}

lemma mem_lowStripK {τ : ℍ} :
    τ ∈ lowStripK ↔ |τ.re| ≤ 3 / 4 ∧ (3 : ℝ) / 2 ≤ τ.im ∧ τ.im ≤ 2 := Iff.rfl

private lemma isClosed_lowStripK : IsClosed lowStripK := by
  have h1 : IsClosed {τ : ℍ | |τ.re| ≤ (3 : ℝ) / 4} :=
    isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
  have h2 : IsClosed {τ : ℍ | (3 : ℝ) / 2 ≤ τ.im} :=
    isClosed_le continuous_const UpperHalfPlane.continuous_im
  have h3 : IsClosed {τ : ℍ | τ.im ≤ 2} :=
    isClosed_le UpperHalfPlane.continuous_im continuous_const
  have h : lowStripK = {τ : ℍ | |τ.re| ≤ (3 : ℝ) / 4} ∩ {τ : ℍ | (3 : ℝ) / 2 ≤ τ.im} ∩
      {τ : ℍ | τ.im ≤ 2} := by
    ext τ; simp [lowStripK, and_assoc]
  rw [h]
  exact (h1.inter h2).inter h3

private lemma isBounded_lowStripK : Bornology.IsBounded lowStripK := by
  rw [Metric.isBounded_iff_subset_closedBall (⟨Complex.I, by simp⟩ : ℍ)]
  refine ⟨3, fun τ hτ => ?_⟩
  obtain ⟨hre, hlo, hhi⟩ := mem_lowStripK.mp hτ
  rw [Metric.mem_closedBall]
  have hstep : dist τ (⟨Complex.I, by simp⟩ : ℍ)
      ≤ ‖(τ : ℂ) - Complex.I‖ / Real.sqrt (τ.im * 1) := by
    have hh := UpperHalfPlane.dist_le_dist_coe_div_sqrt τ (⟨Complex.I, by simp⟩ : ℍ)
    rw [dist_eq_norm] at hh
    rw [show (↑(⟨Complex.I, by simp⟩ : ℍ) : ℂ) = Complex.I from rfl,
        show (⟨Complex.I, by simp⟩ : ℍ).im = 1 from rfl] at hh
    simpa using hh
  have hnum : ‖(τ : ℂ) - Complex.I‖ ≤ 3 := by
    have h := Complex.norm_le_abs_re_add_abs_im ((τ : ℂ) - Complex.I)
    rw [show ((τ : ℂ) - Complex.I).re = τ.re by simp,
        show ((τ : ℂ) - Complex.I).im = τ.im - 1 by simp] at h
    have hre' : |τ.re| ≤ 3 / 4 := hre
    have him' : |τ.im - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hden : (1 : ℝ) ≤ Real.sqrt (τ.im * 1) := by
    rw [Real.one_le_sqrt]; linarith
  calc dist τ (⟨Complex.I, by simp⟩ : ℍ) ≤ ‖(τ : ℂ) - Complex.I‖ / Real.sqrt (τ.im * 1) :=
        hstep
    _ ≤ 3 / 1 := div_le_div₀ (by norm_num) hnum (by norm_num) hden
    _ = 3 := by norm_num

lemma isCompact_lowStripK : IsCompact lowStripK := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨isClosed_lowStripK, isBounded_lowStripK⟩

lemma lowStripK_subset_DomainD : lowStripK ⊆ Work.Asymptotics.DomainD := by
  intro τ hτ
  obtain ⟨hre, hlo, hhi⟩ := mem_lowStripK.mp hτ
  have habs : |τ.re| ≤ 3 / 4 := hre
  rw [Work.Asymptotics.mem_DomainD]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [(abs_le.mp habs).1]
  · linarith [(abs_le.mp habs).2]
  · have hsq : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (τ.re - 1 / 2) ^ 2 + τ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      norm_num [Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hgt : ((1 : ℝ) / 2) ^ 2 < ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg (τ.re - 1 / 2), hlo]
    nlinarith [norm_nonneg ((τ : ℂ) - (1 / 2 : ℂ)), hgt]
  · have hsq : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (τ.re + 1 / 2) ^ 2 + τ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
        UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      norm_num [Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hgt : ((1 : ℝ) / 2) ^ 2 < ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg (τ.re + 1 / 2), hlo]
    nlinarith [norm_nonneg ((τ : ℂ) + (1 / 2 : ℂ)), hgt]

/-- The elementary identity `‖τ‖² = (Re τ)² + (Im τ)²` on `ℍ`. -/
private lemma normSq_coe (τ : ℍ) : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- **`Tregion` from the elementary inequalities.**  If `|Re τ| ≤ 3/4` and `1/2 ≤ Im τ ≤ 3/2`,
then `Re τ² + (Im τ - 1)² ≤ 13/16 < 1`, i.e. `Im (S • τ) ≥ 1/2`; with `Im τ ≥ 1/2` the upper bound
`Im (S • τ) ≤ 2` is automatic. -/
lemma mem_Tregion_of_le (τ : ℍ) (hτ : τ ∈ Work.Asymptotics.DomainD) (hlo : (1 : ℝ) / 2 ≤ τ.im)
    (him3 : τ.im ≤ 3 / 2) (hre : |τ.re| ≤ 3 / 4) : τ ∈ Work.Asymptotics.Tregion := by
  rw [Work.Asymptotics.mem_Tregion]
  refine ⟨hτ, ?_, Work.Asymptotics.im_S_smul_le_two_of_half_le_im hlo⟩
  have hpos : 0 < τ.re ^ 2 + τ.im ^ 2 := by nlinarith [τ.im_pos, sq_nonneg τ.re]
  have hS : (ModularGroup.S • τ).im = τ.im / (τ.re ^ 2 + τ.im ^ 2) := by
    rw [Work.Asymptotics.lowNeg_im_S_smul, normSq_coe]
  rw [hS, le_div_iff₀ hpos]
  have hre_sq : τ.re ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := by
    nlinarith [sq_abs τ.re, abs_nonneg τ.re, abs_le.mp hre]
  have him_sq : (τ.im - 1) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have h1 : |τ.im - 1| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [sq_abs (τ.im - 1), abs_nonneg (τ.im - 1), h1]
  nlinarith [hre_sq, him_sq]

/-- **Cover of the low strip** by the bad lines `|Re τ| > 3/4`, the half tile `Tregion` and the
compact box `lowStripK`. -/
lemma lowstrip_cover (τ : ℍ) (hτ : τ ∈ Work.Asymptotics.DomainD) (hlo : (1 : ℝ) / 2 ≤ τ.im)
    (hhi : τ.im ≤ 2) :
    (3 / 4 < τ.re ∨ τ.re < -(3 / 4)) ∨ τ ∈ Work.Asymptotics.Tregion ∨
      (|τ.re| ≤ 3 / 4 ∧ (3 : ℝ) / 2 ≤ τ.im) := by
  by_cases hre : |τ.re| ≤ 3 / 4
  · by_cases him : τ.im ≤ 3 / 2
    · exact Or.inr (Or.inl (mem_Tregion_of_le τ hτ hlo him hre))
    · rw [not_le] at him
      exact Or.inr (Or.inr ⟨hre, him.le⟩)
  · have h : (3 : ℝ) / 4 < |τ.re| := lt_of_not_ge hre
    rcases lt_abs.mp h with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (by linarith))

theorem layer_semi_lowstrip (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (τ : UpperHalfPlane), τ ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ τ.im →
        τ.im ≤ 2 → ∀ r : ℝ,
        |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
          ≤ C * (Work.Kernels.scale τ) ^ N := by
  intro k l
  -- the three region bounds, each with a constant independent of `τ`
  obtain ⟨CA, hCA, hA⟩ := Work.Asymptotics.layer_lowBadSet_seminorm ℓ d hd k l
  obtain ⟨CB, hCB, hB⟩ := Work.Asymptotics.layerSemi_Tregion ℓ d hd k l
  have hG : ∀ i j : Fin 2,
      Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (Work.Asymptotics.Gcusp ℓ d i j) :=
    fun i j => Work.HFN.Gcusp_moderate ℓ d i j
  have h8 : d = 8 → ∀ j : Fin 2, Work.Asymptotics.Gcusp ℓ d 1 j = 0 := by
    intro h8d j
    rw [Work.Asymptotics.Gcusp, if_pos h8d]
    funext τ
    fin_cases j <;> simp [Work.Asymptotics.Gcusp8]
  obtain ⟨CK, hCK, hK⟩ := Work.HFN.layer_seminorm_on_compact ℓ d hd
    (Work.Asymptotics.Gcusp ℓ d) hG h8 isCompact_lowStripK lowStripK_subset_DomainD
    (fun N hN => Work.Asymptotics.MFix.Kaxis_local_flat ℓ d hd isCompact_lowStripK
      lowStripK_subset_DomainD N hN)
    (Work.HFN.cusp_expansion_of_kernel ℓ d hd isCompact_lowStripK
      lowStripK_subset_DomainD) k l
  refine ⟨CA + CB + CK, 0, by linarith, le_rfl, ?_⟩
  intro τ hτD hlo hhi r
  rw [Real.rpow_zero, mul_one]
  have key : |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
      Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖ ≤ CA + CB + CK := by
    rcases lowstrip_cover τ hτD hlo hhi with hbad | hT | htop
    · exact le_trans (hA τ r ⟨hτD, hlo, hhi, hbad⟩) (by linarith)
    · exact le_trans (hB τ r hT) (by linarith)
    · obtain ⟨hre, him⟩ := htop
      exact le_trans (hK τ r (mem_lowStripK.mpr ⟨hre, him, hhi⟩)) (by linarith)
  linarith

end Work.CKFinal
