import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KaxisMid.Classify

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped Topology MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics.CuspDecay

open Work.Kernels

/-- The half-plane point attached to the real parameter `s`: for `s > 0` this is the point
`i s` of the imaginary axis. -/
def imagPt (s : ℝ) : ℍ := UpperHalfPlane.ofComplex (Complex.I * (s : ℂ))

/-- For `s > 0` the point `imagPt s` really is `i s`. -/
lemma coe_imagPt {s : ℝ} (hs : 0 < s) :
    ((imagPt s : ℍ) : ℂ) = Complex.I * (s : ℂ) := by
  have hz : 0 < (Complex.I * (s : ℂ)).im := by
    rw [Complex.mul_im]; simp [hs]
  have h := UpperHalfPlane.ofComplex_apply_of_im_pos hz
  change ((↑(UpperHalfPlane.ofComplex (Complex.I * (s : ℂ))) : ℂ)) = Complex.I * (s : ℂ)
  rw [h]

/-- `s ↦ i s` is continuous on the positive half-line. -/
lemma continuousOn_imagPt : ContinuousOn imagPt (Set.Ioi (0 : ℝ)) := by
  unfold imagPt
  simpa using UpperHalfPlane.continuousOn_ofComplex_I_mul

/-- A point of the imaginary axis is `i` times its imaginary part. -/
lemma coe_eq_I_mul_im {z : ℍ} (h : z.re = 0) : (z : ℂ) = Complex.I * (z.im : ℂ) := by
  have hh := Complex.re_add_im (z : ℂ)
  have hre : (z : ℂ).re = 0 := by rw [UpperHalfPlane.coe_re]; exact h
  rw [hre, UpperHalfPlane.coe_im] at hh
  rw [← hh]; simp [mul_comm]

/-- A point of the imaginary axis is reconstructed from its imaginary part. -/
lemma imagPt_im {z : ℍ} (h : z.re = 0) : imagPt z.im = z := by
  have h1 : imagPt z.im = UpperHalfPlane.ofComplex (z : ℂ) := by
    unfold imagPt
    rw [coe_eq_I_mul_im h]
  rw [h1, UpperHalfPlane.ofComplex_apply]

/-- **Lower bound for `‖j u - j σ‖` on the compact "box" region.**

For a box `{u : |Re u| ≤ 1/2, 2 ≤ Im u ≤ B}` in the `τ`-variable and a point `σ = i s` of the
imaginary axis of height `s ∈ [1,2]`, the `j`-invariant difference is bounded below by a positive
constant as soon as the two points are at distance `≥ ρ > 0` (all three constants are fixed
beforehand).

The proof is compactness: the parameter space
`{u : |Re u| ≤ 1/2, 2 ≤ Im u ≤ B} × {s ∈ [1,2]} ∩ {‖u - i s‖ ≥ ρ}` is closed and bounded in
`ℂ × ℝ`, hence compact, the function `(u,s) ↦ ‖j u - j(i s)‖` is continuous there, and it vanishes
nowhere: `j u = j(i s)` with `u ∈ 𝒟` would force `i s = u` or `i s = S • u`
(`Work.Asymptotics.KaxisMid.eq_or_eq_S_of_re_eq_zero`); the first contradicts `‖u - i s‖ ≥ ρ > 0`,
and the second gives `u = S • (i s) = i/s`, whose imaginary part `1/s ≤ 1` contradicts `2 ≤ Im u`. -/
theorem box_j_lower (B ρ : ℝ) (hB : 2 ≤ B) (hρ : 0 < ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (u σ : UpperHalfPlane),
      |u.re| ≤ 1 / 2 → 2 ≤ u.im → u.im ≤ B → σ.re = 0 → 1 ≤ σ.im → σ.im ≤ 2 →
      ρ ≤ ‖(u : ℂ) - (σ : ℂ)‖ →
        c ≤ ‖Work.Kernels.jInvariantFun u - Work.Kernels.jInvariantFun σ‖ := by
  have hBpos : (0 : ℝ) < B := by linarith
  -- the reference point and the radius of the compact ball containing the box
  set R : ℝ := B + 1 with hRdef
  set τ₀ : ℍ := ⟨(B : ℂ) * Complex.I, by
    rw [Complex.mul_im]; simp [hBpos]⟩ with hτ₀def
  have hτ₀im : τ₀.im = B := by
    show ((B : ℂ) * Complex.I).im = B
    rw [Complex.mul_im]; simp
  have hτ₀coe : ((τ₀ : ℍ) : ℂ) = (B : ℂ) * Complex.I := rfl
  -- the compact parameter set
  set P : Set (ℍ × ℝ) :=
    {p | |p.1.re| ≤ 1 / 2 ∧ 2 ≤ p.1.im ∧ p.1.im ≤ B ∧ 1 ≤ p.2 ∧ p.2 ≤ 2 ∧
      ρ ≤ ‖(p.1 : ℂ) - Complex.I * (p.2 : ℂ)‖} with hPdef
  have memP : ∀ p : ℍ × ℝ, p ∈ P ↔ |p.1.re| ≤ 1 / 2 ∧ 2 ≤ p.1.im ∧ p.1.im ≤ B ∧
      1 ≤ p.2 ∧ p.2 ≤ 2 ∧ ρ ≤ ‖(p.1 : ℂ) - Complex.I * (p.2 : ℂ)‖ := by
    intro p; rw [hPdef, Set.mem_ofPred_eq]
  -- continuity of `j`
  have hjcont : Continuous (fun τ : ℍ => Work.Kernels.jInvariantFun τ) := by
    have hDcont : Continuous (fun τ : ℍ => Work.Kernels.DeltaFun τ) :=
      (CuspForm.holo' CuspForm.discriminant).continuous
    have hE4cont : Continuous (fun τ : ℍ => Work.Kernels.E4Fun τ) :=
      (ModularForm.holo' ModularForm.E₄).continuous
    simp only [Work.Kernels.jInvariantFun, Work.Kernels.E4Fun]
    exact (hE4cont.pow 3).div hDcont
      (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
  -- `P` is closed
  have hclosed : IsClosed P := by
    have h1 : IsClosed {p : ℍ × ℝ | |p.1.re| ≤ 1 / 2} :=
      isClosed_le (continuous_abs.comp (UpperHalfPlane.continuous_re.comp continuous_fst))
        continuous_const
    have h2 : IsClosed {p : ℍ × ℝ | 2 ≤ p.1.im} :=
      isClosed_le continuous_const (UpperHalfPlane.continuous_im.comp continuous_fst)
    have h3 : IsClosed {p : ℍ × ℝ | p.1.im ≤ B} :=
      isClosed_le (UpperHalfPlane.continuous_im.comp continuous_fst) continuous_const
    have h4 : IsClosed {p : ℍ × ℝ | 1 ≤ p.2} :=
      isClosed_le continuous_const continuous_snd
    have h5 : IsClosed {p : ℍ × ℝ | p.2 ≤ 2} :=
      isClosed_le continuous_snd continuous_const
    have h6 : IsClosed {p : ℍ × ℝ | ρ ≤ ‖(p.1 : ℂ) - Complex.I * (p.2 : ℂ)‖} :=
      isClosed_le continuous_const
        (((UpperHalfPlane.continuous_coe.comp continuous_fst).sub
          (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd))).norm)
    rw [hPdef]
    rw [show {p : ℍ × ℝ | |p.1.re| ≤ 1 / 2 ∧ 2 ≤ p.1.im ∧ p.1.im ≤ B ∧ 1 ≤ p.2 ∧
        p.2 ≤ 2 ∧ ρ ≤ ‖(p.1 : ℂ) - Complex.I * (p.2 : ℂ)‖}
      = {p : ℍ × ℝ | |p.1.re| ≤ 1 / 2} ∩ {p | 2 ≤ p.1.im} ∩ {p | p.1.im ≤ B} ∩
        {p | 1 ≤ p.2} ∩ {p | p.2 ≤ 2} ∩
        {p | ρ ≤ ‖(p.1 : ℂ) - Complex.I * (p.2 : ℂ)‖} from by
      ext p; simp [and_assoc]]
    exact ((((h1.inter h2).inter h3).inter h4).inter h5).inter h6
  -- `P` sits inside a compact set
  have hsub : P ⊆ Metric.closedBall τ₀ R ×ˢ Set.Icc (1 : ℝ) 2 := by
    intro p hp
    obtain ⟨hre, him2, himB, hs1, hs2, hdist⟩ := (memP p).mp hp
    refine ⟨?_, ⟨hs1, hs2⟩⟩
    rw [Metric.mem_closedBall]
    have hsq : dist (p.1 : ℂ) (τ₀ : ℂ) ^ 2 = p.1.re ^ 2 + (p.1.im - B) ^ 2 := by
      rw [dist_eq_norm, hτ₀coe, Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        zero_add, add_zero, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    have hb1 : p.1.re ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      have := abs_le.mp hre
      nlinarith [this.1, this.2]
    have hb2 : (p.1.im - B) ^ 2 ≤ (B - 2) ^ 2 := by
      rw [← sq_abs (p.1.im - B)]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      rw [abs_le]; constructor <;> linarith
    have hfin : dist (p.1 : ℂ) (τ₀ : ℂ) ^ 2 ≤ R ^ 2 := by
      rw [hsq, hRdef]; nlinarith [hb1, hb2, hB]
    have hdn : 0 ≤ dist (p.1 : ℂ) (τ₀ : ℂ) := dist_nonneg
    have hdc : dist (p.1 : ℂ) (τ₀ : ℂ) ≤ R := by
      rw [hRdef] at hfin ⊢
      nlinarith [hfin, hdn, sq_nonneg (B + 1)]
    have hs : (1 : ℝ) ≤ Real.sqrt (p.1.im * τ₀.im) := by
      rw [hτ₀im, Real.one_le_sqrt]; nlinarith
    refine le_trans (UpperHalfPlane.dist_le_dist_coe_div_sqrt p.1 τ₀) ?_
    refine le_trans (div_le_self hdn hs) ?_
    exact hdc
  have hcomp : IsCompact (Metric.closedBall τ₀ R ×ˢ Set.Icc (1 : ℝ) 2) :=
    (isCompact_closedBall τ₀ R).prod isCompact_Icc
  have hPc : IsCompact P := IsCompact.of_isClosed_subset hcomp hclosed hsub
  rcases P.eq_empty_or_nonempty with hPe | hPne
  · -- the parameter set is empty: the statement is vacuous
    refine ⟨1, one_pos, fun u σ _ _ _ hσ0 hσ1 hσ2 hdist => ?_⟩
    exact absurd ((memP (u, σ.im)).mpr ⟨‹|u.re| ≤ 1 / 2›, ‹2 ≤ u.im›, ‹u.im ≤ B›, hσ1, hσ2, by
      rw [← coe_eq_I_mul_im hσ0]; exact hdist⟩) (by rw [hPe]; exact Set.notMem_empty _)
  · -- main case: the minimiser
    have hcont : ContinuousOn (fun p : ℍ × ℝ =>
        ‖Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun (imagPt p.2)‖) P := by
      have hbcont : ContinuousOn (fun p : ℍ × ℝ => imagPt p.2) P :=
        continuousOn_imagPt.comp continuous_snd.continuousOn
          (fun p hp => lt_of_lt_of_le zero_lt_one ((memP p).mp hp).2.2.2.1)
      exact (((hjcont.continuousOn (s := Set.univ)).comp continuous_fst.continuousOn
          (fun p _ => trivial)).sub
        ((hjcont.continuousOn (s := Set.univ)).comp hbcont (fun p _ => trivial))).norm
    obtain ⟨p, hpP, hpmin⟩ := hPc.exists_isMinOn hPne hcont
    obtain ⟨hp1re, hp1im2, hp1imB, hp2ge, hp2le, hpdist⟩ := (memP p).mp hpP
    have hp2pos : (0 : ℝ) < p.2 := by linarith
    have hbpcoe : ((imagPt p.2 : ℍ) : ℂ) = Complex.I * (p.2 : ℂ) := coe_imagPt hp2pos
    have hbpre : ((imagPt p.2 : ℍ) : ℂ).re = 0 := by rw [hbpcoe]; simp
    -- the minimiser value is positive
    have hΦpos : 0 < ‖Work.Kernels.jInvariantFun p.1
        - Work.Kernels.jInvariantFun (imagPt p.2)‖ := by
      refine lt_of_le_of_ne (norm_nonneg _) (Ne.symm ?_)
      intro hzero
      have hjeq : Work.Kernels.jInvariantFun p.1
          = Work.Kernels.jInvariantFun (imagPt p.2) := sub_eq_zero.mp (norm_eq_zero.mp hzero)
      have himpos : (0 : ℝ) < p.1.im := by linarith
      have huD : p.1 ∈ Work.Asymptotics.DomainD := by
        rw [Work.Asymptotics.mem_DomainD]
        have h1 := abs_le.mp hp1re
        refine ⟨by linarith, by linarith, ?_, ?_⟩
        · have h := Complex.abs_im_le_norm ((p.1 : ℂ) - (1 / 2 : ℂ))
          have him : ((p.1 : ℂ) - (1 / 2 : ℂ)).im = p.1.im := by simp
          rw [him, abs_of_pos himpos] at h
          linarith
        · have h := Complex.abs_im_le_norm ((p.1 : ℂ) + (1 / 2 : ℂ))
          have him : ((p.1 : ℂ) + (1 / 2 : ℂ)).im = p.1.im := by simp
          rw [him, abs_of_pos himpos] at h
          linarith
      rcases Work.Asymptotics.KaxisMid.eq_or_eq_S_of_re_eq_zero huD hbpre hjeq with hcase | hcase
      · -- `i s = u`
        have : ‖(p.1 : ℂ) - Complex.I * (p.2 : ℂ)‖ = 0 := by
          rw [← hbpcoe, hcase, sub_self, norm_zero]
        rw [this] at hpdist; linarith
      · -- `i s = S • u`
        have hcoe' : ((imagPt p.2 : ℍ) : ℂ) = (-(p.1 : ℂ))⁻¹ := by
          rw [hcase]
          exact congrArg (fun w : ℍ => (w : ℂ)) (UpperHalfPlane.modular_S_smul p.1)
        have heq : Complex.I * (p.2 : ℂ) = (-(p.1 : ℂ))⁻¹ := by
          rw [← hbpcoe]; exact hcoe'
        have hnorm := congrArg norm heq
        rw [norm_mul, Complex.norm_I, one_mul, norm_inv, norm_neg] at hnorm
        have hp2norm : ‖((p.2 : ℝ) : ℂ)‖ = p.2 := by
          simp [abs_of_nonneg (le_of_lt hp2pos)]
        rw [hp2norm] at hnorm
        have hule : (2 : ℝ) ≤ ‖(p.1 : ℂ)‖ := by
          have h := Complex.abs_im_le_norm (p.1 : ℂ)
          rw [UpperHalfPlane.coe_im, abs_of_pos himpos] at h
          linarith
        have hpos : 0 < ‖(p.1 : ℂ)‖ := by linarith
        have hinv : ‖(p.1 : ℂ)‖⁻¹ ≤ 1 / 2 := by
          have h := (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 2)).mpr hule
          linarith [h]
        linarith
    refine ⟨‖Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun (imagPt p.2)‖,
      hΦpos, ?_⟩
    intro u σ hu1 hu2 huB hσ0 hσ1 hσ2 hdist
    have hmem : (u, σ.im) ∈ P := by
      refine (memP (u, σ.im)).mpr ⟨hu1, hu2, huB, hσ1, hσ2, ?_⟩
      rw [← coe_eq_I_mul_im hσ0]; exact hdist
    have hle := (isMinOn_iff.mp hpmin) (u, σ.im) hmem
    rw [imagPt_im hσ0] at hle
    exact hle

end Work.Asymptotics.CuspDecay
