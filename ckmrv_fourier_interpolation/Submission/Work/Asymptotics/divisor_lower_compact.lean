import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.Divisor

namespace Work.Asymptotics

open Work.Kernels ModularForm
open UpperHalfPlane

/-- The imaginary axis point `it` (`t > 0`) agrees with `ofComplex (I * t)`. -/
private lemma imagAxis_eq_ofComplex (t : ℝ) (ht : 0 < t) :
    imagAxis t ht = UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)) := by
  rw [show UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))
        = ⟨Complex.I * (t : ℂ), by simpa using ht⟩ from
      UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using ht)]
  apply UpperHalfPlane.ext
  show (t : ℂ) * Complex.I = Complex.I * (t : ℂ)
  rw [mul_comm]

/-- **The divisor is bounded below on compact ranges of the contour.**  If on a closed ball of
`τ`'s the contour is pole-free — `j(τ) ≠ j(it)` for every `t > 0` — then on any compact interval
`[δ, 1/δ]` of `t` the CKMRV divisor `Δ(τ)Δ(it)^e(j(τ)-j(it))` is bounded below by a positive
constant.  This is the middle-range ingredient of the contour dominator (the two cusps being
covered by `Work.Asymptotics.growthPrefactor_lower_atTop` and
`Work.Asymptotics.growthPrefactor_lower_atZero`); its proof is continuity plus compactness of
`closedBall τ₀ R × [δ, 1/δ]` and the non-vanishing supplied by the hypothesis. -/
theorem divisor_lower_compact {d : ℕ} (hd : d = 8 ∨ d = 24) {τ₀ : UpperHalfPlane} {R : ℝ}
    (hR : 0 < R)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      dist τ τ₀ ≤ R → δ ≤ t → t ≤ 1 / δ →
      c ≤ ‖Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)‖ := by
  rcases le_or_gt δ 1 with hδle | hδgt
  · -- Main case: `δ ≤ 1`, so `[δ, 1/δ]` is a nonempty compact interval contained in `(0,∞)`.
    have hδinv : δ ≤ 1 / δ := by
      rw [le_div_iff₀ hδ]; nlinarith
    -- Continuity of `Δ` and `j` on `ℍ`.
    have hDcont : Continuous (fun τ : ℍ => Work.Kernels.DeltaFun τ) :=
      (CuspForm.holo' CuspForm.discriminant).continuous
    have hE4cont : Continuous (fun τ : ℍ => Work.Kernels.E4Fun τ) :=
      (ModularForm.holo' ModularForm.E₄).continuous
    have hjcont : Continuous (fun τ : ℍ => Work.Kernels.jInvariantFun τ) := by
      simp only [Work.Kernels.jInvariantFun, Work.Kernels.E4Fun]
      exact (hE4cont.pow 3).div hDcont
        (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
    -- The compact parameter set.
    set K : Set (ℍ × ℝ) := Metric.closedBall τ₀ R ×ˢ Set.Icc δ (1 / δ) with hKdef
    have hKc : IsCompact K := by
      rw [hKdef]; exact (isCompact_closedBall (x := τ₀) (r := R)).prod isCompact_Icc
    have hKne : K.Nonempty := by
      refine ⟨(τ₀, δ), ?_⟩
      rw [hKdef, Set.mem_prod]
      exact ⟨Metric.mem_closedBall_self hR.le, ⟨le_rfl, hδinv⟩⟩
    have hKsub : K ⊆ Set.univ ×ˢ Set.Ioi 0 := by
      intro p hp
      rw [hKdef, Set.mem_prod] at hp
      exact ⟨trivial, lt_of_lt_of_le hδ (Set.mem_Icc.mp hp.2).1⟩
    have hDcont_univ : ContinuousOn (fun τ : ℍ => Work.Kernels.DeltaFun τ) Set.univ :=
      continuousOn_univ.mpr hDcont
    have hjcont_univ : ContinuousOn (fun τ : ℍ => Work.Kernels.jInvariantFun τ) Set.univ :=
      continuousOn_univ.mpr hjcont
    -- Continuity on the parameter set.
    have hA : ContinuousOn (fun p : ℍ × ℝ => Work.Kernels.DeltaFun p.1)
        (Set.univ ×ˢ Set.Ioi 0) :=
      hDcont_univ.comp continuous_fst.continuousOn (fun p _ => trivial)
    have hBv : ContinuousOn
        (fun p : ℍ × ℝ => UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)))
        (Set.univ ×ˢ Set.Ioi 0) :=
      continuousOn_ofComplex_I_mul.comp continuous_snd.continuousOn
        (fun p hp => (Set.mem_prod.mp hp).2)
    have hB : ContinuousOn
        (fun p : ℍ × ℝ => Work.Kernels.DeltaFun
          (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)))) (Set.univ ×ˢ Set.Ioi 0) :=
      hDcont_univ.comp hBv (fun p _ => trivial)
    have hC : ContinuousOn
        (fun p : ℍ × ℝ => Work.Kernels.jInvariantFun
          (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)))) (Set.univ ×ˢ Set.Ioi 0) :=
      hjcont_univ.comp hBv (fun p _ => trivial)
    have hC2 : ContinuousOn
        (fun p : ℍ × ℝ => Work.Kernels.jInvariantFun p.1
          - Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ))))
        (Set.univ ×ˢ Set.Ioi 0) :=
      (hjcont_univ.comp continuous_fst.continuousOn (fun p _ => trivial)).sub hC
    have hprod : ContinuousOn
        (fun p : ℍ × ℝ => Work.Kernels.growthPrefactor d p.1
          (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)))) (Set.univ ×ˢ Set.Ioi 0) := by
      simp only [Work.Kernels.growthPrefactor]
      exact (hA.mul (hB.pow _)).mul hC2
    have hFcont : ContinuousOn
        (fun p : ℍ × ℝ => ‖Work.Kernels.growthPrefactor d p.1
          (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)))‖) K :=
      (hprod.norm).mono hKsub
    obtain ⟨p, hpK, hpmin⟩ := hKc.exists_isMinOn hKne hFcont
    -- Non-vanishing at the minimiser.
    rw [hKdef, Set.mem_prod] at hpK
    have hpball : dist p.1 τ₀ ≤ R := Metric.mem_closedBall.mp hpK.1
    have htpos : 0 < p.2 := lt_of_lt_of_le hδ (Set.mem_Icc.mp hpK.2).1
    have hclean' : Work.Kernels.jInvariantFun p.1
        ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ))) := by
      have h := hclean p.2 htpos p.1 hpball
      rwa [imagAxis_eq_ofComplex p.2 htpos] at h
    have hne : Work.Kernels.growthPrefactor d p.1
        (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ))) ≠ 0 := by
      simp only [Work.Kernels.growthPrefactor]
      intro h
      rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact Work.Kernels.ClassicalFacts.DeltaFun_ne_zero p.1 h''
        · exact (pow_ne_zero _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)) h''
      · exact hclean' (sub_eq_zero.mp h')
    refine ⟨‖Work.Kernels.growthPrefactor d p.1
        (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)))‖, norm_pos_iff.mpr hne, ?_⟩
    intro τ t ht hdist hδt htδ
    have hmem : (τ, t) ∈ K := by
      rw [hKdef, Set.mem_prod]
      exact ⟨by rwa [Metric.mem_closedBall], ⟨hδt, htδ⟩⟩
    have hle := (isMinOn_iff.mp hpmin) (τ, t) hmem
    rw [imagAxis_eq_ofComplex t ht]
    exact hle
  · -- Degenerate case: `1 < δ`, so the constraints `δ ≤ t ≤ 1/δ` are contradictory.
    refine ⟨1, one_pos, ?_⟩
    intro τ t ht hdist hδt htδ
    exfalso
    have hlt : 1 / δ < 1 := by rw [div_lt_one hδ]; exact hδgt
    linarith

end Work.Asymptotics
