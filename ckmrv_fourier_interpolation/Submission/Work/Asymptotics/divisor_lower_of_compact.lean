/-
# The CKMRV divisor is bounded below on any compact set of contour heights

`Work.Asymptotics.divisor_lower_compact` bounds `‖growthPrefactor d τ (imagAxis t ·)‖` below on
the fixed interval `[δ, 1/δ]`, assuming the contour `z = it` carries no pole for *every* `t > 0`.
Here the interval is replaced by an arbitrary compact set `K ⊆ (0,∞)` of heights, and cleanliness
is required only on `K`.  This is the form needed on the clean contour of the CKMRV continuation,
where the removed intervals destroy cleanliness at some heights inside every fixed interval.
-/
import Mathlib
import Submission.Work.Kernels.All

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups Topology

namespace Work.Asymptotics

open Work.Kernels

/-- The point `it` of the imaginary axis is the half-plane point attached to `I * t`. -/
private lemma imagAxis_eq_ofComplex (t : ℝ) (ht : 0 < t) :
    imagAxis t ht = UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)) := by
  rw [show UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))
        = ⟨Complex.I * (t : ℂ), by simpa using ht⟩ from
      UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using ht)]
  apply UpperHalfPlane.ext
  show (t : ℂ) * Complex.I = Complex.I * (t : ℂ)
  rw [mul_comm]

/-- **The divisor is bounded below on a compact set of contour heights.**  For a compact set
`K ⊆ (0,∞)` of heights on which the contour carries no pole of `K^{(d)}` on the closed ball of
radius `R` around `τ₀`, the CKMRV divisor `Δ(τ)Δ(it)^e(j(τ)-j(it))` is bounded below. -/
theorem divisor_lower_of_compact {d : ℕ} {τ₀ : UpperHalfPlane} {R : ℝ} (hR : 0 < R) {K : Set ℝ}
    (hKc : IsCompact K) (hKpos : ∀ t ∈ K, 0 < t)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), t ∈ K → ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), dist τ τ₀ ≤ R → t ∈ K →
      c ≤ ‖Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)‖ := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, fun τ t ht hdist htK => absurd htK (Set.notMem_empty t)⟩
  · -- continuity of `Δ` and `j` on `ℍ`.
    have hDcont : Continuous (fun τ : ℍ => Work.Kernels.DeltaFun τ) :=
      (CuspForm.holo' CuspForm.discriminant).continuous
    have hE4cont : Continuous (fun τ : ℍ => Work.Kernels.E4Fun τ) :=
      (ModularForm.holo' ModularForm.E₄).continuous
    have hjcont : Continuous (fun τ : ℍ => Work.Kernels.jInvariantFun τ) := by
      simp only [Work.Kernels.jInvariantFun, Work.Kernels.E4Fun]
      exact (hE4cont.pow 3).div hDcont
        (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
    -- the compact parameter set
    set P : Set (ℍ × ℝ) := Metric.closedBall τ₀ R ×ˢ K with hPdef
    have hPc : IsCompact P :=
      (isCompact_closedBall (x := τ₀) (r := R)).prod hKc
    obtain ⟨t₀, ht₀⟩ := hKne
    have hPne : P.Nonempty := ⟨(τ₀, t₀), Metric.mem_closedBall_self hR.le, ht₀⟩
    have hPsub : P ⊆ Set.univ ×ˢ Set.Ioi (0 : ℝ) := by
      intro p hp
      rw [hPdef, Set.mem_prod] at hp
      exact ⟨trivial, hKpos p.2 hp.2⟩
    have hDcont_univ : ContinuousOn (fun τ : ℍ => Work.Kernels.DeltaFun τ) Set.univ :=
      continuousOn_univ.mpr hDcont
    have hjcont_univ : ContinuousOn (fun τ : ℍ => Work.Kernels.jInvariantFun τ) Set.univ :=
      continuousOn_univ.mpr hjcont
    -- continuity on the parameter set
    have hA : ContinuousOn (fun p : ℍ × ℝ => Work.Kernels.DeltaFun p.1)
        (Set.univ ×ˢ Set.Ioi (0 : ℝ)) :=
      hDcont_univ.comp continuous_fst.continuousOn (fun p _ => trivial)
    have hBv : ContinuousOn
        (fun p : ℍ × ℝ => UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)))
        (Set.univ ×ˢ Set.Ioi (0 : ℝ)) :=
      continuousOn_ofComplex_I_mul.comp continuous_snd.continuousOn
        (fun p hp => (Set.mem_prod.mp hp).2)
    have hB : ContinuousOn
        (fun p : ℍ × ℝ => Work.Kernels.DeltaFun
          (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)))) (Set.univ ×ˢ Set.Ioi (0 : ℝ)) :=
      hDcont_univ.comp hBv (fun p _ => trivial)
    have hC : ContinuousOn
        (fun p : ℍ × ℝ => Work.Kernels.jInvariantFun
          (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)))) (Set.univ ×ˢ Set.Ioi (0 : ℝ)) :=
      hjcont_univ.comp hBv (fun p _ => trivial)
    have hC2 : ContinuousOn
        (fun p : ℍ × ℝ => Work.Kernels.jInvariantFun p.1
          - Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ))))
        (Set.univ ×ˢ Set.Ioi (0 : ℝ)) :=
      (hjcont_univ.comp continuous_fst.continuousOn (fun p _ => trivial)).sub hC
    have hprod : ContinuousOn
        (fun p : ℍ × ℝ => Work.Kernels.growthPrefactor d p.1
          (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)))) (Set.univ ×ˢ Set.Ioi (0 : ℝ)) := by
      simp only [Work.Kernels.growthPrefactor]
      exact (hA.mul (hB.pow _)).mul hC2
    have hFcont : ContinuousOn
        (fun p : ℍ × ℝ => ‖Work.Kernels.growthPrefactor d p.1
          (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ)))‖) P :=
      (hprod.norm).mono hPsub
    obtain ⟨p, hpP, hpmin⟩ := hPc.exists_isMinOn hPne hFcont
    -- non-vanishing at the minimiser
    rw [hPdef, Set.mem_prod] at hpP
    have hpball : dist p.1 τ₀ ≤ R := Metric.mem_closedBall.mp hpP.1
    have htpos : 0 < p.2 := hKpos p.2 hpP.2
    have hclean' : Work.Kernels.jInvariantFun p.1
        ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (Complex.I * (p.2 : ℂ))) := by
      have h := hclean p.2 htpos hpP.2 p.1 hpball
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
    intro τ t ht hdist htK
    have hmem : (τ, t) ∈ P := by
      rw [hPdef, Set.mem_prod]
      exact ⟨by rwa [Metric.mem_closedBall], htK⟩
    have hle := (isMinOn_iff.mp hpmin) (τ, t) hmem
    rw [imagAxis_eq_ofComplex t ht]
    exact hle

end Work.Asymptotics
