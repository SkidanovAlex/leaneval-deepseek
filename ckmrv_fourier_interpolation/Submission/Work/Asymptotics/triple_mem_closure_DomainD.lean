import Mathlib
import Submission.Work.Asymptotics.DomainD

open scoped UpperHalfPlane

namespace Work.Asymptotics

/-- Squared norm of `a + b·i` (`a, b` real). -/
private lemma norm_add_ofReal_mul_I (a b : ℝ) :
    ‖(a : ℂ) + (b : ℂ) * Complex.I‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]
  simp
  ring

/-- Geometric helper for the propagation theorem (declare in namespace `Work.Asymptotics`).
For every `t > 0` there is a point `τ` such that `τ`, `τ + 1` and `τ + 2` all lie in the closure
of the CKMRV fundamental domain `𝒟` — the witness is `τ = -1 + it`, so that `τ + 1 = it` and
`τ + 2 = 1 + it`.  This makes the sets `O ∩ T⁻¹O ∩ T⁻²O` and `SO ∩ T⁻¹SO ∩ T⁻²SO` of CKMRV
Proposition 3.2 nonempty for every open `O ⊇ closure 𝒟`, i.e. the two propagation identities are
not vacuous.  Proof sketch: `τ + 1 = it` lies in the open `𝒟` because `‖it ∓ 1/2‖² = t² + 1/4`;
`-1 + it` and `1 + it` are limits of `-1 + ε + it` resp. `1 - ε + it` with `0 < ε < 1` and
`ε(1-ε) < t²`, which lie in `𝒟`. -/
theorem triple_mem_closure_DomainD {t : ℝ} (ht : 0 < t) :
    ∃ τ : UpperHalfPlane, τ ∈ closure Work.Asymptotics.DomainD ∧
      (1 : ℝ) +ᵥ τ ∈ closure Work.Asymptotics.DomainD ∧
      (2 : ℝ) +ᵥ τ ∈ closure Work.Asymptotics.DomainD := by
  -- the point `it = i t` of the imaginary axis
  let it : ℍ := ⟨(t : ℂ) * Complex.I, by simpa [Complex.mul_im] using ht⟩
  have hit_re : it.re = 0 := by simp [it, Complex.mul_re]
  have hcoe_it : (it : ℂ) = (t : ℂ) * Complex.I := rfl
  -- general membership criterion: a point `x + it` of the imaginary axis with `-1 < x < 1`
  -- whose squared distances to `±1/2` exceed `1/4` lies in `𝒟`
  have key : ∀ x : ℝ, -1 < x → x < 1 → (1 / 2 : ℝ) ^ 2 < (x - 1 / 2) ^ 2 + t ^ 2 →
      (1 / 2 : ℝ) ^ 2 < (x + 1 / 2) ^ 2 + t ^ 2 → x +ᵥ it ∈ DomainD := by
    intro x hx1 hx2 h3 h4
    rw [mem_DomainD]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [UpperHalfPlane.vadd_re, hit_re]; linarith
    · rw [UpperHalfPlane.vadd_re, hit_re]; linarith
    · have hz : ((x +ᵥ it : ℍ) : ℂ) - 1 / 2 = ((x - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
        rw [UpperHalfPlane.coe_vadd, hcoe_it]; push_cast; ring
      have hnorm : ‖((x +ᵥ it : ℍ) : ℂ) - 1 / 2‖ ^ 2 = (x - 1 / 2) ^ 2 + t ^ 2 := by
        rw [hz, norm_add_ofReal_mul_I]
      have hsq : (1 / 2 : ℝ) ^ 2 < ‖((x +ᵥ it : ℍ) : ℂ) - 1 / 2‖ ^ 2 := by rw [hnorm]; exact h3
      have hlt : (1 / 2 : ℝ) < Real.sqrt (‖((x +ᵥ it : ℍ) : ℂ) - 1 / 2‖ ^ 2) :=
        (Real.lt_sqrt (by norm_num)).mpr hsq
      rwa [Real.sqrt_sq (norm_nonneg (((x +ᵥ it : ℍ) : ℂ) - 1 / 2))] at hlt
    · have hz : ((x +ᵥ it : ℍ) : ℂ) + 1 / 2 = ((x + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
        rw [UpperHalfPlane.coe_vadd, hcoe_it]; push_cast; ring
      have hnorm : ‖((x +ᵥ it : ℍ) : ℂ) + 1 / 2‖ ^ 2 = (x + 1 / 2) ^ 2 + t ^ 2 := by
        rw [hz, norm_add_ofReal_mul_I]
      have hsq : (1 / 2 : ℝ) ^ 2 < ‖((x +ᵥ it : ℍ) : ℂ) + 1 / 2‖ ^ 2 := by rw [hnorm]; exact h4
      have hlt : (1 / 2 : ℝ) < Real.sqrt (‖((x +ᵥ it : ℍ) : ℂ) + 1 / 2‖ ^ 2) :=
        (Real.lt_sqrt (by norm_num)).mpr hsq
      rwa [Real.sqrt_sq (norm_nonneg (((x +ᵥ it : ℍ) : ℂ) + 1 / 2))] at hlt
  -- the radius `ε₀ = min (1/2) (t²/2)` of a one-sided neighbourhood of the real axis
  set ε₀ : ℝ := min (1 / 2) (t ^ 2 / 2) with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]; exact lt_min (by norm_num) (by positivity)
  have hε₀le : ε₀ ≤ 1 / 2 := min_le_left _ _
  have hε₀t : ε₀ ≤ t ^ 2 / 2 := min_le_right _ _
  -- `-1 + ε + it` lies in `𝒟` for `0 < ε < ε₀`
  have hmem1 : ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀, (ε - 1) +ᵥ it ∈ DomainD := by
    intro ε hε
    obtain ⟨hε0, _⟩ := hε
    refine key (ε - 1) (by linarith) (by linarith) ?_ ?_
    · nlinarith [sq_nonneg (ε - 3 / 2)]
    · nlinarith [sq_nonneg (ε - 1 / 2), mul_nonneg hε0.le (show (0 : ℝ) ≤ 1 - ε by linarith)]
  -- `1 - ε + it` lies in `𝒟` for `0 < ε < ε₀`
  have hmem2 : ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀, ((1 : ℝ) - ε) +ᵥ it ∈ DomainD := by
    intro ε hε
    obtain ⟨hε0, _⟩ := hε
    refine key (1 - ε) (by linarith) (by linarith) ?_ ?_
    · nlinarith [sq_nonneg (1 / 2 - ε), mul_nonneg hε0.le (show (0 : ℝ) ≤ 1 - ε by linarith)]
    · nlinarith [sq_nonneg (3 / 2 - ε)]
  have h0mem : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) ε₀) := by
    rw [closure_Ioo (ne_of_lt hε₀pos)]; exact ⟨le_refl 0, hε₀pos.le⟩
  have hcont1 : Continuous (fun ε : ℝ => (ε - 1) +ᵥ it) := by
    refine (UpperHalfPlane.isEmbedding_coe.continuous_iff).mpr ?_
    show Continuous (fun ε : ℝ => (↑(ε - 1) : ℂ) + ((t : ℂ) * Complex.I))
    fun_prop
  have hcont2 : Continuous (fun ε : ℝ => ((1 : ℝ) - ε) +ᵥ it) := by
    refine (UpperHalfPlane.isEmbedding_coe.continuous_iff).mpr ?_
    show Continuous (fun ε : ℝ => (↑((1 : ℝ) - ε) : ℂ) + ((t : ℂ) * Complex.I))
    fun_prop
  -- `-1 + it` is a limit of points of `𝒟`
  have hC1 : ((-1 : ℝ) +ᵥ it) ∈ closure DomainD := by
    have himg := mem_closure_image hcont1.continuousAt h0mem
    have := closure_mono (fun z hz => by
      obtain ⟨ε, hε, rfl⟩ := hz
      exact hmem1 ε hε) himg
    simpa using this
  -- `1 + it` is a limit of points of `𝒟`
  have hC2 : ((1 : ℝ) +ᵥ it) ∈ closure DomainD := by
    have himg := mem_closure_image hcont2.continuousAt h0mem
    have := closure_mono (fun z hz => by
      obtain ⟨ε, hε, rfl⟩ := hz
      exact hmem2 ε hε) himg
    simpa using this
  -- `it` itself lies in `𝒟`
  have hItD : it ∈ DomainD := by
    have h := key 0 (by norm_num) (by norm_num) (by nlinarith [sq_nonneg (0 - 1 / 2 : ℝ)])
      (by nlinarith [sq_nonneg (0 + 1 / 2 : ℝ)])
    simpa using h
  refine ⟨(-1 : ℝ) +ᵥ it, hC1, ?_, ?_⟩
  · have : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ it) = it := by
      rw [← AddSemigroupAction.add_vadd, add_neg_cancel, zero_vadd]
    rw [this]; exact subset_closure hItD
  · have h2eq : (2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ it) = (1 : ℝ) +ᵥ it := by
      rw [← AddSemigroupAction.add_vadd]; norm_num
    rw [h2eq]; exact hC2

end Work.Asymptotics
