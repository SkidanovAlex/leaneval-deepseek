import Mathlib
import Submission.Work.Drive.genFunctionalStable
import Submission.Work.Drive.genAlong_open

/-!
# The genericity survives the class perturbation

The last step of the circularity-free resolution of `(F1)` (`F1_GENERICITY_RESOLUTION.md` §1): if `ℓ` is
generic along a curve `V` (`Work.Drive.GenAlong`, satisfied by the unperturbed reference functional
along the two class lifts, chosen *before* the perturbation parameters by
`Work.Drive.exists_genAlong_family`), then so is the transported functional

> `ℓ ∘ (classEquiv σ)⁻¹ ∘ classEquiv τ`,

for all parameters `τ`, `σ` of small norm — because the transport differs from the identity by
`O(‖τ‖ + ‖σ‖)` (`Work.Drive.classEquiv_sub_classEquiv` plus the inverse estimate
`Work.Drive.exists_norm_classEquiv_symm_sub_one_lt`) and `GenAlong` is open
(`Work.Drive.genAlong_open`).

This is exactly the hypothesis `hgen` of
`Work.Drive.odd_coreSideCountPt_rotCapping_of_genAlong` (`Drive/mixedFactorF1.lean`) at the parameters
supplied by the reference-triple genericity lemma, whose radius is at our disposal.
-/

namespace Work.Drive

open Set
open scoped ContDiff Topology

noncomputable section

/-- The composition of the inverse class perturbation with the class perturbation is the identity. -/
lemma classEquiv_symm_comp (σ : Eucl 3) :
    ((classEquiv σ).symm : Eucl 3 →L[ℝ] Eucl 3) ∘L (classEquiv σ : Eucl 3 →L[ℝ] Eucl 3)
      = 1 := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
  exact ContinuousLinearEquiv.symm_apply_apply (classEquiv σ) v

/-- **The genericity along a curve survives the class perturbation**, for parameters of small norm. -/
theorem genAlong_classEquiv_transfer {V : ℝ → Eucl 3} (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    {ℓ : Eucl 3 →L[ℝ] ℝ} (hℓ : GenAlong ℓ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ σ : Eucl 3, ‖τ‖ < δ → ‖σ‖ < δ →
      GenAlong (ℓ ∘L (((classEquiv σ).symm : Eucl 3 →L[ℝ] Eucl 3)) ∘L
        ((classEquiv τ : Eucl 3 →L[ℝ] Eucl 3))) V := by
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := genAlong_open hVs hℓ
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := exists_norm_classEquiv_symm_sub_one_lt 1 one_pos
  set C : ℝ := classGenC with hCdef
  have hCnn : 0 ≤ C := classGenC_nonneg
  set L : ℝ := ‖ℓ‖ + 1 with hLdef
  have hLpos : 0 < L := by rw [hLdef]; positivity
  refine ⟨min δ₂ (min 1 (δ₁ / (8 * L * (C + 1)))),
    lt_min hδ₂pos (lt_min one_pos (div_pos hδ₁pos (by positivity))), fun τ σ hτ hσ => ?_⟩
  have hτ₂ : ‖τ‖ < δ₂ := lt_of_lt_of_le hτ (min_le_left _ _)
  have hσ₂ : ‖σ‖ < δ₂ := lt_of_lt_of_le hσ (min_le_left _ _)
  have hτb : ‖τ‖ < δ₁ / (8 * L * (C + 1)) :=
    lt_of_lt_of_le hτ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hσb : ‖σ‖ < δ₁ / (8 * L * (C + 1)) :=
    lt_of_lt_of_le hσ (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the inverse is close to `1`
  have hinv : ‖((classEquiv σ).symm : Eucl 3 →L[ℝ] Eucl 3)‖ ≤ 2 := by
    have h := hδ₂ σ hσ₂
    calc ‖((classEquiv σ).symm : Eucl 3 →L[ℝ] Eucl 3)‖
        = ‖(((classEquiv σ).symm : Eucl 3 →L[ℝ] Eucl 3)) - 1 + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖(((classEquiv σ).symm : Eucl 3 →L[ℝ] Eucl 3)) - 1‖ + ‖(1 : Eucl 3 →L[ℝ] Eucl 3)‖ :=
          norm_add_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  -- the difference of the two class equivalences
  have hdiff : ‖((classEquiv τ : Eucl 3 →L[ℝ] Eucl 3)) - (classEquiv σ : Eucl 3 →L[ℝ] Eucl 3)‖
      ≤ C * (‖τ‖ + ‖σ‖) := by
    rw [classEquiv_sub_classEquiv]
    calc ‖classGen (τ - σ)‖ ≤ C * ‖τ - σ‖ := classGen_norm_le (τ - σ)
      _ ≤ C * (‖τ‖ + ‖σ‖) := mul_le_mul_of_nonneg_left (norm_sub_le τ σ) hCnn
  -- the transport as `ℓ ∘ B`
  set B : Eucl 3 →L[ℝ] Eucl 3 := ((classEquiv σ).symm : Eucl 3 →L[ℝ] Eucl 3) ∘L
      (classEquiv τ : Eucl 3 →L[ℝ] Eucl 3) with hBdef
  have hBsub : B - 1 = ((classEquiv σ).symm : Eucl 3 →L[ℝ] Eucl 3) ∘L
      (((classEquiv τ : Eucl 3 →L[ℝ] Eucl 3)) - (classEquiv σ : Eucl 3 →L[ℝ] Eucl 3)) := by
    rw [hBdef, ContinuousLinearMap.comp_sub, classEquiv_symm_comp]
  have hnorm : ‖B - 1‖ ≤ 2 * C * (‖τ‖ + ‖σ‖) := by
    calc ‖B - 1‖ ≤ ‖((classEquiv σ).symm : Eucl 3 →L[ℝ] Eucl 3)‖ *
            ‖(((classEquiv τ : Eucl 3 →L[ℝ] Eucl 3)) - (classEquiv σ : Eucl 3 →L[ℝ] Eucl 3))‖ := by
          rw [hBsub]; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 2 * (C * (‖τ‖ + ‖σ‖)) :=
          mul_le_mul hinv hdiff (by positivity) (by norm_num)
      _ = 2 * C * (‖τ‖ + ‖σ‖) := by ring
  -- the chain of estimates
  have hS : (‖τ‖ + ‖σ‖) * (8 * L * (C + 1)) < 2 * δ₁ := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 8 * L * (C + 1))] at hτb hσb
    nlinarith
  have hkey : ‖ℓ‖ * (2 * C * (‖τ‖ + ‖σ‖)) < δ₁ := by
    have hle : ‖ℓ‖ * (2 * C * (‖τ‖ + ‖σ‖)) ≤ (‖τ‖ + ‖σ‖) * (2 * (C + 1) * L) := by
      rw [hLdef]
      nlinarith [hCnn, norm_nonneg ℓ, norm_nonneg τ, norm_nonneg σ]
    have hlt : (‖τ‖ + ‖σ‖) * (2 * (C + 1) * L) < δ₁ := by
      have : (‖τ‖ + ‖σ‖) * (8 * L * (C + 1)) = 4 * ((‖τ‖ + ‖σ‖) * (2 * (C + 1) * L)) := by ring
      linarith
    linarith
  have hfinal : ‖(ℓ ∘L B) - ℓ‖ < δ₁ := by
    have hcomp : (ℓ ∘L B) - ℓ = ℓ ∘L (B - 1) := by
      rw [ContinuousLinearMap.comp_sub]
      ext v
      simp
    rw [hcomp]
    calc ‖ℓ ∘L (B - 1)‖ ≤ ‖ℓ‖ * ‖B - 1‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖ℓ‖ * (2 * C * (‖τ‖ + ‖σ‖)) :=
          mul_le_mul_of_nonneg_left hnorm (norm_nonneg ℓ)
      _ < δ₁ := hkey
  -- conclusion
  have hℓ' := hδ₁ (ℓ ∘L B) hfinal
  have : ℓ ∘L B = ℓ ∘L (((classEquiv σ).symm : Eucl 3 →L[ℝ] Eucl 3)) ∘L
      ((classEquiv τ : Eucl 3 →L[ℝ] Eucl 3)) := by rw [hBdef]
  rwa [this] at hℓ'

/-- **A single generic functional, robust under small class perturbations, for a finite family of
curves.**  This is the form in which the resolution of the `(F1)` genericity obligation is consumed:
`ℓ` is chosen *once* (before the perturbation parameters) generic along all the curves `V i`, and the
same `ℓ` stays generic for every transported functional
`ℓ ∘ (classEquiv σ)⁻¹ ∘ classEquiv τ` with `‖τ‖, ‖σ‖ < δ`. -/
theorem exists_genAlong_family_classEquiv {ι : Type*} [Fintype ι] (V : ι → ℝ → Eucl 3)
    (hVs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i))
    (hVne : ∀ i t, t ∈ Icc (0 : ℝ) 1 → V i t ≠ 0) :
    ∃ ℓ : Eucl 3 →L[ℝ] ℝ, ℓ ≠ 0 ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ τ σ : Eucl 3,
      ‖τ‖ < δ → ‖σ‖ < δ → ∀ i : ι,
      GenAlong (ℓ ∘L (((classEquiv σ).symm : Eucl 3 →L[ℝ] Eucl 3)) ∘L
        ((classEquiv τ : Eucl 3 →L[ℝ] Eucl 3))) (V i) := by
  classical
  obtain ⟨ℓ, hℓne, hgen⟩ := exists_genAlong_family V hVs hVne
  choose δi hδi using fun i => genAlong_classEquiv_transfer (hVs i) (hgen i)
  by_cases hne : (Finset.univ.image δi).Nonempty
  · have hmem : (Finset.univ.image δi).min' hne ∈ Finset.univ.image δi := Finset.min'_mem _ hne
    refine ⟨ℓ, hℓne, (Finset.univ.image δi).min' hne, ?_, fun τ σ hτ hσ i => ?_⟩
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
      rw [← hj]; exact (hδi j).1
    · refine (hδi i).2 τ σ ?_ ?_
      · exact lt_of_lt_of_le hτ
          (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      · exact lt_of_lt_of_le hσ
          (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  · refine ⟨ℓ, hℓne, 1, one_pos, fun τ σ hτ hσ i => ?_⟩
    exfalso
    exact hne ⟨δi i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩

end

end Work.Drive
