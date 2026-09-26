import Mathlib
import Submission.Work.SphereJordan.halfAnnulusSetup
import Submission.Work.SphereJordan.bdVec_mem_upRectBd
import Submission.Work.SphereJordan.bdVec_eq_imp_smul
import Submission.Work.SphereJordan.halfAnnulusAux

/-!
# The two halves of the model annulus span it, with the source boundary parametrisation

`Work.SphereJordan.annulusSourceSpans`: the two closed half-annuli

`{1/2 ≤ ‖z‖ ≤ 1, 0 ≤ Im (z / cutDir S)}` and `{1/2 ≤ ‖z‖ ≤ 1, Im (z / cutDir S) ≤ 0}`

are the images of two continuous injections `Ψ_up, Ψ_dn : 𝔻 → ℂ` whose boundary circle is mapped to
the source boundary curves `srcUpB S` and `srcDnB S` of
`Submission/Work/Smooth/SphereJordan/annulusInjectionTwoCutsAlt.lean`; consequently they cover the
model annulus `{1/2 ≤ ‖z‖ ≤ 1}` and meet exactly in the two radial cuts.

The maps are the explicit maps of `Submission/Work/SphereJordan/halfAnnulusSetup.lean`,
`z ↦ cutDir S · (R z) · e^{i (Φ z)}`, transported to the disc.
-/

open Set Pointwise

namespace Work.SphereJordan

noncomputable section

open Work.Smooth.SphereJordan (circlePoint srcUpB srcDnB cutDir)

theorem continuous_toCplx : Continuous toCplx := by
  unfold toCplx
  fun_prop

theorem norm_coe_disc_le_one' (z : Work.Smooth.SphereJordan.Disc) : ‖((z : ℂ))‖ ≤ 1 := by
  have h := z.2
  rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h

theorem norm_ofReal_complex (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by simp

theorem annulusSourceSpans {γ : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ∃ Ψ_up Ψ_dn : C(Work.Smooth.SphereJordan.Disc, ℂ),
      Function.Injective Ψ_up ∧ Function.Injective Ψ_dn ∧
      (∀ τ : ℝ, Ψ_up (Work.Smooth.SphereJordan.circlePoint τ) =
        Work.Smooth.SphereJordan.srcUpB S τ) ∧
      (∀ τ : ℝ, Ψ_dn (Work.Smooth.SphereJordan.circlePoint τ) =
        Work.Smooth.SphereJordan.srcDnB S τ) ∧
      Set.range Ψ_up ∪ Set.range Ψ_dn =
        Metric.closedBall (0 : ℂ) 1 \ Metric.ball (0 : ℂ) (1 / 2) ∧
      Set.range Ψ_up ∩ Set.range Ψ_dn =
        ({z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
            z = (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S} ∪
         {z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
            z = -((σ : ℂ) * Work.Smooth.SphereJordan.cutDir S)}) := by
  have hu : Work.Smooth.SphereJordan.cutDir S ≠ 0 :=
    Work.Smooth.SphereJordan.cutDir_ne_zero S
  have hun : ‖Work.Smooth.SphereJordan.cutDir S‖ = 1 :=
    Work.Smooth.SphereJordan.norm_cutDir S
  have hcont : Continuous fun z : Work.Smooth.SphereJordan.Disc => toCplx (radVec (z : ℂ)) :=
    continuous_toCplx.comp (continuous_radVec.comp continuous_subtype_val)
  let Ψ_up : C(Work.Smooth.SphereJordan.Disc, ℂ) :=
    ⟨fun z => Work.Smooth.SphereJordan.cutDir S * toCplx (radVec (z : ℂ)),
      continuous_const.mul hcont⟩
  let Ψ_dn : C(Work.Smooth.SphereJordan.Disc, ℂ) :=
    ⟨fun z => -(Work.Smooth.SphereJordan.cutDir S * toCplx (radVec (z : ℂ))),
      (continuous_const.mul hcont).neg⟩
  have hmem : ∀ z : Work.Smooth.SphereJordan.Disc,
      (z : ℂ) ∈ Metric.closedBall (0:ℂ) 1 := by
    intro z
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact norm_coe_disc_le_one' z
  have hΦ : Set.range (fun z : Work.Smooth.SphereJordan.Disc => toCplx (radVec (z : ℂ)))
      = toCplx '' upRect := by
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨radVec (z : ℂ), radVec_mem (norm_coe_disc_le_one' z), rfl⟩
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨z, hz1, hz2⟩ := radVec_surj hp
      refine ⟨⟨z, ?_⟩, ?_⟩
      · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact hz1
      · show toCplx (radVec ((⟨z, _⟩ : Work.Smooth.SphereJordan.Disc) : ℂ)) = toCplx p
        rw [hz2]
  set A : Set ℂ := {z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 ∧ 0 ≤ z.im} with hA
  set An : Set ℂ := {z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 ∧ z.im ≤ 0} with hAn
  have hAeq : toCplx '' upRect = A := by
    rw [hA]
    exact toCplx_range_up
  have hnegA : {z : ℂ | -z ∈ A} = An := by
    ext z
    simp only [hA, hAn, Set.mem_setOf_eq, norm_neg, Complex.neg_im]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by linarith⟩
  have hUp : Set.range Ψ_up =
      (fun a : ℂ => Work.Smooth.SphereJordan.cutDir S * a) '' A := by
    have hrange : Set.range Ψ_up =
        (fun a : ℂ => Work.Smooth.SphereJordan.cutDir S * a) ''
          Set.range (fun z : Work.Smooth.SphereJordan.Disc => toCplx (radVec (z : ℂ))) := by
      ext w
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨_, ⟨z, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
        exact ⟨z, rfl⟩
    rw [hrange, hΦ, hAeq]
  have hDn : Set.range Ψ_dn =
      (fun a : ℂ => Work.Smooth.SphereJordan.cutDir S * a) '' An := by
    have h1 : Set.range Ψ_dn = Neg.neg '' Set.range Ψ_up := by
      ext w
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨Ψ_up z, ⟨z, rfl⟩, rfl⟩
      · rintro ⟨v, ⟨z, rfl⟩, rfl⟩
        exact ⟨z, rfl⟩
    rw [h1, hUp]
    ext w
    constructor
    · rintro ⟨v, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨-a, ?_, ?_⟩
      · rw [← hnegA]
        simpa using ha
      · ring
    · rintro ⟨b, hb, rfl⟩
      refine ⟨Work.Smooth.SphereJordan.cutDir S * (-b), ⟨-b, ?_, rfl⟩, ?_⟩
      · rw [← hnegA] at hb
        exact hb
      · ring
  refine ⟨Ψ_up, Ψ_dn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- injectivity of `Ψ_up`
    intro z z' hzz
    have h1 : toCplx (radVec (z : ℂ)) = toCplx (radVec (z' : ℂ)) :=
      mul_left_cancel₀ hu hzz
    have h2 : radVec (z : ℂ) = radVec (z' : ℂ) :=
      toCplx_injOn (radVec_mem (norm_coe_disc_le_one' z))
        (radVec_mem (norm_coe_disc_le_one' z')) h1
    exact Subtype.ext (radVec_injOn (hmem z) (hmem z') h2)
  · -- injectivity of `Ψ_dn`
    intro z z' hzz
    have h0 : Work.Smooth.SphereJordan.cutDir S * toCplx (radVec (z : ℂ)) =
        Work.Smooth.SphereJordan.cutDir S * toCplx (radVec (z' : ℂ)) := neg_injective hzz
    have h1 : toCplx (radVec (z : ℂ)) = toCplx (radVec (z' : ℂ)) := mul_left_cancel₀ hu h0
    have h2 : radVec (z : ℂ) = radVec (z' : ℂ) :=
      toCplx_injOn (radVec_mem (norm_coe_disc_le_one' z))
        (radVec_mem (norm_coe_disc_le_one' z')) h1
    exact Subtype.ext (radVec_injOn (hmem z) (hmem z') h2)
  · -- the boundary values of `Ψ_up`
    intro τ
    have h1 : radVec ((circlePoint τ : Work.Smooth.SphereJordan.Disc) : ℂ) =
        bdVec ((circlePoint τ : Work.Smooth.SphereJordan.Disc) : ℂ) := by
      rw [radVec, Work.Smooth.SphereJordan.norm_circlePoint_plain, segVec_one]
    have h2 : Ψ_up (circlePoint τ) = Work.Smooth.SphereJordan.cutDir S * stdHalf τ := by
      show Work.Smooth.SphereJordan.cutDir S * toCplx (radVec _) = _
      rw [h1, bdVec_circlePoint]
      rfl
    rw [h2]
    exact (srcUpB_eq_smul S τ).symm
  · -- the boundary values of `Ψ_dn`
    intro τ
    have h1 : radVec ((circlePoint τ : Work.Smooth.SphereJordan.Disc) : ℂ) =
        bdVec ((circlePoint τ : Work.Smooth.SphereJordan.Disc) : ℂ) := by
      rw [radVec, Work.Smooth.SphereJordan.norm_circlePoint_plain, segVec_one]
    have h2 : Ψ_dn (circlePoint τ) =
        -(Work.Smooth.SphereJordan.cutDir S * stdHalf τ) := by
      show -(Work.Smooth.SphereJordan.cutDir S * toCplx (radVec _)) = _
      rw [h1, bdVec_circlePoint]
      rfl
    rw [h2]
    exact (srcDnB_eq_neg S τ).symm
  · -- the union of the two ranges
    have hAAn : A ∪ An = {z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1} := by
      ext z
      simp only [hA, hAn, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        rcases le_or_gt 0 z.im with h3 | h3
        · exact Or.inl ⟨h1, h2, h3⟩
        · exact Or.inr ⟨h1, h2, le_of_lt h3⟩
    have hclosed : {z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1} =
        Metric.closedBall (0 : ℂ) 1 \ Metric.ball (0 : ℂ) (1 / 2) := by
      ext z
      simp only [Metric.mem_closedBall, Metric.mem_ball, dist_zero_right, Set.mem_sdiff,
        Set.mem_setOf_eq, not_lt]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    have himgself : (fun a : ℂ => Work.Smooth.SphereJordan.cutDir S * a) ''
        {z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1} = {z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1} := by
      ext z
      constructor
      · rintro ⟨s, hs, rfl⟩
        simp only [Set.mem_ofPred_eq] at hs ⊢
        rw [norm_mul, hun, one_mul]
        exact hs
      · intro hz
        simp only [Set.mem_ofPred_eq] at hz
        refine ⟨(Work.Smooth.SphereJordan.cutDir S)⁻¹ * z, ?_, ?_⟩
        · show 1 / 2 ≤ ‖(Work.Smooth.SphereJordan.cutDir S)⁻¹ * z‖ ∧
              ‖(Work.Smooth.SphereJordan.cutDir S)⁻¹ * z‖ ≤ 1
          rw [norm_mul, norm_inv, hun, inv_one, one_mul]
          exact hz
        · show Work.Smooth.SphereJordan.cutDir S *
            ((Work.Smooth.SphereJordan.cutDir S)⁻¹ * z) = z
          rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul]
    rw [hUp, hDn, ← Set.image_union, hAAn, himgself]
    exact hclosed
  · -- the intersection of the two ranges
    have hAAn : A ∩ An = {z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 ∧ z.im = 0} := by
      ext z
      simp only [hA, hAn, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨h1, h2, h3⟩, ⟨-, -, h4⟩⟩
        exact ⟨h1, h2, le_antisymm h4 h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2, le_of_eq h3.symm⟩, ⟨h1, h2, le_of_eq h3⟩⟩
    have himgreal : (fun a : ℂ => Work.Smooth.SphereJordan.cutDir S * a) ''
        {z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 ∧ z.im = 0} =
        ({z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
            z = (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S} ∪
         {z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
            z = -((σ : ℂ) * Work.Smooth.SphereJordan.cutDir S)}) := by
      ext w
      constructor
      · rintro ⟨z, ⟨h1, h2, h3⟩, rfl⟩
        have hz : z = ((z.re : ℝ) : ℂ) := by
          apply Complex.ext <;> simp [h3]
        have hn1 : (1 / 2 : ℝ) ≤ |z.re| := by
          rw [← norm_ofReal_complex, ← hz]
          exact h1
        have hn2 : |z.re| ≤ 1 := by
          rw [← norm_ofReal_complex, ← hz]
          exact h2
        rcases le_or_gt 0 z.re with hpos | hpos
        · left
          refine ⟨z.re, ⟨by rwa [abs_of_nonneg hpos] at hn1, by rwa [abs_of_nonneg hpos] at hn2⟩, ?_⟩
          show Work.Smooth.SphereJordan.cutDir S * z = ((z.re : ℝ) : ℂ) *
            Work.Smooth.SphereJordan.cutDir S
          nth_rewrite 1 [hz]
          ring
        · right
          refine ⟨-z.re, ⟨by rw [abs_of_neg hpos] at hn1; linarith,
            by rw [abs_of_neg hpos] at hn2; linarith⟩, ?_⟩
          show Work.Smooth.SphereJordan.cutDir S * z = -((((-z.re : ℝ)) : ℂ) *
            Work.Smooth.SphereJordan.cutDir S)
          nth_rewrite 1 [hz]
          push_cast
          ring
      · rintro (⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩)
        · refine ⟨(σ : ℂ), ?_, ?_⟩
          · simp only [Set.mem_ofPred_eq]
            have h : ‖((σ : ℝ) : ℂ)‖ = σ := by
              rw [norm_ofReal_complex, abs_of_nonneg (le_trans (by norm_num) hσ.1)]
            exact ⟨by rw [h]; exact hσ.1, by rw [h]; exact hσ.2, by simp⟩
          · ring
        · refine ⟨-(σ : ℂ), ?_, ?_⟩
          · simp only [Set.mem_ofPred_eq]
            have h : ‖(-(σ : ℂ))‖ = σ := by
              rw [norm_neg, norm_ofReal_complex, abs_of_nonneg (le_trans (by norm_num) hσ.1)]
            exact ⟨by rw [h]; exact hσ.1, by rw [h]; exact hσ.2, by simp⟩
          · ring
    have hinter : (fun a : ℂ => Work.Smooth.SphereJordan.cutDir S * a) '' A ∩
        (fun a : ℂ => Work.Smooth.SphereJordan.cutDir S * a) '' An =
        (fun a : ℂ => Work.Smooth.SphereJordan.cutDir S * a) '' (A ∩ An) := by
      ext w
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hb'⟩⟩
        have h : a = b := by
          have hEq : Work.Smooth.SphereJordan.cutDir S * a =
              Work.Smooth.SphereJordan.cutDir S * b := by
            simpa using hb'.symm
          exact mul_left_cancel₀ hu hEq
        exact ⟨a, ⟨ha, h.symm ▸ hb⟩, rfl⟩
      · rintro ⟨c, ⟨hc, hc'⟩, rfl⟩
        exact ⟨⟨c, hc, rfl⟩, ⟨c, hc', rfl⟩⟩
    rw [hUp, hDn, hinter, hAAn]
    exact himgreal

end

end Work.SphereJordan
