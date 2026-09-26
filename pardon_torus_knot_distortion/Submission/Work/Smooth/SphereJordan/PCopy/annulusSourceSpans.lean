import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.halfAnnulusSetup
import Submission.Work.Smooth.SphereJordan.PCopy.bdVec_mem_upRectBd
import Submission.Work.Smooth.SphereJordan.PCopy.bdVec_eq_imp_smul
import Submission.Work.Smooth.SphereJordan.PCopy.halfAnnulusAux

/-!
# The two halves of the model pcannulus span it, with the source boundary parametrisation

`Work.SphereJordan.pcannulusSourceSpans`: the two closed half-annuli

`{1/2 ≤ ‖z‖ ≤ 1, 0 ≤ Im (z / pccutDir S)}` and `{1/2 ≤ ‖z‖ ≤ 1, Im (z / pccutDir S) ≤ 0}`

are the images of two continuous injections `Ψ_up, Ψ_dn : 𝔻 → ℂ` whose boundary circle is mapped to
the source boundary curves `pcsrcUpB S` and `pcsrcDnB S` of
`Submission/Work/Smooth/SphereJordan/pcannulusInjectionTwoCutsAlt.lean`; consequently they cover the
model pcannulus `{1/2 ≤ ‖z‖ ≤ 1}` and meet exactly in the two radial pccuts.

The maps are the explicit maps of `Submission/Work/SphereJordan/halfAnnulusSetup.lean`,
`z ↦ pccutDir S · (R z) · e^{i (Φ z)}`, transported to the disc.
-/

open Set Pointwise

namespace Work.SphereJordan

noncomputable section

open Work.Smooth.SphereJordan (circlePoint pcsrcUpB pcsrcDnB pccutDir)

theorem pccontinuous_toCplx : Continuous pctoCplx := by
  unfold pctoCplx
  fun_prop

theorem pcnorm_coe_disc_le_one' (z : Work.Smooth.SphereJordan.Disc) : ‖((z : ℂ))‖ ≤ 1 := by
  have h := z.2
  rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h

theorem pcnorm_ofReal_complex (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by simp

theorem pcannulusSourceSpans {γ : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ∃ Ψ_up Ψ_dn : C(Work.Smooth.SphereJordan.Disc, ℂ),
      Function.Injective Ψ_up ∧ Function.Injective Ψ_dn ∧
      (∀ τ : ℝ, Ψ_up (Work.Smooth.SphereJordan.circlePoint τ) =
        Work.Smooth.SphereJordan.pcsrcUpB S τ) ∧
      (∀ τ : ℝ, Ψ_dn (Work.Smooth.SphereJordan.circlePoint τ) =
        Work.Smooth.SphereJordan.pcsrcDnB S τ) ∧
      Set.range Ψ_up ∪ Set.range Ψ_dn =
        Metric.closedBall (0 : ℂ) 1 \ Metric.ball (0 : ℂ) (1 / 2) ∧
      Set.range Ψ_up ∩ Set.range Ψ_dn =
        ({z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
            z = (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S} ∪
         {z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
            z = -((σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)}) := by
  have hu : Work.Smooth.SphereJordan.pccutDir S ≠ 0 :=
    Work.Smooth.SphereJordan.pccutDir_ne_zero S
  have hun : ‖Work.Smooth.SphereJordan.pccutDir S‖ = 1 :=
    Work.Smooth.SphereJordan.pcnorm_cutDir S
  have hcont : Continuous fun z : Work.Smooth.SphereJordan.Disc => pctoCplx (pcradVec (z : ℂ)) :=
    pccontinuous_toCplx.comp (pccontinuous_radVec.comp continuous_subtype_val)
  let Ψ_up : C(Work.Smooth.SphereJordan.Disc, ℂ) :=
    ⟨fun z => Work.Smooth.SphereJordan.pccutDir S * pctoCplx (pcradVec (z : ℂ)),
      continuous_const.mul hcont⟩
  let Ψ_dn : C(Work.Smooth.SphereJordan.Disc, ℂ) :=
    ⟨fun z => -(Work.Smooth.SphereJordan.pccutDir S * pctoCplx (pcradVec (z : ℂ))),
      (continuous_const.mul hcont).neg⟩
  have hmem : ∀ z : Work.Smooth.SphereJordan.Disc,
      (z : ℂ) ∈ Metric.closedBall (0:ℂ) 1 := by
    intro z
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact pcnorm_coe_disc_le_one' z
  have hΦ : Set.range (fun z : Work.Smooth.SphereJordan.Disc => pctoCplx (pcradVec (z : ℂ)))
      = pctoCplx '' pcupRect := by
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨pcradVec (z : ℂ), pcradVec_mem (pcnorm_coe_disc_le_one' z), rfl⟩
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨z, hz1, hz2⟩ := pcradVec_surj hp
      refine ⟨⟨z, ?_⟩, ?_⟩
      · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact hz1
      · show pctoCplx (pcradVec ((⟨z, _⟩ : Work.Smooth.SphereJordan.Disc) : ℂ)) = pctoCplx p
        rw [hz2]
  set A : Set ℂ := {z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 ∧ 0 ≤ z.im} with hA
  set An : Set ℂ := {z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 ∧ z.im ≤ 0} with hAn
  have hAeq : pctoCplx '' pcupRect = A := by
    rw [hA]
    exact pctoCplx_range_up
  have hnegA : {z : ℂ | -z ∈ A} = An := by
    ext z
    simp only [hA, hAn, Set.mem_setOf_eq, norm_neg, Complex.neg_im]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by linarith⟩
  have hUp : Set.range Ψ_up =
      (fun a : ℂ => Work.Smooth.SphereJordan.pccutDir S * a) '' A := by
    have hrange : Set.range Ψ_up =
        (fun a : ℂ => Work.Smooth.SphereJordan.pccutDir S * a) ''
          Set.range (fun z : Work.Smooth.SphereJordan.Disc => pctoCplx (pcradVec (z : ℂ))) := by
      ext w
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨_, ⟨z, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
        exact ⟨z, rfl⟩
    rw [hrange, hΦ, hAeq]
  have hDn : Set.range Ψ_dn =
      (fun a : ℂ => Work.Smooth.SphereJordan.pccutDir S * a) '' An := by
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
      refine ⟨Work.Smooth.SphereJordan.pccutDir S * (-b), ⟨-b, ?_, rfl⟩, ?_⟩
      · rw [← hnegA] at hb
        exact hb
      · ring
  refine ⟨Ψ_up, Ψ_dn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- injectivity of `Ψ_up`
    intro z z' hzz
    have h1 : pctoCplx (pcradVec (z : ℂ)) = pctoCplx (pcradVec (z' : ℂ)) :=
      mul_left_cancel₀ hu hzz
    have h2 : pcradVec (z : ℂ) = pcradVec (z' : ℂ) :=
      pctoCplx_injOn (pcradVec_mem (pcnorm_coe_disc_le_one' z))
        (pcradVec_mem (pcnorm_coe_disc_le_one' z')) h1
    exact Subtype.ext (pcradVec_injOn (hmem z) (hmem z') h2)
  · -- injectivity of `Ψ_dn`
    intro z z' hzz
    have h0 : Work.Smooth.SphereJordan.pccutDir S * pctoCplx (pcradVec (z : ℂ)) =
        Work.Smooth.SphereJordan.pccutDir S * pctoCplx (pcradVec (z' : ℂ)) := neg_injective hzz
    have h1 : pctoCplx (pcradVec (z : ℂ)) = pctoCplx (pcradVec (z' : ℂ)) := mul_left_cancel₀ hu h0
    have h2 : pcradVec (z : ℂ) = pcradVec (z' : ℂ) :=
      pctoCplx_injOn (pcradVec_mem (pcnorm_coe_disc_le_one' z))
        (pcradVec_mem (pcnorm_coe_disc_le_one' z')) h1
    exact Subtype.ext (pcradVec_injOn (hmem z) (hmem z') h2)
  · -- the boundary values of `Ψ_up`
    intro τ
    have h1 : pcradVec ((circlePoint τ : Work.Smooth.SphereJordan.Disc) : ℂ) =
        pcbdVec ((circlePoint τ : Work.Smooth.SphereJordan.Disc) : ℂ) := by
      rw [pcradVec, Work.Smooth.SphereJordan.norm_circlePoint_plain, pcsegVec_one]
    have h2 : Ψ_up (circlePoint τ) = Work.Smooth.SphereJordan.pccutDir S * pcstdHalf τ := by
      show Work.Smooth.SphereJordan.pccutDir S * pctoCplx (pcradVec _) = _
      rw [h1, pcbdVec_circlePoint]
      rfl
    rw [h2]
    exact (pcsrcUpB_eq_smul S τ).symm
  · -- the boundary values of `Ψ_dn`
    intro τ
    have h1 : pcradVec ((circlePoint τ : Work.Smooth.SphereJordan.Disc) : ℂ) =
        pcbdVec ((circlePoint τ : Work.Smooth.SphereJordan.Disc) : ℂ) := by
      rw [pcradVec, Work.Smooth.SphereJordan.norm_circlePoint_plain, pcsegVec_one]
    have h2 : Ψ_dn (circlePoint τ) =
        -(Work.Smooth.SphereJordan.pccutDir S * pcstdHalf τ) := by
      show -(Work.Smooth.SphereJordan.pccutDir S * pctoCplx (pcradVec _)) = _
      rw [h1, pcbdVec_circlePoint]
      rfl
    rw [h2]
    exact (pcsrcDnB_eq_neg S τ).symm
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
    have himgself : (fun a : ℂ => Work.Smooth.SphereJordan.pccutDir S * a) ''
        {z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1} = {z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1} := by
      ext z
      constructor
      · rintro ⟨s, hs, rfl⟩
        simp only [Set.mem_ofPred_eq] at hs ⊢
        rw [norm_mul, hun, one_mul]
        exact hs
      · intro hz
        simp only [Set.mem_ofPred_eq] at hz
        refine ⟨(Work.Smooth.SphereJordan.pccutDir S)⁻¹ * z, ?_, ?_⟩
        · show 1 / 2 ≤ ‖(Work.Smooth.SphereJordan.pccutDir S)⁻¹ * z‖ ∧
              ‖(Work.Smooth.SphereJordan.pccutDir S)⁻¹ * z‖ ≤ 1
          rw [norm_mul, norm_inv, hun, inv_one, one_mul]
          exact hz
        · show Work.Smooth.SphereJordan.pccutDir S *
            ((Work.Smooth.SphereJordan.pccutDir S)⁻¹ * z) = z
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
    have himgreal : (fun a : ℂ => Work.Smooth.SphereJordan.pccutDir S * a) ''
        {z : ℂ | 1/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 ∧ z.im = 0} =
        ({z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
            z = (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S} ∪
         {z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
            z = -((σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)}) := by
      ext w
      constructor
      · rintro ⟨z, ⟨h1, h2, h3⟩, rfl⟩
        have hz : z = ((z.re : ℝ) : ℂ) := by
          apply Complex.ext <;> simp [h3]
        have hn1 : (1 / 2 : ℝ) ≤ |z.re| := by
          rw [← pcnorm_ofReal_complex, ← hz]
          exact h1
        have hn2 : |z.re| ≤ 1 := by
          rw [← pcnorm_ofReal_complex, ← hz]
          exact h2
        rcases le_or_gt 0 z.re with hpos | hpos
        · left
          refine ⟨z.re, ⟨by rwa [abs_of_nonneg hpos] at hn1, by rwa [abs_of_nonneg hpos] at hn2⟩, ?_⟩
          show Work.Smooth.SphereJordan.pccutDir S * z = ((z.re : ℝ) : ℂ) *
            Work.Smooth.SphereJordan.pccutDir S
          nth_rewrite 1 [hz]
          ring
        · right
          refine ⟨-z.re, ⟨by rw [abs_of_neg hpos] at hn1; linarith,
            by rw [abs_of_neg hpos] at hn2; linarith⟩, ?_⟩
          show Work.Smooth.SphereJordan.pccutDir S * z = -((((-z.re : ℝ)) : ℂ) *
            Work.Smooth.SphereJordan.pccutDir S)
          nth_rewrite 1 [hz]
          push_cast
          ring
      · rintro (⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩)
        · refine ⟨(σ : ℂ), ?_, ?_⟩
          · simp only [Set.mem_ofPred_eq]
            have h : ‖((σ : ℝ) : ℂ)‖ = σ := by
              rw [pcnorm_ofReal_complex, abs_of_nonneg (le_trans (by norm_num) hσ.1)]
            exact ⟨by rw [h]; exact hσ.1, by rw [h]; exact hσ.2, by simp⟩
          · ring
        · refine ⟨-(σ : ℂ), ?_, ?_⟩
          · simp only [Set.mem_ofPred_eq]
            have h : ‖(-(σ : ℂ))‖ = σ := by
              rw [norm_neg, pcnorm_ofReal_complex, abs_of_nonneg (le_trans (by norm_num) hσ.1)]
            exact ⟨by rw [h]; exact hσ.1, by rw [h]; exact hσ.2, by simp⟩
          · ring
    have hinter : (fun a : ℂ => Work.Smooth.SphereJordan.pccutDir S * a) '' A ∩
        (fun a : ℂ => Work.Smooth.SphereJordan.pccutDir S * a) '' An =
        (fun a : ℂ => Work.Smooth.SphereJordan.pccutDir S * a) '' (A ∩ An) := by
      ext w
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hb'⟩⟩
        have h : a = b := by
          have hEq : Work.Smooth.SphereJordan.pccutDir S * a =
              Work.Smooth.SphereJordan.pccutDir S * b := by
            simpa using hb'.symm
          exact mul_left_cancel₀ hu hEq
        exact ⟨a, ⟨ha, h.symm ▸ hb⟩, rfl⟩
      · rintro ⟨c, ⟨hc, hc'⟩, rfl⟩
        exact ⟨⟨c, hc, rfl⟩, ⟨c, hc', rfl⟩⟩
    rw [hUp, hDn, hinter, hAAn]
    exact himgreal

end

end Work.SphereJordan
