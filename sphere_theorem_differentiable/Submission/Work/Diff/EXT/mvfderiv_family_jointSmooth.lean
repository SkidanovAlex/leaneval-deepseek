import Mathlib
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_along_field
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.covK_spatialDeriv
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_gen

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The vertical lift of a jointly smooth family of sections is jointly smooth.**  This is the
family version of the (already proved) `Work.Diff.EXT.contMDiffAt_prod_inr_field`: if
`(t, y) ↦ W t y` is a jointly smooth family of tangent vectors on `M`, then
`p ↦ (0, W p.1 p.2)` is a jointly smooth section of the tangent bundle of `ℝ × M`
(model `(modelWithCornersSelf ℝ ℝ).prod I`, so that
`TangentSpace ((modelWithCornersSelf ℝ ℝ).prod I) p` is definitionally
`TangentSpace (modelWithCornersSelf ℝ ℝ) p.1 × TangentSpace I p.2`).

The proof is the same as in the fixed-field case, using the canonical family of smooth equivalences
`equivTangentBundleProd I ℝ I M : T(ℝ × M) ≃ Tℝ × TM` (`contMDiff_equivTangentBundleProd_symm`)
and the fact that the zero section is smooth (`contMDiffAt_zeroSection`); the only difference is
that the second factor is a function of the pair `p` and hence is combined by `prodMk` rather than
`prodMap`. -/
theorem contMDiffAt_prod_inr_field_family
    {W : ℝ → TField (I := I) (M := M)} {t₀ : ℝ} {x : M}
    (hW : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M => (⟨p.2, W p.1 p.2⟩ : TangentBundle I M)) (t₀, x)) :
    ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) ((modelWithCornersSelf ℝ ℝ).prod I).tangent
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M =>
        (⟨p, (0, W p.1 p.2)⟩ : TangentBundle ((modelWithCornersSelf ℝ ℝ).prod I) (ℝ × M)))
      (t₀, x) := by
  have h1 : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (𝓘(ℝ,ℝ)).tangent ∞
      (fun p : ℝ × M => zeroSection ℝ (TangentSpace 𝓘(ℝ,ℝ)) p.1) (t₀, x) :=
    (contMDiffAt_zeroSection ℝ (TangentSpace 𝓘(ℝ,ℝ))).comp (t₀, x) contMDiffAt_fst
  have h2 : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M => (⟨p.2, W p.1 p.2⟩ : TangentBundle I M)) (t₀, x) := hW
  have hg : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I)
      ((𝓘(ℝ,ℝ)).tangent.prod I.tangent) ∞
      (fun p : ℝ × M => (zeroSection ℝ (TangentSpace 𝓘(ℝ,ℝ)) p.1,
        (⟨p.2, W p.1 p.2⟩ : TangentBundle I M))) (t₀, x) := h1.prodMk h2
  have he := (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ,ℝ)) (M := ℝ) (I' := I) (M' := M)
    (n := ∞)).contMDiffAt
    (x := ((zeroSection ℝ (TangentSpace 𝓘(ℝ,ℝ)) t₀), (⟨x, W t₀ x⟩ : TangentBundle I M)))
  have hmain : ContMDiffAt (𝓘(ℝ,ℝ).prod I) ((𝓘(ℝ,ℝ).prod I).tangent) ∞
      (fun p : ℝ × M => (equivTangentBundleProd 𝓘(ℝ,ℝ) ℝ I M).symm
        ((zeroSection ℝ (TangentSpace 𝓘(ℝ,ℝ)) p.1),
          (⟨p.2, W p.1 p.2⟩ : TangentBundle I M))) (t₀, x) :=
    he.comp (t₀, x) hg
  refine hmain.congr_of_eventuallyEq (EventuallyEq.of_eq ?_)
  funext p
  rfl

/-- **The pointwise identification of a slice derivative.**  If `Φ : ℝ × M → ℝ` is differentiable
at `p = (t, y)`, then the derivative of `Φ` at `p` in the direction `(0, v)` (where the tangent
space of the product is the product of the tangent spaces) is the derivative of the slice
`y ↦ Φ (t, y)` at `y` in the direction `v`. -/
lemma mvfderiv_prod_slice_eq {Φ : ℝ × M → ℝ} {p : ℝ × M}
    (hp : MDifferentiableAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) Φ p)
    {v : TangentSpace I p.2} :
    mvfderiv ((modelWithCornersSelf ℝ ℝ).prod I) Φ p
        ((0, v) : TangentSpace ((modelWithCornersSelf ℝ ℝ).prod I) p)
      = mvfderiv I (fun y : M => Φ (p.1, y)) p.2 v := by
  have h := mfderiv_prod_eq_add_apply (I := (modelWithCornersSelf ℝ ℝ)) (I' := I)
    (I'' := (modelWithCornersSelf ℝ ℝ)) (f := Φ) (p := p)
    (v := ((0, v) : TangentSpace ((modelWithCornersSelf ℝ ℝ).prod I) p)) hp
  have h0 : ((mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
      (fun z : ℝ => Φ (z, p.2)) p.1))
      (0 : TangentSpace (modelWithCornersSelf ℝ ℝ) p.1) = 0 := map_zero _
  rw [h0, zero_add] at h
  exact h

end Helpers

theorem mvfderiv_family_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {Φ : ℝ × M → ℝ} {W : ℝ → Work.Diff.EXT.TField (I := I) (M := M)} {t₀ : ℝ} {x : M}
    (hΦ : Work.Diff.EXT.JointSmoothAt I M Φ t₀ x)
    (hW : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M => (⟨p.2, W p.1 p.2⟩ : TangentBundle I M)) (t₀, x)) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M => mvfderiv I (fun y : M => Φ (p.1, y)) p.2 (W p.1 p.2)) t₀ x := by
  -- The jointly smooth section `p ↦ (0, W p.1 p.2)` of the tangent bundle of `ℝ × M`.
  have hX : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I)
      ((modelWithCornersSelf ℝ ℝ).prod I).tangent ∞
      (fun p : ℝ × M =>
        (⟨p, (0, W p.1 p.2)⟩ : TangentBundle ((modelWithCornersSelf ℝ ℝ).prod I) (ℝ × M)))
      (t₀, x) :=
    contMDiffAt_prod_inr_field_family (W := W) (t₀ := t₀) (x := x) hW
  -- Smoothness of the full derivative of `Φ` along that section, by `contMDiffAt_mvfderiv_gen`
  -- applied to the product manifold `ℝ × M`.
  have hmain := contMDiffAt_mvfderiv_gen (M := ℝ × M) (I := (modelWithCornersSelf ℝ ℝ).prod I)
    (F := ℝ) (f := Φ)
    (X := fun p : ℝ × M => ((0, W p.1 p.2) : TangentSpace ((modelWithCornersSelf ℝ ℝ).prod I) p))
    hΦ hX
  refine hmain.congr_of_eventuallyEq ?_
  -- The two derivatives agree near `(t₀, x)`, where `Φ` is differentiable.
  have hmd : ∀ᶠ p : ℝ × M in 𝓝 (t₀, x),
      MDifferentiableAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) Φ p := by
    have h1 : ∀ᶠ p : ℝ × M in 𝓝 (t₀, x),
        ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) (1 : ℕ∞ω) Φ p :=
      (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).1 (hΦ.of_le (by norm_num))
    filter_upwards [h1] with p hp
    exact hp.mdifferentiableAt (by norm_num)
  filter_upwards [hmd] with p hp
  exact (mvfderiv_prod_slice_eq (I := I) (M := M) hp (v := W p.1 p.2)).symm

end Work.Diff.EXT
