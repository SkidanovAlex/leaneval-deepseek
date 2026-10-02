import Mathlib
import Submission.Work.ThomBordism.Grassmann.ThomTarget
import Submission.Work.ThomBordism.Grassmann.GoodCover.CohRank
import Submission.Work.ThomBordism.Grassmann.GoodCover.thomSpaceCohomology_of_lowDegree
import Submission.Work.ThomBordism.Grassmann.lowDegreeCohomology
import Submission.Work.Cohomology.kronH_kernel_eq_torsion
import Submission.Work.ThomBordism.Grassmann.Torsion.thomSpaceHomologyFinite

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-! Guidance from the project lead (the requester):

Route (the project lead): Grassmann proved (GoodCover.thomSpaceCohomology_of_lowDegree, CohRank) that for k, m ≥ 10
the rational cohomology H^{k+8}(Th γ;ℚ) is finite-dimensional and spanned by the images of p₁²U, p₂U
(surjective_thomSpaceSpanMap, rank_thomSpaceCohomology_le_two). Derive the torsion-detection form
Work.ThomBordism.Grassmann.ThomSpaceClassesDetect k m U Φ (see Grassmann/ThomTarget.lean for the exact Prop):
for y ∈ H_{k+8}(T;ℤ) with ⟨p₁²U, y⟩ = ⟨p₂U, y⟩ = 0, y is torsion.

The proof given here uses the *source*-level form of the span theorem (`lowDegreeCohomology`, proved):
the two classes of `H^{k+8}(T;ℤ)` in question are the images under the `ℤ`-linear isomorphism
`Ψ = Φ ∘ (Thom isomorphism)` of the two classes `p₁(γ)²`, `p₂(γ)` of `H⁸(G;ℤ)`, whose rationalisations
`1 ⊗ p₁²`, `1 ⊗ p₂` span `ℚ ⊗[ℤ] H⁸(G;ℤ)`.  Hence the `ℤ`-bilinear pairing `a ↦ ⟨Ψ a, y⟩` is a
`ℤ`-linear functional whose base change to `ℚ` vanishes on a spanning pair, so it is zero; surjectivity
of `Ψ` then shows that *every* integral class pairs to zero with `y`, and
`Work.Cohomology.kronH_kernel_eq_torsion` (with the finite generation
`Torsion.thomSpaceHomologyFinite`) concludes that `y` is torsion.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace Work.ThomBordism.Grassmann

noncomputable section

/-- **The `Φ`-argument: two rationally spanning classes detect the vanishing of an integral
functional.**  If `a₁, a₂ ∈ A` are such that `1 ⊗ a₁` and `1 ⊗ a₂` span `ℚ ⊗[ℤ] A`, then a
`ℤ`-linear functional `f : A →ₗ[ℤ] ℤ` vanishing on both vanishes identically: its base change
`f ⊗ ℚ : ℚ ⊗[ℤ] A →ₗ[ℚ] ℚ` is a `ℚ`-linear functional vanishing on a spanning pair. -/
theorem linearMap_eq_zero_of_pair_spanning {A : Type*} [AddCommGroup A] [Module ℤ A]
    (f : A →ₗ[ℤ] ℤ) (a₁ a₂ : A)
    (hspan : Function.Surjective fun p : ℚ × ℚ =>
      p.1 • ((1 : ℚ) ⊗ₜ[ℤ] a₁) + p.2 • ((1 : ℚ) ⊗ₜ[ℤ] a₂))
    (h₁ : f a₁ = 0) (h₂ : f a₂ = 0) : f = 0 := by
  let F : (ℚ ⊗[ℤ] A) →ₗ[ℚ] ℚ :=
    { toFun := fun z => (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ) ((f.baseChange ℚ) z)
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }
  have hF : ∀ (q : ℚ) (a : A), F (q ⊗ₜ[ℤ] a) = q * ((f a : ℤ) : ℚ) := by
    intro q a
    change (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ) ((f.baseChange ℚ) (q ⊗ₜ[ℤ] a))
      = q * ((f a : ℤ) : ℚ)
    rw [f.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul ℚ, zsmul_eq_mul]
    ring
  have hF0 : F = 0 := by
    apply LinearMap.ext
    intro z
    obtain ⟨p, rfl⟩ := hspan z
    rw [map_add, map_smul, map_smul, hF 1 a₁, hF 1 a₂, h₁, h₂]
    simp
  apply LinearMap.ext
  intro a
  have h : F ((1 : ℚ) ⊗ₜ[ℤ] a) = 0 := by rw [hF0]; rfl
  rw [hF 1 a, one_mul] at h
  exact_mod_cast h

theorem thomSpaceClassesDetect_of_lowDegree (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m)
    (U : Work.Thom.ThomClass (Work.ThomBordism.Grassmann.tautologicalBundle k m) k)
    (Φ : Work.Thom.OpenThom (Work.ThomBordism.Grassmann.tautologicalBundle k m) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ
        (Work.ThomBordism.Grassmann.sset (Work.ThomBordism.Grassmann.TautologicalThomSpace k m))).homology (k + 8)) :
    Work.ThomBordism.Grassmann.ThomSpaceClassesDetect k m U Φ := by
  intro y hy1 hy2
  -- the isomorphism `Ψ` sending `p₁(γ)²`, `p₂(γ)` to the two named classes of the Thom space
  let Ψ : (Work.Cohomology.cochainC ℤ (sset (OG k m))).homology 8 ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ
        (sset (TautologicalThomSpace k m))).homology (k + 8) :=
    (U.thomEquiv 8).trans Φ
  have hΨ1 : Ψ (p1Sq k m) = thomSpaceClass1 k m U Φ := rfl
  have hΨ2 : Ψ (p2 k m) = thomSpaceClass2 k m U Φ := rfl
  -- the pairing functional
  let K : (Work.Cohomology.cochainC ℤ
        (sset (TautologicalThomSpace k m))).homology (k + 8) →ₗ[ℤ]
      ((Work.Cohomology.chainC ℤ
        (sset (TautologicalThomSpace k m))).homology (k + 8) →ₗ[ℤ] ℤ) :=
    Work.Cohomology.kronH ℤ (sset (TautologicalThomSpace k m)) (k + 8)
  let g : (Work.Cohomology.cochainC ℤ (sset (OG k m))).homology 8 →ₗ[ℤ] ℤ :=
    (K.flip y).comp (Ψ : _ →ₗ[ℤ] _)
  have hg1 : g (p1Sq k m) = 0 := by
    show K (Ψ (p1Sq k m)) y = 0
    rw [hΨ1]
    exact hy1
  have hg2 : g (p2 k m) = 0 := by
    show K (Ψ (p2 k m)) y = 0
    rw [hΨ2]
    exact hy2
  -- the two classes span `ℚ ⊗ H⁸(G;ℤ)` rationally
  have hspan : Function.Surjective fun p : ℚ × ℚ =>
      p.1 • ((1 : ℚ) ⊗ₜ[ℤ] p1Sq k m) + p.2 • ((1 : ℚ) ⊗ₜ[ℤ] p2 k m) := by
    simpa only [p1SqRat, p2Rat] using (lowDegreeCohomology k m hk hm).2.2.2
  have hg : g = 0 :=
    linearMap_eq_zero_of_pair_spanning g (p1Sq k m) (p2 k m) hspan hg1 hg2
  -- hence every class pairs to zero with `y`
  have hall : ∀ a : (Work.Cohomology.cochainC ℤ
      (sset (TautologicalThomSpace k m))).homology (k + 8), K a y = 0 := by
    intro a
    obtain ⟨b, rfl⟩ := Ψ.surjective a
    show K (Ψ b) y = 0
    exact LinearMap.congr_fun hg b
  -- finite generation + the integral universal coefficient theorem finish
  refine (Work.Cohomology.kronH_kernel_eq_torsion (sset (TautologicalThomSpace k m))
    (fun n => Work.ThomBordism.Grassmann.Torsion.thomSpaceHomologyFinite k m n) (k + 8) y).mp ?_
  intro a
  exact hall a

end

end Work.ThomBordism.Grassmann

