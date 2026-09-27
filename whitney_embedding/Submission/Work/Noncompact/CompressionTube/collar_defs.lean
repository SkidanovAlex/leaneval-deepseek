import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.smooth_left_inverse_tools

/-!
# The basic vocabulary of the collar/transverse-coordinate chapter

This module collects the definition `Transverse` (the pointwise conclusion of the target lemma
`Work.Noncompact.CompressionTube.collar_transverse_coordinate`) together with the three elementary
lemmas about it that every other file of the chapter uses:

* `mfderiv_g_velocity` : `dg (γ s) (γ'(s)) = 1` when `g ∘ γ = id`;
* `mfderiv_velocity_eq_zero` : a function vanishing on the line has derivative killing `γ'(s)`;
* `eq_of_agree_on_ker` : the *matching criterion* — two continuous linear maps out of `T_{γ s}M`
  which both kill the velocity of `γ` and agree on `ker dg` are equal.

These definitions were originally in `collar_transverse_coordinate`; they live here so that the
supporting lemmas of the chapter (which all need `Transverse`) can be stated without importing the
file that contains the target theorem itself.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- **Transversality of a function along a line.**  For a smooth `γ : ℝ → M` and a smooth
`g : M → ℝ` we say that `ψ : M → ℝ^{n-1}` is *transverse at `γ s`* if the pair `(ψ, g)` has
injective manifold derivative at `γ s`.  Equivalently: the differential of `ψ` at `γ s` is
injective on `ker (dg)`.  This is the conclusion that the target lemma asks for, at every `s`. -/
def Transverse {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    (γ : ℝ → M) (g : M → ℝ) (ψ : M → EuclideanSpace ℝ (Fin (n - 1))) (s : ℝ) : Prop :=
  ∀ v : TangentSpace (MC n) (γ s), mfderiv (MC n) (MC (n - 1)) ψ (γ s) v = 0 →
    mfderiv (MC n) MCreal g (γ s) v = 0 → v = 0

/-- If `g ∘ γ = id` then the derivative of `g` in the direction of the velocity of `γ` is `1`. -/
theorem mfderiv_g_velocity {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {γ : ℝ → M} {g : M → ℝ} (hgcore : ∀ s : ℝ, g (γ s) = s)
    (hγ : ContMDiff MCreal (MC n) smoothOrder γ) (hg : ContMDiff (MC n) MCreal smoothOrder g)
    (s : ℝ) :
    mfderiv (MC n) MCreal g (γ s) (mfderiv MCreal (MC n) γ s 1) = 1 := by
  have hn : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hγd : MDifferentiableAt MCreal (MC n) γ s := hγ.mdifferentiableAt (x := s) hn
  have hgd : MDifferentiableAt (MC n) MCreal g (γ s) := hg.mdifferentiableAt (x := γ s) hn
  have hcomp : mfderiv MCreal MCreal (fun t : ℝ => g (γ t)) s =
      (mfderiv (MC n) MCreal g (γ s)).comp (mfderiv MCreal (MC n) γ s) :=
    mfderiv_comp (I := MCreal) (I' := MC n) (I'' := MCreal) (f := γ) (g := g) s hgd hγd
  rw [show (fun t : ℝ => g (γ t)) = id from funext hgcore] at hcomp
  rw [mfderiv_id] at hcomp
  have h := congrArg (fun (L : TangentSpace MCreal s →L[ℝ] TangentSpace MCreal s) => L 1)
    hcomp.symm
  simp only [ContinuousLinearMap.id_apply] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- A function vanishing on the line has derivative killing the velocity of `γ`. -/
theorem mfderiv_velocity_eq_zero {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {γ : ℝ → M} {ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    (hψ : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ) (h0 : ∀ s, ψ (γ s) = 0) (s : ℝ) :
    mfderiv (MC n) (MC (n - 1)) ψ (γ s) (mfderiv MCreal (MC n) γ s 1) = 0 := by
  have hn : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hγd : MDifferentiableAt MCreal (MC n) γ s := hγ.mdifferentiableAt (x := s) hn
  have hψd : MDifferentiableAt (MC n) (MC (n - 1)) ψ (γ s) := hψ.mdifferentiableAt (x := γ s) hn
  have hcomp : mfderiv MCreal (MC (n - 1)) (fun t : ℝ => ψ (γ t)) s =
      (mfderiv (MC n) (MC (n - 1)) ψ (γ s)).comp (mfderiv MCreal (MC n) γ s) :=
    mfderiv_comp (I := MCreal) (I' := MC n) (I'' := MC (n - 1)) (f := γ) (g := ψ) s hψd hγd
  rw [show (fun t : ℝ => ψ (γ t)) = fun _ : ℝ => (0 : EuclideanSpace ℝ (Fin (n - 1)))
      from funext h0] at hcomp
  rw [mfderiv_const] at hcomp
  have h := congrArg (fun (L : TangentSpace MCreal s →L[ℝ] EuclideanSpace ℝ (Fin (n - 1))) => L 1)
    hcomp
  simp only [zero_apply] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- **The matching criterion.**  Two continuous linear maps out of the tangent space at `γ s` which
both kill the velocity of `γ` and which agree on `ker (dg)` are equal.  This is the criterion used
to identify the differentials of two functions which are aligned along the line. -/
theorem eq_of_agree_on_ker {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {γ : ℝ → M} {g : M → ℝ} (hgcore : ∀ s : ℝ, g (γ s) = s)
    (hγ : ContMDiff MCreal (MC n) smoothOrder γ) (hg : ContMDiff (MC n) MCreal smoothOrder g)
    (s : ℝ)
    {L₁ L₂ : TangentSpace (MC n) (γ s) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1))}
    (h₁ : L₁ (mfderiv MCreal (MC n) γ s 1) = 0) (h₂ : L₂ (mfderiv MCreal (MC n) γ s 1) = 0)
    (h : ∀ v : TangentSpace (MC n) (γ s), mfderiv (MC n) MCreal g (γ s) v = 0 → L₁ v = L₂ v) :
    L₁ = L₂ := by
  ext v
  set c : ℝ := (mfderiv (MC n) MCreal g (γ s) v : ℝ) with hc
  have hv : mfderiv (MC n) MCreal g (γ s)
      (v - c • (mfderiv MCreal (MC n) γ s 1)) = 0 := by
    rw [map_sub, map_smul, mfderiv_g_velocity hgcore hγ hg s, hc, smul_eq_mul, mul_one, sub_self]
  have hkey := h _ hv
  have hdecomp : v = (v - c • (mfderiv MCreal (MC n) γ s 1)) +
      c • (mfderiv MCreal (MC n) γ s 1) := by abel
  conv_lhs => rw [hdecomp]
  conv_rhs => rw [hdecomp]
  rw [map_add, map_add, map_smul, map_smul, h₁, h₂, hkey]

end

end Work.Noncompact.CompressionTube
