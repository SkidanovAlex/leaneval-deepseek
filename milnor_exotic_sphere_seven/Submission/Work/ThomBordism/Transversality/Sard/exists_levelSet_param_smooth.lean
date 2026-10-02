import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.Strat
import Submission.Work.ThomBordism.Transversality.Sard.localInverse_smooth

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Local parametrization of a level set of a `C^∞` function

Let `σ` be `C^∞` at every point of an open set `V ∋ x`, with `σ x = 0` and `fderiv ℝ σ x ≠ 0`.  Then
the level set `{σ = 0}` is, near `x`, the image of a `C^∞` map `γ` defined on an open subset `W` of
`ℝⁿ` (with `n + 1` the dimension of the source): the coordinate on `W` is the projection onto the
kernel of `dσ x`, transported to `ℝⁿ` by a linear equivalence, and `γ` is the local inverse of the
implicit-function open partial homeomorphism `(σ, projection)`, which is `C^∞` on a neighbourhood by
`Sard.contDiffOn_symm_of_contDiffOn`.

This is the `C^∞` counterpart of `Sard.exists_levelSet_param`; it is the form needed when Sard's
theorem is applied to smooth (rather than analytic) data.
-/

open scoped ContDiff MeasureTheory
open MeasureTheory Set

namespace Work.ThomBordism.Transversality.Sard

noncomputable section

set_option maxHeartbeats 800000

theorem exists_levelSet_param_smooth {n : ℕ}
    {V : Set (EuclideanSpace ℝ (Fin (n+1)))} (hV : IsOpen V)
    {σ : EuclideanSpace ℝ (Fin (n+1)) → ℝ} (hσ : ∀ y ∈ V, ContDiffAt ℝ ∞ σ y)
    {x : EuclideanSpace ℝ (Fin (n+1))} (hxV : x ∈ V) (hσx : σ x = 0)
    (hσ' : fderiv ℝ σ x ≠ 0) :
    ∃ (N : Set (EuclideanSpace ℝ (Fin (n+1)))) (W : Set (EuclideanSpace ℝ (Fin n)))
      (γ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n+1))),
      IsOpen N ∧ x ∈ N ∧ N ⊆ V ∧ IsOpen W ∧ 0 ∈ W ∧ γ 0 = x ∧
      ContDiffOn ℝ ∞ γ W ∧ (∀ u ∈ W, γ u ∈ N) ∧
      (∀ u ∈ W, σ (γ u) = 0) ∧ (∀ y ∈ N, σ y = 0 → ∃ u ∈ W, γ u = y) := by
  classical
  have hstrict : HasStrictFDerivAt σ (fderiv ℝ σ x) x := (hσ x hxV).hasStrictFDerivAt (by simp)
  have hrange : LinearMap.range (fderiv ℝ σ x : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ] ℝ) = ⊤ := by
    obtain ⟨v₀, hv₀⟩ : ∃ v, fderiv ℝ σ x v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hσ' (ContinuousLinearMap.ext hc)
    rw [LinearMap.range_eq_top]
    intro t
    refine ⟨(t / fderiv ℝ σ x v₀) • v₀, ?_⟩
    rw [LinearMap.map_smul]
    simp only [smul_eq_mul]
    exact div_mul_cancel₀ t hv₀
  have hker : (fderiv ℝ σ x).ker.ClosedComplemented :=
    ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range _
  let D := HasStrictFDerivAt.implicitFunctionDataOfComplemented σ (fderiv ℝ σ x) hstrict hrange hker
  let e := D.toOpenPartialHomeomorph
  let p : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] ↥(fderiv ℝ σ x).ker := Classical.choose hker
  have hleft : D.leftFun = σ := rfl
  have hright : D.rightFun = fun y => p (y - x) := rfl
  have he_coe : (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) = D.prodFun := rfl
  have hprod : D.prodFun = fun y => (σ y, p (y - x)) := by
    funext y
    simp only [ImplicitFunctionData.prodFun_apply, hleft, hright]
  have he_eq : ∀ y : EuclideanSpace ℝ (Fin (n+1)), e y = (σ y, p (y - x)) := by
    intro y
    rw [he_coe, hprod]
  have hpsnd : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (n+1)) => p (y - x)) x :=
    (((p : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] ↥(fderiv ℝ σ x).ker).contDiff).comp
      (contDiff_id.sub contDiff_const)).contDiffAt
  have he_sm : ContDiffAt ℝ ∞ (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) x := by
    rw [he_coe, hprod]
    exact (hσ x hxV).prodMk hpsnd
  have hInv : (fderiv ℝ (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) x).IsInvertible := by
    rw [he_coe]
    exact D.isInvertible_fderiv_prodFun
  -- the open set on which the derivative of the chart is invertible
  have hpsnd_all : ∀ y ∈ V, ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin (n+1)) => p (z - x)) y :=
    fun y _ => (((p : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] ↥(fderiv ℝ σ x).ker).contDiff).comp
      (contDiff_id.sub contDiff_const)).contDiffAt
  have he_smOn : ContDiffOn ℝ ∞ (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) V := by
    intro y hy
    rw [he_coe, hprod]
    exact ((hσ y hy).prodMk (hpsnd_all y hy)).contDiffWithinAt
  have hfdcont : ContinuousOn
      (fun y => fderiv ℝ (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) y) V := by
    have hle1 : (0 : ℕ∞ω) + 1 ≤ ∞ := by
      rw [show (0 : ℕ∞ω) + 1 = (↑(0 + 1) : ℕ∞ω) from rfl,
        show (∞ : ℕ∞ω) = (↑(⊤ : ℕ∞) : ℕ∞ω) from rfl]
      exact WithTop.coe_le_coe.mpr le_top
    exact (ContDiffOn.fderiv_of_isOpen he_smOn hV hle1).continuousOn_zero
  have hGopen : IsOpen (V ∩ (fun y => fderiv ℝ
      (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) y) ⁻¹'
        {L : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] ℝ × ↥(fderiv ℝ σ x).ker | L.IsInvertible}) :=
    hfdcont.isOpen_inter_preimage hV isOpen_setOf_isInvertible
  obtain ⟨W₀, hW₀open, hW₀mem, hW₀sub, hW₀right, hW₀sm⟩ :=
    contDiffOn_symm_of_contDiffOn hGopen (he_smOn.mono inter_subset_left)
      (fun y hy => hy.2) ⟨hxV, by rw [he_coe]; exact D.isInvertible_fderiv_prodFun⟩
      D.pt_mem_toOpenPartialHomeomorph_source
  have hex : e x = (0, 0) := by
    rw [he_eq]
    simp only [hσx, sub_self, map_zero]
  have hxsrc : x ∈ e.source := D.pt_mem_toOpenPartialHomeomorph_source
  set W₁ : Set (ℝ × ↥(fderiv ℝ σ x).ker) :=
    W₀ ∩ (e.target ∩ (e.symm : ℝ × ↥(fderiv ℝ σ x).ker → EuclideanSpace ℝ (Fin (n+1))) ⁻¹' V)
    with hW₁def
  have hW₁open : IsOpen W₁ := hW₀open.inter (e.isOpen_inter_preimage_symm hV)
  have hW₁mem : e x ∈ W₁ := by
    refine ⟨hW₀mem, e.map_source hxsrc, ?_⟩
    · show (e.symm : ℝ × ↥(fderiv ℝ σ x).ker → EuclideanSpace ℝ (Fin (n+1))) (e x) ∈ V
      rw [e.left_inv hxsrc]
      exact hxV
  have hW₁sm : ContDiffOn ℝ ∞
      (e.symm : ℝ × ↥(fderiv ℝ σ x).ker → EuclideanSpace ℝ (Fin (n+1))) W₁ :=
    hW₀sm.mono inter_subset_left
  have hW₁right : ∀ z ∈ W₁, e (e.symm z) = z := fun z hz => hW₀right z hz.1
  have hW₁V : ∀ z ∈ W₁,
      (e.symm : ℝ × ↥(fderiv ℝ σ x).ker → EuclideanSpace ℝ (Fin (n+1))) z ∈ V :=
    fun z hz => hz.2.2
  have hfinrank : Module.finrank ℝ ↥(LinearMap.ker ((fderiv ℝ σ x).toLinearMap)) = n := by
    have h := LinearMap.finrank_range_add_finrank_ker ((fderiv ℝ σ x).toLinearMap)
    rw [hrange] at h
    have h1 : Module.finrank ℝ ↥(⊤ : Submodule ℝ ℝ) = 1 := by simp
    rw [h1] at h
    have h2 : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n + 1 := by
      rw [finrank_euclideanSpace, Fintype.card_fin]
    rw [h2] at h
    omega
  let L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] ↥(LinearMap.ker ((fderiv ℝ σ x).toLinearMap)) :=
    (LinearEquiv.ofFinrankEq (EuclideanSpace ℝ (Fin n))
      ↥(LinearMap.ker ((fderiv ℝ σ x).toLinearMap))
      (by rw [finrank_euclideanSpace, Fintype.card_fin, hfinrank])).toContinuousLinearEquiv
  let γ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n+1)) :=
    fun u => (e.symm : ℝ × ↥(fderiv ℝ σ x).ker → EuclideanSpace ℝ (Fin (n+1))) (0, L u)
  let W : Set (EuclideanSpace ℝ (Fin n)) := {u | ((0 : ℝ), L u) ∈ W₁}
  let N : Set (EuclideanSpace ℝ (Fin (n+1))) :=
    e.source ∩ (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) ⁻¹' W₁
  have hproj_l : Continuous fun u : EuclideanSpace ℝ (Fin n) => ((0 : ℝ), L u) :=
    (ContinuousLinearMap.prod (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ↥(fderiv ℝ σ x).ker)).continuous
  have hγ0 : γ 0 = x := by
    show (e.symm : ℝ × ↥(fderiv ℝ σ x).ker → EuclideanSpace ℝ (Fin (n+1))) ((0 : ℝ), L 0) = x
    have h0 : ((0 : ℝ), L 0) = e x := by rw [map_zero, hex]
    rw [h0, e.left_inv hxsrc]
  refine ⟨N, W, γ, e.isOpen_inter_preimage hW₁open, ⟨hxsrc, hW₁mem⟩, ?_,
    hW₁open.preimage hproj_l, ?_, hγ0, ?_, ?_, ?_, ?_⟩
  · -- N ⊆ V
    intro y hy
    have h := hW₁V (e y) hy.2
    rwa [e.left_inv hy.1] at h
  · -- 0 ∈ W
    show ((0 : ℝ), L 0) ∈ W₁
    have h0 : ((0 : ℝ), L 0) = e x := by rw [map_zero, hex]
    rw [h0]; exact hW₁mem
  · -- CInfOn γ W
    have hlin : ContDiffOn ℝ ∞ (fun u : EuclideanSpace ℝ (Fin n) => ((0 : ℝ), L u)) W :=
      (ContinuousLinearMap.prod (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ↥(fderiv ℝ σ x).ker)).contDiff.contDiffOn
    exact hW₁sm.comp hlin (fun u hu => hu)
  · -- γ '' W ⊆ N
    intro u hu
    have hz : ((0 : ℝ), L u) ∈ W₁ := hu
    refine ⟨e.symm.map_source hz.2.1, ?_⟩
    show e ((e.symm : ℝ × ↥(fderiv ℝ σ x).ker → EuclideanSpace ℝ (Fin (n+1))) ((0 : ℝ), L u)) ∈ W₁
    rw [hW₁right _ hz]
    exact hz
  · -- σ ∘ γ = 0
    intro u hu
    have hz : ((0 : ℝ), L u) ∈ W₁ := hu
    have h1 : e (γ u) = ((0 : ℝ), L u) := hW₁right _ hz
    have : (e (γ u)).1 = σ (γ u) := by rw [he_eq]
    rw [← this, h1]
  · -- covering property
    intro y hy hyσ
    have hy1 : y ∈ e.source := hy.1
    have hy2 : e y ∈ W₁ := hy.2
    have hey : e y = ((0 : ℝ), p (y - x)) := by
      rw [he_eq]
      simp only [hyσ]
    refine ⟨L.symm (p (y - x)), ?_, ?_⟩
    · show ((0 : ℝ), L (L.symm (p (y - x)))) ∈ W₁
      have h2 : ((0 : ℝ), L (L.symm (p (y - x)))) = e y := by
        rw [hey, ContinuousLinearEquiv.apply_symm_apply]
      rw [h2]; exact hy2
    · show (e.symm : ℝ × ↥(fderiv ℝ σ x).ker → EuclideanSpace ℝ (Fin (n+1)))
        ((0 : ℝ), L (L.symm (p (y - x)))) = y
      rw [ContinuousLinearEquiv.apply_symm_apply, ← hey, e.left_inv hy1]

end

end Work.ThomBordism.Transversality.Sard
