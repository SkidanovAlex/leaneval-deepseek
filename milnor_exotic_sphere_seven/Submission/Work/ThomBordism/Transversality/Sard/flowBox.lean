import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.Strat
import Submission.Work.ThomBordism.Transversality.Sard.localInverse_smooth

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The flow box theorem

Let `σ : ℝ^{n+1} → ℝ` be `C^∞` at every point and let `x` be a point with `dσ x ≠ 0`.  Then `σ`
is, near `x`, the first coordinate of a `C^∞` chart: there are open sets `N ∋ x` and
`Ω ∋ (σ x, 0)` in `ℝ × ker (dσ x)` and a `C^∞` bijection `g : Ω → N` with `σ (g u) = u.1`.

The proof is the implicit function theorem: with `f' := fderiv ℝ σ x` surjective and with
complemented kernel, the map `y ↦ (σ y, p (y - x))` (where `p` is a continuous projection of `E`
onto `ker f'`) is an open partial homeomorphism `e` from `E` to `ℝ × ker f'` around `x`, whose
inverse is `C^∞` on a neighbourhood of `e x = (σ x, 0)` by `Sard.contDiffOn_symm_of_contDiffOn`.
The flow box is `g := e.symm` on that neighbourhood.
-/

open scoped ContDiff
open Set

namespace Work.ThomBordism.Transversality.Sard

noncomputable section

theorem flowBox {n : ℕ}
    {σ : EuclideanSpace ℝ (Fin (n+1)) → ℝ}
    (hσ : ∀ y, Work.ThomBordism.Transversality.CInfAt σ y)
    {x : EuclideanSpace ℝ (Fin (n+1))} (hσ' : fderiv ℝ σ x ≠ 0) :
    ∃ (N : Set (EuclideanSpace ℝ (Fin (n+1)))) (Ω : Set (ℝ × ↥((fderiv ℝ σ x).ker)))
      (g : ℝ × ↥((fderiv ℝ σ x).ker) → EuclideanSpace ℝ (Fin (n+1))),
      IsOpen N ∧ x ∈ N ∧ IsOpen Ω ∧ (σ x, 0) ∈ Ω ∧ g (σ x, 0) = x ∧
        Work.ThomBordism.Transversality.CInfOn g Ω ∧ (∀ u ∈ Ω, g u ∈ N) ∧
        (∀ u ∈ Ω, σ (g u) = u.1) ∧ (∀ y ∈ N, ∃ u ∈ Ω, g u = y) := by
  classical
  have hstrict : HasStrictFDerivAt σ (fderiv ℝ σ x) x := (hσ x).hasStrictFDerivAt (by simp)
  have hrange : (fderiv ℝ σ x).range = ⊤ := by
    obtain ⟨v₀, hv₀⟩ : ∃ v, fderiv ℝ σ x v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hσ' (ContinuousLinearMap.ext hc)
    rw [LinearMap.range_eq_top]
    intro t
    refine ⟨(t / fderiv ℝ σ x v₀) • v₀, ?_⟩
    rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ t hv₀
  have hker : (fderiv ℝ σ x).ker.ClosedComplemented :=
    ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range _
  let D := HasStrictFDerivAt.implicitFunctionDataOfComplemented σ (fderiv ℝ σ x) hstrict hrange hker
  let e := D.toOpenPartialHomeomorph
  let p : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] ↥(fderiv ℝ σ x).ker := Classical.choose hker
  have he_coe : (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) = D.prodFun := rfl
  have hprod : D.prodFun = fun y => (σ y, p (y - x)) := by
    funext y
    simp only [ImplicitFunctionData.prodFun_apply]
    rfl
  have he_eq : ∀ y, e y = (σ y, p (y - x)) := fun y => by
    rw [show e y = D.prodFun y from congrFun he_coe y, hprod]
  have hfst : ∀ z : EuclideanSpace ℝ (Fin (n+1)), (e z).1 = σ z := fun z => by rw [he_eq]
  have hex : e x = (σ x, 0) := by rw [he_eq]; simp
  have hxsrc : x ∈ e.source := D.pt_mem_toOpenPartialHomeomorph_source
  -- `e` is smooth everywhere, because `σ` is smooth at every point
  have hpsnd : ∀ y, ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin (n+1)) => p (z - x)) y :=
    fun y => (((p : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] ↥(fderiv ℝ σ x).ker).contDiff).comp
      (contDiff_id.sub contDiff_const)).contDiffAt
  have he_glob : ContDiff ℝ ∞ (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    rw [he_coe, hprod]
    exact (hσ y).prodMk (hpsnd y)
  -- the open set of points at which the derivative of the chart is invertible
  have hfdcont : Continuous (fun y => fderiv ℝ
      (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) y) :=
    he_glob.continuous_fderiv (by simp)
  have hGopen : IsOpen {y | (fderiv ℝ
      (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) y).IsInvertible} :=
    hfdcont.isOpen_preimage {L : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] ℝ × ↥(fderiv ℝ σ x).ker |
      L.IsInvertible} isOpen_setOf_isInvertible
  have hInvx : (fderiv ℝ
      (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) x).IsInvertible := by
    rw [he_coe]
    exact D.isInvertible_fderiv_prodFun
  -- smoothness of the local inverse on a neighbourhood of `e x = (σ x, 0)`
  obtain ⟨W, hWopen, hxW, hWsub, hWright, hWsm⟩ :=
    contDiffOn_symm_of_contDiffOn (G := {y | (fderiv ℝ
        (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) y).IsInvertible})
      hGopen he_glob.contDiffOn (fun y hy => hy) hInvx hxsrc
  refine ⟨e.source ∩ e ⁻¹' W, W,
    (e.symm : ℝ × ↥(fderiv ℝ σ x).ker → EuclideanSpace ℝ (Fin (n+1))),
    e.isOpen_inter_preimage hWopen, ⟨hxsrc, hxW⟩, hWopen, ?_, ?_, hWsm, ?_, ?_, ?_⟩
  · -- `(σ x, 0) ∈ Ω`
    rw [← hex]
    exact hxW
  · -- `g (σ x, 0) = x`
    rw [← hex]
    exact e.left_inv hxsrc
  · -- `g` maps `Ω` into `N`
    intro u hu
    refine ⟨e.symm.map_source (hWsub hu), ?_⟩
    show (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) (e.symm u) ∈ W
    rw [hWright u hu]
    exact hu
  · -- `σ (g u) = u.1`
    intro u hu
    have h := congrArg Prod.fst (hWright u hu)
    rwa [hfst] at h
  · -- every point of `N` is `g u` for some `u ∈ Ω`
    intro y hy
    exact ⟨e y, hy.2, e.left_inv hy.1⟩

end

end Work.ThomBordism.Transversality.Sard
