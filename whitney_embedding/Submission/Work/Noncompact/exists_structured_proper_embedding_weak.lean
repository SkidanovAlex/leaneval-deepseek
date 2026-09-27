import Mathlib
import Submission.Work.Noncompact.weak_whitney
import Submission.Work.Noncompact.exists_pack_data
import Submission.Work.Noncompact.exists_bounded_injective_map

/-!
# A structured proper embedding of a second countable manifold into `ℝ^{2n+1}`

A Hausdorff, second countable, nonempty smooth `n`-manifold `M` admits

* a smooth injective immersion `g : M → ℝ^{2n+1}`,
* a smooth proper function `f : M → ℝ`,
* a nonzero direction `u : ℝ^{2n+1}`,

such that `g x + f x • u` stays in the closed unit ball for every `x`.  Equivalently
`g = b - f • u` where `b : M → ℝ^{2n+1}` is a *bounded* smooth injective immersion and `u` is a
projection direction which is good for the packed map `x ↦ (b x, f x)`.

The construction: take a proper embedding `e : M → ℝ^{2n+1}` (weak Whitney, proved in
`Submission/Work/Noncompact/weak_whitney.lean`), compose it with the bounded injective immersion
`y ↦ y/√(1+‖y‖²)` of `ℝ^{2n+1}` to obtain a bounded smooth injective immersion `b`, add the proper
function `f` as an extra coordinate (`exists_pack_data`), and project back to `ℝ^{2n+1}` along a
direction `u ≠ 0` which avoids the bad sets of the projection argument
(`Work.Projection.exists_good_direction_ne_zero`, applicable because the bad sets have Hausdorff
dimension at most `2n < 2n+1`).  The projection of the packed pair is `b x - f x • u`, whence the
ball bound, while injectivity and the immersion property are exactly the conclusions of
`exists_good_direction_ne_zero`.
-/

namespace Work.Noncompact

open scoped Manifold ContDiff
open Topology Set Function

theorem exists_structured_proper_embedding_weak {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [Nonempty M] :
    ∃ (g : M → EuclideanSpace ℝ (Fin (2 * n + 1))) (f : M → ℝ)
      (u : EuclideanSpace ℝ (Fin (2 * n + 1))),
      u ≠ 0 ∧
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1))))
        ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      IsProperMap f ∧ Function.Injective g ∧
      (∀ x, Function.Injective (mfderiv
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) g x)) ∧
      (∀ x, ‖g x + f x • u‖ ≤ 1) := by
  classical
  haveI : SigmaCompactSpace M := by
    haveI : LocallyCompactSpace M :=
      ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
    exact sigmaCompactSpace_of_locallyCompact_secondCountable
  -- a proper smooth function
  obtain ⟨f, hfsm, hfprop, _⟩ :=
    exists_proper_contMDiff_nonneg (I := 𝓡 n) (M := M)
  -- a proper smooth embedding, composed with a bounded injective immersion
  obtain ⟨e, hesm, _heprop, heinj, heimm⟩ :=
    exists_proper_embedding_euclidean_weak (n := n) (M := M)
  obtain ⟨b, hbsm, hbinj, hbimm, hbbdd⟩ := exists_bounded_injective_map (2 * n + 1)
  set bnd : M → EuclideanSpace ℝ (Fin (2*n+1)) := fun x => b (e x) with hbnd
  have hbndsm : ContMDiff (𝓡 n) (𝓡 (2*n+1)) ∞ bnd := hbsm.comp hesm
  have hbndinj : Function.Injective bnd := hbinj.comp heinj
  have hbndimm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n+1)) bnd x) := by
    intro x
    have h := mfderiv_comp x (f := e) (g := b)
      (hbsm.mdifferentiableAt (by simp)) (hesm.mdifferentiableAt (by simp))
    change Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n+1)) (b ∘ e) x)
    rw [h]
    exact (hbimm (e x)).comp (heimm x)
  have hbndbdd : ∀ x, ‖bnd x‖ ≤ 1 := fun x => hbbdd (e x)
  -- the packed map `x ↦ (bnd x, f x)`
  obtain ⟨P, hPinj, hPproj⟩ := exists_pack_data n
  set pairM : M → (EuclideanSpace ℝ (Fin (2*n+1)) × ℝ) := fun x => (bnd x, f x) with hpairM
  have hpairMsm : ContMDiff (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2*n+1)) × ℝ) ∞ pairM :=
    ContMDiff.prodMk_space hbndsm hfsm
  set Φ' : M → EuclideanSpace ℝ (Fin (2*n+2)) := fun x => P (pairM x) with hΦ'
  have hΦ'sm : ContMDiff (𝓡 n) (𝓡 (2*n+2)) ∞ Φ' := P.contMDiff.comp hpairMsm
  have hΦ'inj : Function.Injective Φ' := by
    refine hPinj.comp ?_
    intro x y hxy
    exact hbndinj (Prod.ext_iff.1 hxy).1
  have hΦ'imm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n+2)) Φ' x) := by
    intro x
    have hchain := mfderiv_comp_clm_of (n := n) (M := M) P pairM hpairMsm x
    have hzero : ∀ z : TangentSpace (𝓡 n) x,
        mfderiv (𝓡 n) (𝓡 (2*n+2)) Φ' x z = 0 → z = 0 := by
      intro z hz
      have h2 : (mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2*n+1)) × ℝ) pairM x) z = 0 := by
        have hz' : (P ∘L mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2*n+1)) × ℝ) pairM x) z
            = 0 := by
          rw [← hchain]
          exact hz
        exact hPinj (hz'.trans (map_zero P).symm)
      have hfst := mfderiv_comp_clm_of (n := n) (M := M)
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (2*n+1))) ℝ) pairM hpairMsm x
      have h4 : mfderiv (𝓡 n) (𝓡 (2*n+1)) bnd x z = 0 := by
        change ((mfderiv (𝓡 n) (𝓡 (2*n+1))
          (⇑(ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (2*n+1))) ℝ) ∘ pairM) x) z) = 0
        rw [hfst]
        change (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (2*n+1))) ℝ)
          ((mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2*n+1)) × ℝ) pairM x) z) = 0
        rw [h2]
        exact map_zero _
      exact hbndimm x (by rw [h4, map_zero])
    intro z w hzw
    exact sub_eq_zero.mp (hzero (z - w) (by rw [map_sub, hzw, sub_self]))
  -- a nonzero good projection direction
  obtain ⟨p, hcov⟩ := Work.Projection.exists_countable_chart_cover n M
  obtain ⟨u, hu0, hu1, hu2⟩ :=
    Work.Projection.exists_good_direction_ne_zero (n := n) (k := 2*n+1) (le_refl _)
      Φ' hΦ'sm hΦ'inj hΦ'imm p hcov
  refine ⟨fun x => Work.Projection.projVec u (Φ' x), f, u, hu0, ?_, hfsm, hfprop, hu1, ?_, ?_⟩
  · exact Work.Projection.contMDiff_comp_clm (Work.Projection.projVec u) Φ' hΦ'sm
  · intro x
    change Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n+1))
      (⇑(Work.Projection.projVec u) ∘ Φ') x)
    rw [Work.Projection.mfderiv_comp_clm (Work.Projection.projVec u) Φ' hΦ'sm x]
    exact hu2 x
  · intro x
    change ‖Work.Projection.projVec u (Φ' x) + f x • u‖ ≤ 1
    have hsplit : Work.Projection.projVec u (Φ' x) = bnd x - f x • u := by
      rw [hΦ', hpairM]
      exact hPproj u (bnd x) (f x)
    rw [hsplit, sub_add_cancel]
    exact hbndbdd x

end Work.Noncompact
