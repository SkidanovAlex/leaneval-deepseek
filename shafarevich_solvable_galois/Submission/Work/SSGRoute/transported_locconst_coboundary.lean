import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.isCoboundary2On_kerSuccCocycle_of_continuous_local_lift
import Submission.Work.SSGRoute.kerSucc_conj_eq_mk_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

set_option maxHeartbeats 1600000

/-!
# Transporting a locally constant coboundary through an equivariant `e : ker ↪ E(m,τ)`

`isCoboundary2On_kerSuccCocycle_of_continuous_local_lift` produces a primitive `b` of the section
`2`-cocycle `κ = kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φ s hs` on a subgroup `H ≤ G_ℚ`, valued in the
kernel of the projection `flowGroupSucc` and locally constant there.  What is needed downstream is
the corresponding statement for the *graded-piece valued* cocycle
`(σ,τ) ↦ e (κ σ τ)`, where `e : ker → E(m,τ)` is the additive `G`-equivariant identification of
`exists_kerSuccAddEquiv_equivariant`.

The transport uses exactly the two structural facts about `e` that the equivariance hypothesis `he`
and the centrality of the kernel (`kerSucc_conj_eq_mk_one`) provide: the conjugation action of `s
(φ σ)` on the kernel only depends on the `G`-coordinate `(s (φ σ)).right`, which is
`AlgEquiv.restrictNormalHom K σ` by `hs` and `hflow`; so `he` turns the transport of the
conjugated term into the `galois action` of `σ`, and additivity of `e` handles the rest.
-/

/-- The `G`-coordinate of the chosen section `s (φ σ)` is `AlgEquiv.restrictNormalHom K σ`. -/
theorem section_right_eq_restrictNormalHom (p : ℕ)
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] (i j m : ℕ)
    (φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hflow : ∀ σ : SSGRoute.GalQ, Work.CohomologicalShrinking.flowQuot p (K ≃ₐ[ℚ] K) m i j (φ σ) =
        AlgEquiv.restrictNormalHom K σ)
    (s : Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j →
      Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
        (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hs : ∀ x, Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) m i j (s x) = x)
    (σ : SSGRoute.GalQ) :
    (s (φ σ)).right = AlgEquiv.restrictNormalHom K σ := by
  rw [← flowGroupSucc_right p (K ≃ₐ[ℚ] K) m i j (s (φ σ)), hs]
  exact hflow σ

theorem transported_locconst_coboundary (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (i j m : ℕ)
    (φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hflow : ∀ σ : SSGRoute.GalQ, Work.CohomologicalShrinking.flowQuot p (K ≃ₐ[ℚ] K) m i j (φ σ) =
        AlgEquiv.restrictNormalHom K σ)
    (hopen : IsOpen (φ.ker : Set SSGRoute.GalQ))
    (e : Additive ↥(Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker ≃+
        Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j)
    (he : ∀ (g : K ≃ₐ[ℚ] K) (x : Additive ↥(Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker),
      e (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) m i j)
        (SemidirectProduct.mk 1 g : Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
          (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
        (Additive.toMul x))) = g • e x)
    (s : Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j →
      Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
        (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hs : ∀ x, Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) m i j (s x) = x) (h1 : s 1 = 1)
    (H : Subgroup SSGRoute.GalQ)
    (l : ↥H →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
          (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hl : ∀ σ : ↥H, SSGRoute.LiftsFlowAt (l σ) (φ σ))
    (hcont : IsOpen (l.ker : Set ↥H)) :
    SSGRoute.IsCoboundary2On (AlgEquiv.restrictNormalHom K) H
      (fun σ τ => e (Work.SSGRoute.kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φ s hs σ τ)) := by
  classical
  obtain ⟨b, hb_loc, hb_cob⟩ :=
    isCoboundary2On_kerSuccCocycle_of_continuous_local_lift p K i j m φ hopen s hs h1 H l hl hcont
  refine ⟨fun σ => e (b σ), ?_, ?_⟩
  · -- local constancy is inherited pointwise from `b`
    obtain ⟨U, hUopen, hU⟩ := hb_loc
    exact ⟨U, hUopen, fun g hg u hu huH => congrArg (fun y => e y) (hU g hg u hu huH)⟩
  · -- the coboundary identity: transport the one for `b` through the additive map `e`
    intro σ hσ τ hτ
    have hsr : (s (φ σ)).right = AlgEquiv.restrictNormalHom K σ :=
      section_right_eq_restrictNormalHom p K i j m φ hflow s hs σ
    -- conjugation by `s (φ σ)` only sees its `G`-coordinate (centrality of the kernel)
    have hconj : Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
          (flowGroupSucc p (K ≃ₐ[ℚ] K) m i j) (s (φ σ)) (Additive.toMul (b τ)))
        = Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
          (flowGroupSucc p (K ≃ₐ[ℚ] K) m i j)
          ((SemidirectProduct.mk 1 (AlgEquiv.restrictNormalHom K σ) :
            flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2))
          (Additive.toMul (b τ))) := by
      congr 1
      rw [show s (φ σ) = SemidirectProduct.mk (s (φ σ)).left (s (φ σ)).right from rfl, hsr]
      exact kerSucc_conj_eq_mk_one p (K ≃ₐ[ℚ] K) i j m (s (φ σ)).left
        (AlgEquiv.restrictNormalHom K σ) (b τ)
    show e (Work.SSGRoute.kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φ s hs σ τ) =
      AlgEquiv.restrictNormalHom K σ • e (b τ) - e (b (σ * τ)) + e (b σ)
    rw [hb_cob σ hσ τ hτ, hconj, map_add, map_sub, he]

end Work.SSGRoute
