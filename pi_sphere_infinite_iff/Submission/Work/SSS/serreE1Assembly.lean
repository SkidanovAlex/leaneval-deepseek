import Mathlib
import Submission.Work.SSS.serreE1Defs
import Submission.Work.SSS.serreE1Graded
import Submission.Work.SSS.serreE1Piece
import Submission.Work.SSS.homology_sigma
import Submission.Work.SSS.serreE1CoefIso
import Submission.Work.SSS.serreE1Transport
import Submission.Work.SSS.transportIsoPath_trans
import Submission.Work.SSS.transportIsoPath_homotopic
import Submission.Work.SSS.fibreTrivializationOfSimplyConn
import Submission.Work.SSS.TensorFG

/-!
# The assembly of the first page of the Serre spectral sequence

This file collects the degreewise isomorphism

  `thetaD p e₀ hfib hc t ξ hξ d : E1 ξ d t ≅ (tensorComplex (Nn B) (coefM p e₀ t)).X d`

of the `d`-th term of the E¹ row complex of the Serre filtration of `ξ` with the `d`-th term of the
normalised chain complex of the base tensored with the homology of the fibre.  It is the composite
of

* the Eilenberg–Zilber decomposition of the graded pieces (`Work.SSS.serreE1Graded_iso`,
  `Work.SSS.homology_sigma`),
* the σ-piece isomorphisms `H_{d+t}(T_σ, ∂T_σ) ≅ H_t(F_{σ(v₀)})` (`Work.SSS.serreE1Piece`),
* the trivialisation of the local system `b ↦ H_t(p⁻¹b)` by the canonical fibre transport
  (`Work.SSS.fibreTrivializationOfSimplyConn`, `Work.SSS.transportIsoPath`), and
* the degreewise description `∐_σ H_t(F) ≅ (N_*(B) ⊗ H_t(F))_d` (`Work.SSS.serreE1CoefIso`).

**Remaining obligation (not yet formalised, see the notes below).**  To conclude `Work.SSS.serreE1`
it remains to show that these degreewise isomorphisms *commute with the differentials*: the
differential `d¹` of the E¹ row complex, read through them, is the differential `∂ ⊗ id` of the
normalised complex of the base tensored with the fibre homology (`REFS/NOTES_LEAD_SSS.md` §2).

The statements `homology_sigma`, `serreE1Piece` and `serreE1CoefIso` currently only assert
`Nonempty (A ≅ B)`, so the composites above go through `Classical.choice` and are *opaque*: the
compatibility with the differentials cannot be derived from their types, and the relevant
constructions must be exposed as explicit (named) isomorphisms first.  In particular
`serreE1Graded_iso` *is* explicit (`Work.SSS.mapPsi`, `Work.SSS.mapPhi`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The coefficient module of the E¹ page: the homology of the fibre `F = p⁻¹(p e₀)`. -/
abbrev coefM (p : C(E, B)) (e₀ : E) (t : ℕ) : ModuleCat ℤ :=
  (Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p (p e₀)))).homology t

/-- The normalised chain complex of the singular simplicial set of the base. -/
abbrev Nn (B : Type) [TopologicalSpace B] : ChainComplex (ModuleCat ℤ) ℕ :=
  (sSing B).normalizedChainComplex (ModuleCat.of ℤ ℤ)

/-- The shifted Serre filtration of the singular complex of `E` along `p`. -/
abbrev Fc (p : C(E, B)) : ℕ ⥤ ChainComplex (ModuleCat ℤ) ℕ := serF (sSingP p)

/-- The trivialisation of the local system `b ↦ H_t(p⁻¹b)` given by the canonical transport. -/
noncomputable def triv (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ) (b : B) :
    Work.PiS.HZ (Work.StemsB.fibre p b) t ≅ coefM p e₀ t :=
  (Classical.choose (fibreTrivializationOfSimplyConn p (p e₀) t
    (fun {b b'} γ => transportIsoPath p hfib γ t)
    (fun γ δ => transportIsoPath_trans p hfib t γ δ)
    (fun γ γ' H => transportIsoPath_homotopic p hfib t γ γ' H) hc)) b

/-- **The σ-indexed description of the `d`-th term of the E¹ complex.** -/
noncomputable def e1Sig (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t d : ℕ) :
    (grF (Fc p) d).homology (d + t) ≅ (∐ (fun _ : nIndex (sSing B) d => coefM p e₀ t)) :=
  HomologicalComplex.homologyMapIso (Classical.choice (serreE1Graded_iso (sSingP p) d)) (d + t) ≪≫
    Classical.choice (homology_sigma
      (fun σ : nIndex (sSing B) d => pieceAlong (sSingP p) (nIndexSigma (sSing B) d σ))
      (d + t)) ≪≫
    Sigma.mapIso (fun σ : nIndex (sSing B) d =>
      Classical.choice (serreE1Piece p hfib d t (nIndexSigma (sSing B) d σ))) ≪≫
    Sigma.mapIso (fun σ : nIndex (sSing B) d =>
      triv p e₀ hfib hc t (sigmaVert (nIndexSigma (sSing B) d σ)))

/-- **The degreewise isomorphism of the E¹ page with `N_*(B) ⊗ H_t(F)`.** -/
noncomputable def thetaD (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ)
    (ξ : Filtration (Work.Cohomology.singularChains ℤ (TopCat.of E)))
    (hξ : ξ.F = Fc p) (d : ℕ) :
    E1 ξ d t ≅ (tensorComplex (Nn B) (coefM p e₀ t)).X d :=
  eqToIso (congrArg (fun F => (grF F d).homology (d + t)) hξ) ≪≫
    e1Sig p e₀ hfib hc t d ≪≫
    Classical.choice (serreE1CoefIso (sSing B) (coefM p e₀ t) d)

end

end Work.SSS
