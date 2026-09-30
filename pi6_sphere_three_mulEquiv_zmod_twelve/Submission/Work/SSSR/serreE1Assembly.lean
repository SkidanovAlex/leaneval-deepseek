import Mathlib
import Submission.Work.SSSR.serreE1Defs
import Submission.Work.SSSR.serreE1Graded
import Submission.Work.SSSR.serreE1Piece
import Submission.Work.SSSR.homology_sigma
import Submission.Work.SSSR.serreE1CoefIso
import Submission.Work.SSSR.serreE1Transport
import Submission.Work.SSSR.transportIsoPath_trans
import Submission.Work.SSSR.transportIsoPath_homotopic
import Submission.Work.SSSR.fibreTrivializationOfSimplyConn
import Submission.Work.SSSR.TensorFG
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The coefficient module of the E¹ page: the homology of the fibre `F = p⁻¹(p e₀)`. -/
abbrev coefM (p : C(E, B)) (e₀ : E) (t : ℕ) : ModuleCat R :=
  (Work.SSSR.Cohomology.singularChains R (TopCat.of (Work.SSSR.StemsB.fibre p (p e₀)))).homology t

/-- The normalised chain complex of the singular simplicial set of the base. -/
abbrev Nn (B : Type) [TopologicalSpace B] : ChainComplex (ModuleCat R) ℕ :=
  (sSing B).normalizedChainComplex (ModuleCat.of R R)

/-- The shifted Serre filtration of the singular complex of `E` along `p`. -/
abbrev Fc (p : C(E, B)) : ℕ ⥤ ChainComplex (ModuleCat R) ℕ := serF R (sSingP p)

/-- The trivialisation of the local system `b ↦ H_t(p⁻¹b)` given by the canonical transport. -/
noncomputable def triv (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t : ℕ) (b : B) :
    Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b) t ≅ coefM p e₀ t :=
  (Classical.choose (fibreTrivializationOfSimplyConn p (p e₀) t
    (fun {b b'} γ => transportIsoPath p hfib γ t)
    (fun γ δ => transportIsoPath_trans p hfib t γ δ)
    (fun γ γ' H => transportIsoPath_homotopic p hfib t γ γ' H) hc)) b

end

end Work.SSSR
