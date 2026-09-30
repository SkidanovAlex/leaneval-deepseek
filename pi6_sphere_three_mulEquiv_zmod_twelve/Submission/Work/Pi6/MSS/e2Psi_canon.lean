import Mathlib
import Submission.Work.Pi6.MSS.e2Lbar
import Submission.Work.Pi6.MSS.e2Canon
import Submission.Work.Pi6.MSS.e2Canon_gen
import Submission.Work.Pi6.MSS.e1SerreIso_gen
import Submission.Work.Pi6.MSS.e2Psi_pairing
import Submission.Work.Pi6.MSS.e2PsiCanon
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

theorem e2Psi_canon (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (s q : ℕ) (hs : s ≤ N) (hq : q ≤ N) :
    ∃ T : (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
          (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) →ₗ[𝕜]
        (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
          (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)),
      Function.Bijective T ∧
      ∀ (ξ : TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
          (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
        (v : ↥(Work.Pi6.MSS.e2KerD 𝕜 p s q)),
        Work.Pi6.MSS.e2Lbar 𝕜 E B p s q
            (Work.Pi6.MSS.e2Psi 𝕜 E B p e₀ (Work.Pi6.MSS.e2Row 𝕜 p)
              (Work.Pi6.MSS.e2ColAll 𝕜 p e₀ N hfib hconn hfin) s q ξ) v
          = (Work.Pi6.MSS.e2Canon 𝕜 E B p e₀ N hfib hconn hfin s q hq (T ξ))
              (Work.Pi6.MSS.e2mkQ 𝕜 E B p s q v) :=
  e2PsiCanon 𝕜 E B p e₀ N hfib hconn hfin s q hs hq

end Work.Pi6.MSS
