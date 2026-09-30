import Mathlib
import Submission.Work.Pi6.MSS.e2Add
import Submission.Work.Pi6.MSS.AssembleCore
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.PageData
import Submission.Work.Pi6.K2Z.transfer
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS.e2ColRho

open CategoryTheory CategoryTheory.Limits

/-- The zeroth column `E_2^{0,q}` of the Serre spectral sequence of a Serre fibration over a simply
connected base is finite dimensional and of the same dimension as `H^q(F;𝕜)` (`F = p⁻¹(p e₀)`).
Proof: `Work.Pi6.MSS.e2Add` at `(s,q) = (0,q)` gives `E_2^{0,q} ≅ H^0(B) ⊗ H^q(F)`, and
`H^0(B) ≅ 𝕜` because `B` is path connected (`Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero`
applied to `hconn.1`, then `Work.Pi6.finrank_coh_zero_of_pathConnected`), so the dimension is
`1 * finrank H^q(F)`.  Uses `Module.finrank_tensorProduct` and `Module.Free.of_divisionRing`
(which must be introduced with `letI`/`haveI`); `FiniteDimensional 𝕜 (Coh 𝕜 B 0)` comes from
`Work.Cohomology.singularCohomology_zero`.  The index mismatch `0 + q` vs `q` in the conclusion of
`e2Add` is a `Nat.zero_add` transport along `pEcastN` (or `eqToIso` of `congrArg`). -/
theorem finrank_col (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (q : ℕ) (hq : q ≤ N) :
    FiniteDimensional 𝕜 (↥(Work.Pi6.MSS.pEraw 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q)) ∧
    Module.finrank 𝕜 (↥(Work.Pi6.MSS.pEraw 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q)) =
      Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) := by
  classical
  -- `B` is path connected, since it is simply connected
  haveI hpcB : PathConnectedSpace B :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero (p e₀) hconn.1
  -- `H^0(B;𝕜)` is one-dimensional
  have href : Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 B 0) = 1 :=
    Work.Pi6.finrank_coh_zero_of_pathConnected 𝕜 B
  -- the additive `E_2` identification, at `(s,q) = (0,q)`, with the index `0 + q` transported to `q`
  obtain ⟨eAdd⟩ := Work.Pi6.MSS.e2Add 𝕜 E B p e₀ N hfib hconn hfin 0 q (Nat.zero_le _) hq
  have e0 : Work.Pi6.MSS.pEraw 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q ≅
      ModuleCat.of 𝕜 (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B 0)
        (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) :=
    (Work.Pi6.MSS.pEcastN 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 (Nat.zero_add q)).symm ≪≫ eAdd
  -- finite dimensionality of the two tensor factors
  haveI hB0 : FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 B 0) := by
    obtain ⟨e⟩ := Work.Cohomology.singularCohomology_zero 𝕜 (TopCat.of B)
    haveI : FiniteDimensional 𝕜 (ModuleCat.of 𝕜 𝕜) := inferInstance
    exact e.toLinearEquiv.symm.finiteDimensional
  haveI hFq : FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) := hfin q hq
  refine ⟨?_, ?_⟩
  · -- finite dimensionality transfers along `e0`
    haveI : FiniteDimensional 𝕜 (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B 0)
        (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) := inferInstance
    exact e0.toLinearEquiv.symm.finiteDimensional
  · -- the dimension is `finrank H^0(B) * finrank H^q(F) = 1 * finrank H^q(F)`
    calc Module.finrank 𝕜 (↥(Work.Pi6.MSS.pEraw 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q))
        = Module.finrank 𝕜 (↥(ModuleCat.of 𝕜 (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B 0)
            (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)))) := e0.toLinearEquiv.finrank_eq
      _ = Module.finrank 𝕜 (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B 0)
            (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) := rfl
      _ = Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 B 0) *
            Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :=
          Module.finrank_tensorProduct
      _ = 1 * Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) := by rw [href]
      _ = Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) := one_mul _

end Work.Pi6.MSS.e2ColRho
