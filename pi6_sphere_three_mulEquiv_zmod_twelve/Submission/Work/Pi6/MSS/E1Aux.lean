import Mathlib
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.PagesComp
import Submission.Work.Pi6.MSS.TensorDefs
import Submission.Work.SSSR.grFMap
import Submission.Work.SSSR.Filtration
import Submission.Work.SSSR.SSetChain
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Auxiliary definitions for the duality of the `E_1` row of the Serre spectral sequence

This file collects the definitions needed to state (and prove) that the cohomological `E_1` row of
the Serre spectral sequence of a Serre fibration over a simply connected base, over a field `𝕜`,
is the `𝕜`-dual of the chain level `E_1` row.

* `serreSubSSet f s` — the `s`-th Serre subcomplex of `X` over `Y` (the preimage of the
  `s`-skeleton), as a simplicial set;
* `serreChains 𝕜 f s` — its singular chain complex;
* `serreChainsIncl 𝕜 f s` — the inclusion of its chains into the chains of `X`;
* `compAnn 𝕜 A n` — the `n`-cochains of `X` vanishing on the chains of a subcomplex `A`.

The main statements using these definitions are

* `Work.Pi6.MSS.coFilt_eq_compAnn` (the Serre cochain filtration `F^s` is the annihilator of the
  chains on the `s`-th Serre subcomplex);
* `Work.Pi6.MSS.serreFiltrationOf` (the shifted Serre filtration of the singular chain complex of
  `E` as a `Work.SSSR.Filtration`);
* `Work.Pi6.MSS.e1CohDual` (the `E_1` row is the dual of the chain level `E_1` row).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

namespace Work.Pi6.MSS

noncomputable section

/-- The `s`-th **Serre subcomplex** of `X` over `Y`: the preimage of the `s`-skeleton of `Y`
(equivalently, the simplices whose image has essential dimension `< s`), seen as a simplicial set. -/
abbrev serreSubSSet {X Y : SSet.{0}} (f : X ⟶ Y) (s : ℕ) : SSet.{0} :=
  ((Work.StemsB.serreSubcomplex f s : X.Subcomplex) : SSet)

/-- The singular chains of the `s`-th Serre subcomplex. -/
abbrev serreChains (𝕜 : Type) [CommRing 𝕜] {X Y : SSet.{0}} (f : X ⟶ Y) (s : ℕ) :
    ChainComplex (ModuleCat 𝕜) ℕ :=
  Work.SSSR.sChains 𝕜 (serreSubSSet f s)

/-- The inclusion of the chains of the `s`-th Serre subcomplex into the chains of `X`. -/
abbrev serreChainsIncl (𝕜 : Type) [CommRing 𝕜] {X Y : SSet.{0}} (f : X ⟶ Y) (s : ℕ) :
    serreChains 𝕜 f s ⟶ Work.SSSR.sChains 𝕜 X :=
  Work.SSSR.sChainMap 𝕜 (Work.StemsB.serreSubcomplex f s).ι

/-- The `n`-cochains of `X` vanishing on the chains of a subcomplex `A ⊆ X`. -/
def compAnn (𝕜 : Type) [CommRing 𝕜] {X : SSet.{0}} (A : X.Subcomplex) (n : ℕ) :
    Submodule 𝕜 (Work.Cohomology.Cochain 𝕜 X n) where
  carrier := {c | ∀ z : (Work.SSSR.sChains 𝕜 (A : SSet)).X n,
    c ((Work.SSSR.sChainMap 𝕜 A.ι).f n z) = 0}
  zero_mem' := by intro z; simp
  add_mem' := by intro a b ha hb z; rw [LinearMap.add_apply, ha z, hb z, add_zero]
  smul_mem' := by intro r c hc z; rw [LinearMap.smul_apply, hc z, smul_zero]

end

end Work.Pi6.MSS
