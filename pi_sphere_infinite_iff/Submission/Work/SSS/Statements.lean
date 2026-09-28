import Mathlib
import Submission.Work.SSS.Packet
import Submission.Work.SSS.TensorFG
import Submission.Work.SSS.SSetChain
import Submission.Work.PiS.Interfaces

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The two inputs of Serre's three-for-two theorem (area SSS)

The three-for-two theorem `Work.PiS.SerreFGThreeForTwo` for a Serre fibration `p : E → B` over a
simply connected base is assembled (in `Submission/Work/SSS/Assembly.lean`) from exactly two
statements:

* `Work.SSS.PacketStatement` — the **convergence theorem**: the spectral sequence of any saturated
  filtration `ξ` of a chain complex of `ℤ`-modules gives an `SSPacket ξ`
  (`Work.SSS.SSPacket`: the image filtration, its graded pieces as subquotients of the E² page, and
  the two edge statements), which is pure homological algebra;
* `Work.SSS.SerreE2Statement` — the **computation of the E² page** of the Serre filtration of the
  singular complex of `p`: the `Filtration` of `C_*(E)` whose `p`-th term is the singular chain
  complex of the preimage of the `p`-skeleton of `Sing B` has
  `E²_{s,t} ≅ H_s(B; H_t(F))`, `B` simply connected, `F = p⁻¹(p e₀)` the fibre.  Read in the Serre
  class of finitely generated abelian groups this gives the three properties below.
-/

set_option autoImplicit false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **The convergence theorem for the spectral sequence of a saturated filtration**
(`Work.SSS.SSPacket`). -/
def PacketStatement : Prop :=
  ∀ (C : ChainComplex (ModuleCat ℤ) ℕ) (ξ : Filtration C), SSPacket ξ

/-- **The E² page of the Serre spectral sequence of a Serre fibration over a simply connected
base.**  Concretely: there is a filtration `ξ` of the singular chain complex of `E` (the Serre
filtration by the skeleta of `Sing B`) such that, with `F = p⁻¹(p e₀)` the fibre and `E²` the E² page
of `ξ`:

* the bottom row `E²_{n,0} = H_n(B; H_0 F)` is f.g. only if `H_n(B)` is (equivalently, `H_n(B)` is a
  quotient of `E²_{n,0}`, `H_0(F)` being free of positive rank);
* `E²_{s,t} ≅ H_s(B; H_t F)` is f.g. when `H_s(B)`, `H_{s-1}(B)` and `H_t(F)` are (universal
  coefficients: `H_s(B;H_tF) ≅ H_s(B)⊗H_tF ⊕ Tor(H_{s-1}(B),H_tF)`, and the `Tor` term is a
  submodule of `H_{s-1}(B) ⊗ H_tF` when `H_t(F)` is f.g.);
* `E²_{0,t} ≅ H_0(B; H_t F) ≅ H_t(F)` (`B` is path connected). -/
def SerreE2Statement : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E),
    Work.StemsB.IsSerreFibration p → Work.PiS.SimplyConn B (p e₀) →
    ∃ ξ : Filtration (Work.Cohomology.singularChains ℤ (TopCat.of E)),
      (∀ n : ℕ, Module.Finite ℤ (E2 ξ n 0) → Module.Finite ℤ (Work.PiS.HZ B n)) ∧
      (∀ s t : ℕ, Module.Finite ℤ (Work.PiS.HZ B s) →
        Module.Finite ℤ (Work.PiS.HZ B (s - 1)) →
        Module.Finite ℤ (Work.PiS.HZ (Work.StemsB.fibre p (p e₀)) t) →
        Module.Finite ℤ (E2 ξ s t)) ∧
      (∀ t : ℕ, Module.Finite ℤ (Work.PiS.HZ (Work.StemsB.fibre p (p e₀)) t) ↔
        Module.Finite ℤ (E2 ξ 0 t))


/-- **The first page of the Serre spectral sequence.**  For a Serre fibration `p : E → B` over a
simply connected base and the Serre filtration `ξ` of `C_*(E)` (whose `s`-th term is the chain
complex of the preimage of the `(s+1)`-skeleton of `Sing B`), the E¹ row complex `E1Complex ξ t`
(with terms `E¹_{s,t} = H_{s+t}(F_s/F_{s-1})` and differential `d¹`) is isomorphic, as a chain
complex, to the **normalized** singular chains of the base tensored with the homology of the fibre,
`N_*(B) ⊗ H_t(F)` (`F = p⁻¹(p e₀)`).  This is proved in `Submission/Work/SSS/serreE1.lean`. -/
def SerreE1Statement : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E),
    Work.StemsB.IsSerreFibration p → Work.PiS.SimplyConn B (p e₀) →
    ∀ (ξ : Filtration (Work.Cohomology.singularChains ℤ (TopCat.of E))),
      ξ.F = natShift ⋙
        Work.StemsB.serreChainFiltration (TopCat.toSSet.map (TopCat.ofHom p)) ℤ →
    ∀ t : ℕ,
      Nonempty (E1Complex ξ t ≅
        tensorComplex
          ((TopCat.toSSet.obj (TopCat.of B)).normalizedChainComplex (ModuleCat.of ℤ ℤ))
          ((Work.Cohomology.singularChains ℤ
            (TopCat.of (Work.StemsB.fibre p (p e₀)))).homology t))

end

end Work.SSS
