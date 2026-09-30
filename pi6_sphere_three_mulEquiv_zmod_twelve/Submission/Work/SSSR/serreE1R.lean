import Mathlib
import Submission.Work.SSSR.serreE1
import Submission.Work.SSSR.serreFiltrationR
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The E¹ page of the Serre spectral sequence over an arbitrary coefficient ring (SSSR)

This is the **coefficient-ring-generic** form of `Work.SSS.serreE1`: for *every* commutative ring
`R`, a Serre fibration `p : E → B` over a simply connected base, and the Serre filtration `ξ` of the
singular chain complex `C_*(E; R)` (any filtration whose underlying functor is the Serre
filtration, as witnessed by the hypothesis `hξ`), the E¹ page of the spectral sequence of `ξ` — the
row complex `E1Complex R ξ t`, with terms `E¹_{s,t} = H_{s+t}(F_s/F_{s-1}; R)` and differential `d¹`
— is isomorphic, as a chain complex of `R`-modules, to the normalized singular chains of the base
tensored with the homology of the fibre:
`E¹_{*,t} ≅ N_*(B; R) ⊗_R H_t(F; R)`, where `F = p⁻¹(p e₀)`.

The whole proof is the chain-level proof of the integral statement, re-run over `R`: the graded
pieces are the pieces `H_{s+t}(T_σ, ∂T_σ; R)` of the Eilenberg–Zilber decomposition, the fibre
computation `H_{s+t}(T_σ, ∂T_σ; R) ≅ H_t(F_{σ(v₀)}; R)` is the prism contraction (a chain
contraction coming from the homotopy lifting property, hence valid over any coefficients), and the
identification of the fibres `H_t(F_b; R) ≅ H_t(F; R)` uses only that the base is simply connected.

## Naming conventions (deviations from the statement as dispatched)

The names below are the ones of this port; the mathematical content is exactly that of the
dispatched statement.

* the theorem is called `Work.SSSR.serreE1R` and takes the coefficient ring `R` *explicitly*, with
  hypotheses `[CommRing R] [Nontrivial R]` (the lead accepted `[Nontrivial R]`; the only consumer,
  area MSS, instantiates `R` at a field, which is nontrivial);
* `Work.StemsB.IsSerreFibration` of the global library is spelled here `Work.SSSR.StemsB.IsSerreFibration`
  (the port's copy of the definition, which is the one the ported E¹ proof is stated for), and
  `Work.PiS.SimplyConn` is spelled `Work.SSSR.PiS.SimplyConn`;
* the singular chains `Work.Cohomology.singularChains R` are spelled
  `Work.SSSR.Cohomology.singularChains R` (the port's copy, with the coefficient ring explicit);
* `Work.SSS.natShift` and `Work.StemsB.serreChainFiltration` are spelled `Work.SSSR.natShift` and
  `Work.SSSR.StemsB.serreChainFiltration`.
-/

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits
open scoped Topology

/-- **The first page of the Serre spectral sequence, over an arbitrary coefficient ring `R`.** -/
theorem serreE1R (R : Type) [CommRing R] [Nontrivial R]
    (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (hfib : Work.SSSR.StemsB.IsSerreFibration p) (hconn : Work.SSSR.PiS.SimplyConn B (p e₀))
    (ξ : Work.SSSR.Filtration R (Work.SSSR.Cohomology.singularChains R (TopCat.of E)))
    (hξ : ξ.F = Work.SSSR.natShift ⋙
      Work.SSSR.StemsB.serreChainFiltration (TopCat.toSSet.map (TopCat.ofHom p)) R) (t : ℕ) :
    Nonempty (Work.SSSR.E1Complex R ξ t ≅ Work.SSSR.tensorComplex R
      ((TopCat.toSSet.obj (TopCat.of B)).normalizedChainComplex (ModuleCat.of R R))
      ((Work.SSSR.Cohomology.singularChains R
        (TopCat.of (Work.SSSR.StemsB.fibre p (p e₀)))).homology t)) :=
  Work.SSSR.serreE1 E B p e₀ hfib hconn ξ hξ t

/-- The Serre filtration exists: `Work.SSSR.serreFiltrationR`, restated in the form in which it is
used by `serreE1R`. -/
theorem serreE1R_exists_filtration (R : Type) [CommRing R] [Nontrivial R]
    (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) :
    ∃ ξ : Work.SSSR.Filtration R (Work.SSSR.Cohomology.singularChains R (TopCat.of E)),
      ξ.F = Work.SSSR.natShift ⋙
        Work.SSSR.StemsB.serreChainFiltration (TopCat.toSSet.map (TopCat.ofHom p)) R :=
  Work.SSSR.serreFiltrationR R E B p

/-- **The E¹ theorem with the Serre filtration produced internally.**  For a Serre fibration over a
simply connected base, there *is* a filtration of `C_*(E; R)` (the Serre filtration) whose E¹ row
complex in fibre degree `t` is `N_*(B; R) ⊗_R H_t(F; R)`.  This is `serreE1R` composed with the
existence of the Serre filtration `serreFiltrationR`, in the form most convenient for a caller who
does not want to exhibit `ξ`. -/
theorem serreE1R_exists (R : Type) [CommRing R] [Nontrivial R]
    (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (hfib : Work.SSSR.StemsB.IsSerreFibration p) (hconn : Work.SSSR.PiS.SimplyConn B (p e₀))
    (t : ℕ) :
    ∃ ξ : Work.SSSR.Filtration R (Work.SSSR.Cohomology.singularChains R (TopCat.of E)),
      ξ.F = Work.SSSR.natShift ⋙
        Work.SSSR.StemsB.serreChainFiltration (TopCat.toSSet.map (TopCat.ofHom p)) R ∧
      Nonempty (Work.SSSR.E1Complex R ξ t ≅ Work.SSSR.tensorComplex R
        ((TopCat.toSSet.obj (TopCat.of B)).normalizedChainComplex (ModuleCat.of R R))
        ((Work.SSSR.Cohomology.singularChains R
          (TopCat.of (Work.SSSR.StemsB.fibre p (p e₀)))).homology t)) := by
  obtain ⟨ξ, hξ⟩ := Work.SSSR.serreFiltrationR R E B p
  exact ⟨ξ, hξ, Work.SSSR.serreE1R R E B p e₀ hfib hconn ξ hξ t⟩

end Work.SSSR
