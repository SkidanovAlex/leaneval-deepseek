-- PORTED COPY (neutral island) of `Submission/Work/Serre/ratShuffle.lean`.
-- The only changes are: the imports of ratShuffle-island modules are redirected to the
-- copies in `Submission/Work/Serre/Neu/`, and the abbrev `singSSet` is renamed to
-- `singSSetN` (same body) so that this module can coexist with `Work.Serre.E0Defs`,
-- which declares the same name.  Declarations and proofs are unchanged.
import Mathlib
import Submission.Work.Serre.relEZ_main
import Submission.Work.Serre.ezShuffleEval
import Submission.Work.Serre.relKron_exists

/-!
# The rational shuffle chain on the product pair

Vocabulary for the assembly of `Work.Serre.modelThomRatPair`:

* `Work.Serre.singSSetN X` — the singular simplicial set of a space;
* `Work.Serre.tpCWQ W P Q` — the Koszul tensor product of the integral singular chains of `W` with
  the integral relative chains of the pair `(P,Q)`;
* `Work.Serre.relBBA W P Q` (integral) and `Work.Serre.relBBA_rat W P Q` (rational) — the relative
  chain complexes of the product pair `(W × P, W × Q)`;
* `Work.Serre.shufRat W P Q m q` — the Eilenberg–Zilber shuffle of a rational `m`-chain of `W` and a
  rational `q`-chain of `P`, as a chain of the product `W × P` (the EZ shuffle transported along
  `Sing (W × P) ≅ Sing W ⊗ Sing P`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct MonoidalCategory

namespace Work.Serre

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The singular simplicial set of a space. -/
abbrev singSSetN (X : Type) [TopologicalSpace X] : SSet := TopCat.toSSet.obj (TopCat.of X)

/-- The Koszul tensor product of the integral singular chains of `W` with the integral relative
chains of the pair `(P,Q)`. -/
abbrev tpCWQ (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P] (Q : Set P) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  Work.Kunneth.tpC (Work.Cohomology.singularChains ℤ (TopCat.of W))
    (Work.Cohomology.relChains (TopCat.of P) Q)

/-- The integral relative chain complex of the product pair `(W × P, W × Q)`. -/
abbrev relBBA (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P] (Q : Set P) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  Work.Cohomology.relChains (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}

/-- The rational relative chain complex of the product pair `(W × P, W × Q)`. -/
abbrev relBBA_rat (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P] (Q : Set P) :
    ChainComplex (ModuleCat ℚ) ℕ :=
  Work.StemsB.relChainsR ℚ (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}

/-- The relative chain complex of the pair `(P,Q)` over `ℚ`. -/
abbrev relPA_rat (P : Type) [TopologicalSpace P] (Q : Set P) : ChainComplex (ModuleCat ℚ) ℕ :=
  Work.StemsB.relChainsR ℚ (TopCat.of P) Q

/-- The transport `C_*(Sing W ⊗ Sing P) ⟶ C_*(Sing (W × P))` along the monoidal isomorphism. -/
noncomputable def prodChainTransport (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P]
    (R : Type) [CommRing R] :
    ((singSSetN W ⊗ singSSetN P).chainComplex (ModuleCat.of R R)) ⟶
      (Work.Cohomology.singularChains R (TopCat.of (W × P))) :=
  SSet.chainComplexMap (Work.Kunneth.singProdIso (TopCat.of W) (TopCat.of P)).inv
    (ModuleCat.of R R)

/-- The Eilenberg–Zilber shuffle of two rational chains, as a chain of the product space. -/
noncomputable def shufRat (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P]
    (m q : ℕ) :
    (Work.Cohomology.singularChains ℚ (TopCat.of W)).X m →ₗ[ℚ]
      (Work.Cohomology.singularChains ℚ (TopCat.of P)).X q →ₗ[ℚ]
        (Work.Cohomology.singularChains ℚ (TopCat.of (W × P))).X (m + q) :=
  LinearMap.mk₂ ℚ
    (fun u v => ((prodChainTransport W P ℚ).f (m + q)).hom
      ((ezBilR ℚ m q (singSSetN W) (singSSetN P)).hom u v))
    (fun a b c => by rw [map_add, LinearMap.add_apply, map_add])
    (fun a b c => by rw [map_smul, LinearMap.smul_apply, map_smul])
    (fun a b c => by rw [map_add, map_add])
    (fun a b c => by rw [map_smul, map_smul])


/-- The EZ shuffle of an integral chain `u` of `W` and an integral chain `vt` of `P`, as a chain of
the product space `W × P` (via the Eilenberg–Zilber shuffle map `Work.Kunneth.ezMapT`). -/
noncomputable def ezShufChain (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P]
    (m q : ℕ) (u : (Work.Cohomology.singularChains ℤ (TopCat.of W)).X m)
    (vt : (Work.Cohomology.singularChains ℤ (TopCat.of P)).X q) :
    (Work.Cohomology.singularChains ℤ (TopCat.of (W × P))).X (m + q) :=
  ((Work.Kunneth.ezMapT (TopCat.of W) (TopCat.of P)).f (m + q))
    ((Work.Kunneth.tpLof (Work.Kunneth.sChain (singSSetN W)) (Work.Kunneth.sChain (singSSetN P))
      (m + q) ⟨(m, q), rfl⟩) (TensorProduct.tmul ℤ u vt))

/-- The Koszul tensor product of a cycle of `W` and a cycle of the relative chains of `(P,Q)`, as a
cycle of `Work.Serre.tpCWQ W P Q`. -/
noncomputable def crossCycTensElem (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P]
    (Q : Set P) (m q : ℕ)
    (u : ↥((Work.Cohomology.singularChains ℤ (TopCat.of W)).cycles m))
    (v : ↥((Work.Cohomology.relChains (TopCat.of P) Q).cycles q)) :
    ↥((tpCWQ W P Q).cycles (m + q)) :=
  Work.Kunneth.crossCycTens (Work.Cohomology.singularChains ℤ (TopCat.of W))
    (Work.Cohomology.relChains (TopCat.of P) Q) (m + q) m q rfl
    (TensorProduct.tmul ℤ u v)

end

end Work.Serre
