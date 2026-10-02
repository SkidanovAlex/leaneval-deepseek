import Mathlib
import Submission.Work.ThomBordism.boundaryAssembly
import Submission.Work.ThomBordism.doubleDefs
import Submission.Work.ThomBordism.goodUnivCharted
import Submission.Work.Bordism.LesImage
import Submission.Work.Cohomology.PairSequence
import Submission.Work.ThomBordism.bdryInterfaces
import Submission.Work.ThomBordism.lefschetzDualityBdry
import Submission.Work.ThomBordism.boundaryOfLefschetz

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The crux of `Work.ThomBordism.BoundarySigma`: `K = Kᗮ` for the pair `(W, ∂W)`

`Work.ThomBordism.BoundaryMaximalIsotropic` is the **maximality half of middle-dimensional
(Lefschetz) duality** for the pair `(W, ∂W)` of a `NullBordismFamily`:

> for every `W` and every `y ∈ H⁴(∂W;ℚ)` orthogonal (for the middle intersection form
> `B = bdryFormBilin W` of the boundary) to `K = bdryK W = im(H⁴(W;ℚ) → H⁴(∂W;ℚ))`, one has `y ∈ K`.

The isotropy half `K ⊆ Kᗮ` is *proved* (`Work.ThomBordism.bdryK_isotropic`); the maximality half is
the content of Lefschetz duality and is what this file owes.

## State of the proof (read this before continuing)

Writing `V = H⁴(∂W;ℚ)`, `K = bdryK W`, `B = bdryFormBilin W`, `w = W.w`,
`L = im(∂ : H₅(W,∂W;ℚ) → H₄(∂W;ℚ)) = ker i_*` and `δ` for the connecting map of the pair, the
following are equivalent and all are the same theorem (see
`Submission/Work/ThomBordism/HALFDIM_EQUIVALENCES.md` and `HALFDIM_PLAN.md`):

* the crux `Kᗮ ⊆ K` (with `bdryK_isotropic`: `K = Kᗮ`);
* `K = ker δ` *maximal*, i.e. `L ⊆ Lᗮ` in `H₄(∂W;ℚ)`;
* `Φ : H⁵(W,∂W;ℚ) → H₄(W;ℚ)`, `z ↦ z ⌢ w`, is injective on `im δ`;
* `dim K = dim L` (equivalently `2 dim K = dim H⁴(∂W;ℚ)`).

The chain-level, *elementary* identities available in the workspace (Leibniz rule for the cap
product `Work.Cohomology.cap_d`, naturality of the Kronecker pairing
`Work.Cohomology.kronH_natural`, the cap/cup adjunction `capPair_cup`,
`relCapH_kronH_cup`, and the exactness `Work.Bordism.range_restr_eq_ker_pairDelta`) give

* `i_*(y ⌢ ∂w) = ± (δ y) ⌢ w` (capping with the relative fundamental class commutes with the
  connecting maps), hence the **transgression identity** `B (r u) y = ± ⟨u, (δ y) ⌢ w⟩`;
* `Φ(δ y) = ± i_*(y ⌢ ∂w)`, hence `im(∂ Ψ) = Φ_M(K)`, `dim K ≤ dim L`, and
  `K = Φ_M^{-1}(L)`.

So the crux is *equivalent* to the injectivity of the **relative cap product with `w`**, i.e.
**Poincaré–Lefschetz duality for the pair `(W, ∂W)`** — the workspace's named input
`Work.Surgery.LefschetzDuality` (`Submission/Work/Surgery/RelativeDisc.lean`), proved there only for
the model pairs (the disc pair and the disc-bundle pair of a `4`-handle).  It is *not* implied by
anything else in the workspace, and it is *not* implied by the absolute Poincaré duality
`Work.Cohomology.pd_middle_even` (that is the duality of a *closed* manifold, while `W` has a
boundary; e.g. the compactly-supported duality of the interior does not compute `H⁵(W,∂W)`).

## The decomposition used (both parts are now proved)

The vocabulary lives in `Submission/Work/ThomBordism/bdryInterfaces.lean`:
`LefschetzDualityBdry W` (the relative cap product with `W.w` is bijective in every bidegree), the
rationalisations `relH`, `homH`, and the rationalised connecting map `deltaRat`.  With it,

* **`Work.ThomBordism.lefschetzDualityBdry (W) : LefschetzDualityBdry W`**
  (`Submission/Work/ThomBordism/lefschetzDualityBdry.lean`) — **the geometric theorem**: middle
  Lefschetz duality for the pair `(W, ∂W)`, i.e. Hatcher's Theorem 3.43.  It is proved there by the
  classical route (compactly supported duality of the interior, realised in this workspace through
  `Work.Cohomology.Good` on the *double* of `W`, together with the two collar-free comparisons
  `int W → W` is a homology equivalence and every relative class lifts off the boundary).  The
  chapter behind it is `Submission/Work/ThomBordism/RelDuality/`; the four ingredients of the
  assembly are `RelDuality.interiorHomology`, `RelDuality.relClass_lift`, `RelDuality.goodOfOpen`
  and `RelDuality.doubleFundClass`, combined by `RelDuality.lefschetzDualityBdry_of_pieces`.
* **`Work.ThomBordism.boundaryOfLefschetz`**
  (`Submission/Work/ThomBordism/boundaryOfLefschetz.lean`) — **the formal reduction**:
  `(∀ W, LefschetzDualityBdry W) → BoundaryMaximalIsotropic`, by the transgression identity, the
  exactness of the pair sequence `K = ker δ`, and the ℚ-detection of integral middle homology of
  `W` (finitely generated, `Work.ThomBordism.homologyFiniteOfNullBordism`).

Both are proof-complete and `#print axioms`-clean (`propext`, `Classical.choice`, `Quot.sound`); the
target below is their composition.

## Import island (watch out)

`Work.Surgery.LefschetzDuality` cannot be imported from this module: the workspace still has two
copies of `Work.Cohomology.prodSphereAux`
(`Submission/Work/Cohomology/prodSphereAux.lean` and
`Submission/Work/Cohomology/CompatTrans/prodSphereAux.lean`) and importing
`Submission.Work.Surgery.RelativeDisc` together with `Submission.Work.ThomBordism.Interface` fails
with "environment already contains `Work.Cohomology.homologyBiprodIso`".  Hence the local copy
`LefschetzDualityBdry` in `bdryInterfaces.lean`.
-/

namespace Work.ThomBordism

/-- **The crux of `Work.ThomBordism.BoundarySigma`**: the image of the restriction
`H⁴(W;ℚ) → H⁴(∂W;ℚ)` is a Lagrangian of the middle intersection form of `∂W` (maximal isotropy).

Proved as the composition of middle Lefschetz duality for the pair `(W, ∂W)`
(`Work.ThomBordism.lefschetzDualityBdry`) with its formal reduction to the crux
(`Work.ThomBordism.boundaryOfLefschetz`). -/
theorem boundaryMaximalIsotropic : Work.ThomBordism.BoundaryMaximalIsotropic :=
  boundaryOfLefschetz (fun ι _ F W => lefschetzDualityBdry W)

end Work.ThomBordism
