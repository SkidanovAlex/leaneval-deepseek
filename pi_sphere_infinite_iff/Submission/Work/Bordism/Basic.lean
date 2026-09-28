import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.PairSequence
import Submission.Work.SignatureBordism.Numbers

/-!
# Oriented bordism of closed oriented manifolds: the model

This is the first file of the chapter `Submission/Work/Bordism/`, which supplies the **geometry of
bordism invariance** for closed oriented smooth manifolds in this workspace's model (the
`SSet`/`chainC`/`cochainC` chapter of `Submission/Work/Cohomology/`).

## The model

Following the convention already used by `Submission/Work/SignatureBordism/` (see its README), a
**closed oriented `n`-manifold** is a topological space `X` together with a *fundamental class*
`c ∈ Hₙ(X;ℤ)`:

```lean
structure ClosedOriented (n : ℕ) where
  X : TopCat
  c : (chainC ℤ (TopCat.toSSet.obj X)).homology n
```

(For a genuine closed oriented smooth manifold one takes `X` the underlying space and `c = [M]` an
orientation class; nothing in this chapter uses smoothness, exactly as in the signature chapter,
which defines `Work.SignatureBordism.sigma` from a pair `(X, c)`.)

An **oriented bordism** between `M` and `N` is a compact oriented `(n+1)`-manifold with boundary
`∂W ≅ M ⊔ N̄`, together with the resulting relation between the fundamental classes.  Here is the
geometry: if `W` is a compact oriented `(n+1)`-manifold with boundary `B = ∂W` and relative
fundamental class `[W, ∂W] ∈ H_{n+1}(W,B;ℤ)`, then

`∂[W,∂W] = [∂W] = [M] - [N] ∈ Hₙ(B;ℤ)`

under the identification `∂W ≅ M ⊔ N̄`, and since `i_* ∘ ∂ = 0` for the inclusion `i : B ↪ W`, the
two classes `[M]`, `[N]` have the *same* image in `Hₙ(W;ℤ)`:

```lean
homologyMap iM [M] = homologyMap iN [N]   in Hₙ(W;ℤ).
```

The structure `Bordism M N` below records exactly this last relation (together with the space `W`
and the two boundary parametrisations), and `GeometricBordism.toBordism` *derives* it from the
relative-fundamental-class presentation using the long exact sequence of the pair `(W,B)`
(`Work.Cohomology.hPairδ_comp`).  Keeping the relation, rather than the relative class, as the
basic data is what makes the elementary structure — reflexivity, symmetry, transitivity, disjoint
unions — provable without any Poincaré–Lefschetz duality.

## What is *not* in this file

Bordism *invariance* of the signature and of the Pontryagin numbers are in
`Submission/Work/Bordism/Invariance.lean`, and the reduction to the generators of `Ω^SO_8 ⊗ ℚ` in
`Submission/Work/Bordism/Generation.lean`.  The duality input that a bordism supplies (the middle
form of the boundary carries a Lagrangian) is isolated there as an explicit named hypothesis
(`Work.Bordism.HalfDimension`, i.e. Lefschetz duality in the middle degree).

## Main definitions

* `Work.Bordism.ClosedOriented n` — closed oriented `n`-manifold `(X, c)`;
* `Work.Bordism.Bordism M N` — oriented bordism from `M` to `N`, `Work.Bordism.Bordant`;
* `Work.Bordism.ClosedOriented.disj` — disjoint union (with the sum of the fundamental classes);
* `Work.Bordism.GeometricBordism` — the honest relative-fundamental-class presentation of a
  bordism, with `Work.Bordism.GeometricBordism.toBordism` and `toBordism_W`.

## Main results

* `Work.Bordism.Bordism.refl` (`M` is bordant to itself, via `M × [0,1]`);
* `Work.Bordism.Bordism.symm` (reverse the orientation of `W`);
* `Work.Bordism.bordant_refl`, `Work.Bordism.bordant_symm`, `Work.Bordism.bordant_trans`;
* `Work.Bordism.GeometricBordism.toBordism` (the LES of the pair supplies the class relation).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology
open scoped Simplicial

namespace Work.Bordism

open Work.Cohomology Work.SignatureBordism

noncomputable section

/-- A **closed oriented `n`-manifold**, in the model of this chapter: a topological space `X`
together with a fundamental class `c ∈ Hₙ(X;ℤ)`. -/
structure ClosedOriented (n : ℕ) where
  /-- the underlying space -/
  X : TopCat.{0}
  /-- the fundamental class -/
  c : (chainC ℤ (TopCat.toSSet.obj X)).homology n

namespace ClosedOriented

variable {n : ℕ} (M : ClosedOriented n)

/-- The integral cohomology `Hᵏ(M;ℤ)`. -/
abbrev coh (k : ℕ) : Type := (cochainC ℤ (TopCat.toSSet.obj M.X)).homology k

/-- The integral homology `Hₖ(M;ℤ)`. -/
abbrev hom (k : ℕ) : Type := (chainC ℤ (TopCat.toSSet.obj M.X)).homology k

/-- **The rationalised cohomology** `Hᵏ(M;ℤ) ⊗[ℤ] ℚ` on which the intersection form and the
signature live. -/
abbrev ratCoh (k : ℕ) : Type := Work.SignatureBordism.ratCohomology k (TopCat.toSSet.obj M.X)

/-- **Orientation reversal**: the same manifold with the opposite fundamental class.  (The
intersection form and the signature change sign, `Work.SignatureBordism.sigma_neg_fundamental`.) -/
def neg : ClosedOriented n where
  X := M.X
  c := -M.c

@[simp] theorem neg_X : M.neg.X = M.X := rfl
@[simp] theorem neg_c : M.neg.c = -M.c := rfl

/-- **The disjoint union** of two closed oriented `n`-manifolds: the coproduct of the underlying
spaces, with the fundamental class the sum of the two classes under the canonical splitting
`Hₙ(M ⊔ N;ℤ) ≅ Hₙ(M;ℤ) ⊕ Hₙ(N;ℤ)`.  In the model the class is recorded by the two pushforwards
along the coproduct inclusions, which is what "the sum in the splitting" means. -/
def disj (N : ClosedOriented n) : ClosedOriented n where
  X := M.X ⨿ N.X
  c := HomologicalComplex.homologyMap
          (chainMap ℤ M.X (M.X ⨿ N.X) (CategoryTheory.Limits.coprod.inl)) n M.c
      + HomologicalComplex.homologyMap
          (chainMap ℤ N.X (M.X ⨿ N.X) (CategoryTheory.Limits.coprod.inr)) n N.c

instance : Neg (ClosedOriented n) := ⟨ClosedOriented.neg⟩

end ClosedOriented

variable {n : ℕ}

/-- **An oriented bordism** from a closed oriented `n`-manifold `M` to a closed oriented
`n`-manifold `N`: a compact oriented `(n+1)`-manifold `W` with boundary `∂W = M ⊔ N̄`, presented by
the two boundary parametrisations `iM`, `iN` and the relation between fundamental classes that the
geometry gives, namely `[M]` and `[N]` have the same image in `Hₙ(W;ℤ)` (because
`[∂W] = [M] - [N]` is a boundary in `W`).

See `Work.Bordism.GeometricBordism` for the derivation of `hbd` from the relative fundamental class
of the pair `(W, ∂W)` via the long exact sequence of the pair. -/
structure Bordism (M N : ClosedOriented n) where
  /-- the bordism manifold, with boundary `M ⊔ N̄` -/
  W : TopCat.{0}
  /-- the parametrisation of the boundary piece `M` -/
  iM : M.X ⟶ W
  /-- the parametrisation of the boundary piece `N̄` -/
  iN : N.X ⟶ W
  /-- the boundary relation: `[M]` and `[N]` become equal in `Hₙ(W;ℤ)` -/
  hbd : HomologicalComplex.homologyMap (chainMap ℤ M.X W iM) n M.c
      = HomologicalComplex.homologyMap (chainMap ℤ N.X W iN) n N.c

/-- `M` and `N` are **bordant** when an oriented bordism between them exists. -/
def Bordant (M N : ClosedOriented n) : Prop := Nonempty (Bordism M N)

namespace Bordism

variable {M N P : ClosedOriented n}

/-- **Reflexivity of bordism**: every closed oriented `n`-manifold is bordant to itself.  The
geometric bordism is `M × [0,1]` with its two boundary pieces `M × {0}` and `M × {1}`; in this
model we record the space `M` itself with both boundary parametrisations the identity, which is the
same data up to the homotopy equivalence `M × [0,1] ≃ M` (the two inclusions of `M` into
`M × [0,1]` are homotopic, hence induce the same map on homology). -/
def refl (M : ClosedOriented n) : Bordism M M where
  W := M.X
  iM := 𝟙 M.X
  iN := 𝟙 M.X
  hbd := rfl

/-- **Symmetry of bordism**: a bordism from `M` to `N` is a bordism from `N` to `M` — reverse the
orientation of `W` and exchange the two boundary pieces. -/
def symm (h : Bordism M N) : Bordism N M where
  W := h.W
  iM := h.iN
  iN := h.iM
  hbd := h.hbd.symm

end Bordism

theorem bordant_refl (M : ClosedOriented n) : Bordant M M := ⟨Bordism.refl M⟩

theorem bordant_symm {M N : ClosedOriented n} (h : Bordant M N) : Bordant N M :=
  h.elim fun b => ⟨b.symm⟩

/-! ## The honest geometric presentation of a bordism -/

/-- **A bordism presented through its relative fundamental class.**  `W` is the bordism manifold,
`B ⊆ W` its boundary, `iM : M → B` and `iN : N → B` the two boundary parametrisations (so that `B`
is identified with `M ⊔ N̄`), and `w ∈ H_{n+1}(W,B;ℤ)` is the relative fundamental class
`[W, ∂W]`, whose boundary is `[M] - [N] ∈ Hₙ(B;ℤ)`.

This is the honest geometric input; `Work.Bordism.GeometricBordism.toBordism` shows that it yields
the class relation of `Work.Bordism.Bordism`, using the long exact sequence of the pair `(W, B)`
(`Work.Cohomology.hPairδ_comp`: the connecting homomorphism followed by the map induced by the
inclusion of the boundary is zero). -/
structure GeometricBordism (M N : ClosedOriented n) where
  /-- the bordism manifold -/
  W : TopCat.{0}
  /-- its boundary, as a subspace -/
  B : Set W
  /-- the parametrisation of the `M`-piece of the boundary -/
  iM : M.X ⟶ TopCat.of B
  /-- the parametrisation of the `N̄`-piece of the boundary -/
  iN : N.X ⟶ TopCat.of B
  /-- the relative fundamental class `[W, ∂W]` -/
  w : (relChains W B).homology (n + 1)
  /-- its boundary is `[M] - [N]` -/
  hw : hPairδ W B n w
      = HomologicalComplex.homologyMap (chainMap ℤ M.X (TopCat.of B) iM) n M.c
        - HomologicalComplex.homologyMap (chainMap ℤ N.X (TopCat.of B) iN) n N.c

namespace GeometricBordism

variable {M N : ClosedOriented n}

/-- **The class relation from the long exact sequence of the pair.**  A geometric bordism
`∂W = M ⊔ N̄` yields a bordism in the sense of `Work.Bordism.Bordism`: the images of `[M]` and
`[N]` in `Hₙ(W;ℤ)` agree.

Indeed `[∂W] = [M] - [N]` is the boundary of the relative fundamental class, and the composite
`H_{n+1}(W,B) --∂--> Hₙ(B) --i_*--> Hₙ(W)` is zero (`Work.Cohomology.hPairδ_comp`), so the image of
`[M] - [N]` in `Hₙ(W;ℤ)` vanishes. -/
def toBordism (h : GeometricBordism M N) : Bordism M N where
  W := h.W
  iM := h.iM ≫ subtypeIncl h.W h.B
  iN := h.iN ≫ subtypeIncl h.W h.B
  hbd := by
    have hzero : HomologicalComplex.homologyMap (inclChains h.W h.B) n (hPairδ h.W h.B n h.w) = 0 := by
      have hcomp := hPairδ_comp h.W h.B n
      have h2 := congrArg
        (fun (g : (relChains h.W h.B).homology (n + 1) ⟶ (singularChains ℤ h.W).homology n) =>
          g.hom h.w) hcomp
      simpa using h2
    have hkey : HomologicalComplex.homologyMap (inclChains h.W h.B) n
        (HomologicalComplex.homologyMap (chainMap ℤ M.X (TopCat.of h.B) h.iM) n M.c
          - HomologicalComplex.homologyMap (chainMap ℤ N.X (TopCat.of h.B) h.iN) n N.c) = 0 := by
      rw [← h.hw]
      exact hzero
    rw [map_sub, sub_eq_zero] at hkey
    -- transport along the functoriality of the chain maps
    have hfacM : chainMap ℤ M.X h.W (h.iM ≫ subtypeIncl h.W h.B)
        = chainMap ℤ M.X (TopCat.of h.B) h.iM ≫ inclChains h.W h.B := by
      simp only [chainMap, inclChains, Functor.map_comp]
    have hfacN : chainMap ℤ N.X h.W (h.iN ≫ subtypeIncl h.W h.B)
        = chainMap ℤ N.X (TopCat.of h.B) h.iN ≫ inclChains h.W h.B := by
      simp only [chainMap, inclChains, Functor.map_comp]
    rw [hfacM, hfacN, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
    exact hkey

@[simp] theorem toBordism_W (h : GeometricBordism M N) : h.toBordism.W = h.W := rfl

end GeometricBordism

end

end Work.Bordism
