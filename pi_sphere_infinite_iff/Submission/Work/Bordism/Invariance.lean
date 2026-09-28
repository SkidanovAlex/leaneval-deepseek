import Mathlib
import Submission.Work.Bordism.Middle
import Submission.Work.Bordism.signature_eq_zero_of_isotropic_half
import Submission.Work.SignatureBordism.signature_prod

/-!
# Bordism invariance of the signature and of the Pontryagin numbers

Let `W` be a bordism from `M` to `N` (`Submission/Work/Bordism/Basic.lean`), so `∂W = M ⊔ N̄` and
the two boundary parametrisations satisfy `(iM)_*[M] = (iN)_*[N]` in `Hₙ(W;ℤ)`.

## The signature

The middle form of the boundary is `Q_∂ = Q_M ⊥ (-Q_N)` (`Work.Bordism.boundaryForm`) and the
middle comparison map `Φ = (iM*, iN*) : Hᵏ(W;ℚ) → Hᵏ(∂W;ℚ)` has image `K`.  The first half of the
Lagrangian property — `K` totally isotropic — is proved in `Submission/Work/Bordism/Middle.lean`
from the boundary relation alone.  The second half is the dimension equality
`Work.Bordism.HalfDimension` ("half lives on each side", the middle-dimensional Lefschetz duality
`Hᵏ(∂W;ℚ)/K ≅ H^{k+1}(W,∂W;ℚ) ≅ H_k(W;ℚ)`).  Together with Poincaré duality on the two closed
pieces (`Work.Bordism.Nondegenerate (midForm M)` etc., triviality of the radical), they give
`signature Q_∂ = 0` (`Work.Bordism.signature_eq_zero_of_isotropic_half`), i.e.

`Work.Bordism.sigma_eq_of_bordant : σ(M) = σ(N)`.

Because `signature (Q_M ⊥ (-Q_N)) = σ(M) - σ(N)` (`signature_prod`, `signature_neg`), this is
bordism invariance of the signature in the standard form: **the signature is a bordism invariant**.

## The Pontryagin numbers

Here no duality is needed at all.  If the classes `p₁^M`, `p₂^M` and `p₁^N`, `p₂^N` are the
restrictions of classes `p₁^W`, `p₂^W` on the bordism (which is what a bordism *with Pontryagin
data* is), then

`⟨p₂^M, [M]⟩ = ⟨p₂^W, (iM)_*[M]⟩ = ⟨p₂^W, (iN)_*[N]⟩ = ⟨p₂^N, [N]⟩`

and similarly for `p₁²`, both by naturality of the Kronecker pairing and of the cup product
(`Work.Bordism.interForm_pullback`).  See `Work.Bordism.p₂Number_eq_of_bordant`,
`Work.Bordism.p₁SqNumber_eq_of_bordant`, packaged as `Work.Bordism.PontryaginBordism`.

## Main definitions

* `Work.Bordism.Nondegenerate.prod` — nondegeneracy is preserved by orthogonal sums;
* `Work.Bordism.PontryaginBordism M N` — a bordism together with compatible Pontryagin classes on
  the two ends.

## Main results

* `Work.Bordism.sigma_eq_of_bordant` — `σ(M) = σ(N)`;
* `Work.Bordism.p₂Number_eq_of_bordant`, `Work.Bordism.p₁SqNumber_eq_of_bordant`,
  `Work.Bordism.p₁Number_eq_of_bordant` — the Pontryagin numbers agree;
* `Work.Bordism.PontryaginBordism.p₁SqNumber_eq`, `Work.Bordism.PontryaginBordism.p₂Number_eq`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.dupNamespace false

open CategoryTheory AlgebraicTopology

namespace Work.Bordism

open Work.Cohomology Work.SignatureBordism

noncomputable section

/-! ## Nondegeneracy of an orthogonal sum -/

/-- **Nondegeneracy is preserved by orthogonal direct sums.**  (The radical of `Q₁ ⊥ Q₂` is the
product of the radicals.) -/
theorem Nondegenerate.prod {𝕜 V W : Type*} [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W] [Invertible (2 : 𝕜)] {Q₁ : QuadraticForm 𝕜 V}
    {Q₂ : QuadraticForm 𝕜 W} (h₁ : Nondegenerate Q₁) (h₂ : Nondegenerate Q₂) :
    Nondegenerate (Q₁.prod Q₂) := by
  intro x hx
  have hx1 : x.1 = 0 := by
    apply h₁
    intro y
    have h := hx (y, 0)
    rw [QuadraticMap.associated_prod] at h
    simpa only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, map_zero, add_zero] using h
  have hx2 : x.2 = 0 := by
    apply h₂
    intro y
    have h := hx (0, y)
    rw [QuadraticMap.associated_prod] at h
    simpa only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, map_zero, zero_add] using h
  exact Prod.ext hx1 hx2

/-- The associated bilinear form of `-Q` is `-` that of `Q` (`associated` is linear in `Q`). -/
theorem associated_neg {𝕜 V : Type*} [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [Invertible (2 : 𝕜)] (Q : QuadraticForm 𝕜 V) :
    QuadraticMap.associated (-Q) = -QuadraticMap.associated Q :=
  map_neg (QuadraticMap.associated (R := 𝕜) (M := V) (N := 𝕜)) Q

/-- Nondegeneracy is preserved by negation of the form. -/
theorem Nondegenerate.neg {𝕜 V : Type*} [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [Invertible (2 : 𝕜)] {Q : QuadraticForm 𝕜 V} (h : Nondegenerate Q) :
    Nondegenerate (-Q) := by
  intro x hx
  apply h x
  intro y
  have h' := hx y
  rw [associated_neg] at h'
  simpa using h'

/-! ## Bordism invariance of the signature -/

/-- **Bordism invariance of the signature.**  Let `M`, `N` be closed oriented `2k`-manifolds and
`h : Bordism M N` a bordism between them, so that the boundary of `W` is `M ⊔ N̄` and
`(iM)_*[M] = (iN)_*[N]` in `H_{2k}(W;ℤ)`.

Assume

* (`hndM`, `hndN`) the middle intersection forms of `M` and `N` are nondegenerate — this is Poincaré
  duality for a closed oriented manifold, a named hypothesis because no general Poincaré duality
  exists in this library;
* (`hdim`) `Work.Bordism.HalfDimension k h` — the middle-dimensional Lefschetz duality "half lives
  on each side": the image of `Hᵏ(W;ℚ) → Hᵏ(∂W;ℚ)` has half the dimension of `Hᵏ(∂W;ℚ)`.

Then **`σ(M) = σ(N)`**.

Proof: the image `K` of the middle comparison map is totally isotropic
(`Work.Bordism.boundaryForm_middleMap_eq_zero`, which uses only the boundary relation), `hdim` says
it has half dimension, and `hndM`, `hndN` make the middle form of the boundary nondegenerate; hence
by `Work.Bordism.signature_eq_zero_of_isotropic_half` the signature of `Q_M ⊥ (-Q_N)` vanishes, and
that signature is `σ(M) - σ(N)`. -/
theorem sigma_eq_of_bordant {k : ℕ} {M N : ClosedOriented (k + k)} (h : Bordism M N)
    [FiniteDimensional ℚ (ratCohomology k (TopCat.toSSet.obj M.X))]
    [FiniteDimensional ℚ (ratCohomology k (TopCat.toSSet.obj N.X))]
    (hndM : Nondegenerate (midForm M)) (hndN : Nondegenerate (midForm N))
    (hdim : HalfDimension k h) :
    sigma k (TopCat.toSSet.obj M.X) M.c = sigma k (TopCat.toSSet.obj N.X) N.c := by
  have hboundary : signature (boundaryForm M N) = 0 := by
    refine signature_eq_zero_of_isotropic_half (boundaryForm M N)
      (LinearMap.range (middleMap k h)) ?_ ?_ ?_
    · intro x hx
      exact boundaryForm_eq_zero_of_mem_range k h x hx
    · intro x hx
      exact Nondegenerate.prod hndM hndN.neg x hx
    · exact hdim
  have hsig : signature (midForm M) - signature (midForm N) = 0 := by
    have h' := hboundary
    rw [boundaryForm, signature_prod, signature_neg] at h'
    linarith
  rw [sigma_eq_signature_midForm M, sigma_eq_signature_midForm N]
  linarith

/-! ## Bordism invariance of the Pontryagin numbers -/

/-- **A bordism with Pontryagin data**: a bordism between closed oriented `8`-manifolds together
with classes `p₁^W ∈ H⁴(W;ℤ)`, `p₂^W ∈ H⁸(W;ℤ)` on the bordism whose restrictions to the two
boundary pieces are the given classes `p₁^M, p₂^M` and `p₁^N, p₂^N`.

This is the honest geometric input for the Pontryagin numbers: the Pontryagin classes of the
tangent bundles of the pieces are the restrictions of a class on the bordism (e.g. because the
tangent bundle of `W` restricts to the tangent bundles of the boundary pieces, up to the
stabilisation by a trivial line bundle).  No duality is needed for the invariance: it follows from
naturality of the Kronecker pairing and of the cup product alone. -/
structure PontryaginBordism (M N : ClosedOriented 8) extends Bordism M N where
  /-- the `p₁`-class on the bordism -/
  p₁W : (cochainC ℤ (TopCat.toSSet.obj W)).homology 4
  /-- the `p₂`-class on the bordism -/
  p₂W : (cochainC ℤ (TopCat.toSSet.obj W)).homology 8
  /-- the `p₁`-class on `M` -/
  p₁M : (cochainC ℤ (TopCat.toSSet.obj M.X)).homology 4
  /-- the `p₂`-class on `M` -/
  p₂M : (cochainC ℤ (TopCat.toSSet.obj M.X)).homology 8
  /-- the `p₁`-class on `N` -/
  p₁N : (cochainC ℤ (TopCat.toSSet.obj N.X)).homology 4
  /-- the `p₂`-class on `N` -/
  p₂N : (cochainC ℤ (TopCat.toSSet.obj N.X)).homology 8
  /-- `p₁M` is the restriction of `p₁W` -/
  hp₁M : (singularCohomologyMap ℤ M.X W iM 4).hom p₁W = p₁M
  /-- `p₁N` is the restriction of `p₁W` -/
  hp₁N : (singularCohomologyMap ℤ N.X W iN 4).hom p₁W = p₁N
  /-- `p₂M` is the restriction of `p₂W` -/
  hp₂M : (singularCohomologyMap ℤ M.X W iM 8).hom p₂W = p₂M
  /-- `p₂N` is the restriction of `p₂W` -/
  hp₂N : (singularCohomologyMap ℤ N.X W iN 8).hom p₂W = p₂N

/-- **Bordism invariance of the `p₂`-number.**  If `p₂^M`, `p₂^N` are the restrictions of a class
`p₂^W ∈ H⁸(W;ℤ)` on the bordism to the two boundary pieces, then
`⟨p₂^M, [M]⟩ = ⟨p₂^N, [N]⟩`.

This is naturality of the Kronecker pairing (`Work.Cohomology.kronH_natural`) together with the
boundary relation `(iM)_*[M] = (iN)_*[N]`. -/
theorem p₂Number_eq_of_bordant {M N : ClosedOriented 8} (h : Bordism M N)
    (p₂W : (cochainC ℤ (TopCat.toSSet.obj h.W)).homology 8)
    (p₂M : (cochainC ℤ (TopCat.toSSet.obj M.X)).homology 8)
    (p₂N : (cochainC ℤ (TopCat.toSSet.obj N.X)).homology 8)
    (hM : (singularCohomologyMap ℤ M.X h.W h.iM 8).hom p₂W = p₂M)
    (hN : (singularCohomologyMap ℤ N.X h.W h.iN 8).hom p₂W = p₂N) :
    p₂Number (TopCat.toSSet.obj M.X) M.c p₂M
      = p₂Number (TopCat.toSSet.obj N.X) N.c p₂N := by
  rw [p₂Number_apply, p₂Number_apply, ← hM, ← hN]
  rw [← kronH_natural M.X h.W h.iM 8 p₂W M.c, h.hbd,
    kronH_natural N.X h.W h.iN 8 p₂W N.c]

/-- **Bordism invariance of the `p₁²`-number.**  If `p₁^M`, `p₁^N` are the restrictions of a class
`p₁^W ∈ H⁴(W;ℤ)` on the bordism to the two boundary pieces, then
`⟨p₁^M ⌣ p₁^M, [M]⟩ = ⟨p₁^N ⌣ p₁^N, [N]⟩`.

This is `Work.Bordism.interForm_pullback` (naturality of the intersection form: naturality of the
cup product together with naturality of the Kronecker pairing) and the boundary relation. -/
theorem p₁SqNumber_eq_of_bordant {M N : ClosedOriented 8} (h : Bordism M N)
    (p₁W : (cochainC ℤ (TopCat.toSSet.obj h.W)).homology 4)
    (p₁M : (cochainC ℤ (TopCat.toSSet.obj M.X)).homology 4)
    (p₁N : (cochainC ℤ (TopCat.toSSet.obj N.X)).homology 4)
    (hM : (singularCohomologyMap ℤ M.X h.W h.iM 4).hom p₁W = p₁M)
    (hN : (singularCohomologyMap ℤ N.X h.W h.iN 4).hom p₁W = p₁N) :
    p₁SqNumber (TopCat.toSSet.obj M.X) M.c p₁M
      = p₁SqNumber (TopCat.toSSet.obj N.X) N.c p₁N := by
  rw [p₁SqNumber_apply, p₁SqNumber_apply, ← hM, ← hN]
  rw [interForm_pullback h.iM 4 M.c p₁W p₁W, h.hbd,
    ← interForm_pullback h.iN 4 N.c p₁W p₁W]

/-- **Bordism invariance of the `p₁`-number** (dimension `4`, for completeness): if `p₁^M`, `p₁^N`
are the restrictions of a class on the bordism, then `⟨p₁^M, [M]⟩ = ⟨p₁^N, [N]⟩`. -/
theorem p₁Number_eq_of_bordant {M N : ClosedOriented 4} (h : Bordism M N)
    (p₁W : (cochainC ℤ (TopCat.toSSet.obj h.W)).homology 4)
    (p₁M : (cochainC ℤ (TopCat.toSSet.obj M.X)).homology 4)
    (p₁N : (cochainC ℤ (TopCat.toSSet.obj N.X)).homology 4)
    (hM : (singularCohomologyMap ℤ M.X h.W h.iM 4).hom p₁W = p₁M)
    (hN : (singularCohomologyMap ℤ N.X h.W h.iN 4).hom p₁W = p₁N) :
    p₁Number (TopCat.toSSet.obj M.X) M.c p₁M
      = p₁Number (TopCat.toSSet.obj N.X) N.c p₁N := by
  rw [p₁Number_apply, p₁Number_apply, ← hM, ← hN]
  rw [← kronH_natural M.X h.W h.iM 4 p₁W M.c, h.hbd,
    kronH_natural N.X h.W h.iN 4 p₁W N.c]

namespace PontryaginBordism

variable {M N : ClosedOriented 8} (h : PontryaginBordism M N)

/-- **Bordism invariance of the `p₂`-number**, for a bordism with Pontryagin data. -/
theorem p₂Number_eq : p₂Number (TopCat.toSSet.obj M.X) M.c h.p₂M
    = p₂Number (TopCat.toSSet.obj N.X) N.c h.p₂N :=
  p₂Number_eq_of_bordant h.toBordism h.p₂W h.p₂M h.p₂N h.hp₂M h.hp₂N

/-- **Bordism invariance of the `p₁²`-number**, for a bordism with Pontryagin data. -/
theorem p₁SqNumber_eq : p₁SqNumber (TopCat.toSSet.obj M.X) M.c h.p₁M
    = p₁SqNumber (TopCat.toSSet.obj N.X) N.c h.p₁N :=
  p₁SqNumber_eq_of_bordant h.toBordism h.p₁W h.p₁M h.p₁N h.hp₁M h.hp₁N

/-- **The `p₁²` and `p₂` numbers of `M` and `N` agree** for a bordism with Pontryagin data. -/
theorem numbers_eq :
    (p₁SqNumber (TopCat.toSSet.obj M.X) M.c h.p₁M, p₂Number (TopCat.toSSet.obj M.X) M.c h.p₂M)
      = (p₁SqNumber (TopCat.toSSet.obj N.X) N.c h.p₁N,
         p₂Number (TopCat.toSSet.obj N.X) N.c h.p₂N) := by
  rw [h.p₁SqNumber_eq, h.p₂Number_eq]

end PontryaginBordism

/-! ## The dimension-`8` case, in the form used by the endgame -/

/-- **Bordism invariance of the signature in dimension `8`** (`k = 4`): the signature of a closed
oriented `8`-manifold is a bordism invariant, given the two named geometric inputs (Poincaré
duality on the two closed pieces, and Lefschetz duality `Work.Bordism.HalfDimension` for the
bordism). -/
theorem sigma_eq_of_bordant_eight {M N : ClosedOriented 8} (h : Bordism M N)
    [FiniteDimensional ℚ (ratCohomology 4 (TopCat.toSSet.obj M.X))]
    [FiniteDimensional ℚ (ratCohomology 4 (TopCat.toSSet.obj N.X))]
    (hndM : Nondegenerate (midForm (k := 4) M)) (hndN : Nondegenerate (midForm (k := 4) N))
    (hdim : HalfDimension 4 h) :
    sigma 4 (TopCat.toSSet.obj M.X) M.c = sigma 4 (TopCat.toSSet.obj N.X) N.c :=
  sigma_eq_of_bordant h hndM hndN hdim

/-- **Bordism invariance of the triple of numbers** `(σ, p₁², p₂)` in dimension `8`**, for a
bordism with Pontryagin data and the duality inputs for the signature.  This is the statement that
the three numbers are well defined on bordism classes, i.e. the input that turns a rational model of
`Ω^SO_8 ⊗ ℚ` into the three `ℚ`-linear functionals of `Work.Bordism.Generation8`. -/
theorem PontryaginBordism.full_numbers_eq {M N : ClosedOriented 8} (h : PontryaginBordism M N)
    [FiniteDimensional ℚ (ratCohomology 4 (TopCat.toSSet.obj M.X))]
    [FiniteDimensional ℚ (ratCohomology 4 (TopCat.toSSet.obj N.X))]
    (hndM : Nondegenerate (midForm (k := 4) M)) (hndN : Nondegenerate (midForm (k := 4) N))
    (hdim : HalfDimension 4 h.toBordism) :
    (sigma 4 (TopCat.toSSet.obj M.X) M.c, p₁SqNumber (TopCat.toSSet.obj M.X) M.c h.p₁M,
        p₂Number (TopCat.toSSet.obj M.X) M.c h.p₂M)
      = (sigma 4 (TopCat.toSSet.obj N.X) N.c, p₁SqNumber (TopCat.toSSet.obj N.X) N.c h.p₁N,
        p₂Number (TopCat.toSSet.obj N.X) N.c h.p₂N) := by
  rw [h.p₁SqNumber_eq, h.p₂Number_eq,
    sigma_eq_of_bordant_eight h.toBordism hndM hndN hdim]

/-! ## The invariance theorem for manifolds bundled with their Poincaré duality data -/

/-- A **closed oriented `2k`-manifold, with its Poincaré duality datum**: the middle cohomology
`Hᵏ(M;ℤ) ⊗[ℤ] ℚ` is finite dimensional and the middle intersection form `midForm M` is
nondegenerate.  Both are theorems of topology for an honest closed oriented smooth manifold
(finite generation of cohomology, and Poincaré duality), which this library cannot prove in general;
they are therefore part of the structure. -/
structure PoincareManifold (k : ℕ) where
  /-- the underlying manifold (space + fundamental class) -/
  toClosedOriented : ClosedOriented (k + k)
  /-- finite generation of the middle cohomology (over `ℚ`) -/
  finite : FiniteDimensional ℚ (ratCohomology k (TopCat.toSSet.obj toClosedOriented.X))
  /-- nondegeneracy of the middle intersection form (Poincaré duality) -/
  nondegenerate : Nondegenerate (midForm toClosedOriented)

namespace PoincareManifold

variable {k : ℕ}

/-- **Bordism invariance of the signature**, for closed oriented `2k`-manifolds bundled with their
Poincaré duality data: if `M` and `N` are bordant (in the sense of
`Work.Bordism.Bordism` between their underlying oriented manifolds) and the bordism satisfies the
middle-degree Lefschetz duality input `Work.Bordism.HalfDimension`, then their signatures agree. -/
theorem sigma_eq_of_bordant {M N : PoincareManifold k} (h : Bordism M.toClosedOriented N.toClosedOriented)
    (hdim : HalfDimension k h) :
    sigma k (TopCat.toSSet.obj M.toClosedOriented.X) M.toClosedOriented.c
      = sigma k (TopCat.toSSet.obj N.toClosedOriented.X) N.toClosedOriented.c := by
  haveI := M.finite
  haveI := N.finite
  exact _root_.Work.Bordism.sigma_eq_of_bordant h M.nondegenerate N.nondegenerate hdim

/-- The middle form of a `PoincareManifold` is nondegenerate, in the form of a statement. -/
theorem nondegenerate_midForm (M : PoincareManifold k) : Nondegenerate (midForm M.toClosedOriented) :=
  M.nondegenerate

end PoincareManifold

end

end Work.Bordism
