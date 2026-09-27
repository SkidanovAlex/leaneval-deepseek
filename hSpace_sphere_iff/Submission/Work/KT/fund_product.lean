import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.Fund.Laurent
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.Fund.geom_glue
import Submission.Work.KT.Fund.Pullback
import Submission.Work.KT.Fund.Clutch
import Submission.Work.KT.Fund.laurent_approx
import Submission.Work.KT.Fund.AssemblyDefs
import Submission.Work.KT.k0_basic
import Submission.Work.KT.EG.fund_product_of_bott
import Submission.Work.KT.FP.fp_retract
import Submission.Work.KT.FP.fp_surj
import Submission.Work.KT.FP.fp_inj

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/KT/DESIGN.md (the lead's design for the odd case: Adams–Atiyah via K₀ of rings of continuous functions, ψ² and ψ³ from symmetric-power eigenspaces, Bott periodicity via Atiyah–Bott clutching). Shared definitions: Submission/Work/KT/Defs.lean (do NOT edit). CONVENTION: use [Ring A] plus an explicit commutativity hypothesis, never [CommRing A] on subalgebras (unification timeouts). Siblings run in parallel.

# Node `fund_product`

**Statement** (`fund_product.lean`, harness format; imports: `Submission.Work.KT.Defs`; namespace `Work.KT`):

```lean
/ -- The fundamental product (Bott periodicity, Atiyah–Bott): for compact Hausdorff `X`,
`K(X × S²)` is free over `K(X)` on `1` and the Hopf line bundle `H`. - /
theorem fund_product (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ)) (hμ : IsK0Mul μ) :
    Function.Bijective (fun ab : K0 C(X, ℂ) × K0 C(X, ℂ) =>
      K0.mapA (pullAlg (ContinuousMap.fst : C(X × S2, X))) ab.1 +
        μ (K0.mapA (pullAlg (ContinuousMap.fst : C(X × S2, X))) ab.2)
          (K0.mapA (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem))) := by sorry
```

**Size:** 15–30k lines. **Risk:** HIGH (hardest node). **Depends on (statements):** homotopy_inv, k0_exact, k0_basic. **Day 1:** yes — start at once (critical path). Fejér + linearisation + splitting (steps 2–4) need no other node; clutching (step 1) consumes k0_exact(3) and homotopy_inv when they land.

## Route

**Bott periodicity, Atiyah–Bott elementary proof.** References: Hatcher VBKT Thm 2.2 (pp. 41–47,
the copy in the workspace) and Atiyah, *K-theory* §2.2. Everything below is done in the idempotent
model: "bundle `E` over `X`" means an idempotent `e` over `C(X)`, and "automorphism of `E` over
`X×S¹`" means an invertible `f` over `C(X×S¹)` with `fe = ef`, invertible on `im e`.
1. **Clutching.** `S² = D₀ ∪_{S¹} D_∞` gives a Milnor square
   `C(X×S²) = C(X×D₀) ×_{C(X×S¹)} C(X×D_∞)`. A ring isomorphism needs an explicit homeomorphism
   `S²` ↔ two discs, which is quick.
   * Idempotents over `X×D` are similar to pull-backs from `X` (radial homotopy + homotopy_inv).
   * Hence every class is `[E, f]`, the clutching of `E ⊕ E` along `f`, built from Milnor patching
     (k0_exact (3)).
   * `[E,f]` depends only on the homotopy class of `f` (homotopy_inv on `X×S²`).
   * The construction is additive and multiplicative, and `[1, z] = [H]` (or `[H⁻¹]`, which is
     harmless because `{1,H}` and `{1,H⁻¹}` are both bases).
   * Check against `hopfIdem` once. Its clutching function is `z` (or `z̄`) on the standard chart.
2. **Laurent approximation.** Fejér sums of `f(x,·)` converge uniformly in `x`. Nearby invertibles
   are homotopic (straight line), so `f ≃ ℓ = Σ_{|k|≤N} a_k(x) z^k`. Then `[E,ℓ] = [E,z^{-N}q]`
   with `q` a polynomial.
3. **Linearisation** (Hatcher's `(n+1)×(n+1)` block matrix, homotopy by row operations):
   `[E,q] + n[E,1] = [(n+1)E, L^n q]`, with `L^n q = A(x)z + B(x)`.
4. **Linear clutching splitting.** For `Az + B` invertible on `|z| = 1`, let `P` be the Riesz
   projection `(1/2πi)∮ (Az+B)⁻¹A dz`. For the formalisation, prefer Hatcher's explicit
   construction via `(A + B)⁻¹` after the normalisation `A + B = 1`, which avoids contour
   integrals. Then `[E, Az+B] = [E₊, z] + [E₋, 1]`.
5. **Define `ν`.** `ν : K(X×S²) → K(X) ⊕ K(X)H` by `ν[E,f] = ((n+1)E ⊗ H^{-N}` reduced …`)`
   exactly as Hatcher. Check well-definedness (independence of `N`, `n`, and of the homotopy class
   within Laurent polynomials, using the linear-homotopy lemma).
6. **Inverse.** Show `ν ∘ μ = id` and `μ ∘ ν = id`. The node's `Function.Bijective` is exactly
   this.

Decomposition advice for the lead:
* clutching (1), 4–7k;
* Laurent/Fejér (2), 2–4k;
* linearisation (3), 2–4k;
* splitting (4), 3–6k;
* `ν` and the inverse (5–6), 4–8k.

If the Fejér step is painful: use Stone–Weierstrass (`ContinuousMap.starSubalgebra_topologicalClosure_eq_top`
for trigonometric polynomials) applied entrywise in `C(X×S¹)`. Laurent polynomials in `z` with
coefficients in `C(X)` are dense in `C(X×S¹)`.
-/


/-! ## Progress note (session H11)

Infrastructure built for this node (all in `Submission/Work/KT/Fund/`, all sorry-free unless
marked):

* `Fund.Basic` — calculus in the idempotent model of `K₀` (`cls` of MvN-equivalent idempotents,
  block sums, `Mat.map`, functoriality `K0.map_cls`/`K0.map_id`/`K0.map_comp`, `IsK0Mul_cls`).
* `Fund.Laurent` — the Laurent polynomial algebra `C(X)[T;T⁻¹]` mapping into `C(X × S¹, ℂ)`
  (`zUnit`, `laurentMap`).
* `Fund.Geom` — `S² = Sph (EuclideanSpace ℝ (Fin 3))` as two discs: the parametrisations
  `up`/`dn` of the closed hemispheres by the unit disc of `ℂ`, their agreement on the equator
  `up_eq_dn_of_norm_eq_one`, and the restriction maps `pullUp`, `pullDn`, `bdryRestrict`.
* `Fund.geom_glue` (delegated) — the gluing property: a compatible pair of functions on the two
  hemispheres glues to a unique function on `X × S²`.
* `Fund.Pullback` — the fibre product `pullAlg2 X` and the algebra isomorphism
  `glueEquiv X : C(X × S², ℂ) ≃ₐ[ℂ] pullAlg2 X`, plus `k0Glue`, the induced isomorphism of `K₀`.

Delegated and proved by the fleet: `Fund.hopf_relation` (the Bott relation `H² + 1 = 2H` for the
Hopf bundle), `Fund.geom_glue`.  Delegated and in progress: `Fund.laurent_approx` (invertible
matrices over `C(X × S¹)` are homotopic to Laurent polynomial ones), `Fund.spectral_split` (the
"inside" spectral projection of a matrix with spectrum off the unit circle).

## The route from here

The target is `Φ : K₀(C(X)) × K₀(C(X)) → K₀(C(X × S²))`, `(a,b) ↦ s(a+b) + s(b)·β` with `β` the
Bott class `H - 1`; `Φ` is bijective exactly when `K₀(C(X × S²)) = s(A) ⊕ s(A)·β`.

1. **Clutching construction.** With `pullAlg2`/`glueEquiv` in place, a class in `K₀(C(X × S²))` can
   be built from a pair `(e₊, e₋)` of idempotent matrices over the two disc algebras agreeing on
   the circle.  For `u` invertible over `C(X × S¹)` the "clutched" class `κ(u)` is obtained from
   lifts `F`, `G` of `u`, `u⁻¹` to the two discs by the *orthogonal projections onto the graph of
   `F`* and *onto the reciprocal graph of `G`*: these have the same image on the equator (the
   graph of `u` equals the reciprocal graph of `u⁻¹`) and hence agree as matrices there.  The
   orthogonality is needed precisely because it makes the projection a function of the image
   alone; the naive non-orthogonal graph projections would glue to a global graph and give the
   trivial bundle.
2. **Milnor patching / excision.** `ker (K₀(C(X × S²)) → K₀(C(X × D)) ⊕ K₀(C(X × D)))` is
   generated by the `κ(u)` (Milnor's Mayer–Vietoris for the square `pullAlg2`); this is the only
   place where the `K₁ → K₀` boundary map is needed (node `k0_exact`).
3. **Laurent + linearisation + splitting** reduce `κ(u)` to a combination of `κ(z)` and `s(A)`
   (`Fund.laurent_approx`, Hatcher's block-matrix linearisation, `Fund.spectral_split`).
4. **Assembly**: `κ(z)` is a generator of the reduced group and `s(b)β = 0 ⇒ b = 0`.
-/

/-! ## Progress note (session H11c) — the clutching construction `κ` is in place

**See `Submission/Work/KT/Fund/NOTES_kappa.md` for the full status, the plan and the pitfalls.**

Summary of this session:

* `Fund/Disc.lean` (new): the disc is contractible — `sD : K0 C(X,ℂ) → K0 C(X×D,ℂ)`,
  `ev0`, `ev0 ∘ sD = id`, `sD ∘ ev0 = id`, hence `sD`/`ev0` are inverse isomorphisms.  Also
  `cls_eq_of_path` (homotopy invariance of `cls` in a Banach algebra) and `continuous_bdryRestrict`.
* `Fund/OrthProjAlg.lean` (new): `orthProj_mul_self`, `orthProj_mul_apply`.
* `Fund/Kappa.lean` (new): the clutching construction over the two-disc decomposition:
  `prF`/`prS`, `pairMat`, `clutchIdem` (+`clutchIdem_isIdem`), `isClosed_pullAlg2`,
  `liftOf`/`liftOf_spec`, and the clutched class `kappa X n u ∈ K0 C(X×S²,ℂ)` of a unit `u`
  over `C(X×S¹,ℂ)`; plus `incl0`/`incl1`, `pullMat`, `zUnitMat`.
* Proved by colleagues (importable): `Fund.kappa_indep` (κ is independent of the chosen lifts),
  `Fund.kappa_one` (`κ(1_n) = cls (Mat.one n)`), `Fund.kappa_homotopic`, `Fund.kappa_const`
  (a unit pulled back from `C(X,ℂ)` has trivial clutch), `Fund.spectral_split_out`
  (the inside/outside spectral projection of a matrix with spectrum off `S¹`).
* Requested and in flight: `kappa_add` (block sums), `kappa_mul` (`∂` is a homomorphism),
  `kappa_hopf` (`κ(z) = snd*(cls hopfIdem)`), `kappa_bott` (the Bott unit
  `1 + (z-1)P`), `kappa_conj_abs` (conjugation by a pulled-back unit), `gen_kernel`
  (generation of `ker r` by the `κ`s — the "(GEN)" step).
* The remaining piece after those is the linear splitting (`kappa_lin`), the Laurent/twist step
  and Hatcher's linearisation, then the assembly described in `NOTES_kappa.md` §3–§5.

## Progress note (session H11d, 09:35) — the endgame

See `Submission/Work/KT/Idx/NOTES.md` for the state of the *only* remaining mathematical piece
(the Bott index, Hatcher's `ν`).  Summary:

* **The assembly of this theorem is verified**: the term
  `EG.fund_product_of_bott X μ hμ μX hμX (K0.mapA (pullAlg (Fund.bp X))) (FP.fp_retract X).1 hr
  (FP.fp_retract X).2 (FP.fp_surj X μ hμ) (FP.fp_inj X μ hμ)`
  (with `μX, hμX` from `k0_basic.1` and `hr := k0_basic.2.1 … (pullAlg (Fund.bp X)).toRingHom …`)
  has the type of this theorem; it is type-checked in
  `Submission/Work/KT/Idx/_asm_probe.lean` with the two later arguments taken as hypotheses.  So
  the file is finished by the above term the moment `FP.fp_surj` and `FP.fp_inj` are sorry-free.
* `FP.fp_retract` and `FP.kappa_eq_disc` are proved; `FP.fp_surj` and `FP.fp_inj` are *written*
  (no `sorry` in the files) but rest on three declarations that are still `sorry`:
  `Fund.kappa_bott` (the Bott-unit formula — blocks both halves, via `EG.kappa_reduce` and
  `kappa_lin`), `FP.bott_index` (the index), and the two remaining gaps of the (D)-route
  (`EG.kappa_twist`, `EG.kappa_linearise`).
* The index (`FP.bott_index`) decomposes into: idempotency of the pencil projection
  (`Work.Idx.penProj_idem`), its naturality/slicing (`Work.Idx.matPenProj_eval`), the pencil
  spectral gap (`Work.Idx.pen_annulus`), the degree-padding relations
  (`Work.Idx.wPen_append`, `Work.Idx.wPen_prepend`) and the normalisation
  (`Work.Idx.wPen_bott`) — all six delegated and in flight from
  `Submission/Work/KT/Idx/{PenDefs,WPen}.lean`.


## Progress note (session H11e, 14:40) — the node is assembled on an owned route

`Work.KT.fund_product` is now *proved* by the term

```
obtain ⟨μX, hμX, -, -, -⟩ := k0_basic.1 (C(X, ℂ)) (fun x y => mul_comm x y)
refine EG.fund_product_of_bott X μ hμ μX hμX (K0.mapA (pullAlg (Fund.bp X)))
  (FP.fp_retract X).1 ?_ (FP.fp_retract X).2 (FP.fp_surj X μ hμ)
  (Idx.BottInj.bottMap_injective X μ hμ)
intro x y
exact k0_basic.2.1 (C(X × S2, ℂ)) (C(X, ℂ)) (fun a b => mul_comm a b)
  (pullAlg (Fund.bp X)).toRingHom μ μX hμ hμX x y
```

whose only inputs are `EG.fund_product_of_bott` (proved), `FP.fp_retract` (proved),
`FP.fp_surj` (proved) and `Idx.BottInj.bottMap_injective` — an **owned** copy of `FP.fp_inj`
(namespace `Work.KT.Idx.BottInj`, file `Idx/bottMap_injective.lean`) that uses our own Bott index
`Work.KT.Idx.bott_index` instead of the (other agent's, still in-flight)
`Work.KT.FP.bott_index`.

The owned index route (all files mine, in `Submission/Work/KT/Idx/`):

* `NvalDefs.lean` — `ApproxData`, `adata`, `Nval`, `lindAt_hom_inv`, `lindAt_radius_eq`,
  `Nval_eq_of_hom`, `Nval_hom_inv` (the homotopy invariance of the index).
* `Nval_normalised.lean` — the normalisation clause `Nval ((1-P) + zP) = [P]` (proved).
* `Nval_stable.lean` — invariance of `Nval` under (left and right) multiplication by a unit pulled
  back from the base (the constant-unit case).
* `bott_index.lean` — `Work.KT.Idx.bott_index`, the two-clause theorem, assembled from
  `FP.disc_unit_homotopic_const`, `Nval_hom_inv` and `Nval_stable`.
* `linBf_const_identities.lean`, `lindAt_constLM.lean` — the block-matrix identities and the
  constant-unit cancellation of `lindAt` on which `Nval_stable` rests.

**Route of the assembly** (verified by hand, see the notes): `Φ` bijective ⟺ `bottMap`,
`a ↦ μ (s a) β`, is an isomorphism `K0 C(X,ℂ) ≅ ker r`.  Surjectivity of `bottMap` is (GEN) + (D);
injectivity is the same statement read backwards (the naive "apply `r` twice" argument does NOT
work, since every restriction map kills `β`).

-/

namespace Work.KT

/-- The fundamental product (Bott periodicity, Atiyah–Bott): for compact Hausdorff `X`,
`K(X × S²)` is free over `K(X)` on `1` and the Hopf line bundle `H`. -/
theorem fund_product (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ)) (hμ : IsK0Mul μ) :
    Function.Bijective (fun ab : K0 C(X, ℂ) × K0 C(X, ℂ) =>
      K0.mapA (pullAlg (ContinuousMap.fst : C(X × S2, X))) ab.1 +
        μ (K0.mapA (pullAlg (ContinuousMap.fst : C(X × S2, X))) ab.2)
          (K0.mapA (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem))) := by
  obtain ⟨μX, hμX, -, -, -⟩ := k0_basic.1 (C(X, ℂ)) (fun x y => mul_comm x y)
  refine EG.fund_product_of_bott X μ hμ μX hμX (K0.mapA (pullAlg (Fund.bp X)))
    (FP.fp_retract X).1 ?_ (FP.fp_retract X).2 (FP.fp_surj X μ hμ)
    (FP.fp_inj X μ hμ)
  intro x y
  exact k0_basic.2.1 (C(X × S2, ℂ)) (C(X, ℂ)) (fun a b => mul_comm a b)
    (pullAlg (Fund.bp X)).toRingHom μ μX hμ hμX x y

end Work.KT
