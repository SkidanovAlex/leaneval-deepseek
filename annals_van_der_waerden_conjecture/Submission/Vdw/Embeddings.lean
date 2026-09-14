import Mathlib
import Submission.Vdw.SplittingField
import Submission.Vdw.GaloisAction

open Polynomial
open scoped NumberField

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Embeddings of `K_p = ℚ[x]/(p)` into algebras where `p` splits (steps 2–3 of (c))

The inertia/orbit analysis of step (c) (`CaseI.fieldDisc_val_one_has_isSwap`)
is phrased over the *embeddings* of `K_f = ℚ[x]/(f)` into the splitting
field `L = p.SplittingField` (the roots of `f` are the values of these
embeddings at a generator).  This module builds the basic API for those
embeddings, quite generally: for any irreducible `p : ℚ[X]` and any
`ℚ`-algebra `S`, the `ℚ`-algebra homomorphisms
`AdjoinRoot p →ₐ[ℚ] S` are in bijection with the roots of `p` in `S`:

* `embRoot`: the value `σ (root p)` of an embedding at the generator;
* `embRoot_aeval`: that value is a root (`aeval (embRoot σ) p = 0`);
* `embEquivRoots`: `(AdjoinRoot p →ₐ[ℚ] S) ≃ {x : S // aeval x p = 0}`
  (inverse: `AdjoinRoot.liftAlgHom` at the root);
* `embEquivRootSet`: reindexing by `p.rootSet p p.SplittingField`;
* `embEquivFin`: for `S = p.SplittingField` there are exactly
  `natDegree p` embeddings (composition with `GaloisAction.rootFinEquiv`) —
  so the embedding set is a concrete finite type of size `n`.

These facts give the vocabulary (embeddings = roots = `Fin n`) in which the
fiber/contraction correspondence of step (c) is stated.
-/

namespace Submission.Vdw

noncomputable section

open Polynomial

/-- The canonical `ℚ`-algebra embedding of `K_p = ℚ[x]/(p)` into its
splitting field (`AdjoinRoot.liftAlgHom` at `splRootVal p`). -/
noncomputable def kpolyAlgEmb (p : ℚ[X]) [Fact (Irreducible p)] :
    AdjoinRoot p →ₐ[ℚ] p.SplittingField :=
  AdjoinRoot.liftAlgHom (p := p) (i := Algebra.ofId ℚ p.SplittingField) (x := splRootVal p)
    (by simpa [Polynomial.aeval_def] using splRoot_aeval p)

/-- The value of an embedding at the generator of `K_p`. -/
noncomputable def embRoot {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : R[X]) (σ : AdjoinRoot p →ₐ[R] S) : S :=
  σ (AdjoinRoot.root p)

/-- An embedding sends the generator to a root of `p`. -/
theorem embRoot_aeval {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : R[X]) (σ : AdjoinRoot p →ₐ[R] S) : aeval (embRoot p σ) p = 0 := by
  dsimp [embRoot]
  have hcomp : σ.toRingHom.comp (AdjoinRoot.of p) = algebraMap R S :=
    RingHom.ext_iff.mpr σ.commutes
  rw [aeval_def, ← hcomp, ← map_zero σ.toRingHom, ← AdjoinRoot.eval₂_root p, Polynomial.hom_eval₂]
  rfl

/-- Two embeddings agree iff they agree at the generator (Mathlib
`AdjoinRoot.algHom_ext`). -/
theorem emb_ext {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {p : R[X]} {σ τ : AdjoinRoot p →ₐ[R] S} (h : embRoot p σ = embRoot p τ) : σ = τ := by
  exact AdjoinRoot.algHom_ext (f := p) h

/-- The embedding obtained from a root (the universal property of the
quotient `R[X]/(p)`). -/
noncomputable def rootEmb {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : R[X]) (x : S) (hx : aeval x p = 0) : AdjoinRoot p →ₐ[R] S := by
  classical
  -- AdjoinRoot.liftAlgHom needs `p.eval₂ i x = 0` with `i : R →ₐ[R] S`; aeval x p
  -- is `eval₂ (algebraMap R S) x p`.
  have hx' : p.eval₂ (Algebra.ofId R S : R →ₐ[R] S) x = 0 := by
    simpa [Polynomial.aeval_def] using hx
  exact AdjoinRoot.liftAlgHom (p := p) (i := Algebra.ofId R S) (x := x) hx'

/-- `embRoot` and `rootEmb` are inverse to each other. -/
theorem embRoot_rootEmb {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : R[X]) (x : S) (hx : aeval x p = 0) : embRoot p (rootEmb p x hx) = x := by
  dsimp [embRoot, rootEmb]
  simp

/-- `rootEmb` of the image recovers the embedding. -/
theorem rootEmb_embRoot {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : R[X]) (σ : AdjoinRoot p →ₐ[R] S) : rootEmb p (embRoot p σ) (embRoot_aeval p σ) = σ := by
  classical
  apply emb_ext
  simp [embRoot_rootEmb]

/-- **Embeddings ↔ roots.**  The `R`-algebra homomorphisms from
`R[x]/(p)` to `S` correspond bijectively to the roots of `p` in `S`. -/
noncomputable def embEquivRoots {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : R[X]) : (AdjoinRoot p →ₐ[R] S) ≃ {x : S // aeval x p = 0} where
  toFun σ := ⟨embRoot p σ, embRoot_aeval p σ⟩
  invFun x := rootEmb p x.1 x.2
  left_inv σ := by
    apply emb_ext
    exact embRoot_rootEmb p (embRoot p σ) (embRoot_aeval p σ)
  right_inv x := by
    ext
    exact embRoot_rootEmb p x.1 x.2

section SplittingField

/-- For irreducible `p`, the roots of `p` in its splitting field are exactly
the points with `aeval x p = 0` (reindexing of `embEquivRoots`). -/
noncomputable def embEquivRootSet (p : ℚ[X]) [Fact (Irreducible p)] :
    (AdjoinRoot p →ₐ[ℚ] p.SplittingField) ≃
      {x : p.SplittingField // x ∈ p.rootSet p.SplittingField} := by
  classical
  have hp0 : p ≠ 0 := (Irreducible.ne_zero Fact.out)
  exact (embEquivRoots p).trans {
    toFun := fun x => ⟨x.1, (Polynomial.mem_rootSet.mpr ⟨hp0, x.2⟩)⟩
    invFun := fun x => ⟨x.1, (Polynomial.mem_rootSet.mp x.2).2⟩
    left_inv := by
      intro x
      apply Subtype.ext
      rfl
    right_inv := by
      intro x
      apply Subtype.ext
      rfl }

/-- **Exactly `natDegree p` embeddings**: the `ℚ`-algebra embeddings of
`K_p = ℚ[x]/(p)` into its splitting field are in bijection with
`Fin p.natDegree` (composition of `embEquivRootSet` with the root
identification `GaloisAction.rootFinEquiv`). -/
noncomputable def embEquivFin (p : ℚ[X]) [Fact (Irreducible p)] :
    (AdjoinRoot p →ₐ[ℚ] p.SplittingField) ≃ Fin p.natDegree := by
  classical
  exact (embEquivRootSet p).trans (rootFinEquiv p (separable_of_irreducible_rat Fact.out))

end SplittingField

end

/-- **Root of the canonical embedding.**  The canonical embedding
`kpolyAlgEmb p : K_p ↪ p.SplittingField` sends the generator to the chosen
root `splRootVal p`. -/
theorem embRoot_kpolyAlgEmb (p : ℚ[X]) [Fact (Irreducible p)] :
    embRoot p (kpolyAlgEmb p) = splRootVal p := by
  dsimp [embRoot, kpolyAlgEmb]
  simp

section GaloisAction

/-- The natural action of `Gal(L/ℚ)` (`L = p.SplittingField`) on the
embeddings of `K_p` into `L`, by composition: `g · σ = g ∘ σ`. -/
noncomputable def galSmulEmb (p : ℚ[X]) [Fact (Irreducible p)] (g : p.Gal)
    (σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField) : AdjoinRoot p →ₐ[ℚ] p.SplittingField :=
  g.toAlgHom.comp σ

/-- The action commutes with taking the root: `embRoot (g · σ) = g (embRoot σ)`. -/
theorem embRoot_galSmulEmb (p : ℚ[X]) [Fact (Irreducible p)] (g : p.Gal)
    (σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField) :
    embRoot p (galSmulEmb p g σ) = g (embRoot p σ) := by
  dsimp [galSmulEmb, embRoot]
  rfl

/-- **Element-level transitivity of roots in the splitting field.**  For
irreducible `p`, the Galois group `Gal(L/ℚ)` (`L = p.SplittingField`) maps
any root of `p` to any other root.  (Consequence of the normality of the
splitting field: `Normal.minpoly_eq_iff_mem_orbit`.) -/
theorem exists_gal_map_root (p : ℚ[X]) [Fact (Irreducible p)] {x y : p.SplittingField}
    (hx : aeval x p = 0) (hy : aeval y p = 0) : ∃ g : p.Gal, g x = y := by
  classical
  have hx' := minpoly.eq_of_irreducible Fact.out hx
  have hy' := minpoly.eq_of_irreducible Fact.out hy
  have heq : minpoly ℚ x = minpoly ℚ y := hx'.symm.trans hy'
  haveI : Normal ℚ p.SplittingField := Polynomial.SplittingField.instNormal p
  obtain ⟨g0, hg0⟩ := (Normal.minpoly_eq_iff_mem_orbit p.SplittingField).mp heq
  -- hg0 : g0 • y = x; take g := g0⁻¹
  refine ⟨g0⁻¹, ?_⟩
  calc
    (g0⁻¹ : p.Gal) x = g0⁻¹ • x := rfl
    _ = g0⁻¹ • (g0 • y) := by rw [← hg0]
    _ = y := by
      rw [← mul_smul]
      simp

/-- **Transitivity of the Galois action on embeddings.**  For irreducible
`p`, any two embeddings of `K_p` into the splitting field are related by an
element of `Gal(L/ℚ)`. -/
theorem galSmulEmb_transitive (p : ℚ[X]) [Fact (Irreducible p)]
    (σ τ : AdjoinRoot p →ₐ[ℚ] p.SplittingField) :
    ∃ g : p.Gal, galSmulEmb p g σ = τ := by
  classical
  rcases exists_gal_map_root p (embRoot_aeval p σ) (embRoot_aeval p τ) with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  apply emb_ext
  rw [embRoot_galSmulEmb]
  exact hg

end GaloisAction

section GaloisActionOnEmbeddings

/-- The Galois action is compatible with composition: `1 · σ = σ`. -/
lemma galSmulEmb_one (p : ℚ[X]) [Fact (Irreducible p)]
    (σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField) :
    galSmulEmb p (1 : p.Gal) σ = σ := by
  rfl

/-- The Galois action is compatible with composition: `(g·h) · σ = g · (h · σ)`. -/
lemma galSmulEmb_mul (p : ℚ[X]) [Fact (Irreducible p)] (g h : p.Gal)
    (σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField) :
    galSmulEmb p (g * h) σ = galSmulEmb p g (galSmulEmb p h σ) := by
  rfl

/-- **Every embedding is `g · ι` for the canonical embedding** `ι =
kpolyAlgEmb p`: the (typeclass-free) content of "the Galois action is
transitive and its orbit of `ι` is the full embedding set". -/
theorem exists_gal_of_embedding (p : ℚ[X]) [Fact (Irreducible p)]
    (σ : AdjoinRoot p →ₐ[ℚ] p.SplittingField) :
    ∃ g : p.Gal, galSmulEmb p g (kpolyAlgEmb p) = σ := by
  exact galSmulEmb_transitive p (kpolyAlgEmb p) σ

end GaloisActionOnEmbeddings


/-- The scalar action underlying the embedding action (`galSmulEmb`), as a
typeclass value for use with Mathlib group-action lemmas (`letI` at use). -/
noncomputable def galEmbSMul (p : ℚ[X]) [Fact (Irreducible p)] :
    SMul p.Gal (AdjoinRoot p →ₐ[ℚ] p.SplittingField) where
  smul := galSmulEmb p

/-- The embedding action as a `MulAction` (pair with `galEmbSMul`). -/
noncomputable def galEmbMulAction (p : ℚ[X]) [Fact (Irreducible p)] :
    MulAction p.Gal (AdjoinRoot p →ₐ[ℚ] p.SplittingField) := by
  letI : SMul p.Gal (AdjoinRoot p →ₐ[ℚ] p.SplittingField) := galEmbSMul p
  exact { one_smul := galSmulEmb_one p, mul_smul := galSmulEmb_mul p }
section StabilizerOnEmbeddings

/-- The stabilizer of the canonical embedding `ι = kpolyAlgEmb p` in
`Gal(L/ℚ)`: `H = {g | g·ι = ι}` (the automorphisms fixing `ι(K_p)`
pointwise). -/
noncomputable def embStabilizer (p : ℚ[X]) [Fact (Irreducible p)] : Subgroup p.Gal where
  carrier := {g : p.Gal | galSmulEmb p g (kpolyAlgEmb p) = kpolyAlgEmb p}
  one_mem' := by
    simpa using (galSmulEmb_one p (kpolyAlgEmb p))
  mul_mem' := by
    intro g h hg hh
    change galSmulEmb p (g * h) (kpolyAlgEmb p) = kpolyAlgEmb p
    rw [galSmulEmb_mul p g h (kpolyAlgEmb p), hh, hg]
  inv_mem' := by
    intro g hg
    -- g⁻¹ · ι = g⁻¹ · (g · ι) = (g⁻¹·g) · ι = 1 · ι = ι
    calc
      galSmulEmb p g⁻¹ (kpolyAlgEmb p) =
          galSmulEmb p g⁻¹ (galSmulEmb p g (kpolyAlgEmb p)) := by rw [hg]
      _ = galSmulEmb p (g⁻¹ * g) (kpolyAlgEmb p) := by rw [galSmulEmb_mul p g⁻¹ g (kpolyAlgEmb p)]
      _ = kpolyAlgEmb p := by
        rw [inv_mul_cancel]
        exact galSmulEmb_one p (kpolyAlgEmb p)

/-- Membership in the stabilizer: `g ∈ embStabilizer p ⟺ g·ι = ι`. -/
theorem mem_embStabilizer (p : ℚ[X]) [Fact (Irreducible p)] (g : p.Gal) :
    g ∈ embStabilizer p ↔ galSmulEmb p g (kpolyAlgEmb p) = kpolyAlgEmb p := by
  rfl

end StabilizerOnEmbeddings
end Submission.Vdw
