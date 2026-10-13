import Mathlib

universe a

open CategoryTheory

namespace Work.DSEQ0

/-- Two `XIsoOfEq`'s of the same equation are equal (they are `eqToIso` of proofs of the
same proposition).  Used to compare reindexing isomorphisms produced by different `by omega`
proofs with the ones coming out of a hypothesis. -/
lemma XIsoOfEq_proof_irrel {ι : Type*} {V : Type*} [Category V] [Limits.HasZeroMorphisms V]
    {c : ComplexShape ι} (K : HomologicalComplex V c) {p q : ι} (h₁ h₂ : p = q) :
    K.XIsoOfEq h₁ = K.XIsoOfEq h₂ := by
  unfold HomologicalComplex.XIsoOfEq
  congr 1

/-- **The trace of `μ (d y, −)` is a difference of the traces of `d ∘ μ (y, −)` in adjacent
degrees.**  For a Leibniz product `μ` on a complex `F` of finite free `A`-modules (with the
standard Koszul sign rule), an element `y ∈ F.X (-1)`, and any degree `i`,
`tr (μ (d y, −)) = tr (d ∘ μ (y, −)) + tr (d ∘ μ (y, −))`,
where the three traces are taken on `F.X i`, `F.X i` and `F.X (i+1)` respectively.

The Leibniz rule at the single pair of indices `(-1, i)` gives
`d ∘ T = A - T' ∘ d` for the degree `-1` operators `T = μ (y, −)`, `T' = μ (y, −)` (shifted) and
the degree `0` operator `A = μ (d y, −)`; taking traces and using cyclicity of the trace
(`LinearMap.trace_comp_comm'`) to rewrite `tr (T' ∘ d) = tr (d ∘ T')` yields the identity.  All
the reindexing isomorphisms `F.XIsoOfEq` are the canonical ones and are handled by
`HomologicalComplex.d_comp_XIsoOfEq_hom`, `HomologicalComplex.XIsoOfEq_hom_comp_d`,
`HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom` and `ModuleCat.hom_comp`. -/
theorem trace_mul_identity (A : Type a) [CommRing A]
    (F : CochainComplex (ModuleCat.{a} A) ℤ)
    [∀ i : ℤ, Module.Finite A ↥(F.X i)] [∀ i : ℤ, Module.Free A ↥(F.X i)]
    (μ : ∀ i j : ℤ, ↥(F.X i) →ₗ[A] ↥(F.X j) →ₗ[A] ↥(F.X (i + j)))
    (hLeib : ∀ (i j : ℤ) (x : ↥(F.X i)) (y : ↥(F.X j)),
        (F.d (i + j) (i + j + 1)).hom ((μ i j x) y) =
          (F.XIsoOfEq (by omega : i + 1 + j = i + j + 1)).hom
              (((μ (i + 1) j) ((F.d i (i + 1)).hom x)) y)
          + (-1 : A) ^ i.natAbs •
              ((F.XIsoOfEq (by omega : i + (j + 1) = i + j + 1)).hom
                ((μ i (j + 1) x) ((F.d j (j + 1)).hom y))))
    (y : ↥(F.X (-1))) (i : ℤ) :
    LinearMap.trace A ↥(F.X i)
        ((F.XIsoOfEq (by omega : 0 + i = i)).hom.hom.comp (μ 0 i ((F.d (-1) 0).hom y)))
      = LinearMap.trace A ↥(F.X i)
          ((F.d (-1 + i) i).hom.comp (μ (-1) i y))
        + LinearMap.trace A ↥(F.X (i + 1))
          ((F.d (-1 + (i + 1)) (i + 1)).hom.comp (μ (-1) (i + 1) y)) := by
  have h0 : 0 + i = i := by omega
  have h1 : -1 + 1 + i = -1 + i + 1 := by omega
  have h2 : -1 + (i + 1) = -1 + i + 1 := by omega
  have he : -1 + i + 1 = i := by omega
  -- Reindexing identities: the differential `F.d (-1+i) i` and the composite of `F.d (-1+i) (-1+i+1)`
  -- with `XIsoOfEq` agree; likewise for the two multiplication maps.
  have hE : (F.XIsoOfEq he).hom.hom.comp (F.d (-1 + i) (-1 + i + 1)).hom
      = (F.d (-1 + i) i).hom := by
    rw [← ModuleCat.hom_comp]
    exact congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_XIsoOfEq_hom F he (-1 + i))
  have hIp : (F.XIsoOfEq he).hom.hom.comp (F.XIsoOfEq h1).hom.hom
      = (F.XIsoOfEq h0).hom.hom := by
    rw [← ModuleCat.hom_comp]
    rw [HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom F h1 he]
  have hIm : (F.XIsoOfEq he).hom.hom.comp (F.XIsoOfEq h2).hom.hom
      = (F.XIsoOfEq (h2.trans he)).hom.hom := by
    rw [← ModuleCat.hom_comp]
    rw [HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom F h2 he]
  have hJd : (F.d i (i + 1)).hom.comp (F.XIsoOfEq (h2.trans he)).hom.hom
      = (F.d (-1 + (i + 1)) (i + 1)).hom := by
    rw [← ModuleCat.hom_comp]
    rw [HomologicalComplex.XIsoOfEq_hom_comp_d F (h2.trans he) (i + 1)]
  -- The Leibniz rule at `(-1, i)`, pointwise, in the normal form used below.
  have hpoint : ∀ z : ↥(F.X i),
      (F.d (-1 + i) (-1 + i + 1)).hom ((μ (-1) i y) z)
        = (F.XIsoOfEq h1).hom.hom (((μ 0 i) ((F.d (-1) 0).hom y)) z)
          + (-1 : A) • ((F.XIsoOfEq h2).hom.hom ((μ (-1) (i + 1) y) ((F.d i (i + 1)).hom z))) := by
    intro z
    have h := hLeib (-1) i y z
    simpa using h
  have hmap : (F.d (-1 + i) (-1 + i + 1)).hom.comp (μ (-1) i y)
      = (F.XIsoOfEq h1).hom.hom.comp (μ 0 i ((F.d (-1) 0).hom y))
        + (-1 : A) • ((F.XIsoOfEq h2).hom.hom.comp
            ((μ (-1) (i + 1) y).comp ((F.d i (i + 1)).hom))) :=
    LinearMap.ext hpoint
  -- Push the reindexing isomorphism `E := F.XIsoOfEq he` through the Leibniz identity.
  have hE2 : (F.XIsoOfEq he).hom.hom.comp ((F.d (-1 + i) (-1 + i + 1)).hom.comp (μ (-1) i y))
      = (F.XIsoOfEq he).hom.hom.comp
          ((F.XIsoOfEq h1).hom.hom.comp (μ 0 i ((F.d (-1) 0).hom y)))
        + (-1 : A) • ((F.XIsoOfEq he).hom.hom.comp
            ((F.XIsoOfEq h2).hom.hom.comp ((μ (-1) (i + 1) y).comp ((F.d i (i + 1)).hom)))) := by
    rw [hmap, LinearMap.comp_add, LinearMap.comp_smul]
  -- The resulting identity of traces.
  have htE2 : LinearMap.trace A ↥(F.X i)
        ((F.XIsoOfEq he).hom.hom.comp ((F.d (-1 + i) (-1 + i + 1)).hom.comp (μ (-1) i y)))
      = LinearMap.trace A ↥(F.X i)
          ((F.XIsoOfEq he).hom.hom.comp
            ((F.XIsoOfEq h1).hom.hom.comp (μ 0 i ((F.d (-1) 0).hom y))))
        + (-1 : A) * LinearMap.trace A ↥(F.X i)
            ((F.XIsoOfEq he).hom.hom.comp
              ((F.XIsoOfEq h2).hom.hom.comp
                ((μ (-1) (i + 1) y).comp ((F.d i (i + 1)).hom)))) := by
    rw [hE2, map_add, map_smul, smul_eq_mul]
  -- Identify the three reindexed traces with the ones appearing in the statement.
  have t1 : LinearMap.trace A ↥(F.X i)
        ((F.XIsoOfEq h0).hom.hom.comp (μ 0 i ((F.d (-1) 0).hom y)))
      = LinearMap.trace A ↥(F.X i)
          ((F.XIsoOfEq he).hom.hom.comp
            ((F.XIsoOfEq h1).hom.hom.comp (μ 0 i ((F.d (-1) 0).hom y)))) := by
    congr 1
    rw [← hIp, LinearMap.comp_assoc]
  have t3 : LinearMap.trace A ↥(F.X i)
        ((F.XIsoOfEq he).hom.hom.comp ((F.d (-1 + i) (-1 + i + 1)).hom.comp (μ (-1) i y)))
      = LinearMap.trace A ↥(F.X i) ((F.d (-1 + i) i).hom.comp (μ (-1) i y)) := by
    congr 1
    rw [← LinearMap.comp_assoc, hE]
  have t4 : LinearMap.trace A ↥(F.X i)
        ((F.XIsoOfEq he).hom.hom.comp
          ((F.XIsoOfEq h2).hom.hom.comp ((μ (-1) (i + 1) y).comp ((F.d i (i + 1)).hom))))
      = LinearMap.trace A ↥(F.X (i + 1))
          ((F.d (-1 + (i + 1)) (i + 1)).hom.comp (μ (-1) (i + 1) y)) := by
    rw [← LinearMap.comp_assoc, hIm]
    rw [← LinearMap.trace_comp_comm' (f := (F.XIsoOfEq (h2.trans he)).hom.hom)
      (g := (μ (-1) (i + 1) y).comp ((F.d i (i + 1)).hom))]
    rw [LinearMap.comp_assoc, hJd]
    rw [← LinearMap.trace_comp_comm' (f := (F.d (-1 + (i + 1)) (i + 1)).hom)
      (g := μ (-1) (i + 1) y)]
  -- Rearranged form of `htE2`, in terms of the traces appearing in the statement.
  have key : LinearMap.trace A ↥(F.X i) ((F.d (-1 + i) i).hom.comp (μ (-1) i y))
      = LinearMap.trace A ↥(F.X i) ((F.XIsoOfEq h0).hom.hom.comp (μ 0 i ((F.d (-1) 0).hom y)))
        + (-1 : A) * LinearMap.trace A ↥(F.X (i + 1))
            ((F.d (-1 + (i + 1)) (i + 1)).hom.comp (μ (-1) (i + 1) y)) := by
    rw [← t3, htE2, ← t1, t4]
  -- The `XIsoOfEq` in the statement uses its own `by omega` proof; replace it by `h0`.
  have hbridge : (F.XIsoOfEq (by omega : 0 + i = i)) = (F.XIsoOfEq h0) :=
    XIsoOfEq_proof_irrel F (by omega : 0 + i = i) h0
  rw [hbridge, key]
  ring

end Work.DSEQ0
