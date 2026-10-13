import Mathlib

namespace Work.DSEQP

universe u

open CategoryTheory

set_option linter.style.haveILetI false

/-- If the `(q+1)`-st homology of a cochain complex of `A`-modules is a finitely generated
`A`-module, then there are finitely many `(q+1)`-cocycles `z i` which generate every cocycle modulo
coboundaries: for every cocycle `w` there are `a i : A` with
`w - ∑ i, a i • z i ∈ LinearMap.range ((K.d q (q+1)).hom)`.

Suggested route: `K.homology (q+1)` is `(K.sc (q+1)).homology` and
`ShortComplex.moduleCatHomologyIso` identifies it with
`↥(LinearMap.ker (K.d (q+1) (q+2)).hom ⧸ range ShortComplex.moduleCatToCycles)`.  Take finitely
many generators of `K.homology (q+1)` (e.g. from `Module.Finite.exists_fin`), transport them to that
quotient, lift each of them to an element `z i` of `LinearMap.ker (K.d (q+1) (q+2)).hom` (using that
`Submodule.mkQ` is surjective), and for an arbitrary cocycle `w` express its class as a linear
combination of the generators and use `Submodule.Quotient.eq` to conclude that the difference lies in
the range of `ShortComplex.moduleCatToCycles`, i.e. is a coboundary. -/
theorem eqp_cech_cocycle_generators {A : Type u} [CommRing A]
    (K : CochainComplex (ModuleCat.{u} A) ℕ) (q : ℕ)
    (h : Module.Finite A (K.homology (q + 1))) :
    ∃ (r : ℕ) (z : Fin r → K.X (q + 1)),
      (∀ i, (K.d (q + 1) (q + 2)).hom (z i) = 0) ∧
      ∀ w : K.X (q + 1), (K.d (q + 1) (q + 2)).hom w = 0 →
        ∃ a : Fin r → A, w - ∑ i, a i • z i ∈ LinearMap.range ((K.d q (q + 1)).hom) := by
  -- `K.homology (q+1)` only knows about the shape `ComplexShape.up ℕ` through the
  -- non-computable `prev`/`next`, so we replace the short complex `K.sc (q+1)` by the
  -- short complex `S` with *explicit* degrees `q → q+1 → q+2`.
  haveI := h
  obtain ⟨r, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := K.homology (q + 1))
  let S : ShortComplex (ModuleCat.{u} A) := K.sc' q (q+1) (q+2)
  have hprev : (ComplexShape.up ℕ).prev (q+1) = q :=
    ComplexShape.prev_eq' _ (ComplexShape.up_mk q (q+1) rfl)
  have hnext : (ComplexShape.up ℕ).next (q+1) = q+2 :=
    ComplexShape.next_eq' _ (ComplexShape.up_mk (q+1) (q+2) (by omega))
  -- The cycles of `K` in degree `q+1`, as a submodule of `K.X (q+1)`.
  let p : Submodule A ↥(LinearMap.ker S.g.hom) := LinearMap.range S.moduleCatToCycles
  -- The concrete description of the homology: cycles modulo boundaries.
  let e : K.homology (q+1) ≃ₗ[A] (↥(LinearMap.ker S.g.hom) ⧸ p) :=
    ((K.homologyIsoSc' q (q+1) (q+2) hprev hnext).trans S.moduleCatHomologyIso).toLinearEquiv
  -- Lift the images of the generators to cycles.
  choose y hy using fun i : Fin r => Submodule.mkQ_surjective p (e (g i))
  let z : Fin r → K.X (q+1) := fun i => ((y i : ↥(LinearMap.ker S.g.hom)) : S.X₂)
  refine ⟨r, z, fun i => (y i).2, ?_⟩
  intro w hw
  let wK : ↥(LinearMap.ker S.g.hom) := ⟨w, hw⟩
  -- The class of `w` is a combination of the classes of the chosen cocycles.
  have hspan : e.symm (p.mkQ wK) ∈ Submodule.span A (Set.range g) := by rw [hg]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hspan
  have ha' : ∑ i, a i • p.mkQ (y i) = p.mkQ wK := by
    calc ∑ i, a i • p.mkQ (y i)
        = ∑ i, a i • e (g i) := by simp [hy]
      _ = e (∑ i, a i • g i) := by simp
      _ = e (e.symm (p.mkQ wK)) := by rw [ha]
      _ = p.mkQ wK := e.apply_symm_apply _
  have hsplit : p.mkQ (∑ i, a i • y i) = p.mkQ wK := by simpa using ha'
  have hmem : (∑ i, a i • y i) - wK ∈ p := by
    have h2 := hsplit
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at h2
    exact (Submodule.Quotient.eq p).1 h2
  -- So the difference is a boundary: it lies in the range of `moduleCatToCycles`.
  obtain ⟨x, hx⟩ := hmem
  have hxval : S.f.hom x = (∑ i, a i • z i) - w := by
    have h1 := congrArg (fun u : ↥(LinearMap.ker S.g.hom) => (u : S.X₂)) hx
    rw [show ((S.moduleCatToCycles x : ↥(LinearMap.ker S.g.hom)) : S.X₂) = S.f.hom x
      from rfl] at h1
    rw [h1]
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul]
    rfl
  refine ⟨a, -x, ?_⟩
  show S.f.hom (-x) = w - ∑ i, a i • z i
  rw [map_neg, hxval]
  abel

end Work.DSEQP
