import Mathlib
import Submission.Commons.Lattice.Minkowski.covol_span_wedge

/-!
# The covol-wedge identity: covolume of a sublattice equals the wedge norm of its basis

Paper §3 works with the Grayson data `φ(W) = log‖W‖ + A·k(d−k)` over the saturated
`ℤ`-subgroups `W` of a lattice `Λ` in the Euclidean space `ℝ^d`; `‖W‖` is the norm of
`w₁∧⋯∧w_k` for a `ℤ`-basis of `W`.  That quantity is really the **covolume of the lattice
`W` inside its own real span** `V = span_ℝ W`.  This module proves the identity

    covol(W ; V) = ‖ιMulti b‖          (wedge norm in the ambient space)

in the following clean form: for a submodule `V` of the standard Euclidean space
`E = EuclideanSpace ℝ (Fin d)` with an `ℝ`-basis `b : Fin r → V` (`r = dim V`),

    covolume (ℤ-span of b, viewed in V) = ‖ιMulti r (ambient images of b)‖

(`covol_wedge_of_submodule_basis`).  The ambient formulation for a saturated submodule of
`E` spanned by an independent integer family `u` is `covol_saturated_wedge`.

The proof assembles three standard pieces:

1. `norm_iMulti_eq_of_inner_preserving` — a (not necessarily surjective) `ℝ`-linear map
   `f : F →ₗ G` preserving inner products preserves the norms of decomposable wedges
   (Gram-determinant argument via `exteriorPower.inner_ιMulti_ιMulti`);
2. `covolume_comap` (`ZLattice.covolume_comap` + `LinearIsometryEquiv.measurePreserving`):
   covolumes are invariant under the orthonormal-basis representation
   `φ : V ≃ₗᵢ EuclideanSpace ℝ (Fin r)`, reducing the covolume to the standard space where
   the Commons lemma `Commons.Lattice.Minkowski.covol_span_wedge` applies;
3. `span_top_of_linearIndependent` (generic): an independent family of `finrank`-many
   vectors spans the space.

All declarations are Mathlib-only apart from the listed Commons covol-wedge lemma.
-/

noncomputable section

open Set Filter Metric MeasureTheory Module Real BigOperators exteriorPower
open scoped ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 800000

namespace Submission.SubLatticeCovol

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- A (not necessarily surjective) `ℝ`-linear map preserving inner products preserves the
norms of decomposable exterior powers: `‖ιMulti (f∘v)‖ = ‖ιMulti v‖`. -/
lemma norm_iMulti_eq_of_inner_preserving (f : F →ₗ[ℝ] G)
    (hf : ∀ x y : F, inner ℝ (f x) (f y) = inner ℝ x y)
    (n : ℕ) (v : Fin n → F) :
    ‖exteriorPower.ιMulti ℝ n (fun i => f (v i))‖ = ‖exteriorPower.ιMulti ℝ n v‖ := by
  have hsq : (‖exteriorPower.ιMulti ℝ n (fun i => f (v i))‖ : ℝ) ^ 2 =
      ‖exteriorPower.ιMulti ℝ n v‖ ^ 2 := by
    calc
      (‖exteriorPower.ιMulti ℝ n (fun i => f (v i))‖ : ℝ) ^ 2 =
          inner ℝ (exteriorPower.ιMulti ℝ n (fun i => f (v i)))
            (exteriorPower.ιMulti ℝ n (fun i => f (v i))) := by
        simp
      _ = (Matrix.of (fun i j : Fin n => inner ℝ (f (v j)) (f (v i)))).det := by
        simpa [Function.comp_def] using
          (exteriorPower.inner_ιMulti_ιMulti (n := n) (x := fun i => f (v i))
            (y := fun i => f (v i)))
      _ = (Matrix.of (fun i j : Fin n => inner ℝ (v j) (v i))).det := by
        congr 1
        ext i j
        exact hf (v j) (v i)
      _ = inner ℝ (exteriorPower.ιMulti ℝ n v) (exteriorPower.ιMulti ℝ n v) := by
        exact (exteriorPower.inner_ιMulti_ιMulti (n := n) (x := v) (y := v)).symm
      _ = ‖exteriorPower.ιMulti ℝ n v‖ ^ 2 := by
        simpa using (inner_self_eq_norm_sq _)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have hpos1 : 0 ≤ ‖exteriorPower.ιMulti ℝ n (fun i => f (v i))‖ := norm_nonneg _
    have hpos2 : 0 ≤ ‖exteriorPower.ιMulti ℝ n v‖ := norm_nonneg _
    nlinarith

/-- An independent family of `finrank`-many vectors in a finite-dimensional space spans the
whole space. -/
lemma span_top_of_linearIndependent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {r : ℕ} (v : Fin r → E) (hv : LinearIndependent ℝ v)
    (hfin : Module.finrank ℝ E = r) :
    ⊤ ≤ Submodule.span ℝ (Set.range v) := by
  classical
  let S : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  have hfinS : Module.finrank ℝ S = r := by
    rw [finrank_span_eq_card (R := ℝ) (b := v) hv]
    simp
  have hq : Module.finrank ℝ (E ⧸ S) ≤ 0 := by
    have h := Module.finrank_quotient_add_finrank_le (R := ℝ) (M := E) (N := S)
    rw [hfinS, hfin] at h
    omega
  have hq0 : Module.finrank ℝ (E ⧸ S) = 0 := le_antisymm hq (Nat.zero_le _)
  have hsub : Subsingleton (E ⧸ S) :=
    (Module.finrank_zero_iff (R := ℝ) (M := E ⧸ S)).mp hq0
  intro x hx
  have hz : (S.mkQ x : E ⧸ S) = 0 := Subsingleton.elim _ _
  have hmem : x ∈ S := by
    have hz0 : (Submodule.Quotient.mk x : E ⧸ S) = 0 := by
      simpa [Submodule.mkQ_apply] using hz
    exact (Submodule.Quotient.mk_eq_zero (p := S)).1 hz0
  simpa [S] using hmem

/-- **The covol-wedge identity.**  Let `E = EuclideanSpace ℝ (Fin d)`, `V ≤ E` a submodule
with an `ℝ`-basis `b : Fin r → V` (so `r = dim V`); the full-rank lattice
`span ℤ (range b)` inside `V` has covolume equal to the **ambient** wedge norm of the basis:

`covolume (span ℤ (range b)) = ‖ιMulti ℝ r (fun i => (b i : E))‖`. -/
theorem covol_wedge_of_submodule_basis {d r : ℕ} (hr : 0 < r) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (b : Basis (Fin r) ℝ V) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) =
      ‖exteriorPower.ιMulti ℝ r (fun i : Fin r => ((b i : V) : EuclideanSpace ℝ (Fin d)))‖ := by
  classical
  let L : Submodule ℤ V := Submodule.span ℤ (Set.range b)
  have hfin : Module.finrank ℝ V = r := by
    rw [Module.finrank_eq_card_basis b]
    simp
  let efin : Fin (Module.finrank ℝ V) ≃ Fin r :=
    Fintype.equivFinOfCardEq (by simpa using hfin)
  let bON : OrthonormalBasis (Fin r) ℝ V := (stdOrthonormalBasis ℝ V).reindex efin
  let φ : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r) := bON.repr
  let eφ : V ≃L[ℝ] EuclideanSpace ℝ (Fin r) := φ.toContinuousLinearEquiv
  let f : V →ₗ[ℝ] EuclideanSpace ℝ (Fin r) := eφ
  let fℤ : V →ₗ[ℤ] EuclideanSpace ℝ (Fin r) := f.restrictScalars ℤ
  let w : Fin r → EuclideanSpace ℝ (Fin r) := fun i => eφ (b i)
  have he : MeasurePreserving (⇑eφ) volume volume := by
    simpa [eφ] using (φ.measurePreserving : MeasurePreserving (⇑φ) volume volume)
  have hinj : Function.Injective (⇑fℤ) := by
    intro x y hxy
    apply eφ.injective
    exact hxy
  have hφv : LinearIndependent ℝ w := by
    have hbLI : LinearIndependent ℝ (fun i : Fin r => (b i : V)) := b.linearIndependent
    have hmap : LinearIndependent ℝ (fun i => f ((b i : V))) := by
      exact hbLI.map' f (LinearMap.ker_eq_bot.mpr (by
        intro x y hxy
        apply eφ.injective
        exact hxy))
    simpa [w, f] using hmap
  have hsp₀ : ⊤ ≤ Submodule.span ℝ (Set.range w) := by
    exact span_top_of_linearIndependent w hφv (by simp)
  let bb₀ : Basis (Fin r) ℝ (EuclideanSpace ℝ (Fin r)) := Module.Basis.mk hφv hsp₀
  have hwbb : (fun i : Fin r => (bb₀ i : EuclideanSpace ℝ (Fin r))) = w :=
    Module.Basis.coe_mk hφv hsp₀
  let S : Submodule ℤ (EuclideanSpace ℝ (Fin r)) := Submodule.span ℤ (Set.range bb₀)
  have hcov := ZLattice.covolume_comap (L := S) (μ := (volume : Measure (EuclideanSpace ℝ (Fin r))))
    (F := V) (ν := (volume : Measure V)) (e := eφ) (he := he)
  have hSmap : S = L.map fℤ := by
    dsimp [S, L]
    have hm : (Submodule.span ℤ (Set.range b)).map fℤ =
        Submodule.span ℤ (Set.range (fun i : Fin r => fℤ (b i))) := by
      rw [Submodule.map_span]
      congr 1
      ext x
      simp
    have hfam : (fun i : Fin r => fℤ (b i)) = fun i : Fin r => (bb₀ i : EuclideanSpace ℝ (Fin r)) := by
      funext i
      rw [congr_fun hwbb i]
      simp [fℤ, f, w]
    rw [hm, hfam]
  have hC : ZLattice.comap ℝ S (↑↑eφ) = L := by
    unfold ZLattice.comap
    rw [hSmap]
    change (L.map fℤ).comap fℤ = L
    exact Submodule.comap_map_eq_of_injective hinj L
  have hT : ZLattice.covolume L (volume : Measure V) =
      ZLattice.covolume S (volume : Measure (EuclideanSpace ℝ (Fin r))) := by
    rw [← hC]
    simpa using hcov
  have hS : ZLattice.covolume S (volume : Measure (EuclideanSpace ℝ (Fin r))) =
      ‖exteriorPower.ιMulti ℝ r w‖ := by
    have hW : ZLattice.covolume (Submodule.span ℤ (Set.range w)) =
        ‖exteriorPower.ιMulti ℝ r w‖ := by
      exact Commons.Lattice.Minkowski.covol_span_wedge r hr w hφv
    have hspan : Submodule.span ℤ (Set.range w) = Submodule.span ℤ (Set.range bb₀) := by
      congr 1
      change Set.range w = Set.range (fun i : Fin r => (bb₀ i : EuclideanSpace ℝ (Fin r)))
      rw [← hwbb]
    simpa [S] using (by
      rw [← hspan]
      exact hW)
  have hN1 : ‖exteriorPower.ιMulti ℝ r w‖ =
      ‖exteriorPower.ιMulti ℝ r (fun i : Fin r => (b i : V))‖ := by
    have hf : ∀ x y : V, inner ℝ (f x) (f y) = inner ℝ x y := by
      intro x y
      simpa [eφ, f] using (φ.inner_map_map x y)
    have hn := norm_iMulti_eq_of_inner_preserving (F := V) (G := EuclideanSpace ℝ (Fin r))
      (f := f) hf r (fun i : Fin r => (b i : V))
    simpa [w, f] using hn
  have hN2 : ‖exteriorPower.ιMulti ℝ r (fun i : Fin r => ((b i : V) : EuclideanSpace ℝ (Fin d)))‖ =
      ‖exteriorPower.ιMulti ℝ r (fun i : Fin r => (b i : V))‖ := by
    have hsub : ∀ x y : V, inner ℝ (V.subtype x) (V.subtype y) = inner ℝ x y := by
      intro x y
      simp
    have hn := norm_iMulti_eq_of_inner_preserving (F := V) (G := EuclideanSpace ℝ (Fin d))
      (f := V.subtype) hsub r (fun i : Fin r => (b i : V))
    simpa using hn
  calc
    ZLattice.covolume L (volume : Measure V) =
        ZLattice.covolume S (volume : Measure (EuclideanSpace ℝ (Fin r))) := hT
    _ = ‖exteriorPower.ιMulti ℝ r w‖ := hS
    _ = ‖exteriorPower.ιMulti ℝ r (fun i : Fin r => (b i : V))‖ := hN1
    _ = ‖exteriorPower.ιMulti ℝ r (fun i : Fin r => ((b i : V) : EuclideanSpace ℝ (Fin d)))‖ :=
      hN2.symm

/-- **The covol-wedge identity, ambient form.**  Let `u : Fin r → E` (`E` the standard
`d`-dimensional Euclidean space) be an `ℝ`-independent family (hence the `ℤ`-span
`W := span ℤ (range u)` is a full-rank lattice in `V := span ℝ (range u)`, `r = dim V`).
The covolume of `W` **inside its own real span `V`** equals the ambient wedge norm of the
generators:

`covol(W;V) = ‖ιMulti ℝ r u‖`. -/
theorem covol_saturated_wedge {d r : ℕ} (hr : 0 < r) (u : Fin r → EuclideanSpace ℝ (Fin d))
    (hu : LinearIndependent ℝ u) :
    ZLattice.covolume (Submodule.span ℤ (Set.range (fun i : Fin r =>
        (⟨u i, Submodule.subset_span (by simp)⟩ : Submodule.span ℝ (Set.range u))))) =
      ‖exteriorPower.ιMulti ℝ r u‖ := by
  classical
  let V : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := Submodule.span ℝ (Set.range u)
  let up : ∀ i : Fin r, u i ∈ V := fun i => Submodule.subset_span (Set.mem_range_self i)
  let uV : Fin r → V := fun i => ⟨u i, up i⟩
  have hmem : (fun i : Fin r => (⟨u i, Submodule.subset_span (by simp)⟩ : V)) = uV := by
    funext i
    apply Subtype.ext
    rfl
  have huV : LinearIndependent ℝ uV := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hcE : (∑ i : Fin r, c i • u i) = 0 := by
      have hc' := congrArg (fun x : V => (V.subtype x)) hc
      simpa [uV] using hc'
    exact (Fintype.linearIndependent_iff.mp hu) c hcE
  have hfin : Module.finrank ℝ V = r := by
    dsimp [V]
    rw [finrank_span_eq_card (R := ℝ) (b := u) hu]
    simp
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range uV) := by
    exact span_top_of_linearIndependent uV huV hfin
  let bV : Basis (Fin r) ℝ V := Module.Basis.mk huV hsp
  have hbV : (fun i : Fin r => (bV i : V)) = uV := Module.Basis.coe_mk huV hsp
  have hmain := covol_wedge_of_submodule_basis (d := d) (r := r) hr V bV
  calc
    ZLattice.covolume (Submodule.span ℤ (Set.range (fun i : Fin r =>
        (⟨u i, Submodule.subset_span (by simp)⟩ : Submodule.span ℝ (Set.range u))))) =
        ZLattice.covolume (Submodule.span ℤ (Set.range bV)) := by
      rw [hmem, ← hbV]
    _ = ‖exteriorPower.ιMulti ℝ r (fun i : Fin r => ((bV i : V) : EuclideanSpace ℝ (Fin d)))‖ :=
      hmain
    _ = ‖exteriorPower.ιMulti ℝ r u‖ := by
      have hfam : (fun i : Fin r => ((bV i : V) : EuclideanSpace ℝ (Fin d))) = u := by
        funext i
        have hbVi : (bV i : V) = uV i := by simpa using congr_fun hbV i
        rw [hbVi]
      rw [hfam]

end SubLatticeCovol
