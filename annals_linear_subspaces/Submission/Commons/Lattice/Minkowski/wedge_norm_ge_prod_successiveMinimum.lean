import Mathlib
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Lattice.SuccessiveMinima.sublattice_ge
import Submission.Commons.Lattice.Minkowski.minkowski_second_upper
import Submission.Commons.Analysis.InnerProductSpace.covol_span_wedge_gen

/-!
# Lower half of Mahler's equivalence: wedge norm vs. product of successive minima

For a `ℤ`-lattice `L ≤ E` (`E` a finite-dimensional real inner product space) and a
`ℤ`-linearly independent family `w : Fin k → L`, the norm of the `k`-fold wedge of `w` is
bounded below by the product of the first `k` Euclidean successive minima of `L`, up to a
constant depending only on `k`:

`C(k) · ∏ᵢ λᵢ(L) ≤ ‖w₁ ∧ … ∧ w_k‖`.

Proof route (all ingredients are in the shared commons):

* `W := span ℤ (range (w i : E)) ≤ L` and `λᵢ(L) ≤ λᵢ(W)` (a family of `i` independent
  elements of `W` is one of `L`);
* `V := span ℝ (range w)`, of dimension `k` (`w` is `ℤ`-independent in a lattice, hence
  `ℝ`-independent), and `W` is the image of the full-rank lattice
  `W_V := span ℤ (range b)` for the `ℝ`-basis `b := Basis.mk …` of `V`, so the successive
  minima agree (`successiveMinimum_eq_of_carrier_eq`);
* Minkowski's second theorem (upper bound, `minkowski_second_upper`) applied to `W_V`
  inside `V` gives `∏ᵢ λᵢ(W_V) · vol(B_V) ≤ 2^{2k} covol(W_V)`;
* the covolume of `W_V` inside `V` is the ambient wedge norm
  (`covol_span_basis_eq_wedge`, from `covol_span_wedge_gen`).

-/

noncomputable section

open MeasureTheory Metric Module
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Commons.Lattice.Minkowski

/-- A (not necessarily surjective) `ℝ`-linear map preserving inner products preserves the
norms of decomposable exterior powers. -/
private lemma norm_iMulti_eq_of_inner_preserving {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (f : F →ₗ[ℝ] G) (hf : ∀ x y : F, inner ℝ (f x) (f y) = inner ℝ x y) (n : ℕ)
    (v : Fin n → F) :
    ‖exteriorPower.ιMulti ℝ n (fun i => f (v i))‖ = ‖exteriorPower.ιMulti ℝ n v‖ := by
  have hsq : (‖exteriorPower.ιMulti ℝ n (fun i => f (v i))‖ : ℝ) ^ 2 =
      ‖exteriorPower.ιMulti ℝ n v‖ ^ 2 := by
    calc
      (‖exteriorPower.ιMulti ℝ n (fun i => f (v i))‖ : ℝ) ^ 2 =
          inner ℝ (exteriorPower.ιMulti ℝ n (fun i => f (v i)))
            (exteriorPower.ιMulti ℝ n (fun i => f (v i))) := by simp
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
      _ = ‖exteriorPower.ιMulti ℝ n v‖ ^ 2 := by simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have h1 : 0 ≤ ‖exteriorPower.ιMulti ℝ n (fun i => f (v i))‖ := norm_nonneg _
    have h2 : 0 ≤ ‖exteriorPower.ιMulti ℝ n v‖ := norm_nonneg _
    nlinarith

/-- An independent family of `finrank`-many vectors spans the whole space. -/
private lemma span_top_of_li_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {r : ℕ} (v : Fin r → E) (hv : LinearIndependent ℝ v)
    (hfin : Module.finrank ℝ E = r) : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
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
  have hsub : Subsingleton (E ⧸ S) := (Module.finrank_zero_iff (R := ℝ) (M := E ⧸ S)).mp hq0
  intro x _
  have hz : (S.mkQ x : E ⧸ S) = 0 := Subsingleton.elim _ _
  have hmem : x ∈ S := by
    have hz0 : (Submodule.Quotient.mk x : E ⧸ S) = 0 := by simpa [Submodule.mkQ_apply] using hz
    exact (Submodule.Quotient.mk_eq_zero (p := S)).1 hz0
  simpa [S] using hmem

/-- A `ℤ`-linearly independent family in a full `ℤ`-lattice is `ℝ`-linearly independent
(coordinates in a `ℤ`-basis are integer vectors, and integer vectors that are independent
over `ℤ` stay independent over `ℝ`). -/
private lemma li_real_of_int_lattice {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} (w : ι → L) (hw : LinearIndependent ℤ w) :
    LinearIndependent ℝ (fun i => (w i : E)) := by
  classical
  haveI : Module.Finite ℤ L := inferInstance
  haveI : Module.Free ℤ L := inferInstance
  let n := Module.finrank ℤ L
  let b : Module.Basis (Fin n) ℤ L := Module.finBasis ℤ L
  let c : ι → (Fin n → ℤ) := fun i j => b.repr (w i) j
  have hc₀ : LinearIndependent ℤ
      (fun i => Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n) (b.repr (w i))) := by
    have h1 : LinearIndependent ℤ (fun i => b.repr (w i)) :=
      hw.map' b.repr.toLinearMap (LinearMap.ker_eq_bot.mpr b.repr.injective)
    exact h1.map' (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).toLinearMap
      (LinearMap.ker_eq_bot.mpr (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).injective)
  have hc : LinearIndependent ℤ c := by
    convert hc₀ using 1
    ext i j
    rfl
  have hcR : LinearIndependent ℝ (fun i => algebraMap ℤ ℝ ∘ c i) := by
    rw [linearIndependent_algebraMap_comp_iff]
    exact hc
  let bE : Module.Basis (Fin n) ℝ E := b.ofZLatticeBasis ℝ L
  have hrepr : ∀ i j, bE.repr (w i : E) j = algebraMap ℤ ℝ (c i j) := by
    intro i j
    rw [Module.Basis.ofZLatticeBasis_repr_apply]
    rfl
  have hE : LinearIndependent ℝ (fun i => fun j => bE.repr (w i : E) j) := by
    convert hcR using 1
    ext i j
    rw [hrepr i j]
    rfl
  have hfin := LinearIndependent.of_comp
    (((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin n)).toLinearMap).comp bE.repr.toLinearMap) hE
  convert hfin using 1

/-- Successive minima are unchanged when a `ℤ`-lattice in a subspace is transported to the
ambient space along the inclusion: if `W'` is the image of `W` under `V ↪ E`, then the
defining sets of `λᵢ` coincide. -/
private lemma successiveMinimum_eq_of_carrier_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : Submodule ℝ E} (W : Submodule ℤ V)
    (W' : Submodule ℤ E) (h : W' = W.map (V.subtype.restrictScalars ℤ)) (i : ℕ) :
    Commons.Lattice.SuccessiveMinima.successiveMinimum (E := V) W i =
      Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) W' i := by
  unfold Commons.Lattice.SuccessiveMinima.successiveMinimum
  congr 1
  ext r
  constructor
  · rintro ⟨hr, f, hlin, hnorm⟩
    refine ⟨hr, (fun a => (⟨((f a : V) : E), ?_⟩ : W')), ?_, ?_⟩
    · rw [h]
      exact Submodule.mem_map.mpr ⟨f a, (f a).2, rfl⟩
    · have hmap : LinearIndependent ℤ (fun a : Fin i => ((f a : V) : E)) :=
        hlin.map' (V.subtype.restrictScalars ℤ)
          (LinearMap.ker_eq_bot.mpr (fun x y hxy => V.injective_subtype hxy))
      exact hmap
    · intro a
      exact hnorm a
  · rintro ⟨hr, f, hlin, hnorm⟩
    choose y hy hxy using fun a => Submodule.mem_map.mp (by rw [← h]; exact (f a).2)
    refine ⟨hr, (fun a => (⟨y a, hy a⟩ : W)), ?_, ?_⟩
    · have h2 : LinearIndependent ℤ (fun a : Fin i => (f a : E)) := hlin
      have h3 : (fun a : Fin i => ((y a : V) : E)) = (fun a : Fin i => (f a : E)) :=
        funext (fun a => hxy a)
      rw [← h3] at h2
      have h4 : LinearIndependent ℤ (fun a : Fin i => (y a : V)) :=
        LinearIndependent.of_comp (V.subtype.restrictScalars ℤ) h2
      exact h4
    · intro a
      have key : ‖(y a : V)‖ = ‖(f a : E)‖ := congrArg norm (hxy a)
      change ‖(y a : V)‖ ≤ r
      rw [key]
      exact hnorm a

/-- The covolume (inside `V`) of the `ℤ`-span of a basis `b` of a subspace `V ≤ E` equals
the ambient norm of the top wedge of `b`. -/
private lemma covolume_span_basis_eq_wedge {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {r : ℕ} (V : Submodule ℝ E)
    [MeasurableSpace V] [BorelSpace V] (b : Module.Basis (Fin r) ℝ V) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) =
      ‖exteriorPower.ιMulti ℝ r (fun i => (b i : E))‖ := by
  have h1 := Commons.Analysis.InnerProductSpace.covol_span_wedge_gen (E := V) (k := r) b
  have h2 := norm_iMulti_eq_of_inner_preserving (F := V) (G := E) (f := V.subtype)
    (fun x y => by simp) r b
  rw [h1, ← h2]
  rfl

/-- The `0`-fold wedge product has norm one. -/
private lemma norm_iMulti_zero {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (u : Fin 0 → F) : ‖exteriorPower.ιMulti ℝ 0 u‖ = 1 := by
  have hsq : ‖exteriorPower.ιMulti ℝ 0 u‖ ^ 2 = 1 := by
    calc
      ‖exteriorPower.ιMulti ℝ 0 u‖ ^ 2 =
          inner ℝ (exteriorPower.ιMulti ℝ 0 u) (exteriorPower.ιMulti ℝ 0 u) := by
        exact (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (exteriorPower.ιMulti ℝ 0 u)).symm
      _ = (Matrix.gram ℝ u).det := by rw [exteriorPower.inner_ιMulti_self]
      _ = (1 : Matrix (Fin 0) (Fin 0) ℝ).det := by
        congr 1
        exact Subsingleton.elim _ _
      _ = 1 := by simp
  have hnn : 0 ≤ ‖exteriorPower.ιMulti ℝ 0 u‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖exteriorPower.ιMulti ℝ 0 u‖)]

/-- **Wedge lower bound (the lower half of Mahler's equivalence; no reduction theory needed).**
For a `ℤ`-lattice `L ≤ E` and a `ℤ`-linearly independent family `w : Fin k → L`, the norm of the
`k`-fold wedge of `w` is bounded below by the product of the first `k` (Euclidean) successive
minima of `L`, up to a constant depending only on `k`.

PROOF ROUTE (all pieces already in the commons). Let `W := span_ℤ (range w)`, a rank-`k`
sublattice of `L` on which `w` is a `ℤ`-basis, so `covol(W)` (computed inside `span_ℝ W`) equals
`‖⋀ᵢ wᵢ‖` — this is a "covolume of a span = wedge norm" statement
(`Commons.Lattice.Minkowski.covol_span_wedge`, or the `SubLatticeCovol` /
`GraysonEndpoints.latticeCovol_eq_covolume_of_span_top` transport on disk in `Submission/Work`).
Then apply Minkowski's second (upper) bound `Commons.Lattice.Minkowski.minkowski_second_upper` to
`W` **inside `span_ℝ W`**: transport along a linear-isometry equivalence
`span_ℝ W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)` (so that the `IsZLattice` hypothesis is available);
successive minima and covolume are preserved by isometries
(`Commons.Lattice.Minkowski.covolume_image_isometry`,
`Commons.Lattice.SuccessiveMinima.isometry_image_eq`).  This gives
`∏_{i ≤ k} λᵢ(W) ≤ 2^(2k) · covol(W) / vol(closedBall 0 1 : ℝᵏ)`, i.e.
`covol(W) ≥ c(k) · ∏_{i ≤ k} λᵢ(W)`.  Finally `W ≤ L` gives `λᵢ(L) ≤ λᵢ(W)` (a family of `i`
independent elements of `W` is one of `L`; cf.
`Commons.Lattice.SuccessiveMinima.successiveMinimum_sublattice_ge`), so
`∏_{i ≤ k} λᵢ(L) ≤ C(k) · ‖⋀ᵢ wᵢ‖`.

This replaces the "Mahler" input of de Saxcé's Corollary 1 (lattices 1132-1165 of the paper text):
the case `k = d` is `minkowski_second_upper` itself. -/
theorem wedge_norm_ge_prod_successiveMinimum {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (w : Fin k → L) (hw : LinearIndependent ℤ w) :
    ∃ C : ℝ, 0 < C ∧
      C * (∏ i : Fin k, Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) L (i.val + 1))
        ≤ ‖exteriorPower.ιMulti ℝ k (fun i => (w i : E))‖ := by
  classical
  set v : Fin k → E := fun i => (w i : E) with hv
  have hvli : LinearIndependent ℝ v := li_real_of_int_lattice L w hw
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- the empty family: the product is `1` and the `0`-fold wedge has norm `1`
    subst hk0
    refine ⟨1, one_pos, ?_⟩
    have hprod : (∏ i : Fin 0,
        Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) L (i.val + 1)) = 1 := by
      simp
    rw [hprod, one_mul]
    exact le_of_eq (norm_iMulti_zero v).symm
  · -- main case `k > 0`
    let V : Submodule ℝ E := Submodule.span ℝ (Set.range v)
    let vV : Fin k → V := fun i => ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
    have hvV : LinearIndependent ℝ vV := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hcE : (∑ i : Fin k, c i • v i) = 0 := by
        have hc' := congrArg (fun x : V => (x : E)) hc
        simpa [vV] using hc'
      exact (Fintype.linearIndependent_iff.mp hvli) c hcE
    have hfinV : Module.finrank ℝ V = k := by
      dsimp [V]
      rw [finrank_span_eq_card (R := ℝ) (b := v) hvli]
      simp
    have hspV : ⊤ ≤ Submodule.span ℝ (Set.range vV) := span_top_of_li_gen vV hvV hfinV
    let b : Module.Basis (Fin k) ℝ V := Module.Basis.mk hvV hspV
    have hbcoe : ∀ i, ((b i : V) : E) = v i := by
      intro i
      have h := congr_fun (Module.Basis.coe_mk hvV hspV) i
      exact congrArg (fun x : V => (x : E)) h
    let W : Submodule ℤ V := Submodule.span ℤ (Set.range b)
    haveI : DiscreteTopology W := by dsimp only [W]; infer_instance
    haveI : IsZLattice ℝ W := by dsimp only [W]; infer_instance
    haveI : Nontrivial V := by
      rw [← Module.finrank_pos_iff (R := ℝ) (M := V), hfinV]
      exact hk
    letI : MeasurableSpace V := borel V
    haveI : BorelSpace V := ⟨rfl⟩
    have hkL : k ≤ Module.finrank ℤ L := by
      have h1 : Module.finrank ℝ V ≤ Module.finrank ℝ E := Submodule.finrank_le V
      have h2 : Module.finrank ℤ L = Module.finrank ℝ E := ZLattice.rank ℝ L
      omega
    -- Minkowski's second theorem (upper bound) for `W` inside `V`
    have hmin : (∏ i : Fin k,
          Commons.Lattice.SuccessiveMinima.successiveMinimum (E := V) W (i.val + 1)) *
          ENNReal.toReal (volume (Metric.closedBall (0 : V) 1)) ≤
        (2 : ℝ) ^ (2 * k) * ZLattice.covolume W := by
      refine minkowski_second_upper (d := k) hk (E := V) (L := W) ?_
      rw [ZLattice.rank ℝ W]
      exact hfinV
    -- the covolume of `W` inside `V` is the ambient wedge norm of `w`
    have hcov : ZLattice.covolume W = ‖exteriorPower.ιMulti ℝ k v‖ := by
      have h := covolume_span_basis_eq_wedge (E := E) V b
      have hfam : (fun i => ((b i : V) : E)) = v := funext (fun i => hbcoe i)
      simpa [W, hfam] using h
    -- the lattice `W` inside `V` is the image of `span ℤ (range w)`
    let WE : Submodule ℤ E := Submodule.span ℤ (Set.range v)
    have hWE_le : WE ≤ L := by
      rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact (w i).2
    have hmap : WE = W.map (V.subtype.restrictScalars ℤ) := by
      dsimp only [WE, W]
      rw [Submodule.map_span]
      congr 1
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨b i, ⟨i, rfl⟩, by simpa using (hbcoe i)⟩
      · rintro ⟨y, ⟨i, rfl⟩, hxy⟩
        exact ⟨i, (hbcoe i).symm.trans hxy⟩
    -- `λᵢ(L) ≤ λᵢ(W_V)` for `i ≤ k`
    have hlam : ∀ j : Fin k, Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) L
        (j.val + 1) ≤
        Commons.Lattice.SuccessiveMinima.successiveMinimum (E := V) W (j.val + 1) := by
      intro j
      have hjk : j.val + 1 ≤ k := by omega
      have hnonempty : (Commons.Lattice.SuccessiveMinima.successiveMinimumSet WE
          (j.val + 1)).Nonempty := by
        have hvint : LinearIndependent ℤ v :=
          hw.map' (L.subtype) (LinearMap.ker_eq_bot.mpr (fun x y hxy => L.injective_subtype hxy))
        refine Commons.Lattice.SuccessiveMinima.successiveMinimumSet_nonempty_of_exists_linearIndependent
          WE (j.val + 1) (fun a => ⟨v (Fin.castLEEmb hjk a),
            Submodule.subset_span (Set.mem_range_self _)⟩)
          (hvint.comp (Fin.castLEEmb hjk) (Fin.castLEEmb hjk).injective)
          (∑ a : Fin (j.val + 1), ‖v (Fin.castLEEmb hjk a)‖) ?_ ?_
        · intro a
          exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin (j.val + 1))))
            (f := fun b : Fin (j.val + 1) => ‖v (Fin.castLEEmb hjk b)‖)
            (fun b _ => norm_nonneg _) (Finset.mem_univ a)
        · exact Finset.sum_nonneg (fun b (_ : b ∈ (Finset.univ : Finset (Fin (j.val + 1)))) =>
            norm_nonneg _)
      have h1 : Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) L (j.val + 1) ≤
          Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) WE (j.val + 1) :=
        Commons.Lattice.SuccessiveMinima.sublattice_ge WE L hWE_le (j.val + 1) hnonempty
      have h2 : Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) WE (j.val + 1) =
          Commons.Lattice.SuccessiveMinima.successiveMinimum (E := V) W (j.val + 1) :=
        (successiveMinimum_eq_of_carrier_eq W WE hmap (j.val + 1)).symm
      linarith
    -- product comparison
    have hprod : (∏ j : Fin k,
          Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) L (j.val + 1)) ≤
        (∏ j : Fin k,
          Commons.Lattice.SuccessiveMinima.successiveMinimum (E := V) W (j.val + 1)) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro j _
        exact Commons.Lattice.SuccessiveMinima.successiveMinimum_nonneg L (j.val + 1)
          (by have := j.isLt; omega)
      · intro j _
        exact hlam j
    -- volume positivity
    have hvolpos : 0 < ENNReal.toReal (volume (Metric.closedBall (0 : V) 1)) := by
      refine ENNReal.toReal_pos ?_ ?_
      · exact (Metric.measure_closedBall_pos volume (0 : V) (by norm_num)).ne'
      · exact (MeasureTheory.measure_closedBall_lt_top (μ := volume)).ne
    have h2k : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := by positivity
    refine ⟨ENNReal.toReal (volume (Metric.closedBall (0 : V) 1)) / (2 : ℝ) ^ (2 * k),
      by positivity, ?_⟩
    rw [div_mul_eq_mul_div, div_le_iff₀ h2k]
    rw [hcov] at hmin
    have h1 : ENNReal.toReal (volume (Metric.closedBall (0 : V) 1)) *
        (∏ j : Fin k, Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) L (j.val + 1))
        ≤ ENNReal.toReal (volume (Metric.closedBall (0 : V) 1)) *
        (∏ j : Fin k, Commons.Lattice.SuccessiveMinima.successiveMinimum (E := V) W (j.val + 1)) :=
      mul_le_mul_of_nonneg_left hprod (le_of_lt hvolpos)
    have h2 : ENNReal.toReal (volume (Metric.closedBall (0 : V) 1)) *
        (∏ j : Fin k, Commons.Lattice.SuccessiveMinima.successiveMinimum (E := V) W (j.val + 1))
        = (∏ j : Fin k, Commons.Lattice.SuccessiveMinima.successiveMinimum (E := V) W (j.val + 1)) *
        ENNReal.toReal (volume (Metric.closedBall (0 : V) 1)) := by ring
    nlinarith [h1, h2, hmin]

end Commons.Lattice.Minkowski
