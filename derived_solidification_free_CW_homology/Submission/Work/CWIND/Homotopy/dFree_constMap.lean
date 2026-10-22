import Mathlib
import Submission.Work.CWIND.Basic

namespace Work.CWIND.Homotopy

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint
open scoped unitInterval

/-! ## The contraction of the standard simplex

This file proves `Work.CWIND.Homotopy.dFree_constMap` (CWIND/T6): for a Hausdorff space `X` and
`n : ℕ` the map `ℤ[X] ⟶ ℤ[X^{Δⁿ}]` induced by the constant map `X ⟶ X^{Δⁿ}` is a solid-equivalence.

The mathematical content here is entirely topological: the compact-open space `X^{Δⁿ}` is homotopy
equivalent to `X`, with forward map the constant map and backward map the evaluation at a chosen
vertex `v` of `Δⁿ`.  The homotopy from `const ≫ eval` to the identity of `X^{Δⁿ}` is induced by a
contraction of the simplex `Δⁿ = StdSimplex ℝ (Fin (n+1))` to its vertex `i`, which is the convex
combination `(s,t) ↦ t • s + (1-t) • eᵢ`.  The general homotopy-invariance statement `hA2` (the
`(b)` part of `CWIND/Homotopy/dFree_homotopy`) then gives the claim.
-/

/-- The standard topological `N`-simplex `Δᴺ`, as a type: it is the underlying type of
`Work.CWIND.Δ N` (definitionally, since `Δ N = ↧(StdSimplex ℝ (Fin (N+1)))`). -/
abbrev Simplex (N : ℕ) : Type := Convexity.StdSimplex ℝ (Fin (N + 1))

/-- `StdSimplex ℝ M` is Hausdorff, since it embeds (continuously and injectively) into `M → ℝ`. -/
theorem t2Space_stdSimplex (M : Type*) : T2Space (Convexity.StdSimplex ℝ M) :=
  T2Space.of_injective_continuous
    (f := fun t : Convexity.StdSimplex ℝ M => fun m => t.weights m)
    (fun _ _ h => Convexity.StdSimplex.ext (Finsupp.ext fun m => congrFun h m))
    (continuous_pi fun m => Convexity.StdSimplex.continuous_weights_apply ℝ m)

/-- The convex combination of `s` with the vertex `i` of `Δᴺ`, of weight `t` on `s` and `1 - t` on
the vertex `i`.  At `t = 1` this is `s`, at `t = 0` it is the vertex `i`. -/
noncomputable def interp (N : ℕ) (i : Fin (N + 1)) (p : Simplex N × unitInterval) : Simplex N where
  weights := (p.2 : ℝ) • p.1.weights + (1 - (p.2 : ℝ)) • (Convexity.StdSimplex.single i).weights
  nonneg := by
    rw [Finsupp.le_def]
    intro j
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    have h0 : (0 : ℝ) ≤ (p.2 : ℝ) := unitInterval.nonneg p.2
    have h1 : (p.2 : ℝ) ≤ 1 := unitInterval.le_one p.2
    have hw : (0 : ℝ) ≤ p.1.weights j := p.1.nonneg j
    have hu : (0 : ℝ) ≤ (Convexity.StdSimplex.single i).weights j :=
      (Convexity.StdSimplex.single i).nonneg j
    nlinarith
  total := by
    rw [Finsupp.sum_fintype _ _ (by intro j; rfl)]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Convexity.StdSimplex.total_of_fintype p.1,
      Convexity.StdSimplex.total_of_fintype (Convexity.StdSimplex.single i)]
    ring

lemma interp_weights (N : ℕ) (i : Fin (N + 1)) (p : Simplex N × unitInterval) :
    (interp N i p).weights =
      (p.2 : ℝ) • p.1.weights + (1 - (p.2 : ℝ)) • (Convexity.StdSimplex.single i).weights := rfl

/-- The contraction at time `0` is the vertex `i`. -/
theorem interp_zero (N : ℕ) (i : Fin (N + 1)) (s : Simplex N) :
    interp N i (s, (0 : unitInterval)) = Convexity.StdSimplex.single i := by
  apply Convexity.StdSimplex.ext
  rw [interp_weights]
  simp

/-- The contraction at time `1` is the identity. -/
theorem interp_one (N : ℕ) (i : Fin (N + 1)) (s : Simplex N) :
    interp N i (s, (1 : unitInterval)) = s := by
  apply Convexity.StdSimplex.ext
  rw [interp_weights]
  simp

/-- The contraction of the simplex to a vertex is continuous. -/
theorem continuous_interp (N : ℕ) (i : Fin (N + 1)) :
    Continuous fun p : Simplex N × unitInterval => interp N i p := by
  rw [Topology.IsEmbedding.continuous_iff
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (N + 1)))]
  refine continuous_pi fun j => ?_
  show Continuous fun p : Simplex N × unitInterval =>
    (((p.2 : ℝ) • p.1.weights + (1 - (p.2 : ℝ)) • (Convexity.StdSimplex.single i).weights :
      Fin (N + 1) →₀ ℝ) j)
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  fun_prop

/-- The contraction of the simplex `Δᴺ` to its `i`-th vertex, as a continuous map. -/
noncomputable def contraction (N : ℕ) (i : Fin (N + 1)) :
    C(Simplex N × unitInterval, Simplex N) :=
  ⟨fun p => interp N i p, continuous_interp N i⟩

@[simp]
lemma contraction_apply (N : ℕ) (i : Fin (N + 1)) (p : Simplex N × unitInterval) :
    contraction N i p = interp N i p := rfl

@[simp]
lemma contraction_zero (N : ℕ) (i : Fin (N + 1)) (s : Simplex N) :
    contraction N i (s, (0 : unitInterval)) = Convexity.StdSimplex.single i :=
  interp_zero N i s

@[simp]
lemma contraction_one (N : ℕ) (i : Fin (N + 1)) (s : Simplex N) :
    contraction N i (s, (1 : unitInterval)) = s :=
  interp_one N i s

/-- **CWIND/T6-aux (continuous family of precompositions).**  For a locally compact space `K`, an
arbitrary space `X` and a continuous map `C : K × [0,1] → K`, the map
`(t, g) ↦ (s ↦ g (C (s,t)))` from `[0,1] × C(K, X)` to `C(K, X)` is continuous. -/
theorem evalCompCurry {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]
    [LocallyCompactSpace K] (C : C(K × unitInterval, K)) :
    ∃ H : C(unitInterval × C(K, X), C(K, X)),
      ∀ (t : unitInterval) (g : C(K, X)) (s : K), H (t, g) s = g (C (s, t)) := by
  refine ⟨ContinuousMap.curry ⟨fun q : (unitInterval × C(K, X)) × K => q.1.2 (C (q.2, q.1.1)),
    ?_⟩, ?_⟩
  · exact continuous_eval.comp
      ((continuous_fst.snd : Continuous fun q : (unitInterval × C(K, X)) × K => q.1.2).prodMk
        (C.continuous.comp (continuous_snd.prodMk continuous_fst.fst)))
  · intro t g s
    rw [ContinuousMap.curry_apply]
    rfl

/-! ## The homotopy equivalence `X ≃ₕ X^{Δⁿ}` -/

/-- The constant map `X ⟶ X^{Δⁿ}` is a homotopy equivalence, with homotopy inverse the evaluation
at a vertex `v` of `Δⁿ` and the homotopy `H` induced by the contraction of the simplex. -/
noncomputable def constMapHomotopyEquiv (X : TopCat.{0}) (n : ℕ) (v : ↥(Δ n))
    (H : C(unitInterval × ↥(singSpace X n), ↥(singSpace X n)))
    (hH0 : ∀ g, H ((0 : unitInterval), g) = ((constMap X n).hom.comp (evalAt X n v).hom) g)
    (hH1 : ∀ g, H ((1 : unitInterval), g) = g) :
    ContinuousMap.HomotopyEquiv ↥X ↥(singSpace X n) where
  toFun := (constMap X n).hom
  invFun := (evalAt X n v).hom
  left_inv := by
    have h : (evalAt X n v).hom.comp (constMap X n).hom = ContinuousMap.id ↥X := by
      ext x
      rfl
    rw [h]
  right_inv := ⟨{ toContinuousMap := H, map_zero_left := hH0, map_one_left := hH1 }⟩

lemma constMapHomotopyEquiv_toFun (X : TopCat.{0}) (n : ℕ) (v : ↥(Δ n))
    (H : C(unitInterval × ↥(singSpace X n), ↥(singSpace X n)))
    (hH0 : ∀ g, H ((0 : unitInterval), g) = ((constMap X n).hom.comp (evalAt X n v).hom) g)
    (hH1 : ∀ g, H ((1 : unitInterval), g) = g) :
    (constMapHomotopyEquiv X n v H hH0 hH1).toFun = (constMap X n).hom := rfl

/-- **CWIND/T6.** For a Hausdorff space `X` and `n : ℕ`, the map `ℤ[X] ⟶ ℤ[X^{Δⁿ}]` induced by the
constant map `X ⟶ X^{Δⁿ}` is a solid-equivalence.  For `n = 0` this is immediate since
`X^{Δ⁰} ≅ X`; for general `n` it is the standard homotopy-invariance statement of REFS/05 section 1:
`X^{Δⁿ}` is Hausdorff, the constant map `X → X^{Δⁿ}` has the evaluation `X^{Δⁿ} → X` as a
retraction, and `const ≫ eval` is homotopic to the identity of the compact-open space `X^{Δⁿ}`
via the contraction of the simplex `Δⁿ`.  The hypothesis `hA2` is the general homotopy-invariance
input (see `CWIND/Homotopy/dFree_homotopy`), supplied separately; the content here is the
topological contraction of the simplex and the reduction to that input. -/
theorem dFree_constMap (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (hA2 : ∀ {Y Z : TopCat.{0}} [T2Space Y] [T2Space Z] (e : ContinuousMap.HomotopyEquiv ↥Y ↥Z),
      SolidEquiv (dFree (TopCat.ofHom e.toFun))) :
    SolidEquiv (dFree (constMap X n)) := by
  let i : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
  let v : ↥(Δ n) := Convexity.StdSimplex.single i
  have : T2Space (Simplex n) := t2Space_stdSimplex (Fin (n + 1))
  have : LocallyCompactSpace (Simplex n) := inferInstance
  obtain ⟨H, hH⟩ := evalCompCurry (K := Simplex n) (X := ↥X) (contraction n i)
  have hH0 : ∀ g : ↥(singSpace X n),
      H ((0 : unitInterval), g) = ((constMap X n).hom.comp (evalAt X n v).hom) g := by
    intro g
    apply ContinuousMap.ext
    intro s
    rw [hH (0 : unitInterval) g s]
    show g ((contraction n i) (s, (0 : unitInterval))) = g v
    rw [contraction_zero]
  have hH1 : ∀ g : ↥(singSpace X n), H ((1 : unitInterval), g) = g := by
    intro g
    apply ContinuousMap.ext
    intro s
    rw [hH (1 : unitInterval) g s]
    show g ((contraction n i) (s, (1 : unitInterval))) = g s
    rw [contraction_one]
  have hmain := hA2 (constMapHomotopyEquiv X n v H hH0 hH1)
  have h : TopCat.ofHom (constMapHomotopyEquiv X n v H hH0 hH1).toFun = constMap X n := by
    rw [constMapHomotopyEquiv_toFun]
    apply TopCat.ext
    intro x
    rfl
  rwa [h] at hmain

end Work.CWIND.Homotopy
