import Mathlib
import Submission.Blueprint.Interfaces

/-!
# AREA SINGMV — small simplices: definitions

This file lays down the definitions for the Mayer–Vietoris theorem for singular chains
("small simplices", Hatcher Proposition 2.21), in the form required by
`Submission.Blueprint.SingMVProp`:

for open `U, V ⊆ X` with `U ∪ V = X`, the canonical map
`pushout (C(U∩V) → C(U)) (C(U∩V) → C(V)) ⟶ C(X)` is a quasi-isomorphism.

The proof proceeds by barycentric subdivision:
* `Sd n` is the barycentric subdivision of the fundamental `n`-simplex, as a chain of the
  singular chain complex of the standard topological `n`-simplex;
* `sddeg X n` is the degreewise subdivision operator on the singular chains of `X`, defined on a
  singular simplex `σ` by pushing `Sd n` forward along `σ`;
* the *mesh* of `Sd n` shrinks under iteration, which yields the Lebesgue-number argument
  ("every chain becomes small after enough subdivisions").

## Conventions

* `tSplx n` is the standard topological `n`-simplex, in the model used by `TopCat.toSSet`.
* `singMap X n` is the type of singular `n`-simplices of `X`, i.e. continuous maps
  `Δⁿ ⟶ X`; `singEquiv X n` identifies the `n`-simplices of the singular simplicial set with
  this type.
* `gen X n σ` is the generator of the singular chain group `C_n(X)` corresponding to `σ`.
* `toE t` is the point of `Δⁿ` given by a probability distribution, as a vector in `ℝ^{n+1}`;
  all metric estimates are performed in this ambient space with the sup metric.
-/

open CategoryTheory Limits Convexity
open scoped BigOperators Simplicial

noncomputable section

namespace Work.SingMV

/-! ## The standard simplex and singular chains -/

/-- The standard topological `n`-simplex, in the model used by `TopCat.toSSet`. Its underlying
type is `StdSimplex ℝ (Fin (n+1))`, the type of probability distributions on `{0, …, n}`. -/
abbrev tSplx (n : ℕ) : TopCat := SimplexCategory.toTop₀.obj (SimplexCategory.mk n)

/-- The singular `n`-simplices of `X`, as continuous maps `Δⁿ ⟶ X`. -/
abbrev singMap (X : TopCat) (n : ℕ) : Type := C(StdSimplex ℝ (Fin (n+1)), X)

/-- The `n`-simplices of the singular simplicial set of `X`, identified with the continuous
maps `Δⁿ ⟶ X`. -/
def singEquiv (X : TopCat) (n : ℕ) :
    (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) ≃ singMap X n :=
  TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))

/-- The generator of the singular chain group `C_n(X)` corresponding to a singular `n`-simplex
`σ : Δⁿ ⟶ X`. -/
def gen (X : TopCat) (n : ℕ) (σ : singMap X n) : ((Submission.Blueprint.singC).obj X).X n :=
  (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) ((singEquiv X n).symm σ) (1 : ℤ)

/-! ## The geometry of the standard simplex -/

/-- A point of the standard `n`-simplex, as a vector in `ℝ^{n+1}` (its tuple of weights). -/
def toE {m : ℕ} (t : StdSimplex ℝ (Fin m)) : Fin m → ℝ := fun i => t.weights i

/-- The uniform probability distribution on a nonempty finite set of vertices
(the barycenter of a finite subset). This is Mathlib's `StdSimplex.subBarycenter`. -/
noncomputable abbrev unif {m : ℕ} (A : Finset (Fin m)) (hA : A.Nonempty) : StdSimplex ℝ (Fin m) :=
  StdSimplex.subBarycenter A hA

/-- The vertices of the standard `n`-simplex, as points. -/
def vert (m : ℕ) (i : Fin m) : StdSimplex ℝ (Fin m) := StdSimplex.single i

/-- Weights of a convex combination of points of the standard simplex, in coordinates. -/
lemma weights_iConvexComb_apply {I J : Type*} [Fintype I] (w : StdSimplex ℝ I)
    (f : I → StdSimplex ℝ J) (j : J) :
    (Convexity.iConvexComb w f).weights j = ∑ i, w.weights i * (f i).weights j := by
  rw [Convexity.iConvexComb, StdSimplex.weights_sConvexComb,
    StdSimplex.weights_map, Finsupp.mapDomain_fintype]
  rw [Finsupp.sum_finsetSum _ _ _ (by intro a; simp) (by intro a m₁ m₂; simp [add_smul])]
  simp

/-- The affine map `Δ^k ⟶ Δ^n` with prescribed vertices is continuous. -/
lemma continuous_affineMapMk {k n : ℕ} (p : Fin (k+1) → StdSimplex ℝ (Fin (n+1))) :
    Continuous (StdSimplex.affineMapMk (R := ℝ) p) := by
  let e : StdSimplex ℝ (Fin (n+1)) → (Fin (n+1) → ℝ) := fun t => ⇑t.weights
  have he : Topology.IsInducing e :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).toIsInducing
  rw [Topology.IsInducing.continuous_iff he]
  have h : (e ∘ StdSimplex.affineMapMk (R := ℝ) p) =
      fun t => fun j => ∑ i, t.weights i * (p i).weights j := by
    funext t j
    show (StdSimplex.affineMapMk (R := ℝ) p t).weights j = _
    rw [StdSimplex.affineMapMk_apply]
    exact weights_iConvexComb_apply t p j
  rw [h]
  fun_prop

/-- The (bundled) affine map `Δ^k ⟶ Δ^n` whose `i`-th vertex is `p i`. -/
def affineSimplex {k n : ℕ} (p : Fin (k+1) → StdSimplex ℝ (Fin (n+1))) :
    C(StdSimplex ℝ (Fin (k+1)), StdSimplex ℝ (Fin (n+1))) :=
  ⟨StdSimplex.affineMapMk (R := ℝ) p, continuous_affineMapMk p⟩

/-- The `i`-th coface inclusion `Δ^n ⟶ Δ^{n+1}` (the face opposite the `i`-th vertex). -/
def coface (n : ℕ) (i : Fin (n+2)) : tSplx n ⟶ tSplx (n+1) :=
  SimplexCategory.toTop₀.map (SimplexCategory.δ i)

/-! ## The barycentric subdivision chain -/

/-- The cone over a chain of the singular chain complex of `Δ^n`, with apex `b ∈ Δ^n`: a `k`-simplex
`γ` is sent to the `(k+1)`-simplex whose vertices are those of `γ` followed by `b`. -/
def coneChain (n : ℕ) (b : StdSimplex ℝ (Fin (n+1))) (k : ℕ) :
    ((Submission.Blueprint.singC).obj (tSplx n)).X k ⟶
      ((Submission.Blueprint.singC).obj (tSplx n)).X (k+1) :=
  Cofan.IsColimit.desc
    ((TopCat.toSSet.obj (tSplx n)).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) k)
    (fun γ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
      (gen (tSplx n) (k+1) (affineSimplex (n := n) (k := k+1) (Fin.snoc
        (fun i : Fin (k+1) => (singEquiv (tSplx n) k) γ (vert (k+1) i)) b)))))

/-- The subdivision of the boundary of `Δ^{n+1}`, pushed forward to the `n`-chains of `Δ^{n+1}`:
`Σᵢ (-1)ⁱ (δᵢ)∗ (Sd n)`. -/
def SdBdry (n : ℕ) (s : ((Submission.Blueprint.singC).obj (tSplx n)).X n) :
    ((Submission.Blueprint.singC).obj (tSplx (n+1))).X n :=
  ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) •
    (((Submission.Blueprint.singC).map (coface n i)).f n s)

/-- The barycentric subdivision of the fundamental `n`-simplex `Δ^n`, as an `n`-chain of the
singular chain complex of `Δ^n`.

It is defined recursively by
`Sd (n+1) = (-1)^{n+1} • cone (∂ Sd n)`, where `∂ Sd n = Σᵢ (-1)ⁱ (δᵢ)∗ (Sd n)` is the
subdivision of the boundary. -/
def Sd : (n : ℕ) → ((Submission.Blueprint.singC).obj (tSplx n)).X n :=
  Nat.rec (motive := fun n => ((Submission.Blueprint.singC).obj (tSplx n)).X n)
    (gen (tSplx 0) 0 (ContinuousMap.id _))
    (fun n s => (-1 : ℤ) ^ (n+1) • coneChain (n+1)
      (unif (Finset.univ : Finset (Fin (n+2))) Finset.univ_nonempty) n (SdBdry n s))

/-- The degreewise barycentric subdivision operator on the singular chain complex of `X`:
on a generator `σ` it is the pushforward of the subdivision of the fundamental simplex along `σ`.
This is only the degreewise map; that it is a chain map is proven separately. -/
def sddeg (X : TopCat) (n : ℕ) :
    ((Submission.Blueprint.singC).obj X).X n ⟶ ((Submission.Blueprint.singC).obj X).X n :=
  Cofan.IsColimit.desc
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
      (((Submission.Blueprint.singC).map
        (TopCat.ofHom ((singEquiv X n) σ))).f n (Sd n))))

/-! ## Small chains -/

/-- The submodule of `C_n(X)` generated by the singular `n`-simplices whose image lies in `U`. -/
def smallSpan (X : TopCat) (n : ℕ) (U : Set X) : Submodule ℤ
    ↥(((Submission.Blueprint.singC).obj X).X n) :=
  Submodule.span ℤ (Set.range (fun σ : {σ : singMap X n // ∀ x, σ x ∈ U} => gen X n σ.1))

/-- The submodule of `C_n(X)` generated by the `(U,V)`-small simplices. -/
def smallChain (X : TopCat) (n : ℕ) (U V : Set X) : Submodule ℤ
    ↥(((Submission.Blueprint.singC).obj X).X n) :=
  smallSpan X n U ⊔ smallSpan X n V

/-! ## The coface sum, the boundary chain, and the mesh of a subdivision -/

/-- The alternating sum of the pushforwards along the coface inclusions,
`Φ n = Σᵢ (-1)ⁱ (δᵢ)∗ : C(Δⁿ) ⟶ C(Δⁿ⁺¹)`, as a chain map. -/
def phi (n : ℕ) : ((Submission.Blueprint.singC).obj (tSplx n)) ⟶
    ((Submission.Blueprint.singC).obj (tSplx (n+1))) :=
  ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) • ((Submission.Blueprint.singC).map (coface n i))

/-- The subdivision of the boundary of `Δⁿ⁺¹`, as a chain of `C(Δⁿ⁺¹)` in degree `n`. -/
def Bdry (n : ℕ) : ((Submission.Blueprint.singC).obj (tSplx (n+1))).X n :=
  (phi n).f n (Sd n)

/-- `VClose q d` means that the points of the vertex tuple `q` are pairwise at distance at most
`d` in the ambient space `ℝ^N` (with the sup metric). -/
def VClose {m N : ℕ} (q : Fin m → StdSimplex ℝ (Fin N)) (d : ℝ) : Prop :=
  ∀ i j, dist (toE (q i)) (toE (q j)) ≤ d

/-- The vertex tuples occurring in one barycentric subdivision step: the `i`-th vertex is the
barycenter of a nonempty subset `A i` of the vertices, and the family `A` is increasing. -/
def SubdivTup (n : ℕ) : Set (Fin (n+1) → StdSimplex ℝ (Fin (n+1))) :=
  {q | ∃ (A : Fin (n+1) → Finset (Fin (n+1))) (hA : ∀ i, (A i).Nonempty),
      (∀ i j, i ≤ j → A i ⊆ A j) ∧ q = fun i => StdSimplex.subBarycenter (A i) (hA i)}

/-- The submodule of `C_k(Δⁿ)` generated by the affine simplices `Δᵏ ⟶ Δⁿ` whose vertex tuple
is `d`-close. -/
def meshSpan (n k : ℕ) (d : ℝ) : Submodule ℤ
    (((Submission.Blueprint.singC).obj (tSplx n)).X k) :=
  Submodule.span ℤ (Set.range (fun q : {q : Fin (k+1) → StdSimplex ℝ (Fin (n+1)) // VClose q d} =>
    gen (tSplx n) k (affineSimplex q.1)))

/-- The `k`-fold subdivision of the fundamental `n`-simplex `Δⁿ`, as a chain in `C_n(Δⁿ)`. -/
def sdIter (n k : ℕ) : ((Submission.Blueprint.singC).obj (tSplx n)).X n :=
  (sddeg (tSplx n) n)^[k] (Sd n)

/-- The submodule of `C_k(Δⁿ)` generated by the affine simplices (those given by `affineSimplex`),
i.e. by the simplices that are themselves affine maps `Δᵏ ⟶ Δⁿ`. -/
def affineSpan (n k : ℕ) : Submodule ℤ (((Submission.Blueprint.singC).obj (tSplx n)).X k) :=
  Submodule.span ℤ (Set.range (fun q : Fin (k+1) → StdSimplex ℝ (Fin (n+1)) =>
    gen (tSplx n) k (affineSimplex q)))

/-- The alternating sum of the pushforwards along the cofaces, applied in a fixed degree:
`Σᵢ (-1)ⁱ (δᵢ)∗`. Equivalently the `k`-th component of `phi n`. -/
def phiF (n k : ℕ) (z : ((Submission.Blueprint.singC).obj (tSplx n)).X k) :
    ((Submission.Blueprint.singC).obj (tSplx (n+1))).X k :=
  (phi n).f k z

/-- The chain `H n ∈ C_{n+1}(Δⁿ)` witnessing the chain homotopy between the barycentric
subdivision `Sd` and the identity on the fundamental simplex. It is defined recursively by
coning the cycle `Sd (n+1) - id - Σᵢ (-1)ⁱ (δᵢ)∗ H n` with apex the barycenter of `Δ^{n+1}`;
the coning formula `∂(cone z) = cone(∂z) + (-1)^{k+2} z` then gives `∂ H (n+1) + D = Sd (n+1) - id`
as soon as the coned cycle has vanishing boundary. -/
def homChain : (n : ℕ) → ((Submission.Blueprint.singC).obj (tSplx n)).X (n+1) :=
  Nat.rec (motive := fun n => ((Submission.Blueprint.singC).obj (tSplx n)).X (n+1)) 0
    (fun n h => (-1 : ℤ) ^ (n+2) • coneChain (n+1)
      (unif (Finset.univ : Finset (Fin (n+2))) Finset.univ_nonempty) (n+1)
      (Sd (n+1) - gen (tSplx (n+1)) (n+1) (ContinuousMap.id _) - phiF n (n+1) h))

/-- The degreewise chain homotopy operator induced by `homChain`: on a generator `σ` it is the
pushforward of `H n` along `σ`. -/
def homdeg (X : TopCat) (n : ℕ) :
    ((Submission.Blueprint.singC).obj X).X n ⟶ ((Submission.Blueprint.singC).obj X).X (n+1) :=
  Cofan.IsColimit.desc
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
      (((Submission.Blueprint.singC).map
        (TopCat.ofHom ((singEquiv X n) σ))).f (n+1) (homChain n))))

/-- The canonical map of chain complexes from the pushout of `C(U∩V) → C(U)`, `C(U∩V) → C(V)`
to `C(X)`, where `C = singC` is the integral singular chain complex. This is the map which is
shown to be a quasi-isomorphism for open `U, V` covering `X` (Hatcher, Proposition 2.21). -/
noncomputable def pushoutMap (X : TopCat) (U V : Set X) :
    CategoryTheory.Limits.pushout
        ((Submission.Blueprint.singC).map
          (Submission.Blueprint.incl (Set.inter_subset_left : U ∩ V ⊆ U)))
        ((Submission.Blueprint.singC).map
          (Submission.Blueprint.incl (Set.inter_subset_right : U ∩ V ⊆ V))) ⟶
      (Submission.Blueprint.singC).obj X :=
  CategoryTheory.Limits.pushout.desc
    ((Submission.Blueprint.singC).map (Submission.Blueprint.inclTop U))
    ((Submission.Blueprint.singC).map (Submission.Blueprint.inclTop V))
    (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; rfl)

/-- One step of the telescoped homotopy recursion: `h + sd ∘ h`. -/
def homPowStep (X : TopCat) (n : ℕ) (h : ((Submission.Blueprint.singC).obj X).X n →
    ((Submission.Blueprint.singC).obj X).X (n+1)) :
    ((Submission.Blueprint.singC).obj X).X n → ((Submission.Blueprint.singC).obj X).X (n+1) :=
  fun z => homdeg X n z + sddeg X (n+1) (h z)

/-- The `k`-fold telescoped homotopy operator `h_k`, defined by `h_0 = 0` and
`h_{k+1} = h + sd ∘ h_k`. It satisfies `∂ h_k + h_k ∂ = sd^k - id`. -/
def homPow (X : TopCat) (n k : ℕ) :
    ((Submission.Blueprint.singC).obj X).X n → ((Submission.Blueprint.singC).obj X).X (n+1) :=
  Nat.rec (motive := fun _ => ((Submission.Blueprint.singC).obj X).X n →
      ((Submission.Blueprint.singC).obj X).X (n+1))
    (fun _ => 0) (fun _ h => homPowStep X n h) k

end Work.SingMV
