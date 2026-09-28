import Mathlib

/-!
# Serre fibrations

Mathlib has no fibrations in `Topology` at all (only `IsCoveringMap`), yet every
fibration-based argument in homotopy theory — most importantly the Serre spectral sequence of the
path–loop fibration, which is the classical route to the rational Hurewicz theorem and hence to
`Work.StemsB.RatHurewiczRange` (see `Submission/Work/StemsB/CONTRACTS.md` §A) — starts here.

This file introduces the two notions and the first basic lemmas:

* `Work.StemsB.HasHLP p Z` — `p : E → B` has the **homotopy lifting property** with respect to
  `Z`: every homotopy `H` in `B` out of a map `b = p ∘ f` can be lifted to a homotopy out of `f`.
* `Work.StemsB.IsSerreFibration p` — the homotopy lifting property with respect to all cubes
  `I^n` (equivalently, with respect to all CW complexes).  Covering maps are Serre fibrations —
  `Work.StemsB.isSerreFibration_of_isCoveringMap`, proved in the sibling file of the same name —
  so the notion is not vacuous; indeed Mathlib's `IsCoveringMap.liftHomotopy` gives the full HLP,
  so coverings are even Hurewicz fibrations, but the cube version is the one that matches the
  classical definition and the one all later arguments use.
* `Work.StemsB.isSerreFibration_id`, `Work.StemsB.hasHLP_fst` — the identity and the projection of
  a product are fibrations.

Proved elsewhere in this directory: `Work.StemsB.isSerreFibration_of_isCoveringMap`
(coverings are fibrations) and `Work.StemsB.isSerreFibration_evalOne` (the path–loop fibration
`{γ : C(I,X) // γ 0 = x₀} → X` is a fibration — the fibration whose Serre spectral sequence
computes `H_*(K(ℤ,n);ℚ)`).

The next milestones (see the file `CONTRACTS.md`) are: stability under base change and
composition, and then the long exact homotopy sequence of a Serre fibration.
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

variable {E B Z : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Z]

/-- `p : E → B` has the **homotopy lifting property with respect to `Z`**: for every map
`f : Z → E` and every homotopy `H` in the base whose initial map is `p ∘ f`, there is a lifted
homotopy `H'` of `f` covering `H`. -/
def HasHLP (p : C(E, B)) (Z : Type*) [TopologicalSpace Z] : Prop :=
  ∀ (f : C(Z, E)) (b : C(Z, B)) (H : (p.comp f).Homotopy b),
    ∃ (g : C(Z, E)) (H' : f.Homotopy g), p.comp H'.toContinuousMap = H.toContinuousMap

/-- A **Serre fibration** is a map satisfying the homotopy lifting property with respect to every
cube `I^n` (`n : ℕ`).  This is the classical notion (equivalently: with respect to all CW
complexes). -/
def IsSerreFibration (p : C(E, B)) : Prop := ∀ (n : ℕ), HasHLP p (Fin n → I)

theorem isSerreFibration_id : IsSerreFibration (ContinuousMap.id E) := by
  intro n f b H
  exact ⟨b, H, by ext x; rfl⟩

/-- The first projection of a product is a fibration (in fact a Hurewicz fibration: the lift is
`(t, z) ↦ (H (t, z), (f z).2)`). -/
theorem hasHLP_fst (F : Type*) [TopologicalSpace F] : HasHLP (Z := Z)
    (ContinuousMap.fst : C(B × F, B)) := by
  intro f b H
  refine ⟨b.prodMk (ContinuousMap.snd.comp f), ?_, ?_⟩
  · refine ContinuousMap.Homotopy.mk
      (H.toContinuousMap.prodMk ((ContinuousMap.snd.comp f).comp ContinuousMap.snd)) ?_ ?_
    · intro z
      ext <;> simp [ContinuousMap.Homotopy.apply_zero]
    · intro z
      ext <;> simp [ContinuousMap.Homotopy.apply_one]
  · ext x
    simp

/-- The second projection of a product is a fibration. -/
theorem hasHLP_snd (F : Type*) [TopologicalSpace F] : HasHLP (Z := Z)
    (ContinuousMap.snd : C(F × B, B)) := by
  intro f b H
  refine ⟨(ContinuousMap.fst.comp f).prodMk b, ?_, ?_⟩
  · refine ContinuousMap.Homotopy.mk
      (((ContinuousMap.fst.comp f).comp ContinuousMap.snd).prodMk H.toContinuousMap) ?_ ?_
    · intro z
      ext <;> simp [ContinuousMap.Homotopy.apply_zero]
    · intro z
      ext <;> simp [ContinuousMap.Homotopy.apply_one]
  · ext x
    simp

theorem isSerreFibration_fst (F : Type*) [TopologicalSpace F] :
    IsSerreFibration (ContinuousMap.fst : C(B × F, B)) :=
  fun _ => hasHLP_fst F

theorem isSerreFibration_snd (F : Type*) [TopologicalSpace F] :
    IsSerreFibration (ContinuousMap.snd : C(F × B, B)) :=
  fun _ => hasHLP_snd F

/-! ## Pullback (base change) of a map -/

section Pullback

variable {E' : Type*} [TopologicalSpace E']

/-- The **pullback** (fibre product) of `p : E → B` along `q : E' → B`, as a topological space. -/
def Pullback (p : C(E, B)) (q : C(E', B)) : Type _ := {x : E × E' // p x.1 = q x.2}

instance instTopologicalSpacePullback (p : C(E, B)) (q : C(E', B)) :
    TopologicalSpace (Pullback p q) :=
  inferInstanceAs (TopologicalSpace {x : E × E' // p x.1 = q x.2})

/-- The projection of the pullback to `E`. -/
def pullbackFst (p : C(E, B)) (q : C(E', B)) : C(Pullback p q, E) where
  toFun x := x.1.1
  continuous_toFun := continuous_fst.comp continuous_subtype_val

/-- The projection of the pullback to `E'`; this is the base change of `p` along `q`. -/
def pullbackSnd (p : C(E, B)) (q : C(E', B)) : C(Pullback p q, E') where
  toFun x := x.1.2
  continuous_toFun := continuous_snd.comp continuous_subtype_val

end Pullback

/-! ## The fibre of a map -/

section Fibre

/-- The **fibre** of `p : E → B` over a point `b₀`, as a topological space. -/
def fibre (p : C(E, B)) (b₀ : B) : Type _ := {x : E // p x = b₀}

instance instTopologicalSpaceFibre (p : C(E, B)) (b₀ : B) : TopologicalSpace (fibre p b₀) :=
  inferInstanceAs (TopologicalSpace {x : E // p x = b₀})

/-- The inclusion of the fibre of `p` over `b₀` into the total space. -/
def fibreIncl (p : C(E, B)) (b₀ : B) : C(fibre p b₀, E) where
  toFun x := x.1
  continuous_toFun := continuous_subtype_val

@[simp]
theorem fibreIncl_apply (p : C(E, B)) (b₀ : B) (x : fibre p b₀) : fibreIncl p b₀ x = x.1 := rfl

/-- The image in `E` of a point of the fibre of `p` over `b₀` lies over `b₀`. -/
theorem p_fibreIncl (p : C(E, B)) (b₀ : B) (x : fibre p b₀) : p (fibreIncl p b₀ x) = b₀ := x.2

end Fibre

/-! ## The path space of a based space -/

section PathSpace

variable (X : Type*) [TopologicalSpace X] (x₀ : X)

/-- The **path space** of `X` based at `x₀`: the space of paths in `X` starting at `x₀`, with the
subspace topology inherited from the compact-open topology on `C(I, X)`. -/
def PathSpace : Type _ := {γ : C(I, X) // γ 0 = x₀}

instance : TopologicalSpace (PathSpace X x₀) := inferInstanceAs (TopologicalSpace {γ : C(I, X) // γ 0 = x₀})

/-- The **evaluation at `1`** map `PX → X` of the path space.  Its fibre over `x₀` is the loop
space `Ω X = Path x₀ x₀`, so `PX → X` is the *path–loop fibration*. -/
def evalOne : C(PathSpace X x₀, X) where
  toFun γ := γ.1 1
  continuous_toFun := continuous_eval.comp (continuous_subtype_val.prodMk continuous_const)

/-- The fibre of the **path–loop fibration** `PX → X` over the base point is the loop space
`Ω X = Path x₀ x₀`. -/
def fibreEvalOneHomeo (X : Type*) [TopologicalSpace X] (x₀ : X) :
    fibre (evalOne X x₀) x₀ ≃ₜ Path x₀ x₀ where
  toFun γ := { toContinuousMap := γ.1.1, source' := γ.1.2, target' := γ.2 }
  invFun p := ⟨⟨p.toContinuousMap, p.source'⟩, p.target'⟩
  left_inv γ := rfl
  right_inv p := rfl
  continuous_toFun := by
    refine (continuous_induced_rng (f := ((↑) : Path x₀ x₀ → C(I, X)))).2 ?_
    show Continuous fun γ : fibre (evalOne X x₀) x₀ => (γ.1.1 : C(I, X))
    fun_prop
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    exact continuous_induced_dom

end PathSpace

/-! ## The relative homotopy lifting property

The *relative* homotopy lifting property is the form of the HLP needed to construct the
connecting map `π_{k+1}(B) → π_k(F)` of a Serre fibration and to prove that it is well defined on
homotopy classes.  It is the HLP for the standard pair

  `(I^k × I, I^k × {0} ∪ ∂I^k × I)`

(a "cube with an `L`-shaped boundary"), i.e. lifting a homotopy whose initial map is prescribed,
together with a prescribed lift on the lateral boundary `∂I^k × I` as well.  The pair is a relative
CW pair (a single `(k+1)`-cell is attached; `L ⧸ (I^k × {0}) ≅ S^k`), so the property holds for
every Serre fibration; the proof is the classical cell-by-cell / homotopy-extension argument.

**Proof strategy** (the statement is the classical characterisation of Serre fibrations: a map is
a Serre fibration *iff* it has the RLP w.r.t. `I^k × {0} ∪ ∂I^k × I ↪ I^k × I` for all `k`
(Quillen; Hatcher, *Algebraic Topology*, Prop. 4.48).  Note that the pair has the *same homotopy
type as* `(D^{k+1}, D^k)` and both members are contractible, so the inclusion is an acyclic
cofibration in the Quillen model structure on `Top`.)  Two routes:

(a) **Homotopy extension + Strøm's lemma.**  The pair `(I^k × I, L)` has the HEP with an *explicit*
    retraction `R : (I^k × I) × I → (I^k × I) × {0} ∪ L × I`: let
    `d(y) = min (last coordinate) (min_i min (y_i) (1 - y_i))`, let `φ(y,s)` be the point obtained
    by lowering the last coordinate and pushing every `i`-th coordinate towards its nearer end by
    `min (s) (d y)`, and set
    `R (y, s) = if s ≤ d y then (φ y s, 0) else (φ y (d y), s - d y)`.
    (Continuity at `s = d y` is the only point to check; `R (y, 0) = (y, 0)` and `R = id` on
    `L × I`.)  Then apply Strøm's lemma: *if `(X,A)` has the HEP and `p` has the HLP w.r.t. `X`,
    then `p` has the HLP w.r.t. `(X,A)`* (Strøm, *Note on cofibrations II*; May–Ponto, *More
    Concise Algebraic Topology*, or any model-category text where this is part of the proof that
    trivial cofibrations lift against fibrations).  The naive shortcut "lift `H ∘ R` by the
    absolute HLP and postcompose with `R`" is *not* enough (it does not control the lateral
    boundary), so the actual content of Strøm's lemma cannot be avoided.
(b) **Cell by cell.**  Write the inclusion as a transfinite composition of cell attachments and
    lift one cell at a time, using the absolute cube HLP and the homeomorphism of an `n`-cell with
    the cube. -/

section Rel

/-- The boundary of the `k`-cube, as a type. -/
abbrev CubeBdry (k : ℕ) : Type := {x : Fin k → I // x ∈ Cube.boundary (Fin k)}

/-- The canonical inclusion `∂I^k × I → I^k × I`. -/
def bdryIncl (k : ℕ) : C(CubeBdry k × I, (Fin k → I) × I) where
  toFun y := (y.1.1, y.2)
  continuous_toFun := by fun_prop

/-- The canonical inclusion `I^k → I^k × I`, `x ↦ (x, 0)`. -/
def zeroIncl (k : ℕ) : C(Fin k → I, (Fin k → I) × I) where
  toFun x := (x, 0)
  continuous_toFun := by fun_prop

end Rel

/-! ## Closure of the homotopy lifting property -/

section Comp

variable {C : Type*} [TopologicalSpace C]

/-- The composite of two maps with the HLP has the HLP: lift first through the first map and then
through the second. -/
theorem HasHLP.comp {p : C(E, B)} {q : C(C, E)} {Z : Type*} [TopologicalSpace Z]
    (hp : HasHLP p Z) (hq : HasHLP q Z) : HasHLP (p.comp q) Z := by
  intro f b H
  obtain ⟨g₁, H₁, hH₁⟩ := hp (q.comp f) b H
  obtain ⟨g₂, H₂, hH₂⟩ := hq f g₁ H₁
  exact ⟨g₂, H₂, by rw [ContinuousMap.comp_assoc, hH₂, hH₁]⟩

/-- The composite of two Serre fibrations is a Serre fibration. -/
theorem IsSerreFibration.comp {p : C(E, B)} {q : C(C, E)}
    (hp : IsSerreFibration p) (hq : IsSerreFibration q) : IsSerreFibration (p.comp q) :=
  fun n => (hp n).comp (hq n)

end Comp

section Prod

variable {E' B' : Type*} [TopologicalSpace E'] [TopologicalSpace B']

/-- The product of two maps with the HLP has the HLP (lift each component). -/
theorem HasHLP.prodMap {p : C(E, B)} {p' : C(E', B')} {Z : Type*} [TopologicalSpace Z]
    (hp : HasHLP p Z) (hp' : HasHLP p' Z) : HasHLP (p.prodMap p') Z := by
  intro f b H
  obtain ⟨g₁, H₁, hH₁⟩ := hp (ContinuousMap.fst.comp f) (ContinuousMap.fst.comp b)
    { toContinuousMap := ContinuousMap.fst.comp H.toContinuousMap
      map_zero_left := fun z => congrArg Prod.fst (H.map_zero_left z)
      map_one_left := fun z => congrArg Prod.fst (H.map_one_left z) }
  obtain ⟨g₂, H₂, hH₂⟩ := hp' (ContinuousMap.snd.comp f) (ContinuousMap.snd.comp b)
    { toContinuousMap := ContinuousMap.snd.comp H.toContinuousMap
      map_zero_left := fun z => congrArg Prod.snd (H.map_zero_left z)
      map_one_left := fun z => congrArg Prod.snd (H.map_one_left z) }
  refine ⟨g₁.prodMk g₂,
    ⟨H₁.toContinuousMap.prodMk H₂.toContinuousMap, ?_, ?_⟩, ?_⟩
  · intro z
    exact Prod.ext (H₁.map_zero_left z) (H₂.map_zero_left z)
  · intro z
    exact Prod.ext (H₁.map_one_left z) (H₂.map_one_left z)
  · apply ContinuousMap.ext
    rintro ⟨s, z⟩
    have h₁ : p (H₁.toContinuousMap (s, z)) = (H.toContinuousMap (s, z)).1 :=
      congrFun (congrArg DFunLike.coe hH₁) (s, z)
    have h₂ : p' (H₂.toContinuousMap (s, z)) = (H.toContinuousMap (s, z)).2 :=
      congrFun (congrArg DFunLike.coe hH₂) (s, z)
    show (p (H₁.toContinuousMap (s, z)), p' (H₂.toContinuousMap (s, z)))
      = H.toContinuousMap (s, z)
    exact Prod.ext h₁ h₂

end Prod

/-- The **relative homotopy lifting property** of `p : E → B` for the standard pair
`(I^k × I, I^k × {0} ∪ ∂I^k × I)`: a homotopy `H : I^k × I → B` together with a lift `f` of its
initial map `H(·,0)` and a lift `g` of its lateral boundary `H|∂I^k × I` (agreeing with `f` on
`∂I^k × {0}`) can be lifted simultaneously. -/
def HasHLPRel (p : C(E, B)) (k : ℕ) : Prop :=
  ∀ (H : C((Fin k → I) × I, B))
    (f : C(Fin k → I, E))
    (_hf : p.comp f = H.comp (zeroIncl k))
    (g : C(CubeBdry k × I, E))
    (_hg : p.comp g = H.comp (bdryIncl k))
    (_hg0 : ∀ (x : CubeBdry k), g (x, 0) = f x.1),
    ∃ G : C((Fin k → I) × I, E),
      p.comp G = H ∧
      (∀ x : Fin k → I, G (x, 0) = f x) ∧
      (∀ (x : CubeBdry k) (t : I), G (x.1, t) = g (x, t))


end

end Work.StemsB
