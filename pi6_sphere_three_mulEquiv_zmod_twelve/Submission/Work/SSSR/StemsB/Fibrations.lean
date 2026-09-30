import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

open scoped Topology unitInterval
namespace Work.SSSR.StemsB

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

end Fibre

section PathSpace

variable (X : Type*) [TopologicalSpace X] (x₀ : X)

/-- The **path space** of `X` based at `x₀`: the space of paths in `X` starting at `x₀`, with the
subspace topology inherited from the compact-open topology on `C(I, X)`. -/
def PathSpace : Type _ := {γ : C(I, X) // γ 0 = x₀}

instance : TopologicalSpace (PathSpace X x₀) := inferInstanceAs (TopologicalSpace {γ : C(I, X) // γ 0 = x₀})

end PathSpace

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

section Comp

variable {C : Type*} [TopologicalSpace C]

end Comp

section Prod

variable {E' B' : Type*} [TopologicalSpace E'] [TopologicalSpace B']

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

end Work.SSSR.StemsB
