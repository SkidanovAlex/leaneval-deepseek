import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-! ## Scaffolding for `free_lie_four_fixed_generation`

A `ZMod 2`-linear map `σA` of `A = MonoidAlgebra (ZMod 2) (FreeMonoid X)` which is multiplicative,
fixes `1` and sends `single x` to `single (σ x)` is necessarily the map induced by the letterwise
action of `σ` on words; in particular it is an involution.  This is the only structural input
needed to *state* the main claim, and it is proved here. -/

section Basic

theorem freeMonoid_map_comp {X : Type*} (σ τ : X → X) (w : FreeMonoid X) :
    FreeMonoid.map σ (FreeMonoid.map τ w) = FreeMonoid.map (σ ∘ τ) w := by
  rw [FreeMonoid.map_comp, MonoidHom.comp_apply]

variable (X : Type) (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
  (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2]
    MonoidAlgebra (ZMod 2) (FreeMonoid X))
  (hmul : ∀ a b, σA (a * b) = σA a * σA b) (hone : σA 1 = 1)
  (hgen : ∀ x, σA (MonoidAlgebra.single (FreeMonoid.of x) 1)
    = MonoidAlgebra.single (FreeMonoid.of (σ x)) 1)

include hmul hone hgen in
/-- `σA` acts on the monomial basis by the letterwise action of `σ` on words. -/
theorem sigmaA_of (w : FreeMonoid X) :
    σA (MonoidAlgebra.of (ZMod 2) (FreeMonoid X) w) =
      MonoidAlgebra.of (ZMod 2) (FreeMonoid X) (FreeMonoid.map (fun x => σ x) w) := by
  induction w using FreeMonoid.recOn with
  | one =>
      rw [map_one (FreeMonoid.map (fun x => σ x)),
          map_one (MonoidAlgebra.of (ZMod 2) (FreeMonoid X)), hone]
  | of_mul x w ihw =>
      rw [map_mul (MonoidAlgebra.of (ZMod 2) (FreeMonoid X)),
          map_mul (FreeMonoid.map (fun x => σ x)),
          FreeMonoid.map_of]
      rw [hmul, ihw, map_mul (MonoidAlgebra.of (ZMod 2) (FreeMonoid X))]
      congr 1
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.of_apply]
      exact hgen x

include hσ hmul hone hgen in
/-- `σA` is an involution (as the hypotheses force it to be the map induced by `σ`). -/
theorem sigmaA_involutive (a : MonoidAlgebra (ZMod 2) (FreeMonoid X)) : σA (σA a) = a := by
  have hσ' : ((fun x => σ x) ∘ (fun x => σ x)) = id := by
    funext x; exact hσ x
  have h1 : ∀ w : FreeMonoid X,
      σA (σA (MonoidAlgebra.of (ZMod 2) (FreeMonoid X) w))
        = MonoidAlgebra.of (ZMod 2) (FreeMonoid X) w := by
    intro w
    rw [sigmaA_of X σ σA hmul hone hgen w,
        sigmaA_of X σ σA hmul hone hgen (FreeMonoid.map (fun x => σ x) w)]
    rw [freeMonoid_map_comp (σ := fun x => σ x) (τ := fun x => σ x) w, hσ', FreeMonoid.map_id]
    rfl
  refine MonoidAlgebra.induction_on (motive := fun t => σA (σA t) = t) a ?_ ?_ ?_
  · intro w
    simpa [MonoidAlgebra.of_apply] using h1 w
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

include hmul hone hgen in
/-- `σA` is an algebra automorphism: it is multiplicative by hypothesis and bijective by
involutivity. -/
theorem sigmaA_mul (a b : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    σA (a * b) = σA a * σA b := hmul a b

include hmul hone hgen in
/-- The image of the evaluation map on the monomial basis, used to build `W`. -/
theorem sigmaA_single (w : FreeMonoid X) :
    σA (MonoidAlgebra.single w (1 : ZMod 2)) =
      MonoidAlgebra.single (FreeMonoid.map (fun x => σ x) w) 1 := by
  rw [← MonoidAlgebra.of_apply (ZMod 2) (FreeMonoid X) w,
      ← MonoidAlgebra.of_apply (ZMod 2) (FreeMonoid X) (FreeMonoid.map (fun x => σ x) w)]
  exact sigmaA_of X σ σA hmul hone hgen w

end Basic



variable {X : Type*}

/-- The coefficient of a word in an element of `A = MonoidAlgebra (ZMod 2) (FreeMonoid X)`. -/
noncomputable def coeffW (x : MonoidAlgebra (ZMod 2) (FreeMonoid X)) (w : FreeMonoid X) : ZMod 2 :=
  x.coeff w

/-- The word `a_i * a_i * b_i * b_i` attached to a letter `i` (with `b_i = σ i`). -/
noncomputable def selfWord (σ : X → X) (i : X) : FreeMonoid X :=
  FreeMonoid.of i * FreeMonoid.of i * FreeMonoid.of (σ i) * FreeMonoid.of (σ i)

/-- The word `a_i * a_j * b_j * b_i` attached to two letters (with `b = σ`). -/
noncomputable def symWord (σ : X → X) (i j : X) : FreeMonoid X :=
  FreeMonoid.of i * FreeMonoid.of j * FreeMonoid.of (σ j) * FreeMonoid.of (σ i)

/-- The word `a_i * b_j * a_j * b_i` attached to two letters (with `b = σ`). -/
noncomputable def flipWord (σ : X → X) (i j : X) : FreeMonoid X :=
  FreeMonoid.of i * FreeMonoid.of (σ j) * FreeMonoid.of j * FreeMonoid.of (σ i)

/-! ## The subspaces `W` and `T` of the statement, and the action of `σA` on them -/

section Defs

variable (X : Type)

/-- The commutator `a*b + b*a`. -/
noncomputable def brk (a b : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    MonoidAlgebra (ZMod 2) (FreeMonoid X) := a * b + b * a

/-- The degree-`4` left-nested commutator monomial attached to a `4`-tuple. -/
noncomputable def brk4 (t : X × X × X × X) : MonoidAlgebra (ZMod 2) (FreeMonoid X) :=
  brk X (brk X (brk X (MonoidAlgebra.single (FreeMonoid.of t.1) (1 : ZMod 2))
      (MonoidAlgebra.single (FreeMonoid.of t.2.1) 1))
      (MonoidAlgebra.single (FreeMonoid.of t.2.2.1) 1))
    (MonoidAlgebra.single (FreeMonoid.of t.2.2.2) 1)

/-- The submodule `W` of the statement: the span of the degree-`4` left-nested commutators. -/
noncomputable def Wsub : Submodule (ZMod 2) (MonoidAlgebra (ZMod 2) (FreeMonoid X)) :=
  Submodule.span (ZMod 2) (Set.range (brk4 X))

/-- The submodule `T` of the statement: the span of `{x*x} ∪ {x*y + y*x}`. -/
noncomputable def Tsub : Submodule (ZMod 2) (MonoidAlgebra (ZMod 2) (FreeMonoid X)) :=
  Submodule.span (ZMod 2) (Set.range fun p : X × X =>
      MonoidAlgebra.single (FreeMonoid.of p.1) (1 : ZMod 2)
        * MonoidAlgebra.single (FreeMonoid.of p.1) 1
    + (MonoidAlgebra.single (FreeMonoid.of p.2) 1
        * MonoidAlgebra.single (FreeMonoid.of p.1) 1
      + MonoidAlgebra.single (FreeMonoid.of p.1) 1
        * MonoidAlgebra.single (FreeMonoid.of p.2) 1))

end Defs

section Stability

variable (X : Type) [Fintype X] (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
  (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2]
    MonoidAlgebra (ZMod 2) (FreeMonoid X))
  (hmul : ∀ a b, σA (a * b) = σA a * σA b) (hone : σA 1 = 1)
  (hgen : ∀ x, σA (MonoidAlgebra.single (FreeMonoid.of x) 1)
    = MonoidAlgebra.single (FreeMonoid.of (σ x)) 1)

include hmul hone hgen in
/-- `σA` sends the generator attached to a tuple to the generator attached to the `σ`-image of the
tuple. -/
theorem sigmaA_brk4 (t : X × X × X × X) :
    σA (brk4 X t) = brk4 X (σ t.1, σ t.2.1, σ t.2.2.1, σ t.2.2.2) := by
  simp only [brk4, brk, map_add, hmul, hgen]

include hmul hone hgen in
/-- `σA` maps every generator of `W` into `W`. -/
theorem sigmaA_brk4_mem (t : X × X × X × X) : σA (brk4 X t) ∈ Wsub X :=
  Submodule.subset_span ⟨(σ t.1, σ t.2.1, σ t.2.2.1, σ t.2.2.2),
    (sigmaA_brk4 X σ σA hmul hone hgen t).symm⟩

include hmul hone hgen in
/-- `W` is stable under `σA`. -/
theorem Wsub_stable : Submodule.map σA (Wsub X) ≤ Wsub X := by
  rw [Submodule.map_le_iff_le_comap]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨t, rfl⟩
  exact sigmaA_brk4_mem X σ σA hmul hone hgen t

include hσ hmul hone hgen in
/-- `W` is `σA`-stable (as a subspace). -/
theorem Wsub_stable_eq : Submodule.map σA (Wsub X) = Wsub X := by
  refine le_antisymm (Wsub_stable X σ σA hmul hone hgen) ?_
  intro v hv
  refine Submodule.mem_map.2 ⟨σA v, ?_, sigmaA_involutive X σ hσ σA hmul hone hgen v⟩
  exact Wsub_stable X σ σA hmul hone hgen (Submodule.mem_map.2 ⟨v, hv, rfl⟩)

end Stability
