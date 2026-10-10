import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option linter.unusedSectionVars false

/-!
# The norm of a 2-cocycle is a 2-coboundary (the `n = 2` instance of "the norm kills
positive group cohomology")

For a finite group `G`, a `k`-linear `G`-representation `A` (`k` a commutative ring) and
`f : G × G → A` a 2-cocycle (in the model `groupCohomology.cocycles₂ A` of
`Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`), the pointwise norm

`p ↦ A.norm (f p)`  (with `A.norm a = ∑_{g : G} g · a`)

is an explicit **2-coboundary**: with the primitive

`b t = ∑_{g : G} f (g, t)`

one has `d₁₂ b = fun p ↦ A.norm (f p)`, because the cocycle identity at `(x, g, y)` and at
`(g, x, y)` give

`A.ρ x (f (g,y)) = f (x*g,y) - f (x,g*y) + f (x,g)`,   `A.ρ g (f (x,y)) = f (g*x,y) - f (g,x*y) + f (g,x)`

and the two reindexings `g ↦ x*g`, `g ↦ g*x` (resp. `g ↦ g*y`) make the two sides agree.  No
commutativity of `G` is used (only that left and right translations are bijections).

Consequently `H²(G, A)` is killed by the norm endomorphism, i.e. the `n = 2` instance of
`groupCohomology.map (MonoidHom.id G) A.norm 2 = 0`.
-/

open scoped BigOperators
open Rep

namespace NK.NUV2.RouteC

variable {k G : Type} [CommRing k] [Group G] [Fintype G]
variable (A : Rep k G)

/-- The norm is the sum of the action: `A.norm a = ∑_g g · a`. -/
lemma norm_apply_eq_sum (a : A) : A.norm.hom a = ∑ g : G, A.ρ g a := by
  rw [Rep.norm_apply, Representation.norm]
  exact LinearMap.sum_apply Finset.univ (fun g : G => A.ρ g) a

/-- The pointwise norm of a 2-cocycle is again a 2-cocycle (the norm is additive). -/
theorem norm_comp_mem_cocycles₂ (f : G × G → A) (hf : f ∈ groupCohomology.cocycles₂ A) :
    (fun p : G × G => A.norm.hom (f p)) ∈ groupCohomology.cocycles₂ A := by
  rw [groupCohomology.mem_cocycles₂_def] at hf ⊢
  intro g h j
  have h := congrArg A.norm.hom (hf g h j)
  simp only [map_add, map_sub, map_zero] at h
  rw [Rep.hom_comm_apply A.norm g] at h
  exact h

/-- **The main computation**: the norm of a 2-cocycle is a 2-coboundary, with primitive
`b t = ∑_g f (g, t)`. -/
theorem norm_comp_mem_coboundaries₂ (f : G × G → A) (hf : f ∈ groupCohomology.cocycles₂ A) :
    (fun p : G × G => A.norm.hom (f p)) ∈ groupCohomology.coboundaries₂ A := by
  classical
  rw [groupCohomology.mem_cocycles₂_def] at hf
  refine LinearMap.mem_range.mpr ⟨fun t : G => ∑ g : G, f (g, t), ?_⟩
  funext p
  obtain ⟨x, y⟩ := p
  rw [groupCohomology.d₁₂_hom_apply]
  have hN : A.norm.hom (f (x, y)) = ∑ g : G, A.ρ g (f (x, y)) := norm_apply_eq_sum (A := A) _
  rw [hN]
  -- the two cocycle identities
  have h1 : ∀ g : G, A.ρ x (f (g, y)) = f (x * g, y) - f (x, g * y) + f (x, g) := by
    intro g
    have h := hf x g y
    linear_combination (norm := abel_nf) h
  have h2 : ∀ g : G, A.ρ g (f (x, y)) = f (g * x, y) - f (g, x * y) + f (g, x) := by
    intro g
    have h := hf g x y
    linear_combination (norm := abel_nf) h
  rw [map_sum]
  rw [Finset.sum_congr rfl (fun g _ => h1 g), Finset.sum_congr rfl (fun g _ => h2 g)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- the reindexings
  have hr1 : (∑ g : G, f (x * g, y)) = ∑ t : G, f (t, y) :=
    Fintype.sum_equiv (Equiv.mulLeft x) (fun g : G => f (x * g, y)) (fun t : G => f (t, y))
      (fun g => rfl)
  have hr2 : (∑ g : G, f (g * x, y)) = ∑ t : G, f (t, y) :=
    Fintype.sum_equiv (Equiv.mulRight x) (fun g : G => f (g * x, y)) (fun t : G => f (t, y))
      (fun g => rfl)
  have hr3 : (∑ g : G, f (x, g * y)) = ∑ s : G, f (x, s) :=
    Fintype.sum_equiv (Equiv.mulRight y) (fun g : G => f (x, g * y)) (fun s : G => f (x, s))
      (fun g => rfl)
  rw [hr1, hr2, hr3]
  abel_nf

/-! ## The cohomology-level statement: the norm kills `H²(G, A)` -/

/-- **`n = 2` instance of "the norm kills positive cohomology"**, in the low-degree model: for
every 2-cocycle `x` the class of its pointwise norm `p ↦ A.norm (x p)` is zero in `H²(G, A)`.

Proof: `H2π_eq_zero_iff` reduces the statement to membership in `coboundaries₂ A`, which is
`norm_comp_mem_coboundaries₂` (the norm of a 2-cocycle *is* a 2-coboundary, explicitly). -/
theorem H2π_norm_comp_eq_zero (x : groupCohomology.cocycles₂ A) :
    groupCohomology.H2π A
      ⟨fun p : G × G => A.norm.hom (x p),
        norm_comp_mem_cocycles₂ (A := A) (⇑x) x.2⟩ = 0 := by
  rw [groupCohomology.H2π_eq_zero_iff]
  exact norm_comp_mem_coboundaries₂ (A := A) (⇑x) x.2

/-! ## The literal statement: `map (MonoidHom.id G) A.norm 2 = 0` -/

set_option backward.isDefEq.respectTransparency false in
/-- **The `n = 2` instance of `map_norm_eq_zero`**: for every finite group `G` and every
`Rep k G` (`k` a commutative ring), the norm endomorphism `A.norm` induces the zero map on
`H²(G, A)`.  This is the form in which the fact is consumed by the character-formula route to
the local reciprocity law (Route C of `NOTES_serre_route.md`).

Assembly: `H2_induction_on` + `H2π_comp_map` (Mathlib) reduce the statement to the cocycle-level
membership `norm_comp_mem_coboundaries₂`, i.e. to the explicit primitive `b t = ∑_g f (g, t)`. -/
theorem map_norm_eq_zero_two :
    groupCohomology.map (MonoidHom.id G) A.norm 2 = 0 := by
  ext x
  refine groupCohomology.H2_induction_on x fun y => ?_
  have key : (groupCohomology.map (MonoidHom.id G) A.norm 2) (groupCohomology.H2π A y)
      = groupCohomology.H2π A
          (groupCohomology.mapCocycles₂ (MonoidHom.id G) A.norm y) := by
    have h := congrArg (fun m => m y)
      (groupCohomology.H2π_comp_map (MonoidHom.id G) A.norm)
    simpa only [h]
  rw [key]
  refine (groupCohomology.H2π_eq_zero_iff _).2 ?_
  have hmem := norm_comp_mem_coboundaries₂ (A := A) (⇑y) y.2
  have hcoe : (⇑(groupCohomology.mapCocycles₂ (MonoidHom.id G) A.norm y) : G × G → A)
      = fun p : G × G => A.norm.hom (y p) := by
    rw [groupCohomology.coe_mapCocycles₂]
    rfl
  rwa [hcoe]

/-! ## The `n = 1` instance: exact, and even simpler than `n = 2`

For a 1-cocycle (a derivation) `d` the norm is *pointwise zero*: the cocycle identity
`A.ρ h (d g) - d (h*g) + d h = 0` gives `A.ρ h (d g) = d (h*g) - d h`, and `h ↦ h*g` is a
bijection, so

`A.norm (d g) = ∑_h A.ρ h (d g) = ∑_h (d (h*g) - d h) = 0`.

Hence the pointwise norm of a 1-cocycle is the coboundary `d₀₁ 0`, and `map (A.norm) 1 = 0`
follows from Mathlib's `H1π_comp_map` exactly as in degree `2`. -/

/-- The pointwise norm of a 1-cocycle vanishes. -/
theorem norm_apply_cocycles₁_eq_zero (d : groupCohomology.cocycles₁ A) (g : G) :
    A.norm.hom (d g) = 0 := by
  rw [norm_apply_eq_sum A]
  have h1 : ∀ h : G, A.ρ h (d g) = d (h * g) - d h := by
    intro h
    have hmem := (groupCohomology.mem_cocycles₁_def (⇑d)).1 d.2 h g
    linear_combination (norm := abel_nf) hmem
  rw [Finset.sum_congr rfl (fun h _ => h1 h), Finset.sum_sub_distrib]
  have hr : (∑ h : G, d (h * g)) = ∑ t : G, d t :=
    Fintype.sum_equiv (Equiv.mulRight g) (fun h : G => d (h * g)) (fun t : G => d t)
      (fun h => rfl)
  rw [hr, sub_self]

/-- The pointwise norm of a 1-cocycle is again a 1-cocycle (the norm is additive). -/
theorem norm_comp_mem_cocycles₁ (f : G → A) (hf : f ∈ groupCohomology.cocycles₁ A) :
    (fun g : G => A.norm.hom (f g)) ∈ groupCohomology.cocycles₁ A := by
  rw [groupCohomology.mem_cocycles₁_def] at hf ⊢
  intro g h
  have h' := congrArg A.norm.hom (hf g h)
  simp only [map_add, map_sub, map_zero] at h'
  rw [← Rep.hom_comm_apply A.norm g]
  exact h'

/-- **`n = 1` instance of "the norm kills positive cohomology"**, low-degree model. -/
theorem H1π_norm_comp_eq_zero (x : groupCohomology.cocycles₁ A) :
    groupCohomology.H1π A
      ⟨fun g : G => A.norm.hom (x g), norm_comp_mem_cocycles₁ (A := A) (⇑x) x.2⟩ = 0 := by
  rw [groupCohomology.H1π_eq_zero_iff]
  refine LinearMap.mem_range.mpr ⟨0, ?_⟩
  funext g
  rw [groupCohomology.d₀₁_hom_apply]
  simp only [map_zero, sub_zero]
  exact (norm_apply_cocycles₁_eq_zero (A := A) x g).symm

set_option backward.isDefEq.respectTransparency false in
/-- **The `n = 1` instance of `map_norm_eq_zero`**: `map (MonoidHom.id G) A.norm 1 = 0`. -/
theorem map_norm_eq_zero_one :
    groupCohomology.map (MonoidHom.id G) A.norm 1 = 0 := by
  ext x
  refine groupCohomology.H1_induction_on x fun y => ?_
  have key : (groupCohomology.map (MonoidHom.id G) A.norm 1) (groupCohomology.H1π A y)
      = groupCohomology.H1π A
          (groupCohomology.mapCocycles₁ (MonoidHom.id G) A.norm y) := by
    have h := congrArg (fun m => m y)
      (groupCohomology.H1π_comp_map (MonoidHom.id G) A.norm)
    simpa only [h]
  rw [key]
  refine (groupCohomology.H1π_eq_zero_iff _).2 ?_
  refine LinearMap.mem_range.mpr ⟨0, ?_⟩
  funext g
  rw [groupCohomology.coe_mapCocycles₁, groupCohomology.d₀₁_hom_apply]
  simp only [map_zero, sub_zero]
  exact (norm_apply_cocycles₁_eq_zero (A := A) y g).symm

end NK.NUV2.RouteC
