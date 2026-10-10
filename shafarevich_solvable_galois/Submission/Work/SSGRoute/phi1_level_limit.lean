import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.phi1_level_system

/-! Guidance from the project lead (the requester): read `DESIGN_FIX.md` §1 and the "colimit step"
section of `PHI1_PGROUP_STATUS.md`.

# The direct limit `V = colim_{L} H²(Gal(L/k), 𝔽_p)` over the levels

The colimit step of `Work.SSGRoute.phi1_mono_step_in` (`exists_realization_of_delta_lam`) defines a
functional `λ` on the union `W = ⋃_L W_L ⊆ V`, extends it to `Λ : V → A[p]` and reads the result off
at the levels.  This file provides the ambient colimit `V` and its API.

* `levelStep p` — the transition maps of the level system `levelMap`, as a family of additive
  homomorphisms (`L ≤ L'` gives `H²(Gal(L/k),𝔽_p) →+ H²(Gal(L'/k),𝔽_p)`);
* `LevelCohLimit p` — the direct limit (Mathlib's `Algebra.Colimit.DirectLimit`, which needs no
  `DecidableEq` on the index — only `IsDirectedOrder`, provided by `phi1_level_index`);
* `LevelCohLimit.of p L` — the canonical map of the `L`-th component;
* `LevelCohLimit.of_levelMap` — the relation of the colimit (`of` is compatible with inflation);
* `LevelCohLimit.of_eq_zero_iff` — an element of the colimit vanishes iff it vanishes at a *higher*
  level (the form in which the colimit's equality relation is consumed);
* `LevelCohLimit.lift`, `LevelCohLimit.hom_ext` — the universal property for additive maps.
-/

noncomputable section

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-! ### A generic additive direct limit API (build speed)

The colimit API below (`LevelCohLimit`, and `Wcolim` in `phi1_wcolim`) is the same for every
directed system of additive groups.  Proving it once for an abstract system `G`, `f` and
instantiating it is much cheaper than elaborating each proof against the concrete (very large)
component types. -/
section GenericDirectLimit

variable {ι : Type} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] {G : ι → Type}
  [∀ i, AddCommGroup (G i)] (f : ∀ i j, i ≤ j → G i →+ G j)
  [DirectedSystem G (fun i j h => f i j h)]

/-- The canonical map of the `L`-th component into the direct limit. -/
def dlOf (L : ι) : G L →+ DirectLimit G f where
  toFun x := ⟦⟨L, x⟩⟧
  map_zero' := (DirectLimit.zero_def L).symm
  map_add' x y := (DirectLimit.add_def L x y).symm

theorem dlOf_apply (L : ι) (x : G L) : dlOf f L x = ⟦⟨L, x⟩⟧ := rfl

theorem dlOf_map {L L' : ι} (h : L ≤ L') (x : G L) : dlOf f L' (f L L' h x) = dlOf f L x :=
  DirectLimit.mk_apply (f := f) L L' x h

theorem dlOf_eq_zero_iff (L : ι) (x : G L) :
    dlOf f L x = 0 ↔ ∃ (L' : ι) (h : L ≤ L'), f L L' h x = 0 := by
  constructor
  · intro hx
    set L₀ : ι := Classical.arbitrary ι with hL₀
    have h0 : (0 : DirectLimit G f) = (⟦⟨L₀, (0 : G L₀)⟩⟧ : DirectLimit G f) :=
      DirectLimit.zero_def L₀
    have heq : (⟦⟨L, x⟩⟧ : DirectLimit G f) = (⟦⟨L₀, (0 : G L₀)⟩⟧ : DirectLimit G f) := by
      rw [← h0]
      exact hx
    obtain ⟨j, hx', hy', heq'⟩ := Quotient.exact heq
    refine ⟨j, hx', ?_⟩
    rw [map_zero] at heq'
    exact heq'
  · rintro ⟨L', h, hz⟩
    rw [← dlOf_map f h x, hz, map_zero]

theorem dl_induction {C : DirectLimit G f → Prop} (ih : ∀ (L : ι) (x : G L), C (dlOf f L x))
    (x : DirectLimit G f) : C x :=
  DirectLimit.induction (f := f) (fun L y => ih L y) x

/-- The universal property for additive maps out of the direct limit. -/
def dlLift {A : Type} [AddCommMonoid A] (g : ∀ L : ι, G L →+ A)
    (hg : ∀ (L L' : ι) (h : L ≤ L') (x : G L), g L' (f L L' h x) = g L x) :
    DirectLimit G f →+ A where
  toFun := DirectLimit.lift f (fun L => g L) (fun L L' h x => (hg L L' h x).symm)
  map_zero' := by
    simpa only using
      DirectLimit.lift_zero (f := f) (g := fun L => g L) (fun L L' h x => (hg L L' h x).symm)
  map_add' x y := by
    simpa only using
      DirectLimit.lift_add (f := f) (g := fun L => g L) (fun L L' h x => (hg L L' h x).symm) x y

theorem dlLift_of {A : Type} [AddCommMonoid A] (g : ∀ L : ι, G L →+ A)
    (hg : ∀ (L L' : ι) (h : L ≤ L') (x : G L), g L' (f L L' h x) = g L x) (L : ι) (x : G L) :
    dlLift f g hg (dlOf f L x) = g L x := rfl

end GenericDirectLimit

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω] [IsGalois k K]

/-- The transition maps of the level system, as a family of additive homomorphisms. -/
abbrev levelStep (p : ℕ) (i j : Lvl k K Ω) (h : i ≤ j) : LevelCoh p i →+ LevelCoh p j :=
  levelMap p i j h

/-- **`V = colim_{L} H²(Gal(L/k), 𝔽_p)`**: the direct limit of the level system. -/
abbrev LevelCohLimit (p : ℕ) : Type _ :=
  DirectLimit (LevelCoh (k := k) (K := K) (Ω := Ω) p)
    (levelStep (k := k) (K := K) (Ω := Ω) p)

/-- The canonical map `H²(Gal(L/k),𝔽_p) → V` of the `L`-th component of the colimit. -/
def LevelCohLimit.of (p : ℕ) (L : Lvl k K Ω) :
    LevelCoh p L →+ LevelCohLimit (k := k) (K := K) (Ω := Ω) p :=
  dlOf (levelStep (k := k) (K := K) (Ω := Ω) p) L

@[simp] theorem LevelCohLimit.of_zero (p : ℕ) (L : Lvl k K Ω) :
    LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L (0 : LevelCoh p L) = 0 := map_zero _

/-- **The colimit relation**: the `L`-component of the colimit is compatible with the transition
maps (`of_L` of an inflated class is `of_{L'}` of the class). -/
theorem LevelCohLimit.of_levelMap (p : ℕ) {L L' : Lvl k K Ω} (h : L ≤ L')
    (x : LevelCoh p L) :
    LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L' (levelMap p L L' h x)
      = LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L x :=
  dlOf_map (levelStep (k := k) (K := K) (Ω := Ω) p) h x

/-- **An element of the colimit vanishes iff it vanishes at a higher level.**  This is the form in
which the equality relation of the colimit (a quotient of `Σ L, H²(Gal(L/k),𝔽_p)` by "agree after
inflation") is consumed in the well-definedness arguments of the realisation step. -/
theorem LevelCohLimit.of_eq_zero_iff (p : ℕ) (L : Lvl k K Ω) (x : LevelCoh p L) :
    LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L x = 0
      ↔ ∃ (L' : Lvl k K Ω) (h : L ≤ L'), levelMap p L L' h x = 0 :=
  dlOf_eq_zero_iff (levelStep (k := k) (K := K) (Ω := Ω) p) L x

/-- Induction on the colimit: it suffices to check a predicate on the components. -/
protected theorem LevelCohLimit.induction (p : ℕ)
    {C : LevelCohLimit (k := k) (K := K) (Ω := Ω) p → Prop}
    (ih : ∀ (L : Lvl k K Ω) (x : LevelCoh p L),
      C (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L x))
    (x : LevelCohLimit (k := k) (K := K) (Ω := Ω) p) : C x :=
  dl_induction (levelStep (k := k) (K := K) (Ω := Ω) p) ih x

/-- **The universal property of the colimit**, for additive maps: a compatible family of additive
maps out of the components induces one out of `V`. -/
noncomputable def LevelCohLimit.lift (p : ℕ) {A : Type} [AddCommMonoid A]
    (g : ∀ L : Lvl k K Ω, LevelCoh p L →+ A)
    (hg : ∀ (L L' : Lvl k K Ω) (h : L ≤ L') (x : LevelCoh p L),
      g L' (levelMap p L L' h x) = g L x) :
    LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+ A :=
  dlLift (levelStep (k := k) (K := K) (Ω := Ω) p) g hg

@[simp] theorem LevelCohLimit.lift_of (p : ℕ) {A : Type} [AddCommMonoid A]
    (g : ∀ L : Lvl k K Ω, LevelCoh p L →+ A)
    (hg : ∀ (L L' : Lvl k K Ω) (h : L ≤ L') (x : LevelCoh p L),
      g L' (levelMap p L L' h x) = g L x)
    (L : Lvl k K Ω) (x : LevelCoh p L) :
    LevelCohLimit.lift (k := k) (K := K) (Ω := Ω) p g hg
        (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L x) = g L x := rfl

/-- **Extensionality for additive maps out of the colimit**: it suffices to agree on the
components. -/
@[ext] theorem LevelCohLimit.hom_ext (p : ℕ) {A : Type} [AddCommMonoid A]
    {g₁ g₂ : LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+ A}
    (h : ∀ L : Lvl k K Ω,
      g₁.comp (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L)
        = g₂.comp (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L)) : g₁ = g₂ := by
  apply AddMonoidHom.ext
  intro x
  exact LevelCohLimit.induction (k := k) (K := K) (Ω := Ω) p
    (C := fun y => g₁ y = g₂ y)
    (fun L z => by
      have hz := congrArg (fun f : LevelCoh p L →+ A => f z) (h L)
      simpa only [AddMonoidHom.coe_comp, Function.comp_apply] using hz) x

end Work.SSGRoute
