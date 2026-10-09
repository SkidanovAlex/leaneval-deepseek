import Mathlib
import Submission.Work.SSGRoute.phi1_level_system
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

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
    LevelCoh p L →+ LevelCohLimit (k := k) (K := K) (Ω := Ω) p where
  toFun x := ⟦⟨L, x⟩⟧
  map_zero' := (DirectLimit.zero_def L).symm
  map_add' x y := (DirectLimit.add_def L x y).symm

@[simp] theorem LevelCohLimit.of_zero (p : ℕ) (L : Lvl k K Ω) :
    LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L (0 : LevelCoh p L) = 0 := map_zero _

/-- **The colimit relation**: the `L`-component of the colimit is compatible with the transition
maps (`of_L` of an inflated class is `of_{L'}` of the class). -/
theorem LevelCohLimit.of_levelMap (p : ℕ) {L L' : Lvl k K Ω} (h : L ≤ L')
    (x : LevelCoh p L) :
    LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L' (levelMap p L L' h x)
      = LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L x :=
  DirectLimit.mk_apply (f := levelStep (k := k) (K := K) (Ω := Ω) p) L L' x h

/-- **An element of the colimit vanishes iff it vanishes at a higher level.**  This is the form in
which the equality relation of the colimit (a quotient of `Σ L, H²(Gal(L/k),𝔽_p)` by "agree after
inflation") is consumed in the well-definedness arguments of the realisation step. -/
theorem LevelCohLimit.of_eq_zero_iff (p : ℕ) (L : Lvl k K Ω) (x : LevelCoh p L) :
    LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L x = 0
      ↔ ∃ (L' : Lvl k K Ω) (h : L ≤ L'), levelMap p L L' h x = 0 := by
  constructor
  · intro hx
    set L₀ : Lvl k K Ω := Classical.arbitrary (Lvl k K Ω) with hL₀
    have h0 : (0 : LevelCohLimit (k := k) (K := K) (Ω := Ω) p)
        = (⟦⟨L₀, (0 : LevelCoh p L₀)⟩⟧ : LevelCohLimit (k := k) (K := K) (Ω := Ω) p) :=
      DirectLimit.zero_def L₀
    have heq : (⟦⟨L, x⟩⟧ : LevelCohLimit (k := k) (K := K) (Ω := Ω) p)
        = (⟦⟨L₀, (0 : LevelCoh p L₀)⟩⟧ : LevelCohLimit (k := k) (K := K) (Ω := Ω) p) := by
      rw [← h0]
      exact hx
    obtain ⟨j, hx', hy', heq'⟩ := Quotient.exact heq
    refine ⟨j, hx', ?_⟩
    have : levelStep (k := k) (K := K) (Ω := Ω) p L₀ j hy' (0 : LevelCoh p L₀) = 0 :=
      map_zero _
    rw [this] at heq'
    simpa only [levelStep] using heq'
  · rintro ⟨L', h, hz⟩
    rw [← LevelCohLimit.of_levelMap (k := k) (K := K) (Ω := Ω) p h x, hz]
    exact LevelCohLimit.of_zero (k := k) (K := K) (Ω := Ω) p L'

/-- Induction on the colimit: it suffices to check a predicate on the components. -/
protected theorem LevelCohLimit.induction (p : ℕ)
    {C : LevelCohLimit (k := k) (K := K) (Ω := Ω) p → Prop}
    (ih : ∀ (L : Lvl k K Ω) (x : LevelCoh p L),
      C (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L x))
    (x : LevelCohLimit (k := k) (K := K) (Ω := Ω) p) : C x :=
  DirectLimit.induction (f := levelStep (k := k) (K := K) (Ω := Ω) p)
    (fun L y => ih L y) x

/-- **The universal property of the colimit**, for additive maps: a compatible family of additive
maps out of the components induces one out of `V`. -/
noncomputable def LevelCohLimit.lift (p : ℕ) {A : Type} [AddCommMonoid A]
    (g : ∀ L : Lvl k K Ω, LevelCoh p L →+ A)
    (hg : ∀ (L L' : Lvl k K Ω) (h : L ≤ L') (x : LevelCoh p L),
      g L' (levelMap p L L' h x) = g L x) :
    LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+ A where
  toFun := DirectLimit.lift (levelStep (k := k) (K := K) (Ω := Ω) p) (fun L => g L)
    (fun L L' h x => (hg L L' h x).symm)
  map_zero' := by
    simpa only using
      DirectLimit.lift_zero (f := levelStep (k := k) (K := K) (Ω := Ω) p) (g := fun L => g L)
        (fun L L' h x => (hg L L' h x).symm)
  map_add' x y := by
    simpa only using
      DirectLimit.lift_add (f := levelStep (k := k) (K := K) (Ω := Ω) p) (g := fun L => g L)
        (fun L L' h x => (hg L L' h x).symm) x y

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
