import Mathlib
import Submission.Work.ShafarevichKoch.freeGroup_twoCocycle_is_coboundary

/-!
# `Hⁿ⁺²` of a free group vanishes

For a free group `G = FreeGroup α`, the trivial `k[G]`-module has a length-one free
resolution `0 → k[G]^{(α)} → k[G] → k → 0`, so `G` has cohomological dimension one and
`Hᵐ(G, A) = 0` for every coefficient representation `A` and every `m ≥ 2`.  This file
proves that statement in the form needed by the Shafarevich--Koch chapter:

`Work.ShafarevichKoch.freeGroup_H2_vanishes`, i.e. `IsZero (groupCohomology A (n + 2))`.

The proof is assembled from two inputs:

* `Work.ShafarevichKoch.freeGroup_twoCocycle_is_coboundary`: every `2`-cocycle of a free
  group is a coboundary, i.e. `H²(G, -) = 0`;
* the coinduced representation `Coind_1^G(A)` of an arbitrary representation `A`, which is
  acyclic (`Shapiro's lemma` + vanishing of the cohomology of the trivial group), so that
  the long exact sequence of the short exact sequence
  `0 → A → Coind_1^G(A) → C → 0` shifts cohomological degree down by one:
  `Hᵐ⁺¹(G, A) ≅ Hᵐ(G, C)` for `m ≥ 1`.  Induction on the degree then gives vanishing in
  all degrees `≥ 2`.
-/

set_option linter.style.haveILetI false

namespace Work.ShafarevichKoch

open CategoryTheory CategoryTheory.Limits

variable {α : Type}

/-! ## `H²` of a free group vanishes -/

/-- **Every `2`-cocycle of a free group with coefficients in a `𝔽₂`-representation is a
coboundary**, hence `H²(FreeGroup α, M) = 0` for every `M`. -/
theorem freeGroup_H2_isZero (M : Rep (ZMod 2) (FreeGroup α)) :
    IsZero (groupCohomology M 2) := by
  have key : ∀ z : groupCohomology.cocycles₂ M, ⇑z ∈ groupCohomology.coboundaries₂ M := by
    intro z
    -- the cocycle condition in the form used by `freeGroup_twoCocycle_is_coboundary`
    have hcoc : ∀ g h j : FreeGroup α,
        (⇑z : FreeGroup α × FreeGroup α → M.V) (g * h, j) + ⇑z (g, h)
          = M.ρ g (⇑z (h, j)) + ⇑z (g, h * j) := by
      intro g h j
      have h0 : (groupCohomology.d₂₃ M).hom ⇑z = 0 := z.2
      have h1 := congr_fun h0 (g, h, j)
      rw [groupCohomology.d₂₃_hom_apply] at h1
      have h2 : (M.ρ g) (⇑z (h, j)) - ⇑z (g * h, j) + ⇑z (g, h * j) - ⇑z (g, h)
          = (0 : FreeGroup α × FreeGroup α × FreeGroup α → M.V) (g, h, j) := h1
      rw [Pi.zero_apply] at h2
      rw [← sub_eq_zero]
      have h3 : -((M.ρ g) (⇑z (h, j)) - ⇑z (g * h, j) + ⇑z (g, h * j) - ⇑z (g, h)) = 0 := by
        rw [h2, neg_zero]
      abel_nf at h3 ⊢
      exact h3
    obtain ⟨x, hx⟩ := freeGroup_twoCocycle_is_coboundary α (ZMod 2) M ⇑z hcoc
    rw [groupCohomology.coboundaries₂, LinearMap.mem_range]
    refine ⟨x, ?_⟩
    funext p
    rw [groupCohomology.d₁₂_hom_apply]
    exact hx p.1 p.2
  have hsub : Subsingleton (groupCohomology M 2) := ⟨fun a b => by
    have ha : a = 0 := groupCohomology.H2_induction_on a
      (fun z => by rw [groupCohomology.H2π_eq_zero_iff]; exact key z)
    have hb : b = 0 := groupCohomology.H2_induction_on b
      (fun z => by rw [groupCohomology.H2π_eq_zero_iff]; exact key z)
    rw [ha, hb]⟩
  exact ModuleCat.isZero_of_subsingleton _

/-! ## The coinduced representation and its acyclicity -/

/-- The coinduction of a representation `A` of a free group from the trivial subgroup; its
underlying module is a submodule of the functions on the group. -/
noncomputable abbrev coindAux (A : Rep (ZMod 2) (FreeGroup α)) : Rep (ZMod 2) (FreeGroup α) :=
  Rep.coind (⊥ : Subgroup (FreeGroup α)).subtype (Rep.res (⊥ : Subgroup (FreeGroup α)).subtype A)

lemma mem_coind (A : Rep (ZMod 2) (FreeGroup α)) (a : A) : (fun x : FreeGroup α => A.ρ x a) ∈
    (Representation.coindV (⊥ : Subgroup (FreeGroup α)).subtype
      (A.ρ.comp (⊥ : Subgroup (FreeGroup α)).subtype)) := by
  intro g h
  have hg : (⊥ : Subgroup (FreeGroup α)).subtype g = 1 := Subgroup.mem_bot.mp g.2
  simp only [hg, one_mul, MonoidHom.comp_apply, MonoidHom.map_one]
  simp

/-- The canonical inclusion of `A` into the coinduced representation `Coind_1^G(A)`,
`a ↦ (x ↦ ρ x a)`. -/
noncomputable def emb (A : Rep (ZMod 2) (FreeGroup α)) : A ⟶ coindAux A :=
  Rep.ofHom
  { toLinearMap :=
      { toFun := fun a => ⟨fun x : FreeGroup α => A.ρ x a, mem_coind A a⟩
        map_add' := fun a b => by ext x; simp
        map_smul' := fun c a => by ext x; simp }
    isIntertwining' := fun g => by
      ext a x
      simp only [LinearMap.coe_comp, Function.comp_apply]
      change A.ρ x (A.ρ g a) = A.ρ (x * g) a
      rw [MonoidHom.map_mul]
      rfl }

lemma emb_injective (A : Rep (ZMod 2) (FreeGroup α)) : Function.Injective (emb A).hom := by
  intro a b h
  have := congrArg (fun (u : ↥(coindAux A)) => (u : FreeGroup α → A) 1) h
  simpa [emb] using this

/-- The coinduced representation is acyclic: its cohomology vanishes in positive degrees. -/
lemma isZero_coind (A : Rep (ZMod 2) (FreeGroup α)) (n : ℕ) :
    IsZero (groupCohomology (coindAux A) (n + 1)) := by
  haveI : Subsingleton ↥(⊥ : Subgroup (FreeGroup α)) := inferInstance
  exact IsZero.of_iso (isZero_groupCohomology_succ_of_subsingleton
    (Rep.res (⊥ : Subgroup (FreeGroup α)).subtype A) n)
    (groupCohomology.coindIso (Rep.res (⊥ : Subgroup (FreeGroup α)).subtype A) (n + 1))

lemma mono_emb (A : Rep (ZMod 2) (FreeGroup α)) : Mono (emb A) := by
  rw [Rep.mono_iff_injective]
  exact emb_injective A

/-- The short exact sequence `0 → A → Coind_1^G(A) → coker → 0`. -/
lemma ses_shortExact (A : Rep (ZMod 2) (FreeGroup α)) :
    (ShortComplex.cokernelSequence (emb A)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact (emb A))
    (ShortComplex.cokernelSequence_f (emb A) ▸ mono_emb A) inferInstance

/-! ## Vanishing in all degrees `≥ 2` -/

/-- If `H²(FreeGroup α, -)` vanishes, then so does `Hⁿ⁺²(FreeGroup α, -)` for every `n`:
each step of the induction shifts the cohomological degree down along the short exact
sequence `0 → A → Coind_1^G(A) → C → 0` whose middle term is acyclic. -/
theorem vanishes_of_H2 (h2 : ∀ M : Rep (ZMod 2) (FreeGroup α), IsZero (groupCohomology M 2)) :
    ∀ (M : Rep (ZMod 2) (FreeGroup α)) (n : ℕ), IsZero (groupCohomology M (n + 2)) := by
  intro M n
  induction n generalizing M with
  | zero => simpa using h2 M
  | succ n ih =>
      have hX : (ShortComplex.cokernelSequence (emb M)).ShortExact := ses_shortExact M
      haveI : IsIso (groupCohomology.δ hX (n + 2) (n + 3) rfl) :=
        groupCohomology.isIso_δ_of_isZero hX (n + 2) (isZero_coind M (n + 1)) (isZero_coind M (n + 2))
      exact IsZero.of_iso (Y := groupCohomology (cokernel (emb M)) (n + 2)) (ih (cokernel (emb M)))
        (asIso (groupCohomology.δ hX (n + 2) (n + 3) rfl)).symm

/-- **`H⁰⁺²` of a free group vanishes**: the second cohomology of a free group with
coefficients in any `𝔽₂`-linear representation is zero. -/
theorem freeGroup_H2_vanishes_zero (A : Rep (ZMod 2) (FreeGroup α)) :
    CategoryTheory.Limits.IsZero (groupCohomology A 2) := freeGroup_H2_isZero A

/-- **The cohomology of a free group vanishes in degrees `≥ 2`.**  For every `𝔽₂`-linear
representation `A` of the free group on `α`, and every `n : ℕ`, the group cohomology
`Hⁿ⁺²(FreeGroup α, A)` is the zero module. -/
theorem freeGroup_H2_vanishes (α : Type) (A : Rep (ZMod 2) (FreeGroup α)) (n : ℕ) :
    CategoryTheory.Limits.IsZero (groupCohomology A (n + 2)) :=
  vanishes_of_H2 freeGroup_H2_isZero A n

end Work.ShafarevichKoch
