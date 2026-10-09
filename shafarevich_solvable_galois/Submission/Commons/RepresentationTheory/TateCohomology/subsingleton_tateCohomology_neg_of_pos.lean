import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Data.Int.Star
import Submission.Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_coind_bot
import Submission.Commons.RepresentationTheory.GroupCohomology.subsingleton_groupCohomology_coind_bot_restrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-
# Vanishing of negative Tate cohomology from the vanishing of `H¹` and `H²`

This file proves that if a `ℤ`-linear representation `A` of a finite group `G` satisfies
`H¹(H, A) = 0 = H²(H, A)` for every subgroup `H ≤ G`, and if moreover the positive-degree
Tate cohomology of every such representation (for every finite group) vanishes, then the Tate
cohomology of `A` vanishes in every *negative* degree as well.

The argument is the standard dimension-shifting argument for cohomologically trivial modules.
For any representation `B` we construct a short exact sequence
`0 ⟶ D ⟶ M ⟶ B ⟶ 0`
where `M = Coind_⊥^G(B.V)` is the coindution of the trivial representation on the underlying
`ℤ`-module of `B` from the trivial subgroup.  The module `M` is acyclic: its Tate cohomology
vanishes in every degree, and this remains true after restriction to any subgroup.  Hence the
connecting homomorphism gives isomorphisms `Ĥʳ(G, B) ≅ Ĥʳ⁺¹(G, D)` in every degree, and likewise
for every subgroup.  In particular `Ĥ⁰(G, D)` agrees with `Ĥ⁻¹(G, B)`, so the positive-degree
vanishing hypothesis applied to `D` produces the vanishing in degree `-1`, and iterating the
construction produces the vanishing in all negative degrees.

## Main result

* `subsingleton_tateCohomology_neg_of_pos`
-/

open CategoryTheory

namespace Commons.RepresentationTheory.TateCohomology

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

-- Allows `Fintype ↥H` to be found by typeclass search for subgroups of a finite group.
attribute [local instance] Classical.propDecidable

variable {G : Type} [Group G] [Fintype G]

/-! ## The acyclic middle term and a surjection onto a given representation -/

section Middle

variable (B : Rep ℤ G)

noncomputable local instance : Module ℤ B.V := B.hV2

/-- The trivial representation of `⊥ ≤ G` on the underlying `ℤ`-module of `B`. -/
noncomputable abbrev coindCoeff : Rep ℤ (⊥ : Subgroup G) :=
  Rep.trivial ℤ (⊥ : Subgroup G) B.V

/-- The coinduction of the trivial representation on `B.V` from the trivial subgroup.  It is
acyclic in every degree for `G` and stays acyclic after restriction to any subgroup. -/
noncomputable abbrev coindMid : Rep ℤ G :=
  Rep.coind (⊥ : Subgroup G).subtype (coindCoeff B)

noncomputable local instance : Module ℤ (coindMid B).V := (coindMid B).hV2

/-- The `x`-th coordinate functional `coindMid B → B`. -/
noncomputable def projFun (x : G) : coindMid B →ₗ[ℤ] B :=
  (LinearMap.proj x).comp
    (Submodule.subtype (Representation.coindV (⊥ : Subgroup G).subtype (coindCoeff B).ρ))

/-- The `G`-equivariant map `coindMid B → B`, `f ↦ ∑ x, ρ(x⁻¹) (f x)`. -/
noncomputable def linMap : coindMid B →ₗ[ℤ] B :=
  ∑ x : G, (B.ρ x⁻¹).comp (projFun B x)

lemma linMap_apply (f : coindMid B) : linMap B f = ∑ x : G, B.ρ x⁻¹ (f.1 x) := by
  simp only [linMap, LinearMap.sum_apply, LinearMap.comp_apply, projFun, LinearMap.proj_apply,
    Submodule.subtype_apply]

lemma coindMid_ρ_apply (h : G) (f : coindMid B) (x : G) :
    (((coindMid B).ρ h) f).1 x = f.1 (x * h) := rfl

theorem linMap_intertwines (h : G) :
    linMap B ∘ₗ (coindMid B).ρ h = (B.ρ h) ∘ₗ linMap B := by
  ext f
  rw [LinearMap.comp_apply, LinearMap.comp_apply, linMap_apply, linMap_apply, map_sum]
  refine Fintype.sum_bijective (· * h) (Group.mulRight_bijective h) _ _ (fun x => ?_)
  rw [coindMid_ρ_apply, ← Module.End.mul_apply, ← map_mul]
  congr 1
  group

theorem linMap_surjective : Function.Surjective (linMap B) := by
  classical
  intro b
  have hm : Pi.single 1 b ∈ Representation.coindV (⊥ : Subgroup G).subtype (coindCoeff B).ρ := by
    rw [Representation.mem_coindV]
    intro g h
    have hg' : g = 1 := Subtype.ext (Subgroup.mem_bot.mp g.2)
    rw [hg']
    simp
  refine ⟨⟨Pi.single 1 b, hm⟩, ?_⟩
  rw [linMap_apply]
  have hcoe : (↑(⟨Pi.single 1 b, hm⟩ : (coindMid B).V) : G → B.V) = Pi.single 1 b := rfl
  rw [hcoe]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro x _ hx
    rw [Pi.single_eq_of_ne hx, map_zero]
  · intro h
    exact absurd (Finset.mem_univ 1) h

/-- The canonical surjection from the acyclic middle term onto `B`. -/
noncomputable def coindEpi : coindMid B ⟶ B :=
  Rep.ofHom ⟨linMap B, linMap_intertwines B⟩

theorem coindEpi_surjective : Function.Surjective (coindEpi B) := fun b =>
  let ⟨f, hf⟩ := linMap_surjective B b
  ⟨f, hf⟩

theorem coindEpi_epi : Epi (coindEpi B) :=
  (Rep.epi_iff_surjective _).2 (coindEpi_surjective B)

end Middle

/-! ## Acyclicity of the restricted coinduced module -/

/-- The coinduction of a trivial representation from the trivial subgroup has vanishing Tate
cohomology in every degree; moreover this remains true after restricting to a subgroup. -/
theorem subsingleton_tateCohomology_coind_bot_restrict_all (H : Subgroup G)
    (W : Rep ℤ (⊥ : Subgroup G)) (r : ℤ) :
    Subsingleton (tateCohomology (Rep.res H.subtype (Rep.coind (⊥ : Subgroup G).subtype W)) r) := by
  let C : Rep ℤ (⊥ : Subgroup H) :=
    Commons.RepresentationTheory.GroupCohomology.supersingletonCoindCoeff H W
  haveI : Subsingleton (tateCohomology (Rep.coind (⊥ : Subgroup H).subtype C) r) :=
    Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_coind_bot C r
  have hIso : Nonempty (Rep.res H.subtype (Rep.coind (⊥ : Subgroup G).subtype W) ≅
      Rep.coind (⊥ : Subgroup H).subtype C) := by
    letI : Module ℤ (Rep.res H.subtype (Rep.coind (⊥ : Subgroup G).subtype W)).V :=
      (Rep.res H.subtype (Rep.coind (⊥ : Subgroup G).subtype W)).hV2
    letI : Module ℤ (Rep.coind (⊥ : Subgroup H).subtype C).V :=
      (Rep.coind (⊥ : Subgroup H).subtype C).hV2
    exact ⟨Rep.mkIso (Representation.Equiv.mk
      (Commons.RepresentationTheory.GroupCohomology.supersingletonResCoindBotLinearEquiv H W)
      (fun s => LinearMap.ext (fun f =>
        Commons.RepresentationTheory.GroupCohomology.supersingletonResCoindBotLinearEquiv_equivariant
          H W s f)))⟩
  obtain ⟨e⟩ := hIso
  exact (Functor.mapIso (tateCohomologyFunctor (R := ℤ) (G := H) r) e).toLinearEquiv.injective.subsingleton

/-! ## The short exact sequence, its acyclicity, and the dimension shifts -/

/-- **Dimension shifting.** If `S : X₁ ⟶ X₂ ⟶ X₃` is a short exact sequence of `ℤ[G]`-modules
whose middle term is trivial in degrees `r` and `r + 1`, then the connecting homomorphism gives an
isomorphism `Ĥʳ(G, X₃) ≅ Ĥʳ⁺¹(G, X₁)`. -/
theorem tateCohomology_iso_of_acyclic_middle_of_subsingleton
    (S : ShortComplex (Rep ℤ G)) (hS : S.ShortExact) (r : ℤ)
    (h₁ : Subsingleton (tateCohomology S.X₂ r))
    (h₂ : Subsingleton (tateCohomology S.X₂ (r + 1))) :
    Nonempty (tateCohomology S.X₃ r ≃ₗ[ℤ] tateCohomology S.X₁ (r + 1)) := by
  haveI hz₁ : Subsingleton ↥((S.map (tateComplexFunctor ℤ G)).X₂.homology r) := h₁
  haveI hz₂ : Subsingleton ↥((S.map (tateComplexFunctor ℤ G)).X₂.homology (r + 1)) := h₂
  haveI : IsIso (TateCohomology.δ hS r) :=
    ShortComplex.ShortExact.isIso_δ (TateCohomology.map_tateComplexFunctor_shortExact hS) r (r + 1)
      rfl (ModuleCat.isZero_of_subsingleton _) (ModuleCat.isZero_of_subsingleton _)
  exact ⟨(asIso (TateCohomology.δ hS r)).toLinearEquiv⟩

section ShortComplexPart

variable (B : Rep ℤ G)

/-- The short exact sequence `0 → D → coindMid B → B → 0` with acyclic middle term. -/
noncomputable def acyclicShortComplex : ShortComplex (Rep ℤ G) :=
  ShortComplex.kernelSequence (coindEpi B)

lemma acyclicShortComplex_X₂ : (acyclicShortComplex B).X₂ = coindMid B := rfl

theorem acyclicShortComplex_shortExact : (acyclicShortComplex B).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact (coindEpi B))
    (inferInstance : Mono (ShortComplex.kernelSequence (coindEpi B)).f)
    (coindEpi_epi B)

theorem acyclicShortComplex_acyclic_middle_G (r : ℤ) :
    Subsingleton (tateCohomology (acyclicShortComplex B).X₂ r) :=
  Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_coind_bot
    (coindCoeff B) r

theorem acyclicShortComplex_acyclic_middle_restrict_all (H : Subgroup G) (r : ℤ) :
    Subsingleton (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₂) r) :=
  Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_coind_bot_restrict_all
    H (coindCoeff B) r

/-- Dimension shift: `Ĥʳ(G, B) ≅ Ĥʳ⁺¹(G, D)` where `D` is the kernel term. -/
theorem acyclicShortComplex_shift_up (r : ℤ) :
    Nonempty (tateCohomology (acyclicShortComplex B).X₃ r ≃ₗ[ℤ]
      tateCohomology (acyclicShortComplex B).X₁ (r + 1)) :=
  tateCohomology_iso_of_acyclic_middle_of_subsingleton (acyclicShortComplex B)
    (acyclicShortComplex_shortExact B) r (acyclicShortComplex_acyclic_middle_G B r)
    (acyclicShortComplex_acyclic_middle_G B (r + 1))

/-- Dimension shift, in the form used to show that the kernel term inherits the
vanishing hypothesis. -/
theorem acyclicShortComplex_shift_down (r : ℤ) :
    Nonempty (tateCohomology (acyclicShortComplex B).X₁ r ≃ₗ[ℤ]
      tateCohomology (acyclicShortComplex B).X₃ (r - 1)) := by
  obtain ⟨e⟩ := acyclicShortComplex_shift_up B (r - 1)
  rw [show (r - 1) + 1 = r from by omega] at e
  exact ⟨e.symm⟩

/-- Dimension shift at the level of an arbitrary subgroup. -/
theorem acyclicShortComplex_shift_restrict_up (H : Subgroup G) (r : ℤ) :
    Nonempty (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₃) r ≃ₗ[ℤ]
      tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₁) (r + 1)) := by
  have hS : ((acyclicShortComplex B).map (Rep.resFunctor H.subtype)).ShortExact :=
    (Rep.shortExact_res (k := ℤ) H.subtype).2 (acyclicShortComplex_shortExact B)
  obtain ⟨e⟩ := tateCohomology_iso_of_acyclic_middle_of_subsingleton
    ((acyclicShortComplex B).map (Rep.resFunctor H.subtype)) hS r
    (acyclicShortComplex_acyclic_middle_restrict_all B H r)
    (acyclicShortComplex_acyclic_middle_restrict_all B H (r + 1))
  exact ⟨e⟩

/-- Dimension shift at the level of an arbitrary subgroup, in the form used to show that the
kernel term inherits the vanishing hypothesis. -/
theorem acyclicShortComplex_shift_restrict_down (H : Subgroup G) (r : ℤ) :
    Nonempty (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₁) r ≃ₗ[ℤ]
      tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₃) (r - 1)) := by
  obtain ⟨e⟩ := acyclicShortComplex_shift_restrict_up B H (r - 1)
  rw [show (r - 1) + 1 = r from by omega] at e
  exact ⟨e.symm⟩

end ShortComplexPart

/-! ## Comparing restrictions along subgroups -/

/-- Restricting a representation first to `H` and then to a subgroup `H' ≤ H` is the same as
restricting along the canonical isomorphism `H' ≅ H'.map H.subtype`. -/
theorem groupCohomology_res_res_iso (H : Subgroup G) (H' : Subgroup H) (B : Rep ℤ G) (n : ℕ) :
    Nonempty (groupCohomology (Rep.res H'.subtype (Rep.res H.subtype B)) n ≅
      groupCohomology (Rep.res (H'.map H.subtype).subtype B) n) := by
  letI : Module ℤ B.V := B.hV2
  let e : H' ≃* H'.map H.subtype :=
    Subgroup.equivMapOfInjective H' H.subtype H.subtype_injective
  refine ⟨groupCohomology.mapIso e (LinearEquiv.refl ℤ B.V) ?_ n⟩
  intro x
  ext v
  rfl

/-! ## The vanishing hypothesis and the kernel construction -/

/-- `B` has vanishing Tate cohomology in all nonnegative degrees after restriction to every
subgroup. -/
def PosTateVanishing (B : Rep ℤ G) : Prop :=
  ∀ (H : Subgroup G) (r : ℤ), 0 ≤ r → Subsingleton (tateCohomology (Rep.res H.subtype B) r)

/-- Vanishing of the kernel term in degree `1`. -/
theorem subsingleton_tateCohomology_kernel_one {B : Rep ℤ G} (hB : PosTateVanishing B)
    (H : Subgroup G) :
    Subsingleton (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₁) 1) := by
  obtain ⟨e⟩ := acyclicShortComplex_shift_restrict_up B H 0
  haveI : Subsingleton (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₃) 0) :=
    hB H 0 le_rfl
  rw [show (0 : ℤ) + 1 = 1 from by norm_num] at e
  exact e.symm.injective.subsingleton

/-- Vanishing of the kernel term in degree `2`. -/
theorem subsingleton_tateCohomology_kernel_two {B : Rep ℤ G} (hB : PosTateVanishing B)
    (H : Subgroup G) :
    Subsingleton (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₁) 2) := by
  obtain ⟨e⟩ := acyclicShortComplex_shift_restrict_up B H 1
  haveI : Subsingleton (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₃) 1) :=
    hB H 1 (by norm_num)
  rw [show (1 : ℤ) + 1 = 2 from by norm_num] at e
  exact e.symm.injective.subsingleton

/-- The kernel term satisfies the `H¹`/`H²` hypothesis of `hpos`. -/
theorem subsingleton_groupCohomology_kernel_one_two {B : Rep ℤ G} (hB : PosTateVanishing B)
    (H : Subgroup G) :
    Subsingleton (groupCohomology (Rep.res H.subtype (acyclicShortComplex B).X₁) 1) ∧
      Subsingleton (groupCohomology (Rep.res H.subtype (acyclicShortComplex B).X₁) 2) := by
  constructor
  · haveI := subsingleton_tateCohomology_kernel_one hB H
    exact (TateCohomology.isoGroupCohomology (R := ℤ) (G := H) 1).app _ |>.symm.toLinearEquiv.injective.subsingleton
  · haveI := subsingleton_tateCohomology_kernel_two hB H
    exact (TateCohomology.isoGroupCohomology (R := ℤ) (G := H) 2).app _ |>.symm.toLinearEquiv.injective.subsingleton

/-- The kernel term of the acyclic short exact sequence inherits the vanishing hypothesis, once
the vanishing in degree `-1` is known. -/
theorem posTateVanishing_kernel {B : Rep ℤ G} (hB : PosTateVanishing B)
    (hneg : ∀ H : Subgroup G, Subsingleton (tateCohomology (Rep.res H.subtype B) (-1))) :
    PosTateVanishing (acyclicShortComplex B).X₁ := by
  intro H r hr
  obtain ⟨e⟩ := acyclicShortComplex_shift_restrict_down B H r
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · subst hr0
    haveI : Subsingleton
        (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₃) (0 - 1 : ℤ)) := by
      rw [show (0 : ℤ) - 1 = -1 from by norm_num]
      exact hneg H
    exact e.injective.subsingleton
  · haveI : Subsingleton
        (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₃) (r - 1)) :=
      hB H (r - 1) (by omega)
    exact e.injective.subsingleton

/-! ## The dimension-shifting induction -/

/-- **Main induction.** If the Tate cohomology of `B` vanishes in all nonnegative degrees after
restriction to every subgroup of `G`, then it vanishes in all negative degrees, both for `G` and
for all of its subgroups.  The hypothesis `hpos` is the positive-degree vanishing statement used
for the `Ĥ⁰` of the kernel term. -/
theorem subsingleton_tateCohomology_neg_of_posTateVanishing {G : Type} [Group G] [Fintype G]
    (hpos : ∀ (K : Type) [Group K] [Fintype K] (B : Rep ℤ K),
        (∀ H : Subgroup K, Subsingleton (groupCohomology (Rep.res H.subtype B) 1) ∧
          Subsingleton (groupCohomology (Rep.res H.subtype B) 2)) →
        ∀ r : ℤ, 0 ≤ r → Subsingleton (tateCohomology B r))
    (B : Rep ℤ G) (hB : PosTateVanishing B) : ∀ r : ℤ, r < 0 → Subsingleton (tateCohomology B r) := by
  have main : ∀ n : ℕ, 1 ≤ n → ∀ (B : Rep ℤ G), PosTateVanishing B →
      Subsingleton (tateCohomology B (-(n : ℤ))) ∧
        ∀ H : Subgroup G,
          Subsingleton (tateCohomology (Rep.res H.subtype B) (-(n : ℤ))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn B hB
      rcases (by omega : n = 1 ∨ 2 ≤ n) with hn1 | hn2
      · subst hn1
        constructor
        · -- `Ĥ⁻¹(G, B) ≅ Ĥ⁰(G, D)` and `Ĥ⁰(G, D) = 0` by `hpos` applied to `D`.
          obtain ⟨e⟩ := acyclicShortComplex_shift_up B (-1)
          rw [show (-1 : ℤ) + 1 = 0 from by norm_num] at e
          haveI : Subsingleton (tateCohomology (acyclicShortComplex B).X₁ 0) :=
            hpos G (acyclicShortComplex B).X₁
              (fun H => subsingleton_groupCohomology_kernel_one_two hB H) 0 le_rfl
          exact e.injective.subsingleton
        · intro H
          obtain ⟨e⟩ := acyclicShortComplex_shift_restrict_up B H (-1)
          rw [show (-1 : ℤ) + 1 = 0 from by norm_num] at e
          haveI : Subsingleton (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₁) 0) :=
            hpos H (Rep.res H.subtype (acyclicShortComplex B).X₁) (fun H' => ?_) 0 le_rfl
          · exact e.injective.subsingleton
          · obtain ⟨e1⟩ := groupCohomology_res_res_iso H H' (acyclicShortComplex B).X₁ 1
            obtain ⟨e2⟩ := groupCohomology_res_res_iso H H' (acyclicShortComplex B).X₁ 2
            obtain ⟨h1, h2⟩ := subsingleton_groupCohomology_kernel_one_two hB (H'.map H.subtype)
            exact ⟨e1.toLinearEquiv.injective.subsingleton,
              e2.toLinearEquiv.injective.subsingleton⟩
      · -- `n ≥ 2`: use the induction hypothesis for the kernel term
        have hneg : ∀ H : Subgroup G,
            Subsingleton (tateCohomology (Rep.res H.subtype B) (-1)) := by
          intro H
          have h1 := (ih 1 (by omega) (by omega) B hB).2 H
          simpa using h1
        have hD : PosTateVanishing (acyclicShortComplex B).X₁ := posTateVanishing_kernel hB hneg
        constructor
        · obtain ⟨e⟩ := acyclicShortComplex_shift_up B (-(n : ℤ))
          rw [show -(n : ℤ) + 1 = -(((n - 1 : ℕ)) : ℤ) from by omega] at e
          haveI : Subsingleton (tateCohomology (acyclicShortComplex B).X₁
              (-((n - 1 : ℕ) : ℤ))) := (ih (n - 1) (by omega) (by omega) _ hD).1
          exact e.injective.subsingleton
        · intro H
          obtain ⟨e⟩ := acyclicShortComplex_shift_restrict_up B H (-(n : ℤ))
          rw [show -(n : ℤ) + 1 = -(((n - 1 : ℕ)) : ℤ) from by omega] at e
          haveI : Subsingleton (tateCohomology
              (Rep.res H.subtype (acyclicShortComplex B).X₁) (-((n - 1 : ℕ) : ℤ))) :=
            (ih (n - 1) (by omega) (by omega) _ hD).2 H
          exact e.injective.subsingleton
  intro r hr
  have hrepr : r = -(((-r).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  rw [hrepr]
  exact (main ((-r).toNat) (by omega) B hB).1

/-! ## Deriving the vanishing hypothesis from `hpos` and `hA` -/

/-- The positive-degree vanishing hypothesis `hpos`, applied to `A` and to all of its restrictions
to subgroups using `hA`, yields `PosTateVanishing A`. -/
theorem posTateVanishing_of_pos {G : Type} [Group G] [Fintype G] (A : Rep ℤ G)
    (hpos : ∀ (K : Type) [Group K] [Fintype K] (B : Rep ℤ K),
        (∀ H : Subgroup K, Subsingleton (groupCohomology (Rep.res H.subtype B) 1) ∧
          Subsingleton (groupCohomology (Rep.res H.subtype B) 2)) →
        ∀ r : ℤ, 0 ≤ r → Subsingleton (tateCohomology B r))
    (hA : ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype A) 1) ∧
        Subsingleton (groupCohomology (Rep.res H.subtype A) 2)) :
    PosTateVanishing A := by
  intro H r hr
  refine hpos H (Rep.res H.subtype A) ?_ r hr
  intro H'
  obtain ⟨e1⟩ := groupCohomology_res_res_iso H H' A 1
  obtain ⟨e2⟩ := groupCohomology_res_res_iso H H' A 2
  obtain ⟨h1, h2⟩ := hA (H'.map H.subtype)
  exact ⟨e1.toLinearEquiv.injective.subsingleton,
    e2.toLinearEquiv.injective.subsingleton⟩

/-! ## The main theorem -/

theorem subsingleton_tateCohomology_neg_of_pos {G : Type} [Group G] [Fintype G] (A : Rep ℤ G)
    (hpos : ∀ (K : Type) [Group K] [Fintype K] (B : Rep ℤ K),
        (∀ H : Subgroup K, Subsingleton (groupCohomology (Rep.res H.subtype B) 1) ∧
          Subsingleton (groupCohomology (Rep.res H.subtype B) 2)) →
        ∀ r : ℤ, 0 ≤ r → Subsingleton (tateCohomology B r))
    (hA : ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype A) 1) ∧
        Subsingleton (groupCohomology (Rep.res H.subtype A) 2)) :
    ∀ r : ℤ, r < 0 → Subsingleton (tateCohomology A r) :=
  subsingleton_tateCohomology_neg_of_posTateVanishing hpos A (posTateVanishing_of_pos A hpos hA)

end Commons.RepresentationTheory.TateCohomology