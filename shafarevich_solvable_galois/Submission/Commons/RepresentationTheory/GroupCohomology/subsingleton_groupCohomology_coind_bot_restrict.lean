import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.Commons.RepresentationTheory.GroupCohomology.subsingleton_groupCohomology_coind_bot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vanishing of the group cohomology of a restricted coinduced representation

Let `G` be a group, `S ≤ G` a subgroup and `A` a `ℤ`-linear representation of the trivial
subgroup `⊥ ≤ G`.  In this file we prove that

`Hⁿ⁺¹(S, Res_S(Coind_⊥^G A)) = 0`

for every `n`.

The proof decomposes the `S`-representation `Res_S(Coind_⊥^G A)` as the permutation module
`Map(G, A)` of functions `G → A`, on which `S` acts by `(s · f)(g) = f (g * s)`.  Since `S`
acts *freely* on `G` by right multiplication, every right coset `gS` is a free transitive
`S`-set, so choosing a representative `c(q)` of every orbit `q` exhibits an isomorphism of
`S`-representations

`Map(G, A) ≅ Map(S, Map(G/S, A)) = Coind_⊥^S (Map(G/S, A)),`

where the right hand side is the coinduction from the *trivial* subgroup of `S` of the
trivial representation on the module `Map(G/S, A)`.  Shapiro's lemma then computes
`Hⁿ⁺¹(S, Coind_⊥^S B) ≅ Hⁿ⁺¹(⊥, B) = 0` because the trivial group has cohomological
dimension `0`.

Besides the target theorem, this file provides the coset machinery used in the proof
(the right coset setoid, representatives, and the "factor" of an element of `G`).
-/

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory

universe u

variable {G : Type u} [Group G] (S : Subgroup G)

/-! ### The right coset decomposition of `G` along `S` -/

/-- The relation whose classes are the right cosets `gS` of `S` in `G`: `a ≈ b` iff
`a⁻¹ * b ∈ S`. -/
def supersingletonRcosetRel : G → G → Prop := fun a b => a⁻¹ * b ∈ S

lemma supersingletonRcosetRel_equiv : Equivalence (supersingletonRcosetRel S) where
  refl a := by simp [supersingletonRcosetRel]
  symm := by intro a b h; simpa [supersingletonRcosetRel] using S.inv_mem h
  trans := by intro a b c hab hbc
              simpa [supersingletonRcosetRel, mul_assoc] using S.mul_mem hab hbc

/-- The setoid of right cosets of `S` in `G`. -/
def supersingletonRcosetSetoid : Setoid G :=
  ⟨supersingletonRcosetRel S, supersingletonRcosetRel_equiv S⟩

/-- The type of right cosets of `S` in `G`. -/
abbrev SupersingletonRCoset : Type u := Quotient (supersingletonRcosetSetoid S)

/-- A chosen representative of a right coset. -/
noncomputable def supersingletonRCosetRep (q : SupersingletonRCoset S) : G := Quotient.out q

lemma supersingletonRCosetRep_mk (q : SupersingletonRCoset S) :
    Quotient.mk (supersingletonRcosetSetoid S) (supersingletonRCosetRep S q) = q :=
  Quotient.out_eq q

/-- For `g : G`, the element `s ∈ S` with `g = c(gS) * s`, where `c(gS)` is the chosen
representative of the right coset of `g`. -/
noncomputable def supersingletonRcosetFactor (g : G) : S :=
  ⟨(supersingletonRCosetRep S (Quotient.mk (supersingletonRcosetSetoid S) g))⁻¹ * g,
    Quotient.exact (Quotient.out_eq (Quotient.mk (supersingletonRcosetSetoid S) g))⟩

lemma supersingletonRCosetRep_mul_factor (g : G) :
    supersingletonRCosetRep S (Quotient.mk (supersingletonRcosetSetoid S) g) *
      (supersingletonRcosetFactor S g : G) = g := by
  simp [supersingletonRcosetFactor]

lemma supersingletonRCoset_mk_rep_mul (q : SupersingletonRCoset S) (s : S) :
    Quotient.mk (supersingletonRcosetSetoid S)
        (supersingletonRCosetRep S q * (s : G)) = q := by
  calc Quotient.mk (supersingletonRcosetSetoid S)
          (supersingletonRCosetRep S q * (s : G))
      = Quotient.mk (supersingletonRcosetSetoid S) (supersingletonRCosetRep S q) := by
        apply Quotient.sound
        change (supersingletonRCosetRep S q * (s : G))⁻¹ * supersingletonRCosetRep S q ∈ S
        have h : (supersingletonRCosetRep S q * (s : G))⁻¹ * supersingletonRCosetRep S q
            = (s : G)⁻¹ := by group
        rw [h]; exact S.inv_mem s.2
    _ = q := supersingletonRCosetRep_mk S q

lemma supersingletonRCosetFactor_rep_mul (q : SupersingletonRCoset S) (s : S) :
    supersingletonRcosetFactor S (supersingletonRCosetRep S q * (s : G)) = s := by
  apply Subtype.ext
  simp only [supersingletonRcosetFactor]
  rw [supersingletonRCoset_mk_rep_mul S q s]
  group

/-! ### The coefficient representation -/

/-- The `S`-representation coinduced from the trivial subgroup with values in the "coset
module" `G/S → A`. -/
abbrev supersingletonCoindCoeff (A : Rep ℤ (⊥ : Subgroup G)) : Rep ℤ (⊥ : Subgroup S) :=
  Rep.trivial ℤ (⊥ : Subgroup S) (SupersingletonRCoset S → A.V)

/-! ### The isomorphism `Res_S(Coind_⊥^G A) ≅ Coind_⊥^S (G/S → A)` -/

variable (A : Rep ℤ (⊥ : Subgroup G))

/-- The underlying module of `Res_S(Coind_⊥^G A)`. -/
abbrev supersingletonResCoindBot :=
  (Rep.res S.subtype (Rep.coind (⊥ : Subgroup G).subtype A)).V

/-- The underlying module of `Coind_⊥^S (G/S → A)`. -/
abbrev supersingletonCoindBotCoeff :=
  (Rep.coind (⊥ : Subgroup S).subtype (supersingletonCoindCoeff S A)).V

section Equiv

/-- Pin the `ℤ`-module structures to those coming from the two representations. -/
noncomputable local instance supersingletonModuleM : Module ℤ (supersingletonResCoindBot S A) :=
  (Rep.res S.subtype (Rep.coind (⊥ : Subgroup G).subtype A)).hV2

noncomputable local instance supersingletonModuleN : Module ℤ (supersingletonCoindBotCoeff S A) :=
  (Rep.coind (⊥ : Subgroup S).subtype (supersingletonCoindCoeff S A)).hV2

/-- The forward map `f ↦ ((s, q) ↦ f (c(q) * s))`. -/
noncomputable def supersingletonResCoindBotToFun
    (f : supersingletonResCoindBot S A) : supersingletonCoindBotCoeff S A :=
  ⟨fun s q => f.1 (supersingletonRCosetRep S q * (s : G)), by
    rw [Representation.mem_coindV]
    intro g h
    have hg : (g : S) = 1 := Subgroup.mem_bot.mp g.2
    simp [hg]⟩

/-- The inverse map `φ ↦ (g ↦ φ (g⁻¹ c(gS)) (gS))`. -/
noncomputable def supersingletonResCoindBotInvFun
    (φ : supersingletonCoindBotCoeff S A) : supersingletonResCoindBot S A :=
  ⟨fun g => φ.1 (supersingletonRcosetFactor S g)
      (Quotient.mk (supersingletonRcosetSetoid S) g), by
    rw [Representation.mem_coindV]
    intro g h
    have hg1 : g = 1 := Subsingleton.elim g 1
    simp [hg1]⟩

/-- The underlying additive equivalence realising `Res_S(Coind_⊥^G A) ≅ Coind_⊥^S (G/S → A)`. -/
noncomputable def supersingletonResCoindBotAddEquiv :
    supersingletonResCoindBot S A ≃+ supersingletonCoindBotCoeff S A where
  toFun := supersingletonResCoindBotToFun S A
  invFun := supersingletonResCoindBotInvFun S A
  left_inv f := by
    apply Subtype.ext
    funext g
    show f.1 (supersingletonRCosetRep S (Quotient.mk (supersingletonRcosetSetoid S) g) *
        (supersingletonRcosetFactor S g : G)) = f.1 g
    rw [supersingletonRCosetRep_mul_factor S]
  right_inv φ := by
    apply Subtype.ext
    funext s q
    show φ.1 (supersingletonRcosetFactor S (supersingletonRCosetRep S q * (s : G)))
        (Quotient.mk (supersingletonRcosetSetoid S) (supersingletonRCosetRep S q * (s : G)))
      = φ.1 s q
    rw [supersingletonRCosetFactor_rep_mul S, supersingletonRCoset_mk_rep_mul S]
  map_add' f g := by ext s q; rfl

/-- The underlying linear equivalence realising `Res_S(Coind_⊥^G A) ≅ Coind_⊥^S (G/S → A)`.
Every additive map between `ℤ`-modules is `ℤ`-linear, so no extra work is needed. -/
noncomputable def supersingletonResCoindBotLinearEquiv :
    supersingletonResCoindBot S A ≃ₗ[ℤ] supersingletonCoindBotCoeff S A :=
  AddEquiv.toIntLinearEquiv (supersingletonResCoindBotAddEquiv S A)

lemma supersingletonResCoindBotLinearEquiv_apply (f : supersingletonResCoindBot S A) (s : S)
    (q : SupersingletonRCoset S) :
    (supersingletonResCoindBotLinearEquiv S A f).1 s q =
      f.1 (supersingletonRCosetRep S q * (s : G)) := rfl

/-- The action of the `G`-representation `Coind_⊥^G A` on the underlying functions. -/
lemma supersingletonCoindBot_apply_coe (h : G) (f : supersingletonResCoindBot S A) (x : G) :
    (((Rep.coind (⊥ : Subgroup G).subtype A).ρ h) f).1 x = f.1 (x * h) := rfl

/-- The action of the `S`-representation `Coind_⊥^S (G/S → A)` on the underlying functions. -/
lemma supersingletonCoindS_apply_coe (h : S) (f : supersingletonCoindBotCoeff S A) (x : S)
    (q : SupersingletonRCoset S) :
    (((Rep.coind (⊥ : Subgroup S).subtype (supersingletonCoindCoeff S A)).ρ h) f).1 x q =
      f.1 (x * h) q := rfl

/-- The linear equivalence is `S`-equivariant. -/
lemma supersingletonResCoindBotLinearEquiv_equivariant (s : S)
    (f : supersingletonResCoindBot S A) :
    supersingletonResCoindBotLinearEquiv S A
        (((Rep.res S.subtype (Rep.coind (⊥ : Subgroup G).subtype A)).ρ s) f)
      = ((Rep.coind (⊥ : Subgroup S).subtype (supersingletonCoindCoeff S A)).ρ s)
          (supersingletonResCoindBotLinearEquiv S A f) := by
  show supersingletonResCoindBotLinearEquiv S A
        (((Rep.coind (⊥ : Subgroup G).subtype A).ρ (S.subtype s)) f)
      = ((Rep.coind (⊥ : Subgroup S).subtype (supersingletonCoindCoeff S A)).ρ s)
          (supersingletonResCoindBotLinearEquiv S A f)
  apply Subtype.ext
  funext s' q
  rw [supersingletonResCoindBotLinearEquiv_apply, supersingletonCoindBot_apply_coe,
    supersingletonCoindS_apply_coe, supersingletonResCoindBotLinearEquiv_apply]
  show f.1 ((supersingletonRCosetRep S q * (s' : G)) * (s : G))
      = f.1 (supersingletonRCosetRep S q * ((s' * s : S) : G))
  rw [mul_assoc]
  rfl

/-- Group cohomology of the restriction to `S` of a representation coinduced from the trivial
subgroup vanishes in positive degrees.  Indeed, `Res_S(Coind_⊥^G A)` is the permutation module
`Map(G, A)`, which splits as a product of copies of `Coind_⊥^S A` indexed by the right cosets
of `S`; equivalently `Res_S(Coind_⊥^G A) ≅ Coind_⊥^S (G/S → A)`, and Shapiro's lemma identifies
`Hⁿ⁺¹(S, Coind_⊥^S B)` with `Hⁿ⁺¹(⊥, B)`, which vanishes because the trivial group has
cohomological dimension `0`. -/
theorem subsingleton_groupCohomology_coind_bot_restrict {G : Type} [Group G] (S : Subgroup G)
    (A : Rep ℤ (⊥ : Subgroup G)) (n : ℕ) :
    Subsingleton (groupCohomology
      (Rep.res S.subtype (Rep.coind (⊥ : Subgroup G).subtype A)) (n + 1)) := by
  have hN : Subsingleton (groupCohomology
      (Rep.coind (⊥ : Subgroup S).subtype (supersingletonCoindCoeff S A)) (n + 1)) :=
    subsingleton_groupCohomology_coind_bot (supersingletonCoindCoeff S A) n
  have h := groupCohomology.mapIso (MulEquiv.refl S)
    (supersingletonResCoindBotLinearEquiv S A)
    (fun g => LinearMap.ext (fun f => by
      simpa using supersingletonResCoindBotLinearEquiv_equivariant S A g f)) (n + 1)
  exact ⟨fun a b => h.toLinearEquiv.injective
    (hN.elim (h.toLinearEquiv a) (h.toLinearEquiv b))⟩

end Equiv

end Commons.RepresentationTheory.GroupCohomology