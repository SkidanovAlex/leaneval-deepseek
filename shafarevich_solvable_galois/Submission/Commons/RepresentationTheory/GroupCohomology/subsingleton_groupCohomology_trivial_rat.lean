import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.Commons.RepresentationTheory.GroupCohomology.subsingleton_groupCohomology_coind_bot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vanishing of the group cohomology of the trivial rational representation

For a finite group `G` and every `n ≥ 1`, the group cohomology `Hⁿ(G, ℚ)` of the trivial
`ℤ[G]`-module `ℚ` vanishes.

The conceptual reason is that `ℚ` is a `ℚ`-vector space, so `|G|` acts invertibly on it, while
`Hⁿ(G, M)` is killed by `|G|` in positive degrees.  Rather than formalising the transfer
(`cor ∘ res = |G|`), we realise the trivial representation `ℚ` as a *retract* of a module whose
cohomology is already known to vanish, namely the module coinduced from the trivial subgroup
`⊥ ≤ G`:

* `Coind_⊥^G(ℚ)` is the permutation module of all functions `G → ℚ`, with `(g · f)(x) = f (x * g)`
  (the coinduction condition from the trivial subgroup is vacuous), and it is the
  `ℤ[G]`-module underlying the "regular" module `ℚ[G]`;
* the constant functions give a `ℤ[G]`-linear section `i : ℚ ⟶ Coind_⊥^G(ℚ)`, and averaging over
  `G`, `f ↦ |G|⁻¹ ∑_{g ∈ G} f g`, is a `ℤ[G]`-linear retraction `r` with `r ∘ i = id`;
* `Hⁿ⁺¹(G, Coind_⊥^G A) = 0` by Shapiro's lemma, since the trivial group has cohomological
  dimension `0` (this is the shared commons lemma `subsingleton_groupCohomology_coind_bot`).

Since cohomology is functorial in the coefficients, the identity of `Hⁿ(G, ℚ)` factors through
the zero module `Hⁿ(G, Coind_⊥^G ℚ)`, hence `Hⁿ(G, ℚ)` is a subsingleton.
-/

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory

noncomputable section

variable (G : Type) [Group G] [Fintype G]

/-- The trivial `ℤ`-linear representation of `G` on `ℚ`. -/
private abbrev trivRatRep (G : Type) [Group G] : Rep ℤ G := Rep.trivial ℤ G ℚ

/-- The `G`-representation coinduced from the trivial subgroup `⊥ ≤ G` with coefficients in the
trivial representation `ℚ` of `⊥`; its underlying module is the set of all functions `G → ℚ`. -/
private abbrev coindTrivRatRep (G : Type) [Group G] : Rep ℤ G :=
  Rep.coind (⊥ : Subgroup G).subtype (trivRatRep (⊥ : Subgroup G))

/-- Every function `G → ℚ` satisfies the (vacuous) equivariance condition defining the
coinduced module, because the trivial subgroup acts trivially. -/
private lemma mem_coindV_const (G : Type) [Group G] (c : ℚ) :
    (fun _ : G => c) ∈ Representation.coindV (⊥ : Subgroup G).subtype
      (trivRatRep (⊥ : Subgroup G)).ρ := by
  rw [Representation.mem_coindV]
  intro _ _
  simp

/-- The constant-function section `ℚ → Coind_⊥^G(ℚ)`. -/
private def iLin (G : Type) [Group G] : ℚ →ₗ[ℤ] (coindTrivRatRep G).V where
  toFun c := ⟨fun _ => c, mem_coindV_const G c⟩
  map_add' _ _ := Subtype.ext (funext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (funext fun _ => rfl)

private lemma iLin_apply_coe (G : Type) [Group G] (c : ℚ) (g : G) :
    (iLin G c).1 g = c := rfl

/-- The action of `G` on `Coind_⊥^G(ℚ)` sends `f` to `x ↦ f (x * g)`, hence fixes constant
functions: the section `iLin` is `G`-equivariant for the trivial action on `ℚ`. -/
private lemma iLin_intertwining (G : Type) [Group G] (g : G) (c : ℚ) :
    iLin G ((trivRatRep G).ρ g c) = (coindTrivRatRep G).ρ g (iLin G c) := by
  have h1 : (trivRatRep G).ρ g c = c := rfl
  rw [h1]
  apply Subtype.ext
  funext x
  show c = (((coindTrivRatRep G).ρ g) (iLin G c)).1 x
  rw [show (((coindTrivRatRep G).ρ g) (iLin G c)).1 x = (iLin G c).1 (x * g) from rfl]
  rfl

/-- The constant-function section as a morphism of `G`-representations. -/
private def iHom (G : Type) [Group G] : trivRatRep G ⟶ coindTrivRatRep G :=
  Rep.ofHom ⟨iLin G, fun g => LinearMap.ext (fun c => iLin_intertwining G g c)⟩

/-- The inclusion `ℤ ↪ ℚ` makes `m • x = (m : ℚ) * x` for the canonical `ℤ`-module structure
on `ℚ`. -/
private lemma zsmul_rat (m : ℤ) (x : ℚ) : m • x = (m : ℚ) * x := by
  rw [← Int.cast_smul_eq_zsmul (R := ℚ) m x, smul_eq_mul]

private lemma cardQ_ne_zero (G : Type) [Group G] [Fintype G] : ((Fintype.card G : ℚ)) ≠ 0 := by
  have h : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  exact_mod_cast h

/-- The averaging retraction `Coind_⊥^G(ℚ) → ℚ`, `f ↦ |G|⁻¹ ∑_{g ∈ G} f g`.  It is `ℤ`-linear
because `ℚ` is a `ℚ`-vector space. -/
private def rLin (G : Type) [Group G] [Fintype G] : (coindTrivRatRep G).V →ₗ[ℤ] ℚ where
  toFun f := (Fintype.card G : ℚ)⁻¹ * ∑ g : G, f.1 g
  map_add' f f' := by
    have h : (∑ g : G, (f + f').1 g) = (∑ g : G, f.1 g) + (∑ g : G, f'.1 g) := by
      simp only [Submodule.coe_add, Pi.add_apply, Finset.sum_add_distrib]
    rw [h, mul_add]
  map_smul' m f := by
    have h : (∑ g : G, (m • f).1 g) = (m : ℚ) * ∑ g : G, f.1 g := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      show m • f.1 g = (m : ℚ) * f.1 g
      rw [zsmul_rat]
    rw [h]
    show (Fintype.card G : ℚ)⁻¹ * ((m : ℚ) * ∑ g : G, f.1 g) =
      m • ((Fintype.card G : ℚ)⁻¹ * ∑ g : G, f.1 g)
    rw [zsmul_rat]
    ring

private lemma rLin_apply (G : Type) [Group G] [Fintype G] (f : (coindTrivRatRep G).V) :
    rLin G f = (Fintype.card G : ℚ)⁻¹ * ∑ g : G, f.1 g := rfl

/-- The averaging retraction is `G`-equivariant for the trivial action on `ℚ`: reindexing the
sum along the bijection `x ↦ x * g` shows that `∑_x f (x * g) = ∑_y f y`. -/
private lemma rLin_intertwining (G : Type) [Group G] [Fintype G] (g : G)
    (f : (coindTrivRatRep G).V) :
    rLin G ((coindTrivRatRep G).ρ g f) = (trivRatRep G).ρ g (rLin G f) := by
  have htriv : (trivRatRep G).ρ g (rLin G f) = rLin G f := rfl
  rw [htriv, rLin_apply, rLin_apply]
  congr 1
  have hsum : (∑ x : G, (((coindTrivRatRep G).ρ g) f).1 x) = ∑ x : G, f.1 (x * g) :=
    Finset.sum_congr rfl (fun x _ => rfl)
  rw [hsum]
  exact Equiv.sum_comp (Equiv.mulRight g) (fun y => f.1 y)

/-- The averaging retraction as a morphism of `G`-representations. -/
private def rHom (G : Type) [Group G] [Fintype G] : coindTrivRatRep G ⟶ trivRatRep G :=
  Rep.ofHom ⟨rLin G, fun g => LinearMap.ext (fun f => rLin_intertwining G g f)⟩

/-- The averaging retraction indeed retracts the constant-function section: the average of the
constant function with value `c` is `c`. -/
private lemma iHom_rHom (G : Type) [Group G] [Fintype G] :
    iHom G ≫ rHom G = 𝟙 (trivRatRep G) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  show rLin G (iLin G c) = c
  rw [rLin_apply]
  have hsum : (∑ g : G, (iLin G c).1 g) = ∑ _ : G, c :=
    Finset.sum_congr rfl (fun g _ => iLin_apply_coe G c g)
  rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (cardQ_ne_zero G), one_mul]

/-- **Vanishing of the group cohomology of the trivial rational representation.**
For a finite group `G` and `n ≥ 1`, the cohomology `Hⁿ(G, ℚ)` of the trivial `ℤ[G]`-module `ℚ`
vanishes, because `ℚ` is a retract of the coinduced module `Coind_⊥^G(ℚ)` (the permutation module
`ℚ[G]`), whose positive-degree cohomology is zero by Shapiro's lemma. -/
theorem subsingleton_groupCohomology_trivial_rat (G : Type) [Group G] [Fintype G]
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (groupCohomology (Rep.trivial ℤ G ℚ) n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hC : Subsingleton (groupCohomology (coindTrivRatRep G) (m + 1)) :=
    subsingleton_groupCohomology_coind_bot (trivRatRep (⊥ : Subgroup G)) m
  -- the identity of `Hⁿ⁺¹(G, ℚ)` factors through `Hⁿ⁺¹(G, Coind_⊥^G ℚ) = 0`
  have hcomp : groupCohomology.map (MonoidHom.id G) (iHom G) (m + 1) ≫
      groupCohomology.map (MonoidHom.id G) (rHom G) (m + 1) =
        𝟙 (groupCohomology (trivRatRep G) (m + 1)) := by
    rw [← groupCohomology.map_id_comp (iHom G) (rHom G) (m + 1), iHom_rHom G,
      groupCohomology.map_id]
  have hzero : ∀ x : groupCohomology (trivRatRep G) (m + 1), x = 0 := by
    intro x
    have key : (groupCohomology.map (MonoidHom.id G) (rHom G) (m + 1))
        ((groupCohomology.map (MonoidHom.id G) (iHom G) (m + 1)) x) = x := by
      have h := congrArg (fun (φ : groupCohomology (trivRatRep G) (m + 1) ⟶
          groupCohomology (trivRatRep G) (m + 1)) => φ x) hcomp
      simpa using h
    have hx : (groupCohomology.map (MonoidHom.id G) (iHom G) (m + 1)) x = 0 :=
      Subsingleton.elim _ _
    rw [← key, hx]
    simp
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

end

end Commons.RepresentationTheory.GroupCohomology
