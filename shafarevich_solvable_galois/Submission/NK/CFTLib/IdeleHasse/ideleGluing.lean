import Mathlib
import Submission.NK.GlobalCFT.Idele
import Submission.NK.HassePrinciple.IdeleCocycle
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Gluing local maps into a map on the idèles

Given a family `f v : K_vˣ →* G` of local maps into a commutative group `G` with the property that
for every idèle `y` the set of places at which `f v (y v) ≠ 1` is finite, we glue them into a
single homomorphism `𝕀[K] →* G`, `y ↦ ∏_v f v (y v)` (a finite product).  This is the standard
construction of the local–global Artin map `Φ = ∏_v λ_v`.

The products are taken in the commutative monoid structure on `G` determined by an explicit
commutativity hypothesis `hcomm`; this keeps the *type* `G →* G`-level structure (and hence all
`MonoidHom`s into `G`) free of instance choices.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.IdeleHasse

open NK.GlobalCFT

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] {ι : Type*}

/-- The product of `f` over a finite set, taken in the commutative monoid structure on `G`
determined by `hcomm`. -/
noncomputable def cprod (hcomm : ∀ x y : G, x * y = y * x) (s : Finset ι) (f : ι → G) : G := by
  letI : CommMonoid G := { ‹Group G› with mul_comm := hcomm }
  exact ∏ i ∈ s, f i

theorem cprod_subset (hcomm : ∀ x y : G, x * y = y * x) {s₁ s₂ : Finset ι} {f : ι → G}
    (h : s₁ ⊆ s₂) (h' : ∀ x ∈ s₂, x ∉ s₁ → f x = 1) :
    cprod hcomm s₁ f = cprod hcomm s₂ f := by
  letI : CommMonoid G := { ‹Group G› with mul_comm := hcomm }
  unfold cprod
  exact Finset.prod_subset h h'

theorem cprod_congr (hcomm : ∀ x y : G, x * y = y * x) {s : Finset ι} {f g : ι → G}
    (h : ∀ i, f i = g i) : cprod hcomm s f = cprod hcomm s g := by
  letI : CommMonoid G := { ‹Group G› with mul_comm := hcomm }
  unfold cprod
  exact Finset.prod_congr rfl fun i _ => h i

theorem cprod_mul (hcomm : ∀ x y : G, x * y = y * x) (s : Finset ι) (f g : ι → G) :
    cprod hcomm s (fun i => f i * g i) = cprod hcomm s f * cprod hcomm s g := by
  letI : CommMonoid G := { ‹Group G› with mul_comm := hcomm }
  unfold cprod
  exact Finset.prod_mul_distrib

theorem cprod_eq_one (hcomm : ∀ x y : G, x * y = y * x) {s : Finset ι} {f : ι → G}
    (h : ∀ i ∈ s, f i = 1) : cprod hcomm s f = 1 := by
  letI : CommMonoid G := { ‹Group G› with mul_comm := hcomm }
  unfold cprod
  exact Finset.prod_eq_one h

theorem cprod_eq_single (hcomm : ∀ x y : G, x * y = y * x) {s : Finset ι} {f : ι → G} (a : ι)
    (h : ∀ b ∈ s, b ≠ a → f b = 1) (h' : a ∉ s → f a = 1) :
    cprod hcomm s f = f a := by
  letI : CommMonoid G := { ‹Group G› with mul_comm := hcomm }
  unfold cprod
  exact Finset.prod_eq_single a h h'

/-- **Gluing local maps.**  A family of local maps `f v : K_vˣ →* G` into a commutative group whose
value is trivial at all but finitely many places glues into a homomorphism `𝕀[K] →* G`. -/
noncomputable def ideleHomOfLocal (hcomm : ∀ x y : G, x * y = y * x)
    (f : ∀ v : Place K, (Place.localField K v)ˣ →* G)
    (hf : ∀ y : Idele K, {v : Place K | f v (y v) ≠ 1}.Finite) : Idele K →* G where
  toFun y := cprod hcomm (hf y).toFinset (fun v => f v (y v))
  map_one' := cprod_eq_one hcomm fun v _ => by rw [Idele.one_apply, map_one]
  map_mul' y z := by
    classical
    have hsub : (hf (y * z)).toFinset ⊆ (hf y).toFinset ∪ (hf z).toFinset := by
      intro v hv
      by_contra hmem
      rw [Finset.mem_union, not_or] at hmem
      obtain ⟨hy, hz⟩ := hmem
      have hy1 : f v (y v) = 1 := by
        by_contra h
        exact hy ((Set.Finite.mem_toFinset _).mpr h)
      have hz1 : f v (z v) = 1 := by
        by_contra h
        exact hz ((Set.Finite.mem_toFinset _).mpr h)
      exact ((Set.Finite.mem_toFinset _).mp hv)
        (by rw [Idele.mul_apply, map_mul, hy1, hz1, one_mul])
    have hS : cprod hcomm (hf (y * z)).toFinset (fun v => f v ((y * z) v))
        = cprod hcomm ((hf y).toFinset ∪ (hf z).toFinset) (fun v => f v ((y * z) v)) :=
      cprod_subset hcomm hsub (fun v _ hv => by
        by_contra h
        exact hv ((Set.Finite.mem_toFinset _).mpr h))
    have hpt : cprod hcomm ((hf y).toFinset ∪ (hf z).toFinset) (fun v => f v ((y * z) v))
        = cprod hcomm ((hf y).toFinset ∪ (hf z).toFinset)
            (fun v => f v (y v) * f v (z v)) :=
      cprod_congr hcomm (fun v => by rw [Idele.mul_apply, map_mul])
    have hmul := cprod_mul hcomm ((hf y).toFinset ∪ (hf z).toFinset)
      (fun v => f v (y v)) (fun v => f v (z v))
    have hy' : cprod hcomm ((hf y).toFinset ∪ (hf z).toFinset) (fun v => f v (y v))
        = cprod hcomm (hf y).toFinset (fun v => f v (y v)) :=
      (cprod_subset hcomm (fun x hx => Finset.mem_union_left _ hx) (fun v _ hv => by
        by_contra h
        exact hv ((Set.Finite.mem_toFinset _).mpr h))).symm
    have hz' : cprod hcomm ((hf y).toFinset ∪ (hf z).toFinset) (fun v => f v (z v))
        = cprod hcomm (hf z).toFinset (fun v => f v (z v)) :=
      (cprod_subset hcomm (fun x hx => Finset.mem_union_right _ hx) (fun v _ hv => by
        by_contra h
        exact hv ((Set.Finite.mem_toFinset _).mpr h))).symm
    rw [hS, hpt, hmul, hy', hz']

@[simp] theorem ideleHomOfLocal_apply (hcomm : ∀ x y : G, x * y = y * x)
    (f : ∀ v : Place K, (Place.localField K v)ˣ →* G)
    (hf : ∀ y : Idele K, {v : Place K | f v (y v) ≠ 1}.Finite) (y : Idele K) :
    ideleHomOfLocal hcomm f hf y = cprod hcomm (hf y).toFinset (fun v => f v (y v)) := rfl

/-- **Value of the glued map at an idèle supported at one place.** -/
theorem ideleHomOfLocal_apply_onePlace (hcomm : ∀ x y : G, x * y = y * x)
    (f : ∀ v : Place K, (Place.localField K v)ˣ →* G)
    (hf : ∀ y : Idele K, {v : Place K | f v (y v) ≠ 1}.Finite) (v : Place K)
    (a : (Place.localField K v)ˣ) :
    ideleHomOfLocal hcomm f hf (NK.HassePrinciple.onePlace v a) = f v a := by
  rw [ideleHomOfLocal_apply]
  have h := cprod_eq_single (hcomm := hcomm) (s := (hf (NK.HassePrinciple.onePlace v a)).toFinset)
    (f := fun w => f w ((NK.HassePrinciple.onePlace v a) w)) v
    (fun b _ hb => by rw [NK.HassePrinciple.onePlace_apply_ne hb, map_one])
    (fun hv => by
      by_contra h
      refine hv ((Set.Finite.mem_toFinset _).mpr ?_)
      show f v ((NK.HassePrinciple.onePlace v a) v) ≠ 1
      simpa using h)
  rw [h, NK.HassePrinciple.onePlace_apply_self]

end NK.CFTLib.IdeleHasse
