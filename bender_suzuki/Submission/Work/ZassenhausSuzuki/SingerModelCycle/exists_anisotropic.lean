/-
# Existence of an anisotropic `ε` over a finite field of characteristic two

Appendix VIII of Peterfalvi I needs, for the definition of the Suzuki groups
`Aut(B(n,1,ε))`, a value `ε` in a finite field `F` of characteristic `2` for which the
quadratic form `(a,b) ↦ a² + εab + b²` is anisotropic.  This file proves that such an `ε`
always exists (i.e. `Anisotropic F ε` holds for some `ε : F`).

The argument is elementary:

* `X² + εX + 1` has a root `t` iff `ε = t + t⁻¹` (for `t ≠ 0`), so anisotropy of `ε` is
  equivalent to the absence of roots of `X² + εX + 1`;
* substituting `u = t/ε` for `ε ≠ 0`, a root of `X² + εX + 1` is the same thing as a
  solution of the Artin–Schreier equation `u² + u = ε⁻²`;
* in a finite field of characteristic `2` the map `u ↦ u² + u` is *not* surjective (it is
  not injective: `0` and `1` both map to `0`, and on a finite type injective and
  surjective are equivalent), while `x ↦ x²` *is* surjective (it is injective because
  `x² = y²` forces `(x+y)² = 0`);
* hence, choosing `v` outside the image of `u ↦ u² + u` and `s` with `s² = v⁻¹`, we get
  `s⁻² = v`, so `X² + sX + 1` has no root and `s` is anisotropic.
-/
import Mathlib
import Submission.Work.Hering.AppVIII.QuadExt

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.SingerModelCycle

open Work.Hering.AppVIII

/-- In a field of characteristic two, `(x + y)² = x² + y²`. -/
lemma add_mul_self (F : Type*) [Field F] [CharP F 2] (x y : F) :
    (x + y) * (x + y) = x * x + y * y := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (x * y) * h2

/-- In a finite field of characteristic two, every element is a square: the map `x ↦ x²`
is injective, because `x² = y²` implies `(x + y)² = 0`, hence `x = y`. -/
lemma exists_sq (F : Type*) [Field F] [CharP F 2] [Finite F] (y : F) : ∃ x : F, x * x = y := by
  have hinj : Function.Injective (fun x : F => x * x) := by
    intro x z hxz
    change x * x = z * z at hxz
    have h : (x + z) * (x + z) = 0 := by
      rw [add_mul_self F x z, hxz, CharTwo.add_self_eq_zero]
    have h0 : x + z = 0 := mul_self_eq_zero.mp h
    have h1 : x = -z := eq_neg_of_add_eq_zero_left h0
    rwa [CharTwo.neg_eq] at h1
  exact (Finite.injective_iff_surjective (f := fun x : F => x * x)).mp hinj y

/-- In a finite field of characteristic two the Artin–Schreier map `u ↦ u² + u` is not
surjective: it is not injective (`0` and `1` have the same image), and a self-map of a
finite type is injective if and only if it is surjective. -/
lemma exists_not_artinSchreier (F : Type*) [Field F] [CharP F 2] [Finite F] :
    ∃ v : F, ∀ u : F, u * u + u ≠ v := by
  by_contra h
  push Not at h
  have hsurj : Function.Surjective (fun u : F => u * u + u) := h
  have hinj := (Finite.injective_iff_surjective (f := fun u : F => u * u + u)).mpr hsurj
  have h01 : (fun u : F => u * u + u) 0 = (fun u : F => u * u + u) 1 := by
    simp [CharTwo.add_self_eq_zero]
  exact zero_ne_one (hinj h01)

/-- Anisotropy of `ε` is equivalent to the polynomial `X² + εX + 1` having no root: a
nontrivial zero `(a, b)` of the form can be normalised to a root `a/b`. -/
lemma anisotropic_iff_no_root (F : Type*) [Field F] [CharP F 2] (ε : F) :
    Anisotropic F ε ↔ ∀ t : F, t * t + ε * t + 1 ≠ 0 := by
  constructor
  · intro h t ht
    have h1 := h t 1 (by simpa using ht)
    exact one_ne_zero h1.2
  · intro h a b hab
    by_cases hb : b = 0
    · subst hb
      simp only [mul_zero, add_zero] at hab
      exact ⟨mul_self_eq_zero.mp hab, rfl⟩
    · exfalso
      have hbb : b * b ≠ 0 := mul_ne_zero hb hb
      have key : (b * b) * ((a / b) * (a / b) + ε * (a / b) + 1)
          = a * a + ε * (a * b) + b * b := by
        field_simp
      rw [hab] at key
      have hz : (a / b) * (a / b) + ε * (a / b) + 1 = 0 :=
        (mul_eq_zero.mp key).resolve_left hbb
      exact h (a / b) hz

/-- For `ε ≠ 0`, a root of `X² + εX + 1` is the same thing as a solution of the
Artin–Schreier equation `u² + u = ε⁻²` (substitute `u = t/ε`). -/
lemma exists_root_iff_artinSchreier (F : Type*) [Field F] [CharP F 2] {ε : F} (hε : ε ≠ 0) :
    (∃ t : F, t * t + ε * t + 1 = 0) ↔ ∃ u : F, u * u + u = (ε * ε)⁻¹ := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t / ε, ?_⟩
    have h1 : t * t + ε * t = 1 := by
      have h := eq_neg_of_add_eq_zero_left ht
      rwa [CharTwo.neg_eq] at h
    field_simp
    linear_combination h1
  · rintro ⟨u, hu⟩
    refine ⟨ε * u, ?_⟩
    have h2 : (ε * ε) * ((ε * ε)⁻¹) = 1 := mul_inv_cancel₀ (mul_ne_zero hε hε)
    have key : (ε * u) * (ε * u) + ε * (ε * u) + 1 = (ε * ε) * (u * u + u) + 1 := by ring
    rw [key, hu, h2, CharTwo.add_self_eq_zero]

theorem exists_anisotropic (F : Type*) [Field F] [CharP F 2] [Finite F] :
    ∃ ε : F, Work.Hering.AppVIII.Anisotropic F ε := by
  obtain ⟨v, hv⟩ := exists_not_artinSchreier F
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 := hv 0
    rw [h0] at h1
    simp at h1
  obtain ⟨s, hs⟩ := exists_sq F v⁻¹
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h1 : (0 : F) = v⁻¹ := by simpa using hs
    exact inv_ne_zero hv0 h1.symm
  refine ⟨s, ?_⟩
  rw [anisotropic_iff_no_root F s]
  intro t ht
  obtain ⟨u, hu⟩ := (exists_root_iff_artinSchreier F hs0).mp ⟨t, ht⟩
  exact hv u (by rw [hu, hs, inv_inv])

end Work.ZassenhausSuzuki.SingerModelCycle
