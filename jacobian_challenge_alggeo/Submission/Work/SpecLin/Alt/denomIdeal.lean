/-
# The denominator ideal of an element of the fraction field

For a commutative ring `A` and an `A`-algebra `K` (in the applications `K` is a field of
fractions of the domain `A`), and an element `x : K`, the **denominator ideal** `denomIdeal x`
is the ideal of those `a : A` for which `x * a` lies in the image of `A` in `K`:

  `denomIdeal x = {a : A | ∃ b : A, x * algebraMap A K a = algebraMap A K b}`.

This is the basic object of the proof that a Noetherian normal domain is the intersection of its
localisations at height one primes (`Work.SpecLin.Alt.normal_eq_iInter_localizations_height_one`):
`x` lies in the image of `A` iff `denomIdeal x = ⊤`, and if `x ∉ A` then the minimal primes of
`denomIdeal x` are the primes that witness the failure, i.e. the primes `p` with `x ∉ A_p`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.SpecLin.Alt

universe u v

/-- The **denominator ideal** of `x : K` with respect to the `A`-algebra `K`: the ideal of all
`a : A` such that `x * a` lies in the image of `A` inside `K`. -/
noncomputable def denomIdeal {A : Type u} [CommRing A] {K : Type v} [CommRing K] [Algebra A K]
    (x : K) : Ideal A :=
  LinearMap.ker ((Submodule.mkQ (Algebra.linearMap A K).range).comp
    ((LinearMap.mulLeft A x).comp (Algebra.linearMap A K)))

theorem mem_denomIdeal {A : Type u} [CommRing A] {K : Type v} [CommRing K] [Algebra A K]
    (x : K) (a : A) :
    a ∈ denomIdeal x ↔ ∃ b : A, x * algebraMap A K a = algebraMap A K b := by
  simp only [denomIdeal, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, LinearMap.mem_range, Algebra.linearMap_apply,
    LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨b, hb⟩; exact ⟨b, hb.symm⟩
  · rintro ⟨b, hb⟩; exact ⟨b, hb.symm⟩

/-- `x` lies in the image of `A` in `K` if and only if its denominator ideal is everything. -/
theorem denomIdeal_eq_top_iff {A : Type u} [CommRing A] {K : Type v} [CommRing K] [Algebra A K]
    (x : K) : (denomIdeal x : Ideal A) = ⊤ ↔ ∃ a : A, x = algebraMap A K a := by
  constructor
  · intro h
    have h1 : (1 : A) ∈ denomIdeal x := by rw [h]; trivial
    rw [mem_denomIdeal] at h1
    obtain ⟨b, hb⟩ := h1
    exact ⟨b, by simpa using hb⟩
  · rintro ⟨a, rfl⟩
    rw [eq_top_iff]
    intro b _
    rw [mem_denomIdeal]
    exact ⟨a * b, by rw [map_mul, mul_comm]⟩

/-- `1` lies in the denominator ideal iff `x` is in the image of `A`. -/
theorem one_mem_denomIdeal_iff {A : Type u} [CommRing A] {K : Type v} [CommRing K] [Algebra A K]
    (x : K) : (1 : A) ∈ denomIdeal x ↔ ∃ a : A, x = algebraMap A K a := by
  rw [mem_denomIdeal]
  constructor
  · rintro ⟨b, hb⟩; exact ⟨b, by simpa using hb⟩
  · rintro ⟨a, rfl⟩; exact ⟨a, by rw [map_one, mul_one]⟩

/-- The denominator ideal of an element of a fraction field is never zero: it contains a
denominator of `x`. -/
theorem denomIdeal_ne_bot {A : Type u} [CommRing A] [IsDomain A] {K : Type v} [Field K]
    [Algebra A K] [IsFractionRing A K] (x : K) : (denomIdeal x : Ideal A) ≠ ⊥ := by
  obtain ⟨a, b, hb, hxab⟩ := IsFractionRing.div_surjective A x
  intro hbot
  have hbD : b ∈ denomIdeal x := by
    rw [mem_denomIdeal]
    refine ⟨a, ?_⟩
    rw [← hxab, div_mul_cancel₀ _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb)]
  have hb0 : b = 0 := by simpa using (show b ∈ (⊥ : Ideal A) from hbot ▸ hbD)
  have hz : (algebraMap A K) b = 0 := by rw [hb0]; simp
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb hz


/-
## The local core of the main theorem

The following statement about `denomIdeal` is the heart of the proof that a Noetherian normal
domain is the intersection of its localisations at height one primes
(`Work.SpecLin.Alt.normal_eq_iInter_localizations_height_one`), and it is *elementary* -- in
particular it does **not** use the theorem being proved (no S2/Serre input), only:

* Krull's theorem on nilpotent radicals (`Ideal.exists_pow_le_of_le_radical_of_fg`),
* the determinant trick (`isIntegral_of_smul_mem_submodule`),
* Krull's principal ideal theorem.

Let `R` be a Noetherian local domain which is integrally closed in a field of fractions `K`, let
`x : K`, `D := denomIdeal x` and `m := IsLocalRing.maximalIdeal R`, and suppose
`D.radical = m`.  Then `m` is principal.

Proof.  (1) `m ≤ D.radical`, `m` is finitely generated and `R` is Noetherian, so
`∃ n, m ^ n ≤ D`.  Take `n` minimal, `c ∈ m ^ (n-1)` with `c ∉ D`, and `y := c * x`.  Then
`{a | ∃ b, y * algebraMap R K a = algebraMap R K b} = m` exactly:
`a ∈ m` gives `a * c ∈ m ^ n ⊆ D`, hence `a * c * x = y * a ∈ R`, and conversely `a ∉ m` is a unit
so `y * a ∈ R` would give `y ∈ R`, i.e. `c ∈ D`.

(2) If for every `a ∈ m` the value `b` with `y * a = algebraMap b` can be taken in `m`, then
`N := m.map (Algebra.linearMap R K)` is a nonzero finitely generated `R`-submodule of `K` with
`y • N ⊆ N`, so `y` is integral over `R` by `isIntegral_of_smul_mem_submodule` and `y ∈ R` by
`IsIntegrallyClosedIn R K`; but then `1 ∈ m`, absurd.

(3) Hence there is `a ∈ m` and `b ∉ m` with `y * algebraMap R K a = algebraMap R K b`.  Then `b`
is a unit of `R`, and for `d ∈ m` the identity `algebraMap b * algebraMap d
= (y * algebraMap d) * algebraMap a` (multiply `y * a = b` by `d` and commute) shows that `d` is
divisible by `a` in `R`; as `a ∈ m` we get `m = Ideal.span {a}`, a principal ideal.
-/

/-- Membership in the localisation of a domain at a submonoid of non-zero-divisors, viewed
inside the fraction field. -/
theorem mem_subalgebra_ofField_iff {A : Type u} [CommRing A] {K : Type v} [Field K] [Algebra A K]
    [IsFractionRing A K] (S : Submonoid A) (hS : S ≤ nonZeroDivisors A) (x : K) :
    x ∈ Localization.subalgebra.ofField K S hS ↔
      ∃ a s : A, ∃ (_ : s ∈ S), x = algebraMap A K a * (algebraMap A K s)⁻¹ :=
  Iff.rfl

end Work.SpecLin.Alt
