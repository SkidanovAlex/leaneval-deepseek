import Mathlib
import Submission.NK.LocalStructure.Defs

namespace NK.LocalStructure.Frobenius

open scoped Classical Pointwise

universe u

/-! ## The coset transfer of a Frobenius lift

The two lemmas `NK.LocalTame.Basic.isTameFrobeniusLift_mul_mem_inertia` and
`..._of_mul_mem_inertia` record that the set of Frobenius lifts is a union of cosets of the
inertia subgroup, provided the tame inertia is abelian modulo the wild inertia.  The version
below drops the superfluous hypothesis `V ≤ I` (which is *not* used in the argument and is not
available in the hypotheses of `frobeniusLiftCharacterisation_of_core`): one only needs `V`
normal and the commutator condition. -/

/-- **Multiplying a Frobenius lift on the left by an inertia element gives a Frobenius lift.**
Both required properties survive the perturbation:

* `y * x ∉ I`, because `x = y⁻¹ * (y * x)` and `y⁻¹ ∈ I`;
* writing `v = x z x⁻¹ (z ^ q)⁻¹ ∈ V` for `z ∈ I`, we get `x z x⁻¹ = v z ^ q`, whence
  `(y x) z (y x)⁻¹ (z ^ q)⁻¹ = (y v y⁻¹) · (y z ^ q y⁻¹ (z ^ q)⁻¹)`,
  the first factor lying in `V` because `V` is normal and the second by the commutator
  hypothesis applied to `y, z ^ q ∈ I`. -/
theorem isTameFrobeniusLift_mul_of_mem_inertia {G : Type u} [Group G] {q : ℕ} {V I : Subgroup G}
    (hV : V.Normal) (hab : ∀ y ∈ I, ∀ z ∈ I, y * z * y⁻¹ * z⁻¹ ∈ V) {x y : G}
    (h : NK.LocalTame.IsTameFrobeniusLift q V I x) (hy : y ∈ I) :
    NK.LocalTame.IsTameFrobeniusLift q V I (y * x) := by
  obtain ⟨hxI, hact⟩ := h
  refine ⟨?_, ?_⟩
  · intro hmem
    refine hxI ?_
    have hx_eq : x = y⁻¹ * (y * x) := by group
    rw [hx_eq]
    exact I.mul_mem (I.inv_mem hy) hmem
  · intro z hz
    have hv : x * z * x⁻¹ * (z ^ q)⁻¹ ∈ V := hact z hz
    have h1 : y * (x * z * x⁻¹ * (z ^ q)⁻¹) * y⁻¹ ∈ V := hV.conj_mem _ hv y
    have h2 : y * z ^ q * y⁻¹ * (z ^ q)⁻¹ ∈ V := hab y hy (z ^ q) (I.pow_mem hz q)
    have heq : (y * x) * z * (y * x)⁻¹ * (z ^ q)⁻¹
        = y * (x * z * x⁻¹ * (z ^ q)⁻¹) * y⁻¹ * (y * z ^ q * y⁻¹ * (z ^ q)⁻¹) := by
      group
    rw [heq]
    exact V.mul_mem h1 h2

/-- **The Frobenius normalisation (NSW (12.1.8) Lemma; Iwasawa).**

An element of `G_κ = Gal(K'/κ)` acts on the prime-to-`p` roots of unity by `ζ ↦ ζ ^ q` — i.e. is
a Frobenius element for the residue field of cardinality `q` — if and only if it lies outside the
inertia subgroup `I_κ` and conjugates the tame inertia `I_κ / V_κ` by the `q`-th power map.

The non-trivial direction is `(⇒)`.  Let `x` be a Frobenius element.  The core hypothesis
`h.exists_frob` supplies a *normalised* Frobenius lift `x₀` — it both acts on the roots of unity
by `ζ ↦ ζ ^ q` and conjugates `I_κ / V_κ` by the `q`-th power map — and the two halves of the
`(12.1.8)` input reduce the general case to it:

* `x * x₀⁻¹` acts trivially on the prime-to-`p` roots of unity, hence lies in the inertia
  subgroup `I_κ` (which by construction is the kernel of that action), so `x` differs from the
  normalised `x₀` by an inertia element;
* the inertia subgroup acts trivially on `I_κ / V_κ` — this is the commutator hypothesis `hcomm`:
  `I_κ / V_κ` is pro-cyclic, hence abelian, so the conjugation action of `I_κ` on its own quotient
  by `V_κ` is trivial (NSW (7.5.7) Corollary).

The direction `(⇐)` is the `actsAsFrobenius_of_isTameFrobeniusLift` half of the core input. -/
theorem frobeniusLiftCharacterisation_of_core {κ K' : Type*} [Field κ]
    [Field K'] [Algebra κ K'] [IsSepClosure κ K'] {p q : ℕ}
    (h : NK.LocalStructure.TameFrobeniusCore p q κ K')
    (hcomm : ∀ y ∈ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p,
      ∀ z ∈ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p,
      y * z * y⁻¹ * z⁻¹ ∈ NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p) :
    NK.LocalTame.FrobeniusLiftCharacterisation p q κ K' := by
  obtain ⟨x₀, hx₀frob, hx₀lift⟩ := h.exists_frob
  refine ⟨h.hp, fun x => ⟨?_, ?_⟩⟩
  · -- `(⇒)`: a Frobenius element is a Frobenius lift.
    intro hx
    -- The quotient `x * x₀⁻¹` acts trivially on the prime-to-`p` roots of unity.
    have ha : x * x₀⁻¹ ∈ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p := by
      intro n hn ζ hζ
      have hζ' : IsPrimitiveRoot (x₀⁻¹ ζ) n := hζ.map_of_injective (x₀⁻¹).injective
      calc (x * x₀⁻¹) ζ = x (x₀⁻¹ ζ) := rfl
        _ = (x₀⁻¹ ζ) ^ q := hx.2 n hn (x₀⁻¹ ζ) hζ'
        _ = ζ := by
            have h₁ := hx₀frob.2 n hn (x₀⁻¹ ζ) hζ'
            rw [← h₁]
            exact AlgEquiv.apply_symm_apply x₀ ζ
    have hx_eq : (x * x₀⁻¹) * x₀ = x := by group
    rw [← hx_eq]
    exact isTameFrobeniusLift_mul_of_mem_inertia
      (NK.LocalTame.wildInertiaSubgroup_normal (κ := κ) (K' := K') p) hcomm hx₀lift ha
  · -- `(⇐)`: a Frobenius lift acts on the roots of unity by `ζ ↦ ζ ^ q` and misses `I_κ`.
    intro hx
    exact ⟨hx.1, h.actsAsFrobenius_of_isTameFrobeniusLift x hx⟩

end NK.LocalStructure.Frobenius
