import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.LocallyConstant.Basic
import Submission.Work.SSGRoute.finite_homs_of_finite_galoisFields
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Galois-theoretic count behind the Kummer pairing: middle characters vs quotient characters

Let `K'/K` be a separable closure, `p` a prime and `L/K` a Galois subextension of degree `p`.
Write `N := L.fixingSubgroup ≤ Gal(K'/K)`; `N` is normal and open (degree `p` is finite), and
`Gal(K'/K) ⧸ N` has exactly `p` elements.

The characters `χ : Gal(K'/K) →* 𝔽_pˣ` that are locally constant (for the Krull topology),
non-trivial, and have kernel exactly `N` are in canonical bijection with the non-trivial
characters `φ : Gal(K'/K) ⧸ N →* 𝔽_pˣ`:

* `φ ↦ φ ∘ mk'` is well defined because `N` is open, hence `φ ∘ mk'` is constant on the
  (open) cosets of `N`; its kernel is `N` because `φ ≠ 1` forces `φ` to be injective (a
  non-trivial homomorphism between groups of the same prime order);
* `χ ↦ QuotientGroup.lift` is the inverse.

This is the purely group-theoretic count used in the Poitou–Tate lane: it identifies the
"middle" locally constant characters with the characters of the degree-`p` Galois quotient.
-/

namespace Work.SSGRoute.PTembedding

open scoped Topology Pointwise

set_option linter.style.haveILetI false

/-- A group homomorphism out of a topological group whose kernel is open is locally constant:
it is constant on the left cosets of its kernel, and those are open. -/
theorem isLocallyConstant_of_isOpen_kernel {G M : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group M] (χ : G →* M) (h : IsOpen (χ.ker : Set G)) :
    IsLocallyConstant χ := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨x • (χ.ker : Set G), h.smul x, ⟨1, χ.ker.one_mem, by simp⟩, ?_⟩
  rintro y ⟨k, hk, rfl⟩
  change χ (x * k) = χ x
  rw [map_mul, MonoidHom.mem_ker.mp hk, mul_one]

/-- In a group `Q` of prime order `p`, every non-trivial homomorphism to a group of order `p`
is injective: its kernel is a proper subgroup, hence trivial. -/
theorem ker_eq_bot_of_ne_one_of_prime_card (p : ℕ) [Fact p.Prime] {Q : Type*} [Group Q]
    (hQ : Nat.card Q = p) (φ : Q →* Multiplicative (ZMod p)) (hne : φ ≠ 1) :
    φ.ker = ⊥ := by
  haveI : Fact (Nat.card Q).Prime := ⟨by rw [hQ]; exact Fact.out⟩
  rcases (φ.ker).eq_bot_or_eq_top_of_prime_card with h | h
  · exact h
  · exact absurd (MonoidHom.ker_eq_top_iff.mp h) hne

/-- **The count.**  For an open normal subgroup `N` of a topological group `G` with
`Nat.card (G ⧸ N) = p` (`p` prime), the locally constant non-trivial characters `G →* 𝔽_pˣ`
whose kernel is exactly `N` are in bijection with the non-trivial characters of the quotient
`G ⧸ N`. -/
theorem natCard_lcHoms_ker_eq_quotient (p : ℕ) [Fact p.Prime] {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (N : Subgroup G) [N.Normal]
    (hNopen : IsOpen (N : Set G)) (hcard : Nat.card (G ⧸ N) = p) :
    Nat.card {χ : G →* Multiplicative (ZMod p) // IsLocallyConstant χ ∧ χ ≠ 1 ∧ χ.ker = N}
      = Nat.card {φ : G ⧸ N →* Multiplicative (ZMod p) // φ ≠ 1} := by
  have hbot : ∀ φ : G ⧸ N →* Multiplicative (ZMod p), φ ≠ 1 → φ.ker = ⊥ :=
    fun φ hne => ker_eq_bot_of_ne_one_of_prime_card p hcard φ hne
  have hker : ∀ φ : G ⧸ N →* Multiplicative (ZMod p), φ ≠ 1 →
      (φ.comp (QuotientGroup.mk' N)).ker = N := by
    intro φ hne
    rw [← MonoidHom.comap_ker, hbot φ hne, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  let toFun : {χ : G →* Multiplicative (ZMod p) // IsLocallyConstant χ ∧ χ ≠ 1 ∧ χ.ker = N} →
      {φ : G ⧸ N →* Multiplicative (ZMod p) // φ ≠ 1} := fun χ =>
    ⟨QuotientGroup.lift N χ.1 (by rw [χ.2.2.2]), by
      intro h
      exact χ.2.2.1 (by
        have h1 := QuotientGroup.lift_comp_mk' N χ.1 (by rw [χ.2.2.2])
        rw [h] at h1
        simpa using h1.symm)⟩
  let invFun : {φ : G ⧸ N →* Multiplicative (ZMod p) // φ ≠ 1} →
      {χ : G →* Multiplicative (ZMod p) // IsLocallyConstant χ ∧ χ ≠ 1 ∧ χ.ker = N} := fun φ =>
    ⟨φ.1.comp (QuotientGroup.mk' N),
      isLocallyConstant_of_isOpen_kernel _ (by rw [hker φ.1 φ.2]; exact hNopen),
      (by intro h; exact φ.2 (by
        apply MonoidHom.ext
        intro q
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
        simpa using DFunLike.congr_fun h g)),
      hker φ.1 φ.2⟩
  have hleft : Function.LeftInverse invFun toFun := by
    intro χ
    apply Subtype.ext
    change (QuotientGroup.lift N χ.1 (by rw [χ.2.2.2])).comp (QuotientGroup.mk' N) = χ.1
    exact QuotientGroup.lift_comp_mk' N χ.1 (by rw [χ.2.2.2])
  have hright : Function.RightInverse invFun toFun := by
    intro φ
    apply Subtype.ext
    apply MonoidHom.ext
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    dsimp only [toFun, invFun]
    simp
  exact Nat.card_congr ⟨toFun, invFun, hleft, hright⟩

/-- For a degree-`p` Galois subextension `L ⊆ K'` of a separable closure, the locally constant
non-trivial characters of `Gal(K'/K)` with kernel `L.fixingSubgroup` are as numerous as the
non-trivial characters of the quotient `Gal(K'/K) ⧸ L.fixingSubgroup`. -/
theorem natCard_mid_eq_quotientHoms (p : ℕ) [Fact p.Prime] {K F' : Type*} [Field K] [Field F']
    [Algebra K F'] [IsSepClosure K F'] (L : IntermediateField K F') [IsGalois K L]
    (hfr : Module.finrank K L = p) :
    Nat.card {χ : (F' ≃ₐ[K] F') →* Multiplicative (ZMod p) //
        IsLocallyConstant χ ∧ χ ≠ 1 ∧ χ.ker = L.fixingSubgroup}
      = Nat.card {φ : (F' ≃ₐ[K] F') ⧸ L.fixingSubgroup →* Multiplicative (ZMod p) // φ ≠ 1} := by
  haveI hfin : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hfr]; exact (Fact.out : p.Prime).pos)
  have hNopen : IsOpen (L.fixingSubgroup : Set (F' ≃ₐ[K] F')) :=
    IntermediateField.fixingSubgroup_isOpen L
  have hcard : Nat.card ((F' ≃ₐ[K] F') ⧸ L.fixingSubgroup) = p := by
    rw [Work.SSGRoute.natCard_quotient_fixingSubgroup_eq_finrank (K := F') L, hfr]
  exact natCard_lcHoms_ker_eq_quotient p L.fixingSubgroup hNopen hcard

end Work.SSGRoute.PTembedding
