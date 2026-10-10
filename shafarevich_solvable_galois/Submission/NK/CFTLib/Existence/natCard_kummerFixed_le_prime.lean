import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer count: `#(Γ₀^{σ}) ≤ p`

This file proves the elementary Kummer-theoretic bound used in the "Kummer count" step of
`NK.CFTLib.Existence.natCard_abelianization_le_of_kummer_orbit` (see
`Submission/Work/CFTLib/Existence/KummerCountNotes.lean`, §(b)).

Setting: `K ⊆ K' ⊆ N` is a tower of fields (`IsScalarTower K K' N`), `p` is a prime,
`σN : N ≃ₐ[K] N`, `a : K'ˣ` and `β₀ : N` satisfy `β₀ ^ p = algebraMap K' N a`, and the orbit of
`β₀` under `σN` generates `N` over `K'`.

The claim is that the set `Γ₀^{σN}` of `K`-automorphisms of `N` which fix `K'` pointwise and
commute with `σN` has at most `p` elements.  The proof is a one-line Kummer argument:

* since `g` fixes `K'` (and `a ∈ K'`), `(g β₀) ^ p = g (β₀ ^ p) = g a = a = β₀ ^ p`, so
  `χ g := g β₀ / β₀` is a `p`-th root of unity of `N`;
* the map `g ↦ χ g` is injective: if `χ g = χ h` then `g β₀ = h β₀`; since `g` and `h` both
  commute with `σN` they agree on the whole `σN`-orbit of `β₀`, hence (by `hgen`) on all of `N`
  over `K'`, so `g = h`;
* the `p`-th roots of unity of a field form a group of order at most `p`
  (`card_rootsOfUnity`).

Nothing here is class field theory; the argument is pure Galois/Kummer theory.
-/

namespace NK.CFTLib.Existence

theorem natCard_kummerFixed_le_prime
    {K K' N : Type*} [Field K] [Field K'] [Field N]
    [Algebra K K'] [Algebra K' N] [Algebra K N] [IsScalarTower K K' N]
    (p : ℕ) [Fact p.Prime] (σN : N ≃ₐ[K] N) (β₀ : N) (a : K'ˣ)
    (hβ₀ : β₀ ^ p = algebraMap K' N (a : K'))
    (hgen : IntermediateField.adjoin K' (Set.range fun i : ℕ => ((σN : N → N)^[i]) β₀) = ⊤) :
    Nat.card {g : N ≃ₐ[K] N // (∀ c : K', g (algebraMap K' N c) = algebraMap K' N c) ∧
      σN * g * σN⁻¹ = g} ≤ p := by
  classical
  have hp : p.Prime := Fact.out
  -- The set of automorphisms under consideration.
  let G : Type _ := {g : N ≃ₐ[K] N // (∀ c : K', g (algebraMap K' N c) = algebraMap K' N c) ∧
      σN * g * σN⁻¹ = g}
  -- An element of `G` commutes with `σN` as a *function*, hence with all its iterates.
  have iterate_apply : ∀ (e : N ≃ₐ[K] N), σN * e * σN⁻¹ = e → ∀ i : ℕ,
      e ((σN : N → N)^[i] β₀) = (σN : N → N)^[i] (e β₀) := by
    intro e he i
    have hcomme : ∀ y, σN (e y) = e (σN y) := by
      intro y
      have h := congrArg (fun (f : N ≃ₐ[K] N) => f (σN y)) he
      simpa using h
    induction i with
    | zero => simp
    | succ i ih =>
      calc e ((σN : N → N)^[i.succ] β₀)
          = e (σN ((σN : N → N)^[i] β₀)) := by rw [Function.iterate_succ_apply']
        _ = σN (e ((σN : N → N)^[i] β₀)) := (hcomme _).symm
        _ = σN ((σN : N → N)^[i] (e β₀)) := by rw [ih]
        _ = (σN : N → N)^[i.succ] (e β₀) := by rw [Function.iterate_succ_apply']
  -- `algebraMap K' N` is injective, so `a ≠ 0` forces `β₀ ≠ 0`.
  have hanne : algebraMap K' N (a : K') ≠ 0 := by
    intro hzero
    have h1 : algebraMap K' N (((a * a⁻¹ : K'ˣ) : K')) = 1 := by
      have : ((a * a⁻¹ : K'ˣ) : K') = 1 := by simp
      rw [this, map_one]
    rw [Units.val_mul, map_mul, hzero, zero_mul] at h1
    exact one_ne_zero h1.symm
  have hβ0ne : β₀ ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero] at hβ₀
    exact hanne hβ₀.symm
  -- The ratio `g β₀ / β₀` is a `p`-th root of unity.
  have hpow : ∀ g : G, ((g.1 β₀) / β₀) ^ p = 1 := by
    intro g
    have h1 : (g.1 β₀) ^ p = algebraMap K' N (a : K') := by
      rw [← map_pow, hβ₀, g.2.1 (a : K')]
    rw [div_pow, h1, hβ₀, div_self hanne]
  -- Ring automorphisms commute with inversion.
  have hinveq : ∀ (e : N ≃ₐ[K] N) (x : N), e x⁻¹ = (e x)⁻¹ := by
    intro e x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hx, map_one])
  -- Injectivity of `g ↦ g β₀ / β₀`: an automorphism of `G` is determined by the image of `β₀`.
  have hinjN : Function.Injective (fun g : G => (g.1 β₀) / β₀) := by
    intro g h hgh
    have hβeq : g.1 β₀ = h.1 β₀ := by
      rw [div_eq_div_iff hβ0ne hβ0ne] at hgh
      exact mul_right_cancel₀ hβ0ne hgh
    refine Subtype.ext (AlgEquiv.ext fun x => ?_)
    have hx : x ∈ IntermediateField.adjoin K' (Set.range fun i : ℕ => ((σN : N → N)^[i]) β₀) := by
      rw [hgen]; exact IntermediateField.mem_top
    refine IntermediateField.adjoin_induction K' ?_ ?_ ?_ ?_ ?_ hx
    · rintro y ⟨i, rfl⟩
      rw [iterate_apply g.1 g.2.2 i, iterate_apply h.1 h.2.2 i, hβeq]
    · intro c
      rw [g.2.1 c, h.2.1 c]
    · intro y z _ _ hy hz
      rw [map_add, map_add, hy, hz]
    · intro y _ hy
      rw [hinveq g.1 y, hinveq h.1 y, hy]
    · intro y z _ _ hy hz
      rw [map_mul, map_mul, hy, hz]
  -- The same map, viewed as taking values in the finite group of `p`-th roots of unity.
  have hinj : Function.Injective
      (fun g : G => rootsOfUnity.mkOfPowEq ((g.1 β₀) / β₀) (hpow g)) := by
    intro g h hgh
    refine hinjN (show (g.1 β₀) / β₀ = (h.1 β₀) / β₀ from ?_)
    have hh := congrArg (fun u : rootsOfUnity p N => ((u : Nˣ) : N)) hgh
    simpa using hh
  calc Nat.card G
      ≤ Nat.card (rootsOfUnity p N) := Nat.card_le_card_of_injective _ hinj
    _ ≤ p := card_rootsOfUnity N p

end NK.CFTLib.Existence
