import Mathlib

namespace NK.Mine

/-- If `U ≤ G` is a subgroup containing all `m`-th powers of `G`, and `ψ : U →* H` is a
surjective homomorphism into a commutative group `H` of exponent dividing `N`, and `m * e ≡ 1`
modulo `N`, then `ψ` extends to a surjective homomorphism `G →* H`.

Concretely, `f x = ψ (x ^ m) ^ e`, which is a homomorphism because `G` and `H` are abelian,
restricts to `ψ` on `U` (there `ψ (x^m)^e = ψ x ^ (m*e) = ψ x`), and is surjective because `ψ`
is. -/
theorem exists_surjective_hom_of_subgroup_index_mul {G H : Type*} [CommGroup G] [CommGroup H]
    (U : Subgroup G) {m e N : ℕ} (hU : ∀ a : G, a ^ m ∈ U) (hH : ∀ y : H, y ^ N = 1)
    (hme : m * e ≡ 1 [MOD N]) (ψ : U →* H) (hψ : Function.Surjective ψ) :
    ∃ f : G →* H, Function.Surjective f := by
  -- the `m`-th power map `G → U`, a homomorphism since `G` is abelian
  let pm : G →* U := MonoidHom.mk' (fun a => ⟨a ^ m, hU a⟩) (by
    intro a b
    ext
    simp [mul_pow])
  -- the `e`-th power map on `H`, a homomorphism since `H` is abelian
  let pe : H →* H := MonoidHom.mk' (fun y => y ^ e) (by
    intro a b
    rw [mul_pow])
  refine ⟨pe.comp (ψ.comp pm), ?_⟩
  intro y
  obtain ⟨u, rfl⟩ := hψ y
  refine ⟨(u : G), ?_⟩
  -- `ψ (pm u) = (ψ u) ^ m`
  have hu : ψ (pm (u : G)) = (ψ u) ^ m := by
    have h : pm (u : G) = u ^ m := by ext; simp [pm]
    rw [h, map_pow]
  -- `(ψ u) ^ (m * e) = ψ u` because the order of `ψ u` divides `N`
  have hord : orderOf (ψ u) ∣ N := orderOf_dvd_of_pow_eq_one (hH (ψ u))
  have hmod : m * e ≡ 1 [MOD orderOf (ψ u)] := Nat.ModEq.of_dvd hord hme
  have hpow : (ψ u) ^ (m * e) = ψ u := by
    simpa using (pow_eq_pow_iff_modEq).mpr hmod
  show pe (ψ (pm (u : G))) = ψ u
  rw [hu]
  show ((ψ u) ^ m) ^ e = ψ u
  rw [← pow_mul, hpow]

end NK.Mine
