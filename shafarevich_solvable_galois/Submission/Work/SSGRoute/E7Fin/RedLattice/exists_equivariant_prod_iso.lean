import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E7Fin.RedLattice

theorem exists_equivariant_prod_iso (p : ℕ) [Fact p.Prime] {G : Type} [Group G]
    {N₁ N₂ N₃ : Type}
    [AddCommGroup N₁] [Module (ZMod p) N₁] [DistribMulAction G N₁] [SMulCommClass G (ZMod p) N₁]
    [AddCommGroup N₂] [Module (ZMod p) N₂] [DistribMulAction G N₂] [SMulCommClass G (ZMod p) N₂]
    [AddCommGroup N₃] [Module (ZMod p) N₃] [DistribMulAction G N₃] [SMulCommClass G (ZMod p) N₃]
    (i : N₁ →ₗ[ZMod p] N₂) (j : N₂ →ₗ[ZMod p] N₃)
    (hi : Function.Injective i) (hker : LinearMap.ker j = LinearMap.range i)
    (hieq : ∀ (g : G) (m : N₁), i (g • m) = g • i m)
    (hjeq : ∀ (g : G) (n : N₂), j (g • n) = g • j n)
    (s : N₃ →ₗ[ZMod p] N₂) (hsj : ∀ c, j (s c) = c)
    (hseq : ∀ (g : G) (c : N₃), s (g • c) = g • s c) :
    ∃ e : (N₁ × N₃) ≃ₗ[ZMod p] N₂, ∀ (g : G) (x : N₁ × N₃), e (g • x) = g • e x := by
  -- The candidate linear map `e (x, c) = i x + s c`.
  let e : (N₁ × N₃) →ₗ[ZMod p] N₂ :=
    i.comp (LinearMap.fst (ZMod p) N₁ N₃) + s.comp (LinearMap.snd (ZMod p) N₁ N₃)
  have he : ∀ (x : N₁) (c : N₃), e (x, c) = i x + s c := by
    intro x c; simp [e]
  -- `j ∘ i = 0` because the image of `i` is the kernel of `j`.
  have hji : ∀ a, j (i a) = 0 := fun a => by
    have h : i a ∈ LinearMap.ker j := by rw [hker]; exact LinearMap.mem_range.mpr ⟨a, rfl⟩
    exact LinearMap.mem_ker.mp h
  -- Injectivity: recover the components using `j` and `i`.
  have hinj : Function.Injective e := by
    intro u v huv
    obtain ⟨a, c⟩ := u
    obtain ⟨a', c'⟩ := v
    rw [he, he] at huv
    have hc : c = c' := by
      have h3 := congrArg j huv
      rwa [map_add, map_add, hji, hji, hsj, hsj, zero_add, zero_add] at h3
    subst hc
    have ha : a = a' := by
      apply hi
      have h2 := add_right_cancel huv
      simpa using h2
    subst ha
    rfl
  -- Surjectivity: `n - s (j n)` lies in the kernel of `j`, hence in the image of `i`.
  have hsurj : Function.Surjective e := by
    intro n
    have hmem : n - s (j n) ∈ LinearMap.range i := by
      rw [← hker]
      exact LinearMap.mem_ker.mpr (by rw [map_sub, hsj]; abel)
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hmem
    exact ⟨(a, j n), by rw [he, ha]; abel⟩
  -- Equivariance of `e` follows from the equivariance of `i` and of `s`.
  have heq : ∀ (g : G) (x : N₁ × N₃), e (g • x) = g • e x := by
    rintro g ⟨a, c⟩
    rw [Prod.smul_mk, he, he]
    rw [smul_add, ← hieq, ← hseq]
  have hbij : Function.Bijective e := ⟨hinj, hsurj⟩
  refine ⟨LinearEquiv.ofBijective e hbij, ?_⟩
  intro g x
  simp only [LinearEquiv.ofBijective_apply, heq]

end Work.SSGRoute.E7Fin.RedLattice
