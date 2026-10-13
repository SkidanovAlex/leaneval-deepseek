import Mathlib

namespace Work.DSM7p.Krull

universe a

/-- Krull intersection step: in a Noetherian local ring `A` with maximal ideal `m`, an element of a
finitely generated module `N` that lies in `S ⊔ m ^ k • ⊤` for every `k` already lies in `S`. -/
theorem mem_of_forall_mem_sup_smul_pow {A : Type a} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] {N : Type a} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (S : Submodule A N) {x : N}
    (h : ∀ k : ℕ, x ∈ S ⊔ ((IsLocalRing.maximalIdeal A) ^ k • ⊤)) : x ∈ S := by
  -- Work in the quotient `N ⧸ S`: the hypothesis says the image of `x` lies in `m ^ k • ⊤` for
  -- every `k`, and the intersection of these is `⊥` by Krull for finitely generated modules over a
  -- Noetherian local ring.
  have hm : IsLocalRing.maximalIdeal A ≠ ⊤ :=
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  have hx : Submodule.mkQ S x ∈ (⨅ k : ℕ,
      ((IsLocalRing.maximalIdeal A) ^ k • ⊤ : Submodule A (N ⧸ S))) := by
    rw [Submodule.mem_iInf]
    intro k
    have hk : Submodule.mkQ S x ∈ Submodule.map (Submodule.mkQ S)
        (S ⊔ ((IsLocalRing.maximalIdeal A) ^ k • ⊤ : Submodule A N)) :=
      Submodule.mem_map_of_mem (f := Submodule.mkQ S) (h k)
    rwa [Submodule.map_sup, Submodule.mkQ_map_self, Submodule.map_smul'',
      Submodule.map_top, Submodule.range_mkQ, bot_sup_eq] at hk
  rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal A) hm,
    Submodule.mem_bot] at hx
  have : x ∈ LinearMap.ker (Submodule.mkQ S) := LinearMap.mem_ker.mpr hx
  rwa [Submodule.ker_mkQ] at this

end Work.DSM7p.Krull
