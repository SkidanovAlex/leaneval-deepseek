import Mathlib.Algebra.Algebra.ZMod
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.PicardGroup
import Submission.Commons.LinearAlgebra.Alternating.nonsingular_subspace_card_sq_le

namespace Commons.LinearAlgebra.Alternating

open LinearMap

/-- **A simple `G`-module carrying a spanning alternating `G`-invariant form with trivial radical
into `A` satisfies `|A|² ≤ |V|`.**

The dual of `β` embeds `A^*` into the space of alternating forms `V →ₗ V →ₗ 𝔽_p`; the image `L`
consists of `G`-invariant forms, and every nonzero element of `L` is nondegenerate because its
radical is a `G`-submodule of the simple module `V`.  The Kneser bound on spaces of nondegenerate
alternating forms (`nonsingular_subspace_card_sq_le`) then gives `|A|² ≤ |V|`. -/
theorem card_le_of_simple_invariant_alternating_span {p : ℕ} [Fact p.Prime] {G V A : Type*}
    [Group G] [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    [AddCommGroup A] [Module (ZMod p) A] [Finite A]
    (ρ : G →* V ≃ₗ[ZMod p] V) (β : V →ₗ[ZMod p] V →ₗ[ZMod p] A)
    (halt : ∀ v : V, β v v = 0)
    (hinv : ∀ (g : G) (v w : V), β (ρ g v) (ρ g w) = β v w)
    (hspan : Submodule.span (ZMod p) (Set.range (fun x : V × V => β x.1 x.2)) = ⊤)
    (hrad : ∀ v : V, (∀ w : V, β v w = 0) → v = 0)
    (hsimple : ∀ W : Submodule (ZMod p) V, (∀ (g : G) (v : V), v ∈ W → ρ g v ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    Nat.card A ^ 2 ≤ Nat.card V := by
  -- `hrad` is recorded but not needed: the nondegeneracy of the elements of `L` below follows
  -- from the simplicity of `V` (the radical of a `G`-invariant form is a `G`-submodule).
  have _ : (0 : V) = 0 := hrad 0 (fun w => by simp)
  let k := ZMod p
  -- The dual of `β`: an `a^* ∈ A^*` yields the alternating form `(v,w) ↦ a^*(β v w)`.
  let ψ : (A →ₗ[k] k) →ₗ[k] (V →ₗ[k] V →ₗ[k] k) :=
    (LinearMap.lcomp k (V →ₗ[k] k) β).comp (LinearMap.llcomp k V A k)
  let L : Submodule k (V →ₗ[k] V →ₗ[k] k) := LinearMap.range ψ
  have hψ : ∀ (a : A →ₗ[k] k) (v w : V), ψ a v w = a (β v w) := by
    intro a v w; rfl
  -- Every element of `L` is alternating.
  have haltL : ∀ b ∈ L, ∀ v : V, b v v = 0 := by
    intro b hb v
    obtain ⟨a, rfl⟩ := hb
    rw [hψ, halt v, map_zero]
  -- Every nonzero element of `L` is nondegenerate, because its radical is a `G`-submodule of the
  -- simple module `V`.
  have hndL : ∀ b ∈ L, b ≠ 0 → ∀ v : V, (∀ w : V, b v w = 0) → v = 0 := by
    intro b hb hb0 v hv
    obtain ⟨a, rfl⟩ := hb
    have hinvW : ∀ (g : G) (u : V), u ∈ LinearMap.ker (ψ a) → ρ g u ∈ LinearMap.ker (ψ a) := by
      intro g u hu
      rw [LinearMap.mem_ker] at hu ⊢
      ext w
      have h2 : β (ρ g u) w = β u (ρ g⁻¹ w) := by
        have h := hinv g u (ρ g⁻¹ w)
        have hw : ρ g (ρ g⁻¹ w) = w := by
          rw [map_inv]
          exact LinearEquiv.apply_symm_apply (ρ g) w
        rwa [hw] at h
      rw [hψ, h2, ← hψ, hu]
      rfl
    rcases hsimple (LinearMap.ker (ψ a)) hinvW with hbot | htop
    · have hv' : v ∈ LinearMap.ker (ψ a) := by
        rw [LinearMap.mem_ker]
        ext w
        exact hv w
      rw [hbot] at hv'
      simpa using hv'
    · exfalso
      apply hb0
      have ha0 : a = 0 := by
        have hle : Submodule.span k (Set.range (fun x : V × V => β x.1 x.2)) ≤
            LinearMap.ker a := by
          rw [Submodule.span_le]
          rintro y ⟨⟨v,w⟩, rfl⟩
          show a (β v w) = 0
          have hv : v ∈ LinearMap.ker (ψ a) := by rw [htop]; trivial
          rw [LinearMap.mem_ker] at hv
          have hw := congrArg (fun f : V →ₗ[k] k => f w) hv
          rwa [hψ] at hw
        rw [hspan] at hle
        exact LinearMap.ker_eq_top.mp (eq_top_iff.mpr hle)
      rw [ha0]; rfl
  -- `ψ` is injective: an `a^*` vanishing on all `β v w` vanishes on the spanning set.
  have hinj : Function.Injective ψ := by
    intro a1 a2 h
    have ha0 : a1 - a2 = 0 := by
      have hle : Submodule.span k (Set.range (fun x : V × V => β x.1 x.2)) ≤
          LinearMap.ker (a1 - a2) := by
        rw [Submodule.span_le]
        rintro y ⟨⟨v,w⟩, rfl⟩
        show (a1 - a2) (β v w) = 0
        rw [LinearMap.sub_apply, sub_eq_zero]
        have key : (ψ a1 v) w = (ψ a2 v) w := congrArg (fun f => (f v) w) h
        rwa [hψ, hψ] at key
      rw [hspan] at hle
      exact LinearMap.ker_eq_top.mp (eq_top_iff.mpr hle)
    exact sub_eq_zero.mp ha0
  -- `|L| = |A^*| = |A|`.
  have hcardL : Nat.card L = Nat.card (A →ₗ[k] k) := by
    have e : (A →ₗ[k] k) ≃ₗ[k] L := LinearEquiv.ofInjective ψ hinj
    exact (Nat.card_congr e.toEquiv).symm
  have hcardA : Nat.card (A →ₗ[k] k) = Nat.card A := by
    have h1 : Nat.card (A →ₗ[k] k)
        = (Nat.card k) ^ Module.finrank k (A →ₗ[k] k) := Module.natCard_eq_pow_finrank
    have h2 : Nat.card A = (Nat.card k) ^ Module.finrank k A := Module.natCard_eq_pow_finrank
    rw [h1, h2, Subspace.dual_finrank_eq]
  -- Kneser's bound for the space `L` of nondegenerate alternating forms.
  have hbound := nonsingular_subspace_card_sq_le L haltL hndL
  rw [hcardL, hcardA] at hbound
  exact hbound

end Commons.LinearAlgebra.Alternating