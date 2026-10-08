import Mathlib
import Submission.Work.Higman.Q3.finrank_dvd_of_irreducible_pow_sub_one
import Submission.Work.Higman.Q3.pow_sub_one_dvd_pow_sub_one_iff
import Submission.Work.Higman.Q3.orderOf_dvd_ncard_of_semiregular

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Higman.H8

/-- The order of an irreducible linear automorphism `ξ` of a finite `𝔽₂`-vector space `V` divides
`|V| - 1`.  Indeed `⟨ξ⟩` acts freely on the non-zero vectors: if `ξ ^ k` fixes some `v ≠ 0` then
the fixed space `{w | ξ ^ k w = w}` is a non-zero `ξ`-invariant subspace, hence all of `V`, so
`ξ ^ k = 1`.  All orbits of `⟨ξ⟩` on `V ∖ {0}` therefore have size `orderOf ξ`. -/
theorem orderOf_dvd_natCard_sub_one_of_irreducible {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] [Nontrivial V] (ξ : V ≃ₗ[ZMod 2] V)
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ v ∈ U, ξ v ∈ U) → U = ⊥ ∨ U = ⊤) :
    orderOf ξ ∣ Nat.card V - 1 := by
  classical
  set σ : Equiv.Perm V := MulAction.toPerm ξ with hσ
  have hσpow : ∀ k : ℕ, (σ ^ k : Equiv.Perm V) = MulAction.toPerm (ξ ^ k) := by
    intro k
    rw [hσ, ← MulAction.toPermHom_apply, ← map_pow, MulAction.toPermHom_apply]
  have hσapply : ∀ (k : ℕ) (v : V), (σ ^ k) v = (ξ ^ k) v := by
    intro k v
    rw [hσpow k]
    rfl
  -- The non-zero vectors are permuted by `σ`.
  have hS : ∀ x ∈ ({v : V | v ≠ 0} : Set V), σ x ∈ ({v : V | v ≠ 0} : Set V) := by
    intro x hx
    have hxe : σ x = ξ x := by rw [hσ]; rfl
    rw [hxe]
    intro h
    exact hx (ξ.injective (by rw [h, map_zero]))
  -- The action is free.
  have hfree : ∀ k : ℕ, ∀ x ∈ ({v : V | v ≠ 0} : Set V), (σ ^ k) x = x → σ ^ k = 1 := by
    intro k x hx hfix
    have hfix' : (ξ ^ k) x = x := by rw [← hσapply k x]; exact hfix
    have hcomm : ∀ v : V, (ξ ^ k) (ξ v) = ξ ((ξ ^ k) v) := by
      intro v
      calc (ξ ^ k) (ξ v) = ((ξ ^ k) * ξ) v := (LinearEquiv.mul_apply _ _ _).symm
        _ = (ξ * (ξ ^ k)) v := by rw [((Commute.refl ξ).pow_left k).eq]
        _ = ξ ((ξ ^ k) v) := LinearEquiv.mul_apply _ _ _
    -- The fixed points of `ξ ^ k` form a `ξ`-invariant subspace.
    set U : Submodule (ZMod 2) V :=
      { carrier := {v : V | (ξ ^ k) v = v}
        zero_mem' := by show (ξ ^ k) 0 = 0; exact map_zero _
        add_mem' := by
          intro a b ha hb
          show (ξ ^ k) (a + b) = a + b
          rw [map_add, ha, hb]
        smul_mem' := by
          intro c a ha
          show (ξ ^ k) (c • a) = c • a
          rw [map_smul, ha] } with hU
    have hxU : x ∈ U := by rw [hU]; exact hfix'
    have hinv : ∀ v ∈ U, ξ v ∈ U := by
      intro v hv
      rw [hU] at hv ⊢
      show (ξ ^ k) (ξ v) = ξ v
      rw [hcomm v, hv]
    rcases hirr U hinv with h | h
    · rw [h, Submodule.mem_bot] at hxU
      exact absurd hxU hx
    · have hξk : ξ ^ k = 1 := by
        ext v
        have hv : v ∈ U := by rw [h]; exact Submodule.mem_top
        rw [hU] at hv
        simpa using hv
      have hσk : σ ^ k = 1 := by
        ext v
        rw [hσapply k v, hξk]
        simp
      exact hσk
  have hdvd := Work.Higman.Q3.orderOf_dvd_ncard_of_semiregular σ
    ({v : V | v ≠ 0} : Set V) hS hfree
  have horder : orderOf σ = orderOf ξ := by
    rw [hσ]
    exact orderOf_injective (MulAction.toPermHom (V ≃ₗ[ZMod 2] V) V)
      MulAction.toPerm_injective ξ
  rw [horder] at hdvd
  have hSncard : ({v : V | v ≠ 0} : Set V).ncard = Nat.card V - 1 := by
    have hcompl : ({v : V | v ≠ 0} : Set V)ᶜ = {0} := by
      ext x; simp
    have h := Set.ncard_add_ncard_compl ({v : V | v ≠ 0} : Set V)
    rw [hcompl, Set.ncard_singleton] at h
    omega
  rwa [hSncard] at hdvd

/-- **Higman's Lemma 8 core count.**  A finite non-trivial `𝔽₂`-vector space carrying an
irreducible linear automorphism `ξ` of order `2 ^ n - 1` has cardinality `2 ^ n`.

Write `d = finrank 𝔽₂ V`; then `|V| = 2 ^ d`.  Since `⟨ξ⟩` acts freely on `V ∖ {0}`, whose
cardinality is `2 ^ d - 1`, we get `2 ^ n - 1 ∣ 2 ^ d - 1`, hence `n ∣ d`.  Conversely `V` is a
simple `𝔽₂[ξ]`-module, so the minimal polynomial `μ` of `ξ` is irreducible of degree `d`
and divides `X ^ (2 ^ n - 1) - 1`; every irreducible factor of `X ^ (2 ^ n - 1) - 1` over `𝔽₂`
has degree dividing `n`, so `d ∣ n`.  Hence `d = n`. -/
theorem card_pow_of_irreducible {n : ℕ} (hn : 1 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] [Nontrivial V]
    (ξ : V ≃ₗ[ZMod 2] V) (hξ : orderOf ξ = 2 ^ n - 1)
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ v ∈ U, ξ v ∈ U) → U = ⊥ ∨ U = ⊤) :
    Nat.card V = 2 ^ n := by
  have hξpow : ξ ^ (2 ^ n - 1) = 1 := by rw [← hξ]; exact pow_orderOf_eq_one ξ
  -- `finrank 𝔽₂ V ∣ n`
  have hdvdn : Module.finrank (ZMod 2) V ∣ n :=
    Work.Higman.Q3.finrank_dvd_of_irreducible_pow_sub_one ξ hn hξpow hirr
  -- `n ∣ finrank 𝔽₂ V`
  have hcardV : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]
  have hNsub : orderOf ξ ∣ Nat.card V - 1 :=
    orderOf_dvd_natCard_sub_one_of_irreducible ξ hirr
  have hdiv : 2 ^ n - 1 ∣ 2 ^ Module.finrank (ZMod 2) V - 1 := by
    rw [← hξ, ← hcardV]
    exact hNsub
  have hndvd : n ∣ Module.finrank (ZMod 2) V :=
    (Work.Higman.Q3.pow_sub_one_dvd_pow_sub_one_iff (x := 2) (m := n)
      (k := Module.finrank (ZMod 2) V) (by norm_num) (by omega)).mp hdiv
  have hdn : Module.finrank (ZMod 2) V = n := Nat.dvd_antisymm hdvdn hndvd
  rw [hcardV, hdn]

end Work.Higman.H8
