import Mathlib
import Submission.Work.Higman.Q3.irreducible_minpoly_of_irreducible

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

namespace Work.Higman.RedAux

open Polynomial

/-- A finite abelian group of order `2 ^ n` (`n ≥ 1`) carrying an automorphism whose only
invariant subgroups are `⊥` and `⊤` is elementary abelian. -/
theorem xi_elementary_abelian {n : ℕ} (hn : 1 ≤ n) {V : Type} [AddCommGroup V] [Finite V]
    (hcardV : Nat.card V = 2 ^ n) (ξ : V ≃+ V)
    (hirr : ∀ W : AddSubgroup V, (∀ v ∈ W, ξ v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∀ v : V, v + v = 0 := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Nontrivial V := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hcardV]
    exact Nat.one_lt_pow (by omega : n ≠ 0) (by norm_num)
  obtain ⟨v0, hv0⟩ := exists_ne (0 : V)
  let δ : V →+ V :=
    { toFun := fun v => v + v
      map_zero' := by simp
      map_add' := fun a b => by abel }
  have hδapply : ∀ v : V, δ v = v + v := fun v => rfl
  have hδinv : ∀ v ∈ δ.range, ξ v ∈ δ.range := by
    intro v hv
    rw [AddMonoidHom.mem_range] at hv ⊢
    obtain ⟨w, rfl⟩ := hv
    refine ⟨ξ w, ?_⟩
    rw [hδapply, hδapply, map_add]
  have hne_top : δ.range ≠ ⊤ := by
    intro htop
    have hsurj : Function.Surjective δ := fun y => by
      have hy : y ∈ δ.range := by rw [htop]; trivial
      rwa [AddMonoidHom.mem_range] at hy
    have key : ∀ k : ℕ, ∀ v : V, ∃ w : V, (2 ^ k) • w = v := by
      intro k
      induction k with
      | zero => intro v; exact ⟨v, by simp⟩
      | succ k ih =>
        intro v
        obtain ⟨w, hw⟩ := hsurj v
        have hw' : w + w = v := by rw [← hδapply w]; exact hw
        obtain ⟨u, hu⟩ := ih w
        refine ⟨u, ?_⟩
        have hp2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
        rw [hp2, add_nsmul, hu]
        exact hw'
    obtain ⟨w, hw⟩ := key n v0
    have hz : (2 ^ n) • w = 0 := by
      rw [← hcardV]
      exact card_nsmul_eq_zero'
    rw [hz] at hw
    exact hv0 hw.symm
  intro v
  rcases hirr δ.range hδinv with h | h
  · have hv'' : δ v ∈ δ.range := AddMonoidHom.mem_range.mpr ⟨v, rfl⟩
    rw [h, AddSubgroup.mem_bot, hδapply] at hv''
    exact hv''
  · exact absurd h hne_top

/-- The `𝔽₂[ξ]`-module structure of an irreducible automorphism of a finite elementary abelian
`2`-group of order `2 ^ n`: `V` is a copy of the field `GF(2^n)` on which `ξ` acts as
multiplication by a non-zero scalar. -/
theorem xi_module_scalar {n : ℕ} (hn : 1 ≤ n) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (hcardV : Nat.card V = 2 ^ n)
    (ξ : V ≃ₗ[ZMod 2] V)
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ v ∈ W, ξ v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ (σ : GaloisField 2 n) (e : V ≃+ GaloisField 2 n),
      σ ≠ 0 ∧ ∀ v : V, e (ξ v) = σ * e v := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Nontrivial V := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hcardV]
    exact Nat.one_lt_pow (by omega : n ≠ 0) (by norm_num)
  let φ : V →ₗ[ZMod 2] V := (ξ : V →ₗ[ZMod 2] V)
  have hφirr : Irreducible (minpoly (ZMod 2) φ) :=
    Work.Higman.Q3.irreducible_minpoly_of_irreducible φ (fun U hU => hirr U hU)
  have hRfield : IsField (AdjoinRoot (minpoly (ZMod 2) φ)) :=
    AdjoinRoot.isField_iff_irreducible.mpr hφirr
  have hker : ∀ a ∈ Ideal.span {minpoly (ZMod 2) φ}, (Polynomial.aeval φ) a = 0 := by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, minpoly.aeval (ZMod 2) φ, zero_mul]
  let ρ : AdjoinRoot (minpoly (ZMod 2) φ) →+* Module.End (ZMod 2) V :=
    Ideal.Quotient.lift (Ideal.span {minpoly (ZMod 2) φ}) (Polynomial.aeval φ).toRingHom hker
  have hρroot : ρ (AdjoinRoot.root (minpoly (ZMod 2) φ)) = φ := by
    show Ideal.Quotient.lift (Ideal.span {minpoly (ZMod 2) φ}) (Polynomial.aeval φ).toRingHom hker
      (Ideal.Quotient.mk (Ideal.span {minpoly (ZMod 2) φ}) Polynomial.X) = φ
    rw [Ideal.Quotient.lift_mk]
    exact Polynomial.aeval_X φ
  obtain ⟨v0, hv0⟩ := exists_ne (0 : V)
  let Ψ : AdjoinRoot (minpoly (ZMod 2) φ) →+ V :=
    { toFun := fun r => ρ r v0
      map_zero' := by simp
      map_add' := fun r s => by rw [map_add]; rfl }
  have hΨmul : ∀ r s : AdjoinRoot (minpoly (ZMod 2) φ), Ψ (r * s) = ρ r (Ψ s) := by
    intro r s
    show ρ (r * s) v0 = ρ r (ρ s v0)
    rw [map_mul, Module.End.mul_apply]
  have hΨone : Ψ 1 = v0 := by
    show ρ 1 v0 = v0
    rw [map_one, Module.End.one_eq_id, LinearMap.id_apply]
  have hΨα : ∀ r : AdjoinRoot (minpoly (ZMod 2) φ),
      Ψ (AdjoinRoot.root (minpoly (ZMod 2) φ) * r) = ξ (Ψ r) := by
    intro r
    rw [hΨmul (AdjoinRoot.root (minpoly (ZMod 2) φ)) r]
    show ρ (AdjoinRoot.root (minpoly (ZMod 2) φ)) (ρ r v0) = ξ (ρ r v0)
    rw [hρroot]
    rfl
  have hrange : ∀ w ∈ Ψ.range, ξ w ∈ Ψ.range := by
    intro w hw
    rw [AddMonoidHom.mem_range] at hw ⊢
    obtain ⟨r, rfl⟩ := hw
    exact ⟨AdjoinRoot.root (minpoly (ZMod 2) φ) * r, hΨα r⟩
  have htop : Ψ.range = ⊤ := by
    have hinv : ∀ v ∈ AddSubgroup.toZModSubmodule 2 Ψ.range,
        ξ v ∈ AddSubgroup.toZModSubmodule 2 Ψ.range :=
      fun v hv => hrange v (by simpa using hv)
    rcases hirr (AddSubgroup.toZModSubmodule 2 Ψ.range) hinv with h | h
    · exfalso
      have hv0mem : v0 ∈ AddSubgroup.toZModSubmodule 2 Ψ.range := by
        rw [AddSubgroup.mem_toZModSubmodule]
        exact AddMonoidHom.mem_range.mpr ⟨1, hΨone⟩
      rw [h, Submodule.mem_bot] at hv0mem
      exact hv0 hv0mem
    · have := congrArg Submodule.toAddSubgroup h
      simpa using this
  have hsurj : Function.Surjective Ψ := by
    intro v
    have : v ∈ Ψ.range := by rw [htop]; trivial
    rwa [AddMonoidHom.mem_range] at this
  have hinj : Function.Injective Ψ := by
    intro r s hrs
    by_contra hne
    have hsub : r - s ≠ 0 := sub_ne_zero.mpr hne
    have h0 : Ψ (r - s) = 0 := by rw [map_sub, hrs, sub_self]
    obtain ⟨b, hb⟩ := hRfield.mul_inv_cancel hsub
    have hb' : b * (r - s) = 1 := by rw [hRfield.mul_comm, hb]
    have h1 : Ψ 1 = 0 := by
      have h2 : Ψ (b * (r - s)) = 0 := by
        rw [hΨmul b (r - s), h0, map_zero]
      rwa [hb'] at h2
    rw [hΨone] at h1
    exact hv0 h1
  let Ψe : AdjoinRoot (minpoly (ZMod 2) φ) ≃+ V := AddEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  have hcardR : Nat.card (AdjoinRoot (minpoly (ZMod 2) φ)) = 2 ^ n := by
    rw [Nat.card_congr Ψe.toEquiv, hcardV]
  let χ : AdjoinRoot (minpoly (ZMod 2) φ) ≃ₐ[ZMod 2] GaloisField 2 n :=
    @GaloisField.algEquivGaloisField 2 ⟨Nat.prime_two⟩ n (AdjoinRoot (minpoly (ZMod 2) φ))
      hRfield.toField inferInstance hcardR
  have hαne : AdjoinRoot.root (minpoly (ZMod 2) φ) ≠ 0 := by
    intro h0
    have hφzero : (ξ : V →ₗ[ZMod 2] V) = 0 := by
      rw [show (ξ : V →ₗ[ZMod 2] V) = φ from rfl, ← hρroot, h0, map_zero]
    have hξ0 : ξ v0 = 0 := by
      have : (ξ : V →ₗ[ZMod 2] V) v0 = 0 := by rw [hφzero, LinearMap.zero_apply]
      simpa using this
    exact hv0 (ξ.injective (by rw [hξ0, map_zero]))
  refine ⟨χ (AdjoinRoot.root (minpoly (ZMod 2) φ)), Ψe.symm.trans (χ.toLinearEquiv).toAddEquiv,
    ?_, ?_⟩
  · intro h
    exact hαne (χ.injective (by rw [h, map_zero]))
  · intro v
    have hsymm : Ψe.symm (ξ v) = AdjoinRoot.root (minpoly (ZMod 2) φ) * Ψe.symm v := by
      apply Ψe.injective
      rw [Ψe.apply_symm_apply]
      show ξ v = Ψ (AdjoinRoot.root (minpoly (ZMod 2) φ) * Ψe.symm v)
      rw [hΨα (Ψe.symm v)]
      rw [show Ψ (Ψe.symm v) = v from Ψe.apply_symm_apply v]
    show χ (Ψe.symm (ξ v)) = χ (AdjoinRoot.root (minpoly (ZMod 2) φ)) * χ (Ψe.symm v)
    rw [hsymm, map_mul]

theorem xi_irreducible_module_scalar {F : Type} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card F = 2 ^ n)
    {V : Type} [AddCommGroup V] [Finite V] (hcardV : Nat.card V = 2 ^ n)
    (ξ : V ≃+ V)
    (hirr : ∀ W : AddSubgroup V, (∀ v ∈ W, ξ v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ (σ : F) (e : V ≃+ F), σ ≠ 0 ∧ ∀ v : V, e (ξ v) = σ * e v := by
  classical
  have h2 : ∀ v : V, v + v = 0 := xi_elementary_abelian hn hcardV ξ hirr
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun x => by rw [two_nsmul]; exact h2 x)
  let ξl : V →ₗ[ZMod 2] V := ξ.toAddMonoidHom.toZModLinearMap 2
  have ξl_apply : ∀ x : V, ξl x = ξ x := fun x => rfl
  have ξbij : Function.Bijective ξl := by
    constructor
    · intro a b h
      rw [ξl_apply a, ξl_apply b] at h
      exact ξ.injective h
    · intro b
      obtain ⟨a, ha⟩ := ξ.surjective b
      exact ⟨a, by rw [ξl_apply]; exact ha⟩
  let ξlin : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective ξl ξbij
  have ξlin_apply : ∀ x : V, ξlin x = ξ x := fun x => ξl_apply x
  have hirr' : ∀ W : Submodule (ZMod 2) V, (∀ v ∈ W, ξlin v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hinv : ∀ v ∈ W.toAddSubgroup, ξ v ∈ W.toAddSubgroup := by
      intro v hv
      have hv' : v ∈ W := by simpa using hv
      have h1 : ξlin v ∈ W := hW v hv'
      rw [ξlin_apply] at h1
      simpa using h1
    rcases hirr W.toAddSubgroup hinv with h | h
    · left
      have := congrArg (AddSubgroup.toZModSubmodule 2) h
      simpa using this
    · right
      have := congrArg (AddSubgroup.toZModSubmodule 2) h
      simpa using this
  obtain ⟨σ₀, e₀, hσ₀, he₀⟩ := xi_module_scalar hn hcardV ξlin hirr'
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hGFcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hFcard : Nat.card F = 2 ^ n := by rw [← Fintype.card_eq_nat_card, hcard]
  let χF : GaloisField 2 n ≃+* F :=
    FiniteField.ringEquivOfCardEq (by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hGFcard, hFcard])
  refine ⟨χF σ₀, e₀.trans χF.toAddEquiv, ?_, ?_⟩
  · intro h
    exact hσ₀ (χF.injective (by rw [h, map_zero]))
  · intro v
    rw [← ξlin_apply v]
    show χF (e₀ (ξlin v)) = χF σ₀ * χF (e₀ v)
    rw [he₀ v, map_mul]

end Work.Higman.RedAux
