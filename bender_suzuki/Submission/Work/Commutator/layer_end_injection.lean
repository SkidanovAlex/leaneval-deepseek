import Mathlib
import Submission.Work.Higman.H8.layer_of_end_injection
import Submission.Work.Higman.H8.frob_irred_le_Mk
import Submission.Work.Higman.H8.frob_submodule_bijective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Commutator

open Work.Higman.H8.FSB

/-- Strengthening of `Work.Higman.H8.layer_of_end_injection`: the Frobenius component is
*explicit*, i.e. `Ψ v` is the map `x ↦ φ v * x ^ (2 ^ k)`. -/
theorem layer_end_injection {n : ℕ} (hn : 2 ≤ n)
    (ν : (GaloisField 2 n)ˣ) (hν : orderOf ν = 2 ^ n - 1)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hVcard : Nat.card V = 2 ^ n)
    (ξV : V ≃ₗ[ZMod 2] V)
    (hsimple : ∀ W : Submodule (ZMod 2) V, (∀ v ∈ W, ξV v ∈ W) → W = ⊥ ∨ W = ⊤)
    (Ψ : V →ₗ[ZMod 2] (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n))
    (hΨinj : Function.Injective Ψ)
    (hΨeq : ∀ v, Ψ (ξV v) = Work.Higman.H8.FSB.singAct ν (Ψ v)) :
    ∃ k : ℕ, k < n ∧ ∃ φ : V →ₗ[ZMod 2] GaloisField 2 n,
      (∀ v x, Ψ v x = φ v * x ^ (2 ^ k)) ∧
      (∀ v, φ v = 0 ↔ v = 0) ∧
      (∀ v, φ (ξV v) = Work.Higman.H8.lam ν k * φ v) ∧
      Function.Surjective φ := by
  classical
  have hn0 : n ≠ 0 := by omega
  -- The image of `Ψ` is a submodule of `End_{𝔽₂}(GF(2^n))`.
  let T : Submodule (ZMod 2) (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n) := LinearMap.range Ψ
  have hTmem : ∀ v : V, Ψ v ∈ T := fun v => LinearMap.mem_range.mpr ⟨v, rfl⟩
  have hTξ : ∀ f ∈ T, singAct ν f ∈ T := by
    intro f hf
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hf
    exact LinearMap.mem_range.mpr ⟨ξV v, hΨeq v⟩
  -- `T` is irreducible under `singAct ν`, transported from the irreducibility of `V`.
  have hirr : ∀ T' : Submodule (ZMod 2) (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n),
      (∀ f ∈ T', singAct ν f ∈ T') → T' ≤ T → T' = ⊥ ∨ T' = T := by
    intro T' hT'ξ hT'le
    let W : Submodule (ZMod 2) V := T'.comap Ψ
    have hWξ : ∀ v ∈ W, ξV v ∈ W := by
      intro v hv
      rw [Submodule.mem_comap] at hv ⊢
      rw [hΨeq v]
      exact hT'ξ (Ψ v) hv
    rcases hsimple W hWξ with hW | hW
    · left
      rw [Submodule.eq_bot_iff]
      intro f hf
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp (hT'le hf)
      have hv : v ∈ W := by
        rw [Submodule.mem_comap]
        exact hf
      rw [hW, Submodule.mem_bot] at hv
      rw [hv, map_zero]
    · right
      refine le_antisymm hT'le ?_
      intro f hf
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hf
      have hv : v ∈ W := by rw [hW]; exact Submodule.mem_top
      rw [Submodule.mem_comap] at hv
      exact hv
  obtain ⟨k, hkn, hTMk⟩ :=
    Work.Higman.H8.frob_irred_submodule_le_Mk hn ν hν T hTξ hirr
  -- Read off the Frobenius coefficient `φ v` from `Ψ v = c · x ^ (2^k)`.
  have hΨmem : ∀ v : V, Ψ v ∈ Mk k := fun v => hTMk (hTmem v)
  let l : GaloisField 2 n →ₗ[ZMod 2] Mk (n := n) k :=
    (frobCompLM (n := n) k).codRestrict (Mk k) (fun c => ⟨c, rfl⟩)
  have hlinj : Function.Injective l := by
    intro c c' h
    exact Work.Higman.H8.frobCompLM_injective n k (Subtype.ext_iff.mp h)
  have hlsurj : Function.Surjective l := by
    intro x
    obtain ⟨c, hc⟩ := mem_Mk.mp x.2
    exact ⟨c, Subtype.ext hc⟩
  let e : GaloisField 2 n ≃ₗ[ZMod 2] Mk (n := n) k :=
    LinearEquiv.ofBijective l ⟨hlinj, hlsurj⟩
  have he_apply : ∀ c : GaloisField 2 n,
      (e c : EndF n) = frobComp k c := fun c => rfl
  let cod : V →ₗ[ZMod 2] Mk (n := n) k := Ψ.codRestrict (Mk k) hΨmem
  have hcod_apply : ∀ v : V, (cod v : EndF n) = Ψ v := fun v => rfl
  let φ : V →ₗ[ZMod 2] GaloisField 2 n := e.symm.toLinearMap.comp cod
  have hφ_apply : ∀ v : V, φ v = e.symm (cod v) := fun v => rfl
  -- The explicit Frobenius form of `Ψ`.
  have hΨfrob : ∀ v : V, Ψ v = frobComp k (φ v) := by
    intro v
    have hcd : cod v = e (φ v) := by
      rw [hφ_apply v]; exact (e.apply_symm_apply (cod v)).symm
    have h3 := congrArg (fun x : Mk (n := n) k => (x : EndF n)) hcd
    rw [hcod_apply v, he_apply] at h3
    exact h3
  have hker : ∀ v : V, φ v = 0 ↔ v = 0 := by
    intro v
    constructor
    · intro hv
      have h1 : cod v = 0 := by
        have h2 : e.symm (cod v) = 0 := by rw [← hφ_apply v]; exact hv
        have h3 := congrArg e h2
        simpa using h3
      have h2 : Ψ v = 0 := by
        have h3 := congrArg (fun x : Mk (n := n) k => (x : EndF n)) h1
        rw [hcod_apply v] at h3
        simpa using h3
      exact hΨinj (by rw [h2, map_zero])
    · intro hv
      rw [hv]
      exact map_zero φ
  have heig : ∀ v : V, φ (ξV v) = Work.Higman.H8.lam ν k * φ v := by
    intro v
    have hcodξ : cod (ξV v) = e (Work.Higman.H8.lam ν k * φ v) := by
      apply Subtype.ext
      show Ψ (ξV v) = frobComp k (Work.Higman.H8.lam ν k * φ v)
      rw [hΨeq v, hΨfrob v, singAct_frobComp]
    calc φ (ξV v) = e.symm (cod (ξV v)) := hφ_apply (ξV v)
      _ = e.symm (e (Work.Higman.H8.lam ν k * φ v)) := by rw [hcodξ]
      _ = Work.Higman.H8.lam ν k * φ v := e.symm_apply_apply _
  refine ⟨k, hkn, φ, ?_, hker, heig, ?_⟩
  · intro v x
    rw [hΨfrob v, frobComp_apply]
  · have hφinj : Function.Injective φ := by
      intro a b hab
      have h0 : φ (a - b) = 0 := by rw [map_sub, hab, sub_self]
      have h1 : a - b = 0 := (hker (a - b)).mp h0
      exact sub_eq_zero.mp h1
    have hFintypeV : Fintype V := Fintype.ofFinite V
    have hcardV : Fintype.card V = Fintype.card (GaloisField 2 n) := by
      rw [← Nat.card_eq_fintype_card (α := V),
        ← Nat.card_eq_fintype_card (α := GaloisField 2 n), hVcard,
        Work.Higman.H8.card_galois hn0]
    exact hφinj.surjective_of_finite (Fintype.equivOfCardEq hcardV)

end Work.Commutator
