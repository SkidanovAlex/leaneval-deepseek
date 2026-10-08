import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.BrauerSuzuki.Dade

/-- `mk' N x = 1 ↔ x ∈ N` in terms of the coercion. -/
private lemma mk'_eq_one_iff {G : Type*} [Group G] {N : Subgroup G} [N.Normal] (x : G) :
    QuotientGroup.mk' N x = 1 ↔ x ∈ N := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

/-!
# The projection `H → H/K ≅ S` for a semidirect decomposition

If `S K H ≤ G` with `K ⊴ H`, `S ≤ H`, `K ⊓ S = ⊥` and `K ⊔ S = H`, then `H` is the semidirect
product `K ⋊ S`: the composite `S → H → H/K` is a bijection, and composing its inverse with
the quotient map `H → H/K` gives a surjective homomorphism `φ : ↥H →* ↥S` with kernel `K`
which is the identity on `S`.  This is the map `φ` of Dade's Lemmas 6.9–6.10.
-/
theorem complement_hom {G : Type*} [Group G] (S K H : Subgroup G) (hKH : K ≤ H)
    (hSH : S ≤ H) (hdisj : K ⊓ S = ⊥) (hsup : K ⊔ S = H)
    (hKn : ∀ k ∈ K, ∀ h ∈ H, h * k * h⁻¹ ∈ K) :
    ∃ φ : ↥H →* ↥S,
      (∀ s : ↥S, φ ⟨(s : G), hSH s.2⟩ = s) ∧
      (∀ h : ↥H, φ h = 1 ↔ ((h : G) ∈ K)) ∧
      Function.Surjective φ ∧
      (∀ h : ↥H, ∃ k ∈ K, (h : G) = ((φ h : ↥S) : G) * k) := by
  have hHK : H ≤ Subgroup.normalizer K := fun h hh =>
    Subgroup.mem_normalizer_iff.mpr fun k => ⟨fun hk => hKn k hk h hh,
      fun hkh => by
        have hk' : h⁻¹ * (h * k * h⁻¹) * (h⁻¹)⁻¹ ∈ K := hKn _ hkh _ (H.inv_mem hh)
        rwa [show h⁻¹ * (h * k * h⁻¹) * (h⁻¹)⁻¹ = k from by group] at hk'⟩
  haveI hN : (K.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHK
  let N : Subgroup ↥H := K.subgroupOf H
  have hNmem : ∀ x : ↥H, x ∈ N ↔ (x : G) ∈ K := fun x => Subgroup.mem_subgroupOf
  have hSK : S ≤ Subgroup.normalizer K := fun x hx => hHK (hSH hx)
  let ψ : ↥S →* ↥H ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hSH)
  have hψ_inj : Function.Injective ψ := by
    intro s1 s2 h
    have h1 : Subgroup.inclusion hSH (s1 * s2⁻¹) ∈ N := by
      have h2 : ψ (s1 * s2⁻¹) = 1 := by
        rw [map_mul, map_inv, h, mul_inv_cancel]
      exact (mk'_eq_one_iff (Subgroup.inclusion hSH (s1 * s2⁻¹))).mp h2
    have h1' : ((s1 * s2⁻¹ : ↥S) : G) ∈ K := by
      have h1'' : ((Subgroup.inclusion hSH (s1 * s2⁻¹) : ↥H) : G) ∈ K := (hNmem _).mp h1
      simpa using h1''
    have h3 : ((s1 * s2⁻¹ : ↥S) : G) ∈ (K ⊓ S : Subgroup G) :=
      ⟨h1', (s1 * s2⁻¹).2⟩
    rw [hdisj] at h3
    have h5 : ((s1 * s2⁻¹ : ↥S) : G) = 1 := by simpa using h3
    exact mul_inv_eq_one.mp (Subtype.ext h5)
  have hψ_surj : Function.Surjective ψ := by
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hh : (h : G) ∈ (K ⊔ S : Subgroup G) := by rw [hsup]; exact h.2
    have hh' : (h : G) ∈ ((K ⊔ S : Subgroup G) : Set G) := hh
    rw [sup_comm, Subgroup.coe_mul_of_left_le_normalizer_right S K hSK] at hh'
    obtain ⟨s, hs, k, hk, hsk⟩ := Set.mem_mul.mp hh'
    refine ⟨⟨s, hs⟩, ?_⟩
    have heq : h = (⟨s, hSH hs⟩ : ↥H) * ⟨k, hKH hk⟩ := by
      ext
      exact hsk.symm
    have hk1 : QuotientGroup.mk' N (⟨k, hKH hk⟩ : ↥H) = 1 := by
      rw [mk'_eq_one_iff]
      exact (hNmem _).mpr hk
    change QuotientGroup.mk' N ⟨s, hSH hs⟩ = QuotientGroup.mk' N h
    rw [heq, map_mul, hk1, mul_one]
  let e : ↥S ≃* ↥H ⧸ N := MulEquiv.ofBijective ψ ⟨hψ_inj, hψ_surj⟩
  set φ : ↥H →* ↥S := e.symm.toMonoidHom.comp (QuotientGroup.mk' N) with hφ
  have hφ_app : ∀ h : ↥H, φ h = e.symm (QuotientGroup.mk' N h) := fun h => rfl
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [hφ_app]
    show e.symm (QuotientGroup.mk' N (Subgroup.inclusion hSH s)) = s
    have h : QuotientGroup.mk' N (Subgroup.inclusion hSH s) = e s := rfl
    rw [h, e.symm_apply_apply]
  · intro h
    rw [hφ_app]
    show e.symm (QuotientGroup.mk' N h) = 1 ↔ (h : G) ∈ K
    constructor
    · intro hh
      have h1 : QuotientGroup.mk' N h = 1 := by
        have := congrArg e hh
        simpa using this
      exact (hNmem h).mp ((mk'_eq_one_iff h).mp h1)
    · intro hh
      have h1 : QuotientGroup.mk' N h = 1 := (mk'_eq_one_iff h).mpr ((hNmem h).mpr hh)
      rw [h1, map_one]
  · intro s
    refine ⟨(⟨(s : G), hSH s.2⟩ : ↥H), ?_⟩
    have hwit : (⟨(s : G), hSH s.2⟩ : ↥H) = Subgroup.inclusion hSH s := rfl
    rw [hφ_app, hwit]
    show e.symm (QuotientGroup.mk' N (Subgroup.inclusion hSH s)) = s
    have h : QuotientGroup.mk' N (Subgroup.inclusion hSH s) = e s := rfl
    rw [h, e.symm_apply_apply]
  · intro h
    -- `(φ h)⁻¹ * h ∈ K`
    have hkey : ((φ h : ↥S) : G)⁻¹ * (h : G) ∈ K := by
      have h1 : QuotientGroup.mk' N h = QuotientGroup.mk' N (Subgroup.inclusion hSH (φ h)) := by
        rw [hφ_app]
        exact (e.apply_symm_apply (QuotientGroup.mk' N h)).symm
      have h2 : QuotientGroup.mk' N (Subgroup.inclusion hSH (φ h)⁻¹ * h) = 1 := by
        rw [map_mul, map_inv, h1]
        exact inv_mul_cancel (QuotientGroup.mk' N (Subgroup.inclusion hSH (φ h)))
      have h3 : Subgroup.inclusion hSH (φ h)⁻¹ * h ∈ N := (mk'_eq_one_iff _).mp h2
      have h3' : ((Subgroup.inclusion hSH (φ h)⁻¹ * h : ↥H) : G) ∈ K := (hNmem _).mp h3
      simpa using h3'
    exact ⟨_, hkey, by group⟩

end Work.BrauerSuzuki.Dade
