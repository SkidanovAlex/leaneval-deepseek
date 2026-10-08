import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.appI_kapp_ncard
import Submission.Work.NormalComplement.appI_phi_surjective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.NormalComplement

/-- If `t` is an involution normalising `X`, then every element `t⁻¹x⁻¹tx` (`x ∈ X`) is fixed
up to inversion by `t`: it lies in `Kset X t = J(X,t)`. -/
theorem kapp_subset_kset {G : Type*} [Group G] [Finite G] {t : G} (ht : orderOf t = 2)
    {X : Subgroup G} (htX : NormalizedBy t X) :
    Kapp t X ⊆ Kset X t := by
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h; simpa [pow_two] using h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rintro z ⟨x, hxX, rfl⟩
  have hmem : t * x⁻¹ * t⁻¹ ∈ X := htX x⁻¹ (X.inv_mem hxX)
  constructor
  · rw [hti]
    exact X.mul_mem (by simpa [hti] using hmem) hxX
  · rw [hti]
    calc t * (t * x⁻¹ * t * x) * t
        = (t * t) * (x⁻¹ * t * x * t) := by group
      _ = x⁻¹ * t * x * t := by rw [ht2, one_mul]
      _ = (t * x⁻¹ * t * x)⁻¹ := by
            simp only [mul_inv_rev, inv_inv, hti]
            group

/-- Uniqueness in App. I (1)(b): if `cᵢ ∈ C_X(t)` and `kᵢ ∈ Kset X t` with `c₁k₁ = c₂k₂`, then
`c₁ = c₂` and `k₁ = k₂` — provided `X` has odd order (so squaring is injective on `X`). -/
theorem phi_injective {G : Type*} [Group G] [Finite G] {t : G} (ht : orderOf t = 2)
    {X : Subgroup G} (hodd : Odd (Nat.card X)) :
    ∀ c₁ c₂ k₁ k₂ : G, c₁ ∈ Subgroup.centralizer ({t} : Set G) → c₁ ∈ X →
      k₁ ∈ Kset X t → c₂ ∈ Subgroup.centralizer ({t} : Set G) → c₂ ∈ X →
      k₂ ∈ Kset X t → c₁ * k₁ = c₂ * k₂ → c₁ = c₂ ∧ k₁ = k₂ := by
  have hsqinj : Function.Injective (fun x : X => x ^ 2) := by
    have hcop : (Nat.card X).Coprime 2 := Nat.coprime_two_right.mpr hodd
    exact (Nat.Coprime.pow_left_bijective (G := X) hcop).1
  intro c₁ c₂ k₁ k₂ hc₁ hc₁X hk₁ hc₂ hc₂X hk₂ heq
  have hkey : k₂ * k₁⁻¹ = c₂⁻¹ * c₁ := by
    have h1 : c₂⁻¹ * c₁ * k₁ = k₂ := by
      calc c₂⁻¹ * c₁ * k₁ = c₂⁻¹ * (c₁ * k₁) := by group
        _ = c₂⁻¹ * (c₂ * k₂) := by rw [heq]
        _ = k₂ := by group
    calc k₂ * k₁⁻¹ = (c₂⁻¹ * c₁ * k₁) * k₁⁻¹ := by rw [h1]
      _ = c₂⁻¹ * c₁ := by group
  have hmem : k₂ * k₁⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := by
    have h1 : c₂⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.centralizer _).inv_mem hc₂
    have h2 : c₂⁻¹ * c₁ ∈ Subgroup.centralizer ({t} : Set G) :=
      (Subgroup.centralizer _).mul_mem h1 hc₁
    simpa [← hkey] using h2
  have hcomm : t * (k₂ * k₁⁻¹) = (k₂ * k₁⁻¹) * t :=
    (Subgroup.mem_centralizer_iff.mp hmem) t (by simp)
  have htmem : t * (k₂ * k₁⁻¹) * t⁻¹ = k₂ * k₁⁻¹ := by
    rw [hcomm]; group
  have hcomp : t * (k₂ * k₁⁻¹) * t⁻¹ = k₂⁻¹ * k₁ := by
    have e1 : t * (k₂ * k₁⁻¹) * t⁻¹ = (t * k₂ * t⁻¹) * (t * k₁⁻¹ * t⁻¹) := by group
    have e2 : t * k₁⁻¹ * t⁻¹ = (t * k₁ * t⁻¹)⁻¹ := by group
    rw [e1, hk₂.2, e2, hk₁.2, inv_inv]
  have h4 : k₂ * k₁⁻¹ = k₂⁻¹ * k₁ := htmem.symm.trans hcomp
  have hsq : k₁ ^ 2 = k₂ ^ 2 := by
    have h5 : k₂ * k₂ * k₁⁻¹ = k₁ := by
      calc k₂ * k₂ * k₁⁻¹ = k₂ * (k₂ * k₁⁻¹) := by group
        _ = k₂ * (k₂⁻¹ * k₁) := by rw [h4]
        _ = k₁ := by group
    have h6 : k₂ * k₂ = k₁ * k₁ := by
      calc k₂ * k₂ = k₂ * k₂ * k₁⁻¹ * k₁ := by group
        _ = k₁ * k₁ := by rw [h5]
    calc k₁ ^ 2 = k₁ * k₁ := by rw [pow_two]
      _ = k₂ * k₂ := h6.symm
      _ = k₂ ^ 2 := by rw [pow_two]
  have hX : (⟨k₁, hk₁.1⟩ : X) ^ 2 = (⟨k₂, hk₂.1⟩ : X) ^ 2 := by
    apply Subtype.ext; simpa using hsq
  have hkeq : k₁ = k₂ := Subtype.ext_iff.mp (hsqinj hX)
  refine ⟨?_, hkeq⟩
  rw [hkeq] at heq
  exact mul_right_cancel heq

/-- The multiplication map `(C_X(t) ⊓ X) × Kset X t → X`, `(c,k) ↦ ck`, of App. I (1)(b). -/
noncomputable def phiFun {G : Type*} [Group G] (t : G) (X : Subgroup G) :
    (↥(Subgroup.centralizer ({t} : Set G) ⊓ X) × ↥(Kset X t)) → ↥X :=
  fun p => ⟨(p.1 : G) * (p.2 : G), X.mul_mem p.1.2.2 p.2.2.1⟩

theorem appI_one {G : Type*} [Group G] [Finite G] {d : ℕ} (hd : d.Prime) {t : G}
    (ht : orderOf t = d) {X : Subgroup G} (htX : Work.NormalComplement.NormalizedBy t X)
    (hdX : Nat.Coprime (Nat.card X) d) :
    (Work.NormalComplement.Kapp t X).ncard =
        ((Subgroup.centralizer ({t} : Set G) ⊓ X).subgroupOf X).index ∧
      (∀ h2 : d = 2, Work.NormalComplement.Kapp t X = Work.NormalComplement.Kset X t ∧
        ∀ z ∈ X, ∃! p : G × G, p.1 ∈ Subgroup.centralizer ({t} : Set G) ∧ p.1 ∈ X ∧
          p.2 ∈ Work.NormalComplement.Kapp t X ∧ p.1 * p.2 = z) := by
  refine ⟨appI_kapp_ncard t X, ?_⟩
  intro h2
  have ht2 : orderOf t = 2 := by rw [ht, h2]
  have hodd : Odd (Nat.card X) := by
    have hc : (Nat.card X).Coprime 2 := by rw [← h2]; exact hdX
    exact Nat.coprime_two_right.mp hc
  have hsub : Kapp t X ⊆ Kset X t := kapp_subset_kset ht2 htX
  have hinj : Function.Injective (phiFun t X) := by
    rintro ⟨c₁, k₁⟩ ⟨c₂, k₂⟩ heq
    have heq' : (c₁ : G) * (k₁ : G) = (c₂ : G) * (k₂ : G) := by
      simpa [phiFun] using congrArg (fun x : ↥X => (x : G)) heq
    obtain ⟨hc, hk⟩ :=
      phi_injective ht2 hodd c₁ c₂ k₁ k₂ c₁.2.1 c₁.2.2 k₁.2 c₂.2.1 c₂.2.2 k₂.2 heq'
    exact Prod.ext (Subtype.ext hc) (Subtype.ext hk)
  have hsurj : Function.Surjective (phiFun t X) := by
    rintro ⟨z, hzX⟩
    obtain ⟨c, hcC, hcX, k, hkKset, hck⟩ := appI_phi_surjective ht2 htX hodd z hzX
    exact ⟨(⟨c, ⟨hcC, hcX⟩⟩, ⟨k, hkKset⟩), Subtype.ext hck⟩
  have hKset : (Kset X t).ncard =
      ((Subgroup.centralizer ({t} : Set G) ⊓ X).subgroupOf X).index := by
    have hbij :
        Nat.card (↥(Subgroup.centralizer ({t} : Set G) ⊓ X) × ↥(Kset X t)) =
          Nat.card ↥X :=
      Nat.card_congr (Equiv.ofBijective (phiFun t X) ⟨hinj, hsurj⟩)
    rw [Nat.card_prod] at hbij
    have hcard_sub : Nat.card ↥((Subgroup.centralizer ({t} : Set G) ⊓ X).subgroupOf X) =
        Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have hright : Nat.card ↥X =
        Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X) *
          ((Subgroup.centralizer ({t} : Set G) ⊓ X).subgroupOf X).index := by
      have hci := Subgroup.card_mul_index
        ((Subgroup.centralizer ({t} : Set G) ⊓ X).subgroupOf X)
      rw [hcard_sub] at hci
      exact hci.symm
    rw [hright] at hbij
    have hpos : 0 < Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X) :=
      Nat.card_pos_iff.mpr ⟨⟨(1 : ↥(Subgroup.centralizer ({t} : Set G) ⊓ X))⟩, inferInstance⟩
    have hfin := Nat.mul_left_cancel hpos hbij
    simpa only [Nat.card_coe_set_eq] using hfin
  have hkappKset : Kapp t X = Kset X t := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_
    rw [hKset, appI_kapp_ncard t X]
  refine ⟨hkappKset, ?_⟩
  intro z hzX
  obtain ⟨c, hcC, hcX, k, hkKset, hck⟩ := appI_phi_surjective ht2 htX hodd z hzX
  have hkKapp : k ∈ Kapp t X := by rw [hkappKset]; exact hkKset
  refine ⟨(c, k), ⟨hcC, hcX, hkKapp, hck⟩, ?_⟩
  rintro ⟨c', k'⟩ ⟨hc'C, hc'X, hk'Kapp, hc'k'⟩
  have hk'Kset : k' ∈ Kset X t := by rw [hkappKset] at hk'Kapp; exact hk'Kapp
  have heq : c' * k' = c * k := by rw [hc'k', hck]
  obtain ⟨hcc, hkk⟩ :=
    phi_injective ht2 hodd c' c k' k hc'C hc'X hk'Kset hcC hcX hkKset heq
  exact Prod.ext hcc hkk

end Work.NormalComplement
