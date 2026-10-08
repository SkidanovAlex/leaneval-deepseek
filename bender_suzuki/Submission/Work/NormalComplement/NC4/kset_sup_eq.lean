import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.NC4.mul_eq_mul_unique

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.NC4

/-! ## Auxiliary facts used in `kset_sup_eq`

Both are stated for the ambient group `G`, and both are used in `kset_sup_eq` below. -/

/-- If two subgroups `S` and `T` of a group commute elementwise, then the join `S ⊔ T` is the
product set `S·T`: every element of `S ⊔ T` is of the form `s * u` with `s ∈ S`, `u ∈ T`. -/
theorem mem_sup_eq_mul {G : Type} [Group G] {S T : Subgroup G}
    (hcomm : ∀ s ∈ S, ∀ u ∈ T, s * u = u * s) {z : G} (hz : z ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ u ∈ T, z = s * u := by
  rw [Subgroup.sup_eq_closure] at hz
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
      rw [Set.mem_union] at hx
      rcases hx with hx | hx
      · exact ⟨x, hx, 1, T.one_mem, by simp⟩
      · exact ⟨1, S.one_mem, x, hx, by simp⟩
  | one => exact ⟨1, S.one_mem, 1, T.one_mem, by simp⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨s₁, hs₁, u₁, hu₁, rfl⟩ := ihx
      obtain ⟨s₂, hs₂, u₂, hu₂, rfl⟩ := ihy
      refine ⟨s₁ * s₂, S.mul_mem hs₁ hs₂, u₁ * u₂, T.mul_mem hu₁ hu₂, ?_⟩
      calc s₁ * u₁ * (s₂ * u₂) = s₁ * (u₁ * s₂) * u₂ := by simp [mul_assoc]
        _ = s₁ * (s₂ * u₁) * u₂ := by rw [hcomm s₂ hs₂ u₁ hu₁]
        _ = s₁ * s₂ * (u₁ * u₂) := by simp [mul_assoc]
  | inv x _ ihx =>
      obtain ⟨s, hs, u, hu, rfl⟩ := ihx
      exact ⟨s⁻¹, S.inv_mem hs, u⁻¹, T.inv_mem hu, by
        rw [mul_inv_rev, (hcomm s⁻¹ (S.inv_mem hs) u⁻¹ (T.inv_mem hu)).symm]⟩

/-- If `S` and `T` are elementwise commuting subgroups of `E`, then the product of an element of
`Kset S t` and an element of `Kset T t` lies in `Kset E t`. -/
theorem mul_mem_kset {G : Type} [Group G] {t : G} {E S T : Subgroup G}
    (hS : S ≤ E) (hT : T ≤ E)
    (hcomm : ∀ s ∈ S, ∀ u ∈ T, s * u = u * s)
    {s u : G} (hs : s ∈ Work.NormalComplement.Kset S t)
    (hu : u ∈ Work.NormalComplement.Kset T t) :
    s * u ∈ Work.NormalComplement.Kset E t := by
  obtain ⟨hsS, hsinv⟩ := hs
  obtain ⟨huT, huinv⟩ := hu
  refine ⟨E.mul_mem (hS hsS) (hT huT), ?_⟩
  have h1 : t * (s * u) * t⁻¹ = (t * s * t⁻¹) * (t * u * t⁻¹) := by simp [mul_assoc]
  have h2 : (s * u)⁻¹ = s⁻¹ * u⁻¹ := by
    rw [mul_inv_rev, (hcomm s⁻¹ (S.inv_mem hsS) u⁻¹ (T.inv_mem huT)).symm]
  rw [h1, hsinv, huinv, h2]

/-- If `E = S ⊔ T` with `S ⊓ T = ⊥`, `S` and `T` elementwise commuting, and `t` normalising both
`S` and `T`, then `Kset E t` is the set of products `s * u` with `s ∈ Kset S t` and `u ∈ Kset T t`
(where `Kset X t = {x ∈ X | t * x * t⁻¹ = x⁻¹}`). -/
theorem kset_sup_eq {G : Type} [Group G] {t : G} {E S T : Subgroup G}
    (hS : S ≤ E) (hT : T ≤ E) (hsup : S ⊔ T = E) (hinf : S ⊓ T = ⊥)
    (hcomm : ∀ s ∈ S, ∀ u ∈ T, s * u = u * s)
    (htS : Work.NormalComplement.NormalizedBy t S)
    (htT : Work.NormalComplement.NormalizedBy t T) :
    Work.NormalComplement.Kset E t =
      {z : G | ∃ s ∈ Work.NormalComplement.Kset S t,
        ∃ u ∈ Work.NormalComplement.Kset T t, z = s * u} := by
  ext z
  constructor
  · -- every `z ∈ Kset E t` is the product of the `S`-part and the `T`-part of `z`
    intro hz
    obtain ⟨hzE, hz2⟩ := hz
    have hzST : z ∈ S ⊔ T := by rw [hsup]; exact hzE
    obtain ⟨s, hs, u, hu, rfl⟩ := mem_sup_eq_mul hcomm hzST
    -- conjugating `s * u` by `t` gives `(t*s*t⁻¹) * (t*u*t⁻¹) = s⁻¹ * u⁻¹`, so the two
    -- factors are inverted by `t` by uniqueness of the decomposition along `S` and `T`
    have hts : t * s * t⁻¹ ∈ S := htS s hs
    have htu : t * u * t⁻¹ ∈ T := htT u hu
    have hkey : (t * s * t⁻¹) * (t * u * t⁻¹) = s⁻¹ * u⁻¹ := by
      have h1 : t * (s * u) * t⁻¹ = (t * s * t⁻¹) * (t * u * t⁻¹) := by simp [mul_assoc]
      have h2 : (s * u)⁻¹ = s⁻¹ * u⁻¹ := by
        rw [mul_inv_rev, (hcomm s⁻¹ (S.inv_mem hs) u⁻¹ (T.inv_mem hu)).symm]
      rw [h1, h2] at hz2
      exact hz2
    obtain ⟨hseq, hueq⟩ :=
      mul_eq_mul_unique hinf hts (S.inv_mem hs) htu (T.inv_mem hu) hkey
    exact ⟨s, ⟨hs, hseq⟩, u, ⟨hu, hueq⟩, rfl⟩
  · rintro ⟨s, hs, u, hu, rfl⟩
    exact mul_mem_kset hS hT hcomm hs hu

end Work.NormalComplement.NC4
