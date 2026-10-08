import Mathlib

open scoped IsMulCommutative

namespace Work.DSTR.M110

/-- Let `Z = ⟨z⟩` be cyclic and suppose `x` acts on `Z` by the `ε`-th power map
(`x * w * x⁻¹ = w ^ ε` for `w ∈ Z`).  Then the number of conjugates `w * x * w⁻¹`
(`w ∈ Z`), multiplied by the number of `w ∈ Z` fixed by `x` (`w ^ ε = w`), equals `|Z|`.

Indeed `w * x * w⁻¹ = w ^ (1 - ε) * x`, so the conjugates form a coset of the image of the
power map `w ↦ w ^ (1 - ε)` on the cyclic group `Z`, whose kernel is exactly the fixed-point
set; the statement is then the first isomorphism theorem. -/
theorem orbitCardZpowers {G : Type*} [Group G] [Finite G] (z x : G) (ε : ℤ)
    (hact : ∀ w ∈ Subgroup.zpowers z, x * w * x⁻¹ = w ^ ε) :
    Nat.card {y : G // ∃ w ∈ Subgroup.zpowers z, y = w * x * w⁻¹} *
        Nat.card {w : G // w ∈ Subgroup.zpowers z ∧ w ^ ε = w} =
      Nat.card (Subgroup.zpowers z) := by
  let Z : Subgroup G := Subgroup.zpowers z
  let p : ↥Z →* ↥Z := MonoidHom.mk' (fun w => w ^ (1 - ε)) (fun a b => mul_zpow a b (1 - ε))
  have hp : ∀ u : ↥Z, p u = u ^ (1 - ε) := fun u => rfl
  -- the key identity: `w * x * w⁻¹` is a translate of `w ^ (1 - ε)`
  have hkey : ∀ (w : G) (hw : w ∈ Subgroup.zpowers z),
      w * x * w⁻¹ = (((⟨w, hw⟩ : ↥Z)) ^ (1 - ε) : ↥Z) * x := by
    intro w hw
    have hw' := hact w⁻¹ ((Subgroup.zpowers z).inv_mem hw)
    have hcoe : (((⟨w, hw⟩ : ↥Z) ^ (1 - ε) : ↥Z) : G) = w ^ (1 - ε) :=
      Subgroup.coe_zpow _ ⟨w, hw⟩ (1 - ε)
    rw [hcoe]
    calc w * x * w⁻¹
        = w * (x * w⁻¹ * x⁻¹) * x := by group
      _ = w * (w ^ ε)⁻¹ * x := by rw [hw', inv_zpow]
      _ = w ^ (1 - ε) * x := by rw [sub_eq_add_neg, zpow_add, zpow_one, zpow_neg]
  -- `ker p` is the fixed-point set
  have hker_iff : ∀ u : ↥Z, p u = 1 ↔ (u : G) ^ ε = (u : G) := by
    intro u
    constructor
    · intro hu
      have hu1 : (u : G) ^ (1 - ε) = 1 := by
        have h : ((u ^ (1 - ε) : ↥Z) : G) = ((1 : ↥Z) : G) := by
          have h' := congrArg (fun t : ↥Z => (t : G)) hu
          rwa [hp u] at h'
        simpa [Subgroup.coe_zpow, Subgroup.coe_one] using h
      have hmain : (u : G) ^ ε * (u : G) ^ (1 - ε) = (u : G) := by
        rw [← zpow_add]
        rw [show ε + (1 - ε) = 1 by ring, zpow_one]
      calc (u : G) ^ ε = (u : G) ^ ε * 1 := (mul_one _).symm
        _ = (u : G) ^ ε * (u : G) ^ (1 - ε) := by rw [hu1]
        _ = (u : G) := hmain
    · intro hu
      apply Subtype.ext
      show ((u ^ (1 - ε) : ↥Z) : G) = ((1 : ↥Z) : G)
      rw [Subgroup.coe_zpow, Subgroup.coe_one, zpow_sub, hu]
      group
  -- the conjugates are in bijection with the image of the power map
  have hA : Nat.card {y : G // ∃ w ∈ Subgroup.zpowers z, y = w * x * w⁻¹}
      = Nat.card ↥p.range := by
    let F : ↥p.range → {y : G // ∃ w ∈ Subgroup.zpowers z, y = w * x * w⁻¹} := fun u =>
      ⟨(u.1 : G) * x, by
        obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp u.2
        refine ⟨(w : G), w.2, ?_⟩
        have h1 : (u.1 : G) = (w : G) ^ (1 - ε) := by
          rw [← hw]; exact Subgroup.coe_zpow _ w (1 - ε)
        rw [h1, hkey (w : G) w.2, Subgroup.coe_zpow, Subgroup.coe_mk]⟩
    have hinj : Function.Injective F := by
      intro u v huv
      have h2 : (u.1 : G) * x = (v.1 : G) * x := congrArg Subtype.val huv
      exact Subtype.ext (Subtype.ext (mul_right_cancel h2))
    have hsurj : Function.Surjective F := by
      rintro ⟨y, w, hw, hy⟩
      refine ⟨⟨⟨w, hw⟩ ^ (1 - ε), MonoidHom.mem_range.mpr ⟨⟨w, hw⟩, hp ⟨w, hw⟩⟩⟩, ?_⟩
      apply Subtype.ext
      show (((⟨w, hw⟩ : ↥Z) ^ (1 - ε) : ↥Z) : G) * x = y
      rw [hy, hkey w hw]
    exact (Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)).symm
  -- the fixed points are in bijection with the kernel of the power map
  have hB : Nat.card {w : G // w ∈ Subgroup.zpowers z ∧ w ^ ε = w} = Nat.card ↥p.ker := by
    let F : {w : G // w ∈ Subgroup.zpowers z ∧ w ^ ε = w} → ↥p.ker := fun w =>
      ⟨⟨(w.1 : G), w.2.1⟩, (hker_iff _).mpr w.2.2⟩
    have hinj : Function.Injective F := by
      intro a b hab
      have h1 : (⟨(a.1 : G), a.2.1⟩ : ↥Z) = ⟨(b.1 : G), b.2.1⟩ := congrArg Subtype.val hab
      exact Subtype.ext (congrArg (fun t : ↥Z => (t : G)) h1)
    have hsurj : Function.Surjective F := by
      rintro ⟨u, hu⟩
      refine ⟨⟨(u : G), u.2, (hker_iff u).mp hu⟩, ?_⟩
      exact Subtype.ext (Subtype.ext rfl)
    exact Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)
  rw [hA, hB, mul_comm]
  exact Subgroup.card_ker_mul_card_range p

end Work.DSTR.M110
