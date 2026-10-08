import Mathlib.Algebra.Group.Subgroup.Finite

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.GroupAction

/-- If a finite subgroup `U` of a finite group `G` fixes a point `z` of a finite
`G`-set `Ω`, if `|Ω| = |U| + 1`, and if `U` acts freely away from `z` (the only
point fixed by a nontrivial `u ∈ U` is `z`), then `U` acts transitively on
`Ω \ {z}`. -/
theorem exists_smul_eq_of_ne_of_card_eq_one_add {G Ω : Type*} [Group G] [MulAction G Ω]
    [Finite G] [Finite Ω] {U : Subgroup G} (z : Ω)
    (hcard : Nat.card Ω = Nat.card ↥U + 1)
    (hfix : ∀ u : U, (u : G) • z = z)
    (hfree : ∀ u : U, u ≠ 1 → ∀ x : Ω, (u : G) • x = x → x = z)
    {x y : Ω} (hx : x ≠ z) (hy : y ≠ z) : ∃ u : U, (u : G) • x = y := by
  classical
  haveI : Fintype Ω := Fintype.ofFinite Ω
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype U := Fintype.ofFinite U
  -- Translate the cardinality hypothesis to `Fintype.card`.
  have hc : Fintype.card Ω = Fintype.card U + 1 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard]
  -- The map `u ↦ u • x` is injective because `U` acts freely away from `z`
  -- and `x ≠ z`.
  have hinj : Function.Injective (fun u : U => (u : G) • x) := by
    intro u v huv
    have huv' : (u : G) • x = (v : G) • x := huv
    have h : ((v⁻¹ * u : U) : G) • x = x := by
      have hcoe : ((v⁻¹ * u : U) : G) = (v : G)⁻¹ * (u : G) := by simp
      rw [hcoe, mul_smul, huv', inv_smul_smul]
    have h1 : v⁻¹ * u = 1 := by
      by_contra hne
      exact hx (hfree (v⁻¹ * u) hne x h)
    have : v = u := by rwa [inv_mul_eq_one] at h1
    exact this.symm
  -- Its image has `|U|` elements.
  have hcard_img : (Finset.univ.image (fun u : U => (u : G) • x)).card = Fintype.card U := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  -- The image lies in `Ω \ {z}`.
  have hsub : Finset.univ.image (fun u : U => (u : G) • x) ⊆ Finset.univ.erase z := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨u, _, rfl⟩ := hw
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro hwz
    have hz : (u : G)⁻¹ • z = z := by simpa using hfix u⁻¹
    exact hx (by calc x = (u : G)⁻¹ • ((u : G) • x) := (inv_smul_smul (u : G) x).symm
                    _ = (u : G)⁻¹ • z := by rw [hwz]
                    _ = z := hz)
  -- `Ω \ {z}` also has `|U|` elements.
  have hcE : (Finset.univ.erase z).card = Fintype.card U := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ, hc, Nat.add_sub_cancel]
  -- Hence the image is all of `Ω \ {z}`.
  have heq : Finset.univ.image (fun u : U => (u : G) • x) = Finset.univ.erase z := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcE, hcard_img]
  -- In particular `y` lies in the image.
  have hyE : y ∈ Finset.univ.erase z := by
    rw [Finset.mem_erase]; exact ⟨hy, Finset.mem_univ y⟩
  rw [← heq, Finset.mem_image] at hyE
  obtain ⟨u, _, hu⟩ := hyE
  exact ⟨u, hu⟩

end Commons.GroupTheory.GroupAction