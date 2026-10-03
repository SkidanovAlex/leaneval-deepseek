import Mathlib

universe u

namespace Work.OROneRel

/-- **Generation of a one-relator group by a vertex subgroup and a stable letter.**  Let
`f : ⟨β | v ^ l⟩ →* ⟨α | u ^ l⟩` be a base map of a candidate splitting, `c : α → ℤ` a weight,
`W : ℤ → FreeGroup α` a gauge of the `ℤ`-cover and `τ` a "deck" element.  Assume that for every
generator `x : α` there is a level `i` such that the *path classes* `W i · τ ^ (-i)` and
`W (i + c x) · τ ^ (-(i + c x))` and the *loop class* `W i · x · (W (i + c x))⁻¹` all lie in the
image `f.range`.  Then `f.range` together with the class of `τ` generates `⟨α | u ^ l⟩`. -/
theorem generation_of_level_factors {α : Type u} (u : FreeGroup α) (l : ℕ)
    {β : Type u} (v : FreeGroup β)
    (f : PresentedGroup ({v ^ l} : Set (FreeGroup β)) →*
          PresentedGroup ({u ^ l} : Set (FreeGroup α)))
    (c : α → ℤ) (W : ℤ → FreeGroup α) (τ : FreeGroup α)
    (hfac : ∀ x : α, ∃ i : ℤ,
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (W i) *
          (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-i) ∈ f.range ∧
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (W (i + c x)) *
          (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-(i + c x)) ∈ f.range ∧
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
          (W i * FreeGroup.of x * (W (i + c x))⁻¹) ∈ f.range) :
    f.range ⊔ Subgroup.closure
        {PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ} = ⊤ := by
  -- Write the target subgroup as `S`, a definite name.
  set S : Subgroup (PresentedGroup ({u ^ l} : Set (FreeGroup α))) :=
    f.range ⊔ Subgroup.closure {PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ} with hS
  -- It suffices to show that `S` contains the classes of all the free generators.
  have key : ∀ x : α, PresentedGroup.of x ∈ S := by
    intro x
    obtain ⟨i, h1, h2, h3⟩ := hfac x
    rw [hS]
    -- The "loop" class `τ^i · x · τ^(-(i + c x))`, obtained as `A⁻¹ · C · B`.
    have hmid : (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (W i) *
          (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-i))⁻¹ *
        PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
          (W i * FreeGroup.of x * (W (i + c x))⁻¹) *
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (W (i + c x)) *
          (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-(i + c x)))
      ∈ f.range ⊔ Subgroup.closure {PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ} :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left h1))
        (Subgroup.mem_sup_left h3)) (Subgroup.mem_sup_left h2)
    have hτ : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ ∈
        Subgroup.closure {PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ} :=
      Subgroup.subset_closure (Set.mem_singleton _)
    have hτ' : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ ∈
        f.range ⊔ Subgroup.closure {PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ} :=
      Subgroup.mem_sup_right hτ
    -- Cancel the gauges to exhibit `x` as a product of a `τ`-power, the loop class, and a
    -- `τ`-power back.
    have heq : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (FreeGroup.of x) =
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-i) *
          ((PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (W i) *
            (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-i))⁻¹ *
            PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
              (W i * FreeGroup.of x * (W (i + c x))⁻¹) *
            (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (W (i + c x)) *
              (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (-(i + c x))))
          * (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) ^ (i + c x) := by
      simp only [map_mul, map_inv]; group
    change PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (FreeGroup.of x) ∈
      f.range ⊔ Subgroup.closure {PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ}
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (zpow_mem hτ' (-i)) hmid) (zpow_mem hτ' (i + c x))
  -- Since the generators of `PresentedGroup {u ^ l}` all lie in `S`, we get `S = ⊤`.
  rw [eq_top_iff]
  intro g _
  exact PresentedGroup.generated_by _ S key g

end Work.OROneRel
