import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

/-- **Transfer of the "Freiheitssatz for the domain" to the vertex presentation of the Magnus
step.**  Let `ρ : F β →* F α` be the class map of a subcomplex of the `ℤ`-cover (in the application
`ρ = coverToClasses`, `v = coverRoot`, `ρ (v ^ l) = u ^ l`), and assume the *preimage* statement
that the class map pulls the normal closure of `u ^ l` back to the normal closure of `v ^ l`.  Then
the induced map of one-relator groups `⟨β | v ^ l⟩ →* ⟨α | u ^ l⟩` — which exists because
`ρ (v ^ l) = u ^ l` (this follows from `hpre` at `x = v ^ l`) — is injective and is the map induced
by `ρ`, i.e. it carries the class of `x` to the class of `ρ x`.  This is the step that identifies
the vertex group of the HNN splitting with `⟨β | v ^ l⟩`.

Suggested proof: define `Φ` with `PresentedGroup.toGroup` (or as `QuotientGroup.map` between the
quotients by the two normal closures) from the well-definedness direction of `hpre`; then for
injectivity use `PresentedGroup.mk_surjective` to write an element as `mk x`, and
`PresentedGroup.mk_eq_one_iff` twice together with the injectivity direction of `hpre`. -/
theorem presentedGroup_map_injective_of_preimage {β α : Type u} (ρ : FreeGroup β →* FreeGroup α)
    (v : FreeGroup β) (u : FreeGroup α) (l : ℕ)
    (hpre : ∀ x : FreeGroup β,
      ρ x ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) ↔
        x ∈ Subgroup.normalClosure ({v ^ l} : Set (FreeGroup β))) :
    ∃ Φ : PresentedGroup ({v ^ l} : Set (FreeGroup β)) →*
        PresentedGroup ({u ^ l} : Set (FreeGroup α)),
      Function.Injective Φ ∧
        ∀ x : FreeGroup β,
          Φ (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) x)
            = PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (ρ x) := by
  -- The class map `ρ` sends `N := normalClosure {v ^ l}` into `M := normalClosure {u ^ l}`,
  -- so it descends to the quotients `⟨β | v ^ l⟩ →* ⟨α | u ^ l⟩`.
  have hmap : Subgroup.normalClosure ({v ^ l} : Set (FreeGroup β)) ≤
      (Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α))).comap ρ := by
    intro x hx
    rw [Subgroup.mem_comap]
    exact (hpre x).mpr hx
  let Φ : PresentedGroup ({v ^ l} : Set (FreeGroup β)) →*
      PresentedGroup ({u ^ l} : Set (FreeGroup α)) :=
    QuotientGroup.map (Subgroup.normalClosure ({v ^ l} : Set (FreeGroup β)))
      (Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α))) ρ hmap
  -- `Φ` is the map induced by `ρ` on classes.
  have hΦ : ∀ x : FreeGroup β,
      Φ (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) x)
        = PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (ρ x) := fun x => rfl
  refine ⟨Φ, ?_, hΦ⟩
  intro a₁ a₂ h
  -- Reduce `a₁ = a₂` to `a₁ * a₂⁻¹ = 1`.
  have h' : Φ (a₁ * a₂⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h'' : a₁ * a₂⁻¹ = 1 := by
    obtain ⟨x, hx⟩ := PresentedGroup.mk_surjective _ (a₁ * a₂⁻¹)
    rw [← hx] at h' ⊢
    -- `Φ (mk x) = 1` means `ρ x ∈ M`, which by `hpre` means `x ∈ N`, i.e. `mk x = 1`.
    rw [hΦ x, PresentedGroup.mk_eq_one_iff] at h'
    rw [PresentedGroup.mk_eq_one_iff]
    exact (hpre x).mp h'
  exact mul_inv_eq_one.mp h''

end Work.OROneRel
