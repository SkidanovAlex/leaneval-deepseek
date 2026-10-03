import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.letterPow
import Submission.Work.OROneRel.FreiheitssatzCases
import Submission.Work.OROneRel.letters_closure_iff

namespace Work.OROneRel

/-
# A generator occurring once: `⟨α | L₁ · x^e · L₂⟩ ≃* F(α \ {x})`

If the relator `w = FreeGroup.mk (L₁ ++ [(x, e)] ++ L₂)` contains the generator `x` exactly once
(the letters of `L₁` and `L₂` all differ from `x`), then the one-relator group `⟨α | w⟩` is free on
the remaining generators `α \ {x}`.

Write `Y = {a : α // a ≠ x}`, `u = mk L₁`, `v = mk L₂` (supported on `Y`), and `d = u'⁻¹ v'⁻¹`
with `u', v' ∈ F(Y)` the preimages of `u`, `v`.  In `⟨α | w⟩` the relation `u x^e v = 1` expresses
`x` in terms of `Y`, so the canonical map `F(Y) →* ⟨α | w⟩` is surjective; a retraction
`⟨α | w⟩ →* F(Y)` (sending the other letters to themselves and `x` to `d^{±1}`) makes it injective.
-/

theorem letter_once_iso_freeGroup {α : Type*} (x : α) (e : Bool) (L₁ L₂ : List (α × Bool))
    (h : ∀ p ∈ L₁ ++ L₂, p.1 ≠ x) :
    Nonempty (PresentedGroup ({FreeGroup.mk (L₁ ++ [(x, e)] ++ L₂)} : Set (FreeGroup α)) ≃*
      FreeGroup {a : α // a ≠ x}) := by
  classical
  set Y : Set α := {a : α | a ≠ x} with hY
  set w : FreeGroup α := FreeGroup.mk (L₁ ++ [(x, e)] ++ L₂) with hw
  -- the two outer words avoid the generator `x`
  have hsub1 : ∀ p ∈ L₁, p.1 ≠ x := fun p hp => h p (List.mem_append.mpr (Or.inl hp))
  have hsub2 : ∀ p ∈ L₂, p.1 ≠ x := fun p hp => h p (List.mem_append.mpr (Or.inr hp))
  have hmem1 : FreeGroup.mk L₁ ∈ Subgroup.closure (FreeGroup.of '' Y) :=
    mk_mem_closure (fun a b hb => hsub1 (a, b) hb)
  have hmem2 : FreeGroup.mk L₂ ∈ Subgroup.closure (FreeGroup.of '' Y) :=
    mk_mem_closure (fun a b hb => hsub2 (a, b) hb)
  obtain ⟨u', hu'⟩ := exists_lift_of_supportedOn (Z := Y) ((letters_closure_iff _ Y).mp hmem1)
  obtain ⟨v', hv'⟩ := exists_lift_of_supportedOn (Z := Y) ((letters_closure_iff _ Y).mp hmem2)
  set ι : FreeGroup ↥Y →* FreeGroup α :=
    FreeGroup.lift (fun a : Y => FreeGroup.of (a : α)) with hι
  have hιu : ι u' = FreeGroup.mk L₁ := hu'
  have hιv : ι v' = FreeGroup.mk L₂ := hv'
  -- the exponent `s ∈ {±1}` attached to the single letter `x`
  set s : ℤ := (if e then (1 : ℤ) else -1) with hs
  have hss : s * s = 1 := by rw [hs]; cases e <;> norm_num
  set d : FreeGroup ↥Y := u'⁻¹ * v'⁻¹ with hd
  set c : FreeGroup ↥Y := if e then d else d⁻¹ with hc
  set f : α → FreeGroup ↥Y :=
    (fun a => if ha : a = x then c else FreeGroup.of ⟨a, ha⟩) with hf
  have hfx : f x = c := by
    show (if ha : x = x then c else FreeGroup.of ⟨x, ha⟩) = c
    rw [dif_pos rfl]
  have hfne : ∀ a : Y, f (a : α) = FreeGroup.of a := by
    intro a; simp only [hf]; rw [dif_neg a.2]
  -- `f` is a retraction of `ι` on generators
  have hcomp : (FreeGroup.lift f).comp ι = MonoidHom.id (FreeGroup ↥Y) := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    show FreeGroup.lift f (ι (FreeGroup.of a)) = FreeGroup.of a
    have hιa : ι (FreeGroup.of a) = FreeGroup.of (a : α) := by
      rw [hι]; exact FreeGroup.lift_apply_of
    rw [hιa, FreeGroup.lift_apply_of]
    exact hfne a
  have hliftL1 : FreeGroup.lift f (FreeGroup.mk L₁) = u' := by
    rw [← hιu, ← MonoidHom.comp_apply, hcomp, MonoidHom.id_apply]
  have hliftL2 : FreeGroup.lift f (FreeGroup.mk L₂) = v' := by
    rw [← hιv, ← MonoidHom.comp_apply, hcomp, MonoidHom.id_apply]
  have hmk_singleton : FreeGroup.mk [(x, e)] = FreeGroup.of x ^ s := by
    rw [hs]; cases e
    · show FreeGroup.mk [(x, false)] = (FreeGroup.of x) ^ (-1 : ℤ)
      rw [zpow_neg_one]; rfl
    · show FreeGroup.mk [(x, true)] = (FreeGroup.of x) ^ (1 : ℤ)
      rw [zpow_one]; rfl
  have hliftmid : FreeGroup.lift f (FreeGroup.mk [(x, e)]) = c ^ s := by
    rw [hmk_singleton, map_zpow, FreeGroup.lift_apply_of, hfx]
  have hc_eq : c = d ^ s := by
    rw [hc, hs]; cases e
    · show d⁻¹ = d ^ (-1 : ℤ); rw [zpow_neg_one]
    · show d = d ^ (1 : ℤ); rw [zpow_one]
  have hmid : c ^ s = d := by rw [hc_eq, ← zpow_mul, hss, zpow_one]
  -- `w` as a product of the three pieces
  have hw' : w = FreeGroup.mk L₁ * FreeGroup.mk [(x, e)] * FreeGroup.mk L₂ := by
    rw [hw, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, mul_assoc]
  -- `f` kills the relator `w`
  have hliftw : FreeGroup.lift f w = 1 := by
    rw [hw', map_mul, map_mul, hliftL1, hliftL2, hliftmid, hmid, hd]
    group
  -- the retraction `⟨α | w⟩ →* F(Y)`
  have hrel : ∀ r ∈ ({w} : Set (FreeGroup α)), FreeGroup.lift f r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact hliftw
  let φ : PresentedGroup ({w} : Set (FreeGroup α)) →* FreeGroup ↥Y :=
    PresentedGroup.toGroup hrel
  -- the canonical map `F(Y) →* ⟨α | w⟩`
  let ψ : FreeGroup ↥Y →* PresentedGroup ({w} : Set (FreeGroup α)) :=
    (PresentedGroup.mk ({w} : Set (FreeGroup α))).comp ι
  have hψ_of : ∀ a : Y, ψ (FreeGroup.of a) = PresentedGroup.of (a : α) := by
    intro a
    show (PresentedGroup.mk ({w} : Set (FreeGroup α))) (ι (FreeGroup.of a)) =
      PresentedGroup.of (a : α)
    rw [show ι (FreeGroup.of a) = FreeGroup.of (a : α) from by
      rw [hι]; exact FreeGroup.lift_apply_of]
    rfl
  have hφψ : φ.comp ψ = MonoidHom.id (FreeGroup ↥Y) := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    show φ (ψ (FreeGroup.of a)) = FreeGroup.of a
    rw [hψ_of a]
    have h2 : φ (PresentedGroup.of (a : α)) = f (a : α) :=
      PresentedGroup.toGroup.of hrel
    rw [h2]
    exact hfne a
  -- the relation in `⟨α | w⟩`
  have hrel1 : PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk L₁) *
      PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk [(x, e)]) *
      PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk L₂) = 1 := by
    have h0 : PresentedGroup.mk ({w} : Set (FreeGroup α)) w = 1 :=
      PresentedGroup.one_of_mem (Set.mem_singleton w)
    rw [hw', map_mul, map_mul] at h0
    exact h0
  have hAX : PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk L₁) *
      PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk [(x, e)]) =
      (PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk L₂))⁻¹ :=
    (mul_eq_one_iff_eq_inv).mp hrel1
  have hX : PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk [(x, e)]) =
      (PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk L₁))⁻¹ *
      (PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk L₂))⁻¹ := by
    rw [← hAX]; group
  have hX_exp : PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk [(x, e)]) =
      (PresentedGroup.of (rels := ({w} : Set (FreeGroup α))) x) ^ s := by
    rw [hmk_singleton, map_zpow]
    rfl
  -- the values of `ψ` on the pieces
  have hψu : ψ u' = PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk L₁) := by
    show (PresentedGroup.mk ({w} : Set (FreeGroup α))) (ι u') = _
    rw [hιu]
  have hψv : ψ v' = PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk L₂) := by
    show (PresentedGroup.mk ({w} : Set (FreeGroup α))) (ι v') = _
    rw [hιv]
  have hψd : ψ d =
      (PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk L₁))⁻¹ *
      (PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk L₂))⁻¹ := by
    rw [hd, map_mul, map_inv, map_inv, hψu, hψv]
  have hψc : ψ c =
      ((PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk L₁))⁻¹ *
      (PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk L₂))⁻¹) ^ s := by
    rw [hc_eq, map_zpow, hψd]
  have hψφ : ψ.comp φ = MonoidHom.id (PresentedGroup ({w} : Set (FreeGroup α))) := by
    refine PresentedGroup.ext fun a => ?_
    show ψ (φ (PresentedGroup.of a)) = PresentedGroup.of a
    by_cases ha : a = x
    · rw [ha]
      have hφx : φ (PresentedGroup.of x) = c := by
        rw [show φ (PresentedGroup.of x) = f x from PresentedGroup.toGroup.of hrel, hfx]
      rw [hφx, hψc]
      have hAB : (PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk L₁))⁻¹ *
          (PresentedGroup.mk ({w} : Set (FreeGroup α)) (FreeGroup.mk L₂))⁻¹ =
          (PresentedGroup.of (rels := ({w} : Set (FreeGroup α))) x) ^ s := by
        rw [← hX, hX_exp]
      rw [hAB, ← zpow_mul, hss, zpow_one]
    · have hfa : f a = FreeGroup.of ⟨a, ha⟩ := by
        simp only [hf]; rw [dif_neg ha]
      have hφa : φ (PresentedGroup.of a) = FreeGroup.of ⟨a, ha⟩ := by
        rw [show φ (PresentedGroup.of a) = f a from PresentedGroup.toGroup.of hrel, hfa]
      rw [hφa]
      show ψ (FreeGroup.of ⟨a, ha⟩) = PresentedGroup.of a
      rw [hψ_of ⟨a, ha⟩]
  exact ⟨MonoidHom.toMulEquiv φ ψ hψφ hφψ⟩

end Work.OROneRel
