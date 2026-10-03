import Mathlib
import Submission.Work.OROneRel.presentedGroup_of_zpow_iso_coprod_zmod

namespace Work.OROneRel

universe u

theorem presentedGroup_of_zpow_iso_coprod_zmod_of_gen {α : Type u} (x : α) (m : ℤ) (hm : m ≠ 0) :
    ∃ e : PresentedGroup ({FreeGroup.of x ^ m} : Set (FreeGroup α)) ≃*
        Monoid.Coprod (Multiplicative (ZMod m.natAbs)) (FreeGroup {a : α // a ≠ x}),
      e (PresentedGroup.of (rels := ({FreeGroup.of x ^ m} : Set (FreeGroup α))) x)
        = Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod m.natAbs)) := by
  classical
  let G := PresentedGroup ({FreeGroup.of x ^ m} : Set (FreeGroup α))
  let C := Monoid.Coprod (Multiplicative (ZMod m.natAbs)) (FreeGroup {a : α // a ≠ x})
  have hpow : (PresentedGroup.of x : G) ^ m = 1 := by
    rw [show (PresentedGroup.of x : G) = PresentedGroup.mk _ (FreeGroup.of x) from rfl,
      ← map_zpow]
    exact PresentedGroup.one_of_mem (by simp)
  have hkpow : (PresentedGroup.of x : G) ^ m.natAbs = 1 := zpow_natAbs_eq_one _ m hpow
  let f : α → C := fun a => if h : a = x then Monoid.Coprod.inl (Multiplicative.ofAdd 1)
                            else Monoid.Coprod.inr (FreeGroup.of ⟨a, h⟩)
  have hfx : f x = Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod m.natAbs)) := by simp [f]
  have hrel : ∀ r ∈ ({FreeGroup.of x ^ m} : Set (FreeGroup α)), FreeGroup.lift f r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    rw [map_zpow, FreeGroup.lift_apply_of]
    rw [hfx, ← map_zpow]
    have hcyc : (Multiplicative.ofAdd (1 : ZMod m.natAbs)) ^ m = 1 := by
      rw [← ofAdd_zsmul, zsmul_one]
      have h0 : (m : ZMod m.natAbs) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact Int.natAbs_dvd.mpr (dvd_refl m)
      rw [h0, ofAdd_zero]
    rw [hcyc, map_one]
  let Φ : G →* C := PresentedGroup.toGroup (f := f) hrel
  have hΦ_of (a : α) : Φ (PresentedGroup.of a) = f a :=
    PresentedGroup.toGroup.of (f := f) hrel
  let φ₂ : FreeGroup {a : α // a ≠ x} →* G := FreeGroup.lift (fun b => PresentedGroup.of (b : α))
  let φ₁ : Multiplicative (ZMod m.natAbs) →* G :=
    zmodHomOfPowEqOne (m.natAbs) (PresentedGroup.of x) hkpow
  have hφ₁ : φ₁ (Multiplicative.ofAdd 1) = PresentedGroup.of x :=
    zmodHomOfPowEqOne_ofAdd_one (m.natAbs) (PresentedGroup.of x) hkpow
  let Ψ : C →* G := Monoid.Coprod.lift φ₁ φ₂
  have hΨΦ : Ψ.comp Φ = MonoidHom.id G := by
    apply PresentedGroup.ext
    intro a
    rw [MonoidHom.comp_apply, hΦ_of, MonoidHom.id_apply]
    by_cases ha : a = x
    · rw [ha, hfx, Monoid.Coprod.lift_apply_inl, hφ₁]
    · rw [show f a = Monoid.Coprod.inr (FreeGroup.of ⟨a, ha⟩) from by simp [f, ha],
        Monoid.Coprod.lift_apply_inr]
      simp [φ₂]
  have hΦΨ : Φ.comp Ψ = MonoidHom.id C := by
    apply Monoid.Coprod.hom_ext
    · rw [MonoidHom.comp_assoc, Monoid.Coprod.lift_comp_inl, MonoidHom.id_comp]
      apply zmod_hom_ext_one
      rw [MonoidHom.comp_apply, hφ₁, hΦ_of]
      exact hfx
    · rw [MonoidHom.comp_assoc, Monoid.Coprod.lift_comp_inr, MonoidHom.id_comp]
      apply FreeGroup.ext_hom
      intro b
      rw [MonoidHom.comp_apply]
      simp only [φ₂, FreeGroup.lift_apply_of]
      rw [hΦ_of]
      simp only [f]
      rw [dif_neg b.2]
  refine ⟨MonoidHom.toMulEquiv Φ Ψ hΨΦ hΦΨ, ?_⟩
  rw [MonoidHom.toMulEquiv_apply, hΦ_of]
  exact hfx

end Work.OROneRel
