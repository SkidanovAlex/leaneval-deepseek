import Mathlib

set_option linter.style.haveILetI false

namespace Work.DSG2

open CategoryTheory Limits AlgebraicGeometry

/-- Two morphisms `f g : X ⟶ Z` that coincide after composing with a scheme-theoretically
dominant `i : Y ⟶ X` and that both equalize a separated morphism `q : Z ⟶ W` must be equal. -/
theorem eq_of_isSchemeTheoreticallyDominant {Y X Z W : AlgebraicGeometry.Scheme}
    (i : Y ⟶ X) [AlgebraicGeometry.IsSchemeTheoreticallyDominant i] {f g : X ⟶ Z} {p : X ⟶ W}
    {q : Z ⟶ W} (hf : CategoryTheory.CategoryStruct.comp f q = p)
    (hg : CategoryTheory.CategoryStruct.comp g q = p) [AlgebraicGeometry.IsSeparated q]
    (h : CategoryTheory.CategoryStruct.comp i f = CategoryTheory.CategoryStruct.comp i g) :
    f = g := by
  -- `f` and `g` give a morphism `φ : X ⟶ Z ×_W Z`.
  have hfg : f ≫ q = g ≫ q := hf.trans hg.symm
  let φ : X ⟶ pullback q q := pullback.lift f g hfg
  have hφfst : φ ≫ pullback.fst q q = f := pullback.lift_fst f g hfg
  have hφsnd : φ ≫ pullback.snd q q = g := pullback.lift_snd f g hfg
  -- The equalizer of `f` and `g` is the pullback of the diagonal along `φ`; since `q` is
  -- separated, it is a closed immersion `e : E ⟶ X`.
  let e : pullback φ (pullback.diagonal q) ⟶ X := pullback.fst φ (pullback.diagonal q)
  have hcond : e ≫ φ = pullback.snd φ (pullback.diagonal q) ≫ pullback.diagonal q :=
    pullback.condition
  have hef : e ≫ f = pullback.snd φ (pullback.diagonal q) := by
    rw [← hφfst, ← Category.assoc, hcond, Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have heg : e ≫ g = pullback.snd φ (pullback.diagonal q) := by
    rw [← hφsnd, ← Category.assoc, hcond, Category.assoc, pullback.diagonal_snd, Category.comp_id]
  have heq : e ≫ f = e ≫ g := hef.trans heg.symm
  -- Since `i ≫ f = i ≫ g`, `i` factors through `e`.
  have hiff : i ≫ φ = (i ≫ f) ≫ pullback.diagonal q := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφfst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, hφsnd, Category.assoc, pullback.diagonal_snd, Category.comp_id]
      exact h.symm
  let i' : Y ⟶ pullback φ (pullback.diagonal q) := pullback.lift i (i ≫ f) hiff
  have hi'e : i' ≫ e = i := pullback.lift_fst i (i ≫ f) hiff
  -- The kernel of `e` contains the kernel of `i ≫ e = i`, which is `⊥`.
  have hbot : e.ker = ⊥ := by
    have h1 : e.ker ≤ i.ker := by
      have h2 := Scheme.Hom.le_ker_comp i' e
      rw [hi'e] at h2
      exact h2
    rw [Scheme.Hom.ker_eq_bot i] at h1
    exact le_bot_iff.mp h1
  have hiso : IsIso e := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hbot
  haveI : IsIso e := hiso
  calc f = 𝟙 X ≫ f := (Category.id_comp f).symm
    _ = (inv e ≫ e) ≫ f := by rw [IsIso.inv_hom_id]
    _ = inv e ≫ (e ≫ f) := Category.assoc _ _ _
    _ = inv e ≫ (e ≫ g) := by rw [heq]
    _ = (inv e ≫ e) ≫ g := (Category.assoc _ _ _).symm
    _ = 𝟙 X ≫ g := by rw [IsIso.inv_hom_id]
    _ = g := Category.id_comp g

end Work.DSG2
