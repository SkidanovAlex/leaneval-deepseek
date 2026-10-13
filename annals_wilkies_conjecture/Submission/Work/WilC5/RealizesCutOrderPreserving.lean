import Mathlib
import Submission.Work.WilC5.realizes_cut
import Submission.Work.WilC5.exists_cut_point_finset
import Submission.Work.WilC5.Saturation

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG FirstOrder Language
open scoped FirstOrder

/-- **Realisation of a cut from order preservation alone** (the `rexp`-reduct of the vdDMM §4 layer
of area C5 lives at a `Work.WilC5.reductStruct`-`LRc`-structure, so the existing
`Work.WilC5.realizes_cut` — which derives order preservation from `↥F ⊨ TR` and converts `leEL` to
`≤` by `Work.WilC5.leEL_iff_le` — is not applicable there; this is the same argument with those two
inputs, `hord` and `hleL`, supplied by the caller instead).

`L` is `κ`-saturated for the ambient `LRc`-structure, `σ : ↥F ↪ L` is order preserving for the
field orders, `leEL` of `L` is the field order, and `κ > |F|`.  Then some `y ∈ L` realises the
image under `σ` of the cut of `x` over `F`:
`f < x ↔ σ f < y` and `x < f ↔ y < σ f` for every `f ∈ F`. -/
theorem RealizesCutOrderPreserving
    {K L : Type} [FirstOrder.Language.Structure WilkiesDesign.CG.LRc K]
      [FirstOrder.Language.Structure WilkiesDesign.CG.LRc L]
    [Field K] [LinearOrder K] [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    (F : WilkiesDesign.CG.LRc.Substructure K) (σ : WilkiesDesign.CG.LRc.Embedding F L) (x : K)
    (hord : ∀ f g : ↥F, (f : K) ≤ (g : K) → (σ f : L) ≤ (σ g : L))
    (hleL : ∀ a b : L, Work.WilC5.leEL a b ↔ a ≤ b)
    (κ : Cardinal.{0}) (hκ : Cardinal.mk ↥F < κ)
    (hsat : @Work.WilC5.IsSaturated WilkiesDesign.CG.LRc L _ κ) :
    ∃ y : L, (∀ f : ↥F, ((f : K) < x ↔ (σ f : L) < y)) ∧
      (∀ f : ↥F, (x < (f : K) ↔ y < (σ f : L))) := by
  classical
  -- the parameter set: the image of `F` in `L`
  set A : Set L := Set.range (fun f : ↥F => (σ f : L)) with hAdef
  let σA : ↥F → ↥A := fun f => ⟨(σ f : L), Set.mem_range_self f⟩
  have hσA : ∀ f : ↥F, ((σA f : ↥A) : L) = (σ f : L) := fun f => rfl
  have hcardA : Cardinal.mk ↥A < κ := by
    rw [hAdef]
    exact lt_of_le_of_lt Cardinal.mk_range_le hκ
  -- the type of the cut
  let P : LRc.Formula (↥A ⊕ Fin 1) → Prop := fun φ =>
    ∃ f : ↥F, (φ = cutLt (σA f) ∧ (f : K) ≤ x) ∨ (φ = cutGt (σA f) ∧ x ≤ (f : K)) ∨
      (φ = cutNe (σA f) ∧ (f : K) ≠ x)
  let p : Set (LRc.Formula (↥A ⊕ Fin 1)) := {φ | P φ}
  -- every finite fragment of the type is realized
  have hp_fin : ∀ T : Finset (LRc.Formula (↥A ⊕ Fin 1)), (∀ φ ∈ T, φ ∈ p) →
      ∃ v : Fin 1 → L, ∀ φ ∈ T,
        @BoundedFormula.Realize LRc L _ (↥A ⊕ Fin 1) 0 φ (Sum.elim (Subtype.val : ↥A → L) v)
          (fun i : Fin 0 => i.elim0) := by
    intro T hT
    let wit : (φ : LRc.Formula (↥A ⊕ Fin 1)) → φ ∈ p → ↥F :=
      fun φ h => Classical.choose (show P φ from h)
    have hwit : ∀ (φ : LRc.Formula (↥A ⊕ Fin 1)) (h : φ ∈ p),
        (φ = cutLt (σA (wit φ h)) ∧ (wit φ h : K) ≤ x) ∨
        (φ = cutGt (σA (wit φ h)) ∧ x ≤ (wit φ h : K)) ∨
        (φ = cutNe (σA (wit φ h)) ∧ (wit φ h : K) ≠ x) :=
      fun φ h => Classical.choose_spec (show P φ from h)
    let S : Finset ↥F := T.attach.image (fun b => wit b.1 (hT b.1 b.2))
    obtain ⟨y, hy1, hy2, hy3⟩ :=
      exists_cut_point_finset F (fun f : ↥F => (σ f : L)) x S hord (fun a b h => σ.injective h)
    refine ⟨fun _ => y, fun φ hφ => ?_⟩
    have hmem : wit φ (hT φ hφ) ∈ S :=
      Finset.mem_image.mpr ⟨⟨φ, hφ⟩, Finset.mem_attach T ⟨φ, hφ⟩, rfl⟩
    rcases hwit φ (hT φ hφ) with ⟨h1, h1'⟩ | ⟨h2, h2'⟩ | ⟨h3, h3'⟩
    · rw [h1]
      refine (cutBounded_iff _ _).mp ((cutLt_realize (σA (wit φ (hT φ hφ)))
        (Sum.elim (Subtype.val : ↥A → L) (fun _ : Fin 1 => y))).mpr ?_)
      simpa [hσA] using (hleL (σ (wit φ (hT φ hφ))) y).mpr
        (hy1 (wit φ (hT φ hφ)) hmem h1')
    · rw [h2]
      refine (cutBounded_iff _ _).mp ((cutGt_realize (σA (wit φ (hT φ hφ)))
        (Sum.elim (Subtype.val : ↥A → L) (fun _ : Fin 1 => y))).mpr ?_)
      simpa [hσA] using (hleL y (σ (wit φ (hT φ hφ)))).mpr
        (hy2 (wit φ (hT φ hφ)) hmem h2')
    · rw [h3]
      refine (cutBounded_iff _ _).mp ((cutNe_realize (σA (wit φ (hT φ hφ)))
        (Sum.elim (Subtype.val : ↥A → L) (fun _ : Fin 1 => y))).mpr ?_)
      simpa [hσA] using hy3 (wit φ (hT φ hφ)) hmem h3'
  -- `κ`-saturation realizes the type
  obtain ⟨v, hv⟩ := hsat A hcardA p hp_fin
  -- unfolding the realization of the three families of formulas
  have key : ∀ φ : LRc.Formula (↥A ⊕ Fin 1), φ ∈ p →
      φ.Realize (Sum.elim (Subtype.val : ↥A → L) v) := fun φ h =>
    (cutBounded_iff φ _).mpr (hv φ h)
  have hL : ∀ f : ↥F, (f : K) ≤ x → leEL (σ f : L) (v 0) := fun f hf =>
    (cutLt_realize (σA f) (Sum.elim (Subtype.val : ↥A → L) v)).mp
      (key (cutLt (σA f)) ⟨f, Or.inl ⟨rfl, hf⟩⟩)
  have hG : ∀ f : ↥F, x ≤ (f : K) → leEL (v 0) (σ f : L) := fun f hf =>
    (cutGt_realize (σA f) (Sum.elim (Subtype.val : ↥A → L) v)).mp
      (key (cutGt (σA f)) ⟨f, Or.inr (Or.inl ⟨rfl, hf⟩)⟩)
  have hN : ∀ f : ↥F, (f : K) ≠ x → v 0 ≠ (σ f : L) := fun f hf =>
    (cutNe_realize (σA f) (Sum.elim (Subtype.val : ↥A → L) v)).mp
      (key (cutNe (σA f)) ⟨f, Or.inr (Or.inr ⟨rfl, hf⟩)⟩)
  refine ⟨v 0, ?_, ?_⟩
  · intro f
    refine ⟨fun hfx => ?_, fun hlt => ?_⟩
    · -- `f < x` gives `σ f ≤ y` and `y ≠ σ f`
      exact lt_of_le_of_ne
        ((hleL (σ f : L) (v 0)).mp (hL f (le_of_lt hfx)))
        (Ne.symm (hN f (ne_of_lt hfx)))
    · -- conversely `σ f < y` forces `f < x`
      rcases le_total (f : K) x with hle | hle
      · by_contra hcon
        have hxeq : (f : K) = x := le_antisymm hle (le_of_not_gt hcon)
        have hb := (hleL (v 0) (σ f : L)).mp (hG f (le_of_eq hxeq.symm))
        exact absurd hb (not_le.mpr hlt)
      · have hb := (hleL (v 0) (σ f : L)).mp (hG f hle)
        exact absurd hb (not_le.mpr hlt)
  · intro f
    refine ⟨fun hxf => ?_, fun hlt => ?_⟩
    · -- `x < f` gives `y ≤ σ f` and `y ≠ σ f`
      exact lt_of_le_of_ne
        ((hleL (v 0) (σ f : L)).mp (hG f (le_of_lt hxf)))
        (hN f (ne_of_gt hxf))
    · -- conversely `y < σ f` forces `x < f`
      rcases le_total x (f : K) with hle | hle
      · by_contra hcon
        have hxeq : (f : K) = x := le_antisymm (le_of_not_gt hcon) hle
        have hb := (hleL (σ f : L) (v 0)).mp (hL f (le_of_eq hxeq))
        exact absurd hb (not_le.mpr hlt)
      · have hb := (hleL (σ f : L) (v 0)).mp (hL f hle)
        exact absurd hb (not_le.mpr hlt)

end Work.WilC5
