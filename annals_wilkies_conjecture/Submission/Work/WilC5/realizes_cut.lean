/-
  WilC5 — realization of the cut of an element in a saturated model.

  vdDMM §4 (Lemma 4.2) needs, for a submodel `F ⊆ K` of a model of `TR` and an embedding
  `σ : F ↪ N` into a `κ`-saturated model `N` with `κ > |F|`, a point `y ∈ N` which is the image
  of the *cut* of `x ∈ K` over `F`: `f < x ↔ σ f < y` for every `f ∈ F`.  This module supplies it.

  The type whose realization is asked for is the set of `LRc`-formulas (with the parameters of
  `A = σ '' F`) saying, for each `f : F`,

  * `σ f ≤ v` when `f ≤ x`,  * `v ≤ σ f` when `x ≤ f`,  * `v ≠ σ f` when `f ≠ x`;

  the last family of formulas is what upgrades the two weak inequalities to the two strict ones
  required by the cut (`y = σ f` would leave the cut undetermined).  Since `LRc` has no relation
  symbols, `≤` is spelled with the definable order `leEL x y := ∃z, z*z = y - x`
  (`LRcOps.lean`, `tr_leE_axioms.lean`); `Work.WilC5.leEL_iff_le` identifies it with the order of
  the model.

  Finite satisfiability of the type is the elementary fact that a *finite* set of such conditions
  is consistent: the constraints coming from `f ≤ x` are bounded above by those coming from
  `x ≤ f`, because `σ` is order preserving (`Work.WilC5.realizes_cut_order_preserving`, which
  transports the definable order along the embedding), and the exceptional case `x ∈ σ '' F`
  forces `y = σ f` and is consistent for the same reason.  `κ`-saturation then realizes the
  whole type.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilC5.Saturation
import Submission.Work.WilC5.ValArith
import Submission.Work.WilC5.tr_leE_axioms
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.embedding_map_leEL
import Submission.Work.WilC5.realizes_cut_order_preserving
import Submission.Work.WilC5.exists_cut_point_finset

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace Work.WilC5

open FirstOrder Language
open WilkiesDesign WilkiesDesign.CG
open scoped FirstOrder

/-! ## 1. The formulas of the cut -/

/-- The `LRc`-formula `a ≤ v`, with the parameter `a : A` and the single free variable `v`
(represented by the `Fin 1` block of the index type `A ⊕ Fin 1`). -/
def cutLt {A : Type} (a : A) : LRc.Formula (A ⊕ Fin 1) :=
  leFormL (Term.var (Sum.inl (Sum.inl a))) (Term.var (Sum.inl (Sum.inr (0 : Fin 1))))

/-- The `LRc`-formula `v ≤ a`. -/
def cutGt {A : Type} (a : A) : LRc.Formula (A ⊕ Fin 1) :=
  leFormL (Term.var (Sum.inl (Sum.inr (0 : Fin 1)))) (Term.var (Sum.inl (Sum.inl a)))

/-- The `LRc`-formula `v ≠ a`. -/
def cutNe {A : Type} (a : A) : LRc.Formula (A ⊕ Fin 1) :=
  (Term.equal (Term.var (Sum.inr (0 : Fin 1))) (Term.var (Sum.inl a))).not

section CutFormulas

variable {A M : Type} [LRc.Structure M]

/-- Realization of `cutLt`. -/
theorem cutLt_realize (a : A) (v : A ⊕ Fin 1 → M) :
    (cutLt a).Realize v ↔ leEL (v (Sum.inl a)) (v (Sum.inr 0)) := by
  have h := leFormL_realize (t₁ := Term.var (Sum.inl (Sum.inl a)))
    (t₂ := Term.var (Sum.inl (Sum.inr (0 : Fin 1)))) (v := v) (xs := (default : Fin 0 → M))
  simpa [cutLt, Formula.Realize, Term.realize_var] using h

/-- Realization of `cutGt`. -/
theorem cutGt_realize (a : A) (v : A ⊕ Fin 1 → M) :
    (cutGt a).Realize v ↔ leEL (v (Sum.inr 0)) (v (Sum.inl a)) := by
  have h := leFormL_realize (t₁ := Term.var (Sum.inl (Sum.inr (0 : Fin 1))))
    (t₂ := Term.var (Sum.inl (Sum.inl a))) (v := v) (xs := (default : Fin 0 → M))
  simpa [cutGt, Formula.Realize, Term.realize_var] using h

/-- Realization of `cutNe`. -/
theorem cutNe_realize (a : A) (v : A ⊕ Fin 1 → M) :
    (cutNe a).Realize v ↔ v (Sum.inr 0) ≠ v (Sum.inl a) := by
  rw [cutNe, Formula.realize_not, Formula.realize_equal]
  simp [Term.realize_var]

end CutFormulas

section Bounded

variable {L : FirstOrder.Language} {M : Type} [L.Structure M] {α : Type}

/-- `Formula.Realize` is `BoundedFormula.Realize` at the (unique) empty tuple: the presentation in
which `Work.WilC5.IsSaturated` states its types. -/
theorem cutBounded_iff (φ : L.Formula α) (v : α → M) :
    φ.Realize v ↔ @BoundedFormula.Realize L M _ α 0 φ v (fun i : Fin 0 => i.elim0) := by
  unfold Formula.Realize
  exact iff_of_eq (congrArg (fun u : Fin 0 → M => @BoundedFormula.Realize L M _ α 0 φ v u)
    (show (default : Fin 0 → M) = (fun i : Fin 0 => i.elim0) from by
      funext i
      exact i.elim0))

end Bounded

/-! ## 2. The cut is realized in a saturated model -/

theorem realizes_cut {K N : Type}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    [Field N] [LinearOrder N] [IsStrictOrderedRing N] [FirstOrder.Ring.CompatibleRing N]
    [WilkiesDesign.CG.rexpL.Structure N] [(FirstOrder.Language.constantsOn ℝ).Structure N]
    [FirstOrder.Language.Theory.Model N WilkiesDesign.CG.TR]
    (F : WilkiesDesign.CG.LRc.Substructure K) (hF : (F : Type) ⊨ WilkiesDesign.CG.TR)
    (σ : WilkiesDesign.CG.LRc.Embedding F N) (x : K)
    (κ : Cardinal.{0}) (hκ : Cardinal.mk F < κ)
    (hsat : @Work.WilC5.IsSaturated WilkiesDesign.CG.LRc N _ κ) :
    ∃ y : N, (∀ f : F, ((f : K) < x ↔ (σ f : N) < y)) ∧
      (∀ f : F, (x < (f : K) ↔ y < (σ f : N))) := by
  classical
  -- the parameter set: the image of `F` in `N`
  set A : Set N := Set.range (fun f : F => (σ f : N)) with hAdef
  let σA : F → ↥A := fun f => ⟨(σ f : N), Set.mem_range_self f⟩
  have hσA : ∀ f : F, ((σA f : ↥A) : N) = (σ f : N) := fun f => rfl
  have hcardA : Cardinal.mk ↥A < κ := by
    rw [hAdef]
    exact lt_of_le_of_lt Cardinal.mk_range_le hκ
  -- `σ` is order preserving for the order of the ambient model `K`
  have hord : ∀ f g : F, (f : K) ≤ (g : K) → (σ f : N) ≤ (σ g : N) :=
    realizes_cut_order_preserving F hF σ
  -- the type of the cut
  let P : LRc.Formula (↥A ⊕ Fin 1) → Prop := fun φ =>
    ∃ f : F, (φ = cutLt (σA f) ∧ (f : K) ≤ x) ∨ (φ = cutGt (σA f) ∧ x ≤ (f : K)) ∨
      (φ = cutNe (σA f) ∧ (f : K) ≠ x)
  let p : Set (LRc.Formula (↥A ⊕ Fin 1)) := {φ | P φ}
  -- every finite fragment of the type is realized
  have hp_fin : ∀ T : Finset (LRc.Formula (↥A ⊕ Fin 1)), (∀ φ ∈ T, φ ∈ p) →
      ∃ v : Fin 1 → N, ∀ φ ∈ T,
        @BoundedFormula.Realize LRc N _ (↥A ⊕ Fin 1) 0 φ (Sum.elim (Subtype.val : ↥A → N) v)
          (fun i : Fin 0 => i.elim0) := by
    intro T hT
    let wit : (φ : LRc.Formula (↥A ⊕ Fin 1)) → φ ∈ p → F :=
      fun φ h => Classical.choose (show P φ from h)
    have hwit : ∀ (φ : LRc.Formula (↥A ⊕ Fin 1)) (h : φ ∈ p),
        (φ = cutLt (σA (wit φ h)) ∧ (wit φ h : K) ≤ x) ∨
        (φ = cutGt (σA (wit φ h)) ∧ x ≤ (wit φ h : K)) ∨
        (φ = cutNe (σA (wit φ h)) ∧ (wit φ h : K) ≠ x) :=
      fun φ h => Classical.choose_spec (show P φ from h)
    let S : Finset F := T.attach.image (fun b => wit b.1 (hT b.1 b.2))
    obtain ⟨y, hy1, hy2, hy3⟩ :=
      exists_cut_point_finset F (fun f : F => (σ f : N)) x S hord (fun a b h => σ.injective h)
    refine ⟨fun _ => y, fun φ hφ => ?_⟩
    have hmem : wit φ (hT φ hφ) ∈ S :=
      Finset.mem_image.mpr ⟨⟨φ, hφ⟩, Finset.mem_attach T ⟨φ, hφ⟩, rfl⟩
    rcases hwit φ (hT φ hφ) with ⟨h1, h1'⟩ | ⟨h2, h2'⟩ | ⟨h3, h3'⟩
    · rw [h1]
      refine (cutBounded_iff _ _).mp ((cutLt_realize (σA (wit φ (hT φ hφ)))
        (Sum.elim (Subtype.val : ↥A → N) (fun _ : Fin 1 => y))).mpr ?_)
      simpa [hσA] using (leEL_iff_le (M := N) inferInstance (σ (wit φ (hT φ hφ))) y).mpr
        (hy1 (wit φ (hT φ hφ)) hmem h1')
    · rw [h2]
      refine (cutBounded_iff _ _).mp ((cutGt_realize (σA (wit φ (hT φ hφ)))
        (Sum.elim (Subtype.val : ↥A → N) (fun _ : Fin 1 => y))).mpr ?_)
      simpa [hσA] using (leEL_iff_le (M := N) inferInstance y (σ (wit φ (hT φ hφ)))).mpr
        (hy2 (wit φ (hT φ hφ)) hmem h2')
    · rw [h3]
      refine (cutBounded_iff _ _).mp ((cutNe_realize (σA (wit φ (hT φ hφ)))
        (Sum.elim (Subtype.val : ↥A → N) (fun _ : Fin 1 => y))).mpr ?_)
      simpa [hσA] using hy3 (wit φ (hT φ hφ)) hmem h3'
  -- `κ`-saturation realizes the type
  obtain ⟨v, hv⟩ := hsat A hcardA p hp_fin
  -- unfolding the realization of the three families of formulas
  have key : ∀ φ : LRc.Formula (↥A ⊕ Fin 1), φ ∈ p →
      φ.Realize (Sum.elim (Subtype.val : ↥A → N) v) := fun φ h =>
    (cutBounded_iff φ _).mpr (hv φ h)
  have hL : ∀ f : F, (f : K) ≤ x → leEL (σ f : N) (v 0) := fun f hf =>
    (cutLt_realize (σA f) (Sum.elim (Subtype.val : ↥A → N) v)).mp
      (key (cutLt (σA f)) ⟨f, Or.inl ⟨rfl, hf⟩⟩)
  have hG : ∀ f : F, x ≤ (f : K) → leEL (v 0) (σ f : N) := fun f hf =>
    (cutGt_realize (σA f) (Sum.elim (Subtype.val : ↥A → N) v)).mp
      (key (cutGt (σA f)) ⟨f, Or.inr (Or.inl ⟨rfl, hf⟩)⟩)
  have hN : ∀ f : F, (f : K) ≠ x → v 0 ≠ (σ f : N) := fun f hf =>
    (cutNe_realize (σA f) (Sum.elim (Subtype.val : ↥A → N) v)).mp
      (key (cutNe (σA f)) ⟨f, Or.inr (Or.inr ⟨rfl, hf⟩)⟩)
  refine ⟨v 0, ?_, ?_⟩
  · intro f
    refine ⟨fun hfx => ?_, fun hlt => ?_⟩
    · -- `f < x` gives `σ f ≤ y` and `y ≠ σ f`
      exact lt_of_le_of_ne
        ((leEL_iff_le (M := N) inferInstance (σ f : N) (v 0)).mp (hL f (le_of_lt hfx)))
        (Ne.symm (hN f (ne_of_lt hfx)))
    · -- conversely `σ f < y` forces `f < x`
      rcases le_total (f : K) x with hle | hle
      · by_contra hcon
        have hxeq : (f : K) = x := le_antisymm hle (le_of_not_gt hcon)
        have hb := (leEL_iff_le (M := N) inferInstance (v 0) (σ f : N)).mp
          (hG f (le_of_eq hxeq.symm))
        exact absurd hb (not_le.mpr hlt)
      · have hb := (leEL_iff_le (M := N) inferInstance (v 0) (σ f : N)).mp (hG f hle)
        exact absurd hb (not_le.mpr hlt)
  · intro f
    refine ⟨fun hxf => ?_, fun hlt => ?_⟩
    · -- `x < f` gives `y ≤ σ f` and `y ≠ σ f`
      exact lt_of_le_of_ne
        ((leEL_iff_le (M := N) inferInstance (v 0) (σ f : N)).mp (hG f (le_of_lt hxf)))
        (hN f (ne_of_gt hxf))
    · -- conversely `y < σ f` forces `x < f`
      rcases le_total x (f : K) with hle | hle
      · by_contra hcon
        have hxeq : (f : K) = x := le_antisymm (le_of_not_gt hcon) hle
        have hb := (leEL_iff_le (M := N) inferInstance (σ f : N) (v 0)).mp
          (hL f (le_of_eq hxeq))
        exact absurd hb (not_le.mpr hlt)
      · have hb := (leEL_iff_le (M := N) inferInstance (σ f : N) (v 0)).mp (hL f hle)
        exact absurd hb (not_le.mpr hlt)

end Work.WilC5
