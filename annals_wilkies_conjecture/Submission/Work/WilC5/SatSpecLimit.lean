/-
  WilC5 — the *limit step* of the transfinite saturation construction.

  `SatSpecLimit` is the second half of the successor/limit case distinction of the main
  induction `SatMain`: at a level `x` which is not the successor of any element (`x` is the
  least element or a limit ordinal of the well-order `SatIdx κ`), every *finite* set of
  sentences of the specification `SatSpecG x` is satisfiable.

  The proof has two halves.

  * If `x` has a predecessor (`∃ y, y < x`), then every sentence of `SatSpecG x` is, above a
    certain threshold `< x`, the image of a sentence of `SatSpecG y` under the constant
    inclusion `SatC y → SatC x` (`exists_pullbackThreshold`).  Since only finitely many
    sentences are involved, all the thresholds can be met by a single level `Y < x`; the
    inductive hypothesis `hIH` at `Y` then says that `SatMod3 Y` realises the pull-backs, and
    the expansion `SatExpansion (SatInc : C Y → C x)` realises the sentences of `T0`
    (`isSatisfiable_of_pullback`).
  * If `x` is the least element of `SatIdx κ`, then `SatSpecG x` consists only of the images
    of the elementary diagram of `M`, and `M` itself (with its constants interpreted by the
    identity) provides a model (`isSatisfiable_of_diagramOnly`).
-/
import Mathlib
import Submission.Work.WilC5.SatSetup
import Submission.Work.WilC5.SatBuild
import Submission.Work.WilC5.SatCore
import Submission.Work.WilC5.SatExpand
import Submission.Work.WilC5.SatExpansionModel
import Submission.Work.WilC5.SatSentRealize

open FirstOrder Language
open scoped FirstOrder

-- `SatLang L C` is `L[[C]]` and `SatC L M κ x` is a `Σ`-type; both are defined by `def`s, so the
-- tactic machinery refuses to unfold them when elaborating implicit arguments.  Marking them
-- implicit-reducible for the duration of this file makes the library lemmas applicable; this is a
-- purely syntactic device and does not change any statement.
attribute [local implicit_reducible] FirstOrder.Language.withConstants Work.WilC5.SatC

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilC5

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [instM : L.Structure M] {κ : Cardinal.{0}}

/-! ## Functoriality of `SatLangMap` -/

/-- `SatLangMap` is functorial in the map on the constant sets. -/
theorem SatLangMap_comp {C C' C'' : Type} (f : C → C') (g : C' → C'') :
    SatLangMap (L := L) (g ∘ f) = (SatLangMap (L := L) g).comp (SatLangMap (L := L) f) := by
  unfold SatLangMap
  apply LHom.funext
  · funext n F
    cases F with
    | inl a => rfl
    | inr b =>
      simp only [LHom.sumMap_onFunction, LHom.comp]
      cases n with
      | zero => rfl
      | succ k => exact isEmptyElim b
  · funext n R
    cases R with
    | inl a => rfl
    | inr b => exact isEmptyElim b

/-- Applying two `SatLangMap`s one after the other is applying the composite map. -/
theorem SatLangMap_comp_onSentence {C C' C'' : Type} (f : C → C') (g : C' → C'')
    (τ : (SatLang L C).Sentence) :
    (SatLangMap (L := L) g).onSentence ((SatLangMap (L := L) f).onSentence τ) =
      (SatLangMap (L := L) (g ∘ f)).onSentence τ := by
  rw [SatLangMap_comp]
  exact (congrFun (@LHom.comp_onBoundedFormula (SatLang L C) (SatLang L C') Empty 0
    (SatLang L C'') (SatLangMap (L := L) g) (SatLangMap (L := L) f)) τ).symm

/-- Applying two inclusions of the constant sets one after the other is applying the composite
inclusion (using `SatInc_comp`). -/
theorem SatInc_onSentence_comp {u v w : SatIdx κ} (huv : u ≤ v) (hvw : v ≤ w)
    (τ : (SatLang L (SatC L M κ u)).Sentence) :
    (SatLangMap (L := L) (SatInc L M κ hvw)).onSentence
        ((SatLangMap (L := L) (SatInc L M κ huv)).onSentence τ) =
      (SatLangMap (L := L) (SatInc L M κ (le_trans huv hvw))).onSentence τ := by
  rw [SatLangMap_comp_onSentence]
  exact congrArg (fun h => (SatLangMap (L := L) h).onSentence τ) (SatInc_comp L M κ huv hvw)

/-! ## Expansion of a model of a lower level -/

/-- If `N` realises a sentence `τ` of `L[[C]]`, then the expansion of `N` to `L[[C']]` along an
injective map `inc : C → C'` (with arbitrary values on the new constants) realises the image
`(SatLangMap inc).onSentence τ` of `τ`. -/
theorem SatExpansion_realize_onSentence {C C' : Type} (inc : C → C')
    (hinc : Function.Injective inc) (N : Type) (instN : (SatLang L C).Structure N) (w : C' → N)
    (τ : (SatLang L C).Sentence)
    (hτ : @Sentence.Realize (SatLang L C) N instN τ) :
    @Sentence.Realize (SatLang L C') N (@SatExpansion L C C' inc hinc N instN w)
      ((SatLangMap (L := L) inc).onSentence τ) :=
  (@LHom.realize_onSentence (SatLang L C) (SatLang L C') N instN
    (@SatExpansion L C C' inc hinc N instN w) (SatLangMap inc)
    (SatExpansion_isExpansionOn inc hinc N instN w) τ).2 hτ

/-! ## The finite satisfiability lemma -/

/-- If every sentence of the finite set `T0` (a set of sentences of level `x`) is the image of a
sentence of `SatSpecG y` under the inclusion `SatC y → SatC x` (`y < x`), and the structure at
level `y` realises `SatSpecG y`, then `T0` is satisfiable. -/
theorem isSatisfiable_of_pullback {x y : SatIdx κ} (hy : y < x)
    (hne : Nonempty (SatMod3 L M κ y))
    (hIH : ∀ (σ : (SatLang L (SatC L M κ y)).Sentence), σ ∈ SatSpecG L M κ y →
      @Sentence.Realize (SatLang L (SatC L M κ y)) (SatMod3 L M κ y) (SatStruc3 L M κ y) σ)
    (T0 : Finset ((SatLang L (SatC L M κ x)).Sentence))
    (hT0 : ∀ σ ∈ T0, σ ∈ (SatLangMap (L := L) (SatInc L M κ (le_of_lt hy))).onTheory
      (SatSpecG L M κ y)) :
    @Theory.IsSatisfiable (SatLang L (SatC L M κ x)) (↑T0) := by
  obtain ⟨a⟩ := hne
  let w : SatC L M κ x → SatMod3 L M κ y := fun _ => a
  letI : (SatLang L (SatC L M κ x)).Structure (SatMod3 L M κ y) :=
    @SatExpansion L (SatC L M κ y) (SatC L M κ x) (SatInc L M κ (le_of_lt hy))
      (SatInc_injective L M κ (le_of_lt hy)) (SatMod3 L M κ y) (SatStruc3 L M κ y) w
  haveI : Nonempty (SatMod3 L M κ y) := ⟨a⟩
  haveI hmodel : @Theory.Model (SatLang L (SatC L M κ x)) (SatMod3 L M κ y) inferInstance (↑T0) := by
    rw [Theory.model_iff]
    intro σ hσ
    obtain ⟨τ, hτ, rfl⟩ := LHom.mem_onTheory.mp (hT0 σ (Finset.mem_coe.mp hσ))
    exact SatExpansion_realize_onSentence (L := L) (SatInc L M κ (le_of_lt hy))
      (SatInc_injective L M κ (le_of_lt hy)) (SatMod3 L M κ y) (SatStruc3 L M κ y) w τ
      (hIH τ hτ)
  exact Theory.Model.isSatisfiable (SatMod3 L M κ y)

/-! ## Thresholds -/

/-- The image of a sentence `τ` of `L[[M]]` at level `y` (the constants of `M` are read through
`Sum.inl : M → SatC L M κ y`).  Writing this as a definition (rather than inline) pins down the
syntactic form of the language, which the elaboration of `SatLangMap` would otherwise unfold. -/
def diagramSent (y : SatIdx κ) (τ : (L[[M]]).Sentence) : (SatLang L (SatC L M κ y)).Sentence :=
  (SatLangMap (L := L) (Sum.inl : M → SatC L M κ y)).onSentence τ

/-- Every sentence of `SatSpecG x`, when `x` has a predecessor, is above a threshold `r < x` the
image of a sentence of `SatSpecG y` under `SatInc : C y → C x`, for every `y` with `r ≤ y < x`. -/
theorem exists_pullbackThreshold {x : SatIdx κ} (hx : ∃ y : SatIdx κ, y < x)
    (hsucc : ∀ u : SatIdx κ, x ≠ Order.succ u)
    {σ : (SatLang L (SatC L M κ x)).Sentence} (hσ : σ ∈ SatSpecG L M κ x) :
    ∃ r : SatIdx κ, r < x ∧
      ∀ (y : SatIdx κ), r ≤ y → (h : y < x) →
        σ ∈ (SatLangMap (L := L) (SatInc L M κ (le_of_lt h))).onTheory (SatSpecG L M κ y) := by
  rcases (mem_SatSpecG (L := L) (M := M) (κ := κ)).mp hσ with hA | hBC
  · -- image of the elementary diagram of `M`
    obtain ⟨τ, hτ, heq⟩ := hA
    refine ⟨hx.choose, hx.choose_spec, fun y _ hyx => ?_⟩
    refine LHom.mem_onTheory.mpr
      ⟨diagramSent (L := L) (M := M) (κ := κ) y τ, ?_, ?_⟩
    · refine (mem_SatSpecG (L := L) (M := M) (κ := κ)).mpr (Or.inl ⟨τ, hτ, ?_⟩)
      rfl
    · rw [diagramSent, SatLangMap_comp_onSentence]
      rw [show (SatInc L M κ (le_of_lt hyx)) ∘ (Sum.inl : M → SatC L M κ y) =
          (Sum.inl : M → SatC L M κ x) from
        funext fun m => SatInc_inl L M κ (le_of_lt hyx) m]
      exact heq
  · rcases hBC with hB | hC
    · -- image of the theory of a lower level
      obtain ⟨y', hy', τ, hτ, heq⟩ := hB
      refine ⟨Order.succ y', ?_, fun y hle hyx => ?_⟩
      · exact lt_of_le_of_ne (Order.succ_le_iff.mpr hy') (Ne.symm (hsucc y'))
      · have hy'y : y' < y := lt_of_lt_of_le (Order.lt_succ_of_le le_rfl) hle
        refine LHom.mem_onTheory.mpr
          ⟨(SatLangMap (L := L) (SatInc L M κ (le_of_lt hy'y))).onSentence τ, ?_, ?_⟩
        · rw [mem_SatSpecG]
          exact Or.inr (Or.inl ⟨y', hy'y, τ, hτ, rfl⟩)
        · rw [SatInc_onSentence_comp (le_of_lt hy'y) (le_of_lt hyx)]
          rw [SatInc_proof_irrel L M κ (le_trans (le_of_lt hy'y) (le_of_lt hyx)) (le_of_lt hy')]
          exact heq
    · -- a witness sentence created at a lower level
      obtain ⟨p, hp, q, hq, φ, hφ, heq⟩ := hC
      refine ⟨Order.succ p, ?_, fun y hle hyx => ?_⟩
      · exact lt_of_le_of_ne (Order.succ_le_iff.mpr hp) (Ne.symm (hsucc p))
      · have hp'y : p < y := lt_of_lt_of_le (Order.lt_succ_of_le le_rfl) hle
        refine LHom.mem_onTheory.mpr
          ⟨(SatLangMap (L := L) (SatInc L M κ hle)).onSentence
            (SatWitSent2 (SatIncSucc L M κ p) (SatNewConst L M κ p) q φ), ?_, ?_⟩
        · rw [mem_SatSpecG]
          refine Or.inr (Or.inr ⟨p, hp'y, q, hq, φ, hφ, ?_⟩)
          rw [SatInc_proof_irrel L M κ (Order.succ_le_of_lt hp'y) hle]
        · rw [SatInc_onSentence_comp hle (le_of_lt hyx)]
          rw [SatInc_proof_irrel L M κ (le_trans hle (le_of_lt hyx)) (Order.succ_le_of_lt hp)]
          exact heq

/-! ## The least element case -/

/-- If `x` is the least element of `SatIdx κ`, then `SatSpecG x` is the image of the elementary
diagram of `M`; a finite subset of it is realised by `M` (with the constants interpreted by the
identity), expanded to the language of level `x`. -/
theorem isSatisfiable_of_diagramOnly {x : SatIdx κ}
    (hleast : ∀ y : SatIdx κ, x ≤ y) (hM : Nonempty M)
    (T0 : Finset ((SatLang L (SatC L M κ x)).Sentence))
    (hT0 : ∀ σ ∈ T0, σ ∈ SatSpecG L M κ x) :
    @Theory.IsSatisfiable (SatLang L (SatC L M κ x)) (↑T0) := by
  obtain ⟨m⟩ := hM
  have hnot : ¬ ∃ y : SatIdx κ, y < x := fun ⟨y, hy⟩ => not_lt_of_ge (hleast y) hy
  let w : SatC L M κ x → M := fun c => match c with
    | Sum.inl a => a
    | Sum.inr p => (not_lt_of_ge (hleast p.1.1) p.1.2).elim
  letI instMM : (FirstOrder.Language.withConstants L M).Structure M := inferInstance
  letI : (SatLang L (SatC L M κ x)).Structure M :=
    @SatExpansion L M (SatC L M κ x) (Sum.inl) Sum.inl_injective M instMM w
  haveI : Nonempty M := ⟨m⟩
  haveI hmodel : @Theory.Model (SatLang L (SatC L M κ x)) M inferInstance (↑T0) := by
    rw [Theory.model_iff]
    intro σ hσ
    have hσG : σ ∈ SatSpecG L M κ x := hT0 σ (Finset.mem_coe.mp hσ)
    have hA : ∃ τ ∈ L.elementaryDiagram M,
        (SatLangMap (L := L) (Sum.inl : M → SatC L M κ x)).onSentence τ = σ :=
      (mem_SatSpecG (L := L) (M := M) (κ := κ)).mp hσG |>.resolve_right fun hbc => hbc.elim
        (fun hb => hnot ⟨hb.choose, hb.choose_spec.choose⟩)
        (fun hc => hnot ⟨hc.choose, hc.choose_spec.choose⟩)
    obtain ⟨τ, hτ, heq⟩ := hA
    rw [← heq]
    have hdiag : @Theory.Model (FirstOrder.Language.withConstants L M) M instMM
        (L.elementaryDiagram M) := inferInstance
    exact SatExpansion_realize_onSentence (L := L) (Sum.inl) Sum.inl_injective M instMM w τ
      (hdiag.realize_of_mem τ hτ)
  exact Theory.Model.isSatisfiable M

/-! ## The limit step -/

theorem SatSpecLimit {L : FirstOrder.Language.{0, 0}} {M : Type} [instM : L.Structure M]
    {κ : Cardinal.{0}} {x : SatIdx κ} (hM : Nonempty M)
    (hsucc : ∀ u : SatIdx κ, x ≠ Order.succ u)
    (hne : ∀ y : SatIdx κ, y < x → Nonempty (SatMod3 L M κ y))
    (hIH : ∀ (y : SatIdx κ) (hy : y < x) (σ : (SatLang L (SatC L M κ y)).Sentence),
      σ ∈ SatSpecG L M κ y →
      @FirstOrder.Language.Sentence.Realize (SatLang L (SatC L M κ y)) (SatMod3 L M κ y)
        (SatStruc3 L M κ y) σ)
    (T0 : Finset ((SatLang L (SatC L M κ x)).Sentence))
    (hT0 : ∀ σ ∈ T0, σ ∈ SatSpecG L M κ x) :
    @FirstOrder.Language.Theory.IsSatisfiable (SatLang L (SatC L M κ x)) (↑T0) := by
  by_cases hx : ∃ y : SatIdx κ, y < x
  · obtain ⟨y₀, hy₀⟩ := hx
    by_cases hT0n : T0.Nonempty
    · -- all thresholds can be met by a single level `Y < x`
      let r : {σ : (SatLang L (SatC L M κ x)).Sentence // σ ∈ T0} → SatIdx κ :=
        fun s => Classical.choose
          (exists_pullbackThreshold (L := L) (M := M) (κ := κ) ⟨y₀, hy₀⟩ hsucc (hT0 s.1 s.2))
      have hr : ∀ s : {σ : (SatLang L (SatC L M κ x)).Sentence // σ ∈ T0},
          r s < x ∧ ∀ (y : SatIdx κ), r s ≤ y → (h : y < x) →
            s.1 ∈ (SatLangMap (L := L) (SatInc L M κ (le_of_lt h))).onTheory (SatSpecG L M κ y) :=
        fun s => Classical.choose_spec
          (exists_pullbackThreshold (L := L) (M := M) (κ := κ) ⟨y₀, hy₀⟩ hsucc (hT0 s.1 s.2))
      let S : Finset (SatIdx κ) := T0.attach.image r
      have hSn : S.Nonempty := hT0n.attach.image r
      let Y : SatIdx κ := S.max' hSn
      have hYmem : Y ∈ S := Finset.max'_mem S hSn
      have hYx : Y < x := by
        rw [Finset.mem_image] at hYmem
        obtain ⟨s, -, hs⟩ := hYmem
        rw [← hs]
        exact (hr s).1
      refine isSatisfiable_of_pullback (L := L) (M := M) (κ := κ) hYx (hne Y hYx) (hIH Y hYx)
        T0 ?_
      intro σ hσ
      have hmem : r ⟨σ, hσ⟩ ∈ S := Finset.mem_image.mpr
        ⟨⟨σ, hσ⟩, Finset.mem_attach T0 ⟨σ, hσ⟩, rfl⟩
      have hmax : r ⟨σ, hσ⟩ ≤ S.max' ⟨r ⟨σ, hσ⟩, hmem⟩ :=
        Finset.le_max' S (r ⟨σ, hσ⟩) hmem
      have hYeq : S.max' ⟨r ⟨σ, hσ⟩, hmem⟩ = S.max' hSn :=
        congrArg S.max' (Subsingleton.elim _ _)
      rw [hYeq] at hmax
      exact (hr ⟨σ, hσ⟩).2 Y hmax hYx
    · -- `T0` is empty: any level below `x` works
      refine isSatisfiable_of_pullback (L := L) (M := M) (κ := κ) hy₀ (hne y₀ hy₀) (hIH y₀ hy₀)
        T0 ?_
      intro σ hσ
      have hT0e : T0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT0n
      rw [hT0e] at hσ
      exact absurd hσ (Finset.notMem_empty σ)
  · push_neg at hx
    exact isSatisfiable_of_diagramOnly (L := L) (M := M) (κ := κ) hx hM T0 hT0

end Work.WilC5
