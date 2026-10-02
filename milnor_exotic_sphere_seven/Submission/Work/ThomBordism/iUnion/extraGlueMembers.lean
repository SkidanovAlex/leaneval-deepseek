import Mathlib
import Submission.Work.ThomBordism.localThom_iUnion_aux
import Submission.Work.ThomBordism.iUnion.extra
import Submission.Work.ThomBordism.Tower.ConeTheory

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# Gluing the `Extra` term of the mapping cone over a **chain** of open pieces

The `Extra` term `ExtraC Z n W = BaseC W 0 × TotC Z W (n-1)` of the augmented mapping cone of the
cochain-level Thom map `ψ` is a product of two cochain complexes, so compatible families of `Extra`
elements over an increasing family of pieces glue (`Work.ThomBordism.extraGlue` in the `ℕ`-indexed
case) and separate.

The purpose of this file is the version of those statements needed by the union/limit step of
`Work.ThomBordism.localThom_iUnion_of_fibreGenerator`, where the pieces form a **chain** `D` of open
sets (`∀ W W' ∈ D, W ⊆ W' ∨ W' ⊆ W`) indexed not by `ℕ` but by the members of `D` themselves, and
where the union is written as `⋃₀ D`:

* `chainLinearOrder` — the chain hypothesis turns the inclusion relation restricted to `↥D` into a
  `LinearOrder`;
* the gluing/separation lemmas `baseRes_eq_of_forall_lin`, `totRes_eq_of_forall_lin`,
  `extraRes_eq_of_forall_lin`, `coneRes_eq_of_forall_lin`, `extraGlue_lin` for an arbitrary linear
  order (these are the `Work.ThomBordism.*_lin` lemmas of `localThom_iUnion_aux` applied
  componentwise);
* `extraGlue_chain`, `extraRes_sep_chain`, `coneRes_sep_chain` — the same statements with the union
  written as `⋃₀ D` (the index type is `↥D`; the equality `⋃₀ D = ⋃ W : ↥D, ↑W` is
  `Set.sUnion_eq_iUnion`, and the inclusion proofs are abstracted so that they can be transported
  along it);
* `extraGlueMembers` — with a prescribed cone primitive `p` on a larger family `D₀ ⊇ D`, the glued
  `Extra` element `Q` has the prescribed `extraD`-image, by separation over the chain.
-/

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The chain order on the members of a chain of sets -/

/-- **The chain order.**  On the members of a chain `D` of subsets (for the inclusion order),
inclusion is a linear order: totality is exactly the chain hypothesis. -/
@[reducible] def chainLinearOrder (D : Set (Set B))
    (hdchain : ∀ W ∈ D, ∀ W' ∈ D, W ⊆ W' ∨ W' ⊆ W) : LinearOrder ↥D := by
  classical
  letI : DecidableEq ↥D := Classical.decEq _
  letI : Min ↥D := ⟨fun a b => if (a : Set B) ⊆ (b : Set B) then a else b⟩
  letI : Max ↥D := ⟨fun a b => if (a : Set B) ⊆ (b : Set B) then b else a⟩
  letI : DecidableLT ↥D := Classical.decRel _
  letI : Ord ↥D := ⟨fun a b => compareOfLessAndEq a b⟩
  exact LinearOrder.mk
    (toPartialOrder := Subtype.partialOrder (p := fun W : Set B => W ∈ D))
    (le_total := fun a b => by
      rcases hdchain a.1 a.2 b.1 b.2 with h | h
      · exact Or.inl h
      · exact Or.inr h)
    (toDecidableLE := Classical.decRel _) (toDecidableEq := Classical.decEq _)
    (toDecidableLT := Classical.decRel _)
    (min_def := fun _ _ => rfl) (max_def := fun _ _ => rfl)
    (compare_eq_compareOfLessAndEq := fun _ _ => rfl)

/-! ## Separation, for an arbitrary linear order -/

/-- **Separation for the absolute-cochain tower.**  Two absolute cochains over the union of an
increasing family which restrict to the same cochain on every piece are equal. -/
theorem baseRes_eq_of_forall_lin {J : Type} [LinearOrder J] {V : J → Set B}
    (hopen : ∀ j, IsOpen (V j)) (hmono : Monotone V) (k : ℕ)
    {x y : BaseC (⋃ j, V j) k}
    (h : ∀ j, baseRes (Set.subset_iUnion V j) k x = baseRes (Set.subset_iUnion V j) k y) :
    x = y := by
  rw [← sub_eq_zero]
  refine baseRes_sep_lin V hopen hmono k ?_
  intro j
  rw [map_sub, h j, sub_self]

/-- **Separation for the total tower.** -/
theorem totRes_eq_of_forall_lin {J : Type} [LinearOrder J] (Z : RealBundle B F ι)
    {V : J → Set B} (hopen : ∀ j, IsOpen (V j)) (hmono : Monotone V) (k : ℕ)
    {x y : TotC Z (⋃ j, V j) k}
    (h : ∀ j, rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (Set.subset_iUnion V j)) k x
      = rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (Set.subset_iUnion V j)) k y) :
    x = y := by
  rw [← sub_eq_zero]
  refine totRes_sep_lin Z V hopen hmono k ?_
  intro j
  rw [map_sub, h j, sub_self]

/-- **Separation for the `Extra` term.** -/
theorem extraRes_eq_of_forall_lin {J : Type} [LinearOrder J] (Z : RealBundle B F ι) (n : ℕ)
    {V : J → Set B} (hopen : ∀ j, IsOpen (V j)) (hmono : Monotone V)
    {x y : ExtraC Z n (⋃ j, V j)}
    (h : ∀ j, extraRes Z n (Set.subset_iUnion V j) x = extraRes Z n (Set.subset_iUnion V j) y) :
    x = y := by
  refine Prod.ext ?_ ?_
  · refine baseRes_eq_of_forall_lin hopen hmono 0 (fun j => ?_)
    have h1 := congrArg Prod.fst (h j)
    simpa only [extraRes_apply] using h1
  · refine totRes_eq_of_forall_lin Z hopen hmono (n - 1) (fun j => ?_)
    have h1 := congrArg Prod.snd (h j)
    simpa only [extraRes_apply] using h1

/-- **Separation for the cone.** -/
theorem coneRes_eq_of_forall_lin {J : Type} [LinearOrder J] (Z : RealBundle B F ι) (n : ℕ)
    {V : J → Set B} (hopen : ∀ j, IsOpen (V j)) (hmono : Monotone V) (m : ℕ)
    {x y : ConeC Z n (⋃ j, V j) m}
    (h : ∀ j, coneRes Z n (Set.subset_iUnion V j) m x = coneRes Z n (Set.subset_iUnion V j) m y) :
    x = y := by
  refine Prod.ext ?_ ?_
  · refine baseRes_eq_of_forall_lin hopen hmono (m + 1) (fun j => ?_)
    have h1 := congrArg Prod.fst (h j)
    simpa only [coneRes_fst] using h1
  · refine totRes_eq_of_forall_lin Z hopen hmono (m + n) (fun j => ?_)
    have h1 := congrArg Prod.snd (h j)
    simpa only [coneRes_snd] using h1

/-! ## Gluing, for an arbitrary linear order -/

/-- **Gluing of a compatible family of `Extra` elements** over an increasing family of open pieces
indexed by an arbitrary linear order.  This is
`Work.ThomBordism.extraGlue` with `ℕ` replaced by `J`. -/
theorem extraGlue_lin (Z : RealBundle B F ι) (n : ℕ) {J : Type} [LinearOrder J] (W : J → Set B)
    (hopen : ∀ a, IsOpen (W a)) (hmono : Monotone W) (q : (a : J) → ExtraC Z n (W a))
    (hq : ∀ a b (hab : a ≤ b), extraRes Z n (hmono hab) (q b) = q a) :
    ∃! Q : ExtraC Z n (⋃ a, W a), ∀ a, extraRes Z n (Set.subset_iUnion W a) Q = q a := by
  obtain ⟨g, hg, -⟩ := baseGlue_lin W hopen hmono 0 (fun a => (q a).1) (fun a b hab => by
    have h1 := congrArg Prod.fst (hq a b hab)
    simpa only [extraRes_apply] using h1)
  obtain ⟨g', hg', -⟩ := totGlue_lin Z W hopen hmono (n - 1) (fun a => (q a).2)
    (fun a b hab => by
      have h1 := congrArg Prod.snd (hq a b hab)
      simpa only [extraRes_apply] using h1)
  refine ⟨(g, g'), ?_, ?_⟩
  · intro a
    exact Prod.ext (hg a) (hg' a)
  · intro Y hY
    refine Prod.ext ?_ ?_
    · refine baseRes_eq_of_forall_lin hopen hmono 0 (fun a => ?_)
      have h1 := congrArg Prod.fst (hY a)
      simp only [extraRes_apply] at h1
      exact h1.trans (hg a).symm
    · refine totRes_eq_of_forall_lin Z hopen hmono (n - 1) (fun a => ?_)
      have h1 := congrArg Prod.snd (hY a)
      simp only [extraRes_apply] at h1
      exact h1.trans (hg' a).symm

/-! ## The same statements with the union written as `⋃₀ D` -/

/-- **Gluing of a compatible family of `Extra` elements over a chain of open sets.**  The pieces are
the members of `D`; the union is `U`, which the caller identifies with `⋃₀ D`. -/
theorem extraGlue_chain {D : Set (Set B)} (hopen : ∀ W ∈ D, IsOpen W)
    (hdchain : ∀ W ∈ D, ∀ W' ∈ D, W ⊆ W' ∨ W' ⊆ W)
    (Z : RealBundle B F ι) (n : ℕ) (q : (W : ↥D) → ExtraC Z n (W : Set B))
    (hq : ∀ (W W' : ↥D) (h : (W : Set B) ⊆ W'), extraRes Z n h (q W') = q W)
    {U : Set B} (hU : U = ⋃ j : ↥D, ((j : Set B)))
    (hinc : ∀ W : ↥D, (W : Set B) ⊆ U) :
    ∃! Q : ExtraC Z n U, ∀ W : ↥D, extraRes Z n (hinc W) Q = q W := by
  subst hU
  obtain ⟨Q, hQ, huniq⟩ :=
    @extraGlue_lin B _ F _ _ ι Z n ↥D (chainLinearOrder D hdchain)
      (fun j : ↥D => (j : Set B)) (fun j => hopen (j : Set B) j.2)
      (by intro a b hab; exact hab) q (by intro a b hab; exact hq a b hab)
  refine ⟨Q, ?_, ?_⟩
  · intro W
    rw [show hinc W = Set.subset_iUnion (fun j : ↥D => (j : Set B)) W from
      Subsingleton.elim _ _]
    exact hQ W
  · intro Y hY
    refine huniq Y (fun W => ?_)
    have hW := hY W
    rw [show hinc W = Set.subset_iUnion (fun j : ↥D => (j : Set B)) W from
      Subsingleton.elim _ _] at hW
    exact hW

/-- **Separation for the `Extra` term over a chain of open sets.** -/
theorem extraRes_sep_chain {D : Set (Set B)} (hopen : ∀ W ∈ D, IsOpen W)
    (hdchain : ∀ W ∈ D, ∀ W' ∈ D, W ⊆ W' ∨ W' ⊆ W)
    (Z : RealBundle B F ι) (n : ℕ) {U : Set B} (hU : U = ⋃ j : ↥D, ((j : Set B)))
    (hinc : ∀ W : ↥D, (W : Set B) ⊆ U) {x y : ExtraC Z n U}
    (h : ∀ W : ↥D, extraRes Z n (hinc W) x = extraRes Z n (hinc W) y) : x = y := by
  subst hU
  refine @extraRes_eq_of_forall_lin B _ F _ _ ι ↥D (chainLinearOrder D hdchain) Z n
    (fun j : ↥D => (j : Set B)) (fun j => hopen (j : Set B) j.2)
    (by intro a b hab; exact hab) _ _ ?_
  intro W
  have hW := h W
  rw [show hinc W = Set.subset_iUnion (fun j : ↥D => (j : Set B)) W from
    Subsingleton.elim _ _] at hW
  exact hW

/-- **Separation for the cone over a chain of open sets.** -/
theorem coneRes_sep_chain {D : Set (Set B)} (hopen : ∀ W ∈ D, IsOpen W)
    (hdchain : ∀ W ∈ D, ∀ W' ∈ D, W ⊆ W' ∨ W' ⊆ W)
    (Z : RealBundle B F ι) (n : ℕ) (m : ℕ) {U : Set B}
    (hU : U = ⋃ j : ↥D, ((j : Set B))) (hinc : ∀ W : ↥D, (W : Set B) ⊆ U)
    {x y : ConeC Z n U m}
    (h : ∀ W : ↥D, coneRes Z n (hinc W) m x = coneRes Z n (hinc W) m y) : x = y := by
  subst hU
  refine @coneRes_eq_of_forall_lin B _ F _ _ ι ↥D (chainLinearOrder D hdchain) Z n
    (fun j : ↥D => (j : Set B)) (fun j => hopen (j : Set B) j.2)
    (by intro a b hab; exact hab) m _ _ ?_
  intro W
  have hW := h W
  rw [show hinc W = Set.subset_iUnion (fun j : ↥D => (j : Set B)) W from
    Subsingleton.elim _ _] at hW
  exact hW

end

end Work.ThomBordism

namespace Work.ThomBordism.iUnion

/-- **The `Extra` gluing over a chain, with a prescribed cone primitive.**  Given a chain `D` of
members of a family `C` of open sets (through `D₀`), compatible `Extra` elements `q W` on the
members of `D` whose `extraD`-images are the restrictions of a fixed cone-`0` primitive `p` over
`⋃₀ D₀`, there is an `Extra` element `Q` over `⋃₀ D` restricting to `q W` on every `W ∈ D` and whose
`extraD`-image is the restriction of `p`. -/
theorem extraGlueMembers {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ)
    (C : Set (Set B)) (hC : ∀ W ∈ C, IsOpen W) (τ : Work.Thom.PieceCoh Z (⋃₀ C) n)
    (D₀ : Set (Set B)) (hD₀ : D₀ ⊆ C)
    {D : Set (Set B)} (hD : D ⊆ D₀) (hdchain : ∀ W ∈ D, ∀ W' ∈ D, W ⊆ W' ∨ W' ⊆ W)
    (p : Work.ThomBordism.ConeC Z n (⋃₀ D₀) 0)
    (q : (W : ↥D) → Work.ThomBordism.ExtraC Z n (W : Set B))
    (hq : ∀ (W W' : ↥D) (h : (W : Set B) ⊆ W'),
      Work.ThomBordism.extraRes Z n h (q W') = q W)
    (heq : ∀ W : ↥D, Work.ThomBordism.extraD Z n (⋃₀ C) τ (W : Set B)
        (Set.subset_sUnion_of_mem (hD₀ (hD W.2))) (q W)
      = Work.ThomBordism.coneRes Z n (Set.subset_sUnion_of_mem (hD W.2)) 0 p) :
    ∃ Q : Work.ThomBordism.ExtraC Z n (⋃₀ D),
      (∀ W : ↥D, Work.ThomBordism.extraRes Z n (Set.subset_sUnion_of_mem W.2) Q = q W) ∧
      Work.ThomBordism.extraD Z n (⋃₀ C) τ (⋃₀ D) (Set.sUnion_mono (hD.trans hD₀)) Q
        = Work.ThomBordism.coneRes Z n (Set.sUnion_mono hD) 0 p := by
  classical
  -- the members of `D` are open (they belong to `D₀ ⊆ C`)
  have hDopen : ∀ W ∈ D, IsOpen W := fun W hW => hC W (hD₀ (hD hW))
  -- glue the compatible family `q`
  obtain ⟨Q, hQ₀, -⟩ := Work.ThomBordism.extraGlue_chain hDopen hdchain Z n q hq
    (U := ⋃₀ D) Set.sUnion_eq_iUnion (fun W => Set.subset_sUnion_of_mem W.2)
  have hQ : ∀ W : ↥D, Work.ThomBordism.extraRes Z n (Set.subset_sUnion_of_mem W.2) Q = q W :=
    fun W => hQ₀ W
  refine ⟨Q, hQ, ?_⟩
  -- both sides of the `extraD`-equation restrict to the same cone element on every member of `D`
  refine Work.ThomBordism.coneRes_sep_chain hDopen hdchain Z n 0 (U := ⋃₀ D)
    Set.sUnion_eq_iUnion (fun W => Set.subset_sUnion_of_mem W.2) (fun W => ?_)
  calc Work.ThomBordism.coneRes Z n (Set.subset_sUnion_of_mem W.2) 0
        (Work.ThomBordism.extraD Z n (⋃₀ C) τ (⋃₀ D) (Set.sUnion_mono (hD.trans hD₀)) Q)
      = Work.ThomBordism.extraD Z n (⋃₀ C) τ (W : Set B)
          (Set.subset_sUnion_of_mem (hD₀ (hD W.2)))
          (Work.ThomBordism.extraRes Z n (Set.subset_sUnion_of_mem W.2) Q) :=
        Work.ThomBordism.coneRes_extraD Z n (⋃₀ C) τ (Set.subset_sUnion_of_mem W.2)
          (Set.subset_sUnion_of_mem (hD₀ (hD W.2))) (Set.sUnion_mono (hD.trans hD₀)) Q
    _ = Work.ThomBordism.extraD Z n (⋃₀ C) τ (W : Set B)
          (Set.subset_sUnion_of_mem (hD₀ (hD W.2))) (q W) := by rw [hQ W]
    _ = Work.ThomBordism.coneRes Z n (Set.subset_sUnion_of_mem (hD W.2)) 0 p := heq W
    _ = Work.ThomBordism.coneRes Z n (Set.subset_sUnion_of_mem W.2) 0
          (Work.ThomBordism.coneRes Z n (Set.sUnion_mono hD) 0 p) := by
        rw [Work.ThomBordism.coneRes_comp Z n (Set.subset_sUnion_of_mem W.2)
          (Set.sUnion_mono hD) 0 p]

end Work.ThomBordism.iUnion
