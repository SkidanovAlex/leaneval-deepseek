import Mathlib
import Submission.Szemeredi.Removal.GoodAtomsMain
import Submission.Commons.Data.Fintype.sum_pi_split
import Submission.Commons.Data.Fintype.sum_pi_restrict
import Submission.Commons.Data.Fintype.card_pt_mul
import Submission.Commons.Data.Finset.prod_ite_one_mem

/-!
# Hypergraph bundles (Tao, arXiv:math/0503572, §4): the transport layer

A *bundle* over the hypergraph system `(ι, V)` is an index type `κ` together with a
projection `π : κ → ι` which is injective on every edge of the bundle.  The point
space of the bundle is `BPt V π = ∏_{k : κ} V (π k)`.  A set `A ⊆ Pt V` lifts to
the bundle (`liftSet`), and the average of its indicator is unchanged: this is the
key transport fact that lets the counting lemma be applied inside bundles.
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]

/-- The point space of a bundle: index type `κ`, projection `π : κ → ι`. -/
abbrev BPt {κ : Type*} (V : ι → Type*) (π : κ → ι) : Type _ := (k : κ) → V (π k)

/-- The average is invariant under a bijection of the underlying type. -/
theorem avg_equiv' {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    avg (fun a : α => f (e a)) = avg f := by
  unfold avg
  rw [Equiv.sum_comp e f, Fintype.card_congr e]

/-- The average of a function of the restriction to `e` is the average over `Pd V e`. -/
theorem avg_restrict_eq (e : Finset ι) (f : Pd (V := V) e → ℝ) :
    avg (fun x : Pt V => f (restrict x e)) = avg f := by
  have key : (fun x : Pt V => f (restrict x e)) = fun x : Pt V => f (fun i => x i.val) := rfl
  rw [key]
  unfold avg
  rw [Commons.Data.Fintype.sum_pi_restrict (W := V) e f]
  have hcard : (Fintype.card (Pt V) : ℝ)
      = ((Fintype.card ((i : {i // i ∉ e}) → V i.val) : ℕ) : ℝ)
        * ((Fintype.card (Pd (V := V) e) : ℕ) : ℝ) := by
    have h := Commons.Data.Fintype.card_pt_mul (V := V) e
    rw [h, mul_comm]
    push_cast
    ring
  rw [hcard]
  have hN : ((Fintype.card ((i : {i // i ∉ e}) → V i.val) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ((i : {i // i ∉ e}) → V i.val) ≠ 0)
  have hD : ((Fintype.card (Pd (V := V) e) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Pd (V := V) e) ≠ 0)
  rw [mul_div_mul_left _ _ hN]

/-- The projection `{k // k ∈ g} → {j // j ∈ g.image π}` induced by `π`. -/
noncomputable def imageEquiv {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) :
    {k // k ∈ g} ≃ {j // j ∈ g.image π} := by
  classical
  refine Equiv.ofBijective (fun k => ⟨π k.val, Finset.mem_image.mpr ⟨k.val, k.2, rfl⟩⟩) ⟨?_, ?_⟩
  · intro k₁ k₂ h
    have h' : π k₁.val = π k₂.val := congrArg Subtype.val h
    exact Subtype.ext (hinj k₁.val k₁.2 k₂.val k₂.2 h')
  · intro j
    obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp j.2
    refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
    show π k = j.1
    exact hkj

/-- `Pd (V ∘ π) g` identifies with `Pd V (g.image π)` when `π` is injective on `g`. -/
noncomputable def piCongrImage {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) :
    Pd (V := fun k => V (π k)) g ≃ Pd (V := V) (g.image π) :=
  Equiv.piCongrLeft (fun j : {j // j ∈ g.image π} => V j.1)
    (imageEquiv π g hinj)

/-- The `Pd`-level lift of `A ⊆ Pt V` to the bundle. -/
noncomputable def liftPd {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (A : Finset (Pt V)) :
    Finset (Pd (V := fun k => V (π k)) g) :=
  (shadow (V := V) (g.image π) A).preimage (piCongrImage (V := V) π g hinj)
    (fun a _ b _ h => (piCongrImage (V := V) π g hinj).injective h)

/-- The lift of `A ⊆ Pt V` to the bundle: points whose `g`-restriction (in `π`
coordinates) lies in the shadow of `A`. -/
noncomputable def liftSet {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (A : Finset (Pt V)) :
    Finset (BPt V π) :=
  Finset.univ.filter (fun v => restrict (V := fun k => V (π k)) v g ∈ liftPd (V := V) π g hinj A)

theorem mem_liftSet {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {g : Finset κ}
    {hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b} {A : Finset (Pt V)} {v : BPt V π} :
    v ∈ liftSet (V := V) π g hinj A ↔ restrict (V := fun k => V (π k)) v g ∈ liftPd (V := V) π g hinj A := by
  classical
  simp only [liftSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem liftSet_isMeas {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (A : Finset (Pt V)) :
    (coord (V := fun k => V (π k)) g).IsMeas (liftSet (V := V) π g hinj A) := by
  classical
  rw [coord_isMeas_iff]
  intro x y hxy
  rw [mem_liftSet, mem_liftSet]
  have h1 : restrict (V := fun k => V (π k)) y g = restrict (V := fun k => V (π k)) x g := by
    funext i
    exact hxy i.val i.2
  rw [h1]

theorem liftSet_mono {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) {A B : Finset (Pt V)} (h : A ⊆ B) :
    liftSet (V := V) π g hinj A ⊆ liftSet (V := V) π g hinj B := by
  intro v hv
  rw [mem_liftSet] at hv ⊢
  exact Finset.mem_preimage.mpr (shadow_mono (V := V) (e := g.image π) h (Finset.mem_preimage.mp hv))

/-- **Transport**: the average of the indicator of a lifted set equals the average of
the indicator of the original set. -/
theorem liftSet_avg {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) {A : Finset (Pt V)}
    (hA : (coord (V := V) (g.image π)).IsMeas A) :
    avg (fun v : BPt V π => indicator (liftSet (V := V) π g hinj A) v)
      = avg (fun x : Pt V => indicator A x) := by
  classical
  have hfun : (fun v : BPt V π => indicator (liftSet (V := V) π g hinj A) v)
      = fun v => (fun w : Pd (V := fun k => V (π k)) g =>
            indicator (liftPd (V := V) π g hinj A) w)
          (restrict (V := fun k => V (π k)) v g) := by
    funext v
    simp only [indicator]
    by_cases h : v ∈ liftSet (V := V) π g hinj A
    · rw [if_pos h, if_pos (mem_liftSet.mp h)]
    · rw [if_neg h, if_neg (fun hh => h (mem_liftSet.mpr hh))]
  rw [hfun, avg_restrict_eq (V := fun k => V (π k)) g]
  have step : avg (fun w : Pd (V := fun k => V (π k)) g =>
        indicator (liftPd (V := V) π g hinj A) w)
      = avg (fun w' : Pd (V := V) (g.image π) =>
        indicator (shadow (V := V) (g.image π) A) w') := by
    have eqn : (fun w : Pd (V := fun k => V (π k)) g =>
          indicator (liftPd (V := V) π g hinj A) w)
        = fun w => (fun w' : Pd (V := V) (g.image π) =>
              indicator (shadow (V := V) (g.image π) A) w')
            (piCongrImage (V := V) π g hinj w) := by
      funext w
      simp only [indicator]
      by_cases h : w ∈ liftPd (V := V) π g hinj A
      · rw [if_pos h, if_pos (Finset.mem_preimage.mp h)]
      · rw [if_neg h, if_neg (fun hh => h (Finset.mem_preimage.mpr hh))]
    rw [eqn, avg_equiv']
  exact step.trans (avg_indicator_shadow (V := V) hA).symm


/-- Lifting of a function `φ : Pd V (g.image π) → ℝ` to the bundle. -/
noncomputable abbrev liftFun {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (φ : Pd (V := V) (g.image π) → ℝ) :
    BPt V π → ℝ :=
  fun v => φ (piCongrImage (V := V) π g hinj (restrict (V := fun k => V (π k)) v g))

theorem liftFun_apply {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (φ : Pd (V := V) (g.image π) → ℝ)
    (v : BPt V π) :
    liftFun (V := V) π g hinj φ v
      = φ (piCongrImage (V := V) π g hinj (restrict (V := fun k => V (π k)) v g)) := rfl

/-- The indicator of `liftPd` is the indicator of the shadow, transported. -/
theorem indicator_liftPd {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (A : Finset (Pt V))
    (w : Pd (V := fun k => V (π k)) g) :
    indicator (liftPd (V := V) π g hinj A) w
      = indicator (shadow (V := V) (g.image π) A) (piCongrImage (V := V) π g hinj w) := by
  by_cases h : w ∈ liftPd (V := V) π g hinj A
  · rw [show indicator (liftPd (V := V) π g hinj A) w = (1 : ℝ) from by
        rw [indicator, if_pos h],
      show indicator (shadow (V := V) (g.image π) A) (piCongrImage (V := V) π g hinj w)
          = (1 : ℝ) from by rw [indicator, if_pos (Finset.mem_preimage.mp h)]]
  · rw [show indicator (liftPd (V := V) π g hinj A) w = (0 : ℝ) from by
        rw [indicator, if_neg h],
      show indicator (shadow (V := V) (g.image π) A) (piCongrImage (V := V) π g hinj w)
          = (0 : ℝ) from by
        rw [indicator, if_neg (fun hh => h (Finset.mem_preimage.mpr hh))]]

/-- The indicator of `liftSet` is the indicator of `liftPd` at the restriction. -/
theorem indicator_liftSet {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (A : Finset (Pt V)) (v : BPt V π) :
    indicator (liftSet (V := V) π g hinj A) v
      = indicator (liftPd (V := V) π g hinj A) (restrict (V := fun k => V (π k)) v g) := by
  by_cases h : v ∈ liftSet (V := V) π g hinj A
  · rw [show indicator (liftSet (V := V) π g hinj A) v = (1 : ℝ) from by
        rw [indicator, if_pos h],
      show indicator (liftPd (V := V) π g hinj A)
          (restrict (V := fun k => V (π k)) v g) = (1 : ℝ) from by
        rw [indicator, if_pos (mem_liftSet.mp h)]]
  · rw [show indicator (liftSet (V := V) π g hinj A) v = (0 : ℝ) from by
        rw [indicator, if_neg h],
      show indicator (liftPd (V := V) π g hinj A)
          (restrict (V := fun k => V (π k)) v g) = (0 : ℝ) from by
        rw [indicator, if_neg (fun hh => h (mem_liftSet.mpr hh))]]

/-- **Transport of a product**: averages of `liftFun φ · 1_{liftSet A}` equal the
corresponding averages on `Pt V`. -/
theorem lift_avg {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b)
    (φ : Pd (V := V) (g.image π) → ℝ) {A : Finset (Pt V)}
    (hA : (coord (V := V) (g.image π)).IsMeas A) :
    avg (fun v : BPt V π => liftFun (V := V) π g hinj φ v
        * indicator (liftSet (V := V) π g hinj A) v)
      = avg (fun x : Pt V => φ (restrict (V := V) x (g.image π)) * indicator A x) := by
  classical
  have h1 : avg (fun v : BPt V π => liftFun (V := V) π g hinj φ v
        * indicator (liftSet (V := V) π g hinj A) v)
      = avg (fun w : Pd (V := fun k => V (π k)) g =>
          φ (piCongrImage (V := V) π g hinj w) * indicator (liftPd (V := V) π g hinj A) w) := by
    refine (?_ : avg (fun v : BPt V π => liftFun (V := V) π g hinj φ v
        * indicator (liftSet (V := V) π g hinj A) v)
        = avg (fun v => (fun w : Pd (V := fun k => V (π k)) g =>
            φ (piCongrImage (V := V) π g hinj w)
              * indicator (liftPd (V := V) π g hinj A) w)
            (restrict (V := fun k => V (π k)) v g))).trans
      (avg_restrict_eq (V := fun k => V (π k)) g
        (fun w => φ (piCongrImage (V := V) π g hinj w)
          * indicator (liftPd (V := V) π g hinj A) w))
    congr 1
    funext v
    rw [liftFun_apply, indicator_liftSet]
  rw [h1]
  have h2 : (fun w : Pd (V := fun k => V (π k)) g =>
        φ (piCongrImage (V := V) π g hinj w) * indicator (liftPd (V := V) π g hinj A) w)
      = fun w => (fun w' : Pd (V := V) (g.image π) =>
            φ w' * indicator (shadow (V := V) (g.image π) A) w')
          (piCongrImage (V := V) π g hinj w) := by
    funext w
    rw [indicator_liftPd]
  rw [h2, avg_equiv' (piCongrImage (V := V) π g hinj)
    (fun w' : Pd (V := V) (g.image π) =>
      φ w' * indicator (shadow (V := V) (g.image π) A) w')]
  rw [← avg_restrict_eq (V := V) (g.image π)
    (fun w => φ w * indicator (shadow (V := V) (g.image π) A) w)]
  congr 1
  funext x
  rw [indicator_shadow (V := V) hA x]


/-- A function depending only on the coordinates in `e` factors through the restriction. -/
theorem exists_factor_coord (e : Finset ι) (φ : Pt V → ℝ)
    (h : ∀ x y : Pt V, (∀ i ∈ e, x i = y i) → φ x = φ y) :
    ∃ ψ : Pd (V := V) e → ℝ, ∀ x : Pt V, φ x = ψ (restrict x e) := by
  classical
  refine ⟨fun w => φ (fun i => if hi : i ∈ e then w ⟨i, hi⟩ else Classical.arbitrary (V i)), ?_⟩
  intro x
  refine (h (fun i => if hi : i ∈ e then (restrict x e) ⟨i, hi⟩ else Classical.arbitrary (V i)) x ?_).symm
  intro i hi
  rw [dif_pos hi]
  rfl

/-- The intersection of a family of sets over the proper subsets of `e`. -/
noncomputable def interProper (A : Finset ι → Finset (Pt V)) (e : Finset ι) : Finset (Pt V) :=
  Finset.univ.filter (fun x => ∀ f ∈ e.powerset, f ⊂ e → x ∈ A f)

theorem mem_interProper {A : Finset ι → Finset (Pt V)} {e : Finset ι} {x : Pt V} :
    x ∈ interProper A e ↔ ∀ f ∈ e.powerset, f ⊂ e → x ∈ A f := by
  classical
  simp only [interProper, Finset.mem_filter, Finset.mem_univ, true_and]

theorem interProper_isMeas {A : Finset ι → Finset (Pt V)} {e : Finset ι}
    (hA : ∀ f, f ⊂ e → (coord (V := V) f).IsMeas (A f)) :
    (coord (V := V) e).IsMeas (interProper A e) := by
  classical
  rw [coord_isMeas_iff]
  intro x y hxy
  rw [mem_interProper, mem_interProper]
  have key : ∀ f, f ⊂ e → ∀ i ∈ f, y i = x i := by
    intro f hf i hi
    exact hxy i (Finset.mem_of_subset hf.1 hi)
  constructor
  · intro h f hf hfe
    exact ((coord_isMeas_iff.mp (hA f hfe)) x y (key f hfe)).mp (h f hf hfe)
  · intro h f hf hfe
    exact ((coord_isMeas_iff.mp (hA f hfe)) x y (key f hfe)).mpr (h f hf hfe)

/-- The "lower" set of a bundle edge: the lift of `⋂_{f ⊂ π''g} A f`. -/
noncomputable def lowSetLift {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (A : Finset ι → Finset (Pt V)) :
    Finset (BPt V π) :=
  liftSet (V := V) π g hinj (interProper A (g.image π))

theorem lowSet_isMeas {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) {A : Finset ι → Finset (Pt V)}
    (hA : ∀ f, f ⊂ g.image π → (coord (V := V) f).IsMeas (A f)) :
    (coord (V := fun k => V (π k)) g).IsMeas (lowSetLift (V := V) π g hinj A) :=
  liftSet_isMeas (V := V) π g hinj _


@[simp] theorem imageEquiv_apply_val {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    (g : Finset κ) (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (k : {k // k ∈ g}) :
    (imageEquiv π g hinj k).val = π k.val := rfl

theorem piCongrImage_symm_apply {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    (g : Finset κ) (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b)
    (x : Pd (V := V) (g.image π)) (k : {k // k ∈ g}) :
    (piCongrImage (V := V) π g hinj).symm x k
      = x ⟨π k.val, Finset.mem_image.mpr ⟨k.val, k.2, rfl⟩⟩ := by
  show (Equiv.piCongrLeft (fun j : {j // j ∈ g.image π} => V (j.val))
      (imageEquiv π g hinj)).symm x k = x ⟨π k.val, Finset.mem_image.mpr ⟨k.val, k.2, rfl⟩⟩
  rw [show (Equiv.piCongrLeft (fun j : {j // j ∈ g.image π} => V (j.val))
      (imageEquiv π g hinj)).symm x k = x (imageEquiv π g hinj k) from
    Equiv.piCongrLeft_symm_apply _ _ _ _]
  rfl

/-- The "lower" set of an edge of a bundle: the intersection of the previous factors. -/
noncomputable def lowSet {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (G : Finset (Finset κ))
    (Ag : Finset κ → Finset (BPt V π)) (g : Finset κ) : Finset (BPt V π) :=
  Finset.univ.filter (fun v => ∀ g' ∈ G, g' ⊂ g → v ∈ Ag g')

theorem mem_lowSet {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {G : Finset (Finset κ)}
    {Ag : Finset κ → Finset (BPt V π)} {g : Finset κ} {v : BPt V π} :
    v ∈ lowSet π G Ag g ↔ ∀ g' ∈ G, g' ⊂ g → v ∈ Ag g' := by
  classical
  simp only [lowSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The product of the indicators of the factors below `g` is the indicator of `lowSet`. -/
theorem prod_indicator_lowSet {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    (G : Finset (Finset κ)) (Ag : Finset κ → Finset (BPt V π)) (g : Finset κ) (v : BPt V π) :
    (∏ g' ∈ G.filter (fun g' => g' ⊂ g), indicator (Ag g') v)
      = indicator (lowSet π G Ag g) v := by
  classical
  rw [show (∏ g' ∈ G.filter (fun g' => g' ⊂ g), indicator (Ag g') v)
      = ∏ g' ∈ G.filter (fun g' => g' ⊂ g), (if v ∈ Ag g' then (1 : ℝ) else 0) from rfl]
  rw [Commons.Data.Finset.prod_ite_one_mem]
  rw [show indicator (lowSet π G Ag g) v
      = (if v ∈ lowSet π G Ag g then (1 : ℝ) else 0) from rfl]
  by_cases h : v ∈ lowSet π G Ag g
  · have h' : ∀ g' ∈ G.filter (fun g' => g' ⊂ g), v ∈ Ag g' := fun g' hg' =>
      (mem_lowSet.mp h) g' (Finset.mem_filter.mp hg').1 (Finset.mem_filter.mp hg').2
    rw [if_pos h, if_pos h']
  · have h' : ¬ ∀ g' ∈ G.filter (fun g' => g' ⊂ g), v ∈ Ag g' := fun hh =>
      h (mem_lowSet.mpr (fun g' hg' hlt => hh g' (Finset.mem_filter.mpr ⟨hg', hlt⟩)))
    rw [if_neg h, if_neg h']

/-- Membership in the `Pd`-level lift. -/
theorem mem_liftPd {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (A : Finset (Pt V))
    (w : Pd (V := fun k => V (π k)) g) :
    w ∈ liftPd (V := V) π g hinj A
      ↔ piCongrImage (V := V) π g hinj w ∈ shadow (V := V) (g.image π) A :=
  Finset.mem_preimage

/-- Membership characterisation of the lifted set. -/
theorem mem_liftSet_iff {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (A : Finset (Pt V)) (v : BPt V π) :
    v ∈ liftSet (V := V) π g hinj A ↔ ∃ x ∈ A, ∀ k ∈ g, x (π k) = v k := by
  classical
  rw [mem_liftSet, mem_liftPd, mem_shadow]
  constructor
  · rintro ⟨x, hxA, hx⟩
    refine ⟨x, hxA, fun k hk => ?_⟩
    have h3 : (piCongrImage (V := V) π g hinj).symm (restrict (V := V) x (g.image π))
        ⟨k, hk⟩ = (restrict (V := fun k => V (π k)) v g) ⟨k, hk⟩ := by
      rw [hx, Equiv.symm_apply_apply]
    rw [piCongrImage_symm_apply] at h3
    simp only [restrict_apply] at h3
    exact h3
  · rintro ⟨x, hxA, hx⟩
    refine ⟨x, hxA, ?_⟩
    funext j
    obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp j.2
    have h3 := piCongrImage_symm_apply (V := V) π g hinj
      ((piCongrImage (V := V) π g hinj) (restrict (V := fun k => V (π k)) v g)) ⟨k, hk⟩
    rw [Equiv.symm_apply_apply] at h3
    have h4 : (piCongrImage (V := V) π g hinj) (restrict (V := fun k => V (π k)) v g) j
        = x j.1 := by
      rw [show j = (⟨π k, Finset.mem_image.mpr ⟨k, hk, rfl⟩⟩ : {j // j ∈ g.image π})
        from Subtype.ext hkj.symm]
      rw [← h3, restrict_apply, hx k hk]
    rw [h4]
    rfl

/-! ## The extension of a bundle point to an ambient point

For a bundle edge `g` of a bundle `(κ, π, V)` and a bundle point `v`, `extPt` is an
arbitrary ambient point `Pt V` whose `π`-coordinates on `g` agree with `v`.  Such a
point exists because `π` is injective on `g`. -/

/-- An arbitrary extension of a `Pd V e` point to `Pt V`. -/
noncomputable def extOfPd (e : Finset ι) (w : Pd (V := V) e) : Pt V :=
  fun j => if h : j ∈ e then w ⟨j, h⟩ else Classical.arbitrary (V j)

theorem extOfPd_apply {e : Finset ι} (w : Pd (V := V) e) {j : ι} (hj : j ∈ e) :
    extOfPd (V := V) e w j = w ⟨j, hj⟩ := dif_pos hj

theorem restrict_extOfPd (e : Finset ι) (w : Pd (V := V) e) :
    restrict (extOfPd (V := V) e w) e = w := by
  funext i
  exact extOfPd_apply (V := V) w i.2

/-- The canonical point of `Pd V (g.image π)` carrying the values of `v` on `g`. -/
noncomputable def extPd {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (v : BPt V π) : Pd (V := V) (g.image π) :=
  piCongrImage (V := V) π g hinj (restrict (V := fun k => V (π k)) v g)

/-- An ambient point of `Pt V` extending a bundle point (along `π` on `g`). -/
noncomputable def extPt {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (v : BPt V π) : Pt V :=
  extOfPd (V := V) (g.image π) (extPd (V := V) π g hinj v)

theorem extPt_apply {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (v : BPt V π) {k : κ} (hk : k ∈ g) :
    extPt (V := V) π g hinj v (π k) = v k := by
  have hmem : π k ∈ g.image π := Finset.mem_image.mpr ⟨k, hk, rfl⟩
  rw [extPt, extOfPd_apply (V := V) _ hmem]
  show (piCongrImage (V := V) π g hinj (restrict (V := fun k => V (π k)) v g))
      ⟨π k, Finset.mem_image.mpr ⟨k, hk, rfl⟩⟩ = v k
  have h := piCongrImage_symm_apply (V := V) π g hinj
    ((piCongrImage (V := V) π g hinj) (restrict (V := fun k => V (π k)) v g)) ⟨k, hk⟩
  rw [Equiv.symm_apply_apply] at h
  rw [← h]
  rfl

/-- Two points agreeing on `e` are equivalent for `coord e`-measurable sets. -/
theorem mem_iff_of_agree {e : Finset ι} {A : Finset (Pt V)}
    (hA : (coord (V := V) e).IsMeas A) {x y : Pt V} (h : ∀ i ∈ e, y i = x i) :
    y ∈ A ↔ x ∈ A :=
  (coord_isMeas_iff.mp hA) x y h

/-- The image under `π` of a proper subset of `g` is a proper subset of `g.image π`
when `π` is injective on `g`. -/
theorem image_ssubset_image {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {g g' : Finset κ}
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (hsub : g' ⊆ g) (hne : g' ≠ g) :
    g'.image π ⊂ g.image π := by
  classical
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.image_subset_image hsub, ?_⟩
  intro himg
  apply hne
  have hgsub : g ⊆ g' := by
    intro k hk
    have : π k ∈ g'.image π := by rw [himg]; exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    obtain ⟨k', hk', hk'k⟩ := Finset.mem_image.mp this
    have : k' = k := hinj k' (hsub hk') k hk hk'k
    rwa [this] at hk'
  exact Finset.Subset.antisymm hsub hgsub

/-- Lifting a set along a subset of a bundle edge (vacuous when not a subset). -/
noncomputable def liftSetSub {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (A : Finset (Pt V)) (g' : Finset κ) :
    Finset (BPt V π) :=
  if h : g' ⊆ g then
    liftSet (V := V) π g' (fun a ha b hb hab => hinj a (h ha) b (h hb) hab) A
  else ∅

theorem liftSetSub_of_subset {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (A : Finset (Pt V)) {g' : Finset κ}
    (h : g' ⊆ g) :
    liftSetSub (V := V) π g hinj A g'
      = liftSet (V := V) π g' (fun a ha b hb hab => hinj a (h ha) b (h hb) hab) A :=
  dif_pos h

/-- **`lowSet` is the lift of `interProper`.** -/
theorem lowSet_liftSet_eq {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b) (A : Finset ι → Finset (Pt V))
    (hA : ∀ f, f ⊂ g.image π → (coord (V := V) f).IsMeas (A f)) :
    lowSet π g.powerset (fun g' => liftSetSub (V := V) π g hinj (A (g'.image π)) g') g
      = lowSetLift (V := V) π g hinj A := by
  classical
  ext v
  rw [mem_lowSet]
  simp only [lowSetLift]
  rw [mem_liftSet_iff]
  constructor
  · intro h
    refine ⟨extPt (V := V) π g hinj v, ?_, fun k hk => extPt_apply (V := V) π g hinj v hk⟩
    rw [mem_interProper]
    intro f hfpow hflt
    have hfsub : f ⊆ g.image π := Finset.mem_powerset.mp hfpow
    set gf : Finset κ := g.filter (fun k => π k ∈ f) with hgf
    have hgfsub : gf ⊆ g := Finset.filter_subset _ _
    have hgfimg : gf.image π = f := by
      apply Finset.Subset.antisymm
      · intro j hj
        obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp hj
        rw [← hkj]
        exact (Finset.mem_filter.mp hk).2
      · intro j hj
        have : j ∈ g.image π := hfsub hj
        obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp this
        refine Finset.mem_image.mpr ⟨k, ?_, hkj⟩
        exact Finset.mem_filter.mpr ⟨hk, by rw [hkj]; exact hj⟩
    have hgfne : gf ≠ g := by
      intro heq
      have : f = g.image π := by rw [← hgfimg, heq]
      exact (Finset.ssubset_iff_subset_ne.mp hflt).2 this
    have hgfss : gf ⊂ g := Finset.ssubset_iff_subset_ne.mpr ⟨hgfsub, hgfne⟩
    have hv := h gf (Finset.mem_powerset.mpr hgfsub) hgfss
    rw [liftSetSub_of_subset (V := V) π g hinj (A (gf.image π)) hgfsub, hgfimg,
      mem_liftSet_iff] at hv
    obtain ⟨xf, hxAf, hxf⟩ := hv
    refine (mem_iff_of_agree (hA f hflt) ?_).mpr hxAf
    intro i hi
    have hi' : i ∈ g.image π := hfsub hi
    obtain ⟨k, hk, hki⟩ := Finset.mem_image.mp hi'
    have hkf : k ∈ gf := Finset.mem_filter.mpr ⟨hk, by rw [hki]; exact hi⟩
    rw [← hki, extPt_apply (V := V) π g hinj v hk, (hxf k hkf).symm]
  · rintro ⟨x, hx, hxv⟩ g' hg'pow hg'lt
    have hg'sub : g' ⊆ g := Finset.mem_powerset.mp hg'pow
    rw [liftSetSub_of_subset (V := V) π g hinj (A (g'.image π)) hg'sub, mem_liftSet_iff]
    refine ⟨x, ?_, fun k hk => hxv k (hg'lt.1 hk)⟩
    exact (mem_interProper.mp hx) (g'.image π)
      (Finset.mem_powerset.mpr (Finset.image_subset_image hg'sub))
      (image_ssubset_image hinj hg'sub (Finset.ssubset_iff_subset_ne.mp hg'lt).2)

/-- The product of the lifted indicators over the proper subsets of `g` is the
indicator of the lift of `interProper`. -/
theorem prod_indicator_liftSet_lowSet {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    (g : Finset κ) (hinj : ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b)
    (A : Finset ι → Finset (Pt V)) (hA : ∀ f, f ⊂ g.image π → (coord (V := V) f).IsMeas (A f))
    (v : BPt V π) :
    (∏ g' ∈ g.powerset.filter (fun g' => g' ⊂ g),
        indicator (liftSetSub (V := V) π g hinj (A (g'.image π)) g') v)
      = indicator (lowSetLift (V := V) π g hinj A) v := by
  rw [prod_indicator_lowSet (V := V) π g.powerset
      (fun g' => liftSetSub (V := V) π g hinj (A (g'.image π)) g') g v,
    lowSet_liftSet_eq (V := V) π g hinj A hA]

end Szemeredi.Removal
