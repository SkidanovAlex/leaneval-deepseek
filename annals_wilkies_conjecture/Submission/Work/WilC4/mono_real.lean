/-
  WilC4 : `mono_real` — the o-minimal monotonicity theorem ("R-mono" of the C4 route).

  `mono_real` states: a `∅`-definable functional subset `Y ⊆ ℝ²` (a partial definable function)
  agrees with a monotone function on every interval avoiding a finite exceptional set `B`.

  Proof outline (the classical proof of the o-minimal monotonicity theorem; see the design notes in
  `Submission/Work/WilC4/monoDefs.lean` and `sources/wilkiesC4route/wilkies_C4_route.md`):

  * `hOM` (o-minimality of every model of `TR`) instantiated at `ℝ` gives, for every `∅`-definable
    set of reals, a decomposition into finitely many order-convex pieces; consequently the
    topological boundary (`Work.WilC2.IsBnd`) of such a set is finite.
  * The exceptional set `MonoBnd Y` is the union of the boundaries of the domain, of the locally
    constant locus and of the four one-sided germ-type sets `MonoLm, MonoHm, MonoLp, MonoHp`; it is
    `∅`-definable (`WilC2.bnd_definable_alt`) and finite.
  * On an interval `(a,b)` avoiding `MonoBnd Y`: either `Y` is locally constant on it (hence
    constant), or no point of it is locally constant and the one-sided germ dichotomy shows that
    every point is of one of the four germ types; the boundaries being avoided, the type is
    constant along `(a,b)`.  The combinations (left below, right above) and (left above, right
    below) force monotonicity, while the two "local extremum at every point" combinations are
    impossible.
-/
import Mathlib
import Submission.Work.WilC4.monoDefs
import Submission.Work.WilC4.monoDefinable_basic
import Submission.Work.WilC4.monoDefinable_W
import Submission.Work.WilC4.monoDefinable_germs
import Submission.Work.WilC4.monoLHset_ordConnected
import Submission.Work.WilC4.finUnionOrd_germ
import Submission.Work.WilC4.bnd_interval_dichotomy
import Submission.Work.WilC4.germ_extr
import Submission.Work.WilC4.germ_mono_of_types
import Submission.Work.WilC4.germ_cover
import Submission.Work.WilC4.germ_const_of_W
import Submission.Work.WilC2.Main
import Submission.Work.WilC2.bnd_ordConnected_finite
import Submission.Work.WilC2.bnd_sUnion_finset
import Submission.Work.WilC2.bnd_definable_alt

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-! ### O-minimality at `ℝ` -/

theorem oMin_structure (hOM : OMinModels) {X : Set (Fin 1 → ℝ)}
    (hX : (Set.univ : Set ℝ).Definable LRc X) :
    ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      X = {x : Fin 1 → ℝ | x 0 ∈ ⋃₀ (s : Set (Set ℝ))} := by
  haveI : ℝ ⊨ TR := inferInstanceAs (ℝ ⊨ LRc.completeTheory ℝ)
  exact hOM ℝ X hX

theorem univ_definable {S : Set ℝ} (h : (∅ : Set ℝ).Definable₁ LRc S) :
    (Set.univ : Set ℝ).Definable LRc {x : Fin 1 → ℝ | x 0 ∈ S} :=
  h.mono (Set.empty_subset _)

/-- A `∅`-definable set of reals is a finite union of order-convex pieces. -/
theorem oMin_ordConnected_set (hOM : OMinModels) {S : Set ℝ}
    (hS : (∅ : Set ℝ).Definable₁ LRc S) :
    ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧ S = ⋃₀ (s : Set (Set ℝ)) := by
  obtain ⟨s, hs, heq⟩ := oMin_structure hOM (univ_definable hS)
  refine ⟨s, hs, ?_⟩
  ext x
  have h := Set.ext_iff.mp heq (fun _ : Fin 1 => x)
  simpa using h

theorem bnd_finite_of_ordConnected {S : Set ℝ} {s : Finset (Set ℝ)}
    (hs : ∀ I ∈ s, I.OrdConnected) (hS : S = ⋃₀ (s : Set (Set ℝ))) :
    {x : ℝ | WilC2.IsBnd S x}.Finite := by
  rw [hS]
  refine (Set.Finite.biUnion s.finite_toSet
    (fun I hI => WilC2.bnd_ordConnected_finite (hs I hI))).subset ?_
  intro x hx
  obtain ⟨I, hI, hIx⟩ := WilC2.bnd_sUnion_finset hx
  exact Set.mem_biUnion hI hIx

/-- The boundary points of a `∅`-definable set of reals form a finite set. -/
theorem bnd_finite_of_definable (hOM : OMinModels) {S : Set ℝ}
    (hS : (∅ : Set ℝ).Definable₁ LRc S) :
    {x : ℝ | WilC2.IsBnd S x}.Finite := by
  obtain ⟨s, hs, heq⟩ := oMin_ordConnected_set hOM hS
  exact bnd_finite_of_ordConnected hs heq

/-! ### The exceptional set: definability and finiteness -/

theorem monoBnd_definable {Y : Set (Fin 2 → ℝ)}
    (hDom : (∅ : Set ℝ).Definable₁ LRc (MonoDom Y))
    (hW : (∅ : Set ℝ).Definable₁ LRc (MonoW Y))
    (hLm : (∅ : Set ℝ).Definable₁ LRc (MonoLm Y))
    (hHm : (∅ : Set ℝ).Definable₁ LRc (MonoHm Y))
    (hLp : (∅ : Set ℝ).Definable₁ LRc (MonoLp Y))
    (hHp : (∅ : Set ℝ).Definable₁ LRc (MonoHp Y)) :
    (∅ : Set ℝ).Definable₁ LRc (MonoBnd Y) := by
  have h1 : (∅ : Set ℝ).Definable₁ LRc {x : ℝ | WilC2.IsBnd (MonoDom Y) x} :=
    WilC2.bnd_definable_alt WilC2.real_exists_sq hDom
  have h2 : (∅ : Set ℝ).Definable₁ LRc {x : ℝ | WilC2.IsBnd (MonoW Y) x} :=
    WilC2.bnd_definable_alt WilC2.real_exists_sq hW
  have h3 : (∅ : Set ℝ).Definable₁ LRc {x : ℝ | WilC2.IsBnd (MonoLm Y) x} :=
    WilC2.bnd_definable_alt WilC2.real_exists_sq hLm
  have h4 : (∅ : Set ℝ).Definable₁ LRc {x : ℝ | WilC2.IsBnd (MonoHm Y) x} :=
    WilC2.bnd_definable_alt WilC2.real_exists_sq hHm
  have h5 : (∅ : Set ℝ).Definable₁ LRc {x : ℝ | WilC2.IsBnd (MonoLp Y) x} :=
    WilC2.bnd_definable_alt WilC2.real_exists_sq hLp
  have h6 : (∅ : Set ℝ).Definable₁ LRc {x : ℝ | WilC2.IsBnd (MonoHp Y) x} :=
    WilC2.bnd_definable_alt WilC2.real_exists_sq hHp
  exact ((((h1.union h2).union h3).union h4).union h5).union h6

theorem monoBnd_finite {Y : Set (Fin 2 → ℝ)} (hOM : OMinModels)
    (hDom : (∅ : Set ℝ).Definable₁ LRc (MonoDom Y))
    (hW : (∅ : Set ℝ).Definable₁ LRc (MonoW Y))
    (hLm : (∅ : Set ℝ).Definable₁ LRc (MonoLm Y))
    (hHm : (∅ : Set ℝ).Definable₁ LRc (MonoHm Y))
    (hLp : (∅ : Set ℝ).Definable₁ LRc (MonoLp Y))
    (hHp : (∅ : Set ℝ).Definable₁ LRc (MonoHp Y)) :
    (MonoBnd Y).Finite := by
  have hu : ((((({x : ℝ | WilC2.IsBnd (MonoDom Y) x} ∪ {x : ℝ | WilC2.IsBnd (MonoW Y) x}) ∪
      {x : ℝ | WilC2.IsBnd (MonoLm Y) x}) ∪ {x : ℝ | WilC2.IsBnd (MonoHm Y) x}) ∪
      {x : ℝ | WilC2.IsBnd (MonoLp Y) x}) ∪ {x : ℝ | WilC2.IsBnd (MonoHp Y) x}).Finite :=
    (((((bnd_finite_of_definable hOM hDom).union (bnd_finite_of_definable hOM hW)).union
      (bnd_finite_of_definable hOM hLm)).union
      (bnd_finite_of_definable hOM hHm)).union
      (bnd_finite_of_definable hOM hLp)).union (bnd_finite_of_definable hOM hHp)
  refine hu.subset ?_
  intro x hx
  simpa only [MonoBnd, Set.mem_union, Set.mem_setOf_eq] using hx

/-! ### The monotonicity alternative on an interval -/

theorem monoOn_main {Y : Set (Fin 2 → ℝ)} (hY : (∅ : Set ℝ).Definable LRc Y)
    (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y')
    (hOM : OMinModels) {a b : ℝ} (hab : a < b)
    (havb : ∀ x ∈ Set.Ioo a b, x ∉ MonoBnd Y) :
    MonoIncOn Y a b ∨ MonoDecOn Y a b := by
  obtain ⟨hDomD, hLAD, hHAD⟩ := monoDefinable_basic hY
  have hWD := monoDefinable_W hY
  obtain ⟨hLmD, hHmD, hLpD, hHpD⟩ := monoDefinable_germs hY
  obtain ⟨hLs_ord, hHs_ord⟩ := monoLHset_ordConnected hLAD hHAD hOM
  have hbDom : ∀ x ∈ Set.Ioo a b, ¬ WilC2.IsBnd (MonoDom Y) x :=
    fun x hx h => havb x hx (isBnd_dom_mem_MonoBnd Y h)
  have hbW : ∀ x ∈ Set.Ioo a b, ¬ WilC2.IsBnd (MonoW Y) x :=
    fun x hx h => havb x hx (isBnd_W_mem_MonoBnd Y h)
  have hbLm : ∀ x ∈ Set.Ioo a b, ¬ WilC2.IsBnd (MonoLm Y) x :=
    fun x hx h => havb x hx (isBnd_Lm_mem_MonoBnd Y h)
  have hbHm : ∀ x ∈ Set.Ioo a b, ¬ WilC2.IsBnd (MonoHm Y) x :=
    fun x hx h => havb x hx (isBnd_Hm_mem_MonoBnd Y h)
  have hbLp : ∀ x ∈ Set.Ioo a b, ¬ WilC2.IsBnd (MonoLp Y) x :=
    fun x hx h => havb x hx (isBnd_Lp_mem_MonoBnd Y h)
  have hbHp : ∀ x ∈ Set.Ioo a b, ¬ WilC2.IsBnd (MonoHp Y) x :=
    fun x hx h => havb x hx (isBnd_Hp_mem_MonoBnd Y h)
  have hDom := bnd_interval_dichotomy hbDom
  have hW := bnd_interval_dichotomy hbW
  have hLm := bnd_interval_dichotomy hbLm
  have hHm := bnd_interval_dichotomy hbHm
  have hLp := bnd_interval_dichotomy hbLp
  have hHp := bnd_interval_dichotomy hbHp
  rcases hDom with hDom | hDom
  · rcases hW with hW | hW
    · exact Or.inl (germ_const_of_W hfun hW)
    · have hW' : ∀ x ∈ Set.Ioo a b, x ∉ MonoW Y := fun x hx => hW hx
      have hcov : ∀ x ∈ Set.Ioo a b,
          (x ∈ MonoLm Y ∨ x ∈ MonoHm Y) ∧ (x ∈ MonoLp Y ∨ x ∈ MonoHp Y) :=
        fun x hx => germ_cover hfun (fun S hS y => finUnionOrd_germ hS y) hLs_ord hHs_ord hDom hW' hx
      have hleft : Set.Ioo a b ⊆ MonoLm Y ∨ Set.Ioo a b ⊆ MonoHm Y := by
        rcases hLm with h | h
        · exact Or.inl h
        · refine Or.inr fun x hx => ?_
          rcases (hcov x hx).1 with hl | hm
          · exact absurd hl (h hx)
          · exact hm
      have hright : Set.Ioo a b ⊆ MonoLp Y ∨ Set.Ioo a b ⊆ MonoHp Y := by
        rcases hLp with h | h
        · exact Or.inl h
        · refine Or.inr fun x hx => ?_
          rcases (hcov x hx).2 with hl | hp
          · exact absurd hl (h hx)
          · exact hp
      rcases hleft with hleft | hleft
      · rcases hright with hright | hright
        · exact (germ_extr hab hfun).1 ⟨hleft, hright⟩ |>.elim
        · exact Or.inl ((germ_mono_of_types hfun).1 ⟨hleft, hright⟩)
      · rcases hright with hright | hright
        · exact Or.inr ((germ_mono_of_types hfun).2 ⟨hleft, hright⟩)
        · exact (germ_extr hab hfun).2 ⟨hleft, hright⟩ |>.elim
  · exact Or.inl fun x₁ x₂ y₁ y₂ h1 h2 h3 hy1 _ =>
      absurd ⟨y₁, hy1⟩ (hDom ⟨h1, h2.trans h3⟩)

/-! ### The monotonicity theorem -/

theorem mono_real {Y : Set (Fin 2 → ℝ)} (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y') (hOM : WilkiesDesign.CG.OMinModels) : ∃ B : Set ℝ, (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc {p : Fin 1 → ℝ | p 0 ∈ B} ∧ B.Finite ∧ ∀ a b : ℝ, a < b → (∀ x ∈ Set.Ioo a b, x ∉ B) → ∀ x₁ x₂ x₃ y₁ y₂ y₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b → x₃ ∈ Set.Ioo a b → x₁ < x₂ → x₂ < x₃ → ![x₁, y₁] ∈ Y → ![x₂, y₂] ∈ Y → ![x₃, y₃] ∈ Y → ((y₁ ≤ y₂ ∧ y₂ ≤ y₃) ∨ (y₂ ≤ y₁ ∧ y₃ ≤ y₂)) := by
  obtain ⟨hDomD, hLAD, hHAD⟩ := monoDefinable_basic hY
  have hWD := monoDefinable_W hY
  obtain ⟨hLmD, hHmD, hLpD, hHpD⟩ := monoDefinable_germs hY
  refine ⟨MonoBnd Y, monoBnd_definable hDomD hWD hLmD hHmD hLpD hHpD,
    monoBnd_finite hOM hDomD hWD hLmD hHmD hLpD hHpD, ?_⟩
  intro a b hab havb x₁ x₂ x₃ y₁ y₂ y₃ hx₁ hx₂ hx₃ hlt₁ hlt₂ hy₁ hy₂ hy₃
  rcases monoOn_main hY hfun hOM hab havb with hinc | hdec
  · exact Or.inl ⟨hinc _ _ _ _ hx₁.1 hlt₁ hx₂.2 hy₁ hy₂,
      hinc _ _ _ _ hx₂.1 hlt₂ hx₃.2 hy₂ hy₃⟩
  · exact Or.inr ⟨hdec _ _ _ _ hx₁.1 hlt₁ hx₂.2 hy₁ hy₂,
      hdec _ _ _ _ hx₂.1 hlt₂ hx₃.2 hy₂ hy₃⟩

end Work.WilC4
