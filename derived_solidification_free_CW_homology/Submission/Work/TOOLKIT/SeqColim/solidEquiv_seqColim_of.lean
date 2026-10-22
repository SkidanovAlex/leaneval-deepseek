import Mathlib
import Submission.Work.TOOLKIT.Basic
import Submission.Work.TOOLKIT.Instances
import Submission.Work.TOOLKIT.SeqColim.Defs
import Submission.Work.TOOLKIT.SeqColim.mono_toPi
import Submission.Work.TOOLKIT.SeqColim.exact_telShort
import Submission.Work.TOOLKIT.SeqColim.exists_telShortMap

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Submission.Blueprint

noncomputable section

set_option linter.style.haveILetI false

namespace Work.TOOLKIT.SeqColim

/-! ## Auxiliary results about the telescope of a sequential diagram

`Submission.Work.TOOLKIT.SeqColim.Defs` defines, for `F : ℕ ⥤ Cpx`, the telescope short complex
`telShort F = (∐_n F_n --telD F--> ∐_n F_n --toColim F--> colim F)`, where `telD F = 1 - shift`.

The following three facts are proved in the sibling modules:

* `mono_toPi X`: the canonical map `∐_n X_n ⟶ ∏_n X_n` is a monomorphism (`mono_toPi.lean`);
* `exact_telShort F`: `telShort F` is exact (`exact_telShort.lean`);
* `exists_telShortMap F G τ`: a natural transformation of towers induces a morphism of telescope
  short complexes whose components are `Sigma.map (fun n => τ.app n)` and `colim.map τ`
  (`exists_telShortMap.lean`).

Here we draw the consequences used in the proof of the main theorem. -/

/-- A morphism into a coproduct of an `ℕ`-indexed family all of whose coordinates vanish is
zero.  This is the "detection" form of `mono_toPi`. -/
lemma eq_zero_of_forall_coord_eq_zero (X : ℕ → Cpx) (T : Cpx) (u : T ⟶ ∐ X)
    (h : ∀ n, u ≫ coord X n = 0) : u = 0 := by
  haveI : Mono (Pi.lift (fun n => coord X n)) := mono_toPi X
  refine (cancel_mono (Pi.lift (fun n => coord X n))).mp ?_
  rw [zero_comp]
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, Pi.lift_comp_π, h n, zero_comp]

/-- `1 - shift` is a monomorphism on the coproduct of a tower: this is the "coordinate recursion",
using that a morphism into a coproduct all of whose coordinates vanish is zero. -/
theorem mono_telD (F : ℕ ⥤ Cpx) : Mono (telD F) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro T u hu
  apply eq_zero_of_forall_coord_eq_zero (fun n => F.obj n) T u
  intro n
  have h1 : u = u ≫ towerShift (fun n => F.obj n) (step F) := by
    have h2 : u ≫ (𝟙 (∐ fun n => F.obj n) - towerShift (fun n => F.obj n) (step F)) =
        u - u ≫ towerShift (fun n => F.obj n) (step F) := by
      rw [Preadditive.comp_sub, Category.comp_id]
    rw [telD, towerD] at hu
    rw [h2, sub_eq_zero] at hu
    exact hu
  induction n with
  | zero => rw [h1, Category.assoc, towerShift_coord_zero, comp_zero]
  | succ k ih => rw [h1, Category.assoc, towerShift_coord_succ, ← Category.assoc, ih, zero_comp]

/-- The telescope short complex of a sequential diagram is short exact. -/
theorem shortExact_telShort (F : ℕ ⥤ Cpx) : (telShort F).ShortExact := by
  refine ShortComplex.ShortExact.mk' (exact_telShort F) (mono_telD F) ?_
  exact epi_toColim F

/-! ## The main theorem -/

/-- Sequential colimits along monomorphisms preserve solid-equivalences, assuming the
two-out-of-three property for short exact sequences (`hSes`) and stability under small coproducts
(`hsigma`).  Route: for a tower of complexes with monomorphisms the telescope sequence
`∐_n F_n → ∐_n F_n → colim F` (the first map being `1 - shift`, where `shift` is induced by the
transition maps) is short exact; applying it to the tower `F` and to the tower `G` and using `τ`
gives a morphism of short exact sequences whose first two components are the coproduct of the
`τ_n`'s (solid-equivalences by `hsigma`), so the third component `colim.map τ` is one as well
(this is `hSes` applied with `φ.τ₃ = colim.map τ`). -/
theorem solidEquiv_seqColim_of
    (hSes : ∀ {S₁ S₂ : CategoryTheory.ShortComplex Work.TOOLKIT.Cpx}, S₁.ShortExact →
      S₂.ShortExact → (φ : S₁ ⟶ S₂) →
      Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map φ.τ₁) →
      Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map φ.τ₂) →
      Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map φ.τ₃))
    (hsigma : ∀ (J : Type) (K L : J → Work.TOOLKIT.Cpx)
      [CategoryTheory.Limits.HasCoproduct K] [CategoryTheory.Limits.HasCoproduct L]
      (f : ∀ j, K j ⟶ L j), (∀ j, Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map (f j))) →
      Submission.Blueprint.SolidEquiv
        (DerivedCategory.Q.map (CategoryTheory.Limits.Sigma.map f)))
    (F G : CategoryTheory.Functor ℕ Work.TOOLKIT.Cpx) (τ : F ⟶ G)
    (hF : ∀ n, CategoryTheory.Mono (F.map (CategoryTheory.homOfLE (Nat.le_succ n))))
    (hG : ∀ n, CategoryTheory.Mono (G.map (CategoryTheory.homOfLE (Nat.le_succ n))))
    (h : ∀ n, Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map (τ.app n))) :
    Submission.Blueprint.SolidEquiv
      (DerivedCategory.Q.map (CategoryTheory.Limits.colim.map τ)) := by
  obtain ⟨φ, h1, h2, h3⟩ := exists_telShortMap F G τ
  haveI : CategoryTheory.Limits.HasCoproduct (fun n => F.obj n) := inferInstance
  haveI : CategoryTheory.Limits.HasCoproduct (fun n => G.obj n) := inferInstance
  have hσ : Submission.Blueprint.SolidEquiv
      (DerivedCategory.Q.map (CategoryTheory.Limits.Sigma.map (fun n => τ.app n))) :=
    hsigma ℕ (fun n => F.obj n) (fun n => G.obj n) (fun n => τ.app n) h
  have hres := hSes (shortExact_telShort F) (shortExact_telShort G) φ
    (by rw [h1]; exact hσ) (by rw [h2]; exact hσ)
  rw [← h3]
  exact hres

end Work.TOOLKIT.SeqColim
