/-
  WilC4 : the *parametric* o-minimal monotonicity theorem.

  The vocabulary (`PDom`, `PW`, `PLm`, `PHm`, `PLp`, `PHp`, `PBnd`, `Pfibre`) is in
  `Submission.Work.WilC4.ParamMonoDefs`.  `mono_real` gives, for a single `∅`-definable partial
  function `Y ⊆ ℝ²`, a finite exceptional set `MonoBnd Y` off which `Y` is monotone.  Here a
  `∅`-definable *family* `Y ⊆ ℝ^{k+2}` of partial functions is handled:

  * `PBnd Y ⊆ ℝ^{k+1}` is the family `c ↦ MonoBnd (Pfibre Y c)` of exceptional sets; it is
    `∅`-definable by the delegated lemmas `paramDom_definable`, `paramW_definable`,
    `paramGerms_definable` and `paramBnd_definable` (see `PBnd_definable` below).
  * the fibres of `PBnd Y` are uniformly finite: `PBnd Y` is given by an `LRc`-formula, so the
    uniform finiteness theorem `exists_alt_bound` bounds the number of order-convex components of
    every fibre uniformly; each fibre is finite because it is the boundary set of a definable
    partial function (`monoBnd_finite`).
  * off `PBnd Y`, each fibre is monotone (`monoOn_main`), which yields the three-point order
    condition of the statement.
-/
import Mathlib
import Submission.Work.WilC4.mono_real
import Submission.Work.WilC4.unifFinite_of_omin
import Submission.Work.WilC4.ParamMonoDefs
import Submission.Work.WilC4.paramDom_definable
import Submission.Work.WilC4.paramW_definable
import Submission.Work.WilC4.paramGerms_definable
import Submission.Work.WilC4.paramBnd_definable
import Submission.Work.WilC4.paramFibre_definable
import Submission.Work.WilC4.encard_le_of_not_altChain

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-- `PBnd Y` is `∅`-definable: assemble the six parametric boundary sets, each of which is
`∅`-definable by definability of the corresponding parametric locus plus the parametric boundary
lemma. -/
theorem PBnd_definable {n : ℕ} {Y : Set (Fin (n + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PBnd Y) := by
  have h1 : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {p : Fin (n + 1) → ℝ | WilC2.IsBnd (Pfib1 (PDom Y) p) (p 0)} :=
    paramBnd_definable (paramDom_definable hY)
  have h2 : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {p : Fin (n + 1) → ℝ | WilC2.IsBnd (Pfib1 (PW Y) p) (p 0)} :=
    paramBnd_definable (paramW_definable hY)
  obtain ⟨h3, h4, h5, h6⟩ := paramGerms_definable (Y := Y) hY
  have h3' : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {p : Fin (n + 1) → ℝ | WilC2.IsBnd (Pfib1 (PLm Y) p) (p 0)} :=
    paramBnd_definable h3
  have h4' : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {p : Fin (n + 1) → ℝ | WilC2.IsBnd (Pfib1 (PHm Y) p) (p 0)} :=
    paramBnd_definable h4
  have h5' : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {p : Fin (n + 1) → ℝ | WilC2.IsBnd (Pfib1 (PLp Y) p) (p 0)} :=
    paramBnd_definable h5
  have h6' : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {p : Fin (n + 1) → ℝ | WilC2.IsBnd (Pfib1 (PHp Y) p) (p 0)} :=
    paramBnd_definable h6
  unfold PBnd
  exact ((((h1.union h2).union h3').union h4').union h5').union h6'

theorem ulpm_mono_param {k : ℕ} (hOM : WilkiesDesign.CG.OMinModels) (Y : Set (Fin (k + 2) → ℝ))
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
      Fin.cons x (Fin.cons y' c) ∈ Y → y = y') :
    ∃ N : ℕ, ∃ B : Set (Fin (k + 1) → ℝ), (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B ∧
      (∀ c : Fin k → ℝ, {x : ℝ | Fin.cons x c ∈ B}.encard ≤ N) ∧
      ∀ c : Fin k → ℝ, ∀ a b : ℝ, a < b →
        (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B) →
        ∀ x₁ x₂ x₃ y₁ y₂ y₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b →
          x₃ ∈ Set.Ioo a b → x₁ < x₂ → x₂ < x₃ →
          Fin.cons x₁ (Fin.cons y₁ c) ∈ Y → Fin.cons x₂ (Fin.cons y₂ c) ∈ Y →
          Fin.cons x₃ (Fin.cons y₃ c) ∈ Y →
          ((y₁ ≤ y₂ ∧ y₂ ≤ y₃) ∨ (y₃ ≤ y₂ ∧ y₂ ≤ y₁)) := by
  have hB : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PBnd Y) := PBnd_definable hY
  -- isolate the last coordinate by reindexing `Fin (k+1)` as `Fin k ⊕ Fin 1`
  set g : Fin (k + 1) → Fin k ⊕ Fin 1 :=
    Fin.cases (Sum.inr 0) (fun j : Fin k => Sum.inl j) with hg
  set B' : Set ((Fin k ⊕ Fin 1) → ℝ) :=
    (fun v : (Fin k ⊕ Fin 1) → ℝ => v ∘ g) ⁻¹' PBnd Y with hB'
  have hB'd : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B' := by
    rw [hB']
    exact hB.preimage_comp g
  obtain ⟨φ, hφ⟩ := Set.empty_definable_iff.mp hB'd
  obtain ⟨N, hN⟩ := exists_alt_bound hOM φ
  refine ⟨N, PBnd Y, hB, ?_, ?_⟩
  · -- uniform finiteness of the fibres
    intro c
    have hYc : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Pfibre Y c) :=
      paramFibre_definable hY c
    have hfin : (MonoBnd (Pfibre Y c)).Finite := by
      obtain ⟨hDomD, hLAD, hHAD⟩ := monoDefinable_basic (Y := Pfibre Y c) hYc
      have hWD := monoDefinable_W (Y := Pfibre Y c) hYc
      obtain ⟨hLmD, hHmD, hLpD, hHpD⟩ := monoDefinable_germs (Y := Pfibre Y c) hYc
      exact monoBnd_finite hOM hDomD hWD hLmD hHmD hLpD hHpD
    have hS : {x : ℝ | Fin.cons x c ∈ PBnd Y} = MonoBnd (Pfibre Y c) := by
      ext x
      exact mem_PBnd_iff Y x c
    have hc : {t : ℝ | φ.Realize (Sum.elim c (fun _ : Fin 1 => t))} =
        {t : ℝ | Fin.cons t c ∈ PBnd Y} := by
      have hφ' : ∀ w : (Fin k ⊕ Fin 1) → ℝ, (w ∈ B' ↔ φ.Realize w) := by
        intro w
        rw [hφ]
        exact Iff.rfl
      have hcg : ∀ t : ℝ, (Sum.elim c (fun _ : Fin 1 => t)) ∘ g = Fin.cons t c := by
        intro t
        funext i
        induction i using Fin.cases with
        | zero => rfl
        | succ j => rfl
      ext t
      simp only [Set.mem_ofPred_eq]
      rw [← hφ' (Sum.elim c (fun _ : Fin 1 => t)), hB', Set.mem_preimage, hcg t]
    have hnc : ¬ AltChain N (MonoBnd (Pfibre Y c)) := by
      rw [← hS, ← hc]
      exact hN c
    rw [hS]
    exact encard_le_of_not_altChain hfin hnc
  · -- the three-point order condition off the exceptional set
    intro c a b hab havb x₁ x₂ x₃ y₁ y₂ y₃ hx₁ hx₂ hx₃ hlt₁ hlt₂ hy₁ hy₂ hy₃
    have hYc : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Pfibre Y c) :=
      paramFibre_definable hY c
    have hS : {x : ℝ | Fin.cons x c ∈ PBnd Y} = MonoBnd (Pfibre Y c) := by
      ext x
      exact mem_PBnd_iff Y x c
    have havb' : ∀ x ∈ Set.Ioo a b, x ∉ MonoBnd (Pfibre Y c) := by
      intro x hx hmem
      exact havb x hx ((Set.ext_iff.mp hS x).mpr hmem)
    have hy₁' : ![x₁, y₁] ∈ Pfibre Y c := by simpa [Pfibre] using hy₁
    have hy₂' : ![x₂, y₂] ∈ Pfibre Y c := by simpa [Pfibre] using hy₂
    have hy₃' : ![x₃, y₃] ∈ Pfibre Y c := by simpa [Pfibre] using hy₃
    rcases monoOn_main hYc (Pfibre_fun (Y := Y) hfun c) hOM hab havb' with hinc | hdec
    · have hinc' := (mem_MonoIncOn (Y := Pfibre Y c) (a := a) (b := b)).mp hinc
      exact Or.inl ⟨hinc' x₁ x₂ y₁ y₂ hx₁.1 hlt₁ hx₂.2 hy₁' hy₂',
        hinc' x₂ x₃ y₂ y₃ hx₂.1 hlt₂ hx₃.2 hy₂' hy₃'⟩
    · have hdec' := (mem_MonoDecOn (Y := Pfibre Y c) (a := a) (b := b)).mp hdec
      exact Or.inr ⟨hdec' x₂ x₃ y₂ y₃ hx₂.1 hlt₂ hx₃.2 hy₂' hy₃',
        hdec' x₁ x₂ y₁ y₂ hx₁.1 hlt₁ hx₂.2 hy₁' hy₂'⟩

end Work.WilC4
