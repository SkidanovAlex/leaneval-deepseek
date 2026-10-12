import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.BoseBoxFock.pairRowDirDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxSmoothAux` — infrastructure for `boxSmooth_fibres`

The predicate `BoxSmooth ℓ G` (of `pairRowDirDefs`) asks for a `C^∞` function agreeing with `G`
on the box squared `boxL ℓ × boxL ℓ`.  For the three fibres `pairG13`, `pairG23`, `pairG21` of
`pairRowGDefs` the state enters only through `CutSmooth`/`CutSmooth1` factors
(`Θ = 1_{abox}·Θ₀`, `A = 1_{boxL}·A₀`, `B = 1_{boxL}·B₀`), so on the box squared the fibre is the
**box-restricted integral of the "clean" integrand** built from `Θ₀`, `A₀`, `B₀`

    G'(w, y) = ∫_{x' ∈ box^n} ∫_{u ∈ box} (clean integrand)                     (`pairG13`),

a *parametric integral over a compact set*, which is `C^∞` by
`Commons.Analysis.Calculus.contDiff_setIntegral_isCompact` (or its `ℂ`-valued general form
`Work.BoseBoxFock.contDiff_setIntegral_compact_gen`).

This module collects the pieces shared by the three fibres:

* smoothness of the coordinate-insertion and coordinate-update maps
  (`contDiff_insertCoord_comp`, `contDiff_insertCoord2_comp`, `contDiff_update_comp`);
* the compact boxes `boxPiSet ℓ` and their basic API;
* the three clean integrands and their joint `C^∞`-regularity;
* the set-membership facts (which coordinates of the inserted/updated configuration lie in the
  box) used to compare the fibre with the box-restricted integral.

**Notation trap.**  In this file every smoothness order is written `(⊤ : ℕ∞)` — the *coercion* of
the top of `ℕ∞` into `ℕ∞ω`, i.e. `C^∞`.  A bare `⊤` in a `ContDiff ℝ ⊤ _` statement elaborates
instead to the top of `ℕ∞ω`, which is *analyticity* (`C^ω`) and is therefore **not** the same
statement (it cannot be fed with the `CutSmooth` data, whose order is `C^∞`).

`sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-! ## 1. Smoothness of the elementary configuration maps -/

/-- Complex conjugation is `C^∞`. -/
lemma contDiff_starC : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => star z) := by
  have h := (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff (n := (⊤ : ℕ∞))
  have heq : (⇑(RCLike.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ → ℂ) = fun z => star z := by
    ext z; simp only [RCLike.conjCLE_apply]; simp [RCLike.star_def]
  rwa [heq] at h

/-- Insertion of a smoothly varying value into a smoothly varying fibre is smooth. -/
lemma contDiff_insertCoord_comp {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {n : ℕ} (j : Fin n) {w : P → E3} {x' : P → ({k : Fin n // k ≠ j} → E3)}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hx' : ContDiff ℝ (⊤ : ℕ∞) x') :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => insertCoord j (w q) (x' q)) := by
  rw [contDiff_pi]
  intro k
  by_cases hk : k = j
  · subst hk
    have : (fun q => insertCoord k (w q) (x' q) k) = w := by
      funext q; simp [insertCoord]
    rw [this]; exact hw
  · have : (fun q => insertCoord j (w q) (x' q) k) = fun q => x' q ⟨k, hk⟩ := by
      funext q; simp [insertCoord, dif_neg hk]
    rw [this]
    exact (contDiff_apply ℝ E3 ⟨k, hk⟩).comp hx'

/-- Insertion of two smoothly varying values into a smoothly varying fibre is smooth. -/
lemma contDiff_insertCoord2_comp {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {n : ℕ} (p : Fin n × Fin n) {w₀ w₁ : P → E3}
    {x' : P → ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)}
    (h₀ : ContDiff ℝ (⊤ : ℕ∞) w₀) (h₁ : ContDiff ℝ (⊤ : ℕ∞) w₁) (hx' : ContDiff ℝ (⊤ : ℕ∞) x') :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => insertCoord2 p (w₀ q) (w₁ q) (x' q)) := by
  rw [contDiff_pi]
  intro k
  by_cases h1 : k = p.1
  · have : (fun q => insertCoord2 p (w₀ q) (w₁ q) (x' q) k) = w₀ := by
      funext q; simp only [insertCoord2_eq, dif_pos h1]
    rw [this]; exact h₀
  · by_cases h2 : k = p.2
    · have : (fun q => insertCoord2 p (w₀ q) (w₁ q) (x' q) k) = w₁ := by
        funext q; simp only [insertCoord2_eq, dif_neg h1, dif_pos h2]
      rw [this]; exact h₁
    · have : (fun q => insertCoord2 p (w₀ q) (w₁ q) (x' q) k) = fun q => x' q ⟨k, h1, h2⟩ := by
        funext q; simp only [insertCoord2_eq, dif_neg h1, dif_neg h2]
      rw [this]
      exact (contDiff_apply ℝ E3 ⟨k, h1, h2⟩).comp hx'

/-- A coordinate update of a smoothly varying configuration is smooth. -/
lemma contDiff_update_comp {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {n : ℕ} (j : Fin n) {f : P → (Fin n → E3)} {g : P → E3}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => Function.update (f q) j (g q)) := by
  rw [contDiff_pi]
  intro k
  by_cases hk : k = j
  · subst hk
    have : (fun q => Function.update (f q) k (g q) k) = g := by
      funext q; rw [Function.update_apply, if_pos rfl]
    rw [this]; exact hg
  · have : (fun q => Function.update (f q) j (g q) k) = fun q => f q k := by
      funext q; rw [Function.update_apply, if_neg hk]
    rw [this]; exact (contDiff_apply ℝ E3 k).comp hf

/-! ## 2. The compact boxes -/

/-- The `n`-fold box `∏_{i ∈ ι} boxL ℓ`, a compact subset of `ι → E3`. -/
def boxPiSet (ι : Type*) (ℓ : ℝ) : Set (ι → E3) :=
  Set.pi Set.univ fun _ => Work.BoseK15.corpusBox.boxL ℓ

lemma mem_boxPiSet {ι : Type*} {ℓ : ℝ} {x : ι → E3} :
    x ∈ boxPiSet ι ℓ ↔ ∀ k, x k ∈ Work.BoseK15.corpusBox.boxL ℓ := by
  simp [boxPiSet]

lemma isCompact_boxPiSet {ι : Type*} [Fintype ι] {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsCompact (boxPiSet ι ℓ) := by
  have h : boxPiSet ι ℓ = Set.pi Set.univ (fun _ : ι => Submission.BoseGases.acube ℓ) := by
    simp only [boxPiSet, corpusBox_boxL_eq_acube hℓ]
  rw [h]
  exact isCompact_univ_pi (fun _ => Submission.BoseGases.acube_compact hℓ)

/-! ## 3. The clean integrands and their regularity -/

/-- The clean integrand of `pairG13`: the state factors with the box indicators removed. -/
def clean13 {n : ℕ} (p : Fin n × Fin n) (Θ₀ : Xn n → ℂ) (A₀ B₀ : E3 → ℂ)
    (q : (E3 × E3) × (({k : Fin n // k ≠ p.2} → E3) × E3)) : ℂ :=
  star (Θ₀ (insertCoord p.2 q.1.1 q.2.1))
    * A₀ ((insertCoord p.2 q.1.1 q.2.1) p.1)
    * star (B₀ q.2.2)
    * Θ₀ (Function.update (Function.update (insertCoord p.2 q.1.1 q.2.1) p.1 q.1.2) p.2 q.2.2)

/-- The clean integrand of `pairG23`. -/
def clean23 {n : ℕ} (p : Fin n × Fin n) (Θ₀ : Xn n → ℂ) (A₀ B₀ : E3 → ℂ)
    (q : (E3 × E3) × (({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × E3 × E3)) : ℂ :=
  star (Θ₀ (insertCoord2 p q.1.1 q.1.2 q.2.1))
    * star (A₀ q.2.2.1)
    * star (B₀ q.2.2.2)
    * Θ₀ (Function.update (Function.update (insertCoord2 p q.1.1 q.1.2 q.2.1) p.1 q.2.2.1)
        p.2 q.2.2.2)

/-- The clean integrand of `pairG21` (the parameters are `(u, y)`, as in the definition). -/
def clean21 {n : ℕ} (p : Fin n × Fin n) (Θ₀ : Xn n → ℂ) (A₀ : E3 → ℂ)
    (q : (E3 × E3) × (Fin n → E3)) : ℂ :=
  star (Θ₀ q.2) * A₀ (q.2 p.1) * A₀ (q.2 p.2)
    * Θ₀ (Function.update (Function.update q.2 p.1 q.1.2) p.2 q.1.1)

lemma contDiff_clean13 {n : ℕ} (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ} {A₀ B₀ : E3 → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA₀ : ContDiff ℝ (⊤ : ℕ∞) A₀) (hB₀ : ContDiff ℝ (⊤ : ℕ∞) B₀) :
    ContDiff ℝ (⊤ : ℕ∞) (clean13 p Θ₀ A₀ B₀) := by
  have hw : ContDiff ℝ (⊤ : ℕ∞) (fun q : (E3 × E3) × (({k : Fin n // k ≠ p.2} → E3) × E3) => q.1.1) :=
    contDiff_fst.comp contDiff_fst
  have hx : ContDiff ℝ (⊤ : ℕ∞) (fun q : (E3 × E3) × (({k : Fin n // k ≠ p.2} → E3) × E3) => q.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hy : ContDiff ℝ (⊤ : ℕ∞) (fun q : (E3 × E3) × (({k : Fin n // k ≠ p.2} → E3) × E3) => q.1.2) :=
    contDiff_snd.comp contDiff_fst
  have hu : ContDiff ℝ (⊤ : ℕ∞) (fun q : (E3 × E3) × (({k : Fin n // k ≠ p.2} → E3) × E3) => q.2.2) :=
    contDiff_snd.comp contDiff_snd
  have hα : ContDiff ℝ (⊤ : ℕ∞) (fun q : (E3 × E3) × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
      insertCoord p.2 q.1.1 q.2.1) := contDiff_insertCoord_comp p.2 hw hx
  have hβ : ContDiff ℝ (⊤ : ℕ∞) (fun q : (E3 × E3) × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
      Function.update (Function.update (insertCoord p.2 q.1.1 q.2.1) p.1 q.1.2) p.2 q.2.2) :=
    contDiff_update_comp p.2 (contDiff_update_comp p.1 hα hy) hu
  exact (((contDiff_starC.comp (hΘ₀.comp hα)).mul
    (hA₀.comp ((contDiff_pi.mp hα) p.1))).mul
    (contDiff_starC.comp (hB₀.comp hu))).mul (hΘ₀.comp hβ)

lemma contDiff_clean23 {n : ℕ} (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ} {A₀ B₀ : E3 → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA₀ : ContDiff ℝ (⊤ : ℕ∞) A₀) (hB₀ : ContDiff ℝ (⊤ : ℕ∞) B₀) :
    ContDiff ℝ (⊤ : ℕ∞) (clean23 p Θ₀ A₀ B₀) := by
  have hw₀ : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (E3 × E3) × (({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × E3 × E3) => q.1.1) :=
    contDiff_fst.comp contDiff_fst
  have hw₁ : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (E3 × E3) × (({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × E3 × E3) => q.1.2) :=
    contDiff_snd.comp contDiff_fst
  have hx : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (E3 × E3) × (({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × E3 × E3) => q.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hy : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (E3 × E3) × (({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × E3 × E3) => q.2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
  have hu : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (E3 × E3) × (({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × E3 × E3) => q.2.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp contDiff_snd)
  have hα : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (E3 × E3) × (({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × E3 × E3) =>
        insertCoord2 p q.1.1 q.1.2 q.2.1) := contDiff_insertCoord2_comp p hw₀ hw₁ hx
  have hβ : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (E3 × E3) × (({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × E3 × E3) =>
        Function.update (Function.update (insertCoord2 p q.1.1 q.1.2 q.2.1) p.1 q.2.2.1)
          p.2 q.2.2.2) :=
    contDiff_update_comp p.2 (contDiff_update_comp p.1 hα hy) hu
  exact (((contDiff_starC.comp (hΘ₀.comp hα)).mul
    (contDiff_starC.comp (hA₀.comp hy))).mul
    (contDiff_starC.comp (hB₀.comp hu))).mul (hΘ₀.comp hβ)

lemma contDiff_clean21 {n : ℕ} (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ} {A₀ : E3 → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA₀ : ContDiff ℝ (⊤ : ℕ∞) A₀) :
    ContDiff ℝ (⊤ : ℕ∞) (clean21 p Θ₀ A₀) := by
  have hx : ContDiff ℝ (⊤ : ℕ∞) (fun q : (E3 × E3) × (Fin n → E3) => q.2) := contDiff_snd
  have hu : ContDiff ℝ (⊤ : ℕ∞) (fun q : (E3 × E3) × (Fin n → E3) => q.1.1) :=
    contDiff_fst.comp contDiff_fst
  have hy : ContDiff ℝ (⊤ : ℕ∞) (fun q : (E3 × E3) × (Fin n → E3) => q.1.2) :=
    contDiff_snd.comp contDiff_fst
  have hβ : ContDiff ℝ (⊤ : ℕ∞) (fun q : (E3 × E3) × (Fin n → E3) =>
      Function.update (Function.update q.2 p.1 q.1.2) p.2 q.1.1) :=
    contDiff_update_comp p.2 (contDiff_update_comp p.1 hx hy) hu
  exact (((contDiff_starC.comp (hΘ₀.comp hx)).mul
    (hA₀.comp ((contDiff_pi.mp hx) p.1))).mul
    (hA₀.comp ((contDiff_pi.mp hx) p.2))).mul (hΘ₀.comp hβ)

/-! ## 4. Membership of the inserted / updated configurations in the boxes -/

/-- For `w` in the box, the configuration `insertCoord j w x'` lies in `abox n ℓ` exactly when
`x'` is in the `j`-fold box. -/
lemma insertCoord_mem_abox_iff {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {j : Fin n} {w : E3}
    (hw : w ∈ Work.BoseK15.corpusBox.boxL ℓ) (x' : {k : Fin n // k ≠ j} → E3) :
    insertCoord j w x' ∈ Submission.BoseGases.abox n ℓ ↔ x' ∈ boxPiSet _ ℓ := by
  rw [mem_boxPiSet, Submission.BoseGases.mem_abox_iff,
    ← corpusBox_boxL_eq_acube hℓ]
  constructor
  · intro h k
    have h1 := h k.1
    simpa only [insertCoord_eq, dif_neg k.2] using h1
  · intro h i
    by_cases hi : i = j
    · simpa only [insertCoord_eq, dif_pos hi] using hw
    · simpa only [insertCoord_eq, dif_neg hi] using h ⟨i, hi⟩

/-- For `w` in the box and `x'` in the `j`-fold box, all coordinates of `insertCoord j w x'`
are in the box. -/
lemma insertCoord_apply_mem_boxL {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {j i : Fin n} (hij : i ≠ j)
    {w : E3} (hw : w ∈ Work.BoseK15.corpusBox.boxL ℓ) {x' : {k : Fin n // k ≠ j} → E3}
    (hx : x' ∈ boxPiSet _ ℓ) : (insertCoord j w x') i ∈ Work.BoseK15.corpusBox.boxL ℓ := by
  simpa only [insertCoord_eq, dif_neg hij] using (mem_boxPiSet.mp hx) ⟨i, hij⟩

/-- The updated configuration of `pairG13` lies in `abox n ℓ`. -/
lemma upd13_mem_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {w y u : E3} (hw : w ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (hy : y ∈ Work.BoseK15.corpusBox.boxL ℓ) (hu : u ∈ Work.BoseK15.corpusBox.boxL ℓ)
    {x' : {k : Fin n // k ≠ p.2} → E3} (hx : x' ∈ boxPiSet _ ℓ) :
    Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u
      ∈ Submission.BoseGases.abox n ℓ := by
  rw [Submission.BoseGases.mem_abox_iff, ← corpusBox_boxL_eq_acube hℓ]
  intro i
  rw [Function.update_apply]
  by_cases hi2 : i = p.2
  · rw [if_pos hi2]; exact hu
  · rw [if_neg hi2, Function.update_apply]
    by_cases hi1 : i = p.1
    · rw [if_pos hi1]; exact hy
    · rw [if_neg hi1]
      simpa only [insertCoord_eq, dif_neg hi2] using (mem_boxPiSet.mp hx) ⟨i, hi2⟩

/-- For `w₀, w₁` in the box, the configuration `insertCoord2 p w₀ w₁ x'` lies in `abox n ℓ`
exactly when `x'` is in the two-fold box. -/
lemma insertCoord2_mem_abox_iff {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    {w₀ w₁ : E3} (h₀ : w₀ ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (h₁ : w₁ ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) :
    insertCoord2 p w₀ w₁ x' ∈ Submission.BoseGases.abox n ℓ ↔ x' ∈ boxPiSet _ ℓ := by
  rw [mem_boxPiSet, Submission.BoseGases.mem_abox_iff, ← corpusBox_boxL_eq_acube hℓ]
  constructor
  · intro h k
    have h1 := h k.1
    simpa only [insertCoord2_eq, dif_neg k.2.1, dif_neg k.2.2] using h1
  · intro h i
    by_cases hi1 : i = p.1
    · simpa only [insertCoord2_eq, dif_pos hi1] using h₀
    · by_cases hi2 : i = p.2
      · simpa only [insertCoord2_eq, dif_neg hi1, dif_pos hi2] using h₁
      · simpa only [insertCoord2_eq, dif_neg hi1, dif_neg hi2] using h ⟨i, hi1, hi2⟩

/-- The updated configuration of `pairG23` lies in `abox n ℓ`. -/
lemma upd23_mem_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    {w₀ w₁ y u : E3} (h₀ : w₀ ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (h₁ : w₁ ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (hy : y ∈ Work.BoseK15.corpusBox.boxL ℓ) (hu : u ∈ Work.BoseK15.corpusBox.boxL ℓ)
    {x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3} (hx : x' ∈ boxPiSet _ ℓ) :
    Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u
      ∈ Submission.BoseGases.abox n ℓ := by
  rw [Submission.BoseGases.mem_abox_iff, ← corpusBox_boxL_eq_acube hℓ]
  intro i
  rw [Function.update_apply]
  by_cases hi2 : i = p.2
  · rw [if_pos hi2]; exact hu
  · rw [if_neg hi2, Function.update_apply]
    by_cases hi1 : i = p.1
    · rw [if_pos hi1]; exact hy
    · rw [if_neg hi1]
      simpa only [insertCoord2_eq, dif_neg hi1, dif_neg hi2] using (mem_boxPiSet.mp hx) ⟨i, hi1, hi2⟩

/-- For `x` in the full box and `y`, `u` in the box, the updated configuration of `pairG21`
lies in `abox n ℓ`. -/
lemma upd21_mem_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    {y u : E3} (hy : y ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (hu : u ∈ Work.BoseK15.corpusBox.boxL ℓ) {x : Fin n → E3}
    (hx : x ∈ boxPiSet _ ℓ) :
    Function.update (Function.update x p.1 y) p.2 u ∈ Submission.BoseGases.abox n ℓ := by
  rw [Submission.BoseGases.mem_abox_iff, ← corpusBox_boxL_eq_acube hℓ]
  intro i
  rw [Function.update_apply]
  by_cases hi2 : i = p.2
  · rw [if_pos hi2]; exact hu
  · rw [if_neg hi2, Function.update_apply]
    by_cases hi1 : i = p.1
    · rw [if_pos hi1]; exact hy
    · rw [if_neg hi1]
      exact (mem_boxPiSet.mp hx) i

/-- For `x` in the full box and `y` in the box, `(x[p.1 ↦ y]) p.1` is in the box. -/
lemma upd21_apply_mem_boxL {n : ℕ} {ℓ : ℝ} {p : Fin n × Fin n} {y : E3}
    (hy : y ∈ Work.BoseK15.corpusBox.boxL ℓ) (x : Fin n → E3) :
    Function.update x p.1 y p.1 ∈ Work.BoseK15.corpusBox.boxL ℓ := by
  rw [Function.update_apply, if_pos rfl]; exact hy

end Work.BoseBoxFock
