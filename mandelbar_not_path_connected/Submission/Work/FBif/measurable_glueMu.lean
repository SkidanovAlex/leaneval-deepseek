/-
Copyright: subproject `Submission/Work/FBif/` of `mandelbar_not_path_connected`.

# Measurability of `pullIter` and of the invariant coefficient `glueMu`

The glued map `F` is Borel measurable (it is a `C¹` map in the applications), and the pull-back
coefficient of a measurable coefficient is measurable:

`pullRev ν F z = (star (∂F z) + star (ν (F z)) · ∂̄F z) / (star (∂̄F z) + star (ν (F z)) · ∂F z)`

is a measurable function of `z` as soon as `ν` and `F` are measurable: the Wirtinger derivatives
`∂F`, `∂̄F` are always measurable (`Work.MRMT.QC.measurable_dz`, `measurable_dzbar`), `ν ∘ F` is
measurable, and all the operations involved (star, `+`, `*`, `/`) preserve measurability.
Consequently every `pullIter F n` (the `n`-fold pull-back of `0`) is measurable.

For `glueMu` the point is the *first hitting time* of the far region `{‖z‖ ≥ R}`: the coefficient
is the pull-back of `0` along `n z` steps, where `n z` is a `Nat.find`, so its measurability is
not immediate.  We prove that all level sets of the first hitting time
`hitTime F R z = Nat.find (…)` are Borel:
* `hitTime F R z = 0` iff the orbit never reaches `{‖z‖ ≥ R}` or `R ≤ ‖z‖`;
* `hitTime F R z = k + 1` iff `R ≤ ‖F^[k+1] z‖` and `R > ‖F^[j] z‖` for all `j < k + 1`.
Hence `hitTime F R` is measurable, and `(n, z) ↦ pullIter F n z` is jointly measurable because
`ℕ` is countable and each `pullIter F n` is measurable.  Composing with `z ↦ (z, hitTime F R z)`
and using `glueMu F R z = pullIter F (hitTime F R z) z` we obtain the measurability of `glueMu`.
-/
import Mathlib
import Submission.Work.FBif.Glue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function MeasureTheory

noncomputable section

namespace Work.FBif

/-! ## Measurability of the pull-back coefficient and of `pullIter` -/

/-- The pull-back coefficient `pullRev ν F` is measurable as soon as `ν` and `F` are. -/
lemma measurable_pullRev {F ν : ℂ → ℂ} (hF : Measurable F) (hν : Measurable ν) :
    Measurable (fun z : ℂ => Work.MRMT.Found.pullRev ν F z) := by
  have hdz : Measurable (fun z : ℂ => Work.MRMT.dz F z) := Work.MRMT.QC.measurable_dz F
  have hdzb : Measurable (fun z : ℂ => Work.MRMT.dzbar F z) :=
    Work.MRMT.QC.measurable_dzbar F
  have hcomp : Measurable (fun z : ℂ => ν (F z)) := hν.comp hF
  have hnum : Measurable (fun z : ℂ =>
      star (Work.MRMT.dz F z) + star (ν (F z)) * Work.MRMT.dzbar F z) :=
    (continuous_star.measurable.comp hdz).add
      ((continuous_star.measurable.comp hcomp).mul hdzb)
  have hden : Measurable (fun z : ℂ =>
      star (Work.MRMT.dzbar F z) + star (ν (F z)) * Work.MRMT.dz F z) :=
    (continuous_star.measurable.comp hdzb).add
      ((continuous_star.measurable.comp hcomp).mul hdz)
  have hfun : (fun z : ℂ => Work.MRMT.Found.pullRev ν F z) =
      ((fun z : ℂ => star (Work.MRMT.dz F z) + star (ν (F z)) * Work.MRMT.dzbar F z) /
       (fun z : ℂ => star (Work.MRMT.dzbar F z) + star (ν (F z)) * Work.MRMT.dz F z)) := by
    funext z
    simp only [Work.MRMT.Found.pullRev, Pi.div_apply]
  rw [hfun]
  exact hnum.div hden

/-- Every `pullIter F n` is measurable when `F` is. -/
lemma measurable_pullIter {F : ℂ → ℂ} (hF : Measurable F) (n : ℕ) :
    Measurable (pullIter F n) := by
  induction n with
  | zero =>
      rw [show pullIter F 0 = fun _ : ℂ => (0 : ℂ) from by rw [pullIter]; rfl]
      exact measurable_const
  | succ n ih =>
      rw [show pullIter F (n + 1) =
          fun z : ℂ => Work.MRMT.Found.pullRev (pullIter F n) F z from by
        rw [pullIter, Function.iterate_succ_apply']; rfl]
      exact measurable_pullRev hF ih

/-! ## The first hitting time of the far region -/

/-- The first hitting time is `0` exactly when the orbit never enters the far region, or when
`z` itself is already in the far region. -/
lemma hitTime_eq_zero_iff {F : ℂ → ℂ} {R : ℝ} {z : ℂ} :
    hitTime F R z = 0 ↔ (¬ ∃ m : ℕ, R ≤ ‖(F^[m]) z‖) ∨ R ≤ ‖z‖ := by
  constructor
  · intro h
    by_cases hz : ∃ m : ℕ, R ≤ ‖(F^[m]) z‖
    · right
      have h0 : Nat.find hz = 0 := by simpa only [hitTime, dite_eq_left hz] using h
      have := (Nat.find_eq_zero hz).mp h0
      simpa using this
    · left; exact hz
  · intro h
    rcases h with h | h
    · simp only [hitTime, dite_eq_right h]
    · have hz : ∃ m : ℕ, R ≤ ‖(F^[m]) z‖ := ⟨0, by simpa using h⟩
      simp only [hitTime, dite_eq_left hz]
      exact (Nat.find_eq_zero hz).mpr (by simpa using h)

/-- The first hitting time equals `k + 1` exactly when time `k + 1` is a hitting time and all
earlier times are not. -/
lemma hitTime_eq_succ_iff {F : ℂ → ℂ} {R : ℝ} {z : ℂ} {k : ℕ} :
    hitTime F R z = k + 1 ↔
      R ≤ ‖(F^[k + 1]) z‖ ∧ ∀ j : ℕ, j < k + 1 → ¬ R ≤ ‖(F^[j]) z‖ := by
  constructor
  · intro h
    have hz : ∃ m : ℕ, R ≤ ‖(F^[m]) z‖ := by
      by_contra hc
      rw [hitTime, dite_eq_right hc] at h
      exact Nat.succ_ne_zero k h.symm
    have hfind : Nat.find hz = k + 1 := by
      rw [hitTime, dite_eq_left hz] at h; exact h
    constructor
    · have hspec := Nat.find_spec hz
      rwa [hfind] at hspec
    · intro j hj
      exact Nat.find_min hz (by rw [hfind]; exact hj)
  · intro h1
    obtain ⟨h1, h2⟩ := h1
    have hz : ∃ m : ℕ, R ≤ ‖(F^[m]) z‖ := ⟨k + 1, h1⟩
    rw [hitTime, dite_eq_left hz]
    exact (Nat.find_eq_iff hz).mpr ⟨h1, fun n hn => h2 n hn⟩

/-- Every level set of the first hitting time of the far region is Borel. -/
lemma measurableSet_hitTime_eq {F : ℂ → ℂ} (hF : Measurable F) (R : ℝ) (n : ℕ) :
    MeasurableSet {z : ℂ | hitTime F R z = n} := by
  have hC : ∀ k : ℕ, MeasurableSet {z : ℂ | R ≤ ‖(F^[k]) z‖} := fun k =>
    measurableSet_le measurable_const (continuous_norm.measurable.comp (hF.iterate k))
  rcases n with _ | k
  · have h1 : MeasurableSet {z : ℂ | ¬ ∃ m : ℕ, R ≤ ‖(F^[m]) z‖} := by
      rw [show {z : ℂ | ¬ ∃ m : ℕ, R ≤ ‖(F^[m]) z‖}
          = (⋃ m, {z : ℂ | R ≤ ‖(F^[m]) z‖})ᶜ from by
        ext z; simp]
      exact (MeasurableSet.iUnion fun m => hC m).compl
    have hset : {z : ℂ | hitTime F R z = 0} =
        {z : ℂ | ¬ ∃ m : ℕ, R ≤ ‖(F^[m]) z‖} ∪ {z : ℂ | R ≤ ‖z‖} := by
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_union]; exact hitTime_eq_zero_iff
    rw [hset]
    exact h1.union (measurableSet_le measurable_const continuous_norm.measurable)
  · have h2 : MeasurableSet {z : ℂ | ∀ j : ℕ, j < k + 1 → ¬ R ≤ ‖(F^[j]) z‖} := by
      rw [show {z : ℂ | ∀ j : ℕ, j < k + 1 → ¬ R ≤ ‖(F^[j]) z‖}
          = ⋂ j, ⋂ (_ : j < k + 1), ({z : ℂ | R ≤ ‖(F^[j]) z‖})ᶜ from by
        ext z; simp [Set.mem_iInter]]
      exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hC j).compl
    have hset : {z : ℂ | hitTime F R z = k + 1} =
        {z : ℂ | R ≤ ‖(F^[k + 1]) z‖} ∩
          {z : ℂ | ∀ j : ℕ, j < k + 1 → ¬ R ≤ ‖(F^[j]) z‖} := by
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]; exact hitTime_eq_succ_iff
    rw [hset]
    exact (hC (k + 1)).inter h2

/-- The first hitting time of the far region is measurable. -/
lemma measurable_hitTime {F : ℂ → ℂ} (hF : Measurable F) (R : ℝ) :
    Measurable (hitTime F R) :=
  measurable_to_nat fun z => measurableSet_hitTime_eq hF R (hitTime F R z)

/-- `glueMu` is the pull-back of `0` along `hitTime F R z` steps. -/
lemma glueMu_eq_pullIter_hitTime (F : ℂ → ℂ) (R : ℝ) (z : ℂ) :
    glueMu F R z = pullIter F (hitTime F R z) z := by
  by_cases h : ∃ n : ℕ, R ≤ ‖(F^[n]) z‖
  · simp only [glueMu, hitTime, dite_eq_left h]
  · simp only [glueMu, hitTime, dite_eq_right h, pullIter, Function.iterate_zero_apply]
    rfl

/-! ## The main statement -/

set_option linter.unusedVariables false in
theorem measurable_glueMu {F : ℂ → ℂ} (hF : Measurable F)
    (hdz : Measurable (fun z : ℂ => Work.MRMT.dz F z))
    (hdzb : Measurable (fun z : ℂ => Work.MRMT.dzbar F z)) (R : ℝ) :
    (∀ n : ℕ, Measurable (Work.FBif.pullIter F n)) ∧ Measurable (Work.FBif.glueMu F R) := by
  refine ⟨fun n => measurable_pullIter hF n, ?_⟩
  have hhit : Measurable (hitTime F R) := measurable_hitTime hF R
  have hpair : Measurable (fun z : ℂ => (z, hitTime F R z)) := measurable_id.prodMk hhit
  have hG : Measurable (fun p : ℂ × ℕ => pullIter F p.2 p.1) :=
    measurable_from_prod_countable_left fun n => measurable_pullIter hF n
  have hcomp := hG.comp hpair
  have heq : ((fun p : ℂ × ℕ => pullIter F p.2 p.1) ∘ fun z : ℂ => (z, hitTime F R z))
      = glueMu F R := by
    funext z; simp only [Function.comp_apply]
    exact (glueMu_eq_pullIter_hitTime F R z).symm
  rwa [heq] at hcomp

end Work.FBif

end
