import Mathlib
import Submission.Work.ANALYTIC.CechPt.DualCechSetup
import Submission.Work.ANALYTIC.CechPt.diff_comp_diff

/-!
# Exactness of the dual Čech complex of the Cantor cover

`DualC p = LocallyConstant ↥(cechTerm p) ℤ` is the group of locally constant `ℤ`-valued functions
on the `p`-th term of the Čech nerve of the binary expansion, `dualD p` is the alternating sum of
the pullbacks along the face maps `cechFace p i`, and `dualAug` is the augmentation
"constant function `1`" (`DualCechSetup`).  This module proves that the augmented complex

`0 ⟶ ℤ ⟶ C(C_0,ℤ) ⟶ C(C_1,ℤ) ⟶ ⋯`

is exact, i.e. `range dualAug = ker (dualD 0)` and `range (dualD p) = ker (dualD (p+1))` for all
`p`.

The route is the level model: `cechTerm p` is the inverse limit of the finite dyadic nerves
`Level.lev (2^(n+1)) p` along the projections `lvlOf p n`
(`CechPt.cechTermLevelProjections`), every locally constant function factors through some level
(`exists_factor_lvlOf`), the level projections are surjective, and `lvlOf` commutes with the face
maps (`lvlOf_cechFace`).  Hence `dualD` is `Level.diff` after transporting a level function along
`lvlOf`, and the exactness of the dual complex reduces to the exactness of the level complex
`(Level.lev M • → ℤ, Level.diff)`, which is `level_acyclic` (in positive degrees) together with
`Level.diff ∘ Level.diff = 0` (`CechPt.diff_comp_diff`).
-/

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option linter.style.haveILetI false

namespace Work.ANALYTIC.CechPt

/-- The element of the dual Čech complex induced by a function on the level-`n` model: the
composition `F ∘ lvlOf p n` is locally constant because `lvlOf p n` is. -/
def lcOfLev (p n : ℕ) (F : Level.lev (2 ^ (n + 1)) p → ℤ) : DualC p :=
  ⟨F ∘ lvlOf p n, (isLocallyConstant_lvlOf p n).comp F⟩

@[simp]
theorem lcOfLev_apply (p n : ℕ) (F : Level.lev (2 ^ (n + 1)) p → ℤ)
    (x : ↥(cechTerm p)) : lcOfLev p n F x = F (lvlOf p n x) := rfl

/-- The zero function on a level model induces the zero element of the dual complex. -/
theorem lcOfLev_zero (p n : ℕ) :
    lcOfLev p n (fun _ : Level.lev (2 ^ (n + 1)) p => (0 : ℤ)) = 0 := by
  apply LocallyConstant.ext
  intro x
  simp

/-- The augmentation is the constant level-`n` function with value `c`. -/
theorem dualAug_eq_lcOfLev (n : ℕ) (c : ℤ) :
    dualAug c = lcOfLev 0 n (fun _ : Level.lev (2 ^ (n + 1)) 0 => c) := by
  apply LocallyConstant.ext
  intro x
  simp

/-- The key computation: on level-`n` functions the dual Čech differential is the level
differential `Level.diff`. -/
theorem dualD_lcOfLev (p n : ℕ) (F : Level.lev (2 ^ (n + 1)) p → ℤ) :
    dualD p (lcOfLev p n F) = lcOfLev (p + 1) n (Level.diff F) := by
  apply LocallyConstant.ext
  intro x
  rw [dualD_apply]
  simp only [lcOfLev_apply, Level.diff, lvlOf_cechFace]

/-- Every element of the dual Čech complex is induced by a function on a level model. -/
theorem exists_lcOfLev (p : ℕ) (f : DualC p) :
    ∃ (n : ℕ) (F : Level.lev (2 ^ (n + 1)) p → ℤ), f = lcOfLev p n F := by
  obtain ⟨n, F, hF⟩ := exists_factor_lvlOf p f.1 f.2
  refine ⟨n, F, LocallyConstant.ext fun x => ?_⟩
  show f.1 x = F (lvlOf p n x)
  rw [hF]
  rfl

/-- If the differential of a level-`n` function vanishes, then the level function is a level
cycle. -/
theorem diff_eq_zero_of_dualD_eq_zero (q n : ℕ) (F : Level.lev (2 ^ (n + 1)) q → ℤ)
    (h : dualD q (lcOfLev q n F) = 0) : Level.diff F = 0 := by
  have h0 : lcOfLev (q + 1) n (Level.diff F) = 0 := by
    rw [← dualD_lcOfLev q n F]; exact h
  funext w
  obtain ⟨z, rfl⟩ := lvlOf_surjective (q + 1) n w
  have hz := congrArg (fun (g : DualC (q + 1)) => g z) h0
  simpa using hz

/-- **The dual Čech differential squares to zero.** -/
theorem dualD_comp_dualD (p : ℕ) (f : DualC p) : dualD (p + 1) (dualD p f) = 0 := by
  obtain ⟨n, F, hf⟩ := exists_lcOfLev p f
  rw [hf, dualD_lcOfLev p n F, dualD_lcOfLev (p + 1) n (Level.diff F), diff_comp_diff]
  exact lcOfLev_zero (p + 2) n

/-- **Exactness of the augmented dual Čech complex of the Cantor cover.** -/
theorem dualCech_exact :
    (LinearMap.range Work.ANALYTIC.CechPt.dualAug = LinearMap.ker (Work.ANALYTIC.CechPt.dualD 0)) ∧
    (∀ p : ℕ, LinearMap.range (Work.ANALYTIC.CechPt.dualD p)
      = LinearMap.ker (Work.ANALYTIC.CechPt.dualD (p + 1))) := by
  constructor
  · refine le_antisymm ?_ ?_
    · intro k hk
      rw [LinearMap.mem_range] at hk
      obtain ⟨c, rfl⟩ := hk
      rw [LinearMap.mem_ker]
      apply LocallyConstant.ext
      intro x
      rw [dualD_apply]
      simp [dualAug_apply, Fin.sum_univ_two]
    · intro f hf
      rw [LinearMap.mem_ker] at hf
      obtain ⟨n, F, hF⟩ := exists_lcOfLev 0 f
      have hdiff : Level.diff F = 0 := diff_eq_zero_of_dualD_eq_zero 0 n F (by rw [← hF]; exact hf)
      obtain ⟨c, hc⟩ := (level_acyclic (2 ^ (n + 1))).2 F hdiff
      refine LinearMap.mem_range.mpr ⟨c, ?_⟩
      rw [dualAug_eq_lcOfLev n c, hF, ← hc]
  · intro p
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [LinearMap.mem_range] at hx
      obtain ⟨y, rfl⟩ := hx
      rw [LinearMap.mem_ker]
      exact dualD_comp_dualD p y
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      obtain ⟨n, F, hF⟩ := exists_lcOfLev (p + 1) x
      have hdiff : Level.diff F = 0 :=
        diff_eq_zero_of_dualD_eq_zero (p + 1) n F (by rw [← hF]; exact hx)
      obtain ⟨G, hG⟩ := (level_acyclic (2 ^ (n + 1))).1 p F hdiff
      refine LinearMap.mem_range.mpr ⟨lcOfLev p n G, ?_⟩
      rw [dualD_lcOfLev p n G, hG, hF]

end Work.ANALYTIC.CechPt
