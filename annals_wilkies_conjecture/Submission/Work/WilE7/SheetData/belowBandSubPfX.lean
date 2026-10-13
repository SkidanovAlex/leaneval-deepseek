/-
  `Work.WilE7.SheetData.belowBandSubPfX`: the *open below band* of the `i`-th sheet of a fibre of
  a semi-Pfaffian set is sub-Pfaffian.

  The data: a restricted semi-Pfaffian set `X ⊆ ℝ^{p+(m+1)}`, a sub-Pfaffian base region
  `C ⊆ ℝ^p`, and `k` sheets `s j : C → ℝ^{m+1}` whose graphs over `C` are exactly the fibre of
  `X` (`hsub` + `hcov`), pairwise distinct (`hinj`), with levels `j ↦ (s j x) (Fin.last m)`
  non-decreasing in `j` (`hmono`).  The claim is that for every `i : Fin k` the region

      Bᵢ = {y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
              y (Fin.last p) < (s i (Fin.init y)) (Fin.last m)}

  is sub-Pfaffian (`WilkiesDesign.E.SubPf (p+1) Bᵢ`).

  ## The mathematics

  For `x ∈ C` the fibre of `X.set` over `x` is exactly the `k`-element set `{s j x}`
  (`fiber_eq_range_sheets`), and since the levels are non-decreasing in `j`, the level
  `L i = (s i x) (Fin.last m)` is the `(i+1)`-st smallest of the `k` levels, counted with
  multiplicity.  Hence

      `t < L i`  ⟺  at least `k - i` of the fibre points have level `> t`
                 ⟺  there are `k - i` pairwise *distinct* points of the fibre above `t`.

  The counting direction is `lt_level_of_levelsAbove` (an injective `σ : Fin (k - i) → Fin k`
  all of whose levels exceed `t` forces `L i > t`), and it is here that the hypothesis `hmono`
  enters: it must be `Monotone` and **not** `StrictMono`, because two sheets of one stratum may
  well share their level (the "duplicate-level obstruction", see `BelowLevelX`).

  The set of levels below which `k - i` pairwise distinct fibre points lie is presented as a
  single semi-Pfaffian set by `BelowLevelX.belowLevelZ` — the mirror image of
  `AboveAux.aboveLevel_subPf` — whose projection is `BelowLevelX.belowLevelSet`
  (`belowLevelPresent`), and `belowLevelSet` is identified with `Bᵢ` in the two inclusions
  `band_subset_belowLevel` and `belowLevel_subset_band` below.
-/
import Mathlib
import Submission.Work.WilE7.SheetData.DefsX
import Submission.Work.WilE7.SheetData._incl_dev
import Submission.Work.WilE7.SheetData.NonstrictLevelFibre
import Submission.Work.WilE7.AboveAux.aboveLevel_subPf
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.SemiPfInter
import Submission.Work.WilE7.subPf_algebra
import Submission.Work.WilE7.SheetData.BelowLevelX
import Submission.Work.WilE7.SheetData.lt_level_of_levelsAbove
import Submission.Work.WilE7.SheetData.belowLevelPresent

set_option autoImplicit false
-- some of the sheet-data hypotheses are carried uniformly through the auxilliary lemmas below
-- although an individual lemma does not consume all of them
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilE7.SheetData

open WilkiesConjecture WilkiesDesign WilkiesDesign.E
open Work.WilE7.AboveAux

/-! ## §1. The band below the `i`-th sheet -/

/-- The open band strictly below the sheet `s i` over the base region `C`. -/
def bandSetX (p m : ℕ) (C : Set (Fin p → ℝ))
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (i : Fin k) :
    Set (Fin (p + 1) → ℝ) :=
  {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
    y (Fin.last p) < (s i (Fin.init y)) (Fin.last m)}

/-! ## §2. Index shifts -/

/-- The index `i.val + l.val` of `Fin k`, for `l : Fin (k - i.val)`. -/
def shiftIdx {k : ℕ} (i : Fin k) (l : Fin (k - i.val)) : Fin k :=
  ⟨i.val + l.val, by have := l.isLt; have := i.isLt; omega⟩

@[simp] theorem shiftIdx_val {k : ℕ} (i : Fin k) (l : Fin (k - i.val)) :
    (shiftIdx i l).val = i.val + l.val := rfl

theorem shiftIdx_injective {k : ℕ} (i : Fin k) : Function.Injective (shiftIdx i) := by
  intro a b hab
  apply Fin.ext
  have h2 : (shiftIdx i a).val = (shiftIdx i b).val := congrArg Fin.val hab
  simp only [shiftIdx_val] at h2
  omega

theorem le_shiftIdx {k : ℕ} (i : Fin k) (l : Fin (k - i.val)) : i ≤ shiftIdx i l := by
  rw [Fin.le_iff_val_le_val]
  simp [shiftIdx_val]

/-! ## §3. Elementary coordinate facts -/

/-- Gluing the two projections of a point of `ℝ^{p+q}` gives the point back. -/
theorem append_projFirst_projSndX {p q : ℕ} (z : Fin (p + q) → ℝ) :
    Fin.append (projFirst p q z) (projSnd p q z) = z := by
  funext i
  exact Fin.addCases (motive := fun i => Fin.append (projFirst p q z) (projSnd p q z) i = z i)
    (fun i => by rw [Fin.append_left]; rfl)
    (fun i => by rw [Fin.append_right]; rfl) i

/-- The projection of a point of a semi-Pfaffian set lies in the cube. -/
theorem mem_cubeC_of_mem_projFirst {p M : ℕ} (XC : SemiPf (p + M)) {z : Fin (p + M) → ℝ}
    (hz : z ∈ XC.set) : projFirst p M z ∈ cubeC p :=
  fun a => mem_cubeC_of_mem_set XC hz (Fin.castAdd M a)

/-- The base region `C = π (XC)` is contained in the cube. -/
theorem mem_cubeC_of_mem_base {p M : ℕ} {XC : SemiPf (p + M)} {C : Set (Fin p → ℝ)}
    (hC : C = projFirst p M '' XC.set) {x : Fin p → ℝ} (hx : x ∈ C) : x ∈ cubeC p := by
  rw [hC] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  exact mem_cubeC_of_mem_projFirst XC hz

/-- Over `x ∈ C` the fibre of `X.set` is exactly the range of the sheets. -/
theorem fiber_eq_range_sheets {p m k : ℕ} {X : SemiPf (p + (m + 1))} {C : Set (Fin p → ℝ)}
    {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
    (hcov : ∀ z ∈ X.set, projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (projFirst p (m + 1) z) = projSnd p (m + 1) z)
    {x : Fin p → ℝ} (hx : x ∈ C) : fiber X.set x = Set.range (fun j : Fin k => s j x) := by
  have _ := hinj
  ext y
  constructor
  · intro hy
    obtain ⟨j, hj⟩ := hcov (Fin.append x y) hy (by rw [projFirst_append]; exact hx)
    refine ⟨j, ?_⟩
    rw [projFirst_append, projSnd_append] at hj
    exact hj
  · rintro ⟨j, rfl⟩
    exact hsub j x hx

/-! ## §4. The band is contained in the below-level set -/

/-- **The band below the `i`-th sheet consists of levels below which `k - i` distinct fibre
points lie.**  The `k - i` sheets `s i, s (i+1), …, s (k-1)` over `x` are pairwise distinct and
all of them have level `≥ L i > t`. -/
theorem band_subset_belowLevel (p m : ℕ) (X : SemiPf (p + (m + 1)))
    (C : Set (Fin p → ℝ)) (M : ℕ) (XC : SemiPf (p + M))
    (hC : C = projFirst p M '' XC.set)
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
    (hcov : ∀ z ∈ X.set, projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (projFirst p (m + 1) z) = projSnd p (m + 1) z)
    (hmono : ∀ x ∈ C, Monotone fun j : Fin k => (s j x) (Fin.last m))
    (i : Fin k) :
    bandSetX p m C k s i ⊆
      belowLevelSet p (m + 1) M (k - i.val) (Fin.last m) X XC := by
  have _ := hcov
  intro y hy
  obtain ⟨hxC, hgt, hlt⟩ := hy
  have hx_cube : Fin.init y ∈ cubeC p := mem_cubeC_of_mem_base hC hxC
  -- the level of the `i`-th sheet is bounded by `±1`
  have hmem_i := hsub i (Fin.init y) hxC
  have hlev_abs := mem_cubeC_of_mem_set X hmem_i (Fin.natAdd p (Fin.last m))
  rw [Fin.append_right] at hlev_abs
  have hlev_le : (s i (Fin.init y)) (Fin.last m) ≤ 1 := (abs_le.mp hlev_abs).2
  refine ⟨?_, ?_, hgt, lt_of_lt_of_le hlt hlev_le, ?_⟩
  · -- the target is in the cube
    intro a
    rcases Fin.eq_castSucc_or_eq_last a with ⟨ā, rfl⟩ | rfl
    · exact hx_cube ā
    · rw [abs_le]
      exact ⟨le_of_lt hgt, le_trans (le_of_lt hlt) hlev_le⟩
  · -- the base point is in the projection of `XC`
    rw [hC] at hxC
    obtain ⟨z, hz, hzy⟩ := hxC
    exact ⟨projSnd p M z, by rw [← hzy, append_projFirst_projSndX]; exact hz⟩
  · -- the `k - i.val` fibre points
    refine ⟨fun l => Fin.append (Fin.init y) (s (shiftIdx i l) (Fin.init y)),
      ?_, ?_, ?_, ?_⟩
    · intro l
      exact hsub (shiftIdx i l) (Fin.init y) hxC
    · intro l
      exact projFirst_append _ _
    · intro l l' hll hEq
      have h1 : s (shiftIdx i l) (Fin.init y) = s (shiftIdx i l') (Fin.init y) := by
        have h2 := congrArg (projSnd p (m + 1)) hEq
        rwa [projSnd_append, projSnd_append] at h2
      have h2 : l = l' := shiftIdx_injective i (hinj (Fin.init y) hxC h1)
      exact absurd h2 (ne_of_lt hll)
    · intro l
      show y (Fin.last p) <
        (Fin.append (Fin.init y) (s (shiftIdx i l) (Fin.init y))) (Fin.natAdd p (Fin.last m))
      rw [Fin.append_right]
      exact lt_of_lt_of_le hlt (hmono (Fin.init y) hxC (le_shiftIdx i l))

/-! ## §5. The below-level set is contained in the band -/

/-- **The counting direction.**  If `k - i` pairwise distinct points of the fibre over `x ∈ C`
all have level `> t`, then the level of the `i`-th sheet exceeds `t`: the points determine `k - i`
distinct sheet indices, and an injective `σ` of `Fin (k - i)` into `Fin k` must hit an index
`≤ i` (`lt_level_of_levelsAbove`), which by monotonicity bounds `L i` from below by `t`. -/
theorem belowLevel_subset_band (p m : ℕ) (X : SemiPf (p + (m + 1)))
    (C : Set (Fin p → ℝ)) (M : ℕ) (XC : SemiPf (p + M))
    (hC : C = projFirst p M '' XC.set)
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
    (hcov : ∀ z ∈ X.set, projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (projFirst p (m + 1) z) = projSnd p (m + 1) z)
    (hmono : ∀ x ∈ C, Monotone fun j : Fin k => (s j x) (Fin.last m))
    (i : Fin k) :
    belowLevelSet p (m + 1) M (k - i.val) (Fin.last m) X XC ⊆ bandSetX p m C k s i := by
  have _ := hsub
  intro y hy
  obtain ⟨-, ⟨w, hw⟩, hgt, -, z, hzmem, hzbase, hzdist, hzlvl⟩ := hy
  have hxC : Fin.init y ∈ C := by
    rw [hC]
    exact ⟨Fin.append (Fin.init y) w, hw, projFirst_append _ _⟩
  -- each fibre point is a sheet value over `Fin.init y`
  have hσex : ∀ l : Fin (k - i.val), ∃ j : Fin k,
      s j (Fin.init y) = projSnd p (m + 1) (z l) := fun l => by
    have h := hcov (z l) (hzmem l) (by rw [hzbase l]; exact hxC)
    rwa [hzbase l] at h
  choose σ hσspec using hσex
  have hzeq : ∀ l, z l = Fin.append (Fin.init y) (s (σ l) (Fin.init y)) := by
    intro l
    calc z l = Fin.append (projFirst p (m + 1) (z l)) (projSnd p (m + 1) (z l)) :=
          (append_projFirst_projSndX (z l)).symm
      _ = Fin.append (Fin.init y) (s (σ l) (Fin.init y)) := by rw [hzbase l, hσspec l]
  -- the sheet indices are pairwise distinct
  have hσinj : Function.Injective σ := by
    intro l l' hll
    rcases lt_trichotomy l l' with h | h | h
    · have heq : z l = z l' := by rw [hzeq l, hzeq l', hll]
      exact absurd heq (hzdist l l' h)
    · exact h
    · have heq : z l = z l' := by rw [hzeq l, hzeq l', hll]
      exact absurd heq.symm (hzdist l' l h)
  -- all the levels are above `t`
  have hlev : ∀ l : Fin (k - i.val),
      y (Fin.last p) < (s (σ l) (Fin.init y)) (Fin.last m) := by
    intro l
    have h1 := hzlvl l
    rwa [hzeq l, Fin.append_right] at h1
  exact ⟨hxC, hgt, lt_level_of_levelsAbove (hmono (Fin.init y) hxC) i σ hσinj hlev⟩

/-! ## §6. The theorem -/

/-- The below-level set with `k - i` blocks is the band below the `i`-th sheet. -/
theorem bandSetX_eq_belowLevelSet (p m : ℕ) (X : SemiPf (p + (m + 1)))
    (C : Set (Fin p → ℝ)) (M : ℕ) (XC : SemiPf (p + M))
    (hC : C = projFirst p M '' XC.set)
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
    (hcov : ∀ z ∈ X.set, projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (projFirst p (m + 1) z) = projSnd p (m + 1) z)
    (hmono : ∀ x ∈ C, Monotone fun j : Fin k => (s j x) (Fin.last m))
    (i : Fin k) :
    bandSetX p m C k s i =
      belowLevelSet p (m + 1) M (k - i.val) (Fin.last m) X XC :=
  Set.Subset.antisymm
    (band_subset_belowLevel p m X C M XC hC k s hinj hsub hcov hmono i)
    (belowLevel_subset_band p m X C M XC hC k s hinj hsub hcov hmono i)

theorem belowBandSubPfX (p m : ℕ) (X : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (C : Set (Fin p → ℝ)) (hCpf : WilkiesDesign.E.SubPf p C)
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
    (hcov : ∀ z ∈ X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) = WilkiesDesign.E.projSnd p (m + 1) z)
    (hmono : ∀ x ∈ C, Monotone fun j : Fin k => (s j x) (Fin.last m))
    (i : Fin k) :
    WilkiesDesign.E.SubPf (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s i (Fin.init y)) (Fin.last m)} := by
  obtain ⟨M, XC, hC⟩ := hCpf
  change WilkiesDesign.E.SubPf (p + 1) (bandSetX p m C k s i)
  rw [bandSetX_eq_belowLevelSet p m X C M XC hC k s hinj hsub hcov hmono i]
  exact ⟨M + (p + (m + 1)) * (k - i.val),
    belowLevelZ p (m + 1) M (k - i.val) (Fin.last m) X XC,
    belowLevelPresent p (m + 1) M (k - i.val) (Fin.last m) X XC⟩

end Work.WilE7.SheetData
