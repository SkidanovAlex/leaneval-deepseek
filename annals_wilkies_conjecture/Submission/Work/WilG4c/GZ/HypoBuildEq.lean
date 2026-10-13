/-
  WilG4c / `CritFixOmega` — `HypoBuild = HypoRawE`, the unfolding of the `Ω`-construction
  behind the ball-condensation operator.

  (This is the same proof as our teammate's module
  `Submission.Work.WilG4cR.HypoRaw_eq_HypoBuild`; it is reproduced here so that the final
  `CritFixOmega` module depends only on files in its own directory plus the frozen/clean
  infrastructure.)

  `HypoRaw p n X` (the ball-condensation of `X`) is the set of `u` such that some fibre ball
  around `u` lies in `X`; `HypoRawE p n X` is the same with the Euclidean ball explicitly;
  `HypoBuild p n X` is the six-step `Ω`-construction (pull back `Xᶜ` along `(x,r,y) ↦
  (parPt x, y)`, intersect with `r² - Σ(y_j - z_j)² > 0`, project away `y`, complement, record
  `r > 0`, project away `r`).  This file proves `HypoBuild = HypoRawE`, the bookkeeping step of
  `HypoRaw = HypoBuild`.
-/
import Mathlib
import Submission.Work.WilG4c.CritAux.HypoDefs
import Submission.Work.WilG4c.CritAux
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.snocIt_castAdd

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c.GZ

open WilkiesDesign

/-- `Work.WilG0.snocIt` is the same gluing as `Fin.append`: it puts `x` in front and `w` at the
end. -/
theorem snocIt_eq_append (n m : ℕ) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    Work.WilG0.snocIt n m x w = Fin.append x w := by
  funext k
  refine Fin.addCases (motive := fun k => Work.WilG0.snocIt n m x w k = Fin.append x w k) ?_ ?_ k
  · intro i
    rw [Work.WilG0.snocIt_castAdd, Fin.append_left]
  · intro j
    rw [Work.WilG0.snocIt_natAdd, Fin.append_right]

/-- The substitution `iotaA` reads the glued vector `(x, t, y)` as `(parPt x, y)`. -/
theorem iotaA_comp (p n : ℕ) (x : Fin (p + (n + 1)) → ℝ) (t : ℝ) (y : Fin (n + 1) → ℝ) :
    (Fin.append (Fin.snoc x t) y) ∘ Work.WilkG4c.iotaA p n
      = Fin.append (Work.WilkG4c.parPt x) y := by
  funext i
  refine Fin.addCases (motive := fun i =>
      ((Fin.append (Fin.snoc x t) y) ∘ Work.WilkG4c.iotaA p n) i
        = Fin.append (Work.WilkG4c.parPt x) y i) ?_ ?_ i
  · intro i'
    show Fin.append (Fin.snoc x t) y (Work.WilkG4c.iotaA p n (Fin.castAdd (n + 1) i'))
        = Fin.append (Work.WilkG4c.parPt x) y (Fin.castAdd (n + 1) i')
    simp only [Work.WilkG4c.iotaA, Fin.append_left, Fin.snoc_castSucc, Work.WilkG4c.parPt_apply]
  · intro j
    show Fin.append (Fin.snoc x t) y (Work.WilkG4c.iotaA p n (Fin.natAdd p j))
        = Fin.append (Work.WilkG4c.parPt x) y (Fin.natAdd p j)
    simp only [Work.WilkG4c.iotaA, Fin.append_right]

/-- The value of the ball polynomial at the glued vector `(x, t, y)` is `t² - Σ(y_j - z_j)²`,
where `z = cubePt x` is the fibre point. -/
theorem eval_ballP (p n : ℕ) (x : Fin (p + (n + 1)) → ℝ) (t : ℝ) (y : Fin (n + 1) → ℝ) :
    MvPolynomial.eval (Fin.append (Fin.snoc x t) y) (Work.WilkG4c.ballP p n)
      = t ^ 2 - ∑ j : Fin (n + 1), (y j - Work.WilkG4c.cubePt x j) ^ 2 := by
  simp only [Work.WilkG4c.ballP, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
    MvPolynomial.eval_X, MvPolynomial.eval_sum, Fin.append_left, Fin.append_right,
    Fin.snoc_last, Fin.snoc_castSucc, Work.WilkG4c.cubePt_apply]

/-- Unfolding of the pullback set `HypoA`. -/
theorem mem_HypoA {p n : ℕ} {X : Set (Fin (p + (n + 1)) → ℝ)}
    {w : Fin (Work.WilkG4c.hypoM p n) → ℝ} :
    (w ∈ Work.WilkG4c.HypoA p n X) ↔ ¬ (w ∘ Work.WilkG4c.iotaA p n ∈ X) := Iff.rfl

/-- Unfolding of the positivity locus `HypoBall`. -/
theorem mem_HypoBall {p n : ℕ} {w : Fin (Work.WilkG4c.hypoM p n) → ℝ} :
    (w ∈ Work.WilkG4c.HypoBall p n) ↔ 0 < MvPolynomial.eval w (Work.WilkG4c.ballP p n) :=
  Iff.rfl

/-- The `Ω`-construction `HypoBuild`, written out: `x` lies in it iff there is a radius `t > 0`
with the whole Euclidean fibre ball of radius `t` around `x` contained in `X`. -/
theorem hypoBuild_eq_HypoRawE (p n : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)) :
    Work.WilkG4c.HypoBuild p n X = Work.WilkG4c.HypoRawE p n X := by
  ext x
  have key : (x ∈ Work.WilkG4c.HypoBuild p n X) ↔ ∃ t : ℝ, 0 < t ∧ ∀ y : Fin (n + 1) → ℝ,
        (∑ j : Fin (n + 1), (y j - Work.WilkG4c.cubePt x j) ^ 2 < t ^ 2) →
          Fin.append (Work.WilkG4c.parPt x) y ∈ X := by
    simp only [Work.WilkG4c.HypoBuild, Work.WilkG4c.hypoN, WilkiesDesign.projLast,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht⟩
      rw [Set.mem_inter_iff, Set.mem_compl_iff, Work.WilG0.projLastIter_eq] at ht
      simp only [Set.mem_ofPred_eq, Fin.snoc_last] at ht
      obtain ⟨hnot, hpos⟩ := ht
      refine ⟨t, hpos, fun y hy => ?_⟩
      have hz : ¬ (Work.WilG0.snocIt (p + (n + 1) + 1) (n + 1) (Fin.snoc x t) y
          ∈ Work.WilkG4c.HypoA p n X ∩ Work.WilkG4c.HypoBall p n) :=
        fun hcon => hnot ⟨y, hcon⟩
      rw [Set.mem_inter_iff, not_and_or] at hz
      rcases hz with hA | hB
      · have hzA : (Work.WilG0.snocIt (p + (n + 1) + 1) (n + 1) (Fin.snoc x t) y)
            ∘ Work.WilkG4c.iotaA p n ∈ X := by
          simp only [mem_HypoA, not_not] at hA
          exact hA
        rwa [snocIt_eq_append, iotaA_comp p n x t y] at hzA
      · have hzB : ¬ (0 < t ^ 2 - ∑ j : Fin (n + 1),
            (y j - Work.WilkG4c.cubePt x j) ^ 2) := by
          simp only [mem_HypoBall] at hB
          rwa [snocIt_eq_append, eval_ballP p n x t y] at hB
        exact absurd (sub_pos.mpr hy) hzB
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_, ?_⟩
      · rw [Set.mem_compl_iff, Work.WilG0.projLastIter_eq]
        simp only [Set.mem_ofPred_eq]
        intro hcon
        obtain ⟨y, hy⟩ := hcon
        rw [Set.mem_inter_iff] at hy
        obtain ⟨hA, hB⟩ := hy
        have hAz : ¬ (Fin.append (Work.WilkG4c.parPt x) y ∈ X) := by
          have h := hA
          simp only [mem_HypoA] at h
          rwa [snocIt_eq_append, iotaA_comp p n x t y] at h
        have hBz : 0 < t ^ 2 - ∑ j : Fin (n + 1),
            (y j - Work.WilkG4c.cubePt x j) ^ 2 := by
          have h := hB
          simp only [mem_HypoBall] at h
          rwa [snocIt_eq_append, eval_ballP p n x t y] at h
        exact hAz (ht.2 y (sub_pos.mp hBz))
      · simpa using ht.1
  rw [key]
  simp only [Work.WilkG4c.HypoRawE, Set.mem_ofPred_eq]

end Work.WilkG4c.GZ
