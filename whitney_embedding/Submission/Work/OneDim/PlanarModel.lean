import Mathlib

/-!
# Planar model maps and placement data for the `n = 1` Whitney embedding theorem

This file sets up the two explicit planar model maps used in the disjoint-union assembly of the
`n = 1` case of Whitney's strong embedding theorem:

* `planarLine c : ℝ → ℝ²`, the horizontal line `{p | p 1 = c}`, used to place the non-compact
  connected components (those diffeomorphic to `ℝ`);
* `planarCircle c : Circle → ℝ²`, the circle of radius `1/4` centred at `(c, 0)`, used to place
  the compact connected components (those diffeomorphic to the circle).

`planarPlace` combines the two cases: given the model data `d` of a connected component `C`
(a diffeomorphism `ℝ ≃ C`, or `Circle ≃ C`) and a slot index `j`, it maps `C` into the `j`-th
slot of the plane.
-/

open scoped Manifold ContDiff
open Topology Set Function

namespace Work.OneDim

noncomputable section

/-- The direction vector `(1,0)` of the plane. -/
def lineDir : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => if i = 0 then 1 else 0)

/-- The vector `(0,c)` of the plane. -/
def heightVec (c : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => if i = 0 then 0 else c)

/-- The horizontal line `{p | p 1 = c}` in the plane, parametrised by `ℝ`. -/
def planarLine (c : ℝ) : ℝ → EuclideanSpace ℝ (Fin 2) :=
  fun t => t • lineDir + heightVec c

/-- The circle of radius `1/4` centred at `(c,0)`, parametrised by the unit circle `Circle`. -/
def planarCircle (c : ℝ) : Circle → EuclideanSpace ℝ (Fin 2) :=
  fun z => (EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun i : Fin 2 => if i = 0 then c + (1/4) * ((z : ℂ)).re else (1/4) * ((z : ℂ)).im)

@[simp] theorem lineDir_apply_zero : (lineDir : EuclideanSpace ℝ (Fin 2)).ofLp 0 = 1 := by
  simp [lineDir]

@[simp] theorem lineDir_apply_one : (lineDir : EuclideanSpace ℝ (Fin 2)).ofLp 1 = 0 := by
  simp [lineDir]

@[simp] theorem heightVec_apply_zero (c : ℝ) : (heightVec c).ofLp 0 = 0 := by
  simp [heightVec]

@[simp] theorem heightVec_apply_one (c : ℝ) : (heightVec c).ofLp 1 = c := by
  simp [heightVec]

@[simp] theorem planarLine_apply_zero (c t : ℝ) : (planarLine c t).ofLp 0 = t := by
  simp [planarLine]

@[simp] theorem planarLine_apply_one (c t : ℝ) : (planarLine c t).ofLp 1 = c := by
  simp [planarLine]

@[simp] theorem planarCircle_apply_zero (c : ℝ) (z : Circle) :
    (planarCircle c z).ofLp 0 = c + (1/4) * ((z : ℂ)).re := by
  simp [planarCircle]

@[simp] theorem planarCircle_apply_one (c : ℝ) (z : Circle) :
    (planarCircle c z).ofLp 1 = (1/4) * ((z : ℂ)).im := by
  simp [planarCircle]

/-- The data attached to a connected component: a diffeomorphism onto it from `ℝ` (non-compact
case) or from the unit circle `Circle` (compact case). -/
abbrev PlanarPlaceData (C : Type*) [TopologicalSpace C] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) C] :=
  (Diffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
    ℝ C ((⊤ : ℕ∞) : WithTop ℕ∞)) ⊕
  (Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) Circle C ((⊤ : ℕ∞) : WithTop ℕ∞))

/-- Place the connected component `C` (with model data `d`) into the plane, in the slot of index
`j`: on the horizontal line `{p | p 1 = j + 1/2}` in the `ℝ` case, and on the circle of radius
`1/4` centred at `(j, 0)` in the `Circle` case. -/
def planarPlace {C : Type*} [TopologicalSpace C] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) C]
    (j : ℕ) (d : PlanarPlaceData C) (y : C) : EuclideanSpace ℝ (Fin 2) :=
  Sum.elim (fun φ => planarLine (j + 1/2 : ℝ) (φ.symm y))
    (fun ψ => planarCircle (j : ℝ) (ψ.symm y)) d

/-- The `i`-th coordinate of a point of the plane is bounded by its norm. -/
theorem norm_apply_le_two (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : ‖x.ofLp i‖ ≤ ‖x‖ := by
  have h1 : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  exact PiLp.norm_apply_le x i

theorem abs_apply_le_two (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : |x.ofLp i| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using norm_apply_le_two x i

/-- The `1`-coordinate of a point of the circle `planarCircle c` is at most `1/4` in absolute
value. -/
theorem planarCircle_abs_apply_one (c : ℝ) (z : Circle) :
    |(planarCircle c z).ofLp 1| ≤ 1/4 := by
  rw [planarCircle_apply_one, abs_mul]
  have h : |((z : ℂ)).im| ≤ 1 := by
    have h2 : |((z : ℂ)).im| ≤ ‖(z : ℂ)‖ := Complex.abs_im_le_norm (z : ℂ)
    rwa [Circle.norm_coe] at h2
  calc |(1/4 : ℝ)| * |((z : ℂ)).im| ≤ (1/4) * 1 :=
        mul_le_mul (by norm_num) h (abs_nonneg _) (by norm_num)
    _ = 1/4 := by norm_num

/-- The `0`-coordinate of a point of the circle `planarCircle c` lies in `[c - 1/4, c + 1/4]`. -/
theorem planarCircle_apply_zero_mem (c : ℝ) (z : Circle) :
    (planarCircle c z).ofLp 0 ∈ Set.Icc (c - 1/4) (c + 1/4) := by
  rw [planarCircle_apply_zero]
  have h : |((z : ℂ)).re| ≤ 1 := by
    have h2 : |((z : ℂ)).re| ≤ ‖(z : ℂ)‖ := Complex.abs_re_le_norm (z : ℂ)
    rwa [Circle.norm_coe] at h2
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  constructor <;> linarith

/-- The slot index of a point of `planarPlace j d` is bounded by its norm plus `1/2`. -/
theorem natCast_le_norm_planarPlace {C : Type*} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) C] (j : ℕ) (d : PlanarPlaceData C) (y : C) :
    (j : ℝ) ≤ ‖planarPlace j d y‖ + 1/2 := by
  rcases d with φ | ψ
  · have h : (planarPlace j (Sum.inl φ) y).ofLp 1 = (j : ℝ) + 1/2 := by
      simp [planarPlace]
    have h2 : |(j : ℝ) + 1/2| ≤ ‖planarPlace j (Sum.inl φ) y‖ := by
      have h3 := abs_apply_le_two (planarPlace j (Sum.inl φ) y) 1
      rwa [h] at h3
    have h4 : (0 : ℝ) ≤ (j : ℝ) + 1/2 := by positivity
    linarith [abs_of_nonneg h4, h2]
  · have h : (planarPlace j (Sum.inr ψ) y).ofLp 0
        = (j : ℝ) + (1/4) * (((ψ.symm y : Circle)) : ℂ).re := by
      simp [planarPlace]
    have h2 : |(planarPlace j (Sum.inr ψ) y).ofLp 0| ≤ ‖planarPlace j (Sum.inr ψ) y‖ :=
      abs_apply_le_two _ 0
    have h3 : -1 ≤ (((ψ.symm y : Circle)) : ℂ).re := by
      have h4 : |(((ψ.symm y : Circle)) : ℂ).re| ≤ 1 := by
        have h5 : |(((ψ.symm y : Circle)) : ℂ).re| ≤ ‖(((ψ.symm y : Circle)) : ℂ)‖ :=
          Complex.abs_re_le_norm _
        rwa [Circle.norm_coe] at h5
      exact (abs_le.mp h4).1
    have h6 : (j : ℝ) - 1/4 ≤ (planarPlace j (Sum.inr ψ) y).ofLp 0 := by
      rw [h]; nlinarith
    linarith [le_abs_self ((planarPlace j (Sum.inr ψ) y).ofLp 0), h2, h6]

end

end Work.OneDim
