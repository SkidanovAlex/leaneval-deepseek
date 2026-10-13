import Mathlib

namespace Work.WilE2.Cb

theorem hasFDerivAt_graphSlope_coord {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (hF : ContDiff ℝ 2 F)
    (i : Fin (m+1)) {A : Set (Fin m → ℝ)} (hA : IsOpen A) {h : (Fin m → ℝ) → ℝ}
    (hh : ContDiffOn ℝ 1 h A) {u : Fin m → ℝ} (hu : u ∈ A)
    (hne : fderiv ℝ F (Fin.insertNth i (h u) u) (Pi.single i 1) ≠ 0) (l : Fin m) :
    HasFDerivAt (fun u' : Fin m → ℝ =>
        fderiv ℝ F (Fin.insertNth i (h u') u') (Pi.single (i.succAbove l) 1)
          / fderiv ℝ F (Fin.insertNth i (h u') u') (Pi.single i 1))
      ((fderiv ℝ (fun y : Fin (m+1) → ℝ => fderiv ℝ F y (Pi.single (i.succAbove l) 1)
          / fderiv ℝ F y (Pi.single i 1)) (Fin.insertNth i (h u) u)).comp
        (fderiv ℝ (fun u' : Fin m → ℝ => Fin.insertNth i (h u') u') u)) u := by
  -- `h` is differentiable at `u` (it is `C¹` on the open set `A`).
  have hhd : DifferentiableAt ℝ h u :=
    (hh.contDiffAt (hA.mem_nhds hu)).differentiableAt (by norm_num)
  -- The graph parametrisation `Φ u' = insertNth i (h u') u'` is differentiable at `u`.
  have hΦ : DifferentiableAt ℝ
      (fun u' : Fin m → ℝ => (Fin.insertNth (α := fun _ => ℝ) i (h u') u')) u := by
    rw [differentiableAt_pi]
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with hji | ⟨k, hk⟩
    · rw [hji]
      simpa using hhd
    · rw [hk]
      simpa using (differentiableAt_apply k u)
  -- Each partial derivative `y ↦ ∂_j F y` is differentiable at the base point (`F` is `C²`).
  have hfd_all : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) (Fin.insertNth i (h u) u) := hfd_all _
  have hpj : DifferentiableAt ℝ (fun y : Fin (m+1) → ℝ =>
      (fderiv ℝ F y) (Pi.single (i.succAbove l) 1)) (Fin.insertNth i (h u) u) :=
    hfd.clm_apply (differentiableAt_const _)
  have hpi : DifferentiableAt ℝ (fun y : Fin (m+1) → ℝ =>
      (fderiv ℝ F y) (Pi.single i 1)) (Fin.insertNth i (h u) u) :=
    hfd.clm_apply (differentiableAt_const _)
  -- Hence the quotient `y ↦ ∂_j F y / ∂_i F y` is differentiable (`∂_i F` is nonzero at `y₀`).
  have hψmul : DifferentiableAt ℝ (fun y : Fin (m+1) → ℝ =>
      (fderiv ℝ F y) (Pi.single (i.succAbove l) 1) * ((fderiv ℝ F y) (Pi.single i 1))⁻¹)
      (Fin.insertNth i (h u) u) := hpj.mul (hpi.inv hne)
  have hψ : DifferentiableAt ℝ (fun y : Fin (m+1) → ℝ =>
      (fderiv ℝ F y) (Pi.single (i.succAbove l) 1) / (fderiv ℝ F y) (Pi.single i 1))
      (Fin.insertNth i (h u) u) := by
    rw [show (fun y : Fin (m+1) → ℝ =>
        (fderiv ℝ F y) (Pi.single (i.succAbove l) 1) / (fderiv ℝ F y) (Pi.single i 1))
        = fun y : Fin (m+1) → ℝ =>
        (fderiv ℝ F y) (Pi.single (i.succAbove l) 1) * ((fderiv ℝ F y) (Pi.single i 1))⁻¹
        from by funext y; rw [div_eq_mul_inv]]
    exact hψmul
  -- Chain rule for `u' ↦ ψ (Φ u')`.
  have hcomp := HasFDerivAt.comp
    (f := fun u' : Fin m → ℝ => (Fin.insertNth (α := fun _ => ℝ) i (h u') u'))
    u (hψ.hasFDerivAt) (hΦ.hasFDerivAt)
  simpa only [Function.comp_def] using hcomp

end Work.WilE2.Cb
