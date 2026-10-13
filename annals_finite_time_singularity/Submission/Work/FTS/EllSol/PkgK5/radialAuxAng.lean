import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllSol.PkgK5.radialAuxBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Radial profiles vs. their `sin (2θ)`-multiples: the angular identities

Part 2 of the proof of `Work.FTS.EllSol.PkgK5.radialHkNorm_le_sinMul`: the `D_θ`-algebra
(the `Lop` iterates of `sin 2·`, the product identity `D_θ^i (Λ·B) = Λ · D_θ^i B`, the
vanishing of the angular derivatives of a radial profile and the mixed identity).
-/

namespace Work.FTS.EllSol.PkgK5

namespace Radial

/-! ## The angular profile `sin (2θ)` -/

/-- All `Lop`-iterates of `sin (2·)` are smooth everywhere. -/
theorem contDiffOn_LopIter_sin :
    ∀ i n : ℕ, ContDiffOn ℝ n (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)))
      Set.univ := by
  intro i
  induction i with
  | zero =>
    intro n
    exact (by fun_prop : ContDiffOn ℝ n (fun θ : ℝ => Real.sin (2 * θ)) Set.univ)
  | succ i ih =>
    intro n
    have h1 : ContDiffOn ℝ (n + 1)
        (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ))) Set.univ := ih (n + 1)
    have h2 : ContDiffOn ℝ n
        (deriv (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)))) Set.univ :=
      h1.deriv_of_isOpen isOpen_univ (by simp)
    have h3 : Work.FTS.EllipticEst.LopIter (i + 1) (fun θ : ℝ => Real.sin (2 * θ))
        = fun θ => Real.sin (2 * θ)
            * deriv (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ))) θ := by
      rw [Work.FTS.EllipticEst.LopIter_succ]; rfl
    rw [h3]
    exact ((by fun_prop : ContDiffOn ℝ n (fun θ : ℝ => Real.sin (2 * θ)) Set.univ)).mul h2

theorem differentiable_LopIter_sin (i : ℕ) :
    Differentiable ℝ (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ))) := fun θ =>
  ((contDiffOn_LopIter_sin i 1).differentiableOn (by simp)).differentiableAt (by simp)

theorem continuous_LopIter_sin (i : ℕ) :
    Continuous (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ))) :=
  continuousOn_univ.mp (contDiffOn_LopIter_sin i 0).continuousOn

/-- `D_θ^i` of a function of the form `(z,θ) ↦ Λ z · B θ` is `(Λ z) · D_θ^i B θ`. -/
theorem DthIter_mul_theta (Λ B : ℝ → ℝ)
    (hB : ∀ i : ℕ, Differentiable ℝ (Work.FTS.EllipticEst.LopIter i B)) :
    ∀ i : ℕ, Work.Spaces.DthIter i (fun z θ => Λ z * B θ)
      = fun z θ => Λ z * Work.FTS.EllipticEst.LopIter i B θ := by
  intro i
  induction i with
  | zero => funext z θ; simp
  | succ i ih =>
    funext z θ
    have hfun : (fun θ' => Work.Spaces.DthIter i (fun z θ => Λ z * B θ) z θ')
        = fun θ' => Λ z * Work.FTS.EllipticEst.LopIter i B θ' := by
      funext θ'
      rw [congrFun (congrFun ih z) θ']
    have hd : DifferentiableAt ℝ (Work.FTS.EllipticEst.LopIter i B) θ := hB i θ
    rw [Work.Spaces.DthIter_succ]
    simp only [Work.Spaces.Dth, Work.Spaces.pth, hfun, deriv_const_mul _ hd,
      Work.FTS.EllipticEst.LopIter_succ, Work.Spaces.Lop]
    ring

/-- `D_θ^i (Λ·sin 2·) = Λ · D_θ^i (sin 2·)`. -/
theorem DthIter_sinMul (Λ : ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => Λ z * Real.sin (2 * θ))
      = fun z θ => Λ z * Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ :=
  DthIter_mul_theta Λ (fun θ : ℝ => Real.sin (2 * θ)) differentiable_LopIter_sin i

/-! ## Vanishing of the angular derivatives of a radial function -/

theorem DthIter_radial_zero (Λ : ℝ → ℝ) (m : ℕ) :
    Work.Spaces.DthIter (m + 1) (fun z θ => Λ z) = 0 := by
  induction m with
  | zero =>
    funext z θ
    simp [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
  | succ m ih =>
    rw [show m + 1 + 1 = (m + 1) + 1 from rfl, Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp [Work.Spaces.Dth, Work.Spaces.pth]

theorem Dz_zero (j : ℕ) : Work.Spaces.DzIter j (0 : ℝ → ℝ → ℝ) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.DzIter_succ, ih]
    funext z θ
    simp [Work.Spaces.Dz, Work.Spaces.pz]

/-- The mixed summands of `HkIntegrand` vanish for a radial function. -/
theorem mixed_radial_zero (Λ : ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => Λ z) z θ = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [Work.Spaces.mixed, DthIter_radial_zero Λ m, Dz_zero j]
  rfl

/-- The mixed derivative of `(z,θ) ↦ Λ z · sin(2θ)`. -/
theorem mixed_sinMul (Λ : ℝ → ℝ) (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0))
    (j i : ℕ) {z : ℝ} (hz : 0 < z) (θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => Λ z * Real.sin (2 * θ)) z θ
      = RIter j Λ z * Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ := by
  have h1 : Work.Spaces.mixed j i (fun z θ => Λ z * Real.sin (2 * θ))
      = Work.Spaces.DzIter j
          (fun z θ => Λ z * Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) := by
    rw [Work.Spaces.mixed, DthIter_sinMul Λ i]
  rw [h1, DzIter_mul_theta Λ hΛ (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ))) j hz θ]

/-! ## Two `rpow` rewrites -/

theorem rpow_neg_half_sq (γ : ℝ) (hγ : γ ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := by
  rcases lt_or_eq_of_le hs with h | h
  · rw [sq, ← Real.rpow_add h]
    congr 1
    ring
  · subst h
    have h1 : -(γ / 2) ≠ 0 := by intro hc; exact hγ (by linarith [neg_eq_zero.mp hc])
    have h2 : -γ ≠ 0 := by intro hc; exact hγ (by linarith [neg_eq_zero.mp hc])
    rw [Real.zero_rpow h1, Real.zero_rpow h2]
    norm_num

theorem sq_mul_rpow_neg (e : ℝ) (he : e ≠ 2) {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 * s ^ (-e) = s ^ (2 - e) := by
  rcases lt_or_eq_of_le hs with h | h
  · rw [← Real.rpow_natCast s 2, ← Real.rpow_add h]
    ring_nf
  · subst h
    have h3 : 2 - e ≠ 0 := by intro hc; exact he (by linarith)
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, Real.zero_rpow h3]

end Radial

end Work.FTS.EllSol.PkgK5
