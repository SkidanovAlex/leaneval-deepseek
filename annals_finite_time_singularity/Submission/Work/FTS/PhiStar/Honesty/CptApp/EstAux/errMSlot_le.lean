import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.SmoothErr
import Submission.Work.FTS.PhiStar.Honesty.CptApp.LamEst.lamContDiffOn
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The moment slot of the approximation error

The error `err n F = approx n F - F` splits into three groups of terms
(see `CptApp/EstDefs.lean`): the `(χζ − 1)`-group, the localised-Hardy group, and the
moment correction `- chiR n z * lam n F z * rho θ = - mu n F z * rho θ`.

This file proves the pointwise bound for the moment group: for every `k` there is a
universal constant `C` with

  `(D_z^i (mu n F · rho) · w / sin(2θ)^{η/2})² ≤ C · Good α k n F z θ`

for all `i ≤ k`, `z ∈ Iz`, `θ ∈ Iθ`.

Mathematically the bound is the obvious one: `rho` does not depend on `z`, so the whole
`z`-derivative falls on `mu n F`; and the angular profile `rhoProf α k θ` of the third
group of `Good` contains, as its `i = 0` term, the quantity `(rho θ)² · sin(2θ)^{-η}`
which dominates the angular factor `rho θ² sin(2θ)^{-η}` coming from the weight
`w/sin(2θ)^{η/2}` squared.  Consequently the whole slot is absorbed by the third group of
`Good` alone, with the constant `1` (only the elementary nonnegativity of the first two
groups of `Good` is used).

The three ingredients are the lemmas

* `DzIter_mul_rho_eq` — the `z`-derivative of `mu n F · rho` is `rho` times the
  `z`-derivative of `mu n F` (evaluated at `θ = 0`, the `θ`-independence of `mu n F`);
* `sq_div_sin` — `(w / sin(2θ)^{η/2})² = w² · sin(2θ)^{-η}`;
* `rhoProf_ge` — `(rho θ)² · sin(2θ)^{-η} ≤ rhoProf α k θ`.
-/

namespace Work.FTS.PhiStar.Honesty.CptApp.EstAux

/-! ## The three ingredients -/

/-- `D_z^i (mu n F · rho)` with a `θ`-only right factor: the derivative falls entirely on
the `z`-dependent factor, and the factor `D_z^i mu n F` is independent of `θ`, hence may be
evaluated at `θ = 0` (the form in which `Good` presents it). -/
theorem DzIter_mul_rho_eq (g : ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter i (fun z θ => g z * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z θ
      = Work.Spaces.DzIter i (fun z' _ : ℝ => g z') z 0
        * Work.FTS.PhiStar.Honesty.CptApp.rho θ := by
  induction i generalizing z θ with
  | zero => rfl
  | succ i ih =>
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    have hfun : (fun z' => Work.Spaces.DzIter i (fun z θ => g z * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z' θ)
        = (fun z' => Work.Spaces.DzIter i (fun z' _ : ℝ => g z') z' 0
            * Work.FTS.PhiStar.Honesty.CptApp.rho θ) :=
      funext (fun z' => ih z' θ)
    rw [hfun, deriv_mul_const_field]
    ring

/-- The square of the radial/angular weight `w / sin(2θ)^{η/2}`. -/
theorem sq_div_sin (z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.PhiStar.Honesty.CptApp.sin_two_nonneg_of_mem_Iθ hθ
  have hb : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = Real.sin (2 * θ) ^ Work.Spaces.eta := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    congr 1
    ring
  rw [div_pow, hb, div_eq_mul_inv, Real.rpow_neg hs]

/-- The angular factor of the moment slot is dominated by the angular profile `rhoProf`:
its `i = 0` term alone is `(rho θ)² · (sin(2θ)^{-γ} + sin(2θ)^{-η})`. -/
theorem rhoProf_ge (α : ℝ) (k : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.PhiStar.Honesty.CptApp.rho θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ Work.FTS.PhiStar.Honesty.CptApp.rhoProf α k θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.PhiStar.Honesty.CptApp.sin_two_nonneg_of_mem_Iθ hθ
  rw [Work.FTS.PhiStar.Honesty.CptApp.rhoProf]
  have hmem : 0 ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.succ_pos k)
  have hnn : ∀ i ∈ Finset.range (k + 1),
      0 ≤ (Work.Spaces.DthIter i (fun _ θ' : ℝ => Work.FTS.PhiStar.Honesty.CptApp.rho θ') 0 θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) + (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
    fun i _ => mul_nonneg (sq_nonneg _) (add_nonneg (Real.rpow_nonneg hs _) (Real.rpow_nonneg hs _))
  have hsingle := Finset.single_le_sum hnn hmem
  simp only [Work.Spaces.DthIter_zero] at hsingle
  refine le_trans ?_ hsingle
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact le_add_of_nonneg_left (Real.rpow_nonneg hs _)

/-! ## The slot bound -/

theorem errMSlot_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → 3 ≤ n →
      Work.FTS.EllipticEst.SmoothOpen F →
      ∀ (i : ℕ), i ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        (Work.Spaces.DzIter i (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z
            * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ C * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
  refine ⟨1, one_pos, ?_⟩
  intro α n F hα0 hα1 hn hsm i hi z hz θ hθ
  have hA := DzIter_mul_rho_eq (fun z => Work.FTS.PhiStar.Honesty.CptApp.mu n F z) i z θ
  have hB := sq_div_sin z hθ
  have hC := rhoProf_ge α k hθ
  have hWnn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hSn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_nonneg (Work.FTS.PhiStar.Honesty.CptApp.sin_two_nonneg_of_mem_Iθ hθ) _
  set T : ℝ := ∑ m ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
    with hT
  have hD : (Work.Spaces.DzIter i (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
      ≤ T := by
    rw [hT]
    exact Finset.single_le_sum
      (f := fun m => (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2)
      (fun m _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have hTnn : 0 ≤ T := by
    rw [hT]; exact Finset.sum_nonneg (fun m _ => sq_nonneg _)
  have hstep : (Work.Spaces.DzIter i (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
        * (Work.FTS.PhiStar.Honesty.CptApp.rho θ) ^ 2
        * (((Work.Spaces.w z) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ T * (((Work.Spaces.w z) ^ 2) * Work.FTS.PhiStar.Honesty.CptApp.rhoProf α k θ) := by
    have h1 : (Work.Spaces.DzIter i (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
          * (Work.Spaces.w z) ^ 2 ≤ T * (Work.Spaces.w z) ^ 2 :=
      mul_le_mul_of_nonneg_right hD hWnn
    have h3 : 0 ≤ (Work.FTS.PhiStar.Honesty.CptApp.rho θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := mul_nonneg (sq_nonneg _) hSn
    have h4 : 0 ≤ T * (Work.Spaces.w z) ^ 2 := mul_nonneg hTnn hWnn
    calc (Work.Spaces.DzIter i (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
          * (Work.FTS.PhiStar.Honesty.CptApp.rho θ) ^ 2
          * (((Work.Spaces.w z) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = ((Work.Spaces.DzIter i (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
            * (Work.Spaces.w z) ^ 2)
          * ((Work.FTS.PhiStar.Honesty.CptApp.rho θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
      _ ≤ (T * (Work.Spaces.w z) ^ 2) * Work.FTS.PhiStar.Honesty.CptApp.rhoProf α k θ :=
          mul_le_mul h1 hC h3 h4
      _ = T * (((Work.Spaces.w z) ^ 2) * Work.FTS.PhiStar.Honesty.CptApp.rhoProf α k θ) := by ring
  have hGood : T * (((Work.Spaces.w z) ^ 2) * Work.FTS.PhiStar.Honesty.CptApp.rhoProf α k θ)
      ≤ Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
    rw [hT, Work.FTS.PhiStar.Honesty.CptApp.Good]
    exact le_add_of_nonneg_left (add_nonneg
      (Work.FTS.PhiStar.Honesty.CptApp.omegaPart_nonneg α k n F z θ)
      (mul_nonneg (Work.FTS.PhiStar.Honesty.CptApp.thShrink_nonneg n θ)
        (Work.FTS.PhiStar.Honesty.CptApp.hkZsum_nonneg α k F z hθ)))
  calc (Work.Spaces.DzIter i (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z
          * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = ((Work.Spaces.DzIter i (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0
            * Work.FTS.PhiStar.Honesty.CptApp.rho θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by rw [hA]
    _ = (Work.Spaces.DzIter i (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
          * (Work.FTS.PhiStar.Honesty.CptApp.rho θ) ^ 2
          * (((Work.Spaces.w z) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        rw [mul_pow, mul_pow, hB]
    _ ≤ T * (((Work.Spaces.w z) ^ 2) * Work.FTS.PhiStar.Honesty.CptApp.rhoProf α k θ) := hstep
    _ ≤ Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := hGood
    _ = 1 * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by ring

end Work.FTS.PhiStar.Honesty.CptApp.EstAux
