/-
# `err_dzSlot_le`: the pure `D_z`-slots of the error are dominated by `Good`

Target: `Work.FTS.PhiStar.Honesty.CptApp.Est.err_dzSlot_le`.

The error of the approximation is

  `err n F = (chiR n · zetaR n − 1)·F − (chiR n · lam n F)·rho`,

and this module reduces the estimate for its pure `D_z`-slots

  `(D_z^i (err n F) · w/sin(2θ)^{η/2})² ≤ C · Good α k n F`

to the two halves of that decomposition:

* `EstAux.errASlot_le` — the `(χζ−1)F` part, dominated by the `Ω_n`-term of `Good`
  (the `D_z`-jets of `χζ−1` are supported in `Ω_n` and bounded uniformly in `n`);
* `EstAux.errMSlot_le` — the moment correction `χ·lam n F·rho`, which is exactly the
  slot that `Good`'s third term (`rhoProf`) was designed to dominate.

Proved here:

* `estASlot_le` — the `(χζ−1)·F` half, from the two smaller delegated ingredients
  `EstAux.errAdjBound` (the `D_z`-jets of `χζ−1` are supported in `Ω_n` and bounded
  uniformly in `n`; see `EstAux.errAdjBound`) and `EstAux.errASlot_expand` (the Leibniz
  expansion of `D_z^i ((χζ−1)F)`): Cauchy–Schwarz plus the termwise bound of the pure
  `D_z`-slots of `HkIntegrand` give `C · omegaPart`, and `omegaPart ≤ Good`;
* `estOmegaPart_eq` / `estOmegaPart_le_Good` — `omegaPart α k n F = omegaInd n · HkIntegrand`
  and `omegaPart ≤ Good`;
* `estDzIter_congr_slice` / `estDzIter_sub` — locality of `D_z` in `θ` and additivity of
  the iterated `D_z` over differences on the open quadrant;
* the decomposition of the error: `D_z^i (err n F)` splits additively into the `D_z`-iterates
  of the two pieces (on the open quadrant where both are `C^∞`), together with the
  trivial cases `z = 0` and `θ ∈ {0, π/2}` in which the weight `w z / sin(2θ)^{η/2}`
  vanishes.  The final constant is `2 (C_1 + C_2) + 1`.

The `(χζ−1)·F` half is also available, independently, as `EstAux.errASlot_le`
(a different implementation of the same bound).
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.ZetaBound
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.PlateauZero
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.SmoothErr
import Submission.Work.FTS.PhiStar.Honesty.CptApp.LamAux.chiR_dzIter_boundAux
import Submission.Work.FTS.PhiStar.Honesty.CptApp.LamEst.lamContDiffOn
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.errAdjBound
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.errASlot_expand
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.errMSlot_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.Est

set_option autoImplicit false

/-! ## Locality of `D_z` in the angular variable -/

/-- `D_z`-iterates only see the `z`-slice at the given angle: two functions with the same
`θ`-slice at `θ` have the same `D_z`-iterates at `(z,θ)`. -/
theorem estDzIter_congr_slice {f g : ℝ → ℝ → ℝ} (i : ℕ) {θ : ℝ}
    (h : ∀ z : ℝ, f z θ = g z θ) (z : ℝ) :
    Work.Spaces.DzIter i f z θ = Work.Spaces.DzIter i g z θ := by
  have hfg : (fun z' : ℝ => f z' θ) = fun z' : ℝ => g z' θ := funext fun z' => h z'
  rw [congrFun (Work.FTS.LocData.Zop_iterate_slice i f θ) z,
      congrFun (Work.FTS.LocData.Zop_iterate_slice i g θ) z, hfg]

/-! ## Additivity of `D_z`-iterates over differences -/

/-- **The iterated `D_z`-operator is additive over differences** on the open quadrant, for
`SmoothOpen` data: the same induction as for `SmoothOpen.DzIter_add`, with `deriv_sub`. -/
theorem estDzIter_sub {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter i (fun z θ => f z θ - g z θ) z θ
        = Work.Spaces.DzIter i f z θ - Work.Spaces.DzIter i g z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => f z θ - g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter n f z' θ - Work.Spaces.DzIter n g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n f z' θ) z :=
        ((hf.DzIter n).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n g z' θ) z :=
        ((hg.DzIter n).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd : deriv (fun z' => Work.Spaces.DzIter n f z' θ - Work.Spaces.DzIter n g z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n f z' θ) z
            - deriv (fun z' => Work.Spaces.DzIter n g z' θ) z := deriv_sub hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- The `Ω_n`-part of `Good` is exactly `omegaInd · HkIntegrand`. -/
theorem estOmegaPart_eq (α : ℝ) (k n : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ
      = Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
        * Work.Spaces.HkIntegrand α k F z θ := by
  rw [Work.FTS.PhiStar.Honesty.CptApp.omegaPart,
      Work.FTS.PhiStar.Honesty.CptApp.omegaInd]
  split_ifs <;> ring

/-- The `Ω_n`-part of `Good` is dominated by `Good`. -/
theorem estOmegaPart_le_Good (α : ℝ) (k n : ℕ) (F : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ
      ≤ Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
  rw [Work.FTS.PhiStar.Honesty.CptApp.Good]
  have h1 : 0 ≤ Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ
      * (∑ s ∈ Finset.range k, (Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    mul_nonneg (Work.FTS.PhiStar.Honesty.CptApp.thShrink_nonneg n θ)
      (Work.FTS.PhiStar.Honesty.CptApp.hkZsum_nonneg α k F z hθ)
  have h2 : 0 ≤ (∑ m ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2)
      * ((Work.Spaces.w z) ^ 2 * Work.FTS.PhiStar.Honesty.CptApp.rhoProf α k θ) :=
    mul_nonneg (Finset.sum_nonneg fun m _ => sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (Work.FTS.PhiStar.Honesty.CptApp.rhoProf_nonneg α k hθ))
  linarith

/-- **Abstract `(χζ−1)·F` slot bound.**  Given a family of multipliers `A n`, whose
`D_z`-jets are bounded by `K b` inside the shrinking region `Ω n` and whose Leibniz
expansion holds, the corresponding `D_z`-slots of `A n · F` are dominated by `Good`. -/
theorem estASlot_general (k : ℕ) (A : ℕ → ℝ → ℝ → ℝ) (K : ℕ → ℝ) (hKnn : ∀ b : ℕ, 0 ≤ K b)
    (hAB : ∀ (n b : ℕ), 2 ≤ n → ∀ (z θ : ℝ),
      |Work.Spaces.DzIter b (A n) z θ| ≤ K b * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ)
    (hExp : ∀ (F : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen F → ∀ (n i : ℕ) (z θ : ℝ),
      0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.DzIter i (fun z θ => A n z θ * F z θ) z θ
        = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Spaces.DzIter b (A n) z θ * Work.Spaces.DzIter (i - b) F z θ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → 3 ≤ n →
        Work.FTS.EllipticEst.SmoothOpen F →
        ∀ (i : ℕ), i ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
          (Work.Spaces.DzIter i (fun z θ => A n z θ * F z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ C * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
  set Bc : ℕ → ℝ := fun i' => ((i' : ℝ) + 1) * ∑ b ∈ Finset.range (i' + 1),
      ((i'.choose b : ℝ) ^ 2 * (K b) ^ 2) with hBc
  have hBcnn : ∀ i' : ℕ, 0 ≤ Bc i' := by
    intro i'
    rw [hBc]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun b _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hBsum : 0 ≤ ∑ i' ∈ Finset.range (k + 1), Bc i' :=
    Finset.sum_nonneg fun i' _ => hBcnn i'
  refine ⟨1 + ∑ i' ∈ Finset.range (k + 1), Bc i', by linarith, ?_⟩
  intro α n F hα hα1 hn hsm i hi z hz θ hθ
  have hn2 : 2 ≤ n := by omega
  set Wz := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hWz
  have hWz0 : 0 ≤ Wz := by
    rw [hWz]
    exact div_nonneg (Work.FTS.PhiStar.Honesty.CptApp.w_nonneg z)
      (Real.rpow_nonneg (Work.FTS.PhiStar.Honesty.CptApp.sin_two_nonneg_of_mem_Iθ hθ) _)
  have hOPnn : 0 ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ :=
    Work.FTS.PhiStar.Honesty.CptApp.omegaPart_nonneg α k n F z θ
  have hBle : Bc i ≤ 1 + ∑ i' ∈ Finset.range (k + 1), Bc i' := by
    have hmem : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    have h := Finset.single_le_sum (f := Bc) (fun i' _ => hBcnn i') hmem
    linarith
  have hCA : 0 ≤ 1 + ∑ i' ∈ Finset.range (k + 1), Bc i' := by linarith
  suffices hmain : (Work.Spaces.DzIter i (fun z θ => A n z θ * F z θ) z θ * Wz) ^ 2
      ≤ (1 + ∑ i' ∈ Finset.range (k + 1), Bc i')
        * Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ by
    exact le_trans hmain (mul_le_mul_of_nonneg_left (estOmegaPart_le_Good α k n F hθ) hCA)
  by_cases hz0 : z = 0
  · have h0 : Wz = 0 := by rw [hWz, hz0, Work.Spaces.w]; norm_num
    rw [h0, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact mul_nonneg hCA hOPnn
  · by_cases hs : Real.sin (2 * θ) = 0
    · have hsin : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
        rw [hs]; exact Real.zero_rpow (by norm_num [Work.Spaces.eta])
      have h0 : Wz = 0 := by rw [hWz, hsin, div_zero]
      rw [h0, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      exact mul_nonneg hCA hOPnn
    · have hzpos : 0 < z := lt_of_le_of_ne (show (0 : ℝ) ≤ z from hz) (Ne.symm hz0)
      have hθpos : 0 < θ := by
        rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
        rcases lt_or_eq_of_le hθ.1 with h | h
        · exact h
        · exfalso; apply hs; rw [← h]; norm_num
      have hθlt : θ < Real.pi / 2 := by
        rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
        rcases lt_or_eq_of_le hθ.2 with h | h
        · exact h
        · exfalso; apply hs
          rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      rw [hExp F hsm n i z θ hzpos ⟨hθpos, hθlt⟩]
      have hω0 : 0 ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ :=
        Work.FTS.PhiStar.Honesty.CptApp.omegaInd_nonneg n z θ
      have hω1 : Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ ≤ 1 :=
        Work.FTS.PhiStar.Honesty.CptApp.omegaInd_le_one n z θ
      have hsum_bound : |∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Spaces.DzIter b (A n) z θ * Work.Spaces.DzIter (i - b) F z θ)|
          ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
            * ∑ b ∈ Finset.range (i + 1),
                ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ|) := by
        calc |∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Spaces.DzIter b (A n) z θ * Work.Spaces.DzIter (i - b) F z θ)|
            ≤ ∑ b ∈ Finset.range (i + 1), |(i.choose b : ℝ)
                * (Work.Spaces.DzIter b (A n) z θ * Work.Spaces.DzIter (i - b) F z θ)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ b ∈ Finset.range (i + 1),
                Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
                  * ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ|) := by
              refine Finset.sum_le_sum fun b _ => ?_
              have hcb : (0 : ℝ) ≤ (i.choose b : ℝ) := Nat.cast_nonneg _
              rw [abs_mul, abs_mul, abs_of_nonneg hcb]
              calc (i.choose b : ℝ) * (|Work.Spaces.DzIter b (A n) z θ|
                    * |Work.Spaces.DzIter (i - b) F z θ|)
                  ≤ (i.choose b : ℝ)
                      * ((K b * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ)
                          * |Work.Spaces.DzIter (i - b) F z θ|) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_right (hAB n b hn2 z θ) (abs_nonneg _)) hcb
                _ = Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
                      * ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ|) := by ring
          _ = Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
                * ∑ b ∈ Finset.range (i + 1),
                    ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ|) := by
              rw [Finset.mul_sum]
      have hSmul : (∑ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ|)) * Wz
          = ∑ b ∈ Finset.range (i + 1),
              ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz) :=
        Finset.sum_mul _ _ _
      have hS2Sq : (∑ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz)) ^ 2
          ≤ Bc i * Work.Spaces.HkIntegrand α k F z θ := by
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
          (f := fun b => (i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz)
        have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
          rw [Finset.card_range]; push_cast; ring
        have hterm : ∀ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz) ^ 2
              ≤ (i.choose b : ℝ) ^ 2 * (K b) ^ 2 * Work.Spaces.HkIntegrand α k F z θ := by
          intro b hb
          have hb' : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
          have hik : i - b ≤ k := by omega
          have hHI := Work.Spaces.sq_le_HkIntegrand_z α k F z θ (i - b) hik
          have hnn : 0 ≤ (i.choose b : ℝ) ^ 2 * (K b) ^ 2 :=
            mul_nonneg (sq_nonneg _) (sq_nonneg _)
          have heq : ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz) ^ 2
              = (i.choose b : ℝ) ^ 2 * (K b) ^ 2
                * (Work.Spaces.DzIter (i - b) F z θ * Wz) ^ 2 := by
            rw [mul_pow, mul_pow, mul_pow, sq_abs]; ring
          rw [heq]
          exact mul_le_mul_of_nonneg_left hHI hnn
        calc (∑ b ∈ Finset.range (i + 1),
              ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz)) ^ 2
            ≤ ((Finset.range (i + 1)).card : ℝ)
                * ∑ b ∈ Finset.range (i + 1),
                    ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz) ^ 2 :=
              hcs
          _ ≤ ((i : ℝ) + 1)
                * ∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ) ^ 2 * (K b) ^ 2
                    * Work.Spaces.HkIntegrand α k F z θ) := by
              rw [hcard]
              exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
          _ = Bc i * Work.Spaces.HkIntegrand α k F z θ := by
              rw [hBc]
              rw [← Finset.sum_mul]
              ring
      calc ((∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
              * (Work.Spaces.DzIter b (A n) z θ * Work.Spaces.DzIter (i - b) F z θ)) * Wz) ^ 2
          = (|∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
                * (Work.Spaces.DzIter b (A n) z θ * Work.Spaces.DzIter (i - b) F z θ)| * Wz) ^ 2 := by
              rw [← sq_abs ((∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
                * (Work.Spaces.DzIter b (A n) z θ * Work.Spaces.DzIter (i - b) F z θ)) * Wz),
                abs_mul, abs_of_nonneg hWz0]
        _ ≤ (Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
              * (∑ b ∈ Finset.range (i + 1),
                  ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz))) ^ 2 := by
              refine pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hWz0) ?_ 2
              rw [← hSmul]
              exact le_trans (mul_le_mul_of_nonneg_right hsum_bound hWz0) (le_of_eq (by ring))
        _ ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
              * (∑ b ∈ Finset.range (i + 1),
                  ((i.choose b : ℝ) * K b * |Work.Spaces.DzIter (i - b) F z θ| * Wz)) ^ 2 := by
              rw [mul_pow]
              have hω2 : Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ ^ 2
                  ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ := by nlinarith
              exact mul_le_mul_of_nonneg_right hω2 (sq_nonneg _)
        _ ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
              * (Bc i * Work.Spaces.HkIntegrand α k F z θ) :=
              mul_le_mul_of_nonneg_left hS2Sq hω0
        _ = Bc i * Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ := by
              rw [show Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
                    * (Bc i * Work.Spaces.HkIntegrand α k F z θ)
                  = Bc i * (Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
                    * Work.Spaces.HkIntegrand α k F z θ) by ring,
                ← estOmegaPart_eq α k n F z θ]
        _ ≤ (1 + ∑ i' ∈ Finset.range (k + 1), Bc i')
              * Work.FTS.PhiStar.Honesty.CptApp.omegaPart α k n F z θ :=
              mul_le_mul_of_nonneg_right hBle hOPnn

/-- The `(χζ−1)·F` slot of the error, from the two delegated ingredients. -/
theorem estASlot_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → 3 ≤ n →
      Work.FTS.EllipticEst.SmoothOpen F →
      ∀ (i : ℕ), i ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        (Work.Spaces.DzIter i (fun z θ => (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) * F z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ C * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
  obtain ⟨K, hKnn, hKbd⟩ := Work.FTS.PhiStar.Honesty.CptApp.EstAux.errAdjBound
  exact estASlot_general k (fun n z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
      * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) K hKnn hKbd
    (fun F hsm n i z θ hz hθ => Work.FTS.PhiStar.Honesty.CptApp.EstAux.errASlot_expand hsm n i hz hθ)

/-! ## The two halves of the error (delegated) -/

/-- The moment-correction slot of the error (delegated to `EstAux.errMSlot_le`):
`(D_z^i (mu n F · rho) · w/sin(2θ)^{η/2})² ≤ C · Good α k n F`. -/
theorem estMSlot_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → 3 ≤ n →
      Work.FTS.EllipticEst.SmoothOpen F →
      ∀ (i : ℕ), i ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        (Work.Spaces.DzIter i (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z
            * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ C * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ :=
  Work.FTS.PhiStar.Honesty.CptApp.EstAux.errMSlot_le k

/-! ## The main estimate -/

theorem err_dzSlot_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → 3 ≤ n →
      Work.FTS.EllipticEst.SmoothOpen F →
      ∀ (i : ℕ), i ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        (Work.Spaces.DzIter i (Work.FTS.PhiStar.Honesty.CptApp.err n F) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ C * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
  obtain ⟨C₁, hC₁pos, hA⟩ := estASlot_le k
  obtain ⟨C₂, hC₂pos, hM⟩ := estMSlot_le k
  refine ⟨2 * (C₁ + C₂) + 1, by linarith, ?_⟩
  intro α n F hα hα1 hn hsm i hi z hz θ hθ
  have hn1 : 1 ≤ n := by omega
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · -- `z = 0`: the weight `w 0 = 0` kills the slot
    rw [← hz0, Work.Spaces.w]
    have hL : (Work.Spaces.DzIter i (Work.FTS.PhiStar.Honesty.CptApp.err n F) 0 θ
        * ((1 + 0) ^ 2 / 0 ^ 2
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
      norm_num
    rw [hL]
    exact mul_nonneg (by linarith) (Work.FTS.PhiStar.Honesty.CptApp.Good_nonneg α k n F hθ)
  · by_cases hs : Real.sin (2 * θ) = 0
    · -- `θ ∈ {0, π/2}`: the angular weight vanishes
      have hsin : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
        rw [hs]; exact Real.zero_rpow (by norm_num [Work.Spaces.eta])
      have hL : (Work.Spaces.DzIter i (Work.FTS.PhiStar.Honesty.CptApp.err n F) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
        rw [hsin, div_zero, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      rw [hL]
      exact mul_nonneg (by linarith) (Work.FTS.PhiStar.Honesty.CptApp.Good_nonneg α k n F hθ)
    · -- the interior of the quadrant: `0 < θ < π/2`
      have hθpos : 0 < θ := by
        rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
        rcases lt_or_eq_of_le hθ.1 with h | h
        · exact h
        · exfalso; apply hs; rw [← h]; norm_num
      have hθlt : θ < Real.pi / 2 := by
        rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
        rcases lt_or_eq_of_le hθ.2 with h | h
        · exact h
        · exfalso; apply hs
          rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      -- the two summands of `err`
      have hdec := estDzIter_sub
        (Work.FTS.PhiStar.Honesty.CptApp.EstAux.smoothOpen_chiZeta_sub_one hsm n)
        (Work.FTS.PhiStar.Honesty.CptApp.EstAux.smoothOpen_muRho hsm hn1) i z θ hzpos hθpos hθlt
      have hpoint : ∀ z' : ℝ, Work.FTS.PhiStar.Honesty.CptApp.err n F z' θ
          = (fun z θ => (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
              * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) * F z θ) z' θ
            - (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z
              * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z' θ := by
        intro z'
        simp only [Work.FTS.PhiStar.Honesty.CptApp.err, Work.FTS.PhiStar.Honesty.CptApp.approx,
          Work.FTS.PhiStar.Honesty.CptApp.mu]
        ring
      have hXeq : Work.Spaces.DzIter i (Work.FTS.PhiStar.Honesty.CptApp.err n F) z θ
          = Work.Spaces.DzIter i (fun z θ => (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) * F z θ) z θ
            - Work.Spaces.DzIter i (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z
                * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z θ := by
        rw [← hdec]
        exact estDzIter_congr_slice i (θ := θ) hpoint z
      set X := Work.Spaces.DzIter i (fun z θ => (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) * F z θ) z θ with hXdef
      set Y := Work.Spaces.DzIter i (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z
          * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z θ with hYdef
      set Wz := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hWdef
      have hGnn : 0 ≤ Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ :=
        Work.FTS.PhiStar.Honesty.CptApp.Good_nonneg α k n F hθ
      have hXq : Work.Spaces.DzIter i (Work.FTS.PhiStar.Honesty.CptApp.err n F) z θ
          = X - Y := hXeq
      have hA' : (X * Wz) ^ 2
          ≤ C₁ * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ :=
        hA α n F hα hα1 hn hsm i hi z hz θ hθ
      have hM' : (Y * Wz) ^ 2
          ≤ C₂ * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ :=
        hM α n F hα hα1 hn hsm i hi z hz θ hθ
      calc (Work.Spaces.DzIter i (Work.FTS.PhiStar.Honesty.CptApp.err n F) z θ * Wz) ^ 2
          = ((X - Y) * Wz) ^ 2 := by rw [hXq]
        _ = (X * Wz - Y * Wz) ^ 2 := by ring
        _ ≤ 2 * (X * Wz) ^ 2 + 2 * (Y * Wz) ^ 2 := by
              nlinarith [sq_nonneg (X * Wz + Y * Wz)]
        _ ≤ 2 * (C₁ * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ)
              + 2 * (C₂ * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ) := by
              linarith [mul_le_mul_of_nonneg_left hA' (by norm_num : (0 : ℝ) ≤ 2),
                mul_le_mul_of_nonneg_left hM' (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ (2 * (C₁ + C₂) + 1) * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
              nlinarith [hGnn]

end Work.FTS.PhiStar.Honesty.CptApp.Est
