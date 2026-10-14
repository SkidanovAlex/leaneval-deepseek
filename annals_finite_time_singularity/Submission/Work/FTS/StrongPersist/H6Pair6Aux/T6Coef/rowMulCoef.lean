import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.mulTermLarge
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.mulTermSmall
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCoefCase
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.summand_le_easy
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.c2mGam_Wt_bound
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMul6Cont
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.HProductRule_bad_term
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SepParts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2400000

/-! ## The one-variable `dthU`-calculus -/

/-- `dthU` is linear in the constant: `dthU (c·g) = c·dthU g`. -/
theorem dthU_const_mul (c : ℝ) (g : ℝ → ℝ) :
    Work.Spaces.dthU (fun θ => c * g θ) = fun θ => c * Work.Spaces.dthU g θ := by
  funext θ
  simp only [Work.Spaces.dthU_apply, deriv_const_mul_field]
  ring

/-- The iterate of `dthU` is linear in the constant. -/
theorem dthU_iter_const_mul (c : ℝ) (g : ℝ → ℝ) (i : ℕ) :
    (Work.Spaces.dthU^[i]) (fun θ => c * g θ)
      = fun θ => c * (Work.Spaces.dthU^[i]) g θ := by
  induction i generalizing g with
  | zero => rfl
  | succ n ih =>
      show (Work.Spaces.dthU^[n]) (Work.Spaces.dthU (fun θ => c * g θ))
        = fun θ => c * (Work.Spaces.dthU^[n]) (Work.Spaces.dthU g) θ
      rw [dthU_const_mul c g]
      exact ih (Work.Spaces.dthU g)

/-- At a point where `sin(2θ) = 0` every positive iterate of `dthU` vanishes. -/
theorem dthU_iter_eq_zero_of_sin_eq_zero {g : ℝ → ℝ} {θ : ℝ} (i : ℕ) (hi : 1 ≤ i)
    (h : Real.sin (2 * θ) = 0) : (Work.Spaces.dthU^[i]) g θ = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Function.iterate_succ_apply']
  simp only [Work.Spaces.dthU_apply, h, zero_mul]

/-- `(sin(2θ)^κ)² = sin(2θ)^{2κ}` on the open interval. -/
theorem sq_sin_rpow {κ θ : ℝ} (hs : 0 < Real.sin (2 * θ)) :
    ((Real.sin (2 * θ)) ^ κ) ^ 2 = (Real.sin (2 * θ)) ^ (2 * κ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hs)]
  congr 1
  ring

/-- `|c2m θ| ≤ 2` for every `θ`. -/
theorem abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  rw [Work.Construction.c2m_eq]
  calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
      = |Real.cos (2 * θ) + -(Real.sin θ ^ 2)| := by ring_nf
    _ ≤ |Real.cos (2 * θ)| + |-(Real.sin θ ^ 2)| := abs_add_le _ _
    _ = |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := by rw [abs_neg]
    _ ≤ 1 + 1 := by
        have hs : |Real.sin θ ^ 2| ≤ 1 := by
          rw [abs_of_nonneg (sq_nonneg _)]
          exact Real.sin_sq_le_one θ
        have hc := Real.abs_cos_le_one (2 * θ)
        linarith
    _ = 2 := by norm_num

/-- **The angular reduction.**  It suffices to bound the `dthU`-iterates of an angular
profile on the *open* interval `(0,π/2)`: at the two endpoints every positive iterate
vanishes, and so does `sin(2θ)^{2κ}`. -/
theorem dthU_iter_sq_le_sin_aux {a : ℝ → ℝ} {κ B1 : ℝ} (hκ : 0 < κ)
    (hint : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ((Work.Spaces.dthU^[i]) a θ) ^ 2 ≤ B1 * (Real.sin (2 * θ)) ^ (2 * κ)) :
    ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      ((Work.Spaces.dthU^[i]) a θ) ^ 2 ≤ B1 * (Real.sin (2 * θ)) ^ (2 * κ) := by
  intro i hi1 hi6 θ hθ
  by_cases hθo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  · exact hint i hi1 hi6 θ hθo
  · have hs : Real.sin (2 * θ) = 0 := sin_two_zero_of_not_Ioo hθ hθo
    rw [dthU_iter_eq_zero_of_sin_eq_zero i hi1 hs, hs,
      Real.zero_rpow (ne_of_gt (by linarith : (0 : ℝ) < 2 * κ))]
    simp

/-! ## The radial profile `φ = FM.Fstar = 2z/(1+z)²` -/

/-- All finite orders of smoothness of `φ` on `(0,∞)`. -/
theorem Fstar_contDiffOn : ∀ m : ℕ, ContDiffOn ℝ m Work.FM.Fstar (Set.Ioi 0) := by
  intro m
  have h1 : ContDiffOn ℝ m (fun z : ℝ => 2 * z) (Set.Ioi 0) :=
    contDiffOn_const.mul contDiffOn_id
  show ContDiffOn ℝ m (fun z : ℝ => 2 * z / (1 + z) ^ 2) (Set.Ioi 0)
  exact h1.div ((contDiffOn_const.add contDiffOn_id).pow 2)
    (fun z hz => by have hz' : (0 : ℝ) < z := hz; positivity)

/-- All finite orders of smoothness of the first `D_z`-jet of `φ`. -/
theorem Fstar_shift_contDiffOn :
    ∀ n : ℕ, ContDiffOn ℝ n (fun z => Work.Elliptic.DzdIter 1 Work.FM.Fstar z) (Set.Ioi 0) := by
  intro n
  exact Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial
    (r := Work.FM.Fstar) (n := n + 1) (fun m _ => Fstar_contDiffOn m)
    (a := 1) (t := n) (by omega)

/-- **The `z`-jet bounds of `φ` and of its first jet.**  `DzdIter m φ = DzdIter (m-1) (DzdIter 1 φ)`
as functions, so the order-seven bound of `FstarJet7` transfers to the shifted family. -/
theorem Fstar_jets_shift (M₂ : ℝ)
    (hM₂ : ∀ j : ℕ, j ≤ 7 → ∀ z : ℝ, 0 ≤ z → |Work.Elliptic.DzdIter j Work.FM.Fstar z| ≤ M₂) :
    (∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 ≤ z → |Work.Elliptic.DzdIter j Work.FM.Fstar z| ≤ M₂) ∧
      (∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter j (fun z => Work.Elliptic.DzdIter 1 Work.FM.Fstar z) z| ≤ M₂) := by
  have hshift : ∀ m : ℕ, Work.Elliptic.DzdIter m
      (fun z => Work.Elliptic.DzdIter 1 Work.FM.Fstar z)
        = Work.Elliptic.DzdIter (m + 1) Work.FM.Fstar := by
    intro m
    induction m with
    | zero => rfl
    | succ k ih =>
        rw [Work.Elliptic.DzdIter_succ, ih, Work.Elliptic.DzdIter_succ]
        rfl
  exact ⟨fun j hj z hz => hM₂ j (by omega) z hz,
    fun j hj z hz => by rw [hshift j]; exact hM₂ (j + 1) (by omega) z (le_of_lt hz)⟩


/-- The `-c2m(θ)·D_z f`-field is honest in `ℋ⁶` (`c2m = cos 2θ - sin²θ = -1 + 3sin²θ`). -/
theorem c2m_Dz_mem {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (m7 : Work.Spaces.HkMem α 7 f) :
    Work.Spaces.HkMem α 6 (fun z θ => -(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ) := by
  have hDzmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dz f) :=
    Work.FTS.IPGen.HkMem_Dz_le hf m7
  have hsin2sm : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Real.sin θ ^ 2) :=
    so_snd ((Real.contDiff_sin).pow 2)
  obtain ⟨_, _, hmul⟩ := Work.Blocks.HkMul_ang_le 6
  obtain ⟨-, -, hmain⟩ := hmul α (Work.Spaces.Dz f) hα hα1 hf.Dz
  obtain ⟨-, -, hs2mem, -⟩ := hmain hDzmem
  have h1 : Work.Spaces.HkMem α 6 (fun z θ => (-1 : ℝ) * Work.Spaces.Dz f z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 (-1) hDzmem
  have h2 : Work.Spaces.HkMem α 6
      (fun z θ => (3 : ℝ) * (Real.sin θ ^ 2 * Work.Spaces.Dz f z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 6 3 hs2mem
  have hsm1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-1 : ℝ) * Work.Spaces.Dz f z θ) :=
    so_const_mul (-1) hf.Dz
  have hsm2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 : ℝ) * (Real.sin θ ^ 2 * Work.Spaces.Dz f z θ)) :=
    so_const_mul 3 (so_mul hsin2sm hf.Dz)
  have hsum := Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 6 hsm1 hsm2 h1 h2
  refine Work.Coercivity.HkMem_congr_Ioi α 6 hsum ?_
  intro z hz θ hθ
  rw [Work.Construction.c2m_eq, Real.cos_two_mul, Real.sin_sq]
  ring

/-! ## The term `N04a` -/


/-! ## The term `N05a` -/


/-! ## The term `N06` -/


end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.rowMulCoef =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

/-- **The level-six `A · f` coefficient row.**  The slot pairing of the product `A · f` against
the datum `f` is bounded by `C·α^{-3}` times the two `L²`-prices of the coefficient `A`
(`K0`, `K4`) against the `ℋ⁶`-energy of `f`, plus the `ℋ⁶`-price `K6` against the
`a`-priori bound `M` of `Xn α f`.

Assembled in `rowMulAsm` from the Leibniz expansion `mulExpansion` and the two per-summand
bounds `mulTermSmall` (`a₁ + b₁ ≤ 2`) and `mulTermLarge` (`3 ≤ a₁ + b₁`). -/
theorem rowMulCoef : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * f z θ) f|
        ≤ C * α ^ (-(3 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
  rowMulAsm mulExpansion mulTermSmall mulTermLarge

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
