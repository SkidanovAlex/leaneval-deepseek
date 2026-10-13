/-
# `Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG.nsumG2`

Piece bounds for the three "star coefficient × datum slot" pieces of the level-six `N`-row:
`nsP1 = 2·Rop(PhiTs α Φs)·f`, `nsP5 = -2·(Uop(PhiTs α Φs)/s2)·D_θf`,
`nsP9 = -2α·Vop(PhiTs α Φs)·D_zf`.

## Route

* `nsP1`, `nsP5`: the flat star-price rows `rowStarFam` (`A · f` and `A · D_θf`), with the
  coefficient `A` a scalar multiple of one of the star fields of `StarPkg6`; `starDat` supplies
  `SmoothOpen` and the pointwise price
  `|D_z^jD_θ^iA| ≤ C·(Cs·α)·z/(1+z)·(α+σ)σ^{α/5}`, and scalar multiples are handled by
  `mixed_const_mul`.
* `nsP9`: the `D_z`-slot row `rowDzWlInfFlat` with the coefficient `A = -2α·Vop(PhiTs α Φs)`;
  its hypotheses are `SmoothOpen` (from `starDat`), the `𝒲^{6,∞}`-membership and its bound
  (`StarPkg6.VW6`, scaled by `WlInf_const_mul_le_abs`), and the three flat `∂_θA`-bounds
  supplied by `StarPkgo.Vth : CoefThMem 3 (Vop (PhiTs α Φs))` together with `supAbsO_le_coefTh`.

The datum data is `T6Coef.DatData α (slice g τ) M` from `L6Ctx` (`datData_of_H6Adm`), and the
final `α^{-10}(1+|Ce|+|Cs|)^4(1+M)^4`-budget is the coarse form of the rows' `α^{-3}`/`α^{-4}`
prices (`arith_fam`, `arith_dz` below).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.starDat
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowDzWlInfFlat
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.rowDthWlInf
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.rowMulCoef
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowStarFam
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0coefA4_WlInf6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongPersist.H6Rows.Npair6SupAux
open Work.FTS.StrongPersist.H6Rows.N0pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Scalar multiples: the operators and the flat norms -/

/-- Scalar multiplication commutes with `D_z` (unconditionally: `deriv_const_mul_field`). -/
theorem Dz_const_mul (c : ℝ) (h : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * h z θ) = fun z θ => c * Work.Spaces.Dz h z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [deriv_const_mul_field]
  ring

/-- Scalar multiplication commutes with the iterated `D_z`. -/
theorem DzIter_const_mul (c : ℝ) (h : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => c * h z θ) = fun z θ => c * Work.Spaces.DzIter j h z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, ih]
      exact Dz_const_mul c (Work.Spaces.DzIter j h)

/-- Scalar multiplication commutes with `D_θ`. -/
theorem Dth_const_mul (c : ℝ) (h : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * h z θ) = fun z θ => c * Work.Spaces.Dth h z θ :=
  DthIter_const_mul' c h 1

/-- Scalar multiplication commutes with the mixed operator. -/
theorem mixed_const_mul (c : ℝ) (g : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => c * g z θ) = fun z θ => c * Work.Spaces.mixed j i g z θ := by
  unfold Work.Spaces.mixed
  rw [DthIter_const_mul', DzIter_const_mul]

/-- `supAbs` scales by `|c|`. -/
theorem supAbs_const_mul_le_abs {g : ℝ → ℝ → ℝ} (c : ℝ) (hg : Work.Spaces.SupFinite g) :
    Work.Spaces.supAbs (fun z θ => c * g z θ) ≤ |c| * Work.Spaces.supAbs g := by
  refine Work.Spaces.supAbs_le fun z hz θ hθ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (Work.Spaces.abs_le_supAbs hz hθ hg) (abs_nonneg c)

/-- The `𝒲^{l,∞}`-norm scales by `|c|`. -/
theorem WlInf_const_mul_le_abs {α : ℝ} {l : ℕ} {f : ℝ → ℝ → ℝ} (c : ℝ)
    (hmem : Work.Spaces.WlInfMem α l f) :
    Work.Spaces.WlInf α l (fun z θ => c * f z θ) ≤ |c| * Work.Spaces.WlInf α l f := by
  have hZ : (∑ k ∈ Finset.range (l + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => c * f z θ) z θ))
      ≤ |c| * ∑ k ∈ Finset.range (l + 1),
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' : k ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [show (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => c * f z θ) z θ)
          = fun z θ => c * ((z + 1) ^ k * Work.Spaces.pzIter k f z θ) from by
        funext z θ; rw [pzIter_const_mul']; ring]
    exact supAbs_const_mul_le_abs c (hmem.1 k hk')
  have hM : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        if 1 ≤ j ∧ k + j ≤ l then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => c * f z θ)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0)
      ≤ |c| * ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        (if 1 ≤ j ∧ k + j ≤ l then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    by_cases hcond : 1 ≤ j ∧ k + j ≤ l
    · rw [if_pos hcond, if_pos hcond]
      rw [show (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => c * f z θ)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          = fun z θ => c * ((z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) from by
        funext z θ
        rw [DthIter_const_mul', pzIter_const_mul']
        ring]
      exact supAbs_const_mul_le_abs c (hmem.2 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
        k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hcond.1 hcond.2)
    · rw [if_neg hcond, if_neg hcond, mul_zero]
  rw [Work.Spaces.WlInf, Work.Spaces.WlInf, mul_add]
  exact add_le_add hZ hM

/-! ## The arithmetic conversions

Both are the coarse form of a row price: `α^{-3}` resp. `α^{-4}` is bounded by `α^{-10}`,
`(1+M)` by `(1+M)^4`, and the `(1+|Ce|+|Cs|)^4`-factor absorbs the star prices. -/

theorem arith_fam {α M Cs Ce C1 C3 KA W : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hC1 : 0 ≤ C1) (hKA0 : 0 ≤ KA) (hC3 : 0 ≤ C3)
    (hKA : 1 + KA ≤ (1 + 2 * C3) * (1 + |Ce| + |Cs|) ^ 4)
    (hM : 0 ≤ M) (hW : 0 ≤ W) :
    C1 * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M) * W
      ≤ (C1 * (1 + 2 * C3)) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * W := by
  have hα3 : α ^ (-(3 : ℝ)) ≤ α ^ (-(10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hαnn : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hXnn : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
  have hM4nn : 0 ≤ (1 + M) ^ 4 := by positivity
  have hM4 : 1 + M ≤ (1 + M) ^ 4 := by
    have h1 : (1 : ℝ) ≤ 1 + M := by linarith
    nlinarith [sq_nonneg (1 + M), sq_nonneg ((1 + M) ^ 2 - 1)]
  have hA : 0 ≤ (1 + 2 * C3) * (1 + |Ce| + |Cs|) ^ 4 := mul_nonneg (by linarith) hXnn
  have hstep1 : C1 * α ^ (-(3 : ℝ)) ≤ C1 * α ^ (-(10 : ℝ)) :=
    mul_le_mul_of_nonneg_left hα3 hC1
  have hstep2 : C1 * α ^ (-(3 : ℝ)) * (1 + KA)
      ≤ C1 * α ^ (-(10 : ℝ)) * ((1 + 2 * C3) * (1 + |Ce| + |Cs|) ^ 4) :=
    mul_le_mul hstep1 hKA (by linarith) (mul_nonneg hC1 hαnn)
  have hstep3 : C1 * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M)
      ≤ C1 * α ^ (-(10 : ℝ)) * ((1 + 2 * C3) * (1 + |Ce| + |Cs|) ^ 4) * (1 + M) ^ 4 :=
    mul_le_mul hstep2 hM4 (by linarith) (mul_nonneg (mul_nonneg hC1 hαnn) hA)
  have hstep4 := mul_le_mul hstep3 (le_refl W) hW
    (mul_nonneg (mul_nonneg (mul_nonneg hC1 hαnn) hA) hM4nn)
  calc C1 * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M) * W
      ≤ C1 * α ^ (-(10 : ℝ)) * ((1 + 2 * C3) * (1 + |Ce| + |Cs|) ^ 4) * (1 + M) ^ 4 * W :=
        hstep4
    _ = (C1 * (1 + 2 * C3)) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * W := by
        ring

theorem arith_dz {α M Cs Ce C2 K Kf W : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hC2 : 0 ≤ C2) (hK0 : 0 ≤ K) (hKf0 : 0 ≤ Kf)
    (hK : 1 + K + Kf ≤ 5 * (1 + |Ce| + |Cs|) ^ 4)
    (hM : 0 ≤ M) (hW : 0 ≤ W) :
    C2 * α ^ (-(4 : ℝ)) * (1 + K + Kf) * (1 + M) * W
      ≤ (5 * C2) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * W := by
  have hα4 : α ^ (-(4 : ℝ)) ≤ α ^ (-(10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hαnn : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hXnn : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
  have hM4nn : 0 ≤ (1 + M) ^ 4 := by positivity
  have hM4 : 1 + M ≤ (1 + M) ^ 4 := by
    have h1 : (1 : ℝ) ≤ 1 + M := by linarith
    nlinarith [sq_nonneg (1 + M), sq_nonneg ((1 + M) ^ 2 - 1)]
  have hA : 0 ≤ 5 * (1 + |Ce| + |Cs|) ^ 4 := mul_nonneg (by norm_num) hXnn
  have hstep1 : C2 * α ^ (-(4 : ℝ)) ≤ C2 * α ^ (-(10 : ℝ)) :=
    mul_le_mul_of_nonneg_left hα4 hC2
  have hstep2 : C2 * α ^ (-(4 : ℝ)) * (1 + K + Kf)
      ≤ C2 * α ^ (-(10 : ℝ)) * (5 * (1 + |Ce| + |Cs|) ^ 4) :=
    mul_le_mul hstep1 hK (by linarith) (mul_nonneg hC2 hαnn)
  have hstep3 : C2 * α ^ (-(4 : ℝ)) * (1 + K + Kf) * (1 + M)
      ≤ C2 * α ^ (-(10 : ℝ)) * (5 * (1 + |Ce| + |Cs|) ^ 4) * (1 + M) ^ 4 :=
    mul_le_mul hstep2 hM4 (by linarith) (mul_nonneg (mul_nonneg hC2 hαnn) hA)
  have hstep4 := mul_le_mul hstep3 (le_refl W) hW
    (mul_nonneg (mul_nonneg (mul_nonneg hC2 hαnn) hA) hM4nn)
  calc C2 * α ^ (-(4 : ℝ)) * (1 + K + Kf) * (1 + M) * W
      ≤ C2 * α ^ (-(10 : ℝ)) * (5 * (1 + |Ce| + |Cs|) ^ 4) * (1 + M) ^ 4 * W := hstep4
    _ = (5 * C2) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * W := by ring

/-- The star price bound: `1 + 2·C₃·(Cs·α) ≤ (1+2C₃)·(1+|Ce|+|Cs|)⁴` for `0 < α ≤ 1`,
`0 ≤ C₃`, `0 ≤ Cs`. -/
theorem one_add_star_price_le {α Cs Ce C3 : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hC3 : 0 ≤ C3)
    (hCs0 : 0 ≤ Cs) :
    1 + 2 * (C3 * (Cs * α)) ≤ (1 + 2 * C3) * (1 + |Ce| + |Cs|) ^ 4 := by
  have hCsα_le : Cs * α ≤ Cs := by
    calc Cs * α ≤ Cs * 1 := mul_le_mul_of_nonneg_left hα1 hCs0
      _ = Cs := by ring
  have h2 : 1 + 2 * (C3 * (Cs * α)) ≤ (1 + 2 * C3) * (1 + Cs) := by
    nlinarith [hCsα_le, hC3, hCs0]
  have hX : 1 + Cs ≤ (1 + |Ce| + |Cs|) ^ 4 := by
    rw [abs_of_nonneg hCs0]
    have h1 : 1 + Cs ≤ 1 + |Ce| + Cs := by linarith [abs_nonneg Ce]
    have hY1 : (1 : ℝ) ≤ 1 + |Ce| + Cs := by linarith
    have hY2 : (1 : ℝ) ≤ (1 + |Ce| + Cs) ^ 2 := by nlinarith [hY1]
    have hY3 : (1 : ℝ) ≤ (1 + |Ce| + Cs) ^ 3 := by nlinarith [hY1, hY2]
    have hY4 : (1 + |Ce| + Cs) ≤ (1 + |Ce| + Cs) ^ 4 := by nlinarith [hY1, hY3]
    linarith
  calc 1 + 2 * (C3 * (Cs * α)) ≤ (1 + 2 * C3) * (1 + Cs) := h2
    _ ≤ (1 + 2 * C3) * (1 + |Ce| + |Cs|) ^ 4 :=
        mul_le_mul_of_nonneg_left hX (by linarith)

/-- The `D_z`-slot price bound: `1 + 2·(2α(Cs·α)) ≤ 5·(1+|Ce|+|Cs|)⁴` for `0 < α ≤ 1`, `0 ≤ Cs`. -/
theorem one_add_dz_price_le {α Cs Ce : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hCs0 : 0 ≤ Cs) :
    1 + 2 * α * (Cs * α) + 2 * α * (Cs * α) ≤ 5 * (1 + |Ce| + |Cs|) ^ 4 := by
  have hαα : α * α ≤ 1 := by nlinarith [hα0, hα1, sq_nonneg α]
  have hKle : 2 * α * (Cs * α) ≤ 2 * Cs := by nlinarith [hα0.le, hα1, hCs0, hαα]
  have hX : 1 + Cs ≤ (1 + |Ce| + |Cs|) ^ 4 := by
    rw [abs_of_nonneg hCs0]
    have h1 : 1 + Cs ≤ 1 + |Ce| + Cs := by linarith [abs_nonneg Ce]
    have hY1 : (1 : ℝ) ≤ 1 + |Ce| + Cs := by linarith
    have hY2 : (1 : ℝ) ≤ (1 + |Ce| + Cs) ^ 2 := by nlinarith [hY1]
    have hY3 : (1 : ℝ) ≤ (1 + |Ce| + Cs) ^ 3 := by nlinarith [hY1, hY2]
    have hY4 : (1 + |Ce| + Cs) ≤ (1 + |Ce| + Cs) ^ 4 := by nlinarith [hY1, hY3]
    linarith
  have h5 : 1 + 4 * Cs ≤ 5 * (1 + Cs) := by linarith
  have hX5 : 5 * (1 + Cs) ≤ 5 * (1 + |Ce| + |Cs|) ^ 4 :=
    mul_le_mul_of_nonneg_left hX (by norm_num)
  nlinarith [hKle, h5, hX5]

theorem nsumG2 (Ce : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn),
      0 ≤ τ →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1)
        α M Ce Cs E Φs g Φ τ →
      ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      (|Work.FTS.TransportS.slotPairing ρ a b (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP1 α Φs (Work.FTS.Galerkin.slice g τ)) (Work.FTS.Galerkin.slice g τ)|
          ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)) ∧
       |Work.FTS.TransportS.slotPairing ρ a b (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP5 α Φs (Work.FTS.Galerkin.slice g τ)) (Work.FTS.Galerkin.slice g τ)|
          ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)) ∧
       |Work.FTS.TransportS.slotPairing ρ a b (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsP9 α Φs (Work.FTS.Galerkin.slice g τ)) (Work.FTS.Galerkin.slice g τ)|
          ≤ C * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
              * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ))) := by
  obtain ⟨C1, hC1pos, hFam⟩ := rowStarFam
  obtain ⟨C2, hC2pos, hDz⟩ := rowDzWlInfFlat
  obtain ⟨C3, hC3pos, hStar⟩ := starDat
  refine ⟨max (C1 * (1 + 2 * C3)) (5 * C2) + 1, by positivity, ?_⟩
  intro α hα g Φ τ M Cs E Φs hτ hctx a b ρ hab hleaf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hCfg1 : C1 * (1 + 2 * C3) ≤ max (C1 * (1 + 2 * C3)) (5 * C2) + 1 :=
    le_trans (le_max_left _ _) (le_add_of_nonneg_right (by norm_num))
  have hCfg2 : 5 * C2 ≤ max (C1 * (1 + 2 * C3)) (5 * C2) + 1 :=
    le_trans (le_max_right _ _) (le_add_of_nonneg_right (by norm_num))
  -- ## the `2·Rop(PhiTs α Φs)·f` piece
  have h1 : |Work.FTS.TransportS.slotPairing ρ a b
        (nsP1 α Φs (Work.FTS.Galerkin.slice g τ)) (Work.FTS.Galerkin.slice g τ)|
      ≤ (max (C1 * (1 + 2 * C3)) (5 * C2) + 1) * α ^ (-(10 : ℝ))
          * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)) := by
    set f : Fn := Work.FTS.Galerkin.slice g τ with hf
    obtain ⟨hRsm, -, -, hprice⟩ := hStar α hα Φs Cs hctx.hstar6
    have hdat : Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M := by
      simpa only [hf] using
        (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.datData_of_H6Adm hctx.hreg hctx.h7 hctx.hbdd)
    have hCsα0 : 0 ≤ Cs * α :=
      le_trans (Work.Spaces.WlInf_nonneg α 6 _ hctx.hstar6.RW6.1) hctx.hstar6.RW6.2
    have hCs0 : 0 ≤ Cs := nonneg_of_mul_nonneg_left hCsα0 hα0
    have hKA0 : 0 ≤ 2 * (C3 * (Cs * α)) :=
      mul_nonneg (by norm_num) (mul_nonneg hC3pos.le (mul_nonneg hCs0 hα0.le))
    have hprice1 : ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (fun z θ => 2 * coefR1 α Φs z θ) z θ|
          ≤ (2 * (C3 * (Cs * α))) * (z / (1 + z)) *
            (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) := by
      intro j i hji z θ hz hθ hθ2
      have hh := hprice (coefR1 α Φs) (Or.inl rfl) j i hji z θ hz hθ hθ2
      have hsplit : Work.Spaces.mixed j i (fun z θ => 2 * coefR1 α Φs z θ) z θ
          = 2 * Work.Spaces.mixed j i (coefR1 α Φs) z θ := by
        simp only [mixed_const_mul]
      rw [hsplit, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc 2 * |Work.Spaces.mixed j i (coefR1 α Φs) z θ|
          ≤ 2 * ((C3 * (Cs * α)) * (z / (1 + z)) *
              (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) :=
            mul_le_mul_of_nonneg_left hh (by norm_num)
        _ = (2 * (C3 * (Cs * α))) * (z / (1 + z)) *
              (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) := by
            ring
    have hrow := (hFam α hα (fun z θ => 2 * coefR1 α Φs z θ) f (2 * (C3 * (Cs * α))) M a b ρ
        (smoothOpen_const_mul 2 hRsm) hdat hprice1 hab hleaf).1
    have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
    have hW0 : 0 ≤ 1 + Work.Spaces.HkSq α 6 f := by
      have := Work.Spaces.HkSq_nonneg α 6 f; linarith
    have hKAle := one_add_star_price_le (Ce := Ce) hα0 hα1 hC3pos.le hCs0
    have hnn : 0 ≤ α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
        * (1 + Work.Spaces.HkSq α 6 f) := by
      have h1 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
      have h2 : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
      have h3 : 0 ≤ (1 + M) ^ 4 := by positivity
      positivity
    refine le_trans hrow ?_
    calc C1 * α ^ (-(3 : ℝ)) * (1 + 2 * (C3 * (Cs * α))) * (1 + M)
          * (1 + Work.Spaces.HkSq α 6 f)
        ≤ (C1 * (1 + 2 * C3)) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) :=
          arith_fam hα0 hα1 hC1pos.le hKA0 hC3pos.le hKAle hM0 hW0
      _ ≤ (max (C1 * (1 + 2 * C3)) (5 * C2) + 1) * α ^ (-(10 : ℝ))
            * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
          calc (C1 * (1 + 2 * C3)) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                * (1 + Work.Spaces.HkSq α 6 f)
              = (C1 * (1 + 2 * C3))
                  * (α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                    * (1 + Work.Spaces.HkSq α 6 f)) := by ring
            _ ≤ (max (C1 * (1 + 2 * C3)) (5 * C2) + 1)
                  * (α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                    * (1 + Work.Spaces.HkSq α 6 f)) :=
                mul_le_mul_of_nonneg_right hCfg1 hnn
            _ = (max (C1 * (1 + 2 * C3)) (5 * C2) + 1) * α ^ (-(10 : ℝ))
                  * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                  * (1 + Work.Spaces.HkSq α 6 f) := by ring
  -- ## the `-2·(Uop(PhiTs α Φs)/s2)·D_θf` piece
  have h5 : |Work.FTS.TransportS.slotPairing ρ a b
        (nsP5 α Φs (Work.FTS.Galerkin.slice g τ)) (Work.FTS.Galerkin.slice g τ)|
      ≤ (max (C1 * (1 + 2 * C3)) (5 * C2) + 1) * α ^ (-(10 : ℝ))
          * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)) := by
    set f : Fn := Work.FTS.Galerkin.slice g τ with hf
    obtain ⟨-, hUsm, -, hprice⟩ := hStar α hα Φs Cs hctx.hstar6
    have hdat : Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M := by
      simpa only [hf] using
        (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.datData_of_H6Adm hctx.hreg hctx.h7 hctx.hbdd)
    have hCsα0 : 0 ≤ Cs * α :=
      le_trans (Work.Spaces.WlInf_nonneg α 6 _ hctx.hstar6.RW6.1) hctx.hstar6.RW6.2
    have hCs0 : 0 ≤ Cs := nonneg_of_mul_nonneg_left hCsα0 hα0
    have hKA0 : 0 ≤ 2 * (C3 * (Cs * α)) :=
      mul_nonneg (by norm_num) (mul_nonneg hC3pos.le (mul_nonneg hCs0 hα0.le))
    have hprice5 : ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i (fun z θ => -2 * coefU1 α Φs z θ) z θ|
          ≤ (2 * (C3 * (Cs * α))) * (z / (1 + z)) *
            (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) := by
      intro j i hji z θ hz hθ hθ2
      have hh := hprice (coefU1 α Φs) (Or.inr (Or.inl rfl)) j i hji z θ hz hθ hθ2
      have hsplit : Work.Spaces.mixed j i (fun z θ => -2 * coefU1 α Φs z θ) z θ
          = -2 * Work.Spaces.mixed j i (coefU1 α Φs) z θ := by
        simp only [mixed_const_mul]
      have habs : |-2 * Work.Spaces.mixed j i (coefU1 α Φs) z θ|
          = 2 * |Work.Spaces.mixed j i (coefU1 α Φs) z θ| := by
        rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hsplit, habs]
      calc 2 * |Work.Spaces.mixed j i (coefU1 α Φs) z θ|
          ≤ 2 * ((C3 * (Cs * α)) * (z / (1 + z)) *
              (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) :=
            mul_le_mul_of_nonneg_left hh (by norm_num)
        _ = (2 * (C3 * (Cs * α))) * (z / (1 + z)) *
              (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) := by
            ring
    have hrow := (hFam α hα (fun z θ => -2 * coefU1 α Φs z θ) f (2 * (C3 * (Cs * α))) M a b ρ
        (smoothOpen_const_mul (-2) hUsm) hdat hprice5 hab hleaf).2
    have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
    have hW0 : 0 ≤ 1 + Work.Spaces.HkSq α 6 f := by
      have := Work.Spaces.HkSq_nonneg α 6 f; linarith
    have hKAle := one_add_star_price_le (Ce := Ce) hα0 hα1 hC3pos.le hCs0
    have hnn : 0 ≤ α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
        * (1 + Work.Spaces.HkSq α 6 f) := by
      have h1 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
      have h2 : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
      have h3 : 0 ≤ (1 + M) ^ 4 := by positivity
      positivity
    refine le_trans hrow ?_
    calc C1 * α ^ (-(3 : ℝ)) * (1 + 2 * (C3 * (Cs * α))) * (1 + M)
          * (1 + Work.Spaces.HkSq α 6 f)
        ≤ (C1 * (1 + 2 * C3)) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) :=
          arith_fam hα0 hα1 hC1pos.le hKA0 hC3pos.le hKAle hM0 hW0
      _ ≤ (max (C1 * (1 + 2 * C3)) (5 * C2) + 1) * α ^ (-(10 : ℝ))
            * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
          calc (C1 * (1 + 2 * C3)) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                * (1 + Work.Spaces.HkSq α 6 f)
              = (C1 * (1 + 2 * C3))
                  * (α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                    * (1 + Work.Spaces.HkSq α 6 f)) := by ring
            _ ≤ (max (C1 * (1 + 2 * C3)) (5 * C2) + 1)
                  * (α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                    * (1 + Work.Spaces.HkSq α 6 f)) :=
                mul_le_mul_of_nonneg_right hCfg1 hnn
            _ = (max (C1 * (1 + 2 * C3)) (5 * C2) + 1) * α ^ (-(10 : ℝ))
                  * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                  * (1 + Work.Spaces.HkSq α 6 f) := by ring
  -- ## the `-2α·Vop(PhiTs α Φs)·D_zf` piece
  have h9 : |Work.FTS.TransportS.slotPairing ρ a b
        (nsP9 α Φs (Work.FTS.Galerkin.slice g τ)) (Work.FTS.Galerkin.slice g τ)|
      ≤ (max (C1 * (1 + 2 * C3)) (5 * C2) + 1) * α ^ (-(10 : ℝ))
          * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
          * (1 + Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)) := by
    set f : Fn := Work.FTS.Galerkin.slice g τ with hf
    set A9 : Fn := fun z θ => -2 * α * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
      with hA9
    obtain ⟨-, -, hVsm, -⟩ := hStar α hα Φs Cs hctx.hstar6
    have hdat : Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M := by
      simpa only [hf] using
        (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.datData_of_H6Adm hctx.hreg hctx.h7 hctx.hbdd)
    have hVth := hctx.hstar6.Vth
    have hVW6 := hctx.hstar6.VW6
    have hCsα0 : 0 ≤ Cs * α :=
      le_trans (Work.Spaces.WlInf_nonneg α 6 _ hctx.hstar6.RW6.1) hctx.hstar6.RW6.2
    have hCs0 : 0 ≤ Cs := nonneg_of_mul_nonneg_left hCsα0 hα0
    have hK0 : 0 ≤ 2 * α * (Cs * α) := mul_nonneg (by linarith) hCsα0
    have habs : |((-2) * α)| = 2 * α := by
      rw [abs_of_neg (by linarith : ((-2) * α) < 0)]
      ring
    have hflatV : ∀ b i : ℕ, b + i ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b i
            (Work.Spaces.pth (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs))) z θ|
          ≤ Cs * α := by
      intro b i hbi z θ hz hθ hθ2
      obtain ⟨K, hK⟩ := hVth.1 b i hbi
      exact le_trans (Work.FTS.H2.le_supAbsO hz hθ hθ2 hK)
        (le_trans (Work.FTS.TransportS.supAbsO_le_coefTh hbi) hVth.2)
    have hpthA : Work.Spaces.pth A9
        = fun z θ => ((-2) * α)
            * Work.Spaces.pth (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) z θ := by
      rw [hA9]
      funext z θ
      simp only [Work.Spaces.pth]
      rw [deriv_const_mul_field]
    have hsm9 : Work.FTS.EllipticEst.SmoothOpen A9 := by
      rw [hA9]
      exact smoothOpen_const_mul ((-2) * α) hVsm
    have hwl9 : Work.Spaces.WlInfMem α 6 A9 := by
      rw [hA9]
      exact WlInfMem_const_mul' ((-2) * α) hVW6.1
    have hle9 : Work.Spaces.WlInf α 6 A9 ≤ 2 * α * (Cs * α) := by
      rw [hA9]
      have h := WlInf_const_mul_le_abs ((-2) * α) hVW6.1
      rw [habs] at h
      exact le_trans h (mul_le_mul_of_nonneg_left hVW6.2 (by linarith))
    have hflat0 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.pth A9 z θ| ≤ 2 * α * (Cs * α) := by
      intro z θ hz hθ hθ2
      have hp : Work.Spaces.pth A9 z θ = ((-2) * α)
          * Work.Spaces.pth (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) z θ :=
        congrFun (congrFun hpthA z) θ
      rw [hp, abs_mul, habs]
      exact mul_le_mul_of_nonneg_left (hflatV 0 0 (by omega) z θ hz hθ hθ2) (by linarith)
    have hflat1 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.Dz (Work.Spaces.pth A9) z θ| ≤ 2 * α * (Cs * α) := by
      intro z θ hz hθ hθ2
      have hDz : Work.Spaces.Dz (Work.Spaces.pth A9) z θ = ((-2) * α)
          * Work.Spaces.Dz (Work.Spaces.pth
              (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs))) z θ := by
        rw [hpthA]
        exact congrFun (congrFun (Dz_const_mul ((-2) * α)
          (Work.Spaces.pth (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)))) z) θ
      rw [hDz, abs_mul, habs]
      exact mul_le_mul_of_nonneg_left (hflatV 1 0 (by omega) z θ hz hθ hθ2) (by linarith)
    have hflat2 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.Dth (Work.Spaces.pth A9) z θ| ≤ 2 * α * (Cs * α) := by
      intro z θ hz hθ hθ2
      have hDth : Work.Spaces.Dth (Work.Spaces.pth A9) z θ = ((-2) * α)
          * Work.Spaces.Dth (Work.Spaces.pth
              (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs))) z θ := by
        rw [hpthA]
        exact congrFun (congrFun (Dth_const_mul ((-2) * α)
          (Work.Spaces.pth (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)))) z) θ
      rw [hDth, abs_mul, habs]
      exact mul_le_mul_of_nonneg_left (hflatV 0 1 (by omega) z θ hz hθ hθ2) (by linarith)
    have hrow := hDz α hα A9 f (2 * α * (Cs * α)) M (2 * α * (Cs * α)) a b ρ
      hsm9 hwl9 hle9 hdat hflat0 hflat1 hflat2 hab hleaf
    have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
    have hW0 : 0 ≤ 1 + Work.Spaces.HkSq α 6 f := by
      have := Work.Spaces.HkSq_nonneg α 6 f; linarith
    have hKK := one_add_dz_price_le (Ce := Ce) hα0 hα1 hCs0
    have hnn : 0 ≤ α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
        * (1 + Work.Spaces.HkSq α 6 f) := by
      have h1 : 0 ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
      have h2 : 0 ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
      have h3 : 0 ≤ (1 + M) ^ 4 := by positivity
      positivity
    refine le_trans hrow ?_
    calc C2 * α ^ (-(4 : ℝ)) * (1 + 2 * α * (Cs * α) + 2 * α * (Cs * α)) * (1 + M)
          * (1 + Work.Spaces.HkSq α 6 f)
        ≤ (5 * C2) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) :=
          arith_dz hα0 hα1 hC2pos.le hK0 hK0 hKK hM0 hW0
      _ ≤ (max (C1 * (1 + 2 * C3)) (5 * C2) + 1) * α ^ (-(10 : ℝ))
            * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
          calc (5 * C2) * α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                * (1 + Work.Spaces.HkSq α 6 f)
              = (5 * C2)
                  * (α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                    * (1 + Work.Spaces.HkSq α 6 f)) := by ring
            _ ≤ (max (C1 * (1 + 2 * C3)) (5 * C2) + 1)
                  * (α ^ (-(10 : ℝ)) * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                    * (1 + Work.Spaces.HkSq α 6 f)) :=
                mul_le_mul_of_nonneg_right hCfg2 hnn
            _ = (max (C1 * (1 + 2 * C3)) (5 * C2) + 1) * α ^ (-(10 : ℝ))
                  * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4
                  * (1 + Work.Spaces.HkSq α 6 f) := by ring
  exact ⟨h1, h5, h9⟩

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG
