import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_EllLimOK.LimExtract.limExtract_bounds10_const
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.st1_stdata2
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.LeibBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.JetCalc.LeibBound` — the bounded Leibniz expansion

`|D_z^jD_θ^i(f·h)| ≤ 2^{j+i}·(C_f·C_g)` at a point of an open set where `f`, `h` are `C^{j+i}`
and their mixed jets of order `≤ j+i` are bounded by `C_f`, `C_g`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem abs_mixed_mul_bound {j i : ℕ} {f h : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ (j + i) (Function.uncurry f) V)
    (hh : ContDiffOn ℝ (j + i) (Function.uncurry h) V)
    {p : ℝ × ℝ} (hp : p ∈ V) {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hbf : ∀ a b : ℕ, a + b ≤ j + i → |Work.Spaces.mixed b a f p.1 p.2| ≤ Cf)
    (hbh : ∀ a b : ℕ, a + b ≤ j + i → |Work.Spaces.mixed b a h p.1 p.2| ≤ Cg) :
    |Work.Spaces.mixed j i (fun z θ => f z θ * h z θ) p.1 p.2|
      ≤ (2 : ℝ) ^ (j + i) * (Cf * Cg) := by
  rw [Work.FTS_RegExport.RXT.Sys.JetCalc.mixed_mul_fin hV hf hh p.1 p.2 hp]
  have hsumi : ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) = (2 : ℝ) ^ i := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  have hsumj : ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) = (2 : ℝ) ^ j := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  have hK : 0 ≤ Cf * Cg := mul_nonneg hCf hCg
  -- the double sum of the absolute values
  have hstep1 : |∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a f p.1 p.2 * Work.Spaces.mixed (j - b) (i - a) h p.1 p.2)|
      ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ)) * (Cf * Cg) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun a ha => le_trans (Finset.abs_sum_le_sum_abs _ _) ?_)
    refine Finset.sum_le_sum (fun b hb => ?_)
    have ha' : a ≤ i := by have := Finset.mem_range.mp ha; omega
    have hb' : b ≤ j := by have := Finset.mem_range.mp hb; omega
    have hX : |Work.Spaces.mixed b a f p.1 p.2| ≤ Cf := hbf a b (by omega)
    have hY : |Work.Spaces.mixed (j - b) (i - a) h p.1 p.2| ≤ Cg := hbh (i - a) (j - b) (by omega)
    have hc : 0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
    have hXY : |Work.Spaces.mixed b a f p.1 p.2|
        * |Work.Spaces.mixed (j - b) (i - a) h p.1 p.2| ≤ Cf * Cg :=
      mul_le_mul hX hY (abs_nonneg _) hCf
    calc |((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a f p.1 p.2 * Work.Spaces.mixed (j - b) (i - a) h p.1 p.2)|
        = ((i.choose a : ℝ) * (j.choose b : ℝ))
          * |Work.Spaces.mixed b a f p.1 p.2 * Work.Spaces.mixed (j - b) (i - a) h p.1 p.2| := by
          rw [abs_mul, abs_of_nonneg hc]
      _ = ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (|Work.Spaces.mixed b a f p.1 p.2| * |Work.Spaces.mixed (j - b) (i - a) h p.1 p.2|) := by
          rw [abs_mul]
      _ ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) * (Cf * Cg) :=
          mul_le_mul_of_nonneg_left hXY hc
  have hstep2 : ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ)) * (Cf * Cg)
      = (2 : ℝ) ^ (j + i) * (Cf * Cg) := by
    have houter : ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ)) * (Cf * Cg)
        = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (i.choose a : ℝ) * (j.choose b : ℝ)) * (Cf * Cg) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_mul]
    rw [houter, ← Finset.sum_mul_sum, hsumi, hsumj, ← pow_add, Nat.add_comm]
  exact le_trans hstep1 (le_of_eq hstep2)

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.OpFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.JetCalc.OpFacts` — elementary facts about `D_z^k`, `D_θ^k`

Oddness of the curvilinear operators and their iterates, the monoid facts for the iterates
(`D_z^k ∘ D_z = D_z^{k+1}`), the index shifts `mixed k l (D_θ u) = mixed k (l+1) u`
(definitional) and `mixed k l (D_z u) = mixed (k+1) l u` (Clairaut at finite order), and
Clairaut for the lowest mixed jets.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 1000000
/-! ## §1 Elementary facts about the iterated operators `D_z^k`, `D_θ^k` -/

/-- `D_z` is odd: `D_z(-f) = -D_z f`. -/
theorem Dz_neg (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => - f z θ) = fun z θ => - Work.Spaces.Dz f z θ := by
  funext z θ
  show z * deriv (fun z' => - f z' θ) z = - (z * deriv (fun z' => f z' θ) z)
  rw [show (fun z' => - f z' θ) = fun z' => (-1 : ℝ) * f z' θ from by funext z'; ring,
    deriv_const_mul_field]
  ring

/-- `D_θ` is odd: `D_θ(-f) = -D_θ f`. -/
theorem Dth_neg (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => - f z θ) = fun z θ => - Work.Spaces.Dth f z θ := by
  funext z θ
  show Real.sin (2 * θ) * deriv (fun θ' => - f z θ') θ
    = - (Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ)
  rw [show (fun θ' => - f z θ') = fun θ' => (-1 : ℝ) * f z θ' from by funext θ'; ring,
    deriv_const_mul_field]
  ring

/-- The iterates of `D_z` are odd. -/
theorem DzIter_neg (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter k (fun z θ => - f z θ)
      = fun z θ => - Work.Spaces.DzIter k f z θ := by
  induction k with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ, Dz_neg]

/-- The iterates of `D_θ` are odd. -/
theorem DthIter_neg (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter k (fun z θ => - f z θ)
      = fun z θ => - Work.Spaces.DthIter k f z θ := by
  induction k with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ, Dth_neg]

/-- The mixed operators are odd. -/
theorem mixed_neg (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => - f z θ)
      = fun z θ => - Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed]
  rw [DthIter_neg, DzIter_neg]

/-- `D_z^k` applied after one more `D_z` is `D_z^{k+1}`. -/
theorem DzIter_comp_Dz (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter k (Work.Spaces.Dz f) = Work.Spaces.DzIter (k + 1) f := by
  induction k with
  | zero => rfl
  | succ n ih =>
      have h := congrArg (fun h : ℝ → ℝ → ℝ => Work.Spaces.Dz h) ih
      rw [Work.Spaces.DzIter_succ]
      exact h.trans (Work.Spaces.DzIter_succ (n + 1) f).symm

/-- `D_θ^k` applied after one more `D_θ` is `D_θ^{k+1}`. -/
theorem DthIter_comp_Dth (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter k (Work.Spaces.Dth f) = Work.Spaces.DthIter (k + 1) f := by
  induction k with
  | zero => rfl
  | succ n ih =>
      have h := congrArg (fun h : ℝ → ℝ → ℝ => Work.Spaces.Dth h) ih
      rw [Work.Spaces.DthIter_succ]
      exact h.trans (Work.Spaces.DthIter_succ (n + 1) f).symm

/-- The `D_θ`-shift of the angular index (purely definitional). -/
theorem mixed_Dth_shift (k l : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed k l (Work.Spaces.Dth f) = Work.Spaces.mixed k (l + 1) f := by
  simp only [Work.Spaces.mixed]
  rw [DthIter_comp_Dth]

/-- The `D_z`-shift of the radial index, on an open set where `f` is smooth enough: this is
Clairaut's theorem (`D_θ` commutes with the radial iterate) at the finite order `l + 1`. -/
theorem mixed_Dz_shift {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (hf : ContDiffOn ℝ n (Function.uncurry f) V) {k l : ℕ} (hkl : k + l + 1 ≤ n) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed k l (Work.Spaces.Dz f)))
      (Function.uncurry (Work.Spaces.mixed (k + 1) l f)) V := by
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.DthIter l (Work.Spaces.DzIter 1 f)))
      (Function.uncurry (Work.Spaces.DzIter 1 (Work.Spaces.DthIter l f))) V :=
    Work.FTS.RegPkgGal.Sup.DthIter_DzIter_comm_fin hV n hf l 1 (by omega)
  have hcongr := Work.FTS.H2.DzIter_congr_of_isOpen hV hcomm k
  intro p hp
  have h1 := hcongr hp
  have h2 : Work.Spaces.DzIter k (Work.Spaces.DthIter l (Work.Spaces.DzIter 1 f)) p.1 p.2
      = Work.Spaces.DzIter k (Work.Spaces.DzIter 1 (Work.Spaces.DthIter l f)) p.1 p.2 := h1
  show Work.Spaces.DzIter k (Work.Spaces.DthIter l (Work.Spaces.DzIter 1 f)) p.1 p.2
      = Work.Spaces.DzIter (k + 1) (Work.Spaces.DthIter l f) p.1 p.2
  rw [h2]
  exact congrFun (congrFun (DzIter_comp_Dz k (Work.Spaces.DthIter l f)) p.1) p.2

/-- The definitional relation `D_z^{k+1}D_θ^i f = z · ∂_z (D_z^kD_θ^i f)`. -/
theorem mixed_fst_eq (f : ℝ → ℝ → ℝ) (k i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed (k + 1) i f z θ
      = z * Work.Spaces.pz (Work.Spaces.mixed k i f) z θ :=
  congrFun (congrFun (Work.FTS_RegExport.RXT.mixed_succ_fst_eq f k i) z) θ

/-- `∂_z` of a mixed jet, in terms of the next mixed jet. -/
theorem pz_mixed_eq (f : ℝ → ℝ → ℝ) (k i : ℕ) {z θ : ℝ} (hz : z ≠ 0) :
    Work.Spaces.pz (Work.Spaces.mixed k i f) z θ
      = Work.Spaces.mixed (k + 1) i f z θ / z := by
  rw [eq_div_iff hz, mul_comm]
  exact (mixed_fst_eq f k i z θ).symm

/-- **Clairaut for the lowest mixed jets**: for `f` of class `C²` at `(z,θ)` with `sin(2θ) ≠ 0`,
the `θ`-derivative of the mixed jets of total order `≤ 1` is the mixed jet of one higher angular
order divided by `sin(2θ)` (both sides are `D_θ` of the jet, and `D_θ` is `sin(2θ)·∂_θ`). -/
theorem pth_mixed_eq {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) (hsin : Real.sin (2 * θ) ≠ 0) :
    ∀ {j i : ℕ}, j + i ≤ 1 →
      Work.Spaces.pth (Work.Spaces.mixed j i f) z θ
        = Work.Spaces.mixed j (i + 1) f z θ / Real.sin (2 * θ) := by
  have h00 : Work.Spaces.mixed 0 0 f = f := rfl
  have h01 : Work.Spaces.mixed 0 1 f = Work.Spaces.Dth f := rfl
  have h10 : Work.Spaces.mixed 1 0 f = Work.Spaces.Dz f := rfl
  have h11 : Work.Spaces.mixed 1 1 f = Work.Spaces.Dz (Work.Spaces.Dth f) := rfl
  have h02 : Work.Spaces.mixed 0 2 f = Work.Spaces.Dth (Work.Spaces.Dth f) := rfl
  have hDth : ∀ g : ℝ → ℝ → ℝ, Work.Spaces.Dth g z θ
      = Real.sin (2 * θ) * Work.Spaces.pth g z θ := fun g => rfl
  intro j i hji
  have hcases : (j = 0 ∧ i = 0) ∨ (j = 0 ∧ i = 1) ∨ (j = 1 ∧ i = 0) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [h00, h01, hDth, mul_div_cancel_left₀ _ hsin]
  · rw [h01, h02, hDth, mul_div_cancel_left₀ _ hsin]
  · rw [h10, h11, Work.Spaces.Dz_Dth_comm hf, hDth, mul_div_cancel_left₀ _ hsin]

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.mixed_integral_identity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.mixed_integral_identity` — S5a of the RX-St1 leaf plan

The integrated identity for the six components `w_k = D_z^{j}D_θ^{i}(slice g τ)`, `(j,i) = idx k`:

  `w_k(τ₂) − w_k(τ₁) = ∫_{τ₁}^{τ₂} (D^β ∂_τ g)(σ) dσ`

The base case `(0,0)` is the fundamental theorem of calculus in `τ` and each step differentiates
the identity for the lower slot in `z` (resp. `θ`) along a difference-quotient sequence, passing to
the limit with the dominated convergence theorem.  The six leaves are assembled from `mii_P_00`,
`mii_step_z` and `mii_step_theta` (`Submission/Work/FTS_RegExport/RXT/Sys/miiSteps.lean`) using the
index list `idx = ![(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)]`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mixed_integral_identity {S α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hG : Work.FTS.RegExportIface.RXT.GdotLoc S g) :
    ∀ k : Fin 6, ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ τ₁ τ₂, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ S →
      Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
          (Work.FTS.RegExportIface.RXT.idx k).2 (Work.FTS.Galerkin.slice g τ₂) z θ
        - Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
          (Work.FTS.RegExportIface.RXT.idx k).2 (Work.FTS.Galerkin.slice g τ₁) z θ
      = ∫ σ in τ₁..τ₂, Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
          (Work.FTS.RegExportIface.RXT.idx k).2 (Work.FTS.Galerkin.gdot g σ) z θ := by
  -- the three inputs read off the hypothesis bundle
  have hc4 : ∀ τ, 0 ≤ τ →
      ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ)) Work.FTS.EllipticEst.Q0 :=
    fun τ hτ => hOK.1.1.c4 τ hτ
  have hcontτ : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ContinuousOn (fun τ => g z θ τ) (Set.Ici 0) :=
    fun z θ h => hOK.1.1.cont z θ h
  have hderivg : ∀ z θ σ, 0 < σ → (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s => g z θ s) (Work.FTS.Galerkin.gdot g σ z θ) σ := by
    intro z θ σ hσ hQd
    exact (hSol.2 z θ σ (le_of_lt hσ) hQd).hasDerivAt (Ici_mem_nhds hσ)
      |>.differentiableAt.hasDerivAt
  -- the six leaves, by induction on the total order
  have h00 : mii_P S g 0 0 := mii_P_00 hcontτ hderivg (mii_R_00 hG)
  have h10 : mii_P S g 1 0 := mii_step_z hG hc4 (j := 0) (i := 0) (by omega) h00 (mii_R_00 hG)
  have h01 : mii_P S g 0 1 := mii_step_theta hG hc4 (i := 0) (by omega) h00 (mii_R_00 hG)
  have h20 : mii_P S g 2 0 := mii_step_z hG hc4 (j := 1) (i := 0) (by omega) h10 (mii_R_10 hG)
  have h11 : mii_P S g 1 1 := mii_step_z hG hc4 (j := 0) (i := 1) (by omega) h01 (mii_R_01 hG)
  have h02 : mii_P S g 0 2 := mii_step_theta hG hc4 (i := 1) (by omega) h01 (mii_R_01 hG)
  intro k
  fin_cases k
  · exact h00
  · exact h10
  · exact h01
  · exact h20
  · exact h11
  · exact h02

end Work.FTS_RegExport.RXT.Sys
end
end
