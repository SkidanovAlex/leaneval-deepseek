import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.CoeffJetsDefs
import Submission.Work.FTS_RegExport.RXT.loc_sup4
import Submission.Work.FTS_RegExport.RXT.MixedUniform
import Submission.Work.FTS_RegExport.RXT.slice_space_lip
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS.RegPkgGal.Sup.DthIter_DzIter_comm_fin
import Submission.Work.FTS_RegExport.RXT.C2Psi
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.mixed_mul_fin

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
