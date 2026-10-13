import Mathlib.Analysis.Complex.Exponential
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
import Submission.Work.FTS.StrongEps.PZeroAux.softClass_Pz
import Submission.Work.FTS.StrongEps.PZeroAux.hkNorm_Pz_le
import Submission.Work.FTS.StrongPersist.IP6Clauses

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Proofs/RawE6Aux/Basic.lean` — the bilinearity bookkeeping of `IP6o`

`IP6` is symmetric (`IP6_symm`) and additive/homogeneous in its **first** argument on the honest
class (`IP6_add`, `IP6_smul`); the lemmas here move that to the second argument, which is what
turns the rank-one projection `Pz h = h − (L₁₂ h 0 / pzNorm) • bump` into a *correction* of the
pairing.  They are used by `RawE6Aux/Main.lean` (the repaired leaf L-A) and by the assigned file
`rawE6_ineq_proof.lean`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.RawE6Aux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- shorthand for the route's level-six pairing. -/
abbrev IP6o := Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o

/-- `IP6o` is additive in its second argument on the honest class. -/
theorem IP6o_add_right (α : ℝ) (hα : 0 < α) {u u₁ u₂ : Fn}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (h₁ : Work.FTS.EllipticEst.SmoothOpen u₁)
    (h₂ : Work.FTS.EllipticEst.SmoothOpen u₂) (mu : Work.Spaces.HkMem α 6 u)
    (m₁ : Work.Spaces.HkMem α 6 u₁) (m₂ : Work.Spaces.HkMem α 6 u₂) :
    IP6o α u (fun z θ => u₁ z θ + u₂ z θ) = IP6o α u u₁ + IP6o α u u₂ := by
  have hsymm : ∀ a b : Fn, IP6o α a b = IP6o α b a := fun a b =>
    Work.FTS.StrongPersist.IP6_symm 1 1 1 1 1 1 1 1 1 1 α a b
  have hadd : IP6o α (fun z θ => u₁ z θ + u₂ z θ) u = IP6o α u₁ u + IP6o α u₂ u :=
    Work.FTS.StrongPersist.IP6_add 1 1 1 1 1 1 1 1 1 1 α hα h₁ h₂ hu m₁ m₂ mu
  rw [hsymm u (fun z θ => u₁ z θ + u₂ z θ), hadd, hsymm u₁ u, hsymm u₂ u]

/-- `IP6o` is homogeneous in its second argument. -/
theorem IP6o_const_mul_right (α : ℝ) (c : ℝ) (u v : Fn) :
    IP6o α u (fun z θ => c * v z θ) = c * IP6o α u v := by
  show Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u (fun z θ => c * v z θ)
    = c * Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u v
  rw [Work.FTS.StrongPersist.IP6_symm 1 1 1 1 1 1 1 1 1 1 α u (fun z θ => c * v z θ),
    Work.FTS.StrongPersist.IP6_smul 1 1 1 1 1 1 1 1 1 1 α c v u,
    Work.FTS.StrongPersist.IP6_symm 1 1 1 1 1 1 1 1 1 1 α v u]

/-- The `P₀`-correction of the pairing: pairing `u` against `v − c • bump`. -/
theorem IP6o_sub_smul_bump (α : ℝ) (hα : 0 < α) {u v : Fn} (c : ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v)
    (mu : Work.Spaces.HkMem α 6 u) (mv : Work.Spaces.HkMem α 6 v) :
    IP6o α u (fun z θ => v z θ - c * Work.FTS.StrongEps.bump z θ)
      = IP6o α u v - c * IP6o α u Work.FTS.StrongEps.bump := by
  have hb : Work.FTS.EllipticEst.SmoothOpen Work.FTS.StrongEps.bump :=
    Work.FTS.StrongEps.smoothOpen_bump
  have hbm : Work.Spaces.HkMem α 6 Work.FTS.StrongEps.bump :=
    Work.FTS.StrongEps.PZeroAux.HkMem_bump α 6
  have hcm : Work.Spaces.HkMem α 6 (fun z θ => (-c) * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-c) hbm
  have hcs : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-c) * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen (-c) hb
  have hfun : (fun z θ => v z θ - c * Work.FTS.StrongEps.bump z θ)
      = fun z θ => v z θ + (-c) * Work.FTS.StrongEps.bump z θ := by
    funext z θ; ring
  rw [hfun, IP6o_add_right α hα hu hv hcs mu mv hcm,
    IP6o_const_mul_right α (-c) u Work.FTS.StrongEps.bump]
  ring

/-- The `P₀`-correction of the pairing in its **first** argument: pairing `v − c • bump`
against `u`. -/
theorem IP6o_sub_smul_bump_left (α : ℝ) (hα : 0 < α) {v u : Fn} (c : ℝ)
    (hv : Work.FTS.EllipticEst.SmoothOpen v) (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (mv : Work.Spaces.HkMem α 6 v) (mu : Work.Spaces.HkMem α 6 u) :
    IP6o α (fun z θ => v z θ - c * Work.FTS.StrongEps.bump z θ) u
      = IP6o α v u - c * IP6o α Work.FTS.StrongEps.bump u := by
  have hb : Work.FTS.EllipticEst.SmoothOpen Work.FTS.StrongEps.bump :=
    Work.FTS.StrongEps.smoothOpen_bump
  have hbm : Work.Spaces.HkMem α 6 Work.FTS.StrongEps.bump :=
    Work.FTS.StrongEps.PZeroAux.HkMem_bump α 6
  have hcm : Work.Spaces.HkMem α 6 (fun z θ => (-c) * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen (-c) hbm
  have hcs : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-c) * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen (-c) hb
  have hfun : (fun z θ => v z θ - c * Work.FTS.StrongEps.bump z θ)
      = fun z θ => v z θ + (-c) * Work.FTS.StrongEps.bump z θ := by
    funext z θ; ring
  rw [hfun]
  show Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
      (fun z θ => v z θ + (-c) * Work.FTS.StrongEps.bump z θ) u
    = Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α v u
      - c * Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α Work.FTS.StrongEps.bump u
  rw [Work.FTS.StrongPersist.IP6_add 1 1 1 1 1 1 1 1 1 1 α hα hv hcs hu mv hcm mu,
    Work.FTS.StrongPersist.IP6_smul 1 1 1 1 1 1 1 1 1 1 α (-c) Work.FTS.StrongEps.bump u]
  ring

/-- Homogeneity of `IP6o` in the **first** argument. -/
theorem IP6o_const_mul_right' (α : ℝ) (c : ℝ) (v u : Fn) :
    IP6o α (fun z θ => c * v z θ) u = c * IP6o α v u :=
  Work.FTS.StrongPersist.IP6_smul 1 1 1 1 1 1 1 1 1 1 α c v u

/-- `√(exp x) = exp (x/2)`. -/
theorem sqrt_exp_eq (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  have h : (Real.exp (x / 2)) ^ 2 = Real.exp x := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [← h, Real.sqrt_sq (Real.exp_pos _).le]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.RawE6Aux
