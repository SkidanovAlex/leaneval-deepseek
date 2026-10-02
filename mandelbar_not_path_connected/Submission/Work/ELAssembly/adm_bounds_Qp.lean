import Mathlib
import Submission.Work.ELAssembly.PullInputs
import Submission.Work.ELNest.T_iterate_bAng

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

/-- **The four angles of an admissible level-`n` `z₁`-polygon are ordered.**  The flattened angle
list of `[P0, N.Qp n]` is `[P0.a, P0.b, βₙ', βₙ + 1]` (`N.Qpa`, `N.Qpb`); `PolyAdmissible.cyc`
gives it strictly increasing, and the `headD`-bound gives `βₙ + 1 < P0.a + 1`. -/
private lemma order_of_adm {c : ℂ} {d : Work.EL.RootParabolic c} {P0 : Work.EL.CoPair d.hN}
    {N : Work.ELAssembly.NestPairs d} {n : ℕ} (h : Work.EL.PolyAdmissible [P0, N.Qp n]) :
    P0.a < P0.b ∧ P0.b < Work.ELNest.bAng' n ∧ Work.ELNest.bAng n < P0.a := by
  have hcyc : ([P0.a, P0.b, (N.Qp n).a, (N.Qp n).b]).Pairwise (· < ·) := by
    have := h.cyc.2.1
    simpa using this
  have h01 : P0.a < P0.b := (List.pairwise_cons.mp hcyc).1 P0.b (by simp)
  have h12 : P0.b < (N.Qp n).a :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp hcyc).2).1 (N.Qp n).a (by simp)
  have hb_lt : (N.Qp n).b < P0.a + 1 := by
    have := h.cyc.2.2 (N.Qp n).b (by simp)
    simpa using this
  rw [N.Qpa n] at h12
  rw [N.Qpb n] at hb_lt
  exact ⟨h01, h12, by linarith⟩

/-- The nest angles `bAng n` tend to `α₁ = 371/1023` from below. -/
private lemma tendsto_bAng :
    Tendsto (fun n : ℕ => Work.ELNest.bAng n) atTop (nhds Work.ELNest.alpha1) := by
  have hpow : Tendsto (fun n : ℕ => (1024 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hzero : Tendsto
      (fun n : ℕ => (Work.ELNest.alpha1 - Work.ELNest.beta0) / (1024 : ℝ) ^ n)
      atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero.comp hpow).const_mul
      (Work.ELNest.alpha1 - Work.ELNest.beta0)
    simpa [div_eq_mul_inv] using h
  have h := hzero.const_sub Work.ELNest.alpha1
  simpa [Work.ELNest.bAng] using h

/-- The nest angles `bAng' n` tend to `α₂ = 404/1023` from above. -/
private lemma tendsto_bAng' :
    Tendsto (fun n : ℕ => Work.ELNest.bAng' n) atTop (nhds Work.ELNest.alpha2) := by
  have hpow : Tendsto (fun n : ℕ => (1024 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hzero : Tendsto
      (fun n : ℕ => (Work.ELNest.beta0' - Work.ELNest.alpha2) / (1024 : ℝ) ^ n)
      atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero.comp hpow).const_mul
      (Work.ELNest.beta0' - Work.ELNest.alpha2)
    simpa [div_eq_mul_inv] using h
  have h := hzero.const_add Work.ELNest.alpha2
  simpa [Work.ELNest.bAng'] using h

/-- **The `α`-pair angles are squeezed between `α₁` and `α₂`.**  `adm_order_Qp` at every level `n`
gives `βₙ < P0.a` and `P0.b < βₙ'`, and `βₙ → α₁`, `βₙ' → α₂`
(`bAng n = α₁ - (α₁ - β₀)/1024ⁿ`, `bAng' n = α₂ + (β₀' - α₂)/1024ⁿ`, with
`(1024ⁿ)⁻¹ → 0` as `n → ∞`, via `tendsto_pow_atTop_atTop_of_one_lt` and
`tendsto_inv_atTop_zero`); passing to the limit with `le_of_tendsto_of_tendsto` gives `α₁ ≤ P0.a`
and `P0.b ≤ α₂`, and `P0.a < P0.b` is `adm_order_Qp` at level `0`.  (Note
`Work.EL.alpha1 = Work.ELNest.alpha1` and likewise for `alpha2`, definitionally.) -/
theorem adm_bounds_Qp {c : ℂ} {d : Work.EL.RootParabolic c} {P0 : Work.EL.CoPair d.hN}
    {N : Work.ELAssembly.NestPairs d} (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible [P0, N.Qp n]) :
    Work.EL.alpha1 ≤ P0.a ∧ P0.a < P0.b ∧ P0.b ≤ Work.EL.alpha2 := by
  have hab : P0.a < P0.b := (order_of_adm (hadm 0)).1
  have hle1 : Work.ELNest.alpha1 ≤ P0.a :=
    le_of_tendsto_of_tendsto tendsto_bAng tendsto_const_nhds
      (Eventually.of_forall fun n => (order_of_adm (hadm n)).2.2.le)
  have hle2 : P0.b ≤ Work.ELNest.alpha2 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds tendsto_bAng'
      (Eventually.of_forall fun n => (order_of_adm (hadm n)).2.1.le)
  refine ⟨?_, hab, ?_⟩
  · show Work.ELNest.alpha1 ≤ P0.a
    exact hle1
  · show P0.b ≤ Work.ELNest.alpha2
    exact hle2

end Work.ELAssembly
