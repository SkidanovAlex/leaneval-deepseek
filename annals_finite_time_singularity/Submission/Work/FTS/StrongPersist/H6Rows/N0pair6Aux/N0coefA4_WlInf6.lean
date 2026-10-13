import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.LocData.SmoothQuad_Fstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `𝒲^{6,∞}`-data of the coefficient `(3/(2α))·D_θF_*`

The `A₄`-coefficient of the `N₀`-row is `A₄ = (3/(2α))·D_θ(F_*)`.  The scaled
profile `D_θ(F_*)` is already known to lie in `𝒲^{6,∞}` with norm `≤ C α²`
(`Work.FTS.StrongPersist.DthFstar_W6`), so the present lemma is the bookkeeping
which (a) records the smoothness on the open quadrant and (b) transports the
`𝒲^{6,∞}`-membership and the norm through the scalar factor `3/(2α)`:

* `SmoothOpen (D_θF_*)` comes from `SmoothQuad_Fstar` (`D_θ` preserves the class,
  open-quadrant version) and multiplication by a constant;
* `WlInfMem α 6` is transported by the elementary scaling lemmas
  `WlInfMem_const_mul'`/`WlInf_const_mul_le` below (the iterated operators commute
  with scalar multiplication — `deriv_const_mul_field` is unconditional);
* the norm `(3/(2α))·(C α²) = (3C/2)·α` is `α`-linear, as required.
-/

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open Work.Spaces
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## Smoothness on the open quadrant -/

/-- `SmoothQuad` (genuine `C^∞` on `z > -1`, `0 < θ < π/2`) implies `SmoothOpen`
(the same on the smaller open quadrant `(0,∞) × (0,π/2)`). -/
theorem smoothOpen_of_smoothQuad' {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) :
    Work.FTS.EllipticEst.SmoothOpen f := by
  refine hf.mono ?_
  intro p hp
  simp only [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
  exact ⟨by linarith [hp.1], hp.2⟩

/-- `SmoothOpen` is stable under multiplication by a constant. -/
theorem smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (fun n => ?_)
  exact contDiffOn_const.mul ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hf n)

/-! ## Scalar multiplication commutes with the iterated operators

`deriv_const_mul` needs differentiability, but `deriv_const_mul_field` is
unconditional (the junk value `0` is compatible with scalar multiplication), which is
what makes these two identities valid for an arbitrary `f`. -/

theorem pzIter_const_mul' (c : ℝ) (f : ℝ → ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pzIter k f z θ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.pz]
      exact deriv_const_mul_field c

theorem DthIter_const_mul' (c : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DthIter j (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter j f z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field c]
      ring

/-! ## Scaling the suprema and the `𝒲^{l,∞}`-data -/

theorem SupFinite_const_mul {g : ℝ → ℝ → ℝ} (c : ℝ) (h : SupFinite g) :
    SupFinite (fun z θ => c * g z θ) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨|c| * M, ?_⟩
  rintro y ⟨z, hz, θ, hθ, rfl⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM ⟨z, hz, θ, hθ, rfl⟩) (abs_nonneg c)

theorem SupFinite_congr {g h : ℝ → ℝ → ℝ} (hgh : ∀ z θ, g z θ = h z θ) (hg : SupFinite g) :
    SupFinite h := by
  obtain ⟨M, hM⟩ := hg
  refine ⟨M, ?_⟩
  rintro y ⟨z, hz, θ, hθ, rfl⟩
  rw [← hgh z θ]
  exact hM ⟨z, hz, θ, hθ, rfl⟩

/-- `supAbs` is always nonnegative (`sSup` of an unbounded set is `0 = sSup ∅`). -/
theorem supAbs_nonneg_of (g : ℝ → ℝ → ℝ) : 0 ≤ supAbs g := by
  by_cases h : BddAbove {y : ℝ | ∃ z ∈ Iz, ∃ θ ∈ Iθ, y = |g z θ|}
  · exact le_trans (abs_nonneg _)
      (le_csSup h ⟨0, zero_mem_Iz, 0, zero_mem_Iθ, rfl⟩)
  · rw [Work.Spaces.supAbs, csSup_of_not_bddAbove h, Real.sSup_def]
    simp

theorem supAbs_const_mul_le {g : ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hg : SupFinite g) :
    supAbs (fun z θ => c * g z θ) ≤ c * supAbs g := by
  refine supAbs_le fun z hz θ hθ => ?_
  rw [abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (abs_le_supAbs hz hθ hg) hc

/-- Membership in `𝒲^{l,∞}` is preserved by scalar multiplication. -/
theorem WlInfMem_const_mul' {α : ℝ} {l : ℕ} {f : ℝ → ℝ → ℝ} (c : ℝ)
    (hmem : WlInfMem α l f) :
    WlInfMem α l (fun z θ => c * f z θ) := by
  refine ⟨fun k hk => ?_, fun j hj k hk hj1 hjk => ?_⟩
  · refine SupFinite_congr (fun z θ => ?_) (SupFinite_const_mul c (hmem.1 k hk))
    rw [pzIter_const_mul']
    ring
  · refine SupFinite_congr (fun z θ => ?_) (SupFinite_const_mul c (hmem.2 j hj k hk hj1 hjk))
    rw [DthIter_const_mul', pzIter_const_mul']
    ring

/-- The `𝒲^{l,∞}`-norm scales by the factor `c` (for `c ≥ 0`). -/
theorem WlInf_const_mul_le {α : ℝ} {l : ℕ} {f : ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hmem : WlInfMem α l f) :
    WlInf α l (fun z θ => c * f z θ) ≤ c * WlInf α l f := by
  have hZ : (∑ k ∈ Finset.range (l + 1),
        supAbs (fun z θ => (z + 1) ^ k * pzIter k (fun z θ => c * f z θ) z θ))
      ≤ c * ∑ k ∈ Finset.range (l + 1),
          supAbs (fun z θ => (z + 1) ^ k * pzIter k f z θ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' : k ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [show (fun z θ => (z + 1) ^ k * pzIter k (fun z θ => c * f z θ) z θ)
          = fun z θ => c * ((z + 1) ^ k * pzIter k f z θ) from by
        funext z θ; rw [pzIter_const_mul']; ring]
    exact supAbs_const_mul_le hc (hmem.1 k hk')
  have hM : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        if 1 ≤ j ∧ k + j ≤ l then
          supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j (fun z θ => c * f z θ)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0)
      ≤ c * ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        (if 1 ≤ j ∧ k + j ≤ l then
          supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    by_cases hcond : 1 ≤ j ∧ k + j ≤ l
    · rw [if_pos hcond, if_pos hcond]
      rw [show (fun z θ => (z + 1) ^ k * pzIter k (DthIter j (fun z θ => c * f z θ)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          = fun z θ => c * ((z + 1) ^ k * pzIter k (DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) from by
        funext z θ; rw [DthIter_const_mul', pzIter_const_mul']; ring]
      exact supAbs_const_mul_le hc (hmem.2 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
        k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hcond.1 hcond.2)
    · rw [if_neg hcond, if_neg hcond, mul_zero]
  rw [Work.Spaces.WlInf, Work.Spaces.WlInf, mul_add]
  exact add_le_add hZ hM

/-! ## The requested statement -/

theorem N0coefA4_WlInf6 : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
    Work.Spaces.WlInfMem α 6
      (fun z θ => (3 / (2 * α)) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
    Work.Spaces.WlInf α 6
      (fun z θ => (3 / (2 * α)) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
        ≤ C * α := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FTS.StrongPersist.DthFstar_W6
  refine ⟨3 * C₀ / 2, by linarith, fun α hα hα1 => ?_⟩
  have hmem : WlInfMem α 6 (Work.Spaces.Dth (Work.Construction.Fstar α)) := (hC₀ α hα hα1).1
  have hbnd : WlInf α 6 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ C₀ * α ^ 2 :=
    (hC₀ α hα hα1).2
  have hcpos : (0 : ℝ) < 3 / (2 * α) := by positivity
  have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Construction.Fstar α)) :=
    (smoothOpen_of_smoothQuad' (Work.FTS.LocData.SmoothQuad_Fstar α)).Dth
  refine ⟨smoothOpen_const_mul (3 / (2 * α)) hsm, WlInfMem_const_mul' (3 / (2 * α)) hmem, ?_⟩
  calc Work.Spaces.WlInf α 6
        (fun z θ => (3 / (2 * α)) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
      ≤ (3 / (2 * α)) * Work.Spaces.WlInf α 6 (Work.Spaces.Dth (Work.Construction.Fstar α)) :=
        WlInf_const_mul_le hcpos.le hmem
    _ ≤ (3 / (2 * α)) * (C₀ * α ^ 2) := mul_le_mul_of_nonneg_left hbnd hcpos.le
    _ = (3 * C₀ / 2) * α := by
        field_simp

end

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
