/-
# `PL/Uhol` — `PsiU` is entire and bounded, hence constant (Liouville)

The cut-free extension `PsiU` of `Work.GATE2.PL.Urec` is

* continuous on all of `ℂ`,
* the inverse of the Fatou coordinate far to the right (`PsiU_far`),
* equivariant for the shift: `F c₀ (PsiU w) = PsiU (w + 1)`,

and it avoids the critical values of `G5 c₀` (`PsiU_notMem_critVals`).  From the latter we deduce
that `PsiU` never meets a critical point of the holomorphic iterate `F c₀ = (Tsq c₀)^[5]`: if some
`(T_{c₀})^[m] (PsiU w)`, `m ≤ 9`, vanished, then either the intertwining relation
`G5 (PsiU w) = PsiU (sig w)` (for `m ≤ 4`) or the shift relation `F (PsiU w) = PsiU (w + 1)` (for
`5 ≤ m ≤ 9`) would exhibit a critical value as a value of `PsiU`, which is impossible.

Consequently `deriv (F c₀)` does not vanish on the image of `PsiU`, and analyticity propagates
from the right half-plane `{Re > X}` (where `PsiU` is the inverse of the injective analytic
Fatou coordinate `φa` on `Pg`) to all of `ℂ` by `Work.GATE2.PL.analyticAt_of_shift_global`.

Finally `PsiU` is bounded (`‖PsiU w‖ ≤ max 2 ‖c₀‖`), so by Liouville it is constant; but on the
half-plane `{Re > X}` it is injective (`φa (PsiU w) = w`), contradiction.  This is the last step
of `eq_c0_of_good`.
-/
import Mathlib
import Submission.Work.GATE2.ExitPathInputs
import Submission.Work.GATE2.ExitPath
import Submission.Work.GATE2.PL.Defs
import Submission.Work.GATE2.PL.UCore
import Submission.Work.GATE2.PL.Uavoid
import Submission.Work.GATE2.PL.Urec
import Submission.Work.GATE2.PL.deriv_tsqIterate_ne_zero_of_iterate_ne_zero
import Submission.Work.ELRig.analyticOnNhd_invFunOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

open Set Function Filter
open scoped Topology
open Classical
open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-! ## Propagation of analyticity along a shift (local copy)

The following two lemmas are the abstract engine of `PsiU_analytic`: they are a self-contained copy
of `Work.GATE2.PL.analyticAt_of_shift` / `analyticAt_of_shift_global`, kept here so that this file
(in particular the proof of `eq_c0_of_good`) does not depend on any external file that may change.
-/

/-- **Propagation of analyticity one step to the left along a shift.**  If `ψ` is continuous at
`w₀`, is analytic at `w₀ + 1`, and `F (ψ z) = ψ (z + 1)` for `z` near `w₀`, with `F` analytic at
`ψ w₀` and `deriv F (ψ w₀) ≠ 0`, then `ψ` is analytic at `w₀`. -/
theorem analyticAt_of_shift_one {F ψ : ℂ → ℂ} {w₀ : ℂ} (hF : AnalyticAt ℂ F (ψ w₀))
    (hderiv : deriv F (ψ w₀) ≠ 0) (hshift : F (ψ w₀) = ψ (w₀ + 1))
    (hψ1 : AnalyticAt ℂ ψ (w₀ + 1)) (hcont : ContinuousAt ψ w₀)
    (heq : ∀ᶠ z in nhds w₀, F (ψ z) = ψ (z + 1)) :
    AnalyticAt ℂ ψ w₀ := by
  have hρa : AnalyticAt ℂ (hF.hasStrictDerivAt.localInverse F (deriv F (ψ w₀)) (ψ w₀) hderiv)
      (F (ψ w₀)) := hF.analyticAt_localInverse hderiv
  have hρa' : AnalyticAt ℂ (hF.hasStrictDerivAt.localInverse F (deriv F (ψ w₀)) (ψ w₀) hderiv)
      (ψ (w₀ + 1)) := by rw [← hshift]; exact hρa
  have hρF : ∀ᶠ z in nhds (ψ w₀),
      hF.hasStrictDerivAt.localInverse F (deriv F (ψ w₀)) (ψ w₀) hderiv (F z) = z :=
    HasStrictDerivAt.eventually_left_inverse hF.hasStrictDerivAt hderiv
  have h2 : ψ =ᶠ[nhds w₀]
      fun z => hF.hasStrictDerivAt.localInverse F (deriv F (ψ w₀)) (ψ w₀) hderiv (ψ (z + 1)) := by
    filter_upwards [heq, hcont.eventually hρF] with z hz hzρ
    rw [← hzρ, hz]
  have h4 : AnalyticAt ℂ (fun z : ℂ => z + 1) w₀ := analyticAt_id.add analyticAt_const
  have h5 : AnalyticAt ℂ ψ ((fun z : ℂ => z + 1) w₀) := hψ1
  have h6 : AnalyticAt ℂ (fun z : ℂ => ψ (z + 1)) w₀ :=
    AnalyticAt.comp (f := fun z : ℂ => z + 1) (x := w₀) h5 h4
  have h7 : AnalyticAt ℂ
      (fun z => hF.hasStrictDerivAt.localInverse F (deriv F (ψ w₀)) (ψ w₀) hderiv (ψ (z + 1)))
      w₀ := AnalyticAt.comp (f := fun z : ℂ => ψ (z + 1)) (x := w₀) hρa' h6
  exact h7.congr h2.symm

/-- **Global propagation.**  If `ψ : ℂ → ℂ` is continuous, satisfies `F (ψ w) = ψ (w + 1)` for
all `w`, and `deriv F` does not vanish on the image of `ψ`, with `F` entire, then analyticity of
`ψ` on a right half-plane `{Re > X}` implies that `ψ` is analytic everywhere. -/
theorem analyticAt_of_shift_all {F ψ : ℂ → ℂ} (hcont : Continuous ψ)
    (hF : ∀ z, AnalyticAt ℂ F z) (hderiv : ∀ w : ℂ, deriv F (ψ w) ≠ 0)
    (hshift : ∀ w : ℂ, F (ψ w) = ψ (w + 1))
    {X : ℝ} (hbase : ∀ w : ℂ, X < w.re → AnalyticAt ℂ ψ w) :
    ∀ w : ℂ, AnalyticAt ℂ ψ w := by
  have hmain : ∀ n : ℕ, ∀ w : ℂ, X < w.re + (n : ℝ) → AnalyticAt ℂ ψ w := by
    intro n
    induction n with
    | zero =>
      intro w hw
      exact hbase w (by simpa using hw)
    | succ n ih =>
      intro w hw
      have hw1 : X < (w + 1).re + (n : ℝ) := by
        have h2 : w.re + ((n + 1 : ℕ) : ℝ) = w.re + 1 + (n : ℝ) := by push_cast; ring
        rw [h2] at hw
        simpa using hw
      have h1 : AnalyticAt ℂ ψ (w + 1) := ih (w + 1) hw1
      refine analyticAt_of_shift_one (hF (ψ w)) (hderiv w) (hshift w) h1 hcont.continuousAt ?_
      exact Eventually.of_forall fun z => hshift z
  intro w
  obtain ⟨n, hn⟩ := exists_nat_gt (X - w.re)
  exact hmain n w (by linarith)

variable (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) (G5 c₀) d.z₁)
variable (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) (G5 c₀) d.z₁ fl.Pa fl.φa)
variable {v X : ℝ} {Ψs : ℂ → ℂ}

/-! ## Avoidance of the critical values and of the critical points -/

/-- `PsiU` never takes a critical value of `G5 c₀ = (T_{c₀})^[5]`. -/
theorem PsiU_notMem_critVals (S : Seed fl FF v X Ψs) (w : ℂ) :
    PsiU fl FF S w ∉ critVals (c₀ := c₀) := by
  have h1 : w ∈ U X (lvl X w) := mem_U_lvl
  rw [PsiU_eq fl FF S h1]
  exact (seqU2 fl FF S (lvl X w)).2.avoid w h1

/-- The `k`-th iterate of `T_{c₀}` at the critical point `0` is the `(k-1)`-st iterate at `c₀`. -/
theorem Tantibar_iterate_zero_eq (c : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    (Tantibar c)^[k] 0 = (Tantibar c)^[k - 1] c := by
  have h : k = (k - 1) + 1 := by omega
  conv_lhs => rw [h]
  rw [Function.iterate_succ_apply]
  simp [Tantibar]

/-- **`PsiU` avoids the critical points of `F c₀ = (T_{c₀})^[10]`.**  If `(T_{c₀})^[m] (PsiU w)`
vanished for some `m ≤ 9`, then the intertwining relation with `sig` (for `m ≤ 4`) or the shift
relation `F (PsiU w) = PsiU (w + 1)` (for `5 ≤ m ≤ 9`) would exhibit a critical value
`T_{c₀}^[j] c₀`, `j ≤ 4`, as a value of `PsiU`, contradicting `PsiU_notMem_critVals`. -/
theorem PsiU_iterate_ne_zero (S : Seed fl FF v X Ψs) (w : ℂ) {m : ℕ} (hm : m ≤ 9) :
    (Tantibar c₀)^[m] (PsiU fl FF S w) ≠ 0 := by
  intro hzero
  rcases lt_or_ge m 5 with hm5 | hm5
  · -- `m ≤ 4`: use the intertwining relation `G5 (PsiU w) = PsiU (sig w)`
    have hsplit : (Tantibar c₀)^[5] (PsiU fl FF S w)
        = (Tantibar c₀)^[5 - m] ((Tantibar c₀)^[m] (PsiU fl FF S w)) := by
      have h : (5 : ℕ) = (5 - m) + m := by omega
      conv_lhs => rw [h]
      exact Function.iterate_add_apply (Tantibar c₀) (5 - m) m (PsiU fl FF S w)
    have hz : (Tantibar c₀)^[5 - m] (0 : ℂ) = (Tantibar c₀)^[4 - m] c₀ := by
      have h : 5 - m = (4 - m) + 1 := by omega
      conv_lhs => rw [h]
      rw [Function.iterate_succ_apply]
      simp [Tantibar]
    have hcrit : PsiU fl FF S (sig w) = (Tantibar c₀)^[4 - m] c₀ := by
      rw [← PsiU_anti fl FF S w, show G5 c₀ = (Tantibar c₀)^[5] from rfl, hsplit, hzero, hz]
    exact PsiU_notMem_critVals fl FF S (sig w) ⟨4 - m, by omega, hcrit⟩
  · -- `5 ≤ m ≤ 9`: use the shift relation `F (PsiU w) = PsiU (w + 1)`
    have hsplit : Work.EL.F c₀ (PsiU fl FF S w)
        = (Tantibar c₀)^[10 - m] ((Tantibar c₀)^[m] (PsiU fl FF S w)) := by
      rw [show Work.EL.F c₀ = (Tantibar c₀)^[10] from Work.EL.F_eq_tantibar c₀]
      have h : (10 : ℕ) = (10 - m) + m := by omega
      conv_lhs => rw [h]
      exact Function.iterate_add_apply (Tantibar c₀) (10 - m) m (PsiU fl FF S w)
    have hz : (Tantibar c₀)^[10 - m] (0 : ℂ) = (Tantibar c₀)^[9 - m] c₀ := by
      have h : 10 - m = (9 - m) + 1 := by omega
      conv_lhs => rw [h]
      rw [Function.iterate_succ_apply]
      simp [Tantibar]
    have hcrit : PsiU fl FF S (w + 1) = (Tantibar c₀)^[9 - m] c₀ := by
      rw [← PsiU_shift fl FF S w, hsplit, hzero, hz]
    exact PsiU_notMem_critVals fl FF S (w + 1) ⟨9 - m, by omega, hcrit⟩

/-- **The multiplier of `F c₀` does not vanish on the image of `PsiU`.** -/
theorem PsiU_deriv_ne_zero (S : Seed fl FF v X Ψs) (w : ℂ) :
    deriv (Work.EL.F c₀) (PsiU fl FF S w) ≠ 0 := by
  have h : ∀ m : ℕ, m ≤ 2 * 5 - 1 → (Tantibar c₀)^[m] (PsiU fl FF S w) ≠ 0 := by
    intro m hm
    exact PsiU_iterate_ne_zero fl FF S w (by omega)
  have h5 := deriv_tsqIterate_ne_zero_of_iterate_ne_zero (c := c₀) (z := PsiU fl FF S w)
    (k := 5) (by norm_num) h
  rwa [show Work.EL.F c₀ = (Work.Landing.Tsq c₀)^[5] from rfl]

/-! ## Analyticity -/

/-- `Ψs` restricted to the right half-plane is the inverse of the injective analytic Fatou
coordinate `φa` on the sub-petal `Pg`, hence analytic. -/
theorem PsiU_analytic_right (S : Seed fl FF v X Ψs) {w : ℂ} (hw : X < w.re) :
    AnalyticAt ℂ (PsiU fl FF S) w := by
  -- `φa` is analytic on the open set `Pg`, and injective there
  have hφa_diff : DifferentiableOn ℂ fl.φa FF.Pg := fl.φa_fatou.1.2.1.mono FF.Pg_sub
  have hφa_an : AnalyticOnNhd ℂ fl.φa FF.Pg := fun x hx =>
    hφa_diff.analyticAt (FF.isOpen_Pg.mem_nhds hx)
  have hinj : Set.InjOn fl.φa FF.Pg := fl.φa_fatou.2.mono FF.Pg_sub
  have hbase_an : AnalyticOnNhd ℂ (Function.invFunOn fl.φa FF.Pg) (fl.φa '' FF.Pg) :=
    Work.ELRig.analyticOnNhd_invFunOn FF.isOpen_Pg hφa_an hinj
  obtain ⟨hwPg, hwφa⟩ := PsiU_far fl FF S hw
  have hmem : w ∈ fl.φa '' FF.Pg := ⟨PsiU fl FF S w, hwPg, hwφa⟩
  have h1 : AnalyticAt ℂ (Function.invFunOn fl.φa FF.Pg) w := hbase_an w hmem
  -- on the open half-plane `{Re > X}` the two functions agree
  have hev : (PsiU fl FF S) =ᶠ[nhds w] Function.invFunOn fl.φa FF.Pg := by
    refine Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw) ?_
    intro u hu
    obtain ⟨huPg, huφa⟩ := PsiU_far fl FF S hu
    have hmem' : ∃ a ∈ FF.Pg, fl.φa a = u := ⟨PsiU fl FF S u, huPg, huφa⟩
    have h1' : Function.invFunOn fl.φa FF.Pg u ∈ FF.Pg := Function.invFunOn_mem hmem'
    have h2' : fl.φa (Function.invFunOn fl.φa FF.Pg u) = u := Function.invFunOn_eq hmem'
    exact (fl.φa_fatou.2 (FF.Pg_sub h1') (FF.Pg_sub huPg) (by rw [h2', huφa])).symm
  exact (analyticAt_congr hev).mpr h1

/-- **`PsiU` is analytic everywhere**: analyticity on `{Re > X}` propagates one unit to the left
along the shift relation, using the local analytic inverse of `F c₀` at a non-critical point. -/
theorem PsiU_analytic (S : Seed fl FF v X Ψs) (w : ℂ) : AnalyticAt ℂ (PsiU fl FF S) w := by
  refine analyticAt_of_shift_all (F := Work.EL.F c₀) (ψ := PsiU fl FF S) (X := X)
    (PsiU_cont fl FF S) ?_ ?_ ?_ ?_ w
  · intro z
    have hF_diff : Differentiable ℂ (Work.EL.F c₀) := by
      rw [show Work.EL.F c₀ = (Work.Landing.Tsq c₀)^[5] from rfl]
      have hT : Differentiable ℂ (Work.Landing.Tsq c₀) := by
        show Differentiable ℂ (fun z : ℂ => (z ^ 2 + star c₀) ^ 2 + c₀)
        fun_prop
      exact hT.iterate 5
    exact (hF_diff.differentiableOn.analyticOn isOpen_univ).analyticAt Filter.univ_mem
  · intro u
    exact PsiU_deriv_ne_zero fl FF S u
  · intro u
    exact PsiU_shift fl FF S u
  · intro u hu
    exact PsiU_analytic_right fl FF S hu

/-- `PsiU` is complex differentiable on all of `ℂ`. -/
theorem PsiU_differentiable (S : Seed fl FF v X Ψs) : Differentiable ℂ (PsiU fl FF S) :=
  fun w => (PsiU_analytic fl FF S w).differentiableAt

/-! ## Boundedness and Liouville -/

/-- `PsiU` is bounded (`‖PsiU w‖ ≤ max 2 ‖c₀‖` for all `w`). -/
theorem PsiU_isBounded_range (S : Seed fl FF v X Ψs) (hK : fl.Pa ⊆ Work.EL.K c₀) :
    Bornology.IsBounded (Set.range (PsiU fl FF S)) := by
  have h : ∀ w : ℂ, ‖PsiU fl FF S w‖ ≤ max 2 ‖c₀‖ := fun w => PsiU_norm_le fl FF S hK w
  rw [Metric.isBounded_range_iff]
  refine ⟨2 * max 2 ‖c₀‖, fun x y => ?_⟩
  rw [dist_eq_norm]
  calc ‖PsiU fl FF S x - PsiU fl FF S y‖
      ≤ ‖PsiU fl FF S x‖ + ‖PsiU fl FF S y‖ := norm_sub_le _ _
    _ ≤ max 2 ‖c₀‖ + max 2 ‖c₀‖ := by linarith [h x, h y]
    _ = 2 * max 2 ‖c₀‖ := by ring

/-- **A bounded differentiable function with the inverse-Fatou-coordinate property on a
half-plane cannot exist.**  This is the contradiction that closes `eq_c0_of_good`: `PsiU` would be
constant, but `φa (PsiU w) = w` on `{Re > X}` forces two distinct real points to have distinct
images. -/
theorem PsiU_not_bounded_differentiable (S : Seed fl FF v X Ψs) :
    ¬ (Differentiable ℂ (PsiU fl FF S) ∧
        ∃ C : ℝ, ∀ w : ℂ, ‖PsiU fl FF S w‖ ≤ C) := by
  rintro ⟨hdiff, C, hC⟩
  have hbdd : Bornology.IsBounded (Set.range (PsiU fl FF S)) := by
    rw [Metric.isBounded_range_iff]
    refine ⟨2 * |C|, fun x y => ?_⟩
    rw [dist_eq_norm]
    calc ‖PsiU fl FF S x - PsiU fl FF S y‖
        ≤ ‖PsiU fl FF S x‖ + ‖PsiU fl FF S y‖ := norm_sub_le _ _
      _ ≤ |C| + |C| := by
          have h1 := hC x
          have h2 := hC y
          rw [abs_of_nonneg (le_trans (norm_nonneg _) h1)] at *
          linarith
      _ = 2 * |C| := by ring
  obtain ⟨c, hc⟩ := hdiff.exists_eq_const_of_bounded hbdd
  have h1 : PsiU fl FF S (((X + 1 : ℝ) : ℂ)) = c := congrFun hc _
  have h2 : PsiU fl FF S (((X + 2 : ℝ) : ℂ)) = c := congrFun hc _
  have hr1 : X < (((X + 1 : ℝ) : ℂ)).re := by simp
  have hr2 : X < (((X + 2 : ℝ) : ℂ)).re := by simp
  have e1 : fl.φa (PsiU fl FF S (((X + 1 : ℝ) : ℂ))) = (((X + 1 : ℝ)) : ℂ) :=
    (PsiU_far fl FF S hr1).2
  have e2 : fl.φa (PsiU fl FF S (((X + 2 : ℝ) : ℂ))) = (((X + 2 : ℝ)) : ℂ) :=
    (PsiU_far fl FF S hr2).2
  rw [h1] at e1
  rw [h2] at e2
  have hbad : (((X + 1 : ℝ)) : ℂ) = (((X + 2 : ℝ)) : ℂ) := by rw [← e1, ← e2]
  have : X + 1 = X + 2 := by exact_mod_cast hbad
  linarith

end

end Work.GATE2.PL
