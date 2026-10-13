import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.E4R3.Flow5
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.RawE6IneqFlow
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.sixthChapterB_leaf_of_uniform
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.GronwallAbsorb
import Submission.Work.FTS.StrongEps.E4R3.Decay3Aux.ellPkg_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.ChapterOfS2` — the level-six chapter from the semi-tame estimate `S2`

`sixthChapterBF_of_S2` is the assembly of `SixthChapterBF` (the level-six chapter over the flow
class) out of the four already-proved ingredients of the route:

* the **energy identity** `S4` over the flow class (`E4R5.rawE6_deriv_of_flow`, proved);
* the **`ε`-uniform superlinear defect inequality L-A** (`E4R4.rawE6_ineq_flow`, proved from the
  semi-tame estimate `S2` and the pairing estimate `H6Pair_ones3`);
* **Grönwall with an absorbed quadratic defect** (`E4R4.gronwall_absorb`, proved);
* the **Cauchy–Schwarz bound** for the level-six pairing (`exists_IP6o_cs_uniform`, proved),
  which prices the datum's energy `rawE6 α g 0 = IP6o α g₀ g₀ ≤ CC·(K α²)²`.

The elliptic constant is replaced by `Ce⁺ = max Ce 1` (the packages are monotone in `Ce`,
`Decay3Aux.ellPkg_mono`), so that the positive constant required by `H6Pair_ones3` is available
for *every* `Ce`.  This module is imported both by `E4R3/sixthChapterBF_leaf.lean` (the target)
and by `Nblock6/Assembly.lean` (which produces `S2Stmt` from the `N`-block groups), so that the
dependency on the groups stays acyclic.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The semi-tame estimate `S2`** — the type of `EpsWPSemitame.epsWP_semitame` (and the exact
first argument of `E4R4.rawE6_ineq_flow`): the level-4 and level-6 semi-tame size of the projected
right-hand side `epsWP`, with a constant chosen after `α` (hence allowed to depend on `α`) but
*before* the data, the mollifier parameter `ε` and the solution. -/
abbrev S2Stmt : Prop :=
  ∀ C₀ Ce Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀, ∃ Ct : ℝ, 0 ≤ Ct ∧
    ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}, Work.FTS.StrongEps.IsSmoothKernel ρ →
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs → Work.FTS.StrongEps.MuLamOK α C₀ Φs E →
    ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ (g : Fam) (τ : ℝ),
      Work.FTS.ClassC.ClassC α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
      Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
      Work.FTS.VocabO.HQo α 6 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ) ∧
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ)
        ≤ Ct * (1 + Work.Spaces.HkNorm α 5 (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) ∧
      Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ)
        ≤ Ct * (1 + Work.Spaces.HkNorm α 7 (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ))
          + Ct * (1 + Work.Spaces.HkNorm α 6 (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) ^ 2

/-- **The level-six chapter from the semi-tame estimate.**  `E₁` is chosen before `ε₆`, and the
`ε`-threshold is `(Λ+1)/(C₁·2(1+E₀)e^{2(Λ+1)T} + 1)` — the Grönwall smallness condition. -/
theorem sixthChapterBF_of_S2 (hS2 : S2Stmt) {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) :
    ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ →
      Work.FTS.StrongEps.EpsE4Thr.E4R5.SixthChapterBF Ce Cs C₀ ρ := by
  classical
  set Ce' : ℝ := max Ce 1 with hCe'def
  have hCe'pos : 0 < Ce' := lt_of_lt_of_le one_pos (le_max_right Ce 1)
  have hCe'le : Ce ≤ Ce' := le_max_left Ce 1
  have HLAfun : ∀ C₀ Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀, ∃ Λ C₁ : ℝ,
      0 ≤ Λ ∧ 0 ≤ C₁ ∧ ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
      Work.FTS.StrongEps.EpsE4Thr.E4Data α C₀ K Ce' Cs ρ Φs E g₀ →
        Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ T : ℝ, 0 < T → ∀ g : Fam,
        Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g →
          Work.FTS.StrongEps.EpsRegP α ρ ε T g →
        Work.FTS.StrongEps.EpsE4Thr.E4R5.EpsFlowP α ρ ε T Φs E g →
        (∀ τ ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
          ≤ C₀ * α ^ 2) →
        ∀ τ ∈ Set.Ioo 0 T,
          2 * Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o α
            (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) (slice g τ)
            ≤ Λ * (1 + Work.FTS.StrongEps.EpsE4Thr.E4R4.rawE6 α g τ)
              + ε * C₁ * (1 + Work.FTS.StrongEps.EpsE4Thr.E4R4.rawE6 α g τ) ^ 2 :=
    fun C₀ Cs => Work.FTS.StrongEps.EpsE4Thr.E4R4.rawE6_ineq_flow hS2 hρ hρs
      (Ce := Ce') hCe'pos C₀ Cs
  obtain ⟨CC, hCCpos, hCS⟩ := Work.FTS.StrongEps.E4R3.Apriori4Proofs.exists_IP6o_cs_uniform
  refine ⟨1, ?_⟩
  intro C₀ hC₀
  have hC₀0 : (0 : ℝ) ≤ C₀ := le_trans zero_le_one hC₀
  obtain ⟨α₀, hα₀pos, Hα⟩ := HLAfun C₀ Cs
  refine ⟨min α₀ 1, lt_min hα₀pos one_pos, min_le_right _ _, ?_⟩
  intro α' hα' K Φs E g₀ hdat hstar6 T hT
  have hα'0 : 0 < α' := hα'.1
  have hα'1 : α' ≤ 1 := le_trans hα'.2 (min_le_right _ _)
  have hα'a : α' ∈ Set.Ioc 0 α₀ := ⟨hα'0, le_trans hα'.2 (min_le_left _ _)⟩
  have hα'Ioc : α' ∈ Set.Ioc (0 : ℝ) 1 := ⟨hα'0, hα'1⟩
  obtain ⟨Λ, C₁, hΛnn, hC₁nn, Hineq⟩ := Hα α' hα'a
  -- the datum, transported to the positive elliptic constant
  have hdat' : Work.FTS.StrongEps.EpsE4Thr.E4Data α' C₀ K Ce' Cs ρ Φs E g₀ :=
    ⟨hdat.1, hdat.2.1, (fun u hu => Work.FTS.StrongEps.E4R3.Decay3Aux.ellPkg_mono hCe'le
        (hdat.2.2.1 u hu)), hdat.2.2.2.1, hdat.2.2.2.2.1, hdat.2.2.2.2.2.1,
      hdat.2.2.2.2.2.2.1, hdat.2.2.2.2.2.2.2⟩
  have hKnn : 0 ≤ K := hdat.1
  have hX6₀ : Work.FTS.StrongGlobal.Xn6 α' g₀ ≤ K * α' ^ 2 := hdat.2.2.2.2.2.2.2
  -- the datum's `ℋ⁶`-honesty and its level-six energy
  have hd1 : Work.FTS.StrongEps.EpsDatum α' ρ 1 g₀ := hdat.2.2.2.2.2.1 1 one_pos
  have hg₀Qo : Work.FTS.VocabO.HQo α' 6 g₀ := ⟨hd1.1, hd1.2.1⟩
  have hXn₀nn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α' g₀ := Work.Spaces.HkNorm_nonneg α' 6 g₀
  set E0 : ℝ := CC * (K * α' ^ 2) ^ 2 with hE0def
  have hE0nn : 0 ≤ E0 := by rw [hE0def]; exact mul_nonneg hCCpos.le (sq_nonneg _)
  set M : ℝ := (1 + E0) * Real.exp (2 * (Λ + 1) * T) with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]; exact mul_pos (by linarith) (Real.exp_pos _)
  refine ⟨max (K ^ 2) (max 0 (M - 1)), le_trans (sq_nonneg K) (le_max_left _ _), ?_⟩
  refine ⟨le_max_left _ _, ?_⟩
  refine ⟨min 1 ((Λ + 1)
      / (C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T)) + 1)),
    lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro ε hε T' hT' hT'le g hsol hreg hflow hball τ hτ
  have hεpos : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := le_trans hε.2 (min_le_left _ _)
  have hε6 : ε ≤ (Λ + 1) / (C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T)) + 1) :=
    le_trans hε.2 (min_le_right _ _)
  -- L-A along the flow
  have hineq : ∀ σ ∈ Set.Ioo 0 T',
      2 * Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o α'
          (Work.FTS.StrongEps.epsRHSP α' ρ ε Φs E g σ) (slice g σ)
        ≤ Λ * (1 + Work.FTS.StrongEps.EpsE4Thr.E4R4.rawE6 α' g σ)
          + ε * C₁ * (1 + Work.FTS.StrongEps.EpsE4Thr.E4R4.rawE6 α' g σ) ^ 2 :=
    fun σ hσ => Hineq hdat' hstar6 ε ⟨hεpos, hε1⟩ T' hT' g hsol hreg hflow hball σ hσ
  -- the energy identity S4 over the flow class
  obtain ⟨hcontRA, hderiv⟩ :=
    Work.FTS.StrongEps.EpsE4Thr.E4R5.rawE6_deriv_of_flow hα'Ioc hreg hflow
  -- the datum's energy
  have he0 : Work.FTS.StrongEps.EpsE4Thr.E4R4.rawE6 α' g 0 ≤ E0 := by
    have hslice0 : slice g 0 = g₀ := funext fun z => funext fun θ => hsol.1 z θ
    have hraw : Work.FTS.StrongEps.EpsE4Thr.E4R4.rawE6 α' g 0
        = Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o α' g₀ g₀ := by
      show Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o α' (slice g 0) (slice g 0) = _
      rw [hslice0]
    rw [hraw, hE0def]
    have hcs := hCS α' hα'Ioc g₀ g₀ hg₀Qo hg₀Qo
    have hle : Work.FTS.StrongGlobal.Xn6 α' g₀ * Work.FTS.StrongGlobal.Xn6 α' g₀
        ≤ (K * α' ^ 2) * (K * α' ^ 2) :=
      mul_le_mul hX6₀ hX6₀ hXn₀nn (by positivity)
    calc Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o α' g₀ g₀
        ≤ |Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o α' g₀ g₀| := le_abs_self _
      _ ≤ CC * Work.FTS.StrongGlobal.Xn6 α' g₀ * Work.FTS.StrongGlobal.Xn6 α' g₀ := hcs
      _ = CC * (Work.FTS.StrongGlobal.Xn6 α' g₀ * Work.FTS.StrongGlobal.Xn6 α' g₀) := by ring
      _ ≤ CC * ((K * α' ^ 2) * (K * α' ^ 2)) := mul_le_mul_of_nonneg_left hle hCCpos.le
      _ = CC * (K * α' ^ 2) ^ 2 := by ring
  -- the Grönwall smallness condition
  have hexp_le : Real.exp (2 * (Λ + 1) * T') ≤ Real.exp (2 * (Λ + 1) * T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hT'le (by linarith)
  have hXnn : 0 ≤ C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T)) := by positivity
  have hsmall : ε * C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T'))
      ≤ Λ + 1 := by
    have h1 : ε * C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T'))
        ≤ ε * C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T)) := by
      have hcoef : 0 ≤ ε * C₁ * (2 * (1 + E0)) := by positivity
      have := mul_le_mul_of_nonneg_left hexp_le hcoef
      calc ε * C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T'))
          = ε * C₁ * (2 * (1 + E0)) * Real.exp (2 * (Λ + 1) * T') := by ring
        _ ≤ ε * C₁ * (2 * (1 + E0)) * Real.exp (2 * (Λ + 1) * T) := this
        _ = ε * C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T)) := by ring
    have h2 : ε * C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T))
        ≤ (Λ + 1) / (C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T)) + 1)
            * (C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T))) := by
      have heq : ε * C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T))
          = ε * (C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T))) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hε6 hXnn
    have h3 : (Λ + 1) / (C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T)) + 1)
        * (C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T))) ≤ Λ + 1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0 : ℝ)
        < C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T)) + 1)]
      nlinarith [hXnn, hΛnn]
    linarith [h1, h2, h3]
  have hgr := Work.FTS.StrongEps.EpsE4Thr.E4R4.gronwall_absorb (e :=
      Work.FTS.StrongEps.EpsE4Thr.E4R4.rawE6 α' g) (T := T') (Λ := Λ) (C₁ := C₁) (ε := ε)
      (E0 := E0) hT' hΛnn hC₁nn hεpos.le hE0nn hcontRA
      (fun σ hσ => ⟨2 * Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o α'
          (Work.FTS.StrongEps.epsRHSP α' ρ ε Φs E g σ) (slice g σ), hderiv σ hσ,
        hineq σ hσ⟩) he0 hsmall
  have hfin := hgr τ hτ
  have h2 : 1 + Work.FTS.StrongEps.EpsE4Thr.E4R4.rawE6 α' g τ ≤ M := by
    rw [hMdef]
    exact le_trans hfin (mul_le_mul_of_nonneg_left hexp_le (by linarith))
  have h3 : Work.FTS.StrongEps.EpsE4Thr.E4R4.rawE6 α' g τ ≤ M - 1 := by linarith
  exact le_trans h3 (le_trans (le_max_right (0 : ℝ) (M - 1)) (le_max_right (K ^ 2) _))

end Work.FTS.StrongEps.E4R3
