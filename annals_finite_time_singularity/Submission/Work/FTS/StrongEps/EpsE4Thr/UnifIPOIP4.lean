/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/UnifIPOIP4.lean` — the reduction of the open-class
coercivity interface to **four** clauses

`OpenClass.UnifIPO` is the open-class analogue of the frozen `Nonlin.UnifIP`: the interface the
level-four barrier can be run against (`OpenBarrier.apriori_fourth_of_barrier_open`), because the
projected mollified slice `Pz (J_ε (slice g τ))` *does* lie in `CoerAdmO` along the route
(`OpenBarrier.coerAdmO_slice_JfamP`), while it does **not** lie in the frozen `CoerAdm`
(`CoerAdmSlice.coerAdm_slice_JfamP` reduces the latter to the unavailable `SmoothQuad`).

This module shows that for the concrete pairing of the paper,
`IP4 c₁ c₂ c₁' c₂' c₁'' c₂''` (`CoercivityFix.Assembly.IP4`), all the algebraic clauses of
`UnifIPO` are *already proved* on the open class:

* `symm` — `Assembly.vc_symm` above the unconditional base
  `CoercivityStep.Base.H1IP_comm`;
* `add_fst` — the `Comm2o` induction `IPGen.Comm2o_three` (used here without an `α`-range: it only
  needs `α > 0`), on `SmoothOpen` plus `HkMem α 4`;
* `smul_fst` — `IPGen.ip4_smul`, with no regularity at all;
* `congr_qd` — `IPGen.ip4_congr_Qd`, with no membership at all;
* `nonneg` — the three-fold `Assembly.vc_nonneg` above `Coercivity.H1IP_nonneg` (no regularity:
  each leaf of the recursion is a nonnegative-weighted square, and a non-integrable leaf
  integrates to the junk value `0`);
* `cs` — `IPGen.ip4_cs_HQo`, on `SmoothOpen` plus `HkMem α 4`.

Consequently `UnifIPO (IP4 …)` follows from exactly **four** clauses on the open class
`CoerAdmO`:

  `lo`  `clo·|f|²_{ℋ⁴} ≤ IP4 α f f`,
  `up`  `IP4 α f f ≤ Cup·|f|²_{ℋ⁴}`,
  `coer`  `cc·|f|²_{ℋ⁴} ≤ IP4 α (𝓛_Γ^T f) f`   (the coercivity of the linearised operator),
  `Dz_self`  `|IP4 α (D_z f) f| ≤ Cdz·|f|²_{ℋ⁴}`.

These four are the *only* analytic work that a re-run of the coercivity chapter against the open
class has to deliver; the shape of the corresponding frozen statements is `V_bounds.lo_four`,
`up_four`, `dz_four` and `Coer1.coer1_LGammaT` (all stated on the frozen `RegQ`/`CoerAdm`).

*Confluence note.*  This module deliberately uses the `IPGen`/`CoercivityFix` originals of the
algebraic clauses rather than the `StrongEps.IP4_*` wrappers of `IP4_Jeps_comm.lean`: the latter
imports `IP6_Jeps_comm`, which redeclares `Work.FTS.StrongEps.smoothOpen_Jeps` and therefore cannot
be combined with the `JepsSmoothOpen` cone in which the level-four chain lives.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.IPGen.Assembly
import Submission.Work.FTS.CoercivityFix.Assembly.V_core
import Submission.Work.Coercivity.H1IP_nonneg
import Submission.Work.FTS.CoercivityStep.Base.H1IP_add_snd
import Submission.Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem
import Submission.Work.FTS.StrongPersist.IP6_cs_coeffs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (Xn)

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4

/-- **Cauchy–Schwarz for `IP4` on the open class `RegQo α 4`, with an explicit constant**, valid
for every `α ∈ (0,1]`: three lifts of the recursion (`StrongPersist.abs_HkIPStep_le`, each
multiplying the constant by `1 + |c₁| + |c₂|`) above the `ℋ¹` base
`CoercivityFix.Transfer.H1IP_cs_of_mem`.  This is `StrongEps.IP4_cs_HQo` with the constant (and
the `α`-range `Ioc 0 1`) made explicit, so that a consumer can *name* the range of the interface it
builds. -/
theorem IP4_cs_open {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} :
    ∀ α ∈ Set.Ioc 0 1, ∀ f g : Fn, RegQo α 4 f → RegQo α 4 g →
      |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g|
        ≤ ((1 + |c₁''| + |c₂''|) * ((1 + |c₁'| + |c₂'|) * ((1 + |c₁| + |c₂|) * 10 ^ 22)))
          * Xn α f * Xn α g := by
  intro α hα f g hf hg
  have hα0 : 0 < α := hα.1
  have hbase : ∀ u v : Fn, Work.FTS.VocabO.HQo α 1 u → Work.FTS.VocabO.HQo α 1 v →
      |Work.Coercivity.H1IP α u v| ≤ 10 ^ 22 * Work.Spaces.HkNorm α 1 u
        * Work.Spaces.HkNorm α 1 v :=
    fun u v hu hv => Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem α hα0 u v hu.2 hv.2
  have h1 := Work.FTS.StrongPersist.abs_HkIPStep_le (α := α) hα0 (n := 1)
    (IP := Work.Coercivity.H1IP α) (CC := 10 ^ 22) (c₁ := c₁) (c₂ := c₂)
    (by norm_num) hbase
  have h2 := Work.FTS.StrongPersist.abs_HkIPStep_le (α := α) hα0 (n := 2)
    (IP := Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α))
    (CC := (1 + |c₁| + |c₂|) * 10 ^ 22) (c₁ := c₁') (c₂ := c₂') (by positivity) h1
  have h3 := Work.FTS.StrongPersist.abs_HkIPStep_le (α := α) hα0 (n := 3)
    (IP := Work.Coercivity.HkIPStep c₁' c₂'
      (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α)))
    (CC := (1 + |c₁'| + |c₂'|) * ((1 + |c₁| + |c₂|) * 10 ^ 22))
    (c₁ := c₁'') (c₂ := c₂'') (by positivity) h2
  simpa only [Work.FTS.CoercivityFix.Assembly.IP4] using h3 f g ⟨hf.1, hf.2.1⟩ ⟨hg.1, hg.2.1⟩

/-- **`UnifIPO` for the paper's pairing `IP4`, from the four open-class clauses.**

The six algebraic clauses of `UnifIPO` are proved on the open class (see the module docstring);
the four remaining clauses are taken as hypotheses, with the Cauchy–Schwarz constant taken from
`IP4_cs_open` (range `Ioc 0 1`) and the `D_z`-self constant returned by the last hypothesis.

The range of the resulting instance is pinned to `min α₂ 1`: the algebraic clauses and `symm`
hold for every `α > 0`, `add_fst` for every `α > 0`, and `cs` exactly on `Ioc 0 1`. -/
theorem unifIPO_IP4_of_open_clauses {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) (h₁' : 0 ≤ c₁') (h₂' : 0 ≤ c₂')
    (h₁'' : 0 ≤ c₁'') (h₂'' : 0 ≤ c₂'')
    {α₂ cc clo Cup : ℝ} (hα₂ : 0 < α₂) (hcc : 0 < cc) (hclo : 0 < clo) (hCup : 0 < Cup)
    (hlo : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, CoerAdmO α f →
      clo * Work.Spaces.HkSq α 4 f ≤ IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f f)
    (hup : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, CoerAdmO α f →
      IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f f ≤ Cup * Work.Spaces.HkSq α 4 f)
    (hcoer : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, CoerAdmO α f →
      cc * Work.Spaces.HkSq α 4 f
        ≤ IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Work.Coercivity.LGammaT α f) f)
    (hdz : ∃ Cdz : ℝ, 0 < Cdz ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, CoerAdmO α f →
      |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Work.Spaces.Dz f) f| ≤ Cdz * Xn α f ^ 2) :
    ∃ Ccs : ℝ, 0 < Ccs ∧
      UnifIPO (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') (min α₂ 1) cc clo Cup Ccs := by
  obtain ⟨Cdz, hCdz_pos, hdzb⟩ := hdz
  refine ⟨max ((1 + |c₁''| + |c₂''|)
    * ((1 + |c₁'| + |c₂'|) * ((1 + |c₁| + |c₂|) * 10 ^ 22))) Cdz,
    lt_max_iff.mpr (Or.inl (by positivity)), ?_⟩
  refine
    { pos := ⟨lt_min hα₂ one_pos, hcc, hclo, hCup,
        lt_of_lt_of_le (by positivity : (0:ℝ) < (1 + |c₁''| + |c₂''|)
          * ((1 + |c₁'| + |c₂'|) * ((1 + |c₁| + |c₂|) * 10 ^ 22))) (le_max_left _ _)⟩
      symm := fun α f g =>
        Work.FTS.CoercivityFix.Assembly.vc_symm (c₁ := c₁'') (c₂ := c₂'')
          (Work.FTS.CoercivityFix.Assembly.vc_symm (c₁ := c₁') (c₂ := c₂')
            (Work.FTS.CoercivityFix.Assembly.vc_symm (c₁ := c₁) (c₂ := c₂)
              (Work.FTS.CoercivityStep.Base.H1IP_comm α))) f g
      add_fst := ?_
      smul_fst := ?_
      congr_qd := ?_
      nonneg := ?_
      cs := ?_
      lo := ?_
      up := ?_
      coer := ?_
      Dz_self := ?_ }
  · intro α hα f₁ f₂ g h₁r h₂r h₃r
    exact (Work.FTS.IPGen.Comm2o_three α (by linarith [hα.1])).add f₁ f₂ g
      h₁r.1 h₂r.1 h₃r.1 h₁r.2.1 h₂r.2.1 h₃r.2.1
  · intro α _ c f g _ _
    exact Work.FTS.IPGen.ip4_smul c₁ c₂ c₁' c₂' c₁'' c₂'' c α f g
  · intro α hα f f' g _ _ hc
    exact Work.FTS.IPGen.ip4_congr_Qd (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
      (c₁'' := c₁'') (c₂'' := c₂'') (f := f) (f' := f') (g := g) hα.1 hc
  · intro α _ f _
    exact (Work.FTS.CoercivityFix.Assembly.vc_nonneg h₁'' h₂''
      (Work.FTS.CoercivityFix.Assembly.vc_nonneg h₁' h₂'
        (Work.FTS.CoercivityFix.Assembly.vc_nonneg h₁ h₂
          (fun u => Work.Coercivity.H1IP_nonneg α u)))) f
  · intro α hα f g hfr hgr
    have h := IP4_cs_open (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
      (c₁'' := c₁'') (c₂'' := c₂'') α
      ⟨hα.1, le_trans hα.2 (min_le_right _ _)⟩ f g hfr hgr
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ Cdz)
        (Work.Spaces.HkNorm_nonneg α 4 f)) (Work.Spaces.HkNorm_nonneg α 4 g)
  · intro α hα f hfr
    exact hlo α ⟨hα.1, le_trans hα.2 (min_le_left _ _)⟩ f hfr
  · intro α hα f hfr
    exact hup α ⟨hα.1, le_trans hα.2 (min_le_left _ _)⟩ f hfr
  · intro α hα f hfr
    exact hcoer α ⟨hα.1, le_trans hα.2 (min_le_left _ _)⟩ f hfr
  · intro α hα f hfr
    have h := hdzb α ⟨hα.1, le_trans hα.2 (min_le_left _ _)⟩ f hfr
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ Cdz) (by positivity)

end Work.FTS.StrongEps.EpsE4Thr
