/-
Copyright: work module for the Elgindi finite-time singularity project.

# `StrongPersist/IP6_cs_coeffs` — Cauchy–Schwarz for the level-six pairing `IP6`

The package `H6Coer` of `StrongPersist/Defs.lean` asks, among other things, for the
Cauchy–Schwarz clause of the level-six inner product `IP6`,

  `|IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α f g| ≤ CC · |f|_{ℋ⁶} · |g|_{ℋ⁶}`

for every `α ∈ (0, α₂]` and every pair of honest `ℋ⁶` profiles — with a **single** constant
`CC`, independent of `α` and depending only on the ten step coefficients.  This file proves
it.

## The route

`IP6` is the paper's recursion `IP^{k+1} = HkIPStep c₁ c₂ IP^k = IP^k + c₁ IP^k(D_θ·,D_θ·) +
c₂ IP^k(D_z·,D_z·)` (tex 686), applied five times on top of `H1IP`:

  `IP6 = HkIPStep e₁ e₂ (HkIPStep f₁ f₂ (HkIPStep c₁'' c₂'' (HkIPStep c₁' c₂' (HkIPStep c₁ c₂ H1IP))))`

(see `StrongPersist/IP6_eq` and `IPGen.IPnG_eq_IP4`).  So it suffices to

1. bound the **base** `H1IP` against the `ℋ¹`-norm on the honest `ℋ¹`-class: this is the
   proved lemma `CoercivityFix.Transfer.H1IP_cs_of_mem` (Cauchy–Schwarz for the four
   weighted pairings of `H1IP`, with the sharp constant `10^22`, needing only
   `HkMem α 1` — no smoothness, no boundary traces);
2. lift one level at a time, `abs_HkIPStep_le` below: a Cauchy–Schwarz bound for `IP`
   against the `ℋⁿ`-norm gives one for `HkIPStep c₁ c₂ IP` against the `ℋ^{n+1}`-norm with
   the constant multiplied by `1 + |c₁| + |c₂|`.  The only inputs are the two comparison
   inequalities `HkNorm α n (D_θ u) ≤ HkNorm α (n+1) u`, `HkNorm α n (D_z u) ≤
   HkNorm α (n+1) u` (`HkSq_Dth_le_ge` and the open-class `D_z`-shift proved here) together
   with their unshifted instance `HkSq_mono_le`, and the descent of the honest class along
   `D_θ`, `D_z` (`IPGen.HkMem_Dth_le`, `IPGen.HkMem_Dz_le`).

Five lifts give the stated bound.  **No positivity of the step coefficients is used** (the
triangle inequality is taken with `|c₁|`, `|c₂|`), so the ten coefficients remain
completely free — which is what the caller needs, since `H6Coer` is consumed with the
coefficients that the coercivity chapter's induction produces.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.ClauseFields
import Submission.Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem
import Submission.Work.FTS.CoercivityFix.Assembly.HkSq_Dth_le_ge
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.EllipticEst.UopHk.hkMemDzPth_of_shifted
import Submission.Work.FTS.IPGen.OpenBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Descent of the honest class along the two recursion slots -/

/-- The honest `ℋⁿ`-class is preserved by `D_θ` when the level drops by one. -/
theorem hqo_dth {α : ℝ} {n : ℕ} {u : Fn} (hα : -(1 / 10 : ℝ) ≤ α)
    (hu : Work.FTS.VocabO.HQo α (n + 1) u) : Work.FTS.VocabO.HQo α n (Work.Spaces.Dth u) :=
  ⟨hu.1.Dth, Work.FTS.IPGen.HkMem_Dth_le hα hu.1 hu.2⟩

/-- The honest `ℋⁿ`-class is preserved by `D_z` when the level drops by one. -/
theorem hqo_dz {α : ℝ} {n : ℕ} {u : Fn} (hu : Work.FTS.VocabO.HQo α (n + 1) u) :
    Work.FTS.VocabO.HQo α n (Work.Spaces.Dz u) :=
  ⟨hu.1.Dz, Work.FTS.IPGen.HkMem_Dz_le hu.1 hu.2⟩

/-- The honest `ℋˡ`-class for `l ≤ k` is contained in the honest `ℋᵏ`-class. -/
theorem hqo_mono {α : ℝ} {k l : ℕ} {u : Fn} (hkl : l ≤ k) (hu : Work.FTS.VocabO.HQo α k u) :
    Work.FTS.VocabO.HQo α l u :=
  ⟨hu.1, Work.FTS.IPGen.HkMem_mono_le hu.1 l hkl hu.2⟩

/-! ## The three norm comparisons of the recursion step -/

/-- The `ℋⁿ`-norm of `u` is dominated by its `ℋ^{n+1}`-norm. -/
theorem hkNorm_mono {α : ℝ} {n : ℕ} {u : Fn} (hu : Work.Spaces.HkMem α (n + 1) u) :
    Work.Spaces.HkNorm α n u ≤ Work.Spaces.HkNorm α (n + 1) u :=
  Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hu)

/-- The `ℋⁿ`-norm of `D_θ u` is dominated by the `ℋ^{n+1}`-norm of `u`
(`CoercivityFix.Assembly.HkSq_Dth_le_ge` in square-root form). -/
theorem hkNorm_dth {α : ℝ} {n : ℕ} {u : Fn} (hα : 0 < α)
    (hu : Work.Spaces.HkMem α (n + 1) u) :
    Work.Spaces.HkNorm α n (Work.Spaces.Dth u) ≤ Work.Spaces.HkNorm α (n + 1) u :=
  Real.sqrt_le_sqrt (Work.FTS.CoercivityFix.Assembly.HkSq_Dth_le_ge α (by linarith) n hu)

/-- **The `D_z`-index shift for the squared `ℋ`-norm, in the open class**: for a profile
which is `C^∞` on the open quadrant and honest in `ℋ^{n+1}`, the squared `ℋⁿ`-norm of
`D_z u` is dominated by the squared `ℋ^{n+1}`-norm of `u`.  This is
`CoercivityStep.Norm.HkSq_Dz_le` with the analytic hypothesis `SmoothNbhd` weakened to
`SmoothOpen` (the pointwise domination of the integrands is the same,
`EllipticEst.UopHk.HkIntegrand_Dz_le_succ`). -/
theorem hkSq_dz_le_open (α : ℝ) (n : ℕ) {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hm : Work.Spaces.HkMem α (n + 1) u) :
    Work.Spaces.HkSq α n (Work.Spaces.Dz u) ≤ Work.Spaces.HkSq α (n + 1) u := by
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dz u) z θ) hm.2 ?_
  show ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (Work.Spaces.Dz u) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (n + 1) u z θ
  exact MeasureTheory.ae_restrict_of_forall_mem hmesz fun z hz =>
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dz u) z θ)
      (hm.1 z hz)
      (MeasureTheory.ae_restrict_of_forall_mem hmesθ fun θ hθ =>
        Work.FTS.EllipticEst.UopHk.HkIntegrand_Dz_le_succ α n hu z θ hz hθ)

/-- The `ℋⁿ`-norm of `D_z u` is dominated by the `ℋ^{n+1}`-norm of `u`, in the open class. -/
theorem hkNorm_dz {α : ℝ} {n : ℕ} {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hm : Work.Spaces.HkMem α (n + 1) u) :
    Work.Spaces.HkNorm α n (Work.Spaces.Dz u) ≤ Work.Spaces.HkNorm α (n + 1) u :=
  Real.sqrt_le_sqrt (hkSq_dz_le_open α n hu hm)

/-! ## The arithmetic of the triple product -/

/-- `CC * A * B ≤ CC * A' * B'` for nonnegative `CC`, `A`, `B` and `A ≤ A'`, `B ≤ B'`. -/
theorem mul_three_le {CC A A' B B' : ℝ} (hCC : 0 ≤ CC) (hA : A ≤ A') (hB : B ≤ B')
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) : CC * A * B ≤ CC * A' * B' := by
  have h1 : CC * A ≤ CC * A' := mul_le_mul_of_nonneg_left hA hCC
  have h2 : CC * A * B ≤ CC * A' * B := mul_le_mul_of_nonneg_right h1 hB0
  have h3 : CC * A' * B ≤ CC * A' * B' :=
    mul_le_mul_of_nonneg_left hB (mul_nonneg hCC (le_trans hA0 hA))
  linarith

/-! ## One step of the recursion -/

/-- **One step of the Cauchy–Schwarz recursion.**  If `IP` satisfies a Cauchy–Schwarz bound
against the `ℋⁿ`-norm with constant `CC`, then `HkIPStep c₁ c₂ IP` satisfies one against the
`ℋ^{n+1}`-norm with constant `(1 + |c₁| + |c₂|) · CC`: the three slots `u`, `D_θu`, `D_zu`
of `HkIPStep` all sit inside the `(n+1)`-ball (`hkNorm_mono`, `hkNorm_dth`, `hkNorm_dz`),
and the triangle inequality is taken with `|c₁|`, `|c₂|`.  No positivity of the coefficients
is needed. -/
theorem abs_HkIPStep_le {α : ℝ} (hα : 0 < α) {n : ℕ} {IP : Fn → Fn → ℝ} {CC c₁ c₂ : ℝ}
    (hCC : 0 ≤ CC)
    (hcs : ∀ u v : Fn, Work.FTS.VocabO.HQo α n u → Work.FTS.VocabO.HQo α n v →
      |IP u v| ≤ CC * Work.Spaces.HkNorm α n u * Work.Spaces.HkNorm α n v) :
    ∀ u v : Fn, Work.FTS.VocabO.HQo α (n + 1) u → Work.FTS.VocabO.HQo α (n + 1) v →
      |Work.Coercivity.HkIPStep c₁ c₂ IP u v|
        ≤ (1 + |c₁| + |c₂|) * CC * Work.Spaces.HkNorm α (n + 1) u
            * Work.Spaces.HkNorm α (n + 1) v := by
  have hα' : -(1 / 10 : ℝ) ≤ α := by linarith
  intro u v hu hv
  -- the six slots of the step, and their norm comparisons
  have hun : Work.FTS.VocabO.HQo α n u := hqo_mono (Nat.le_succ n) hu
  have hvn : Work.FTS.VocabO.HQo α n v := hqo_mono (Nat.le_succ n) hv
  have huth : Work.FTS.VocabO.HQo α n (Work.Spaces.Dth u) := hqo_dth hα' hu
  have hvth : Work.FTS.VocabO.HQo α n (Work.Spaces.Dth v) := hqo_dth hα' hv
  have huz : Work.FTS.VocabO.HQo α n (Work.Spaces.Dz u) := hqo_dz hu
  have hvz : Work.FTS.VocabO.HQo α n (Work.Spaces.Dz v) := hqo_dz hv
  have e0u : Work.Spaces.HkNorm α n u ≤ Work.Spaces.HkNorm α (n + 1) u := hkNorm_mono hu.2
  have e0v : Work.Spaces.HkNorm α n v ≤ Work.Spaces.HkNorm α (n + 1) v := hkNorm_mono hv.2
  have e1u : Work.Spaces.HkNorm α n (Work.Spaces.Dth u) ≤ Work.Spaces.HkNorm α (n + 1) u :=
    hkNorm_dth hα hu.2
  have e1v : Work.Spaces.HkNorm α n (Work.Spaces.Dth v) ≤ Work.Spaces.HkNorm α (n + 1) v :=
    hkNorm_dth hα hv.2
  have e2u : Work.Spaces.HkNorm α n (Work.Spaces.Dz u) ≤ Work.Spaces.HkNorm α (n + 1) u :=
    hkNorm_dz hu.1 hu.2
  have e2v : Work.Spaces.HkNorm α n (Work.Spaces.Dz v) ≤ Work.Spaces.HkNorm α (n + 1) v :=
    hkNorm_dz hv.1 hv.2
  -- the three terms of the step
  have hA : |IP u v| ≤ CC * Work.Spaces.HkNorm α (n + 1) u
      * Work.Spaces.HkNorm α (n + 1) v :=
    le_trans (hcs u v hun hvn)
      (mul_three_le hCC e0u e0v (Work.Spaces.HkNorm_nonneg α n u)
        (Work.Spaces.HkNorm_nonneg α n v))
  have hB : |IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) u * Work.Spaces.HkNorm α (n + 1) v :=
    le_trans (hcs _ _ huth hvth)
      (mul_three_le hCC e1u e1v (Work.Spaces.HkNorm_nonneg α n (Work.Spaces.Dth u))
        (Work.Spaces.HkNorm_nonneg α n (Work.Spaces.Dth v)))
  have hC : |IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) u * Work.Spaces.HkNorm α (n + 1) v :=
    le_trans (hcs _ _ huz hvz)
      (mul_three_le hCC e2u e2v (Work.Spaces.HkNorm_nonneg α n (Work.Spaces.Dz u))
        (Work.Spaces.HkNorm_nonneg α n (Work.Spaces.Dz v)))
  set Z : ℝ := CC * Work.Spaces.HkNorm α (n + 1) u * Work.Spaces.HkNorm α (n + 1) v with hZ
  have htri : |IP u v + c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)
      + c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
      ≤ Z + |c₁| * Z + |c₂| * Z := by
    have h1 : |IP u v + c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)
        + c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
        ≤ |IP u v + c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
          + |c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)| := abs_add_le _ _
    have h2 : |IP u v + c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
        ≤ |IP u v| + |c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)| := abs_add_le _ _
    have h3 : |c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
        = |c₁| * |IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)| := abs_mul _ _
    have h4 : |c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
        = |c₂| * |IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)| := abs_mul _ _
    have h5 : |c₁| * |IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)| ≤ |c₁| * Z :=
      mul_le_mul_of_nonneg_left hB (abs_nonneg c₁)
    have h6 : |c₂| * |IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)| ≤ |c₂| * Z :=
      mul_le_mul_of_nonneg_left hC (abs_nonneg c₂)
    linarith
  have hstep : Work.Coercivity.HkIPStep c₁ c₂ IP u v
      = IP u v + c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)
        + c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v) := rfl
  rw [hstep]
  calc |IP u v + c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)
        + c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
      ≤ Z + |c₁| * Z + |c₂| * Z := htri
    _ = (1 + |c₁| + |c₂|) * CC * Work.Spaces.HkNorm α (n + 1) u
          * Work.Spaces.HkNorm α (n + 1) v := by
        rw [hZ]; ring

/-! ## The level-six Cauchy–Schwarz bound -/

/-- **Cauchy–Schwarz for the level-six pairing `IP6`**, for arbitrary coefficients: there is
a constant `CC > 0`, depending only on the ten step coefficients, such that
`|IP6 … α f g| ≤ CC |f|_{ℋ⁶} |g|_{ℋ⁶}` for every `α ∈ (0, α₂]` and every pair of honest
`ℋ⁶` profiles. -/
theorem IP6_cs_coeffs (e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α₂ : ℝ) (hα₂ : 0 < α₂) :
    ∃ CC : ℝ, 0 < CC ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 6 f → Work.FTS.VocabO.HQo α 6 g →
      |Work.FTS.StrongPersist.IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α f g|
        ≤ CC * Work.FTS.StrongPersist.Xn6 α f * Work.FTS.StrongPersist.Xn6 α g := by
  -- the constant: five lifts, each multiplying by `1 + |c₁| + |c₂|`
  let C0 : ℝ := 10 ^ 22
  let C1 : ℝ := (1 + |c₁| + |c₂|) * C0
  let C2 : ℝ := (1 + |c₁'| + |c₂'|) * C1
  let C3 : ℝ := (1 + |c₁''| + |c₂''|) * C2
  let C4 : ℝ := (1 + |f₁| + |f₂|) * C3
  let C5 : ℝ := (1 + |e₁| + |e₂|) * C4
  have hC0 : 0 < C0 := by norm_num
  have h1 : (0 : ℝ) < 1 + |c₁| + |c₂| := by
    have a := abs_nonneg c₁; have b := abs_nonneg c₂; linarith
  have h2 : (0 : ℝ) < 1 + |c₁'| + |c₂'| := by
    have a := abs_nonneg c₁'; have b := abs_nonneg c₂'; linarith
  have h3 : (0 : ℝ) < 1 + |c₁''| + |c₂''| := by
    have a := abs_nonneg c₁''; have b := abs_nonneg c₂''; linarith
  have h4 : (0 : ℝ) < 1 + |f₁| + |f₂| := by
    have a := abs_nonneg f₁; have b := abs_nonneg f₂; linarith
  have h5 : (0 : ℝ) < 1 + |e₁| + |e₂| := by
    have a := abs_nonneg e₁; have b := abs_nonneg e₂; linarith
  have hC1 : 0 < C1 := mul_pos h1 hC0
  have hC2 : 0 < C2 := mul_pos h2 hC1
  have hC3 : 0 < C3 := mul_pos h3 hC2
  have hC4 : 0 < C4 := mul_pos h4 hC3
  have hC5 : 0 < C5 := mul_pos h5 hC4
  refine ⟨C5, hC5, ?_⟩
  intro α hα f g hf hg
  have hα0 : 0 < α := hα.1
  -- the base: `H1IP` against the `ℋ¹`-norm on the honest class
  have cs0 : ∀ u v : Fn, Work.FTS.VocabO.HQo α 1 u → Work.FTS.VocabO.HQo α 1 v →
      |Work.Coercivity.H1IP α u v| ≤ C0 * Work.Spaces.HkNorm α 1 u * Work.Spaces.HkNorm α 1 v :=
    fun u v hu hv => Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem α hα0 u v hu.2 hv.2
  -- the five lifts
  have cs1 := abs_HkIPStep_le hα0 (c₁ := c₁) (c₂ := c₂) (le_of_lt hC0) cs0
  have cs2 := abs_HkIPStep_le hα0 (c₁ := c₁') (c₂ := c₂') (le_of_lt hC1) cs1
  have cs3 := abs_HkIPStep_le hα0 (c₁ := c₁'') (c₂ := c₂'') (le_of_lt hC2) cs2
  have cs4 := abs_HkIPStep_le hα0 (c₁ := f₁) (c₂ := f₂) (le_of_lt hC3) cs3
  have cs5 := abs_HkIPStep_le hα0 (c₁ := e₁) (c₂ := e₂) (le_of_lt hC4) cs4
  -- identify the composite with `IP6`
  have hIP4 : Work.Coercivity.HkIPStep c₁'' c₂''
        (Work.Coercivity.HkIPStep c₁' c₂'
          (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α)))
      = Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α := by
    simpa only [Work.FTS.IPGen.IPnG_succ, Work.FTS.IPGen.IPnG_zero] using
      Work.FTS.IPGen.IPnG_eq_IP4 (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
        (c₁'' := c₁'') (c₂'' := c₂'') (α := α)
  have hIP6 : Work.FTS.StrongPersist.IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α
      = Work.Coercivity.HkIPStep e₁ e₂ (Work.Coercivity.HkIPStep f₁ f₂
          (Work.Coercivity.HkIPStep c₁'' c₂'' (Work.Coercivity.HkIPStep c₁' c₂'
            (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α))))) := by
    rw [Work.FTS.StrongPersist.IP6, hIP4]
  rw [hIP6]
  exact cs5 f g hf hg

end Work.FTS.StrongPersist
