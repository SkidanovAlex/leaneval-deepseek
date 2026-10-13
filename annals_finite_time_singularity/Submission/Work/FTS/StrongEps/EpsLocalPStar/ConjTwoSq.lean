/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsLocalPStar/ConjTwoSq.lean` — the Lipschitz half of the `X`-gate `EpsRHSPLipX_Sq`

This module proves the second (Lipschitz) conjunct of the `X`-gate
`EpsRHSPLipX_Sq`: for the parameters of the projected `ε`-scheme there is a constant `L > 0` such
that for any two *admissible data* in the `X`-ball (`SmoothOpen`, `EpsMem`, `EpsSq ≤ R`, and the
class-`C` small ball on the projected-mollified profile `W_u = Wp ρ ε u`) the slice-integrated
right-hand side at time `0` is `X`-Lipschitz:

  `EpsSq α (epsRHPSlice … 0 u − epsRHPSlice … 0 v) ≤ L · EpsSq α (u − v)`.

It is a verbatim adaptation of `Work.FTS.StrongEps.EpsRLX.ConjTwo` (the same statement with the
strong `ℋ⁶`-data in place of the `X`-ball), with exactly two changes:

* the uniform `ℋᵏ`-size (`k ≤ 6`) of the profiles `W_u`, `W_v` comes from
  `EpsLocalPStar.exists_Wp_bound_of_EpsMem` (whose hypotheses `SmoothOpen`, `EpsMem`, `EpsSq ≤ R`
  are exactly the ball hypotheses) instead of `WpSixBound`/`WpUniformBound`;
* the level-`5` `ℋ`-size of the profile difference comes from
  `EpsLocalPStar.HkSq_Wp_sub_le_of_ClassC` (whose `ClassC`/`EpsMem α (u − v)` hypotheses are in
  the statement) instead of `DeltaData`.

Everything else (the decomposition `epsRHPSlice … u − epsRHPSlice … v = Pz (J_ε Φ_u) − Pz (J_ε Φ_v)`,
`Jeps_sub_eq`, `EpsSq_Jeps_le`, `DiffTraces` + `TraceToEpsMem`, `HkSq α 1 Δ ≤ (Xn α Δ)²`,
`DeltaXnBound`, the constant chase and the `max 1 L` at the end) is copied unchanged.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsLocalPStar.XBallFacts
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceToEpsMem
import Submission.Work.FTS.StrongEps.EpsRLX.XDataClean
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaXnBound
import Submission.Work.FTS.StrongEps.EpsRLX.BasicFacts
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_Pz_sub_le
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.EpsSq_Jeps_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongEps.EpsRLX (Wp)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem ConjTwoSq {α C₀ Ce Cs R : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 < L ∧
      (∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen u →
        Work.FTS.EllipticEst.SmoothOpen v →
        Work.FTS.StrongEps.EpsMem α u →
        Work.FTS.StrongEps.EpsSq α u ≤ R →
        Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) →
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ C₀ * α ^ 2 →
        Work.FTS.StrongEps.EpsMem α v → Work.FTS.StrongEps.EpsSq α v ≤ R →
        Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) →
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ C₀ * α ^ 2 →
        Work.FTS.StrongEps.EpsMem α (fun z θ => u z θ - v z θ) →
        Work.FTS.StrongEps.EpsSq α (fun z θ => Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u z θ
            - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v z θ)
          ≤ L * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
  have hα0 : 0 < α := hα.1
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα0
    linarith
  -- ## the six constants
  obtain ⟨K₁, hK₁pos, hK₁⟩ := Work.FTS.StrongEps.EpsRLX.DeltaXnBound (α := α) (C₀ := C₀)
    (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) hα hEll hstar hml
  obtain ⟨CP, hCPpos, hCP⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSq_Pz_sub_le
  obtain ⟨CM, hCMpos, hCM⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6 ρ hρ
  obtain ⟨CJ, hCJpos, hCJ⟩ := Work.FTS.StrongEps.EpsSq_Jeps_le ρ hρ.moll
  obtain ⟨CT, hCTpos, hCT⟩ := Work.FTS.StrongEps.EpsLocalPStar.TraceToEpsMem
  obtain ⟨CD, hCDpos, hCD⟩ := Work.FTS.StrongEps.EpsLocalPStar.HkSq_Wp_sub_le_of_ClassC ρ hρ
  obtain ⟨CW, hCWpos, hCW⟩ := Work.FTS.StrongEps.EpsLocalPStar.exists_Wp_bound_of_EpsMem ρ hρ
  -- ## the uniform `ℋᵏ`-size (`k ≤ 6`) of an admissible profile, from the `X`-ball
  set BS : ℝ := CW * (CW / ε) ^ 6 * (1 + R) with hBSdef
  have hBS0 : 0 ≤ BS := by
    rw [hBSdef]
    have hdiv : 0 ≤ CW / ε := div_nonneg hCWpos.le hε.le
    exact mul_nonneg (mul_nonneg hCWpos.le (pow_nonneg hdiv 6)) (by linarith)
  have hWp : ∀ {f : Fn}, Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.StrongEps.EpsMem α f →
      Work.FTS.StrongEps.EpsSq α f ≤ R → ∀ k : ℕ, k ≤ 6 →
      Work.Spaces.HkNorm α k (Wp ρ ε f) ≤ BS := by
    intro f hf hm hRf k hk
    exact hCW α hα ε ⟨hε, hε1⟩ R hR f hf hm hRf k hk
  -- ## the uniform a-priori data of `profRHS` at such a profile
  obtain ⟨BR, hBRpos, hRX⟩ := Work.FTS.StrongEps.EpsRLX.XDataClean (α := α) (Ce := Ce) (Cs := Cs)
    (C₀ := C₀) (B := BS) hα hEll hstar hml hBS0
  -- ## the profile-factor parameter `M₀`
  set M₀ : ℝ := 1 + 2 * BS with hM₀def
  have hM₀1 : 1 ≤ M₀ := by rw [hM₀def]; linarith
  have hM₀0 : 0 ≤ M₀ := le_trans zero_le_one hM₀1
  -- ## the Lipschitz constant
  set L : ℝ := CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2) * K₁ ^ 2 * M₀ ^ 4
    * CD * (CD / ε) ^ 12 with hLdef
  refine ⟨max 1 L, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u v hu hv hmemu hSqu hclu hxnu hmemv hSqv hclv hxnv hmemuv
  -- ## the abbreviations
  set Φu : Fn := profRHS α Φs E (Wp ρ ε u) with hΦudef
  set Φv : Fn := profRHS α Φs E (Wp ρ ε v) with hΦvdef
  set Δ : Fn := fun z θ => Φu z θ - Φv z θ with hΔdef
  set d : Fn := fun z θ => Wp ρ ε u z θ - Wp ρ ε v z θ with hddef
  have hdXN : Work.Spaces.HkNorm α 5 d
      = Work.Spaces.HkNorm α 5 (fun z θ => Wp ρ ε u z θ - Wp ρ ε v z θ) := by rw [hddef]
  -- ## the smoothness / honesty / size of `Δ`
  obtain ⟨hΔsm₀, hΔmem₀, hΔxn₀⟩ :=
    hK₁ (W₁ := Wp ρ ε u) (W₂ := Wp ρ ε v) hclu hclv hxnu hxnv
  have hΔsm : Work.FTS.EllipticEst.SmoothOpen Δ := by
    rw [hΔdef]
    simpa only [hΦudef, hΦvdef, Wp] using hΔsm₀
  have hΔmem4 : Work.Spaces.HkMem α 4 Δ := by
    rw [hΔdef]
    simpa only [hΦudef, hΦvdef, Wp] using hΔmem₀
  have hΔxn : Work.FTS.Nonlin.Xn α Δ
      ≤ K₁ * (1 + Work.Spaces.HkNorm α 5 (Wp ρ ε u)
          + Work.Spaces.HkNorm α 5 (Wp ρ ε v)) ^ 2 * Work.Spaces.HkNorm α 5 d := by
    rw [hΔdef, hdXN]
    simpa only [hΦudef, hΦvdef, Wp] using hΔxn₀
  have hΔmem1 : Work.Spaces.HkMem α 1 Δ :=
    Work.FTS.OpenPkg.HkMem_mono_open hΔsm 1 (by norm_num) hΔmem4
  -- ## `EpsMem`/`EpsSq` of `Δ` via the vanishing traces
  obtain ⟨ht1, ht2⟩ := Work.FTS.StrongEps.EpsRLX.DiffTraces (α := α) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (W₁ := Wp ρ ε u) (W₂ := Wp ρ ε v) (E := E) hα hclu hclv
    ((hEll (Wp ρ ε u) hclu).1) ((hEll (Wp ρ ε v) hclv).1) hstar
  have ht1' : ∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ => Δ z θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro z hz
    have hfun : (fun θ => Δ z θ) = fun θ : ℝ =>
        profRHS α Φs E (Wp ρ ε u) z θ - profRHS α Φs E (Wp ρ ε v) z θ := by
      funext θ
      simp only [hΔdef, hΦudef, hΦvdef]
    rw [hfun]
    exact ht1 z hz
  have ht2' : ∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ => Δ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    intro z hz
    have hfun : (fun θ => Δ z θ) = fun θ : ℝ =>
        profRHS α Φs E (Wp ρ ε u) z θ - profRHS α Φs E (Wp ρ ε v) z θ := by
      funext θ
      simp only [hΔdef, hΦudef, hΦvdef]
    rw [hfun]
    exact ht2 z hz
  obtain ⟨hΔepsMem, hΔepsSq⟩ := hCT α hα Δ hΔsm hΔmem1 ht1' ht2'
  -- ## `HkSq α 1 Δ ≤ (Xn α Δ)²`
  have hΔHk : Work.Spaces.HkSq α 1 Δ ≤ (Work.FTS.Nonlin.Xn α Δ) ^ 2 := by
    refine le_trans (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hΔmem4) ?_
    rw [show Work.FTS.Nonlin.Xn α Δ = Work.Spaces.HkNorm α 4 Δ from rfl, Work.Spaces.HkNorm,
      Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 Δ)]
  -- ## the smoothness / honesty of the two pre-mollified profiles
  have hXud := hRX (W := Wp ρ ε u) hclu hxnu (hWp hu hmemu hSqu 6 (by norm_num))
  have hXvd := hRX (W := Wp ρ ε v) hclv hxnv (hWp hv hmemv hSqv 6 (by norm_num))
  have hsmΦu : Work.FTS.EllipticEst.SmoothOpen Φu := by
    rw [hΦudef]; exact hXud.1
  have hsmΦv : Work.FTS.EllipticEst.SmoothOpen Φv := by
    rw [hΦvdef]; exact hXvd.1
  have hmem4Φu : Work.Spaces.HkMem α 4 Φu := by
    rw [hΦudef]; exact hXud.2.1
  have hmem4Φv : Work.Spaces.HkMem α 4 Φv := by
    rw [hΦvdef]; exact hXvd.2.1
  -- ## the mollified profile
  have hsmFact : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Δ) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Δ).mp hΔsm
  have hJepsΔmem : Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε Δ) :=
    (hCM α hα ε hε hε1 Δ hsmFact hΔepsMem).1
  have hJepsΔSq : Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Δ)
      ≤ Real.exp (CJ * ε) * Work.FTS.StrongEps.EpsSq α Δ :=
    hCJ α hα ε hε hε1 Δ hΔepsMem hJepsΔmem
  -- ## the `J_ε`-linearity and the `P₀`-bound
  have hJsub : Work.FTS.StrongEps.Jeps ρ ε Φu - Work.FTS.StrongEps.Jeps ρ ε Φv
      = Work.FTS.StrongEps.Jeps ρ ε Δ := by
    rw [hΔdef]
    exact Work.FTS.StrongEps.EpsRLX.Jeps_sub_eq hρ.moll hε hsmΦu hsmΦv
  have hsubMem : Work.FTS.StrongEps.EpsMem α
      (fun z θ => Work.FTS.StrongEps.Jeps ρ ε Φu z θ - Work.FTS.StrongEps.Jeps ρ ε Φv z θ) :=
    Work.FTS.StrongEps.EpsSqTools.EpsMem_congr
      (fun z θ => (congrFun (congrFun hJsub z) θ).symm) hJepsΔmem
  have hPzData := hCP α hα (Work.FTS.StrongEps.Jeps ρ ε Φu) (Work.FTS.StrongEps.Jeps ρ ε Φv)
    (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Φu).mp hsmΦu))
    (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Φv).mp hsmΦv))
    (Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Φu).mp hsmΦu) hmem4Φu)
    (Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Φv).mp hsmΦv) hmem4Φv)
    hsubMem
  have hEpsSqJsub : Work.FTS.StrongEps.EpsSq α
      (fun z θ => Work.FTS.StrongEps.Jeps ρ ε Φu z θ - Work.FTS.StrongEps.Jeps ρ ε Φv z θ)
      = Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Δ) :=
    Work.FTS.StrongEps.EpsSq_congr (fun z θ => congrFun (congrFun hJsub z) θ)
  -- ## the two right-hand sides
  have hslice : (fun z θ => Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u z θ
        - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v z θ)
      = (fun z θ => Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φu) z θ
        - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φv) z θ) := by
    funext z θ
    simp only [Work.FTS.StrongEps.EpsLocalPStar.epsRHPSlice_eq_profRHS, hΦudef, hΦvdef, Wp]
  -- ## the delta-data bound
  have hDd : (Work.Spaces.HkNorm α 5 d) ^ 2
      ≤ CD * (CD / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) := by
    rw [hddef, Work.Spaces.HkNorm,
      Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 5
        (fun z θ => Wp ρ ε u z θ - Wp ρ ε v z θ))]
    exact hCD α hα ε ⟨hε, hε1⟩ hu hv hclu hclv hmemuv
  -- ## the uniform profile factor
  have hWu : Work.Spaces.HkNorm α 5 (Wp ρ ε u) ≤ BS := hWp hu hmemu hSqu 5 (by norm_num)
  have hWv : Work.Spaces.HkNorm α 5 (Wp ρ ε v) ≤ BS := hWp hv hmemv hSqv 5 (by norm_num)
  have hMle : 1 + Work.Spaces.HkNorm α 5 (Wp ρ ε u) + Work.Spaces.HkNorm α 5 (Wp ρ ε v)
      ≤ M₀ := by
    rw [hM₀def]
    linarith
  have hM0 : 0 ≤ 1 + Work.Spaces.HkNorm α 5 (Wp ρ ε u)
      + Work.Spaces.HkNorm α 5 (Wp ρ ε v) := by
    have h1 : 0 ≤ Work.Spaces.HkNorm α 5 (Wp ρ ε u) := Work.Spaces.HkNorm_nonneg α 5 _
    have h2 : 0 ≤ Work.Spaces.HkNorm α 5 (Wp ρ ε v) := Work.Spaces.HkNorm_nonneg α 5 _
    linarith
  have hXs : (Work.FTS.Nonlin.Xn α Δ) ^ 2 ≤ (K₁ * M₀ ^ 2 * Work.Spaces.HkNorm α 5 d) ^ 2 := by
    refine pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 Δ) ?_ 2
    have hM2 : (1 + Work.Spaces.HkNorm α 5 (Wp ρ ε u)
        + Work.Spaces.HkNorm α 5 (Wp ρ ε v)) ^ 2 ≤ M₀ ^ 2 :=
      pow_le_pow_left₀ hM0 hMle 2
    have hZ : 0 ≤ Work.Spaces.HkNorm α 5 d := Work.Spaces.HkNorm_nonneg α 5 d
    calc Work.FTS.Nonlin.Xn α Δ
        ≤ K₁ * (1 + Work.Spaces.HkNorm α 5 (Wp ρ ε u)
            + Work.Spaces.HkNorm α 5 (Wp ρ ε v)) ^ 2 * Work.Spaces.HkNorm α 5 d := hΔxn
      _ ≤ K₁ * M₀ ^ 2 * Work.Spaces.HkNorm α 5 d :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM2 hK₁pos.le) hZ
  -- ## the final chain
  have hT0 : 0 ≤ CT / (Work.Spaces.gam α - 1) ^ 2 := div_nonneg hCTpos.le (pow_pos hγ 2).le
  have hE0 : 0 ≤ Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) :=
    Work.FTS.StrongEps.EpsSq_nonneg α _
  have hfinal : Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u z θ
          - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v z θ)
      ≤ CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2)
        * K₁ ^ 2 * M₀ ^ 4 * CD * (CD / ε) ^ 12
        * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) := by
    calc Work.FTS.StrongEps.EpsSq α (fun z θ =>
          Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u z θ
            - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v z θ)
        = Work.FTS.StrongEps.EpsSq α (fun z θ =>
            Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φu) z θ
              - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φv) z θ) :=
          Work.FTS.StrongEps.EpsSq_congr (fun z θ => congrFun (congrFun hslice z) θ)
      _ ≤ CP * Work.FTS.StrongEps.EpsSq α (fun z θ =>
            Work.FTS.StrongEps.Jeps ρ ε Φu z θ
              - Work.FTS.StrongEps.Jeps ρ ε Φv z θ) := hPzData.2
      _ = CP * Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Δ) := by
          rw [hEpsSqJsub]
      _ ≤ CP * (Real.exp (CJ * ε) * Work.FTS.StrongEps.EpsSq α Δ) :=
          mul_le_mul_of_nonneg_left hJepsΔSq hCPpos.le
      _ ≤ CP * (Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2
            * Work.Spaces.HkSq α 1 Δ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hΔepsSq (Real.exp_pos _).le) hCPpos.le
      _ ≤ CP * (Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2
            * (Work.FTS.Nonlin.Xn α Δ) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΔHk hT0)
              (Real.exp_pos _).le) hCPpos.le
      _ = CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2)
            * (Work.FTS.Nonlin.Xn α Δ) ^ 2 := by ring
      _ ≤ CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2)
            * (K₁ * M₀ ^ 2 * Work.Spaces.HkNorm α 5 d) ^ 2 :=
          mul_le_mul_of_nonneg_left hXs
            (mul_nonneg (mul_nonneg hCPpos.le (Real.exp_pos _).le) hT0)
      _ = CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2) * K₁ ^ 2 * M₀ ^ 4
            * (Work.Spaces.HkNorm α 5 d) ^ 2 := by ring
      _ ≤ CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2) * K₁ ^ 2 * M₀ ^ 4
            * (CD * (CD / ε) ^ 12
              * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
          refine mul_le_mul_of_nonneg_left hDd ?_
          have h1 : 0 ≤ CP * Real.exp (CJ * ε) :=
            mul_nonneg hCPpos.le (Real.exp_pos _).le
          have h2 : 0 ≤ CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2) :=
            mul_nonneg h1 hT0
          have h3 : 0 ≤ CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2)
              * K₁ ^ 2 := mul_nonneg h2 (pow_nonneg hK₁pos.le 2)
          exact mul_nonneg h3 (pow_nonneg hM₀0 4)
      _ = CP * Real.exp (CJ * ε) * (CT / (Work.Spaces.gam α - 1) ^ 2) * K₁ ^ 2 * M₀ ^ 4
            * CD * (CD / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) := by
          ring
  rw [← hLdef] at hfinal
  exact le_trans hfinal (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) L) hE0)

end Work.FTS.StrongEps.EpsLocalPStar
