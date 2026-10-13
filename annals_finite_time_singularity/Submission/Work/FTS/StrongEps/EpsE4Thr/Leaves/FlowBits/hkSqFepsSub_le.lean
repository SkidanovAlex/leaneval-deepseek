/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/Leaves/FlowBits/hkSqFepsSub_le.lean`

**The `ℋ⁶`-Lipschitz bound of the projected `ε`-scheme's right-hand side on the `X`-ball.**

For two profiles `u, v` in the `X`-ball invariant

    XBall α ρ ε R C₁ u  :=  SmoothOpen u ∧ EpsMem α u ∧ EpsSq α u ≤ R
                             ∧ ClassC α (W_u) ∧ Xn α (W_u) ≤ C₁ α²      (W_u = Pz (J_ε u))

of `EpsEngine.LocalStepXBall`, the right-hand side `Feps α ρ ε Φs E` of the projected scheme is
`ℋ⁶`-Lipschitz with respect to the *weighted `L²`-size* `EpsSq` of the datum difference:

    HkSq α 6 (Feps u − Feps v) ≤ C · EpsSq α (u − v)

with a constant `C > 0` depending only on the parameters (through the hypotheses), *not* on the
two profiles.

## The route (nothing new is needed; the five inputs are already proved)

Writing `W_f = Wp ρ ε f = Pz (J_ε f)` and `Δ = profRHS α Φs E W_u − profRHS α Φs E W_v` for the
difference of the *pre-mollified* right-hand sides, the difference of the scheme's right-hand
sides is

    Feps u − Feps v = Pz (J_ε Δ)

(`Feps` unfolds to `Pz (J_ε (profRHS (W_·)))`; `J_ε` is additive on the open quadrant
(`EpsRLX.Jeps_sub_eq`) and `P₀` is affine modulo its zero-mode, which the `ℋ⁴`-data of the two
mollified profiles supplies via `EComparison.L12_sub_HkMem` + `EpsRLX.Pz_sub_eq`).

1. **`EpsSq α Δ ≤ C (Xn α Δ)²`** — `EpsEngine.profRHSDiffEpsSq` (the sharp quadratic bound of the
   `ε`-energy of the pre-mollified difference).
2. **`Xn α Δ ≤ K (1 + Xn₅ W_u + Xn₅ W_v)² Xn₅ (W_u − W_v)`** — `EpsRLX.DeltaXnBound`.
3. **`Xn₅ W_f ≤ BS = CW (CW/ε)⁶ (1+R)`** — `EpsLocalPStar.exists_Wp_bound_of_EpsMem` (the uniform
   `ℋᵏ`-size of the projected-mollified profile, `k ≤ 6`, from the `X`-ball data alone).
4. **`HkSq α 5 (W_u − W_v) ≤ CD (CD/ε)¹² EpsSq α (u − v)`** —
   `EpsLocalPStar.HkSq_Wp_sub_le_of_ClassC`.
5. **`HkSq α 6 (Pz (J_ε Δ)) ≤ CH (CH/ε)¹² EpsSq α Δ`** — `EpsSqTools.HkSq_JepsPz_le` at `k = 6`.

Chaining 1–5 gives the claim, the constants being absorbed into one existential `C`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.EpsLocalPStar.ConjTwoSq
import Submission.Work.FTS.StrongEps.EpsLocalPStar.XBallFacts
import Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceToEpsMem
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaXnBound
import Submission.Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le
import Submission.Work.FTS.EpsEngine.EpsClass
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.EpsEngine.profRHSDiffEpsSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongEps
open Work.FTS.EpsEngine
open Work.FTS.GalFields (Xn5)
open Work.Spaces (HkSq HkNorm HkMem HkSq_nonneg HkNorm_nonneg)
open Work.FTS.Nonlin (Xn)
open Work.FTS.EllipticEst (SmoothOpen smoothOpen_iff_forall)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem hkSqFepsSub_le {α C₁ Ce Cs R ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₁ Φs E) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : Work.FTS.Galerkin.Fn,
      Work.FTS.EpsEngine.XBall α ρ ε R C₁ u → Work.FTS.EpsEngine.XBall α ρ ε R C₁ v →
      Work.Spaces.HkSq α 6 (fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ)
        ≤ C * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) := by
  have hα0 : 0 < α := hα.1
  have hε0 : 0 < ε := hε
  -- ## the five constants of the proof
  obtain ⟨CH, hCHpos, hCH⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  obtain ⟨K, hKpos, hK⟩ :=
    Work.FTS.StrongEps.EpsRLX.DeltaXnBound (α := α) (C₀ := C₁) (Ce := Ce) (Cs := Cs)
      (Φs := Φs) (E := E) hα hEll hstar hml
  obtain ⟨CD, hCDpos, hCD⟩ := Work.FTS.StrongEps.EpsLocalPStar.HkSq_Wp_sub_le_of_ClassC ρ hρ
  obtain ⟨CW, hCWpos, hCW⟩ := Work.FTS.StrongEps.EpsLocalPStar.exists_Wp_bound_of_EpsMem ρ hρ
  obtain ⟨CP, hCPpos, hCP⟩ :=
    Work.FTS.EpsEngine.profRHSDiffEpsSq (α := α) (C₀ := C₁) (Ce := Ce) (Cs := Cs)
      (Φs := Φs) (E := E) hα hEll hstar hml
  -- ## the uniform `ℋ⁶`-size `BS` of a projected-mollified profile of the ball
  set BS : ℝ := CW * (CW / ε) ^ 6 * (1 + R) with hBSdef
  have hBS0 : 0 ≤ BS := by
    rw [hBSdef]
    have h1 : 0 ≤ CW / ε := div_nonneg hCWpos.le hε0.le
    exact mul_nonneg (mul_nonneg hCWpos.le (pow_nonneg h1 6)) (by linarith)
  -- ## the composite constant
  set Λ : ℝ := CP * (K * (1 + 2 * BS) ^ 2) ^ 2 * CD * (CD / ε) ^ 12 with hΛdef
  -- ## the a-priori data of the pre-mollified profile, at the size `BS`
  obtain ⟨_, -, hXData⟩ :=
    Work.FTS.StrongEps.EpsRLX.XDataClean (α := α) (Ce := Ce) (Cs := Cs) (C₀ := C₁) (B := BS)
      hα hEll hstar hml hBS0
  refine ⟨max 1 (CH * (CH / ε) ^ 12 * Λ), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u v hu hv
  -- ## the honest membership of the datum difference
  have hak_u : Work.FTS.StrongEps.EpsSqTools.AK α u :=
    Work.FTS.StrongEps.EpsSqTools.AK_of_uncurry (Work.Spaces.aesm_of_continuousOn_Qd
      (Function.uncurry u)
      (((smoothOpen_iff_forall u).mp (XBall.smoothOpen hu)) 0).continuousOn)
  have hak_v : Work.FTS.StrongEps.EpsSqTools.AK α v :=
    Work.FTS.StrongEps.EpsSqTools.AK_of_uncurry (Work.Spaces.aesm_of_continuousOn_Qd
      (Function.uncurry v)
      (((smoothOpen_iff_forall v).mp (XBall.smoothOpen hv)) 0).continuousOn)
  have hmem_uv : EpsMem α (fun z θ => u z θ - v z θ) :=
    Work.FTS.StrongEps.EpsSqTools.EpsMem_sub hak_u hak_v (XBall.mem hu) (XBall.mem hv)
  set S : ℝ := EpsSq α (fun z θ => u z θ - v z θ) with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; exact EpsSq_nonneg α _
  -- ## the `ℋ⁵`-size of the profile difference
  have hdSq : HkSq α 5 (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
        - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ) ≤ CD * (CD / ε) ^ 12 * S := by
    rw [hSdef]
    exact hCD α hα ε ⟨hε0, hε1⟩ (XBall.smoothOpen hu) (XBall.smoothOpen hv)
      (XBall.classC hu) (XBall.classC hv) hmem_uv
  have hd5 : (Xn5 α (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
        - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)) ^ 2 ≤ CD * (CD / ε) ^ 12 * S := by
    rw [Work.FTS.GalFields.Xn5, HkNorm, Real.sq_sqrt (HkSq_nonneg α 5 _)]
    exact hdSq
  -- ## the uniform sizes of the two profiles
  have hWu5 : Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ BS := by
    rw [hBSdef]
    exact hCW α hα ε ⟨hε0, hε1⟩ R hR u (XBall.smoothOpen hu) (XBall.mem hu) (XBall.sq_le hu)
      5 (by norm_num)
  have hWv5 : Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ BS := by
    rw [hBSdef]
    exact hCW α hα ε ⟨hε0, hε1⟩ R hR v (XBall.smoothOpen hv) (XBall.mem hv) (XBall.sq_le hv)
      5 (by norm_num)
  have hWu6 : HkNorm α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ BS := by
    rw [hBSdef]
    exact hCW α hα ε ⟨hε0, hε1⟩ R hR u (XBall.smoothOpen hu) (XBall.mem hu) (XBall.sq_le hu)
      6 (by norm_num)
  have hWv6 : HkNorm α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ BS := by
    rw [hBSdef]
    exact hCW α hα ε ⟨hε0, hε1⟩ R hR v (XBall.smoothOpen hv) (XBall.mem hv) (XBall.sq_le hv)
      6 (by norm_num)
  have hMle : 1 + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
      + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ 1 + 2 * BS := by linarith
  have hM0 : 0 ≤ 1 + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
      + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) := by
    have h1 : 0 ≤ Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) := HkNorm_nonneg α 5 _
    have h2 : 0 ≤ Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) := HkNorm_nonneg α 5 _
    linarith
  -- ## the difference of the pre-mollified right-hand sides
  set Δ : Fn := fun z θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
        (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) z θ
      - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
        (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) z θ with hΔdef
  obtain ⟨hΔsm0, hΔmem40, hΔxn0⟩ :=
    hK (W₁ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) (W₂ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)
      (XBall.classC hu) (XBall.classC hv) (XBall.ball hu) (XBall.ball hv)
  have hΔsm : SmoothOpen Δ := by rw [hΔdef]; exact hΔsm0
  have hΔmem4 : HkMem α 4 Δ := by rw [hΔdef]; exact hΔmem40
  have hΔxn : Xn α Δ ≤ K * (1 + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
        + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) ^ 2
      * Xn5 α (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
          - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ) := by
    rw [hΔdef]; exact hΔxn0
  obtain ⟨hΔmemE0, hΔSqE0⟩ :=
    hCP (W₁ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) (W₂ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)
      (XBall.classC hu) (XBall.classC hv) (XBall.ball hu) (XBall.ball hv)
  have hΔmem : EpsMem α Δ := by rw [hΔdef]; exact hΔmemE0
  have hΔSq : EpsSq α Δ ≤ CP * (Xn α Δ) ^ 2 := by rw [hΔdef]; exact hΔSqE0
  -- ## the squared `ℋ⁴`-size of `Δ`
  have hkey : (Xn α Δ) ^ 2 ≤ (K * (1 + 2 * BS) ^ 2) ^ 2 * (CD * (CD / ε) ^ 12 * S) := by
    have h1 : (Xn α Δ) ^ 2
        ≤ (K * (1 + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
              + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) ^ 2
            * Xn5 α (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
                - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)) ^ 2 :=
      pow_le_pow_left₀ (HkNorm_nonneg α 4 Δ) hΔxn 2
    have h2 : K * (1 + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
          + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) ^ 2 ≤ K * (1 + 2 * BS) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM0 hMle 2) hKpos.le
    have h3 : (K * (1 + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
              + Xn5 α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) ^ 2
            * Xn5 α (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
                - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)) ^ 2
        ≤ (K * (1 + 2 * BS) ^ 2) ^ 2
          * (Xn5 α (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
              - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg hKpos.le (sq_nonneg _)) h2 2) (sq_nonneg _)
    exact h1.trans (h3.trans (mul_le_mul_of_nonneg_left hd5 (sq_nonneg _)))
  have hΔSq_le : EpsSq α Δ
      ≤ CP * ((K * (1 + 2 * BS) ^ 2) ^ 2 * (CD * (CD / ε) ^ 12 * S)) :=
    hΔSq.trans (mul_le_mul_of_nonneg_left hkey hCPpos.le)
  -- ## the `ℋ⁶`-bound of the mollified projected difference
  have hfin0 : HkSq α 6 (Pz (Jeps ρ ε Δ)) ≤ CH * (CH / ε) ^ 12 * EpsSq α Δ :=
    hCH α hα ε hε0 hε1 6 (by norm_num) Δ hΔsm hΔmem
  have hfin1 : HkSq α 6 (Pz (Jeps ρ ε Δ))
      ≤ CH * (CH / ε) ^ 12
        * (CP * ((K * (1 + 2 * BS) ^ 2) ^ 2 * (CD * (CD / ε) ^ 12 * S))) :=
    hfin0.trans (mul_le_mul_of_nonneg_left hΔSq_le (by positivity))
  -- ## the identification `Feps u − Feps v = Pz (J_ε Δ)`
  have hsmΦu : SmoothOpen (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)) :=
    (hXData (W := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) (XBall.classC hu) (XBall.ball hu) hWu6).1
  have hsmΦv : SmoothOpen (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) :=
    (hXData (W := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) (XBall.classC hv) (XBall.ball hv) hWv6).1
  have hmemΦu : HkMem α 4 (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)) :=
    (hXData (W := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) (XBall.classC hu) (XBall.ball hu) hWu6).2.1
  have hmemΦv : HkMem α 4 (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) :=
    (hXData (W := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) (XBall.classC hv) (XBall.ball hv) hWv6).2.1
  have hJsu : SmoothOpen (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u))) :=
    smoothOpen_Jeps ρ hρ hε0 ((smoothOpen_iff_forall _).mp hsmΦu)
  have hJsv : SmoothOpen (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v))) :=
    smoothOpen_Jeps ρ hρ hε0 ((smoothOpen_iff_forall _).mp hsmΦv)
  have hJmu : HkMem α 4 (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u))) :=
    HkMem_Jeps hρ.moll hα hε0 ((smoothOpen_iff_forall _).mp hsmΦu) hmemΦu
  have hJmv : HkMem α 4 (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v))) :=
    HkMem_Jeps hρ.moll hα hε0 ((smoothOpen_iff_forall _).mp hsmΦv) hmemΦv
  have hFu : Feps α ρ ε Φs E u = Pz (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u))) := rfl
  have hFv : Feps α ρ ε Φs E v = Pz (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
      (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v))) := rfl
  have hJsub : Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
        (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u))
      - Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
        (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v))
      = Jeps ρ ε (fun z θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) z θ
        - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) z θ) :=
    Work.FTS.StrongEps.EpsRLX.Jeps_sub_eq hρ.moll hε0 hsmΦu hsmΦv
  have hL12 : Work.Construction.L12 (fun z θ => Jeps ρ ε
        (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)) z θ
      - Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) z θ) 0
      = Work.Construction.L12 (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u))) 0
        - Work.Construction.L12 (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v))) 0 :=
    Work.FTS.StrongEps.EComparison.L12_sub_HkMem hJsu hJsv hJmu hJmv 0 (by simp [Work.Spaces.Iz])
  have hPzsub : Pz (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
        (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)))
      - Pz (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
        (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)))
      = Pz (Jeps ρ ε (fun z θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) z θ
        - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
          (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) z θ)) := by
    rw [Work.FTS.StrongEps.EpsRLX.Pz_sub_eq hL12]
    exact congrArg Pz hJsub
  have hident : (fun z θ => Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ) = Pz (Jeps ρ ε Δ) := by
    have hh : (fun z θ => Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ)
        = Feps α ρ ε Φs E u - Feps α ρ ε Φs E v := rfl
    rw [hh, hFu, hFv]
    rw [hΔdef]
    exact hPzsub
  -- ## the assembly
  have harith : CH * (CH / ε) ^ 12
        * (CP * ((K * (1 + 2 * BS) ^ 2) ^ 2 * (CD * (CD / ε) ^ 12 * S)))
      = (CH * (CH / ε) ^ 12 * Λ) * S := by
    rw [hΛdef]; ring
  rw [hident]
  calc HkSq α 6 (Pz (Jeps ρ ε Δ))
      ≤ CH * (CH / ε) ^ 12
          * (CP * ((K * (1 + 2 * BS) ^ 2) ^ 2 * (CD * (CD / ε) ^ 12 * S))) := hfin1
    _ = (CH * (CH / ε) ^ 12 * Λ) * S := harith
    _ ≤ max 1 (CH * (CH / ε) ^ 12 * Λ) * S := mul_le_mul_of_nonneg_right (le_max_right _ _) hS0

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
