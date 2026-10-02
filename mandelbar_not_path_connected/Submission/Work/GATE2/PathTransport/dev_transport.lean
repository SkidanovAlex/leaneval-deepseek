import Mathlib
import Submission.Work.GATE2.Defs
import Submission.Work.GATE2.deviation_continuousAt
import Submission.Work.GATE2.varphiCrit_F_iterate
import Submission.Work.GATE2.PathTransport.angle_F_iterate
import Submission.Work.GATE2.PathTransport.continuousAt_deviation_fixed
import Submission.Work.GATE2.PathTransport.angle_torsion_const

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PathTransport

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## Auxiliary facts for the path transport of the deviation

Everything below is the "Level A" algebra and topology of
`NOTES_LEAD_mandelbar_gate2transport.md` §3, specialised to the single path `γ`.  The two
imported lemmas actually used are `angle_torsion_const` (item A0) and `continuousAt_deviation_fixed`
(item A2); the `1024`-fold angle equation (item A1) is reproved here as `angle_F_iterate_aux` so
that this file is self-contained. -/

/-- `Tantibar c` is continuous (it is the antiholomorphic polynomial `z ↦ (conj z)^2 + c`). -/
theorem continuous_tantibar_local (c : ℂ) : Continuous (Tantibar c) := by
  rw [show Tantibar c = fun z : ℂ => (starRingEnd ℂ z) ^ 2 + c from rfl]
  continuity

/-- `(1024^j) • (2πα)` is `2πα` in the angle group, because `(1024^j - 1) α ∈ ℤ`. -/
theorem nsmul_two_pi_alpha {α : ℝ} (hα : 1023 * α = 371) (j : ℕ) :
    (1024 ^ j) • ((2 * Real.pi * α : ℝ) : Real.Angle) = ((2 * Real.pi * α : ℝ) : Real.Angle) := by
  obtain ⟨t, ht⟩ := Work.GATE2.PhaseGap.exists_int_pow_sub_one_mul hα j
  rw [← Real.Angle.natCast_mul_eq_nsmul]
  refine (Real.Angle.angle_eq_iff_two_pi_dvd_sub
    (θ := (((1024 ^ j : ℕ) : ℝ)) * (2 * Real.pi * α)) (ψ := 2 * Real.pi * α)).mpr ⟨t, ?_⟩
  have hmain : ((((1024 ^ j : ℕ) : ℝ)) * (2 * Real.pi * α)) - (2 * Real.pi * α)
      = 2 * Real.pi * (t : ℝ) := by
    rw [show ((((1024 ^ j : ℕ) : ℝ)) * (2 * Real.pi * α)) - (2 * Real.pi * α)
        = 2 * Real.pi * (((((1024 ^ j : ℕ) : ℝ)) - 1) * α) by ring, ht]
  exact hmain

/-- Scaling in the angle group: `(1024^j) • (2πx/1024^j) = 2πx`. -/
theorem nsmul_angle_div (x : ℝ) (j : ℕ) :
    (1024 ^ j) • (((2 * Real.pi) * x / (1024 : ℝ) ^ j : ℝ) : Real.Angle)
      = (((2 * Real.pi) * x : ℝ) : Real.Angle) := by
  rw [← Real.Angle.natCast_mul_eq_nsmul]
  congr 1
  rw [Nat.cast_pow, Nat.cast_ofNat]
  exact mul_div_cancel₀ ((2 * Real.pi) * x) (pow_ne_zero j (by norm_num))

/-- **The angle of a value is `2π` times its deviation.**  For any Böttcher-type function `φ`,
`A z := arg (φ z) - 2πα` (an angle) equals `2π · deviation φ α z`, again as an angle.  This is
pure algebra of `liftAngle`; no dynamics and no non-vanishing enters. -/
theorem angle_eq_two_pi_deviation (φ : ℂ → ℂ) (α : ℝ) (z : ℂ) :
    (Complex.arg (φ z) : Real.Angle) - ((2 * Real.pi * α : ℝ) : Real.Angle)
      = (((2 * Real.pi) * Work.GATE.deviation φ α z : ℝ) : Real.Angle) := by
  have hkey : (2 * Real.pi) * Work.GATE.deviation φ α z
      = Complex.arg (φ z) - 2 * Real.pi * α
        + ((⌊α - Work.GATE.bAngle φ z + 1 / 2⌋ : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [Work.GATE.deviation_def, Work.GATE.liftAngle, Work.GATE.bAngle]
    push_cast
    field_simp
    ring
  rw [hkey, Real.Angle.coe_add, Real.Angle.coe_sub, Real.Angle.intCast_mul_eq_zsmul,
    Real.Angle.coe_two_pi, zsmul_zero, add_zero]

/-- **The `1024`-fold angle equation along the high iterate** (item A1).  For `z` in the critical
domain of `c`, the `α`-relative Böttcher angle is multiplied by `1024^j` under `(F_c)^[j]`, for a
root angle `α` with `1023 α = 371`. -/
theorem angle_F_iterate_aux {c z : ℂ} {α : ℝ} (hz : z ∈ Work.ParamRays.critDomain c)
    (hα : 1023 * α = 371) (j : ℕ) :
    (Complex.arg (Work.Bottcher.varphiCrit c ((Work.EL.F c)^[j] z)) : Real.Angle)
        - ((2 * Real.pi * α : ℝ) : Real.Angle)
      = (1024 ^ j) • ((Complex.arg (Work.Bottcher.varphiCrit c z) : Real.Angle)
        - ((2 * Real.pi * α : ℝ) : Real.Angle)) := by
  have hpow : (Work.Bottcher.varphiCrit c z) ^ (1024 ^ j)
      = Work.Bottcher.varphiCrit c ((Work.EL.F c)^[j] z) :=
    Work.GATE2.varphiCrit_F_iterate hz j
  have hang : (Complex.arg (Work.Bottcher.varphiCrit c ((Work.EL.F c)^[j] z)) : Real.Angle)
      = (1024 ^ j) • (Complex.arg (Work.Bottcher.varphiCrit c z) : Real.Angle) := by
    rw [← hpow]
    exact Complex.arg_pow_coe_angle _ _
  rw [hang, nsmul_sub, nsmul_two_pi_alpha hα j]

/-- **Transport of the deviation along a path in the chart.**  Let `γ` be a path in the critical
domain of `e` whose `j`-th image under `F_e` has `α`-deviation `< 1/4` throughout.  Then the
`α`-deviations of the two endpoints differ by the difference of the deviations of their `j`-th
images, divided by `1024^j`, up to an integer:

`d(γ 1) − d(γ 0) = (d(F_e^[j] (γ 1)) − d(F_e^[j] (γ 0)))/1024^j + N`, `N ∈ ℤ`.

This is item (A4) of the design `NOTES_LEAD_mandelbar_gate2transport.md` §3 (the path version of
`Work.GATE2.phase_gap_integrality`, with the integer *computed* as the winding of the continuous
`Real.Angle`-valued function `t ↦ A(γ t) − 2π · dev (F_e^[j] (γ t))/1024^j`, which is torsion by
`angle_F_iterate`). -/
theorem dev_transport {e : ℂ} {α : ℝ} (hα : 1023 * α = 371) (γ : C(unitInterval, ℂ)) (j : ℕ)
    (hdom : ∀ t, γ t ∈ Work.ParamRays.critDomain e)
    (hsmall : ∀ t, |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
      ((Work.EL.F e)^[j] (γ t))| < 1 / 4) :
    ∃ N : ℤ, Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 1) -
        Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 0)
      = (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[j] (γ 1))
          - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[j] (γ 0)))
        / (1024 : ℝ) ^ j + (N : ℝ) := by
  -- The `j`-th iterate of a point of the critical domain lies in the critical domain.
  have hFcrit : ∀ t : unitInterval, (Work.EL.F e)^[j] (γ t) ∈ Work.ParamRays.critDomain e := by
    intro t
    have h1 : (Work.EL.F e)^[j] (γ t) = Work.ParamRays.orbit e (γ t) (10 * j) := by
      rw [Work.EL.F_eq_tantibar, ← Function.iterate_mul]
      rfl
    rw [h1]
    exact Work.ParamRays.orbit_mem_critDomain (hdom t) (10 * j)
  -- `F_e` is continuous.
  have hFlcont : Continuous (Work.EL.F e) := by
    have h : Continuous ((Tantibar e)^[10]) := (continuous_tantibar_local e).iterate 10
    simpa [Work.EL.F_eq_tantibar] using h
  -- The deviation along the image of `γ` is continuous.
  have hDcont : Continuous (fun t : unitInterval =>
      Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[j] (γ t))) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hiter : ContinuousAt (fun s : unitInterval => (Work.EL.F e)^[j] (γ s)) t :=
      ContinuousAt.comp (hFlcont.iterate j).continuousAt γ.continuous.continuousAt
    exact ContinuousAt.comp
      (f := fun s : unitInterval => (Work.EL.F e)^[j] (γ s))
      (continuousAt_deviation_fixed (hFcrit t) (hsmall t)) hiter
  -- The Böttcher angle along `γ` is continuous.
  have hAcont : Continuous (fun t : unitInterval =>
      (Complex.arg (Work.Bottcher.varphiCrit e (γ t)) : Real.Angle)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hφc : ContinuousAt (Work.Bottcher.varphiCrit e) (γ t) :=
      (Work.Bottcher.varphiCrit_continuousOn e).continuousAt
        ((Work.ParamRays.isOpen_critDomain e).mem_nhds (hdom t))
    have hγφ : ContinuousAt (fun s : unitInterval => Work.Bottcher.varphiCrit e (γ s)) t :=
      ContinuousAt.comp hφc γ.continuous.continuousAt
    exact ContinuousAt.comp
      (f := fun s : unitInterval => Work.Bottcher.varphiCrit e (γ s))
      (Complex.continuousAt_arg_coe_angle (Work.Bottcher.varphiCrit_ne_zero (hdom t))) hγφ
  -- The torsion function of the transport.
  let g : unitInterval → Real.Angle := fun t =>
    (Complex.arg (Work.Bottcher.varphiCrit e (γ t)) : Real.Angle)
      - ((2 * Real.pi * α : ℝ) : Real.Angle)
      - (((2 * Real.pi) * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
            ((Work.EL.F e)^[j] (γ t)) / (1024 : ℝ)^j : ℝ) : Real.Angle)
  have hBcont : Continuous (fun t : unitInterval =>
      (((2 * Real.pi) * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
          ((Work.EL.F e)^[j] (γ t)) / (1024 : ℝ)^j : ℝ) : Real.Angle)) :=
    Real.Angle.continuous_coe.comp ((continuous_const.mul hDcont).div_const _)
  have hgcont : Continuous g := by
    dsimp only [g]
    exact Continuous.sub (Continuous.sub hAcont continuous_const) hBcont
  -- Torsion: `1024^j • g t = 0` for all `t`.
  have htors : ∀ t : unitInterval, (1024 ^ j) • g t = 0 := by
    intro t
    have hAiter := angle_F_iterate_aux (c := e) (z := γ t) (α := α) (hdom t) hα j
    have hB := angle_eq_two_pi_deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[j] (γ t))
    have hs := nsmul_angle_div
      (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[j] (γ t))) j
    dsimp only [g]
    rw [nsmul_sub, ← hAiter, hB, hs]
    exact sub_self _
  -- The unit interval is connected and the torsion is discrete, so `g` is constant at its ends.
  have hge : g 0 = g 1 :=
    angle_torsion_const (N := 1024 ^ j) (by positivity) (f := ⟨g, hgcont⟩) (fun t => htors t)
  -- The real quantity whose angle is `g`.
  let q : unitInterval → ℝ := fun t =>
    2 * Real.pi * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ t)
      - (2 * Real.pi) * Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
          ((Work.EL.F e)^[j] (γ t)) / (1024 : ℝ)^j
  have hgq : ∀ t, g t = (q t : Real.Angle) := by
    intro t
    have hA := angle_eq_two_pi_deviation (Work.Bottcher.varphiCrit e) α (γ t)
    dsimp only [g, q]
    rw [hA, Real.Angle.coe_sub]
  have hqq : (q 0 : Real.Angle) = (q 1 : Real.Angle) := by
    rw [← hgq 0, ← hgq 1]
    exact hge
  -- Read off the integer.
  obtain ⟨k, hk⟩ := (Real.Angle.angle_eq_iff_two_pi_dvd_sub (θ := q 0) (ψ := q 1)).mp hqq
  have hP : (1024 : ℝ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
  have h2π : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt Real.two_pi_pos
  -- `hk : q 0 - q 1 = 2π k`; cancel `2π`.
  have hs : Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 0)
        - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 1)
        - (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[j] (γ 0))
            - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[j] (γ 1)))
          / (1024 : ℝ) ^ j = (k : ℝ) := by
    have hq : q 0 - q 1 = 2 * Real.pi *
        (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 0)
         - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α (γ 1)
         - (Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[j] (γ 0))
             - Work.GATE.deviation (Work.Bottcher.varphiCrit e) α ((Work.EL.F e)^[j] (γ 1)))
           / (1024 : ℝ) ^ j) := by
      dsimp only [q]
      ring
    rw [hq] at hk
    exact mul_left_cancel₀ h2π hk
  refine ⟨-k, ?_⟩
  rw [show ((-k : ℤ) : ℝ) = -(k : ℝ) by simp]
  linear_combination (-1 : ℝ) * hs

end Work.GATE2.PathTransport
