/-
Copyright: subproject `Submission/Work/PARIMPL/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.Transit` — TRANS: the transit coordinate and its phase blow-up

Item §1.3 of `Submission/Work/NOTES_LEAD_mandelbar_residuals.md`.  The **transit coordinate**
`transU P n c = −Ũ_c(u_c((F c)^[n] c))` is the (lifted) approximate coordinate of the critical
value at the entry time `n` into the transit strip.  Its **class modulo `ℤ`** is the point at
which the critical orbit leaves the transit, and its **real part** is the transit phase
`−(π/λ_c − O(1))`, which blows up as `c` approaches the parabolic locus along the implosion side.

Compared with the residual note the sign is *lifted*: the note writes `Ũ_c(entry) − π/λ_c`, whose
real part is bounded (it is the *predicted* exit position, not the phase).  The phase blow-up
claimed there — and used by the path argument of §1.5 — requires the lifted coordinate
`−Ũ_c(entry)`; the two differ by the (non-integer) real shift `π/λ_c` and by the integer number
of transit steps, and the exit matching below is stated modulo `ℤ`, exactly the ambiguity of
that number of steps.

## Main results

* `Work.PARIMPL.TransitData` — the holder structure: the radius `ρ₁`, the **continuity** of the
  transit coordinate on `Nm ∩ ball c₀ ρ₁`, and the **exit matching** of §1.4;
* `Work.PARIMPL.TransitData.blowup` — the **phase blow-up** `Re (transU) → −∞` at the parabolic
  locus, *derived* from the entry into the incoming window (no extra hypothesis);
* `Work.PARIMPL.TransitData.height` — the **height** of the transit coordinate is as small as we
  like near `c₀`, *derived* from (M-in) of `Work.PARIMPL.MatchData` and `critHeight = 0`.
-/
import Submission.Work.PARIMPL.Match

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c₀ : ℂ}

/-! ## Joint continuity of the entry point -/

/-- The polynomial `Tsq` is jointly continuous in `(c, z)`. -/
theorem continuous_tsq_pair :
    Continuous (fun p : ℂ × ℂ => Work.Landing.Tsq p.1 p.2) := by
  simp only [Work.Landing.Tsq]
  fun_prop

/-- Joint continuity of the iterates of the family `c ↦ Work.Landing.Tsq c` in the parameter. -/
theorem continuous_tsqIter : ∀ m : ℕ,
    Continuous (fun p : ℂ × ℂ => ((Work.Landing.Tsq p.1)^[m]) p.2) := by
  intro m
  induction m with
  | zero => simpa using continuous_snd
  | succ k ih =>
    have hpair : Continuous (fun p : ℂ × ℂ => (p.1, Work.Landing.Tsq p.1 p.2)) :=
      continuous_fst.prodMk continuous_tsq_pair
    have := ih.comp hpair
    simpa only [Function.comp_def, Function.iterate_succ_apply] using this

/-- Joint continuity of `(c, z) ↦ Ft c z`. -/
theorem continuous_ft_pair : Continuous (fun p : ℂ × ℂ => Ft p.1 p.2) := by
  have h := continuous_tsqIter 5
  simpa [Ft, Work.EL.F] using h

/-- Joint continuity of the critical-orbit map `(c, n) ↦ (Ft c)^[n] c` in the parameter. -/
theorem continuous_orbit_pair : ∀ n : ℕ,
    Continuous (fun p : ℂ × ℂ => ((Ft p.1)^[n]) p.2) := by
  intro n
  induction n with
  | zero => simpa using continuous_snd
  | succ k ih =>
    have hpair : Continuous (fun p : ℂ × ℂ => (p.1, Ft p.1 p.2)) :=
      continuous_fst.prodMk continuous_ft_pair
    have := ih.comp hpair
    simpa only [Function.comp_def, Function.iterate_succ_apply] using this

/-- The critical orbit `c ↦ (Ft c)^[n] c` is continuous on the diagonal. -/
theorem continuous_orbit_diag (n : ℕ) : Continuous (fun c : ℂ => ((Ft c)^[n]) c) := by
  have hd : Continuous (fun c : ℂ => (c, c)) := continuous_id.prodMk continuous_id
  have hcomp := (continuous_orbit_pair n).comp hd
  simpa only [Function.comp_def] using hcomp

/-- The entry point `c ↦ (Ft c)^[n] c` is continuous on the normal-form ball. -/
theorem continuousOn_entryPt {d : Work.EL.RootParabolic c₀} (P : ParNormal d) (n : ℕ) :
    ContinuousOn (fun c : ℂ => entryPt P n c) (ball c₀ P.ρ₀) :=
  (continuous_orbit_diag n).continuousOn

/-- The critical-orbit point at the entry time is continuous as a function of the parameter. -/
theorem continuousAt_entryPt {d : Work.EL.RootParabolic c₀} (P : ParNormal d) (n : ℕ) :
    ContinuousAt (fun c : ℂ => entryPt P n c) c₀ :=
  (continuousOn_entryPt P n).continuousAt (isOpen_ball.mem_nhds (by simpa using P.hρ₀))

/-! ## The transit coordinate -/

/-- **Uniform lock-step transit** (the note `NOTES_LEAD_mandelbar_gate2transport.md` §5, quoted
verbatim): for every bounded box `X₁ ≤ Re φa ≤ X₁ + W`, `|Im φa| ≤ H` of the attracting
coordinate and every bounded exit window `−Xo ≤ Re u < −1`, the `n`-th iterate of any point `y'`
within `ρ` of a box point `y` sits within `η` of `Ψ (trans c − nIn + n + φa y)`, uniformly in the
parameter `c ∈ Nm ∩ ball c₀ ρ` and in `n`. -/
def TransitLockstep (c₀ : ℂ) (Nm : Set ℂ) (trans : ℂ → ℂ) (nIn : ℕ) (Ft : ℂ → ℂ → ℂ)
    (Pa : Set ℂ) (φa Ψ : ℂ → ℂ) (v : ℝ) : Prop :=
  ∀ H W Xo η : ℝ, 0 < η → ∃ X₁ ρ : ℝ, 0 < ρ ∧
    ∀ c ∈ Nm ∩ Metric.ball c₀ ρ, ∀ y y' : ℂ, ∀ n : ℕ,
      y ∈ Pa → X₁ ≤ (φa y).re → (φa y).re ≤ X₁ + W → |(φa y).im| ≤ H → ‖y' - y‖ ≤ ρ →
      let u := trans c - nIn - v + n + φa y
      (-Xo) ≤ u.re → u.re < -1 →
        ‖(Ft c)^[n] y' - Ψ u‖ ≤ η

/-- **The bounded-window exit** (`ExitTrackedLoc` of the note §2/§5): the exit of the transit is
restricted to a bounded window.  It is the form `GATE2` consumes, and it is *implied* by
`Work.PARIMPL.TransitLockstep` (for the critical orbit, at the chain point `c_N` of the `c₀`-orbit
and with the integer alignment `Re φa (c_N) = v + N`).

**Defect and repair** (`Submission/Work/PARIMPL2/NOTES_FALSE_ExitTrackedLoc.md`).  As first
stated the half-width `Xo` of the window was *existential* with only `0 < ρ` required, so
`Xo = 1/2` emptied the window `[-Xo, -1)` and the statement was **vacuous** (it held for
arbitrary `trans`, `Ft`, `Ψ` with no hypotheses).  Three corrections, matching the note's §2 form
and GATE2's own `Work.GATE2.ExitTrackedLoc` (`Submission/Work/GATE2/Defs.lean`), which is the
definition the GATE2 escape family actually consumes:

* the window width `X` is quantified **universally** (`1 < X`), so the window is nonempty;
* the tracked quantity is the **integer level** `trans c + k` of the repelling coordinate, not an
  arbitrary `u` of the window (the orbit visits the levels `trans c + k`, spaced by `1`, so
  `Ψ u` for `u` strictly between two levels is in general not near any orbit point);
* the conclusion is the **approximate** form `‖(Ft c)^[n] c - Ψ (trans c + k)‖ ≤ η`, which is what
  `Work.PARIMPL.TransitLockstep` delivers directly and what the escape consumes (the escaping
  region is open).  The design's exact-preimage form follows given the local inverse of `Ψ` on
  `Re < -1`.

`Submission/Work/PARIMPL2/ExitTracking.lean` proves this form from `Work.PARIMPL2.LockstepAll`
(the design's form of the lock-step transit, with the box origin universal). -/
def ExitTrackedLoc (c₀ : ℂ) (Nm : Set ℂ) (trans : ℂ → ℂ) (Ft : ℂ → ℂ → ℂ) (Ψ : ℂ → ℂ) : Prop :=
  ∀ X η : ℝ, 1 < X → 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Nm ∩ Metric.ball c₀ ρ, ∀ k : ℤ,
    -X ≤ (trans c + (k : ℂ)).re → (trans c + (k : ℂ)).re < -1 →
      ∃ n : ℕ, ‖(Ft c)^[n] c - Ψ (trans c + (k : ℂ))‖ ≤ η

/-- **TRANS** — the transit coordinate of §1.3: its continuity on `Nm ∩ ball c₀ ρ₁`, and the
**exit matching** of §1.4 (the class modulo `ℤ` of the transit coordinate is the position at
which the critical orbit leaves the transit).

The exit matching is the conclusion of §1.3's `trans_exit`: the transit error
(`Work.PARIMPL.approxEcal_transit_rot`, uniform in the number of steps) together with (M-out) of
`Work.PARIMPL.MatchData` says that for a suitable *time* `n` on the critical orbit the repelling
coordinate `u` of the orbit point differs from the transit coordinate only by an **integer**
(number of transit steps) and the small transit error `η`. -/
structure TransitData {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (Pa : Set ℂ) (φa : ℂ → ℂ) (Ψ : ℂ → ℂ)
    (M : MatchData d P Pa φa Ψ) where
  /-- the radius on which the transit coordinate is continuous. -/
  ρ₁ : ℝ
  hρ₁ : 0 < ρ₁
  le_ρ₀ : ρ₁ ≤ P.ρ₀
  /-- the transit coordinate is continuous on `Nm ∩ ball c₀ ρ₁`. -/
  cont : ContinuousOn (fun c => transU P M.nIn c) (P.Nm ∩ ball c₀ ρ₁)
  /-- **UT — uniform lock-step transit** (§5 of `NOTES_LEAD_mandelbar_gate2transport.md`),
  verbatim: the transit of **every** point of a bounded box of the attracting coordinate (not
  only of the critical orbit), in lock-step with the repelling coordinate `Ψ`.

  This is the correct uniform form of the exit matching of §1.3/§1.4 (the earlier, stronger
  `Work.GATE2.ExitTracked` is *false*: for an escaping tongue parameter the escaping critical
  orbit returns near `z₁` infinitely often, so no unbounded tracking is available).  It implies
  the bounded-window exit statement `Work.PARIMPL.TransitLockstep.exitLoc`, the form the two-sided
  argument `GATE2` consumes. -/
  UT : TransitLockstep c₀ P.Nm (transU P M.nIn) M.nIn (fun c z => Ft c z) Pa φa Ψ
        ((φa (entryPt P M.nIn c₀)).re - (M.nIn : ℝ))
namespace TransitData

variable {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
  {Pa : Set ℂ} {φa : ℂ → ℂ} {Ψ : ℂ → ℂ}
  {M : MatchData d P Pa φa Ψ}

/-- **The phase blow-up** (HS §4, Prop. 4.6 and its remark): along the implosion side, the real
part of the transit coordinate tends to `−∞` as the parameter approaches the parabolic locus.
It is *derived* from the entry of the critical orbit into the incoming window
(`MatchData.entering`), whose real part is `π/λ_c − O(1)`, together with `λ_c → 0`
(`ParNormal.tendsto_lam`). -/
theorem blowup (T : TransitData d P Pa φa Ψ M) (a : ℂ) (ha : P.a2 a = 0)
    (hab : a ∈ ball c₀ P.ρ₀) :
    Tendsto (fun c => (transU P M.nIn c).re) (𝓝[P.Nm] a) atBot := by
  -- `π/λ → ∞` along the implosion side
  have hgt : Tendsto P.lam (𝓝[P.Nm] a) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨P.tendsto_lam a ha hab, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with c hc using P.lam_pos c hc.1 hc.2
  have hinv : Tendsto (fun c => (P.lam c)⁻¹) (𝓝[P.Nm] a) atTop :=
    hgt.inv_tendsto_nhdsGT_zero
  have htop : Tendsto (fun c => Real.pi / P.lam c) (𝓝[P.Nm] a) atTop := by
    have := Filter.Tendsto.const_mul_atTop Real.pi_pos hinv
    simpa [div_eq_mul_inv] using this
  rw [tendsto_atBot]
  intro b
  have hb : ∀ᶠ c in 𝓝[P.Nm] a, 2 * M.R - b ≤ Real.pi / P.lam c :=
    (tendsto_atTop.mp htop (2 * M.R - b))
  have hball : ∀ᶠ c in 𝓝[P.Nm] a, c ∈ ball c₀ M.ρin := by
    have hab' : a ∈ ball c₀ M.ρin := by
      rw [mem_ball] at hab ⊢
      exact lt_of_lt_of_le hab M.le_ρ₀
    exact (nhdsWithin_le_nhds (s := P.Nm) (a := a)) (Metric.isOpen_ball.mem_nhds hab')
  filter_upwards [hb, hball, self_mem_nhdsWithin] with c hbc hcb hc
  have hmem : entryPt P M.nIn c ∈ Win P M.R c := M.entering c ⟨hc, hcb⟩
  have := transU_re_le_of_mem_Win P M.nIn hmem
  linarith

/-- **The height of the transit coordinate** is as small as we like near `c₀`, *derived* from
(M-in) of `Work.PARIMPL.MatchData` (the entry point is in the incoming window, and there the
height of `Ũ` is the height of the flower's Fatou coordinate) together with the vanishing of the
critical Écalle height and the continuity of `φa` at the entry point.

For the intended instantiation, `hentry₀` is `nEnter_spec` (`(Ft c₀)^[nEnter d fl] c₀ ∈ fl.Pa`)
and `hcrit` is `critHeight = 0` (`critHeight_eq_zero_iff_mem_equator`). -/
theorem height (T : TransitData d P Pa φa Ψ M) (hPa : IsOpen Pa)
    (hφa : DifferentiableOn ℂ φa Pa) (hentry₀ : entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (entryPt P M.nIn c₀)).im = 0) :
    ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ T.ρ₁ ∧
      ∀ c ∈ P.Nm ∩ ball c₀ ρ, |(transU P M.nIn c).im| ≤ η := by
  intro η hη
  obtain ⟨ρm, hρm, hρmle, hmatch⟩ := M.match_in (η / 2) (by linarith)
  -- continuity of `φa` along the entry point at `c₀`
  have hcontφ : ContinuousAt (fun c : ℂ => φa (entryPt P M.nIn c)) c₀ :=
    ((hφa.continuousOn.continuousAt (hPa.mem_nhds hentry₀)).comp
      (continuousAt_entryPt P M.nIn))
  have hnear : ∀ᶠ c in 𝓝 c₀,
      |(φa (entryPt P M.nIn c)).im - (φa (entryPt P M.nIn c₀)).im| ≤ η / 2 := by
    have hev := Metric.tendsto_nhds.mp hcontφ.tendsto (η / 2) (by linarith)
    filter_upwards [hev] with c hc
    refine le_of_lt (lt_of_le_of_lt ?_ hc)
    simpa [Complex.dist_eq, Complex.sub_im] using
      Complex.abs_im_le_norm (φa (entryPt P M.nIn c) - φa (entryPt P M.nIn c₀))
  obtain ⟨δ, hδ, hδ'⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℂ, dist y c₀ < δ →
      |(φa (entryPt P M.nIn y)).im - (φa (entryPt P M.nIn c₀)).im| ≤ η / 2 :=
    Metric.eventually_nhds_iff.mp hnear
  refine ⟨min (min ρm T.ρ₁) δ, lt_min (lt_min hρm T.hρ₁) hδ,
    (min_le_left _ _).trans (min_le_right _ _), ?_⟩
  intro c hc
  obtain ⟨hcNm, hcball⟩ := hc
  have hlt : dist c c₀ < min (min ρm T.ρ₁) δ := by simpa [mem_ball] using hcball
  have hcρm : dist c c₀ < ρm := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_left _ _))
  have hcρin : dist c c₀ < M.ρin := lt_of_lt_of_le hcρm hρmle
  have hz : entryPt P M.nIn c ∈ Win P M.R c :=
    M.entering c ⟨hcNm, by simpa [mem_ball] using hcρin⟩
  have hmm := hmatch c ⟨hcNm, by simpa [mem_ball] using hcρm⟩ (entryPt P M.nIn c) hz
  have hδc : |(φa (entryPt P M.nIn c)).im| ≤ η / 2 := by
    have hδlt : dist c c₀ < δ := lt_of_lt_of_le hlt (min_le_right _ _)
    have h := hδ' c hδlt
    rw [hcrit, sub_zero] at h
    exact h
  have htrans : (transU P M.nIn c).im = -((approxUin P c (entryPt P M.nIn c)).im) := by
    simp only [transU, Complex.neg_im]
  rw [htrans, abs_neg]
  calc |(approxUin P c (entryPt P M.nIn c)).im|
      = |((approxUin P c (entryPt P M.nIn c)).im + (φa (entryPt P M.nIn c)).im)
          - (φa (entryPt P M.nIn c)).im| := by ring_nf
    _ ≤ |(approxUin P c (entryPt P M.nIn c)).im + (φa (entryPt P M.nIn c)).im|
          + |(φa (entryPt P M.nIn c)).im| := by
          have h := abs_add_le ((approxUin P c (entryPt P M.nIn c)).im
            + (φa (entryPt P M.nIn c)).im) (-(φa (entryPt P M.nIn c)).im)
          simpa using h
    _ ≤ η / 2 + η / 2 := add_le_add hmm.2 hδc
    _ = η := by ring

end TransitData

end Work.PARIMPL
