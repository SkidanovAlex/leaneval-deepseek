/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.DefsFix` — the corrected implosion bundles

Chain B of the area: the holder structures of `Submission/Work/PARIMPL/` with the **one**
correction of `NOTES_FALSE_match_in.md` / `NOTES_FALSE_match_out.md` — the two Écalle-height
comparisons of MATCH compare the model coordinate's *reflection* with the flower's coordinates —
and with everything else field-for-field as delivered:

* `Work.PARIMPL2.MatchData` — `Work.PARIMPL.MatchData` with `match_in`/`match_out` repointed
  (`-` ↦ `+`, i.e. `approxUin` ↦ `-approxUin` in the comparison);
* `Work.PARIMPL2.TransitData`, `Work.PARIMPL2.LeakData`, `Work.PARIMPL2.ParImplInputs` — the same
  three structures over the corrected `MatchData`, with the same fields and the same proof
  obligations;
* `Work.PARIMPL2.TransitData.blowup` (verbatim), `Work.PARIMPL2.TransitData.height` (the same
  triangle inequality, using `(transU).im = -(approxUin).im` with the corrected sign),
  `Work.PARIMPL2.LeakData.escape_one`.

The corrected bundles are the *satisfiable* ones; the constructions that inhabit them from the
sibling exports are in `Work.PARIMPL2.FixMain`, and the path assembly is in
`Work.PARIMPL2.PathFix` (`Work.PARIMPL2.transit_crossing`, `Work.PARIMPL2.noPath`).
-/
import Submission.Work.PARIMPL2.SignObstruction

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.PARIMPL (ParNormal nEnter critHeight Win Wout transU approxU approxUin entryPt chartZeta
  ecalUin ecalU Ft gtc distZ)

variable {c₀ : ℂ}

/-! ## MATCH (corrected) -/

/-- **MATCH**, with the Écalle-height comparisons of `match_in`/`match_out` **repointed**.

Same field names and types as `Work.PARIMPL.MatchData`, except that the model coordinate is
compared with the flower's coordinate as a *reflection*: `Im approxUin + Im φa` instead of
`Im approxUin - Im φa` (and likewise for the outgoing window and `Ψ`).  See
`NOTES_FALSE_match_in.md` §1–§3: the model's `approxEcal` is a *decreasing* Abel coordinate
(`Work.PARIMPL.approxEcal_step_rot`) while `φa` and `Ψ` are *increasing*, and the (T-e) field's
`Re β = -1/2` is the reflection constant of the flower's `+1/2`. -/
structure MatchData (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (Pa : Set ℂ) (φa Ψ : ℂ → ℂ) where
  nIn : ℕ
  R : ℝ
  hR : 4 ≤ R
  ρin : ℝ
  hρin : 0 < ρin
  le_ρ₀ : P.ρ₀ ≤ ρin
  /-- **(M-in)**, corrected: the incoming window lies in the petal and its Écalle height, as
  measured by the model's incoming coordinate, is the *negative* of the flower's. -/
  match_in : ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρin ∧
    ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Win P R c →
      z ∈ Pa ∧ |(approxUin P c z).im + (φa z).im| ≤ η
  /-- **(M-out)**, corrected. -/
  match_out : ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρin ∧
    ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Wout P R c →
      ∃ u : ℂ, u.re < -1 ∧ Ψ u = z ∧ |(approxU P c z).im + u.im| ≤ η
  /-- **(T-e)**, the symmetric normalization, on the two windows (the corrected form of
  `NOTES_FALSE_te.md`; the delivered `te` asked for a constant `β` on the whole transit strip,
  which is not satisfiable). -/
  te : ∃ β : ℂ, β.re = -(1 / 2) ∧ ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρin ∧
    ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Win P R c → gtc c z ∈ Wout P R c →
      ‖approxU P c (gtc c z) - (starRingEnd ℂ (approxU P c z) + β)‖ ≤ η
  entering : ∀ c ∈ P.Nm ∩ ball c₀ ρin, entryPt P nIn c ∈ Win P R c

namespace MatchData

variable {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
  {Pa : Set ℂ} {φa : ℂ → ℂ} {Ψ : ℂ → ℂ}

/-- The transit coordinate evaluated with `nIn = M.nIn`. -/
theorem transU_eq (M : MatchData d P Pa φa Ψ) (c : ℂ) :
    transU P M.nIn c = -approxUin P c (entryPt P M.nIn c) := rfl

end MatchData

/-! ## TRANS (corrected) -/

/-- **TRANS** over the corrected `MatchData`: continuity of the transit coordinate on
`Nm ∩ ball c₀ ρ₁`, and the uniform lock-step transit `UT`. -/
structure TransitData (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (Pa : Set ℂ) (φa : ℂ → ℂ) (Ψ : ℂ → ℂ) (M : MatchData d P Pa φa Ψ) where
  ρ₁ : ℝ
  hρ₁ : 0 < ρ₁
  le_ρ₀ : ρ₁ ≤ P.ρ₀
  cont : ContinuousOn (fun c => transU P M.nIn c) (P.Nm ∩ ball c₀ ρ₁)
  UT : Work.PARIMPL.TransitLockstep c₀ P.Nm (transU P M.nIn) M.nIn (fun c z => Ft c z) Pa φa Ψ
        ((φa (entryPt P M.nIn c₀)).re - (M.nIn : ℝ))

namespace TransitData

variable {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
  {Pa : Set ℂ} {φa : ℂ → ℂ} {Ψ : ℂ → ℂ} {M : MatchData d P Pa φa Ψ}

/-- **The phase blow-up** — verbatim the delivered `Work.PARIMPL.TransitData.blowup` (it uses
only `entering` and `λ_c → 0`). -/
theorem blowup (T : TransitData d P Pa φa Ψ M) (a : ℂ) (ha : P.a2 a = 0)
    (hab : a ∈ ball c₀ P.ρ₀) :
    Tendsto (fun c => (transU P M.nIn c).re) (𝓝[P.Nm] a) atBot := by
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
  have := Work.PARIMPL.transU_re_le_of_mem_Win P M.nIn hmem
  linarith

/-- **The height of the transit coordinate**, from the corrected (M-in) and `critHeight = 0`.

Compared with the delivered proof, the only change is in the triangle inequality: the corrected
(M-in) bounds `Im approxUin + Im φa`, and `(transU).im = -(approxUin).im`, so
`|Im transU| ≤ |Im approxUin + Im φa| + |Im φa|`. -/
theorem height (T : TransitData d P Pa φa Ψ M) (hPa : IsOpen Pa)
    (hφa : DifferentiableOn ℂ φa Pa) (hentry₀ : entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (entryPt P M.nIn c₀)).im = 0) :
    ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ T.ρ₁ ∧
      ∀ c ∈ P.Nm ∩ ball c₀ ρ, |(transU P M.nIn c).im| ≤ η := by
  intro η hη
  obtain ⟨ρm, hρm, hρmle, hmatch⟩ := M.match_in (η / 2) (by linarith)
  have hcontφ : ContinuousAt (fun c : ℂ => φa (entryPt P M.nIn c)) c₀ :=
    ((hφa.continuousOn.continuousAt (hPa.mem_nhds hentry₀)).comp
      (Work.PARIMPL.continuousAt_entryPt P M.nIn))
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
          have := abs_add_le ((approxUin P c (entryPt P M.nIn c)).im
            + (φa (entryPt P M.nIn c)).im) (-(φa (entryPt P M.nIn c)).im)
          simpa using this
    _ ≤ η / 2 + η / 2 := add_le_add hmm.2 hδc
    _ = η := by ring

end TransitData

/-! ## LEAK (corrected) -/

/-- **LEAK** over the corrected `MatchData`/`TransitData`: the robust leak disc at GATE2's
ρ-maximising centre. -/
structure LeakData (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (Pa : Set ℂ) (φa : ℂ → ℂ) (Ψ : ℂ → ℂ)
    (M : MatchData d P Pa φa Ψ) (T : TransitData d P Pa φa Ψ M) where
  xstar : ℝ
  j₀ : ℤ
  r₀ : ℝ
  hr₀ : 0 < r₀
  leak : Ψ ((xstar : ℝ) : ℂ) ∉ Work.EL.K c₀
  deep : ∀ y ∈ closedBall (((xstar - (j₀ : ℝ)) : ℝ) : ℂ) r₀,
    0 < Work.Bottcher.green c₀ (Ψ y)
  robust : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ ball c₀ ρ, ∀ y : ℂ,
    (∃ z ∈ closedBall (((xstar - (j₀ : ℝ)) : ℝ) : ℂ) r₀, dist y (Ψ z) ≤ ρ) →
      y ∉ Work.EL.K c
  escape : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ y : ℝ,
    (y = xstar - (j₀ : ℝ) ∨ y = xstar - (j₀ : ℝ) + 1 / 2) →
    distZ (transU P M.nIn c) ((y : ℝ) : ℂ) < r₀ / 2 → c ∉ Mandelbar

namespace LeakData

variable {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
  {Pa : Set ℂ} {φa : ℂ → ℂ} {Ψ : ℂ → ℂ}
  {M : MatchData d P Pa φa Ψ} {T : TransitData d P Pa φa Ψ M}

/-- The leak centre, as a real number. -/
def liftRe (L : LeakData d P Pa φa Ψ M T) : ℝ := L.xstar - (L.j₀ : ℝ)

theorem liftRe_def (L : LeakData d P Pa φa Ψ M T) :
    L.liftRe = L.xstar - (L.j₀ : ℝ) := rfl

/-- The centre of the leak disc: `xstar − j₀`, i.e. GATE2's `xLeak`. -/
def yLeak (L : LeakData d P Pa φa Ψ M T) : ℝ := L.xstar - (L.j₀ : ℝ)

theorem yLeak_eq_liftRe (L : LeakData d P Pa φa Ψ M T) : L.yLeak = L.liftRe := rfl

/-- The leak centre is real — so the `ι`-tongue `yLeak + 1/2` is `conj yLeak + 1/2` and
`ParabolicFlower.Psi_anti` applies to it. -/
theorem yLeak_im (L : LeakData d P Pa φa Ψ M T) : (((L.yLeak : ℝ) : ℂ)).im = 0 := by
  simp

/-- The one-sided form of `escape` (the `b`-tongue). -/
theorem escape_one (L : LeakData d P Pa φa Ψ M T) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ P.Nm ∩ ball c₀ ρ,
      distZ (transU P M.nIn c) ((L.liftRe : ℝ) : ℂ) < L.r₀ / 2 → c ∉ Mandelbar := by
  obtain ⟨ρ, hρ, h⟩ := L.escape
  refine ⟨ρ, hρ, fun c hc hZ => h c hc L.liftRe (Or.inl rfl) hZ⟩

end LeakData

/-! ## The holder structure (corrected) -/

/-- **The residuals of the implosion side**, over the corrected `MatchData`: same fields and types
as `Work.PARIMPL.ParImplInputs`, with `M`/`T`/`L` the corrected bundles. -/
structure ParImplInputs where
  c₀ : ℂ
  d : Work.EL.RootParabolic c₀
  P : ParNormal d
  Pa : Set ℂ
  φa : ℂ → ℂ
  Ψ : ℂ → ℂ
  M : MatchData d P Pa φa Ψ
  T : TransitData d P Pa φa Ψ M
  L : LeakData d P Pa φa Ψ M T
  c_mem_closure : c₀ ∈ closure P.Nm
  fix : Work.PARIMPL.FlowerFix d (Ft c₀) (gtc c₀) d.z₁ Pa φa
  zdecay : Work.PARIMPL.ZDecay d Ψ
  greenOpen : Work.PARIMPL.GreenEscapeOpen
  isOpen_Pa : IsOpen Pa
  diff_φa : DifferentiableOn ℂ φa Pa
  entry_mem : entryPt P M.nIn c₀ ∈ Pa
  critHeight_zero : (φa (entryPt P M.nIn c₀)).im = 0

namespace ParImplInputs

variable (H : ParImplInputs)

/-- The implosion side `Nm`, as the set of the parameter normal form. -/
def Nm : Set ℂ := H.P.Nm

/-- The implosion side is open. -/
theorem isOpen_Nm : IsOpen H.Nm := H.P.isOpen_Nm

/-- The root parameter does not lie on the implosion side. -/
theorem notMem_Nm : H.c₀ ∉ H.Nm := by
  intro h
  have h2 : H.P.a2 H.c₀ < 0 := h.2
  rw [H.P.a2₀] at h2
  exact absurd h2 (lt_irrefl 0)

/-- The root parameter lies on the frontier of the implosion side. -/
theorem mem_frontier_Nm : H.c₀ ∈ frontier H.Nm := by
  rw [frontier_eq_closure_inter_closure]
  refine ⟨H.c_mem_closure, ?_⟩
  change H.c₀ ∈ closure (H.P.Nm)ᶜ
  rw [H.P.isOpen_Nm.isClosed_compl.closure_eq]
  exact H.notMem_Nm

/-- **The implosion side data**: open, accumulating at `c₀`, period-`5` point gone. -/
theorem impl : Work.PARIMPL.ImplSide H.c₀ H.d.z₁ H.Nm :=
  H.P.toImplSide H.c_mem_closure (Work.PARIMPL.periodFiveGone H.d H.P)

end ParImplInputs

end Work.PARIMPL2

end
