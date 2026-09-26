import Mathlib
import Submission.Work.Drive.sweepToNeedleBoundedHalfHavoid
import Submission.Work.Drive.sweepFam_wideEnd_estimate_tol

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant in
/-- **The top end of the chord sweep with a *prescribed* needle parameter, from the slices clause.**

This is *verbatim* the conclusion of `Work.Drive.sweepToNeedleEps`
(`Submission/Work/Drive/sweepToNeedleEps.lean`, axiom-clean), with its three *non-tangency*
hypotheses (`hV`, `hntB`, `hntA`) removed and the slices clause of the `O`-avoiding band arc supplied
instead as the explicit hypothesis `hsl`.

**How to prove it (a transcription, not new mathematics).**  `Work.Drive.sweepToNeedleEps`'s proof is
self-contained from its local `hsel : ∀ ε₁ > 0, ∃ (lam δ₁ δ₂ σ₀ c : ℝ) (Θ : ℝ → ℝ), (boxes) ∧
Θ-clauses ∧ (the slices clause on `[ε, σ₀]`)`: everything after its `obtain ⟨ε_uc, hε_uc_pos, h_uc⟩ :=
uniformCorrection_clauses …` (its line 165) is *independent* of how `hsel` is built (its `hV/hntB/hntA`
and `hbox/hwrap` occur only inside the construction of its own `hsel`, at its lines 76–125).  So copy
its proof from there to its end verbatim (the shifted knot `K`, the wide-end slice `G`, the correction
`w`, the three phases `A`, `B`, `Cc` and their gluing by `Work.Drive.sweepGlue_clauses`), and replace
only its `hsel` by the version whose *boxes and Θ-closeness* come from
`Work.Drive.sweepFam_wideEnd_estimate_tol` alone (the widths are chosen by that estimate, hence free)
and whose *slices clause* is the hypothesis `hsl`: with `σ₀` from the estimate's `htoldots ε₁ hε₁`
(so `1/2 < σ₀ < 1`, whence `ε < σ₀` since `ε < 1/2`), and the width budget
`Lc := min (min L Δ) (min (ε / 4) (1 / 4))` (where `L` is `hsl`'s threshold on `[ε, σ₀]`), one has
`lam ≤ Lc ≤ 1/4 < 1/2`, `δ₁ ≤ Lc ≤ Δ`, `δ₂ ≤ Lc ≤ Δ` and `δ₂ ≤ Lc ≤ ε/4 ≤ ε/2`, and `hsl ε σ₀ hε
(lt_trans hε1 hσ₀half) hσ₀lt` supplies the slices clause at those widths.

The point of the ε-first shape is that the clean needle end on the project's critical path
(`Submission/Work/Generic/of_needleEndEps.lean`, pinned on H481's `nclm_chartData`) has exactly this
quantifier order — `∃ ε₁, ∀ ε ≤ ε₁, ∃ Λ, ∀ lam δ₁ δ₂ ≤ Λ, …` — so the target's reduction consumes the
widths *after* the needle parameter.  (The alternative shape of
`Work.Drive.sweepToNeedleBoundedHalf_of_slices`, which bounds the widths *before* `ε`, is strictly
stronger and is what the still-`sorry`-tainted twisted pin
`Work.Drive.needleEnd_of_twistedPin` provides.)

Note: `havoid` is retained (harmless, and it is the source from which the caller proves `hsl`); the
import order of the file must avoid the duplicated `Work.Drive.avgChord` (in `velNzDefs.lean` and
`avgArcDefs.lean`) — this proof needs neither. NOTE (added by the requesting lane, 08:2x): the import of
`Submission.Work.Drive.sweepToNeedleEps` (the *template* of the transcription) was removed: it is not
used by the proof below (verified: the file compiles unchanged without it) and it drags in the NT
machinery, whose module `Submission.Work.Drive.sfcSideFree` declares `Work.Drive.SmoothTModulus`,
clashing with the copy in `sweepFam_close_chamfer.lean` — which the consumer
`Submission/Work/Drive/unknotted_of_avoidingArc.lean` has in its closure.  Without the import the
module is importable together with the target file.
-/
theorem sweepToNeedleEpsOfSlices {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r)
    (hsl : ∀ ε σ₀ : ℝ, 0 < ε → ε < σ₀ → σ₀ < 1 →
      ∃ L : ℝ, 0 < L ∧
        ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ L → 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L →
          ∀ σ : ℝ, ε ≤ σ → σ ≤ σ₀ →
            Set.InjOn (fun t : ℝ => sweepFam r D lam δ₁ δ₂ σ t) (Set.Ico 0 period) ∧
            (∀ t : ℝ, velocity (fun t : ℝ => sweepFam r D lam δ₁ δ₂ σ t) t ≠ 0))
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    ∀ Δ : ℝ, 0 < Δ →
      ∃ (lam δ₁ δ₂ : ℝ) (r0 : ℝ → Space) (H : ℝ → ℝ → Space),
        (0 < lam ∧ lam < 1 / 2 ∧ 0 < δ₁ ∧ 0 < δ₂ ∧ δ₂ ≤ ε / 2 ∧
          lam ≤ Δ ∧ δ₁ ≤ Δ ∧ δ₂ ≤ Δ) ∧
        IsSmoothKnot r0 ∧
        (∀ t : ℝ, ‖r0 t - r t‖ < δ ∧ ‖velocity r0 t - velocity r t‖ < δ) ∧
        ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2) ∧
        (∀ s t : ℝ, H (t + period) s = H t s) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => H t s)) ∧
        (∀ t : ℝ, H t 0 = r0 t) ∧
        (∀ t : ℝ, H t 1 = sweepNeedleFam r D lam δ₁ δ₂ ε t) := by
  have hsm := fun (lam δ₁ δ₂ : ℝ) (h₁ : δ₁ ≠ 0) (h₂ : δ₂ ≠ 0) =>
    Work.Drive.sweepFam_contDiff_periodic hr.continuous D lam δ₁ δ₂ h₁ h₂
  intro Δ hΔ
  -- ## The parameters of the sweep, selected with the *prescribed* needle parameter `ε`.
  --
  -- The *boxes* and the `Θ`-closeness come from `Work.Drive.sweepFam_wideEnd_estimate_tol` alone
  -- (the widths are free witnesses there), and the *slices clause* on the window `[ε, σ₀]` is the
  -- hypothesis `hsl`.
  have hsel : ∀ ε₁ : ℝ, 0 < ε₁ →
      ∃ (lam δ₁ δ₂ σ₀ c : ℝ) (Θ : ℝ → ℝ),
        (0 < lam ∧ lam < 1 / 2 ∧ 0 < δ₁ ∧ 0 < δ₂ ∧ ε < σ₀ ∧ σ₀ < 1 ∧
          lam ≤ Δ ∧ δ₁ ≤ Δ ∧ δ₂ ≤ Δ ∧ δ₂ ≤ ε / 2) ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
        (∀ t : ℝ, Θ (t + LeanEval.KnotTheory.Quadrisecant.period)
          = Θ t + LeanEval.KnotTheory.Quadrisecant.period) ∧
        (∀ t : ℝ, 0 < deriv Θ t) ∧
        (∀ t : ℝ, ‖Work.Drive.sweepFam r D lam δ₁ δ₂ σ₀ (Θ t) - r (t + c)‖ < ε₁) ∧
        (∀ t : ℝ, ‖deriv (fun u : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ₀ (Θ u)) t
          - LeanEval.KnotTheory.Quadrisecant.velocity r (t + c)‖ < ε₁) ∧
        (∀ σ ∈ Set.Icc ε σ₀,
          Set.InjOn (fun t : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ t)
            (Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period) ∧
          (∀ t : ℝ, LeanEval.KnotTheory.Quadrisecant.velocity
            (fun t : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ t) t ≠ 0)) := by
    intro ε₁ hε₁
    obtain ⟨tol, _htolpos, htoldots, htolmain⟩ := Work.Drive.sweepFam_wideEnd_estimate_tol hr D
    -- the wide-end sweep parameter, in `(1/2, 1)`, chosen so that `tol σ₀ < ε₁`
    obtain ⟨σ₀, _hσ₀half, hσ₀lt, hσ₀tol⟩ := htoldots ε₁ hε₁
    have hσ₀pos : (0 : ℝ) < σ₀ := by linarith
    have hεσ₀ : ε < σ₀ := by linarith
    -- the slices clause on the window `[ε, σ₀]`, and its width threshold `L`
    obtain ⟨L, hLpos, hL⟩ := hsl ε σ₀ hε hεσ₀ hσ₀lt
    -- the width budget: small enough for the slices clause, for the caller's `Δ`,
    -- and below the boxes' structural thresholds (`ε/4` gives `δ₂ ≤ ε/2`)
    set Lc : ℝ := min (min L Δ) (min (ε / 4) (1 / 4)) with hLcdef
    have hLcpos : 0 < Lc := by
      rw [hLcdef]
      exact lt_min (lt_min hLpos hΔ) (lt_min (by linarith) (by norm_num))
    obtain ⟨lam, δ₁, δ₂, c, Θ, hlam0, hlamL, hδ₁0, hδ₁L, hδ₂0, hδ₂L, hΘsm, hΘshift,
      hΘderiv, hΘ1, hΘ2⟩ := htolmain σ₀ hσ₀lt ε₁ hσ₀tol Lc hLcpos
    have hlam_half : lam < 1 / 2 := by
      have h1 : lam ≤ 1 / 4 := (hlamL.trans (min_le_right _ _)).trans (min_le_right _ _)
      linarith
    have hlam_le : lam ≤ L := ((hlamL.trans (min_le_left _ _)).trans (min_le_left _ _))
    have hδ₁_le : δ₁ ≤ L := ((hδ₁L.trans (min_le_left _ _)).trans (min_le_left _ _))
    have hδ₂_le : δ₂ ≤ L := ((hδ₂L.trans (min_le_left _ _)).trans (min_le_left _ _))
    have hlam_Δ : lam ≤ Δ := (hlamL.trans (min_le_left _ _)).trans (min_le_right _ _)
    have hδ₁_Δ : δ₁ ≤ Δ := (hδ₁L.trans (min_le_left _ _)).trans (min_le_right _ _)
    have hδ₂_Δ : δ₂ ≤ Δ := (hδ₂L.trans (min_le_left _ _)).trans (min_le_right _ _)
    have hδ₂_eps : δ₂ ≤ ε / 2 := by
      have h1 : δ₂ ≤ ε / 4 := (hδ₂L.trans (min_le_right _ _)).trans (min_le_left _ _)
      linarith
    exact ⟨lam, δ₁, δ₂, σ₀, c, Θ,
      ⟨hlam0, hlam_half, hδ₁0, hδ₂0, hεσ₀, hσ₀lt, hlam_Δ, hδ₁_Δ, hδ₂_Δ, hδ₂_eps⟩,
      hΘsm, hΘshift, hΘderiv, hΘ1, hΘ2, fun σ hσ =>
        hL lam δ₁ δ₂ hlam0 hlam_le hδ₁0 hδ₁_le hδ₂0 hδ₂_le σ hσ.1 hσ.2⟩
  -- ## (a) a uniform small-correction threshold, valid for every rotation of `r`
  have hle : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have hle0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hrotjoint : ContDiff ℝ 1 (fun p : ℝ × ℝ => r (p.1 + p.2 * period)) := by
    have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 + p.2 * period) := by fun_prop
    exact (hr.smooth.of_le le_top).of_le hle |>.comp h1
  have hrotper : ∀ s t : ℝ, r ((t + period) + s * period) = r (t + s * period) := by
    intro s t
    have h : t + period + s * period = (t + s * period) + period := by ring
    rw [h, hr.periodic]
  have hrotsl : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => r (t + s * period)) := by
    intro s hs
    simpa using isCInfKnot_shift (IsSmoothKnot.toCInf hr) (s * period)
  obtain ⟨ε_uc, hε_uc_pos, h_uc⟩ := uniformCorrection_clauses hrotjoint hrotper hrotsl
  -- ## (b) the sweep data at tolerance `ε_uc`
  obtain ⟨lam, δ₁, δ₂, σ₀, c, Θ, hb, hΘsm, hΘshift, hΘderiv, he1, he2, hσcl⟩ :=
    hsel ε_uc hε_uc_pos
  obtain ⟨hlam0, hlam1, hδ₁0, hδ₂0, hεσ₀, hσ₀1, hlamΔ, hδ₁Δ, hδ₂Δ, hδ₂ε2⟩ := hb
  have hδ₁ne : δ₁ ≠ 0 := ne_of_gt hδ₁0
  have hδ₂ne : δ₂ ≠ 0 := ne_of_gt hδ₂0
  have hsmjoint : ContDiff ℝ 1 (fun p : ℝ × ℝ => sweepFam r D lam δ₁ δ₂ p.1 p.2) :=
    (hsm lam δ₁ δ₂ hδ₁ne hδ₂ne).1
  have hsmper : ∀ σ t : ℝ, sweepFam r D lam δ₁ δ₂ σ (t + period) = sweepFam r D lam δ₁ δ₂ σ t :=
    (hsm lam δ₁ δ₂ hδ₁ne hδ₂ne).2.1
  have hsmslice : ∀ σ : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => sweepFam r D lam δ₁ δ₂ σ t) :=
    (hsm lam δ₁ δ₂ hδ₁ne hδ₂ne).2.2
  -- ## (c) the shifted knot `K`, the wide-end slice `G`, and the correction `w`
  set K : ℝ → Space := fun t => r (t + c) with hK
  set G : ℝ → Space := fun t => sweepFam r D lam δ₁ δ₂ σ₀ (Θ t) with hG
  set w : ℝ → Space := fun t => G t - K t with hw
  have hKsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K := by
    rw [hK]
    exact (hr.smooth.of_le le_top).comp (by
      simpa using (contDiff_id.add contDiff_const :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => t + c)))
  have hGsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    rw [hG]; exact (hsmslice σ₀).comp hΘsm
  have hwsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := by
    rw [hw, hG, hK]
    refine ((hsmslice σ₀).comp hΘsm).sub ?_
    exact (hr.smooth.of_le le_top).comp (by
      simpa using (contDiff_id.add contDiff_const :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => t + c)))
  have hwper : Function.Periodic w period := by
    intro t
    show w (t + period) = w t
    simp only [hw, hG, hK]
    rw [show t + period + c = (t + c) + period from by ring]
    rw [hΘshift t, hsmper σ₀ (Θ t), hr.periodic (t + c)]
  have hwbd : ∀ t : ℝ, ‖w t‖ < ε_uc := by
    intro t
    simpa only [hw, hG, hK] using he1 t
  have hwvel : ∀ t : ℝ, ‖velocity w t‖ < ε_uc := by
    intro t
    have h := he2 t
    have hderiv : velocity w t
        = deriv (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ (Θ u)) t - velocity r (t + c) := by
      simp only [velocity, hw, hG, hK]
      rw [show (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ (Θ u) - r (u + c))
          = (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ (Θ u)) - fun u : ℝ => r (u + c) from rfl]
      rw [deriv_sub]
      · congr 1
        exact deriv_shift r ((hr.smooth.of_le le_top).differentiable hle0 (t + c))
      · exact (hGsmooth.differentiable hle0) t
      · exact DifferentiableAt.comp t
          ((hr.smooth.of_le le_top).differentiable hle0 (t + c)) (by fun_prop)
    rw [hderiv]; exact h
  -- ## (d) the three phases
  set A : ℝ → ℝ → Space := fun t p => r (t + c * p) with hA
  set B : ℝ → ℝ → Space := fun t p => K t + p • w t with hB
  set σfun : ℝ → ℝ := fun p => ε + (σ₀ - ε) * (1 - gluePsi p) with hσfun
  set θfun : ℝ → ℝ → ℝ := fun p t => (1 - p) * Θ t + p * t with hθfun
  set Cc : ℝ → ℝ → Space := fun t p => sweepFam r D lam δ₁ δ₂ (σfun p) (θfun p t) with hC
  -- phase A: rotations of `r`
  have hAjoint : ContDiff ℝ 1 (fun p : ℝ × ℝ => A p.1 p.2) := by
    rw [hA]
    have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 + c * p.2) := by fun_prop
    exact (hr.smooth.of_le le_top).of_le hle |>.comp h1
  have hAper : ∀ s t : ℝ, A (t + period) s = A t s := by
    intro s t
    show r (t + period + c * s) = r (t + c * s)
    rw [show t + period + c * s = (t + c * s) + period from by ring]
    exact hr.periodic _
  have hAslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => A t s) := by
    intro s hs
    rw [hA]
    simpa using isCInfKnot_shift (IsSmoothKnot.toCInf hr) (c * s)
  have hA1 : ∀ t : ℝ, A t 1 = K t := by
    intro t; rw [hA, hK]; ring_nf
  have hA0 : ∀ t : ℝ, A t 0 = r t := by
    intro t; rw [hA]; simp
  -- phase B: interpolating the shifted knot towards the wide-end slice
  have hBjoint : ContDiff ℝ 1 (fun p : ℝ × ℝ => B p.1 p.2) := by
    rw [hB]
    refine (hKsmooth.of_le hle).comp contDiff_fst |>.add ?_
    exact contDiff_snd.smul ((hwsmooth.of_le hle).comp contDiff_fst)
  have hBper : ∀ s t : ℝ, B (t + period) s = B t s := by
    intro s t
    show K (t + period) + s • w (t + period) = K t + s • w t
    rw [show K (t + period) = K t from by
      rw [hK]
      show r (t + period + c) = r (t + c)
      rw [show t + period + c = (t + c) + period from by ring]
      exact hr.periodic (t + c), hwper t]
  have hBslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => B t s) := by
    intro s hs
    have hnorm1 : ∀ t : ℝ, ‖s • w t‖ < ε_uc := by
      intro t
      rw [norm_smul]
      have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
      calc |s| * ‖w t‖ ≤ 1 * ‖w t‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
        _ = ‖w t‖ := one_mul _
        _ < ε_uc := hwbd t
    have hnorm2 : ∀ t : ℝ, ‖deriv (fun u : ℝ => s • w u) t‖ < ε_uc := by
      intro t
      have hd : deriv (fun u : ℝ => s • w u) t = s • velocity w t := by
        show deriv (fun u : ℝ => s • w u) t = s • deriv w t
        exact (((hwsmooth.differentiable hle0) t).hasDerivAt.const_smul s).deriv
      rw [hd, norm_smul]
      have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
      calc |s| * ‖velocity w t‖ ≤ 1 * ‖velocity w t‖ :=
            mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
        _ = ‖velocity w t‖ := one_mul _
        _ < ε_uc := hwvel t
    have hWsm : ContDiff ℝ 1 (fun q : ℝ × ℝ => s • w q.1) :=
      ((hwsmooth.of_le hle).comp contDiff_fst).const_smul s
    have hWper : ∀ a t : ℝ, s • w (t + period) = s • w t := by
      intro a t; rw [hwper t]
    have hWsmall : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
        ‖s • w t‖ < ε_uc ∧ ‖deriv (fun u : ℝ => s • w u) t‖ < ε_uc :=
      fun a ha t => ⟨hnorm1 t, hnorm2 t⟩
    obtain ⟨hc1, hc2, hc3⟩ := h_uc (fun t a => s • w t) hWsm hWper hWsmall
      (sweepParam c) ⟨(sweepParam_mem c).1, (sweepParam_mem c).2.le⟩
    have hshift : (fun t : ℝ => r (t + sweepParam c * period) + s • w t)
        = fun t : ℝ => B t s := by
      funext t
      show r (t + sweepParam c * period) + s • w t = K t + s • w t
      rw [hK]
      congr 1
      exact (shift_eq_mod hr.periodic c t).symm
    rw [hshift] at hc1 hc2 hc3
    refine ⟨?_, hc1, hc2, hc3⟩
    rw [hB]
    simpa only [hK] using hKsmooth.add (hwsmooth.const_smul s)
  have hB0 : ∀ t : ℝ, B t 0 = K t := by
    intro t; rw [hB]; simp
  have hB1 : ∀ t : ℝ, B t 1 = G t := by
    intro t
    show K t + (1 : ℝ) • (G t - K t) = G t
    rw [one_smul]
    abel
  -- the interpolation facts for the reparametrisation θ
  have hΘ1c : ContDiff ℝ 1 Θ := hΘsm.of_le hle
  obtain ⟨hθjoint1, hθderiv, hθshift⟩ := interpTheta_facts hΘ1c hΘshift hΘderiv
  have hθsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (1 - q.2) * Θ q.1 + q.2 * q.1) := interpTheta_smooth hΘsm
  have hσmem : ∀ p ∈ Set.Icc (0 : ℝ) 1, ε ≤ σfun p ∧ σfun p ≤ σ₀ := by
    intro p hp
    have hg : gluePsi p ∈ Set.Icc (0 : ℝ) 1 := gluePsi_facts.2.2.1 p hp
    have hsub : 0 ≤ σ₀ - ε := by linarith
    rw [hσfun]
    have h1 : 0 ≤ (σ₀ - ε) * (1 - gluePsi p) :=
      mul_nonneg hsub (by linarith [hg.2])
    have h2 : (σ₀ - ε) * (1 - gluePsi p) ≤ σ₀ - ε := by
      have h3 : (1 - gluePsi p) ≤ 1 := by linarith [hg.1]
      nlinarith [hsub, h3]
    exact ⟨by linarith, by linarith⟩
  have hσc1 : ContDiff ℝ 1 σfun := by
    rw [hσfun]
    have hg : ContDiff ℝ 1 gluePsi := gluePsi_facts.2.2.2.2
    exact contDiff_const.add (contDiff_const.mul (contDiff_const.sub hg))
  -- phase C: the sweep itself, reparametrised
  have hCcjoint : ContDiff ℝ 1 (fun p : ℝ × ℝ => Cc p.1 p.2) := by
    rw [hC]
    have hinner : ContDiff ℝ 1 (fun q : ℝ × ℝ => (σfun q.2, θfun q.2 q.1)) := by
      refine (hσc1.comp contDiff_snd).prodMk ?_
      rw [hθfun]
      exact hθjoint1
    have hcomp := hsmjoint.comp hinner
    simpa only [Function.comp_def] using hcomp
  have hCcper : ∀ s t : ℝ, Cc (t + period) s = Cc t s := by
    intro s t
    show sweepFam r D lam δ₁ δ₂ (ε + (σ₀ - ε) * (1 - gluePsi s))
        ((1 - s) * Θ (t + period) + s * (t + period))
      = sweepFam r D lam δ₁ δ₂ (ε + (σ₀ - ε) * (1 - gluePsi s)) ((1 - s) * Θ t + s * t)
    rw [show (1 - s) * Θ (t + period) + s * (t + period)
        = ((1 - s) * Θ t + s * t) + period from by rw [hΘshift t]; ring]
    exact hsmper _ _
  have hCcslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => Cc t s) := by
    intro s hs
    have hmem := hσmem s hs
    have hslic : IsCInfKnot (fun t : ℝ => sweepFam r D lam δ₁ δ₂ (σfun s) t) :=
      ⟨hsmslice (σfun s), hsmper (σfun s), (hσcl (σfun s) hmem).1, (hσcl (σfun s) hmem).2⟩
    have hgsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => θfun s t) := by
      rw [hθfun]
      exact hθsmooth.comp (contDiff_id.prodMk contDiff_const)
    have hgshift : ∀ t : ℝ, θfun s (t + period) = θfun s t + period := by
      intro t
      show (1 - s) * Θ (t + period) + s * (t + period) = (1 - s) * Θ t + s * t + period
      rw [hΘshift t]; ring
    have hgderiv : ∀ t : ℝ, 0 < deriv (fun u : ℝ => θfun s u) t := by
      intro t
      have := hθderiv s hs t
      rwa [show (fun u : ℝ => θfun s u) = fun u : ℝ => (1 - s) * Θ u + s * u from by
        funext u; rw [hθfun]] at this
    have hcomp := isCInfKnot_comp_reparam hgsmooth hgshift hgderiv hslic
    rw [hC]
    simpa only [Function.comp_def] using hcomp
  have hCc0 : ∀ t : ℝ, Cc t 0 = G t := by
    intro t
    show sweepFam r D lam δ₁ δ₂ (ε + (σ₀ - ε) * (1 - gluePsi 0)) ((1 - 0) * Θ t + 0 * t) = G t
    have h1 : ε + (σ₀ - ε) * (1 - gluePsi 0) = σ₀ := by rw [gluePsi_facts.1]; ring
    have h2 : (1 - 0) * Θ t + 0 * t = Θ t := by ring
    rw [h1, h2, hG]
  have hCc1 : ∀ t : ℝ, Cc t 1 = sweepNeedleFam r D lam δ₁ δ₂ ε t := by
    intro t
    show sweepFam r D lam δ₁ δ₂ (ε + (σ₀ - ε) * (1 - gluePsi 1)) ((1 - 1) * Θ t + 1 * t)
      = sweepNeedleFam r D lam δ₁ δ₂ ε t
    have h1 : ε + (σ₀ - ε) * (1 - gluePsi 1) = ε := by rw [gluePsi_facts.2.1]; ring
    have h2 : (1 - 1) * Θ t + 1 * t = t := by ring
    rw [h1, h2]
    rfl
  -- ## (e) gluing the phases
  set AB : ℝ → ℝ → Space := fun t s => sweepGlue A B s t with hAB
  obtain ⟨hABjoint, hABper, hABslice, hAB0, hAB1⟩ :=
    sweepGlue_clauses hAjoint hBjoint (fun t => (hA1 t).trans (hB0 t).symm)
      hAslice hBslice hAper hBper
  have hABjoint' : ContDiff ℝ 1 (fun p : ℝ × ℝ => AB p.1 p.2) := hABjoint
  have hABper' : ∀ s t : ℝ, AB (t + period) s = AB t s := hABper
  have hAB0' : ∀ t : ℝ, AB t 0 = A t 0 := hAB0
  have hAB1' : ∀ t : ℝ, AB t 1 = B t 1 := hAB1
  have hjun : ∀ t : ℝ, AB t 1 = Cc t 0 := by
    intro t
    rw [hAB1', hB1 t, hCc0 t]
  obtain ⟨hHjoint, hHper, hHslice, hH0, hH1⟩ :=
    sweepGlue_clauses hABjoint' hCcjoint hjun hABslice hCcslice hABper' hCcper
  refine ⟨lam, δ₁, δ₂, r, fun t s => sweepGlue AB Cc s t, ?_, hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hlam0, hlam1, hδ₁0, hδ₂0, hδ₂ε2, hlamΔ, hδ₁Δ, hδ₂Δ⟩
  · intro t
    exact ⟨by rw [sub_self, norm_zero]; exact hδ, by rw [sub_self, norm_zero]; exact hδ⟩
  · exact hHjoint
  · exact hHper
  · exact hHslice
  · intro t
    show sweepGlue AB Cc 0 t = r t
    rw [hH0, hAB0']
    exact hA0 t
  · intro t
    show sweepGlue AB Cc 1 t = sweepNeedleFam r D lam δ₁ δ₂ ε t
    rw [hH1]
    exact hCc1 t


end Work.Drive
