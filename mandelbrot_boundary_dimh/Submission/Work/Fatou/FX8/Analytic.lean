import Submission.Work.Fatou.FX8.Orbit
import Submission.Work.Fatou.FX8.preimageOfBall
import Submission.Work.Fatou.Qreg.fatouFundamental
import Submission.Work.Fatou.Qreg.forwardIterate
import Submission.Work.Fatou.Qreg.backwardIterate
import Submission.Lib.Unif2.Packaging
import Submission.Lib.Unif2.Work.Parabolic.holomorphicOnX_comp_biholomorph
import Submission.Lib.Unif2.Holomorphic

/-!
# FX8, step 5: holomorphy of the constructed Fatou coordinate

`Φ = Ψ ∘ Π / b` is holomorphic on `Qreg b₁ b₂`.

The argument is by propagation along the sheets:

* on the window `U = {z ∈ Qreg | x₀ - 1/8 < Re z < x₀ + 31/32}` the coordinate is manifestly
  `Ψ ∘ (chart 0)⁻¹ / b` (both sides of the cut are checked by hand with the explicit formulas for
  `devH`), hence holomorphic there;
* holomorphy propagates in both directions along an orbit piece (`F` is a local biholomorphism,
  `Φ (F z) = Φ z + 1`);
* every point of `Qreg` is linked to its fundamental-strip representative by an orbit piece, and
  every fundamental-strip point is either itself in `U` or a single `F`-step away from a point
  of `U` (the preimage of it, which exists in `U`).
-/

namespace Work.Fatou.FX8

open MandelDim Set Metric Complex
open scoped Topology Manifold ContDiff
open LeanEval.Geometry
open Classical

noncomputable section

open Work.Fatou

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ}

/-- The chart at `ofℂ (1/2)` is the chart of index `0`. -/
theorem chartAt_ofℂ_half (D : Work.Fatou.FatouData) :
    (chartAt ℂ (D.ofℂ ((1 : ℂ) / 2)) : OpenPartialHomeomorph D.XF ℂ) = D.chart 0 := by
  rw [show (chartAt ℂ (D.ofℂ ((1 : ℂ) / 2)) : OpenPartialHomeomorph D.XF ℂ)
      = D.chart ⌊(D.toℂ (D.ofℂ ((1 : ℂ) / 2))).re⌋ from rfl]
  norm_num

/-- A biholomorphism `XF D → ℂ` is holomorphic in the sense of the library. -/
theorem holomorphicOnXAt_psi {D : Work.Fatou.FatouData}
    (Ψ : D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) (x : D.XF) :
    Submission.HolomorphicOnXAt Ψ x := by
  have h := Work.Parabolic.analyticAt_chart_representation_infty (Φ := ⇑Ψ) Ψ.contMDiff x
  rw [chartAt_self_eq] at h
  simp only [OpenPartialHomeomorph.refl_apply] at h
  simpa only [Submission.HolomorphicOnXAt, Function.comp_def, id_eq] using h

/-- **The complex coordinate of `Ψ` in the chart of index `0`.** -/
theorem analyticAt_chart0 {D : Work.Fatou.FatouData}
    (Ψ : D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) {u : D.XF}
    (hu : u ∈ (D.chart 0).source) :
    AnalyticAt ℂ (fun v => Ψ ((D.chart 0).symm v)) ((D.chart 0) u) := by
  have hhol : Submission.HolomorphicOnXAt Ψ u := holomorphicOnXAt_psi Ψ u
  have hmem : u ∈ (chartAt ℂ (D.ofℂ ((1 : ℂ) / 2)) : OpenPartialHomeomorph D.XF ℂ).source := by
    rw [chartAt_ofℂ_half D]; exact hu
  have h := (Submission.HolomorphicOnXAt_iff_chart hmem).mp hhol
  rwa [chartAt_ofℂ_half D] at h

/-- The same, phrased on the target of the chart. -/
theorem analyticAt_chart0_target {D : Work.Fatou.FatouData}
    (Ψ : D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) {w : ℂ}
    (hw : w ∈ (D.chart 0).target) :
    AnalyticAt ℂ (fun v => Ψ ((D.chart 0).symm v)) w := by
  have hu : (D.chart 0).symm w ∈ (D.chart 0).source := (D.chart 0).map_target hw
  have h := analyticAt_chart0 Ψ hu
  rwa [(D.chart 0).right_inv hw] at h

/-- Elements of the fundamental strip with `Re z < x₀ + 31/32` are detected by the elementary
estimate on the real part: every `F`-preimage in `Qreg` has real part `< x₀`. -/
theorem mem_fundStrip_of_re (hF : NearTranslationOn F (Qreg b₁ b₂)) {z : ℂ}
    (hz : z ∈ Qreg b₁ b₂) (h0 : Work.Fatou.xOf b₁ b₂ ≤ z.re)
    (h321 : z.re < Work.Fatou.xOf b₁ b₂ + 31 / 32) :
    z ∈ fundStrip F (Qreg b₁ b₂) (Work.Fatou.xOf b₁ b₂) := by
  refine ⟨hz, h0, ?_⟩
  intro w hwQ hFw
  have hε : ‖F w - (w + 1)‖ ≤ (1 / 32 : ℝ) := (hF.2 w hwQ).1
  have hre : |(F w - (w + 1)).re| ≤ (1 / 32 : ℝ) :=
    le_trans (Complex.abs_re_le_norm _) hε
  have hsub : (F w - (w + 1)).re = z.re - w.re - 1 := by
    rw [hFw]; simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; ring
  have hle : -(1 / 32 : ℝ) ≤ z.re - w.re - 1 := by
    rw [← hsub]; exact (abs_le.mp hre).1
  linarith

/-- **Holomorphy propagates forwards along an orbit step.** -/
theorem analyticAt_F_of {Φ : ℂ → ℂ} (hF : NearTranslationOn F (Qreg b₁ b₂))
    (habel : ∀ z ∈ Qreg b₁ b₂, F z ∈ Qreg b₁ b₂ → Φ (F z) = Φ z + 1)
    {z : ℂ} (hz : z ∈ Qreg b₁ b₂) (hzF : F z ∈ Qreg b₁ b₂) (h : AnalyticAt ℂ Φ z) :
    AnalyticAt ℂ Φ (F z) := by
  have hopen : IsOpen (Qreg b₁ b₂) := Work.Fatou.Qreg.isOpen_Qreg b₁ b₂
  have hFan : AnalyticAt ℂ F z := hF.1.analyticAt (hopen.mem_nhds hz)
  have hderiv : deriv F z ≠ 0 := by
    intro h0
    have h32 := (hF.2 z hz).2
    rw [h0] at h32
    norm_num at h32
  let g : ℂ → ℂ := hFan.hasStrictDerivAt.localInverse F (deriv F z) z hderiv
  have hgan : AnalyticAt ℂ g (F z) := hFan.analyticAt_localInverse hderiv
  have hgz : g (F z) = z := HasStrictFDerivAt.localInverse_apply_image _
  have hright : ∀ᶠ w in 𝓝 (F z), F (g w) = w :=
    HasStrictDerivAt.eventually_right_inverse _ hderiv
  have hgQ : ∀ᶠ w in 𝓝 (F z), g w ∈ Qreg b₁ b₂ :=
    hgan.continuousAt.eventually (hopen.mem_nhds (by rw [hgz]; exact hz))
  have h' : AnalyticAt ℂ Φ (g (F z)) := by rw [hgz]; exact h
  have hcomp : AnalyticAt ℂ (fun w => Φ (g w) + 1) (F z) :=
    ((show AnalyticAt ℂ (fun w => Φ (g w)) (F z) from h'.comp hgan)).add analyticAt_const
  have hQnear : ∀ᶠ w in 𝓝 (F z), w ∈ Qreg b₁ b₂ := hopen.mem_nhds hzF
  have heq : Φ =ᶠ[𝓝 (F z)] (fun w => Φ (g w) + 1) := by
    filter_upwards [hright, hgQ, hQnear] with w hw hwQ hwQ'
    have hmem : F (g w) ∈ Qreg b₁ b₂ := by rw [hw]; exact hwQ'
    simpa only [hw] using habel (g w) hwQ hmem
  exact hcomp.congr heq.symm

/-- **Holomorphy propagates backwards along an orbit step.** -/
theorem analyticAt_of_F {Φ : ℂ → ℂ} (hF : NearTranslationOn F (Qreg b₁ b₂))
    (habel : ∀ z ∈ Qreg b₁ b₂, F z ∈ Qreg b₁ b₂ → Φ (F z) = Φ z + 1)
    {z : ℂ} (hz : z ∈ Qreg b₁ b₂) (hzF : F z ∈ Qreg b₁ b₂) (h : AnalyticAt ℂ Φ (F z)) :
    AnalyticAt ℂ Φ z := by
  have hopen : IsOpen (Qreg b₁ b₂) := Work.Fatou.Qreg.isOpen_Qreg b₁ b₂
  have hFan : AnalyticAt ℂ F z := hF.1.analyticAt (hopen.mem_nhds hz)
  have heq : Φ =ᶠ[𝓝 z] (fun w => Φ (F w) - 1) := by
    filter_upwards [hopen.mem_nhds hz,
      hFan.continuousAt.eventually (hopen.mem_nhds hzF)] with w hwQ hwF
    rw [habel w hwQ hwF]
    ring
  exact ((h.comp hFan).sub analyticAt_const).congr heq.symm

/-- Holomorphy propagates backwards along an orbit piece. -/
theorem analyticAt_of_piece {Φ : ℂ → ℂ} (hF : NearTranslationOn F (Qreg b₁ b₂))
    (habel : ∀ z ∈ Qreg b₁ b₂, F z ∈ Qreg b₁ b₂ → Φ (F z) = Φ z + 1) (z : ℂ) :
    ∀ k : ℕ, (∀ j ≤ k, F^[j] z ∈ Qreg b₁ b₂) → AnalyticAt ℂ Φ (F^[k] z) →
      AnalyticAt ℂ Φ z := by
  intro k
  induction k with
  | zero => intro hp h; simpa using h
  | succ n ih =>
    intro hp h
    have hp1 : ∀ j ≤ n, F^[j] z ∈ Qreg b₁ b₂ :=
      fun j hj => hp j (le_trans hj (Nat.le_succ n))
    have hmem : F^[n] z ∈ Qreg b₁ b₂ := hp n (Nat.le_succ n)
    have hmem' : F (F^[n] z) ∈ Qreg b₁ b₂ := by
      have := hp (n + 1) le_rfl
      rwa [Function.iterate_succ_apply'] at this
    have h2 : AnalyticAt ℂ Φ (F (F^[n] z)) := by
      rw [Function.iterate_succ_apply'] at h
      exact h
    have h' : AnalyticAt ℂ Φ (F^[n] z) :=
      analyticAt_of_F hF habel hmem hmem' h2
    exact ih hp1 h'

/-- Holomorphy propagates forwards along an orbit piece. -/
theorem analyticAt_piece_of {Φ : ℂ → ℂ} (hF : NearTranslationOn F (Qreg b₁ b₂))
    (habel : ∀ z ∈ Qreg b₁ b₂, F z ∈ Qreg b₁ b₂ → Φ (F z) = Φ z + 1) (z : ℂ) :
    ∀ k : ℕ, (∀ j ≤ k, F^[j] z ∈ Qreg b₁ b₂) → AnalyticAt ℂ Φ z →
      AnalyticAt ℂ Φ (F^[k] z) := by
  intro k
  induction k with
  | zero => intro hp h; simpa using h
  | succ n ih =>
    intro hp h
    have hp1 : ∀ j ≤ n, F^[j] z ∈ Qreg b₁ b₂ :=
      fun j hj => hp j (le_trans hj (Nat.le_succ n))
    have hmem : F^[n] z ∈ Qreg b₁ b₂ := hp n (Nat.le_succ n)
    have hmem' : F (F^[n] z) ∈ Qreg b₁ b₂ := by
      have := hp (n + 1) le_rfl
      rwa [Function.iterate_succ_apply'] at this
    rw [Function.iterate_succ_apply']
    exact analyticAt_F_of hF habel hmem hmem' (ih hp1 h)

/-- **The window where the coordinate is manifestly `Ψ ∘ (chart 0)⁻¹ / b`.** -/
theorem Phi_eq_chart0 (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    (od : OrbitData b₁ b₂ F)
    (Ψ : (fatouData b₁ b₂ F hadm hF).XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)
    {b : ℂ} (hb : b ≠ 0)
    (hshift : ∀ u, Ψ ((fatouData b₁ b₂ F hadm hF).T u) = Ψ u + b)
    {w : ℂ} (hw : w ∈ Qreg b₁ b₂) (h1 : Work.Fatou.xOf b₁ b₂ - 1 / 8 < w.re)
    (h2 : w.re < Work.Fatou.xOf b₁ b₂ + 31 / 32) :
    Phi hadm hF od Ψ b w = Ψ (((fatouData b₁ b₂ F hadm hF).chart 0).symm w) / b := by
  set D : Work.Fatou.FatouData := fatouData b₁ b₂ F hadm hF with hD
  by_cases hge : Work.Fatou.xOf b₁ b₂ ≤ w.re
  · -- `w` lies in the fundamental strip: `Π w = ζ(w)` and `devH (ζ w) = w`
    have hfs : w ∈ fundStrip F (Qreg b₁ b₂) (Work.Fatou.xOf b₁ b₂) :=
      mem_fundStrip_of_re hF hw hge h2
    have hrep := od.rep_self w hw hfs
    have hPi : Pi hadm hF od w = canonParam hadm hF w := by
      simp only [Pi, hrep.1, hrep.2, Int.cast_zero, add_zero]
    have hcanon : D.devH (canonParam hadm hF w) = w := by
      simpa only [D, fatouData, Work.Fatou.FatouData.devH_eq] using devH_canonParam hadm hF hfs
    have hsymm : (D.chart 0).symm w = D.ofℂ (Pi hadm hF od w) := by
      have h1 : (D.chart 0).symm w = (D.chart 0).symm (D.devH (canonParam hadm hF w)) := by
        rw [hcanon]
      rw [h1, D.chart_symm_devH 0 (canonParam hadm hF w), hPi]
      simp
    rw [Phi_apply, hsymm]
  · -- `w` is on the cut side: `rep w = F w`, `lev w = -1` and `Π w = w - x₀`
    have hlt : w.re < Work.Fatou.xOf b₁ b₂ := lt_of_not_ge hge
    have h₂ : ∀ b ∈ b₂, Work.Fatou.xOf b₁ b₂ + 3 < b.re := Work.Fatou.xOf_lt_right hadm
    have hstep := Work.Fatou.Qreg.step_mem h₂ hF hw hlt
    have hFwQ : F w ∈ Qreg b₁ b₂ := hstep.1
    have hfsF : F w ∈ fundStrip F (Qreg b₁ b₂) (Work.Fatou.xOf b₁ b₂) := by
      refine ⟨hFwQ, by linarith [hstep.2], ?_⟩
      intro u huQ hFu
      have huw : u = w :=
        Work.Fatou.Qreg.fatouInjOnQ b₁ b₂ F hadm hF huQ hw (by rw [hFu])
      rw [huw]; exact hlt
    have hrepF := od.rep_self (F w) hFwQ hfsF
    have hstep2 := od.rep_step w hw hFwQ
    have hrepw : od.rep w = F w := hstep2.1.symm.trans hrepF.1
    have hlevw : od.lev w = -1 := by
      have : (0 : ℤ) = od.lev w + 1 := by rw [← hstep2.2, hrepF.2]
      omega
    have hPi : Pi hadm hF od w = canonParam hadm hF (F w) - 1 := by
      simp only [Pi, hrepw, hlevw]
      push_cast
      ring
    -- `canonParam (F w) = w - x₀ + 1`
    have hlam : canonParam hadm hF (F w) = w - (Work.Fatou.xOf b₁ b₂ : ℂ) + 1 := by
      apply Work.Fatou.devH_injective (Work.Fatou.Surface.devHBound_xOf hadm hF)
      rw [devH_canonParam hadm hF hfsF]
      have h7 : (7 / 8 : ℝ) ≤ (w - (Work.Fatou.xOf b₁ b₂ : ℂ) + 1).re := by
        simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re]
        linarith
      have h9 : (w - (Work.Fatou.xOf b₁ b₂ : ℂ) + 1).re ≤ 9 / 8 := by
        simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re]
        linarith
      rw [Work.Fatou.devH_of_ge h7 h9]
      ring_nf
    have hPi' : Pi hadm hF od w = w - (Work.Fatou.xOf b₁ b₂ : ℂ) := by
      rw [hPi, hlam]; ring
    have hdevw : D.devH (w - (Work.Fatou.xOf b₁ b₂ : ℂ)) = w := by
      have hle : (w - (Work.Fatou.xOf b₁ b₂ : ℂ)).re ≤ 1 / 8 := by
        simp only [Complex.sub_re, Complex.ofReal_re]; linarith
      have hd := Work.Fatou.devH_of_le_one_eighth (x₀ := Work.Fatou.xOf b₁ b₂) (F := F) hle
      simp only [D, fatouData, Work.Fatou.FatouData.devH_eq]
      rw [hd]; ring
    have hsymm : (D.chart 0).symm w = D.ofℂ (Pi hadm hF od w) := by
      have h1 : (D.chart 0).symm w = (D.chart 0).symm (D.devH (w - (xOf b₁ b₂ : ℂ))) := by
        rw [hdevw]
      rw [h1, D.chart_symm_devH 0 (w - (xOf b₁ b₂ : ℂ)), ← hPi']
      simp
    rw [Phi_apply, hsymm]

/-- Points of the window lie in the target of the chart of index `0`. -/
theorem mem_chart0_target (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    {w : ℂ} (hw : w ∈ Qreg b₁ b₂) (h1 : Work.Fatou.xOf b₁ b₂ - 1 / 8 < w.re)
    (h2 : w.re < Work.Fatou.xOf b₁ b₂ + 31 / 32) :
    w ∈ ((fatouData b₁ b₂ F hadm hF).chart 0).target := by
  set D : Work.Fatou.FatouData := fatouData b₁ b₂ F hadm hF with hD
  rw [show (D.chart 0).target = D.devH '' Sigma from Work.Fatou.FatouData.chart_target D 0]
  by_cases hge : Work.Fatou.xOf b₁ b₂ ≤ w.re
  · have hfs : w ∈ fundStrip F (Qreg b₁ b₂) (Work.Fatou.xOf b₁ b₂) :=
      mem_fundStrip_of_re hF hw hge h2
    refine ⟨canonParam hadm hF w, ?_, ?_⟩
    · have hspec := canonParam_spec hadm hF hfs
      exact mem_Sigma.mpr ⟨by linarith [hspec.1], by linarith [hspec.2.1]⟩
    · simpa only [D, fatouData, Work.Fatou.FatouData.devH_eq] using devH_canonParam hadm hF hfs
  · have hlt : w.re < Work.Fatou.xOf b₁ b₂ := lt_of_not_ge hge
    refine ⟨w - (Work.Fatou.xOf b₁ b₂ : ℂ), ?_, ?_⟩
    · exact mem_Sigma.mpr ⟨by simp only [Complex.sub_re, Complex.ofReal_re]; linarith,
        by simp only [Complex.sub_re, Complex.ofReal_re]; linarith⟩
    · have hle : (w - (Work.Fatou.xOf b₁ b₂ : ℂ)).re ≤ 1 / 8 := by
        simp only [Complex.sub_re, Complex.ofReal_re]; linarith
      have hd := Work.Fatou.devH_of_le_one_eighth (x₀ := Work.Fatou.xOf b₁ b₂) (F := F) hle
      simp only [D, fatouData, Work.Fatou.FatouData.devH_eq]
      rw [hd]; ring

/-- The coordinate is holomorphic on the window. -/
theorem analyticAt_of_window (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    (od : OrbitData b₁ b₂ F)
    (Ψ : (fatouData b₁ b₂ F hadm hF).XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)
    {b : ℂ} (hb : b ≠ 0)
    (hshift : ∀ u, Ψ ((fatouData b₁ b₂ F hadm hF).T u) = Ψ u + b)
    {w : ℂ} (hw : w ∈ Qreg b₁ b₂) (h1 : Work.Fatou.xOf b₁ b₂ - 1 / 8 < w.re)
    (h2 : w.re < Work.Fatou.xOf b₁ b₂ + 31 / 32) :
    AnalyticAt ℂ (Phi hadm hF od Ψ b) w := by
  have hwT : w ∈ ((fatouData b₁ b₂ F hadm hF).chart 0).target :=
    mem_chart0_target hadm hF hw h1 h2
  have hA : AnalyticAt ℂ (fun v => Ψ (((fatouData b₁ b₂ F hadm hF).chart 0).symm v) / b) w :=
    (analyticAt_chart0_target Ψ hwT).div_const
  have hnbhd : {v : ℂ | v ∈ Qreg b₁ b₂ ∧ Work.Fatou.xOf b₁ b₂ - 1 / 8 < v.re ∧
      v.re < Work.Fatou.xOf b₁ b₂ + 31 / 32} ∈ 𝓝 w := by
    have hopenQ : IsOpen (Qreg b₁ b₂) := Work.Fatou.Qreg.isOpen_Qreg b₁ b₂
    have hopenRe : IsOpen {v : ℂ | Work.Fatou.xOf b₁ b₂ - 1 / 8 < v.re ∧
        v.re < Work.Fatou.xOf b₁ b₂ + 31 / 32} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    exact (hopenQ.inter hopenRe).mem_nhds ⟨hw, h1, h2⟩
  refine hA.congr ?_
  filter_upwards [hnbhd] with v hv
  exact (Phi_eq_chart0 hadm hF od Ψ hb hshift hv.1 hv.2.1 hv.2.2).symm

/-- The fundamental strip lies below `x₀ + 1 + 1/31`. -/
theorem fundStrip_re_lt (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    {s : ℂ} (hs : s ∈ fundStrip F (Qreg b₁ b₂) (Work.Fatou.xOf b₁ b₂)) :
    s.re < Work.Fatou.xOf b₁ b₂ + 1 + 1 / 31 := by
  by_contra hcon
  obtain ⟨w, hwQ, hFw, hwx⟩ :=
    Work.Fatou.Surface.exists_preimage_of_xOf_add hadm hF hs.1 (by linarith)
  exact absurd hwx (not_le.mpr (hs.2.2 w hwQ hFw))

/-- **A high fundamental-strip point is the image of a point of the window.** -/
theorem exists_preimage_of_fundStrip_high (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂))
    {s : ℂ} (hs : s ∈ fundStrip F (Qreg b₁ b₂) (Work.Fatou.xOf b₁ b₂))
    (hsx : Work.Fatou.xOf b₁ b₂ + 31 / 32 ≤ s.re) :
    ∃ u ∈ Qreg b₁ b₂, F u = s ∧ Work.Fatou.xOf b₁ b₂ - 1 / 8 < u.re ∧
      u.re < Work.Fatou.xOf b₁ b₂ + 31 / 32 := by
  have hslt : s.re < Work.Fatou.xOf b₁ b₂ + 1 + 1 / 31 := fundStrip_re_lt hadm hF hs
  have hball : ∀ u : ℂ, dist u (s - 1) ≤ (1 / 32 : ℝ) → u ∈ Qreg b₁ b₂ := by
    intro u hu
    rw [dist_eq_norm] at hu
    have hre : |(u - (s - 1)).re| ≤ (1 / 32 : ℝ) := le_trans (Complex.abs_re_le_norm _) hu
    have hsub : (u - (s - 1)).re = u.re - s.re + 1 := by
      simp only [Complex.sub_re, Complex.one_re]; ring
    have hbounds := abs_le.mp hre
    rw [hsub] at hbounds
    have huP : s.re - 1 - 1 / 32 ≤ u.re := by linarith [hbounds.1]
    have huQ : u.re ≤ s.re - 1 + 1 / 32 := by linarith [hbounds.2]
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have ha' : a.re + 1 < Work.Fatou.xOf b₁ b₂ := Work.Fatou.xOf_gt_left hadm a ha
      have hpos : 0 < (u - a).re := by simp only [Complex.sub_re]; linarith
      have hle : -|(u - a).im| ≤ 0 := neg_nonpos.mpr (abs_nonneg _)
      linarith
    · have hb' : Work.Fatou.xOf b₁ b₂ + 3 < b.re := Work.Fatou.xOf_lt_right hadm b hb
      have hneg : (u - b).re < 0 := by simp only [Complex.sub_re]; linarith
      have hle : 0 ≤ |(u - b).im| := abs_nonneg _
      linarith
  obtain ⟨u, huQ, hFu, hdist⟩ := preimageOfBall hadm hF hball
  rw [dist_eq_norm] at hdist
  have hre : |(u - (s - 1)).re| ≤ (1 / 32 : ℝ) := le_trans (Complex.abs_re_le_norm _) hdist
  have hsub : (u - (s - 1)).re = u.re - s.re + 1 := by
    simp only [Complex.sub_re, Complex.one_re]; ring
  have hbounds := abs_le.mp hre
  rw [hsub] at hbounds
  refine ⟨u, huQ, hFu, ?_, ?_⟩
  · linarith [hbounds.1]
  · linarith [hbounds.2]

/-- **Holomorphy of the constructed Fatou coordinate.** -/
theorem analyticAt_Phi (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    (od : OrbitData b₁ b₂ F)
    (Ψ : (fatouData b₁ b₂ F hadm hF).XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)
    {b : ℂ} (hb : b ≠ 0)
    (hshift : ∀ u, Ψ ((fatouData b₁ b₂ F hadm hF).T u) = Ψ u + b) :
    ∀ z ∈ Qreg b₁ b₂, AnalyticAt ℂ (Phi hadm hF od Ψ b) z := by
  have habel : ∀ z ∈ Qreg b₁ b₂, F z ∈ Qreg b₁ b₂ →
      Phi hadm hF od Ψ b (F z) = Phi hadm hF od Ψ b z + 1 :=
    fun z hz hzF => Phi_abel hadm hF od Ψ hb hshift hz hzF
  -- holomorphy at a fundamental-strip point
  have hbase : ∀ s ∈ fundStrip F (Qreg b₁ b₂) (Work.Fatou.xOf b₁ b₂),
      AnalyticAt ℂ (Phi hadm hF od Ψ b) s := by
    intro s hs
    rcases lt_or_ge s.re (Work.Fatou.xOf b₁ b₂ + 31 / 32) with hlt | hge
    · exact analyticAt_of_window hadm hF od Ψ hb hshift hs.1 (by linarith [hs.2.1]) hlt
    · obtain ⟨u, huQ, hFu, hu1, hu2⟩ := exists_preimage_of_fundStrip_high hadm hF hs hge
      have hau : AnalyticAt ℂ (Phi hadm hF od Ψ b) u :=
        analyticAt_of_window hadm hF od Ψ hb hshift huQ hu1 hu2
      have hFuQ : F u ∈ Qreg b₁ b₂ := by rw [hFu]; exact hs.1
      have hFs : AnalyticAt ℂ (Phi hadm hF od Ψ b) (F u) :=
        analyticAt_F_of hF habel huQ hFuQ hau
      rwa [hFu] at hFs
  -- propagation to all of `Qreg`
  intro z hz
  obtain ⟨k, hcase⟩ := od.orbit z hz
  rcases hcase with ⟨hfin, hp⟩ | ⟨hfin, hp⟩
  · have hk : AnalyticAt ℂ (Phi hadm hF od Ψ b) (F^[k] z) := by
      rw [hfin]
      exact hbase (od.rep z) (od.rep_mem z hz)
    exact analyticAt_of_piece hF habel z k hp hk
  · have hk : AnalyticAt ℂ (Phi hadm hF od Ψ b) (od.rep z) := hbase (od.rep z) (od.rep_mem z hz)
    have h2 := analyticAt_piece_of hF habel (od.rep z) k hp hk
    rw [hfin] at h2
    exact h2

/-- **Holomorphy of the constructed Fatou coordinate (as a `DifferentiableOn`).** -/
theorem differentiableOn_Phi (hadm : QAdm b₁ b₂) (hF : NearTranslationOn F (Qreg b₁ b₂))
    (od : OrbitData b₁ b₂ F)
    (Ψ : (fatouData b₁ b₂ F hadm hF).XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)
    {b : ℂ} (hb : b ≠ 0)
    (hshift : ∀ u, Ψ ((fatouData b₁ b₂ F hadm hF).T u) = Ψ u + b) :
    DifferentiableOn ℂ (Phi hadm hF od Ψ b) (Qreg b₁ b₂) :=
  fun z hz => (analyticAt_Phi hadm hF od Ψ hb hshift z hz).differentiableAt.differentiableWithinAt

end

end Work.Fatou.FX8
