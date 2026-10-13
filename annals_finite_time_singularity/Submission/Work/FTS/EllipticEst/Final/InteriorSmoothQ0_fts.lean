/-
Copyright: work module for the Elgindi finite-time singularity project.

# Interior regularity for `bslOp α` on the quadrant (weight `(5-α)/α`, restricted tests)

This module *repairs* the last step of the Weyl-lemma chain of
`Submission/Work/EllipticEst/InteriorRegularity/Q0/`.  Everything heavy (the transported weak
identity `transportWeakRR`/`stripWeakQ0_of_RR`, the localized equation, the Sobolev tower
`VT.tower`, the Sobolev embedding and the gluing `glueAll`) is imported from the existing,
`sorry`-free modules; the two lemmas copied here are

* `localSmooth_generic_fts` — the generic local `C^m` representative of a pair `(V, G)` satisfying
  the strip weak identity;
* `localRep_fts` and the final `interiorSmoothQ0_fts` — the assembly.

The copy is necessary because the original home of those lemmas,
`Submission/Work/EllipticEst/InteriorRegularity/Q0/localRep.lean`, refers to two identifiers
that are defined nowhere in the tree (`weakLocQ0'` at line 92, `locallyIntegrableOn_Gf'` at
line 193), so its module cannot be built; the intended names are the (proved, sorry-free)
`Work.EllipticEst.InteriorRegularity.Q0.weakLocQ0` (in `Q0/weakLocQ0.lean`) and
`Work.EllipticEst.InteriorRegularity.Q0.locallyIntegrableOn_Gf` (in
`Q0/locallyIntegrableOn_Gf.lean`), and the four-argument call site is the three-argument one
(the extra `HasCompactSupport χ` hypothesis is not used by the proof of `weakLocQ0`).  The two
substitutions are the only changes; the declarations live in the same namespace so that every
unqualified reference inside the copied proofs resolves exactly as before.

This module is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.InteriorRegularity.Q0.Defs
import Submission.Work.EllipticEst.InteriorRegularity.Q0.locallyIntegrable_Vf
import Submission.Work.EllipticEst.InteriorRegularity.Q0.smoothOn_Gf
import Submission.Work.EllipticEst.InteriorRegularity.Q0.localEq
import Submission.Work.EllipticEst.InteriorRegularity.Q0.weakLocQ0
import Submission.Work.EllipticEst.InteriorRegularity.Q0.locallyIntegrableOn_Gf
import Submission.Work.EllipticEst.InteriorRegularity.VT.Tower
import Submission.Work.EllipticEst.InteriorRegularity.VT.Assembly
import Submission.Work.EllipticEst.InteriorRegularity.VT.LocalSmoothAux
import Submission.Work.EllipticEst.InteriorRegularity.VT.DerivAux
import Submission.Work.EllipticEst.InteriorRegularity.contDiff_mul_of_tsupport_subset
import Submission.Work.EllipticEst.InteriorRegularity.exists_contDiffOn_of_memSobolev
import Submission.Work.EllipticEst.InteriorRegularity.memSobolev_neg_two
import Submission.Work.EllipticEst.InteriorRegularity.Q0.glueAll
import Submission.Work.EllipticEst.InteriorRegularity.Q0.transportWeakRR
import Submission.Work.EllipticEst.InteriorRegularity.Q0.stripWeakQ0_of_RR
import Submission.Work.EllipticEst.InteriorRegularity.Q0.ae_eq_of_ae_eq_Vf
import Submission.Work.EllipticEst.InteriorRegularity.Q0.exists_tan_extension

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology SchwartzMap
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## The repaired chain -/


/-! ## The generic interior-regularity step -/

/-- **Interior regularity, generic form.**  A pair `(V, G)` with `V` locally integrable and `G`
smooth on the strip, satisfying the weak identity `∫ V · Kop ψ = ∫ G · ψ`, has a local `C^m`
representative near every interior point of the strip. -/
theorem localSmooth_generic_fts {V G : E2 → ℂ}
    (hV : MeasureTheory.LocallyIntegrableOn V stripE)
    (hG : MeasureTheory.LocallyIntegrableOn G stripE)
    (hGs : ∀ n : ℕ, ContDiffOn ℝ n G stripE)
    (hSW : StripWeakC V G) :
    ∀ (x₀ : E2) (m : ℕ), x₀ ∈ stripE →
      ∃ r : ℝ, 0 < r ∧ Metric.ball x₀ r ⊆ stripE ∧
        ∃ g : E2 → ℂ, ContDiffOn ℝ m g (Metric.ball x₀ r) ∧
          V =ᵐ[MeasureTheory.volume.restrict (Metric.ball x₀ r)] g := by
  intro x₀ m hx₀
  obtain ⟨h1, h2⟩ : 0 < x₀ 1 ∧ x₀ 1 < Real.pi / 2 := hx₀
  set δ : ℝ := min (x₀ 1) (Real.pi / 2 - x₀ 1) with hδdef
  have hδ : 0 < δ := lt_min h1 (by linarith [Real.pi_pos, h2])
  have hxδ : δ ≤ x₀ 1 := min_le_left _ _
  have hyδ : δ ≤ Real.pi / 2 - x₀ 1 := min_le_right _ _
  have hr8 : 0 < δ / 8 := by linarith
  -- the outer cut-off: supported in the strip, `1` on a neighbourhood of `x₀`
  set χout : E2 → ℂ := Work.EllipticEst.InteriorRegularity.VT.cfun x₀ (δ / 8) hr8 with hχoutdef
  have hout_s : ∀ n : ℕ, ContDiff ℝ n χout :=
    fun n => Work.EllipticEst.InteriorRegularity.VT.cfun_contDiff x₀ (δ / 8) hr8 n
  have hout_c : HasCompactSupport χout :=
    Work.EllipticEst.InteriorRegularity.VT.cfun_hasCompactSupport x₀ (δ / 8) hr8
  have hout_ts : tsupport χout ⊆ stripE := by
    intro x hx
    have hx' : x ∈ Metric.closedBall x₀ (2 * (δ / 8)) := by
      rw [hχoutdef, Work.EllipticEst.InteriorRegularity.VT.cfun_tsupport] at hx
      exact hx
    rw [Work.EllipticEst.InteriorRegularity.VT.mem_stripE]
    exact Work.EllipticEst.InteriorRegularity.VT.mem_Ioo_of_mem_ball hδ hxδ hyδ
      (Metric.closedBall_subset_ball (by linarith) hx')
  -- the cut-off pair is integrable and its source is smooth
  have hVt : Integrable (fun x : E2 => χout x * V x) :=
    integrable_mul_of_locallyIntegrableOn hV (hout_s 0).continuous hout_c hout_ts
  have hGt : Integrable (fun x : E2 => χout x * G x) :=
    integrable_mul_of_locallyIntegrableOn hG (hout_s 0).continuous hout_c hout_ts
  have hGts' : ∀ n : ℕ, ContDiff ℝ n (fun x : E2 => χout x * G x) :=
    fun n => contDiff_mul_of_tsupport_subset (U := stripE) (f := χout) (g := G)
      (hGs n) Work.EllipticEst.InteriorRegularity.VT.isOpen_stripE hout_s hout_ts
  have hweak : ∀ ψ : E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      Function.support ψ ⊆ {x : E2 | χout x = 1} →
      ∫ x, (χout x * V x) * Kop ψ x = ∫ x, (χout x * G x) * ψ x :=
    weakLocQ0 hSW hout_s hout_ts
  have hWball : Metric.closedBall x₀ (δ / 8) ⊆ {x : E2 | χout x = 1} := by
    intro x hx
    rw [hχoutdef]
    exact Work.EllipticEst.InteriorRegularity.VT.cfun_one hr8 hx
  -- the Sobolev tower
  obtain ⟨χ, hχs, hχc, ⟨ρ, hρ, hχ1⟩, hT⟩ :=
    Work.EllipticEst.InteriorRegularity.VT.tower (V := fun x : E2 => χout x * V x)
      (G := fun x : E2 => χout x * G x) hVt hGt hGts' hweak hδ hxδ hyδ hWball m
  have hIntχ : Integrable (fun x : E2 => χ x * (χout x * V x)) :=
    Work.EllipticEst.InteriorRegularity.VT.integrable_mul_of_cc hVt hχc hχs
  have hTχ : TemperedDistribution.MemSobolev (((m + 2 : ℕ) : ℝ)) 2
      (Work.EllipticEst.InteriorRegularity.VT.Td
        (fun x : E2 => χ x * (χout x * V x)) hIntχ) := by
    have h := hT hIntχ
    push_cast at h ⊢
    exact h
  -- the Sobolev embedding
  obtain ⟨r, hr, Φ, hΦ, hpairEmb⟩ :=
    Work.EllipticEst.InteriorRegularity.exists_contDiffOn_of_memSobolev (E := E2)
      (u := Work.EllipticEst.InteriorRegularity.VT.Td
        (fun x : E2 => χ x * (χout x * V x)) hIntχ) (k := m) (m := m + 2)
      (by rw [Work.EllipticEst.InteriorRegularity.VT.finrank_E2]; push_cast; linarith)
      hTχ x₀
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (Work.EllipticEst.InteriorRegularity.VT.isOpen_stripE.mem_nhds
      (show x₀ ∈ stripE from ⟨h1, h2⟩))
  -- shrink the ball so that all the cut-offs are `1` on it
  set ρ' : ℝ := min (min ρ r) (δ / 8) / 2 with hρ'def
  have hminpos : 0 < min (min ρ r) (δ / 8) := lt_min (lt_min hρ hr) hr8
  have hρ' : 0 < ρ' := by
    rw [hρ'def]; linarith
  have hρ'ρ : ρ' < ρ := by
    rw [hρ'def]
    have h2 : min (min ρ r) (δ / 8) ≤ min ρ r := min_le_left _ _
    have h3 : min ρ r ≤ ρ := min_le_left _ _
    linarith
  have hρ'r : ρ' < r := by
    rw [hρ'def]
    have h2 : min (min ρ r) (δ / 8) ≤ min ρ r := min_le_left _ _
    have h3 : min ρ r ≤ r := min_le_right _ _
    linarith
  have hρ'δ : ρ' < δ / 8 := by
    rw [hρ'def]
    have h2 : min (min ρ r) (δ / 8) ≤ δ / 8 := min_le_right _ _
    linarith
  set r₀ : ℝ := min ρ' ε with hr₀def
  have hr₀ : 0 < r₀ := lt_min hρ' hε
  have hr₀sub : Metric.ball x₀ r₀ ⊆ stripE :=
    (Metric.ball_subset_ball (min_le_right ρ' ε)).trans hεsub
  have hr₀r : r₀ ≤ r := le_of_lt (lt_of_le_of_lt (min_le_left ρ' ε) hρ'r)
  have hr₀ρ : Metric.ball x₀ r₀ ⊆ Metric.closedBall x₀ ρ :=
    (Metric.ball_subset_ball (le_of_lt (lt_of_le_of_lt (min_le_left ρ' ε) hρ'ρ))).trans
      Metric.ball_subset_closedBall
  have hr₀δ : Metric.ball x₀ r₀ ⊆ Metric.closedBall x₀ (δ / 8) :=
    (Metric.ball_subset_ball (le_of_lt (lt_of_le_of_lt (min_le_left ρ' ε) hρ'δ))).trans
      Metric.ball_subset_closedBall
  -- the pairings of `Φ` and of the localized unknown
  have hpair : ∀ ψ : 𝓢(E2, ℂ), (∀ y, ψ y ≠ 0 → y ∈ Metric.ball x₀ r₀) →
      ∫ y, ψ y • Φ y = ∫ y, ψ y • (χout y * V y) := by
    intro ψ hψ
    have hψr : ∀ y, ψ y ≠ 0 → y ∈ Metric.ball x₀ r := fun y hy =>
      Metric.ball_subset_ball hr₀r (hψ y hy)
    have h1 : ∫ y, ψ y • Φ y = ∫ y, ψ y • (χ y * (χout y * V y)) := by
      rw [← hpairEmb ψ hψr]
      exact Work.EllipticEst.InteriorRegularity.VT.Td_apply _ _ ψ
    rw [h1]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : ψ y = 0
    · simp [hy]
    · have hy2 : χ y = 1 := hχ1 y (hr₀ρ (hψ y hy))
      simp only [hy2, one_mul]
  have hVV : (fun x : E2 => χout x * V x)
      =ᵐ[MeasureTheory.volume.restrict (Metric.ball x₀ r₀)] Φ :=
    Work.EllipticEst.InteriorRegularity.VT.ae_eq_of_pairing
      (hΦ.mono (Metric.ball_subset_ball hr₀r)).continuousOn hVt hpair
  have hχ1ball : (fun x : E2 => χout x * V x)
      =ᵐ[MeasureTheory.volume.restrict (Metric.ball x₀ r₀)] V := by
    rw [Filter.EventuallyEq]
    refine (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr ?_
    refine Eventually.of_forall fun x hx => ?_
    show χout x * V x = V x
    rw [hWball (hr₀δ hx), one_mul]
  exact ⟨r₀, hr₀, hr₀sub, Φ, hΦ.mono (Metric.ball_subset_ball hr₀r),
    hχ1ball.symm.trans hVV⟩

/-! ## The requested theorem -/

theorem localRep_fts {α : ℝ} (hα : 0 < α) {F Ψ : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    (hsw : Work.EllipticEst.InteriorRegularity.Q0.StripWeakC
      (fun x : E2 => (Work.EllipticEst.InteriorRegularity.Q0.Vf α Ψ x : ℂ))
      (fun x : E2 => (Work.EllipticEst.InteriorRegularity.Q0.Gf α F x : ℂ))) :
    ∀ (x₀ : E2) (m : ℕ), x₀ ∈ Work.EllipticEst.InteriorRegularity.stripE →
      ∃ r : ℝ, 0 < r ∧ Metric.ball x₀ r ⊆ Work.EllipticEst.InteriorRegularity.stripE ∧
        ∃ g : E2 → ℂ, ContDiffOn ℝ m g (Metric.ball x₀ r) ∧
          (fun x : E2 => (Work.EllipticEst.InteriorRegularity.Q0.Vf α Ψ x : ℂ))
            =ᵐ[MeasureTheory.volume.restrict (Metric.ball x₀ r)] g := by
  refine localSmooth_generic_fts ?_ ?_ ?_ hsw
  · exact locallyIntegrable_Vf hα.ne' hΨ
  · exact locallyIntegrableOn_Gf hα hF
  · exact smoothOn_Gf hα hF

/-- The real part of a complex number divided by a real one. -/
theorem div_ofReal_re_fts (z : ℂ) (r : ℝ) : (z / (r : ℂ)).re = z.re / r := by
  rcases eq_or_ne r 0 with hr | hr
  · subst hr
    simp
  · rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_im,
      Complex.ofReal_re]
    simp only [mul_zero, sub_zero]
    rw [div_eq_mul_inv]

/-- The quotient of a `C^∞` function of the strip by the (smooth, nonvanishing) weight is `C^∞`
on the quadrant. -/
theorem smoothOpen_final_fts {α : ℝ} (hα : 0 < α) {Φt : E2 → ℂ}
    (hΦ : ∀ n : ℕ, ContDiffOn ℝ n Φt stripE) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Φt (coords ((1 / α) * Real.log z) θ)).re
        / wt α (coords ((1 / α) * Real.log z) θ)) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
  intro n
  have hlog' : ContDiffOn ℝ n (fun t : ℝ => (1 / α) * Real.log t) (Set.Ioi 0) :=
    contDiffOn_const.mul (Real.contDiffOn_log.mono (by
      intro t ht
      simpa using ne_of_gt ht))
  have hlog : ContDiffOn ℝ n (fun p : ℝ × ℝ => (1 / α) * Real.log p.1)
      Work.FTS.EllipticEst.Q0 := by
    have h := ContDiffOn.comp hlog' contDiff_fst.contDiffOn
      (fun p (hp : p ∈ Work.FTS.EllipticEst.Q0) => hp.1)
    simpa [Function.comp_def] using h
  have hth : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.2) Work.FTS.EllipticEst.Q0 :=
    contDiff_snd.contDiffOn
  have hpair : ContDiffOn ℝ n (fun p : ℝ × ℝ => ((1 / α) * Real.log p.1, p.2))
      Work.FTS.EllipticEst.Q0 := hlog.prodMk hth
  have hchart : ContDiffOn ℝ n (fun p : ℝ × ℝ => coords ((1 / α) * Real.log p.1) p.2)
      Work.FTS.EllipticEst.Q0 :=
    (contDiff_coords n).comp_contDiffOn hpair
  have hmap : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      coords ((1 / α) * Real.log p.1) p.2 ∈ stripE := by
    intro p hp
    rw [mem_stripE_iff]
    exact ⟨hp.2.1, hp.2.2⟩
  have hnum : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      (Φt (coords ((1 / α) * Real.log p.1) p.2)).re) Work.FTS.EllipticEst.Q0 :=
    Complex.reCLM.contDiff.comp_contDiffOn ((hΦ n).comp hchart hmap)
  have hden : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      wt α (coords ((1 / α) * Real.log p.1) p.2)) Work.FTS.EllipticEst.Q0 :=
    (wt_contDiff α n).comp_contDiffOn hchart
  change ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      (Φt (coords ((1 / α) * Real.log p.1) p.2)).re
        / wt α (coords ((1 / α) * Real.log p.1) p.2)) Work.FTS.EllipticEst.Q0
  exact ContDiffOn.div (𝕜 := ℝ) (n := n) hnum hden (fun p hp => wt_ne_zero hα (hmap p hp))

/-! ## The final assembly -/

/-- **Weyl's lemma for `bslOp α` on the quadrant** (weight `(5-α)/α`): a locally integrable weak
solution agrees a.e. with a `C^∞` function. -/
theorem interiorSmoothQ0_fts {α : ℝ} (hα : 0 < α) {F Ψ : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0,
          Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        = ∫ p in Work.FTS.EllipticEst.Q0,
            F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) :
    ∃ Φ : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen Φ ∧
      (fun p : ℝ × ℝ => Ψ p.1 p.2)
        =ᵐ[MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0]
          (fun p : ℝ × ℝ => Φ p.1 p.2) := by
  classical
  -- the transported weak identity
  have hsw : StripWeakC (fun x : E2 => (Vf α Ψ x : ℂ)) (fun x : E2 => (Gf α F x : ℂ)) :=
    stripWeakQ0_of_RR (transportWeakRR hα hΨ hweak)
  -- local `C^m` representatives
  have hrep := localRep_fts hα hF hΨ hsw
  -- gluing
  obtain ⟨Φt, hΦt, hVfeq⟩ :=
    glueAll isOpen_stripE_fts (fun x hx => hrep x 0 hx) (fun x m hx => hrep x m hx)
  refine ⟨fun z θ => (Φt (coords ((1 / α) * Real.log z) θ)).re
      / wt α (coords ((1 / α) * Real.log z) θ), smoothOpen_final_fts hα hΦt, ?_⟩
  -- transport the a.e. equality back to `Q0`
  have h1 := ae_eq_of_ae_eq_Vf hα hVfeq
  filter_upwards [h1] with p hp
  have h2 : (Ψ p.1 p.2 : ℂ).re
      = (Φt (coords ((1 / α) * Real.log p.1) p.2)
          / (wt α (coords ((1 / α) * Real.log p.1) p.2) : ℂ)).re := by rw [hp]
  rw [Complex.ofReal_re, div_ofReal_re_fts] at h2
  exact h2

end Work.EllipticEst.InteriorRegularity.Q0
