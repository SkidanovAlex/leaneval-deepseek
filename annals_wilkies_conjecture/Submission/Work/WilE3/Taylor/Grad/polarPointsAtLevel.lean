import Mathlib
import Submission.Work.WilE3.Taylor.Grad.PolarDefs
import Submission.Work.WilE3.eaEval_analytic
import Submission.Work.WilE3.Taylor.Arc.branch_count
import Submission.Work.WilE3.Taylor.Arc.complexify_order
import Submission.Work.WilE3.Taylor.Arc.ofReal_order
import Submission.Work.WilE3.Taylor.Arc.eaEvalC_arc_order
import Submission.Work.WilE3.Taylor.Arc.card_le_mul_card_image
import Submission.Work.WilE3.Taylor.Arc.fibre_card_le
import Submission.Work.WilE3.Frame.eaEvalC_toC
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

namespace Work.WilE3.Taylor.Grad

open Filter
open scoped Topology

/-!
## The polar points at a level

This file proves `Work.WilE3.Taylor.Grad.polarPointsAtLevel`: along a real analytic arc `γ` through
`y` which lies on the polar (minors) locus of the polar system `polarSys c Φ i₀` of an EA
polynomial `Φ`, the level sets `{Φ = ε}` of the complexified EA polynomial carry, for small
`ε ≠ 0`, at least `m / a` points of the polar locus at which the polar Jacobian is invertible —
where `m = ord₀ (Φ ∘ γ)` and `a = ord₀ (γ - y)`.

The complexification of the arc is the same device as in `Work.WilE3.Taylor.Grad.branchPointsAtLevel`
(the private lemma `ramifiedComplexification`, reproduced here): `γ - y = t ^ a • u t` near `0`, and
complexifying the coordinates of `u` produces a holomorphic arc `σ` with `σ s - σ 0 = s ^ a • v s`
and `v 0 ≠ 0`, agreeing with the complexification of `γ` on the real axis.  The composite
`G = eaEvalC c Φ ∘ σ` is holomorphic at `0` with `G 0 = 0` and `ord₀ G = m`, so the equation
`G = ε` has exactly `m` simple solutions near `0` for small `ε ≠ 0`, all tending to `0`; since `σ`
is at most `a`-to-one near `0` those solutions give at least `m / a` points of the level set
`{eaEvalC c Φ = ε}`, and everything is close to `toC y`.

Two extra pieces of information make these points *polar points*: the (complexified) minor equations
vanish identically in a neighbourhood of `0` (they vanish on the real interval `(0, δ)` along `σ`,
and an analytic germ vanishing on such an interval vanishes identically), and the (complexified)
polar Jacobian determinant is nonzero on a punctured neighbourhood of `0` (it is analytic, and it
cannot be identically zero because its real part is not eventually zero along `γ`).
-/

/-! ## §1. Auxiliary lemmas -/

/-- A punctured-neighbourhood `∀ᶠ` statement is an explicit `ε`-`δ` statement:  if
eventually in `𝓝[≠] 0` the predicate `P` holds, then for all small nonzero `ε` the predicate
holds.  (The converse is not needed.) -/
private lemma punctured_eventually_iff {P : ℂ → Prop}
    (h : ∀ᶠ ε in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, P ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℂ, 0 < ‖ε‖ → ‖ε‖ < δ → P ε := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, hδp⟩ := h
  exact ⟨δ, hδ, fun ε h0 hlt => hδp (by simpa [dist_eq_norm] using hlt) (by simpa using h0)⟩

/-- A complex analytic germ at `0` which vanishes on a right-neighbourhood of `0` in the real axis
vanishes on a complex neighbourhood of `0` (the identity theorem for the real interval). -/
private lemma analyticAt_eventually_eq_zero_of_eventually_eq_zero_on_Ioi {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0)
    (h : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), f (t : ℂ) = 0) :
    f =ᶠ[nhds (0 : ℂ)] 0 := by
  rcases hf.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exact h0
  · exfalso
    have htend : Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhdsWithin (0 : ℂ) ({0}ᶜ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, by
        have hIoi : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), (0 : ℝ) < t :=
          self_mem_nhdsWithin
        filter_upwards [hIoi] with t ht
        simpa using ne_of_gt ht⟩
    have h2 : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), f (t : ℂ) ≠ 0 :=
      htend.eventually hne
    obtain ⟨t, ht⟩ := (h2.and h).exists
    exact ht.1 ht.2

/-- The determinant of a matrix of functions analytic at `0` is analytic at `0`.  (The determinant
is a polynomial in the entries; this is the `Fin k` instance needed below.) -/
private lemma det_analyticAt' {k : ℕ} {f : Fin k → Fin k → ℂ → ℂ}
    (hf : ∀ i j, AnalyticAt ℂ (f i j) 0) :
    AnalyticAt ℂ (fun z => (Matrix.of fun i j => f i j z).det) 0 := by
  have hfun : (fun z => (Matrix.of fun i j => f i j z).det)
      = (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin k))),
          fun z => (↑↑(Equiv.Perm.sign σ) : ℂ) * ∏ i, f (σ i) i z) := by
    ext z
    rw [Finset.sum_apply, Matrix.det_apply']
    simp only [Matrix.of_apply]
  rw [hfun]
  refine Finset.analyticAt_sum _ (fun σ _ => analyticAt_const.mul ?_)
  simpa only [← Finset.prod_apply] using
    (Finset.analyticAt_prod (Finset.univ : Finset (Fin k)) (f := fun i z => f (σ i) i z)
      (fun i _ => hf (σ i) i))

/-- **The complexification of a ramified real analytic arc.**

Let `γ` be a real analytic arc at `0` with `ord_0 (γ - y) = a ≥ 1`.  Then `γ - y` factors as
`t ^ a • u t` near `0` with `u` real analytic at `0` and `u 0 ≠ 0` (the finite order
factorisation `AnalyticAt.analyticOrderNatAt_eq_iff`).  Complexifying the coordinates of `u`
(`Arc.complexify_order`) and setting `σ s := toC y + s ^ a • v s` gives a complex analytic arc `σ`
through the complex point `toC y` which ramifies of order exactly `a` at `0`
(`σ s - σ 0 = s ^ a • v s`, `v 0 ≠ 0`) and agrees with `toC ∘ γ` near `0` on the real axis. -/
private lemma ramifiedComplexification {k : ℕ} {γ : ℝ → Fin k → ℝ} {y : Fin k → ℝ} {a : ℕ}
    (hγ : AnalyticAt ℝ γ 0) (ha : 0 < a)
    (hram : analyticOrderAt (fun t : ℝ => γ t - y) 0 = a) :
    ∃ (σ : ℂ → Fin k → ℂ) (v : ℂ → Fin k → ℂ),
      AnalyticAt ℂ σ 0 ∧ (∀ i, AnalyticAt ℂ (fun s : ℂ => v s i) 0) ∧
      v 0 ≠ 0 ∧ (∀ s : ℂ, σ s - σ 0 = s ^ a • v s) ∧
      σ 0 = Work.WilE3.Frame.toC y ∧
      Filter.Eventually (fun t : ℝ => σ (t : ℂ) = Work.WilE3.Frame.toC (γ t)) (nhds (0 : ℝ)) := by
  have hf : AnalyticAt ℝ (fun t : ℝ => γ t - y) 0 := hγ.sub analyticAt_const
  have hne_top : analyticOrderAt (fun t : ℝ => γ t - y) 0 ≠ ⊤ := by
    rw [hram]; exact ENat.natCast_ne_top a
  have hnat : analyticOrderNatAt (fun t : ℝ => γ t - y) 0 = a := by
    have h := Nat.cast_analyticOrderNatAt (f := fun t : ℝ => γ t - y) (z₀ := (0 : ℝ)) hne_top
    rw [hram] at h
    exact Nat.cast_injective h
  obtain ⟨u, huan, hu0, hufact⟩ := (hf.analyticOrderNatAt_eq_iff hne_top).mp hnat
  -- Complexify the coordinates of `u`.
  have hu_coord : ∀ i : Fin k, AnalyticAt ℝ (fun t : ℝ => u t i) 0 := fun i =>
    ((ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).analyticAt (u 0)).comp huan
  choose F ρ hρpos hFan hFeq _hFord using
    fun i => Work.WilE3.Taylor.Arc.complexify_order (fun t : ℝ => u t i) (hu_coord i)
  obtain ⟨ρ₀, hρ₀pos, hρ₀le⟩ := Work.WilE3.Taylor.Arc.exists_pos_le_all hρpos
  refine ⟨fun s i => (y i : ℂ) + s ^ a * F i s, fun s i => F i s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- analyticity of `σ`
    refine AnalyticAt.pi (f := fun (i : Fin k) (s : ℂ) => (y i : ℂ) + s ^ a * F i s) fun i => ?_
    have hFi : AnalyticAt ℂ (fun s : ℂ => F i s) 0 :=
      hFan i 0 (by rw [Metric.mem_ball, dist_zero_right, norm_zero]; exact hρpos i)
    exact analyticAt_const.add ((analyticAt_id.pow a).mul hFi)
  · -- analyticity of `v`
    intro i
    exact hFan i 0 (by rw [Metric.mem_ball, dist_zero_right, norm_zero]; exact hρpos i)
  · -- `v 0 ≠ 0`
    intro hcontra
    obtain ⟨i, hi⟩ : ∃ i : Fin k, u 0 i ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hu0 (funext h)
    have hFi0 : F i 0 = ((u 0 i : ℝ) : ℂ) := hFeq i 0 (by rw [abs_zero]; exact hρpos i)
    have hz : F i 0 = 0 := congr_fun hcontra i
    rw [hFi0] at hz
    exact hi (Complex.ofReal_eq_zero.mp hz)
  · -- the ramification identity, valid for every `s`
    intro s
    funext i
    show ((y i : ℂ) + s ^ a * F i s) - ((y i : ℂ) + (0 : ℂ) ^ a * F i 0) = s ^ a * F i s
    rw [zero_pow ha.ne', zero_mul, add_zero]
    ring
  · -- `σ 0 = toC y`
    funext i
    show (y i : ℂ) + (0 : ℂ) ^ a * F i 0 = (y i : ℂ)
    rw [zero_pow ha.ne', zero_mul, add_zero]
  · -- agreement with the complexification of `γ` near `0`
    filter_upwards [hufact, Metric.ball_mem_nhds (0 : ℝ) hρ₀pos] with t hfact ht
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    funext i
    show (y i : ℂ) + (t : ℂ) ^ a * F i (t : ℂ) = ((γ t) i : ℂ)
    have hFi : F i (t : ℂ) = ((u t i : ℝ) : ℂ) := hFeq i t (lt_of_lt_of_le ht (hρ₀le i))
    have hfacti : γ t i - y i = t ^ a * u t i := by
      have h := congr_fun hfact i
      simpa [Pi.smul_apply, smul_eq_mul, sub_zero] using h
    rw [hFi]
    have hcast : (y i : ℂ) + (t : ℂ) ^ a * ((u t i : ℝ) : ℂ)
        = (((y i) + t ^ a * u t i : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast]
    congr 1
    linarith

/-! ## §2. The main theorem -/

theorem polarPointsAtLevel {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (Φ : WilkiesDesign.E.EAPoly k r) (y : Fin k → ℝ) (γ : ℝ → Fin k → ℝ) (i₀ : Fin k)
    {m a : ℕ}
    (hγ : AnalyticAt ℝ γ 0) (hγ0 : γ 0 = y) (ha : 0 < a) (hm : 0 < m)
    (hram : analyticOrderAt (fun t : ℝ => γ t - y) 0 = a)
    (hord : analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) 0 = m)
    (hne : ¬ (γ =ᶠ[nhds (0 : ℝ)] fun _ => y))
    (hminors : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i : Fin k, i ≠ i₀ →
      WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.polarSys c Φ i₀ i) (γ t) = 0)
    (hdet : ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (Matrix.of fun i j => WilkiesDesign.E.eaEval c
        (WilkiesDesign.E.eaD c j (Work.WilE3.Taylor.polarSys c Φ i₀ i)) (γ t)).det = 0) :
    ∃ (S : ℂ → Finset (Fin k → ℂ)) (ρ : ℂ → ℝ),
      (∀ ε : ℂ, 0 < ρ ε) ∧
      Filter.Tendsto ρ (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds 0) ∧
      (∀ᶠ ε in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ,
        (∀ z ∈ S ε, Work.WilE3.eaEvalC c Φ z = ε) ∧
        (∀ z ∈ S ε, ∀ i : Fin k, i ≠ i₀ →
          Work.WilE3.eaEvalC c (Work.WilE3.Taylor.polarSys c Φ i₀ i) z = 0) ∧
        (∀ z ∈ S ε, (Matrix.of fun i j => Work.WilE3.eaEvalC c
          (WilkiesDesign.E.eaD c j (Work.WilE3.Taylor.polarSys c Φ i₀ i)) z).det ≠ 0) ∧
        m ≤ a * (S ε).card ∧
        (∀ z ∈ S ε, ‖z - Work.WilE3.Frame.toC y‖ < ρ ε)) := by
  classical
  -- The complexified ramified arc through `y`.
  obtain ⟨σ, v, hσan, hvan, hv0, hramσ, hσ0, hagree⟩ :=
    ramifiedComplexification (y := y) hγ ha hram
  -- The composite `G = eaEvalC c Φ ∘ σ`.
  set G : ℂ → ℂ := fun s => Work.WilE3.eaEvalC c Φ (σ s) with hGdef
  have hGan : AnalyticAt ℂ G 0 :=
    (Work.WilE3.API.eaEvalC_fderiv_analytic c Φ (σ 0)).1.comp hσan
  have hgReal : AnalyticAt ℝ (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) 0 :=
    (Work.WilE3.eaEval_analytic c Φ (γ 0)).comp hγ
  have hGord : analyticOrderAt G 0 = m := by
    rw [← Work.WilE3.Taylor.Arc.order_restrict G hGan]
    rw [analyticOrderAt_congr (f := fun t : ℝ => G (t : ℂ))
      (g := fun t : ℝ => ((WilkiesDesign.E.eaEval c Φ (γ t) : ℝ) : ℂ)) ?_]
    · rw [Work.WilE3.Taylor.Arc.ofReal_order hgReal, hord]
    · filter_upwards [hagree] with t ht
      simp only [hGdef]
      rw [ht, Work.WilE3.Frame.eaEvalC_toC]
  have hG0 : G 0 = 0 := by
    refine apply_eq_zero_of_analyticOrderAt_ne_zero (f := G) (z₀ := (0 : ℂ)) ?_
    rw [hGord]
    exact_mod_cast hm.ne'
  -- The complexified minors vanish in a neighbourhood of `0`.
  have hminEv : ∀ᶠ s in nhds (0 : ℂ), ∀ i : Fin k, i ≠ i₀ →
      Work.WilE3.eaEvalC c (Work.WilE3.Taylor.polarSys c Φ i₀ i) (σ s) = 0 := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i = i₀
    · filter_upwards with s
      simp [hi]
    · have hfian : AnalyticAt ℂ (fun s =>
          Work.WilE3.eaEvalC c (Work.WilE3.Taylor.polarSys c Φ i₀ i) (σ s)) 0 :=
        (Work.WilE3.API.eaEvalC_fderiv_analytic c _ (σ 0)).1.comp hσan
      have hz : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          Work.WilE3.eaEvalC c (Work.WilE3.Taylor.polarSys c Φ i₀ i) (σ (t : ℂ)) = 0 := by
        filter_upwards [hminors, hagree.filter_mono nhdsWithin_le_nhds] with t ht hagt
        rw [hagt, Work.WilE3.Frame.eaEvalC_toC, ht i hi]
        simp
      have h0 := analyticAt_eventually_eq_zero_of_eventually_eq_zero_on_Ioi hfian hz
      filter_upwards [h0] with s hs
      intro _
      exact hs
  -- The complexified polar Jacobian determinant.
  set D : ℂ → ℂ := fun s => (Matrix.of fun i j =>
      Work.WilE3.eaEvalC c (WilkiesDesign.E.eaD c j (Work.WilE3.Taylor.polarSys c Φ i₀ i))
        (σ s)).det with hDdef
  have hDan : AnalyticAt ℂ D 0 := by
    rw [hDdef]
    exact det_analyticAt' (fun i j =>
      (Work.WilE3.API.eaEvalC_fderiv_analytic c _ (σ 0)).1.comp hσan)
  have hDne : ¬ D =ᶠ[nhds (0 : ℂ)] 0 := by
    intro hD0
    apply hdet
    have h1 : ∀ᶠ t : ℝ in nhds (0 : ℝ), D (t : ℂ) = 0 :=
      Complex.continuous_ofReal.continuousAt.tendsto.eventually hD0
    have h2 : ∀ᶠ t : ℝ in nhds (0 : ℝ), D (t : ℂ) = (((Matrix.of fun i j =>
        WilkiesDesign.E.eaEval c
          (WilkiesDesign.E.eaD c j (Work.WilE3.Taylor.polarSys c Φ i₀ i)) (γ t)).det : ℝ) : ℂ) := by
      filter_upwards [hagree] with t ht
      have hDval : D (t : ℂ) = (Matrix.of fun i j => Work.WilE3.eaEvalC c
          (WilkiesDesign.E.eaD c j (Work.WilE3.Taylor.polarSys c Φ i₀ i)) (σ (t : ℂ))).det := by
        rw [hDdef]
      rw [hDval, ht]
      have hmat : (Matrix.of fun i j => Work.WilE3.eaEvalC c
            (WilkiesDesign.E.eaD c j (Work.WilE3.Taylor.polarSys c Φ i₀ i))
            (Work.WilE3.Frame.toC (γ t)))
          = (Matrix.of fun i j => WilkiesDesign.E.eaEval c
            (WilkiesDesign.E.eaD c j (Work.WilE3.Taylor.polarSys c Φ i₀ i)) (γ t)).map
            (algebraMap ℝ ℂ) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.of_apply, Work.WilE3.Frame.eaEvalC_toC]
        rfl
      rw [hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.coe_algebraMap]
    filter_upwards [h1.filter_mono nhdsWithin_le_nhds,
      h2.filter_mono nhdsWithin_le_nhds] with t ht1 ht2
    rw [ht2] at ht1
    exact Complex.ofReal_eq_zero.mp ht1
  obtain ⟨rm, hrm, hrmprop⟩ := Metric.mem_nhds_iff.mp hminEv
  obtain ⟨rD, hrD, hDprop⟩ := Work.WilE3.Taylor.analyticAt_punctured_ne_zero_C hDan hDne
  -- The `m` simple solutions of `G = ε` near `0`.
  obtain ⟨r₁, δ₁, hr₁, hδ₁, hcount, hconv⟩ :=
    Work.WilE3.Frame.exists_card_solutions_simple_tendsto hGan hG0 m hGord
  -- `σ` is at most `a`-to-one near `0`.
  obtain ⟨δc, hδc, hδcprop⟩ :=
    Work.WilE3.Taylor.Arc.card_le_mul_card_image (σ := σ) (v := v) ha
      (AnalyticAt.pi hvan) hv0 hramσ
  -- A common radius for all the requirements.
  set rstar : ℝ := min (min r₁ δc) (min rm rD) with hrstardef
  have hrstarp : 0 < rstar := lt_min (lt_min hr₁ hδc) (lt_min hrm hrD)
  have hle_r1 : rstar ≤ r₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hle_dc : rstar ≤ δc := le_trans (min_le_left _ _) (min_le_right _ _)
  have hle_rm : rstar ≤ rm := le_trans (min_le_right _ _) (min_le_left _ _)
  have hle_rD : rstar ≤ rD := le_trans (min_le_right _ _) (min_le_right _ _)
  -- All solutions in the disc of radius `r₁` are within `rstar` of `0`.
  obtain ⟨δ₂, hδ₂, hδ₂prop⟩ := punctured_eventually_iff (hconv rstar hrstarp)
  set δ : ℝ := min δ₁ δ₂ with hδdef
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  -- The family of polar points: the `σ`-images of the `m` simple solutions of `G = ε`.
  let Sfun : ℂ → Finset (Fin k → ℂ) := fun ε =>
    if h : 0 < ‖ε‖ ∧ ‖ε‖ < δ₁ then (Classical.choose (hcount ε h.1 h.2)).image σ else ∅
  let ρ : ℂ → ℝ := fun ε =>
    if 0 < ‖ε‖ then ‖ε‖ + ∑ z ∈ Sfun ε, ‖z - Work.WilE3.Frame.toC y‖ else 1
  have hSfun_eq : ∀ (ε : ℂ) (h : 0 < ‖ε‖ ∧ ‖ε‖ < δ₁),
      Sfun ε = (Classical.choose (hcount ε h.1 h.2)).image σ := by
    intro ε h
    simp only [Sfun]
    exact dif_pos h
  have hρeq : ∀ (ε : ℂ), 0 < ‖ε‖ →
      ρ ε = ‖ε‖ + ∑ z ∈ Sfun ε, ‖z - Work.WilE3.Frame.toC y‖ := by
    intro ε hε
    simp only [ρ]
    exact dif_pos hε
  -- Positivity of `ρ`.
  have hρpos : ∀ ε : ℂ, 0 < ρ ε := by
    intro ε
    by_cases h : 0 < ‖ε‖
    · rw [hρeq ε h]
      have hnn : 0 ≤ ∑ z ∈ Sfun ε, ‖z - Work.WilE3.Frame.toC y‖ :=
        Finset.sum_nonneg (fun z _ => norm_nonneg _)
      linarith
    · have h1 : ρ ε = 1 := by
        simp only [ρ]
        exact dif_neg h
      rw [h1]
      norm_num
  -- The sum of the distances tends to `0`, hence so does `ρ`.
  have hsum_tendsto : Tendsto (fun ε => ∑ z ∈ Sfun ε, ‖z - Work.WilE3.Frame.toC y‖)
      (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds 0) := by
    rw [tendsto_order]
    refine ⟨?_, ?_⟩
    · intro b hb
      filter_upwards with ε
      exact lt_of_lt_of_le hb (Finset.sum_nonneg (fun z _ => norm_nonneg _))
    · intro b hb
      -- a strictly smaller target for every individual distance
      set η : ℝ := b / ((m : ℝ) + 1) with hηdef
      have hηpos : 0 < η := by
        rw [hηdef]
        positivity
      -- a radius around `0` on which `σ` stays within `η` of `σ 0 = toC y`
      have hrσ : ∃ r : ℝ, 0 < r ∧ ∀ s : ℂ, ‖s‖ < r → ‖σ s - Work.WilE3.Frame.toC y‖ < η := by
        have hpre : σ ⁻¹' Metric.ball (σ 0) η ∈ nhds (0 : ℂ) :=
          hσan.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (σ 0) hηpos)
        obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hpre
        refine ⟨r, hr, fun s hs => ?_⟩
        have h2 : σ s ∈ Metric.ball (σ 0) η :=
          hrsub (by simpa [Metric.mem_ball, dist_zero_right] using hs)
        rwa [Metric.mem_ball, dist_eq_norm, hσ0] at h2
      obtain ⟨rσ, hrσpos, hrσprop⟩ := hrσ
      -- all solutions stay in the ball of radius `min rσ rstar`
      obtain ⟨δ₃, hδ₃, hδ₃prop⟩ :=
        punctured_eventually_iff (hconv (min rσ rstar) (lt_min hrσpos hrstarp))
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (lt_min hδ hδ₃)] with ε hε hne
      rw [Metric.mem_ball, dist_zero_right] at hε
      have hε0 : 0 < ‖ε‖ := by rw [norm_pos_iff]; simpa using hne
      have hεδ : ‖ε‖ < δ := lt_of_lt_of_le hε (min_le_left _ _)
      have hεδ₁ : ‖ε‖ < δ₁ := lt_of_lt_of_le hεδ (min_le_left _ _)
      have hεδ₃ : ‖ε‖ < δ₃ := lt_of_lt_of_le hε (min_le_right _ _)
      obtain ⟨hscard, hsprop, _hsall⟩ := Classical.choose_spec (hcount ε hε0 hεδ₁)
      have hbnd : ∀ z ∈ Sfun ε, ‖z - Work.WilE3.Frame.toC y‖ < η := by
        intro z hz
        rw [hSfun_eq ε ⟨hε0, hεδ₁⟩, Finset.mem_image] at hz
        obtain ⟨s, hs, rfl⟩ := hz
        have hs1 : ‖s‖ < r₁ := by simpa using (hsprop s hs).2.1
        have hs3 : ‖s‖ < min rσ rstar :=
          by simpa using hδ₃prop ε hε0 hεδ₃ s (hsprop s hs).1 (by simpa using hs1)
        exact hrσprop s (lt_of_lt_of_le hs3 (min_le_left _ _))
      have hcard : (Sfun ε).card ≤ m := by
        rw [hSfun_eq ε ⟨hε0, hεδ₁⟩]
        exact (Finset.card_image_le).trans_eq hscard
      calc ∑ z ∈ Sfun ε, ‖z - Work.WilE3.Frame.toC y‖
          ≤ ∑ _z ∈ Sfun ε, η := Finset.sum_le_sum (fun z hz => le_of_lt (hbnd z hz))
        _ = (Sfun ε).card * η := by rw [Finset.sum_const, nsmul_eq_mul]
        _ < b := by
            have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
            have hcard' : ((Sfun ε).card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hcard
            have h1 : ((Sfun ε).card : ℝ) * η ≤ (m : ℝ) * η :=
              mul_le_mul_of_nonneg_right hcard' hηpos.le
            have h2 : (m : ℝ) * (b / ((m : ℝ) + 1)) < b := by
              have hrat : (m : ℝ) / ((m : ℝ) + 1) < 1 := by
                rw [div_lt_one hm1]; linarith
              calc (m : ℝ) * (b / ((m : ℝ) + 1)) = b * ((m : ℝ) / ((m : ℝ) + 1)) := by
                    ring
                _ < b * 1 := mul_lt_mul_of_pos_left hrat hb
                _ = b := mul_one b
            have h3 : (m : ℝ) * η = (m : ℝ) * (b / ((m : ℝ) + 1)) := by rw [hηdef]
            linarith [h1, h2, h3]
  -- The eventual conclusion.
  have hmain : ∀ᶠ ε in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ,
      (∀ z ∈ Sfun ε, Work.WilE3.eaEvalC c Φ z = ε) ∧
      (∀ z ∈ Sfun ε, ∀ i : Fin k, i ≠ i₀ →
        Work.WilE3.eaEvalC c (Work.WilE3.Taylor.polarSys c Φ i₀ i) z = 0) ∧
      (∀ z ∈ Sfun ε, (Matrix.of fun i j => Work.WilE3.eaEvalC c
        (WilkiesDesign.E.eaD c j (Work.WilE3.Taylor.polarSys c Φ i₀ i)) z).det ≠ 0) ∧
      m ≤ a * (Sfun ε).card ∧
      (∀ z ∈ Sfun ε, ‖z - Work.WilE3.Frame.toC y‖ < ρ ε) := by
    have hc0 : ∀ᶠ ε in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, 0 < ‖ε‖ := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [norm_pos_iff]
      simpa using hε
    have hc1 : ∀ᶠ ε in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, ‖ε‖ < δ₁ := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ₁] with ε hε _
      rwa [Metric.mem_ball, dist_zero_right] at hε
    have hc2 : ∀ᶠ ε in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ,
        ∀ z : ℂ, G z = ε → ‖z‖ < r₁ → ‖z‖ < rstar := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ₂] with ε hε hne
      rw [Metric.mem_ball, dist_zero_right] at hε
      intro z hz hzr
      have hz' := hδ₂prop ε (by rw [norm_pos_iff]; simpa using hne) hε z hz (by simpa using hzr)
      simpa using hz'
    filter_upwards [hc0, hc1, hc2] with ε hε0 hεδ₁ hconvv
    have hSfunε := hSfun_eq ε ⟨hε0, hεδ₁⟩
    obtain ⟨hscard, hsprop, hsall⟩ := Classical.choose_spec (hcount ε hε0 hεδ₁)
    have hsn : ∀ s ∈ Classical.choose (hcount ε hε0 hεδ₁), ‖s‖ < rstar := fun s hs =>
      hconvv s (hsprop s hs).1 (by simpa using (hsprop s hs).2.1)
    have hεne : ε ≠ 0 := by rw [norm_pos_iff] at hε0; exact hε0
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- the level set equation
      intro z hz
      rw [hSfunε, Finset.mem_image] at hz
      obtain ⟨s, hs, rfl⟩ := hz
      exact (hsprop s hs).1
    · -- the polar minors vanish
      intro z hz i hi
      rw [hSfunε, Finset.mem_image] at hz
      obtain ⟨s, hs, rfl⟩ := hz
      exact hrmprop (by rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le (hsn s hs) hle_rm)
        i hi
    · -- the polar Jacobian is invertible
      intro z hz
      rw [hSfunε, Finset.mem_image] at hz
      obtain ⟨s, hs, rfl⟩ := hz
      have hs0 : 0 < ‖s‖ := by
        rw [norm_pos_iff]
        intro hs0'
        have : G s = 0 := by rw [hs0']; exact hG0
        rw [(hsprop s hs).1] at this
        exact hεne this
      have h := hDprop s hs0 (lt_of_lt_of_le (hsn s hs) hle_rD)
      rwa [hDdef] at h
    · -- the cardinality bound
      have hcard : (Classical.choose (hcount ε hε0 hεδ₁)).card ≤
          a * ((Classical.choose (hcount ε hε0 hεδ₁)).image σ).card :=
        hδcprop _ (fun s hs => lt_of_lt_of_le (hsn s hs) hle_dc)
      calc m = (Classical.choose (hcount ε hε0 hεδ₁)).card := hscard.symm
        _ ≤ a * ((Classical.choose (hcount ε hε0 hεδ₁)).image σ).card := hcard
        _ = a * (Sfun ε).card := by rw [hSfunε]
    · -- the points are close to `toC y`
      intro z hz
      rw [hρeq ε hε0]
      have hle : ‖z - Work.WilE3.Frame.toC y‖ ≤ ∑ z' ∈ Sfun ε, ‖z' - Work.WilE3.Frame.toC y‖ :=
        Finset.single_le_sum (f := fun z' => ‖z' - Work.WilE3.Frame.toC y‖)
          (fun z' _ => norm_nonneg _) hz
      linarith
  -- Assemble.
  refine ⟨Sfun, ρ, hρpos, ?_, hmain⟩
  have hρevent : ρ =ᶠ[nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ]
      (fun ε => ‖ε‖ + ∑ z ∈ Sfun ε, ‖z - Work.WilE3.Frame.toC y‖) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hρeq ε (by rw [norm_pos_iff]; simpa using hε)
  refine Tendsto.congr' hρevent.symm ?_
  have hnorm : Tendsto (fun ε : ℂ => ‖ε‖) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds 0) := by
    have h := (continuous_norm.continuousAt (x := (0 : ℂ))).tendsto
    simpa using h.mono_left nhdsWithin_le_nhds
  simpa using hnorm.add hsum_tendsto

end Work.WilE3.Taylor.Grad
