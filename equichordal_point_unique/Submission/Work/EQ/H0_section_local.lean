import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.H0_tail_bounded
import Submission.Work.EQ.rel_fibre_analytic_fix
import Submission.Work.EQ.analyticAt_local_inverse
import Submission.Work.EQ.chain_unique_window

/-!
# `H0` is locally an analytic section over the `ψ₁`-plane

We prove `Work.EQ.H0_section_local`: through every point `p` of Rychlik's unbranched connection
surface `H0 a h` there is a radius `ρ > 0` and a continuous family `f` of chains with
`(f u).2.1 = u` and `f p.2.1 = p`, whose every chain coordinate `u ↦ (f u).1 n` and whose
unstable parameter `u ↦ (f u).2.2` are analytic on `ball p.2.1 ρ`, and whose image is a
neighbourhood of `p` in `H0`.

Ingredients:

* `H0_tail_bounded`: on a product-topology neighbourhood of `p` the forward and backward tail
  indices are bounded by `N` resp. `M`; take `K ≥ max N M` so that the window `|k| ≤ K` contains
  both tail levels.
* `chain_unique_window` (colleague's lemma): two chains with the same `ψ₁`, close to `p` on the
  window and with the tails at `N` and `M`, coincide.  This gives the local uniqueness of the
  section and the neighbourhood property.
* the analytic reconstruction: the entry at level `N` is `germC (λ^N ·)`, the entries further back
  are the analytic branches of the relation over the following entry
  (`rel_fibre_analytic_fix`); the branch is pinned down by its value `p.1 j` at `u₀ = p.2.1`, and
  the separation of the two branches propagates the agreement with the family `f` down to `-M`.
* the unstable parameter `ψ₂` is recovered from the entry at level `-M`: the second coordinate of
  `germC` is injective on `ball 0 ρg` (`germC_facts`), so it has an analytic local inverse
  (`analyticAt_local_inverse`).
-/

namespace Work.EQ

open Complex Metric Filter Set
open scoped Topology

noncomputable section

variable {a : ℝ} {h : ℂ → ℂ}

/-! ## Elementary helpers -/

/-- The second coordinate of `ugermC` is the second coordinate of `germC`. -/
@[simp] lemma ugermC_snd (a : ℝ) (h : ℂ → ℂ) (v : ℂ) :
    (ugermC a h v).2 = (germC a h v).2 := by simp [ugermC, eqMirror]

/-- The second coordinate of `germC` is analytic wherever `germC` is. -/
lemma analyticOnNhd_germC_snd {a : ℝ} {h : ℂ → ℂ} {ρ : ℝ}
    (hAn : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρ)) :
    AnalyticOnNhd ℂ (fun u => (germC a h u).2) (Metric.ball (0 : ℂ) ρ) :=
  fun u hu => (analyticAt_snd (p := germC a h u)).comp (hAn u hu)

/-- `eqMirror` is analytic. -/
lemma analyticAt_eqMirror (p : ℂ × ℂ) : AnalyticAt ℂ (fun z : ℂ × ℂ => eqMirror z) p := by
  have h1 : AnalyticAt ℂ (fun z : ℂ × ℂ => -z.1) p := analyticAt_fst.neg
  have h2 : AnalyticAt ℂ (fun z : ℂ × ℂ => z.2) p := analyticAt_snd
  simpa [eqMirror] using h1.prod h2

/-- `ugermC a h ∘ g` is analytic on `s` when `g` maps `s` into the disc of analyticity of
`germC`. -/
lemma analyticOnNhd_ugermC_comp {a : ℝ} {h : ℂ → ℂ} {ρ : ℝ}
    (hAn : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρ))
    {s : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s)
    (hmaps : MapsTo g s (Metric.ball (0 : ℂ) ρ)) :
    AnalyticOnNhd ℂ (fun u => ugermC a h (g u)) s := by
  have hlin : AnalyticOnNhd ℂ (fun z : ℂ × ℂ => eqMirror z) Set.univ :=
    fun z _ => analyticAt_eqMirror z
  have hinner : AnalyticOnNhd ℂ (fun u => germC a h (g u)) s := hAn.comp hg hmaps
  have hcomp : AnalyticOnNhd ℂ (fun u => eqMirror (germC a h (g u))) s :=
    hlin.comp hinner (fun u _ => Set.mem_univ _)
  exact fun u hu => (hcomp u hu).congr (Filter.Eventually.of_forall fun v => by simp [ugermC])

/-- The product-topology window around `p` cut out by the coordinates `|k| ≤ K`. -/
def window (p : ChainData) (K : ℕ) (ε : ℝ) : Set ChainData :=
  {q | (∀ k : ℤ, |k| ≤ (K : ℤ) → ‖q.1 k - p.1 k‖ < ε) ∧ ‖q.2.1 - p.2.1‖ < ε ∧
    ‖q.2.2 - p.2.2‖ < ε}

lemma window_isOpen (p : ChainData) (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    IsOpen (window p K ε) := by
  have hcoord : ∀ k : ℤ, IsOpen {q : ChainData | ‖q.1 k - p.1 k‖ < ε} := by
    intro k
    have hset : {q : ChainData | ‖q.1 k - p.1 k‖ < ε}
        = (fun q : ChainData => q.1 k) ⁻¹' Metric.ball (p.1 k) ε := by
      ext q; simp [Metric.mem_ball, dist_eq_norm]
    rw [hset]
    exact Metric.isOpen_ball.preimage ((continuous_apply k).comp continuous_fst)
  have h1 : IsOpen {q : ChainData | ∀ k : ℤ, |k| ≤ (K : ℤ) → ‖q.1 k - p.1 k‖ < ε} := by
    have hset : {q : ChainData | ∀ k : ℤ, |k| ≤ (K : ℤ) → ‖q.1 k - p.1 k‖ < ε}
        = ⋂ k ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)), {q : ChainData | ‖q.1 k - p.1 k‖ < ε} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_Icc]
      constructor
      · intro h k hk; exact h k (abs_le.mpr hk)
      · intro h k hk; exact h k (abs_le.mp hk)
    rw [hset]
    exact isOpen_biInter_finset fun k _ => hcoord k
  have h2 : IsOpen {q : ChainData | ‖q.2.1 - p.2.1‖ < ε} := by
    have hset : {q : ChainData | ‖q.2.1 - p.2.1‖ < ε}
        = (fun q : ChainData => q.2.1) ⁻¹' Metric.ball p.2.1 ε := by
      ext q; simp [Metric.mem_ball, dist_eq_norm]
    rw [hset]
    exact Metric.isOpen_ball.preimage (continuous_fst.comp continuous_snd)
  have h3 : IsOpen {q : ChainData | ‖q.2.2 - p.2.2‖ < ε} := by
    have hset : {q : ChainData | ‖q.2.2 - p.2.2‖ < ε}
        = (fun q : ChainData => q.2.2) ⁻¹' Metric.ball p.2.2 ε := by
      ext q; simp [Metric.mem_ball, dist_eq_norm]
    rw [hset]
    exact Metric.isOpen_ball.preimage (continuous_snd.comp continuous_snd)
  exact h1.inter (h2.inter h3)

lemma mem_window_self (p : ChainData) (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    p ∈ window p K ε :=
  ⟨fun k _ => by simp [hε], by simp [hε], by simp [hε]⟩

/-- The three-sided triangle inequality for the norm of a difference. -/
lemma norm_sub_le_add {E : Type*} [SeminormedAddCommGroup E] (x y z : E) :
    ‖x - y‖ ≤ ‖x - z‖ + ‖z - y‖ := by
  have := dist_triangle x z y
  rwa [dist_eq_norm, dist_eq_norm, dist_eq_norm] at this

/-- `‖λ^n * v‖ = λ^n * ‖v‖` for `λ = eqLam a ∈ (0,1)`. -/
lemma norm_eqLam_pow_mul {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) (v : ℂ) :
    ‖(eqLam a : ℂ) ^ n * v‖ = (eqLam a) ^ n * ‖v‖ := by
  have hL : 0 < eqLam a := by rw [eqLam]; positivity
  have hnorm : ‖((eqLam a : ℝ) : ℂ)‖ = eqLam a := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hL.le]
  rw [norm_mul, norm_pow, hnorm]

/-- **The branch step.**  Let `f` be a family of chains which, near `u₀`, satisfies the relation
at level `j` against the analytic family `Q`, and let `P` be one of the two analytic branches of
the relation over `Q`, chosen so that `P u₀ = (f u₀).1 j`.  Then `f` agrees with `P` at level `j`
on a neighbourhood of `u₀`. -/
lemma branch_agreement_step {a : ℝ} {j : ℤ} {u₀ : ℂ}
    {Q P Palt : ℂ → ℂ × ℂ} {f : ℂ → ChainData}
    (hfcont : ContinuousAt (fun u => (f u).1 j) u₀)
    (hPan : AnalyticAt ℂ P u₀) (hPaltan : AnalyticAt ℂ Palt u₀) (hPne : P u₀ ≠ Palt u₀)
    (hsol : ∀ᶠ u in 𝓝 u₀, ∀ P' : ℂ × ℂ, EqRelC a P' (Q u) → P' = P u ∨ P' = Palt u)
    (hf0 : (f u₀).1 j = P u₀)
    (hfeq : ∀ᶠ u in 𝓝 u₀, EqRelC a ((f u).1 j) (Q u)) :
    ∀ᶠ u in 𝓝 u₀, (f u).1 j = P u := by
  set d : ℝ := ‖P u₀ - Palt u₀‖ with hddef
  have hdpos : 0 < d := by
    rw [hddef, norm_pos_iff]
    exact sub_ne_zero.mpr hPne
  have evP : ∀ᶠ u in 𝓝 u₀, ‖P u - P u₀‖ < d / 4 := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp hPan.continuousAt (d / 4) (by positivity)
    filter_upwards [Metric.ball_mem_nhds u₀ hδ] with u hu
    simpa [dist_eq_norm] using h hu
  have evPa : ∀ᶠ u in 𝓝 u₀, ‖Palt u - Palt u₀‖ < d / 4 := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp hPaltan.continuousAt (d / 4) (by positivity)
    filter_upwards [Metric.ball_mem_nhds u₀ hδ] with u hu
    simpa [dist_eq_norm] using h hu
  have evf : ∀ᶠ u in 𝓝 u₀, ‖(f u).1 j - (f u₀).1 j‖ < d / 4 := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp hfcont (d / 4) (by positivity)
    filter_upwards [Metric.ball_mem_nhds u₀ hδ] with u hu
    simpa [dist_eq_norm] using h hu
  filter_upwards [hsol, evP, evPa, evf, hfeq] with u hsol_u hPu hPau hfu hrelu
  rcases hsol_u ((f u).1 j) hrelu with h | h
  · exact h
  · exfalso
    have hlow : d / 2 < ‖P u - Palt u‖ := by
      have h3 : d ≤ ‖P u - P u₀‖ + ‖P u - Palt u₀‖ := by
        calc d = ‖P u₀ - Palt u₀‖ := hddef
          _ ≤ ‖P u₀ - P u‖ + ‖P u - Palt u₀‖ := norm_sub_le_add _ _ _
          _ = ‖P u - P u₀‖ + ‖P u - Palt u₀‖ := by rw [norm_sub_rev]
      have h4 : ‖P u - Palt u₀‖ ≤ ‖P u - Palt u‖ + ‖Palt u - Palt u₀‖ :=
        norm_sub_le_add _ _ _
      linarith
    have hup : ‖P u - Palt u‖ < d / 2 := by
      have h3 : ‖P u - Palt u‖ ≤ ‖P u - P u₀‖ + ‖P u₀ - Palt u‖ := norm_sub_le_add _ _ _
      have h4 : ‖P u₀ - Palt u‖ ≤ ‖P u₀ - (f u).1 j‖ + ‖(f u).1 j - Palt u‖ :=
        norm_sub_le_add _ _ _
      have hzero : ‖(f u).1 j - Palt u‖ = 0 := by rw [h, sub_self, norm_zero]
      have hmid : ‖P u₀ - (f u).1 j‖ = ‖(f u).1 j - (f u₀).1 j‖ := by
        rw [norm_sub_rev, ← hf0]
      rw [hzero, hmid, add_zero] at h4
      linarith
    linarith

/-- The `M`-step `germC` tower is injective on `ball v₀ 1` when `λ^M (‖v₀‖ + 1) < ρg`. -/
lemma germC_tower_injOn {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {ρg : ℝ}
    (hAn : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρg))
    (hinj : Set.InjOn (fun u => (germC a h u).2) (Metric.ball (0 : ℂ) ρg))
    {M : ℕ} {v₀ : ℂ} (hM : (eqLam a) ^ M * (‖v₀‖ + 1) < ρg) :
    Set.InjOn (fun v => (germC a h ((eqLam a : ℂ) ^ M * v)).2) (Metric.ball v₀ 1) := by
  have hmaps : MapsTo (fun v : ℂ => (eqLam a : ℂ) ^ M * v) (Metric.ball v₀ 1)
      (Metric.ball (0 : ℂ) ρg) := by
    intro v hv
    rw [Metric.mem_ball, dist_eq_norm] at hv
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_eqLam_pow_mul ha0 ha1]
    have hL0 : 0 ≤ eqLam a := by rw [eqLam]; positivity
    have h2 : ‖v‖ ≤ ‖v₀‖ + 1 := by
      calc ‖v‖ = ‖v₀ + (v - v₀)‖ := by ring_nf
        _ ≤ ‖v₀‖ + ‖v - v₀‖ := norm_add_le _ _
        _ ≤ ‖v₀‖ + 1 := by linarith
    calc (eqLam a) ^ M * ‖v‖ ≤ (eqLam a) ^ M * (‖v₀‖ + 1) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hL0 M)
      _ < ρg := hM
  intro v hv w hw hvw
  have hvρ : (eqLam a : ℂ) ^ M * v ∈ Metric.ball (0 : ℂ) ρg := hmaps hv
  have hwρ : (eqLam a : ℂ) ^ M * w ∈ Metric.ball (0 : ℂ) ρg := hmaps hw
  have h2 : (eqLam a : ℂ) ^ M * v = (eqLam a : ℂ) ^ M * w := hinj hvρ hwρ hvw
  have hL : (eqLam a : ℂ) ^ M ≠ 0 := by
    have h0 : (0 : ℝ) < eqLam a := by rw [eqLam]; positivity
    exact pow_ne_zero M (Complex.ofReal_ne_zero.mpr (ne_of_gt h0))
  exact mul_left_cancel₀ hL h2

/-- **The analytic local inverse of the `M`-step `germC` tower.** -/
lemma germC_tower_local_inverse {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {ρg : ℝ} (hρg : 0 < ρg)
    (hAn : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρg))
    (hinj : Set.InjOn (fun u => (germC a h u).2) (Metric.ball (0 : ℂ) ρg))
    {M : ℕ} {v₀ : ℂ} (hM : (eqLam a) ^ M * (‖v₀‖ + 1) < ρg) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ ψ (Metric.ball ((germC a h ((eqLam a : ℂ) ^ M * v₀)).2) ε) ∧
      ψ ((germC a h ((eqLam a : ℂ) ^ M * v₀)).2) = v₀ ∧
      (∀ w ∈ Metric.ball ((germC a h ((eqLam a : ℂ) ^ M * v₀)).2) ε,
        (germC a h ((eqLam a : ℂ) ^ M * ψ w)).2 = w) ∧
      (∀ w ∈ Metric.ball ((germC a h ((eqLam a : ℂ) ^ M * v₀)).2) ε,
        ψ w ∈ Metric.ball v₀ 1) := by
  have hmaps : MapsTo (fun v : ℂ => (eqLam a : ℂ) ^ M * v) (Metric.ball v₀ 1)
      (Metric.ball (0 : ℂ) ρg) := by
    intro v hv
    rw [Metric.mem_ball, dist_eq_norm] at hv
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_eqLam_pow_mul ha0 ha1]
    have hL0 : 0 ≤ eqLam a := by rw [eqLam]; positivity
    have h2 : ‖v‖ ≤ ‖v₀‖ + 1 := by
      calc ‖v‖ = ‖v₀ + (v - v₀)‖ := by ring_nf
        _ ≤ ‖v₀‖ + ‖v - v₀‖ := norm_add_le _ _
        _ ≤ ‖v₀‖ + 1 := by linarith
    calc (eqLam a) ^ M * ‖v‖ ≤ (eqLam a) ^ M * (‖v₀‖ + 1) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hL0 M)
      _ < ρg := hM
  have hSan : AnalyticOnNhd ℂ (fun v => (germC a h ((eqLam a : ℂ) ^ M * v)).2)
      (Metric.ball v₀ 1) :=
    (analyticOnNhd_germC_snd hAn).comp (fun v _ => analyticAt_const.mul analyticAt_id) hmaps
  have hSinj : Set.InjOn (fun v => (germC a h ((eqLam a : ℂ) ^ M * v)).2)
      (Metric.ball v₀ 1) :=
    germC_tower_injOn ha0 ha1 hAn hinj hM
  obtain ⟨ε, hε, ψ, hψan, hψ0, hψright, hψU⟩ :=
    analyticAt_local_inverse (g := fun v => (germC a h ((eqLam a : ℂ) ^ M * v)).2)
      (U := Metric.ball v₀ 1) Metric.isOpen_ball hSan hSinj
      (Metric.mem_ball_self (x := v₀) zero_lt_one)
  exact ⟨ε, hε, ψ, hψan, hψ0, fun w hw => hψright w hw, hψU⟩


theorem H0_section_local {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∀ p ∈ H0 a h, ∃ ρ : ℝ, 0 < ρ ∧ ∃ f : ℂ → ChainData, f p.2.1 = p ∧
      (∀ u ∈ Metric.ball p.2.1 ρ, f u ∈ H0 a h ∧ (f u).2.1 = u) ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (fun u => (f u).1 n) (Metric.ball p.2.1 ρ)) ∧
      AnalyticOnNhd ℂ (fun u => (f u).2.2) (Metric.ball p.2.1 ρ) ∧
      nhdsWithin p (H0 a h) ≤ Filter.principal (f '' Metric.ball p.2.1 ρ) := by
  intro p hp
  -- ## 0. the data
  have hpcopy : p ∈ H0 a h := hp
  have hpchain : IsChain a h p := isChain_of_mem_H0 hp
  obtain ⟨εH, hεH, f, hfcont, hf0, hfic⟩ := hp
  set u₀ : ℂ := p.2.1 with hu₀
  set v₀ : ℂ := p.2.2 with hv₀
  have hf0u : f u₀ = p := hf0
  have hfic' : ∀ u ∈ Metric.ball u₀ εH, IsChain a h (f u) ∧ (f u).2.1 = u := hfic
  have hcontf : ContinuousAt f u₀ := hfcont.continuousAt (Metric.ball_mem_nhds u₀ hεH)
  have hfH0 : ∀ u ∈ Metric.ball u₀ εH, f u ∈ H0 a h := by
    intro u hu
    have hu' : dist u u₀ < εH := hu
    refine ⟨εH - dist u u₀, by linarith [hu'], f, ?_, ?_, ?_⟩
    · rw [(hfic' u hu).2]
      refine hfcont.mono ?_
      intro v hv
      rw [Metric.mem_ball] at hv ⊢
      calc dist v u₀ ≤ dist v u + dist u u₀ := dist_triangle v u u₀
        _ < (εH - dist u u₀) + dist u u₀ := by linarith
        _ = εH := by ring
    · rw [(hfic' u hu).2]
    · intro v hv
      refine hfic' v ?_
      rw [Metric.mem_ball] at hv ⊢
      have h1 : dist v u < εH - dist u u₀ := by
        rw [(hfic' u hu).2] at hv
        exact hv
      calc dist v u₀ ≤ dist v u + dist u u₀ := dist_triangle v u u₀
        _ < (εH - dist u u₀) + dist u u₀ := by linarith
        _ = εH := by ring
  obtain ⟨ρg, hρg, hAnC, hgerm0, hregC, hinjY, hderY⟩ := germC_facts ha0 ha1 hh
  obtain ⟨N₀, M₀, K₀, εt, hεt, hN₀K₀, hM₀K₀, htb⟩ := H0_tail_bounded ha0 ha1 hh p hpcopy
  have hL0 : 0 < eqLam a := by rw [eqLam]; positivity
  have hL1 : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
  -- ## 1. choose the tail levels `N`, `M` and the window half-width `K`
  have hchoose : ∀ (K' N' : ℕ) (c : ℝ), 0 < c → ∃ N : ℕ, K' ≤ N ∧ N' ≤ N ∧ eqLam a ^ N * c < ρg := by
    intro K' N' c hc
    have hpos : 0 < ρg / c := div_pos hρg hc
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hL1
    refine ⟨max (max K' N') n, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), ?_⟩
    have hle : eqLam a ^ max (max K' N') n ≤ eqLam a ^ n :=
      pow_le_pow_of_le_one hL0.le hL1.le (le_max_right _ _)
    have h2 : eqLam a ^ max (max K' N') n * c ≤ eqLam a ^ n * c :=
      mul_le_mul_of_nonneg_right hle hc.le
    have h3 : eqLam a ^ n * c < ρg := by
      rw [lt_div_iff₀ hc] at hn
      linarith
    linarith
  obtain ⟨N, hNK₀, hN₀N, hNbig⟩ := hchoose K₀ N₀ (‖u₀‖ + 1) (by positivity)
  obtain ⟨M, hMK₀, hM₀M, hMbig⟩ := hchoose K₀ M₀ (‖v₀‖ + 1) (by positivity)
  set K : ℕ := max N M with hKdef
  have hN_le_K : N ≤ K := le_max_left _ _
  have hM_le_K : M ≤ K := le_max_right _ _
  have hKlarge : ∀ k : ℤ, |k| ≤ (K₀ : ℤ) → |k| ≤ (K : ℤ) :=
    fun k hk => le_trans hk (by exact_mod_cast le_trans hNK₀ hN_le_K)
  -- ## 2. the tail-window and its radius
  have hWopen : IsOpen (window p K εt) := window_isOpen p K hεt
  have hpW : p ∈ window p K εt := mem_window_self p K hεt
  have hpre : f ⁻¹' (window p K εt) ∈ 𝓝 u₀ :=
    hcontf (hWopen.mem_nhds (by rw [hf0u]; exact hpW))
  obtain ⟨ρw, hρw, hρwsub⟩ := Metric.mem_nhds_iff.mp hpre
  set ρ₁ : ℝ := min (min ρw 1) εH with hρ₁def
  have hρ₁pos : 0 < ρ₁ := lt_min (lt_min hρw one_pos) hεH
  have hρ₁ρw : ρ₁ ≤ ρw := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ₁1 : ρ₁ ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ₁εH : ρ₁ ≤ εH := min_le_right _ _
  have hptail : (∀ n : ℕ, N ≤ n → p.1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * p.2.1)) ∧
      (∀ n : ℕ, M ≤ n → p.1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * p.2.2)) := by
    obtain ⟨t1, t2⟩ := htb p hpcopy (fun k _ => by simp [hεt]) (by simp [hεt]) (by simp [hεt])
    exact ⟨fun n hn => t1 n (le_trans hN₀N hn), fun n hn => t2 n (le_trans hM₀M hn)⟩
  have htailf : ∀ u ∈ Metric.ball u₀ ρ₁,
      (∀ n : ℕ, N ≤ n → (f u).1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * u)) ∧
      (∀ n : ℕ, M ≤ n → (f u).1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * (f u).2.2)) := by
    intro u hu
    have huH0 : f u ∈ H0 a h := hfH0 u (lt_of_lt_of_le hu hρ₁εH)
    have hw : f u ∈ window p K εt := hρwsub (lt_of_lt_of_le hu hρ₁ρw)
    have hψ1 : (f u).2.1 = u := (hfic' u (lt_of_lt_of_le hu hρ₁εH)).2
    obtain ⟨t1, t2⟩ := htb (f u) huH0 (fun k hk => hw.1 k (hKlarge k hk)) hw.2.1 hw.2.2
    refine ⟨fun n hn => ?_, fun n hn => ?_⟩
    · rw [hψ1] at t1
      exact t1 n (le_trans hN₀N hn)
    · exact t2 n (le_trans hM₀M hn)
  have hchainf : ∀ u ∈ Metric.ball u₀ ρ₁, IsChain a h (f u) :=
    fun u hu => (hfic' u (lt_of_lt_of_le hu hρ₁εH)).1
  have hψ1f : ∀ u ∈ Metric.ball u₀ ρ₁, (f u).2.1 = u :=
    fun u hu => (hfic' u (lt_of_lt_of_le hu hρ₁εH)).2
  -- ## 3. the analytic entries of the window, by downward induction
  set L : ℕ := N + M with hLdef
  have hP : ∀ k : ℕ, k ≤ L → ∃ (Φ : ℕ → ℂ → ℂ × ℂ) (ρ : ℝ), 0 < ρ ∧ ρ ≤ ρ₁ ∧
      (∀ j : ℕ, j ≤ k → AnalyticOnNhd ℂ (Φ j) (Metric.ball u₀ ρ)) ∧
      (∀ j : ℕ, j ≤ k → Φ j u₀ = p.1 ((N : ℤ) - (j : ℤ))) ∧
      (∀ j : ℕ, j ≤ k → ∀ u ∈ Metric.ball u₀ ρ, (f u).1 ((N : ℤ) - (j : ℤ)) = Φ j u) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun _ u => germC a h ((eqLam a : ℂ) ^ N * u), ρ₁, hρ₁pos, le_rfl, ?_, ?_, ?_⟩
      · intro j hj
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
        subst hj0
        have hmaps : MapsTo (fun u : ℂ => (eqLam a : ℂ) ^ N * u) (Metric.ball u₀ ρ₁)
            (Metric.ball (0 : ℂ) ρg) := by
          intro u hu
          rw [Metric.mem_ball, dist_eq_norm] at hu
          rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_eqLam_pow_mul ha0 ha1]
          have h2 : ‖u‖ ≤ ‖u₀‖ + 1 := by
            calc ‖u‖ = ‖u₀ + (u - u₀)‖ := by ring_nf
              _ ≤ ‖u₀‖ + ‖u - u₀‖ := norm_add_le _ _
              _ ≤ ‖u₀‖ + 1 := by linarith [lt_of_lt_of_le hu hρ₁1]
          calc (eqLam a) ^ N * ‖u‖ ≤ (eqLam a) ^ N * (‖u₀‖ + 1) :=
                mul_le_mul_of_nonneg_left h2 (pow_nonneg hL0.le N)
            _ < ρg := hNbig
        exact hAnC.comp (fun u _ => analyticAt_const.mul analyticAt_id) hmaps
      · intro j hj
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
        subst hj0
        simp only [Nat.cast_zero, sub_zero]
        exact (hptail.1 N le_rfl).symm
      · intro j hj u hu
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
        subst hj0
        simp only [Nat.cast_zero, sub_zero]
        exact (htailf u hu).1 N le_rfl
    | succ k ih =>
      intro hk
      have hkL : k ≤ L := by omega
      obtain ⟨Φ, ρ, hρ, hρρ₁, han, hval, hagr⟩ := ih hkL
      set jj : ℤ := (N : ℤ) - (k : ℤ) - 1 with hjj
      have hjj1 : jj + 1 = (N : ℤ) - (k : ℤ) := by rw [hjj]; ring
      set Q : ℂ → ℂ × ℂ := Φ k with hQ
      have hQan : AnalyticAt ℂ Q u₀ := han k le_rfl u₀ (Metric.mem_ball_self hρ)
      have hQ0 : Q u₀ = p.1 (jj + 1) := by
        rw [hQ, hjj1]
        exact hval k le_rfl
      have hne : bsq (subO1 a (Q u₀)) ≠ 0 := by
        rw [hQ0]
        exact (hpchain.1 jj).2.2
      obtain ⟨P₁, P₂, hP₁an, hP₂an, hP₁₂ne, hrel12, hsol12⟩ :=
        rel_fibre_analytic_fix (a := a) (Q := Q) hQan hne
      have hw0 : EqRelC a (p.1 jj) (Q u₀) := by
        rw [hQ0]
        exact (hpchain.1 jj).1
      have hsol0 := hsol12.self_of_nhds
      set P : ℂ → ℂ × ℂ := if p.1 jj = P₁ u₀ then P₁ else P₂ with hPdef
      set Palt : ℂ → ℂ × ℂ := if p.1 jj = P₁ u₀ then P₂ else P₁ with hPaltdef
      have hPan : AnalyticAt ℂ P u₀ := by
        rw [hPdef]; split_ifs with hh
        · exact hP₁an
        · exact hP₂an
      have hPaltan : AnalyticAt ℂ Palt u₀ := by
        rw [hPaltdef]; split_ifs with hh
        · exact hP₂an
        · exact hP₁an
      have hPval : P u₀ = p.1 jj := by
        rw [hPdef]; split_ifs with hh
        · exact hh.symm
        · rcases hsol0 (p.1 jj) hw0 with h | h
          · exact absurd h hh
          · exact h.symm
      have hPnep : P u₀ ≠ Palt u₀ := by
        intro hcon
        rw [hPdef] at hcon
        rw [hPaltdef] at hcon
        split_ifs at hcon with hh
        · exact hP₁₂ne hcon
        · exact hP₁₂ne hcon.symm
      have hPsol : ∀ᶠ u in 𝓝 u₀, ∀ P' : ℂ × ℂ, EqRelC a P' (Q u) → P' = P u ∨ P' = Palt u := by
        filter_upwards [hsol12] with u hu
        intro P' hP'
        rcases hu P' hP' with h | h
        · rw [hPdef, hPaltdef]
          split_ifs with hh
          · exact Or.inl h
          · exact Or.inr h
        · rw [hPdef, hPaltdef]
          split_ifs with hh
          · exact Or.inr h
          · exact Or.inl h
      have hfeqe : ∀ᶠ u in 𝓝 u₀, EqRelC a ((f u).1 jj) (Q u) := by
        filter_upwards [Metric.ball_mem_nhds u₀ hρ] with u hu
        have hrel := (hchainf u (lt_of_lt_of_le hu hρρ₁)).1 jj
        have hag := hagr k le_rfl u hu
        rw [← hjj1] at hag
        rw [hag] at hrel
        exact hrel.1
      have hfu0 : (f u₀).1 jj = P u₀ := by
        rw [hf0u, hPval]
      have hcoord : ContinuousAt (fun u => (f u).1 jj) u₀ :=
        (((continuous_apply jj).comp continuous_fst).continuousAt).comp hcontf
      have hagree_event := branch_agreement_step (a := a) (j := jj)
        (Q := Q) (P := P) (Palt := Palt) (f := f) hcoord hPan hPaltan hPnep hPsol hfu0 hfeqe
      obtain ⟨ρ', hρ'pos, hρ'sub⟩ := Metric.mem_nhds_iff.mp hagree_event
      obtain ⟨ρa, hρapos, hρaan⟩ := hPan.exists_ball_analyticOnNhd
      set ρnext : ℝ := min (min ρ' ρa) ρ with hρnextdef
      have hρnextpos : 0 < ρnext := lt_min (lt_min hρ'pos hρapos) hρ
      have hρnextρ : ρnext ≤ ρ := min_le_right _ _
      have hρnextρ' : ρnext ≤ ρ' := le_trans (min_le_left _ _) (min_le_left _ _)
      have hρnextρa : ρnext ≤ ρa := le_trans (min_le_left _ _) (min_le_right _ _)
      have hρnextρ₁ : ρnext ≤ ρ₁ := le_trans hρnextρ hρρ₁
      refine ⟨fun j => if j = k + 1 then P else Φ j, ρnext, hρnextpos, hρnextρ₁, ?_, ?_, ?_⟩
      · intro j hj
        rcases eq_or_ne j (k + 1) with h | h
        · subst h
          simp only [if_pos rfl]
          exact hρaan.mono (Metric.ball_subset_ball hρnextρa)
        · simp only [if_neg h]
          exact (han j (by omega)).mono (Metric.ball_subset_ball hρnextρ)
      · intro j hj
        rcases eq_or_ne j (k + 1) with h | h
        · subst h
          simp only [if_pos rfl]
          have hidx : (N : ℤ) - (((k + 1 : ℕ)) : ℤ) = jj := by
            rw [hjj]; push_cast; ring
          rw [hidx]
          exact hPval
        · simp only [if_neg h]
          exact hval j (by omega)
      · intro j hj u hu
        rcases eq_or_ne j (k + 1) with h | h
        · subst h
          simp only [if_pos rfl]
          have hidx : (N : ℤ) - (((k + 1 : ℕ)) : ℤ) = jj := by
            rw [hjj]; push_cast; ring
          rw [hidx]
          exact hρ'sub (lt_of_lt_of_le hu hρnextρ')
        · simp only [if_neg h]
          exact hagr j (by omega) u (lt_of_lt_of_le hu hρnextρ)
  obtain ⟨Φb, ρb, hρbpos, hρbρ₁, hanb, hvalb, hagrb⟩ := hP L le_rfl
  -- ## 4. the unstable parameter `ψ₂` as an analytic function of `ψ₁`
  obtain ⟨εψ, hεψ, ψ, hψan, hψ0, hψright, hψU⟩ :=
    germC_tower_local_inverse (a := a) (h := h) ha0 ha1 (ρg := ρg) hρg hAnC hinjY hMbig
  have hSinj : Set.InjOn (fun v => (germC a h ((eqLam a : ℂ) ^ M * v)).2)
      (Metric.ball v₀ 1) := germC_tower_injOn ha0 ha1 hAnC hinjY hMbig
  have hΦLval : (Φb L u₀).2 = (germC a h ((eqLam a : ℂ) ^ M * v₀)).2 := by
    have hidx : (N : ℤ) - (L : ℤ) = -(M : ℤ) := by rw [hLdef]; push_cast; ring
    rw [hvalb L le_rfl, hidx, hptail.2 M le_rfl]
    simp only [ugermC, eqMirror]
    rw [hv₀]
  set Ψ : ℂ → ℂ := fun u => ψ ((Φb L u).2) with hΨdef
  have hΨan : AnalyticAt ℂ Ψ u₀ := by
    have hinner : AnalyticAt ℂ (fun u => (Φb L u).2) u₀ :=
      (analyticAt_snd (p := Φb L u₀)).comp (hanb L le_rfl u₀ (Metric.mem_ball_self hρbpos))
    have hmem : (fun u => (Φb L u).2) u₀ ∈
        Metric.ball ((germC a h ((eqLam a : ℂ) ^ M * v₀)).2) εψ := by
      show (Φb L u₀).2 ∈ Metric.ball ((germC a h ((eqLam a : ℂ) ^ M * v₀)).2) εψ
      rw [hΦLval]
      exact Metric.mem_ball_self hεψ
    have hψpt : AnalyticAt ℂ ψ ((fun u : ℂ => (Φb L u).2) u₀) := hψan _ hmem
    have hcomp : AnalyticAt ℂ (fun u : ℂ => ψ ((Φb L u).2)) u₀ :=
      AnalyticAt.comp (g := ψ) (f := fun u : ℂ => (Φb L u).2) (x := u₀) hψpt hinner
    rw [hΨdef]
    exact hcomp
  obtain ⟨ρΨ, hρΨpos, hρΨan⟩ := hΨan.exists_ball_analyticOnNhd
  have hkey : ∀ᶠ u in 𝓝 u₀,
      (f u).2.2 = Ψ u ∧ Ψ u ∈ Metric.ball v₀ 1 ∧ (f u).2.2 ∈ Metric.ball v₀ 1 := by
    have ev1 : ∀ᶠ u in 𝓝 u₀, (f u).1 (-(M : ℤ)) = Φb L u := by
      filter_upwards [Metric.ball_mem_nhds u₀ hρbpos] with u hu
      have h := hagrb L le_rfl u hu
      rw [show (N : ℤ) - (L : ℤ) = -(M : ℤ) by rw [hLdef]; push_cast; ring] at h
      exact h
    have ev2 : ∀ᶠ u in 𝓝 u₀,
        (f u).1 (-(M : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ M * (f u).2.2) := by
      filter_upwards [Metric.ball_mem_nhds u₀ hρbpos] with u hu
      exact (htailf u (lt_of_lt_of_le hu hρbρ₁)).2 M le_rfl
    have ev3 : ∀ᶠ u in 𝓝 u₀, (Φb L u).2 ∈ Metric.ball ((germC a h ((eqLam a : ℂ) ^ M * v₀)).2) εψ := by
      have hcont : ContinuousAt (fun u : ℂ => (Φb L u).2) u₀ :=
        (hanb L le_rfl u₀ (Metric.mem_ball_self hρbpos)).continuousAt.snd
      have hb : Metric.ball ((germC a h ((eqLam a : ℂ) ^ M * v₀)).2) εψ ∈
          𝓝 ((fun u => (Φb L u).2) u₀) := by
        show Metric.ball ((germC a h ((eqLam a : ℂ) ^ M * v₀)).2) εψ ∈ 𝓝 ((Φb L u₀).2)
        rw [hΦLval]
        exact Metric.ball_mem_nhds _ hεψ
      exact hcont.eventually hb
    have ev4 : ∀ᶠ u in 𝓝 u₀, (f u).2.2 ∈ Metric.ball v₀ 1 := by
      have hcont2 : ContinuousAt (fun u => (f u).2.2) u₀ :=
        (continuous_snd.comp continuous_snd).continuousAt.comp hcontf
      have hb : Metric.ball v₀ 1 ∈ 𝓝 ((fun u => (f u).2.2) u₀) := by
        rw [show (fun u => (f u).2.2) u₀ = v₀ from by
          show (f u₀).2.2 = v₀
          rw [hf0u]]
        exact Metric.ball_mem_nhds _ one_pos
      exact hcont2.eventually hb
    filter_upwards [ev1, ev2, ev3, ev4] with u h1 h2 h3 h4
    have hS : (germC a h ((eqLam a : ℂ) ^ M * (f u).2.2)).2 =
        (germC a h ((eqLam a : ℂ) ^ M * Ψ u)).2 := by
      have hA : (germC a h ((eqLam a : ℂ) ^ M * (f u).2.2)).2 = ((f u).1 (-(M : ℤ))).2 := by
        rw [h2]
        simp [ugermC, eqMirror]
      have hB : ((f u).1 (-(M : ℤ))).2 = (Φb L u).2 := by rw [h1]
      have hC : (Φb L u).2 = (germC a h ((eqLam a : ℂ) ^ M * Ψ u)).2 := by
        rw [hΨdef]
        exact (hψright ((Φb L u).2) h3).symm
      rw [hA, hB, hC]
    have hU : Ψ u ∈ Metric.ball v₀ 1 := by
      rw [hΨdef]
      exact hψU ((Φb L u).2) h3
    exact ⟨hSinj h4 hU hS, hU, h4⟩
  obtain ⟨ρk, hρkpos, hρksub⟩ := Metric.mem_nhds_iff.mp hkey
  set ρf : ℝ := min (min ρb ρΨ) (min ρ₁ ρk) with hρfdef
  have hρfpos : 0 < ρf := lt_min (lt_min hρbpos hρΨpos) (lt_min hρ₁pos hρkpos)
  have hρfρb : ρf ≤ ρb := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρfρΨ : ρf ≤ ρΨ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρfρ₁ : ρf ≤ ρ₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρfρk : ρf ≤ ρk := le_trans (min_le_right _ _) (min_le_right _ _)
  have hρf1 : ρf ≤ 1 := le_trans hρfρ₁ hρ₁1
  have hρfεH : ρf ≤ εH := le_trans hρfρ₁ hρ₁εH
  have hΨball : ∀ u ∈ Metric.ball u₀ ρf, Ψ u ∈ Metric.ball v₀ 1 :=
    fun u hu => (hρksub (lt_of_lt_of_le hu hρfρk)).2.1
  have hψ2agree : ∀ u ∈ Metric.ball u₀ ρf, (f u).2.2 = Ψ u :=
    fun u hu => (hρksub (lt_of_lt_of_le hu hρfρk)).1
  -- ## 5. analyticity of the coordinates
  have hcoord_an : ∀ n : ℤ, AnalyticOnNhd ℂ (fun u => (f u).1 n) (Metric.ball u₀ ρf) := by
    intro n
    by_cases hnN : (N : ℤ) ≤ n
    · obtain ⟨n', hn'⟩ : ∃ n' : ℕ, n = (n' : ℤ) := ⟨n.toNat, by omega⟩
      rw [hn'] at hnN ⊢
      have hn'N : N ≤ n' := by exact_mod_cast hnN
      have hset : ∀ u ∈ Metric.ball u₀ ρf,
          (f u).1 (n' : ℤ) = germC a h ((eqLam a : ℂ) ^ n' * u) :=
        fun u hu => (htailf u (lt_of_lt_of_le hu hρfρ₁)).1 n' hn'N
      refine AnalyticOnNhd.congr Metric.isOpen_ball ?_ (fun u hu => (hset u hu).symm)
      have hmaps : MapsTo (fun u : ℂ => (eqLam a : ℂ) ^ n' * u) (Metric.ball u₀ ρf)
          (Metric.ball (0 : ℂ) ρg) := by
        intro u hu
        rw [Metric.mem_ball, dist_eq_norm] at hu
        rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_eqLam_pow_mul ha0 ha1]
        have h1 : ‖u‖ ≤ ‖u₀‖ + 1 := by
          calc ‖u‖ = ‖u₀ + (u - u₀)‖ := by ring_nf
            _ ≤ ‖u₀‖ + ‖u - u₀‖ := norm_add_le _ _
            _ ≤ ‖u₀‖ + 1 := by linarith [lt_of_lt_of_le hu hρf1]
        have h2 : (eqLam a) ^ n' ≤ (eqLam a) ^ N :=
          pow_le_pow_of_le_one hL0.le hL1.le hn'N
        calc (eqLam a) ^ n' * ‖u‖ ≤ (eqLam a) ^ N * (‖u₀‖ + 1) :=
              mul_le_mul h2 h1 (norm_nonneg u) (pow_nonneg hL0.le N)
          _ < ρg := hNbig
      exact hAnC.comp (fun u _ => analyticAt_const.mul analyticAt_id) hmaps
    · by_cases hnM : -(M : ℤ) ≤ n
      · -- middle window: use the induction hypothesis
        set j : ℕ := ((N : ℤ) - n).toNat with hj
        have hidx : (N : ℤ) - (j : ℤ) = n := by
          have h2 : 0 ≤ (N : ℤ) - n := by omega
          rw [hj, Int.toNat_of_nonneg h2]
          ring
        have hjle : j ≤ L := by
          have h2 : (N : ℤ) - n ≤ (L : ℤ) := by
            rw [hLdef]; push_cast; omega
          have h3 : j ≤ ((L : ℤ)).toNat := by
            rw [hj]; exact Int.toNat_le_toNat h2
          simpa using h3
        have hset : ∀ u ∈ Metric.ball u₀ ρf, (f u).1 n = Φb j u := by
          intro u hu
          have h1 := hagrb j hjle u (lt_of_lt_of_le hu hρfρb)
          rwa [hidx] at h1
        refine AnalyticOnNhd.congr Metric.isOpen_ball ?_ (fun u hu => (hset u hu).symm)
        exact (hanb j hjle).mono (Metric.ball_subset_ball hρfρb)
      · -- deep backward: `n < -M`
        obtain ⟨n', hn'⟩ : ∃ n' : ℕ, n = -(n' : ℤ) := ⟨(-n).toNat, by omega⟩
        have hn'M : M ≤ n' := by omega
        rw [hn']
        have hset : ∀ u ∈ Metric.ball u₀ ρf,
            (f u).1 (-(n' : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n' * Ψ u) := by
          intro u hu
          rw [(htailf u (lt_of_lt_of_le hu hρfρ₁)).2 n' hn'M, hψ2agree u hu]
        refine AnalyticOnNhd.congr Metric.isOpen_ball ?_ (fun u hu => (hset u hu).symm)
        have hΨan' : AnalyticOnNhd ℂ Ψ (Metric.ball u₀ ρf) := hρΨan.mono (Metric.ball_subset_ball hρfρΨ)
        have hmaps : MapsTo (fun u : ℂ => (eqLam a : ℂ) ^ n' * Ψ u) (Metric.ball u₀ ρf)
            (Metric.ball (0 : ℂ) ρg) := by
          intro u hu
          rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_eqLam_pow_mul ha0 ha1]
          have h1 : ‖Ψ u‖ ≤ ‖v₀‖ + 1 := by
            have hb := hΨball u hu
            rw [Metric.mem_ball, dist_eq_norm] at hb
            calc ‖Ψ u‖ = ‖v₀ + (Ψ u - v₀)‖ := by ring_nf
              _ ≤ ‖v₀‖ + ‖Ψ u - v₀‖ := norm_add_le _ _
              _ ≤ ‖v₀‖ + 1 := by linarith
          have h2 : (eqLam a) ^ n' ≤ (eqLam a) ^ M :=
            pow_le_pow_of_le_one hL0.le hL1.le hn'M
          calc (eqLam a) ^ n' * ‖Ψ u‖ ≤ (eqLam a) ^ M * (‖v₀‖ + 1) :=
                mul_le_mul h2 h1 (norm_nonneg (Ψ u)) (pow_nonneg hL0.le M)
            _ < ρg := hMbig
        exact analyticOnNhd_ugermC_comp hAnC
          (fun u _ => analyticAt_const.mul (hΨan' u ‹u ∈ Metric.ball u₀ ρf›)) hmaps
  have hψ2_an : AnalyticOnNhd ℂ (fun u => (f u).2.2) (Metric.ball u₀ ρf) := by
    refine AnalyticOnNhd.congr Metric.isOpen_ball ?_ (fun u hu => (hψ2agree u hu).symm)
    exact hρΨan.mono (Metric.ball_subset_ball hρfρΨ)
  -- ## 6. the neighbourhood property, via uniqueness of the chain with given `ψ₁`
  obtain ⟨εL3, hεL3pos, huniq⟩ := chain_unique_window (a := a) (h := h) (p := p)
    (N := N) (M := M) (K := K) hN_le_K hM_le_K (ρg := ρg) hρg hinjY (by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_eqLam_pow_mul ha0 ha1]
      have hnorm : ‖p.2.2‖ = ‖v₀‖ := by rw [hv₀]
      rw [hnorm]
      calc (eqLam a) ^ M * ‖v₀‖ ≤ (eqLam a) ^ M * (‖v₀‖ + 1) :=
            mul_le_mul_of_nonneg_left (by linarith [norm_nonneg v₀]) (pow_nonneg hL0.le M)
        _ < ρg := hMbig)
  have hWo : IsOpen (window p K (min εt εL3)) := window_isOpen p K (lt_min hεt hεL3pos)
  have hprec : f ⁻¹' (window p K (min εt εL3)) ∈ 𝓝 u₀ :=
    hcontf (hWo.mem_nhds (by rw [hf0u]; exact mem_window_self p K (lt_min hεt hεL3pos)))
  obtain ⟨rc, hrc, hrcsub⟩ := Metric.mem_nhds_iff.mp hprec
  set εw : ℝ := min (min εt εL3) (min rc ρf) with hεwdef
  have hεwpos : 0 < εw := lt_min (lt_min hεt hεL3pos) (lt_min hrc hρfpos)
  have hεwεt : εw ≤ εt := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεwεL3 : εw ≤ εL3 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hεwrc : εw ≤ rc := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεwρf : εw ≤ ρf := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨ρf, hρfpos, f, hf0u, ?_, hcoord_an, hψ2_an, ?_⟩
  · intro u hu
    exact ⟨hfH0 u (lt_of_lt_of_le hu hρfεH), (hfic' u (lt_of_lt_of_le hu hρfεH)).2⟩
  · rw [le_principal_iff]
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨window p K εw, (window_isOpen p K hεwpos).mem_nhds (mem_window_self p K hεwpos), ?_⟩
    rintro q ⟨hqw, hqH0⟩
    obtain ⟨hqwK, hqw1, hqw2⟩ := hqw
    have hq_ball : q.2.1 ∈ Metric.ball u₀ ρf := by
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖q.2.1 - u₀‖ = ‖q.2.1 - p.2.1‖ := by rw [hu₀]
        _ < εw := hqw1
        _ ≤ ρf := hεwρf
    have hq_ball₁ : q.2.1 ∈ Metric.ball u₀ ρ₁ := Metric.ball_subset_ball hρfρ₁ hq_ball
    have hfq : f q.2.1 ∈ window p K (min εt εL3) := by
      refine hrcsub ?_
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖q.2.1 - u₀‖ = ‖q.2.1 - p.2.1‖ := by rw [hu₀]
        _ < εw := hqw1
        _ ≤ rc := hεwrc
    have hqchain : IsChain a h q := isChain_of_mem_H0 hqH0
    have hqtail := htb q hqH0 (fun k hk => lt_of_lt_of_le (hqwK k (hKlarge k hk)) hεwεt)
      (lt_of_lt_of_le hqw1 hεwεt) (lt_of_lt_of_le hqw2 hεwεt)
    have hftail := htb (f q.2.1) (hfH0 _ (lt_of_lt_of_le hq_ball hρfεH))
      (fun k hk => lt_of_lt_of_le (hfq.1 k (hKlarge k hk)) (min_le_left _ _))
      (lt_of_lt_of_le hfq.2.1 (min_le_left _ _))
      (lt_of_lt_of_le hfq.2.2 (min_le_left _ _))
    have hψ1eq : q.2.1 = (f q.2.1).2.1 := (hψ1f q.2.1 hq_ball₁).symm
    have heq := huniq q (f q.2.1) hqchain (hchainf q.2.1 hq_ball₁) hψ1eq
      (fun k hk => lt_of_lt_of_le (hqwK k hk) hεwεL3)
      (fun k hk => lt_of_lt_of_le (hfq.1 k hk) (min_le_right _ _))
      (lt_of_lt_of_le hqw2 hεwεL3) (lt_of_lt_of_le hfq.2.2 (min_le_right _ _))
      (fun n hn => hqtail.1 n (le_trans hN₀N hn))
      (fun n hn => hftail.1 n (le_trans hN₀N hn))
      (fun n hn => hqtail.2 n (le_trans hM₀M hn))
      (fun n hn => hftail.2 n (le_trans hM₀M hn))
    exact ⟨q.2.1, hq_ball, heq.symm⟩

end

end Work.EQ
