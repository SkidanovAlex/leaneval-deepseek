import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.fan_base

/-! Auxiliary development for `Work.EQ.backward_puiseux` (F3):

* the algebra of the backward branch `paramΛ`;
* existence of analytic square roots of nonvanishing analytic functions;
* the factorisation `f = z^e · U` of a meromorphic function at `0`. -/

namespace Work.EQ

open Filter _root_.Topology
open Complex Metric

noncomputable section

/-! ## 1. Algebra of the backward branch -/

/-- `O₁ = (-a/2, 0)`. -/
def O1 (a : ℝ) : ℂ × ℂ := (-(((a / 2 : ℝ)) : ℂ), 0)

/-- `O₂ = (a/2, 0)`. -/
def O2 (a : ℝ) : ℂ × ℂ := ((((a / 2 : ℝ)) : ℂ), 0)

/-- `ρ(P)² = (P.1 - a/2)² + P.2²` (relative to `O₂`). -/
def rhoSq (a : ℝ) (P : ℂ × ℂ) : ℂ := (P.1 - ((a / 2 : ℝ) : ℂ)) ^ 2 + P.2 ^ 2

/-- `ρ'(P)² = (P.1 + a/2)² + P.2²` (relative to `O₁`). -/
def rhoPrimeSq (a : ℝ) (P : ℂ × ℂ) : ℂ := (P.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + P.2 ^ 2

/-- The backward point attached to `Q` and a square root `λ` of `ρ'(Q)²`:
`paramΛ a Q λ = O₂ + (1 - λ) · (Q - O₁)/λ`. -/
def paramΛ (a : ℝ) (Q : ℂ × ℂ) (lam : ℂ) : ℂ × ℂ :=
  (((a / 2 : ℝ) : ℂ) + (1 - lam) * (Q.1 + ((a / 2 : ℝ) : ℂ)) / lam, (1 - lam) * Q.2 / lam)

lemma fst_add_paramΛ {a : ℝ} {Q : ℂ × ℂ} {lam : ℂ} (hlam : lam ≠ 0) :
    Q.1 + (paramΛ a Q lam).1 = (Q.1 + ((a / 2 : ℝ) : ℂ)) / lam := by
  simp only [paramΛ]
  field_simp
  ring

lemma snd_add_paramΛ {a : ℝ} {Q : ℂ × ℂ} {lam : ℂ} (hlam : lam ≠ 0) :
    Q.2 + (paramΛ a Q lam).2 = Q.2 / lam := by
  simp only [paramΛ]
  field_simp
  ring

lemma eqRelC_paramΛ {a : ℝ} {Q : ℂ × ℂ} {lam : ℂ} (hlam : lam ≠ 0)
    (h : lam ^ 2 = rhoPrimeSq a Q) : EqRelC a (paramΛ a Q lam) Q := by
  obtain ⟨Q1, Q2⟩ := Q
  have hS : lam * lam = (Q1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q2 ^ 2 := by
    have h' := h; simp only [rhoPrimeSq] at h'
    rw [← h']; ring
  have h1 : Q1 + (((a / 2 : ℝ) : ℂ) + (1 - lam) * (Q1 + ((a / 2 : ℝ) : ℂ)) / lam)
      = (Q1 + ((a / 2 : ℝ) : ℂ)) / lam := by field_simp; ring
  have h2 : Q2 + (1 - lam) * Q2 / lam = Q2 / lam := by field_simp; ring
  rw [EqRelC]
  simp only [paramΛ]
  constructor
  · rw [h1, h2, div_pow, div_pow, ← add_div, div_eq_one_iff_eq (by positivity : lam ^ 2 ≠ 0)]
    linear_combination -hS
  · rw [h1, h2]
    field_simp
    push_cast
    ring

lemma rhoSq_paramΛ {a : ℝ} {Q : ℂ × ℂ} {lam : ℂ} (hlam : lam ≠ 0)
    (h : lam ^ 2 = rhoPrimeSq a Q) : rhoSq a (paramΛ a Q lam) = (1 - lam) ^ 2 := by
  obtain ⟨Q1, Q2⟩ := Q
  have hS : lam * lam = (Q1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q2 ^ 2 := by
    have h' := h; simp only [rhoPrimeSq] at h'
    rw [← h']; ring
  have h1 : (paramΛ a (Q1,Q2) lam).1 - ((a / 2 : ℝ) : ℂ)
      = (1 - lam) * (Q1 + ((a / 2 : ℝ) : ℂ)) / lam := by
    simp only [paramΛ]; ring
  have h2 : (paramΛ a (Q1,Q2) lam).2 = (1 - lam) * Q2 / lam := rfl
  rw [rhoSq, h1, h2, div_pow, div_pow, mul_pow, mul_pow, ← add_div, ← mul_add]
  rw [div_eq_iff (by positivity : lam ^ 2 ≠ 0)]
  linear_combination (-(1 - lam)^2) * hS

lemma regPair_paramΛ {a : ℝ} {Q : ℂ × ℂ} {lam : ℂ} (hlam : lam ≠ 0) (hlam1 : lam ≠ 1)
    (h : lam ^ 2 = rhoPrimeSq a Q) : RegPair a (paramΛ a Q lam) Q := by
  have h2 : rhoSq a (paramΛ a Q lam) ≠ 0 := by
    rw [rhoSq_paramΛ hlam h]; intro hc
    exact hlam1 (by
      have h1l : (1 - lam) = 0 := by
        rw [pow_two] at hc; exact mul_self_eq_zero.mp hc
      linear_combination -h1l)
  have h3 : rhoPrimeSq a Q ≠ 0 := by rw [← h]; exact pow_ne_zero 2 hlam
  exact ⟨eqRelC_paramΛ hlam h, h2, h3⟩

lemma par_of_eqRelC {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q) :
    (Q.2 + P.2) * (Q.1 + ((a / 2 : ℝ) : ℂ)) = (Q.1 + P.1) * Q.2 := by
  obtain ⟨P1, P2⟩ := P; obtain ⟨Q1, Q2⟩ := Q
  simp only [EqRelC] at h
  linear_combination h.2

theorem exists_paramΛ_of_regPair {a : ℝ} {P Q : ℂ × ℂ} (h : RegPair a P Q) :
    ∃ lam : ℂ, lam ≠ 0 ∧ lam ^ 2 = rhoPrimeSq a Q ∧ P = paramΛ a Q lam := by
  obtain ⟨hrel, hP, hQ⟩ := h
  have he : (Q.1 + P.1) ^ 2 + (Q.2 + P.2) ^ 2 = 1 := hrel.1
  have hp : (Q.2 + P.2) * (Q.1 + ((a / 2 : ℝ) : ℂ)) = (Q.1 + P.1) * Q.2 := par_of_eqRelC hrel
  have hQ' : (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2 ≠ 0 := hQ
  have hex : ∃ lam : ℂ, lam * (Q.1 + P.1) = Q.1 + ((a / 2 : ℝ) : ℂ) ∧ lam * (Q.2 + P.2) = Q.2 := by
    by_cases h1 : Q.1 + P.1 = 0
    · have he2 : (Q.2 + P.2) ^ 2 = 1 := by rw [h1] at he; simpa using he
      have he2ne : (Q.2 + P.2) ≠ 0 := by
        intro hc; rw [hc] at he2; norm_num at he2
      have hSa : Q.1 + ((a / 2 : ℝ) : ℂ) = 0 := by
        have hz : (Q.2 + P.2) * (Q.1 + ((a / 2 : ℝ) : ℂ)) = 0 := by rw [hp, h1, zero_mul]
        exact (mul_eq_zero.mp hz).resolve_left he2ne
      exact ⟨Q.2 / (Q.2 + P.2), by rw [h1, mul_zero, hSa], by field_simp⟩
    · exact ⟨(Q.1 + ((a / 2 : ℝ) : ℂ)) / (Q.1 + P.1), by field_simp,
        by rw [div_mul_eq_mul_div, div_eq_iff h1]; linear_combination hp⟩
  obtain ⟨lam, hle1, hle2⟩ := hex
  have hlam2 : lam ^ 2 = rhoPrimeSq a Q := by
    have hkey : lam ^ 2 * ((Q.1 + P.1) ^ 2 + (Q.2 + P.2) ^ 2)
        = (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2 := by
      linear_combination (lam * (Q.1 + P.1) + (Q.1 + ((a/2:ℝ):ℂ))) * hle1
        + (lam * (Q.2 + P.2) + Q.2) * hle2
    rw [he, mul_one] at hkey
    simpa only [rhoPrimeSq] using hkey
  have hlamne : lam ≠ 0 := by
    intro hc; rw [hc] at hlam2; norm_num at hlam2
    exact hQ' hlam2.symm
  refine ⟨lam, hlamne, hlam2, ?_⟩
  ext
  · simp only [paramΛ]; rw [mul_div_assoc, (show (Q.1 + ((a / 2 : ℝ) : ℂ)) / lam = Q.1 + P.1 from by
      field_simp; linear_combination -hle1)]
    linear_combination hle1
  · simp only [paramΛ]; rw [mul_div_assoc, (show Q.2 / lam = Q.2 + P.2 from by
      field_simp; linear_combination -hle2)]
    linear_combination hle2

/-! ## 2. Analytic square roots -/

lemma sq_sqrt (w : ℂ) : Complex.sqrt w ^ 2 = w := by
  rw [Complex.sqrt]; exact Complex.cpow_nat_inv_pow w (by norm_num)

/-- A nonvanishing analytic function on a ball has an analytic square root on a (smaller)
ball. -/
lemma exists_analytic_sqrt {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : AnalyticOnNhd ℂ g (ball 0 ρ)) (hg0 : g 0 ≠ 0) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (ball 0 ρ') ∧
      ∀ z ∈ ball 0 ρ', h z ^ 2 = g z := by
  set u : ℂ → ℂ := fun z => g z / g 0 with hu
  have hu0 : u 0 = 1 := by simp [hu, hg0]
  have huan : AnalyticOnNhd ℂ u (ball 0 ρ) := fun z hz => (hg z hz).div analyticAt_const hg0
  have hcont : ContinuousAt u 0 := (huan 0 (by simpa using hρ)).continuousAt
  have hmem : {z : ℂ | u z ∈ slitPlane} ∈ 𝓝 (0 : ℂ) := by
    have h1 : u 0 ∈ slitPlane := by rw [hu0]; exact one_mem_slitPlane
    exact hcont.preimage_mem_nhds (isOpen_slitPlane.mem_nhds h1)
  rw [Metric.mem_nhds_iff] at hmem
  obtain ⟨ρ₁, hρ₁0, hρ₁⟩ := hmem
  refine ⟨min ρ₁ ρ, lt_min hρ₁0 hρ, min_le_right _ _, ?_⟩
  refine ⟨fun z => sqrt (g 0) * sqrt (u z), ?_, ?_⟩
  · have hball : ball 0 (min ρ₁ ρ) ⊆ {z | u z ∈ slitPlane} := fun z hz =>
      hρ₁ (by rw [Metric.mem_ball] at hz ⊢; exact lt_of_lt_of_le hz (min_le_left _ _))
    have hmono : ball (0:ℂ) (min ρ₁ ρ) ⊆ ball (0:ℂ) ρ := by
      intro y hy; rw [Metric.mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy (min_le_right _ _)
    have hsqrt : AnalyticOnNhd ℂ sqrt slitPlane :=
      differentiableOn_sqrt.analyticOnNhd isOpen_slitPlane
    intro z hz
    exact analyticAt_const.mul (hsqrt.comp (huan.mono hmono) hball z hz)
  · intro z hz
    rw [mul_pow, sq_sqrt, sq_sqrt]
    simp only [hu]
    rw [mul_div_cancel₀ _ hg0]

/-! ## 3. Factorisation of a meromorphic function at `0` -/

/-- A meromorphic function on a punctured ball which is not eventually zero factors as
`z^e · U` with `U` analytic and nonvanishing near `0`. -/
lemma meromorphic_factor {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : MeromorphicAt f 0) (_han : AnalyticOnNhd ℂ f (ball 0 ρ \ {0}))
    (hne : ¬ (f =ᶠ[𝓝[≠] (0:ℂ)] 0)) :
    ∃ (e : ℤ) (U : ℂ → ℂ) (ρ' : ℝ), 0 < ρ' ∧ ρ' ≤ ρ ∧ AnalyticOnNhd ℂ U (ball 0 ρ') ∧
      U 0 ≠ 0 ∧ ∀ v, 0 < ‖v‖ → ‖v‖ < ρ' → f v = v ^ e * U v := by
  have htop : meromorphicOrderAt f 0 ≠ ⊤ := by
    intro hc; exact hne ((meromorphicOrderAt_eq_top_iff).1 hc)
  obtain ⟨U, hUan, hU0, hUeq⟩ := (meromorphicOrderAt_ne_top_iff hf).1 htop
  set e : ℤ := (meromorphicOrderAt f 0).untop₀ with he
  have hev2 : ∀ᶠ v in 𝓝 (0 : ℂ), v ∈ ({0}ᶜ : Set ℂ) → f v = v ^ e * U v := by
    have h := hUeq
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at h
    filter_upwards [h] with v hv hvc
    rw [hv hvc]; simp [e]
  rw [Filter.eventually_iff, Metric.mem_nhds_iff] at hev2
  obtain ⟨ρ₂, hρ₂0, hρ₂⟩ := hev2
  have hev3 := hUan.eventually_analyticAt
  rw [Filter.eventually_iff, Metric.mem_nhds_iff] at hev3
  obtain ⟨ρU, hρU0, hρU⟩ := hev3
  have hsub : ball (0:ℂ) (min ρ₂ (min ρU ρ)) ⊆ ball (0:ℂ) ρU := by
    intro y hy
    rw [Metric.mem_ball] at hy ⊢
    exact lt_of_lt_of_le hy (le_trans (min_le_right _ _) (min_le_left _ _))
  have hsub2 : ball (0:ℂ) (min ρ₂ (min ρU ρ)) ⊆ ball (0:ℂ) ρ₂ := by
    intro y hy
    rw [Metric.mem_ball] at hy ⊢
    exact lt_of_lt_of_le hy (min_le_left _ _)
  refine ⟨e, U, min ρ₂ (min ρU ρ), lt_min hρ₂0 (lt_min hρU0 hρ),
    le_trans (min_le_right _ _) (min_le_right _ _), fun (y : ℂ) hy => hρU (hsub hy), hU0, ?_⟩
  intro v hv0 hvr
  refine hρ₂ (hsub2 ?_) (by simpa using hv0.ne')
  rw [Metric.mem_ball, dist_zero_right]
  exact hvr

/-! ## 4. The single backward step -/

lemma analyticAt_zpow_id {w : ℂ} (hw : w ≠ 0) (e : ℤ) :
    AnalyticAt ℂ (fun z : ℂ => z ^ e) w := by
  have h : AnalyticAt ℂ (id ^ e : ℂ → ℂ) w :=
    (analyticAt_id (𝕜 := ℂ) (E := ℂ) (z := w)).zpow (n := e) hw
  refine AnalyticAt.congr h ?_
  filter_upwards with z
  rfl

/-- One step of the backward recursion: given a meromorphic-at-`0` point function `Y`, there is
a function `λ`, meromorphic at `0` and analytic on a punctured ball, with
`λ w ^ 2 = ρ'(Y (w^2))²` there and `λ w ≠ 0`. -/
lemma step_exists {a : ℝ} {Y : ℂ → ℂ × ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hYm1 : MeromorphicAt (fun v => (Y v).1) 0)
    (hYm2 : MeromorphicAt (fun v => (Y v).2) 0)
    (hYan1 : AnalyticOnNhd ℂ (fun v => (Y v).1) (ball 0 ρ \ {0}))
    (hYan2 : AnalyticOnNhd ℂ (fun v => (Y v).2) (ball 0 ρ \ {0}))
    (hne : ¬ (fun v => rhoPrimeSq a (Y v)) =ᶠ[𝓝[≠] (0:ℂ)] 0) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ^ 2 ≤ ρ ∧
      ∃ lam : ℂ → ℂ, MeromorphicAt lam 0 ∧ AnalyticOnNhd ℂ lam (ball 0 ρ' \ {0}) ∧
        (∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ' → lam w ^ 2 = rhoPrimeSq a (Y (w ^ 2))) ∧
        (∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ' → lam w ≠ 0) := by
  have hFm : MeromorphicAt (fun v => rhoPrimeSq a (Y v)) 0 := by
    have h := (((hYm1.add (MeromorphicAt.const (((a/2:ℝ):ℂ)) 0)).pow 2)).add (hYm2.pow 2)
    refine h.congr ?_
    filter_upwards with v
    simp only [Pi.add_apply, Pi.pow_apply, rhoPrimeSq]
  have hFan : AnalyticOnNhd ℂ (fun v => rhoPrimeSq a (Y v)) (ball 0 ρ \ {0}) := by
    intro v hv
    have h : AnalyticAt ℂ (fun w : ℂ => ((Y w).1 + ((a/2:ℝ):ℂ)) ^ 2 + (Y w).2 ^ 2) v :=
      (((hYan1 v hv).add (analyticAt_const (v := ((a/2:ℝ):ℂ)) (x := v))).pow 2).add
        ((hYan2 v hv).pow 2)
    refine AnalyticAt.congr h ?_
    filter_upwards with w
    simp only [rhoPrimeSq]
  obtain ⟨e, U, ρ₁, hρ₁0, hρ₁ρ, hUan, hU0, hUfac⟩ := meromorphic_factor hρ hFm hFan hne
  obtain ⟨ρ_U, hρ_U0, hρ_Ule, hUne⟩ : ∃ ρ_U : ℝ, 0 < ρ_U ∧ ρ_U ≤ ρ₁ ∧
      ∀ y ∈ ball 0 ρ_U, U y ≠ 0 := by
    have hev : ∀ᶠ y in 𝓝 (0:ℂ), U y ≠ 0 :=
      (hUan 0 (by simpa using hρ₁0)).continuousAt.eventually_ne hU0
    rw [Filter.eventually_iff, Metric.mem_nhds_iff] at hev
    obtain ⟨r, hr0, hr⟩ := hev
    exact ⟨min r ρ₁, lt_min hr0 hρ₁0, min_le_right _ _, fun y hy =>
      hr (by rw [Metric.mem_ball] at hy ⊢; exact lt_of_lt_of_le hy (min_le_left _ _))⟩
  set ρG : ℝ := Real.sqrt ρ_U with hρGdef
  have hρG0 : 0 < ρG := by rw [hρGdef]; exact Real.sqrt_pos.mpr hρ_U0
  have hρGsq : ρG ^ 2 = ρ_U := by rw [hρGdef]; exact Real.sq_sqrt hρ_U0.le
  have hGan : AnalyticOnNhd ℂ (fun w : ℂ => U (w^2)) (ball 0 ρG) := by
    refine hUan.comp (fun w hw => analyticAt_id.pow 2) ?_
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw ⊢
    rw [norm_pow]
    calc ‖w‖ ^ 2 < ρG ^ 2 := by nlinarith [norm_nonneg w, hρG0]
      _ = ρ_U := hρGsq
      _ ≤ ρ₁ := hρ_Ule
  obtain ⟨ρS, hρS0, hρSle, S, hSan, hSsq⟩ :=
    exists_analytic_sqrt hρG0 hGan (by simpa using hU0)
  have hρSsqρ : ρS ^ 2 ≤ ρ := by
    calc ρS ^ 2 ≤ ρG ^ 2 := by nlinarith [hρSle, hρS0.le]
      _ = ρ_U := hρGsq
      _ ≤ ρ₁ := hρ_Ule
      _ ≤ ρ := hρ₁ρ
  have hρSsqU : ρS ^ 2 ≤ ρ_U := by
    calc ρS ^ 2 ≤ ρG ^ 2 := by nlinarith [hρSle, hρS0.le]
      _ = ρ_U := hρGsq
  refine ⟨ρS, hρS0, hρSsqρ, fun w => w ^ e * S w, ?_, ?_, ?_, ?_⟩
  · have h1 : MeromorphicAt (fun w : ℂ => w ^ e) 0 :=
      MeromorphicAt.fun_zpow (analyticAt_id (z := (0:ℂ))).meromorphicAt e
    have h2 : MeromorphicAt S 0 := (hSan 0 (by simpa using hρS0)).meromorphicAt
    exact h1.mul h2
  · intro w hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    exact (analyticAt_zpow_id hw0 e).mul (hSan w hw.1)
  · intro w hw0 hw
    have hwS : w ∈ ball 0 ρS := by rw [Metric.mem_ball, dist_zero_right]; exact hw
    have hw2pos : 0 < ‖w ^ 2‖ := by rw [norm_pow]; positivity
    have hw2lt : ‖w ^ 2‖ < ρ_U := by
      rw [norm_pow]
      calc ‖w‖ ^ 2 < ρS ^ 2 := by nlinarith [hw, norm_nonneg w, hρS0]
        _ ≤ ρ_U := hρSsqU
    have hpow : (w ^ e) ^ 2 = (w ^ 2) ^ e := by
      rw [show w ^ 2 = w * w from by ring, mul_zpow]
      ring
    rw [hUfac (w ^ 2) hw2pos (lt_of_lt_of_le hw2lt hρ_Ule), mul_pow, hSsq w hwS, hpow]
  · intro w hw0 hw
    have hw0ne : w ≠ 0 := by rintro rfl; simp at hw0
    have hwS : w ∈ ball 0 ρS := by rw [Metric.mem_ball, dist_zero_right]; exact hw
    have hw2lt : ‖w ^ 2‖ < ρ_U := by
      rw [norm_pow]
      calc ‖w‖ ^ 2 < ρS ^ 2 := by nlinarith [hw, norm_nonneg w, hρS0]
        _ ≤ ρ_U := hρSsqU
    have hSne : S w ≠ 0 := by
      intro hS0
      refine hUne (w ^ 2) (by rw [Metric.mem_ball, dist_zero_right]; exact hw2lt) ?_
      rw [← hSsq w hwS, hS0]; ring
    exact mul_ne_zero (zpow_ne_zero e hw0ne) hSne

/-! ## 5. The recursion along a sign sequence -/

/-- The sign attached to a `Bool`. -/
def sgn (b : Bool) : ℂ := if b then 1 else -1

/-- The data produced by one backward step: a radius, a meromorphic `λ` with `λ² = ρ'(Y(·²))²`
on the punctured ball, nonvanishing there, and analytic on a punctured ball. -/
structure StepOut (a : ℝ) (Y : ℂ → ℂ × ℂ) (ρY : ℝ) where
  ρ : ℝ
  hρ : 0 < ρ
  hρle : ρ ^ 2 ≤ ρY
  lam : ℂ → ℂ
  hlam_m : MeromorphicAt lam 0
  hlam_an : AnalyticOnNhd ℂ lam (ball 0 ρ \ {0})
  hlam_sq : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ → lam w ^ 2 = rhoPrimeSq a (Y (w ^ 2))
  hlam_ne : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ → lam w ≠ 0

lemma stepOut_exists {a : ℝ} {Y : ℂ → ℂ × ℂ} {ρY : ℝ} (hρY : 0 < ρY)
    (hYm1 : MeromorphicAt (fun v => (Y v).1) 0)
    (hYm2 : MeromorphicAt (fun v => (Y v).2) 0)
    (hYan1 : AnalyticOnNhd ℂ (fun v => (Y v).1) (ball 0 ρY \ {0}))
    (hYan2 : AnalyticOnNhd ℂ (fun v => (Y v).2) (ball 0 ρY \ {0}))
    (hne : ¬ (fun v => rhoPrimeSq a (Y v)) =ᶠ[𝓝[≠] (0:ℂ)] 0) :
    ∃ S : StepOut a Y ρY, True := by
  obtain ⟨ρ', hρ'0, hρ'le, lam, hlam_m, hlam_an, hlam_sq, hlam_ne⟩ :=
    step_exists hρY hYm1 hYm2 hYan1 hYan2 hne
  exact ⟨⟨ρ', hρ'0, hρ'le, lam, hlam_m, hlam_an, hlam_sq, hlam_ne⟩, trivial⟩

noncomputable def stepOut (a : ℝ) (b : Bool) (Y : ℂ → ℂ × ℂ) (ρY : ℝ) :
    ℝ × (ℂ → ℂ × ℂ) := by
  classical
  exact if h : ∃ S : StepOut a Y ρY, True then
    (h.choose.ρ, fun w => paramΛ a (Y (w ^ 2)) (sgn b * h.choose.lam w))
  else (1, fun _ => (0, 0))

noncomputable def stepLam (a : ℝ) (Y : ℂ → ℂ × ℂ) (ρY : ℝ) : ℂ → ℂ := by
  classical
  exact if h : ∃ S : StepOut a Y ρY, True then h.choose.lam else fun _ => 0

/-- The pair `(radius, point-function)` at level `m` along the sign sequence `σ`. -/
noncomputable def seqP (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) (σ : ℕ → Bool) :
    ℕ → ℝ × (ℂ → ℂ × ℂ) :=
  Nat.rec (R, fun w => c (u₀ + w)) (fun m prev => stepOut a (σ m) prev.2 prev.1)

noncomputable def Xf (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) (σ : ℕ → Bool) (m : ℕ) :
    ℂ → ℂ × ℂ :=
  (seqP a c u₀ R σ m).2

noncomputable def seqRho (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) (σ : ℕ → Bool) (m : ℕ) :
    ℝ :=
  (seqP a c u₀ R σ m).1

/-- The `λ` used at the step producing level `m+1` along `σ`. -/
noncomputable def Lf (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) (σ : ℕ → Bool) (m : ℕ) :
    ℂ → ℂ :=
  stepLam a (Xf a c u₀ R σ m) (seqRho a c u₀ R σ m)

lemma analyticAt_sq {w : ℂ} : AnalyticAt ℂ (fun z : ℂ => z ^ 2) w := by
  have h : AnalyticAt ℂ (id ^ (2:ℕ) : ℂ → ℂ) w :=
    (analyticAt_id (𝕜 := ℂ) (E := ℂ) (z := w)).pow 2
  refine AnalyticAt.congr h ?_
  filter_upwards with z
  rfl

lemma sgn_ne_zero (b : Bool) : sgn b ≠ 0 := by cases b <;> norm_num [sgn]

lemma sgn_mul_sgn (b : Bool) : sgn b * sgn b = 1 := by cases b <;> norm_num [sgn]

lemma analyticAt_paramΛ_fst {a : ℝ} {Y : ℂ → ℂ × ℂ} {b : Bool} {lam : ℂ → ℂ} {w : ℂ}
    (hY1 : AnalyticAt ℂ (fun v => (Y v).1) (w^2))
    (hlam : AnalyticAt ℂ lam w) (hlamw : lam w ≠ 0) :
    AnalyticAt ℂ (fun z => (paramΛ a (Y (z^2)) (sgn b * lam z)).1) w := by
  have hlamS : AnalyticAt ℂ (fun z : ℂ => sgn b * lam z) w := analyticAt_const.mul hlam
  have hlamSne : (sgn b * lam w) ≠ 0 := mul_ne_zero (sgn_ne_zero b) hlamw
  have h1 : AnalyticAt ℂ (fun z : ℂ => 1 - sgn b * lam z) w := analyticAt_const.sub hlamS
  have h2 : AnalyticAt ℂ (fun z : ℂ => (Y (z^2)).1 + (((a / 2 : ℝ)) : ℂ)) w :=
    (hY1.comp (f := fun z : ℂ => z^2) (analyticAt_sq (w := w))).add analyticAt_const
  have h3 : AnalyticAt ℂ ((fun z : ℂ => 1 - sgn b * lam z) *
      (fun z : ℂ => (Y (z^2)).1 + (((a / 2 : ℝ)) : ℂ))) w := h1.mul h2
  have h4 : AnalyticAt ℂ (((fun z : ℂ => 1 - sgn b * lam z) *
      (fun z : ℂ => (Y (z^2)).1 + (((a / 2 : ℝ)) : ℂ))) / (fun z : ℂ => sgn b * lam z)) w :=
    h3.div hlamS hlamSne
  have h5 : AnalyticAt ℂ (fun z : ℂ => (((a / 2 : ℝ)) : ℂ) +
      ((1 - sgn b * lam z) * ((Y (z^2)).1 + (((a / 2 : ℝ)) : ℂ))) / (sgn b * lam z)) w :=
    analyticAt_const.add h4
  refine AnalyticAt.congr h5 ?_
  filter_upwards with z
  rfl

lemma analyticAt_paramΛ_snd {a : ℝ} {Y : ℂ → ℂ × ℂ} {b : Bool} {lam : ℂ → ℂ} {w : ℂ}
    (hY2 : AnalyticAt ℂ (fun v => (Y v).2) (w^2))
    (hlam : AnalyticAt ℂ lam w) (hlamw : lam w ≠ 0) :
    AnalyticAt ℂ (fun z => (paramΛ a (Y (z^2)) (sgn b * lam z)).2) w := by
  have hlamS : AnalyticAt ℂ (fun z : ℂ => sgn b * lam z) w := analyticAt_const.mul hlam
  have hlamSne : (sgn b * lam w) ≠ 0 := mul_ne_zero (sgn_ne_zero b) hlamw
  have h1 : AnalyticAt ℂ (fun z : ℂ => 1 - sgn b * lam z) w := analyticAt_const.sub hlamS
  have h2 : AnalyticAt ℂ (fun z : ℂ => (Y (z^2)).2) w := hY2.comp (f := fun z : ℂ => z^2) (analyticAt_sq (w := w))
  have h3 : AnalyticAt ℂ ((fun z : ℂ => 1 - sgn b * lam z) * (fun z : ℂ => (Y (z^2)).2)) w :=
    h1.mul h2
  have h4 : AnalyticAt ℂ (((fun z : ℂ => 1 - sgn b * lam z) * (fun z : ℂ => (Y (z^2)).2)) /
      (fun z : ℂ => sgn b * lam z)) w := h3.div hlamS hlamSne
  refine AnalyticAt.congr h4 ?_
  filter_upwards with z
  rfl

lemma meromorphicAt_paramΛ_fst {a : ℝ} {Y : ℂ → ℂ × ℂ} {b : Bool} {lam : ℂ → ℂ}
    (hY1 : MeromorphicAt (fun w => (Y (w^2)).1) 0) (hlam : MeromorphicAt lam 0) :
    MeromorphicAt (fun z => (paramΛ a (Y (z^2)) (sgn b * lam z)).1) 0 := by
  have hlamS : MeromorphicAt (fun z : ℂ => sgn b * lam z) 0 :=
    (MeromorphicAt.const (sgn b) 0).mul hlam
  have h1 : MeromorphicAt (fun z : ℂ => 1 - sgn b * lam z) 0 :=
    (MeromorphicAt.const (1:ℂ) 0).sub hlamS
  have h2 : MeromorphicAt (fun z : ℂ => (Y (z^2)).1 + (((a / 2 : ℝ)) : ℂ)) 0 :=
    hY1.add (MeromorphicAt.const _ 0)
  have h3 : MeromorphicAt ((fun z : ℂ => 1 - sgn b * lam z) *
      (fun z : ℂ => (Y (z^2)).1 + (((a / 2 : ℝ)) : ℂ))) 0 := h1.mul h2
  have h4 : MeromorphicAt (((fun z : ℂ => 1 - sgn b * lam z) *
      (fun z : ℂ => (Y (z^2)).1 + (((a / 2 : ℝ)) : ℂ))) / (fun z : ℂ => sgn b * lam z)) 0 :=
    h3.div hlamS
  have h5 : MeromorphicAt (fun z : ℂ => (((a / 2 : ℝ)) : ℂ) +
      ((1 - sgn b * lam z) * ((Y (z^2)).1 + (((a / 2 : ℝ)) : ℂ))) / (sgn b * lam z)) 0 :=
    (MeromorphicAt.const _ 0).add h4
  refine h5.congr ?_
  filter_upwards with z
  rfl

lemma meromorphicAt_paramΛ_snd {a : ℝ} {Y : ℂ → ℂ × ℂ} {b : Bool} {lam : ℂ → ℂ}
    (hY2 : MeromorphicAt (fun w => (Y (w^2)).2) 0) (hlam : MeromorphicAt lam 0) :
    MeromorphicAt (fun z => (paramΛ a (Y (z^2)) (sgn b * lam z)).2) 0 := by
  have hlamS : MeromorphicAt (fun z : ℂ => sgn b * lam z) 0 :=
    (MeromorphicAt.const (sgn b) 0).mul hlam
  have h1 : MeromorphicAt (fun z : ℂ => 1 - sgn b * lam z) 0 :=
    (MeromorphicAt.const (1:ℂ) 0).sub hlamS
  have h3 : MeromorphicAt ((fun z : ℂ => 1 - sgn b * lam z) * (fun z : ℂ => (Y (z^2)).2)) 0 :=
    h1.mul hY2
  have h4 : MeromorphicAt (((fun z : ℂ => 1 - sgn b * lam z) * (fun z : ℂ => (Y (z^2)).2)) /
      (fun z : ℂ => sgn b * lam z)) 0 := h3.div hlamS
  refine h4.congr ?_
  filter_upwards with z
  rfl


/-- The radicand of `X_k` is not identically zero for all levels `k < m`. -/
def Good (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) (σ : ℕ → Bool) (m : ℕ) : Prop :=
  ∀ k < m, ¬ (fun w => rhoPrimeSq a (Xf a c u₀ R σ k w)) =ᶠ[𝓝[≠] (0:ℂ)] 0

structure XProps (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) (σ : ℕ → Bool) (m : ℕ) : Prop where
  hρ : 0 < seqRho a c u₀ R σ m
  han1 : AnalyticOnNhd ℂ (fun v => (Xf a c u₀ R σ m v).1) (ball 0 (seqRho a c u₀ R σ m) \ {0})
  han2 : AnalyticOnNhd ℂ (fun v => (Xf a c u₀ R σ m v).2) (ball 0 (seqRho a c u₀ R σ m) \ {0})
  hm1 : MeromorphicAt (fun v => (Xf a c u₀ R σ m v).1) 0
  hm2 : MeromorphicAt (fun v => (Xf a c u₀ R σ m v).2) 0

lemma seqP_succ (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) (σ : ℕ → Bool) (m : ℕ) :
    seqP a c u₀ R σ (m+1) =
      stepOut a (σ m) (Xf a c u₀ R σ m) (seqRho a c u₀ R σ m) := rfl

lemma Xf_zero (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) (σ : ℕ → Bool) :
    Xf a c u₀ R σ 0 = fun w => c (u₀ + w) := rfl

lemma seqRho_zero (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) (σ : ℕ → Bool) :
    seqRho a c u₀ R σ 0 = R := rfl

theorem XProps_of_good {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : AnalyticOnNhd ℂ c (ball u₀ R)) (σ : ℕ → Bool) (m : ℕ)
    (hgood : Good a c u₀ R σ m) : XProps a c u₀ R σ m := by
  induction m with
  | zero =>
    have hX : AnalyticOnNhd ℂ (fun w : ℂ => c (u₀ + w)) (ball 0 R) := by
      refine hc.comp (fun w hw => (analyticAt_const (v := u₀) (x := w)).add
        (analyticAt_id (z := w))) ?_
      intro w hw
      rw [Metric.mem_ball] at hw ⊢
      simpa [dist_eq_norm, add_sub_cancel_left] using hw
    have hX0 : AnalyticAt ℂ (fun w : ℂ => c (u₀ + w)) 0 :=
      hX 0 (by rw [Metric.mem_ball, dist_zero_right]; simpa using hR)
    refine ⟨hR, ?_, ?_, ?_, ?_⟩
    · rw [seqRho_zero]
      change AnalyticOnNhd ℂ (fun v => (c (u₀ + v)).1) (ball 0 R \ {0})
      intro v hv
      exact (analyticAt_fst (p := c (u₀ + v))).comp (f := fun w : ℂ => c (u₀ + w)) (hX v hv.1)
    · rw [seqRho_zero]
      change AnalyticOnNhd ℂ (fun v => (c (u₀ + v)).2) (ball 0 R \ {0})
      intro v hv
      exact (analyticAt_snd (p := c (u₀ + v))).comp (f := fun w : ℂ => c (u₀ + w)) (hX v hv.1)
    · change MeromorphicAt (fun v => (c (u₀ + v)).1) 0
      exact ((analyticAt_fst (p := c (u₀ + (0:ℂ)))).comp (f := fun w : ℂ => c (u₀ + w)) hX0).meromorphicAt
    · change MeromorphicAt (fun v => (c (u₀ + v)).2) 0
      exact ((analyticAt_snd (p := c (u₀ + (0:ℂ)))).comp (f := fun w : ℂ => c (u₀ + w)) hX0).meromorphicAt
  | succ m ih =>
    have hgoodm : Good a c u₀ R σ m := fun k hk => hgood k (Nat.lt_succ_of_lt hk)
    have hpm := ih hgoodm
    have hne : ¬ (fun v => rhoPrimeSq a (Xf a c u₀ R σ m v)) =ᶠ[𝓝[≠] (0:ℂ)] 0 :=
      hgood m (Nat.lt_succ_self m)
    have hex : ∃ S : StepOut a (Xf a c u₀ R σ m) (seqRho a c u₀ R σ m), True :=
      stepOut_exists hpm.hρ hpm.hm1 hpm.hm2 hpm.han1 hpm.han2 hne
    have hunf : stepOut a (σ m) (Xf a c u₀ R σ m) (seqRho a c u₀ R σ m)
        = ((hex.choose).ρ, fun w => paramΛ a (Xf a c u₀ R σ m (w ^ 2))
            (sgn (σ m) * (hex.choose).lam w)) := by
      unfold stepOut
      rw [dif_pos hex]
    have hρsucc : seqRho a c u₀ R σ (m+1) = (hex.choose).ρ := by
      rw [seqRho, seqP_succ, hunf]
    have hXsucc : Xf a c u₀ R σ (m+1)
        = fun w => paramΛ a (Xf a c u₀ R σ m (w ^ 2)) (sgn (σ m) * (hex.choose).lam w) := by
      rw [Xf, seqP_succ, hunf]
    have hYm1 : MeromorphicAt (fun w : ℂ => (Xf a c u₀ R σ m (w ^ 2)).1) 0 :=
      MeromorphicAt.comp_analyticAt (x := (0:ℂ)) (f := fun v : ℂ => (Xf a c u₀ R σ m v).1)
        (g := fun z : ℂ => z^2) (by simpa using hpm.hm1) (analyticAt_sq (w := (0:ℂ)))
    have hYm2 : MeromorphicAt (fun w : ℂ => (Xf a c u₀ R σ m (w ^ 2)).2) 0 :=
      MeromorphicAt.comp_analyticAt (x := (0:ℂ)) (f := fun v : ℂ => (Xf a c u₀ R σ m v).2)
        (g := fun z : ℂ => z^2) (by simpa using hpm.hm2) (analyticAt_sq (w := (0:ℂ)))
    have hsqle := hex.choose.hρle
    have hρc := hex.choose.hρ
    have hlaman := hex.choose.hlam_an
    have hlamne := hex.choose.hlam_ne
    have hlam_m := hex.choose.hlam_m
    refine ⟨by rw [hρsucc]; exact hρc, ?_, ?_, ?_, ?_⟩
    · rw [hXsucc]
      intro v hv
      rw [hρsucc] at hv
      have hvρ : ‖v‖ < (hex.choose).ρ := by
        have h := hv.1; rwa [Metric.mem_ball, dist_zero_right] at h
      have hvne : v ≠ 0 := by simpa using hv.2
      have hvn : 0 < ‖v‖ := by rw [norm_pos_iff]; exact hvne
      have hv2 : (v^2) ∈ ball 0 (seqRho a c u₀ R σ m) \ {0} := by
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, dist_zero_right, norm_pow]
          calc ‖v‖ ^ 2 < (hex.choose).ρ ^ 2 := by nlinarith [norm_nonneg v, hρc]
            _ ≤ seqRho a c u₀ R σ m := hsqle
        · simp [hvne]
      exact analyticAt_paramΛ_fst (hpm.han1 (v^2) hv2) (hlaman v hv) (hlamne v hvn hvρ)
    · rw [hXsucc]
      intro v hv
      rw [hρsucc] at hv
      have hvρ : ‖v‖ < (hex.choose).ρ := by
        have h := hv.1; rwa [Metric.mem_ball, dist_zero_right] at h
      have hvne : v ≠ 0 := by simpa using hv.2
      have hvn : 0 < ‖v‖ := by rw [norm_pos_iff]; exact hvne
      have hv2 : (v^2) ∈ ball 0 (seqRho a c u₀ R σ m) \ {0} := by
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, dist_zero_right, norm_pow]
          calc ‖v‖ ^ 2 < (hex.choose).ρ ^ 2 := by nlinarith [norm_nonneg v, hρc]
            _ ≤ seqRho a c u₀ R σ m := hsqle
        · simp [hvne]
      exact analyticAt_paramΛ_snd (hpm.han2 (v^2) hv2) (hlaman v hv) (hlamne v hvn hvρ)
    · rw [hXsucc]
      exact meromorphicAt_paramΛ_fst hYm1 hlam_m
    · rw [hXsucc]
      exact meromorphicAt_paramΛ_snd hYm2 hlam_m

/-! ## 6. Admissibility, radii and the branch families -/

/-- Extension of a `Fin N`-sign sequence to `ℕ`. -/
def sigmaExtN {N : ℕ} (σ : Fin N → Bool) : ℕ → Bool :=
  fun k => if h : k < N then σ ⟨k, h⟩ else false

@[simp] lemma sigmaExtN_apply {N : ℕ} (σ : Fin N → Bool) (k : ℕ) (hk : k < N) :
    sigmaExtN σ k = σ ⟨k, hk⟩ := by
  simp only [sigmaExtN, dif_pos hk]

/-- `Adm σ` says that the sign sequence `σ` never produces a degenerate branch: the radicands of
`X_m` are not identically zero and the `λ` never equals the chosen sign. -/
def Adm (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) {N : ℕ} (σ : Fin N → Bool) : Prop :=
  Good a c u₀ R (sigmaExtN σ) N ∧
    ∀ m < N, ¬ (fun w => Lf a c u₀ R (sigmaExtN σ) m w - sgn (sigmaExtN σ m)) =ᶠ[𝓝[≠] (0:ℂ)] 0

lemma meromorphicAt_stepLam {a : ℝ} {Y : ℂ → ℂ × ℂ} {ρY : ℝ} :
    MeromorphicAt (stepLam a Y ρY) 0 := by
  unfold stepLam
  by_cases h : ∃ S : StepOut a Y ρY, True
  · rw [dif_pos h]; exact h.choose.hlam_m
  · rw [dif_neg h]; exact MeromorphicAt.const 0 0

lemma exists_analyticOnNhd_stepLam {a : ℝ} {Y : ℂ → ℂ × ℂ} {ρY : ℝ} :
    ∃ ρL : ℝ, 0 < ρL ∧ AnalyticOnNhd ℂ (stepLam a Y ρY) (ball 0 ρL \ {0}) := by
  unfold stepLam
  by_cases h : ∃ S : StepOut a Y ρY, True
  · rw [dif_pos h]; exact ⟨h.choose.ρ, h.choose.hρ, h.choose.hlam_an⟩
  · rw [dif_neg h]
    refine ⟨1, one_pos, fun z _ => analyticAt_const⟩

/-- A positive radius on which `Lf σ m - sgn (σ m)` does not vanish, when `Adm σ`. -/
noncomputable def etaBad (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) {N : ℕ}
    (σ : Fin N → Bool) (m : ℕ) : ℝ := by
  classical
  exact if h : ∃ η : ℝ, 0 < η ∧
      ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < η → Lf a c u₀ R (sigmaExtN σ) m w - sgn (sigmaExtN σ m) ≠ 0
  then h.choose else 1

lemma etaBad_spec {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} {σ : Fin N → Bool} {m : ℕ}
    (hσ : Adm a c u₀ R σ) (hm : m < N) :
    (∃ h : ∃ η : ℝ, 0 < η ∧ ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < η →
        Lf a c u₀ R (sigmaExtN σ) m w - sgn (sigmaExtN σ m) ≠ 0,
      True) := by
  have hne := hσ.2 m hm
  have hm_m : MeromorphicAt (Lf a c u₀ R (sigmaExtN σ) m) 0 := meromorphicAt_stepLam
  obtain ⟨ρL, hρL0, hρLan⟩ := exists_analyticOnNhd_stepLam (a := a)
    (Y := Xf a c u₀ R (sigmaExtN σ) m) (ρY := seqRho a c u₀ R (sigmaExtN σ) m)
  have hfm : MeromorphicAt (fun w => Lf a c u₀ R (sigmaExtN σ) m w - sgn (sigmaExtN σ m)) 0 :=
    hm_m.sub (MeromorphicAt.const _ 0)
  have hfan : AnalyticOnNhd ℂ (fun w => Lf a c u₀ R (sigmaExtN σ) m w - sgn (sigmaExtN σ m))
      (ball 0 ρL \ {0}) := fun z hz => (hρLan z hz).sub analyticAt_const
  obtain ⟨e, U, ρ', hρ'0, hρ'le, hUan, hU0, hUfac⟩ :=
    meromorphic_factor hρL0 hfm hfan hne
  have hUev : ∀ᶠ y in 𝓝 (0:ℂ), U y ≠ 0 := (hUan 0 (by simpa using hρ'0)).continuousAt.eventually_ne hU0
  rw [Filter.eventually_iff, Metric.mem_nhds_iff] at hUev
  obtain ⟨ρU, hρU0, hρU⟩ := hUev
  refine ⟨⟨min ρ' ρU, lt_min hρ'0 hρU0, fun w hw0 hw => ?_⟩, trivial⟩
  have hwρ' : 0 < ‖w‖ ∧ ‖w‖ < ρ' := ⟨hw0, lt_of_lt_of_le hw (min_le_left _ _)⟩
  have hwρU : ‖w‖ < ρU := lt_of_lt_of_le hw (min_le_right _ _)
  rw [hUfac w hwρ'.1 hwρ'.2]
  exact mul_ne_zero (zpow_ne_zero e (norm_ne_zero_iff.mp hw0.ne')) (hρU (by rwa [Metric.mem_ball, dist_zero_right]))

lemma etaBad_pos {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} {σ : Fin N → Bool} {m : ℕ}
    (hσ : Adm a c u₀ R σ) (hm : m < N) : 0 < etaBad a c u₀ R σ m := by
  obtain ⟨h, -⟩ := etaBad_spec hσ hm
  rw [etaBad, dif_pos h]; exact h.choose_spec.1

lemma etaBad_ne {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} {σ : Fin N → Bool} {m : ℕ}
    (hσ : Adm a c u₀ R σ) (hm : m < N) {w : ℂ} (hw0 : 0 < ‖w‖)
    (hw : ‖w‖ < etaBad a c u₀ R σ m) :
    Lf a c u₀ R (sigmaExtN σ) m w - sgn (sigmaExtN σ m) ≠ 0 := by
  obtain ⟨h, -⟩ := etaBad_spec hσ hm
  have hw' : ‖w‖ < h.choose := by rwa [etaBad, dif_pos h] at hw
  exact h.choose_spec.2 w hw0 hw'

noncomputable def rawRho (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) (σ : ℕ → Bool) (m : ℕ) : ℝ := by
  classical
  exact if h : ∃ S : StepOut a (Xf a c u₀ R σ m) (seqRho a c u₀ R σ m), True then h.choose.ρ else 1

lemma stepOut_exists_of_good {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {σ : ℕ → Bool} {m : ℕ}
    (hpm : XProps a c u₀ R σ m) (hne : ¬ (fun v => rhoPrimeSq a (Xf a c u₀ R σ m v)) =ᶠ[𝓝[≠] (0:ℂ)] 0) :
    ∃ S : StepOut a (Xf a c u₀ R σ m) (seqRho a c u₀ R σ m), True :=
  stepOut_exists hpm.hρ hpm.hm1 hpm.hm2 hpm.han1 hpm.han2 hne

lemma Good.mono {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {σ : ℕ → Bool} {m m' : ℕ}
    (h : Good a c u₀ R σ m) (h' : m' ≤ m) : Good a c u₀ R σ m' :=
  fun k hk => h k (lt_of_lt_of_le hk h')

/-- Radii from the `seqRho` sequence, over all sign sequences (guarded by `Adm`). -/
noncomputable def rhoSeq (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) (N : ℕ) : ℝ := by
  classical
  exact if h : ((Finset.univ : Finset ((Fin N → Bool) × Fin (N+1)))).Nonempty then
    (Finset.univ : Finset ((Fin N → Bool) × Fin (N+1))).inf' h
      (fun p => if Good a c u₀ R (sigmaExtN p.1) (N - (p.2 : ℕ)) then
        (seqRho a c u₀ R (sigmaExtN p.1) (N - (p.2 : ℕ))) ^
          ((((2:ℕ) ^ ((p.2 : ℕ)) : ℕ) : ℝ))⁻¹ else 1)
  else 1

noncomputable def rhoBad (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) (N : ℕ) : ℝ := by
  classical
  exact if h : ((Finset.univ : Finset ((Fin N → Bool) × Fin N))).Nonempty then
    (Finset.univ : Finset ((Fin N → Bool) × Fin N)).inf' h
      (fun p => if Adm a c u₀ R p.1 then
        (etaBad a c u₀ R p.1 (p.2 : ℕ)) ^ ((((2:ℕ) ^ (N - ((p.2 : ℕ)) - 1) : ℕ) : ℝ))⁻¹ else 1)
  else 1

noncomputable def rhoLf (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) (N : ℕ) : ℝ := by
  classical
  exact if h : ((Finset.univ : Finset ((Fin N → Bool) × Fin N))).Nonempty then
    (Finset.univ : Finset ((Fin N → Bool) × Fin N)).inf' h
      (fun p => if Good a c u₀ R (sigmaExtN p.1) ((p.2 : ℕ) + 1) then
        (rawRho a c u₀ R (sigmaExtN p.1) (p.2 : ℕ)) ^
          ((((2:ℕ) ^ (N - ((p.2 : ℕ)) - 1) : ℕ) : ℝ))⁻¹ else 1)
  else 1

noncomputable def rhoFin' (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) (N : ℕ) : ℝ :=
  min (1/2) (min (min (rhoSeq a c u₀ R N) (rhoBad a c u₀ R N)) (rhoLf a c u₀ R N))

lemma rhoSeq_pos {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} (hR : 0 < R)
    (hc : AnalyticOnNhd ℂ c (ball u₀ R)) : 0 < rhoSeq a c u₀ R N := by
  rw [rhoSeq]
  split_ifs with hh
  · refine (Finset.lt_inf'_iff hh).mpr (fun p _ => ?_)
    by_cases hp : Good a c u₀ R (sigmaExtN p.1) (N - (p.2:ℕ))
    · rw [if_pos hp]
      exact Real.rpow_pos_of_pos (XProps.hρ (XProps_of_good hR hc
        (sigmaExtN p.1) (N - (p.2:ℕ)) hp)) _
    · rw [if_neg hp]; norm_num
  · norm_num

lemma rhoBad_pos (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) (N : ℕ) :
    0 < rhoBad a c u₀ R N := by
  rw [rhoBad]
  split_ifs with hh
  · refine (Finset.lt_inf'_iff hh).mpr (fun p _ => ?_)
    by_cases hp : Adm a c u₀ R p.1
    · rw [if_pos hp]
      exact Real.rpow_pos_of_pos (etaBad_pos hp (p.2.isLt)) _
    · rw [if_neg hp]; norm_num
  · norm_num

lemma rhoLf_pos {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} (hR : 0 < R)
    (hc : AnalyticOnNhd ℂ c (ball u₀ R)) : 0 < rhoLf a c u₀ R N := by
  rw [rhoLf]
  split_ifs with hh
  · refine (Finset.lt_inf'_iff hh).mpr (fun p _ => ?_)
    by_cases hp : Good a c u₀ R (sigmaExtN p.1) ((p.2:ℕ)+1)
    · rw [if_pos hp]
      have hex := stepOut_exists_of_good
        (XProps_of_good hR hc (sigmaExtN p.1) (p.2:ℕ) (Good.mono hp (by omega : (p.2:ℕ) ≤ (p.2:ℕ)+1)))
        (hp (p.2:ℕ) (by omega : (p.2:ℕ) < (p.2:ℕ)+1))
      rw [rawRho, dif_pos hex]
      exact Real.rpow_pos_of_pos hex.choose.hρ _
    · rw [if_neg hp]; norm_num
  · norm_num

lemma rhoFin'_pos {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} (hR : 0 < R)
    (hc : AnalyticOnNhd ℂ c (ball u₀ R)) : 0 < rhoFin' a c u₀ R N :=
  lt_min (by norm_num) (lt_min (lt_min (rhoSeq_pos hR hc) (rhoBad_pos a c u₀ R N))
    (rhoLf_pos hR hc))

lemma rhoFin'_le_half {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} :
    rhoFin' a c u₀ R N ≤ 1/2 := min_le_left _ _

lemma rhoFin'_le_seq {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} :
    rhoFin' a c u₀ R N ≤ rhoSeq a c u₀ R N :=
  le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))

lemma rhoFin'_le_bad {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} :
    rhoFin' a c u₀ R N ≤ rhoBad a c u₀ R N :=
  le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))

lemma rhoFin'_le_lf {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} :
    rhoFin' a c u₀ R N ≤ rhoLf a c u₀ R N :=
  le_trans (min_le_right _ _) (min_le_right _ _)

lemma Xf_succ {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {σ : ℕ → Bool} {m : ℕ}
    (h : ∃ S : StepOut a (Xf a c u₀ R σ m) (seqRho a c u₀ R σ m), True) :
    Xf a c u₀ R σ (m+1) = fun w => paramΛ a (Xf a c u₀ R σ m (w ^ 2))
      (sgn (σ m) * Lf a c u₀ R σ m w) := by
  rw [Xf, seqP_succ]
  unfold stepOut Lf stepLam
  simp only [dif_pos h]

lemma seqRho_succ {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {σ : ℕ → Bool} {m : ℕ}
    (h : ∃ S : StepOut a (Xf a c u₀ R σ m) (seqRho a c u₀ R σ m), True) :
    seqRho a c u₀ R σ (m+1) = (h.choose).ρ := by
  rw [seqRho, seqP_succ]
  unfold stepOut
  rw [dif_pos h]

lemma rawRho_eq {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {σ : ℕ → Bool} {m : ℕ}
    (h : ∃ S : StepOut a (Xf a c u₀ R σ m) (seqRho a c u₀ R σ m), True) :
    rawRho a c u₀ R σ m = (h.choose).ρ := by
  rw [rawRho]; rw [dif_pos h]

lemma Lf_eq {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {σ : ℕ → Bool} {m : ℕ}
    (h : ∃ S : StepOut a (Xf a c u₀ R σ m) (seqRho a c u₀ R σ m), True) :
    Lf a c u₀ R σ m = (h.choose).lam := by
  rw [Lf, stepLam]; rw [dif_pos h]

lemma Lf_sq {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {σ : ℕ → Bool} {m : ℕ}
    (h : ∃ S : StepOut a (Xf a c u₀ R σ m) (seqRho a c u₀ R σ m), True) :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < rawRho a c u₀ R σ m →
      Lf a c u₀ R σ m w ^ 2 = rhoPrimeSq a (Xf a c u₀ R σ m (w ^ 2)) := by
  intro w hw0 hw
  have hw' : ‖w‖ < (h.choose).ρ := by rwa [rawRho_eq h] at hw
  have hg : Lf a c u₀ R σ m w = (h.choose).lam w := by rw [Lf_eq h]
  rw [hg]
  exact h.choose.hlam_sq w hw0 hw'

lemma Lf_ne {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {σ : ℕ → Bool} {m : ℕ}
    (h : ∃ S : StepOut a (Xf a c u₀ R σ m) (seqRho a c u₀ R σ m), True) :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < rawRho a c u₀ R σ m → Lf a c u₀ R σ m w ≠ 0 := by
  intro w hw0 hw
  have hw' : ‖w‖ < (h.choose).ρ := by rwa [rawRho_eq h] at hw
  have hg : Lf a c u₀ R σ m w = (h.choose).lam w := by rw [Lf_eq h]
  rw [hg]
  exact h.choose.hlam_ne w hw0 hw'

lemma Lf_an {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {σ : ℕ → Bool} {m : ℕ}
    (h : ∃ S : StepOut a (Xf a c u₀ R σ m) (seqRho a c u₀ R σ m), True) :
    AnalyticOnNhd ℂ (Lf a c u₀ R σ m) (ball 0 (rawRho a c u₀ R σ m) \ {0}) := by
  have hg : Lf a c u₀ R σ m = (h.choose).lam := Lf_eq h
  have hr : rawRho a c u₀ R σ m = (h.choose).ρ := rawRho_eq h
  rw [hg, hr]
  exact h.choose.hlam_an

lemma rhoSeq_le_apply {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ}
    {σ : Fin N → Bool} (j : Fin (N+1)) (hσ : Good a c u₀ R (sigmaExtN σ) (N - (j:ℕ))) :
    rhoSeq a c u₀ R N ≤ (seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ))) ^
      ((((2:ℕ) ^ ((j:ℕ)) : ℕ) : ℝ))⁻¹ := by
  classical
  rw [rhoSeq]
  split_ifs with hh
  · refine le_trans (Finset.inf'_le
      (fun p : (Fin N → Bool) × Fin (N+1) => if Good a c u₀ R (sigmaExtN p.1) (N - (p.2:ℕ)) then
        (seqRho a c u₀ R (sigmaExtN p.1) (N - (p.2:ℕ))) ^ ((((2:ℕ) ^ ((p.2:ℕ)) : ℕ) : ℝ))⁻¹ else 1)
      (Finset.mem_univ (σ, j))) ?_
    rw [if_pos hσ]
  · exact absurd ⟨(σ, j), Finset.mem_univ _⟩ hh

lemma rhoBad_le_apply {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ}
    {σ : Fin N → Bool} (hσ : Adm a c u₀ R σ) (m : Fin N) :
    rhoBad a c u₀ R N ≤ (etaBad a c u₀ R σ (m:ℕ)) ^
      ((((2:ℕ) ^ (N - (m:ℕ) - 1) : ℕ) : ℝ))⁻¹ := by
  classical
  rw [rhoBad]
  split_ifs with hh
  · refine le_trans (Finset.inf'_le
      (fun p : (Fin N → Bool) × Fin N => if Adm a c u₀ R p.1 then
        (etaBad a c u₀ R p.1 (p.2:ℕ)) ^ ((((2:ℕ) ^ (N - (p.2:ℕ) - 1) : ℕ) : ℝ))⁻¹ else 1)
      (Finset.mem_univ (σ, m))) ?_
    rw [if_pos hσ]
  · exact absurd ⟨(σ, m), Finset.mem_univ _⟩ hh

lemma rhoLf_le_apply {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ}
    {σ : Fin N → Bool} (m : Fin N) (hσ : Good a c u₀ R (sigmaExtN σ) ((m:ℕ)+1)) :
    rhoLf a c u₀ R N ≤ (rawRho a c u₀ R (sigmaExtN σ) (m:ℕ)) ^
      ((((2:ℕ) ^ (N - (m:ℕ) - 1) : ℕ) : ℝ))⁻¹ := by
  classical
  rw [rhoLf]
  split_ifs with hh
  · refine le_trans (Finset.inf'_le
      (fun p : (Fin N → Bool) × Fin N => if Good a c u₀ R (sigmaExtN p.1) ((p.2:ℕ)+1) then
        (rawRho a c u₀ R (sigmaExtN p.1) (p.2:ℕ)) ^ ((((2:ℕ) ^ (N - (p.2:ℕ) - 1) : ℕ) : ℝ))⁻¹ else 1)
      (Finset.mem_univ (σ, m))) ?_
    rw [if_pos hσ]
  · exact absurd ⟨(σ, m), Finset.mem_univ _⟩ hh

lemma sgn_mul_eq_one {b : Bool} {x : ℂ} (h : sgn b * x = 1) : x = sgn b := by
  calc x = sgn b * (sgn b * x) := by rw [← mul_assoc, sgn_mul_sgn, one_mul]
    _ = sgn b := by rw [h, mul_one]

/-! ## 7. The branch families -/

/-- The `j`-th point of the branch of the sign sequence `σ` at parameter `t`
(where `u = u₀ + t^{2^N}`). -/
noncomputable def branchPt (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) {N : ℕ}
    (σ : Fin N → Bool) (t : ℂ) (j : Fin (N+1)) : ℂ × ℂ :=
  Xf a c u₀ R (sigmaExtN σ) (N - (j:ℕ)) (t ^ (2 ^ (j:ℕ)))

lemma branchPt_last {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ}
    (σ : Fin N → Bool) (t : ℂ) :
    branchPt a c u₀ R σ t (Fin.last N) = c (u₀ + t ^ (2 ^ N)) := by
  unfold branchPt
  rw [show N - ((Fin.last N : Fin (N+1)) : ℕ) = 0 from by simp]
  rw [show (2:ℕ) ^ (((Fin.last N : Fin (N+1)) : ℕ)) = 2^N from by simp]
  rw [Xf_zero]

lemma hasGood_of_adm {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ}
    {σ : Fin N → Bool} (hσ : Adm a c u₀ R σ) (m : ℕ) (hm : m ≤ N) :
    Good a c u₀ R (sigmaExtN σ) m :=
  Good.mono hσ.1 hm

lemma branchPt_le_seqRho {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ}
    (hR : 0 < R) (hc : AnalyticOnNhd ℂ c (ball u₀ R)) {σ : Fin N → Bool}
    (hσ : Adm a c u₀ R σ) {t : ℂ} (ht : ‖t‖ < rhoFin' a c u₀ R N) (ht0 : t ≠ 0)
    (j : Fin (N+1)) :
    t ^ (2 ^ (j:ℕ)) ∈ ball 0 (seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ))) \ {0} := by
  have hNle : N - (j:ℕ) ≤ N := Nat.sub_le _ _
  have hseqpos : 0 < seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ)) :=
    XProps.hρ (XProps_of_good hR hc (sigmaExtN σ) (N - (j:ℕ))
      (Good.mono hσ.1 hNle))
  have hle : rhoFin' a c u₀ R N ≤ (seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ))) ^
      ((((2:ℕ) ^ ((j:ℕ)) : ℕ) : ℝ))⁻¹ :=
    le_trans (rhoFin'_le_seq) (rhoSeq_le_apply j (Good.mono hσ.1 (Nat.sub_le N (j:ℕ))))
  have hlt : ‖t‖ ^ (2 ^ (j:ℕ)) < seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ)) := by
    have hrp : ((seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ))) ^
        ((((2:ℕ) ^ ((j:ℕ)) : ℕ) : ℝ))⁻¹) ^ (2 ^ (j:ℕ)) = seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hseqpos.le]
      have h1 : ((((2:ℕ) ^ ((j:ℕ)) : ℕ) : ℝ))⁻¹ * (((2:ℕ) ^ ((j:ℕ)) : ℕ) : ℝ) = 1 := by
        rw [inv_mul_cancel₀]
        positivity
      rw [h1, Real.rpow_one]
    calc ‖t‖ ^ (2 ^ (j:ℕ)) < (rhoFin' a c u₀ R N) ^ (2 ^ (j:ℕ)) :=
          pow_lt_pow_left₀ ht (norm_nonneg t) (by positivity)
      _ ≤ ((seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ))) ^
            ((((2:ℕ) ^ ((j:ℕ)) : ℕ) : ℝ))⁻¹) ^ (2 ^ (j:ℕ)) :=
          pow_le_pow_left₀ (rhoFin'_pos hR hc).le hle _
      _ = seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ)) := hrp
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_pow]
    exact hlt
  · simp only [Set.mem_singleton_iff]
    exact pow_ne_zero _ ht0

lemma analyticAt_pow_id {t : ℂ} (n : ℕ) : AnalyticAt ℂ (fun z : ℂ => z ^ n) t := by
  have h : AnalyticAt ℂ (id ^ n : ℂ → ℂ) t := analyticAt_id.pow n
  refine AnalyticAt.congr h ?_
  filter_upwards with z
  rfl

lemma rpow_bound {X ρ : ℝ} (hX : 0 ≤ X) (hρ : 0 ≤ ρ) {k : ℕ} (hk : 0 < k)
    (h : ρ ≤ X ^ (((k:ℝ))⁻¹)) : ρ ^ k ≤ X := by
  have hk0 : (k:ℝ) ≠ 0 := by positivity
  calc ρ ^ k ≤ (X ^ (((k:ℝ))⁻¹)) ^ k := pow_le_pow_left₀ hρ h k
    _ = X ^ (((k:ℝ))⁻¹ * (k:ℝ)) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hX]
    _ = X ^ (1:ℝ) := by rw [inv_mul_cancel₀ hk0]
    _ = X := Real.rpow_one X

lemma rawRho_pos {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} {σ : Fin N → Bool}
    (hR : 0 < R) (hc : AnalyticOnNhd ℂ c (ball u₀ R)) {m : ℕ}
    (hm : m < N) (hG : Good a c u₀ R (sigmaExtN σ) (m+1)) :
    0 < rawRho a c u₀ R (sigmaExtN σ) m := by
  have hex := stepOut_exists_of_good
    (XProps_of_good hR hc (sigmaExtN σ) m (Good.mono hG (by omega : m ≤ m+1)))
    (hG m (by omega : m < m+1))
  rw [rawRho_eq hex]
  exact hex.choose.hρ

lemma branchPt_analytic {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ}
    (hR : 0 < R) (hc : AnalyticOnNhd ℂ c (ball u₀ R)) {σ : Fin N → Bool}
    (hσ : Adm a c u₀ R σ) (j : Fin (N+1)) :
    AnalyticOnNhd ℂ (fun t => (branchPt a c u₀ R σ t j).1) (ball 0 (rhoFin' a c u₀ R N) \ {0}) ∧
    AnalyticOnNhd ℂ (fun t => (branchPt a c u₀ R σ t j).2) (ball 0 (rhoFin' a c u₀ R N) \ {0}) := by
  have hP := XProps_of_good hR hc (sigmaExtN σ) (N - (j:ℕ))
    (hasGood_of_adm hσ (N - (j:ℕ)) (Nat.sub_le _ _))
  constructor <;> intro t ht
  · have ht0 : t ≠ 0 := by simpa using ht.2
    have htb : ‖t‖ < rhoFin' a c u₀ R N := by
      have h := ht.1; rwa [Metric.mem_ball, dist_zero_right] at h
    have hw := branchPt_le_seqRho hR hc hσ htb ht0 j
    exact (hP.han1 _ hw).comp (f := fun z : ℂ => z ^ (2^(j:ℕ))) (analyticAt_pow_id _)
  · have ht0 : t ≠ 0 := by simpa using ht.2
    have htb : ‖t‖ < rhoFin' a c u₀ R N := by
      have h := ht.1; rwa [Metric.mem_ball, dist_zero_right] at h
    have hw := branchPt_le_seqRho hR hc hσ htb ht0 j
    exact (hP.han2 _ hw).comp (f := fun z : ℂ => z ^ (2^(j:ℕ))) (analyticAt_pow_id _)

lemma branchPt_reg {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ}
    (hR : 0 < R) (hc : AnalyticOnNhd ℂ c (ball u₀ R)) {σ : Fin N → Bool}
    (hσ : Adm a c u₀ R σ) {t : ℂ} (ht : ‖t‖ < rhoFin' a c u₀ R N) (ht0 : t ≠ 0) (j : Fin N) :
    RegPair a (branchPt a c u₀ R σ t (Fin.castSucc j))
      (branchPt a c u₀ R σ t (Fin.succ j)) := by
  set m : ℕ := N - 1 - (j:ℕ) with hm
  have hmN : m < N := by omega
  have hmj : m + 1 = N - (j:ℕ) := by omega
  have hmj2 : N - ((j:ℕ) + 1) = m := by omega
  have hPm := XProps_of_good hR hc (sigmaExtN σ) m (hasGood_of_adm hσ m (le_of_lt hmN))
  have hex := stepOut_exists_of_good hPm (hσ.1 m hmN)
  set w : ℂ := t ^ (2 ^ (j:ℕ)) with hw_def
  have hw0 : 0 < ‖w‖ := by
    rw [hw_def, norm_pow]; exact pow_pos (norm_pos_iff.mpr ht0) _
  have hpowpos : 0 < 2 ^ (j:ℕ) := by positivity
  have hNm : N - m - 1 = (j:ℕ) := by omega
  have hraw : ‖w‖ < rawRho a c u₀ R (sigmaExtN σ) m := by
    have hX : 0 ≤ rawRho a c u₀ R (sigmaExtN σ) m :=
      (rawRho_pos hR hc hmN (Good.mono hσ.1 (by omega : m+1 ≤ N))).le
    have hb := le_trans (rhoFin'_le_lf) (rhoLf_le_apply ⟨m, hmN⟩ (Good.mono hσ.1 (by omega : m + 1 ≤ N)))
    rw [hNm, Fin.val_mk] at hb
    have hb' := rpow_bound (ρ := rhoFin' a c u₀ R N) hX (rhoFin'_pos hR hc).le hpowpos hb
    rw [hw_def, norm_pow]
    calc ‖t‖ ^ (2 ^ (j:ℕ)) < (rhoFin' a c u₀ R N) ^ (2 ^ (j:ℕ)) :=
          pow_lt_pow_left₀ ht (norm_nonneg t) (by positivity)
      _ ≤ rawRho a c u₀ R (sigmaExtN σ) m := hb'
  have heta : ‖w‖ < etaBad a c u₀ R σ m := by
    have hb := le_trans (rhoFin'_le_bad) (rhoBad_le_apply hσ ⟨m, hmN⟩)
    rw [hNm, Fin.val_mk] at hb
    have hb' := rpow_bound (ρ := rhoFin' a c u₀ R N) (etaBad_pos hσ hmN).le (rhoFin'_pos hR hc).le hpowpos hb
    rw [hw_def, norm_pow]
    calc ‖t‖ ^ (2 ^ (j:ℕ)) < (rhoFin' a c u₀ R N) ^ (2 ^ (j:ℕ)) :=
          pow_lt_pow_left₀ ht (norm_nonneg t) (by positivity)
      _ ≤ etaBad a c u₀ R σ m := hb'
  have hstep := Xf_succ (σ := sigmaExtN σ) (m := m) hex
  have hsq := Lf_sq (σ := sigmaExtN σ) (m := m) hex w hw0 hraw
  have hne := Lf_ne (σ := sigmaExtN σ) (m := m) hex w hw0 hraw
  have hne' := etaBad_ne hσ hmN hw0 heta
  have hlamne : sgn (sigmaExtN σ m) * Lf a c u₀ R (sigmaExtN σ) m w ≠ 1 :=
    fun hc1 => hne' (sub_eq_zero.mpr (sgn_mul_eq_one hc1))
  have hlam0 : sgn (sigmaExtN σ m) * Lf a c u₀ R (sigmaExtN σ) m w ≠ 0 :=
    mul_ne_zero (sgn_ne_zero _) hne
  have hsq' : (sgn (sigmaExtN σ m) * Lf a c u₀ R (sigmaExtN σ) m w) ^ 2
      = rhoPrimeSq a (Xf a c u₀ R (sigmaExtN σ) m (w ^ 2)) := by
    rw [mul_pow, sq, sgn_mul_sgn, one_mul]; exact hsq
  have hreg := regPair_paramΛ (Q := Xf a c u₀ R (sigmaExtN σ) m (w ^ 2))
    (lam := sgn (sigmaExtN σ m) * Lf a c u₀ R (sigmaExtN σ) m w) hlam0 hlamne hsq'
  have key1 : Xf a c u₀ R (sigmaExtN σ) (m + 1) w
      = branchPt a c u₀ R σ t (Fin.castSucc j) := by
    rw [hmj, hw_def]; rfl
  have key2 : Xf a c u₀ R (sigmaExtN σ) m (w ^ 2)
      = branchPt a c u₀ R σ t (Fin.succ j) := by
    have h1 : w ^ 2 = t ^ ((2:ℕ) ^ ((j:ℕ) + 1)) := by
      rw [hw_def, ← pow_mul]; ring_nf
    rw [h1, ← hmj2]; rfl
  rw [← key1, ← key2]
  rw [hstep]
  simp only []
  exact hreg

lemma isPreconnected_punctured_ball {ρ : ℝ} (hρ : 0 < ρ) :
    IsPreconnected (ball (0:ℂ) ρ \ {0}) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ) * cexp ((p.2 : ℂ) * I))
      (Set.Ioo 0 ρ ×ˢ Set.univ) := by
    apply Continuous.continuousOn
    exact (continuous_ofReal.comp continuous_fst).mul
      (continuous_exp.comp ((continuous_ofReal.comp continuous_snd).mul continuous_const))
  have himg : (fun p : ℝ × ℝ => (p.1 : ℂ) * cexp (p.2 * I)) '' (Set.Ioo 0 ρ ×ˢ Set.univ)
      = ball (0:ℂ) ρ \ {0} := by
    ext z
    constructor
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      have h1 : 0 < p.1 := hp1.1
      have h2 : p.1 < ρ := hp1.2
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
        simpa [abs_of_pos h1] using h2
      · simp only [Set.mem_singleton_iff]
        intro hc
        rw [mul_eq_zero] at hc
        rcases hc with hc | hc
        · exact h1.ne' (Complex.ofReal_injective (by simpa using hc))
        · exact Complex.exp_ne_zero _ hc
    · intro hz
      have hzn : z ≠ 0 := by simpa using hz.2
      have hzb : ‖z‖ < ρ := by
        have h := hz.1; rwa [Metric.mem_ball, dist_zero_right] at h
      refine ⟨(‖z‖, z.arg), ⟨⟨norm_pos_iff.mpr hzn, hzb⟩, trivial⟩, ?_⟩
      · exact Complex.norm_mul_exp_arg_mul_I z
  rw [← himg]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ hcont

lemma eqOn_zero_of_eventually_zero {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : AnalyticOnNhd ℂ f (ball 0 ρ \ {0})) (hz : f =ᶠ[𝓝[≠] (0:ℂ)] 0) :
    ∀ z ∈ ball 0 ρ \ {0}, f z = 0 := by
  have hev : ∀ᶠ z in 𝓝 (0:ℂ), z ∈ ({0}ᶜ : Set ℂ) → f z = 0 := by
    have h := hz; rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at h; exact h
  rw [Filter.eventually_iff, Metric.mem_nhds_iff] at hev
  obtain ⟨ε, hε0, hε⟩ := hev
  have hερ : 0 < min ε ρ := lt_min hε0 hρ
  set z₁ : ℂ := (((min ε ρ)/2 : ℝ) : ℂ) with hz₁def
  have h0 : (0:ℝ) ≤ min ε ρ / 2 := by linarith [hερ]
  have hz₁norm : ‖z₁‖ = min ε ρ / 2 := by
    rw [hz₁def]
    have h1 : ‖(((min ε ρ / 2 : ℝ)) : ℂ)‖ ^ 2 = (min ε ρ / 2)^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
    nlinarith [norm_nonneg ((((min ε ρ / 2 : ℝ)) : ℂ))]
  have hz₁ne : z₁ ≠ 0 := by
    rw [← norm_pos_iff]
    rw [hz₁norm]
    linarith [hερ]
  have hz₁mem : z₁ ∈ ball (0:ℂ) ρ \ {0} := by
    refine ⟨?_, by simpa using hz₁ne⟩
    rw [Metric.mem_ball, dist_zero_right, hz₁norm]
    linarith [min_le_right ε ρ, hερ]
  have hz₁eq : f =ᶠ[𝓝 z₁] 0 := by
    filter_upwards [Metric.ball_mem_nhds z₁ (by linarith [hερ] : (0:ℝ) < min ε ρ / 4),
      isOpen_ne.mem_nhds hz₁ne] with y hy hyne
    exact hε (by
      rw [Metric.mem_ball, dist_zero_right]
      rw [Metric.mem_ball] at hy
      calc ‖y‖ ≤ ‖y - z₁‖ + ‖z₁‖ := by
            conv_lhs => rw [← sub_add_cancel y z₁]
            exact norm_add_le _ _
        _ < min ε ρ / 4 + min ε ρ / 2 := by
            have hy' : ‖y - z₁‖ < min ε ρ / 4 := by rw [← dist_eq_norm]; exact hy
            rw [hz₁norm]
            linarith
        _ < ε := by linarith [min_le_left ε ρ, hερ]) (by simpa using hyne)
  exact fun z hz => AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hf
    (isPreconnected_punctured_ball hρ) hz₁mem hz₁eq hz

lemma seqP_congr {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {σ σ' : ℕ → Bool} :
    ∀ m, (∀ k < m, σ k = σ' k) → seqP a c u₀ R σ m = seqP a c u₀ R σ' m
  | 0, _ => rfl
  | (m+1), h => by
    have ih := seqP_congr (a := a) (c := c) (u₀ := u₀) (R := R) (σ := σ) (σ' := σ') m (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have hX : Xf a c u₀ R σ m = Xf a c u₀ R σ' m := by unfold Xf; rw [ih]
    have hρ : seqRho a c u₀ R σ m = seqRho a c u₀ R σ' m := by unfold seqRho; rw [ih]
    show stepOut a (σ m) (Xf a c u₀ R σ m) (seqRho a c u₀ R σ m)
      = stepOut a (σ' m) (Xf a c u₀ R σ' m) (seqRho a c u₀ R σ' m)
    rw [hX, hρ, h m (Nat.lt_succ_self m)]

lemma Xf_congr {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {σ σ' : ℕ → Bool} {m : ℕ}
    (h : ∀ k < m, σ k = σ' k) : Xf a c u₀ R σ m = Xf a c u₀ R σ' m := by
  unfold Xf; rw [seqP_congr m h]

lemma seqRho_congr {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {σ σ' : ℕ → Bool} {m : ℕ}
    (h : ∀ k < m, σ k = σ' k) : seqRho a c u₀ R σ m = seqRho a c u₀ R σ' m := by
  unfold seqRho; rw [seqP_congr m h]

lemma Lf_congr {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {σ σ' : ℕ → Bool} {m : ℕ}
    (h : ∀ k < m, σ k = σ' k) : Lf a c u₀ R σ m = Lf a c u₀ R σ' m := by
  unfold Lf; rw [Xf_congr h, seqRho_congr h]

lemma Good_congr {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {σ σ' : ℕ → Bool} {m : ℕ}
    (h : ∀ k < m, σ k = σ' k) : Good a c u₀ R σ m ↔ Good a c u₀ R σ' m := by
  constructor <;> intro hg k hk
  · rw [← Xf_congr (σ := σ) (σ' := σ') (m := k) (fun i hi => h i (lt_trans hi hk))]
    exact hg k hk
  · rw [Xf_congr (σ := σ) (σ' := σ') (m := k) (fun i hi => h i (lt_trans hi hk))]
    exact hg k hk

/-! ## 8. Coverage -/

noncomputable def covSign (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) {N : ℕ}
    (P : Fin (N+1) → ℂ × ℂ)
    (hreg : ∀ j : Fin N, RegPair a (P (Fin.castSucc j)) (P (Fin.succ j)))
    (t : ℂ) (σ : Fin N → Bool) (m : ℕ) (hm : m < N) : Bool := by
  classical
  exact if (Classical.choose (exists_paramΛ_of_regPair (hreg ⟨N - m - 1, by omega⟩)))
      = Lf a c u₀ R (sigmaExtN σ) m (t ^ (2 ^ (N - m - 1))) then true else false

lemma covSign_spec {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ}
    {P : Fin (N+1) → ℂ × ℂ}
    {hreg : ∀ j : Fin N, RegPair a (P (Fin.castSucc j)) (P (Fin.succ j))}
    {t : ℂ} {σ : Fin N → Bool} {m : ℕ} (hm : m < N) :
    covSign a c u₀ R P hreg t σ m hm = true ↔
      (Classical.choose (exists_paramΛ_of_regPair (hreg ⟨N - m - 1, by omega⟩)))
        = Lf a c u₀ R (sigmaExtN σ) m (t ^ (2 ^ (N - m - 1))) := by
  classical
  unfold covSign
  by_cases hc : (Classical.choose (exists_paramΛ_of_regPair (hreg ⟨N - m - 1, by omega⟩)))
      = Lf a c u₀ R (sigmaExtN σ) m (t ^ (2 ^ (N - m - 1)))
  · rw [if_pos hc]; exact ⟨fun _ => hc, fun _ => rfl⟩
  · rw [if_neg hc]
    exact ⟨fun hh => absurd hh (by simp), fun hh => absurd hh hc⟩

noncomputable def covAcc (a : ℝ) (c : ℂ → ℂ × ℂ) (u₀ : ℂ) (R : ℝ) {N : ℕ}
    (P : Fin (N+1) → ℂ × ℂ)
    (hreg : ∀ j : Fin N, RegPair a (P (Fin.castSucc j)) (P (Fin.succ j)))
    (t : ℂ) : ℕ → (Fin N → Bool) :=
  Nat.rec (fun _ => false) (fun m prev =>
    if hm : m < N then Function.update prev ⟨m, hm⟩
      (covSign a c u₀ R P hreg t prev m hm) else prev)

lemma covAcc_succ {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ}
    {P : Fin (N+1) → ℂ × ℂ}
    {hreg : ∀ j : Fin N, RegPair a (P (Fin.castSucc j)) (P (Fin.succ j))}
    {t : ℂ} {m : ℕ} :
    covAcc a c u₀ R P hreg t (m+1) = (if hm : m < N then
      Function.update (covAcc a c u₀ R P hreg t m) ⟨m, hm⟩
        (covSign a c u₀ R P hreg t (covAcc a c u₀ R P hreg t m) m hm)
      else covAcc a c u₀ R P hreg t m) := by
  show (if ht : m < N then Function.update (covAcc a c u₀ R P hreg t m) ⟨m, ht⟩
      (covSign a c u₀ R P hreg t (covAcc a c u₀ R P hreg t m) m ht)
      else covAcc a c u₀ R P hreg t m) = _
  rfl

lemma covAcc_succ_apply {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ}
    {P : Fin (N+1) → ℂ × ℂ}
    {hreg : ∀ j : Fin N, RegPair a (P (Fin.castSucc j)) (P (Fin.succ j))}
    {t : ℂ} {m : ℕ} {k : Fin N} (hk : (k:ℕ) ≠ m) :
    covAcc a c u₀ R P hreg t (m+1) k = covAcc a c u₀ R P hreg t m k := by
  rw [covAcc_succ]
  split_ifs with hm
  · rw [Function.update_apply, if_neg]
    intro hc; simp only [Fin.ext_iff, Fin.val_mk] at hc; exact hk hc
  · rfl

lemma covAcc_prefix {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ}
    {P : Fin (N+1) → ℂ × ℂ}
    {hreg : ∀ j : Fin N, RegPair a (P (Fin.castSucc j)) (P (Fin.succ j))}
    {t : ℂ} :
    ∀ {m m' : ℕ}, m ≤ m' → ∀ k : Fin N, (k:ℕ) < m →
      covAcc a c u₀ R P hreg t m' k = covAcc a c u₀ R P hreg t m k := by
  intro m m' hle
  induction m' with
  | zero =>
    intro k hk
    have : m = 0 := by omega
    subst this; rfl
  | succ j ih =>
    intro k hk
    by_cases hkm : (k:ℕ) = j
    · have hmj : m = j+1 := by omega
      subst hmj; rfl
    · rw [covAcc_succ_apply (m := j) hkm]
      by_cases hjk : m ≤ j
      · exact ih hjk k hk
      · have hmj : m = j + 1 := by omega
        subst hmj
        exact (covAcc_succ_apply (m := j) hkm).symm

lemma tmem_seqRho {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} (hR : 0 < R)
    (hc : AnalyticOnNhd ℂ c (ball u₀ R)) {σ : Fin N → Bool} {t : ℂ}
    (ht : ‖t‖ < rhoFin' a c u₀ R N) (ht0 : t ≠ 0) (j : Fin (N+1))
    (hG : Good a c u₀ R (sigmaExtN σ) (N - (j:ℕ))) :
    t ^ (2 ^ (j:ℕ)) ∈ ball 0 (seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ))) \ {0} := by
  have hseqpos : 0 < seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ)) :=
    XProps.hρ (XProps_of_good hR hc (sigmaExtN σ) (N - (j:ℕ)) hG)
  have hle : rhoFin' a c u₀ R N ≤ (seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ))) ^
      ((((2:ℕ) ^ ((j:ℕ)) : ℕ) : ℝ))⁻¹ :=
    le_trans (rhoFin'_le_seq) (rhoSeq_le_apply j hG)
  have hlt : ‖t‖ ^ (2 ^ (j:ℕ)) < seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ)) := by
    have hrp : ((seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ))) ^
        ((((2:ℕ) ^ ((j:ℕ)) : ℕ) : ℝ))⁻¹) ^ (2 ^ (j:ℕ))
        = seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hseqpos.le]
      rw [inv_mul_cancel₀ (by positivity : (((2:ℕ) ^ ((j:ℕ)) : ℕ) : ℝ) ≠ 0), Real.rpow_one]
    calc ‖t‖ ^ (2 ^ (j:ℕ)) < (rhoFin' a c u₀ R N) ^ (2 ^ (j:ℕ)) :=
          pow_lt_pow_left₀ ht (norm_nonneg t) (by positivity)
      _ ≤ ((seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ))) ^
            ((((2:ℕ) ^ ((j:ℕ)) : ℕ) : ℝ))⁻¹) ^ (2 ^ (j:ℕ)) :=
          pow_le_pow_left₀ (rhoFin'_pos hR hc).le hle _
      _ = seqRho a c u₀ R (sigmaExtN σ) (N - (j:ℕ)) := hrp
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_pow]
    exact hlt
  · simp only [Set.mem_singleton_iff]
    exact pow_ne_zero _ ht0

lemma tmem_rawRho {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {N : ℕ} (hR : 0 < R)
    (hc : AnalyticOnNhd ℂ c (ball u₀ R)) {σ : Fin N → Bool} {t : ℂ}
    (ht : ‖t‖ < rhoFin' a c u₀ R N) (m : Fin N)
    (hG : Good a c u₀ R (sigmaExtN σ) ((m:ℕ)+1)) :
    ‖t ^ (2 ^ (N - 1 - (m:ℕ)))‖ < rawRho a c u₀ R (sigmaExtN σ) (m:ℕ) := by
  have hk : 0 < 2 ^ (N - 1 - (m:ℕ)) := by positivity
  have hX : 0 ≤ rawRho a c u₀ R (sigmaExtN σ) (m:ℕ) :=
    (rawRho_pos hR hc (by omega : (m:ℕ) < N) hG).le
  have hb := le_trans (rhoFin'_le_lf) (rhoLf_le_apply m hG)
  have hNm : N - ((m:ℕ)) - 1 = N - 1 - (m:ℕ) := by omega
  rw [hNm] at hb
  have hb' := rpow_bound hX (rhoFin'_pos hR hc).le hk hb
  rw [norm_pow]
  exact lt_of_lt_of_le (pow_lt_pow_left₀ ht (norm_nonneg t) (by positivity)) hb'

lemma radicand_analytic {a : ℝ} {c : ℂ → ℂ × ℂ} {u₀ : ℂ} {R : ℝ} {σ : ℕ → Bool} {m : ℕ}
    (hpm : XProps a c u₀ R σ m) :
    AnalyticOnNhd ℂ (fun w => rhoPrimeSq a (Xf a c u₀ R σ m w))
      (ball 0 (seqRho a c u₀ R σ m) \ {0}) := by
  intro v hv
  have h : AnalyticAt ℂ (fun w : ℂ => ((Xf a c u₀ R σ m w).1 + (((a/2:ℝ)):ℂ)) ^ 2
      + (Xf a c u₀ R σ m w).2 ^ 2) v :=
    (((hpm.han1 v hv).add (analyticAt_const (v := ((a/2:ℝ):ℂ)) (x := v))).pow 2).add
      ((hpm.han2 v hv).pow 2)
  refine AnalyticAt.congr h ?_
  filter_upwards with w
  simp only [rhoPrimeSq]

set_option maxHeartbeats 1600000 in
theorem coverage {a : ℝ} {u₀ : ℂ} {R : ℝ} (hR : 0 < R) {c : ℂ → ℂ × ℂ}
    (hc : AnalyticOnNhd ℂ c (ball u₀ R)) {N : ℕ} {u t : ℂ} (ht : t ^ (2^N) = u - u₀)
    (ht0 : t ≠ 0) (htρ : ‖t‖ < rhoFin' a c u₀ R N)
    (P : Fin (N+1) → ℂ × ℂ) (hP : P (Fin.last N) = c u)
    (hreg : ∀ j : Fin N, RegPair a (P (Fin.castSucc j)) (P (Fin.succ j))) :
    ∃ σ : Fin N → Bool, Adm a c u₀ R σ ∧ ∀ j : Fin (N+1), P j = branchPt a c u₀ R σ t j := by
  classical
  have key : ∀ m, m ≤ N →
      Good a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t m)) m ∧
      P ⟨N - m, by omega⟩ = Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t m)) m
        (t ^ (2 ^ (N - m))) ∧
      (∀ j < m, ¬ (fun w => Lf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t N)) j w
          - sgn ((sigmaExtN (covAcc a c u₀ R P hreg t N)) j)) =ᶠ[𝓝[≠] (0:ℂ)] 0) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun k hk => absurd hk (Nat.not_lt_zero k), ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      have hsub : N - 0 = N := by omega
      rw [show (⟨N - 0, by omega⟩ : Fin (N+1)) = Fin.last N from by
        ext; simp [Fin.last], hP, Xf_zero]
      simp only []
      have : u₀ + t ^ (2 ^ (N - 0)) = u := by rw [hsub, ht]; ring
      rw [this]
    | succ m ih =>
      intro hm
      have hmN : m < N := by omega
      have hprev := ih (by omega : m ≤ N)
      have hsig := covAcc_succ (a := a) (c := c) (u₀ := u₀) (R := R) (P := P) (hreg := hreg)
        (t := t) (m := m)
      rw [dif_pos hmN] at hsig
      have hpref : ∀ k ≤ m, Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) k
          = Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t m)) k := by
        intro k hk
        apply Xf_congr
        intro i hi
        show sigmaExtN (covAcc a c u₀ R P hreg t (m+1)) i = sigmaExtN (covAcc a c u₀ R P hreg t m) i
        rw [sigmaExtN_apply (N := N) _ i (by omega), sigmaExtN_apply (N := N) _ i (by omega)]
        exact covAcc_prefix (m := m) (m' := m+1) (by omega) ⟨i, by omega⟩ (by simp only; omega)
      -- the radicand at level m is not identically zero
      have hradne : ¬ (fun w => rhoPrimeSq a (Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t m)) m w))
          =ᶠ[𝓝[≠] (0:ℂ)] 0 := by
        intro hzero
        have hpm := XProps_of_good hR hc (sigmaExtN (covAcc a c u₀ R P hreg t m)) m
          hprev.1
        have heq := eqOn_zero_of_eventually_zero hpm.hρ (radicand_analytic hpm) hzero
        have hj : N - (N - m) = m := by omega
        have hwm := tmem_seqRho hR hc htρ ht0 ⟨N - m, by omega⟩
          (by rw [hj]; exact hprev.1)
        rw [hj] at hwm
        have hw := heq _ hwm
        rw [show Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t m)) m (t ^ (2 ^ (N - m)))
            = P ⟨N - m, by omega⟩ from hprev.2.1.symm] at hw
        refine (hreg ⟨N - m - 1, by omega⟩).2.2 ?_
        rw [show (Fin.succ ⟨N - m - 1, by omega⟩ : Fin (N+1)) = ⟨N - m, by omega⟩ from by
          ext; simp only [Fin.val_succ, Fin.val_mk]; omega]
        simpa only [rhoPrimeSq] using hw
      -- hence Good at m+1
      have hgood : Good a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) (m+1) := by
        intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
        · have hfun : (fun w => rhoPrimeSq a (Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) k w))
              = (fun w => rhoPrimeSq a (Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t m)) k w)) := by
            funext w
            rw [hpref k (by omega : k ≤ m)]
          rw [hfun]
          exact hprev.1 k hk'
        · rw [hk']
          have hfun : (fun w => rhoPrimeSq a (Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m w))
              = (fun w => rhoPrimeSq a (Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t m)) m w)) := by
            funext w
            rw [hpref m le_rfl]
          rw [hfun]
          exact hradne
      -- the step relation
      have hex1 : ∃ S : StepOut a (Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m)
          (seqRho a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m), True :=
        stepOut_exists_of_good (XProps_of_good hR hc _ m (Good.mono hgood (by omega : m ≤ m+1)))
          (hgood m (by omega : m < m+1))
      have hsteprel := Xf_succ (σ := sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) (m := m) hex1
      -- the chain's lambda
      set hregm := hreg ⟨N - m - 1, by omega⟩ with hregmdef
      have hexists : ∃ lam : ℂ, lam ≠ 0 ∧
          lam ^ 2 = rhoPrimeSq a (P (Fin.succ ⟨N - m - 1, by omega⟩)) ∧
          P (Fin.castSucc ⟨N - m - 1, by omega⟩) = paramΛ a (P (Fin.succ ⟨N - m - 1, by omega⟩)) lam :=
        exists_paramΛ_of_regPair hregm
      set lam : ℂ := Classical.choose hexists with hlamdef
      have hlam2 : lam ^ 2 = rhoPrimeSq a (P (Fin.succ ⟨N - m - 1, by omega⟩)) :=
        (Classical.choose_spec hexists).2.1
      have hlamP : P (Fin.castSucc ⟨N - m - 1, by omega⟩)
          = paramΛ a (P (Fin.succ ⟨N - m - 1, by omega⟩)) lam :=
        (Classical.choose_spec hexists).2.2
      have hPm : P ⟨N - m, by omega⟩
          = Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m
              (t ^ (2 ^ (N - m))) := by
        rw [hprev.2.1, hpref m le_rfl]
      have hPsucc : P (Fin.succ ⟨N - m - 1, by omega⟩) = P ⟨N - m, by omega⟩ := by
        congr 1; ext; simp only [Fin.val_succ, Fin.val_mk]; omega
      have hPcast : P (Fin.castSucc ⟨N - m - 1, by omega⟩) = P ⟨N - m - 1, by omega⟩ :=
        congrArg P (Fin.ext (by simp only [Fin.val_castSucc, Fin.val_mk]))
      have hLfsq := Lf_sq (σ := sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) (m := m) hex1
        (t ^ (2 ^ (N - 1 - m))) (by rw [norm_pow]; exact pow_pos (norm_pos_iff.mpr ht0) _)
        (tmem_rawRho hR hc htρ ⟨m, hmN⟩ hgood)
      have hL2 : (Lf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m
          (t ^ (2 ^ (N - 1 - m)))) ^ 2 = lam ^ 2 := by
        rw [hLfsq, show (t ^ (2 ^ (N - 1 - m))) ^ 2 = t ^ (2 ^ (N - m)) from by
          rw [← pow_mul]; congr 1; rw [← pow_succ]; congr 1; omega]
        rw [← hPm, ← hPsucc, ← hlam2]
      have hcase : lam = Lf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m
            (t ^ (2 ^ (N - 1 - m))) ∨
          lam = -Lf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m
            (t ^ (2 ^ (N - 1 - m))) := by
        have h : (lam - Lf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m
            (t ^ (2 ^ (N - 1 - m)))) * (lam + Lf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m
            (t ^ (2 ^ (N - 1 - m)))) = 0 := by
          linear_combination -hL2
        rcases mul_eq_zero.mp h with h' | h'
        · left; linear_combination h'
        · right; linear_combination h'
      have hsigval : (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m
          = covSign a c u₀ R P hreg t (covAcc a c u₀ R P hreg t m) m hmN := by
        rw [hsig, sigmaExtN_apply (N := N) _ m hmN, Function.update_self]
      have hlamdef2 : lam = Classical.choose (exists_paramΛ_of_regPair
          (hreg ⟨N - m - 1, by omega⟩)) := by
        rw [hlamdef]
      have hsign : sgn ((sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m)
          * Lf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m
            (t ^ (2 ^ (N - 1 - m))) = lam := by
        rw [hsigval]
        have hLfc : Lf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t m)) m
            = Lf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m := by
          apply Lf_congr
          intro i hi
          show sigmaExtN (covAcc a c u₀ R P hreg t m) i
            = sigmaExtN (covAcc a c u₀ R P hreg t (m+1)) i
          rw [sigmaExtN_apply (N := N) _ i (by omega), sigmaExtN_apply (N := N) _ i (by omega)]
          exact (covAcc_prefix (m := m) (m' := m+1) (by omega) ⟨i, by omega⟩ (by simp only; omega)).symm
        have htexp : t ^ (2 ^ (N - m - 1)) = t ^ (2 ^ (N - 1 - m)) := by
          rw [show N - m - 1 = N - 1 - m from by omega]
        by_cases hct : covSign a c u₀ R P hreg t (covAcc a c u₀ R P hreg t m) m hmN = true
        · have hl := (covSign_spec hmN).mp hct
          rw [← hlamdef2, hLfc, htexp] at hl
          rw [hct, ← hl]
          norm_num [sgn]
        · have hne' : lam ≠ Lf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m
              (t ^ (2 ^ (N - 1 - m))) := by
            intro hh
            refine hct ((covSign_spec hmN).mpr ?_)
            rw [← hlamdef2, hLfc, htexp]
            exact hh
          have hneg : lam = -(Lf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m
              (t ^ (2 ^ (N - 1 - m)))) := by
            rcases hcase with h | h
            · exact absurd h hne'
            · exact h
          have hsgn : sgn (covSign a c u₀ R P hreg t (covAcc a c u₀ R P hreg t m) m hmN) = -1 := by
            rw [sgn, if_neg hct]
          rw [hsgn, hneg]
          ring
      refine ⟨hgood, ?_, ?_⟩
      · have hidx : (⟨N - (m+1), by omega⟩ : Fin (N+1)) = Fin.castSucc ⟨N - m - 1, by omega⟩ := by
          ext; simp only [Fin.val_castSucc, Fin.val_mk]; omega
        rw [hidx, hlamP, hsteprel]
        simp only []
        have htexp2 : N - (m+1) = N - 1 - m := by omega
        rw [htexp2]
        rw [show (t ^ (2 ^ (N - 1 - m))) ^ 2 = t ^ (2 ^ (N - m)) from by
          rw [← pow_mul]; congr 1; rw [← pow_succ]; congr 1; omega]
        rw [← hPm, hsign, hPsucc]
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj''
        · exact hprev.2.2 j hj'
        · rw [hj'']
          intro hzero
          have hsig2 : (sigmaExtN (covAcc a c u₀ R P hreg t N)) m
              = (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m := by
            rw [sigmaExtN_apply (N := N) _ m hmN, sigmaExtN_apply (N := N) _ m hmN]
            exact covAcc_prefix (m := m+1) (m' := N) (by omega) ⟨m, hmN⟩ (by simp only; omega)
          have hLfN : Lf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t N)) m
              = Lf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m := by
            apply Lf_congr
            intro i hi
            show sigmaExtN (covAcc a c u₀ R P hreg t N) i
              = sigmaExtN (covAcc a c u₀ R P hreg t (m+1)) i
            rw [sigmaExtN_apply (N := N) _ i (by omega), sigmaExtN_apply (N := N) _ i (by omega)]
            exact covAcc_prefix (m := m+1) (m' := N) (by omega) ⟨i, by omega⟩ (by simp only; omega)
          have hXk : ∀ k ≤ m, Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t N)) k
              = Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) k := by
            intro k hk
            apply Xf_congr
            intro i hi
            show sigmaExtN (covAcc a c u₀ R P hreg t N) i
              = sigmaExtN (covAcc a c u₀ R P hreg t (m+1)) i
            rw [sigmaExtN_apply (N := N) _ i (by omega), sigmaExtN_apply (N := N) _ i (by omega)]
            exact covAcc_prefix (m := m+1) (m' := N) (by omega) ⟨i, by omega⟩ (by simp only; omega)
          have hGm1 : Good a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t N)) (m+1) := by
            intro k hk
            rw [show (fun w => rhoPrimeSq a
                  (Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t N)) k w))
                = (fun w => rhoPrimeSq a
                  (Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) k w)) from by
              funext w; rw [hXk k (by omega)]]
            exact hgood k hk
          have hexN := stepOut_exists_of_good
            (XProps_of_good hR hc _ m (Good.mono hGm1 (by omega : m ≤ m+1)))
            (hGm1 m (by omega : m < m+1))
          have hanN : AnalyticOnNhd ℂ
              (fun w => Lf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t N)) m w
                - sgn ((sigmaExtN (covAcc a c u₀ R P hreg t N)) m))
              (ball 0 (rawRho a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t N)) m) \ {0}) := by
            rw [Lf_eq hexN, rawRho_eq hexN]
            exact fun w hw => (hexN.choose.hlam_an w hw).sub analyticAt_const
          have heqN := eqOn_zero_of_eventually_zero
            (rawRho_pos hR hc (by omega : m < N) hGm1) hanN hzero
          have hwltN := tmem_rawRho hR hc htρ ⟨m, hmN⟩ hGm1
          have hwmemN : t ^ (2 ^ (N - 1 - m))
              ∈ ball 0 (rawRho a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t N)) m) \ {0} := by
            refine ⟨?_, ?_⟩
            · rw [Metric.mem_ball, dist_zero_right]
              simpa only [Fin.val_mk] using hwltN
            · simp only [Set.mem_singleton_iff]; exact pow_ne_zero _ ht0
          have hwN := heqN _ hwmemN
          have hLfEq : Lf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m
              (t ^ (2 ^ (N - 1 - m)))
              = sgn ((sigmaExtN (covAcc a c u₀ R P hreg t (m+1))) m) := by
            rw [hLfN, hsig2] at hwN
            exact sub_eq_zero.mp hwN
          have hlam1 : lam = 1 := by
            rw [← hsign, hLfEq, sgn_mul_sgn]
          have hprime : (1 : ℂ) ^ 2 = rhoPrimeSq a (P (Fin.succ ⟨N - m - 1, by omega⟩)) := by
            rw [one_pow, ← hlam2, hlam1]
            ring
          have hzero2 : rhoSq a (P ⟨N - m - 1, by omega⟩) = 0 := by
            rw [← hPcast, hlamP, hlam1, rhoSq_paramΛ (lam := 1) one_ne_zero hprime]
            ring
          refine (hreg ⟨N - m - 1, by omega⟩).2.1 ?_
          rw [hPcast]
          exact hzero2
  -- conclusion
  refine ⟨covAcc a c u₀ R P hreg t N, ⟨(key N le_rfl).1, fun m hm => (key N le_rfl).2.2 m hm⟩, ?_⟩
  · intro j
    have hj : N - (N - (j:ℕ)) = (j:ℕ) := by omega
    have hidx : (⟨N - (N - (j:ℕ)), by omega⟩ : Fin (N+1)) = j := by
      ext; simp only [Fin.val_mk, hj]
    have hprev := (key (N - (j:ℕ)) (Nat.sub_le N _)).2.1
    rw [hidx] at hprev
    have hXfeq : Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t (N - (j:ℕ)))) (N - (j:ℕ))
        = Xf a c u₀ R (sigmaExtN (covAcc a c u₀ R P hreg t N)) (N - (j:ℕ)) := by
      apply Xf_congr
      intro i hi
      show sigmaExtN (covAcc a c u₀ R P hreg t (N - (j:ℕ))) i
        = sigmaExtN (covAcc a c u₀ R P hreg t N) i
      rw [sigmaExtN_apply (N := N) _ i (by omega), sigmaExtN_apply (N := N) _ i (by omega)]
      exact (covAcc_prefix (m := N - (j:ℕ)) (m' := N) (Nat.sub_le N _) ⟨i, by omega⟩ (by simp only; omega)).symm
    rw [hprev, hXfeq, hj]
    simp only [branchPt]

end

end Work.EQ
