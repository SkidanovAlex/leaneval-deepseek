import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.bp_aux
import Submission.Work.EQ.chart_uniform_tails

/-! # Auxiliary lemmas for `genuine_puncture_degenerate`

Small self-contained pieces used by `Submission.Work.EQ.genuine_puncture_degenerate`:

* `gpd_meromorphic_bdd_analytic`: a meromorphic function bounded near the centre extends
  analytically to the centre (Riemann's removable singularity, in the `MeromorphicAt` language);
* the algebra of `paramΛ` (the backward partner of `Q` parametrised by a square root of
  `rhoPrimeSq a Q`): it is `invBranch` at the principal root, the two roots give distinct partners,
  and it recovers an `invBranch`;
* `exists_analytic_sqrt_ball`, `exists_sqrt_bsq_subO1`: analytic square roots of nonvanishing
  analytic functions, in the vector-valued setting needed for `x ↦ bsq (subO1 a x)` on `ℂ × ℂ`;
* `gpd_eventually_zero_of_punctured`: an analytic function vanishing on a punctured disc around
  the centre vanishes on a neighbourhood;
* `gpd_v0_ne_zero`: the `ψ₂`-limit of a punctured chart is nonzero;
* `gpd_sheet_analytic`: the analytic sheet of the middle of an unramified chart.
-/

namespace Work.EQ

open Filter _root_.Topology

noncomputable section

/-! ## Riemann's removable singularity in the `MeromorphicAt` language -/

/-- A meromorphic function bounded near the centre extends analytically to the centre. -/
theorem gpd_meromorphic_bdd_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {M : ℝ}
    (hf : MeromorphicAt f (0 : ℂ))
    (hM : ∀ᶠ ζ in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, ‖f ζ‖ ≤ M) :
    ∃ F : ℂ → E, AnalyticAt ℂ F 0 ∧
      Filter.EventuallyEq (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) f F := by
  by_contra hcon
  push_neg at hcon
  have hneg : meromorphicOrderAt f 0 < 0 := by
    by_contra h
    push_neg at h
    obtain ⟨g, hg1, hg2⟩ := (MeromorphicAt.meromorphicOrderAt_nonneg_iff hf).mp h
    exact hcon g hg1 hg2
  have hcob : Tendsto f (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (Bornology.cobounded E) :=
    (tendsto_cobounded_iff_meromorphicOrderAt_neg hf).mpr hneg
  have h1 : Tendsto (fun ζ => ‖f ζ‖) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) atTop :=
    (tendsto_norm_atTop_iff_cobounded).mpr hcob
  haveI : NeBot (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) := inferInstance
  have h2 : ∀ᶠ ζ in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, False := by
    filter_upwards [h1.eventually (eventually_gt_atTop M), hM] with ζ h3 h4
    exact absurd h4 (not_le.mpr h3)
  exact (h2.exists).elim (fun x hx => hx)

/-- An analytic function vanishing on the punctured disc `u₀ + κ·(punctured ball of radius ρ)`
vanishes on a neighbourhood of `u₀`. -/
lemma gpd_eventually_zero_of_punctured {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {u₀ κ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hκ : κ ≠ 0)
    (hfan : AnalyticAt ℂ f u₀)
    (hz : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < ρ → f (u₀ + κ * ζ) = 0) :
    ∀ᶠ w in 𝓝 u₀, f w = 0 := by
  have hV : Metric.ball u₀ (‖κ‖ * ρ) \ {u₀} ∈ 𝓝[≠] u₀ :=
    Filter.inter_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds u₀ (by positivity)))
      self_mem_nhdsWithin
  have hzero : ∀ w ∈ Metric.ball u₀ (‖κ‖ * ρ) \ {u₀}, f w = 0 := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hwd : ‖w - u₀‖ < ‖κ‖ * ρ := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hw1
    set ζ : ℂ := (w - u₀) / κ with hζ
    have hwns : w - u₀ ≠ 0 := by
      intro h
      exact hw2 (by rw [Set.mem_singleton_iff]; exact sub_eq_zero.mp h)
    have hζne : ζ ≠ 0 := by
      rw [hζ]
      exact div_ne_zero hwns hκ
    have hζnorm : ‖ζ‖ < ρ := by
      rw [hζ, norm_div, div_lt_iff₀ (norm_pos_iff.mpr hκ), mul_comm]
      exact hwd
    have hwκ : u₀ + κ * ζ = w := by
      rw [hζ]; field_simp; ring
    rw [← hwκ]
    exact hz ζ (norm_pos_iff.mpr hζne) hζnorm
  rcases hfan.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact h
  · exfalso
    haveI : NeBot (nhdsWithin u₀ {u₀}ᶜ) := inferInstance
    have hmem : (Metric.ball u₀ (‖κ‖ * ρ) \ {u₀}) ∩ {w | f w ≠ 0} ∈ 𝓝[≠] u₀ :=
      Filter.inter_mem hV h
    obtain ⟨w, hw1, hw2⟩ := Filter.nonempty_of_mem hmem
    exact hw2 (hzero w hw1)

/-! ## The algebra of `paramΛ` -/

lemma sqhalf (w : ℂ) : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
  have h : (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ := by norm_num
  rw [h]
  exact Complex.cpow_nat_inv_pow w (by norm_num)

/-- `paramΛ` at the principal square root of `rhoPrimeSq a Q` is the principal backward branch. -/
lemma paramΛ_sqrt_eq_true (a : ℝ) (Q : ℂ × ℂ) (hQ : rhoPrimeSq a Q ≠ 0) :
    paramΛ a Q ((rhoPrimeSq a Q) ^ (1 / 2 : ℂ)) = invBranch a true Q := by
  obtain ⟨Q1, Q2⟩ := Q
  simp only [paramΛ, invBranch, rhoPrimeSq, Prod.fst, Prod.snd, ite_true]
  set D : ℂ := ((Q1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q2 ^ 2) ^ (1 / 2 : ℂ) with hD
  have hDne : D ≠ 0 := by
    intro h
    refine hQ ?_
    have h' : ((Q1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q2 ^ 2) = 0 := by
      rw [← sqhalf ((Q1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q2 ^ 2), ← hD, h]; ring
    simpa only [rhoPrimeSq, Prod.fst, Prod.snd] using h'
  ext <;> field_simp <;> ring

/-- `paramΛ` at the other square root of `rhoPrimeSq a Q` is the other backward branch. -/
lemma paramΛ_sqrt_eq_false (a : ℝ) (Q : ℂ × ℂ) (hQ : rhoPrimeSq a Q ≠ 0) :
    paramΛ a Q (-((rhoPrimeSq a Q) ^ (1 / 2 : ℂ))) = invBranch a false Q := by
  obtain ⟨Q1, Q2⟩ := Q
  simp only [paramΛ, invBranch, rhoPrimeSq, Prod.fst, Prod.snd]
  set D : ℂ := ((Q1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q2 ^ 2) ^ (1 / 2 : ℂ) with hD
  have hDne : D ≠ 0 := by
    intro h
    refine hQ ?_
    have h' : ((Q1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q2 ^ 2) = 0 := by
      rw [← sqhalf ((Q1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q2 ^ 2), ← hD, h]; ring
    simpa only [rhoPrimeSq, Prod.fst, Prod.snd] using h'
  ext <;> simp only [ite_eq_iff] <;> norm_num <;> field_simp <;> ring

/-- The backward partner attached to any square root `S` of `rhoPrimeSq a Q` is an `invBranch`
of `Q`. -/
lemma paramΛ_mem_invBranch {a : ℝ} {Q : ℂ × ℂ} {S : ℂ} (hS : S ^ 2 = rhoPrimeSq a Q)
    (hQ : rhoPrimeSq a Q ≠ 0) :
    paramΛ a Q S = invBranch a true Q ∨ paramΛ a Q S = invBranch a false Q := by
  rcases (sq_eq_sq_iff_eq_or_eq_neg (a := S) (b := (rhoPrimeSq a Q) ^ (1 / 2 : ℂ))).mp
    (by rw [hS, sqhalf]) with h | h
  · exact Or.inl (by rw [h, paramΛ_sqrt_eq_true a Q hQ])
  · exact Or.inr (by rw [h, paramΛ_sqrt_eq_false a Q hQ])

/-- The backward partner attached to `-S` is also an `invBranch`. -/
lemma paramΛ_neg_mem_invBranch {a : ℝ} {Q : ℂ × ℂ} {S : ℂ} (hS : S ^ 2 = rhoPrimeSq a Q)
    (hQ : rhoPrimeSq a Q ≠ 0) :
    paramΛ a Q (-S) = invBranch a true Q ∨ paramΛ a Q (-S) = invBranch a false Q :=
  paramΛ_mem_invBranch (a := a) (Q := Q) (S := -S) (by rw [neg_pow, hS]; ring) hQ

/-- The two backward partners attached to the roots `±S` of `rhoPrimeSq a Q` are distinct. -/
lemma paramΛ_ne_neg {a : ℝ} {Q : ℂ × ℂ} {S : ℂ} (hS : S ^ 2 = rhoPrimeSq a Q)
    (hQ : rhoPrimeSq a Q ≠ 0) : paramΛ a Q S ≠ paramΛ a Q (-S) := by
  have hbsq : bsq (subO1 a Q) ≠ 0 := by simpa only [rhoPrimeSq, subO1, bsq] using hQ
  intro hc
  rcases (sq_eq_sq_iff_eq_or_eq_neg (a := S) (b := (rhoPrimeSq a Q) ^ (1 / 2 : ℂ))).mp
    (by rw [hS, sqhalf]) with h | h
  · rw [h] at hc
    rw [paramΛ_sqrt_eq_true a Q hQ, paramΛ_sqrt_eq_false a Q hQ] at hc
    exact invBranch_true_ne_false hbsq hc
  · rw [h, neg_neg] at hc
    rw [paramΛ_sqrt_eq_false a Q hQ, paramΛ_sqrt_eq_true a Q hQ] at hc
    exact invBranch_true_ne_false hbsq hc.symm

/-! ## Analytic square roots, vector valued -/

/-- A nonvanishing analytic function on a ball of a complex normed space has an analytic square
root on a (smaller) ball.  This is `Work.EQ.exists_analytic_sqrt` with the scalar variable
replaced by a vector variable. -/
lemma exists_analytic_sqrt_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : E → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 ρ)) (hg0 : g 0 ≠ 0) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∃ h : E → ℂ, AnalyticOnNhd ℂ h (Metric.ball 0 ρ') ∧
      ∀ z ∈ Metric.ball 0 ρ', h z ^ 2 = g z := by
  set u : E → ℂ := fun z => g z / g 0 with hu
  have hu0 : u 0 = 1 := by simp [hu, hg0]
  have huan : AnalyticOnNhd ℂ u (Metric.ball 0 ρ) := fun z hz => (hg z hz).div analyticAt_const hg0
  have hcont : ContinuousAt u 0 := (huan 0 (by simpa using hρ)).continuousAt
  have hmem : {z : E | u z ∈ Complex.slitPlane} ∈ 𝓝 (0 : E) := by
    have h1 : u 0 ∈ Complex.slitPlane := by rw [hu0]; exact Complex.one_mem_slitPlane
    exact hcont.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds h1)
  rw [Metric.mem_nhds_iff] at hmem
  obtain ⟨ρ₁, hρ₁0, hρ₁⟩ := hmem
  refine ⟨min ρ₁ ρ, lt_min hρ₁0 hρ, min_le_right _ _, ?_⟩
  refine ⟨fun z => Complex.sqrt (g 0) * Complex.sqrt (u z), ?_, ?_⟩
  · have hball : Metric.ball (0 : E) (min ρ₁ ρ) ⊆ {z | u z ∈ Complex.slitPlane} := fun z hz =>
      hρ₁ (by rw [Metric.mem_ball] at hz ⊢; exact lt_of_lt_of_le hz (min_le_left _ _))
    have hmono : Metric.ball (0 : E) (min ρ₁ ρ) ⊆ Metric.ball (0 : E) ρ := by
      intro y hy; rw [Metric.mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy (min_le_right _ _)
    have hsqrt : AnalyticOnNhd ℂ Complex.sqrt Complex.slitPlane :=
      Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane
    have hcomp : AnalyticOnNhd ℂ (fun z : E => Complex.sqrt (u z)) (Metric.ball 0 (min ρ₁ ρ)) :=
      hsqrt.comp (huan.mono hmono) (fun y hy => hball hy)
    intro z hz
    exact analyticAt_const.mul (hcomp z hz)
  · intro z hz
    rw [mul_pow, sq_sqrt, sq_sqrt]
    simp only [hu]
    rw [mul_div_cancel₀ _ hg0]

/-- The `O₁`-radicand `x ↦ bsq (subO1 a x)` has an analytic square root near any point where it
does not vanish. -/
lemma exists_sqrt_bsq_subO1 {a : ℝ} {Q : ℂ × ℂ} (hQ : bsq (subO1 a Q) ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ S : ℂ × ℂ → ℂ, AnalyticOnNhd ℂ S (Metric.ball Q ρ) ∧
      S Q ^ 2 = bsq (subO1 a Q) ∧ ∀ x ∈ Metric.ball Q ρ, S x ^ 2 = bsq (subO1 a x) := by
  have hgan : AnalyticOnNhd ℂ (fun z : ℂ × ℂ => bsq (subO1 a (Q + z))) (Metric.ball 0 1) := by
    intro z _
    have h1 : AnalyticAt ℂ (fun z : ℂ × ℂ => Q.1 + z.1) z :=
      analyticAt_const.add analyticAt_fst
    have h2 : AnalyticAt ℂ (fun z : ℂ × ℂ => Q.2 + z.2) z :=
      analyticAt_const.add analyticAt_snd
    have h3 : AnalyticAt ℂ
        (fun z : ℂ × ℂ => (Q.1 + z.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + (Q.2 + z.2) ^ 2) z :=
      ((h1.add analyticAt_const).pow 2).add (h2.pow 2)
    simpa only [bsq, subO1, Prod.fst_add, Prod.snd_add] using h3
  have hg0 : (fun z : ℂ × ℂ => bsq (subO1 a (Q + z))) 0 ≠ 0 := by
    simpa only [add_zero] using hQ
  obtain ⟨ρ', hρ'0, -, h, hhan, hh⟩ := exists_analytic_sqrt_ball (ρ := 1) one_pos hgan hg0
  refine ⟨ρ', hρ'0, fun x => h (x - Q), ?_, ?_, ?_⟩
  · have h1 : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => x - Q) (Metric.ball Q ρ') :=
      fun y _ => analyticAt_id.sub analyticAt_const
    have h2 : Set.MapsTo (fun x : ℂ × ℂ => x - Q) (Metric.ball Q ρ') (Metric.ball 0 ρ') := by
      intro y hy
      simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hy
    exact hhan.comp h1 h2
  · have h1 : (fun x : ℂ × ℂ => h (x - Q)) Q = h 0 := by simp
    rw [h1]
    have h2 := hh 0 (by simpa using hρ'0)
    rw [h2]
    simp only [subO1, bsq, Prod.fst, Prod.snd, add_zero]
  · intro x hx
    have h1 : x - Q ∈ Metric.ball (0 : ℂ × ℂ) ρ' := by
      simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hx
    have h2 := hh (x - Q) h1
    have h3 : Q + (x - Q) = x := by abel
    rw [h3] at h2
    exact h2

/-! ## Analyticity of `germC` on a ball, for `ψ₁`-limits -/

/-- `ugermC` of a small parameter is the mirror of `germC`. -/
lemma ugermC_eq (a : ℝ) (h : ℂ → ℂ) (v : ℂ) : ugermC a h v = eqMirror (germC a h v) := rfl

/-- The `O₁`-radicand of an `ugermC` value is the `O₂`-radicand of the corresponding `germC`
value. -/
lemma bsq_subO1_ugermC (a : ℝ) (h : ℂ → ℂ) (v : ℂ) :
    bsq (subO1 a (ugermC a h v)) = bsq (subO2 a (germC a h v)) := by
  simp only [ugermC, eqMirror, subO1, subO2, bsq]
  ring

/-! ## The `ψ₂`-limit of a punctured chart is nonzero -/

/-- **The `ψ₂`-limit of a punctured chart is nonzero.** -/
theorem gpd_v0_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {e : ℂ → ChainData} {u₀ : ℂ} {k : ℕ}
    (he : IsPuncturedChart a h e u₀ k) {v₀ : ℂ}
    (hv : Tendsto (fun ζ => (e ζ).2.2) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds v₀)) :
    v₀ ≠ 0 := by
  obtain ⟨hk, hu₀, κ, hκ, hchart, hInj, hcont, hMer, hMern⟩ := he
  obtain ⟨ρ, hρ, hb⟩ := H0_invParam_ge ha0 ha1 hh
  have hball : Metric.ball (0 : ℂ) 1 \ {0} ∈ nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ :=
    Filter.inter_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 one_pos)) self_mem_nhdsWithin
  have hψ1 : Tendsto (fun ζ => (e ζ).2.1) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds u₀) := by
    have h3 : Tendsto (fun ζ : ℂ => u₀ + κ * ζ ^ k) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ)
        (nhds (u₀ + κ * (0 : ℂ) ^ k)) :=
      ((continuousAt_const.add (continuousAt_const.mul (continuousAt_id.pow k))).tendsto).mono_left
        nhdsWithin_le_nhds
    have h0 : u₀ + κ * (0 : ℂ) ^ k = u₀ := by
      rw [zero_pow (by omega : k ≠ 0), mul_zero, add_zero]
    rw [h0] at h3
    have hev : (fun ζ : ℂ => u₀ + κ * ζ ^ k) =ᶠ[nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ]
        (fun ζ => (e ζ).2.1) :=
      Filter.eventually_iff.mpr (Filter.mem_of_superset hball (fun ζ hζ => ((hchart ζ hζ).2).symm))
    exact h3.congr' hev
  have hprod : Tendsto (fun ζ => (e ζ).2.1 * (e ζ).2.2) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ)
      (nhds (u₀ * v₀)) := hψ1.mul hv
  have hle : ρ ≤ ‖u₀ * v₀‖ := by
    refine ge_of_tendsto hprod.norm ?_
    filter_upwards [hball] with ζ hζ
    exact hb (e ζ) (hchart ζ hζ).1
  have hne : u₀ * v₀ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hle
    linarith
  exact fun hv0 => hne (by rw [hv0, mul_zero])

/-! ## The analytic sheet of the middle of an unramified chart -/

/-- **The analytic sheet of the middle of an unramified chart.** -/
theorem gpd_sheet_analytic {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {u₀ κ : ℂ} {N : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (hκ : κ ≠ 0)
    (hgermAn : AnalyticAt ℂ (fun w : ℂ => germC a h
      (((eqLam a : ℝ) : ℂ) ^ N * w)) u₀)
    {F : ℕ → ℂ → ℂ × ℂ}
    (hFan : ∀ i ≤ 2 * N, AnalyticAt ℂ (F i) 0)
    (hF0 : F 0 0 = germC a h (((eqLam a : ℝ) : ℂ) ^ N * u₀) ∧
      ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < ρ →
        F 0 ζ = germC a h (((eqLam a : ℝ) : ℂ) ^ N * (u₀ + κ * ζ)))
    (hchain : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < ρ → ∀ i < 2 * N,
      EqRelC a (F (i + 1) ζ) (F i ζ))
    (hreg : ∀ i < 2 * N, bsq (subO1 a (F i 0)) ≠ 0) :
    ∃ g : ℂ → ℕ → ℂ × ℂ,
      (∀ i ≤ 2 * N, AnalyticAt ℂ (fun w => g w i) u₀) ∧
      (∀ i ≤ 2 * N, g u₀ i = F i 0) ∧
      (∀ᶠ w in nhds u₀, g w 0 = germC a h (((eqLam a : ℝ) : ℂ) ^ N * w) ∧
        ∀ i < 2 * N, EqRelC a (g w (i + 1)) (g w i) ∧
          bsq (subO1 a (g w i)) ≠ 0) ∧
      (∀ i ≤ 2 * N, ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < ρ → g (u₀ + κ * ζ) i = F i ζ) := by
  set φ : ℂ → ℂ := fun w => (w - u₀) / κ with hφ
  have hφan : AnalyticAt ℂ φ u₀ := (analyticAt_id.sub analyticAt_const).div analyticAt_const hκ
  have hφ0 : φ u₀ = 0 := by rw [hφ]; simp
  have hζφ : ∀ ζ : ℂ, φ (u₀ + κ * ζ) = ζ := by
    intro ζ
    rw [hφ]
    simp only
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hκ]
  have hanF : ∀ i ≤ 2 * N, AnalyticAt ℂ (fun w => F i (φ w)) u₀ := by
    intro i hi
    have h1 := hFan i hi
    rw [show (0 : ℂ) = φ u₀ from hφ0.symm] at h1
    exact h1.comp hφan
  set G : ℂ → ℕ → ℂ × ℂ := fun w i => F i (φ w) with hG
  have hGu : ∀ i, G u₀ i = F i 0 := by
    intro i; rw [hG]; simp [hφ0]
  refine ⟨G, fun i hi => hanF i hi, fun i hi => hGu i, ?_, ?_⟩
  · have hmain : ∀ᶠ w in nhds u₀,
        G w 0 = germC a h (((eqLam a : ℝ) : ℂ) ^ N * w) := by
      have hmain0 : ∀ᶠ w in nhds u₀,
          (fun w : ℂ => G w 0 - germC a h (((eqLam a : ℝ) : ℂ) ^ N * w)) w = 0 := by
        refine gpd_eventually_zero_of_punctured (f := fun w : ℂ =>
          G w 0 - germC a h (((eqLam a : ℝ) : ℂ) ^ N * w)) hρ hκ ?_ ?_
        · exact (hanF 0 (by omega)).sub hgermAn
        · intro ζ h1 h2
          rw [hG]
          simp only
          rw [hζφ ζ, hF0.2 ζ h1 h2, sub_self]
      filter_upwards [hmain0] with w hw
      exact sub_eq_zero.mp hw
    have hEq : ∀ i < 2 * N, ∀ᶠ w in nhds u₀, EqRelC a (G w (i + 1)) (G w i) := by
      intro i hi
      have han1 : AnalyticAt ℂ (fun w : ℂ =>
          ((G w i).1 + (G w (i + 1)).1) ^ 2 + ((G w i).2 + (G w (i + 1)).2) ^ 2 - 1) u₀ := by
        have h1 : AnalyticAt ℂ (fun w : ℂ => (G w i).1) u₀ :=
          analyticAt_fst.comp (hanF i (by omega))
        have h2 : AnalyticAt ℂ (fun w : ℂ => (G w (i+1)).1) u₀ :=
          analyticAt_fst.comp (hanF (i+1) (by omega))
        have h3 : AnalyticAt ℂ (fun w : ℂ => (G w i).2) u₀ :=
          analyticAt_snd.comp (hanF i (by omega))
        have h4 : AnalyticAt ℂ (fun w : ℂ => (G w (i+1)).2) u₀ :=
          analyticAt_snd.comp (hanF (i+1) (by omega))
        exact (((h1.add h2).pow 2).add ((h3.add h4).pow 2)).sub analyticAt_const
      have han2 : AnalyticAt ℂ (fun w : ℂ =>
          ((G w i).1 + (G w (i + 1)).1) * (G w (i + 1)).2 -
            ((G w i).2 + (G w (i + 1)).2) * ((G w (i + 1)).1 - ((a / 2 : ℝ) : ℂ))) u₀ := by
        have h1 : AnalyticAt ℂ (fun w : ℂ => (G w i).1) u₀ :=
          analyticAt_fst.comp (hanF i (by omega))
        have h2 : AnalyticAt ℂ (fun w : ℂ => (G w (i+1)).1) u₀ :=
          analyticAt_fst.comp (hanF (i+1) (by omega))
        have h3 : AnalyticAt ℂ (fun w : ℂ => (G w i).2) u₀ :=
          analyticAt_snd.comp (hanF i (by omega))
        have h4 : AnalyticAt ℂ (fun w : ℂ => (G w (i+1)).2) u₀ :=
          analyticAt_snd.comp (hanF (i+1) (by omega))
        exact ((h1.add h2).mul h4).sub ((h3.add h4).mul (h2.sub analyticAt_const))
      have hz1 : ∀ᶠ w in nhds u₀,
          ((G w i).1 + (G w (i + 1)).1) ^ 2 + ((G w i).2 + (G w (i + 1)).2) ^ 2 - 1 = 0 := by
        refine gpd_eventually_zero_of_punctured (f := fun w : ℂ =>
          ((G w i).1 + (G w (i + 1)).1) ^ 2 + ((G w i).2 + (G w (i + 1)).2) ^ 2 - 1) hρ hκ
            han1 ?_
        intro ζ h1 h2
        rw [hG]
        simp only
        rw [hζφ ζ]
        exact sub_eq_zero.mpr (hchain ζ h1 h2 i hi).1
      have hz2 : ∀ᶠ w in nhds u₀,
          ((G w i).1 + (G w (i + 1)).1) * (G w (i + 1)).2 -
            ((G w i).2 + (G w (i + 1)).2) * ((G w (i + 1)).1 - ((a / 2 : ℝ) : ℂ)) = 0 := by
        refine gpd_eventually_zero_of_punctured (f := fun w : ℂ =>
          ((G w i).1 + (G w (i + 1)).1) * (G w (i + 1)).2 -
            ((G w i).2 + (G w (i + 1)).2) * ((G w (i + 1)).1 - ((a / 2 : ℝ) : ℂ))) hρ hκ
            han2 ?_
        intro ζ h1 h2
        rw [hG]
        simp only
        rw [hζφ ζ]
        exact sub_eq_zero.mpr (hchain ζ h1 h2 i hi).2
      filter_upwards [hz1, hz2] with w h1 h2
      exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
    have hrad : ∀ i < 2 * N, ∀ᶠ w in nhds u₀, bsq (subO1 a (G w i)) ≠ 0 := by
      intro i hi
      have hcont : ContinuousAt (fun w : ℂ => bsq (subO1 a (G w i))) u₀ := by
        have hcomp : ContinuousAt (fun w : ℂ => G w i) u₀ := (hanF i (by omega)).continuousAt
        have h2 : ContinuousAt (fun p : ℂ × ℂ => bsq (subO1 a p)) (G u₀ i) := by
          simp only [bsq, subO1]
          fun_prop
        exact ContinuousAt.comp (x := u₀) h2 hcomp
      refine hcont.eventually_ne ?_
      rw [hGu i]
      exact hreg i hi
    have hall : ∀ᶠ w in nhds u₀, ∀ i ∈ Finset.range (2 * N),
        EqRelC a (G w (i + 1)) (G w i) ∧ bsq (subO1 a (G w i)) ≠ 0 :=
      (Filter.eventually_all_finset (Finset.range (2 * N))).mpr (fun i hi =>
        (hEq i (Finset.mem_range.mp hi)).and (hrad i (Finset.mem_range.mp hi)))
    filter_upwards [hmain, hall] with w hw1 hw2
    exact ⟨hw1, fun i hi => hw2 i (Finset.mem_range.mpr hi)⟩
  · intro i hi ζ h1 h2
    rw [hG]
    simp only
    rw [hζφ ζ]

/-- The complex form of the eigenvalue `λ(a)`. -/
noncomputable def eqLamC (a : ℝ) : ℂ := ((eqLam a : ℝ) : ℂ)

@[simp] lemma eqLamC_eq (a : ℝ) : eqLamC a = ((eqLam a : ℝ) : ℂ) := rfl

/-- `λ = (1-a)/(1+a)` is positive for `0 < a < 1`. -/
lemma lam_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < eqLam a := by
  rw [eqLam]; positivity

/-- `λ = (1-a)/(1+a)` is less than `1` for `a > 0`. -/
lemma lam_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a < 1 := by
  rw [eqLam, div_lt_one (by linarith)]; linarith

lemma lamC_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLamC a ≠ 0 := by
  rw [eqLamC_eq]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (lam_pos ha0 ha1))

lemma lamC_norm {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : ‖eqLamC a‖ = eqLam a := by
  rw [eqLamC_eq, Complex.norm_of_nonneg (le_of_lt (lam_pos ha0 ha1))]

/-- `EqRelC` is preserved by the bisector reflection, with the arguments swapped. -/
lemma eqRelC_swap_mirror {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q) :
    EqRelC a (eqMirror Q) (eqMirror P) :=
  H0_invParam_ge_eqRelC_mirror.mpr h

/-- **The germ facts on a ball, in the form used by `gpd_middle_limits`.**  On a ball of radius
`λ·ρ` (where `ρ` is the radius of `germC_facts`), the germ curvature is analytic, the `O₁`- and
`O₂`-radicands do not vanish, and consecutive germ values satisfy `EqRelC`. -/
lemma germC_ball_facts {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ ρg : ℝ, 0 < ρg ∧ AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρg) ∧
      ∀ u ∈ Metric.ball (0 : ℂ) ρg,
        bsq (subO1 a (germC a h u)) ≠ 0 ∧ bsq (subO2 a (germC a h u)) ≠ 0 ∧
          EqRelC a (germC a h u) (germC a h (eqLamC a * u)) := by
  obtain ⟨ρ0, hρ0, hAn, h00, hReg, hInj, hDer⟩ := germC_facts ha0 ha1 hh
  have hlam0 : 0 < eqLam a := lam_pos ha0 ha1
  have hlamlt : eqLam a < 1 := lam_lt_one ha0 ha1
  have hle : eqLam a * ρ0 ≤ ρ0 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_of_lt hlamlt) (le_of_lt hρ0)
  refine ⟨eqLam a * ρ0, mul_pos hlam0 hρ0, hAn.mono (Metric.ball_subset_ball hle), ?_⟩
  intro u hu
  have hu' : ‖u‖ < eqLam a * ρ0 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hu0 : u ∈ Metric.ball (0 : ℂ) ρ0 := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_lt_of_le hu' hle
  have hregU : RegPair a (germC a h u) (germC a h (((eqLam a : ℝ) : ℂ) * u)) :=
    (hReg u hu0).1
  have huDiv : u / (((eqLam a : ℝ) : ℂ)) ∈ Metric.ball (0 : ℂ) ρ0 := by
    rw [Metric.mem_ball, dist_zero_right, norm_div, norm_eqLamC ha0 ha1]
    rw [div_lt_iff₀ hlam0]
    calc ‖u‖ < eqLam a * ρ0 := hu'
      _ = ρ0 * eqLam a := mul_comm _ _
  have hregU' : RegPair a (germC a h (u / (((eqLam a : ℝ) : ℂ))))
      (germC a h (((eqLam a : ℝ) : ℂ) * (u / (((eqLam a : ℝ) : ℂ))))) :=
    (hReg _ huDiv).1
  have hmul : ((eqLam a : ℝ) : ℂ) * (u / (((eqLam a : ℝ) : ℂ))) = u := by
    rw [mul_div_cancel₀ u]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hlam0)
  rw [hmul] at hregU'
  exact ⟨hregU'.2.2, hregU.2.1, hregU.1⟩

end

end Work.EQ
