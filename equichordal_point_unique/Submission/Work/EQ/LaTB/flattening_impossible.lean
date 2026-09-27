import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.la_nnas
import Submission.Work.EQ.FanUniform.fan_uniform_estimates
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.H0_invParam_ge

namespace Work.EQ.LaTB

open Work.EQ Complex Filter _root_.Topology

noncomputable section

/-- A member of `⁰H` is a chain.  (Local copy of `Work.EQ.isChain_of_mem_H0`, whose module
`Submission.Work.EQ.StableTailDefs` is not importable here.) -/
lemma la_isChain_of_mem_H0 {a : ℝ} {h : ℂ → ℂ} {q : ChainData} (hq : q ∈ H0 a h) :
    IsChain a h q := by
  obtain ⟨ε, hε, f, hcont, hf0, hf⟩ := hq
  have hmem : q.2.1 ∈ Metric.ball q.2.1 ε := by
    rw [Metric.mem_ball, dist_self]; exact hε
  rw [← hf0]
  exact (hf q.2.1 hmem).1

/-- `eqMirror` is an involution. -/
@[simp] theorem la_eqMirror_involutive (P : ℂ × ℂ) : eqMirror (eqMirror P) = P := by
  simp [eqMirror]

/-- `‖λ^{l}‖ = λ^{l}` for the real `λ`. -/
theorem la_norm_lamC_zpow {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (l : ℤ) :
    ‖((eqLam a : ℝ) : ℂ) ^ l‖ = (eqLam a) ^ l := by
  rw [norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (eqLam_pos' ha0 ha1)]

/-- **The mirror (unstable) fan reading of a chain.** -/
theorem la_mirror_fan_reading {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {q : ChainData}
    (hq : IsChain a h q) (l : ℤ) :
    ∃ η : List Bool,
      q.1 (-l) = eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ l * q.2.2)) := by
  obtain ⟨η, hη⟩ := chain_eq_fan' ha0 ha1
    (p := shiftZ a l (mirrorChain q))
    (isChain_shiftZ ha0 ha1 (isChain_mirrorChain hq) l)
  refine ⟨η, ?_⟩
  have h2 : (shiftZ a l (mirrorChain q)).1 0 = eqMirror (q.1 (0 - l)) := by
    rw [shiftZ_fst, mirrorChain_fst]
    norm_num
  have h3 : (shiftZ a l (mirrorChain q)).2.1 = ((eqLam a : ℝ) : ℂ) ^ l * q.2.2 := by
    rw [shiftZ_psi1, mirrorChain_psi1]
  rw [h2, h3] at hη
  rw [show (0 : ℤ) - l = -l by ring] at hη
  rw [← hη, la_eqMirror_involutive]

/-- **The stable fan reading of a chain at an arbitrary level.** -/
theorem la_fan_reading {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {q : ChainData}
    (hq : IsChain a h q) (l : ℤ) :
    ∃ ε : List Bool, q.1 l = fan a h ε (((eqLam a : ℝ) : ℂ) ^ l * q.2.1) := by
  obtain ⟨ε, hε⟩ := chain_eq_fan' ha0 ha1 (isChain_shiftZ ha0 ha1 hq l)
  exact ⟨ε, by rw [show q.1 l = (shiftZ a l q).1 0 by simp, hε, shiftZ_psi1]⟩

/-- **The annulus reading level.** -/
theorem la_exists_zpow_mem {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hratio : 1 / eqLam a < r₂ / r₁) {t : ℝ} (ht : 0 < t) :
    ∃ l : ℤ, r₁ ≤ (eqLam a) ^ l * t ∧ (eqLam a) ^ l * t ≤ r₂ := by
  have hl0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hr₂pos : 0 < r₂ := lt_trans hr₁ hr₁₂
  have hprod : r₁ < eqLam a * r₂ := by
    rw [div_lt_div_iff₀ hl0 hr₁] at hratio
    linarith
  have hsmall : ∃ n : ℕ, (eqLam a) ^ n * t ≤ r₂ := by
    have hlim : Tendsto (fun n : ℕ => (eqLam a) ^ n * t) atTop (𝓝 0) :=
      by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hl0.le hl1).mul_const t
    obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds hr₂pos)).exists
    exact ⟨n, le_of_lt hn⟩
  have hlarge : ∃ n : ℕ, r₁ ≤ (eqLam a) ^ (-(n : ℤ)) * t := by
    have hlt1 : 1 < (eqLam a)⁻¹ := by
      rw [one_lt_inv_iff₀]; exact ⟨hl0, hl1⟩
    have hlim : Tendsto (fun n : ℕ => (eqLam a) ^ (-(n : ℤ)) * t) atTop atTop := by
      have h2 : Tendsto (fun n : ℕ => ((eqLam a)⁻¹) ^ n * t) atTop atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt hlt1).atTop_mul_const ht
      refine h2.congr' ?_
      filter_upwards with n
      rw [zpow_neg, zpow_natCast, inv_pow]
    obtain ⟨n, hn⟩ := (hlim.eventually (eventually_ge_atTop r₁)).exists
    exact ⟨n, hn⟩
  rcases lt_trichotomy t r₁ with hlt | heq | hgt
  · -- `t < r₁`
    have hspec : r₁ ≤ (eqLam a) ^ (-((Nat.find hlarge : ℕ) : ℤ)) * t := Nat.find_spec hlarge
    have hmin : ∀ m < Nat.find hlarge,
        ¬ (r₁ ≤ (eqLam a) ^ (-((m : ℕ) : ℤ)) * t) :=
      fun m hm => Nat.find_min hlarge hm
    have hnpos : 0 < Nat.find hlarge := by
      rcases Nat.eq_zero_or_pos (Nat.find hlarge) with h | h
      · rw [h] at hspec
        simp only [Nat.cast_zero, neg_zero, zpow_zero, one_mul] at hspec
        linarith
      · exact h
    have hprev : (eqLam a) ^ (-(((Nat.find hlarge - 1 : ℕ)) : ℤ)) * t < r₁ := by
      have h1 := hmin (Nat.find hlarge - 1) (by omega)
      push Not at h1
      exact h1
    have hcast : -(↑(Nat.find hlarge) : ℤ) = -(((Nat.find hlarge - 1 : ℕ)) : ℤ) + (-1 : ℤ) := by
      omega
    have h3 : (eqLam a) ^ (-(((Nat.find hlarge - 1 : ℕ)) : ℤ) + (-1 : ℤ)) * t
        = (eqLam a)⁻¹ * ((eqLam a) ^ (-(((Nat.find hlarge - 1 : ℕ)) : ℤ)) * t) := by
      rw [zpow_add₀ (ne_of_gt hl0), zpow_neg_one]; ring
    refine ⟨-(↑(Nat.find hlarge) : ℤ), hspec, ?_⟩
    · rw [hcast, h3]
      have h4 : (eqLam a)⁻¹ * ((eqLam a) ^ (-(((Nat.find hlarge - 1 : ℕ)) : ℤ)) * t)
          < (eqLam a)⁻¹ * r₁ := mul_lt_mul_of_pos_left hprev (inv_pos.mpr hl0)
      have h5 : (eqLam a)⁻¹ * r₁ ≤ r₂ := by
        rw [inv_mul_le_iff₀ hl0]; linarith [hprod]
      linarith
  · exact ⟨0, by simpa [heq] using hr₁.le, by simpa [heq] using hr₁₂.le⟩
  · -- `r₁ < t`
    rcases lt_trichotomy t r₂ with hlt2 | heq2 | hgt2
    · exact ⟨0, by simpa using hgt.le, by simpa using hlt2.le⟩
    · exact ⟨0, by simpa using hgt.le, by simpa [heq2] using le_refl (r₂)⟩
    · have hspec : (eqLam a) ^ (Nat.find hsmall) * t ≤ r₂ := Nat.find_spec hsmall
      have hmin : ∀ m < Nat.find hsmall, ¬ ((eqLam a) ^ m * t ≤ r₂) :=
        fun m hm => Nat.find_min hsmall hm
      have hnpos : 0 < Nat.find hsmall := by
        rcases Nat.eq_zero_or_pos (Nat.find hsmall) with h | h
        · rw [h] at hspec; simp only [pow_zero, one_mul] at hspec; linarith
        · exact h
      have hprev : r₂ < (eqLam a) ^ (Nat.find hsmall - 1) * t := by
        have h1 := hmin (Nat.find hsmall - 1) (by omega)
        push Not at h1
        exact h1
      refine ⟨(Nat.find hsmall : ℤ), ?_, ?_⟩
      · rw [zpow_natCast]
        have hpow : (eqLam a) ^ (Nat.find hsmall - 1) * eqLam a
            = (eqLam a) ^ Nat.find hsmall := by
          rw [← pow_succ, Nat.sub_add_cancel hnpos]
        have hstep : (eqLam a) ^ Nat.find hsmall * t
            = eqLam a * ((eqLam a) ^ (Nat.find hsmall - 1) * t) := by
          rw [← hpow]; ring
        rw [hstep]
        nlinarith [hprod, hl0, hprev]
      · rw [zpow_natCast]; exact hspec


/-- Helper: the norm of a real zpow. -/
private lemma la_norm_lamC_zpow' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (l : ℤ) :
    ‖(((eqLam a) ^ l : ℝ) : ℂ)‖ = (eqLam a) ^ l := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zpow_pos (eqLam_pos' ha0 ha1) l)]

/-- **A mirrored fan value at a small parameter is unstable-near its centre.** -/
private theorem la_mirror_fan_UnNear {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {η : List Bool} {w : ℂ} {δE Ke Lam : ℝ}
    (hest : ∀ (ε : List Bool) (u : ℂ), u ∈ Metric.ball (0 : ℂ) δE →
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ Ke * ‖u‖ ∧
      ‖(fan a h ε u).2‖ ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖)
    (hctr : ∀ ε : List Bool, ∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k)
    (hw : ‖w‖ < δE) :
    Work.EQ.LaNnas.UnNear a (eqMirror (fan a h η w)) (max Ke Lam * ‖w‖) := by
  obtain ⟨h1, h2⟩ := hest η w (by simpa [Metric.mem_ball, dist_eq_norm] using hw)
  obtain ⟨k, hk⟩ := hctr η
  refine ⟨-k, ?_, ?_⟩
  · have hc : (1 / 2 + 2 * (((-k : ℤ)) : ℂ)) = -((fan a h η 0).1) := by
      rw [hk]; push_cast; ring
    simp only [eqMirror]
    rw [hc]
    rw [show (-(fan a h η w).1 - -(fan a h η 0).1)
        = -((fan a h η w).1 - (fan a h η 0).1) by ring, norm_neg]
    exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg w))
  · simp only [eqMirror]
    rw [show (-(fan a h η w).1 + ((a / 2 : ℝ) : ℂ))
        = -((fan a h η w).1 - ((a / 2 : ℝ) : ℂ)) by ring, norm_neg]
    calc ‖(fan a h η w).2‖
        ≤ Lam * ‖w‖ * ‖(fan a h η w).1 - ((a / 2 : ℝ) : ℂ)‖ := h2
      _ ≤ max Ke Lam * ‖w‖ * ‖(fan a h η w).1 - ((a / 2 : ℝ) : ℂ)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg w)

/-- **A fan value at a small parameter is stable-near its centre.** -/
private theorem la_fan_SnNear {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {η : List Bool} {w : ℂ} {δE Ke Lam : ℝ}
    (hest : ∀ (ε : List Bool) (u : ℂ), u ∈ Metric.ball (0 : ℂ) δE →
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ Ke * ‖u‖ ∧
      ‖(fan a h ε u).2‖ ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖)
    (hctr : ∀ ε : List Bool, ∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k)
    (hw : ‖w‖ < δE) :
    Work.EQ.LaNnas.SnNear a (fan a h η w) (max Ke Lam * ‖w‖) := by
  obtain ⟨h1, h2⟩ := hest η w (by simpa [Metric.mem_ball, dist_eq_norm] using hw)
  obtain ⟨k, hk⟩ := hctr η
  refine ⟨k, ?_, ?_⟩
  · rw [hk] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg w))
  · calc ‖(fan a h η w).2‖
        ≤ Lam * ‖w‖ * ‖(fan a h η w).1 - ((a / 2 : ℝ) : ℂ)‖ := h2
      _ ≤ max Ke Lam * ‖w‖ * ‖(fan a h η w).1 - ((a / 2 : ℝ) : ℂ)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg w)

/-- **The shrinking-fan case (iii) of the trichotomy is impossible** (Rychlik's omitted case).

A copy, in a fresh namespace and proved with the `Work.EQ.LaNnas.*` near-axis vocabulary, of
`Work.EQ.tb_flattening_impossible` from `Submission/Work/EQ/tail_bound_of_words.lean`.  The
reason for the copy is only importability: `tail_bound_of_words` imports
`Submission.Work.EQ.no_near_axis_segment`, which declares `Work.EQ.norm_sub_le_add`, colliding
with the declaration of the same name in `Submission.Work.EQ.H0_section_local`; a file that must
import the latter (for Rychlik's regularity/section machinery) therefore cannot import the
former, but can import this copy (`Submission.Work.EQ.la_nnas` carries the collision-free
`Work.EQ.LaNnas.*` copy of the whole near-axis file).

Proof: copy `tb_flattening_impossible` (and every helper it uses that cannot be imported:
`tb_norm_lamC_zpow'`, `tb_mirror_fan_UnNear`, `tb_fan_SnNear` are private, and
`tb_norm_lamC_zpow`, `tb_eqMirror_involutive`, `tb_exists_zpow_mem`, `tb_fan_reading`,
`tb_mirror_fan_reading` are public but live only in the unimportable file; copy all of them as
`la_*`) verbatim, replacing every reference to `SnNear`, `UnNear`, `SnNear.mono`, `UnNear.mono`,
`not_un_and_sn`, `propagate_fwd`, `propagate_bwd`, `nnK`, `nnC`, `nnD`, `nnK_pos`,
`nnD_pos`, `nnD_le_quarter`, `nnC_pos`, `nnC_ge_one`, `nnK_ge_one`, `nnK_mul_nnD_le`,
`nnK_le_nnC`, `norm_sub_le_add`, `abs_neg_half_add_two_mul`, `axis_bounds` by
`Work.EQ.LaNnas.<same name>`.  It is recommended to put `la_exists_zpow_mem`, `la_fan_reading`,
`la_mirror_fan_reading` in this same file (the companion
`EQ/LaTB/flattening_impossible_bwd` will import it).  Do **not** import
`Submission.Work.EQ.no_near_axis_segment` nor `Submission.Work.EQ.tail_bound_of_words`.

(The result is the case-(iii) exclusion: for a small annulus of ratio `> 1/λ` and a fixed value
`c₀` there is `η > 0` such that no chain of `⁰H` over the annulus has its index-`0` point equal
to a fan value whose map is `η`-flat in the semi-projective sense at the parameter `ψ₁`.) -/
theorem flattening_impossible {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δres : ℝ, 0 < δres ∧ ∀ (r₁ r₂ : ℝ) (c₀ : ℂ),
      0 < r₁ → r₁ < r₂ → r₂ < δres → 1 / Work.EQ.eqLam a < r₂ / r₁ →
      ∃ η : ℝ, 0 < η ∧ ∀ (q : Work.EQ.ChainData), q ∈ Work.EQ.H0 a h →
        q.2.1 ∈ Work.EQ.Ann r₁ r₂ → q.2.1 * q.2.2 = c₀ → ∀ ε : List Bool,
        q.1 0 = Work.EQ.fan a h ε q.2.1 →
        ¬ (‖(Work.EQ.fan a h ε q.2.1).1 - (Work.EQ.fan a h ε 0).1‖ < η ∧
           ‖(Work.EQ.fan a h ε q.2.1).2‖ < η *
             ‖(Work.EQ.fan a h ε q.2.1).1 - ((a / 2 : ℝ) : ℂ)‖) := by

  obtain ⟨δE, Ke, Lam, hδEpos, hKepos, hLampos, hE⟩ :=
    FanUniform.fan_uniform_estimates ha0 ha1 hh
  obtain ⟨-, hctr⟩ := FanSep.axis_walk ha0 ha1 hh
  obtain ⟨ρ, hρpos, hρ⟩ := H0_invParam_ge ha0 ha1 hh
  have hl0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  set K : ℝ := max Ke Lam with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le hKepos (le_max_left _ _)
  have hKest : ∀ (ε : List Bool) (u : ℂ), u ∈ Metric.ball (0 : ℂ) δE →
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ Ke * ‖u‖ ∧
      ‖(fan a h ε u).2‖ ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ :=
    fun ε u hu => (hE ε).2 u hu
  have hctr' : ∀ ε : List Bool, ∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k :=
    fun ε => (hctr ε).2
  have hnnD : 0 < Work.EQ.LaNnas.nnD a := by rw [Work.EQ.LaNnas.nnD]; linarith
  have hnnDq : Work.EQ.LaNnas.nnD a ≤ 1 / 4 := Work.EQ.LaNnas.nnD_le_quarter ha0
  have hnnC1 : 1 ≤ Work.EQ.LaNnas.nnC a := Work.EQ.LaNnas.nnC_ge_one ha0 ha1
  have hnnCpos : 0 < Work.EQ.LaNnas.nnC a := lt_of_lt_of_le one_pos hnnC1
  refine ⟨min δE (1 / (4 * K)), lt_min hδEpos (by positivity), ?_⟩
  intro r₁ r₂ c₀ hr₁ hr₁₂ hr₂ hrratio
  have hr₂K : K * r₂ < 1 / 4 := by
    have h1 : r₂ < 1 / (4 * K) := lt_of_lt_of_le hr₂ (min_le_right _ _)
    have h2 : K * r₂ < K * (1 / (4 * K)) := mul_lt_mul_of_pos_left h1 hKpos
    have h3 : K * (1 / (4 * K)) = 1 / 4 := by field_simp
    linarith [h2, h3]
  -- the uniform bound on the positive reading levels
  set μ : ℝ := max ‖c₀‖ ρ with hμdef
  have hμpos : 0 < μ := lt_of_lt_of_le hρpos (le_max_right _ _)
  have hμc : ‖c₀‖ ≤ μ := le_max_left _ _
  obtain ⟨L₀, hL₀⟩ : ∃ N : ℕ, (eqLam a) ^ N ≤ r₁ ^ 2 / μ := by
    have hlim : Tendsto (fun N : ℕ => (eqLam a) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hl0.le hl1
    have hpos : 0 < r₁ ^ 2 / μ := by positivity
    obtain ⟨N, hN⟩ := (hlim.eventually (eventually_lt_nhds hpos)).exists
    exact ⟨N, le_of_lt hN⟩
  refine ⟨(Work.EQ.LaNnas.nnD a / 4) * (Work.EQ.LaNnas.nnC a) ^ (-(L₀ : ℤ)), by positivity, ?_⟩
  rintro q hqH hqA hval ε hε ⟨hfl1, hfl2⟩
  have hchain : IsChain a h q := la_isChain_of_mem_H0 hqH
  have hu1 : r₁ ≤ ‖q.2.1‖ := hqA.1
  have hu2 : ‖q.2.1‖ ≤ r₂ := hqA.2
  have hu0 : 0 < ‖q.2.1‖ := lt_of_lt_of_le hr₁ hu1
  have hv0 : 0 < ‖q.2.2‖ := norm_pos_iff.mpr hchain.2.2.1
  have hnorm : ‖q.2.2‖ = ‖c₀‖ / ‖q.2.1‖ := by
    rw [eq_div_iff (ne_of_gt hu0), mul_comm, ← norm_mul, hval]
  have hvle : ‖q.2.2‖ ≤ ‖c₀‖ / r₁ := by
    rw [hnorm]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hr₁ hu1
  obtain ⟨l, hl1z, hl2z⟩ := la_exists_zpow_mem ha0 ha1 hr₁ hr₁₂ hrratio hv0
  have hznorm : ‖(((eqLam a : ℝ) : ℂ) ^ l * q.2.2)‖ = (eqLam a) ^ l * ‖q.2.2‖ := by
    rw [norm_mul, ← Complex.ofReal_zpow, la_norm_lamC_zpow' ha0 ha1 l]
  have hznorm' : ‖(((eqLam a : ℝ) : ℂ) ^ (-l) * q.2.1)‖
      = (eqLam a) ^ (-l) * ‖q.2.1‖ := by
    rw [norm_mul, ← Complex.ofReal_zpow, la_norm_lamC_zpow' ha0 ha1 (-l)]
  have hwr : ‖(((eqLam a : ℝ) : ℂ) ^ l * q.2.2)‖ < δE := by
    rw [hznorm]
    exact lt_of_le_of_lt hl2z (lt_of_lt_of_le hr₂ (min_le_left _ _))
  by_cases hle : l ≤ 0
  · -- `l ≤ 0`: both readings at the level `-l ≥ 0` are close to the axis
    have hzle : (eqLam a) ^ (-l) ≤ 1 := by
      rw [show -l = (((-l).toNat : ℕ) : ℤ) by omega, zpow_natCast]
      exact pow_le_one₀ hl0.le hl1.le
    obtain ⟨ε', hε'⟩ := la_fan_reading ha0 ha1 hchain (-l)
    obtain ⟨η', hη'⟩ := la_mirror_fan_reading ha0 ha1 hchain l
    have hwr' : ‖(((eqLam a : ℝ) : ℂ) ^ (-l) * q.2.1)‖ < δE := by
      rw [hznorm']
      calc (eqLam a) ^ (-l) * ‖q.2.1‖ ≤ 1 * ‖q.2.1‖ :=
            mul_le_mul_of_nonneg_right hzle (norm_nonneg _)
        _ = ‖q.2.1‖ := one_mul _
        _ < δE := lt_of_le_of_lt hu2 (lt_of_lt_of_le hr₂ (min_le_left _ _))
    have hSn : Work.EQ.LaNnas.SnNear a (q.1 (-l)) (K * r₂) := by
      have hbase := la_fan_SnNear (a := a) ha0 ha1 (h := h) (η := ε')
        (w := (((eqLam a : ℝ) : ℂ) ^ (-l) * q.2.1)) hKest hctr' hwr'
      rw [← hε'] at hbase
      refine hbase.mono ?_
      have h1 : ‖(((eqLam a : ℝ) : ℂ) ^ (-l) * q.2.1)‖ ≤ r₂ := by
        rw [hznorm']
        calc (eqLam a) ^ (-l) * ‖q.2.1‖ ≤ 1 * ‖q.2.1‖ :=
              mul_le_mul_of_nonneg_right hzle (norm_nonneg _)
          _ = ‖q.2.1‖ := one_mul _
          _ ≤ r₂ := hu2
      exact mul_le_mul_of_nonneg_left h1 hKpos.le
    have hUn : Work.EQ.LaNnas.UnNear a (q.1 (-l)) (K * r₂) := by
      have hbase := la_mirror_fan_UnNear ha0 ha1 hh (η := η')
        (w := (((eqLam a : ℝ) : ℂ) ^ l * q.2.2)) hKest hctr' hwr
      rw [← hη'] at hbase
      refine hbase.mono ?_
      have h2 : ‖(((eqLam a : ℝ) : ℂ) ^ l * q.2.2)‖ ≤ r₂ := by
        rw [hznorm]; exact hl2z
      exact mul_le_mul_of_nonneg_left h2 hKpos.le
    exact Work.EQ.LaNnas.not_un_and_sn (by linarith [hr₂K, hnnDq]) hUn hSn
  · -- `l > 0`: the flat stable end propagates backward to the unstable end
    push Not at hle
    have hlpos : (0 : ℤ) ≤ l := le_of_lt hle
    have hlz : r₁ ^ 2 / μ ≤ (eqLam a) ^ l := by
      have h1 : r₁ ≤ (eqLam a) ^ l * ‖q.2.2‖ := hl1z
      have h2 : (eqLam a) ^ l * ‖q.2.2‖ ≤ (eqLam a) ^ l * (‖c₀‖ / r₁) :=
        mul_le_mul_of_nonneg_left hvle (zpow_nonneg hl0.le l)
      have h3 : (eqLam a) ^ l * (‖c₀‖ / r₁) = (eqLam a) ^ l * ‖c₀‖ / r₁ := by ring
      have h4 : r₁ ≤ (eqLam a) ^ l * ‖c₀‖ / r₁ := by
        rw [← h3]; exact le_trans h1 h2
      rw [le_div_iff₀ hr₁] at h4
      rw [div_le_iff₀ hμpos]
      nlinarith [h4, hμc, hr₁, norm_nonneg c₀]
    have hlL₀ : l.toNat ≤ L₀ := by
      by_contra hcon
      push Not at hcon
      have h1 : L₀ + 1 ≤ l.toNat := by omega
      have h2 : (eqLam a) ^ l.toNat ≤ (eqLam a) ^ (L₀ + 1) :=
        pow_le_pow_of_le_one hl0.le hl1.le h1
      have h3 : (eqLam a) ^ (L₀ + 1) < (eqLam a) ^ L₀ := by
        rw [pow_succ]; nlinarith [pow_pos hl0 L₀, hl1]
      have h4 : (eqLam a) ^ l = (eqLam a) ^ l.toNat := by
        conv_lhs => rw [show l = (((l.toNat : ℕ)) : ℤ) by omega]
        rw [zpow_natCast]
      have h5 : (eqLam a) ^ L₀ ≤ (eqLam a) ^ l.toNat := by
        rw [← h4]; exact le_trans hL₀ hlz
      linarith
    obtain ⟨η', hη'⟩ := la_mirror_fan_reading ha0 ha1 hchain l
    have hUn : Work.EQ.LaNnas.UnNear a (q.1 (-l)) (K * r₂) := by
      have hbase := la_mirror_fan_UnNear ha0 ha1 hh (η := η')
        (w := (((eqLam a : ℝ) : ℂ) ^ l * q.2.2)) hKest hctr' hwr
      rw [← hη'] at hbase
      refine hbase.mono ?_
      have h2 : ‖(((eqLam a : ℝ) : ℂ) ^ l * q.2.2)‖ ≤ r₂ := by
        rw [hznorm]; exact hl2z
      exact mul_le_mul_of_nonneg_left h2 hKpos.le
    have hSn0 : Work.EQ.LaNnas.SnNear a (q.1 0) ((Work.EQ.LaNnas.nnD a / 4) * (Work.EQ.LaNnas.nnC a) ^ (-(L₀ : ℤ))) := by
      obtain ⟨k, hk⟩ := hctr' ε
      refine ⟨k, ?_, ?_⟩
      · rw [hε]
        rw [hk] at hfl1
        exact le_of_lt hfl1
      · rw [hε]
        exact le_of_lt hfl2
    have hsmall : ∀ n : ℕ, n ≤ l.toNat →
        ((Work.EQ.LaNnas.nnD a / 4) * (Work.EQ.LaNnas.nnC a) ^ (-(L₀ : ℤ))) * (Work.EQ.LaNnas.nnC a) ^ n ≤ Work.EQ.LaNnas.nnD a := by
      intro n hn
      have hnL : n ≤ L₀ := le_trans hn hlL₀
      have hpow : (Work.EQ.LaNnas.nnC a) ^ n ≤ (Work.EQ.LaNnas.nnC a) ^ L₀ := pow_le_pow_right₀ hnnC1 hnL
      have hz : (Work.EQ.LaNnas.nnC a) ^ (-(L₀ : ℤ)) = ((Work.EQ.LaNnas.nnC a) ^ L₀)⁻¹ := by
        rw [zpow_neg, zpow_natCast]
      have h1 : (Work.EQ.LaNnas.nnC a) ^ n * ((Work.EQ.LaNnas.nnC a) ^ L₀)⁻¹ ≤ 1 := by
        rw [inv_eq_one_div, mul_one_div, div_le_one (pow_pos hnnCpos L₀)]
        exact hpow
      calc ((Work.EQ.LaNnas.nnD a / 4) * (Work.EQ.LaNnas.nnC a) ^ (-(L₀ : ℤ))) * (Work.EQ.LaNnas.nnC a) ^ n
          = (Work.EQ.LaNnas.nnD a / 4) * ((Work.EQ.LaNnas.nnC a) ^ n * ((Work.EQ.LaNnas.nnC a) ^ L₀)⁻¹) := by rw [hz]; ring
        _ ≤ (Work.EQ.LaNnas.nnD a / 4) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ Work.EQ.LaNnas.nnD a := by linarith [hnnD]
    have hstep : ∀ j : ℕ, j < l.toNat →
        RegPair a (q.1 (((j : ℤ) - l))) (q.1 ((((j + 1 : ℕ)) : ℤ) - l)) := by
      intro j hj
      have := hchain.1 (((j : ℤ) - l))
      convert this using 2
      push_cast
      ring
    have hprop := Work.EQ.LaNnas.propagate_bwd ha0 ha1 l.toNat (fun j => q.1 (((j : ℤ) - l)))
      ((Work.EQ.LaNnas.nnD a / 4) * (Work.EQ.LaNnas.nnC a) ^ (-(L₀ : ℤ))) hstep (by positivity) hsmall ?_
    · have h1 : ((Work.EQ.LaNnas.nnD a / 4) * (Work.EQ.LaNnas.nnC a) ^ (-(L₀ : ℤ))) * (Work.EQ.LaNnas.nnC a) ^ l.toNat ≤ Work.EQ.LaNnas.nnD a :=
        hsmall l.toNat le_rfl
      have hSn : Work.EQ.LaNnas.SnNear a (q.1 (-l)) (Work.EQ.LaNnas.nnD a) := by
        have := hprop.mono h1
        simpa using this
      exact Work.EQ.LaNnas.not_un_and_sn (by linarith [hr₂K, hnnDq]) hUn hSn
    · show Work.EQ.LaNnas.SnNear a (q.1 (((l.toNat : ℤ) - l))) ((Work.EQ.LaNnas.nnD a / 4) * (Work.EQ.LaNnas.nnC a) ^ (-(L₀ : ℤ)))
      have h0 : ((l.toNat : ℤ) - l) = 0 := by omega
      rw [h0]
      exact hSn0

end

end Work.EQ.LaTB
