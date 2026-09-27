import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.la_nnas
import Submission.Work.EQ.FanUniform.fan_uniform_estimates
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.H0_invParam_ge

namespace Work.EQ.LaTB

open Work.EQ Complex Filter _root_.Topology

/-! ## Local copies of the reading and near-axis helpers

The private helpers of `Submission/Work/EQ/tail_bound_of_words.lean` cannot be imported, and the
`Work.EQ.LaNnas.*` copies of the near-axis vocabulary live in `Submission/Work/EQ/la_nnas.lean`.
Everything this file needs beyond those is reproduced here (with `laB_` prefixed names, so that
nothing collides with the companion `Submission/Work/EQ/LaTB/flattening_impossible.lean`). -/

/-- Helper: the norm of a real zpow. -/
theorem laB_norm_lamC_zpow' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (l : ℤ) :
    ‖(((eqLam a) ^ l : ℝ) : ℂ)‖ = (eqLam a) ^ l := by
  rw [LaNnas.norm_ofReal_eq_abs, abs_of_pos (zpow_pos (eqLam_pos' ha0 ha1) l)]

/-- Every point of `H0` is a chain. -/
theorem laB_isChain_of_mem_H0 {a : ℝ} {h : ℂ → ℂ} {q : ChainData} (hq : q ∈ H0 a h) :
    IsChain a h q := by
  obtain ⟨ε, hε, f, hcont, hf0, hf⟩ := hq
  have hmem : q.2.1 ∈ Metric.ball q.2.1 ε := by
    rw [Metric.mem_ball, dist_self]; exact hε
  rw [← hf0]
  exact (hf q.2.1 hmem).1

/-- **The stable fan reading of a chain at an arbitrary level.** -/
theorem laB_fan_reading {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {q : ChainData}
    (hq : IsChain a h q) (l : ℤ) :
    ∃ ε : List Bool, q.1 l = fan a h ε (((eqLam a : ℝ) : ℂ) ^ l * q.2.1) := by
  obtain ⟨ε, hε⟩ := chain_eq_fan' ha0 ha1 (isChain_shiftZ ha0 ha1 hq l)
  exact ⟨ε, by rw [show q.1 l = (shiftZ a l q).1 0 by simp, hε, shiftZ_psi1]⟩

/-- **A fan value at a small parameter is stable-near its centre.** -/
theorem laB_fan_SnNear {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {η : List Bool} {w : ℂ} {δE Ke Lam : ℝ}
    (hest : ∀ (ε : List Bool) (u : ℂ), u ∈ Metric.ball (0 : ℂ) δE →
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ Ke * ‖u‖ ∧
      ‖(fan a h ε u).2‖ ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖)
    (hctr : ∀ ε : List Bool, ∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k)
    (hw : ‖w‖ < δE) :
    LaNnas.SnNear a (fan a h η w) (max Ke Lam * ‖w‖) := by
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



/-- **The unstable-side form of the shrinking-fan exclusion.**

A verbatim copy, in a fresh namespace and proved with the `Work.EQ.LaNnas.*` near-axis
vocabulary, of `Work.EQ.tb_flattening_impossible_bwd` from
`Submission/Work/EQ/tail_bound_of_words.lean`.  The reason for the copy is only importability
(see `Work.EQ.LaTB.flattening_impossible`).

Proof: copy `tb_flattening_impossible_bwd` verbatim, renaming it `la_*` and replacing every
reference to `SnNear`, `UnNear`, `SnNear.mono`, `UnNear.mono`, `not_un_and_sn`, `propagate_fwd`,
`propagate_bwd`, `nnK`, `nnC`, `nnD`, `nnK_pos`, `nnD_pos`, `nnD_le_quarter`, `nnC_pos`,
`nnC_ge_one`, `nnK_ge_one`, `nnK_mul_nnD_le`, `nnK_le_nnC` by `Work.EQ.LaNnas.<same name>`.
The private helpers of that file cannot be imported (`tb_norm_lamC_zpow'`,
`tb_mirror_fan_UnNear`, `tb_fan_SnNear`) and the public ones `tb_norm_lamC_zpow`,
`tb_eqMirror_involutive`, `tb_exists_zpow_mem`, `tb_fan_reading`, `tb_mirror_fan_reading` live
only in the unimportable file: the companion file
`Submission/Work/EQ/LaTB/flattening_impossible.lean` should carry copies of them (as `la_*`);
import it and use them.  Do **not** import `Submission.Work.EQ.no_near_axis_segment` nor
`Submission.Work.EQ.tail_bound_of_words`.

(This is the case-(iii) exclusion for the unstable side: for a chain `q ∈ ⁰H` over a small
annulus of ratio `> 1/λ` of value `c₀`, read at a level `-l` where the unstable parameter
`λ^l ψ₂ q` again lies in the *same* annulus, the mirror fan map of the reading word cannot be
`η`-flat at that parameter.  The lower bound `r₁ ≤ λ^l ‖ψ₂ q‖` is essential — without it the
statement is false, since `l → ∞` makes `λ^l ψ₂ q → 0` and the fan estimates force flatness.) -/
theorem flattening_impossible_bwd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δres : ℝ, 0 < δres ∧ ∀ (r₁ r₂ : ℝ) (c₀ : ℂ),
      0 < r₁ → r₁ < r₂ → r₂ < δres → 1 / Work.EQ.eqLam a < r₂ / r₁ →
      ∃ η : ℝ, 0 < η ∧ ∀ (q : Work.EQ.ChainData) (l : ℤ) (η' : List Bool), q ∈ Work.EQ.H0 a h →
        q.2.1 ∈ Work.EQ.Ann r₁ r₂ → q.2.1 * q.2.2 = c₀ →
        r₁ ≤ (Work.EQ.eqLam a) ^ l * ‖q.2.2‖ → (Work.EQ.eqLam a) ^ l * ‖q.2.2‖ ≤ r₂ →
        q.1 (-l) = Work.EQ.eqMirror (Work.EQ.fan a h η' (((Work.EQ.eqLam a : ℝ) : ℂ) ^ l * q.2.2)) →
        ¬ (‖(Work.EQ.fan a h η' (((Work.EQ.eqLam a : ℝ) : ℂ) ^ l * q.2.2)).1 -
              (Work.EQ.fan a h η' 0).1‖ < η ∧
           ‖(Work.EQ.fan a h η' (((Work.EQ.eqLam a : ℝ) : ℂ) ^ l * q.2.2)).2‖ <
             η * ‖(Work.EQ.fan a h η' (((Work.EQ.eqLam a : ℝ) : ℂ) ^ l * q.2.2)).1 -
                   ((a / 2 : ℝ) : ℂ)‖) := by
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
  have hnnD : 0 < LaNnas.nnD a := by rw [LaNnas.nnD]; linarith
  have hnnDq : LaNnas.nnD a ≤ 1 / 4 := LaNnas.nnD_le_quarter ha0
  have hnnC1 : 1 ≤ LaNnas.nnC a := LaNnas.nnC_ge_one ha0 ha1
  have hnnCpos : 0 < LaNnas.nnC a := lt_of_lt_of_le one_pos hnnC1
  refine ⟨min δE (1 / (4 * K)), lt_min hδEpos (by positivity), ?_⟩
  intro r₁ r₂ c₀ hr₁ hr₁₂ hr₂ hrratio
  have hr₂K : K * r₂ < 1 / 4 := by
    have h1 : r₂ < 1 / (4 * K) := lt_of_lt_of_le hr₂ (min_le_right _ _)
    have h2 : K * r₂ < K * (1 / (4 * K)) := mul_lt_mul_of_pos_left h1 hKpos
    have h3 : K * (1 / (4 * K)) = 1 / 4 := by field_simp
    linarith [h2, h3]
  set μ : ℝ := max ‖c₀‖ ρ with hμdef
  have hμpos : 0 < μ := lt_of_lt_of_le hρpos (le_max_right _ _)
  have hμc : ‖c₀‖ ≤ μ := le_max_left _ _
  obtain ⟨L₀, hL₀⟩ : ∃ N : ℕ, (eqLam a) ^ N ≤ r₁ ^ 2 / μ := by
    have hlim : Tendsto (fun N : ℕ => (eqLam a) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hl0.le hl1
    have hpos : 0 < r₁ ^ 2 / μ := by positivity
    obtain ⟨N, hN⟩ := (hlim.eventually (eventually_lt_nhds hpos)).exists
    exact ⟨N, le_of_lt hN⟩
  have hηle : (LaNnas.nnD a / 4) * (LaNnas.nnC a) ^ (-(L₀ : ℤ)) ≤ LaNnas.nnD a / 4 := by
    have h1 : (LaNnas.nnC a) ^ (-(L₀ : ℤ)) ≤ 1 := by
      rw [zpow_neg, zpow_natCast, inv_le_one₀ (pow_pos hnnCpos L₀)]
      exact one_le_pow₀ hnnC1
    nlinarith [hnnD, h1]
  refine ⟨(LaNnas.nnD a / 4) * (LaNnas.nnC a) ^ (-(L₀ : ℤ)), by positivity, ?_⟩
  rintro q l η' hqH hqA hval hl1z hl2z hread ⟨hfl1, hfl2⟩
  have hchain : IsChain a h q := laB_isChain_of_mem_H0 hqH
  have hu1 : r₁ ≤ ‖q.2.1‖ := hqA.1
  have hu2 : ‖q.2.1‖ ≤ r₂ := hqA.2
  have hv0 : 0 < ‖q.2.2‖ := norm_pos_iff.mpr hchain.2.2.1
  -- the LaNnas.UnNear at the level `-l`, straight from the flatness
  have hUn : LaNnas.UnNear a (q.1 (-l)) (LaNnas.nnD a / 4 * (LaNnas.nnC a) ^ (-(L₀ : ℤ))) := by
    obtain ⟨k, hk⟩ := hctr' η'
    refine ⟨-k, ?_, ?_⟩
    · have hc : (1 / 2 + 2 * (((-k : ℤ)) : ℂ)) = -(fan a h η' 0).1 := by
        rw [hk]; push_cast; ring
      rw [hread]
      simp only [eqMirror]
      rw [hc]
      rw [show (-(fan a h η' _).1 - -(fan a h η' 0).1)
          = -((fan a h η' _).1 - (fan a h η' 0).1) by ring, norm_neg]
      exact le_of_lt hfl1
    · rw [hread]
      simp only [eqMirror]
      rw [show (-(fan a h η' _).1 + ((a / 2 : ℝ) : ℂ))
          = -((fan a h η' _).1 - ((a / 2 : ℝ) : ℂ)) by ring, norm_neg]
      exact le_of_lt hfl2
  -- the stable reading at the level `-l`
  obtain ⟨ε', hε'⟩ := laB_fan_reading ha0 ha1 hchain (-l)
  have hznorm' : ‖(((eqLam a : ℝ) : ℂ) ^ (-l) * q.2.1)‖
      = (eqLam a) ^ (-l) * ‖q.2.1‖ := by
    rw [norm_mul, ← Complex.ofReal_zpow, laB_norm_lamC_zpow' ha0 ha1 (-l)]
  by_cases hle : l ≤ 0
  · -- `l ≤ 0`: the stable parameter at the level `-l` is small
    have hzle : (eqLam a) ^ (-l) ≤ 1 := by
      rw [show -l = (((-l).toNat : ℕ) : ℤ) by omega, zpow_natCast]
      exact pow_le_one₀ hl0.le hl1.le
    have hwr' : ‖(((eqLam a : ℝ) : ℂ) ^ (-l) * q.2.1)‖ < δE := by
      rw [hznorm']
      calc (eqLam a) ^ (-l) * ‖q.2.1‖ ≤ 1 * ‖q.2.1‖ :=
            mul_le_mul_of_nonneg_right hzle (norm_nonneg _)
        _ = ‖q.2.1‖ := one_mul _
        _ < δE := lt_of_le_of_lt hu2 (lt_of_lt_of_le hr₂ (min_le_left _ _))
    have hbase := laB_fan_SnNear (a := a) ha0 ha1 (h := h) (η := ε')
      (w := (((eqLam a : ℝ) : ℂ) ^ (-l) * q.2.1)) hKest hctr' hwr'
    rw [← hε'] at hbase
    have h1 : ‖(((eqLam a : ℝ) : ℂ) ^ (-l) * q.2.1)‖ ≤ r₂ := by
      rw [hznorm']
      calc (eqLam a) ^ (-l) * ‖q.2.1‖ ≤ 1 * ‖q.2.1‖ :=
            mul_le_mul_of_nonneg_right hzle (norm_nonneg _)
        _ = ‖q.2.1‖ := one_mul _
        _ ≤ r₂ := hu2
    have hSn : LaNnas.SnNear a (q.1 (-l)) (K * r₂) :=
      hbase.mono (mul_le_mul_of_nonneg_left h1 hKpos.le)
    exact LaNnas.not_un_and_sn (by linarith [hr₂K, hnnDq, hηle]) hUn hSn
  · -- `l > 0`: propagate the flat (unstable) end forward to the stable end
    push Not at hle
    have hz : r₁ ^ 2 / μ ≤ (eqLam a) ^ l := by
      have h1 : r₁ ≤ (eqLam a) ^ l * ‖q.2.2‖ := hl1z
      have hvle : ‖q.2.2‖ ≤ ‖c₀‖ / r₁ := by
        have hnorm : ‖q.2.2‖ = ‖c₀‖ / ‖q.2.1‖ := by
          have hu0 : 0 < ‖q.2.1‖ := lt_of_lt_of_le hr₁ hu1
          rw [eq_div_iff (ne_of_gt hu0), mul_comm, ← norm_mul, hval]
        rw [hnorm]
        exact div_le_div_of_nonneg_left (norm_nonneg _) hr₁ hu1
      have h2 : (eqLam a) ^ l * ‖q.2.2‖ ≤ (eqLam a) ^ l * (‖c₀‖ / r₁) :=
        mul_le_mul_of_nonneg_left hvle (zpow_nonneg hl0.le l)
      have h3 : (eqLam a) ^ l * (‖c₀‖ / r₁) = (eqLam a) ^ l * ‖c₀‖ / r₁ := by ring
      have h4 : r₁ ≤ (eqLam a) ^ l * ‖c₀‖ / r₁ := by rw [← h3]; exact le_trans h1 h2
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
        rw [← h4]; exact le_trans hL₀ hz
      linarith
    have hsmall : ∀ n : ℕ, n ≤ l.toNat →
        ((LaNnas.nnD a / 4) * (LaNnas.nnC a) ^ (-(L₀ : ℤ))) * (LaNnas.nnC a) ^ n ≤ LaNnas.nnD a := by
      intro n hn
      have hnL : n ≤ L₀ := le_trans hn hlL₀
      have hpow : (LaNnas.nnC a) ^ n ≤ (LaNnas.nnC a) ^ L₀ := pow_le_pow_right₀ hnnC1 hnL
      have hz' : (LaNnas.nnC a) ^ (-(L₀ : ℤ)) = ((LaNnas.nnC a) ^ L₀)⁻¹ := by
        rw [zpow_neg, zpow_natCast]
      have h1 : (LaNnas.nnC a) ^ n * ((LaNnas.nnC a) ^ L₀)⁻¹ ≤ 1 := by
        rw [inv_eq_one_div, mul_one_div, div_le_one (pow_pos hnnCpos L₀)]
        exact hpow
      calc ((LaNnas.nnD a / 4) * (LaNnas.nnC a) ^ (-(L₀ : ℤ))) * (LaNnas.nnC a) ^ n
          = (LaNnas.nnD a / 4) * ((LaNnas.nnC a) ^ n * ((LaNnas.nnC a) ^ L₀)⁻¹) := by rw [hz']; ring
        _ ≤ (LaNnas.nnD a / 4) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ LaNnas.nnD a := by linarith [hnnD]
    have hstep : ∀ j : ℕ, j < l.toNat →
        RegPair a (q.1 (((j : ℤ) - l))) (q.1 ((((j + 1 : ℕ)) : ℤ) - l)) := by
      intro j hj
      have := hchain.1 (((j : ℤ) - l))
      convert this using 2
      push_cast
      ring
    have hprop := LaNnas.propagate_fwd ha0 ha1 l.toNat (fun j => q.1 (((j : ℤ) - l)))
      ((LaNnas.nnD a / 4) * (LaNnas.nnC a) ^ (-(L₀ : ℤ))) hstep (by positivity) hsmall ?_
    · have h1 : (LaNnas.nnD a / 4 * (LaNnas.nnC a) ^ (-(L₀ : ℤ))) * (LaNnas.nnC a) ^ l.toNat ≤ LaNnas.nnD a :=
        hsmall l.toNat le_rfl
      have hbase := hprop.mono h1
      -- the stable reading at level 0
      obtain ⟨ε, hε⟩ := laB_fan_reading ha0 ha1 hchain 0
      have hwr0 : ‖(((eqLam a : ℝ) : ℂ) ^ (0 : ℤ) * q.2.1)‖ < δE := by
        rw [zpow_zero, one_mul]
        exact lt_of_le_of_lt hu2 (lt_of_lt_of_le hr₂ (min_le_left _ _))
      have hb0 := laB_fan_SnNear (a := a) ha0 ha1 (h := h) (η := ε)
        (w := (((eqLam a : ℝ) : ℂ) ^ (0 : ℤ) * q.2.1)) hKest hctr' hwr0
      rw [← hε] at hb0
      have h2 : ‖(((eqLam a : ℝ) : ℂ) ^ (0 : ℤ) * q.2.1)‖ ≤ r₂ := by
        rw [zpow_zero, one_mul]; exact hu2
      have hSn : LaNnas.SnNear a (q.1 0) (K * r₂) :=
        hb0.mono (mul_le_mul_of_nonneg_left h2 hKpos.le)
      have hUn0 : LaNnas.UnNear a (q.1 0) (LaNnas.nnD a) := by
        have : LaNnas.UnNear a (q.1 (((l.toNat : ℤ) - l))) (LaNnas.nnD a) := by
          simpa using hbase
        have h0 : ((l.toNat : ℤ) - l) = 0 := by omega
        rwa [h0] at this
      exact LaNnas.not_un_and_sn (by linarith [hr₂K, hnnDq, hηle]) hUn0 hSn
    · show LaNnas.UnNear a (q.1 (((0 : ℕ) : ℤ) - l)) ((LaNnas.nnD a / 4) * (LaNnas.nnC a) ^ (-(L₀ : ℤ)))
      rw [show (((0 : ℕ) : ℤ) - l) = -l by ring]
      exact hUn

end Work.EQ.LaTB
