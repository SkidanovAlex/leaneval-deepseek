import Mathlib
import Submission.Work.Anchor.Xi_contDiffOn
import Submission.Work.OddVolterra.Existence.aw_xi_smooth
import Submission.Work.Anchor.Xif_contDiff
import Submission.Work.OddExistence.Manifest.thetaM_lipschitz
import Submission.Work.OddVolterra.Existence.krad_pos_state_region
import Submission.Work.OddVolterra.WinData.win_data

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

open Work.OddVolterra
open Work.OddVolterra.KernelExt

noncomputable section

/-! ## Two elementary facts about the ball profile and the Abel radicand

These are needed for the smoothness of the frozen tail on the source window; they are proved
here (rather than imported) because the module holding their canonical form is not part of the
current build.  -/

/-- On `|s| ≤ 21/20` the ball profile stays above `17/25`. -/
lemma profileX_ge_17_25' {s : ℝ} (hs : |s| ≤ 21 / 20) :
    17 / 25 ≤ Commons.Geometry.Ulam.profileX s := by
  have hs2 : s ^ 2 ≤ (21 / 20 : ℝ) ^ 2 := by
    have h := abs_le.mp hs
    nlinarith [h.1, h.2]
  have hsq : Real.sqrt (1 + s ^ 2) ≤ 25 / 17 := by
    have hle : 1 + s ^ 2 ≤ (25 / 17 : ℝ) ^ 2 := by nlinarith [hs2]
    calc Real.sqrt (1 + s ^ 2) ≤ Real.sqrt ((25 / 17 : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
      _ = 25 / 17 := Real.sqrt_sq (by norm_num)
  rw [Commons.Geometry.Ulam.profileX, le_div_iff₀ (Real.sqrt_pos.mpr (by positivity))]
  calc 17 / 25 * Real.sqrt (1 + s ^ 2) ≤ 17 / 25 * (25 / 17) :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 1 := by norm_num

/-- **Positivity of the Abel radicand for large slopes.**  If `h` is supported in the transition
window with `C¹`-norm at most `1/100`, then for `σ + a > 1/10` and `|t| ≥ 1/5` both factors of

`krad h σ t a = (t + H(a,σ)) (L_σ(t) + L_a(t))`

have the sign of `t`.  (No upper bound on the slopes is needed.) -/
lemma krad_pos_of_add_pos' {h : ℝ → ℝ}
    (_hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {a σ t : ℝ} (hS : 1 / 10 < σ + a) (ht : 1 / 5 ≤ |t|) : 0 < krad h σ t a := by
  have hh0 : ∀ x : ℝ, |h x| ≤ 1 / 100 := fun x => hsmall 0 (by norm_num) x
  have hh1 : ∀ x : ℝ, |deriv h x| ≤ 1 / 100 := by
    intro x; simpa using hsmall 1 (by norm_num) x
  have hbnd : |hquot h a σ| ≤ 1 / 100 := Existence.abs_hquot_le_state hh1
  have hb := abs_le.mp hbnd
  have hhl : |h σ + h a| ≤ 1 / 50 := by
    have h1 := abs_le.mp (hh0 σ)
    have h2 := abs_le.mp (hh0 a)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hSpos : 0 < σ + a := by linarith
  have hsumlt : |h σ + h a| < (σ + a) * (1 / 5) := by
    have h1 : (1 / 10 : ℝ) * (1 / 5) ≤ (σ + a) * (1 / 5) :=
      mul_le_mul_of_nonneg_right (le_of_lt hS) (by norm_num)
    have h2 : (1 / 10 : ℝ) * (1 / 5) = 1 / 50 := by norm_num
    linarith [hhl, h1, h2]
  have hhline : line h σ t + line h a t = (σ + a) * t + (h σ + h a) := by
    unfold line; ring
  rw [krad_apply, hhline]
  rcases lt_trichotomy t 0 with htn | htz | htp
  · have htle : t ≤ -(1 / 5) := by
      have h := ht; rw [abs_of_neg htn] at h; linarith
    have h1 : t + hquot h a σ < 0 := by linarith [hb.2]
    have hmul : (σ + a) * t ≤ -((σ + a) * (1 / 5)) := by
      have h := mul_le_mul_of_nonneg_left htle (le_of_lt hSpos)
      rwa [show (σ + a) * (-(1 / 5)) = -((σ + a) * (1 / 5)) by ring] at h
    have h2 : (σ + a) * t + (h σ + h a) < 0 := by
      have h3 : h σ + h a < (σ + a) * (1 / 5) := lt_of_le_of_lt (le_abs_self _) hsumlt
      linarith
    exact mul_pos_of_neg_of_neg h1 h2
  · rw [htz] at ht; norm_num at ht
  · have htge : 1 / 5 ≤ t := by
      have h := ht; rwa [abs_of_pos htp] at h
    have h1 : 0 < t + hquot h a σ := by linarith [hb.1]
    have hmul : (σ + a) * (1 / 5) ≤ (σ + a) * t :=
      mul_le_mul_of_nonneg_left htge (le_of_lt hSpos)
    have h2 : 0 < (σ + a) * t + (h σ + h a) := by
      have h3 : -((σ + a) * (1 / 5)) < h σ + h a := by
        have h4 : -((σ + a) * (1 / 5)) < -|h σ + h a| := by linarith
        linarith [neg_abs_le (h σ + h a)]
      linarith
    exact mul_pos h1 h2

/-! ## The two summands of the source

The source of the odd windowed system is the sum of the paper's `Ξ` and the frozen tail

`∫_σ in 19/20..1, ΘM n h s σ (baseState σ)`.

Both are `C^∞` on the source window `(1/8, 99/100)`:

* `Ξ = ![profileX 1, profileX 1, Q̃ 0, Q̃ 1]` is smooth as soon as the Cauchy datum `Q n h` is
  `C^∞` on `(0,1)` and continuous up to `1`, which holds because the ball sections are
  non-degenerate (`aw_Q_contDiffOn`, `Q_regularity`) and the derivative of a truncated Abel
  transform of such a datum is `C^∞` on `(a,1)` (`aw_abel_deriv_contDiffOn`);
* the tail integrand `(s,σ) ↦ ΘM n h s σ (baseState σ)` is smooth on the open product
  `(1/8,99/100) ×ˢ (481/1000, 102/100)` because the manifest `Θ` is smooth on any region where the
  Abel radicand `krad` is positive at the two chord endpoints and along the whole `τ`-segment
  (`contDiffOn_KernelExtThetaM_of_pos`), and here the state is `baseState σ`, so both chord
  endpoints have modulus `≥ 17/25 - 9/20 > 1/5`, while `σ + a > 1/10` holds for every slope `a`
  on the segment (`krad_pos_of_add_pos`). The `σ`-integration is then a parametric integral over
  the fixed interval `[19/20,1]`, localised by the bump `psiT`. -/

/-- `Ξ` is `C^∞` on the source window `(1/8, 99/100)`. -/
lemma Xi_contDiffOn_window (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => Xi n h s) (Set.Ioo (1 / 8 : ℝ) (99 / 100)) := by
  have hsmall' : ∀ t : ℝ, |h t| ≤ 1 / 100 := by
    intro t
    have h0 := hsmall 0 (by norm_num) t
    rwa [iteratedDeriv_zero] at h0
  have hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1))
        (Commons.Geometry.Ulam.profileX 1),
      0 < psi h Commons.Geometry.Ulam.semicircle s t :=
    Existence.aw_hmid hsupp hsmall
  have hQcont : ContinuousOn (Q n h) (Set.Icc (1 / 8 : ℝ) 1) :=
    (Smooth.Q_regularity n hn hh (by norm_num) hsupp hsmall' hmid).1
  have hQsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (Q n h) (Set.Ioo (0 : ℝ) 1) :=
    Existence.aw_Q_contDiffOn n hn hh hsupp hsmall
  have hQtilde : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => deriv (fun u : ℝ => ∫ v in u..(1 : ℝ),
        (Q n h v) i / Real.sqrt (v - u)) s) (Set.Ioo (1 / 8 : ℝ) 1) :=
    fun i => Existence.aw_abel_deriv_contDiffOn (Q := fun v : ℝ => (Q n h v) i)
      (a := 1 / 8) (by norm_num) (by norm_num)
      ((contDiffOn_pi.mp hQsmooth) i) ((continuousOn_pi.mp hQcont) i)
  have hmain : ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => Xi n h s) (Set.Ioo (1 / 8 : ℝ) 1) := by
    have hfun : (fun s : ℝ => Xi n h s) = fun s : ℝ =>
        ![Commons.Geometry.Ulam.profileX 1, Commons.Geometry.Ulam.profileX 1,
          deriv (fun u : ℝ => ∫ v in u..(1 : ℝ), (Q n h v) 0 / Real.sqrt (v - u)) s,
          deriv (fun u : ℝ => ∫ v in u..(1 : ℝ), (Q n h v) 1 / Real.sqrt (v - u)) s] := by
      funext s
      simp [Xi, Qtilde]
    rw [hfun, contDiffOn_pi]
    intro i
    fin_cases i
    · simpa using (contDiffOn_const (c := Commons.Geometry.Ulam.profileX 1)
        (s := (Set.Ioo (1 / 8 : ℝ) 1 : Set ℝ)))
    · simpa using (contDiffOn_const (c := Commons.Geometry.Ulam.profileX 1)
        (s := (Set.Ioo (1 / 8 : ℝ) 1 : Set ℝ)))
    · simpa using hQtilde 0
    · simpa using hQtilde 1
  exact hmain.mono (fun s hs => ⟨hs.1, by linarith [hs.2]⟩)

/-- The frozen tail `s ↦ ∫_σ in 19/20..1, ΘM n h s σ (baseState σ)` is `C^∞` on the source
window `(1/8, 99/100)`. -/
lemma thetaM_tail_contDiffOn (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => ∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
        ThetaM n h s σ (baseState σ)) (Set.Ioo (1 / 8 : ℝ) (99 / 100)) := by
  -- the open region of the slope/state space on which the manifest kernel is smooth
  set U : Set (ℝ × (ℝ × St)) :=
    {q | 1 / 8 < q.1 ∧ q.1 < 99 / 100 ∧ 481 / 1000 < q.2.1 ∧ q.2.1 < 102 / 100 ∧
      ‖q.2.2 - baseState q.2.1‖ < 9 / 20} with hUdef
  have hUopen : IsOpen U := by
    rw [hUdef]
    have heq : {q : ℝ × (ℝ × St) |
        1 / 8 < q.1 ∧ q.1 < 99 / 100 ∧ 481 / 1000 < q.2.1 ∧ q.2.1 < 102 / 100 ∧
          ‖q.2.2 - baseState q.2.1‖ < 9 / 20} =
        {q : ℝ × (ℝ × St) | 1 / 8 < q.1} ∩ {q | q.1 < 99 / 100} ∩
        {q | 481 / 1000 < q.2.1} ∩ {q | q.2.1 < 102 / 100} ∩
        {q | ‖q.2.2 - baseState q.2.1‖ < 9 / 20} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5⟩
        exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
      · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
        exact ⟨h1, h2, h3, h4, h5⟩
    rw [heq]
    refine IsOpen.inter (IsOpen.inter (IsOpen.inter (IsOpen.inter ?_ ?_) ?_) ?_) ?_
    · exact isOpen_lt continuous_const continuous_fst
    · exact isOpen_lt continuous_fst continuous_const
    · exact isOpen_lt continuous_const (continuous_fst.comp continuous_snd)
    · exact isOpen_lt (continuous_fst.comp continuous_snd) continuous_const
    · have hc : Continuous (fun q : ℝ × (ℝ × St) => ‖q.2.2 - baseState q.2.1‖) :=
        continuous_norm.comp ((continuous_snd.comp continuous_snd).sub
          ((Work.Anchor.contDiff_baseState_eng.continuous).comp (continuous_fst.comp continuous_snd)))
      exact isOpen_lt hc continuous_const
  -- on `U` the two chord endpoints are at distance `> 1/5` from the axis
  have hzt' : ∀ (σ : ℝ) (z : St), 481 / 1000 < σ → σ < 102 / 100 →
      ‖z - baseState σ‖ < 9 / 20 → 1 / 5 ≤ |z 0| ∧ 1 / 5 ≤ |z 1| := by
    intro σ z hσ3 hσ4 hz
    have hσabs : |σ| ≤ 21 / 20 := by
      rw [abs_le]
      constructor <;> linarith
    have hprof : 17 / 25 ≤ Commons.Geometry.Ulam.profileX σ :=
      profileX_ge_17_25' hσabs
    have go : ∀ i : Fin 4, (i = 0 ∨ i = 1) → 1 / 5 ≤ |z i| := by
      intro i hi
      have hii : |z i - baseState σ i| ≤ ‖z - baseState σ‖ := by
        have := norm_le_pi_norm (z - baseState σ) i
        rwa [Pi.sub_apply, Real.norm_eq_abs] at this
      have hlt : |z i - baseState σ i| ≤ 9 / 20 := le_of_lt (lt_of_le_of_lt hii hz)
      have hlow : -(9 / 20 : ℝ) ≤ z i - baseState σ i := (abs_le.mp hlt).1
      have hb : baseState σ i = Commons.Geometry.Ulam.profileX σ := by
        rcases hi with rfl | rfl <;> simp [Work.OddVolterra.baseState]
      rw [hb] at hlow
      have hz5 : (1 / 5 : ℝ) ≤ z i := by linarith
      rwa [abs_of_nonneg (by linarith)]
    exact ⟨go 0 (Or.inl rfl), go 1 (Or.inr rfl)⟩
  -- the positivity hypotheses of the smoothness criterion
  have hposU : ∀ q ∈ U, 0 < krad h q.2.1 (-(q.2.2 0)) q.1 ∧
      0 < krad h q.2.1 (q.2.2 1) q.1 := by
    intro q hq
    rw [hUdef] at hq
    obtain ⟨h1, h2, h3, h4, h5⟩ := hq
    obtain ⟨hz0, hz1⟩ := hzt' q.2.1 q.2.2 h3 h4 h5
    constructor
    · refine krad_pos_of_add_pos' hsupp hsmall ?_ ?_
      · linarith
      · rwa [abs_neg]
    · refine krad_pos_of_add_pos' hsupp hsmall ?_ hz1
      · linarith
  have hposτ : ∀ q ∈ U, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      0 < krad h q.2.1 (-(q.2.2 0)) (q.1 + τ * (q.2.1 - q.1)) ∧
      0 < krad h q.2.1 (q.2.2 1) (q.1 + τ * (q.2.1 - q.1)) := by
    intro q hq τ hτ
    rw [hUdef] at hq
    obtain ⟨h1, h2, h3, h4, h5⟩ := hq
    obtain ⟨hτ0, hτ1⟩ := hτ
    obtain ⟨hz0, hz1⟩ := hzt' q.2.1 q.2.2 h3 h4 h5
    have ha : 1 / 8 < q.1 + τ * (q.2.1 - q.1) := by
      rcases le_total q.1 q.2.1 with hle | hle
      · have hnn : 0 ≤ τ * (q.2.1 - q.1) := mul_nonneg hτ0 (by linarith)
        linarith
      · have hge : τ * (q.2.1 - q.1) ≥ q.2.1 - q.1 := by
          have := mul_le_mul_of_nonpos_right hτ1 (by linarith : q.2.1 - q.1 ≤ 0)
          linarith
        linarith
    constructor
    · refine krad_pos_of_add_pos' hsupp hsmall ?_ ?_
      · linarith
      · rwa [abs_neg]
    · refine krad_pos_of_add_pos' hsupp hsmall ?_ hz1
      · linarith
  have hsm := Work.OddExistence.Manifest.contDiffOn_KernelExtThetaM_of_pos n hh hUopen
    hposU hposτ
  -- the tail integrand on the product of the source window and the `σ`-window
  have hbase : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => (p.1, p.2, baseState p.2)) := by
    refine contDiff_fst.prodMk (contDiff_snd.prodMk ?_)
    exact Work.Anchor.contDiff_baseState_eng.comp contDiff_snd
  have hmap : MapsTo (fun p : ℝ × ℝ => (p.1, p.2, baseState p.2))
      (Set.Ioo (1 / 8 : ℝ) (99 / 100) ×ˢ Work.Anchor.Jx) U := by
    rintro ⟨s, σ⟩ ⟨hs, hσ⟩
    simp only [Set.mem_Ioo] at hs
    rw [Work.Anchor.Jx] at hσ
    simp only [Set.mem_Ioo] at hσ
    rw [hUdef]
    exact ⟨hs.1, hs.2, hσ.1, hσ.2, by rw [sub_self, norm_zero]; norm_num⟩
  have hF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => ThetaM n h p.1 p.2 (baseState p.2))
      (Set.Ioo (1 / 8 : ℝ) (99 / 100) ×ˢ Work.Anchor.Jx) := by
    simpa only [Function.comp_def] using hsm.comp hbase.contDiffOn hmap
  -- the parametric integral over the fixed interval `[19/20, 1]`
  exact Work.Anchor.contDiffOn_integral_fixed_of_contDiffOn (E := St)
    (F := fun s σ : ℝ => ThetaM n h s σ (baseState σ)) isOpen_Ioo
    Work.Anchor.isOpen_Jx hF (ContDiffBump.contDiff Work.Anchor.psiT)
    Work.Anchor.tsupport_psiT_subset Work.Anchor.psiT_one

theorem source_contDiffOn (n : ℕ) (hn : 1 ≤ n) :
    ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun s : ℝ => Work.OddVolterra.Xi n h s +
          ∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
            Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.baseState σ))
        (Set.Ioo (1 / 8 : ℝ) (99 / 100 : ℝ)) := by
  intro h hh hsupp hsmall
  exact (Xi_contDiffOn_window n hn hh hsupp hsmall).add
    (thetaM_tail_contDiffOn n hh hsupp hsmall)

end

end Work.OddVolterra.WinData
