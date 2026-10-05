import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPV.VBasic
import Submission.Work.RPV.V
import Submission.Work.RPB.B2.chordSurf_lagrangian
import Submission.Work.RPB.B4.periodic_reduce
import Submission.Work.RPB.B5.kappa_aux
import Submission.Work.RPB.B5.halfChordSmooth
import Submission.Work.RPB.B5.pos_min_of_compact

/-!
# B5: the sign of the chord-chart level function just below the blown-up diagonal

Write `χ τ t ρ = K₀ (W τ t ρ) + 1` for the `ρ = r²`-chart level function of the chord annulus.
On the chord annulus (`ρ = r²`, `0 < r ≤ π/2`) one has

`χ τ t ρ = ‖halfChord CI.c τ t r‖²`,

which is positive and, by `halfChord_lower_bound` (proved below from the smooth extension of the
half chord, `pos_min_of_compact` and the smooth-even-extension lemma
`IsCompact.exists_cthickening_subset_open`), uniformly bounded below by `c·ρ` for small `ρ > 0`.

Since `χ τ t ·` is `C¹` in `ρ` on the whole strip `(-ρ₀, ρ₀)`, its `ρ`-derivative is continuous
*on the closed `τ`-box* (`continuousOn_slice_deriv`), and the mean value theorem gives

`χ τ t ρ - χ τ t 0 = ρ · Φ τ t ρ`,  `Φ τ t ρ = ∫₀¹ ∂_ρχ (τ,t,ρs) ds`,

with `Φ` continuous (after clamping `τ` and `ρ` into the box, by
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`).  One has
`χ τ t 0 = 0` (the chord side tends to `0` as `r → 0`), and `Φ τ t ρ ≥ c` for small `ρ > 0` by the
uniform chord bound, so `Φ τ t 0 ≥ c > 0`; a second thickening argument then makes `Φ > 0` on a
whole slab `|ρ| < ε`.  Hence `χ τ t ρ < 0` for `ρ ∈ (-ε, 0)`, uniformly in `(τ, t)`.
-/

open Set Filter
open scoped Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

namespace Work.RPB.B5

/-! ## Small clamps -/

/-- The continuous clamp of `ℝ` onto `[0,1]`, the identity on `[0,1]`. -/
private def kcl01 (x : ℝ) : ℝ := max 0 (min 1 x)

/-- The continuous clamp of `ℝ` onto `[-r/2, r/2]`, the identity on `[-r/2, r/2]`. -/
private def kclR (r x : ℝ) : ℝ := max (-(r / 2)) (min (r / 2) x)

private lemma kcl01_cont : Continuous kcl01 := by
  unfold kcl01
  exact continuous_const.max (continuous_const.min continuous_id)

private lemma kclR_cont (r : ℝ) : Continuous (kclR r) := by
  unfold kclR
  exact continuous_const.max (continuous_const.min continuous_id)

private lemma kcl01_eq {x : ℝ} (h : x ∈ Set.Icc (0 : ℝ) 1) : kcl01 x = x := by
  unfold kcl01
  rw [min_eq_right h.2, max_eq_right h.1]

private lemma kcl01_mem (x : ℝ) : kcl01 x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold kcl01
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private lemma kclR_eq {r x : ℝ} (h : |x| ≤ r / 2) : kclR r x = x := by
  unfold kclR
  rw [min_eq_right (by linarith [(abs_le.mp h).2]), max_eq_right (by linarith [(abs_le.mp h).1])]

private lemma kclR_mem {r x : ℝ} (hr : 0 < r) : kclR r x ∈ Set.Ioo (-r) r := by
  have h1 : -(r / 2) ≤ kclR r x := by
    unfold kclR; exact le_max_left _ _
  have h2 : kclR r x ≤ r / 2 := by
    unfold kclR; exact max_le (by linarith) (min_le_left _ _)
  exact ⟨by linarith, by linarith⟩

/-! ## The level function and its `ρ`-derivative -/

/-- The level function `χ τ t ρ = K₀ (W τ t ρ) + 1` of the `ρ = r²`-chart. -/
private def kPsi (W : ℝ → ℝ → ℝ → Work.RPV.PS) (z : ℝ × (ℝ × ℝ)) : ℝ :=
  Work.RPV.K0 (W z.1 z.2.1 z.2.2) + 1

/-- The `ρ`-derivative of `kPsi`, as a function of the point. -/
private def kG (W : ℝ → ℝ → ℝ → Work.RPV.PS) (z : ℝ × (ℝ × ℝ)) : ℝ :=
  deriv (fun r : ℝ => kPsi W (z.1, (z.2.1, r))) z.2.2

/-- The clamped average of the `ρ`-derivative, a function that is continuous on all of
`ℝ × (ℝ × ℝ)` and agrees with `ρ ↦ (χ τ t ρ - χ τ t 0)/ρ` for `|ρ| < ρ₀/2`, `τ ∈ [0,1]`. -/
private def kPhi (W : ℝ → ℝ → ℝ → Work.RPV.PS) (r₀ : ℝ) (z : ℝ × (ℝ × ℝ)) : ℝ :=
  ∫ s in (0 : ℝ)..1, kG W (kcl01 z.1, (z.2.1, kclR r₀ (z.2.2 * s)))

/-- The compact fundamental domain of the base `ρ = 0` over `τ ∈ [0,1]`, `t ∈ [0,2π]`. -/
private def kS1 : Set (ℝ × (ℝ × ℝ)) :=
  Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ ({0} : Set ℝ))

private lemma kS1_compact : IsCompact kS1 := by
  unfold kS1
  exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_singleton)

/-! ## Uniform lower bound for the half chord -/

/-- **Uniform lower bound for the half chord.**  For a curve isotopy there are `m > 0` and
`δ > 0` with `m ≤ ‖halfChord CI.c τ t r‖` for all `τ ∈ [0,1]`, all `t` and all `0 < r < δ`. -/
theorem halfChord_lower_bound (CI : Work.RPV.CurveIsotopy) :
    ∃ m : ℝ, 0 < m ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) δ,
        m ≤ ‖Work.RPB.halfChord CI.c τ t r‖ := by
  have hcs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => CI.c z.1 z.2) := CI.smooth
  have hcsm : ContDiff ℝ ∞
      (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B5.halfChordExt CI.c z.1 z.2.1 z.2.2) :=
    Work.RPB.B5.contDiff_halfChordExt CI.c hcs
  have hcontF : Continuous
      (fun p : ℝ × (ℝ × ℝ) => ‖Work.RPB.B5.halfChordExt CI.c p.1 p.2.1 p.2.2‖) :=
    hcsm.continuous.norm
  have hcper : ∀ τ t r, Work.RPB.B5.halfChordExt CI.c τ (t + 2 * Real.pi) r
      = Work.RPB.B5.halfChordExt CI.c τ t r :=
    fun τ t r => Work.RPB.B5.halfChordExt_periodic CI.c hcs CI.per τ t r
  have hczero : ∀ τ t, Work.RPB.B5.halfChordExt CI.c τ t 0 = deriv (CI.c τ) t :=
    fun τ t => Work.RPB.B5.halfChordExt_zero CI.c hcs τ t
  have hceq : ∀ τ t r, r ≠ 0 → Work.RPB.B5.halfChordExt CI.c τ t r
      = Work.RPB.halfChord CI.c τ t r :=
    fun τ t r hr => Work.RPB.B5.halfChordExt_eq CI.c hcs τ t r hr
  set S : Set (ℝ × (ℝ × ℝ)) :=
    Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ ({0} : Set ℝ)) with hS
  have hScomp : IsCompact S := by
    rw [hS]
    exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_singleton)
  have hSne : S.Nonempty := by
    rw [hS]
    exact ⟨(0, (0, 0)), ⟨⟨le_rfl, zero_le_one⟩, ⟨⟨le_rfl, Real.two_pi_pos.le⟩, rfl⟩⟩⟩
  have hposS : ∀ p ∈ S, 0 < ‖Work.RPB.B5.halfChordExt CI.c p.1 p.2.1 0‖ := by
    intro p hp
    rw [hS] at hp
    obtain ⟨hτ, -, -⟩ := hp
    rw [hczero p.1 p.2.1]
    exact norm_pos_iff.mpr (CI.imm p.1 hτ p.2.1)
  obtain ⟨m₀, hm₀pos, hm₀⟩ :=
    Work.RPB.B5.pos_min_of_compact hScomp hSne
      (fun p : ℝ × (ℝ × ℝ) => ‖Work.RPB.B5.halfChordExt CI.c p.1 p.2.1 0‖)
      ((hcontF.comp (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
        continuous_const))).continuousOn) hposS
  have hST : S ⊆ {p : ℝ × (ℝ × ℝ) | m₀ / 2 < ‖Work.RPB.B5.halfChordExt CI.c p.1 p.2.1 p.2.2‖} := by
    intro p hp
    rw [hS] at hp
    obtain ⟨hτ, ht, hr⟩ := hp
    rw [Set.mem_singleton_iff] at hr
    have h1 : m₀ ≤ ‖Work.RPB.B5.halfChordExt CI.c p.1 p.2.1 0‖ :=
      hm₀ p (by rw [hS]; exact ⟨hτ, ht, hr⟩)
    change m₀ / 2 < ‖Work.RPB.B5.halfChordExt CI.c p.1 p.2.1 p.2.2‖
    rw [hr]
    linarith
  obtain ⟨δ, hδpos, hδsub⟩ :=
    hScomp.exists_cthickening_subset_open (isOpen_lt continuous_const hcontF) hST
  refine ⟨m₀ / 2, by linarith, δ, hδpos, ?_⟩
  intro τ hτ t r hr
  obtain ⟨hrlo, hrhi⟩ := hr
  obtain ⟨k, t', ht'Ico, -, hft⟩ :=
    Work.RPB.B4.periodic_reduce (fun s => Work.RPB.B5.halfChordExt CI.c τ s r)
      (fun s => hcper τ s r) t
  have ht'Icc : t' ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨ht'Ico.1, ht'Ico.2.le⟩
  have hmemS : (τ, (t', 0)) ∈ S := by
    rw [hS]
    exact ⟨hτ, ht'Icc, rfl⟩
  have hdist : dist ((τ, (t', r)) : ℝ × (ℝ × ℝ)) (τ, (t', 0)) ≤ δ := by
    have h1 : dist ((τ, (t', r)) : ℝ × (ℝ × ℝ)) (τ, (t', 0)) = |r| := by
      simp [Prod.dist_eq, Real.dist_eq]
    rw [h1, abs_of_pos hrlo]
    exact hrhi.le
  have hmemT : (τ, (t', r)) ∈ Metric.cthickening δ S :=
    Metric.mem_cthickening_of_dist_le (τ, (t', r)) (τ, (t', 0)) δ S hmemS hdist
  have hbound : m₀ / 2 < ‖Work.RPB.B5.halfChordExt CI.c τ t' r‖ := hδsub hmemT
  rw [← hceq τ t r (ne_of_gt hrlo)]
  rw [hft]
  exact le_of_lt hbound

/-- **Sign of the chart level function below the diagonal.**  For the `ρ = r²`-chart `W` of the
chord annulus of `(CI, a)` there is `ε > 0` with `K₀ (W τ t ρ) + 1 < 0` for every `τ ∈ [0,1]`,
every `t` and every `ρ ∈ (-ε, 0)`. -/
theorem kappa_W_sign (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ ρ ∈ Set.Ioo (-ε) 0,
        Work.RPV.K0 (W τ t ρ) + 1 < 0 := by
  obtain ⟨mh, hmhpos, δh, hδhpos, hbound⟩ := halfChord_lower_bound CI
  have hcs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => CI.c z.1 z.2) := CI.smooth
  -- the level function is `C¹²` on the strip
  have hΨ : ContDiffOn ℝ 12 (kPsi W)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) := by
    have hK0 : ContDiff ℝ 12 (fun p : Work.RPV.PS => Work.RPV.K0 p + 1) := by
      simp only [Work.RPV.K0]
      fun_prop
    have h := hK0.contDiffOn.comp hW (fun z _ => Set.mem_univ _)
    exact h
  -- its `ρ`-derivative is continuous on the strip (uniformly on the closed `τ`-box)
  have hGcont : ContinuousOn (kG W)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) := by
    have h := Work.RPB.B5.continuousOn_slice_deriv (a := (0 : ℝ)) (b := 1) (c := -ρ₀) (d := ρ₀)
      (by norm_num) (n := 12) (by norm_num) hΨ
    exact h
  -- differentiability of the `ρ`-slices
  have hslice_cd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (-ρ₀) ρ₀,
      DifferentiableAt ℝ (fun r' : ℝ => kPsi W (τ, (t, r'))) r := by
    intro τ hτ t r hr
    have hmaps : Set.MapsTo (fun r' : ℝ => (τ, (t, r'))) (Set.Ioo (-ρ₀) ρ₀)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) :=
      fun r' hr' => ⟨hτ, Set.mem_univ _, hr'⟩
    have hcd : ContDiffOn ℝ 12 (fun r' : ℝ => kPsi W (τ, (t, r'))) (Set.Ioo (-ρ₀) ρ₀) := by
      have hcomp := hΨ.comp
        ((by fun_prop : ContDiff ℝ 12 (fun r' : ℝ => (τ, (t, r')))).contDiffOn) hmaps
      simpa [Function.comp_def] using hcomp
    have hd : DifferentiableOn ℝ (fun r' : ℝ => kPsi W (τ, (t, r'))) (Set.Ioo (-ρ₀) ρ₀) :=
      hcd.differentiableOn (by norm_num)
    exact (hd r hr).differentiableAt (isOpen_Ioo.mem_nhds hr)
  -- the chord-side formula for the level function
  have hlen : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ ρ ∈ Set.Ioo (0 : ℝ) (Real.pi ^ 2 / 4),
      kPsi W (τ, (t, ρ)) = ρ * ‖Work.RPB.B5.halfChordExt CI.c τ t (Real.sqrt ρ)‖ ^ 2 := by
    intro τ hτ t ρ hρ
    have hρpos : 0 < ρ := hρ.1
    have hsppos : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρpos
    have hsq : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρpos.le
    have hsplt : Real.sqrt ρ < Real.pi / 2 := by
      rw [Real.sqrt_lt' (by positivity : (0 : ℝ) < Real.pi / 2)]
      rw [show (Real.pi / 2) ^ 2 = Real.pi ^ 2 / 4 by ring]
      exact hρ.2
    have h1 : kPsi W (τ, (t, ρ)) =
        ‖CI.c τ (t + Real.sqrt ρ) - CI.c τ (t - Real.sqrt ρ)‖ ^ 2 / 4 := by
      rw [show kPsi W (τ, (t, ρ)) = Work.RPV.K0 (W τ t (Real.sqrt ρ ^ 2)) + 1 from by
        rw [hsq]; rfl]
      rw [hWchord τ hτ t (Real.sqrt ρ) ⟨hsppos, hsplt.le⟩, Work.RPB.chordSurf,
        Work.RPV.K0_chordPS]
      ring
    rw [h1]
    have hext : Work.RPB.B5.halfChordExt CI.c τ t (Real.sqrt ρ)
        = (CI.c τ (t + Real.sqrt ρ) - CI.c τ (t - Real.sqrt ρ))
            / (2 * (Real.sqrt ρ : ℂ)) := by
      rw [Work.RPB.B5.halfChordExt_eq CI.c hcs τ t (Real.sqrt ρ) (ne_of_gt hsppos)]
      rfl
    rw [hext]
    have hden : ‖((2 : ℂ) * (Real.sqrt ρ : ℂ))‖ = 2 * Real.sqrt ρ := by
      simp [abs_of_pos hsppos]
    rw [norm_div, hden, div_pow]
    have h22 : (2 * Real.sqrt ρ) ^ 2 = 4 * ρ := by
      rw [mul_pow, hsq]; norm_num
    rw [h22]
    field_simp
  -- the value at `ρ = 0`
  have hΨ0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, kPsi W (τ, (t, 0)) = 0 := by
    intro τ hτ t
    have hct : ContinuousAt (fun ρ : ℝ => kPsi W (τ, (t, ρ))) 0 :=
      ((hslice_cd τ hτ t 0 ⟨by linarith, hρ₀⟩).continuousAt)
    have hlim1 : Tendsto (fun ρ : ℝ => kPsi W (τ, (t, ρ))) (𝓝[>] (0 : ℝ))
        (𝓝 (kPsi W (τ, (t, 0)))) := hct.tendsto.mono_left nhdsWithin_le_nhds
    have hc1 : Continuous (fun r : ℝ => Work.RPB.B5.halfChordExt CI.c τ t r) :=
      (Work.RPB.B5.contDiff_halfChordExt CI.c hcs).continuous.comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    have hFcont : ContinuousAt
        (fun r : ℝ => ‖Work.RPB.B5.halfChordExt CI.c τ t r‖ ^ 2) 0 :=
      (hc1.continuousAt.norm).pow 2
    have hlimF : Tendsto (fun r : ℝ => ‖Work.RPB.B5.halfChordExt CI.c τ t r‖ ^ 2)
        (𝓝 (0 : ℝ)) (𝓝 (‖Work.RPB.B5.halfChordExt CI.c τ t 0‖ ^ 2)) :=
      hFcont.tendsto
    have hsqrt : Tendsto (fun ρ : ℝ => Real.sqrt ρ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := Real.continuous_sqrt.continuousAt (x := 0)
      have h2 : Tendsto (fun ρ : ℝ => Real.sqrt ρ) (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
        h.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
      simpa using h2
    have hid : Tendsto (fun ρ : ℝ => ρ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
    have hprod := hid.mul (hlimF.comp hsqrt)
    have hlim0 : Tendsto (fun ρ : ℝ => kPsi W (τ, (t, ρ))) (𝓝[>] (0 : ℝ))
        (𝓝 (0 * ‖Work.RPB.B5.halfChordExt CI.c τ t 0‖ ^ 2)) := by
      refine Tendsto.congr' ?_ hprod
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi ^ 2 / 4 by positivity)] with ρ hρ
      exact (hlen τ hτ t ρ hρ).symm
    rw [zero_mul] at hlim0
    exact tendsto_nhds_unique hlim1 hlim0
  -- the clamped average is continuous
  have hΦcont : Continuous (kPhi W ρ₀) := by
    have hp11 : Continuous (fun p : (ℝ × (ℝ × ℝ)) × ℝ => p.1.1) :=
      continuous_fst.comp continuous_fst
    have hp121 : Continuous (fun p : (ℝ × (ℝ × ℝ)) × ℝ => p.1.2.1) :=
      continuous_fst.comp (continuous_snd.comp continuous_fst)
    have hp122 : Continuous (fun p : (ℝ × (ℝ × ℝ)) × ℝ => p.1.2.2) :=
      continuous_snd.comp (continuous_snd.comp continuous_fst)
    have hp2 : Continuous (fun p : (ℝ × (ℝ × ℝ)) × ℝ => p.2) := continuous_snd
    have hφ : Continuous (fun p : (ℝ × (ℝ × ℝ)) × ℝ =>
        (kcl01 p.1.1, (p.1.2.1, kclR ρ₀ (p.1.2.2 * p.2)))) :=
      (kcl01_cont.comp hp11).prodMk
        (hp121.prodMk ((kclR_cont ρ₀).comp (hp122.mul hp2)))
    have hmem : ∀ p : (ℝ × (ℝ × ℝ)) × ℝ,
        (kcl01 p.1.1, (p.1.2.1, kclR ρ₀ (p.1.2.2 * p.2))) ∈
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) :=
      fun p => ⟨kcl01_mem _, Set.mem_univ _, kclR_mem hρ₀⟩
    have hGcomp : Continuous ((kG W) ∘ (fun p : (ℝ × (ℝ × ℝ)) × ℝ =>
        (kcl01 p.1.1, (p.1.2.1, kclR ρ₀ (p.1.2.2 * p.2))))) :=
      hGcont.comp_continuous hφ hmem
    have huncurry : Continuous (Function.uncurry (fun z : ℝ × (ℝ × ℝ) => fun s : ℝ =>
        kG W (kcl01 z.1, (z.2.1, kclR ρ₀ (z.2.2 * s))))) := by
      exact hGcomp
    have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume) huncurry (0 : ℝ) (1 : ℝ)
    exact h
  -- the mean value identity
  have hPhi_id : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t ρ : ℝ, |ρ| < ρ₀ / 2 →
      kPsi W (τ, (t, ρ)) - kPsi W (τ, (t, 0)) = ρ * kPhi W ρ₀ (τ, (t, ρ)) := by
    intro τ hτ t ρ hρ
    have hρlt : |ρ| < ρ₀ := by linarith [abs_nonneg ρ]
    have hmaps : Set.MapsTo (fun r : ℝ => (τ, (t, r))) (Set.uIcc 0 ρ)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) := by
      intro r hr
      have hrle : |r| ≤ |ρ| := by
        rw [Set.mem_uIcc] at hr
        rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          exact h2
        · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          linarith
      exact ⟨hτ, Set.mem_univ _,
        abs_lt.mp (lt_of_le_of_lt hrle hρlt)⟩
    rcases eq_or_ne ρ 0 with h0 | h0
    · subst h0
      rw [sub_self, zero_mul]
    · have hGslice : ContinuousOn (fun r : ℝ => kG W (τ, (t, r))) (Set.uIcc 0 ρ) :=
        hGcont.comp
          ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn) hmaps
      have hint : IntervalIntegrable (fun r : ℝ => kG W (τ, (t, r))) MeasureTheory.volume 0 ρ :=
        hGslice.intervalIntegrable
      have hdiff : ∀ r ∈ Set.uIcc (0 : ℝ) ρ,
          DifferentiableAt ℝ (fun r' : ℝ => kPsi W (τ, (t, r'))) r := by
        intro r hr
        have hrle : |r| ≤ |ρ| := by
          rw [Set.mem_uIcc] at hr
          rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
            exact h2
          · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
            linarith
        exact hslice_cd τ hτ t r (abs_lt.mp (lt_of_le_of_lt hrle hρlt))
      have hFTC : ∫ r in (0 : ℝ)..ρ, kG W (τ, (t, r))
          = kPsi W (τ, (t, ρ)) - kPsi W (τ, (t, 0)) := by
        have h := intervalIntegral.integral_deriv_eq_sub (a := (0 : ℝ)) (b := ρ)
          (f := fun r : ℝ => kPsi W (τ, (t, r))) hdiff hint
        exact h
      have hsub : ∫ s in (0 : ℝ)..1, kG W (τ, (t, ρ * s))
          = ρ⁻¹ * ∫ r in (0 : ℝ)..ρ, kG W (τ, (t, r)) := by
        have h := intervalIntegral.integral_comp_mul_right
          (f := fun r : ℝ => kG W (τ, (t, r))) (a := (0 : ℝ)) (b := (1 : ℝ)) (c := ρ) h0
        simpa [smul_eq_mul, mul_comm] using h
      have hΦeq : kPhi W ρ₀ (τ, (t, ρ)) = ∫ s in (0 : ℝ)..1, kG W (τ, (t, ρ * s)) := by
        change (∫ s in (0 : ℝ)..1, kG W (kcl01 τ, (t, kclR ρ₀ (ρ * s))))
          = ∫ s in (0 : ℝ)..1, kG W (τ, (t, ρ * s))
        apply intervalIntegral.integral_congr
        intro s hs
        show kG W (kcl01 τ, (t, kclR ρ₀ (ρ * s))) = kG W (τ, (t, ρ * s))
        have hs1 : |s| ≤ 1 := by
          rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
          rw [abs_le]; exact ⟨by linarith [hs.1], hs.2⟩
        have hxs : |ρ * s| ≤ ρ₀ / 2 := by
          rw [abs_mul]
          calc |ρ| * |s| ≤ |ρ| * 1 := mul_le_mul_of_nonneg_left hs1 (abs_nonneg ρ)
            _ = |ρ| := mul_one _
            _ ≤ ρ₀ / 2 := hρ.le
        rw [kcl01_eq hτ, kclR_eq hxs]
      rw [hΦeq, hsub, hFTC, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
  -- a positive lower bound for the clamped average on the base
  have hbase : ∀ p ∈ kS1, 0 < kPhi W ρ₀ p := by
    intro p hp
    unfold kS1 at hp
    obtain ⟨τ, t, ρ⟩ := p
    obtain ⟨hτ, ht, hr⟩ := hp
    rw [Set.mem_singleton_iff] at hr
    rw [show ρ = 0 from hr]
    have hε₀ : 0 < min (ρ₀ / 2) (min (Real.pi ^ 2 / 4) (δh ^ 2)) :=
      lt_min (by linarith) (lt_min (by positivity) (by positivity))
    have hlim : Tendsto (fun ρ : ℝ => kPhi W ρ₀ (τ, (t, ρ))) (𝓝[>] (0 : ℝ))
        (𝓝 (kPhi W ρ₀ (τ, (t, 0)))) := by
      have hcont : ContinuousAt (fun ρ : ℝ => kPhi W ρ₀ (τ, (t, ρ))) 0 :=
        (hΦcont.continuousAt.comp
          ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt))
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), mh ^ 2 ≤ kPhi W ρ₀ (τ, (t, ρ)) := by
      filter_upwards [Ioo_mem_nhdsGT hε₀] with ρ hρ
      have hρ1 : ρ < ρ₀ / 2 := lt_of_lt_of_le hρ.2 (min_le_left _ _)
      have hρ2 : ρ < Real.pi ^ 2 / 4 :=
        lt_of_lt_of_le hρ.2 (le_trans (min_le_right _ _) (min_le_left _ _))
      have hρ3 : ρ < δh ^ 2 :=
        lt_of_lt_of_le hρ.2 (le_trans (min_le_right _ _) (min_le_right _ _))
      have hid := hPhi_id τ hτ t ρ (by rw [abs_of_pos hρ.1]; linarith)
      rw [hΨ0 τ hτ t, sub_zero] at hid
      rw [hlen τ hτ t ρ ⟨hρ.1, hρ2⟩] at hid
      have hΦeq : kPhi W ρ₀ (τ, (t, ρ))
          = ‖Work.RPB.B5.halfChordExt CI.c τ t (Real.sqrt ρ)‖ ^ 2 :=
        (mul_left_cancel₀ (ne_of_gt hρ.1) hid).symm
      rw [hΦeq]
      have hrlt : Real.sqrt ρ < δh := by
        rw [Real.sqrt_lt' hδhpos]
        exact hρ3
      have hrpos : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ.1
      have hb := hbound τ hτ t (Real.sqrt ρ) ⟨hrpos, hrlt⟩
      have heq : Work.RPB.B5.halfChordExt CI.c τ t (Real.sqrt ρ)
          = Work.RPB.halfChord CI.c τ t (Real.sqrt ρ) :=
        Work.RPB.B5.halfChordExt_eq CI.c hcs τ t _ (ne_of_gt hrpos)
      rw [heq]
      nlinarith [hb, hmhpos, norm_nonneg (Work.RPB.halfChord CI.c τ t (Real.sqrt ρ))]
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < mh ^ 2) (ge_of_tendsto hlim hev)
  -- hence on a whole slab around the base
  obtain ⟨ε₁, hε₁pos, hε₁sub⟩ :=
    kS1_compact.exists_cthickening_subset_open (isOpen_lt continuous_const hΦcont) hbase
  have hΨper : ∀ τ s ρ, kPsi W (τ, (s + 2 * Real.pi, ρ)) = kPsi W (τ, (s, ρ)) := by
    intro τ s ρ
    rw [show kPsi W (τ, (s + 2 * Real.pi, ρ))
          = Work.RPV.K0 (W τ (s + 2 * Real.pi) ρ) + 1 from rfl,
      show kPsi W (τ, (s, ρ)) = Work.RPV.K0 (W τ s ρ) + 1 from rfl, hWper τ s ρ,
      Work.RPV.K0_Tk]
  refine ⟨min ε₁ (ρ₀ / 2), lt_min hε₁pos (by linarith), ?_⟩
  intro τ hτ t ρ hρ
  obtain ⟨hρgt, hρlt0⟩ := hρ
  have hεpos : 0 < min ε₁ (ρ₀ / 2) := lt_min hε₁pos (by linarith)
  have hρabs : |ρ| < min ε₁ (ρ₀ / 2) := abs_lt.mpr ⟨hρgt, by linarith [hεpos, hρlt0]⟩
  have hρabs1 : |ρ| < ε₁ := lt_of_lt_of_le hρabs (min_le_left _ _)
  have hρabs2 : |ρ| < ρ₀ / 2 := lt_of_lt_of_le hρabs (min_le_right _ _)
  obtain ⟨k, t', ht'Ico, -, hper⟩ :=
    Work.RPB.B4.periodic_reduce (fun s : ℝ => kPsi W (τ, (s, ρ))) (fun s => hΨper τ s ρ) t
  have ht'Icc : t' ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨ht'Ico.1, ht'Ico.2.le⟩
  have hmemS₁ : (τ, (t', 0)) ∈ kS1 := by
    unfold kS1
    exact ⟨hτ, ht'Icc, rfl⟩
  have hΦpos : 0 < kPhi W ρ₀ (τ, (t', ρ)) := by
    apply hε₁sub
    apply Metric.mem_cthickening_of_dist_le _ _ ε₁ kS1 hmemS₁
    have h1 : dist ((τ, (t', ρ)) : ℝ × (ℝ × ℝ)) (τ, (t', 0)) = |ρ| := by
      simp [Prod.dist_eq, Real.dist_eq]
    rw [h1]
    exact hρabs1.le
  have hid := hPhi_id τ hτ t' ρ hρabs2
  rw [hΨ0 τ hτ t', sub_zero] at hid
  have hneg : kPsi W (τ, (t', ρ)) < 0 := by
    rw [hid]
    exact mul_neg_of_neg_of_pos hρlt0 hΦpos
  change kPsi W (τ, (t, ρ)) < 0
  rw [hper]
  exact hneg

end Work.RPB.B5
