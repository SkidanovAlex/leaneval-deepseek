import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.kappa_shape_basic
import Submission.Work.RPB.B5.kappaSmallAux
import Submission.Work.RPB.B5.kappa_kshape_contDiff_joint
import Submission.Work.RPB.B5.C8.kcj_tau_contDiffOn
import Submission.Work.RPB.B5.kappa_collar_area_all
import Submission.Work.RPB.B5.contDiff_signedArea_gen
import Submission.Work.RPB.B5.contDiff_sliceDeriv_gen
import Submission.Work.RPB.B4.paramIntegral_variable
import Submission.Work.RPB.B5.tauSlabExtend
import Submission.Work.RPB.B5.kA0_spec

namespace Work.RPB.B5

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology Interval

set_option autoImplicit false

noncomputable section

/-! ## The smoothing clamps

`c8tau` is a smooth map which is the identity on `[0,1]` and whose range lies in the open interval
`(-1,2)`; `c8tclamp M` is a smooth map which is the identity on `[0,M/2]` and whose range lies in
`(-M,M)`.  Both are built from the one-sided clamps `kcneg`/`kcpos` of `kappaDefs`. -/

/-- A smooth retraction of `ℝ` onto `(-1,2)` which is the identity on `[0,1]`. -/
def c8tau (τ : ℝ) : ℝ := kcpos 2 (kcneg (1 / 2) τ)

/-- A smooth clamp of `ℝ` into `(-M,M)` which is the identity on `[0,M/2]`. -/
def c8tclamp (M t : ℝ) : ℝ := kcpos M (kcneg (M / 2) t)

theorem c8tau_contDiff : ContDiff ℝ ∞ c8tau := by
  unfold c8tau kcpos kcneg kstp
  fun_prop

theorem c8tclamp_contDiff (M : ℝ) : ContDiff ℝ ∞ (c8tclamp M) := by
  unfold c8tclamp kcpos kcneg kstp
  fun_prop

theorem c8tau_of_mem {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) : c8tau τ = τ := by
  have h1 : kcneg (1 / 2) τ = τ := kcneg_eq_self (by norm_num) (by linarith [hτ.1])
  have h2 : kcpos 2 τ = τ := kcpos_eq_self (by norm_num) (by linarith [hτ.2])
  unfold c8tau
  rw [h1, h2]

theorem c8tau_mem (τ : ℝ) : c8tau τ ∈ Set.Ioo (-1 : ℝ) 2 := by
  have hσ1 : (-(1 / 2) : ℝ) ≤ kcneg (1 / 2) τ := by
    rcases lt_or_ge τ (-(1 / 2 / 2)) with h | h
    · have hmem := kcneg_mem_Icc (δ := 1 / 2) (σ := τ) (by norm_num) (le_of_lt h)
      linarith [hmem.1]
    · rw [kcneg_eq_self (by norm_num) h]
      linarith
  refine ⟨?_, ?_⟩
  · have hmin : min (kcneg (1 / 2) τ) (2 / 2) ≤ kcpos 2 (kcneg (1 / 2) τ) :=
      kcpos_ge_min (by norm_num)
    have h2 : (-1 : ℝ) < min (kcneg (1 / 2) τ) (2 / 2) := lt_min (by linarith) (by norm_num)
    change (-1 : ℝ) < c8tau τ
    unfold c8tau
    linarith
  · change c8tau τ < 2
    unfold c8tau
    rcases lt_or_ge (kcneg (1 / 2) τ) 2 with h | h
    · rcases lt_or_ge (kcneg (1 / 2) τ) 1 with h1 | h1
      · rw [kcpos_eq_self (by norm_num) (by linarith [h1])]
        linarith
      · have hmax : kcpos 2 (kcneg (1 / 2) τ) ≤ max (kcneg (1 / 2) τ) (2 / 2) :=
          kcpos_le_max (by norm_num)
        have hmax2 : max (kcneg (1 / 2) τ) (2 / 2) = kcneg (1 / 2) τ := max_eq_left (by linarith [h1])
        linarith [hmax, hmax2]
    · rw [kcpos_eq_half (by norm_num) (by linarith [h])]
      norm_num

theorem c8tclamp_of_mem {M t : ℝ} (hM : 0 < M) (ht : t ∈ Set.Icc (0 : ℝ) (M / 2)) :
    c8tclamp M t = t := by
  have h1 : kcneg (M / 2) t = t :=
    kcneg_eq_self (by linarith) (by linarith [ht.1])
  have h2 : kcpos M t = t := kcpos_eq_self hM (by linarith [ht.2])
  change kcpos M (kcneg (M / 2) t) = t
  rw [h1, h2]

theorem c8tclamp_mem {M t : ℝ} (hM : 0 < M) : c8tclamp M t ∈ Set.Ioo (-M) M := by
  have hσ : (-(M / 2) : ℝ) ≤ kcneg (M / 2) t := by
    rcases lt_or_ge t (-(M / 2 / 2)) with h | h
    · have hmem := kcneg_mem_Icc (δ := M / 2) (σ := t) (by linarith) (le_of_lt h)
      linarith [hmem.1]
    · rw [kcneg_eq_self (by linarith) h]
      linarith
  refine ⟨?_, ?_⟩
  · have hmin : min (kcneg (M / 2) t) (M / 2) ≤ kcpos M (kcneg (M / 2) t) := kcpos_ge_min hM
    have h2 : (-M : ℝ) < min (kcneg (M / 2) t) (M / 2) := lt_min (by linarith) (by linarith)
    change (-M : ℝ) < c8tclamp M t
    unfold c8tclamp
    linarith
  · change c8tclamp M t < M
    unfold c8tclamp
    rcases lt_or_ge (kcneg (M / 2) t) M with h | h
    · rcases lt_or_ge (kcneg (M / 2) t) (M / 2) with h2 | h2
      · rw [kcpos_eq_self hM (by linarith [h2])]
        linarith
      · have hmax : kcpos M (kcneg (M / 2) t) ≤ max (kcneg (M / 2) t) (M / 2) := kcpos_le_max hM
        have hmax2 : max (kcneg (M / 2) t) (M / 2) = kcneg (M / 2) t := max_eq_left (by linarith [h2])
        linarith [hmax, hmax2]
    · rw [kcpos_eq_half hM (by linarith [h])]
      linarith

/-! ## Globalising the collar

For a fixed admissible scale `δ` we extend the glued shape `kshape` in the `τ`-variable (which the
hypotheses only control on `[0,1]`) with `tauSlabExtend`, clamp `τ` and `t` with the smooth maps
`c8tau`, `c8tclamp M`, and read off a globally smooth family `V` agreeing with `kshape` on
`(-M/4, M/2)`.  Its signed area gives a global `C¹¹` function whose restriction to `[0,1] × ℝ` is
`karS`; dividing by it after a bump correction produces a global smooth `kg`, hence a global
smooth model of `kgam` agreeing with `kgam` on `[0,1] × ℝ × [0,M/2]`. -/

/-- A smooth bump in `τ` which equals `1` exactly on `[0,1]`. -/
def c8chi (τ : ℝ) : ℝ := kstp (1 + τ) * kstp (2 - τ)

theorem c8chi_contDiff : ContDiff ℝ ∞ c8chi := by
  unfold c8chi kstp; fun_prop

theorem c8chi_eq_one {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) : c8chi τ = 1 := by
  obtain ⟨h0, h1⟩ := hτ
  unfold c8chi
  rw [kstp_one (by linarith), kstp_one (by linarith), mul_one]

theorem c8chi_mem (τ : ℝ) : c8chi τ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨mul_nonneg (kstp_nonneg _) (kstp_nonneg _),
    mul_le_mul (kstp_le_one (1 + τ)) (kstp_le_one (2 - τ)) (kstp_nonneg (2 - τ)) zero_le_one |>.trans_eq
      (mul_one 1)⟩

theorem c8chi_eq_one_iff {τ : ℝ} : c8chi τ = 1 ↔ τ ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨fun h => ?_, c8chi_eq_one⟩
  unfold c8chi at h
  have hb : kstp (2 - τ) = 1 := by
    have hle : kstp (2 - τ) ≤ 1 := kstp_le_one _
    have hge : (1 : ℝ) ≤ kstp (2 - τ) := by
      have hab : kstp (1 + τ) * kstp (2 - τ) ≤ kstp (2 - τ) :=
        (mul_le_mul_of_nonneg_right (kstp_le_one (1 + τ)) (kstp_nonneg (2 - τ))).trans_eq
          (one_mul _)
      linarith [h]
    exact le_antisymm hle hge
  have ha : kstp (1 + τ) = 1 := by
    have hle : kstp (1 + τ) ≤ 1 := kstp_le_one _
    have hge : (1 : ℝ) ≤ kstp (1 + τ) := by
      have hab : kstp (1 + τ) * kstp (2 - τ) ≤ kstp (1 + τ) :=
        (mul_le_mul_of_nonneg_left (kstp_le_one (2 - τ)) (kstp_nonneg (1 + τ))).trans_eq
          (mul_one _)
      linarith [h]
    exact le_antisymm hle hge
  have h1 : (1 : ℝ) ≤ 1 + τ := (Real.smoothTransition.eq_one_iff_one_le).1 ha
  have h2 : (1 : ℝ) ≤ 2 - τ := (Real.smoothTransition.eq_one_iff_one_le).1 hb
  exact ⟨by linarith, by linarith⟩

theorem c8tclamp_of_mem' {M t : ℝ} (hM : 0 < M) (ht : t ∈ Set.Ioo (-(M / 4)) (M / 2)) :
    c8tclamp M t = t := by
  have h1 : kcneg (M / 2) t = t := kcneg_eq_self (by linarith) (by linarith [ht.1])
  have h2 : kcpos M t = t := kcpos_eq_self hM (by linarith [ht.2])
  change kcpos M (kcneg (M / 2) t) = t
  rw [h1, h2]

/-- **The glued shape, globalised in the `τ`-variable.**  It extends in `τ` with
`tauSlabExtend`, clamps `τ` into `(-1,2)` and `t` into `(-M,M)`, giving a globally `C¹²` family
agreeing with `kshape` on `[0,1] × ℝ × (-M/4, M/2)`. -/
theorem c8_shape_global (CI : Work.RPV.CurveIsotopy) {ρ₀ κ δ : ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hδ : 0 < δ) (hδκ : δ < κ) (hδ2 : δ ≤ 2) (k : ℤ) {M : ℝ} (hM : 0 < M) :
    ∃ V : ℝ → ℝ → ℝ → ℂ,
      ContDiff ℝ 12 (fun z : ℝ × (ℝ × ℝ) => V z.1 z.2.1 z.2.2) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, ∀ t ∈ Set.Ioo (-(M / 4)) (M / 2),
        V τ σ t = kshape CI W ρh δ k τ σ t) := by
  have hks12 : ContDiffOn ℝ 12
      (fun z : ℝ × (ℝ × ℝ) => kshape CI W ρh δ k z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-M) M) :=
    (kappa_kshape_contDiff_joint (CI := CI) (ρ₀ := ρ₀) (W := W) (ρh := ρh) hW hκ hρh hρhv
      hδ hδκ hδ2 k).mono (fun z hz => ⟨hz.1, trivial, trivial⟩)
  obtain ⟨F, hFcd, hFeq⟩ := tauSlabExtend (fun τ σ t => kshape CI W ρh δ k τ σ t) 12 hM hks12
  refine ⟨fun τ σ t => F (c8tau τ) σ (c8tclamp M t), ?_, ?_⟩
  · have h1 : ContDiff ℝ 12 (fun z : ℝ × (ℝ × ℝ) => c8tau z.1) :=
      (c8tau_contDiff.comp contDiff_fst).of_le (by simp)
    have h2 : ContDiff ℝ 12 (fun z : ℝ × (ℝ × ℝ) => z.2.1) := contDiff_snd.fst
    have h3 : ContDiff ℝ 12 (fun z : ℝ × (ℝ × ℝ) => c8tclamp M z.2.2) :=
      ((c8tclamp_contDiff M).comp contDiff_snd.snd).of_le (by simp)
    have hmap : ContDiff ℝ 12
        (fun z : ℝ × (ℝ × ℝ) => (c8tau z.1, z.2.1, c8tclamp M z.2.2)) :=
      h1.prodMk (h2.prodMk h3)
    have hmem : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (c8tau z.1, z.2.1, c8tclamp M z.2.2))
        Set.univ (Set.Ioo (-1 : ℝ) 2 ×ˢ Set.univ ×ˢ Set.Ioo (-M) M) :=
      fun z _ => ⟨c8tau_mem z.1, trivial, c8tclamp_mem hM⟩
    have h := hFcd.comp hmap.contDiffOn hmem
    rw [contDiffOn_univ] at h
    exact h
  · intro τ hτ σ t ht
    have h1 : c8tau τ = τ := c8tau_of_mem hτ
    have h2 : c8tclamp M t = t := c8tclamp_of_mem' hM ht
    have htM : t ∈ Set.Ioo (-M) M := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    show F (c8tau τ) σ (c8tclamp M t) = kshape CI W ρh δ k τ σ t
    rw [h1, h2]
    exact hFeq τ hτ σ t htM

/-- **`karS` is `C¹¹` on the `τ`-strip `[0,1] × ℝ`.** -/
theorem c8_karS_contDiffOn (CI : Work.RPV.CurveIsotopy) {ρ₀ κ δ : ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hδ : 0 < δ) (hδκ : δ < κ) (hδ2 : δ ≤ 2) (k : ℤ) :
    ContDiffOn ℝ 11 (fun z : ℝ × ℝ => karS CI W ρh δ k z.1 z.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  have hM : (0 : ℝ) < 4 * Real.pi + 1 := by linarith [Real.pi_pos]
  have hM4 : (0 : ℝ) < (4 * Real.pi + 1) / 4 := by linarith [Real.pi_pos]
  have hM2 : 2 * Real.pi < (4 * Real.pi + 1) / 2 := by linarith [Real.pi_pos]
  obtain ⟨V, hVcd, hVeq⟩ := c8_shape_global (CI := CI) (W := W) (ρh := ρh) hW hκ hρh hρhv
    hδ hδκ hδ2 k hM
  have hVcd' : ContDiff ℝ 12 (fun z : (ℝ × ℝ) × ℝ => V z.1.1 z.1.2 z.2) := by
    have hφ : ContDiff ℝ 12 (fun z : (ℝ × ℝ) × ℝ => ((z.1.1, (z.1.2, z.2)) : ℝ × (ℝ × ℝ))) :=
      (by fun_prop : ContDiff ℝ 12 fun z : (ℝ × ℝ) × ℝ => (z.1.1, (z.1.2, z.2)))
    have h := hVcd.comp hφ
    simpa only [Function.comp_def] using h
  have hkarSg : ContDiff ℝ 11 (fun p : ℝ × ℝ => Work.RPB.signedArea (fun t => V p.1 p.2 t)) :=
    contDiff_signedArea_gen (X := ℝ × ℝ) (fun p t => V p.1 p.2 t) 11 hVcd'
  refine hkarSg.contDiffOn.congr (fun p hp => ?_)
  obtain ⟨hp1, -⟩ := hp
  -- compare the signed areas on `[0,1] × ℝ`
  have hval : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), V p.1 p.2 t = kshape CI W ρh δ k p.1 p.2 t :=
    fun t ht => hVeq p.1 hp1 p.2 t ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hM2⟩
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      deriv (fun s => V p.1 p.2 s) t = deriv (fun s => kshape CI W ρh δ k p.1 p.2 s) t := by
    intro t ht
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Set.Ioo (-((4 * Real.pi + 1) / 4))
        ((4 * Real.pi + 1) / 2) from ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hM2⟩)] with s hs
    exact hVeq p.1 hp1 p.2 s hs
  have hInt : (∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (V p.1 p.2 t) (deriv (fun s => V p.1 p.2 s) t))
      = (∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (kshape CI W ρh δ k p.1 p.2 t)
          (deriv (fun s => kshape CI W ρh δ k p.1 p.2 s) t)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ht0 : (0 : ℝ) < t := by
      have h : min (0 : ℝ) (2 * Real.pi) = 0 := min_eq_left (by positivity)
      linarith [h, ht.1]
    have ht2 : t ≤ 2 * Real.pi := by
      have h : max (0 : ℝ) (2 * Real.pi) = 2 * Real.pi := max_eq_right (by positivity)
      linarith [h, ht.2]
    have ht' : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨le_of_lt ht0, ht2⟩
    rw [hderiv t ht', hval t ht']
  show karS CI W ρh δ k p.1 p.2 = Work.RPB.signedArea (fun t => V p.1 p.2 t)
  unfold karS Work.RPB.signedArea
  rw [hInt]

/-- **`kg` is `C¹¹` on the `τ`-strip**, being `2π(1+σ)` divided by the non-vanishing `karS`. -/
theorem c8_kg_contDiffOn (CI : Work.RPV.CurveIsotopy) {ρ₀ κ δ : ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hδ : 0 < δ) (hδκ : δ < κ) (hδ2 : δ ≤ 2) (k : ℤ)
    (hkarS : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, karS CI W ρh δ k τ σ ≠ 0) :
    ContDiffOn ℝ 11 (fun z : ℝ × ℝ => kg CI W ρh δ k z.1 z.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  have hkarScd := c8_karS_contDiffOn (CI := CI) (W := W) (ρh := ρh) hW hκ hρh hρhv
    hδ hδκ hδ2 k
  have hnum : ContDiffOn ℝ 11 (fun z : ℝ × ℝ => 2 * Real.pi * (1 + z.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by fun_prop
  have h := hnum.div hkarScd (fun p hp => hkarS p.1 hp.1 p.2)
  exact h.congr (fun p _ => rfl)

/-- **The collar curve family is globally smooth in the `τ`-strip.** -/
theorem c8_kgam_contDiffOn (CI : Work.RPV.CurveIsotopy) {ρ₀ κ δ : ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hδ : 0 < δ) (hδκ : δ < κ) (hδ2 : δ ≤ 2) (k : ℤ)
    (hkarS : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, karS CI W ρh δ k τ σ ≠ 0) :
    ContDiffOn ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => kgam CI W ρh δ k z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)) := by
  have hkg := c8_kg_contDiffOn (CI := CI) (W := W) (ρh := ρh) hW hκ hρh hρhv hδ hδκ hδ2 k hkarS
  have hkg8 : ContDiffOn ℝ 8 (fun z : ℝ × ℝ => kg CI W ρh δ k z.1 z.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := hkg.of_le (by norm_num)
  have hksh : ContDiffOn ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => kshape CI W ρh δ k z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)) :=
    (kappa_kshape_contDiff_joint (CI := CI) (ρ₀ := ρ₀) (W := W) (ρh := ρh) hW hκ hρh hρhv
      hδ hδκ hδ2 k).of_le (by norm_num) |>.mono (fun z hz => ⟨hz.1, trivial, trivial⟩)
  have hpair : ContDiffOn ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => (kg CI W ρh δ k z.1 z.2.1, kshape CI W ρh δ k z.1 z.2.1 z.2.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)) :=
    (hkg8.comp (by fun_prop : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ))) (fun z hz => ⟨hz.1, trivial⟩)).prodMk hksh
  have hk : ContDiff ℝ 8 (fun p : ℝ × ℂ => kdiagM p.1 p.2) := by
    have h1 : ContDiff ℝ 8 (fun p : ℝ × ℂ => ((Complex.reCLM p.2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp contDiff_snd)
    have h2 : ContDiff ℝ 8
        (fun p : ℝ × ℂ => (((p.1 * Complex.imCLM p.2 : ℝ)) : ℂ) * Complex.I) :=
      (Complex.ofRealCLM.contDiff.comp
        (contDiff_fst.mul (Complex.imCLM.contDiff.comp contDiff_snd))).mul contDiff_const
    have h := h1.add h2
    simpa only [kdiagM, Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply] using h
  have h := hk.comp_contDiffOn hpair
  simpa only [Function.comp_def, kgam, kdiagM] using h


/-- Globalise a function of `(τ,σ)` which is only known to be `C^n` on the strip
`[0,1] × ℝ`, using `tauSlabExtend` with a dummy third variable. -/
theorem c8_extend_tau_sigma {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (f : ℝ → ℝ → E)
    (hf : ContDiffOn ℝ n (fun z : ℝ × ℝ => f z.1 z.2) (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) :
    ∃ f' : ℝ → ℝ → E, ContDiff ℝ n (fun z : ℝ × ℝ => f' z.1 z.2) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, f' τ σ = f τ σ) := by
  have hdummy : ContDiffOn ℝ n (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2.1)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :=
    hf.comp (by fun_prop : ContDiffOn ℝ n
      (fun z : ℝ × (ℝ × ℝ) => ((z.1, z.2.1) : ℝ × ℝ))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1))
      (fun z hz => ⟨hz.1, trivial⟩)
  obtain ⟨F, hFcd, hFeq⟩ := tauSlabExtend (fun τ σ _ => f τ σ) n (by norm_num) hdummy
  refine ⟨fun τ σ => F (c8tau τ) σ 0, ?_, ?_⟩
  · have hmap : ContDiff ℝ n (fun z : ℝ × ℝ => (c8tau z.1, z.2, (0 : ℝ))) :=
      ((c8tau_contDiff.comp contDiff_fst).of_le (by simp)).prodMk
        (contDiff_snd.prodMk contDiff_const)
    have hmem : Set.MapsTo (fun z : ℝ × ℝ => (c8tau z.1, z.2, (0 : ℝ)))
        Set.univ (Set.Ioo (-1 : ℝ) 2 ×ˢ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :=
      fun z _ => ⟨c8tau_mem z.1, trivial, ⟨by norm_num, by norm_num⟩⟩
    have h := hFcd.comp hmap.contDiffOn hmem
    rw [contDiffOn_univ] at h
    exact h
  · intro τ hτ σ
    have h1 : c8tau τ = τ := c8tau_of_mem hτ
    show F (c8tau τ) σ 0 = f τ σ
    rw [h1]
    exact hFeq τ hτ σ 0 ⟨by norm_num, by norm_num⟩

/-- **A global smooth model of `kac` on the `τ`-strip up to `t = M/2`.** -/
theorem c8_kac_global (CI : Work.RPV.CurveIsotopy) {ρ₀ κ δ : ℝ}
    {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hδ : 0 < δ) (hδκ : δ < κ) (hδ2 : δ ≤ 2) (k : ℤ)
    (hkarS : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, karS CI W ρh δ k τ σ ≠ 0)
    (hkA0 : ContDiffOn ℝ 8 (fun z : ℝ × ℝ => kA0 W ρh δ k z.1 z.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))
    {M : ℝ} (hM4 : 4 * Real.pi < M) :
    ∃ G : ℝ → ℝ → ℝ → ℝ,
      ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => G z.1 z.2.1 z.2.2) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (M / 2),
        G τ σ t = kac CI W ρh δ k τ σ t) := by
  have hM : (0 : ℝ) < M := by linarith [Real.pi_pos]
  have h2M : (0 : ℝ) < 2 * M := by linarith
  -- the globalised shape (with a doubled clamp, so that `[0,M/2]` sits strictly inside)
  obtain ⟨V, hVcd, hVeq⟩ := c8_shape_global (CI := CI) (W := W) (ρh := ρh) hW hκ hρh hρhv
    hδ hδκ hδ2 k h2M
  have hVeq' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (M / 2),
      V τ σ t = kshape CI W ρh δ k τ σ t :=
    fun τ hτ σ t ht => hVeq τ hτ σ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- the globalised `kg`
  obtain ⟨kgg, hkggcd, hkggeq⟩ := c8_extend_tau_sigma
    (fun τ σ : ℝ => kg CI W ρh δ k τ σ)
    (c8_kg_contDiffOn (CI := CI) (W := W) (ρh := ρh) hW hκ hρh hρhv hδ hδκ hδ2 k hkarS)
  -- the global model of `kgam`
  set GΓ : ℝ → ℝ → ℝ → ℂ := fun τ σ t => kdiagM (kgg τ σ) (V τ σ t) with hGΓdef
  have hGΓcd : ContDiff ℝ 11 (fun z : ℝ × (ℝ × ℝ) => GΓ z.1 z.2.1 z.2.2) := by
    have hpair : ContDiff ℝ 11 (fun z : ℝ × (ℝ × ℝ) => (kgg z.1 z.2.1, V z.1 z.2.1 z.2.2)) :=
      ((hkggcd.comp (by fun_prop : ContDiff ℝ 11 (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1)))).prodMk
        (hVcd.of_le (by norm_num)))
    have hk : ContDiff ℝ 11 (fun p : ℝ × ℂ => kdiagM p.1 p.2) := by
      have h1 : ContDiff ℝ 11 (fun p : ℝ × ℂ => ((Complex.reCLM p.2 : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp contDiff_snd)
      have h2 : ContDiff ℝ 11
          (fun p : ℝ × ℂ => (((p.1 * Complex.imCLM p.2 : ℝ)) : ℂ) * Complex.I) :=
        (Complex.ofRealCLM.contDiff.comp
          (contDiff_fst.mul (Complex.imCLM.contDiff.comp contDiff_snd))).mul contDiff_const
      have h := h1.add h2
      simpa only [kdiagM, Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply] using h
    have h := hk.comp hpair
    simpa only [Function.comp_def, hGΓdef] using h
  have hGΓeq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, ∀ t ∈ Set.Ioo (-(M / 2)) M,
      GΓ τ σ t = kgam CI W ρh δ k τ σ t := by
    intro τ hτ σ t ht
    have h1 : kgg τ σ = kg CI W ρh δ k τ σ := hkggeq τ hτ σ
    have h2 : V τ σ t = kshape CI W ρh δ k τ σ t :=
      hVeq τ hτ σ t (by refine ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    simp only [hGΓdef, h1, h2, kgam]
  -- the flux integrand, globalised
  have h9a : ContDiff ℝ 9 (fun z : (ℝ × ℝ) × ℝ => GΓ z.1.1 z.2 z.1.2) := by
    have hφ : ContDiff ℝ 9 (fun z : (ℝ × ℝ) × ℝ => ((z.1.1, (z.2, z.1.2)) : ℝ × (ℝ × ℝ))) :=
      (by fun_prop : ContDiff ℝ 9 fun z : (ℝ × ℝ) × ℝ => (z.1.1, (z.2, z.1.2)))
    have h := hGΓcd.of_le (by norm_num) |>.comp hφ
    simpa [Function.comp_def] using h
  have hF1' : ContDiff ℝ 8
      (fun z : (ℝ × ℝ) × ℝ => deriv (fun s => GΓ z.1.1 s z.1.2) z.2) :=
    contDiff_sliceDeriv_gen (X := ℝ × ℝ) (V := fun x s => GΓ x.1 s x.2) (k := 8) h9a
  have hF1 : ContDiff ℝ 8
      (fun z : (ℝ × ℝ) × ℝ => deriv (fun s => GΓ z.1.1 s z.2) z.1.2) := by
    have hφ : ContDiff ℝ 8 (fun z : (ℝ × ℝ) × ℝ => ((z.1.1, z.2), z.1.2)) := by fun_prop
    have h := hF1'.comp hφ
    simpa [Function.comp_def] using h
  have h9b : ContDiff ℝ 9 (fun z : (ℝ × ℝ) × ℝ => GΓ z.1.1 z.1.2 z.2) := by
    have hφ : ContDiff ℝ 9 (fun z : (ℝ × ℝ) × ℝ => ((z.1.1, (z.1.2, z.2)) : ℝ × (ℝ × ℝ))) :=
      (by fun_prop : ContDiff ℝ 9 fun z : (ℝ × ℝ) × ℝ => (z.1.1, (z.1.2, z.2)))
    have h := hGΓcd.of_le (by norm_num) |>.comp hφ
    simpa [Function.comp_def] using h
  have hF2 : ContDiff ℝ 8
      (fun z : (ℝ × ℝ) × ℝ => deriv (fun s => GΓ z.1.1 z.1.2 s) z.2) :=
    contDiff_sliceDeriv_gen (X := ℝ × ℝ) (V := fun x s => GΓ x.1 x.2 s) (k := 8) h9b
  have hWω : ContDiff ℝ 8 (fun z : (ℝ × ℝ) × ℝ =>
      Work.RPV.ωC (deriv (fun s => GΓ z.1.1 s z.2) z.1.2)
        (deriv (fun s => GΓ z.1.1 z.1.2 s) z.2)) := contDiff_omegaC hF1 hF2
  have hK : ContDiff ℝ 8 (fun z : (ℝ × ℝ) × ℝ =>
      ∫ u in (0 : ℝ)..z.2, Work.RPV.ωC (deriv (fun s => GΓ z.1.1 s u) z.1.2)
        (deriv (fun s => GΓ z.1.1 z.1.2 s) u)) :=
    Work.RPB.B4.paramIntegral_variable 8 (fun (z : ℝ × ℝ) u => Work.RPV.ωC
      (deriv (fun s => GΓ z.1 s u) z.2) (deriv (fun s => GΓ z.1 z.2 s) u)) hWω
  -- the globalised constant
  obtain ⟨kA0g, hkA0g, hkA0geq⟩ := c8_extend_tau_sigma (fun τ σ : ℝ => kA0 W ρh δ k τ σ) hkA0
  refine ⟨fun τ σ t => kA0g τ σ +
      ∫ u in (0 : ℝ)..t, Work.RPV.ωC (deriv (fun s => GΓ τ s u) σ)
        (deriv (fun s => GΓ τ σ s) u), ?_, ?_⟩
  · have h1 : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => kA0g z.1 z.2.1) :=
      ((hkA0g.comp (by fun_prop : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1)))).of_le le_rfl)
    have h2 : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) =>
        ∫ u in (0 : ℝ)..z.2.2, Work.RPV.ωC (deriv (fun s => GΓ z.1 s u) z.2.1)
          (deriv (fun s => GΓ z.1 z.2.1 s) u)) := by
      have hφ : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ((z.1, z.2.1), z.2.2)) := by fun_prop
      have h := hK.comp hφ
      simpa [Function.comp_def] using h
    exact h1.add h2
  · -- the agreement with `kac`
    intro τ hτ σ t ht
    have hA0 : kA0g τ σ = kA0 W ρh δ k τ σ := hkA0geq τ hτ σ
    have hflux : ∀ u ∈ Set.Icc (0 : ℝ) (M / 2),
        Work.RPV.ωC (deriv (fun s => GΓ τ s u) σ) (deriv (fun s => GΓ τ σ s) u)
          = Work.RPV.ωC (deriv (fun s => kgam CI W ρh δ k τ s u) σ)
              (deriv (fun s => kgam CI W ρh δ k τ σ s) u) := by
      intro u hu
      have hu' : u ∈ Set.Ioo (-(M / 2)) M :=
        ⟨by linarith [hu.1, hM], by linarith [hu.2, hM]⟩
      have hσ : deriv (fun s => GΓ τ s u) σ
          = deriv (fun s => kgam CI W ρh δ k τ s u) σ := by
        apply Filter.EventuallyEq.deriv_eq
        exact Filter.Eventually.of_forall (fun s => hGΓeq τ hτ s u hu')
      have ht' : deriv (fun s => GΓ τ σ s) u
          = deriv (fun s => kgam CI W ρh δ k τ σ s) u := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [isOpen_Ioo.mem_nhds
          (show u ∈ Set.Ioo (-(M / 2)) M from ⟨by linarith [hu.1, hM], by linarith [hu.2, hM]⟩)]
          with u' hu'
        exact hGΓeq τ hτ σ u' hu'
      rw [hσ, ht']
    have hInt : (∫ u in (0 : ℝ)..t, Work.RPV.ωC (deriv (fun s => GΓ τ s u) σ)
        (deriv (fun s => GΓ τ σ s) u))
        = (∫ u in (0 : ℝ)..t, Work.RPV.ωC (deriv (fun s => kgam CI W ρh δ k τ s u) σ)
            (deriv (fun s => kgam CI W ρh δ k τ σ s) u)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with u hu
      have hu0 : (0 : ℝ) < u := by
        have h : min (0 : ℝ) t = 0 := min_eq_left ht.1
        linarith [h, hu.1]
      have hut : u ≤ t := by
        have h : max (0 : ℝ) t = t := max_eq_right ht.1
        linarith [h, hu.2]
      exact hflux u ⟨le_of_lt hu0, le_trans hut ht.2⟩
    show kA0g τ σ + (∫ u in (0 : ℝ)..t, Work.RPV.ωC (deriv (fun s => GΓ τ s u) σ)
        (deriv (fun s => GΓ τ σ s) u)) = kac CI W ρh δ k τ σ t
    rw [hInt, hA0]
    rfl

/-- **`kA0` is `C⁸` on the `τ`-strip**, given the `τ`-smoothness of the jets `kcj`. -/
theorem c8_kA0_contDiffOn (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (κ : ℝ) (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    (δ : ℝ) (k : ℤ) :
    ContDiffOn ℝ 8 (fun z : ℝ × ℝ => kA0 W ρh δ k z.1 z.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  have hcj : ∀ j : ℕ, j ≤ 8 → ContDiffOn ℝ 8 (fun τ : ℝ => kcj W ρh τ j)
      (Set.Icc (0 : ℝ) 1) :=
    fun j hj => Work.RPB.B5.C8.kcj_tau_contDiffOn CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hρh hρh0 hρhv hρhl j hj
  have hcst : ContDiffOn ℝ 8
      (fun z : ℝ × ℝ => kphc δ k z.2 + Real.pi / 2 + 2 * Real.pi * (k : ℝ))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    have : ContDiff ℝ 8 (fun z : ℝ × ℝ => kphc δ k z.2 + Real.pi / 2 + 2 * Real.pi * (k : ℝ)) := by
      have h : ContDiff ℝ 8 (fun σ : ℝ => kphc δ k σ) := by
        have hk : ContDiff ℝ 8 kstp := kstp_contDiff.of_le (by norm_num)
        unfold kphc
        exact (contDiff_const.mul (hk.comp (by fun_prop)))
      simpa only [Function.comp_def, add_assoc] using (h.comp contDiff_snd).add
        (contDiff_const : ContDiff ℝ 8 (fun _ : ℝ × ℝ => Real.pi / 2 + 2 * Real.pi * (k : ℝ)))
    exact this.contDiffOn.mono (Set.subset_univ _)
  have hsum : ContDiffOn ℝ 8 (fun z : ℝ × ℝ =>
      ∑ j ∈ Finset.range 9,
        (kcj W ρh z.1 j - kcj W ρh 0 j) * (z.2 ^ j / (Nat.factorial j : ℝ)) * kjbump δ z.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    refine ContDiffOn.sum (fun j hj => ?_)
    have hj8 : j ≤ 8 := Nat.le_of_lt_succ (Finset.mem_range.1 hj)
    have hkj : ContDiffOn ℝ 8
        (fun z : ℝ × ℝ => kcj W ρh z.1 j - kcj W ρh 0 j) (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
      ((hcj j hj8).comp (by fun_prop) (fun z hz => hz.1)).sub contDiffOn_const
    have hkjb : ContDiffOn ℝ 8
        (fun z : ℝ × ℝ => z.2 ^ j / (Nat.factorial j : ℝ) * kjbump δ z.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
      have hbump : ContDiff ℝ 8 (fun z : ℝ × ℝ => kjbump δ z.2) := by
        have hk : ContDiff ℝ 8 kstp := kstp_contDiff.of_le (by norm_num)
        unfold kjbump
        exact contDiff_const.sub (hk.comp (by fun_prop))
      have : ContDiff ℝ 8 (fun z : ℝ × ℝ => z.2 ^ j / (Nat.factorial j : ℝ) * kjbump δ z.2) :=
        (by fun_prop : ContDiff ℝ 8 (fun z : ℝ × ℝ => z.2 ^ j / (Nat.factorial j : ℝ))).mul hbump
      exact this.contDiffOn.mono (Set.subset_univ _)
    exact (hkj.mul hkjb).congr (fun z _ => by ring)
  unfold kA0
  exact hcst.add hsum

theorem kappa_collar_C8 (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (κ : ℝ) (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    (hρhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    (k : ℤ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ κ ∧
      ∀ δ ∈ Set.Ioo (0 : ℝ) δ₀,
        ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B5.kgam CI W ρh δ k z.1 z.2.1 z.2.2)
            (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)) ∧
        ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B5.kac CI W ρh δ k z.1 z.2.1 z.2.2)
            (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)) := by
  obtain ⟨δA, hδApos, hδAκ, hA⟩ :=
    kappa_collar_area_all CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hWper hρh hρh0 hρhv hρhl hρhper k
  have hpos : (0 : ℝ) < min δA (min κ 2) := lt_min hδApos (lt_min hκ (by norm_num))
  refine ⟨min δA (min κ 2) / 4, by positivity, ?_, ?_⟩
  · have h1 : min δA (min κ 2) / 4 ≤ min δA (min κ 2) := by linarith
    have h2 : min δA (min κ 2) ≤ κ := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  · intro δ hδ
    obtain ⟨hδpos, hδlt⟩ := hδ
    have hδsmall : δ < min δA (min κ 2) := by linarith
    have hδA2 : δ < δA := lt_of_lt_of_le hδsmall (min_le_left _ _)
    have hδκ2 : δ < κ :=
      lt_of_lt_of_le hδsmall (le_trans (min_le_right _ _) (min_le_left _ _))
    have hδ2 : δ ≤ 2 :=
      le_of_lt (lt_of_lt_of_le hδsmall (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hkarS : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, karS CI W ρh δ k τ σ ≠ 0 :=
      fun τ hτ σ => (hA δ ⟨hδpos, hδA2⟩ τ hτ σ).2
    have hkA0 := c8_kA0_contDiffOn CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hρh hρh0 hρhv hρhl δ k
    refine ⟨c8_kgam_contDiffOn (CI := CI) (W := W) (ρh := ρh) hW hκ hρh hρhv
      hδpos hδκ2 hδ2 k hkarS, ?_⟩
    refine contDiffOn_of_locally_contDiffOn (fun x hx => ?_)
    set M : ℝ := max (2 * (x.2.2 + 1)) (8 * Real.pi + 1) with hMdef
    have hM4 : 4 * Real.pi < M := by
      have h1 : 4 * Real.pi < 8 * Real.pi + 1 := by linarith [Real.pi_pos]
      exact lt_of_lt_of_le h1 (le_max_right _ _)
    obtain ⟨G, hGcd, hGeq⟩ := c8_kac_global (CI := CI) (W := W) (ρh := ρh) hW hκ hρh hρhv
      hδpos hδκ2 hδ2 k hkarS hkA0 hM4
    refine ⟨Set.Ioo (-2 : ℝ) 3 ×ˢ Set.univ ×ˢ Set.Ioo (x.2.2 - 1) (x.2.2 + 1), ?_, ?_, ?_⟩
    · exact isOpen_Ioo.prod (isOpen_univ.prod isOpen_Ioo)
    · exact ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, trivial, ⟨by linarith, by linarith⟩⟩
    · refine (hGcd.contDiffOn.mono (Set.subset_univ _)).congr (fun z hz => ?_)
      obtain ⟨hz1, hz2⟩ := hz
      have htmax : x.2.2 + 1 ≤ M / 2 := by
        have h1 : 2 * (x.2.2 + 1) ≤ M := le_max_left _ _
        linarith
      have hz3 : z.2.2 ∈ Set.Icc (0 : ℝ) (M / 2) :=
        ⟨hz1.2.2, le_trans (le_of_lt hz2.2.2.2) htmax⟩
      exact ((hGeq z.1 hz1.1 z.2.1 z.2.2 hz3).symm)
