import Mathlib
import Submission.Work.WilE2.RegVals.Basic
import Submission.Work.WilE2.RegVals.reg_aux
import Submission.Work.WilE2.RegVals.reg_chart
import Submission.Work.WilE2.RegVals.isClosed_setOf_not_surjective

open MeasureTheory
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.WilE2.RegVals

/-! ## 3. The reduction step -/

/-- The index complementary to `i` at `m`. -/
theorem choose_succAbove {k : ℕ} (i : Fin (k+1)) {m : Fin (k+1)} (hm : m ≠ i) :
    i.succAbove (Classical.choose (Fin.exists_succAbove_eq hm)) = m :=
  Classical.choose_spec (Fin.exists_succAbove_eq hm)

/-- The linear map `(v,c) ↦ Fin.insertNth i c v`. -/
def insCLM {k : ℕ} (i : Fin (k+1)) : ((Fin k → ℝ) × ℝ) →L[ℝ] (Fin (k+1) → ℝ) :=
  ContinuousLinearMap.pi (fun m => dite (m = i)
    (fun _ => ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ)
    (fun hm => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ)
        (Classical.choose (Fin.exists_succAbove_eq hm))).comp
      (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)))

theorem insCLM_apply {k : ℕ} (i : Fin (k+1)) (v : Fin k → ℝ) (c : ℝ) :
    insCLM i (v, c) = Fin.insertNth (α := fun _ => ℝ) i c v := by
  funext m
  rw [insCLM, ContinuousLinearMap.pi_apply]
  by_cases hm : m = i
  · rw [dif_pos hm, hm, Fin.insertNth_apply_same]
    rfl
  · rw [dif_neg hm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    set l := Classical.choose (Fin.exists_succAbove_eq hm) with hl
    have hlm : i.succAbove l = m := by rw [hl]; exact choose_succAbove i hm
    show v l = Fin.insertNth (α := fun _ => ℝ) i c v m
    rw [← hlm, Fin.insertNth_apply_succAbove]

theorem insCLM_surjective {k : ℕ} (i : Fin (k+1)) : Function.Surjective (insCLM i) := by
  intro y
  exact ⟨(fun l => y (i.succAbove l), y i), by
    rw [insCLM_apply]; exact insertNth_self i y⟩

theorem insCLM_injective {k : ℕ} (i : Fin (k+1)) : Function.Injective (insCLM i) := by
  intro p q hpq
  rw [show p = (p.1, p.2) from rfl, show q = (q.1, q.2) from rfl, insCLM_apply, insCLM_apply] at hpq
  obtain ⟨h1, h2⟩ := insertNth_inj i p.2 q.2 p.1 q.1 hpq
  exact Prod.ext h2 h1

/-- The `(k+1)`-dimensional stage of the codimension-one Sard reduction. -/
theorem reduction_step_aux {k : ℕ} (g : (Fin (k+2) → ℝ) → (Fin (k+1) → ℝ))
    (hg : ContDiff ℝ 2 g) (x₀ : Fin (k+2) → ℝ)
    (hx₀ : ¬ Function.Surjective (fderiv ℝ g x₀)) (hne : fderiv ℝ g x₀ ≠ 0)
    (IH : ∀ j, j < k+2 → ∀ (h : (Fin j → ℝ) → (Fin (j-1) → ℝ)), ContDiff ℝ 2 h →
        MeasureTheory.volume (h '' {z | ¬ Function.Surjective (fderiv ℝ h z)}) = 0) :
    ∃ δ > 0,
      MeasureTheory.volume (g '' (Metric.ball x₀ δ ∩ {z | ¬ Function.Surjective (fderiv ℝ g z)})) = 0 := by
  classical
  obtain ⟨i, j, hj⟩ := exists_coord (fderiv ℝ g x₀) hne
  have hj' : (fderiv ℝ (fun z => g z i) x₀) (Pi.single j (1:ℝ)) ≠ 0 := by
    have hdc := fderiv_coord g x₀ (hg.contDiffAt.differentiableAt (by norm_num)) i
    rw [hdc, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    exact hj
  -- ## Step 1: the local inverse of `Xi`
  have hbij : Function.Bijective (XiD g i j x₀) :=
    ⟨fun u v huv => by
      have hsub : u - v = 0 :=
        XiD_eq_zero g i j x₀ hj' (u - v) (by rw [map_sub, huv, sub_self])
      exact sub_eq_zero.mp hsub,
     XiD_surjective g i j x₀ hj'⟩
  let e : (Fin (k+2) → ℝ) ≃L[ℝ] (Fin (k+2) → ℝ) :=
    (LinearEquiv.ofBijective (XiD g i j x₀).toLinearMap hbij).toContinuousLinearEquiv
  have he : (e : (Fin (k+2) → ℝ) →L[ℝ] (Fin (k+2) → ℝ)) = XiD g i j x₀ := by
    refine ContinuousLinearMap.ext fun v => ?_
    change e v = XiD g i j x₀ v
    rw [show e v = e.toLinearEquiv v from rfl]
    rw [show e.toLinearEquiv = LinearEquiv.ofBijective (XiD g i j x₀).toLinearMap hbij from
      LinearEquiv.toLinearEquiv_toContinuousLinearEquiv _]
    rw [LinearEquiv.ofBijective_apply]
    rfl
  have hXiD' : HasFDerivAt (Xi g i j) (e : (Fin (k+2) → ℝ) →L[ℝ] (Fin (k+2) → ℝ)) x₀ := by
    rw [he]; exact hasFDerivAt_Xi g i j x₀ hg
  have hstr : HasStrictFDerivAt (Xi g i j) (e : (Fin (k+2) → ℝ) →L[ℝ] (Fin (k+2) → ℝ)) x₀ :=
    (contDiffAt_Xi g i j x₀ hg).hasStrictFDerivAt' hXiD' (by norm_num)
  let Ω : (Fin (k+2) → ℝ) → (Fin (k+2) → ℝ) := hstr.localInverse
  have hΩcd : ContDiffAt ℝ 2 Ω (Xi g i j x₀) :=
    (contDiffAt_Xi g i j x₀ hg).to_localInverse hXiD' (by norm_num)
  have hΩleft : ∀ᶠ z in 𝓝 x₀, Ω (Xi g i j z) = z := by
    simpa [Ω] using hstr.eventually_left_inverse
  have hΩright : ∀ᶠ w in 𝓝 (Xi g i j x₀), Xi g i j (Ω w) = w := by
    simpa [Ω] using hstr.eventually_right_inverse
  obtain ⟨r₀, hr₀pos, hr₀⟩ : ∃ r > 0, ∀ z, dist z x₀ < r → Ω (Xi g i j z) = z :=
    Metric.mem_nhds_iff.mp hΩleft
  -- ## Step 2: `fderiv Ξ` is surjective near `x₀`
  obtain ⟨uΩ, huΩ, hΩon⟩ : ∃ u ∈ 𝓝 (Xi g i j x₀), ContDiffOn ℝ 2 Ω u :=
    hΩcd.contDiffOn (le_refl (2 : WithTop ℕ∞)) (by intro h; exact absurd h (by norm_num))
  set U' : Set (Fin (k+2) → ℝ) := interior uΩ with hU'def
  have hU'o : IsOpen U' := isOpen_interior
  have hU'mem : Xi g i j x₀ ∈ U' := mem_interior_iff_mem_nhds.mpr huΩ
  have hΩon' : ContDiffOn ℝ 2 Ω U' := hΩon.mono interior_subset
  have hΩcd_at : ∀ w ∈ U', ContDiffAt ℝ 2 Ω w := fun w hw =>
    hΩon'.contDiffAt (hU'o.mem_nhds hw)
  have hΩdiff_at : ∀ w ∈ U', DifferentiableAt ℝ Ω w := fun w hw =>
    ((hΩon'.differentiableOn (by norm_num) w hw)).differentiableAt (hU'o.mem_nhds hw)
  obtain ⟨r₁, hr₁pos, hr₁⟩ : ∃ r > 0, Metric.ball (Xi g i j x₀) r ⊆ U' :=
    Metric.mem_nhds_iff.mp (hU'o.mem_nhds hU'mem)
  obtain ⟨r₂, hr₂pos, hr₂⟩ : ∃ r > 0, Metric.ball (Xi g i j x₀) r ⊆
      {w | Xi g i j (Ω w) = w} :=
    Metric.mem_nhds_iff.mp hΩright
  obtain ⟨r₃, hr₃pos, hr₃⟩ : ∃ r > 0, ∀ z, dist z x₀ < r →
      dist (Xi g i j z) (Xi g i j x₀) < min r₁ r₂ :=
    Metric.continuousAt_iff.mp (contDiffAt_Xi g i j x₀ hg).continuousAt (min r₁ r₂)
      (lt_min hr₁pos hr₂pos)
  have hsurjΞ : ∀ z, dist z x₀ < min r₀ r₃ →
      Function.Surjective (fderiv ℝ (Xi g i j) z) := by
    intro z hz
    have hz₀ : dist z x₀ < r₀ := lt_of_lt_of_le hz (min_le_left _ _)
    have hz₃ : dist z x₀ < r₃ := lt_of_lt_of_le hz (min_le_right _ _)
    have hz₁ : dist (Xi g i j z) (Xi g i j x₀) < r₁ :=
      lt_of_lt_of_le (hr₃ z hz₃) (min_le_left _ _)
    have hz₂ : dist (Xi g i j z) (Xi g i j x₀) < r₂ :=
      lt_of_lt_of_le (hr₃ z hz₃) (min_le_right _ _)
    have hΩdiff : DifferentiableAt ℝ Ω (Xi g i j z) := hΩdiff_at _ (hr₁ hz₁)
    have hΩz : Ω (Xi g i j z) = z := hr₀ z hz₀
    have hEq : (Xi g i j ∘ Ω) =ᶠ[𝓝 (Xi g i j z)] id := by
      refine Filter.mem_of_superset
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball.mpr hz₂)) ?_
      intro w hw
      simp only [Function.comp_apply, id_eq]
      exact hr₂ hw
    have hcomp : (fderiv ℝ (Xi g i j) (Ω (Xi g i j z))).comp (fderiv ℝ Ω (Xi g i j z))
        = ContinuousLinearMap.id ℝ (Fin (k+2) → ℝ) := by
      rw [← fderiv_comp (Xi g i j z)
        ((contDiffAt_Xi g i j (Ω (Xi g i j z)) hg).differentiableAt (by norm_num)) hΩdiff]
      rw [hEq.fderiv_eq, fderiv_id]
    rw [hΩz] at hcomp
    intro v
    refine ⟨(fderiv ℝ Ω (Xi g i j z)) v, ?_⟩
    have hh := congrFun (congrArg DFunLike.coe hcomp) v
    simpa using hh
  -- ## Step 3: the slice map and its global `C²` extension
  set Sig : (Fin (k+2) → ℝ) → ((Fin (k+1) → ℝ) × ℝ) := fun z => (crj j z, g z i) with hSigdef
  have hSigcont : Continuous Sig :=
    (kdrj j).continuous.prodMk
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+1) => ℝ) i).continuous.comp hg.continuous)
  have hΞSig : ∀ z, insCLM j (Sig z) = Xi g i j z := by
    intro z
    simp only [hSigdef, Prod.mk.eta]
    rw [insCLM_apply]
    funext m
    rw [Xi_apply g i j z m]
    by_cases hm : m = j
    · rw [hm, Fin.insertNth_apply_same, if_pos rfl]
    · rw [if_neg hm]
      obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hm
      rw [← hl, Fin.insertNth_apply_succAbove]
      rfl
  have hWopen : IsOpen {p : (Fin (k+1) → ℝ) × ℝ | insCLM j p ∈ Metric.ball (Xi g i j x₀) r₁} :=
    (insCLM j).continuous.isOpen_preimage _ Metric.isOpen_ball
  have hx₀W : Sig x₀ ∈ {p : (Fin (k+1) → ℝ) × ℝ | insCLM j p ∈ Metric.ball (Xi g i j x₀) r₁} := by
    rw [Set.mem_setOf_eq, hΞSig]; exact Metric.mem_ball_self hr₁pos
  obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ : ∃ ρ > 0, Metric.ball x₀ ρ ⊆ Sig ⁻¹'
      {p : (Fin (k+1) → ℝ) × ℝ | insCLM j p ∈ Metric.ball (Xi g i j x₀) r₁} :=
    Metric.mem_nhds_iff.mp (hSigcont.continuousAt.preimage_mem_nhds (hWopen.mem_nhds hx₀W))
  set ρ : ℝ := min (min ρ₀ r₀) r₃ / 2 with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; have h := lt_min (lt_min hρ₀pos hr₀pos) hr₃pos; linarith
  have hρρ₀ : ρ < ρ₀ := by
    rw [hρdef]
    have h1 : min (min ρ₀ r₀) r₃ ≤ ρ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
    have h2 := lt_min (lt_min hρ₀pos hr₀pos) hr₃pos
    linarith
  have hρr₀ : ρ < r₀ := by
    rw [hρdef]
    have h1 : min (min ρ₀ r₀) r₃ ≤ r₀ := le_trans (min_le_left _ _) (min_le_right _ _)
    have h2 := lt_min (lt_min hρ₀pos hr₀pos) hr₃pos
    linarith
  have hρr₃ : ρ < r₃ := by
    rw [hρdef]
    have h1 : min (min ρ₀ r₀) r₃ ≤ r₃ := min_le_right _ _
    have h2 := lt_min (lt_min hρ₀pos hr₀pos) hr₃pos
    linarith
  have hρ : Metric.ball x₀ ρ ⊆ Sig ⁻¹'
      {p : (Fin (k+1) → ℝ) × ℝ | insCLM j p ∈ Metric.ball (Xi g i j x₀) r₁} :=
    fun z hz => hρ₀ (Metric.mem_ball.mpr (lt_trans (Metric.mem_ball.mp hz) hρρ₀))
  set K : Set ((Fin (k+1) → ℝ) × ℝ) := Sig '' Metric.closedBall x₀ (ρ/2) with hKdef
  have hKcomp : IsCompact K := (isCompact_closedBall x₀ (ρ/2)).image hSigcont
  have hKW : K ⊆ {p : (Fin (k+1) → ℝ) × ℝ | insCLM j p ∈ Metric.ball (Xi g i j x₀) r₁} := by
    rintro p ⟨z, hz, rfl⟩
    exact hρ (by
      rw [Metric.mem_ball]
      have h := Metric.mem_closedBall.mp hz
      linarith)
  obtain ⟨V, hVo, hKV, hVW⟩ := exists_open_between hKcomp hWopen hKW
  obtain ⟨χ, hχcd, hχ1, hχsupp⟩ := exists_smooth_cutoff_supp hKcomp hVo hKV
  set φ : ((Fin (k+1) → ℝ) × ℝ) → (Fin k → ℝ) :=
    fun p l => g (Ω (insCLM j p)) (i.succAbove l) with hφdef
  have hφcd : ∀ p ∈ V, ContDiffAt ℝ 2 φ p := by
    intro p hp
    have hpW : insCLM j p ∈ U' := hr₁ (hVW (subset_closure hp))
    have h1 : ContDiffAt ℝ 2 (fun q : (Fin (k+1) → ℝ) × ℝ => Ω (insCLM j q)) p :=
      (hΩcd_at _ hpW).comp p ((ContinuousLinearMap.contDiff (insCLM j)).contDiffAt)
    rw [hφdef]
    refine contDiffAt_pi.mpr fun l => ?_
    exact (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+1) => ℝ)
      (i.succAbove l)).contDiff).contDiffAt).comp p (hg.contDiffAt.comp p h1)
  set Φ : ((Fin (k+1) → ℝ) × ℝ) → (Fin k → ℝ) := fun p => χ p • φ p with hΦdef
  have hΦcd : ContDiff ℝ 2 Φ := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ V
    · exact hχcd.contDiffAt.smul (hφcd p hp)
    · have hp' : p ∉ tsupport χ := fun h => hp (hχsupp h)
      have hχ0 : χ =ᶠ[𝓝 p] 0 := by
        have hop : (tsupport χ)ᶜ ∈ 𝓝 p := (isClosed_tsupport χ).isOpen_compl.mem_nhds hp'
        filter_upwards [hop] with q hq
        exact image_eq_zero_of_notMem_tsupport hq
      have hsm : (fun q => χ q • φ q) =ᶠ[𝓝 p] (fun _ => (0 : Fin k → ℝ)) := by
        filter_upwards [hχ0] with q hq
        rw [hq]; simp
      rw [hΦdef]
      exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hsm
  have hΦeq : ∀ p ∈ K, Φ =ᶠ[𝓝 p] φ := by
    intro p hp
    filter_upwards [hχ1 p hp] with q hq
    rw [hΦdef]
    simp [hq]
  -- ## Step 4: `g` in terms of `Sig` and `Φ`
  have hgΘSig : ∀ z ∈ Metric.closedBall x₀ (ρ/2), g z = insCLM i (Φ (Sig z), g z i) := by
    intro z hz
    have hzK : Sig z ∈ K := Set.mem_image_of_mem _ hz
    have hΦz : Φ (Sig z) = φ (Sig z) := (hΦeq _ hzK).self_of_nhds
    have hPinv : Ω (insCLM j (Sig z)) = z := by
      rw [hΞSig z]
      exact hr₀ z (by
        have h := Metric.mem_closedBall.mp hz
        linarith [hρr₀, hρpos, h])
    have h1 : φ (Sig z) = fun l => g z (i.succAbove l) := by
      funext l
      rw [hφdef]
      show g (Ω (insCLM j (Sig z))) (i.succAbove l) = g z (i.succAbove l)
      rw [hPinv]
    rw [hΦz, h1, insCLM_apply, insertNth_self]
  -- ## Step 5: criticality transfers
  have hSigdiff : ∀ z, DifferentiableAt ℝ Sig z := by
    intro z
    have h1 : HasFDerivAt (fun z : Fin (k+2) → ℝ => crj j z) (kdrj j) z := by
      rw [show (fun z : Fin (k+2) → ℝ => crj j z) = kdrj j from
        funext fun z => (kdrj_apply j z).symm]
      exact (kdrj j).hasFDerivAt
    have h2 : HasFDerivAt (fun z : Fin (k+2) → ℝ => g z i)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+1) => ℝ) i).comp
          (fderiv ℝ g z)) z :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+1) => ℝ) i).hasFDerivAt.comp z
        ((hg.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt)
    have h3 := (h1.prodMk h2).differentiableAt
    simpa [hSigdef] using h3
  have hThdiff : ∀ p, DifferentiableAt ℝ (fun q => insCLM i (Φ q, q.2)) p := by
    intro p
    have hA : HasFDerivAt (fun q : (Fin (k+1) → ℝ) × ℝ => (Φ q, q.2))
        ((fderiv ℝ Φ p).prod (ContinuousLinearMap.snd ℝ (Fin (k+1) → ℝ) ℝ)) p :=
      ((hΦcd.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt).prodMk
        (ContinuousLinearMap.snd ℝ (Fin (k+1) → ℝ) ℝ).hasFDerivAt
    exact ((ContinuousLinearMap.hasFDerivAt (insCLM i)).comp p hA).differentiableAt
  have hcrit : ∀ z ∈ Metric.ball x₀ (ρ/2), Function.Surjective (fderiv ℝ g z) ↔
      Function.Surjective (fderiv ℝ (fun u' => Φ (u', g z i)) (crj j z)) := by
    intro z hz
    have hz' : dist z x₀ < min r₀ r₃ := by
      have h := Metric.mem_ball.mp hz
      have h2 : ρ / 2 < min r₀ r₃ :=
        lt_min (by linarith [hρr₀, hρpos]) (by linarith [hρr₃, hρpos])
      linarith
    have h1 : (fun z' : Fin (k+2) → ℝ => g z') =ᶠ[𝓝 z]
        (fun q => insCLM i (Φ q, q.2)) ∘ Sig := by
      have hmem : Metric.closedBall x₀ (ρ/2) ∈ 𝓝 z :=
        Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
      filter_upwards [hmem] with z' hz'
      simpa [Function.comp_def] using hgΘSig z' hz'
    have h2 : fderiv ℝ g z = (fderiv ℝ (fun q => insCLM i (Φ q, q.2)) (Sig z)).comp
        (fderiv ℝ Sig z) := by
      rw [h1.fderiv_eq, fderiv_comp z (hThdiff (Sig z)) (hSigdiff z)]
    have hSigsurj : Function.Surjective (fderiv ℝ Sig z) := by
      have hT₀ : Function.Surjective
          ((kdrj j).prod (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+2) => ℝ) j)) := by
        intro y
        refine ⟨Fin.insertNth (α := fun _ => ℝ) j y.2 y.1, ?_⟩
        rw [show ((kdrj j).prod (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+2) => ℝ) j))
            (Fin.insertNth (α := fun _ => ℝ) j y.2 y.1) = (y.1, y.2) from by
          rw [ContinuousLinearMap.prod_apply, ContinuousLinearMap.proj_apply, kdrj_apply]
          refine Prod.ext ?_ ?_
          · show crj j (Fin.insertNth (α := fun _ => ℝ) j y.2 y.1) = y.1
            funext l
            rw [crj_apply, Fin.insertNth_apply_succAbove]
          · show (Fin.insertNth (α := fun _ => ℝ) j y.2 y.1) j = y.2
            rw [Fin.insertNth_apply_same]]
      have hSigfun : Sig = ((kdrj j).prod
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+2) => ℝ) j)) ∘ Xi g i j := by
        funext z'
        rw [Function.comp_apply, show Sig z' = (crj j z', g z' i) from rfl,
          show ((kdrj j).prod (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+2) => ℝ) j))
            (Xi g i j z') = (crj j (Xi g i j z'), (Xi g i j z') j) from by
          rw [ContinuousLinearMap.prod_apply, ContinuousLinearMap.proj_apply, kdrj_apply]]
        rw [crj_Xi, Xi_apply]
        simp
      have hfd : fderiv ℝ Sig z = ((kdrj j).prod
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+2) => ℝ) j)).comp
            (fderiv ℝ (Xi g i j) z) := by
        rw [hSigfun, fderiv_comp z
          ((((kdrj j).prod (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+2) => ℝ) j)).hasFDerivAt).differentiableAt)
          ((contDiffAt_Xi g i j z hg).differentiableAt (by norm_num)),
          ContinuousLinearMap.fderiv]
      rw [hfd]
      exact hT₀.comp (hsurjΞ z hz')
    have h3 : Function.Surjective (fderiv ℝ g z) ↔
        Function.Surjective (fderiv ℝ (fun q => insCLM i (Φ q, q.2)) (Sig z)) := by
      rw [h2]
      exact ⟨fun h => Function.Surjective.of_comp h, fun h => h.comp hSigsurj⟩
    have h4 : Function.Surjective (fderiv ℝ (fun q => insCLM i (Φ q, q.2)) (Sig z)) ↔
        Function.Surjective ((fderiv ℝ Φ (Sig z)).comp
          (ContinuousLinearMap.inl ℝ (Fin (k+1) → ℝ) ℝ)) := by
      have hcomp : fderiv ℝ (fun q => insCLM i (Φ q, q.2)) (Sig z)
          = (insCLM i).comp ((fderiv ℝ Φ (Sig z)).prod
              (ContinuousLinearMap.snd ℝ (Fin (k+1) → ℝ) ℝ)) := by
        have hA : HasFDerivAt (fun q : (Fin (k+1) → ℝ) × ℝ => (Φ q, q.2))
            ((fderiv ℝ Φ (Sig z)).prod (ContinuousLinearMap.snd ℝ (Fin (k+1) → ℝ) ℝ)) (Sig z) :=
          ((hΦcd.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt).prodMk
            (ContinuousLinearMap.snd ℝ (Fin (k+1) → ℝ) ℝ).hasFDerivAt
        exact ((ContinuousLinearMap.hasFDerivAt (insCLM i)).comp (Sig z) hA).fderiv
      rw [hcomp]
      constructor
      · intro h
        have hA : Function.Surjective
            ((fderiv ℝ Φ (Sig z)).prod (ContinuousLinearMap.snd ℝ (Fin (k+1) → ℝ) ℝ)) := by
          intro y
          obtain ⟨p, hp⟩ := h (insCLM i y)
          exact ⟨p, insCLM_injective i (by simpa [Function.comp_def] using hp)⟩
        exact (surjective_prod_snd_iff (fderiv ℝ Φ (Sig z))).mp hA
      · intro h
        exact (insCLM_surjective i).comp ((surjective_prod_snd_iff (fderiv ℝ Φ (Sig z))).mpr h)
    have h5 : Function.Surjective ((fderiv ℝ Φ (Sig z)).comp
          (ContinuousLinearMap.inl ℝ (Fin (k+1) → ℝ) ℝ)) ↔
        Function.Surjective (fderiv ℝ (fun u' => Φ (u', g z i)) (crj j z)) := by
      rw [← fderiv_slice Φ (Sig z).1 (Sig z).2
        (hΦcd.contDiffAt.differentiableAt (by norm_num))]
    exact h3.trans (h4.trans h5)
  -- ## Step 6: the measure-theoretic conclusion
  set δ : ℝ := min r₀ (min r₃ (ρ/4)) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδlt : δ < ρ/4 := by
    have h1 : δ < min r₀ (min r₃ (ρ/4)) := by
      rw [hδdef]
      have : 0 < min r₀ (min r₃ (ρ/4)) := lt_min hr₀pos (lt_min hr₃pos (by positivity))
      linarith
    have h2 : min r₀ (min r₃ (ρ/4)) ≤ ρ/4 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  refine ⟨δ, hδpos, ?_⟩
  have hcritClosed : IsClosed {z : Fin (k+2) → ℝ | ¬ Function.Surjective (fderiv ℝ g z)} :=
    isClosed_setOf_not_surjective.preimage (hg.continuous_fderiv (by norm_num))
  set Scrit : Set (Fin (k+2) → ℝ) :=
    Metric.closedBall x₀ (ρ/4) ∩ {z | ¬ Function.Surjective (fderiv ℝ g z)} with hScritdef
  have hScritcomp : IsCompact Scrit :=
    (isCompact_closedBall x₀ (ρ/4)).inter_right hcritClosed
  set Λ : ((Fin (k+1) → ℝ) × ℝ) → (ℝ × (Fin k → ℝ)) := fun p => (p.2, Φ p) with hΛdef
  have hΛcont : Continuous Λ := continuous_snd.prodMk hΦcd.continuous
  set T : Set (ℝ × (Fin k → ℝ)) := Λ '' (Sig '' Scrit) with hTdef
  have hTmeas : MeasurableSet T := ((hScritcomp.image hSigcont).image hΛcont).measurableSet
  have hTnull : volume T = 0 := by
    refine volume_eq_zero_of_slices_null_real hTmeas fun c => ?_
    refine measure_mono_null ?_ (IH (k+1) (by omega) (fun u => Φ (u, c)) (by
      have harg : (fun u : Fin (k+1) → ℝ => (u, c))
          = (⇑(ContinuousLinearMap.inl ℝ (Fin (k+1) → ℝ) ℝ))
            + (fun _ => ((0 : Fin (k+1) → ℝ), c)) := by
        funext u; ext <;> simp
      rw [show (fun u => Φ (u, c)) = Φ ∘ (fun u : Fin (k+1) → ℝ => (u, c)) from rfl, harg]
      exact hΦcd.comp (((ContinuousLinearMap.inl ℝ (Fin (k+1) → ℝ) ℝ).contDiff).add contDiff_const)))
    rintro v ⟨p, hp, hpv⟩
    obtain ⟨z, hz, rfl⟩ := hp
    have hΛz : Λ (Sig z) = (g z i, Φ (Sig z)) := rfl
    have hpv2 : (g z i, Φ (Sig z)) = (c, v) := by rw [← hΛz]; exact hpv
    have hpc : g z i = c := congrArg Prod.fst hpv2
    have hpv' : Φ (Sig z) = v := congrArg Prod.snd hpv2
    have hzball : z ∈ Metric.ball x₀ (ρ/2) := by
      rw [Metric.mem_ball]
      have h := Metric.mem_closedBall.mp hz.1
      linarith [hρpos]
    refine ⟨crj j z, ?_, ?_⟩
    · rw [Set.mem_setOf_eq, ← hpc]
      intro hsurj
      exact hz.2 ((hcrit z hzball).mpr hsurj)
    · rw [← hpv']
      show Φ (crj j z, c) = Φ (Sig z)
      rw [← hpc]
  have hfinal : ∀ z ∈ Metric.ball x₀ δ ∩ {z | ¬ Function.Surjective (fderiv ℝ g z)},
      g z ∈ (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) i).symm) '' T := by
    rintro z ⟨hzball, hzcrit⟩
    have hzcb : z ∈ Metric.closedBall x₀ (ρ/2) := by
      rw [Metric.mem_closedBall]
      have := Metric.mem_ball.mp hzball
      linarith [hδlt, hρpos]
    have hzcrit' : Sig z ∈ Sig '' Scrit := by
      refine Set.mem_image_of_mem _ ⟨?_, hzcrit⟩
      rw [Metric.mem_closedBall]
      have := Metric.mem_ball.mp hzball
      linarith [hδlt]
    refine ⟨(g z i, Φ (Sig z)), ?_, ?_⟩
    · rw [hTdef]
      exact ⟨Sig z, hzcrit', rfl⟩
    · rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
      show Fin.insertNth (α := fun _ => ℝ) i (g z i) (Φ (Sig z)) = g z
      rw [← insCLM_apply]
      exact (hgΘSig z hzcb).symm
  have hnullT : volume ((⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) i).symm) '' T) = 0 := by
    rw [image_null_iff_of_measurePreserving
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) i).symm)
      (volume_preserving_piFinSuccAbove (fun _ : Fin (k+1) => ℝ) i).symm T]
    exact hTnull
  exact measure_mono_null (fun y hy => by
    obtain ⟨z, hz, rfl⟩ := hy
    exact hfinal z hz) hnullT

theorem reduction_step {n : ℕ} (hn : 2 ≤ n) (g : (Fin n → ℝ) → (Fin (n-1) → ℝ))
    (hg : ContDiff ℝ 2 g) (x₀ : Fin n → ℝ) (hx₀ : ¬ Function.Surjective (fderiv ℝ g x₀))
    (hne : fderiv ℝ g x₀ ≠ 0)
    (IH : ∀ k, k < n → ∀ (h : (Fin k → ℝ) → (Fin (k-1) → ℝ)), ContDiff ℝ 2 h →
        MeasureTheory.volume (h '' {z | ¬ Function.Surjective (fderiv ℝ h z)}) = 0) :
    ∃ δ > 0, MeasureTheory.volume (g '' (Metric.ball x₀ δ ∩ {z | ¬ Function.Surjective (fderiv ℝ g z)})) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  exact reduction_step_aux g hg x₀ hx₀ hne IH

end Work.WilE2.RegVals
