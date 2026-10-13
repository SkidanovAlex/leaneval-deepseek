import Mathlib
import Submission.Work.WilE2.RegVals.Basic
import Submission.Work.WilE2.RegVals.reg_aux
import Submission.Work.WilE2.RegVals.isClosed_setOf_not_surjective
import Submission.Work.WilE9G.Sard.rankDefs
import Submission.Work.WilE9G.Sard.exists_coord_of_ne_zero
import Submission.Work.WilE9G.Sard.dchart_bijective
import Submission.Work.WilE9G.Sard.insertNthChart
import Submission.Work.WilE9G.Sard.hasFDerivAt_chart
import Submission.Work.WilE9G.Sard.contDiff_chart
import Submission.Work.WilE9G.Sard.exists_cutoff_supp_infty
open MeasureTheory
open scoped Topology

set_option maxHeartbeats 1600000

noncomputable section

namespace Work.WilE9G.Sard


/-! ## Auxiliary constructions -/

/-- `Fin.insertNth i c v` as a continuous linear map of `(v, c)`. -/
def insL {m : ℕ} (i : Fin (m + 1)) : ((Fin m → ℝ) × ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
  ContinuousLinearMap.pi (fun k : Fin (m + 1) =>
    if h : k = i then ContinuousLinearMap.snd ℝ (Fin m → ℝ) ℝ
    else (ContinuousLinearMap.proj (Classical.choose (Fin.exists_succAbove_eq h))).comp
      (ContinuousLinearMap.fst ℝ (Fin m → ℝ) ℝ))

theorem insL_apply_same {m : ℕ} (i : Fin (m + 1)) (v : Fin m → ℝ) (c : ℝ) :
    insL i (v, c) i = c := by
  rw [insL, ContinuousLinearMap.pi_apply, dif_pos rfl]
  rfl

theorem insL_apply_succAbove {m : ℕ} (i : Fin (m + 1)) (v : Fin m → ℝ) (c : ℝ) (l : Fin m) :
    insL i (v, c) (i.succAbove l) = v l := by
  have hne : i.succAbove l ≠ i := Fin.succAbove_ne i l
  have hc : Classical.choose (Fin.exists_succAbove_eq hne) = l :=
    Fin.succAbove_right_injective (Classical.choose_spec (Fin.exists_succAbove_eq hne))
  rw [insL, ContinuousLinearMap.pi_apply, dif_neg hne]
  show v (Classical.choose (Fin.exists_succAbove_eq hne)) = v l
  rw [hc]

theorem insertNth_eq_insL {m : ℕ} (i : Fin (m + 1)) (v : Fin m → ℝ) (c : ℝ) :
    Fin.insertNth (α := fun _ => ℝ) i c v = insL i (v, c) := by
  funext k
  by_cases hk : k = i
  · subst hk
    rw [Fin.insertNth_apply_same, insL_apply_same]
  · obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hk
    rw [← hl, Fin.insertNth_apply_succAbove, insL_apply_succAbove]

/-- The reassembled map `q ↦ insertNth i q.2 (Φ q)` has the expected derivative. -/
theorem hasFDerivAt_insertNth {d m : ℕ} (i : Fin (m + 1))
    (Φ : ((Fin d → ℝ) × ℝ) → (Fin m → ℝ)) {p : (Fin d → ℝ) × ℝ}
    (hΦ : DifferentiableAt ℝ Φ p) :
    HasFDerivAt (fun q : (Fin d → ℝ) × ℝ => Fin.insertNth (α := fun _ => ℝ) i q.2 (Φ q))
      ((insL i).comp ((fderiv ℝ Φ p).prod (ContinuousLinearMap.snd ℝ (Fin d → ℝ) ℝ))) p := by
  have h1 : (fun q : (Fin d → ℝ) × ℝ => Fin.insertNth (α := fun _ => ℝ) i q.2 (Φ q))
      = (⇑(insL i)) ∘ (fun q : (Fin d → ℝ) × ℝ => (Φ q, q.2)) := by
    funext q
    exact insertNth_eq_insL i (Φ q) q.2
  rw [h1]
  exact (insL i).hasFDerivAt.comp p
    (hΦ.hasFDerivAt.prodMk (ContinuousLinearMap.snd ℝ (Fin d → ℝ) ℝ).hasFDerivAt)

/-- Reindexing along an equality of dimensions transports the critical-nullity hypothesis. -/
theorem critNull_transport {k : ℕ} {n n' m m' : ℕ} (h₁ : n = n') (h₂ : m = m')
    (H : ∀ g : (Fin n → ℝ) → (Fin m → ℝ), ContDiff ℝ k g →
      MeasureTheory.volume (g '' {z | ¬ Function.Surjective (fderiv ℝ g z)}) = 0) :
    ∀ g : (Fin n' → ℝ) → (Fin m' → ℝ), ContDiff ℝ k g →
      MeasureTheory.volume (g '' {z | ¬ Function.Surjective (fderiv ℝ g z)}) = 0 := by
  subst h₁; subst h₂
  exact H

/-! ## The successor-form reduction -/

theorem rankPosReductionAux_succ {d m k : ℕ}
    (f : (Fin (d + 1) → ℝ) → (Fin (m + 1) → ℝ)) (hf : ContDiff ℝ k f) (hk : 1 ≤ k)
    (x₀ : Fin (d + 1) → ℝ) (hpos : fderiv ℝ f x₀ ≠ 0)
    (IH : ∀ g : (Fin d → ℝ) → (Fin m → ℝ), ContDiff ℝ k g →
      MeasureTheory.volume (g '' {z | ¬ Function.Surjective (fderiv ℝ g z)}) = 0) :
    ∃ r : ℝ, 0 < r ∧ MeasureTheory.volume
      (f '' ({z | ¬ Function.Surjective (fderiv ℝ f z)} ∩ Metric.ball x₀ r)) = 0 := by
  classical
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by
    have h1 : (1 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hk
    intro h
    rw [h] at h1
    exact absurd h1 (by norm_num)
  -- ## Step 0: coordinates and the straightening chart
  obtain ⟨i, j, hij⟩ := exists_coord_of_ne_zero (fderiv ℝ f x₀) hpos
  set S : (Fin (d + 1) → ℝ) → ((Fin d → ℝ) × ℝ) := chart f i j with hS
  have hScd : ContDiff ℝ k S := contDiff_chart f i j hf
  have hSdiff : DifferentiableAt ℝ S x₀ := (hScd.contDiffAt).differentiableAt hk0
  have hSderiv : HasFDerivAt S (dchart f i j x₀) x₀ :=
    hasFDerivAt_chart f i j x₀ ((hf.contDiffAt).differentiableAt hk0)
  have hbij : Function.Bijective (dchart f i j x₀) :=
    dchart_bijective (fderiv ℝ f x₀) i j hij
  let e : (Fin (d + 1) → ℝ) ≃L[ℝ] ((Fin d → ℝ) × ℝ) :=
    (LinearEquiv.ofBijective (dchart f i j x₀).toLinearMap hbij).toContinuousLinearEquiv
  have he : (e : (Fin (d + 1) → ℝ) →L[ℝ] ((Fin d → ℝ) × ℝ)) = dchart f i j x₀ := by
    refine ContinuousLinearMap.ext fun v => ?_
    change e v = dchart f i j x₀ v
    rw [show e v = e.toLinearEquiv v from rfl]
    rw [show e.toLinearEquiv
        = LinearEquiv.ofBijective (dchart f i j x₀).toLinearMap hbij from
      LinearEquiv.toLinearEquiv_toContinuousLinearEquiv _]
    rw [LinearEquiv.ofBijective_apply]
    rfl
  have hSderiv' : HasFDerivAt S (e : (Fin (d + 1) → ℝ) →L[ℝ] ((Fin d → ℝ) × ℝ)) x₀ := by
    rw [he]; exact hSderiv
  have hstr : HasStrictFDerivAt S (e : (Fin (d + 1) → ℝ) →L[ℝ] ((Fin d → ℝ) × ℝ)) x₀ :=
    (hScd.contDiffAt).hasStrictFDerivAt' hSderiv' hk0
  let Ω : ((Fin d → ℝ) × ℝ) → (Fin (d + 1) → ℝ) := hstr.localInverse
  have hΩcd : ContDiffAt ℝ k Ω (S x₀) := (hScd.contDiffAt).to_localInverse hSderiv' hk0
  have hΩleft : ∀ᶠ z in 𝓝 x₀, Ω (S z) = z := by
    simpa [Ω] using hstr.eventually_left_inverse
  have hΩright : ∀ᶠ w in 𝓝 (S x₀), S (Ω w) = w := by
    simpa [Ω] using hstr.eventually_right_inverse
  obtain ⟨r₀, hr₀pos, hr₀⟩ : ∃ r > 0, ∀ z, dist z x₀ < r → Ω (S z) = z :=
    Metric.mem_nhds_iff.mp hΩleft
  -- ## Step 1: the chart is submersive near `x₀`
  obtain ⟨uΩ, huΩ, hΩon⟩ : ∃ u ∈ 𝓝 (S x₀), ContDiffOn ℝ k Ω u :=
    hΩcd.contDiffOn (le_refl (k : WithTop ℕ∞)) (fun h => by simpa using h)
  set U' : Set ((Fin d → ℝ) × ℝ) := interior uΩ with hU'def
  have hU'o : IsOpen U' := isOpen_interior
  have hU'mem : S x₀ ∈ U' := mem_interior_iff_mem_nhds.mpr huΩ
  have hΩon' : ContDiffOn ℝ k Ω U' := hΩon.mono interior_subset
  have hΩcd_at : ∀ w ∈ U', ContDiffAt ℝ k Ω w := fun w hw => hΩon'.contDiffAt (hU'o.mem_nhds hw)
  have hΩdiff_at : ∀ w ∈ U', DifferentiableAt ℝ Ω w := fun w hw =>
    (hΩon'.differentiableOn hk0 w hw).differentiableAt (hU'o.mem_nhds hw)
  obtain ⟨r₁, hr₁pos, hr₁⟩ : ∃ r > 0, Metric.ball (S x₀) r ⊆ U' :=
    Metric.mem_nhds_iff.mp (hU'o.mem_nhds hU'mem)
  obtain ⟨r₂, hr₂pos, hr₂⟩ : ∃ r > 0, Metric.ball (S x₀) r ⊆ {w | S (Ω w) = w} :=
    Metric.mem_nhds_iff.mp hΩright
  obtain ⟨r₃, hr₃pos, hr₃⟩ : ∃ r > 0, ∀ z, dist z x₀ < r →
      dist (S z) (S x₀) < min r₁ r₂ :=
    Metric.continuousAt_iff.mp (hScd.contDiffAt).continuousAt (min r₁ r₂)
      (lt_min hr₁pos hr₂pos)
  have hsurjS : ∀ z, dist z x₀ < min r₀ r₃ → Function.Surjective (fderiv ℝ S z) := by
    intro z hz
    have hz₀ : dist z x₀ < r₀ := lt_of_lt_of_le hz (min_le_left _ _)
    have hz₃ : dist z x₀ < r₃ := lt_of_lt_of_le hz (min_le_right _ _)
    have hz₁ : dist (S z) (S x₀) < r₁ := lt_of_lt_of_le (hr₃ z hz₃) (min_le_left _ _)
    have hz₂ : dist (S z) (S x₀) < r₂ := lt_of_lt_of_le (hr₃ z hz₃) (min_le_right _ _)
    have hΩz : Ω (S z) = z := hr₀ z hz₀
    have hΩdiff : DifferentiableAt ℝ Ω (S z) := hΩdiff_at _ (hr₁ hz₁)
    have hSdiffΩ : DifferentiableAt ℝ S (Ω (S z)) := by
      rw [hΩz]; exact (hScd.contDiffAt).differentiableAt hk0
    have hEq : (S ∘ Ω) =ᶠ[𝓝 (S z)] id := by
      refine Filter.mem_of_superset
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball.mpr hz₂)) ?_
      intro w hw
      simp only [Function.comp_apply, id_eq]
      exact hr₂ hw
    have hcomp : (fderiv ℝ S (Ω (S z))).comp (fderiv ℝ Ω (S z))
        = ContinuousLinearMap.id ℝ ((Fin d → ℝ) × ℝ) := by
      rw [← fderiv_comp (S z) hSdiffΩ hΩdiff, hEq.fderiv_eq, fderiv_id]
    rw [hΩz] at hcomp
    intro v
    refine ⟨(fderiv ℝ Ω (S z)) v, ?_⟩
    have hh := congrFun (congrArg DFunLike.coe hcomp) v
    simpa using hh
  -- ## Step 2: the slice map and a smooth cut-off
  obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ : ∃ ρ > 0,
      Metric.ball x₀ ρ ⊆ S ⁻¹' (Metric.ball (S x₀) r₁) :=
    Metric.mem_nhds_iff.mp ((hScd.continuous.continuousAt).preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₁pos)))
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
  set Kc : Set ((Fin d → ℝ) × ℝ) := S '' Metric.closedBall x₀ (ρ / 2) with hKcdef
  have hKccont : Continuous S := hScd.continuous
  have hKccomp : IsCompact Kc := (isCompact_closedBall x₀ (ρ / 2)).image hKccont
  have hKcW : Kc ⊆ Metric.ball (S x₀) r₁ := by
    rintro p ⟨z, hz, rfl⟩
    exact hρ₀ (Metric.mem_ball.mpr (by
      have h := Metric.mem_closedBall.mp hz
      linarith))
  obtain ⟨V, hVo, hKV, hVW⟩ := Work.WilE2.RegVals.exists_open_between hKccomp Metric.isOpen_ball hKcW
  obtain ⟨χ, hχcd, hU, hχsupp⟩ := exists_cutoff_supp_infty hKccomp hVo hKV
  obtain ⟨U, hUo, hKU, hχU⟩ := hU
  have hχ1 : ∀ x ∈ Kc, χ =ᶠ[𝓝 x] 1 := fun x hx =>
    Filter.mem_of_superset (hUo.mem_nhds (hKU hx)) (fun y hy => hχU y hy)
  set φ : ((Fin d → ℝ) × ℝ) → (Fin m → ℝ) := fun p l => f (Ω p) (i.succAbove l) with hφdef
  have hφcd : ∀ p ∈ V, ContDiffAt ℝ k φ p := by
    intro p hp
    have hpU' : p ∈ U' := hr₁ (hVW (subset_closure hp))
    have h1 : ContDiffAt ℝ k Ω p := hΩcd_at p hpU'
    refine contDiffAt_pi.mpr fun l => ?_
    rw [hφdef]
    exact (((ContinuousLinearMap.proj (i.succAbove l)).contDiff).contDiffAt).comp p
      (hf.contDiffAt.comp p h1)
  set Φ : ((Fin d → ℝ) × ℝ) → (Fin m → ℝ) := fun p => χ p • φ p with hΦdef
  have hΦcd : ContDiff ℝ k Φ := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ V
    · exact ((hχcd.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt).smul (hφcd p hp)
    · have hp' : p ∉ tsupport χ := fun h => hp (hχsupp h)
      have hχ0 : χ =ᶠ[𝓝 p] 0 := by
        have hop : (tsupport χ)ᶜ ∈ 𝓝 p := (isClosed_tsupport χ).isOpen_compl.mem_nhds hp'
        filter_upwards [hop] with q hq
        exact image_eq_zero_of_notMem_tsupport hq
      have hsm : (fun q => χ q • φ q) =ᶠ[𝓝 p] (fun _ => (0 : Fin m → ℝ)) := by
        filter_upwards [hχ0] with q hq
        rw [hq]; simp
      rw [hΦdef]
      exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hsm
  have hΦeq : ∀ p ∈ Kc, Φ =ᶠ[𝓝 p] φ := by
    intro p hp
    filter_upwards [hχ1 p hp] with q hq
    show χ q • φ q = φ q
    rw [show χ q = 1 by simpa using hq, one_smul]
  -- ## Step 3: `f` is the reassembly of `Φ` along the chart
  have hf_S : ∀ z ∈ Metric.closedBall x₀ (ρ / 2),
      f z = Fin.insertNth (α := fun _ => ℝ) i (f z i) (Φ (S z)) := by
    intro z hz
    have hzK : S z ∈ Kc := Set.mem_image_of_mem S hz
    have hΦz : Φ (S z) = φ (S z) := (hΦeq _ hzK).eq_of_nhds
    have hΩz : Ω (S z) = z := hr₀ z (Metric.mem_ball.mpr (by
      have h := Metric.mem_closedBall.mp hz
      linarith))
    have h1 : φ (S z) = fun l => f z (i.succAbove l) := by
      funext l
      simp only [hφdef]
      rw [hΩz]
    rw [hΦz, h1]
    exact (Work.WilE2.RegVals.insertNth_self i (f z)).symm
  -- ## Step 4: the criticality transfer
  set Ψ : ((Fin d → ℝ) × ℝ) → (Fin (m + 1) → ℝ) :=
    fun q => Fin.insertNth (α := fun _ => ℝ) i q.2 (Φ q) with hΨdef
  have hΨdiff : ∀ p, DifferentiableAt ℝ Φ p → DifferentiableAt ℝ Ψ p := fun p hp =>
    (hasFDerivAt_insertNth i Φ hp).differentiableAt
  have hcrit : ∀ z ∈ Metric.ball x₀ (ρ / 2),
      Function.Surjective (fderiv ℝ f z) ↔
        Function.Surjective (fderiv ℝ (fun u : Fin d → ℝ => Φ (u, f z i)) (crj j z)) := by
    intro z hz
    have hzρ : dist z x₀ < min r₀ r₃ := by
      have h1 : dist z x₀ < ρ / 2 := Metric.mem_ball.mp hz
      have h2 : ρ / 2 < min r₀ r₃ := lt_min (by linarith) (by linarith)
      linarith
    have hagree : f =ᶠ[𝓝 z] Ψ ∘ S := by
      refine Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) ?_
      intro y hy
      simp only [Function.comp_apply, hΨdef]
      exact hf_S y (Metric.ball_subset_closedBall hy)
    have hSzy : DifferentiableAt ℝ S z := (hScd.contDiffAt).differentiableAt hk0
    have hΨy : DifferentiableAt ℝ Ψ (S z) :=
      hΨdiff _ (hΦcd.contDiffAt.differentiableAt hk0)
    have hchain : fderiv ℝ f z = (fderiv ℝ Ψ (S z)).comp (fderiv ℝ S z) := by
      rw [hagree.fderiv_eq, fderiv_comp z hΨy hSzy]
    have hstep : Function.Surjective (fderiv ℝ f z) ↔ Function.Surjective (fderiv ℝ Ψ (S z)) := by
      rw [hchain]
      exact ⟨fun h => Function.Surjective.of_comp h, fun h => h.comp (hsurjS z hzρ)⟩
    have hslice := surjectiveFderivInsertNthIffAux i Φ (S z)
      (hΦcd.contDiffAt.differentiableAt hk0)
    have h1 : (S z).1 = crj j z := rfl
    have h2 : (S z).2 = f z i := rfl
    rw [h1, h2] at hslice
    exact hstep.trans hslice
  -- ## Step 5: the null set of critical values
  have hcritClosed : IsClosed {z : Fin (d + 1) → ℝ | ¬ Function.Surjective (fderiv ℝ f z)} :=
    Work.WilE2.RegVals.isClosed_setOf_not_surjective.preimage (hf.continuous_fderiv hk0)
  set Scrit : Set (Fin (d + 1) → ℝ) :=
    Metric.closedBall x₀ (ρ / 4) ∩ {z | ¬ Function.Surjective (fderiv ℝ f z)} with hScritdef
  have hScritcomp : IsCompact Scrit :=
    (isCompact_closedBall x₀ (ρ / 4)).inter_right hcritClosed
  set Λ : ((Fin d → ℝ) × ℝ) → (ℝ × (Fin m → ℝ)) := fun p => (p.2, Φ p) with hΛdef
  have hΛcont : Continuous Λ := continuous_snd.prodMk hΦcd.continuous
  set Tset : Set (ℝ × (Fin m → ℝ)) := Λ '' (S '' Scrit) with hTdef
  have hTmeas : MeasurableSet Tset := ((hScritcomp.image hKccont).image hΛcont).measurableSet
  have hΦslice_cd : ∀ c : ℝ, ContDiff ℝ k (fun u : Fin d → ℝ => Φ (u, c)) := by
    intro c
    have harg : (fun u : Fin d → ℝ => (u, c))
        = (⇑(ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ))
          + (fun _ => ((0 : Fin d → ℝ), c)) := by
      funext u; ext <;> simp
    rw [show (fun u : Fin d → ℝ => Φ (u, c))
        = Φ ∘ (fun u : Fin d → ℝ => (u, c)) from rfl, harg]
    exact hΦcd.comp (((ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ).contDiff).add contDiff_const)
  have hTnull : volume Tset = 0 := by
    refine Work.WilE2.RegVals.volume_eq_zero_of_slices_null_real hTmeas fun c => ?_
    refine measure_mono_null ?_ (IH (fun u : Fin d → ℝ => Φ (u, c)) (hΦslice_cd c))
    rintro v hv
    simp only [Set.mem_setOf_eq] at hv
    obtain ⟨p₀, ⟨z, hz, rfl⟩, hp₀⟩ := hv
    have hpc : f z i = c := congrArg Prod.fst hp₀
    have hpv : Φ (S z) = v := congrArg Prod.snd hp₀
    refine ⟨crj j z, ?_, ?_⟩
    · rw [Set.mem_setOf_eq]
      intro hsurj
      have hsurj' : Function.Surjective
          (fderiv ℝ (fun u : Fin d → ℝ => Φ (u, f z i)) (crj j z)) := by
        rw [hpc]; exact hsurj
      exact hz.2 ((hcrit z (Metric.mem_ball.mpr (by
        have h := Metric.mem_closedBall.mp hz.1
        linarith))).mpr hsurj')
    · show Φ (crj j z, c) = v
      rw [← hpc]
      exact hpv
  -- ## Step 6: transfer back along the measure preserving rearrangement
  set δ : ℝ := min r₀ (min r₃ (ρ / 4)) / 2 with hδdef
  have hminpos : 0 < min r₀ (min r₃ (ρ / 4)) :=
    lt_min hr₀pos (lt_min hr₃pos (by linarith))
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδρ : δ < ρ / 4 := by
    rw [hδdef]
    have h1 : min r₀ (min r₃ (ρ / 4)) ≤ ρ / 4 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hfinal : ∀ z ∈ Metric.ball x₀ δ ∩ {z | ¬ Function.Surjective (fderiv ℝ f z)},
      f z ∈ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm '' Tset := by
    intro z hz
    have hzcrit : ¬ Function.Surjective (fderiv ℝ f z) := hz.2
    have hzcb : z ∈ Metric.closedBall x₀ (ρ / 2) := by
      rw [Metric.mem_closedBall]
      have h := Metric.mem_ball.mp hz.1
      linarith
    refine ⟨(f z i, Φ (S z)), ?_, ?_⟩
    · rw [hTdef]
      refine ⟨S z, ⟨z, ⟨?_, hzcrit⟩, rfl⟩, rfl⟩
      rw [Metric.mem_closedBall]
      have h := Metric.mem_ball.mp hz.1
      linarith
    · rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact (hf_S z hzcb).symm
  refine ⟨δ, hδpos, ?_⟩
  have hnull : volume
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm '' Tset) = 0 := by
    rw [Work.WilE2.image_null_iff_of_measurePreserving
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm)
      (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm Tset]
    exact hTnull
  refine measure_mono_null ?_ hnull
  rintro y ⟨z, ⟨hzcrit, hzball⟩, rfl⟩
  exact hfinal z ⟨hzball, hzcrit⟩

/-! ## The general statement from the successor form -/

theorem rankPosReductionAux {D T k : ℕ} (hD : 1 ≤ D) (hT : 1 ≤ T)
    (f : (Fin D → ℝ) → (Fin T → ℝ)) (hf : ContDiff ℝ k f) (hk : 1 ≤ k)
    (x₀ : Fin D → ℝ) (hpos : fderiv ℝ f x₀ ≠ 0)
    (IH : ∀ g : (Fin (D - 1) → ℝ) → (Fin (T - 1) → ℝ), ContDiff ℝ k g →
      MeasureTheory.volume (g '' {z | ¬ Function.Surjective (fderiv ℝ g z)}) = 0) :
    ∃ r : ℝ, 0 < r ∧ MeasureTheory.volume
      (f '' ({z | ¬ Function.Surjective (fderiv ℝ f z)} ∩ Metric.ball x₀ r)) = 0 := by
  obtain ⟨d, hd⟩ : ∃ d, D = d + 1 := ⟨D - 1, (Nat.sub_add_cancel hD).symm⟩
  obtain ⟨m, hm⟩ : ∃ m, T = m + 1 := ⟨T - 1, (Nat.sub_add_cancel hT).symm⟩
  subst hd
  subst hm
  exact rankPosReductionAux_succ f hf hk x₀ hpos
    (critNull_transport (Nat.add_sub_cancel d 1) (Nat.add_sub_cancel m 1) IH)

end Work.WilE9G.Sard
