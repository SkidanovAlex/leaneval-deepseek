import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.BasinSC.defs
import Submission.Work.Horn.fiber_finite
import Submission.Work.Horn.localBiholo_source_subset
import Submission.Work.BasinSC.StepOneCrit.Auxiliary
import Submission.Work.BasinSC.StepOneCrit.uniformization_to_ball
import Submission.Work.Horn.exists_polynomial_of_proper_entire
import Submission.Lib.Unif2.Commons.Analysis.Complex.exists_two_preimages_near_of_deriv_eq_zero
import Submission.Work.Horn.exists_root_homeo_of_singleCritVal
import Submission.Work.Horn.existsUnique_root_of_roots_derivative

/-!
# One critical value forces one critical point (Riemann–Hurwitz/χ count)

`f : B → B` proper holomorphic self-map of the simply connected plane domain `B`, onto, with all
critical values equal to a single value `v`; if `f` has a critical point at all it has exactly one.

See `Notes_unique_crit.md` for the plan of the two cases.
-/

namespace Work.Horn

open Set Filter Topology

noncomputable section

/-! ## A surjective holomorphic map is nowhere locally constant -/

lemma not_eventuallyEq_const_of_surj {B : Set ℂ} {f : ℂ → ℂ}
    (hBopen : IsOpen B) (hBconn : IsConnected B) (hf : DifferentiableOn ℂ f B)
    (hsurj : B ⊆ f '' B) {c : ℂ} (hc : c ∈ B) :
    ¬ ∀ᶠ z in nhds c, f z = f c := by
  intro h
  have heq : Set.EqOn f (fun _ => f c) B :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hf.analyticOnNhd hBopen)
      analyticOnNhd_const hBconn.isPreconnected hc h
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hBopen c hc
  have hc₂B : c + (ε / 2 : ℝ) ∈ B := by
    apply hεsub
    rw [Metric.mem_ball, dist_eq_norm]
    have hε' : ‖((ε / 2 : ℝ) : ℂ)‖ < ε := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < ε/2)]
      linarith
    simpa using hε'
  have hc₂ne : c + (ε / 2 : ℝ) ≠ c := by
    intro hh
    have hsub : c + ((ε / 2 : ℝ) : ℂ) - c = 0 := by rw [hh, sub_self]
    have hzero : ((ε / 2 : ℝ) : ℂ) = 0 := by simpa using hsub
    have hzero' : (ε / 2 : ℝ) = 0 := by exact_mod_cast hzero
    linarith
  obtain ⟨z, hzB, hzc⟩ := hsurj hc
  obtain ⟨z', hz'B, hz'c⟩ := hsurj hc₂B
  have h1 : c + (ε / 2 : ℝ) = f c := by
    calc c + (ε / 2 : ℝ) = f z' := hz'c.symm
      _ = f c := heq hz'B
  have h2 : c = f c := by
    calc c = f z := hzc.symm
      _ = f c := heq hzB
  exact hc₂ne (by rw [h1]; exact h2.symm)

/-! ## The analytic core of the `B ≅ 𝔻` case -/

/-! ## Case `B = ℂ`: the polynomial count -/

/-- If `P` represents `f` and every critical point of `f` maps to `v`, while `f` is not
constantly `v`, then the fibre of `v` has one point. -/
lemma ncard_fiber_eq_one_of_polynomial_rep {f : ℂ → ℂ} {P : Polynomial ℂ}
    (hPval : ∀ z : ℂ, P.eval z = f z) {v : ℂ}
    (hv : ∀ z : ℂ, deriv f z = 0 → f z = v) (hne : ∃ z : ℂ, f z ≠ v) :
    (f ⁻¹' {v}).ncard = 1 := by
  set Q : Polynomial ℂ := P - Polynomial.C v with hQdef
  have hQval : ∀ z : ℂ, Q.eval z = f z - v := by
    intro z
    rw [hQdef]
    simp [hPval, Polynomial.eval_sub, Polynomial.eval_C]
  have hQne : Q ≠ 0 := by
    intro h0
    obtain ⟨z, hz⟩ := hne
    have h1 : Q.eval z = 0 := by rw [h0]; simp
    rw [hQval, sub_eq_zero] at h1
    exact hz h1
  have hroot : ∀ z : ℂ, (Polynomial.derivative Q).IsRoot z → Q.IsRoot z := by
    intro z hz
    rw [Polynomial.IsRoot.def] at hz ⊢
    have hderiv : deriv (fun w : ℂ => Q.eval w) z = 0 := by
      rw [Polynomial.deriv]; exact hz
    have h2 : deriv (fun w : ℂ => f w - v) z = 0 := by
      rw [show (fun w : ℂ => f w - v) = (fun w : ℂ => Q.eval w) from funext fun w => (hQval w).symm]
      exact hderiv
    have h3 : deriv f z = 0 := by
      rw [deriv_sub_const] at h2
      exact h2
    rw [hQval, hv z h3, sub_self]
  obtain ⟨z₀, hz₀, huniq⟩ :=
    existsUnique_root_of_roots_derivative (P := Q) hQne hroot
  have hset : f ⁻¹' {v} = {z₀} := by
    ext z
    constructor
    · intro hz
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hz
      have h1 : Q.IsRoot z := by
        rw [Polynomial.IsRoot.def, hQval, hz, sub_self]
      exact huniq z h1
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      have h1 : Q.eval z₀ = 0 := hz₀
      rw [hQval, sub_eq_zero] at h1
      exact h1
  rw [hset, Set.ncard_singleton]

/-- **Core of the uniformized case.** -/
lemma ncard_fiber_eq_one_of_root_homeo {B : Set ℂ} {f : ℂ → ℂ} {v : ℂ} {φ : ℂ → ℂ}
    (F Z : Set ℂ) (hFdef : F = B ∩ f ⁻¹' {v}) (hZdef : Z = B \ F)
    (hBopen : IsOpen B) (hBconn : IsConnected B) (hf : DifferentiableOn ℂ f B)
    (hmap : Set.MapsTo f B B) (hsurj : B ⊆ f '' B)
    (hvB : v ∈ B) (hcritval : ∀ z ∈ B, deriv f z = 0 → f z = v)
    (hFfin : F.Finite)
    (hφ0 : φ v = 0) (hφne : ∀ z ∈ B, z ≠ v → φ z ≠ 0)
    (hφana : ∀ z ∈ B, AnalyticAt ℂ φ z)
    (hφsurj : ∀ w : ℂ, ‖w‖ < 1 → ∃ z ∈ B, φ z = w)
    (d : ℕ) (hd : 0 < d)
    (ψ₂ : ↥Z ≃ₜ ↥Work.BasinSC.puncturedDisc)
    (hpow : ∀ z : ↥Z, (ψ₂ z : ℂ) ^ d = φ (f z.1)) :
    F.ncard = 1 := by
  classical
  have hmemF : ∀ z : ℂ, z ∈ F ↔ z ∈ B ∧ f z = v := by
    intro z; rw [hFdef]; simp
  have hmemZ : ∀ z : ℂ, z ∈ Z ↔ z ∈ B ∧ f z ≠ v := by
    intro z
    rw [hZdef, Set.mem_sdiff, hmemF]
    constructor
    · rintro ⟨hzB, hzF⟩
      exact ⟨hzB, fun h => hzF ⟨hzB, h⟩⟩
    · rintro ⟨hzB, hzv⟩
      exact ⟨hzB, fun h => hzv h.2⟩
  have hZopen : IsOpen Z := by rw [hZdef]; exact hBopen.sdiff hFfin.isClosed
  let Ψ : ℂ → ℂ := fun z => if h : z ∈ Z then ((ψ₂ ⟨z, h⟩ : ↥Work.BasinSC.puncturedDisc) : ℂ) else 0
  have hΨval : ∀ z (hz : z ∈ Z), Ψ z = ((ψ₂ ⟨z, hz⟩ : ↥Work.BasinSC.puncturedDisc) : ℂ) :=
    fun z hz => dite_eq_left hz
  have hΨzero : ∀ z ∉ Z, Ψ z = 0 := fun z hz => dite_eq_right hz
  have hpowZ : ∀ z ∈ Z, (Ψ z) ^ d = φ (f z) := by
    intro z hz
    rw [hΨval z hz]
    exact hpow ⟨z, hz⟩
  have hpowB : ∀ z ∈ B, (Ψ z) ^ d = φ (f z) := by
    intro z hzB
    by_cases hz : z ∈ Z
    · exact hpowZ z hz
    · have hzv : f z = v := by
        by_contra hzv
        exact hz ((hmemZ z).mpr ⟨hzB, hzv⟩)
      rw [hΨzero z hz, hzv, hφ0, zero_pow hd.ne']
  have hΨne : ∀ z ∈ Z, Ψ z ≠ 0 := by
    intro z hz
    rw [hΨval z hz]
    exact (ψ₂ ⟨z, hz⟩).2.1
  have hΨcont : ContinuousOn Ψ Z := by
    have h1 : Continuous (fun z : ↥Z => ((ψ₂ z : ↥Work.BasinSC.puncturedDisc) : ℂ)) :=
      continuous_subtype_val.comp ψ₂.continuous
    rw [continuousOn_iff_continuous_domRestrict]
    rw [show Z.domRestrict Ψ = (fun z : ↥Z =>
      ((ψ₂ z : ↥Work.BasinSC.puncturedDisc) : ℂ)) from funext fun z => hΨval z.1 z.2]
    exact h1
  have hanZ : ∀ z ∈ Z, AnalyticAt ℂ Ψ z := by
    intro z hz
    refine Work.BasinSC.StepOneCrit.analyticAt_of_pow_eq_of_continuousAt
      (q := fun w : ℂ => φ (f w)) hd ?_ ?_ ?_ ?_
    · have hzf : AnalyticAt ℂ (fun w : ℂ => φ (f w)) z :=
        AnalyticAt.comp (g := φ) (f := f) (x := z)
          (hφana (f z) (hmap ((hmemZ z).mp hz).1))
          (hf.analyticAt (hBopen.mem_nhds ((hmemZ z).mp hz).1))
      exact hzf
    · exact hφne (f z) (hmap ((hmemZ z).mp hz).1) (((hmemZ z).mp hz).2)
    · exact hΨcont.continuousAt (hZopen.mem_nhds hz)
    · filter_upwards [hZopen.mem_nhds hz] with w hw
      exact hpowZ w hw
  have hanB : ∀ z ∈ B, AnalyticAt ℂ Ψ z := by
    intro z hzB
    by_cases hz : z ∈ Z
    · exact hanZ z hz
    · have hzv : f z = v := by
        by_contra hzv
        exact hz ((hmemZ z).mpr ⟨hzB, hzv⟩)
      have hΨz : Ψ z = 0 := hΨzero z hz
      have hφfv : φ (f z) = 0 := by rw [hzv, hφ0]
      obtain ⟨δ, hδpos, hδF⟩ := Metric.isOpen_iff.mp
        ((hFfin.subset Set.sdiff_subset).isClosed).isOpen_compl z (fun h => h.2 rfl)
      have hnorm : ∀ᶠ w in nhds z, ‖Ψ w‖ = ‖φ (f w)‖ ^ ((1 : ℝ) / d) := by
        filter_upwards [hBopen.mem_nhds hzB] with w hwB
        by_cases hwZ : w ∈ Z
        · have h1 : ‖φ (f w)‖ = ‖Ψ w‖ ^ d := by rw [← hpowZ w hwZ, norm_pow]
          rw [h1, ← Real.rpow_natCast (‖Ψ w‖) d, ← Real.rpow_mul (norm_nonneg _), mul_one_div,
            div_self (by exact_mod_cast hd.ne'), Real.rpow_one]
        · have hwv : f w = v := by
            by_contra hwv
            exact hwZ ((hmemZ w).mpr ⟨hwB, hwv⟩)
          rw [hΨzero w hwZ, hwv, hφ0, norm_zero,
            Real.zero_rpow (by positivity : ((1 : ℝ) / d) ≠ 0)]
      have htend : Tendsto (fun w => ‖Ψ w‖) (nhds z) (nhds 0) := by
        have hcontφ : ContinuousAt (fun w : ℂ => φ (f w)) z :=
          ((hφana (f z) (hmap hzB)).continuousAt).comp
            ((hf.differentiableAt (hBopen.mem_nhds hzB)).continuousAt)
        have hc : Tendsto (fun w => ‖φ (f w)‖) (nhds z) (nhds 0) := by
          have h1 : Tendsto (fun w : ℂ => ‖φ (f w)‖) (nhds z) (nhds ‖φ (f z)‖) := hcontφ.norm
          rw [hφfv, norm_zero] at h1
          exact h1
        have hrpow := (Real.continuousAt_rpow_const 0 ((1 : ℝ) / d) (Or.inr (by positivity))).tendsto
        rw [Real.zero_rpow (by positivity : ((1 : ℝ) / d) ≠ 0)] at hrpow
        exact Tendsto.congr' (Filter.EventuallyEq.symm hnorm) (hrpow.comp hc)
      have hcontΨ : ContinuousAt Ψ z := by
        show Tendsto Ψ (nhds z) (nhds (Ψ z))
        rw [hΨz]
        exact tendsto_zero_iff_norm_tendsto_zero.mpr htend
      refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ hcontΨ
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (hBopen.mem_nhds hzB),
        nhdsWithin_le_nhds (Metric.ball_mem_nhds z hδpos)] with w hwne hwB hwball
      have hwz_not : w ∉ ({z} : Set ℂ) := by simpa using hwne
      have hwne' : w ≠ z := fun hwz => hwz_not (Set.mem_singleton_iff.mpr hwz)
      have hwZ : w ∈ Z := by
        refine (hmemZ w).mpr ⟨hwB, fun hwv => ?_⟩
        exact hδF hwball ⟨(hmemF w).mpr ⟨hwB, hwv⟩, fun hzw => hwne' hzw.symm⟩
      exact (hanZ w hwZ).differentiableAt
  have hinj : ∀ z ∈ Z, ∀ z' ∈ Z, Ψ z = Ψ z' → z = z' := by
    intro z hz z' hz' h
    rw [hΨval z hz, hΨval z' hz'] at h
    have h1 : (⟨z, hz⟩ : ↥Z) = ⟨z', hz'⟩ := ψ₂.injective (Subtype.ext h)
    exact congrArg Subtype.val h1
  have hnonlc : ∀ p ∈ F, ¬ ∀ᶠ z in nhds p, Ψ z = Ψ p := by
    intro p hp hcon
    have hpB : p ∈ B := ((hmemF p).mp hp).1
    have hpv : f p = v := ((hmemF p).mp hp).2
    have hfv : ∀ᶠ w in nhds p, f w = v := by
      filter_upwards [hcon, hBopen.mem_nhds hpB] with w hw hwB
      have h1 : φ (f w) = φ (f p) := by
        rw [← hpowB w hwB, ← hpowB p hpB]
        exact congrArg (fun t => t ^ d) hw
      have h2 : φ (f w) = 0 := by rw [h1, hpv, hφ0]
      by_contra hwne
      exact hφne (f w) (hmap hwB) hwne h2
    refine (not_eventuallyEq_const_of_surj hBopen hBconn hf hsurj hpB) ?_
    filter_upwards [hfv] with w hw
    rw [hw, hpv]
  have hmap_ball : ∀ p ∈ F, ∀ U ∈ nhds p, Ψ '' U ∈ nhds (Ψ p) := by
    intro p hp U hU
    rcases AnalyticAt.eventually_constant_or_nhds_le_map_nhds (hanB p ((hmemF p).mp hp).1) with hcon | hle
    · exact absurd hcon (hnonlc p hp)
    · exact hle (Filter.mem_map.mpr (Filter.mem_of_superset hU (fun w hw => ⟨w, hw, rfl⟩)))
  have hderiv : ∀ p ∈ F, deriv Ψ p ≠ 0 := by
    intro p hp h0
    have hpB : p ∈ B := ((hmemF p).mp hp).1
    obtain ⟨ε₁, hε₁, hε₁B⟩ := Metric.isOpen_iff.mp hBopen p hpB
    obtain ⟨ε₂, hε₂, hε₂F⟩ := Metric.isOpen_iff.mp
      ((hFfin.subset Set.sdiff_subset).isClosed).isOpen_compl p (fun h => h.2 rfl)
    set ε : ℝ := min ε₁ ε₂ / 2 with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; exact half_pos (lt_min hε₁ hε₂)
    have hle₁ : ε ≤ ε₁ := by rw [hεdef]; linarith [min_le_left ε₁ ε₂]
    have hle₂ : ε ≤ ε₂ := by rw [hεdef]; linarith [min_le_right ε₁ ε₂]
    obtain ⟨w, hwne, -, a, b, hab, haε, hbε, hΨa, hΨb⟩ :=
      Commons.Analysis.Complex.exists_two_preimages_near_of_deriv_eq_zero
        (hanB p hpB) h0 (hnonlc p hp) hεpos
    have hpF : Ψ p = 0 := hΨzero p (fun h => ((hmemZ p).mp h).2 (((hmemF p).mp hp).2))
    have hwne' : w ≠ 0 := by rw [← hpF]; exact hwne
    have haB : a ∈ B := by
      apply hε₁B
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_lt_of_le haε hle₁
    have hbB : b ∈ B := by
      apply hε₁B
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_lt_of_le hbε hle₁
    have haF : a ∉ F := fun hmem => hε₂F (by
      rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le haε hle₂)
      ⟨hmem, fun hpa => hwne' (by rw [← hΨa, hpa.symm]; exact hpF)⟩
    have hbF : b ∉ F := fun hmem => hε₂F (by
      rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hbε hle₂)
      ⟨hmem, fun hpb => hwne' (by rw [← hΨb, hpb.symm]; exact hpF)⟩
    have haZ : a ∈ Z := (hmemZ a).mpr ⟨haB, fun h => haF ((hmemF a).mpr ⟨haB, h⟩)⟩
    have hbZ : b ∈ Z := (hmemZ b).mpr ⟨hbB, fun h => hbF ((hmemF b).mpr ⟨hbB, h⟩)⟩
    exact hab (hinj a haZ b hbZ (by rw [hΨa, hΨb]))
  have hlocal : ∀ p ∈ F, ∀ ρ > 0, ∃ r > 0, r < ρ ∧ ∃ ε > 0,
      Metric.ball 0 ε ⊆ Ψ '' Metric.ball p r := by
    intro p hp ρ hρ
    have hrpos : 0 < ρ / 2 := by positivity
    have hrlt : ρ / 2 < ρ := by linarith
    have hUtend : Ψ '' Metric.ball p (ρ / 2) ∈ nhds (Ψ p) :=
      hmap_ball p hp _ (Metric.ball_mem_nhds p hrpos)
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hUtend
    refine ⟨ρ / 2, hrpos, hrlt, ε, hε, ?_⟩
    have hpF : Ψ p = 0 := hΨzero p (fun h => ((hmemZ p).mp h).2 (((hmemF p).mp hp).2))
    rwa [hpF] at hεsub
  have hFne : F.Nonempty := by
    obtain ⟨z, hzB, hzv⟩ := hsurj hvB
    exact ⟨z, (hmemF z).mpr ⟨hzB, hzv⟩⟩
  by_contra hnc1
  obtain ⟨p, hpF⟩ := hFne
  have hex2 : ∃ p' ∈ F, p' ≠ p := by
    by_contra hh
    push_neg at hh
    have hFeq : F = {p} := by
      refine Set.Subset.antisymm (fun x hx => by rw [Set.mem_singleton_iff]; exact hh x hx) ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact hpF
    rw [hFeq, Set.ncard_singleton] at hnc1
    exact hnc1 rfl
  obtain ⟨p', hp'F, hpp'⟩ := hex2
  have hdistpos : 0 < dist p p' := dist_pos.mpr (Ne.symm hpp')
  obtain ⟨r, hrpos, hrlt, ε₁, hε₁, hε₁sub⟩ := hlocal p hpF (dist p p' / 3) (by positivity)
  obtain ⟨r', hr'pos, hr'lt, ε₂, hε₂, hε₂sub⟩ := hlocal p' hp'F (dist p p' / 3) (by positivity)
  have hdisj : Disjoint (Metric.ball p r) (Metric.ball p' r') := by
    rw [Set.disjoint_left]
    intro y hy hy'
    rw [Metric.mem_ball] at hy hy'
    have h1 : dist p p' ≤ dist p y + dist y p' := dist_triangle p y p'
    have h2 : dist y p' = dist p' y := dist_comm y p'
    have h3 : dist p p' / 3 + dist p p' / 3 < dist p p' := by linarith [hdistpos]
    linarith [h1, h2, hy, hy', hrlt, hr'lt, h3, dist_nonneg (x := p) (y := p'),
      dist_comm y p, dist_comm y p']
  set ε : ℝ := min (min ε₁ ε₂) 1 / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact half_pos (lt_min (lt_min hε₁ hε₂) one_pos)
  have hεlt1 : ε < ε₁ := by
    rw [hεdef]; linarith [min_le_left (min ε₁ ε₂) 1, min_le_left ε₁ ε₂]
  have hεlt2 : ε < ε₂ := by
    rw [hεdef]; linarith [min_le_left (min ε₁ ε₂) 1, min_le_right ε₁ ε₂]
  have hεlt1' : ε < 1 := by rw [hεdef]; linarith [min_le_right (min ε₁ ε₂) 1]
  have hpowd : (0:ℝ) < ε ^ d := pow_pos hεpos d
  have hεd1 : ε ^ d < ε₁ ^ d := pow_lt_pow_left₀ hεlt1 (le_of_lt hεpos) hd.ne'
  have hεd2 : ε ^ d < ε₂ ^ d := pow_lt_pow_left₀ hεlt2 (le_of_lt hεpos) hd.ne'
  have hεdhalf1 : ε ^ d / 2 < ε₁ ^ d := by linarith
  have hεdhalf2 : ε ^ d / 2 < ε₂ ^ d := by linarith
  have hsmall : ε ^ d / 2 < 1 := by
    have h1 : ε ^ d ≤ ε := by
      cases d with
      | zero => exact absurd hd (lt_irrefl 0)
      | succ k =>
        rw [pow_succ]
        exact mul_le_of_le_one_left (le_of_lt hεpos) (pow_le_one₀ (le_of_lt hεpos) (le_of_lt hεlt1'))
    linarith
  obtain ⟨w, hwB, hφw⟩ := hφsurj ((ε ^ d / 2 : ℝ) : ℂ) (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact hsmall)
  have hwζ : ((ε ^ d / 2 : ℝ) : ℂ) ≠ 0 := by
    have h1 : (0:ℝ) < ε ^ d / 2 := by positivity
    exact_mod_cast h1.ne'
  have hwne : w ≠ v := by
    intro hwv
    rw [hwv, hφ0] at hφw
    exact hwζ hφw.symm
  obtain ⟨z, hzB, hzw⟩ := hsurj hwB
  have hzZ : z ∈ Z := (hmemZ z).mpr ⟨hzB, fun h => hwne (by rw [← hzw, h])⟩
  have hroot : (Ψ z) ^ d = ((ε ^ d / 2 : ℝ) : ℂ) := by
    rw [hpowB z hzB, hzw, hφw]
  have hnormz : ‖Ψ z‖ ^ d = ε ^ d / 2 := by
    rw [← norm_pow, hroot, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hlt1 : ‖Ψ z‖ < ε₁ := by
    have h2 : ‖Ψ z‖ ^ d < ε₁ ^ d := by rw [hnormz]; exact hεdhalf1
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (le_of_lt hε₁) hd.ne').mp h2
  have hlt2 : ‖Ψ z‖ < ε₂ := by
    have h2 : ‖Ψ z‖ ^ d < ε₂ ^ d := by rw [hnormz]; exact hεdhalf2
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (le_of_lt hε₂) hd.ne').mp h2
  have hmem1 : Ψ z ∈ Metric.ball (0:ℂ) ε₁ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hlt1
  have hmem2 : Ψ z ∈ Metric.ball (0:ℂ) ε₂ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hlt2
  obtain ⟨y, hyr, hyΨ⟩ := hε₁sub hmem1
  obtain ⟨y', hy'r', hy'Ψ⟩ := hε₂sub hmem2
  have hyZ : y ∈ Z := by
    by_contra hy
    exact hΨne z hzZ (by rw [← hyΨ, hΨzero y hy])
  have hy'Z : y' ∈ Z := by
    by_contra hy
    exact hΨne z hzZ (by rw [← hy'Ψ, hΨzero y' hy])
  have hzy : z = y := hinj z hzZ y hyZ hyΨ.symm
  have hzy' : z = y' := hinj z hzZ y' hy'Z hy'Ψ.symm
  have hyy' : y = y' := by rw [← hzy, hzy']
  have hy1 : y ∈ Metric.ball p r := hyr
  have hy2 : y ∈ Metric.ball p' r' := by rw [hyy']; exact hy'r'
  exact (Set.disjoint_left.mp hdisj hy1) hy2

/-! ## Uniformization of a proper simply connected plane domain -/

lemma exists_uniformization_model {B : Set ℂ} (hBopen : IsOpen B) (hBne : B.Nonempty)
    (hBsc : SimplyConnectedSpace ↥B) (hBproper : B ≠ Set.univ) {v : ℂ} (hv : v ∈ B) :
    ∃ φ : ℂ → ℂ, φ v = 0 ∧ (∀ z ∈ B, ‖φ z‖ < 1) ∧
      (∀ w : ℂ, ‖w‖ < 1 → ∃ z ∈ B, φ z = w) ∧
      (∀ z ∈ B, z ≠ v → φ z ≠ 0) ∧
      (∀ z ∈ B, AnalyticAt ℂ φ z) ∧ Set.InjOn φ B := by
  obtain ⟨φ, ψ, hφ0, hφmaps, hψmaps, hφψ, hψφ, hφdiff, hψdiff, hφderiv, hψderiv⟩ :=
    Work.BasinSC.StepOneCrit.uniformization_to_ball hBopen hBne hBsc hBproper hv
  have hmem : ∀ w : ℂ, ‖w‖ < 1 ↔ w ∈ Metric.ball (0 : ℂ) 1 := by
    intro w; rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  have hφDO : DifferentiableOn ℂ φ B := fun z hz => (hφdiff z hz).differentiableWithinAt
  refine ⟨φ, hφ0, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    simpa [Metric.mem_ball, dist_eq_norm] using hφmaps z hz
  · intro w hw
    exact ⟨ψ w, hψmaps w ((hmem w).mp hw), hψφ w ((hmem w).mp hw)⟩
  · intro z hz hzv hφz
    refine hzv ?_
    calc z = ψ (φ z) := (hφψ z hz).symm
      _ = ψ (φ v) := by rw [hφz, hφ0]
      _ = v := hφψ v hv
  · intro z hz
    exact hφDO.analyticAt (hBopen.mem_nhds hz)
  · intro z hz w hw hzw
    calc z = ψ (φ z) := (hφψ z hz).symm
      _ = ψ (φ w) := by rw [hzw]
      _ = w := hφψ w hw

/-! ## Assembly -/

theorem unique_critPoint_of_single_critVal {f : ℂ → ℂ} {B : Set ℂ}
    (hBopen : IsOpen B) (hBconn : IsConnected B) (hBsc : SimplyConnectedSpace B)
    (hf : DifferentiableOn ℂ f B) (hmap : Set.MapsTo f B B) (hsurj : B ⊆ f '' B)
    (hproper : ∀ L : Set ℂ, L ⊆ B → IsCompact L → IsCompact (B ∩ f ⁻¹' L))
    (hcritval : ∃ v : ℂ, ∀ z ∈ B, deriv f z = 0 → f z = v)
    (hex : ∃ z ∈ B, deriv f z = 0) :
    ∃! c : ℂ, c ∈ B ∧ deriv f c = 0 := by
  classical
  obtain ⟨v, hv⟩ := hcritval
  have hexkeep : ∃ z ∈ B, deriv f z = 0 := hex
  obtain ⟨z₀, hz₀B, hz₀d⟩ := hex
  have hvB : v ∈ B := by rw [← hv z₀ hz₀B hz₀d]; exact hmap hz₀B
  obtain ⟨c, hcB⟩ := hBconn.nonempty
  have hnc : ∃ c ∈ B, ¬ ∀ᶠ z in nhds c, f z = f c :=
    ⟨c, hcB, not_eventuallyEq_const_of_surj hBopen hBconn hf hsurj hcB⟩
  have hFfin : (B ∩ f ⁻¹' {v}).Finite := by
    obtain ⟨c', hc'B, hnc'⟩ := hnc
    exact fiber_finite hBopen hBconn.isPreconnected hf hc'B hnc' hproper hvB
  have key : (B ∩ f ⁻¹' {v}).ncard = 1 := by
    by_cases hB : B = Set.univ
    · have hproper' : ∀ L : Set ℂ, IsCompact L → IsCompact (f ⁻¹' L) := by
        intro L hL
        have h1 := hproper L (by rw [hB]; exact Set.subset_univ L) hL
        rwa [hB, Set.univ_inter] at h1
      have hf' : DifferentiableOn ℂ f Set.univ := hf.mono (le_of_eq hB.symm)
      obtain ⟨P, hPval⟩ := exists_polynomial_of_proper_entire hf' hproper'
      have hne : ∃ z : ℂ, f z ≠ v := by
        obtain ⟨z, -, hz⟩ := hsurj (by rw [hB]; exact Set.mem_univ (v + 1))
        refine ⟨z, fun hfv => ?_⟩
        rw [hz] at hfv
        exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using congrArg (fun t : ℂ => t - v) hfv)
      have hkey : (Set.univ ∩ f ⁻¹' {v}).ncard = 1 := by
        simpa using ncard_fiber_eq_one_of_polynomial_rep hPval
          (fun z hz => hv z (by rw [hB]; exact Set.mem_univ z) hz) hne
      rw [hB]
      exact hkey
    · obtain ⟨φ, hφ0, hφmaps, hφsurj, hφne, hφana, hφinj⟩ :=
        exists_uniformization_model hBopen ⟨c, hcB⟩ hBsc hB hvB
      obtain ⟨d, hd, ψ₂, hpow⟩ :=
        exists_root_homeo_of_singleCritVal hBopen hBconn hf hmap hsurj hproper hvB hv hnc
          hφ0 hφmaps hφsurj hφne hφana hφinj
      exact ncard_fiber_eq_one_of_root_homeo (B ∩ f ⁻¹' {v}) (B \ (B ∩ f ⁻¹' {v})) rfl rfl
        hBopen hBconn hf hmap hsurj hvB hv hFfin hφ0 hφne hφana hφsurj d hd ψ₂ hpow
  obtain ⟨c₀, hc₀⟩ := Set.ncard_eq_one.mp key
  have hc₀F : c₀ ∈ B ∩ f ⁻¹' {v} := by rw [hc₀]; exact rfl
  have hcrit : deriv f c₀ = 0 := by
    obtain ⟨z, hzB, hzd⟩ := hexkeep
    have hzF : z ∈ B ∩ f ⁻¹' {v} := ⟨hzB, by
      rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hv z hzB hzd⟩
    have hz : z = c₀ := by
      have h2 : z ∈ ({c₀} : Set ℂ) := by rw [← hc₀]; exact hzF
      simpa using h2
    rw [← hz]; exact hzd
  refine ⟨c₀, ⟨hc₀F.1, hcrit⟩, ?_⟩
  intro y hy
  have hyF : y ∈ B ∩ f ⁻¹' {v} := ⟨hy.1, by
    rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hv y hy.1 hy.2⟩
  have h2 : y ∈ ({c₀} : Set ℂ) := by rw [← hc₀]; exact hyF
  simpa using h2

end

end Work.Horn
