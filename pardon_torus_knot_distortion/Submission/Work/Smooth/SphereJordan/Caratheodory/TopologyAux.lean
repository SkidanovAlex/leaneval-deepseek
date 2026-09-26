import Mathlib
import Submission.Work.Smooth.SphereJordan.jsepDefs

/-!
# Elementary topological lemmas for the Carathéodory boundary correspondence
-/

noncomputable section
open Set Metric Filter
open scoped Topology

namespace Work.Smooth.SphereJordan.Caratheodory

/-! ## 1. The diameter of an open set is attained on its frontier -/

/-- **A bounded open set has diameter at most that of its frontier.** -/
theorem diam_le_diam_frontier {U : Set ℂ} (hUo : IsOpen U) (hUb : Bornology.IsBounded U) :
    Metric.diam U ≤ Metric.diam (frontier U) := by
  rcases U.eq_empty_or_nonempty with hUe | hne
  · rw [hUe]; simp
  · obtain ⟨x₀, hx₀⟩ := hne
    have hcl : IsCompact (closure U) := hUb.isCompact_closure
    obtain ⟨p, hp, hpmax⟩ := (hcl.prod hcl).exists_isMaxOn
      ⟨(x₀, x₀), subset_closure hx₀, subset_closure hx₀⟩
      (continuous_fst.dist continuous_snd).continuousOn
    rw [isMaxOn_iff] at hpmax
    have hp1 : p.1 ∈ closure U := hp.1
    have hp2 : p.2 ∈ closure U := hp.2
    have hdiam : Metric.diam U ≤ dist p.1 p.2 :=
      Metric.diam_le_of_forall_dist_le dist_nonneg fun u hu v hv =>
        hpmax (u, v) ⟨subset_closure hu, subset_closure hv⟩
    rcases eq_or_ne p.1 p.2 with hxy | hxy
    · rw [hxy, dist_self] at hdiam
      exact le_trans hdiam (Metric.diam_nonneg)
    · -- neither `p.1` nor `p.2` is an interior point: moving it slightly away from the other
      -- would increase the distance
      have hkey : ∀ z ∈ closure U, z ∉ frontier U → z ∈ U := by
        intro z hzcl hzfr
        rw [hUo.frontier_eq] at hzfr
        by_contra hzU
        exact hzfr ⟨hzcl, hzU⟩
      have hpush : ∀ (u w : ℂ), u ∈ U → u ≠ w → ∃ q ∈ U, dist w u < dist w q := by
        intro u w hu huw
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo u hu
        have hpos : 0 < ‖u - w‖ := by rw [norm_sub_pos_iff]; exact huw
        set δ : ℝ := ε / (2 * ‖u - w‖) with hδ
        have hδpos : 0 < δ := by rw [hδ]; positivity
        set q : ℂ := w + ((1 + δ : ℝ) : ℂ) * (u - w) with hq
        have hd : dist w u = ‖u - w‖ := by rw [dist_eq_norm, norm_sub_rev]
        refine ⟨q, ?_, ?_⟩
        · apply hball
          rw [Metric.mem_ball, dist_eq_norm]
          have h1 : q - u = ((δ : ℝ) : ℂ) * (u - w) := by rw [hq]; push_cast; ring
          rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos, hδ,
            div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * ‖u - w‖)]
          nlinarith [hpos, hε]
        · rw [hd, dist_eq_norm]
          have h1 : w - q = -((((1 + δ : ℝ)) : ℂ) * (u - w)) := by rw [hq]; ring
          rw [h1, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith)]
          nlinarith [hpos, hδpos]
      have hfront1 : p.1 ∈ frontier U := by
        by_contra hcon
        obtain ⟨q, hqmem, hqdist⟩ := hpush p.1 p.2 (hkey p.1 hp1 hcon) hxy
        have h2 := hpmax (q, p.2) ⟨subset_closure hqmem, hp2⟩
        have h3 : dist p.2 q ≤ dist p.2 p.1 := by
          rw [dist_comm p.2 q, dist_comm p.2 p.1]; exact h2
        linarith [h3, hqdist]
      have hfront2 : p.2 ∈ frontier U := by
        by_contra hcon
        obtain ⟨q, hqmem, hqdist⟩ := hpush p.2 p.1 (hkey p.2 hp2 hcon) hxy.symm
        have h2 := hpmax (p.1, q) ⟨hp1, subset_closure hqmem⟩
        linarith [h2, hqdist]
      exact le_trans hdiam
        (Metric.dist_le_diam_of_mem (hcl.isBounded.subset frontier_subset_closure) hfront1 hfront2)

/-! ## 2. The bounded side of a Jordan curve inside `Ω` -/

/-- **If the trace of a Jordan curve `c` avoids the exterior of `Ω = S.V`, then it bounds a subset
of `Ω`.** -/
theorem JSep.V_subset_of_disjoint_trace {γ c : Work.Smooth.Jordan.PlaneCurve} (S : JSep γ)
    (T : JSep c) (h : Disjoint c.trace S.U) : T.V ⊆ S.V := by
  have hcsub : c.trace ⊆ S.Uᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    exact fun hcon => Set.disjoint_left.mp h hz hcon
  have hUnbdd : ¬ Bornology.IsBounded S.U := by
    obtain ⟨R, hR⟩ := S.bounded_V.subset_closedBall (0 : ℂ)
    obtain ⟨R₀, hR₀⟩ := S.nonempty_V
    have hRnn : 0 ≤ R := by
      have h1 := hR hR₀
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      exact le_trans (norm_nonneg R₀) h1
    intro hb
    obtain ⟨R', hR'⟩ := hb.subset_closedBall (0 : ℂ)
    obtain ⟨R₀', hR₀'⟩ := S.nonempty_U
    have hR'nn : 0 ≤ R' := by
      have h1 := hR' hR₀'
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      exact le_trans (norm_nonneg R₀') h1
    set M : ℝ := max R R' + 1 with hM
    have hMpos : 0 < M := by rw [hM]; linarith [le_max_left R R', le_max_right R R']
    have hMnorm : ‖(((M : ℝ)) : ℂ)‖ = M := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos]
    have hclV : closure S.V ⊆ Metric.closedBall (0 : ℂ) R :=
      closure_minimal hR Metric.isClosed_closedBall
    have hMV : (((M : ℝ)) : ℂ) ∉ S.V := by
      intro hcon
      have h1 := hR hcon
      rw [Metric.mem_closedBall, dist_zero_right, hMnorm] at h1
      linarith [le_max_left R R']
    have hMT : (((M : ℝ)) : ℂ) ∉ γ.trace := by
      intro hcon
      have hfr : (((M : ℝ)) : ℂ) ∈ frontier S.V := by rw [S.frontier_V]; exact hcon
      have h1 := hclV (frontier_subset_closure hfr)
      rw [Metric.mem_closedBall, dist_zero_right, hMnorm] at h1
      linarith [le_max_left R R']
    have hMU : (((M : ℝ)) : ℂ) ∈ S.U := by
      have h1 : (((M : ℝ)) : ℂ) ∈ S.U ∪ S.V := by rw [S.union_eq]; exact hMT
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 hMV
    have h3 := hR' hMU
    rw [Metric.mem_closedBall, dist_zero_right, hMnorm] at h3
    linarith [le_max_right R R']
  have hUsub : S.U ⊆ T.U := by
    rcases S.preconn_U.subset_or_subset T.isOpen_U T.isOpen_V T.disjoint_UV
      (fun z hz => by
        rw [T.union_eq, Set.mem_compl_iff]
        exact fun hc => Set.disjoint_left.mp h hc hz) with h' | h'
    · exact h'
    · exact absurd (T.bounded_V.subset h') hUnbdd
  intro p hp
  have hpU : p ∉ S.U := fun hcon => Set.disjoint_left.mp T.disjoint_UV (hUsub hcon) hp
  have hpT : p ∉ γ.trace := by
    intro hpt
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp T.isOpen_V p hp
    have hfr : p ∈ frontier S.U := by rw [S.frontier_U]; exact hpt
    obtain ⟨q, hqU, hqball⟩ :=
      (Metric.mem_closure_iff.mp (frontier_subset_closure hfr)) ε hε
    have hqV : q ∈ T.V := hball (Metric.mem_ball.mpr (by rw [dist_comm]; exact hqball))
    exact Set.disjoint_left.mp T.disjoint_UV (hUsub hqU) hqV
  have hunion : p ∈ S.U ∪ S.V := by
    rw [S.union_eq]; exact hpT
  rcases hunion with h1 | h1
  · exact absurd h1 hpU
  · exact h1

/-! ## 3. Uniformity of a parametrised simple closed curve -/

/-- Reduction of a real number into `[0, 2π)` by an integer multiple of the period. -/
theorem exists_period_reduce {γ : ℝ → ℂ} (hγp : Function.Periodic γ (2 * Real.pi)) (s : ℝ) :
    ∃ k : ℤ, s - 2 * Real.pi * (k : ℝ) ∈ Set.Ico 0 (2 * Real.pi) ∧
      γ (s - 2 * Real.pi * (k : ℝ)) = γ s := by
  have h2π : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  set k : ℤ := ⌊s / (2 * Real.pi)⌋ with hk
  have h1 : ((k : ℝ)) ≤ s / (2 * Real.pi) := by rw [hk]; exact Int.floor_le _
  have h2 : s / (2 * Real.pi) < ((k : ℝ)) + 1 := by rw [hk]; exact Int.lt_floor_add_one _
  have h3 : (2 * Real.pi) * ((k : ℝ)) ≤ s := by
    have := mul_le_mul_of_nonneg_left h1 h2π.le
    rwa [mul_div_cancel₀ _ (ne_of_gt h2π)] at this
  have h4 : s < (2 * Real.pi) * (((k : ℝ)) + 1) := by
    have := mul_lt_mul_of_pos_left h2 h2π
    rwa [mul_div_cancel₀ _ (ne_of_gt h2π)] at this
  refine ⟨k, ?_, ?_⟩
  · rw [Set.mem_Ico]; constructor <;> linarith
  · have hsplit : s = (s - 2 * Real.pi * ((k : ℝ))) + ((k : ℤ) : ℝ) * (2 * Real.pi) := by ring
    conv_rhs => rw [hsplit]
    exact ((hγp.int_mul k) (s - 2 * Real.pi * ((k : ℝ)))).symm

/-- **Injectivity on an interval shorter than the period.** -/
theorem injOn_Icc_of_sub_lt {γ : ℝ → ℂ} (hγp : Function.Periodic γ (2 * Real.pi))
    (hγi : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) {x y : ℝ} (h : y - x < 2 * Real.pi) :
    Set.InjOn γ (Set.Icc x y) := by
  intro s hs t ht hst
  obtain ⟨ks, hs', hsγ⟩ := exists_period_reduce hγp s
  obtain ⟨kt, ht', htγ⟩ := exists_period_reduce hγp t
  have heq : s - 2 * Real.pi * (ks : ℝ) = t - 2 * Real.pi * (kt : ℝ) :=
    hγi hs' ht' (by rw [hsγ, htγ, hst])
  have hdiff : s - t = 2 * Real.pi * (((ks - kt : ℤ)) : ℝ) := by push_cast; linarith
  have habs : |s - t| < 2 * Real.pi := by
    rw [Set.mem_Icc] at hs ht
    rw [abs_lt]; constructor <;> linarith
  have hm0 : (((ks - kt : ℤ)) : ℝ) = 0 := by
    have h2 : |s - t| = 2 * Real.pi * |(((ks - kt : ℤ)) : ℝ)| := by
      rw [hdiff, abs_mul, abs_of_pos Real.two_pi_pos]
    have h3 : |(((ks - kt : ℤ)) : ℝ)| < 1 := by
      have h4 : 2 * Real.pi * |(((ks - kt : ℤ)) : ℝ)| < 2 * Real.pi := by rw [← h2]; exact habs
      by_contra hcon
      rw [not_lt] at hcon
      have h6 : 2 * Real.pi * 1 ≤ 2 * Real.pi * |(((ks - kt : ℤ)) : ℝ)| :=
        mul_le_mul_of_nonneg_left hcon Real.two_pi_pos.le
      rw [mul_one] at h6
      linarith
    have h5 : ks - kt = 0 := by
      have h8 : (((|(ks - kt : ℤ)| : ℤ)) : ℝ) < ((1 : ℤ) : ℝ) := by
        rw [Int.cast_abs]; simpa using h3
      have h7 : |(ks - kt : ℤ)| < 1 := by exact_mod_cast h8
      by_contra hcon
      have h9 : (1 : ℤ) ≤ |ks - kt| := Int.one_le_abs hcon
      linarith
    exact_mod_cast h5
  exact sub_eq_zero.mp (by rw [hdiff, hm0, mul_zero])

/-- **Nearby points of a simple closed curve are joined by a short simple sub-arc.** -/
theorem exists_short_arc {γ : ℝ → ℂ} (hγc : Continuous γ) (hγp : Function.Periodic γ (2 * Real.pi))
    (hγi : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a ∈ Set.range γ, ∀ b ∈ Set.range γ, a ≠ b → ‖a - b‖ < δ →
      ∃ x y : ℝ, x < y ∧ Set.InjOn γ (Set.Icc x y) ∧
        Metric.diam (γ '' Set.Icc x y) ≤ ε ∧
        ((γ x = a ∧ γ y = b) ∨ (γ x = b ∧ γ y = a)) := by
  have h2π : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  obtain ⟨η₀, hη₀pos, hη₀⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc (a := (0 : ℝ)) (b := 4 * Real.pi)).uniformContinuousOn_of_continuous
      hγc.continuousOn) (ε / 2) (by linarith)
  set η : ℝ := min (η₀ / 2) 1 with hηdef
  have hηpos : 0 < η := lt_min (by linarith) one_pos
  have hηle1 : η ≤ 1 := min_le_right _ _
  have hηlt : η < η₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  -- a short interval inside `[0, 4π]` has small image diameter
  have hdiam : ∀ x y : ℝ, 0 ≤ x → y ≤ 4 * Real.pi → y - x ≤ η →
      Metric.diam (γ '' Set.Icc x y) ≤ ε := by
    intro x y hx hy hxy
    refine Metric.diam_le_of_forall_dist_le (le_of_lt hε) fun u hu v hv => ?_
    obtain ⟨s, hs, rfl⟩ := hu
    obtain ⟨t, ht, rfl⟩ := hv
    have hs1 : s ∈ Set.Icc (0 : ℝ) (4 * Real.pi) := ⟨le_trans hx hs.1, le_trans hs.2 hy⟩
    have ht1 : t ∈ Set.Icc (0 : ℝ) (4 * Real.pi) := ⟨le_trans hx ht.1, le_trans ht.2 hy⟩
    have hst : dist s t < η₀ := by
      rw [Real.dist_eq]
      refine lt_of_le_of_lt ?_ hηlt
      rw [abs_sub_le_iff]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    exact le_trans (le_of_lt (hη₀ s hs1 t ht1 hst)) (by linarith)
  -- the compactness argument
  have hcd : Continuous fun p : ℝ × ℝ => min |p.1 - p.2| (2 * Real.pi - |p.1 - p.2|) := by
    fun_prop
  set K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi) ∩
    {p : ℝ × ℝ | η ≤ min |p.1 - p.2| (2 * Real.pi - |p.1 - p.2|)} with hKdef
  have hK : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).inter_right (isClosed_le continuous_const hcd)
  have hKne : K.Nonempty := by
    refine ⟨(0, η), ⟨⟨le_refl 0, by linarith⟩, ⟨hηpos.le, by linarith⟩⟩, ?_⟩
    show η ≤ min |(0 : ℝ) - η| (2 * Real.pi - |(0 : ℝ) - η|)
    rw [zero_sub, abs_neg, abs_of_pos hηpos, min_eq_left]
    linarith
  obtain ⟨p, hp, hpmin⟩ := hK.exists_isMinOn hKne
    ((hγc.comp continuous_fst).dist (hγc.comp continuous_snd)).continuousOn
  rw [isMinOn_iff] at hpmin
  have hpcd : η ≤ min |p.1 - p.2| (2 * Real.pi - |p.1 - p.2|) := hp.2
  have hp1mem : p.1 ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := hp.1.1
  have hp2mem : p.2 ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := hp.1.2
  have hpm : 0 < dist (γ p.1) (γ p.2) := by
    rw [dist_pos]
    intro hcon
    obtain ⟨k1, h1mem, h1γ⟩ := exists_period_reduce hγp p.1
    obtain ⟨k2, h2mem, h2γ⟩ := exists_period_reduce hγp p.2
    have heq : p.1 - 2 * Real.pi * (k1 : ℝ) = p.2 - 2 * Real.pi * (k2 : ℝ) :=
      hγi h1mem h2mem (by rw [h1γ, h2γ, hcon])
    have hdiff : p.1 - p.2 = 2 * Real.pi * (((k1 - k2 : ℤ)) : ℝ) := by push_cast; linarith
    have hlt1 : η ≤ |p.1 - p.2| := le_trans hpcd (min_le_left _ _)
    have hlt2 : η ≤ 2 * Real.pi - |p.1 - p.2| := le_trans hpcd (min_le_right _ _)
    rcases eq_or_ne (k1 - k2) 0 with hm | hm
    · have hzero : (((k1 - k2 : ℤ)) : ℝ) = 0 := by simp [hm]
      rw [hdiff, hzero, mul_zero, abs_zero] at hlt1
      linarith [hηpos]
    · have hm1 : (1 : ℝ) ≤ |(((k1 - k2 : ℤ)) : ℝ)| := by
        have h3 : (1 : ℤ) ≤ |k1 - k2| := Int.one_le_abs hm
        exact_mod_cast h3
      have habs : |p.1 - p.2| = 2 * Real.pi * |(((k1 - k2 : ℤ)) : ℝ)| := by
        rw [hdiff, abs_mul, abs_of_pos h2π]
      have hbig : 2 * Real.pi ≤ |p.1 - p.2| := by rw [habs]; nlinarith
      linarith
  refine ⟨dist (γ p.1) (γ p.2), hpm, ?_⟩
  intro a ha b hb hab hlt
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  obtain ⟨k1, hx₀mem, hx₀γ⟩ := exists_period_reduce hγp s
  obtain ⟨k2, hy₀mem, hy₀γ⟩ := exists_period_reduce hγp t
  set x₀ : ℝ := s - 2 * Real.pi * (k1 : ℝ) with hx₀def
  set y₀ : ℝ := t - 2 * Real.pi * (k2 : ℝ) with hy₀def
  have hγx₀ : γ x₀ = a := by rw [hx₀def]; exact hx₀γ.trans hs
  have hγy₀ : γ y₀ = b := by rw [hy₀def]; exact hy₀γ.trans ht
  have hx₀0 : 0 ≤ x₀ := hx₀mem.1
  have hx₀lt : x₀ < 2 * Real.pi := hx₀mem.2
  have hy₀0 : 0 ≤ y₀ := hy₀mem.1
  have hy₀lt : y₀ < 2 * Real.pi := hy₀mem.2
  have hminlt : min |x₀ - y₀| (2 * Real.pi - |x₀ - y₀|) < η := by
    by_contra hcon
    rw [not_lt] at hcon
    have hmemK : (x₀, y₀) ∈ K :=
      ⟨⟨⟨hx₀mem.1, hx₀mem.2.le⟩, ⟨hy₀mem.1, hy₀mem.2.le⟩⟩, hcon⟩
    have h1 := hpmin (x₀, y₀) hmemK
    simp only [Function.comp_apply] at h1
    have h2 : dist (γ x₀) (γ y₀) < dist (γ p.1) (γ p.2) := by
      simpa only [dist_eq_norm, hγx₀, hγy₀] using hlt
    linarith
  rcases lt_or_ge |x₀ - y₀| η with hlt1 | hge
  · rcases le_total x₀ y₀ with hle | hle
    · have hne : x₀ ≠ y₀ := by
        intro hcon
        exact hab (hγx₀.symm.trans ((congrArg γ hcon).trans hγy₀))
      refine ⟨x₀, y₀, lt_of_le_of_ne hle hne, injOn_Icc_of_sub_lt hγp hγi (by linarith), ?_,
        Or.inl ⟨hγx₀, hγy₀⟩⟩
      refine hdiam x₀ y₀ hx₀0 (by linarith) ?_
      have h := hlt1
      rw [abs_of_nonpos (by linarith : x₀ - y₀ ≤ 0)] at h
      linarith
    · have hne : y₀ ≠ x₀ := by
        intro hcon
        exact hab (hγx₀.symm.trans ((congrArg γ hcon).symm.trans hγy₀))
      refine ⟨y₀, x₀, lt_of_le_of_ne hle hne, injOn_Icc_of_sub_lt hγp hγi (by linarith), ?_,
        Or.inr ⟨hγy₀, hγx₀⟩⟩
      refine hdiam y₀ x₀ hy₀0 (by linarith) ?_
      have h := hlt1
      rw [abs_of_nonneg (by linarith : 0 ≤ x₀ - y₀)] at h
      linarith
  · have hwrap : 2 * Real.pi - |x₀ - y₀| < η := by
      rcases min_lt_iff.mp hminlt with h | h
      · exact absurd h (not_lt.mpr hge)
      · exact h
    rcases le_total x₀ y₀ with hle | hle
    · have hlen : (2 * Real.pi + x₀) - y₀ < η := by
        rw [abs_of_nonpos (by linarith)] at hwrap
        linarith
      refine ⟨y₀, 2 * Real.pi + x₀, by linarith, ?_, ?_, Or.inr ⟨hγy₀, ?_⟩⟩
      · exact injOn_Icc_of_sub_lt hγp hγi (by linarith [hηle1, hlen])
      · exact hdiam y₀ (2 * Real.pi + x₀) hy₀0 (by linarith) (le_of_lt hlen)
      · rw [show 2 * Real.pi + x₀ = x₀ + 2 * Real.pi by ring, hγp x₀]
        exact hγx₀
    · have hlen : (2 * Real.pi + y₀) - x₀ < η := by
        rw [abs_of_nonneg (by linarith)] at hwrap
        linarith
      refine ⟨x₀, 2 * Real.pi + y₀, by linarith, ?_, ?_, Or.inl ⟨hγx₀, ?_⟩⟩
      · exact injOn_Icc_of_sub_lt hγp hγi (by linarith [hηle1, hlen])
      · exact hdiam x₀ (2 * Real.pi + y₀) hx₀0 (by linarith) (le_of_lt hlen)
      · rw [show 2 * Real.pi + y₀ = y₀ + 2 * Real.pi by ring, hγp y₀]
        exact hγy₀

end Work.Smooth.SphereJordan.Caratheodory
