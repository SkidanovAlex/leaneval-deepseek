import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.ODE.ExistUnique
import Submission.Work.RiemLib.Commons.Analysis.ODE.dist_le_exp_mul_dist_of_hasDerivAt_of_norm_sub_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.ODE

open scoped _root_.ContDiff
open Set Filter Metric
open scoped Topology NNReal

/-- One-sided no-exit: a solution confined (a priori) within the Grönwall bound stays in the ball,
and satisfies the Grönwall estimate, for all nonnegative times in its interval of definition. -/
theorem norm_sub_le_exp_mul_of_hasDerivAt_of_lipschitzOnWith_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {z₀ y : E} {R : ℝ} (hR : 0 < R) {L : NNReal}
    (hF0 : F z₀ = 0) (hLip : LipschitzOnWith L F (closedBall z₀ R))
    {z : ℝ → E} {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hz : ∀ t ∈ Ioo a b, HasDerivAt z (F (z t)) t) (h0 : z 0 = y)
    (hsmall : ‖y - z₀‖ * Real.exp ((L : ℝ) * b) < R) :
    ∀ t ∈ Ico 0 b, ‖z t - z₀‖ ≤ ‖y - z₀‖ * Real.exp ((L : ℝ) * t) ∧
      z t ∈ closedBall z₀ R := by
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have hz0mem : z₀ ∈ closedBall z₀ R := mem_closedBall_self hR.le
  have hcb : ‖y - z₀‖ < R := by
    have hexp1 : (1 : ℝ) ≤ Real.exp ((L : ℝ) * b) := Real.one_le_exp (by positivity)
    have : ‖y - z₀‖ * 1 ≤ ‖y - z₀‖ * Real.exp ((L : ℝ) * b) :=
      mul_le_mul_of_nonneg_left hexp1 (norm_nonneg _)
    linarith [hsmall]
  -- Gronwall on any piece on which the solution is known to be confined
  have gron : ∀ s ∈ Ico 0 b, (∀ t ∈ Icc 0 s, z t ∈ closedBall z₀ R) →
      ∀ t ∈ Icc 0 s, ‖z t - z₀‖ ≤ ‖y - z₀‖ * Real.exp ((L : ℝ) * t) := by
    intro s hs hp t ht
    have htb : t < b := lt_of_le_of_lt ht.2 hs.2
    have hdc := dist_le_exp_mul_dist_of_hasDerivAt_of_norm_sub_le
      (x := z) (y := fun _ : ℝ => z₀) (x' := fun u => F (z u)) (y' := fun _ : ℝ => 0)
      (a := 0) (b := t) (L := (L : ℝ)) ht.1 hL0
      (fun u hu => hz u ⟨by linarith [hu.1, ha, hs.1], lt_of_le_of_lt hu.2 htb⟩)
      (fun u _ => hasDerivAt_const u z₀)
      (fun u hu => by
        have huIcc : u ∈ Icc 0 s := ⟨hu.1, le_trans hu.2 ht.2⟩
        have := hLip.dist_le_mul (z u) (hp u huIcc) z₀ hz0mem
        rw [dist_eq_norm, dist_eq_norm, hF0] at this
        simpa using this)
    simpa [dist_eq_norm, h0] using hdc
  -- the bootstrap step
  have boot : ∀ s ∈ Ico 0 b, (∀ t ∈ Icc 0 s, z t ∈ closedBall z₀ R) →
      ∃ s' ∈ Ico 0 b, s < s' ∧ ∀ t ∈ Icc 0 s', z t ∈ closedBall z₀ R := by
    intro s hs hp
    have hbs : ‖z s - z₀‖ ≤ ‖y - z₀‖ * Real.exp ((L : ℝ) * s) := gron s hs hp s ⟨hs.1, le_rfl⟩
    have hexp_le : Real.exp ((L : ℝ) * s) ≤ Real.exp ((L : ℝ) * b) :=
      Real.exp_le_exp.mpr (by nlinarith [hL0, hs.2.le])
    have hlt : ‖z s - z₀‖ < R := by
      have h1 : ‖y - z₀‖ * Real.exp ((L : ℝ) * s) ≤ ‖y - z₀‖ * Real.exp ((L : ℝ) * b) :=
        mul_le_mul_of_nonneg_left hexp_le (norm_nonneg _)
      linarith [hbs, h1, hsmall]
    have hmem : closedBall z₀ R ∈ 𝓝 (z s) :=
      closedBall_mem_nhds_of_mem (by rw [mem_ball, dist_eq_norm]; exact hlt)
    have hcont : ContinuousAt z s := (hz s ⟨by linarith [hs.1, ha], hs.2⟩).continuousAt
    obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp (hcont.eventually hmem)
    have hbs' : 0 < b - s := by linarith [hs.2]
    have hminpos : 0 < min ε ((b - s) / 2) := lt_min hε (by linarith)
    refine ⟨s + min ε ((b - s) / 2) / 2, ⟨?_, ?_⟩, ?_, ?_⟩
    · linarith [hs.1, hminpos]
    · have h1 : min ε ((b - s) / 2) ≤ (b - s) / 2 := min_le_right _ _
      linarith [h1, hbs']
    · linarith [hminpos]
    · intro t ht
      rcases le_or_gt t s with h | h
      · exact hp t ⟨ht.1, h⟩
      · have h4 : min ε ((b - s) / 2) ≤ ε := min_le_left _ _
        have h3 : min ε ((b - s) / 2) / 2 < ε := by linarith
        have h2 : t < s + ε := by linarith [ht.2]
        have : t ∈ ball s ε := by
          rw [mem_ball, Real.dist_eq, abs_lt]
          exact ⟨by linarith [h], by linarith [h2]⟩
        exact hε' this
  -- supremum argument
  intro t ht
  set S : Set ℝ := {s | s ∈ Ico 0 b ∧ ∀ t ∈ Icc 0 s, z t ∈ closedBall z₀ R} with hSdef
  have hp0 : ∀ u ∈ Icc (0 : ℝ) 0, z u ∈ closedBall z₀ R := by
    intro u hu
    rw [Icc_self] at hu
    rw [hu, h0]
    exact mem_closedBall_iff_norm.mpr hcb.le
  have hSne : S.Nonempty := ⟨0, ⟨⟨le_rfl, hb⟩, hp0⟩⟩
  have hSbdd : BddAbove S := ⟨b, fun s hs => hs.1.2.le⟩
  set sstar : ℝ := sSup S with hstardef
  have hle_b : sstar ≤ b := csSup_le hSne (fun s hs => hs.1.2.le)
  have hsstar_eq : sstar = b := by
    by_contra hne
    have hlt : sstar < b := lt_of_le_of_ne hle_b hne
    have hge0 : 0 ≤ sstar := le_csSup hSbdd ⟨⟨le_rfl, hb⟩, hp0⟩
    have pstar : ∀ u ∈ Icc 0 sstar, z u ∈ closedBall z₀ R := by
      intro u hu
      rcases lt_or_eq_of_le hu.2 with h | h
      · obtain ⟨s, hsS, hus⟩ := exists_lt_of_lt_csSup hSne h
        exact hsS.2 u ⟨hu.1, le_of_lt hus⟩
      · have humem : z sstar ∈ closedBall z₀ R := by
          rcases eq_or_lt_of_le hge0 with h0' | h0'
          · rw [← h0', h0]
            exact mem_closedBall_iff_norm.mpr hcb.le
          · have hcont : ContinuousAt z sstar := (hz sstar ⟨by linarith [h0', ha], hlt⟩).continuousAt
            have hev : ∀ᶠ u in 𝓝[<] sstar, z u ∈ closedBall z₀ R := by
              filter_upwards [Ioo_mem_nhdsLT h0'] with u hu
              obtain ⟨s, hsS, hus⟩ := exists_lt_of_lt_csSup hSne hu.2
              exact hsS.2 u ⟨hu.1.le, le_of_lt hus⟩
            exact IsClosed.mem_of_tendsto isClosed_closedBall
              (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
        rw [h]
        exact humem
    obtain ⟨s', hs'Ico, hs'gt, hs'p⟩ := boot sstar ⟨hge0, hlt⟩ pstar
    exact absurd (le_csSup hSbdd ⟨hs'Ico, hs'p⟩) (not_le.mpr hs'gt)
  have htlt : t < sstar := by rw [hsstar_eq]; exact ht.2
  obtain ⟨s, hsS, hts⟩ := exists_lt_of_lt_csSup hSne htlt
  exact ⟨gron s hsS.1 hsS.2 t ⟨ht.1, le_of_lt hts⟩, hsS.2 t ⟨ht.1, le_of_lt hts⟩⟩

/-- **No exit from the Grönwall ball**, two-sided version. -/
theorem norm_sub_le_exp_mul_of_hasDerivAt_of_lipschitzOnWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {z₀ y : E} {R : ℝ} (hR : 0 < R) {L : NNReal}
    (hF0 : F z₀ = 0) (hLip : LipschitzOnWith L F (closedBall z₀ R))
    {z : ℝ → E} {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hz : ∀ t ∈ Ioo a b, HasDerivAt z (F (z t)) t) (h0 : z 0 = y)
    (hsmall : ‖y - z₀‖ * Real.exp ((L : ℝ) * max |a| |b|) < R) :
    ∀ t ∈ Ioo a b, ‖z t - z₀‖ ≤ ‖y - z₀‖ * Real.exp ((L : ℝ) * |t|) ∧
      z t ∈ closedBall z₀ R := by
  have hb' : ‖y - z₀‖ * Real.exp ((L : ℝ) * b) < R := by
    have h1 : b ≤ max |a| |b| := le_trans (le_abs_self b) (le_max_right _ _)
    have h2 : (L : ℝ) * b ≤ (L : ℝ) * max |a| |b| :=
      mul_le_mul_of_nonneg_left h1 L.coe_nonneg
    have h3 : Real.exp ((L : ℝ) * b) ≤ Real.exp ((L : ℝ) * max |a| |b|) :=
      Real.exp_le_exp.mpr h2
    have h4 := mul_le_mul_of_nonneg_left h3 (norm_nonneg (y - z₀))
    linarith [hsmall]
  have ha' : ‖y - z₀‖ * Real.exp ((L : ℝ) * (-a)) < R := by
    have h : (-a : ℝ) = |a| := (abs_of_neg ha).symm
    have h1 : |a| ≤ max |a| |b| := le_max_left _ _
    have h2 : (L : ℝ) * (-a) ≤ (L : ℝ) * max |a| |b| := by
      rw [h]; exact mul_le_mul_of_nonneg_left h1 L.coe_nonneg
    have h3 : Real.exp ((L : ℝ) * (-a)) ≤ Real.exp ((L : ℝ) * max |a| |b|) :=
      Real.exp_le_exp.mpr h2
    have h4 := mul_le_mul_of_nonneg_left h3 (norm_nonneg (y - z₀))
    linarith [hsmall]
  have hright := norm_sub_le_exp_mul_of_hasDerivAt_of_lipschitzOnWith_right
    hR hF0 hLip ha hb hz h0 hb'
  -- time reversal
  have hzr : ∀ u ∈ Ioo (-b) (-a),
      HasDerivAt (fun u : ℝ => z (-u)) ((fun x => -F x) ((fun u : ℝ => z (-u)) u)) u := by
    intro u hu
    have hu' : -u ∈ Ioo a b := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have := (hz (-u) hu').scomp u (hasDerivAt_neg u)
    simpa [Function.comp_def] using this
  have hleft := norm_sub_le_exp_mul_of_hasDerivAt_of_lipschitzOnWith_right
    (z := fun u : ℝ => z (-u)) (F := fun x => -F x) hR
    (by simpa using hF0) hLip.neg (by linarith) (by linarith) hzr (by simpa using h0) ha'
  intro t ht
  rcases le_or_gt (0 : ℝ) t with h | h
  · have hh := hright t ⟨h, ht.2⟩
    rwa [abs_of_nonneg h]
  · have ht' : -t ∈ Ico 0 (-a) := ⟨by linarith, by linarith [ht.1]⟩
    have hh := hleft (-t) ht'
    obtain ⟨h1, h2⟩ := hh
    have h3 : (-t : ℝ) = |t| := (abs_of_neg h).symm
    have h4 : -(-t) = t := neg_neg t
    rw [h4] at h1
    rw [h3] at h1
    exact ⟨h1, by simpa only [h4] using h2⟩

theorem exists_uniform_local_solution_of_lipschitzOnWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {z₀ : E} {R r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁R : r₁ < R) {L : NNReal}
    (hF0 : F z₀ = 0) (hLip : LipschitzOnWith L F (closedBall z₀ R)) :
    ∃ s > (0 : ℝ), ∀ l ∈ closedBall z₀ r₁, ∀ τ : ℝ, ∃ α : ℝ → E, α τ = l ∧
      (∀ t ∈ Ioo (τ - s) (τ + s), HasDerivAt α (F (α t)) t) ∧
      (∀ t ∈ Icc (τ - s) (τ + s), α t ∈ closedBall z₀ R) := by
  have hR : 0 < R := lt_of_le_of_lt hr₁0 hr₁R
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have hMpos : 0 < ((L : ℝ) + 1) * R := by positivity
  have har : 0 < R - r₁ := by linarith
  have hs0 : 0 < (R - r₁) / (2 * (((L : ℝ) + 1) * R)) := by positivity
  refine ⟨(R - r₁) / (2 * (((L : ℝ) + 1) * R)), hs0, ?_⟩
  intro l hl τ
  let A : NNReal := ⟨R - r₁, har.le⟩
  let M : NNReal := ⟨((L : ℝ) + 1) * R, hMpos.le⟩
  have hA : (A : ℝ) = R - r₁ := rfl
  have hM : (M : ℝ) = ((L : ℝ) + 1) * R := rfl
  have hlmem : ‖l - z₀‖ ≤ r₁ := mem_closedBall_iff_norm.mp hl
  have hsub : closedBall l A ⊆ closedBall z₀ R := by
    intro x hx
    rw [mem_closedBall_iff_norm] at hx ⊢
    rw [hA] at hx
    calc ‖x - z₀‖ ≤ ‖x - l‖ + ‖l - z₀‖ := norm_sub_le_norm_sub_add_norm_sub x l z₀
      _ ≤ (R - r₁) + r₁ := by linarith
      _ = R := by ring
  have hτmem : τ ∈ Icc (τ - (R - r₁) / (2 * (((L : ℝ) + 1) * R)))
      (τ + (R - r₁) / (2 * (((L : ℝ) + 1) * R))) :=
    ⟨by linarith [hs0.le], by linarith [hs0.le]⟩
  have hpl : IsPicardLindelof (fun _ : ℝ => F)
      (⟨τ, hτmem⟩ :
        Icc (τ - (R - r₁) / (2 * (((L : ℝ) + 1) * R)))
          (τ + (R - r₁) / (2 * (((L : ℝ) + 1) * R))))
      l A 0 M L := by
    refine IsPicardLindelof.of_time_independent ?_ ?_ ?_
    · intro x hx
      have hxR : x ∈ closedBall z₀ R := hsub hx
      have hxz : ‖x - z₀‖ ≤ R := mem_closedBall_iff_norm.mp hxR
      have hdist := hLip.dist_le_mul x hxR z₀ (mem_closedBall_self hR.le)
      rw [dist_eq_norm, dist_eq_norm, hF0, sub_zero] at hdist
      calc ‖F x‖ ≤ (L : ℝ) * ‖x - z₀‖ := hdist
        _ ≤ (L : ℝ) * R := by gcongr
        _ ≤ ((L : ℝ) + 1) * R := by nlinarith
        _ = (M : ℝ) := hM.symm
    · exact hLip.mono hsub
    · simp only [add_sub_cancel_left, sub_sub_self, max_self, NNReal.coe_zero, sub_zero]
      rw [hA, hM]
      have hid : ((L : ℝ) + 1) * R * ((R - r₁) / (2 * (((L : ℝ) + 1) * R))) = (R - r₁) / 2 := by
        rw [← mul_div_assoc, mul_comm (2 : ℝ) (((L : ℝ) + 1) * R), mul_div_mul_left]
        positivity
      rw [hid]
      linarith
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hpl
    (show l ∈ closedBall l (↑(0 : NNReal)) from mem_closedBall_self le_rfl)
  refine ⟨α.compProj, ?_, ?_, ?_⟩
  · exact (ODE.FunSpace.compProj_of_mem (α := α) (t := τ) hτmem).trans
      (ODE.FunSpace.apply_of_zero α)
  · intro t ht
    have hd : HasDerivWithinAt α.compProj (F (α.compProj t))
        (Icc (τ - (R - r₁) / (2 * (((L : ℝ) + 1) * R)))
          (τ + (R - r₁) / (2 * (((L : ℝ) + 1) * R)))) t := by
      apply ODE.hasDerivWithinAt_picard_Icc (f := fun _ : ℝ => F)
        hτmem hpl.continuousOn_uncurry
        α.continuous_compProj.continuousOn
        (fun t' _ => α.compProj_mem_closedBall hpl.mul_max_le) l
        (Ioo_subset_Icc_self ht)
        |>.congr_of_mem _ (Ioo_subset_Icc_self ht)
      intro t' ht'
      nth_rw 1 [← hα]
      rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
    exact hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  · intro t ht
    exact hsub (α.compProj_mem_closedBall hpl.mul_max_le)


/-- If two functions agree eventually at `τ` (from the left), then replacing the first by the
second on `(-∞, τ)` keeps differentiability at `τ`. -/
theorem hasDerivAt_ite_lt_of_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w₁ w₂ : ℝ → E} {v : E} {τ : ℝ} (h : w₁ =ᶠ[𝓝 τ] w₂) (h₂ : HasDerivAt w₂ v τ) :
    HasDerivAt (fun t => if t < τ then w₁ t else w₂ t) v τ := by
  refine h₂.congr_of_eventuallyEq ?_
  filter_upwards [h] with t ht
  by_cases hlt : t < τ
  · simp only [hlt, if_pos]; exact ht
  · simp only [hlt, if_false]

/-- **Global (fixed-interval) existence with a priori confinement.**

Let `F` be `L`-Lipschitz on the closed ball of radius `R` around `z₀`, with `F z₀ = 0`, and let
`y` be an initial value with `‖y - z₀‖ * exp (L * T) < R`.  Then `z' = F z`, `z 0 = y` has a
solution on the whole interval `(-T, T)`, and every such solution stays inside `closedBall z₀ R`
there. -/
theorem exists_solution_on_Ioo_of_lipschitzOnWith_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {z₀ y : E} {R : ℝ} (hR : 0 < R) {L : NNReal}
    (hF0 : F z₀ = 0) (hLip : LipschitzOnWith L F (closedBall z₀ R))
    {T : ℝ} (hT : 0 < T) (hsmall : ‖y - z₀‖ * Real.exp ((L : ℝ) * T) < R) :
    ∃ z : ℝ → E, z 0 = y ∧ (∀ t ∈ Ioo (-T) T, HasDerivAt z (F (z t)) t) ∧
      (∀ t ∈ Ioo (-T) T, z t ∈ closedBall z₀ R) := by
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  set r₁ : ℝ := ‖y - z₀‖ * Real.exp ((L : ℝ) * T) with hr₁def
  have hr₁0 : 0 ≤ r₁ := by rw [hr₁def]; positivity
  have hr₁R : r₁ < R := by rw [hr₁def]; exact hsmall
  obtain ⟨s, hs_pos, hrestart⟩ :=
    exists_uniform_local_solution_of_lipschitzOnWith hr₁0 hr₁R hF0 hLip
  set ε₀ : ℝ := min s T with hε₀def
  have hε₀_pos : 0 < ε₀ := by rw [hε₀def]; exact lt_min hs_pos hT
  have hε₀_le_s : ε₀ ≤ s := by rw [hε₀def]; exact min_le_left _ _
  have hε₀_le_T : ε₀ ≤ T := by rw [hε₀def]; exact min_le_right _ _
  set δ : ℝ := min s ε₀ / 4 with hδdef
  have hδ_pos : 0 < δ := by
    rw [hδdef]
    have : 0 < min s ε₀ := lt_min hs_pos hε₀_pos
    linarith
  have h4δ : 4 * δ ≤ ε₀ := by
    rw [hδdef]
    have := min_le_right s ε₀
    linarith
  have h2δs : 2 * δ ≤ s := by
    rw [hδdef]
    have := min_le_left s ε₀
    linarith
  -- a local solution around `0`
  have hy_mem : y ∈ closedBall z₀ r₁ := by
    rw [hr₁def, mem_closedBall_iff_norm]
    calc ‖y - z₀‖ = ‖y - z₀‖ * 1 := (mul_one _).symm
      _ ≤ ‖y - z₀‖ * Real.exp ((L : ℝ) * T) :=
          mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity)) (norm_nonneg _)
  obtain ⟨z₁, hz₁τ, hz₁d, -⟩ := hrestart y hy_mem 0
  have hz₁d' : ∀ t ∈ Ioo (-ε₀) ε₀, HasDerivAt z₁ (F (z₁ t)) t := fun t ht =>
    hz₁d t ⟨by linarith [ht.1, hε₀_le_s], by linarith [ht.2, hε₀_le_s]⟩
  -- the set of admissible lengths
  set A : Set ℝ := {T₀ | ε₀ ≤ T₀ ∧ T₀ ≤ T ∧
    ∃ z : ℝ → E, z 0 = y ∧ ∀ t ∈ Ioo (-T₀) T₀, HasDerivAt z (F (z t)) t} with hAdef
  have hA_ne : A.Nonempty := ⟨ε₀, le_rfl, hε₀_le_T, z₁, hz₁τ, hz₁d'⟩
  have hA_bdd : BddAbove A := ⟨T, fun x hx => hx.2.1⟩
  -- the extension step
  have hext : ∀ T₀ ∈ A, 2 * δ ≤ T₀ → ∃ z : ℝ → E, z 0 = y ∧
      ∀ t ∈ Ioo (-(T₀ + δ)) (T₀ + δ), HasDerivAt z (F (z t)) t := by
    intro T₀ hT₀A hT₀2δ
    obtain ⟨hε₀T₀, hT₀T, z, hz0, hzderiv⟩ := hT₀A
    have hT₀pos : 0 < T₀ := lt_of_lt_of_le hδ_pos (by linarith)
    -- the a priori bound
    have hsmallT₀ : ‖y - z₀‖ * Real.exp ((L : ℝ) * T₀) < R := by
      have h1 : Real.exp ((L : ℝ) * T₀) ≤ Real.exp ((L : ℝ) * T) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT₀T hLnn)
      have h2 : ‖y - z₀‖ * Real.exp ((L : ℝ) * T₀) ≤
          ‖y - z₀‖ * Real.exp ((L : ℝ) * T) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      linarith [h2, hsmall]
    have hnoexit := norm_sub_le_exp_mul_of_hasDerivAt_of_lipschitzOnWith hR hF0 hLip
      (neg_lt_zero.mpr hT₀pos) hT₀pos hzderiv hz0 (by
        rw [abs_neg, abs_of_pos hT₀pos, max_self]
        exact hsmallT₀)
    have hzr₁ : ∀ t ∈ Ioo (-T₀) T₀, z t ∈ closedBall z₀ r₁ := by
      intro t ht
      obtain ⟨h1, -⟩ := hnoexit t ht
      have habs : |t| ≤ T₀ := (abs_lt.mpr ht).le
      have h2 : (L : ℝ) * |t| ≤ (L : ℝ) * T₀ := mul_le_mul_of_nonneg_left habs hLnn
      have h3 : ‖y - z₀‖ * Real.exp ((L : ℝ) * |t|) ≤ ‖y - z₀‖ * Real.exp ((L : ℝ) * T₀) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) (norm_nonneg _)
      have h4 : ‖y - z₀‖ * Real.exp ((L : ℝ) * T₀) ≤ r₁ := by
        rw [hr₁def]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT₀T hLnn))
          (norm_nonneg _)
      rw [mem_closedBall_iff_norm]
      linarith [h1, h3, h4]
    -- restart to the right at an interior point
    set t₁ : ℝ := T₀ - δ with ht₁def
    have ht₁_in : t₁ ∈ Ioo (-T₀) T₀ :=
      ⟨by rw [ht₁def]; linarith [hT₀2δ], by rw [ht₁def]; linarith [hδ_pos]⟩
    have ht₁pos : 0 < t₁ := by rw [ht₁def]; linarith [hT₀2δ, hδ_pos]
    obtain ⟨αr, hαrτ, hαrd, hαrc⟩ := hrestart (z t₁) (hzr₁ t₁ ht₁_in) t₁
    have hzeq : z =ᶠ[𝓝 t₁] αr := by
      refine ODE_solution_unique_of_eventually (v := fun _ : ℝ => F)
        (s := fun _ : ℝ => closedBall z₀ R) (K := L) (t₀ := t₁) (f := z) (g := αr)
        ?_ ?_ ?_ hαrτ.symm
      · exact Eventually.of_forall (fun _ => hLip)
      · filter_upwards [Ioo_mem_nhds ht₁_in.1 ht₁_in.2] with u hu
        exact ⟨hzderiv u hu, closedBall_subset_closedBall hr₁R.le (hzr₁ u hu)⟩
      · have hlt₁ : t₁ - s < t₁ := by linarith [hs_pos]
        have hlt₂ : t₁ < t₁ + s := by linarith [hs_pos]
        filter_upwards [Ioo_mem_nhds hlt₁ hlt₂] with u hu
        exact ⟨hαrd u hu, hαrc u (Ioo_subset_Icc_self hu)⟩
    set w₁ : ℝ → E := fun u => if u < t₁ then z u else αr u with hw₁def
    have hw₁d : ∀ u ∈ Ioo (-T₀) (t₁ + s), HasDerivAt w₁ (F (w₁ u)) u := by
      intro u hu
      rcases lt_trichotomy u t₁ with h | h | h
      · have hev : w₁ =ᶠ[𝓝 u] z := by
          filter_upwards [isOpen_Iio.mem_nhds h] with v hv
          simp only [Set.mem_Iio] at hv
          simp only [hw₁def, if_pos hv]
        have huz : HasDerivAt z (F (z u)) u := hzderiv u ⟨hu.1, lt_trans h ht₁_in.2⟩
        have hwu : w₁ u = z u := by simp only [hw₁def, if_pos h]
        rw [hwu]
        exact huz.congr_of_eventuallyEq hev
      · have hev : w₁ =ᶠ[𝓝 t₁] αr := by
          filter_upwards [hzeq] with v hv
          by_cases hlt : v < t₁
          · simp only [hw₁def, if_pos hlt]; exact hv
          · simp only [hw₁def, if_neg hlt]
        have hα' : HasDerivAt αr (F (αr t₁)) t₁ :=
          hαrd t₁ ⟨by linarith [hδ_pos], by linarith [hδ_pos]⟩
        subst h
        have hwu : w₁ t₁ = αr t₁ := by simp only [hw₁def, if_neg (lt_irrefl t₁)]
        rw [hwu]
        exact hα'.congr_of_eventuallyEq hev
      · have hev : w₁ =ᶠ[𝓝 u] αr := by
          filter_upwards [isOpen_Ioi.mem_nhds h] with v hv
          simp only [Set.mem_Ioi] at hv
          simp only [hw₁def, if_neg (not_lt.mpr hv.le)]
        have hα' : HasDerivAt αr (F (αr u)) u :=
          hαrd u ⟨by linarith [h, hs_pos], hu.2⟩
        have hwu : w₁ u = αr u := by simp only [hw₁def, if_neg (not_lt.mpr h.le)]
        rw [hwu]
        exact hα'.congr_of_eventuallyEq hev
    -- restart to the left
    set t₂ : ℝ := -T₀ + δ with ht₂def
    have ht₂_in : t₂ ∈ Ioo (-T₀) (t₁ + s) :=
      ⟨by rw [ht₂def]; linarith [hδ_pos],
       by rw [ht₂def, ht₁def]; linarith [hT₀2δ, hδ_pos, hs_pos]⟩
    have ht₂_inT : t₂ ∈ Ioo (-T₀) T₀ :=
      ⟨by rw [ht₂def]; linarith [hδ_pos], by rw [ht₂def]; linarith [hT₀2δ, hδ_pos]⟩
    have ht₂_lt_t₁ : t₂ < t₁ := by rw [ht₂def, ht₁def]; linarith [hT₀2δ, hδ_pos]
    have hw₁t₂ : w₁ t₂ = z t₂ := by simp only [hw₁def, if_pos ht₂_lt_t₁]
    obtain ⟨αl, hαlτ, hαld, hαlc⟩ := hrestart (w₁ t₂) (by rw [hw₁t₂]; exact hzr₁ t₂ ht₂_inT) t₂
    have hw₁eq : w₁ =ᶠ[𝓝 t₂] αl := by
      refine ODE_solution_unique_of_eventually (v := fun _ : ℝ => F)
        (s := fun _ : ℝ => closedBall z₀ R) (K := L) (t₀ := t₂) (f := w₁) (g := αl)
        ?_ ?_ ?_ hαlτ.symm
      · exact Eventually.of_forall (fun _ => hLip)
      · filter_upwards [Ioo_mem_nhds ht₂_inT.1 ht₂_inT.2, isOpen_Iio.mem_nhds ht₂_lt_t₁]
          with u hu hu'
        refine ⟨hw₁d u ⟨hu.1, ?_⟩, ?_⟩
        · rw [ht₁def]; linarith [hu.2, hδ_pos, hs_pos]
        · rw [show w₁ u = z u from by
              simp only [Set.mem_Iio] at hu'
              simp only [hw₁def, if_pos hu']]
          exact closedBall_subset_closedBall hr₁R.le (hzr₁ u hu)
      · have hlt₁ : t₂ - s < t₂ := by linarith [hs_pos]
        have hlt₂ : t₂ < t₂ + s := by linarith [hs_pos]
        filter_upwards [Ioo_mem_nhds hlt₁ hlt₂] with u hu
        exact ⟨hαld u hu, hαlc u (Ioo_subset_Icc_self hu)⟩
    set w : ℝ → E := fun u => if u < t₂ then αl u else w₁ u with hwdef
    refine ⟨w, ?_, ?_⟩
    · have h0t₂ : ¬ ((0 : ℝ) < t₂) := by rw [ht₂def]; linarith [hT₀2δ, hδ_pos]
      have h0t₁ : (0 : ℝ) < t₁ := ht₁pos
      simp only [hwdef, if_neg h0t₂, hw₁def, if_pos h0t₁]
      exact hz0
    · intro u hu
      rcases lt_trichotomy u t₂ with h | h | h
      · have hev : w =ᶠ[𝓝 u] αl := by
          filter_upwards [isOpen_Iio.mem_nhds h] with v hv
          simp only [Set.mem_Iio] at hv
          simp only [hwdef, if_pos hv]
        have hα' : HasDerivAt αl (F (αl u)) u :=
          hαld u ⟨by linarith [hu.1, h2δs], by linarith [h, hs_pos]⟩
        have hwu : w u = αl u := by simp only [hwdef, if_pos h]
        rw [hwu]
        exact hα'.congr_of_eventuallyEq hev
      · have hev : w =ᶠ[𝓝 t₂] αl := by
          filter_upwards [hw₁eq] with v hv
          by_cases hlt : v < t₂
          · simp only [hwdef, if_pos hlt]
          · simp only [hwdef, if_neg hlt]; exact hv
        have hα' : HasDerivAt αl (F (αl t₂)) t₂ :=
          hαld t₂ ⟨by linarith [hs_pos], by linarith [hs_pos]⟩
        subst h
        have hwu : w t₂ = αl t₂ := by
          simp only [hwdef, if_neg (lt_irrefl t₂)]
          exact hαlτ.symm
        rw [hwu]
        exact hα'.congr_of_eventuallyEq hev
      · have hev : w =ᶠ[𝓝 u] w₁ := by
          filter_upwards [isOpen_Ioi.mem_nhds h] with v hv
          simp only [Set.mem_Ioi] at hv
          simp only [hwdef, if_neg (not_lt.mpr hv.le)]
        have hw' : HasDerivAt w₁ (F (w₁ u)) u :=
          hw₁d u ⟨by linarith [ht₂_inT.1, h], by linarith [hu.2, h2δs]⟩
        have hwu : w u = w₁ u := by simp only [hwdef, if_neg (not_lt.mpr h.le)]
        rw [hwu]
        exact hw'.congr_of_eventuallyEq hev
  -- sup argument
  set Tstar : ℝ := sSup A with hTstardef
  have hle : Tstar ≤ T := csSup_le hA_ne (fun x hx => hx.2.1)
  have hge : ε₀ ≤ Tstar := le_csSup hA_bdd ⟨le_rfl, hε₀_le_T, z₁, hz₁τ, hz₁d'⟩
  have hkey : T - δ < Tstar := by
    by_contra hcon
    push Not at hcon
    have h2δ : 2 * δ < Tstar := by linarith [hge, h4δ, hδ_pos]
    have hmaxlt : max (2 * δ) (Tstar - δ) < Tstar := max_lt h2δ (by linarith [hδ_pos])
    obtain ⟨b, hb1, hb2⟩ : ∃ b : ℝ, max (2 * δ) (Tstar - δ) < b ∧ b < Tstar :=
      ⟨(max (2 * δ) (Tstar - δ) + Tstar) / 2, by linarith, by linarith⟩
    have h1 : 2 * δ ≤ b := le_trans (le_max_left _ _) hb1.le
    have h2 : Tstar - δ < b := lt_of_le_of_lt (le_max_right _ _) hb1
    obtain ⟨T₀, hT₀A, hbT₀⟩ := exists_lt_of_lt_csSup hA_ne hb2
    have hT₀le : T₀ ≤ Tstar := le_csSup hA_bdd hT₀A
    have hT₀2δ : 2 * δ ≤ T₀ := by linarith
    have hT₀δT : T₀ + δ ≤ T := by linarith
    obtain ⟨z, hz0, hzd⟩ := hext T₀ hT₀A hT₀2δ
    have hmem : T₀ + δ ∈ A := ⟨by linarith [hT₀A.1, hδ_pos], hT₀δT, z, hz0, hzd⟩
    have := le_csSup hA_bdd hmem
    linarith [hbT₀, h2]
  obtain ⟨T₀, hT₀A, hT₀gt⟩ := exists_lt_of_lt_csSup hA_ne hkey
  have hfin : ∃ T₁ ≥ T, ∃ z : ℝ → E, z 0 = y ∧
      ∀ t ∈ Ioo (-T₁) T₁, HasDerivAt z (F (z t)) t := by
    by_cases hcase : T ≤ T₀
    · exact ⟨T₀, hcase, hT₀A.2.2⟩
    · push Not at hcase
      have hT₀2δ : 2 * δ ≤ T₀ := by linarith [hT₀gt, h4δ, hε₀_le_T, hT]
      obtain ⟨z, hz0, hzd⟩ := hext T₀ hT₀A hT₀2δ
      exact ⟨T₀ + δ, by linarith [hT₀gt], z, hz0, hzd⟩
  obtain ⟨T₁, hTT₁, z, hz0, hzd⟩ := hfin
  refine ⟨z, hz0, fun t ht => hzd t ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  have hnoexit := norm_sub_le_exp_mul_of_hasDerivAt_of_lipschitzOnWith hR hF0 hLip
    (neg_lt_zero.mpr hT) hT
    (fun t ht => hzd t ⟨by linarith [ht.1], by linarith [ht.2]⟩) hz0
    (by rw [abs_neg, abs_of_pos hT, max_self]; exact hsmall)
  exact fun t ht => (hnoexit t ht).2



/-- **Uniform local existence inside an open set on which the field is `C¹`.**

Let `U` be an open subset of `E × E` containing `(p₀, 0)`, and let `G : E × E → E` be `C¹` at every
point of `U` with `G (p₀, 0) = 0`.  Then there is `ρ > 0` such that *every* initial velocity `w`
with `‖w‖ ≤ ρ` gives a solution of `u'' = G (u, u')`, `u 0 = p₀`, `u' 0 = w`, defined on the whole
fixed interval `Set.Ioo (-2) 2` **and taking all its values in `U`**.

The uniformity in `w` near `w = 0` and the confinement to `U` are the key points: because `G`
vanishes at `(p₀,0)`, the Gronwall estimate `‖(u t, u' t) - (p₀,0)‖ ≤ ‖w‖ * exp (L t)` (with `L` a
local Lipschitz constant of `z ↦ (z.2, G z)` on a ball around `(p₀,0)` contained in `U`) keeps the
solution inside that ball as long as `‖w‖ * exp (L t) ≤ ρ'`, so `ρ ≤ ρ' * exp (-2L)` suffices. -/
theorem exists_uniform_secondOrderODE_solution_in_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : E × E → E} {U : Set (E × E)} {p₀ : E} (hU : IsOpen U) (hp₀ : (p₀, (0 : E)) ∈ U)
    (hG : ∀ z ∈ U, ContDiffAt ℝ 1 G z) (hG0 : G (p₀, 0) = 0) :
    ∃ ρ > (0 : ℝ), ∀ w : E, ‖w‖ ≤ ρ → ∃ u v : ℝ → E,
      u 0 = p₀ ∧ v 0 = w ∧
      (∀ t ∈ Set.Ioo (-2 : ℝ) 2, (u t, v t) ∈ U) ∧
      (∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt u (v t) t) ∧
      (∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt v (G (u t, v t)) t) := by
  set z₀ : E × E := (p₀, (0 : E)) with hz₀def
  set F : E × E → E × E := fun z => (z.2, G z) with hFdef
  have hz₀U : z₀ ∈ U := hp₀
  have hF0 : F z₀ = 0 := by
    simp only [hFdef]
    ext
    · simp [hz₀def]
    · exact hG0
  have hFcont : ContDiffAt ℝ 1 F z₀ := by
    rw [hFdef]
    exact (contDiffAt_snd (𝕜 := ℝ) (n := 1) (p := z₀)).prodMk (hG z₀ hz₀U)
  obtain ⟨K, s, hs, hK⟩ := hFcont.exists_lipschitzOnWith
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀U)
  set R : ℝ := min ε δ₁ / 2 with hRdef
  have hR : 0 < R := by
    rw [hRdef]
    have := lt_min hε hδ₁
    linarith
  have hRsub : closedBall z₀ R ⊆ U := by
    intro x hx
    apply hεsub
    exact closedBall_subset_ball (by rw [hRdef]; have := min_le_left ε δ₁; linarith) hx
  have hLip : LipschitzOnWith K F (closedBall z₀ R) :=
    hK.mono (fun x hx =>
      hδ₁sub (closedBall_subset_ball (by rw [hRdef]; have := min_le_right ε δ₁; linarith) hx))
  refine ⟨R * Real.exp (-((K : ℝ) * 2)) / 2, by positivity, ?_⟩
  intro w hw
  have hy : ‖(p₀, w) - z₀‖ * Real.exp ((K : ℝ) * 2) < R := by
    have h1 : ‖(p₀, w) - z₀‖ = ‖w‖ := by
      rw [hz₀def, Prod.mk_sub_mk, sub_self, Prod.norm_def]
      simp
    rw [h1]
    have h2 : ‖w‖ * Real.exp ((K : ℝ) * 2) ≤ R / 2 := by
      calc ‖w‖ * Real.exp ((K : ℝ) * 2)
          ≤ (R * Real.exp (-((K : ℝ) * 2)) / 2) * Real.exp ((K : ℝ) * 2) :=
            mul_le_mul_of_nonneg_right hw (Real.exp_nonneg _)
        _ = R / 2 := by
            rw [div_mul_eq_mul_div, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
              mul_one]
    linarith [h2, hR]
  obtain ⟨z, hz0, hzd, hzball⟩ :=
    exists_solution_on_Ioo_of_lipschitzOnWith_ball hR hF0 hLip (by norm_num : (0 : ℝ) < 2) hy
  refine ⟨fun t => (z t).1, fun t => (z t).2, ?_, ?_, ?_, ?_, ?_⟩
  · exact congrArg Prod.fst hz0
  · exact congrArg Prod.snd hz0
  · intro t ht
    exact hRsub (hzball t ht)
  · intro t ht
    have h := HasFDerivAt.comp_hasDerivAt (f := z) t
      (hasFDerivAt_fst (𝕜 := ℝ) (E := E) (F := E) (p := z t)) (hzd t ht)
    simpa [hFdef, Function.comp_def] using h
  · intro t ht
    have h := HasFDerivAt.comp_hasDerivAt (f := z) t
      (hasFDerivAt_snd (𝕜 := ℝ) (E := E) (F := E) (p := z t)) (hzd t ht)
    simpa [hFdef, Function.comp_def] using h

end Commons.Analysis.ODE