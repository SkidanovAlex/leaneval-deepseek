import Mathlib
import Submission.Work.Smooth.SphereJordan.windNumber_ne_of_straight_piece
import Submission.Work.Smooth.SphereJordan.loopIndexSeparation

/-!
# Separation of the two cusp germs at a tangency point

Two externally tangent closed discs of radius `r` with centres `a`, `b` (so `a + b = 2x`, where `x`
is the tangency point) have locally complementary sectors at `x`; this file shows that the two
sectors are *separated*: the two points of the complement just off `x` in the two directions
perpendicular to `b - a` lie in different connected components of the complement of the union,
provided the rest of the union is joined up (preconnectedness of the open union).

The separating curve is the loop

`Λ = [b → x] ∪ [x → a] ∪ β`,

where `β` is a path in the open union joining `a` to `b` (which preconnectedness of the open union
provides).  The loop passes through `x` along the straight line through `a` and `b`, so the two
points `x ± ρ·I·(a - x)/r` lie on opposite sides of it, and the classical index argument
(`loopIndex_ne_of_straight_piece`) separates them.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-- A preconnected open subset of `ℂ` joins any two of its points by a path inside it. -/
theorem exists_path_in_openUnion' {Q : Finset ℂ} {r : ℝ}
    (hB : IsPreconnected (⋃ w ∈ Q, Metric.ball w r)) {a b : ℂ}
    (ha : a ∈ ⋃ w ∈ Q, Metric.ball w r) (hb : b ∈ ⋃ w ∈ Q, Metric.ball w r) :
    ∃ β : C(unitInterval, ℂ), (∀ t, β t ∈ ⋃ w ∈ Q, Metric.ball w r) ∧ β 0 = a ∧ β 1 = b := by
  set U : Set ℂ := ⋃ w ∈ Q, Metric.ball w r with hUdef
  have hUopen : IsOpen U := by
    rw [hUdef]
    exact isOpen_iUnion fun w => isOpen_iUnion fun _ => Metric.isOpen_ball
  haveI : LocallyPathConnectedSpace ↥U := hUopen.locallyPathConnectedSpace
  haveI : PreconnectedSpace ↥U := (isPreconnected_iff_preconnectedSpace).mp (hUdef ▸ hB)
  haveI : ConnectedSpace ↥U := ConnectedSpace.mk ⟨⟨a, hUdef ▸ ha⟩⟩
  haveI : PathConnectedSpace ↥U := PathConnectedSpace.of_locallyPathConnectedSpace
  let γ : Path (⟨a, hUdef ▸ ha⟩ : ↥U) (⟨b, hUdef ▸ hb⟩ : ↥U) := PathConnectedSpace.somePath _ _
  exact ⟨⟨fun t => (γ t : ℂ), γ.continuous.subtype_val⟩, fun t => (γ t).2,
    congrArg Subtype.val γ.source, congrArg Subtype.val γ.target⟩

/-- **The index of a loop about the two sides of a straight cut through which it passes exactly
once differs.**  This is `windNumber_ne_of_straight_piece` for a closed path on `[0,1]`; the
injectivity hypothesis of that theorem is replaced by `hfirst`, the assumption that the loop meets
the crossing point `x` only at the parameter `τ₀`. -/
theorem loopIndex_ne_of_straight_piece {Λ : C(unitInterval, ℂ)} (hloop : Λ 0 = Λ 1)
    (x u v : ℂ) (hu : ‖u‖ = 1) (hv : v = Complex.I * u) {cc : ℝ → ℝ}
    {τ₀ : unitInterval} (ht₀ : (τ₀ : ℝ) ∈ Set.Ioo 0 1) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hx : Λ τ₀ = x)
    (hpiece : ∀ t : unitInterval, |(t : ℝ) - (τ₀ : ℝ)| < δ →
      Λ t = x + (((cc (t : ℝ)) : ℝ) : ℂ) * u)
    (hmono : ∀ t : unitInterval, |(t : ℝ) - (τ₀ : ℝ)| < δ →
      (cc (t : ℝ) < 0 ↔ (t : ℝ) < (τ₀ : ℝ)))
    (havoid : ∀ t : unitInterval, ∀ b : ℝ, -ρ < b → b < ρ → b ≠ 0 → Λ t ≠ x + (b : ℂ) * v)
    (hoff₁ : ∀ t : unitInterval, Λ t ≠ x + (ρ : ℂ) * v)
    (hoff₂ : ∀ t : unitInterval, Λ t ≠ x - (ρ : ℂ) * v)
    (hfirst : ∀ t : unitInterval, Λ t = x → t = τ₀) :
    loopIndex (loopSub Λ (x + (ρ : ℂ) * v)) ≠ loopIndex (loopSub Λ (x - (ρ : ℂ) * v)) := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; norm_num at hu
  have hv0 : v ≠ 0 := by rw [hv]; exact mul_ne_zero Complex.I_ne_zero hu0
  set zmin : ℂ := x - (ρ : ℂ) * v with hzmin
  set zplus : ℂ := x + (ρ : ℂ) * v with hzplus
  have hΛmin : ∀ t : unitInterval, Λ t ≠ zmin := fun t => by rw [hzmin]; exact hoff₂ t
  have hΛplus : ∀ t : unitInterval, Λ t ≠ zplus := fun t => by rw [hzplus]; exact hoff₁ t
  set c : C(unitInterval, ℂ) := ⟨fun t => (Λ t - zmin) / (Λ t - zplus),
    (Λ.continuous.sub continuous_const).div (Λ.continuous.sub continuous_const)
      (fun t => sub_ne_zero.mpr (hΛplus t))⟩ with hcdef
  have hcapp : ∀ t, c t = (Λ t - zmin) / (Λ t - zplus) := fun t => rfl
  have hcne : ∀ t, c t ≠ 0 := fun t => by
    rw [hcapp]
    exact div_ne_zero (sub_ne_zero.mpr (hΛmin t)) (sub_ne_zero.mpr (hΛplus t))
  have hcloop : c 0 = c 1 := by rw [hcapp, hcapp, hloop]
  have hc₀ : c τ₀ = -1 := by
    rw [hcapp, hx, hzmin, hzplus]
    have h1 : x - (x - (ρ : ℂ) * v) = (ρ : ℂ) * v := by ring
    have h2 : x - (x + (ρ : ℂ) * v) = -((ρ : ℂ) * v) := by ring
    rw [h1, h2, div_neg, div_self (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hρ)) hv0)]
  have hτ₀mem : (c τ₀).im = 0 := by rw [hc₀]; norm_num
  have hτ₀neg : (c τ₀).re < 0 := by rw [hc₀]; norm_num
  -- the quotient loop meets the closed negative real axis only at the crossing parameter
  have hreal : ∀ t : unitInterval, (c t).im = 0 → (c t).re ≤ 0 → t = τ₀ := by
    intro t hsim hsre
    by_contra hne
    have hslit : c t ∈ Complex.slitPlane := by
      have hseg : ∀ r : ℝ, r ∈ Set.Icc 0 1 → Λ t ≠ (1 - r) * zmin + r * zplus := by
        intro r hr hcon
        have hb : (1 - r) * zmin + r * zplus = x + (((2 * r - 1) * ρ : ℝ) : ℂ) * v := by
          rw [hzmin, hzplus, segment_interp]
        rw [hb] at hcon
        have hb1 : -ρ ≤ (2 * r - 1) * ρ := by nlinarith [hr.1, hr.2, hρ]
        have hb2 : (2 * r - 1) * ρ ≤ ρ := by nlinarith [hr.1, hr.2, hρ]
        rcases lt_trichotomy ((2 * r - 1) * ρ) 0 with hlt | heq | hgt
        · rcases eq_or_lt_of_le hb1 with h1 | h1
          · rw [← h1] at hcon
            exact hΛmin t (by rw [hcon, hzmin]; push_cast; ring)
          · exact havoid t _ h1 (by linarith) (ne_of_lt hlt) hcon
        · have hΛx : Λ t = x := by
            rw [hcon, heq, Complex.ofReal_zero, zero_mul, add_zero]
          exact hne (hfirst t hΛx)
        · rcases eq_or_lt_of_le hb2 with h2 | h2
          · rw [h2] at hcon
            exact hΛplus t (by rw [hcon, hzplus])
          · exact havoid t _ (by linarith) h2 (ne_of_gt hgt) hcon
      have h1 : (Λ t - zplus) / (Λ t - zmin) ∈ Complex.slitPlane :=
        div_sub_mem_slitPlane_of_notMem_segment (x := zmin) (y := zplus) hseg
      have h2 : ((Λ t - zplus) / (Λ t - zmin))⁻¹ ∈ Complex.slitPlane := inv_mem_slitPlane h1
      have h3 : c t = ((Λ t - zplus) / (Λ t - zmin))⁻¹ := by rw [hcapp, inv_div]
      rwa [h3]
    rw [Complex.mem_slitPlane_iff] at hslit
    rcases hslit with h | h
    · linarith
    · exact h hsim
  have hccτ₀ : cc (τ₀ : ℝ) = 0 := by
    have h2 : x + (((cc (τ₀ : ℝ)) : ℝ) : ℂ) * u = x := by
      rw [← hpiece τ₀ (by rw [sub_self, abs_zero]; exact hδ), hx]
    have h3 : (((cc (τ₀ : ℝ)) : ℝ) : ℂ) * u = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact_mod_cast h
    · exact absurd h hu0
  -- the transversal sign condition at the crossing parameter
  have hsign : ∃ δ' : ℝ, 0 < δ' ∧ ∀ t : unitInterval, |(t : ℝ) - (τ₀ : ℝ)| < δ' →
      (t : ℝ) ≠ (τ₀ : ℝ) →
      (((t : ℝ) < (τ₀ : ℝ)) ↔ (c t).im < 0) ∧ (((τ₀ : ℝ) < (t : ℝ)) ↔ 0 < (c t).im) := by
    refine ⟨δ, hδ, ?_⟩
    intro t htδ htne
    have hccne : cc (t : ℝ) ≠ 0 := by
      intro h0
      have hΛx : Λ t = x := by rw [hpiece t htδ, h0]; simp
      have : t = τ₀ := hfirst t hΛx
      exact htne (congrArg Subtype.val this)
    have hcval : c t = ((cc (t : ℝ) : ℂ) + (ρ : ℂ) * Complex.I)
        / ((cc (t : ℝ) : ℂ) - (ρ : ℂ) * Complex.I) := by
      rw [hcapp, hpiece t htδ, hzmin, hzplus]
      exact straightBlock_quotient x u v hu0 hv hρ
    have him : (c t).im = 2 * ρ * cc (t : ℝ) / ((cc (t : ℝ)) ^ 2 + ρ ^ 2) := by
      rw [hcval]
      exact straightBlock_quotient_im (r := cc (t : ℝ)) hρ
    have hpos : 0 < (cc (t : ℝ)) ^ 2 + ρ ^ 2 := by positivity
    have hneg : (c t).im < 0 ↔ cc (t : ℝ) < 0 := by
      rw [him, div_lt_iff₀ hpos]
      constructor <;> intro h <;> nlinarith [hρ, h]
    have hposim : 0 < (c t).im ↔ 0 < cc (t : ℝ) := by
      rw [him, div_pos_iff_of_pos_right hpos]
      constructor <;> intro h <;> nlinarith [hρ, h]
    constructor
    · rw [hneg, hmono t htδ]
    · rw [hposim]
      constructor
      · intro hgt
        have h1 : ¬ ((t : ℝ) < (τ₀ : ℝ)) := not_lt.mpr (le_of_lt hgt)
        have h2 : ¬ (cc (t : ℝ) < 0) := fun hc => h1 ((hmono t htδ).mp hc)
        exact lt_of_le_of_ne (not_lt.mp h2) (Ne.symm hccne)
      · intro h
        by_contra hcon
        push_neg at hcon
        rcases lt_or_eq_of_le hcon with hlt | heq
        · have hcc : cc (t : ℝ) < 0 := (hmono t htδ).mpr hlt
          linarith [hcc, h]
        · have hte : t = τ₀ := Subtype.ext heq
          rw [hte, hccτ₀] at h
          exact absurd h (lt_irrefl 0)
  have hne0 : loopIndex c ≠ 0 :=
    loopIndex_ne_zero_of_crossOnce hcne hcloop ht₀ hτ₀mem hτ₀neg hreal hsign
  intro hgoal
  have hdiff := loopIndex_div_eq_sub hloop hΛmin hΛplus
  have hgoal' : loopIndex (loopSub Λ zplus) = loopIndex (loopSub Λ zmin) := by
    rw [hzplus, hzmin]
    exact hgoal
  have h0 : loopIndex (loopSub Λ zmin) - loopIndex (loopSub Λ zplus) = 0 := by
    rw [hgoal']; ring
  rw [← hdiff] at h0
  exact hne0 h0


/-- **The two cusp germs at a tangency point are separated.**  Let `a`, `b ∈ Q` be two centres with
`dist x a = r` and `a + b = 2x` (so the closed discs of radius `r` about `a` and `b` are externally
tangent at `x`), suppose that the points `x + c·I·(a - x)/r` for `0 < |c| ≤ ρ` are outside the union
`⋃ w ∈ Q, closedBall w r`, and that the open union `⋃ w ∈ Q, ball w r` is preconnected.  Then the two
points `x ± ρ·I·(a - x)/r` lie in *different* connected components of the complement of the union. -/
theorem tangency_cusps_separated {Q : Finset ℂ} {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hB : IsPreconnected (⋃ w ∈ Q, Metric.ball w r)) {x a b : ℂ} (ha : a ∈ Q) (hb : b ∈ Q)
    (hab : a + b = 2 * x) (haxr : dist x a = r) (hxout : ∀ w ∈ Q, r ≤ dist x w)
    (hseg : ∀ c : ℝ, c ≠ 0 → |c| ≤ ρ →
      x + (c : ℂ) * (Complex.I * ((a - x) / (r : ℂ))) ∉ ⋃ w ∈ Q, Metric.closedBall w r) :
    ∀ z : ℂ, ¬ (x + (ρ : ℂ) * (Complex.I * ((a - x) / (r : ℂ))) ∈
          connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) z ∧
        x - (ρ : ℂ) * (Complex.I * ((a - x) / (r : ℂ))) ∈
          connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) z) := by
  classical
  set u : ℂ := (a - x) / (r : ℂ) with hudef
  have hnorma : ‖a - x‖ = r := by rw [← dist_eq_norm, dist_comm]; exact haxr
  have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hu1 : ‖u‖ = 1 := by
    rw [hudef, norm_div, hnorma, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact div_self (ne_of_gt hr)
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu1; norm_num at hu1
  have hax : a - x = (r : ℂ) * u := by rw [hudef]; field_simp
  have hbx : b - x = -((r : ℂ) * u) := by
    have h : b - x = -(a - x) := by linear_combination hab
    rw [h, hax]
  have hxb : x - b = (r : ℂ) * u := by
    rw [show x - b = -(b - x) from by ring, hbx]; ring
  have hxa : x - a = -((r : ℂ) * u) := by
    rw [show x - a = -(a - x) from by ring, hax]
  have hxbeq : x = b + (r : ℂ) * u := by linear_combination hxb
  set v : ℂ := Complex.I * u with hvdef
  have hv0 : v ≠ 0 := by rw [hvdef]; exact mul_ne_zero Complex.I_ne_zero hu0
  have hseg' : ∀ c : ℝ, c ≠ 0 → |c| ≤ ρ →
      x + (c : ℂ) * v ∉ ⋃ w ∈ Q, Metric.closedBall w r := by
    intro c hc0 hcabs
    have h := hseg c hc0 hcabs
    rwa [hvdef, hudef] at h
  -- the path in the open union joining `a` and `b`
  obtain ⟨β, hβU, hβ0, hβ1⟩ := exists_path_in_openUnion' hB
    (Set.mem_iUnion₂.mpr ⟨a, ha, Metric.mem_ball_self hr⟩)
    (Set.mem_iUnion₂.mpr ⟨b, hb, Metric.mem_ball_self hr⟩)
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  set βf : ℝ → ℂ := fun t => β (Set.projIcc 0 1 h01 t) with hβfdef
  have hβfcont : Continuous βf := by
    rw [hβfdef]
    exact β.continuous.comp (continuous_projIcc (h := h01))
  have hβf0 : βf 0 = a := by
    have h0 : Set.projIcc 0 1 h01 (0 : ℝ) = (0 : unitInterval) := Subtype.ext (by simp)
    simp only [hβfdef]
    rw [h0, hβ0]
  have hβf1 : βf 1 = b := by
    have h0 : Set.projIcc 0 1 h01 (1 : ℝ) = (1 : unitInterval) := Subtype.ext (by simp)
    simp only [hβfdef]
    rw [h0, hβ1]
  have hβfU : ∀ t : ℝ, βf t ∈ ⋃ w ∈ Q, Metric.ball w r := by
    intro t; rw [hβfdef]; exact hβU _
  have hβfU' : ∀ t : ℝ, βf t ∈ ⋃ w ∈ Q, Metric.closedBall w r := by
    intro t
    obtain ⟨w, hw, hwt⟩ := Set.mem_iUnion₂.mp (hβfU t)
    exact Set.mem_iUnion₂.mpr ⟨w, hw, Metric.ball_subset_closedBall hwt⟩
  have hxV : x ∉ ⋃ w ∈ Q, Metric.ball w r := by
    intro h
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp h
    have h1 : dist x w < r := by rwa [Metric.mem_ball] at hxw
    linarith [hxout w hw]
  -- the loop `[b → x] ∪ [x → a] ∪ β`
  set L : ℝ → ℂ := fun t => if t ≤ 1 / 4 then b + (((4 * t : ℝ)) : ℂ) * (x - b)
      else if t ≤ 1 / 2 then x + (((4 * t - 1 : ℝ)) : ℂ) * (a - x)
      else βf (2 * t - 1) with hLdef
  have hLcont : Continuous L := by
    rw [hLdef]
    have hinner : Continuous (fun t : ℝ =>
        if t ≤ 1 / 2 then x + (((4 * t - 1 : ℝ)) : ℂ) * (a - x) else βf (2 * t - 1)) := by
      refine continuous_if_le continuous_id continuous_const ?_ ?_ ?_
      · fun_prop
      · exact (hβfcont.comp (by fun_prop)).continuousOn
      · intro t ht
        have h1 : (4 * (1 / 2 : ℝ) - 1) = 1 := by norm_num
        have h2 : 2 * (1 / 2 : ℝ) - 1 = 0 := by norm_num
        rw [ht, h1, h2, hβf0]
        push_cast
        ring
    refine continuous_if_le continuous_id continuous_const ?_ ?_ ?_
    · fun_prop
    · exact hinner.continuousOn
    · intro t ht
      have h1 : (4 * (1 / 4 : ℝ)) = 1 := by norm_num
      rw [ht, h1, if_pos (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)]
      push_cast
      ring
  have Lval₁ : ∀ t : ℝ, t ≤ 1 / 4 → L t = b + (((4 * t : ℝ)) : ℂ) * (x - b) := by
    intro t ht; simp only [hLdef, if_pos ht]
  have Lval₂ : ∀ t : ℝ, 1 / 4 ≤ t → t ≤ 1 / 2 →
      L t = x + (((4 * t - 1 : ℝ)) : ℂ) * (a - x) := by
    intro t h1 h2
    by_cases ht : t = 1 / 4
    · rw [ht, Lval₁ (1 / 4) (le_refl _)]
      push_cast
      ring
    · have ht' : ¬ (t ≤ 1 / 4) := not_le.mpr (lt_of_le_of_ne h1 (Ne.symm ht))
      simp only [hLdef, if_neg ht', if_pos h2]
  have Lval₃ : ∀ t : ℝ, 1 / 2 ≤ t → L t = βf (2 * t - 1) := by
    intro t ht
    by_cases ht1 : t = 1 / 2
    · rw [ht1, Lval₂ (1 / 2) (by norm_num) (le_refl _), show 2 * (1 / 2 : ℝ) - 1 = 0 from by norm_num,
        hβf0]
      push_cast
      ring
    · have ht' : ¬ (t ≤ 1 / 2) := not_le.mpr (lt_of_le_of_ne ht (Ne.symm ht1))
      simp only [hLdef, if_neg (by linarith : ¬ (t ≤ 1 / 4)), if_neg ht']
  set Λ : C(unitInterval, ℂ) := ⟨fun t => L (t : ℝ), hLcont.comp continuous_subtype_val⟩
    with hΛdef
  have hΛval : ∀ t : unitInterval, Λ t = L (t : ℝ) := fun t => rfl
  have hloop : Λ 0 = Λ 1 := by
    have h1 : L (((0 : unitInterval) : ℝ)) = b := by
      rw [show (((0 : unitInterval) : ℝ)) = (0 : ℝ) from rfl, Lval₁ 0 (by norm_num)]
      norm_num
    have h2 : L (((1 : unitInterval) : ℝ)) = b := by
      rw [show (((1 : unitInterval) : ℝ)) = (1 : ℝ) from rfl, Lval₃ 1 (by norm_num),
        show 2 * (1 : ℝ) - 1 = 1 from by norm_num, hβf1]
    change L (((0 : unitInterval) : ℝ)) = L (((1 : unitInterval) : ℝ))
    rw [h1, h2]
  have hLmem : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → L t ∈ ⋃ w ∈ Q, Metric.closedBall w r := by
    intro t ht0 ht1
    by_cases h1 : t ≤ 1 / 4
    · rw [Lval₁ t h1]
      refine Set.mem_iUnion₂.mpr ⟨b, hb, Metric.mem_closedBall.mpr ?_⟩
      have hstep : dist (b + (((4 * t : ℝ)) : ℂ) * (x - b)) b = 4 * t * r := by
        rw [dist_eq_norm,
          show b + (((4 * t : ℝ)) : ℂ) * (x - b) - b = (((4 * t : ℝ)) : ℂ) * (x - b) from by ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), hxb,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hu1, mul_one]
      rw [hstep]; nlinarith [ht0, h1, hr]
    · by_cases h2 : t ≤ 1 / 2
      · rw [Lval₂ t (le_of_lt (not_le.mp h1)) h2]
        refine Set.mem_iUnion₂.mpr ⟨a, ha, Metric.mem_closedBall.mpr ?_⟩
        have hstep : dist (x + (((4 * t - 1 : ℝ)) : ℂ) * (a - x)) a = (1 - (4 * t - 1)) * r := by
          rw [dist_eq_norm,
            show x + (((4 * t - 1 : ℝ)) : ℂ) * (a - x) - a
              = ((1 - (4 * t - 1) : ℝ) : ℂ) * (x - a) from by push_cast; ring,
            norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - (4 * t - 1)), hxa, norm_neg, norm_mul,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hu1, mul_one]
        rw [hstep]; nlinarith [h1, h2, hr]
      · rw [Lval₃ t (le_of_lt (not_le.mp h2))]
        exact hβfU' (2 * t - 1)
  have hΛmem : ∀ t : unitInterval, Λ t ∈ ⋃ w ∈ Q, Metric.closedBall w r := fun t =>
    hLmem (t : ℝ) t.2.1 t.2.2
  set τ₀ : unitInterval := ⟨1 / 4, by norm_num⟩ with hτ₀def
  have hτ₀coe : (τ₀ : ℝ) = 1 / 4 := rfl
  have ht₀ : (τ₀ : ℝ) ∈ Set.Ioo 0 1 := by rw [hτ₀coe]; norm_num
  have hx : Λ τ₀ = x := by
    rw [hΛval, hτ₀coe, Lval₁ (1 / 4) (le_refl _)]
    push_cast
    ring
  set cc : ℝ → ℝ := fun s => (4 * s - 1) * r with hccdef
  have hpiece : ∀ t : unitInterval, |(t : ℝ) - (τ₀ : ℝ)| < 1 / 8 →
      Λ t = x + (((cc (t : ℝ)) : ℝ) : ℂ) * u := by
    intro t ht
    have ht2 : (t : ℝ) < 1 / 2 := by
      rw [hτ₀coe, abs_lt] at ht; linarith [ht.2]
    rw [hΛval]
    by_cases h1 : (t : ℝ) ≤ 1 / 4
    · rw [Lval₁ (t : ℝ) h1]
      have e : b + (((4 * (t : ℝ) : ℝ)) : ℂ) * (x - b)
          = x + ((((4 * (t : ℝ) - 1) * r : ℝ)) : ℂ) * u := by
        rw [hxb, hxbeq]
        push_cast
        ring
      exact e
    · rw [Lval₂ (t : ℝ) (le_of_lt (not_le.mp h1)) (le_of_lt ht2)]
      have e : x + (((4 * (t : ℝ) - 1 : ℝ)) : ℂ) * (a - x)
          = x + ((((4 * (t : ℝ) - 1) * r : ℝ)) : ℂ) * u := by
        rw [hax]
        push_cast
        ring
      exact e
  have hmono : ∀ t : unitInterval, |(t : ℝ) - (τ₀ : ℝ)| < 1 / 8 →
      (cc (t : ℝ) < 0 ↔ (t : ℝ) < (τ₀ : ℝ)) := by
    intro t ht
    rw [hτ₀coe]
    constructor
    · intro h
      by_contra hcon
      push_neg at hcon
      nlinarith
    · intro h
      nlinarith
  have hfirst : ∀ t : unitInterval, Λ t = x → t = τ₀ := by
    intro t ht
    rw [hΛval] at ht
    by_cases h1 : (t : ℝ) ≤ 1 / 4
    · rw [Lval₁ (t : ℝ) h1] at ht
      have h2 : ((4 * (t : ℝ) - 1 : ℝ) : ℂ) * (x - b) = 0 := by
        have e : b + (((4 * (t : ℝ) : ℝ)) : ℂ) * (x - b)
            = x + (((4 * (t : ℝ) - 1 : ℝ)) : ℂ) * (x - b) := by push_cast; ring
        rw [e] at ht
        linear_combination ht
      rw [hxb] at h2
      rcases mul_eq_zero.mp h2 with h3 | h3
      · have h4 : (4 * (t : ℝ) - 1) = 0 := Complex.ofReal_inj.mp h3
        have h5 : (t : ℝ) = 1 / 4 := by linarith
        exact Subtype.ext (by rw [h5, hτ₀coe])
      · have h3' : ‖(r : ℂ) * u‖ = 0 := by rw [h3, norm_zero]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hu1, mul_one] at h3'
        linarith
    · by_cases h2 : (t : ℝ) ≤ 1 / 2
      · rw [Lval₂ (t : ℝ) (le_of_lt (not_le.mp h1)) h2] at ht
        have h3 : (((4 * (t : ℝ) - 1 : ℝ)) : ℂ) * (a - x) = 0 := by
          linear_combination ht
        rw [hax] at h3
        rcases mul_eq_zero.mp h3 with h4 | h4
        · have h5 : (4 * (t : ℝ) - 1) = 0 := Complex.ofReal_inj.mp h4
          have h6 : (t : ℝ) = 1 / 4 := by linarith
          exact Subtype.ext (by rw [h6, hτ₀coe])
        · have h4' : ‖(r : ℂ) * u‖ = 0 := by rw [h4, norm_zero]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hu1, mul_one] at h4'
          linarith
      · rw [Lval₃ (t : ℝ) (le_of_lt (not_le.mp h2))] at ht
        have hmem : x ∈ ⋃ w ∈ Q, Metric.ball w r := by
          rw [← ht]; exact hβfU (2 * (t : ℝ) - 1)
        exact absurd hmem hxV
  have havoid : ∀ t : unitInterval, ∀ c : ℝ, -ρ < c → c < ρ → c ≠ 0 → Λ t ≠ x + (c : ℂ) * v := by
    intro t c hc1 hc2 hc0 hcon
    have h1 : Λ t ∈ ⋃ w ∈ Q, Metric.closedBall w r := hΛmem t
    have h2 : x + (c : ℂ) * v ∉ ⋃ w ∈ Q, Metric.closedBall w r :=
      hseg' c hc0 (by rw [abs_le]; exact ⟨le_of_lt hc1, le_of_lt hc2⟩)
    exact h2 (hcon ▸ h1)
  have hoff₁ : ∀ t : unitInterval, Λ t ≠ x + (ρ : ℂ) * v := by
    intro t hcon
    exact (hseg' ρ (ne_of_gt hρ) (by rw [abs_of_pos hρ])) (hcon ▸ hΛmem t)
  have hoff₂ : ∀ t : unitInterval, Λ t ≠ x - (ρ : ℂ) * v := by
    intro t hcon
    have hmem : x - (ρ : ℂ) * v ∈ ⋃ w ∈ Q, Metric.closedBall w r := hcon ▸ hΛmem t
    have h2 : x - (ρ : ℂ) * v ∉ ⋃ w ∈ Q, Metric.closedBall w r := by
      have h3 := hseg' (-ρ) (neg_ne_zero.mpr (ne_of_gt hρ)) (by rw [abs_neg, abs_of_pos hρ])
      rwa [show x + ((-ρ : ℝ) : ℂ) * v = x - (ρ : ℂ) * v from by push_cast; ring] at h3
    exact h2 hmem
  have hne_loop : loopIndex (loopSub Λ (x + (ρ : ℂ) * v)) ≠
      loopIndex (loopSub Λ (x - (ρ : ℂ) * v)) :=
    loopIndex_ne_of_straight_piece (δ := 1 / 8) (cc := cc) hloop x u v hu1 hvdef ht₀
      (by norm_num) hρ hx hpiece hmono
      havoid hoff₁ hoff₂ hfirst
  have key : ∀ z : ℂ, ¬ (x + (ρ : ℂ) * v ∈
        connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) z ∧
      x - (ρ : ℂ) * v ∈ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) z) := by
    intro z hmem
    have hsub : connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) z ⊆
        (Set.range Λ)ᶜ := by
      intro y hy hyl
      obtain ⟨t, ht⟩ := hyl
      rw [← ht] at hy
      exact (connectedComponentIn_subset _ _ hy) (hΛmem t)
    exact hne_loop (loopIndex_eq_of_preconnected hloop isPreconnected_connectedComponentIn
      hsub hmem.1 hmem.2)
  intro z hmem
  exact key z (by simpa only [hvdef, hudef] using hmem)

end

end Work.Smooth.SphereJordan
