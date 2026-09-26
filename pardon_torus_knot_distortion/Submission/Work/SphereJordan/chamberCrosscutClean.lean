import Mathlib
import Submission.Work.SphereJordan.chamberDefs
import Submission.Work.SphereJordan.component_open_of_real_bounded
import Submission.Work.SphereJordan.ball_sdiff_trace_atMostTwo
import Submission.Work.SphereJordan.chamberLocalWindow
import Submission.Work.SphereJordan.exists_trace_crosscut
import Submission.Work.SphereJordan.gammaInjOnArc
import Submission.Work.SphereJordan.crosscutAtMostTwoDomain

/-!
# The chamber of a trace component minus the trace component has at most two components

Let `γ` be a simple closed plane curve, `S` a Jordan separation of `γ`, `B = Metric.ball p ε` a
ball and `a ∈ γ.trace ∩ B`, with

`A := traceComponent γ p ε a = connectedComponentIn (γ.trace ∩ B) a`

the component of `a` in the trace inside the ball, and

`Ξ := connectedComponentIn (sideChamber γ p ε a) a`

the *chamber* of `a` (the component of `a` in the ball with all the other trace components
deleted).  The target is: of any three points of `Ξ \ A`, two lie in the same connected component
of `Ξ \ A` — i.e. `Ξ \ A` has at most two connected components (the two sides of the "crosscut"
`A`).

The proof cuts `Ξ` along the arc `A`, which is the range of an embedded arc with endpoints on
`Metric.sphere p ε` (hence outside `Ξ ⊆ B`), and applies the crosscut theorem for a plane domain
(`Work.Spike.crosscutAtMostTwoDomain_of_compactTwoPoints`, instantiated with the compact two-point
Janiszewski pigeonhole obtained from the transfer / `π₁` route
`Work.Spike.twoPointPigeonhole_aux`; no Mayer–Vietoris input is used).
-/

namespace Work.SphereJordan

open Set Metric

noncomputable section

/-! ## The crosscut theorem for a plane domain (axiom-clean instantiation) -/

/-- **The crosscut theorem**: an injective arc whose endpoints lie outside an open preconnected
`D ⊆ ℂ` and whose interior lies in `D` cuts `D` into at most two components. -/
theorem crosscutThm {D : Set ℂ} (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    {β : C(Set.Icc (0 : ℝ) 1, ℂ)} (hβ : Function.Injective β)
    (h₀ : β ⟨0, by norm_num⟩ ∉ D) (h₁ : β ⟨1, by norm_num⟩ ∉ D)
    (hint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∈ D) :
    ∀ x y z : ℂ, x ∈ D \ Set.range β → y ∈ D \ Set.range β → z ∈ D \ Set.range β →
      connectedComponentIn (D \ Set.range β) x = connectedComponentIn (D \ Set.range β) y ∨
      connectedComponentIn (D \ Set.range β) x = connectedComponentIn (D \ Set.range β) z ∨
      connectedComponentIn (D \ Set.range β) y = connectedComponentIn (D \ Set.range β) z :=
  Work.SphereJordan.crosscutAtMostTwoDomain hDopen hDconn hβ h₀ h₁ hint

/-- Reducing a real number modulo `2π` into a window `Ioo c (c + 2π)`, when possible. -/
theorem exists_int_sub_mem_Ioo {c t : ℝ} (ht : ∀ k : ℤ, t ≠ c + (k : ℝ) * (2 * Real.pi)) :
    ∃ k : ℤ, t - (k : ℝ) * (2 * Real.pi) ∈ Set.Ioo c (c + 2 * Real.pi) := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlow : (⌊(t - c) / (2 * Real.pi)⌋ : ℤ) ≤ (t - c) / (2 * Real.pi) :=
    Int.floor_le ((t - c) / (2 * Real.pi))
  have hup : (t - c) / (2 * Real.pi) < ((⌊(t - c) / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one ((t - c) / (2 * Real.pi))
  have hk1 : (⌊(t - c) / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤ t - c := by
    have := (le_div_iff₀ hp).mp hlow
    linarith
  have hk2 : t - c < ((⌊(t - c) / (2 * Real.pi)⌋ : ℝ) + 1) * (2 * Real.pi) := by
    have := (div_lt_iff₀ hp).mp hup
    linarith
  refine ⟨⌊(t - c) / (2 * Real.pi)⌋, ?_⟩
  have hne : t - (⌊(t - c) / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≠ c := fun h =>
    ht _ (by linarith)
  have hge : c ≤ t - (⌊(t - c) / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) := by linarith
  have hlt : t - (⌊(t - c) / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) < c + 2 * Real.pi := by linarith
  exact ⟨lt_of_le_of_ne hge (Ne.symm hne), hlt⟩

/-! ## Elementary facts about the chamber -/

/-- The trace component of `a` is contained in the side chamber of `a`. -/
theorem traceComponent_subset_sideChamber (γ : Work.Smooth.Jordan.PlaneCurve) (p : ℂ) (ε : ℝ)
    (a : ℂ) : traceComponent γ p ε a ⊆ sideChamber γ p ε a := by
  rw [sideChamber_eq]
  intro z hz
  exact Or.inr hz

/-- `a` lies in its own side chamber. -/
theorem mem_sideChamber {γ : Work.Smooth.Jordan.PlaneCurve} {p : ℂ} {ε : ℝ} {a : ℂ}
    (ha : a ∈ γ.trace ∩ Metric.ball p ε) : a ∈ sideChamber γ p ε a :=
  traceComponent_subset_sideChamber γ p ε a (mem_traceComponent ha)

/-- **The side chamber is open.** -/
theorem isOpen_sideChamber {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) {p : ℂ} {ε : ℝ}
    (hε : 0 < ε) {a : ℂ} (ha : a ∈ γ.trace ∩ Metric.ball p ε) :
    IsOpen (sideChamber γ p ε a) := by
  rw [Metric.isOpen_iff]
  intro z hz
  obtain ⟨hzB, hznot⟩ := hz
  have hzp : dist z p < ε := Metric.mem_ball.mp hzB
  by_cases hztr : z ∈ γ.trace
  · have hzC : z ∈ traceComponent γ p ε a := by
      by_contra hcon
      exact hznot ⟨⟨hztr, hzB⟩, hcon⟩
    obtain ⟨r, hr, hrsub⟩ := mem_traceComponent_open (γ := γ) hs hε ha hzC
    set r' : ℝ := min r (ε - dist z p) / 2 with hr'def
    have hr'pos : 0 < r' := by
      rw [hr'def]; exact div_pos (lt_min hr (by linarith)) two_pos
    have hr'le : r' ≤ r := by
      rw [hr'def]; linarith [min_le_left r (ε - dist z p)]
    have hr'p : r' ≤ ε - dist z p := by
      rw [hr'def]; linarith [min_le_right r (ε - dist z p)]
    refine ⟨r', hr'pos, ?_⟩
    intro w hw
    have hwz : dist w z < r' := Metric.mem_ball.mp hw
    have hwB : w ∈ Metric.ball p ε := by
      rw [Metric.mem_ball]
      calc dist w p ≤ dist w z + dist z p := dist_triangle _ _ _
        _ < r' + dist z p := by linarith
        _ ≤ (ε - dist z p) + dist z p := by linarith
        _ = ε := by ring
    rw [sideChamber_eq]
    by_cases hwtr : w ∈ γ.trace
    · refine Or.inr ?_
      have hrw : dist w z < r := lt_of_lt_of_le hwz hr'le
      exact hrsub ⟨hwtr, Metric.mem_ball.mpr hrw⟩
    · exact Or.inl ⟨hwB, hwtr⟩
  · obtain ⟨δ₁, hδ₁, hδ₁sub⟩ :=
      Metric.mem_nhds_iff.mp (γ.isClosed_trace.isOpen_compl.mem_nhds hztr)
    have hδ₂ : 0 < ε - dist z p := by rw [sub_pos]; exact hzp
    refine ⟨min δ₁ (ε - dist z p), lt_min hδ₁ hδ₂, ?_⟩
    intro w hw
    have hw1 : dist w z < δ₁ := lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _)
    have hw2 : dist w z < ε - dist z p :=
      lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_right _ _)
    have hwB : w ∈ Metric.ball p ε := by
      rw [Metric.mem_ball]
      calc dist w p ≤ dist w z + dist z p := dist_triangle _ _ _
        _ < (ε - dist z p) + dist z p := by linarith
        _ = ε := by ring
    have hwnt : w ∉ γ.trace := by
      have := hδ₁sub (Metric.mem_ball.mpr hw1); simpa using this
    rw [sideChamber_eq]
    exact Or.inl ⟨hwB, hwnt⟩


/-- **A simple closed curve inside a closed ball has its bounded side inside the open ball.** -/
theorem V_subset_ball_of_trace_subset_closedBall {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation γ) {p : ℂ} {ε : ℝ}
    (hsub : γ.trace ⊆ Metric.closedBall p ε) : S.V ⊆ Metric.ball p ε := by
  have hVcl : S.V ⊆ Metric.closedBall p ε := by
    intro v hv
    by_contra hvout
    rw [Metric.mem_closedBall, not_le] at hvout
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp S.bounded_V
    set w : ℝ → ℂ := fun t => v + t • (v - p) with hwdef
    have hwcont : Continuous w :=
      continuous_const.add (continuous_id'.smul continuous_const)
    have hdv : dist v p = ‖v - p‖ := dist_eq_norm v p
    have hd : 0 < ‖v - p‖ := by
      rcases lt_or_eq_of_le (norm_nonneg (v - p)) with hpos | hzero
      · exact hpos
      · exfalso
        have h1 := hsub (γ.mem_trace 0)
        rw [Metric.mem_closedBall, dist_eq_norm] at h1
        have h2 : dist v p = 0 := by rw [dist_eq_norm]; exact hzero.symm
        linarith [hvout, h1, h2, norm_nonneg (γ.γ 0 - p)]
    have hray : w '' Set.Ici (0 : ℝ) ⊆ γ.traceᶜ := by
      rintro z ⟨t, ht, rfl⟩
      rw [Set.mem_compl_iff]
      intro hzt
      have hb := hsub hzt
      rw [Metric.mem_closedBall, dist_eq_norm] at hb
      have ht0 : (0 : ℝ) ≤ t := ht
      have hnorm : ‖w t - p‖ = (1 + t) * ‖v - p‖ := by
        rw [hwdef]
        have h1 : v + t • (v - p) - p = (1 + t) • (v - p) := by module
        rw [h1, norm_smul, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1 + t)]
      rw [hnorm] at hb
      nlinarith [hvout, ht0, hdv, hb, norm_nonneg (v - p)]
    obtain ⟨t₁, ht₁⟩ : ∃ t : ℝ, 0 ≤ t ∧ R < ‖w t‖ := by
      obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖p‖) / ‖v - p‖)
      refine ⟨n, Nat.cast_nonneg n, ?_⟩
      have h1 : (R + ‖p‖) < (n : ℝ) * ‖v - p‖ := by
        have := (div_lt_iff₀ hd).mp hn
        linarith
      have h3 : w n = p + (1 + (n:ℝ)) • (v - p) := by rw [hwdef]; module
      have h2 : ‖w n‖ ≥ (1 + (n:ℝ)) * ‖v - p‖ - ‖p‖ := by
        rw [h3]
        have h4 := norm_sub_le (p + (1 + (n:ℝ)) • (v - p)) p
        rw [add_sub_cancel_left] at h4
        rw [norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 + (n:ℝ))] at h4
        linarith
      have h1' : R + ‖p‖ < (1 + (n:ℝ)) * ‖v - p‖ := by
        refine lt_of_lt_of_le h1 ?_
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      linarith [h1', h2]
    have hRtpre : IsPreconnected (w '' Set.Ici (0 : ℝ)) :=
      (isPreconnected_Ici).image w hwcont.continuousOn
    have hRtUV : w '' Set.Ici (0 : ℝ) ⊆ S.U ∪ S.V := by
      intro z hz
      have h := hray hz
      rw [← S.union_eq] at h
      exact h
    have hfarU : w t₁ ∈ S.U := by
      have h1 : w t₁ ∉ S.V := by
        intro hmem
        have := hR hmem
        rw [Metric.mem_closedBall, dist_zero_right] at this
        linarith [ht₁.2, this]
      rcases hRtUV ⟨t₁, ht₁.1, rfl⟩ with h | h
      · exact h
      · exact absurd h h1
    have hvR : v ∈ w '' Set.Ici (0 : ℝ) := ⟨0, by simp, by simp [hwdef]⟩
    have hfarR : w t₁ ∈ w '' Set.Ici (0 : ℝ) := ⟨t₁, ht₁.1, rfl⟩
    rcases hRtpre.subset_or_subset S.isOpen_U S.isOpen_V S.disjoint_UV hRtUV with h | h
    · exact (Set.disjoint_left.mp S.disjoint_UV (h hvR)) hv
    · exact (Set.disjoint_left.mp S.disjoint_UV hfarU) (h hfarR)
  intro v hv
  rw [Metric.mem_ball]
  by_contra hcon
  have hcon' : ε ≤ dist v p := not_lt.mp hcon
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp S.isOpen_V v hv
  have hex : ∃ z ∈ Metric.ball v r, dist v p < dist z p := by
    by_cases hvp : v = p
    · subst hvp
      refine ⟨v + (r/2 : ℂ), ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm]
        have h1 : v + (r/2 : ℂ) - v = ((r/2 : ℝ) : ℂ) := by push_cast; ring
        rw [h1, Complex.norm_real, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ r/2)]
        linarith
      · rw [dist_self, dist_eq_norm]
        have h1 : v + (r/2 : ℂ) - v = ((r/2 : ℝ) : ℂ) := by push_cast; ring
        rw [h1, Complex.norm_real, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ r/2)]
        linarith
    · set u : ℂ := ((‖v - p‖ : ℝ) : ℂ)⁻¹ * (v - p) with hudef
      have hnorm : ‖v - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvp)
      have hu : ‖u‖ = 1 := by
        rw [hudef, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
          inv_mul_cancel₀ hnorm]
      have hvu : v - p = ((‖v - p‖ : ℝ) : ℂ) * u := by
        rw [hudef, ← mul_assoc,
          mul_inv_cancel₀ (by exact_mod_cast hnorm : ((‖v - p‖ : ℝ) : ℂ) ≠ 0), one_mul]
      refine ⟨v + (r/2) • u, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm]
        have h1 : v + (r/2) • u - v = (r/2) • u := by rw [add_sub_cancel_left]
        rw [h1, norm_smul, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ r/2), hu, mul_one]
        linarith
      · rw [dist_eq_norm, dist_eq_norm]
        have h1 : v + (r/2) • u - p = ((‖v - p‖ + r / 2 : ℝ) : ℂ) * u := by
          calc v + (r/2) • u - p
              = (v - p) + (r/2) • u := by ring
            _ = ((‖v - p‖ : ℝ) : ℂ) * u + ((r/2 : ℝ) : ℂ) * u := by
                  conv_lhs => rw [hvu]
                  rw [Complex.real_smul]
            _ = ((‖v - p‖ + r / 2 : ℝ) : ℂ) * u := by push_cast; ring
        rw [h1, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (by linarith [norm_nonneg (v - p)] : (0:ℝ) ≤ ‖v - p‖ + r / 2),
          hu, mul_one]
        linarith
  obtain ⟨z, hzball, hzgt⟩ := hex
  have hzV : z ∈ S.V := hrsub hzball
  have hzcl : z ∈ Metric.closedBall p ε := hVcl hzV
  rw [Metric.mem_closedBall] at hzcl
  exact absurd hzcl (not_le.mpr (lt_of_le_of_lt hcon' hzgt))

/-- Reducing a real number modulo `2π` into a window `Ico c (c + 2π)`. -/
theorem exists_int_sub_mem_Ico (c x : ℝ) :
    ∃ k : ℤ, x - (k : ℝ) * (2 * Real.pi) ∈ Set.Ico c (c + 2 * Real.pi) := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlow : (⌊(x - c) / (2 * Real.pi)⌋ : ℤ) ≤ (x - c) / (2 * Real.pi) :=
    Int.floor_le ((x - c) / (2 * Real.pi))
  have hup : (x - c) / (2 * Real.pi) < ((⌊(x - c) / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one ((x - c) / (2 * Real.pi))
  have hk1 : (⌊(x - c) / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤ x - c := by
    have := (le_div_iff₀ hp).mp hlow
    linarith
  have hk2 : x - c < ((⌊(x - c) / (2 * Real.pi)⌋ : ℝ) + 1) * (2 * Real.pi) := by
    have := (div_lt_iff₀ hp).mp hup
    linarith
  exact ⟨⌊(x - c) / (2 * Real.pi)⌋, by
    rw [Set.mem_Ico]
    exact ⟨by linarith, by linarith⟩⟩

theorem traceComponentInterval {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple)
    {p : ℂ} {ε : ℝ} {a : ℂ} (ha : a ∈ γ.trace ∩ Metric.ball p ε)
    (hnot : ¬ γ.trace ⊆ Metric.ball p ε) :
    ∃ s₀ s₁ : ℝ, s₀ < s₁ ∧ s₁ - s₀ ≤ 2 * Real.pi ∧
      γ.γ s₀ ∈ Metric.sphere p ε ∧ γ.γ s₁ ∈ Metric.sphere p ε ∧
      Work.SphereJordan.traceComponent γ p ε a = γ.γ '' Set.Ioo s₀ s₁ := by
  obtain ⟨t₀, ht₀⟩ : ∃ t : ℝ, γ.γ t = a := ha.1
  have ht₀B : γ.γ t₀ ∈ Metric.ball p ε := by rw [ht₀]; exact ha.2
  set P : Set ℝ := {t : ℝ | γ.γ t ∈ Metric.ball p ε} with hP
  have hPopen : IsOpen P := Metric.isOpen_ball.preimage γ.cont
  have ht₀P : t₀ ∈ P := ht₀B
  set K : Set ℝ := connectedComponentIn P t₀ with hK
  have hKpre : IsPreconnected K := by rw [hK]; exact isPreconnected_connectedComponentIn
  have hKP : K ⊆ P := by rw [hK]; exact connectedComponentIn_subset P t₀
  have hKopen : IsOpen K := by rw [hK]; exact hPopen.connectedComponentIn
  have hKbdd : Bornology.IsBounded K := by
    by_contra hcon
    have hnotbdd : ¬ (BddAbove K ∧ BddBelow K) := by
      intro hb
      apply hcon
      rw [Metric.isBounded_iff_subset_closedBall (0 : ℝ)]
      obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := hb
      refine ⟨max |A| |B|, fun y hy => ?_⟩
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      by_cases hy0 : 0 ≤ y
      · rw [abs_of_nonneg hy0]
        exact le_trans (le_trans (hA hy) (le_abs_self A)) (le_max_left _ _)
      · rw [abs_of_neg (not_le.mp hy0)]
        have h1 : B ≤ y := hB hy
        have h2 : -y ≤ -B := by linarith
        exact le_trans (le_trans h2 (neg_le_abs B)) (le_max_right _ _)
    have hPuniv : P = Set.univ := by
      ext x
      constructor
      · intro _; trivial
      · intro _
        rcases not_and_or.mp hnotbdd with hAb | hBb
        · have hbig : ∀ y : ℝ, t₀ < y → y ∈ K := by
            intro y hy
            by_contra hyK
            apply hAb
            refine ⟨y, fun z hz => ?_⟩
            by_contra hzy
            have hyz : y < z := not_le.mp hzy
            have hconv : Set.Icc t₀ z ⊆ K := hKpre.ordConnected.out (mem_connectedComponentIn ht₀P) hz
            exact hyK (hconv ⟨le_of_lt hy, le_of_lt hyz⟩)
          obtain ⟨n, hn⟩ := exists_nat_gt ((t₀ - x) / (2 * Real.pi))
          have hp : (0:ℝ) < 2 * Real.pi := by positivity
          have hn' : t₀ < x + (n : ℝ) * (2 * Real.pi) := by
            have := (div_lt_iff₀ hp).mp hn
            linarith
          have hxP : γ.γ (x + (n : ℝ) * (2 * Real.pi)) ∈ Metric.ball p ε := hKP (hbig _ hn')
          rwa [show γ.γ (x + (n:ℝ) * (2*Real.pi)) = γ.γ x from by
            simpa using γ.apply_add_int_mul x (n : ℤ)] at hxP
        · have hsmall : ∀ y : ℝ, y < t₀ → y ∈ K := by
            intro y hy
            by_contra hyK
            apply hBb
            refine ⟨y, fun z hz => ?_⟩
            by_contra hzy
            have hzy' : z < y := not_le.mp hzy
            have hconv : Set.Icc z t₀ ⊆ K := hKpre.ordConnected.out hz (mem_connectedComponentIn ht₀P)
            exact hyK (hconv ⟨le_of_lt hzy', le_of_lt hy⟩)
          obtain ⟨n, hn⟩ := exists_nat_gt ((x - t₀) / (2 * Real.pi))
          have hp : (0:ℝ) < 2 * Real.pi := by positivity
          have hn' : x - (n : ℝ) * (2 * Real.pi) < t₀ := by
            have := (div_lt_iff₀ hp).mp hn
            linarith
          have hxP : γ.γ (x - (n : ℝ) * (2 * Real.pi)) ∈ Metric.ball p ε := hKP (hsmall _ hn')
          rwa [show γ.γ (x - (n:ℝ) * (2*Real.pi)) = γ.γ x from by
            have h := γ.apply_add_int_mul (x - (n:ℝ) * (2*Real.pi)) (n : ℤ)
            rw [show ((n : ℤ) : ℝ) * (2 * Real.pi) = (n:ℝ) * (2*Real.pi) from by
              push_cast; ring] at h
            have harg : x - (n:ℝ) * (2*Real.pi) + (n:ℝ) * (2*Real.pi) = x := by ring
            rw [harg] at h
            exact h.symm] at hxP
    have htr : γ.trace ⊆ Metric.ball p ε := by
      rintro z ⟨t, rfl⟩
      have : t ∈ P := by rw [hPuniv]; trivial
      exact this
    exact hnot htr
  obtain ⟨s₀, s₁, hKeq, hs₀t₀, ht₀s₁, hs₀P, hs₁P⟩ :=
    component_open_of_real_bounded hPopen ht₀P hKbdd
  have hKIoo : K = Set.Ioo s₀ s₁ := hKeq
  have hs₀s₁ : s₀ < s₁ := lt_trans hs₀t₀ ht₀s₁
  have hs₁s₀ : s₁ - s₀ ≤ 2 * Real.pi := by
    by_contra hcon
    have hcon' : s₀ + 2 * Real.pi < s₁ := by linarith
    have hs : s₀ + 2 * Real.pi ∈ K := by
      rw [hKIoo]; exact ⟨by linarith [Real.pi_pos], hcon'⟩
    have h1 : γ.γ (s₀ + 2 * Real.pi) ∈ Metric.ball p ε := hKP hs
    rw [show γ.γ (s₀ + 2 * Real.pi) = γ.γ s₀ from by
      simpa using γ.apply_add_int_mul s₀ 1] at h1
    exact hs₀P h1
  have hsphere₀ : γ.γ s₀ ∈ Metric.sphere p ε := by
    rw [Metric.mem_sphere]
    refine le_antisymm ?_ ?_
    · have hcl : s₀ ∈ closure K := by
        rw [hKIoo, Metric.mem_closure_iff]
        intro δ hδ
        set y : ℝ := s₀ + min (δ/2) ((s₁ - s₀)/2) with hy
        have hypos : 0 < min (δ/2) ((s₁ - s₀)/2) := lt_min (by linarith) (by linarith)
        refine ⟨y, ⟨?_, ?_⟩, ?_⟩
        · rw [hy]; linarith [hypos]
        · rw [hy]
          linarith [min_le_right (δ/2) ((s₁ - s₀)/2), hs₀s₁]
        · rw [Real.dist_eq, show s₀ - y = -(min (δ/2) ((s₁ - s₀)/2)) from by rw [hy]; ring,
            abs_neg, abs_of_pos hypos]
          linarith [min_le_left (δ/2) ((s₁ - s₀)/2)]
      have hmem : γ.γ s₀ ∈ closure (γ.γ '' K) :=
        image_closure_subset_closure_image γ.cont ⟨s₀, hcl, rfl⟩
      have hsubcl : γ.γ '' K ⊆ Metric.closedBall p ε := by
        rintro z ⟨t, htK, rfl⟩
        exact Metric.ball_subset_closedBall (hKP htK)
      exact Metric.mem_closedBall.mp ((Metric.isClosed_closedBall.closure_subset_iff).mpr hsubcl hmem)
    · exact not_lt.mp fun hlt => hs₀P (Metric.mem_ball.mpr hlt)
  have hsphere₁ : γ.γ s₁ ∈ Metric.sphere p ε := by
    rw [Metric.mem_sphere]
    refine le_antisymm ?_ ?_
    · have hcl : s₁ ∈ closure K := by
        rw [hKIoo, Metric.mem_closure_iff]
        intro δ hδ
        set y : ℝ := s₁ - min (δ/2) ((s₁ - s₀)/2) with hy
        have hypos : 0 < min (δ/2) ((s₁ - s₀)/2) := lt_min (by linarith) (by linarith)
        refine ⟨y, ⟨?_, ?_⟩, ?_⟩
        · rw [hy]
          linarith [min_le_right (δ/2) ((s₁ - s₀)/2), hs₀s₁]
        · rw [hy]; linarith [hypos]
        · rw [Real.dist_eq, show s₁ - y = min (δ/2) ((s₁ - s₀)/2) from by rw [hy]; ring,
            abs_of_pos hypos]
          linarith [min_le_left (δ/2) ((s₁ - s₀)/2)]
      have hmem : γ.γ s₁ ∈ closure (γ.γ '' K) :=
        image_closure_subset_closure_image γ.cont ⟨s₁, hcl, rfl⟩
      have hsubcl : γ.γ '' K ⊆ Metric.closedBall p ε := by
        rintro z ⟨t, htK, rfl⟩
        exact Metric.ball_subset_closedBall (hKP htK)
      exact Metric.mem_closedBall.mp ((Metric.isClosed_closedBall.closure_subset_iff).mpr hsubcl hmem)
    · exact not_lt.mp fun hlt => hs₁P (Metric.mem_ball.mpr hlt)
  have hCpre : IsPreconnected (γ.γ '' K) := hKpre.image γ.γ γ.cont.continuousOn
  have hCsub : γ.γ '' K ⊆ γ.trace ∩ Metric.ball p ε := by
    rintro z ⟨t, htK, rfl⟩
    exact ⟨⟨t, rfl⟩, hKP htK⟩
  have haK : a ∈ γ.γ '' K := ⟨t₀, by rw [hK]; exact mem_connectedComponentIn ht₀P, ht₀⟩
  have hAK : connectedComponentIn (γ.trace ∩ Metric.ball p ε) a = γ.γ '' K := by
    apply Set.Subset.antisymm
    · have hTpre : IsPreconnected (connectedComponentIn (γ.trace ∩ Metric.ball p ε) a) :=
        isPreconnected_connectedComponentIn
      have hclosed : closure (γ.γ '' K) ∩ (γ.trace ∩ Metric.ball p ε) ⊆ γ.γ '' K := by
        rintro z ⟨hzcl, hzt, hzB⟩
        have hKsub : K ⊆ Set.Icc s₀ s₁ := by rw [hKIoo]; exact Set.Ioo_subset_Icc_self
        have hcompact : IsCompact (γ.γ '' Set.Icc s₀ s₁) := isCompact_Icc.image γ.cont
        have hzIcc : z ∈ γ.γ '' Set.Icc s₀ s₁ :=
          (hcompact.isClosed.closure_subset_iff).mpr (Set.image_mono hKsub) hzcl
        obtain ⟨u, hu, huz⟩ := hzIcc
        rw [Set.mem_Icc] at hu
        rcases lt_or_eq_of_le hu.1 with hlt | hlt
        · rcases lt_or_eq_of_le hu.2 with hgt | hgt
          · exact ⟨u, by rw [hKIoo]; exact ⟨hlt, hgt⟩, huz⟩
          · exfalso
            have h1 : γ.γ s₁ ∈ Metric.ball p ε := by
              rw [hgt] at huz
              rw [← huz] at hzB
              exact hzB
            rw [Metric.mem_ball, Metric.mem_sphere.mp hsphere₁] at h1
            exact absurd h1 (lt_irrefl ε)
        · exfalso
          have h1 : γ.γ s₀ ∈ Metric.ball p ε := by
            rw [← hlt] at huz
            rw [← huz] at hzB
            exact hzB
          rw [Metric.mem_ball, Metric.mem_sphere.mp hsphere₀] at h1
          exact absurd h1 (lt_irrefl ε)
      have hloc : ∀ z : ℂ, z ∈ γ.γ '' K → ∃ ρ : ℝ, 0 < ρ ∧
          ∀ w : ℂ, w ∈ γ.trace → dist w z < ρ → w ∈ γ.γ '' K := by
        rintro z ⟨t, htK, rfl⟩
        have htI : t ∈ Set.Ioo s₀ s₁ := by rw [← hKIoo]; exact htK
        set E : Set ℝ := {r : ℝ | r ∈ Set.Icc s₀ (s₀ + 2 * Real.pi) ∧ r ∉ K} with hE
        have hEne : (γ.γ '' E).Nonempty :=
          ⟨γ.γ s₀, s₀, ⟨⟨le_refl _, by linarith⟩, fun h => hs₀P (hKP h)⟩, rfl⟩
        have hEclosed : IsClosed E := by
          rw [hE]
          exact isClosed_Icc.inter hKopen.isClosed_compl
        have hEcompact : IsCompact (γ.γ '' E) :=
          (isCompact_Icc.of_isClosed_subset hEclosed (by rw [hE]; exact Set.inter_subset_left)).image γ.cont
        have hEcl : IsClosed (γ.γ '' E) := hEcompact.isClosed
        have hmemE : γ.γ t ∉ γ.γ '' E := by
          rintro ⟨r, hrE, hrt⟩
          have hrI : r ∈ Set.Icc s₀ (s₀ + 2 * Real.pi) := hrE.1
          have hrK : r ∉ K := hrE.2
          obtain ⟨k, hk⟩ := Work.SphereJordan.gamma_eq_imp_mod hs hrt
          have hlt2 : |r - t| < 2 * Real.pi := by
            rw [abs_lt]
            constructor
            · linarith [hrI.1, htI.1, htI.2, hs₁s₀, hs₀s₁]
            · linarith [hrI.2, htI.1]
          have hk0 : k = 0 := by
            have hp : (0:ℝ) < 2 * Real.pi := by positivity
            have h2 : |r - t| = |(k:ℝ)| * (2 * Real.pi) := by rw [hk, abs_mul, abs_of_pos hp]
            rw [h2] at hlt2
            have h3 : |(k:ℝ)| < 1 := by nlinarith [hlt2, hp]
            have h4 : |k| < 1 := by
              have : ((|k| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact h3
              exact_mod_cast this
            exact Int.abs_lt_one_iff.mp h4
          have hrt' : r = t := by
            have h0 : r - t = 0 := by rw [hk, hk0]; push_cast; ring
            linarith
          exact hrK (by rw [hrt']; exact htK)
        obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hEcl.isOpen_compl (γ.γ t) hmemE
        refine ⟨ρ, hρ, ?_⟩
        intro w hwtr hwd
        obtain ⟨r, hrw⟩ := hwtr
        obtain ⟨k, hk⟩ := exists_int_sub_mem_Ico s₀ r
        set r' : ℝ := r - (k : ℝ) * (2 * Real.pi) with hr'def
        have hper : γ.γ r' = γ.γ r := by
          have h := γ.apply_add_int_mul r' k
          have harg : r' + (k:ℝ) * (2*Real.pi) = r := by rw [hr'def]; ring
          rw [harg] at h
          exact h.symm
        have hr'w : γ.γ r' = w := by rw [hper, hrw]
        by_contra hwK
        have hr'K : r' ∉ K := fun h => hwK (by rw [← hr'w]; exact ⟨r', h, rfl⟩)
        have hr'E : r' ∈ E := ⟨⟨hk.1, le_of_lt hk.2⟩, hr'K⟩
        have hball : γ.γ r' ∈ Metric.ball (γ.γ t) ρ :=
          Metric.mem_ball.mpr (by rw [hr'w]; exact hwd)
        exact hρsub hball ⟨r', hr'E, rfl⟩
      have hopen : (γ.trace ∩ Metric.ball p ε) ∩ closure ((γ.trace ∩ Metric.ball p ε) \ γ.γ '' K) ⊆
          (γ.trace ∩ Metric.ball p ε) \ γ.γ '' K := by
        rintro z ⟨hzT, hzcl⟩
        refine ⟨hzT, fun hzK => ?_⟩
        obtain ⟨ρ, hρ, hρloc⟩ := hloc z hzK
        obtain ⟨w, hw, hwd⟩ := Metric.mem_closure_iff.mp hzcl ρ hρ
        exact hw.2 (hρloc w hw.1.1 (by rw [dist_comm]; exact hwd))
      intro z hz
      have hzT : z ∈ γ.trace ∩ Metric.ball p ε := connectedComponentIn_subset _ _ hz
      have hsub2 : connectedComponentIn (γ.trace ∩ Metric.ball p ε) a ⊆
          closure (γ.γ '' K) ∪ closure ((γ.trace ∩ Metric.ball p ε) \ γ.γ '' K) := by
        intro y hy
        have hyT : y ∈ γ.trace ∩ Metric.ball p ε := connectedComponentIn_subset _ _ hy
        by_cases hyK : y ∈ γ.γ '' K
        · exact Or.inl (subset_closure hyK)
        · exact Or.inr (subset_closure ⟨hyT, hyK⟩)
      have hdisj : connectedComponentIn (γ.trace ∩ Metric.ball p ε) a ∩
          (closure (γ.γ '' K) ∩ closure ((γ.trace ∩ Metric.ball p ε) \ γ.γ '' K)) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro y ⟨hyA, hy1, hy2⟩
        have hyT : y ∈ γ.trace ∩ Metric.ball p ε := connectedComponentIn_subset _ _ hyA
        have hyK : y ∈ γ.γ '' K := hclosed ⟨hy1, hyT⟩
        exact (hopen ⟨hyT, hy2⟩).2 hyK
      rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hTpre)
        (closure (γ.γ '' K)) (closure ((γ.trace ∩ Metric.ball p ε) \ γ.γ '' K))
        isClosed_closure isClosed_closure hsub2 hdisj with h | h
      · exact hclosed ⟨h hz, hzT⟩
      · exfalso
        have ha2 : a ∈ closure ((γ.trace ∩ Metric.ball p ε) \ γ.γ '' K) :=
          h (mem_connectedComponentIn ha)
        exact (hopen ⟨ha, ha2⟩).2 haK
    · intro z hz
      exact hCpre.subset_connectedComponentIn haK hCsub hz
  refine ⟨s₀, s₁, hs₀s₁, hs₁s₀, hsphere₀, hsphere₁, ?_⟩
  show connectedComponentIn (γ.trace ∩ Metric.ball p ε) a = γ.γ '' Set.Ioo s₀ s₁
  rw [hAK, hKIoo]


/-! ## The main theorem -/

theorem chamberCrosscut {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple)
    (S : Work.Smooth.Jordan.PlaneSeparation γ) {p : ℂ} {ε : ℝ} {a : ℂ}
    (ha : a ∈ γ.trace ∩ Metric.ball p ε) :
    ∀ x y z : ℂ,
      x ∈ connectedComponentIn (Work.SphereJordan.sideChamber γ p ε a) a \ Work.SphereJordan.traceComponent γ p ε a →
      y ∈ connectedComponentIn (Work.SphereJordan.sideChamber γ p ε a) a \ Work.SphereJordan.traceComponent γ p ε a →
      z ∈ connectedComponentIn (Work.SphereJordan.sideChamber γ p ε a) a \ Work.SphereJordan.traceComponent γ p ε a →
      connectedComponentIn
          (connectedComponentIn (Work.SphereJordan.sideChamber γ p ε a) a \ Work.SphereJordan.traceComponent γ p ε a) x =
        connectedComponentIn
          (connectedComponentIn (Work.SphereJordan.sideChamber γ p ε a) a \ Work.SphereJordan.traceComponent γ p ε a) y ∨
      connectedComponentIn
          (connectedComponentIn (Work.SphereJordan.sideChamber γ p ε a) a \ Work.SphereJordan.traceComponent γ p ε a) x =
        connectedComponentIn
          (connectedComponentIn (Work.SphereJordan.sideChamber γ p ε a) a \ Work.SphereJordan.traceComponent γ p ε a) z ∨
      connectedComponentIn
          (connectedComponentIn (Work.SphereJordan.sideChamber γ p ε a) a \ Work.SphereJordan.traceComponent γ p ε a) y =
        connectedComponentIn
          (connectedComponentIn (Work.SphereJordan.sideChamber γ p ε a) a \ Work.SphereJordan.traceComponent γ p ε a) z := by
  intro x y z hx hy hz
  set A : Set ℂ := Work.SphereJordan.traceComponent γ p ε a with hA
  set X : Set ℂ := connectedComponentIn (Work.SphereJordan.sideChamber γ p ε a) a with hX
  have hε : 0 < ε := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp ha.2)
  have haA : a ∈ A := mem_traceComponent ha
  have hAX : A ⊆ X := by
    rw [hX]
    exact (isPreconnected_connectedComponentIn (x := a)
      (F := γ.trace ∩ Metric.ball p ε)).subset_connectedComponentIn haA
      (traceComponent_subset_sideChamber γ p ε a)
  have hXB : X ⊆ Metric.ball p ε := by
    intro w hw
    rw [hX] at hw
    exact sideChamber_subset_ball γ p ε a (connectedComponentIn_subset _ _ hw)
  have hXopen : IsOpen X := by
    rw [hX]
    exact (isOpen_sideChamber hs hε ha).connectedComponentIn
  have hXpre : IsPreconnected X := by rw [hX]; exact isPreconnected_connectedComponentIn
  have hXtrace : X ∩ γ.trace = A := by
    apply Set.Subset.antisymm
    · rintro w ⟨hwX, hwt⟩
      have hw2 : w ∈ sideChamber γ p ε a := by
        rw [hX] at hwX
        exact connectedComponentIn_subset _ _ hwX
      rw [sideChamber_eq] at hw2
      rcases hw2 with h | h
      · exact absurd hwt h.2
      · exact h
    · intro w hw
      exact ⟨hAX hw, traceComponent_subset_trace γ p ε a hw⟩
  have haB : a ∈ Metric.ball p ε := ha.2
  have hBpre : IsPreconnected (Metric.ball p ε) := (convex_ball p ε).isPreconnected
  by_cases hout : ∃ t : ℝ, ε < dist (γ.γ t) p
  · -- Case A: some trace point lies strictly outside the closed ball
    have hout' : ∃ t : ℝ, γ.γ t ∉ Metric.closedBall p ε := by
      obtain ⟨t, ht⟩ := hout
      exact ⟨t, fun h => absurd (Metric.mem_closedBall.mp h) (not_le.mpr ht)⟩
    obtain ⟨κ, hκinj, hκrange, hκint, -, hκ0, hκ1, hκeq⟩ :=
      exists_trace_crosscut (γ := γ) hs (z := a) ha hout'
    have hAκ : A = κ '' {t : Set.Icc (0 : ℝ) 1 | (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1} := hκeq
    have hκ0X : κ ⟨0, by norm_num⟩ ∉ X := fun h => by
      have h1 : κ ⟨0, by norm_num⟩ ∈ Metric.ball p ε := hXB h
      rw [Metric.mem_ball, Metric.mem_sphere.mp hκ0] at h1
      exact absurd h1 (lt_irrefl ε)
    have hκ1X : κ ⟨1, by norm_num⟩ ∉ X := fun h => by
      have h1 : κ ⟨1, by norm_num⟩ ∈ Metric.ball p ε := hXB h
      rw [Metric.mem_ball, Metric.mem_sphere.mp hκ1] at h1
      exact absurd h1 (lt_irrefl ε)
    have hintX : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 → κ t ∈ X := by
      intro t ht
      refine hAX ?_
      rw [hAκ]
      exact ⟨t, ht, rfl⟩
    have hset : X \ Set.range κ = X \ A := by
      apply Set.Subset.antisymm
      · rintro w ⟨hwX, hwr⟩
        refine ⟨hwX, fun hwA => hwr ?_⟩
        rw [hAκ] at hwA
        obtain ⟨t, ht, htw⟩ := hwA
        exact ⟨t, htw⟩
      · rintro w ⟨hwX, hwA⟩
        refine ⟨hwX, fun hwr => hwA ?_⟩
        obtain ⟨t, rfl⟩ := hwr
        have hmem : κ t ∈ X ∩ γ.trace := ⟨hwX, hκrange ⟨t, rfl⟩⟩
        rwa [hXtrace] at hmem
    rw [← hset] at hx hy hz
    have key := crosscutThm hXopen hXpre hκinj hκ0X hκ1X hintX x y z hx hy hz
    rw [hset] at key
    exact key
  · -- The trace lies in the closed ball
    have hsubCB : γ.trace ⊆ Metric.closedBall p ε := by
      rintro w ⟨t, rfl⟩
      rw [Metric.mem_closedBall]
      exact not_lt.mp fun h => hout ⟨t, h⟩
    by_cases hsub : γ.trace ⊆ Metric.ball p ε
    · -- Case B: the whole trace lies in the ball
      have hAeq : A = γ.trace := by
        have hpre : IsPreconnected (γ.trace ∩ Metric.ball p ε) := by
          rw [Set.inter_eq_left.mpr hsub]
          exact isPreconnected_range γ.cont
        have hsub' : connectedComponentIn (γ.trace ∩ Metric.ball p ε) a =
            γ.trace ∩ Metric.ball p ε :=
          Set.Subset.antisymm (connectedComponentIn_subset _ _)
            (hpre.subset_connectedComponentIn ha (Subset.refl _))
        have h1 : A = connectedComponentIn (γ.trace ∩ Metric.ball p ε) a := hA
        rw [h1, hsub', Set.inter_eq_left.mpr hsub]
      have hside : sideChamber γ p ε a = Metric.ball p ε := by
        have hthis : (γ.trace ∩ Metric.ball p ε) \ A = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro w ⟨hwt, hwA⟩
          exact hwA (by rw [hAeq]; exact hwt.1)
        rw [sideChamber, hthis, Set.sdiff_empty]
      have hXeq : X = Metric.ball p ε := by
        rw [hX, hside]
        exact Set.Subset.antisymm (connectedComponentIn_subset _ _)
          (hBpre.subset_connectedComponentIn haB (Subset.refl _))
      have hset : Metric.ball p ε \ γ.trace = X \ A := by
        rw [hXeq, hAeq]
      have hV : S.V ⊆ Metric.ball p ε := V_subset_ball_of_trace_subset_closedBall S hsubCB
      have hZempty : γ.trace ∩ (Metric.ball p ε)ᶜ = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro w ⟨hwt, hwB⟩
        exact hwB (hsub hwt)
      have hZ : IsPreconnected (γ.trace ∩ (Metric.ball p ε)ᶜ) := by
        rw [hZempty]; exact isPreconnected_empty
      rw [← hset] at hx hy hz
      have key := ball_sdiff_trace_atMostTwo S hsubCB hV hZ x y z hx hy hz
      rw [hset] at key
      exact key
    · -- Case C: some trace point lies on the sphere
      obtain ⟨s₀, s₁, hs01, hs1s0, hsp₀, hsp₁, hAeq⟩ := traceComponentInterval hs ha hsub
      rw [← hA] at hAeq
      have hnotP : γ.γ s₀ ∉ Metric.ball p ε := by
        rw [Metric.mem_ball, Metric.mem_sphere.mp hsp₀]
        exact lt_irrefl ε
      have hAcB : A ⊆ Metric.ball p ε := fun w hw => traceComponent_subset_ball γ p ε a hw
      by_cases hslt : s₁ - s₀ < 2 * Real.pi
      · -- Case C1: the arc is a proper crosscut of the ball
        have hspos : 0 < s₁ - s₀ := by linarith
        have hcont : Continuous fun t : Set.Icc (0 : ℝ) 1 => γ.γ (s₀ + (t : ℝ) * (s₁ - s₀)) :=
          γ.cont.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))
        let κ : C(Set.Icc (0 : ℝ) 1, ℂ) :=
          ⟨fun t => γ.γ (s₀ + (t : ℝ) * (s₁ - s₀)), hcont⟩
        have hκval : ∀ t : Set.Icc (0 : ℝ) 1, κ t = γ.γ (s₀ + (t : ℝ) * (s₁ - s₀)) := fun t => rfl
        have hκinj : Function.Injective κ := by
          intro u v huv
          have hu : s₀ + (u : ℝ) * (s₁ - s₀) ∈ Set.Icc s₀ s₁ :=
            ⟨by nlinarith [u.2.1, hspos], by nlinarith [u.2.2, hspos]⟩
          have hv : s₀ + (v : ℝ) * (s₁ - s₀) ∈ Set.Icc s₀ s₁ :=
            ⟨by nlinarith [v.2.1, hspos], by nlinarith [v.2.2, hspos]⟩
          have heq : γ.γ (s₀ + (u : ℝ) * (s₁ - s₀)) = γ.γ (s₀ + (v : ℝ) * (s₁ - s₀)) := by
            have h := huv
            rwa [hκval u, hκval v] at h
          have h2 := gammaInjOn_of_sub_lt hs hu hv hslt heq
          exact Subtype.ext (mul_right_cancel₀ (ne_of_gt hspos) (add_left_cancel h2))
        have hκ0 : κ ⟨0, by norm_num⟩ = γ.γ s₀ := by
          rw [hκval]; congr 1; ring
        have hκ1 : κ ⟨1, by norm_num⟩ = γ.γ s₁ := by
          rw [hκval]; congr 1; ring
        have hκ0X : κ ⟨0, by norm_num⟩ ∉ X := fun h => by
          have h1 : κ ⟨0, by norm_num⟩ ∈ Metric.ball p ε := hXB h
          rw [hκ0, Metric.mem_ball, Metric.mem_sphere.mp hsp₀] at h1
          exact absurd h1 (lt_irrefl ε)
        have hκ1X : κ ⟨1, by norm_num⟩ ∉ X := fun h => by
          have h1 : κ ⟨1, by norm_num⟩ ∈ Metric.ball p ε := hXB h
          rw [hκ1, Metric.mem_ball, Metric.mem_sphere.mp hsp₁] at h1
          exact absurd h1 (lt_irrefl ε)
        have hintX : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 → κ t ∈ X := by
          intro t ht
          have harg : s₀ + (t : ℝ) * (s₁ - s₀) ∈ Set.Ioo s₀ s₁ :=
            ⟨by nlinarith [ht.1, hspos], by nlinarith [ht.2, hspos]⟩
          have hmem : γ.γ (s₀ + (t : ℝ) * (s₁ - s₀)) ∈ γ.γ '' Set.Ioo s₀ s₁ := ⟨_, harg, rfl⟩
          rw [← hAeq] at hmem
          rw [hκval t]
          exact hAX hmem
        have hset : X \ Set.range κ = X \ A := by
          apply Set.Subset.antisymm
          · rintro w ⟨hwX, hwr⟩
            refine ⟨hwX, fun hwA => hwr ?_⟩
            rw [hAeq] at hwA
            obtain ⟨u, hu, huw⟩ := hwA
            refine ⟨⟨(u - s₀) / (s₁ - s₀), ⟨?_, ?_⟩⟩, ?_⟩
            · exact div_nonneg (by linarith [hu.1]) (le_of_lt hspos)
            · rw [div_le_one hspos]; linarith [hu.2]
            · rw [hκval]
              have harg : s₀ + ((u - s₀) / (s₁ - s₀)) * (s₁ - s₀) = u := by
                field_simp
                ring
              rw [harg]
              exact huw
          · rintro w ⟨hwX, hwA⟩
            refine ⟨hwX, fun hwr => hwA ?_⟩
            obtain ⟨t, rfl⟩ := hwr
            have hmem : κ t ∈ X ∩ γ.trace := by
              refine ⟨hwX, ?_⟩
              rw [hκval]
              exact ⟨_, rfl⟩
            rwa [hXtrace] at hmem
        rw [← hset] at hx hy hz
        have key := crosscutThm hXopen hXpre hκinj hκ0X hκ1X hintX x y z hx hy hz
        rw [hset] at key
        exact key
      · -- Case C2: the arc wraps around once
        have hs2 : s₁ - s₀ = 2 * Real.pi := le_antisymm hs1s0 (not_lt.mp hslt)
        have hlen : s₀ + 2 * Real.pi = s₁ := by linarith
        have hper0 : ∀ k : ℤ, γ.γ (s₀ + (k : ℝ) * (2 * Real.pi)) = γ.γ s₀ :=
          fun k => γ.apply_add_int_mul s₀ k
        have hBt : γ.trace ∩ Metric.ball p ε = A := by
          apply Set.Subset.antisymm
          · rintro w ⟨hwt, hwB⟩
            obtain ⟨t, rfl⟩ := hwt
            by_cases ht : ∃ k : ℤ, t = s₀ + (k : ℝ) * (2 * Real.pi)
            · obtain ⟨k, hk⟩ := ht
              exfalso
              have h1 := hwB
              rw [hk] at h1
              rw [hper0 k] at h1
              exact hnotP h1
            · push_neg at ht
              obtain ⟨k, hk⟩ := exists_int_sub_mem_Ioo (c := s₀) ht
              rw [hlen] at hk
              have hmem : γ.γ (t - (k : ℝ) * (2 * Real.pi)) ∈ A := by
                rw [hAeq]
                exact ⟨_, hk, rfl⟩
              have hper : γ.γ (t - (k : ℝ) * (2 * Real.pi)) = γ.γ t := by
                have h := γ.apply_add_int_mul (t - (k : ℝ) * (2 * Real.pi)) k
                have harg : t - (k : ℝ) * (2 * Real.pi) + (k : ℝ) * (2 * Real.pi) = t := by ring
                rw [harg] at h
                exact h.symm
              rwa [hper] at hmem
          · intro w hw
            exact ⟨traceComponent_subset_trace γ p ε a hw, hAcB hw⟩
        have hside : sideChamber γ p ε a = Metric.ball p ε := by
          have hthis : (γ.trace ∩ Metric.ball p ε) \ A = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro w ⟨hwt, hwA⟩
            rw [hBt] at hwt
            exact hwA hwt
          rw [sideChamber, hthis, Set.sdiff_empty]
        have hXeq : X = Metric.ball p ε := by
          rw [hX, hside]
          exact Set.Subset.antisymm (connectedComponentIn_subset _ _)
            (hBpre.subset_connectedComponentIn haB (Subset.refl _))
        have hset : Metric.ball p ε \ γ.trace = X \ A := by
          rw [hXeq]
          apply Set.Subset.antisymm
          · rintro w ⟨hwB, hwt⟩
            refine ⟨hwB, fun hwA => hwt ?_⟩
            rw [← hBt] at hwA
            exact hwA.1
          · rintro w ⟨hwB, hwA⟩
            refine ⟨hwB, fun hwt => hwA ?_⟩
            rw [← hBt]
            exact ⟨hwt, hwB⟩
        have hV : S.V ⊆ Metric.ball p ε := V_subset_ball_of_trace_subset_closedBall S hsubCB
        have hZeq : γ.trace ∩ (Metric.ball p ε)ᶜ = {γ.γ s₀} := by
          apply Set.Subset.antisymm
          · rintro w ⟨hwt, hwB⟩
            obtain ⟨t, rfl⟩ := hwt
            by_cases ht : ∃ k : ℤ, t = s₀ + (k : ℝ) * (2 * Real.pi)
            · obtain ⟨k, hk⟩ := ht
              rw [hk, hper0 k]
              exact Set.mem_singleton _
            · push_neg at ht
              obtain ⟨k, hk⟩ := exists_int_sub_mem_Ioo (c := s₀) ht
              rw [hlen] at hk
              have hmem : γ.γ (t - (k : ℝ) * (2 * Real.pi)) ∈ A := by
                rw [hAeq]
                exact ⟨_, hk, rfl⟩
              have hper : γ.γ (t - (k : ℝ) * (2 * Real.pi)) = γ.γ t := by
                have h := γ.apply_add_int_mul (t - (k : ℝ) * (2 * Real.pi)) k
                have harg : t - (k : ℝ) * (2 * Real.pi) + (k : ℝ) * (2 * Real.pi) = t := by ring
                rw [harg] at h
                exact h.symm
              rw [hper] at hmem
              exact absurd (hAcB hmem) hwB
          · rintro w rfl
            exact ⟨⟨_, rfl⟩, hnotP⟩
        have hZ : IsPreconnected (γ.trace ∩ (Metric.ball p ε)ᶜ) := by
          rw [hZeq]; exact isPreconnected_singleton
        rw [← hset] at hx hy hz
        have key := ball_sdiff_trace_atMostTwo S hsubCB hV hZ x y z hx hy hz
        rw [hset] at key
        exact key

end

end Work.SphereJordan
