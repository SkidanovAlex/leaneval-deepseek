import Mathlib
import Submission.Work.Drive.CleanDiscsDefs

/-!
# Auxiliary lemmas for `Work.Drive.WeakDatumStepOfSign`

The single surgery step for the weak disc datum: given the structural data `InnermostSignData` of
the innermost trace `K = κ i₀`, one cuts the disc `D.e` along `K`, replaces the cap by the pushed
null-homotopy `β` of the curve `D.curves i₀` and pushes off the resulting map along the collar.

This file isolates the elementary ingredients of that construction:

* the region facts for the planar Jordan–Schoenflies cap (`hsch_range_eq` etc.);
* the homeomorphism `phiHome : 𝔻 ≃ₜ Set.range hsch.e` and the value of its inverse;
* the identity `β (phiHome.symm z) = D.e z` on the trace (the putty that makes the cut-and-paste
  map continuous and boundary-fixing);
* the bump functions `tubeBump` (a tube around the trace) and `deltaFun` (the signed push amount);
* `continuous_phi`: the cut-and-paste map is continuous.
-/

open Classical
open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.SurgStrict
open Work.CoreTopology

variable {ψ : R3 ≃ₜ R3} {PD : PushData ψ} {D : WeakDatum ψ} {S : InnermostSignData ψ PD D}

/-! ## The region of the Schoenflies cap -/

/-- The image of the boundary circle under the Schoenflies embedding is the trace. -/
theorem hsch_sphere_image :
    S.hsch.e '' {z : Work.Smooth.Jordan.Disc | ‖(z : ℂ)‖ = 1} = (D.kappa S.i₀).trace := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨θ, rfl⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz
    exact ⟨θ, (S.hsch.boundary θ).symm⟩
  · rintro _ ⟨θ, rfl⟩
    refine ⟨Work.Smooth.Jordan.circlePoint θ, ?_, S.hsch.boundary θ⟩
    show ‖((Work.Smooth.Jordan.circlePoint θ : Work.Smooth.Jordan.Disc) : ℂ)‖ = 1
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

/-- The range of the Schoenflies embedding is the bounded side together with the trace. -/
theorem hsch_range_subset :
    Set.range S.hsch.e ⊆ S.hsch.V ∪ (D.kappa S.i₀).trace := by
  rintro _ ⟨z, rfl⟩
  have hzle : ‖(z : ℂ)‖ ≤ 1 := by
    have h := z.2; rwa [Metric.mem_closedBall, dist_zero_right] at h
  rcases lt_or_eq_of_le hzle with hlt | heq
  · left
    rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S.hsch]
    exact ⟨z, hlt, rfl⟩
  · right
    rw [← hsch_sphere_image]
    exact ⟨z, heq, rfl⟩

/-- The bounded side is contained in the range of the Schoenflies embedding. -/
theorem hsch_V_subset_range : S.hsch.V ⊆ Set.range S.hsch.e := by
  intro z hz; rw [S.hsch.range_e]; exact subset_closure hz

theorem kappa_trace_subset_ball : (D.kappa S.i₀).trace ⊆ Metric.closedBall (0:ℂ) 1 :=
  fun z hz => by obtain ⟨t, rfl⟩ := hz; exact D.kappa_mem S.i₀ t

/-- The bounded side of the curve avoids the unit circle. -/
theorem not_mem_V_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : z ∉ S.hsch.V := by
  intro hzV
  have hsub : Set.range S.hsch.e ⊆ Metric.closedBall (0:ℂ) 1 :=
    Work.Smooth.Jordan.plane_schoenflies_convex S.hsch (convex_closedBall _ _)
      Metric.isClosed_closedBall kappa_trace_subset_ball
  have hVball : S.hsch.V ⊆ Metric.closedBall (0:ℂ) 1 :=
    fun w hw => hsub (by rw [S.hsch.range_e]; exact subset_closure hw)
  have hVint : S.hsch.V ⊆ interior (Metric.closedBall (0:ℂ) 1) :=
    calc S.hsch.V = interior S.hsch.V := (S.hsch.isOpen_V.interior_eq).symm
      _ ⊆ interior (Metric.closedBall (0:ℂ) 1) := interior_mono hVball
  rw [interior_closedBall (0:ℂ) one_ne_zero] at hVint
  have h2 := hVint hzV
  rw [Metric.mem_ball, dist_zero_right] at h2
  linarith

/-- The range of the Schoenflies embedding is *exactly* the bounded side together with the trace. -/
theorem hsch_range_eq : Set.range S.hsch.e = S.hsch.V ∪ (D.kappa S.i₀).trace := by
  apply Set.Subset.antisymm hsch_range_subset
  rintro z (h | h)
  · exact hsch_V_subset_range h
  · obtain ⟨t, ht⟩ := h
    exact ⟨Work.Smooth.Jordan.circlePoint t, by rw [S.hsch.boundary]; exact ht⟩

theorem kappa_trace_subset_range : (D.kappa S.i₀).trace ⊆ Set.range S.hsch.e :=
  fun z hz => by rw [hsch_range_eq]; exact Or.inr hz

/-- A point of the range of norm one is on the trace. -/
theorem mem_trace_of_mem_range_of_norm_one {z : ℂ} (hzr : z ∈ Set.range S.hsch.e)
    (hz : ‖z‖ = 1) : z ∈ (D.kappa S.i₀).trace := by
  rcases hsch_range_subset hzr with h | h
  · exact absurd h (not_mem_V_of_norm_one hz)
  · exact h

/-- The trace of any other curve is disjoint from the range of the Schoenflies embedding. -/
theorem disjoint_trace_range {j : D.ι} (hj : j ≠ S.i₀) :
    Disjoint (Set.range (D.kappa j).γ) (Set.range S.hsch.e) := by
  rw [Set.disjoint_left]
  intro z hzj hzr
  rcases hsch_range_subset hzr with h | h
  · exact Set.disjoint_left.mp (S.outside j) hzj h
  · exact Set.disjoint_left.mp (D.kappa_disj hj) hzj h

theorem isClosed_range_e : IsClosed (Set.range S.hsch.e) := by
  rw [S.hsch.range_e]; exact isClosed_closure

/-! ## The homeomorphism of the cap -/

/-- The Schoenflies embedding, as a homeomorphism onto its range. -/
noncomputable def phiHome : Work.InnermostDisk.Disc ≃ₜ Set.range S.hsch.e :=
  (S.hsch.e.continuous.isClosedEmbedding S.hsch.inj).toIsEmbedding.toHomeomorph

theorem phiHome_symm_val (w : Set.range S.hsch.e) :
    S.hsch.e (phiHome (S := S).symm w) = (w : ℂ) := by
  have h1 : (phiHome (S := S) (phiHome (S := S).symm w) : ℂ) = (w : ℂ) :=
    congrArg Subtype.val (Homeomorph.apply_symm_apply (phiHome (S := S)) w)
  rwa [show (phiHome (S := S) (phiHome (S := S).symm w) : ℂ) = S.hsch.e _ from rfl] at h1

/-! ## The agreement of the cap with the old disc along the trace -/

/-- On the trace, the pushed null-homotopy `β` of the curve `D.curves i₀` agrees with the old disc
map `D.e`.  This is what makes the cut-and-paste map continuous and boundary-fixing. -/
theorem beta_agrees {β : C(Work.InnermostDisk.Disc, R3)}
    (hβbdy : ∀ θ : ℝ, β (Work.CoreTopology.circlePoint θ) = (D.curves S.i₀).γ θ)
    {z : Work.InnermostDisk.Disc} (hzK : (z : ℂ) ∈ (D.kappa S.i₀).trace)
    (hmem : (z : ℂ) ∈ Set.range S.hsch.e) :
    β (phiHome (S := S).symm ⟨(z : ℂ), hmem⟩) = D.e z := by
  obtain ⟨t, ht⟩ := hzK
  have hw : phiHome (S := S).symm ⟨(z:ℂ), hmem⟩ = Work.Smooth.Jordan.circlePoint t := by
    apply S.hsch.inj
    rw [phiHome_symm_val, S.hsch.boundary t]
    exact ht.symm
  have hβ1 : β (phiHome (S := S).symm ⟨(z:ℂ), hmem⟩) = β (Work.CoreTopology.circlePoint t) := by
    rw [hw]
    congr 1
  rw [hβ1, hβbdy t]
  have hsub : (z : Work.InnermostDisk.Disc) = ⟨(D.kappa S.i₀).γ t, D.kappa_mem S.i₀ t⟩ := by
    apply Subtype.ext
    exact ht.symm
  rw [hsub, D.maps_kappa S.i₀ t]

/-! ## The signed push amount -/

theorem abs_sigma : |S.σ| = 1 := by rcases S.hσ with h | h <;> rw [h] <;> norm_num
theorem sigma_mul_self : S.σ * S.σ = 1 := by rcases S.hσ with h | h <;> rw [h] <;> norm_num
theorem sigma_ne_zero : S.σ ≠ 0 := by
  intro h0; have := abs_sigma (S := S); rw [h0] at this; norm_num at this

/-- A bump that is `1` on the trace and `0` at distance at least `S.r` from it. -/
noncomputable def tubeBump (z : Work.InnermostDisk.Disc) : ℝ :=
  max 0 (min 1 ((S.r - Metric.infDist (z : ℂ) (Set.range (D.kappa S.i₀).γ)) * (2/S.r)))

theorem tubeBump_cont : Continuous (tubeBump (S := S)) := by
  unfold tubeBump
  fun_prop

theorem tubeBump_nonneg (z : Work.InnermostDisk.Disc) : 0 ≤ tubeBump (S := S) z := le_max_left _ _

theorem tubeBump_le_one (z : Work.InnermostDisk.Disc) : tubeBump (S := S) z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem tubeBump_eq_zero {z : Work.InnermostDisk.Disc}
    (h : S.r ≤ Metric.infDist (z : ℂ) (Set.range (D.kappa S.i₀).γ)) :
    tubeBump (S := S) z = 0 := by
  unfold tubeBump
  have h2 : (0:ℝ) < 2/S.r := div_pos (by norm_num) S.hr
  have h1 : (S.r - Metric.infDist (z : ℂ) (Set.range (D.kappa S.i₀).γ)) * (2/S.r) ≤ 0 := by
    have : S.r - Metric.infDist (z : ℂ) (Set.range (D.kappa S.i₀).γ) ≤ 0 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg this (le_of_lt h2)
  have h3 : min 1 ((S.r - Metric.infDist (z : ℂ) (Set.range (D.kappa S.i₀).γ)) * (2/S.r)) ≤ 0 :=
    le_trans (min_le_right _ _) h1
  rw [max_eq_left h3]

theorem tubeBump_eq_one_of_mem {z : Work.InnermostDisk.Disc}
    (hz : (z : ℂ) ∈ Set.range (D.kappa S.i₀).γ) : tubeBump (S := S) z = 1 := by
  have h0 : Metric.infDist (z : ℂ) (Set.range (D.kappa S.i₀).γ) = 0 := by
    have hle := Metric.infDist_le_dist_of_mem (x := (z:ℂ)) hz
    rw [dist_self] at hle
    linarith [Metric.infDist_nonneg (x := (z:ℂ)) (s := Set.range (D.kappa S.i₀).γ)]
  unfold tubeBump
  rw [h0]
  have hr' : S.r ≠ 0 := ne_of_gt S.hr
  have h2 : (S.r - 0) * (2/S.r) = 2 := by field_simp; ring
  rw [h2]
  norm_num

/-- The signed push amount: non-zero with the sign `S.σ` inside the tube around the trace, zero on
the boundary circle of the disc and at distance at least `S.r` from the trace. -/
noncomputable def deltaFun (z : Work.InnermostDisk.Disc) : ℝ :=
  (S.σ/4) * (1 - ‖(z : ℂ)‖) * tubeBump (S := S) z

theorem deltaFun_cont : Continuous (deltaFun (S := S)) := by
  unfold deltaFun tubeBump
  fun_prop

theorem deltaFun_abs_le (z : Work.InnermostDisk.Disc) : |deltaFun (S := S) z| ≤ 1/4 := by
  have hzle : ‖(z:ℂ)‖ ≤ 1 := by
    have h := z.2; rwa [Metric.mem_closedBall, dist_zero_right] at h
  have hz0 : (0:ℝ) ≤ ‖(z:ℂ)‖ := norm_nonneg _
  have hnn : 0 ≤ 1 - ‖(z:ℂ)‖ := by linarith
  have h1 : |S.σ/4| = 1/4 := by rw [abs_div, abs_sigma]; norm_num
  have htb : 0 ≤ tubeBump (S := S) z := tubeBump_nonneg z
  calc |deltaFun (S := S) z| = |S.σ/4| * |1 - ‖(z:ℂ)‖| * |tubeBump (S := S) z| := by
        rw [deltaFun, abs_mul, abs_mul]
    _ = (1/4) * (1 - ‖(z:ℂ)‖) * tubeBump (S := S) z := by
        rw [h1, abs_of_nonneg hnn, abs_of_nonneg htb]
    _ ≤ (1/4) * 1 * 1 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
        · exact tubeBump_le_one z
        · exact htb
        · norm_num
    _ = 1/4 := by norm_num

theorem deltaFun_sign {z : Work.InnermostDisk.Disc} (h : deltaFun (S := S) z ≠ 0) :
    0 < S.σ * deltaFun (S := S) z := by
  have hnn : 0 ≤ 1 - ‖(z:ℂ)‖ := by linarith [norm_nonneg (z:ℂ), (by
    have h := z.2; rwa [Metric.mem_closedBall, dist_zero_right] at h : ‖(z:ℂ)‖ ≤ 1)]
  have htb : 0 ≤ tubeBump (S := S) z := tubeBump_nonneg z
  have hprod : 0 < (1 - ‖(z:ℂ)‖) * tubeBump (S := S) z := by
    rcases lt_or_eq_of_le hnn with h1 | h1
    · rcases lt_or_eq_of_le htb with h2 | h2
      · positivity
      · exfalso; apply h; unfold deltaFun; rw [h2.symm]; ring
    · exfalso; apply h; unfold deltaFun; rw [h1.symm]; ring
  have hσ4 : S.σ * (S.σ/4) = 1/4 := by
    field_simp; nlinarith [sigma_mul_self (S := S)]
  have key : S.σ * deltaFun (S := S) z = (1/4) * ((1 - ‖(z:ℂ)‖) * tubeBump (S := S) z) := by
    unfold deltaFun
    rw [show S.σ * (S.σ/4 * (1 - ‖(z:ℂ)‖) * tubeBump (S := S) z)
        = (S.σ * (S.σ/4)) * ((1 - ‖(z:ℂ)‖) * tubeBump (S := S) z) from by ring, hσ4]
  rw [key]
  exact mul_pos (by norm_num) hprod

theorem deltaFun_eq_zero_of_far {z : Work.InnermostDisk.Disc}
    (h : S.r ≤ Metric.infDist (z : ℂ) (Set.range (D.kappa S.i₀).γ)) :
    deltaFun (S := S) z = 0 := by
  unfold deltaFun; rw [tubeBump_eq_zero h]; ring

theorem deltaFun_circlePoint (θ : ℝ) :
    deltaFun (S := S) (Work.CoreTopology.circlePoint θ) = 0 := by
  unfold deltaFun
  have h : ‖((Work.CoreTopology.circlePoint θ : Work.InnermostDisk.Disc) : ℂ)‖ = 1 := by
    rw [Work.CoreTopology.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
  rw [h]; ring

theorem deltaFun_ne_zero_of_mem {z : Work.InnermostDisk.Disc}
    (hz : (z : ℂ) ∈ Set.range (D.kappa S.i₀).γ) (hzlt : ‖(z : ℂ)‖ < 1) :
    deltaFun (S := S) z ≠ 0 := by
  unfold deltaFun
  rw [tubeBump_eq_one_of_mem hz]
  have hσ4 : S.σ/4 ≠ 0 := div_ne_zero (sigma_ne_zero (S := S)) (by norm_num)
  have h2 : (1 - ‖(z:ℂ)‖) ≠ 0 := by intro hc; linarith
  exact mul_ne_zero (mul_ne_zero hσ4 h2) one_ne_zero

theorem norm_le_one_disc (z : Work.InnermostDisk.Disc) : ‖(z : ℂ)‖ ≤ 1 := by
  have h := z.2; rwa [Metric.mem_closedBall, dist_zero_right] at h

/-! ## The cut-and-paste map and its push-off -/

/-- The cut-and-paste map: the pushed null-homotopy `β` of the curve of the innermost trace on the
cap of that trace, the old disc map `D.e` away from the bounded side. -/
noncomputable def phiMap (β : C(Work.InnermostDisk.Disc, R3))
    (z : Work.InnermostDisk.Disc) : R3 :=
  if hz : (z : ℂ) ∈ Set.range S.hsch.e then
    β (phiHome (S := S).symm ⟨(z : ℂ), hz⟩) else D.e z

theorem phiMap_of_mem {β : C(Work.InnermostDisk.Disc, R3)} {z : Work.InnermostDisk.Disc}
    (hz : (z : ℂ) ∈ Set.range S.hsch.e) :
    phiMap (S := S) β z = β (phiHome (S := S).symm ⟨(z : ℂ), hz⟩) := by
  unfold phiMap; rw [dif_pos hz]

theorem phiMap_of_not_mem {β : C(Work.InnermostDisk.Disc, R3)} {z : Work.InnermostDisk.Disc}
    (hz : (z : ℂ) ∉ Set.range S.hsch.e) : phiMap (S := S) β z = D.e z := by
  unfold phiMap; rw [dif_neg hz]

theorem continuous_phi {β : C(Work.InnermostDisk.Disc, R3)}
    (hβbdy : ∀ θ : ℝ, β (Work.CoreTopology.circlePoint θ) = (D.curves S.i₀).γ θ) :
    Continuous (phiMap (S := S) β) := by
  classical
  have hAclosed : IsClosed {z : Work.InnermostDisk.Disc | (z:ℂ) ∈ Set.range S.hsch.e} :=
    (isClosed_range_e (S := S)).preimage continuous_subtype_val
  have hBclosed : IsClosed {z : Work.InnermostDisk.Disc | (z:ℂ) ∉ S.hsch.V} :=
    (S.hsch.isOpen_V.isClosed_compl).preimage continuous_subtype_val
  have hcover : {z : Work.InnermostDisk.Disc | (z:ℂ) ∈ Set.range S.hsch.e}
      ∪ {z : Work.InnermostDisk.Disc | (z:ℂ) ∉ S.hsch.V} = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    by_cases hz : (z:ℂ) ∈ S.hsch.V
    · exact Or.inl (hsch_V_subset_range hz)
    · exact Or.inr hz
  have h1 : ContinuousOn (phiMap (S := S) β)
      {z : Work.InnermostDisk.Disc | (z:ℂ) ∈ Set.range S.hsch.e} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : ({z : Work.InnermostDisk.Disc | (z:ℂ) ∈ Set.range S.hsch.e}).domRestrict
          (phiMap (S := S) β)
        = fun w : {z : Work.InnermostDisk.Disc | (z:ℂ) ∈ Set.range S.hsch.e} =>
            β (phiHome (S := S).symm ⟨((w : Work.InnermostDisk.Disc) : ℂ), w.2⟩) := by
      funext w
      change phiMap (S := S) β (w : Work.InnermostDisk.Disc) = _
      rw [phiMap_of_mem (S := S)
        (show (((w : Work.InnermostDisk.Disc) : ℂ) ∈ Set.range S.hsch.e) from w.2)]
    rw [heq]
    refine β.continuous.comp ((phiHome (S := S)).symm.continuous.comp ?_)
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun w => w.2)
  have h2 : ContinuousOn (phiMap (S := S) β)
      {z : Work.InnermostDisk.Disc | (z:ℂ) ∉ S.hsch.V} := by
    refine ContinuousOn.congr D.e.continuous.continuousOn (fun z hz => ?_)
    by_cases hmem : (z:ℂ) ∈ Set.range S.hsch.e
    · have hK : (z:ℂ) ∈ (D.kappa S.i₀).trace := by
        rcases hsch_range_subset hmem with h' | h'
        · exact absurd h' hz
        · exact h'
      rw [phiMap_of_mem (S := S) hmem]
      exact beta_agrees (S := S) hβbdy hK hmem
    · rw [phiMap_of_not_mem (S := S) hmem]
  have hglue := h1.union_of_isClosed h2 hAclosed hBclosed
  rw [hcover, continuousOn_univ] at hglue
  exact hglue

/-- The pushed cut-and-paste map. -/
noncomputable def EMap (β : C(Work.InnermostDisk.Disc, R3))
    (z : Work.InnermostDisk.Disc) : R3 :=
  PD.pushP (phiMap (S := S) β z) (deltaFun (S := S) z)

theorem EMap_apply {β : C(Work.InnermostDisk.Disc, R3)} (z : Work.InnermostDisk.Disc) :
    EMap (S := S) β z = PD.pushP (phiMap (S := S) β z) (deltaFun (S := S) z) := rfl

theorem EMap_cont {β : C(Work.InnermostDisk.Disc, R3)}
    (hβbdy : ∀ θ : ℝ, β (Work.CoreTopology.circlePoint θ) = (D.curves S.i₀).γ θ) :
    Continuous (EMap (S := S) β) := by
  refine PD.hcont.comp ((continuous_phi (S := S) hβbdy).prodMk (deltaFun_cont (S := S)))

end Work.Drive.SurgStrict
