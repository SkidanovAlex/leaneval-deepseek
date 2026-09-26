import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Topology.PlaneCurve.CruxBoundedComponentClean

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-- The connected component of `0` in a closed set whose component of `0` is bounded is compact. -/
theorem isCompact_connectedComponentIn_zero {F : Set ℂ} (hF : IsClosed F) (h0 : (0 : ℂ) ∈ F)
    (hbdd : Bornology.IsBounded (connectedComponentIn F (0 : ℂ))) :
    IsCompact (connectedComponentIn F (0 : ℂ)) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨?_, hbdd⟩
  rw [connectedComponentIn_eq_image h0]
  exact (hF.isClosedEmbedding_subtypeVal).isClosedMap _ isClosed_connectedComponent

/-- **Reduction.**  If `F` is closed and the component of `0` in `F` is bounded, then there is a
compact `U ⊆ F` containing `0` which is at *positive distance* from `F \ U`. -/
theorem exists_compact_gap {F : Set ℂ} (hF : IsClosed F) (h0 : (0 : ℂ) ∈ F)
    (hbdd : Bornology.IsBounded (connectedComponentIn F (0 : ℂ))) :
    ∃ (U : Set ℂ) (ρ : ℝ), IsCompact U ∧ (0 : ℂ) ∈ U ∧ U ⊆ F ∧ 0 < ρ ∧
      ∀ u ∈ U, ∀ v ∈ F, v ∉ U → ρ ≤ dist u v := by
  classical
  obtain ⟨C, hC⟩ := hbdd.exists_norm_le
  have hC0 : (0 : ℝ) ≤ C := by simpa using hC 0 (mem_connectedComponentIn h0)
  set R : ℝ := C + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hKball : connectedComponentIn F (0 : ℂ) ⊆ Metric.ball (0 : ℂ) R := by
    intro z hz
    have h := hC z hz
    rw [Metric.mem_ball, dist_zero_right, hRdef]
    linarith
  set M : Set ℂ := F ∩ Metric.closedBall (0 : ℂ) R with hMdef
  have hMclosed : IsClosed M := hF.inter Metric.isClosed_closedBall
  have hMbdd : Bornology.IsBounded M := Metric.isBounded_closedBall.subset inter_subset_right
  have hMcompact : IsCompact M := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hMclosed, hMbdd⟩
  have h0M : (0 : ℂ) ∈ M :=
    ⟨h0, by rw [Metric.mem_closedBall, dist_zero_right, norm_zero, hRdef]; linarith⟩
  have hsub : connectedComponentIn M (0 : ℂ) = connectedComponentIn F (0 : ℂ) := by
    refine Subset.antisymm (connectedComponentIn_mono 0 inter_subset_left) ?_
    refine (isPreconnected_connectedComponentIn).subset_connectedComponentIn
      (mem_connectedComponentIn h0) ?_
    intro z hz
    exact ⟨connectedComponentIn_subset F 0 hz, by
      have h := hC z hz
      rw [Metric.mem_closedBall, dist_zero_right, hRdef]; linarith⟩
  set S : Set ℂ := M ∩ Metric.sphere (0 : ℂ) R with hSdef
  have hSclosed : IsClosed S := hMclosed.inter Metric.isClosed_sphere
  have hSK : Disjoint S (connectedComponentIn F (0 : ℂ)) := by
    rw [Set.disjoint_left]
    rintro z ⟨-, hzs⟩ hzK
    have h1 : ‖z‖ < R := by
      have h := hKball hzK; rw [Metric.mem_ball, dist_zero_right] at h; exact h
    have h2 : ‖z‖ = R := by rw [Metric.mem_sphere, dist_zero_right] at hzs; exact hzs
    linarith
  haveI : CompactSpace M := isCompact_iff_compactSpace.mp hMcompact
  have hper : ∀ x : M, (x : ℂ) ∈ S → ∃ Z : Set M, IsClopen Z ∧ (⟨0, h0M⟩ : M) ∈ Z ∧ x ∉ Z := by
    intro x hxS
    have hxK : (x : ℂ) ∉ connectedComponentIn F (0 : ℂ) := Set.disjoint_left.mp hSK hxS
    have hxnot : x ∉ connectedComponent (⟨0, h0M⟩ : M) := by
      intro hxc
      refine hxK ?_
      have hcc := connectedComponentIn_eq_image h0M
      rw [← hsub, hcc]
      exact ⟨x, hxc, rfl⟩
    have hcc := connectedComponent_eq_iInter_isClopen (⟨0, h0M⟩ : M)
    by_contra hcon
    push_neg at hcon
    apply hxnot
    rw [hcc]
    exact Set.mem_iInter.mpr (fun s => hcon s.1 s.2.1 s.2.2)
  choose Z hZcl hZ0 hZx using hper
  set S' : Set M := {x : M | (x : ℂ) ∈ S} with hS'def
  have hS'closed : IsClosed S' := IsClosed.preimage continuous_subtype_val hSclosed
  have hS'compact : IsCompact S' := hS'closed.isCompact
  have hcov : S' ⊆ ⋃ x : S', {y : M | y ∉ Z x.1 x.2} := by
    rintro ⟨y, hyS⟩ hy
    exact Set.mem_iUnion.mpr ⟨⟨⟨y, hyS⟩, hy⟩, hZx ⟨y, hyS⟩ hy⟩
  obtain ⟨t, ht⟩ := hS'compact.elim_finite_subcover (fun x : S' => {y : M | y ∉ Z x.1 x.2})
    (fun x => (hZcl x.1 x.2).isClosed.isOpen_compl) hcov
  set Z₀ : Set M := ⋂ x ∈ t, Z x.1 x.2 with hZ₀def
  have hZ₀cl : IsClopen Z₀ := by
    rw [hZ₀def]
    exact Set.Finite.isClopen_biInter t.finite_toSet (fun x _ => hZcl x.1 x.2)
  have hZ₀0 : (⟨0, h0M⟩ : M) ∈ Z₀ := by
    rw [hZ₀def]; exact Set.mem_iInter₂.mpr (fun x _ => hZ0 x.1 x.2)
  have hZ₀S : Disjoint Z₀ S' := by
    rw [Set.disjoint_left]
    rintro x hxZ hxS
    obtain ⟨y, hyt, hyx⟩ := Set.mem_iUnion₂.mp (ht hxS)
    exact hyx (Set.mem_iInter₂.mp hxZ y hyt)
  set U : Set ℂ := Subtype.val '' Z₀ with hUdef
  have hUcompact : IsCompact U := hZ₀cl.isClosed.isCompact.image continuous_subtype_val
  have hU0 : (0 : ℂ) ∈ U := ⟨⟨0, h0M⟩, hZ₀0, rfl⟩
  have hUF : U ⊆ F := by rintro z ⟨x, -, rfl⟩; exact (x.2).1
  have hUball : U ⊆ Metric.ball (0 : ℂ) R := by
    rintro z ⟨x, hxZ, rfl⟩
    rw [Metric.mem_ball, dist_zero_right]
    have hxMcl : ‖(x : ℂ)‖ ≤ R := by
      have h := (x.2).2; rw [Metric.mem_closedBall, dist_zero_right] at h; exact h
    rcases lt_or_eq_of_le hxMcl with hlt | heq
    · exact hlt
    · exfalso
      have hxS : (x : ℂ) ∈ S := ⟨x.2, by rw [Metric.mem_sphere, dist_zero_right, heq]⟩
      exact (Set.disjoint_left.mp hZ₀S hxZ) hxS
  obtain ⟨z₀, hz₀U, hz₀max⟩ := hUcompact.exists_isMaxOn ⟨0, hU0⟩ continuous_norm.continuousOn
  have hz₀lt : ‖z₀‖ < R := by
    have h := hUball hz₀U; rw [Metric.mem_ball, dist_zero_right] at h; exact h
  have hρ₂ : 0 < R - ‖z₀‖ := by linarith
  have hdist_pos : ∃ ρ₁ > 0, ∀ z ∈ Z₀, ∀ w : M, w ∉ Z₀ → ρ₁ ≤ dist z w := by
    by_cases hne : (Z₀ᶜ : Set M).Nonempty
    · obtain ⟨w₀, hw₀⟩ := hne
      have hcompact : IsCompact ((Z₀ᶜ : Set M)) := hZ₀cl.compl.isClosed.isCompact
      obtain ⟨p₁, hp₁, hp₁min⟩ := (hZ₀cl.isClosed.isCompact.prod hcompact).exists_isMinOn
        ⟨(⟨0, h0M⟩, w₀), hZ₀0, hw₀⟩ (continuous_fst.dist continuous_snd).continuousOn
      refine ⟨dist p₁.1 p₁.2, ?_, ?_⟩
      · refine dist_pos.mpr (fun h => ?_)
        exact hp₁.2 (h ▸ hp₁.1)
      · rintro z hz w hw
        have hw' : w ∈ (Z₀ᶜ : Set M) := by simpa using hw
        have hmem : (z, w) ∈ Z₀ ×ˢ (Z₀ᶜ : Set M) := ⟨hz, hw'⟩
        exact hp₁min hmem
    · refine ⟨1, one_pos, fun z hz w hw => absurd ⟨w, hw⟩ hne⟩
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := hdist_pos
  refine ⟨U, min ρ₁ (R - ‖z₀‖) / 2, hUcompact, hU0, hUF, ?_, ?_⟩
  · have h2 : (0:ℝ) ≤ min ρ₁ (R - ‖z₀‖) := le_min hρ₁pos.le hρ₂.le
    positivity
  rintro u ⟨zu, hzu, rfl⟩ v hv hvU
  have hmin0 : (0:ℝ) ≤ min ρ₁ (R - ‖z₀‖) := le_min hρ₁pos.le hρ₂.le
  have hle₁ : min ρ₁ (R - ‖z₀‖) / 2 ≤ ρ₁ := by
    have h1 : min ρ₁ (R - ‖z₀‖) ≤ ρ₁ := min_le_left _ _; linarith
  have hle₂ : min ρ₁ (R - ‖z₀‖) / 2 ≤ R - ‖z₀‖ := by
    have h1 : min ρ₁ (R - ‖z₀‖) ≤ R - ‖z₀‖ := min_le_right _ _; linarith
  by_cases hvM : v ∈ M
  · have hv' : (⟨v, hvM⟩ : M) ∉ Z₀ := fun h => hvU ⟨⟨v, hvM⟩, h, rfl⟩
    have h := hρ₁ zu hzu ⟨v, hvM⟩ hv'
    rw [Subtype.dist_eq] at h
    exact le_trans hle₁ h
  · have hvR : R < ‖v‖ := by
      by_contra hcon
      push_neg at hcon
      exact hvM ⟨hv, by rw [Metric.mem_closedBall, dist_zero_right]; linarith⟩
    have hzuU : (zu : ℂ) ∈ U := ⟨zu, hzu, rfl⟩
    have hle : ‖(zu : ℂ)‖ ≤ ‖z₀‖ := hz₀max hzuU
    have hge : R - ‖z₀‖ ≤ dist (zu : ℂ) v := by
      rw [dist_comm, dist_eq_norm]
      have h2 : ‖v‖ - ‖(zu : ℂ)‖ ≤ ‖v - (zu : ℂ)‖ :=
        le_trans (le_abs_self _) (abs_norm_sub_norm_le v _)
      linarith
    exact le_trans hle₂ hge


/-- A closed loop with a lift whose increment is `2 * π * I` has index `1`. -/
theorem loopIndex_eq_of_lift_one {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0)
    (hloop : c 0 = c 1) (Λ : C(unitInterval, ℂ)) (hΛ : ∀ t, Complex.exp (Λ t) = c t)
    (hincr : Λ 1 - Λ 0 = 2 * ↑Real.pi * Complex.I) : loopIndex c = 1 := by
  have h := loopIndex_spec c hc hloop Λ hΛ
  rw [hincr] at h
  have h2 : ((loopIndex c : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) =
      (1 : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    rw [← h]; ring
  exact_mod_cast mul_right_cancel₀ two_pi_I_ne_zero h2

/-- The circle of radius `t > 0` about the origin, as a loop, has index `1`. -/
theorem loopIndex_circle (t : ℝ) (ht : 0 < t) :
    loopIndex (⟨fun s : unitInterval => (t : ℂ) * Complex.exp (2 * ↑Real.pi * Complex.I * (s : ℝ)),
      by fun_prop⟩ : C(unitInterval, ℂ)) = 1 := by
  set c : C(unitInterval, ℂ) :=
    ⟨fun s : unitInterval => (t : ℂ) * Complex.exp (2 * ↑Real.pi * Complex.I * (s : ℝ)),
      by fun_prop⟩ with hcdef
  have hc : ∀ s, c s ≠ 0 := by
    intro s
    simp only [hcdef, ContinuousMap.coe_mk]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)) (Complex.exp_ne_zero _)
  have key0 : Complex.exp (2 * ↑Real.pi * Complex.I * (0 : ℂ)) = 1 := by
    rw [mul_zero, Complex.exp_zero]
  have key1 : Complex.exp (2 * ↑Real.pi * Complex.I * (1 : ℂ)) = 1 := by
    rw [mul_one, Complex.exp_eq_one_iff]
    exact ⟨1, by push_cast; ring⟩
  have hloop : c 0 = c 1 := by
    have e0 : ((0 : unitInterval) : ℝ) = 0 := by norm_num
    have e1 : ((1 : unitInterval) : ℝ) = 1 := by norm_num
    simp only [hcdef, ContinuousMap.coe_mk, e0, e1, Complex.ofReal_zero, Complex.ofReal_one]
    rw [key0, key1, mul_one]
  set Λ : C(unitInterval, ℂ) :=
    ⟨fun s : unitInterval => (Real.log t : ℂ) + 2 * ↑Real.pi * Complex.I * (s : ℝ),
      by fun_prop⟩ with hΛdef
  have hΛ : ∀ s, Complex.exp (Λ s) = c s := by
    intro s
    simp only [hΛdef, hcdef, ContinuousMap.coe_mk]
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ht]
  have hincr : Λ 1 - Λ 0 = 2 * ↑Real.pi * Complex.I := by
    simp only [hΛdef, ContinuousMap.coe_mk]
    rw [show ((1 : unitInterval) : ℝ) = 1 by norm_num, show ((0 : unitInterval) : ℝ) = 0 by norm_num]
    push_cast
    ring
  exact loopIndex_eq_of_lift_one hc hloop Λ hΛ hincr

/-- **The logarithmic preimage of a compact set lies in a half-plane.**  If `U ⊆ ℂ` is compact then
every `w` with `exp w ∈ U` satisfies `Re w ≤ M` for a suitable `M` (namely `log` of a norm bound
for `U`).  Consequently the half-plane `{M < Re w}` is free of the lift `{w | exp w ∈ U}` — this is
the part of the logarithmic picture that *compactness* supplies. -/
theorem exp_preimage_subset_halfplane {U : Set ℂ} (hU : IsCompact U) :
    ∃ M : ℝ, ∀ w : ℂ, Complex.exp w ∈ U → w.re ≤ M := by
  obtain ⟨R, hR⟩ := hU.isBounded.exists_norm_le
  refine ⟨Real.log R, fun w hw => ?_⟩
  have h1 : Real.exp w.re ≤ R := by
    have h := hR (Complex.exp w) hw
    rwa [Complex.norm_exp] at h
  by_cases hR0 : R ≤ 0
  · exact absurd (h1.trans hR0) (not_le.mpr (Real.exp_pos w.re))
  · calc w.re = Real.log (Real.exp w.re) := (Real.log_exp w.re).symm
      _ ≤ Real.log R := Real.log_le_log (Real.exp_pos w.re) h1

/-- **A path in the logarithmic plane produces the loop.**  If `Λ : [0,1] → ℂ` is a continuous
path whose exponential avoids a set `F` and which is translated by `2 π I` at its endpoint, then
`t ↦ exp (Λ t)` is a closed loop avoiding `F` whose index about `0` is exactly `1`.

This reduces the existence of a non-zero-index loop in the complement of `F` to the existence of a
path in the complement of the *logarithmic preimage* `{w | exp w ∈ F}` joining a point to its
translate by the period `2 π I` (the covering-space formulation of "winding once around `0`"). -/
theorem loop_index_one_of_exp_path {F : Set ℂ} (Λ : C(unitInterval, ℂ))
    (hΛ : ∀ t, Complex.exp (Λ t) ∉ F) (hincr : Λ 1 = Λ 0 + 2 * ↑Real.pi * Complex.I) :
    ∃ c : C(unitInterval, ℂ), (∀ t, c t ∉ F) ∧ (∀ t, c t ≠ 0) ∧ c 0 = c 1 ∧ loopIndex c = 1 := by
  have hkey : Complex.exp (2 * ↑Real.pi * Complex.I) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨1, by push_cast; ring⟩
  have hper : Complex.exp (Λ 1) = Complex.exp (Λ 0) := by
    rw [hincr, Complex.exp_add, hkey, mul_one]
  refine ⟨⟨fun t : unitInterval => Complex.exp (Λ t), by fun_prop⟩, ?_, ?_, ?_, ?_⟩
  · intro t; exact hΛ t
  · intro t; exact Complex.exp_ne_zero _
  · show Complex.exp (Λ 0) = Complex.exp (Λ 1); exact hper.symm
  · have hincr' : Λ 1 - Λ 0 = 2 * ↑Real.pi * Complex.I := by rw [hincr]; ring
    exact loopIndex_eq_of_lift_one (fun t => Complex.exp_ne_zero _) hper.symm Λ
      (fun t => rfl) hincr'

/-- **The target in the bounded case.**  If `F` is closed, contains `0`, and is *bounded*, then the
circle of radius `e^(M+1)` (where `F ⊆ closedBall 0 (e^M)`) is a loop avoiding `F` of index `1`.

The proof goes through the logarithmic plane: by `exp_preimage_subset_halfplane` the lift of `F` is
contained in `{Re w ≤ M}`, so the straight segment from `M+1` to `M+1 + 2πI` avoids the lift, and
`loop_index_one_of_exp_path` converts that segment (whose exponential is the circle of radius
`e^(M+1)`) into the loop. -/
theorem exists_loop_of_isBounded {F : Set ℂ} (hF : IsClosed F) (h0 : (0 : ℂ) ∈ F)
    (hbdd : Bornology.IsBounded F) :
    ∃ c : C(unitInterval, ℂ), (∀ t, c t ∉ F) ∧ (∀ t, c t ≠ 0) ∧ c 0 = c 1
      ∧ loopIndex c ≠ 0 := by
  have hcpt : IsCompact F := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hF, hbdd⟩
  obtain ⟨M, hM⟩ := exp_preimage_subset_halfplane hcpt
  set Λ : C(unitInterval, ℂ) :=
    ⟨fun t : unitInterval => ((M + 1 : ℝ) : ℂ) + 2 * ↑Real.pi * Complex.I * (t : ℝ),
      by fun_prop⟩ with hΛdef
  have hre : ∀ t : unitInterval, (2 * ↑Real.pi * Complex.I * (t : ℝ) : ℂ).re = 0 := by
    intro t
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    norm_num
  have hΛre : ∀ t : unitInterval, (Λ t).re = M + 1 := by
    intro t
    simp only [hΛdef, ContinuousMap.coe_mk, Complex.add_re, Complex.ofReal_re]
    rw [hre t, add_zero]
  have hΛmem : ∀ t : unitInterval, Complex.exp (Λ t) ∉ F := by
    intro t hmem
    have h := hM (Λ t) hmem
    rw [hΛre t] at h
    linarith
  have hΛ1 : Λ 1 = Λ 0 + 2 * ↑Real.pi * Complex.I := by
    simp only [hΛdef, ContinuousMap.coe_mk]
    rw [show ((1 : unitInterval) : ℝ) = 1 by norm_num,
      show ((0 : unitInterval) : ℝ) = 0 by norm_num]
    push_cast
    ring
  obtain ⟨c, hcF, hc0, hcloop, hidx⟩ := loop_index_one_of_exp_path Λ hΛmem hΛ1
  exact ⟨c, hcF, hc0, hcloop, by rw [hidx]; exact one_ne_zero⟩

/-- **From a Jordan curve enclosing `0` to the loop.**  If `γ` is a continuous `2π`-periodic curve
injective on one period, avoiding a closed set `F ∋ 0`, and `0` lies in a *bounded* complementary
component of the trace of `γ`, then `t ↦ γ (2π t)` is a loop avoiding `F`, avoiding `0`, closed, of
non-zero index about `0`.

The index input is the (axiom-clean) crux for Jordan curves,
`Work.Smooth.SphereJordan.windNumber_ne_zero_of_bounded_component`: for a simple closed curve,
`0` lying in a bounded complementary component forces the winding number about `0` to be non-zero.
The only bookkeeping is that `windNumber γ _ 0` is by definition the index of the loop
`t ↦ γ (2π t) - 0`, which agrees pointwise with `t ↦ γ (2π t)`. -/
theorem exists_loop_of_jordan {F : Set ℂ} (h0 : (0 : ℂ) ∈ F) {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) (havoid : ∀ t, γ t ∉ F)
    (hbdd : Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ (0 : ℂ))) :
    ∃ c : C(unitInterval, ℂ), (∀ t, c t ∉ F) ∧ (∀ t, c t ≠ 0) ∧ c 0 = c 1
      ∧ loopIndex c ≠ 0 := by
  have hz : (0 : ℂ) ∉ Set.range γ := by
    rintro ⟨t, ht⟩
    exact havoid t (ht ▸ h0)
  have hwn : windNumber γ hγ 0 ≠ 0 :=
    windNumber_ne_zero_of_bounded_component hγ hper hinj hz hbdd
  set c : C(unitInterval, ℂ) := curveLoop γ hγ with hc
  have hc_apply : ∀ t : unitInterval, c t = γ (2 * Real.pi * (t : ℝ)) := fun t => rfl
  have hne : ∀ t : unitInterval, c t ≠ 0 := by
    intro t h
    refine hz ⟨2 * Real.pi * (t : ℝ), ?_⟩
    rw [hc_apply t] at h; exact h
  have hloop : c 0 = c 1 := by
    have e0 : (((0 : unitInterval) : ℝ)) = 0 := by norm_num
    have e1 : (((1 : unitInterval) : ℝ)) = 1 := by norm_num
    simp only [hc_apply, e0, e1, mul_zero, mul_one]
    simpa using (hper 0).symm
  have hmem : ∀ t : unitInterval, c t ∉ F := by
    intro t h
    exact havoid _ (by rw [hc_apply t] at h; exact h)
  refine ⟨c, hmem, hne, hloop, ?_⟩
  intro hzero
  apply hwn
  have hcongr : loopIndex (curveLoop (fun t => γ t - 0) (hγ.sub continuous_const))
      = loopIndex c := by
    refine loopIndex_congr (fun t => ?_) ?_ ?_ ?_ ?_
    · show γ (2 * Real.pi * (t : ℝ)) - 0 = c t
      rw [hc_apply t, sub_zero]
    · intro t
      show γ (2 * Real.pi * (t : ℝ)) - 0 ≠ 0
      rw [sub_zero]
      exact hne t
    · exact hne
    · show γ (2 * Real.pi * (((0 : unitInterval) : ℝ))) - 0
          = γ (2 * Real.pi * (((1 : unitInterval) : ℝ))) - 0
      have h := hloop
      simp only [hc_apply] at h
      simpa using h
    · exact hloop
  rw [windNumber, hcongr, hzero]
