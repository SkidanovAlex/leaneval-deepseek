import Mathlib
import Submission.Work.Smooth.SphereJordan.brouwer_disc
import Submission.Work.Smooth.JordanSeparation.ComplHelpers
import Submission.Work.Smooth.JordanSeparation.exists_continuum_separating
import Submission.Work.Smooth.SphereJordan.range_eq_of_subset_of_periodic

/-!
# Maehara's Lemma 1: the components of the complement of a Jordan curve

For a continuous `2π`-periodic curve `γ : ℝ → ℂ` which is injective on one period and whose
complement is not connected, the frontier of every connected component of the complement is the
whole trace of `γ`.

The proof is the one of R. Maehara (*The Jordan curve theorem via the Brouwer fixed point
theorem*, Amer. Math. Monthly **91** (1984), 637-646, Lemma 1): if `∂U` were a proper subset of the
trace, it would be contained in a compact sub-arc `A` of the trace; a continuous retraction
`r : ℂ → A` (Tietze extension of the inverse parametrisation, then composition with the
parametrisation) is used to glue `r` on `U` with the identity off `U`, giving a fixed-point-free
self-map of a large disc, contradicting Brouwer's fixed point theorem
(`Work.Smooth.SphereJordan.brouwer_disc`).
-/

namespace Work.Topology.PlaneCurve

open Set Metric

noncomputable section

/-! ## Brouwer's theorem on a disc, and the fixed-point-free map -/

/-- **Brouwer's fixed point theorem for a closed disc of arbitrary centre and radius.** -/
theorem brouwer_closedBall (o : ℂ) {R : ℝ} (hR : 0 < R)
    (Φ : C(Metric.closedBall o R, Metric.closedBall o R)) : ∃ x, Φ x = x := by
  classical
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR
  have hmem : ∀ z : Work.Smooth.SphereJordan.Disc,
      o + (R : ℂ) * (z : ℂ) ∈ Metric.closedBall o R := by
    intro z
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hR.le]
    have hz := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    calc R * ‖(z : ℂ)‖ ≤ R * 1 := mul_le_mul_of_nonneg_left hz hR.le
      _ = R := mul_one R
  let T : Work.Smooth.SphereJordan.Disc → Metric.closedBall o R :=
    fun z => ⟨o + (R : ℂ) * (z : ℂ), hmem z⟩
  have hTcont : Continuous T :=
    Continuous.subtype_mk (f := fun z : Work.Smooth.SphereJordan.Disc => o + (R : ℂ) * (z : ℂ))
      (by fun_prop) hmem
  let valFun : Work.Smooth.SphereJordan.Disc → ℂ :=
    fun z => (((Φ (T z) : Metric.closedBall o R) : ℂ) - o) / R
  have hnorm : ∀ z, ‖valFun z‖ ≤ 1 := by
    intro z
    have h1 : ‖((Φ (T z) : Metric.closedBall o R) : ℂ) - o‖ ≤ R := by
      have h2 := (Φ (T z)).2
      rwa [Metric.mem_closedBall, dist_eq_norm] at h2
    have h2 : ‖valFun z‖ = ‖((Φ (T z) : Metric.closedBall o R) : ℂ) - o‖ / R := by
      simp only [valFun, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    rw [h2]
    exact (div_le_iff₀ hR).mpr (by simpa using h1)
  have hmem2 : ∀ z, valFun z ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro z; rw [Metric.mem_closedBall, dist_zero_right]; exact hnorm z
  have hvalcont : Continuous valFun := by
    apply Continuous.div_const
    fun_prop
  let Ψ : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc) :=
    ⟨fun z => ⟨valFun z, hmem2 z⟩, hvalcont.subtype_mk hmem2⟩
  obtain ⟨z, hz⟩ := Work.Smooth.SphereJordan.brouwer_disc Ψ
  refine ⟨T z, ?_⟩
  have hzv : valFun z = (z : ℂ) := by
    simpa [Ψ] using congrArg (fun w : Work.Smooth.SphereJordan.Disc => (w : ℂ)) hz
  have hmain : ((Φ (T z) : Metric.closedBall o R) : ℂ) = o + (z : ℂ) * R := by
    have h3 : ((Φ (T z) : Metric.closedBall o R) : ℂ) - o = valFun z * R := by
      show ((Φ (T z) : Metric.closedBall o R) : ℂ) - o =
        ((((Φ (T z) : Metric.closedBall o R) : ℂ) - o) / R) * R
      rw [div_mul_cancel₀ _ hRne]
    rw [hzv] at h3
    linear_combination h3
  apply Subtype.ext
  rw [hmain]
  show o + (z : ℂ) * R = o + (R : ℂ) * (z : ℂ)
  ring

/-- A continuous self-map of a closed disc that misses the centre and fixes the boundary sphere
pointwise contradicts Brouwer's fixed point theorem. -/
theorem false_of_misses_center_fixes_sphere (o : ℂ) {R : ℝ} (hR : 0 < R)
    (q : C(Metric.closedBall o R, Metric.closedBall o R)) (hq : ∀ z, (q z : ℂ) ≠ o)
    (hfix : ∀ z : Metric.closedBall o R, (z : ℂ) ∈ Metric.sphere o R → q z = z) : False := by
  classical
  have hRne : R ≠ 0 := ne_of_gt hR
  have hrefl : ∀ w : ℂ, (2 * o - w) ∈ Metric.sphere o R ↔ w ∈ Metric.sphere o R := by
    intro w
    rw [Metric.mem_sphere, Metric.mem_sphere, dist_eq_norm, dist_eq_norm,
      show 2 * o - w - o = -(w - o) by ring, norm_neg]
  set p : ℂ → ℂ := fun w => o + (R / ‖w - o‖) • (w - o) with hpdef
  have hp_mem : ∀ w : ℂ, w ≠ o → p w ∈ Metric.sphere o R := by
    intro w hw
    have h0 : ‖w - o‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw)
    rw [Metric.mem_sphere, dist_eq_norm]
    show ‖o + (R / ‖w - o‖) • (w - o) - o‖ = R
    rw [show o + (R / ‖w - o‖) • (w - o) - o = (R / ‖w - o‖) • (w - o) by abel]
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hR.le (norm_nonneg _))]
    field_simp
  have hp_self : ∀ w : ℂ, ‖w - o‖ = R → p w = w := by
    intro w hw
    show o + (R / ‖w - o‖) • (w - o) = w
    rw [hw, div_self hRne, one_smul]
    abel
  have hp_contAt : ∀ w : ℂ, w ≠ o → ContinuousAt p w := by
    intro w hw
    have hne : ‖w - o‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw)
    have hnum : ContinuousAt (fun x : ℂ => ‖x - o‖) w :=
      (continuousAt_id.sub continuousAt_const).norm
    have hdiv : ContinuousAt (fun x : ℂ => R / ‖x - o‖) w :=
      ContinuousAt.div continuousAt_const hnum hne
    have hsub : ContinuousAt (fun x : ℂ => x - o) w := continuousAt_id.sub continuousAt_const
    exact (hdiv.smul hsub).const_add o
  let q' : C(Metric.closedBall o R, ℂ) :=
    ⟨fun z => (q z : ℂ), continuous_subtype_val.comp q.continuous⟩
  have hq' : ∀ z, q' z = (q z : ℂ) := fun z => rfl
  have hq'ne : ∀ z, q' z ≠ o := fun z => hq z
  have hpsphere : ∀ z, p (q' z) ∈ Metric.sphere o R := fun z => hp_mem _ (hq'ne z)
  let Ψ : Metric.closedBall o R → Metric.closedBall o R := fun z =>
    ⟨2 * o - p (q' z), by
      have h2 : ‖2 * o - p (q' z) - o‖ = R := by
        have h1 : ‖p (q' z) - o‖ = R := by
          have := hpsphere z
          rwa [Metric.mem_sphere, dist_eq_norm] at this
        rw [show 2 * o - p (q' z) - o = -(p (q' z) - o) by ring, norm_neg, h1]
      rw [Metric.mem_closedBall, dist_eq_norm]
      linarith [h2, hR.le]⟩
  have hcont : Continuous fun z : Metric.closedBall o R => p (q' z) :=
    continuous_iff_continuousAt.mpr
      fun z => (hp_contAt (q' z) (hq'ne z)).comp q'.continuous.continuousAt
  have hΨcont : Continuous Ψ := (continuous_const.sub hcont).subtype_mk (fun z => (Ψ z).2)
  obtain ⟨z, hz⟩ := brouwer_closedBall o hR ⟨Ψ, hΨcont⟩
  have hz' : 2 * o - p (q' z) = (z : ℂ) := by
    have := congrArg (fun w : Metric.closedBall o R => (w : ℂ)) hz
    simpa [Ψ] using this
  have hzsphere : (z : ℂ) ∈ Metric.sphere o R := by
    rw [← hz']
    exact (hrefl (p (q' z))).mpr (hpsphere z)
  have hqz : q' z = (z : ℂ) := by
    have h1 := hfix z hzsphere
    have := congrArg (fun w : Metric.closedBall o R => (w : ℂ)) h1
    simpa [q'] using this
  have hpz : p (z : ℂ) = (z : ℂ) := by
    apply hp_self
    rwa [Metric.mem_sphere, dist_eq_norm] at hzsphere
  rw [hqz, hpz] at hz'
  have h4 : (z : ℂ) = o := by
    have h6 : 2 * o = (z : ℂ) + (z : ℂ) := sub_eq_iff_eq_add.mp hz'
    exact mul_left_cancel₀ two_ne_zero (by rw [h6, two_mul])
  have h5 : ‖(z : ℂ) - o‖ = 0 := by rw [h4]; simp
  have h6 : ‖(z : ℂ) - o‖ = R := by
    rwa [Metric.mem_sphere, dist_eq_norm] at hzsphere
  rw [h6] at h5
  exact hRne h5

/-! ## The two disc contradictions (the "gluing" engines) -/

/-- **Bounded case.**  Let `A` be the range of a retraction `r` of the plane, `U` an open set with
`frontier U ⊆ A` and `U ∩ A = ∅`, and suppose `U` lies in a disc `D` of centre `o ∈ U` with
`A ⊆ D`.  Then the map which equals `r` on `U` and the identity outside `U` is a continuous
self-map of `D` missing `o` and fixing `∂D`, contradicting Brouwer. -/
theorem false_of_retraction_bounded {A : Set ℂ} {r : C(ℂ, ℂ)}
    (hr1 : ∀ a ∈ A, r a = a) (hr2 : ∀ z, r z ∈ A)
    {U : Set ℂ} (hfr : frontier U ⊆ A) (hUA : Disjoint U A)
    {o : ℂ} {R : ℝ} (hR : 0 < R) (hoU : o ∈ U) (hUball : U ⊆ Metric.ball o R)
    (hAD : A ⊆ Metric.closedBall o R) : False := by
  classical
  have hcont : Continuous (U.piecewise (fun z => r z) id) := by
    refine continuous_piecewise (f := fun z => r z) (g := id) (s := U) ?_ ?_ ?_
    · intro a ha; exact hr1 a (hfr ha)
    · exact r.continuous.continuousOn
    · exact continuousOn_id
  have hmap : ∀ z : Metric.closedBall o R,
      U.piecewise (fun z => r z) id (z : ℂ) ∈ Metric.closedBall o R := by
    intro z
    by_cases h : (z : ℂ) ∈ U
    · rw [Set.piecewise_eq_of_mem _ _ _ h]; exact hAD (hr2 _)
    · rw [Set.piecewise_eq_of_notMem _ _ _ h]; exact z.2
  let Q : C(Metric.closedBall o R, Metric.closedBall o R) :=
    ⟨fun z => ⟨U.piecewise (fun z => r z) id (z : ℂ), hmap z⟩,
      (hcont.comp continuous_subtype_val).subtype_mk hmap⟩
  have hQ : ∀ z : Metric.closedBall o R,
      (Q z : ℂ) = U.piecewise (fun z => r z) id (z : ℂ) := fun z => rfl
  refine false_of_misses_center_fixes_sphere o hR Q ?_ ?_
  · intro z
    rw [hQ z]
    by_cases h : (z : ℂ) ∈ U
    · rw [Set.piecewise_eq_of_mem _ _ _ h]
      intro hcon
      have hmem : o ∈ U ∩ A := ⟨hoU, by rw [← hcon]; exact hr2 (z : ℂ)⟩
      rw [Set.disjoint_iff_inter_eq_empty.mp hUA] at hmem
      exact hmem
    · rw [Set.piecewise_eq_of_notMem _ _ _ h]
      intro hcon
      simp only [id_eq] at hcon
      exact h (by rw [hcon]; exact hoU)
  · intro z hz
    have hzU : (z : ℂ) ∉ U := fun hcon => by
      have h1 : dist (z : ℂ) o < R := by
        have := hUball hcon; rwa [Metric.mem_ball] at this
      have h2 : dist (z : ℂ) o = R := by
        have := hz; rwa [Metric.mem_sphere] at this
      linarith
    apply Subtype.ext
    rw [hQ z, Set.piecewise_eq_of_notMem _ _ _ hzU]
    rfl

/-- **Unbounded case.**  Let `A` be the range of a retraction `r` of the plane, `U` an open set
with `frontier U ⊆ A` and `U ∩ A = ∅`, and suppose that the disc `D` of centre `o` and radius `R`
contains `A`, that `o ∉ U`, `o ∉ A` and that the sphere `∂D` is contained in `U`.  Then the map
which equals the identity on `U` and `r` outside `U` is a continuous self-map of `D` missing `o`
and fixing `∂D`, contradicting Brouwer. -/
theorem false_of_retraction_unbounded {A : Set ℂ} {r : C(ℂ, ℂ)}
    (hr1 : ∀ a ∈ A, r a = a) (hr2 : ∀ z, r z ∈ A)
    {U : Set ℂ} (hfr : frontier U ⊆ A) (_hUA : Disjoint U A)
    {o : ℂ} {R : ℝ} (hR : 0 < R) (hoU : o ∉ U) (hoA : o ∉ A)
    (hAD : A ⊆ Metric.closedBall o R) (hsphere : Metric.sphere o R ⊆ U) : False := by
  classical
  have hcont : Continuous (U.piecewise id (fun z => r z)) := by
    refine continuous_piecewise (f := id) (g := fun z => r z) (s := U) ?_ ?_ ?_
    · intro a ha; exact (hr1 a (hfr ha)).symm
    · exact continuousOn_id
    · exact r.continuous.continuousOn
  have hmap : ∀ z : Metric.closedBall o R,
      U.piecewise id (fun z => r z) (z : ℂ) ∈ Metric.closedBall o R := by
    intro z
    by_cases h : (z : ℂ) ∈ U
    · rw [Set.piecewise_eq_of_mem _ _ _ h]; exact z.2
    · rw [Set.piecewise_eq_of_notMem _ _ _ h]; exact hAD (hr2 _)
  let Q : C(Metric.closedBall o R, Metric.closedBall o R) :=
    ⟨fun z => ⟨U.piecewise id (fun z => r z) (z : ℂ), hmap z⟩,
      (hcont.comp continuous_subtype_val).subtype_mk hmap⟩
  have hQ : ∀ z : Metric.closedBall o R,
      (Q z : ℂ) = U.piecewise id (fun z => r z) (z : ℂ) := fun z => rfl
  refine false_of_misses_center_fixes_sphere o hR Q ?_ ?_
  · intro z
    rw [hQ z]
    by_cases h : (z : ℂ) ∈ U
    · rw [Set.piecewise_eq_of_mem _ _ _ h]
      exact fun hcon => hoU (by rw [← hcon]; exact h)
    · rw [Set.piecewise_eq_of_notMem _ _ _ h]
      exact fun hcon => hoA (by rw [← hcon]; exact hr2 (z : ℂ))
  · intro z hz
    have hzU : (z : ℂ) ∈ U := hsphere hz
    apply Subtype.ext
    rw [hQ z, Set.piecewise_eq_of_mem _ _ _ hzU]
    rfl

/-! ## Basic periodicity helpers -/

/-- A continuous `2π`-periodic map is injective on every interval of length `< 2π`. -/
theorem injOn_Icc_of_injOn_Ico {f : ℝ → ℂ} (hper : Function.Periodic f (2 * Real.pi))
    (hinj : Set.InjOn f (Set.Ico 0 (2 * Real.pi))) {a b : ℝ}
    (hab : b - a < 2 * Real.pi) : Set.InjOn f (Set.Icc a b) := by
  intro u hu v hv huv
  obtain ⟨k, hk⟩ :=
    Work.Smooth.SphereJordan.exists_int_sub_eq_of_periodic_injOn hper hinj huv
  have h1 : |u - v| < 2 * Real.pi := by
    rw [abs_lt]
    exact ⟨by linarith [hu.1, hv.2], by linarith [hu.2, hv.1]⟩
  have h2 : (k : ℝ) * (2 * Real.pi) = u - v := by linarith [hk]
  have hk0 : k = 0 := by
    by_contra hkne
    have h3 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hkne
    have h4 : 2 * Real.pi ≤ |u - v| := by
      rw [← h2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [h3, Real.pi_pos]
    linarith
  rw [hk0] at h2
  simp only [Int.cast_zero, zero_mul] at h2
  linarith [h2]

/-- Any real number has an integer translate in `[s, s + T)`. -/
theorem exists_int_mul_add_mem_Ico {T : ℝ} (hT : 0 < T) (s t : ℝ) :
    ∃ m : ℤ, t + (m : ℝ) * T ∈ Set.Ico s (s + T) := by
  refine ⟨⌈(s - t) / T⌉, ?_, ?_⟩
  · have h1 : (s - t) / T ≤ (((⌈(s - t) / T⌉ : ℤ) : ℝ)) := Int.le_ceil _
    have h2 : ((s - t) / T) * T ≤ ((((⌈(s - t) / T⌉ : ℤ) : ℝ))) * T :=
      mul_le_mul_of_nonneg_right h1 hT.le
    rw [div_mul_cancel₀ _ (ne_of_gt hT)] at h2
    linarith
  · have h1 : ((((⌈(s - t) / T⌉ : ℤ) : ℝ))) < (s - t) / T + 1 := Int.ceil_lt_add_one _
    have h2 : ((((⌈(s - t) / T⌉ : ℤ) : ℝ))) * T < ((s - t) / T + 1) * T :=
      mul_lt_mul_of_pos_right h1 hT
    have h3 : ((s - t) / T + 1) * T = (s - t) + T := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hT)]
    rw [h3] at h2
    linarith

/-- The trace of a `2π`-periodic curve is the image of one period `[0, 2π]`. -/
theorem range_eq_image_Icc {f : ℝ → ℂ} (hper : Function.Periodic f (2 * Real.pi)) :
    Set.range f = f '' Set.Icc 0 (2 * Real.pi) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨m, hm⟩ := exists_int_mul_add_mem_Ico hπ 0 t
    refine ⟨t + (m : ℝ) * (2 * Real.pi), ⟨hm.1, by linarith [hm.2]⟩, ?_⟩
    exact (hper.int_mul m) t
  · rintro ⟨t, -, rfl⟩
    exact ⟨t, rfl⟩

/-- The trace of a `2π`-periodic continuous curve is compact. -/
theorem isCompact_range_of_periodic {f : ℝ → ℂ} (hf : Continuous f)
    (hper : Function.Periodic f (2 * Real.pi)) : IsCompact (Set.range f) := by
  rw [range_eq_image_Icc hper]
  exact isCompact_Icc.image hf

/-! ## Retraction of the plane onto a compact arc -/

/-- A compact arc in the plane is a retract of the plane: the inverse parametrisation extends by
Tietze's theorem and is composed back with the parametrisation. -/
theorem exists_retraction_range {φ : C(Set.Icc (0 : ℝ) 1, ℂ)} (hφ : Function.Injective φ) :
    ∃ r : C(ℂ, ℂ), (∀ t : Set.Icc (0 : ℝ) 1, r (φ t) = φ t) ∧ ∀ z : ℂ, r z ∈ Set.range φ := by
  classical
  haveI : CompactSpace (Set.Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  set A : Set ℂ := Set.range φ with hA
  have hAcl : IsClosed A := (isCompact_range φ.continuous).isClosed
  have hbij : Function.Bijective fun t : Set.Icc (0 : ℝ) 1 => (⟨φ t, t, rfl⟩ : A) :=
    ⟨fun t u h => hφ (Subtype.ext_iff.mp h), fun a => by
      obtain ⟨t, ht⟩ := Set.mem_range.mp a.2
      exact ⟨t, Subtype.ext ht⟩⟩
  have h1 : Continuous fun t : Set.Icc (0 : ℝ) 1 => φ t := by fun_prop
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) 1 => (⟨φ t, t, rfl⟩ : A) :=
    h1.subtype_mk _
  let h : Set.Icc (0 : ℝ) 1 ≃ₜ A :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hbij) hcont
  have hcoe : ∀ t : Set.Icc (0 : ℝ) 1, (h t : A) = ⟨φ t, t, rfl⟩ := fun t => rfl
  let f : C(A, ℝ) := ⟨fun a => ((h.symm a : Set.Icc (0 : ℝ) 1) : ℝ),
    h.symm.continuous.subtype_val⟩
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hAcl f
  have hG' : ∀ a : A, max 0 (min 1 (G a)) = ((h.symm a : Set.Icc (0 : ℝ) 1) : ℝ) := by
    intro a
    have h1 : G a = ((h.symm a : Set.Icc (0 : ℝ) 1) : ℝ) := by
      have := congrArg (fun F : C(A, ℝ) => F a) hG
      simpa [f] using this
    rw [h1, min_eq_right (h.symm a).2.2, max_eq_right (h.symm a).2.1]
  have hclamp : ∀ z : ℂ, max 0 (min 1 (G z)) ∈ Set.Icc (0 : ℝ) 1 := fun z =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  refine ⟨⟨fun z => φ ⟨max 0 (min 1 (G z)), hclamp z⟩, ?_⟩, ?_, ?_⟩
  · exact φ.continuous.comp (Continuous.subtype_mk
      (continuous_const.max (continuous_const.min G.continuous)) hclamp)
  · intro t
    have hh : h.symm (⟨φ t, t, rfl⟩ : A) = t := by
      rw [← hcoe t]
      exact h.symm_apply_apply t
    have h2 : (⟨max 0 (min 1 (G (φ t))), hclamp (φ t)⟩ : Set.Icc (0 : ℝ) 1) = t := by
      apply Subtype.ext
      show max 0 (min 1 (G (φ t))) = (t : ℝ)
      rw [hG' ⟨φ t, t, rfl⟩, hh]
    show φ ⟨max 0 (min 1 (G (φ t))), hclamp (φ t)⟩ = φ t
    rw [h2]
  · intro z
    rw [hA]
    exact ⟨_, rfl⟩

/-! ## Extraction of a covering arc -/

/-- Given a point `x` of the trace of `γ` and a compact `K ⊆ trace` with `x ∉ K`, there is a
compact sub-arc of the trace (the image of an injective continuous map of `[0,1]`) containing
`K`. -/
theorem exists_arc_covering {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {x : ℂ} (hx : x ∈ Set.range γ) {K : Set ℂ} (hKc : IsCompact K) (hKJ : K ⊆ Set.range γ)
    (hxK : x ∉ K) :
    ∃ φ : C(Set.Icc (0 : ℝ) 1, ℂ), Function.Injective φ ∧ K ⊆ Set.range φ ∧
      Set.range φ ⊆ Set.range γ := by
  classical
  obtain ⟨s, hs⟩ := hx
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · refine ⟨⟨fun τ => γ (s + (τ : ℝ) * Real.pi),
        hcont.comp (by fun_prop)⟩, ?_, by simp, ?_⟩
    · intro τ τ' h
      apply Subtype.ext
      have hsub : Set.InjOn γ (Set.Icc s (s + Real.pi)) :=
        injOn_Icc_of_injOn_Ico hper hinj (by linarith [Real.pi_pos])
      have hτ : s + (τ : ℝ) * Real.pi ∈ Set.Icc s (s + Real.pi) :=
        ⟨by nlinarith [τ.2.1, Real.pi_pos], by nlinarith [τ.2.2, Real.pi_pos]⟩
      have hτ' : s + (τ' : ℝ) * Real.pi ∈ Set.Icc s (s + Real.pi) :=
        ⟨by nlinarith [τ'.2.1, Real.pi_pos], by nlinarith [τ'.2.2, Real.pi_pos]⟩
      have hthis := hsub hτ hτ' h
      exact mul_right_cancel₀ (ne_of_gt Real.pi_pos) (by linarith [hthis])
    · rintro y ⟨τ, rfl⟩
      exact ⟨_, rfl⟩
  · -- main case
    set T : Set ℝ := {t | t ∈ Set.Icc s (s + 2 * Real.pi) ∧ γ t ∈ K} with hTdef
    have hTsub : T ⊆ Set.Icc s (s + 2 * Real.pi) := fun t ht => ht.1
    have hTclosed : IsClosed T := by
      refine (isClosed_Icc.inter ?_)
      exact (hKc.isClosed.preimage hcont)
    have hTcompact : IsCompact T := isCompact_Icc.of_isClosed_subset hTclosed hTsub
    have hTne : T.Nonempty := by
      obtain ⟨k, hkK⟩ := hKne
      obtain ⟨t, ht⟩ := hKJ hkK
      obtain ⟨m, hm⟩ := exists_int_mul_add_mem_Ico hπ s t
      refine ⟨t + (m : ℝ) * (2 * Real.pi), ⟨hm.1, by linarith [hm.2]⟩, ?_⟩
      show γ (t + (m : ℝ) * (2 * Real.pi)) ∈ K
      have hstep : γ (t + (m : ℝ) * (2 * Real.pi)) = γ t := (hper.int_mul m) t
      rw [hstep, ht]
      exact hkK
    obtain ⟨tmin, htmin_mem, htmin⟩ := hTcompact.exists_isMinOn hTne
      (continuous_id.continuousOn : ContinuousOn (fun t : ℝ => t) T)
    obtain ⟨tmax, htmax_mem, htmax⟩ := hTcompact.exists_isMaxOn hTne
      (continuous_id.continuousOn : ContinuousOn (fun t : ℝ => t) T)
    have htminI := hTsub htmin_mem
    have htmaxI := hTsub htmax_mem
    -- `s < tmin` and `tmax < s + 2π`
    have hstmin : s < tmin := by
      rcases lt_or_eq_of_le htminI.1 with h | h
      · exact h
      · exfalso
        have hthis : γ tmin ∈ K := htmin_mem.2
        rw [← h] at hthis
        rw [hs] at hthis
        exact hxK hthis
    have htmaxs : tmax < s + 2 * Real.pi := by
      rcases lt_or_eq_of_le htmaxI.2 with h | h
      · exact h
      · exfalso
        have hKmem : γ tmax ∈ K := htmax_mem.2
        have heq : γ tmax = x := by rw [h]; exact (hper s).trans hs
        rw [heq] at hKmem
        exact hxK hKmem
    set a : ℝ := (s + tmin) / 2 with hadef
    set b : ℝ := (tmax + (s + 2 * Real.pi)) / 2 with hbdef
    have hatmin : a < tmin := by rw [hadef]; linarith
    have htminb : tmin ≤ tmax := htmin htmax_mem
    have htmaxb : tmax < b := by rw [hbdef]; linarith
    have hab : b - a < 2 * Real.pi := by
      rw [hadef, hbdef]
      have : tmax - tmin < 2 * Real.pi := by linarith [htminI.1, htmaxI.2]
      linarith
    have has : s < a := by rw [hadef]; linarith
    have hKsub : K ⊆ γ '' Set.Icc a b := by
      intro k hkK
      obtain ⟨t, ht⟩ := hKJ hkK
      obtain ⟨m, hm⟩ := exists_int_mul_add_mem_Ico hπ s t
      have hTmem : t + (m : ℝ) * (2 * Real.pi) ∈ T := by
        refine ⟨⟨hm.1, by linarith [hm.2]⟩, ?_⟩
        show γ (t + (m : ℝ) * (2 * Real.pi)) ∈ K
        have hstep : γ (t + (m : ℝ) * (2 * Real.pi)) = γ t := (hper.int_mul m) t
        rw [hstep, ht]
        exact hkK
      have h1 : tmin ≤ t + (m : ℝ) * (2 * Real.pi) := htmin hTmem
      have h2 : t + (m : ℝ) * (2 * Real.pi) ≤ tmax := htmax hTmem
      refine ⟨t + (m : ℝ) * (2 * Real.pi), ⟨by linarith, by linarith⟩, ?_⟩
      have hstep : γ (t + (m : ℝ) * (2 * Real.pi)) = γ t := (hper.int_mul m) t
      rw [hstep, ht]
    have hab_le : a ≤ b := by linarith [hatmin, htminb, htmaxb]
    have hbpos : (0 : ℝ) < b - a := by linarith
    have hrange1 : Set.range (fun τ : ↥(Set.Icc (0 : ℝ) 1) => a + (τ : ℝ) * (b - a))
        = Set.Icc a b := by
      ext y
      constructor
      · rintro ⟨τ, rfl⟩
        exact ⟨by nlinarith [τ.2.1, hbpos.le], by nlinarith [τ.2.2, hbpos.le]⟩
      · intro hy
        refine ⟨⟨(y - a) / (b - a), ⟨?_, ?_⟩⟩, ?_⟩
        · exact div_nonneg (by linarith [hy.1]) hbpos.le
        · rw [div_le_one hbpos]; linarith [hy.2]
        · field_simp
          ring
    have hrange : Set.range (fun τ : ↥(Set.Icc (0 : ℝ) 1) => γ (a + (τ : ℝ) * (b - a)))
        = γ '' Set.Icc a b := by
      show Set.range (γ ∘ fun τ : ↥(Set.Icc (0 : ℝ) 1) => a + (τ : ℝ) * (b - a)) = _
      rw [Set.range_comp, hrange1]
    let φ : C(Set.Icc (0 : ℝ) 1, ℂ) :=
      ⟨fun τ => γ (a + (τ : ℝ) * (b - a)), hcont.comp (by fun_prop)⟩
    have hrangeφ : Set.range φ = γ '' Set.Icc a b := hrange
    refine ⟨φ, ?_, ?_, ?_⟩
    · intro τ τ' h
      apply Subtype.ext
      have hsub : Set.InjOn γ (Set.Icc a b) := injOn_Icc_of_injOn_Ico hper hinj hab
      have hτ : a + (τ : ℝ) * (b - a) ∈ Set.Icc a b :=
        ⟨by nlinarith [τ.2.1, sub_nonneg.mpr hab_le], by nlinarith [τ.2.2, sub_nonneg.mpr hab_le]⟩
      have hτ' : a + (τ' : ℝ) * (b - a) ∈ Set.Icc a b :=
        ⟨by nlinarith [τ'.2.1, sub_nonneg.mpr hab_le], by nlinarith [τ'.2.2, sub_nonneg.mpr hab_le]⟩
      have hh : γ (a + (τ : ℝ) * (b - a)) = γ (a + (τ' : ℝ) * (b - a)) := h
      have hthis := hsub hτ hτ' hh
      exact mul_right_cancel₀ (ne_of_gt hbpos) (by linarith [hthis])
    · rw [hrangeφ]
      exact hKsub
    · rw [hrangeφ]
      rintro y ⟨t, -, rfl⟩
      exact ⟨t, rfl⟩


/-! ## Maehara's Lemma 1 -/

/-- **Maehara's Lemma 1.**  For a continuous `2π`-periodic curve injective on one period and whose
complement is not connected, the frontier of every connected component of the complement is the
whole trace of the curve. -/
theorem frontier_component_eq_range {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hdis : ¬ IsPreconnected (Set.range γ)ᶜ) (z : ℂ) (hz : z ∉ Set.range γ) :
    frontier (connectedComponentIn (Set.range γ)ᶜ z) = Set.range γ := by
  classical
  set U : Set ℂ := connectedComponentIn (Set.range γ)ᶜ z with hUdef
  have hJcompact : IsCompact (Set.range γ) := isCompact_range_of_periodic hcont hper
  have hJclosed : IsClosed (Set.range γ) := hJcompact.isClosed
  have hzU : z ∈ U := mem_connectedComponentIn hz
  have hUo : IsOpen U := IsOpen.connectedComponentIn hJclosed.isOpen_compl
  have hUsub : U ⊆ (Set.range γ)ᶜ := connectedComponentIn_subset _ _
  have hfrU : frontier U ⊆ Set.range γ :=
    Work.Smooth.JordanSeparation.frontier_connectedComponentIn_subset hJclosed z
  have hUeq : U ≠ (Set.range γ)ᶜ := by
    intro h
    exact hdis (h ▸ isPreconnected_connectedComponentIn)
  have hnotsub : ¬ ((Set.range γ)ᶜ ⊆ U) := fun h => hUeq (Subset.antisymm hUsub h)
  refine Subset.antisymm hfrU ?_
  rw [hUo.frontier_eq]
  intro p hp
  refine ⟨?_, ?_⟩
  · by_contra hpcl
    have hpfr : p ∉ frontier U := fun h => hpcl (frontier_subset_closure h)
    have hKcompact : IsCompact (frontier U) :=
      hJcompact.of_isClosed_subset isClosed_frontier hfrU
    obtain ⟨φ, hφinj, hKφ, hφJ⟩ :=
      exists_arc_covering hcont hper hinj hp hKcompact hfrU hpfr
    obtain ⟨r, hr1, hr2⟩ := exists_retraction_range hφinj
    have hr1' : ∀ a ∈ Set.range φ, r a = a := by
      rintro a ⟨t, rfl⟩
      exact hr1 t
    have hAcompact : IsCompact (Set.range φ) := isCompact_range φ.continuous
    have hUA : Disjoint U (Set.range φ) := by
      rw [Set.disjoint_left]
      intro a haU haA
      exact hUsub haU (hφJ haA)
    obtain ⟨w, hwJc, hwU⟩ := Set.not_subset.mp hnotsub
    by_cases hbdd : ∃ R : ℝ, U ⊆ Metric.ball z R
    · obtain ⟨R₁, hR₁⟩ := hbdd
      obtain ⟨Ma, hMa⟩ := hAcompact.isBounded.exists_norm_le
      have hUball : U ⊆ Metric.ball z (max R₁ (Ma + ‖z‖) + 1) :=
        hR₁.trans (Metric.ball_subset_ball
          (by have := le_max_left R₁ (Ma + ‖z‖); linarith))
      have hAD : Set.range φ ⊆ Metric.closedBall z (max R₁ (Ma + ‖z‖) + 1) := by
        intro a ha
        rw [Metric.mem_closedBall]
        have h1 : ‖a‖ ≤ Ma := hMa a ha
        have h2 : dist a z ≤ ‖a‖ + ‖z‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
        have h3 : (Ma + ‖z‖) < max R₁ (Ma + ‖z‖) + 1 := by
          have := le_max_right R₁ (Ma + ‖z‖); linarith
        linarith
      have hR : 0 < max R₁ (Ma + ‖z‖) + 1 := by
        have := hUball hzU
        rw [Metric.mem_ball] at this
        simpa using this
      exact false_of_retraction_bounded hr1' hr2 hKφ hUA hR hzU hUball hAD
    · obtain ⟨Ma, hMa⟩ := hJcompact.isBounded.exists_norm_le
      set M : ℝ := max Ma 0 with hMdef
      have hM0 : 0 ≤ M := le_max_right _ _
      have hu : ∃ u ∈ U, M < ‖u‖ := by
        by_contra h
        push_neg at h
        refine hbdd ⟨M + ‖z‖ + 1, fun u huU => ?_⟩
        rw [Metric.mem_ball]
        have h1 : ‖u‖ ≤ M := h u huU
        have h2 : dist u z ≤ ‖u‖ + ‖z‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
        linarith
      obtain ⟨u, huU, huM⟩ := hu
      have hSJ : {y : ℂ | M < ‖y‖} ⊆ (Set.range γ)ᶜ := by
        intro y hy hyJ
        obtain ⟨t, ht⟩ := hyJ
        have hy' : M < ‖y‖ := hy
        have h1 : ‖y‖ ≤ Ma := by
          have := hMa (γ t) ⟨t, rfl⟩
          rwa [ht] at this
        have h2 : Ma ≤ M := le_max_left _ _
        linarith
      have hSU : {y : ℂ | M < ‖y‖} ⊆ U := by
        have hpre := Work.Smooth.JordanSeparation.isPreconnected_lt_norm_compl M hM0
        have hsub := hpre.subset_connectedComponentIn (F := (Set.range γ)ᶜ) (x := u)
          (by simpa using huM) hSJ
        rwa [← connectedComponentIn_eq huU, ← hUdef] at hsub
      have hhoA : w ∉ Set.range φ := fun h => hwJc (hφJ h)
      have hAD : Set.range φ ⊆ Metric.closedBall w (M + ‖w‖ + 1) := by
        intro a ha
        rw [Metric.mem_closedBall]
        have h1 : ‖a‖ ≤ Ma := hMa a (hφJ ha)
        have h2 : Ma ≤ M := le_max_left _ _
        have h3 : dist a w ≤ ‖a‖ + ‖w‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
        linarith
      have hsphere : Metric.sphere w (M + ‖w‖ + 1) ⊆ U := by
        intro y hy
        apply hSU
        simp only [Set.mem_ofPred_eq]
        have h1 : ‖y - w‖ = M + ‖w‖ + 1 := by
          rw [Metric.mem_sphere, dist_eq_norm] at hy
          linarith [hy]
        have h2 : ‖y - w‖ ≤ ‖y‖ + ‖w‖ := norm_sub_le _ _
        linarith
      have hR : 0 < M + ‖w‖ + 1 := by linarith [hM0, norm_nonneg w]
      exact false_of_retraction_unbounded hr1' hr2 hKφ hUA hR hwU hhoA hAD hsphere
  · intro hpU
    exact hUsub hpU hp


end

end Work.Topology.PlaneCurve
