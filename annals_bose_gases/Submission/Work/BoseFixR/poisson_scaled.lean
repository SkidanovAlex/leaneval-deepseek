import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseFixR.PoissonScaleDefs
import Submission.Work.BoseFixR.Rb5Lin.ps3_summableWeight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

open MeasureTheory

noncomputable section

theorem periodZ3_continuous {g : (Fin 3 → ℝ) → ℂ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) : Continuous (periodZ3 g) := by
  obtain ⟨R₀, hR₀⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Fin 3 → ℝ)).mp hgs.isCompact.isBounded
  set R : ℝ := max R₀ 0 with hRdef
  have hsupp : Function.support g ⊆ Metric.closedBall 0 R := by
    intro y hy
    have h1 := Metric.mem_closedBall.mp (hR₀ (subset_closure hy))
    rw [dist_eq_norm] at h1
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [sub_zero] at h1 ⊢
    have hRge : R₀ ≤ R := by rw [hRdef]; exact le_max_left _ _
    linarith
  rw [continuous_iff_continuousAt]
  intro x₀
  set S : Finset (Fin 3 → ℤ) :=
    (Rb5Lin.ps3_latticeBall_finite (R + ‖x₀‖ + 1)).toFinset with hSdef
  have hfin : Continuous (fun x : Fin 3 → ℝ => ∑ d ∈ S, g (x + Rb5Lin.latPoint d)) :=
    continuous_finsetSum S (fun d _ => hgc.comp (continuous_id.add continuous_const))
  refine hfin.continuousAt.congr ?_
  filter_upwards [Metric.closedBall_mem_nhds x₀ (by norm_num : (0:ℝ) < 1)] with x hx
  have hxn : ‖x‖ ≤ ‖x₀‖ + 1 := by
    have h1 : ‖x - x₀‖ ≤ 1 := by
      have := Metric.mem_closedBall.mp hx
      rwa [dist_eq_norm] at this
    have h2 : ‖x‖ - ‖x₀‖ ≤ ‖x - x₀‖ := (le_abs_self _).trans (abs_norm_sub_norm_le x x₀)
    linarith
  have hzero : ∀ d : Fin 3 → ℤ, d ∉ S → g (x + Rb5Lin.latPoint d) = 0 := by
    intro d hd
    have hbig : R + ‖x₀‖ + 1 < ‖Rb5Lin.latPoint d‖ := by
      refine not_le.mp fun hle => hd ?_
      rw [hSdef, Set.Finite.mem_toFinset]
      exact hle
    have hgt : R < ‖x + Rb5Lin.latPoint d‖ := by
      have h3 : ‖Rb5Lin.latPoint d‖ ≤ ‖x‖ + ‖x + Rb5Lin.latPoint d‖ := by
        have h4 := norm_sub_le (x + Rb5Lin.latPoint d) x
        have h5 : (x + Rb5Lin.latPoint d) - x = Rb5Lin.latPoint d := by abel
        rw [h5] at h4
        linarith
      linarith
    by_contra hne
    have hmem : x + Rb5Lin.latPoint d ∈ Metric.closedBall 0 R :=
      hsupp (Function.mem_support.mpr hne)
    have h6 := Metric.mem_closedBall.mp hmem
    rw [dist_eq_norm] at h6
    simp only [sub_zero] at h6
    linarith
  rw [periodZ3]
  exact (tsum_eq_sum hzero).symm

theorem integral_periodZ3_mul_box3 {g : (Fin 3 → ℝ) → ℂ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) {φ : (Fin 3 → ℝ) → ℂ} (hφc : Continuous φ)
    (hφper : ∀ (x : Fin 3 → ℝ) (m : Fin 3 → ℤ), φ (x + Rb5Lin.latPoint m) = φ x) :
    (∫ x in Rb5Lin.box3, φ x * periodZ3 g x)
      = ∑' d : Fin 3 → ℤ, ∫ x in Rb5Lin.box3, φ x * g (x + Rb5Lin.latPoint d) := by
  -- a radius containing the support of `g`
  obtain ⟨R₀, hR₀⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Fin 3 → ℝ)).mp hgs.isCompact.isBounded
  set R : ℝ := max R₀ 0 with hRdef
  have hsupp : Function.support g ⊆ Metric.closedBall 0 R := by
    intro y hy
    have h1 := Metric.mem_closedBall.mp (hR₀ (subset_closure hy))
    rw [dist_eq_norm] at h1
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [sub_zero] at h1 ⊢
    have hRge : R₀ ≤ R := by rw [hRdef]; exact le_max_left _ _
    linarith
  set S : Finset (Fin 3 → ℤ) := (Rb5Lin.ps3_latticeBall_finite (R + 1)).toFinset with hSdef
  have hxbox : ∀ x ∈ Rb5Lin.box3, ‖x‖ ≤ 1 := by
    intro x hx
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    rw [Real.norm_eq_abs]
    have h := Rb5Lin.mem_box3.mp hx i
    exact abs_le.mpr ⟨by linarith [h.1], by simpa using h.2⟩
  have hsub : Rb5Lin.box3 ⊆ Metric.closedBall (0 : Fin 3 → ℝ) 1 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using hxbox x hx
  -- vanishing of every lattice translate outside `S`, on `box3`
  have hvan : ∀ d : Fin 3 → ℤ, d ∉ S → ∀ x ∈ Rb5Lin.box3, g (x + Rb5Lin.latPoint d) = 0 := by
    intro d hd x hx
    have hbig : R + 1 < ‖Rb5Lin.latPoint d‖ := by
      refine not_le.mp fun hle => hd ?_
      rw [hSdef, Set.Finite.mem_toFinset]
      exact hle
    have hgt : R < ‖x + Rb5Lin.latPoint d‖ := by
      have h3 : ‖Rb5Lin.latPoint d‖ ≤ ‖x‖ + ‖x + Rb5Lin.latPoint d‖ := by
        have h4 := norm_sub_le (x + Rb5Lin.latPoint d) x
        have h5 : (x + Rb5Lin.latPoint d) - x = Rb5Lin.latPoint d := by abel
        rw [h5] at h4
        linarith
      linarith [hxbox x hx]
    by_contra hne
    have hmem : x + Rb5Lin.latPoint d ∈ Metric.closedBall 0 R :=
      hsupp (Function.mem_support.mpr hne)
    have h6 := Metric.mem_closedBall.mp hmem
    rw [dist_eq_norm] at h6
    simp only [sub_zero] at h6
    linarith
  have hsum_box : ∀ x ∈ Rb5Lin.box3,
      periodZ3 g x = ∑ d ∈ S, g (x + Rb5Lin.latPoint d) := by
    intro x hx
    rw [periodZ3]
    exact tsum_eq_sum (fun d hd => hvan d hd x hx)
  -- a global bound for `g` and a bound for `φ` on the box
  have hboxfin : (volume : Measure (Fin 3 → ℝ)) Rb5Lin.box3 < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) (isCompact_closedBall (0 : Fin 3 → ℝ) 1).measure_lt_top
  obtain ⟨Cφ, hCφ⟩ :=
    (isCompact_closedBall (0 : Fin 3 → ℝ) 1).exists_bound_of_continuousOn hφc.continuousOn
  have hCφnn : 0 ≤ Cφ :=
    le_trans (norm_nonneg _) (hCφ 0 (by rw [Metric.mem_closedBall, dist_eq_norm]; simp))
  obtain ⟨Cg, hCg⟩ := hgs.isCompact.exists_bound_of_continuousOn hgc.continuousOn
  have hCg' : ∀ y : Fin 3 → ℝ, ‖g y‖ ≤ max Cg 0 := by
    intro y
    by_cases hy : y ∈ tsupport g
    · exact (hCg y hy).trans (le_max_left _ _)
    · have : g y = 0 := by
        by_contra hne
        exact hy (subset_closure (Function.mem_support.mpr hne))
      simp [this]
  have hInt : ∀ d : Fin 3 → ℤ,
      IntegrableOn (fun x : Fin 3 → ℝ => φ x * g (x + Rb5Lin.latPoint d)) Rb5Lin.box3 := by
    intro d
    refine IntegrableOn.of_bound hboxfin ?_ (Cφ * max Cg 0) ?_
    · exact (hφc.mul (hgc.comp (continuous_id.add continuous_const))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem Rb5Lin.measurableSet_box3] with x hx
      rw [norm_mul]
      exact mul_le_mul (hCφ x (hsub hx)) (hCg' _) (norm_nonneg _) hCφnn
  have hL : (∫ x in Rb5Lin.box3, φ x * periodZ3 g x)
      = ∫ x in Rb5Lin.box3, ∑ d ∈ S, φ x * g (x + Rb5Lin.latPoint d) := by
    refine setIntegral_congr_fun Rb5Lin.measurableSet_box3 (fun x hx => ?_)
    rw [hsum_box x hx, Finset.mul_sum]
  have hS2 : (∫ x in Rb5Lin.box3, ∑ d ∈ S, φ x * g (x + Rb5Lin.latPoint d))
      = ∑ d ∈ S, ∫ x in Rb5Lin.box3, φ x * g (x + Rb5Lin.latPoint d) :=
    integral_finsetSum S (fun d _ => hInt d)
  have hR3 : (∑' d : Fin 3 → ℤ, ∫ x in Rb5Lin.box3, φ x * g (x + Rb5Lin.latPoint d))
      = ∑ d ∈ S, ∫ x in Rb5Lin.box3, φ x * g (x + Rb5Lin.latPoint d) := by
    refine tsum_eq_sum (fun d hd => ?_)
    have h0 : Set.EqOn (fun x : Fin 3 → ℝ => φ x * g (x + Rb5Lin.latPoint d))
        (fun _ => (0 : ℂ)) Rb5Lin.box3 := fun x hx => by
          show φ x * g (x + Rb5Lin.latPoint d) = 0
          rw [hvan d hd x hx, mul_zero]
    rw [setIntegral_congr_fun Rb5Lin.measurableSet_box3 h0]
    simp
  rw [hL, hS2, hR3]

theorem mFourierCoeff_periodZ3 {g : (Fin 3 → ℝ) → ℂ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) (G : C(UnitAddTorus (Fin 3), ℂ))
    (hG : ∀ x : Fin 3 → ℝ, G (fun i => (x i : UnitAddCircle)) = periodZ3 g x)
    (n : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff (⇑G) n
      = ∫ x : Fin 3 → ℝ, g x * Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((x i : ℂ) * (n i : ℂ))))) := by
  set φ : (Fin 3 → ℝ) → ℂ :=
    fun y => UnitAddTorus.mFourier (-n) (fun i => (y i : UnitAddCircle)) with hφdef
  have hzero_int : ∀ k : ℤ, (((k : ℝ)) : UnitAddCircle) = 0 := by
    intro k
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by simp⟩
  have hφc : Continuous φ := by
    rw [hφdef]
    fun_prop
  have hφper : ∀ (x : Fin 3 → ℝ) (m : Fin 3 → ℤ), φ (x + Rb5Lin.latPoint m) = φ x := by
    intro x m
    show (UnitAddTorus.mFourier (-n) fun i => ((x + Rb5Lin.latPoint m) i : UnitAddCircle))
        = (UnitAddTorus.mFourier (-n) fun i => (x i : UnitAddCircle))
    congr 1
    funext i
    simp only [Pi.add_apply, Rb5Lin.latPoint_apply]
    rw [AddCircle.coe_add,
      show (((m i : ℝ)) : UnitAddCircle) = 0 from by
        rw [AddCircle.coe_eq_zero_iff]
        exact ⟨m i, by simp⟩, add_zero]
  have hφbdd : ∀ y : Fin 3 → ℝ, ‖φ y‖ ≤ 1 := by
    intro y
    rw [hφdef]
    have h := ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n))
      (fun i => (y i : UnitAddCircle))
    rw [UnitAddTorus.mFourier_norm] at h
    simpa using h
  have hΨint : Integrable (fun y : Fin 3 → ℝ => φ y * g y) :=
    (hgc.integrable_of_hasCompactSupport hgs).bdd_mul hφc.aestronglyMeasurable
      (Filter.Eventually.of_forall hφbdd)
  have hphase : ∀ y : Fin 3 → ℝ, φ y
      = Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((y i : ℂ) * (n i : ℂ))))) := by
    intro y
    rw [hφdef]
    have h := Rb5Lin.ps3_mFourier_smul n y (1 : ℂ)
    simpa [smul_eq_mul] using h
  calc UnitAddTorus.mFourierCoeff (⇑G) n
      = ∫ x in Rb5Lin.box3, φ x * periodZ3 g x := by
        rw [UnitAddTorus.mFourierCoeff_eq_integral (⇑G) n (fun _ => (0 : ℝ))]
        refine setIntegral_congr_fun Rb5Lin.measurableSet_box3 (fun x hx => ?_)
        show (UnitAddTorus.mFourier (-n) (fun i => (x i : UnitAddCircle))) •
            G (fun i => (x i : UnitAddCircle)) = φ x * periodZ3 g x
        rw [hG x, smul_eq_mul]
    _ = ∑' d : Fin 3 → ℤ, ∫ x in Rb5Lin.box3, φ x * g (x + Rb5Lin.latPoint d) :=
        integral_periodZ3_mul_box3 hgc hgs hφc hφper
    _ = ∑' d : Fin 3 → ℤ, ∫ x in Rb5Lin.box3,
          φ (d +ᵥ x) * g (d +ᵥ x) := by
        refine tsum_congr (fun d => ?_)
        refine setIntegral_congr_fun Rb5Lin.measurableSet_box3 (fun x hx => ?_)
        show φ x * g (x + Rb5Lin.latPoint d) = φ (d +ᵥ x) * g (d +ᵥ x)
        rw [Rb5Lin.vadd_eq_add_latPoint, hφper x d]
    _ = ∫ y, φ y * g y :=
        (MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum''
          Rb5Lin.ps3_fundamentalDomain (fun y : Fin 3 → ℝ => φ y * g y) hΨint).symm
    _ = ∫ x : Fin 3 → ℝ, g x *
          Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((x i : ℂ) * (n i : ℂ))))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        show φ y * g y = g y * Complex.exp (-(2 * Real.pi * Complex.I *
          (∑ i, ((y i : ℂ) * (n i : ℂ)))))
        rw [hphase y]
        ring

theorem periodZ3_periodic (g : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) (m : Fin 3 → ℤ) :
    periodZ3 g (x + Rb5Lin.latPoint m) = periodZ3 g x := by
  have h1 : ∀ d : Fin 3 → ℤ, g ((x + Rb5Lin.latPoint m) + Rb5Lin.latPoint d)
      = g (x + Rb5Lin.latPoint (d + m)) := by
    intro d
    congr 1
    ext i
    simp only [Pi.add_apply, Rb5Lin.latPoint_apply, Int.cast_add]
    ring
  simp only [periodZ3, h1]
  exact (Equiv.addRight m).tsum_eq (fun d : Fin 3 → ℤ => g (x + Rb5Lin.latPoint d))

theorem poissonZ3 {g : (Fin 3 → ℝ) → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hsum : Summable (fun m : Fin 3 → ℤ => ∫ x : Fin 3 → ℝ, g x *
      Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((x i : ℂ) * (m i : ℂ))))))) :
    (∑' m : Fin 3 → ℤ, ∫ x : Fin 3 → ℝ, g x *
      Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((x i : ℂ) * (m i : ℂ))))))
      = ∑' d : Fin 3 → ℤ, g (Rb5Lin.latPoint d) := by
  have hPc : Continuous (periodZ3 g) := periodZ3_continuous hgc hgs
  have hPper : ∀ (x : Fin 3 → ℝ) (m : Fin 3 → ℤ), periodZ3 g (x + Rb5Lin.latPoint m)
      = periodZ3 g x := fun x m => periodZ3_periodic g x m
  obtain ⟨G, hG⟩ := Rb5Lin.ps3_torus_lift ⟨periodZ3 g, hPc⟩ hPper
  have hcoeff : ∀ n : Fin 3 → ℤ, UnitAddTorus.mFourierCoeff (⇑G) n
      = ∫ x : Fin 3 → ℝ, g x *
          Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((x i : ℂ) * (n i : ℂ))))) :=
    fun n => mFourierCoeff_periodZ3 hgc hgs G hG n
  have hsum' : Summable (fun n : Fin 3 → ℤ => UnitAddTorus.mFourierCoeff (⇑G) n) :=
    hsum.congr (fun n => (hcoeff n).symm)
  have hseries := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := G) hsum'
    (0 : UnitAddTorus (Fin 3))
  have hone : ∀ n : Fin 3 → ℤ, (UnitAddTorus.mFourier n) (0 : UnitAddTorus (Fin 3)) = 1 := by
    intro n
    rw [UnitAddTorus.mFourier]
    simp
  have hsum_eq : (∑' n : Fin 3 → ℤ, UnitAddTorus.mFourierCoeff (⇑G) n) = G 0 := by
    have h' : HasSum (fun n : Fin 3 → ℤ => UnitAddTorus.mFourierCoeff (⇑G) n) (G 0) := by
      simpa only [hone, smul_eq_mul, mul_one] using hseries
    exact h'.tsum_eq
  have hG0 : G 0 = periodZ3 g 0 := by
    have h := hG (0 : Fin 3 → ℝ)
    change G (fun i : Fin 3 => ((0 : Fin 3 → ℝ) i : UnitAddCircle)) = periodZ3 g 0
    exact h
  calc (∑' m : Fin 3 → ℤ, ∫ x : Fin 3 → ℝ, g x *
        Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((x i : ℂ) * (m i : ℂ))))))
      = ∑' m : Fin 3 → ℤ, UnitAddTorus.mFourierCoeff (⇑G) m :=
        tsum_congr (fun m => (hcoeff m).symm)
    _ = G 0 := hsum_eq
    _ = periodZ3 g 0 := hG0
    _ = ∑' d : Fin 3 → ℤ, g (Rb5Lin.latPoint d) := by
        rw [periodZ3]
        exact tsum_congr (fun d => by rw [zero_add])

theorem integral_scaled_fourier {ℓ : ℝ} (hℓ : 0 < ℓ) (F : EuclideanSpace ℝ (Fin 3) → ℂ) (m : Fin 3 → ℤ) :
    (∫ x : EuclideanSpace ℝ (Fin 3), F x * Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • BoseB4.vec m) x : ℂ))))
      = ℓ ^ 3 * ∫ t : Fin 3 → ℝ,
          F (WithLp.toLp 2 (fun i => ℓ * t i))
            * Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((t i : ℂ) * (m i : ℂ))))) := by
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  set w : Fin 3 → ℝ := fun i => ℓ⁻¹ * (2 * Real.pi * (m i : ℝ)) with hw
  -- the frequency pairing, in coordinates
  have hinner : ∀ y : Fin 3 → ℝ,
      (inner ℝ (ℓ⁻¹ • BoseB4.vec m) (WithLp.toLp 2 y) : ℂ)
        = ∑ i, ((y i : ℂ) * (w i : ℂ)) := by
    intro y
    have hinner0 : inner ℝ (BoseB4.vec m) (WithLp.toLp 2 y)
        = ∑ i, y i * (2 * Real.pi * (m i : ℝ)) := by
      rw [show BoseB4.vec m = WithLp.toLp 2 (fun i => 2 * Real.pi * (m i : ℝ)) from rfl,
        PiLp.inner_apply]
      exact Finset.sum_congr rfl (fun i _ => by rw [RCLike.inner_apply]; simp)
    rw [real_inner_smul_left, hinner0, hw, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hstep1 : (∫ x : EuclideanSpace ℝ (Fin 3),
        F x * Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • BoseB4.vec m) x : ℂ))))
      = ∫ y : Fin 3 → ℝ, F (WithLp.toLp 2 y) *
          Complex.exp (-(Complex.I * (∑ i, ((y i : ℂ) * (w i : ℂ))))) := by
    rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    show F (WithLp.toLp 2 y) * Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • BoseB4.vec m) (WithLp.toLp 2 y) : ℂ)))
        = F (WithLp.toLp 2 y) * Complex.exp (-(Complex.I * (∑ i, ((y i : ℂ) * (w i : ℂ)))))
    rw [hinner y]
  have hstep2 : (∫ y : Fin 3 → ℝ, F (WithLp.toLp 2 y) *
        Complex.exp (-(Complex.I * (∑ i, ((y i : ℂ) * (w i : ℂ))))))
      = ℓ ^ 3 * ∫ t : Fin 3 → ℝ, F (WithLp.toLp 2 (fun i => ℓ * t i)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((t i : ℂ) * (m i : ℂ))))) := by
    set f : (Fin 3 → ℝ) → ℂ := fun y => F (WithLp.toLp 2 y) *
      Complex.exp (-(Complex.I * (∑ i, ((y i : ℂ) * (w i : ℂ))))) with hf
    have hcomp := MeasureTheory.Measure.integral_comp_smul (volume : Measure (Fin 3 → ℝ)) f ℓ
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hcomp
    have hmul : ℓ ^ 3 • (∫ y, f (ℓ • y)) = ∫ y, f y := by
      rw [hcomp, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hℓ.le 3)), smul_smul,
        mul_inv_cancel₀ (pow_ne_zero 3 hℓ0), one_smul]
    have hwR : ∀ i : Fin 3, ℓ * w i = 2 * Real.pi * (m i : ℝ) := by
      intro i
      rw [hw]
      field_simp
    have hwc : ∀ i : Fin 3, (ℓ : ℂ) * (w i : ℂ) = 2 * Real.pi * (m i : ℂ) := by
      intro i
      exact_mod_cast hwR i
    have hexp : ∀ y : Fin 3 → ℝ,
        ∑ i, (((ℓ • y) i : ℝ) : ℂ) * (w i : ℂ)
          = 2 * Real.pi * (∑ i, ((y i : ℂ) * (m i : ℂ))) := by
      intro y
      calc ∑ i, (((ℓ • y) i : ℝ) : ℂ) * (w i : ℂ)
          = ∑ i, ((ℓ : ℂ) * (y i : ℂ)) * (w i : ℂ) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              simp only [Pi.smul_apply, smul_eq_mul]
              push_cast
              ring
        _ = ∑ i, (y i : ℂ) * ((ℓ : ℂ) * (w i : ℂ)) := by
              refine Finset.sum_congr rfl (fun i _ => by ring)
        _ = ∑ i, (y i : ℂ) * (2 * Real.pi * (m i : ℂ)) := by
              refine Finset.sum_congr rfl (fun i _ => by rw [hwc i])
        _ = 2 * Real.pi * (∑ i, (y i : ℂ) * (m i : ℂ)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun i _ => by ring)
    have hInt : (∫ y : Fin 3 → ℝ, f (ℓ • y)) = ∫ t : Fin 3 → ℝ,
        F (WithLp.toLp 2 (fun i => ℓ * t i)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((t i : ℂ) * (m i : ℂ))))) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      show f (ℓ • y) = F (WithLp.toLp 2 (fun i => ℓ * y i)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((y i : ℂ) * (m i : ℂ)))))
      rw [hf]
      show F (WithLp.toLp 2 (ℓ • y)) *
          Complex.exp (-(Complex.I * (∑ i, (((ℓ • y) i : ℝ) : ℂ) * (w i : ℂ))))
        = F (WithLp.toLp 2 (fun i => ℓ * y i)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((y i : ℂ) * (m i : ℂ)))))
      have htoLp : WithLp.toLp 2 (ℓ • y) = WithLp.toLp 2 (fun i => ℓ * y i) := rfl
      rw [htoLp, hexp y]
      congr 1
      congr 1
      ring
    rw [← hmul, hInt, RCLike.real_smul_eq_coe_mul]
    push_cast
    rfl
  rw [hstep1, hstep2]

theorem poisson_scaled {ℓ : ℝ} (hℓ : 0 < ℓ) {F : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hFc : Continuous F) (hFs : HasCompactSupport F)
    (hsum : Summable (fun m : Fin 3 → ℤ => ∫ x : EuclideanSpace ℝ (Fin 3),
      F x * Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec m) x : ℂ))))) :
    (∑' m : Fin 3 → ℤ, ∫ x : EuclideanSpace ℝ (Fin 3),
      F x * Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • Work.BoseB4.vec m) x : ℂ))))
      = ℓ ^ 3 * ∑' d : Fin 3 → ℤ, F (Work.BoseFixR.lat ℓ d) := by
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  set g : (Fin 3 → ℝ) → ℂ := fun t => F (WithLp.toLp 2 (fun i => ℓ * t i)) with hg
  have hgc : Continuous g := by
    rw [hg]
    refine hFc.comp ?_
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
      (continuous_pi (fun i => continuous_const.mul (continuous_apply i)))
  have hgs : HasCompactSupport g := by
    rw [hg]
    have h1 : HasCompactSupport (fun t : Fin 3 → ℝ => F (WithLp.toLp 2 t)) :=
      hFs.comp_homeomorph (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm
    have h2 : HasCompactSupport (fun t : Fin 3 → ℝ =>
        F (WithLp.toLp 2 ((Units.mk0 ℓ hℓ0 : Units ℝ) • t))) :=
      h1.comp_homeomorph (Homeomorph.smul (Units.mk0 ℓ hℓ0))
    have hfun : (fun t : Fin 3 → ℝ => F (WithLp.toLp 2 (fun i => ℓ * t i)))
        = fun t : Fin 3 → ℝ => F (WithLp.toLp 2 ((Units.mk0 ℓ hℓ0 : Units ℝ) • t)) := by
      funext t
      congr 1
    rwa [hfun]
  have hterm : ∀ m : Fin 3 → ℤ, (∫ x : EuclideanSpace ℝ (Fin 3),
        F x * Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • BoseB4.vec m) x : ℂ))))
      = ℓ ^ 3 * ∫ t : Fin 3 → ℝ, g t *
          Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((t i : ℂ) * (m i : ℂ))))) := by
    intro m
    rw [integral_scaled_fourier hℓ F m, hg]
  have hsumG : Summable (fun m : Fin 3 → ℤ => ∫ t : Fin 3 → ℝ, g t *
      Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((t i : ℂ) * (m i : ℂ)))))) := by
    have h1 : Summable (fun m : Fin 3 → ℤ => ℓ ^ 3 * ∫ t : Fin 3 → ℝ, g t *
        Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((t i : ℂ) * (m i : ℂ)))))) :=
      hsum.congr (fun m => hterm m)
    have h2 : Summable (fun m : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * (ℓ ^ 3 * ∫ t : Fin 3 → ℝ, g t *
        Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((t i : ℂ) * (m i : ℂ))))))) :=
      h1.mul_left _
    refine h2.congr (fun m => ?_)
    have hc : ((ℓ : ℂ) ^ 3) ≠ 0 := pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr hℓ0)
    push_cast
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hcore := poissonZ3 hgc hgs hsumG
  calc (∑' m : Fin 3 → ℤ, ∫ x : EuclideanSpace ℝ (Fin 3),
          F x * Complex.exp (-(Complex.I * (inner ℝ (ℓ⁻¹ • BoseB4.vec m) x : ℂ))))
      = ∑' m : Fin 3 → ℤ, ℓ ^ 3 * ∫ t : Fin 3 → ℝ, g t *
          Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((t i : ℂ) * (m i : ℂ))))) :=
        tsum_congr hterm
    _ = ℓ ^ 3 * ∑' m : Fin 3 → ℤ, ∫ t : Fin 3 → ℝ, g t *
          Complex.exp (-(2 * Real.pi * Complex.I * (∑ i, ((t i : ℂ) * (m i : ℂ))))) :=
        tsum_mul_left
    _ = ℓ ^ 3 * ∑' d : Fin 3 → ℤ, g (Rb5Lin.latPoint d) := by rw [hcore]
    _ = ℓ ^ 3 * ∑' d : Fin 3 → ℤ, F (lat ℓ d) := by
        congr 1

end

end Work.BoseFixR
