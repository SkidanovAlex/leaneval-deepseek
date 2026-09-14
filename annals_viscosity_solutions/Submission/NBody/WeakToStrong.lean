import Submission.NBody.FirstVariation
import Submission.Commons.Analysis.Calculus.ae_eq_add_intervalIntegral_of_forall_weighted_inner_deriv_add_eq_zero
import Submission.Commons.Analysis.Calculus.hasDerivAt_of_ae_deriv_eq_continuousOn
import Mathlib

/-!
# Minimisers satisfy Newton's equations

Upgrading the weak Euler--Lagrange equation of `Submission.NBody.weak_first_variation_scalar` to the
strong form: an `h`-minimiser `γ` on `[a,b]` (collision free there, with finite action potential) is
differentiable off the collisions with `(deriv γ)' = ∇ₘU(γ)` — i.e. it is a genuine solution of
Newton's equations on `(a,b)`.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- A function vanishes off the topological support of its derivative. -/
lemma eq_zero_of_notMem_tsupport {f : ℝ → ℝ} {x : ℝ} (h : x ∉ tsupport f) : f x = 0 := by
  by_contra hc
  exact h (subset_closure (Function.mem_support.mpr hc))

/-- An integral over `ℝ` of a compactly supported function equals its integral over a larger
interval. -/
lemma integral_eq_intervalIntegral_of_tsupport_subset {φ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h : ∀ t, t ∉ Set.Ioo a b → φ t = 0) :
    MeasureTheory.integral MeasureTheory.volume φ = ∫ t in a..b, φ t := by
  rw [intervalIntegral.integral_of_le hab.le]
  refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Ioc a b) fun t ht => h t ?_).symm
  rintro ⟨h1, h2⟩
  exact ht ⟨h1, h2.le⟩

/-- **The velocity of an `h`-minimiser is the primitive of the force, almost everywhere.** -/
theorem minimizer_deriv_ae_eq_primitive {m : Fin N → ℝ} {h a b : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ a b)
    (hfin : actionPot m h (γ a) (γ b) < ⊤) :
    ∃ c : EN E N, deriv γ =ᵐ[MeasureTheory.volume.restrict (Set.Ioo a b)]
      (fun t => c + ∫ s in a..t, ∇_[m] (U m) (γ s)) := by
  classical
  have hh0 : 0 ≤ h := hh.le
  have hmnn : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hγcont : ContinuousOn γ (Set.Icc a b) := by
    have h := hac.continuousOn
    rwa [uIcc_of_le hab.le] at h
  have haction : actionOn m h γ a b < ⊤ := hmin ▸ hfin
  obtain ⟨c0, hc0, hmc0⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ m i := by
    by_cases hN : N = 0
    · subst hN
      exact ⟨1, one_pos, fun i => i.elim0⟩
    · haveI : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero hN⟩⟩
      set sf : Finset ℝ := Finset.univ.image m with hsf
      have hsfne : sf.Nonempty := hsf ▸ (Finset.univ_nonempty (α := Fin N)).image m
      refine ⟨sf.min' hsfne, ?_, ?_⟩
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem sf hsfne)
        rw [← hi]; exact hm i
      · intro i
        exact Finset.min'_le sf (m i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hderiv_norm_int : IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b :=
    intervalIntegrable_deriv_of_actionOn_lt_top hc0 hmc0 hh0 hab.le hac haction
  have hderiv_int : IntervalIntegrable (deriv γ) volume a b :=
    hderiv_norm_int.mono_fun'
      (by
        rw [uIoc_of_le hab.le]
        exact Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
          hac)
      (Filter.Eventually.of_forall fun t => le_rfl)
  have hfli : MeasureTheory.LocallyIntegrableOn (deriv γ) (Set.Ioo a b) MeasureTheory.volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hderiv_int).locallyIntegrableOn.mono_set
      Set.Ioo_subset_Ioc_self
  have hgrad_cont : ContinuousOn (fun t => ∇_[m] (U m) (γ t)) (Set.Icc a b) :=
    continuousOn_weightedGrad_comp (continuousOn_fderiv_U_comp (m := m) hγcont hnc)
  suffices hweak : ∀ (ψ : ℝ → ℝ) (w : EN E N),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Set.Ioo a b →
      MeasureTheory.integral MeasureTheory.volume
          (fun t => deriv ψ t * (Finset.sum Finset.univ fun i =>
            m i * inner ℝ ((deriv γ t) i) (w i)))
        + MeasureTheory.integral MeasureTheory.volume
          (fun t => ψ t * (Finset.sum Finset.univ fun i =>
            m i * inner ℝ ((∇_[m] (U m) (γ t)) i) (w i))) = 0 by
    exact Commons.Analysis.Calculus.ae_eq_add_intervalIntegral_of_forall_weighted_inner_deriv_add_eq_zero
      (f := deriv γ) (g := fun t => ∇_[m] (U m) (γ t)) hm hab hfli hgrad_cont hweak
  intro ψ w hψ hψc hts
  have hsc := weak_first_variation_scalar (m := m) (h := h) (γ := γ) hm hh hab hac hnc hmin hfin
    hψ hψc hts w
  have h1 : MeasureTheory.integral MeasureTheory.volume
      (fun t => deriv ψ t * (Finset.sum Finset.univ fun i =>
        m i * inner ℝ ((deriv γ t) i) (w i)))
      = ∫ t in a..b, deriv ψ t * massInner m (deriv γ t) w :=
    integral_eq_intervalIntegral_of_tsupport_subset hab (φ := fun t =>
        deriv ψ t * massInner m (deriv γ t) w) fun t ht => by
      have htd : t ∉ tsupport (deriv ψ) :=
        fun hmem => ht (hts (tsupport_deriv_subset hmem))
      rw [eq_zero_of_notMem_tsupport htd, zero_mul]
  have h2 : MeasureTheory.integral MeasureTheory.volume
      (fun t => ψ t * (Finset.sum Finset.univ fun i =>
        m i * inner ℝ ((∇_[m] (U m) (γ t)) i) (w i)))
      = ∫ t in a..b, ψ t * massInner m (∇_[m] (U m) (γ t)) w :=
    integral_eq_intervalIntegral_of_tsupport_subset hab (φ := fun t =>
        ψ t * massInner m (∇_[m] (U m) (γ t)) w) fun t ht => by
      have htt : t ∉ tsupport ψ := fun hmem => ht (hts hmem)
      rw [eq_zero_of_notMem_tsupport htt, zero_mul]
  rw [h1, h2]
  exact hsc

/-- **An `h`-minimiser is a genuine motion.**  On the interior of its interval of definition (where
it is collision free) an `h`-minimiser satisfies Newton's equations. -/
theorem minimizer_hasDerivAt_deriv {m : Fin N → ℝ} {h a b : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ a b)
    (hfin : actionPot m h (γ a) (γ b) < ⊤) :
    ∀ t ∈ Set.Ioo a b, HasDerivAt (deriv γ) (∇_[m] (U m) (γ t)) t := by
  classical
  have hγcont : ContinuousOn γ (Set.Icc a b) := by
    have h := hac.continuousOn
    rwa [uIcc_of_le hab.le] at h
  have hgrad_cont : ContinuousOn (fun t => ∇_[m] (U m) (γ t)) (Set.Icc a b) :=
    continuousOn_weightedGrad_comp (continuousOn_fderiv_U_comp (m := m) hγcont hnc)
  obtain ⟨cst, hcst⟩ := minimizer_deriv_ae_eq_primitive hm hh hab hac hnc hmin hfin
  -- continuity of the primitive
  have hPcont : ContinuousOn (fun x => cst + ∫ t in a..x, ∇_[m] (U m) (γ t)) (Set.Icc a b) := by
    have hii : MeasureTheory.IntegrableOn (fun t => ∇_[m] (U m) (γ t)) (Set.Icc a b)
        MeasureTheory.volume := hgrad_cont.integrableOn_Icc
    have h1 : ContinuousOn (fun x => ∫ t in Set.Ioc a x, ∇_[m] (U m) (γ t)) (Set.Icc a b) :=
      intervalIntegral.continuousOn_primitive hii
    have h2 : ContinuousOn (fun x => ∫ t in a..x, ∇_[m] (U m) (γ t)) (Set.Icc a b) :=
      h1.congr fun x hx => by rw [intervalIntegral.integral_of_le hx.1]
    exact h2.const_add cst
  have hPae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioo a b →
      deriv γ t = cst + ∫ s in a..t, ∇_[m] (U m) (γ s) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp hcst
  have hderivAt : ∀ t ∈ Set.Ioo a b,
      HasDerivAt γ (cst + ∫ s in a..t, ∇_[m] (U m) (γ s)) t :=
    Commons.Analysis.Calculus.hasDerivAt_of_ae_deriv_eq_continuousOn hab hac hPcont hPae
  intro t ht
  have hP : HasDerivAt (fun u => cst + ∫ s in a..u, ∇_[m] (U m) (γ s)) (∇_[m] (U m) (γ t)) t := by
    have hii : IntervalIntegrable (fun s => ∇_[m] (U m) (γ s)) volume a t := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le ht.1.le]
      exact hgrad_cont.mono (Set.Icc_subset_Icc_right ht.2.le)
    have hsm : StronglyMeasurableAtFilter (fun s => ∇_[m] (U m) (γ s)) (𝓝 t) volume :=
      (hgrad_cont.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht
    have hct : ContinuousAt (fun s => ∇_[m] (U m) (γ s)) t :=
      hgrad_cont.continuousAt (Icc_mem_nhds ht.1 ht.2)
    exact (intervalIntegral.integral_hasDerivAt_right hii hsm hct).const_add cst
  refine hP.congr_of_eventuallyEq ?_
  filter_upwards [IsOpen.mem_nhds isOpen_Ioo ht] with u hu
  exact (hderivAt u hu).deriv

/-- The second derivative of an `h`-minimiser is the force: Newton's equations. -/
theorem minimizer_iteratedDeriv_two {m : Fin N → ℝ} {h a b : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ a b)
    (hfin : actionPot m h (γ a) (γ b) < ⊤) :
    ∀ t ∈ Set.Ioo a b, iteratedDeriv 2 γ t = ∇_[m] (U m) (γ t) := by
  intro t ht
  have h := minimizer_hasDerivAt_deriv hm hh hab hac hnc hmin hfin t ht
  rw [show iteratedDeriv 2 γ = deriv (deriv γ) from by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]]
  exact h.deriv

/-- On the interior of its interval of definition an `h`-minimiser is differentiable with its own
derivative as derivative. -/
theorem minimizer_hasDerivAt {m : Fin N → ℝ} {h a b : ℝ} {γ : ℝ → EN E N}
    (hac : AbsolutelyContinuousOnInterval γ a b) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioo a b → HasDerivAt γ (deriv γ t) t := by
  have hae := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_ae_differentiableAt_vector
    hac
  filter_upwards [hae] with t ht htI
  exact (ht (Set.Icc_subset_uIcc ⟨htI.1.le, htI.2.le⟩)).hasDerivAt

/-- **An `h`-minimiser is `C²` off collisions.** -/
theorem minimizer_contDiffOn_two {m : Fin N → ℝ} {h a b : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ a b)
    (hfin : actionPot m h (γ a) (γ b) < ⊤) :
    ContDiffOn ℝ 2 γ (Set.Ioo a b) := by
  classical
  have hγcont : ContinuousOn γ (Set.Icc a b) := by
    have h := hac.continuousOn
    rwa [uIcc_of_le hab.le] at h
  have hgrad_cont : ContinuousOn (fun t => ∇_[m] (U m) (γ t)) (Set.Icc a b) :=
    continuousOn_weightedGrad_comp (continuousOn_fderiv_U_comp (m := m) hγcont hnc)
  obtain ⟨cst, hcst⟩ := minimizer_deriv_ae_eq_primitive hm hh hab hac hnc hmin hfin
  let P : ℝ → EN E N := fun x => cst + ∫ t in a..x, ∇_[m] (U m) (γ t)
  have hPcont : ContinuousOn P (Set.Icc a b) := by
    have hii : MeasureTheory.IntegrableOn (fun t => ∇_[m] (U m) (γ t)) (Set.Icc a b)
        MeasureTheory.volume := hgrad_cont.integrableOn_Icc
    have h1 : ContinuousOn (fun x => ∫ t in Set.Ioc a x, ∇_[m] (U m) (γ t)) (Set.Icc a b) :=
      intervalIntegral.continuousOn_primitive hii
    have h2 : ContinuousOn (fun x => ∫ t in a..x, ∇_[m] (U m) (γ t)) (Set.Icc a b) :=
      h1.congr fun x hx => by rw [intervalIntegral.integral_of_le hx.1]
    exact h2.const_add cst
  have hPae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioo a b → deriv γ t = P t :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp hcst
  have hderivAt : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (P t) t :=
    Commons.Analysis.Calculus.hasDerivAt_of_ae_deriv_eq_continuousOn hab hac hPcont hPae
  have hderiv_eq : ∀ t ∈ Set.Ioo a b, deriv γ t = P t := fun t ht => (hderivAt t ht).deriv
  have hPderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt P (∇_[m] (U m) (γ t)) t := by
    intro t ht
    have hii : IntervalIntegrable (fun s => ∇_[m] (U m) (γ s)) volume a t := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le ht.1.le]
      exact hgrad_cont.mono (Set.Icc_subset_Icc_right ht.2.le)
    have hsm : StronglyMeasurableAtFilter (fun s => ∇_[m] (U m) (γ s)) (𝓝 t) volume :=
      (hgrad_cont.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht
    have hct : ContinuousAt (fun s => ∇_[m] (U m) (γ s)) t :=
      hgrad_cont.continuousAt (Icc_mem_nhds ht.1 ht.2)
    exact (intervalIntegral.integral_hasDerivAt_right hii hsm hct).const_add cst
  have hP1 : ContDiffOn ℝ 1 P (Set.Ioo a b) :=
    (contDiffOn_succ_iff_deriv_of_isOpen (n := (0 : WithTop ℕ∞)) isOpen_Ioo
      (f := P) (s := Set.Ioo a b)).mpr
      ⟨fun t ht => (hPderiv t ht).differentiableAt.differentiableWithinAt,
        (fun h => absurd h (by simp)),
        by
          rw [contDiffOn_zero]
          exact (hgrad_cont.mono Set.Ioo_subset_Icc_self).congr
            fun t ht => (hPderiv t ht).deriv⟩
  have hderiv1 : ContDiffOn ℝ 1 (deriv γ) (Set.Ioo a b) :=
    hP1.congr fun t ht => hderiv_eq t ht
  exact (contDiffOn_succ_iff_deriv_of_isOpen (n := (1 : WithTop ℕ∞)) isOpen_Ioo
    (f := γ) (s := Set.Ioo a b)).mpr
    ⟨fun t ht => (hderivAt t ht).differentiableAt.differentiableWithinAt,
      (fun h => absurd h (by simp)), hderiv1⟩

/-- Energy conservation for an `h`-minimiser. -/
theorem minimizer_energy_eq {m : Fin N → ℝ} {h a b : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t))
    (hmin : IsHMinimizer m h γ a b)
    (hfin : actionPot m h (γ a) (γ b) < ⊤) :
    ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, energy m γ s = energy m γ t := by
  classical
  have hmne : ∀ i, m i ≠ 0 := fun i => ne_of_gt (hm i)
  have hdiff : ContDiffOn ℝ 2 γ (Set.Ioo a b) :=
    minimizer_contDiffOn_two hm hh hab hac hnc hmin hfin
  have heq : ∀ t ∈ Set.Ioo a b, iteratedDeriv 2 γ t = ∇_[m] (U m) (γ t) :=
    minimizer_iteratedDeriv_two hm hh hab hac hnc hmin hfin
  have hnc' : ∀ t ∈ Set.Ioo a b, WithoutCollisions (γ t) :=
    fun t ht => hnc t ⟨ht.1.le, ht.2.le⟩
  have hzero : ∀ t ∈ Set.Ioo a b, HasDerivAt (energy m γ) 0 t := by
    intro t ht
    have hcAt : ContDiffAt ℝ 2 γ t := hdiff.contDiffAt (isOpen_Ioo.mem_nhds ht)
    have hdy : HasDerivAt γ (deriv γ t) t := (hcAt.differentiableAt (by norm_num)).hasDerivAt
    have hd2 : HasDerivAt (deriv γ) (iteratedDeriv 2 γ t) t := hasDerivAt_deriv_of_contDiffAt hcAt
    have hkin : HasDerivAt (fun s : ℝ => (1 / 2) * ∑ i, m i * ‖deriv γ s i‖ ^ 2)
        ((1 / 2) * (∑ i, m i * (2 * inner ℝ (deriv γ t i) (iteratedDeriv 2 γ t i)))) t :=
      HasDerivAt.const_mul (𝔸 := ℝ) (1 / 2) (hasDerivAt_kinetic_sum m hd2)
    have hpot : HasDerivAt (fun s : ℝ => U m (γ s)) ((fderiv ℝ (U m) (γ t)) (deriv γ t)) t := by
      have hU_at : HasFDerivAt (U m) (fderiv ℝ (U m) (γ t)) (γ t) :=
        (hasFDerivAt_U m (γ t) (hnc' t ht)).differentiableAt.hasFDerivAt
      simpa [Function.comp_def] using hU_at.comp_hasDerivAt t hdy
    have hE : HasDerivAt (energy m γ)
        ((1 / 2) * (∑ i, m i * (2 * inner ℝ (deriv γ t i) (iteratedDeriv 2 γ t i))) -
          (fderiv ℝ (U m) (γ t)) (deriv γ t)) t := by
      have hE' := hkin.sub hpot
      rw [show (fun s : ℝ => (1 / 2) * ∑ i, m i * ‖deriv γ s i‖ ^ 2) - (fun s : ℝ => U m (γ s))
          = energy m γ by
        funext s
        simp [energy, Pi.sub_apply]] at hE'
      exact hE'
    have hkey : (fderiv ℝ (U m) (γ t)) (deriv γ t) =
        ∑ i, m i * inner ℝ (iteratedDeriv 2 γ t i) (deriv γ t i) := by
      rw [← inner_gradient_eq_fderiv (γ t) (deriv γ t)]
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [gradient_eq_smul_weightedGrad m hmne (γ t) i, ← heq t ht]
      rw [inner_smul_left]
      simp
    rw [hkey] at hE
    have hzero' : (1 / 2) * (∑ i, m i * (2 * inner ℝ (deriv γ t i) (iteratedDeriv 2 γ t i))) -
        (∑ i, m i * inner ℝ (iteratedDeriv 2 γ t i) (deriv γ t i)) = 0 := by
      rw [Finset.mul_sum, sub_eq_zero]
      apply Finset.sum_congr rfl
      intro i hi
      rw [real_inner_comm]
      ring
    rwa [hzero'] at hE
  have hdiffE : DifferentiableOn ℝ (energy m γ) (Set.Ioo a b) := fun x hx =>
    (hzero x hx).differentiableAt.differentiableWithinAt
  have hfderiv : ∀ x ∈ Set.Ioo a b, fderivWithin ℝ (energy m γ) (Set.Ioo a b) x = 0 := by
    intro x hx
    have hf : fderiv ℝ (energy m γ) x = 0 := by
      simpa using (hzero x hx).hasFDerivAt.fderiv
    rw [fderivWithin_of_isOpen isOpen_Ioo hx, hf]
  intro s hs t ht
  exact Convex.is_const_of_fderivWithin_eq_zero (convex_Ioo a b) hdiffE hfderiv hs ht

end Submission.NBody
