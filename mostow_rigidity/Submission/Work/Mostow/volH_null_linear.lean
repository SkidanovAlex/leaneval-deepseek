import Mathlib
import Submission.Work.Mostow.VolDefs
import Submission.Work.Mostow.BaryBase

/-!
# Level sets of `u ↦ ⟪a,u⟫ + b·√(1+‖u‖²)` are `volH`-null

In the chart `E n = EuclideanSpace ℝ (Fin n)` of ℍⁿ, the set
`{u | ⟪a,u⟫ + b·tpart u = 0}` (a horosphere, a geodesic hyperplane, or empty, according to the
sign of `‖a‖² - b²`, and with `tpart u = √(1+‖u‖²)`) is a level set of a smooth function with
nowhere-vanishing gradient; in particular it has zero `volH`-measure.

The proof is elementary: `volH` is absolutely continuous with respect to Lebesgue measure with a
strictly positive density, so it suffices to show that `S` is Lebesgue-null.  Writing
`E n = (aᗮ) × ℝ` via the orthogonal decomposition along `a`, Fubini reduces this to the fact that
along each line parallel to `a` the equation is a genuine quadratic, hence has at most two
solutions.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- Pythagorean identity: if `z` is a unit vector orthogonal to `v`, then
`‖v + s • z‖ ^ 2 = ‖v‖ ^ 2 + s ^ 2`. -/
theorem volH_null_linear_norm_sq {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
    (v z : F) (s : ℝ) (hz : ‖z‖ = 1) (hv : inner ℝ v z = 0) :
    ‖v + s • z‖ ^ 2 = ‖v‖ ^ 2 + s ^ 2 := by
  have h1 : inner ℝ v (s • z) = 0 := by rw [real_inner_smul_right, hv, mul_zero]
  rw [pow_two, pow_two, pow_two,
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero v (s • z) h1,
      norm_smul, hz, mul_one, Real.norm_eq_abs, abs_mul_abs_self]

/-- One-dimensional section estimate: the set of solutions of
`c·s + b·√(1 + (r + s²)) = 0` (with `c > 0`, `r ≥ 0`) is finite, hence Lebesgue-null. -/
theorem volH_null_linear_section (c b : ℝ) (hc : 0 < c) (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure ℝ) {s : ℝ | s * c + b * Real.sqrt (1 + (r + s ^ 2)) = 0} = 0 := by
  set R : ℝ := b ^ 2 * (1 + r) / (c ^ 2 - b ^ 2) with hR
  have hsub : {s : ℝ | s * c + b * Real.sqrt (1 + (r + s ^ 2)) = 0} ⊆
      {s : ℝ | (c ^ 2 - b ^ 2) * s ^ 2 = b ^ 2 * (1 + r)} := by
    intro s hs
    have hs' : s * c + b * Real.sqrt (1 + (r + s ^ 2)) = 0 := hs
    show (c ^ 2 - b ^ 2) * s ^ 2 = b ^ 2 * (1 + r)
    have hpos : (0 : ℝ) < 1 + (r + s ^ 2) := by nlinarith [sq_nonneg s]
    have h1 : s * c = - b * Real.sqrt (1 + (r + s ^ 2)) := by linarith
    have h2 : (s * c) ^ 2 = b ^ 2 * (1 + (r + s ^ 2)) := by
      calc (s * c) ^ 2 = (-(b * Real.sqrt (1 + (r + s ^ 2)))) ^ 2 := by rw [h1]; ring
        _ = (b * Real.sqrt (1 + (r + s ^ 2))) ^ 2 := by ring
        _ = b ^ 2 * (Real.sqrt (1 + (r + s ^ 2))) ^ 2 := by ring
        _ = b ^ 2 * (1 + (r + s ^ 2)) := by rw [Real.sq_sqrt (le_of_lt hpos)]
    nlinarith [h2]
  by_cases hb : b = 0
  · have hsub1 : {s : ℝ | s * c + b * Real.sqrt (1 + (r + s ^ 2)) = 0} ⊆ {0} := by
      intro s hs
      have hs' : s * c + b * Real.sqrt (1 + (r + s ^ 2)) = 0 := hs
      rw [hb, zero_mul, add_zero] at hs'
      show s ∈ ({0} : Set ℝ)
      rw [Set.mem_singleton_iff]
      rcases mul_eq_zero.mp hs' with h | h
      · exact h
      · exact absurd h (ne_of_gt hc)
    exact measure_mono_null hsub1 (by simp)
  · by_cases hA : c ^ 2 - b ^ 2 = 0
    · have hempty : {s : ℝ | s * c + b * Real.sqrt (1 + (r + s ^ 2)) = 0} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro s hs
        have h1 : (c ^ 2 - b ^ 2) * s ^ 2 = b ^ 2 * (1 + r) := hsub hs
        rw [hA, zero_mul] at h1
        have : 0 < b ^ 2 * (1 + r) := by positivity
        linarith
      rw [hempty, measure_empty]
    · have hfin : ({s : ℝ | s * c + b * Real.sqrt (1 + (r + s ^ 2)) = 0} : Set ℝ).Finite := by
        refine (Set.finite_singleton (-Real.sqrt R)).insert (Real.sqrt R) |>.subset ?_
        intro s hs
        have h1 : (c ^ 2 - b ^ 2) * s ^ 2 = b ^ 2 * (1 + r) := hsub hs
        have hs2 : s ^ 2 = R := by
          rw [hR]; field_simp; linarith [h1]
        show s = Real.sqrt R ∨ s = -Real.sqrt R
        by_cases hRnn : 0 ≤ R
        · have hsq : s ^ 2 = (Real.sqrt R) ^ 2 := by rw [hs2, Real.sq_sqrt hRnn]
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
          · exact Or.inl h
          · exact Or.inr h
        · have : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
          linarith
      exact Set.Finite.measure_zero hfin (volume : Measure ℝ)

/-- The main lemma: a level set of `u ↦ ⟪a,u⟫ + b·tpart u` with `(a,b) ≠ 0` is `volH`-null. -/
theorem volH_null_linear (n : ℕ) (a : Submission.Mostow.E n) (b : ℝ)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    Submission.Mostow.volH n {u : Submission.Mostow.E n |
      inner ℝ a u + b * Submission.Mostow.tpart u = 0} = 0 := by
  rw [volHNull]
  by_cases ha : a = 0
  · -- `a = 0`: then `b ≠ 0` and the set is empty.
    subst ha
    have hb : b ≠ 0 := hab.resolve_left (by simp)
    have hS : {u : E n | inner ℝ (0 : E n) u + b * tpart u = 0} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro u hu
      have hu' : inner ℝ (0 : E n) u + b * tpart u = 0 := hu
      rw [inner_zero_left, zero_add] at hu'
      exact (mul_ne_zero hb (ne_of_gt (tpart_pos u))) hu'
    rw [hS, measure_empty]
  · by_cases hb : b = 0
    · -- `b = 0`, `a ≠ 0`: the set is the kernel of the functional `⟪a,·⟫`, a proper subspace.
      subst hb
      have hS : {u : E n | inner ℝ a u + 0 * tpart u = 0} =
          (LinearMap.ker (innerSL ℝ a).toLinearMap : Set (E n)) := by
        ext u
        show (inner ℝ a u + 0 * tpart u = 0) ↔
          (u ∈ LinearMap.ker (innerSL ℝ a).toLinearMap)
        rw [LinearMap.mem_ker]
        simp
      rw [hS]
      refine Measure.addHaar_submodule (volume : Measure (E n)) _ ?_
      intro htop
      have hmem : a ∈ LinearMap.ker (innerSL ℝ a).toLinearMap := by rw [htop]; trivial
      rw [LinearMap.mem_ker] at hmem
      have hmem' : inner ℝ a a = 0 := hmem
      rw [real_inner_self_eq_norm_sq] at hmem'
      have ha0 : ‖a‖ = 0 := by
        have h2 : ‖a‖ ^ 2 = 0 := hmem'
        nlinarith [norm_nonneg a, h2]
      exact ha (norm_eq_zero.mp ha0)
    · -- `a ≠ 0`, `b ≠ 0`: Fubini along the orthogonal decomposition `E n = aᗮ × ℝ`.
      set z : E n := (‖a‖)⁻¹ • a with hz
      set K : Submodule ℝ (E n) := LinearMap.ker (innerSL ℝ a).toLinearMap with hK
      set L : K × ℝ →ₗ[ℝ] E n :=
        (Submodule.subtype K).coprod (LinearMap.toSpanSingleton ℝ (E n) z) with hL
      have hanorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
      have hLapply : ∀ (v : K) (s : ℝ), L (v, s) = (v : E n) + s • z := by
        intro v s; simp [hL, LinearMap.coprod_apply]
      have hKmem : ∀ v : K, inner ℝ a (v : E n) = 0 := by
        intro v
        have hv : (v : E n) ∈ (LinearMap.ker (innerSL ℝ a).toLinearMap : Submodule ℝ (E n)) := by
          rw [← hK]; exact v.2
        rw [LinearMap.mem_ker] at hv
        exact hv
      have hznorm : ‖z‖ = 1 := by
        rw [hz, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hanorm]
        field_simp
      have hzorth : ∀ v : K, inner ℝ (v : E n) z = 0 := by
        intro v
        rw [hz, inner_smul_right, real_inner_comm, hKmem v, mul_zero]
      have hainnerz : inner ℝ a z = ‖a‖ := by
        rw [hz, inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      have htp : ∀ (v : K) (s : ℝ), tpart ((v : E n) + s • z) =
          Real.sqrt (1 + (‖(v : E n)‖ ^ 2 + s ^ 2)) := by
        intro v s
        rw [tpart, volH_null_linear_norm_sq (v : E n) z s hznorm (hzorth v)]
      -- `L` is onto: every `u` is `(u - (⟪a,u⟫/‖a‖) z) + (⟪a,u⟫/‖a‖) z`.
      have hsurj : Function.Surjective L := by
        intro u
        refine ⟨(⟨u - (inner ℝ a u / ‖a‖) • z, ?_⟩, inner ℝ a u / ‖a‖), ?_⟩
        · show inner ℝ a (u - (inner ℝ a u / ‖a‖) • z) = 0
          rw [inner_sub_right, inner_smul_right, hainnerz]
          field_simp
          ring
        · rw [hLapply, sub_add_cancel]
      have hHaar : Measure.IsAddHaarMeasure (volume : Measure (K × ℝ)) :=
        Measure.prod.instIsAddHaarMeasure (volume : Measure K) (volume : Measure ℝ)
      obtain ⟨cc, hcc, hcmap⟩ :=
        LinearMap.exists_map_addHaar_eq_smul_addHaar L volume volume hsurj
      have hSmeas : MeasurableSet {u : E n | inner ℝ a u + b * tpart u = 0} := by
        have hcont : Continuous (fun u : E n => inner ℝ a u + b * tpart u) := by
          have h1 : Continuous (fun u : E n => inner ℝ a u) := by fun_prop
          exact h1.add (continuous_const.mul continuous_tpart)
        exact (isClosed_eq hcont continuous_const).measurableSet
      have hpre_meas : MeasurableSet (L ⁻¹' {u : E n | inner ℝ a u + b * tpart u = 0}) :=
        hSmeas.preimage (LinearMap.continuous_of_finiteDimensional L).measurable
      -- The fibre of `L ⁻¹' S` over `v` is the finite set of the one-dimensional estimate.
      have hsec : ∀ v : K,
          volume (Prod.mk v ⁻¹' (L ⁻¹' {u : E n | inner ℝ a u + b * tpart u = 0})) = 0 := by
        intro v
        have hset : Prod.mk v ⁻¹' (L ⁻¹' {u : E n | inner ℝ a u + b * tpart u = 0}) =
            {s : ℝ | s * ‖a‖ + b * Real.sqrt (1 + (‖(v : E n)‖ ^ 2 + s ^ 2)) = 0} := by
          ext s
          show inner ℝ a (L (v, s)) + b * tpart (L (v, s)) = 0 ↔
              s * ‖a‖ + b * Real.sqrt (1 + (‖(v : E n)‖ ^ 2 + s ^ 2)) = 0
          rw [hLapply v s, inner_add_right, hKmem v, zero_add, inner_smul_right, hainnerz,
              htp v s]
        rw [hset]
        exact volH_null_linear_section ‖a‖ b hanorm (‖(v : E n)‖ ^ 2) (by positivity)
      have hpre_zero : volume (L ⁻¹' {u : E n | inner ℝ a u + b * tpart u = 0}) = 0 := by
        rw [Measure.volume_eq_prod, Measure.prod_apply hpre_meas]
        simp only [hsec, lintegral_zero]
      -- Transfer the nullity back along the surjection `L`.
      have hmap := Measure.map_apply (μ := (volume : Measure (K × ℝ))) (f := ⇑L)
        (LinearMap.continuous_of_finiteDimensional L).measurable hSmeas
      rw [hcmap, Measure.smul_apply] at hmap
      rw [hpre_zero] at hmap
      rw [smul_eq_mul] at hmap
      rcases mul_eq_zero.mp hmap with h0 | h0
      · exact absurd h0 (ne_of_gt hcc)
      · exact h0

end

end Work.Mostow
