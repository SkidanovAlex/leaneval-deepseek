import ChallengeDeps
import Submission.NBody.Chazy
import Submission.Commons.Analysis.Calculus.norm_sub_le_of_hasDerivAt_of_norm_le_inv_sq
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Monotone

/-!
# The invariant tube (Chazy's continuity of the limit shape)

The second part of Chazy's lemma says that a motion which starts close enough to a hyperbolic
motion stays close to it forever: the "tube" `‖z - t·a‖ < t ρ` around the ray `t ↦ t · a` (in
position space) and the ball `B(a, 2ρ/3)` (in velocity space) are invariant, provided `a` has no
collisions, `ρ` is small enough that the ball `B(a,ρ)` is collision-free and `K/t₁ < ρ/3`, where
`K` bounds the mass-weighted force on `B(a,ρ)`.

The mechanism is the integrability of the force at infinity: on the tube the force is bounded by
`K/t²`, so the total variation of the velocity after time `t₁` is at most `K/t₁ < ρ/3`; the
velocity therefore stays within `2ρ/3` of `a`, which in turn keeps the position inside the tube.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators
open scoped Topology

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Invariant tube.**  Let `a` be collision-free, `ρ > 0` such that `B(a,ρ)` is collision-free
and the mass-weighted force is bounded by `K` on `B(a,ρ)`, and let `t₁ > 0` with `K/t₁ < ρ/3`.
Then every solution of the state equation on `[t₁,∞)` whose state at `t₁` satisfies
`‖x(t₁) - t₁·a‖ < t₁ρ/3` and `‖v(t₁) - a‖ < ρ/3` satisfies `‖x(t) - t·a‖ < tρ` and
`‖v(t) - a‖ < 2ρ/3` for all `t ≥ t₁`. -/
theorem invariant_tube (m : Fin N → ℝ) {a : EN E N} {ρ K t₁ : ℝ}
    (hρ : 0 < ρ) (ht₁ : 0 < t₁) (htK : K / t₁ < ρ / 3)
    (hnc : ∀ y : EN E N, dist y a ≤ ρ → WithoutCollisions y)
    (hb : ∀ y : EN E N, dist y a ≤ ρ → ‖weightedGrad m (U m) y‖ ≤ K)
    {z : ℝ → EN E N × EN E N} (hz : ∀ t ∈ Ici t₁, HasDerivAt z (stateField m (z t)) t)
    (hpos : dist (z t₁).1 (t₁ • a) < t₁ * ρ / 3) (hvel : dist (z t₁).2 a < ρ / 3) :
    ∀ t ≥ t₁, dist (z t).1 (t • a) < t * ρ ∧ dist (z t).2 a < 2 * ρ / 3 := by
  have hfst : ∀ u ∈ Ici t₁, HasDerivAt (fun v : ℝ => (z v).1) ((z u).2) u := by
    intro u hu
    have h := (ContinuousLinearMap.fst ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt u (hz u hu)
    simpa [stateField, Function.comp_def] using h
  have hsnd : ∀ u ∈ Ici t₁, HasDerivAt (fun v : ℝ => (z v).2)
      (weightedGrad m (U m) (z u).1) u := by
    intro u hu
    have h := (ContinuousLinearMap.snd ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt u (hz u hu)
    simpa [stateField, Function.comp_def] using h
  -- normalizing the configuration puts it inside the collision-free ball
  have hnormTube : ∀ u : ℝ, 0 < u → dist (z u).1 (u • a) < u * ρ →
      dist (u⁻¹ • (z u).1) a < ρ := by
    intro u hu0 hPu
    have hsm : u⁻¹ • (u • a) = a := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hu0), one_smul]
    have h1 : dist (u⁻¹ • (z u).1) (u⁻¹ • (u • a)) = ‖(u⁻¹ : ℝ)‖ * dist (z u).1 (u • a) :=
      dist_smul₀ _ _ _
    rw [hsm] at h1
    rw [h1, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu0)]
    calc u⁻¹ * dist (z u).1 (u • a) < u⁻¹ * (u * ρ) := by gcongr
      _ = ρ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hu0), one_mul]
  -- the collision-free condition holds on the tube
  have hncTube : ∀ u ∈ Ici t₁, dist (z u).1 (u • a) < u * ρ → WithoutCollisions (z u).1 := by
    intro u hu hPu
    have hu0 : 0 < u := lt_of_lt_of_le ht₁ hu
    have h1 := hnc _ (hnormTube u hu0 hPu).le
    have hzu : (z u).1 = u • (u⁻¹ • (z u).1) := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hu0), one_smul]
    rw [hzu]
    exact withoutCollisions_smul h1 (ne_of_gt hu0)
  -- the force is bounded by `K/u²` on the tube
  have hforce : ∀ u ∈ Ici t₁, dist (z u).1 (u • a) < u * ρ →
      ‖weightedGrad m (U m) (z u).1‖ ≤ K / u ^ 2 := by
    intro u hu hPu
    have hu0 : 0 < u := lt_of_lt_of_le ht₁ hu
    have hw := hnormTube u hu0 hPu
    have hnc' := hnc _ hw.le
    have hb' := hb _ hw.le
    have hzu : (z u).1 = u • (u⁻¹ • (z u).1) := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hu0), one_smul]
    rw [hzu, weightedGrad_U_smul m hu0 _ hnc', norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (u ^ 2)⁻¹)]
    calc (u ^ 2)⁻¹ * ‖weightedGrad m (U m) (u⁻¹ • (z u).1)‖ ≤ (u ^ 2)⁻¹ * K :=
          mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = K / u ^ 2 := by rw [div_eq_inv_mul]
  -- velocity estimate
  have velEst : ∀ s ≥ t₁, (∀ u ∈ Icc t₁ s, dist (z u).1 (u • a) < u * ρ) →
      dist (z s).2 a < 2 * ρ / 3 := by
    intro s hs hP
    have hf' : ∀ u ∈ Icc t₁ s, HasDerivAt (fun v : ℝ => (z v).2)
        (weightedGrad m (U m) (z u).1) u := fun u hu => hsnd u hu.1
    have hcont : ContinuousOn (fun u : ℝ => weightedGrad m (U m) (z u).1) (Icc t₁ s) := by
      have hzcont : ContinuousOn z (Icc t₁ s) :=
        fun u hu => (hz u hu.1).continuousAt.continuousWithinAt
      have hmaps : MapsTo z (Icc t₁ s) {w : EN E N × EN E N | WithoutCollisions w.1} :=
        fun u hu => hncTube u hu.1 (hP u hu)
      have hcomp := ((continuous_snd.continuousOn).comp (continuousOn_stateField m)
        (fun w _ => Set.mem_univ (stateField m w))).comp hzcont hmaps
      simpa [stateField, Function.comp_def] using hcomp
    have hbd : ∀ u ∈ Icc t₁ s, ‖weightedGrad m (U m) (z u).1‖ ≤ K / u ^ 2 :=
      fun u hu => hforce u hu.1 (hP u hu)
    have hmain := Commons.Analysis.Calculus.norm_sub_le_of_hasDerivAt_of_norm_le_inv_sq
      ht₁ hs hf' hcont hbd
    calc dist (z s).2 a ≤ dist (z s).2 (z t₁).2 + dist (z t₁).2 a := dist_triangle _ _ _
      _ = ‖(z s).2 - (z t₁).2‖ + dist (z t₁).2 a := by rw [dist_eq_norm]
      _ ≤ K / t₁ + ρ / 3 := add_le_add hmain hvel.le
      _ < 2 * ρ / 3 := by linarith
  -- position estimate
  have propEst : ∀ s ≥ t₁, (∀ u ∈ Icc t₁ s, dist (z u).2 a < 2 * ρ / 3) →
      dist (z s).1 (s • a) < (2 * s - t₁) * ρ / 3 := by
    intro s hs hV
    have hf' : ∀ u ∈ Icc t₁ s, HasDerivAt (fun v : ℝ => (z v).1 - v • a) ((z u).2 - a) u := by
      intro u hu
      have h2 : HasDerivAt (fun v : ℝ => v • a) a u := by
        simpa using (hasDerivAt_id u).smul_const a
      exact (hfst u hu.1).sub h2
    have hbound : ∀ u ∈ Icc t₁ s, ‖(z u).2 - a‖ ≤ 2 * ρ / 3 := by
      intro u hu
      have h := hV u hu
      rw [dist_eq_norm] at h
      exact h.le
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Icc t₁ s)
      (f := fun v : ℝ => (z v).1 - v • a) (f' := fun u => (z u).2 - a) (C := 2 * ρ / 3)
      (fun u hu => (hf' u hu).hasDerivWithinAt) hbound (convex_Icc t₁ s)
      (left_mem_Icc.mpr hs) (right_mem_Icc.mpr hs)
    have hs1 : ‖s - t₁‖ = s - t₁ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs)]
    have hineq : ‖(fun v : ℝ => (z v).1 - v • a) s - (fun v : ℝ => (z v).1 - v • a) t₁‖
        ≤ (2 * ρ / 3) * (s - t₁) := by
      simpa [hs1] using hmvt
    have htri : ‖(fun v : ℝ => (z v).1 - v • a) s‖
        ≤ ‖(fun v : ℝ => (z v).1 - v • a) s - (fun v : ℝ => (z v).1 - v • a) t₁‖
          + ‖(fun v : ℝ => (z v).1 - v • a) t₁‖ := by
      have h := dist_triangle ((fun v : ℝ => (z v).1 - v • a) s)
        ((fun v : ℝ => (z v).1 - v • a) t₁) 0
      simpa [dist_eq_norm] using h
    have hnorm₁ : ‖(fun v : ℝ => (z v).1 - v • a) t₁‖ = dist (z t₁).1 (t₁ • a) := by
      simp [dist_eq_norm]
    have hfirst : ‖(fun v : ℝ => (z v).1 - v • a) s‖ = dist (z s).1 (s • a) := by
      simp [dist_eq_norm]
    rw [hfirst, hnorm₁] at htri
    have harith : (2 * s - t₁) * ρ / 3 = t₁ * ρ / 3 + (2 * ρ / 3) * (s - t₁) := by ring
    rw [harith]
    linarith [htri, hineq, hpos]
  -- the tube predicate and the set of times at which it has been verified
  let Tube : ℝ → Prop := fun s => dist (z s).1 (s • a) < s * ρ ∧ dist (z s).2 a < 2 * ρ / 3
  let C : Set ℝ := {t | ∀ s, t₁ < s → s < t → Tube s}
  have hT₁ : Tube t₁ := ⟨by nlinarith [hpos, ht₁], by linarith [hvel, hρ]⟩
  have hCclosed : IsClosed C := by
    show IsClosed {t : ℝ | ∀ s, t₁ < s → s < t → Tube s}
    have hEq : {t : ℝ | ∀ s, t₁ < s → s < t → Tube s}
        = ⋂ (s : ℝ), {t : ℝ | t₁ < s → s < t → Tube s} := by
      ext t; simp
    rw [hEq]
    refine isClosed_iInter fun s => ?_
    by_cases hst : t₁ < s
    · by_cases hPs : Tube s
      · have : {t : ℝ | t₁ < s → s < t → Tube s} = univ := by
          ext t; simp [hst, hPs]
        rw [this]; exact isClosed_univ
      · have : {t : ℝ | t₁ < s → s < t → Tube s} = Iic s := by
          ext t
          simp only [Set.mem_Iic]
          constructor
          · intro h
            by_contra hlt
            exact hPs (h hst (not_le.mp hlt))
          · intro h hts hst
            exact absurd hst (not_lt.mpr h)
        rw [this]; exact isClosed_Iic
    · have : {t : ℝ | t₁ < s → s < t → Tube s} = univ := by
        ext t; simp [hst]
      rw [this]; exact isClosed_univ
  have ht₁C : t₁ ∈ C := by
    intro s hs h2
    exact absurd h2 (not_lt.mpr hs.le)
  -- both components are open conditions at every time
  have hopen : ∀ t : ℝ, t₁ ≤ t → Tube t → ∃ η > 0, ∀ s ∈ Ioo (t - η) (t + η), Tube s := by
    intro t ht hTt
    have hzt : ContinuousAt z t := (hz t ht).continuousAt
    have hcontP : ContinuousAt (fun s : ℝ => s * ρ - dist ((z s).1) (s • a)) t :=
      (continuousAt_id.mul_const ρ).sub
        (((continuous_fst.continuousAt.comp hzt).dist (continuous_id.smul continuous_const).continuousAt))
    have hcontV : ContinuousAt (fun s : ℝ => dist ((z s).2) a) t :=
      ((continuous_snd.continuousAt.comp hzt).dist continuous_const.continuousAt)
    have h1 : ∀ᶠ s in 𝓝 t, dist (z s).1 (s • a) < s * ρ := by
      have hpos' : 0 < t * ρ - dist ((z t).1) (t • a) := by linarith [hTt.1]
      filter_upwards [hcontP.eventually (isOpen_Ioi.mem_nhds hpos')] with s hs
      linarith
    have h2 : ∀ᶠ s in 𝓝 t, dist (z s).2 a < 2 * ρ / 3 :=
      hcontV.eventually (isOpen_Iio.mem_nhds hTt.2)
    obtain ⟨η, hη, hηP⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and h2)
    refine ⟨η, hη, fun s hs => hηP s ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- main dichotomy: either the verification can always be continued (done), or a maximal
  -- verification time `T` exists and leads to a contradiction
  have key : ∀ t ≥ t₁, Tube t := by
    intro t ht
    by_cases hbd : BddAbove C
    · exfalso
      set T : ℝ := sSup C
      have hTmem : T ∈ C := by
        have h := csSup_mem_closure ⟨t₁, ht₁C⟩ hbd
        rwa [hCclosed.closure_eq] at h
      have hTgt : t₁ < T := by
        obtain ⟨η, hη, hηP⟩ := hopen t₁ le_rfl hT₁
        have hs₀C : t₁ + η / 2 ∈ C := by
          intro s hs1 hs2
          exact hηP s ⟨by linarith, by linarith⟩
        have := le_csSup hbd hs₀C
        linarith
      have huT : ∀ u, t₁ < u → u < T → Tube u := fun u h1 h2 => hTmem u h1 h2
      -- the position condition holds at `T` by continuity
      have hPT : dist (z T).1 (T • a) < T * ρ := by
        have hgcont : Tendsto (fun s : ℝ => dist ((z s).1) (s • a)) (𝓝[<] T)
            (𝓝 (dist ((z T).1) (T • a))) := by
          have : ContinuousAt (fun s : ℝ => dist ((z s).1) (s • a)) T :=
            ((continuous_fst.continuousAt.comp (hz T hTgt.le).continuousAt).dist
              (continuous_id.smul continuous_const).continuousAt)
          exact this.continuousWithinAt
        have hbnd : ∀ᶠ s in 𝓝[<] T,
            dist ((z s).1) (s • a) ≤ (2 * s - t₁) * ρ / 3 := by
          filter_upwards [Ioo_mem_nhdsLT hTgt] with s hs
          have hV : ∀ u ∈ Icc t₁ s, dist (z u).2 a < 2 * ρ / 3 := by
            intro u hu
            rcases eq_or_lt_of_le hu.1 with h | h
            · rw [← h]; linarith [hvel, hρ]
            · exact (huT u h (lt_of_le_of_lt hu.2 hs.2)).2
          exact (propEst s hs.1.le hV).le
        have hlin : Tendsto (fun s : ℝ => (2 * s - t₁) * ρ / 3) (𝓝[<] T)
            (𝓝 ((2 * T - t₁) * ρ / 3)) := by
          have h1 : ContinuousAt (fun s : ℝ => (2 * s - t₁) * ρ / 3) T := by
            have h2 : ContinuousAt (fun s : ℝ => 2 * s - t₁) T :=
              (continuousAt_id.const_mul 2).sub_const t₁
            exact ContinuousAt.div_const (h2.mul_const ρ) 3
          exact h1.continuousWithinAt
        have hle := le_of_tendsto_of_tendsto hgcont hlin hbnd
        have hlt : (2 * T - t₁) * ρ / 3 < T * ρ := by nlinarith [hTgt, hρ]
        linarith
      have hVT : dist (z T).2 a < 2 * ρ / 3 := by
        refine velEst T hTgt.le ?_
        intro u hu
        rcases eq_or_lt_of_le hu.1 with h | h
        · rw [← h]; nlinarith [hpos, ht₁, hρ]
        · rcases eq_or_lt_of_le hu.2 with h2 | h2
          · rw [h2]; exact hPT
          · exact (huT u h h2).1
      -- hence a whole neighbourhood of `T` is verified, contradicting `T = sSup C`
      obtain ⟨η, hη, hηP⟩ := hopen T hTgt.le ⟨hPT, hVT⟩
      have hs₀C : T + η / 2 ∈ C := by
        intro s hs1 hs2
        by_cases hsT : s ≤ T
        · rcases eq_or_lt_of_le hsT with h | h
          · rw [h]; exact ⟨hPT, hVT⟩
          · exact huT s hs1 h
        · exact hηP s ⟨by linarith [not_le.mp hsT], by linarith [hs2, hη]⟩
      have hle := le_csSup hbd hs₀C
      linarith
    · have hub : ∀ b : ℝ, ∃ s ∈ C, b < s := not_bddAbove_iff.mp hbd
      rcases eq_or_lt_of_le ht with h | h
      · rw [← h]; exact hT₁
      · obtain ⟨s, hsC, hts⟩ := hub t
        exact hsC t h hts
  intro t ht
  exact key t ht

end Submission.NBody

namespace Submission.NBody

/-- **Chazy's lemma, second part, conclusion.**  A solution of the state equation which enters the
invariant tube around the ray `t ↦ t · a` has an asymptotic velocity `b`, with `‖b - a‖ ≤ 2ρ/3`:
the limit shape depends continuously on the initial data. -/
theorem exists_asymptotic_velocity_of_tube (m : Fin N → ℝ) {a : EN E N} {ρ K t₁ : ℝ}
    (hρ : 0 < ρ) (ht₁ : 0 < t₁) (htK : K / t₁ < ρ / 3)
    (hnc : ∀ y : EN E N, dist y a ≤ ρ → WithoutCollisions y)
    (hb : ∀ y : EN E N, dist y a ≤ ρ → ‖weightedGrad m (U m) y‖ ≤ K)
    {z : ℝ → EN E N × EN E N} (hz : ∀ t ∈ Ici t₁, HasDerivAt z (stateField m (z t)) t)
    (hpos : dist (z t₁).1 (t₁ • a) < t₁ * ρ / 3) (hvel : dist (z t₁).2 a < ρ / 3) :
    ∃ b : EN E N, dist b a ≤ 2 * ρ / 3 ∧
      Tendsto (fun t : ℝ => t⁻¹ • (z t).1) atTop (𝓝 b) := by
  have htube := invariant_tube m hρ ht₁ htK hnc hb hz hpos hvel
  -- the normalized configuration stays in the collision-free ball
  have hnorm : ∀ t ∈ Ici t₁, dist (t⁻¹ • (z t).1) a < ρ := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ht₁ ht
    have hsm : t⁻¹ • (t • a) = a := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt ht0), one_smul]
    have h1 : dist (t⁻¹ • (z t).1) (t⁻¹ • (t • a)) = ‖(t⁻¹ : ℝ)‖ * dist (z t).1 (t • a) :=
      dist_smul₀ _ _ _
    rw [hsm] at h1
    rw [h1, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
    have := (htube t ht).1
    calc t⁻¹ * dist (z t).1 (t • a) < t⁻¹ * (t * ρ) := by gcongr
      _ = ρ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ht0), one_mul]
  -- hence the force decays like `t⁻²` for all large `t`
  have hforce : ∀ᶠ t : ℝ in atTop, ‖weightedGrad m (U m) (z t).1‖ ≤ K / t ^ 2 := by
    filter_upwards [eventually_ge_atTop t₁] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le ht₁ ht
    have hw := hnorm t ht
    have hnc' := hnc _ hw.le
    have hb' := hb _ hw.le
    have hzu : (z t).1 = t • (t⁻¹ • (z t).1) := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt ht0), one_smul]
    rw [hzu, weightedGrad_U_smul m ht0 _ hnc', norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t ^ 2)⁻¹)]
    calc (t ^ 2)⁻¹ * ‖weightedGrad m (U m) (t⁻¹ • (z t).1)‖ ≤ (t ^ 2)⁻¹ * K :=
          mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = K / t ^ 2 := by rw [div_eq_inv_mul]
  have hsnd : ∀ t ∈ Ici t₁, HasDerivAt (fun v : ℝ => (z v).2)
      (weightedGrad m (U m) (z t).1) t := by
    intro t ht
    have h := (ContinuousLinearMap.snd ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt t (hz t ht)
    simpa [stateField, Function.comp_def] using h
  have hcont : ContinuousOn (fun t : ℝ => weightedGrad m (U m) (z t).1) (Ici t₁) := by
    have hzcont : ContinuousOn z (Ici t₁) := fun t ht => (hz t ht).continuousAt.continuousWithinAt
    have hmaps : MapsTo z (Ici t₁) {w : EN E N × EN E N | WithoutCollisions w.1} := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le ht₁ ht
      have h1 := hnc _ ((hnorm t ht).le)
      have hzu : (z t).1 = t • (t⁻¹ • (z t).1) := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt ht0), one_smul]
      show WithoutCollisions (z t).1
      rw [hzu]
      exact withoutCollisions_smul h1 (ne_of_gt ht0)
    have hcomp := ((continuous_snd.continuousOn).comp (continuousOn_stateField m)
      (fun w _ => Set.mem_univ (stateField m w))).comp hzcont hmaps
    simpa [stateField, Function.comp_def] using hcomp
  obtain ⟨b, hb_lim⟩ := Commons.Analysis.Asymptotics.exists_tendsto_atTop_of_eventually_norm_le_inv_sq
    ht₁ hsnd hcont hforce
  refine ⟨b, ?_, ?_⟩
  · -- `b` is a limit of velocities which are all within `2ρ/3` of `a`
    have h1 : Tendsto (fun t : ℝ => dist (z t).2 a) atTop (𝓝 (dist b a)) :=
      (hb_lim.dist tendsto_const_nhds)
    have h2 : ∀ᶠ t : ℝ in atTop, dist (z t).2 a ≤ 2 * ρ / 3 :=
      eventually_ge_atTop t₁ |>.mono fun t ht => (htube t ht).2.le
    exact le_of_tendsto_of_tendsto h1 tendsto_const_nhds h2
  · have hfst : ∀ t ∈ Ici t₁, HasDerivAt (fun v : ℝ => (z v).1) ((z t).2) t := by
      intro t ht
      have h := (ContinuousLinearMap.fst ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt t (hz t ht)
      simpa [stateField, Function.comp_def] using h
    have h1 := Commons.Analysis.Calculus.tendsto_smul_inv_sub_of_tendsto_deriv (T := t₁) hfst hb_lim
    have h2 : Tendsto (fun t : ℝ => t⁻¹ • (z t₁).1) atTop (𝓝 (0 : EN E N)) := by
      have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).smul (tendsto_const_nhds (x := (z t₁).1))
      simpa using h
    have h3 := h1.add h2
    simpa [smul_sub, add_sub_cancel] using h3

end Submission.NBody
