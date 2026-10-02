/-
# Preimages of a landing ray under `Tantibar c`

If the external ray of angle `T θ = -2θ mod 1` (dynamical Böttcher/Nakane vocabulary `LandsN`)
lands at `y ≠ c`, then the ray of angle `θ` lands at one of the two preimages of `y` under
`Tantibar c` (the antiholomorphic quadratic map `z ↦ conj z ^ 2 + c`).

The content is the converse of `landsN_image`.  Since `Tantibar c z = conj z ^ 2 + c` has the
single critical point `0` with critical value `c`, for a regular value `y ≠ c` the deviation from
`y` factors as

  `Tantibar c z - y = conj ((z - u) (z + u))`,   `‖Tantibar c z - y‖ = ‖z - u‖ ‖z + u‖`,

where `±u` are the two preimages of `y`.  Near level `1` the point `rayPt θ t` is therefore
eventually confined to the union of the two *disjoint* open discs about `u` and `-u`; as the ray
parametrisation `t ↦ rayPt θ t` is continuous and the level interval is connected, the image lies
in a *single* one of them, so the family is Cauchy and converges.  Its limit `w` satisfies
`Tantibar c w = y` by continuity, and `LandsN hN θ w` is the definition of the convergence.
-/
import Mathlib
import Submission.Work.ELPull.Defs
import Submission.Work.ELPull.landsN_image
import Submission.Work.ELPull.preimage_localization
import Submission.Work.Top.continuousOn_rayPt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELPull

open Classical Set Function Filter
open scoped Topology

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The quadratic factorisation at a regular value of `Tantibar c` -/

/-- `Tantibar c` at the conjugate of `w` is the square `w * w + c`. -/
theorem tantibar_conj_sq (c w : ℂ) : Tantibar c (starRingEnd ℂ w) = w * w + c := by
  simp only [Tantibar, starRingEnd_apply]
  rw [star_star]; ring

/-- The deviation of `Tantibar c z` from the value `Tantibar c (conj w)` is the conjugate of the
product of the differences to the two preimages `conj w` and `-conj w`. -/
theorem tantibar_sub (c w z : ℂ) :
    Tantibar c z - Tantibar c (starRingEnd ℂ w)
      = starRingEnd ℂ ((z - starRingEnd ℂ w) * (z + starRingEnd ℂ w)) := by
  rw [tantibar_conj_sq]
  simp only [Tantibar, map_mul, map_sub, map_add, starRingEnd_apply]
  rw [star_star]
  ring

/-- The norm of the deviation is the product of the distances to the two preimages. -/
theorem norm_tantibar_sub (c w z : ℂ) :
    ‖Tantibar c z - Tantibar c (starRingEnd ℂ w)‖
      = ‖z - starRingEnd ℂ w‖ * ‖z + starRingEnd ℂ w‖ := by
  rw [tantibar_sub, Complex.norm_conj, norm_mul]

/-! ## The main statement -/

theorem landsN_preimage {c : ℂ} (hN : DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    {θ : ℝ} {y : ℂ} (hy : y ≠ c) (h : LandsN hN (T θ) y) :
    ∃ w : ℂ, LeanEval.ComplexAnalysis.Tantibar c w = y ∧ LandsN hN θ w := by
  -- a square root of `y - c`; the two preimages of `y` are `u = conj w₀` and `-u`
  obtain ⟨w₀, hw₀⟩ := IsAlgClosed.exists_eq_mul_self (y - c)
  have hyw : w₀ * w₀ + c = y := by rw [← hw₀]; ring
  set u : ℂ := starRingEnd ℂ w₀ with hu
  have hTantu : Tantibar c u = y := by rw [hu, tantibar_conj_sq, hyw]
  have hu_ne : u ≠ 0 := by
    intro h0
    have : y = c := by
      rw [← hTantu, h0]
      simp only [Tantibar, map_zero]
      ring
    exact hy this
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  -- the norm identity and the resulting localization at `y`
  have hnorm : ∀ z : ℂ, ‖Tantibar c z - y‖ = ‖z - u‖ * ‖z + u‖ := by
    intro z
    rw [← hTantu, hu, norm_tantibar_sub]
  have hloc : ∀ ε' : ℝ, 0 < ε' → ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ z : ℂ,
      ‖Tantibar c z - y‖ < δ₂ → z ∈ Metric.ball u ε' ∪ Metric.ball (-u) ε' := by
    intro ε' hε'
    refine ⟨ε' ^ 2, pow_pos hε' 2, fun z hz => ?_⟩
    by_contra hcon
    have hcon1 : z ∉ Metric.ball u ε' := fun hh => hcon (Or.inl hh)
    have hcon2 : z ∉ Metric.ball (-u) ε' := fun hh => hcon (Or.inr hh)
    have h1 : ε' ≤ ‖z - u‖ := by
      have hh := hcon1
      rwa [Metric.mem_ball, not_lt, dist_eq_norm] at hh
    have h2 : ε' ≤ ‖z + u‖ := by
      have hh := hcon2
      rw [Metric.mem_ball, not_lt, dist_eq_norm, sub_neg_eq_add] at hh
      exact hh
    have hle : ε' ^ 2 ≤ ‖z - u‖ * ‖z + u‖ := by
      have h := mul_le_mul h1 h2 (le_of_lt hε') (norm_nonneg (z - u))
      nlinarith [h]
    rw [hnorm z] at hz
    linarith
  -- the ray parametrisation
  let g : ℝ → ℂ := fun t => hN.rayPt θ t
  have hg_cont : ContinuousOn g (Set.Ioi (1:ℝ)) := Work.Top.continuousOn_rayPt hN θ
  -- `Tantibar c ∘ g` converges to `y`
  have hsq : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] (1:ℝ)) (𝓝[>] (1:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using ((continuous_pow 2).continuousAt (x := (1:ℝ))).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (1:ℝ) < t := ht
      show (1:ℝ) < t ^ 2
      nlinarith [ht']
  have hcomp : Tendsto (fun t : ℝ => hN.rayPt (T θ) (t ^ 2)) (𝓝[>] (1:ℝ)) (𝓝 y) :=
    h.comp hsq
  have hfg : Tendsto (fun t : ℝ => Tantibar c (g t)) (𝓝[>] (1:ℝ)) (𝓝 y) := by
    refine hcomp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact rayPt_Tantibar hN hφ ht
  -- the family `g` is Cauchy at level `1`
  have hcauchy : Cauchy (map g (𝓝[>] (1:ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨by infer_instance, fun ε hε => ?_⟩
    let ε' : ℝ := min (ε / 4) (‖u‖ / 2)
    have hε'pos : 0 < ε' := lt_min (by linarith) (by linarith)
    have hε'le : 2 * ε' ≤ ε := by
      have hm := min_le_left (ε / 4) (‖u‖ / 2); linarith
    have hε'lt : 2 * ε' < 2 * ‖u‖ := by
      have hm := min_le_right (ε / 4) (‖u‖ / 2); linarith
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hloc ε' hε'pos
    have hev : ∀ᶠ t in 𝓝[>] (1:ℝ), g t ∈ Metric.ball u ε' ∪ Metric.ball (-u) ε' := by
      filter_upwards [hfg.eventually (Metric.ball_mem_nhds y hδ₂pos)] with t ht
      exact hδ₂ (g t) (by rwa [dist_eq_norm] at ht)
    obtain ⟨t₀, ht₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
    refine ⟨g '' Set.Ioo (1:ℝ) t₀, ?_, ?_⟩
    · rw [Filter.mem_map]
      refine mem_of_superset ?_ (fun x hx => ⟨x, hx, rfl⟩)
      exact mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨t₀, ht₀, subset_rfl⟩
    · rintro x ⟨s, hs, rfl⟩ z ⟨t, ht, rfl⟩
      have hpre : IsPreconnected (g '' Set.Ioo (1:ℝ) t₀) :=
        isPreconnected_Ioo.image g (hg_cont.mono Set.Ioo_subset_Ioi_self)
      have hsub2 : g '' Set.Ioo (1:ℝ) t₀ ⊆ Metric.ball u ε' ∪ Metric.ball (-u) ε' :=
        fun w ⟨a, ha, hw⟩ => hw ▸ hsub ha
      have hdisj : Disjoint (Metric.ball u ε') (Metric.ball (-u) ε') := by
        rw [disjoint_left]
        intro z hz1 hz2
        rw [Metric.mem_ball, dist_eq_norm] at hz1 hz2
        have h1 : dist u z < ε' := by rw [dist_comm, dist_eq_norm]; exact hz1
        have h2 : dist z (-u) < ε' := by rw [dist_eq_norm]; exact hz2
        have htri : dist u (-u) ≤ dist u z + dist z (-u) := dist_triangle u z (-u)
        have hd : dist u (-u) = 2 * ‖u‖ := by
          rw [dist_eq_norm, show u - -u = (2:ℂ) * u by ring, norm_mul]; norm_num
        rw [hd] at htri
        linarith
      rcases hpre.subset_or_subset Metric.isOpen_ball Metric.isOpen_ball hdisj hsub2 with
        hcase | hcase
      · have h1 : dist (g s) u < ε' := by
          have hh := hcase ⟨s, hs, rfl⟩; rwa [Metric.mem_ball] at hh
        have h2 : dist (g t) u < ε' := by
          have hh := hcase ⟨t, ht, rfl⟩; rwa [Metric.mem_ball] at hh
        have htri := dist_triangle (g s) u (g t)
        rw [dist_comm u (g t)] at htri
        linarith
      · have h1 : dist (g s) (-u) < ε' := by
          have hh := hcase ⟨s, hs, rfl⟩; rwa [Metric.mem_ball] at hh
        have h2 : dist (g t) (-u) < ε' := by
          have hh := hcase ⟨t, ht, rfl⟩; rwa [Metric.mem_ball] at hh
        have htri := dist_triangle (g s) (-u) (g t)
        rw [dist_comm (-u) (g t)] at htri
        linarith
  obtain ⟨w, hw⟩ := CompleteSpace.complete hcauchy
  have hcont : Continuous (Tantibar c) := by
    change Continuous (fun z : ℂ => (starRingEnd ℂ z) ^ 2 + c)
    exact (Complex.continuous_conj.pow 2).add_const c
  have hfw : Tendsto (fun t : ℝ => Tantibar c (g t)) (𝓝[>] (1:ℝ))
      (𝓝 (Tantibar c w)) := hcont.continuousAt.tendsto.comp hw
  have hTy : Tantibar c w = y := tendsto_nhds_unique hfw hfg
  exact ⟨w, hTy, hw⟩

end Work.ELPull
