/-
# Landing in `Work.Top`'s vocabulary versus `Work.Landing`'s

`Work.EL.LandsN hN θ y` (the ray of angle `θ` lands at `y`) is phrased in `Work.Top`'s
parametrised vocabulary: the ray points `t ↦ rayPt hN θ t` converge to `y` as the level
`t → 1⁺`.  `Work.Landing.landsAt c θ y` is phrased in terms of the accumulation set
`rayAccum c φ θ` of the ray, which is a set of points (the ray `R_c(θ)` is the inverse image
of the radial line `{r e^{2πiθ} : r > 1}` under the Böttcher coordinate).

This file bridges the two: for the concrete Böttcher datum `hN : DynB c φ` of the dynamical
plane and any Böttcher coordinate `φ`,

`Work.EL.LandsN hN θ y ↔ Work.Landing.landsAt c θ y`.

The bridge rests on two observations.

* The truncations agree: for `ρ > 1` the truncated dynamic ray
  `{z ∈ dynRay c φ θ : ‖φ z‖ ≤ ρ}` is exactly the ray piece `rayPiece hN θ 0 ρ`
  (`trunc_eq_rayPiece`), because off the filled Julia set `φ` agrees with `dynPhi c φ`
  and `φ z` lies on the radial line of angle `θ` exactly when `φ z = rayPoint θ t`, `t > 1`.
  Hence `rayAccum c φ θ = {z : ∀ ρ > 1, z ∈ closure (rayPiece hN θ 0 ρ)}`.

* The level interval `(1, ρ]` is a neighbourhood of `1` inside `(1, ∞)`, so `rayPiece hN θ 0 ρ`
  is the image of `(1, ρ]` under `t ↦ rayPt hN θ t` (`rayPiece_eq_image`), and a general
  filter lemma (`tendsto_nhdsWithin_iff_clusterSet`) identifies the convergence `t → 1⁺` with
  the statement that the *closure-intersection* `⋂_{ρ>1} closure (f '' (1, ρ])` is the
  singleton `{y}` — using that the ray points below any bounded level lie in the compact
  sublevel set `{pot ≤ log 2}` of the potential.

Finally `landsAt` is the same as `RayLands c φ θ y` for the *given* coordinate `φ`, by
uniqueness of the Böttcher coordinate (`isDynBottcher_unique`).
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.closure_rayPiece
import Submission.Work.ELTop.rayPiece_eq_image
import Submission.Work.ParamRays.isDynBottcher_unique
import Submission.Work.ParamRays.DynBottcher
import Submission.Work.Landing.Rays.radialRay_norm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

variable {c : ℂ} {φ : ℂ → ℂ}

/-! ## The radial line in terms of the circle points -/

/-- The circle point of angle `θ` and level `t` is `t` times the direction `e^{2πiθ}`. -/
theorem rayPoint_eq_mul_rayDirection (θ t : ℝ) :
    Work.Top.NakaneData.rayPoint θ t = (t : ℂ) * Work.Landing.rayDirection θ := by
  simp only [Work.Top.NakaneData.rayPoint, Work.Landing.rayDirection]
  congr 1
  push_cast
  ring

/-- The radial line of angle `θ` is the range of the circle points at levels `t > 1`. -/
theorem mem_radialRay_iff (θ : ℝ) (w : ℂ) :
    w ∈ Work.Landing.radialRay θ ↔ ∃ t : ℝ, 1 < t ∧ w = Work.Top.NakaneData.rayPoint θ t := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, by rw [rayPoint_eq_mul_rayDirection]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by rw [rayPoint_eq_mul_rayDirection]⟩

/-- A point escapes iff it is not in the filled Julia set. -/
theorem escaping_iff_notMem_K (c z : ℂ) :
    Work.ParamRays.Escaping c z ↔ z ∉ Work.EL.K c := by
  show Work.ParamRays.Escaping c z ↔ z ∈ (Work.ParamRays.filledJulia c)ᶜ
  rw [Work.ParamRays.compl_filledJulia c, Work.ParamRays.mem_escapingSet]

/-! ## The truncated ray is a ray piece -/

/-- The truncation of the dynamic ray `R_c(θ)` at Böttcher modulus `ρ` is the ray piece of
angle `θ` between levels `0` and `R = ρ`. -/
theorem trunc_eq_rayPiece (hN : Work.EL.DynB c φ) {θ ρ : ℝ} (hρ : 0 < ρ) :
    {z : ℂ | z ∈ Work.Landing.dynRay c φ θ ∧ ‖φ z‖ ≤ ρ} = Work.EL.rayPiece hN θ 0 ρ := by
  ext z
  rw [Work.ELTop.mem_rayPiece_iff, Work.Landing.dynRay.eq_1]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hesc, hrad⟩, hle⟩
    obtain ⟨t, ht, ht_eq⟩ := (mem_radialRay_iff θ (φ z)).mp hrad
    have hzK : z ∉ Work.EL.K c := (escaping_iff_notMem_K c z).mp hesc
    have hphi : Work.EL.dynPhi c φ z = Work.Top.NakaneData.rayPoint θ t := by
      rw [Work.EL.dynPhi_of_notMem hzK, ht_eq]
    have hpot : Work.EL.pot hN z = Real.log ‖φ z‖ := by
      rw [Work.EL.pot_of_notMem hN hzK, Work.EL.dynPhi_of_notMem hzK]
    refine ⟨(Work.Top.NakaneData.mem_paramRay_iff hN).mpr ⟨hzK, t, ht, hphi⟩,
      Work.EL.pot_nonneg hN z, ?_⟩
    rw [hpot]
    exact (Real.log_le_log_iff (lt_trans zero_lt_one (Work.Landing.Rays.radialRay_norm hrad))
      hρ).mpr hle
  · rintro ⟨hparam, -, hlog⟩
    obtain ⟨hzK, t, ht, hphi⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hparam
    have ht_eq : φ z = Work.Top.NakaneData.rayPoint θ t := by
      rw [Work.EL.dynPhi_of_notMem (c := c) (φ := φ) hzK] at hphi
      exact hphi
    have hpos : 0 < ‖φ z‖ := by
      rw [ht_eq, Work.Top.NakaneData.norm_rayPoint, abs_of_pos (by linarith)]
      exact lt_trans zero_lt_one ht
    refine ⟨⟨(escaping_iff_notMem_K c z).mpr hzK,
      (mem_radialRay_iff θ (φ z)).mpr ⟨t, ht, ht_eq⟩⟩, ?_⟩
    have hpot : Work.EL.pot hN z = Real.log ‖φ z‖ := by
      rw [Work.EL.pot_of_notMem hN hzK, Work.EL.dynPhi_of_notMem hzK]
    rw [hpot] at hlog
    exact (Real.log_le_log_iff hpos hρ).mp hlog

/-- The accumulation set of the ray of angle `θ` is the intersection over `ρ > 1` of the
closures of the ray pieces of level `ρ`. -/
theorem rayAccum_eq_closure (hN : Work.EL.DynB c φ) (θ : ℝ) :
    Work.Landing.rayAccum c φ θ
      = {z : ℂ | ∀ ρ : ℝ, 1 < ρ → z ∈ closure (Work.EL.rayPiece hN θ 0 ρ)} := by
  ext z
  rw [Work.Landing.rayAccum.eq_1]
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h ρ hρ
    rw [← trunc_eq_rayPiece hN (by linarith : (0:ℝ) < ρ)]
    exact h ρ hρ
  · intro h ρ hρ
    rw [trunc_eq_rayPiece hN (by linarith : (0:ℝ) < ρ)]
    exact h ρ hρ

/-- The accumulation set only depends on the values of the Böttcher coordinate on the escaping
set. -/
theorem rayAccum_congr {c : ℂ} {φ ψ : ℂ → ℂ}
    (h : ∀ w : ℂ, Work.ParamRays.Escaping c w → φ w = ψ w) (θ : ℝ) :
    Work.Landing.rayAccum c φ θ = Work.Landing.rayAccum c ψ θ := by
  have htrunc : ∀ ρ : ℝ, {z : ℂ | z ∈ Work.Landing.dynRay c φ θ ∧ ‖φ z‖ ≤ ρ}
      = {z : ℂ | z ∈ Work.Landing.dynRay c ψ θ ∧ ‖ψ z‖ ≤ ρ} := by
    intro ρ
    ext z
    rw [Work.Landing.dynRay.eq_1, Work.Landing.dynRay.eq_1]
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hesc, hrad⟩, hle⟩
      rw [h z hesc] at hrad hle
      exact ⟨⟨hesc, hrad⟩, hle⟩
    · rintro ⟨⟨hesc, hrad⟩, hle⟩
      rw [← h z hesc] at hrad hle
      exact ⟨⟨hesc, hrad⟩, hle⟩
  ext w
  rw [Work.Landing.rayAccum.eq_1, Work.Landing.rayAccum.eq_1]
  simp only [Set.mem_ofPred_eq]
  refine forall_congr' (fun ρ => imp_congr_right (fun _ => ?_))
  rw [htrunc ρ]

/-! ## A filter lemma: convergence is a unique cluster point -/

/-- **Convergence versus unique cluster point.**  For a map `f : ℝ → ℂ` whose values below a
bounded level stay in a compact set, the convergence `f t → y` as `t → 1⁺` is equivalent to the
statement that the closure-intersection `⋂_{ρ>1} closure (f '' (1, ρ])` is the singleton `{y}`.

(The hypothesis is only used in the direction “unique cluster point ⟹ convergence”: a failing
convergence gives a sequence of levels `→ 1⁺` whose values stay outside a neighbourhood of `y`,
and compactness extracts a limit point, which is a cluster point distinct from `y`.) -/
theorem tendsto_nhdsWithin_iff_clusterSet {f : ℝ → ℂ} {y : ℂ}
    (hK : ∃ K : Set ℂ, IsCompact K ∧ ∀ᶠ t in 𝓝[Set.Ioi (1:ℝ)] 1, f t ∈ K) :
    Filter.Tendsto f (𝓝[Set.Ioi (1:ℝ)] 1) (𝓝 y) ↔
      {z : ℂ | ∀ ρ : ℝ, 1 < ρ → z ∈ closure (f '' Set.Ioc 1 ρ)} = {y} := by
  have hIoc : ∀ ⦃ρ : ℝ⦄, 1 < ρ → Set.Ioc (1:ℝ) ρ ∈ 𝓝[Set.Ioi (1:ℝ)] 1 := by
    intro ρ hρ
    have hsub : Set.Ioo (1:ℝ) ρ ⊆ Set.Ioc (1:ℝ) ρ := fun t ht => ⟨ht.1, le_of_lt ht.2⟩
    have hmem : Set.Ioo (1:ℝ) ρ ∈ 𝓝[Set.Ioi (1:ℝ)] 1 :=
      Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hρ))
    exact Filter.mem_of_superset hmem hsub
  constructor
  · intro hf
    ext z
    constructor
    · intro hz
      have hseq : ∀ n : ℕ, ∃ t : ℝ,
          t ∈ Set.Ioc (1:ℝ) (1 + 1/((n:ℝ)+1)) ∧ dist z (f t) < 1/((n:ℝ)+1) := by
        intro n
        have hρ : (1:ℝ) < 1 + 1/((n:ℝ)+1) := by
          have : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
          linarith
        have hmem : z ∈ closure (f '' Set.Ioc (1:ℝ) (1 + 1/((n:ℝ)+1))) := hz _ hρ
        rw [Metric.mem_closure_iff] at hmem
        obtain ⟨w, hw, hwd⟩ := hmem (1/((n:ℝ)+1)) (by positivity)
        obtain ⟨t, ht, rfl⟩ := hw
        exact ⟨t, ht, hwd⟩
      let t : ℕ → ℝ := fun n => Classical.choose (hseq n)
      have ht1 : ∀ n, (1:ℝ) < t n := fun n => (Classical.choose_spec (hseq n)).1.1
      have ht2 : ∀ n, t n ≤ 1 + 1/((n:ℝ)+1) := fun n => (Classical.choose_spec (hseq n)).1.2
      have hd : ∀ n, dist (f (t n)) z < 1/((n:ℝ)+1) := fun n => by
        rw [dist_comm]; exact (Classical.choose_spec (hseq n)).2
      have htend : Tendsto t atTop (𝓝 (1:ℝ)) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
          (fun n => le_of_lt (ht1 n)) ht2
        simpa using tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have htend' : Tendsto t atTop (𝓝[Set.Ioi (1:ℝ)] 1) :=
        tendsto_nhdsWithin_iff.mpr ⟨htend, Filter.Eventually.of_forall (fun n => ht1 n)⟩
      have hfy : Tendsto (fun n => f (t n)) atTop (𝓝 y) := hf.comp htend'
      have hfz : Tendsto (fun n => f (t n)) atTop (𝓝 z) := by
        rw [tendsto_iff_dist_tendsto_zero]
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
          (fun n => dist_nonneg) (fun n => le_of_lt (hd n))
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      exact Set.mem_singleton_iff.mpr (tendsto_nhds_unique hfz hfy)
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      intro ρ hρ
      refine mem_closure_of_tendsto hf ?_
      exact Filter.mem_of_superset (hIoc hρ) (fun t ht => ⟨t, ht, rfl⟩)
  · intro hCl
    obtain ⟨K, hKc, hKf⟩ := hK
    refine hKc.tendsto_nhds_of_unique_mapClusterPt hKf ?_
    intro x _ hx
    have hxCl : x ∈ {z : ℂ | ∀ ρ : ℝ, 1 < ρ → z ∈ closure (f '' Set.Ioc 1 ρ)} := by
      intro ρ hρ
      exact hx.clusterPt.mem_closure_of_mem _
        (Filter.mem_map.mpr (Filter.mem_of_superset (hIoc hρ) (fun t ht => ⟨t, ht, rfl⟩)))
    rw [hCl] at hxCl
    exact Set.mem_singleton_iff.mp hxCl

/-! ## The bridge -/

theorem landsN_iff_landsAt {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (θ : ℝ) (y : ℂ) :
    Work.EL.LandsN hN θ y ↔ Work.Landing.landsAt c θ y := by
  -- the ray points below level `2` lie in the compact set `{pot ≤ log 2}`
  have hK : ∃ K : Set ℂ, IsCompact K ∧
      ∀ᶠ t in 𝓝[Set.Ioi (1:ℝ)] 1, Work.EL.rayPt hN θ t ∈ K := by
    refine ⟨{z : ℂ | Work.EL.pot hN z ≤ Real.log 2}, Work.EL.isCompact_le_pot hN _, ?_⟩
    have hIoc : Set.Ioc (1:ℝ) 2 ∈ 𝓝[Set.Ioi (1:ℝ)] 1 := by
      have hsub : Set.Ioo (1:ℝ) 2 ⊆ Set.Ioc (1:ℝ) 2 := fun t ht => ⟨ht.1, le_of_lt ht.2⟩
      have hmem : Set.Ioo (1:ℝ) 2 ∈ 𝓝[Set.Ioi (1:ℝ)] 1 :=
        Filter.inter_mem self_mem_nhdsWithin
          (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (by norm_num : (1:ℝ) < 2)))
      exact Filter.mem_of_superset hmem hsub
    refine Filter.mem_of_superset hIoc (fun t ht => ?_)
    simp only [Set.mem_ofPred_eq]
    rw [Work.EL.pot_rayPt hN ht.1]
    exact Real.log_le_log (by linarith [ht.1]) ht.2
  have hkey := tendsto_nhdsWithin_iff_clusterSet (f := fun t => Work.EL.rayPt hN θ t) (y := y) hK
  have hCl : Work.Landing.rayAccum c φ θ
      = {z : ℂ | ∀ ρ : ℝ, 1 < ρ → z ∈ closure ((fun t => Work.EL.rayPt hN θ t) '' Set.Ioc 1 ρ)} := by
    rw [rayAccum_eq_closure hN θ]
    congr 1
    ext z
    constructor
    · intro h ρ hρ
      rw [← rayPiece_eq_image hN hρ]
      exact h ρ hρ
    · intro h ρ hρ
      rw [rayPiece_eq_image hN hρ]
      exact h ρ hρ
  change Filter.Tendsto (fun t => Work.EL.rayPt hN θ t) (𝓝[Set.Ioi (1:ℝ)] 1) (𝓝 y) ↔
    Work.Landing.landsAt c θ y
  rw [hkey]
  constructor
  · intro hy
    exact ⟨φ, hφ, hCl.trans hy⟩
  · rintro ⟨ψ, hψ, hψy⟩
    exact hCl.symm.trans
      ((rayAccum_congr (fun w hw => Work.ParamRays.isDynBottcher_unique hφ hψ hw) θ).trans hψy)

end Work.ELTop
