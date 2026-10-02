import Mathlib
import Submission.Work.ThomBordism.TwoSet.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Piece (5) of the `SphereExtension` architecture: the coning

If a homotopy `H` takes a map `Φ : ∂I^m → Y` to a constant, then `Φ` extends over `I^m`: the
homotopy, read along the rays of the cone `I^m = C(∂I^m)`, *is* the extension.  This is the step
that converts "null-homotopic" into "extends", and it needs no hypotheses beyond `m ≥ 1`.

See `SPHEREEXT_NOTES.md` §3, piece (5).
-/

namespace Work.ThomBordism.TwoSet

open scoped Topology unitInterval

variable {m : ℕ}

/-- `Fin m` is nonempty when `1 ≤ m`. -/
theorem finset_univ_nonempty {m : ℕ} (hm : 1 ≤ m) :
    (Finset.univ : Finset (Fin m)).Nonempty :=
  ⟨⟨0, hm⟩, Finset.mem_univ _⟩

/-- The `ℓ∞` "radius" of a point of the cube: `max_i |2 p_i - 1|`, so `0` at the centre and `1`
exactly on the boundary. -/
noncomputable def rad (hm : 1 ≤ m) (p : Fin m → unitInterval) : ℝ :=
  (Finset.univ : Finset (Fin m)).sup' (finset_univ_nonempty hm)
    (fun i => |2 * (p i : ℝ) - 1|)

/-- `rad` is continuous: a finite `max` of continuous functions. -/
theorem continuous_rad (hm : 1 ≤ m) : Continuous (rad hm) :=
  Continuous.finset_sup'_apply (s := Finset.univ) (finset_univ_nonempty hm) fun i _ =>
    ((continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))).sub
      continuous_const).abs

theorem rad_nonneg (hm : 1 ≤ m) (p : Fin m → unitInterval) : 0 ≤ rad hm p := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) (finset_univ_nonempty hm)
    (fun i => |2 * (p i : ℝ) - 1|)
  rw [rad, hi]; positivity

theorem rad_le_one (hm : 1 ≤ m) (p : Fin m → unitInterval) : rad hm p ≤ 1 := by
  rw [rad]
  refine Finset.sup'_le _ (fun i => |2 * (p i : ℝ) - 1|) fun i _ => ?_
  have h0 : (0:ℝ) ≤ (p i : ℝ) := (p i).2.1
  have h1 : (p i : ℝ) ≤ 1 := (p i).2.2
  rw [abs_le]; constructor <;> linarith

theorem rad_le (hm : 1 ≤ m) (p : Fin m → unitInterval) (i : Fin m) :
    |2 * (p i : ℝ) - 1| ≤ rad hm p := by
  rw [rad]
  exact (Finset.le_sup'_iff (finset_univ_nonempty hm)).mpr ⟨i, Finset.mem_univ i, le_rfl⟩

theorem rad_boundary_eq_one (hm : 1 ≤ m) {x : Fin m → unitInterval}
    (hx : x ∈ Cube.boundary (Fin m)) : rad hm x = 1 := by
  obtain ⟨i, hi⟩ := hx
  have h2 : |2 * (x i : ℝ) - 1| = 1 := by
    rcases hi with h | h <;> rw [h] <;> norm_num
  refine le_antisymm (rad_le_one hm x) ?_
  calc (1:ℝ) = |2 * (x i : ℝ) - 1| := h2.symm
    _ ≤ rad hm x := rad_le hm x i

/-- The real formula underlying `bpt`. -/
noncomputable def bptR (hm : 1 ≤ m) (p : Fin m → unitInterval) (i : Fin m) : ℝ :=
  1/2 + ((p i : ℝ) - 1/2) / rad hm p

/-- The value of the radial projection stays in the unit interval. -/
theorem bptR_mem (hm : 1 ≤ m) (p : Fin m → unitInterval) (i : Fin m) :
    bptR hm p i ∈ Set.Icc (0:ℝ) 1 := by
  have hr := rad_nonneg hm p
  have hb := rad_le hm p i
  constructor
  · by_cases hr0 : rad hm p = 0
    · simp only [bptR, hr0, div_zero, add_zero]; norm_num
    · have hrp : 0 < rad hm p := lt_of_le_of_ne hr (Ne.symm hr0)
      have h1 : -(1/2) ≤ ((p i : ℝ) - 1/2) / rad hm p := by
        rw [le_div_iff₀ hrp]
        nlinarith [abs_le.mp hb]
      simp only [bptR]; linarith
  · by_cases hr0 : rad hm p = 0
    · simp only [bptR, hr0, div_zero, add_zero]; norm_num
    · have hrp : 0 < rad hm p := lt_of_le_of_ne hr (Ne.symm hr0)
      have h1 : ((p i : ℝ) - 1/2) / rad hm p ≤ 1/2 := by
        rw [div_le_iff₀ hrp]
        nlinarith [abs_le.mp hb]
      simp only [bptR]; linarith

/-- The boundary point on the ray from the centre through `p` (meaningful when `rad > 0`). -/
noncomputable def bpt (hm : 1 ≤ m) (p : Fin m → unitInterval) : Fin m → unitInterval :=
  fun i => ⟨bptR hm p i, bptR_mem hm p i⟩

theorem bpt_coe (hm : 1 ≤ m) (p : Fin m → unitInterval) (i : Fin m) :
    ((bpt hm p) i : ℝ) = bptR hm p i := rfl

theorem bpt_eq_self_of_mem_boundary (hm : 1 ≤ m) {x : Fin m → unitInterval}
    (hx : x ∈ Cube.boundary (Fin m)) : bpt hm x = x := by
  funext i
  apply Subtype.ext
  simp only [bpt_coe, bptR, rad_boundary_eq_one hm hx, div_one]
  ring

/-- The boundary point really is on the boundary, when the radius is nonzero. -/
theorem bpt_mem_boundary (hm : 1 ≤ m) (p : Fin m → unitInterval) (hp : rad hm p ≠ 0) :
    bpt hm p ∈ Cube.boundary (Fin m) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) (finset_univ_nonempty hm)
    (fun i => |2 * (p i : ℝ) - 1|)
  refine ⟨i, ?_⟩
  have hri : rad hm p = |2 * (p i : ℝ) - 1| := hi
  have hne : 2 * (p i : ℝ) - 1 ≠ 0 := by intro h; exact hp (by rw [hri, h]; norm_num)
  have hval : 2 * ((bpt hm p) i : ℝ) - 1 = (2 * (p i : ℝ) - 1) / rad hm p := by
    rw [bpt_coe, bptR]; field_simp; ring
  have h2 : |2 * ((bpt hm p) i : ℝ) - 1| = 1 := by
    rw [hval, abs_div, hri, abs_of_pos (abs_pos.mpr hne), div_self (abs_ne_zero.mpr hne)]
  have hgoal : ((bpt hm p) i : ℝ) = 0 ∨ ((bpt hm p) i : ℝ) = 1 := by
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h2 with h | h
    · right; linarith
    · left; linarith
  rcases hgoal with h | h
  · left; exact Subtype.ext h
  · right; exact Subtype.ext h

/-- The boundary computation: along `∂I^m` the cone formula returns `H (x, 0)`. -/
theorem bpt_cone_boundary {Y : Type*} [TopologicalSpace Y] {m : ℕ} (hm : 1 ≤ m)
    (H : C({x : (Fin m → unitInterval) // x ∈ Cube.boundary (Fin m)} × unitInterval, Y))
    (x : {x : (Fin m → unitInterval) // x ∈ Cube.boundary (Fin m)}) :
    H (⟨bpt hm x.1, bpt_mem_boundary hm x.1 (by rw [rad_boundary_eq_one hm x.2]; norm_num)⟩,
       ⟨1 - rad hm x.1, by rw [rad_boundary_eq_one hm x.2]; norm_num⟩) = H (x, 0) := by
  have h1 : bpt hm x.1 = x.1 := bpt_eq_self_of_mem_boundary hm x.2
  have h2 : rad hm x.1 = 1 := rad_boundary_eq_one hm x.2
  have hb : bpt hm x.1 ∈ Cube.boundary (Fin m) := by rw [h1]; exact x.2
  have hs : (1 - rad hm x.1 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by rw [h2]; norm_num
  rw [show (⟨bpt hm x.1, hb⟩ : {x // x ∈ Cube.boundary (Fin m)}) = x from Subtype.ext h1]
  have h3 : (⟨1 - rad hm x.1, hs⟩ : unitInterval) = 0 := by
    apply Subtype.ext
    show (1 - rad hm x.1 : ℝ) = ((0 : unitInterval) : ℝ)
    rw [h2]; norm_num
  rw [h3]

/-- **Uniform convergence.**  Along `∂I^m`, the homotopy `H (·, s)` enters every neighbourhood of
`y₀` uniformly as `s → 1`.  (`Y` is an arbitrary topological space, so this is necessarily stated
with neighbourhoods rather than with a metric.) -/
theorem uniform_conv {Y : Type*} [TopologicalSpace Y] {m : ℕ} (hm : 1 ≤ m) {y₀ : Y}
    (H : C({x : (Fin m → unitInterval) // x ∈ Cube.boundary (Fin m)} × unitInterval, Y))
    (hH : ∀ x, H (x, 1) = y₀) :
    ∀ V : Set Y, V ∈ 𝓝 y₀ → ∃ s₀ : ℝ, s₀ < 1 ∧
      ∀ (x : {x : (Fin m → unitInterval) // x ∈ Cube.boundary (Fin m)}) (s : unitInterval),
        s₀ < (s : ℝ) → H (x, s) ∈ V := by
  intro V hV
  have hVi : y₀ ∈ interior V := mem_interior_iff_mem_nhds.mpr hV
  have hVsub : interior V ⊆ V := interior_subset
  haveI : CompactSpace {x : Fin m → unitInterval // x ∈ Cube.boundary (Fin m)} :=
    isCompact_iff_compactSpace.mp
      ((isCompact_univ : IsCompact (Set.univ : Set (Fin m → unitInterval))).of_isClosed_subset
        (isClosed_cubeBoundary m) (Set.subset_univ _))
  let T : Set unitInterval :=
    Prod.snd '' {q : ({x : Fin m → unitInterval // x ∈ Cube.boundary (Fin m)}) × unitInterval |
      H q ∉ interior V}
  have hclosed : IsClosed {q : ({x : Fin m → unitInterval // x ∈ Cube.boundary (Fin m)}) ×
      unitInterval | H q ∉ interior V} :=
    isClosed_compl_iff.mpr (isOpen_interior.preimage H.continuous)
  have hcomp : IsCompact T :=
    ((isCompact_univ.of_isClosed_subset hclosed (Set.subset_univ _)).image continuous_snd)
  have h1T : (1 : unitInterval) ∉ T := by
    rintro ⟨q, hq, hq1⟩
    have hqy : H q = y₀ := by
      rw [show q = (q.1, q.2) from rfl, hq1]; exact hH q.1
    exact hq (by rw [hqy]; exact hVi)
  by_cases hne : T.Nonempty
  · obtain ⟨s₀, hs₀T, hs₀max⟩ := hcomp.exists_isMaxOn hne continuousOn_id
    refine ⟨(s₀ : ℝ), ?_, ?_⟩
    · have hle : (s₀ : ℝ) ≤ 1 := s₀.2.2
      refine lt_of_le_of_ne hle fun h => ?_
      obtain ⟨q, hq, hq2⟩ := hs₀T
      exact h1T ⟨q, hq, by rw [hq2]; exact Subtype.ext h⟩
    · intro x s hs
      by_contra hcon
      have hsT : s ∈ T := ⟨(x, s), fun hc => hcon (hVsub hc), rfl⟩
      have : (s : ℝ) ≤ (s₀ : ℝ) := hs₀max hsT
      linarith
  · refine ⟨0, by norm_num, ?_⟩
    intro x s _
    by_contra hcon
    exact hne ⟨s, (x, s), fun hc => hcon (hVsub hc), rfl⟩

/-- `bptR` is continuous in the point, wherever `rad ≠ 0`. -/
theorem bptR_continuous (hm : 1 ≤ m) (i : Fin m) :
    Continuous fun q : {p : Fin m → unitInterval // rad hm p ≠ 0} => bptR hm q.1 i := by
  have hnum : Continuous fun q : {p : Fin m → unitInterval // rad hm p ≠ 0} =>
      ((q.1 i : ℝ) - 1/2) := by
    have h1 : Continuous fun q : {p : Fin m → unitInterval // rad hm p ≠ 0} =>
        ((q.1 i : unitInterval) : ℝ) :=
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)
    exact h1.sub continuous_const
  have hden : Continuous fun q : {p : Fin m → unitInterval // rad hm p ≠ 0} => rad hm q.1 :=
    (continuous_rad hm).comp continuous_subtype_val
  exact continuous_const.add (hnum.div hden (fun q => q.2))

/-- `bpt` is continuous wherever `rad ≠ 0`. -/
theorem continuous_bpt (hm : 1 ≤ m) :
    Continuous (fun q : {p : Fin m → unitInterval // rad hm p ≠ 0} => bpt hm q.1) := by
  refine continuous_pi (fun i => ?_)
  have hfun : (fun q : {p : Fin m → unitInterval // rad hm p ≠ 0} => bpt hm q.1 i)
      = fun q => (⟨bptR hm q.1 i, bptR_mem hm q.1 i⟩ : unitInterval) := rfl
  rw [hfun]
  exact Continuous.subtype_mk (bptR_continuous hm i) (fun q => bptR_mem hm q.1 i)

/-- The point `p` with `rad p = 0` is the centre of the cube. -/
theorem eq_cen_of_rad_eq_zero (hm : 1 ≤ m) {p : Fin m → unitInterval} (hp : rad hm p = 0) :
    p = fun _ => (⟨1/2, by norm_num⟩ : unitInterval) := by
  funext i
  have h := rad_le hm p i
  rw [hp] at h
  have h' : |2 * (p i : ℝ) - 1| = 0 := le_antisymm h (abs_nonneg _)
  have h2 : 2 * (p i : ℝ) - 1 = 0 := abs_eq_zero.mp h'
  apply Subtype.ext
  show ((p i : unitInterval) : ℝ) = 1/2
  linarith

/-- **Piece (5): the coning.**  A homotopy of `Φ : ∂I^m → Y` to a constant extends `Φ` over the
cube `I^m`.

The extension is the cone formula: `Ψ p` is `y₀` at the centre and `H (bpt p, 1 - rad p)` otherwise,
where `bpt p` is the boundary point on the ray from the centre through `p` and `rad p` is the
`ℓ∞`-radius.  Continuity away from the centre is immediate (`bpt` and `rad` are continuous there);
at the centre it follows from the uniform convergence of `H (·, s)` to `y₀` as `s → 1`. -/
theorem ConeDescent {Y : Type*} [TopologicalSpace Y] {m : ℕ} (hm : 1 ≤ m) {y₀ : Y}
    (H : C({x : (Fin m → unitInterval) // x ∈ Cube.boundary (Fin m)} × unitInterval, Y))
    (hH : ∀ x, H (x, 1) = y₀) :
    ∃ Ψ : C(Fin m → unitInterval, Y), ∀ x, Ψ x.1 = H (x, 0) := by
  classical
  have hmem : ∀ p : Fin m → unitInterval, rad hm p ≠ 0 →
      (1 - rad hm p : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
    intro p hp
    have h0 := rad_nonneg hm p
    have h1 := rad_le_one hm p
    exact ⟨by linarith, by linarith⟩
  let cen : Fin m → unitInterval := fun _ => ⟨1/2, by norm_num⟩
  have hrad_cen : rad hm cen = 0 := by
    have h1 : ∀ i : Fin m, |2 * ((cen i : unitInterval) : ℝ) - 1| = 0 := by
      intro i; simp only [cen]; norm_num
    rw [rad]
    refine le_antisymm ?_ (rad_nonneg hm cen)
    refine Finset.sup'_le (finset_univ_nonempty hm) _ fun i _ => ?_
    rw [h1 i]
  let Ψfun : (Fin m → unitInterval) → Y := fun p =>
    if h : rad hm p = 0 then y₀
    else H (⟨bpt hm p, bpt_mem_boundary hm p h⟩, ⟨1 - rad hm p, hmem p h⟩)
  have hopen : IsOpen {p : Fin m → unitInterval | rad hm p ≠ 0} :=
    (isOpen_ne (x := (0:ℝ))).preimage (continuous_rad hm)
  let gamma : {p : Fin m → unitInterval // rad hm p ≠ 0} →
      ({x : Fin m → unitInterval // x ∈ Cube.boundary (Fin m)} × unitInterval) :=
    fun q => (⟨bpt hm q.1, bpt_mem_boundary hm q.1 q.2⟩, ⟨1 - rad hm q.1, hmem q.1 q.2⟩)
  have hgamma : Continuous gamma := by
    refine Continuous.prodMk ?_ ?_
    · refine continuous_induced_rng.mpr ?_
      show Continuous fun q : {p : Fin m → unitInterval // rad hm p ≠ 0} => bpt hm q.1
      exact continuous_bpt hm
    · refine continuous_induced_rng.mpr ?_
      show Continuous fun q : {p : Fin m → unitInterval // rad hm p ≠ 0} =>
        (1 - rad hm q.1 : ℝ)
      exact continuous_const.sub ((continuous_rad hm).comp continuous_subtype_val)
  have hcontOn : ContinuousOn Ψfun {p : Fin m → unitInterval | rad hm p ≠ 0} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h2 : ∀ q : {p : Fin m → unitInterval // rad hm p ≠ 0}, Ψfun q.1 = H (gamma q) := by
      intro q
      simp only [Ψfun, dif_neg q.2]
      rfl
    exact (H.continuous.comp hgamma).congr (fun q => (h2 q).symm)
  have hcont_off : ∀ p, rad hm p ≠ 0 → ContinuousAt Ψfun p := fun p hp =>
    hcontOn.continuousAt (hopen.mem_nhds hp)
  have hcen0 : Ψfun cen = y₀ := by
    simp only [Ψfun]; rw [dif_pos hrad_cen]
  have hcont_cen : ContinuousAt Ψfun cen := by
    rw [ContinuousAt, hcen0, Filter.tendsto_def]
    intro V hV
    obtain ⟨s₀, hs₀, hV'⟩ := uniform_conv hm H hH V hV
    have h1s : (0:ℝ) < 1 - s₀ := by linarith
    have hnb : ({q : Fin m → unitInterval | rad hm q < 1 - s₀}) ∈ 𝓝 cen := by
      refine IsOpen.mem_nhds (isOpen_lt (continuous_rad hm) continuous_const) ?_
      show rad hm cen < 1 - s₀
      rw [hrad_cen]; exact h1s
    refine Filter.mem_of_superset hnb ?_
    · intro p hp
      show Ψfun p ∈ V
      by_cases h0 : rad hm p = 0
      · have hpc : Ψfun p = y₀ := by simp only [Ψfun]; rw [dif_pos h0]
        rw [hpc]
        exact mem_of_mem_nhds hV
      · have hsp : s₀ < (1 - rad hm p) := by
          have hp' : rad hm p < 1 - s₀ := by simpa using hp
          linarith
        have := hV' ⟨bpt hm p, bpt_mem_boundary hm p h0⟩ ⟨1 - rad hm p, hmem p h0⟩ hsp
        simpa only [Ψfun, dif_neg h0] using this
  have hΨcont : Continuous Ψfun := by
    rw [continuous_iff_continuousAt]
    intro p
    by_cases hp : rad hm p = 0
    · rw [eq_cen_of_rad_eq_zero hm hp]; exact hcont_cen
    · exact hcont_off p hp
  refine ⟨⟨Ψfun, hΨcont⟩, ?_⟩
  intro x
  have hx0 : rad hm x.1 ≠ 0 := by rw [rad_boundary_eq_one hm x.2]; norm_num
  show Ψfun x.1 = H (x, 0)
  simp only [Ψfun, dif_neg hx0]
  exact bpt_cone_boundary hm H x

end Work.ThomBordism.TwoSet
