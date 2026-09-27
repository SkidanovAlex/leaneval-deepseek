import Mathlib
import Submission.Work.Drive.geometricCount
import Submission.Work.Drive.clampedSweepImage
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.tripleMultiplicativity
import Submission.Work.Drive.refPlaneLevel
import Submission.Work.Drive.sideGerm_good_exists
import Submission.Work.Drive.sideGerm_good_exists_two_levels

/-!
# Two bridges of the design's `hdense`/`hn2` route: the germ value at a good angle, and the
# independence of the side count from the truncation level

`SWEEP_TRIPLE_GENERIC_STATUS.md` §6 records the chain from the triple genericity to the design's
`hn2`/`hdense`, and `orderTripleParity.lean` supplies the parity half of it (engine + ends clause
`⟹ Odd (Σ_k top_k)`).  Two further identifications are needed to read that identity in the shape in
which `Work.Drive.parityCore_of_sideGerm` states `hdense`, and they are the content of this file.

* **The germ value at a good angle is the honest parity** (`sideGerm_eq_sideVal_of_good`): if the
  *unperturbed* configuration at the angle `w` is a `GoodPair` (`GoodAt Ξ Q c w 0`, which holds at the
  generic angles of the design), then the germ value `sideGerm Ξ Q c w` is the parity of the honest
  loop-vs-sweep count `coreSideCount Q c (rotPresentation Q w)` — because `Ξ 0 = id` makes the honest
  configuration the centre of the germ, and the parity of the count is constant on a ball around it
  (`hU`, the parity locality of the germ lane).  This is what turns an identity between *honest* side
  counts into the identity between *germ* values that `hdense` demands.

* **The side count does not depend on the truncation level** (`coreMeetPt_eq_of_lt_level`,
  `odd_coreSideCount_eq_of_lt_level`): the sweep truncated at the level `c` and the sweep truncated at
  the level `c'` meet the core loop in the *same* set of points, as long as both levels lie below
  every level of the loop, because the sweep's image is
  `{p : class p ∈ classImage P, c ≤ level p ≤ levelOf (P y)}`
  (`Work.Drive.image_clampedSweep`) and the lower bound is then automatic.  Consequence: the
  multiplicativity T6, whose two side values are computed at the *two different* truncation levels of
  the two swept planes (`Work.Drive.odd_topBdryMeet_iff_coreSideCounts`), produces products of the
  *same* side function `e (w) = Odd (coreSideCount Q c (rotPresentation Q w))` at the design's fixed
  level `c`: this is the identification that makes the identity of `orderTripleParity.lean` literally
  the `hdense` identity `e a · e (a+c) + e (-a) · e c + e (-(a+c)) · e (-c) = 1`.

The two are independent of each other and of the triple machinery.
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- In `ZMod 2` the only element different from `1` is `0`. -/
lemma zmod2_eq_zero_of_ne_one {x : ZMod 2} (h : x ≠ 1) : x = 0 := by
  have h2 : x = 0 ∨ x = 1 := by decide +revert
  tauto

/-! ## 1. The germ value at a good angle -/

/-- **The honest configuration is the centre of the germ.**  The count of the perturbed pair at the
parameter `0` is the honest loop-vs-sweep count, because `Ξ 0 = id`. -/
theorem CntAt_zero {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle) (hΞ0 : ∀ p : CappingSpace, Ξ 0 p = p) :
    CntAt Ξ Q c w 0 = coreSideCount Q c (rotPresentation Q w) := by
  have hfun : pertChart Ξ Q (0 : EuclideanSpace ℝ (Fin m)) = Q := by
    funext z
    exact hΞ0 (Q z)
  simp only [CntAt, Prod.fst_zero, Prod.snd_zero]
  rw [hfun]

/-- **The germ value at a good angle is the honest parity.**  Given

* `hE`: good configurations accumulate at `0` (the Sard existence of the germ lane),
* `hU`: the parity of the count is constant on a ball around `0` among good configurations (the parity
  locality of the germ lane),
* `hg0`: the *honest* configuration (parameter `0`) is a `GoodPair` — i.e. the unperturbed pair has
  finitely many, interior, transversal meets (the design's generic-angle condition),

the germ value is `1` exactly when the honest count is odd. -/
theorem sideGerm_eq_one_iff_odd_honest {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) {w : UnitAddCircle}
    (hE : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w t)
    (hU : ∃ ε : ℝ, 0 < ε ∧ ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c w t → GoodAt Ξ Q c w t' →
        Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w t'))
    (hg0 : GoodAt Ξ Q c w 0) :
    sideGerm Ξ Q c w = 1 ↔ Odd (coreSideCount Q c (rotPresentation Q w)) := by
  rw [sideGerm_eq_one_iff_frequently_good_odd Ξ Q c w hE hU]
  obtain ⟨ε, hε, hUε⟩ := hU
  have hball : ∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0, ‖t‖ < ε := by
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m)) hε] with t ht
    rwa [Metric.mem_ball, dist_zero_right] at ht
  have h0lt : ‖(0 : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))‖ < ε := by
    simpa using hε
  have h0cnt : Odd (CntAt Ξ Q c w 0) ↔ Odd (coreSideCount Q c (rotPresentation Q w)) :=
    iff_of_eq (congrArg Odd (CntAt_zero Ξ Q c w hΞ.1))
  constructor
  · intro hf
    obtain ⟨t, ⟨⟨hg, ho⟩, ht⟩⟩ := (hf.and_eventually hball).exists
    exact h0cnt.mp ((hUε t 0 ht h0lt hg hg0) ▸ ho)
  · intro ho
    refine (hE.and_eventually hball).mono fun t ht => ⟨ht.1, ?_⟩
    exact (hUε t 0 ht.2 h0lt ht.1 hg0) ▸ (h0cnt.mpr ho)

/-- **The germ value at a good angle is the design's side value** in `ZMod 2` form: the bridge
between the germ route's count and the honest multiplicativity T6. -/
theorem sideGerm_eq_sideVal_of_good {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) {w : UnitAddCircle}
    (hE : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w t)
    (hU : ∃ ε : ℝ, 0 < ε ∧ ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c w t → GoodAt Ξ Q c w t' →
        Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w t'))
    (hg0 : GoodAt Ξ Q c w 0) :
    sideGerm Ξ Q c w = sideVal Q c (rotPresentation Q w) := by
  have h := sideGerm_eq_one_iff_odd_honest Ξ Q c hΞ hE hU hg0
  rw [sideVal_eq_ite]
  by_cases ho : Odd (coreSideCount Q c (rotPresentation Q w))
  · rw [if_pos ho]
    exact h.mpr ho
  · rw [if_neg ho]
    exact zmod2_eq_zero_of_ne_one fun hh => ho (h.mp hh)

/-! ## 1bis. The germ value from a good configuration, in both directions -/

/-- **A good configuration of odd count forces the germ value to be `1`.**  Given the parity locality
`hU` in a ball of radius `ε`, any good configuration `t` of norm `< ε` with odd count witnesses
`sideGerm Ξ Q c w = 1`.  This is the direction in which the triple identity — proved at a *particular*
perturbation parameter — produces the germ values of `hdense`. -/
theorem sideGerm_eq_one_of_good_odd {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) {w : UnitAddCircle} {ε : ℝ}
    (hU : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c w t → GoodAt Ξ Q c w t' →
        Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w t'))
    {t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)}
    (ht : ‖t‖ < ε) (hg : GoodAt Ξ Q c w t) (ho : Odd (CntAt Ξ Q c w t)) :
    sideGerm Ξ Q c w = 1 := by
  by_contra hne
  have hfreq : ∃ᶠ t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w t' ∧ Even (CntAt Ξ Q c w t') :=
    not_not.mp ((sideGerm_eq_one_iff Ξ Q c w).not.mp hne)
  have hball : ∀ᶠ t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      ‖t'‖ < ε := by
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m)) (lt_of_le_of_lt (norm_nonneg t) ht)] with t' ht'
    rwa [Metric.mem_ball, dist_zero_right] at ht'
  obtain ⟨t', ⟨⟨hg', he'⟩, ht'⟩⟩ := (hfreq.and_eventually hball).exists
  have hodd : Odd (CntAt Ξ Q c w t') := by
    rw [hU t' t ht' ht hg' hg]
    exact ho
  exact (Nat.not_odd_iff_even.mpr he') hodd

/-- **The germ value `1` produces a good configuration of odd count** (the converse direction):
given the Sard existence `hE` and the parity locality `hU` in the ball of radius `ε`,
`sideGerm Ξ Q c w = 1` implies that *any* good configuration of norm `< ε` has odd count.  Together
with `Work.Drive.sideGerm_eq_one_of_good_odd` this is the exact dictionary between the germ values of
`hdense` and the counts produced by the triple machinery. -/
theorem odd_of_sideGerm_eq_one {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) {w : UnitAddCircle}
    (hE : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w t)
    {ε : ℝ} (hε : 0 < ε)
    (hU : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c w t → GoodAt Ξ Q c w t' →
        Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w t'))
    {t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)}
    (h : sideGerm Ξ Q c w = 1) (ht : ‖t‖ < ε) (hg : GoodAt Ξ Q c w t) :
    Odd (CntAt Ξ Q c w t) := by
  obtain ⟨t₀, ⟨⟨hg₀, ho₀⟩, ht₀⟩⟩ :=
    ((sideGerm_eq_one_iff_frequently_good_odd Ξ Q c w hE ⟨ε, hε, hU⟩).mp h).and_eventually
      (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) hε)
      |>.exists
  have ht₀' : ‖t₀‖ < ε := by simpa [dist_zero_right] using ht₀
  rw [hU t t₀ ht ht₀' hg hg₀]
  exact ho₀

/-- **The parity of a perturbed count *is* the germ value** (the semantic content of the definition of
`sideGerm`).  If `t` is a good configuration at the angle `w`, of norm inside the locality ball of
radius `ε`, then the `ZMod 2` value of its count is `sideGerm Ξ Q c w` — in both directions:
`Odd (CntAt)` gives the germ value `1` (`sideGerm_eq_one_of_good_odd`) and `Even (CntAt)` gives `0`
(contrapositive of `odd_of_sideGerm_eq_one`).

This is the dictionary that turns an identity among counts at a *good perturbed* configuration into the
germ identity of `hdense`; it needs neither the honest configuration nor any genericity in the angle. -/
theorem CntAt_cast_eq_sideGerm {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) {w : UnitAddCircle} {ε : ℝ}
    (hE : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w t)
    (hε : 0 < ε)
    (hU : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c w t → GoodAt Ξ Q c w t' →
        Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w t'))
    {t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)}
    (ht : ‖t‖ < ε) (hg : GoodAt Ξ Q c w t) :
    ((CntAt Ξ Q c w t : ℕ) : ZMod 2) = sideGerm Ξ Q c w := by
  by_cases ho : Odd (CntAt Ξ Q c w t)
  · rw [(zmod2_natCast_eq_one_iff_odd _).mpr ho,
      sideGerm_eq_one_of_good_odd Ξ Q c hU ht hg ho]
  · have hne : sideGerm Ξ Q c w ≠ 1 := fun h =>
      ho (odd_of_sideGerm_eq_one Ξ Q c hE hε hU h ht hg)
    rw [zmod2_eq_zero_of_ne_one (fun hh => ho ((zmod2_natCast_eq_one_iff_odd _).mp hh)),
      zmod2_eq_zero_of_ne_one hne]

/-! ## 2. The side count is independent of the truncation level -/

/-- The cutoff of the clamped sweep, `1 - ·`, is admissible. -/
theorem oneSub_psi_data :
    (fun t : ℝ => 1 - t) 0 = 1 ∧ (fun t : ℝ => 1 - t) 1 = 0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, (fun t : ℝ => 1 - t) t ∈ Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn (fun t : ℝ => 1 - t) (Set.Icc (0 : ℝ) 1) :=
  ⟨by norm_num, by norm_num,
    fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩,
    (continuous_const.sub continuous_id).continuousOn⟩

/-- **The geometric meet set of the loop with the sweep does not depend on the truncation level**, as
long as both levels lie below every level of the loop.  (The sweep's image is the cone between its
truncation level and the plane, so the only role of the truncation level is the lower bound
`c ≤ levelOf p`, which is then automatic.) -/
theorem coreMeetPt_eq_of_lt_level {Q : ℂ → CappingSpace} {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c')
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hloop : ∀ t ∈ Set.Icc (0 : ℝ) 1, c < levelOf (coreLoop Q t) ∧ c' < levelOf (coreLoop Q t))
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (hr' : ∀ y ∈ Submission.Drive.unitBox 1, c' ≤ levelOf (P y)) :
    coreMeetPt Q c P = coreMeetPt Q c' P := by
  obtain ⟨hψ0, hψ1, hψ01, hcont⟩ := oneSub_psi_data
  unfold coreMeetPt
  rw [image_clampedSweep c hc (fun t : ℝ => 1 - t) hψ0 hψ1 hψ01 hcont P hr,
    image_clampedSweep c' hc' (fun t : ℝ => 1 - t) hψ0 hψ1 hψ01 hcont P hr']
  ext p
  constructor
  · rintro ⟨hloop_mem, y, hy, hcls, -, hle⟩
    obtain ⟨t, ht, rfl⟩ := hloop_mem
    exact ⟨⟨t, ht, rfl⟩, y, hy, hcls, le_of_lt (hloop t ht).2, hle⟩
  · rintro ⟨hloop_mem, y, hy, hcls, -, hle⟩
    obtain ⟨t, ht, rfl⟩ := hloop_mem
    exact ⟨⟨t, ht, rfl⟩, y, hy, hcls, le_of_lt (hloop t ht).1, hle⟩

/-- **The pairing count is independent of the truncation level.** -/
theorem coreSideCountPt_eq_of_lt_level {Q : ℂ → CappingSpace} {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c')
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hloop : ∀ t ∈ Set.Icc (0 : ℝ) 1, c < levelOf (coreLoop Q t) ∧ c' < levelOf (coreLoop Q t))
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (hr' : ∀ y ∈ Submission.Drive.unitBox 1, c' ≤ levelOf (P y)) :
    coreSideCountPt Q c P = coreSideCountPt Q c' P := by
  rw [coreSideCountPt, coreSideCountPt, coreMeetPt_eq_of_lt_level hc hc' P hloop hr hr']

/-- **The parity of the box count is independent of the truncation level**, at configurations at which
the parameterisation of the meets is injective (i.e. no meet lies on a seam of the two parameter
squares — the design's `GoodPair` interiority) and the meet sets are finite. -/
theorem odd_coreSideCount_eq_of_lt_level {Q : ℂ → CappingSpace} {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c')
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hloop : ∀ t ∈ Set.Icc (0 : ℝ) 1, c < levelOf (coreLoop Q t) ∧ c' < levelOf (coreLoop Q t))
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (hr' : ∀ y ∈ Submission.Drive.unitBox 1, c' ≤ levelOf (P y))
    (hfin : (coreMeet Q c P).Finite) (hfin' : (coreMeet Q c' P).Finite)
    (hinj : Set.InjOn (fun p : ℝ × Work.Drive.Amb 2 => coreLoop Q p.1) (coreMeet Q c P))
    (hinj' : Set.InjOn (fun p : ℝ × Work.Drive.Amb 2 => coreLoop Q p.1) (coreMeet Q c' P)) :
    Odd (coreSideCount Q c P) ↔ Odd (coreSideCount Q c' P) := by
  have h1 := (coreMeetPt_ncard_eq_iff Q c P hfin).mpr hinj
  have h2 := (coreMeetPt_ncard_eq_iff Q c' P hfin').mpr hinj'
  have h3 := coreSideCountPt_eq_of_lt_level hc hc' P hloop hr hr'
  rw [← h1, ← h2, h3]

/-! ## 3. The level transfer in the design's chart-band form -/

/-- **The parity of the side count of a rotated plane presentation does not depend on the truncation
level, given the chart's level band.**  This is the design-facing form of
`odd_coreSideCount_eq_of_lt_level`: the chart `Q` is continuous on the closed disk with
`clo ≤ levelOf (Q z)`, and the truncated levels `c`, `c'` lie strictly below `clo`.  Every rotated
presentation `rotPresentation Q v` has its levels in the same band
(`Work.Drive.le_levelOf_rotPresentation`), so both hypotheses of the level-independence lemma are
automatic — the only remaining inputs are the finiteness and the injectivity of the parameterisation on
the meet set (the design's `GoodPair` data at the two levels). -/
theorem odd_coreSideCount_eq_of_levelBand
    (Q : ℂ → CappingSpace) (v : UnitAddCircle) {clo : ℝ}
    (hband : ∀ z : ℂ, ‖z‖ ≤ 1 → clo ≤ levelOf (Q z))
    {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (hcc : c < clo) (hc'c : c' < clo)
    (hfin : (coreMeet Q c (rotPresentation Q v)).Finite)
    (hfin' : (coreMeet Q c' (rotPresentation Q v)).Finite)
    (hinj : Set.InjOn (fun p : ℝ × Work.Drive.Amb 2 => coreLoop Q p.1)
      (coreMeet Q c (rotPresentation Q v)))
    (hinj' : Set.InjOn (fun p : ℝ × Work.Drive.Amb 2 => coreLoop Q p.1)
      (coreMeet Q c' (rotPresentation Q v))) :
    Odd (coreSideCount Q c (rotPresentation Q v))
      ↔ Odd (coreSideCount Q c' (rotPresentation Q v)) := by
  have hloop : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      c < levelOf (coreLoop Q t) ∧ c' < levelOf (coreLoop Q t) := by
    intro t _
    have hnorm : ‖Complex.exp (Real.pi * (t : ℂ) * Complex.I)‖ ≤ 1 := by
      rw [Complex.norm_exp]
      simp
    have h1 : clo ≤ levelOf (coreLoop Q t) :=
      hband (Complex.exp (Real.pi * (t : ℂ) * Complex.I)) hnorm
    exact ⟨lt_of_lt_of_le hcc h1, lt_of_lt_of_le hc'c h1⟩
  exact odd_coreSideCount_eq_of_lt_level hc hc' (rotPresentation Q v) hloop
    (fun y _ => le_of_lt (lt_of_lt_of_le hcc (le_levelOf_rotPresentation Q hband v y)))
    (fun y _ => le_of_lt (lt_of_lt_of_le hc'c (le_levelOf_rotPresentation Q hband v y)))
    hfin hfin' hinj hinj'

/-! ## 3bis. The germ value does not depend on the truncation level -/

/-- **The germ value is independent of the truncation level.**  Two levels `c`, `c'` give the same germ
value, provided that

* `hE`, `hE'`: good configurations accumulate at `0` at the two levels (the Sard existence,
  `Work.Drive.sideGerm_good_exists`);
* `hU`, `hU'`: the parity of the count is constant on the ball of radius `ε` among the good
  configurations at the level (the parity locality of the germ lane);
* (the joint density of good configurations at **both** levels, inside the ball, is *derived* here
  from `Work.Drive.sideGerm_good_exists_two_levels` — the joint Sard statement proved by the fleet);
* `hpar`: the parity of the count agrees at the two levels at a configuration good at **both**
  (`Work.Drive.odd_coreSideCount_eq_of_lt_level` / `..._of_levelBand`, whose level hypotheses are
  automatic below the chart's level band).

The proof is the standard "dense bridge" argument: `sideGerm` at a level is `1` exactly when there is a
good configuration of odd count (`Work.Drive.sideGerm_eq_one_iff_frequently_good_odd`), and the joint
density plus `hpar` and the two locality statements move that witness between the levels.

This is the bridge that lets the multiplicativity T6 — whose factors come at the *truncation* levels of
the swept planes — be read off at the design's fixed level `c` in the germ route
(`TRIPLE_IDENTITY_STATUS.md` §9.1). -/
theorem sideGerm_eq_of_level_lt {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (w : UnitAddCircle) {ε : ℝ} (hε : 0 < ε)
    (hE : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w t)
    (hU : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c w t → GoodAt Ξ Q c w t' →
        Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w t'))
    (hE' : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c' w t)
    (hU' : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c' w t → GoodAt Ξ Q c' w t' →
        Odd (CntAt Ξ Q c' w t) = Odd (CntAt Ξ Q c' w t'))
    (hpar : ∀ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      GoodAt Ξ Q c w t → GoodAt Ξ Q c' w t →
        Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c' w t)) :
    sideGerm Ξ Q c w = sideGerm Ξ Q c' w := by
  -- the joint density of good configurations at the two levels
  have hJ : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      ‖t‖ < ε ∧ GoodAt Ξ Q c w t ∧ GoodAt Ξ Q c' w t := by
    refine ((sideGerm_good_exists_two_levels Ξ Q c c' hΞ hQ hc hc' w).and_eventually
      (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m) ×
        EuclideanSpace ℝ (Fin m)) hε)).mono ?_
    rintro t ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by simpa [Metric.mem_ball, dist_zero_right] using h3, h1, h2⟩
  have hiff := sideGerm_eq_one_iff_frequently_good_odd Ξ Q c w hE ⟨ε, hε, hU⟩
  have hiff' := sideGerm_eq_one_iff_frequently_good_odd Ξ Q c' w hE' ⟨ε, hε, hU'⟩
  have hkey : (∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t ∧ Odd (CntAt Ξ Q c w t)) ↔
      (∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c' w t ∧ Odd (CntAt Ξ Q c' w t)) := by
    constructor
    · intro hf
      obtain ⟨t₀, hlt₀, hg₀, hg₀'⟩ := hJ.exists
      obtain ⟨t₁, ht₁⟩ :=
        (hf.and_eventually
          (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m) ×
            EuclideanSpace ℝ (Fin m)) hε)).exists
      obtain ⟨⟨hg₁, ho₁⟩, hmem₁⟩ := ht₁
      have hlt₁ : ‖t₁‖ < ε := by
        simpa [Metric.mem_ball, dist_zero_right] using hmem₁
      have ho₀ : Odd (CntAt Ξ Q c w t₀) := by
        rw [hU t₀ t₁ hlt₀ hlt₁ hg₀ hg₁]
        exact ho₁
      have ho₀' : Odd (CntAt Ξ Q c' w t₀) := by
        rw [← hpar t₀ hg₀ hg₀']
        exact ho₀
      refine hJ.mono fun t ht => ⟨ht.2.2, ?_⟩
      rw [hU' t t₀ ht.1 hlt₀ ht.2.2 hg₀']
      exact ho₀'
    · intro hf
      obtain ⟨t₀, hlt₀, hg₀, hg₀'⟩ := hJ.exists
      obtain ⟨t₁, ht₁⟩ :=
        (hf.and_eventually
          (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m) ×
            EuclideanSpace ℝ (Fin m)) hε)).exists
      obtain ⟨⟨hg₁, ho₁⟩, hmem₁⟩ := ht₁
      have hlt₁ : ‖t₁‖ < ε := by
        simpa [Metric.mem_ball, dist_zero_right] using hmem₁
      have ho₀ : Odd (CntAt Ξ Q c' w t₀) := by
        rw [hU' t₀ t₁ hlt₀ hlt₁ hg₀' hg₁]
        exact ho₁
      have ho₀'' : Odd (CntAt Ξ Q c w t₀) := by
        rw [hpar t₀ hg₀ hg₀']
        exact ho₀
      refine hJ.mono fun t ht => ⟨ht.2.1, ?_⟩
      rw [hU t t₀ ht.1 hlt₀ ht.2.1 hg₀]
      exact ho₀''
  have h1 : sideGerm Ξ Q c w = 1 ↔ sideGerm Ξ Q c' w = 1 :=
    hiff.trans (hkey.trans hiff'.symm)
  by_cases h : sideGerm Ξ Q c w = 1
  · have h' : sideGerm Ξ Q c' w = 1 := h1.mp h
    rw [h, h']
  · have h' : sideGerm Ξ Q c' w ≠ 1 := fun hh => h (h1.mpr hh)
    rw [zmod2_eq_zero_of_ne_one h, zmod2_eq_zero_of_ne_one h']

/-! ## 3ter. The dictionary at a level, transferred to the design's level -/

/-- **The parity of a perturbed count is the design's germ value.**  This packages
`Work.Drive.CntAt_cast_eq_sideGerm` (the dictionary at the truncation level `c'`) with the germ's level
independence `Work.Drive.sideGerm_eq_of_level_lt`, so that a count taken at the level `c'` of a swept
plane is read at the design's fixed level `c` — the form in which the multiplicitavity T6's factors are
converted into `sideGerm` values.

The two Sard existences `hE`/`hE'` are *derived* here from `Work.Drive.sideGerm_good_exists`; the
locality `hU` at the two levels, the joint density `hJ` and the cross-level parity agreement `hpar`
are the caller's inputs (the last two are the statements being proved by the fleet:
`Work.Drive.sideGerm_good_exists_two_levels` and `Work.Drive.odd_coreSideCount_eq_of_level_lt`). -/
theorem CntAt_cast_eq_sideGerm_of_level_lt {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    {c c' : ℝ} (w : UnitAddCircle) {ε : ℝ} (hε : 0 < ε) (hc : 0 < c) (hc' : 0 < c')
    (hU : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c w t → GoodAt Ξ Q c w t' →
        Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w t'))
    (hU' : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c' w t → GoodAt Ξ Q c' w t' →
        Odd (CntAt Ξ Q c' w t) = Odd (CntAt Ξ Q c' w t'))
    (hpar : ∀ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      GoodAt Ξ Q c w t → GoodAt Ξ Q c' w t →
        Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c' w t))
    {t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)}
    (ht : ‖t‖ < ε) (hg : GoodAt Ξ Q c' w t) :
    ((CntAt Ξ Q c' w t : ℕ) : ZMod 2) = sideGerm Ξ Q c w := by
  have hE : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w t := sideGerm_good_exists Ξ Q c hΞ hQ hc w
  have hE' : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c' w t := sideGerm_good_exists Ξ Q c' hΞ hQ hc' w
  rw [CntAt_cast_eq_sideGerm Ξ Q c' hE' hε hU' ht hg,
    ← sideGerm_eq_of_level_lt Ξ Q hΞ hQ hc hc' w hε hE hU hE' hU' hpar]

/-! ## 4. The `hdense` identity at a good triple, from the honest identity -/

/-- **The design's functional identity for the germ values, from the honest identity.**

This is the `hid` obligation of `Work.Drive.hdense_sideGerm_of_good_identity` at a pair `(a, c')` whose
six associated angles are *good* (the honest configuration at the parameter `0` is a `GoodPair`): the
six germ values are then the six honest side values
(`Work.Drive.sideGerm_eq_sideVal_of_good`, which uses the Sard existence `hE` and the parity locality
`hU` at each of the six angles), and the honest identity is the output of the triple machinery
(`Work.Drive.sum_sideVal_mul_eq_one_of_blockT6_design`).

`hE` is provable for every angle (`Work.Drive.sideGerm_good_exists`) and `hU` at every angle is the
germ lane's parity locality (`Work.Drive.sideGerm_parity_eq_of_close`); only the six `GoodAt … 0`
facts are genuinely restricted (they hold on a dense set of angles — the design's genericity). -/
theorem hdense_identity_of_honest_identity {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (a c' : UnitAddCircle)
    (hΞ : ChartPert Q m Ξ)
    (hE : ∀ w : UnitAddCircle, ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w t)
    (hU : ∀ w : UnitAddCircle, ∃ ε : ℝ, 0 < ε ∧
      ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
        ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c w t → GoodAt Ξ Q c w t' →
          Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w t'))
    (hg0 : GoodAt Ξ Q c a 0) (hg1 : GoodAt Ξ Q c (a + c') 0) (hg2 : GoodAt Ξ Q c (-a) 0)
    (hg3 : GoodAt Ξ Q c c' 0) (hg4 : GoodAt Ξ Q c (-(a + c')) 0) (hg5 : GoodAt Ξ Q c (-c') 0)
    (hhonest : sideVal Q c (rotPresentation Q a) * sideVal Q c (rotPresentation Q (a + c'))
      + sideVal Q c (rotPresentation Q (-a)) * sideVal Q c (rotPresentation Q c')
      + sideVal Q c (rotPresentation Q (-(a + c'))) * sideVal Q c (rotPresentation Q (-c')) = 1) :
    sideGerm Ξ Q c a * sideGerm Ξ Q c (a + c')
      + sideGerm Ξ Q c (-a) * sideGerm Ξ Q c c'
      + sideGerm Ξ Q c (-(a + c')) * sideGerm Ξ Q c (-c') = 1 := by
  rw [sideGerm_eq_sideVal_of_good Ξ Q c hΞ (hE a) (hU a) hg0,
    sideGerm_eq_sideVal_of_good Ξ Q c hΞ (hE (a + c')) (hU (a + c')) hg1,
    sideGerm_eq_sideVal_of_good Ξ Q c hΞ (hE (-a)) (hU (-a)) hg2,
    sideGerm_eq_sideVal_of_good Ξ Q c hΞ (hE c') (hU c') hg3,
    sideGerm_eq_sideVal_of_good Ξ Q c hΞ (hE (-(a + c'))) (hU (-(a + c'))) hg4,
    sideGerm_eq_sideVal_of_good Ξ Q c hΞ (hE (-c')) (hU (-c')) hg5]
  exact hhonest

end

end Work.Drive
