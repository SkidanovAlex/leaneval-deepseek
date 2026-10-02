/-
# The superlevel sets `{G_c > r}` are preconnected

The critical domain `critDomain c = {G_c > G_c 0}` of the parameter-plane Böttcher theory is
*preconnected*; this is the only genuinely new topological fact the `ParamRaysCrit` area needs
(it replaces the preconnectedness of the escaping set `{G_c > 0}`, which suffices in the
dynamical plane).

The proof uses the two-sided bound `|G_c w - log ‖w‖| ≤ log 2` above the escape radius
(`abs_greenFun_sub_log_le`) to write, for `r > 0`,

  `{z | G_c z > r} = ⋃_{n ∈ ℕ} {z | max (escR c) (exp (4^n r + log 2)) < ‖T_c^{2n} z‖}`,

a union of *preimages of exteriors of balls* under the entire coercive maps
`z ↦ T_c^{2n} z`.  Each member of the family is preconnected
(`isPreconnected_lt_norm_of_differentiable`), and any two members meet outside a large ball:
if `max 2 ‖c‖ < ‖z‖` then `‖z‖ ≤ ‖T_c^k z‖` (`norm_le_norm_orbit`), so a point of sufficiently
large norm lies in every member.  A union of preconnected sets with a common point is
preconnected (`isPreconnected_iUnion`).

  * `⊆`: for `G_c z > r > 0` the orbit of `z` escapes; at a large even iterate both
    `‖T_c^{2n} z‖ > escR c` and `4^n (G_c z - r) > 2 log 2` hold, whence the bound
    `log ‖T_c^{2n} z‖ ≥ 4^n G_c z - log 2 > 4^n r + log 2`.
  * `⊇`: a point with `‖T_c^{2n} z‖ > max (escR c) (exp (4^n r + log 2))` satisfies
    `4^n G_c z = G_c (T_c^{2n} z) ≥ log ‖T_c^{2n} z‖ - log 2 > 4^n r`.

## Main results

* `Work.ParamRays.levelRadius`, `Work.ParamRays.levelSet` : the threshold and the approximating
  sets of the union above.
* `Work.ParamRays.levelSet_subset_le_greenFun`, `Work.ParamRays.lt_greenFun_subset_iUnion_levelSet`.
* `Work.ParamRays.isPreconnected_greenFun_gt` : `{z | r < G_c z}` is preconnected for `r > 0`.
* `Work.ParamRays.isOpen_lt_greenFun`, `Work.ParamRays.isOpen_critDomain` : the same sets are open.
* `Work.ParamRays.isPreconnected_critDomain` : `critDomain c` is preconnected.
-/
import Submission.Work.ParamRaysCrit.GreenBound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology

namespace Work.ParamRays

/-! ## The approximating family -/

/-- The threshold above which `T_c^{2n} z` must lie in order that `G_c z > r`:
`max (escR c) (exp (4^n r + log 2))`. -/
noncomputable def levelRadius (c : ℂ) (r : ℝ) (n : ℕ) : ℝ :=
  max (escR c) (Real.exp ((4 : ℝ) ^ n * r + Real.log 2))

/-- The `n`-th approximating set of `{G_c > r}`: the points whose `2n`-th iterate lies above the
threshold `levelRadius c r n`. -/
def levelSet (c : ℂ) (r : ℝ) (n : ℕ) : Set ℂ :=
  {z : ℂ | levelRadius c r n < ‖orbit c z (2 * n)‖}

theorem levelRadius_pos (c : ℂ) (r : ℝ) (n : ℕ) : 0 < levelRadius c r n :=
  lt_of_lt_of_le (escR_pos c) (le_max_left _ _)

/-- Each approximating set is preconnected: it is the preimage of an exterior of a ball under
the entire coercive map `z ↦ T_c^{2n} z`. -/
theorem isPreconnected_levelSet (c : ℂ) (r : ℝ) (n : ℕ) :
    IsPreconnected (levelSet c r n) :=
  isPreconnected_lt_norm_of_differentiable (differentiable_orbit_two_mul c n)
    (tendsto_norm_orbit_two_mul c n) (levelRadius_pos c r n).le

/-- Any two approximating sets meet: outside a sufficiently large ball the norm of `z` is a
lower bound for the norms of all its even orbit points (`norm_le_norm_orbit`). -/
theorem levelSet_nonempty_inter (c : ℂ) (r : ℝ) (n m : ℕ) :
    (levelSet c r n ∩ levelSet c r m).Nonempty := by
  have hbase : (0 : ℝ) ≤ max 2 ‖c‖ := le_trans (by norm_num) (le_max_left _ _)
  set N : ℝ := max (max (levelRadius c r n) (levelRadius c r m)) (max 2 ‖c‖) + 1 with hN
  have hbig : max (levelRadius c r n) (levelRadius c r m) < N := by
    have h := le_max_left (max (levelRadius c r n) (levelRadius c r m)) (max 2 ‖c‖)
    rw [hN]; linarith
  have hcN : max 2 ‖c‖ < N := by
    have h := le_max_right (max (levelRadius c r n) (levelRadius c r m)) (max 2 ‖c‖)
    rw [hN]; linarith
  have hN0 : (0 : ℝ) ≤ N := le_trans hbase hcN.le
  have hnorm : ‖(N : ℂ)‖ = N := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN0]
  have hlt : max 2 ‖c‖ < ‖(N : ℂ)‖ := by rw [hnorm]; exact hcN
  refine ⟨(N : ℂ), ?_, ?_⟩
  · show levelRadius c r n < ‖orbit c (N : ℂ) (2 * n)‖
    have hln : levelRadius c r n ≤ max (levelRadius c r n) (levelRadius c r m) := le_max_left _ _
    have h2n := norm_le_norm_orbit c (N : ℂ) hlt (2 * n)
    rw [hnorm] at h2n
    linarith
  · show levelRadius c r m < ‖orbit c (N : ℂ) (2 * m)‖
    have hlm : levelRadius c r m ≤ max (levelRadius c r n) (levelRadius c r m) := le_max_right _ _
    have h2m := norm_le_norm_orbit c (N : ℂ) hlt (2 * m)
    rw [hnorm] at h2m
    linarith

/-! ## The two inclusions -/

/-- A point of `levelSet c r n` has `G_c > r`: above the threshold, `log ‖T_c^{2n} z‖` exceeds
`4^n r + log 2`, while `G_c (T_c^{2n} z) ≥ log ‖T_c^{2n} z‖ - log 2`. -/
theorem levelSet_subset_le_greenFun (c : ℂ) (r : ℝ) (n : ℕ) :
    levelSet c r n ⊆ {z : ℂ | r < greenFun c z} := by
  intro z hz
  have hz' : levelRadius c r n < ‖orbit c z (2 * n)‖ := hz
  have h1 : escR c < ‖orbit c z (2 * n)‖ := lt_of_le_of_lt (le_max_left _ _) hz'
  have h2 : Real.exp ((4 : ℝ) ^ n * r + Real.log 2) < ‖orbit c z (2 * n)‖ :=
    lt_of_le_of_lt (le_max_right _ _) hz'
  have hc : max 2 ‖c‖ < ‖orbit c z (2 * n)‖ := lt_of_lt_of_le (lt_max_escR c) h1.le
  have hlog : Real.log (Real.exp ((4 : ℝ) ^ n * r + Real.log 2)) <
      Real.log ‖orbit c z (2 * n)‖ := Real.log_lt_log (Real.exp_pos _) h2
  rw [Real.log_exp] at hlog
  have h3 := log_sub_le_greenFun c (orbit c z (2 * n)) hc
  rw [greenFun_orbit] at h3
  have hpow : (2 : ℝ) ^ (2 * n) = (4 : ℝ) ^ n := by rw [pow_mul]; norm_num
  rw [hpow] at h3
  have h4 : (4 : ℝ) ^ n * r < (4 : ℝ) ^ n * greenFun c z := by
    rw [mul_comm ((4 : ℝ) ^ n) r]
    linarith
  exact lt_of_mul_lt_mul_left h4 (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ n)

/-- Every point with `G_c > r > 0` lies in some `levelSet c r n`. -/
theorem lt_greenFun_subset_iUnion_levelSet (c : ℂ) {r : ℝ} (hr : 0 < r) :
    {z : ℂ | r < greenFun c z} ⊆ ⋃ n : ℕ, levelSet c r n := by
  intro z hz
  have hzr : r < greenFun c z := hz
  have hesc : Escaping c z := (greenFun_pos_iff_escaping c z).mp (lt_trans hr hzr)
  have hApos : 0 < greenFun c z - r := by linarith
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hesc.eventually_gt (escR c))
  have hbig : ∀ᶠ n : ℕ in Filter.atTop, 2 * Real.log 2 / (greenFun c z - r) < (4 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).eventually
      (Filter.eventually_gt_atTop _)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hbig
  refine Set.mem_iUnion.mpr ⟨max N₁ N₂, ?_⟩
  show levelRadius c r (max N₁ N₂) < ‖orbit c z (2 * max N₁ N₂)‖
  have h1 : N₁ ≤ 2 * max N₁ N₂ :=
    le_trans (le_max_left _ _) (Nat.le_mul_of_pos_left (max N₁ N₂) (by norm_num))
  have hfar : escR c < ‖orbit c z (2 * max N₁ N₂)‖ := hN₁ _ h1
  have hgt2 : max 2 ‖c‖ < ‖orbit c z (2 * max N₁ N₂)‖ := lt_of_lt_of_le (lt_max_escR c) hfar.le
  have hmax : 2 * Real.log 2 < (4 : ℝ) ^ (max N₁ N₂) * (greenFun c z - r) := by
    have h5 := hN₂ (max N₁ N₂) (le_max_right _ _)
    rw [div_lt_iff₀ hApos] at h5
    linarith
  have hgl := greenFun_le_log_add c (orbit c z (2 * max N₁ N₂)) hgt2
  rw [greenFun_orbit] at hgl
  have hpow : (2 : ℝ) ^ (2 * max N₁ N₂) = (4 : ℝ) ^ (max N₁ N₂) := by rw [pow_mul]; norm_num
  rw [hpow] at hgl
  have hlogbig : (4 : ℝ) ^ (max N₁ N₂) * r + Real.log 2 <
      Real.log ‖orbit c z (2 * max N₁ N₂)‖ := by linarith
  rw [levelRadius, max_lt_iff]
  refine ⟨hfar, ?_⟩
  have hXpos : 0 < ‖orbit c z (2 * max N₁ N₂)‖ := lt_of_lt_of_le (escR_pos c) hfar.le
  have hexp := Real.exp_lt_exp.mpr hlogbig
  rwa [Real.exp_log hXpos] at hexp

/-! ## Preconnectedness -/

/-- **The superlevel sets of the Green function are preconnected.** -/
theorem isPreconnected_greenFun_gt (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsPreconnected {z : ℂ | r < greenFun c z} := by
  have hEq : {z : ℂ | r < greenFun c z} =
      ⋃ n : ℕ, (levelSet c r n ∪ levelSet c r 0) := by
    ext z
    constructor
    · intro hz
      have hzr : r < greenFun c z := hz
      have hmem : z ∈ ⋃ n : ℕ, levelSet c r n := lt_greenFun_subset_iUnion_levelSet c hr hzr
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
      exact Set.mem_iUnion.mpr ⟨n, Or.inl hn⟩
    · intro hz
      obtain ⟨n, h⟩ := Set.mem_iUnion.mp hz
      rcases h with h | h
      · exact levelSet_subset_le_greenFun c r n h
      · exact levelSet_subset_le_greenFun c r 0 h
  rw [hEq]
  refine isPreconnected_iUnion ?_ ?_
  · obtain ⟨x, hx⟩ := levelSet_nonempty_inter c r 0 0
    exact ⟨x, Set.mem_iInter.mpr fun n => Or.inr hx.2⟩
  · intro n
    obtain ⟨y, hy₁, hy₂⟩ := levelSet_nonempty_inter c r n 0
    exact IsPreconnected.union y hy₁ hy₂ (isPreconnected_levelSet c r n)
      (isPreconnected_levelSet c r 0)

/-! ## Openness -/

/-- Each approximating set is open (preimage of an open ray under a continuous map). -/
theorem isOpen_levelSet (c : ℂ) (r : ℝ) (n : ℕ) : IsOpen (levelSet c r n) :=
  isOpen_lt continuous_const ((differentiable_orbit_two_mul c n).continuous.norm)

/-- **The superlevel sets of the Green function are open** (for `r > 0`). -/
theorem isOpen_lt_greenFun (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsOpen {z : ℂ | r < greenFun c z} := by
  have hEq : {z : ℂ | r < greenFun c z} = ⋃ n : ℕ, levelSet c r n := by
    ext z
    constructor
    · intro hz
      exact lt_greenFun_subset_iUnion_levelSet c hr hz
    · intro hz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
      exact levelSet_subset_le_greenFun c r n hn
  rw [hEq]
  exact isOpen_iUnion fun n => isOpen_levelSet c r n

/-- **The critical domain is open.**  On the mandelbar it is the escaping set, which is the union
of the (open) sets `{z | escR c < ‖T_c^{2n} z‖}`. -/
theorem isOpen_critDomain (c : ℂ) : IsOpen (critDomain c) := by
  rcases eq_or_lt_of_le (paramPotential_nonneg c) with h | h
  · have hEq : critDomain c = ⋃ n : ℕ, {z : ℂ | escR c < ‖orbit c z (2 * n)‖} := by
      ext z
      rw [mem_critDomain, Set.mem_iUnion, ← h]
      exact (greenFun_pos_iff_escaping c z).trans (escaping_iff_exists_escR c z)
    rw [hEq]
    refine isOpen_iUnion fun n => isOpen_lt continuous_const ?_
    exact ((differentiable_orbit_two_mul c n).continuous.norm)
  · exact isOpen_lt_greenFun c h

/-- **The critical domain is preconnected.**  Off the mandelbar this is
`isPreconnected_greenFun_gt` at `r = paramPotential c > 0`; on the mandelbar the critical domain
is the escaping set, whose preconnectedness is `isPreconnected_escapingSet`. -/
theorem isPreconnected_critDomain (c : ℂ) : IsPreconnected (critDomain c) := by
  rcases eq_or_lt_of_le (paramPotential_nonneg c) with h | h
  · have hEq : critDomain c = escapingSet c := by
      ext z
      rw [mem_critDomain, mem_escapingSet, ← h]
      exact greenFun_pos_iff_escaping c z
    rw [hEq]
    exact isPreconnected_escapingSet c
  · exact isPreconnected_greenFun_gt c h

end Work.ParamRays
