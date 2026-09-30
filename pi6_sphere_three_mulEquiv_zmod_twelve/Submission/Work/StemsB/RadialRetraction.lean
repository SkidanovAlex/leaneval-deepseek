import Mathlib
import Submission.Work.StemsB.SphLoopModel

set_option synthInstance.maxHeartbeats 400000

/-!
# The radial compression of the outer thickening onto the outer disc (piece (T3) of §H1)

For the thickening step (T3) of `CONTRACTS.md` §H1 the inclusion of the outer closed disc
`A = sphLoopOut n = {∞} ∪ {v | ∃ i, 1 ≤ |v i|}` into the open thickening
`U = {∞} ∪ {v | 1/2 < ‖v‖}` must be a homotopy equivalence, so that
`Work.StemsB.isIso_relChainsMapOf_of_homotopyEquiv` (`RelThickening.lean`) turns it into a
quasi-isomorphism `C_*(E, p⁻¹A) → C_*(E, p⁻¹U)`.

`CONTRACTS.md` §H4 explains why the naive projection `v ↦ v/‖v‖_∞` cannot be used (it is not
continuous at `∞`) and why the correct map is the compression along the sup-norm of the
coordinates,

`v ↦ compFactor n v • v`,   `compFactor n v = max 1 (coordSup n v)⁻¹`,

which is the identity as soon as `coordSup v ≥ 1`, hence the identity near `∞`.  This file proves
the arithmetic content of that map and of the interpolation `((1 - t) * compFactor n v + t) • v`:

* `coordSup_le` — each coordinate is bounded by the sup-norm;
* `exists_coordSup_eq`, `exists_coordSup_eq_of_pos` — the sup-norm is attained (the latter as soon
  as it is positive, i.e. for `v ≠ 0`);
* `one_le_compFactor`, `compFactor_of_one_le` — the size and the two regimes of the factor;
* `mem_sphLoopOut_compFactor` — the compressed point lies in the outer disc `A`;
* `norm_interp_ge`, `norm_interp_gt` — the interpolation keeps the norm `≥ ‖v‖`, hence stays in the
  thickening `U`.

The remaining step (not in this file) is the packaging of the compression and of the interpolation
as *continuous* maps of the model `OnePoint ℝⁿ`: this needs continuity at `∞` only, which follows
from `OnePoint.le_nhds_infty` together with `compFactor = 1` for large `coordSup` and with
`norm_interp_ge`.
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

variable {n : ℕ}

/-- The **sup-norm of the coordinates** of `v : ℝⁿ`: the supremum of `nnnorm (v i)`. -/
def coordSup (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) : NNReal :=
  Finset.univ.sup (fun i => nnnorm (v i))

/-- Each coordinate of `v` is bounded by the sup-norm. -/
theorem coordSup_le (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    nnnorm (v i) ≤ coordSup n v := by
  rw [coordSup]
  exact Finset.le_sup (f := fun i => nnnorm (v i)) (Finset.mem_univ i)

/-- The sup-norm of the coordinates is attained (for a nonempty index type). -/
theorem exists_coordSup_eq (v : EuclideanSpace ℝ (Fin n)) [Nonempty (Fin n)] :
    ∃ i : Fin n, coordSup n v = nnnorm (v i) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n))
    (Finset.univ_nonempty (α := Fin n)) (fun i => nnnorm (v i))
  exact ⟨i, by simpa [coordSup] using hi⟩

/-- The sup-norm of the coordinates is attained as soon as it is positive. -/
theorem exists_coordSup_eq_of_pos (v : EuclideanSpace ℝ (Fin n)) (hv : 0 < coordSup n v) :
    ∃ i : Fin n, coordSup n v = nnnorm (v i) := by
  haveI : Nonempty (Fin n) := by
    rcases isEmpty_or_nonempty (Fin n) with hE | hN
    · haveI := hE
      have hzero : coordSup n v = 0 := by
        rw [coordSup, Finset.univ_eq_empty]
        exact Finset.sup_empty
      rw [hzero] at hv
      exact absurd hv (lt_irrefl 0)
    · exact hN
  exact exists_coordSup_eq v

/-- The **compression factor** `max 1 (coordSup v)⁻¹`. -/
def compFactor (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  max 1 ((coordSup n v : ℝ))⁻¹

/-- The compression factor is at least `1`. -/
theorem one_le_compFactor (v : EuclideanSpace ℝ (Fin n)) : 1 ≤ compFactor n v :=
  le_max_left _ _

/-- For `coordSup v ≥ 1` the compression factor is `1` (the compression fixes `v`). -/
theorem compFactor_of_one_le (v : EuclideanSpace ℝ (Fin n)) (h : 1 ≤ (coordSup n v : ℝ)) :
    compFactor n v = 1 := by
  have hpos : (0 : ℝ) < (coordSup n v : ℝ) := lt_of_lt_of_le zero_lt_one h
  have hinv : ((coordSup n v : ℝ))⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr h
  rw [compFactor]
  exact max_eq_left hinv

/-- **The compressed point lies in the outer closed disc** `sphLoopOut n` (an attaining coordinate
is supplied). -/
theorem mem_sphLoopOut_compFactor (v : EuclideanSpace ℝ (Fin n)) (hv : 0 < coordSup n v)
    (i : Fin n) (hi : coordSup n v = nnnorm (v i)) :
    (OnePoint.some (compFactor n v • v) : SphModel n) ∈ sphLoopOut n := by
  refine Or.inr ⟨compFactor n v • v, rfl, i, ?_⟩
  have hspos : (0 : ℝ) < (coordSup n v : ℝ) := by exact_mod_cast hv
  have hvi : (coordSup n v : ℝ) = |v i| := by
    have h1 : ((coordSup n v : ℝ)) = (nnnorm (v i) : ℝ) := by rw [hi]
    rw [coe_nnnorm, Real.norm_eq_abs] at h1
    exact h1
  have hcoord : (compFactor n v • v) i = compFactor n v * v i := by simp
  have habs : |(compFactor n v • v) i| = max (coordSup n v : ℝ) 1 := by
    have hc0 : (0 : ℝ) ≤ compFactor n v := le_trans zero_le_one (one_le_compFactor v)
    rw [hcoord, abs_mul, abs_of_nonneg hc0]
    rw [← hvi, compFactor]
    rw [max_mul_of_nonneg 1 ((coordSup n v : ℝ))⁻¹ hspos.le]
    rw [one_mul, inv_mul_cancel₀ hspos.ne']
  rw [habs]
  exact le_max_right _ _

/-- **The interpolation keeps the norm at least `‖v‖`**: the factor
`(1 - t) * compFactor v + t` is always `≥ 1`. -/
theorem norm_interp_ge (v : EuclideanSpace ℝ (Fin n)) (t : unitInterval) :
    ‖v‖ ≤ ‖(((1 - (t : ℝ)) * compFactor n v + (t : ℝ)) • v)‖ := by
  have h1 : (1 : ℝ) ≤ compFactor n v := one_le_compFactor v
  have hc : (1 : ℝ) ≤ (1 - (t : ℝ)) * compFactor n v + (t : ℝ) := by
    nlinarith [t.2.1, t.2.2, h1]
  have hc0 : (0 : ℝ) ≤ (1 - (t : ℝ)) * compFactor n v + (t : ℝ) := le_trans zero_le_one hc
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
  nlinarith [norm_nonneg v]

/-- The interpolated point stays in the outer thickening `{∞} ∪ {‖v‖ > 1/2}`. -/
theorem norm_interp_gt (v : EuclideanSpace ℝ (Fin n)) (t : unitInterval)
    (hv : (1 / 2 : ℝ) < ‖v‖) :
    (1 / 2 : ℝ) < ‖(((1 - (t : ℝ)) * compFactor n v + (t : ℝ)) • v)‖ :=
  lt_of_lt_of_le hv (norm_interp_ge v t)

/-! ## The continuity obligations at `∞` -/

/-- The **compression** of the model: `∞ ↦ ∞`, `↑v ↦ ↑(compFactor v • v)`.  This is the map whose
restriction to `↥U` is the retraction onto `↥A` of §H4. -/
def compressFun (n : ℕ) : SphModel n → SphModel n
  | none => none
  | some v => some (compFactor n v • v)

@[simp] theorem compressFun_infty (n : ℕ) :
    compressFun n OnePoint.infty = OnePoint.infty := rfl

@[simp] theorem compressFun_some (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    compressFun n (OnePoint.some v) = OnePoint.some (compFactor n v • v) := rfl

/-- **Continuity of the compression at `∞`** (the only non-formal point of (T3)): for `v → ∞` the
norms of `compFactor v • v` are `≥ ‖v‖ → ∞`, so the compression is eventually outside every compact
set. -/
theorem continuousAt_compressFun_infty (n : ℕ) :
    ContinuousAt (compressFun n) OnePoint.infty := by
  rw [OnePoint.continuousAt_infty]
  intro s hs
  obtain ⟨t₀, ⟨ht₀cl, ht₀cp⟩, ht₀sub⟩ := (OnePoint.hasBasis_nhds_infty.mem_iff).mp hs
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall
    (0 : EuclideanSpace ℝ (Fin n))).mp ht₀cp.isBounded
  refine ⟨Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, Metric.isClosed_closedBall,
    isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ?_⟩
  intro v hv
  have hnorm : R < ‖v‖ := by
    have hv' : R < dist v (0 : EuclideanSpace ℝ (Fin n)) := by
      simpa only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] using hv
    simpa [dist_eq_norm, sub_zero] using hv'
  have hbig : R < ‖compFactor n v • v‖ := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_trans zero_le_one (one_le_compFactor v))]
    exact lt_of_lt_of_le hnorm (le_mul_of_one_le_left (norm_nonneg v) (one_le_compFactor v))
  have hnot : compFactor n v • v ∉ t₀ := by
    intro hmem
    have hle : ‖compFactor n v • v‖ ≤ R := by
      have := hR hmem
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using this
    linarith
  exact ht₀sub (Or.inl ⟨compFactor n v • v, hnot, rfl⟩)

/-- **The coordinate sup-norm vanishes exactly at the origin.** -/
theorem coordSup_eq_zero_iff (v : EuclideanSpace ℝ (Fin n)) : coordSup n v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hcoord : ∀ i : Fin n, v i = 0 := by
      intro i
      have hle : nnnorm (v i) ≤ 0 := by
        have := coordSup_le v i
        rwa [h] at this
      exact nnnorm_eq_zero.mp (le_antisymm hle zero_le)
    ext i
    simpa using hcoord i
  · intro h
    rw [h, coordSup]
    exact le_antisymm (Finset.sup_le (fun i _ => by simp)) zero_le

/-- **The coordinate sup-norm is continuous.** -/
theorem continuous_coordSup (n : ℕ) : Continuous (coordSup n) := by
  change Continuous fun v : EuclideanSpace ℝ (Fin n) =>
    Finset.univ.sup (fun i => nnnorm (v i))
  fun_prop

/-- **Continuity of the compression factor at a non-zero point**: there the coordinate sup-norm is
non-zero (`coordSup_eq_zero_iff`), so the inversion is continuous. -/
theorem continuousAt_compFactor_of_ne_zero (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    ContinuousAt (fun w : EuclideanSpace ℝ (Fin n) => compFactor n w) v := by
  have hne : coordSup n v ≠ 0 := fun h => hv ((coordSup_eq_zero_iff v).mp h)
  have hne' : (coordSup n v : ℝ) ≠ 0 := by simpa using hne
  have h1 : ContinuousAt (fun w : EuclideanSpace ℝ (Fin n) => (coordSup n w : ℝ)) v :=
    continuous_subtype_val.continuousAt.comp (continuous_coordSup n).continuousAt
  have h2 : ContinuousAt (fun w : EuclideanSpace ℝ (Fin n) => ((coordSup n w : ℝ))⁻¹) v :=
    h1.inv₀ hne'
  have h3 : ContinuousAt (fun w : EuclideanSpace ℝ (Fin n) =>
      max 1 ((coordSup n w : ℝ))⁻¹) v :=
    continuousAt_const.max h2
  simpa [compFactor] using h3

/-- **Continuity of the compression `v ↦ compFactor v • v` at a non-zero point.** -/
theorem continuousAt_compressOnV_of_ne_zero (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    ContinuousAt (fun w : EuclideanSpace ℝ (Fin n) => compFactor n w • w) v :=
  (continuousAt_compFactor_of_ne_zero v hv).smul continuousAt_id

/-- **The last finite-point obligation**: `compressFun` is continuous at `↑v` for `v ≠ 0`
(equivalently on `↥(sphLoopThick n)` and on `↥(sphLoopOut n)`, both of which avoid the origin, where
the compression jumps — see `CONTRACTS.md` §H4). -/
theorem continuousAt_compressFun_some_of_ne_zero (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    ContinuousAt (compressFun n) (OnePoint.some v) := by
  have hcoe : Continuous (OnePoint.some : EuclideanSpace ℝ (Fin n) → SphModel n) :=
    OnePoint.isOpenEmbedding_coe.continuous
  have hinner : Filter.Tendsto (fun w : EuclideanSpace ℝ (Fin n) => compFactor n w • w) (𝓝 v)
      (𝓝 (compFactor n v • v)) := continuousAt_compressOnV_of_ne_zero v hv
  have houter : Filter.Tendsto (OnePoint.some : EuclideanSpace ℝ (Fin n) → SphModel n)
      (𝓝 (compFactor n v • v)) (𝓝 (OnePoint.some (compFactor n v • v))) :=
    (hcoe.continuousAt : ContinuousAt (OnePoint.some : EuclideanSpace ℝ (Fin n) → SphModel n)
      (compFactor n v • v))
  have hcomp : Filter.Tendsto (compressFun n) (Filter.map OnePoint.some (𝓝 v))
      (𝓝 (compressFun n (OnePoint.some v))) :=
    Filter.tendsto_map'_iff.mp (show Filter.Tendsto (compressFun n ∘ OnePoint.some) (𝓝 v)
      (𝓝 (compressFun n (OnePoint.some v))) from houter.comp hinner)
  show Filter.Tendsto (compressFun n) (𝓝 (OnePoint.some v))
    (𝓝 (compressFun n (OnePoint.some v)))
  simpa only [OnePoint.nhds_coe_eq] using hcomp

/-! ## The restricted compression `↥(sphLoopThick n) → ↥(sphLoopOut n)` -/

/-- **The restricted compression**: on the thickening `↥(sphLoopThick n)` the compression is a
continuous map onto the outer disc `↥(sphLoopOut n)`.  This is the map whose homotopy inverse
(the inclusion `↥A ↪ ↥U`) gives the homotopy equivalence of (T3). -/
theorem continuous_compress_sphLoopThick (n : ℕ) :
    ∃ F : C(↥(sphLoopThick n), ↥(sphLoopOut n)),
      ∀ u, (F u : SphModel n) = compressFun n u.1 := by
  have hmem : ∀ u : ↥(sphLoopThick n), compressFun n u.1 ∈ sphLoopOut n := by
    intro u
    rcases u.2 with h | ⟨v, hv, hlt⟩
    · rw [show u.1 = OnePoint.infty from h]
      exact Or.inl rfl
    · have hv0 : v ≠ 0 := by
        intro h0
        rw [h0] at hlt
        norm_num at hlt
      have hpos : 0 < coordSup n v := by
        rcases lt_or_eq_of_le (zero_le : (0 : NNReal) ≤ coordSup n v) with h' | h'
        · exact h'
        · exact absurd ((coordSup_eq_zero_iff v).mp h'.symm) hv0
      obtain ⟨i, hi⟩ := exists_coordSup_eq_of_pos v hpos
      rw [show u.1 = OnePoint.some v from hv]
      simpa using mem_sphLoopOut_compFactor v hpos i hi
  have hcont : Continuous fun u : ↥(sphLoopThick n) => compressFun n u.1 := by
    rw [continuous_iff_continuousAt]
    intro u
    have hval : ContinuousAt (Subtype.val : ↥(sphLoopThick n) → SphModel n) u :=
      continuous_subtype_val.continuousAt
    rcases u.2 with h | ⟨v, hv, hlt⟩
    · have hu : u.1 = OnePoint.infty := h
      exact ((hu ▸ continuousAt_compressFun_infty n)).comp hval
    · have hv0 : v ≠ 0 := by
        intro h0
        rw [h0] at hlt
        norm_num at hlt
      have hu : u.1 = OnePoint.some v := hv
      exact ((hu ▸ continuousAt_compressFun_some_of_ne_zero v hv0)).comp hval
  exact ⟨⟨fun u => ⟨compressFun n u.1, hmem u⟩, hcont.subtype_mk hmem⟩, fun u => rfl⟩

/-! ## The interpolation `H` on the model -/

/-- The **interpolation** on the model: `(∞, t) ↦ ∞` and
`(↑v, t) ↦ ↑(((1 - t) * compFactor v + t) • v)`.  This is the homotopy from the compression
`compressFun n` (at `t = 0`) to the identity (at `t = 1`). -/
def interpolateFun (n : ℕ) (p : SphModel n × unitInterval) : SphModel n :=
  match p.1 with
  | none => none
  | some v => some (((1 - (p.2 : ℝ)) * compFactor n v + (p.2 : ℝ)) • v)

@[simp] theorem interpolateFun_infty (n : ℕ) (t : unitInterval) :
    interpolateFun n (OnePoint.infty, t) = OnePoint.infty := rfl

@[simp] theorem interpolateFun_some (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (t : unitInterval) :
    interpolateFun n (OnePoint.some v, t) =
      OnePoint.some (((1 - (t : ℝ)) * compFactor n v + (t : ℝ)) • v) := rfl






end

end Work.StemsB
