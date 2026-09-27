import Mathlib
set_option linter.unusedVariables false

/-!
# Flat (clean-crossing) frontiers

This file develops the "(c2)" ingredient of the spine recursion: the purely topological
**clean-crossing** property of a frontier, which turns a level arc's footprint in the next shell
into a single *spike* (an arc attached to the frontier with a free end) — hence into a harmless
obstacle for the next level (see `escape_spikes_and_slits`).  The point of the notion is that it
*does not require smoothness*: it is the property that near a frontier point, an arc starting
inside and ending outside crosses the frontier along an initial segment of its parameter interval.

## The Euclidean model

`CleanCrossingAt S S' z` says: there is a ball `ball z ρ` which is *disjoint from `S'`* and such
that every straight segment from a point of `ball z ρ ∩ interior S` to a point of
`ball z ρ \ S` meets `S` in an initial segment of its parameter interval.  The extra set `S'` is the
"already occupied" part of the region (for instance the previous exhaustion level `L i` in the
application `S = L (i+1)`, `S' = L i`): the whole point is that the crossing can be performed
*away from* `S'`, so that the level arc does not enter it.

## Proved here

* `cleanCrossing_segment_closedBall` — **the convexity lemma**: for a closed ball, the set of
  parameters of a segment from a point inside to a point outside is an initial segment.
* `cleanCrossingAt_closedBall` — the packaged "flatness of a closed ball", relative to a smaller
  concentric ball `closedBall c r'` (`r' < r`).
* `cleanCrossing_segment_halfSpace_le`, `cleanCrossingAt_halfSpace_le` — the model case of a
  closed half-space (the local model at a point of an honest smooth boundary).

## Next (delegated / to come)

The finite disjoint union of closed balls (`L i` will be such a union), and its image under a
chart, giving the manifold-level statement: for a compact `K` and open `U ⊇ K`, a compact
`S` with `K ⊆ interior S ⊆ S ⊆ U` whose frontier is clean-crossing away from `K`.
-/

namespace Work.Noncompact.CompressionTube

open Set Metric

variable {n : ℕ}

/-- **Clean crossing of a frontier, away from `S'`** (Euclidean model).  There is a ball around `z`
disjoint from `S'` such that every straight segment from a point of the ball inside `S` to a point
of the ball outside `S` crosses the frontier of `S` exactly once, and does so "cleanly": the set of
parameters at which the segment lies in `S` is an initial segment of `[0,1]`. -/
def CleanCrossingAt (S S' : Set (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ Disjoint (Metric.ball z ρ) S' ∧
    ∀ p ∈ Metric.ball z ρ ∩ interior S, ∀ q ∈ Metric.ball z ρ \ S,
      ∃ s ∈ Icc (0 : ℝ) 1,
        (∀ t ∈ Icc (0 : ℝ) s, (1 - t) • p + t • q ∈ S) ∧
        (∀ t ∈ Ioc s 1, (1 - t) • p + t • q ∉ S)

/-- **Clean crossing of a frontier by an *arc*** (Euclidean model).  This is `CleanCrossingAt` with
the straight segment replaced by an arbitrary continuous path inside the ball.  It is the correct
notion at *corner* points of a union of balls: there the straight segment from `p ∈ int S` to
`q ∉ S` can leave `S`, pass through the gap between the balls and re-enter `S`, whereas an arc can
route around the corner and leave `S` exactly once.  (The statement `CleanCrossingAt` for a finite
union of balls is *false*: see §10 of `NOTES_flat_scheme.md`.) -/
def CleanArcCrossingAt (S S' : Set (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ Disjoint (Metric.ball z ρ) S' ∧
    ∀ p ∈ Metric.ball z ρ ∩ interior S, ∀ q ∈ Metric.ball z ρ \ S,
      ∃ (s : ℝ) (α : ℝ → EuclideanSpace ℝ (Fin n)),
        Continuous α ∧ α 0 = p ∧ α 1 = q ∧ α '' Icc (0 : ℝ) 1 ⊆ Metric.ball z ρ ∧
        s ∈ Icc (0 : ℝ) 1 ∧ (∀ t ∈ Icc (0 : ℝ) s, α t ∈ S) ∧ (∀ t ∈ Ioc s 1, α t ∉ S)

/-- **The convexity lemma.**  For a closed ball, the set of parameters for which the segment from
`p` (inside) to `q` (outside) lies in the ball is an initial segment. -/
theorem cleanCrossing_segment_closedBall {c : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    {p q : EuclideanSpace ℝ (Fin n)} (hp : p ∈ closedBall c r) (hq : q ∉ closedBall c r) :
    ∃ s ∈ Icc (0 : ℝ) 1,
      (∀ t ∈ Icc (0 : ℝ) s, (1 - t) • p + t • q ∈ closedBall c r) ∧
      (∀ t ∈ Ioc s 1, (1 - t) • p + t • q ∉ closedBall c r) := by
  have hconv : Convex ℝ (closedBall c r) := convex_closedBall c r
  set A : Set ℝ := {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ (1 - t) • p + t • q ∈ closedBall c r}
    with hAdef
  have hAne : A.Nonempty := ⟨0, by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    simpa using hp⟩
  have hAbdd : BddAbove A := ⟨1, fun t ht => ht.1.2⟩
  have hAclosed : IsClosed A := by
    have hcont : Continuous fun t : ℝ => (1 - t) • p + t • q := by fun_prop
    exact isClosed_Icc.inter (((isCompact_closedBall c r).isClosed).preimage hcont)
  set s : ℝ := sSup A with hsdef
  have hsA : s ∈ A := hAclosed.csSup_mem hAne hAbdd
  have hs01 : s ∈ Icc (0 : ℝ) 1 := hsA.1
  have hxs : (1 - s) • p + s • q ∈ closedBall c r := hsA.2
  refine ⟨s, hs01, ?_, ?_⟩
  · intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hts : t ≤ s := ht.2
    rcases eq_or_lt_of_le hts with h | h
    · rw [h]; exact hxs
    · have hs0 : 0 < s := lt_of_le_of_lt ht0 h
      have hcomb : (1 - t) • p + t • q
          = ((s - t) / s) • p + (t / s) • ((1 - s) • p + s • q) := by
        have hs : s ≠ 0 := ne_of_gt hs0
        have h1 : (1 - t) = (s - t) / s + (t / s) * (1 - s) := by
          rw [div_mul_eq_mul_div, ← add_div, eq_div_iff hs]
          ring
        have h2 : t = (t / s) * s := by
          rw [div_mul_cancel₀ _ hs]
        have hp1 : (1 - t) • p = ((s - t) / s + (t / s) * (1 - s)) • p :=
          congrArg (· • p) h1
        have hq : t • q = ((t / s) * s) • q := congrArg (· • q) h2
        rw [hp1, hq, add_smul, mul_smul, mul_smul, smul_add]
        abel
      have hsum : ((s - t) / s + t / s : ℝ) = 1 := by
        rw [← add_div, div_eq_iff (ne_of_gt hs0), one_mul]; ring
      rw [hcomb]
      exact hconv hp hxs (div_nonneg (by linarith) hs0.le) (div_nonneg (by linarith) hs0.le)
        hsum
  · intro t ht htS
    have ht1 : t ≤ 1 := ht.2
    have ht0 : 0 ≤ t := le_of_lt (lt_of_le_of_lt hs01.1 ht.1)
    have htA : t ∈ A := ⟨⟨ht0, ht1⟩, htS⟩
    exact absurd (le_csSup hAbdd htA) (not_le.mpr ht.1)

/-- **Flatness of a closed ball**, relative to a smaller concentric ball: the crossing can be made
away from `closedBall c r'`. -/
theorem cleanCrossingAt_closedBall {c : EuclideanSpace ℝ (Fin n)} {r r' : ℝ}
    (hr' : 0 ≤ r') (hlt : r' < r) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ frontier (closedBall c r)) :
    CleanCrossingAt (closedBall c r) (closedBall c r') z := by
  have hr : 0 < r := lt_of_le_of_lt hr' hlt
  have hzdist : dist z c = r := by
    have h := hz
    rw [frontier_closedBall c (ne_of_gt hr)] at h
    simpa [mem_sphere, dist_eq_norm] using h
  refine ⟨(r - r') / 2, by linarith, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro y hy hy'
    have hy1 : dist y z < (r - r') / 2 := hy
    have hy2 : dist y c ≤ r' := hy'
    have h3 : dist z c ≤ dist z y + dist y c := dist_triangle z y c
    rw [hzdist] at h3
    have hyz : dist z y = dist y z := dist_comm z y
    rw [hyz] at h3
    linarith
  · intro p hp q hq
    exact cleanCrossing_segment_closedBall (interior_subset hp.2) hq.2

/-- **The model case: a closed half-space.**  The parameter set is computed by linearity. -/
theorem cleanCrossing_segment_halfSpace_le {l : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ}
    (_hl : l ≠ 0) {a : ℝ} {p q : EuclideanSpace ℝ (Fin n)} (hp : l p ≤ a) (hq : a < l q) :
    ∃ s ∈ Icc (0 : ℝ) 1,
      (∀ t ∈ Icc (0 : ℝ) s, l ((1 - t) • p + t • q) ≤ a) ∧
      (∀ t ∈ Ioc s 1, a < l ((1 - t) • p + t • q)) := by
  set s : ℝ := (a - l p) / (l q - l p) with hsdef
  have hden : 0 < l q - l p := by linarith
  have hs0 : 0 ≤ s := by
    rw [hsdef]; exact div_nonneg (by linarith) hden.le
  have hs1 : s ≤ 1 := by
    rw [hsdef, div_le_one hden]
    linarith
  have hval : ∀ t : ℝ, l ((1 - t) • p + t • q) = (1 - t) * l p + t * l q := by
    intro t
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hexpand : ∀ t : ℝ, (1 - t) * l p + t * l q = l p + t * (l q - l p) := by
    intro t; ring
  refine ⟨s, ⟨hs0, hs1⟩, ?_, ?_⟩
  · intro t ht
    have h : t * (l q - l p) ≤ a - l p := by
      have h2 : t ≤ s := ht.2
      rw [le_div_iff₀ hden] at h2
      linarith
    calc l ((1 - t) • p + t • q) = l p + t * (l q - l p) := by rw [hval t, hexpand t]
      _ ≤ a := by linarith
  · intro t ht
    have h : a - l p < t * (l q - l p) := by
      have h2 : s < t := ht.1
      rw [div_lt_iff₀ hden] at h2
      linarith
    calc a < l p + t * (l q - l p) := by linarith
      _ = l ((1 - t) • p + t • q) := by rw [hval t, hexpand t]

/-- **Flatness of a closed half-space.** -/
theorem cleanCrossingAt_halfSpace_le {l : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ} (hl : l ≠ 0)
    (a : ℝ) :
    ∀ z ∈ frontier {y : EuclideanSpace ℝ (Fin n) | l y ≤ a},
      CleanCrossingAt {y : EuclideanSpace ℝ (Fin n) | l y ≤ a} ∅ z := by
  intro z hz
  refine ⟨1, one_pos, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro y hy hy'
    exact hy'
  · intro p hp q hq
    have hpS : l p ≤ a :=
      (interior_subset : interior {y : EuclideanSpace ℝ (Fin n) | l y ≤ a} ⊆
        {y : EuclideanSpace ℝ (Fin n) | l y ≤ a}) hp.2
    have hqz : a < l q := by
      by_contra hcon
      exact hq.2 (not_lt.mp hcon)
    obtain ⟨s, hs, h1, h2⟩ := cleanCrossing_segment_halfSpace_le hl hpS hqz
    exact ⟨s, hs, fun t ht => h1 t ht, fun t ht => not_le.mpr (h2 t ht)⟩

end Work.Noncompact.CompressionTube
