import Mathlib
import Submission.Work.Drive.sideGermLoop
import Submission.Work.Drive.germLevelBridge

/-!
# `hn2` at an angle, reduced to a parity statement at *joint-good* parameters

This file is the interface between the **germ** antisymmetry `hn2_sideGerm`
(`Submission/Work/Drive/hn2_sideGerm.lean`)

> `sideGerm Ξ Q c (v - u) + sideGerm Ξ Q c (u - v) = 1`   for `v - u ∈ Zc γ`

and the **count** identity that the reference-triple machinery (the triples of chains, the engine and the
multiplicativity T6) produces, which is a statement about `CntAt`, the parity of the loop-vs-sweep count
at a *good perturbed* configuration.

The point is that the two germ values `sideGerm a` and `sideGerm (-a)` may be evaluated at **different**
good parameters `t` and `t'`: `Work.Drive.CntAt_cast_eq_sideGerm` says that at *any* good parameter of
norm inside the locality ball the `ZMod 2` value of the count *is* the germ value.  Hence

> `sideGerm a + sideGerm (-a) = 1`   ⟸   `Odd (CntAt a t + CntAt (-a) t')`

for *any* pair of good parameters `(t, t')` of small norm — and this is exactly the shape in which the
reference-triple count identity is delivered (block `0` at the coupled parameter `(τ₀,τ₁)` and block `1`
at the transposed one `(τ₁,τ₀)`).

Nothing here is geometric: it is the dictionary `CntAt ↔ sideGerm` of `germLevelBridge.lean` applied at
the two angles, together with the parity locality of the germ route
(`Work.Drive.sideGerm_parity_eq_of_close_loop`) to produce the locality balls.
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The germ antisymmetry at an angle, from the parity of the two counts at (possibly different)
good parameters.**  `hUa`/`hUn` are the parity localities at the two angles (any two good
configurations of norm `< ε` have counts of the same parity); the conclusion needs only the *sum* of the
two counts to be odd at *one* pair of good parameters `t`, `t'` of norm `< ε`.

This is the exact shape of the reference-triple computation of `hn2`: the triple machinery produces
`Odd (CntAt Ξ Q (cblk 1) (v - u) (τ₀, τ₁) + CntAt Ξ Q (cblk 0) (u - v) (τ₁, τ₀))`, and the level
transfer (`Work.Drive.CntAt_cast_eq_sideGerm_of_level_lt`) moves the truncation levels to the design's
level `c`. -/
theorem sideGerm_add_neg_eq_one_of_counts {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (a : UnitAddCircle) {ε : ℝ} (hε : 0 < ε)
    (hUa : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c a t → GoodAt Ξ Q c a t' →
        Odd (CntAt Ξ Q c a t) = Odd (CntAt Ξ Q c a t'))
    (hUn : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c (-a) t → GoodAt Ξ Q c (-a) t' →
        Odd (CntAt Ξ Q c (-a) t) = Odd (CntAt Ξ Q c (-a) t'))
    (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q) (hc : 0 < c)
    {t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)}
    (ht : ‖t‖ < ε) (ht' : ‖t'‖ < ε) (hg : GoodAt Ξ Q c a t) (hg' : GoodAt Ξ Q c (-a) t')
    (hpar : Odd (CntAt Ξ Q c a t + CntAt Ξ Q c (-a) t')) :
    sideGerm Ξ Q c a + sideGerm Ξ Q c (-a) = 1 := by
  have h2 : ((CntAt Ξ Q c a t : ℕ) : ZMod 2) = sideGerm Ξ Q c a :=
    CntAt_cast_eq_sideGerm Ξ Q c (sideGerm_good_exists Ξ Q c hΞ hQ hc a) hε hUa ht hg
  have h3 : ((CntAt Ξ Q c (-a) t' : ℕ) : ZMod 2) = sideGerm Ξ Q c (-a) :=
    CntAt_cast_eq_sideGerm Ξ Q c (sideGerm_good_exists Ξ Q c hΞ hQ hc (-a)) hε hUn ht' hg'
  have h4 : (((CntAt Ξ Q c a t + CntAt Ξ Q c (-a) t' : ℕ)) : ZMod 2) = 1 :=
    (zmod2_natCast_eq_one_iff_odd _).mpr hpar
  rw [Nat.cast_add] at h4
  rw [← h2, ← h3, h4]

/-- **The same, with the locality balls produced by the germ route.**  The only hypotheses on the chart
are the loop-vs-rotated-disk disjointness at the two angles `a` and `-a` (which the chart lane derives
from `Zc γ`, `Work.Drive.disjoint_range_coreLoop_rotCapping_chartDisk`); the conclusion is that *some*
radius `ε > 0` works.

This is the local form of `hn2_sideGerm` at the angle `a`: it remains to produce, for every `a`, a pair
of good parameters of norm `< ε` whose counts have odd sum — which is what the reference triple
`(P_u, P_v, R)` computes. -/
theorem exists_pos_sideGerm_add_neg_eq_one_of_counts_loop {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (a : UnitAddCircle)
    (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q) (hc : 0 < c)
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hloopa : Disjoint (Set.range (coreLoop Q)) (rotCapping a '' chartDisk Q))
    (hloopn : Disjoint (Set.range (coreLoop Q)) (rotCapping (-a) '' chartDisk Q)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
        ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c a t → GoodAt Ξ Q c (-a) t' →
          Odd (CntAt Ξ Q c a t + CntAt Ξ Q c (-a) t') →
            sideGerm Ξ Q c a + sideGerm Ξ Q c (-a) = 1 := by
  obtain ⟨εa, δa, hεa, hδa, hAa⟩ :=
    sideGerm_parity_eq_of_close_loop Ξ Q c hΞ hQ hc hcbot a hloopa
  obtain ⟨εn, δn, hεn, hδn, hAn⟩ :=
    sideGerm_parity_eq_of_close_loop Ξ Q c hΞ hQ hc hcbot (-a) hloopn
  refine ⟨min εa εn, lt_min hεa hεn, ?_⟩
  intro t t' ht ht' hg hg' hpar
  have ht1 : ‖t‖ < εa := lt_of_lt_of_le ht (min_le_left _ _)
  have ht2 : ‖t‖ < εn := lt_of_lt_of_le ht (min_le_right _ _)
  have ht'1 : ‖t'‖ < εa := lt_of_lt_of_le ht' (min_le_left _ _)
  have ht'2 : ‖t'‖ < εn := lt_of_lt_of_le ht' (min_le_right _ _)
  refine sideGerm_add_neg_eq_one_of_counts Ξ Q c a (lt_min hεa hεn) ?_ ?_ hΞ hQ.1 hc
    ht ht' hg hg' hpar
  · intro s s' hs hs' h1 h2
    refine hAa s s' a (lt_of_lt_of_le hs (min_le_left _ _))
      (lt_of_lt_of_le hs' (min_le_left _ _)) ?_ h1 h2
    rw [dist_self]
    exact hδa
  · intro s s' hs hs' h1 h2
    refine hAn s s' (-a) (lt_of_lt_of_le hs (min_le_right _ _))
      (lt_of_lt_of_le hs' (min_le_right _ _)) ?_ h1 h2
    rw [dist_self]
    exact hδn

/-- **The germ antisymmetry at an angle from the *count identity at the truncation levels*.**

This is the form in which the reference-triple machinery delivers its conclusion: a `ZMod 2` identity
between the two counts `CntAt` taken at the **truncation levels** `c₀`, `c₁` of the two swept planes
(not at the design's level `c`).  The dictionary
`Work.Drive.CntAt_cast_eq_sideGerm_of_level_lt` moves each count to the design's level and to the germ
value, so the two-term identity transfers verbatim.

The hypotheses `hUa`/`hUa'`/`hparA` (resp. `hUn`/`hUn'`/`hparN`) are the germ lane's locality data at
the design's level and at the truncation level, and the cross-level parity agreement; all three are
proved at *every* angle by `Work.Drive.sideGerm_parity_eq_of_close_loop` /
`Work.Drive.odd_coreSideCount_eq_of_level_lt` in the consuming files. -/
theorem sideGerm_add_neg_eq_one_of_counts_at_levels {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (c c₀ c₁ : ℝ) (hc : 0 < c) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (a : UnitAddCircle) {ε : ℝ} (hε : 0 < ε)
    (hUa : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c a t → GoodAt Ξ Q c a t' →
        Odd (CntAt Ξ Q c a t) = Odd (CntAt Ξ Q c a t'))
    (hUa' : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c₀ a t → GoodAt Ξ Q c₀ a t' →
        Odd (CntAt Ξ Q c₀ a t) = Odd (CntAt Ξ Q c₀ a t'))
    (hparA : ∀ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      GoodAt Ξ Q c a t → GoodAt Ξ Q c₀ a t → Odd (CntAt Ξ Q c a t) = Odd (CntAt Ξ Q c₀ a t))
    (hUn : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c (-a) t → GoodAt Ξ Q c (-a) t' →
        Odd (CntAt Ξ Q c (-a) t) = Odd (CntAt Ξ Q c (-a) t'))
    (hUn' : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c₁ (-a) t → GoodAt Ξ Q c₁ (-a) t' →
        Odd (CntAt Ξ Q c₁ (-a) t) = Odd (CntAt Ξ Q c₁ (-a) t'))
    (hparN : ∀ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      GoodAt Ξ Q c (-a) t → GoodAt Ξ Q c₁ (-a) t → Odd (CntAt Ξ Q c (-a) t) = Odd (CntAt Ξ Q c₁ (-a) t))
    {t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)}
    (ht : ‖t‖ < ε) (ht' : ‖t'‖ < ε) (hg : GoodAt Ξ Q c₀ a t) (hg' : GoodAt Ξ Q c₁ (-a) t')
    (hkey : ((CntAt Ξ Q c₀ a t : ℕ) : ZMod 2) + ((CntAt Ξ Q c₁ (-a) t' : ℕ) : ZMod 2) = 1) :
    sideGerm Ξ Q c a + sideGerm Ξ Q c (-a) = 1 := by
  rw [← CntAt_cast_eq_sideGerm_of_level_lt Ξ Q hΞ hQ (c := c) (c' := c₀) a hε hc hc₀
      hUa hUa' hparA ht hg,
    ← CntAt_cast_eq_sideGerm_of_level_lt Ξ Q hΞ hQ (c := c) (c' := c₁) (-a) hε hc hc₁
      hUn hUn' hparN ht' hg']
  exact hkey

/-- **The cross-level parity of the perturbed count** — the `hpar` obligation of
`Work.Drive.CntAt_cast_eq_sideGerm_of_level_lt`, discharged by the germ lane's
`Work.Drive.odd_coreSideCount_eq_of_lt_level` at the *perturbed* chart.

`CntAt Ξ Q c a t` unfolds to the box count `coreSideCount (pertChart Ξ Q t.1) c
(rotPresentation (pertChart Ξ Q t.2) a)`, so the level independence of the box count applies verbatim:
the two truncation levels `c`, `c'` (both below every level of the loop) give the same parity as soon
as the two meet parameterisations are faithful (finite, and the loop parameter determines the meet).

The level-band hypotheses (`hloop` for the loop, `hr`/`hr'` for the swept plane) are consequences of
the chart's level band and of `levelOf_rotPresentation`; the faithfulness hypotheses are the two
clauses of the design's goodness at the two levels. -/
theorem odd_CntAt_eq_of_lt_level {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace)
    {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (a : UnitAddCircle)
    (t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (hloop : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      c < levelOf (coreLoop (pertChart Ξ Q t.1) s) ∧ c' < levelOf (coreLoop (pertChart Ξ Q t.1) s))
    (hr : ∀ y ∈ Submission.Drive.unitBox 1,
      c ≤ levelOf (rotPresentation (pertChart Ξ Q t.2) a y))
    (hr' : ∀ y ∈ Submission.Drive.unitBox 1,
      c' ≤ levelOf (rotPresentation (pertChart Ξ Q t.2) a y))
    (hfin : (coreMeet (pertChart Ξ Q t.1) c (rotPresentation (pertChart Ξ Q t.2) a)).Finite)
    (hfin' : (coreMeet (pertChart Ξ Q t.1) c' (rotPresentation (pertChart Ξ Q t.2) a)).Finite)
    (hinj : Set.InjOn (fun p : ℝ × Work.Drive.Amb 2 => coreLoop (pertChart Ξ Q t.1) p.1)
      (coreMeet (pertChart Ξ Q t.1) c (rotPresentation (pertChart Ξ Q t.2) a)))
    (hinj' : Set.InjOn (fun p : ℝ × Work.Drive.Amb 2 => coreLoop (pertChart Ξ Q t.1) p.1)
      (coreMeet (pertChart Ξ Q t.1) c' (rotPresentation (pertChart Ξ Q t.2) a))) :
    Odd (CntAt Ξ Q c a t) ↔ Odd (CntAt Ξ Q c' a t) :=
  odd_coreSideCount_eq_of_lt_level hc hc' (rotPresentation (pertChart Ξ Q t.2) a)
    hloop hr hr' hfin hfin' hinj hinj'

/-- **The `ZMod 2` two-term identity implies the oddness of the sum of the two counts** (the form in
which `Work.Drive.cntAt_pair_eq_one_of_threeBlockT6` feeds
`Work.Drive.sideGerm_add_neg_eq_one_of_counts`). -/
theorem odd_add_of_zmod2_add_eq_one {x y : ℕ}
    (h : ((x : ℕ) : ZMod 2) + ((y : ℕ) : ZMod 2) = 1) : Odd (x + y) :=
  (zmod2_natCast_eq_one_iff_odd (x + y)).mp (by rw [Nat.cast_add]; exact h)

end

end Work.Drive
