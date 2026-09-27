import Mathlib
import Submission.Work.Whitney.CutPush.arc_straightening

/-!
# The adapter: from the straightening family to a family of embedded regular arcs

`CutPush/NOTES_hasFingerData_S49.md` §6.  The straightening family
`straighteningFamily c v Λ : ℝ → ℝ → ℝ^m` of `CutPush/arc_straightening.lean` goes from the arc `c`
(at parameter `1`) to the straight segment (at parameter `0`), and it is injective and regular, but
it is not yet a family in the shape required by `CutPush/ambientIsotopy_of_arcFamily`: that statement
wants

* `hstat0`/`hstat1` — stationarity in the time parameter outside `[0,1]`, at *both* ends (the base
  member for `lam ≤ 0`, the target member for `lam ≥ 1`), and
* `hbound` — the trail of the family is bounded (this is what the flow construction's cutoff needs;
  note that the unbounded `straighteningFamily` itself is *not* bounded in `t`).

This file builds the adapter `localisedArc`:

    localisedArc lam t = χ t • straighteningFamily c v Λ (1 - σ lam) t + (1 - χ t) • c 0

with `σ := Real.smoothTransition` and `χ t := σ (t + 2) * σ (3 - t)`.  The point of the choice of `χ`
is that its "`1`-region" is the **closed** interval `[-1, 2]`, which contains an *open neighbourhood*
of `Icc 0 1`; hence on `Icc 0 1` the bump is locally constant, so **its derivative vanishes there by
local constancy** — no flatness-at-the-endpoint input is needed (which is what a bump with
`1`-region exactly `Icc 0 1` would have required).  This is what carries `hinj` *and* `himm` from the
straightening family to the adapter (via the product rule, where the `χ'` terms drop out).

Blending to the *constant* `c 0` (rather than back to `c`) is what makes `hbound` true: `χ` is
compactly supported, and off its support the adapter is the single point `c 0`.
-/

namespace Work.Whitney.CutPush

open scoped Manifold ContDiff
open Topology

/-- The bump `χ t = σ (t + 2) * σ (3 - t)`: `1` on `[-1, 2]`, `0` off `[-2, 3]`. -/
noncomputable def arcBump (t : ℝ) : ℝ :=
  Real.smoothTransition (t + 2) * Real.smoothTransition (3 - t)

@[fun_prop]
theorem arcBump_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) arcBump := by
  unfold arcBump
  fun_prop

theorem arcBump_eq_one {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 2) : arcBump t = 1 := by
  have h1 : (1 : ℝ) ≤ t + 2 := by linarith [ht.1]
  have h2 : (1 : ℝ) ≤ 3 - t := by linarith [ht.2]
  simp [arcBump, Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2]

/-- `χ` is locally constant equal to `1` on the *open* interval `(-1, 2)`. -/
theorem arcBump_eventuallyEq_one {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 2) :
    arcBump =ᶠ[nhds t] fun _ => (1 : ℝ) := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact arcBump_eq_one ⟨le_of_lt hs.1, le_of_lt hs.2⟩

/-- **The derivative of the bump vanishes on `Icc 0 1`** — by local constancy, since `Icc 0 1` lies in
the interior of the `1`-region `Icc (-1) 2`. -/
theorem arcBump_hasDerivAt_zero {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt arcBump 0 t :=
  (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq
    (arcBump_eventuallyEq_one ⟨by linarith [ht.1], by linarith [ht.2]⟩)

/-- The adapter family: the straightening family reindexed by `lam ↦ 1 - σ lam` and localised to a
neighbourhood of `Icc 0 1`, blending to the constant point `c 0` off the bump's support. -/
noncomputable def localisedArc {m : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin m)) (Λ : ℝ) : ℝ → ℝ → EuclideanSpace ℝ (Fin m) :=
  fun lam t =>
    arcBump t • straighteningFamily c v Λ (1 - Real.smoothTransition lam) t
      + (1 - arcBump t) • c 0

theorem localisedArc_contDiff {m : ℕ} {c : ℝ → EuclideanSpace ℝ (Fin m)}
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c) (v : EuclideanSpace ℝ (Fin m)) (Λ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => localisedArc c v Λ p.1 p.2) := by
  unfold localisedArc straighteningFamily
  fun_prop

/-- On `Icc 0 1` the adapter *is* the straightening family (the bump is `1` there). -/
theorem localisedArc_eq_on {m : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin m)) (Λ lam : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    localisedArc c v Λ lam t = straighteningFamily c v Λ (1 - Real.smoothTransition lam) t := by
  have h := arcBump_eq_one (t := t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simp [localisedArc, h]

/-- **`hinj` transfers.** -/
theorem localisedArc_injOn {m : ℕ} {c : ℝ → EuclideanSpace ℝ (Fin m)}
    {v : EuclideanSpace ℝ (Fin m)} (hv : v ≠ 0) (hcf : ChordFree c v) (Λ : ℝ) (hΛ : Λ ≠ 0)
    (lam : ℝ) : Set.InjOn (localisedArc c v Λ lam) (Set.Icc (0 : ℝ) 1) := by
  intro t ht t' ht' hcon
  rw [localisedArc_eq_on c v Λ lam ht, localisedArc_eq_on c v Λ lam ht'] at hcon
  exact straighteningFamily_injOn hv hcf Λ hΛ (1 - Real.smoothTransition lam)
    ht ht' hcon

theorem arcBump_eq_zero_of_le {t : ℝ} (h : t ≤ -2) : arcBump t = 0 := by
  have h1 : Real.smoothTransition (t + 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  simp [arcBump, h1]

theorem arcBump_eq_zero_of_ge {t : ℝ} (h : 3 ≤ t) : arcBump t = 0 := by
  have h1 : Real.smoothTransition (3 - t) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  simp [arcBump, h1]

/-- **`himm` transfers: the adapter has the derivative of the straightening family on `Icc 0 1`.**
The product rule gives `χ' • (Φ - c 0) + χ • Φ'`, and on `Icc 0 1` the bump is locally constant with
value `1`, so `χ = 1` and `χ' = 0` and the derivative is exactly `Φ'`. -/
theorem localisedArc_hasDerivAt {m : ℕ} {c : ℝ → EuclideanSpace ℝ (Fin m)}
    (hc : Differentiable ℝ c) (v : EuclideanSpace ℝ (Fin m)) (Λ lam : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (localisedArc c v Λ lam)
      (fderiv ℝ (straighteningFamily c v Λ (1 - Real.smoothTransition lam)) t 1) t := by
  have hχ : HasDerivAt arcBump 0 t := arcBump_hasDerivAt_zero ht
  have hχ1 : arcBump t = 1 := arcBump_eq_one ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set η : ℝ := 1 - Real.smoothTransition lam with hη
  have hΦ : HasDerivAt (straighteningFamily c v Λ η)
      (fderiv ℝ (straighteningFamily c v Λ η) t 1) t := by
    refine (hasDerivAt_straighteningFormula hc v Λ η t).congr_deriv ?_
    rw [fderiv_straighteningFamily_apply_one hc v Λ η t, smul_smul]
  have hprod : HasDerivAt (fun s : ℝ => arcBump s • straighteningFamily c v Λ η s)
      (arcBump t • (fderiv ℝ (straighteningFamily c v Λ η) t 1)
        + ((0 : ℝ) • straighteningFamily c v Λ η t)) t := hχ.smul hΦ
  have hsub : HasDerivAt (fun s : ℝ => 1 - arcBump s) ((0 : ℝ) - 0) t :=
    (hasDerivAt_const t (1 : ℝ)).sub hχ
  have hconst : HasDerivAt (fun s : ℝ => (1 - arcBump s) • c 0) (((0 : ℝ) - 0) • c 0) t :=
    hsub.smul_const (c 0)
  have hsum := hprod.add hconst
  have hbridge : ((fun s : ℝ => arcBump s • straighteningFamily c v Λ η s)
        + fun s : ℝ => (1 - arcBump s) • c 0)
      = (fun s : ℝ => arcBump s • straighteningFamily c v Λ η s + (1 - arcBump s) • c 0) := by
    funext s
    rfl
  rw [hbridge] at hsum
  have hsimp : arcBump t • (fderiv ℝ (straighteningFamily c v Λ η) t 1)
        + ((0 : ℝ) • straighteningFamily c v Λ η t) + (((0 : ℝ) - 0) • c 0)
      = fderiv ℝ (straighteningFamily c v Λ η) t 1 := by
    rw [hχ1]; simp
  rw [hsimp] at hsum
  have hgoal : localisedArc c v Λ lam
      = fun s : ℝ => arcBump s • straighteningFamily c v Λ η s + (1 - arcBump s) • c 0 := by
    funext s
    simp only [localisedArc, hη]
  rw [hgoal]
  exact hsum

/-- **The adapter consists of regular arcs on `Icc 0 1`.** -/
theorem localisedArc_fderiv_ne_zero {m : ℕ} {c : ℝ → EuclideanSpace ℝ (Fin m)}
    (hc : Differentiable ℝ c) {v : EuclideanSpace ℝ (Fin m)} (hv : v ≠ 0) {Λ : ℝ} (hΛ : Λ ≠ 0)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, fderiv ℝ c t 1 ≠ 0)
    (hpar : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ μ : ℝ, fderiv ℝ c t 1 ≠ μ • v) :
    ∀ lam : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      fderiv ℝ (localisedArc c v Λ lam) t 1 ≠ 0 := by
  intro lam t ht hzero
  have hd := localisedArc_hasDerivAt hc v Λ lam ht
  rw [hd.hasFDerivAt.fderiv] at hzero
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hzero
  exact straighteningFamily_fderiv_ne_zero hc hv hΛ hreg hpar
    (1 - Real.smoothTransition lam) t ht hzero

/-- **`hstat0`**: the adapter is stationary in `lam` for `lam ≤ 0` (there the smooth step is `0`, so
the inner parameter is `1`, i.e. the base arc). -/
theorem localisedArc_hstat0 {m : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin m)) (Λ lam : ℝ) (h : lam ≤ 0) (t : ℝ) :
    localisedArc c v Λ lam t = localisedArc c v Λ 0 t := by
  have h1 : Real.smoothTransition lam = 0 := Real.smoothTransition.zero_of_nonpos h
  have h2 : Real.smoothTransition (0 : ℝ) = 0 := Real.smoothTransition.zero_of_nonpos le_rfl
  simp [localisedArc, h1, h2]

/-- **`hstat1`**: the adapter is stationary in `lam` for `1 ≤ lam` (there the smooth step is `1`, so
the inner parameter is `0`, i.e. the straight segment). -/
theorem localisedArc_hstat1 {m : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin m)) (Λ lam : ℝ) (h : 1 ≤ lam) (t : ℝ) :
    localisedArc c v Λ lam t = localisedArc c v Λ 1 t := by
  have h1 : Real.smoothTransition lam = 1 := Real.smoothTransition.one_of_one_le h
  have h2 : Real.smoothTransition (1 : ℝ) = 1 := Real.smoothTransition.one_of_one_le le_rfl
  simp [localisedArc, h1, h2]

/-- **The adapter is the straight segment at `lam = 1`** (on `Icc 0 1`). -/
theorem localisedArc_one_eq_segment {m : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin m)) (Λ t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    localisedArc c v Λ 1 t = c 0 + (Λ * t) • v := by
  have h1 : Real.smoothTransition (1 : ℝ) = 1 := Real.smoothTransition.one_of_one_le le_rfl
  rw [localisedArc_eq_on c v Λ 1 ht, h1, sub_self]
  simp [straighteningFamily]

/-- **`hbound`**: the trail of the adapter is bounded — off the compact support of the bump the
adapter is the single point `c 0`. -/
theorem localisedArc_bound {m : ℕ} {c : ℝ → EuclideanSpace ℝ (Fin m)} (hc : Continuous c)
    (v : EuclideanSpace ℝ (Fin m)) (Λ : ℝ) :
    ∃ K : Set (EuclideanSpace ℝ (Fin m)), IsCompact K ∧
      ∀ lam, lam ∈ Set.Icc (0 : ℝ) 1 → ∀ t, localisedArc c v Λ lam t ∈ K := by
  have hcont : Continuous (fun p : ℝ × ℝ => localisedArc c v Λ p.1 p.2) := by
    unfold localisedArc straighteningFamily
    fun_prop
  refine ⟨(fun p : ℝ × ℝ => localisedArc c v Λ p.1 p.2) '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-2 : ℝ) 3)
    ∪ {c 0}, (isCompact_Icc.prod isCompact_Icc).image hcont |>.union isCompact_singleton, ?_⟩
  rintro lam hlam t
  by_cases ht : t ∈ Set.Icc (-2 : ℝ) 3
  · exact Or.inl ⟨(lam, t), ⟨hlam, ht⟩, rfl⟩
  · have h0 : arcBump t = 0 := by
      by_cases h : t ≤ -2
      · exact arcBump_eq_zero_of_le h
      · exact arcBump_eq_zero_of_ge (le_of_lt (not_le.mp fun h3 => ht ⟨le_of_lt (not_le.mp h), h3⟩))
    exact Or.inr (by simp [localisedArc, h0])

end Work.Whitney.CutPush
