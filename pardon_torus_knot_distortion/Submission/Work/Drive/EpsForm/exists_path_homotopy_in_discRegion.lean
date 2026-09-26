import Mathlib
import Submission.Work.SurgeryInvariance.Defs

/-!
# Homotoping a path inside an embedded disc region

Let `D` be an embedded disc of the torus `F = P.carrier`
(`Work.SurgeryInvariance.DiscRegion`) and let `Φ` be a continuous section of `D.e` over its
range (`D.e (Φ x) = x`); in other words `D.carrier = range D.e` is homeomorphic to the closed
unit disc of `ℂ`, hence contractible (it is a convex set).

Given two continuous paths `c`, `d : ℝ → ℝ³` whose restrictions to `[u,v]` lie in `D.carrier`
and which agree at `u`, at `v` and outside `[u,v]`, we produce a homotopy `H` from `c` to `d`
which

* is jointly continuous,
* stays inside `D.carrier` over `[u,v]`,
* is constant in `s` at the two endpoints `u`, `v`,
* leaves the values outside `[u,v]` untouched.

The construction is the straight-line homotopy in the disc: the points `c t` and `d t`
(`t ∈ [u,v]`) are sent to the disc by `Φ` and joined by the segment
`(1-σ) • Φ (c t) + σ • Φ (d t)`, which stays in the (convex) unit disc; `D.e` pushes the result
back to `ℝ³`.  The parameter `σ` is the projection of `s` onto `[0,1]`, so that the homotopy is
defined for *every* real `s` and always stays inside the disc, while `σ 0 = 0`, `σ 1 = 1` give
the two ends.  The path parameter `t` is clamped to `[u,v]` before applying `Φ` (`Φ` is only
defined on `D.carrier`), which makes the disc-part of the formula globally continuous; the
piecewise definition is then continuous because the two branches agree on the frontier
`{t = u} ∪ {t = v}` of `[u,v]`.
-/

open Set

namespace Work.Drive.EpsForm

/-- Projection of `ℝ` onto the interval `[0,1]`. -/
def hpathClamp01 (s : ℝ) : ℝ := min (max s 0) 1

/-- Projection of `ℝ` onto the interval `[u,v]` of the path parameter. -/
def hpathClampIcc (u v t : ℝ) : ℝ := min (max t u) v

theorem continuous_hpathClamp01 : Continuous hpathClamp01 :=
  (continuous_id.max continuous_const).min continuous_const

theorem hpathClamp01_mem (s : ℝ) : hpathClamp01 s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

@[simp] theorem hpathClamp01_zero : hpathClamp01 0 = 0 := by simp [hpathClamp01]

@[simp] theorem hpathClamp01_one : hpathClamp01 1 = 1 := by simp [hpathClamp01]

theorem continuous_hpathClampIcc (u v : ℝ) : Continuous (hpathClampIcc u v) :=
  (continuous_id.max continuous_const).min continuous_const

theorem hpathClampIcc_mem {u v : ℝ} (huv : u ≤ v) (t : ℝ) :
    hpathClampIcc u v t ∈ Set.Icc u v :=
  ⟨le_min (le_max_right _ _) huv, min_le_right _ _⟩

theorem hpathClampIcc_eq_left {u v : ℝ} (huv : u ≤ v) : hpathClampIcc u v u = u := by
  simp [hpathClampIcc, min_eq_left huv]

theorem hpathClampIcc_eq_right {u v : ℝ} (huv : u ≤ v) : hpathClampIcc u v v = v := by
  simp [hpathClampIcc, max_eq_left huv]

theorem hpathClampIcc_id {u v t : ℝ} (ht : t ∈ Set.Icc u v) : hpathClampIcc u v t = t := by
  simp [hpathClampIcc, max_eq_left ht.1, min_eq_left ht.2]

/-- A pair of points of `[0,1]` is joined by the segment to any point of the unit disc; the
segment stays in the (convex) unit disc. -/
theorem lineMap_mem_closedBall_one (q r : ℂ) (hq : q ∈ Metric.closedBall (0 : ℂ) 1)
    (hr : r ∈ Metric.closedBall (0 : ℂ) 1) (σ : ℝ) (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    (1 - σ) • q + σ • r ∈ Metric.closedBall (0 : ℂ) 1 := by
  have h := (convex_closedBall (0 : ℂ) 1).lineMap_mem hq hr hσ
  simpa only [AffineMap.lineMap_apply_module] using h

theorem exists_path_homotopy_in_discRegion {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P)
    (Φ : C(↥(Set.range D.e), Metric.closedBall (0 : ℂ) 1))
    (hΦ : ∀ x : ↥(Set.range D.e), D.e (Φ x) = (x : LeanEval.KnotTheory.PardonDistortion.R3))
    {u v : ℝ} (huv : u ≤ v)
    {c d : ℝ → LeanEval.KnotTheory.PardonDistortion.R3} (hc : Continuous c) (hd : Continuous d)
    (hcmem : ∀ t ∈ Set.Icc u v, c t ∈ D.carrier) (hdmem : ∀ t ∈ Set.Icc u v, d t ∈ D.carrier)
    (hcu : c u = d u) (hcv : c v = d v)
    (hcd : ∀ t : ℝ, t ∉ Set.Icc u v → c t = d t) :
    ∃ H : ℝ → ℝ → LeanEval.KnotTheory.PardonDistortion.R3, Continuous (Function.uncurry H) ∧
      (∀ s t, t ∈ Set.Icc u v → H s t ∈ D.carrier) ∧
      (∀ t, H 0 t = c t) ∧ (∀ t, H 1 t = d t) ∧
      (∀ s, H s u = c u ∧ H s v = c v) ∧
      (∀ s t, t ∉ Set.Icc u v → H s t = c t) := by
  classical
  -- the two clamped paths, as maps into the disc `range D.e`
  let A : ℝ → ↥(Set.range D.e) :=
    fun t => ⟨c (hpathClampIcc u v t), hcmem _ (hpathClampIcc_mem huv t)⟩
  let B : ℝ → ↥(Set.range D.e) :=
    fun t => ⟨d (hpathClampIcc u v t), hdmem _ (hpathClampIcc_mem huv t)⟩
  have hA : Continuous A :=
    Continuous.subtype_mk (hc.comp (continuous_hpathClampIcc u v))
      (fun t => hcmem _ (hpathClampIcc_mem huv t))
  have hB : Continuous B :=
    Continuous.subtype_mk (hd.comp (continuous_hpathClampIcc u v))
      (fun t => hdmem _ (hpathClampIcc_mem huv t))
  have hΦA : Continuous fun t : ℝ => ((Φ (A t)) : ℂ) :=
    continuous_subtype_val.comp (Φ.continuous.comp hA)
  have hΦB : Continuous fun t : ℝ => ((Φ (B t)) : ℂ) :=
    continuous_subtype_val.comp (Φ.continuous.comp hB)
  -- the straight-line homotopy in the disc, as a map into the closed unit disc
  have hzmem : ∀ p : ℝ × ℝ,
      (1 - hpathClamp01 p.1) • ((Φ (A p.2)) : ℂ) + hpathClamp01 p.1 • ((Φ (B p.2)) : ℂ)
        ∈ Metric.closedBall (0 : ℂ) 1 :=
    fun p => lineMap_mem_closedBall_one _ _ (Φ (A p.2)).2 (Φ (B p.2)).2 _
      (hpathClamp01_mem p.1)
  let z : ℝ × ℝ → Metric.closedBall (0 : ℂ) 1 := fun p =>
    ⟨(1 - hpathClamp01 p.1) • ((Φ (A p.2)) : ℂ) + hpathClamp01 p.1 • ((Φ (B p.2)) : ℂ),
      hzmem p⟩
  have hzval : Continuous fun p : ℝ × ℝ =>
      (1 - hpathClamp01 p.1) • ((Φ (A p.2)) : ℂ) + hpathClamp01 p.1 • ((Φ (B p.2)) : ℂ) :=
    ((continuous_const.sub (continuous_hpathClamp01.comp continuous_fst)).smul
        (hΦA.comp continuous_snd)).add
      ((continuous_hpathClamp01.comp continuous_fst).smul (hΦB.comp continuous_snd))
  have hz : Continuous z := Continuous.subtype_mk hzval hzmem
  have hzcont : Continuous fun p : ℝ × ℝ => D.e (z p) := Continuous.comp D.e.continuous hz
  -- the frontier of `{t ∈ [u,v]}` consists of the two endpoints
  have hfront : frontier {p : ℝ × ℝ | p.2 ∈ Set.Icc u v} =
      {p : ℝ × ℝ | p.2 = u} ∪ {p : ℝ × ℝ | p.2 = v} := by
    have h1 : (Prod.snd : ℝ × ℝ → ℝ) ⁻¹' Set.Icc u v = {p : ℝ × ℝ | p.2 ∈ Set.Icc u v} := rfl
    rw [← h1, ← IsOpenMap.preimage_frontier_eq_frontier_preimage isOpenMap_snd continuous_snd,
      frontier_Icc huv]
    ext p
    simp
  -- the two branches agree on the frontier
  have hfront_agree : ∀ p ∈ frontier {p : ℝ × ℝ | p.2 ∈ Set.Icc u v}, D.e (z p) = c p.2 := by
    intro p hp
    rw [hfront] at hp
    rcases hp with hp | hp
    · -- `p.2 = u`: the two clamped paths coincide there, so the segment is a point
      have hAB : A p.2 = B p.2 := by
        apply Subtype.ext
        show c (hpathClampIcc u v p.2) = d (hpathClampIcc u v p.2)
        rw [hp, hpathClampIcc_eq_left huv, hcu]
      have hz_eq : z p = Φ (A p.2) := by
        apply Subtype.ext
        show (1 - hpathClamp01 p.1) • ((Φ (A p.2)) : ℂ) + hpathClamp01 p.1 • ((Φ (B p.2)) : ℂ)
          = ((Φ (A p.2)) : ℂ)
        rw [show ((Φ (B p.2)) : ℂ) = ((Φ (A p.2)) : ℂ) from by rw [hAB],
          ← add_smul, sub_add_cancel, one_smul]
      calc D.e (z p) = (A p.2 : LeanEval.KnotTheory.PardonDistortion.R3) := by rw [hz_eq, hΦ]
        _ = c (hpathClampIcc u v p.2) := rfl
        _ = c u := by rw [hp, hpathClampIcc_eq_left huv]
        _ = c p.2 := by rw [hp]
    · -- `p.2 = v`
      have hAB : B p.2 = A p.2 := by
        apply Subtype.ext
        show d (hpathClampIcc u v p.2) = c (hpathClampIcc u v p.2)
        rw [hp, hpathClampIcc_eq_right huv, hcv]
      have hz_eq : z p = Φ (B p.2) := by
        apply Subtype.ext
        show (1 - hpathClamp01 p.1) • ((Φ (A p.2)) : ℂ) + hpathClamp01 p.1 • ((Φ (B p.2)) : ℂ)
          = ((Φ (B p.2)) : ℂ)
        rw [show ((Φ (A p.2)) : ℂ) = ((Φ (B p.2)) : ℂ) from by rw [hAB],
          ← add_smul, sub_add_cancel, one_smul]
      calc D.e (z p) = (B p.2 : LeanEval.KnotTheory.PardonDistortion.R3) := by rw [hz_eq, hΦ]
        _ = d (hpathClampIcc u v p.2) := rfl
        _ = d v := by rw [hp, hpathClampIcc_eq_right huv]
        _ = c p.2 := by rw [hp, ← hcv]
  -- the glued homotopy
  let Hf : ℝ × ℝ → LeanEval.KnotTheory.PardonDistortion.R3 :=
    fun p => if p.2 ∈ Set.Icc u v then D.e (z p) else c p.2
  have hHcont : Continuous Hf := by
    apply continuous_if (f := fun p : ℝ × ℝ => D.e (z p)) (g := fun p : ℝ × ℝ => c p.2)
      (p := fun p : ℝ × ℝ => p.2 ∈ Set.Icc u v)
    · exact hfront_agree
    · exact hzcont.continuousOn
    · exact (hc.comp continuous_snd).continuousOn
  refine ⟨fun s t => Hf (s, t), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : Function.uncurry (fun s t : ℝ => Hf (s, t)) = Hf := by funext p; rfl
    rw [h]; exact hHcont
  · intro s t ht
    dsimp only
    show Hf (s, t) ∈ D.carrier
    rw [show Hf (s, t) = D.e (z (s, t)) from if_pos ht]
    exact ⟨z (s, t), rfl⟩
  · intro t
    dsimp only
    by_cases ht : t ∈ Set.Icc u v
    · rw [show Hf (0, t) = D.e (z (0, t)) from if_pos ht]
      have hz0 : z (0, t) = Φ (A t) := by
        apply Subtype.ext
        show (1 - hpathClamp01 0) • ((Φ (A t)) : ℂ) + hpathClamp01 0 • ((Φ (B t)) : ℂ)
          = ((Φ (A t)) : ℂ)
        simp
      rw [hz0, hΦ]
      show c (hpathClampIcc u v t) = c t
      rw [hpathClampIcc_id ht]
    · rw [show Hf (0, t) = c t from if_neg ht]
  · intro t
    dsimp only
    by_cases ht : t ∈ Set.Icc u v
    · rw [show Hf (1, t) = D.e (z (1, t)) from if_pos ht]
      have hz1 : z (1, t) = Φ (B t) := by
        apply Subtype.ext
        show (1 - hpathClamp01 1) • ((Φ (A t)) : ℂ) + hpathClamp01 1 • ((Φ (B t)) : ℂ)
          = ((Φ (B t)) : ℂ)
        simp
      rw [hz1, hΦ]
      show d (hpathClampIcc u v t) = d t
      rw [hpathClampIcc_id ht]
    · rw [show Hf (1, t) = c t from if_neg ht, hcd t ht]
  · intro s
    dsimp only
    constructor
    · have hu : u ∈ Set.Icc u v := Set.left_mem_Icc.mpr huv
      rw [show Hf (s, u) = D.e (z (s, u)) from if_pos hu]
      have hAB : A u = B u := by
        apply Subtype.ext
        show c (hpathClampIcc u v u) = d (hpathClampIcc u v u)
        rw [hpathClampIcc_eq_left huv, hcu]
      have hzu : z (s, u) = Φ (A u) := by
        apply Subtype.ext
        show (1 - hpathClamp01 s) • ((Φ (A u)) : ℂ) + hpathClamp01 s • ((Φ (B u)) : ℂ)
          = ((Φ (A u)) : ℂ)
        rw [show ((Φ (B u)) : ℂ) = ((Φ (A u)) : ℂ) from by rw [hAB],
          ← add_smul, sub_add_cancel, one_smul]
      calc D.e (z (s, u)) = (A u : LeanEval.KnotTheory.PardonDistortion.R3) := by rw [hzu, hΦ]
        _ = c (hpathClampIcc u v u) := rfl
        _ = c u := by rw [hpathClampIcc_eq_left huv]
    · have hv : v ∈ Set.Icc u v := Set.right_mem_Icc.mpr huv
      rw [show Hf (s, v) = D.e (z (s, v)) from if_pos hv]
      have hBA : B v = A v := by
        apply Subtype.ext
        show d (hpathClampIcc u v v) = c (hpathClampIcc u v v)
        rw [hpathClampIcc_eq_right huv, hcv]
      have hzv : z (s, v) = Φ (B v) := by
        apply Subtype.ext
        show (1 - hpathClamp01 s) • ((Φ (A v)) : ℂ) + hpathClamp01 s • ((Φ (B v)) : ℂ)
          = ((Φ (B v)) : ℂ)
        rw [show ((Φ (A v)) : ℂ) = ((Φ (B v)) : ℂ) from by rw [hBA],
          ← add_smul, sub_add_cancel, one_smul]
      calc D.e (z (s, v)) = (B v : LeanEval.KnotTheory.PardonDistortion.R3) := by rw [hzv, hΦ]
        _ = d (hpathClampIcc u v v) := rfl
        _ = d v := by rw [hpathClampIcc_eq_right huv]
        _ = c v := hcv.symm
  · intro s t ht
    dsimp only
    rw [show Hf (s, t) = c t from if_neg ht]

end Work.Drive.EpsForm
