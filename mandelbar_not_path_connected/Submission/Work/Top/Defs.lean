/-
# The plane-topology endgame of the mandelbar theorem: interfaces

This module sets up the abstract interface on which the endgame
(`Work.Top.not_isPathConnected_of_twoSidedPinch`) rests.  Nothing here uses dynamics:
`Mb` (the connectedness locus) and `Φ` (Nakane's parameter Böttcher coordinate) are
arbitrary, subject to the abstract interface `NakaneData`.

* `exteriorDisc` : the exterior `1 < ‖w‖` of the closed unit disc, the image of `Mbᶜ`
  under `Φ`;
* `potential Mb Φ` : the potential `log ‖Φ c‖` off `Mb`, extended by `0` on `Mb`;
* `NakaneData Mb Φ` : `Φ` is a homeomorphism `Mbᶜ ≃ₜ exteriorDisc`, zero on `Mb`, the
  potential is continuous and tends to `+∞` at infinity;
* `rayPt hN θ t` : the point of the parameter ray of angle `θ` at level `t > 1`;
* `paramRay hN θ` : the parameter ray of angle `θ`;
* `extAngle Φ c` : the external angle of `c`, i.e. the angle of `Φ c` normalized to `[0,1)`.
-/
import ChallengeDeps

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.Top

/-! ## The exterior of the unit disc -/

/-- The exterior of the closed unit disc, in the Böttcher coordinate. -/
def exteriorDisc : Set ℂ := {w : ℂ | 1 < ‖w‖}

@[simp] theorem mem_exteriorDisc {w : ℂ} : w ∈ exteriorDisc ↔ 1 < ‖w‖ := Iff.rfl

/-! ## The potential -/

/-- The potential of the family: `log ‖Φ c‖` off `Mb`, extended by `0` on `Mb`.  This is the
Green function of the parameter plane. -/
def potential (Mb : Set ℂ) (Φ : ℂ → ℂ) (c : ℂ) : ℝ := if c ∈ Mb then 0 else Real.log ‖Φ c‖

@[simp] theorem potential_of_mem {Mb : Set ℂ} {Φ : ℂ → ℂ} {c : ℂ} (hc : c ∈ Mb) :
    potential Mb Φ c = 0 := ite_eq_left hc

theorem potential_of_not_mem {Mb : Set ℂ} {Φ : ℂ → ℂ} {c : ℂ} (hc : c ∉ Mb) :
    potential Mb Φ c = Real.log ‖Φ c‖ := ite_eq_right hc

/-! ## The Nakane interface -/

/-- **Nakane's parameter Böttcher coordinate**, as an abstract interface.

* `e` is a homeomorphism from the complement of `Mb` onto the exterior of the unit disc;
* `Φ` agrees with `e` there, and `Φ = 0` on `Mb`;
* the potential `potential Mb Φ` is continuous on the whole plane and tends to `+∞` at
  infinity (Nakane's theorem: `Φ c / c → 1` as `c → ∞`). -/
structure NakaneData (Mb : Set ℂ) (Φ : ℂ → ℂ) where
  /-- the homeomorphism underlying `Φ`. -/
  e : ↥Mbᶜ ≃ₜ ↥exteriorDisc
  /-- `Φ` agrees with that homeomorphism off `Mb`. -/
  he : ∀ c : ↥Mbᶜ, Φ (c : ℂ) = ((e c : ↥exteriorDisc) : ℂ)
  /-- `Φ` vanishes on the connectedness locus. -/
  Phi_eq_zero_of_mem : ∀ c ∈ Mb, Φ c = 0
  /-- the potential is continuous on the whole plane. -/
  continuous_potential : Continuous (potential Mb Φ)
  /-- the potential tends to `+∞` at infinity. -/
  tendsto_potential : ∀ t : ℝ, ∃ R : ℝ, ∀ c : ℂ, R ≤ ‖c‖ → t ≤ potential Mb Φ c

namespace NakaneData

variable {Mb : Set ℂ} {Φ : ℂ → ℂ}

theorem Phi_mem_exteriorDisc (hN : NakaneData Mb Φ) {c : ℂ} (hc : c ∉ Mb) : 1 < ‖Φ c‖ := by
  rw [hN.he ⟨c, hc⟩]
  exact (hN.e ⟨c, hc⟩ : ↥exteriorDisc).2

theorem Phi_ne_zero (hN : NakaneData Mb Φ) {c : ℂ} (hc : c ∉ Mb) : Φ c ≠ 0 := by
  have h := hN.Phi_mem_exteriorDisc hc
  intro h0
  rw [h0, norm_zero] at h
  linarith

theorem mem_exteriorDisc_iff (hN : NakaneData Mb Φ) (c : ℂ) : Φ c ∈ exteriorDisc ↔ c ∉ Mb := by
  rw [mem_exteriorDisc]
  refine ⟨fun h hc => ?_, hN.Phi_mem_exteriorDisc⟩
  rw [hN.Phi_eq_zero_of_mem c hc, norm_zero] at h
  linarith

theorem potential_nonneg (hN : NakaneData Mb Φ) (c : ℂ) : 0 ≤ potential Mb Φ c := by
  rcases Classical.em (c ∈ Mb) with hc | hc
  · simp [hc]
  · rw [potential_of_not_mem hc]
    exact Real.log_nonneg (le_of_lt (hN.Phi_mem_exteriorDisc hc))

theorem potential_eq_zero_iff (hN : NakaneData Mb Φ) (c : ℂ) :
    potential Mb Φ c = 0 ↔ c ∈ Mb := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  by_contra hc
  rw [potential_of_not_mem hc] at h
  exact Real.log_ne_zero_of_pos_of_ne_one (lt_trans zero_lt_one (hN.Phi_mem_exteriorDisc hc))
    (ne_of_gt (hN.Phi_mem_exteriorDisc hc)) h

theorem potential_pos_iff (hN : NakaneData Mb Φ) (c : ℂ) : 0 < potential Mb Φ c ↔ c ∉ Mb := by
  constructor
  · intro h hc
    rw [(hN.potential_eq_zero_iff c).mpr hc] at h
    exact lt_irrefl 0 h
  · intro hc
    rw [potential_of_not_mem hc]
    exact Real.log_pos (hN.Phi_mem_exteriorDisc hc)

theorem isClosed_mb (hN : NakaneData Mb Φ) : IsClosed Mb := by
  have h : Mb = {c : ℂ | potential Mb Φ c = 0} := by
    ext c
    exact (hN.potential_eq_zero_iff c).symm
  rw [h]
  exact isClosed_eq hN.continuous_potential continuous_const

theorem isBounded_mb (hN : NakaneData Mb Φ) : Bornology.IsBounded Mb := by
  obtain ⟨R, hR⟩ := hN.tendsto_potential 1
  refine (Metric.isBounded_closedBall (x := (0:ℂ)) (r := max R 1)).subset ?_
  intro c hc
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  have h1 : max R 1 ≤ ‖c‖ := (not_le.mp hcon).le
  have h2 := hR c (le_trans (le_max_left R 1) h1)
  rw [(hN.potential_eq_zero_iff c).mpr hc] at h2
  linarith

theorem isCompact_mb (hN : NakaneData Mb Φ) : IsCompact Mb :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨hN.isClosed_mb, hN.isBounded_mb⟩

theorem isCompact_le_potential (hN : NakaneData Mb Φ) (t : ℝ) :
    IsCompact {c : ℂ | potential Mb Φ c ≤ t} := by
  obtain ⟨R, hR⟩ := hN.tendsto_potential (t + 1)
  have hclosed : IsClosed {c : ℂ | potential Mb Φ c ≤ t} :=
    isClosed_le hN.continuous_potential continuous_const
  have hbdd : Bornology.IsBounded {c : ℂ | potential Mb Φ c ≤ t} := by
    refine (Metric.isBounded_closedBall (x := (0:ℂ)) (r := max R 1)).subset ?_
    intro c hc
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hcon
    have h1 : max R 1 ≤ ‖c‖ := (not_le.mp hcon).le
    have h2 := hR c (le_trans (le_max_left R 1) h1)
    have h3 : potential Mb Φ c ≤ t := hc
    linarith
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩

theorem injOn_Phi (hN : NakaneData Mb Φ) : Set.InjOn Φ Mbᶜ := by
  intro c hc c' hc' h
  have h1 : ((hN.e ⟨c, hc⟩ : ↥exteriorDisc) : ℂ) = ((hN.e ⟨c', hc'⟩ : ↥exteriorDisc) : ℂ) := by
    rw [← hN.he ⟨c, hc⟩, ← hN.he ⟨c', hc'⟩, h]
  have h2 : hN.e ⟨c, hc⟩ = hN.e ⟨c', hc'⟩ := Subtype.ext h1
  have h3 := hN.e.injective h2
  simpa using congrArg (fun x : ↥Mbᶜ => (x : ℂ)) h3

theorem exists_Phi_eq (hN : NakaneData Mb Φ) {w : ℂ} (hw : w ∈ exteriorDisc) :
    ∃ c : ℂ, c ∉ Mb ∧ Φ c = w := by
  refine ⟨((hN.e.symm ⟨w, hw⟩ : ↥Mbᶜ) : ℂ), (hN.e.symm ⟨w, hw⟩ : ↥Mbᶜ).2, ?_⟩
  rw [hN.he, Homeomorph.apply_symm_apply]

/-! ## Parameter rays -/

/-- The normalized exponential `t * exp (2πiθ)`. -/
def rayPoint (θ t : ℝ) : ℂ := t * Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)

theorem norm_rayPoint (θ t : ℝ) : ‖rayPoint θ t‖ = |t| := by
  rw [rayPoint, Complex.norm_mul, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I).re = 0 := by simp
  rw [hre, Real.exp_zero, mul_one]
  simp

theorem rayPoint_mem_exteriorDisc {θ t : ℝ} (ht : 1 < t) : rayPoint θ t ∈ exteriorDisc := by
  rw [mem_exteriorDisc, norm_rayPoint, abs_of_pos (by linarith)]
  exact ht

/-- The point of the parameter ray of angle `θ` at level `t` (`t > 1`): the unique `c` with
`Φ c = t * exp (2πiθ)`.  For `t ≤ 1` it is set to `0`. -/
def rayPt (hN : NakaneData Mb Φ) (θ t : ℝ) : ℂ :=
  if h : 1 < t then ((hN.e.symm ⟨rayPoint θ t, rayPoint_mem_exteriorDisc h⟩ : ↥Mbᶜ) : ℂ)
  else 0

theorem rayPt_notMem (hN : NakaneData Mb Φ) {θ t : ℝ} (ht : 1 < t) : rayPt hN θ t ∉ Mb := by
  rw [rayPt, dite_eq_left ht]
  exact (hN.e.symm ⟨rayPoint θ t, rayPoint_mem_exteriorDisc ht⟩ : ↥Mbᶜ).2

theorem Phi_rayPt (hN : NakaneData Mb Φ) {θ t : ℝ} (ht : 1 < t) :
    Φ (rayPt hN θ t) = rayPoint θ t := by
  rw [rayPt, dite_eq_left ht, hN.he, Homeomorph.apply_symm_apply]

theorem potential_rayPt (hN : NakaneData Mb Φ) {θ t : ℝ} (ht : 1 < t) :
    potential Mb Φ (rayPt hN θ t) = Real.log t := by
  rw [potential_of_not_mem (hN.rayPt_notMem ht), hN.Phi_rayPt ht, norm_rayPoint,
    abs_of_pos (by linarith)]

/-- The **parameter ray** of angle `θ`. -/
def paramRay (hN : NakaneData Mb Φ) (θ : ℝ) : Set ℂ :=
  {c : ℂ | c ∉ Mb ∧ ∃ t : ℝ, 1 < t ∧ Φ c = rayPoint θ t}

theorem mem_paramRay_iff (hN : NakaneData Mb Φ) {θ : ℝ} {c : ℂ} :
    c ∈ paramRay hN θ ↔ c ∉ Mb ∧ ∃ t : ℝ, 1 < t ∧ Φ c = rayPoint θ t := Iff.rfl

theorem paramRay_subset_compl (hN : NakaneData Mb Φ) (θ : ℝ) : paramRay hN θ ⊆ Mbᶜ :=
  fun _ h => h.1

theorem paramRay_eq_range (hN : NakaneData Mb Φ) (θ : ℝ) :
    paramRay hN θ = Set.range fun t : {t : ℝ // 1 < t} => rayPt hN θ t.1 := by
  ext c
  constructor
  · rintro ⟨hc, t, ht, h⟩
    have : rayPt hN θ t = c :=
      hN.injOn_Phi (hN.rayPt_notMem ht) hc (by rw [hN.Phi_rayPt ht, h])
    exact ⟨⟨t, ht⟩, this⟩
  · rintro ⟨t, rfl⟩
    exact ⟨hN.rayPt_notMem t.2, t.1, t.2, hN.Phi_rayPt t.2⟩

/-! ## External angles -/

/-- The **external angle**: the angle of `Φ c`, normalized to `[0,1)`. -/
def extAngle (Φ : ℂ → ℂ) (c : ℂ) : ℝ := toIcoMod (p := (1 : ℝ)) one_pos 0 (Complex.arg (Φ c) / (2 * Real.pi))

theorem extAngle_mem_Ico (Φ : ℂ → ℂ) (c : ℂ) : extAngle Φ c ∈ Set.Ico (0 : ℝ) 1 := by
  simpa [extAngle] using
    toIcoMod_mem_Ico (p := (1 : ℝ)) one_pos 0 (Complex.arg (Φ c) / (2 * Real.pi))

theorem extAngle_nonneg (Φ : ℂ → ℂ) (c : ℂ) : 0 ≤ extAngle Φ c := (extAngle_mem_Ico Φ c).1

theorem extAngle_lt_one (Φ : ℂ → ℂ) (c : ℂ) : extAngle Φ c < 1 := (extAngle_mem_Ico Φ c).2

/-! ## The equipotential arc, the ray pieces and the rotation used for the local model -/

/-- The **equipotential arc** of level `R` between the angles `β₁` and `β₂`: the image of the
parameter rays of those angles, cut at level `R`. -/
def eqArc (hN : NakaneData Mb Φ) (β₁ β₂ R : ℝ) : Set ℂ :=
  Set.range fun s : Set.Icc β₁ β₂ => rayPt hN s.1 R

/-- The piece of the parameter ray of angle `β` between the levels `t₀` and `R`. -/
def rayPiece (hN : NakaneData Mb Φ) (β t₀ R : ℝ) : Set ℂ :=
  {c : ℂ | c ∈ paramRay hN β ∧ t₀ ≤ potential Mb Φ c ∧ potential Mb Φ c ≤ Real.log R}

theorem rayPiece_subset_paramRay {hN : NakaneData Mb Φ} {β t₀ R : ℝ} :
    rayPiece hN β t₀ R ⊆ paramRay hN β := fun _ h => h.1

theorem rayPiece_subset_ge {hN : NakaneData Mb Φ} {β t₀ R : ℝ} :
    rayPiece hN β t₀ R ⊆ {c : ℂ | t₀ ≤ potential Mb Φ c} := fun _ h => h.2.1

theorem rayPiece_subset_le {hN : NakaneData Mb Φ} {β t₀ R : ℝ} :
    rayPiece hN β t₀ R ⊆ {c : ℂ | potential Mb Φ c ≤ Real.log R} := fun _ h => h.2.2

end NakaneData
/-- The rotation of the Böttcher plane by `-2πθ`, used to bring a point of the circle
`‖w‖ = R` to the positive real axis. -/
def rayRot (θ : ℝ) (w : ℂ) : ℂ := w * Complex.exp (-(2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I))

@[simp] theorem rayRot_apply (θ : ℝ) (w : ℂ) :
    rayRot θ w = w * Complex.exp (-(2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)) := rfl

theorem norm_rayRot (θ : ℝ) (w : ℂ) : ‖rayRot θ w‖ = ‖w‖ := by
  rw [rayRot, norm_mul, Complex.norm_exp]
  have hre : (-(2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)).re = 0 := by simp
  rw [hre, Real.exp_zero, mul_one]

theorem rayRot_rayPoint (θ s : ℝ) :
    rayRot θ (NakaneData.rayPoint s 1) = Complex.exp (2 * Real.pi * (s - θ) * Complex.I) := by
  have h1 : ((1 : ℝ) : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * (s : ℂ) * Complex.I)
      = Complex.exp (2 * (Real.pi : ℂ) * (s : ℂ) * Complex.I) := by simp
  rw [rayRot, NakaneData.rayPoint, h1, ← Complex.exp_add]
  congr 1
  push_cast
  ring


end Work.Top
