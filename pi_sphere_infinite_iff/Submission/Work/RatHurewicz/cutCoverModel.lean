import Mathlib
import Submission.Work.RatHurewicz.thickCover

set_option synthInstance.maxHeartbeats 400000

/-!
# The model set of `coneDown`: convexity, non-emptiness, contractibility

Inside the model cell `D^{n+2} = cellDisk n`, the model set of the cut piece `coneDown` is

  `coneDownModel sr ε = {y | ‖y‖ < sr ∧ cellLast y + ε‖y‖ < 0}`,

the model ball of radius `sr` cut by the open cone `cellLast y + ε‖y‖ < 0`.  It is convex (the norm
term contributes at most its triangle-inequality defect), and it is non-empty when `0 < sr` and
`ε < 1` (the point `-(sr/2) • e_last` lies strictly below the cone).  Hence it is contractible.
-/

namespace Work.RatHurewicz

open scoped Topology

noncomputable section

/-- The **model set of `coneDown`**: the points of the model ball of radius `sr` strictly below the
open cone `cellLast y + ε‖y‖ < 0`. -/
def coneDownModel (n : ℕ) (sr ε : ℝ) : Set (CellVec n) :=
  {y | ‖y‖ < sr ∧ cellLast y + ε * ‖y‖ < 0}

/-- A unit vector whose last coordinate is `1` (the "south pole" direction used to witness the
non-emptiness of the cone below the equator). -/
def lastUnit (n : ℕ) : CellVec n :=
  (WithLp.equiv 2 (Fin (n+2) → ℝ)).symm (Pi.single (Fin.last (n+1)) 1)

@[simp] theorem norm_lastUnit (n : ℕ) : ‖lastUnit n‖ = 1 := by
  simp [lastUnit]

@[simp] theorem cellLast_lastUnit (n : ℕ) : cellLast (lastUnit n) = 1 := by
  simp [lastUnit, cellLast]

/-- `cellLast` is linear. -/
theorem cellLast_smul {n : ℕ} (c : ℝ) (y : CellVec n) : cellLast (c • y) = c * cellLast y := by
  simp [cellLast, Pi.smul_apply, smul_eq_mul]

/-- The point of the lower cone used to witness non-emptiness: `-(sr/2) • e_last`. -/
def coneWitness (n : ℕ) (sr : ℝ) : CellVec n := (-(sr/2)) • lastUnit n

theorem norm_coneWitness (n : ℕ) {sr : ℝ} (hsr : 0 ≤ sr) :
    ‖coneWitness n sr‖ = sr/2 := by
  have h : (0 : ℝ) ≤ sr/2 := by linarith
  simp only [coneWitness, norm_smul, norm_neg, Real.norm_of_nonneg h, norm_lastUnit, mul_one]

theorem cellLast_coneWitness (n : ℕ) (sr : ℝ) : cellLast (coneWitness n sr) = -(sr/2) := by
  rw [coneWitness, cellLast_smul, cellLast_lastUnit, mul_one]

/-- **The sublevel set of `y ↦ cellLast y + ε‖y‖` is convex** for `ε ≥ 0`. -/
theorem convex_coneLevel (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    Convex ℝ {y : CellVec n | cellLast y + ε * ‖y‖ < 0} := by
  intro x hx y hy a b ha hb hab
  show cellLast (a • x + b • y) + ε * ‖a • x + b • y‖ < 0
  have hlast : cellLast (a • x + b • y) = a * cellLast x + b * cellLast y := by
    simp [cellLast, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hnorm : ε * ‖a • x + b • y‖ ≤ a * (ε * ‖x‖) + b * (ε * ‖y‖) := by
    have h1 : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
      calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
        _ = a * ‖x‖ + b * ‖y‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    calc ε * ‖a • x + b • y‖ ≤ ε * (a * ‖x‖ + b * ‖y‖) := mul_le_mul_of_nonneg_left h1 hε
      _ = a * (ε * ‖x‖) + b * (ε * ‖y‖) := by ring
  rw [hlast]
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · -- `a = 0`: the convex combination is just `y`
    have hb1 : b = 1 := by linarith
    subst ha0
    subst hb1
    simpa using hy
  · have hA : a * (cellLast x + ε * ‖x‖) < 0 := mul_neg_of_pos_of_neg hapos hx
    have hB : b * (cellLast y + ε * ‖y‖) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hb (le_of_lt hy)
    have hP : a * (cellLast x + ε * ‖x‖) + b * (cellLast y + ε * ‖y‖) < 0 := by linarith
    have hle : a * cellLast x + b * cellLast y + ε * ‖a • x + b • y‖
        ≤ a * (cellLast x + ε * ‖x‖) + b * (cellLast y + ε * ‖y‖) := by linarith [hnorm]
    linarith [hP, hle]

/-- **The model set of `coneDown` is convex.** -/
theorem convex_coneDownModel (n : ℕ) (sr : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    Convex ℝ (coneDownModel n sr ε) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨?_, (convex_coneLevel n hε) hx2 hy2 ha hb hab⟩
  have h1 : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  refine lt_of_le_of_lt h1 ?_
  have hsum : a * sr + b * sr = sr := by rw [← add_mul, hab, one_mul]
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    rw [ha0, zero_mul, zero_add, hb1, one_mul]
    exact hy1
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hlt : a * ‖x‖ < a * sr := mul_lt_mul_of_pos_left hx1 hapos
    have hle : b * ‖y‖ ≤ b * sr := mul_le_mul_of_nonneg_left (le_of_lt hy1) hb
    linarith [hlt, hle, hsum]

/-- **The model set of `coneDown` is non-empty** for `0 < sr`, `ε < 1`. -/
theorem nonempty_coneDownModel (n : ℕ) {sr ε : ℝ} (hsr : 0 < sr) (hε1 : ε < 1) :
    (coneDownModel n sr ε).Nonempty := by
  refine ⟨coneWitness n sr, ?_, ?_⟩
  · rw [norm_coneWitness n (le_of_lt hsr)]; linarith
  · rw [cellLast_coneWitness, norm_coneWitness n (le_of_lt hsr)]
    nlinarith [hsr, hε1]

/-- **The model set of `coneDown` is contractible** for `0 < sr`, `0 ≤ ε`, `ε < 1`. -/
theorem contractibleSpace_coneDownModel (n : ℕ) {sr ε : ℝ} (hsr : 0 < sr) (hε : 0 ≤ ε)
    (hε1 : ε < 1) : ContractibleSpace ↥(coneDownModel n sr ε) :=
  (convex_coneDownModel n sr hε).contractibleSpace (nonempty_coneDownModel n hsr hε1)

/-- The **model set of `ballSlit`**: the model ball of radius `sr`, minus the closed truncated cone
`{ρ ≤ ‖y‖ ∧ cellLast y + η‖y‖ ≤ 0}`.  Unlike `coneDownModel` it is **not** convex (the slit opens
it), but it is still contractible: it splits radially into the full inner ball of radius `ρ` and the
shell outside the cone, and the shell retracts radially onto its inner boundary
`{‖y‖ = ρ, 0 < cellLast y + η‖y‖} ≅ ℝ^{n+1}`. -/
def ballSlitModel (n : ℕ) (ρ sr η : ℝ) : Set (CellVec n) :=
  {y | ‖y‖ < sr ∧ ¬ (ρ ≤ ‖y‖ ∧ cellLast y + η * ‖y‖ ≤ 0)}

/-- **Radial decomposition of the slitted ball.**  It is the union of the full inner ball
`{‖y‖ < ρ}` and the part of the shell `{ρ ≤ ‖y‖ < sr}` lying strictly above the cone
(`0 < cellLast y + η‖y‖`).  The two pieces are contractible with contractible intersection
(`{‖y‖ < ρ}` convex; the shell piece retracts radially onto the sphere piece, `≅ ℝ^{n+1}`). -/
theorem ballSlitModel_eq (n : ℕ) {ρ sr η : ℝ} (hρsr : ρ ≤ sr) :
    ballSlitModel n ρ sr η
      = {y : CellVec n | ‖y‖ < ρ}
        ∪ {y : CellVec n | ρ ≤ ‖y‖ ∧ ‖y‖ < sr ∧ 0 < cellLast y + η * ‖y‖} := by
  ext y
  simp only [ballSlitModel, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hρ : ρ ≤ ‖y‖
    · refine Or.inr ⟨hρ, h1, ?_⟩
      by_contra hc
      exact h2 ⟨hρ, not_lt.mp hc⟩
    · exact Or.inl (not_le.mp hρ)
  · rintro (h | ⟨hρ, h1, h2⟩)
    · exact ⟨lt_of_lt_of_le h hρsr, fun hc => (not_le.mpr h) hc.1⟩
    · exact ⟨h1, fun hc => absurd hc.2 (not_le.mpr h2)⟩

/-- **The cone function is positively homogeneous**: `s ↦ cellLast (c•y) + η‖c•y‖ = c·(cellLast y +
η‖y‖)` for `c > 0`.  This is what makes the *direction-preserving* radial moves of the contraction
of `ballSlitModel` stay inside the shell (`f_η > 0` is preserved) and inside its inner boundary. -/
theorem coneLevel_smul_pos {n : ℕ} {η : ℝ} {c : ℝ} (hc : 0 < c) (y : CellVec n) :
    cellLast (c • y) + η * ‖c • y‖ = c * (cellLast y + η * ‖y‖) := by
  rw [cellLast_smul, norm_smul, Real.norm_of_nonneg (le_of_lt hc)]
  ring

/-- A point of the shell outside the cone is in the slitted ball. -/
theorem mem_ballSlitModel_shell {n : ℕ} {ρ sr η : ℝ} {y : CellVec n} (hsr : ‖y‖ < sr)
    (hpos : 0 < cellLast y + η * ‖y‖) : y ∈ ballSlitModel n ρ sr η :=
  ⟨hsr, fun hc => absurd hc.2 (not_le.mpr hpos)⟩

/-- **The shell piece is preserved by the radial push to radius `ρ`**: for `y` in the shell
(`ρ ≤ ‖y‖`, `f_η y > 0`) and `c ≥ ρ`, the point `(c/‖y‖) • y` — same direction, radius `c` — is in
the slitted ball exactly when `c < sr`.  Its cone value is positive throughout (`f_η` is positively
homogeneous), which is what lets the contraction push the shell radially to radius `ρ`. -/
theorem ballSlitModel_radial_mem {n : ℕ} {ρ sr η c : ℝ} {y : CellVec n} (hρ : 0 < ρ)
    (hyρ : ρ ≤ ‖y‖) (hypos : 0 < cellLast y + η * ‖y‖) (hcρ : ρ ≤ c) :
    ((c / ‖y‖) • y) ∈ ballSlitModel n ρ sr η ↔ c < sr := by
  have hyn : 0 < ‖y‖ := lt_of_lt_of_le hρ hyρ
  have hcmul : 0 < c / ‖y‖ := div_pos (lt_of_lt_of_le hρ hcρ) hyn
  have hnorm : ‖(c / ‖y‖) • y‖ = c := by
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt hcmul)]
    field_simp
  constructor
  · intro h
    have h1 := h.1
    rwa [hnorm] at h1
  · intro hc
    refine mem_ballSlitModel_shell (y := (c / ‖y‖) • y) (by rw [hnorm]; exact hc) ?_
    rw [coneLevel_smul_pos hcmul]
    exact mul_pos hcmul hypos

/-- **The first stage of the contraction, at `c = ρ`.**  A point `y` of the shell
(`ρ ≤ ‖y‖ < sr`, `f_η y > 0`) pushed radially to radius `ρ` lands on the inner boundary sphere
`{‖·‖ = ρ}`, still in the slitted ball and still strictly above the cone.  This is the endpoint of
the first stage of the contraction of `ballSlitModel`: the shell retracts radially onto its inner
boundary, and `ballSlitModel_radial_mem` at `c = ρ` is exactly what says the move stays inside. -/
theorem ballSlitModel_radial_zero {n : ℕ} {ρ sr η : ℝ} {y : CellVec n} (hρ : 0 < ρ)
    (hyρ : ρ ≤ ‖y‖) (hypos : 0 < cellLast y + η * ‖y‖) (hsr : ‖y‖ < sr) :
    ‖(ρ / ‖y‖) • y‖ = ρ ∧
      ((ρ / ‖y‖) • y) ∈ ballSlitModel n ρ sr η ∧
      0 < cellLast ((ρ / ‖y‖) • y) + η * ‖(ρ / ‖y‖) • y‖ := by
  have hyn : 0 < ‖y‖ := lt_of_lt_of_le hρ hyρ
  have hcmul : 0 < ρ / ‖y‖ := div_pos hρ hyn
  have hnorm : ‖(ρ / ‖y‖) • y‖ = ρ := by
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt hcmul)]
    field_simp
  refine ⟨hnorm, ?_, ?_⟩
  · exact (ballSlitModel_radial_mem hρ hyρ hypos le_rfl).mpr (lt_of_le_of_lt hyρ hsr)
  · rw [coneLevel_smul_pos hcmul]
    exact mul_pos hcmul hypos

/-!
## Wiring `ContractibleSpace ↥(ballSlitModel n ρ sr η)` (lump 1): the anchor is *not* `{‖y‖ ≤ ρ}`

All ingredients are now on disk: `coneLevel_smul_pos`, `ballSlitModel_radial_mem`,
`ballSlitModel_radial_zero` (stages one and two) and `contractibleSpace_sphereSilt`
(`Submission/Work/RatHurewicz/contractibleSpace_sphereSilt.lean`, `0 < ρ`, `|η| < 1`).

**Correction found while wiring.**  The shell retracts onto the sphere piece
`{‖y‖ = ρ, 0 < cellLast y + η‖y‖}`, but that sphere piece is `ballSlitModel ∩ {‖y‖ = ρ}` — *not*
all of `{‖y‖ = ρ}`: the slit `{ρ ≤ ‖y‖ ∧ cellLast y + η‖y‖ ≤ 0}` also removes the points of the
ρ-sphere below the cone.  So the decomposition of `ballSlitModel` to use is the radial cut

  `A := ballSlitModel ∩ {‖y‖ ≤ ρ}`,  `B := ballSlitModel ∩ {ρ ≤ ‖y‖}`,

with `A = {‖y‖ < ρ} ∪ {‖y‖ = ρ, 0 < cellLast y + η‖y‖}` (contractible: it deformation retracts
radially to `0`, the removed boundary cap being no obstruction), `B = {ρ ≤ ‖y‖ < sr, 0 < f_η}`
(contractible: it retracts radially onto the sphere piece by `ballSlitModel_radial_mem` at
`c = (1-t)‖y‖ + tρ`, and the sphere piece is contractible by `contractibleSpace_sphereSilt`), and
`A ∩ B` exactly the sphere piece.  The *un*anchored union `{‖y‖ ≤ ρ} ∪ B` is **not** the model set
(they differ on the closed cap of the ρ-sphere), which is why the naive `≤`-version of
`ballSlitModel_eq` cannot be used for the gluing.
-/

end

end Work.RatHurewicz
