/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# The Écalle coordinate of the local model (Hubbard–Schleicher §4)

For the local normal form `f(ζ) = ζ + (ζ² − a²)h(ζ)` of `Basic.lean`, with two
simple fixed points at `±a`, this file builds the *Écalle coordinate*

  `u(ζ) = log((ζ+a)/(ζ−a)) / (2a)`,

equivalently `ζ(u) = a·(e^{2au}+1)/(e^{2au}−1) = a·coth(a u)`.

Why this coordinate matters.  Write `s(u) = e^{2au}`.  Then

* the two fixed points `±a` correspond to `s = ∞` and `s = 0`, i.e. to the two
  ends `u = ±∞` of the coordinate;
* the cut `ℓ = [−a, a]` separating the incoming from the outgoing petal is the
  straight line `u = (log((1+t)/(1−t)) + πi)/(2a)`, `t ∈ (−1,1)`; for `a = iλ`
  this is the vertical line `Re u = π/(2λ)`;
* the *punctures* (ends of the Écalle cylinder) are at `u ∈ (πi/a)·ℤ`, with
  successive spacing `π/‖a‖`;
* `dζ/du = a² − ζ² = −(ζ² − a²)`, hence
  `f(ζ(u)) = ζ(u) − (dζ/du)(u)·h(ζ(u))`: in the `u`-coordinate the dynamics is a
  step of size `h(ζ(u)) ≈ 1`, i.e. *asymptotically the translation* `u ↦ u − 1`.

This last fact is the mechanism of the parabolic implosion ("the egg-beater") of
Hubbard–Schleicher §4; it is made quantitative in `Model.lean` and `Phase.lean`.
-/
import Submission.Work.Implosion.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion

open Complex

/-! ## The Möbius coordinate `m_a` and the multiplier coordinate `s` -/

/-- `m_a(ζ) = (ζ+a)/(ζ−a)`: the Möbius transformation with `a ↦ ∞`, `−a ↦ 0`,
`∞ ↦ 1`. -/
noncomputable def mobius (a ζ : ℂ) : ℂ := (ζ + a) / (ζ - a)

/-- The multiplier coordinate `s = e^{2au}` of the Écalle coordinate. -/
noncomputable def ecalE (a u : ℂ) : ℂ := Complex.exp (2 * a * u)

/-- The **Écalle point map** `ζ(u) = a·(s+1)/(s−1)` with `s = e^{2au}`, the inverse
of the Écalle coordinate. -/
noncomputable def ecalPt (a u : ℂ) : ℂ := a * (ecalE a u + 1) / (ecalE a u - 1)

/-- The **Écalle coordinate** `u(ζ) = log(m_a(ζ))/(2a)`. -/
noncomputable def ecalCoord (a ζ : ℂ) : ℂ := Complex.log (mobius a ζ) / (2 * a)

/-- The **Écalle height** of a point: the imaginary part in the Écalle coordinate.
Points of height zero form the *equator* (HS Lemma 2.3). -/
noncomputable def ecalleHeight (a ζ : ℂ) : ℝ := (ecalCoord a ζ).im

/-- The **Écalle phase** of a point: the real part in the Écalle coordinate, i.e.
the cylinder coordinate along which the transit map translates. -/
noncomputable def ecallePhase (a ζ : ℂ) : ℝ := (ecalCoord a ζ).re

/-- The complex hyperbolic cotangent `coth w = cosh w / sinh w`. -/
noncomputable def coth (w : ℂ) : ℂ := Complex.cosh w / Complex.sinh w

@[simp] theorem mobius_apply (a ζ : ℂ) : mobius a ζ = (ζ + a) / (ζ - a) := rfl

theorem mobius_left (a : ℂ) : mobius a a = 0 := by simp [mobius]

theorem mobius_right (a : ℂ) : mobius a (-a) = 0 := by simp [mobius]

theorem mobius_ne_zero_iff (a ζ : ℂ) : mobius a ζ ≠ 0 ↔ ζ ≠ -a ∧ ζ ≠ a := by
  constructor
  · intro h
    refine ⟨fun h1 => h ?_, fun h1 => h ?_⟩
    · rw [h1, mobius]; simp
    · rw [h1, mobius]; simp
  · rintro ⟨h1, h2⟩
    rw [mobius]
    exact div_ne_zero (fun h => h1 (by linear_combination h))
      (fun h => h2 (by linear_combination h))

/-! ## Basic identities -/

theorem ecalPt_apply (a u : ℂ) :
    ecalPt a u = a * (ecalE a u + 1) / (ecalE a u - 1) := rfl

/-- `ζ(u) + a = 2a·s/(s−1)`. -/
theorem ecalPt_add (a u : ℂ) (hs : ecalE a u ≠ 1) :
    ecalPt a u + a = 2 * a * ecalE a u / (ecalE a u - 1) := by
  have hd : ecalE a u - 1 ≠ 0 := sub_ne_zero.mpr hs
  simp only [ecalPt]
  field_simp
  try ring

/-- `ζ(u) − a = 2a/(s−1)`. -/
theorem ecalPt_sub (a u : ℂ) (hs : ecalE a u ≠ 1) :
    ecalPt a u - a = 2 * a / (ecalE a u - 1) := by
  have hd : ecalE a u - 1 ≠ 0 := sub_ne_zero.mpr hs
  simp only [ecalPt]
  field_simp
  try ring

/-- The fundamental identity: `m_a(ζ(u)) = e^{2au}`. -/
theorem mobius_ecalPt (a u : ℂ) (ha : a ≠ 0) (hs : ecalE a u ≠ 1) :
    mobius a (ecalPt a u) = ecalE a u := by
  have hd : ecalE a u - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [mobius, ecalPt_add a u hs, ecalPt_sub a u hs]
  field_simp
  try ring

/-- `ecalPt` inverts `ecalCoord`. -/
theorem ecalPt_ecalCoord (a ζ : ℂ) (ha : a ≠ 0) (h1 : ζ ≠ a) (h2 : ζ ≠ -a) :
    ecalPt a (ecalCoord a ζ) = ζ := by
  have hnum : ζ + a ≠ 0 := fun h => h2 (by linear_combination h)
  have hden : ζ - a ≠ 0 := fun h => h1 (by linear_combination h)
  have hm : mobius a ζ ≠ 0 := by
    rw [mobius]; exact div_ne_zero hnum hden
  have hm1 : mobius a ζ - 1 ≠ 0 := by
    intro h
    have hh : ζ + a = ζ - a := by
      rw [mobius, sub_eq_zero, div_eq_one_iff_eq hden] at h
      exact h
    have hh2 : a = -a := add_left_cancel_iff.1 hh
    have hsum : a + a = 0 := eq_neg_iff_add_eq_zero.1 hh2
    have ha2 : (2 : ℂ) * a = 0 := by rw [two_mul]; exact hsum
    exact ha ((mul_eq_zero.1 ha2).resolve_left two_ne_zero)
  have h2a : 2 * a * (Complex.log (mobius a ζ) / (2 * a)) = Complex.log (mobius a ζ) := by
    rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ (by simp [ha])
  have key : a * (mobius a ζ + 1) / (mobius a ζ - 1) = ζ := by
    apply (div_eq_iff hm1).2
    rw [mobius]
    field_simp
    ring
  rw [ecalCoord]
  simp only [ecalPt, ecalE]
  rw [h2a, Complex.exp_log hm, key]

/-! ## Periodicity: the lattice `(πi/a)ℤ`, the punctures of the cylinder -/

/-- The **period lattice** of the Écalle coordinate: the poles of `ζ`, i.e. the
ends (punctures) of the Écalle cylinder. -/
def periodLattice (a : ℂ) : Set ℂ := {u | ecalE a u = 1}

theorem ecalPt_add_period (a u : ℂ) (ha : a ≠ 0) :
    ecalPt a (u + Real.pi * I / a) = ecalPt a u := by
  have harg : 2 * a * (u + Real.pi * I / a) = 2 * a * u + 2 * Real.pi * I := by
    field_simp
  have hexp : Complex.exp (2 * Real.pi * I) = 1 := by
    simpa only [Int.cast_one, one_mul] using Complex.exp_int_mul_two_pi_mul_I 1
  simp only [ecalPt, ecalE, harg, Complex.exp_add, hexp, mul_one]

theorem mem_periodLattice_iff (a u : ℂ) (ha : a ≠ 0) :
    u ∈ periodLattice a ↔ ∃ n : ℤ, u = n * (Real.pi * I / a) := by
  have h2a : (2 : ℂ) * a ≠ 0 := by simp [ha]
  constructor
  · intro h
    simp only [periodLattice, Set.mem_ofPred_eq, ecalE] at h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n, ?_⟩
    apply mul_left_cancel₀ h2a
    rw [hn]
    field_simp
  · rintro ⟨n, rfl⟩
    simp only [periodLattice, Set.mem_ofPred_eq, ecalE]
    rw [show 2 * a * (↑n * (↑Real.pi * I / a)) = ↑n * (2 * ↑Real.pi * I) by
      field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I n

/-- The punctures of the Écalle cylinder: the poles of `ζ`, i.e. the ends. -/
theorem ecalE_eq_one_iff (a u : ℂ) :
    ecalE a u = 1 ↔ u ∈ periodLattice a := Iff.rfl

/-! ## The cut in the Écalle coordinate -/

/-- The Möbius image of the cut: `m_a(t·a) = −(1+t)/(1−t)`. -/
theorem mobius_cutPt (a : ℂ) (t : ℝ) (ha : a ≠ 0) (ht : t ≠ 1) :
    mobius a (cutPt a t) = (((1 + t) / (1 - t) : ℝ) : ℂ) * (-1) := by
  have ht' : (t : ℂ) ≠ 1 := by exact_mod_cast ht
  have h1 : (1 - (t : ℂ)) ≠ 0 := by intro h; exact ht' (by linear_combination -h)
  have h2 : (t : ℂ) * a - a ≠ 0 := by
    intro h
    have h3 : ((t : ℂ) - 1) * a = 0 := by linear_combination h
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact ht' (by linear_combination h4)
    · exact ha h4
  rw [show (((1 + t) / (1 - t) : ℝ) : ℂ) = (1 + (t : ℂ)) / (1 - (t : ℂ)) by
    push_cast; ring, mobius, cutPt]
  field_simp
  try ring

/-- On the cut, the Écalle coordinate is the affine function
`u = (log((1+t)/(1−t)) + πi)/(2a)`: geometrically `ℓ` is a straight line in the
Écalle coordinate. -/
theorem ecalCoord_cutPt (a : ℂ) (t : ℝ) (ha : a ≠ 0) (ht : t ∈ Set.Ioo (-1:ℝ) 1) :
    ecalCoord a (cutPt a t)
      = ((Real.log ((1 + t) / (1 - t)) : ℂ) + Real.pi * I) / (2 * a) := by
  have ht1 : t ≠ 1 := ne_of_lt ht.2
  have hr : 0 < (1 + t) / (1 - t) := div_pos (by linarith [ht.1]) (by linarith [ht.2])
  have hm : mobius a (cutPt a t) = (((1 + t) / (1 - t) : ℝ) : ℂ) * (-1) :=
    mobius_cutPt a t ha ht1
  rw [ecalCoord, hm, Complex.log_ofReal_mul hr (by norm_num : (-1 : ℂ) ≠ 0),
    Complex.log_neg_one]

/-- The cut is the vertical line `Re u = π/(2λ)` when `a = iλ`, `λ > 0`. -/
theorem ecalCoord_cutPt_re (lam : ℝ) (hlam : 0 < lam) (t : ℝ)
    (ht : t ∈ Set.Ioo (-1:ℝ) 1) :
    (ecalCoord (lam * I) (cutPt (lam * I) t)).re = Real.pi / (2 * lam) := by
  have ha : (lam : ℂ) * I ≠ 0 := by simp [Complex.I_ne_zero, ne_of_gt hlam]
  rw [ecalCoord_cutPt (lam * I) t ha ht]
  have hD : 2 * ((lam : ℂ) * I) = ((2 * lam : ℝ) : ℂ) * I := by push_cast; ring
  rw [hD]
  have hnum : ((Real.log ((1 + t) / (1 - t)) : ℂ) + Real.pi * I)
      = ((Real.log ((1 + t) / (1 - t)) : ℝ) : ℂ) + ((Real.pi : ℝ) : ℂ) * I := by
    norm_num
  rw [hnum, Complex.div_re]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  norm_num
  field_simp
  try ring

end Work.Implosion
