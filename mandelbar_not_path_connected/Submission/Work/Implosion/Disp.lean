/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# The `u`-model of parabolic implosion: the displacement formula

Let `f(ζ) = ζ + (ζ² − a²)h(ζ)` be the local normal form with fixed points `±a` and
let `ζ(u) = a·coth(a u)` be the Écalle coordinate of `Ecalle.lean`.  This file
describes, *exactly*, the map induced by `f` in the `u`-coordinate and proves the
quantitative estimate showing that it is the translation `u ↦ u − 1` up to
`O(‖a‖ + ε)`.

Write `G(u) = u(f(ζ(u)))`, the `u`-coordinate of `f(ζ(u))`.  Two exact identities
drive everything.

* **Factorisation.**  `f(ζ) − a = (ζ−a)(1 + (ζ+a)h(ζ))` and
  `f(ζ) + a = (ζ+a)(1 + (ζ−a)h(ζ))`, hence for `A₁ = (ζ−a)h(ζ)`,
  `A₂ = (ζ+a)h(ζ)`,

    `m_a(f(ζ)) = m_a(ζ) · (1+A₁)/(1+A₂)`.

* **Multiplier form.**  Since `e^{2aG(u)} = m_a(f(ζ(u)))` and `e^{2au} = m_a(ζ(u))`,

    `e^{2aG(u)} = e^{2au} · (1+A₁)/(1+A₂)`.

Taking logarithms gives the **displacement**

    `Φ(u) := (log(1+A₁) − log(1+A₂))/(2a)`,  so that  `e^{2a(u+Φ(u))} = e^{2aG(u)}`,

i.e. `G(u) ≡ u + Φ(u)` modulo the period lattice `(πi/a)ℤ` — which is exactly the
Écalle cylinder.  Finally `A₁ − A₂ = −2a·h(ζ(u))`, so the logarithm bounds of
Mathlib give

    `‖Φ(u) + h(ζ(u))‖ ≤ (‖A₁‖² + ‖A₂‖²)/(2‖a‖)`,

and with `‖h − 1‖ ≤ ε` on `‖ζ‖ ≤ ρ` this is `‖Φ(u) + 1‖ ≤ ε + O((ρ+‖a‖)²/‖a‖)`,
which is `O(‖a‖)` in the regime `ρ ≲ ‖a‖`.  This is the parabolic implosion: the
dynamics becomes the translation `u ↦ u − 1`.
-/
import Submission.Work.Implosion.Ecalle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion

open Complex

/-! ## The induced map and the displacement -/

/-- The map induced by the normal form `f` on the Écalle coordinate:
`G(u) = u(f(ζ(u)))`. -/
noncomputable def modelMap (a : ℂ) (h : ℂ → ℂ) (u : ℂ) : ℂ :=
  ecalCoord a (normalForm a h (ecalPt a u))

/-- The numerator perturbation `A₁ = (ζ−a)·h(ζ)`. -/
noncomputable def dispNum1 (a : ℂ) (h : ℂ → ℂ) (u : ℂ) : ℂ :=
  (ecalPt a u - a) * h (ecalPt a u)

/-- The denominator perturbation `A₂ = (ζ+a)·h(ζ)`. -/
noncomputable def dispNum2 (a : ℂ) (h : ℂ → ℂ) (u : ℂ) : ℂ :=
  (ecalPt a u + a) * h (ecalPt a u)

/-- The **displacement** of the Écalle coordinate in one iterate:
`Φ(u) = (log(1+A₁) − log(1+A₂))/(2a)`.  It satisfies `e^{2a(u+Φ(u))} = e^{2a·G(u)}`,
so `G(u) = u + Φ(u)` in the Écalle cylinder `ℂ/(πi/a)ℤ`. -/
noncomputable def modelDisp (a : ℂ) (h : ℂ → ℂ) (u : ℂ) : ℂ :=
  (Complex.log (1 + dispNum1 a h u) - Complex.log (1 + dispNum2 a h u)) / (2 * a)

/-! ## The exact identities -/

/-- `A₁ − A₂ = −2a·h(ζ(u))`. -/
theorem dispNum1_sub_dispNum2 (a : ℂ) (h : ℂ → ℂ) (u : ℂ) :
    dispNum1 a h u - dispNum2 a h u = -2 * a * h (ecalPt a u) := by
  simp only [dispNum1, dispNum2]; ring

/-- The factorisation of the normal form in the Écalle coordinate: the exact
`m`-coordinate relation.  This is the combinatorial heart of the implosion. -/
theorem mobius_normalForm (a : ℂ) (h : ℂ → ℂ) (ζ : ℂ) (h1 : ζ ≠ a)
    (h2 : 1 + (ζ + a) * h ζ ≠ 0) :
    mobius a (normalForm a h ζ)
      = mobius a ζ * ((1 + (ζ - a) * h ζ) / (1 + (ζ + a) * h ζ)) := by
  have hden : normalForm a h ζ - a ≠ 0 := by
    rw [normalForm_sub_left]
    exact mul_ne_zero (sub_ne_zero.mpr h1) h2
  rw [mobius, normalForm_add_left, normalForm_sub_left, mobius]
  field_simp
  try ring

/-- The exact multiplier identity: `e^{2aG(u)} = e^{2au}·(1+A₁)/(1+A₂)`. -/
theorem ecalE_modelMap (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ha : a ≠ 0)
    (hs : ecalE a u ≠ 1) (h1 : ecalPt a u ≠ a) (h2 : 1 + dispNum2 a h u ≠ 0)
    (h3 : mobius a (normalForm a h (ecalPt a u)) ≠ 0) :
    ecalE a (modelMap a h u)
      = ecalE a u * ((1 + dispNum1 a h u) / (1 + dispNum2 a h u)) := by
  have hkey : 2 * a * (Complex.log (mobius a (normalForm a h (ecalPt a u))) / (2 * a))
      = Complex.log (mobius a (normalForm a h (ecalPt a u))) := by
    rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ (by simp [ha])
  have hm : mobius a (normalForm a h (ecalPt a u))
      = mobius a (ecalPt a u) * ((1 + dispNum1 a h u) / (1 + dispNum2 a h u)) := by
    rw [dispNum1, dispNum2]
    exact mobius_normalForm a h (ecalPt a u) h1 h2
  have hmult : mobius a (ecalPt a u) = ecalE a u := mobius_ecalPt a u ha hs
  rw [modelMap, ecalCoord, ecalE, hkey, Complex.exp_log h3, hm, hmult]

/-- The exact multiplier identity for the explicit displacement. -/
theorem ecalE_add_modelDisp (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ha : a ≠ 0)
    (h2 : 1 + dispNum2 a h u ≠ 0) (h1 : 1 + dispNum1 a h u ≠ 0) :
    ecalE a (u + modelDisp a h u)
      = ecalE a u * ((1 + dispNum1 a h u) / (1 + dispNum2 a h u)) := by
  have hdecomp : 2 * a * (u + modelDisp a h u)
      = 2 * a * u + (Complex.log (1 + dispNum1 a h u) - Complex.log (1 + dispNum2 a h u)) := by
    rw [modelDisp]
    field_simp
    try ring
  rw [ecalE, hdecomp, Complex.exp_add]
  congr 1
  rw [sub_eq_add_neg, Complex.exp_add, Complex.exp_neg, Complex.exp_log h1, Complex.exp_log h2]
  field_simp
  try ring

/-- **The exact relation between the model map and the displacement**: they agree
modulo the period lattice `(πi/a)ℤ` of the Écalle cylinder. -/
theorem modelMap_eq_modelDisp_add_lattice (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ha : a ≠ 0)
    (hs : ecalE a u ≠ 1) (h1 : ecalPt a u ≠ a) (h2 : 1 + dispNum2 a h u ≠ 0)
    (h3 : mobius a (normalForm a h (ecalPt a u)) ≠ 0)
    (h4 : 1 + dispNum1 a h u ≠ 0) :
    ∃ k : ℤ, modelMap a h u = u + modelDisp a h u + k * (Real.pi * I / a) := by
  have heq : ecalE a (modelMap a h u) = ecalE a (u + modelDisp a h u) := by
    rw [ecalE_modelMap a h u ha hs h1 h2 h3, ecalE_add_modelDisp a h u ha h2 h4]
  simp only [ecalE] at heq
  rw [Complex.exp_eq_exp_iff_exists_int] at heq
  obtain ⟨n, hn⟩ := heq
  -- 2*a*x = 2*a*y + n*(2πI)  ⟹  x = y + n*(πI/a)
  have h2a : (2 : ℂ) * a ≠ 0 := by simp [ha]
  refine ⟨n, ?_⟩
  have : 2 * a * (modelMap a h u) = 2 * a * (u + modelDisp a h u + ↑n * (Real.pi * I / a)) := by
    rw [mul_add, hn]
    field_simp
    try ring
  exact mul_left_cancel₀ h2a this

/-! ## The quantitative estimate -/

/-- **Logarithm bound.**  `‖log(1+z) − z‖ ≤ ‖z‖²` for `‖z‖ ≤ 1/2`. -/
theorem norm_log_one_add_sub_self_le_of_le_half {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (1 + z) - z‖ ≤ ‖z‖ ^ 2 := by
  have hlt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  refine (Complex.norm_log_one_add_sub_self_le hlt).trans ?_
  have h1 : 0 < 1 - ‖z‖ := by linarith
  have h2 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ h1 (by norm_num)]; linarith
  calc ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 * 2 / 2 := by
        gcongr
    _ = ‖z‖ ^ 2 := by ring

/-- **The displacement estimate.**  The `u`-displacement differs from `−h(ζ(u))`
by at most `(‖A₁‖² + ‖A₂‖²)/(2‖a‖)`. -/
theorem norm_modelDisp_add_h_le (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ha : a ≠ 0)
    (hA1 : ‖dispNum1 a h u‖ ≤ 1 / 2) (hA2 : ‖dispNum2 a h u‖ ≤ 1 / 2) :
    ‖modelDisp a h u + h (ecalPt a u)‖
      ≤ (‖dispNum1 a h u‖ ^ 2 + ‖dispNum2 a h u‖ ^ 2) / (2 * ‖a‖) := by
  have h2a : (2 : ℂ) * a ≠ 0 := by simp [ha]
  have hna : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  have hsub : dispNum2 a h u - dispNum1 a h u = 2 * a * h (ecalPt a u) := by
    simp only [dispNum1, dispNum2]; ring
  have hh_eq : h (ecalPt a u) = (dispNum2 a h u - dispNum1 a h u) / (2 * a) := by
    rw [hsub, mul_div_cancel_left₀ _ h2a]
  have hsplit : modelDisp a h u + h (ecalPt a u)
      = ((Complex.log (1 + dispNum1 a h u) - dispNum1 a h u)
          + (dispNum2 a h u - Complex.log (1 + dispNum2 a h u))) / (2 * a) := by
    rw [modelDisp, hh_eq, ← add_div]
    ring_nf
  have e1 : ‖Complex.log (1 + dispNum1 a h u) - dispNum1 a h u‖
      ≤ ‖dispNum1 a h u‖ ^ 2 := norm_log_one_add_sub_self_le_of_le_half hA1
  have e2 : ‖dispNum2 a h u - Complex.log (1 + dispNum2 a h u)‖
      ≤ ‖dispNum2 a h u‖ ^ 2 := by
    rw [norm_sub_rev]; exact norm_log_one_add_sub_self_le_of_le_half hA2
  rw [hsplit, norm_div, norm_mul, Complex.norm_ofNat]
  refine div_le_div_of_nonneg_right ?_ (by linarith)
  exact (norm_add_le _ _).trans (by linarith)

/-- **The displacement estimate, final form.**  With `‖h − 1‖ ≤ ε` on the region
where `‖ζ‖ ≤ ρ`, the `u`-displacement is `−1` up to `ε + (‖A₁‖²+‖A₂‖²)/(2‖a‖)`. -/
theorem norm_modelDisp_add_one_le (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ρ ε : ℝ) (ha : a ≠ 0)
    (hA1 : ‖dispNum1 a h u‖ ≤ 1 / 2) (hA2 : ‖dispNum2 a h u‖ ≤ 1 / 2)
    (hζ : ‖ecalPt a u‖ ≤ ρ) (hh : ∀ ζ : ℂ, ‖ζ‖ ≤ ρ → ‖h ζ - 1‖ ≤ ε) :
    ‖modelDisp a h u + 1‖
      ≤ ε + (‖dispNum1 a h u‖ ^ 2 + ‖dispNum2 a h u‖ ^ 2) / (2 * ‖a‖) := by
  have h1 := norm_modelDisp_add_h_le a h u ha hA1 hA2
  have h2 : ‖h (ecalPt a u) - 1‖ ≤ ε := hh _ hζ
  calc ‖modelDisp a h u + 1‖
      = ‖(modelDisp a h u + h (ecalPt a u)) - (h (ecalPt a u) - 1)‖ := by
        congr 1; ring
    _ ≤ ‖modelDisp a h u + h (ecalPt a u)‖ + ‖h (ecalPt a u) - 1‖ := norm_sub_le _ _
    _ ≤ (‖dispNum1 a h u‖ ^ 2 + ‖dispNum2 a h u‖ ^ 2) / (2 * ‖a‖) + ε := add_le_add h1 h2
    _ = ε + (‖dispNum1 a h u‖ ^ 2 + ‖dispNum2 a h u‖ ^ 2) / (2 * ‖a‖) := by ring

/-- Bounds on `A₁`, `A₂` in terms of the size of `ζ` and the size of `a`. -/
theorem norm_dispNum_le (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ρ ε : ℝ)
    (hρ : 0 ≤ ρ) (_hε : 0 ≤ ε)
    (hζ : ‖ecalPt a u‖ ≤ ρ) (hh : ∀ ζ : ℂ, ‖ζ‖ ≤ ρ → ‖h ζ - 1‖ ≤ ε) :
    ‖dispNum1 a h u‖ ≤ (ρ + ‖a‖) * (1 + ε)
      ∧ ‖dispNum2 a h u‖ ≤ (ρ + ‖a‖) * (1 + ε) := by
  have hha : ‖h (ecalPt a u)‖ ≤ 1 + ε := by
    have hh' := hh _ hζ
    calc ‖h (ecalPt a u)‖ = ‖(h (ecalPt a u) - 1) + 1‖ := by ring_nf
      _ ≤ ‖h (ecalPt a u) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖h (ecalPt a u) - 1‖ + 1 := by rw [norm_one]
      _ ≤ ε + 1 := by linarith
      _ = 1 + ε := by ring
  have hb : (0 : ℝ) ≤ ρ + ‖a‖ := by positivity
  constructor
  · calc ‖dispNum1 a h u‖ = ‖(ecalPt a u - a) * h (ecalPt a u)‖ := rfl
      _ = ‖ecalPt a u - a‖ * ‖h (ecalPt a u)‖ := norm_mul _ _
      _ ≤ (ρ + ‖a‖) * (1 + ε) := by
            refine mul_le_mul ?_ hha (norm_nonneg _) hb
            calc ‖ecalPt a u - a‖ ≤ ‖ecalPt a u‖ + ‖a‖ := norm_sub_le _ _
              _ ≤ ρ + ‖a‖ := by linarith
  · calc ‖dispNum2 a h u‖ = ‖(ecalPt a u + a) * h (ecalPt a u)‖ := rfl
      _ = ‖ecalPt a u + a‖ * ‖h (ecalPt a u)‖ := norm_mul _ _
      _ ≤ (ρ + ‖a‖) * (1 + ε) := by
            refine mul_le_mul ?_ hha (norm_nonneg _) hb
            calc ‖ecalPt a u + a‖ ≤ ‖ecalPt a u‖ + ‖a‖ := norm_add_le _ _
              _ ≤ ρ + ‖a‖ := by linarith

/-- **The displacement estimate in the regime `ρ ≤ ‖a‖`**: the displacement is
`−1` up to `ε + 4‖a‖(1+ε)²`. -/
theorem norm_modelDisp_add_one_le_small (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ρ ε : ℝ)
    (ha : a ≠ 0) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε) (hερ : (ρ + ‖a‖) * (1 + ε) ≤ 1 / 2) (hρa : ρ ≤ ‖a‖)
    (hζ : ‖ecalPt a u‖ ≤ ρ) (hh : ∀ ζ : ℂ, ‖ζ‖ ≤ ρ → ‖h ζ - 1‖ ≤ ε) :
    ‖modelDisp a h u + 1‖ ≤ ε + 4 * ‖a‖ * (1 + ε) ^ 2 := by
  obtain ⟨b1, b2⟩ := norm_dispNum_le a h u ρ ε hρ hε hζ hh
  have hA1 : ‖dispNum1 a h u‖ ≤ 1 / 2 := le_trans b1 hερ
  have hA2 : ‖dispNum2 a h u‖ ≤ 1 / 2 := le_trans b2 hερ
  refine (norm_modelDisp_add_one_le a h u ρ ε ha hA1 hA2 hζ hh).trans ?_
  have hna : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  have h4 : (ρ + ‖a‖) ^ 2 ≤ 4 * ‖a‖ ^ 2 := by nlinarith
  have hkey : (‖dispNum1 a h u‖ ^ 2 + ‖dispNum2 a h u‖ ^ 2) / (2 * ‖a‖)
      ≤ 4 * ‖a‖ * (1 + ε) ^ 2 := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * ‖a‖)]
    have hb1 : ‖dispNum1 a h u‖ ^ 2 ≤ ((ρ + ‖a‖) * (1 + ε)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) b1 2
    have hb2 : ‖dispNum2 a h u‖ ^ 2 ≤ ((ρ + ‖a‖) * (1 + ε)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) b2 2
    nlinarith [hb1, hb2, h4, hna, sq_nonneg (1 + ε), hρ, hε]
  linarith

/-! ## The transit map -/

/-- The **transit map** of HS §4 in the Écalle coordinate: one iterate of the local
dynamics, i.e. the translation `u ↦ u − 1` corrected by the exact displacement `Φ`.
It sends the incoming petal to the outgoing petal across the egg-beater. -/
noncomputable def transitMap (a : ℂ) (h : ℂ → ℂ) (u : ℂ) : ℂ := u + modelDisp a h u

@[simp] theorem transitMap_apply (a : ℂ) (h : ℂ → ℂ) (u : ℂ) :
    transitMap a h u = u + modelDisp a h u := rfl

theorem transitMap_sub (a : ℂ) (h : ℂ → ℂ) (u : ℂ) :
    transitMap a h u - u = modelDisp a h u := by simp [transitMap]

/-- The transit map preserves the **Écalle height** up to the per-step error
(HS Prop. 4.6: it preserves the equators). -/
theorem abs_transitMap_im_sub_le (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (δ : ℝ)
    (hδ : ‖modelDisp a h u + 1‖ ≤ δ) :
    |(transitMap a h u).im - u.im| ≤ δ := by
  have habs := Complex.abs_im_le_norm (modelDisp a h u + 1)
  simp only [Complex.add_im, Complex.one_im, add_zero] at habs
  have hkey : (transitMap a h u).im - u.im = (modelDisp a h u).im := by
    rw [transitMap_apply, Complex.add_im]; ring
  rw [hkey]
  linarith

/-- The transit map moves the **Écalle phase** by `−1` up to the per-step error. -/
theorem abs_transitMap_re_sub_le (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (δ : ℝ)
    (hδ : ‖modelDisp a h u + 1‖ ≤ δ) :
    |(transitMap a h u).re - u.re + 1| ≤ δ := by
  have habs := Complex.abs_re_le_norm (modelDisp a h u + 1)
  simp only [Complex.add_re, Complex.one_re] at habs
  have hkey : (transitMap a h u).re - u.re + 1 = (modelDisp a h u).re + 1 := by
    rw [transitMap_apply, Complex.add_re]; ring
  rw [hkey, abs_le]
  have h1 := (abs_le.1 habs).1
  have h2 := (abs_le.1 habs).2
  constructor <;> linarith

end Work.Implosion
