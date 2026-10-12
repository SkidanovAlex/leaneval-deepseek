import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB1.RegimeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.q2Regime` — the `q2` regime at FS's parameters

The `q2` node of the box ↔ Fock interface is the matrix-window truncation of FS
`eq:DefM` at the localisation function `eq:chiBdefinition`.  Its two side
conditions are *regime* conditions, not state conditions:

1. the box side `ℓ = sideAt μ A` eventually dominates the interaction radius
   `R` in the normalised form `R ≤ ℓ·χ_{R₀}` (which is what makes
   `(χ ⋆ χ)_ℓ ≥ 1/2` on the support of `v`, `Submission.BoseGases.chiR0_half`);
2. the matrix window `𝓜 = bigM (paramsAt μ A) A μ` is eventually negligible
   against `ℓ²`, with the explicit constant `1024 π χ_sup C_χ R²` of the node.

Both are closed-form monomial facts in the diluteness `t = μA³`.  Indeed
(`Work.BoseFixB1.sideAt_eq_fsXp`, `Work.BoseBox.bigM_paramsAt`)

    ℓ = A·t^{-163/323},     𝓜 = t^{-327/1292},

so `𝓜/ℓ² = A^{-2} t^{977/1292}` (the exponents add:
`-327/1292 + 326/323 = 977/1292 > 0`), while `ℓ·χ_{R₀} = A χ_{R₀} t^{-163/323}`
grows like `t^{-163/323} → ∞`.  Both conditions therefore hold for all
sufficiently small `t > 0`, and the proof below *exhibits* the threshold
`ε₀ = min ((A χ_{R₀}/R)^{323/163}) ((1+K)^{-1292/977})` with
`K = 1024 π χ_sup C_χ R²/A²`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBoxFock

open Work.BoseBox

/-- **The matrix window against the box side**, in closed form: at FS's
parameters `𝓜 = (μA³)^{-327/1292}` and `ℓ = A(μA³)^{-163/323}`, so the
exponents add to `977/1292 > 0`:

    `𝓜 / ℓ² = (μA³)^{977/1292} / A²`.

This is the identity that turns the node's second regime condition into a
statement about `(μA³)^{977/1292} → 0`. -/
lemma bigM_div_sideAt_sq {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    Work.BoseBox.bigM (Work.BoseBox.paramsAt μ A) A μ / (Work.BoseBox.sideAt μ A) ^ 2
      = (μ * A ^ 3) ^ (977 / 1292 : ℝ) / A ^ 2 := by
  have ht : 0 < μ * A ^ 3 := by positivity
  have hbm : Work.BoseBox.bigM (Work.BoseBox.paramsAt μ A) A μ
      = (μ * A ^ 3) ^ (-(327 / 1292) : ℝ) := by
    rw [Work.BoseBox.bigM_paramsAt hμ hA]
    dsimp [Work.BoseBox.fsXp]
    norm_num
  have hs : Work.BoseBox.sideAt μ A = A * (μ * A ^ 3) ^ (-(163 / 323) : ℝ) := by
    rw [Work.BoseFixB1.sideAt_eq_fsXp hA hμ]
    dsimp [Work.BoseBox.fsXp]
    norm_num
  rw [hbm, hs, mul_pow]
  have hsq : ((μ * A ^ 3) ^ (-(163 / 323) : ℝ)) ^ 2
      = (μ * A ^ 3) ^ (-(326 / 323) : ℝ) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul ht.le]
    norm_num
  rw [hsq, mul_comm (A ^ 2), div_mul_eq_div_div, ← Real.rpow_sub ht]
  norm_num

/-- **The support-radius condition is eventually satisfied**: for every fixed
radius `R > 0` and every fixed `χ > 0` (here `χ = χ_{R₀}`) the box side
`ℓ = sideAt μ A` dominates `R/χ` as soon as the diluteness is below the
exhibited threshold `(Aχ/R)^{323/163}`. -/
lemma sideAt_ge_of_diluteness_le {A R χ μ : ℝ} (hA : 0 < A) (hR : 0 < R) (hχ : 0 < χ)
    (hμ : 0 < μ) (h : μ * A ^ 3 ≤ (A * χ / R) ^ (323 / 163 : ℝ)) :
    R ≤ Work.BoseBox.sideAt μ A * χ := by
  have ht : 0 < μ * A ^ 3 := by positivity
  have hbase : 0 < A * χ / R := by positivity
  have hs : Work.BoseBox.sideAt μ A = A * (μ * A ^ 3) ^ (-(163 / 323) : ℝ) := by
    rw [Work.BoseFixB1.sideAt_eq_fsXp hA hμ]
    dsimp [Work.BoseBox.fsXp]
    norm_num
  -- the positive power of the diluteness is bounded by `Aχ/R`
  have hpow : (μ * A ^ 3) ^ (163 / 323 : ℝ) ≤ A * χ / R := by
    calc (μ * A ^ 3) ^ (163 / 323 : ℝ)
        ≤ ((A * χ / R) ^ (323 / 163 : ℝ)) ^ (163 / 323 : ℝ) :=
          Real.rpow_le_rpow ht.le h (by norm_num)
      _ = A * χ / R := by
          rw [← Real.rpow_mul hbase.le,
            show (323 / 163 : ℝ) * (163 / 323) = 1 by norm_num, Real.rpow_one]
  -- hence the negative power dominates `R/(Aχ)`
  have htpos : 0 < (μ * A ^ 3) ^ (163 / 323 : ℝ) := Real.rpow_pos_of_pos ht _
  have hleinv : (A * χ / R)⁻¹ ≤ (μ * A ^ 3) ^ (-(163 / 323) : ℝ) := by
    rw [Real.rpow_neg ht.le]
    exact (inv_le_inv₀ hbase htpos).mpr hpow
  have hkey : A * (A * χ / R)⁻¹ * χ = R := by field_simp
  have hmid : A * (A * χ / R)⁻¹ * χ ≤ A * (μ * A ^ 3) ^ (-(163 / 323) : ℝ) * χ := by
    have h1 : (A * χ / R)⁻¹ * χ ≤ (μ * A ^ 3) ^ (-(163 / 323) : ℝ) * χ :=
      mul_le_mul_of_nonneg_right hleinv hχ.le
    calc A * (A * χ / R)⁻¹ * χ = A * ((A * χ / R)⁻¹ * χ) := by ring
      _ ≤ A * ((μ * A ^ 3) ^ (-(163 / 323) : ℝ) * χ) := mul_le_mul_of_nonneg_left h1 hA.le
      _ = A * (μ * A ^ 3) ^ (-(163 / 323) : ℝ) * χ := by ring
  calc R = A * (A * χ / R)⁻¹ * χ := hkey.symm
    _ ≤ A * (μ * A ^ 3) ^ (-(163 / 323) : ℝ) * χ := hmid
    _ = Work.BoseBox.sideAt μ A * χ := by rw [hs]

/-- **The `q2` regime of the box ↔ Fock interface.**  Fix the interaction
radius `R > 0`, the scattering length `A > 0` (at the parameters
`paramsAt μ A = fsParams (μA³)`) and the two node constants
`χ_sup, C_χ ≥ 0`.  Then for all sufficiently small diluteness `μA³` **both**
regime conditions of the `q2` node hold:

* the box side dominates the support radius, `R ≤ ℓ·χ_{R₀}`, and
* the matrix window is negligible against `ℓ²`:
  `1024 π χ_sup C_χ R²·𝓜/ℓ² ≤ 1`.

Both are the same monomial statement in `t = μA³`: the side grows like
`t^{-163/323}` while `𝓜/ℓ² = A^{-2}t^{977/1292}`. -/
theorem q2Regime {A R chiSup Cχ : ℝ} (hA : 0 < A) (hR : 0 < R) (hchi : 0 ≤ chiSup)
    (hCχ : 0 ≤ Cχ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * A ^ 3 ≤ ε₀ →
      R ≤ Work.BoseBox.sideAt μ A * Submission.BoseGases.chiR0 ∧
      1024 * Real.pi * chiSup * Cχ * R ^ 2 * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ A) A μ
        / (Work.BoseBox.sideAt μ A) ^ 2 ≤ 1 := by
  have hχ : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  -- the constant multiplying `𝓜/ℓ²` in the second condition
  set K : ℝ := 1024 * Real.pi * chiSup * Cχ * R ^ 2 / A ^ 2 with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  have hK1 : 0 < K + 1 := by linarith
  have hb2 : 0 < 1 / (K + 1) := by positivity
  refine ⟨min ((A * Submission.BoseGases.chiR0 / R) ^ (323 / 163 : ℝ))
      ((1 / (K + 1)) ^ (1292 / 977 : ℝ)), lt_min ?_ ?_, ?_⟩
  · exact Real.rpow_pos_of_pos (by positivity) _
  · exact Real.rpow_pos_of_pos hb2 _
  intro μ hμ hμA
  have ht : 0 < μ * A ^ 3 := by positivity
  constructor
  · exact sideAt_ge_of_diluteness_le hA hR hχ hμ (le_trans hμA (min_le_left _ _))
  · -- `𝓜/ℓ² = A^{-2}t^{977/1292}`, so the condition is `K t^{977/1292} ≤ 1`
    have hval : 1024 * Real.pi * chiSup * Cχ * R ^ 2
          * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ A) A μ
        / (Work.BoseBox.sideAt μ A) ^ 2 = K * (μ * A ^ 3) ^ (977 / 1292 : ℝ) := by
      rw [mul_div_assoc, bigM_div_sideAt_sq hA hμ]
      rw [show 1024 * Real.pi * chiSup * Cχ * R ^ 2
            * ((μ * A ^ 3) ^ (977 / 1292 : ℝ) / A ^ 2)
          = (1024 * Real.pi * chiSup * Cχ * R ^ 2 / A ^ 2)
            * (μ * A ^ 3) ^ (977 / 1292 : ℝ) by ring]
    have hc2 : μ * A ^ 3 ≤ (1 / (K + 1)) ^ (1292 / 977 : ℝ) :=
      le_trans hμA (min_le_right _ _)
    have htpow : (μ * A ^ 3) ^ (977 / 1292 : ℝ) ≤ 1 / (K + 1) := by
      calc (μ * A ^ 3) ^ (977 / 1292 : ℝ)
          ≤ ((1 / (K + 1)) ^ (1292 / 977 : ℝ)) ^ (977 / 1292 : ℝ) :=
            Real.rpow_le_rpow ht.le hc2 (by norm_num)
        _ = 1 / (K + 1) := by
            rw [← Real.rpow_mul hb2.le,
              show (1292 / 977 : ℝ) * (977 / 1292) = 1 by norm_num, Real.rpow_one]
    calc 1024 * Real.pi * chiSup * Cχ * R ^ 2
          * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ A) A μ
          / (Work.BoseBox.sideAt μ A) ^ 2 = K * (μ * A ^ 3) ^ (977 / 1292 : ℝ) := hval
      _ ≤ K * (1 / (K + 1)) := mul_le_mul_of_nonneg_left htpow hKnn
      _ = K / (K + 1) := by rw [mul_one_div]
      _ ≤ 1 := by
          rw [div_le_iff₀ hK1]
          linarith

end Work.BoseBoxFock
