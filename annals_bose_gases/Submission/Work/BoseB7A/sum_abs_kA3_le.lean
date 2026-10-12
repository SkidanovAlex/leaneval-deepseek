import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7A.estQ3fourADefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.sum_abs_kA3_le`

The third of the four coefficient bounds of the `Q₃⁽⁴⁾` estimate
(`Work.BoseB7A.estQ3fourA`).  Recall (FS `eq:1Q-integral`)

```
kA3 s = -f_L(s) χ̂²(s) Σ_{k∈P_H} Ŵ₁(k) α_k ( 𝒟_{sk}(1-α_{s-k}α_{-k}) - 1 ) ,
```

the `eq:1Q-integral` remainder of the `k`-sum, of order `𝓁²` (it is charged to
the kinetic reserve by the `ε`-trick in FS's proof of `eq:EstimateQ3Tilde4`).

The target bounds the whole sum by

```
K₀ · (12(64K₀)² + 4(64K₀)⁴)·𝓁² · (2ρ_z K₀ a)·ℓ³ .
```

## The proof

Everything factorises, because

* `Σ_{k∈P_H} |Ŵ₁(k)α_k| ≤ 2ρ_z K₀ a ℓ³` (`sum_abs_W1_alpha_le` below, via
  `α_k ≤ |ℬ_k|/𝒜_k ≤ 2ρ_z K₀a/|k|²` on `P_H^q` and the lattice bound
  `Q3Kernel.sum_W1sq`),
* the per-`(s,k)` remainder is uniformly `O(𝓁²)`
  (`q3Denom_remainder_le`: with `b = α_k`, `c = α_{s-k}`, `δ = 64K₀𝓁`,

  `𝒟_{sk}(1-cα_{-k}) - 1 = (c² + b² - cb - c²b²)/((1-b²)(1-c²))`,
  the denominator is `≥ 1/4` by `1-α² ≥ 1/2` (`hAB`) and the numerator is
  `≤ 3δ²+δ⁴` in absolute value, whence `|·| ≤ 12δ² + 4δ⁴`), and
* `Σ_{s∈excited} f_L(s)|χ̂²(s)| ≤ Σ_s |χ̂²(s)| ≤ K₀` (`Q3Kernel.sum_hatChiSq`).

The final arithmetic is `𝓁⁴ ≤ 𝓁²` (`𝓁 ≤ 1`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The elementary scalar algebra -/

/-- `|x + y - z - w| ≤ |x| + |y| + |z| + |w|`. -/
private lemma abs_add_sub_sub_le (x y z w : ℝ) : |x + y - z - w| ≤ |x| + |y| + |z| + |w| := by
  rw [show x + y - z - w = (x + y) + (-z + -w) by ring]
  calc |(x + y) + (-z + -w)| ≤ |x + y| + |-z + -w| := abs_add_le _ _
    _ ≤ (|x| + |y|) + (|-z| + |-w|) := add_le_add (abs_add_le _ _) (abs_add_le _ _)
    _ = |x| + |y| + |z| + |w| := by rw [abs_neg, abs_neg]; ring

/-- **The scalar core of the `kA3` remainder.**  For `|b|, |c| ≤ δ` and
`1 - b², 1 - c² ≥ 1/2` (so that the denominator is `≥ 1/4`),

`|(1 - cb)/((1-b²)(1-c²)) - 1| = |c² + b² - cb - c²b²| / ((1-b²)(1-c²)) ≤ 12δ² + 4δ⁴`.

Applied with `b = α_k`, `c = α_{s-k}` and `δ = 64K₀𝓁` this is the uniform
`O(𝓁²)` bound on the `𝒟_{sk}(1-α_{s-k}α_{-k}) - 1` of `eq:1Q-integral`. -/
lemma q3Denom_scalar {b c δ : ℝ} (hδ : 0 ≤ δ) (hb : |b| ≤ δ) (hc : |c| ≤ δ)
    (hd1 : 1 / 2 ≤ 1 - b ^ 2) (hd2 : 1 / 2 ≤ 1 - c ^ 2) :
    |(1 - c * b) / ((1 - b ^ 2) * (1 - c ^ 2)) - 1| ≤ 12 * δ ^ 2 + 4 * δ ^ 4 := by
  have hd1pos : 0 < 1 - b ^ 2 := by linarith
  have hd2pos : 0 < 1 - c ^ 2 := by linarith
  have hDpos : 0 < (1 - b ^ 2) * (1 - c ^ 2) := mul_pos hd1pos hd2pos
  have hDne : (1 - b ^ 2) * (1 - c ^ 2) ≠ 0 := ne_of_gt hDpos
  have hDge : (1 : ℝ) / 4 ≤ (1 - b ^ 2) * (1 - c ^ 2) := by
    have h := mul_le_mul hd1 hd2 (by norm_num : (0 : ℝ) ≤ 1 / 2) hd1pos.le
    nlinarith [h]
  have hb2d : b ^ 2 ≤ δ ^ 2 := by
    rw [← sq_abs b]; exact pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hc2d : c ^ 2 ≤ δ ^ 2 := by
    rw [← sq_abs c]; exact pow_le_pow_left₀ (abs_nonneg c) hc 2
  have hbc : |c * b| ≤ δ ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hc hb (abs_nonneg b) hδ
  have hbc2 : c ^ 2 * b ^ 2 ≤ δ ^ 4 := by
    have h : (c * b) ^ 2 ≤ (δ ^ 2) ^ 2 := by
      have h' := pow_le_pow_left₀ (abs_nonneg (c * b)) hbc 2
      rwa [sq_abs] at h'
    have h2 : (δ ^ 2) ^ 2 = δ ^ 4 := by ring
    rwa [mul_pow, h2] at h
  have hnum : |c ^ 2 + b ^ 2 - c * b - c ^ 2 * b ^ 2| ≤ 3 * δ ^ 2 + δ ^ 4 := by
    have htri := abs_add_sub_sub_le (c ^ 2) (b ^ 2) (c * b) (c ^ 2 * b ^ 2)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ c ^ 2),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ b ^ 2),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ c ^ 2 * b ^ 2)] at htri
    linarith
  have hkey : (1 - c * b) / ((1 - b ^ 2) * (1 - c ^ 2)) - 1
      = (c ^ 2 + b ^ 2 - c * b - c ^ 2 * b ^ 2) / ((1 - b ^ 2) * (1 - c ^ 2)) := by
    rw [div_sub_one hDne]
    congr 1
    ring
  rw [hkey, abs_div, abs_of_pos hDpos]
  calc |c ^ 2 + b ^ 2 - c * b - c ^ 2 * b ^ 2| / ((1 - b ^ 2) * (1 - c ^ 2))
      ≤ (3 * δ ^ 2 + δ ^ 4) / ((1 - b ^ 2) * (1 - c ^ 2)) :=
        div_le_div_of_nonneg_right hnum hDpos.le
    _ ≤ (3 * δ ^ 2 + δ ^ 4) / ((1 : ℝ) / 4) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hDge
    _ = 12 * δ ^ 2 + 4 * δ ^ 4 := by ring

/-! ## 2. The uniform per-`(s,k)` bound on the `eq:1Q-integral` remainder -/

/-- **The `kA3` remainder is `O(𝓁²)` uniformly.**  For `s` in the support of the
low-momentum localisation and `k ∈ P_H`,

`|𝒟_{sk}(1 - α_{s-k}α_{-k}) - 1| ≤ 12(64K₀𝓁)² + 4(64K₀𝓁)⁴`.

The two `1-α²` factors in `𝒟_{sk}` are `≥ 1/2` by `hAB` on `P_H^q`; the factors
`α_k, α_{s-k}, α_{-k}` are all `≤ 64K₀𝓁` by `hα` (`s-k ∈ P_H^q` is `hsub`;
`k ∈ P_H ⊆ P_H^q`; `α` is even). -/
lemma q3Denom_remainder_le (K₀ : ℝ)
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (hK : Work.BoseB7A.Q3Kernel K₀ F T E) (hv : Work.BoseB7.FSParamsView E)
    (hAB : ∀ q : Mode, F.PHq E.KH E.aScat q → 1 / 2 ≤ 1 - E.alpha q ^ 2)
    (hα : ∀ q : Mode, F.PHq E.KH E.aScat q → |E.alpha q| ≤ 64 * K₀ * E.lille)
    (hsub : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → F.PHq E.KH E.aScat (s - k))
    {s k : Mode} (hs : E.fL s ≠ 0) (hk : k ∈ F.PHset E) :
    |E.q3Denom s k * (1 - E.alpha (s - k) * E.alpha (-k)) - 1|
      ≤ 12 * (64 * K₀ * E.lille) ^ 2 + 4 * (64 * K₀ * E.lille) ^ 4 := by
  have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
  have hqk : F.PHq E.KH E.aScat k := PH_subset_PHq F E hv k hkPH
  have hqsk : F.PHq E.KH E.aScat (s - k) := hsub s k hs hk
  have hδ : 0 ≤ 64 * K₀ * E.lille := le_trans (abs_nonneg _) (hα k hqk)
  have heven : E.alpha (-k) = E.alpha k := by
    simp only [Work.BoseB7.Q3Env.alpha, Work.BoseB7.alphaCoef, hK.A_even k, hK.B_even k]
  have hrew : 1 / ((1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2)) *
      (1 - E.alpha (s - k) * E.alpha k)
      = (1 - E.alpha (s - k) * E.alpha k) /
        ((1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2)) := by ring
  rw [Work.BoseB7.Q3Env.q3Denom, heven, hrew]
  exact q3Denom_scalar hδ (hα k hqk) (hα (s - k) hqsk) (hAB k hqk) (hAB (s - k) hqsk)

/-! ## 3. The sum of the `k`-weights -/

/-- **The `P_H`-sum of the `k`-weights is `2ρ_z K₀ a ℓ³`.**  On `P_H^q` one has
`|α_k| ≤ |ℬ_k|/𝒜_k = ρ_z|Ŵ₁(k)|/𝒜_k ≤ 2ρ_z|Ŵ₁(k)|/‖k‖²` (`𝒜_k ≥ ‖k‖²/2`), so

`Σ_{k∈P_H} |Ŵ₁(k)α_k| ≤ 2ρ_z Σ_{k∈P_H^q} Ŵ₁(k)²/‖k‖² ≤ 2ρ_z K₀ a ℓ³`

by the lattice bound `Q3Kernel.sum_W1sq` (and `P_H ⊆ P_H^q`). -/
lemma sum_abs_W1_alpha_le (K₀ : ℝ)
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (hK : Work.BoseB7A.Q3Kernel K₀ F T E) (hv : Work.BoseB7.FSParamsView E) :
    ∑ k ∈ F.PHset E, |E.W1 k * E.alpha k| ≤ 2 * E.rho * K₀ * E.aScat * E.ell ^ 3 := by
  have hell : 0 < E.ell := Work.BoseB7.ell_pos E hv
  have hell3 : 0 ≤ E.ell ^ 3 := (pow_pos hell 3).le
  have hrho : 0 ≤ E.rho := (Work.BoseB7.rho_pos E hv).le
  have hsub2 : F.PHset E ⊆ (excited Mode).filter (F.PHq E.KH E.aScat) := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1,
      PH_subset_PHq F E hv k (Finset.mem_filter.mp hk).2⟩
  have hpt : ∀ k ∈ F.PHset E,
      |E.W1 k * E.alpha k| ≤ 2 * E.rho * (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) := by
    intro k hk
    have hq : F.PHq E.KH E.aScat k := PH_subset_PHq F E hv k (Finset.mem_filter.mp hk).2
    have hcutpos : 0 < 1 / (4 * E.KH * E.aScat) := by
      have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
      have ha : 0 < E.aScat := hv.a_pos
      positivity
    have hRpos : 0 < ‖F.kmom k‖ := lt_of_lt_of_le hcutpos hq
    have hR2pos : 0 < ‖F.kmom k‖ ^ 2 / 2 := div_pos (pow_pos hRpos 2) (by norm_num)
    have hApos : 0 < E.A k := lt_of_lt_of_le hR2pos (hK.A_ge k hq)
    have hαle : |E.alpha k| ≤ |E.B k| / E.A k := abs_alphaCoef_le hApos
    have hsq : |E.W1 k| * |E.W1 k| = E.W1 k ^ 2 := by rw [← pow_two, sq_abs, pow_two]
    calc |E.W1 k * E.alpha k| = |E.W1 k| * |E.alpha k| := abs_mul _ _
      _ ≤ |E.W1 k| * (|E.B k| / E.A k) := mul_le_mul_of_nonneg_left hαle (abs_nonneg _)
      _ = E.rho * E.W1 k ^ 2 / E.A k := by
          rw [hK.B_eq k, abs_mul, abs_of_nonneg hrho,
            show |E.W1 k| * (E.rho * |E.W1 k| / E.A k)
              = E.rho * (|E.W1 k| * |E.W1 k|) / E.A k by ring, hsq]
      _ ≤ E.rho * E.W1 k ^ 2 / (‖F.kmom k‖ ^ 2 / 2) :=
          div_le_div_of_nonneg_left (mul_nonneg hrho (sq_nonneg _)) hR2pos (hK.A_ge k hq)
      _ = 2 * E.rho * (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) := by ring
  calc ∑ k ∈ F.PHset E, |E.W1 k * E.alpha k|
      ≤ ∑ k ∈ F.PHset E, 2 * E.rho * (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) := Finset.sum_le_sum hpt
    _ = 2 * E.rho * ∑ k ∈ F.PHset E, (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) := by rw [Finset.mul_sum]
    _ ≤ 2 * E.rho * ∑ k ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
          (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hrho)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub2
          (fun i _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ 2 * E.rho * (K₀ * E.aScat * E.ell ^ 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hrho)
        have h3 : E.ell ^ (-(3 : ℝ)) *
            ∑ k ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
              (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) ≤ K₀ * E.aScat := hK.sum_W1sq
        have hinv : E.ell ^ 3 * E.ell ^ (-(3 : ℝ)) = 1 := by
          rw [← Real.rpow_natCast E.ell 3, ← Real.rpow_add hell]
          norm_num
        have h4 : E.ell ^ 3 * (E.ell ^ (-(3 : ℝ)) *
            ∑ k ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
              (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2)) ≤ E.ell ^ 3 * (K₀ * E.aScat) :=
          mul_le_mul_of_nonneg_left h3 hell3
        have h5 : (∑ k ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
              (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2)) ≤ E.ell ^ 3 * (K₀ * E.aScat) := by
          rwa [← mul_assoc, hinv, one_mul] at h4
        calc (∑ k ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
              (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2)) ≤ E.ell ^ 3 * (K₀ * E.aScat) := h5
          _ = K₀ * E.aScat * E.ell ^ 3 := by ring
    _ = 2 * E.rho * K₀ * E.aScat * E.ell ^ 3 := by ring

/-! ## 4. The per-`s` bound, and the sum -/

/-- **`|kA3(s)|` factorises.**  For every mode `s`,

`|kA3(s)| ≤ f_L(s)|χ̂²(s)| · (Σ_{k∈P_H}|Ŵ₁(k)α_k|) · (12(64K₀𝓁)² + 4(64K₀𝓁)⁴)`,

by the triangle inequality over the finite `k`-sum and the uniform per-`(s,k)`
bound `q3Denom_remainder_le` (for `f_L(s) = 0` both sides vanish). -/
private lemma abs_kA3_le (K₀ : ℝ)
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (hK : Work.BoseB7A.Q3Kernel K₀ F T E) (hv : Work.BoseB7.FSParamsView E)
    (hAB : ∀ q : Mode, F.PHq E.KH E.aScat q → 1 / 2 ≤ 1 - E.alpha q ^ 2)
    (hα : ∀ q : Mode, F.PHq E.KH E.aScat q → |E.alpha q| ≤ 64 * K₀ * E.lille)
    (hsub : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → F.PHq E.KH E.aScat (s - k))
    (s : Mode) :
    |kA3 F E s| ≤ E.fL s * |E.hatChiSq s| *
      ((∑ k ∈ F.PHset E, |E.W1 k * E.alpha k|)
        * (12 * (64 * K₀ * E.lille) ^ 2 + 4 * (64 * K₀ * E.lille) ^ 4)) := by
  by_cases hfs : E.fL s = 0
  · rw [kA3, hfs]
    simp
  · have hCnn : 0 ≤ 12 * (64 * K₀ * E.lille) ^ 2 + 4 * (64 * K₀ * E.lille) ^ 4 := by
      positivity
    have h1 : |kA3 F E s| = E.fL s * |E.hatChiSq s| *
        |∑ k ∈ F.PHset E, E.W1 k * E.alpha k *
          (E.q3Denom s k * (1 - E.alpha (s - k) * E.alpha (-k)) - 1)| := by
      rw [kA3, abs_neg, abs_mul, abs_mul, abs_of_nonneg (hK.fL_nonneg s)]
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hK.fL_nonneg s) (abs_nonneg _))
    calc |∑ k ∈ F.PHset E, E.W1 k * E.alpha k *
            (E.q3Denom s k * (1 - E.alpha (s - k) * E.alpha (-k)) - 1)|
        ≤ ∑ k ∈ F.PHset E, |E.W1 k * E.alpha k *
            (E.q3Denom s k * (1 - E.alpha (s - k) * E.alpha (-k)) - 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ F.PHset E, |E.W1 k * E.alpha k| *
            (12 * (64 * K₀ * E.lille) ^ 2 + 4 * (64 * K₀ * E.lille) ^ 4) :=
          Finset.sum_le_sum fun k hk => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left
              (q3Denom_remainder_le K₀ F T E hK hv hAB hα hsub hfs hk) (abs_nonneg _)
      _ = (∑ k ∈ F.PHset E, |E.W1 k * E.alpha k|) *
            (12 * (64 * K₀ * E.lille) ^ 2 + 4 * (64 * K₀ * E.lille) ^ 4) := by
          rw [Finset.sum_mul]

theorem sum_abs_kA3_le (K₀ : ℝ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (hK : Work.BoseB7A.Q3Kernel K₀ F T E) (hv : Work.BoseB7.FSParamsView E) (hK₀ : 0 ≤ K₀)
    (hAB : ∀ q : Mode, F.PHq E.KH E.aScat q → 1 / 2 ≤ 1 - E.alpha q ^ 2)
    (hα : ∀ q : Mode, F.PHq E.KH E.aScat q → |E.alpha q| ≤ 64 * K₀ * E.lille)
    (hsub : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → F.PHq E.KH E.aScat (s - k)) :
    ∑ s ∈ Work.BoseB7.excited Mode, |Work.BoseB7A.kA3 F E s|
      ≤ K₀ * ((12 * (64 * K₀) ^ 2 + 4 * (64 * K₀) ^ 4) * E.lille ^ 2
          * (2 * E.rho * K₀ * E.aScat) * E.ell ^ 3) := by
  have hlille_nn : 0 ≤ E.lille := (lille_pos E hv).le
  have hlille1 : E.lille ≤ 1 := lille_le_one E hv
  have hCnn : 0 ≤ 12 * (64 * K₀ * E.lille) ^ 2 + 4 * (64 * K₀ * E.lille) ^ 4 := by
    positivity
  have hSnn : 0 ≤ ∑ k ∈ F.PHset E, |E.W1 k * E.alpha k| :=
    Finset.sum_nonneg fun k _ => abs_nonneg _
  have hSl := sum_abs_W1_alpha_le K₀ F T E hK hv
  have hrhnn : 0 ≤ 2 * E.rho * K₀ * E.aScat * E.ell ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (rho_pos E hv).le) hK₀)
      hv.a_pos.le) (pow_nonneg (ell_pos E hv).le 3)
  have hsumfL : ∑ s ∈ Work.BoseB7.excited Mode, E.fL s * |E.hatChiSq s| ≤ K₀ := by
    calc ∑ s ∈ Work.BoseB7.excited Mode, E.fL s * |E.hatChiSq s|
        ≤ ∑ s ∈ Work.BoseB7.excited Mode, |E.hatChiSq s| :=
          Finset.sum_le_sum fun s _ => mul_le_of_le_one_left (abs_nonneg _) (hK.fL_le_one s)
      _ ≤ K₀ := hK.sum_hatChiSq
  have hCl : 12 * (64 * K₀ * E.lille) ^ 2 + 4 * (64 * K₀ * E.lille) ^ 4
      ≤ (12 * (64 * K₀) ^ 2 + 4 * (64 * K₀) ^ 4) * E.lille ^ 2 := by
    have hl4 : E.lille ^ 4 ≤ E.lille ^ 2 := by
      have h2 : E.lille ^ 2 ≤ 1 := by nlinarith
      calc E.lille ^ 4 = E.lille ^ 2 * E.lille ^ 2 := by ring
        _ ≤ E.lille ^ 2 * 1 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
        _ = E.lille ^ 2 := by ring
    have hstep : 4 * (64 * K₀) ^ 4 * E.lille ^ 4 ≤ 4 * (64 * K₀) ^ 4 * E.lille ^ 2 :=
      mul_le_mul_of_nonneg_left hl4 (by positivity)
    rw [show (64 * K₀ * E.lille) ^ 2 = (64 * K₀) ^ 2 * E.lille ^ 2 by ring,
        show (64 * K₀ * E.lille) ^ 4 = (64 * K₀) ^ 4 * E.lille ^ 4 by ring]
    linarith
  calc ∑ s ∈ Work.BoseB7.excited Mode, |Work.BoseB7A.kA3 F E s|
      ≤ ∑ s ∈ Work.BoseB7.excited Mode, E.fL s * |E.hatChiSq s| *
          ((∑ k ∈ F.PHset E, |E.W1 k * E.alpha k|)
            * (12 * (64 * K₀ * E.lille) ^ 2 + 4 * (64 * K₀ * E.lille) ^ 4)) :=
        Finset.sum_le_sum fun s _ => abs_kA3_le K₀ F T E hK hv hAB hα hsub s
    _ = (∑ s ∈ Work.BoseB7.excited Mode, E.fL s * |E.hatChiSq s|)
          * ((∑ k ∈ F.PHset E, |E.W1 k * E.alpha k|)
            * (12 * (64 * K₀ * E.lille) ^ 2 + 4 * (64 * K₀ * E.lille) ^ 4)) :=
        (Finset.sum_mul (Work.BoseB7.excited Mode)
          (fun s => E.fL s * |E.hatChiSq s|) _).symm
    _ ≤ K₀ * ((∑ k ∈ F.PHset E, |E.W1 k * E.alpha k|)
          * (12 * (64 * K₀ * E.lille) ^ 2 + 4 * (64 * K₀ * E.lille) ^ 4)) :=
        mul_le_mul_of_nonneg_right hsumfL (mul_nonneg hSnn hCnn)
    _ ≤ K₀ * ((2 * E.rho * K₀ * E.aScat * E.ell ^ 3)
          * (12 * (64 * K₀ * E.lille) ^ 2 + 4 * (64 * K₀ * E.lille) ^ 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSl hCnn) hK₀
    _ ≤ K₀ * ((2 * E.rho * K₀ * E.aScat * E.ell ^ 3)
          * ((12 * (64 * K₀) ^ 2 + 4 * (64 * K₀) ^ 4) * E.lille ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hCl hrhnn) hK₀
    _ = K₀ * ((12 * (64 * K₀) ^ 2 + 4 * (64 * K₀) ^ 4) * E.lille ^ 2
          * (2 * E.rho * K₀ * E.aScat) * E.ell ^ 3) := by ring

end Work.BoseB7A
