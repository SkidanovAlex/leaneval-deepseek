import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.estQ3fourADefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.sum_sq_kA4_le` — the `kA4`-sum of FS `eq:EstimateQ3Tilde4`

FS's fourth estimate `eq:EstimateQ3Tilde4` (`Work.BoseC3QAll.estQ3fourA`) decomposes
the coefficient `c_s = (z/ℓ³)(kA1+kA2+kA3+kA4)` of a linear word in the θ-modes
`ã_s`, and the linear-form bound `NWindow_linear_bound` needs the `ℓ²`-norm
`√(Σ_s c_s²)`.  The three pieces `kA1`, `kA2`, `kA3` are bounded in `ℓ¹`;
the fourth,

`kA4(s) = f_L(s) Σ_{k∈P_H} Ŵ₁(k)α_k 𝒟_{sk}(χ̂(s−k)χ̂(−k) − α_{s−k}α_{−k}χ̂(k)χ̂(k−s))`,

is the exponentially small `eq:1Q-integral2` word, and this file proves the
`ℓ²`-bound for it (the statement of `Work.BoseC3QAll.sum_sq_kA4_le`).

## The bound

Only the `P_H^q`-smallness of `χ̂` and of `α` is used, *not* a cancellation
between the two terms of the bracket:

* `k ∈ P_H^q` and `s − k ∈ P_H^q` (for `f_L(s) ≠ 0`) give
  `|χ̂| ≤ K₀η` (`Q3KernelFSAll.hatChi_small`) and `|α| ≤ 64K₀𝓁` (hypothesis `hα`),
  so the bracket is `≤ K₀²η²(1+(64K₀𝓁)²)`;
* `𝒟_{sk} = 1/((1−α_k²)(1−α_{s−k}²)) ≤ 4`, from `1−α² ≥ 1/2` on `P_H^q` (`hAB`);
* the remaining `k`-sum `Σ_{k∈P_H}|Ŵ₁(k)α_k|` is bounded with the *lattice form*
  of `Ŵ₁α_k = ρ_zŴ₁(k)²/(2𝒟_k)`: `|α_k| ≤ |ℬ_k|/𝒜_k ≤ 2|ℬ_k|/‖k‖²` and
  `ℬ_k = ρ_zŴ₁(k)`, so the sum is `2ρ_zℓ³(ℓ⁻³Σ_{P_H^q}Ŵ₁²/‖k‖²) ≤ 2ρ_zℓ³K₀a`
  (`Q3KernelFSAll.sum_W1sq`, `A_ge`).

Summing the squares over the (at most `K₀(K_ℓK_L)³` — `Q3KernelFSAll.count_PL`) modes
with `f_L(s) ≠ 0` and using the parameter values of `FSParamsView`
(`η = X^{1236} ≤ 1`, `𝓁 = X^{97/2} ≤ 1`) gives the stated bound.

## Provenance of `kA4`

`kA4` is FS's `eq:1Q-integral2` word, defined (verbatim) in
`Submission/Work/BoseB7A/estQ3fourADefs.lean`, which this file imports.  The
definition is the one of `estQ3fourA.lean`: that module holds the definitions
*and* the proof of the `EstQ3fourA` estimate, which uses this lemma, so the
definitions had to be extracted below the resulting import cycle (see the header
of `estQ3fourADefs.lean` and `NOTE_kA4_import_cycle.md`).  Only `kA4` itself is
used here (unfolded once, in the per-`s` estimate).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 0. Elementary scalar helpers -/

/-- `η ≥ 0`. -/
lemma kA4_eta_nonneg (E : Q3Env Mode) (hv : FSParamsView E) : 0 ≤ eta E := by
  rw [eta]
  refine Real.rpow_nonneg ?_ _
  have hKl : 0 < E.Kl := lt_of_lt_of_le zero_lt_one hv.one_le_Kl
  have hl : 0 ≤ E.lille := le_of_lt (lille_pos E hv)
  exact mul_nonneg (Real.rpow_nonneg hKl.le _) hl

/-- `η = X^{1236} ≤ 1` at FS's parameter point. -/
lemma kA4_eta_le_one (E : Q3Env Mode) (hv : FSParamsView E) : eta E ≤ 1 := by
  rw [eta_eq E hv]
  exact Work.BoseBox.fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)

/-- `64K₀𝓁 ≤ 64K₀` (`𝓁 ≤ 1`, `K₀ ≥ 0`). -/
lemma sixtyfour_le (E : Q3Env Mode) (hv : FSParamsView E) {K₀ : ℝ} (hK₀ : 0 ≤ K₀) :
    64 * K₀ * E.lille ≤ 64 * K₀ := by
  have h : K₀ * E.lille ≤ K₀ * 1 :=
    mul_le_mul_of_nonneg_left (lille_le_one E hv) hK₀
  linarith

/-- `(1 + (64K₀𝓁)²) ≤ (1 + (64K₀)²)`. -/
lemma one_add_sq_le (E : Q3Env Mode) (hv : FSParamsView E) {K₀ : ℝ} (hK₀ : 0 ≤ K₀) :
    1 + (64 * K₀ * E.lille) ^ 2 ≤ 1 + (64 * K₀) ^ 2 := by
  have h1 : 0 ≤ 64 * K₀ * E.lille :=
    mul_nonneg (mul_nonneg (by norm_num) hK₀) (le_of_lt (lille_pos E hv))
  have h2 : 64 * K₀ * E.lille ≤ 64 * K₀ := sixtyfour_le E hv hK₀
  nlinarith [h1, h2, sq_nonneg (64 * K₀)]

/-- Generic four-factor product inequality. -/
lemma mul4_le {a b c d A B C D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (haA : a ≤ A) (hbB : b ≤ B) (hcC : c ≤ C) (hdD : d ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    a * b * c * d ≤ A * B * C * D := by
  have h1 : a * b ≤ A * B := mul_le_mul haA hbB hb hA
  have h2 : a * b * c ≤ A * B * C := mul_le_mul h1 hcC hc (mul_nonneg hA hB)
  exact mul_le_mul h2 hdD hd (mul_nonneg (mul_nonneg hA hB) hC)

/-! ## 1. Region facts and the two coefficient bounds on `P_H^q` -/

/-- `P_H ⊆ P_H^q` (the threshold `1/(4K_Ha)` is below `1/(2K_Ha)`). -/
lemma mem_PHq_of_mem_PHset (F : FockData Mode) (E : Q3Env Mode) (hv : FSParamsView E)
    {k : Mode} (hk : k ∈ F.PHset E) : F.PHq E.KH E.aScat k := by
  have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
  have ha : 0 < E.aScat := hv.a_pos
  have hpos : 0 < 2 * E.KH * E.aScat := by positivity
  have hle : 2 * E.KH * E.aScat ≤ 4 * E.KH * E.aScat := by linarith
  exact le_trans (one_div_le_one_div_of_le hpos hle) (Finset.mem_filter.mp hk).2

/-- On `P_H^q` the momentum does not vanish. -/
lemma kmom_pos_of_PHq (F : FockData Mode) (E : Q3Env Mode) (hv : FSParamsView E)
    {q : Mode} (hq : F.PHq E.KH E.aScat q) : 0 < ‖F.kmom q‖ := by
  have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
  have ha : 0 < E.aScat := hv.a_pos
  have hpos : 0 < 1 / (4 * E.KH * E.aScat) := by positivity
  exact lt_of_lt_of_le hpos hq

/-- On `P_H^q` the kinetic coefficient `𝒜` is positive. -/
lemma A_pos_of_PHq (F : FockData Mode) (E : Q3Env Mode) {K₀ : ℝ}
    {T : TildeData F} (hK : Q3KernelFSAll K₀ F T E) (hv : FSParamsView E)
    {q : Mode} (hq : F.PHq E.KH E.aScat q) : 0 < E.A q := by
  have hkm : 0 < ‖F.kmom q‖ := kmom_pos_of_PHq F E hv hq
  have h : 0 < ‖F.kmom q‖ ^ 2 / 2 := by positivity
  linarith [hK.A_ge q hq]

/-- `|α_q| ≤ |ℬ_q|/𝒜_q` on `P_H^q` (the denominator `𝒜 + √(𝒜²−ℬ²) ≥ 𝒜 > 0`). -/
lemma alpha_abs_le_B_div_A (F : FockData Mode) (E : Q3Env Mode) {K₀ : ℝ}
    {T : TildeData F} (hK : Q3KernelFSAll K₀ F T E) (hv : FSParamsView E)
    {q : Mode} (hq : F.PHq E.KH E.aScat q) : |E.alpha q| ≤ |E.B q| / E.A q := by
  have hA : 0 < E.A q := A_pos_of_PHq F E hK hv hq
  have hS : 0 ≤ Submission.BoseGases.bogS (E.A q) (E.B q) :=
    Submission.BoseGases.bogS_nonneg _ _
  have hden : 0 < E.A q + Submission.BoseGases.bogS (E.A q) (E.B q) := by linarith
  simp only [Q3Env.alpha, Work.BoseB7.alphaCoef, Submission.BoseGases.bogAlpha,
    abs_div, abs_of_pos hden]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hA (by linarith)

/-- **`Σ_{k∈P_H}|Ŵ₁(k)α_k| ≤ 2ρ_zℓ³K₀a`.**  Uses `α_k = ℬ_k/(𝒜_k+√(𝒜_k²−ℬ_k²))`,
`ℬ_k = ρ_zŴ₁(k)`, `𝒜_k ≥ ‖k‖²/2` on `P_H^q` and the lattice form
`ℓ⁻³Σ_{P_H^q}Ŵ₁²/‖k‖² ≤ K₀a` of `Q3KernelFSAll.sum_W1sq`. -/
lemma sum_W1_alpha_le (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    (hK : Q3KernelFSAll K₀ F T E) (hv : FSParamsView E) :
    ∑ k ∈ F.PHset E, |E.W1 k * E.alpha k| ≤ 2 * E.rho * E.ell ^ 3 * (K₀ * E.aScat) := by
  -- the per-mode bound
  have hterm : ∀ k ∈ F.PHset E,
      |E.W1 k * E.alpha k| ≤ 2 * E.rho * E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 := by
    intro k hk
    have hq : F.PHq E.KH E.aScat k := mem_PHq_of_mem_PHset F E hv hk
    have hA : 0 < E.A k := A_pos_of_PHq F E hK hv hq
    have hkm : 0 < ‖F.kmom k‖ := kmom_pos_of_PHq F E hv hq
    have hρ : 0 < E.rho := Work.BoseB7.rho_pos E hv
    have h1 : |E.W1 k * E.alpha k| ≤ E.rho * E.W1 k ^ 2 / E.A k := by
      have hα := alpha_abs_le_B_div_A F E hK hv hq
      have hB : |E.B k| = E.rho * |E.W1 k| := by
        rw [hK.B_eq k, abs_mul, abs_of_pos hρ]
      calc |E.W1 k * E.alpha k| = |E.W1 k| * |E.alpha k| := abs_mul _ _
        _ ≤ |E.W1 k| * (|E.B k| / E.A k) :=
            mul_le_mul_of_nonneg_left hα (abs_nonneg _)
        _ = E.rho * E.W1 k ^ 2 / E.A k := by
            rw [hB, ← sq_abs (E.W1 k)]
            ring
    have h2 : E.rho * E.W1 k ^ 2 / E.A k
        ≤ 2 * E.rho * E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 := by
      rw [div_le_div_iff₀ hA (by positivity)]
      have hρnn : 0 ≤ E.rho := le_of_lt hρ
      have hdt : ‖F.kmom k‖ ^ 2 ≤ 2 * E.A k := by linarith [hK.A_ge k hq]
      have hc : 0 ≤ E.rho * E.W1 k ^ 2 := mul_nonneg hρnn (sq_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_left hdt hc]
    linarith
  -- the lattice sum
  have hsub : F.PHset E ⊆ (excited Mode).filter (F.PHq E.KH E.aScat) := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1, mem_PHq_of_mem_PHset F E hv hk⟩
  have hmono : ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2
      ≤ ∑ k ∈ (excited Mode).filter (F.PHq E.KH E.aScat), E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
  have hell : 0 < E.ell := Work.BoseB7.ell_pos E hv
  have h3 : E.ell ^ 3 * E.ell ^ (-(3 : ℝ)) = 1 := by
    rw [← Real.rpow_natCast E.ell 3, ← Real.rpow_add hell]
    norm_num
  have hlat : ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 ≤ E.ell ^ 3 * (K₀ * E.aScat) := by
    calc ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2
        ≤ ∑ k ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
            E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 := hmono
      _ = E.ell ^ 3 * (E.ell ^ (-(3 : ℝ)) *
            ∑ k ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
              E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) := by
          rw [← mul_assoc, h3, one_mul]
      _ ≤ E.ell ^ 3 * (K₀ * E.aScat) :=
          mul_le_mul_of_nonneg_left hK.sum_W1sq (pow_pos hell 3).le
  calc ∑ k ∈ F.PHset E, |E.W1 k * E.alpha k|
      ≤ ∑ k ∈ F.PHset E, 2 * E.rho * E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 :=
        Finset.sum_le_sum hterm
    _ = 2 * E.rho * ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
    _ ≤ 2 * E.rho * (E.ell ^ 3 * (K₀ * E.aScat)) :=
        mul_le_mul_of_nonneg_left hlat
          (by have h := Work.BoseB7.rho_pos E hv; linarith)
    _ = 2 * E.rho * E.ell ^ 3 * (K₀ * E.aScat) := by ring

/-! ## 2. The `χ̂`-bracket -/

/-- The two-term `χ̂`-bracket of `kA4` is `K₀²η²(1+(64K₀𝓁)²)`-small on `P_H`. -/
lemma chihat_bracket_le (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    (hK : Q3KernelFSAll K₀ F T E) (hv : FSParamsView E) (hK₀ : 0 ≤ K₀)
    (hα : ∀ q : Mode, F.PHq E.KH E.aScat q → |E.alpha q| ≤ 64 * K₀ * E.lille)
    (hsub : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
      F.PHq E.KH E.aScat (s - k))
    {s k : Mode} (hs : E.fL s ≠ 0) (hk : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    |E.hatChi (s - k) * E.hatChi (-k)
        - E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s))|
      ≤ K₀ ^ 2 * eta E ^ 2 * (1 + (64 * K₀ * E.lille) ^ 2) := by
  have hqk : F.PHq E.KH E.aScat k := mem_PHq_of_mem_PHset F E hv hk
  have hqsk : F.PHq E.KH E.aScat (s - k) := hsub s k hs hk hW
  -- parities
  have hnegk : E.hatChi (-k) = E.hatChi k := hK.hatChi_even k
  have hks : E.hatChi (k - s) = E.hatChi (s - k) := by
    have h := hK.hatChi_even (s - k)
    rwa [show -(s - k) = k - s by abel] at h
  have halphaneg : E.alpha (-k) = E.alpha k := by
    simp only [Q3Env.alpha, Work.BoseB7.alphaCoef, hK.A_even k, hK.B_even k]
  -- the four smallness bounds
  have h1 : |E.hatChi (s - k)| ≤ K₀ * eta E := hK.hatChi_small (s - k) hqsk
  have h2 : |E.hatChi (-k)| ≤ K₀ * eta E := by rw [hnegk]; exact hK.hatChi_small k hqk
  have h3 : |E.hatChi k| ≤ K₀ * eta E := hK.hatChi_small k hqk
  have h4 : |E.hatChi (k - s)| ≤ K₀ * eta E := by
    rw [hks]; exact hK.hatChi_small (s - k) hqsk
  have h5 : |E.alpha (s - k)| ≤ 64 * K₀ * E.lille := hα (s - k) hqsk
  have h6 : |E.alpha (-k)| ≤ 64 * K₀ * E.lille := by rw [halphaneg]; exact hα k hqk
  have hCnn : 0 ≤ K₀ * eta E := mul_nonneg hK₀ (kA4_eta_nonneg E hv)
  have hDnn : 0 ≤ 64 * K₀ * E.lille :=
    mul_nonneg (mul_nonneg (by norm_num) hK₀) (le_of_lt (lille_pos E hv))
  -- the two products
  have hp1 : |E.hatChi (s - k)| * |E.hatChi (-k)| ≤ (K₀ * eta E) * (K₀ * eta E) :=
    mul_le_mul h1 h2 (abs_nonneg _) hCnn
  have hp2 : |E.alpha (s - k)| * |E.alpha (-k)| * |E.hatChi k| * |E.hatChi (k - s)|
      ≤ (64 * K₀ * E.lille) * (64 * K₀ * E.lille) * (K₀ * eta E) * (K₀ * eta E) :=
    mul4_le (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
      h5 h6 h3 h4 hDnn hDnn hCnn hCnn
  have htri : |E.hatChi (s - k) * E.hatChi (-k)
        - E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s))|
      ≤ |E.hatChi (s - k) * E.hatChi (-k)|
        + |E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s))| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (E.hatChi (s - k) * E.hatChi (-k))
        (-(E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s))))
  calc |E.hatChi (s - k) * E.hatChi (-k)
        - E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s))|
      ≤ |E.hatChi (s - k) * E.hatChi (-k)|
          + |E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s))| := htri
    _ = |E.hatChi (s - k)| * |E.hatChi (-k)|
          + |E.alpha (s - k)| * |E.alpha (-k)| * |E.hatChi k| * |E.hatChi (k - s)| := by
        simp only [abs_mul]
        ring
    _ ≤ (K₀ * eta E) * (K₀ * eta E)
          + (64 * K₀ * E.lille) * (64 * K₀ * E.lille) * (K₀ * eta E) * (K₀ * eta E) :=
        add_le_add hp1 hp2
    _ = K₀ ^ 2 * eta E ^ 2 * (1 + (64 * K₀ * E.lille) ^ 2) := by ring

/-! ## 3. The `𝒟`-denominator -/

/-- `0 ≤ 𝒟_{sk} ≤ 4` whenever both modes carry the `P_H^q`-smallness
(`1 − α² ≥ 1/2`) of `hAB`. -/
lemma q3Denom_bounds (F : FockData Mode) (E : Q3Env Mode) (hv : FSParamsView E)
    (hAB : ∀ q : Mode, F.PHq E.KH E.aScat q → 1 / 2 ≤ 1 - E.alpha q ^ 2)
    (hsub : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
      F.PHq E.KH E.aScat (s - k))
    {s k : Mode} (hs : E.fL s ≠ 0) (hk : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    0 ≤ E.q3Denom s k ∧ E.q3Denom s k ≤ 4 := by
  have hqk : F.PHq E.KH E.aScat k := mem_PHq_of_mem_PHset F E hv hk
  have hqsk : F.PHq E.KH E.aScat (s - k) := hsub s k hs hk hW
  have h1 : (1 / 2 : ℝ) ≤ 1 - E.alpha k ^ 2 := hAB k hqk
  have h2 : (1 / 2 : ℝ) ≤ 1 - E.alpha (s - k) ^ 2 := hAB (s - k) hqsk
  have hprod : (1 / 2 : ℝ) * (1 / 2) ≤ (1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2) :=
    mul_le_mul h1 h2 (by norm_num) (by linarith [h1])
  have hp : 0 < (1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2) := by linarith
  constructor
  · rw [Q3Env.q3Denom]
    exact le_of_lt (one_div_pos.mpr hp)
  · rw [Q3Env.q3Denom, div_le_iff₀ hp]
    linarith

/-! ## 4. The two monomials of the bound -/

/-- The per-`s` bound of this file for `kA4(s)`. -/
noncomputable def kA4bd (F : FockData Mode) (E : Q3Env Mode) (K₀ : ℝ) : ℝ :=
  8 * E.rho * E.ell ^ 3 * (K₀ * E.aScat)
    * (K₀ ^ 2 * eta E ^ 2 * (1 + (64 * K₀ * E.lille) ^ 2))

/-- The bracket of `sum_sq_kA4_le`. -/
noncomputable def kA4tg (F : FockData Mode) (E : Q3Env Mode) (K₀ : ℝ) : ℝ :=
  8 * (1 + (64 * K₀) ^ 2) * K₀ ^ 3 * E.rho * E.aScat * E.ell ^ 3 * eta E

lemma kA4bd_le_kA4tg (F : FockData Mode) (E : Q3Env Mode) (hv : FSParamsView E)
    {K₀ : ℝ} (hK₀ : 0 ≤ K₀) : kA4bd F E K₀ ≤ kA4tg F E K₀ := by
  have heta : 0 ≤ eta E := kA4_eta_nonneg E hv
  have hmain : eta E ^ 2 * (1 + (64 * K₀ * E.lille) ^ 2) ≤ (1 + (64 * K₀) ^ 2) * eta E := by
    have h1 : eta E ^ 2 * (1 + (64 * K₀ * E.lille) ^ 2)
        ≤ eta E ^ 2 * (1 + (64 * K₀) ^ 2) :=
      mul_le_mul_of_nonneg_left (one_add_sq_le E hv hK₀) (sq_nonneg _)
    have h2 : eta E ^ 2 * (1 + (64 * K₀) ^ 2) ≤ eta E * (1 + (64 * K₀) ^ 2) := by
      have hη1 : eta E ≤ 1 := kA4_eta_le_one E hv
      have hfac : 0 ≤ 1 + (64 * K₀) ^ 2 := by positivity
      have hηsq : eta E ^ 2 ≤ eta E := by nlinarith [heta, hη1, sq_nonneg (eta E)]
      exact mul_le_mul_of_nonneg_right hηsq hfac
    linarith
  have hconst : 0 ≤ 8 * E.rho * E.ell ^ 3 * E.aScat * K₀ ^ 3 := by
    have hρ : 0 ≤ E.rho := le_of_lt (Work.BoseB7.rho_pos E hv)
    have hl : 0 ≤ E.ell := le_of_lt (Work.BoseB7.ell_pos E hv)
    have ha : 0 ≤ E.aScat := le_of_lt hv.a_pos
    positivity
  have hexp : kA4bd F E K₀
      = (8 * E.rho * E.ell ^ 3 * E.aScat * K₀ ^ 3)
          * (eta E ^ 2 * (1 + (64 * K₀ * E.lille) ^ 2)) := by
    rw [kA4bd]; ring
  have hexp2 : kA4tg F E K₀
      = (8 * E.rho * E.ell ^ 3 * E.aScat * K₀ ^ 3) * ((1 + (64 * K₀) ^ 2) * eta E) := by
    rw [kA4tg]; ring
  rw [hexp, hexp2]
  exact mul_le_mul_of_nonneg_left hmain hconst

/-! ## 5. The theorem -/

theorem sum_sq_kA4_le (K₀ : ℝ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (hK : Work.BoseC3QAll.Q3KernelFSAll K₀ F T E) (hv : Work.BoseB7.FSParamsView E) (hK₀ : 0 ≤ K₀)
    (hAB : ∀ q : Mode, F.PHq E.KH E.aScat q → 1 / 2 ≤ 1 - E.alpha q ^ 2)
    (hα : ∀ q : Mode, F.PHq E.KH E.aScat q → |E.alpha q| ≤ 64 * K₀ * E.lille)
    (hsub : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
      F.PHq E.KH E.aScat (s - k)) :
    ∑ s ∈ Work.BoseB7.excited Mode, (Work.BoseC3QAll.kA4 F E s) ^ 2
      ≤ (K₀ * (E.Kl * E.KL) ^ 3) *
          (8 * (1 + (64 * K₀) ^ 2) * K₀ ^ 3 * E.rho * E.aScat * E.ell ^ 3
            * Work.BoseC3QAll.eta E) ^ 2 := by
  have hρ : 0 ≤ E.rho := le_of_lt (Work.BoseB7.rho_pos E hv)
  have hl : 0 ≤ E.ell := le_of_lt (Work.BoseB7.ell_pos E hv)
  have ha : 0 ≤ E.aScat := le_of_lt hv.a_pos
  have heta : 0 ≤ eta E := kA4_eta_nonneg E hv
  have hCnn : 0 ≤ K₀ ^ 2 * eta E ^ 2 * (1 + (64 * K₀ * E.lille) ^ 2) := by positivity
  have hDnn : 0 ≤ kA4bd F E K₀ := by
    rw [kA4bd]; positivity
  have hKl : 0 < E.Kl := lt_of_lt_of_le zero_lt_one hv.one_le_Kl
  have hKL : 0 < E.KL := lt_of_lt_of_le zero_lt_one hv.one_le_KL
  have hcard : 0 ≤ K₀ * (E.Kl * E.KL) ^ 3 :=
    mul_nonneg hK₀ (pow_nonneg (mul_nonneg hKl.le hKL.le) 3)
  -- the per-`s` estimate
  have hper : ∀ s : Mode, E.fL s ≠ 0 → |Work.BoseC3QAll.kA4 F E s| ≤ kA4bd F E K₀ := by
    intro s hs
    have hbr : ∀ k ∈ F.PHset E, E.W1 k ≠ 0 →
        |E.hatChi (s - k) * E.hatChi (-k)
            - E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s))|
          ≤ K₀ ^ 2 * eta E ^ 2 * (1 + (64 * K₀ * E.lille) ^ 2) :=
      fun k hk hW => chihat_bracket_le K₀ F T E hK hv hK₀ hα hsub hs hk hW
    have hden : ∀ k ∈ F.PHset E, E.W1 k ≠ 0 → |E.q3Denom s k| ≤ 4 := by
      intro k hk hW
      have h := q3Denom_bounds F E hv hAB hsub hs hk hW
      rw [abs_of_nonneg h.1]
      exact h.2
    have hterm : ∀ k ∈ F.PHset E,
        |E.W1 k * E.alpha k * E.q3Denom s k *
            (E.hatChi (s - k) * E.hatChi (-k)
              - E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s)))|
          ≤ 4 * |E.W1 k * E.alpha k|
            * (K₀ ^ 2 * eta E ^ 2 * (1 + (64 * K₀ * E.lille) ^ 2)) := by
      intro k hk
      by_cases hW : E.W1 k = 0
      · simp [hW]
      have h4 := hden k hk hW
      have hb := hbr k hk hW
      have hann : 0 ≤ |E.W1 k * E.alpha k| := abs_nonneg _
      have h1 : |E.W1 k * E.alpha k| * |E.q3Denom s k|
              * |E.hatChi (s - k) * E.hatChi (-k)
                  - E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s))|
          ≤ |E.W1 k * E.alpha k| * 4
              * |E.hatChi (s - k) * E.hatChi (-k)
                  - E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s))| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hann) (abs_nonneg _)
      have h2 : |E.W1 k * E.alpha k| * 4
              * |E.hatChi (s - k) * E.hatChi (-k)
                  - E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s))|
          ≤ |E.W1 k * E.alpha k| * 4
              * (K₀ ^ 2 * eta E ^ 2 * (1 + (64 * K₀ * E.lille) ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      calc |E.W1 k * E.alpha k * E.q3Denom s k *
            (E.hatChi (s - k) * E.hatChi (-k)
              - E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s)))|
          = |E.W1 k * E.alpha k| * |E.q3Denom s k|
              * |E.hatChi (s - k) * E.hatChi (-k)
                  - E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s))| := by
            rw [abs_mul, abs_mul]
        _ ≤ |E.W1 k * E.alpha k| * 4
              * |E.hatChi (s - k) * E.hatChi (-k)
                  - E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s))| := h1
        _ ≤ |E.W1 k * E.alpha k| * 4
              * (K₀ ^ 2 * eta E ^ 2 * (1 + (64 * K₀ * E.lille) ^ 2)) := h2
        _ = 4 * |E.W1 k * E.alpha k|
              * (K₀ ^ 2 * eta E ^ 2 * (1 + (64 * K₀ * E.lille) ^ 2)) := by ring
    have hsumW := sum_W1_alpha_le K₀ F T E hK hv
    calc |Work.BoseC3QAll.kA4 F E s|
        = |E.fL s| * |∑ k ∈ F.PHset E, E.W1 k * E.alpha k * E.q3Denom s k *
            (E.hatChi (s - k) * E.hatChi (-k)
              - E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s)))| := by
          rw [Work.BoseC3QAll.kA4, abs_mul]
      _ ≤ |E.fL s| * ∑ k ∈ F.PHset E, |E.W1 k * E.alpha k * E.q3Denom s k *
            (E.hatChi (s - k) * E.hatChi (-k)
              - E.alpha (s - k) * E.alpha (-k) * (E.hatChi k * E.hatChi (k - s)))| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
      _ ≤ |E.fL s| * ∑ k ∈ F.PHset E, 4 * |E.W1 k * E.alpha k|
            * (K₀ ^ 2 * eta E ^ 2 * (1 + (64 * K₀ * E.lille) ^ 2)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (abs_nonneg _)
      _ = |E.fL s| * (4 * (K₀ ^ 2 * eta E ^ 2 * (1 + (64 * K₀ * E.lille) ^ 2))
            * ∑ k ∈ F.PHset E, |E.W1 k * E.alpha k|) := by
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by ring)
      _ ≤ |E.fL s| * (4 * (K₀ ^ 2 * eta E ^ 2 * (1 + (64 * K₀ * E.lille) ^ 2))
            * (2 * E.rho * E.ell ^ 3 * (K₀ * E.aScat))) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply mul_le_mul_of_nonneg_left hsumW
          positivity
      _ ≤ 1 * (4 * (K₀ ^ 2 * eta E ^ 2 * (1 + (64 * K₀ * E.lille) ^ 2))
            * (2 * E.rho * E.ell ^ 3 * (K₀ * E.aScat))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [abs_of_nonneg (hK.fL_nonneg s)]
          exact hK.fL_le_one s
      _ = kA4bd F E K₀ := by rw [kA4bd]; ring
  -- the summation
  set S : Finset Mode := (excited Mode).filter (fun s => E.fL s ≠ 0) with hSdef
  have hSsub : ∀ s ∈ excited Mode, s ∉ S → (Work.BoseC3QAll.kA4 F E s) ^ 2 = 0 := by
    intro s hsmem hsS
    have hfL : E.fL s = 0 := by
      by_contra h
      exact hsS (by rw [hSdef]; exact Finset.mem_filter.mpr ⟨hsmem, h⟩)
    rw [Work.BoseC3QAll.kA4, hfL]
    simp
  have hstep1 : ∑ s ∈ excited Mode, (Work.BoseC3QAll.kA4 F E s) ^ 2 = ∑ s ∈ S, (Work.BoseC3QAll.kA4 F E s) ^ 2 :=
    (Finset.sum_subset (by rw [hSdef]; exact Finset.filter_subset _ _) hSsub).symm
  have hstep2 : ∑ s ∈ S, (Work.BoseC3QAll.kA4 F E s) ^ 2 ≤ ∑ s ∈ S, (kA4bd F E K₀) ^ 2 := by
    refine Finset.sum_le_sum fun s hs => ?_
    have hs' : s ∈ (excited Mode).filter (fun s => E.fL s ≠ 0) := by rwa [hSdef] at hs
    have hfL : E.fL s ≠ 0 := (Finset.mem_filter.mp hs').2
    have h := hper s hfL
    rw [← sq_abs (Work.BoseC3QAll.kA4 F E s)]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  calc ∑ s ∈ excited Mode, (Work.BoseC3QAll.kA4 F E s) ^ 2
      = ∑ s ∈ S, (Work.BoseC3QAll.kA4 F E s) ^ 2 := hstep1
    _ ≤ ∑ s ∈ S, (kA4bd F E K₀) ^ 2 := hstep2
    _ = (S.card : ℝ) * (kA4bd F E K₀) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (K₀ * (E.Kl * E.KL) ^ 3) * (kA4bd F E K₀) ^ 2 :=
        mul_le_mul_of_nonneg_right hK.count_PL (sq_nonneg _)
    _ ≤ (K₀ * (E.Kl * E.KL) ^ 3) * (kA4tg F E K₀) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hcard
        exact pow_le_pow_left₀ hDnn (kA4bd_le_kA4tg F E hv hK₀) 2
    _ = (K₀ * (E.Kl * E.KL) ^ 3) *
          (8 * (1 + (64 * K₀) ^ 2) * K₀ ^ 3 * E.rho * E.aScat * E.ell ^ 3
            * Work.BoseC3QAll.eta E) ^ 2 := by rw [kA4tg]

end Work.BoseC3QAll
