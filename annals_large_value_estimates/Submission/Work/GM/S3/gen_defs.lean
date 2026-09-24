import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.prop101_defs

/-!
# The §10 objects of GM Prop 10.1 with **three independent dyadic scales**

`Submission/Work/GM/S3/prop101_defs.lean` fixes the objects of GM's Proposition 10.1 for a box with
a *single* dyadic scale `M` in the two "large" slots (`idxM M` in the `m₂`- and `m₃`-slots) and a
`m₁`-scale `M₁ ≤ M`:

`S30 = Σ_{m₁∈idx1 M₁}Σ_{m₂∈idxM M}Σ_{m₃∈idxM M} ∫_{1/2}^{2} ‖R(v)‖ R̃(a₁)R̃(a₂) dv`,

together with the intermediate objects `Gsum`, `S32 = ∫ G²`, `Asum`, `Bsum`, `S33 = ∫ Asum²`,
`S34 = ∫ Bsum²` of the two Cauchy–Schwarz steps.

**Why this file exists.**  GM's Proposition 7.2 has `|m₂|,|m₃| ≍ M` (comparability up to an
absolute constant) and `|m₁| ∼ M₁` (dydadic).  The formal interface `Prop72RelaxedStatement` (and
the in-flight `SumStepRelaxedStatement`) sharpens `≍` to the *strict factor two* window
`M < |m₂|,|m₃| ≤ 2M`.  The team's analysis (`NOTES_prop72_session5.md`,
`NOTES_prop72_relaxed_reduction.md`) found that this strict form is a genuine strengthening: the
constraint region of Proposition 7.1 only forces the two largest coordinates to lie within a
*factor four* of each other, so triples whose two largest coordinates straddle a dyadic boundary
(ratio in `(2,4]`) lie in **no** strict factor-two box.  Covering them requires a box with
*independent* dyadic windows in the three slots, and then the §10 argument has to bound
*each* such cell.

The objects below are therefore the verbatim analogues of `S30`, `Gsum`, `S32`, `Asum`, `Bsum`,
`S33`, `S34` with `idxM M` replaced by `idxM M₂` / `idxM M₃` in the two large slots:

* `S30g N W B M₁ M₂ M₃ ψ₁ ψ₂` — the cell sum;
* `Gsumg`, `S32g` — the Cauchy–Schwarz intermediate `Σ_m R̃(a₁)R̃(a₂)` and its `L²` integral;
* `Asumg`, `S33g` — the `a₁`-factor, `Bsumg`, `S34g` — the `a₂`-factor;
* `AsumInvg`, `AsumgPos`, `BsumgPos`, `AsumInvgPos` — the auxiliary `u = 1/v` forms.

The scale machinery for the *family of cells* of the §7 decomposition is also here:

* `Klev N δ = (M N)^{1+δ}/N` — the truncation level of `s3_tail_noclash`;
* `Mdy N δ j = Klev N δ / 2^j` — the dyadic scale of level `j` (the window `Mdy j < |m| ≤ 2 Mdy j`);
* `Bdy N δ η j = Mdy N δ j / (2 (M N)^η)` — the smoothing attached to a cell whose *second* slot
  has scale `Mdy j` (matched: the per-`m` estimate `norm_Iterm_le_Rtilde_of_domain` needs
  `B (M N)^η ≤ |m₂|/2`, and slot 2 of a cell of scale `Mdy j` has `|m₂| > Mdy j`);
* `cellJ N = 4 (log₂ N + 1) + 256` — the number of levels (the windows `(M(j),2M(j)]`, `j < cellJ`,
  cover the whole truncation range for large `N`);
* `cellFam N δ η J` — the family of cells `(i,j,k)` with `j ≤ i`, `j ≤ k` (the second slot has the
  largest scale up to a factor two) and `32 ≤ N B(j)` (so that the cell bound applies);
* `cellSum N W δ η J ψ₁ ψ₂` — the resulting right hand side `Σ_{(i,j,k)} (N²/B(j)) · S30g(cell)`.
-/

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators

open Submission.GM (Rfun energy Separated Iterm Spart affineSum)

namespace Gen

noncomputable section

/-! ## The generalized §10 objects -/

/-- GM 10.1: `S₃,₀` for a cell with scales `M₁, M₂, M₃` in the three slots and smoothing `B`. -/
def S30g (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) : ℝ :=
  ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxM M₂, ∑ m₃ ∈ idxM M₃,
    ∫ v in (1 / 2 : ℝ)..2, ‖Rfun W v‖ *
      Rtilde W N B ψ₁ ψ₂ (arg1 m₁ m₂ m₃ v) * Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v)

/-- The inner sum `G(v) = Σ_m R̃(a₁(m,v)) R̃(a₂(m,v))` of `S30g`. -/
def Gsumg (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxM M₂, ∑ m₃ ∈ idxM M₃,
    Rtilde W N B ψ₁ ψ₂ (arg1 m₁ m₂ m₃ v) * Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v)

/-- `S₃,₂ = ∫_{1/2}^2 G(v)² dv`. -/
def S32g (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) : ℝ :=
  ∫ v in (1 / 2 : ℝ)..2, (Gsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v) ^ 2

/-- `Σ_m R̃(a₁(m,v))²`. -/
def Asumg (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxM M₂, ∑ m₃ ∈ idxM M₃,
    Rtilde W N B ψ₁ ψ₂ (arg1 m₁ m₂ m₃ v) ^ 2

/-- `Σ_m R̃(a₂(m,v))²`. -/
def Bsumg (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxM M₂, ∑ m₃ ∈ idxM M₃,
    Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v) ^ 2

/-- `S₃,₃ = ∫_{1/2}^2 (Σ_m R̃(a₁(m,v))²)² dv`. -/
def S33g (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) : ℝ :=
  ∫ v in (1 / 2 : ℝ)..2, (Asumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v) ^ 2

/-- `S₃,₄ = ∫_{1/2}^2 (Σ_m R̃(a₂(m,v))²)² dv`. -/
def S34g (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) : ℝ :=
  ∫ v in (1 / 2 : ℝ)..2, (Bsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v) ^ 2

/-- The `u = 1/v` form of `Asumg`: `Σ_m R̃((m₃u + m₁)/m₂)²`. -/
def AsumInvg (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxM M₂, ∑ m₃ ∈ idxM M₃,
    Rtilde W N B ψ₁ ψ₂ (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)) ^ 2

/-- The `m₂ > 0` part of `Asumg`. -/
def AsumgPos (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M₂, ∑ m₃ ∈ idxM M₃,
    Rtilde W N B ψ₁ ψ₂ (arg1 m₁ m₂ m₃ v) ^ 2

/-- The `m₂ > 0` part of `Bsumg`. -/
def BsumgPos (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M₂, ∑ m₃ ∈ idxM M₃,
    Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v) ^ 2

/-- The `m₂ > 0` part of `AsumInvg`. -/
def AsumInvgPos (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M₂, ∑ m₃ ∈ idxM M₃,
    Rtilde W N B ψ₁ ψ₂ (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)) ^ 2

/-! ## The scale machinery of the cell decomposition -/

/-- The truncation level of `Work.GM.S3.s3_tail_noclash`: `K = (M N)^{1+δ}/N`. -/
def Klev (N : ℕ) (δ : ℝ) : ℝ := (Submission.LargeValues.M N) ^ (1 + δ) / (N : ℝ)

/-- The dyadic scale of level `j`: `M(j) = K/2^j`.  The window of level `j` is
`M(j) < |m| ≤ 2 M(j)`, i.e. `K/2^j < |m| ≤ K/2^{j-1}`; these windows (`j ≥ 1`) partition `(0,K]`. -/
def Mdy (N : ℕ) (δ : ℝ) (j : ℕ) : ℝ := Klev N δ / 2 ^ j

/-- The smoothing attached to a cell whose second slot has scale `M(j)`: `B(j) = M(j)/(2 T^η)`,
the *matched* smoothing (`norm_Iterm_le_Rtilde_of_domain` needs `B T^η ≤ |m₂|/2`, and a cell of
scale `M(j)` has `|m₂| > M(j)`). -/
def Bdy (N : ℕ) (δ η : ℝ) (j : ℕ) : ℝ := Mdy N δ j / (2 * (Submission.LargeValues.M N) ^ η)

/-- The number of dyadic levels used by the cell decomposition.  It must exceed
`log₂ (Klev N δ)` for the covering (every integer `t ∈ [1, Klev]` must have a window index
`< cellJ`), and `log₂ (Klev/(T^η/N))`.  Since `Klev = N^{(1+6δ)/5}` the leading term must carry
the factor `⌈δ⌉`; the `8 ⌈δ⌉ (log₂ N + 1)` below does, and for the *small* exponents `δ'` used in
the final assembly (`⌈δ'⌉ = 1`) it is `8 (log₂ N + 1) + 256 = O(log N)`. -/
def cellJ (N : ℕ) (δ : ℝ) : ℕ := 8 * Nat.ceil δ * (Nat.log 2 N + 1) + 256

/-- The family of cells `(i,j,k)`: the second slot has the largest scale up to a factor two
(`j ≤ i`, `j ≤ k`), and the cell's smoothing satisfies `32 ≤ N B(j)` so that the cell bound
`Work.GM.S3.Gen.S30g_le_cell` applies. -/
def cellFam (N : ℕ) (δ η : ℝ) (J : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (((Finset.range J) ×ˢ (Finset.range J) ×ˢ (Finset.range J)).filter
    (fun p : ℕ × (ℕ × ℕ) => p.2.1 ≤ p.1 ∧ p.2.1 ≤ p.2.2 ∧
      32 ≤ (N : ℝ) * Bdy N δ η p.2.1))

/-- The right hand side produced by the cell decomposition of GM 7.2:
`Σ_{(i,j,k)} (N²/B(j)) · S30g` over the family `cellFam`. -/
def cellSum (N : ℕ) (W : Finset ℝ) (δ η : ℝ) (J : ℕ) (ψ₁ ψ₂ : ℝ → ℝ) : ℝ :=
  ∑ p ∈ cellFam N δ η J, ((N : ℝ) ^ 2 / Bdy N δ η p.2.1) *
    S30g N W (Bdy N δ η p.2.1) (Mdy N δ p.1) (Mdy N δ p.2.1) (Mdy N δ p.2.2) ψ₁ ψ₂

/-! ## Elementary facts -/

/-- The index sets `idxM` are symmetric under negation. -/
theorem mem_idxM_neg_iff {M : ℝ} {m : ℤ} : -m ∈ idxM M ↔ m ∈ idxM M := by
  simp only [idxM, mem_filter, mem_Icc, Int.cast_neg, abs_neg]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, h2⟩

/-- The index set `idx1` is symmetric under negation. -/
theorem mem_idx1_neg_iff {M : ℝ} {m : ℤ} : -m ∈ idx1 M ↔ m ∈ idx1 M := by
  simp only [idx1, mem_filter, mem_Icc, Int.cast_neg, abs_neg]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, h2⟩

/-- `Rtilde` is non-negative (definitionally a square root). -/
theorem Rtilde_nonneg' (W : Finset ℝ) (N : ℕ) (B : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (u : ℝ) :
    0 ≤ Rtilde W N B ψ₁ ψ₂ u := Real.sqrt_nonneg _

/-- `S30g` is non-negative. -/
theorem S30g_nonneg (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) :
    0 ≤ S30g N W B M₁ M₂ M₃ ψ₁ ψ₂ := by
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    Finset.sum_nonneg fun c _ => ?_
  refine intervalIntegral.integral_nonneg (by norm_num) fun v _ => ?_
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (Rtilde_nonneg' ..)) (Rtilde_nonneg' ..)

/-- `Gsumg`-summands are non-negative only if both `R̃` are; the products themselves need not be.

This is the identity expressing the `m ↦ -m` invariance of the *arguments*:
`arg1 (-m₁) (-m₂) (-m₃) v = arg1 m₁ m₂ m₃ v` and likewise for `arg2`. -/
theorem arg1_neg (m₁ m₂ m₃ : ℤ) (v : ℝ) :
    arg1 (-m₁) (-m₂) (-m₃) v = arg1 m₁ m₂ m₃ v := by
  simp only [arg1]
  push_cast
  ring

/-- `arg2` is invariant under `m ↦ -m`. -/
theorem arg2_neg (m₁ m₂ m₃ : ℤ) (v : ℝ) :
    arg2 (-m₁) (-m₂) (-m₃) v = arg2 m₁ m₂ m₃ v := by
  simp only [arg2]
  push_cast
  ring

/-- `Bdy` is positive for `N ≥ 1` when `Klev > 0`. -/
theorem Bdy_pos {N : ℕ} {δ η : ℝ} {j : ℕ} (hN : 1 ≤ N) (hK : 0 < Klev N δ) :
    0 < Bdy N δ η j := by
  have hM1 : (1 : ℝ) ≤ Submission.LargeValues.M N := Submission.LargeValues.M_ge_one hN
  have hT : 0 < (Submission.LargeValues.M N) ^ η := Real.rpow_pos_of_pos (by linarith) η
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  simp only [Bdy, Mdy]
  positivity

end

end Gen

end Work.GM.S3
