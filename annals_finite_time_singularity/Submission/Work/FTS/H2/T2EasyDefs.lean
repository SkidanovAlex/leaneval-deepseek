import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-! ## The block decomposition of the "easy part" `Heasy`

`Heasy α f g = H4PairInt α (f·D_z g) g - Hhard α f g` is a sum of the sixteen
`H⁴`-pairing blocks of `u = f·D_z g` against those of `g`, minus the five "hard"
terms of `Hhard`, each of which equals exactly the block product whose `g`-factor
carries all five derivatives.  Removing those five cancellations block by block
leaves `Heasy` as a sum of products

  `EasyZ f g i · GblkZ g i`     (`i ≤ 4`, weight `Whz² = w²sin(2θ)^{-η}`),
  `EasyM α f g j i · GblkM α g j i`  (`1 ≤ i`, `i+j ≤ 4`, weight `Wm² = w²sin(2θ)^{-γ}`),

where the `g`-blocks are the summands of `HkIntegrand α 4 g` and each "easy block"
has the *same* weight as its `g`-partner.  Hence the pointwise Cauchy–Schwarz
inequality bounds `|Heasy|` by `√(EasyU)·√(HkIntegrand α 4 g)`, with
`EasyU` the sum of the squares of the easy blocks.  -/

/-- The `D_z`-block of the `ℋ⁴`-integrand: `D_z^i h · w/sin(2θ)^{η/2}`. -/
def GblkZ (h : ℝ → ℝ → ℝ) (i : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => Spaces.DzIter i h z θ * Whz z θ

/-- The mixed block of the `ℋ⁴`-integrand: `D_z^j D_θ^i h · W`. -/
def GblkM (α : ℝ) (h : ℝ → ℝ → ℝ) (j i : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => Spaces.mixed j i h z θ * Wm α z θ

/-- The `D_z`-blocks of the pairing `H4PairInt α (f·D_z g) g`: for `i ≤ 3` the block is
`D_z^i(f·D_z g)`, and for `i = 4` the part surviving the cancellation against `Hhard`,
i.e. `D_z^4(f·D_z g) - f·D_z^5 g`. -/
def EasyZ (f g : ℝ → ℝ → ℝ) (i : ℕ) : ℝ → ℝ → ℝ :=
  if i ≤ 3 then
    fun z θ => Spaces.DzIter i (fun z θ => f z θ * Spaces.Dz g z θ) z θ * Whz z θ
  else
    fun z θ => (Spaces.DzIter 4 (fun z θ => f z θ * Spaces.Dz g z θ) z θ
      - f z θ * Spaces.DzIter 5 g z θ) * Whz z θ

/-- The mixed blocks of the pairing `H4PairInt α (f·D_z g) g`: for `i + j ≤ 3` the block is
`D_z^j D_θ^i (f·D_z g)`, and for `i + j = 4` the part surviving the cancellation against
`Hhard`, i.e. `D_z^j D_θ^i(f·D_z g) - f·D_z(D_z^j D_θ^i g)`. -/
def EasyM (α : ℝ) (f g : ℝ → ℝ → ℝ) (j i : ℕ) : ℝ → ℝ → ℝ :=
  if i + j ≤ 3 then
    fun z θ => Spaces.mixed j i (fun z θ => f z θ * Spaces.Dz g z θ) z θ * Wm α z θ
  else
    fun z θ => (Spaces.mixed j i (fun z θ => f z θ * Spaces.Dz g z θ) z θ
      - f z θ * Spaces.Dz (Spaces.mixed j i g) z θ) * Wm α z θ

/-- The "easy energy" of the pairing: the sum of the squares of the easy blocks, with the
same index pattern as `HkIntegrand`. -/
def EasyU (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range 5, (EasyZ f g i z θ) ^ 2)
    + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then (EasyM α f g j i z θ) ^ 2 else 0)

/-- `HkIntegrand α 4 h` is the sum of the squares of the blocks `GblkZ h i` (`i ≤ 4`) and
`GblkM α h j i` (`1 ≤ i`, `i + j ≤ 4`). -/
theorem HkIntegrand_eq_blocks (α : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Spaces.HkIntegrand α 4 h z θ =
      (∑ i ∈ Finset.range 5, (GblkZ h i z θ) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then (GblkM α h j i z θ) ^ 2 else 0) := by
  unfold Spaces.HkIntegrand GblkZ GblkM Whz Wm Spaces.Wt
  simp only [pow_two]

end Work.FTS.H2
