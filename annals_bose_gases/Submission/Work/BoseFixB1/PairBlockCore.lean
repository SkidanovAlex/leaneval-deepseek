import ChallengeDeps
import Submission.Work.BoseFixB1S.BoxQWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.PairBlockCore` — the pair-block objects of the box-projected
# `lm:appinteractionestimate` rung, placed BELOW `boxQSum_ge_a0Main_add_A2`

`Work.BoseFixB1.boxQSum_ge_a0Main_add_A2` (the rung-4 target) is about the five box words
`Work.BoseFixB1S.boxQ0 … boxQ4`.  The *per-pair* reorganisations of those words —
the five-term integrand `pairFive`, its unordered-pair recombination `pairBlock`, and the
pointwise ω-cancellation `pairFive_add_swap` — are needed by that target's own proof, but they
must be stated in a module that the target module *imports* (otherwise no lemma about them can be
used inside the target's proof: a lemma proved in a module that imports the target creates an
import cycle).

This module therefore holds exactly those objects (moved verbatim out of
`Submission/Work/BoseFixB1/boxQSum_ge_a0Main_add_A2.lean`), together with the three kernel
linearity identities (`w₁ = w(1−ω)`, `w₂ = w₁(1+ω)`) that every use of them needs.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.UBB
open Work.SmallBoxSliding
open Work.UBBInputs8

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The kernel relations used by the `ω`-cancellation

`wSmallPair` is `χ_B(x)·(h(x−y)/(χ⋆χ)((x−y)/(ℓd)))/(χ⋆χ)((x−y)/ℓ)·χ_B(y)` — *linear* in its
numerator `h`.  Hence, with `w := wSmallPair M ℓ d u v`, `w₁ := wSmall1Pair h M ℓ d u =
wSmallPair M ℓ d u (g₀ v h)` and `w₂ := wSmallPair M ℓ d u (g₂ v h)`,

    w₁ = w·(1 − ω) ,   w₂ = w₁·(1 + ω) ,   ω := omC w₀ , w₀ := Classical.choose h ,

pointwise. -/

/-- **Linearity of the localised kernel in its numerator.** -/
theorem wSmallPair_numerator_mul {M : ℕ} {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    (f g : EuclideanSpace ℝ (Fin 3) → ℝ) (x y : EuclideanSpace ℝ (Fin 3)) :
    wSmallPair M ℓ d u (fun z => f z * g z) x y
      = wSmallPair M ℓ d u f x y * g (x - y) := by
  unfold Submission.BoseGases.wSmallPair Submission.BoseGases.wSmallScaled
  ring

/-- **`w₁ = w·(1 − ω)`** pointwise (`g₀ = v(1 − ω)`). -/
theorem wSmall1Pair_eq_mul {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} {ℓ d : ℝ} (u x y : EuclideanSpace ℝ (Fin 3)) :
    wSmall1Pair h M ℓ d u x y
      = wSmallPair M ℓ d u v x y * (1 - Classical.choose h (x - y)) := by
  have hlin := wSmallPair_numerator_mul (M := M) (ℓ := ℓ) (d := d) u v
    (fun z => 1 - Classical.choose h z) x y
  have hg0 : Submission.BoseGases.g0 v h = fun z => v z * (1 - Classical.choose h z) := rfl
  rw [Submission.BoseGases.wSmall1Pair, hg0, hlin]

/-- **`w₂ = w₁·(1 + ω)`** pointwise (`g₂ = g₀(1 + ω)`). -/
theorem wSmallPair_g2_eq_mul {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} {ℓ d : ℝ} (u x y : EuclideanSpace ℝ (Fin 3)) :
    wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) x y
      = wSmall1Pair h M ℓ d u x y * (1 + Classical.choose h (x - y)) := by
  have hlin := wSmallPair_numerator_mul (M := M) (ℓ := ℓ) (d := d) u
    (Submission.BoseGases.g0 v h) (fun z => 1 + Classical.choose h z) x y
  have hg2 : Submission.BoseGases.g2 v h
      = fun z => Submission.BoseGases.g0 v h z * (1 + Classical.choose h z) := rfl
  rw [hg2, hlin, ← Submission.BoseGases.wSmall1Pair]

local notation "𝔼3" => EuclideanSpace ℝ (Fin 3)

/-! ## The exact pair decomposition of the five box words

`boxQSum − boxA2` is, by definition, `boxQ0 + (boxQ1 + boxQ2' + boxQ3 + boxQ4)` where
`boxQ2' = boxQ2 − boxA2` (the `boxA2` summand of `boxQ2` is *the same atom* as the displayed
`boxA2`).  The potential parts of the four words are `pairSet`-sums of five integrands; for one
ordered pair `p` with

    A := P_{p.1}P_{p.2}Φ ,  B := P_{p.1}Q_{p.2}Φ ,  B' := P_{p.2}Q_{p.1}Φ ,  D := Q_{p.2}Q_{p.1}Φ

they read `2BAw₂ + BB'w₂ + B²w₂ + 2BDw₁ + ½(D+ω(A+B+B'))²w`.  For the *unordered* pair the two
orientations combine to the exact identity

    2sAw₂ + s²w₂ + 2sDw₁ + (D+ω(A+s))²w = (D+s+ωA)²w + 2(1−ω)sAw ,   s := B+B' ,

i.e. a manifest square plus the single weighted cross term `2(1−ω)sAw`.  This is FS's
"the first term of `eq:Q3+Q4CS` cancels the second line of `eq:Q1n0`", done as an identity.
-/

/-- The five integrands of one ordered pair (`p`-orientation). -/
noncomputable def pairFive (volA : ℝ) (A : Set 𝔼3)
    (w w₁ w₂ : 𝔼3 → 𝔼3 → ℝ) (om : 𝔼3 → 𝔼3 → ℝ) {N : ℕ}
    (Φ : Submission.BoseGases.X N → ℝ) (p : Fin N × Fin N)
    (x : Submission.BoseGases.X N) : ℝ :=
  2 * (boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x)
      * (boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x) * w₂ (x p.1) (x p.2)
    + (boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x)
        * (boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x) * w₂ (x p.1) (x p.2)
    + (boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x)
        * (boxQInd volA A p.2 (boxPInd volA A p.1 Φ) x) * w₂ (x p.1) (x p.2)
    + 2 * ((boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x)
        * (boxQInd volA A p.2 (boxQInd volA A p.1 Φ) x)) * w₁ (x p.1) (x p.2)
    + (1 / 2) * (Work.BoseFixB1S.boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2)

/-- The pair block: square plus the weighted cross term. -/
noncomputable def pairBlock (volA : ℝ) (A : Set 𝔼3)
    (w : 𝔼3 → 𝔼3 → ℝ) (om : 𝔼3 → 𝔼3 → ℝ) {N : ℕ}
    (Φ : Submission.BoseGases.X N → ℝ) (p : Fin N × Fin N)
    (x : Submission.BoseGases.X N) : ℝ :=
  ((boxQInd volA A p.2 (boxQInd volA A p.1 Φ) x)
      + ((boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x)
          + (boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x))
      + om (x p.1) (x p.2) * (boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x)) ^ 2
    * w (x p.1) (x p.2)
  + 2 * (1 - om (x p.1) (x p.2))
      * ((boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x)
          + (boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x))
      * (boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x)
      * w (x p.1) (x p.2)

/-- **The unordered-pair identity**: the two orientations' five integrands are the block. -/
theorem pairFive_add_swap {N : ℕ} (volA : ℝ) (A : Set 𝔼3)
    (w w₁ w₂ : 𝔼3 → 𝔼3 → ℝ) (om : 𝔼3 → 𝔼3 → ℝ)
    {Φ : Submission.BoseGases.X N → ℝ} {i j : Fin N} (x : Submission.BoseGases.X N)
    (hw1 : ∀ a b : 𝔼3, w₁ a b = w a b * (1 - om a b))
    (hw2 : ∀ a b : 𝔼3, w₂ a b = w a b * (1 - om a b ^ 2))
    (hwsym : ∀ a b : 𝔼3, w a b = w b a)
    (homsym : ∀ a b : 𝔼3, om a b = om b a)
    (hPP : boxPInd volA A j (boxPInd volA A i Φ) x = boxPInd volA A i (boxPInd volA A j Φ) x)
    (hQQ : boxQInd volA A i (boxQInd volA A j Φ) x = boxQInd volA A j (boxQInd volA A i Φ) x)
    (hPQ : boxPInd volA A j (boxQInd volA A i Φ) x = boxQInd volA A i (boxPInd volA A j Φ) x)
    (hQP : boxQInd volA A j (boxPInd volA A i Φ) x = boxPInd volA A i (boxQInd volA A j Φ) x) :
    pairFive volA A w w₁ w₂ om Φ (i, j) x + pairFive volA A w w₁ w₂ om Φ (j, i) x
      = pairBlock volA A w om Φ (i, j) x := by
  have hw1s : w₁ (x j) (x i) = w₁ (x i) (x j) := by
    rw [hw1, hw1, hwsym (x i) (x j), homsym (x i) (x j)]
  have hw2s : w₂ (x j) (x i) = w₂ (x i) (x j) := by
    rw [hw2, hw2, hwsym (x i) (x j), homsym (x i) (x j)]
  have h4 : Work.BoseFixB1S.boxQ4B volA A om Φ (j, i) x = Work.BoseFixB1S.boxQ4B volA A om Φ (i, j) x := by
    simp only [Work.BoseFixB1S.boxQ4B, hQQ, homsym (x j) (x i), hPP, hPQ, hQP]
    ring
  simp only [pairFive, pairBlock, Work.BoseFixB1S.boxQ4B, hQQ, homsym (x j) (x i), hPP, hPQ, hQP,
    hw1s, hw2s, h4, hwsym (x j) (x i)]
  simp only [hw1, hw2]
  ring


/-! ## The two summands of the pair block, and the box-level square/cross split

`pairBlock = pairSq + 2·pairCross` pointwise (`pairBlock_eq_sq_add_cross`), hence
`½Σ_{p∈pairSet}∫pairBlock = boxSqPart + boxCrossPart` (`boxSqPart` collects the *manifest square*
`(D+s+ωA)²w`, which is `≥ 0` whenever `w ≥ 0` a.e., and `boxCrossPart` is the surviving *cross
term* `Σ_{i<j}∫w₁(x_i,x_j)(P_iQ_jΦ + P_jQ_iΦ)(P_iP_jΦ)`).  This is the split used by the rung-4
target `boxQSum_ge_a0Main_add_A2`: after the sum-level reduction
`Work.BoseFixB1S.boxQSum_sub_boxA2_blockSum` the target is *equivalent* to

    boxSqPart + boxCrossPart ≥ −M₁G − ½(M₂/V²)Pc + ½(M₁/V²)(S²−S) − C a(μ+S/V)n₊ + 2μP + μQ ,

so `boxSqPart ≥ 0` may be dropped and the *single* analytic statement left is a **lower** bound
for `boxCrossPart`.  Cf. `Submission/Work/BoseFixB1/FINDING_boxQSum_reduction_sign_and_sharp_constant.md`. -/

/-- The manifest square of one ordered pair: `(D + s + ωA)² w`. -/
noncomputable def pairSq (volA : ℝ) (A : Set 𝔼3) (w : 𝔼3 → 𝔼3 → ℝ)
    (om : 𝔼3 → 𝔼3 → ℝ) {N : ℕ} (Φ : Submission.BoseGases.X N → ℝ)
    (p : Fin N × Fin N) (x : Submission.BoseGases.X N) : ℝ :=
  ((boxQInd volA A p.2 (boxQInd volA A p.1 Φ) x)
      + ((boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x)
          + (boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x))
      + om (x p.1) (x p.2) * (boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x)) ^ 2
    * w (x p.1) (x p.2)

/-- The cross term of one ordered pair: `s · A · w₁` with `s = P_iQ_jΦ + P_jQ_iΦ`, `A = P_iP_jΦ`
(note `pairBlock = pairSq + 2·pairCross`, using `w₁ = w(1−ω)`). -/
noncomputable def pairCross (volA : ℝ) (A : Set 𝔼3) (w₁ : 𝔼3 → 𝔼3 → ℝ)
    {N : ℕ} (Φ : Submission.BoseGases.X N → ℝ)
    (p : Fin N × Fin N) (x : Submission.BoseGases.X N) : ℝ :=
  ((boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x)
      + (boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x))
    * (boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x) * w₁ (x p.1) (x p.2)

/-- **`pairBlock = pairSq + 2·pairCross`** pointwise (pure algebra, using `w₁ = w(1−ω)`). -/
theorem pairBlock_eq_sq_add_cross {N : ℕ} (volA : ℝ) (A : Set 𝔼3)
    (w w₁ : 𝔼3 → 𝔼3 → ℝ) (om : 𝔼3 → 𝔼3 → ℝ)
    {Φ : Submission.BoseGases.X N → ℝ} (p : Fin N × Fin N) (x : Submission.BoseGases.X N)
    (hw1 : ∀ a b : 𝔼3, w₁ a b = w a b * (1 - om a b)) :
    pairBlock volA A w om Φ p x = pairSq volA A w om Φ p x + 2 * pairCross volA A w₁ Φ p x := by
  simp only [pairBlock, pairSq, pairCross]
  rw [hw1 (x p.1) (x p.2)]
  ring

/-- The manifest-square part of `½Σ_{p∈pairSet}∫pairBlock`. -/
noncomputable def boxSqPart {N : ℕ} (volA ℓ : ℝ) (A : Set 𝔼3)
    (w : 𝔼3 → 𝔼3 → ℝ) (om : 𝔼3 → 𝔼3 → ℝ) (Φ : Submission.BoseGases.X N → ℝ) : ℝ :=
  (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet N,
    ∫ x in Submission.BoseGases.abox N ℓ, pairSq volA A w om Φ p x

/-- The surviving cross-term part of `½Σ_{p∈pairSet}∫pairBlock`. -/
noncomputable def boxCrossPart {N : ℕ} (volA ℓ : ℝ) (A : Set 𝔼3)
    (w₁ : 𝔼3 → 𝔼3 → ℝ) (Φ : Submission.BoseGases.X N → ℝ) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet N,
    ∫ x in Submission.BoseGases.abox N ℓ, pairCross volA A w₁ Φ p x


/-- **The square/cross split of the pair-block sum** (PROVED): with `w₁ = w(1−ω)`,
`pairBlock = pairSq + 2·pairCross` pointwise, so summing and integrating,

    (1/2)·Σ_{p∈pairSet}∫pairBlock = boxSqPart + boxCrossPart .

The three `IntegrableOn` hypotheses are what the `integral_add`/`integral_const_mul` steps need;
they are *not* automatic from the target's hypotheses (`w` is only `L¹`-dominated, not continuous). -/
theorem boxSqPart_add_boxCrossPart_eq_blockSum {N : ℕ} {ℓ volA : ℝ}
    {A : Set 𝔼3} {w w₁ : 𝔼3 → 𝔼3 → ℝ} {om : 𝔼3 → 𝔼3 → ℝ}
    {Φ : Submission.BoseGases.X N → ℝ}
    (hintSq : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => pairSq volA A w om Φ p x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hintCr : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => pairCross volA A w₁ Φ p x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hintBlk : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => pairBlock volA A w om Φ p x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hw1 : ∀ a b : 𝔼3, w₁ a b = w a b * (1 - om a b)) :
    (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ, pairBlock volA A w om Φ p x
      = boxSqPart volA ℓ A w om Φ + boxCrossPart volA ℓ A w₁ Φ := by
  have hper : ∀ p ∈ Submission.BoseGases.pairSet N,
      (∫ x in Submission.BoseGases.abox N ℓ, pairBlock volA A w om Φ p x)
        = (∫ x in Submission.BoseGases.abox N ℓ, pairSq volA A w om Φ p x)
          + 2 * (∫ x in Submission.BoseGases.abox N ℓ, pairCross volA A w₁ Φ p x) := by
    intro p hp
    have hpt : (fun x : Submission.BoseGases.X N => pairBlock volA A w om Φ p x)
        = fun x => pairSq volA A w om Φ p x + 2 * pairCross volA A w₁ Φ p x := by
      funext x
      exact pairBlock_eq_sq_add_cross volA A w w₁ om p x hw1
    rw [hpt]
    rw [MeasureTheory.integral_add (hintSq p hp) ((hintCr p hp).const_mul 2)]
    rw [show (∫ x in Submission.BoseGases.abox N ℓ, 2 * pairCross volA A w₁ Φ p x)
        = 2 * (∫ x in Submission.BoseGases.abox N ℓ, pairCross volA A w₁ Φ p x)
        from MeasureTheory.integral_const_mul 2 _]
  rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold boxSqPart boxCrossPart
  ring

end Work.BoseFixB1
