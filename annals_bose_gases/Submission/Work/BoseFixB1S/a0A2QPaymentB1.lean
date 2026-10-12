import ChallengeDeps
import Submission.Work.BoseFixB1.boxPairBlockIntegrable
import Submission.Work.BoseFixB1.boxQ0SlackIntegrable
import Submission.Work.BoseFixB1S.Clean.Fragments
import Submission.Work.BoseFixB1S.Clean.Target
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.a0A2QPaymentB1` — rung 4 of FS `lm:appinteractionestimate`

**STATUS: the statement is FALSE as written** (it is missing the state-localisation hypothesis of
FS's setting).  Details, the exact equivalence that exhibits the defect, and the refuting family:
`Submission/Work/BoseFixB1S/FINDING_boxCrossJoint_false.md` (and the sibling
`FINDING_boxHopArith_false.md`, `FINDING_boxHopArithB_false.md` for the same mechanism).  Short
version: for every `Φ` the rung-4 inequality is *equivalent* (by the Lean-proved reduction (R1)
`Work.BoseFixB1S.Clean.boxQSum_sub_boxA2_blockSum`, the slack identity
`Work.BoseFixB1.boxQ0_sub_a0MainLocBox_eq`, and the sorry-free
`Work.BoseFixB1S.boxPairManifestSumB1S`) to

    (T′) Σ_{i<j}∫1_A(xᵢ)1_A(xⱼ)Φ²w + M₁G + C·a(v)(μ+S/V)n₊ ≥ 2μP + μQ + boxA2 + ½(M₁/V²)(S²−S) ,

and `(T′)` fails for the (admissible) product state `Φ = a·⊗u₀` with `u₀` a bump supported where
the cutoff `χ_B = chiSmallB M ℓ d u` vanishes: then the square term is `0` exactly
(`w = χ_B(x)(…)(x−y)χ_B(y)`) while `boxA2 = Θ(N)` — the required constant grows linearly in `N`.

**What is nevertheless proved here and reusable for a repaired statement.**  The whole assembly of
`BoseFixB1/a0SectorLower.lean` is transcribed into the proof of the theorem below (so the statement
is reduced, *inside this module*, to the single analytic hypothesis `have hcross : … := by sorry`,
whose type is the *joint* form `(★★)`: the same inequality with `boxSqPart` and the
pair-condensate slack `½(M₂/V²)Pc − ½(M₁/V²)(S²−S)` kept on the left), together with the local
arithmetic core `Work.BoseFixB1S.boxTarget_of_joint`.  Adding FS's localisation hypothesis (e.g.
`Φ` supported in `(dlBox ℓ d u)^N`, equivalently `n₀ + n₊ = N` on the support) to both the target
and `(★★)` makes them the true FS lemma, and then the same assembly finishes the proof.
Also proved here: `boxPairWordCancel`, `boxQSum_reduce`, `boxPairBlock_eq_twoOrient`,
`boxPairFive_add_swap`, `boxPairFive_integrable`, `boxPairSum_fold`,
`boxPairFive_add_swap_integral_local`, `boxWordPairSum` (the words-to-block identity).
-/

namespace Work.BoseFixB1S

open Submission.BoseGases

/-! ## The exact per-pair `ω`-cancellation

For one unordered pair `{i,j}`, the ordered pairs `(i,j)` and `(j,i)` contribute to
`boxQ1 + (boxQ2 − boxA2) + boxQ3 + boxQ4` the ten pointwise terms below; with
`D := Q_jQ_iΦ`, `s := P_iQ_jΦ + P_jQ_iΦ`, `ā := P_iP_jΦ`, `ω := om (x i) (x j)`,
`w₁ = w(1−ω)`, `w₂ = w(1−ω²)` they collapse **exactly** to a manifest square plus one weighted
cross term:

    2 s ā w₂ + s² w₂ + 2 s D w₁ + ½[(q4B_{ij})² + (q4B_{ji})²] w = (D + s + ω ā)² w + 2(1−ω) s ā w .

This is FS `final_v2.tex` l.3718 ("*the first term of eq:Q3+Q4CS cancels the second line of
eq:Q1n0*") done as an identity; see `Submission/Work/BoseFixB1S/NOTES_a0A2Q_reduction.md` §1. -/
lemma boxPairWordCancel {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w₁ w₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    {Φ : Submission.BoseGases.X N → ℝ} {i j : Fin N} (x : Submission.BoseGases.X N)
    (hw1 : ∀ a b : EuclideanSpace ℝ (Fin 3), w₁ a b = w a b * (1 - om a b))
    (hw2 : ∀ a b : EuclideanSpace ℝ (Fin 3), w₂ a b = w a b * (1 - om a b ^ 2))
    (hwsym : ∀ a b : EuclideanSpace ℝ (Fin 3), w a b = w b a)
    (homsym : ∀ a b : EuclideanSpace ℝ (Fin 3), om a b = om b a)
    (hPP : Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
        = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
    (hQQ : Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
        = Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
    (hPQ : Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
        = Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
    (hQP : Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
        = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) :
    2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
        * (w₂ (x i) (x j))
      + 2 * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
          * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)
          * (w₂ (x j) (x i))
      + (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
          * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
          * (w₂ (x i) (x j))
      + (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
          * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
          * (w₂ (x j) (x i))
      + (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) ^ 2
          * (w₂ (x i) (x j))
      + (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2
          * (w₂ (x j) (x i))
      + 2 * ((Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
              * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x))
          * (w₁ (x i) (x j))
      + 2 * ((Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
              * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x))
          * (w₁ (x j) (x i))
      + (1 / 2) * ((boxQ4B volA A om Φ (i, j) x) ^ 2 + (boxQ4B volA A om Φ (j, i) x) ^ 2)
          * (w (x i) (x j))
    = ((Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
          + ((Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
              + (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x))
          + om (x i) (x j)
              * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)) ^ 2
        * (w (x i) (x j))
      + 2 * (1 - om (x i) (x j))
          * ((Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
              + (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x))
          * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
          * (w (x i) (x j)) := by
  have hw1s : w₁ (x j) (x i) = w₁ (x i) (x j) := by
    rw [hw1, hw1, hwsym (x i) (x j), homsym (x i) (x j)]
  have hw2s : w₂ (x j) (x i) = w₂ (x i) (x j) := by
    rw [hw2, hw2, hwsym (x i) (x j), homsym (x i) (x j)]
  have h4 : boxQ4B volA A om Φ (j, i) x = boxQ4B volA A om Φ (i, j) x := by
    simp only [boxQ4B, hQQ, homsym (x j) (x i), hPP, hPQ, hQP]
    ring
  simp only [boxQ4B, hQQ, homsym (x j) (x i), hPP, hPQ, hQP, hw1s, hw2s]
  simp only [hw1, hw2]
  ring_nf

/-! ## The sum-level regrouping (`boxWordPairSum`)

`boxPairWordCancel` is the per-*unordered*-pair identity: the two orientations' ten terms equal
`boxPairBlock`.  Summing it over `pairSet N` (each unordered pair counted twice, once as `p` and
once as `p.swap` — `Submission.PotWords.pairSet_swap_sum` is the reindexing) rewrites the whole
pair part of `boxQ1 + boxQ2 + boxQ3 + boxQ4 − boxA2` as the pair-block sum; the `μ`-lines and the
`boxA2` summand are carried explicitly on the left so that the identity is an equality of the
*definitions*.  Proof plan (all parts available):
* `BoxPotOper.boxPPswap/boxQQswap/boxPQswap/boxQPswap` supply the four swap hypotheses of
  `boxPairWordCancel` (they need `hℓ hvol hA hvolA hAc hij hΦc` and, for the `PQ`/`QP` ones,
  `x ∈ abox N ℓ`);
* the ten integrands are merged into one pointwise sum with `integral_add`/`integral_sum`
  (under the stated `IntegrableOn` hypotheses);
* `PotWords.pairSet_swap_sum` does the `Finset` reindexing. -/
noncomputable def boxPairBlock (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) {N : ℕ}
    (Φ : Submission.BoseGases.X N → ℝ) (p : Fin N × Fin N) (x : Submission.BoseGases.X N) : ℝ :=
  ((Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
      + ((Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          + (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x))
      + om (x p.1) (x p.2)
          * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)) ^ 2
    * w (x p.1) (x p.2)
  + 2 * (1 - om (x p.1) (x p.2))
      * ((Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          + (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x))
      * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
      * w (x p.1) (x p.2)

/-! ## Step (i) of the merge: the raw ordered-pair sums

Unfold the five box words, cancel the two `μ`-fibre lines against the ones carried on the left,
cancel `boxA2` against `boxQ2`'s fourth summand (they are the *same* `pairSet`-sum, hence the same
atom), and collect the pair part as the five raw ordered-pair sums.  Pure unfolding + `ring`. -/
theorem boxQSum_reduce {N : ℕ} (volA ℓ μ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w₁ w₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) :
    boxQ1 volA ℓ μ A w₁ w₂ Φ
        + (boxQ2 volA ℓ μ A w₁ w₂ Φ - Work.BoseFixB1.boxA2 ℓ volA A w₁ Φ)
        + boxQ3 volA ℓ A w₁ Φ + boxQ4 volA ℓ A w om Φ
        + 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x)
              * (Work.UBBInputs8.boxPInd volA A i Φ x)
              * Submission.BoseGases.w1Fibre ℓ w₁ (x i))
        + μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2
              * Submission.BoseGases.w1Fibre ℓ w₁ (x i))
      = 2 * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxPInd volA A p.1
                    (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
                * w₂ (x p.1) (x p.2))
        + (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxPInd volA A p.2
                    (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
                * w₂ (x p.1) (x p.2))
        + (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxQInd volA A p.2
                    (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
                * w₂ (x p.1) (x p.2))
        + 2 * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxQInd volA A p.2
                    (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
                * w₁ (x p.1) (x p.2))
        + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2)) := by
  simp only [boxQ1, boxQ2, boxQ3, boxQ4, Work.BoseFixB1.boxA2]
  ring

/-- **The bridge between the engine `boxPairWordCancel` and the definition `boxPairBlock`**:
the two orientations' five-term integrand sums *are* the block.  This is the form the merge
consumes — with `pairSet_swap_sum` it turns `Σ_{p ∈ pairSet} ∫[5 ordered terms](p)` into
`½ Σ_{p ∈ pairSet} ∫ boxPairBlock p`.

(Note: the *single*-orientation identity "`[5 terms](p) = ½ boxPairBlock p`" would be FALSE —
it would need `P_iQ_jΦ = P_jQ_iΦ`; only the two-orientation sum is the block.) -/
lemma boxPairBlock_eq_twoOrient {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w₁ w₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    {Φ : Submission.BoseGases.X N → ℝ} {i j : Fin N} (x : Submission.BoseGases.X N)
    (hw1 : ∀ a b : EuclideanSpace ℝ (Fin 3), w₁ a b = w a b * (1 - om a b))
    (hw2 : ∀ a b : EuclideanSpace ℝ (Fin 3), w₂ a b = w a b * (1 - om a b ^ 2))
    (hwsym : ∀ a b : EuclideanSpace ℝ (Fin 3), w a b = w b a)
    (homsym : ∀ a b : EuclideanSpace ℝ (Fin 3), om a b = om b a)
    (hPP : Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
        = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
    (hQQ : Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
        = Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
    (hPQ : Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
        = Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
    (hQP : Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
        = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) :
    2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
        * (w₂ (x i) (x j))
      + 2 * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
          * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)
          * (w₂ (x j) (x i))
      + (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
          * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
          * (w₂ (x i) (x j))
      + (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
          * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
          * (w₂ (x j) (x i))
      + (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) ^ 2
          * (w₂ (x i) (x j))
      + (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2
          * (w₂ (x j) (x i))
      + 2 * ((Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
              * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x))
          * (w₁ (x i) (x j))
      + 2 * ((Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
              * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x))
          * (w₁ (x j) (x i))
      + (1 / 2) * ((boxQ4B volA A om Φ (i, j) x) ^ 2 + (boxQ4B volA A om Φ (j, i) x) ^ 2)
          * (w (x i) (x j))
      = boxPairBlock volA A w om Φ (i, j) x := by
  have hw1s : w₁ (x j) (x i) = w₁ (x i) (x j) := by
    rw [hw1, hw1, hwsym (x i) (x j), homsym (x i) (x j)]
  have hw2s : w₂ (x j) (x i) = w₂ (x i) (x j) := by
    rw [hw2, hw2, hwsym (x i) (x j), homsym (x i) (x j)]
  rw [boxPairBlock]
  simp only [boxQ4B, hQQ, homsym (x j) (x i), hPP, hPQ, hQP, hw1s, hw2s]
  simp only [hw1, hw2]
  ring_nf

/-- **The arithmetic core, in the *joint* (square-keeping) form.**  This is
`Work.BoseFixB1.boxTarget_of_pieces` with its hypothesis `(♦)` replaced by the *weaker* (hence
easier, and the one FS actually prove) form `(★★)` in which the manifest square `Sqp` and the
pair-condensate slack `pcb := ½(M₂/V²)Pc − ½(M₁/V²)(S²−S)` are kept on the left.  Note
`(♦) ⟹ (★★)` but *not* conversely (`(★★)` has the bigger left-hand side), so `(★★)` is the
correct target for the analytic core — see `NOTES_crux_boxCrossLower.md`. -/
theorem boxTarget_of_joint {V μ M₁ M₂ S Pc nq C aa Sqp L P Q Q0 A2 Qsum a0 : ℝ}
    (hV : 0 < V) (hM1 : 0 ≤ M₁) (hM2 : M₁ ≤ M₂) (hPc : 0 ≤ Pc) (hcS2 : S * S - S ≤ Pc)
    (hred : Qsum - A2 + (2 * μ * P + μ * Q) = Q0 + (Sqp + L))
    (hslack : Q0 - a0 = M₁ * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
        + (1 / 2) * (M₂ / V ^ 2) * Pc - (1 / 2) * (M₁ / V ^ 2) * (S ^ 2 - S))
    (hjoint : Sqp + L + M₁ * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
        + (1 / 2) * (M₂ / V ^ 2) * Pc - (1 / 2) * (M₁ / V ^ 2) * (S ^ 2 - S)
        + C * aa * (μ + S / V) * nq ≥ 2 * μ * P + μ * Q) :
    a0 + A2 - C * aa * (μ + S / V) * nq ≤ Qsum := by
  linarith [hred, hslack, hjoint]

theorem a0A2QPaymentB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
        (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
        (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
        (hμv : 1 ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u)
        {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
        (hM1nn : 0 ≤ Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u))
        (hM2 : Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)))
        (hPcnn : 0 ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ)
        (hcS2 : Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
              ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ),
        Work.BoseFixB1.a0MainLocBox (Work.SmallBoxSliding.boxMass ℓ d u) μ
            (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u))
            (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ)
          + Work.BoseFixB1.boxA2 ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
          - C * (_root_.BoseGases.a v)
              * (μ + Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u)
              * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
        ≤ Work.BoseFixB1S.boxQSum (Work.SmallBoxSliding.boxMass ℓ d u) ℓ μ
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
            (Submission.BoseGases.omC (Classical.choose h)) Φ := by
  classical
  /- **`(★★)` — the single analytic input, in its *joint* (square-keeping) form**, exactly the
  statement delegated at `Submission/Work/BoseFixB1S/boxCrossJoint.lean`
  (`Work.BoseFixB1S.boxCrossJoint`).  The manifest square `boxSqPart` and the pair-condensate
  slack `½(M₂/V²)Pc − ½(M₁/V²)(S²−S)` are KEPT on the left — this is the form FS actually prove
  (`eq:Q1n0` + `eq:Q3+Q4CS`, `final_v2.tex` l.3726–3740, with `Q₄` and the pair term kept), and
  it is *strictly weaker* than the `(♦)` of the corpus's `Work.BoseFixB1.boxCrossLower` (whose
  left-hand side drops both).  `(♦)` is not implied by the paper's argument; `(★★)` is exactly
  what `boxTarget_of_joint` above consumes.

  Once `BoseFixB1S/boxCrossJoint.lean` lands, **replace this `sorry` by**
  `Work.BoseFixB1S.boxCrossJoint hv_supp hR0 hv hvrad hv1 h hM`
  — nothing else in the proof below has to change.  See
  `Submission/Work/BoseFixB1S/NOTES_crux_boxCrossLower.md` for the analysis of the crux
  (it is FS's completion-of-squares chapter with the operator weights `n₀^{1/2} ± (μV)^{1/2}`;
  the naive Cauchy–Schwarz chain provably does *not* close, its required constant growing
  like `√N`). -/
  have hcross : ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
        (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
        (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
        (hμv : 1 ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u)
        {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
        (hM1nn : 0 ≤ Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u))
        (hM2 : Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)))
        (hPcnn : 0 ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ)
        (hcS2 : Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
              ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ),
        Work.BoseFixB1.boxSqPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.omC (Classical.choose h)) Φ
          + Work.BoseFixB1.boxCrossPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
          + Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            * ((1 / 4) * (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u - μ) ^ 2
                + (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u + μ)
                  / (2 * Work.SmallBoxSliding.boxMass ℓ d u)
                + 1 / (4 * Work.SmallBoxSliding.boxMass ℓ d u ^ 2))
          + (1 / 2) * (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
                / Work.SmallBoxSliding.boxMass ℓ d u ^ 2)
              * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
          - (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmall1Pair h M ℓ d u)
                / Work.SmallBoxSliding.boxMass ℓ d u ^ 2)
              * (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ ^ 2
                  - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ)
          + C * (_root_.BoseGases.a v)
              * (μ + Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u)
              * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
        ≥ 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x)
                * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) i Φ x)
                * Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
          + μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
                * Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)) := by
    sorry
  obtain ⟨C, hC0, hC⟩ := hcross
  refine ⟨C, hC0, ?_⟩
  intro ℓ d μ hℓ hd hμ hR hRχ u hvol hμv N Φ hΦc hM1nn hM2 hPcnn hcS2
  -- ## the sliding-box data
  have hVpos : (0 : ℝ) < Work.SmallBoxSliding.boxMass ℓ d u := hvol
  have hAmeas : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hvolA : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  -- ## the integrability bundles (proved, cycle-free copies of the corpus modules)
  obtain ⟨hint0, hint1, hint2, hint3, hint4, hint5⟩ :=
    Work.BoseFixB1.Clean.boxFragmentsIntegrable (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h
      hM hℓ hd hR hRχ u (Φ := Φ) hΦc
  obtain ⟨hBlk, hSq, hCr⟩ :=
    Work.BoseFixB1.boxPairBlockIntegrable (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h
      hM hℓ hd hR hRχ u (Φ := Φ) hΦc
  obtain ⟨hW2i, hFib⟩ :=
    Work.BoseFixB1.boxQ0SlackIntegrable (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u
  -- ## the kernel identities
  have hw1 : ∀ x y : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.wSmall1Pair h M ℓ d u x y
        = Submission.BoseGases.wSmallPair M ℓ d u v x y
            * (1 - Submission.BoseGases.omC (Classical.choose h) x y) := by
    intro x y
    rw [Work.BoseFixB1.wSmall1Pair_eq_mul h u x y]
    simp only [Submission.BoseGases.omC]
  have hw2 : ∀ x y : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) x y
        = Submission.BoseGases.wSmallPair M ℓ d u v x y
            * (1 - Submission.BoseGases.omC (Classical.choose h) x y ^ 2) := by
    intro x y
    rw [Work.BoseFixB1.wSmallPair_g2_eq_mul h u x y, Work.BoseFixB1.wSmall1Pair_eq_mul h u x y]
    simp only [Submission.BoseGases.omC]
    ring
  have hwsym : ∀ x y : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.wSmallPair M ℓ d u v x y
        = Submission.BoseGases.wSmallPair M ℓ d u v y x :=
    fun x y => Submission.BoseGases.wSmallPair_symm hM u (radial_even hvrad) x y
  have homsym : ∀ x y : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.omC (Classical.choose h) x y
        = Submission.BoseGases.omC (Classical.choose h) y x := by
    intro x y
    have hw0 : ∀ z : EuclideanSpace ℝ (Fin 3), Classical.choose h (-z) = Classical.choose h z :=
      radial_even (Classical.choose_spec h).1
    simp only [Submission.BoseGases.omC]
    rw [show y - x = -(x - y) from by abel, hw0]
  -- ## (R1) the sum-level reduction, then the square/cross split
  have hred : Work.BoseFixB1S.boxQSum (Work.SmallBoxSliding.boxMass ℓ d u) ℓ μ
        (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmallPair M ℓ d u v)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u)
        (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
        (Submission.BoseGases.omC (Classical.choose h)) Φ
      - Work.BoseFixB1.boxA2 ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
      + (2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x)
              * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x)
              * Submission.BoseGases.w1Fibre ℓ
                  (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
          + μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
                * Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)))
      = Work.BoseFixB1S.boxQ0 (Work.SmallBoxSliding.boxMass ℓ d u) ℓ μ
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) Φ
        + (Work.BoseFixB1.boxSqPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
              (Submission.BoseGases.omC (Classical.choose h)) Φ
            + Work.BoseFixB1.boxCrossPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ) := by
    have h1 := Work.BoseFixB1S.Clean.boxQSum_sub_boxA2_blockSum (N := N) (ℓ := ℓ)
      (volA := Work.SmallBoxSliding.boxMass ℓ d u) (μ := μ)
      (A := Submission.BoseGases.dlBox ℓ d u) hℓ hVpos hAmeas hvolA hAc
      (w := Submission.BoseGases.wSmallPair M ℓ d u v)
      (w₁ := Submission.BoseGases.wSmall1Pair h M ℓ d u)
      (w₂ := Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
      (om := Submission.BoseGases.omC (Classical.choose h))
      hw1 hw2 hwsym homsym hΦc hint0 hint1 hint2 hint3 hint4 hint5
    have h2 := Work.BoseFixB1.boxSqPart_add_boxCrossPart_eq_blockSum (N := N) (ℓ := ℓ)
      (volA := Work.SmallBoxSliding.boxMass ℓ d u) (A := Submission.BoseGases.dlBox ℓ d u)
      (w := Submission.BoseGases.wSmallPair M ℓ d u v)
      (w₁ := Submission.BoseGases.wSmall1Pair h M ℓ d u)
      (om := Submission.BoseGases.omC (Classical.choose h)) (Φ := Φ) hSq hCr hBlk hw1
    linarith [h1, h2]
  -- ## `0 ≤ boxSqPart`
  -- ## `(★★)`: the *joint* (square-keeping) form of the analytic core, instantiated at
  -- the state.  This is the shape FS prove (they keep the manifest square `boxSqPart`
  -- and the pair-condensate term), and it is exactly what the reduction needs: see
  -- `boxTarget_of_joint` below and `NOTES_crux_boxCrossLower.md`.
  -- ## the arithmetic core
  exact boxTarget_of_joint (V := Work.SmallBoxSliding.boxMass ℓ d u)
    (μ := μ)
    (M₁ := Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Submission.BoseGases.wSmall1Pair h M ℓ d u))
    (M₂ := Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u)
      (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)))
    (S := Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
      (Submission.BoseGases.dlBox ℓ d u) Φ)
    (Pc := Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
      (Submission.BoseGases.dlBox ℓ d u) Φ)
    (nq := Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
      (Submission.BoseGases.dlBox ℓ d u) Φ)
    (C := C) (aa := _root_.BoseGases.a v)
    (Sqp := Work.BoseFixB1.boxSqPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
      (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
      (Submission.BoseGases.omC (Classical.choose h)) Φ)
    (L := Work.BoseFixB1.boxCrossPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
      (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ)
    (P := ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x)
        * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x)
        * Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
    (Q := ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
        * Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
    (Q0 := Work.BoseFixB1S.boxQ0 (Work.SmallBoxSliding.boxMass ℓ d u) ℓ μ
      (Submission.BoseGases.dlBox ℓ d u)
      (Submission.BoseGases.wSmall1Pair h M ℓ d u)
      (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) Φ)
    (A2 := Work.BoseFixB1.boxA2 ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ)
    (Qsum := Work.BoseFixB1S.boxQSum (Work.SmallBoxSliding.boxMass ℓ d u) ℓ μ
      (Submission.BoseGases.dlBox ℓ d u)
      (Submission.BoseGases.wSmallPair M ℓ d u v)
      (Submission.BoseGases.wSmall1Pair h M ℓ d u)
      (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
      (Submission.BoseGases.omC (Classical.choose h)) Φ)
    (a0 := Work.BoseFixB1.a0MainLocBox (Work.SmallBoxSliding.boxMass ℓ d u) μ
      (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u))
      (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
        (Submission.BoseGases.dlBox ℓ d u) Φ))
    hVpos hM1nn hM2 hPcnn hcS2 hred
    (Work.BoseFixB1.Clean.boxQ0_sub_a0MainLocBox_eq (N := N) (ℓ := ℓ)
      (volA := Work.SmallBoxSliding.boxMass ℓ d u) (μ := μ)
      (A := Submission.BoseGases.dlBox ℓ d u) hℓ hVpos hAmeas hvolA hAc hW2i hFib hΦc)
    (hC hℓ hd hμ hR hRχ u hvol hμv hΦc hM1nn hM2 hPcnn hcS2)

/-- The five ordered-pair integrands of step (i)'s right-hand side, for one ordered pair `p`
(the `p`-orientation half of `boxPairBlock`; only the two orientations *together* make the block,
see `boxPairBlock_eq_twoOrient`). -/
noncomputable def boxPairFive (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w₁ w₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) {N : ℕ}
    (Φ : Submission.BoseGases.X N → ℝ) (p : Fin N × Fin N) (x : Submission.BoseGases.X N) : ℝ :=
  2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
      * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
      * w₂ (x p.1) (x p.2)
    + (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
        * w₂ (x p.1) (x p.2)
    + (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
        * w₂ (x p.1) (x p.2)
    + 2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
        * w₁ (x p.1) (x p.2)
    + (1 / 2) * (boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2)

/-- **The per-pair merge**: `boxPairFive` at `p` plus `boxPairFive` at `p.swap` is the block.
Immediate from the bridge `boxPairBlock_eq_twoOrient` plus the symmetry of `w`; this is the lemma
the `pairSet`-sum in `boxWordPairSum` is paired with. -/
lemma boxPairFive_add_swap {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w₁ w₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    {Φ : Submission.BoseGases.X N → ℝ} {i j : Fin N} (x : Submission.BoseGases.X N)
    (hw1 : ∀ a b : EuclideanSpace ℝ (Fin 3), w₁ a b = w a b * (1 - om a b))
    (hw2 : ∀ a b : EuclideanSpace ℝ (Fin 3), w₂ a b = w a b * (1 - om a b ^ 2))
    (hwsym : ∀ a b : EuclideanSpace ℝ (Fin 3), w a b = w b a)
    (homsym : ∀ a b : EuclideanSpace ℝ (Fin 3), om a b = om b a)
    (hPP : Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
        = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
    (hQQ : Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
        = Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
    (hPQ : Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
        = Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
    (hQP : Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
        = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) :
    boxPairFive volA A w w₁ w₂ om Φ (i, j) x
        + boxPairFive volA A w w₁ w₂ om Φ (j, i) x
      = boxPairBlock volA A w om Φ (i, j) x := by
  have h := boxPairBlock_eq_twoOrient volA A w w₁ w₂ om x hw1 hw2 hwsym homsym hPP hQQ hPQ hQP
  rw [← h]
  simp only [boxPairFive, hQQ, homsym (x j) (x i), hPP, hPQ, hQP]
  rw [hwsym (x j) (x i)]
  ring

/-- **The five-piece decomposition of `boxPairFive`, pointwise.**  Each piece is written with its
constant exposed *outside* the product chain (`2 * (A*B*w₂)`, not `2*A*B*w₂`), which is the form
`MeasureTheory.integral_const_mul` needs — the associativity trap named in the fold's docstring.
This is the pointwise half of the fold's per-`p` residual; the integral half is then
`MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall …)` followed by the explicit
inside-out splits against `hinta … hinte`. -/
lemma boxPairFive_eq_pieces {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w₁ w₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (p : Fin N × Fin N) (x : Submission.BoseGases.X N) :
    boxPairFive volA A w w₁ w₂ om Φ p x
      = 2 * ((Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
            * w₂ (x p.1) (x p.2))
        + ((Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
            * w₂ (x p.1) (x p.2))
        + ((Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
            * w₂ (x p.1) (x p.2))
        + 2 * ((Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
            * w₁ (x p.1) (x p.2))
        + (1 / 2) * ((boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2)) := by
  simp only [boxPairFive]
  ring

/-- **Integrability of `boxPairFive`** — the extraction that `boxWordPairSum` needs: the fold's
`h1 … h5` construction, as one reusable lemma.  Body (next pass, mirrors the verified fold code
exactly): `h1 := ((hinta p hp).const_mul 2).congr (…ring…)`, `h2 := h1.add (hintb p hp)`,
`h3 := h2.add (hintc p hp)`, `h4 := ((hintd p hp).const_mul 2).congr (…ring…)`,
`h5 := (hinte p hp).const_mul (1/2)`, then `((h3.add h4).add h5).congr (…simp only [boxPairFive]; ring…)`
back to `boxPairFive … p x`.  The `.swap` companion is the same lemma at `(p.2, p.1)`. -/
theorem boxPairFive_integrable {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w₁ w₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ)
    (hinta : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.1
              (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
          * w₂ (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hintb : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.2
              (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hintc : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2
              (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hintd : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2
              (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₁ (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hinte : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (p : Fin N × Fin N) (hp : p ∈ Submission.BoseGases.pairSet N) :
    MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N => boxPairFive volA A w w₁ w₂ om Φ p x)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
  -- Recipe (the fold's verified chain, both `congr`s *inside ascribed* `have`s — the rule this
  -- file learned the hard way): ascribed `h1 := ((hinta p hp).const_mul 2).congr (…ring…)`,
  -- `h2 := h1.add (hintb p hp)`, `h3 := h2.add (hintc p hp)`, ascribed
  -- `h4 := ((hintd p hp).const_mul 2).congr (…ring…)`, `h5 := (hinte p hp).const_mul (1/2)`, then
  -- `exact ((h3.add h4).add h5).congr (of_forall (fun x => by simp only [boxPairFive]; ring))`.
  -- Note: the *closing* `congr` compares two lambdas, so if `ring` alone does not close it, do
  -- `funext`-style: `exact ((h3.add h4).add h5).congr (Filter.Eventually.of_forall (fun x => by
  -- simp only [boxPairFive]; ring))` may need the pointwise version spelled at the *value* level.
  have h1 : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N =>
        2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
          * w₂ (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    ((hinta p hp).const_mul 2).congr
      (Filter.Eventually.of_forall (fun x => by ring))
  have h2 := h1.add (hintb p hp)
  have h3 := h2.add (hintc p hp)
  have h4 : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N =>
        2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₁ (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    ((hintd p hp).const_mul 2).congr
      (Filter.Eventually.of_forall (fun x => by ring))
  have h5 := (hinte p hp).const_mul (1 / 2)
  have h6 : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N =>
        2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
          * (w₂ (x p.1) (x p.2))
        + (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
            * (w₂ (x p.1) (x p.2))
        + (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
            * (w₂ (x p.1) (x p.2))
        + 2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
            * (w₁ (x p.1) (x p.2))
        + (1 / 2) * ((boxQ4B volA A om Φ p x) ^ 2 * (w (x p.1) (x p.2))))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    (h3.add h4).add h5
  exact h6.congr (Filter.Eventually.of_forall (fun x => by
    simp only [boxPairFive]
    ring))

/-- **The `integral_add`/`integral_sum` fold** (the first formal move of `boxWordPairSum`):
the five `pairSet`-sums of `boxQSum_reduce`'s right-hand side recollect into the single sum of
the per-pair integrand `boxPairFive`.  Proof recipe (everything here is formal):
* `Finset.mul_sum` / `Finset.sum_add_distrib` recollect the scalars `2`, `2`, `1/2` under the
  `pairSet`-sums, giving `Σ_p (2∫a_p + ∫b_p + ∫c_p + 2∫d_p + ½∫e_p)`;
* `Finset.sum_congr rfl` reduces to the per-`p` fact
  `2∫a + ∫b + ∫c + 2∫d + ½∫e = ∫ (2a + b + c + 2d + ½e)`, which is four `integral_add`s
  (`IntegrableOn` of the five pieces is exactly the hypotheses below) and three
  `integral_const_mul`s, then `rw [boxPairFive]` and `ring`.

The consumer afterwards is `pairSet_swap_sum` + `boxPairFive_add_swap`:
`Σ_p ∫ boxPairFive p = ½ Σ_p ∫ (boxPairFive p + boxPairFive (p.swap)) = ½ Σ_p ∫ boxPairBlock p`. -/
theorem boxPairSum_fold {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w₁ w₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ)
    (hinta : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.1
              (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
          * w₂ (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hintb : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.2
              (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hintc : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2
              (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hintd : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2
              (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₁ (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hinte : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    2 * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxPInd volA A p.1
                    (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
                * w₂ (x p.1) (x p.2))
        + (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxPInd volA A p.2
                    (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
                * w₂ (x p.1) (x p.2))
        + (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxQInd volA A p.2
                    (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
                * w₂ (x p.1) (x p.2))
        + 2 * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
                * (Work.UBBInputs8.boxQInd volA A p.2
                    (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
                * w₁ (x p.1) (x p.2))
        + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))
      = ∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ, boxPairFive volA A w w₁ w₂ om Φ p x := by
  -- PROGRESS (recorded for the next pass): the two bookkeeping lines below are *checked* --
  -- `rw [Finset.mul_sum, ...]` recollects the scalars `2, 2, 1/2` and the four
  -- `rw [← Finset.sum_add_distrib]` merge the five `pairSet`-sums into one, leaving exactly the
  -- per-`p` goal `2∫a + ∫b + ∫c + 2∫d + ½∫e = ∫ boxPairFive p`.  On that goal
  -- `simp only [boxPairFive]` unfolds the integrand as required, but
  -- `simp only [MeasureTheory.integral_add, MeasureTheory.integral_const_mul]` reports "no
  -- progress" (the splitting lemmas are not firing as simp rules on the displayed
  -- `∫ x in s, ...` form).  Next pass: do the splits *explicitly* and inside-out, building the
  -- partial sums' integrability first --
  --   `(hinta p hp).const_mul 2`, then `.add (hintb p hp)`, `.add (hintc p hp)`, ...
  -- and then `rw [MeasureTheory.integral_add hAB hC, ...]` /
  -- `rw [MeasureTheory.integral_const_mul]`, closing with `ring`.  Note the associativity trap
  -- named in the docstring: the constants sit left-associated (`2 * A * B * w₂`), so each
  -- `integral_const_mul` needs the body normalised to `c * (·)` first.
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpt : ∀ x : Submission.BoseGases.X N,
      2 * ((Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
            * w₂ (x p.1) (x p.2))
        + ((Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
            * w₂ (x p.1) (x p.2))
        + ((Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
            * w₂ (x p.1) (x p.2))
        + 2 * ((Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
            * w₁ (x p.1) (x p.2))
        + (1 / 2) * ((boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))
      = boxPairFive volA A w w₁ w₂ om Φ p x := by
    intro x
    simp only [boxPairFive]
    ring
  conv_rhs => change (∫ x in Submission.BoseGases.abox N ℓ,
      2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
        * w₂ (x p.1) (x p.2)
      + (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2)
      + (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2)
      + 2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₁ (x p.1) (x p.2)
      + (1 / 2) * (boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))
  have h1 : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N =>
        2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
          * w₂ (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    ((hinta p hp).const_mul 2).congr
      (Filter.Eventually.of_forall (fun x => by ring))
  have h2 := h1.add (hintb p hp)
  have h3 := h2.add (hintc p hp)
  have h4 : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N =>
        2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₁ (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    ((hintd p hp).const_mul 2).congr
      (Filter.Eventually.of_forall (fun x => by ring))
  have h5 : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N =>
        (1 / 2) * (boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    ((hinte p hp).const_mul (1 / 2)).congr
      (Filter.Eventually.of_forall (fun x => by ring))
  have hp4 := h3.add h4
  rw [MeasureTheory.integral_add
    (f := fun x : Submission.BoseGases.X N =>
      2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
        * w₂ (x p.1) (x p.2)
      + (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2)
      + (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2)
      + 2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₁ (x p.1) (x p.2))
    (g := fun x : Submission.BoseGases.X N =>
      (1 / 2) * (boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))
    hp4 h5]
  rw [MeasureTheory.integral_add
    (f := fun x : Submission.BoseGases.X N =>
      2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
        * w₂ (x p.1) (x p.2)
      + (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2)
      + (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2))
    (g := fun x : Submission.BoseGases.X N =>
      2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
        * w₁ (x p.1) (x p.2))
    h3 h4]
  rw [MeasureTheory.integral_add
    (f := fun x : Submission.BoseGases.X N =>
      2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
        * w₂ (x p.1) (x p.2)
      + (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2))
    (g := fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
        * w₂ (x p.1) (x p.2))
    h2 (hintc p hp)]
  rw [MeasureTheory.integral_add
    (f := fun x : Submission.BoseGases.X N =>
      2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
        * w₂ (x p.1) (x p.2))
    (g := fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
        * w₂ (x p.1) (x p.2))
    h1 (hintb p hp)]
  rw [show (∫ x in Submission.BoseGases.abox N ℓ,
        2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
          * (w₂ (x p.1) (x p.2)))
      = ∫ x in Submission.BoseGases.abox N ℓ,
        2 * ((Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
          * (w₂ (x p.1) (x p.2)))
      from MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun x => by ring))]
  rw [MeasureTheory.integral_const_mul]
  rw [show (∫ x in Submission.BoseGases.abox N ℓ,
        2 * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * (w₁ (x p.1) (x p.2)))
      = ∫ x in Submission.BoseGases.abox N ℓ,
        2 * ((Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * (w₁ (x p.1) (x p.2)))
      from MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun x => by ring))]
  rw [MeasureTheory.integral_const_mul]
  rw [show (∫ x in Submission.BoseGases.abox N ℓ,
        (1 / 2) * (boxQ4B volA A om Φ p x) ^ 2 * (w (x p.1) (x p.2)))
      = ∫ x in Submission.BoseGases.abox N ℓ,
        (1 / 2) * ((boxQ4B volA A om Φ p x) ^ 2 * (w (x p.1) (x p.2)))
      from MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun x => by ring))]
  rw [MeasureTheory.integral_const_mul]

/-- **The per-`p` identity of the `boxWordPairSum` assembly**, restated *inside this file*: the
delegated `Work.BoseFixB1S.boxPairFive_add_swap_integral` cannot be cited here because its module
imports this one (import cycle) — the rule being *a lemma your own file must cite cannot be
delegated, only restated*.  Proof transcribed from that file: `boxPairFive_integrable` at `p` and
at `(p.2,p.1)` (`pairSet` is symmetric), `← integral_add`, then `integral_congr_ae` with
`ae_restrict_mem (abox_measurable N ℓ)` and the four `BoxPotOper` swaps fed to
`boxPairFive_add_swap`. -/
theorem boxPairFive_add_swap_integral_local {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w w₁ w₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hw1 : ∀ x y : EuclideanSpace ℝ (Fin 3), w₁ x y = w x y * (1 - om x y))
    (hw2 : ∀ x y : EuclideanSpace ℝ (Fin 3), w₂ x y = w x y * (1 - om x y ^ 2))
    (hwsym : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y = w y x)
    (homsym : ∀ x y : EuclideanSpace ℝ (Fin 3), om x y = om y x)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hinta : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.1
              (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
          * w₂ (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hintb : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.2
              (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hintc : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2
              (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hintd : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2
              (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₁ (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hinte : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    {p : Fin N × Fin N} (hp : p ∈ Submission.BoseGases.pairSet N) :
    (∫ x in Submission.BoseGases.abox N ℓ, boxPairFive volA A w w₁ w₂ om Φ p x)
        + (∫ x in Submission.BoseGases.abox N ℓ,
            boxPairFive volA A w w₁ w₂ om Φ (p.2, p.1) x)
      = ∫ x in Submission.BoseGases.abox N ℓ, boxPairBlock volA A w om Φ p x := by
  have hpneq : p.1 ≠ p.2 := by
    simpa only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ, true_and] using hp
  have hpswap : (p.2, p.1) ∈ Submission.BoseGases.pairSet N := by
    simp only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun h => hpneq h.symm
  have hI1 : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N => boxPairFive volA A w w₁ w₂ om Φ p x)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    boxPairFive_integrable volA ℓ A w w₁ w₂ om Φ hinta hintb hintc hintd hinte p hp
  have hI2 : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N => boxPairFive volA A w w₁ w₂ om Φ (p.2, p.1) x)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    boxPairFive_integrable volA ℓ A w w₁ w₂ om Φ hinta hintb hintc hintd hinte
      (p.2, p.1) hpswap
  rw [← MeasureTheory.integral_add hI1 hI2]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable N ℓ)]
    with x hx
  exact boxPairFive_add_swap volA A w w₁ w₂ om x hw1 hw2 hwsym homsym
    (boxPPswap (i := p.1) (j := p.2) hℓ hvol hA hvolA hAc hpneq hΦc x)
    (boxQQswap (i := p.1) (j := p.2) hℓ hvol hA hvolA hAc hpneq hΦc x hx).symm
    (boxPQswap (i := p.1) (j := p.2) hℓ hvol hA hvolA hAc hpneq hΦc x hx)
    (boxQPswap (i := p.1) (j := p.2) hℓ hvol hA hvolA hAc hpneq hΦc x hx)

/-- **The sum-level regrouping (`boxWordPairSum`)** — placed after its ingredients
(`boxPairFive`, `boxPairSum_fold`), which Lean requires.  The assembly is
`boxQSum_reduce` ▸ `boxPairSum_fold` ▸ the `pairSet_swap_sum` step with the `1/2`. -/
theorem boxWordPairSum {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w w₁ w₂ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hw1 : ∀ x y : EuclideanSpace ℝ (Fin 3), w₁ x y = w x y * (1 - om x y))
    (hw2 : ∀ x y : EuclideanSpace ℝ (Fin 3), w₂ x y = w x y * (1 - om x y ^ 2))
    (hwsym : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y = w y x)
    (homsym : ∀ x y : EuclideanSpace ℝ (Fin 3), om x y = om y x)
    (hsuppA : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y ≠ 0 → x ∈ A ∧ y ∈ A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hinta : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.1
              (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
          * w₂ (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hintb : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.2
              (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hintc : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2
              (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
          * w₂ (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hintd : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2
              (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w₁ (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hinte : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    Work.BoseFixB1S.boxQ1 volA ℓ μ A w₁ w₂ Φ
        + (Work.BoseFixB1S.boxQ2 volA ℓ μ A w₁ w₂ Φ
            - Work.BoseFixB1.boxA2 ℓ volA A w₁ Φ)
        + Work.BoseFixB1S.boxQ3 volA ℓ A w₁ Φ
        + Work.BoseFixB1S.boxQ4 volA ℓ A w om Φ
        + 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x)
              * (Work.UBBInputs8.boxPInd volA A i Φ x)
              * Submission.BoseGases.w1Fibre ℓ w₁ (x i))
        + μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2
              * Submission.BoseGases.w1Fibre ℓ w₁ (x i))
      = (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ, boxPairBlock volA A w om Φ p x := by
  rw [boxQSum_reduce]
  rw [boxPairSum_fold volA ℓ A w w₁ w₂ om Φ hinta hintb hintc hintd hinte]
  have hswap : (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          boxPairFive volA A w w₁ w₂ om Φ (p.2, p.1) x)
      = ∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ, boxPairFive volA A w w₁ w₂ om Φ p x :=
    Submission.BoseGases.pairSet_swap_sum
      (fun p => ∫ x in Submission.BoseGases.abox N ℓ,
        boxPairFive volA A w w₁ w₂ om Φ p x)
  have hsum : (∑ p ∈ Submission.BoseGases.pairSet N,
        ((∫ x in Submission.BoseGases.abox N ℓ,
            boxPairFive volA A w w₁ w₂ om Φ p x)
          + (∫ x in Submission.BoseGases.abox N ℓ,
              boxPairFive volA A w w₁ w₂ om Φ (p.2, p.1) x)))
      = (∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ, boxPairFive volA A w w₁ w₂ om Φ p x)
        + (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              boxPairFive volA A w w₁ w₂ om Φ (p.2, p.1) x) :=
    Finset.sum_add_distrib
  have hhalf : (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ, boxPairFive volA A w w₁ w₂ om Φ p x)
      = (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
        ((∫ x in Submission.BoseGases.abox N ℓ,
            boxPairFive volA A w w₁ w₂ om Φ p x)
          + (∫ x in Submission.BoseGases.abox N ℓ,
              boxPairFive volA A w w₁ w₂ om Φ (p.2, p.1) x))) := by
    rw [hsum, hswap]
    ring
  -- REMAINING: from `hswap`, `∑ p, h p = (1/2) * ∑ p, (h p + h (p.swap))`, and then
  -- `boxPairFive_add_swap` + `integral_add` (explicit `f`/`g`, body-association spellings)
  rw [hhalf]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  exact boxPairFive_add_swap_integral_local hℓ hvol hA hvolA hAc om hw1 hw2 hwsym homsym
    hΦc hinta hintb hintc hintd hinte hp

end Work.BoseFixB1S
