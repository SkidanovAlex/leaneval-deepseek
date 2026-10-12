import ChallengeDeps
import Submission.Work.BoseBoxFock.pairRowS3Defs
import Submission.Work.BoseBoxFock.potTruncRepair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowWordParts` — the split of the `Q₂` dictionary into two halves

`FINDING_PotPairRows_exists.md` §13 reduced the node to the single theorem `pairRowS3Bound`
(the limit-kernel comparison of the `Q₂` row with `q2word`).  This module records the *finer*
decomposition of that comparison into the two halves of FS's own proof (`lem:2ndQuand` +
`eq:Q2n0`), namely

    (A)  row-at-`pairRowNice` + block III  ≤  T₁ + T₄ + (the mass row)  + errA
    (B)  T₁ + T₄ + (the mass row)           ≤  q2word                    + errB

with the same intermediate object `rowWordParts` on both sides.  The point of the split is that
**(B) is a purely *first-quantised* word comparison** — FS's `eq:Q2n0` with the condensate density
`ρ₀ = n₀/ℓ³` *as an operator* — and *not* a statement about the box row; it can therefore be
attacked with the corpus's word vocabulary (`q1PairWord`, `q2PairWord`, `q4PairWord`, `qOneMass`,
`q2MassChi` of `QMassUpper`/`QDecompSimpler`), while **(A)** is the box-side algebra (the
second-quantisation identities of `lem:2ndQuand`).

The intermediate object:

* `q1PairWord ℓ v h Φ` — `T₁ = Σ_{i≠j}∫ (P_iQ_jΦ)(P_jQ_iΦ) w₂` (FS `eq:DefQ2`, first summand),
* `q4PairWord ℓ v h Φ` — `T₄ = Σ_{i≠j}∫ (P_iP_jΦ)(Q_jQ_iΦ) w₁` (fourth summand),
* `rowMassWord` — the *operator* mass row `(ρ₀Ŵ₁(0) + ρ₀Ŵ₁ω(0) − μŴ₁(0))·dΓ(Qχ²Q)` of
  `pairRowB3`, in the form `ℓ⁻³(Ŵ₁(0)+Ŵ₁ω(0))·⟨n₀Θ, Σ_jQ_jχ²Q_jΘ⟩ − μ Ŵ₁(0)·q2MassChi`,
  where `n₀ = Σ_iP_i` is the condensate number operator and
  `q2MassChi ℓ Φ = Σ_j∫(Q_jΦ)²χ_ℓ(x_j)²`.

NOTE (found numerically, see the FINDING): block I of the row *equals* `T₁` exactly (as a
quadratic form on symmetric box states, up to the lattice images removed by
`rowPairSubC_stripImages`), and block II equals `T₄` the same way; the mass row equals block III
exactly.  So `errA` is only the images/truncation residue, while `errB` is FS's
`eq:Q2n0`-error `C(μ+ρ₀)a(R/ℓ)²n₊`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The kernel identification `wLoc ℓ h 0 = wPairC ℓ h` -/

/-- `chiU ℓ 0 = chiScale ℓ`. -/
theorem chiU_zero (ℓ : ℝ) (x : E3) :
    Submission.BoseGases.chiU ℓ 0 x = Submission.BoseGases.chiScale ℓ x := by
  simp only [Submission.BoseGases.chiU, Submission.BoseGases.chiScale, sub_zero]

/-- **`wLoc ℓ h 0 = wPairC ℓ h`** — the localised kernel of the corpus's `wLoc` at `u = 0` is
the pair kernel `wPairC` used by the word modules (a local copy of
`Work.BoseFixB2.Pot.wLoc_zero_eq_wPairC`, which is outside this cone). -/
theorem wLoc0_eq_wPairC (ℓ : ℝ) (h : E3 → ℝ) (a b : E3) :
    Submission.BoseGases.wLoc ℓ h 0 a b = Submission.BoseGases.wPairC ℓ h a b := by
  simp only [Submission.BoseGases.wLoc, Submission.BoseGases.wPairC, Submission.BoseGases.wPair,
    chiU_zero]

/-- Function form of `wLoc0_eq_wPairC` (needed to rewrite the *fibres* of the word). -/
theorem wLoc0_eq_wPairC_fn (ℓ : ℝ) (h : E3 → ℝ) :
    Submission.BoseGases.wLoc ℓ h 0 = Submission.BoseGases.wPairC ℓ h :=
  funext (fun a => funext (fun b => wLoc0_eq_wPairC ℓ h a b))

/-! ## 2. The split of the corpus word `q2word` into its four summands -/

/-- **`q2word = T₁ + T₂ − μ·T₃ + T₄`** at the honest kernels `w₁ = wLoc ℓ (g₀ v h) 0`,
`w₂ = wLoc ℓ (g₂ v h) 0` (FS `eq:DefQ2`; the corpus's `q1PairWord`/`q2PairWord`/`qOneMass`/
`q4PairWord` splitting). -/
theorem q2word_split {N : ℕ} (ℓ μ : ℝ) {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    (Φ : Submission.BoseGases.X N → ℝ) :
    Submission.BoseGases.q2word (N := N) ℓ μ
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0)
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0) Φ
      = Submission.BoseGases.q1PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
        + Submission.BoseGases.q2PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
        - μ * Submission.BoseGases.qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
        + Submission.BoseGases.q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) := by
  simp only [Submission.BoseGases.q1PairWord, Submission.BoseGases.q2PairWord,
    Submission.BoseGases.qOneMass, Submission.BoseGases.q4PairWord]
  rw [wLoc0_eq_wPairC_fn ℓ (Submission.BoseGases.g0 v h),
    wLoc0_eq_wPairC_fn ℓ (Submission.BoseGases.g2 v h)]
  unfold Submission.BoseGases.q2word
  ring

/-! ## 3. The mass row in word form -/

/-- **The condensate-number-weighted `χ²`-mass** `⟨n₀Θ, Σ_jQ_jχ²Q_jΘ⟩`, written as a
first-quantised word in `Φ`: `Σ_j∫ (Σ_i aP_i(aQ_jΦ)(x))·(aQ_jΦ(x))·χ_ℓ(x_j)²`.

(Note the *single* power of `aQ_jΦ`: `Q_jχ²Q_j`'s form is `∫(Q_jΘ)χ²(Q_jΘ)` and the
`n₀`-factor contributes `Σ_i aP_i(aQ_jΦ)`; the object is therefore **quadratic** in `Φ`, like
every other word term of `q2word`.) -/
noncomputable def n0MassWord {n : ℕ} (ℓ : ℝ)
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
    (∑ i : Fin n, Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x)
      * (Submission.BoseGases.aQ ℓ j Φ x)
      * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2

/-- **The mass row of `block III` in word form**: `(ρ₀Ŵ₁(0) + ρ₀Ŵ₁ω(0) − μŴ₁(0))·dΓ(Qχ²Q)` with
`ρ₀ = n₀/ℓ³`, evaluated on the real box state `Φ`. -/
noncomputable def rowMassWord {n : ℕ} (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (μ ℓ : ℝ)
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  (ℓ ^ 3)⁻¹ * (Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h)) 0
        + Work.BoseFixR.chat
            (Submission.BoseGases.wScaled ℓ
              (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z)) 0)
      * n0MassWord ℓ Φ
    - μ * Work.BoseFixR.chat
        (Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h)) 0
      * Submission.BoseGases.q2MassChi (ℓ := ℓ) (Φ := Φ)

/-- **The intermediate word form** `T₁ + T₄ + (mass row)`. -/
noncomputable def rowWordParts {n : ℕ} (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (μ ℓ : ℝ)
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  Submission.BoseGases.q1PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
    + Submission.BoseGases.q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
    + rowMassWord v h μ ℓ Φ

/-- The same at the box side `ℓ = ellH v μ`. -/
noncomputable def rowWordPartsH {n : ℕ} (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  rowWordParts v h μ (ellH v μ) Φ

end Work.BoseBoxFock
