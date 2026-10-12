import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.SlabArmExcited
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixR.PerBoxWordCrudeHigh` — the high-count arm of the crude per-box bound

Target (kept verbatim at the bottom): the crude sliding-box bound `PerBoxWordCrude` in the regime
`occChi ≥ K(μ·chiMass + 1)·‖Φ‖²`.

## The dichotomy used for the proof

Write `ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`, `M = (paramsAt μ (a v)).M`,
`B = dlBox ℓ d u`, `V = boxMass ℓ d u = |B|`, `χ_M = chiMass M ℓ d u = ∫χ_B²`, and for a state `Φ`

* `cnt := Σᵢ ∫_{abox n ℓ} Φ²·1_B(xᵢ)` — the `B`-occupancy count,
* `n₀ := Σᵢ ∫ (boxPInd V B i Φ)²` — the condensate count (`P_{B,i} = |B|⁻¹⟨1_B,·⟩1_B`),
* `n₊ := cnPlusBoxInd ℓ B V Φ` — the excited count (`Q_{B,i} = 1_B(xᵢ) − P_{B,i}`).

**Count identity** (`Work.BoseFixR.SlabCountSplit`, PROVED): `cnt = n₀ + n₊` for every continuous
`Φ`.  Hence the two arms below are *complementary* and cover every state.

**Arm A** (`Work.BoseFixR.SlabArmExcited`, PROVED): a state whose occupancy is at least
half excited, `n₊ ≥ (1/2)·cnt`, is paid by FS's definitional gap payment plus the (linear, PROVED)
fibre bound: `sbWord ≥ 0 ≥ −C(μ²(a v)χ_M + μ(a v))‖Φ‖²` at suitable constants.

**Arm B** (`Work.BoseFixR.SlabCondensedHalf`, in flight): the corresponding statement with the
condensed premise `(1/2)·cnt ≤ n₀` — by the count identity `cnt = n₀ + n₊` this is *exactly* the
complement of arm A's premise.

DEFECT FOUND AND REPAIRED (this stretch): the first delegation of arm B asked for the premise
`n₀ ≥ (1−δ)·cnt` with an *existentially* chosen `δ ≤ 1/2`; that premise is *stronger* than
`n₀ ≥ cnt/2` (a small `δ` makes it stronger), so it does **not** cover the complement of arm A and
left the band `δ·cnt < n₊ < cnt/2` uncovered.  The repair (delegated as `SlabCondensedHalf`) fixes
the threshold at `δ = 1/2`: the premise `(1/2)·cnt ≤ n₀` — verbatim what the else-branch of the
case split produces.  Its content is FS's potential-side chain (`lm:appinteractionestimate` at the
sliding box with the box-indicator projections: the flat-part mean-field square for the condensate,
the crude Cauchy–Schwarz payment of the `Q`-cross and pairing terms, the `D`-cancellation).  The arm
is *not* automatic from the count hypothesis (box-supported high-frequency states satisfy the count
hypothesis and violate the condensed premise), so it is a genuine proper sub-case, and the dichotomy
below is a genuine decomposition of the target.

**Assembly** (this file — written, compiles): take `ε₀ := min ε_A ε_B`, `K := max K_A K_B`, `C := max C_A C_B`; by the
count identity `cnt = n₀ + n₊`, `by_cases` on `n₊ ≥ cnt/2`: in the first case arm A applies (its
premise is verbatim); otherwise `n₀ = cnt − n₊ > cnt/2 ≥ (1−δ_B)·cnt` (using `δ_B ≤ 1/2` from arm
B's own conclusion), so arm B's premise holds.  Enlarging `K` only strengthens the hypothesis
(`crudeThreshold` is monotone in `K` against the nonnegative factor `(μ·chiMass + 1)·normB`) and
enlarging `C` only weakens the conclusion (against the nonnegative factor
`X := μ²(a v)·chiMass + μ(a v)` and `normB ≥ 0`).  Both steps are implemented below with
`mul_le_mul_of_nonneg_right` against the named nonnegativity lemmas `hχ1`, `hnB0`, `hX0`.

**State of the file.**  The body of `PerBoxWordCrudeHigh` below is complete and
`lake build Submission.Work.BoseFixR.PerBoxWordCrudeHigh` succeeds; the *only* remaining input is
the imported `Work.BoseFixR.SlabCondensedHalf` (file `Submission/Work/BoseFixR/SlabCondensedHalf.lean`,
still carrying its `sorry` while its prover works).  `SlabCountSplit`, `SlabArmExcited` and
`ChiSmallBSupport` of the arithmetic are PROVED and imported.
-/

namespace Work.BoseFixR

open MeasureTheory

theorem PerBoxWordCrudeHigh {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ K C : ℝ, 0 < ε₀ ∧ 0 < K ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          Work.BoseFixR.crudeThreshold v K μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                (Φ : Submission.BoseGases.X n → ℝ) →
          -(C * (μ ^ 2 * _root_.BoseGases.a v
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * _root_.BoseGases.a v))
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  obtain ⟨εA, KA, CA, hεA, hKA, hCA, harmA⟩ :=
    Work.BoseFixR.SlabArmExcited (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εB, KB, CB, hεB, hKB, hCB, harmB⟩ :=
    Work.BoseFixR.SlabCondensedHalf (v := v) h hv hv1 hvrad hR hv_supp hav
  refine ⟨min εA εB, max KA KB, max CA CB, lt_min hεA hεB,
    lt_of_lt_of_le hKA (le_max_left _ _), le_trans hCA (le_max_left _ _), ?_⟩
  intro μ hAdm n Φ u hthr
  have hAdmA : Work.BoseBoxFix.Adm v εA μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hAdmB : Work.BoseBoxFix.Adm v εB μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_right _ _), hAdm.2.2⟩
  have hχ0 : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := by
    rw [Work.SmallBoxSliding.chiMass_def]
    exact integral_nonneg fun x => sq_nonneg _
  have hnB0 : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    exact integral_nonneg fun x => sq_nonneg _
  have hχ1 : 0 ≤ μ * Work.SmallBoxSliding.chiMass
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + 1 := by
    linarith [mul_nonneg (le_of_lt hAdm.1) hχ0]
  have hZ0 : 0 ≤ (μ * Work.SmallBoxSliding.chiMass
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + 1)
      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    mul_nonneg hχ1 hnB0
  have hX0 : 0 ≤ μ ^ 2 * _root_.BoseGases.a v
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      + μ * _root_.BoseGases.a v :=
    add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) (le_of_lt hav)) hχ0)
      (le_of_lt (mul_pos hAdm.1 hav))
  -- threshold monotonicity in `K`
  have hthrA : Work.BoseFixR.crudeThreshold v KA μ
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          (Φ : Submission.BoseGases.X n → ℝ) := by
    refine le_trans ?_ hthr
    simp only [Work.BoseFixR.crudeThreshold]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left KA KB) hχ1) hnB0
  have hthrB : Work.BoseFixR.crudeThreshold v KB μ
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          (Φ : Submission.BoseGases.X n → ℝ) := by
    refine le_trans ?_ hthr
    simp only [Work.BoseFixR.crudeThreshold]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right KA KB) hχ1) hnB0
  -- the constant comparison in the conclusion
  have hconcl : ∀ {C0 C' : ℝ}, C0 ≤ C' →
      -(C' * (μ ^ 2 * _root_.BoseGases.a v
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            + μ * _root_.BoseGases.a v))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ -(C0 * (μ ^ 2 * _root_.BoseGases.a v
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            + μ * _root_.BoseGases.a v))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    intro C0 C' hC'
    have h1 : C0 * (μ ^ 2 * _root_.BoseGases.a v
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            + μ * _root_.BoseGases.a v)
        ≤ C' * (μ ^ 2 * _root_.BoseGases.a v
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            + μ * _root_.BoseGases.a v) :=
      mul_le_mul_of_nonneg_right hC' hX0
    nlinarith [mul_le_mul_of_nonneg_right h1 hnB0]
  -- the two counts
  set cnt : ℝ := ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
          (fun _ => (1 : ℝ)) (x i) with hcnt
  set n0 : ℝ := ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Work.UBBInputs8.boxPInd
        (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) i
        (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 with hn0
  set nplus : ℝ := Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Φ : Submission.BoseGases.X n → ℝ) with hnplus
  have hcnt0 : 0 ≤ cnt := by
    rw [hcnt]
    refine Finset.sum_nonneg fun i _ => integral_nonneg fun x => ?_
    exact mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ => by norm_num) _)
  have hsplit : cnt = n0 + nplus := by
    rw [hcnt, hn0, hnplus]
    exact Work.BoseFixR.SlabCountSplit
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (u := u) (N := n)
      (Φ := (Φ : Submission.BoseGases.X n → ℝ))
      (Work.BoseFixB1.adm_ell_pos hAdm) (Work.BoseFixB1.adm_d_pos hAdm)
      (Φ.contDiff.continuous)
  by_cases hcase : (1 / 2 : ℝ) * cnt ≤ nplus
  · -- arm A
    have hcase' : (1 / 2 : ℝ) * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
            (fun _ => (1 : ℝ)) (x i))
        ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Φ : Submission.BoseGases.X n → ℝ) := by
      simpa only [hcnt, hnplus] using hcase
    have h := harmA μ hAdmA n Φ u hthrA hcase'
    exact le_trans (hconcl (le_max_left _ _)) h
  · -- arm B: `n₀ > cnt/2`, i.e. the half-condensed premise of `SlabCondensedHalf`
    push_neg at hcase
    have hprem : (1 / 2 : ℝ) * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
            (fun _ => (1 : ℝ)) (x i))
        ≤ (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.UBBInputs8.boxPInd
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) i
              (Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) := by
      have h' : (1 / 2 : ℝ) * cnt ≤ n0 := by linarith
      simpa only [hcnt, hn0] using h'
    have h := harmB μ hAdmB n Φ u hthrB hprem
    exact le_trans (hconcl (le_max_right _ _)) h

end Work.BoseFixR
