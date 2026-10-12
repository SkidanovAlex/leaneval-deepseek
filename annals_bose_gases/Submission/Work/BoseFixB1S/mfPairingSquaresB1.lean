import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.boxBogB1Fix
import Submission.Work.BoseFixB1S.boxFlatCount_le_NB1
import Submission.Work.BoseFixB1S.boxM2_sub_boxM1_nonneg_slidingB1
import Submission.Work.BoseFixB1S.boxPairManifestSumB1S
import Submission.Work.BoseFixB1S.mfBoxAbbrev
import Submission.Work.BoseFixB1S.mf_boxMass_pos_of_mem_interiorSet
import Submission.Work.BoseFixB1S.n0SpectralMomentsB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal
open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-- **THE REDUCTION (★), in the raw corpus vocabulary.**  At an admissible box
`(ℓ, d, u)` with `R ≤ ℓd/16`, `R ≤ ℓ·chiR0`, and a `Continuous` state `Φ`, the pairing word
`boxA2`, the manifest square `boxSqPart` and the cross term `boxCrossPart` combine to the
manifest `σ²`-mass minus the pair-condensate mass:

    boxA2 ℓ V A w₁ Φ + boxSqPart V ℓ A w ω Φ + boxCrossPart V ℓ A w₁ Φ
      = ½·Σ_p∫σ_p²·w − ½·(M₂/V²)·boxPairCount V ℓ A Φ ,

with `σ_p := 1_A(x_{p.1})·(1_A(x_{p.2})·Φ x)`, `V := boxMass ℓ d u`, `A := dlBox ℓ d u`,
`w := wSmallPair M ℓ d u v`, `w₁ := wSmall1Pair h M ℓ d u`,
`w₂ := wSmallPair M ℓ d u (g₂ v h)`, `ω := omC (choose h)`, `M₂ := boxM2 V A w₂`.

Proof: `boxSqPart_add_boxCrossPart_eq_blockSum` (the square/cross split of `½Σ∫pairBlock`)
combined with `boxPairBlock_eq_crossForm` (the same sum in cross form); `boxA2` *is* the last
summand of the cross form (definitionally, up to commutativity of multiplication). -/
theorem boxA2_add_squares_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB1.boxA2 ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
      + Work.BoseFixB1.boxSqPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
          (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.omC (Classical.choose h)) Φ
      + Work.BoseFixB1.boxCrossPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
          (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
    = (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ,
            (((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.1))
              * ((Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2
              * (Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)))
      - (1 / 2) * (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
            / (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)
          * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ := by
  classical
  obtain ⟨hBlk, hSq, hCr⟩ :=
    Work.BoseFixB1.boxPairBlockIntegrable (v := v) (R0 := R) (M := M) (ℓ := ℓ) (d := d)
      (N := N) (Φ := Φ) hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u hΦc
  have hw1rel : ∀ a b : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.wSmall1Pair h M ℓ d u a b
        = Submission.BoseGases.wSmallPair M ℓ d u v a b
            * (1 - Submission.BoseGases.omC (Classical.choose h) a b) := by
    intro a b
    simpa only [Submission.BoseGases.omC] using
      Work.BoseFixB1.wSmall1Pair_eq_mul (v := v) h (M := M) (ℓ := ℓ) (d := d) u a b
  have hsplit := Work.BoseFixB1.boxSqPart_add_boxCrossPart_eq_blockSum (N := N) (ℓ := ℓ)
    (volA := Work.SmallBoxSliding.boxMass ℓ d u) (A := Submission.BoseGases.dlBox ℓ d u)
    (w := Submission.BoseGases.wSmallPair M ℓ d u v)
    (w₁ := Submission.BoseGases.wSmall1Pair h M ℓ d u)
    (om := Submission.BoseGases.omC (Classical.choose h)) (Φ := Φ) hSq hCr hBlk hw1rel
  have hcross := Work.BoseFixB1.boxPairBlock_eq_crossForm (v := v) (R0 := R) (M := M)
    (ℓ := ℓ) (d := d) (N := N) (Φ := Φ) hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u hΦc
  have hsum_eq : (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1S.boxPairBlock (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.omC (Classical.choose h)) Φ p x)
      = (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1.pairBlock (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.omC (Classical.choose h)) Φ p x) := rfl
  rw [hsum_eq] at hcross
  -- the last summand of `hcross` is `boxA2` (the factors are commuted)
  have hA2 : (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) p.2
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.1 Φ) x)
            * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.1
                (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x)
            * (Submission.BoseGases.wSmall1Pair h M ℓ d u (x p.1) (x p.2)))
      = Work.BoseFixB1.boxA2 ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Work.BoseFixB1.boxA2]
    ring
  rw [hA2] at hcross
  linarith [hsplit, hcross]

/-- **The reduction (★) at FS's parameters, in the `mf*` vocabulary** — the form the target's
statement uses.  `mfA2 + boxSqPart + boxCrossPart = ½Σ_p∫σ_p²w − ½(M₂/V²)·Pc`. -/
theorem mfA2_add_squares_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) (hav : 0 < _root_.BoseGases.a v) {μ : ℝ}
    (hMbox : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hR : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3))
    (hvol : 0 < mfV v μ u) {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) :
    mfA2 h μ N Φ u
      + Work.BoseFixB1.boxSqPart (mfV v μ u) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (boxA v μ u) (boxW h μ u) (Submission.BoseGases.omC (Classical.choose h)) Φ
      + Work.BoseFixB1.boxCrossPart (mfV v μ u) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (boxA v μ u) (boxW1 h μ u) Φ
    = (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (((boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.1))
              * ((boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2
              * (boxW h μ u (x p.1) (x p.2)))
      - (1 / 2) * (mfM2 h μ u / (mfV v μ u) ^ 2) * mfPc v μ N Φ u := by
  have key := boxA2_add_squares_eq (v := v) (R := R) hv_supp hR0 hv hvrad hv1 h
    (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) hMbox hℓ hd hR hRχ u
    (by simpa only [mfV] using hvol) (N := N) (Φ := Φ) hΦc
  simpa only [mfA2, mfM2, mfPc, mfV, boxA, boxW, boxW1] using key

/-- **`Pc ≤ S·(N−1)`** — the sharp form of `boxPairCount_le_N_mul_flatCount`, from the three
spectral moments `n0Moments_threeB1`/`n0Moments_twoB1`: with `m_S := ∫(n0ProjOp S Φ)² ≥ 0`,

    Pc = Σ_S (|S|² − |S|)·m_S ≤ (N−1)·Σ_S |S|·m_S = (N−1)·S .

This is the `(R3)`-step of the ledger of `FINDING_mfPairingSquaresB1_reduction.md`: it hands the
`n₊`-part of `Pc` to the `e₅`-term of the target. -/
theorem boxPairCount_le_flatCount_mul {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    boxPairCount volA ℓ A Φ ≤ boxFlatCount volA ℓ A Φ * ((N : ℝ) - 1) := by
  have h2 := n0Moments_twoB1 (N := N) hℓ hvol hA hvolA hAc hΦc
  have h3 := n0Moments_threeB1 (N := N) hℓ hvol hA hvolA hAc hΦc
  have hsplit : (∑ S : Finset (Fin N), (((S.card : ℝ) ^ 2) - (S.card : ℝ))
        * (∫ x in Submission.BoseGases.abox N ℓ, (n0ProjOp volA A S Φ x) ^ 2))
      = (∑ S : Finset (Fin N), ((S.card : ℝ) ^ 2)
          * (∫ x in Submission.BoseGases.abox N ℓ, (n0ProjOp volA A S Φ x) ^ 2))
        - (∑ S : Finset (Fin N), (S.card : ℝ)
          * (∫ x in Submission.BoseGases.abox N ℓ, (n0ProjOp volA A S Φ x) ^ 2)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun S _ => by ring
  have hPc : boxPairCount volA ℓ A Φ
      = ∑ S : Finset (Fin N), (((S.card : ℝ) ^ 2) - (S.card : ℝ))
          * (∫ x in Submission.BoseGases.abox N ℓ, (n0ProjOp volA A S Φ x) ^ 2) := by
    rw [hsplit, h3, h2]
    ring
  rw [hPc]
  have hper : ∀ S : Finset (Fin N),
      (((S.card : ℝ) ^ 2) - (S.card : ℝ))
          * (∫ x in Submission.BoseGases.abox N ℓ, (n0ProjOp volA A S Φ x) ^ 2)
        ≤ ((N : ℝ) - 1) * ((S.card : ℝ)
          * (∫ x in Submission.BoseGases.abox N ℓ, (n0ProjOp volA A S Φ x) ^ 2)) := by
    intro S
    have hm : 0 ≤ ∫ x in Submission.BoseGases.abox N ℓ, (n0ProjOp volA A S Φ x) ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    have hk : (S.card : ℝ) ≤ (N : ℝ) := by
      have h := Finset.card_le_univ S
      rw [Fintype.card_fin] at h
      exact_mod_cast h
    have hk0 : (0 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast (Nat.zero_le S.card)
    have hkey : (S.card : ℝ) * ((S.card : ℝ) - 1) ≤ ((N : ℝ) - 1) * (S.card : ℝ) := by
      have h1 : (S.card : ℝ) - 1 ≤ (N : ℝ) - 1 := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hk0
      linarith [h2]
    nlinarith [hm, hkey]
  calc ∑ S : Finset (Fin N), (((S.card : ℝ) ^ 2) - (S.card : ℝ))
          * (∫ x in Submission.BoseGases.abox N ℓ, (n0ProjOp volA A S Φ x) ^ 2)
      ≤ ∑ S : Finset (Fin N), ((N : ℝ) - 1) * ((S.card : ℝ)
          * (∫ x in Submission.BoseGases.abox N ℓ, (n0ProjOp volA A S Φ x) ^ 2)) :=
        Finset.sum_le_sum fun S _ => hper S
    _ = ((N : ℝ) - 1) * boxFlatCount volA ℓ A Φ := by
        rw [← Finset.mul_sum, h2]
    _ = boxFlatCount volA ℓ A Φ * ((N : ℝ) - 1) := by ring

/-- **The deficit bound `N(N−1) − Pc ≤ 2N·n₊`.**  From the Jensen bound
`boxFlatSqJensen` (`S² − S·∫Φ² ≤ (∫Φ²)·Pc`) at a normalised state and the count split
`S + n₊ = N`:

    N(N−1) − Pc ≤ N(N−1) − S² + S = (N−S)(N+S−1) = n₊·(N+S−1) ≤ 2N·n₊ .

This is the step that hands the *whole* deficit of the target's pair-condensate term to the
`e₅`-slack `C·a(N+1)n₊/V`, i.e. it is what makes the target's `n₊`-correction legitimate. -/
theorem deficit_le_two_mul_nq {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hΦnorm : ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 = 1)
    (hcount : boxFlatCount volA ℓ A Φ + boxQCount volA ℓ A Φ = (N : ℝ)) :
    (N : ℝ) * ((N : ℝ) - 1) - boxPairCount volA ℓ A Φ ≤ 2 * (N : ℝ) * boxQCount volA ℓ A Φ := by
  have hj := boxFlatSqJensen (N := N) hℓ hvol hA hvolA hAc hΦc
  have hj' : boxFlatCount volA ℓ A Φ ^ 2 - boxFlatCount volA ℓ A Φ ≤ boxPairCount volA ℓ A Φ := by
    simpa only [hΦnorm, mul_one, one_mul] using hj
  have hnl : 0 ≤ boxQCount volA ℓ A Φ := by
    rw [boxQCount]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  have hS : boxFlatCount volA ℓ A Φ ≤ (N : ℝ) := by linarith
  nlinarith [hj', hnl, hS, hN0, hcount, mul_nonneg hnl hN0,
    sq_nonneg (boxFlatCount volA ℓ A Φ)]

/-- **The `e₅`-slack covers the deficit.**  If `M₂ ≤ K·(a v)·χ_B` (the PROVED
`boxM2LeConstMulChiMass`) and `K·N·χ_B ≤ C·(N+1)·V`, then the target's `n₊`-term
`C·a·((N+1)/V)·n₊` dominates `(M₂/V²)·N·n₊` - i.e. it pays the whole deficit supplied by
`deficit_le_two_mul_nq`.  At `Adm` parameters `χ_B ≍ V`, so the hypothesis on `C` reduces to
`C ≳ K`: this is how the target's *free* constant absorbs the `n₊`-correction. -/
theorem e5_covers_deficit {v : EuclideanSpace ℝ (Fin 3) → ℝ} {M : ℕ} (h : Work.UBB.ScatSol v)
    {μ : ℝ} {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    {C K : ℝ} (hK : mfM2 h μ u ≤ K * (_root_.BoseGases.a v) * mfChi v μ u)
    (hC : K * (N : ℝ) * mfChi v μ u ≤ C * ((N : ℝ) + 1) * mfV v μ u)
    (hnq : 0 ≤ mfQ v μ N Φ u) (hV : 0 < mfV v μ u) (ha : 0 ≤ _root_.BoseGases.a v) :
    (mfM2 h μ u / (mfV v μ u) ^ 2) * (N : ℝ) * mfQ v μ N Φ u
      ≤ C * (_root_.BoseGases.a v) * (((N : ℝ) + 1) / mfV v μ u) * mfQ v μ N Φ u := by
  have hV2 : (0 : ℝ) < (mfV v μ u) ^ 2 := pow_pos hV 2
  have hV1 : (0 : ℝ) ≤ (N : ℝ) * mfQ v μ N Φ u / (mfV v μ u) ^ 2 :=
    div_nonneg (mul_nonneg (by exact_mod_cast (Nat.zero_le N)) hnq) hV2.le
  have h1 : mfM2 h μ u * ((N : ℝ) * mfQ v μ N Φ u / (mfV v μ u) ^ 2)
      ≤ (K * (_root_.BoseGases.a v) * mfChi v μ u)
        * ((N : ℝ) * mfQ v μ N Φ u / (mfV v μ u) ^ 2) :=
    mul_le_mul_of_nonneg_right hK hV1
  have h2 : (K * (_root_.BoseGases.a v) * mfChi v μ u)
        * ((N : ℝ) * mfQ v μ N Φ u / (mfV v μ u) ^ 2)
      = (_root_.BoseGases.a v)
        * ((K * (N : ℝ) * mfChi v μ u) * (mfQ v μ N Φ u / (mfV v μ u) ^ 2)) := by ring
  have h3 : (K * (N : ℝ) * mfChi v μ u) * (mfQ v μ N Φ u / (mfV v μ u) ^ 2)
      ≤ (C * ((N : ℝ) + 1) * mfV v μ u) * (mfQ v μ N Φ u / (mfV v μ u) ^ 2) :=
    mul_le_mul_of_nonneg_right hC (div_nonneg hnq hV2.le)
  have h4 : (C * ((N : ℝ) + 1) * mfV v μ u) * (mfQ v μ N Φ u / (mfV v μ u) ^ 2)
      = C * ((N : ℝ) + 1) * (mfQ v μ N Φ u / mfV v μ u) := by
    field_simp
  have h4b : (_root_.BoseGases.a v) * (C * ((N : ℝ) + 1) * (mfQ v μ N Φ u / mfV v μ u))
      = C * (_root_.BoseGases.a v) * (((N : ℝ) + 1) / mfV v μ u) * mfQ v μ N Φ u := by
    field_simp
  have h5 : mfM2 h μ u * ((N : ℝ) * mfQ v μ N Φ u / (mfV v μ u) ^ 2)
      ≤ (_root_.BoseGases.a v) * (C * ((N : ℝ) + 1) * (mfQ v μ N Φ u / mfV v μ u)) := by
    rw [h2] at h1
    have h3' := mul_le_mul_of_nonneg_left h3 ha
    have h4a : (_root_.BoseGases.a v) * ((C * ((N : ℝ) + 1) * mfV v μ u)
          * (mfQ v μ N Φ u / (mfV v μ u) ^ 2))
        = (_root_.BoseGases.a v) * (C * ((N : ℝ) + 1) * (mfQ v μ N Φ u / mfV v μ u)) :=
      congrArg (fun t => (_root_.BoseGases.a v) * t) h4
    linarith [h1, h3', h4a]
  have h6 : (mfM2 h μ u / (mfV v μ u) ^ 2) * (N : ℝ) * mfQ v μ N Φ u
      = mfM2 h μ u * ((N : ℝ) * mfQ v μ N Φ u / (mfV v μ u) ^ 2) := by ring
  rw [h6, ← h4b]
  exact h5

/-- **(W), the non-saturated case - the `e₅`-slack dominates the pair-condensate mass.**
Suppose the pair-condensate mass is *not* saturated (`2·Pc ≤ N(N−1)`) and the state satisfies the
deficit bound `N(N−1) − Pc ≤ 2N·n₊` (which holds for box-supported normalised states, PROVED as
`deficit_le_two_mul_nq`; the target's hypotheses do not supply box support, so it is a hypothesis
here).  Then `n₊ ≥ (N−1)/4`, and with `M₂ ≤ K·(a v)·V` the whole pair-condensate mass is paid by
the `e₅`-term:

    ½·(M₂/V²)·Pc ≤ C·(a v)·((N+1)/V)·n₊      whenever  C ≥ K·N/(N+1)  (⟸ C ≥ K).

Consequently - via `mfPairingSquares_lhs_nonpos` (LHS ≤ 0) and the identity
`mfA2_add_squares_eq` (RHS = `mfSpec + ½Σσ²w − ½(M₂/V²)Pc`) - **the target's conclusion holds for
every state with `2·Pc ≤ N(N−1)`**, leaving only the *saturated* case, which is paid by the
`χ_B`-cubic `e₄`-term and the sharp-fibre estimate (S). -/
theorem e5_dominates_Pc {v : EuclideanSpace ℝ (Fin 3) → ℝ} {M : ℕ} (h : Work.UBB.ScatSol v)
    {μ : ℝ} {N : ℕ} (hN : 1 ≤ N) {Φ : Submission.BoseGases.X N → ℝ}
    {u : EuclideanSpace ℝ (Fin 3)}
    {C K : ℝ} (hM2 : mfM2 h μ u ≤ K * (_root_.BoseGases.a v) * mfV v μ u)
    (hC : K * (N : ℝ) ≤ C * ((N : ℝ) + 1))
    (hPc : 2 * mfPc v μ N Φ u ≤ (N : ℝ) * ((N : ℝ) - 1))
    (hdef : (N : ℝ) * ((N : ℝ) - 1) - mfPc v μ N Φ u ≤ 2 * (N : ℝ) * mfQ v μ N Φ u)
    (hnq : 0 ≤ mfQ v μ N Φ u) (hV : 0 < mfV v μ u)
    (hK : 0 ≤ K) (ha : 0 ≤ _root_.BoseGases.a v) :
    (1 / 2) * (mfM2 h μ u / (mfV v μ u) ^ 2) * mfPc v μ N Φ u
      ≤ C * (_root_.BoseGases.a v) * (((N : ℝ) + 1) / mfV v μ u) * mfQ v μ N Φ u := by
  have hN1n : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by linarith
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by linarith
  have hC0 : (0 : ℝ) ≤ C := by
    have h1 : (0 : ℝ) ≤ K * (N : ℝ) := mul_nonneg hK hN0
    have h2 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
    exact nonneg_of_mul_nonneg_right (le_trans h1 (by linarith [hC])) h2
  -- (1) `n₊ ≥ (N−1)/4` from the deficit bound and the non-saturation
  have hPc' : mfPc v μ N Φ u ≤ (N : ℝ) * ((N : ℝ) - 1) / 2 := by nlinarith [hPc]
  have hPc0 : 0 ≤ mfPc v μ N Φ u := by
    simp only [mfPc, boxPairCount]
    exact Finset.sum_nonneg fun p _ => integral_nonneg fun x => sq_nonneg _
  have hnq_ge : ((N : ℝ) - 1) / 4 ≤ mfQ v μ N Φ u := by nlinarith [hPc, hdef, hN1n, hN1, hN0]
  -- (2) the cleared comparison `½ M₂ Pc ≤ C a (N+1) V n₊`
  have hmul : mfM2 h μ u * mfPc v μ N Φ u
      ≤ (K * (_root_.BoseGases.a v) * mfV v μ u) * ((N : ℝ) * ((N : ℝ) - 1) / 2) :=
    mul_le_mul hM2 hPc' hPc0 (mul_nonneg (mul_nonneg hK ha) hV.le)
  have hV4 : (0 : ℝ) ≤ mfV v μ u * ((N : ℝ) - 1) / 4 :=
    div_nonneg (mul_nonneg hV.le hN1) (by norm_num)
  have hC' : K * (N : ℝ) * (mfV v μ u * ((N : ℝ) - 1) / 4)
      ≤ C * ((N : ℝ) + 1) * (mfV v μ u * ((N : ℝ) - 1) / 4) :=
    mul_le_mul_of_nonneg_right hC hV4
  have hCa : (0 : ℝ) ≤ C * (_root_.BoseGases.a v) * mfV v μ u :=
    mul_nonneg (mul_nonneg hC0 ha) hV.le
  have hC'C : (C * (_root_.BoseGases.a v) * mfV v μ u) * ((N : ℝ) - 1) / 4
      ≤ (C * (_root_.BoseGases.a v) * mfV v μ u) * mfQ v μ N Φ u := by
    have := mul_le_mul_of_nonneg_left hnq_ge hCa
    linarith [this]
  have hCn : C * (_root_.BoseGases.a v) * (mfV v μ u * ((N : ℝ) - 1) / 4)
      ≤ C * (_root_.BoseGases.a v) * (mfV v μ u * mfQ v μ N Φ u) := by
    nlinarith [hC'C]
  have hcleared : (1 / 2) * mfM2 h μ u * mfPc v μ N Φ u
      ≤ C * (_root_.BoseGases.a v) * ((N : ℝ) + 1) * mfV v μ u * mfQ v μ N Φ u := by
    nlinarith [hmul, mul_le_mul_of_nonneg_left hC' ha, hCn, hV.le, hN1, hN0, ha, hK, hC0]
  -- (3) convert to the divided form
  have hV2 : (0 : ℝ) < (mfV v μ u) ^ 2 := pow_pos hV 2
  have hL : (1 / 2) * (mfM2 h μ u / (mfV v μ u) ^ 2) * mfPc v μ N Φ u
      = ((1 / 2) * mfM2 h μ u * mfPc v μ N Φ u) / (mfV v μ u) ^ 2 := by ring
  rw [hL, div_le_iff₀ hV2]
  have hR : (C * (_root_.BoseGases.a v) * (((N : ℝ) + 1) / mfV v μ u)
        * mfQ v μ N Φ u) * (mfV v μ u) ^ 2
      = C * (_root_.BoseGases.a v) * ((N : ℝ) + 1) * mfV v μ u * mfQ v μ N Φ u := by
    field_simp
  rw [hR]
  exact hcleared

/-- **The target's left-hand side is `≤ 0`.**  Each of the five summands of the target's left side
carries a minus sign in front of a nonnegative quantity: `0 ≤ M₂ − M₁`
(`boxM2_sub_boxM1_nonneg_slidingB1`), `Cut > 0` (`sbCut_pos`), `χ_B ≥ 0` (a square integral),
`n₊ ≥ 0`, `V > 0`, `a v > 0`, `N ≥ 0`, `C ≥ 0`, `R ≥ 0`.  Consequently the target is *equivalent*
to the inequality (T) of `FINDING_mfPairingSquaresB1_reduction.md`. -/
theorem mfPairingSquares_lhs_nonpos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) (hav : 0 < _root_.BoseGases.a v) {μ : ℝ} (hμ : 0 < μ)
    (hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hR : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < mfV v μ u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} {C : ℝ} (hC : 0 ≤ C) :
    - (1 / 2) * (1 + C * (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
          + (_root_.BoseGases.a v) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        * (mfM2 h μ u - mfM1 h μ u)
        * (((N : ℝ) + 1) * (N : ℝ) / mfV v μ u ^ 2)
    - C * (mfM2 h μ u - mfM1 h μ u) * mfCut v μ
        * (1 + |Real.log (1 / (mfCut v μ * (_root_.BoseGases.a v)))|)
        * (((N : ℝ) + 1) * (N : ℝ) / mfV v μ u ^ 2)
    - C * (mfM2 h μ u - mfM1 h μ u) * (_root_.BoseGases.a v) ^ 3
        * (mfCut v μ) ^ (-(3 : ℝ))
        * (((N : ℝ) + 1) ^ 3 * (N : ℝ)) / mfV v μ u ^ 4
    - C * (_root_.BoseGases.a v) * (mfCut v μ) ^ (3 : ℝ)
        * ((N : ℝ) * mfChi v μ u / mfV v μ u)
    - C * (_root_.BoseGases.a v) * (((N : ℝ) + 1) / mfV v μ u)
        * mfQ v μ N Φ u ≤ 0 := by
  have hM21 : 0 ≤ mfM2 h μ u - mfM1 h μ u :=
    boxM2_sub_boxM1_nonneg_slidingB1 (v := v) (R := R) hv_supp hR0 hv hvrad hv1 h hav hM
      hℓ hd hR hRχ u
  have hcut : 0 < mfCut v μ := sbCut_pos hμ hav
  have hchi : 0 ≤ mfChi v μ u := by
    rw [mfChi, Work.SmallBoxSliding.chiMass_def]
    exact integral_nonneg fun x => sq_nonneg _
  have hnq : 0 ≤ mfQ v μ N Φ u := by
    rw [mfQ, Work.UBBInputs8.cnPlusBoxInd]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hV : 0 < mfV v μ u := hvol
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith [hN0]
  have hη : (0 : ℝ) ≤ 1 + C * (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      + (_root_.BoseGases.a v) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) := by
    have h1 : (0 : ℝ) ≤ R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) :=
      div_nonneg hR0.le (mul_pos hℓ hd).le
    have h2 : (0 : ℝ) ≤ (_root_.BoseGases.a v) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
      div_nonneg hav.le hℓ.le
    nlinarith [mul_nonneg hC (add_nonneg h1 h2)]
  have hNN : (0 : ℝ) ≤ ((N : ℝ) + 1) * (N : ℝ) / mfV v μ u ^ 2 :=
    div_nonneg (mul_nonneg hN1.le hN0) (pow_pos hvol 2).le
  have hP1 : 0 ≤ (1 / 2) * (1 + C * (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
        + (_root_.BoseGases.a v) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
      * (mfM2 h μ u - mfM1 h μ u)
      * (((N : ℝ) + 1) * (N : ℝ) / mfV v μ u ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hη) hM21) hNN
  have hP2 : 0 ≤ C * (mfM2 h μ u - mfM1 h μ u) * mfCut v μ
      * (1 + |Real.log (1 / (mfCut v μ * (_root_.BoseGases.a v)))|)
      * (((N : ℝ) + 1) * (N : ℝ) / mfV v μ u ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hM21) hcut.le)
      (one_add_abs_log_nonneg _)) hNN
  have hP3 : 0 ≤ C * (mfM2 h μ u - mfM1 h μ u) * (_root_.BoseGases.a v) ^ 3
      * (mfCut v μ) ^ (-(3 : ℝ))
      * (((N : ℝ) + 1) ^ 3 * (N : ℝ)) / mfV v μ u ^ 4 :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hM21)
      (pow_nonneg hav.le 3)) (rpow_neg_three_nonneg hcut.le))
      (mul_nonneg (pow_nonneg hN1.le 3) hN0)) (pow_pos hvol 4).le
  have hP4 : 0 ≤ C * (_root_.BoseGases.a v) * (mfCut v μ) ^ (3 : ℝ)
      * ((N : ℝ) * mfChi v μ u / mfV v μ u) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hav.le) (rpow_three_nonneg hcut.le))
      (div_nonneg (mul_nonneg hN0 hchi) hV.le)
  have hP5 : 0 ≤ C * (_root_.BoseGases.a v) * (((N : ℝ) + 1) / mfV v μ u)
      * mfQ v μ N Φ u :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hav.le) (div_nonneg hN1.le hV.le)) hnq
  linarith [hP1, hP2, hP3, hP4, hP5]

/-- **The conclusion of the target, as a `Prop`** (the `mf*` vocabulary of the target, so that
the case lemmas below can be stated uniformly).  It is `boxConcl`-shaped: the (negative) demand
of FS's `eq:refinedaprioribog` against `mfSpec + mfA2 + boxSqPart + boxCrossPart`. -/
abbrev mfConcl {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (h : Work.UBB.ScatSol v)
    (μ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (N : ℕ)
    (Φ : Submission.BoseGases.X N → ℝ) (C : ℝ) : Prop :=
    - (1 / 2) * (1 + C * (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
          + (_root_.BoseGases.a v) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        * (mfM2 h μ u - mfM1 h μ u)
        * (((N : ℝ) + 1) * (N : ℝ) / mfV v μ u ^ 2)
    - C * (mfM2 h μ u - mfM1 h μ u) * mfCut v μ
        * (1 + |Real.log (1 / (mfCut v μ * (_root_.BoseGases.a v)))|)
        * (((N : ℝ) + 1) * (N : ℝ) / mfV v μ u ^ 2)
    - C * (mfM2 h μ u - mfM1 h μ u) * (_root_.BoseGases.a v) ^ 3
        * (mfCut v μ) ^ (-(3 : ℝ))
        * (((N : ℝ) + 1) ^ 3 * (N : ℝ)) / mfV v μ u ^ 4
    - C * (_root_.BoseGases.a v) * (mfCut v μ) ^ (3 : ℝ)
        * ((N : ℝ) * mfChi v μ u / mfV v μ u)
    - C * (_root_.BoseGases.a v) * (((N : ℝ) + 1) / mfV v μ u)
        * mfQ v μ N Φ u
    ≤ mfSpec v μ N Φ u + mfA2 h μ N Φ u
      + Work.BoseFixB1.boxSqPart (mfV v μ u)
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (boxA v μ u)
          (boxW h μ u) (Submission.BoseGases.omC (Classical.choose h)) Φ
      + Work.BoseFixB1.boxCrossPart (mfV v μ u)
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (boxA v μ u) (boxW1 h μ u) Φ

/-- The *demand* of the target: its five left-hand summands with the signs stripped.  The target
is `-mfDemand ≤ mfSpec + mfA2 + boxSqPart + boxCrossPart`, so `mfDemand` is the quantity the
state-independent terms (`e₂`,`e₃`,`e₄`,`e₅` and the pair-mass payer) have to beat. -/
abbrev mfDemand {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) (N : ℕ) (Φ : Submission.BoseGases.X N → ℝ) (C : ℝ) : ℝ :=
  (1 / 2) * (1 + C * (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
        + (_root_.BoseGases.a v) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
      * (mfM2 h μ u - mfM1 h μ u)
      * (((N : ℝ) + 1) * (N : ℝ) / mfV v μ u ^ 2)
  + C * (mfM2 h μ u - mfM1 h μ u) * mfCut v μ
      * (1 + |Real.log (1 / (mfCut v μ * (_root_.BoseGases.a v)))|)
      * (((N : ℝ) + 1) * (N : ℝ) / mfV v μ u ^ 2)
  + C * (mfM2 h μ u - mfM1 h μ u) * (_root_.BoseGases.a v) ^ 3
      * (mfCut v μ) ^ (-(3 : ℝ))
      * (((N : ℝ) + 1) ^ 3 * (N : ℝ)) / mfV v μ u ^ 4
  + C * (_root_.BoseGases.a v) * (mfCut v μ) ^ (3 : ℝ)
      * ((N : ℝ) * mfChi v μ u / mfV v μ u)
  + C * (_root_.BoseGases.a v) * (((N : ℝ) + 1) / mfV v μ u) * mfQ v μ N Φ u

/-- The manifest `σ²`-mass `Σ_p∫σ_p²w` of the reduction (★)
(`mfA2_add_squares_eq`). -/
abbrev mfSig {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) (N : ℕ)
    (Φ : Submission.BoseGases.X N → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet N,
    ∫ x in Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (((boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.1))
        * ((boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2
        * (boxW h μ u (x p.1) (x p.2))

/-- The reduction (★) of `mfA2_add_squares_eq`, stated in the abbreviations of this file. -/
theorem mfA2_add_squares_eq' {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) (hav : 0 < _root_.BoseGases.a v) {μ : ℝ}
    (hMbox : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hR : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < mfV v μ u) {N : ℕ}
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    mfA2 h μ N Φ u
      + Work.BoseFixB1.boxSqPart (mfV v μ u) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (boxA v μ u) (boxW h μ u) (Submission.BoseGases.omC (Classical.choose h)) Φ
      + Work.BoseFixB1.boxCrossPart (mfV v μ u) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (boxA v μ u) (boxW1 h μ u) Φ
    = (1 / 2) * mfSig h μ N Φ u - (1 / 2) * (mfM2 h μ u / (mfV v μ u) ^ 2) * mfPc v μ N Φ u :=
  mfA2_add_squares_eq (v := v) (R := R) hv_supp hR0 hv hvrad hv1 h hav hMbox hℓ hd hR hRχ u
    hvol hΦc

/-- The target's conclusion is `-mfDemand ≤ mfSpec + mfA2 + boxSqPart + boxCrossPart`. -/
theorem mfConcl_iff {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (h : Work.UBB.ScatSol v)
    (μ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (N : ℕ)
    (Φ : Submission.BoseGases.X N → ℝ) (C : ℝ) :
    mfConcl (v := v) (R := R) h μ u N Φ C ↔
      - mfDemand (v := v) (R := R) h μ u N Φ C
        ≤ mfSpec v μ N Φ u + mfA2 h μ N Φ u
          + Work.BoseFixB1.boxSqPart (mfV v μ u)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (boxA v μ u)
              (boxW h μ u) (Submission.BoseGases.omC (Classical.choose h)) Φ
          + Work.BoseFixB1.boxCrossPart (mfV v μ u)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (boxA v μ u) (boxW1 h μ u) Φ := by
  simp only [mfConcl, mfDemand]
  constructor <;> intro hh <;> linarith [hh]

/-- The demand is nonnegative whenever the parameters are (it is a sum of five nonnegative
terms: `0 ≤ M₂ − M₁` (PROVED, `boxM2_sub_boxM1_nonneg_slidingB1`), `Cut > 0`, `χ_B ≥ 0`,
`n₊ ≥ 0`, `V > 0`, `a v > 0`, `C ≥ 0`, `N ≥ 0`, `R ≥ 0`). -/
theorem mfDemand_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) (hav : 0 < _root_.BoseGases.a v) {μ : ℝ} (hμ : 0 < μ)
    (hMbox : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hR : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < mfV v μ u) {N : ℕ}
    {Φ : Submission.BoseGases.X N → ℝ} {C : ℝ}
    (hC : 0 ≤ C) : 0 ≤ mfDemand (v := v) (R := R) h μ u N Φ C := by
  have hM21 : 0 ≤ mfM2 h μ u - mfM1 h μ u :=
    boxM2_sub_boxM1_nonneg_slidingB1 (v := v) (R := R) hv_supp hR0 hv hvrad hv1 h hav hMbox
      hℓ hd hR hRχ u
  have hcut : 0 < mfCut v μ := sbCut_pos hμ hav
  have hchi : 0 ≤ mfChi v μ u := by
    rw [mfChi, Work.SmallBoxSliding.chiMass_def]
    exact integral_nonneg fun x => sq_nonneg _
  have hnq : 0 ≤ mfQ v μ N Φ u := by
    rw [mfQ, Work.UBBInputs8.cnPlusBoxInd]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith [hN0]
  have hη : (0 : ℝ) ≤ 1 + C * (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      + (_root_.BoseGases.a v) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) := by
    have h1 : (0 : ℝ) ≤ R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) :=
      div_nonneg hR0.le (mul_pos hℓ hd).le
    have h2 : (0 : ℝ) ≤ (_root_.BoseGases.a v) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
      div_nonneg hav.le hℓ.le
    nlinarith [mul_nonneg hC (add_nonneg h1 h2)]
  have hNN : (0 : ℝ) ≤ ((N : ℝ) + 1) * (N : ℝ) / mfV v μ u ^ 2 :=
    div_nonneg (mul_nonneg hN1.le hN0) (pow_pos hvol 2).le
  have hP1 : 0 ≤ (1 / 2) * (1 + C * (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
        + (_root_.BoseGases.a v) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
      * (mfM2 h μ u - mfM1 h μ u)
      * (((N : ℝ) + 1) * (N : ℝ) / mfV v μ u ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hη) hM21) hNN
  have hP2 : 0 ≤ C * (mfM2 h μ u - mfM1 h μ u) * mfCut v μ
      * (1 + |Real.log (1 / (mfCut v μ * (_root_.BoseGases.a v)))|)
      * (((N : ℝ) + 1) * (N : ℝ) / mfV v μ u ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hM21) hcut.le)
      (one_add_abs_log_nonneg _)) hNN
  have hP3 : 0 ≤ C * (mfM2 h μ u - mfM1 h μ u) * (_root_.BoseGases.a v) ^ 3
      * (mfCut v μ) ^ (-(3 : ℝ))
      * (((N : ℝ) + 1) ^ 3 * (N : ℝ)) / mfV v μ u ^ 4 :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hM21)
      (pow_nonneg hav.le 3)) (rpow_neg_three_nonneg hcut.le))
      (mul_nonneg (pow_nonneg hN1.le 3) hN0)) (pow_pos hvol 4).le
  have hP4 : 0 ≤ C * (_root_.BoseGases.a v) * (mfCut v μ) ^ (3 : ℝ)
      * ((N : ℝ) * mfChi v μ u / mfV v μ u) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hav.le) (rpow_three_nonneg hcut.le))
      (div_nonneg (mul_nonneg hN0 hchi) hvol.le)
  have hP5 : 0 ≤ C * (_root_.BoseGases.a v) * (((N : ℝ) + 1) / mfV v μ u)
      * mfQ v μ N Φ u :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hav.le) (div_nonneg hN1.le hvol.le)) hnq
  simp only [mfDemand]
  linarith [hP1, hP2, hP3, hP4, hP5]

/-- **The easy case of the target.**  Whenever the five LHS summands (the pair-mass payer and the
`e₂`–`e₅` errors) alone dominate the *maximal* pair-condensate mass `½(M₂/V²)·N(N−1)`, the target's
conclusion holds — with no state-level input beyond `Pc ≤ N(N−1)` (PROVED:
`boxPairCount_le_flatCount_mul` + `boxFlatCount_le_NB1`), `mfSpec ≥ 0`
(`Work.BoseFixB1.tBwordKinInd_nonneg`) and `Σσ²w ≥ 0` (`wSmallPair_nonneg_B1S`), via the
reduction (★) `mfA2_add_squares_eq`.  In particular this covers the two state-independent
sub-cases: `N ≤ 1 + 2C·Cut³·V/K` (paid by `e₄`) and `n₊ ≥ K·C₂·N/(2C)` (paid by `e₅`), so that
the *only* remaining content of the target is the complementary regime. -/
theorem mfConcl_of_demand_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) (hav : 0 < _root_.BoseGases.a v) {μ : ℝ} (hμ : 0 < μ)
    (hMbox : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hR : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < mfV v μ u) {N : ℕ} (hN : 1 ≤ N)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) {C : ℝ} (hC : 0 ≤ C)
    (hnorm : ∫ x in Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Φ x) ^ 2 = 1)
    (hQ : (1 / 2) * (mfM2 h μ u / mfV v μ u ^ 2) * ((N : ℝ) * ((N : ℝ) - 1))
        ≤ mfDemand (v := v) (R := R) h μ u N Φ C) :
    mfConcl (v := v) (R := R) h μ u N Φ C := by
  rw [mfConcl_iff]
  have hstar := mfA2_add_squares_eq' (v := v) (R := R) hv_supp hR0 hv hvrad hv1 h hav hMbox hℓ
    hd hR hRχ u hvol hΦc
  have hspec : 0 ≤ mfSpec v μ N Φ u := Work.BoseFixB1.tBwordKinInd_nonneg Φ
  have hsigW : ∀ x y : EuclideanSpace ℝ (Fin 3), 0 ≤ boxW h μ u x y :=
    fun x y => Work.BoseFixB1S.wSmallPair_nonneg_B1S u x y (hv (x - y))
  have hsig : 0 ≤ mfSig h μ N Φ u := by
    refine Finset.sum_nonneg fun p _ => integral_nonneg fun x => ?_
    exact mul_nonneg (sq_nonneg _) (hsigW (x p.1) (x p.2))
  have hsig2 : 0 ≤ (1 / 2) * mfSig h μ N Φ u := mul_nonneg (by norm_num) hsig
  have hPc0 : 0 ≤ mfPc v μ N Φ u := by
    simp only [mfPc, boxPairCount]
    exact Finset.sum_nonneg fun p _ => integral_nonneg fun x => sq_nonneg _
  have hPc : mfPc v μ N Φ u ≤ (N : ℝ) * ((N : ℝ) - 1) := by
    have h1 : mfPc v μ N Φ u
        ≤ boxFlatCount (mfV v μ u) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (boxA v μ u) Φ * ((N : ℝ) - 1) :=
      boxPairCount_le_flatCount_mul (N := N) hℓ hvol
        (Work.SmallBoxSliding.measurableSet_dlBox _ _ _)
        (Work.SmallBoxSliding.boxMass_eq_measureReal _ _ _)
        (Work.SmallBoxSliding.dlBox_subset_acube _ _ _) hΦc
    have h2 : boxFlatCount (mfV v μ u) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (boxA v μ u) Φ ≤ (N : ℝ) := by
      have hb := boxFlatCount_le_NB1 (N := N) hℓ hvol
        (Work.SmallBoxSliding.measurableSet_dlBox _ _ _)
        (Work.SmallBoxSliding.dlBox_subset_acube _ _ _)
        (Work.SmallBoxSliding.boxMass_eq_measureReal _ _ _) hΦc
      rw [hnorm, mul_one] at hb
      exact hb
    have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    calc mfPc v μ N Φ u
        ≤ boxFlatCount (mfV v μ u) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (boxA v μ u) Φ * ((N : ℝ) - 1) := h1
      _ ≤ (N : ℝ) * ((N : ℝ) - 1) := mul_le_mul_of_nonneg_right h2 hN1
  have key : (1 / 2) * (mfM2 h μ u / mfV v μ u ^ 2) * mfPc v μ N Φ u
      ≤ mfDemand (v := v) (R := R) h μ u N Φ C := by
    by_cases hM2 : 0 ≤ mfM2 h μ u
    · have hcoef : 0 ≤ (1 / 2) * (mfM2 h μ u / mfV v μ u ^ 2) :=
        mul_nonneg (by norm_num) (div_nonneg hM2 (pow_pos hvol 2).le)
      exact le_trans (mul_le_mul_of_nonneg_left hPc hcoef) hQ
    · have hM2' : mfM2 h μ u ≤ 0 := (not_le.mp hM2).le
      have hcoef : (1 / 2) * (mfM2 h μ u / mfV v μ u ^ 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by norm_num)
          (div_nonpos_of_nonpos_of_nonneg hM2' (pow_pos hvol 2).le)
      have hzero : (1 / 2) * (mfM2 h μ u / mfV v μ u ^ 2) * mfPc v μ N Φ u ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hcoef hPc0
      exact le_trans hzero
        (mfDemand_nonneg (v := v) (R := R) hv_supp hR0 hv hvrad hv1 h hav hμ hMbox hℓ hd hR
          hRχ u hvol hC)
  linarith [hstar, hspec, hsig2, key]

theorem mfPairingSquaresB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) (hav : 0 < _root_.BoseGases.a v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ u : EuclideanSpace ℝ (Fin 3),
        Work.BoseFixB1S.mfInt v μ u →
        ∀ {N : ℕ}, 1 ≤ N → ∀ {Φ : Submission.BoseGases.X N → ℝ},
          ContDiff ℝ (⊤ : ℕ∞) Φ →
          (∫ x in Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Φ x) ^ 2) = 1 →
          - (1 / 2) * (1 + C * (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
                + (_root_.BoseGases.a v) / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
              * (Work.BoseFixB1S.mfM2 h μ u - Work.BoseFixB1S.mfM1 h μ u)
              * (((N : ℝ) + 1) * (N : ℝ) / Work.BoseFixB1S.mfV v μ u ^ 2)
          - C * (Work.BoseFixB1S.mfM2 h μ u - Work.BoseFixB1S.mfM1 h μ u) * Work.BoseFixB1S.mfCut v μ
              * (1 + |Real.log (1 / (Work.BoseFixB1S.mfCut v μ * (_root_.BoseGases.a v)))|)
              * (((N : ℝ) + 1) * (N : ℝ) / Work.BoseFixB1S.mfV v μ u ^ 2)
          - C * (Work.BoseFixB1S.mfM2 h μ u - Work.BoseFixB1S.mfM1 h μ u) * (_root_.BoseGases.a v) ^ 3
              * (Work.BoseFixB1S.mfCut v μ) ^ (-(3 : ℝ))
              * (((N : ℝ) + 1) ^ 3 * (N : ℝ)) / Work.BoseFixB1S.mfV v μ u ^ 4
          - C * (_root_.BoseGases.a v) * (Work.BoseFixB1S.mfCut v μ) ^ (3 : ℝ)
              * ((N : ℝ) * Work.BoseFixB1S.mfChi v μ u / Work.BoseFixB1S.mfV v μ u)
          - C * (_root_.BoseGases.a v) * (((N : ℝ) + 1) / Work.BoseFixB1S.mfV v μ u)
              * Work.BoseFixB1S.mfQ v μ N Φ u
          ≤ Work.BoseFixB1S.mfSpec v μ N Φ u + Work.BoseFixB1S.mfA2 h μ N Φ u
            + Work.BoseFixB1.boxSqPart (Work.BoseFixB1S.mfV v μ u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Work.BoseFixB1S.boxA v μ u)
                (Work.BoseFixB1S.boxW h μ u) (Submission.BoseGases.omC (Classical.choose h)) Φ
            + Work.BoseFixB1.boxCrossPart (Work.BoseFixB1S.mfV v μ u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Work.BoseFixB1S.boxA v μ u)
                (Work.BoseFixB1S.boxW1 h μ u) Φ
    := by sorry

end

end Work.BoseFixB1S
