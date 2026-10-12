import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseB1Cube.cubeDenseDev_le_pairQCount
import Submission.Work.BoseB1Cube.swhChiMassSqLe
import Submission.Work.BoseB1Cube.swhCruxSqrtSum
import Submission.Work.BoseB1Cube.swhManifestInst
import Submission.Work.BoseB1Cube.swhManifestReduced
import Submission.Work.BoseB1Cube.swhPayoutBook
import Submission.Work.BoseB1Cube.swhQBound
import Submission.Work.BoseB1Cube.swhSlidingBookkeeping
import Submission.Work.BoseB1Cube.swhTruncFactsFixed
import Submission.Work.BoseB1Cube.wSmallPair_integrableOn_pairs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.swhThinNodeProved`

Holder of `Work.BoseB1Cube.swhThinNodeProved` (node N3, the thin non-degenerate boxes, of
`Submission/Work/BoseB1Cube/smallWinNodes.lean`).

## The argument (final form)

With `bG := bGapCoeff v μ`, `Q := bQ v μ Ψ u` (the excited count), `S := bFlat v μ Ψ u`,
`V := bV v μ u`, `W := bW v h μ u`, `T := swhDem v h μ n u + μ·fibSum h _ _ _ u Ψ`:

* The matched sliding word splits as `sbWordCube = sbKinCube + sbPot`, with
  `sbKinCube = bG·Q + cubeSpectral ≥ bG·Q` and `sbPot = pairSum − μ·fibSum`. Hence it suffices to
  prove `T ≤ bG·Q + pairSum`.
* **The manifest reduction** (`swhManifestReduced`): Young's inequality on the manifest's cross
  term, with the free parameter `εη := 57(1 + Cm·a)`, gives
  `T − bG·Q ≤ k·(μWS/V)` and, in the branch `bG·Q < T`, the bound
  `Q ≤ k·W·S/(2·Kg·V·a)`, where `k = 19/18 + Cm·a/(4εη) ≤ 1.06` and `Kg` is a large fixed
  constant (the gate `4·Kg·μ·a ≤ bGapCoeff` is available for *every* prescribed `Kg`).
* **Smallness of `Q`** (`swhQBound`): the branch bound plus `W ≤ 17πa·d^79·V`, `S ≤ n ≤ 2Cn μV`
  and `d^79 ≤ 1` gives `Q ≤ (1/500)·μV`, whence `S − 1 ≥ 2.99·μV`.
* **The truncation** (`swhTruncFactsFixed` at level `K`): `boxM2(w_{v∧K}) ≥ (3/4)·W`, and the
  pointwise bound `|w_{v∧K}| ≤ Kw := 2K(smallConvLower 48)⁻¹d^79` (using `swhThin`), so the pair
  deviation obeys `D̂ ≤ 4·Kw·(n−1)·Q`.
* **The payout** (`swhPayoutGen`, the symmetry-free form of the sharp pairing payout): at the
  truncated numerator, `pairSum (v∧K) ≥ (√Â − √(D̂/2))²`, and `pairSum_min_le` transfers it to `v`.
* **The two square roots** (`swhCruxSqrtSum`): with `ϱ := 8kμV/(3(S−1))` and
  `Γ := 16Kw n Q V²/(3W(S²−S))` one has `√ϱ + √Γ ≤ 1`; the rest is the pure algebra
  `swhPayoutBook` (assembling `κ ≤ ϱÂ`, `D̂/(2Â) ≤ Γ`).

Everything else is the elementary bookkeeping `swhSlidingBookkeeping` (`0 < V`, `1 ≤ μV`,
`V ≤ (ℓd)³`, `M = 48`, the two regime inequalities), the count split `b1sCountSplit` and
`Q0C.count_ge` (`Pc ≥ S² − S`).

Note that the node's two "extra" hypotheses (`bQ < c₀`, `swhPairDead`) are **not needed**: the
dichotomy `T ≤ bG·Q` / `bG·Q < T` covers both cases directly.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000

theorem swhPayoutArith {A D θ : ℝ} (hA : 0 < A) (hD : 0 ≤ D) (hθ1 : θ ≤ 1)
    (hθ2 : Real.sqrt (D / (2 * A)) ≤ θ) :
    A * (1 - θ) ^ 2 ≤ (Real.sqrt A - Real.sqrt (D / 2)) ^ 2 := by
  have hA0 : 0 ≤ A := hA.le
  have hφ0 : 0 ≤ Real.sqrt (D / (2 * A)) := Real.sqrt_nonneg _
  have hid : Real.sqrt (D / 2) = Real.sqrt A * Real.sqrt (D / (2 * A)) := by
    rw [← Real.sqrt_mul hA0 (D / (2 * A)), show A * (D / (2 * A)) = D / 2 by field_simp]
  rw [hid]
  have h3 : A * (1 - θ) ^ 2 ≤ A * (1 - Real.sqrt (D / (2 * A))) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hA0
    nlinarith [hθ1, hθ2, hφ0]
  have hkey : (Real.sqrt A - Real.sqrt A * Real.sqrt (D / (2 * A))) ^ 2
      = A * (1 - Real.sqrt (D / (2 * A))) ^ 2 := by
    rw [show Real.sqrt A - Real.sqrt A * Real.sqrt (D / (2 * A))
        = Real.sqrt A * (1 - Real.sqrt (D / (2 * A))) by ring]
    rw [mul_pow, Real.sq_sqrt hA0]
  rw [hkey]
  exact h3

theorem swhArith {A T D r ε : ℝ} (hA : 0 < A) (hD : 0 ≤ D) (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (hcond : Real.sqrt r + Real.sqrt (ε * r) ≤ 1) (hT : T ≤ r * A)
    (hDr : D ≤ 2 * A * (ε * r)) :
    T ≤ (Real.sqrt A - Real.sqrt (D / 2)) ^ 2 := by
  have hA0 : 0 ≤ A := hA.le
  have hεr0 : 0 ≤ ε * r := mul_nonneg hε hr
  have hy0 : 0 ≤ Real.sqrt (ε * r) := Real.sqrt_nonneg _
  have hx0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hy1 : Real.sqrt (ε * r) ≤ 1 := by linarith
  have hxle : Real.sqrt r ≤ 1 - Real.sqrt (ε * r) := by linarith
  have hr2 : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr
  have hrmain : r ≤ (1 - Real.sqrt (ε * r)) ^ 2 := by nlinarith [hr2, hx0, hy0, hxle, hy1]
  have hTm : T ≤ A * (1 - Real.sqrt (ε * r)) ^ 2 := by nlinarith [hT, hrmain, hA0]
  have hθ2 : Real.sqrt (D / (2 * A)) ≤ Real.sqrt (ε * r) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * A)]
    nlinarith [hDr]
  exact le_trans hTm (swhPayoutArith hA hD hy1 hθ2)

/-! ## 1. The geometric power bound `((ℓ d))³·d^79 ≤ a³` -/

lemma swhGeomPow {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) (ht : μ * a ^ 3 ≤ 1) :
    (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d) ^ 3
      * ((Work.BoseBox.paramsAt μ a).d) ^ 79 ≤ a ^ 3 := by
  have ht0 : 0 < μ * a ^ 3 := by positivity
  have h1 : Work.BoseBox.sideAt μ a ^ 3 = a ^ 3 * Work.BoseBox.fsXp (μ * a ^ 3) (-489) :=
    Work.BoseFixB1.sideAt_cube_eq ha hμ
  have h2 : (Work.BoseBox.paramsAt μ a).d ^ 3 = Work.BoseBox.fsXp (μ * a ^ 3) 18 :=
    Work.BoseFixB1.d_cube_eq ha hμ
  have h3 : ((Work.BoseBox.paramsAt μ a).d) ^ 79 = Work.BoseBox.fsXp (μ * a ^ 3) 474 := by
    rw [Work.BoseFixB1.d_eq_fsXp, Work.BoseBox.fsXp_pow ht0.le 6 79]
    norm_num
  have h4 : Work.BoseBox.fsXp (μ * a ^ 3) (-489) * Work.BoseBox.fsXp (μ * a ^ 3) 18
      = Work.BoseBox.fsXp (μ * a ^ 3) (-471) := by
    rw [Work.BoseBox.fsXp_mul ht0 (-489) 18]; norm_num
  have h5 : Work.BoseBox.fsXp (μ * a ^ 3) (-471) * Work.BoseBox.fsXp (μ * a ^ 3) 474
      = Work.BoseBox.fsXp (μ * a ^ 3) 3 := by
    rw [Work.BoseBox.fsXp_mul ht0 (-471) 474]; norm_num
  have hgoal : (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d) ^ 3
      * ((Work.BoseBox.paramsAt μ a).d) ^ 79
      = a ^ 3 * Work.BoseBox.fsXp (μ * a ^ 3) 3 := by
    rw [mul_pow, h1, h2, h3]
    rw [show a ^ 3 * Work.BoseBox.fsXp (μ * a ^ 3) (-489)
        * Work.BoseBox.fsXp (μ * a ^ 3) 18 * Work.BoseBox.fsXp (μ * a ^ 3) 474
        = a ^ 3 * ((Work.BoseBox.fsXp (μ * a ^ 3) (-489)
            * Work.BoseBox.fsXp (μ * a ^ 3) 18)
          * Work.BoseBox.fsXp (μ * a ^ 3) 474) by ring]
    rw [h4, h5]
  rw [hgoal]
  have hle : Work.BoseBox.fsXp (μ * a ^ 3) 3 ≤ 1 := Work.BoseBox.fsXp_le_one ht0 ht (by norm_num)
  have hnn : 0 ≤ Work.BoseBox.fsXp (μ * a ^ 3) 3 := Work.BoseBox.fsXp_nonneg ht0.le
  nlinarith [hle, hnn, pow_pos ha 3]

/-! ## 1b. The count split -/

theorem swhCountSplit {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : E3} {n : ℕ}
    (Φ : X n → ℝ) (hΦc : Continuous Φ)
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      Φ x ≠ 0 → ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox ℓ d u) :
    Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
        (Submission.BoseGases.dlBox ℓ d u) Φ
      + Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
        (Submission.BoseGases.dlBox ℓ d u) Φ
      = (n : ℝ) * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hvolA : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal :=
    Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Set.inter_subset_left
  have hsplit : (∑ i : Fin n,
        ((∫ x in Submission.BoseGases.abox n ℓ,
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)
          + ∫ x in Submission.BoseGases.abox n ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2))
      = ∑ i : Fin n,
          ∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 :=
    Finset.sum_congr rfl (fun i _ =>
      Work.BoseFixB1S.boxPInd_sq_add_boxQInd_sq hℓ hA hvolA hAc i hΦc)
  have hterm : ∀ i : Fin n,
      (∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
        = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
    intro i
    refine integral_congr_ae ?_
    filter_upwards [hsupp] with x hx
    by_cases hmem : x i ∈ Submission.BoseGases.dlBox ℓ d u
    · rw [Set.indicator_of_mem hmem, one_mul]
    · have hΦ : Φ x = 0 := by
        by_contra hc
        exact hmem (hx hc i)
      rw [Set.indicator_of_notMem hmem]
      simp [hΦ]
  rw [Work.BoseFixB1S.boxFlatCount, Work.BoseFixB1S.boxQCount, ← Finset.sum_add_distrib, hsplit,
    Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-! ## 2. The payout at an arbitrary continuous state -/

theorem swhPayoutGenK {v : E3 → ℝ} {M : ℕ} {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) {u : E3} {n : ℕ}
    (Φ : X n → ℝ) (hΦc : Continuous Φ) (hv : 0 ≤ v)
    (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    (hM2 : 0 ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v))
    (hint : ∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.IntegrableOn
      (fun x : X n => Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))
      (Submission.BoseGases.abox n ℓ)) :
    (Real.sqrt (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
        * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ
        / (2 * (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2))
      - Real.sqrt ((∑ p ∈ Submission.BoseGases.pairSet n,
            ∫ x in Submission.BoseGases.abox n ℓ,
              (Φ x - Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1
                  (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2
                * Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) / 2)) ^ 2
      ≤ Work.BoseFixB1.pairSum v M ℓ d u Φ := by
  classical
  rw [Work.BoseFixB1.pairSum]
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set w : E3 → E3 → ℝ := Submission.BoseGases.wSmallPair M ℓ d u v with hwdef
  have hVpos : 0 < V := hV
  have hVeq : V = (MeasureTheory.volume A).toReal := by
    rw [hVdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hAmeas : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Set.inter_subset_left
  have hint' : ∀ p ∈ Submission.BoseGases.pairSet n,
      MeasureTheory.Integrable (fun x : X n => w (x p.1) (x p.2))
        ((MeasureTheory.volume : MeasureTheory.Measure (X n)).restrict
          (Submission.BoseGases.abox n ℓ)) := fun p hp => hint p hp
  let F : Fin n × Fin n → X n → ℝ := fun p x =>
    Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x
  let G : Fin n × Fin n → X n → ℝ := fun p x => Φ x - F p x
  let wt : Fin n × Fin n → X n → ℝ := fun p x => w (x p.1) (x p.2)
  have hwnn : ∀ p x, 0 ≤ wt p x := fun p x => by
    show 0 ≤ w (x p.1) (x p.2)
    rw [hwdef]
    exact Work.BoseFixB1.wSmallPair_nonneg_qLHS hv M ℓ d u (x p.1) (x p.2)
  have heqFG : ∀ p x, Φ x = F p x + G p x := by
    intro p x; dsimp only [G]; ring
  have hF : ∀ p ∈ Submission.BoseGases.pairSet n,
      MeasureTheory.Integrable (fun x : X n => F p x ^ 2 * wt p x)
        ((MeasureTheory.volume : MeasureTheory.Measure (X n)).restrict
          (Submission.BoseGases.abox n ℓ)) :=
    fun p hp => (Work.BoseFixB1S.pairProductsIntegrable hℓ hVpos hAmeas hVeq hAc hΦc hint' hp).1
  have hFG : ∀ p ∈ Submission.BoseGases.pairSet n,
      MeasureTheory.Integrable (fun x : X n => F p x * G p x * wt p x)
        ((MeasureTheory.volume : MeasureTheory.Measure (X n)).restrict
          (Submission.BoseGases.abox n ℓ)) :=
    fun p hp => (Work.BoseFixB1S.pairProductsIntegrable hℓ hVpos hAmeas hVeq hAc hΦc hint' hp).2.1
  have hG : ∀ p ∈ Submission.BoseGases.pairSet n,
      MeasureTheory.Integrable (fun x : X n => G p x ^ 2 * wt p x)
        ((MeasureTheory.volume : MeasureTheory.Measure (X n)).restrict
          (Submission.BoseGases.abox n ℓ)) :=
    fun p hp => (Work.BoseFixB1S.pairProductsIntegrable hℓ hVpos hAmeas hVeq hAc hΦc hint' hp).2.2.1
  have hΦi : ∀ p ∈ Submission.BoseGases.pairSet n,
      MeasureTheory.Integrable (fun x : X n => Φ x ^ 2 * wt p x)
        ((MeasureTheory.volume : MeasureTheory.Measure (X n)).restrict
          (Submission.BoseGases.abox n ℓ)) :=
    fun p hp => (Work.BoseFixB1S.pairProductsIntegrable hℓ hVpos hAmeas hVeq hAc hΦc hint' hp).2.2.2
  have hmass : (∑ p ∈ Submission.BoseGases.pairSet n,
      ∫ x in Submission.BoseGases.abox n ℓ,
        (Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x) ^ 2
          * w (x p.1) (x p.2))
      = 2 * (Work.BoseFixB1S.boxM2 V A w * Work.BoseFixB1S.boxPairCount V ℓ A Φ / (2 * V ^ 2)) := by
    have hmm := Work.BoseFixB1S.pairMassSumEq (N := n) (ℓ := ℓ) (V := V) hℓ hVpos hAmeas hVeq hAc w Φ
    rw [hmm]
    have hVne : V ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hVpos)
    field_simp
  exact Work.BoseFixB1S.pairingAssembly (Submission.BoseGases.pairSet n) (F := F) (G := G) (wt := wt)
    (Φ := Φ)
    (A2 := Work.BoseFixB1S.boxM2 V A w * Work.BoseFixB1S.boxPairCount V ℓ A Φ / (2 * V ^ 2))
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (X n)).restrict
      (Submission.BoseGases.abox n ℓ))
    hwnn heqFG hF hFG hG hΦi hmass

/-- The payout at a scattering-solution numerator (the historical form of `swhPayoutGenK`). -/
theorem swhPayoutGen {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) {M : ℕ} {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) {u : E3} {n : ℕ}
    (Φ : X n → ℝ) (hΦc : Continuous Φ)
    (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    (hM2 : 0 ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v))
    (hint : ∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.IntegrableOn
      (fun x : X n => Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))
      (Submission.BoseGases.abox n ℓ)) :
    (Real.sqrt (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
        * Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ
        / (2 * (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2))
      - Real.sqrt ((∑ p ∈ Submission.BoseGases.pairSet n,
            ∫ x in Submission.BoseGases.abox n ℓ,
              (Φ x - Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1
                  (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2
                * Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) / 2)) ^ 2
      ≤ Work.BoseFixB1.pairSum v M ℓ d u Φ :=
  swhPayoutGenK hℓ hd Φ hΦc hv hV hM2 hint

/-! ## 3. The final payout algebra -/

/-- **The final payout algebra**: if `κ ≤ ϱ·A`, `D/(2A) ≤ Γ` and `√ϱ + √Γ ≤ 1` then
`κ ≤ (√A − √(D/2))²`. -/
theorem swhPayoutFinal {A D κ ϱ Γ : ℝ} (hA : 0 < A) (hD : 0 ≤ D) (hϱ0 : 0 ≤ ϱ) (hΓ0 : 0 ≤ Γ)
    (hκ : κ ≤ ϱ * A) (hDΓ : D / (2 * A) ≤ Γ) (hsum : Real.sqrt ϱ + Real.sqrt Γ ≤ 1) :
    κ ≤ (Real.sqrt A - Real.sqrt (D / 2)) ^ 2 := by
  have hA0 : 0 ≤ A := hA.le
  have hsϱ0 : 0 ≤ Real.sqrt ϱ := Real.sqrt_nonneg ϱ
  have hsΓ0 : 0 ≤ Real.sqrt Γ := Real.sqrt_nonneg Γ
  have hsΓ1 : Real.sqrt Γ ≤ 1 := by linarith
  have hq0 : 0 ≤ D / (2 * A) := div_nonneg hD (by linarith)
  have hqΓ : Real.sqrt (D / (2 * A)) ≤ Real.sqrt Γ := Real.sqrt_le_sqrt hDΓ
  have hq1 : Real.sqrt (D / (2 * A)) ≤ 1 := le_trans hqΓ hsΓ1
  have hqnn : 0 ≤ Real.sqrt (D / (2 * A)) := Real.sqrt_nonneg _
  have hkey : ϱ ≤ (1 - Real.sqrt (D / (2 * A))) ^ 2 := by
    have h1 : (1 - Real.sqrt Γ) ^ 2 ≤ (1 - Real.sqrt (D / (2 * A))) ^ 2 := by
      nlinarith [hqΓ, hq1, hsΓ1, hqnn]
    have h2 : ϱ ≤ (1 - Real.sqrt Γ) ^ 2 := by
      have h3 : Real.sqrt ϱ ≤ 1 - Real.sqrt Γ := by linarith
      nlinarith [h3, hsϱ0, hsΓ0, Real.sq_sqrt hϱ0]
    linarith
  have hsq : (Real.sqrt A - Real.sqrt (D / 2)) ^ 2
      = A * (1 - Real.sqrt (D / (2 * A))) ^ 2 := by
    have hid : Real.sqrt (D / 2) = Real.sqrt A * Real.sqrt (D / (2 * A)) := by
      rw [← Real.sqrt_mul hA0 (D / (2 * A)), show A * (D / (2 * A)) = D / 2 by field_simp]
    rw [hid, show Real.sqrt A - Real.sqrt A * Real.sqrt (D / (2 * A))
        = Real.sqrt A * (1 - Real.sqrt (D / (2 * A))) by ring]
    rw [mul_pow, Real.sq_sqrt hA0]
  calc κ ≤ ϱ * A := hκ
    _ = A * ϱ := by ring
    _ ≤ A * (1 - Real.sqrt (D / (2 * A))) ^ 2 := mul_le_mul_of_nonneg_left hkey hA0
    _ = (Real.sqrt A - Real.sqrt (D / 2)) ^ 2 := hsq.symm

/-- **The node N3** (`Work.BoseB1Cube.swhThinNode`): the thin, non-degenerate boxes of the
small-window box split.  Holder statement — the proof is the assembly described in the module
docstring. -/
theorem swhThinNodeProved {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseB1Cube.swhThinNode v h := by
  classical
  intro Cn hCn η hη
  have hsclpos : 0 < Work.SmallBoxSliding.smallConvLower 48 :=
    Work.SmallBoxSliding.smallConvLower_pos 48
  obtain ⟨Cm, hCm0, εmf, hεmf, hman⟩ :=
    Work.BoseB1Cube.swhManifestInst (v := v) h hv hv1 hvrad hR hv_supp hav η hη
  obtain ⟨K, hK0, hKtail, hKall⟩ :=
    Work.BoseB1Cube.swhTruncFactsFixed (v := v) h hv hv1 hvrad hR hv_supp hav
      (η * Work.SmallBoxSliding.smallConvLower 48 / 8)
      (div_pos (mul_pos hη hsclpos) (by norm_num))
  set εη : ℝ := 57 * (1 + Cm * _root_.BoseGases.a v) with hεηdef
  have hεηpos : 0 < εη := by rw [hεηdef]; positivity
  have hk1 : 19 / 18 + Cm * _root_.BoseGases.a v / (4 * εη) ≤ 1.06 := by
    have hCma : 0 ≤ Cm * _root_.BoseGases.a v := mul_nonneg hCm0 hav.le
    have h1 : Cm * _root_.BoseGases.a v
        / (4 * (57 * (1 + Cm * _root_.BoseGases.a v))) ≤ 1 / 225 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * (57 * (1 + Cm * _root_.BoseGases.a v)))]
      nlinarith [hCma]
    rw [hεηdef]
    linarith
  set Kg : ℝ := max (12000 * Cn * (5 + K * (_root_.BoseGases.a v) ^ 2
        / Work.SmallBoxSliding.smallConvLower 48))
      (max (Cm * (εη + 1)) 1) with hKgdef
  have hKgpos : 0 < Kg := by
    rw [hKgdef]
    exact lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_right _ _))
  have hKgnn : 0 ≤ Kg := hKgpos.le
  have hKgbig0 : 12000 * Cn * (5 + K * (_root_.BoseGases.a v) ^ 2
      / Work.SmallBoxSliding.smallConvLower 48) ≤ Kg := by
    rw [hKgdef]; exact le_max_left _ _
  have hKgCm : Cm * (εη + 1) ≤ Kg := by
    rw [hKgdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hKgbig : 12000 * Cn * (1 + K * (_root_.BoseGases.a v) ^ 2
      / Work.SmallBoxSliding.smallConvLower 48) ≤ Kg := by
    refine le_trans ?_ hKgbig0
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (by linarith))
    have hx : 0 ≤ K * (_root_.BoseGases.a v) ^ 2 / Work.SmallBoxSliding.smallConvLower 48 :=
      div_nonneg (mul_nonneg hK0 (sq_nonneg _)) hsclpos.le
    linarith
  have hKg60000 : 60000 * Cn ≤ Kg := by
    refine le_trans ?_ hKgbig0
    have hx : 0 ≤ K * (_root_.BoseGases.a v) ^ 2 / Work.SmallBoxSliding.smallConvLower 48 :=
      div_nonneg (mul_nonneg hK0 (sq_nonneg _)) hsclpos.le
    have h1 : (60000 : ℝ) * Cn = 12000 * Cn * 5 := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by norm_num) (by linarith))
  have hKg17 : 17 * Real.pi / 18 ≤ Kg := by
    have h1 : (17 * Real.pi / 18 : ℝ) ≤ 60000 * Cn := by
      nlinarith [Real.pi_lt_four, hCn]
    linarith [h1, hKg60000]
  obtain ⟨εg, hεg, hgate4⟩ :=
    Work.BoseB1Cube.bGapCoeff_gate (v := v) hav (4 * Kg) (by positivity)
  obtain ⟨εbk, hεbk, hbk⟩ := Work.BoseB1Cube.swhSlidingBookkeeping (v := v) h hav hR hv_supp
  obtain ⟨εsh, hεsh, hsh⟩ := Work.BoseB1Cube.w1MassB_le_sharp (v := v) h hv hv1 hvrad hR hv_supp
    hav (δ := 1 / 16) (by norm_num)
  refine ⟨1, min (min (min εg εbk) (min εsh εmf)) 1, one_pos,
    lt_min (lt_min (lt_min hεg hεbk) (lt_min hεsh hεmf)) one_pos, ?_⟩
  intro μ hAdm n Ψ u hu hμW hΨc hsupp hnorm hn1 hn2 hQc hpd hthin hηχ
  have hAdmg : Work.BoseBoxFix.Adm v εg μ := Work.BoseFixB1.Adm.mono hAdm
    (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _))
  have hAdmbk : Work.BoseBoxFix.Adm v εbk μ := Work.BoseFixB1.Adm.mono hAdm
    (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _))
  have hAdmsh : Work.BoseBoxFix.Adm v εsh μ := Work.BoseFixB1.Adm.mono hAdm
    (le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (min_le_left _ _))
  have hAdmmf : Work.BoseBoxFix.Adm v εmf μ := Work.BoseFixB1.Adm.mono hAdm
    (le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (min_le_right _ _))
  have hAdm1 : Work.BoseBoxFix.Adm v 1 μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  -- ## elementary bookkeeping
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  obtain ⟨hVpos, hV1, hμV, hVcube, hd1, hM48, hR16, hRχ⟩ := hbk μ hAdmbk u hu
  have hM1 : 1 ≤ Work.BoseFixB1.bM v μ := by rw [hM48]; norm_num
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := Work.BoseFixB1.adm_dilute_le_one hAdm1 le_rfl
  have hav0 : 0 ≤ _root_.BoseGases.a v := hav.le
  have hΨcont : Continuous Ψ := hΨc.continuous
  have hSQ : Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ
      + Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u) Ψ = (n : ℝ) := by
    have hh := Work.BoseFixB1S.b1sCountSplit (N := n) (ℓ := Work.BoseFixB1.bSide v μ)
      (volA := Work.BoseFixB1.bV v μ u)
      (A := Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
      hℓ hVpos
      (Work.SmallBoxSliding.measurableSet_dlBox (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u)
      (by simp only [Work.BoseFixB1.bV, Work.SmallBoxSliding.boxMass_eq_measureReal,
          MeasureTheory.Measure.real_def])
      (Work.SmallBoxSliding.dlBox_subset_acube (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u)
      hΨcont hsupp
    rw [hnorm, mul_one] at hh
    exact hh
  have hSnn : 0 ≤ Work.BoseFixB1.bFlat v μ Ψ u := by
    simp only [Work.BoseFixB1.bFlat, Work.BoseFixB1S.boxFlatCount]
    exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hQnn : 0 ≤ Work.BoseFixB1.bQ v μ Ψ u := by
    simp only [Work.BoseFixB1.bQ, Work.BoseFixB1S.boxQCount]
    exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hμVpos : 0 < μ * Work.BoseFixB1.bV v μ u := lt_of_lt_of_le zero_lt_one hμV
  have hWnn : 0 ≤ Work.BoseFixB1.bW v h μ u :=
    Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hpairnn : 0 ≤ Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u Ψ :=
    Work.BoseFixB1.pairSum_nonneg hv u Ψ
  -- ## the geometric inputs
  have hDd0 : 0 ≤ (Work.BoseFixB1.bD v μ) ^ 79 := by positivity
  have hχm_le : Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u ≤ (Work.BoseFixB1.bD v μ) ^ 79 * Work.BoseFixB1.bV v μ u :=
    Work.BoseB1Cube.swhChiMassSqLe hM1 hℓ hd hDd0 u hthin
  have hWsh : Work.BoseFixB1.bW v h μ u ≤ (1 + 1 / 16) * (8 * Real.pi * _root_.BoseGases.a v)
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u := hsh μ hAdmsh u
  have hgeom := Work.BoseB1Cube.swhGeomPow (μ := μ) (a := _root_.BoseGases.a v) hμ hav ht1
  have hgeom' : (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3
      * (Work.BoseFixB1.bD v μ) ^ 79 ≤ (_root_.BoseGases.a v) ^ 3 := hgeom
  have hDdV : (Work.BoseFixB1.bD v μ) ^ 79 * Work.BoseFixB1.bV v μ u
      ≤ (_root_.BoseGases.a v) ^ 3 := by
    have h1 : (Work.BoseFixB1.bD v μ) ^ 79 * Work.BoseFixB1.bV v μ u
        ≤ (Work.BoseFixB1.bD v μ) ^ 79
          * (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3 :=
      mul_le_mul_of_nonneg_left hVcube hDd0
    nlinarith only [h1, hgeom']
  have ha3V : (_root_.BoseGases.a v) ^ 3 ≤ Work.BoseFixB1.bV v μ u := by
    have h1 : (_root_.BoseGases.a v) ^ 3
        ≤ (_root_.BoseGases.a v) ^ 3 * (μ * Work.BoseFixB1.bV v μ u) := by
      nlinarith only [hμV, hav, pow_pos hav 3]
    have h2 : (_root_.BoseGases.a v) ^ 3 * (μ * Work.BoseFixB1.bV v μ u)
        = (μ * (_root_.BoseGases.a v) ^ 3) * Work.BoseFixB1.bV v μ u := by ring
    have h3 : (μ * (_root_.BoseGases.a v) ^ 3) * Work.BoseFixB1.bV v μ u
        ≤ 1 * Work.BoseFixB1.bV v μ u := mul_le_mul_of_nonneg_right ht1 hVpos.le
    nlinarith only [h1, h2, h3]
  have hDd1 : (Work.BoseFixB1.bD v μ) ^ 79 ≤ 1 := pow_le_one₀ hd.le hd1
  have hχmnn : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hWupD : Work.BoseFixB1.bW v h μ u ≤ 17 * Real.pi * _root_.BoseGases.a v
      * ((Work.BoseFixB1.bD v μ) ^ 79 * Work.BoseFixB1.bV v μ u) := by
    have hDdVV : 0 ≤ (Work.BoseFixB1.bD v μ) ^ 79 * Work.BoseFixB1.bV v μ u :=
      mul_nonneg hDd0 hVpos.le
    have h2 := mul_le_mul_of_nonneg_left hχm_le (by positivity :
      (0:ℝ) ≤ (1 + 1 / 16) * (8 * Real.pi * _root_.BoseGases.a v))
    have h3 : (1 + 1 / 16) * (8 * Real.pi * _root_.BoseGases.a v)
          * ((Work.BoseFixB1.bD v μ) ^ 79 * Work.BoseFixB1.bV v μ u)
        ≤ 17 * Real.pi * _root_.BoseGases.a v
          * ((Work.BoseFixB1.bD v μ) ^ 79 * Work.BoseFixB1.bV v μ u) := by
      apply mul_le_mul_of_nonneg_right _ hDdVV
      nlinarith only [Real.pi_pos, hav0]
    exact le_trans hWsh (le_trans h2 h3)
  have hWup : Work.BoseFixB1.bW v h μ u
      ≤ 17 * Real.pi * _root_.BoseGases.a v * Work.BoseFixB1.bV v μ u := by
    have hDdV' : (Work.BoseFixB1.bD v μ) ^ 79 * Work.BoseFixB1.bV v μ u
        ≤ Work.BoseFixB1.bV v μ u := by
      nlinarith only [hDd1, hVpos]
    have h2 := mul_le_mul_of_nonneg_left hDdV'
      (show (0:ℝ) ≤ 17 * Real.pi * _root_.BoseGases.a v by
        exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hav0)
    exact le_trans hWupD h2
  have hWupQ : Work.BoseFixB1.bW v h μ u ≤ 17 * Real.pi * _root_.BoseGases.a v
      * (Work.BoseFixB1.bD v μ) ^ 79 * Work.BoseFixB1.bV v μ u := by
    have hh := hWupD
    linarith only [hh]
  -- ## the truncation
  obtain ⟨hKpt, hKloss⟩ := hKall hM1 hℓ hd hR16 hRχ u
  set Kwv : ℝ := 2 * K * (Work.SmallBoxSliding.smallConvLower 48)⁻¹
      * (Work.BoseFixB1.bD v μ) ^ 79 with hKwvdef
  have hKw0 : 0 ≤ Kwv := by rw [hKwvdef]; positivity
  have hKwvV : Kwv * Work.BoseFixB1.bV v μ u
      ≤ 2 * K * (_root_.BoseGases.a v) ^ 3 / Work.SmallBoxSliding.smallConvLower 48 := by
    have hmain : Kwv * Work.BoseFixB1.bV v μ u * Work.SmallBoxSliding.smallConvLower 48
        ≤ 2 * K * (_root_.BoseGases.a v) ^ 3 := by
      rw [hKwvdef]
      have h1 : 2 * K * (Work.SmallBoxSliding.smallConvLower 48)⁻¹
            * (Work.BoseFixB1.bD v μ) ^ 79 * Work.BoseFixB1.bV v μ u
            * Work.SmallBoxSliding.smallConvLower 48
          = 2 * K * ((Work.BoseFixB1.bD v μ) ^ 79 * Work.BoseFixB1.bV v μ u) := by
        field_simp
      rw [h1]
      exact mul_le_mul_of_nonneg_left hDdV (by positivity)
    rw [le_div_iff₀ hsclpos]
    linarith [hmain]
  have hscl_eq : Work.SmallBoxSliding.smallConvLower (Work.BoseFixB1.bM v μ)
      = Work.SmallBoxSliding.smallConvLower 48 := by rw [hM48]
  have hminnn : 0 ≤ fun z : E3 => min (v z) K := fun z => le_min (hv z) hK0
  -- the pointwise kernel bound at the truncation
  have hw : ∀ x y : E3, |Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u (fun z => min (v z) K) x y| ≤ Kwv := by
    intro x y
    have h1 := hKpt x y
    rw [hscl_eq] at h1
    have hχx : Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u x
        ≤ Real.sqrt ((Work.BoseFixB1.bD v μ) ^ 79) := by
      rw [← Real.sqrt_sq (Submission.BoseGases.chiSmallB_nonneg _ _ _ _ _)]
      exact Real.sqrt_le_sqrt (hthin x)
    have hχy : Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u y
        ≤ Real.sqrt ((Work.BoseFixB1.bD v μ) ^ 79) := by
      rw [← Real.sqrt_sq (Submission.BoseGases.chiSmallB_nonneg _ _ _ _ _)]
      exact Real.sqrt_le_sqrt (hthin y)
    have h2 : Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u x * Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ)
        (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u y ≤ (Work.BoseFixB1.bD v μ) ^ 79 := by
      have hprod := mul_le_mul hχx hχy
        (Submission.BoseGases.chiSmallB_nonneg _ _ _ _ _) (Real.sqrt_nonneg _)
      rwa [Real.mul_self_sqrt hDd0] at hprod
    have h3 : 2 * K * (Work.SmallBoxSliding.smallConvLower 48)⁻¹
        * (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u x
          * Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u y)
        ≤ Kwv := by
      rw [hKwvdef]
      have hc : 0 ≤ 2 * K * (Work.SmallBoxSliding.smallConvLower 48)⁻¹ := by positivity
      nlinarith [h2, hc, hDd0]
    linarith [h1, h3]
  have hint : ∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.IntegrableOn
      (fun x : X n => Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ)
        (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u (fun z => min (v z) K)
          (x p.1) (x p.2))
      (Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ)) :=
    Work.BoseB1Cube.wSmallPair_integrableOn_pairs (v := fun z : E3 => min (v z) K)
      (Work.BoseB1Cube.memLp_one_min hv hK0 hv1 hv_supp) hR
      (Work.BoseB1Cube.tsupport_min_subset hv hK0 hv_supp) hM1 hℓ hd hR16 hRχ
  -- ## the payout ingredients
  have hAmeas : MeasurableSet (Work.BoseFixB1.bA v μ u) :=
    Work.SmallBoxSliding.measurableSet_dlBox (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
  have hAac : Work.BoseFixB1.bA v μ u ⊆ Submission.BoseGases.acube (Work.BoseFixB1.bSide v μ) :=
    Work.SmallBoxSliding.dlBox_subset_acube (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
  have hvolA : Work.BoseFixB1.bV v μ u
      = (MeasureTheory.volume (Work.BoseFixB1.bA v μ u)).toReal := by
    simp only [Work.BoseFixB1.bV, Work.BoseFixB1.bA, Work.SmallBoxSliding.boxMass_eq_measureReal,
      MeasureTheory.Measure.real_def]
  have hM2nn : 0 ≤ Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
      (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u (fun z => min (v z) K)) := by
    simp only [Work.BoseFixB1S.boxM2]
    refine MeasureTheory.setIntegral_nonneg (hAmeas.prod hAmeas) ?_
    intro p _
    exact Work.BoseFixB1.wSmallPair_nonneg_qLHS hminnn _ _ _ _ p.1 p.2
  have hPc0 : 0 ≤ Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) Ψ := by
    simp only [Work.BoseFixB1S.boxPairCount]
    exact Finset.sum_nonneg (fun p _ => integral_nonneg (fun x => sq_nonneg _))
  have hPc_ge : Work.BoseFixB1.bFlat v μ Ψ u ^ 2 - Work.BoseFixB1.bFlat v μ Ψ u
      ≤ Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Ψ :=
    Work.BoseFixB1S.Q0C.count_ge hℓ hVpos (A := Work.BoseFixB1.bA v μ u) hAmeas hvolA hAac
      hΨcont hnorm
  have hpay := Work.BoseB1Cube.swhPayoutGenK (v := fun z : E3 => min (v z) K)
    hℓ hd Ψ hΨcont hminnn hVpos hM2nn hint
  have hDle : Work.BoseB1Cube.cubeDenseDev (fun z : E3 => min (v z) K) (Work.BoseFixB1.bM v μ)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u n Ψ
      ≤ 4 * Kwv * ((n : ℝ) - 1) * Work.BoseFixB1.bQ v μ Ψ u :=
    Work.BoseB1Cube.cubeDenseDev_le_pairQCount hℓ hVpos hKw0 hw hΨcont hint
  have hD0 : 0 ≤ Work.BoseB1Cube.cubeDenseDev (fun z : E3 => min (v z) K) (Work.BoseFixB1.bM v μ)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u n Ψ := by
    rw [Work.BoseB1Cube.cubeDenseDev]
    refine Finset.sum_nonneg (fun p _ => integral_nonneg (fun x => ?_))
    exact mul_nonneg (sq_nonneg _)
      (Work.BoseFixB1.wSmallPair_nonneg_qLHS hminnn _ _ _ _ (x p.1) (x p.2))
  have hg0eq : Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
        (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g0 v h))
      = Work.BoseFixB1.bW v h μ u :=
    (Work.BoseB1Cube.w1MassB_eq_boxM2 (h := h) (hR := hR) (hv_supp := hv_supp)
      (M := Work.BoseFixB1.bM v μ) (ℓ := Work.BoseFixB1.bSide v μ)
      (d := Work.BoseFixB1.bD v μ) hM1 hℓ hd hR16 hRχ u).symm
  -- the truncation loss
  have hloss : Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
        (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g0 v h))
      - Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
        (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u (fun z => min (v z) K))
      ≤ (1 / 4) * Work.BoseFixB1.bW v h μ u := by
    have hKloss' : Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g0 v h))
        - Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u (fun z => min (v z) K))
        ≤ 2 * (Work.SmallBoxSliding.smallConvLower 48)⁻¹
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
            * (∫ z : E3, max (Submission.BoseGases.g0 v h z - K) 0) := by
      simpa only [Work.BoseFixB1.bV, Work.BoseFixB1.bA, hscl_eq] using hKloss
    have hkey : 2 * (Work.SmallBoxSliding.smallConvLower 48)⁻¹
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u
        * (∫ z : E3, max (Submission.BoseGases.g0 v h z - K) 0) ≤ (1 / 4) * Work.BoseFixB1.bW v h μ u := by
      have h1 : (∫ z : E3, max (Submission.BoseGases.g0 v h z - K) 0)
          ≤ (η * Work.SmallBoxSliding.smallConvLower 48 / 8) * _root_.BoseGases.a v := hKtail
      have h3 : 0 ≤ 2 * (Work.SmallBoxSliding.smallConvLower 48)⁻¹
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u :=
        mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hsclpos.le)) hχmnn
      have h4 := mul_le_mul_of_nonneg_left h1 h3
      have h5 : 2 * (Work.SmallBoxSliding.smallConvLower 48)⁻¹
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u
          * ((η * Work.SmallBoxSliding.smallConvLower 48 / 8) * _root_.BoseGases.a v)
          = (η * _root_.BoseGases.a v
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u) / 4 := by
        field_simp
        ring
      have h6 : (η * _root_.BoseGases.a v
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u) / 4 ≤ (1 / 4) * Work.BoseFixB1.bW v h μ u := by
        linarith only [hηχ]
      linarith only [h4, h5, h6]
    linarith only [hKloss', hkey]
  have hM2K_low : (3 / 4) * Work.BoseFixB1.bW v h μ u
      ≤ Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
        (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u (fun z => min (v z) K)) := by
    linarith [hg0eq, hloss]
  -- ## the payout branch bound on `Q`
  have hgate : 4 * Kg * μ * _root_.BoseGases.a v ≤ Work.BoseFixB1.bGapCoeff v μ := by
    have hh := hgate4 μ hAdmg
    linarith [hh]
  have hfib : Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u Ψ
      ≤ (Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u) * Work.BoseFixB1.bFlat v μ Ψ u
        + Cm * _root_.BoseGases.a v
          * (Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
                * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
                  * Work.BoseFixB1.bFlat v μ Ψ u))
            + Work.BoseFixB1.bQ v μ Ψ u) := by
    have hh := hman μ hAdmmf u hu Ψ hΨc hsupp hnorm
    have hh' : μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u Ψ
        ≤ μ * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
              * Work.BoseFixB1.bFlat v μ Ψ u
            + Cm * _root_.BoseGases.a v
              * (Real.sqrt (Work.BoseFixB1.bQ v μ Ψ u
                    * ((Work.BoseFixB1.bW v h μ u / Work.BoseFixB1.bV v μ u)
                      * Work.BoseFixB1.bFlat v μ Ψ u))
                + Work.BoseFixB1.bQ v μ Ψ u)) := by
      simpa only [mul_assoc] using hh
    exact le_of_mul_le_mul_left hh' hμ
  -- ## the assembly
  have hTle : Work.BoseB1Cube.swhDem v h μ n u
        + μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u Ψ
      ≤ Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u
        + Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u Ψ := by
    by_cases hbr : Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u
        < Work.BoseB1Cube.swhDem v h μ n u
          + μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u Ψ
    · have hred := Work.BoseB1Cube.swhManifestReduced (μ := μ) (a := _root_.BoseGases.a v)
        (V := Work.BoseFixB1.bV v μ u) (W := Work.BoseFixB1.bW v h μ u)
        (S := Work.BoseFixB1.bFlat v μ Ψ u) (Q := Work.BoseFixB1.bQ v μ Ψ u) (n := (n : ℝ))
        (Cm := Cm) (εη := εη) (Kg := Kg) (bG := Work.BoseFixB1.bGapCoeff v μ)
        (fib := Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u Ψ)
        (T := Work.BoseB1Cube.swhDem v h μ n u
          + μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u Ψ)
        hμ hav0 hVpos hWnn hSnn hQnn hCm0 hεηpos hKgpos hgate hKgCm hKg17 hWup hSQ hfib rfl
      have hQsm := hred.2 hbr
      have hqb := Work.BoseB1Cube.swhQBound (μ := μ) (av := _root_.BoseGases.a v)
        (V := Work.BoseFixB1.bV v μ u) (W := Work.BoseFixB1.bW v h μ u)
        (S := Work.BoseFixB1.bFlat v μ Ψ u) (Q := Work.BoseFixB1.bQ v μ Ψ u) (n := (n : ℝ))
        (Cn := Cn) (Kg := Kg) (k := 19 / 18 + Cm * _root_.BoseGases.a v / (4 * εη))
        (d79 := (Work.BoseFixB1.bD v μ) ^ 79)
        hμ hav hVpos hWnn hSnn hQnn hCn hKgpos (by positivity) hk1 hDd0 hDd1 hSQ hn1 hn2 hμV
        hQsm hWupQ hKg60000
      have hS1 := hqb.2
      have hWpos : 0 < Work.BoseFixB1.bW v h μ u := by
        rcases eq_or_lt_of_le hWnn with h0 | h0
        · exfalso
          have hz : (19 / 18 + Cm * _root_.BoseGases.a v / (4 * εη))
              * (μ * Work.BoseFixB1.bW v h μ u * Work.BoseFixB1.bFlat v μ Ψ u
                / Work.BoseFixB1.bV v μ u) = 0 := by
            rw [← h0]
            simp
          linarith only [hred.1, hbr, hz]
        · exact h0
      have hSpos : 0 < Work.BoseFixB1.bFlat v μ Ψ u := by
        have h2 : 0 < 2.99 * μ * Work.BoseFixB1.bV v μ u := by positivity
        linarith [hS1, h2]
      have hsqrt := Work.BoseB1Cube.swhCruxSqrtSum (μ := μ) (a := _root_.BoseGases.a v)
        (V := Work.BoseFixB1.bV v μ u) (W := Work.BoseFixB1.bW v h μ u)
        (S := Work.BoseFixB1.bFlat v μ Ψ u) (Q := Work.BoseFixB1.bQ v μ Ψ u) (n := (n : ℝ))
        (Cn := Cn) (K := K) (scl := Work.SmallBoxSliding.smallConvLower 48) (Kw := Kwv)
        (k := 19 / 18 + Cm * _root_.BoseGases.a v / (4 * εη)) (Kg := Kg)
        hμ hav hVpos hWpos hSpos hQnn hCn hK0 hsclpos hKw0 hKgpos
        (by positivity) hk1 hn2 hS1 hQsm hKwvV hKgbig
      have hbook := Work.BoseB1Cube.swhPayoutBook (V := Work.BoseFixB1.bV v μ u)
        (W := Work.BoseFixB1.bW v h μ u) (S := Work.BoseFixB1.bFlat v μ Ψ u)
        (Q := Work.BoseFixB1.bQ v μ Ψ u) (n := (n : ℝ)) (Kw := Kwv)
        (D := Work.BoseB1Cube.cubeDenseDev (fun z : E3 => min (v z) K) (Work.BoseFixB1.bM v μ)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u n Ψ)
        (M2K := Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u (fun z => min (v z) K)))
        (Pc := Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u) Ψ)
        (k := 19 / 18 + Cm * _root_.BoseGases.a v / (4 * εη)) (μ := μ)
        hVpos hWpos (by linarith only [hS1, hμVpos]) hQnn (by positivity) hKw0 (by positivity) hμ
        hM2K_low hPc_ge hD0 hDle hsqrt
      have hstep : (19 / 18 + Cm * _root_.BoseGases.a v / (4 * εη)) * μ
            * Work.BoseFixB1.bW v h μ u * Work.BoseFixB1.bFlat v μ Ψ u
            / Work.BoseFixB1.bV v μ u
          ≤ Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u Ψ :=
        le_trans hbook (le_trans hpay (Work.BoseB1Cube.pairSum_min_le (h := h) hv hv1 hR hv_supp
          hK0 hM1 hℓ hd hR16 hRχ u Ψ hΨcont))
      have hkey2 : Work.BoseB1Cube.swhDem v h μ n u
            + μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u Ψ
          - Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u
          ≤ Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u Ψ := by
        have hb : (19 / 18 + Cm * _root_.BoseGases.a v / (4 * εη)) * μ
              * Work.BoseFixB1.bW v h μ u * Work.BoseFixB1.bFlat v μ Ψ u
              / Work.BoseFixB1.bV v μ u
            = (19 / 18 + Cm * _root_.BoseGases.a v / (4 * εη))
              * (μ * Work.BoseFixB1.bW v h μ u * Work.BoseFixB1.bFlat v μ Ψ u
                / Work.BoseFixB1.bV v μ u) := by
          ring_nf
        have hstep' := hstep
        rw [hb] at hstep'
        linarith only [hred.1, hstep']
      linarith only [hkey2]
    · push_neg at hbr
      linarith [hbr, hpairnn]
  -- ## the word identity
  have hword := Work.BoseFixB1C.sbWordCube_eq_add (v := v) (h := h) (μ := μ) u Ψ
  have hkin : Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u
      ≤ Work.BoseFixB1B.sbKinCube v μ u Ψ := by
    have hsp : 0 ≤ Work.BoseFixB1B.cubeSpectral v μ Ψ u := by
      rw [Work.BoseFixB1B.cubeSpectral]
      exact Work.BoseFixB1.tBwordKinInd_nonneg Ψ
    rw [Work.BoseFixB1B.sbKinCube]
    have hq : Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
        (Work.BoseFixB1.bV v μ u) Ψ = Work.BoseFixB1.bQ v μ Ψ u := rfl
    rw [hq]
    linarith only [hsp]
  have hpot := Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1
    hAdm hΨcont u hR16 hRχ
  have hAsm : Work.BoseB1Cube.swhDem v h μ n u
      ≤ Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u
        + Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u Ψ
        - μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u Ψ := by
    linarith only [hTle]
  have hBsm : Work.BoseFixB1.bGapCoeff v μ * Work.BoseFixB1.bQ v μ Ψ u
        + Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u Ψ
        - μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u Ψ
      ≤ Work.BoseFixB1B.sbKinCube v μ u Ψ
        + (-(μ * Work.BoseFixB1.fibSum h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u Ψ)
          + Work.BoseFixB1.pairSum v (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u Ψ) := by
    linarith only [hkin]
  show Work.BoseB1Cube.swhDem v h μ n u ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ
  rw [hword, hpot]
  exact le_trans hAsm hBsm

end Work.BoseB1Cube
