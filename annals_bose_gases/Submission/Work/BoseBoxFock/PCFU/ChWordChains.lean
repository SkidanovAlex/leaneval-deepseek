import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.PCFU.Achan_dzero_word_split_v2
import Submission.Work.BoseBoxFock.PCFU.Bchan_dzero_word_split_v3
import Submission.Work.BoseBoxFock.PCFU.Cchan_dzero_word_split_v4
import Submission.Work.BoseBoxFock.PCFU.Dchan_dzero_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.PCFU.ChWordChains` — the four channel chains of the cubic dictionary

The four `MiddleU` channels (`ChAU …ChDU`), in the **canonical** form of
`chanA_canonical`/`chanBCD_canonical`, are evaluated in two steps by the eight PROVED bridges

* `Xchan_eq_imageSum` — the channel at the image sum of the low cut-off kernel,
* `Xchan_dzero_split` — the `d = 0` extraction (producing the word's `Γ_j = lowSlot`), and
* `Xchan_dzero_word_split*` — the pass to the word's `w₁`-weighted integral,

and the composite identity is, with `ℓ = ellH v μ`,

    (A)  chAint = ℓ⁹·chAword + ℓ⁶·(chAslot + chAimg)
    (B)  chBint = ℓ⁹·chBword + ℓ⁶·(chBslot + chBimg)
    (C)  chCint = ℓ⁹·chCword + ℓ³·(chCslot + chCimg)
    (D)  chDint = ℓ⁹·chDword + ℓ³·(chDslot + chDimg)

The word terms carry the four columns `(1, −P_i, −P_j, +Π)` of `Q_jQ_i = 1 − P_i − P_j + Π`
(`chAword` … `chDword` are the two-slot pairings against `Θ, P_iΘ, P_jΘ, P_iP_jΘ`), the `ℓ⁹` being
what remains of `ℓ^6·ℓ^3` (or `ℓ³·ℓ⁶` for the `(C)`,`(D)` pair).  The slots are the two error
genera of the dictionary: the **alias** slot (`KfrU − ℓ³W1fun` / `KχfrU − ∫χW1fun`, `chAslot`/
`chBslot`, and their image-augmented twins `chCslot`/`chDslot`) and the **lattice-image** slot
(`chAimg` … `chDimg`, the `d ≠ 0` images of the low cut-off kernel).  The `(C)`,`(D)` slots carry
`ℓ³` (not `ℓ⁶`) because their inner `∫_z χ(z)` already supplies one `ℓ³`.

The file also carries `slotAvg_neg_Kchi`, the `KχfrU`-twin of `PCFU.slotAvg_neg`, which is the
`w ↦ −w` substitution the `(D)`-chain needs.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

set_option linter.unusedVariables false
local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Work.BoseB4 Work.BoseBoxFock

set_option maxHeartbeats 3000000
set_option linter.unusedVariables false

/-- The low-momentum cut-off `κ = (d²·ℓ)⁻¹`. -/
noncomputable def chKappa (v : E3 → ℝ) (μ : ℝ) : ℝ :=
  ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
    * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹

/-- The `(A)`-channel integral of `MiddleU`. -/
def chAint {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  ∫ q : Submission.BoseGases.X n × (E3 × E3),
    ((Θ q.1 : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
      * ChAU v h fc fu μ N q.2.1 (q.1 j) q.2.2
      * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)

/-- The `(A)`-channel word integral. -/
def chAword {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  ∫ x in Submission.BoseGases.abox n (ellH v μ),
    ((Θ x : ℝ) : ℂ)
      * ((Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
      * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
            (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)) x
          : ℝ) : ℂ)

/-- The `(A)`-channel alias slot (`KfrU − ℓ³W1fun` against the low slot). -/
def chAslot {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  ∫ x : Submission.BoseGases.X n,
    ((Θ x : ℝ) : ℂ)
      * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (x i) : ℝ) : ℂ)
      * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (x j) : ℝ) : ℂ)
      * (KfrU v h μ fu N (x j - x i)
          - ((ellH v μ : ℂ)) ^ 3 * ((Work.BoseFixR.W1fun v h (ellH v μ) (x j - x i) : ℝ) : ℂ))
      * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
            (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)) x
          : ℝ) : ℂ)

/-- The `(A)`-channel lattice-image slot. -/
def chAimg {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  ∫ x : Submission.BoseGases.X n,
    ((Θ x : ℝ) : ℂ)
      * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (x i) : ℝ) : ℂ)
      * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (x j) : ℝ) : ℂ)
      * KfrU v h μ fu N (x j - x i)
      * (∫ u in Submission.BoseGases.acube (ellH v μ),
          (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
              else ((lowKer fc (chKappa v μ)
                (u - x j + ellH v μ • latVec d) : ℝ) : ℂ))
            * ((Submission.BoseGases.aQ (ellH v μ) j
                (Submission.BoseGases.aP (ellH v μ) i Θ) (Function.update x j u) : ℝ) : ℂ))

theorem chAint_eq {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (hvrad : _root_.BoseGases.IsRadial v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hℓ : 0 < ellH v μ)
    (hκ : 0 < chKappa v μ)
    (hN : 2 * (chKappa v μ) * ellH v μ / (2 * Real.pi) ≤ (N : ℝ))
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    chAint v h fc fu μ N i j Θ
      = ((ellH v μ : ℂ)) ^ 9 * chAword v h fc fu μ N i j Θ
        + ((ellH v μ : ℂ)) ^ 6 * (chAslot v h fc fu μ N i j Θ + chAimg v h fc fu μ N i j Θ) := by
  have h1 := Achan_dzero_split hij v h fc fu μ N hℓ (by simpa only [chKappa] using hκ)
    (by simpa only [chKappa] using hN) Θ hΘ hΘm hΘb hΘs
  have h2 := Achan_dzero_word_split_v2 hij v h hvrad fc fu μ N hℓ
    (by simpa only [chKappa] using hκ) Θ hΘ hΘm hΘb hΘs
  simp only [chAint, chAword, chAslot, chAimg, chKappa] at h1 h2 ⊢
  rw [h1, h2]
  ring

/-! ## The `(B)` channel -/

def chBint {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  ∫ q : Submission.BoseGases.X n × (E3 × E3),
    ((Θ q.1 : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
      * ChBU v h fc fu μ N q.2.1 (q.1 j) q.2.2
      * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)

def chBword {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  ∫ x in Submission.BoseGases.abox n (ellH v μ),
    ((Submission.BoseGases.aP (ellH v μ) i Θ x : ℝ) : ℂ)
      * ((Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
      * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
            (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)) x
          : ℝ) : ℂ)

def chBslot {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  ∫ x : Submission.BoseGases.X n,
    ((Θ x : ℝ) : ℂ)
      * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (x j) : ℝ) : ℂ)
      * (KχfrU v h μ fu N (x j)
          - (∫ y : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
              * ((Work.BoseFixR.W1fun v h (ellH v μ) (y - x j) : ℝ) : ℂ)))
      * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
            (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)) x
          : ℝ) : ℂ)

def chBimg {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  ∫ x : Submission.BoseGases.X n,
    ((Θ x : ℝ) : ℂ)
      * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (x j) : ℝ) : ℂ)
      * KχfrU v h μ fu N (x j)
      * (∫ u in Submission.BoseGases.acube (ellH v μ),
          (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
              else ((lowKer fc (chKappa v μ)
                (u - x j + ellH v μ • latVec d) : ℝ) : ℂ))
            * ((Submission.BoseGases.aQ (ellH v μ) j
                (Submission.BoseGases.aP (ellH v μ) i Θ) (Function.update x j u) : ℝ) : ℂ))

theorem chBint_eq {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hℓ : 0 < ellH v μ)
    (hκ : 0 < chKappa v μ)
    (hN : 2 * (chKappa v μ) * ellH v μ / (2 * Real.pi) ≤ (N : ℝ))
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    chBint v h fc fu μ N i j Θ
      = ((ellH v μ : ℂ)) ^ 9 * chBword v h fc fu μ N i j Θ
        + ((ellH v μ : ℂ)) ^ 6 * (chBslot v h fc fu μ N i j Θ + chBimg v h fc fu μ N i j Θ) := by
  have h1 := Bchan_dzero_split hij v h fc fu μ N hℓ (by simpa only [chKappa] using hκ)
    (by simpa only [chKappa] using hN) Θ hΘ hΘm hΘb hΘs
  have h2 := Bchan_dzero_word_split_v3 hij v h fc fu μ N hℓ
    (by simpa only [chKappa] using hκ) Θ hΘ hΘm hΘb hΘs
  simp only [chBint, chBword, chBslot, chBimg, chKappa] at h1 h2 ⊢
  rw [h1, h2]
  ring

/-! ## The sign substitution for the `KχfrU`-smear (the twin of `slotAvg_neg`) -/

theorem slotAvg_neg_Kchi {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {fu : Work.BoseBoxFix.LowCut} {N : ℕ} (H : E3 → ℂ) :
    (∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * KχfrU v h μ fu N w * H (-w))
      = ∫ z : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)
        * KχfrU v h μ fu N z * H z := by
  have hneg := (MeasureTheory.Measure.measurePreserving_neg
    (MeasureTheory.volume : MeasureTheory.Measure E3)).integral_comp
    measurableEmbedding_neg
    (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)
      * KχfrU v h μ fu N z * H z)
  have hpt : ∀ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * KχfrU v h μ fu N w * H (-w)
      = ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (-w) : ℝ) : ℂ)
        * KχfrU v h μ fu N (-w) * H (-w) := fun w => by
    rw [Work.BoseB4.BoxData.chiLam_even, KχfrU_neg v h μ fu N w]
  exact (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)).trans hneg

/-! ## The `(C)` channel -/

def chCint {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  ∫ q : Submission.BoseGases.X n × (E3 × E3),
    ((Θ q.1 : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
      * ChCU v h fc fu μ N q.2.1 (q.1 j) q.2.2
      * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)

def chCword {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  ∫ x in Submission.BoseGases.abox n (ellH v μ),
    ((Submission.BoseGases.aP (ellH v μ) j Θ x : ℝ) : ℂ)
      * ((Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
      * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
            (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)) x
          : ℝ) : ℂ)

def chCslot {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  ∫ x : Submission.BoseGases.X n,
    ((Θ x : ℝ) : ℂ)
      * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (x i) : ℝ) : ℂ)
      * (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)
          * (KfrU v h μ fu N (x i - z)
              - ((ellH v μ : ℂ)) ^ 3
                * ((Work.BoseFixR.W1fun v h (ellH v μ) (x i - z) : ℝ) : ℂ))
          * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
                (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ))
                (Function.update x j z) : ℝ) : ℂ))

def chCimg {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  ∫ x : Submission.BoseGases.X n,
    ((Θ x : ℝ) : ℂ)
      * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (x i) : ℝ) : ℂ)
      * (∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * KfrU v h μ fu N (x i + w)
          * (∫ u in Submission.BoseGases.acube (ellH v μ),
              (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
                  else ((lowKer fc (chKappa v μ)
                    (u + w + ellH v μ • latVec d) : ℝ) : ℂ))
                * ((Submission.BoseGases.aQ (ellH v μ) j
                    (Submission.BoseGases.aP (ellH v μ) i Θ) (Function.update x j u) : ℝ) : ℂ)))

theorem chCint_eq {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hℓ : 0 < ellH v μ)
    (hκ : 0 < chKappa v μ)
    (hN : 2 * (chKappa v μ) * ellH v μ / (2 * Real.pi) ≤ (N : ℝ))
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    chCint v h fc fu μ N i j Θ
      = ((ellH v μ : ℂ)) ^ 9 * chCword v h fc fu μ N i j Θ
        + ((ellH v μ : ℂ)) ^ 3 * (chCslot v h fc fu μ N i j Θ + chCimg v h fc fu μ N i j Θ) := by
  have h1 := Cchan_dzero_split hij v h fc fu μ N hℓ (by simpa only [chKappa] using hκ)
    (by simpa only [chKappa] using hN) Θ hΘ hΘm hΘb hΘs
  have h2 := Cchan_dzero_word_split_v4 hij v h fc fu μ N hℓ
    (by simpa only [chKappa] using hκ) Θ hΘ hΘm hΘb hΘs
  simp only [chCint, chCword, chCslot, chCimg, chKappa] at h1 h2 ⊢
  have hsub : ∀ x : Submission.BoseGases.X n,
      (∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * KfrU v h μ fu N (x i + w)
          * ((Work.BoseBoxFix.lowSlot fc
                ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                  * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ (ellH v μ) j
                (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ))
                (Function.update x j (-w)) : ℝ) : ℂ))
        = ∫ z : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)
          * KfrU v h μ fu N (x i - z)
          * ((Work.BoseBoxFix.lowSlot fc
                ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                  * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ (ellH v μ) j
                (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ))
                (Function.update x j z) : ℝ) : ℂ) := by
    intro x
    exact slotAvg_neg (v := v) (h := h) (μ := μ) (fu := fu) (N := N) (x i)
      (fun z : E3 => ((Work.BoseBoxFix.lowSlot fc
        ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ (ellH v μ) j
        (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ))
        (Function.update x j z) : ℝ) : ℂ))
  have hsub' : (∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ) * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (x i) : ℝ) : ℂ)
          * (∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
              * KfrU v h μ fu N (x i + w)
              * ((Work.BoseBoxFix.lowSlot fc
                    ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ (ellH v μ) j
                    (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ))
                    (Function.update x j (-w)) : ℝ) : ℂ)))
      = ∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ) * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (x i) : ℝ) : ℂ)
          * (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)
              * KfrU v h μ fu N (x i - z)
              * ((Work.BoseBoxFix.lowSlot fc
                    ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ (ellH v μ) j
                    (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ))
                    (Function.update x j z) : ℝ) : ℂ)) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x =>
      congrArg (fun t : ℂ => ((Θ x : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (x i) : ℝ) : ℂ) * t) (hsub x)))
  rw [h1, hsub', h2]
  ring

/-! ## The `(D)` channel -/

def chDint {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  ∫ q : Submission.BoseGases.X n × (E3 × E3),
    ((Θ q.1 : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
      * ChDU v h fc fu μ N q.2.1 (q.1 j) q.2.2
      * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)

def chDword {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  ∫ x in Submission.BoseGases.abox n (ellH v μ),
    ((Submission.BoseGases.aP (ellH v μ) i (Submission.BoseGases.aP (ellH v μ) j Θ) x : ℝ) : ℂ)
      * ((Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
      * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
            (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)) x
          : ℝ) : ℂ)

def chDslot {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  ∫ x : Submission.BoseGases.X n,
    ((Θ x : ℝ) : ℂ)
      * (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)
          * (KχfrU v h μ fu N z
              - (∫ y : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
                  * ((Work.BoseFixR.W1fun v h (ellH v μ) (y - z) : ℝ) : ℂ)))
          * ((Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
                (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ))
                (Function.update x j z) : ℝ) : ℂ))

def chDimg {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  ∫ x : Submission.BoseGases.X n,
    ((Θ x : ℝ) : ℂ)
      * (∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * KχfrU v h μ fu N w
          * (∫ u in Submission.BoseGases.acube (ellH v μ),
              (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
                  else ((lowKer fc (chKappa v μ)
                    (u + w + ellH v μ • latVec d) : ℝ) : ℂ))
                * ((Submission.BoseGases.aQ (ellH v μ) j
                    (Submission.BoseGases.aP (ellH v μ) i Θ) (Function.update x j u) : ℝ) : ℂ)))

theorem chDint_eq {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hℓ : 0 < ellH v μ)
    (hκ : 0 < chKappa v μ)
    (hN : 2 * (chKappa v μ) * ellH v μ / (2 * Real.pi) ≤ (N : ℝ))
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    chDint v h fc fu μ N i j Θ
      = ((ellH v μ : ℂ)) ^ 9 * chDword v h fc fu μ N i j Θ
        + ((ellH v μ : ℂ)) ^ 3 * (chDslot v h fc fu μ N i j Θ + chDimg v h fc fu μ N i j Θ) := by
  have h1 := Dchan_dzero_split hij v h fc fu μ N hℓ (by simpa only [chKappa] using hκ)
    (by simpa only [chKappa] using hN) Θ hΘ hΘm hΘb hΘs
  have h2 := Dchan_dzero_word_split hij v h fc fu μ N hℓ
    (by simpa only [chKappa] using hκ) Θ hΘ hΘm hΘb hΘs
  simp only [chDint, chDword, chDslot, chDimg, chKappa] at h1 h2 ⊢
  have hsub : ∀ x : Submission.BoseGases.X n,
      (∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * KχfrU v h μ fu N w
          * ((Work.BoseBoxFix.lowSlot fc
                ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                  * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ (ellH v μ) j
                (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ))
                (Function.update x j (-w)) : ℝ) : ℂ))
        = ∫ z : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)
          * KχfrU v h μ fu N z
          * ((Work.BoseBoxFix.lowSlot fc
                ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                  * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ (ellH v μ) j
                (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ))
                (Function.update x j z) : ℝ) : ℂ) := by
    intro x
    exact slotAvg_neg_Kchi (v := v) (h := h) (μ := μ) (fu := fu) (N := N)
      (fun z : E3 => ((Work.BoseBoxFix.lowSlot fc
        ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ (ellH v μ) j
        (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ))
        (Function.update x j z) : ℝ) : ℂ))
  have hsub' : (∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ)
          * (∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
              * KχfrU v h μ fu N w
              * ((Work.BoseBoxFix.lowSlot fc
                    ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ (ellH v μ) j
                    (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ))
                    (Function.update x j (-w)) : ℝ) : ℂ)))
      = ∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ)
          * (∫ z : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)
              * KχfrU v h μ fu N z
              * ((Work.BoseBoxFix.lowSlot fc
                    ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ (ellH v μ) j
                    (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ))
                    (Function.update x j z) : ℝ) : ℂ)) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x =>
      congrArg (fun t : ℂ => ((Θ x : ℝ) : ℂ) * t) (hsub x)))
  rw [h1, hsub', h2]
  ring

/-! ## The four channel integrands, as one-variable functions (for integrability) -/

/-- The integrand of the `(A)`-channel integral `chAint`. -/
def chAintand {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) :
    Submission.BoseGases.X n × (E3 × E3) → ℂ :=
  fun q => ((Θ q.1 : ℝ) : ℂ)
    * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
    * ChAU v h fc fu μ N q.2.1 (q.1 j) q.2.2
    * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)

/-- The integrand of the `(B)`-channel integral `chBint`. -/
def chBintand {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) :
    Submission.BoseGases.X n × (E3 × E3) → ℂ :=
  fun q => ((Θ q.1 : ℝ) : ℂ)
    * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
    * ChBU v h fc fu μ N q.2.1 (q.1 j) q.2.2
    * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)

/-- The integrand of the `(C)`-channel integral `chCint`. -/
def chCintand {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) :
    Submission.BoseGases.X n × (E3 × E3) → ℂ :=
  fun q => ((Θ q.1 : ℝ) : ℂ)
    * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
    * ChCU v h fc fu μ N q.2.1 (q.1 j) q.2.2
    * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)

/-- The integrand of the `(D)`-channel integral `chDint`. -/
def chDintand {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) :
    Submission.BoseGases.X n × (E3 × E3) → ℂ :=
  fun q => ((Θ q.1 : ℝ) : ℂ)
    * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
    * ChDU v h fc fu μ N q.2.1 (q.1 j) q.2.2
    * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)

theorem chAint_eq_integral (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) {n : ℕ} (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) :
    chAint v h fc fu μ N i j Θ
      = ∫ q : Submission.BoseGases.X n × (E3 × E3), chAintand v h fc fu μ N i j Θ q := rfl

theorem chBint_eq_integral (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) {n : ℕ} (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) :
    chBint v h fc fu μ N i j Θ
      = ∫ q : Submission.BoseGases.X n × (E3 × E3), chBintand v h fc fu μ N i j Θ q := rfl

theorem chCint_eq_integral (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) {n : ℕ} (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) :
    chCint v h fc fu μ N i j Θ
      = ∫ q : Submission.BoseGases.X n × (E3 × E3), chCintand v h fc fu μ N i j Θ q := rfl

theorem chDint_eq_integral (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) {n : ℕ} (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) :
    chDint v h fc fu μ N i j Θ
      = ∫ q : Submission.BoseGases.X n × (E3 × E3), chDintand v h fc fu μ N i j Θ q := rfl

/-! ## The combined per-pair identity -/

/-- The word part of the combined channel difference: `(1 − P_i − P_j + P_iP_j)Θ` against `w₁`. -/
def chWord {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  chAword v h fc fu μ N i j Θ - chBword v h fc fu μ N i j Θ
    - chCword v h fc fu μ N i j Θ + chDword v h fc fu μ N i j Θ

/-- The two alias slots of the `(A)`,`(B)` pair, with the channel signs. -/
def chSlotAB {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  (chAslot v h fc fu μ N i j Θ + chAimg v h fc fu μ N i j Θ)
    - (chBslot v h fc fu μ N i j Θ + chBimg v h fc fu μ N i j Θ)

/-- The two alias slots of the `(C)`,`(D)` pair, with the channel signs. -/
def chSlotCD {n : ℕ} (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (i j : Fin n) (Θ : Submission.BoseGases.X n → ℝ) : ℂ :=
  - (chCslot v h fc fu μ N i j Θ + chCimg v h fc fu μ N i j Θ)
    + (chDslot v h fc fu μ N i j Θ + chDimg v h fc fu μ N i j Θ)

/-- **The combined per-pair channel identity.** -/
theorem chDiff_eq {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (hvrad : _root_.BoseGases.IsRadial v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hℓ : 0 < ellH v μ)
    (hκ : 0 < chKappa v μ)
    (hN : 2 * (chKappa v μ) * ellH v μ / (2 * Real.pi) ≤ (N : ℝ))
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    chAint v h fc fu μ N i j Θ - chBint v h fc fu μ N i j Θ
        - chCint v h fc fu μ N i j Θ + chDint v h fc fu μ N i j Θ
      = ((ellH v μ : ℂ)) ^ 9 * chWord v h fc fu μ N i j Θ
        + ((ellH v μ : ℂ)) ^ 6 * chSlotAB v h fc fu μ N i j Θ
        + ((ellH v μ : ℂ)) ^ 3 * chSlotCD v h fc fu μ N i j Θ := by
  have hA := chAint_eq hij v h hvrad fc fu μ N hℓ hκ hN Θ hΘ hΘm hΘb hΘs
  have hB := chBint_eq hij v h fc fu μ N hℓ hκ hN Θ hΘ hΘm hΘb hΘs
  have hC := chCint_eq hij v h fc fu μ N hℓ hκ hN Θ hΘ hΘm hΘb hΘs
  have hD := chDint_eq hij v h fc fu μ N hℓ hκ hN Θ hΘ hΘm hΘb hΘs
  simp only [chWord, chSlotAB, chSlotCD] at *
  rw [hA, hB, hC, hD]
  ring

end Work.BoseBoxFock.PCFU
