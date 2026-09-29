import Mathlib
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.paProofs1
import Submission.Work.Resample.pbCostArithKit
import Submission.Work.MainP.ss_prod_le_ts_prod
import Submission.Work.Resample.paDSumT
import Submission.Work.Resample.paDSumCm
import Submission.Work.Resample.paDSetupBr
import Submission.Work.Resample.paDRestLit

namespace Work.Resample

open HvdH

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! ## Splitting the per-axis budget

`PABr` is a sum of nine terms.  For the cost arithmetic of `Work.Resample.paCostD` it is useful to
group them as

* `paDZ` — the `prep` table of the axis (`Kb * (t_j+1) * (p+1)^Kb`), absorbed by the
  `ts.sum * (p+1)^K` term of `resCost`;
* `paDCm` — the `applyAlong` passes that call `self` (the only terms carrying `Cm`), absorbed by the
  `ts.prod * (√p+1) * α * (Cm (K*p) + p)` term;
* `paDRest` — the layout, `isz` and constant terms, absorbed by the `ts.prod * p^2` term. -/

/-- The `prep`-table term of `PABr` at axis `j`. -/
def paDZ (Kb p : ℕ) (ts : List ℕ) (j : ℕ) : ℕ :=
  Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb

/-- The `Cm`-carrying terms of `PABr` at axis `j`. -/
def paDCm (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) : ℕ :=
  ((ts.take j).prod * (ss.drop (j + 1)).prod) *
    (Kb * (ts.getD j 0 + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1))

/-- The remaining terms of `PABr` at axis `j` (layout, `isz` and the `j`-independent constants). -/
def paDRest (Kb p : ℕ) (ss ts : List ℕ) (j : ℕ) : ℕ :=
  64 * (((ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
      ((2 * p + 8) +
        ((ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
      (((ts.take j).prod * (ss.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)).size + 1))
  + 64 * (HvdH.isz (((ts.take j).prod : ℕ) : ℤ) + HvdH.isz ((ss.getD j 0 : ℕ) : ℤ) +
      HvdH.isz ((ts.getD j 0 : ℕ) : ℤ) + HvdH.isz (((ss.drop (j + 1)).prod : ℕ) : ℤ))
  + 1048576 * (ts.prod * (2 * p + 8) + ts.prod + 2)
  + 1048576 * ((HvdH.D + 1) * (p + 2))
  + 1048576 * ((HvdH.D + 1) * (p + 2) * ((HvdH.D + 1) * (p + 2)))
  + 1048576 * ((p + 3) * (p + 3))
  + 1000000

/-- `PABr` is the sum of its three groups. -/
theorem paDBr_eq (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) :
    PABr Kb Cm p α ss ts j =
      64 * paDZ Kb p ts j + 64 * paDCm Kb Cm p α ss ts j + paDRest Kb p ss ts j := by
  unfold PABr paDZ paDCm paDRest
  ring


/-- The explicit constant of `paCostD`: `1000 * (Kc1 + Kc2 + Kc3 + Kb + D^3 + 1)^8`. -/
def paDK (Kb Kc1 Kc2 Kc3 : ℕ) : ℕ :=
  1000 * (Kc1 + Kc2 + Kc3 + Kb + HvdH.D ^ 3 + 1) ^ 8

/-- The arithmetic requirements on `paDK` used by the three group estimates of `paCostD`:
`K` dominates each of the four constants, and it is large enough for the three coefficient
comparisons `128*Kc2*Kb ≤ K` (`prep` group), `512*Kc2*D*Kb ≤ K` (`Cm` group) and
`4096*(Kc1+Kc3) + (Kc2*(D*(2^24*D^3*(D+5))) + Kc2) ≤ K` (`paDRest`/setup/epilogue group). -/
theorem paDK_facts (Kb Kc1 Kc2 Kc3 : ℕ) :
    Kc1 ≤ paDK Kb Kc1 Kc2 Kc3 ∧
    Kc2 ≤ paDK Kb Kc1 Kc2 Kc3 ∧
    Kc3 ≤ paDK Kb Kc1 Kc2 Kc3 ∧
    Kb ≤ paDK Kb Kc1 Kc2 Kc3 ∧
    128 * Kc2 * Kb ≤ paDK Kb Kc1 Kc2 Kc3 ∧
    512 * Kc2 * HvdH.D * Kb ≤ paDK Kb Kc1 Kc2 Kc3 ∧
    4096 * (Kc1 + Kc3) ≤ paDK Kb Kc1 Kc2 Kc3 ∧
    4096 * (Kc1 + Kc3)
      + (Kc2 * (HvdH.D * (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5))) + Kc2)
        ≤ paDK Kb Kc1 Kc2 Kc3 := by
  set T : ℕ := Kc1 + Kc2 + Kc3 + Kb + HvdH.D ^ 3 + 1 with hTdef
  have hKdef : paDK Kb Kc1 Kc2 Kc3 = 1000 * T ^ 8 := by rw [paDK, hTdef]
  have hT1 : 1 ≤ T := by rw [hTdef]; omega
  have hTc1 : Kc1 ≤ T := by rw [hTdef]; omega
  have hTc2 : Kc2 ≤ T := by rw [hTdef]; omega
  have hTc3 : Kc3 ≤ T := by rw [hTdef]; omega
  have hTKb : Kb ≤ T := by rw [hTdef]; omega
  have hTD : HvdH.D ≤ T := by
    have h : HvdH.D ≤ HvdH.D ^ 3 := by rw [pbcaD]; norm_num
    rw [hTdef]; omega
  have hT8 : T ≤ T ^ 8 := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < T) (show 1 ≤ 8 by norm_num)
  have hTnum : ∀ n : ℕ, n ≤ 1729 ^ 3 → n ≤ T := by
    intro n hn
    have hn' : n ≤ HvdH.D ^ 3 := by rw [pbcaD]; exact hn
    rw [hTdef]; omega
  have h128 : 128 ≤ T := hTnum 128 (by norm_num)
  have h512 : 512 ≤ T := hTnum 512 (by norm_num)
  have h4096 : 4096 ≤ T := hTnum 4096 (by norm_num)
  have h2p24 : 2 ^ 24 ≤ T := hTnum (2 ^ 24) (by norm_num)
  have hD5 : HvdH.D + 5 ≤ T := by rw [pbcaD]; exact hTnum 1734 (by norm_num)
  have hb1 : ∀ a : ℕ, a ≤ T → a ≤ 100 * T ^ 8 := fun a ha => pbcaKge1 T a hT1 ha
  have hb2 : ∀ a b : ℕ, a ≤ T → b ≤ T → a * b ≤ 100 * T ^ 8 :=
    fun a b ha hb => pbcaKge2 T a b hT1 ha hb
  have hb3 : ∀ a b c : ℕ, a ≤ T → b ≤ T → c ≤ T → a * b * c ≤ 100 * T ^ 8 :=
    fun a b c ha hb hc => pbcaKge3 T a b c hT1 ha hb hc
  have hb4 : ∀ a b c d : ℕ, a ≤ T → b ≤ T → c ≤ T → d ≤ T → a * b * c * d ≤ 100 * T ^ 8 :=
    fun a b c d ha hb hc hd => pbcaKge4 T a b c d hT1 ha hb hc hd
  have hb7 : ∀ a b c d e f g : ℕ, a ≤ T → b ≤ T → c ≤ T → d ≤ T → e ≤ T → f ≤ T → g ≤ T →
      a * b * c * d * e * f * g ≤ 100 * T ^ 8 := by
    intro a b c d e f g ha hb hc hd he hf hg
    calc a * b * c * d * e * f * g ≤ T * T * T * T * T * T * T := by gcongr
      _ = T ^ 7 := by ring
      _ ≤ T ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ ≤ 100 * T ^ 8 := by omega
  have h5 : 128 * Kc2 * Kb ≤ 100 * T ^ 8 := hb3 128 Kc2 Kb h128 hTc2 hTKb
  have h6 : 512 * Kc2 * HvdH.D * Kb ≤ 100 * T ^ 8 :=
    hb4 512 Kc2 HvdH.D Kb h512 hTc2 hTD hTKb
  have h7 : 4096 * Kc1 ≤ 100 * T ^ 8 := hb2 4096 Kc1 h4096 hTc1
  have h8 : 4096 * Kc3 ≤ 100 * T ^ 8 := hb2 4096 Kc3 h4096 hTc3
  have h9 : 4096 * (Kc1 + Kc3) ≤ 200 * T ^ 8 := by omega
  have h10 : Kc2 * HvdH.D * 2 ^ 24 * HvdH.D * HvdH.D * HvdH.D * (HvdH.D + 5) ≤ 100 * T ^ 8 :=
    hb7 Kc2 HvdH.D (2 ^ 24) HvdH.D HvdH.D HvdH.D (HvdH.D + 5) hTc2 hTD h2p24 hTD hTD hTD hD5
  have h11 : Kc2 ≤ 100 * T ^ 8 := hb1 Kc2 hTc2
  have hHe : Kc2 * (HvdH.D * (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5)))
      = Kc2 * HvdH.D * 2 ^ 24 * HvdH.D * HvdH.D * HvdH.D * (HvdH.D + 5) := by ring
  have h12 : Kc2 * (HvdH.D * (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5))) + Kc2 ≤ 200 * T ^ 8 := by
    rw [hHe]; omega
  have h13 : 4096 * (Kc1 + Kc3)
      + (Kc2 * (HvdH.D * (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5))) + Kc2) ≤ 400 * T ^ 8 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hKdef]
  all_goals omega

/-- **Group `Z` of the cost arithmetic.**  The `prep` table of every axis
(`Kb * (t_j + 1) * (p + 1)^Kb`) is absorbed by the `ts.sum * (p + 1)^K` term of `resCost`. -/
theorem paDGroupZ {Kb Kc2 p α : ℕ} {ss ts : List ℕ} (h : HvdH.ResParams p α ss ts) {K : ℕ}
    (hKbK : Kb ≤ K) (hKz : 128 * Kc2 * Kb ≤ K) :
    Kc2 * (64 * (∑ j ∈ Finset.range HvdH.D, paDZ Kb p ts j))
      ≤ K * ts.sum * (p + 1) ^ K := by
  have hSZ : (∑ j ∈ Finset.range HvdH.D, paDZ Kb p ts j)
      ≤ 2 * Kb * (p + 1) ^ Kb * ts.sum := by
    have h1 : (∑ j ∈ Finset.range HvdH.D, paDZ Kb p ts j)
        = Kb * (p + 1) ^ Kb * (∑ j ∈ Finset.range HvdH.D, (ts.getD j 0 + 1)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by unfold paDZ; ring)
    rw [h1]
    calc Kb * (p + 1) ^ Kb * (∑ j ∈ Finset.range HvdH.D, (ts.getD j 0 + 1))
        ≤ Kb * (p + 1) ^ Kb * (2 * ts.sum) := Nat.mul_le_mul_left _ (paDSumT h)
      _ = 2 * Kb * (p + 1) ^ Kb * ts.sum := by ring
  have hp1 : 1 ≤ p := by have := h.2.2.1; omega
  have hZb : (p + 1) ^ Kb ≤ (p + 1) ^ K := Nat.pow_le_pow_right (by omega) hKbK
  calc Kc2 * (64 * (∑ j ∈ Finset.range HvdH.D, paDZ Kb p ts j))
      ≤ Kc2 * (64 * (2 * Kb * (p + 1) ^ Kb * ts.sum)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hSZ)
    _ = (128 * Kc2 * Kb) * (ts.sum * (p + 1) ^ Kb) := by ring
    _ ≤ (128 * Kc2 * Kb) * (ts.sum * (p + 1) ^ K) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hZb)
    _ ≤ K * (ts.sum * (p + 1) ^ K) := Nat.mul_le_mul_right _ hKz
    _ = K * ts.sum * (p + 1) ^ K := by ring

/-- **Group `Cm` of the cost arithmetic.**  The `applyAlong` passes calling `self` are absorbed by
the `ts.prod * (√p + 1) * α * (Cm (K*p) + p)` term of `resCost`. -/
theorem paDGroupCm {Kb Kc2 p α : ℕ} {ss ts : List ℕ} (h : HvdH.ResParams p α ss ts)
    (Cm : ℕ → ℕ) (hmon : Monotone Cm) {K : ℕ} (hKbK : Kb ≤ K)
    (hKcm : 512 * Kc2 * HvdH.D * Kb ≤ K) :
    Kc2 * (64 * (∑ j ∈ Finset.range HvdH.D, paDCm Kb Cm p α ss ts j))
      ≤ K * ts.prod * (Nat.sqrt p + 1) * α * (Cm (K * p) + p) := by
  have hSCm : (∑ j ∈ Finset.range HvdH.D, paDCm Kb Cm p α ss ts j)
      ≤ Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1) * (2 * HvdH.D * ts.prod) := by
    have h1 : (∑ j ∈ Finset.range HvdH.D, paDCm Kb Cm p α ss ts j)
        = (Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1))
          * (∑ j ∈ Finset.range HvdH.D,
              (ts.take j).prod * (ss.drop (j + 1)).prod * (ts.getD j 0 + 1)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by unfold paDCm; ring)
    rw [h1]
    calc (Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1))
          * (∑ j ∈ Finset.range HvdH.D,
              (ts.take j).prod * (ss.drop (j + 1)).prod * (ts.getD j 0 + 1))
        ≤ (Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1))
          * (2 * HvdH.D * ts.prod) := Nat.mul_le_mul_left _ (paDSumCm h)
      _ = Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1)
          * (2 * HvdH.D * ts.prod) := by ring
  have hmonK : Cm (Kb * p) ≤ Cm (K * p) := hmon (Nat.mul_le_mul_right p hKbK)
  have hα1 : 1 ≤ α := by have := h.2.2.2.1; omega
  have hp1 : 1 ≤ p := by have := h.2.2.1; omega
  have hα2' : α + 1 ≤ 2 * α := by omega
  have hpp' : Cm (Kb * p) + p + 1 ≤ 2 * (Cm (K * p) + p) := by omega
  have hcoef : 128 * Kc2 * HvdH.D * Kb * ((α + 1) * (Cm (Kb * p) + p + 1))
      ≤ K * (α * (Cm (K * p) + p)) := by
    have hstep : 128 * Kc2 * HvdH.D * Kb * ((α + 1) * (Cm (Kb * p) + p + 1))
        ≤ 128 * Kc2 * HvdH.D * Kb * ((2 * α) * (2 * (Cm (K * p) + p))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hα2' hpp')
    have heq : 128 * Kc2 * HvdH.D * Kb * ((2 * α) * (2 * (Cm (K * p) + p)))
        = (512 * Kc2 * HvdH.D * Kb) * (α * (Cm (K * p) + p)) := by ring
    rw [heq] at hstep
    exact le_trans hstep (Nat.mul_le_mul_right _ hKcm)
  calc Kc2 * (64 * (∑ j ∈ Finset.range HvdH.D, paDCm Kb Cm p α ss ts j))
      ≤ Kc2 * (64 * (Kb * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1)
          * (2 * HvdH.D * ts.prod))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hSCm)
    _ = (ts.prod * (Nat.sqrt p + 1))
          * (128 * Kc2 * HvdH.D * Kb * ((α + 1) * (Cm (Kb * p) + p + 1))) := by ring
    _ ≤ (ts.prod * (Nat.sqrt p + 1)) * (K * (α * (Cm (K * p) + p))) :=
        Nat.mul_le_mul_left _ hcoef
    _ = K * ts.prod * (Nat.sqrt p + 1) * α * (Cm (K * p) + p) := by ring

/-- **Group `A` of the cost arithmetic.**  The prologue, the epilogue and everything in the per-axis
budgets except the `prep` tables and the `Cm`-carrying passes are absorbed by the `ts.prod * p^2`
term of `resCost`. -/
theorem paDGroupA {Kb Kc1 Kc2 Kc3 p α : ℕ} {ss ts : List ℕ}
    (h : HvdH.ResParams p α ss ts) {K : ℕ}
    (hreq : 4096 * (Kc1 + Kc3)
      + (Kc2 * (HvdH.D * (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5))) + Kc2) ≤ K)
    (hsetup : PASetupBr p ss ts + PAFinalBr p ss ts ≤ 4096 * (ts.prod * p ^ 2))
    (hrest : ∀ j : ℕ, j < HvdH.D → paDRest Kb p ss ts j
      ≤ (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5)) * (ts.prod * p ^ 2)) :
    Kc1 * PASetupBr p ss ts
      + Kc2 * ((∑ j ∈ Finset.range HvdH.D, paDRest Kb p ss ts j) + 1)
      + Kc3 * PAFinalBr p ss ts ≤ K * (ts.prod * p ^ 2) := by
  have hA1 : 1 ≤ ts.prod := (pbcaParamFacts p α ss ts h).1
  have hp1 : 1 ≤ p := by have := h.2.2.1; omega
  have hB1 : 1 ≤ ts.prod * p ^ 2 := by
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ ts.prod * p ^ 2 := Nat.mul_le_mul hA1 (by nlinarith)
  have hSR : (∑ j ∈ Finset.range HvdH.D, paDRest Kb p ss ts j)
      ≤ HvdH.D * ((2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5)) * (ts.prod * p ^ 2)) := by
    have hcard : (Finset.range HvdH.D).card = HvdH.D := Finset.card_range _
    calc (∑ j ∈ Finset.range HvdH.D, paDRest Kb p ss ts j)
        ≤ ∑ _j ∈ Finset.range HvdH.D,
            ((2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5)) * (ts.prod * p ^ 2)) :=
          Finset.sum_le_sum (fun j hj => hrest j (Finset.mem_range.mp hj))
      _ = HvdH.D * ((2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5)) * (ts.prod * p ^ 2)) := by
          rw [Finset.sum_const, hcard, smul_eq_mul]
  have h1 : Kc1 * PASetupBr p ss ts + Kc3 * PAFinalBr p ss ts
      ≤ (4096 * (Kc1 + Kc3)) * (ts.prod * p ^ 2) := by
    have ha : Kc1 * PASetupBr p ss ts ≤ Kc1 * (4096 * (ts.prod * p ^ 2)) :=
      le_trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) (Nat.mul_le_mul_left _ hsetup)
    have hb : Kc3 * PAFinalBr p ss ts ≤ Kc3 * (4096 * (ts.prod * p ^ 2)) :=
      le_trans (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) (Nat.mul_le_mul_left _ hsetup)
    calc Kc1 * PASetupBr p ss ts + Kc3 * PAFinalBr p ss ts
        ≤ Kc1 * (4096 * (ts.prod * p ^ 2)) + Kc3 * (4096 * (ts.prod * p ^ 2)) :=
          add_le_add ha hb
      _ = (4096 * (Kc1 + Kc3)) * (ts.prod * p ^ 2) := by ring
  have h2 : Kc2 * ((∑ j ∈ Finset.range HvdH.D, paDRest Kb p ss ts j) + 1)
      ≤ (Kc2 * (HvdH.D * (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5))) + Kc2) * (ts.prod * p ^ 2) := by
    have hSR1 : (∑ j ∈ Finset.range HvdH.D, paDRest Kb p ss ts j) + 1
        ≤ (HvdH.D * (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5)) + 1) * (ts.prod * p ^ 2) := by
      have h0 := hSR
      calc (∑ j ∈ Finset.range HvdH.D, paDRest Kb p ss ts j) + 1
          ≤ HvdH.D * ((2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5)) * (ts.prod * p ^ 2))
            + (ts.prod * p ^ 2) := by omega
        _ = (HvdH.D * (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5)) + 1) * (ts.prod * p ^ 2) := by ring
    calc Kc2 * ((∑ j ∈ Finset.range HvdH.D, paDRest Kb p ss ts j) + 1)
        ≤ Kc2 * ((HvdH.D * (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5)) + 1) * (ts.prod * p ^ 2)) :=
          Nat.mul_le_mul_left _ hSR1
      _ = (Kc2 * (HvdH.D * (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5))) + Kc2) * (ts.prod * p ^ 2) := by
          ring
  calc Kc1 * PASetupBr p ss ts
        + Kc2 * ((∑ j ∈ Finset.range HvdH.D, paDRest Kb p ss ts j) + 1)
        + Kc3 * PAFinalBr p ss ts
      = (Kc1 * PASetupBr p ss ts + Kc3 * PAFinalBr p ss ts)
        + Kc2 * ((∑ j ∈ Finset.range HvdH.D, paDRest Kb p ss ts j) + 1) := by ring
    _ ≤ (4096 * (Kc1 + Kc3)) * (ts.prod * p ^ 2)
        + (Kc2 * (HvdH.D * (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5))) + Kc2) * (ts.prod * p ^ 2) :=
        add_le_add h1 h2
    _ = (4096 * (Kc1 + Kc3)
        + (Kc2 * (HvdH.D * (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5))) + Kc2)) * (ts.prod * p ^ 2) := by
        ring
    _ ≤ K * (ts.prod * p ^ 2) := Nat.mul_le_mul_right _ hreq

/-- **Cost arithmetic of the `Ã` program.**  For every `Kb` and every triple of constants
`Kc1 Kc2 Kc3` (the constants produced by the prologue, iteration and epilogue lemmas) there is a
constant `K` such that, under `ResParams p α ss ts` and monotonicity of `Cm`, the total budget of
the program is dominated by the target cost:

`Kc1 * PASetupBr p ss ts + Kc2 * PAIterBrF Kb Cm p α ss ts + Kc3 * PAFinalBr p ss ts
  ≤ resCost K Cm p α ts = K*ts.prod*(√p+1)*α*(Cm (K*p) + p) + K*ts.prod*p² + K*ts.sum*(p+1)^K`

with `Kc1 ≤ K`, `Kc2 ≤ K`, `Kc3 ≤ K`, `Kb ≤ K`.  (`PAIterBrF` is the Finset form of `PAIterBr`, from
`Submission.Work.Resample.paProofs1`.)

Note that the constants `Kc1, Kc2, Kc3` multiply the *bracket* expressions, while `K` multiplies
`ts.prod`, `ts.sum`; so the comparison is term by term, using

* `ts.prod ≥ 2^(HvdH.D)` (each `t_i ≥ 2`), so `K*ts.prod*p²` absorbs every polynomial term in
  `HvdH.D` and `p` carrying a `ts.prod` factor (in particular `Kc2` times the applyAlong "layout"
  terms `64 * (A_j*B_{j+1}*(s_j+t_j+1)+1) * (…size+1) * (…size+1)`, whose size factors are at most
  `p*HvdH.D + 3` because `ts.prod < 2^(p*HvdH.D)`; summing over the `D` axes costs a constant
  factor) — so `K ≥ 64*HvdH.D²*Kc2` suffices for those;
* the `Cm`-terms: `Kc2 * Σ_{j<D} 64*(A_j*B_{j+1}/s_j)*(t_j+1)*(Kb*(√p+1)*(α+1)*(Cm (Kb*p)+p+1))`
  `≤ K*ts.prod*(√p+1)*α*(Cm (K*p)+p)` since `A_j*B_{j+1}*t_j/s_j = n_{j+1} ≤ ts.prod`,
  `Σ_j n_{j+1} ≤ HvdH.D*ts.prod`, `α+1 ≤ 2α` and `Cm (Kb*p) ≤ Cm (K*p)` — so
  `K ≥ 256*Kb*HvdH.D*Kc2` suffices;
* the `(p+1)^Kb`-type terms (`prep`, the drain in `clearRgn`, the product `pbW6`) are absorbed by
  `K*ts.sum*(p+1)^K` with `K ≥ 2*Kb + 4` and `ts.sum ≥ 2*HvdH.D`. -/
theorem paCostD (Kb Kc1 Kc2 Kc3 : ℕ) :
    ∃ K : ℕ, Kc1 ≤ K ∧ Kc2 ≤ K ∧ Kc3 ≤ K ∧ Kb ≤ K ∧
      ∀ (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ),
      HvdH.ResParams p α ss ts → Monotone Cm →
      Kc1 * Work.Resample.PASetupBr p ss ts + Kc2 * Work.Resample.PAIterBrF Kb Cm p α ss ts +
        Kc3 * Work.Resample.PAFinalBr p ss ts ≤ HvdH.resCost K Cm p α ts := by
  obtain ⟨hKc1, hKc2, hKc3, hKKb, hKz, hKcm, hKa1, hKA⟩ := paDK_facts Kb Kc1 Kc2 Kc3
  refine ⟨paDK Kb Kc1 Kc2 Kc3, hKc1, hKc2, hKc3, hKKb, ?_⟩
  intro Cm p α ss ts hRes hmon
  have hSplit : (∑ j ∈ Finset.range HvdH.D, PABr Kb Cm p α ss ts j)
      = 64 * (∑ j ∈ Finset.range HvdH.D, paDZ Kb p ts j)
        + 64 * (∑ j ∈ Finset.range HvdH.D, paDCm Kb Cm p α ss ts j)
        + (∑ j ∈ Finset.range HvdH.D, paDRest Kb p ss ts j) := by
    rw [Finset.sum_congr rfl (fun j _ => paDBr_eq Kb Cm p α ss ts j)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hIter : PAIterBrF Kb Cm p α ss ts
      = 64 * (∑ j ∈ Finset.range HvdH.D, paDZ Kb p ts j)
        + 64 * (∑ j ∈ Finset.range HvdH.D, paDCm Kb Cm p α ss ts j)
        + (∑ j ∈ Finset.range HvdH.D, paDRest Kb p ss ts j) + 1 := by
    unfold PAIterBrF
    rw [hSplit]
  have hZ := paDGroupZ (Kb := Kb) (Kc2 := Kc2) hRes hKKb hKz
  have hCm := paDGroupCm (Kb := Kb) (Kc2 := Kc2) hRes Cm hmon hKKb hKcm
  have hA := paDGroupA (Kb := Kb) (Kc1 := Kc1) (Kc2 := Kc2) (Kc3 := Kc3)
    hRes hKA (paDSetupBr hRes) (fun j hj => paDRest_body_le hRes Kb j hj)
  calc Kc1 * PASetupBr p ss ts + Kc2 * PAIterBrF Kb Cm p α ss ts + Kc3 * PAFinalBr p ss ts
      = (Kc1 * PASetupBr p ss ts
          + Kc2 * ((∑ j ∈ Finset.range HvdH.D, paDRest Kb p ss ts j) + 1)
          + Kc3 * PAFinalBr p ss ts)
        + Kc2 * (64 * (∑ j ∈ Finset.range HvdH.D, paDZ Kb p ts j))
        + Kc2 * (64 * (∑ j ∈ Finset.range HvdH.D, paDCm Kb Cm p α ss ts j)) := by
        rw [hIter]; ring
    _ ≤ paDK Kb Kc1 Kc2 Kc3 * (ts.prod * p ^ 2)
        + paDK Kb Kc1 Kc2 Kc3 * ts.sum * (p + 1) ^ (paDK Kb Kc1 Kc2 Kc3)
        + paDK Kb Kc1 Kc2 Kc3 * ts.prod * (Nat.sqrt p + 1) * α
            * (Cm (paDK Kb Kc1 Kc2 Kc3 * p) + p) :=
        add_le_add (add_le_add hA hZ) hCm
    _ = HvdH.resCost (paDK Kb Kc1 Kc2 Kc3) Cm p α ts := by
        unfold HvdH.resCost
        ring

end Work.Resample
