import Mathlib
import Submission.Szemeredi.Removal.GenCount
import Submission.Commons.Analysis.Real.bterm_arith

/-!
# The `b`-term bound of the generalized counting lemma

This file proves the estimate for the `b`-term contribution in the induction step of
Tao's `gencount` (arXiv:math/0503572, §4): after discarding the top-order factors and
applying Fubini, the weighted Cauchy–Schwarz inequality bounds it by the square roots of
the weighted `L²` norm of `b_{g₀}` (controlled by (H3)) and of the counting functional of
the doubled bundle (controlled by the induction hypothesis).
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]

namespace SigAlg

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

/-- The average of the absolute value dominates the absolute value of the average. -/
theorem abs_avg_le_avg_abs (f : Ω → ℝ) : |avg f| ≤ avg (fun x => |f x|) := by
  have h1 : avg (fun x => |f x| - f x) = avg (fun x => |f x|) - avg f := by
    unfold avg
    rw [Finset.sum_sub_distrib]
    ring
  have h2 : avg (fun x => |f x| + f x) = avg (fun x => |f x|) + avg f := by
    rw [avg_add]
  have h3 : 0 ≤ avg (fun x => |f x| - f x) := avg_nonneg (fun x => sub_nonneg.mpr (le_abs_self _))
  have h4 : 0 ≤ avg (fun x => |f x| + f x) :=
    avg_nonneg (fun x => by have := neg_le_abs (f x); linarith)
  rw [h1] at h3
  rw [h2] at h4
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end SigAlg


/-- `√(a + b) ≤ √a + √b`. -/
theorem sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h : (Real.sqrt a + Real.sqrt b) ^ 2 = a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
  rw [h]
  have := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  linarith

/-- **The `Rg`-aware arithmetic of the `b`-term.**  This is `bterm_arith` with the
square-root of `Rg` inserted in the three numerical keys, which retains the
`Rg^{-1/2}` damping of the weighted `L²` bound; it is derived from `bterm_arith` by
substituting `AvgB := Rg * AvgB`, `ηB := ηB * √Rg`, `CB := CB * √Rg`, `Rg := 1`. -/
theorem bterm_arithR {AvgB AvgLow CntDbl PGlt PGgt P ρ Rg η₁ η₂ C₁ C₂ KK L₂ ηB CB : ℝ} {N : ℕ}
    (hRg : 1 ≤ Rg) (hρ : 0 ≤ ρ) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hAvgB0 : 0 ≤ AvgB) (hAvgLow0 : 0 ≤ AvgLow) (hCntDbl0 : 0 ≤ CntDbl)
    (hPGlt0 : 0 ≤ PGlt) (hPGgt0 : 0 ≤ PGgt) (hP0 : 0 ≤ P)
    (hPGlt1 : PGlt ≤ 1) (hPGgt1 : PGgt ≤ 1)
    (hH3 : AvgB ≤ (1 / Rg) * AvgLow)
    (hIHLow : AvgLow ≤ (1 + η₁) * PGlt + C₁ * ρ)
    (hIHDbl : CntDbl ≤ (1 + η₂) * (PGlt * PGgt ^ 2) + C₂ * ρ)
    (hprod : PGlt * PGgt ≤ KK * P)
    (hP : (1 / L₂) ^ N ≤ P)
    (hηB0 : 0 ≤ ηB)
    (hkey1 : Real.sqrt (1 + η₁) * Real.sqrt (1 + η₂) * KK ≤ (ηB / 2) * Real.sqrt Rg)
    (hkey2 : Real.sqrt ρ * (Real.sqrt (1 + η₁) * Real.sqrt C₂ + Real.sqrt (1 + η₂) * Real.sqrt C₁)
        ≤ (ηB / 2) * Real.sqrt Rg * (1 / L₂) ^ N)
    (hkey3 : Real.sqrt (C₁ * C₂) ≤ (CB / 2) * Real.sqrt Rg) :
    Real.sqrt AvgB * Real.sqrt CntDbl ≤ ηB * P + CB * ρ := by
  have hRg0 : (0 : ℝ) < Rg := by linarith
  have hsRg : (0 : ℝ) < Real.sqrt Rg := Real.sqrt_pos.mpr hRg0
  have hRgnn : (0 : ℝ) ≤ Rg := le_of_lt hRg0
  have hsRgnn : (0 : ℝ) ≤ Real.sqrt Rg := le_of_lt hsRg
  have hAvgB' : (0 : ℝ) ≤ Rg * AvgB := mul_nonneg hRgnn hAvgB0
  have hH3' : Rg * AvgB ≤ (1 / (1 : ℝ)) * AvgLow := by
    have h1 : Rg * ((1 / Rg) * AvgLow) = AvgLow := by
      rw [← mul_assoc, mul_one_div, div_self (ne_of_gt hRg0), one_mul]
    calc Rg * AvgB ≤ Rg * ((1 / Rg) * AvgLow) := mul_le_mul_of_nonneg_left hH3 hRgnn
      _ = (1 / (1 : ℝ)) * AvgLow := by rw [h1]; ring
  have hkey1' : Real.sqrt (1 + η₁) * Real.sqrt (1 + η₂) * KK ≤ (ηB * Real.sqrt Rg) / 2 := by
    linarith [hkey1]
  have hkey2' : Real.sqrt ρ * (Real.sqrt (1 + η₁) * Real.sqrt C₂ + Real.sqrt (1 + η₂) * Real.sqrt C₁)
      ≤ ((ηB * Real.sqrt Rg) / 2) * (1 / L₂) ^ N := by
    nlinarith [hkey2]
  have hkey3' : Real.sqrt (C₁ * C₂) ≤ (CB * Real.sqrt Rg) / 2 := by
    nlinarith [hkey3]
  have h := Commons.Analysis.Real.bterm_arith (AvgB := Rg * AvgB) (AvgLow := AvgLow)
    (CntDbl := CntDbl) (PGlt := PGlt) (PGgt := PGgt) (P := P) (ρ := ρ) (Rg := 1)
    (η₁ := η₁) (η₂ := η₂) (C₁ := C₁) (C₂ := C₂) (KK := KK) (L₂ := L₂)
    (ηB := ηB * Real.sqrt Rg) (CB := CB * Real.sqrt Rg) (N := N)
    (by norm_num) hρ hη₁ hη₂ hC₁ hC₂ hAvgB' hAvgLow0 hCntDbl0 hPGlt0 hPGgt0 hP0 hPGlt1 hPGgt1
    hH3' hIHLow hIHDbl hprod hP (by positivity) hkey1' hkey2' hkey3'
  have hsqrt : Real.sqrt (Rg * AvgB) = Real.sqrt Rg * Real.sqrt AvgB := Real.sqrt_mul hRgnn AvgB
  rw [hsqrt] at h
  have hfinal : Real.sqrt Rg * (Real.sqrt AvgB * Real.sqrt CntDbl)
      ≤ Real.sqrt Rg * (ηB * P + CB * ρ) := by
    have he : Real.sqrt Rg * Real.sqrt AvgB * Real.sqrt CntDbl
        = Real.sqrt Rg * (Real.sqrt AvgB * Real.sqrt CntDbl) := by ring
    rw [he] at h
    calc Real.sqrt Rg * (Real.sqrt AvgB * Real.sqrt CntDbl)
        ≤ (ηB * Real.sqrt Rg) * P + (CB * Real.sqrt Rg) * ρ := h
      _ = Real.sqrt Rg * (ηB * P + CB * ρ) := by ring
  exact le_of_mul_le_mul_left hfinal hsRg

/-- **The `b`-term bound.** -/
theorem bterm_bound {Hd : Finset (Finset ι)} {A : Finset ι → Finset (Pt V)}
    {B B' : ℕ → Finset ι → SigAlg (Pt V)}
    {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {G : Finset (Finset κ)}
    (hB : IsBundle Hd π G) {pg Rg : Finset κ → ℝ} {ρ : ℝ}
    {g₀ : Finset κ} (hg₀ : g₀ ∈ G) (d' : ℕ) (hd' : 1 ≤ d') (hg₀card : g₀.card = d')
    (hGCH : GCHyp (V := V) π G (AgOf (V := V) A π G hB.inj) pg Rg
      (bgOf (V := V) B B' A π G hB.inj) (cgOf (V := V) B' A π G hB.inj) ρ)
    (η₁ η₂ C₁ C₂ KK L₂ ηB CB : ℝ) (N : ℕ)
    (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hρ : 0 ≤ ρ)
    (hKK : 0 ≤ KK) (hL₂ : 1 ≤ L₂) (hRg1 : 1 ≤ Rg g₀) (hηB0 : 0 ≤ ηB)
    (hpg0 : ∀ g ∈ G, 0 ≤ pg g) (hpg1 : ∀ g ∈ G, pg g ≤ 1)
    (hIHglt : Cnt π (Glt G g₀) (AgOf (V := V) A π G hB.inj)
        ≤ (1 + η₁) * (∏ h ∈ Glt G g₀, pg h) + C₁ * ρ)
    (hIHdbl : Cnt (dblπ π g₀) (dblG G g₀ d') (AgDbl (V := V) A π G g₀ d' hB.inj)
        ≤ (1 + η₂) * ((∏ h ∈ Glt G g₀, pg h) * (∏ h ∈ Ggt G g₀ d', pg h) ^ 2) + C₂ * ρ)
    (hprod : (∏ h ∈ Glt G g₀, pg h) * (∏ h ∈ Ggt G g₀ d', pg h)
        ≤ KK * (∏ g ∈ G, pg g))
    (hP : (1 / L₂) ^ N ≤ ∏ g ∈ G, pg g)
    (hkey1 : Real.sqrt (1 + η₁) * Real.sqrt (1 + η₂) * KK ≤ (ηB / 2) * Real.sqrt (Rg g₀))
    (hkey2 : Real.sqrt ρ * (Real.sqrt (1 + η₁) * Real.sqrt C₂
        + Real.sqrt (1 + η₂) * Real.sqrt C₁) ≤ (ηB / 2) * Real.sqrt (Rg g₀) * (1 / L₂) ^ N)
    (hkey3 : Real.sqrt (C₁ * C₂) ≤ (CB / 2) * Real.sqrt (Rg g₀)) :
    |avg (fun v : BPt V π => bgOf (V := V) B B' A π G hB.inj g₀ v
        * ∏ g ∈ G.erase g₀, indicator (AgOf (V := V) A π G hB.inj g) v)|
      ≤ ηB * (∏ g ∈ G, pg g) + CB * ρ := by
  classical
  have hXw0 : ∀ w : W1 (V := V) π g₀, 0 ≤ Xw (V := V) A π G g₀ hB.inj w := by
    intro w
    rw [Xw]
    exact Finset.prod_nonneg (fun h _ => by
      by_cases hh : combine (V := V) π g₀ w (Classical.arbitrary (W2 (V := V) π g₀))
          ∈ AgOf (V := V) A π G hB.inj h <;> simp [indicator, hh])
  -- the two Cauchy–Schwarz factors, as functions of `w`
  have hstep : |avg (fun v : BPt V π => bgOf (V := V) B B' A π G hB.inj g₀ v
        * ∏ g ∈ G.erase g₀, indicator (AgOf (V := V) A π G hB.inj g) v)|
      ≤ Real.sqrt (avg (fun w : W1 (V := V) π g₀ => Xw (V := V) A π G g₀ hB.inj w
            * (betaOf (V := V) B B' A (g₀.image π)
                (piCongrImage (V := V) π g₀ (hB.inj g₀ hg₀) w)) ^ 2))
        * Real.sqrt (avg (fun w : W1 (V := V) π g₀ => Xw (V := V) A π G g₀ hB.inj w
            * (avg (fun u : W2 (V := V) π g₀ =>
                Pw (V := V) A π G g₀ d' hB.inj w u)) ^ 2)) := by
    have hpt : ∀ v : BPt V π,
        |bgOf (V := V) B B' A π G hB.inj g₀ v
          * ∏ g ∈ G.erase g₀, indicator (AgOf (V := V) A π G hB.inj g) v|
        ≤ |bgOf (V := V) B B' A π G hB.inj g₀ v|
          * ∏ h ∈ Glt G g₀ ∪ Ggt G g₀ d', indicator (AgOf (V := V) A π G hB.inj h) v := by
      intro v
      have hW0 : 0 ≤ ∏ g ∈ G.erase g₀, indicator (AgOf (V := V) A π G hB.inj g) v :=
        Finset.prod_nonneg (fun g _ => by
          by_cases hh : v ∈ AgOf (V := V) A π G hB.inj g <;> simp [indicator, hh])
      rw [abs_mul, abs_of_nonneg hW0]
      exact mul_le_mul_of_nonneg_left
        (prod_erase_le_Glt_Ggt d' hd' G hg₀ hg₀card _
          (fun g => by by_cases hh : v ∈ AgOf (V := V) A π G hB.inj g <;>
            simp [indicator, hh])
          (fun g => by by_cases hh : v ∈ AgOf (V := V) A π G hB.inj g <;>
            simp [indicator, hh]))
        (abs_nonneg _)
    calc |avg (fun v : BPt V π => bgOf (V := V) B B' A π G hB.inj g₀ v
          * ∏ g ∈ G.erase g₀, indicator (AgOf (V := V) A π G hB.inj g) v)|
        ≤ avg (fun v : BPt V π => |bgOf (V := V) B B' A π G hB.inj g₀ v
            * ∏ g ∈ G.erase g₀, indicator (AgOf (V := V) A π G hB.inj g) v|) :=
          SigAlg.abs_avg_le_avg_abs _
      _ ≤ avg (fun v : BPt V π => |bgOf (V := V) B B' A π G hB.inj g₀ v|
            * ∏ h ∈ Glt G g₀ ∪ Ggt G g₀ d', indicator (AgOf (V := V) A π G hB.inj h) v) :=
          avg_le_avg hpt
      _ = avg (fun w : W1 (V := V) π g₀ =>
            (|betaOf (V := V) B B' A (g₀.image π)
                (piCongrImage (V := V) π g₀ (hB.inj g₀ hg₀) w)|
              * Xw (V := V) A π G g₀ hB.inj w)
            * avg (fun u : W2 (V := V) π g₀ =>
                Pw (V := V) A π G g₀ d' hB.inj w u)) :=
          bterm_fubini (V := V) hB hg₀ d' hd'
      _ = avg (fun w : W1 (V := V) π g₀ => Xw (V := V) A π G g₀ hB.inj w
            * |betaOf (V := V) B B' A (g₀.image π)
                (piCongrImage (V := V) π g₀ (hB.inj g₀ hg₀) w)|
            * avg (fun u : W2 (V := V) π g₀ =>
                Pw (V := V) A π G g₀ d' hB.inj w u)) := by
          congr 1
          funext w
          ring
      _ ≤ |avg (fun w : W1 (V := V) π g₀ => Xw (V := V) A π G g₀ hB.inj w
            * |betaOf (V := V) B B' A (g₀.image π)
                (piCongrImage (V := V) π g₀ (hB.inj g₀ hg₀) w)|
            * avg (fun u : W2 (V := V) π g₀ =>
                Pw (V := V) A π G g₀ d' hB.inj w u))| := le_abs_self _
      _ ≤ Real.sqrt (avg (fun w : W1 (V := V) π g₀ => Xw (V := V) A π G g₀ hB.inj w
            * (betaOf (V := V) B B' A (g₀.image π)
                (piCongrImage (V := V) π g₀ (hB.inj g₀ hg₀) w)) ^ 2))
          * Real.sqrt (avg (fun w : W1 (V := V) π g₀ => Xw (V := V) A π G g₀ hB.inj w
            * (avg (fun u : W2 (V := V) π g₀ =>
                Pw (V := V) A π G g₀ d' hB.inj w u)) ^ 2)) :=
          bterm_cauchy (V := V) A π G hB.inj
            (fun w => betaOf (V := V) B B' A (g₀.image π)
              (piCongrImage (V := V) π g₀ (hB.inj g₀ hg₀) w))
            (fun w => avg (fun u : W2 (V := V) π g₀ =>
              Pw (V := V) A π G g₀ d' hB.inj w u)) hXw0
  rw [avg_Xw_mul_sq (V := V) hB hg₀, avg_Xw_Yw_sq (V := V) hB hg₀ hd' hg₀card] at hstep
  -- (H3) and the two induction hypotheses
  have hAVB : avg (fun v : BPt V π => (bgOf (V := V) B B' A π G hB.inj g₀ v) ^ 2
        * indicator (lowSetAll π (AgOf (V := V) A π G hB.inj) g₀) v)
      ≤ (1 / Rg g₀) * avg (indicator (lowSetAll π (AgOf (V := V) A π G hB.inj) g₀)) :=
    hGCH.h3 g₀ hg₀
  have hAVL : avg (indicator (lowSetAll π (AgOf (V := V) A π G hB.inj) g₀))
      ≤ (1 + η₁) * (∏ h ∈ Glt G g₀, pg h) + C₁ * ρ := by
    rw [← cnt_Glt_eq (V := V) hB hg₀]
    exact hIHglt
  have hPGlt0 : 0 ≤ ∏ h ∈ Glt G g₀, pg h := Finset.prod_nonneg (fun h hh => hpg0 h (mem_Glt.mp hh).1)
  have hPGgt0 : 0 ≤ ∏ h ∈ Ggt G g₀ d', pg h :=
    Finset.prod_nonneg (fun h hh => hpg0 h (mem_Ggt.mp hh).1)
  have hPGlt1 : (∏ h ∈ Glt G g₀, pg h) ≤ 1 :=
    Finset.prod_le_one (fun h hh => hpg0 h (mem_Glt.mp hh).1)
      (fun h hh => hpg1 h (mem_Glt.mp hh).1)
  have hPGgt1 : (∏ h ∈ Ggt G g₀ d', pg h) ≤ 1 :=
    Finset.prod_le_one (fun h hh => hpg0 h (mem_Ggt.mp hh).1)
      (fun h hh => hpg1 h (mem_Ggt.mp hh).1)
  have hP0 : 0 ≤ ∏ g ∈ G, pg g := Finset.prod_nonneg (fun g hg => hpg0 g hg)
  have hAVB0 : 0 ≤ avg (fun v : BPt V π => (bgOf (V := V) B B' A π G hB.inj g₀ v) ^ 2
      * indicator (lowSetAll π (AgOf (V := V) A π G hB.inj) g₀) v) :=
    avg_nonneg (fun v => mul_nonneg (sq_nonneg _) (by
      by_cases hh : v ∈ lowSetAll π (AgOf (V := V) A π G hB.inj) g₀ <;>
        simp [indicator, hh]))
  have hAVL0 : 0 ≤ avg (indicator (lowSetAll π (AgOf (V := V) A π G hB.inj) g₀)) :=
    avg_nonneg (fun v => by
      by_cases hh : v ∈ lowSetAll π (AgOf (V := V) A π G hB.inj) g₀ <;>
        simp [indicator, hh])
  have hCD0 : 0 ≤ Cnt (dblπ π g₀) (dblG G g₀ d') (AgDbl (V := V) A π G g₀ d' hB.inj) := by
    rw [Cnt]
    refine avg_nonneg (fun v => Finset.prod_nonneg (fun gg _ => ?_))
    by_cases hh : v ∈ AgDbl (V := V) A π G g₀ d' hB.inj gg <;> simp [indicator, hh]
  exact le_trans hstep (bterm_arithR (AvgB := avg (fun v : BPt V π =>
        (bgOf (V := V) B B' A π G hB.inj g₀ v) ^ 2
          * indicator (lowSetAll π (AgOf (V := V) A π G hB.inj) g₀) v))
      (AvgLow := avg (indicator (lowSetAll π (AgOf (V := V) A π G hB.inj) g₀)))
      (CntDbl := Cnt (dblπ π g₀) (dblG G g₀ d') (AgDbl (V := V) A π G g₀ d' hB.inj))
      (PGlt := ∏ h ∈ Glt G g₀, pg h) (PGgt := ∏ h ∈ Ggt G g₀ d', pg h)
      (P := ∏ g ∈ G, pg g) (Rg := Rg g₀)
      hRg1 hρ hη₁ hη₂ hC₁ hC₂ hAVB0 hAVL0 hCD0 hPGlt0 hPGgt0 hP0 hPGlt1 hPGgt1
      hAVB hAVL hIHdbl hprod hP hηB0 hkey1 hkey2 hkey3)

end Szemeredi.Removal
