import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.ModelBDefs
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.ZeroDensity.Jutila.KappaMertensDefs

namespace Work.ZeroDensity.Jutila.BzCross
open Finset
open Work.ZeroDensity.Jutila

noncomputable section

def czTmax (w y : ℝ) (N q r : ℕ) : ℕ :=
  min (czT y N q) ⌊w / (((⌊y / (r:ℝ)⌋₊ : ℕ) : ℝ) + 1)⌋₊

def czInSum (w y : ℝ) (N q r : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
    (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ) * (t:ℝ) / kap t else 0)
      * ((⌊w/(t:ℝ)⌋₊ : ℝ) * czFII w y r t)

lemma czD_lt_iff {w y : ℝ} (hy : 0 ≤ y) {r t : ℕ} (hr : 1 ≤ r)
    (hA : 1 ≤ ⌊w/(t:ℝ)⌋₊) :
    (czD w y t < r) ↔ (⌊w/(t:ℝ)⌋₊ ≥ ⌊y/(r:ℝ)⌋₊ + 1) := by
  have hApos : (0:ℝ) < (⌊w/(t:ℝ)⌋₊ : ℝ) := by exact_mod_cast hA
  have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have e1 : czD w y t < r ↔ y / (⌊w/(t:ℝ)⌋₊ : ℝ) < (r:ℝ) := by
    unfold czD; rw [Nat.floor_lt (by positivity)]
  have e2 : y / (⌊w/(t:ℝ)⌋₊ : ℝ) < (r:ℝ) ↔ y / (r:ℝ) < (⌊w/(t:ℝ)⌋₊ : ℝ) := by
    rw [div_lt_iff₀ hApos, div_lt_iff₀ hrpos]; constructor <;> intro h <;> nlinarith
  have e3 : y / (r:ℝ) < (⌊w/(t:ℝ)⌋₊ : ℝ) ↔ ⌊y/(r:ℝ)⌋₊ < ⌊w/(t:ℝ)⌋₊ := by
    rw [Nat.floor_lt (by positivity)]
  rw [e1, e2, e3]; omega

lemma floor_le_iff_lt {w : ℝ} (hw : 0 ≤ w) (C t : ℕ) (ht : 1 ≤ t) :
    (⌊w/(t:ℝ)⌋₊ ≥ C+1) ↔ (t ≤ ⌊w/((C:ℝ)+1)⌋₊) := by
  have htR : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  have hC : (0:ℝ) < (C:ℝ) + 1 := by positivity
  have hfloor : ⌊((C:ℝ)+1)⌋₊ = C+1 := by
    rw [show ((C:ℝ)+1) = ((C+1:ℕ):ℝ) by push_cast; ring, Nat.floor_natCast]
  constructor
  · intro h
    have hcast : ((C:ℝ)+1) ≤ (⌊w/(t:ℝ)⌋₊ : ℝ) := by
      have hc : ((C+1 : ℕ) : ℝ) ≤ (⌊w/(t:ℝ)⌋₊ : ℝ) := by exact_mod_cast h
      push_cast at hc; linarith
    have h1 : ((C:ℝ)+1) ≤ w/(t:ℝ) := le_trans hcast (Nat.floor_le (by positivity))
    have h2 : (t:ℝ) ≤ w/((C:ℝ)+1) := by
      have := (le_div_iff₀ htR).mp h1
      rw [le_div_iff₀ hC]; nlinarith
    calc t = ⌊(t:ℝ)⌋₊ := (Nat.floor_natCast t).symm
      _ ≤ ⌊w/((C:ℝ)+1)⌋₊ := Nat.floor_mono h2
  · intro h
    have h1 : (t:ℝ) ≤ w/((C:ℝ)+1) := le_trans (by exact_mod_cast h) (Nat.floor_le (by positivity))
    have h2 : ((C:ℝ)+1) ≤ w/(t:ℝ) := by
      have := (le_div_iff₀ hC).mp h1
      rw [le_div_iff₀ htR]; nlinarith
    have h4 : ⌊((C:ℝ)+1)⌋₊ ≤ ⌊w/(t:ℝ)⌋₊ := Nat.floor_mono h2
    rw [hfloor] at h4
    exact_mod_cast h4

private lemma sum_Icc_succ_indicator (D R : ℕ) (g : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc (D+1) R, g r) = ∑ r ∈ Finset.Icc 1 R, (if D < r then g r else 0) := by
  rw [← Finset.sum_filter]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

private lemma sum_Icc_of_le_indicator {K T : ℕ} (hK : K ≤ T) (g : ℕ → ℝ) :
    (∑ t ∈ Finset.Icc 1 T, (if t ≤ K then g t else 0)) = ∑ t ∈ Finset.Icc 1 K, g t := by
  rw [← Finset.sum_filter]
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

lemma reindex_pt {w y : ℝ} (N : ℕ) (q r t : ℕ) (hw : 1 ≤ w) (hy : 0 ≤ y)
    (ht : 1 ≤ t) (hr : 1 ≤ r) (htT : t ≤ czT y N q) :
    (if czD w y t < r then
        czMM r t * ((r:ℝ)/kap r) * ((t:ℝ)/kap t) * ((⌊w/(t:ℝ)⌋₊:ℝ) * czFII w y r t)
      else 0)
    = (if t ≤ czTmax w y N q r then
        ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
        * ((if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ) * (t:ℝ)/kap t else 0)
            * ((⌊w/(t:ℝ)⌋₊:ℝ) * czFII w y r t)) else 0) := by
  have hpt : czMM r t * ((r:ℝ)/kap r) * ((t:ℝ)/kap t) * ((⌊w/(t:ℝ)⌋₊:ℝ) * czFII w y r t)
      = ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
        * ((if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ) * (t:ℝ)/kap t else 0)
            * ((⌊w/(t:ℝ)⌋₊:ℝ) * czFII w y r t)) := by
    unfold czMM
    by_cases h : Nat.Coprime r t
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  rcases Nat.eq_zero_or_pos (⌊w/(t:ℝ)⌋₊) with hA | hA
  · -- A_t = 0 : both sides zero
    have hA0 : ((⌊w/(t:ℝ)⌋₊ : ℕ) : ℝ) = 0 := by rw [hA, Nat.cast_zero]
    by_cases hcd : czD w y t < r <;> rw [hpt] <;> simp [hcd, hA0]
  · -- A_t >= 1
    have h1 := czD_lt_iff hy hr hA
    have h2 := floor_le_iff_lt (by linarith : (0:ℝ) ≤ w) (⌊y/(r:ℝ)⌋₊) t ht
    have hiff : czD w y t < r ↔ t ≤ czTmax w y N q r := by
      rw [h1, h2]
      simp only [czTmax]
      rw [le_min_iff]
      exact ⟨fun h => ⟨htT, h⟩, fun h => h.2⟩
    by_cases hcd : czD w y t < r
    · rw [if_pos hcd, if_pos (hiff.mp hcd), hpt]
    · rw [if_neg hcd, if_neg (fun h => hcd (hiff.mpr h))]

lemma czRII_reindex {w y : ℝ} (N : ℕ) (hw : 1 ≤ w) (hy : 0 ≤ y) :
    czRII w y N = ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ r ∈ Finset.Icc 1 (czR w N q),
      ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r) * czInSum w y N q r := by
  unfold czRII czInSum
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.sum_congr rfl (fun t _ => sum_Icc_succ_indicator (czD w y t) (czR w N q)
        (fun r => czMM r t * ((r:ℝ)/kap r) * ((t:ℝ)/kap t) * ((⌊w/(t:ℝ)⌋₊:ℝ) * czFII w y r t)))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [Finset.mem_Icc] at hr
  have hK : czTmax w y N q r ≤ czT y N q := by simp only [czTmax]; exact min_le_left _ _
  rw [Finset.sum_congr rfl (fun t ht => reindex_pt N q r t hw hy
        (Finset.mem_Icc.mp ht).1 hr.1 (Finset.mem_Icc.mp ht).2)]
  have hfac : ∀ t : ℕ, (if t ≤ czTmax w y N q r then
        ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
          * ((if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ) * (t:ℝ)/kap t else 0)
              * ((⌊w/(t:ℝ)⌋₊:ℝ) * czFII w y r t)) else 0)
      = ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
        * (if t ≤ czTmax w y N q r then
            (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ) * (t:ℝ)/kap t else 0)
              * ((⌊w/(t:ℝ)⌋₊:ℝ) * czFII w y r t) else 0) := by
    intro t; by_cases h : t ≤ czTmax w y N q r <;> simp [h]
  rw [Finset.sum_congr rfl (fun t _ => hfac t), ← Finset.mul_sum]
  congr 1
  exact sum_Icc_of_le_indicator hK _

end
end Work.ZeroDensity.Jutila.BzCross
