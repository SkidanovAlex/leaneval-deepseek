import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.crt.Pinv_spec
import Submission.Work.DFT.phaseLin
import Submission.Work.Main.chunks.sum_cyclic_eq_hcoeff
import Submission.Work.Main.conv.sum_convC_reindex

set_option autoImplicit false

open Work.Main

namespace Work.Main.conv

lemma vget_flatv {ss : List ℕ} {b N y l : ℕ} (hl : l < ss.prod) :
    HvdH.vget (flatv b N ss y) l = (pchunk y b N (Pinv ss l) : ℂ) / 2 ^ b := by
  rw [HvdH.vget, dite_eq_left hl]
  rfl

lemma inv_pow_mul_inv_pow (k : ℕ) :
    (1 / (2 : ℂ) ^ k) * (1 / (2 : ℂ) ^ k) = 1 / (2 : ℂ) ^ (2 * k) := by
  rw [div_mul_div_comm, one_mul, ← pow_add, show k + k = 2 * k by omega]

theorem hcoeff_eq_convC (hDFT : HvdH.DFTMathProp) {ss : List ℕ} (hcop : ss.Pairwise Nat.Coprime)
    (hpos : ∀ s ∈ ss, 0 < s) {x y b N q : ℕ} (hSN : 2 * N - 1 ≤ ss.prod) (hq : q < ss.prod) :
    (hcoeff x y b N (Pinv ss q) : ℂ) =
      (2 : ℂ) ^ (2 * b) * (ss.prod : ℂ) * HvdH.convC ss (flatv b N ss x) (flatv b N ss y) ⟨q, hq⟩ := by
  obtain ⟨hmlt, hmq⟩ := Work.Main.crt.Pinv_spec hcop hpos hq
  have hPpos : 0 < ss.prod := List.prod_pos hpos
  have key : ∀ (j : Fin ss.prod) (m : ℕ), Pcr ss m = ↑j → m < ss.prod →
      (hcoeff x y b N m : ℂ) = (2 : ℂ) ^ (2 * b) * (ss.prod : ℂ) *
        HvdH.convC ss (flatv b N ss x) (flatv b N ss y) j := by
    intro j m hjm hm
    rw [HvdH.convC]
    rw [← hjm]
    have hsum : (∑ k : Fin ss.prod,
          flatv b N ss x k * HvdH.vget (flatv b N ss y) (HvdH.subIdx ss (Pcr ss m) ↑k))
        = (1 / (2 : ℂ) ^ b) * (1 / (2 : ℂ) ^ b) * (hcoeff x y b N m : ℂ) := by
      have hterm : ∀ k : Fin ss.prod,
          flatv b N ss x k * HvdH.vget (flatv b N ss y) (HvdH.subIdx ss (Pcr ss m) ↑k)
            = ((pchunk x b N (Pinv ss k) : ℂ) *
                (pchunk y b N (Pinv ss (HvdH.subIdx ss (Pcr ss m) ↑k)) : ℂ))
              * ((1 / (2 : ℂ) ^ b) * (1 / (2 : ℂ) ^ b)) := by
        intro k
        rw [vget_flatv (ss := ss) (b := b) (N := N) (y := y)
          (l := HvdH.subIdx ss (Pcr ss m) ↑k) (Work.DFT.subIdx_lt ss hpos (Pcr ss m) ↑k)]
        simp only [flatv]
        ring
      calc (∑ k : Fin ss.prod, flatv b N ss x k * HvdH.vget (flatv b N ss y) (HvdH.subIdx ss (Pcr ss m) ↑k))
          = ∑ k : Fin ss.prod, ((pchunk x b N (Pinv ss k) : ℂ) *
                (pchunk y b N (Pinv ss (HvdH.subIdx ss (Pcr ss m) ↑k)) : ℂ))
              * ((1 / (2 : ℂ) ^ b) * (1 / (2 : ℂ) ^ b)) :=
            Finset.sum_congr rfl (fun k _ => hterm k)
        _ = (∑ k : Fin ss.prod, (pchunk x b N (Pinv ss k) : ℂ) *
                (pchunk y b N (Pinv ss (HvdH.subIdx ss (Pcr ss m) ↑k)) : ℂ))
              * ((1 / (2 : ℂ) ^ b) * (1 / (2 : ℂ) ^ b)) := (Finset.sum_mul _ _ _).symm
        _ = (∑ i ∈ Finset.range ss.prod, (pchunk x b N i : ℂ) *
                (pchunk y b N ((m + ss.prod - i) % ss.prod) : ℂ))
              * ((1 / (2 : ℂ) ^ b) * (1 / (2 : ℂ) ^ b)) := by
            rw [sum_convC_reindex (ss := ss) hcop hpos hm (fun i => (pchunk x b N i : ℂ))
              (fun i => (pchunk y b N i : ℂ))]
        _ = ((∑ i ∈ Finset.range ss.prod,
                pchunk x b N i * pchunk y b N ((m + ss.prod - i) % ss.prod) : ℕ) : ℂ)
              * ((1 / (2 : ℂ) ^ b) * (1 / (2 : ℂ) ^ b)) := by
            simp only [← Nat.cast_mul, ← Nat.cast_sum]
        _ = (hcoeff x y b N m : ℂ) * ((1 / (2 : ℂ) ^ b) * (1 / (2 : ℂ) ^ b)) := by
            rw [Work.Main.chunks.sum_cyclic_eq_hcoeff hSN hm]
        _ = (1 / (2 : ℂ) ^ b) * (1 / (2 : ℂ) ^ b) * (hcoeff x y b N m : ℂ) := by ring
    rw [hsum, inv_pow_mul_inv_pow]
    have hA : (2 : ℂ) ^ (2 * b) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hP : (ss.prod : ℂ) ≠ 0 := by
      exact_mod_cast hPpos.ne'
    field_simp
  exact key ⟨q, hq⟩ (Pinv ss q) hmq hmlt

end Work.Main.conv
