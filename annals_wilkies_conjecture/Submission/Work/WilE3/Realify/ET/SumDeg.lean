/-
  annals_wilkies_conjecture, AREA E3, `Realify` (`ET`): CLEAN copy of the total-degree estimate
  `sum_deg_le`, routed through the proved `Work.WilE3.Realify.ET.totalDegree_realify_le` instead of
  the unproved `Work.WilE3.Realify.totalDegree_realify_le`.
-/
import Mathlib
import Submission.Work.WilE3.Realify.Defs
import Submission.Work.WilE3.Realify.MultiplicityBound_proved
import Submission.Work.WilE3.Realify.ET.totalDegree_realify_le

namespace Work.WilE3.Realify.ET

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical Topology Filter
open WilkiesDesign.E

variable {k r : ℕ}

theorem sum_deg_le (c : EAChain k r) (cc e : Fin r → ℝ) (N N₀ F : ℕ) (f g : Fin k → EAPoly k r)
    (a b : ℝ) (hkF : k ≤ F) (hrF : r ≤ F) (hN : N ≤ N₀ + 1)
    (hf : ∀ i, (f i).totalDegree ≤ N₀) (hg : ∀ i, (g i).totalDegree ≤ N₀) :
    ∑ i : Fin (k + k), atomDeg (realSys c cc e N f g a b i)
      + ∑ j : Fin (r + r), ((mkChain c cc).R j).totalDegree
      ≤ 6 * F * (F + 1) * N₀ + (12 * F * F + 5 * F) := by
  have hb : 3 * r * (N + 1) ≤ 3 * F * (N₀ + 2) := by
    have h4 : N + 1 ≤ N₀ + 2 := by omega
    calc 3 * r * (N + 1) = 3 * (r * (N + 1)) := by ring
      _ ≤ 3 * (F * (N₀ + 2)) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul hrF h4)
      _ = 3 * F * (N₀ + 2) := by ring
  have hper : ∀ i : Fin k, atomDeg (realSys c cc e N f g a b (Fin.castAdd k i))
      ≤ 3 * N₀ + 3 * F * (N₀ + 2) + 1 := by
    intro i
    have h1 : (realifyRe N e (f i)).totalDegree
        ≤ 3 * (f i).totalDegree + 3 * F * (N₀ + 2) :=
      le_trans (totalDegree_realify_le N e (f i)).1 (Nat.add_le_add_left hb _)
    have h2 : (realifyRe N e (g i)).totalDegree
        ≤ 3 * (g i).totalDegree + 3 * F * (N₀ + 2) :=
      le_trans (totalDegree_realify_le N e (g i)).1 (Nat.add_le_add_left hb _)
    have h3 : (realifyIm N e (g i)).totalDegree
        ≤ 3 * (g i).totalDegree + 3 * F * (N₀ + 2) :=
      le_trans (totalDegree_realify_le N e (g i)).2 (Nat.add_le_add_left hb _)
    have h1' : 3 * (f i).totalDegree ≤ 3 * N₀ := Nat.mul_le_mul_left 3 (hf i)
    have h2' : 3 * (g i).totalDegree ≤ 3 * N₀ := Nat.mul_le_mul_left 3 (hg i)
    have hA : (realifyRe N e (f i)).totalDegree ≤ 3 * N₀ + 3 * F * (N₀ + 2) := by omega
    have hB : (MvPolynomial.C a * realifyRe N e (g i)).totalDegree
        ≤ 3 * N₀ + 3 * F * (N₀ + 2) := by
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      omega
    have hC : (MvPolynomial.C (-b) * realifyIm N e (g i)).totalDegree
        ≤ 3 * N₀ + 3 * F * (N₀ + 2) := by
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      omega
    have hsum : (realifyRe N e (f i) + MvPolynomial.C a * realifyRe N e (g i)
        + MvPolynomial.C (-b) * realifyIm N e (g i)).totalDegree
        ≤ 3 * N₀ + 3 * F * (N₀ + 2) := by
      refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ hC)
      exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le hA hB)
    rw [realSys_castAdd]
    have heq : atomDeg (realifyRe N e (f i) + MvPolynomial.C a * realifyRe N e (g i)
        + MvPolynomial.C (-b) * realifyIm N e (g i))
        = (realifyRe N e (f i) + MvPolynomial.C a * realifyRe N e (g i)
          + MvPolynomial.C (-b) * realifyIm N e (g i)).totalDegree + 1 := rfl
    rw [heq]
    omega
  have hper' : ∀ i : Fin k, atomDeg (realSys c cc e N f g a b (Fin.natAdd k i))
      ≤ 3 * N₀ + 3 * F * (N₀ + 2) + 1 := by
    intro i
    have h1 : (realifyIm N e (f i)).totalDegree
        ≤ 3 * (f i).totalDegree + 3 * F * (N₀ + 2) :=
      le_trans (totalDegree_realify_le N e (f i)).2 (Nat.add_le_add_left hb _)
    have h2 : (realifyIm N e (g i)).totalDegree
        ≤ 3 * (g i).totalDegree + 3 * F * (N₀ + 2) :=
      le_trans (totalDegree_realify_le N e (g i)).2 (Nat.add_le_add_left hb _)
    have h3 : (realifyRe N e (g i)).totalDegree
        ≤ 3 * (g i).totalDegree + 3 * F * (N₀ + 2) :=
      le_trans (totalDegree_realify_le N e (g i)).1 (Nat.add_le_add_left hb _)
    have h1' : 3 * (f i).totalDegree ≤ 3 * N₀ := Nat.mul_le_mul_left 3 (hf i)
    have h2' : 3 * (g i).totalDegree ≤ 3 * N₀ := Nat.mul_le_mul_left 3 (hg i)
    have hA : (realifyIm N e (f i)).totalDegree ≤ 3 * N₀ + 3 * F * (N₀ + 2) := by omega
    have hB : (MvPolynomial.C a * realifyIm N e (g i)).totalDegree
        ≤ 3 * N₀ + 3 * F * (N₀ + 2) := by
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      omega
    have hC : (MvPolynomial.C b * realifyRe N e (g i)).totalDegree
        ≤ 3 * N₀ + 3 * F * (N₀ + 2) := by
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      omega
    have hsum : (realifyIm N e (f i) + MvPolynomial.C a * realifyIm N e (g i)
        + MvPolynomial.C b * realifyRe N e (g i)).totalDegree
        ≤ 3 * N₀ + 3 * F * (N₀ + 2) := by
      refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ hC)
      exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le hA hB)
    rw [realSys_natAdd]
    have heq : atomDeg (realifyIm N e (f i) + MvPolynomial.C a * realifyIm N e (g i)
        + MvPolynomial.C b * realifyRe N e (g i))
        = (realifyIm N e (f i) + MvPolynomial.C a * realifyIm N e (g i)
          + MvPolynomial.C b * realifyRe N e (g i)).totalDegree + 1 := rfl
    rw [heq]
    omega
  have hsumA : ∑ i : Fin k, atomDeg (realSys c cc e N f g a b (Fin.castAdd k i))
      ≤ k * (3 * N₀ + 3 * F * (N₀ + 2) + 1) := by
    calc ∑ i : Fin k, atomDeg (realSys c cc e N f g a b (Fin.castAdd k i))
        ≤ ∑ _i : Fin k, (3 * N₀ + 3 * F * (N₀ + 2) + 1) :=
          Finset.sum_le_sum fun i _ => hper i
      _ = k * (3 * N₀ + 3 * F * (N₀ + 2) + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hsumB : ∑ i : Fin k, atomDeg (realSys c cc e N f g a b (Fin.natAdd k i))
      ≤ k * (3 * N₀ + 3 * F * (N₀ + 2) + 1) := by
    calc ∑ i : Fin k, atomDeg (realSys c cc e N f g a b (Fin.natAdd k i))
        ≤ ∑ _i : Fin k, (3 * N₀ + 3 * F * (N₀ + 2) + 1) :=
          Finset.sum_le_sum fun i _ => hper' i
      _ = k * (3 * N₀ + 3 * F * (N₀ + 2) + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hsum : ∑ i : Fin (k + k), atomDeg (realSys c cc e N f g a b i)
      ≤ 2 * k * (3 * N₀ + 3 * F * (N₀ + 2) + 1) := by
    rw [Fin.sum_univ_add]
    calc (∑ i : Fin k, atomDeg (realSys c cc e N f g a b (Fin.castAdd k i)))
          + (∑ i : Fin k, atomDeg (realSys c cc e N f g a b (Fin.natAdd k i)))
        ≤ k * (3 * N₀ + 3 * F * (N₀ + 2) + 1) + k * (3 * N₀ + 3 * F * (N₀ + 2) + 1) :=
          add_le_add hsumA hsumB
      _ = 2 * k * (3 * N₀ + 3 * F * (N₀ + 2) + 1) := by ring
  have hR := totalDegree_R_le c cc
  have hk2 : 2 * k * (3 * N₀ + 3 * F * (N₀ + 2) + 1)
      ≤ 2 * F * (3 * N₀ + 3 * F * (N₀ + 2) + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hkF)
  have h3F : 3 * r ≤ 3 * F := Nat.mul_le_mul_left 3 hrF
  refine le_trans (add_le_add (le_trans hsum hk2) hR) ?_
  have harith : (2 * F * (3 * N₀ + 3 * F * (N₀ + 2) + 1) + 3 * F : ℝ)
      ≤ 6 * F * (F + 1) * N₀ + (12 * F * F + 5 * F) := by
    nlinarith
  have harith2 : 2 * F * (3 * N₀ + 3 * F * (N₀ + 2) + 1) + 3 * F
      ≤ 6 * F * (F + 1) * N₀ + (12 * F * F + 5 * F) := by
    exact_mod_cast harith
  exact le_trans (add_le_add le_rfl h3F) harith2

end

end Work.WilE3.Realify.ET
