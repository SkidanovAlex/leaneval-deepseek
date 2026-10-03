import Mathlib
import Submission.Commons.Analysis.ExponentialSums.intDist_abs_sub_le
import Submission.Work.A3.Weil.card_emod_eq_le
import Submission.Work.A3.Weil.card_multiples_le
import Submission.Work.A3.Weil.card_goodResidues_le
import Submission.Work.A3.Weil.emod_mul_injOn
import Submission.Work.A3.Weil.intDist_ediv_emod_eq_min

namespace Work.A3.Weil

open Finset
open scoped BigOperators

private lemma intDist_add_intCast_w (x : ℝ) (n : ℤ) :
    Submission.VanDerCorput.intDist (x + (n : ℝ)) = Submission.VanDerCorput.intDist x := by
  simp only [Submission.VanDerCorput.intDist, Int.fract_add_intCast]

private lemma intDist_le_intDist_add_abs_w (x y : ℝ) :
    Submission.VanDerCorput.intDist x ≤ Submission.VanDerCorput.intDist y + |x - y| := by
  have h := Commons.Analysis.ExponentialSums.intDist_abs_sub_le x y
  have h2 : Submission.VanDerCorput.intDist x - Submission.VanDerCorput.intDist y ≤ |x - y| :=
    le_trans (le_abs_self _) h
  linarith

private lemma emod_mul_eq_w (a P : ℤ) {q : ℤ} (hq : 0 < q) :
    (a * P) % q = (a * (P % q)) % q := by
  have h3 : (P % q) % q = P % q :=
    Int.emod_eq_of_lt (Int.emod_nonneg _ (ne_of_gt hq)) (Int.emod_lt_of_pos _ hq)
  calc (a * P) % q = (a % q) * (P % q) % q := Int.mul_emod a P q
    _ = (a % q) * ((P % q) % q) % q := by rw [h3]
    _ = (a * (P % q)) % q := (Int.mul_emod a (P % q) q).symm

theorem card_intDist_le_linear {M Q k : ℕ} {Λ : ℝ} {a q : ℤ}
    (hM : 1 ≤ M) (hq : 1 ≤ q) (hQ : 2 * M ≤ Q) (hk : 1 ≤ k)
    (hc : IsCoprime a q)
    (hΛ : |Λ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (Q : ℝ))) :
    (((Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun P : ℤ =>
        P ≠ 0 ∧ Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)))).card : ℝ)
      ≤ 2 * ((M : ℝ) / (q : ℝ)) + 2 * (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ) * (2 * ((M : ℝ) / (q : ℝ)) + 1) := by
  classical
  have hq0 : (0 : ℤ) < q := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hQ0 : (0 : ℕ) < Q := by omega
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have h2M : (2 : ℝ) * (M : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  set A : Finset ℤ := (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun P : ℤ =>
      P ≠ 0 ∧ Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ))) with hA
  set A0 : Finset ℤ := A.filter (fun P : ℤ => q ∣ P) with hA0
  set A1 : Finset ℤ := A.filter (fun P : ℤ => ¬ (q ∣ P)) with hA1
  have memA : ∀ P : ℤ, P ∈ A ↔ P ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) ∧
      P ≠ 0 ∧ Submission.VanDerCorput.intDist (Λ * (P : ℝ)) ≤ 1 / (2 * (k : ℝ)) := by
    intro P
    rw [hA, Finset.mem_filter]
  have memA0 : ∀ P : ℤ, P ∈ A0 ↔ P ∈ A ∧ q ∣ P := by
    intro P
    rw [hA0, Finset.mem_filter]
  have memA1 : ∀ P : ℤ, P ∈ A1 ↔ P ∈ A ∧ ¬ (q ∣ P) := by
    intro P
    rw [hA1, Finset.mem_filter]
  have hsplit : A.card = A0.card + A1.card := by
    have h := Finset.card_filter_add_card_filter_not (s := A) (p := fun P : ℤ => q ∣ P)
    rw [← hA0, ← hA1] at h
    exact h.symm
  have hA0_bound : (A0.card : ℝ) ≤ 2 * (M : ℝ) / (q : ℝ) := by
    refine card_multiples_le M hq A0 ?_ ?_
    · intro P hP
      obtain ⟨hPA, _⟩ := (memA0 P).mp hP
      obtain ⟨hIcc, hne, _⟩ := (memA P).mp hPA
      exact Finset.mem_filter.mpr ⟨hIcc, hne⟩
    · intro P hP
      exact ((memA0 P).mp hP).2
  have hA1_bound : (A1.card : ℝ) ≤
      2 * (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ) * (2 * (M : ℝ) / (q : ℝ) + 1) := by
    set Sres : Finset ℤ := A1.image (fun P : ℤ => P % q) with hSres
    set Rb : Finset ℤ := (Finset.Icc (1 : ℤ) (q - 1)).filter (fun s : ℤ =>
        ((min s (q - s) : ℤ) : ℝ) ≤ (q : ℝ) / (2 * (k : ℝ)) + 1 / 2) with hRb
    set φ : ℤ → ℤ := fun r => (a * r) % q with hφ
    have hA1_Icc : ∀ P ∈ A1, P ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) := fun P hP =>
      ((memA P).mp ((memA1 P).mp hP).1).1
    have hSres_sub : Sres ⊆ Finset.Icc (1 : ℤ) (q - 1) := by
      intro r hr
      obtain ⟨P, hP, hPr⟩ := by
        rwa [hSres, Finset.mem_image] at hr
      obtain ⟨hPA, hPndvd⟩ := (memA1 P).mp hP
      have hge : 0 ≤ P % q := Int.emod_nonneg _ (ne_of_gt hq0)
      have hlt : P % q < q := Int.emod_lt_of_pos _ hq0
      have hne : P % q ≠ 0 := fun h => hPndvd (Int.dvd_of_emod_eq_zero h)
      rw [← hPr]
      rw [Finset.mem_Icc]
      constructor <;> omega
    have hres : ∀ P ∈ A1, ((min ((a * (P % q)) % q) (q - (a * (P % q)) % q) : ℤ) : ℝ)
        ≤ (q : ℝ) / (2 * (k : ℝ)) + 1 / 2 := by
      intro P hP
      obtain ⟨hPA, _⟩ := (memA1 P).mp hP
      obtain ⟨hIcc, hne0, hcond⟩ := (memA P).mp hPA
      have hIcc' := hIcc
      rw [Finset.mem_Icc] at hIcc'
      have hPabs : |(P : ℝ)| ≤ (M : ℝ) := by
        rw [abs_le]
        exact ⟨by exact_mod_cast hIcc'.1, by exact_mod_cast hIcc'.2⟩
      have hdiff : |((a : ℝ) * (P : ℝ)) / (q : ℝ) - Λ * (P : ℝ)|
          ≤ (M : ℝ) * (1 / ((q : ℝ) * (Q : ℝ))) := by
        have hfactor : ((a : ℝ) * (P : ℝ)) / (q : ℝ) - Λ * (P : ℝ)
            = (P : ℝ) * ((a : ℝ) / (q : ℝ) - Λ) := by ring
        rw [hfactor, abs_mul]
        refine mul_le_mul hPabs ?_ (abs_nonneg _) (le_of_lt hMR)
        rw [abs_sub_comm]
        exact hΛ
      have hMq : (M : ℝ) * (1 / ((q : ℝ) * (Q : ℝ))) ≤ 1 / (2 * (q : ℝ)) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have hmul : (2 : ℝ) * (M : ℝ) * (q : ℝ) ≤ (Q : ℝ) * (q : ℝ) :=
          mul_le_mul_of_nonneg_right h2M (le_of_lt hqR)
        linarith
      have hle : Submission.VanDerCorput.intDist (((a : ℝ) * (P : ℝ)) / (q : ℝ))
          ≤ 1 / (2 * (k : ℝ)) + 1 / (2 * (q : ℝ)) := by
        have hd := intDist_le_intDist_add_abs_w (((a : ℝ) * (P : ℝ)) / (q : ℝ)) (Λ * (P : ℝ))
        linarith [hd, hdiff, hMq, hcond]
      have hcast : ((a * P : ℤ) : ℝ) = (a : ℝ) * (P : ℝ) := Int.cast_mul a P
      have hkey1 : ((min ((a * P) % q) (q - (a * P) % q) : ℤ) : ℝ) / (q : ℝ)
          ≤ 1 / (2 * (k : ℝ)) + 1 / (2 * (q : ℝ)) := by
        rw [← intDist_ediv_emod_eq_min hq (a * P), hcast]
        exact hle
      have hkey2 : ((min ((a * P) % q) (q - (a * P) % q) : ℤ) : ℝ)
          ≤ (q : ℝ) / (2 * (k : ℝ)) + 1 / 2 := by
        have hm := mul_le_mul_of_nonneg_right hkey1 (le_of_lt hqR)
        have h1 : ((min ((a * P) % q) (q - (a * P) % q) : ℤ) : ℝ) / (q : ℝ) * (q : ℝ)
            = ((min ((a * P) % q) (q - (a * P) % q) : ℤ) : ℝ) := by
          field_simp
        have h2 : (1 / (2 * (k : ℝ)) + 1 / (2 * (q : ℝ))) * (q : ℝ)
            = (q : ℝ) / (2 * (k : ℝ)) + 1 / 2 := by
          field_simp
        linarith [hm, h1, h2]
      simpa only [emod_mul_eq_w a P hq0] using hkey2
    have hφ_inj : Set.InjOn φ (Sres : Set ℤ) := by
      intro r₁ h₁ r₂ h₂ heq
      exact emod_mul_injOn hq hc (hSres_sub h₁) (hSres_sub h₂) heq
    have hmaps : ∀ r ∈ Sres, φ r ∈ Rb := by
      intro r hr
      obtain ⟨P, hP, hPr⟩ := by
        rw [hSres, Finset.mem_image] at hr
        exact hr
      rw [← hPr]
      rw [hRb, Finset.mem_filter]
      obtain ⟨hPA, hPndvd⟩ := (memA1 P).mp hP
      have hge : 0 ≤ φ (P % q) := Int.emod_nonneg _ (ne_of_gt hq0)
      have hlt : φ (P % q) < q := Int.emod_lt_of_pos _ hq0
      have hne : φ (P % q) ≠ 0 := by
        intro hφ0
        have h1 : (a * P) % q = 0 := by
          rw [emod_mul_eq_w a P hq0]
          exact hφ0
        exact hPndvd (hc.symm.dvd_of_dvd_mul_left (Int.dvd_of_emod_eq_zero h1))
      refine ⟨?_, hres P hP⟩
      rw [Finset.mem_Icc]
      constructor <;> omega
    have hSres_card : (Sres.card : ℝ) ≤ 2 * (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ) := by
      have himg : Sres.image φ ⊆ Rb := Finset.image_subset_iff.mpr hmaps
      have h1 : ((Sres.image φ).card : ℝ) ≤ (Rb.card : ℝ) := by
        exact_mod_cast Finset.card_le_card himg
      have h2 : (Rb.card : ℝ) ≤ 2 * (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ) := by
        rw [hRb]
        exact card_goodResidues_le hq hk
      have h3 : Sres.card = (Sres.image φ).card := (Finset.card_image_of_injOn hφ_inj).symm
      rw [h3]
      linarith
    have hA1_sub : A1 ⊆ (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun P : ℤ => P % q ∈ Sres) := by
      intro P hP
      rw [Finset.mem_filter]
      exact ⟨hA1_Icc P hP, by rw [hSres, Finset.mem_image]; exact ⟨P, hP, rfl⟩⟩
    have hdecomp : ((Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun P : ℤ => P % q ∈ Sres)).card
        = ∑ r ∈ Sres, (((Finset.Icc (-(M : ℤ)) (M : ℤ)).filter
            (fun P : ℤ => P % q ∈ Sres)).filter (fun P : ℤ => P % q = r)).card :=
      Finset.card_eq_sum_card_fiberwise (f := fun P : ℤ => P % q) (t := Sres)
        (fun P hP => (Finset.mem_filter.mp hP).2)
    have hfib : ∀ r ∈ Sres, ((((Finset.Icc (-(M : ℤ)) (M : ℤ)).filter
        (fun P : ℤ => P % q ∈ Sres)).filter (fun P : ℤ => P % q = r)).card : ℝ)
        ≤ 2 * (M : ℝ) / (q : ℝ) + 1 := by
      intro r _
      have hsub : ((Finset.Icc (-(M : ℤ)) (M : ℤ)).filter
            (fun P : ℤ => P % q ∈ Sres)).filter (fun P : ℤ => P % q = r)
          ⊆ (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun P : ℤ => P % q = r) := by
        intro P hP
        simp only [Finset.mem_filter] at hP ⊢
        exact ⟨hP.1.1, hP.2⟩
      calc ((((Finset.Icc (-(M : ℤ)) (M : ℤ)).filter
              (fun P : ℤ => P % q ∈ Sres)).filter (fun P : ℤ => P % q = r)).card : ℝ)
          ≤ (((Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun P : ℤ => P % q = r)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ 2 * (M : ℝ) / (q : ℝ) + 1 := card_emod_eq_le M hq r
    have hle1 : (A1.card : ℝ) ≤ (((Finset.Icc (-(M : ℤ)) (M : ℤ)).filter
        (fun P : ℤ => P % q ∈ Sres)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hA1_sub
    rw [hdecomp, Nat.cast_sum] at hle1
    have hle2 : ∑ r ∈ Sres, ((((Finset.Icc (-(M : ℤ)) (M : ℤ)).filter
          (fun P : ℤ => P % q ∈ Sres)).filter (fun P : ℤ => P % q = r)).card : ℝ)
        ≤ ∑ r ∈ Sres, (2 * (M : ℝ) / (q : ℝ) + 1) := Finset.sum_le_sum hfib
    have hsum : ∑ r ∈ Sres, (2 * (M : ℝ) / (q : ℝ) + 1)
        = (Sres.card : ℝ) * (2 * (M : ℝ) / (q : ℝ) + 1) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    calc (A1.card : ℝ)
        ≤ (Sres.card : ℝ) * (2 * (M : ℝ) / (q : ℝ) + 1) := by linarith [hle1, hle2, hsum]
      _ ≤ (2 * (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ)) * (2 * (M : ℝ) / (q : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hSres_card (by positivity)
  have hfinal : (A.card : ℝ) ≤ 2 * ((M : ℝ) / (q : ℝ)) +
      2 * (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ) * (2 * ((M : ℝ) / (q : ℝ)) + 1) := by
    have hcast : (A.card : ℝ) = (A0.card : ℝ) + (A1.card : ℝ) := by
      rw [hsplit]
      push_cast
      ring
    rw [hcast]
    have hsum2 : (A0.card : ℝ) + (A1.card : ℝ) ≤ 2 * (M : ℝ) / (q : ℝ) +
        2 * (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ) * (2 * (M : ℝ) / (q : ℝ) + 1) :=
      add_le_add hA0_bound hA1_bound
    calc (A0.card : ℝ) + (A1.card : ℝ)
        ≤ 2 * (M : ℝ) / (q : ℝ) +
            2 * (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ) * (2 * (M : ℝ) / (q : ℝ) + 1) := hsum2
      _ = 2 * ((M : ℝ) / (q : ℝ)) +
            2 * (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ) * (2 * ((M : ℝ) / (q : ℝ)) + 1) := by ring
  exact hfinal

end Work.A3.Weil
