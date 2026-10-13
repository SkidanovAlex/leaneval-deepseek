import Mathlib
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.StarR.proj
import Submission.Work.WilE8.Ocube.ocube_star
import Submission.Work.WilE8.Star.init_star
import Submission.Work.WilE8.Sharp.CylTransport
import Submission.Work.WilE8.Sharp.exists_dom_max
import Submission.Work.WilE8.Poly.eval_mono_nat

namespace Work.WilE8.Sharp

open WilkiesDesign WilkiesDesign.E

theorem sharpCD_starR
    (hBV : ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D k : ℕ) (Y : Fin k → Set (Fin n → ℝ)), (∀ i, WilkiesDesign.E.Star F D n (Y i)) →
      ∃ C : Finset (Set (Fin n → ℝ)), WilkiesDesign.E.IsCylDecompOn n (WilkiesDesign.E.cubeC n) C ∧
        (∀ i, ∀ κ ∈ C, κ ⊆ Y i ∨ Disjoint κ (Y i)) ∧
        C.card ≤ MvPolynomial.eval ![D, k] b ∧ ∀ κ ∈ C, WilkiesDesign.E.Star a (c.eval D) n κ)
    (hInter : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (k : ℕ) (D : Fin k → ℕ)
      (Y : Fin k → Set (Fin n → ℝ)), (∀ i, WilkiesDesign.E.Star F (D i) n (Y i)) →
      WilkiesDesign.E.Star a (p.eval (∑ i, D i)) n (WilkiesDesign.E.cubeC n ∩ ⋂ i, Y i))
    (hOcube : ∀ N : ℕ, WilkiesDesign.E.Star N (2 * N + 1) N (Work.WilE8.ocube N))
    (F n : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D k : ℕ) (X : Fin k → Set (Fin n → ℝ)), (∀ i, WilkiesDesign.E.StarR F D n (X i)) →
        ∃ C : Finset (Set (Fin n → ℝ)), WilkiesDesign.IsCylDecomp n C ∧
          (∀ i, ∀ κ ∈ C, κ ⊆ X i ∨ Disjoint κ (X i)) ∧
          C.card ≤ MvPolynomial.eval ![D, k] b ∧
          ∀ κ ∈ C, WilkiesDesign.E.StarR a (c.eval D) n κ := by
  classical
  obtain ⟨a₀, b₀, c₀, hBV'⟩ := hBV (max F n) n
  obtain ⟨b₁, hb₁⟩ := exists_dom_max (2 * n + 1) b₀
  have hc₁ : ∀ D : ℕ, c₀.eval (max D (2 * n + 1)) ≤
      (c₀.comp (Polynomial.X + Polynomial.C (2 * n + 1))).eval D := by
    intro D
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    exact Work.WilE8.Poly.eval_mono_nat c₀
      (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))
  refine ⟨a₀, b₁, c₀.comp (Polynomial.X + Polynomial.C (2 * n + 1)), ?_⟩
  intro D k X hX
  choose Z hZstar hZX using hX
  obtain ⟨C₀, hCyl, hsep, hcard, hcell⟩ :=
    hBV' (max D (2 * n + 1)) (k + 1) (Fin.cons (ocube n) Z) (by
      intro j
      refine Fin.cases ?_ ?_ j
      · rw [Fin.cons_zero]
        exact Work.WilE8.Star.mono (hOcube n) (le_max_right F n) (le_max_right D (2 * n + 1))
      · intro i
        rw [Fin.cons_succ]
        exact Work.WilE8.Star.mono (hZstar i) (le_max_left F n) (le_max_left D (2 * n + 1)))
  have hcut : ∀ κ ∈ C₀, κ ⊆ ocube n ∨ Disjoint κ (ocube n) := fun κ hκ => hsep 0 κ hκ
  refine ⟨(C₀.filter fun κ => κ ⊆ ocube n).image (fun κ => psiV ⁻¹' κ), ?_, ?_, ?_, ?_⟩
  · have htr := transport_aux n n le_rfl C₀ hCyl hcut
    rwa [show (C₀.filter fun κ => κ ⊆ ocube n).image (keep (le_rfl : n ≤ n))
          = C₀.filter fun κ => κ ⊆ ocube n from by
        rw [Finset.image_congr (fun c _ => keep_self (le_rfl : n ≤ n) c), Finset.image_id']]
      at htr
  · intro i κ hκ
    obtain ⟨κ', hκ', rfl⟩ := Finset.mem_image.mp hκ
    have hκ'₀ : κ' ∈ C₀ := (Finset.mem_filter.mp hκ').1
    rcases hsep (Fin.succ i) κ' hκ'₀ with hsub | hdis
    · left
      rw [hZX i]
      exact Set.preimage_mono hsub
    · right
      rw [hZX i]
      exact hdis.preimage psiV
  · calc ((C₀.filter fun κ => κ ⊆ ocube n).image (fun κ => psiV ⁻¹' κ)).card
        ≤ (C₀.filter fun κ => κ ⊆ ocube n).card := Finset.card_image_le
      _ ≤ C₀.card := Finset.card_filter_le _ _
      _ ≤ MvPolynomial.eval ![max D (2 * n + 1), k + 1] b₀ := hcard
      _ ≤ MvPolynomial.eval ![D, k] b₁ := hb₁ D k
  · intro κ hκ
    obtain ⟨κ', hκ', rfl⟩ := Finset.mem_image.mp hκ
    exact Work.WilE8.StarR.mono ⟨κ', hcell κ' (Finset.mem_filter.mp hκ').1, rfl⟩ le_rfl (hc₁ D)

end Work.WilE8.Sharp
