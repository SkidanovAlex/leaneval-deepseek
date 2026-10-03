import Mathlib
import Submission.Work.Peluse.Ulower.iterDefs
import Submission.Work.Peluse.Ulower.u2inverse_arithIcc

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## Helpers of the degree-lowering assembly, shared with the sub-modules

These two lemmas are used by several modules of the assembly (`Ulower/step`), so they live in
their own module (the main statement's module imports this one, and the assembly modules import it
too -- putting them in the main module would create an import cycle). -/

/-! ## Helper: the `U²`-inverse theorem step of the assembly

The next lemma is the only place where the hypothesis `h1 = PeluseU2Inverse` is consumed in the
degree-lowering route: from a level-2 box-norm bound at the *interval* direction set `arithIcc 1 D`
one extracts a character correlation, normalised by the support radius.  It is a direct
consequence of `Ulower/u2inverse_arithIcc` (which is `PeluseU2Inverse` in the `uNormPow 2` form
with the `L` factor). -/
theorem char_of_boxNormPow_two (h1 : Work.Peluse.PeluseU2Inverse) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
      ∀ (L D : ℕ) (g : ℤ → ℂ) (η : ℝ), 1 ≤ L → 1 ≤ D → (D : ℝ) ≤ (L : ℝ) →
        Work.Peluse.SupportIn g L → (∀ x : ℤ, ‖g x‖ ≤ 1) → 0 < η → η ≤ 1 →
        η ≤ Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Work.Peluse.arithIcc 1 D)
              (Work.Peluse.symIcc L) g →
        ∃ β : ℝ, C₀ * η ^ K₀ * ((D : ℝ) / (L : ℝ)) ^ K₀ * (L : ℝ) ≤
          ‖∑' x : ℤ, g x *
            Complex.exp (2 * Real.pi * Complex.I * β * (x : ℝ))‖ := by
  obtain ⟨C₀, hC₀, K₀, hK₀, h⟩ := Work.Peluse.Ulower.u2inverse_arithIcc h1
  exact ⟨C₀, hC₀, K₀, hK₀, fun L D g η hL hD hDL hsupp hbd hη0 hη1 hbox =>
    h L D g η hL hD hDL hsupp hbd hη0 hη1 hbox⟩

/-! ## Helper: the density/Markov step of the assembly

From an average bound `η ≤ |H|⁻¹ ∑_{p∈H} X p` with `X p ≤ 1` on `H` one extracts a **dense**
sub-family on which `X ≥ η/2`.  This is the step that turns the peel identity (P1) into the dense
family to which `h1` is applied, and (applied a second time, to `□_{t-2}(H₁)`) the dense family to
which `h2` is applied. -/
theorem denseSet_of_avg {ι : Type*} [DecidableEq ι] (H : Finset ι) (X : ι → ℝ) {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hX1 : ∀ p ∈ H, X p ≤ 1)
    (havg : η ≤ ((H.card : ℝ))⁻¹ * ∑ p ∈ H, X p) :
    ∃ H' ⊆ H, η / 2 * (H.card : ℝ) ≤ (H'.card : ℝ) ∧ ∀ p ∈ H', η / 2 ≤ X p := by
  classical
  set A : Finset ι := H.filter (fun p => η / 2 ≤ X p) with hA
  have hAsub : A ⊆ H := Finset.filter_subset _ _
  have hHpos : 0 < (H.card : ℝ) := by
    rcases Nat.eq_zero_or_pos H.card with h0 | h0
    · exfalso
      rw [h0] at havg
      simp at havg
      linarith
    · exact_mod_cast h0
  have hmain : η * (H.card : ℝ) ≤ ∑ p ∈ H, X p := by
    have h1 : ((H.card : ℝ))⁻¹ * (H.card : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hHpos)
    calc η * (H.card : ℝ) ≤ (((H.card : ℝ))⁻¹ * ∑ p ∈ H, X p) * (H.card : ℝ) :=
          mul_le_mul_of_nonneg_right havg hHpos.le
      _ = (∑ p ∈ H, X p) * (((H.card : ℝ))⁻¹ * (H.card : ℝ)) := by ring
      _ = ∑ p ∈ H, X p := by rw [h1, mul_one]
  have hsd : ∑ p ∈ H \ A, X p + ∑ p ∈ A, X p = ∑ p ∈ H, X p := Finset.sum_sdiff hAsub
  have hcast : ((H \ A).card : ℝ) = (H.card : ℝ) - (A.card : ℝ) := by
    have h1 : (H \ A).card = H.card - A.card := by
      rw [Finset.card_sdiff]
      have hinter : A ∩ H = A := Finset.inter_eq_left.mpr hAsub
      rw [hinter]
    rw [h1, Nat.cast_sub (Finset.card_le_card hAsub)]
  have hAle : ∑ p ∈ A, X p ≤ (A.card : ℝ) := by
    calc ∑ p ∈ A, X p ≤ ∑ p ∈ A, (1 : ℝ) := Finset.sum_le_sum (fun p hp => hX1 p (hAsub hp))
      _ = (A.card : ℝ) := by simp
  have hBle : ∑ p ∈ H \ A, X p ≤ ((H.card : ℝ) - (A.card : ℝ)) * (η / 2) := by
    calc ∑ p ∈ H \ A, X p ≤ ∑ p ∈ H \ A, (η / 2) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hp1 : p ∈ H := (Finset.mem_sdiff.mp hp).1
          have hp2 : p ∉ A := (Finset.mem_sdiff.mp hp).2
          have hq : ¬ (η / 2 ≤ X p) := by
            intro hcon
            exact hp2 (by rw [hA, Finset.mem_filter]; exact ⟨hp1, hcon⟩)
          exact le_of_lt (not_le.mp hq)
      _ = ((H \ A).card : ℝ) * (η / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((H.card : ℝ) - (A.card : ℝ)) * (η / 2) := by rw [hcast]
  have hchain : η * (H.card : ℝ) ≤ (A.card : ℝ) + ((H.card : ℝ) - (A.card : ℝ)) * (η / 2) := by
    linarith [hmain, hsd, hAle, hBle]
  refine ⟨A, hAsub, ?_, ?_⟩
  · nlinarith [hchain, hη0, hη1, Nat.cast_nonneg (α := ℝ) A.card]
  · intro p hp
    have := (Finset.mem_filter.mp (by rw [← hA]; exact hp)).2
    exact this


end

end Work.Peluse.Ulower
