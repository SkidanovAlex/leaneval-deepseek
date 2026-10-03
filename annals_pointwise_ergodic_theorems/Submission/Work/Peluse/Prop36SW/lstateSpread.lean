import Mathlib
import Submission.Work.Peluse.Prop36SW.roundDefs

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-- A `1`-bounded function supported in `[-N,N]` has box norm at most `1` on the window `symIcc N`.
(This is `Work.Peluse.BoxNorm.boxNormPow_le_one` transported through
`boxNorm = boxNormPow ^ (1/2^t)`.) -/
private lemma boxNorm_le_one_of_supportIn' {t : ℕ} {Q : Fin t → Finset ℤ} {N : ℕ} {f : ℤ → ℂ}
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsu : Work.Peluse.SupportIn f N) :
    boxNorm t Q (symIcc N) f ≤ 1 := by
  have h1 : boxNormPow t Q (symIcc N) f ≤ 1 :=
    Work.Peluse.BoxNorm.boxNormPow_le_one hf (fun x hx => hsu x (by
      have h : ¬ (-(N : ℤ) ≤ x ∧ x ≤ (N : ℤ)) := by
        simpa [symIcc, Finset.mem_Icc] using hx
      omega))
  have h2 : boxNorm t Q (symIcc N) f
      = (boxNormPow t Q (symIcc N) f) ^ (1 / (2 : ℝ) ^ t) := rfl
  rw [h2]
  exact Real.rpow_le_one (norm_nonneg _) h1 (by positivity)

/-- **Mass spreading over a `Finset`.**

Let `F : A → Pf → ℝ` be bounded by `1` on `A × Pf`, and suppose the average of `F` over `A × Pf`
is at least `γ`.  If `A' ⊆ A` and the complement `A \ A'` occupies at most a `γ/4` fraction of `A`
(measured by cardinality), then the average of `F` over `A' × Pf` is at least `3γ/4`.

The hypotheses `γ ≤ 1` and `4|A \ A'| ≤ γ|A|` force `|A'| ≥ 3|A|/4 > 0`, and every one of the at
most `|A \ A'| · |Pf|` terms removed is at most `1`, so at most a `γ/4` fraction of the total mass
`γ|A||Pf|` is lost; normalising by `|A'| ≤ |A|` gives the factor `3/4`. -/
private lemma spreadCore {α β : Type} [DecidableEq α] [DecidableEq β]
    (A A' : Finset α) (Pf : Finset β) (F : α → β → ℝ) (γ : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hA' : A' ⊆ A)
    (hgood : 4 * ((A \ A').card : ℝ) ≤ γ * (A.card : ℝ))
    (hbound : ∀ a ∈ A, ∀ b ∈ Pf, F a b ≤ 1)
    (hPf : 1 ≤ Pf.card)
    (hfam : γ ≤ (A.card : ℝ)⁻¹ * (Pf.card : ℝ)⁻¹ * ∑ a ∈ A, ∑ b ∈ Pf, F a b) :
    3 * γ / 4 ≤ (A'.card : ℝ)⁻¹ * (Pf.card : ℝ)⁻¹ * ∑ a ∈ A', ∑ b ∈ Pf, F a b := by
  classical
  have hm : 0 < (Pf.card : ℝ) := by
    have h : 0 < Pf.card := Nat.lt_of_lt_of_le Nat.zero_lt_one hPf
    exact_mod_cast h
  -- `A` is nonempty: otherwise `hfam` gives `γ ≤ 0`.
  have hAcard : 0 < (A.card : ℝ) := by
    rcases Nat.eq_zero_or_pos A.card with h0 | hpos
    · exfalso
      have hAe : A = ∅ := Finset.card_eq_zero.mp h0
      have hγle : γ ≤ 0 := by
        have h := hfam
        rw [hAe] at h
        simpa using h
      linarith
    · exact_mod_cast hpos
  -- the removed mass is at most `|A \ A'| · |Pf|`
  have hSbad_le : (∑ a ∈ A \ A', ∑ b ∈ Pf, F a b) ≤ ((A \ A').card : ℝ) * (Pf.card : ℝ) := by
    calc ∑ a ∈ A \ A', ∑ b ∈ Pf, F a b
        ≤ ∑ a ∈ A \ A', ∑ b ∈ Pf, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          apply Finset.sum_le_sum
          intro b hb
          exact hbound a (Finset.mem_sdiff.mp ha).1 b hb
      _ = ∑ a ∈ A \ A', (Pf.card : ℝ) := by simp
      _ = ((A \ A').card : ℝ) * (Pf.card : ℝ) := by simp [Finset.sum_const, nsmul_eq_mul]
  -- the total mass is at least `γ |A| |Pf|`
  have hS_ge : γ * (A.card : ℝ) * (Pf.card : ℝ) ≤ ∑ a ∈ A, ∑ b ∈ Pf, F a b := by
    have h := mul_le_mul_of_nonneg_right hfam
      (show (0 : ℝ) ≤ (A.card : ℝ) * (Pf.card : ℝ) from le_of_lt (mul_pos hAcard hm))
    have hrhs : ((A.card : ℝ)⁻¹ * (Pf.card : ℝ)⁻¹ * (∑ a ∈ A, ∑ b ∈ Pf, F a b))
        * ((A.card : ℝ) * (Pf.card : ℝ)) = ∑ a ∈ A, ∑ b ∈ Pf, F a b := by
      rw [show ((A.card : ℝ)⁻¹ * (Pf.card : ℝ)⁻¹ * (∑ a ∈ A, ∑ b ∈ Pf, F a b))
          * ((A.card : ℝ) * (Pf.card : ℝ))
          = ((A.card : ℝ)⁻¹ * (A.card : ℝ)) * ((Pf.card : ℝ)⁻¹ * (Pf.card : ℝ))
            * (∑ a ∈ A, ∑ b ∈ Pf, F a b) by ring]
      rw [inv_mul_cancel₀ (ne_of_gt hAcard), inv_mul_cancel₀ (ne_of_gt hm)]
      ring
    rw [hrhs] at h
    simpa only [mul_assoc] using h
  have hbad_le : ((A \ A').card : ℝ) * (Pf.card : ℝ) ≤ (γ * (A.card : ℝ) / 4) * (Pf.card : ℝ) := by
    have hb : ((A \ A').card : ℝ) ≤ γ * (A.card : ℝ) / 4 := by linarith
    exact mul_le_mul_of_nonneg_right hb (le_of_lt hm)
  have hSeq : (∑ a ∈ A \ A', ∑ b ∈ Pf, F a b) + (∑ a ∈ A', ∑ b ∈ Pf, F a b)
      = ∑ a ∈ A, ∑ b ∈ Pf, F a b :=
    Finset.sum_sdiff hA' (f := fun a => ∑ b ∈ Pf, F a b)
  -- `A'` is nonempty
  have hA'pos : 0 < (A'.card : ℝ) := by
    have hone : 1 ≤ (A.card : ℝ) := by
      have hAne : A.card ≠ 0 := by
        intro h
        rw [h] at hAcard
        exact (lt_irrefl (0 : ℝ)) (by simpa using hAcard)
      have h1 : 1 ≤ A.card := Nat.one_le_iff_ne_zero.mpr hAne
      exact_mod_cast h1
    have hb_le : 4 * ((A \ A').card : ℝ) ≤ (A.card : ℝ) := by
      nlinarith [hgood, hγ1, hAcard.le]
    have hcard' : (A'.card : ℝ) = (A.card : ℝ) - ((A \ A').card : ℝ) := by
      have hsum : (A \ A').card + A'.card = A.card := Finset.card_sdiff_add_card_eq_card hA'
      have hcast : ((A \ A').card : ℝ) + (A'.card : ℝ) = (A.card : ℝ) := by
        rw [← Nat.cast_add, hsum]
      linarith
    nlinarith [hcard', hone, hb_le]
  have hkey : (3 * γ / 4) * ((A'.card : ℝ) * (Pf.card : ℝ))
      ≤ ∑ a ∈ A', ∑ b ∈ Pf, F a b := by
    have h1 : (3 * γ / 4) * ((A'.card : ℝ) * (Pf.card : ℝ))
        ≤ (3 * γ / 4) * ((A.card : ℝ) * (Pf.card : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast Finset.card_le_card hA') (le_of_lt hm)
    have h3 : (3 * γ / 4) * ((A.card : ℝ) * (Pf.card : ℝ))
        ≤ ∑ a ∈ A', ∑ b ∈ Pf, F a b := by
      nlinarith [hSeq, hSbad_le, hbad_le, hS_ge]
    linarith [h1, h3]
  calc 3 * γ / 4
      ≤ (∑ a ∈ A', ∑ b ∈ Pf, F a b) / ((A'.card : ℝ) * (Pf.card : ℝ)) := by
        rw [le_div_iff₀ (mul_pos hA'pos hm)]
        exact hkey
    _ = (A'.card : ℝ)⁻¹ * (Pf.card : ℝ)⁻¹ * ∑ a ∈ A', ∑ b ∈ Pf, F a b := by
        rw [div_eq_mul_inv, mul_inv]
        ring

/-- **The good-set spread of the §5 chain state.**

If the full-box state `LStateBox` holds at strength `γ`, then on the subset of the parameter box
where *no* slot coefficient vanishes, the state `LStateAbs` holds at strength `3γ/4`.  The price is
paid by the hypothesis that the vanishing-coefficient set occupies at most a `γ/4` fraction of the
box, together with the fact that every `boxNorm ≤ 1`. -/
theorem lstateSpread {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} [DecidableEq P]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ)
    (p : ι → P → ℤ) (M₁ M₂ N Dc : ℕ) (A : Finset P) (g : P → ℤ → ℂ) (γ : ℝ)
    (hst : Work.Peluse.Prop36SW.LStateBox kω p M₁ M₂ N Dc A g γ)
    (hγ0 : 0 < γ)
    (hgood : 4 * ((A.filter (fun a => ∃ i, p i a = 0)).card : ℝ) ≤ γ * (A.card : ℝ)) :
    Work.Peluse.Prop36SW.LStateAbs kω p M₁ M₂ N Dc
      (A.filter (fun a => ∀ i, p i a ≠ 0)) g (3 * γ / 4) := by
  classical
  obtain ⟨hγ0', hγ1, hM2a, hM2b, hN1, hM1M2N, hpN, hpD, hg1, hg2, hfam⟩ := hst
  set A' : Finset P := A.filter (fun a => ∀ i, p i a ≠ 0) with hA'def
  have hA'sub : A' ⊆ A := by
    rw [hA'def]
    exact Finset.filter_subset _ _
  have hdiff : A \ A' = A.filter (fun a => ∃ i, p i a = 0) := by
    rw [hA'def]
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · rintro ⟨ha, hna⟩
      refine ⟨ha, ?_⟩
      by_contra hcon
      push_neg at hcon
      exact hna ⟨ha, hcon⟩
    · rintro ⟨ha, i, hi⟩
      refine ⟨ha, ?_⟩
      rintro ⟨-, hall⟩
      exact hall i hi
  have hgood' : 4 * ((A \ A').card : ℝ) ≤ γ * (A.card : ℝ) := by
    rw [hdiff]
    exact hgood
  refine ⟨?_, ?_, hM2a, hM2b, hN1, hM1M2N, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · intro i a ha
    rw [hA'def] at ha
    exact (Finset.mem_filter.mp ha).2 i
  · intro i a ha
    rw [hA'def] at ha
    exact hpN i a (Finset.mem_filter.mp ha).1
  · intro i a ha
    rw [hA'def] at ha
    exact hpD i a (Finset.mem_filter.mp ha).1
  · intro a ha x
    rw [hA'def] at ha
    exact hg1 a (Finset.mem_filter.mp ha).1 x
  · intro a ha
    rw [hA'def] at ha
    exact hg2 a (Finset.mem_filter.mp ha).1
  · refine spreadCore A A' (paramBox (k := fun _ : ι => 1) M₂)
      (fun a b => boxNorm (Fintype.card (FamIdx kω))
        (fun j : Fin (Fintype.card (FamIdx kω)) => pDirFamG p M₁ a b
          ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) (g a))
      γ hγ0 hγ1 hA'sub hgood' ?_ ?_ hfam
    · intro a ha b hb
      exact boxNorm_le_one_of_supportIn' (hg1 a ha) (hg2 a ha)
    · have hmem : (fun _ : Slot ι (fun _ => 1) => (0 : ℤ))
          ∈ paramBox (k := fun _ : ι => 1) M₂ := by
        rw [paramBox, Fintype.mem_piFinset]
        intro s
        rw [Finset.mem_Ioo]
        constructor <;> omega
      exact Finset.card_pos.mpr ⟨_, hmem⟩

end

end Work.Peluse.Prop36SW
