import Mathlib
import Submission.Work.Peluse.Prop36SW.conclDirAbs

/-!
# The endgame of the §5 chain: the ladder's conclusion at a **constant** coefficient

At the very end of the chain the state lives at **slot level `0`**, where the chain's coefficient
function is

  `pFlat D d c 0 Λ s x = Λ · (d - 0) · D.dir d c 0 (D.par 0 s) (…) = Λ·d·c = d!·c`,

constant in both the slot `s` and the parameter `x` (since `D.dir d c 0 _ _ = c`).  Hence *every*
long direction of a ladder application at that level is the same AP `arithIcc (d!c)[L']`.

If moreover the multiplicity function `kω` of that state is supported on nonempty subsets of the
slot type that all contain a *common* slot `s₀`, then the ladder's *short* family — indexed by the
nonempty subsets avoiding `s₀` — is **empty**, the conclusion's index type is `Fin t'`, and its
family is the `t'`-fold repetition of the single AP `arithIcc κ[L']`.  The conclusion is then
literally `γ ≤ (uNormPow t' (arithIcc κ L') S f) ^ (1 / 2^{t'})`, since the summand does not depend
on the averaged parameters; raising to the power `2^{t'}` gives the final `uNormPow` bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl
open Work.Peluse

/-- **The conclusion's index type collapses to `Fin t'`** when the multiplicities vanish off the
subsets containing `s₀`. -/
lemma card_conclIdx_of_notMem {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : SlotSet ι (fun _ => 1) → ℕ) (s₀ : Slot ι (fun _ => 1))
    (hkar : ∀ ω : SlotSet ι (fun _ => 1), s₀ ∉ ω.1 → kω ω = 0) (t' : ℕ) :
    Fintype.card (ConclIdx s₀ kω t') = t' := by
  have h0 : Fintype.card
      (Σ ω : {s : Finset (Slot ι (fun _ => 1)) // s.Nonempty ∧ s₀ ∉ s},
        Fin (kω ⟨ω.1, ω.2.1⟩)) = 0 := by
    rw [Fintype.card_sigma]
    refine Finset.sum_eq_zero (fun ω _ => ?_)
    rw [Fintype.card_fin, hkar ⟨ω.1, ω.2.1⟩ ω.2.2]
  show Fintype.card (Sum (Fin t')
      (Σ ω : {s : Finset (Slot ι (fun _ => 1)) // s.Nonempty ∧ s₀ ∉ s},
        Fin (kω ⟨ω.1, ω.2.1⟩))) = t'
  rw [Fintype.card_sum, Fintype.card_fin, h0, add_zero]

/-- **Every direction of the conclusion's family is the same AP** `arithIcc κ [L']` when the
coefficient is the constant `κ` and the multiplicities vanish off the subsets containing `s₀`. -/
lemma conclDirG_const {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : SlotSet ι (fun _ => 1) → ℕ) (s₀ : Slot ι (fun _ => 1))
    (hkar : ∀ ω : SlotSet ι (fun _ => 1), s₀ ∉ ω.1 → kω ω = 0)
    (κ : ℤ) (M₁ M₂ : ℕ) (γ' : ℝ) (t' : ℕ) {n : ℕ} (a : Fin n → ℤ)
    (b : Slot ι (fun _ => 1) → ℤ) (z : ConclIdx s₀ kω t') :
    Work.Peluse.Prop36SW.conclDirG (fun _ (_ : Fin n → ℤ) => κ) M₁ M₂ γ' s₀ t' a b z
      = arithIcc κ (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat := by
  rcases z with u | ⟨ω, r⟩
  · rfl
  · exact Fin.elim0 ((hkar ⟨ω.1, ω.2.1⟩ ω.2.2) ▸ r)

/-- **The endgame of the §5 chain.**  From the ladder's conclusion at a state whose coefficient is
the constant `κ` and whose multiplicities are supported on the subsets containing `s₀`, conclude the
`uNormPow` bound at the single long AP `arithIcc κ [⌊γ'M₁M₂⌋]`. -/
theorem endgameOfConcl {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : SlotSet ι (fun _ => 1) → ℕ) (s₀ : Slot ι (fun _ => 1))
    (hkar : ∀ ω : SlotSet ι (fun _ => 1), s₀ ∉ ω.1 → kω ω = 0)
    (κ : ℤ) (M₁ M₂ : ℕ) (hM₂ : 1 ≤ M₂) (γ' : ℝ) (t' : ℕ) (n : ℕ) (S : Finset ℤ)
    (f : ℤ → ℂ) (A : Finset (Fin n → ℤ)) (γ : ℝ) (hγ : 0 < γ)
    (hconcl : γ ≤ (A.card : ℝ)⁻¹ * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
        ∑ a ∈ A, ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
          boxNorm (Fintype.card (ConclIdx s₀ kω t'))
            (fun i => Work.Peluse.Prop36SW.conclDirG (fun _ (_ : Fin n → ℤ) => κ) M₁ M₂ γ' s₀ t'
              a b ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)) S f) :
    γ ^ (2 ^ t') ≤ uNormPow t' (arithIcc κ (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) S f := by
  classical
  set Q : Finset ℤ := arithIcc κ (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat with hQ
  set X : ℝ := boxNorm (Fintype.card (ConclIdx s₀ kω t'))
      (fun _ : Fin (Fintype.card (ConclIdx s₀ kω t')) => Q) S f with hX
  have hcard := card_conclIdx_of_notMem kω s₀ hkar t'
  have hsummand : ∀ a ∈ A, ∀ b ∈ paramBox (k := fun _ : ι => 1) M₂,
      boxNorm (Fintype.card (ConclIdx s₀ kω t'))
        (fun i => Work.Peluse.Prop36SW.conclDirG (fun _ (_ : Fin n → ℤ) => κ) M₁ M₂ γ' s₀ t' a b
          ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)) S f = X := by
    intro a _ b _
    rw [hX]
    refine congrArg (fun F : Fin (Fintype.card (ConclIdx s₀ kω t')) → Finset ℤ =>
      boxNorm (Fintype.card (ConclIdx s₀ kω t')) F S f) ?_
    funext i
    exact conclDirG_const kω s₀ hkar κ M₁ M₂ γ' t' a b _
  have hsum : ∑ a ∈ A, ∑ b ∈ paramBox (k := fun _ : ι => 1) M₂,
      boxNorm (Fintype.card (ConclIdx s₀ kω t'))
        (fun i => Work.Peluse.Prop36SW.conclDirG (fun _ (_ : Fin n → ℤ) => κ) M₁ M₂ γ' s₀ t' a b
          ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)) S f
      = (A.card : ℝ) * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) * X := by
    rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => hsummand a ha b hb))]
    rw [Finset.sum_const, Finset.sum_const]
    push_cast
    ring
  rw [hsum] at hconcl
  have hAcard : (A.card : ℝ) ≠ 0 := by
    intro h0
    rw [h0, inv_zero, zero_mul, zero_mul] at hconcl
    exact absurd hconcl (not_le.mpr hγ)
  have hPcard : ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) ≠ 0 := by
    have hmem : (fun _ : Slot ι (fun _ => 1) => (0 : ℤ)) ∈ paramBox (k := fun _ : ι => 1) M₂ := by
      rw [paramBox, Fintype.mem_piFinset]
      intro s
      rw [Finset.mem_Ioo]
      constructor <;> omega
    have := Finset.card_pos.mpr ⟨_, hmem⟩
    exact_mod_cast this.ne'
  have hXeq : (A.card : ℝ)⁻¹ * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
      ((A.card : ℝ) * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) * X) = X := by
    have h1 : (A.card : ℝ)⁻¹ * (A.card : ℝ) = 1 := inv_mul_cancel₀ hAcard
    have h2 : ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
        ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) = 1 := inv_mul_cancel₀ hPcard
    calc (A.card : ℝ)⁻¹ * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
          ((A.card : ℝ) * ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) * X)
        = ((A.card : ℝ)⁻¹ * (A.card : ℝ)) *
            (((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
              ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)) * X := by ring
      _ = 1 * 1 * X := by rw [h1, h2]
      _ = X := by ring
  rw [hXeq] at hconcl
  have hXu : X = (uNormPow t' Q S f) ^ (1 / ((2 : ℝ) ^ t')) := by
    rw [hX, hcard]
    rfl
  rw [hXu] at hconcl
  have hXnn : (0 : ℝ) ≤ uNormPow t' Q S f := by
    rw [uNormPow]
    exact norm_nonneg _
  have hmain : γ ^ (2 ^ t') ≤ ((uNormPow t' Q S f) ^ (1 / ((2 : ℝ) ^ t'))) ^ (2 ^ t') :=
    pow_le_pow_left₀ hγ.le hconcl (2 ^ t')
  have hpow : ((uNormPow t' Q S f) ^ (1 / ((2 : ℝ) ^ t'))) ^ (2 ^ t') = uNormPow t' Q S f := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXnn]
    have h2t : ((2 ^ t' : ℕ) : ℝ) ≠ 0 := by positivity
    have : (1 / ((2 : ℝ) ^ t')) * ((2 ^ t' : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_one]
  rw [hpow] at hmain
  simpa only [hQ] using hmain

end

end Work.Peluse.Prop36SW
