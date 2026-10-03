import Mathlib
import Submission.Work.Peluse.Prop36SW.conclPeelLongG

namespace Work.Peluse.Prop36SW

theorem conclPeelAvgShort {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) {P : Type} (p : ι → P → ℤ)
    (M₁ M₂ N : ℕ) (γ' : ℝ) (t' : ℕ) (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1))
    (hT : 1 ≤ t') (hB : 1 ≤ Fintype.card (Work.Peluse.Prop36SW.ShortIdx (k := fun _ : ι => 1) kω s₀))
    (hL : 1 ≤ (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
    (a : P) (hc : p s₀.1 a ≠ 0)
    (b : Work.Peluse.UControl.Slot ι (fun _ => 1) → ℤ) (g : ℤ → ℂ) (hg : Work.Peluse.FinSuppZ g) :
    Work.Peluse.boxNormPow (Fintype.card (Work.Peluse.UControl.ConclIdx s₀ kω t'))
        (fun i => Work.Peluse.Prop36SW.conclDirG p M₁ M₂ γ' s₀ t' a b ((Fintype.equivFin (Work.Peluse.UControl.ConclIdx s₀ kω t')).symm i))
        (Work.Peluse.symIcc N) g
      = (((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ))⁻¹ ^ (2 * t') *
        ∑ sh : (j : Fin t') → ↥(Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) ×
                          ↥(Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat),
          Work.Peluse.boxNormPow (Fintype.card (Work.Peluse.Prop36SW.ShortIdx (k := fun _ : ι => 1) kω s₀))
            (Work.Peluse.Prop36SW.shortFamG kω p M₁ a b s₀) (Work.Peluse.symIcc N)
            (Work.Peluse.Ulower.iterDelta t' (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) g) := by
  -- `conclPeelLongG` gives the same identity with the constant `∏_{j : Fin t'} (|c[L]|⁻¹)²`, where
  -- `c = p s₀.1 a` and `L = ⌊γ'M₁M₂⌋`; since `c ≠ 0`, `|c[L]| = L`, so the product collapses to
  -- `L^{-2t'}`.
  have hcard : ((Work.Peluse.arithIcc (p s₀.1 a)
        (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat).card : ℝ)
      = ((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ) := by
    rw [Work.Peluse.BoxNormDilation.card_arithIcc hc]
  have hprod : (∏ j : Fin t',
        (((Work.Peluse.arithIcc (p s₀.1 a)
          (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat).card : ℝ))⁻¹ ^ 2)
      = (((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ))⁻¹ ^ (2 * t') := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcard, ← pow_mul]
  rw [conclPeelLongG (k := fun _ : ι => 1) kω p M₁ M₂ γ' s₀ t' hT hB a b
        (Work.Peluse.symIcc N) g hg, hprod]

end Work.Peluse.Prop36SW
