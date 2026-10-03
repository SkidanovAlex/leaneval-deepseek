import Mathlib
import Submission.Work.Peluse.Prop36SW.PeelData

/-!
# Averaging over the peeled parameter type

`Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀` is the dependent sigma type

`Σ ab : {a // a ∈ A} × {b // b ∈ paramBox M₂}, (j : Fin t') → c[L] × c[L]`

with `L = ⌊γ'M₁M₂⌋` and `c = p s₀.1 a`.  This module shows that the uniform average over it is the
iterated uniform average over its three components: it is the Fubini/cardinality identity behind
"one application of `PeluseLadderA` followed by the peel of the long directions averages the
parameter family".

The only arithmetic input is `p s₀.1 a ≠ 0` (`hp`), which makes the arithmetic progression
`c[L] = {c, 2c, …, Lc}` have exactly `L` elements; the `L^{2t'}` in the statement is the
cardinality of the block `(c[L] × c[L])^{t'}` of shifts.
-/

open scoped BigOperators

namespace Work.Peluse.Prop36SW

open Work.Peluse.UControl

/-- The arithmetic progression `c[L]` has exactly `L` elements when its step is nonzero. -/
private lemma card_arithIcc (c : ℤ) (L : ℕ) (hc : c ≠ 0) :
    (Work.Peluse.arithIcc c L).card = L := by
  rw [Work.Peluse.arithIcc, Finset.card_image_of_injective _ (fun n m h => ?_), Nat.card_Icc]
  · simp
  · exact_mod_cast mul_left_cancel₀ hc h

/-- The block of `t'` pairs of shifts has cardinality `L ^ (2 * t')`. -/
private lemma card_sh (c : ℤ) (L t' : ℕ) (hc : c ≠ 0) :
    Fintype.card ((j : Fin t') → ↥(Work.Peluse.arithIcc c L) × ↥(Work.Peluse.arithIcc c L))
      = L ^ (2 * t') := by
  have h2 : ∀ _j : Fin t',
      Fintype.card (↥(Work.Peluse.arithIcc c L) × ↥(Work.Peluse.arithIcc c L)) = L ^ 2 := by
    intro j
    rw [Fintype.card_prod, Fintype.card_coe, card_arithIcc c L hc]
    ring
  rw [Fintype.card_pi, Finset.prod_congr rfl (fun j _ => h2 j), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul]

/-- Fubini for a two-step dependent product: summing over the subtype of a finset is summing over
the finset. -/
private lemma sum_subtype_sum {P Q : Type} (A : Finset P) (Box : Finset Q)
    (Sh : P → Type) [∀ a, Fintype (Sh a)] (f : (a : P) → Q → Sh a → ℝ) :
    (∑ a : ↥A, ∑ b : ↥Box, ∑ sh : Sh a.1, f a.1 b.1 sh)
      = ∑ a ∈ A, ∑ b ∈ Box, ∑ sh : Sh a, f a b sh := by
  have hX : ∀ a : P, (∑ b : ↥Box, ∑ sh : Sh a, f a b.1 sh) = ∑ b ∈ Box, ∑ sh : Sh a, f a b sh :=
    fun a => (Finset.sum_subtype Box (fun x => Iff.rfl) (fun b => ∑ sh : Sh a, f a b sh)).symm
  calc (∑ a : ↥A, ∑ b : ↥Box, ∑ sh : Sh a.1, f a.1 b.1 sh)
      = ∑ a : ↥A, ∑ b ∈ Box, ∑ sh : Sh a.1, f a.1 b sh := by
        apply Finset.sum_congr rfl
        intro a _
        exact hX a.1
    _ = ∑ a ∈ A, ∑ b ∈ Box, ∑ sh : Sh a, f a b sh :=
        (Finset.sum_subtype A (fun x => Iff.rfl) (fun a => ∑ b ∈ Box, ∑ sh : Sh a, f a b sh)).symm

theorem peelParamAverage {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} [DecidableEq P]
    (p : ι → P → ℤ) (M₁ M₂ : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1))
    (hp : ∀ a ∈ A, p s₀.1 a ≠ 0)
    (Φ : (a : P) → (b : Work.Peluse.UControl.Slot ι (fun _ => 1) → ℤ) →
        ((j : Fin t') →
            ↥(Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) ×
            ↥(Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)) → ℝ) :
    ((Fintype.card (Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀) : ℝ))⁻¹ *
        (∑ q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀,
          Φ q.1.1.1 q.1.2.1 q.2)
      = ((A.card : ℝ))⁻¹ *
          (((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂).card : ℝ))⁻¹ *
          (((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ))⁻¹ ^ (2 * t') *
          ∑ a ∈ A, ∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂,
            ∑ sh : (j : Fin t') →
                ↥(Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) ×
                ↥(Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat),
              Φ a b sh := by
  classical
  -- The uniform average over `PeelParam` unwinds to the iterated average over `A`, `paramBox M₂`
  -- and the shift block.
  have hsum : (∑ q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀,
          Φ q.1.1.1 q.1.2.1 q.2)
      = ∑ a ∈ A, ∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂,
            ∑ sh : (j : Fin t') →
                ↥(Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) ×
                ↥(Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat),
              Φ a b sh := by
    rw [Fintype.sum_sigma]
    dsimp only
    rw [Fintype.sum_prod_type]
    dsimp only
    exact sum_subtype_sum A (Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂) _ Φ
  -- The cardinality of `PeelParam` is the product of the cardinalities of the three components.
  have hcard : Fintype.card (Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀)
      = A.card * (Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂).card *
        ((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) ^ (2 * t') := by
    rw [Fintype.card_sigma]
    have h : ∀ ab : {a : P // a ∈ A} ×
        {b : Slot ι (fun _ => 1) → ℤ // b ∈ paramBox (k := fun _ : ι => 1) M₂},
        Fintype.card ((j : Fin t') →
            ↥(arithIcc (p s₀.1 ab.1.1) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) ×
            ↥(arithIcc (p s₀.1 ab.1.1) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat))
          = ((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) ^ (2 * t') :=
      fun ab => card_sh _ _ t' (hp _ ab.1.2)
    simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_coe]
    ring
  rw [hsum, hcard]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, mul_inv, mul_inv, inv_pow]

end Work.Peluse.Prop36SW
