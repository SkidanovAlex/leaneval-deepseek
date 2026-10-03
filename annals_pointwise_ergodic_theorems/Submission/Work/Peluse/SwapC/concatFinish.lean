import Mathlib
import Submission.Work.Peluse.SwapC.peelBack

open scoped BigOperators

set_option linter.style.haveILetI false

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-!
# The "finish" of `Work.Peluse.SwapC.concatStep`

The expansion step (`Work.Peluse.SwapC.expansion`) produces, from the hypothesis of KKL Lemma 6.1,

  `δ ^ 2 * |S| ≤ 3 * |S| * avg_j (Zm j) ^ (1/2^{2s})`,

i.e. `δ²/3 ≤ avg_j (Zm j)^{1/p}` with `p = 2^{2s}`.  The box-norm identification of the
concatenation (`Work.Peluse.SwapC.peelBack`) says

  `avg_j (Zm j) = avg_p pbox (2s+1) (concatenated slots) p`,

so the power-mean inequality `(avg y^{1/p})^p ≤ avg y` (`pow_mean_avg_le`) upgrades the expansion
into the conclusion of the node with the explicit constants `C = 3^{-2^{2s}}`, `e = 2^{2s+1}`.

Nothing here depends on Gowers–Cauchy–Schwarz: it is the bookkeeping that turns the *expansion* into
the *node's conclusion*.
-/

/-- `avg` is invariant under replacing the index type by an equivalent one. -/
private lemma avg_equiv {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (g : B → ℝ) :
    avg (fun a : A => g (e a)) = avg g := by
  rw [avg, avg, Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e (fun a => g (e a)) g (fun a => rfl)

/-- `avg` respects pointwise equality. -/
private lemma avg_congr {ι : Type} [Fintype ι] {F G : ι → ℝ} (h : ∀ i, F i = G i) : avg F = avg G := by
  rw [avg, avg]
  exact congrArg (fun x => ((Fintype.card ι : ℝ))⁻¹ * x) (Finset.sum_congr rfl fun i _ => h i)

/-- `avg` over a product type is the iterated `avg` (with no nonemptiness hypotheses). -/
private lemma avg_prod' {A B : Type} [Fintype A] [Fintype B] (F : A × B → ℝ) :
    avg F = avg (fun a : A => avg (fun b : B => F (a, b))) := by
  simp only [avg, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_inv_rev]
  ring

/-- `avg` over `A × B × C`, split into the outer pair and the last factor. -/
private lemma avg_prod_assoc {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (g : A × B × C → ℝ) :
    avg g = avg (fun p : A × B => avg (fun c : C => g (p.1, p.2, c))) := by
  have h1 : avg g = avg (fun x : (A × B) × C => g (Equiv.prodAssoc A B C x)) :=
    (avg_equiv (Equiv.prodAssoc A B C) g).symm
  rw [h1, avg_prod']
  refine avg_congr fun p => ?_
  refine avg_congr fun c => ?_
  exact congrArg g (Equiv.prodAssoc_apply A B C (p, c))

theorem concatFinish {I : Type} [Fintype I] [Nonempty I] (s M N : ℕ) (hs : 1 ≤ s) (qH : I → ℤ)
    (q₁ q₂ : I → Fin s → ℤ) (δ : ℝ) (f : ℤ → ℂ) (hδ : 0 < δ) (hf : Work.Peluse.FinSuppZ f)
    (hexp : δ ^ 2 * ((Work.Peluse.symIcc N).card : ℝ) ≤ 3 * ((Work.Peluse.symIcc N).card : ℝ) *
      Work.Peluse.LadderP.Swap.avg (fun j : I × I × Fin M × Fin M × Fin M × Fin M =>
        (Work.Peluse.SwapC.Zm s M N qH q₁ q₂ f j.1 j.2.1 j.2.2.1 j.2.2.2.1 j.2.2.2.2.1 j.2.2.2.2.2)
          ^ (1 / (2 : ℝ) ^ (2 * s)))) :
    (δ ^ 2 / 3) ^ ((2 : ℝ) ^ (2 * s))
      ≤ Work.Peluse.LadderP.Swap.avg (fun p : I × I => Work.Peluse.LadderP.Swap.pbox (s + s + 1)
          (Fin.snoc (Fin.append (q₁ p.1) (q₁ p.2)) (qH p.2))
          (Fin.snoc (Fin.append (q₂ p.1) (q₂ p.2)) (qH p.1)) M (Work.Peluse.symIcc N) f) := by
  classical
  have hL1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * s) := one_le_pow₀ (by norm_num)
  have hL0 : (0 : ℝ) < (2 : ℝ) ^ (2 * s) := lt_of_lt_of_le zero_lt_one hL1
  have hCpos : (0 : ℝ) < ((symIcc N).card : ℝ) := by
    have h : 0 < (symIcc N).card :=
      Finset.card_pos.mpr ⟨0, by rw [mem_symIcc_iff]; simp⟩
    exact_mod_cast h
  -- the hypothesis, normalised: `δ²/3 ≤ avg_j (Zm j)^{1/p}`
  have hδ3 : δ ^ 2 / 3 ≤ avg (fun j : I × I × Fin M × Fin M × Fin M × Fin M =>
        (Zm s M N qH q₁ q₂ f j.1 j.2.1 j.2.2.1 j.2.2.2.1 j.2.2.2.2.1 j.2.2.2.2.2)
          ^ (1 / (2 : ℝ) ^ (2 * s))) := by
    nlinarith [hexp, hCpos]
  rcases isEmpty_or_nonempty (I × I × Fin M × Fin M × Fin M × Fin M) with hempty | hne
  · -- degenerate case: the index type is empty, so the hypothesis forces `δ = 0`
    haveI := hempty
    have havg0 : avg (fun j : I × I × Fin M × Fin M × Fin M × Fin M =>
        (Zm s M N qH q₁ q₂ f j.1 j.2.1 j.2.2.1 j.2.2.2.1 j.2.2.2.2.1 j.2.2.2.2.2)
          ^ (1 / (2 : ℝ) ^ (2 * s))) = 0 := by
      simp [avg]
    rw [havg0, mul_zero] at hexp
    have hδ0 : δ = 0 := by
      have h2 : δ ^ 2 ≤ 0 := by nlinarith [hexp, hCpos]
      nlinarith [sq_nonneg δ]
    subst hδ0
    rw [show (0 : ℝ) ^ 2 / 3 = 0 by norm_num, Real.zero_rpow (ne_of_gt hL0)]
    exact avg_nonneg fun p => pbox_nonneg (s + s + 1) _ _ M (symIcc N) f
  · -- main case: Jensen on the nonempty index type, then `peelBack`
    haveI := hne
    have hJ := Work.Peluse.Holds.ExpPET.pow_le_avg_of_le_avg_rpow
      (s := (Finset.univ : Finset (I × I × Fin M × Fin M × Fin M × Fin M)))
      Finset.univ_nonempty (p := (2 : ℝ) ^ (2 * s)) (δ := δ ^ 2 / 3) hL1 (by positivity)
      (fun j => Zm s M N qH q₁ q₂ f j.1 j.2.1 j.2.2.1 j.2.2.2.1 j.2.2.2.2.1 j.2.2.2.2.2)
      (fun j _ => norm_nonneg _)
      (by simpa only [avg, Finset.card_univ] using hδ3)
    have hJ' : (δ ^ 2 / 3) ^ ((2 : ℝ) ^ (2 * s))
        ≤ avg (fun j : I × I × Fin M × Fin M × Fin M × Fin M =>
            Zm s M N qH q₁ q₂ f j.1 j.2.1 j.2.2.1 j.2.2.2.1 j.2.2.2.2.1 j.2.2.2.2.2) := by
      simpa only [avg, Finset.card_univ] using hJ
    -- identify the average of `Zm` with the average of the concatenated `pbox`
    have hpeel : avg (fun j : I × I × Fin M × Fin M × Fin M × Fin M =>
          Zm s M N qH q₁ q₂ f j.1 j.2.1 j.2.2.1 j.2.2.2.1 j.2.2.2.2.1 j.2.2.2.2.2)
        = avg (fun p : I × I => pbox (s + s + 1)
            (Fin.snoc (Fin.append (q₁ p.1) (q₁ p.2)) (qH p.2))
            (Fin.snoc (Fin.append (q₂ p.1) (q₂ p.2)) (qH p.1)) M (symIcc N) f) := by
      have h1 : avg (fun j : I × I × Fin M × Fin M × Fin M × Fin M =>
            Zm s M N qH q₁ q₂ f j.1 j.2.1 j.2.2.1 j.2.2.2.1 j.2.2.2.2.1 j.2.2.2.2.2)
          = avg (fun p : I × I => avg (fun c : Fin M × Fin M × Fin M × Fin M =>
              Zm s M N qH q₁ q₂ f p.1 p.2 c.1 c.2.1 c.2.2.1 c.2.2.2)) :=
        avg_prod_assoc (fun j : I × I × Fin M × Fin M × Fin M × Fin M =>
          Zm s M N qH q₁ q₂ f j.1 j.2.1 j.2.2.1 j.2.2.2.1 j.2.2.2.2.1 j.2.2.2.2.2)
      rw [h1]
      refine avg_congr fun p => ?_
      exact peelBack s M N hs qH q₁ q₂ p f hf
    rw [hpeel] at hJ'
    exact hJ'

end

end Work.Peluse.SwapC
