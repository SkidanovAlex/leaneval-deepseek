import Mathlib
import Submission.Work.LinnikAreas.BGTZ.sum_divisors_card_div_le
import Submission.Work.LinnikAreas.harmonic_sum_le_one_add_log

namespace Work.LinnikAreas.BGTZ.E

open scoped BigOperators

/-- `ω n = #n.primeFactors`, i.e. `ArithmeticFunction.cardDistinctFactors` agrees with the number
of distinct prime factors of `n`. -/
private lemma omega_eq_primeFactors_card (n : ℕ) :
    ArithmeticFunction.cardDistinctFactors n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors]

/-- There are `3 ^ ω n` ordered triples of positive integers with product `n`, when `n` is
squarefree. Equivalently, the cardinality of `Nat.finMulAntidiag 3 n` is `(3 : ℝ) ^ ω n`. -/
private lemma card_finMulAntidiag_three (n : ℕ) (hn : Squarefree n) :
    ((Nat.finMulAntidiag 3 n).card : ℝ) = (3 : ℝ) ^ n.primeFactors.card := by
  rw [Nat.card_finMulAntidiag_of_squarefree hn, omega_eq_primeFactors_card]
  push_cast
  rfl

/-- The reciprocal of a product of a `Fin 3`-tuple is the product of the reciprocals. -/
private lemma prod_recip_eq (f : Fin 3 → ℕ) :
    ∏ i, (1 : ℝ) / (f i : ℝ) = (1 : ℝ) / ((∏ i, f i : ℕ) : ℝ) := by
  simp only [one_div]
  rw [Finset.prod_inv_distrib, Nat.cast_prod]

/-- For squarefree `d`, the tuple-sum `∑_{abc = d} 1/(abc)` equals `3 ^ ω d / d`. -/
private lemma sum_finMulAntidiag_eq (d : ℕ) (hdsq : Squarefree d) :
    ∑ f ∈ Nat.finMulAntidiag 3 d, (∏ i : Fin 3, (1 : ℝ) / (f i : ℝ))
      = (3 : ℝ) ^ d.primeFactors.card / (d : ℝ) := by
  rw [← card_finMulAntidiag_three d hdsq]
  have h : ∑ f ∈ Nat.finMulAntidiag 3 d, (∏ i : Fin 3, (1 : ℝ) / (f i : ℝ))
      = ∑ f ∈ Nat.finMulAntidiag 3 d, (1 : ℝ) / (d : ℝ) := by
    apply Finset.sum_congr rfl
    intro f hf
    rw [prod_recip_eq f, Nat.prod_eq_of_mem_finMulAntidiag hf]
  rw [h, Finset.sum_const, nsmul_eq_mul, mul_one_div]

private lemma mem_finMulAntidiag_iff {d : ℕ} (hd : d ≠ 0) (f : Fin 3 → ℕ) :
    f ∈ Nat.finMulAntidiag 3 d ↔ ∏ i, f i = d := by
  rw [Nat.mem_finMulAntidiag]
  exact ⟨fun h => h.1, fun h => ⟨h, hd⟩⟩

/-- Every tuple with product `d ≤ Y` has all its entries in `[1, Y]`. -/
private lemma finMulAntidiag_subset_box {d Y : ℕ} (hd : d ∈ Finset.Icc 1 Y) :
    Nat.finMulAntidiag 3 d ⊆ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc 1 Y) := by
  intro f hf
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  obtain ⟨hd1, hdY⟩ := Finset.mem_Icc.mp hd
  refine ⟨?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_zero_of_mem_finMulAntidiag hf i)
  · calc f i ≤ d := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_finMulAntidiag hf i)
      _ ≤ Y := hdY

/-- The triple box sum `∑_{a,b,c ≤ Y} 1/(abc)` is the cube of the harmonic sum. -/
private lemma cube_sum (Y : ℕ) :
    ∑ f ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc 1 Y),
      (∏ i : Fin 3, (1 : ℝ) / (f i : ℝ))
      = (∑ m ∈ Finset.Icc 1 Y, (1 : ℝ) / (m : ℝ)) ^ 3 := by
  rw [Finset.sum_prod_piFinset (s := Finset.Icc 1 Y)
      (g := fun (_ : Fin 3) (j : ℕ) => (1 : ℝ) / (j : ℝ))]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem sum_sqfree_three_pow_div_le (Y : ℕ) :
    ∑ d ∈ (Finset.Icc 1 Y).filter Squarefree, (3 : ℝ) ^ d.primeFactors.card / (d : ℝ)
      ≤ (1 + Real.log (Y : ℝ)) ^ 3 := by
  -- The core estimate: the squarefree sum is bounded by the cube of the harmonic sum.
  have key : ∑ d ∈ (Finset.Icc 1 Y).filter Squarefree, (3 : ℝ) ^ d.primeFactors.card / (d : ℝ)
      ≤ (∑ m ∈ Finset.Icc 1 Y, (1 : ℝ) / (m : ℝ)) ^ 3 := by
    set B : Finset ℕ := Finset.Icc 1 Y with hB
    set H : ℝ := ∑ m ∈ B, (1 : ℝ) / (m : ℝ) with hH
    set g : (Fin 3 → ℕ) → ℝ := fun f => ∏ i : Fin 3, (1 : ℝ) / (f i : ℝ) with hg
    set box : Finset (Fin 3 → ℕ) := Fintype.piFinset (fun _ : Fin 3 => B) with hboxdef
    have hg_nonneg : ∀ f : Fin 3 → ℕ, 0 ≤ g f := by
      intro f
      rw [hg]
      exact Finset.prod_nonneg (fun i _ => by positivity)
    -- Rewrite each term `3 ^ ω d / d` as a sum over triples with product `d`.
    have stepA : ∑ d ∈ B.filter Squarefree, (3 : ℝ) ^ d.primeFactors.card / (d : ℝ)
        = ∑ d ∈ B.filter Squarefree, ∑ f ∈ Nat.finMulAntidiag 3 d, g f := by
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨hdmem, hdsq⟩ := Finset.mem_filter.mp hd
      rw [hg]
      exact (sum_finMulAntidiag_eq d hdsq).symm
    have hbox : ∑ f ∈ box, g f = H ^ 3 := by
      rw [hboxdef, hg, hH, hB]
      exact cube_sum Y
    have stepB : ∑ d ∈ B.filter Squarefree, ∑ f ∈ Nat.finMulAntidiag 3 d, g f ≤ H ^ 3 := by
      calc ∑ d ∈ B.filter Squarefree, ∑ f ∈ Nat.finMulAntidiag 3 d, g f
          ≤ ∑ d ∈ B, ∑ f ∈ Nat.finMulAntidiag 3 d, g f := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro d hd hnd
            exact Finset.sum_nonneg (fun f hf => hg_nonneg f)
        _ = ∑ d ∈ B, ∑ f ∈ box, (if f ∈ Nat.finMulAntidiag 3 d then g f else 0) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hd' : d ∈ Finset.Icc 1 Y := by rw [hB] at hd; exact hd
            have hsub : Nat.finMulAntidiag 3 d ⊆ box := by
              rw [hboxdef, hB]
              exact finMulAntidiag_subset_box hd'
            have h1 : ∑ f ∈ Nat.finMulAntidiag 3 d, g f
                = ∑ f ∈ Nat.finMulAntidiag 3 d,
                    (if f ∈ Nat.finMulAntidiag 3 d then g f else 0) :=
              Finset.sum_congr rfl (fun f hf => by rw [if_pos hf])
            have h2 : ∑ f ∈ Nat.finMulAntidiag 3 d,
                  (if f ∈ Nat.finMulAntidiag 3 d then g f else 0)
                = ∑ f ∈ box, (if f ∈ Nat.finMulAntidiag 3 d then g f else 0) :=
              Finset.sum_subset hsub (fun x hx hxs => by simp [hxs])
            exact h1.trans h2
        _ = ∑ f ∈ box, ∑ d ∈ B, (if f ∈ Nat.finMulAntidiag 3 d then g f else 0) :=
            Finset.sum_comm
        _ ≤ ∑ f ∈ box, g f := by
            apply Finset.sum_le_sum
            intro f hf
            -- for fixed `f`, at most one `d ∈ B` gives a nonzero contribution
            have hrew : ∑ d ∈ B, (if f ∈ Nat.finMulAntidiag 3 d then g f else 0)
                = ∑ d ∈ B, (if d = ∏ i, f i then g f else 0) := by
              apply Finset.sum_congr rfl
              intro d hd
              apply if_congr _ rfl rfl
              rw [mem_finMulAntidiag_iff ?_ f]
              exact eq_comm
              have := Finset.mem_Icc.mp (hB ▸ hd)
              omega
            rw [hrew, Finset.sum_ite_eq']
            split_ifs with h
            · exact le_rfl
            · exact hg_nonneg f
        _ = H ^ 3 := hbox
    rw [stepA]
    exact stepB
  have hHle : ∑ m ∈ Finset.Icc 1 Y, (1 : ℝ) / (m : ℝ) ≤ 1 + Real.log (Y : ℝ) :=
    Work.LinnikAreas.harmonic_sum_le_one_add_log Y
  have hH0 : 0 ≤ ∑ m ∈ Finset.Icc 1 Y, (1 : ℝ) / (m : ℝ) := by
    apply Finset.sum_nonneg
    intro m _
    positivity
  exact key.trans (pow_le_pow_left₀ hH0 hHle 3)

end Work.LinnikAreas.BGTZ.E
