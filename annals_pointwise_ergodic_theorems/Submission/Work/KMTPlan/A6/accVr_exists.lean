/-
# An "accumulating variation" majorant for a finite family of `L^r`-norms

Given a measure `μ`, an exponent `R > 0`, an exponent `r ≥ 0` and a family of functions
`g : ℕ → X → ℂ`, this file produces a monotone sequence `a : ℕ → ℝ≥0∞` with the two properties

* `(a j) ^ (1/R) ≤ V` for `j ≤ K`, where `V` is the *free* `R`-variation of the family `g`
  (the supremum, over all nondecreasing finite chains `k` in `ℕ`, of the `ℓ^R`-norm
  `(∑_i ‖g (k (i+1)) - g (k i)‖_r ^ R) ^ (1/R)`);
* `a p + ‖g q - g p‖_r ^ R ≤ a q` for `p ≤ q ≤ K`.

The construction is the natural one: `a j` is the supremum, over all nondecreasing chains
`k : Fin (J+1) → ℕ` ending at `j`, of the `R`-th power of the `ℓ^R`-norm of the successive
jumps `g (k (i+1)) - g (k i)`.  The second property is then the *chain extension* trick:
append the point `q` to a chain ending at `p`, which adds exactly the jump `g q - g p`; the
first is the observation that such a chain is one of the chains over which `V` is defined.
-/
import Mathlib

namespace Work.KMTPlan.A6

open scoped ENNReal

private lemma rpow_one_div_mul_cancel {R : ℝ} (hR : R ≠ 0) (x : ENNReal) :
    (x ^ (1 / R)) ^ R = x := by
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hR, ENNReal.rpow_one]

private lemma rpow_mul_one_div_cancel {R : ℝ} (hR : R ≠ 0) (x : ENNReal) :
    (x ^ R) ^ (1 / R) = x := by
  rw [← ENNReal.rpow_mul, one_div, mul_inv_cancel₀ hR, ENNReal.rpow_one]

/-- If `k : Fin (n+1) → ℕ` is nondecreasing and `k (last n) ≤ c`, then appending `c` to `k`
keeps it nondecreasing. -/
private lemma monotone_snoc {n : ℕ} {k : Fin (n+1) → ℕ} (hk : Monotone k) {c : ℕ}
    (hc : k (Fin.last n) ≤ c) : Monotone (Fin.snoc k c) := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hk (Fin.castSucc_le_castSucc_iff.mp hij)
    · rw [Fin.snoc_castSucc, Fin.snoc_last]
      exact (hk (Fin.le_last i')).trans hc
  · have hji : j = Fin.last (n+1) := le_antisymm (Fin.le_last j) hij
    rw [hji, Fin.snoc_last]

/-- The `ℓ^R`-sum of the jumps of a chain splits along the appended last point. -/
private lemma sum_snoc {n : ℕ} (k : Fin (n+1) → ℕ) (c : ℕ) (R : ℝ)
    (d : ℕ → ℕ → ENNReal) :
    (∑ i : Fin (n+1),
        d ((Fin.snoc k c : Fin (n+2) → ℕ) i.succ) ((Fin.snoc k c : Fin (n+2) → ℕ) i.castSucc) ^ R)
      = (∑ i : Fin n, d (k i.succ) (k i.castSucc) ^ R) + d c (k (Fin.last n)) ^ R := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]

/-- The index type of nondecreasing chains `k : Fin (J+1) → ℕ` with `k (last J) = j`. -/
private def accChain (j : ℕ) : Type :=
  Σ J : ℕ, {k : Fin (J+1) → ℕ // Monotone k ∧ k (Fin.last J) = j}

private instance instNonemptyAccChain (j : ℕ) : Nonempty (accChain j) :=
  ⟨⟨0, ⟨fun _ => j, ⟨monotone_const, rfl⟩⟩⟩⟩

theorem accVr_exists {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X) (R : ℝ)
    (hR : 0 < R) (r : NNReal) (g : ℕ → X → ℂ) (K : ℕ) :
    ∃ a : ℕ → ENNReal,
      Monotone a ∧
      (∀ j, j ≤ K → (a j) ^ (1 / R) ≤
        ⨆ (J : ℕ) (k : Fin (J + 1) → ℕ), ⨆ (_ : Monotone k),
          (∑ i : Fin J,
            (MeasureTheory.eLpNorm (fun x => g (k i.succ) x - g (k i.castSucc) x)
              (r : ENNReal) μ) ^ R) ^ (1 / R)) ∧
      (∀ p q, p ≤ q → q ≤ K →
        a p + (MeasureTheory.eLpNorm (fun x => g q x - g p x) (r : ENNReal) μ) ^ R ≤ a q) := by
  classical
  -- The jump norm and the `ℓ^R`-sum of the jumps of a chain.
  let d : ℕ → ℕ → ENNReal :=
    fun s t => MeasureTheory.eLpNorm (fun x => g s x - g t x) (r : ENNReal) μ
  let S : (J : ℕ) → (Fin (J+1) → ℕ) → ENNReal :=
    fun J k => ∑ i : Fin J, (d (k i.succ) (k i.castSucc)) ^ R
  -- The accumulating variation: the supremum of `S` over chains ending at `j`.
  let a : ℕ → ENNReal := fun j => ⨆ (x : accChain j), S x.1 x.2.1
  refine ⟨a, ?_, ?_, ?_⟩
  · -- monotonicity: extend a chain ending at `j` by the point `j' ≥ j`
    intro j j' hjj'
    refine iSup_le fun x => ?_
    obtain ⟨J, k, hk, hl⟩ := x
    have hc : k (Fin.last J) ≤ j' := by rw [hl]; exact hjj'
    have hk' : Monotone (Fin.snoc k j') := monotone_snoc hk hc
    have hl' : (Fin.snoc k j' : Fin (J+2) → ℕ) (Fin.last (J+1)) = j' := by rw [Fin.snoc_last]
    have hsum : S (J+1) (Fin.snoc k j') = S J k + d j' (k (Fin.last J)) ^ R := by
      simpa only [S] using sum_snoc k j' R d
    calc S J k ≤ S (J+1) (Fin.snoc k j') := by rw [hsum]; exact le_self_add
      _ ≤ a j' := le_iSup (fun x : accChain j' => S x.1 x.2.1)
          ⟨J+1, ⟨(Fin.snoc k j' : Fin (J+2) → ℕ), hk', hl'⟩⟩
  · -- the `(1/R)`-th power of `a j` is bounded by the free `R`-variation
    intro j _hjK
    have hsup : a j ≤ (⨆ (J : ℕ) (k : Fin (J+1) → ℕ), ⨆ (_ : Monotone k),
        (S J k) ^ (1 / R)) ^ R := by
      refine iSup_le fun x => ?_
      obtain ⟨J, k, hk, _hl⟩ := x
      have h1 : (S J k) ^ (1/R) ≤
          ⨆ (J : ℕ) (k : Fin (J+1) → ℕ), ⨆ (_ : Monotone k), (S J k) ^ (1/R) :=
        le_iSup_of_le J (le_iSup_of_le k (le_iSup_of_le hk le_rfl))
      calc S J k = ((S J k) ^ (1/R)) ^ R := (rpow_one_div_mul_cancel hR.ne' _).symm
        _ ≤ _ := ENNReal.rpow_le_rpow h1 (le_of_lt hR)
    calc (a j) ^ (1 / R)
        ≤ ((⨆ (J : ℕ) (k : Fin (J+1) → ℕ), ⨆ (_ : Monotone k), (S J k) ^ (1 / R)) ^ R)
            ^ (1 / R) :=
          ENNReal.rpow_le_rpow hsup (le_of_lt (one_div_pos.mpr hR))
      _ = ⨆ (J : ℕ) (k : Fin (J+1) → ℕ), ⨆ (_ : Monotone k), (S J k) ^ (1 / R) :=
          rpow_mul_one_div_cancel hR.ne' _
  · -- the accumulation condition: append the point `q` to a chain ending at `p ≤ q`
    intro p q hpq _hqK
    have hstep : a p + d q p ^ R = ⨆ (x : accChain p), (S x.1 x.2.1 + d q p ^ R) :=
      ENNReal.iSup_add (fun x : accChain p => S x.1 x.2.1)
    rw [hstep]
    refine iSup_le fun x => ?_
    obtain ⟨J, k, hk, hl⟩ := x
    have hc : k (Fin.last J) ≤ q := by rw [hl]; exact hpq
    have hk' : Monotone (Fin.snoc k q) := monotone_snoc hk hc
    have hl' : (Fin.snoc k q : Fin (J+2) → ℕ) (Fin.last (J+1)) = q := by rw [Fin.snoc_last]
    have hsum : S (J+1) (Fin.snoc k q) = S J k + d q (k (Fin.last J)) ^ R := by
      simpa only [S] using sum_snoc k q R d
    have hEq : S J k + d q p ^ R = S (J+1) (Fin.snoc k q) := by
      rw [hsum, hl]
    rw [hEq]
    exact le_iSup (fun x : accChain q => S x.1 x.2.1)
      ⟨J+1, ⟨(Fin.snoc k q : Fin (J+2) → ℕ), hk', hl'⟩⟩

end Work.KMTPlan.A6
