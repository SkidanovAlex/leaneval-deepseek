import Mathlib
import Submission.Work.Peluse.Ulower.boxSumPow_split
import Submission.Work.Peluse.Ulower.dualFn_tsum_le
import Submission.Work.Peluse.Ulower.iterDelta_finsupp
import Submission.Work.Peluse.Ulower.ssA.GapLocalAna
import Submission.Work.Peluse.Ulower.card_large_values
import Submission.Work.Peluse.Ulower.supportIn_tsum_le
import Submission.Work.Peluse.Ulower.iterDelta_tsum_le

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## Elementary lemmas -/

/-- Membership in the symmetric interval `symIcc L = [-L,L]`, in terms of `Int.natAbs`. -/
private lemma mem_symIcc_iff_ss {L : ℕ} {x : ℤ} : x ∈ symIcc L ↔ x.natAbs ≤ L := by
  rw [symIcc, Finset.mem_Icc]
  constructor
  · intro h
    have h1 : |x| ≤ (L : ℤ) := abs_le.mpr h
    rw [← Int.natCast_natAbs] at h1
    exact_mod_cast h1
  · intro hx
    have h1 : (x.natAbs : ℤ) ≤ (L : ℤ) := by exact_mod_cast hx
    rw [Int.natCast_natAbs] at h1
    exact abs_le.mp h1

/-- The cardinality of the symmetric interval. -/
private lemma symIcc_card (L : ℕ) : (symIcc L).card = 2 * L + 1 := by
  rw [symIcc, Int.card_Icc]
  have h : (L : ℤ) + 1 - (-(L : ℤ)) = ((2 * L + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- A finitely supported function vanishes off an explicit `Finset`. -/
private lemma finsupp_exists_finset {F : ℤ → ℂ} (h : FinSuppZ F) :
    ∃ s : Finset ℤ, ∀ x : ℤ, x ∉ s → F x = 0 := by
  obtain ⟨N, hN⟩ := h
  refine ⟨symIcc N, fun x hx => hN x ?_⟩
  by_contra hcon
  exact hx (mem_symIcc_iff_ss.mpr (not_lt.mp hcon))

/-- `FinSuppZ` gives summability of the norm. -/
private lemma summable_norm_of_finsupp {F : ℤ → ℂ} (h : FinSuppZ F) :
    Summable (fun x : ℤ => ‖F x‖) := by
  obtain ⟨s, hs⟩ := finsupp_exists_finset h
  exact summable_of_ne_finset_zero (s := s) (fun x hx => by simp [hs x hx])

/-- The cardinality of the arithmetic-progression set `arithIcc c D = c[1,D]`. -/
private lemma arithIcc_card {c : ℤ} (hc : c ≠ 0) (D : ℕ) : (arithIcc c D).card = D := by
  have hinj : Function.Injective (fun n : ℕ => c * (n : ℤ)) := by
    intro a b hab
    have h : (a : ℤ) = (b : ℤ) := mul_left_cancel₀ hc hab
    exact_mod_cast h
  rw [arithIcc, Finset.card_image_of_injective _ hinj, Nat.card_Icc]
  omega

/-- The leading coefficient of a polynomial of degree `≥ 2` is nonzero. -/
private lemma leadingCoeff_ne_zero_of_two_le_natDegree {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree) :
    P.leadingCoeff ≠ 0 := by
  intro h
  have hP : P = 0 := Polynomial.leadingCoeff_eq_zero.mp h
  rw [hP] at hd
  simp at hd

/-! ## The iterated peel identity -/

/-- The shift tuple underlying a tuple of pairs of shifts. -/
private def pairVal {A : Finset ℤ} {k : ℕ} (t : Fin k → ↥A × ↥A) : Fin k → ℤ × ℤ :=
  fun i => ((t i).1.val, (t i).2.val)

/-- `DeltaP` is one `iterDelta` step with the two shifts swapped. -/
private lemma DeltaP_eq_iterDeltaStep (a b : ℤ) (F : ℤ → ℂ) :
    DeltaP a b F = iterDeltaStep (b, a) F := by
  funext x
  simp only [DeltaP, iterDeltaStep]
  rw [mul_comm]

/-- Two `iterDelta` steps commute. -/
private lemma iterDeltaStep_step_comm (p q : ℤ × ℤ) (F : ℤ → ℂ) :
    iterDeltaStep p (iterDeltaStep q F) = iterDeltaStep q (iterDeltaStep p F) := by
  funext x
  simp only [iterDeltaStep, star_mul, star_star, add_comm, add_left_comm, mul_assoc, mul_comm,
    mul_left_comm]

/-- One `iterDelta` step commutes with any iterate of `iterDelta`. -/
private lemma iterDeltaStep_iterDelta_comm {k : ℕ} (p : ℤ × ℤ) (sh : Fin k → ℤ × ℤ)
    (F : ℤ → ℂ) :
    iterDeltaStep p (iterDelta k sh F) = iterDelta k sh (iterDeltaStep p F) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change iterDeltaStep p (iterDeltaStep (sh 0) (iterDelta k (fun i => sh i.succ) F))
        = iterDeltaStep (sh 0) (iterDelta k (fun i => sh i.succ) (iterDeltaStep p F))
      rw [iterDeltaStep_step_comm p (sh 0) (iterDelta k (fun i => sh i.succ) F), ih]

/-- The shift tuple `Fin.cons q t` picks out exactly the tuple `t` in the lower iterate. -/
private lemma iterDelta_cons_eq {k : ℕ} {A : Finset ℤ} (q : ↥A × ↥A) (t : Fin k → ↥A × ↥A)
    (F : ℤ → ℂ) :
    iterDelta k (pairVal t) (iterDeltaStep (q.1.val, q.2.val) F)
      = iterDelta (k + 1) (pairVal (Fin.cons q t)) F := by
  rw [← iterDeltaStep_iterDelta_comm]
  change iterDeltaStep (q.1.val, q.2.val) (iterDelta k (pairVal t) F)
    = iterDeltaStep ((pairVal (Fin.cons q t)) 0)
        (iterDelta k (fun i => (pairVal (Fin.cons q t)) i.succ) F)
  have h0 : (pairVal (Fin.cons q t)) 0 = (q.1.val, q.2.val) := rfl
  have hfun : (fun i : Fin k => (pairVal (Fin.cons q t)) i.succ) = pairVal t := by
    funext i
    rfl
  rw [h0, hfun]

/-- Summation over a `Fin (k+1)`-tuple splits as the sum over the head and the tail. -/
private lemma sum_over_cons {k : ℕ} {A : Finset ℤ} {M : Type*} [AddCommMonoid M]
    (g : (Fin (k + 1) → ↥A × ↥A) → M) :
    (∑ q : ↥A × ↥A, ∑ t : Fin k → ↥A × ↥A, g (Fin.cons q t))
      = ∑ u : Fin (k + 1) → ↥A × ↥A, g u := by
  have h1 : (∑ q : ↥A × ↥A, ∑ t : Fin k → ↥A × ↥A, g (Fin.cons q t))
      = ∑ x : (↥A × ↥A) × (Fin k → ↥A × ↥A), g (Fin.cons x.1 x.2) :=
    (Fintype.sum_prod_type (f := fun x : (↥A × ↥A) × (Fin k → ↥A × ↥A) =>
      g (Fin.cons x.1 x.2))).symm
  rw [h1]
  refine Finset.sum_bij (fun x _ => Fin.cons x.1 x.2) (fun x _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro x₁ _ x₂ _ h
    refine Prod.ext ?_ ?_
    · have h0 := congrFun h 0
      simpa [Fin.cons_zero] using h0
    · funext i
      have hi := congrFun h i.succ
      simpa [Fin.cons_succ] using hi
  · intro u _
    exact ⟨(u 0, fun i => u i.succ), Finset.mem_univ _, Fin.cons_self_tail u⟩
  · intro x _
    rfl

/-- **The iterated peel identity.**  Peeling the uniform box sum `boxSumPow (k+2)` down to level
`2` with `boxSumPow_split` produces, for each tuple `t` of `k` shift pairs from `A × A`, the level
two box sum of the iterated difference `iterDelta k t F`. -/
private lemma peel_iter_aux : ∀ (k : ℕ) (A S : Finset ℤ) (F : ℤ → ℂ),
    boxSumPow (k + 2) (fun _ : Fin (k + 2) => A) S F
      = ((((A.card : ℂ)) ^ 2)⁻¹) ^ k *
        ∑ t : Fin k → ↥A × ↥A, boxSumPow 2 (fun _ : Fin 2 => A) S (iterDelta k (pairVal t) F) := by
  intro k
  induction k with
  | zero =>
      intro A S F
      rw [pow_zero, one_mul]
      have hconst : (∑ t : Fin 0 → ↥A × ↥A,
          boxSumPow 2 (fun _ : Fin 2 => A) S (iterDelta 0 (pairVal t) F))
          = boxSumPow 2 (fun _ : Fin 2 => A) S F := by
        rw [Finset.sum_congr rfl (fun t _ => by rw [iterDelta_zero])]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
        simp
      rw [hconst]
  | succ k ih =>
      intro A S F
      change boxSumPow ((k + 2) + 1) (fun _ : Fin ((k + 2) + 1) => A) S F
        = ((((A.card : ℂ)) ^ 2)⁻¹) ^ (k + 1) *
          ∑ u : Fin (k + 1) → ↥A × ↥A,
            boxSumPow 2 (fun _ : Fin 2 => A) S (iterDelta (k + 1) (pairVal u) F)
      rw [boxSumPow_split (k + 2) (fun _ : Fin ((k + 2) + 1) => A) S F]
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => by
        rw [DeltaP_eq_iterDeltaStep]))]
      have hinner : (∑ q : ↥A × ↥A, ∑ t : Fin k → ↥A × ↥A,
            boxSumPow 2 (fun _ : Fin 2 => A) S
              (iterDelta k (pairVal t) (iterDeltaStep (q.1.val, q.2.val) F)))
          = ∑ u : Fin (k + 1) → ↥A × ↥A,
              boxSumPow 2 (fun _ : Fin 2 => A) S (iterDelta (k + 1) (pairVal u) F) := by
        have hstep1 : (∑ q : ↥A × ↥A, ∑ t : Fin k → ↥A × ↥A,
              boxSumPow 2 (fun _ : Fin 2 => A) S
                (iterDelta k (pairVal t) (iterDeltaStep (q.1.val, q.2.val) F)))
            = ∑ q : ↥A × ↥A, ∑ t : Fin k → ↥A × ↥A,
                boxSumPow 2 (fun _ : Fin 2 => A) S
                  (iterDelta (k + 1) (pairVal (Fin.cons q t)) F) := by
          refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun t _ => ?_))
          rw [iterDelta_cons_eq q t F]
        rw [hstep1, sum_over_cons (g := fun u : Fin (k + 1) → ↥A × ↥A =>
          boxSumPow 2 (fun _ : Fin 2 => A) S (iterDelta (k + 1) (pairVal u) F))]
      rw [← Fintype.sum_prod_type (f := fun q : ↥A × ↥A => boxSumPow (k + 2)
            (fun _ : Fin (k + 2) => A) S (iterDeltaStep (q.1.val, q.2.val) F)),
        Finset.sum_congr rfl (fun q _ => ih A S (iterDeltaStep (q.1.val, q.2.val) F)),
        ← Finset.mul_sum, hinner]
      rw [pow_succ]
      ring

/-- **The level-two box norm of an iterated difference of the dual function is at most `1`.** -/
private lemma boxNormPow_two_iterDelta_le_one {P : Polynomial ℤ} {N₀ N : ℕ} {f₀ f₁ : ℤ → ℂ}
    (hN : 1 ≤ N) (hNN₀ : N ≤ N₀)
    (h0 : SupportIn f₀ N₀) (h1 : SupportIn f₁ N₀)
    (hb0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1) (hb1 : ∀ x : ℤ, ‖f₁ x‖ ≤ 1)
    (A : Finset ℤ) (k : ℕ) (sh : Fin k → ℤ × ℤ) :
    boxNormPow 2 (fun _ : Fin 2 => A) (symIcc (dSup P N₀ N))
      (iterDelta k sh (dualFn N P f₀ f₁)) ≤ 1 := by
  set F : ℤ → ℂ := dualFn N P f₀ f₁ with hF
  have hFbd : ∀ x : ℤ, ‖F x‖ ≤ 1 := by
    intro x
    rw [hF]
    exact SsA.dualFn_norm_le_one N P hb0 hb1 x
  have hFfin : FinSuppZ F := by
    rw [hF]
    exact FinSuppZ.of_supportIn
      (Work.Peluse.Tools.dualFn_supportIn (N := N₀) (M := N) (by omega) P f₀ f₁ h0 h1 hNN₀)
  have hsumF : Summable (fun x : ℤ => ‖F x‖) := summable_norm_of_finsupp hFfin
  have hgfin : FinSuppZ (iterDelta k sh F) := iterDelta_finsupp sh hFfin
  have hgbd : ∀ x : ℤ, ‖iterDelta k sh F x‖ ≤ 1 := norm_iterDelta_le_one k sh F hFbd
  have hSpos : 0 < (symIcc (dSup P N₀ N)).card := by rw [symIcc_card]; omega
  have hSposR : (0 : ℝ) < ((symIcc (dSup P N₀ N)).card : ℝ) := by exact_mod_cast hSpos
  have hbL1 := boxNormPow_le_L1 (t := 2) (by norm_num) (fun _ : Fin 2 => A) (symIcc (dSup P N₀ N))
      (iterDelta k sh F) (M := 1) zero_le_one hgbd (finsupp_exists_finset hgfin) hSpos
  have htsum : (∑' x : ℤ, ‖iterDelta k sh F x‖) ≤ ∑' x : ℤ, ‖F x‖ :=
    iterDelta_tsum_le sh F hFbd hsumF
  have hFmass : (∑' x : ℤ, ‖F x‖) ≤ ((2 * N₀ + 1 : ℕ) : ℝ) := by
    have hF1fin : FinSuppZ f₁ := FinSuppZ.of_supportIn h1
    have h3a : (∑' x : ℤ, ‖dualFn N P f₀ f₁ x‖) ≤ ∑' x : ℤ, ‖f₁ x‖ :=
      Work.Peluse.Ulower.dualFn_tsum_le hN P f₀ f₁ hb0 hF1fin
    have h3b : (∑' x : ℤ, ‖f₁ x‖) ≤ ((2 * N₀ + 1 : ℕ) : ℝ) := supportIn_tsum_le h1 hb1
    rw [hF]
    exact le_trans h3a h3b
  have hScard : ((2 * N₀ + 1 : ℕ) : ℝ) ≤ ((symIcc (dSup P N₀ N)).card : ℝ) := by
    have hNd : N₀ ≤ dSup P N₀ N := by rw [dSup]; exact Nat.le_add_right _ _
    have hNd' : (N₀ : ℝ) ≤ ((dSup P N₀ N : ℕ) : ℝ) := by exact_mod_cast hNd
    rw [symIcc_card]
    push_cast
    linarith
  have htsum' : (∑' x : ℤ, ‖iterDelta k sh F x‖) ≤ ((symIcc (dSup P N₀ N)).card : ℝ) :=
    le_trans htsum (le_trans hFmass hScard)
  calc boxNormPow 2 (fun _ : Fin 2 => A) (symIcc (dSup P N₀ N)) (iterDelta k sh F)
      ≤ 1 * (∑' x : ℤ, ‖iterDelta k sh F x‖) / ((symIcc (dSup P N₀ N)).card : ℝ) := by
        simpa using hbL1
    _ ≤ 1 := by
        rw [one_mul, div_le_one hSposR]
        exact htsum'

/-! ## The main theorem -/

theorem ss_gap_peel_many {P : Polynomial ℤ} {s : ℕ} (hs : 2 ≤ s) {N₀ N D : ℕ} {f₀ f₁ : ℤ → ℂ}
    {δ : ℝ} (hd : 2 ≤ P.natDegree) (hN : 1 ≤ N) (hN₀ : 1 ≤ N₀) (hD : 1 ≤ D)
    (hDN : (D : ℝ) ≤ (N : ℝ) ^ P.natDegree)
    (hgap : 2 * (N : ℝ) ^ P.natDegree < (N₀ : ℝ)) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (h0 : Work.Peluse.SupportIn f₀ N₀) (h1 : Work.Peluse.SupportIn f₁ N₀)
    (hb0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1) (hb1 : ∀ x : ℤ, ‖f₁ x‖ ≤ 1)
    (hδ : δ ≤ Work.Peluse.uNormPow s (Work.Peluse.arithIcc P.leadingCoeff D)
      (Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N)) (Work.Peluse.dualFn N P f₀ f₁)) :
    ∃ H : Finset (Fin (s - 2) → ℤ × ℤ),
      (∀ sh ∈ H, ∀ i, (sh i).1 ∈ Work.Peluse.arithIcc P.leadingCoeff D ∧
        (sh i).2 ∈ Work.Peluse.arithIcc P.leadingCoeff D) ∧
      (δ / 4 / (1 + (s : ℝ) + |((P.leadingCoeff : ℤ) : ℝ)|)) *
          (((Work.Peluse.arithIcc P.leadingCoeff D).card : ℝ)) ^ (2 * (s - 2)) ≤ (H.card : ℝ) ∧
      ∀ sh ∈ H, δ / 4 ≤ Work.Peluse.boxNormPow 2
        (fun _ : Fin 2 => Work.Peluse.arithIcc P.leadingCoeff D)
        (Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N))
        (Work.Peluse.Ulower.iterDelta (s - 2) sh (Work.Peluse.dualFn N P f₀ f₁)) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  set A : Finset ℤ := arithIcc P.leadingCoeff D with hA
  set S : Finset ℤ := symIcc (dSup P N₀ N) with hS
  set F : ℤ → ℂ := dualFn N P f₀ f₁ with hF
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero_of_two_le_natDegree hd
  have hAcard : A.card = D := by rw [hA]; exact arithIcc_card hlc D
  have hApos : (0 : ℝ) < (A.card : ℝ) := by
    rw [hAcard]
    exact_mod_cast hD
  have hNN₀ : N ≤ N₀ := by
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hd1 : 1 ≤ P.natDegree := by omega
    have hpow : (N : ℝ) ≤ (N : ℝ) ^ P.natDegree := by
      simpa using pow_le_pow_right₀ h1N hd1
    have hlt : (N : ℝ) < (N₀ : ℝ) := by linarith
    have hlt' : N < N₀ := by exact_mod_cast hlt
    omega
  have hFbd : ∀ x : ℤ, ‖F x‖ ≤ 1 := by
    intro x
    rw [hF]
    exact SsA.dualFn_norm_le_one N P hb0 hb1 x
  have hFfin : FinSuppZ F := by
    rw [hF]
    exact FinSuppZ.of_supportIn
      (Work.Peluse.Tools.dualFn_supportIn (N := N₀) (M := N) (by omega) P f₀ f₁ h0 h1 hNN₀)
  have hsumF : Summable (fun x : ℤ => ‖F x‖) := summable_norm_of_finsupp hFfin
  -- the peel identity
  have hpeel := peel_iter_aux k A S F
  -- the level-two box norms of the iterated differences
  set Z : (Fin k → ↥A × ↥A) → ℝ := fun t => boxNormPow 2 (fun _ : Fin 2 => A) S
      (iterDelta k (pairVal t) F) with hZ
  have hZnn : ∀ t : Fin k → ↥A × ↥A, 0 ≤ Z t := fun t => norm_nonneg _
  have hZsumm : (0 : ℝ) ≤ ∑ t : Fin k → ↥A × ↥A, Z t :=
    Finset.sum_nonneg (fun t _ => hZnn t)
  have hboxpeel : boxSumPow (k + 2) (fun _ : Fin (k + 2) => A) S F
      = (((A.card : ℂ) ^ 2)⁻¹) ^ k * ((∑ t : Fin k → ↥A × ↥A, Z t : ℝ) : ℂ) := by
    rw [hpeel]
    have hterm : ∀ t : Fin k → ↥A × ↥A,
        boxSumPow 2 (fun _ : Fin 2 => A) S (iterDelta k (pairVal t) F)
          = ((Z t : ℝ) : ℂ) := by
      intro t
      rw [hZ]
      exact Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow (t := 2) (by norm_num)
        (iterDelta_finsupp (pairVal t) hFfin)
    rw [Finset.sum_congr rfl (fun t _ => hterm t), ← Complex.ofReal_sum]
  have hδZ : δ ≤ (((A.card : ℝ) ^ 2)⁻¹) ^ k * ∑ t : Fin k → ↥A × ↥A, Z t := by
    have hnorm : ‖(((A.card : ℂ) ^ 2)⁻¹) ^ k * ((∑ t : Fin k → ↥A × ↥A, Z t : ℝ) : ℂ)‖
        = (((A.card : ℝ) ^ 2)⁻¹) ^ k * ∑ t : Fin k → ↥A × ↥A, Z t := by
      rw [norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_natCast,
        Complex.norm_of_nonneg hZsumm]
    calc δ ≤ boxNormPow (k + 2) (fun _ : Fin (k + 2) => A) S F := hδ
      _ = ‖boxSumPow (k + 2) (fun _ : Fin (k + 2) => A) S F‖ := rfl
      _ = ‖(((A.card : ℂ) ^ 2)⁻¹) ^ k * ((∑ t : Fin k → ↥A × ↥A, Z t : ℝ) : ℂ)‖ := by
            rw [hboxpeel]
      _ = (((A.card : ℝ) ^ 2)⁻¹) ^ k * ∑ t : Fin k → ↥A × ↥A, Z t := hnorm
  have hsumZ : δ * (A.card : ℝ) ^ (2 * k) ≤ ∑ t : Fin k → ↥A × ↥A, Z t := by
    have h2 : ((A.card : ℝ) ^ 2) ^ k * δ
        ≤ ((A.card : ℝ) ^ 2) ^ k * ((((A.card : ℝ) ^ 2)⁻¹) ^ k *
            ∑ t : Fin k → ↥A × ↥A, Z t) :=
      mul_le_mul_of_nonneg_left hδZ (by positivity)
    have hAB : ((A.card : ℝ) ^ 2) ^ k * (((A.card : ℝ) ^ 2)⁻¹) ^ k = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (by positivity : ((A.card : ℝ) ^ 2) ≠ 0), one_pow]
    have h3 : ((A.card : ℝ) ^ 2) ^ k * ((((A.card : ℝ) ^ 2)⁻¹) ^ k *
        ∑ t : Fin k → ↥A × ↥A, Z t) = ∑ t : Fin k → ↥A × ↥A, Z t := by
      rw [← mul_assoc, hAB, one_mul]
    have h4 : ((A.card : ℝ) ^ 2) ^ k = (A.card : ℝ) ^ (2 * k) := (pow_mul _ 2 k).symm
    have h6 : ((A.card : ℝ) ^ 2) ^ k * δ ≤ ∑ t : Fin k → ↥A × ↥A, Z t := by
      rw [h3] at h2
      exact h2
    rw [h4, mul_comm] at h6
    exact h6
  have hcardι : Fintype.card (Fin k → ↥A × ↥A) = A.card ^ (2 * k) := by
    have h1 : (A.card * A.card) ^ k = A.card ^ (2 * k) := by
      rw [← pow_two, ← pow_mul]
    calc Fintype.card (Fin k → ↥A × ↥A)
        = (A.card * A.card) ^ k := by
          simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
      _ = A.card ^ (2 * k) := h1
  have hKpos : (0 : ℝ) < 1 + ((k + 2 : ℕ) : ℝ) + |((P.leadingCoeff : ℤ) : ℝ)| := by
    have h1 : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ |((P.leadingCoeff : ℤ) : ℝ)| := abs_nonneg _
    linarith
  have hZleK : ∀ t : Fin k → ↥A × ↥A,
      Z t ≤ 1 + ((k + 2 : ℕ) : ℝ) + |((P.leadingCoeff : ℤ) : ℝ)| := by
    intro t
    have h1 : Z t ≤ 1 := by
      rw [hZ]
      exact boxNormPow_two_iterDelta_le_one hN hNN₀ h0 h1 hb0 hb1 A k (pairVal t)
    have h2 : (1 : ℝ) ≤ 1 + ((k + 2 : ℕ) : ℝ) + |((P.leadingCoeff : ℤ) : ℝ)| := by
      have h3 : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      have h4 : (0 : ℝ) ≤ |((P.leadingCoeff : ℤ) : ℝ)| := abs_nonneg _
      linarith
    linarith
  have hcount : δ / 4 / (1 + ((k + 2 : ℕ) : ℝ) + |((P.leadingCoeff : ℤ) : ℝ)|) *
      (Fintype.card (Fin k → ↥A × ↥A) : ℝ)
      ≤ (((Finset.univ : Finset (Fin k → ↥A × ↥A)).filter (fun t => δ / 4 ≤ Z t)).card : ℝ) := by
    refine card_large_values (ι := Fin k → ↥A × ↥A) (Z := Z) hδ0 hKpos hZnn hZleK ?_
    rw [hcardι, Nat.cast_pow]
    exact hsumZ
  have hk2 : k + 2 - 2 = k := Nat.add_sub_cancel k 2
  set H : Finset (Fin k → ℤ × ℤ) := ((Finset.univ : Finset (Fin k → ↥A × ↥A)).filter
      (fun t => δ / 4 ≤ Z t)).image (fun t : Fin k → ↥A × ↥A => pairVal t) with hHdef
  have hinj : Function.Injective
      (fun t : Fin k → ↥A × ↥A => pairVal t) := by
    intro t₁ t₂ h
    funext i
    have hi : pairVal t₁ i = pairVal t₂ i := congrFun h i
    simp only [pairVal, Prod.mk.injEq] at hi
    exact Prod.ext (Subtype.ext hi.1) (Subtype.ext hi.2)
  have hHcard : H.card = ((Finset.univ : Finset (Fin k → ↥A × ↥A)).filter
      (fun t => δ / 4 ≤ Z t)).card :=
    Finset.card_image_of_injective _ hinj
  refine ⟨H, ?_, ?_, ?_⟩
  · intro sh hsh i
    rw [hHdef] at hsh
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hsh
    rw [← ht]
    exact ⟨(t i).1.2, (t i).2.2⟩
  · rw [hHcard]
    have hc := hcount
    rw [hcardι, Nat.cast_pow] at hc
    exact hc
  · intro sh hsh
    rw [hHdef] at hsh
    obtain ⟨t, htmem, ht⟩ := Finset.mem_image.mp hsh
    have htZ : δ / 4 ≤ boxNormPow 2 (fun _ : Fin 2 => A) S (iterDelta k (pairVal t) F) := by
      have hfilt := (Finset.mem_filter.mp htmem).2
      simpa [hZ] using hfilt
    rw [← ht]
    exact htZ


end

end Work.Peluse.Ulower
