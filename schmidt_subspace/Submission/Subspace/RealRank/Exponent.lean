import Mathlib

/-!
# Combinatorial bookkeeping for the wedge exponents

This file records the combinatorial input of the exponent bookkeeping of the wedge (compound)
box: the cardinality of the "top" index set `{t | k ≤ t.val}` and the double-counting identity

`∑_{|T| = r} ∑_{t ∈ T} f t = C(N-1, r-1) * ∑_t f t`,

which is what makes the `∑_{T} c_T` and the `∑_T log μ_T` terms cancel against the volume
bound `∏ λ_j ≤ |det M| Q^{-∑ c}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Submission.Subspace.RealRank

/-- The "top" index set `{t | k ≤ t.val}`. -/
def tailSet (N k : ℕ) : Finset (Fin N) := Finset.univ.filter (fun t => k ≤ t.val)

lemma tailSet_card {N k : ℕ} (hk : k ≤ N) : (tailSet N k).card = N - k := by
  have h2 : (Finset.univ : Finset (Fin (N - k))).card = N - k := by simp
  rw [← h2]
  refine Finset.card_bij (fun t ht => (⟨t.val - k, by
    have h := ht
    simp only [tailSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
    omega⟩ : Fin (N - k))) ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_univ]
  · intro t1 h1 t2 h2 h
    have := congrArg Fin.val h
    simp only [Fin.val_mk] at this
    have h1' : k ≤ t1.val := by
      simpa only [tailSet, Finset.mem_filter, Finset.mem_univ, true_and] using h1
    have h2' : k ≤ t2.val := by
      simpa only [tailSet, Finset.mem_filter, Finset.mem_univ, true_and] using h2
    exact Fin.ext (by omega)
  · intro j _
    refine ⟨⟨k + j.val, by omega⟩, ?_, ?_⟩
    · simp only [tailSet, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · exact Fin.ext (by simp)

/-- **Double counting over `r`-element subsets.** -/
theorem sum_powersetCard_sum_eq {N r : ℕ} (hr : 1 ≤ r) (f : Fin N → ℝ) :
    (∑ T ∈ Finset.powersetCard r (Finset.univ : Finset (Fin N)), ∑ t ∈ T, f t)
      = (Nat.choose (N - 1) (r - 1) : ℝ) * ∑ t, f t := by
  classical
  have hcard : ∀ t : Fin N,
      ((Finset.powersetCard r (Finset.univ : Finset (Fin N))).filter
        (fun T => t ∈ T)).card = Nat.choose (N - 1) (r - 1) := by
    intro t
    have h1 : (Finset.univ.erase t : Finset (Fin N)).card = N - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ, Fintype.card_fin]
    rw [← h1, ← Finset.card_powersetCard (r - 1) (Finset.univ.erase t)]
    refine Finset.card_bij (fun T _ => T.erase t) ?_ ?_ ?_
    · intro T hT
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_erase] at hx ⊢
        exact ⟨hx.1, hT.1.1 hx.2⟩
      · rw [Finset.card_erase_of_mem hT.2, hT.1.2]
    · intro T1 h1' T2 h2' hEq
      rw [Finset.mem_filter] at h1' h2'
      rw [← Finset.insert_erase h1'.2, ← Finset.insert_erase h2'.2, hEq]
    · intro T' hT'
      rw [Finset.mem_powersetCard] at hT'
      have htT' : t ∉ T' := fun h => (Finset.mem_erase.mp (hT'.1 h)).1 rfl
      refine ⟨insert t T', ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨fun x _ => Finset.mem_univ x, ?_⟩, Finset.mem_insert_self _ _⟩
        rw [Finset.card_insert_of_notMem htT', hT'.2]
        omega
      · exact Finset.erase_insert htT'
  rw [Finset.sum_comm' (s := Finset.powersetCard r (Finset.univ : Finset (Fin N)))
    (t := fun T => T) (t' := Finset.univ)
    (s' := fun t => (Finset.powersetCard r (Finset.univ : Finset (Fin N))).filter
      (fun T => t ∈ T)) (f := fun T t => f t)
    (by intro T t; simp only [Finset.mem_univ, true_and, Finset.mem_filter]; tauto)]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard, Finset.sum_mul]
  rw [Finset.mul_sum]


/-- A noncomputable choice of an `r`-element subset, used to reindex sums over
`Set.powersetCard` as sums over `Finset.powersetCard`. -/
noncomputable def toPCE {N r : ℕ} (h : r ≤ N) (T : Finset (Fin N)) :
    Set.powersetCard (Fin N) r :=
  if hT : T.card = r then ⟨T, hT⟩ else
    Classical.choice (Fintype.card_pos_iff.mp (by
      rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_fin]
      exact Nat.choose_pos h))

lemma toPCE_val {N r : ℕ} (h : r ≤ N) {T : Finset (Fin N)} (hT : T.card = r) :
    (toPCE h T : Finset (Fin N)) = T := by
  rw [toPCE, dif_pos hT]

/-- Reindexing a sum over `Set.powersetCard` as a sum over `Finset.powersetCard`. -/
lemma sum_powersetCard_eq_sum {M : Type*} [AddCommMonoid M] {N r : ℕ} (h : r ≤ N)
    (g : Set.powersetCard (Fin N) r → M) :
    (∑ T : Set.powersetCard (Fin N) r, g T)
      = ∑ T ∈ Finset.powersetCard r (Finset.univ : Finset (Fin N)), g (toPCE h T) := by
  classical
  rw [Finset.sum_subtype (p := fun T : Finset (Fin N) => T.card = r)
    (Finset.powersetCard r (Finset.univ : Finset (Fin N)))
    (fun T => by
      rw [Finset.mem_powersetCard]
      exact ⟨fun hT => hT.2, fun hT => ⟨Finset.subset_univ _, hT⟩⟩)
    (fun T => g (toPCE h T))]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  congr 1
  exact Subtype.ext (toPCE_val h T.2).symm

/-- **The exponent sum of the wedge box is negative.** -/
theorem wedge_exponent_sum_neg {N r k : ℕ} (hrk : r + k = N) (hr : 1 ≤ r)
    (M : Matrix (Fin N) (Fin N) ℝ) (hMdet : 0 < |M.det|)
    (c : Fin N → ℝ) (π : Equiv.Perm (Fin N)) (lam : ℕ → ℝ)
    (hlam0 : ∀ j, j < N → 0 < lam j)
    {Q : ℝ} (hQ : 2 ≤ Q)
    (hprod : ∏ j : Fin N, lam j.val ≤ |M.det| * Q ^ (-(∑ i, c i)))
    {gap ε0 : ℝ} (hgap0 : 0 < gap) (hε0 : 0 < ε0)
    (hgap : gap ≤ Q ^ (-ε0)) (K γ : ℝ) (hK : 0 < K) (hγ : 0 ≤ γ)
    (hbig : (Nat.choose N r : ℝ) * Real.log K +
        (Nat.choose (N - 1) (r - 1) : ℝ) * Real.log |M.det| ≤ ε0 / 4 * Real.log Q)
    (hgamma : (Nat.choose N r : ℝ) * γ ≤ ε0 / 4) :
    ∑ T : Set.powersetCard (Fin N) r,
      ((∑ t ∈ (T : Finset (Fin N)), c (π t)) +
        ((Real.log (K * ∏ t ∈ (T : Finset (Fin N)), lam t.val) +
          (if (T : Finset (Fin N)) = Finset.univ.filter (fun t => k ≤ t.val)
            then Real.log gap else 0)) / Real.log Q + γ))
      ≤ -ε0 / 2 := by
  classical
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hQlog : 0 < Real.log Q := Real.log_pos (by linarith)
  have hrN : r ≤ N := by omega
  have hkN : k ≤ N := by omega
  have hC'0 : (0 : ℝ) ≤ (Nat.choose (N - 1) (r - 1) : ℝ) := by positivity
  set tstar : Set.powersetCard (Fin N) r :=
    ⟨tailSet N k, by simp only [Set.powersetCard.mem_iff]; rw [tailSet_card hkN]; omega⟩ with htstar
  have hiff : ∀ T : Set.powersetCard (Fin N) r,
      ((T : Finset (Fin N)) = Finset.univ.filter (fun t : Fin N => k ≤ t.val)) ↔ T = tstar := by
    intro T
    rw [htstar]
    constructor
    · intro h; exact Subtype.ext h
    · intro h
      subst h
      show (tailSet N k : Finset (Fin N)) = Finset.univ.filter (fun t : Fin N => k ≤ t.val)
      rfl
  -- the `c`-part
  have hXsum : (∑ T : Set.powersetCard (Fin N) r, ∑ t ∈ (T : Finset (Fin N)), c (π t))
      = (Nat.choose (N - 1) (r - 1) : ℝ) * ∑ i, c i := by
    have h1 : (∑ T : Set.powersetCard (Fin N) r, ∑ t ∈ (T : Finset (Fin N)), c (π t))
        = ∑ T ∈ Finset.powersetCard r (Finset.univ : Finset (Fin N)),
            ∑ t ∈ T, c (π t) := by
      rw [sum_powersetCard_eq_sum hrN (fun T => ∑ t ∈ (T : Finset (Fin N)), c (π t))]
      refine Finset.sum_congr rfl fun T hT => ?_
      show (∑ t ∈ ((toPCE hrN T : Set.powersetCard (Fin N) r) : Finset (Fin N)), c (π t))
        = ∑ t ∈ T, c (π t)
      rw [toPCE_val hrN (Finset.mem_powersetCard.mp hT).2]
    rw [h1, sum_powersetCard_sum_eq hr (fun t => c (π t)), Equiv.sum_comp π c]
  -- the `log K + log ∏ λ`-part
  have hYsum : (∑ T : Set.powersetCard (Fin N) r,
        Real.log (K * ∏ t ∈ (T : Finset (Fin N)), lam t.val))
      = (Nat.choose N r : ℝ) * Real.log K +
        (Nat.choose (N - 1) (r - 1) : ℝ) * Real.log (∏ j : Fin N, lam j.val) := by
    have h1 : (∑ T : Set.powersetCard (Fin N) r,
          Real.log (K * ∏ t ∈ (T : Finset (Fin N)), lam t.val))
        = ∑ T ∈ Finset.powersetCard r (Finset.univ : Finset (Fin N)),
            (Real.log K + ∑ t ∈ T, Real.log (lam t.val)) := by
      rw [sum_powersetCard_eq_sum hrN (fun T => Real.log (K * ∏ t ∈ (T : Finset (Fin N)), lam t.val))]
      refine Finset.sum_congr rfl fun T hT => ?_
      show Real.log (K * ∏ t ∈ ((toPCE hrN T : Set.powersetCard (Fin N) r) : Finset (Fin N)),
        lam t.val) = Real.log K + ∑ t ∈ T, Real.log (lam t.val)
      rw [toPCE_val hrN (Finset.mem_powersetCard.mp hT).2,
        Real.log_mul (ne_of_gt hK) (ne_of_gt (Finset.prod_pos (fun t _ => hlam0 t.val t.isLt))),
        Real.log_prod]
      intro t _
      exact ne_of_gt (hlam0 t.val t.isLt)
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      sum_powersetCard_sum_eq hr (fun t => Real.log (lam t.val))]
    congr 1
    rw [Real.log_prod]
    intro j _
    exact ne_of_gt (hlam0 j.val j.isLt)
  -- the `log gap`-part
  have hZsum : (∑ T : Set.powersetCard (Fin N) r,
        (if (T : Finset (Fin N)) = Finset.univ.filter (fun t : Fin N => k ≤ t.val)
          then Real.log gap else 0)) = Real.log gap := by
    have h1 : ∀ T : Set.powersetCard (Fin N) r,
        (if (T : Finset (Fin N)) = Finset.univ.filter (fun t : Fin N => k ≤ t.val)
          then Real.log gap else 0) = (if T = tstar then Real.log gap else 0) := by
      intro T
      exact if_congr (hiff T) rfl rfl
    simp_rw [h1]
    rw [Finset.sum_eq_single tstar]
    · simp
    · intro T _ hT
      simp [hT]
    · intro h
      exact absurd (Finset.mem_univ tstar) h
  -- splitting the sum
  have hsplit : (∑ T : Set.powersetCard (Fin N) r,
        ((∑ t ∈ (T : Finset (Fin N)), c (π t)) +
          ((Real.log (K * ∏ t ∈ (T : Finset (Fin N)), lam t.val) +
            (if (T : Finset (Fin N)) = Finset.univ.filter (fun t : Fin N => k ≤ t.val)
              then Real.log gap else 0)) / Real.log Q + γ)))
      = (∑ T : Set.powersetCard (Fin N) r, ∑ t ∈ (T : Finset (Fin N)), c (π t)) +
        ((∑ T : Set.powersetCard (Fin N) r,
            Real.log (K * ∏ t ∈ (T : Finset (Fin N)), lam t.val)) +
         (∑ T : Set.powersetCard (Fin N) r,
            (if (T : Finset (Fin N)) = Finset.univ.filter (fun t : Fin N => k ≤ t.val)
              then Real.log gap else 0))) / Real.log Q +
        (Fintype.card (Set.powersetCard (Fin N) r) : ℝ) * γ := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_div Finset.univ
        (fun x : Set.powersetCard (Fin N) r =>
          Real.log (K * ∏ t ∈ (x : Finset (Fin N)), lam t.val) +
          (if (x : Finset (Fin N)) = Finset.univ.filter (fun t : Fin N => k ≤ t.val)
            then Real.log gap else 0)) (Real.log Q),
      Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    ring
  have hcardN : (Fintype.card (Set.powersetCard (Fin N) r) : ℝ) = (Nat.choose N r : ℝ) := by
    rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_fin]
  -- the volume and gap bounds
  have hprod_log : Real.log (∏ j : Fin N, lam j.val) ≤
      Real.log |M.det| - (∑ i, c i) * Real.log Q := by
    have h1 : Real.log (∏ j : Fin N, lam j.val) ≤
        Real.log (|M.det| * Q ^ (-(∑ i, c i))) :=
      Real.log_le_log (Finset.prod_pos (fun j _ => hlam0 j.val j.isLt)) hprod
    rw [Real.log_mul (ne_of_gt hMdet) (ne_of_gt (Real.rpow_pos_of_pos hQpos _)),
      Real.log_rpow hQpos] at h1
    linarith
  have hgap_log : Real.log gap ≤ -ε0 * Real.log Q := by
    have h1 : Real.log gap ≤ Real.log (Q ^ (-ε0)) := Real.log_le_log hgap0 hgap
    rwa [Real.log_rpow hQpos] at h1
  have hsingle : (Nat.choose N r : ℝ) * Real.log K +
      (Nat.choose (N - 1) (r - 1) : ℝ) * Real.log |M.det| + Real.log gap
      ≤ ε0 / 4 * Real.log Q - ε0 * Real.log Q := by linarith
  -- the final arithmetic
  rw [hsplit, hXsum, hYsum, hZsum, hcardN]
  have hSP : (∑ i, c i) * Real.log Q + Real.log (∏ j : Fin N, lam j.val) ≤ Real.log |M.det| := by
    linarith [hprod_log]
  have key1 : (Nat.choose (N - 1) (r - 1) : ℝ) * (∑ i, c i) +
        ((Nat.choose N r : ℝ) * Real.log K +
          (Nat.choose (N - 1) (r - 1) : ℝ) * Real.log (∏ j : Fin N, lam j.val) + Real.log gap) /
          Real.log Q
      = (((Nat.choose N r : ℝ) * Real.log K + Real.log gap) +
          (Nat.choose (N - 1) (r - 1) : ℝ) * Real.log |M.det|) / Real.log Q +
        ((Nat.choose (N - 1) (r - 1) : ℝ) *
          ((∑ i, c i) * Real.log Q + Real.log (∏ j : Fin N, lam j.val)) -
          (Nat.choose (N - 1) (r - 1) : ℝ) * Real.log |M.det|) / Real.log Q := by
    field_simp
    ring
  rw [key1]
  have key2 : ((Nat.choose (N - 1) (r - 1) : ℝ) *
        ((∑ i, c i) * Real.log Q + Real.log (∏ j : Fin N, lam j.val)) -
        (Nat.choose (N - 1) (r - 1) : ℝ) * Real.log |M.det|) / Real.log Q ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [mul_le_mul_of_nonneg_left hSP hC'0])
      (le_of_lt hQlog)
  have key3 : (((Nat.choose N r : ℝ) * Real.log K + Real.log gap) +
        (Nat.choose (N - 1) (r - 1) : ℝ) * Real.log |M.det|) / Real.log Q +
        (Nat.choose N r : ℝ) * γ ≤ -ε0 / 2 := by
    have hleft : (((Nat.choose N r : ℝ) * Real.log K + Real.log gap) +
          (Nat.choose (N - 1) (r - 1) : ℝ) * Real.log |M.det|) / Real.log Q +
          (Nat.choose N r : ℝ) * γ
        = (((Nat.choose N r : ℝ) * Real.log K + Real.log gap) +
            (Nat.choose (N - 1) (r - 1) : ℝ) * Real.log |M.det| +
            (Nat.choose N r : ℝ) * γ * Real.log Q) / Real.log Q := by
      field_simp
    rw [hleft, div_le_iff₀ hQlog]
    have hg' := mul_le_mul_of_nonneg_right hgamma (le_of_lt hQlog)
    linarith [hsingle, hg']
  linarith [key2, key3]


end Submission.Subspace.RealRank
