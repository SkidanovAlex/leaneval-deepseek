import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_adjoint_eq_of_indicial

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.Algebra.Polynomial
open Commons.FieldTheory.RatFunc

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- **Indicial exactness, weakened hypotheses.**  Same conclusion as
`ordAtT_adjoint_eq_of_indicial`, but the exactness hypothesis `ordAt α (γ i) = e i` is relaxed to the
lower bound `e i ≤ ordAt α (γ i)` (needed only for the indices `i` with `e i - i ≠ m`), and the
leading-coefficient residual hypothesis `hlam` is required only for the indices with `e i - i = m`.

With `b ≠ 0`, `ord_α b = N` with leading coefficient `r ≠ 0`, `m ≤ e i − i` for all `i`, and the
indicial value `Σ_{i : eᵢ−i=m}(−1)ⁱλᵢ(N+eᵢ)ᵢ ≠ 0`, the expression `Σᵢ(−1)ⁱ Dⁱ(γᵢ b)` has order
*exactly* `N + m`. -/
theorem ordAtT_adjoint_eq_of_indicial_le {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    (α : K) (b : RatFunc K) (hb : b ≠ 0) (N : ℤ) (hN : ordAt α b = N) (r : K)
    (hr : r ≠ 0)
    (hb' : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (b - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
        * linFactor (K := K) α ^ N))
    (γ : Fin 5 → RatFunc K) (e : Fin 5 → ℤ) (lam : Fin 5 → K) (m : ℤ)
    (he : ∀ i : Fin 5, e i - ((i : ℕ) : ℤ) ≠ m →
      ((e i : ℤ) : WithTop ℤ) ≤ ordAtT α (γ i))
    (hm : ∀ i : Fin 5, m ≤ e i - ((i : ℕ) : ℤ))
    (hlam : ∀ i : Fin 5, e i - ((i : ℕ) : ℤ) = m → (((e i + 1 : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (γ i - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam i))
        * linFactor (K := K) α ^ (e i)))
    (hP : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = m),
        (-1 : ℤ) ^ (i : ℕ) • (lam i * ∏ j ∈ Finset.range (i : ℕ), ((N + e i - (j : ℤ) : ℤ) : K))) ≠ 0) :
    ordAtT α (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) •
      ((fun x : RatFunc K => D x)^[i] (γ i * b)))
      = ((N + m : ℤ) : WithTop ℤ) := by
  classical
  have hprod : ∀ i : Fin 5, (∏ j ∈ Finset.range (i : ℕ), ((N + e i - (j : ℤ) : ℤ) : K))
      = ((fallFact (N + e i) ((i : ℕ)) : ℤ) : K) := by
    intro i
    simp only [fallFact, Int.cast_prod]
  have hPne : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = m),
      (-1 : ℤ) ^ (i : ℕ) • (lam i * ((fallFact (N + e i) ((i : ℕ)) : ℤ) : K))) ≠ 0 := by
    simpa only [hprod] using hP
  let FF : Fin 5 → K := fun i => ((fallFact (N + e i) ((i : ℕ)) : ℤ) : K)
  let F : Finset (Fin 5) := Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = m)
  let V : K := ∑ i ∈ F, (-1 : ℤ) ^ (i : ℕ) • (lam i * FF i)
  have hVne : V ≠ 0 := hPne
  let c : Fin 5 → K := fun i => (-1 : ℤ) ^ (i : ℕ) • (lam i * r * FF i)
  let T : Fin 5 → RatFunc K := fun i =>
      (-1 : ℤ) ^ (i : ℕ) • ((fun x : RatFunc K => D x)^[i] (γ i * b))
  let W : RatFunc K := algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (r * V))
      * linFactor (K := K) α ^ (N + m)
  let g : Fin 5 → RatFunc K := fun i => if e i - ((i : ℕ) : ℤ) = m then
      T i - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (c i))
        * linFactor (K := K) α ^ (N + m) else T i
  -- Per-index expansion, needed only for the indices with `e i - i = m`.
  have hExp : ∀ i : Fin 5, e i - ((i : ℕ) : ℤ) = m → ((N + m + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (((fun x : RatFunc K => D x)^[i]) (γ i * b)
        - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam i * r * FF i))
          * linFactor (K := K) α ^ (N + m)) := by
    intro i hcond
    have hf : ordAtT α b = (N : WithTop ℤ) := by rw [ordAtT_def α hb, hN]
    have h := ordAtT_iterate_deriv_mul_leading (D := D) hd (α := α) (γ := γ i) (f := b)
      (e := e i) (N := N) (lam := lam i) (r := r) (hlam i hcond) hf hb' (i : ℕ)
    have heq : N + e i - ((i : ℕ) : ℤ) = N + m := by omega
    rwa [heq] at h
  -- Bound on each `g i`.
  have hgle : ∀ i : Fin 5, ((N + m + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α (g i) := by
    intro i
    by_cases hcond : e i - ((i : ℕ) : ℤ) = m
    · have hexp : ((N + m + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
          (((fun x : RatFunc K => D x)^[i]) (γ i * b)
            - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam i * r * FF i))
              * linFactor (K := K) α ^ (N + m)) := hExp i hcond
      have hgi : g i = (((-1 : ℤ) ^ (i : ℕ) : ℤ) : RatFunc K)
          * ((((fun x : RatFunc K => D x)^[i]) (γ i * b)
            - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam i * r * FF i))
              * linFactor (K := K) α ^ (N + m))) := by
        have hgu : g i = T i - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (c i))
            * linFactor (K := K) α ^ (N + m) := by
          simp only [g]
          exact if_pos hcond
        rw [hgu, show c i = (-1 : ℤ) ^ (i : ℕ) • (lam i * r * FF i) from rfl,
          algebraMap_C_zsmul]
        simp only [T, zsmul_eq_mul]
        ring
      rw [hgi]
      have h0 : (0 : WithTop ℤ) ≤ ordAtT α (((-1 : ℤ) ^ (i : ℕ) : ℤ) : RatFunc K) :=
        zero_le_ordAtT_intCast α _
      refine le_trans (le_of_eq ?_)
        (le_trans (add_le_add h0 hexp) (ordAtT_mul_ge α _ _))
      rw [zero_add]
    · -- Here only the lower bound `e i ≤ ordAt γ i` is available.
      have hexp : ((N + m + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
          (((fun x : RatFunc K => D x)^[i]) (γ i * b)) := by
        have hge := ordAtT_iterate_deriv_mul_ge (D := D) hd α (γ i) b hb (i : ℕ)
        rw [hN] at hge
        have hei : ((e i : ℤ) : WithTop ℤ) ≤ ordAtT α (γ i) := he i hcond
        have hlt : m + 1 ≤ e i - ((i : ℕ) : ℤ) := by
          rcases lt_trichotomy (e i - ((i : ℕ) : ℤ)) m with h | h | h
          · exact absurd (le_antisymm (le_of_lt h) (hm i)) hcond
          · exact absurd h hcond
          · linarith
        have hle1 : ((N + m + 1 : ℤ) : WithTop ℤ)
            ≤ ((e i : ℤ) : WithTop ℤ) + (N : WithTop ℤ)
              - (((i : ℕ) : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
          rw [WithTop.coe_le_coe]
          linarith
        have hle2 : ((e i : ℤ) : WithTop ℤ) + (N : WithTop ℤ)
              - (((i : ℕ) : ℤ) : WithTop ℤ)
            ≤ ordAtT α (γ i) + (N : WithTop ℤ) - (((i : ℕ) : ℤ) : WithTop ℤ) := by
          simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (add_le_add_right (add_le_add_right hei (N : WithTop ℤ))
              (-(((i : ℕ) : ℤ) : WithTop ℤ)))
        exact le_trans (le_trans hle1 hle2) hge
      have h2 : ordAtT α (((fun x : RatFunc K => D x)^[i]) (γ i * b)) ≤ ordAtT α (T i) := by
        have hTi : T i = (((-1 : ℤ) ^ (i : ℕ) : ℤ) : RatFunc K)
            * (((fun x : RatFunc K => D x)^[i]) (γ i * b)) := by
          simp only [T, zsmul_eq_mul]
        rw [hTi]
        exact le_ordAtT_mul_intCast α _ _
      rw [show g i = T i from by
        simp only [g]
        exact if_neg hcond]
      exact le_trans hexp h2
  -- The sum identity.
  have hcV : (∑ i ∈ F, c i) = r * V := by
    show (∑ i ∈ F, (-1 : ℤ) ^ (i : ℕ) • (lam i * r * FF i))
      = r * (∑ i ∈ F, (-1 : ℤ) ^ (i : ℕ) • (lam i * FF i))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [zsmul_eq_mul]
    ring
  have hsum : (∑ i : Fin 5, g i) = (∑ i : Fin 5, T i) - W := by
    have hg' : ∀ i : Fin 5, g i = T i - (if e i - ((i : ℕ) : ℤ) = m then
        algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (c i))
          * linFactor (K := K) α ^ (N + m) else 0) := by
      intro i
      by_cases h : e i - ((i : ℕ) : ℤ) = m <;> simp [g, h]
    rw [Finset.sum_congr rfl (fun i _ => hg' i), Finset.sum_sub_distrib]
    congr 1
    show (∑ i : Fin 5, (if e i - ((i : ℕ) : ℤ) = m then
        algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (c i))
          * linFactor (K := K) α ^ (N + m) else 0)) = W
    show _ = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (r * V))
        * linFactor (K := K) α ^ (N + m)
    rw [← Finset.sum_filter, ← Finset.sum_mul]
    congr 1
    rw [← map_sum (algebraMap (Polynomial K) (RatFunc K)) (fun i => Polynomial.C (c i)) _]
    congr 1
    simp only [Polynomial.C_eq_algebraMap]
    rw [← map_sum (algebraMap K (Polynomial K)) (fun i => c i) _, hcV]
  -- Order of the leading term.
  have hW : ordAtT α W = ((N + m : ℤ) : WithTop ℤ) := by
    show ordAtT α (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (r * V))
        * linFactor (K := K) α ^ (N + m)) = _
    have hC0 : (Polynomial.C (r * V) : Polynomial K) ≠ 0 := by
      rw [Polynomial.C_ne_zero]; exact mul_ne_zero hr hVne
    have hC : algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (r * V)) ≠ 0 :=
      RatFunc.algebraMap_ne_zero hC0
    rw [ordAtT_mul α hC (zpow_ne_zero _ (linFactor_ne_zero α)), ordAtT_algebraMap hC0,
      Polynomial.rootMultiplicity_C, ordAtT_linFactor_zpow]
    simp
  -- Finish.
  have hgl : ((N + m + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α (∑ i : Fin 5, g i) :=
    le_ordAtT_finset_sum (fun i _ => hgle i)
  have hsum' : (∑ i : Fin 5, T i) = W + ∑ i : Fin 5, g i := by
    rw [hsum]; abel
  change ordAtT α (∑ i : Fin 5, T i) = ((N + m : ℤ) : WithTop ℤ)
  rw [hsum']
  exact ordAtT_add_eq_of_le_succ hW hgl

end Commons.FieldTheory.RatFunc
