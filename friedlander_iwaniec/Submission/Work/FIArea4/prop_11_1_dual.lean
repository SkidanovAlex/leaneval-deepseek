/-
# The duality principle for the Jacobi-twisted variance (FI §11)

The variance `V(D) = ‖M α‖²` and its dual form `W(D) = ‖M * γ‖²` (see
`Submission/Work/FIArea4/prop_11_1_defs.lean`) satisfy the duality principle familiar from the
theory of the large sieve: a bound `W(D) ≤ K ‖γ‖²` for *all* dual vectors `γ` implies the bound
`V(D) ≤ K ‖α‖²` for all `α`.

Writing `u_{d,a} = Σ_{r,s} α_{rs} M((d,a),(r,s))` for the class sums, the proof is

`Σ |u|² = |Σ_{r,s} α_{rs} · (Σ_{d,a} conj(u_{d,a}) M((d,a),(r,s)))| ≤ ‖α‖ · ‖M conj(u)‖`
`        ≤ ‖α‖ √(K Σ|u|²)`.
-/
import Mathlib
import Submission.Work.FIArea4.prop_11_1_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary Cauchy–Schwarz for complex sums -/

/-- Cauchy–Schwarz for finite complex sums. -/
lemma norm_sum_mul_le {ι : Type*} (s : Finset ι) (x y : ι → ℂ) :
    ‖∑ i ∈ s, x i * y i‖ ≤
      Real.sqrt (∑ i ∈ s, Complex.normSq (x i)) * Real.sqrt (∑ i ∈ s, Complex.normSq (y i)) := by
  have h1 : ‖∑ i ∈ s, x i * y i‖ ≤ ∑ i ∈ s, ‖x i‖ * ‖y i‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i _ => ?_))
    rw [norm_mul]
  have h2 : ∑ i ∈ s, ‖x i‖ * ‖y i‖ ≤
      Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt s (fun i => ‖x i‖) (fun i => ‖y i‖)
  have e1 : (∑ i ∈ s, Complex.normSq (x i)) = ∑ i ∈ s, ‖x i‖ ^ 2 :=
    Finset.sum_congr rfl (fun i _ => Complex.normSq_eq_norm_sq (x i))
  have e2 : (∑ i ∈ s, Complex.normSq (y i)) = ∑ i ∈ s, ‖y i‖ ^ 2 :=
    Finset.sum_congr rfl (fun i _ => Complex.normSq_eq_norm_sq (y i))
  calc ‖∑ i ∈ s, x i * y i‖ ≤ ∑ i ∈ s, ‖x i‖ * ‖y i‖ := h1
    _ ≤ Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2) := h2
    _ = Real.sqrt (∑ i ∈ s, Complex.normSq (x i))
        * Real.sqrt (∑ i ∈ s, Complex.normSq (y i)) := by rw [e1, e2]

/-- The norm of a nonnegative real, viewed as a complex number. -/
lemma norm_ofReal_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖((r : ℝ) : ℂ)‖ = r := by
  have h1 : Complex.normSq ((r : ℝ) : ℂ) = r ^ 2 := by
    rw [Complex.normSq_ofReal]; ring
  have h2 : Real.sqrt (Complex.normSq ((r : ℝ) : ℂ)) = ‖((r : ℝ) : ℂ)‖ := by
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [h1, Real.sqrt_sq_eq_abs, abs_of_nonneg h] at h2
  exact h2.symm

/-- `C ≤ √A √(K C)` with `A, K, C ≥ 0` implies `C ≤ K A`. -/
lemma le_of_le_sqrt_mul_sqrt {C A K : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (h : C ≤ Real.sqrt A * Real.sqrt (K * C)) : C ≤ K * A := by
  have hKC : 0 ≤ K * C := mul_nonneg hK hC
  have hKA : 0 ≤ K * A := mul_nonneg hK hA
  have h2 : C ≤ Real.sqrt (K * A) * Real.sqrt C := by
    calc C ≤ Real.sqrt A * Real.sqrt (K * C) := h
      _ = Real.sqrt (A * (K * C)) := (Real.sqrt_mul hA (K * C)).symm
      _ = Real.sqrt (K * A * C) := by congr 1; ring
      _ = Real.sqrt (K * A) * Real.sqrt C := Real.sqrt_mul hKA C
  rcases eq_or_lt_of_le hC with h0 | hpos
  · rw [← h0]; exact hKA
  · have h4 : (Real.sqrt C) ^ 2 ≤ Real.sqrt (K * A) * Real.sqrt C := by
      rw [Real.sq_sqrt hC]; exact h2
    have hs : Real.sqrt C ≤ Real.sqrt (K * A) :=
      le_of_mul_le_mul_right (by simpa [sq] using h4) (Real.sqrt_pos.mpr hpos)
    calc C = (Real.sqrt C) ^ 2 := (Real.sq_sqrt hC).symm
      _ ≤ (Real.sqrt (K * A)) ^ 2 := by
          have h5 := mul_le_mul hs hs (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          simpa [sq] using h5
      _ = K * A := Real.sq_sqrt hKA

/-! ## The variance as a matrix product -/

/-- `Work.FIPlan.Evar` is the squared norm of the class sums, i.e. of the rows of `Mentry`. -/
lemma Evar_eq (R S d : ℕ) (α : ℕ → ℕ → ℂ) :
    Work.FIPlan.Evar R S d α
      = ∑ a ∈ Finset.range d, Complex.normSq (∑ r ∈ Finset.Icc 1 (2 * R),
          ∑ s ∈ Finset.Icc 1 (2 * S), α r s * Mentry d a r s) := by
  unfold Work.FIPlan.Evar
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases hc : Nat.Coprime r d
  · rw [if_pos hc]
    have hstep : ∀ s : ℕ, α r s * Mentry d a r s
        = (if ((s : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) * ((a : ℕ) : ZMod d)
            then α r s * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ) else 0) := by
      intro s
      by_cases hcond : ((s : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) * ((a : ℕ) : ZMod d)
      · unfold Mentry
        rw [if_pos ⟨hc, hcond⟩, if_pos hcond]
      · unfold Mentry
        rw [if_neg (fun h => hcond h.2), if_neg hcond, mul_zero]
    rw [Finset.sum_congr rfl (fun s _ => hstep s)]
    exact Finset.sum_filter _ _
  · rw [if_neg hc]
    refine (Finset.sum_eq_zero (fun s _ => ?_)).symm
    unfold Mentry
    rw [if_neg (fun h => hc h.1), mul_zero]

lemma Vmat_eq_Vvar (R S D : ℕ) (α : ℕ → ℕ → ℂ) :
    Vmat R S D α = Work.FIPlan.Vvar R S D α := by
  unfold Vmat Work.FIPlan.Vvar
  refine Finset.sum_congr rfl (fun d _ => ?_)
  exact (Evar_eq R S d α).symm

/-- The double sum over the box as a sum over the product set. -/
lemma sum_box_eq (R S : ℕ) {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M) :
    (∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S), f r s)
      = ∑ p ∈ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S), f p.1 p.2 := by
  rw [Finset.sum_product]

/-! ## The duality principle -/

/-- **Duality principle.**  If the dual form `W(D)` is bounded by `K ‖γ‖²` for every `γ`, then the
variance `V(D)` is bounded by `K ‖α‖²` for every `α`. -/
theorem duality_principle (R S D : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hW : ∀ γ : ℕ → ℕ → ℂ, Wform R S D γ ≤ K * (∑ d ∈ Finset.Ioc D (2 * D),
        ∑ a ∈ Finset.range d, Complex.normSq (γ a d)))
    (α : ℕ → ℕ → ℂ) :
    Vmat R S D α ≤ K * (∑ r ∈ Finset.Icc 1 (2 * R),
      ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s)) := by
  classical
  set Bs : Finset (ℕ × ℕ) := Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S) with hBs
  set u : ℕ → ℕ → ℂ := fun a d => ∑ p ∈ Bs, α p.1 p.2 * Mentry d a p.1 p.2 with hu
  have hu_apply : ∀ a d : ℕ, u a d = ∑ p ∈ Bs, α p.1 p.2 * Mentry d a p.1 p.2 :=
    fun a d => rfl
  set Y : ℕ × ℕ → ℂ := fun p => ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
      (starRingEnd ℂ) (u a d) * Mentry d a p.1 p.2 with hY
  set A : ℝ := ∑ p ∈ Bs, Complex.normSq (α p.1 p.2) with hA
  have hAeq : A = ∑ r ∈ Finset.Icc 1 (2 * R),
      ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s) := by
    rw [hA, hBs, sum_box_eq (M := ℝ)]
  have hAnn : 0 ≤ A := by
    rw [hA]; exact Finset.sum_nonneg (fun p _ => Complex.normSq_nonneg _)
  set C : ℝ := ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
      Complex.normSq (u a d) with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    exact Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _))
  have hV : Vmat R S D α = C := by
    rw [hC, Vmat]
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun a _ => ?_))
    congr 1
    show (∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
        α r s * Mentry d a r s) = ∑ p ∈ Bs, α p.1 p.2 * Mentry d a p.1 p.2
    rw [hBs]
    exact sum_box_eq (M := ℂ) R S (fun r s => α r s * Mentry d a r s)
  -- the swap of the sums
  have hinner : ∀ d : ℕ, (∑ a ∈ Finset.range d, u a d * (starRingEnd ℂ) (u a d))
      = (∑ p ∈ Bs, ∑ a ∈ Finset.range d,
          α p.1 p.2 * Mentry d a p.1 p.2 * (starRingEnd ℂ) (u a d)) := by
    intro d
    have h1 : ∀ a : ℕ, u a d * (starRingEnd ℂ) (u a d)
        = (∑ p ∈ Bs, α p.1 p.2 * Mentry d a p.1 p.2) * (starRingEnd ℂ) (u a d) := by
      intro a; rw [hu_apply a d]
    rw [Finset.sum_congr rfl (fun a _ => h1 a)]
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  have hswap : (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
        u a d * (starRingEnd ℂ) (u a d)) = ∑ p ∈ Bs, α p.1 p.2 * Y p := by
    rw [Finset.sum_congr rfl (fun d _ => hinner d)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hY]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  have hsum_real : (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
      u a d * (starRingEnd ℂ) (u a d)) = ((C : ℝ) : ℂ) := by
    rw [hC]
    push_cast
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun a _ => ?_))
    exact Complex.mul_conj (u a d)
  have key : C = ‖∑ p ∈ Bs, α p.1 p.2 * Y p‖ := by
    calc C = ‖((C : ℝ) : ℂ)‖ := (norm_ofReal_of_nonneg hCnn).symm
      _ = ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
            u a d * (starRingEnd ℂ) (u a d)‖ := by rw [hsum_real]
      _ = ‖∑ p ∈ Bs, α p.1 p.2 * Y p‖ := by rw [hswap]
  have hCS : C ≤ Real.sqrt A * Real.sqrt (∑ p ∈ Bs, Complex.normSq (Y p)) := by
    rw [key, hA]
    exact norm_sum_mul_le Bs (fun p => α p.1 p.2) Y
  have hWbound : (∑ p ∈ Bs, Complex.normSq (Y p)) ≤ K * C := by
    have h1 : (∑ p ∈ Bs, Complex.normSq (Y p))
        = Wform R S D (fun a d => (starRingEnd ℂ) (u a d)) := by
      rw [hY, Wform, hBs]
      exact (sum_box_eq (M := ℝ) R S (fun r s => Complex.normSq (∑ d ∈ Finset.Ioc D (2 * D),
        ∑ a ∈ Finset.range d, (starRingEnd ℂ) (u a d) * Mentry d a r s))).symm
    rw [h1]
    refine le_trans (hW (fun a d => (starRingEnd ℂ) (u a d))) ?_
    refine mul_le_mul_of_nonneg_left ?_ hK
    rw [hC]
    exact Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun a _ =>
      le_of_eq (by rw [Complex.normSq_conj])))
  calc Vmat R S D α = C := hV
    _ ≤ K * A := le_of_le_sqrt_mul_sqrt hCnn hAnn hK
        (le_trans hCS (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hWbound)
          (Real.sqrt_nonneg A)))
    _ = K * (∑ r ∈ Finset.Icc 1 (2 * R),
        ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s)) := by rw [hAeq]


/-- **Duality principle, general column set.**  For an arbitrary set `Bs` of pairs (rows `(r,s)`)
the adjoint form `W` of the variance matrix, a bound `W ≤ K‖γ‖²` for every `γ` implies
`‖M α‖² ≤ K ‖α‖²`, where both sums run over the same column set `Bs`. -/
theorem duality_principle_gen (Bs : Finset (ℕ × ℕ)) (D : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hW : ∀ γ : ℕ → ℕ → ℂ, (∑ p ∈ Bs, Complex.normSq (∑ d ∈ Finset.Ioc D (2 * D),
        ∑ a ∈ Finset.range d, γ a d * Mentry d a p.1 p.2))
        ≤ K * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)))
    (α : ℕ → ℕ → ℂ) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
        Complex.normSq (∑ p ∈ Bs, α p.1 p.2 * Mentry d a p.1 p.2))
      ≤ K * (∑ p ∈ Bs, Complex.normSq (α p.1 p.2)) := by
  classical
  set u : ℕ → ℕ → ℂ := fun a d => ∑ p ∈ Bs, α p.1 p.2 * Mentry d a p.1 p.2 with hu
  have hu_apply : ∀ a d : ℕ, u a d = ∑ p ∈ Bs, α p.1 p.2 * Mentry d a p.1 p.2 :=
    fun a d => rfl
  set Y : ℕ × ℕ → ℂ := fun p => ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
      (starRingEnd ℂ) (u a d) * Mentry d a p.1 p.2 with hY
  set C : ℝ := ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
      Complex.normSq (u a d) with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    exact Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _))
  have hAnn : 0 ≤ ∑ p ∈ Bs, Complex.normSq (α p.1 p.2) :=
    Finset.sum_nonneg (fun p _ => Complex.normSq_nonneg _)
  have hinner : ∀ d : ℕ, (∑ a ∈ Finset.range d, u a d * (starRingEnd ℂ) (u a d))
      = (∑ p ∈ Bs, ∑ a ∈ Finset.range d,
          α p.1 p.2 * Mentry d a p.1 p.2 * (starRingEnd ℂ) (u a d)) := by
    intro d
    have h1 : ∀ a : ℕ, u a d * (starRingEnd ℂ) (u a d)
        = (∑ p ∈ Bs, α p.1 p.2 * Mentry d a p.1 p.2) * (starRingEnd ℂ) (u a d) := by
      intro a; rw [hu_apply a d]
    rw [Finset.sum_congr rfl (fun a _ => h1 a)]
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  have hswap : (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
        u a d * (starRingEnd ℂ) (u a d)) = ∑ p ∈ Bs, α p.1 p.2 * Y p := by
    rw [Finset.sum_congr rfl (fun d _ => hinner d)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hY]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  have hsum_real : (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
      u a d * (starRingEnd ℂ) (u a d)) = ((C : ℝ) : ℂ) := by
    rw [hC]
    push_cast
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun a _ => ?_))
    exact Complex.mul_conj (u a d)
  have key : C = ‖∑ p ∈ Bs, α p.1 p.2 * Y p‖ := by
    calc C = ‖((C : ℝ) : ℂ)‖ := (norm_ofReal_of_nonneg hCnn).symm
      _ = ‖∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
            u a d * (starRingEnd ℂ) (u a d)‖ := by rw [hsum_real]
      _ = ‖∑ p ∈ Bs, α p.1 p.2 * Y p‖ := by rw [hswap]
  have hCS : C ≤ Real.sqrt (∑ p ∈ Bs, Complex.normSq (α p.1 p.2))
      * Real.sqrt (∑ p ∈ Bs, Complex.normSq (Y p)) := by
    rw [key]
    exact norm_sum_mul_le Bs (fun p => α p.1 p.2) Y
  have hWbound : (∑ p ∈ Bs, Complex.normSq (Y p)) ≤ K * C := by
    rw [hY]
    refine le_trans (hW (fun a d => (starRingEnd ℂ) (u a d))) ?_
    refine mul_le_mul_of_nonneg_left ?_ hK
    rw [hC]
    exact Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun a _ =>
      le_of_eq (by rw [Complex.normSq_conj])))
  calc (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
        Complex.normSq (∑ p ∈ Bs, α p.1 p.2 * Mentry d a p.1 p.2))
      = C := by rw [hC]
    _ ≤ K * (∑ p ∈ Bs, Complex.normSq (α p.1 p.2)) :=
        le_of_le_sqrt_mul_sqrt hCnn hAnn hK
          (le_trans hCS (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hWbound)
            (Real.sqrt_nonneg _)))

end

end Work.FIArea4
