import Mathlib
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `pdVec_mul_comp_le`: a pointwise Leibniz/Faà di Bruno jet bound for `A · (R ∘ φ)`

The partial-derivative vector `∂^β (A · (R ∘ φ)) (z₀)` of a product with a composition is
controlled, at the single point `z₀`, by the jets of the three factors at `z₀`, `φ z₀`, `φ z₀`
respectively:

`‖∂^β (A · (R ∘ φ)) z₀‖ ≤ C · MA · (1 + MD)^m · MR`

whenever `‖D^i A z₀‖ ≤ MA` (`i ≤ m`), `‖D^i φ z₀‖ ≤ MD^i` (`1 ≤ i ≤ m`) and
`‖D^i R (φ z₀)‖ ≤ MR` (`i ≤ m`), with `C` depending only on `m`.

The proof is the two classical estimates for iterated derivatives, both in Mathlib:

* Leibniz, `norm_iteratedFDeriv_mul_le`:
  `‖D^m (f · g) x‖ ≤ ∑_{i ≤ m} (m.choose i) ‖D^i f x‖ ‖D^{m-i} g x‖`;
* Faà di Bruno, `norm_iteratedFDeriv_comp_le`:
  `‖D^n (g ∘ f) x‖ ≤ n! · C · D^n` from `‖D^i g (f x)‖ ≤ C` and `‖D^i f x‖ ≤ D^i` (`1 ≤ i ≤ n`).

All the combinatorial constants are absorbed into `C`; the geometric factor `D^{m-i}` is turned
into `(1 + D)^m` using `D ≥ 0` (which for `m ≥ 1` is forced by the `i = 1` hypothesis) and
`m - i ≤ m`.

The value of the `m`-th derivative at `z₀` is evaluated on the tuple of standard basis vectors
`(e_{β 0}, …, e_{β (m-1)})`, which has multilinear norm `1`; `pdVec_eq_iteratedFDeriv` identifies
the partial derivative vector with this evaluation.
-/

namespace Work.Diff.STE.B3

theorem pdVec_mul_comp_le {n m : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : (Fin n → ℝ) → ℂ) (φ : (Fin n → ℝ) → (Fin n → ℝ))
      (R : (Fin n → ℝ) → ℂ) (z₀ : Fin n → ℝ) (β : Fin m → Fin n) (MA MD MR : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) A → ContDiff ℝ (⊤ : ℕ∞) φ → ContDiff ℝ (⊤ : ℕ∞) R →
      (∀ i : ℕ, i ≤ m → ‖iteratedFDeriv ℝ i A z₀‖ ≤ MA) →
      (∀ i : ℕ, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i φ z₀‖ ≤ MD ^ i) →
      (∀ i : ℕ, i ≤ m → ‖iteratedFDeriv ℝ i R (φ z₀)‖ ≤ MR) →
      ‖Work.Diff.STE.pdVec m β (fun z => A z * R (φ z)) z₀‖ ≤ C * MA * (1 + MD) ^ m * MR := by
  classical
  refine ⟨∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ((m - i).factorial : ℝ), ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro A φ R z₀ β MA MD MR hA hφ hR hMA hMD hMR
    set Cc : ℝ := ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ((m - i).factorial : ℝ)
      with hCcdef
    -- nonnegativity of the two jet bounds
    have hMA0 : 0 ≤ MA := (norm_nonneg _).trans (hMA 0 (Nat.zero_le m))
    have hMR0 : 0 ≤ MR := (norm_nonneg _).trans (hMR 0 (Nat.zero_le m))
    -- smoothness of the two factors of the product
    have hRφ : ContDiff ℝ (⊤ : ℕ∞) (fun z => R (φ z)) := hR.comp hφ
    have hFsm : ContDiff ℝ (⊤ : ℕ∞) (fun z => A z * R (φ z)) := hA.mul hRφ
    -- evaluating the multilinear map on the standard basis vectors does not increase the norm
    have heval :
        ‖iteratedFDeriv ℝ m (fun z => A z * R (φ z)) z₀ (fun j => Pi.single (β j) 1)‖
          ≤ ‖iteratedFDeriv ℝ m (fun z => A z * R (φ z)) z₀‖ := by
      have h := ContinuousMultilinearMap.le_opNorm
        (iteratedFDeriv ℝ m (fun z => A z * R (φ z)) z₀)
        (fun j : Fin m => (Pi.single (β j) (1 : ℝ) : Fin n → ℝ))
      have hprod : ∏ j : Fin m, ‖(Pi.single (β j) (1 : ℝ) : Fin n → ℝ)‖ = 1 := by
        simp [Pi.norm_single]
      rwa [hprod, mul_one] at h
    -- Leibniz for the product `A · (R ∘ φ)`
    have hmul :
        ‖iteratedFDeriv ℝ m (fun z => A z * R (φ z)) z₀‖
          ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i A z₀‖
              * ‖iteratedFDeriv ℝ (m - i) (fun z => R (φ z)) z₀‖ :=
      norm_iteratedFDeriv_mul_le hA hRφ z₀ (WithTop.coe_le_coe.mpr le_top)
    -- Faà di Bruno for the composition `R ∘ φ`
    have hcomp : ∀ i ≤ m, ‖iteratedFDeriv ℝ i (fun z => R (φ z)) z₀‖
        ≤ (i.factorial : ℝ) * MR * MD ^ i := by
      intro i hi
      have h := norm_iteratedFDeriv_comp_le (n := i) hR hφ
        (WithTop.coe_le_coe.mpr le_top) z₀ (C := MR) (D := MD)
        (fun j hj => hMR j (hj.trans hi)) (fun j hj1 hj2 => hMD j hj1 (hj2.trans hi))
      exact h
    -- the geometric factor: `D^(m-i) ≤ (1 + D)^m`
    have hpow : ∀ i ∈ Finset.range (m + 1), MD ^ (m - i) ≤ (1 + MD) ^ m := by
      intro i hi
      have hi' : i ≤ m := Finset.mem_range_succ_iff.mp hi
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        have hi0 : i = 0 := Nat.le_zero.mp hi'
        subst hi0
        simp
      · have hMD0 : 0 ≤ MD := by
          have h1 : ‖iteratedFDeriv ℝ 1 φ z₀‖ ≤ MD := by
            simpa using hMD 1 le_rfl hmpos
          exact (norm_nonneg _).trans h1
        calc MD ^ (m - i) ≤ (1 + MD) ^ (m - i) := pow_le_pow_left₀ hMD0 (by linarith) _
          _ ≤ (1 + MD) ^ m := pow_le_pow_right₀ (by linarith) (Nat.sub_le m i)
    -- termwise estimate
    have hsum0 :
        ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i A z₀‖
            * ‖iteratedFDeriv ℝ (m - i) (fun z => R (φ z)) z₀‖
          ≤ ∑ i ∈ Finset.range (m + 1),
              (m.choose i : ℝ) * MA * ((m - i).factorial : ℝ) * MR * MD ^ (m - i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ m := Finset.mem_range_succ_iff.mp hi
      have h1 : ‖iteratedFDeriv ℝ i A z₀‖ ≤ MA := hMA i hi'
      have h2 := hcomp (m - i) (Nat.sub_le m i)
      calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i A z₀‖
              * ‖iteratedFDeriv ℝ (m - i) (fun z => R (φ z)) z₀‖
          ≤ (m.choose i : ℝ) * MA * (((m - i).factorial : ℝ) * MR * MD ^ (m - i)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) hMA0)
        _ = (m.choose i : ℝ) * MA * ((m - i).factorial : ℝ) * MR * MD ^ (m - i) := by ring
    -- absorb the powers of `MD` into `(1 + MD)^m`
    have hsum1 :
        ∑ i ∈ Finset.range (m + 1),
            (m.choose i : ℝ) * MA * ((m - i).factorial : ℝ) * MR * MD ^ (m - i)
          ≤ Cc * MA * MR * (1 + MD) ^ m := by
      rw [hCcdef]
      calc ∑ i ∈ Finset.range (m + 1),
              (m.choose i : ℝ) * MA * ((m - i).factorial : ℝ) * MR * MD ^ (m - i)
          ≤ ∑ i ∈ Finset.range (m + 1),
              ((m.choose i : ℝ) * ((m - i).factorial : ℝ)) * (MA * MR * (1 + MD) ^ m) := by
            apply Finset.sum_le_sum
            intro i hi
            have hb : (0 : ℝ) ≤ (m.choose i : ℝ) * ((m - i).factorial : ℝ) :=
              mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
            have hx : (0 : ℝ) ≤ MA * MR := mul_nonneg hMA0 hMR0
            calc (m.choose i : ℝ) * MA * ((m - i).factorial : ℝ) * MR * MD ^ (m - i)
                = ((m.choose i : ℝ) * ((m - i).factorial : ℝ)) * (MA * MR) * MD ^ (m - i) := by
                  ring
              _ ≤ ((m.choose i : ℝ) * ((m - i).factorial : ℝ)) * (MA * MR) * (1 + MD) ^ m :=
                  mul_le_mul_of_nonneg_left (hpow i hi) (mul_nonneg hb hx)
              _ = ((m.choose i : ℝ) * ((m - i).factorial : ℝ))
                    * (MA * MR * (1 + MD) ^ m) := by ring
        _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ((m - i).factorial : ℝ))
              * (MA * MR * (1 + MD) ^ m) := by
            rw [Finset.sum_mul]
        _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ((m - i).factorial : ℝ))
              * MA * MR * (1 + MD) ^ m := by ring
    rw [hCcdef]
    calc ‖Work.Diff.STE.pdVec m β (fun z => A z * R (φ z)) z₀‖
        = ‖iteratedFDeriv ℝ m (fun z => A z * R (φ z)) z₀ (fun j => Pi.single (β j) 1)‖ := by
          rw [Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv m (fun z => A z * R (φ z)) hFsm z₀ β]
      _ ≤ ‖iteratedFDeriv ℝ m (fun z => A z * R (φ z)) z₀‖ := heval
      _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i A z₀‖
              * ‖iteratedFDeriv ℝ (m - i) (fun z => R (φ z)) z₀‖ := hmul
      _ ≤ ∑ i ∈ Finset.range (m + 1),
              (m.choose i : ℝ) * MA * ((m - i).factorial : ℝ) * MR * MD ^ (m - i) := hsum0
      _ ≤ Cc * MA * MR * (1 + MD) ^ m := hsum1
      _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ((m - i).factorial : ℝ))
              * MA * (1 + MD) ^ m * MR := by ring

end Work.Diff.STE.B3
