import Mathlib
import Submission.Work.Diff.Alg.Pinch.Chat_margin
import Submission.Work.Diff.Alg.Pinch.ChatShiftDefs
import Submission.Work.Diff.Alg.Pinch.inPIC2_comp_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The shift of the cone `Dpic p` by `γ₁ • (Ric₀ S ∧ id) + γ₂ • Iso n`

Let `S ∈ Dpic p` (algebraic curvature tensor, `InPIC2 S`, and `Ric S ≥ (p/n) · scal S`), let
`γ₁ ≤ 0`, `γ₂ > 0`, and form `W := S + γ₁ • (Ric₀ S ∧ id) + γ₂ • Iso n`.  This file shows that
`W ∈ Dpic p'` provided the two "room" inequalities `ChSRoom` hold:

* `|γ₁| · C_EF · C_T · σ ≤ γ₂`, and
* `γ₂ (n-1)(1 - p') ≥ |γ₁| (n-2) C_ric σ + σ (p' - p)/n`,

where `σ = scalAlg S` and the constants `C_EF`, `C_T`, `C_ric` bound respectively
`|EF D| ≤ C_EF ‖D‖ EF (Iso n)` (`EF_algCurv_bound`), `‖Ric₀ S ∧ id‖ ≤ C_T scalAlg S`
(`ChatShift.knProd_ric0_norm_bound`) and `|⟨Ric₀ S v, v⟩| ≤ C_ric scalAlg S ‖v‖²`
(`ChatShift.ric0_form_bound`).

This is the algebraic core of the Brendle–Schoen "shift inclusion"
`R + c • Iso n ∈ Ĉ(s) → R + 2c • Iso n ∈ Ĉ(s + ε)`: for algebraic curvature tensors the round
sphere is an interior point of the cone, so a small `Iso n`-perturbation of a tensor with bounded
`scalAlg` can be absorbed, at the price of moving the cone parameter slightly.

**Provenance.**  The statement and proof below are a copy of `Work.Diff.Alg.Pinch.Dpic_shift_core`
from `Submission/Work/Diff/Alg/Pinch/chat_shift_inclusion.lean` (same team, proved in parallel).
The copy is necessary because that module declares `Work.Diff.Alg.Pinch.ell_zero'`, which clashes
with the identically named declaration in `Submission/Work/Diff/Alg/Pinch/Chat_shift_base.lean`, so
no single module may import both; this file is importable together with `Chat_shift_base`, whose
parametrisation of the family `Ĉ(s)` is used by `Chat_shift_inclusion_any`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg Work.Diff.Alg.Pinch

variable {n : ℕ}

namespace ChatAny

/-- **Core step.**  If the two "room" inequalities `ChSRoom` hold, then the perturbation
`S ↦ S + γ₁ • (Ric₀ S ∧ id) + γ₂ • Iso n` stays inside `Dpic P'` whenever `S ∈ Dpic P`.

The two `Iso`-directions are harmless (`InPIC2` and `RicPinch` are closed under adding
nonnegative multiples of `Iso n`), the `Ric₀ ∧ id`-direction is absorbed by the rooms:
`C_EF` bounds the isotropic curvature form of an algebraic tensor by `‖D‖ · EF (Iso n)`,
`C_T` bounds `‖Ric₀ S ∧ id‖` and `C_ric` bounds `|⟨Ric₀ S v, v⟩|`, both by `C · scalAlg S`. -/
theorem dpic_shift_core (n : ℕ) (hn : 2 ≤ n) {C_EF C_T C_ric : ℝ}
    (hC_EF : 0 ≤ C_EF) (hC_T : 0 ≤ C_T) (hC_ric : 0 ≤ C_ric)
    (hEF : ∀ D : Curv4 n, IsAlgCurv D → ∀ x y z w : Fin n → ℝ,
      |Cone.EF D x y z w| ≤ C_EF * ‖D‖ * Cone.EF (Iso n) x y z w)
    (hTb : ∀ S : Curv4 n, IsAlgCurv S → InPIC2 S →
      ‖knProd (ric0 S) (id2 n)‖ ≤ C_T * scalAlg S)
    (hricb : ∀ S : Curv4 n, IsAlgCurv S → InPIC2 S → ∀ v : Fin n → ℝ,
      |∑ i, ∑ j, ric0 S i j * v i * v j| ≤ C_ric * scalAlg S * (∑ i, v i * v i))
    {a a' b b' P P' t σ : ℝ} (hP : P ≤ P') (hP' : P' < 1)
    {S : Curv4 n} (hS : IsAlgCurv S) (hPIC : InPIC2 S) (hRic : RicPinch P S)
    (hσ : scalAlg S = σ)
    (hroom : ChSRoom n C_EF C_T C_ric a a' b b' P P' t σ) :
    S + chSg1 n b b' • knProd (ric0 S) (id2 n) + chSg2 n a a' t σ • Iso n ∈ Dpic (n := n) P' := by
  have hσ0 : 0 ≤ σ := by rw [← hσ]; exact (inPIC2_metric_basic n).2.2 S hPIC
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hTalg : IsAlgCurv (knProd (ric0 S) (id2 n)) :=
    knProd_isAlgCurv (fun i j => ric0_symm hS i j) (fun i j => id2_symm i j)
  have hTbd : ‖knProd (ric0 S) (id2 n)‖ ≤ C_T * σ := by
    rw [← hσ]; exact hTb S hS hPIC
  have hricbd : ∀ v : Fin n → ℝ,
      |∑ i, ∑ j, ric0 S i j * v i * v j| ≤ C_ric * σ * (∑ i, v i * v i) := by
    intro v; rw [← hσ]; exact hricb S hS hPIC v
  refine ⟨?_, ?_, ?_⟩
  · exact isAlgCurv_add (isAlgCurv_add hS (isAlgCurv_smul _ hTalg))
      (isAlgCurv_smul _ (Iso_algCurv n))
  · rw [Cone.inPIC2_iff]
    intro x y z w
    have hIso : 0 ≤ Cone.EF (Iso n) x y z w :=
      (Cone.inPIC2_iff (Iso n)).mp (Cone.inPIC2_iso n) x y z w
    have hSnn : 0 ≤ Cone.EF S x y z w := (Cone.inPIC2_iff S).mp hPIC x y z w
    have hEFT : |Cone.EF (knProd (ric0 S) (id2 n)) x y z w|
        ≤ C_EF * (C_T * σ) * Cone.EF (Iso n) x y z w := by
      refine (hEF _ hTalg x y z w).trans ?_
      have h1 := mul_le_mul_of_nonneg_left hTbd hC_EF
      have h2 := mul_le_mul_of_nonneg_right h1 hIso
      linarith
    have hg : -( |chSg1 n b b'| * (C_EF * (C_T * σ)) * Cone.EF (Iso n) x y z w)
        ≤ chSg1 n b b' * Cone.EF (knProd (ric0 S) (id2 n)) x y z w := by
      have h1 : -( |chSg1 n b b'| * |Cone.EF (knProd (ric0 S) (id2 n)) x y z w|)
          ≤ chSg1 n b b' * Cone.EF (knProd (ric0 S) (id2 n)) x y z w := by
        have h := neg_abs_le (chSg1 n b b' * Cone.EF (knProd (ric0 S) (id2 n)) x y z w)
        rw [abs_mul] at h
        linarith
      have h2 : |chSg1 n b b'| * |Cone.EF (knProd (ric0 S) (id2 n)) x y z w|
          ≤ |chSg1 n b b'| * (C_EF * (C_T * σ) * Cone.EF (Iso n) x y z w) :=
        mul_le_mul_of_nonneg_left hEFT (abs_nonneg _)
      linarith
    have hmul : |chSg1 n b b'| * C_EF * C_T * σ * Cone.EF (Iso n) x y z w
        ≤ chSg2 n a a' t σ * Cone.EF (Iso n) x y z w :=
      mul_le_mul_of_nonneg_right hroom.1 hIso
    have hsplit : Cone.EF (S + chSg1 n b b' • knProd (ric0 S) (id2 n)
        + chSg2 n a a' t σ • Iso n) x y z w
        = Cone.EF S x y z w + chSg1 n b b' * Cone.EF (knProd (ric0 S) (id2 n)) x y z w
          + chSg2 n a a' t σ * Cone.EF (Iso n) x y z w := by
      simp only [Cone.EF_add, Cone.EF_smul]
    rw [hsplit]
    linarith
  · intro v
    set V : ℝ := ∑ i, v i * v i with hVdef
    have hV0 : 0 ≤ V := by
      rw [hVdef]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
    have hric0v : -(C_ric * σ * V) ≤ ∑ i, ∑ j, ric0 S i j * v i * v j := by
      have h := (abs_le.mp (hricbd v)).1
      rw [← hVdef] at h
      linarith
    have hric0v' : |∑ i, ∑ j, ric0 S i j * v i * v j| ≤ C_ric * σ * V := by
      have h := hricbd v
      rwa [← hVdef] at h
    have hricS : (P * σ / (n : ℝ)) * V ≤ ∑ i, ∑ j, ric S i j * v i * v j := by
      have h := hRic v
      rw [hσ] at h
      simpa [hVdef] using h
    have hricPt : ∀ i j : Fin n,
        ric (S + chSg1 n b b' • knProd (ric0 S) (id2 n) + chSg2 n a a' t σ • Iso n) i j
        = ric S i j + chSg1 n b b' * (((n : ℝ) - 2) * ric0 S i j)
          + chSg2 n a a' t σ * (((n : ℝ) - 1) * id2 n i j) := by
      intro i j
      simp only [ric_add, ric_smul, ric_knProd_ric0_id2, ric_iso] <;> ring
    have hsumA : (∑ i, ∑ j, (ric S i j + chSg1 n b b' * (((n : ℝ) - 2) * ric0 S i j)
          + chSg2 n a a' t σ * (((n : ℝ) - 1) * id2 n i j)) * v i * v j)
        = (∑ i, ∑ j, ric S i j * v i * v j)
          + (chSg1 n b b' * ((n : ℝ) - 2)) * (∑ i, ∑ j, ric0 S i j * v i * v j)
          + (chSg2 n a a' t σ * ((n : ℝ) - 1)) * V := by
      have hB : (∑ i, ∑ j, (chSg1 n b b' * (((n : ℝ) - 2) * ric0 S i j)) * v i * v j)
          = (chSg1 n b b' * ((n : ℝ) - 2)) * (∑ i, ∑ j, ric0 S i j * v i * v j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        ring
      have hC : (∑ i, ∑ j, (chSg2 n a a' t σ * (((n : ℝ) - 1) * id2 n i j)) * v i * v j)
          = (chSg2 n a a' t σ * ((n : ℝ) - 1)) * V := by
        have hpt : ∀ i j : Fin n,
            (chSg2 n a a' t σ * (((n : ℝ) - 1) * id2 n i j)) * v i * v j
              = (chSg2 n a a' t σ * ((n : ℝ) - 1)) * (id2 n i j * v i * v j) := by
          intro i j; ring
        rw [hVdef]
        calc (∑ i, ∑ j, (chSg2 n a a' t σ * (((n : ℝ) - 1) * id2 n i j)) * v i * v j)
            = ∑ i, ∑ j, (chSg2 n a a' t σ * ((n : ℝ) - 1)) * (id2 n i j * v i * v j) := by
              apply Finset.sum_congr rfl; intro i _
              apply Finset.sum_congr rfl; intro j _
              rw [hpt i j]
          _ = (chSg2 n a a' t σ * ((n : ℝ) - 1)) * (∑ i, ∑ j, id2 n i j * v i * v j) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro i _
              rw [Finset.mul_sum]
          _ = (chSg2 n a a' t σ * ((n : ℝ) - 1)) * (∑ i, v i * v i) := by
              congr 1
              apply Finset.sum_congr rfl; intro i _
              have h1 : (∑ j, id2 n i j * v i * v j) = v i * (∑ j, id2 n i j * v j) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl; intro j _; ring
              rw [h1, ellinv_sum_id2_mul]
      have hsplit : (∑ i, ∑ j, (ric S i j + chSg1 n b b' * (((n : ℝ) - 2) * ric0 S i j)
            + chSg2 n a a' t σ * (((n : ℝ) - 1) * id2 n i j)) * v i * v j)
          = (∑ i, ∑ j, ric S i j * v i * v j)
            + (∑ i, ∑ j, (chSg1 n b b' * (((n : ℝ) - 2) * ric0 S i j)) * v i * v j)
            + (∑ i, ∑ j, (chSg2 n a a' t σ * (((n : ℝ) - 1) * id2 n i j)) * v i * v j) := by
        simp only [add_mul, Finset.sum_add_distrib]
      rw [hsplit, hB, hC]
    have hsum : (∑ i, ∑ j,
          ric (S + chSg1 n b b' • knProd (ric0 S) (id2 n) + chSg2 n a a' t σ • Iso n) i j
            * v i * v j)
        = (∑ i, ∑ j, ric S i j * v i * v j)
          + (chSg1 n b b' * ((n : ℝ) - 2)) * (∑ i, ∑ j, ric0 S i j * v i * v j)
          + (chSg2 n a a' t σ * ((n : ℝ) - 1)) * V := by
      rw [show (∑ i, ∑ j,
            ric (S + chSg1 n b b' • knProd (ric0 S) (id2 n) + chSg2 n a a' t σ • Iso n) i j
              * v i * v j)
          = ∑ i, ∑ j, (ric S i j + chSg1 n b b' * (((n : ℝ) - 2) * ric0 S i j)
              + chSg2 n a a' t σ * (((n : ℝ) - 1) * id2 n i j)) * v i * v j from by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [hricPt i j]]
      exact hsumA
    have hscal' : scalAlg (S + chSg1 n b b' • knProd (ric0 S) (id2 n)
          + chSg2 n a a' t σ • Iso n)
        = σ + chSg2 n a a' t σ * ((n : ℝ) * ((n : ℝ) - 1)) := by
      rw [scalAlg_add, scalAlg_add, scalAlg_smul, scalAlg_smul, scalAlg_knProd_ric0, hσ, scalAlg_iso]
      ring
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hroom' : (chSg2 n a a' t σ * ((n : ℝ) - 1)) * V - (P' * chSg2 n a a' t σ * ((n : ℝ) - 1)) * V
        ≥ (|chSg1 n b b'| * ((n : ℝ) - 2) * C_ric * σ) * V + (σ * (P' - P) / (n : ℝ)) * V := by
      have h := mul_le_mul_of_nonneg_right hroom.2 hV0
      have he : (chSg2 n a a' t σ * ((n : ℝ) - 1) * (1 - P')) * V
          = (chSg2 n a a' t σ * ((n : ℝ) - 1)) * V
            - (P' * chSg2 n a a' t σ * ((n : ℝ) - 1)) * V := by ring
      have he2 : (|chSg1 n b b'| * ((n : ℝ) - 2) * C_ric * σ + σ * (P' - P) / (n : ℝ)) * V
          = (|chSg1 n b b'| * ((n : ℝ) - 2) * C_ric * σ) * V
            + (σ * (P' - P) / (n : ℝ)) * V := by
        rw [add_mul, mul_div_assoc]
      rw [he, he2] at h
      linarith
    have hγ₁'' : (chSg1 n b b' * ((n : ℝ) - 2)) * (∑ i, ∑ j, ric0 S i j * v i * v j)
        ≥ -((|chSg1 n b b'| * ((n : ℝ) - 2) * C_ric * σ) * V) := by
      have h1 : -( |chSg1 n b b' * ((n : ℝ) - 2)| * |∑ i, ∑ j, ric0 S i j * v i * v j|)
          ≤ (chSg1 n b b' * ((n : ℝ) - 2)) * (∑ i, ∑ j, ric0 S i j * v i * v j) := by
        have h := neg_abs_le ((chSg1 n b b' * ((n : ℝ) - 2))
          * (∑ i, ∑ j, ric0 S i j * v i * v j))
        rw [abs_mul] at h
        linarith
      have hc1n : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
      have h2 : |chSg1 n b b' * ((n : ℝ) - 2)| * |∑ i, ∑ j, ric0 S i j * v i * v j|
          ≤ |chSg1 n b b'| * ((n : ℝ) - 2) * (C_ric * σ * V) := by
        have h3 : |chSg1 n b b' * ((n : ℝ) - 2)| = |chSg1 n b b'| * ((n : ℝ) - 2) := by
          rw [abs_mul, abs_of_nonneg hc1n]
        rw [h3]
        exact mul_le_mul_of_nonneg_left hric0v' (by positivity)
      linarith
    have hA : (P' * (σ + chSg2 n a a' t σ * ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ)) * V
        = (P * σ / (n : ℝ)) * V + (σ * (P' - P) / (n : ℝ)) * V
          + (P' * chSg2 n a a' t σ * ((n : ℝ) - 1)) * V := by
      have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
      field_simp
      ring
    rw [hscal', hsum, hA]
    linarith [hricS, hγ₁'', hroom']

end ChatAny

end Work.Diff.Alg.Pinch
