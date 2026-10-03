import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.prop_11_1_defs
import Submission.Work.FIArea4.prop_11_1_dual
import Submission.Work.FIArea4.prop_11_1_W_dyad
import Submission.Work.FIArea4.prop_11_1_reduce
import Submission.Work.FIArea4.jacobi_congruence_count
import Submission.Work.FIArea4.Evar_le_trivial

namespace Work.FIArea4

open scoped BigOperators

/-- The dyadic-box version of Friedlander–Iwaniec's Proposition 11.1 (11.14), obtained from the
dual bound `Work.FIArea4.prop_11_1_W_dyad` by the duality principle
(`Work.FIArea4.duality_principle_gen`). -/
theorem Vdyad_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
        (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
        Vdyad D R S α ≤ C * braceV D R S ε *
          (∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
            Complex.normSq (α r s)) := by
  intro ε hε
  obtain ⟨C, hCpos, hC⟩ := prop_11_1_W_dyad ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro D R S α hD hR hS hsupp
  set Bs : Finset (ℕ × ℕ) := Finset.Ioc R (2 * R) ×ˢ Finset.Ioc S (2 * S) with hBs
  have hW : ∀ γ : ℕ → ℕ → ℂ,
      (∑ p ∈ Bs, Complex.normSq (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
        γ a d * Mentry d a p.1 p.2))
      ≤ (C * (braceV D R S ε
            + (D : ℝ) * min (R : ℝ) (S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε)))
        * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
            Complex.normSq (γ a d)) := by
    intro γ
    have h := hC D R S γ hD hR hS
    rw [Wdyad] at h
    rw [sum_prod_eq] at h
    rw [hBs]
    exact h
  have hK : 0 ≤ C * (braceV D R S ε
      + (D : ℝ) * min (R : ℝ) (S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε)) := by
    refine mul_nonneg hCpos.le ?_
    have h1 : 0 ≤ braceV D R S ε := by unfold braceV; positivity
    have h2 : 0 ≤ (D : ℝ) * min (R : ℝ) (S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε) := by positivity
    linarith
  have hV := duality_principle_gen Bs D _ hK hW α
  have hleft : Vdyad D R S α = ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
      Complex.normSq (∑ p ∈ Bs, α p.1 p.2 * Mentry d a p.1 p.2) := by
    rw [Vdyad, hBs]
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun a _ => ?_))
    congr 1
    exact sum_prod_eq _ _ (fun r s => α r s * Mentry d a r s)
  have hright : (∑ p ∈ Bs, Complex.normSq (α p.1 p.2))
      = ∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
          Complex.normSq (α r s) := by
    rw [hBs]
    rw [sum_prod_eq]
    refine Finset.sum_subset ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_Ioc, Finset.mem_Icc] at hp ⊢
      omega
    · intro p hp hpnot
      simp only [Finset.mem_product, Finset.mem_Ioc, Finset.mem_Icc] at hp
      have hzero : α p.1 p.2 = 0 := by
        by_contra hne
        obtain ⟨h1, h2, h3, h4⟩ := hsupp p.1 p.2 hne
        exact hpnot (by
          simp only [Finset.mem_product, Finset.mem_Ioc]
          exact ⟨⟨h1, h2⟩, h3, h4⟩)
      rw [hzero]
      simp
  have hmin : min (R : ℝ) (S : ℝ) ≤ Real.sqrt ((R : ℝ) * (S : ℝ)) := by
    rw [← Nat.cast_min]
    have h1 : ((min R S : ℕ) : ℝ) ^ 2 ≤ (R : ℝ) * (S : ℝ) := by
      have h2 : ((min R S : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast min_le_left R S
      have h3 : ((min R S : ℕ) : ℝ) ≤ (S : ℝ) := by exact_mod_cast min_le_right R S
      have h4 : (0 : ℝ) ≤ ((min R S : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact Real.le_sqrt_of_sq_le h1
  have hstep : (D : ℝ) * min (R : ℝ) (S : ℝ) ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) :=
    mul_le_mul_of_nonneg_left hmin (Nat.cast_nonneg D)
  have hle2 : (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((R : ℝ) * (S : ℝ)) ^ ε)
      ≤ braceV D R S ε := by
    have h1 : (0 : ℝ) ≤ (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε) := by positivity
    have h2 : (0 : ℝ) ≤ (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) * (((R : ℝ) * (S : ℝ)) ^ ε) := by positivity
    have h3 : (0 : ℝ) ≤ (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ) := by positivity
    simp only [braceV]
    rw [add_mul, add_mul]
    linarith
  have hle : (D : ℝ) * min (R : ℝ) (S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε) ≤ braceV D R S ε :=
    le_trans (mul_le_mul_of_nonneg_right hstep (by positivity)) hle2
  have hconst : C * (braceV D R S ε + (D : ℝ) * min (R : ℝ) (S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε))
      ≤ (2 * C) * braceV D R S ε := by
    nlinarith [hCpos]
  calc Vdyad D R S α
      = ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
          Complex.normSq (∑ p ∈ Bs, α p.1 p.2 * Mentry d a p.1 p.2) := hleft
    _ ≤ (C * (braceV D R S ε + (D : ℝ) * min (R : ℝ) (S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε)))
          * (∑ p ∈ Bs, Complex.normSq (α p.1 p.2)) := hV
    _ = (C * (braceV D R S ε + (D : ℝ) * min (R : ℝ) (S : ℝ) * (((R : ℝ) * (S : ℝ)) ^ ε)))
          * (∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
              Complex.normSq (α r s)) := by rw [hright]
    _ ≤ (2 * C) * braceV D R S ε
          * (∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
              Complex.normSq (α r s)) := by
        refine mul_le_mul_of_nonneg_right hconst ?_
        exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ =>
          Complex.normSq_nonneg _))

/-- FI Proposition 11.1, (11.14): for `ε > 0` there is `C` with, for all `D, R, S ≥ 1` and all
`α : ℕ → ℕ → ℂ`,
`V(D) ≤ C·{D^{-1/2}RS + (D√(RS) + R·S^{3/4} + S·R^{3/4})·(RS)^ε}·Σ_{r,s}‖α r s‖²`,
where `V(D) = Work.FIPlan.Vvar R S D α = Σ_{D<d≤2D} Σ_{a mod d} |Σ_{r̄s ≡ a (d)} α r s (r|d')|²`
and `(r|d')` is the Jacobi symbol with `d' = oddPart d`.  The sum over `(r,s)` in `V(D)` runs
over the box `1 ≤ r ≤ 2R`, `1 ≤ s ≤ 2S`; no support hypothesis on `α` is needed (the paper's box
`R < r ≤ 2R`, `S < s ≤ 2S` is a sub-box; the extra dyadic bookkeeping is absorbed by `(RS)^ε`). -/
theorem prop_11_1 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
        Work.FIPlan.Vvar R S D α ≤
          C * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
                + ((D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))
                    + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
                    + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4))
                  * (((R : ℝ) * (S : ℝ)) ^ ε))
            * (∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
                Complex.normSq (α r s)) :=
  prop_11_1_reduce Vdyad_bound

end Work.FIArea4
