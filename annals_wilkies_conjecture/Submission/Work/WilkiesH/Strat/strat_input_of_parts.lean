import Mathlib
import Submission.Work.WilkiesH.Strat.Defs
import Submission.Work.WilkiesH.Strat.omega_closure_v2
import Submission.Work.WilkiesH.Mfd.mem_alg_of_isGraphAt
import Submission.Work.WilkiesH.Strat.rft.Assemble
import Submission.Work.WilkiesH.Strat.SI.cellRelFrontierThin
import Submission.Work.WilkiesH.Strat.SI.regularPartCover
import Submission.Work.WilkiesH.Strat.SI.polybook
import Submission.Work.WilkiesH.Strat.stratInput_of_one
import Submission.Work.WilkiesH.Strat.dimLE_iUnion_fin

/-!
# The stratification input, assembled from its parts

This file proves `Work.WilkiesH.StratInput` (BNZ §2.3 in the shape consumed by the counting
induction) from the sharp cell decomposition axiom `S.SharpCD` and the geometric parts proved
separately:

* `Work.WilkiesH.Strat.cellRelFrontierThin`: for a cell `κ` inside a semialgebraic `V` of
  dimension `≤ μ`, the relative frontier `κ ∩ closure (V \ κ)` is covered by an `Ω`-set of
  dimension `≤ μ - 1`;
* `Work.WilkiesH.Strat.regularPartCover`: the complement of the `μ`-regular part of a
  semialgebraic `V` is an `Ω`-set of dimension `≤ μ - 1`, and every point of `V` outside it is
  `IsGraphAt μ V`;
* the closure calculus of `omega_closure_v2` and the elementary bookkeeping of `SI/polybook`.

The assembly is: with `A = X ∩ V` and `Vlow` the thin complement of the regular part of `V`,

`(X ∩ V) \ X.alg ⊆ (X ∩ V ∩ Vlow) ∪ (X ∩ V ∩ closure (V \ X))`,

both pieces are `Ω`-sets of dimension `≤ μ - 1` and are contained in `X`, and the union is thin
by `dimLE_iUnion_fin`.  The pointwise dichotomy is:

* a point `x ∈ X ∩ V` outside `X.alg` which is a limit of points of `V \ X` lies in the second
  piece;
* otherwise `V` is locally contained in `X` at `x`, so if `x` were outside `Vlow` then `V` is a
  `μ`-dimensional graph at `x` (`regularPartCover`) and `x ∈ X.alg`
  (`Work.WilkiesH.Mfd.mem_alg_of_isGraphAt`), a contradiction; so `x ∈ Vlow` and `x` lies in
  the first piece.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilkiesH.Strat

open WilkiesDesign WilkiesConjecture

/-- The relative frontier of `X` in a semialgebraic `V` of dimension `≤ μ` is contained in an
`Ω`-set of dimension `≤ μ - 1`: `rel_frontier_thin_of_crux` applied to the `V`-relative cell
frontier thinness `cellRelFrontierThin`. -/
theorem relFrontier_thin_assembly {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) :
    ∀ F n : ℕ, ∃ (a : ℕ) (pm : MvPolynomial (Fin 2) ℕ),
      ∀ (μ D Dv : ℕ) (X V : Set (Fin n → ℝ)),
        X ∈ S.Ω F D n → V ∈ S.Ω F Dv n → WilkiesConjecture.IsSemialgebraic V →
        WilkiesDesign.DimLE V μ →
        WilkiesDesign.DimLE (X ∩ V ∩ closure (V \ X)) (μ - 1) :=
  rel_frontier_thin_of_crux (S := S) hcd (SI.cellRelFrontierThin (S := S) hcd)

/-- **The stratification input, assembled from the sharp cell decomposition axiom and its two
geometric parts.** -/
theorem strat_input_of_parts {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) :
    Work.WilkiesH.StratInput S := by
  classical
  refine stratInput_of_one (S := S) ?_
  intro F n
  obtain ⟨ar, pmr, hr⟩ := SI.regularPartCover (S := S) hcd F n
  obtain ⟨ac, qc, hcl⟩ := omega_closure_v2 (S := S) hcd (F + 2) n
  obtain ⟨pm, hpm⟩ := SI.Book.exists_pm_dominate_sum_two pmr qc
  refine ⟨max (max (F + 1) ar + 1) (max (F + 1) ac + 1), pm, ?_⟩
  intro μ D Dv X V hX hV hVsem hVdim
  -- the two elementary cases `μ = 0` and `n = 0`
  by_cases hμ0 : μ = 0
  · subst hμ0
    refine ⟨X ∩ V, ?_, Set.inter_subset_left, ?_, ?_⟩
    · have hA : X ∩ V ∈ S.Ω (F + 1) (D + Dv) n := Work.WilG0.Omega_inter2 hX hV
      refine Work.WilG5.mem_mono hA _ _ (by omega) ?_
      have hp := hpm D Dv (n + 1)
      omega
    · exact Work.WilkiesH.dimLE_of_subset hVdim Set.inter_subset_right
    · intro x hx
      exact hx.1
  · by_cases hn0 : n = 0
    · subst hn0
      refine ⟨X ∩ V, ?_, Set.inter_subset_left, ?_, ?_⟩
      · have hA : X ∩ V ∈ S.Ω (F + 1) (D + Dv) 0 := Work.WilG0.Omega_inter2 hX hV
        refine Work.WilG5.mem_mono hA _ _ (by omega) ?_
        have hp := hpm D Dv (0 + 1)
        omega
      · -- `ℝ⁰` admits no `(μ-1+1)`-tuple of coordinates
        intro e
        exact Fin.elim0 (e ⟨0, Nat.succ_pos _⟩)
      · intro x hx
        exact hx.1
    · -- main case
      have hμ : 1 ≤ μ := Nat.pos_of_ne_zero hμ0
      obtain ⟨Vlow, hVlowΩ, _, hVlowdim, hVlowreg⟩ := hr μ Dv V hV hVsem hVdim
      -- `A = X ∩ V`
      have hA : X ∩ V ∈ S.Ω (F + 1) (D + Dv) n := Work.WilG0.Omega_inter2 hX hV
      -- piece 1: the points of `A` in the thin complement of the regular part of `V`
      have hP1 : (X ∩ V) ∩ Vlow ∈ S.Ω (max (F + 1) ar + 1)
          ((D + Dv) + MvPolynomial.eval ![(Dv : ℕ), (n + 1 : ℕ)] pmr) n :=
        Work.WilG0.Omega_inter2
          (Work.WilG5.mem_mono hA (max (F + 1) ar) (D + Dv) (le_max_left _ _) le_rfl)
          (Work.WilG5.mem_mono hVlowΩ (max (F + 1) ar)
            (MvPolynomial.eval ![(Dv : ℕ), (n + 1 : ℕ)] pmr) (le_max_right _ _) le_rfl)
      -- `V \ X` is an `Ω`-set
      have hVcX : V \ X ∈ S.Ω (F + 2) (D + Dv) n := by
        have hcompl : Xᶜ ∈ S.Ω (F + 1) D n := S.compl hX
        have h : V ∩ Xᶜ ∈ S.Ω (F + 2) (Dv + D) n :=
          Work.WilG0.Omega_inter2 (S.mono_F hV) hcompl
        have h' := Work.WilG5.mem_mono h (F + 2) (D + Dv) le_rfl (by omega)
        simpa [Set.sdiff_eq] using h'
      obtain ⟨Ccl, hCclΩ, hCcl⟩ := hcl (D + Dv) (V \ X) hVcX
      have hcl_eq : Ccl = closure (V \ X) := by
        have h1 : Ccl = closureSet (V \ X) := by
          ext x
          exact hCcl x
        rw [h1, SI.Book.closureSet_eq_closure]
      -- piece 2: the points of `A` on the relative frontier of `X` in `V`
      have hP2 : (X ∩ V) ∩ closure (V \ X) ∈ S.Ω (max (F + 1) ac + 1)
          ((D + Dv) + Polynomial.eval (D + Dv) qc) n := by
        rw [← hcl_eq]
        exact Work.WilG0.Omega_inter2
          (Work.WilG5.mem_mono hA (max (F + 1) ac) (D + Dv) (le_max_left _ _) le_rfl)
          (Work.WilG5.mem_mono hCclΩ (max (F + 1) ac) (Polynomial.eval (D + Dv) qc)
            (le_max_right _ _) le_rfl)
      -- thinness of the two pieces
      have hthin1 : WilkiesDesign.DimLE ((X ∩ V) ∩ Vlow) (μ - 1) :=
        Work.WilkiesH.dimLE_of_subset hVlowdim Set.inter_subset_right
      have hthin2 : WilkiesDesign.DimLE ((X ∩ V) ∩ closure (V \ X)) (μ - 1) := by
        obtain ⟨_, _, h'⟩ := relFrontier_thin_assembly (S := S) hcd F n
        exact Work.WilkiesH.dimLE_of_subset (h' μ D Dv X V hX hV hVsem hVdim)
          (fun y hy => ⟨hy.1, hy.2⟩)
      -- a common format for the two pieces
      let aF : ℕ := max (max (F + 1) ar + 1) (max (F + 1) ac + 1)
      have hP1' : (X ∩ V) ∩ Vlow ∈ S.Ω aF
          ((D + Dv) + MvPolynomial.eval ![(Dv : ℕ), (n + 1 : ℕ)] pmr) n :=
        Work.WilG5.mem_mono hP1 aF _ (le_max_left _ _) le_rfl
      have hP2' : (X ∩ V) ∩ closure (V \ X) ∈ S.Ω aF
          ((D + Dv) + Polynomial.eval (D + Dv) qc) n :=
        Work.WilG5.mem_mono hP2 aF _ (le_max_right _ _) le_rfl
      refine ⟨((X ∩ V) ∩ Vlow) ∪ ((X ∩ V) ∩ closure (V \ X)), ?_, ?_, ?_, ?_⟩
      · -- `Ω`-membership
        have hu := Work.WilG0.Omega_union2 hP1' hP2'
        refine Work.WilG5.mem_mono hu aF (MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)] pm)
          le_rfl ?_
        have hmono := SI.Book.mv_nat_eval_mono (b := pmr) (x := ![Dv, n + 1])
          (y := ![D + Dv, n + 1])
          (by intro i; fin_cases i <;> simp [Nat.le_add_left, Nat.le_add_right])
        have hp := hpm D Dv (n + 1)
        omega
      · -- contained in `X`
        intro y hy
        rcases hy with h | h
        · exact h.1.1
        · exact h.1.1
      · -- thinness
        have hF0 : ∀ i : Fin 2, (![(X ∩ V) ∩ Vlow, (X ∩ V) ∩ closure (V \ X)] :
            Fin 2 → Set (Fin n → ℝ)) i ∈ S.Ω aF
              (max ((D + Dv) + MvPolynomial.eval ![(Dv : ℕ), (n + 1 : ℕ)] pmr)
                ((D + Dv) + Polynomial.eval (D + Dv) qc)) n := by
          intro i
          fin_cases i
          · exact Work.WilG5.mem_mono hP1' aF _ le_rfl (le_max_left _ _)
          · exact Work.WilG5.mem_mono hP2' aF _ le_rfl (le_max_right _ _)
        have hdim0 : ∀ i : Fin 2, WilkiesDesign.DimLE
            ((![(X ∩ V) ∩ Vlow, (X ∩ V) ∩ closure (V \ X)] : Fin 2 → Set (Fin n → ℝ)) i)
            (μ - 1) := by
          intro i
          fin_cases i
          · simpa using hthin1
          · simpa using hthin2
        have hu := dimLE_iUnion_fin (S := S) hcd
          (![(X ∩ V) ∩ Vlow, (X ∩ V) ∩ closure (V \ X)] : Fin 2 → Set (Fin n → ℝ))
          hF0 hdim0
        refine Work.WilkiesH.dimLE_of_subset hu ?_
        intro y hy
        rcases hy with h | h
        · exact Set.mem_iUnion.mpr ⟨0, by simpa using h⟩
        · exact Set.mem_iUnion.mpr ⟨1, by simpa using h⟩
      · -- covering
        intro x hx
        obtain ⟨⟨hxX, hxV⟩, hxalg⟩ := hx
        by_cases hclmem : x ∈ closure (V \ X)
        · exact Or.inr ⟨⟨hxX, hxV⟩, hclmem⟩
        · by_cases hlmem : x ∈ Vlow
          · exact Or.inl ⟨⟨hxX, hxV⟩, hlmem⟩
          · exfalso
            -- `V` is locally contained in `X` at `x`
            have hloc : Work.WilkiesH.LocallyIn V X x := by
              rw [Metric.mem_closure_iff] at hclmem
              push Not at hclmem
              obtain ⟨ε, hε, hε'⟩ := hclmem
              refine ⟨ε, hε, fun y hy hyV => ?_⟩
              by_contra hyX
              have hyS : y ∈ V \ X := ⟨hyV, hyX⟩
              have h2 : ε ≤ dist x y := hε' y hyS
              have hdist : dist x y < ε := by
                rw [dist_pi_lt_iff hε]
                intro i
                rw [Real.dist_eq]
                have h1 := (Work.WilkiesH.mem_boxAround.mp hy) i
                rw [abs_sub_comm] at h1
                linarith
              linarith
            exact hxalg (Work.WilkiesH.Mfd.mem_alg_of_isGraphAt hμ hVsem
              (hVlowreg x hxV hlmem) hloc)

end Work.WilkiesH.Strat
