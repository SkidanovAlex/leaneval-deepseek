import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilkiesH.Tarski.definable_iff_polynomialSignSet
import Submission.Work.WilkiesH.Omega.omega_poly_le

/-!
# Every semialgebraic set belongs to `Ω`

For a sharply o-minimal structure `S` (BNZ, *Wilkie's conjecture for Pfaffian structures*,
§2.1) and a semialgebraic set `X ⊆ ℝⁿ`, there are format and degree bounds `F`, `D` with
`X ∈ S.Ω F D n`.

The route is Tarski–Seidenberg.  `Work.WilkiesH.Tarski.definable_iff_polynomialSignSet`
turns `IsSemialgebraic X` into `PolynomialSignSet id X`, i.e. `X` is built from the zero
sets `{x | p x = 0}` and the positivity sets `{x | 0 < p x}` of real polynomials by
complementation and finite unions.  Each of these four operations is available in `Ω`:

* zero sets: `SOMin.hyp`, format `n`, degree `p.totalDegree`;
* positivity sets: `{x | 0 < p x} = {x | p x ≤ 0}ᶜ`, and `omega_poly_le` puts the sublevel
  set in `Ω (n+2) (p.totalDegree+2)`, so complementation gives format `n+3`;
* complementation: `SOMin.compl`, one extra format;
* binary union: `SOMin.union`, formats joined by `max`, degrees added.

The induction is over the `PolynomialSignSet` derivation, so no quantifier elimination has
to be re-run here: that is the content of the imported bridge.
-/

set_option autoImplicit false
noncomputable section

namespace Work.WilkiesH.Omega

open WilkiesDesign

/-- Iterated monotonicity of the format index. -/
private theorem omega_mono_F_le {S : WilkiesDesign.SOMin} {F F' D n : ℕ} {X : Set (Fin n → ℝ)}
    (h : X ∈ S.Ω F D n) (hle : F ≤ F') : X ∈ S.Ω F' D n :=
  Nat.le_induction h (fun _ _ ih => S.mono_F ih) F' hle

theorem semialgebraic_mem_Omega (S : WilkiesDesign.SOMin) {n : ℕ} {X : Set (Fin n → ℝ)}
    (hX : WilkiesConjecture.IsSemialgebraic X) : ∃ F D : ℕ, X ∈ S.Ω F D n := by
  have hPSS : Work.WilLibTS.TS.PolynomialSignSet (fun x : Fin n → ℝ => x) X :=
    Work.WilkiesH.Tarski.definable_iff_polynomialSignSet.mp hX
  -- The recursion is stated with the set as an explicit argument so that the induction
  -- hypothesis is a plain `∃ F D` statement (no hypothesis is reverted along with it).
  have key : ∀ Y : Set (Fin n → ℝ),
      Work.WilLibTS.TS.PolynomialSignSet (fun x : Fin n → ℝ => x) Y → ∃ F D, Y ∈ S.Ω F D n := by
    intro Y hY
    induction hY with
    | zero p => exact ⟨n, p.totalDegree, S.hyp n p⟩
    | positive p =>
        -- `0 < p x` is the complement of the sublevel set `p x ≤ 0`
        have h := S.compl (omega_poly_le S n p)
        have hset : {x : Fin n → ℝ | 0 < p.eval x} = {x : Fin n → ℝ | p.eval x ≤ 0}ᶜ := by
          ext x
          simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
        exact ⟨n + 2 + 1, p.totalDegree + 2, by rw [hset]; exact h⟩
    | compl =>
        -- `Aᶜ` for `A ∈ Ω F D n` costs one format
        rename_i A hA ih
        obtain ⟨F, D, h⟩ := ih
        exact ⟨F + 1, D, S.compl h⟩
    | union =>
        -- `A ∪ B` at a common format `max F₁ F₂`, degrees added
        rename_i A B hA hB ihA ihB
        obtain ⟨F₁, D₁, h₁⟩ := ihA
        obtain ⟨F₂, D₂, h₂⟩ := ihB
        refine ⟨max F₁ F₂, D₁ + D₂, ?_⟩
        have h₁' : A ∈ S.Ω (max F₁ F₂) D₁ n := omega_mono_F_le h₁ (le_max_left _ _)
        have h₂' : B ∈ S.Ω (max F₁ F₂) D₂ n := omega_mono_F_le h₂ (le_max_right _ _)
        have hu := S.union (fun i : Fin 2 => ![D₁, D₂] i) (fun i : Fin 2 => ![A, B] i)
          (by intro i; fin_cases i
              · simpa using h₁'
              · simpa using h₂')
        have hun : (⋃ i : Fin 2, ![A, B] i) = A ∪ B := by
          ext x
          simp [Fin.exists_fin_two]
        rw [hun] at hu
        simpa [Fin.sum_univ_two] using hu
  exact key X hPSS

end Work.WilkiesH.Omega
