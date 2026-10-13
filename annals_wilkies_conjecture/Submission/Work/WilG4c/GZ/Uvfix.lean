/-
  WilG4c / `CritFixOmega` — supporting lemmas.

  Self-contained (proved-from-scratch) pieces used by the proof of `Work.WilkG4c.CritFixOmega`:

  * `finset_inter_mem`    — `Ω`-bookkeeping for a `Finset`-indexed intersection;
  * `eval_X1_add_two_pow` — evaluation of `(X₁+2)^{n+2}` at `![D,k]`;
  * `limcond_fix_mem`     — `Ω`-definability of the per-index limit condition `LimCond`
                            (uniform in the index `i : Σ m : Fin k, Fin (n+1) → Fin (m+2)`);
  * `uvfix_mem`           — `Ω`-definability of the corrected value-free criterion `UVFix`.

  All the `Ω`-inputs used here (`CritFixAux.contSetMem`, `dgSet_mem`, `fibreLimitEqMem_pi`,
  `CritFixAux.card_critIdxFix_le`, `CritFixAux.eval_pair_mono`, `WilG1.Omega.*`) are clean.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4c.CritFixDefs
import Submission.Work.WilG4c.CritMem
import Submission.Work.WilG4c.fibreLimitEqMem_pi
import Submission.Work.WilG4c.CritFixAux.contSetMem
import Submission.Work.WilG4c.CritFixAux.critIdxFixCard
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c.GZ

open WilkiesDesign WilkiesDesign.CG

/-- `Ω`-bookkeeping for a `Finset`-indexed intersection at a common format `a` and a common
degree `MvPolynomial.eval ![D,k] b`: the intersection lies in `S.Ω (a+1) (card * b)`. -/
theorem finset_inter_mem {S : WilkiesDesign.SOMin} {n : ℕ} {a : ℕ}
    {b : MvPolynomial (Fin 2) ℕ} {D k : ℕ} {ι : Type*}
    (s : Finset ι) (A : ι → Set (Fin n → ℝ))
    (hA : ∀ i ∈ s, A i ∈ S.Ω a (MvPolynomial.eval ![D, k] b) n) :
    (⋂ i ∈ s, A i) ∈ S.Ω (a + 1)
      (MvPolynomial.eval ![D, k] (MvPolynomial.C s.card * b)) n := by
  have hA' : ∀ j : Fin s.card, (fun j => A ((Finset.equivFin s).symm j).1) j ∈
      S.Ω a ((Work.WilG1.psubst b k).eval D) n := by
    intro j
    rw [Work.WilG1.eval_psubst]
    exact hA _ ((Finset.equivFin s).symm j).2
  have h := Work.WilG1.Omega.inter_mem (S := S)
    (fun j : Fin s.card => A ((Finset.equivFin s).symm j).1) hA'
  have hset : (⋂ j : Fin s.card, A ((Finset.equivFin s).symm j).1) = ⋂ i ∈ s, A i := by
    ext x
    simp only [Set.mem_iInter]
    constructor
    · intro hh i hi
      have := hh ((Finset.equivFin s) ⟨i, hi⟩)
      simpa using this
    · intro hh j
      exact hh _ ((Finset.equivFin s).symm j).2
  rw [hset] at h
  refine Work.WilG1.Omega.mono h le_rfl (le_of_eq ?_)
  rw [Polynomial.eval_mul, Work.WilG1.eval_psubst, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  simp

/-- The evaluation of `(X₁ + 2)^{n+2}` at `![D,k]` is `(k+2)^{n+2}`. -/
theorem eval_X1_add_two_pow (n D k : ℕ) :
    MvPolynomial.eval ![D, k]
        ((MvPolynomial.X (1 : Fin 2) + MvPolynomial.C 2) ^ (n + 2))
      = (k + 2) ^ (n + 2) := by
  simp [MvPolynomial.eval_pow, MvPolynomial.eval_add, MvPolynomial.eval_X,
    Matrix.cons_val_one]

/-- **Uniform `Ω`-definability of the per-index limit condition `LimCond`.**  The format and the
two-variable degree polynomial are independent of the index `i` and of `k`. -/
theorem limcond_fix_mem (S : WilkiesDesign.SOMin) (hder : WilkiesDesign.SOMin.SharpDeriv S)
    (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D k : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
      (i : Σ m : Fin k, Fin (n + 1) → Fin (m.val + 2)),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.LimCond p n f (i.1.val + 1) (fun j => (i.2 j).val) ∈
        S.Ω a (MvPolynomial.eval ![D, k] b) (p + (n + 1)) := by
  obtain ⟨aD, bD, hD⟩ := Work.WilkG4c.dgSet_mem S hder p n F0
  obtain ⟨aL, bL, hL⟩ := Work.WilG4c.fibreLimitEqMem_pi (S := S) (p := p) (n := n)
  refine ⟨aD + aL + 1, bL.eval₂ MvPolynomial.C bD, ?_⟩
  intro D k f i hf
  set c : Fin (n + 1) → ℕ := fun j => (i.2 j).val with hc
  have hm : i.1.val + 1 ≤ k := by have := i.1.isLt; omega
  have hdg : Work.WilkG4c.dgSet p n f (i.1.val + 1) (Work.WilkG4c.cntWord n (i.1.val + 1) c) ∈
      S.Ω aD (MvPolynomial.eval ![D, i.1.val + 1] bD) (p + (n + 1) + 1) :=
    hD D f hf (i.1.val + 1) (Work.WilkG4c.cntWord n (i.1.val + 1) c)
  have h2 : bL.eval (MvPolynomial.eval ![D, i.1.val + 1] bD) ≤
      bL.eval (MvPolynomial.eval ![D, k] bD) :=
    Work.WilG1.Polynomial.eval_mono (Work.WilkG4c.CritFixAux.eval_pair_mono bD le_rfl hm)
  have hdeg : bL.eval (MvPolynomial.eval ![D, i.1.val + 1] bD) ≤
      MvPolynomial.eval ![D, k] (bL.eval₂ MvPolynomial.C bD) := by
    simpa only [Work.WilkG4c.eval_eval₂] using h2
  have hLimeq := hL (Work.WilkG4c.dgSet p n f (i.1.val + 1)
    (Work.WilkG4c.cntWord n (i.1.val + 1) c)) hdg
  have hmono := Work.WilG1.Omega.mono hLimeq (le_refl (aD + aL)) hdeg
  have hproj := S.proj hmono
  simpa only [Work.WilkG4c.LimCond, Work.WilkG4c.ProjLim, Work.WilG4c.LimeqP, hc] using hproj

/-- **`Ω`-definability of the corrected value-free criterion `UVFix`.** -/
theorem uvfix_mem (S : WilkiesDesign.SOMin) (hder : WilkiesDesign.SOMin.SharpDeriv S)
    (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D k : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.UVFix p n f k ∈ S.Ω a (MvPolynomial.eval ![D, k] b) (p + (n + 1)) := by
  obtain ⟨aC, bC, hC⟩ := Work.WilkG4c.CritFixAux.contSetMem S p n F0
  obtain ⟨aL, bL, hL⟩ := limcond_fix_mem S hder p n F0
  refine ⟨max aC (aL + 1) + 1,
    bC + (MvPolynomial.X (1 : Fin 2) + MvPolynomial.C 2) ^ (n + 2) * bL, ?_⟩
  intro D k f hf
  have hcon := hC D k f hf
  have hLim : (⋂ i ∈ Work.WilkG4c.critIdxFix n k,
      Work.WilkG4c.LimCond p n f (i.1.val + 1) (fun j => (i.2 j).val)) ∈
      S.Ω (aL + 1) (MvPolynomial.eval ![D, k]
        (MvPolynomial.C (Work.WilkG4c.critIdxFix n k).card * bL)) (p + (n + 1)) :=
    finset_inter_mem _ _ (fun i _ => hL D k f i hf)
  have hcard : MvPolynomial.eval ![D, k]
        (MvPolynomial.C (Work.WilkG4c.critIdxFix n k).card * bL)
      ≤ MvPolynomial.eval ![D, k]
        ((MvPolynomial.X (1 : Fin 2) + MvPolynomial.C 2) ^ (n + 2) * bL) := by
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      eval_X1_add_two_pow]
    exact Nat.mul_le_mul_right _ (Work.WilkG4c.CritFixAux.card_critIdxFix_le n k)
  have hLim' := Work.WilG1.Omega.mono hLim le_rfl hcard
  have hboth := Work.WilkG4c.inter_mv hcon hLim'
  rw [Work.WilkG4c.UVFix]
  exact hboth

end Work.WilkG4c.GZ
