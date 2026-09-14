import Mathlib
import Submission.Subspace.ElimIter
import Submission.Subspace.ElimBlock

/-!
# The geometric elimination (Schmidt's specialization)

Let `F ∈ K[X (h,j)]` (`h : Fin m`, `j : Fin N`) be a polynomial and let
`l_h = ∑_j b h j X (h,j)` be the linear form defining the hyperplane `V_h`.  Writing
`Φ` for the substitution which solves `l_h = 0` for the pivot variable `X (h,0)`, the condition
"`f` vanishes on `∏_h V_h`" is `Φ f = 0`.  Eliminating the variables `X (h,j)` with `j ≥ 2`
(keeping `X (h,0)` and a second coordinate `q` of value `1`) turns this into a statement about
a polynomial in two variables per block.
-/

open scoped BigOperators
open MvPolynomial

namespace Submission.Subspace

variable {K : Type*} [Field K] {m N : ℕ} [NeZero N]

/-- The list of "eliminated" variables: all `(h,j)` with `j ≥ 2`. -/
noncomputable def elimList (m N : ℕ) : List (Fin m × Fin N) :=
  ((Finset.univ : Finset (Fin m × Fin N)).filter (fun y => 2 ≤ (y.2 : ℕ))).toList

lemma elimList_toFinset (m N : ℕ) :
    (elimList m N).toFinset =
      (Finset.univ.filter (fun y : Fin m × Fin N => 2 ≤ (y.2 : ℕ))) := by
  rw [elimList]
  exact Finset.toList_toFinset _

lemma mem_elimList_toFinset {h : Fin m} {j : Fin N} :
    (h, j) ∈ (elimList m N).toFinset ↔ 2 ≤ (j : ℕ) := by
  rw [elimList_toFinset, Finset.mem_filter]
  simp

/-- The substitution solving the linear system `l_h = 0` for the pivot variable `X (h,0)`. -/
noncomputable def pivotSubst (b : Fin m → Fin N → K) :
    MvPolynomial (Fin m × Fin N) K →ₐ[K] MvPolynomial (Fin m × Fin N) K :=
  MvPolynomial.aeval fun hi : Fin m × Fin N =>
    if hi.2 = 0 then
      MvPolynomial.C (-((b hi.1 0)⁻¹)) *
        ∑ j ∈ Finset.univ.erase 0, MvPolynomial.C (b hi.1 j) * MvPolynomial.X (hi.1, j)
    else MvPolynomial.X hi

/-- The substitution obtained after eliminating the variables `j ≥ 2`: `X (h,0)` is sent to
`-(b h 0)⁻¹ b h q • X (h,q)`, `X (h,q)` is fixed (for the "second" coordinate `q`) and all
other variables are killed. -/
noncomputable def chartSubst (b : Fin m → Fin N → K) (q : Fin N) :
    MvPolynomial (Fin m × Fin N) K →ₐ[K] MvPolynomial (Fin m × Fin N) K :=
  MvPolynomial.aeval fun hi : Fin m × Fin N =>
    if hi.2 = 0 then MvPolynomial.C (-((b hi.1 0)⁻¹) * b hi.1 q) * MvPolynomial.X (hi.1, q)
    else if hi.2 = q then MvPolynomial.X hi
    else 0

lemma pivotSubst_X_zero (b : Fin m → Fin N → K) (h : Fin m) :
    pivotSubst b (MvPolynomial.X (h, 0) : MvPolynomial (Fin m × Fin N) K) =
      MvPolynomial.C (-((b h 0)⁻¹)) *
        ∑ j ∈ Finset.univ.erase 0, MvPolynomial.C (b h j) * MvPolynomial.X (h, j) := by
  rw [pivotSubst, MvPolynomial.aeval_X]
  exact if_pos rfl

lemma pivotSubst_X_of_ne (b : Fin m → Fin N → K) (h : Fin m) {j : Fin N} (hj : j ≠ 0) :
    pivotSubst b (MvPolynomial.X (h, j) : MvPolynomial (Fin m × Fin N) K) =
      MvPolynomial.X (h, j) := by
  rw [pivotSubst, MvPolynomial.aeval_X]
  exact if_neg hj

lemma chartSubst_X_zero (b : Fin m → Fin N → K) (q : Fin N) (h : Fin m) :
    chartSubst b q (MvPolynomial.X (h, 0) : MvPolynomial (Fin m × Fin N) K) =
      MvPolynomial.C (-((b h 0)⁻¹) * b h q) * MvPolynomial.X (h, q) := by
  rw [chartSubst, MvPolynomial.aeval_X]
  exact if_pos rfl

lemma chartSubst_X_q (b : Fin m → Fin N → K) {q : Fin N} (hq0 : q ≠ 0) (h : Fin m) :
    chartSubst b q (MvPolynomial.X (h, q) : MvPolynomial (Fin m × Fin N) K) =
      MvPolynomial.X (h, q) := by
  rw [chartSubst, MvPolynomial.aeval_X, if_neg hq0, if_pos rfl]

lemma chartSubst_X_of_other (b : Fin m → Fin N → K) {q : Fin N} (h : Fin m) {j : Fin N}
    (hj0 : j ≠ 0) (hjq : j ≠ q) :
    chartSubst b q (MvPolynomial.X (h, j) : MvPolynomial (Fin m × Fin N) K) = 0 := by
  rw [chartSubst, MvPolynomial.aeval_X, if_neg hj0, if_neg hjq]

lemma kill_C' (a : K) (S : Finset (Fin m × Fin N)) :
    kill S (MvPolynomial.C a : MvPolynomial (Fin m × Fin N) K) = MvPolynomial.C a := by
  rw [kill, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

/-- The composition of the elimination substitutions with the pivot substitution. -/
theorem elimRho_pivotSubst (b : Fin m → Fin N → K) (hb : ∀ h, b h 0 ≠ 0)
    {q : Fin N} (hq : (q : ℕ) = 1) :
    elimRho (elimList m N) (pivotSubst b) = chartSubst b q := by
  rw [elimRho_eq_kill]
  refine MvPolynomial.algHom_ext fun z => ?_
  obtain ⟨h, j⟩ := z
  rw [AlgHom.comp_apply]
  have hq0 : q ≠ 0 := by intro hh; rw [hh] at hq; simp at hq
  have hkill : ∀ j' : Fin N, kill (elimList m N).toFinset
      (MvPolynomial.X (h, j') : MvPolynomial (Fin m × Fin N) K) =
      if 2 ≤ (j' : ℕ) then 0 else MvPolynomial.X (h, j') := by
    intro j'
    by_cases hj : 2 ≤ (j' : ℕ)
    · rw [if_pos hj, kill_X_of_mem (mem_elimList_toFinset.mpr hj)]
    · rw [if_neg hj, kill_X_of_notMem (fun hmem => hj (mem_elimList_toFinset.mp hmem))]
  by_cases hj0 : j = 0
  · subst hj0
    rw [pivotSubst_X_zero, chartSubst_X_zero, map_mul, kill_C', map_sum]
    have hsum : ∀ j' : Fin N, kill (elimList m N).toFinset
        (MvPolynomial.C (b h j') * MvPolynomial.X (h, j') : MvPolynomial (Fin m × Fin N) K) =
        MvPolynomial.C (b h j') * (if 2 ≤ (j' : ℕ) then 0 else MvPolynomial.X (h, j')) := by
      intro j'
      rw [map_mul, kill_C', hkill j']
    rw [Finset.sum_congr rfl fun j' _ => hsum j']
    have hqz : (q : ℕ) ≠ 0 := by omega
    have hqmem : q ∈ Finset.univ.erase (0 : Fin N) :=
      Finset.mem_erase.mpr ⟨(fun hh => hqz (by rw [hh]; rfl)), Finset.mem_univ q⟩
    rw [Finset.sum_eq_single q]
    · rw [if_neg (by omega : ¬ (2 ≤ (q : ℕ)))]
      rw [show MvPolynomial.C (-((b h 0)⁻¹)) *
            (MvPolynomial.C (b h q) * MvPolynomial.X (h, q)) =
          MvPolynomial.C (-((b h 0)⁻¹) * b h q) * MvPolynomial.X (h, q) from by
        rw [← mul_assoc, MvPolynomial.C_mul]]
    · intro j' hmem hjne
      have hj'2 : 2 ≤ (j' : ℕ) := by
        rw [Finset.mem_erase] at hmem
        have h1 : (j' : ℕ) ≠ 0 := fun hh => hmem.1 (Fin.ext (by simp [hh]))
        have h2 : (j' : ℕ) ≠ 1 := fun hh => hjne (Fin.ext (by
          show (j' : ℕ) = (q : ℕ)
          rw [hh, hq]))
        exact lt_of_le_of_ne (Nat.succ_le_of_lt (Nat.pos_of_ne_zero h1)) (Ne.symm h2)
      rw [if_pos hj'2, mul_zero]
    · intro hnot
      exact absurd hqmem hnot
  · rw [pivotSubst_X_of_ne b h hj0, hkill j]
    by_cases hj2 : 2 ≤ (j : ℕ)
    · rw [if_pos hj2, chartSubst_X_of_other b h (by omega) (by
        intro hh
        rw [hh] at hj2
        rw [hq] at hj2
        exact absurd hj2 (by norm_num))]
    · rw [if_neg hj2]
      have hjq : j = q := by
        have hle : (j : ℕ) ≤ 1 := by omega
        have hj0' : (j : ℕ) ≠ 0 := fun hh => hj0 (Fin.ext (by simpa using hh))
        refine Fin.ext ?_
        omega
      subst hjq
      rw [chartSubst_X_q b hq0 h]


/-- The point of the "two variables per block" variety: `X (h,0) ↦ b h q` and
`X (h,q) ↦ -(b h 0)`, all other variables being `0`. -/
noncomputable def pivotPoint (b : Fin m → Fin N → K) (q : Fin N) : Fin m × Fin N → K :=
  fun hi => if hi.2 = 0 then b hi.1 q else if hi.2 = q then -(b hi.1 0) else 0

/-- Composition of two substitutions. -/
lemma aeval_comp_aeval {σ : Type*} [Fintype σ] [DecidableEq σ] {A : Type*} [CommSemiring A]
    [Algebra K A] (ψ : σ → MvPolynomial σ K) (g : MvPolynomial σ K →ₐ[K] A) :
    g.comp (MvPolynomial.aeval ψ) = MvPolynomial.aeval (fun z => g (ψ z)) := by
  refine MvPolynomial.algHom_ext fun z => ?_
  rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X]

/-- If the dehomogenised elimination result vanishes, then the original polynomial vanishes at
the point `(b h q, -b h 0)_h` of the variety. -/
theorem aeval_chartSubst_eq_zero (b : Fin m → Fin N → K) (hb : ∀ h, b h 0 ≠ 0)
    {q : Fin N} (hq0 : q ≠ 0) (f : MvPolynomial (Fin m × Fin N) K)
    (hf : chartSubst b q f = 0) :
    MvPolynomial.aeval (pivotPoint b q) f = 0 := by
  have hcomp : (MvPolynomial.aeval (pivotPoint b q)).comp (chartSubst b q) =
      MvPolynomial.aeval (pivotPoint b q) := by
    rw [chartSubst, aeval_comp_aeval]
    congr 1
    funext z
    obtain ⟨h, j⟩ := z
    by_cases hj0 : j = 0
    · subst hj0
      rw [if_pos rfl, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
      show -((b h 0)⁻¹) * b h q * pivotPoint b q (h, q) = pivotPoint b q (h, 0)
      rw [show pivotPoint b q (h, q) = -(b h 0) from by
            rw [pivotPoint, if_neg hq0, if_pos rfl],
        show pivotPoint b q (h, 0) = b h q from by rw [pivotPoint, if_pos rfl]]
      have hone : -(b h 0)⁻¹ * (-(b h 0)) = 1 := by
        rw [neg_mul_neg, inv_mul_cancel₀ (hb h)]
      calc -(b h 0)⁻¹ * b h q * -(b h 0)
          = b h q * (-(b h 0)⁻¹ * -(b h 0)) := by ring
        _ = b h q * 1 := by rw [hone]
        _ = b h q := by ring
    · rw [if_neg hj0]
      by_cases hjq : j = q
      · subst hjq
        rw [if_pos rfl, MvPolynomial.aeval_X]
      · rw [if_neg hjq, map_zero]
        rw [show pivotPoint b q (h, j) = 0 from by
              rw [pivotPoint, if_neg hj0, if_neg hjq]]
  rw [← hcomp, AlgHom.comp_apply, hf, map_zero]

end Submission.Subspace

