import Mathlib
import Submission.Work.DSEQ0.SurjBasic

/-!
# `Work.DSEQ0.FAcyclic_succ`

The ascending step of the image-size filtration of the Čech (surjection) complex.

Recall (`SurjBasic.lean`) that `D k` is the group of `M`-valued functions on `(k+1)`-tuples of
`ι`, `F m` is the subcomplex of functions vanishing on tuples whose image has fewer than `m`
elements, `FAcyclic m m₀` says `F m` is acyclic above degree `m₀`, and `GrAcyclic m m₀` says the
graded piece `F m / F (m+1)` is acyclic above degree `m₀`.

This file proves: if `F m` is acyclic above degree `m` and `gr m = F m / F (m+1)` is acyclic
above degree `m`, then `F (m+1)` is acyclic above degree `m+1`.

The proof is the long exact sequence of `0 → F (m+1) → F m → gr m → 0`, made explicit.  Given a
cocycle `f ∈ F (m+1)` of degree `k+1 ≥ m+1`:

* `FAcyclic m m` (valid since `k+1 ≥ m`) gives `h ∈ F m` of degree `k` with `d h = f`;
* `d h = f ∈ F (m+1)` says the class of `h` in `gr m` is a cocycle, so `GrAcyclic m m` at degree
  `k` (valid since `k ≥ m`) gives `g ∈ F m` of degree `k-1` with `d g - h ∈ F (m+1)`;
* then `h' = h - d g ∈ F (m+1)` and `d h' = d h - d d g = f`.

The `GrAcyclic` step is isolated in `grAcyclic_lift` below.
-/

namespace Work.DSEQ0

universe u

variable {ι : Type u} [Fintype ι] {M : Type u} [AddCommGroup M]

/-- The alternating coboundary satisfies `d ∘ d = 0`.

Writing out `cob (k+1) (cob k f)` at a tuple `x` gives the signed double sum
`∑_{p : Fin (k+3) × Fin (k+2)} (-1)^{p.1 + p.2} • f (x ∘ (succAbove p.1 ∘ succAbove p.2))`.
The map `τ p = (p.1.succAbove p.2, p.2.predAbove p.1)` is a fixed-point-free involution of the
index set — the two "insert the same pair of values in the other order" presentations of the
composite — by the cosimplicial identities `Fin.succAbove_succAbove_predAbove` and
`Fin.predAbove_predAbove_succAbove`.  It leaves the composite `succAbove p.1 ∘ succAbove p.2`
unchanged (`Fin.removeNth_removeNth_eq_swap`) while reversing the parity of `p.1 + p.2`, so
`Finset.sum_involution` makes the whole sum vanish. -/
theorem cob_cob_aux (k : ℕ) (f : (Fin (k + 1) → ι) → M) : cob (k + 1) (cob k f) = 0 := by
  funext x
  simp only [cob, Pi.zero_apply]
  simp only [Finset.smul_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ _
    dsimp only
    have hcomp : (x ∘ j.succAbove) ∘ i.succAbove
        = (x ∘ (j.succAbove i).succAbove) ∘ (i.predAbove j).succAbove := by
      funext t
      have := congrFun (Fin.removeNth_removeNth_eq_swap x i j) t
      simpa only [Function.comp_apply, Fin.removeNth] using this
    rw [← hcomp]
    have hpar : ((j.succAbove i).val : ℕ) + ((i.predAbove j).val : ℕ) = (j:ℕ) + (i:ℕ) + 1
        ∨ (j:ℕ) + (i:ℕ) = ((j.succAbove i).val : ℕ) + ((i.predAbove j).val : ℕ) + 1 := by
      by_cases h : (j:ℕ) ≤ (i:ℕ)
      · left
        have hh : j ≤ i.castSucc := Fin.le_def.mpr (by simpa only [Fin.val_castSucc] using h)
        have h1 : ((j.succAbove i).val : ℕ) = (i:ℕ) + 1 := by
          rw [Fin.succAbove_of_le_castSucc j i hh, Fin.val_succ]
        have h2 : ((i.predAbove j).val : ℕ) = (j:ℕ) := by
          rw [Fin.predAbove_of_le_castSucc i j hh]; rfl
        omega
      · right
        have h' : (i:ℕ) < (j:ℕ) := Nat.lt_of_not_le h
        have hh : i.castSucc < j := Fin.lt_def.mpr (by simpa only [Fin.val_castSucc] using h')
        have h1 : ((j.succAbove i).val : ℕ) = (i:ℕ) := by
          rw [Fin.succAbove_of_castSucc_lt j i hh]; exact Fin.val_castSucc i
        have h2 : ((i.predAbove j).val : ℕ) = (j:ℕ) - 1 := by
          rw [Fin.predAbove_of_castSucc_lt i j hh]; exact Fin.val_pred j _
        omega
    have hsign : (-1:ℤ) ^ ((j.succAbove i).val) * (-1:ℤ) ^ ((i.predAbove j).val)
        = - ((-1:ℤ) ^ (j:ℕ) * (-1:ℤ) ^ (i:ℕ)) := by
      rw [← pow_add, ← pow_add]
      rcases hpar with h | h
      · rw [h, pow_succ]; ring
      · rw [h, pow_succ]; ring
    rw [smul_smul, smul_smul, hsign, neg_smul, ← smul_smul, add_neg_cancel]
  · rintro ⟨j, i⟩ _ hne hfix
    dsimp only at hfix
    exact Fin.succAbove_ne j i (by simpa using congrArg Prod.fst hfix)
  · rintro ⟨j, i⟩ _
    simp
  · rintro ⟨j, i⟩ _
    dsimp only
    apply Prod.ext
    · exact Fin.succAbove_succAbove_predAbove j i
    · exact Fin.predAbove_predAbove_succAbove j i

/-- `inF m` is closed under negation. -/
theorem inF_neg {m k : ℕ} {f : (Fin (k + 1) → ι) → M} (hf : inF m f) : inF m (-f) :=
  fun g hg => by rw [Pi.neg_apply, hf g hg, neg_zero]

/-- Consequence of `GrAcyclic m m` used by the long exact sequence argument: if `f ∈ F m` of
degree `j+1` has `d f ∈ F (m+1)`, then `d f` is already a coboundary *in* `F (m+1)`, i.e. there
is `h ∈ F (m+1)` of degree `j+1` with `d h = d f`.

(Explicitly `h = f - d g` for the `g ∈ F m` produced by `GrAcyclic m m`.) -/
theorem grAcyclic_lift {m j : ℕ} (hgr : @GrAcyclic ι M _ m m) (hmj : m ≤ j + 1)
    (f : (Fin (j + 2) → ι) → M) (hf : inF m f) (hfd : inF (m + 1) (cob (j + 1) f)) :
    ∃ h : (Fin (j + 2) → ι) → M, inF (m + 1) h ∧ cob (j + 1) h = cob (j + 1) f := by
  obtain ⟨h', hh', hh'd⟩ := hgr j hmj f hf hfd
  refine ⟨f - cob j h', ?_, ?_⟩
  · rw [← neg_sub]
    exact inF_neg hh'd
  · rw [cob_sub, cob_cob_aux, sub_zero]

theorem FAcyclic_succ {ι : Type u} [Fintype ι] {M : Type u} [AddCommGroup M] (m : ℕ) (hm : 1 ≤ m)
    (hF : @FAcyclic ι M _ m m) (hgr : @GrAcyclic ι M _ m m) :
    @FAcyclic ι M _ (m + 1) (m + 1) := by
  intro k hk f hf hcob
  have hmk : m ≤ k := by omega
  obtain ⟨h, hh, hdh⟩ := hF k (by omega) f (inF_anti (by omega : m ≤ m + 1) hf) hcob
  obtain ⟨j, hjk⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  subst hjk
  obtain ⟨h₂, h₂in, h₂eq⟩ :=
    grAcyclic_lift (m := m) (j := j) hgr (by omega) h hh (by rw [hdh]; exact hf)
  exact ⟨h₂, h₂in, by rw [h₂eq, hdh]⟩

end Work.DSEQ0
