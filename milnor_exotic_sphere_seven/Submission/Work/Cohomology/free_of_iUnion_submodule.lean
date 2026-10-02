import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A countable increasing union of free `ℤ`-modules with free successive quotients is free

`Work.Cohomology.free_of_iUnion_submodule` proves that if a `ℤ`-module `M` is the union of an
increasing sequence `A 0 ≤ A 1 ≤ ⋯` of free submodules, each step splitting as an internal direct
sum `A (n+1) = A n ⊔ C n` with `C n` free, then `M` itself is free.

The proof follows the natural line: the family `ℳ` with `ℳ 0 = A 0` and `ℳ (n+1) = C n` is an
internal direct sum decomposition of `M`, so `M ≃ₗ[ℤ] ⨁ n, ℳ n` is a direct sum of free modules.

* Spanning, `⨆ n, ℳ n = ⊤`: by induction `A n = A 0 ⊔ C 0 ⊔ ⋯ ⊔ C (n-1)` lies in `⨆ n, ℳ n`, and
  every element of `M` lies in some `A n`.
* Independence, `iSupIndep ℳ`: this is proved through the criterion
  `iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero`.  Given `∑ i ∈ s, v i = 0` with `v i ∈ ℳ i` and
  `k = max s`, all the terms other than `v k` are indexed by `i < k` and hence lie in `A (k-1)`,
  so `v k = -∑ i ∈ s.erase k, v i ∈ A (k-1)`, while `v k ∈ ℳ k = C (k-1)`; these two submodules are
  disjoint, so `v k = 0`, and induction on the finset finishes.  (The case `k = 0` is degenerate:
  then `s.erase k` is empty and `v k = 0` directly.)
* The identification `M ≃ₗ[ℤ] ⨁ n, ℳ n` is obtained from the additive equivalence
  `DirectSum.decomposeAddEquiv` of the internal decomposition together with
  `AddEquiv.toIntLinearEquiv`: an additive equivalence of abelian groups is `ℤ`-linear, and the two
  `ℤ`-module structures are *arguments* of that construction, so they are determined by unification
  with the surrounding data rather than by instance synthesis.  This is what keeps the proof clear
  of the `Submodule.module` / `AddCommGroup.toIntModule` instance diamond (which instance search
  resolves inconsistently for the subtype `↥(ℳ n)` and for `⨁ n, ↥(ℳ n)`).
* The final transfer of freeness uses `Module.Free.directSum` and `Module.Free.of_equiv'`. -/

namespace Work.Cohomology

open scoped Classical

/-- **A countable increasing union of free submodules with free successive quotients is free.**

If a `ℤ`-module `M` is the union of an increasing sequence of submodules `A n` such that each `A n`
is free and each step splits as an internal direct sum `A (n+1) = A n ⊔ C n` with `C n` free, then
`M` is free: indeed `M ≅ A 0 ⊕ ⨁ n, C n`.

Suggested proof: choose the complements `C n`.  By induction `A n = A 0 ⊔ C 0 ⊔ ⋯ ⊔ C (n-1)` is an
internal direct sum; hence the family `(C n)` is independent and `M = A 0 ⊕ ⨁ n, C n`.  Formally:
build the linear map `A 0 × DirectSum ℕ (fun n => C n) → M`, `(a, d) ↦ a + ∑ d` (using
`DirectSum.toModule`), show it is injective (independence, using the finite support of `d`) and
surjective (`hspan` plus the partial decompositions), and conclude with `Module.Free.of_equiv'`
from `Module.Free.prod` and `Module.Free.directSum`.  To avoid `ℤ`-module instance diamonds
between `Submodule.module` and `AddCommGroup.toIntModule` one may need
`attribute [local instance 5000] Submodule.module` and/or
`set_option backward.isDefEq.respectTransparency false`. -/
theorem free_of_iUnion_submodule {M : Type*} [AddCommGroup M] [Module ℤ M]
    (A : ℕ → Submodule ℤ M) (hmono : ∀ n, A n ≤ A (n + 1))
    (hA : ∀ n, Module.Free ℤ ↥(A n))
    (hsplit : ∀ n, ∃ (C : Submodule ℤ M),
      Disjoint (A n) C ∧ A n ⊔ C = A (n + 1) ∧ Module.Free ℤ ↥C)
    (hspan : ∀ x : M, ∃ n, x ∈ A n) :
    Module.Free ℤ M := by
  classical
  -- choose the complementary summands `C n`
  choose C hdisj hsupC hCfree using hsplit
  -- the family `ℳ` given by `ℳ 0 = A 0` and `ℳ (n+1) = C n`
  let ℳ : ℕ → Submodule ℤ M := fun n => match n with
    | 0 => A 0
    | (k + 1) => C k
  have hMs : ∀ k, ℳ (k + 1) = C k := fun k => rfl
  have hmonoA : Monotone A := monotone_nat_of_le_succ hmono
  -- every member of the family, indexed by `i ≤ m`, lies in `A m`
  have hMA : ∀ i m, i ≤ m → ℳ i ≤ A m := by
    intro i m him
    match i with
    | 0 => exact hmonoA (Nat.zero_le m)
    | k + 1 =>
      rw [hMs k]
      exact le_trans (le_trans le_sup_right (le_of_eq (hsupC k))) (hmonoA him)
  -- the family spans `M`
  have hle : ∀ n, A n ≤ ⨆ i, ℳ i := by
    intro n
    induction n with
    | zero => exact le_iSup ℳ 0
    | succ n ih =>
      have h1 : A (n + 1) = A n ⊔ ℳ (n + 1) := by
        rw [hMs n, hsupC n]
      rw [h1]
      exact sup_le ih (le_iSup ℳ (n + 1))
  have hsup : ⨆ i, ℳ i = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    obtain ⟨n, hn⟩ := hspan x
    exact hle n hn
  -- the family `ℳ` is independent
  have hind : iSupIndep ℳ := by
    rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s
    refine Finset.strongInductionOn s (fun s ih v hv hsum i hi => ?_)
    rcases s.eq_empty_or_nonempty with rfl | hsne
    · simp at hi
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, k = s.max' hsne ∧ k ∈ s :=
      ⟨_, rfl, Finset.max'_mem s hsne⟩
    have hsumk : ∑ x ∈ s.erase k, v x + v k = 0 :=
      (Finset.sum_erase_add s v hk2).trans hsum
    rcases k with _ | k'
    · -- the largest index is `0`, so `s = {0}` and there is nothing to cancel against
      have herase : s.erase 0 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        rw [Finset.mem_erase] at hx
        have hxle : x ≤ s.max' hsne := Finset.le_max' s x hx.2
        omega
      have hvk : v 0 = 0 := by
        have h := hsumk
        rw [herase, Finset.sum_empty, zero_add] at h
        exact h
      have hi0 : i = 0 := by
        have hile : i ≤ s.max' hsne := Finset.le_max' s i hi
        omega
      rw [hi0]
      exact hvk
    · -- the largest index is `k' + 1`: the remaining terms lie in `A k'`, which is disjoint from
      -- `C k' = ℳ (k'+1)`
      have hxle : ∀ x ∈ s.erase (k' + 1), x ≤ k' := by
        intro x hx
        have h := Finset.lt_max'_of_mem_erase_max' s hsne (hk1 ▸ hx)
        omega
      have hmemA : (∑ x ∈ s.erase (k' + 1), v x) ∈ A k' :=
        Submodule.sum_mem (A k') fun x hx =>
          hMA x k' (hxle x hx) (hv x (Finset.mem_of_mem_erase hx))
      have hvk : v (k' + 1) = 0 := by
        have hC : v (k' + 1) ∈ C k' := by
          have hmem := hv (k' + 1) hk2
          rwa [hMs k'] at hmem
        refine (Submodule.disjoint_def.mp (hdisj k')) _ ?_ hC
        rw [eq_neg_of_add_eq_zero_right hsumk]
        exact (A k').neg_mem hmemA
      have hsum0 : ∑ x ∈ s.erase (k' + 1), v x = 0 := by
        have h := hsumk
        rw [hvk, add_zero] at h
        exact h
      have hrest : ∀ x ∈ s.erase (k' + 1), v x = 0 :=
        ih (s.erase (k' + 1)) (Finset.erase_ssubset hk2) v
          (fun x hx => hv x (Finset.mem_of_mem_erase hx)) hsum0
      rw [← Finset.insert_erase hk2] at hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact hvk
      · exact hrest i hi'
  -- each member of the family is free (`hfreeI` is also used as a local instance below)
  have hfreeI : ∀ i, Module.Free ℤ ↥(ℳ i) := by
    intro i
    match i with
    | 0 => exact hA 0
    | k + 1 =>
      rw [hMs k]
      exact hCfree k
  -- the family is an internal direct sum decomposition of `M`, and `M ≃ₗ[ℤ] ⨁ i, ℳ i`
  have hdec : DirectSum.Decomposition ℳ :=
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top ℳ).mpr ⟨hind, hsup⟩).chooseDecomposition
  have hD := Module.Free.directSum ℤ (fun i => ↥(ℳ i))
  have d := DirectSum.decomposeAddEquiv ℳ
  exact Module.Free.of_equiv' hD d.symm.toIntLinearEquiv

end Work.Cohomology
