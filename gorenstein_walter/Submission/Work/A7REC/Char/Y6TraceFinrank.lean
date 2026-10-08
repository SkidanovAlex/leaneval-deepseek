/-
# `A7Y6TraceFinrankProp`: an element of order `7` is never in the kernel of a trace-`6` map

We prove `Work.A7REC.A7Y6TraceFinrankProp`: for a representation `ρ : G → GL(V)` of a group `G`
on a finite dimensional `ℂ`-vector space `V`, and `x : G` of order `7`, the equality
`trace (ρ x) = dim V` forces `ρ x = 1`.

The mathematical content is the following linear-algebra statement (proved here as
`end_eq_one_of_pow_seven_eq_one`): if `A : End ℂ V` satisfies `A ^ 7 = 1` and
`trace A = finrank ℂ V`, then `A = 1`.

Proof sketch of the linear-algebra statement.  Since `ℂ` is algebraically closed, the
characteristic polynomial of `A` splits, so `trace A` is the sum of the `finrank ℂ V` roots of
`charpoly A` (with multiplicity).  Every root `ω` is an eigenvalue of `A`, hence `ω ^ 7 = 1`
(the eigenvector computation), so in particular `‖ω‖ = 1` and `Re ω ≤ 1`.  Combining
`∑ ω = trace A = finrank ℂ V` with `∑ 1 = finrank ℂ V` gives `∑ (1 - Re ω) = 0`; each summand is
non-negative, so every root has `Re ω = 1`, and together with `ω ^ 7 = 1` this forces `ω = 1`.
Thus all eigenvalues of `A` are `1`.  Finally `A ^ 7 = 1` shows that the minimal polynomial of `A`
divides the squarefree polynomial `X ^ 7 - 1`, so `A` is semisimple, and a semisimple
endomorphism all of whose eigenvalues are `1` is the identity.

The `7`-th root of unity occurrences are packaged as the helper lemmas
`complex_re_le_one_of_pow_seven` and `complex_eq_one_of_pow_seven_of_re`; the
"sum of non-negative reals vanishes termwise" step is `multiset_sum_nonneg` and
`multiset_forall_eq_zero_of_sum_eq_zero_of_nonneg`.
-/
import Mathlib
import Submission.Work.A7REC.Char.Y6Defs

namespace Work.A7REC.Char

/-! ## Elementary facts about the `7`-th roots of unity -/

/-- A multiset of non-negative reals has a non-negative sum. -/
private lemma multiset_sum_nonneg {s : Multiset ℝ} (h : ∀ x ∈ s, 0 ≤ x) : 0 ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons]
    exact add_nonneg (h a (Multiset.mem_cons_self a s))
      (ih (fun x hx => h x (Multiset.mem_cons_of_mem hx)))

/-- If all elements of a multiset of reals are non-negative and the sum vanishes, then every
element vanishes. -/
private lemma multiset_forall_eq_zero_of_sum_eq_zero_of_nonneg {s : Multiset ℝ}
    (h : ∀ x ∈ s, 0 ≤ x) (hs : s.sum = 0) : ∀ x ∈ s, x = 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons] at hs
    have h' : ∀ x ∈ s, 0 ≤ x := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have hsnn : 0 ≤ s.sum := multiset_sum_nonneg h'
    have ha : 0 ≤ a := h a (Multiset.mem_cons_self a s)
    have ha0 : a = 0 := by linarith
    have hs' : s.sum = 0 := by linarith
    intro x hx
    rcases Multiset.mem_cons.mp hx with hxa | hxs
    · exact hxa ▸ ha0
    · exact ih h' hs' x hxs

/-- The real part of an `ω : ℂ` with `ω ^ 7 = 1` is at most `1`. -/
private lemma complex_re_le_one_of_pow_seven (ω : ℂ) (h : ω ^ 7 = 1) : ω.re ≤ 1 := by
  have hnorm : ‖ω‖ = 1 := by
    have h1 : ‖ω‖ ^ 7 = 1 := by rw [← norm_pow, h, norm_one]
    rcases lt_trichotomy ‖ω‖ 1 with hlt | heq | hgt
    · have := pow_lt_one₀ (norm_nonneg ω) hlt (by norm_num : (7:ℕ) ≠ 0)
      rw [h1] at this; exact absurd this (lt_irrefl 1)
    · exact heq
    · have := one_lt_pow₀ hgt (by norm_num : (7:ℕ) ≠ 0)
      rw [h1] at this; exact absurd this (lt_irrefl 1)
  calc ω.re ≤ ‖ω‖ := Complex.re_le_norm ω
    _ = 1 := hnorm

/-- An `ω : ℂ` with `ω ^ 7 = 1` and real part `1` is `1`. -/
private lemma complex_eq_one_of_pow_seven_of_re (ω : ℂ) (h : ω ^ 7 = 1) (hre : ω.re = 1) :
    ω = 1 := by
  have hnorm : ‖ω‖ = 1 := by
    have h1 : ‖ω‖ ^ 7 = 1 := by rw [← norm_pow, h, norm_one]
    rcases lt_trichotomy ‖ω‖ 1 with hlt | heq | hgt
    · have := pow_lt_one₀ (norm_nonneg ω) hlt (by norm_num : (7:ℕ) ≠ 0)
      rw [h1] at this; exact absurd this (lt_irrefl 1)
    · exact heq
    · have := one_lt_pow₀ hgt (by norm_num : (7:ℕ) ≠ 0)
      rw [h1] at this; exact absurd this (lt_irrefl 1)
  have him : ω.im = 0 := by
    have h1 : Complex.normSq ω = 1 := by rw [Complex.normSq_eq_norm_sq, hnorm]; norm_num
    rw [Complex.normSq_apply, hre] at h1
    have : ω.im * ω.im = 0 := by linarith
    exact mul_self_eq_zero.mp this
  exact Complex.ext hre (by rw [him]; rfl)

/-! ## The linear-algebra statement -/

/-- If `A : End ℂ V` has `A ^ 7 = 1` and `trace A = finrank ℂ V`, then `A = 1`. -/
private lemma end_eq_one_of_pow_seven_eq_one {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Module.End ℂ V) (hA : A ^ 7 = 1)
    (htr : LinearMap.trace ℂ V A = (Module.finrank ℂ V : ℂ)) : A = 1 := by
  have hne : LinearMap.charpoly A ≠ 0 := (LinearMap.charpoly_monic A).ne_zero
  have hsplit : (LinearMap.charpoly A).Splits := IsAlgClosed.splits _
  have hroots_sum : (LinearMap.charpoly A).roots.sum = (Module.finrank ℂ V : ℂ) := by
    rw [← Module.End.trace_eq_sum_roots_charpoly_of_splits hsplit, htr]
  have hcard : (LinearMap.charpoly A).roots.card = Module.finrank ℂ V := by
    rw [Polynomial.splits_iff_card_roots.mp hsplit, LinearMap.charpoly_natDegree]
  -- every root of the characteristic polynomial is a `7`-th root of unity
  have hpow : ∀ ω ∈ (LinearMap.charpoly A).roots, ω ^ 7 = 1 := by
    intro ω hω
    have hroot : (LinearMap.charpoly A).IsRoot ω := (Polynomial.mem_roots hne).mp hω
    have hev : A.HasEigenvalue ω := (Module.End.hasEigenvalue_iff_isRoot_charpoly A ω).mpr hroot
    rw [Module.End.hasEigenvalue_iff] at hev
    obtain ⟨v, hv, hvne⟩ := Submodule.ne_bot_iff _ |>.mp hev
    rw [Module.End.mem_eigenspace_iff] at hv
    have hk : ∀ k : ℕ, (A ^ k) v = (ω ^ k) • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ih, LinearMap.map_smul, hv, smul_smul, pow_succ]
    have h7 := hk 7
    rw [hA, Module.End.one_apply] at h7
    have hz : (ω ^ 7 - 1) • v = 0 := by
      rw [sub_smul, one_smul]
      rw [h7.symm, sub_self]
    rcases smul_eq_zero.mp hz with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hvne
  -- the sum of `1 - re ω` over the roots vanishes
  have hsum : ((LinearMap.charpoly A).roots.map (fun ω => (1:ℝ) - ω.re)).sum = 0 := by
    rw [Multiset.sum_map_sub]
    have h1 : (Multiset.map (fun _ : ℂ => (1:ℝ)) (LinearMap.charpoly A).roots).sum =
        (Module.finrank ℂ V : ℝ) := by
      have : (Multiset.map (fun _ : ℂ => (1:ℝ)) (LinearMap.charpoly A).roots) =
          Multiset.replicate (LinearMap.charpoly A).roots.card (1:ℝ) := Multiset.map_const _ _
      rw [this, Multiset.sum_replicate, nsmul_eq_mul, mul_one, hcard]
    have h2 : (Multiset.map (fun ω => ω.re) (LinearMap.charpoly A).roots).sum =
        (Module.finrank ℂ V : ℝ) := by
      have h := (map_multiset_sum Complex.reAddGroupHom (LinearMap.charpoly A).roots).symm
      rw [hroots_sum] at h
      simpa using h
    rw [h1, h2, sub_self]
  -- hence every root is `1`
  have hall : ∀ ω ∈ (LinearMap.charpoly A).roots, ω = 1 := by
    have hnonneg' : ∀ x ∈ ((LinearMap.charpoly A).roots.map (fun ω => (1:ℝ) - ω.re)), 0 ≤ x := by
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨ω, hω, rfl⟩ := hx
      have := complex_re_le_one_of_pow_seven ω (hpow ω hω)
      linarith
    intro ω hω
    have hmem : (1:ℝ) - ω.re ∈ (LinearMap.charpoly A).roots.map (fun ω => (1:ℝ) - ω.re) :=
      Multiset.mem_map.mpr ⟨ω, hω, rfl⟩
    have hz := multiset_forall_eq_zero_of_sum_eq_zero_of_nonneg hnonneg' hsum _ hmem
    exact complex_eq_one_of_pow_seven_of_re ω (hpow ω hω) (by linarith)
  -- `A` is semisimple since its minimal polynomial divides the squarefree polynomial `X ^ 7 - 1`
  have hA_semi : A.IsSemisimple := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := Polynomial.X ^ 7 - Polynomial.C 1)
    · rw [← PerfectField.separable_iff_squarefree]
      exact Polynomial.separable_X_pow_sub_C 1 (by norm_num) (by norm_num)
    · simp [Polynomial.aeval_X, hA]
  have hsub_semi : (A - 1).IsSemisimple := by
    have h := hA_semi.aeval (Polynomial.X - Polynomial.C 1)
    simpa [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C] using h
  -- so it suffices to see that every eigenvalue of `A - 1` is `0`
  have hev0 : ∀ μ : ℂ, (A - 1).HasEigenvalue μ → μ = 0 := by
    intro μ hμ
    rw [Module.End.hasEigenvalue_iff] at hμ
    obtain ⟨v, hv, hvne⟩ := Submodule.ne_bot_iff _ |>.mp hμ
    rw [Module.End.mem_eigenspace_iff] at hv
    have hv' : A v - v = μ • v := by simpa [LinearMap.sub_apply, Module.End.one_apply] using hv
    have hAv : A v = (μ + 1) • v := by
      have h1 : A v = μ • v + v := by
        have := congrArg (fun w => w + v) hv'
        simpa using this
      rw [h1, add_smul, one_smul]
    have hevA : A.HasEigenvalue (μ + 1) := by
      rw [Module.End.hasEigenvalue_iff]
      exact Submodule.ne_bot_iff _ |>.mpr
        ⟨v, by rw [Module.End.mem_eigenspace_iff]; exact hAv, hvne⟩
    have hroot : (μ + 1) ∈ (LinearMap.charpoly A).roots :=
      (Polynomial.mem_roots hne).mpr
        ((Module.End.hasEigenvalue_iff_isRoot_charpoly A (μ + 1)).mp hevA)
    exact add_eq_right.mp (hall (μ + 1) hroot)
  have hzero : A - 1 = 0 :=
    (Module.End.IsSemisimple.eq_zero_iff_forall_eigenvalue hsub_semi).mpr hev0
  exact sub_eq_zero.mp hzero

/-! ## The requested leaf -/

theorem Y6TraceFinrank : Work.A7REC.A7Y6TraceFinrankProp := by
  intro G _ V _ _ _ ρ x hx htr
  have hx7 : x ^ 7 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  have hpow : (ρ x) ^ 7 = 1 := by
    rw [← map_pow, hx7, map_one]
  exact end_eq_one_of_pow_seven_eq_one (ρ x) hpow htr

end Work.A7REC.Char
