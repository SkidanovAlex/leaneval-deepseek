import Mathlib

set_option linter.unusedVariables false

namespace Work.BourgainPlan.Maximal

/-- For a polynomial `q` with nonzero derivative, every real number `x` has a symmetric closed
neighbourhood `[x - r, x + r]` on which `x` is the only possible zero of `q'`.

This is the "isolated zeros of `q'`" fact needed to build the half-open cover of a compact
interval: since `{y | q'.eval y = 0}` is finite (`Polynomial.finite_setOfPred_isRoot`) it is a
closed set, so `{y | q'.eval y = 0} \ {x}` is closed as well and its complement is an open
neighbourhood of `x`. -/
lemma exists_radius_deriv_ne (q : Polynomial ℝ) (hq : q.derivative ≠ 0) (x : ℝ) :
    ∃ r > 0, ∀ y ∈ Set.Icc (x - r) (x + r), q.derivative.eval y = 0 → y = x := by
  have hZ : ({y : ℝ | q.derivative.eval y = 0}).Finite := by
    simpa only [Polynomial.IsRoot] using
      Polynomial.finite_setOfPred_isRoot (p := q.derivative) hq
  have hcl : IsClosed ({y : ℝ | q.derivative.eval y = 0} \ {x}) := hZ.sdiff.isClosed
  have hopen : IsOpen ({y : ℝ | q.derivative.eval y = 0} \ {x})ᶜ := hcl.isOpen_compl
  have hx : x ∈ ({y : ℝ | q.derivative.eval y = 0} \ {x})ᶜ := by simp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hx
  refine ⟨ε / 2, by linarith, ?_⟩
  intro y hy hy0
  have hb : y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hmem := hball hb
  by_contra hne
  exact hmem (by
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨hy0, hne⟩)

/-- A compact interval can be covered by finitely many intervals on each of which the derivative of `q` is either nonvanishing on the half-open interval `(a,b]` or nonvanishing on `[a,b)`.  HINT: the zero set of `q'` is finite (`Polynomial.finite_setOfPred_isRoot`), so every point has a punctured neighbourhood free of zeros of `q'`; cover `[0,U']` by such symmetric open intervals and extract a finite subcover (e.g. `IsCompact.elim_finite_subcover`), then use the two halves of each cover element as the pieces. -/
theorem exists_cover_deriv_ne (q : Polynomial ℝ) (hq : q.derivative ≠ 0) {U' : ℝ}
    (hU' : 0 ≤ U') :
    ∃ (n : ℕ) (a b : Fin n → ℝ),
      (∀ i, a i < b i) ∧
      (∀ i, (∀ u ∈ Set.Ioc (a i) (b i), q.derivative.eval u ≠ 0) ∨
            (∀ u ∈ Set.Ico (a i) (b i), q.derivative.eval u ≠ 0)) ∧
      Set.Icc 0 U' ⊆ ⋃ i, Set.Icc (a i) (b i) := by
  classical
  -- around every point the derivative has at most that point as a zero
  choose r hrpos hrZ using exists_radius_deriv_ne q hq
  -- the associated symmetric open intervals cover `[0,U']`
  have hcover : Set.Icc 0 U' ⊆ ⋃ x : ↥(Set.Icc 0 U'), Set.Ioo (↑x - r ↑x) (↑x + r ↑x) := by
    intro y hy
    refine Set.mem_iUnion.mpr ⟨⟨y, hy⟩, ?_⟩
    simp only [Set.mem_Ioo]
    exact ⟨by linarith [hrpos y], by linarith [hrpos y]⟩
  obtain ⟨t, htcov⟩ := (isCompact_Icc).elim_finite_subcover
      (fun x : ↥(Set.Icc 0 U') => Set.Ioo (↑x - r ↑x) (↑x + r ↑x))
      (fun x => isOpen_Ioo) hcover
  have htcov' : ∀ y ∈ Set.Icc 0 U',
      ∃ i : ↥(Set.Icc 0 U'), i ∈ t ∧ y ∈ Set.Ioo (↑i - r ↑i) (↑i + r ↑i) := by
    intro y hy
    have h := htcov hy
    simpa only [Set.mem_iUnion, exists_prop] using h
  -- the finite family of pieces: `Sum.inl i` is the left half `[x - r x, x]` of the `i`-th
  -- member of the subcover, `Sum.inr i` is its right half `[x, x + r x]`
  let e : (↥t ⊕ ↥t) ≃ Fin (Fintype.card (↥t ⊕ ↥t)) := Fintype.equivFin _
  let aa : ↥t ⊕ ↥t → ℝ := fun p => match p with
    | Sum.inl i => (i.1.1 : ℝ) - r (i.1.1)
    | Sum.inr i => (i.1.1 : ℝ)
  let bb : ↥t ⊕ ↥t → ℝ := fun p => match p with
    | Sum.inl i => (i.1.1 : ℝ)
    | Sum.inr i => (i.1.1 : ℝ) + r (i.1.1)
  refine ⟨Fintype.card (↥t ⊕ ↥t), fun j => aa (e.symm j), fun j => bb (e.symm j), ?_, ?_, ?_⟩
  · -- the pieces are nondegenerate
    intro j
    dsimp only
    rcases hh : e.symm j with i | i <;> simp only [aa, bb] <;> linarith [hrpos (i.1.1)]
  · -- on each piece the derivative is nonvanishing on the appropriate half-open interval
    intro j
    dsimp only
    rcases hh : e.symm j with i | i
    · -- left half `[x - r x, x]`: nonvanishing on `[x - r x, x)`
      right
      simp only [aa, bb]
      intro u hu
      have huI : u ∈ Set.Icc ((i.1.1 : ℝ) - r (i.1.1)) ((i.1.1 : ℝ) + r (i.1.1)) :=
        ⟨hu.1, by linarith [hu.2, hrpos (i.1.1)]⟩
      have hne : u ≠ (i.1.1 : ℝ) := by linarith [hu.2]
      exact fun h0 => hne (hrZ (i.1.1) u huI h0)
    · -- right half `[x, x + r x]`: nonvanishing on `(x, x + r x]`
      left
      simp only [aa, bb]
      intro u hu
      have huI : u ∈ Set.Icc ((i.1.1 : ℝ) - r (i.1.1)) ((i.1.1 : ℝ) + r (i.1.1)) :=
        ⟨by linarith [hu.1, hrpos (i.1.1)], hu.2⟩
      have hne : u ≠ (i.1.1 : ℝ) := by linarith [hu.1]
      exact fun h0 => hne (hrZ (i.1.1) u huI h0)
  · -- the pieces cover `[0,U']`
    intro y hy
    obtain ⟨i, hi, hyI⟩ := htcov' y hy
    by_cases hcase : y ≤ (i : ℝ)
    · -- `y` lies in the left half of the member `i` of the subcover
      refine Set.mem_iUnion.mpr ⟨e (Sum.inl ⟨i, hi⟩), ?_⟩
      simp only [Equiv.symm_apply_apply, aa, bb]
      exact ⟨le_of_lt hyI.1, hcase⟩
    · -- `y` lies in the right half of the member `i` of the subcover
      simp only [not_le] at hcase
      refine Set.mem_iUnion.mpr ⟨e (Sum.inr ⟨i, hi⟩), ?_⟩
      simp only [Equiv.symm_apply_apply, aa, bb]
      exact ⟨le_of_lt hcase, le_of_lt hyI.2⟩

end Work.BourgainPlan.Maximal
