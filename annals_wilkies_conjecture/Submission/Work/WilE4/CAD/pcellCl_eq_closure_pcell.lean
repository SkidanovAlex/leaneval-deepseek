/-
  WilE4 / CAD — the closed sign-condition cell is the closure of the (strict) sign-condition cell.

  For a family `P : Fin k → ℝ[X]` that is closed under differentiation (`hderiv`) and a sign vector
  `v` that is realised by `pcell P v` (`hne`), the non-strict sign-condition set `pcellCl P v` is
  exactly the topological closure of `pcell P v`.

  The proof has three ingredients.

  * `pcellCl` is order-connected (convex), i.e. it is an interval; this is proved in
    `pcellCl_ordConnected` and is where the derivative-closure hypothesis is used.
  * If some index with `v i = 0` carries a *non-zero* polynomial, then `pcellCl ⊆ {x | P i x = 0}`
    together with convexity forces `pcellCl = pcell`: two distinct points of `pcellCl` spanning a
    non-degenerate interval would make `P i` vanish on infinitely many points.  Hence `pcellCl` is
    the closure of `pcell` (it is closed).
  * Otherwise every index with `v i = 0` carries the zero polynomial, and then membership in
    `pcell` is membership in `pcellCl` plus non-vanishing of the non-zero members; the non-vanishing
    is automatic on all but finitely many points of an interval, so again `pcellCl ⊆ closure pcell`.
-/
import Mathlib
import Submission.Work.WilE4.CAD.Fibre
import Submission.Work.WilE4.CAD.derivChain_interval

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilE4.CAD

open Polynomial

variable {k : ℕ}

/-! ## Elementary interval/root tools -/

/-- A non-degenerate interval contains a point which is not a root of any member of a finite family
of non-zero polynomials. -/
theorem exists_not_isRoot_of_Ioo {ι : Type*} [Fintype ι] (Q : ι → Polynomial ℝ)
    (hQ : ∀ i, Q i ≠ 0) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Set.Ioo a b, ∀ i, ¬ (Q i).IsRoot x := by
  by_contra h
  push Not at h
  have hsub : Set.Ioo a b ⊆ ⋃ i, {x : ℝ | (Q i).IsRoot x} := by
    intro x hx
    obtain ⟨i, hi⟩ := h x hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hfin : (⋃ i, {x : ℝ | (Q i).IsRoot x}).Finite :=
    Set.finite_iUnion fun i => finite_setOfPred_isRoot (hQ i)
  exact (Set.Ioo_infinite hab).not_finite (hfin.subset hsub)

/-! ## Membership in `pcell` when every zero condition is carried by the zero polynomial -/

/-- If every index with `v i = 0` carries the zero polynomial, then `x ∈ pcell P v` is the same as
`x ∈ pcellCl P v` together with non-vanishing of all the members with `v i ≠ 0`. -/
theorem mem_pcell_iff_mem_pcellCl_and_ne {P : Fin k → Polynomial ℝ} {v : Fin k → SignType}
    (hzero' : ∀ i, v i = 0 → P i = 0) {x : ℝ} :
    x ∈ pcell P v ↔ x ∈ pcellCl P v ∧ ∀ i, v i ≠ 0 → (P i).eval x ≠ 0 := by
  constructor
  · intro hx
    refine ⟨pcell_subset_pcellCl P v hx, fun i hi he => ?_⟩
    have h1 : SignType.sign ((P i).eval x) = v i := hx i
    rw [he, sign_zero] at h1
    exact hi h1.symm
  · rintro ⟨hcl, hnv⟩ i
    have hcl' := hcl i
    rcases SignType.trichotomy (v i) with h | h | h
    · have hle : (P i).eval x ≤ 0 := hcl'.2.1 h
      have hne : (P i).eval x ≠ 0 := hnv i (by rw [h]; decide)
      rw [h]
      exact sign_neg (lt_of_le_of_ne hle hne)
    · have h0 : (P i).eval x = 0 := hcl'.2.2 h
      rw [h, h0, sign_zero]
    · have hle : 0 ≤ (P i).eval x := hcl'.1 h
      have hne : (P i).eval x ≠ 0 := hnv i (by rw [h]; decide)
      rw [h]
      exact sign_pos (lt_of_le_of_ne hle (Ne.symm hne))

/-! ## Case A: some `v i = 0` is carried by a non-zero polynomial -/

/-- If some index with `v i = 0` carries a non-zero polynomial, then every point of the closed cell
is already a point of the strict cell. -/
theorem pcellCl_subset_pcell_of_exists_zero {P : Fin k → Polynomial ℝ} {v : Fin k → SignType}
    (hconv : Set.OrdConnected (pcellCl P v)) (hne : (pcell P v).Nonempty)
    {i₀ : Fin k} (hv : v i₀ = 0) (hP : P i₀ ≠ 0) : pcellCl P v ⊆ pcell P v := by
  intro t ht
  obtain ⟨u, hu⟩ := hne
  have hu' : u ∈ pcellCl P v := pcell_subset_pcellCl P v hu
  rcases lt_trichotomy u t with h | h | h
  · exfalso
    have hroot : ∀ x ∈ Set.Icc u t, (P i₀).eval x = 0 := fun x hx =>
      ((hconv.out hu' ht) hx i₀).2.2 hv
    have hinf : Set.Infinite {x : ℝ | (P i₀).IsRoot x} :=
      (Set.Icc_infinite h).mono fun x hx => Polynomial.IsRoot.def.mpr (hroot x hx)
    exact hP (Polynomial.eq_zero_of_infinite_isRoot _ hinf)
  · rwa [← h]
  · exfalso
    have hroot : ∀ x ∈ Set.Icc t u, (P i₀).eval x = 0 := fun x hx =>
      ((hconv.out ht hu') hx i₀).2.2 hv
    have hinf : Set.Infinite {x : ℝ | (P i₀).IsRoot x} :=
      (Set.Icc_infinite h).mono fun x hx => Polynomial.IsRoot.def.mpr (hroot x hx)
    exact hP (Polynomial.eq_zero_of_infinite_isRoot _ hinf)

/-! ## Case B: every zero condition is carried by the zero polynomial -/

/-- If every index with `v i = 0` carries the zero polynomial, then the closed cell is contained in
the closure of the strict cell: off the finitely many points where a member with `v i ≠ 0` vanishes,
the closed conditions are already strict. -/
theorem pcellCl_subset_closure_pcell_of_forall_zero {P : Fin k → Polynomial ℝ}
    {v : Fin k → SignType} (hzero' : ∀ i, v i = 0 → P i = 0)
    (hconv : Set.OrdConnected (pcellCl P v)) (hne : (pcell P v).Nonempty) :
    pcellCl P v ⊆ closure (pcell P v) := by
  have hnonzero : ∀ i : {i : Fin k // v i ≠ 0}, P (i : Fin k) ≠ 0 := by
    rintro ⟨i, hi⟩ h0
    obtain ⟨u, hu⟩ := hne
    have h1 : SignType.sign ((P i).eval u) = v i := hu i
    have h2 : (P i).eval u = 0 := by rw [h0]; simp
    rw [h2, sign_zero] at h1
    exact hi h1.symm
  intro t ht
  obtain ⟨u, hu⟩ := hne
  have hu' : u ∈ pcellCl P v := pcell_subset_pcellCl P v hu
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases lt_trichotomy u t with h | h | h
  · obtain ⟨x, hxI, hxnr⟩ := exists_not_isRoot_of_Ioo (fun i : {i : Fin k // v i ≠ 0} => P i.1)
      hnonzero (max_lt h (by linarith : t - ε < t))
    refine ⟨x, ?_, ?_⟩
    · rw [mem_pcell_iff_mem_pcellCl_and_ne hzero']
      exact ⟨(hconv.out hu' ht) ⟨le_trans (le_max_left _ _) hxI.1.le, hxI.2.le⟩,
        fun i hi h0 => hxnr ⟨i, hi⟩ (Polynomial.IsRoot.def.mpr h0)⟩
    · have h1 : t - ε < x := lt_of_le_of_lt (le_max_right u (t - ε)) hxI.1
      have h2 : x < t + ε := by linarith [hxI.2]
      rw [Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · refine ⟨u, hu, ?_⟩
    rw [← h, dist_self]
    exact hε
  · obtain ⟨x, hxI, hxnr⟩ := exists_not_isRoot_of_Ioo (fun i : {i : Fin k // v i ≠ 0} => P i.1)
      hnonzero (lt_min h (by linarith : t < t + ε))
    refine ⟨x, ?_, ?_⟩
    · rw [mem_pcell_iff_mem_pcellCl_and_ne hzero']
      exact ⟨(hconv.out ht hu') ⟨hxI.1.le, le_trans hxI.2.le (min_le_left u (t + ε))⟩,
        fun i hi h0 => hxnr ⟨i, hi⟩ (Polynomial.IsRoot.def.mpr h0)⟩
    · have h1 : t - ε < x := by linarith [hxI.1]
      have h2 : x < t + ε := lt_of_lt_of_le hxI.2 (min_le_right u (t + ε))
      rw [Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-! ## Convexity of the closed cell

The closed cell of a derivative-closed family is an interval.  The proof runs the chain lemma
`derivChain_interval` on the derivative chain `P i, (P i)', (P i)'', …`: at both endpoints `a`, `b`
of the segment under consideration all the non-strict sign conditions hold, so they hold throughout
the segment. -/

/-- Iterated derivatives of a family member are again members of the family, unless they vanish. -/
private theorem iterate_derivative_zero_or_mem {P : Fin k → Polynomial ℝ}
    (hderiv : ∀ i, (P i).derivative = 0 ∨ ∃ j, P j = (P i).derivative) (i : Fin k) :
    ∀ s : ℕ, (Polynomial.derivative^[s]) (P i) = 0 ∨
      ∃ j : Fin k, P j = (Polynomial.derivative^[s]) (P i) := by
  intro s
  induction s with
  | zero => exact Or.inr ⟨i, by simp⟩
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | ⟨j, hj⟩
    · exact Or.inl (by rw [h, Polynomial.derivative_zero])
    · rcases hderiv j with h0 | ⟨j', hj'⟩
      · exact Or.inl (by rw [← hj, h0])
      · exact Or.inr ⟨j', by rw [← hj, hj']⟩

/-- The sign attributed to the `s`-th iterated derivative of `P i` along its derivative chain. -/
private noncomputable def chainSign (P : Fin k → Polynomial ℝ) (v : Fin k → SignType)
    (i : Fin k) : ℕ → SignType
  | 0 => v i
  | (s + 1) =>
      if h : ∃ j : Fin k, P j = (Polynomial.derivative^[s + 1]) (P i) then
        v (Classical.choose h) else 0

/-- The signs `chainSign` attributes are consistent with the closed cell. -/
private theorem chainSign_wcond {P : Fin k → Polynomial ℝ} {v : Fin k → SignType}
    (hderiv : ∀ i, (P i).derivative = 0 ∨ ∃ j, P j = (P i).derivative) (i : Fin k)
    {t : ℝ} (ht : t ∈ pcellCl P v) (s : ℕ) :
    (chainSign P v i s = 1 → 0 ≤ ((Polynomial.derivative^[s]) (P i)).eval t) ∧
      (chainSign P v i s = -1 → ((Polynomial.derivative^[s]) (P i)).eval t ≤ 0) ∧
      (chainSign P v i s = 0 → ((Polynomial.derivative^[s]) (P i)).eval t = 0) := by
  match s with
  | 0 =>
    have h0 : chainSign P v i 0 = v i := rfl
    have h1 : (Polynomial.derivative^[0]) (P i) = P i := by simp
    rw [h0, h1]
    exact ht i
  | (s + 1) =>
    by_cases h : ∃ j : Fin k, P j = (Polynomial.derivative^[s + 1]) (P i)
    · have hw : chainSign P v i (s + 1) = v (Classical.choose h) := by
        simp only [chainSign, dif_pos h]
      have hgen : ∀ j : Fin k, P j = (Polynomial.derivative^[s + 1]) (P i) →
          (v j = 1 → 0 ≤ ((Polynomial.derivative^[s + 1]) (P i)).eval t) ∧
            (v j = -1 → ((Polynomial.derivative^[s + 1]) (P i)).eval t ≤ 0) ∧
            (v j = 0 → ((Polynomial.derivative^[s + 1]) (P i)).eval t = 0) := by
        intro j hj
        have h1 := ht j
        rw [hj] at h1
        exact h1
      rw [hw]
      exact hgen (Classical.choose h) (Classical.choose_spec h)
    · have hw : chainSign P v i (s + 1) = 0 := by
        simp only [chainSign, dif_neg h]
      have hf : (Polynomial.derivative^[s + 1]) (P i) = 0 := by
        rcases iterate_derivative_zero_or_mem hderiv i (s + 1) with h0 | ⟨j, hj⟩
        · exact h0
        · exact absurd ⟨j, hj⟩ h
      rw [hw, hf]
      simp

/-- The closed sign-condition cell of a derivative-closed family is order-connected. -/
private theorem pcellCl_ordConnected' {P : Fin k → Polynomial ℝ} (v : Fin k → SignType)
    (hderiv : ∀ i, (P i).derivative = 0 ∨ ∃ j, P j = (P i).derivative) :
    Set.OrdConnected (pcellCl P v) := by
  rw [Set.ordConnected_iff]
  intro a ha b hb hab x hx i
  have hstep : ∀ s ≤ (P i).natDegree,
      Polynomial.derivative ((Polynomial.derivative^[s]) (P i)) =
        (Polynomial.derivative^[s + 1]) (P i) := fun s _ => by
    rw [Function.iterate_succ_apply']
  have hlast : Polynomial.derivative ((Polynomial.derivative^[(P i).natDegree]) (P i)) = 0 := by
    have h := Polynomial.iterate_derivative_eq_zero (p := P i) (x := (P i).natDegree + 1)
      (Nat.lt_succ_self _)
    simpa [Function.iterate_succ_apply'] using h
  have hres := derivChain_interval ((P i).natDegree) (fun s => (Polynomial.derivative^[s]) (P i))
    (chainSign P v i) hab hstep hlast
    (fun s _ => chainSign_wcond hderiv i ha s)
    (fun s _ => chainSign_wcond hderiv i hb s)
  have h0 := hres x hx 0 (Nat.zero_le _)
  simpa [chainSign, Function.iterate_zero_apply] using h0

/-! ## Assembly -/

/-- The closed cell is the union of the closure of the strict cell and itself; with convexity of
`pcellCl` and a realised sign vector this yields the equality. -/
theorem pcellCl_eq_closure_pcell_of_ordConnected {P : Fin k → Polynomial ℝ} {v : Fin k → SignType}
    (hconv : Set.OrdConnected (pcellCl P v)) (hne : (pcell P v).Nonempty) :
    pcellCl P v = closure (pcell P v) := by
  have hclosed : IsClosed (pcellCl P v) := pcellCl_isClosed P v
  have hsub : pcell P v ⊆ pcellCl P v := pcell_subset_pcellCl P v
  by_cases hA : ∃ i : Fin k, v i = 0 ∧ P i ≠ 0
  · obtain ⟨i, hv, hP⟩ := hA
    have heq : pcellCl P v = pcell P v :=
      Set.Subset.antisymm (pcellCl_subset_pcell_of_exists_zero hconv hne hv hP) hsub
    rw [heq]
    exact (show closure (pcell P v) = pcell P v from by rw [← heq]; exact hclosed.closure_eq).symm
  · push Not at hA
    refine Set.Subset.antisymm (pcellCl_subset_closure_pcell_of_forall_zero hA hconv hne) (by
      calc closure (pcell P v) ⊆ closure (pcellCl P v) := closure_mono hsub
        _ = pcellCl P v := hclosed.closure_eq)

theorem pcellCl_eq_closure_pcell {k : ℕ} (P : Fin k → Polynomial ℝ) (v : Fin k → SignType)
    (hzero : ∀ i, P i = 0 → v i = 0)
    (hderiv : ∀ i, (P i).derivative = 0 ∨ ∃ j, P j = (P i).derivative)
    (hne : (pcell P v).Nonempty) :
    pcellCl P v = closure (pcell P v) :=
  pcellCl_eq_closure_pcell_of_ordConnected (pcellCl_ordConnected' v hderiv) hne

end Work.WilE4.CAD
