import Mathlib

/-!
# `Work.DSG4b.le_span_of_forall_corrections`

The "limit step" used in the Rees/Nakayama argument for the direct summand theorem:

If `A` is `I`-adically complete, `g : ι → A` is a finite family and `d : ι → ℕ` are exponents such
that every `x ∈ J ⊓ I ^ n` can be corrected to lie in `J ⊓ I ^ (n+1)` by subtracting a combination
`∑ j, a j * g j` with `a j ∈ I ^ (n - d j)`, then `J ≤ span (range g)`.

The proof iterates the correction step, producing remainders `x_N ∈ J ⊓ I ^ N`.  The coefficient
`a^(k)_j` chosen at stage `k` lies in `I ^ (k - d j)`, so the partial sums `∑_{k<N} a^(k)_j`
converge `I`-adically (after shifting the index by `d j` they form a Cauchy sequence in the sense of
`IsPrecomplete.prec'`).  Their limits `b_j` satisfy `x = ∑ j, b_j * g j` by separatedness
(`IsHausdorff`).
-/

namespace Work.DSG4b

/-- The iteration of the correction step: there is a sequence of coefficient vectors `a k` with
`a k j ∈ I ^ (k - d j)` whose partial sums correct `x` down to `J ⊓ I ^ N`. -/
private lemma approx_seq_aux {A : Type*} [CommRing A] {I J : Ideal A}
    {ι : Type*} [Fintype ι] (g : ι → A) (d : ι → ℕ)
    (hstep : ∀ n (x : A), x ∈ J ⊓ I ^ n →
      ∃ a : ι → A, (∀ j, a j ∈ I ^ (n - d j)) ∧ x - ∑ j, a j * g j ∈ J ⊓ I ^ (n + 1))
    (x : A) (hx : x ∈ J) :
    ∃ a : ℕ → ι → A, (∀ n j, a n j ∈ I ^ (n - d j)) ∧
      ∀ N, x - ∑ j, (∑ k ∈ Finset.range N, a k j) * g j ∈ J ⊓ I ^ N := by
  classical
  let coef : ℕ → A → ι → A := fun n y =>
    if h : y ∈ J ⊓ I ^ n then Classical.choose (hstep n y h) else 0
  let yS : ℕ → A := Nat.rec x (fun n ih => ih - ∑ j, coef n ih j * g j)
  have hyS : ∀ n, yS n ∈ J ⊓ I ^ n := by
    intro n
    induction n with
    | zero => simpa [yS] using hx
    | succ n ih =>
        have hc : coef n (yS n) = Classical.choose (hstep n (yS n) ih) := by
          simp only [coef, dite_eq_left ih]
        have hstep' : yS n - ∑ j, coef n (yS n) j * g j ∈ J ⊓ I ^ (n + 1) := by
          rw [hc]
          exact (Classical.choose_spec (hstep n (yS n) ih)).2
        simpa [yS] using hstep'
  let a : ℕ → ι → A := fun n => coef n (yS n)
  have ha : ∀ n j, a n j ∈ I ^ (n - d j) := by
    intro n j
    have hc : a n = Classical.choose (hstep n (yS n) (hyS n)) := by
      simp only [a, coef, dite_eq_left (hyS n)]
    rw [hc]
    exact (Classical.choose_spec (hstep n (yS n) (hyS n))).1 j
  have happrox : ∀ N, x - ∑ j, (∑ k ∈ Finset.range N, a k j) * g j ∈ J ⊓ I ^ N := by
    intro N
    have heq : x - ∑ j, (∑ k ∈ Finset.range N, a k j) * g j = yS N := by
      induction N with
      | zero => simp [yS]
      | succ N ih =>
          have h1 : (∑ j, (∑ k ∈ Finset.range (N + 1), a k j) * g j)
              = (∑ j, (∑ k ∈ Finset.range N, a k j) * g j) + ∑ j, a N j * g j := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_range_succ, add_mul]
          have h2 : yS (N + 1) = yS N - ∑ j, a N j * g j := by
            simp only [yS, a]
          rw [h1, h2, ← ih]
          ring
    rw [heq]
    exact hyS N
  exact ⟨a, ha, happrox⟩

/-- Construction of the limits of the partial sums: if `a k j ∈ I ^ (k - d j)`, then the partial
sums of the family `a · j` converge in the `I`-adic topology. -/
private lemma limit_aux {A : Type*} [CommRing A] {I : Ideal A}
    (hI : IsAdicComplete I A) {ι : Type*} (d : ι → ℕ) (a : ℕ → ι → A)
    (ha : ∀ n j, a n j ∈ I ^ (n - d j)) :
    ∃ b : ι → A, ∀ j N, (∑ k ∈ Finset.range N, a k j) - b j ∈ I ^ (N - d j) := by
  classical
  haveI : IsPrecomplete I A := hI.toIsPrecomplete
  have hsmul : ∀ m : ℕ, I ^ m • (⊤ : Submodule A A) = (I ^ m : Ideal A) := fun m => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have hlim : ∀ j : ι, ∃ b : A, ∀ N, (∑ k ∈ Finset.range (N + d j), a k j) - b ∈ I ^ N := by
    intro j
    have hcauchy : ∀ {m n : ℕ}, m ≤ n →
        (∑ k ∈ Finset.range (m + d j), a k j) ≡ (∑ k ∈ Finset.range (n + d j), a k j)
          [SMOD I ^ m • (⊤ : Submodule A A)] := by
      intro m n hmn
      apply SModEq.symm
      rw [SModEq.sub_mem, hsmul m]
      rw [← Finset.sum_Ico_eq_sub (fun k => a k j) (Nat.add_le_add_right hmn (d j))]
      apply Ideal.sum_mem
      intro k hk
      rw [Finset.mem_Ico] at hk
      exact Ideal.pow_le_pow_right (Nat.le_sub_of_add_le hk.1) (ha k j)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (M := A)
      (fun N => ∑ k ∈ Finset.range (N + d j), a k j) hcauchy
    refine ⟨L, fun N => ?_⟩
    have := hL N
    rwa [SModEq.sub_mem, hsmul N] at this
  choose b hb using hlim
  refine ⟨b, fun j N => ?_⟩
  by_cases h : d j ≤ N
  · have := hb j (N - d j)
    rwa [Nat.sub_add_cancel h] at this
  · have h0 : N - d j = 0 := Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp h))
    simp [h0]

theorem le_span_of_forall_corrections {A : Type*} [CommRing A] {I J : Ideal A}
    (hI : IsAdicComplete I A) {ι : Type*} [Fintype ι] (g : ι → A) (d : ι → ℕ)
    (hgJ : ∀ j, g j ∈ J)
    (hstep : ∀ n (x : A), x ∈ J ⊓ I ^ n →
      ∃ a : ι → A, (∀ j, a j ∈ I ^ (n - d j)) ∧ x - ∑ j, a j * g j ∈ J ⊓ I ^ (n + 1)) :
    J ≤ Ideal.span (Set.range g) := by
  intro x hx
  classical
  haveI : IsHausdorff I A := hI.toIsHausdorff
  obtain ⟨a, ha, happrox⟩ := approx_seq_aux g d hstep x hx
  obtain ⟨b, hb⟩ := limit_aux hI d a ha
  have hsmul : ∀ m : ℕ, I ^ m • (⊤ : Submodule A A) = (I ^ m : Ideal A) := fun m => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have hx_eq : x = ∑ j, b j * g j := by
    have hzero : x - ∑ j, b j * g j = 0 := by
      refine IsHausdorff.haus' (I := I) (x - ∑ j, b j * g j) ?_
      intro m
      rw [SModEq.zero, hsmul m]
      let D : ℕ := ∑ i : ι, d i
      have hNm : m ≤ m + D := Nat.le_add_right m D
      have h1 : x - ∑ j, (∑ k ∈ Finset.range (m + D), a k j) * g j ∈ I ^ m :=
        Ideal.pow_le_pow_right hNm (happrox (m + D)).2
      have h2 : ∑ j, ((∑ k ∈ Finset.range (m + D), a k j) - b j) * g j ∈ I ^ m := by
        apply Ideal.sum_mem
        intro j _
        refine Ideal.mul_mem_right (g j) (I ^ m) ?_
        have hdj : d j ≤ D :=
          Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
        have hmj : m ≤ (m + D) - d j :=
          Nat.le_sub_of_add_le (Nat.add_le_add_left hdj m)
        exact Ideal.pow_le_pow_right hmj (hb j (m + D))
      have h3 : x - ∑ j, b j * g j
          = (x - ∑ j, (∑ k ∈ Finset.range (m + D), a k j) * g j)
            + ∑ j, ((∑ k ∈ Finset.range (m + D), a k j) - b j) * g j := by
        have hsum : ∑ j, ((∑ k ∈ Finset.range (m + D), a k j) - b j) * g j
            = (∑ j, (∑ k ∈ Finset.range (m + D), a k j) * g j) - ∑ j, b j * g j := by
          simp_rw [sub_mul]
          rw [Finset.sum_sub_distrib]
        rw [hsum]
        ring
      rw [h3]
      exact add_mem h1 h2
    exact sub_eq_zero.mp hzero
  rw [hx_eq]
  exact Ideal.sum_mem _ (fun j _ =>
    Ideal.mul_mem_left _ (b j) (Ideal.subset_span (Set.mem_range_self j)))

end Work.DSG4b
