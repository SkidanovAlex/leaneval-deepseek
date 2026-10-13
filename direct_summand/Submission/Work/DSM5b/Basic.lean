import Submission.Work.DSMap.Mix2

/-!
# DSM5b — the characteristic-`p` perfected-blowup almost-acyclicity area (M5b)

This directory builds the mathematics of the frozen node

`DSMap.Mix2.area_M5b`  (`Submission/Work/DSMap/Mix2.lean`, read-only)

> `R` perfect of characteristic `p`, `t : ι → R` finite, `T ∈ R`, `j₀`, `e` with `t j₀ = T ^ e`:
> the coaugmented Čech complex `R → Č(perfected charts of Bl_{(t)} R)` is `(T^{1/p^k})`-almost
> acyclic.

The route formalised here (see `Submission/Work/DSM5b/DESIGN.md`) is

1. **localisation/descent**: for each `k`, after inverting `ϖ_k = T^{1/p^k}` the perfected chart
   Čech complex becomes the Amitsur complex of the cover `{D(t_i)}` of `Spec R[1/ϖ_k]` (the `t_i`
   generate the unit ideal there because `t_{j₀} = T^e`), hence is exact in positive degrees with
   `H⁰ = R[1/ϖ_k]`.  This yields *power* killing: every cycle becomes a boundary after multiplying
   by a power of `ϖ_k`.
2. **Frobenius upgrade**: the perfected chart rings are perfect and the `p`-th power map is an
   automorphism of the whole complex, commuting with the differentials and semilinear over `R`.
   Killing by a *power* of `ϖ_k` upgrades to killing by `ϖ_k` itself
   (`pow_kill_to_root_kill`).

This file collects the vocabulary: the root tower `ϖ_k` of `T` (in the general form used by the
upgrade argument), the perfected chart rings (`perfChartRing`) and their elementary properties.
-/

universe a b c

namespace Work.DSM5b

open CategoryTheory

open DSMap DSMap.Mix DSMap.Mix2

section RootTower

/-- A compatible system of `p`-power roots of `T`: `ϖ 0 = T` and `(ϖ (k+1)) ^ p = ϖ k`.  All the
tower combinatorics used by the M5b argument is stated for such a system; the frozen family
`k ↦ (frobeniusEquiv R p).symm^[k] T` is one (`IsRootTower.frozen`). -/
structure IsRootTower (p : ℕ) (R : Type a) [CommRing R] (T : R) (ϖ : ℕ → R) : Prop where
  zero : ϖ 0 = T
  pow_succ : ∀ k, (ϖ (k + 1)) ^ p = ϖ k

variable {p : ℕ} {R : Type a} [CommRing R] {T : R} {ϖ : ℕ → R}

/-- The frozen `ϖ`-family `k ↦ T ^ (1/p^k)` is a root tower. -/
theorem IsRootTower.frozen (p : ℕ) (R : Type a) [CommRing R] [ExpChar R p] [PerfectRing R p]
    (T : R) : IsRootTower p R T (fun k => (frobeniusEquiv R p).symm^[k] T) where
  zero := rfl
  pow_succ k := by
    rw [Function.iterate_succ_apply']
    exact frobenius_apply_frobeniusEquiv_symm R p _

/-- The `j`-th iterated power of the `(k+j)`-th root is the `k`-th root. -/
theorem IsRootTower.pow_pow (h : IsRootTower p R T ϖ) (k j : ℕ) :
    (ϖ (k + j)) ^ (p ^ j) = ϖ k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ, pow_succ', pow_mul, h.pow_succ (k + j)]
    exact ih

/-- Powers: `ϖ k ^ (p^j) = ϖ (k-j)` for `j ≤ k`. -/
theorem IsRootTower.pow_eq (h : IsRootTower p R T ϖ) {k j : ℕ} (hk : j ≤ k) :
    (ϖ k) ^ (p ^ j) = ϖ (k - j) := by
  conv_lhs => rw [← Nat.sub_add_cancel hk]
  exact h.pow_pow (k - j) j

end RootTower

section FrobeniusTower

variable {p : ℕ} (R : Type a) [CommRing R] [ExpChar R p] [PerfectRing R p]
  {T : R} {ϖ : ℕ → R}

/-- `S^j` of the `(k+j)`-th root is the `k`-th root: `(ϖ_{k+j})^{p^j} = ϖ_k`. -/
theorem IsRootTower.pow_pow_iterate (h : IsRootTower p R T ϖ) (k j : ℕ) :
    _root_.iterateFrobeniusEquiv R p j (ϖ (k + j)) = ϖ k := by
  rw [_root_.iterateFrobeniusEquiv_def]
  exact h.pow_pow k j

/-- The `p`-th power map on the root tower: `(ϖ_{k+1})^p = ϖ_k`. -/
theorem IsRootTower.pow_iterate_frob (h : IsRootTower p R T ϖ) (k : ℕ) :
    _root_.frobeniusEquiv R p (ϖ (k + 1)) = ϖ k := by
  rw [_root_.frobeniusEquiv_def]
  exact h.pow_succ k

/-- The `(k+1)`-th root is the `p`-th root of the `k`-th root. -/
theorem IsRootTower.root_succ (h : IsRootTower p R T ϖ) (k : ℕ) :
    (_root_.frobeniusEquiv R p).symm (ϖ k) = ϖ (k + 1) :=
  (_root_.frobeniusEquiv R p).injective
    (by rw [RingEquiv.apply_symm_apply, h.pow_iterate_frob])

end FrobeniusTower

section PerfChartGens

variable (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p] {ι : Type a}
  [DecidableEq ι] (t : ι → R) (S : Finset ι)

/-- The set of generators of the perfected chart: the elements all of whose sufficiently high
`p`-power lies in the honest chart ring `R[J/t_S]`. -/
def perfChartGens : Set (Localization.Away (tS t S)) :=
  {x | ∃ e : ℕ, x ^ (p ^ e) ∈ chartRing t S}

lemma perfChartRing_eq_adjoin :
    perfChartRing p t S = Algebra.adjoin R (perfChartGens p t S) := rfl

lemma perfChartGens_mono {e e' : ℕ} (h : e ≤ e') {x : Localization.Away (tS t S)}
    (hx : x ^ (p ^ e) ∈ chartRing t S) : x ^ (p ^ e') ∈ chartRing t S := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, pow_mul]
  exact Subalgebra.pow_mem _ hx _

lemma chartRing_le_perfChartRing : chartRing t S ≤ perfChartRing p t S := by
  intro x hx
  exact Algebra.subset_adjoin ⟨0, by simpa using hx⟩

lemma perfChartGens_add [CharP (Localization.Away (tS t S)) p]
    {x y : Localization.Away (tS t S)}
    {e₁ e₂ : ℕ} (hx : x ^ (p ^ e₁) ∈ chartRing t S)
    (hy : y ^ (p ^ e₂) ∈ chartRing t S) :
    (x + y) ^ (p ^ max e₁ e₂) ∈ chartRing t S := by
  rw [add_pow_char_pow]
  exact Subalgebra.add_mem _
    (perfChartGens_mono p t S (le_max_left e₁ e₂) hx)
    (perfChartGens_mono p t S (le_max_right e₁ e₂) hy)

lemma perfChartGens_mul {x y : Localization.Away (tS t S)}
    {e₁ e₂ : ℕ} (hx : x ^ (p ^ e₁) ∈ chartRing t S)
    (hy : y ^ (p ^ e₂) ∈ chartRing t S) :
    (x * y) ^ (p ^ max e₁ e₂) ∈ chartRing t S := by
  rw [mul_pow]
  exact Subalgebra.mul_mem _
    (perfChartGens_mono p t S (le_max_left e₁ e₂) hx)
    (perfChartGens_mono p t S (le_max_right e₁ e₂) hy)

end PerfChartGens

end Work.DSM5b
