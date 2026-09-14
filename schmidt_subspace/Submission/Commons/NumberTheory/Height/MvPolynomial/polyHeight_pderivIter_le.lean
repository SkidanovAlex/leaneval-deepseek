import Mathlib
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties
import Submission.Commons.Algebra.MvPolynomial.coeff_pderivIter
import Submission.Commons.NumberTheory.Height.mulHeight_finsupp_coe_eq
import Submission.Commons.NumberTheory.Height.NumberField.mulHeight1_natCast
import Submission.Commons.NumberTheory.Height.NumberField.mulHeight_mul_nat_le

/-!
# Height of an iterated partial derivative of a multivariate polynomial over `ℚ`

We bound the (projective, i.e. `max 1`-normalised) logarithmic coefficient height of the
iterated formal partial derivative `∂^m P` of a multivariate polynomial `P` over `ℚ` by the
height of `P` plus `|m| · log D`, where `D ≥ 1` bounds the total degree of the monomials of
`P` and `|m| = m.sum (fun _ k => k)`.

The height used is `Height.logHeight` of the function `Option (σ →₀ ℕ) → ℚ` that takes the
value `1` at `none` and the coefficient `coeff n ·` at `some n`; this is the coefficient
height of `P` in the normalisation where the coefficient vector is augmented by a `1`
(equivalently, the height of `[1 : coeffs]` in projective space).

The mathematical content is the standard estimate for formal derivatives.  Writing
`c = coeff P` and `d = coeff (∂^m P)`, the coefficient formula
(`Commons.Algebra.MvPolynomial.coeff_pderivIter`) gives

  `d n = c (n + m) * ∏ i, ((n + m) i).descFactorial (m i)`.

Since `(n + m)` is a monomial of `P` whenever `d n ≠ 0`, each component of `n + m` is at most
`D`, so the `descFactorial` product is at most `∏ i, D ^ (m i) = D ^ |m|`.  As
`∏ i, ... .descFactorial ...` is a natural number it is `≤ 1` at every non-archimedean place,
while at the archimedean place of `ℚ` it contributes at most `D ^ |m|`.  Multiplying by the
bounded natural-number factor therefore multiplies the height by at most
`Height.mulHeight₁ ((D ^ |m| : ℕ) : ℚ) = (D ^ |m| : ℝ)` (here `Height.totalWeight ℚ = 1`,
i.e. `ℚ` has a single archimedean absolute value of multiplicity one), and taking logarithms
gives the claim.  The technical core is the comparison

  `mulHeight (F|_S) ≤ mulHeight (G|_T) * mulHeight₁ ((D ^ |m| : ℕ) : ℚ)`

obtained from `Height.mulHeight_mul_le`, the monotonicity `Height.mulHeight_comp_le` for the
injective shift `some n ↦ some (n + m)`, and the commons lemma
`Commons.NumberTheory.Height.NumberField.mulHeight_natCast_le`.

## Main result

* `Commons.NumberTheory.Height.MvPolynomial.polyHeight_pderivIter_le`
-/

namespace Commons.NumberTheory.Height.MvPolynomial

open scoped BigOperators

/-- The total weight of `ℚ` is `1`: `ℚ` has exactly one archimedean absolute value, with
multiplicity one. -/
private theorem totalWeight_rat : Height.totalWeight ℚ = 1 := by
  rw [NumberField.totalWeight_eq_sum_mult]
  simp

/-- `Finsupp.sum s (fun _ k => k)` (the total degree of a multi-index) written as a
`Finset.sum`. -/
private theorem finsupp_sum_apply_eq_sum {σ : Type*} [Fintype σ] (s : σ →₀ ℕ) :
    s.sum (fun _ k => k) = ∑ j : σ, s j := by
  rw [Finsupp.sum]
  rw [Finset.sum_subset (Finset.subset_univ _)]
  intro j _ hj
  rw [Finsupp.notMem_support_iff.mp hj]

/-- The multiplicative height of a natural number `C ≥ 1` inside `ℚ` is `C` itself. -/
private theorem mulHeight1_rat_natCast (C : ℕ) (hC : 1 ≤ C) :
    Height.mulHeight₁ (C : ℚ) = (C : ℝ) := by
  rw [Commons.NumberTheory.Height.NumberField.mulHeight1_natCast C hC, totalWeight_rat, pow_one]

/-- **Height growth of an iterated partial derivative.**  If every monomial of
`P : MvPolynomial σ ℚ` has total degree at most `D ≥ 1`, then the coefficient height of
`∂^m P` (in the normalisation in which a `1` is appended to the vector of coefficients)
is at most the coefficient height of `P` plus `|m| · log D`, where `|m| = m.sum (fun _ k => k)`
is the total degree of the multi-index `m`. -/
theorem polyHeight_pderivIter_le {σ : Type*} [Fintype σ]
    (D : ℕ) (hD : 1 ≤ D) (m : σ →₀ ℕ) (P : MvPolynomial σ ℚ)
    (hdeg : ∀ t ∈ P.support, t.sum (fun _ k => k) ≤ D) :
    Height.logHeight (fun o : Option (σ →₀ ℕ) =>
        o.elim (1 : ℚ) (fun n =>
          MvPolynomial.coeff n (Commons.Algebra.MvPolynomial.pderivIter m P))) ≤
      Height.logHeight (fun o : Option (σ →₀ ℕ) =>
        o.elim (1 : ℚ) (fun n => MvPolynomial.coeff n P)) +
      (m.sum (fun _ k => k) : ℝ) * Real.log D := by
  classical
  set e : ℕ := m.sum (fun _ k => k) with he
  have heR : (e : ℝ) = m.sum (fun _ (k : ℕ) => (k : ℝ)) := by
    rw [he, Finsupp.sum, Finsupp.sum, Nat.cast_sum]
  set Q : MvPolynomial σ ℚ := Commons.Algebra.MvPolynomial.pderivIter m P with hQ
  -- the two functions whose heights we compare
  set F : Option (σ →₀ ℕ) → ℚ := fun o => o.elim (1 : ℚ) (fun n => MvPolynomial.coeff n Q)
  set G : Option (σ →₀ ℕ) → ℚ := fun o => o.elim (1 : ℚ) (fun n => MvPolynomial.coeff n P)
  -- the finite index sets supporting them
  set S : Finset (Option (σ →₀ ℕ)) := insert none (Q.support.map (Function.Embedding.some))
  set T : Finset (Option (σ →₀ ℕ)) := insert none (P.support.map (Function.Embedding.some))
  -- the monomial multiplicities `∏ i, ((n+m) i).descFactorial (m i)`, extended by `1` at `none`
  set bb : Option (σ →₀ ℕ) → ℕ :=
    fun o => o.elim 1 (fun n => ∏ i : σ, ((n + m) i).descFactorial (m i))
  have hFS : ∀ o : Option (σ →₀ ℕ), o ∉ S → F o = 0 := by
    intro o ho
    cases o with
    | none => exact absurd (Finset.mem_insert_self _ _) ho
    | some n =>
      have hn : n ∉ Q.support := by
        intro h
        exact ho (Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨n, h, rfl⟩))
      simp only [F, Option.elim_some]
      exact MvPolynomial.notMem_support_iff.mp hn
  have hGT : ∀ o : Option (σ →₀ ℕ), o ∉ T → G o = 0 := by
    intro o ho
    cases o with
    | none => exact absurd (Finset.mem_insert_self _ _) ho
    | some n =>
      have hn : n ∉ P.support := by
        intro h
        exact ho (Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨n, h, rfl⟩))
      simp only [G, Option.elim_some, MvPolynomial.notMem_support_iff.mp hn]
  -- membership descriptions
  have hmemS : ∀ n : σ →₀ ℕ, some n ∈ S ↔ n ∈ Q.support := by
    intro n
    simp [S, Finset.mem_map]
  have hmemT : ∀ n : σ →₀ ℕ, some n ∈ T ↔ n ∈ P.support := by
    intro n
    simp [T, Finset.mem_map]
  -- the shift map `none ↦ none`, `some n ↦ some (n + m)`
  have hshift : ∀ i : ↥S, (match (i : Option (σ →₀ ℕ)) with
      | none => (none : Option (σ →₀ ℕ))
      | some n => some (n + m)) ∈ T := by
    rintro ⟨o, ho⟩
    cases o with
    | none => exact Finset.mem_insert_self _ _
    | some n =>
      refine Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨n + m, ?_, rfl⟩)
      have hn : n ∈ Q.support := (hmemS n).mp ho
      have h1 : MvPolynomial.coeff n Q ≠ 0 := MvPolynomial.mem_support_iff.mp hn
      rw [hQ, Commons.Algebra.MvPolynomial.coeff_pderivIter m n P] at h1
      by_contra hc
      exact h1 (by rw [MvPolynomial.notMem_support_iff.mp hc, zero_mul])
  set φ : ↥S → ↥T := fun i => ⟨_, hshift i⟩
  -- the pointwise identity `F = (G ∘ φ) * bb`
  have hpoint : ∀ i : ↥S, F i = G (φ i) * (bb i : ℚ) := by
    rintro ⟨o, ho⟩
    cases o with
    | none => simp [F, G, bb, φ]
    | some n =>
      have hn : n ∈ Q.support := (hmemS n).mp ho
      have hcoeff : MvPolynomial.coeff n Q =
          MvPolynomial.coeff (n + m) P * (∏ i : σ, ((n + m) i).descFactorial (m i)) := by
        rw [hQ]
        exact Commons.Algebra.MvPolynomial.coeff_pderivIter m n P
      simp only [F, G, bb, φ, Option.elim_some]
      rw [hcoeff]
  -- the natural-number bound on `bb`
  have hbb : ∀ i : ↥S, bb i ≤ D ^ e := by
    rintro ⟨o, ho⟩
    cases o with
    | none => simp only [bb, Option.elim_none]; exact one_le_pow₀ hD
    | some n =>
      have hn : n ∈ Q.support := (hmemS n).mp ho
      have hmem : n + m ∈ P.support := by
        have h1 : MvPolynomial.coeff n Q ≠ 0 := MvPolynomial.mem_support_iff.mp hn
        rw [hQ, Commons.Algebra.MvPolynomial.coeff_pderivIter m n P] at h1
        exact MvPolynomial.mem_support_iff.mpr fun hc => h1 (by rw [hc, zero_mul])
      have hle : ∀ j : σ, (n + m) j ≤ D := by
        intro j
        have h1 : (n + m) j ≤ ∑ j : σ, (n + m) j :=
          Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
        have h2 : ∑ j : σ, (n + m) j = (n + m).sum (fun _ k => k) :=
          (finsupp_sum_apply_eq_sum _).symm
        have h3 := hdeg (n + m) hmem
        omega
      have hprod : (∏ j : σ, ((n + m) j).descFactorial (m j)) ≤ D ^ e := by
        calc ∏ j : σ, ((n + m) j).descFactorial (m j)
            ≤ ∏ j : σ, D ^ (m j) :=
              Finset.prod_le_prod (fun j _ => Nat.zero_le _)
                (fun j _ => le_trans (Nat.descFactorial_le_pow _ _)
                  (Nat.pow_le_pow_left (hle j) _))
          _ = D ^ (∑ j : σ, m j) := Finset.prod_pow_eq_pow_sum _ _ _
          _ = D ^ e := by rw [he, finsupp_sum_apply_eq_sum]
      simpa only [bb, Option.elim_some] using hprod
  -- multiplicative-height comparison
  have hcomp : Height.mulHeight (fun i : ↥S => F i)
      = Height.mulHeight ((fun j : ↥T => G j) ∘ φ * fun i : ↥S => (bb i : ℚ)) := by
    congr 1
    funext i
    exact hpoint i
  have hmul : Height.mulHeight (fun i : ↥S => F i)
      ≤ Height.mulHeight (fun j : ↥T => G j) * Height.mulHeight₁ ((D ^ e : ℕ) : ℚ) := by
    rw [hcomp]
    calc Height.mulHeight ((fun j : ↥T => G j) ∘ φ * fun i : ↥S => (bb i : ℚ))
        ≤ Height.mulHeight ((fun j : ↥T => G j) ∘ φ) *
            Height.mulHeight (fun i : ↥S => (bb i : ℚ)) := Height.mulHeight_mul_le _ _
      _ ≤ Height.mulHeight (fun j : ↥T => G j) * Height.mulHeight₁ ((D ^ e : ℕ) : ℚ) := by
          refine mul_le_mul (Height.mulHeight_comp_le φ _)
            (Commons.NumberTheory.Height.NumberField.mulHeight_natCast_le (fun i : ↥S => bb i)
              (D ^ e) hbb (one_le_pow₀ hD))
            (by positivity) (Height.mulHeight_pos _).le
  have hlogF : Height.logHeight F = Height.logHeight (fun i : ↥S => F i) := by
    rw [Height.logHeight_eq_log_mulHeight, Height.logHeight_eq_log_mulHeight,
      Commons.NumberTheory.Height.mulHeight_eq_mulHeight_finset S hFS]
  have hlogG : Height.logHeight G = Height.logHeight (fun j : ↥T => G j) := by
    rw [Height.logHeight_eq_log_mulHeight, Height.logHeight_eq_log_mulHeight,
      Commons.NumberTheory.Height.mulHeight_eq_mulHeight_finset T hGT]
  have hlogC : Real.log (Height.mulHeight₁ ((D ^ e : ℕ) : ℚ)) = (e : ℝ) * Real.log D := by
    rw [mulHeight1_rat_natCast (D ^ e) (one_le_pow₀ hD), Nat.cast_pow, Real.log_pow]
  calc Height.logHeight F
      = Height.logHeight (fun i : ↥S => F i) := hlogF
    _ = Real.log (Height.mulHeight (fun i : ↥S => F i)) := rfl
    _ ≤ Real.log (Height.mulHeight (fun j : ↥T => G j) *
          Height.mulHeight₁ ((D ^ e : ℕ) : ℚ)) :=
        Real.log_le_log (Height.mulHeight_pos _) hmul
    _ = Real.log (Height.mulHeight (fun j : ↥T => G j)) +
          Real.log (Height.mulHeight₁ ((D ^ e : ℕ) : ℚ)) :=
        Real.log_mul (Height.mulHeight_pos _).ne' (Height.mulHeight₁_ne_zero _)
    _ = Height.logHeight (fun j : ↥T => G j) + (e : ℝ) * Real.log D := by
        rw [hlogC, ← Height.logHeight_eq_log_mulHeight]
    _ = Height.logHeight G + (m.sum (fun _ k => k) : ℝ) * Real.log D := by
        rw [← hlogG, heR]

end Commons.NumberTheory.Height.MvPolynomial
