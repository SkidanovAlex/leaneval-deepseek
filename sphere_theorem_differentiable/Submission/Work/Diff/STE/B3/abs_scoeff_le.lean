import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.J_finite_rank

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Fourier coefficients of a cube-supported function are bounded by its sup norm

`Work.Diff.STE.B3.scoeff n ρ ε f q` is the coefficient of the mode `q` in the truncation `trunc ρ ε`
of the periodisation `perCoeffN n f` of `f`, i.e. (up to the choice of real or imaginary part)

  `scoeff ρ ε f q = ρ (ε • m) · (per f)^(m)`,   `q = (m, σ)`,

see `Work.Diff.STE.B3.scoeff` and `Work.Diff.STE.trunc`.  The lemma proved here,

`Work.Diff.STE.B3.abs_scoeff_le`,

bounds it by `|ρ (ε • m)| * C` whenever `f` is supported in the half-open cube
`(-1/2, 1/2]ⁿ` and `|f| ≤ C` pointwise.  The point is that the periodisation of such an `f` is, on
the fundamental cube `(0,1]ⁿ`, a *single* translate of `f`:

  `per f (x) = ∑'_k f (x + k) = f (x + k(x))`   for `x ∈ (0,1]ⁿ`,

where the lattice vector `k(x) ∈ {-1,0}ⁿ` is the unique one with `x + k(x) ∈ (-1/2,1/2]ⁿ`; indeed
any `k` with `f (x + k) ≠ 0` has `x + k ∈ (-1/2,1/2]ⁿ`, which forces `kᵢ ∈ {-1,0}`, and then the
sign of `xᵢ - 1/2` determines `kᵢ` uniquely.  Hence `‖per f x‖ ≤ C` on the whole cube, and the
Fourier coefficient is an integral over a measure-one set, so it is bounded by `C`.

The only analytic input used is `MeasureTheory.norm_integral_le_of_norm_le_const`; no continuity of
`f` and no summability of the lattice sum are needed (the `tsum` collapses to a single term).
-/

noncomputable section

open MeasureTheory

namespace Work.Diff.STE.B3

/-! ## Elementary measure-theoretic and trigonometric bookkeeping -/

/-- The Fourier characters have modulus one. -/
lemma abs_scoeff_norm_fourierExp {ι : Type*} [Fintype ι] (k : ι → ℤ) (x : ι → ℝ) :
    ‖Work.Diff.STE.fourierExp k x‖ = 1 := by
  have hmain : (2 * (Real.pi : ℂ) * Complex.I * ∑ i, ((k i : ℤ) : ℂ) * (x i : ℂ))
      = (((2 * Real.pi * ∑ i, ((k i : ℤ) : ℝ) * x i : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [Work.Diff.STE.fourierExp, hmain, Complex.norm_exp_ofReal_mul_I]

/-- The unit cube `(0,1]꜀` has measure one. -/
lemma abs_scoeff_volume_unitCube {ι : Type*} [Fintype ι] :
    (volume : Measure (ι → ℝ)) (Work.Diff.STE.unitCube (ι := ι)) = 1 := by
  rw [Work.Diff.STE.unitCube, Real.volume_pi_Ioc]
  simp

/-- The unit cube is measurable. -/
lemma abs_scoeff_measurableSet_unitCube {ι : Type*} [Fintype ι] :
    MeasurableSet (Work.Diff.STE.unitCube (ι := ι)) := by
  rw [Work.Diff.STE.unitCube]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/-! ## The bound on the Fourier coefficients of the periodisation -/

/-- **The coefficients of the periodisation are bounded by the sup norm.**  If `f` is supported in
the half-open cube `(-1/2, 1/2]ⁿ` and `|f| ≤ C`, then every Fourier coefficient (on the unit torus)
of its periodisation `∑'_k f (· + k)` is bounded by `C` in modulus.

The proof is the "wrapping" argument: on the fundamental cube `(0,1]ⁿ` the lattice sum has a single
nonzero term, whose value is a value of `f`; hence `‖per f‖ ≤ C` there, and the coefficient is the
integral of `per f` against a character of modulus one over a measure-one set. -/
lemma abs_scoeff_perCoeffN_norm_le {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hfs : Function.support f ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)))
    (C : ℝ) (hfC : ∀ z, |f z| ≤ C) (m : Fin n → ℤ) :
    ‖perCoeffN n f m‖ ≤ C := by
  have hdef : perCoeffN n f m
      = ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          Work.Diff.STE.fourierExp (-m) x *
            (∑' k : Fin n → ℤ, ((f (x + Work.Diff.STE.iVec k) : ℝ) : ℂ)) := rfl
  rw [hdef]
  -- on the fundamental cube, the periodisation is a single translate of `f`
  have hpt : ∀ x ∈ Work.Diff.STE.unitCube (ι := Fin n),
      ‖∑' k : Fin n → ℤ, ((f (x + Work.Diff.STE.iVec k) : ℝ) : ℂ)‖ ≤ C := by
    intro x hx
    -- the unique lattice vector with `x + k` in the half-open cube
    set kx : Fin n → ℤ := fun i => if (1 / 2 : ℝ) < x i then -1 else 0 with hkx
    have hsingle : ∀ k : Fin n → ℤ, k ≠ kx →
        ((f (x + Work.Diff.STE.iVec k) : ℝ) : ℂ) = 0 := by
      intro k hk
      by_contra hne
      have hmem : x + Work.Diff.STE.iVec k ∈ Function.support f := by
        simp only [Function.mem_support]
        intro hc
        exact hne (by rw [hc]; norm_num)
      have hcoord : ∀ i, x i + ((k i : ℤ) : ℝ) ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
        intro i
        have := Set.mem_pi.mp (hfs hmem) i (Set.mem_univ i)
        simpa using this
      have hxi : ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1 := by
        intro i
        have := Set.mem_pi.mp hx i (Set.mem_univ i)
        simpa [Work.Diff.STE.unitCube] using this
      have hkk : k = kx := by
        funext i
        have hi := hcoord i
        rw [Set.mem_Ioc] at hi
        have hxI := hxi i
        rw [Set.mem_Ioc] at hxI
        have h1 : ((k i : ℤ) : ℝ) < 1 := by linarith [hi.2, hxI.1]
        have h2 : ((k i : ℤ) : ℝ) > -(2 : ℝ) := by linarith [hi.1, hxI.2]
        have hk1 : (k i : ℤ) < 1 := by exact_mod_cast h1
        have hk2 : (-2 : ℤ) < k i := by exact_mod_cast h2
        have hcases : k i = -1 ∨ k i = 0 := by omega
        rw [hkx]
        change k i = (if (1 / 2 : ℝ) < x i then (-1 : ℤ) else 0)
        split_ifs with hlt
        · rcases hcases with h | h
          · exact h
          · exfalso; rw [h] at hi; simp at hi; linarith [hi.2, hlt.le]
        · rcases hcases with h | h
          · exfalso; rw [h] at hi; simp at hi; linarith [hi.1]
          · exact h
      exact hk hkk
    rw [tsum_eq_single kx hsingle]
    have := hfC (x + Work.Diff.STE.iVec kx)
    simpa [Complex.norm_real] using this
  haveI : IsFiniteMeasure ((volume : Measure (Fin n → ℝ)).restrict
      (Work.Diff.STE.unitCube (ι := Fin n))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      abs_scoeff_volume_unitCube (ι := Fin n)]
    exact ENNReal.one_lt_top
  have hae : ∀ᵐ x ∂((volume : Measure (Fin n → ℝ)).restrict
      (Work.Diff.STE.unitCube (ι := Fin n))),
      ‖Work.Diff.STE.fourierExp (-m) x *
        (∑' k : Fin n → ℤ, ((f (x + Work.Diff.STE.iVec k) : ℝ) : ℂ))‖ ≤ C := by
    rw [MeasureTheory.ae_restrict_iff' (abs_scoeff_measurableSet_unitCube (ι := Fin n))]
    exact Filter.Eventually.of_forall fun x hx => by
      rw [norm_mul, abs_scoeff_norm_fourierExp (-m) x, one_mul]
      exact hpt x hx
  have hb := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := (volume : Measure (Fin n → ℝ)).restrict (Work.Diff.STE.unitCube (ι := Fin n))) hae
  have hreal : ((volume : Measure (Fin n → ℝ)).restrict
      (Work.Diff.STE.unitCube (ι := Fin n))).real Set.univ = 1 := by
    rw [MeasureTheory.Measure.real_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      abs_scoeff_volume_unitCube (ι := Fin n)]
    exact ENNReal.toReal_one
  rwa [hreal, mul_one] at hb

/-! ## The bound on `scoeff` -/

theorem abs_scoeff_le
    {n : ℕ} (ρ : (Fin n → ℝ) → ℝ) (ε : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : Continuous f)
    (hfs : Function.support f ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)))
    (q : Work.Diff.STE.B3.QIdx n ε) (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ z, |f z| ≤ C) :
    |Work.Diff.STE.B3.scoeff n ρ ε f q| ≤
      |ρ (ε • fun i => ((q.1.1 i : ℤ) : ℝ))| * C := by
  have hb : ‖perCoeffN n f q.1.1‖ ≤ C := abs_scoeff_perCoeffN_norm_le f hfs C hfC q.1.1
  have hre : |(perCoeffN n f q.1.1).re| ≤ C := le_trans (Complex.abs_re_le_norm _) hb
  have him : |(perCoeffN n f q.1.1).im| ≤ C := le_trans (Complex.abs_im_le_norm _) hb
  have htrre : (Work.Diff.STE.trunc ρ ε (perCoeffN n f) q.1.1).re
      = ρ (ε • fun i => (q.1.1 i : ℝ)) * (perCoeffN n f q.1.1).re := by
    simp [Work.Diff.STE.trunc]
  have htrim : (Work.Diff.STE.trunc ρ ε (perCoeffN n f) q.1.1).im
      = ρ (ε • fun i => (q.1.1 i : ℝ)) * (perCoeffN n f q.1.1).im := by
    simp [Work.Diff.STE.trunc]
  cases hq : q.2
  · unfold scoeff
    rw [hq]
    simp only [Bool.cond_false]
    rw [htrre, abs_mul]
    exact mul_le_mul_of_nonneg_left hre (abs_nonneg _)
  · unfold scoeff
    rw [hq]
    simp only [Bool.cond_true]
    rw [abs_neg, htrim, abs_mul]
    exact mul_le_mul_of_nonneg_left him (abs_nonneg _)

end Work.Diff.STE.B3
