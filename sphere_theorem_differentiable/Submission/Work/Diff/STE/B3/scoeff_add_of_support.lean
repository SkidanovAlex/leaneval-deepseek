import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.J_finite_rank

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Additivity of the Fourier coefficient functional `scoeff` for functions supported in the cube

`Work.Diff.STE.B3.scoeff n ρ ε f q` is the `q`-th Fourier coefficient of the truncation of the
*periodisation* of `f` (`Work.Diff.STE.B3.perCoeffN`), i.e. of

  `per f = fun y => ∑' k : Fin n → ℤ, ((f (y + k) : ℝ) : ℂ)`   evaluated at `ρ (ε • m)`.

The file proves `scoeff_add_of_support`: for continuous `f g` whose supports lie in the *half open*
unit cube `(-1/2, 1/2]^n`, `scoeff` is additive in its function argument.  This is one of the two
linearity properties of the coefficient functional used by the Galerkin scheme of Layer B3
(`abs_scoeff_le`, `scoeff_smul_of_support` are the siblings).

The mathematical content is that for `f` supported in the half-open cube the lattice sum defining
`per f` has **at most one** non-zero term at every point `y` (the intervals
`(-1/2 - y i, 1/2 - y i]` have length `1`), and that `per f` is continuous (a local finite sum
argument).  Additivity then follows from `Summable.tsum_add` together with additivity of the
Bochner integral, and from the (pointwise) linearity of `trunc`, `Complex.re`, `Complex.im`.
-/

noncomputable section

namespace Work.Diff.STE.B3

open MeasureTheory Set
open scoped BigOperators

/-! ## 1. The periodisation of the complexification of a real function -/

/-- The periodisation of the complexification of `f : (Fin n → ℝ) → ℝ`:
`perFun f y = ∑' k, (f (y + k) : ℂ)`.  This is the function whose higher Fourier coefficients
`perCoeffN n f` are. -/
def perFun {n : ℕ} (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℂ :=
  fun y => ∑' k : Fin n → ℤ, ((f (y + Work.Diff.STE.iVec k) : ℝ) : ℂ)

/-- `perCoeffN n f` is the Fourier coefficient family of `perFun f`, by definition. -/
theorem perCoeffN_eq_fourierCoeff {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    perCoeffN n f = Work.Diff.STE.fourierCoeff (perFun f) := rfl

/-- The character `x ↦ e^{2πi m·x}` is continuous. -/
theorem continuous_fourierExp_fin {n : ℕ} (m : Fin n → ℤ) :
    Continuous (Work.Diff.STE.fourierExp m) := by
  unfold Work.Diff.STE.fourierExp
  fun_prop

/-! ## 2. Summability of the lattice translates

For `f` supported in the half-open cube `(-1/2, 1/2]^n` and *every* `y`, the family
`k ↦ f (y + k)` is finitely supported: the half-open intervals `(-1/2 - y i, 1/2 - y i]` have
length one, so each coordinate of `k` is determined by `y`. -/

/-- If `f` is supported in the half-open cube `(-1/2, 1/2]^n`, then for every `y` the set of
`k` with `f (y + k) ≠ 0` is a subsingleton (two such `k` would differ by a non-zero integer vector
whose coordinates all lie in `(-1, 1)`). -/
lemma subsingleton_support_lattice {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hfs : Function.support f ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)))
    (y : Fin n → ℝ) :
    Set.Subsingleton {k : Fin n → ℤ | f (y + Work.Diff.STE.iVec k) ≠ 0} := by
  intro k hk k' hk'
  have h1 : y + Work.Diff.STE.iVec k ∈
      Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) := hfs hk
  have h2 : y + Work.Diff.STE.iVec k' ∈
      Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) := hfs hk'
  by_contra hne
  have hex : ∃ i, k i ≠ k' i := by
    by_contra h
    exact hne (funext fun i => by by_contra h2'; exact h ⟨i, h2'⟩)
  obtain ⟨i, hi⟩ := hex
  have c1 := Set.mem_pi.mp h1 i (Set.mem_univ i)
  have c2 := Set.mem_pi.mp h2 i (Set.mem_univ i)
  rw [Set.mem_Ioc] at c1 c2
  have e1 : (y + Work.Diff.STE.iVec k) i = y i + (k i : ℝ) := by simp [Work.Diff.STE.iVec]
  have e2 : (y + Work.Diff.STE.iVec k') i = y i + (k' i : ℝ) := by simp [Work.Diff.STE.iVec]
  rw [e1] at c1
  rw [e2] at c2
  have hz : |((k i - k' i : ℤ) : ℝ)| < 1 := by
    have hcast : ((k i - k' i : ℤ) : ℝ) = (y i + (k i : ℝ)) - (y i + (k' i : ℝ)) := by
      push_cast; ring
    rw [hcast, abs_lt]
    exact ⟨by linarith [c1.1, c2.2], by linarith [c1.2, c2.1]⟩
  have hz2 : |k i - k' i| < (1 : ℤ) := by
    have h := hz
    rw [← Int.cast_abs] at h
    exact_mod_cast h
  have h3 := abs_lt.mp hz2
  omega

/-- For `f` supported in the half-open cube and every `y`, the lattice sum `k ↦ f (y + k)` is
summable. -/
lemma summable_perFun {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hfs : Function.support f ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)))
    (y : Fin n → ℝ) :
    Summable (fun k : Fin n → ℤ => ((f (y + Work.Diff.STE.iVec k) : ℝ) : ℂ)) := by
  have hsub := subsingleton_support_lattice hfs y
  have hfin : ({k : Fin n → ℤ | f (y + Work.Diff.STE.iVec k) ≠ 0}).Finite := hsub.finite
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun k hk => ?_
  by_cases hfk : f (y + Work.Diff.STE.iVec k) = 0
  · rw [hfk, Complex.ofReal_zero]
  · exact absurd ((Set.Finite.mem_toFinset hfin).mpr hfk) hk

/-! ## 3. Additivity of the periodisation -/

/-- The periodisation is additive in the function. -/
lemma perFun_add {n : ℕ} (f g : (Fin n → ℝ) → ℝ)
    (hfs : Function.support f ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)))
    (hgs : Function.support g ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)))
    (y : Fin n → ℝ) :
    perFun (f + g) y = perFun f y + perFun g y := by
  have h1 : ∀ k : Fin n → ℤ,
      (((f + g) (y + Work.Diff.STE.iVec k) : ℝ) : ℂ)
        = ((f (y + Work.Diff.STE.iVec k) : ℝ) : ℂ)
          + ((g (y + Work.Diff.STE.iVec k) : ℝ) : ℂ) := by
    intro k
    simp only [Pi.add_apply, Complex.ofReal_add]
  simp only [perFun]
  rw [tsum_congr h1]
  exact Summable.tsum_add (summable_perFun hfs y) (summable_perFun hgs y)

/-- The periodisation is additive in the function, as an equality of functions. -/
lemma perFun_add_fun {n : ℕ} (f g : (Fin n → ℝ) → ℝ)
    (hfs : Function.support f ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)))
    (hgs : Function.support g ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))) :
    perFun (f + g) = perFun f + perFun g :=
  funext fun y => perFun_add f g hfs hgs y

/-! ## 4. Continuity of the periodisation

Near a point `x` only the finitely many `k` with `|k i| ≤ ⌊|x i|⌋ + 1` can contribute (the
half-open intervals `(-1/2 - y i, 1/2 - y i]` have length `1` and `|y i - x i| < 1/2`), so locally
the sum is a finite sum of continuous translates of `f`. -/

/-- **The periodisation of a continuous function supported in the half-open cube is
continuous.** -/
lemma perFun_continuous {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    (hfs : Function.support f ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))) :
    Continuous (perFun f) := by
  rw [continuous_iff_continuousAt]
  intro x
  classical
  set N : Fin n → ℤ := fun i => ⌊|x i|⌋ + 2 with hNdef
  set S : Finset (Fin n → ℤ) := Fintype.piFinset (fun i => Finset.Icc (-(N i)) (N i)) with hSdef
  have hfin : Continuous
      (fun y : Fin n → ℝ => ∑ m ∈ S, ((f (y + Work.Diff.STE.iVec m) : ℝ) : ℂ)) := by
    refine continuous_finsetSum S (fun m _ => ?_)
    exact Complex.continuous_ofReal.comp (hf.comp (continuous_id.add continuous_const))
  have hBopen : IsOpen (Set.pi Set.univ (fun i : Fin n => Set.Ioo (x i - 1 / 2) (x i + 1 / 2))) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hxB : x ∈ Set.pi Set.univ (fun i : Fin n => Set.Ioo (x i - 1 / 2) (x i + 1 / 2)) := by
    rw [Set.mem_pi]
    intro i _
    rw [Set.mem_Ioo]
    constructor <;> linarith
  have hEq : (fun y : Fin n → ℝ => ∑ m ∈ S, ((f (y + Work.Diff.STE.iVec m) : ℝ) : ℂ))
      =ᶠ[nhds x] perFun f := by
    refine Filter.eventually_of_mem (hBopen.mem_nhds hxB) ?_
    intro y hy
    refine (tsum_eq_sum (s := S) ?_).symm
    intro m hm
    by_contra hc
    have hyabs : ∀ i, |y i - x i| < 1 / 2 := by
      intro i
      have h := Set.mem_pi.mp hy i (Set.mem_univ i)
      rw [Set.mem_Ioo] at h
      rw [abs_lt]
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have hfne : f (y + Work.Diff.STE.iVec m) ≠ 0 := by
      rw [ne_eq, ← Complex.ofReal_eq_zero]
      exact hc
    have hmem : y + Work.Diff.STE.iVec m ∈
        Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) := hfs hfne
    have hbound : m ∈ S := by
      rw [hSdef, Fintype.mem_piFinset]
      intro i
      have hcoord := Set.mem_pi.mp hmem i (Set.mem_univ i)
      rw [Set.mem_Ioc] at hcoord
      have hval : (y + Work.Diff.STE.iVec m) i = y i + (m i : ℝ) := by
        simp [Work.Diff.STE.iVec]
      rw [hval] at hcoord
      have h1 : |(m i : ℝ)| ≤ 1 / 2 + |y i| := by
        calc |(m i : ℝ)| = |(y i + (m i : ℝ)) - y i| := by rw [add_sub_cancel_left]
          _ ≤ |y i + (m i : ℝ)| + |y i| := by
              simpa using abs_sub_le (y i + (m i : ℝ)) 0 (y i)
          _ ≤ 1 / 2 + |y i| := by
              have hle : |y i + (m i : ℝ)| ≤ 1 / 2 := by
                rw [abs_le]
                exact ⟨by linarith [hcoord.1], hcoord.2⟩
              linarith
      have h2 : |y i| < |x i| + 1 / 2 := by
        calc |y i| = |(y i - x i) + x i| := by ring_nf
          _ ≤ |y i - x i| + |x i| := abs_add_le _ _
          _ < 1 / 2 + |x i| := by linarith [hyabs i]
          _ = |x i| + 1 / 2 := by ring
      have hfl := Int.lt_floor_add_one (|x i|)
      have h3 : |(m i : ℝ)| < (N i : ℝ) := by
        rw [hNdef]
        push_cast
        linarith
      have h3z : |m i| < N i := by
        rw [← Int.cast_abs] at h3
        exact_mod_cast h3
      obtain ⟨hlo, hhi⟩ := abs_lt.mp h3z
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact hm hbound
  exact hfin.continuousAt.congr hEq

/-! ## 5. Additivity of the Fourier coefficient -/

/-- Additivity of the Fourier coefficient in the function, for integrable integrands. -/
lemma fourierCoeff_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F G : (ι → ℝ) → ℂ) (k : ι → ℤ)
    (hF : IntegrableOn (fun x => Work.Diff.STE.fourierExp (-k) x * F x)
      (Work.Diff.STE.unitCube (ι := ι)))
    (hG : IntegrableOn (fun x => Work.Diff.STE.fourierExp (-k) x * G x)
      (Work.Diff.STE.unitCube (ι := ι))) :
    Work.Diff.STE.fourierCoeff (fun x => F x + G x) k
      = Work.Diff.STE.fourierCoeff F k + Work.Diff.STE.fourierCoeff G k := by
  simp only [Work.Diff.STE.fourierCoeff]
  rw [show (fun x => Work.Diff.STE.fourierExp (-k) x * (F x + G x))
      = fun x => Work.Diff.STE.fourierExp (-k) x * F x
          + Work.Diff.STE.fourierExp (-k) x * G x from funext fun x => mul_add _ _ _]
  exact integral_add hF hG

/-- The integrand `e_{-m} · perFun f` is integrable on the unit cube as soon as `perFun f` is
continuous: the unit cube is contained in the compact box `[0,1]^n`. -/
lemma integrableOn_fourierExp_mul_perFun {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hcont : Continuous (perFun f)) (m : Fin n → ℤ) :
    IntegrableOn (fun x => Work.Diff.STE.fourierExp (-m) x * perFun f x)
      (Work.Diff.STE.unitCube (ι := Fin n)) := by
  have hc : Continuous (fun x : Fin n → ℝ => Work.Diff.STE.fourierExp (-m) x * perFun f x) :=
    (continuous_fourierExp_fin (-m)).mul hcont
  have hK : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : Work.Diff.STE.unitCube (ι := Fin n)
      ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [Work.Diff.STE.unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (ContinuousOn.integrableOn_compact hK hc.continuousOn).mono_set hsub

/-- **Additivity of the periodised Fourier coefficients.** -/
theorem perCoeffN_add {n : ℕ} (f g : (Fin n → ℝ) → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfs : Function.support f ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)))
    (hgs : Function.support g ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))) :
    perCoeffN n (f + g) = perCoeffN n f + perCoeffN n g := by
  funext m
  show Work.Diff.STE.fourierCoeff (perFun (f + g)) m
      = Work.Diff.STE.fourierCoeff (perFun f) m + Work.Diff.STE.fourierCoeff (perFun g) m
  rw [perFun_add_fun f g hfs hgs]
  exact fourierCoeff_add (perFun f) (perFun g) m
    (integrableOn_fourierExp_mul_perFun (perFun_continuous hf hfs) m)
    (integrableOn_fourierExp_mul_perFun (perFun_continuous hg hgs) m)

/-! ## 6. The target: additivity of `scoeff` -/

theorem scoeff_add_of_support
    {n : ℕ} (ρ : (Fin n → ℝ) → ℝ) (ε : ℝ) (f g : (Fin n → ℝ) → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfs : Function.support f ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)))
    (hgs : Function.support g ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)))
    (q : Work.Diff.STE.B3.QIdx n ε) :
    Work.Diff.STE.B3.scoeff n ρ ε (f + g) q
      = Work.Diff.STE.B3.scoeff n ρ ε f q + Work.Diff.STE.B3.scoeff n ρ ε g q := by
  have hcoeff : ∀ m : Fin n → ℤ, perCoeffN n (f + g) m = perCoeffN n f m + perCoeffN n g m :=
    fun m => congrFun (perCoeffN_add f g hf hg hfs hgs) m
  rcases q with ⟨⟨m, hm⟩, σ⟩
  have htr : Work.Diff.STE.trunc ρ ε (perCoeffN n (f + g)) m
      = Work.Diff.STE.trunc ρ ε (perCoeffN n f) m
        + Work.Diff.STE.trunc ρ ε (perCoeffN n g) m := by
    simp only [Work.Diff.STE.trunc]
    rw [hcoeff m, mul_add]
  simp only [Work.Diff.STE.B3.scoeff]
  cases σ
  · simp only [Bool.cond_false, htr, Complex.add_re]
  · simp only [Bool.cond_true, htr, Complex.add_im]
    ring

end Work.Diff.STE.B3
