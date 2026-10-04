import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep5.conjCut_lapPow
import Submission.Work.Diff.STE.flat.fourierCoeff_seriesFun
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.summable_norm_of_CSq
import Submission.Work.Diff.STE.eq_zero_of_fourierCoeff_eq_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# B3 symbol calculus: the algebra of the flat Laplacian powers `Λ^j`

`Work.Diff.STE.B3.SymCalcStep5.lapPow j` is the flat Laplacian power `Λ^j` on the torus, *defined*
as the Fourier multiplier with symbol `flatLam m ^ j = (Σᵢ (2π mᵢ)²)^j`
(`seriesFun (fun m => (flatLam m)^j · û(m))`).

This file proves the two algebraic identities of `Λ^·` on the class of smooth `1`-periodic
functions:

* `Λ^i (Λ^j w) = Λ^{i+j} w`  (composition of the multipliers),
* `Λ^j (u + v) = Λ^j u + Λ^j v`  (linearity).

Both are immediate once one knows that for a smooth `1`-periodic `w` the coefficients are again
the multiplier family,

  `fourierCoeff (Λ^j w) k = (flatLam k)^j · û(k)`   (`fourierCoeff_lapPow`),

because then both sides of the two identities are the `seriesFun` of the *same* coefficient
family (respectively of the sum of the two families), and `seriesFun` is a termwise-defined
`tsum`.  The only analysis is therefore

* the *rapid decay* of the coefficients `û(k)` of a smooth `1`-periodic function, which makes the
  multiplier family `ℓ¹`-summable (`summable_lapCoeff`): from
  `summable_weighted_fourierCoeff_of_contDiff` (weighted `ℓ²`, weight `⟨k⟩^{2s}`, any `s`) and the
  `ℓ² → ℓ¹` passage `summable_norm_of_CSq`, using `flatLam k ≤ 4π²⟨k⟩`
  (`flatLam_le_wt'`) to convert the multiplier `(flatLam k)^j` into the weight `⟨k⟩^j`;
* the additivity of `fourierCoeff` for continuous functions (`fourierCoeff_add_c`, linearity of the
  integral over the cube `(0,1]^ι`, a compact set).

With these, `fourierCoeff_seriesFun` (the absolutely convergent half of Fourier inversion) gives
`fourierCoeff_lapPow`, and the two identities follow by `seriesFun`-congruence.
-/

noncomputable section

namespace Work.Diff.STE.B3.SymCalcStep6

open MeasureTheory BigOperators

/-! ## 0. The characters have modulus one -/

private lemma nfe {ι : Type*} [Fintype ι] (k : ι → ℤ) (x : ι → ℝ) :
    ‖Work.Diff.STE.fourierExp k x‖ = 1 := by
  have hS : (∑ i, (k i : ℂ) * (x i : ℂ))
      = (((∑ i, ((k i : ℤ) : ℝ) * x i : ℝ)) : ℂ) := by
    push_cast
    rfl
  rw [Work.Diff.STE.fourierExp, hS]
  have h2 : 2 * (Real.pi : ℂ) * Complex.I * ((↑(∑ i, ↑↑(k i) * x i) : ℂ))
      = ((2 * Real.pi * (∑ i, ((k i : ℤ) : ℝ) * x i) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h2, Complex.norm_exp_ofReal_mul_I]

/-! ## 1. `seriesFun`: congruence and additivity -/

/-- Summability of `k ↦ c k · e^{2πi k·x}` from `ℓ¹` summability of `c`: the characters have
modulus one. -/
private lemma sm {ι : Type*} [Fintype ι] (x : ι → ℝ) {c : (ι → ℤ) → ℂ}
    (hc : Summable fun k => ‖c k‖) :
    Summable (fun k => c k * Work.Diff.STE.fourierExp k x) := by
  refine Summable.of_norm ?_
  refine hc.congr (fun k => ?_)
  rw [norm_mul, nfe k x, mul_one]

private lemma seriesFun_congr' {ι : Type*} [Fintype ι] {c d : (ι → ℤ) → ℂ}
    (h : ∀ k, c k = d k) :
    Work.Diff.STE.seriesFun c = Work.Diff.STE.seriesFun d := by
  funext x
  simp only [Work.Diff.STE.seriesFun]
  exact tsum_congr fun k => by rw [h k]

/-- `seriesFun` is additive on `ℓ¹`-summable coefficient families. -/
private lemma seriesFun_add' {ι : Type*} [Fintype ι] {c d : (ι → ℤ) → ℂ}
    (hc : Summable fun k => ‖c k‖) (hd : Summable fun k => ‖d k‖) :
    Work.Diff.STE.seriesFun (c + d)
      = Work.Diff.STE.seriesFun c + Work.Diff.STE.seriesFun d := by
  funext x
  have hc' := sm x hc
  have hd' := sm x hd
  simp only [Work.Diff.STE.seriesFun, Pi.add_apply]
  rw [show (∑' k, (c k + d k) * Work.Diff.STE.fourierExp k x)
      = ∑' k, (c k * Work.Diff.STE.fourierExp k x + d k * Work.Diff.STE.fourierExp k x) from
    tsum_congr fun k => add_mul _ _ _]
  rw [Summable.tsum_add hc' hd']

/-! ## 2. Additivity of the Fourier coefficient (linearity of the integral) -/

private lemma fourierCoeff_add_c {ι : Type*} [Fintype ι] (u v : (ι → ℝ) → ℂ)
    (hu : Continuous u) (hv : Continuous v) (k : ι → ℤ) :
    Work.Diff.STE.fourierCoeff (u + v) k
      = Work.Diff.STE.fourierCoeff u k + Work.Diff.STE.fourierCoeff v k := by
  have h1 : MeasureTheory.Integrable
      (fun x : ι → ℝ => Work.Diff.STE.fourierExp (-k) x * u x)
      (MeasureTheory.volume.restrict Work.Diff.STE.unitCube) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous_cplx
      ((Work.Diff.STE.continuous_fourierExp (-k)).mul hu)
  have h2 : MeasureTheory.Integrable
      (fun x : ι → ℝ => Work.Diff.STE.fourierExp (-k) x * v x)
      (MeasureTheory.volume.restrict Work.Diff.STE.unitCube) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous_cplx
      ((Work.Diff.STE.continuous_fourierExp (-k)).mul hv)
  simp only [Work.Diff.STE.fourierCoeff, Pi.add_apply]
  rw [show (fun x : ι → ℝ => Work.Diff.STE.fourierExp (-k) x * (u x + v x))
      = fun x : ι → ℝ => Work.Diff.STE.fourierExp (-k) x * u x
          + Work.Diff.STE.fourierExp (-k) x * v x from
    funext fun x => mul_add _ _ _]
  exact MeasureTheory.integral_add h1 h2

/-! ## 3. The flat symbol `flatLam m = Σᵢ (2π mᵢ)²` is a weight `⟨m⟩ = wt m` of degree one -/

private lemma flatLamNonneg {ι : Type*} [Fintype ι] (k : ι → ℤ) :
    0 ≤ Work.Diff.STE.B3.SymCalc.flatLam k := by
  simp only [Work.Diff.STE.B3.SymCalc.flatLam]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

private lemma flatLam_le_wt' {ι : Type*} [Fintype ι] (k : ι → ℤ) :
    Work.Diff.STE.B3.SymCalc.flatLam k ≤ (4 * Real.pi ^ 2) * Work.Diff.STE.wt k := by
  have hsum : ∑ i, ((k i : ℝ)) ^ 2 ≤ Work.Diff.STE.wt k := by
    have h1 : (0 : ℝ) ≤ ∑ i, (((k i : ℤ)) : ℝ) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    simp only [Work.Diff.STE.wt]
    linarith
  calc Work.Diff.STE.B3.SymCalc.flatLam k
      = ∑ i, (2 * Real.pi * (k i : ℝ)) ^ 2 := rfl
    _ = (4 * Real.pi ^ 2) * ∑ i, ((k i : ℝ)) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ (4 * Real.pi ^ 2) * Work.Diff.STE.wt k :=
        mul_le_mul_of_nonneg_left hsum (by positivity)

private lemma normFlatLamPow {ι : Type*} [Fintype ι] (j : ℕ) (k : ι → ℤ) :
    ‖((((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ)) : ℂ)‖
      = (Work.Diff.STE.B3.SymCalc.flatLam k) ^ j := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (flatLamNonneg k) j)]

private lemma normFlatLamPow_le {ι : Type*} [Fintype ι] (j : ℕ) (k : ι → ℤ) :
    ‖((((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ)) : ℂ)‖
      ≤ (4 * Real.pi ^ 2) ^ j * (Work.Diff.STE.wt k) ^ j := by
  calc ‖((((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ)) : ℂ)‖
      = (Work.Diff.STE.B3.SymCalc.flatLam k) ^ j := normFlatLamPow j k
    _ ≤ ((4 * Real.pi ^ 2) * Work.Diff.STE.wt k) ^ j :=
        pow_le_pow_left₀ (flatLamNonneg k) (flatLam_le_wt' k) j
    _ = (4 * Real.pi ^ 2) ^ j * (Work.Diff.STE.wt k) ^ j := by rw [mul_pow]

/-! ## 4. The multiplier family `k ↦ (flatLam k)^j · û(k)` is `ℓ¹`-summable -/

/-- **Rapid decay of the LapLacian-power coefficients.**  For smooth `1`-periodic `w` the family
`k ↦ ‖(flatLam k)^j · û(k)‖` is summable, so the Fourier series defining `Λ^j w` converges
absolutely.  Proof: `summable_weighted_fourierCoeff_of_contDiff` provides the weighted `ℓ²`
summability at weight `⟨k⟩^{s + 2j}`, `(flatLam k)^j ≤ (4π²⟨k⟩)^j` transfers it to
`Σ_k ⟨k⟩^s ‖(flatLam k)^j û(k)‖²`, and `summable_norm_of_CSq` (with `2s > card ι`) converts that
into `ℓ¹` summability. -/
private lemma summable_lapCoeff {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ℕ)
    (w : (ι → ℝ) → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hper : Work.Diff.STE.Periodic1 w) :
    Summable (fun k : ι → ℤ =>
      ‖((((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ)) : ℂ)
        * Work.Diff.STE.fourierCoeff w k‖) := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : ℕ, Fintype.card ι < 2 * s := ⟨Fintype.card ι + 1, by omega⟩
  set C : ℝ := (4 * Real.pi ^ 2) ^ (2 * j) with hC
  have hbase : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (s + 2 * j)
      * ‖Work.Diff.STE.fourierCoeff w k‖ ^ 2) :=
    Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff w hw hper (s + 2 * j)
  have hpt : ∀ k : ι → ℤ, (Work.Diff.STE.wt k) ^ s
      * ‖((((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ)) : ℂ)
          * Work.Diff.STE.fourierCoeff w k‖ ^ 2
      ≤ C * ((Work.Diff.STE.wt k) ^ (s + 2 * j)
          * ‖Work.Diff.STE.fourierCoeff w k‖ ^ 2) := by
    intro k
    rw [norm_mul, mul_pow]
    have h1 : ‖((((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ)) : ℂ)‖ ^ 2
        ≤ ((4 * Real.pi ^ 2) ^ j * (Work.Diff.STE.wt k) ^ j) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (normFlatLamPow_le j k) 2
    have h2 : ((4 * Real.pi ^ 2) ^ j * (Work.Diff.STE.wt k) ^ j) ^ 2
        = (4 * Real.pi ^ 2) ^ (2 * j) * (Work.Diff.STE.wt k) ^ (2 * j) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm j 2]
    calc (Work.Diff.STE.wt k) ^ s
          * (‖((((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ)) : ℂ)‖ ^ 2
            * ‖Work.Diff.STE.fourierCoeff w k‖ ^ 2)
        ≤ (Work.Diff.STE.wt k) ^ s
            * (((4 * Real.pi ^ 2) ^ j * (Work.Diff.STE.wt k) ^ j) ^ 2
              * ‖Work.Diff.STE.fourierCoeff w k‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Work.Diff.STE.wt_pos k).le s)
          exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = (Work.Diff.STE.wt k) ^ s
            * (((4 * Real.pi ^ 2) ^ (2 * j) * (Work.Diff.STE.wt k) ^ (2 * j))
              * ‖Work.Diff.STE.fourierCoeff w k‖ ^ 2) := by rw [h2]
      _ = C * ((Work.Diff.STE.wt k) ^ (s + 2 * j)
            * ‖Work.Diff.STE.fourierCoeff w k‖ ^ 2) := by
          rw [hC, pow_add]; ring
  refine Work.Diff.STE.summable_norm_of_CSq s hs _ ?_
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos k).le s) (sq_nonneg _))
    hpt (hbase.mul_left C)

/-! ## 5. Fourier inversion for `Λ^j`: the multiplier acts on the coefficients -/

private lemma fourierCoeff_lapPow {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ℕ)
    (w : (ι → ℝ) → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hper : Work.Diff.STE.Periodic1 w)
    (k : ι → ℤ) :
    Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalcStep5.lapPow j w) k
      = (((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ) : ℂ)
        * Work.Diff.STE.fourierCoeff w k :=
  Work.Diff.STE.flat.fourierCoeff_seriesFun _ (summable_lapCoeff j w hw hper) k

/-! ## 6. The algebra -/

theorem lapPow_algebra
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (∀ (i j : ℕ) (w : (ι → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) w → Work.Diff.STE.Periodic1 w →
      Work.Diff.STE.B3.SymCalcStep5.lapPow i (Work.Diff.STE.B3.SymCalcStep5.lapPow j w)
        = Work.Diff.STE.B3.SymCalcStep5.lapPow (i + j) w)
    ∧ (∀ (j : ℕ) (u v : (ι → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) u → ContDiff ℝ (⊤ : ℕ∞) v →
      Work.Diff.STE.Periodic1 u → Work.Diff.STE.Periodic1 v →
      Work.Diff.STE.B3.SymCalcStep5.lapPow j (u + v)
        = Work.Diff.STE.B3.SymCalcStep5.lapPow j u
          + Work.Diff.STE.B3.SymCalcStep5.lapPow j v) := by
  constructor
  · intro i j w hw hper
    have hfj : ∀ k : ι → ℤ,
        Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalcStep5.lapPow j w) k
          = (((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ) : ℂ)
            * Work.Diff.STE.fourierCoeff w k := fourierCoeff_lapPow j w hw hper
    calc Work.Diff.STE.B3.SymCalcStep5.lapPow i (Work.Diff.STE.B3.SymCalcStep5.lapPow j w)
        = Work.Diff.STE.seriesFun (fun k : ι → ℤ =>
            (((Work.Diff.STE.B3.SymCalc.flatLam k) ^ i : ℝ) : ℂ)
              * Work.Diff.STE.fourierCoeff
                  (Work.Diff.STE.B3.SymCalcStep5.lapPow j w) k) := rfl
      _ = Work.Diff.STE.seriesFun (fun k : ι → ℤ =>
            (((Work.Diff.STE.B3.SymCalc.flatLam k) ^ i : ℝ) : ℂ)
              * ((((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ) : ℂ)
                * Work.Diff.STE.fourierCoeff w k)) :=
          seriesFun_congr' (fun k => by rw [hfj k])
      _ = Work.Diff.STE.seriesFun (fun k : ι → ℤ =>
            (((Work.Diff.STE.B3.SymCalc.flatLam k) ^ (i + j) : ℝ) : ℂ)
              * Work.Diff.STE.fourierCoeff w k) :=
          seriesFun_congr' (fun k => by
            push_cast
            rw [← mul_assoc, ← pow_add])
      _ = Work.Diff.STE.B3.SymCalcStep5.lapPow (i + j) w := rfl
  · intro j u v hu hv hpu hpv
    have hsum : ∀ k : ι → ℤ, Work.Diff.STE.fourierCoeff (u + v) k
        = Work.Diff.STE.fourierCoeff u k + Work.Diff.STE.fourierCoeff v k :=
      fun k => fourierCoeff_add_c u v hu.continuous hv.continuous k
    have hu' := summable_lapCoeff j u hu hpu
    have hv' := summable_lapCoeff j v hv hpv
    calc Work.Diff.STE.B3.SymCalcStep5.lapPow j (u + v)
        = Work.Diff.STE.seriesFun (fun k : ι → ℤ =>
            (((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ) : ℂ)
              * Work.Diff.STE.fourierCoeff (u + v) k) := rfl
      _ = Work.Diff.STE.seriesFun (fun k : ι → ℤ =>
            (((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ) : ℂ)
              * Work.Diff.STE.fourierCoeff u k
            + (((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ) : ℂ)
              * Work.Diff.STE.fourierCoeff v k) :=
          seriesFun_congr' (fun k => by rw [hsum k]; ring)
      _ = Work.Diff.STE.seriesFun (fun k : ι → ℤ =>
            (((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ) : ℂ)
              * Work.Diff.STE.fourierCoeff u k)
          + Work.Diff.STE.seriesFun (fun k : ι → ℤ =>
            (((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ) : ℂ)
              * Work.Diff.STE.fourierCoeff v k) :=
          seriesFun_add' hu' hv'
      _ = Work.Diff.STE.B3.SymCalcStep5.lapPow j u
          + Work.Diff.STE.B3.SymCalcStep5.lapPow j v := rfl

end Work.Diff.STE.B3.SymCalcStep6
