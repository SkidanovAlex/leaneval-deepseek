import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation
import Submission.Work.BourgainPlan.Maximal.poly_block_defs
import Submission.Work.Analysis.ExponentialSums.model721_bundle

/-!
# The general-`P` window model of Bourgain §7.2 (Lemma 7.20) — vocabulary

This file fixes the objects used in the proof of
`Work.BourgainPlan.Maximal.polyGeneral_window_maximal_lp`.

For `N = 2^k`, a modulus `q ≥ 1`, a window width parameter `D ≥ q`, a bump `φ`, a finitely
supported `g : ℤ → ℂ` (support `s`) the §7.2 model reads

`genWindow P k q D φ g s m = Σ_{a<q} ∫_{|β| ≤ 1/(2D)} ĝ(a/q+β) · conj(Φ_N(β)) · φ(Dβ) · e(m(a/q+β)) dβ`

where `Φ_N(β) = polyProfile P N β = ∫_0^1 e(β P(N t)) dt` is the oscillatory profile.

The residue identity `Σ_{a<q} e((j+m)a/q) = q [q ∣ j+m]` collapses the `a`-sum, and for
`m = y q + z`, `0 ≤ z < q` the operator becomes (in the `β`-variable, after the substitution
`γ = q β`) the `q`-multiple inverse transform

`genBlock P k q D φ g s z y = q · ∫_β genBetaAmp(β) conj(Φ_N(β)) e(q y β) dβ`

of the amplitude `genBetaAmp(β) = φ(Dβ) Σ_{j ≡ -z (q)} g_j e((j+z)β)`.  The family `genBlock k`
is band-limited to `[-q/(2D), q/(2D)] ⊆ [-1/2, 1/2]`, which is what lets `§7.1` (`poly_dilation_lp`)
be applied on the `ℤ`-lattice.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Work.BourgainPlan.Maximal

/-- The `z`-slice amplitude of the model in the `β`-variable:
`φ(Dβ) · Σ_{j ≡ -z mod q} g_j e((j+z)β)`. -/
noncomputable def genBetaAmp (q : ℕ) (D : ℝ) (φ : ℝ → ℂ) (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ)
    (β : ℝ) : ℂ :=
  φ (D * β) * ∑ j ∈ s.filter (fun j => (q : ℤ) ∣ (z + j)),
    g j * Complex.exp (2 * Real.pi * Complex.I * (((j : ℂ) + (z : ℂ)) * (β : ℂ)))

/-- The full amplitude of the `k`-th block: the slice amplitude times the conjugated profile. -/
noncomputable def genAmpF (P : Polynomial ℤ) (k : ℕ) (q : ℕ) (D : ℝ) (φ : ℝ → ℂ) (g : ℤ → ℂ)
    (s : Finset ℤ) (z : ℤ) (β : ℝ) : ℂ :=
  genBetaAmp q D φ g s z β * starRingEnd ℂ (polyProfile P (2 ^ k) β)

/-- The `k`-th block of the `z`-slice: `q · 𝓕⁻(genAmpF)(q x)`. -/
noncomputable def genBlock (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ) (g : ℤ → ℂ)
    (s : Finset ℤ) (z : ℤ) (x : ℝ) : ℂ :=
  (q : ℂ) * FourierTransformInv.fourierInv (genAmpF P k q D φ g s z) ((q : ℝ) * x)

/-- The window model of Bourgain (7.21) at scale `N = 2^k` (the expression appearing in
`polyGeneral_window_maximal_lp`). -/
noncomputable def genWindow (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ) (g : ℤ → ℂ)
    (s : Finset ℤ) (m : ℤ) : ℂ :=
  ∑ a ∈ Finset.range q,
    ∫ β in (-(1 / (2 * D)))..(1 / (2 * D)),
      (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) *
          ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ))))
      * (∫ t in (0 : ℝ)..1, Complex.exp (-(2 * Real.pi * Complex.I *
          (((β : ℝ) * (P.map (Int.castRingHom ℝ)).eval (((2 : ℝ) ^ k) * t) : ℝ) : ℂ))))
      * φ (D * β)
      * Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) *
          ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ)))

/-! ## Elementary support facts -/

/-- The bump vanishes outside the window: if `|β| > 1/(2D)` then `φ (D β) = 0`. -/
lemma phi_dilate_eq_zero {D : ℝ} (hD : 0 < D) {φ : ℝ → ℂ}
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    {β : ℝ} (hβ : β ∉ Set.Icc (-(1/(2*D))) (1/(2*D))) : φ (D * β) = 0 := by
  have hD2 : (0:ℝ) < 2 * D := by linarith
  have hout : D * β < -(1/2) ∨ (1/2) < D * β := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hβ
    rcases hβ with h | h
    · left
      have hh : β * (2*D) < -1 := by
        have hm := mul_lt_mul_of_pos_right h hD2
        rwa [neg_mul, div_mul_cancel₀ 1 (ne_of_gt hD2)] at hm
      nlinarith [hh]
    · right
      have hh : 1 < β * (2*D) := by
        have hm := mul_lt_mul_of_pos_right h hD2
        rwa [div_mul_cancel₀ 1 (ne_of_gt hD2)] at hm
      nlinarith [hh]
  apply hφs
  intro hmem
  rw [Set.mem_Icc] at hmem
  rcases hout with h | h
  · linarith [hmem.1]
  · linarith [hmem.2]

/-- The slice amplitude vanishes outside the window `|β| ≤ 1/(2D)`. -/
lemma genBetaAmp_eq_zero_of_notMem (q : ℕ) {D : ℝ} (hD : 0 < D) {φ : ℝ → ℂ}
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) {β : ℝ}
    (hβ : β ∉ Set.Icc (-(1/(2*D))) (1/(2*D))) : genBetaAmp q D φ g s z β = 0 := by
  rw [genBetaAmp, phi_dilate_eq_zero hD hφs hβ, zero_mul]

/-- Continuity of the slice amplitude. -/
lemma continuous_genBetaAmp (q : ℕ) (D : ℝ) {φ : ℝ → ℂ} (hφ : Continuous φ) (g : ℤ → ℂ)
    (s : Finset ℤ) (z : ℤ) : Continuous (genBetaAmp q D φ g s z) := by
  unfold genBetaAmp
  refine Continuous.mul (hφ.comp (by fun_prop)) ?_
  refine continuous_finsetSum _ (fun j _ => ?_)
  exact continuous_const.mul (by fun_prop)

/-- Continuity of the conjugated profile composed with a real rescaling. -/
lemma continuous_conj_polyProfile (P : Polynomial ℤ) (N : ℕ) :
    Continuous (fun β : ℝ => starRingEnd ℂ (polyProfile P N β)) :=
  Complex.continuous_conj.comp (continuous_polyProfile P N)

/-- The amplitude of the `k`-th block is continuous. -/
lemma continuous_genAmpF (P : Polynomial ℤ) (k : ℕ) (q : ℕ) (D : ℝ) {φ : ℝ → ℂ}
    (hφ : Continuous φ) (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    Continuous (genAmpF P k q D φ g s z) :=
  (continuous_genBetaAmp q D hφ g s z).mul (continuous_conj_polyProfile P (2 ^ k))

/-- The window model is `genWindow`.  This is the `rfl`-level identification with the expression
appearing in `polyGeneral_window_maximal_lp`. -/
lemma genWindow_apply (P : Polynomial ℤ) (k q : ℕ) (D : ℝ) (φ : ℝ → ℂ) (g : ℤ → ℂ)
    (s : Finset ℤ) (m : ℤ) : genWindow P k q D φ g s m =
  ∑ a ∈ Finset.range q,
    ∫ β in (-(1 / (2 * D)))..(1 / (2 * D)),
      (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) *
          ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ))))
      * (∫ t in (0 : ℝ)..1, Complex.exp (-(2 * Real.pi * Complex.I *
          (((β : ℝ) * (P.map (Int.castRingHom ℝ)).eval (((2 : ℝ) ^ k) * t) : ℝ) : ℂ))))
      * φ (D * β)
      * Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) *
          ((((a : ℝ) / (q : ℝ)) + β : ℝ) : ℂ))) := rfl

/-- A bound for the polynomial values on the dilation window `(0,1]`. -/
theorem exists_eval_bound_Ioc (P : Polynomial ℤ) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, s ∈ Set.Ioc (0:ℝ) 1 →
      |(toRealPoly P).eval ((N:ℝ)*s)| ≤ M := by
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1),
      |((P.coeff i : ℤ) : ℝ)| * (N:ℝ)^i, by positivity, fun s hs => ?_⟩
  have hs1 : |s| ≤ 1 := by
    rw [abs_of_pos hs.1]
    exact hs.2
  have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hdeg : (toRealPoly P).natDegree ≤ P.natDegree := by
    rw [toRealPoly]
    exact Polynomial.natDegree_map_le
  have heval : (toRealPoly P).eval ((N:ℝ)*s)
      = ∑ i ∈ Finset.range (P.natDegree+1),
          (((P.coeff i : ℤ)) : ℝ) * (((N:ℝ)*s)^i) := by
    rw [Polynomial.eval_eq_sum_range' (p := (toRealPoly P)) (n := P.natDegree + 1)
      (by omega : (toRealPoly P).natDegree < P.natDegree + 1)]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [toRealPoly, Polynomial.coeff_map]
    simp
  calc |(toRealPoly P).eval ((N:ℝ)*s)|
      = |∑ i ∈ Finset.range (P.natDegree+1),
          (((P.coeff i : ℤ)) : ℝ) * (((N:ℝ)*s)^i)| := by rw [heval]
    _ ≤ ∑ i ∈ Finset.range (P.natDegree+1),
          |(((P.coeff i : ℤ)) : ℝ) * (((N:ℝ)*s)^i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (P.natDegree+1),
          |((P.coeff i : ℤ) : ℝ)| * |(N:ℝ)*s|^i := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [abs_mul, abs_pow _ i]
    _ ≤ ∑ i ∈ Finset.range (P.natDegree+1),
          |((P.coeff i : ℤ) : ℝ)| * (N:ℝ)^i := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_mul, abs_of_nonneg hN]
        exact pow_le_pow_left₀ (mul_nonneg hN (abs_nonneg s)) (by nlinarith [hs1, hN]) i

/-- The real-variable dilation maximal function of the slice amplitude along the polynomial values
`P(N s)`: this is the object to which §7.1 (`poly_dilation_lp`) is applied. -/
noncomputable def genDilMax (P : Polynomial ℤ) (q : ℕ) (D : ℝ) (φ : ℝ → ℂ) (g : ℤ → ℂ)
    (s : Finset ℤ) (z : ℤ) (u : ℝ) : ℝ≥0∞ :=
  ⨆ N : ℕ, ∫⁻ t in Set.Ioc (0:ℝ) 1,
    ‖FourierTransformInv.fourierInv (genBetaAmp q D φ g s z)
      (u - (toRealPoly P).eval ((N:ℝ)*t))‖ₑ

end Work.BourgainPlan.Maximal
