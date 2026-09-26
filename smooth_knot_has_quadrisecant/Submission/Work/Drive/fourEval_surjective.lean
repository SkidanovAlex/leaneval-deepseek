import Mathlib
import Submission.Work.Drive.qwDefs

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-! ## The scalar four-point independence

We adapt the argument of `Work.Drive.trigBasis_five_independent` to four parameters.  With
`z i = exp (t i * I)` the four real equations of frequency `k` (`k = 0, 1, 2, 3`) supply the
complex moments `∑ i, α i * (z i) ^ k = 0`; the Vandermonde determinant then forces `α = 0`. -/

private lemma trigBasis_zero (t : ℝ) : trigBasis 0 t = 1 := rfl

private lemma trigBasis_one (t : ℝ) : trigBasis 1 t = Real.cos t := rfl

private lemma trigBasis_two (t : ℝ) : trigBasis 2 t = Real.sin t := rfl

private lemma trigBasis_three (t : ℝ) : trigBasis 3 t = Real.cos (2 * t) := rfl

private lemma trigBasis_four (t : ℝ) : trigBasis 4 t = Real.sin (2 * t) := rfl

private lemma trigBasis_five (t : ℝ) : trigBasis 5 t = Real.cos (3 * t) := rfl

private lemma trigBasis_six (t : ℝ) : trigBasis 6 t = Real.sin (3 * t) := rfl

private lemma period_eq_two_pi : period = 2 * Real.pi := rfl

/-- Real equations for the frequency `k` give the complex equation `∑ αᵢ zᵢ^k = 0`, where
`zᵢ = exp (wᵢ * I)`. -/
private lemma sum_exp_pow_zero (w : Fin 4 → ℝ) (α : Fin 4 → ℝ) (k : ℕ)
    (hc : ∑ i, α i * Real.cos (k * w i) = 0)
    (hs : ∑ i, α i * Real.sin (k * w i) = 0) :
    ∑ i, (α i : ℂ) * (Complex.exp ((w i : ℂ) * Complex.I)) ^ k = 0 := by
  have hterm : ∀ i : Fin 4, (α i : ℂ) * (Complex.exp ((w i : ℂ) * Complex.I)) ^ k
      = ((α i * Real.cos (k * w i) : ℝ) : ℂ)
        + ((α i * Real.sin (k * w i) : ℝ) : ℂ) * Complex.I := by
    intro i
    have e1 : Complex.exp ((w i : ℂ) * Complex.I) ^ k
        = Complex.exp ((k : ℂ) * ((w i : ℂ) * Complex.I)) :=
      (Complex.exp_nat_mul ((w i : ℂ) * Complex.I) k).symm
    have e2 : (k : ℂ) * ((w i : ℂ) * Complex.I) = ((k * w i : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e1, e2, Complex.exp_ofReal_mul_I]
    push_cast
    ring
  calc ∑ i, (α i : ℂ) * (Complex.exp ((w i : ℂ) * Complex.I)) ^ k
      = ∑ i, (((α i * Real.cos (k * w i) : ℝ) : ℂ)
          + ((α i * Real.sin (k * w i) : ℝ) : ℂ) * Complex.I) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = ((∑ i, α i * Real.cos (k * w i) : ℝ) : ℂ)
        + ((∑ i, α i * Real.sin (k * w i) : ℝ) : ℂ) * Complex.I := by
        rw [Finset.sum_add_distrib, ← Complex.ofReal_sum, ← Finset.sum_mul, ← Complex.ofReal_sum]
    _ = 0 := by rw [hc, hs]; simp

/-- **Four value functionals of the trigonometric basis are independent.**  If four parameters are
pairwise distinct modulo the period, a relation `∑ i, α i * trigBasis j (t i) = 0` for all
`j : Fin 9` forces `α = 0`.  (The frequencies `0 … 3`, i.e. the rows `0 … 6`, suffice.) -/
private theorem fourTrig_independent {t : Fin 4 → ℝ}
    (hsep : ∀ i j : Fin 4, i ≠ j → ∀ m : ℤ, t i - t j ≠ (m : ℝ) * period)
    (α : Fin 4 → ℝ)
    (h : ∀ j : Fin 9, ∑ i : Fin 4, α i * trigBasis j (t i) = 0) : α = 0 := by
  classical
  set z : Fin 4 → ℂ := fun i => Complex.exp ((t i : ℂ) * Complex.I) with hzdef
  have hz : ∀ i : Fin 4, z i = Complex.exp ((t i : ℂ) * Complex.I) := fun i => by rw [hzdef]
  have hzinj : Function.Injective z := by
    intro i j hij
    by_contra hne
    rw [hz i, hz j] at hij
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hij
    have h3 : (t i : ℂ) = (t j : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ)) := by
      have h4 : (t i : ℂ) * Complex.I = ((t j : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
        rw [hn]; ring
      exact mul_right_cancel₀ Complex.I_ne_zero h4
    have h5 : t i = t j + (n : ℝ) * (2 * Real.pi) := by
      have h6 : ((t i : ℂ)) = ((t j + (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
        push_cast
        exact h3
      exact Complex.ofReal_inj.mp h6
    have h7 : t i - t j = (n : ℝ) * period := by
      rw [period_eq_two_pi]; linarith
    exact hsep i j hne n h7
  -- the real equations of frequencies `0, 1, 2, 3`
  have hc0 : ∑ i : Fin 4, α i * Real.cos (((0 : ℕ) : ℝ) * t i) = 0 := by
    simpa [trigBasis_zero] using h 0
  have hs0 : ∑ i : Fin 4, α i * Real.sin (((0 : ℕ) : ℝ) * t i) = 0 := by simp
  have hc1 : ∑ i : Fin 4, α i * Real.cos (((1 : ℕ) : ℝ) * t i) = 0 := by
    simpa [trigBasis_one] using h 1
  have hs1 : ∑ i : Fin 4, α i * Real.sin (((1 : ℕ) : ℝ) * t i) = 0 := by
    simpa [trigBasis_two] using h 2
  have hc2 : ∑ i : Fin 4, α i * Real.cos (((2 : ℕ) : ℝ) * t i) = 0 := by
    simpa [trigBasis_three] using h 3
  have hs2 : ∑ i : Fin 4, α i * Real.sin (((2 : ℕ) : ℝ) * t i) = 0 := by
    simpa [trigBasis_four] using h 4
  have hc3 : ∑ i : Fin 4, α i * Real.cos (((3 : ℕ) : ℝ) * t i) = 0 := by
    simpa [trigBasis_five] using h 5
  have hs3 : ∑ i : Fin 4, α i * Real.sin (((3 : ℕ) : ℝ) * t i) = 0 := by
    simpa [trigBasis_six] using h 6
  -- the complex moments `0, 1, 2, 3`
  have hmom : ∀ m : Fin 4, ∑ i : Fin 4, (α i : ℂ) * (z i) ^ (m : ℕ) = 0 := by
    intro m
    fin_cases m
    · have hh := sum_exp_pow_zero t α 0 hc0 hs0
      simpa [hz] using hh
    · have hh := sum_exp_pow_zero t α 1 hc1 hs1
      simpa [hz] using hh
    · have hh := sum_exp_pow_zero t α 2 hc2 hs2
      simpa [hz] using hh
    · have hh := sum_exp_pow_zero t α 3 hc3 hs3
      simpa [hz] using hh
  -- Vandermonde
  have hmat : Matrix.mulVec (Matrix.transpose (Matrix.vandermonde z)) (fun i => (α i : ℂ)) = 0 := by
    funext m
    simpa [Matrix.mulVec, dotProduct, Matrix.vandermonde, mul_comm] using hmom m
  have hzdet : (Matrix.vandermonde z).det ≠ 0 := by
    rw [Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    rw [sub_ne_zero]
    intro hji
    exact absurd (hzinj hji).symm (ne_of_lt (Finset.mem_Ioi.mp hj))
  have hdet : (Matrix.transpose (Matrix.vandermonde z)).det ≠ 0 := by
    rw [Matrix.det_transpose]; exact hzdet
  have hunit : IsUnit (Matrix.transpose (Matrix.vandermonde z)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hαzero : (fun i => (α i : ℂ)) = 0 :=
    (Matrix.mulVec_injective_of_isUnit hunit) (by rw [hmat, Matrix.mulVec_zero])
  funext i
  exact Complex.ofReal_eq_zero.mp (congrFun hαzero i)

/-- The evaluation of `linSum` at a coefficient vector: it is the value of the trigonometric
polynomial at the given parameter. -/
private lemma linSum_eq_coeff (τ : QP) (dc : Coeff) (i : Fin 4) :
    linSum (fun j : Fin 9 => trigBasis j (qtp τ i)) dc
      = ∑ j : Fin 9, trigBasis j (qtp τ i) • dc j := by
  rw [linSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeffProj_apply]
  rfl

/-- **The homomorphism on the product space is surjective.**  This is the vector-valued form of
the independence of the four evaluation functionals `fourTrig_independent`: test a linear functional
`φ` vanishing on the range against the four coordinates `φ ∘ proj i`. -/
private theorem fourTrig_surj_aux (τ : QP)
    (hsep : ∀ i j : Fin 4, i ≠ j → ∀ m : ℤ, qtp τ i - qtp τ j ≠ (m : ℝ) * period) :
    Function.Surjective (fun d : Fin 9 → Space => fun i : Fin 4 =>
      ∑ j : Fin 9, trigBasis j (qtp τ i) • d j) := by
  classical
  -- the bundled linear map
  let Θ : (Fin 9 → Space) →ₗ[ℝ] (Fin 4 → Space) :=
    LinearMap.pi fun i : Fin 4 =>
      ∑ j : Fin 9, (trigBasis j (qtp τ i)) • (LinearMap.proj j : (Fin 9 → Space) →ₗ[ℝ] Space)
  have hΘ : ∀ d : Fin 9 → Space,
      Θ d = fun i : Fin 4 => ∑ j : Fin 9, trigBasis j (qtp τ i) • d j := by
    intro d; funext i
    simp only [Θ, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply]
  have hsingle : ∀ (j : Fin 9) (v : Space) (i : Fin 4),
      ∑ j' : Fin 9, trigBasis j' (qtp τ i) • (Pi.single j v : Fin 9 → Space) j'
        = trigBasis j (qtp τ i) • v := by
    intro j v i
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb]; simp
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have hΘsurj : Function.Surjective Θ := by
    rw [← LinearMap.range_eq_top, ← Submodule.dualAnnihilator_eq_bot_iff, Submodule.eq_bot_iff]
    intro φ hφmem
    have hφ : ∀ w ∈ LinearMap.range Θ, φ w = 0 := (Submodule.mem_dualAnnihilator φ).mp hφmem
    have hdecomp : φ = ∑ i : Fin 4,
        (φ.comp (LinearMap.single ℝ (fun _ : Fin 4 => Space) i)).comp
          (LinearMap.proj i : (Fin 4 → Space) →ₗ[ℝ] Space) := by
      refine LinearMap.pi_ext fun i v => ?_
      rw [LinearMap.sum_apply, Finset.sum_eq_single i]
      · simp [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply]
      · intro b _ hb
        have hb' : (LinearMap.proj b : (Fin 4 → Space) →ₗ[ℝ] Space) (Pi.single i v) = 0 := by
          rw [LinearMap.proj_apply, Pi.single_eq_of_ne hb]
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hb', map_zero, map_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    have hφeval : ∀ z : Fin 4 → Space, φ z = ∑ i : Fin 4,
        (φ.comp (LinearMap.single ℝ (fun _ : Fin 4 => Space) i)) (z i) := by
      intro z
      have h := congrArg (fun g : (Fin 4 → Space) →ₗ[ℝ] ℝ => g z) hdecomp
      simpa [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply] using h
    have key : ∀ (v : Space) (j : Fin 9),
        ∑ i : Fin 4, (φ.comp (LinearMap.single ℝ (fun _ : Fin 4 => Space) i)) v
          * trigBasis j (qtp τ i) = 0 := by
      intro v j
      have hmem : Θ (Pi.single j v) ∈ LinearMap.range Θ := LinearMap.mem_range.mpr ⟨_, rfl⟩
      have h0 : φ (Θ (Pi.single j v)) = 0 := hφ _ hmem
      have hz : Θ (Pi.single j v) = fun i : Fin 4 => trigBasis j (qtp τ i) • v := by
        rw [hΘ]; funext i; exact hsingle j v i
      rw [hz] at h0
      rw [hφeval] at h0
      have h1 : ∑ i : Fin 4, trigBasis j (qtp τ i)
          * (φ.comp (LinearMap.single ℝ (fun _ : Fin 4 => Space) i)) v = 0 := by
        simpa [LinearMap.comp_apply, map_smul, smul_eq_mul, Pi.single_smul] using h0
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hfam0 : ∀ i : Fin 4,
        (φ.comp (LinearMap.single ℝ (fun _ : Fin 4 => Space) i)) = 0 := by
      intro i
      ext v
      have h := fourTrig_independent hsep
        (fun i' => (φ.comp (LinearMap.single ℝ (fun _ : Fin 4 => Space) i')) v)
        (fun j => key v j)
      exact congrFun h i
    have hzero : (∑ i : Fin 4,
        (φ.comp (LinearMap.single ℝ (fun _ : Fin 4 => Space) i)).comp
          (LinearMap.proj i : (Fin 4 → Space) →ₗ[ℝ] Space)) = 0 := by
      simp [hfam0]
    exact hdecomp.trans hzero
  have hplain : Function.Surjective (fun d : Fin 9 → Space => fun i : Fin 4 =>
      ∑ j : Fin 9, trigBasis j (qtp τ i) • d j) := fun y => by
    obtain ⟨d, hd⟩ := hΘsurj y
    exact ⟨d, (hΘ d).symm.trans hd⟩
  exact hplain

open Work.Drive LeanEval.KnotTheory.Quadrisecant in
/-- **The four value functionals of the perturbation family are surjective at separated windows.**

If the four parameters `qA τ, qZ τ, qW τ, qB τ` of a window are distinct modulo the period `2π`
(`hsep`), then the linear map sending a coefficient direction `dc` to the four induced changes of
the perturbation `perturbCorr` at those parameters is surjective onto `(Fin 4 → Space)`.

This is the `hsurj` hypothesis of the rank lemmas: a four-point instance of the
Vandermonde/trigonometric independence already used by
`Work.Drive.trigBasis_five_independent` (`Submission/Work/Drive/trigBasis_five_independent.lean`):
a relation `∑ i, α i * trigBasis j (t i) = 0` for all `j : Fin 9` with four distinct parameters
forces `α = 0` (test against the frequencies `0, 1, 2, 3` and use the Vandermonde determinant in
`z i = exp (t i * I)`; note the rows `0 … 6` already suffice). -/
theorem fourEval_surjective {τ : QP}
    (hsep : ∀ i j : Fin 4, i ≠ j → ∀ m : ℤ, qtp τ i - qtp τ j ≠ (m : ℝ) * period) :
    Function.Surjective fun dc : Coeff => fun i : Fin 4 =>
      (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc := by
  intro y
  obtain ⟨d, hd⟩ := fourTrig_surj_aux τ hsep y
  refine ⟨eCoeff.symm d, ?_⟩
  have h1 : (fun i : Fin 4 => linSum (fun j : Fin 9 => trigBasis j (qtp τ i)) (eCoeff.symm d))
      = fun i : Fin 4 => ∑ j : Fin 9, trigBasis j (qtp τ i) • d j := by
    funext i
    rw [linSum_eq_coeff τ (eCoeff.symm d) i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (eCoeff.symm d) j = d j from rfl]
  show (fun i : Fin 4 => linSum (fun j : Fin 9 => trigBasis j (qtp τ i)) (eCoeff.symm d)) = y
  rw [h1]
  exact hd

end

end Work.Drive
