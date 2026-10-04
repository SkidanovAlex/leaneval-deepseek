/-
# `Work.Diff.STE.flat.pairing_zero_le`

The zeroth-order pairing bound of the multi-level a priori estimate of the flat DeTurck
(Galerkin) system: the `L²` pairing of the DeTurck nonlinearity along the jet of a Fourier series
against the series itself is controlled by the full level-`(s+1)` energy.

## The statement

`∑_{i,j} |L2re (Φ (·, jetM (seriesFunM c)) i j) (seriesFunM c · i j)| ≤ C (1 + ENormSqFull (s+1) u)`,

with a constant `C ≥ 0` that is *uniform* in the Galerkin truncation `N` and in the coefficient
family `c` (it may depend on `n`, `s`, the ellipticity constant `lam`, the energy bound `Bs` and
the sup bound `K` of the lower-order term).  The hypotheses are the box support of `c`, the
level-`s` energy bound `ENormSqFull s u ≤ Bs²`, uniform ellipticity with constant `lam > 0`, the
DeTurck decomposition `Φ (x,(A,L,B)) = secOpFlat A B + Nfun (x,(A,L))` on `det (reMat A) ≠ 0`,
and the uniform bound `‖D^j Nfun‖ ≤ K` (`j ≤ s+1`) at the points
`(x, u x, ∂u x)`, `u = seriesFunM c`.

## The proof

1. **Pointwise bound of the nonlinearity.**  `jetM u x` factors through `jetP c x`, and the
   ellipticity hypothesis makes `det (reMat (u x)) ≠ 0`
   (`det_ne_zero_of_elliptic`), so the DeTurck decomposition applies at every `x`:

   `Φ (x, jetM u x) = secOpFlat (u x) (∂²u) + Nfun (x, jetP c x)`.

   The principal part is estimated by the entrywise sup bounds of the inverse metric
   (`inv_jet_bound`, its first component at `j = 0`, giving `‖G_{ab}‖ ≤ Cinv (1+Bs)`) together
   with the sup bounds of the second derivatives of `seriesFunM c`
   (`jet_sup_le_uniform_level` at level `s+1`, `m = 2`, giving
   `‖∂_a∂_b u_{ij}‖ ≤ Cjet (1 + √(ENormSqFull (s+1) u))` and using that
   `pdVec 2 ![a,b] = ∂_a∂_b`); the lower-order part by the hypothesis
   `‖Nfun (x, jetP c x)‖ ≤ K` (the `j = 0` case of `hKsup`, read off with
   `iteratedFDeriv_zero_apply`).  This yields

   `‖Φ (x, jetM u x) i j‖ ≤ A (1 + √E) + K =: M`,  `E := ENormSqFull (s+1) u`,
   `A := n² Cinv (1+Bs) Cjet`.

2. **Pairing against the series.**  `|L2re f g| ≤ C ∫ ‖g‖` when `‖f‖ ≤ C` pointwise
   (`pairingZero_abs_L2re_le`): the `L¹`–`L²` comparison is applied to the *product* `f · conj g`,
   so that the only measurability hypothesis is on that product — if it fails, the Bochner
   integral is `0` by definition and the bound is trivial, and if it holds the product is
   dominated by `C ‖g‖`.  (This is why no smoothness of `Nfun` is needed.)

3. **The `L¹`–`L²` comparison on the unit cube.**  `∫ ‖g‖ ≤ √(∫ ‖g‖²)`
   (`pairingZero_integral_norm_le_sqrt`), from Cauchy–Schwarz (`L2re_abs_le_sqrt`) for the pair
   `(1, ‖g‖)` and the unit volume of the cube.  With `∫ ‖u_{ij}‖² = ENormSq 0 u_{ij} ≤ E`
   (`pairingZero_ENormSq_zero_eq`) this gives `|L2re (Φ∘jet) u_{ij}| ≤ M √E`.

4. **Assembly.**  `M √E = A(1+√E)√E + K√E ≤ (2A + K)(1+E)`, and summing over the `n²` entries
   gives the claim with `C = n² (2A + K)`.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_defs
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.inv_jet_bound_symm
import Submission.Work.Diff.STE.flat.jet_sup_le_uniform_level

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

noncomputable section

/-! ## Elementary measure-theoretic and combinatorial inputs -/

/-- The unit cube has volume `1` (for the restricted measure: total mass `1`). -/
lemma pairingZero_vol_restrict_unitCube {ι : Type*} [Fintype ι] :
    (volume.restrict (Work.Diff.STE.unitCube (ι := ι)) : Measure (ι → ℝ)).real Set.univ = 1 := by
  show ((volume.restrict (Work.Diff.STE.unitCube (ι := ι)) : Measure (ι → ℝ)) Set.univ).toReal = 1
  rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Work.Diff.STE.unitCube, Real.volume_pi_Ioc]
  simp

/-- Squared norm of a real number seen as a complex number. -/
lemma pairingZero_norm_complex_ofReal_sq {ι : Type*} (g : (ι → ℝ) → ℂ) (x : ι → ℝ) :
    ‖(((‖g x‖ : ℝ)) : ℂ)‖ ^ 2 = ‖g x‖ ^ 2 := by
  rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (norm_nonneg _)]

/-- **`L¹`–`L²` comparison on the unit cube.**  `∫ ‖g‖ ≤ √(∫ ‖g‖²)`: this is Cauchy–Schwarz for
the pair `(1, ‖g‖)` (`L2re_abs_le_sqrt`) combined with the unit volume of the cube. -/
lemma pairingZero_integral_norm_le_sqrt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ℝ) → ℂ)
    (hg : Integrable (fun x => ‖g x‖ ^ 2) (volume.restrict (Work.Diff.STE.unitCube (ι := ι)))) :
    ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖
      ≤ Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖ ^ 2) := by
  have hvol := pairingZero_vol_restrict_unitCube (ι := ι)
  have hF : Integrable (fun x : ι → ℝ => ‖(1 : ℂ)‖ ^ 2)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
    simpa using (MeasureTheory.integrable_const (1 : ℝ) :
      Integrable (fun _ : ι → ℝ => (1 : ℝ)) (volume.restrict (Work.Diff.STE.unitCube (ι := ι))))
  have hG : Integrable (fun x : ι → ℝ => ‖(((‖g x‖ : ℝ)) : ℂ)‖ ^ 2)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
    have h2 : (fun x : ι → ℝ => ‖(((‖g x‖ : ℝ)) : ℂ)‖ ^ 2) = fun x => ‖g x‖ ^ 2 :=
      funext fun x => pairingZero_norm_complex_ofReal_sq g x
    rw [h2]; exact hg
  have hcs := Work.Diff.STE.L2re_abs_le_sqrt (fun _ : ι → ℝ => (1 : ℂ))
    (fun x : ι → ℝ => (((‖g x‖ : ℝ)) : ℂ)) hF hG
  have hleft : Work.Diff.STE.L2re (fun _ : ι → ℝ => (1 : ℂ)) (fun x => (((‖g x‖ : ℝ)) : ℂ))
      = ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖ := by
    simp only [Work.Diff.STE.L2re]
    rw [show (fun x : ι → ℝ => (1 : ℂ) * star (((‖g x‖ : ℝ)) : ℂ))
        = fun x => (((‖g x‖ : ℝ)) : ℂ) from funext fun x => by simp]
    rw [show (∫ x in Work.Diff.STE.unitCube (ι := ι), ((‖g x‖ : ℝ) : ℂ))
        = (((∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖) : ℝ) : ℂ) from integral_ofReal]
    rw [Complex.ofReal_re]
  have hright : (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖(((‖g x‖ : ℝ)) : ℂ)‖ ^ 2)
      = ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖ ^ 2 := by
    simp only [pairingZero_norm_complex_ofReal_sq]
  rw [hleft, hright] at hcs
  have hF2 : ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖(1 : ℂ)‖ ^ 2 = 1 := by
    simp only [MeasureTheory.integral_const, hvol, one_smul]
    norm_num
  rw [hF2, Real.sqrt_one, one_mul] at hcs
  exact (abs_le.mp hcs).2

/-- **The `L²` pairing against a pointwise bounded function.**  If `‖f x‖ ≤ C` for all `x` and
`‖g‖` is integrable then `|L2re f g| ≤ C ∫ ‖g‖`.

No hypothesis whatsoever is imposed on `f`: the bound is applied to `f · conj g`, whose
measurability is all that the Bochner integral sees.  If `f · conj g` is *not* a.e. strongly
measurable the integral is `0` by definition (`integral_non_aestronglyMeasurable`), so the bound
is trivial; otherwise `‖f · conj g‖ ≤ C ‖g‖` is integrable and monotonicity of the integral
finishes. -/
lemma pairingZero_abs_L2re_le {ι : Type*} [Fintype ι] [DecidableEq ι] {f g : (ι → ℝ) → ℂ}
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C)
    (hg : Integrable (fun x => ‖g x‖) (volume.restrict (Work.Diff.STE.unitCube (ι := ι)))) :
    |Work.Diff.STE.L2re f g| ≤ C * ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖ := by
  have h1 : |Work.Diff.STE.L2re f g|
      ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖f x * star (g x)‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    have h := MeasureTheory.norm_integral_le_integral_norm
      (μ := volume.restrict (Work.Diff.STE.unitCube (ι := ι)))
      (fun x : ι → ℝ => f x * star (g x))
    simpa only [Work.Diff.STE.L2re, norm_mul, norm_star] using h
  by_cases h : AEStronglyMeasurable (fun x : ι → ℝ => f x * star (g x))
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι)))
  · have hpt : ∀ x : ι → ℝ, ‖f x * star (g x)‖ ≤ C * ‖g x‖ := by
      intro x
      rw [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_right (hf x) (norm_nonneg _)
    have hmeas : AEStronglyMeasurable (fun x : ι → ℝ => ‖f x * star (g x)‖)
        (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := h.norm
    have hint : Integrable (fun x : ι → ℝ => ‖f x * star (g x)‖)
        (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
      MeasureTheory.Integrable.mono' (hg.const_mul C) hmeas
        (Filter.Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hpt x)
    have hle := MeasureTheory.integral_mono_ae hint (hg.const_mul C)
      (Filter.Eventually.of_forall hpt)
    rw [MeasureTheory.integral_const_mul] at hle
    exact h1.trans hle
  · have hz : (∫ x in Work.Diff.STE.unitCube (ι := ι), f x * star (g x)) = 0 :=
      MeasureTheory.integral_non_aestronglyMeasurable h
    have hz' : Work.Diff.STE.L2re f g = 0 := by
      rw [show Work.Diff.STE.L2re f g
        = (∫ x in Work.Diff.STE.unitCube (ι := ι), f x * star (g x)).re from rfl, hz]
      simp
    rw [hz', abs_zero]
    exact mul_nonneg hC (MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x => norm_nonneg _))

/-- The level-`0` energy is the `L²` norm squared: `ENormSq 0 f = ∫_{cube} ‖f‖²`. -/
lemma pairingZero_ENormSq_zero_eq {m : ℕ} (f : (Fin m → ℝ) → ℂ) :
    Work.Diff.STE.ENormSq 0 f = ∫ x in Work.Diff.STE.unitCube (ι := Fin m), ‖f x‖ ^ 2 := by
  rw [Work.Diff.STE.ENormSq]
  rw [Finset.sum_eq_single (fun i : Fin 0 => i.elim0)]
  · simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
  · intro b _ hb; exact absurd (Subsingleton.elim b _) hb
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The two-fold iterated partial derivative along the multi-index `![a,b]` is `∂_a∂_b`. -/
lemma pairingZero_pdVec_two_eq {m : ℕ} (a b : Fin m) (f : (Fin m → ℝ) → ℂ) :
    Work.Diff.STE.pdVec 2 (Fin.cons a (Fin.cons b (fun i : Fin 0 => i.elim0))) f
      = Work.Diff.STE.pd a (Work.Diff.STE.pd b f) := by
  have h1 := Work.Diff.STE.pdVec_cons_eq (ι := Fin m) 1 a
    (Fin.cons b (fun i : Fin 0 => i.elim0)) f
  have h2 := Work.Diff.STE.pdVec_cons_eq (ι := Fin m) 0 b (fun i : Fin 0 => i.elim0) f
  rw [h1, h2]
  simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]

/-! ## The pairing bound -/

theorem pairing_zero_le {n s : ℕ} (hn : 1 ≤ n) (hs : n + 5 ≤ s)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (Nfun : (Fin n → ℝ) × (Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n))
      → Work.Diff.STE.Flat.MatC n)
    (hNdec : ∀ (x : Fin n → ℝ) (A : Work.Diff.STE.Flat.MatC n)
        (L : Fin n → Work.Diff.STE.Flat.MatC n)
        (B : Fin n → Fin n → Work.Diff.STE.Flat.MatC n),
        (Work.Diff.STE.Flat.reMat A).det ≠ 0 →
          Φ (x, (A, L, B)) = Work.Diff.STE.Flat.secOpFlat A B + Nfun (x, (A, L)))
    (lam : ℝ) (hlam : 0 < lam) (Bs : ℝ) (hBs : 0 ≤ Bs)
    (K : ℝ) (hK : 0 ≤ K)
    (hKsup : ∀ (N : ℕ),
      ∀ (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
      Work.Diff.STE.Flat.ENormSqFull s (Work.Diff.STE.Flat.seriesFunM c) ≤ Bs ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
      ∀ (j : ℕ), j ≤ s + 1 → ∀ (x : Fin n → ℝ),
        ‖iteratedFDeriv ℝ j Nfun
          (x, Work.Diff.STE.Flat.seriesFunM c x,
            fun a i j' => Work.Diff.STE.pd a
              (fun y => Work.Diff.STE.Flat.seriesFunM c y i j') x)‖ ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
      Work.Diff.STE.Flat.ENormSqFull s (Work.Diff.STE.Flat.seriesFunM c) ≤ Bs ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
      (∑ i : Fin n, ∑ j : Fin n, |Work.Diff.STE.L2re
          (fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) i j)
          (fun x => Work.Diff.STE.Flat.seriesFunM c x i j)|)
        ≤ C * (1 + Work.Diff.STE.Flat.ENormSqFull (s + 1) (Work.Diff.STE.Flat.seriesFunM c)) := by
  classical
  obtain ⟨Cinv, hCinv0, hCinv⟩ := inv_jet_bound hn hs lam hlam Bs hBs
  obtain ⟨Cjet, hCjet0, hCjet⟩ := jet_sup_le_uniform_level (n := n) (s := s + 1)
  have h2sob1 : 2 + sob n ≤ s + 1 := by
    have h1 : sob n ≤ n + 1 := by
      have h : n / 2 ≤ n := Nat.div_le_self n 2
      simp only [sob]; omega
    omega
  refine ⟨(n : ℝ) * n * (2 * (((n : ℝ) * n) * (Cinv * (1 + Bs)) * Cjet) + K),
    by positivity, ?_⟩
  intro N c hc hen hell
  set E : ℝ := Work.Diff.STE.Flat.ENormSqFull (s + 1) (Work.Diff.STE.Flat.seriesFunM c) with hEdef
  have hEnn : 0 ≤ E := by
    rw [hEdef]; exact ENormSqFull_nonneg _ _
  set A : ℝ := ((n : ℝ) * n) * (Cinv * (1 + Bs)) * Cjet with hAdef
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  set M : ℝ := A * (1 + Real.sqrt E) + K with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  have hmom : ∀ (i j : Fin n) (M' : ℕ),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ M' * ‖c k i j‖) :=
    fun i j M' => summable_moment_box c hc i j M'
  have hcontij : ∀ i j : Fin n, Continuous
      (fun x : Fin n → ℝ => Work.Diff.STE.Flat.seriesFunM c x i j) := by
    intro i j
    have h := Work.Diff.STE.contDiff_seriesFun (c := fun k : Fin n → ℤ => c k i j) (hmom i j)
    simpa only [Work.Diff.STE.Flat.seriesFunM_apply] using h.continuous
  -- the per-entry bound
  have key : ∀ i j : Fin n,
      |Work.Diff.STE.L2re
        (fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) i j)
        (fun x => Work.Diff.STE.Flat.seriesFunM c x i j)| ≤ M * Real.sqrt E := by
    intro i j
    -- pointwise bound of the nonlinearity along the jet
    have hpt : ∀ x : Fin n → ℝ,
        ‖Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) i j‖ ≤ M := by
      intro x
      have hdet : (Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x)).det ≠ 0 :=
        det_ne_zero_of_elliptic _ hlam (hell x)
      have hdec := hNdec x (Work.Diff.STE.Flat.seriesFunM c x)
        (fun a i j' => Work.Diff.STE.pd a (fun y => Work.Diff.STE.Flat.seriesFunM c y i j') x)
        (fun a b i j' => Work.Diff.STE.pd a (Work.Diff.STE.pd b
          (fun z => Work.Diff.STE.Flat.seriesFunM c z i j')) x) hdet
      have hjet : Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x
          = (Work.Diff.STE.Flat.seriesFunM c x,
             (fun a i j' => Work.Diff.STE.pd a
                (fun y => Work.Diff.STE.Flat.seriesFunM c y i j') x),
             (fun a b i j' => Work.Diff.STE.pd a (Work.Diff.STE.pd b
               (fun z => Work.Diff.STE.Flat.seriesFunM c z i j')) x)) := rfl
      have hdecomp : Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x)
          = Work.Diff.STE.Flat.secOpFlat (Work.Diff.STE.Flat.seriesFunM c x)
              (fun a b i j' => Work.Diff.STE.pd a (Work.Diff.STE.pd b
                (fun z => Work.Diff.STE.Flat.seriesFunM c z i j')) x)
            + Nfun (x, (Work.Diff.STE.Flat.seriesFunM c x,
                fun a i j' => Work.Diff.STE.pd a
                  (fun y => Work.Diff.STE.Flat.seriesFunM c y i j') x)) := by
        rw [hjet, hdec]
      -- the principal part
      have hsec : ‖Work.Diff.STE.Flat.secOpFlat (Work.Diff.STE.Flat.seriesFunM c x)
            (fun a b i j' => Work.Diff.STE.pd a (Work.Diff.STE.pd b
              (fun z => Work.Diff.STE.Flat.seriesFunM c z i j')) x) i j‖
          ≤ A * (1 + Real.sqrt E) := by
        have hterm : ∀ a b : Fin n,
            ‖(((Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x))⁻¹) a b : ℂ)
                * Work.Diff.STE.pd a (Work.Diff.STE.pd b
                    (fun z => Work.Diff.STE.Flat.seriesFunM c z i j)) x‖
              ≤ (Cinv * (1 + Bs)) * (Cjet * (1 + Real.sqrt E)) := by
          intro a b
          rw [norm_mul]
          refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
          · have h := (hCinv N c hc hen hell).1 a b 0 (by omega)
              (fun i : Fin 0 => i.elim0) x
            simpa [Work.Diff.STE.pdVec, Work.Diff.STE.pdList] using h
          · have h := hCjet 2 h2sob1 N c hc
              (Fin.cons a (Fin.cons b (fun i : Fin 0 => i.elim0))) i j x
            rwa [pairingZero_pdVec_two_eq] at h
        calc ‖Work.Diff.STE.Flat.secOpFlat (Work.Diff.STE.Flat.seriesFunM c x)
              (fun a b i j' => Work.Diff.STE.pd a (Work.Diff.STE.pd b
                (fun z => Work.Diff.STE.Flat.seriesFunM c z i j')) x) i j‖
            = ‖∑ a : Fin n, ∑ b : Fin n,
                (((Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x))⁻¹) a b : ℂ)
                  * Work.Diff.STE.pd a (Work.Diff.STE.pd b
                      (fun z => Work.Diff.STE.Flat.seriesFunM c z i j)) x‖ := rfl
          _ ≤ ∑ a : Fin n, ‖∑ b : Fin n,
                (((Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x))⁻¹) a b : ℂ)
                  * Work.Diff.STE.pd a (Work.Diff.STE.pd b
                      (fun z => Work.Diff.STE.Flat.seriesFunM c z i j)) x‖ :=
              norm_sum_le _ _
          _ ≤ ∑ a : Fin n, ∑ b : Fin n,
                ‖(((Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x))⁻¹) a b : ℂ)
                  * Work.Diff.STE.pd a (Work.Diff.STE.pd b
                      (fun z => Work.Diff.STE.Flat.seriesFunM c z i j)) x‖ :=
              Finset.sum_le_sum (fun a _ => norm_sum_le _ _)
          _ ≤ ∑ a : Fin n, ∑ b : Fin n,
                (Cinv * (1 + Bs)) * (Cjet * (1 + Real.sqrt E)) :=
              Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hterm a b))
          _ = A * (1 + Real.sqrt E) := by
              rw [hAdef]
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              ring
      -- the lower-order part
      have hN : ‖Nfun (x, (Work.Diff.STE.Flat.seriesFunM c x,
            fun a i j' => Work.Diff.STE.pd a
              (fun y => Work.Diff.STE.Flat.seriesFunM c y i j') x)) i j‖ ≤ K := by
        have h0 := hKsup N c hc hen hell 0 (Nat.zero_le _) x
        have hval : (iteratedFDeriv ℝ 0 Nfun (x, (Work.Diff.STE.Flat.seriesFunM c x,
              fun a i j' => Work.Diff.STE.pd a
                (fun y => Work.Diff.STE.Flat.seriesFunM c y i j') x)))
            (fun _ : Fin 0 => (0 : (Fin n → ℝ) × (Work.Diff.STE.Flat.MatC n ×
              (Fin n → Work.Diff.STE.Flat.MatC n)))) =
            Nfun (x, (Work.Diff.STE.Flat.seriesFunM c x,
              fun a i j' => Work.Diff.STE.pd a
                (fun y => Work.Diff.STE.Flat.seriesFunM c y i j') x)) :=
          iteratedFDeriv_zero_apply _
        have hle : ‖Nfun (x, (Work.Diff.STE.Flat.seriesFunM c x,
              fun a i j' => Work.Diff.STE.pd a
                (fun y => Work.Diff.STE.Flat.seriesFunM c y i j') x))‖
            ≤ ‖iteratedFDeriv ℝ 0 Nfun (x, (Work.Diff.STE.Flat.seriesFunM c x,
              fun a i j' => Work.Diff.STE.pd a
                (fun y => Work.Diff.STE.Flat.seriesFunM c y i j') x))‖ := by
          rw [← hval]
          refine (ContinuousMultilinearMap.le_opNorm _ _).trans_eq ?_
          simp
        exact (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans (hle.trans h0))
      calc ‖Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) i j‖
          = ‖(Work.Diff.STE.Flat.secOpFlat (Work.Diff.STE.Flat.seriesFunM c x)
                (fun a b i j' => Work.Diff.STE.pd a (Work.Diff.STE.pd b
                  (fun z => Work.Diff.STE.Flat.seriesFunM c z i j')) x)
              + Nfun (x, (Work.Diff.STE.Flat.seriesFunM c x,
                  fun a i j' => Work.Diff.STE.pd a
                    (fun y => Work.Diff.STE.Flat.seriesFunM c y i j') x))) i j‖ := by
            rw [hdecomp]
        _ = ‖Work.Diff.STE.Flat.secOpFlat (Work.Diff.STE.Flat.seriesFunM c x)
                (fun a b i j' => Work.Diff.STE.pd a (Work.Diff.STE.pd b
                  (fun z => Work.Diff.STE.Flat.seriesFunM c z i j')) x) i j
              + Nfun (x, (Work.Diff.STE.Flat.seriesFunM c x,
                  fun a i j' => Work.Diff.STE.pd a
                    (fun y => Work.Diff.STE.Flat.seriesFunM c y i j') x)) i j‖ := rfl
        _ ≤ _ := norm_add_le _ _
        _ ≤ A * (1 + Real.sqrt E) + K := add_le_add hsec hN
        _ = M := by rw [hMdef]
    -- integrability of the series entry and of its norm
    have hU : Continuous
        (fun x : Fin n → ℝ => Work.Diff.STE.Flat.seriesFunM c x i j) := hcontij i j
    have hL1 : Integrable (fun x : Fin n → ℝ => ‖Work.Diff.STE.Flat.seriesFunM c x i j‖)
        (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
      Work.Diff.STE.integrableOn_unitCube_of_continuous_real hU.norm
    have hL2 : Integrable (fun x : Fin n → ℝ => ‖Work.Diff.STE.Flat.seriesFunM c x i j‖ ^ 2)
        (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
      Work.Diff.STE.integrableOn_unitCube_of_continuous_real (hU.norm.pow 2)
    have h1 := pairingZero_abs_L2re_le (hC := hMnn)
      (f := fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) i j)
      (g := fun x => Work.Diff.STE.Flat.seriesFunM c x i j) (fun x => hpt x) hL1
    have h2 := pairingZero_integral_norm_le_sqrt
      (fun x : Fin n → ℝ => Work.Diff.STE.Flat.seriesFunM c x i j) hL2
    have hE0 : (∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ‖Work.Diff.STE.Flat.seriesFunM c x i j‖ ^ 2) ≤ E := by
      rw [← pairingZero_ENormSq_zero_eq (fun x => Work.Diff.STE.Flat.seriesFunM c x i j), hEdef]
      exact (ENormSq_le_ENormSqM _ i j).trans (ENormSqM_zero_le_ENormSqFull _ _)
    calc |Work.Diff.STE.L2re
          (fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) i j)
          (fun x => Work.Diff.STE.Flat.seriesFunM c x i j)|
        ≤ M * ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
            ‖Work.Diff.STE.Flat.seriesFunM c x i j‖ := h1
      _ ≤ M * Real.sqrt (∫ x in Work.Diff.STE.unitCube (ι := Fin n),
            ‖Work.Diff.STE.Flat.seriesFunM c x i j‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hMnn
      _ ≤ M * Real.sqrt E := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE0) hMnn
  have hMs : M * Real.sqrt E ≤ (2 * A + K) * (1 + E) := by
    have hsq : Real.sqrt E ^ 2 = E := Real.sq_sqrt hEnn
    have hr : Real.sqrt E ≤ 1 + E := by nlinarith [Real.sqrt_nonneg E, hsq, hEnn]
    rw [hMdef]
    nlinarith [hAnn, hK, Real.sqrt_nonneg E, hsq, hEnn]
  calc (∑ i : Fin n, ∑ j : Fin n, |Work.Diff.STE.L2re
        (fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x) i j)
        (fun x => Work.Diff.STE.Flat.seriesFunM c x i j)|)
      ≤ ∑ i : Fin n, ∑ j : Fin n, M * Real.sqrt E :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => key i j))
    _ = (n : ℝ) * n * (M * Real.sqrt E) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ (n : ℝ) * n * ((2 * A + K) * (1 + E)) :=
        mul_le_mul_of_nonneg_left hMs (by positivity)
    _ = ((n : ℝ) * n * (2 * A + K)) * (1 + E) := by ring

end

end Work.Diff.STE.flat
