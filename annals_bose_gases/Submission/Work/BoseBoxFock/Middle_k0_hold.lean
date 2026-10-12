import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.ValMinAbs
import Submission.Work.BoseBoxFock.Middle_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

noncomputable section

open scoped BigOperators
open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `Work.BoseBoxFock.Middle_k0_hold` — the `k = 0` slice of the middle kernel `Middle`

The `k = 0` slice of FS's cubic-row middle kernel `Middle` (`pcfFrameDefs.Middle`), expanded in
the four channels of `summand_four_split` (`PotCubicExpansion`) — exactly as in
`Middle_expansion_repaired`, but with the `k`-sum collapsed to its only term `k = 0`.

At `k = 0` the label-additivity hypothesis `hsub` used by the general channels is **not needed**:
the pair `(s, 0)` has `s - 0 = s` and `kmomLab ℓ N 0 = 0` (`k0_kmomLab_zero`), so the `u`-slot
phase of the `(a)`/`(c)` channels is trivial (`k0_exp_zero_phase`) and the `s`-slot phases
`e^{-i⟪κ_s,y⟫}χ(y)`, `e^{i⟪κ_s,x⟫}θ(x)` combine — through `inner_sub_right` — into
`e^{i⟪κ_s,x−y⟫}`, the argument of the `s`-frame `Ksfr (x − y)` (`k0_phase_pull`).

## Layout

* `k0_kmomLab_zero`, `k0_exp_zero_phase`, `k0_phase_pull` — the three labelled facts above;
* `k0_expand`, `k0_sum_factor`, `k0_sum_split4mul` — the elementary finite-sum algebra;
* `k0_summand` — the pointwise `(a) − (b) − (c) + (d)` expansion of the `k = 0` summand (from
  `summand_four_split` at `k = 0`, with the `u`-phase and the `s`-phase collapsed);
* `k0_chanA0 … k0_chanD0` — the four channel sums at `k = 0`, in the `(√ℓ³)⁻³`-free form, with
  the closed `s`-sums `Ksfr (x − y)` (channels `(a)`, `(b)`) and the `χ̂`-weighted `s`-sum
  `∑_s f_L(s)χ̂(ℓκ_s)e^{i⟪κ_s,x⟫}` (channels `(c)`, `(d)`);
* `k0_chanA … k0_chanD` — the same with the outer `(√ℓ³)⁻³` restored (`k0_sum_factor`);
* `Middle_k0_hold` — the assembly, with `((√ℓ³)⁻¹)³ = ℓ^{-9/2}` (`inv_sqrt_cube`).
-/

/-! ## 1. The labelled facts at `k = 0` -/

/-- The dual-lattice momentum of the zero integer vector vanishes. -/
lemma k0_vec_zero : Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 := by
  simp [Work.BoseB4.vec]
  funext i
  simp

/-- The centred integer vector of the zero label vanishes. -/
lemma k0_labVec_zero (N : ℕ) : labVec N (0 : Lab N) = 0 := by
  funext i
  simp [labVec, ZMod.valMinAbs_zero]

/-- The lattice momentum of the zero label vanishes. -/
lemma k0_kmomLab_zero (ℓ : ℝ) (N : ℕ) : kmomLab ℓ N (0 : Lab N) = 0 := by
  rw [kmomLab, k0_labVec_zero, k0_vec_zero, smul_zero]

/-- The `u`-phase of the zero label is trivial. -/
lemma k0_exp_zero_phase (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (u : Ω) :
    Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N (0 : Lab N)) u : ℂ))) = 1 := by
  rw [k0_kmomLab_zero]
  simp

/-- The plane-wave algebra of the `(a)`-channel at `k = 0`: the two `s`-phases collapse into the
phase `e^{i⟪κ_s,x−y⟫}` of the `s`-frame. -/
lemma k0_phase_pull (a y x : Ω) (χy θx : ℂ) :
    Complex.exp (-(Complex.I * (inner ℝ a y : ℂ))) * χy
        * (Complex.exp (Complex.I * (inner ℝ a x : ℂ)) * θx)
      = Complex.exp (Complex.I * (inner ℝ a (x - y) : ℂ)) * (χy * θx) := by
  rw [← exp_shift_left a x y]
  ring

/-! ## 2. Elementary finite-sum algebra -/

/-- The `(a)`-channel factorisation: the product of the two `c`-factors of the `y`- and `x`-slots
expands as `c³` times the four monomials. -/
lemma k0_expand (c A B V W : ℂ) :
    (c * (A - B)) * (c * V) * (c * W) = c ^ 3 * (A * V * W - B * V * W) := by ring

/-- Pulling a constant out of a finite sum of products. -/
lemma k0_sum_factor {ι : Type*} (t : Finset ι) (F Y : ι → ℂ) (c : ℂ) :
    (∑ i ∈ t, F i * (c * Y i)) = c * ∑ i ∈ t, F i * Y i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The linearity of a finite sum over the four channels, with the constant `c` kept inside. -/
lemma k0_sum_split4mul {ι : Type*} (t : Finset ι) (F a b d e : ι → ℂ) (c : ℂ) :
    (∑ i ∈ t, F i * (c * (a i - b i - d i + e i)))
      = (∑ i ∈ t, F i * (c * a i)) - (∑ i ∈ t, F i * (c * b i))
        - (∑ i ∈ t, F i * (c * d i)) + (∑ i ∈ t, F i * (c * e i)) := by
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-! ## 3. The pointwise `k = 0` expansion -/

/-- **The `k = 0` four-channel split.**  Specialising `summand_four_split` to `k = 0` and using
`s - 0 = s`, `kmomLab ℓ N 0 = 0` (hence the trivial `u`-phase) and `inner_sub_right` (hence the
`s`-frame phase `e^{i⟪κ_s,x−y⟫}`). -/
lemma k0_summand (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (s : Lab N) (x y u : Ω) :
    (starRingEnd ℂ) (pinQ v μ N s y) * pinTheta v μ N s x * (starRingEnd ℂ) (pinQ v μ N 0 u)
      = ((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3 *
          ( Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ))
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ)
            - Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ))
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
              * (((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N 0) : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u)
            - ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N s) : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y
              * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ)
            + ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N s) : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y
              * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
              * (((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N 0) : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u)) := by
  have hE := k0_exp_zero_phase v μ N u
  rw [conj_pinQ_eq v μ N s y, pinTheta_eq_exp v μ N s x, conj_pinQ_eq v μ N 0 u, hE]
  simp only [one_mul]
  rw [k0_expand]
  have hAV : Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) y : ℂ)))
        * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
        * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
      = Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ))
          * (((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x) :=
    k0_phase_pull (kmomLab (ellH v μ) N s) y x _ _
  rw [hAV]
  congr 1
  ring

/-! ## 4. The four channel sums -/

/-- Channel `(a)` of the `k = 0` slice: the two `χ_Λ`-parts. -/
lemma k0_chanA0 (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (x y u : Ω) :
    (∑ s ∈ Work.BoseB7.excited (Lab N),
        ((fLh v fc μ N s * W1h v h μ fu N 0 : ℝ) : ℂ)
          * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ))
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ)))
      = ((W1h v h μ fu N 0 : ℝ) : ℂ) * Ksfr v fc μ N (x - y)
          * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
          * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ) := by
  set χy : ℂ := ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ) with hχy
  set θx : ℂ := Work.BoseK15.corpusBox.thetaFun (ellH v μ) x with hθx
  set χu : ℂ := ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ) with hχu
  set dd : ℂ := ((W1h v h μ fu N 0 : ℝ) : ℂ) with hdd
  set Ks : ℂ := Ksfr v fc μ N (x - y) with hKs
  rw [hKs]
  simp only [Ksfr]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Complex.ofReal_mul]
  try ring

/-- Channel `(b)` of the `k = 0` slice: `χ_Λ(y)` with the condensate part of `pinQ 0 u`. -/
lemma k0_chanB0 (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (x y u : Ω) :
    (∑ s ∈ Work.BoseB7.excited (Lab N),
        ((fLh v fc μ N s * W1h v h μ fu N 0 : ℝ) : ℂ)
          * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ))
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
              * (((Work.BoseK15.corpusBox.hatChi
                    ((ellH v μ) • kmomLab (ellH v μ) N 0) : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u)))
      = ((W1h v h μ fu N 0 : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N 0) : ℝ) : ℂ)
          * Ksfr v fc μ N (x - y)
          * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u := by
  set χy : ℂ := ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ) with hχy
  set θx : ℂ := Work.BoseK15.corpusBox.thetaFun (ellH v μ) x with hθx
  set θu : ℂ := Work.BoseK15.corpusBox.thetaFun (ellH v μ) u with hθu
  set dd : ℂ := ((W1h v h μ fu N 0 : ℝ) : ℂ) with hdd
  set H0 : ℂ :=
    ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N 0) : ℝ) : ℂ) with hH0
  set Ks : ℂ := Ksfr v fc μ N (x - y) with hKs
  rw [hKs]
  simp only [Ksfr]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Complex.ofReal_mul]
  try ring

/-- Channel `(c)` of the `k = 0` slice: the condensate part of `pinQ s y` with the `χ_Λ`-part of
`pinQ 0 u`; the surviving `s`-sum is the `χ̂`-weighted frame `∑_s f_L(s)χ̂(ℓκ_s)e^{i⟪κ_s,x⟫}`. -/
lemma k0_chanC0 (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (x y u : Ω) :
    (∑ s ∈ Work.BoseB7.excited (Lab N),
        ((fLh v fc μ N s * W1h v h μ fu N 0 : ℝ) : ℂ)
          * (((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N s) : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y
              * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ)))
      = ((W1h v h μ fu N 0 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
          * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ)
          * (∑ s ∈ Work.BoseB7.excited (Lab N),
              ((fLh v fc μ N s : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.hatChi
                      ((ellH v μ) • kmomLab (ellH v μ) N s) : ℝ) : ℂ)
                * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))) := by
  set θy : ℂ := Work.BoseK15.corpusBox.thetaFun (ellH v μ) y with hθy
  set θx : ℂ := Work.BoseK15.corpusBox.thetaFun (ellH v μ) x with hθx
  set χu : ℂ := ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ) with hχu
  set dd : ℂ := ((W1h v h μ fu N 0 : ℝ) : ℂ) with hdd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Complex.ofReal_mul]
  try ring

/-- Channel `(d)` of the `k = 0` slice: both condensate parts; the `u`-slot has no phase. -/
lemma k0_chanD0 (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (x y u : Ω) :
    (∑ s ∈ Work.BoseB7.excited (Lab N),
        ((fLh v fc μ N s * W1h v h μ fu N 0 : ℝ) : ℂ)
          * (((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N s) : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y
              * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
              * (((Work.BoseK15.corpusBox.hatChi
                    ((ellH v μ) • kmomLab (ellH v μ) N 0) : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u)))
      = ((W1h v h μ fu N 0 : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N 0) : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u
          * (∑ s ∈ Work.BoseB7.excited (Lab N),
              ((fLh v fc μ N s : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.hatChi
                      ((ellH v μ) • kmomLab (ellH v μ) N s) : ℝ) : ℂ)
                * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))) := by
  set θy : ℂ := Work.BoseK15.corpusBox.thetaFun (ellH v μ) y with hθy
  set θx : ℂ := Work.BoseK15.corpusBox.thetaFun (ellH v μ) x with hθx
  set θu : ℂ := Work.BoseK15.corpusBox.thetaFun (ellH v μ) u with hθu
  set dd : ℂ := ((W1h v h μ fu N 0 : ℝ) : ℂ) with hdd
  set H0 : ℂ :=
    ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N 0) : ℝ) : ℂ) with hH0
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Complex.ofReal_mul]
  try ring

/-- Channel `(a)` with the outer `(√ℓ³)⁻³` restored. -/
lemma k0_chanA (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (x y u : Ω) :
    (∑ s ∈ Work.BoseB7.excited (Lab N),
        ((fLh v fc μ N s * W1h v h μ fu N 0 : ℝ) : ℂ)
          * (((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
              * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ))
                  * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
                  * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
                  * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ))))
      = ((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
          * (((W1h v h μ fu N 0 : ℝ) : ℂ) * Ksfr v fc μ N (x - y)
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ)) := by
  rw [k0_sum_factor, k0_chanA0]

/-- Channel `(b)` with the outer `(√ℓ³)⁻³` restored. -/
lemma k0_chanB (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (x y u : Ω) :
    (∑ s ∈ Work.BoseB7.excited (Lab N),
        ((fLh v fc μ N s * W1h v h μ fu N 0 : ℝ) : ℂ)
          * (((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
              * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (x - y) : ℂ))
                  * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
                  * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
                  * (((Work.BoseK15.corpusBox.hatChi
                        ((ellH v μ) • kmomLab (ellH v μ) N 0) : ℝ) : ℂ)
                    * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u))))
      = ((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
          * (((W1h v h μ fu N 0 : ℝ) : ℂ)
              * ((Work.BoseK15.corpusBox.hatChi
                    ((ellH v μ) • kmomLab (ellH v μ) N 0) : ℝ) : ℂ)
              * Ksfr v fc μ N (x - y)
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u) := by
  rw [k0_sum_factor, k0_chanB0]

/-- Channel `(c)` with the outer `(√ℓ³)⁻³` restored. -/
lemma k0_chanC (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (x y u : Ω) :
    (∑ s ∈ Work.BoseB7.excited (Lab N),
        ((fLh v fc μ N s * W1h v h μ fu N 0 : ℝ) : ℂ)
          * (((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
              * (((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N s) : ℝ) : ℂ)
                  * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y
                  * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
                    * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
                  * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ))))
      = ((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
          * (((W1h v h μ fu N 0 : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
              * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ)
              * (∑ s ∈ Work.BoseB7.excited (Lab N),
                  ((fLh v fc μ N s : ℝ) : ℂ)
                    * ((Work.BoseK15.corpusBox.hatChi
                          ((ellH v μ) • kmomLab (ellH v μ) N s) : ℝ) : ℂ)
                    * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ)))) := by
  rw [k0_sum_factor, k0_chanC0]

/-- Channel `(d)` with the outer `(√ℓ³)⁻³` restored. -/
lemma k0_chanD (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) (x y u : Ω) :
    (∑ s ∈ Work.BoseB7.excited (Lab N),
        ((fLh v fc μ N s * W1h v h μ fu N 0 : ℝ) : ℂ)
          * (((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
              * (((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N s) : ℝ) : ℂ)
                  * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y
                  * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
                    * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
                  * (((Work.BoseK15.corpusBox.hatChi
                        ((ellH v μ) • kmomLab (ellH v μ) N 0) : ℝ) : ℂ)
                    * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u))))
      = ((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
          * (((W1h v h μ fu N 0 : ℝ) : ℂ)
              * ((Work.BoseK15.corpusBox.hatChi
                    ((ellH v μ) • kmomLab (ellH v μ) N 0) : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u
              * (∑ s ∈ Work.BoseB7.excited (Lab N),
                  ((fLh v fc μ N s : ℝ) : ℂ)
                    * ((Work.BoseK15.corpusBox.hatChi
                          ((ellH v μ) • kmomLab (ellH v μ) N s) : ℝ) : ℂ)
                    * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ)))) := by
  rw [k0_sum_factor, k0_chanD0]

/-! ## 5. The assembly -/

theorem Middle_k0_hold (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (x y u : EuclideanSpace ℝ (Fin 3)) :
    (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
        ((Work.BoseBoxFock.fLh v fc μ N s * Work.BoseBoxFock.W1h v h μ fu N 0 : ℝ) : ℂ)
          * ((starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N s y)
              * Work.BoseBoxFock.pinTheta v μ N s x
              * (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N 0 u)))
      = ((Work.BoseBoxFock.W1h v h μ fu N 0 : ℝ) : ℂ)
          * (((Work.BoseBoxFock.ellH v μ) ^ (-(9 / 2 : ℝ)) : ℝ) : ℂ)
          * ( Work.BoseBoxFock.Ksfr v fc μ N (x - y)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) y : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ)
              - ((Work.BoseK15.corpusBox.hatChi
                    ((Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N 0) : ℝ) : ℂ)
                * Work.BoseBoxFock.Ksfr v fc μ N (x - y)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) y : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) u
              - Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) y
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ)
                * (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
                    ((Work.BoseBoxFock.fLh v fc μ N s : ℝ) : ℂ)
                      * ((Work.BoseK15.corpusBox.hatChi
                            ((Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s) : ℝ) : ℂ)
                      * Complex.exp (Complex.I * (inner ℝ
                          (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s) x : ℂ)))
              + ((Work.BoseK15.corpusBox.hatChi
                    ((Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N 0) : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) y
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) u
                * (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
                    ((Work.BoseBoxFock.fLh v fc μ N s : ℝ) : ℂ)
                      * ((Work.BoseK15.corpusBox.hatChi
                            ((Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s) : ℝ) : ℂ)
                      * Complex.exp (Complex.I * (inner ℝ
                          (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s) x : ℂ)))) := by
  have hc3 : ((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
      = (((ellH v μ) ^ (-(9 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, inv_sqrt_cube (ellH_pos v μ)]
  rw [Finset.sum_congr rfl (fun s (_ : s ∈ Work.BoseB7.excited (Lab N)) => by
        rw [k0_summand v h fc fu μ N s x y u])]
  rw [k0_sum_split4mul]
  rw [k0_chanA, k0_chanB, k0_chanC, k0_chanD]
  rw [hc3]
  ring

end

end Work.BoseBoxFock
