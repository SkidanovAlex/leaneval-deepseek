import Submission.ZagierHoffmanProof.GenEvalEntire

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial PowerSeries Finset
open scoped WithZero Topology

/-!
# The polynomials `ℓ_d = ∏_{i=1}^{d}(t - θ^{q^i})` and the iterated functional equation

The ζ_A ↔ CMPL bridge (Dac (4.2) / AT09 (2.4.1) / Chang–Green–Mishiba `(E:InterpolationAT)`)
rests on the following elementary consequence of the functional equation `Ω^{(1)} = Ω/(t-θ^q)` of
the Anderson–Thakur period: for every `d`,

    `(∏_{i=1}^{d}(t-θ^{q^i})) · Ω^{(d)} = Ω`,   hence   `(Ω^{(d)})(θ) = Ω(θ)/ℓ_d`,

where `Ω^{(d)}` is the `d`-fold coefficientwise Frobenius twist `frobTwist d` of the workspace.
(For the workspace's period `Ω = ambMu · atOmegaGen` the functional equation is
`AmbPeriod.ambOmega_functional`.)  We prove the iteration for a general `ω` satisfying it, together
with its evaluation at `t = θ`.

## Main results

* `ellSh`                    — the family `∏_{i<d}(t - θ^{q^{i+a}})` (`a = 1` is the paper's `ℓ_d`).
* `ellSh_succ'`              — `ellSh a (d+1) = (t-θ^{q^a})·ellSh (a+1) d`.
* `frobTwist_one_ellSh`      — `(∏_{i<d}(t-θ^{q^{i+a}}))^{(1)} = ∏_{i<d}(t-θ^{q^{i+a+1}})`.
* `ellSh_one_mul_frobTwist`  — the iterated functional equation (twist form).
* `ellSh_eval_mul`           — `(∏_{i<d}(θ-θ^{q^{i+1}}))·(ω^{(d)})(θ) = ω(θ)`.
-/

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

section Ell

variable (q : ℕ) [FrobPow K q] (θ : K)

/-- `ellSh a d = ∏_{i<d}(t - θ ^ (q ^ (i+a)))`; `ellSh 1 d` is the paper's `ℓ_d`
(`∏_{i=1}^{d}(t-θ^{q^i})`). -/
noncomputable def ellSh (a d : ℕ) : PowerSeries K :=
  ∏ i ∈ Finset.range d, (PowerSeries.X - PowerSeries.C (θ ^ (q ^ (i + a))))

@[simp] lemma ellSh_zero (a : ℕ) : ellSh q θ a 0 = 1 := by
  rw [ellSh]; simp

/-- The `d`-fold Frobenius twist commutes with finite products. -/
lemma frobTwist_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries K) (n : ℕ) :
    frobTwist (R := K) (p := q) n (∏ i ∈ s, f i)
      = ∏ i ∈ s, frobTwist (R := K) (p := q) n (f i) := by
  change (frobTwistHom (R := K) (p := q) n) (∏ i ∈ s, f i)
      = ∏ i ∈ s, (frobTwistHom (R := K) (p := q) n) (f i)
  rw [map_prod]

/-- The `d = 0` Frobenius twist is the identity. -/
lemma frobTwist_zero_iter' (f : PowerSeries K) :
    frobTwist (R := K) (p := q) 0 f = f := by
  ext k
  rw [frobTwist_coeff, pow_zero, pow_one]

/-- The Frobenius twist fixes `t`. -/
lemma frobTwist_X' (n : ℕ) :
    frobTwist (R := K) (p := q) n (PowerSeries.X : PowerSeries K) = PowerSeries.X := by
  ext k
  rw [frobTwist_coeff, PowerSeries.coeff_X]
  by_cases h : k = 1 <;> simp [h, zero_pow (pow_ne_zero n (FrobPow.ne_zero K (q := q)))]

/-- The reindexing used in the induction step: `ellSh a (d+1) = (t-θ^{q^a})·ellSh (a+1) d`. -/
lemma ellSh_succ' (a d : ℕ) :
    ellSh q θ a (d + 1) = (PowerSeries.X - PowerSeries.C (θ ^ (q ^ a))) * ellSh q θ (a + 1) d := by
  have h1 : (θ : K) ^ (q ^ (0 + a)) = θ ^ (q ^ a) := by rw [Nat.zero_add]
  have h2 : (fun i : ℕ => (PowerSeries.X - PowerSeries.C (θ ^ (q ^ (i + 1 + a)))))
      = fun i : ℕ => (PowerSeries.X - PowerSeries.C (θ ^ (q ^ (i + (a + 1))))) := by
    funext i
    rw [show i + 1 + a = i + (a + 1) from by omega]
  rw [ellSh, ellSh, Finset.prod_range_succ', h1, h2]
  exact mul_comm _ _

/-- The single twist step of `ellSh`: the exponent `q^(i+a)` becomes `q^(i+a+1)`. -/
lemma frobTwist_one_ellSh (a d : ℕ) :
    frobTwist (R := K) (p := q) 1 (ellSh q θ a d) = ellSh q θ (a + 1) d := by
  rw [ellSh, frobTwist_prod, ellSh]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 : ((θ : K) ^ (q ^ (i + a))) ^ q = θ ^ (q ^ (i + (a + 1))) := by
    rw [← pow_mul, ← pow_succ, show (i + a) + 1 = i + (a + 1) from by omega]
  rw [frobTwist_sub, frobTwist_X' (q := q) 1, frobTwist_C, pow_one, h2]

/-- `ellSh` is super-entire (it is a polynomial). -/
lemma gSuperEntire_ellSh {γ : Γ₀} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (a d : ℕ) :
    GSuperEntire γ (ellSh q θ a d) := by
  rw [ellSh]
  refine GSuperEntire.prod hγ1 _ _ fun i _ => ?_
  exact (GSuperEntire.X (K := K) (γ := γ) hγ0).sub (GSuperEntire.C γ _)

/-- Evaluation of `t - c`. -/
lemma evalSeriesGen_X_sub_C {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    (hγ0 : 0 < γ) (c : K) :
    evalSeriesGen (PowerSeries.X - PowerSeries.C c : PowerSeries K) θ = θ - c := by
  rw [evalSeriesGen_sub hγ harch (GSuperEntire.X (K := K) (γ := γ) hγ0)
    (GSuperEntire.C γ c) θ]
  simp

/-- Evaluation of `ellSh` at `θ`. -/
lemma evalSeriesGen_ellSh {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀)
    (hγ0 : 0 < γ) (a d : ℕ) :
    evalSeriesGen (ellSh q θ a d) θ = ∏ i ∈ Finset.range d, (θ - θ ^ (q ^ (i + a))) := by
  have hfac : ∀ d, ellSh q θ a (d + 1)
      = ellSh q θ a d * (PowerSeries.X - PowerSeries.C (θ ^ (q ^ (d + a)))) := by
    intro d
    rw [ellSh, ellSh, Finset.prod_range_succ]
  have hge : ∀ d, GSuperEntire γ (ellSh q θ a d) :=
    fun d => gSuperEntire_ellSh q θ hγ0 hγ.le a d
  have hgc : ∀ d, GSuperEntire γ (PowerSeries.X - PowerSeries.C (θ ^ (q ^ (d + a)))) :=
    fun d => (GSuperEntire.X (K := K) (γ := γ) hγ0).sub (GSuperEntire.C γ _)
  induction d with
  | zero => rw [ellSh_zero, Finset.range_zero, Finset.prod_empty, evalSeriesGen_one]
  | succ d ih =>
    rw [hfac d, evalSeriesGen_mul hγ harch (hge d) (hgc d) θ, ih,
      evalSeriesGen_X_sub_C (θ := θ) hγ harch hγ0 (θ ^ (q ^ (d + a)))]
    conv_rhs => rw [Finset.prod_range_succ]

/-- **The iterated functional equation** (cleared form): if `(t-θ^q)·ω^{(1)} = ω` then
`(∏_{i=1}^{d}(t-θ^{q^i}))·ω^{(d)} = ω`. -/
theorem ellSh_one_mul_frobTwist (d : ℕ) {ω : PowerSeries K}
    (hω : (PowerSeries.X - PowerSeries.C (θ ^ q)) * frobTwist (R := K) (p := q) 1 ω = ω) :
    ellSh q θ 1 d * frobTwist (R := K) (p := q) d ω = ω := by
  induction d with
  | zero => rw [ellSh_zero, one_mul, frobTwist_zero_iter']
  | succ d ih =>
    have h1 : frobTwist (R := K) (p := q) 1 (ellSh q θ 1 d)
        * frobTwist (R := K) (p := q) 1 (frobTwist (R := K) (p := q) d ω)
        = frobTwist (R := K) (p := q) 1 ω := by
      rw [← frobTwist_mul, ih]
    rw [frobTwist_one_ellSh, frobTwist_comp] at h1
    rw [show (1 + d) = d + 1 from by omega] at h1
    rw [ellSh_succ' (q := q) (θ := θ) 1 d]
    simp only [pow_one]
    rw [mul_assoc, h1, hω]

end Ell

section Eval

variable (q : ℕ) [FrobPow K q] (θ : K) {γ : Γ₀}

/-- **The evaluation of the iterated functional equation at `θ`**:
`(∏_{i=1}^{d}(θ-θ^{q^i}))·(ω^{(d)})(θ) = ω(θ)`.  This is the identity
`(Ω^{(d)})(θ) = Ω(θ)/ℓ_d` that the ζ_A ↔ CMPL bridge (Dac (4.2)) uses. -/
theorem ellSh_eval_mul (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hγ0 : 0 < γ)
    (d : ℕ) {ω : PowerSeries K} (hse : GSuperEntire γ ω)
    (hω : (PowerSeries.X - PowerSeries.C (θ ^ q)) * frobTwist (R := K) (p := q) 1 ω = ω) :
    (∏ i ∈ Finset.range d, (θ - θ ^ (q ^ (i + 1)))) *
      evalSeriesGen (frobTwist (R := K) (p := q) d ω) θ = evalSeriesGen ω θ := by
  have h := ellSh_one_mul_frobTwist q θ d hω
  have h2 := congrArg (fun f : PowerSeries K => evalSeriesGen f θ) h
  rw [evalSeriesGen_mul hγ harch (gSuperEntire_ellSh q θ hγ0 hγ.le 1 d)
    (hse.frobTwist hγ.le d) θ, evalSeriesGen_ellSh q θ hγ harch hγ0 1 d] at h2
  exact h2

end Eval

end ZagierHoffmanPositiveChar
