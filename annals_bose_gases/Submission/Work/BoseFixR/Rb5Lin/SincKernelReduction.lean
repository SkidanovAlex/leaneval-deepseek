import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.BoseBoxFock.Defs
import Submission.Work.BoseFixR.Rb5Lin.Sinc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.Rb5Lin.SincKernelReduction` — the "difference of cosines" reduction

The target of this file is the **sharp** lattice ↦ continuum comparison for the
`sincR`-transform of an `L¹` profile `f` on `[0,R]`, `R ≤ ℓ`:

```
∑_{k ∈ Lab N, k ≠ 0} (∫_0^R f(r) sincR(‖q_k‖ r) dr)² / ‖q_k‖²
  ≤ (2 ℓ³ / π²) ∫_0^∞ (∫_0^R f(r) sincR(a r) dr)² da ,      q_k = kmomLab ℓ N k.
```

## The reduction used here (the "difference of cosines" route)

The whole lattice content is the *pointwise* kernel bound

```
K(r,s) := ∑_{k ≠ 0} sincR(q_k r) sincR(q_k s)/q_k² ≤ (ℓ³/π)/max r s        (0 < r,s ≤ R)
```

and — this is the point of this file — that bound is *equivalent* to a single
**oscillatory lattice sum** bound: writing `a = 2πr/ℓ`, `b = 2πs/ℓ` and
`P(c) = ∑_m sin(c‖m‖)/‖m‖³` over the cube `m ∈ {-N,…,N}³`,

```
sincR(a‖m‖) sincR(b‖m‖)/‖m‖²  =  (1/(2ab)) ∫_{a-b}^{a+b} sin(c‖m‖)/‖m‖³ dc
```

because `sin x sin y = (cos(x-y)-cos(x+y))/2` and `cos α - cos β = ∫_α^β ρ sin(cρ) dc`.
Summing over `m` and bounding the interval integral by its length `2a` times
`sup_{|c| ≤ 4π} |P(c)|` gives `K ≤ sup |P| / max(r,s)`; since the required constant is
`8π² ≈ 78.96`, it is enough to know `|P(c)| ≤ 40` for `0 < c ≤ 4π` — the numerically
true supremum is `≈ 23.3`, approached as `c → 0⁺`.

This file therefore isolates that oscillatory bound as a single hypothesis (the `hP`
arguments below) and proves everything above it.
-/

noncomputable section

open MeasureTheory intervalIntegral
open scoped Real BigOperators

namespace Work.BoseFixR.Rb5Lin

/-- The lattice cube `{-N,…,N}³ ⊂ ℤ³`. -/
def cube (N : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(N : ℤ)) N)

/-- The Euclidean norm of an integer vector, `√(Σ mᵢ²)`. -/
def nrm (m : Fin 3 → ℤ) : ℝ := Real.sqrt (∑ i, ((m i : ℝ)) ^ 2)

lemma nrm_nonneg (m : Fin 3 → ℤ) : 0 ≤ nrm m := Real.sqrt_nonneg _

/-- The oscillatory lattice sum `P(c) = ∑_m sin(c‖m‖)/‖m‖³` over the cube. -/
def oscillSum (N : ℕ) (c : ℝ) : ℝ :=
  ∑ m ∈ cube N, Real.sin (c * nrm m) / (nrm m) ^ 3

/-- The weighted `sincR`-kernel sum `T(a,b) = ∑_m sincR(a‖m‖) sincR(b‖m‖)/‖m‖²`. -/
def sincKernel (N : ℕ) (a b : ℝ) : ℝ :=
  ∑ m ∈ cube N, Work.BoseFixR.sincR (a * nrm m) * Work.BoseFixR.sincR (b * nrm m)
    / (nrm m) ^ 2

/-! ## 1. The termwise identity

`sincR(aρ) sincR(bρ)/ρ² = (1/(2ab)) ∫_{a-b}^{a+b} sin(cρ)/ρ³ dc`. -/

theorem sincR_mul_sincR_eq_interval {a b ρ : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Work.BoseFixR.sincR (a * ρ) * Work.BoseFixR.sincR (b * ρ) / ρ ^ 2
      = (1 / (2 * a * b)) * ∫ c in (a - b)..(a + b), Real.sin (c * ρ) / ρ ^ 3 := by
  rcases eq_or_ne ρ 0 with hρ | hρ
  · subst hρ
    simp
  · have haρ : a * ρ ≠ 0 := mul_ne_zero (ne_of_gt ha) hρ
    have hbρ : b * ρ ≠ 0 := mul_ne_zero (ne_of_gt hb) hρ
    have hInt : (∫ c in (a - b)..(a + b), Real.sin (c * ρ))
        = (Real.cos ((a - b) * ρ) - Real.cos ((a + b) * ρ)) / ρ := by
      rw [intervalIntegral.integral_comp_mul_right (f := Real.sin) hρ, integral_sin]
      simp only [smul_eq_mul]
      ring
    have hInt2 : (∫ c in (a - b)..(a + b), Real.sin (c * ρ) / ρ ^ 3)
        = (Real.cos ((a - b) * ρ) - Real.cos ((a + b) * ρ)) / ρ ^ 4 := by
      rw [show (fun c : ℝ => Real.sin (c * ρ) / ρ ^ 3)
            = fun c : ℝ => (ρ ^ 3)⁻¹ * Real.sin (c * ρ) by
          funext c; rw [div_eq_inv_mul]]
      rw [intervalIntegral.integral_const_mul, hInt]
      field_simp
    rw [hInt2, Work.BoseFixR.sincR_of_ne haρ, Work.BoseFixR.sincR_of_ne hbρ]
    have htrig : Real.cos ((a - b) * ρ) - Real.cos ((a + b) * ρ)
        = 2 * (Real.sin (a * ρ) * Real.sin (b * ρ)) := by
      have h1 : (a - b) * ρ = a * ρ - b * ρ := by ring
      have h2 : (a + b) * ρ = a * ρ + b * ρ := by ring
      rw [h1, h2, Real.cos_sub, Real.cos_add]
      ring
    rw [htrig]
    field_simp

/-! ## 2. Summing over the cube -/

theorem sincKernel_eq_integral (N : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    sincKernel N a b
      = (1 / (2 * a * b)) * ∫ c in (a - b)..(a + b), oscillSum N c := by
  unfold sincKernel oscillSum
  rw [intervalIntegral.integral_finset_sum]
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => sincR_mul_sincR_eq_interval ha hb
  · intro m _
    by_cases h : nrm m = 0
    · simp [h]
    · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-! ## 3. Oddness of `P` and the interval-integral bound

The oscillatory bound `|P(c)| ≤ 40` for *positive* `c ≤ 4π` extends to negative `c` by
oddness of `P`, hence gives `|∫_{a-b}^{a+b} P| ≤ 40·2a` for `0 < a ≤ b`. -/

theorem oscillSum_neg (N : ℕ) (c : ℝ) : oscillSum N (-c) = -oscillSum N c := by
  unfold oscillSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [neg_mul, Real.sin_neg]
  ring

/-- The pointwise bound on `P` on `[b-a, a+b]`, assuming the oscillatory bound on `(0, 4π]`. -/
theorem abs_oscillSum_le_of_pos {N : ℕ} {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb4 : b ≤ 2 * Real.pi)
    (hP : ∀ c : ℝ, 0 < c → c ≤ 4 * Real.pi → |oscillSum N c| ≤ 40)
    (hc : c ∈ Set.uIoc (b - a) (a + b)) : |oscillSum N c| ≤ 40 := by
  rw [Set.uIoc_of_le (by linarith), Set.mem_Ioc] at hc
  exact hP c (by linarith [hc.1]) (by linarith [hc.2])

/-- **Odd symmetry kills the symmetric part of the interval**: `∫_{a-b}^{a+b} P = ∫_{b-a}^{a+b} P`.
This is what makes the interval short (`2a`, not `2b`) and hence the bound sharp. -/
theorem integral_oscillSum_eq {N : ℕ} {a b : ℝ} :
    (∫ c in (a - b)..(a + b), oscillSum N c)
      = ∫ c in (b - a)..(a + b), oscillSum N c := by
  have hodd : (∫ c in (a - b)..(b - a), oscillSum N c) = 0 := by
    have h2 : (∫ c in (a - b)..(b - a), oscillSum N (-c))
        = ∫ c in (a - b)..(b - a), oscillSum N c := by
      rw [intervalIntegral.integral_comp_neg]
      simp only [neg_sub]
    have h3 : (∫ c in (a - b)..(b - a), oscillSum N (-c))
        = -(∫ c in (a - b)..(b - a), oscillSum N c) := by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr fun c _ => oscillSum_neg N c
    linarith
  have hii : IntervalIntegrable (oscillSum N) volume (a - b) (b - a) :=
    Continuous.intervalIntegrable (by unfold oscillSum; fun_prop) _ _
  have hii2 : IntervalIntegrable (oscillSum N) volume (b - a) (a + b) :=
    Continuous.intervalIntegrable (by unfold oscillSum; fun_prop) _ _
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hii hii2
  linarith [hsplit]

/-- **The oscillatory bound implies the weighted `sincR`-kernel bound** (in the microscopic
normalisation `a = 2πr/ℓ`, `b = 2πs/ℓ`). -/
theorem abs_sincKernel_le {N : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb4 : b ≤ 2 * Real.pi)
    (hP : ∀ c : ℝ, 0 < c → c ≤ 4 * Real.pi → |oscillSum N c| ≤ 40) :
    |sincKernel N a b| ≤ 8 * Real.pi ^ 2 / b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hmain : sincKernel N a b
      = (1 / (2 * a * b)) * ∫ c in (a - b)..(a + b), oscillSum N c :=
    sincKernel_eq_integral N ha hb
  rw [hmain, integral_oscillSum_eq]
  have hbnd : ∀ c ∈ Set.uIoc (b - a) (a + b), |oscillSum N c| ≤ 40 :=
    fun c hc => abs_oscillSum_le_of_pos ha hab hb4 hP hc
  have h1 : ‖∫ c in (b - a)..(a + b), oscillSum N c‖ ≤ 40 * |(a + b) - (b - a)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hbnd
  have hlen : |(a + b) - (b - a)| = 2 * a := by
    rw [abs_of_nonneg (by linarith)]
    ring
  rw [Real.norm_eq_abs, hlen] at h1
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * a * b))]
  calc (1 / (2 * a * b)) * |∫ c in (b - a)..(a + b), oscillSum N c|
      ≤ (1 / (2 * a * b)) * (40 * (2 * a)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 40 / b := by field_simp
    _ ≤ 8 * Real.pi ^ 2 / b := by
        gcongr
        nlinarith [Real.pi_gt_three]

/-! ## 4. The cube `{-N,…,N}³` versus the box lattice `Lab N` -/

/-- `valMinAbs` lands in `[-N,N]` for the odd modulus `2N+1`. -/
lemma valMinAbs_mem (N : ℕ) (x : ZMod (2 * N + 1)) :
    -((N : ℤ)) ≤ x.valMinAbs ∧ x.valMinAbs ≤ (N : ℤ) := by
  rw [ZMod.valMinAbs]
  split_ifs with h
  · constructor <;> omega
  · have hlt : x.val < 2 * N + 1 := ZMod.val_lt x
    constructor <;> omega

/-- The integer label of a box mode lies in the cube. -/
lemma labVec_mem_cube (N : ℕ) (n : Work.BoseBoxFock.Lab N) :
    Work.BoseBoxFock.labVec N n ∈ cube N := by
  rw [cube, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  exact valMinAbs_mem N (n i)

lemma labVec_inj (N : ℕ) : Function.Injective (Work.BoseBoxFock.labVec N) := by
  intro n m h
  funext i
  exact ZMod.injective_valMinAbs (congrFun h i)

lemma labVec_zero (N : ℕ) : Work.BoseBoxFock.labVec N 0 = 0 := by
  funext i
  simp [Work.BoseBoxFock.labVec]

lemma zero_mem_cube (N : ℕ) : (0 : Fin 3 → ℤ) ∈ cube N := by
  rw [cube, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  simp only [Pi.zero_apply]
  constructor <;> omega

lemma card_Icc_int (N : ℕ) : (Finset.Icc (-((N : ℤ))) (N : ℤ)).card = 2 * N + 1 := by
  rw [Int.card_Icc]
  omega

lemma card_cube (N : ℕ) : (cube N).card = (2 * N + 1) ^ 3 := by
  rw [cube, Fintype.card_piFinset]
  simp only [card_Icc_int, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma card_Lab (N : ℕ) : Fintype.card (Work.BoseBoxFock.Lab N) = (2 * N + 1) ^ 3 := by
  have h : Fintype.card (Work.BoseBoxFock.Lab N) = Fintype.card (Fin 3 → ZMod (2 * N + 1)) := rfl
  rw [h, Fintype.card_pi]
  simp only [ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The labels `k ≠ 0` of the box lattice are exactly the nonzero cube vectors: the labelling
`labVec N` is a bijection from `Lab N` onto the cube `{-N,…,N}³`. -/
theorem image_labVec_eq (N : ℕ) :
    ((Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0).image (Work.BoseBoxFock.labVec N)
      = (cube N).erase 0 := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro m hm
    rw [Finset.mem_erase]
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    rw [Finset.mem_erase] at hk
    exact ⟨fun h0 => hk.1 (labVec_inj N (by rw [h0, labVec_zero])), labVec_mem_cube N k⟩
  · rw [Finset.card_image_of_injective _ (labVec_inj N),
      Finset.card_erase_of_mem (Finset.mem_univ (0 : Work.BoseBoxFock.Lab N)),
      Finset.card_erase_of_mem (zero_mem_cube N), Finset.card_univ, card_Lab, card_cube]

/-! ## 5. The norm of `kmomLab` -/

lemma norm_vec (m : Fin 3 → ℤ) : ‖Work.BoseB4.vec m‖ = 2 * Real.pi * nrm m := by
  rw [EuclideanSpace.norm_eq]
  have h1 : ∀ i, ‖(Work.BoseB4.vec m).ofLp i‖ ^ 2 = (2 * Real.pi * (m i : ℝ)) ^ 2 := by
    intro i
    rw [Work.BoseB4.vec, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  have h2 : (∑ i, (2 * Real.pi * (m i : ℝ)) ^ 2)
      = (2 * Real.pi) ^ 2 * ∑ i, ((m i : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), nrm]

lemma norm_kmomLab {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (k : Work.BoseBoxFock.Lab N) :
    ‖Work.BoseBoxFock.kmomLab ℓ N k‖
      = 2 * Real.pi * nrm (Work.BoseBoxFock.labVec N k) / ℓ := by
  rw [Work.BoseBoxFock.kmomLab, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le),
    norm_vec, inv_mul_eq_div]

/-! ## 6. The kernel bound in the box-lattice language -/

/-- The kernel `Σ_{k≠0} sincR(‖q_k‖ r) sincR(‖q_k‖ s)/‖q_k‖²` for the honest box lattice. -/
def labKernel (ℓ : ℝ) (N : ℕ) (r s : ℝ) : ℝ :=
  ∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
    Work.BoseFixR.sincR (‖Work.BoseBoxFock.kmomLab ℓ N k‖ * r)
      * Work.BoseFixR.sincR (‖Work.BoseBoxFock.kmomLab ℓ N k‖ * s)
      / ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2

/-- Termwise conversion of the box-lattice summand to the cube summand. -/
lemma labKernel_term {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (k : Work.BoseBoxFock.Lab N) (r s : ℝ) :
    Work.BoseFixR.sincR (‖Work.BoseBoxFock.kmomLab ℓ N k‖ * r)
        * Work.BoseFixR.sincR (‖Work.BoseBoxFock.kmomLab ℓ N k‖ * s)
        / ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2
      = (ℓ ^ 2 / (4 * Real.pi ^ 2))
        * (Work.BoseFixR.sincR ((2 * Real.pi * r / ℓ) * nrm (Work.BoseBoxFock.labVec N k))
            * Work.BoseFixR.sincR ((2 * Real.pi * s / ℓ) * nrm (Work.BoseBoxFock.labVec N k))
            / (nrm (Work.BoseBoxFock.labVec N k)) ^ 2) := by
  rw [norm_kmomLab hℓ N k]
  have harg : ∀ t : ℝ, 2 * Real.pi * nrm (Work.BoseBoxFock.labVec N k) / ℓ * t
      = (2 * Real.pi * t / ℓ) * nrm (Work.BoseBoxFock.labVec N k) := by
    intro t; ring
  rw [harg r, harg s]
  rcases eq_or_ne (nrm (Work.BoseBoxFock.labVec N k)) 0 with h0 | h0
  · simp [h0]
  · field_simp
    ring

/-- **The box-lattice kernel bound** (the case `r ≤ s`), assuming the oscillatory bound
`|P(c)| ≤ 40` for `0 < c ≤ 4π`. -/
theorem labKernel_le_aux {ℓ R : ℝ} (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ) (N : ℕ)
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (hsR : s ≤ R)
    (hP : ∀ c : ℝ, 0 < c → c ≤ 4 * Real.pi → |oscillSum N c| ≤ 40) :
    labKernel ℓ N r s ≤ ℓ ^ 3 / (Real.pi * s) := by
  have ha : 0 < 2 * Real.pi * r / ℓ := by positivity
  have hab : 2 * Real.pi * r / ℓ ≤ 2 * Real.pi * s / ℓ := by gcongr
  have hb4 : 2 * Real.pi * s / ℓ ≤ 2 * Real.pi := by
    rw [div_le_iff₀ hℓ]
    nlinarith [Real.pi_pos, hsR, hRℓ]
  have hT := abs_sincKernel_le ha hab hb4 hP
  have hre : labKernel ℓ N r s
      = (ℓ ^ 2 / (4 * Real.pi ^ 2)) * sincKernel N (2 * Real.pi * r / ℓ) (2 * Real.pi * s / ℓ) := by
    have h1 : labKernel ℓ N r s
        = ∑ m ∈ (cube N).erase 0,
            (ℓ ^ 2 / (4 * Real.pi ^ 2))
              * (Work.BoseFixR.sincR ((2 * Real.pi * r / ℓ) * nrm m)
                  * Work.BoseFixR.sincR ((2 * Real.pi * s / ℓ) * nrm m) / (nrm m) ^ 2) := by
      unfold labKernel
      rw [← image_labVec_eq N, Finset.sum_image (fun x _ y _ h => labVec_inj N h)]
      exact Finset.sum_congr rfl fun k _ => labKernel_term hℓ N k r s
    have h2 : (∑ m ∈ (cube N).erase 0,
            (ℓ ^ 2 / (4 * Real.pi ^ 2))
              * (Work.BoseFixR.sincR ((2 * Real.pi * r / ℓ) * nrm m)
                  * Work.BoseFixR.sincR ((2 * Real.pi * s / ℓ) * nrm m) / (nrm m) ^ 2))
        = (ℓ ^ 2 / (4 * Real.pi ^ 2)) * sincKernel N (2 * Real.pi * r / ℓ) (2 * Real.pi * s / ℓ) := by
      rw [← Finset.mul_sum]
      congr 1
      unfold sincKernel
      have hzero : Work.BoseFixR.sincR ((2 * Real.pi * r / ℓ) * nrm 0)
            * Work.BoseFixR.sincR ((2 * Real.pi * s / ℓ) * nrm 0) / (nrm 0) ^ 2 = 0 := by
        simp [nrm]
      have := Finset.sum_erase_add (cube N)
        (fun m => Work.BoseFixR.sincR ((2 * Real.pi * r / ℓ) * nrm m)
            * Work.BoseFixR.sincR ((2 * Real.pi * s / ℓ) * nrm m) / (nrm m) ^ 2)
        (zero_mem_cube N)
      rw [hzero, add_zero] at this
      exact this
    rw [h1, h2]
  rw [hre]
  have hcoef : (0:ℝ) ≤ ℓ ^ 2 / (4 * Real.pi ^ 2) := by positivity
  calc (ℓ ^ 2 / (4 * Real.pi ^ 2)) * sincKernel N (2 * Real.pi * r / ℓ) (2 * Real.pi * s / ℓ)
      ≤ (ℓ ^ 2 / (4 * Real.pi ^ 2))
          * (8 * Real.pi ^ 2 / (2 * Real.pi * s / ℓ)) :=
        mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hT) hcoef
    _ = ℓ ^ 3 / (Real.pi * s) := by
        field_simp
        ring

/-- **The box-lattice kernel bound**, assuming the oscillatory bound `|P(c)| ≤ 40` for
`0 < c ≤ 4π`. -/
theorem labKernel_le_of_crux {ℓ R : ℝ} (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ) (N : ℕ)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrR : r ≤ R) (hsR : s ≤ R)
    (hP : ∀ c : ℝ, 0 < c → c ≤ 4 * Real.pi → |oscillSum N c| ≤ 40) :
    labKernel ℓ N r s ≤ ℓ ^ 3 / (Real.pi * max r s) := by
  rcases le_total r s with hrs | hrs
  · rw [max_eq_right hrs]
    exact labKernel_le_aux hℓ hRℓ N hr hrs hsR hP
  · rw [max_eq_left hrs]
    have hsym : labKernel ℓ N r s = labKernel ℓ N s r := by
      unfold labKernel
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsym]
    exact labKernel_le_aux hℓ hRℓ N hs hrs hrR hP

/-! ## 7. From the annulus (range) form of the oscillatory bound to the full-cube form -/

lemma nrm_le_threeN (N : ℕ) {m : Fin 3 → ℤ} (hm : m ∈ cube N) : nrm m ≤ 3 * N + 1 := by
  rw [cube, Fintype.mem_piFinset] at hm
  have h1 : ∀ i, (m i : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
    intro i
    have hi := hm i
    rw [Finset.mem_Icc] at hi
    have h2 : |((m i : ℤ) : ℝ)| ≤ (N : ℝ) := by
      rw [abs_le]
      exact_mod_cast hi
    nlinarith [abs_nonneg ((m i : ℝ)), sq_abs ((m i : ℝ)), h2]
  have h2 : (∑ i, ((m i : ℝ)) ^ 2) ≤ 3 * (N : ℝ) ^ 2 := by
    calc (∑ i, ((m i : ℝ)) ^ 2) ≤ ∑ _i : Fin 3, (N : ℝ) ^ 2 :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = 3 * (N : ℝ) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h3 : nrm m ≤ Real.sqrt (3 * (N : ℝ) ^ 2) := Real.sqrt_le_sqrt h2
  have h4 : Real.sqrt (3 * (N : ℝ) ^ 2) ≤ 3 * N + 1 := by
    have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
    have h5 : Real.sqrt 3 ≤ 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
    calc Real.sqrt (3 * (N : ℝ) ^ 2)
        = Real.sqrt 3 * N := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_sq hN]
      _ ≤ 3 * N := by nlinarith
      _ ≤ 3 * N + 1 := by linarith
  linarith

/-- The annulus (range) form of the oscillatory bound implies the full-cube form: take
`X₁ = 0`, `X₂ = 3N+1 ≥ max_{m ∈ cube} ‖m‖`. -/
theorem oscillSum_abs_of_crux
    (crux : ∀ (N : ℕ) {c X₁ X₂ : ℝ}, 0 < c → c ≤ 4 * Real.pi → X₁ ≤ X₂ →
      |∑ m ∈ cube N, (if X₁ ≤ nrm m ∧ nrm m ≤ X₂ then Real.sin (c * nrm m) / (nrm m) ^ 3
        else 0)| ≤ 40)
    (N : ℕ) (c : ℝ) (hc : 0 < c) (hc4 : c ≤ 4 * Real.pi) :
    |oscillSum N c| ≤ 40 := by
  have h := crux N hc hc4 (X₁ := 0) (X₂ := 3 * (N : ℝ) + 1) (by positivity)
  have hsum : (∑ m ∈ cube N, (if (0:ℝ) ≤ nrm m ∧ nrm m ≤ 3 * (N : ℝ) + 1
        then Real.sin (c * nrm m) / (nrm m) ^ 3 else 0)) = oscillSum N c := by
    unfold oscillSum
    exact Finset.sum_congr rfl fun m hm => by
      rw [if_pos ⟨nrm_nonneg m, nrm_le_threeN N hm⟩]
  rw [hsum] at h
  exact h

/-! ## 2. Structure of the approximating profiles `f = -2r φ'` -/

/-- A continuous function is bounded on the compact interval `[0,R]`. -/
lemma exists_bound_of_continuous {g : ℝ → ℝ} {R : ℝ} (hg : Continuous g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Icc (0:ℝ) R, |g r| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun r hr =>
    le_trans (by simpa [Real.norm_eq_abs] using hC r hr) (le_max_left _ _)⟩

/-- For a `C²` function `φ` with support inside `(-R,R)`, the profile `f = -2r φ'` is
continuous, bounded on `[0,R]` and integrable there. -/
lemma niceFacts {φ : ℝ → ℝ} {R : ℝ} (hR : 0 < R) (hφ : ContDiff ℝ 2 φ)
    (hsupp : tsupport φ ⊆ Set.Ioo (-R) R) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Icc (0:ℝ) R, |(-2 * r * deriv φ r)| ≤ C) ∧
      MeasureTheory.IntegrableOn (fun r : ℝ => -2 * r * deriv φ r) (Set.Icc (0:ℝ) R) := by
  have hcont : Continuous (fun r : ℝ => -2 * r * deriv φ r) := by
    refine Continuous.mul (Continuous.mul continuous_const continuous_id) ?_
    exact hφ.continuous_deriv (by norm_num)
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Icc (0:ℝ) R, |(-2 * r * deriv φ r)| ≤ C :=
    exists_bound_of_continuous hcont
  exact ⟨hbdd, hcont.continuousOn.integrableOn_compact isCompact_Icc⟩


end Work.BoseFixR.Rb5Lin
