import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.opArc_eq_sum_singletons
import Submission.Work.BourgainPlan.IonescuWainger.OpMulLinear
import Submission.Work.BourgainPlan.IonescuWainger.comp_sum_bound_perTuple_strata
import Submission.Work.BourgainPlan.IonescuWainger.khintchine_majorArc_strata
import Submission.Work.BourgainPlan.IonescuWainger.layer_sunflower_bound_powerset

/-!
# The lower bound for the major-arc system of a single bump `φ` (`ortho-apply`(i), system form)

`ortho_apply_lower_strata_system` is the form of Tao's `ortho-apply`(i) that the Ionescu–Wainger
multiplier theorem consumes: the major-arc system is not an abstract band-limited family `f_δ` but
the explicit system `δ ↦ Op_{φ;{δ}} f = opArc φ hφ {δ} f hf` obtained from one bump `φ` and one
sequence `f`, and the strata sums carry coefficients `ε_A` (`‖ε_A‖ ≤ 1`).

The proof splits as in `ortho_apply_lower_strata`:

0. a Khintchine/square-function inequality for the *coefficient-weighted* hypersystem
   `A ↦ ε_A · f_{Σ_A}` (`khintchine_majorArc_real_strata_coeff`): the point is that the coefficients
   are constants per stratum, so they can be absorbed into a single scaled system
   `δ ↦ c(δ) · f_δ` (with `c` the stratum-wise constant extension of `ε`, well defined by the
   disjointness of the strata `Σ_A`, `A ⊆ S`) and `khintchine_majorArc_real_strata` applies; the
   square function of the scaled system is dominated by the unweighted one because `‖ε_A‖ ≤ 1`;
1. the layer-wise Erdős–Rado/sunflower bound `layer_sunflower_bound_powerset`;
2. the per-core Pythagoras `comp_sum_bound_perTuple_strata`;
3. assembly.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal lp

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **The stratum-wise extension of a family of coefficients on the subsets of `S`.**  For `δ` in the
stratum `Σ_A` (`A ⊆ S`, `|A| ≤ k`) this is `c A`; for `δ` outside `⋃_{A} Σ_A` it is `0`.  It is well
defined because the strata of distinct subsets of a pairwise coprime `S` are disjoint. -/
noncomputable def strataCoeff (S : Finset ℕ) (k : ℕ) (c : Finset ℕ → ℂ) (δ : Circle) : ℂ :=
  ∑ A ∈ (S.powerset.filter (fun A => A.card ≤ k)).filter (fun A => δ ∈ sigmaStrataFinset A), c A

/-- The defining property of `strataCoeff`: on a stratum `Σ_A` it takes the value `c A`. -/
theorem strataCoeff_eq {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) (k : ℕ) (c : Finset ℕ → ℂ)
    {A : Finset ℕ} (hA : A ∈ S.powerset.filter (fun A => A.card ≤ k))
    {α : Circle} (hα : α ∈ sigmaStrataFinset A) : strataCoeff S k c α = c A := by
  classical
  have hfilter : (S.powerset.filter (fun A => A.card ≤ k)).filter
      (fun A' => α ∈ sigmaStrataFinset A') = {A} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hA, hα⟩, ?_⟩
    intro A' hA'
    rw [Finset.mem_filter] at hA'
    obtain ⟨hA'mem, hA'α⟩ := hA'
    have hA'S : A' ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hA'mem).1
    have hAS : A ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
    exact circle_strata_disjoint h2 hS hA'S hAS hA'α hα
  rw [strataCoeff, hfilter, Finset.sum_singleton]

/-- The frequency support of a scalar multiple of a band-limited sequence. -/
theorem hasFreqSupport_const_smul {h : ℤ → ℂ} {hh : Memℓp h 2} {E : Set Circle} (c : ℂ)
    (H : HasFreqSupport h hh E) : HasFreqSupport (c • h) (hh.const_smul c) E := by
  simp only [HasFreqSupport] at H ⊢
  filter_upwards [H, Lp.coeFn_smul c (ftLp h hh)] with θ hθ hsmul
  intro hθE
  rw [ftLp_smul c hh, hsmul, Pi.smul_apply, hθ hθE, smul_zero]

/-- The multiplier over a translated arc set is the sum of the single-frequency multipliers over the
translated points. -/
theorem opArc_arcShift_eq (φ : Circle → ℂ)
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (E : Finset Circle) (α : Circle) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    opArc φ hφ (arcShift E α) f hf = ∑ γ ∈ E, opArc φ hφ {γ + α} f hf := by
  rw [opArc_eq_sum_singletons, arcShift, Finset.sum_image]
  intro a _ b _ hab
  exact add_right_cancel hab

/-- The value at `x` of the sum of the single-frequency multipliers over `E` is the sum of the values
of `Op_{φ;E}`. -/
theorem sum_singletons_apply (φ : Circle → ℂ)
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (E : Finset Circle) (f : ℤ → ℂ) (hf : Memℓp f 2) (x : ℤ) :
    (∑ β ∈ E, opArc φ hφ {β} f hf x) = opArc φ hφ E f hf x := by
  rw [← Finset.sum_apply, ← opArc_eq_sum_singletons]

/-- **The Khintchine/square-function inequality for the strata, with stratum-constant
coefficients.**  For a band-limited family `f : 𝕋 → ℓ²(ℤ)` satisfying the nonce smallness condition
and coefficients `c : binom(S,≤k) → ℂ` of modulus at most `1`,
`Σ_x ‖Σ_A c_A f_{Σ_A}(x)‖^{2r} ≤ C^{kr} Σ_x (Σ_A ‖f_{Σ_A}(x)‖²)^r`.

Route: absorb the coefficients into the system, `δ ↦ c(δ) f_δ` with `c` the stratum-wise extension
(`strataCoeff`, well defined by `circle_strata_disjoint`), apply the unweighted Khintchine
inequality `khintchine_majorArc_real_strata` to it and use `‖c_A‖ ≤ 1` to dominate the weighted
square function by the unweighted one. -/
theorem khintchine_majorArc_real_strata_coeff (k r : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
      (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
      {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
      (hF : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε))
      (hsmall : ∀ A : Fin r ⊕ Fin r → Finset ℕ, (∀ j, A j ⊆ S ∧ (A j).card ≤ k) → HasNonce A →
        2 * (r : ℝ) * ε < 1 / ((∏ j, QA (A j) : ℕ) : ℝ))
      (c : Finset ℕ → ℂ) (hc : ∀ A, ‖c A‖ ≤ 1),
      ∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          c A * (∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ (2 * r)
        ≤ C ^ (k * r) * ∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
            ‖(∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ 2) ^ r := by
  classical
  obtain ⟨C₁, hC₁pos, hkhi⟩ := khintchine_majorArc_real_strata k r hr hk
  refine ⟨C₁, hC₁pos, ?_⟩
  intro S h2 hS f hf ε hF hsmall c hc
  let G : Circle → ℤ → ℂ := fun δ => strataCoeff S k c δ • f δ
  have hGmem : ∀ δ, Memℓp (G δ) 2 :=
    fun δ => (hf δ).const_smul (strataCoeff S k c δ)
  have hGF : ∀ δ, HasFreqSupport (G δ) (hGmem δ) (arcSet δ ε) :=
    fun δ => hasFreqSupport_const_smul (strataCoeff S k c δ) (hF δ)
  have hK := hkhi (S := S) h2 hS (f := G) hGmem hGF hsmall
  -- the pointwise identification of the strata sums of the scaled system
  have hpoint : ∀ A ∈ S.powerset.filter (fun A => A.card ≤ k), ∀ x : ℤ,
      (∑ α ∈ sigmaStrataFinset A, G α x) = c A * (∑ α ∈ sigmaStrataFinset A, f α x) := by
    intro A hA x
    have h1 : (∑ α ∈ sigmaStrataFinset A, G α x)
        = ∑ α ∈ sigmaStrataFinset A, strataCoeff S k c α * f α x := by
      refine Finset.sum_congr rfl (fun α _ => ?_)
      show strataCoeff S k c α • f α x = strataCoeff S k c α * f α x
      rw [smul_eq_mul]
    rw [h1]
    have h2' : (∑ α ∈ sigmaStrataFinset A, strataCoeff S k c α * f α x)
        = ∑ α ∈ sigmaStrataFinset A, c A * f α x :=
      Finset.sum_congr rfl (fun α hα => by rw [strataCoeff_eq h2 hS k c hA hα])
    rw [h2', Finset.mul_sum]
  have hLHS : (∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∑ α ∈ sigmaStrataFinset A, G α x‖ ^ (2 * r))
      = ∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        c A * (∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ (2 * r) := by
    refine tsum_congr (fun x => ?_)
    rw [show (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          ∑ α ∈ sigmaStrataFinset A, G α x)
        = ∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          c A * (∑ α ∈ sigmaStrataFinset A, f α x) from
      Finset.sum_congr rfl (fun A hA => hpoint A hA x)]
  rw [hLHS] at hK
  -- the square function of the scaled system is dominated by the unweighted one
  have hsq : ∀ x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        ‖(∑ α ∈ sigmaStrataFinset A, G α x)‖ ^ 2)
      ≤ (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        ‖(∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ 2) := by
    intro x
    refine Finset.sum_le_sum (fun A hA => ?_)
    rw [hpoint A hA x, norm_mul, mul_pow]
    have h1 : ‖c A‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (c A), hc A]
    calc ‖c A‖ ^ 2 * ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2
        ≤ 1 * ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2 := one_mul _
  have hsumG : Summable fun x : ℤ => (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
      ‖∑ α ∈ sigmaStrataFinset A, G α x‖ ^ 2) ^ r :=
    summable_powerset_rpow_strata (S := S) (f := G) hGmem k r hr
  have hsumf : Summable fun x : ℤ => (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
      ‖∑ α ∈ sigmaStrataFinset A, f α x‖ ^ 2) ^ r :=
    summable_powerset_rpow_strata (S := S) (f := f) hf k r hr
  refine hK.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hC₁pos.le _))
  exact Summable.tsum_le_tsum
    (fun x => pow_le_pow_left₀ (Finset.sum_nonneg (fun A _ => sq_nonneg _)) (hsq x) r)
    hsumG hsumf

end

end Work.BourgainPlan.IonescuWainger

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **Tao's `ortho-apply`(i) in the system form with coefficients.**  The abstract band-limited
system of `ortho_apply_lower_strata` is kept, but the strata sums carry coefficients `c A`,
`‖c A‖ ≤ 1`.  The proof is that of `ortho_apply_lower_strata` with the unweighted Khintchine
inequality replaced by `khintchine_majorArc_real_strata_coeff`. -/
theorem ortho_apply_lower_strata_coeff (k r : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
      (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
      {M : ℕ} (hM : 2 ≤ M)
      (hsun : ∀ T : Finset (Finset ℕ), (∀ A ∈ T, A ⊆ S) → (∀ A ∈ T, A.card ≤ k) → M ≤ T.card →
        ∃ A : Fin r → Finset ℕ, (∀ i, A i ∈ T) ∧ Function.Injective A ∧ IsSunflower A)
      {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
      (hF : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε))
      (hsmallN : ∀ A : Fin r ⊕ Fin r → Finset ℕ, (∀ j, A j ⊆ S ∧ (A j).card ≤ k) → HasNonce A →
        2 * (r : ℝ) * ε < 1 / ((∏ j, QA (A j) : ℕ) : ℝ))
      (hsmallP : ∀ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∀ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
          (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1)) →
          2 * (r : ℝ) * ε * ((QA A₀ * (∏ i, QA ((A i).1)) : ℕ) : ℝ) < 1)
      (c : Finset ℕ → ℂ) (hc : ∀ A, ‖c A‖ ≤ 1),
      ∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          c A * (∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ (2 * r)
        ≤ C ^ (k * r) * (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
            ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
              ∑' x : ℤ, (∑ α ∈ strataCompFinset S k A₀,
                ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + α) x)‖ ^ 2) ^ r := by
  classical
  obtain ⟨C₁, hC₁pos, hkhi⟩ := khintchine_majorArc_real_strata_coeff k r (by omega) hk
  refine ⟨max 1 C₁, lt_max_of_lt_left one_pos, ?_⟩
  intro S h2 hS M hM hsun f hf ε hF hsmallN hsmallP c hc
  -- (0) the coefficient-weighted Khintchine / square-function bound
  have hK : (∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        c A * (∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ (2 * r))
      ≤ C₁ ^ (k * r) * (∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        ‖(∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ 2) ^ r) :=
    hkhi (S := S) h2 hS hf hF hsmallN c hc
  -- (1) the layer-wise sunflower bound
  have hL : (∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        ‖(∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ 2) ^ r)
      ≤ (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
              (if (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1))
               then ∑' x : ℤ, ∏ i, ‖(∑ α ∈ sigmaStrataFinset (A₀ ∪ (A i).1), f α x)‖ ^ 2
               else 0) :=
    layer_sunflower_bound_powerset (S := S) (k := k) (r := r) (M := M) hr hM hsun
      (f := fun A x => ∑ α ∈ sigmaStrataFinset A, f α x)
      (fun A => Memℓp.finsetSum (sigmaStrataFinset A) (fun α _ => hf α))
  -- (2) the per-core rearrangement
  have hP : (∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∑ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
          (if (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1))
           then ∑' x : ℤ, ∏ i, ‖(∑ α ∈ sigmaStrataFinset (A₀ ∪ (A i).1), f α x)‖ ^ 2
           else 0))
      ≤ ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
          ∑' x : ℤ,
            (∑ α ∈ strataCompFinset S k A₀,
              ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + α) x)‖ ^ 2) ^ r := by
    refine Finset.sum_le_sum (fun A₀ hA₀ => ?_)
    exact comp_sum_bound_perTuple_strata (S := S) (k := k) (r := r) (by omega) h2 hS
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hA₀).1) (f := f) hf (ε := ε) hF
      (hsmallP A₀ hA₀)
  have hSumnn : 0 ≤ ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∑' x : ℤ,
          (∑ α ∈ strataCompFinset S k A₀,
            ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + α) x)‖ ^ 2) ^ r :=
    Finset.sum_nonneg (fun A₀ _ => tsum_nonneg (fun x =>
      pow_nonneg (Finset.sum_nonneg (fun α _ => sq_nonneg _)) r))
  -- (3) assembly
  have hX : (∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        ‖(∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ 2) ^ r)
      ≤ (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑' x : ℤ,
              (∑ α ∈ strataCompFinset S k A₀,
                ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + α) x)‖ ^ 2) ^ r :=
    hL.trans (mul_le_mul_of_nonneg_left hP (by positivity))
  calc (∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        c A * (∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ (2 * r))
      ≤ C₁ ^ (k * r) * (∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          ‖(∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ 2) ^ r) := hK
    _ ≤ C₁ ^ (k * r) * ((k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑' x : ℤ,
              (∑ α ∈ strataCompFinset S k A₀,
                ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + α) x)‖ ^ 2) ^ r) :=
        mul_le_mul_of_nonneg_left hX (pow_nonneg hC₁pos.le _)
    _ ≤ (max 1 C₁) ^ (k * r) * ((k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑' x : ℤ,
              (∑ α ∈ strataCompFinset S k A₀,
                ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + α) x)‖ ^ 2) ^ r) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC₁pos.le (le_max_right 1 C₁) (k * r))
          (mul_nonneg (by positivity) hSumnn)
    _ = (max 1 C₁) ^ (k * r) * (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑' x : ℤ,
              (∑ α ∈ strataCompFinset S k A₀,
                ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + α) x)‖ ^ 2) ^ r := by ring

end

end Work.BourgainPlan.IonescuWainger

namespace Work.IonescuWainger

set_option maxHeartbeats 1000000

theorem ortho_apply_lower_strata_system (k r : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
      (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
      {M : ℕ} (hM : 2 ≤ M)
      (hsun : ∀ T : Finset (Finset ℕ), (∀ A ∈ T, A ⊆ S) → (∀ A ∈ T, A.card ≤ k) → M ≤ T.card →
        ∃ A : Fin r → Finset ℕ, (∀ i, A i ∈ T) ∧ Function.Injective A ∧
          Work.BourgainPlan.IonescuWainger.IsSunflower A)
      (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {ε : ℝ}
      (f : ℤ → ℂ) (hf : Memℓp f 2)
      (hFsupp : ∀ δ : Work.BourgainPlan.IonescuWainger.Circle,
        Work.BourgainPlan.IonescuWainger.HasFreqSupport
          (Work.BourgainPlan.IonescuWainger.opArc φ hφ {δ} f hf)
          (Work.BourgainPlan.IonescuWainger.opMul_memℓp
            (Work.BourgainPlan.IonescuWainger.arcSymbolLp φ hφ {δ}) f hf)
          (Work.BourgainPlan.IonescuWainger.arcSet δ ε))
      (hsmallN : ∀ A : Fin r ⊕ Fin r → Finset ℕ, (∀ j, A j ⊆ S ∧ (A j).card ≤ k) →
        Work.BourgainPlan.IonescuWainger.HasNonce A →
        2 * (r : ℝ) * ε < 1 / ((∏ j, Work.BourgainPlan.IonescuWainger.QA (A j) : ℕ) : ℝ))
      (hsmallP : ∀ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∀ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
          (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1)) →
          2 * (r : ℝ) * ε * ((Work.BourgainPlan.IonescuWainger.QA A₀ *
            (∏ i, Work.BourgainPlan.IonescuWainger.QA ((A i).1)) : ℕ) : ℝ) < 1)
      (εs : Finset ℕ → ℂ) (hεs : ∀ A, ‖εs A‖ ≤ 1),
      ∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          εs A * Work.BourgainPlan.IonescuWainger.opArc φ hφ
            (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A) f hf x‖ ^ (2 * r)
        ≤ C ^ (k * r) * (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
            ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
              ∑' x : ℤ, (∑ α ∈ Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀,
                ‖Work.BourgainPlan.IonescuWainger.opArc φ hφ
                  (Work.BourgainPlan.IonescuWainger.arcShift
                    (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀) α) f hf x‖ ^ 2) ^ r := by
  classical
  obtain ⟨C, hCpos, hC⟩ :=
    Work.BourgainPlan.IonescuWainger.ortho_apply_lower_strata_coeff k r hr hk
  refine ⟨C, hCpos, ?_⟩
  intro S h2 hS M hM hsun φ hφ ε f hf hFsupp hsmallN hsmallP εs hεs
  let sys : Work.BourgainPlan.IonescuWainger.Circle → ℤ → ℂ :=
    fun δ => Work.BourgainPlan.IonescuWainger.opArc φ hφ {δ} f hf
  have hsys : ∀ δ, Memℓp (sys δ) 2 := fun δ =>
    Work.BourgainPlan.IonescuWainger.opMul_memℓp
      (Work.BourgainPlan.IonescuWainger.arcSymbolLp φ hφ {δ}) f hf
  have hsysF : ∀ δ, Work.BourgainPlan.IonescuWainger.HasFreqSupport (sys δ) (hsys δ)
      (Work.BourgainPlan.IonescuWainger.arcSet δ ε) := fun δ => hFsupp δ
  have hmain := hC h2 hS hM hsun hsys hsysF hsmallN hsmallP εs hεs
  have hsys_eq : ∀ (A : Finset ℕ) (x : ℤ),
      (∑ α ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A, sys α x)
        = Work.BourgainPlan.IonescuWainger.opArc φ hφ
            (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A) f hf x := by
    intro A x
    rw [show (∑ α ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A, sys α x)
        = (∑ α ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A,
            Work.BourgainPlan.IonescuWainger.opArc φ hφ {α} f hf x) from rfl]
    rw [← Finset.sum_apply, ← Work.BourgainPlan.IonescuWainger.opArc_eq_sum_singletons]
  have hshift_eq : ∀ (A₀ : Finset ℕ) (α : Work.BourgainPlan.IonescuWainger.Circle) (x : ℤ),
      (∑ γ ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀, sys (γ + α) x)
        = Work.BourgainPlan.IonescuWainger.opArc φ hφ
            (Work.BourgainPlan.IonescuWainger.arcShift
              (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀) α) f hf x := by
    intro A₀ α x
    rw [show (∑ γ ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀, sys (γ + α) x)
        = (∑ γ ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀,
            Work.BourgainPlan.IonescuWainger.opArc φ hφ {γ + α} f hf x) from rfl]
    rw [← Finset.sum_apply,
      ← Work.BourgainPlan.IonescuWainger.opArc_arcShift_eq φ hφ
        (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀) α f hf]
  have hLHS : (∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        εs A * (∑ α ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A, sys α x)‖ ^ (2 * r))
      = ∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        εs A * Work.BourgainPlan.IonescuWainger.opArc φ hφ
          (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A) f hf x‖ ^ (2 * r) := by
    refine tsum_congr (fun x => ?_)
    rw [show (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          εs A * (∑ α ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A, sys α x))
        = ∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          εs A * Work.BourgainPlan.IonescuWainger.opArc φ hφ
            (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A) f hf x from
      Finset.sum_congr rfl (fun A _ => by rw [hsys_eq A x])]
  have hRHS : (∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∑' x : ℤ, (∑ α ∈ Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀,
          ‖(∑ γ ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀, sys (γ + α) x)‖ ^ 2) ^ r)
      = ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∑' x : ℤ, (∑ α ∈ Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀,
          ‖Work.BourgainPlan.IonescuWainger.opArc φ hφ
            (Work.BourgainPlan.IonescuWainger.arcShift
              (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀) α) f hf x‖ ^ 2) ^ r := by
    refine Finset.sum_congr rfl (fun A₀ _ => ?_)
    refine tsum_congr (fun x => ?_)
    rw [show (∑ α ∈ Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀,
          ‖(∑ γ ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀, sys (γ + α) x)‖ ^ 2)
        = ∑ α ∈ Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀,
          ‖Work.BourgainPlan.IonescuWainger.opArc φ hφ
            (Work.BourgainPlan.IonescuWainger.arcShift
              (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀) α) f hf x‖ ^ 2 from
      Finset.sum_congr rfl (fun α _ => by rw [hshift_eq A₀ α x])]
  rw [hLHS, hRHS] at hmain
  exact hmain


end Work.IonescuWainger
