import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Maximal.shift_fourier_coeff_conj
import Submission.Work.BourgainPlan.Maximal.poly_dyadic_of_model
import Submission.Work.BourgainPlan.Oscillation.oscZ_cesaro_X

/-!
# The degree-`≤ 1` lacunary oscillation inequality

For a linear polynomial `P = aX + b` the Weyl average is the arithmetic-progression average
`N⁻¹ Σ_{n<N} g (x + a n + b)`, and the residue classes of `x + b` mod `a` decompose the
`ℤ`-oscillation functional into the moving averages `F_r (m) = g (a m + r)` of the residue
classes.  Hence the degree-`≤ 1` case reduces to the moving-average case `P = X`, which is
proved separately.
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-! ## 1. The Weyl operator of a linear polynomial is an AP average -/

/-- **The Weyl operator of a linear polynomial is the arithmetic-progression average.**
For `P = a X + b` (`a b : ℤ`), `polyWeylOp P g s N x = N⁻¹ ∑_{n<N} g (x + a n + b)`. -/
theorem polyWeylOp_linear_eq' (a b : ℤ) (g : ℤ → ℂ) (s : Finset ℤ)
    (hs : ∀ n, n ∉ s → g n = 0) (N : ℕ) (x : ℤ) :
    polyWeylOp (Polynomial.C a * Polynomial.X + Polynomial.C b) g s N x
      = ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, g (x + a * (n : ℤ) + b) := by
  have heval : ∀ i : ℕ,
      (Polynomial.C a * Polynomial.X + Polynomial.C b).eval (i : ℤ) = a * (i : ℤ) + b := by
    intro i; simp
  have hLHS : (∫ θ in (0 : ℝ)..1,
        starRingEnd ℂ (Work.BourgainPlan.Maximal.polyWeylKernel
            (Polynomial.C a * Polynomial.X + Polynomial.C b) N θ) *
          (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ)))))
      = ∫ θ in (0 : ℝ)..1,
          ((((N : ℂ))⁻¹ * ∑ i ∈ Finset.range N,
              Complex.exp (-(2 * Real.pi * Complex.I *
                (((((Polynomial.C a * Polynomial.X + Polynomial.C b).eval (i : ℤ) : ℤ) : ℝ)) *
                  θ))))) *
            (∑ m ∈ s, g m * Complex.exp (2 * Real.pi * Complex.I * (((m : ℝ)) * θ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (((x : ℝ)) * θ))) := by
    apply intervalIntegral.integral_congr
    intro θ _
    simp only []
    rw [Work.BourgainPlan.Maximal.conj_polyWeylKernel]
    push_cast
    ring_nf
  have hident := Work.BourgainPlan.Maximal.shift_fourier_coeff_conj
    (Polynomial.C a * Polynomial.X + Polynomial.C b) g s hs N x
  show (∫ θ in (0 : ℝ)..1,
        starRingEnd ℂ (Work.BourgainPlan.Maximal.polyWeylKernel
            (Polynomial.C a * Polynomial.X + Polynomial.C b) N θ) *
          (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ)))))
      = ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, g (x + a * (n : ℤ) + b)
  rw [hLHS, hident]
  have hcoef : (((N : ℂ))⁻¹) = (((N : ℝ))⁻¹ : ℂ) := by congr 1
  have hsum : (∑ i ∈ Finset.range N,
        g (x + (Polynomial.C a * Polynomial.X + Polynomial.C b).eval (i : ℤ)))
      = ∑ n ∈ Finset.range N, g (x + a * (n : ℤ) + b) :=
    Finset.sum_congr rfl (fun i _ => by congr 1; rw [heval]; ring)
  rw [hcoef, hsum]

/-! ## 2. The residue class of `x + b` modulo `a` -/

/-- The residue class of `x + b` modulo `a ≥ 1`, as an element of `Fin a`. -/
def resFin (a : ℕ) (ha : 1 ≤ a) (b x : ℤ) : Fin a :=
  ⟨((x + b) % (a : ℤ)).toNat, by
    have hlt : (x + b) % (a : ℤ) < (a : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast ha)
    have h0 : 0 ≤ (x + b) % (a : ℤ) :=
      Int.emod_nonneg _ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp ha))
    omega⟩

/-- The quotient `(x + b) / a`. -/
def quoZ (a : ℕ) (b x : ℤ) : ℤ := (x + b) / (a : ℤ)

lemma resFin_coe (a : ℕ) (ha : 1 ≤ a) (b x : ℤ) :
    (((resFin a ha b x : ℕ)) : ℤ) = (x + b) % (a : ℤ) := by
  rw [resFin, Fin.val_mk,
    Int.toNat_of_nonneg (Int.emod_nonneg (x + b) (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp ha)))]

lemma resFin_key (a : ℕ) (ha : 1 ≤ a) (b x : ℤ) :
    (a : ℤ) * quoZ a b x + (((resFin a ha b x : ℕ)) : ℤ) = x + b := by
  rw [resFin, Fin.val_mk, quoZ,
    Int.toNat_of_nonneg (Int.emod_nonneg (x + b) (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp ha)))]
  linarith [Int.emod_add_mul_ediv (x + b) (a : ℤ)]

lemma resFin_injective (a : ℕ) (ha : 1 ≤ a) (b : ℤ) :
    Function.Injective (fun x : ℤ => (resFin a ha b x, quoZ a b x)) := by
  intro x y hxy
  have h0x : 0 ≤ (x + b) % (a : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp ha))
  have h0y : 0 ≤ (y + b) % (a : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp ha))
  have h1 : (x + b) % (a : ℤ) = (y + b) % (a : ℤ) := by
    have h1' : (((resFin a ha b x : ℕ)) : ℤ) = (((resFin a ha b y : ℕ)) : ℤ) := by
      have := congrArg (fun p : Fin a × ℤ => (((p.1 : ℕ)) : ℤ)) hxy
      simpa using this
    rw [resFin_coe, resFin_coe] at h1'
    exact h1'
  have h2 : quoZ a b x = quoZ a b y := congrArg Prod.snd hxy
  have hx := resFin_key a ha b x
  have hy := resFin_key a ha b y
  rw [resFin_coe a ha b x] at hx
  rw [resFin_coe a ha b y] at hy
  rw [h2] at hx
  linarith [hx, hy, h1]

/-! ## 3. Reindexing a `tsum` on `ℤ` by residue classes -/

/-- Reindexing a `tsum` on `ℤ` by the residue classes mod `a`, shifted by `b`. -/
theorem tsum_int_le_fin_shift (a : ℕ) (ha : 1 ≤ a) (b : ℤ) (H : ℤ → ℝ≥0∞) :
    ∑' x : ℤ, H x ≤ ∑ r : Fin a, ∑' m : ℤ, H ((a : ℤ) * m + (r : ℤ) - b) := by
  have hinj : Function.Injective (fun x : ℤ => (resFin a ha b x, quoZ a b x)) :=
    resFin_injective a ha b
  have hstep : ∑' x : ℤ, H x
      ≤ ∑' p : Fin a × ℤ, H ((a : ℤ) * p.2 + (p.1 : ℤ) - b) := by
    have hmain := ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun p : Fin a × ℤ => H ((a : ℤ) * p.2 + (p.1 : ℤ) - b))
    refine le_trans (le_of_eq ?_) hmain
    refine tsum_congr (fun x => ?_)
    have key : (a : ℤ) * quoZ a b x + (((resFin a ha b x : ℕ)) : ℤ) - b = x := by
      have hx := resFin_key a ha b x
      linarith [hx]
    rw [key]
  refine hstep.trans (le_of_eq ?_)
  rw [ENNReal.tsum_prod (f := fun (r : Fin a) (m : ℤ) => H ((a : ℤ) * m + (r : ℤ) - b))]
  exact tsum_fintype _

/-! ## 4. The residue decomposition of the AP-average oscillation -/

/-- **Residue decomposition.**  The block oscillation of the AP averages of `g` is bounded by
the sum, over the residue classes `r` mod `a`, of the block oscillations of the moving averages
of `F_r (m) = g (a m + r)`. -/
theorem oscZ_ap_le_sum_mv (a : ℕ) (ha : 1 ≤ a) (b : ℤ) (ρ : ℝ) :
    ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
      oscZ (fun i x => ((lacScale ρ i : ℝ)⁻¹ : ℂ) *
          ∑ n ∈ Finset.range (lacScale ρ i), g (x + (a : ℤ) * (n : ℤ) + b)) J k
        ≤ ∑ r : Fin a, oscZ (fun i m => ((lacScale ρ i : ℝ)⁻¹ : ℂ) *
            ∑ n ∈ Finset.range (lacScale ρ i),
              g ((a : ℤ) * (m + (n : ℤ)) + ((r : ℕ) : ℤ))) J k := by
  intro g s _ J k _
  have hinj : Function.Injective (fun x : ℤ => (resFin a ha b x, quoZ a b x)) :=
    resFin_injective a ha b
  have harg : ∀ (x : ℤ) (i : ℕ),
      (∑ n ∈ Finset.range (lacScale ρ i), g (x + (a : ℤ) * (n : ℤ) + b))
        = ∑ n ∈ Finset.range (lacScale ρ i),
            g ((a : ℤ) * (quoZ a b x + (n : ℤ)) + ((resFin a ha b x : ℕ) : ℤ)) := by
    intro x i
    refine Finset.sum_congr rfl (fun n _ => ?_)
    congr 1
    have hbase := resFin_key a ha b x
    rw [mul_add]
    linarith [hbase]
  have hinner : ∀ j ∈ Finset.range J,
      (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖((lacScale ρ i : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ i), g (x + (a : ℤ) * (n : ℤ) + b)
              - ((lacScale ρ (k j) : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ (k j)), g (x + (a : ℤ) * (n : ℤ) + b)‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count)
        ≤ ∑ r : Fin a, ∫⁻ m : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖((lacScale ρ i : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ i),
                  g ((a : ℤ) * (m + (n : ℤ)) + ((r : ℕ) : ℤ))
              - ((lacScale ρ (k j) : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ (k j)),
                  g ((a : ℤ) * (m + (n : ℤ)) + ((r : ℕ) : ℤ))‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count := by
    intro j _
    have hpt : ∀ x : ℤ,
        (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖((lacScale ρ i : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ i), g (x + (a : ℤ) * (n : ℤ) + b)
              - ((lacScale ρ (k j) : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ (k j)), g (x + (a : ℤ) * (n : ℤ) + b)‖ₑ) ^ (2 : ℝ)
          = (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖((lacScale ρ i : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ i),
                  g ((a : ℤ) * (quoZ a b x + (n : ℤ)) + ((resFin a ha b x : ℕ) : ℤ))
              - ((lacScale ρ (k j) : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ (k j)),
                  g ((a : ℤ) * (quoZ a b x + (n : ℤ)) + ((resFin a ha b x : ℕ) : ℤ))‖ₑ) ^ (2 : ℝ) := by
      intro x
      congr 1
      refine iSup_congr (fun i => iSup_congr (fun _ => ?_))
      rw [harg x i, harg x (k j)]
    simp only [lintegral_count]
    refine le_trans (le_of_eq (tsum_congr (fun x => hpt x))) ?_
    have := ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun p : Fin a × ℤ => (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖((lacScale ρ i : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ i),
                  g ((a : ℤ) * (p.2 + (n : ℤ)) + ((p.1 : ℕ) : ℤ))
              - ((lacScale ρ (k j) : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ (k j)),
                  g ((a : ℤ) * (p.2 + (n : ℤ)) + ((p.1 : ℕ) : ℤ))‖ₑ) ^ (2 : ℝ))
    refine this.trans (le_of_eq ?_)
    rw [ENNReal.tsum_prod (f := fun (r : Fin a) (m : ℤ) => (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖((lacScale ρ i : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ i),
                  g ((a : ℤ) * (m + (n : ℤ)) + ((r : ℕ) : ℤ))
              - ((lacScale ρ (k j) : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ (k j)),
                  g ((a : ℤ) * (m + (n : ℤ)) + ((r : ℕ) : ℤ))‖ₑ) ^ (2 : ℝ))]
    rw [tsum_fintype]
  calc oscZ (fun i x => ((lacScale ρ i : ℝ)⁻¹ : ℂ) *
        ∑ n ∈ Finset.range (lacScale ρ i), g (x + (a : ℤ) * (n : ℤ) + b)) J k
      = ∑ j ∈ Finset.range J,
          ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖((lacScale ρ i : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ i), g (x + (a : ℤ) * (n : ℤ) + b)
              - ((lacScale ρ (k j) : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ (k j)), g (x + (a : ℤ) * (n : ℤ) + b)‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count := rfl
    _ ≤ ∑ j ∈ Finset.range J, ∑ r : Fin a,
          ∫⁻ m : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖((lacScale ρ i : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ i),
                  g ((a : ℤ) * (m + (n : ℤ)) + ((r : ℕ) : ℤ))
              - ((lacScale ρ (k j) : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ (k j)),
                  g ((a : ℤ) * (m + (n : ℤ)) + ((r : ℕ) : ℤ))‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count := Finset.sum_le_sum hinner
    _ = ∑ r : Fin a, ∑ j ∈ Finset.range J,
          ∫⁻ m : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖((lacScale ρ i : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ i),
                  g ((a : ℤ) * (m + (n : ℤ)) + ((r : ℕ) : ℤ))
              - ((lacScale ρ (k j) : ℝ)⁻¹ : ℂ) *
                ∑ n ∈ Finset.range (lacScale ρ (k j)),
                  g ((a : ℤ) * (m + (n : ℤ)) + ((r : ℕ) : ℤ))‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count := Finset.sum_comm
    _ = ∑ r : Fin a, oscZ (fun i m => ((lacScale ρ i : ℝ)⁻¹ : ℂ) *
            ∑ n ∈ Finset.range (lacScale ρ i),
              g ((a : ℤ) * (m + (n : ℤ)) + ((r : ℕ) : ℤ))) J k := rfl


/-! ## 5. From the moving-average case to the AP-average case -/

/-- **The AP-average oscillation bound, given the moving-average case.** -/
theorem oscZ_ap_bound_of_cesaro (a : ℕ) (ha : 1 ≤ a) (b : ℤ) (ρ : ℝ) (hρ : 1 < ρ)
    (hX : ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
      ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
        oscZ (fun i x => polyWeylOp Polynomial.X g s (lacScale ρ i) x) J k
          ≤ ENNReal.ofReal (C^2) *
              ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
        oscZ (fun i x => ((lacScale ρ i : ℝ)⁻¹ : ℂ) *
            ∑ n ∈ Finset.range (lacScale ρ i), g (x + (a : ℤ) * (n : ℤ) + b)) J k
          ≤ ENNReal.ofReal (C^2) *
              ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨C₀, hC₀, hC₀b⟩ := hX
  have haZ : (a : ℤ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp ha)
  have hXpoly : (Polynomial.C (1:ℤ) * Polynomial.X + Polynomial.C (0:ℤ)) = Polynomial.X := by simp
  refine ⟨C₀ * (a : ℝ), by positivity, fun g s hs J k hk => ?_⟩
  refine (oscZ_ap_le_sum_mv a ha b ρ g s hs J k hk).trans ?_
  have hterm : ∀ r : Fin a,
      oscZ (fun i m => ((lacScale ρ i : ℝ)⁻¹ : ℂ) *
          ∑ n ∈ Finset.range (lacScale ρ i),
            g ((a : ℤ) * (m + (n : ℤ)) + ((r : ℕ) : ℤ))) J k
        ≤ ENNReal.ofReal (C₀ ^ 2) *
            ∫⁻ m : ℤ, ‖g ((a : ℤ) * m + ((r : ℕ) : ℤ))‖ₑ ^ (2 : ℝ)
              ∂MeasureTheory.Measure.count := by
    intro r
    set F : ℤ → ℂ := fun y => g ((a : ℤ) * y + ((r : ℕ) : ℤ)) with hF
    set s' : Finset ℤ := s.image (fun z : ℤ => (z - ((r : ℕ) : ℤ)) / (a : ℤ)) with hs'
    have hs'p : ∀ n, n ∉ s' → F n = 0 := by
      intro n hn
      by_contra hne
      have hmem : (a : ℤ) * n + ((r : ℕ) : ℤ) ∈ s := by
        by_contra hc
        exact hne (hs _ hc)
      exact hn (by
        rw [hs']
        refine Finset.mem_image.mpr ⟨(a : ℤ) * n + ((r : ℕ) : ℤ), hmem, ?_⟩
        rw [add_sub_cancel_right]
        exact Int.mul_ediv_cancel_left n haZ)
    have hc := hC₀b J k hk F s' hs'p
    have hfam : (fun i x => polyWeylOp Polynomial.X F s' (lacScale ρ i) x)
        = fun i m => ((lacScale ρ i : ℝ)⁻¹ : ℂ) *
            ∑ n ∈ Finset.range (lacScale ρ i),
              g ((a : ℤ) * (m + (n : ℤ)) + ((r : ℕ) : ℤ)) := by
      funext i m
      rw [← hXpoly]
      rw [polyWeylOp_linear_eq' 1 0 F s' hs'p (lacScale ρ i) m]
      have hsum_eq : (∑ n ∈ Finset.range (lacScale ρ i), F (m + 1 * (n : ℤ) + 0))
          = ∑ n ∈ Finset.range (lacScale ρ i),
              g ((a : ℤ) * (m + (n : ℤ)) + ((r : ℕ) : ℤ)) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [hF]
        congr 1
        ring
      rw [hsum_eq]
    rw [hfam] at hc
    simpa only [hF] using hc
  refine (Finset.sum_le_sum (fun r _ => hterm r)).trans ?_
  rw [← Finset.mul_sum]
  have hsingle : ∀ r : Fin a,
      (∫⁻ m : ℤ, ‖g ((a : ℤ) * m + ((r : ℕ) : ℤ))‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
        ≤ ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
    intro r
    rw [lintegral_count, lintegral_count]
    refine ENNReal.tsum_comp_le_tsum_of_injective
      (f := fun m : ℤ => (a : ℤ) * m + ((r : ℕ) : ℤ)) ?_
      (fun x : ℤ => ‖g x‖ₑ ^ (2 : ℝ))
    intro x y hxy
    have h : (a : ℤ) * x = (a : ℤ) * y := by
      have h' := congrArg (fun z : ℤ => z - ((r : ℕ) : ℤ)) hxy
      simpa only [add_sub_cancel_right] using h'
    exact mul_left_cancel₀ haZ h
  have hsum : (∑ r : Fin a,
        (∫⁻ m : ℤ, ‖g ((a : ℤ) * m + ((r : ℕ) : ℤ))‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count))
      ≤ (a : ℝ≥0∞) * ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
    refine (Finset.sum_le_sum (fun r _ => hsingle r)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcoef2 : ENNReal.ofReal (C₀ ^ 2) * (a : ℝ≥0∞) ≤ ENNReal.ofReal ((C₀ * (a : ℝ)) ^ 2) := by
    have h1 : ENNReal.ofReal (C₀ ^ 2) * (a : ℝ≥0∞) = ENNReal.ofReal (C₀ ^ 2 * (a : ℝ)) := by
      rw [← ENNReal.ofReal_natCast a, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C₀ ^ 2)]
    rw [h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    nlinarith [sq_nonneg C₀]
  calc ENNReal.ofReal (C₀ ^ 2) * (∑ r : Fin a,
        ∫⁻ m : ℤ, ‖g ((a : ℤ) * m + ((r : ℕ) : ℤ))‖ₑ ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count)
      ≤ ENNReal.ofReal (C₀ ^ 2) * ((a : ℝ≥0∞) *
          ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (ENNReal.ofReal (C₀ ^ 2) * (a : ℝ≥0∞)) *
          ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by rw [mul_assoc]
    _ ≤ ENNReal.ofReal ((C₀ * (a : ℝ)) ^ 2) *
          ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count :=
        mul_le_mul_of_nonneg_right hcoef2 bot_le

/-! ## 6. The target theorem -/

theorem oscZ_deg_le_one_v2 (P : Polynomial ℤ)
    (hP : Submission.BourgainPlan.NonnegOnNat P) (hd : P.natDegree ≤ 1)
    (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
        Work.BourgainPlan.Oscillation.oscZ (fun i x =>
            Work.BourgainPlan.Oscillation.polyWeylOp P g s
              (Work.BourgainPlan.Oscillation.lacScale ρ i) x) J k
          ≤ ENNReal.ofReal (C^2) *
              ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨a₀, b₀, hPab⟩ : ∃ a b : ℤ, P = Polynomial.C a * Polynomial.X + Polynomial.C b :=
    ⟨P.coeff 1, P.coeff 0, Polynomial.eq_X_add_C_of_natDegree_le_one hd⟩
  have hb₀ : 0 ≤ b₀ := by have := hP 0; rw [hPab] at this; simpa using this
  have ha₀ : 0 ≤ a₀ := by
    by_contra hcon
    have hlt : a₀ ≤ -1 := by omega
    have h := hP (b₀.natAbs + 1)
    rw [hPab] at h
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at h
    have hmpos : (0 : ℤ) ≤ (((b₀.natAbs + 1 : ℕ)) : ℤ) := by positivity
    have h1 : a₀ * (((b₀.natAbs + 1 : ℕ)) : ℤ) ≤ -((((b₀.natAbs + 1 : ℕ)) : ℤ)) := by
      have := mul_le_mul_of_nonneg_right hlt hmpos
      simpa using this
    have h2 : b₀ ≤ (b₀.natAbs : ℤ) := Int.le_natAbs
    have hmcast : (((b₀.natAbs + 1 : ℕ)) : ℤ) = (b₀.natAbs : ℤ) + 1 := by push_cast; ring
    linarith
  rcases Nat.eq_zero_or_pos a₀.toNat with hz | hpos
  · -- constant polynomial: the family is a fixed translate of `g`
    have ha0z : a₀ = 0 := by
      rw [← Int.toNat_of_nonneg ha₀, hz]
      simp
    refine ⟨1, one_pos, fun g s hs J k hk => ?_⟩
    have hfam : (fun i x => polyWeylOp P g s (lacScale ρ i) x) = fun i x => g (x + b₀) := by
      funext i x
      rw [hPab, ha0z, polyWeylOp_linear_eq' 0 b₀ g s hs (lacScale ρ i) x]
      have h1 : 1 ≤ lacScale ρ i := Nat.le_floor (by simpa using one_le_pow₀ (n := i) hρ.le)
      have hN : ((lacScale ρ i : ℝ)) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp h1)
      have hsum : (∑ n ∈ Finset.range (lacScale ρ i), g (x + 0 * (n : ℤ) + b₀))
          = (lacScale ρ i) • g (x + b₀) := by
        have hpt : ∀ n : ℕ, g (x + 0 * (n : ℤ) + b₀) = g (x + b₀) := by
          intro n
          simp only [zero_mul, add_zero]
        rw [Finset.sum_congr rfl (fun n _ => hpt n)]
        rw [Finset.sum_const, Finset.card_range]
      have hcoef : ((lacScale ρ i : ℝ)⁻¹ : ℂ) * ((lacScale ρ i : ℂ)) = 1 := by
        push_cast
        exact inv_mul_cancel₀ (by exact_mod_cast hN : (((lacScale ρ i : ℝ)) : ℂ) ≠ 0)
      rw [hsum, nsmul_eq_mul, ← mul_assoc, hcoef, one_mul]
    rw [hfam]
    have hz0 : oscZ (fun i x => g (x + b₀)) J k = 0 := by
      simp only [oscZ]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      simp
    rw [hz0]
    exact bot_le
  · -- non-constant: the AP average with slope `≥ 1`
    obtain ⟨C, hC, hCb⟩ := oscZ_ap_bound_of_cesaro a₀.toNat hpos b₀ ρ hρ (oscZ_cesaro_X ρ hρ)
    refine ⟨C, hC, fun g s hs J k hk => ?_⟩
    have hfam : (fun i x => polyWeylOp P g s (lacScale ρ i) x)
        = fun i x => ((lacScale ρ i : ℝ)⁻¹ : ℂ) *
            ∑ n ∈ Finset.range (lacScale ρ i),
              g (x + ((a₀.toNat : ℕ) : ℤ) * (n : ℤ) + b₀) := by
      funext i x
      rw [hPab, polyWeylOp_linear_eq' a₀ b₀ g s hs (lacScale ρ i) x]
      have hsum_eq : (∑ n ∈ Finset.range (lacScale ρ i), g (x + a₀ * (n : ℤ) + b₀))
          = ∑ n ∈ Finset.range (lacScale ρ i),
              g (x + ((a₀.toNat : ℕ) : ℤ) * (n : ℤ) + b₀) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        have hbase : ((a₀.toNat : ℕ) : ℤ) = a₀ := Int.toNat_of_nonneg ha₀
        rw [hbase]
      rw [hsum_eq]
    rw [hfam]
    exact hCb g s hs J k hk

end

end Work.BourgainPlan.Oscillation
