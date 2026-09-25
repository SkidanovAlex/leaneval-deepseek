import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.decouple_defs
import Submission.Work.BourgainPlan.IonescuWainger.sum_powerset_card_eq_avg
import Submission.Work.BourgainPlan.IonescuWainger.transversal_sum_aemeasurable
import Submission.Work.BourgainPlan.IonescuWainger.const_arith

/-!
# Averaging the decoupled Khintchine inequality over colourings

This file proves `Work.BourgainPlan.IonescuWainger.averaged_bound`: the (Ionescu–Wainger style)
reduction from the decoupled Khintchine inequality at a single colouring `c : S → Fin k` to the
inequality for the sum over the `k`-element subsets of `S`.

The proof is the one advertised by Bourgain/Tao.  `sum_powerset_card_eq_avg` expresses the sum over
the `k`-subsets of `S` as `k^k / (k! · k^{|S|})` times the sum over the `k^{|S|}` colourings of the
transversal sums.  The power-mean inequality turns the `2r`-th power of that `k^{|S|}`-fold sum into
`k^{|S|(2r-1)}` times the sum of the `2r`-th powers, and each transversal sum is controlled by the
(single-colouring) decoupled bound; the remaining factors collapse to `(k^k/k!)^{2r}` because the
averaging weight `k^{-|S|}` cancels against the number `k^{|S|}` of colourings.
-/

namespace Work.BourgainPlan.IonescuWainger

open scoped ENNReal BigOperators
open MeasureTheory Finset

/-- Power means for finite sums in `ℝ≥0∞` with a natural exponent: the `n`-th power of a sum is
dominated by `(card)^{n-1}` times the sum of the `n`-th powers. -/
theorem ENNReal_sum_pow_le_card_pow_mul_sum_pow {ι : Type*} [Fintype ι] (u : ι → ENNReal)
    {n : ℕ} (hn : 1 ≤ n) :
    (∑ i, u i) ^ n ≤ (Fintype.card ι : ENNReal) ^ (n - 1) * ∑ i, u i ^ n := by
  have h := ENNReal.rpow_sum_le_const_mul_sum_rpow (Finset.univ : Finset ι) u
    (p := (n : ℝ)) (by exact_mod_cast hn)
  have hc : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hn]; norm_num
  rw [hc, ENNReal.rpow_natCast, Finset.card_univ] at h
  simpa using h

/-- A transversal tuple is determined by its underlying set: `σ ↦ tupleSet S σ` is injective on
the transversal tuples of a colouring.  Consequently the square function of a single colouring is
dominated, pointwise, by the square function over all `k`-element subsets of `S`. -/
theorem sum_transversal_enorm_le {X : Type*} {α : Type*} [DecidableEq α]
    (S : Finset α) (k : ℕ) (c : S → Fin k) (f : Finset α → X → ℂ) (x : X) :
    (∑ σ ∈ transversalTuples S k c, enorm (f (tupleSet S σ) x) ^ (2 : ℝ))
      ≤ ∑ A ∈ S.powerset.filter (fun A => A.card = k), enorm (f A x) ^ (2 : ℝ) := by
  classical
  have hinj : Set.InjOn (fun σ : Fin k → S => tupleSet S σ)
      ((transversalTuples S k c : Finset (Fin k → S)) : Set (Fin k → S)) := by
    intro σ hσ σ' hσ' heq
    have heq' : tupleSet S σ = tupleSet S σ' := heq
    have hc : ∀ j, c (σ j) = j := (Finset.mem_filter.mp hσ).2
    have hc' : ∀ j, c (σ' j) = j := (Finset.mem_filter.mp hσ').2
    funext j
    have hmem : (σ j).1 ∈ tupleSet S σ' := by
      rw [← heq']; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    obtain ⟨j', -, hj'⟩ := Finset.mem_image.mp hmem
    have h1 : σ j = σ' j' := Subtype.ext hj'.symm
    have h2 : j = j' := by rw [← hc j, h1, hc' j']
    rw [h1, h2]
  rw [← Finset.sum_image (f := fun A => enorm (f A x) ^ (2 : ℝ))
    (g := fun σ : Fin k → S => tupleSet S σ) hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro A hA
    rcases Finset.mem_image.mp hA with ⟨σ, hσ, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (tupleSet_subset S σ), ?_⟩
    exact tupleSet_card_of_injective S (fun j j' h => by
      have hc : ∀ j, c (σ j) = j := (Finset.mem_filter.mp hσ).2
      have h2 : c (σ j) = c (σ j') := by rw [h]
      rwa [hc j, hc j'] at h2)
  · intro A hA hAn; exact zero_le

/-- The combinatorial identity `sum_powerset_card_eq_avg`, divided by the number
`k! · k^{|S|}` of "colouring-plus-bijection" pairs: the sum over the `k`-subsets of `S` is the
averaging weight `k^k / (k! · k^{|S|})` times the sum over all colourings of the transversal sums. -/
theorem enorm_powerset_eq {X : Type*} {α : Type*} [DecidableEq α]
    (S : Finset α) (k : ℕ) (hk : 1 ≤ k) (f : Finset α → X → ℂ) :
    ∀ x : X, enorm (∑ A ∈ S.powerset.filter (fun A => A.card = k), f A x)
      = ENNReal.ofReal (((k^k : ℕ) : ℝ) / (((k.factorial * k^S.card : ℕ)) : ℝ))
        * enorm (∑ c : S → Fin k, ∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) := by
  intro x
  have hId := sum_powerset_card_eq_avg S k hk (fun A => f A x)
  have h1 : enorm (((k.factorial * k^S.card : ℕ) : ℂ) * (∑ A ∈ S.powerset.filter (fun A => A.card = k), f A x))
      = enorm (((k^k : ℕ) : ℂ) * (∑ c : S → Fin k, ∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x)) := by
    rw [hId]
  rw [enorm_mul, enorm_mul] at h1
  rw [show enorm (((k.factorial * k^S.card : ℕ) : ℂ)) = (((k.factorial * k^S.card : ℕ)) : ENNReal) from by
        rw [← ofReal_norm, Complex.norm_natCast, ENNReal.ofReal_natCast],
      show enorm (((k^k : ℕ) : ℂ)) = (((k^k : ℕ)) : ENNReal) from by
        rw [← ofReal_norm, Complex.norm_natCast, ENNReal.ofReal_natCast]] at h1
  have hdne : (((k.factorial * k^S.card : ℕ)) : ENNReal) ≠ 0 := by
    exact_mod_cast (show k.factorial * k^S.card ≠ 0 from
      Nat.mul_ne_zero (Nat.factorial_ne_zero k) (pow_ne_zero _ (by omega)))
  have hdtop : (((k.factorial * k^S.card : ℕ)) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h2 : enorm (∑ A ∈ S.powerset.filter (fun A => A.card = k), f A x)
      = (((k.factorial * k^S.card : ℕ)) : ENNReal)⁻¹ *
        ((((k^k : ℕ)) : ENNReal) * enorm (∑ c : S → Fin k, ∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x)) := by
    calc enorm (∑ A ∈ S.powerset.filter (fun A => A.card = k), f A x)
        = ((((k.factorial * k^S.card : ℕ)) : ENNReal)⁻¹ * (((k.factorial * k^S.card : ℕ)) : ENNReal)) *
            enorm (∑ A ∈ S.powerset.filter (fun A => A.card = k), f A x) := by
          rw [ENNReal.inv_mul_cancel hdne hdtop, one_mul]
      _ = (((k.factorial * k^S.card : ℕ)) : ENNReal)⁻¹ *
            ((((k.factorial * k^S.card : ℕ)) : ENNReal) * enorm (∑ A ∈ S.powerset.filter (fun A => A.card = k), f A x)) := by
          rw [mul_assoc]
      _ = (((k.factorial * k^S.card : ℕ)) : ENNReal)⁻¹ *
            ((((k^k : ℕ)) : ENNReal) * enorm (∑ c : S → Fin k, ∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x)) := by
          rw [h1]
  rw [h2, ← mul_assoc]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (show (0:ℝ) < (((k.factorial * k^S.card : ℕ)) : ℝ) from by
        exact_mod_cast (Nat.mul_pos (Nat.factorial_pos k) (Nat.pow_pos hk))),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, mul_comm]
  rfl

/-- **Averaging over colourings.**  Suppose the (decoupled) Khintchine bound holds for every
colouring `c : S → Fin k` with constant `C₀`.  Then the same bound holds for the sum over the
`k`-element subsets of `S`, with `C₀` replaced by `C₀ · (k^k / k!)^{(2r)/k}` (the averaging weight
`k^{-|S|}` cancels against the number `k^{|S|}` of colourings).  Ingredients: the combinatorial
identity `sum_powerset_card_eq_avg` (in this workspace), the power-mean inequality
`ENNReal.rpow_sum_le_const_mul_sum_rpow` (Mathlib), the fact that a transversal tuple's underlying
`k`-set has cardinality `k` (`tupleSet_card_le`, and injectivity since the colouring separates the
coordinates), and `lintegral_finsetSum` (which needs the measurability hypothesis `hfm`). -/
theorem averaged_bound {X : Type*} [MeasurableSpace X] {α : Type*} [DecidableEq α]
    (S : Finset α) (k r : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (f : Finset α → X → ℂ)
    (μ : MeasureTheory.Measure X) {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hfm : ∀ A, A ⊆ S → A.card ≤ k → AEMeasurable (f A) μ)
    (hdec : ∀ c : S → Fin k,
      MeasureTheory.lintegral μ (fun x => enorm (∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ (2 * (r : ℝ)))
        ≤ ENNReal.ofReal (C₀ ^ (r * k)) *
          MeasureTheory.lintegral μ (fun x => (∑ σ ∈ transversalTuples S k c, enorm (f (tupleSet S σ) x) ^ (2 : ℝ)) ^ r)) :
    MeasureTheory.lintegral μ (fun x => enorm (∑ A ∈ S.powerset.filter (fun A => A.card = k), f A x) ^ (2 * (r : ℝ)))
      ≤ ENNReal.ofReal (C₀ ^ (r * k) * ((k : ℝ) ^ k / (k.factorial : ℝ)) ^ (2 * r)) *
        MeasureTheory.lintegral μ (fun x => (∑ A ∈ S.powerset.filter (fun A => A.card = k), enorm (f A x) ^ (2 : ℝ)) ^ r) := by
  classical
  set P : ℕ := 2 * r with hPdef
  have hP1 : 1 ≤ P := by omega
  have hPcast : ((P : ℕ) : ℝ) = 2 * (r : ℝ) := by rw [hPdef]; push_cast; ring
  have hdec' : ∀ c : S → Fin k,
      ∫⁻ x, enorm (∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ P ∂μ
        ≤ ENNReal.ofReal (C₀ ^ (r * k)) *
          ∫⁻ x, (∑ σ ∈ transversalTuples S k c, enorm (f (tupleSet S σ) x) ^ (2 : ℝ)) ^ r ∂μ := by
    intro c
    have h := hdec c
    have hfun : (fun x => enorm (∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ (2 * (r : ℝ)))
        = fun x => enorm (∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ P := by
      funext x
      rw [← hPcast, ENNReal.rpow_natCast]
    rwa [hfun] at h
  have hstep1 : ∫⁻ x, enorm (∑ A ∈ S.powerset.filter (fun A => A.card = k), f A x) ^ P ∂μ
      = ENNReal.ofReal (((k ^ k : ℕ) : ℝ) / ((k.factorial * k ^ S.card : ℕ) : ℝ)) ^ P
        * ∫⁻ x, enorm (∑ c : S → Fin k, ∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ P ∂μ := by
    rw [show (∫⁻ x, enorm (∑ A ∈ S.powerset.filter (fun A => A.card = k), f A x) ^ P ∂μ)
        = ∫⁻ x, ENNReal.ofReal (((k ^ k : ℕ) : ℝ) / ((k.factorial * k ^ S.card : ℕ) : ℝ)) ^ P
            * enorm (∑ c : S → Fin k, ∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ P ∂μ from
      lintegral_congr (fun x => by rw [enorm_powerset_eq S k hk f x, mul_pow])]
    rw [MeasureTheory.lintegral_const_mul']
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hstep2 : ∫⁻ x, enorm (∑ c : S → Fin k, ∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ P ∂μ
      ≤ ∫⁻ x, (Fintype.card (S → Fin k) : ENNReal) ^ (P - 1)
          * ∑ c : S → Fin k, enorm (∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ P ∂μ := by
    apply lintegral_mono
    intro x
    calc enorm (∑ c : S → Fin k, ∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ P
        ≤ (∑ c : S → Fin k, enorm (∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x)) ^ P :=
          pow_le_pow_left₀ zero_le (by
            simpa using enorm_sum_le (Finset.univ : Finset (S → Fin k))
              (fun c => ∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x)) P
      _ ≤ (Fintype.card (S → Fin k) : ENNReal) ^ (P - 1)
            * ∑ c : S → Fin k, enorm (∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ P :=
          ENNReal_sum_pow_le_card_pow_mul_sum_pow _ hP1
  have hstep3 : ∫⁻ x, (Fintype.card (S → Fin k) : ENNReal) ^ (P - 1)
          * ∑ c : S → Fin k, enorm (∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ P ∂μ
      = (Fintype.card (S → Fin k) : ENNReal) ^ (P - 1)
          * ∑ c : S → Fin k, ∫⁻ x, enorm (∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ P ∂μ := by
    rw [MeasureTheory.lintegral_const_mul' _ _ (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))]
    congr 1
    rw [MeasureTheory.lintegral_finsetSum' (Finset.univ)
      (f := fun c x => enorm (∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ P)
      (fun c _ => transversal_sum_aemeasurable S k P c f μ hfm)]
  have hstep4 : ∑ c : S → Fin k, ∫⁻ x, enorm (∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ P ∂μ
      ≤ ∑ c : S → Fin k, ENNReal.ofReal (C₀ ^ (r * k))
          * ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card = k), enorm (f A x) ^ (2 : ℝ)) ^ r ∂μ := by
    apply Finset.sum_le_sum
    intro c _
    calc ∫⁻ x, enorm (∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ P ∂μ
        ≤ ENNReal.ofReal (C₀ ^ (r * k))
            * ∫⁻ x, (∑ σ ∈ transversalTuples S k c, enorm (f (tupleSet S σ) x) ^ (2 : ℝ)) ^ r ∂μ := hdec' c
      _ ≤ ENNReal.ofReal (C₀ ^ (r * k))
            * ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card = k), enorm (f A x) ^ (2 : ℝ)) ^ r ∂μ :=
          mul_le_mul_right (lintegral_mono (fun x =>
            pow_le_pow_left₀ zero_le (sum_transversal_enorm_le S k c f x) r)) _
  have hstep5 : (∑ c : S → Fin k, ENNReal.ofReal (C₀ ^ (r * k))
          * ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card = k), enorm (f A x) ^ (2 : ℝ)) ^ r ∂μ)
      = (Fintype.card (S → Fin k) : ENNReal) * (ENNReal.ofReal (C₀ ^ (r * k))
          * ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card = k), enorm (f A x) ^ (2 : ℝ)) ^ r ∂μ) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hconst2 : ENNReal.ofReal (((k ^ k : ℕ) : ℝ) / ((k.factorial * k ^ S.card : ℕ) : ℝ)) ^ P
        * ((Fintype.card (S → Fin k) : ENNReal) ^ (P - 1) * (Fintype.card (S → Fin k) : ENNReal))
        * ENNReal.ofReal (C₀ ^ (r * k))
      = ENNReal.ofReal (C₀ ^ (r * k) * ((k : ℝ) ^ k / (k.factorial : ℝ)) ^ (2 * r)) := by
    simpa [hPdef] using const_arith S k r hk hr hC₀
  rw [show (∫⁻ x, enorm (∑ A ∈ S.powerset.filter (fun A => A.card = k), f A x) ^ (2 * (r : ℝ)) ∂μ)
      = ∫⁻ x, enorm (∑ A ∈ S.powerset.filter (fun A => A.card = k), f A x) ^ P ∂μ from
    lintegral_congr (fun x => by rw [← hPcast, ENNReal.rpow_natCast])]
  calc ∫⁻ x, enorm (∑ A ∈ S.powerset.filter (fun A => A.card = k), f A x) ^ P ∂μ
      = ENNReal.ofReal (((k ^ k : ℕ) : ℝ) / ((k.factorial * k ^ S.card : ℕ) : ℝ)) ^ P
          * ∫⁻ x, enorm (∑ c : S → Fin k, ∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ P ∂μ := hstep1
    _ ≤ ENNReal.ofReal (((k ^ k : ℕ) : ℝ) / ((k.factorial * k ^ S.card : ℕ) : ℝ)) ^ P
          * ∫⁻ x, (Fintype.card (S → Fin k) : ENNReal) ^ (P - 1)
            * ∑ c : S → Fin k, enorm (∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ P ∂μ :=
        mul_le_mul_right hstep2 _
    _ = ENNReal.ofReal (((k ^ k : ℕ) : ℝ) / ((k.factorial * k ^ S.card : ℕ) : ℝ)) ^ P
          * ((Fintype.card (S → Fin k) : ENNReal) ^ (P - 1)
            * ∑ c : S → Fin k, ∫⁻ x, enorm (∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x) ^ P ∂μ) := by
        rw [hstep3]
    _ ≤ ENNReal.ofReal (((k ^ k : ℕ) : ℝ) / ((k.factorial * k ^ S.card : ℕ) : ℝ)) ^ P
          * ((Fintype.card (S → Fin k) : ENNReal) ^ (P - 1)
            * ∑ c : S → Fin k, ENNReal.ofReal (C₀ ^ (r * k))
              * ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card = k), enorm (f A x) ^ (2 : ℝ)) ^ r ∂μ) :=
        mul_le_mul_right (mul_le_mul_right hstep4 _) _
    _ = ENNReal.ofReal (((k ^ k : ℕ) : ℝ) / ((k.factorial * k ^ S.card : ℕ) : ℝ)) ^ P
          * ((Fintype.card (S → Fin k) : ENNReal) ^ (P - 1)
            * ((Fintype.card (S → Fin k) : ENNReal) * (ENNReal.ofReal (C₀ ^ (r * k))
              * ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card = k), enorm (f A x) ^ (2 : ℝ)) ^ r ∂μ))) := by
        rw [hstep5]
    _ = (ENNReal.ofReal (((k ^ k : ℕ) : ℝ) / ((k.factorial * k ^ S.card : ℕ) : ℝ)) ^ P
          * ((Fintype.card (S → Fin k) : ENNReal) ^ (P - 1) * (Fintype.card (S → Fin k) : ENNReal))
          * ENNReal.ofReal (C₀ ^ (r * k)))
          * ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card = k), enorm (f A x) ^ (2 : ℝ)) ^ r ∂μ := by
        ring
    _ = ENNReal.ofReal (C₀ ^ (r * k) * ((k : ℝ) ^ k / (k.factorial : ℝ)) ^ (2 * r))
          * ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card = k), enorm (f A x) ^ (2 : ℝ)) ^ r ∂μ := by
        rw [hconst2]

end Work.BourgainPlan.IonescuWainger
