import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.opArc_strata_incl_excl

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped lp BigOperators ENNReal

noncomputable section

/-- The shift `E + 0` of an arc set is the arc set itself. -/
theorem arcShift_zero (E : Finset Circle) : arcShift E 0 = E := by
  simp [arcShift]

/-- **The mixed norm `ℓ^p(ℤ; ℓ²(κ))` as an `eLpNorm`.**  For a family `g : ℤ → EuclideanSpace ℂ κ`
(the norm on `EuclideanSpace ℂ κ` is `√(Σ_t ‖·_t‖²)`), the counting-measure `L^p`-seminorm on `ℤ`
is exactly the mixed norm `(Σ'_n (Σ_t ‖g n t‖²)^{p/2})^{1/p}`.

Route: `eLpNorm_eq_lintegral_rpow_enorm_toReal` reduces the `eLpNorm` to the `lintegral` of
`‖g n‖ₑ ^ p`; on `ℤ` with the counting measure the `lintegral` is the `tsum` (`lintegral_count`),
and `‖g n‖ₑ ^ (2:ℝ) = Σ_t ofReal ‖g n t‖²` because the Euclidean norm is `√(Σ ‖·‖²)`
(`EuclideanSpace.norm_sq_eq`); the exponent is rearranged with `ENNReal.rpow_mul`. -/
theorem eLpNorm_euclidean_tsum {κ : Type*} [Fintype κ] (g : ℤ → EuclideanSpace ℂ κ) {p : ℝ}
    (hp : 1 ≤ p) :
    eLpNorm g (ENNReal.ofReal p) Measure.count
      = (∑' n : ℤ, (∑ t : κ, ENNReal.ofReal (‖g n t‖ ^ 2)) ^ (p / 2)) ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h2sq : ∀ n : ℤ, ‖g n‖ₑ ^ (2 : ℝ)
      = ∑ t : κ, ENNReal.ofReal (‖g n t‖ ^ 2) := by
    intro n
    rw [enorm_eq_nnnorm, ENNReal.rpow_two, ← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_pow, coe_nnnorm, EuclideanSpace.norm_sq_eq,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
  have hpt : ∀ n : ℤ, ‖g n‖ₑ ^ p
      = (∑ t : κ, ENNReal.ofReal (‖g n t‖ ^ 2)) ^ (p / 2) := by
    intro n
    calc ‖g n‖ₑ ^ p = ‖g n‖ₑ ^ (2 * (p / 2)) := by ring_nf
      _ = (‖g n‖ₑ ^ (2 : ℝ)) ^ (p / 2) := ENNReal.rpow_mul _ _ _
      _ = (∑ t : κ, ENNReal.ofReal (‖g n t‖ ^ 2)) ^ (p / 2) := by rw [h2sq n]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by rw [ENNReal.ofReal_ne_zero_iff]; linarith) ENNReal.ofReal_ne_top
        AEStronglyMeasurable.of_discrete,
      ENNReal.toReal_ofReal (le_of_lt hp0), lintegral_count]
  congr 1
  exact tsum_congr (fun n => hpt n)

/-- **Change of the index set in the mixed norm.**  If `e : μ ≃ κ` is a bijection of finite types,
the mixed norm of the `κ`-family `F` equals the mixed norm of the `μ`-family `u ↦ F (e u)`. -/
theorem mixedNorm_sum_equiv {κ μ : Type*} [Fintype κ] [Fintype μ] (e : μ ≃ κ)
    (F : κ → ℤ → ℝ≥0∞) {p : ℝ} :
    (∑' n : ℤ, (∑ u : μ, F (e u) n) ^ (p / 2)) ^ (1 / p)
      = (∑' n : ℤ, (∑ t : κ, F t n) ^ (p / 2)) ^ (1 / p) := by
  congr 1
  refine tsum_congr (fun n => ?_)
  congr 1
  exact Fintype.sum_equiv e (fun u : μ => F (e u) n) (fun t : κ => F t n) (fun u => rfl)

/-- The strata inclusion–exclusion step of Tao's `main`, in the mixed norm `ℓ^p(ℤ; ℓ²(κ))`: the family bound for the *strata* multipliers `Op_{φ;Σ_{A₀}}` follows, with the loss `2^{|A₀|}`, from the corresponding bounds for the *torsion* multipliers `Op_{φ;Σ_{⊆B}}`, `B ⊆ A₀`.  Indeed `opArc_strata_incl_excl` writes `Op_{φ;Σ_{A₀}} = Σ_{B ⊆ A₀} (−1)^{|A₀|−|B|} Op_{φ;Σ_{⊆B}}` (as functions, for every input; for the unshifted arcs this is the `α = 0` case of that result, using `arcShift E 0 = E`), so the `ℓ²(κ)`-norm at each `n` is at most the sum over `B ⊆ A₀` of the individual `ℓ²(κ)`-norms (triangle inequality in `ℂ^κ`), and the `ℓ^p(ℤ)`-norm of the sum is at most the sum of the `ℓ^p`-norms (triangle inequality for the `ℓ²(κ)`-valued `ℓ^p`; equivalently `Minkowski`/`eLpNorm_sum_le`).  Combined with the modulation step (`lpL2_family_arcShift_invariant`) and the Magyar–Stein–Wainger bound for the torsion multipliers this is the `‖(Op_{m;Σ_{A₀}}F_α)_α‖ ≤ O(1)^k‖(F_α)_α‖` step in Tao's proof of `main` (the "conceding a factor of `2^k`" of `ortho-apply`(ii) is exactly the `2^{|A₀|} ≤ 2^k` here). -/
theorem lpL2_family_strata_incl_excl {p : ℝ} (_hp : 1 ≤ p)
    (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    {A₀ : Finset ℕ} (hA₀ : ∀ q ∈ A₀, 2 ≤ q)
    (hcop : ∀ p' ∈ A₀, ∀ q' ∈ A₀, p' ≠ q' → Nat.Coprime p' q') {D : ℝ}
    (htor : ∀ (B : Finset ℕ), B ⊆ A₀ → ∀ {κ : Type*} [Fintype κ] (G : κ → ℤ → ℂ)
      (hG : ∀ t, Memℓp (G t) 2),
      (∑' n : ℤ, (∑ t : κ, ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opArc φ hφ
          (Work.BourgainPlan.IonescuWainger.sigmaSubAFinset B) (G t) (hG t) n‖ ^ 2))
          ^ (p / 2)) ^ (1 / p)
        ≤ ENNReal.ofReal D * (∑' n : ℤ, (∑ t : κ, ENNReal.ofReal (‖G t n‖ ^ 2))
          ^ (p / 2)) ^ (1 / p))
    {κ : Type*} [Fintype κ] (F : κ → ℤ → ℂ) (hF : ∀ t, Memℓp (F t) 2) :
    (∑' n : ℤ, (∑ t : κ, ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opArc φ hφ
        (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀) (F t) (hF t) n‖ ^ 2))
        ^ (p / 2)) ^ (1 / p)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ A₀.card * D)
        * (∑' n : ℤ, (∑ t : κ, ENNReal.ofReal (‖F t n‖ ^ 2)) ^ (p / 2)) ^ (1 / p) := by
  classical
  have hp : 1 ≤ p := _hp
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  -- The hypothesis `htor` only speaks about index types in *its own* universe.  Since `κ` is
  -- finite, we may replace it by the equivalent, universe-flexible type `ULift (Fin κ.card)`,
  -- which the elaboration is free to place in that universe.
  let μ : Type _ := ULift (Fin (Fintype.card κ))
  let e : μ ≃ κ := Equiv.ulift.trans (Fintype.equivFin κ).symm
  set R : ℝ≥0∞ := (∑' n : ℤ, (∑ t : κ, ENNReal.ofReal (‖F t n‖ ^ 2)) ^ (p / 2)) ^ (1 / p)
    with hR
  let fB : Finset ℕ → ℤ → EuclideanSpace ℂ κ :=
    fun B n => WithLp.toLp 2 (fun t : κ => opArc φ hφ (sigmaSubAFinset B) (F t) (hF t) n)
  let fS : ℤ → EuclideanSpace ℂ κ :=
    fun n => WithLp.toLp 2 (fun t : κ => opArc φ hφ (sigmaStrataFinset A₀) (F t) (hF t) n)
  have sum_apply' : ∀ (s : Finset (Finset ℕ)) (g : Finset ℕ → EuclideanSpace ℂ κ) (t : κ),
      (∑ B ∈ s, g B) t = ∑ B ∈ s, g B t := by
    intro s g t
    rw [show (∑ B ∈ s, g B) t = (∑ B ∈ s, g B).ofLp t from rfl, WithLp.ofLp_sum,
      Finset.sum_apply]
  have hpt : ∀ n, fS n = ∑ B ∈ A₀.powerset, ((-1 : ℂ) ^ (A₀.card - B.card)) • fB B n := by
    intro n
    apply PiLp.ext
    intro t
    rw [sum_apply']
    simp only [PiLp.smul_apply, smul_eq_mul]
    have h := congrFun (opArc_strata_incl_excl A₀ hA₀ hcop 0 φ hφ (F t) (hF t)) n
    simp only [arcShift_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    simpa [fS, fB] using h
  have hfun : fS = ∑ B ∈ A₀.powerset,
      (fun n : ℤ => ((-1 : ℂ) ^ (A₀.card - B.card)) • fB B n) := by
    funext n
    rw [hpt n, Finset.sum_apply]
  have hconvS : eLpNorm fS (ENNReal.ofReal p) Measure.count
      = (∑' n : ℤ, (∑ t : κ, ENNReal.ofReal (‖opArc φ hφ
          (sigmaStrataFinset A₀) (F t) (hF t) n‖ ^ 2)) ^ (p / 2)) ^ (1 / p) := by
    rw [eLpNorm_euclidean_tsum fS hp]
  have hconvB : ∀ B, eLpNorm (fB B) (ENNReal.ofReal p) Measure.count
      = (∑' n : ℤ, (∑ t : κ, ENNReal.ofReal (‖opArc φ hφ
          (sigmaSubAFinset B) (F t) (hF t) n‖ ^ 2)) ^ (p / 2)) ^ (1 / p) := by
    intro B
    rw [eLpNorm_euclidean_tsum (fB B) hp]
  rw [← hconvS, hfun]
  calc eLpNorm (∑ B ∈ A₀.powerset,
        (fun n : ℤ => ((-1 : ℂ) ^ (A₀.card - B.card)) • fB B n))
        (ENNReal.ofReal p) Measure.count
      ≤ ∑ B ∈ A₀.powerset, eLpNorm
          (fun n : ℤ => ((-1 : ℂ) ^ (A₀.card - B.card)) • fB B n)
          (ENNReal.ofReal p) Measure.count :=
        eLpNorm_sum_le hpE
    _ = ∑ B ∈ A₀.powerset, eLpNorm (fB B) (ENNReal.ofReal p) Measure.count := by
        refine Finset.sum_congr rfl (fun B _ => ?_)
        rw [show (fun n : ℤ => ((-1 : ℂ) ^ (A₀.card - B.card)) • fB B n)
              = ((-1 : ℂ) ^ (A₀.card - B.card)) • (fB B) from rfl,
          eLpNorm_const_smul ((-1 : ℂ) ^ (A₀.card - B.card)) (fB B)
            (ENNReal.ofReal p) Measure.count,
          show ‖((-1 : ℂ) ^ (A₀.card - B.card))‖ₑ = 1 from by simp, one_mul]
    _ ≤ ∑ B ∈ A₀.powerset, ENNReal.ofReal D * R := by
        refine Finset.sum_le_sum (fun B hB => ?_)
        have hh := htor B (Finset.mem_powerset.mp hB) (fun u : μ => F (e u))
          (fun u : μ => hF (e u))
        rw [hconvB B]
        rw [← mixedNorm_sum_equiv (e := e)
          (F := fun t n => ENNReal.ofReal
            (‖opArc φ hφ (sigmaSubAFinset B) (F t) (hF t) n‖ ^ 2)) (p := p)]
        refine hh.trans (mul_le_mul' le_rfl ?_)
        rw [mixedNorm_sum_equiv (e := e) (F := fun t n => ENNReal.ofReal (‖F t n‖ ^ 2))
          (p := p)]
    _ = ENNReal.ofReal ((2 : ℝ) ^ A₀.card * D) * R := by
        have hcard : ((A₀.powerset.card : ℕ) : ℝ≥0∞)
            = ENNReal.ofReal ((2 : ℝ) ^ A₀.card) := by
          rw [Finset.card_powerset, ← ENNReal.ofReal_natCast, Nat.cast_pow]
          norm_num
        rw [Finset.sum_const, nsmul_eq_mul, hcard,
          show ENNReal.ofReal ((2 : ℝ) ^ A₀.card * D)
              = ENNReal.ofReal ((2 : ℝ) ^ A₀.card) * ENNReal.ofReal D from
            ENNReal.ofReal_mul (by positivity),
          mul_assoc]

end

end Work.BourgainPlan.IonescuWainger
