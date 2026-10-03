import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.khintchine_hilbert_lower_fintype

open Finset
open scoped ENNReal
set_option maxHeartbeats 800000

namespace Work.BourgainPlan.IonescuWainger

/-! ## Rademacher (Khintchine) bounds, finite-type form

Auxiliary facts for `rademacher_two_stage_lower`: the `ENNReal`-valued norm conversions and the
real-valued two-stage lower bound obtained by running Khintchine's inequality twice.

The general-`Fintype` lower half of Khintchine's inequality (with Hilbert-space values) is
`Work.BourgainPlan.IonescuWainger.khintchine_hilbert_lower_fintype`, proved in the companion module
`Submission.Work.BourgainPlan.IonescuWainger.khintchine_hilbert_lower_fintype`. -/

/-- `‖z‖ₑ ^ 2 = ofReal (‖z‖ ^ 2)` for a complex number. -/
private lemma enorm_rpow_two (z : ℂ) : ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [show ‖z‖ₑ = ENNReal.ofReal ‖z‖ from by simp [enorm]]
  exact (ENNReal.rpow_natCast (ENNReal.ofReal ‖z‖) 2).trans
    (ENNReal.ofReal_pow (norm_nonneg z) 2).symm

/-- `ofReal (‖z‖ ^ q) = ‖z‖ₑ ^ q` for `q ≥ 0` and `z : ℂ`. -/
private lemma ofReal_norm_rpow (z : ℂ) {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal (‖z‖ ^ q) = ‖z‖ₑ ^ q := by
  rw [show ‖z‖ₑ = ENNReal.ofReal ‖z‖ from by simp [enorm]]
  exact (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg z) hq).symm

private theorem real_bound (p : ℝ) (hp : 1 ≤ p) (c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2)
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (a : ι → κ → ℂ)
    (hK1 : ∀ (y : ι → ℂ),
      c1 * (∑ i, ‖y i‖ ^ 2) ^ ((1 : ℝ) / 2) ≤
        ((∑ ε : ι → Bool, ‖∑ i, (if ε i then (1 : ℂ) else -1) • y i‖ ^ p) /
          (Fintype.card (ι → Bool) : ℝ)) ^ ((1 : ℝ) / p))
    (hK2 : ∀ (y : κ → EuclideanSpace ℂ ι),
      c2 * (∑ t, ‖y t‖ ^ 2) ^ ((1 : ℝ) / 2) ≤
        ((∑ η : κ → Bool, ‖∑ t, (if η t then (1 : ℂ) else -1) • y t‖ ^ p) /
          (Fintype.card (κ → Bool) : ℝ)) ^ ((1 : ℝ) / p)) :
    c1 ^ p * c2 ^ p * (∑ i, ∑ t, ‖a i t‖ ^ 2) ^ (p / 2) ≤
      (∑ ε : ι → Bool, ∑ η : κ → Bool,
          ‖∑ i, ∑ t, (if ε i then (1 : ℂ) else -1) * (if η t then (1 : ℂ) else -1) * a i t‖ ^ p)
        / ((Fintype.card (ι → Bool) : ℝ) * (Fintype.card (κ → Bool) : ℝ)) := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hKι : (0:ℝ) < (Fintype.card (ι → Bool) : ℝ) := by
    have h : 0 < Fintype.card (ι → Bool) := Fintype.card_pos_iff.mpr ⟨fun _ => true⟩
    exact_mod_cast h
  have hKκ : (0:ℝ) < (Fintype.card (κ → Bool) : ℝ) := by
    have h : 0 < Fintype.card (κ → Bool) := Fintype.card_pos_iff.mpr ⟨fun _ => true⟩
    exact_mod_cast h
  set A2 : ℝ := ∑ i, ∑ t, ‖a i t‖ ^ 2 with hA2
  set b : (κ → Bool) → ι → ℂ := fun η i => ∑ t, (if η t then (1 : ℂ) else -1) * a i t with hb
  set V : ℝ := ∑ η : κ → Bool, (∑ i, ‖b η i‖ ^ 2) ^ (p / 2) with hV
  set U : ℝ := ∑ ε : ι → Bool, ∑ η : κ → Bool,
      ‖∑ i, ∑ t, (if ε i then (1 : ℂ) else -1) * (if η t then (1 : ℂ) else -1) * a i t‖ ^ p
    with hU
  have hA2nn : 0 ≤ A2 := by rw [hA2]; positivity
  have hstep1 : ∀ η : κ → Bool,
      c1 ^ p * (∑ i, ‖b η i‖ ^ 2) ^ (p / 2)
        ≤ (∑ ε : ι → Bool,
            ‖∑ i, ∑ t, (if ε i then (1 : ℂ) else -1) * (if η t then (1 : ℂ) else -1) * a i t‖ ^ p)
          / (Fintype.card (ι → Bool) : ℝ) := by
    intro η
    have h := hK1 (b η)
    have hsum : ∀ ε : ι → Bool,
        (∑ i, (if ε i then (1 : ℂ) else -1) • b η i)
          = ∑ i, ∑ t, (if ε i then (1 : ℂ) else -1) * (if η t then (1 : ℂ) else -1) * a i t := by
      intro ε
      apply Finset.sum_congr rfl
      intro i _
      simp only [hb]
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t _ => by rw [mul_assoc])
    simp only [hsum] at h
    have hBnn : 0 ≤ ∑ i, ‖b η i‖ ^ 2 := by positivity
    have hRnn : 0 ≤ (∑ ε : ι → Bool,
          ‖∑ i, ∑ t, (if ε i then (1 : ℂ) else -1) * (if η t then (1 : ℂ) else -1)
            * a i t‖ ^ p) / (Fintype.card (ι → Bool) : ℝ) := by positivity
    have h1 := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ c1 * (∑ i, ‖b η i‖ ^ 2) ^ ((1:ℝ)/2))
      h hp0.le
    have h2 : (c1 * (∑ i, ‖b η i‖ ^ 2) ^ ((1 : ℝ)/2)) ^ p
        = c1 ^ p * (∑ i, ‖b η i‖ ^ 2) ^ (p / 2) := by
      rw [Real.mul_rpow hc1.le (Real.rpow_nonneg hBnn _), ← Real.rpow_mul hBnn,
        show (1:ℝ)/2 * p = p/2 by ring]
    have h3 : (((∑ ε : ι → Bool,
          ‖∑ i, ∑ t, (if ε i then (1 : ℂ) else -1) * (if η t then (1 : ℂ) else -1)
            * a i t‖ ^ p) / (Fintype.card (ι → Bool) : ℝ)) ^ ((1:ℝ)/p)) ^ p
        = (∑ ε : ι → Bool,
          ‖∑ i, ∑ t, (if ε i then (1 : ℂ) else -1) * (if η t then (1 : ℂ) else -1)
            * a i t‖ ^ p) / (Fintype.card (ι → Bool) : ℝ) := by
      rw [← Real.rpow_mul hRnn,
        show (1:ℝ)/p * p = 1 by rw [one_div, inv_mul_cancel₀ hpne], Real.rpow_one]
    rw [h2, h3] at h1
    exact h1
  set x : κ → EuclideanSpace ℂ ι :=
    fun t => (WithLp.equiv 2 (ι → ℂ)).symm (fun i => a i t) with hx
  have hxnorm : ∀ t : κ, ‖x t‖ ^ 2 = ∑ i, ‖a i t‖ ^ 2 := by
    intro t
    simp only [hx]
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl (fun i _ => by simp)
  have hYpt : ∀ η : κ → Bool, ∀ i : ι,
      ((∑ t, (if η t then (1 : ℂ) else -1) • x t : EuclideanSpace ℂ ι)).ofLp i = b η i := by
    intro η i
    rw [WithLp.ofLp_sum]
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro t _
    rw [PiLp.smul_apply]
    simp [hx, smul_eq_mul]
  have hynorm : ∀ η : κ → Bool,
      ‖∑ t, (if η t then (1 : ℂ) else -1) • x t‖ ^ p = (∑ i, ‖b η i‖ ^ 2) ^ (p / 2) := by
    intro η
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_rpow]
    have hpt : ∀ i : ι,
        ‖((∑ t, (if η t then (1 : ℂ) else -1) • x t : EuclideanSpace ℂ ι)).ofLp i‖ = ‖b η i‖ :=
      fun i => by rw [hYpt η i]
    simp only [hpt]
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ ∑ i, ‖b η i‖ ^ 2)]
    congr 1
    ring
  have hstep2 : c2 ^ p * A2 ^ (p / 2) ≤ V / (Fintype.card (κ → Bool) : ℝ) := by
    have h := hK2 x
    have h1 : (∑ t : κ, ‖x t‖ ^ 2) = A2 := by
      rw [hA2]
      rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => hxnorm t)]
      exact Finset.sum_comm
    have h2 : (∑ η : κ → Bool, ‖∑ t, (if η t then (1 : ℂ) else -1) • x t‖ ^ p) = V := by
      rw [hV]
      exact Finset.sum_congr rfl (fun η _ => hynorm η)
    rw [h1, h2] at h
    have h3 := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ c2 * A2 ^ ((1:ℝ)/2)) h hp0.le
    have h4 : (c2 * A2 ^ ((1 : ℝ)/2)) ^ p = c2 ^ p * A2 ^ (p / 2) := by
      rw [Real.mul_rpow hc2.le (Real.rpow_nonneg hA2nn _), ← Real.rpow_mul hA2nn,
        show (1:ℝ)/2 * p = p/2 by ring]
    have h5 : ((V / (Fintype.card (κ → Bool) : ℝ)) ^ ((1:ℝ)/p)) ^ p
        = V / (Fintype.card (κ → Bool) : ℝ) := by
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ V / (Fintype.card (κ → Bool) : ℝ)),
        show (1:ℝ)/p * p = 1 by rw [one_div, inv_mul_cancel₀ hpne], Real.rpow_one]
    rw [h4, h5] at h3
    exact h3
  have hsum1 : c1 ^ p * V ≤ U / (Fintype.card (ι → Bool) : ℝ) := by
    have h := Finset.sum_le_sum (fun η (_ : η ∈ Finset.univ) => hstep1 η)
    have e1 : (∑ η : κ → Bool, c1 ^ p * (∑ i, ‖b η i‖ ^ 2) ^ (p / 2)) = c1 ^ p * V := by
      rw [hV, Finset.mul_sum]
    have e2 : (∑ η : κ → Bool,
          (∑ ε : ι → Bool, ‖∑ i, ∑ t, (if ε i then (1 : ℂ) else -1)
            * (if η t then (1 : ℂ) else -1) * a i t‖ ^ p)
            / (Fintype.card (ι → Bool) : ℝ)) = U / (Fintype.card (ι → Bool) : ℝ) := by
      rw [← Finset.sum_div, hU, Finset.sum_comm]
    rw [e1, e2] at h
    exact h
  have hc1p : 0 ≤ c1 ^ p := Real.rpow_nonneg hc1.le p
  calc c1 ^ p * c2 ^ p * A2 ^ (p / 2)
      = c1 ^ p * (c2 ^ p * A2 ^ (p / 2)) := by ring
    _ ≤ c1 ^ p * (V / (Fintype.card (κ → Bool) : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep2 hc1p
    _ = c1 ^ p * V / (Fintype.card (κ → Bool) : ℝ) := by ring
    _ ≤ (U / (Fintype.card (ι → Bool) : ℝ)) / (Fintype.card (κ → Bool) : ℝ) :=
        div_le_div_of_nonneg_right hsum1 hKκ.le
    _ = U / ((Fintype.card (ι → Bool) : ℝ) * (Fintype.card (κ → Bool) : ℝ)) := by
        rw [div_div]

/-- **Two-stage Rademacher (Khintchine) lower bound.** For every `p ≥ 1` there is `c > 0` such that
for every finite index type `ι`, every finite index type `κ` and every `a : ι → κ → ℂ`,

`c * (Σ_{i,t} ‖a i t‖²)^{p/2} ≤ avg_{ε : ι→Bool} avg_{η : κ→Bool} |Σ_{i,t} ε_i η_t a_{i,t}|^p`,

where `‖z‖ₑ` is the `ENNReal`-valued norm and the average is the sum over all sign choices divided
by the number `2^|ι| · 2^|κ|` of sign choices (written `(card (ι→Bool) * card (κ→Bool))⁻¹` in
`ENNReal`).  The constant `c` is uniform in `ι`, `κ` and `a`.  `ENNReal` is written out because the
notation `ℝ≥0∞` is scoped (`open scoped ENNReal`); the `DecidableEq` hypotheses are only there so
that `Fintype (ι → Bool)`, `Fintype (κ → Bool)` are available for the sums (callers pass them via
`classical`).

TOOL: the module `Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert` (namespace
`Commons.Analysis.Walsh`; add `import Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert`)
proves the two-sided Rademacher/Khintchine inequality, with constants uniform in the number of
terms, for Hilbert-space-valued sums: for `p ≥ 1` there are `c, C > 0` with
`c (Σᵢ ‖xᵢ‖²)^{1/2} ≤ (2^{-n} Σ_{ε} ‖Σᵢ εᵢ•xᵢ‖^p)^{1/p} ≤ C p^{1/2} (Σᵢ ‖xᵢ‖²)^{1/2}` for all
`n` and `x : Fin n → H`, `H` a Hilbert space over `ℂ`.  It is used twice here: once in the `κ`
variable with the Hilbert space `H = EuclideanSpace ℂ ι` (so that `‖x_t‖ = (Σ_i ‖a i t‖²)^{1/2}`
and `‖Σ_t η_t • x_t‖ = (Σ_i ‖Σ_t η_t a i t‖²)^{1/2}`, by `EuclideanSpace.norm_eq`) and once, for
each fixed `η`, in the scalar `ι` variable with `H = ℂ`.  The general-`Fintype` index sets can be
reduced to `Fin n` with `Fintype.equivFin` / `Fintype.sum_equiv` / `Equiv.arrowCongr`.  Everything
is finite, so the `ENNReal` statement follows from the real one by `ENNReal.ofReal_sum_of_nonneg`,
`ENNReal.ofReal_pow`, `ENNReal.ofReal_rpow_of_nonneg`, `ENNReal.ofReal_mul`,
`ENNReal.ofReal_div_of_pos`, `ofReal_norm_eq_enorm`, `ENNReal.rpow_two`, `ENNReal.ofReal_natCast`,
`ENNReal.div_eq_inv_mul`, `ENNReal.mul_inv_cancel`/`ENNReal.inv_mul_cancel`. -/
theorem rademacher_two_stage_lower (p : ℝ) (hp : 1 ≤ p) :
    ∃ c : ℝ, 0 < c ∧ ∀ {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
      (a : ι → κ → ℂ),
      ENNReal.ofReal c * (∑ i, ∑ t, ‖a i t‖ₑ ^ (2 : ℝ)) ^ (p / 2) ≤
        (∑ ε : ι → Bool, ∑ η : κ → Bool,
            ‖∑ i, ∑ t, (if ε i then (1 : ℂ) else -1) * (if η t then (1 : ℂ) else -1)
              * a i t‖ₑ ^ p)
          * ((Fintype.card (ι → Bool) : ENNReal) * (Fintype.card (κ → Bool) : ENNReal))⁻¹ := by
  obtain ⟨c1, hc1, hK1⟩ := khintchine_hilbert_lower_fintype p hp
  obtain ⟨c2, hc2, hK2⟩ := khintchine_hilbert_lower_fintype p hp
  refine ⟨c1 ^ p * c2 ^ p, mul_pos (Real.rpow_pos_of_pos hc1 p) (Real.rpow_pos_of_pos hc2 p), ?_⟩
  intro ι κ _ _ _ _ a
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hhalf : 0 ≤ p / 2 := by linarith
  have hreal := real_bound p hp c1 c2 hc1 hc2 a (fun y => hK1 y) (fun y => hK2 y)
  have hA2nn : 0 ≤ ∑ i, ∑ t, ‖a i t‖ ^ 2 := by positivity
  have hKι0 : (0:ℝ) < (Fintype.card (ι → Bool) : ℝ) := by
    have h : 0 < Fintype.card (ι → Bool) := Fintype.card_pos_iff.mpr ⟨fun _ => true⟩
    exact_mod_cast h
  have hKκ0 : (0:ℝ) < (Fintype.card (κ → Bool) : ℝ) := by
    have h : 0 < Fintype.card (κ → Bool) := Fintype.card_pos_iff.mpr ⟨fun _ => true⟩
    exact_mod_cast h
  have hden : (0:ℝ) < (Fintype.card (ι → Bool) : ℝ) * (Fintype.card (κ → Bool) : ℝ) :=
    mul_pos hKι0 hKκ0
  have hX : (∑ i, ∑ t, ‖a i t‖ₑ ^ (2 : ℝ)) = ENNReal.ofReal (∑ i, ∑ t, ‖a i t‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => by positivity)]
    exact Finset.sum_congr rfl (fun t _ => enorm_rpow_two (a i t))
  have hY : ENNReal.ofReal (∑ ε : ι → Bool, ∑ η : κ → Bool,
        ‖∑ i, ∑ t, (if ε i then (1 : ℂ) else -1) * (if η t then (1 : ℂ) else -1)
          * a i t‖ ^ p)
      = ∑ ε : ι → Bool, ∑ η : κ → Bool,
        ‖∑ i, ∑ t, (if ε i then (1 : ℂ) else -1) * (if η t then (1 : ℂ) else -1)
          * a i t‖ₑ ^ p := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun ε _ => by positivity)]
    apply Finset.sum_congr rfl
    intro ε _
    rw [ENNReal.ofReal_sum_of_nonneg (fun η _ => by positivity)]
    exact Finset.sum_congr rfl (fun η _ => ofReal_norm_rpow _ hp0.le)
  calc ENNReal.ofReal (c1 ^ p * c2 ^ p) * (∑ i, ∑ t, ‖a i t‖ₑ ^ (2 : ℝ)) ^ (p / 2)
      = ENNReal.ofReal (c1 ^ p * c2 ^ p * (∑ i, ∑ t, ‖a i t‖ ^ 2) ^ (p / 2)) := by
        rw [hX, ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ c1 ^ p * c2 ^ p),
          ← ENNReal.ofReal_rpow_of_nonneg hA2nn hhalf]
    _ ≤ ENNReal.ofReal ((∑ ε : ι → Bool, ∑ η : κ → Bool,
          ‖∑ i, ∑ t, (if ε i then (1 : ℂ) else -1) * (if η t then (1 : ℂ) else -1)
            * a i t‖ ^ p)
          / ((Fintype.card (ι → Bool) : ℝ) * (Fintype.card (κ → Bool) : ℝ))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = (∑ ε : ι → Bool, ∑ η : κ → Bool,
          ‖∑ i, ∑ t, (if ε i then (1 : ℂ) else -1) * (if η t then (1 : ℂ) else -1)
            * a i t‖ₑ ^ p)
        * ((Fintype.card (ι → Bool) : ENNReal) * (Fintype.card (κ → Bool) : ENNReal))⁻¹ := by
        rw [ENNReal.ofReal_div_of_pos hden, hY,
          ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (Fintype.card (ι → Bool) : ℝ)),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, div_eq_mul_inv]

end Work.BourgainPlan.IonescuWainger
