import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.rowShape_pinCond
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.rowShape_wLoc_aPC` — step (S3), the χχ row of the `Q₂` row in `aPC` form

`FINDING_PotPairRows_exists.md` §12.6, step 1 of the (S3) work list.  With the condensate pin
`A = pinCond v μ c = c·θ_Λ` (`θ_Λ = 1_{Λ}`, `c̄c·ℓ³ = 1`, `c̄ = c`, `ℓ = ellH v μ`) the two row
shapes `rowShape13`, `rowShape23` of `pairRowS2Row` at the weightless kernel `wLoc ℓ h 0` collapse,
after the `rowShape_pinCond` factorisation and the normalisation `c·c̄ = ℓ⁻³`, onto the
**slot-mean (`aPC`) form** of the row: the `∫_u` of the row is the average `aPC ℓ p.2` and the
`∫_y` is the average `aPC ℓ p.1` (with its arguments **swapped**, because the row's kernel is
evaluated at the *old* `p.2`-value and the *new* `p.1`-value).

The proof splits into

* §0 `aPCInt_mul_const_integral` — the elementary linearity of the Bochner integral used at the
  end of both cores: a constant may be pulled out of a *nested* pair of integrals
  (`∫ g·(c·∫ f) = c·∫∫ g·f`).
* §1 the two **cores** `aPC_rowShape13_core`, `aPC_rowShape23_core`: the exact identity of the
  two *slot-mean* integrals with `ℓ⁻⁶`-times the plain triple Bochner integral.  Nothing here
  needs measurability: the state `Θ` is only assumed to be supported in the `n`-particle box
  `boxPow n ℓ`, so the double integral localises to `acube ℓ × acube ℓ` (the two `u`,`y` slots of
  the updated configuration), and `MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero`
  turns the *set* integral into the full one with no hypothesis.
* §2 the assembly: `rowShape_pinCond` (which strips the two `pinCond` factors to `c·c̄`, resp.
  `c̄·c̄`) and the arithmetic `c·c̄ = ℓ⁻³`, `c̄·c̄ = ℓ⁻³` (from `hc` and `hr`), `(1/ℓ³) = (ℓ³)⁻¹`.

Everything is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-! ## 0. Pulling a constant out of a nested pair of integrals -/

/-- **Linearity of the Bochner integral over a nested pair of integrals.**  A constant `c` may be
pulled out of the inner integral and out of the outer one at once:
`∫_y g y · (c · ∫_u f y u) = c · ∫_y ∫_u g y · f y u`.  The point is that the two constants
(`c` between the two integrals, and the factors of the outer integrand) have to be moved past two
integral signs; the proof uses `integral_const_mul` both ways, so no measurability hypothesis is
needed. -/
theorem aPCInt_mul_const_integral (c : ℂ) (A : E3 → ℂ) (B : E3 → E3 → ℂ) :
    ∫ y : E3, A y * (c * ∫ u : E3, B y u) = c * ∫ y : E3, ∫ u : E3, A y * B y u := by
  conv_rhs => rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  change A y * (c * ∫ u : E3, B y u) = c * ∫ u : E3, A y * B y u
  rw [← MeasureTheory.integral_const_mul c (fun u => A y * B y u)]
  rw [show (∫ u : E3, c * (A y * B y u)) = ∫ u : E3, A y * (c * B y u) by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => by ring))]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-! ## 1. The two cores

Both cores are the *exact* evaluation of the slot-mean integral at the general kernel `K`; the only
hypotheses on the state are the support condition and `p.1 ≠ p.2`, and the conclusion carries the
plain (full-measure) triple Bochner integral. -/

/-- **Core of the block-`I` shape (kernel at the old `p.2`-slot and the new `p.1`-slot).**  For
any kernel `K`, any off-diagonal pair `p` and any state supported in `boxPow n ℓ`,

`∫_x Θ̄(x)·aPC ℓ p.1 (z ↦ K (z p.2) (z p.1)·aPC ℓ p.2 Θ z) x
   = ℓ⁻³·(ℓ⁻³·∫_x∫_y∫_u Θ̄(x)·K (x p.2) y·Θ(x[p.1↦y][p.2↦u]))`. -/
theorem aPC_rowShape13_core {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ : Xn n → ℂ} {K : E3 → E3 → ℂ}
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) :
    (∫ x : Xn n, star (Θ x) * Work.BoseBoxFock.aPC ℓ p.1
        (fun z => K (z p.2) (z p.1) * Work.BoseBoxFock.aPC ℓ p.2 Θ z) x)
      = ((1/ℓ^3 : ℝ) : ℂ) * (((1/ℓ^3 : ℝ) : ℂ) *
          ∫ x : Xn n, ∫ y : E3, ∫ u : E3,
            star (Θ x) * K (x p.2) y * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
  have hz : ∀ z : Xn n, z ∉ Work.MB.boxPow n ℓ → Θ z = 0 := by
    intro z hz'
    by_contra h
    exact hz' (hΘs (Function.mem_support.mpr h))
  have hA : Submission.BoseGases.acube ℓ = Work.BoseK15.corpusBox.boxL ℓ :=
    (Work.BoseBoxFock.boxL_eq_acube hℓ).symm
  have hpt : ∀ x : Xn n,
      star (Θ x) * Work.BoseBoxFock.aPC ℓ p.1
        (fun z => K (z p.2) (z p.1) * Work.BoseBoxFock.aPC ℓ p.2 Θ z) x
      = ((1/ℓ^3 : ℝ) : ℂ) * (((1/ℓ^3 : ℝ) : ℂ) *
          ∫ y : E3, ∫ u : E3,
            star (Θ x) * K (x p.2) y * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
    intro x
    -- the configuration `x[p.1↦y][p.2↦u]` leaves the box as soon as `u` (resp. `y`) does
    have hzu : ∀ y u : E3, u ∉ Submission.BoseGases.acube ℓ →
        Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 := by
      intro y u hu
      refine hz _ ?_
      intro hall
      have h2 : (Function.update (Function.update x p.1 y) p.2 u) p.2 = u :=
        Function.update_self ..
      exact hu (hA.symm ▸ (h2 ▸ (Work.MB.mem_boxPow_iff.mp hall) p.2))
    have hzy : ∀ y u : E3, y ∉ Submission.BoseGases.acube ℓ →
        Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 := by
      intro y u hy
      refine hz _ ?_
      intro hall
      have h1 : (Function.update (Function.update x p.1 y) p.2 u) p.1 = y := by
        rw [Function.update_of_ne hp, Function.update_self]
      exact hy (hA.symm ▸ (h1 ▸ (Work.MB.mem_boxPow_iff.mp hall) p.1))
    have hzu' : ∀ y : E3, (∫ u in Submission.BoseGases.acube ℓ,
          Θ (Function.update (Function.update x p.1 y) p.2 u))
        = ∫ u : E3, Θ (Function.update (Function.update x p.1 y) p.2 u) :=
      fun y => MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => hzu y u hu)
    have hzyI : ∀ y : E3, y ∉ Submission.BoseGases.acube ℓ →
        (∫ u : E3, Θ (Function.update (Function.update x p.1 y) p.2 u)) = 0 := by
      intro y hy
      rw [show (fun u => Θ (Function.update (Function.update x p.1 y) p.2 u)) = fun _ => (0:ℂ) by
            funext u; exact hzy y u hy]
      exact MeasureTheory.integral_zero E3 ℂ
    have hzuy : ∀ y : E3, y ∉ Submission.BoseGases.acube ℓ →
        K (x p.2) y * Work.BoseBoxFock.aPC ℓ p.2 Θ (Function.update x p.1 y) = 0 := by
      intro y hy
      simp only [Work.BoseBoxFock.aPC]
      rw [hzu' y, hzyI y hy]
      simp
    rw [Work.BoseBoxFock.aPC]
    simp only [Function.update_self, Function.update_of_ne (Ne.symm hp)]
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzuy]
    simp only [Work.BoseBoxFock.aPC]
    simp only [hzu']
    have hJ1 : star (Θ x) * (((1/ℓ^3 : ℝ) : ℂ) *
        ∫ y : E3, K (x p.2) y * (((1/ℓ^3 : ℝ) : ℂ) *
          ∫ u : E3, Θ (Function.update (Function.update x p.1 y) p.2 u)))
        = ((1/ℓ^3 : ℝ) : ℂ) * (star (Θ x) *
            ∫ y : E3, K (x p.2) y * (((1/ℓ^3 : ℝ) : ℂ) *
              ∫ u : E3, Θ (Function.update (Function.update x p.1 y) p.2 u))) := by ring
    have hJ2 : star (Θ x) * ∫ y : E3, K (x p.2) y * (((1/ℓ^3 : ℝ) : ℂ) *
          ∫ u : E3, Θ (Function.update (Function.update x p.1 y) p.2 u))
        = ∫ y : E3, (star (Θ x) * K (x p.2) y) * (((1/ℓ^3 : ℝ) : ℂ) *
            ∫ u : E3, Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
      rw [(MeasureTheory.integral_const_mul (star (Θ x)) (fun y : E3 => K (x p.2) y *
            (((1/ℓ^3 : ℝ) : ℂ) * ∫ u : E3,
              Θ (Function.update (Function.update x p.1 y) p.2 u)))).symm]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by ring))
    have hJ3 : (∫ y : E3, (star (Θ x) * K (x p.2) y) * (((1/ℓ^3 : ℝ) : ℂ) *
          ∫ u : E3, Θ (Function.update (Function.update x p.1 y) p.2 u)))
        = ((1/ℓ^3 : ℝ) : ℂ) * ∫ y : E3, ∫ u : E3, (star (Θ x) * K (x p.2) y) *
            Θ (Function.update (Function.update x p.1 y) p.2 u) :=
      aPCInt_mul_const_integral _ _ _
    rw [hJ1, hJ2, hJ3]
  calc ∫ x : Xn n, star (Θ x) * Work.BoseBoxFock.aPC ℓ p.1
        (fun z => K (z p.2) (z p.1) * Work.BoseBoxFock.aPC ℓ p.2 Θ z) x
      = ∫ x : Xn n, ((1/ℓ^3 : ℝ) : ℂ) * (((1/ℓ^3 : ℝ) : ℂ) *
          ∫ y : E3, ∫ u : E3,
            star (Θ x) * K (x p.2) y * Θ (Function.update (Function.update x p.1 y) p.2 u)) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ((1/ℓ^3 : ℝ) : ℂ) * (∫ x : Xn n, ((1/ℓ^3 : ℝ) : ℂ) *
          ∫ y : E3, ∫ u : E3,
            star (Θ x) * K (x p.2) y * Θ (Function.update (Function.update x p.1 y) p.2 u)) :=
        MeasureTheory.integral_const_mul _ _
    _ = ((1/ℓ^3 : ℝ) : ℂ) * (((1/ℓ^3 : ℝ) : ℂ) *
          ∫ x : Xn n, ∫ y : E3, ∫ u : E3,
            star (Θ x) * K (x p.2) y * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
        rw [MeasureTheory.integral_const_mul]

/-- **Core of the block-`II.2` shape (kernel at the two old slots).**  For any kernel `K`, any
off-diagonal pair `p` and any state supported in `boxPow n ℓ`,

`∫_x Θ̄(x)·K (x p.1) (x p.2)·aPC ℓ p.1 (aPC ℓ p.2 Θ) x
   = ℓ⁻³·(ℓ⁻³·∫_x∫_y∫_u Θ̄(x)·K (x p.1) (x p.2)·Θ(x[p.1↦y][p.2↦u]))`. -/
theorem aPC_rowShape23_core {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ : Xn n → ℂ} {K : E3 → E3 → ℂ}
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) :
    (∫ x : Xn n, star (Θ x) * K (x p.1) (x p.2) *
        Work.BoseBoxFock.aPC ℓ p.1 (Work.BoseBoxFock.aPC ℓ p.2 Θ) x)
      = ((1/ℓ^3 : ℝ) : ℂ) * (((1/ℓ^3 : ℝ) : ℂ) *
          ∫ x : Xn n, ∫ y : E3, ∫ u : E3,
            star (Θ x) * K (x p.1) (x p.2) * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
  have hz : ∀ z : Xn n, z ∉ Work.MB.boxPow n ℓ → Θ z = 0 := by
    intro z hz'
    by_contra h
    exact hz' (hΘs (Function.mem_support.mpr h))
  have hA : Submission.BoseGases.acube ℓ = Work.BoseK15.corpusBox.boxL ℓ :=
    (Work.BoseBoxFock.boxL_eq_acube hℓ).symm
  have hpt : ∀ x : Xn n,
      star (Θ x) * K (x p.1) (x p.2) *
        Work.BoseBoxFock.aPC ℓ p.1 (Work.BoseBoxFock.aPC ℓ p.2 Θ) x
      = ((1/ℓ^3 : ℝ) : ℂ) * (((1/ℓ^3 : ℝ) : ℂ) *
          ∫ y : E3, ∫ u : E3,
            star (Θ x) * K (x p.1) (x p.2) * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
    intro x
    have hzu : ∀ y u : E3, u ∉ Submission.BoseGases.acube ℓ →
        Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 := by
      intro y u hu
      refine hz _ ?_
      intro hall
      have h2 : (Function.update (Function.update x p.1 y) p.2 u) p.2 = u :=
        Function.update_self ..
      exact hu (hA.symm ▸ (h2 ▸ (Work.MB.mem_boxPow_iff.mp hall) p.2))
    have hzy : ∀ y u : E3, y ∉ Submission.BoseGases.acube ℓ →
        Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 := by
      intro y u hy
      refine hz _ ?_
      intro hall
      have h1 : (Function.update (Function.update x p.1 y) p.2 u) p.1 = y := by
        rw [Function.update_of_ne hp, Function.update_self]
      exact hy (hA.symm ▸ (h1 ▸ (Work.MB.mem_boxPow_iff.mp hall) p.1))
    have hzu' : ∀ y : E3, (∫ u in Submission.BoseGases.acube ℓ,
          Θ (Function.update (Function.update x p.1 y) p.2 u))
        = ∫ u : E3, Θ (Function.update (Function.update x p.1 y) p.2 u) :=
      fun y => MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => hzu y u hu)
    have hzyI : ∀ y : E3, y ∉ Submission.BoseGases.acube ℓ →
        (∫ u : E3, Θ (Function.update (Function.update x p.1 y) p.2 u)) = 0 := by
      intro y hy
      rw [show (fun u => Θ (Function.update (Function.update x p.1 y) p.2 u)) = fun _ => (0:ℂ) by
            funext u; exact hzy y u hy]
      exact MeasureTheory.integral_zero E3 ℂ
    have hzuy : ∀ y : E3, y ∉ Submission.BoseGases.acube ℓ →
        Work.BoseBoxFock.aPC ℓ p.2 Θ (Function.update x p.1 y) = 0 := by
      intro y hy
      simp only [Work.BoseBoxFock.aPC]
      rw [hzu' y, hzyI y hy]
      simp
    rw [Work.BoseBoxFock.aPC]
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzuy]
    simp only [Work.BoseBoxFock.aPC]
    simp only [hzu']
    have h1 : (star (Θ x) * K (x p.1) (x p.2)) * (((1/ℓ^3 : ℝ) : ℂ) *
          ∫ y : E3, (((1/ℓ^3 : ℝ) : ℂ) *
            ∫ u : E3, Θ (Function.update (Function.update x p.1 y) p.2 u)))
        = ((1/ℓ^3 : ℝ) : ℂ) * ((star (Θ x) * K (x p.1) (x p.2)) *
            ∫ y : E3, (((1/ℓ^3 : ℝ) : ℂ) *
              ∫ u : E3, Θ (Function.update (Function.update x p.1 y) p.2 u))) := by ring
    have h2 : (star (Θ x) * K (x p.1) (x p.2)) *
          ∫ y : E3, (((1/ℓ^3 : ℝ) : ℂ) * ∫ u : E3,
            Θ (Function.update (Function.update x p.1 y) p.2 u))
        = ∫ y : E3, (star (Θ x) * K (x p.1) (x p.2)) * (((1/ℓ^3 : ℝ) : ℂ) *
            ∫ u : E3, Θ (Function.update (Function.update x p.1 y) p.2 u)) :=
      (MeasureTheory.integral_const_mul (star (Θ x) * K (x p.1) (x p.2)) (fun y : E3 =>
        ((1/ℓ^3 : ℝ) : ℂ) * ∫ u : E3,
          Θ (Function.update (Function.update x p.1 y) p.2 u))).symm
    have h3 : (∫ y : E3, (star (Θ x) * K (x p.1) (x p.2)) * (((1/ℓ^3 : ℝ) : ℂ) *
          ∫ u : E3, Θ (Function.update (Function.update x p.1 y) p.2 u)))
        = ((1/ℓ^3 : ℝ) : ℂ) * ∫ y : E3, ∫ u : E3, (star (Θ x) * K (x p.1) (x p.2)) *
            Θ (Function.update (Function.update x p.1 y) p.2 u) :=
      aPCInt_mul_const_integral _ _ _
    rw [h1, h2, h3]
  calc ∫ x : Xn n, star (Θ x) * K (x p.1) (x p.2) *
        Work.BoseBoxFock.aPC ℓ p.1 (Work.BoseBoxFock.aPC ℓ p.2 Θ) x
      = ∫ x : Xn n, ((1/ℓ^3 : ℝ) : ℂ) * (((1/ℓ^3 : ℝ) : ℂ) *
          ∫ y : E3, ∫ u : E3,
            star (Θ x) * K (x p.1) (x p.2) * Θ (Function.update (Function.update x p.1 y) p.2 u)) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ((1/ℓ^3 : ℝ) : ℂ) * (∫ x : Xn n, ((1/ℓ^3 : ℝ) : ℂ) *
          ∫ y : E3, ∫ u : E3,
            star (Θ x) * K (x p.1) (x p.2) * Θ (Function.update (Function.update x p.1 y) p.2 u)) :=
        MeasureTheory.integral_const_mul _ _
    _ = ((1/ℓ^3 : ℝ) : ℂ) * (((1/ℓ^3 : ℝ) : ℂ) *
          ∫ x : Xn n, ∫ y : E3, ∫ u : E3,
            star (Θ x) * K (x p.1) (x p.2) * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
        rw [MeasureTheory.integral_const_mul]

/-! ## 2. The target: the χχ row of the `Q₂` row in `aPC` form -/

theorem rowShape_wLoc_aPC {n : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {c : ℂ}
    {h : EuclideanSpace ℝ (Fin 3) → ℝ} {Θ : Work.BoseDict.Xn n → ℂ}
    (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n (Work.BoseBoxFock.ellH v μ))
    (hc : (starRingEnd ℂ) c * c * (((Work.BoseBoxFock.ellH v μ) ^ 3 : ℝ) : ℂ) = 1)
    (hr : (starRingEnd ℂ) c = c) :
    ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ *
        Work.BoseBoxFock.rowShape13 Θ (Work.BoseBoxFock.pinCond v μ c) (Work.BoseBoxFock.pinCond v μ c)
          (fun w y => ((Submission.BoseGases.wLoc (Work.BoseBoxFock.ellH v μ) h 0 w y : ℝ) : ℂ)) p
      = ∫ x : Work.BoseDict.Xn n, star (Θ x) * Work.BoseBoxFock.aPC (Work.BoseBoxFock.ellH v μ) p.1
          (fun z => ((Submission.BoseGases.wLoc (Work.BoseBoxFock.ellH v μ) h 0 (z p.2) (z p.1) : ℝ) : ℂ)
            * Work.BoseBoxFock.aPC (Work.BoseBoxFock.ellH v μ) p.2 Θ z) x
      ∧ ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ *
        Work.BoseBoxFock.rowShape23 Θ (Work.BoseBoxFock.pinCond v μ c) (Work.BoseBoxFock.pinCond v μ c)
          (fun w y => ((Submission.BoseGases.wLoc (Work.BoseBoxFock.ellH v μ) h 0 w y : ℝ) : ℂ)) p
      = ∫ x : Work.BoseDict.Xn n, star (Θ x)
          * ((Submission.BoseGases.wLoc (Work.BoseBoxFock.ellH v μ) h 0 (x p.1) (x p.2) : ℝ) : ℂ)
            * Work.BoseBoxFock.aPC (Work.BoseBoxFock.ellH v μ) p.1
                (Work.BoseBoxFock.aPC (Work.BoseBoxFock.ellH v μ) p.2 Θ) x := by
  -- the weightless kernel of the χχ row
  set Kc : E3 → E3 → ℂ :=
    fun w y => ((Submission.BoseGases.wLoc (Work.BoseBoxFock.ellH v μ) h 0 w y : ℝ) : ℂ) with hKc
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  -- the target's scalar is the real inverse of `ℓ³`, cast to `ℂ`
  have hL3 : ((((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ : ℝ) : ℂ) =
      (((Work.BoseBoxFock.ellH v μ) ^ 3 : ℝ) : ℂ)⁻¹ := by rw [Complex.ofReal_inv]
  -- `c̄·c = ℓ⁻³` and its two consequence spellings
  have hc' : (starRingEnd ℂ) c * c = (((Work.BoseBoxFock.ellH v μ) ^ 3 : ℝ) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_left hc
  have hcc : c * (starRingEnd ℂ) c = (((Work.BoseBoxFock.ellH v μ) ^ 3 : ℝ) : ℂ)⁻¹ := by
    rw [mul_comm]; exact hc'
  have hss : (starRingEnd ℂ) c * (starRingEnd ℂ) c =
      (((Work.BoseBoxFock.ellH v μ) ^ 3 : ℝ) : ℂ)⁻¹ := by
    simpa only [hr] using hc'
  -- the scalar produced by `aPC`
  have hc1 : ((1 / (Work.BoseBoxFock.ellH v μ) ^ 3 : ℝ) : ℂ) =
      (((Work.BoseBoxFock.ellH v μ) ^ 3 : ℝ) : ℂ)⁻¹ := by rw [one_div, Complex.ofReal_inv]
  refine ⟨?_, ?_⟩
  · rw [hL3]
    rw [(Work.BoseBoxFock.rowShape_pinCond (v := v) (μ := μ) (c := c) (Θ := Θ) (K := Kc) p
          hp hΘs).1, hcc]
    rw [aPC_rowShape13_core (ℓ := Work.BoseBoxFock.ellH v μ) hℓ (K := Kc) hp hΘs, hc1]
  · rw [hL3]
    rw [(Work.BoseBoxFock.rowShape_pinCond (v := v) (μ := μ) (c := c) (Θ := Θ) (K := Kc) p
          hp hΘs).2.2, hss]
    rw [aPC_rowShape23_core (ℓ := Work.BoseBoxFock.ellH v μ) hℓ (K := Kc) hp hΘs, hc1]

end Work.BoseBoxFock
