import ChallengeDeps
import Mathlib.Tactic.Have
import Submission.Work.MGroupInput.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `MGroupWindow Cn` from the per-state bound

`Work.MGroupInput.MGroupWindow Cn s μ v h c₀ cgap` is the per-*group* lower bound
on the faithful small-box ground energy `Work.BlockBound4.diagWeBAt P …`, which
is the infimum

  `diagWeBAt P … = ⨅_{Ψ : CSBox P s} blockE P Ψ / ∫_{abox P s} Ψ²`

over the corpus's smooth trial states `CSBox P s` (word `diagSlotWord s c₀ cgap`,
kernels `wPairC s v`, `wPairC s (g0 v h)`).

The hypothesis `hp` of the target gives that bound **at every normalised smooth
state** (`∫ Φ² = 1`, `ContDiff ℝ ⊤ Φ`).  Since `blockE` is homogeneous of degree
two in the state — `blockE (d·Φ) = d²·blockE Φ`, and the coefficient `K =
diagSlotWord = cgap·cnPlus + pDiagForm` and the potential density integrand are
both quadratic in `Φ` — the `blockE`-quotient is scale invariant, so a bound at
normalised states is a bound at *every* `CSBox` state, hence bounds the infimum.

This file supplies the two ingredients:

* the scaling lemmas `aP_mul`, `aQ_mul`, `pSlotAmp_mul`, `cnPlus_mul`,
  `pDiagForm_mul` and their combination `blockE_diagSlotWord_mul`;
* the infimum assembly `le_slotEB_of_forall_normalized` (normalised per-state
  bound + degree-two homogeneity ⟹ lower bound on `slotEB`), on top of which the
  target theorem is a two-line instantiation.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Real BigOperators
open Submission BoseGases

namespace Work.MGroupInput

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-! ## 1  The state-argument words are (at least) quadratic in the state -/

/-- Linearity of the condensate mean `aP` in the state. -/
lemma aP_mul {N : ℕ} (ℓ c : ℝ) (i : Fin N) (Φ : X N → ℝ) (x : X N) :
    aP ℓ i (fun x => c * Φ x) x = c * aP ℓ i Φ x := by
  unfold aP
  rw [MeasureTheory.integral_const_mul]
  ring

/-- Linearity of the excited part `aQ = 1 - aP` in the state. -/
lemma aQ_mul {N : ℕ} (ℓ c : ℝ) (i : Fin N) (Φ : X N → ℝ) (x : X N) :
    aQ ℓ i (fun x => c * Φ x) x = c * aQ ℓ i Φ x := by
  unfold aQ
  rw [aP_mul]
  ring

/-- Linearity of the slot amplitude `pSlotAmp` (a `z`-integral of the fibre of
the state against the mode `qMode`) in the state. -/
lemma pSlotAmp_mul {N : ℕ} (s c : ℝ) (p : ℝ³) (i : Fin N)
    (Φ : X N → ℝ) (x : X N) :
    pSlotAmp s p (fun x => c * Φ x) i x = (c : ℂ) * pSlotAmp s p Φ i x := by
  unfold pSlotAmp
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  push_cast
  ring

/-- The squared modulus of a real multiple of a complex number. -/
lemma normC_sq (c : ℝ) : ‖(c : ℂ)‖ ^ 2 = c ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_ofReal]; ring

/-- The excited-particle count `cnPlus` is quadratic in the state. -/
lemma cnPlus_mul {N : ℕ} (ℓ c : ℝ) (Φ : X N → ℝ) :
    cnPlus ℓ (fun x => c * Φ x) = c^2 * cnPlus ℓ Φ := by
  unfold cnPlus
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  rw [aQ_mul]
  ring

/-- The diagonal mode form `pDiagForm` is quadratic in the state. -/
lemma pDiagForm_mul {N : ℕ} (s c : ℝ) (F : ℝ → ℝ) (Φ : X N → ℝ) :
    pDiagForm s F (fun x => c * Φ x) = c^2 * pDiagForm s F Φ := by
  unfold pDiagForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hinner : ∀ p : ℝ³,
      (∫ x in abox N s, ‖pSlotAmp s p (fun x => c * Φ x) i x‖ ^ 2)
        = c^2 * (∫ x in abox N s, ‖pSlotAmp s p Φ i x‖ ^ 2) := by
    intro p
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [pSlotAmp_mul, norm_mul, mul_pow, normC_sq]
  have houter : (∫ p : ℝ³, F ‖p‖ *
        ((s ^ 3)⁻¹ * ∫ x in abox N s, ‖pSlotAmp s p (fun x => c * Φ x) i x‖ ^ 2))
      = c^2 * (∫ p : ℝ³, F ‖p‖ *
        ((s ^ 3)⁻¹ * ∫ x in abox N s, ‖pSlotAmp s p Φ i x‖ ^ 2)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [hinner y]
    ring
  rw [houter]
  ring

/-- **The faithful block energy is homogeneous of degree two.**  With the word
`diagSlotWord s c₀ cgap = cgap·cnPlus + pDiagForm s (fsKinCoeff c₀)` and any
kernels `(w, w₁)`,

  `blockE (d·Φ) = d²·blockE Φ`,

since both the kinetic word and the potential integrand `Φ²·qLHSden` are
quadratic in `Φ`. -/
lemma blockE_diagSlotWord_mul {s μ c₀ cgap : ℝ} {w w1 : ℝ³ → ℝ³ → ℝ}
    (N : ℕ) (d : ℝ) (Φ : X N → ℝ) :
    Work.KinPSuperadd.blockE s μ w w1 (Work.KinPSuperadd.diagSlotWord s c₀ cgap) N
        (fun x => d * Φ x)
      = d^2 * Work.KinPSuperadd.blockE s μ w w1 (Work.KinPSuperadd.diagSlotWord s c₀ cgap) N Φ := by
  unfold Work.KinPSuperadd.blockE Work.KinPSuperadd.diagSlotWord
  rw [cnPlus_mul, pDiagForm_mul]
  have hInt : (∫ x in abox N s, (d * Φ x)^2 * qLHSden N s μ w w1 x)
      = d^2 * ∫ x in abox N s, (Φ x)^2 * qLHSden N s μ w w1 x := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    ring
  rw [hInt]
  ring

/-! ## 2  From the normalised per-state bound to the infimum -/

/-- **The infimum assembly.**  If `blockE` is homogeneous of degree two in the
state and the bound `c` holds at every *normalised* smooth state, then `c`
bounds the `eB`-level infimum `slotEB`. -/
lemma le_slotEB_of_forall_normalized {s μ c : ℝ} {w w1 : ℝ³ → ℝ³ → ℝ}
    {K : ∀ N : ℕ, (X N → ℝ) → ℝ} {N : ℕ}
    (hmul : ∀ (d : ℝ) (Φ : X N → ℝ),
      Work.KinPSuperadd.blockE s μ w w1 K N (fun x => d * Φ x)
        = d^2 * Work.KinPSuperadd.blockE s μ w w1 K N Φ)
    (hper : ∀ (Φ : X N → ℝ), ContDiff ℝ (⊤ : ℕ∞) Φ →
      (∫ x in abox N s, (Φ x) ^ 2) = 1 →
        c ≤ Work.KinPSuperadd.blockE s μ w w1 K N Φ)
    (hs : 0 < s) :
    c ≤ Work.KinPSuperadd.slotEB s μ w w1 K N := by
  haveI : Nonempty (CSBox N s) := nonempty_CSBox N hs
  refine le_ciInf ?_
  intro Ψ
  set Φ₀ : X N → ℝ := (Ψ : X N → ℝ) with hΦ₀
  have hQpos : 0 < ∫ x in abox N s, (Φ₀ x) ^ 2 := by
    rw [hΦ₀]; exact Ψ.sq_pos
  set d : ℝ := (Real.sqrt (∫ x in abox N s, (Φ₀ x) ^ 2))⁻¹ with hd
  have hd2 : d ^ 2 = (∫ x in abox N s, (Φ₀ x) ^ 2)⁻¹ := by
    rw [hd, inv_pow, Real.sq_sqrt hQpos.le]
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => d * Φ₀ x) := by
    have hsm := Ψ.contDiff.const_smul d
    simpa [hΦ₀, smul_eq_mul] using hsm
  have hnorm : (∫ x in abox N s, (d * Φ₀ x) ^ 2) = 1 := by
    have heq : (fun x => (d * Φ₀ x) ^ 2) = fun x => d ^ 2 * (Φ₀ x) ^ 2 := by
      funext x; ring
    rw [heq, MeasureTheory.integral_const_mul, hd2,
      inv_mul_cancel₀ (ne_of_gt hQpos)]
  have hb := hper (fun x => d * Φ₀ x) hcd hnorm
  rw [hmul d Φ₀, hd2] at hb
  rw [div_eq_inv_mul]
  exact hb

/-! ## 3  The target -/

theorem mGroupWindow_of_perStateBound {Cn s μ : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v) (c₀ cgap : ℝ)
    (hs : 0 < s)
    (hp : ∀ (P : ℕ), 1 ≤ P → Cn * μ * s ^ 3 ≤ (P : ℝ) →
      ∀ (Φ : Submission.BoseGases.X P → ℝ), ContDiff ℝ (⊤ : ℕ∞) Φ →
        (∫ x in Submission.BoseGases.abox P s, (Φ x) ^ 2) = 1 →
        (1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2 * (8 * Real.pi * (BoseGases.a v) * s ^ 3)
          ≤ Work.KinPSuperadd.blockE s μ (Submission.BoseGases.wPairC s v)
              (Submission.BoseGases.wPairC s (Submission.BoseGases.g0 v h))
              (Work.KinPSuperadd.diagSlotWord s c₀ cgap) P Φ) :
    Work.MGroupInput.MGroupWindow Cn s μ v h c₀ cgap := by
  intro P hP1 hP2
  refine le_slotEB_of_forall_normalized (N := P)
    (c := (1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2 * (8 * Real.pi * (BoseGases.a v) * s ^ 3))
    (w := Submission.BoseGases.wPairC s v)
    (w1 := Submission.BoseGases.wPairC s (Submission.BoseGases.g0 v h))
    (K := Work.KinPSuperadd.diagSlotWord s c₀ cgap) ?_ ?_ hs
  · intro d Φ
    exact blockE_diagSlotWord_mul (s := s) (μ := μ) (c₀ := c₀) (cgap := cgap)
      (w := Submission.BoseGases.wPairC s v)
      (w1 := Submission.BoseGases.wPairC s (Submission.BoseGases.g0 v h)) P d Φ
  · intro Φ hΦc hΦn
    exact hp P hP1 hP2 Φ hΦc hΦn

end Work.MGroupInput
