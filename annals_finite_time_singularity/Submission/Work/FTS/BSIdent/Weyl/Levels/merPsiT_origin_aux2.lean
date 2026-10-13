import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev5
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev6
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev11
import Submission.Work.FTS.BSIdent.Weyl.Levels.merPsiT_origin_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliaries for the vanishing of `ψ`, `∂_zψ`, `∂_rψ` at the origin

Part 2: the pointwise bounds for `∂_zψ` and `∂_rψ` on the whole half-plane `r > 0` (chain rule
on the open quadrant via `_dev6`, the values on `z = 0` via `_dev5`/`_dev11`, and the reduction
of `z < 0` to `z > 0` by oddness in `z`).  Consumed by
`Work.FTS.BSIdent.Weyl.Levels.merPsiT_origin_profiles`.
-/

namespace Work.FTS.BSIdent.Weyl.Levels

open Filter Set
open scoped Topology

set_option maxHeartbeats 2000000

/-- On `z > 0` the chain rule of `_dev6` writes `∂_zψ` and `∂_rψ` as combinations whose
coefficients are `O(ρ)` and whose profile factors are bounded by the rate hypothesis. -/
theorem abs_pdZ_pdR_merPsiT_le_of_pos {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hB : 0 < B (Physical.clockInv C t)) (hp : 0 ≤ Work.FTS.Regularity.pExp α)
    {C₀ lam : ℝ} (hlam : 0 < lam) (hC₀ : 0 ≤ C₀)
    (hval : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam))
    (hwd : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1))
    (hth : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ|
        ≤ C₀ * (1 + w) ^ (-lam)) :
    ∀ r z : ℝ, 0 < r → 0 < z →
      |Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z|
        ≤ |(A (Physical.clockInv C t))⁻¹| * C₀
            * (2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1)
            * Work.Cyl.rhoP r z ∧
      |Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z|
        ≤ |(A (Physical.clockInv C t))⁻¹| * C₀
            * (2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1)
            * Work.Cyl.rhoP r z := by
  intro r z hr hz
  have hθpos : 0 < Work.Cyl.thetaP r z := Work.FTS.BSIdent.Cyl.thetaP_pos_of_pos hr hz
  have hθlt : Work.Cyl.thetaP r z < Real.pi / 2 := Work.FTS.BSIdent.Cyl.thetaP_lt_pi_div_two r z
  have hρpos : 0 < Work.Cyl.rhoP r z := Work.Cyl.rhoP_pos hr z
  have hρnn : 0 ≤ Work.Cyl.rhoP r z := hρpos.le
  have hwpos : 0 < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
      / B (Physical.clockInv C t) :=
    div_pos (Real.rpow_pos_of_pos hρpos _) hB
  have hwnn : 0 ≤ Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
      / B (Physical.clockInv C t) := hwpos.le
  have hGv : |Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t)
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
            / B (Physical.clockInv C t)) ^ (-lam) := by
    rw [Work.FTS.BSIdent.Weyl.Dev5.GG_of_nonneg hθpos.le]
    exact hval _ _ hwpos.le hθpos.le hθlt
  have hGw : |Work.Cyl.pdR (Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
            / B (Physical.clockInv C t)) ^ (-lam - 1) := by
    have hrew : Work.Cyl.pdR (Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z)
        = deriv (fun w' : ℝ => Φ w' (Work.Cyl.thetaP r z) (Physical.clockInv C t))
            (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t)) :=
      Filter.EventuallyEq.deriv_eq (Filter.Eventually.of_forall
        (fun w' => Work.FTS.BSIdent.Weyl.Dev5.GG_of_nonneg (Φ := Φ)
          (τ := Physical.clockInv C t) hθpos.le))
    rw [hrew]
    exact hwd _ _ hwpos.le hθpos.le hθlt
  have hGt : |Work.Cyl.pdZ (Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z)|
      ≤ C₀ * (1 + Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
          / B (Physical.clockInv C t)) ^ (-lam) := by
    have hrew : Work.Cyl.pdZ (Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z)
        = deriv (fun θ' : ℝ => Φ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
            / B (Physical.clockInv C t)) θ' (Physical.clockInv C t)) (Work.Cyl.thetaP r z) := by
      rw [show Work.Cyl.pdZ (Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t))
          (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
          (Work.Cyl.thetaP r z)
          = deriv (fun θ' : ℝ => Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t)
              (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
                / B (Physical.clockInv C t)) θ') (Work.Cyl.thetaP r z) from rfl]
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hθpos] with θ' hθ'
      exact Work.FTS.BSIdent.Weyl.Dev5.GG_of_nonneg (Φ := Φ)
        (τ := Physical.clockInv C t) hθ'.le
    rw [hrew]
    exact hth _ _ hwpos.le hθpos.le hθlt
  have hZ : |z| ≤ Work.Cyl.rhoP r z := Work.FTS.BSIdent.Cyl.abs_snd_le_rhoP r z
  have hR : |r| ≤ Work.Cyl.rhoP r z := by
    rw [abs_of_nonneg hr.le]
    exact Work.FTS.BSIdent.Cyl.le_rhoP r z hr.le
  have hZneg : |-z| ≤ Work.Cyl.rhoP r z := by rwa [abs_neg]
  constructor
  · rw [Work.FTS.BSIdent.Weyl.Dev6.pdZ_merPsiT_eq (τ := Physical.clockInv C t) (α := α)
      (A := A) (B := B) (Φ := Φ) (C := C) (t := t) rfl hsm hB hr (ne_of_gt hz)]
    exact abs_chain_le (c := (A (Physical.clockInv C t))⁻¹)
      (p := Work.FTS.Regularity.pExp α) (C₀ := C₀) (lam := lam)
      (ρ := Work.Cyl.rhoP r z) (θ := Work.Cyl.thetaP r z)
      (w := Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
      (Z := z) (R := r)
      (Gv := Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t)
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z))
      (Gw := Work.Cyl.pdR (Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z))
      (Gt := Work.Cyl.pdZ (Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z))
      hC₀ hlam hp hθpos.le hρnn hwnn hZ hR hGv hGw hGt
  · rw [Work.FTS.BSIdent.Weyl.Dev6.pdR_merPsiT_eq (τ := Physical.clockInv C t) (α := α)
      (A := A) (B := B) (Φ := Φ) (C := C) (t := t) rfl hsm hB hr (ne_of_gt hz)]
    exact abs_chain_le (c := (A (Physical.clockInv C t))⁻¹)
      (p := Work.FTS.Regularity.pExp α) (C₀ := C₀) (lam := lam)
      (ρ := Work.Cyl.rhoP r z) (θ := Work.Cyl.thetaP r z)
      (w := Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
      (Z := r) (R := -z)
      (Gv := Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t)
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z))
      (Gw := Work.Cyl.pdR (Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z))
      (Gt := Work.Cyl.pdZ (Work.FTS.BSIdent.Weyl.Dev5.GG Φ (Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t))
        (Work.Cyl.thetaP r z))
      hC₀ hlam hp hθpos.le hρnn hwnn hR hZneg hGv hGw hGt

/-- The two partials are odd/even in the axial variable, because `ψ` is odd. -/
theorem pdZ_merPsiT_odd {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hB : 0 < B (Physical.clockInv C t))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    {r z : ℝ} (hr : 0 < r) :
    Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r (-z)
      = Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z :=
  (Work.FTS.BSIdent.Cyl.deriv_odd_eq (f := fun z' : ℝ =>
      Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r z')
    (fun y => Work.FTS.BSIdent.Cyl.merPsiT_odd_z hB h0 (r := r) (z := y) hr) z).symm

theorem pdR_merPsiT_odd {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hB : 0 < B (Physical.clockInv C t))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    {r z : ℝ} (hr : 0 < r) :
    Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r (-z)
      = -Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z := by
  have hev : (fun r' : ℝ => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r' (-z))
      =ᶠ[𝓝 r] (fun r' : ℝ => -Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r' z) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with r' hr'
    exact Work.FTS.BSIdent.Cyl.merPsiT_odd_z hB h0 (r := r') (z := z) hr'
  show deriv (fun r' : ℝ => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r' (-z)) r = _
  rw [Filter.EventuallyEq.deriv_eq hev]
  exact Work.FTS.BSIdent.Cyl.deriv_neg_fun (g := fun r' : ℝ =>
    Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r' z) r

/-- `|∂_zψ(r,z)| ≤ K ρ(r,z)` for all `r > 0`, all `z`. -/
theorem abs_pdZ_merPsiT_le {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hB : 0 < B (Physical.clockInv C t))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hp : 0 ≤ Work.FTS.Regularity.pExp α)
    {C₀ lam : ℝ} (hlam : 0 < lam) (hC₀ : 0 ≤ C₀)
    (hval : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam))
    (hwd : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1))
    (hth : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ|
        ≤ C₀ * (1 + w) ^ (-lam)) :
    ∀ r z : ℝ, 0 < r →
      |Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z|
        ≤ |(A (Physical.clockInv C t))⁻¹| * C₀
            * (2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1)
            * Work.Cyl.rhoP r z := by
  intro r z hr
  rcases lt_trichotomy z 0 with hlt | heq | hgt
  · have hpos := abs_pdZ_pdR_merPsiT_le_of_pos (α := α) (A := A) (B := B) (Φ := Φ) (C := C)
      (t := t) hsm hB hp hlam hC₀ hval hwd hth r (-z) hr (by linarith)
    rw [Work.Cyl.rhoP_neg] at hpos
    rw [← pdZ_merPsiT_odd (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (t := t)
      (z := z) hB h0 hr]
    exact hpos.1
  · subst heq
    rw [Work.FTS.BSIdent.Weyl.Dev11.pdZ_merPsiT_zero_snd (τ := Physical.clockInv C t)
      (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (t := t) rfl hsm h0 hB hr]
    have hw1 : 0 < r ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t) :=
      div_pos (Real.rpow_pos_of_pos hr _) hB
    have hd : |deriv (fun θ' : ℝ => Φ (r ^ Work.FTS.Regularity.pExp α
        / B (Physical.clockInv C t)) θ' (Physical.clockInv C t)) 0| ≤ C₀ := by
      refine (hth (r ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t)) 0
        hw1.le le_rfl (by linarith [Real.pi_pos])).trans ?_
      have hp1 : (1 + r ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t)) ^ (-lam) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      calc C₀ * (1 + r ^ Work.FTS.Regularity.pExp α / B (Physical.clockInv C t)) ^ (-lam)
          ≤ C₀ * 1 := mul_le_mul_of_nonneg_left hp1 hC₀
        _ = C₀ := by ring
    rw [abs_mul, abs_mul, abs_of_nonneg hr.le, Work.FTS.BSIdent.Weyl.Dev11.rhoP_zero_snd hr]
    have h2 : 0 ≤ Work.FTS.Regularity.pExp α * (Real.pi / 2) :=
      mul_nonneg hp (by linarith [Real.pi_pos])
    have hK : |(A (Physical.clockInv C t))⁻¹| * C₀
        ≤ |(A (Physical.clockInv C t))⁻¹| * C₀
            * (2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1) := by
      have h1 : (1:ℝ) ≤ 2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1 := by
        linarith [Real.pi_pos, h2]
      calc |(A (Physical.clockInv C t))⁻¹| * C₀
          = |(A (Physical.clockInv C t))⁻¹| * C₀ * 1 := by ring
        _ ≤ |(A (Physical.clockInv C t))⁻¹| * C₀
              * (2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    calc |(A (Physical.clockInv C t))⁻¹| * r
          * |deriv (fun θ' : ℝ => Φ (r ^ Work.FTS.Regularity.pExp α
              / B (Physical.clockInv C t)) θ' (Physical.clockInv C t)) 0|
        ≤ |(A (Physical.clockInv C t))⁻¹| * r * C₀ :=
          mul_le_mul_of_nonneg_left hd (by positivity)
      _ = |(A (Physical.clockInv C t))⁻¹| * C₀ * r := by ring
      _ ≤ |(A (Physical.clockInv C t))⁻¹| * C₀
            * (2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1) * r :=
          mul_le_mul_of_nonneg_right hK hr.le
  · exact (abs_pdZ_pdR_merPsiT_le_of_pos (α := α) (A := A) (B := B) (Φ := Φ) (C := C)
      (t := t) hsm hB hp hlam hC₀ hval hwd hth r z hr hgt).1

/-- `|∂_rψ(r,z)| ≤ K ρ(r,z)` for all `r > 0`, all `z`. -/
theorem abs_pdR_merPsiT_le {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hB : 0 < B (Physical.clockInv C t))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hp : 0 ≤ Work.FTS.Regularity.pExp α)
    {C₀ lam : ℝ} (hlam : 0 < lam) (hC₀ : 0 ≤ C₀)
    (hval : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam))
    (hwd : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1))
    (hth : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ|
        ≤ C₀ * (1 + w) ^ (-lam)) :
    ∀ r z : ℝ, 0 < r →
      |Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z|
        ≤ |(A (Physical.clockInv C t))⁻¹| * C₀
            * (2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1)
            * Work.Cyl.rhoP r z := by
  intro r z hr
  rcases lt_trichotomy z 0 with hlt | heq | hgt
  · have hpos := abs_pdZ_pdR_merPsiT_le_of_pos (α := α) (A := A) (B := B) (Φ := Φ) (C := C)
      (t := t) hsm hB hp hlam hC₀ hval hwd hth r (-z) hr (by linarith)
    rw [Work.Cyl.rhoP_neg] at hpos
    rw [pdR_merPsiT_odd (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (t := t)
      (z := z) hB h0 hr, abs_neg] at hpos
    exact hpos.2
  · subst heq
    rw [Work.FTS.BSIdent.Weyl.Dev5.pdR_merPsiT_zero_snd (τ := Physical.clockInv C t)
      (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (t := t) rfl hB h0 hr]
    have h2 : 0 ≤ Work.FTS.Regularity.pExp α * (Real.pi / 2) :=
      mul_nonneg hp (by linarith [Real.pi_pos])
    have hKnn : 0 ≤ |(A (Physical.clockInv C t))⁻¹| * C₀
        * (2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1) := by
      have h3 : (0:ℝ) < 2 * (Real.pi / 2) + Work.FTS.Regularity.pExp α * (Real.pi / 2) + 1 := by
        linarith [Real.pi_pos, h2]
      positivity
    rw [abs_zero]
    exact mul_nonneg hKnn (Work.Cyl.rhoP_nonneg r 0)
  · exact (abs_pdZ_pdR_merPsiT_le_of_pos (α := α) (A := A) (B := B) (Φ := Φ) (C := C)
      (t := t) hsm hB hp hlam hC₀ hval hwd hth r z hr hgt).2

end Work.FTS.BSIdent.Weyl.Levels
