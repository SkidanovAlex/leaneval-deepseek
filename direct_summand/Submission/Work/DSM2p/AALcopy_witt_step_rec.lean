-- Redirected copy of `Submission.Work.DSM2p.witt_step_rec` (imports re-pointed to the `AALvaln` vocabulary layer so that
-- `area_AAL_proved.lean` can import the result without an import cycle).  The original
-- file is untouched; this copy is generated mechanically.
import Mathlib
import Submission.Work.DSM2p.AALcopy_DigLeDefs
import Submission.Work.DSM2p.AALcopy_untilt_add_le
import Submission.Work.DSM2p.AALcopy_DigLeEngine
import Submission.Work.DSM2p.AALcopy_mul_p_sub_teichmuller
import Submission.Work.DSPB1.Basic

/-!
# `witt_step_rec` — the one-step Česnavičius–Scholze recursion

This file proves the one-step recursion at the heart of the analytic node
`Work.DSM2p.approx_lem` (Česnavičius–Scholze, *Purity for flat cohomology*, `approx-lem`).

The construction is the source's

`z' = z - ξ · ((z - [z̄]) / p) · ((ξ - [ξ̄]) / p)⁻¹`,

written here in the equivalent form `z' = z - ξ * vv` where `vv = (z - [z̄])/p` is the explicit
shift `vv.coeff j = (z.coeff (j+1))^{1/p}` (an element of the tilt, so its `p`-adic division is
free).  The generator `ξ` of the kernel of `θ` is taken to be

`ξ = p - [ϖ♭ ^ p] · ũ`,  where `♯(ϖ♭) = ϖ 0` and `θ ũ = (ϖ 0 ^ p / p)⁻¹`,

so that `θ ξ = 0` and `p - ξ = [ϖ♭ ^ p] · ũ` has all tilt digits bounded by `v p = v (ϖ 0) ^ p`.

The estimates are the Gauss-norm calculus of `DigLeEngine`:

* `DigLe v (z' - [x]) (v (ϖ 0)^p * β)` since `z' - [x] = (p - ξ) * vv`;
* `DigLe v z' (max (v (ϖ 0)^p * β) (v (♯(z.coeff 0))))` by subadditivity with `[z.coeff 0]`;
* the same for the tail `z' - [z'.coeff 0]`, using `[x] - [x'] = [x] + (-1) * [x']`.
-/

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.DSM2p

universe u v

open WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [Fact (¬ IsUnit (p : R))]
    [IsAdicComplete (Ideal.span {(p : R)}) R]

/-! ## Elementary inputs -/

/-- `fontaineTheta` is surjective, because Frobenius is surjective on `R ⧸ (p)`. -/
theorem surjective_fontaineTheta_of_frobSurj' (QR : DSMap.PerfectoidData p R) :
    Function.Surjective (WittVector.fontaineTheta R p) := by
  refine surjective_fontaineTheta ?_
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨z, hz⟩ := QR.frobSurj x
  refine ⟨Ideal.Quotient.mk (Ideal.span {(p : R)}) z, ?_⟩
  rw [frobenius_def, ← map_pow, Ideal.Quotient.eq]
  simpa [sub_eq_add_neg, add_comm] using neg_mem hz

/-- A unit in the unit ball has value `1`. -/
theorem v_units_eq_one {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation R Γ₀} (hball : IsUnitBall v Set.univ) (u : Rˣ) : v (↑u : R) = 1 := by
  have hmul : v (↑u : R) * v (↑u⁻¹ : R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h1 : v (↑u : R) ≤ 1 := hball _ (Set.mem_univ _)
  have h2 : v (↑u⁻¹ : R) ≤ 1 := hball _ (Set.mem_univ _)
  have hge : 1 ≤ v (↑u : R) := by
    calc (1 : Γ₀) = v (↑u : R) * v (↑u⁻¹ : R) := hmul.symm
      _ ≤ v (↑u : R) * 1 := mul_le_mul' le_rfl h2
      _ = v (↑u : R) := mul_one _
  exact le_antisymm h1 hge

/-- On the unit ball, `v (ϖ ^ p) = v p`. -/
theorem v_varpi_pow_eq_v_p (QR : DSMap.PerfectoidData p R)
    {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}
    (hball : IsUnitBall v Set.univ) : v (QR.ϖ 0) ^ p = v (p : R) := by
  obtain ⟨u, hu⟩ := QR.unit
  rw [← map_pow, hu, map_mul, v_units_eq_one hball u, mul_one]

/-- Continuity of `v` at `ϖ 0` gives continuity at `p`. -/
theorem hv_of_isContinuousValuation (QR : DSMap.PerfectoidData p R)
    {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}
    (hcont : IsContinuousValuation (QR.ϖ 0) v) (hball : IsUnitBall v Set.univ) :
    ∀ γ : Γ₀, γ ≠ 0 → ∃ n : ℕ, v (p : R) ^ n < γ := by
  intro γ hγ
  obtain ⟨n, hn⟩ := hcont γ hγ
  refine ⟨n, ?_⟩
  rw [← v_varpi_pow_eq_v_p QR hball, ← pow_mul]
  exact lt_of_le_of_lt
    (pow_le_pow_right_of_le_one' (hball _ (Set.mem_univ _))
      (Nat.le_mul_of_pos_left n (Fact.out : p.Prime).pos)) hn

theorem DigLe.one {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}
    (hball : IsUnitBall v Set.univ) (z : WittVector p (PreTilt R p)) : DigLe v z 1 :=
  fun j => nv_le_one hball _

/-! ## The recursion step -/

theorem witt_step_rec {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    (QR : DSMap.PerfectoidData p R) [Fact (¬ IsUnit (p : R))]
    [IsAdicComplete (Ideal.span {(p : R)}) R] (z : WittVector p (PreTilt R p)) :
    ∃ z' : WittVector p (PreTilt R p),
      WittVector.fontaineTheta R p z' = WittVector.fontaineTheta R p z ∧
      ∀ (Γ₀ : Type*) [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),
        IsContinuousValuation (QR.ϖ 0) v → IsUnitBall v Set.univ →
        ∀ (β : Γ₀), (∀ j : ℕ, v (PreTilt.untilt (tiltDigit z j)) ≤ β) →
          (∀ j : ℕ, v (PreTilt.untilt (tiltDigit z' j)) ≤
              max (v (QR.ϖ 0) ^ p * β) (v (PreTilt.untilt (z.coeff 0)))) ∧
          (∀ j : ℕ,
            v (PreTilt.untilt (tiltDigit (z' - WittVector.teichmuller p (z'.coeff 0)) j)) ≤
              max (v (QR.ϖ 0) ^ p * β) (v (PreTilt.untilt (z.coeff 0)))) := by
  classical
  -- the generator `ξ` of `ker θ`
  obtain ⟨u1, hu1⟩ := QR.unit
  obtain ⟨ũ, hũ⟩ := surjective_fontaineTheta_of_frobSurj' QR (↑(u1⁻¹) : R)
  set ab : PreTilt R p := (Work.DSPB1.varpiTilt QR) ^ p with hab
  set ξ : WittVector p (PreTilt R p) :=
    (p : WittVector p (PreTilt R p)) - WittVector.teichmuller p ab * ũ with hξ
  have hvarpi : PreTilt.untilt (Work.DSPB1.varpiTilt QR) = QR.ϖ 0 :=
    Work.DSPB1.varpiTilt_untilt QR
  have habval : PreTilt.untilt ab = (p : R) * (↑u1 : R) := by
    rw [hab, map_pow, hvarpi, hu1]
  have hθξ : WittVector.fontaineTheta R p ξ = 0 := by
    rw [hξ, map_sub, map_mul, map_natCast, WittVector.fontaineTheta_teichmuller, hũ, habval]
    rw [mul_assoc, ← Units.val_mul,
      show (↑(u1 * u1⁻¹) : R) = 1 from by rw [Units.val_mul, Units.mul_inv]]
    simp
  -- the shift `vv = (z - [z.coeff 0]) / p`
  set vv : WittVector p (PreTilt R p) :=
    WittVector.mk p (fun j => (frobeniusEquiv (PreTilt R p) p).symm (z.coeff (j + 1))) with hvv
  have hpvv : (p : WittVector p (PreTilt R p)) * vv
      = z - WittVector.teichmuller p (z.coeff 0) := by
    rw [hvv]; exact mul_p_sub_teichmuller z
  refine ⟨z - ξ * vv, ?_, ?_⟩
  · rw [map_sub, map_mul, hθξ, zero_mul, sub_zero]
  · intro Γ₀ _ v hcont hball β hβ
    have hv := hv_of_isContinuousValuation QR hcont hball
    have hvp1 : v (QR.ϖ 0) ^ p ≤ 1 := by
      rw [← map_pow]
      exact hball _ (Set.mem_univ _)
    -- reduce to `β ≤ 1`
    set β' : Γ₀ := min β 1 with hβ'def
    have hβ'1 : β' ≤ 1 := min_le_right _ _
    have hβ'β : β' ≤ β := min_le_left _ _
    have hzβ : DigLe v z β' := fun j => le_min (hβ j) (nv_le_one hball _)
    -- `vv` has the same digit bound as `z`
    have hvv_le : DigLe v vv β' := by
      refine DigLe.of_coeff fun j => ?_
      rw [hvv]
      show nv v ((frobeniusEquiv (PreTilt R p) p).symm (z.coeff (j + 1))) ≤ β' ^ p ^ j
      have h := DigLe.to_coeff hzβ (j + 1)
      have h2 : nv v ((frobeniusEquiv (PreTilt R p) p).symm (z.coeff (j + 1))) ^ p
          = nv v (z.coeff (j + 1)) := by
        have key : PreTilt.untilt ((frobeniusEquiv (PreTilt R p) p).symm (z.coeff (j + 1))) ^ p
            = PreTilt.untilt (z.coeff (j + 1)) := by
          rw [← map_pow]
          exact congrArg PreTilt.untilt (frobeniusEquiv_symm_apply_pow (z.coeff (j + 1)))
        simp only [nv]
        rw [← map_pow v, key]
      refine le_of_pow_le_pow_left₀ (Fact.out : p.Prime).ne_zero (zero_le) ?_
      rw [h2]
      calc nv v (z.coeff (j + 1)) ≤ β' ^ p ^ (j + 1) := h
        _ = (β' ^ p ^ j) ^ p := by rw [pow_succ, pow_mul]
    -- the digit bound of `p - ξ`
    have hq_le : DigLe v ((p : WittVector p (PreTilt R p)) - ξ) (v (QR.ϖ 0) ^ p) := by
      have hpeq : (p : WittVector p (PreTilt R p)) - ξ = WittVector.teichmuller p ab * ũ := by
        rw [hξ]; abel
      rw [hpeq]
      have h1 : nv v ab = v (QR.ϖ 0) ^ p := by
        rw [nv, habval, map_mul, v_units_eq_one hball u1, mul_one,
          ← v_varpi_pow_eq_v_p QR hball]
      have hbnd : DigLe v (WittVector.teichmuller p ab) (v (PreTilt.untilt ab)) :=
        DigLe.teichmuller_self v ab
      have hone : DigLe v ũ 1 := DigLe.one hball ũ
      have hb1 : v (PreTilt.untilt ab) ≤ 1 := nv_le_one hball _
      have hmul := DigLe.mul hball hv hb1 le_rfl hbnd hone
      rw [mul_one] at hmul
      exact DigLe.mono (le_of_eq h1) hmul
    have hprod : DigLe v (((p : WittVector p (PreTilt R p)) - ξ) * vv)
        (v (QR.ϖ 0) ^ p * β') :=
      DigLe.mul hball hv hvp1 hβ'1 hq_le hvv_le
    have hzx : (p : WittVector p (PreTilt R p)) * vv
        = z - WittVector.teichmuller p (z.coeff 0) := hpvv
    -- clause 1
    have hsplit : z - ξ * vv
        = WittVector.teichmuller p (z.coeff 0)
          + ((p : WittVector p (PreTilt R p)) - ξ) * vv := by
      rw [show ((p : WittVector p (PreTilt R p)) - ξ) * vv
          = (p : WittVector p (PreTilt R p)) * vv - ξ * vv from sub_mul _ _ _]
      rw [hzx]
      abel
    have hM : DigLe v (z - ξ * vv)
        (max (v (QR.ϖ 0) ^ p * β') (v (PreTilt.untilt (z.coeff 0)))) := by
      rw [hsplit]
      have hb : v (QR.ϖ 0) ^ p * β' ≤ 1 := by
        simpa using mul_le_mul' hvp1 hβ'1
      have hadd := DigLe.add hball hv (nv_le_one hball _) hb
        (DigLe.teichmuller_self v (z.coeff 0)) hprod
      rwa [max_comm] at hadd
    have hMβ : DigLe v (z - ξ * vv)
        (max (v (QR.ϖ 0) ^ p * β) (v (PreTilt.untilt (z.coeff 0)))) :=
      DigLe.mono (max_le_max (mul_le_mul' le_rfl hβ'β) le_rfl) hM
    refine ⟨fun j => hMβ j, ?_⟩
    -- clause 2
    set x' : PreTilt R p := (z - ξ * vv).coeff 0 with hx'def
    have hM1 : max (v (QR.ϖ 0) ^ p * β') (v (PreTilt.untilt (z.coeff 0))) ≤ 1 :=
      max_le (by simpa using mul_le_mul' hvp1 hβ'1) (nv_le_one hball _)
    have hx'M : nv v x' ≤ max (v (QR.ϖ 0) ^ p * β') (v (PreTilt.untilt (z.coeff 0))) := by
      have h := DigLe.to_coeff hM 0
      simpa [hx'def] using h
    have hsplit2 : (z - ξ * vv) - WittVector.teichmuller p x'
        = ((p : WittVector p (PreTilt R p)) - ξ) * vv
          + (WittVector.teichmuller p (z.coeff 0) - WittVector.teichmuller p x') := by
      rw [hsplit, hx'def]
      abel
    have hsecond : DigLe v
        (WittVector.teichmuller p (z.coeff 0) - WittVector.teichmuller p x')
        (max (v (QR.ϖ 0) ^ p * β') (v (PreTilt.untilt (z.coeff 0)))) := by
      have hneg : WittVector.teichmuller p (z.coeff 0) - WittVector.teichmuller p x'
          = WittVector.teichmuller p (z.coeff 0)
            + (-1 : WittVector p (PreTilt R p)) * WittVector.teichmuller p x' := by
        rw [neg_one_mul]; abel
      rw [hneg]
      have hone : DigLe v (-1 : WittVector p (PreTilt R p)) 1 := DigLe.one hball _
      have htg : DigLe v (WittVector.teichmuller p x') (nv v x') := DigLe.teichmuller_self v x'
      have hmul := DigLe.mul (B := (1 : Γ₀)) (C := v (PreTilt.untilt x'))
        hball hv (le_refl (1 : Γ₀)) (nv_le_one hball x') hone htg
      rw [one_mul] at hmul
      have hadd := DigLe.add hball hv (nv_le_one hball _) (nv_le_one hball _)
        (DigLe.teichmuller_self v (z.coeff 0)) hmul
      refine DigLe.mono (max_le (le_max_right _ _) hx'M) hadd
    have h2 : DigLe v ((z - ξ * vv) - WittVector.teichmuller p x')
        (max (v (QR.ϖ 0) ^ p * β') (v (PreTilt.untilt (z.coeff 0)))) := by
      rw [hsplit2]
      have hb : v (QR.ϖ 0) ^ p * β' ≤ 1 := by
        simpa using mul_le_mul' hvp1 hβ'1
      have hadd := DigLe.add hball hv hb hM1 hprod hsecond
      rwa [max_eq_right (le_max_left _ _)] at hadd
    refine fun j => le_trans (h2 j) ?_
    exact max_le_max (mul_le_mul' le_rfl hβ'β) le_rfl

end Work.DSM2p
