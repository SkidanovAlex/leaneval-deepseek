import Mathlib
import Submission.Work.DSPB2.Basic

/-!
# DSPB2 — the tilt: `p`-power roots, `♯`-map, coefficients

Second layer of DSPB2.  We fix `DSMap.PerfectoidData p C` and develop the API of the tilt
`C♭ = PreTilt C p` that the mod-`p` comparison needs:

* `tiltRoot c n` — the `n`-th `p`-power root of `c` in the (perfect) ring `C♭`;
* its coefficients `PreTilt.coeff n`, and its `♯`-image `PreTilt.untilt (tiltRoot c n)` in `C`.

`untilt` is Mathlib's multiplicative "untilt" map `C♭ →* C` whose composite with reduction mod `p`
is the `0`-th coefficient (`PreTilt.mk_untilt_eq_coeff_zero`).
-/

set_option linter.unusedSectionVars false

namespace Work.DSPB2

universe a

open Ideal

variable (p : ℕ) [Fact p.Prime] (C : Type a) [CommRing C] [Fact ¬IsUnit (p : C)]

/-! ### The `p`-power roots in the tilt -/

/-- The `n`-th `p`-power root of `x` in the tilt: `((Frobenius⁻¹)^[n]) x`. -/
noncomputable def tiltRoot (x : Tilt p C) (n : ℕ) : Tilt p C :=
  ((frobeniusEquiv (PreTilt C p) p).symm)^[n] x

theorem tiltRoot_zero (x : Tilt p C) : tiltRoot p C x 0 = x := rfl

theorem tiltRoot_succ (x : Tilt p C) (n : ℕ) :
    tiltRoot p C x (n + 1) = (frobeniusEquiv (PreTilt C p) p).symm (tiltRoot p C x n) := by
  simp only [tiltRoot, Function.iterate_succ_apply']

theorem tiltRoot_pow (x : Tilt p C) (n : ℕ) : (tiltRoot p C x n) ^ p ^ n = x :=
  iterate_frobeniusEquiv_symm_pow_p_pow (PreTilt C p) p x n

theorem coeff_tiltRoot (x : Tilt p C) (m n : ℕ) :
    PreTilt.coeff m (tiltRoot p C x n) = PreTilt.coeff (m + n) x :=
  PreTilt.coeff_iterate_frobeniusEquiv_symm m n x

theorem coeff_zero_tiltRoot (x : Tilt p C) (n : ℕ) :
    PreTilt.coeff 0 (tiltRoot p C x n) = PreTilt.coeff n x := by
  simp only [tiltRoot, PreTilt.coeff_iterate_frobeniusEquiv_symm, Nat.zero_add]

/-! ### The coefficients of a power -/

theorem coeff_pow_p_succ (x : Tilt p C) (n : ℕ) :
    PreTilt.coeff (n + 1) (x ^ p) = PreTilt.coeff n x := by
  rw [map_pow, PreTilt.coeff_pow_p]

/-- Conversely, the `p ^ m`-th power of the `m`-th coefficient is the `0`-th coefficient. -/
theorem pow_coeff (x : Tilt p C) (m : ℕ) :
    (PreTilt.coeff m x) ^ p ^ m = PreTilt.coeff 0 x := by
  induction m with
  | zero => rw [pow_zero, pow_one]
  | succ m ih => rw [pow_succ', pow_mul, PreTilt.coeff_pow_p, ih]

/-! ### The `♯`-map on `p`-power roots -/

variable [IsAdicComplete (Ideal.span {(p : C)}) C]

theorem untilt_pow (x : Tilt p C) (k : ℕ) : PreTilt.untilt (x ^ k) = PreTilt.untilt x ^ k :=
  map_pow _ x k

theorem untilt_tiltRoot_pow (x : Tilt p C) (n : ℕ) :
    PreTilt.untilt (tiltRoot p C x n) ^ p ^ n = PreTilt.untilt x :=
  PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n

theorem untilt_tiltRoot_succ (x : Tilt p C) (n : ℕ) :
    PreTilt.untilt (tiltRoot p C x (n + 1)) ^ p = PreTilt.untilt (tiltRoot p C x n) := by
  have h := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow (tiltRoot p C x n) 1
  rw [Function.iterate_one, pow_one] at h
  rwa [← tiltRoot_succ] at h

theorem coeff_zero_untilt (x : Tilt p C) :
    PreTilt.coeff 0 x = Ideal.Quotient.mk (Ideal.span {(p : C)}) (PreTilt.untilt x) :=
  (PreTilt.mk_untilt_eq_coeff_zero x).symm

/-- Every element of `C ⧸ (p)` is the `0`-th coefficient of an element of the tilt. -/
theorem coeff_zero_surjective (P : DSMap.PerfectoidData p C) :
    Function.Surjective (PreTilt.coeff 0 : Tilt p C →+* ModP C p) :=
  Perfection.coeff_surjective (frobenius_red_surjective p C P) 0

/-- The `0`-th coefficient vanishes exactly when `♯ x ≡ 0` modulo `p`; this is the form in which
`ker (coeff 0)` is used downstream. -/
theorem coeff_zero_eq_zero_iff (x : Tilt p C) :
    PreTilt.coeff 0 x = 0 ↔ PreTilt.untilt x ∈ Ideal.span {(p : C)} := by
  rw [coeff_zero_untilt, Ideal.Quotient.eq_zero_iff_mem]

/-! ### `♯` of the `p`-power roots of `ϖ♭`, and divisibility of `p` -/

/-- If `♯ c = ϖ 0` then `♯ (c^{1/p^n})` divides `p` in `C`. -/
theorem p_mem_span_untilt_tiltRoot (P : DSMap.PerfectoidData p C) (c : Tilt p C)
    (hϖ : PreTilt.untilt c = P.ϖ 0) (n : ℕ) :
    (p : C) ∈ Ideal.span {PreTilt.untilt (tiltRoot p C c n)} := by
  obtain ⟨u, hu⟩ := P.unit
  refine Ideal.mem_span_singleton'.mpr
    ⟨↑u⁻¹ * (PreTilt.untilt (tiltRoot p C c n)) ^ (p ^ (n + 1) - 1), ?_⟩
  have hτ : PreTilt.untilt (tiltRoot p C c n) ^ p ^ n = P.ϖ 0 := by
    rw [untilt_tiltRoot_pow, hϖ]
  have hk : 1 ≤ p ^ (n + 1) := Nat.one_le_pow _ _ (Fact.out : Nat.Prime p).pos
  have hpow : PreTilt.untilt (tiltRoot p C c n) ^ p ^ (n + 1) = (p : C) * ↑u := by
    rw [pow_succ', pow_mul', hτ, hu]
  have hfin : (↑u⁻¹ : C) * ((p : C) * ↑u) = (p : C) := by
    rw [mul_comm (p : C) (↑u : C), ← mul_assoc, Units.inv_mul, one_mul]
  rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hk, hpow, hfin]

/-- `♯ (ϖ♭^{1/p^n})` is a nonzerodivisor. -/
theorem isSMulRegular_untilt_tiltRoot (P : DSMap.PerfectoidData p C) (c : Tilt p C)
    (hϖ : PreTilt.untilt c = P.ϖ 0) (n : ℕ) :
    IsSMulRegular C (PreTilt.untilt (tiltRoot p C c n)) :=
  isSMulRegular_of_pow_eq_varpi p C P _ n (by rw [untilt_tiltRoot_pow, hϖ])



end Work.DSPB2
