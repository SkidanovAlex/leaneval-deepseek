import Mathlib
import Submission.Work.DSPB2.Basic
import Submission.Work.DSPB2.Tilt
import Submission.Work.DSPB2.coeff_mem_span_coeff
import Submission.Work.DSPB2.untilt_tiltRoot_mem_span

/-!
# DSPB2 — the mod-`p` / tilt identification (Bhatt–Morrow–Scholze, Lemma 3.5/3.10)

This file assembles the area `DSPB2` of the direct-summand proof map
(`sources/dsmap/direct_summand_mix_design.md` PB2, reviewed in
`sources/dsmap/direct_summand_mix_design_REVIEW.md` §3), and delivers the frozen statement
`DSMap.Mix.perfectoid_modp_tilt`.

Let `C` be integral perfectoid in the sense of `DSMap.PerfectoidData p C` (`p`-torsion-free,
`p`-adically complete, Frobenius surjective modulo `p`, `y ^ p ∈ pC → y ∈ (ϖ 0) C`, and
`(ϖ 0) ^ p = p · unit`), and let `ϖf ∈ C♭ = PreTilt C p` satisfy `♯ ϖf = ϖ 0`.  The theorem says
that the `♯`-map induces a ring isomorphism `C ⧸ (p) ≅ C♭ ⧸ (ϖ♭) ^ p`, i.e.
`e (x♯ mod p) = x mod (ϖ♭) ^ p`.

## Proof

Write `R = C♭ = lim_φ (C ⧸ p)`, `ϖₙ = ♯ (ϖf ^ (1/p^n))` (the `n`-th `p`-power root of `ϖ 0` in `C`)
and `coeff n : R → C ⧸ p` for the `n`-th coefficient.  The two inputs are

* `coeff 0` is surjective (`coeff_zero_surjective`, from Frobenius surjectivity modulo `p`);
* `Work.DSPB2.coeff_mem_span_coeff` plus `Work.DSPB2.untilt_tiltRoot_mem_span`: if `♯ y ∈ (ϖ 0)`
  then `♯ (y ^ (1/p^n)) ∈ (ϖₙ)` for every `n`.  Since `ϖₙ` is a nonzerodivisor
  (`isSMulRegular_untilt_tiltRoot`), the quotients `vₙ := ♯(y^{1/p^n}) / ϖₙ` are *unique* and
  satisfy `vₙ₊₁ ^ p = vₙ`, so they glue to an element `d ∈ R` with `ϖf * d = y`
  (`exists_mul_eq_of_untilt_mem`).

Applying the second point to `y = x ^ (1/p)` for `x` with `coeff 0 x = 0` (i.e. `♯ x ∈ (p)`, so
`♯ (x ^ (1/p)) ∈ (ϖ 0)` by the injectivity of Frobenius modulo `ϖ`) gives `x = ϖf ^ p * d ^ p`,
i.e. `mem_span_varpi_pow_of_coeff_zero_eq_zero`: `ker (coeff 0) ⊆ (ϖf ^ p)`.  The reverse
inclusion is `coeff_zero_mul_varpi_pow`, so `ker (coeff 0) = (ϖf ^ p)`; the first isomorphism
theorem then gives that `coeff 0` descends to an isomorphism inverse to `♯` modulo `p`.

## Main results

* `Work.DSPB2.exists_mul_eq_of_untilt_mem` — the `ϖ`-form: `♯ y ∈ (ϖ 0) → ∃ d, ϖf * d = y`.
* `Work.DSPB2.mem_span_varpi_pow_of_coeff_zero_eq_zero` — `ker (coeff 0) ⊆ (ϖf ^ p)`.
* `Work.DSPB2.coeff_zero_mul_varpi_pow` — `(ϖf ^ p) ⊆ ker (coeff 0)`.
* `DSMap.Mix.perfectoid_modp_tilt_proved` — the frozen statement, proved.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Work.DSPB2

universe a

open Ideal

variable (p : ℕ) [Fact p.Prime] (C : Type a) [CommRing C] (P : DSMap.PerfectoidData p C)
  [Fact ¬IsUnit (p : C)] [IsAdicComplete (Ideal.span {(p : C)}) C]

/-- **The `ϖ`-form of the tilt-kernel computation.**  If `♯ c = ϖ 0` and `♯ y ∈ (ϖ 0)`, then `y` is
divisible by `c` in the tilt.  (`c` is `ϖ♭`; the statement is Bhatt–Morrow–Scholze's
`ker (C♭ → C ⧸ (ϖ)) = ϖ♭ · C♭`.) -/
theorem exists_mul_eq_of_untilt_mem (c y : PreTilt C p) (hϖ : PreTilt.untilt c = P.ϖ 0)
    (hy : PreTilt.untilt y ∈ Ideal.span {P.ϖ 0}) : ∃ d : PreTilt C p, c * d = y := by
  classical
  have hmem : ∀ n, PreTilt.untilt (tiltRoot p C y n) ∈
      Ideal.span {PreTilt.untilt (tiltRoot p C c n)} :=
    untilt_tiltRoot_mem_span p C P c y hϖ hy
  choose v hv using fun n => Ideal.mem_span_singleton'.mp (hmem n)
  have hcompat : ∀ n, (v (n + 1)) ^ p = v n := by
    intro n
    refine isSMulRegular_untilt_tiltRoot p C P c hϖ n ?_
    simp only [smul_eq_mul]
    calc PreTilt.untilt (tiltRoot p C c n) * v (n + 1) ^ p
        = (PreTilt.untilt (tiltRoot p C c (n + 1)) * v (n + 1)) ^ p := by
          rw [mul_pow, untilt_tiltRoot_succ p C c n]
      _ = PreTilt.untilt (tiltRoot p C y n) := by
          rw [mul_comm (PreTilt.untilt (tiltRoot p C c (n + 1))) (v (n + 1)), hv (n + 1),
            untilt_tiltRoot_succ p C y n]
      _ = PreTilt.untilt (tiltRoot p C c n) * v n := by
          rw [← hv n, mul_comm]
  let d : PreTilt C p := ⟨fun n => Ideal.Quotient.mk (Ideal.span {(p : C)}) (v n), by
    intro n
    rw [← map_pow, hcompat n]⟩
  have hdc : ∀ n, PreTilt.coeff n d = Ideal.Quotient.mk (Ideal.span {(p : C)}) (v n) :=
    fun n => rfl
  refine ⟨d, ?_⟩
  apply Perfection.ext
  intro n
  show PreTilt.coeff n (c * d) = PreTilt.coeff n y
  rw [map_mul, coeff_eq_mk_untilt_tiltRoot p C c n, coeff_eq_mk_untilt_tiltRoot p C y n,
    hdc n, ← map_mul, mul_comm (PreTilt.untilt (tiltRoot p C c n)) (v n), hv n]

/-- **The kernel of `coeff 0` is contained in `(ϖf ^ p)`**: if the `0`-th coefficient of `x`
vanishes (equivalently `♯ x ∈ (p)`), then `x = ϖf ^ p · d ^ p`. -/
theorem mem_span_varpi_pow_of_coeff_zero_eq_zero (ϖf x : PreTilt C p)
    (hϖ : PreTilt.untilt ϖf = P.ϖ 0) (hx : PreTilt.coeff 0 x = 0) :
    x ∈ Ideal.span {ϖf ^ p} := by
  -- `♯ x ∈ (p) = (ϖ 0 ^ p)`, hence `♯ (x ^ (1/p)) ∈ (ϖ 0)` by the injectivity axiom.
  have h1 : PreTilt.untilt x ∈ Ideal.span {(p : C)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_zero_untilt p C x, hx]
  have h2 : PreTilt.untilt (tiltRoot p C x 1) ∈ Ideal.span {P.ϖ 0} := by
    refine DSMap.PerfectoidData.frobInj P _ ?_
    rw [untilt_tiltRoot_succ p C x 0, tiltRoot_zero]
    exact h1
  obtain ⟨d, hd⟩ := exists_mul_eq_of_untilt_mem p C P ϖf (tiltRoot p C x 1) hϖ h2
  have hx' : x = ϖf ^ p * d ^ p := by
    rw [← tiltRoot_pow p C x 1, ← hd, mul_pow, pow_one]
  rw [hx']
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- **`(ϖf ^ p) ⊆ ker (coeff 0)`.** -/
theorem coeff_zero_mul_varpi_pow (ϖf : PreTilt C p) (hϖ : PreTilt.untilt ϖf = P.ϖ 0) :
    PreTilt.coeff 0 (ϖf ^ p) = 0 := by
  obtain ⟨u, hu⟩ := P.unit
  rw [map_pow, coeff_eq_mk_untilt_tiltRoot p C ϖf 0, tiltRoot_zero, hϖ, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton'.mpr ⟨↑u, by rw [mul_comm, hu]⟩

end Work.DSPB2

/-! ## The delivered theorem (the frozen statement `DSMap.Mix.perfectoid_modp_tilt`) -/

namespace DSMap.Mix

universe a

/-- **PB2** (Bhatt–Morrow–Scholze, Lemma 3.5(ii)/3.10, in the `ϖ ^ p = p · unit` convention): for
an integral perfectoid ring `C` and `ϖf ∈ C♭` with `♯ ϖf = ϖ 0`, the `♯`-map induces a ring
isomorphism `C ⧸ (p) ≅ C♭ ⧸ (ϖ♭) ^ p`. -/
theorem perfectoid_modp_tilt_proved (p : ℕ) [Fact p.Prime] (C : Type a) [CommRing C]
    (P : DSMap.PerfectoidData p C) [Fact ¬IsUnit (p : C)] (ϖf : PreTilt C p)
    (hϖ : (letI := P.complete; PreTilt.untilt ϖf) = P.ϖ 0) :
    letI := P.complete
    ∃ e : (C ⧸ Ideal.span {(p : C)}) ≃+* (PreTilt C p ⧸ Ideal.span {ϖf ^ p}),
      ∀ x : PreTilt C p, e (Ideal.Quotient.mk _ (PreTilt.untilt x)) = Ideal.Quotient.mk _ x := by
  letI : IsAdicComplete (Ideal.span {(p : C)}) C := P.complete
  have hsurj : Function.Surjective (PreTilt.coeff 0 : PreTilt C p →+* ModP C p) :=
    Work.DSPB2.coeff_zero_surjective p C P
  have hkill : ∀ a : PreTilt C p, a ∈ Ideal.span {ϖf ^ p} → PreTilt.coeff 0 a = 0 := by
    intro a ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ha
    rw [← hb]
    have hm : PreTilt.coeff 0 (b * ϖf ^ p) =
        PreTilt.coeff 0 b * PreTilt.coeff 0 (ϖf ^ p) := map_mul (PreTilt.coeff 0) b (ϖf ^ p)
    rw [hm, Work.DSPB2.coeff_zero_mul_varpi_pow p C P ϖf hϖ, mul_zero]
  let ē : PreTilt C p ⧸ Ideal.span {ϖf ^ p} →+* ModP C p :=
    Ideal.Quotient.lift _ (PreTilt.coeff 0) hkill
  have hē : ∀ a : PreTilt C p, ē (Ideal.Quotient.mk _ a) = PreTilt.coeff 0 a :=
    fun _ => Ideal.Quotient.lift_mk _ (PreTilt.coeff 0) hkill
  have hbij : Function.Bijective ē := by
    refine ⟨?_, ?_⟩
    · intro u v huv
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
      rw [hē, hē] at huv
      have h0 : PreTilt.coeff 0 (a - b) = 0 := by
        rw [map_sub (PreTilt.coeff 0) a b, huv, sub_self]
      rw [Ideal.Quotient.eq]
      exact Work.DSPB2.mem_span_varpi_pow_of_coeff_zero_eq_zero p C P ϖf (a - b) hϖ h0
    · intro y
      obtain ⟨a, ha⟩ := hsurj y
      exact ⟨Ideal.Quotient.mk _ a, by rw [hē, ha]⟩
  refine ⟨(RingEquiv.ofBijective ē hbij).symm, ?_⟩
  intro x
  rw [PreTilt.mk_untilt_eq_coeff_zero]
  exact (RingEquiv.symm_apply_eq (RingEquiv.ofBijective ē hbij)).mpr (hē x).symm

end DSMap.Mix

namespace Work.DSPB2

universe a

/-- The delivered theorem, also available under the `Work.DSPB2` namespace. -/
alias perfectoid_modp_tilt_proved := DSMap.Mix.perfectoid_modp_tilt_proved

end Work.DSPB2
