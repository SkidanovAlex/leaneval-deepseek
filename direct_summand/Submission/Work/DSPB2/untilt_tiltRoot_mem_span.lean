import Mathlib
import Submission.Work.DSPB2.Basic
import Submission.Work.DSPB2.Tilt
import Submission.Work.DSPB2.coeff_mem_span_coeff

/-!
# DSPB2 — divisibility of `♯`-images of `p`-power roots

Third layer of DSPB2.  We upgrade the mod-`p` statement `coeff_mem_span_coeff`
(`coeff n y ∈ (coeff n c)`) to its lift to `C`:

`♯ (y^{1/p^n}) ∈ (♯ (c^{1/p^n}))`   whenever   `♯ y ∈ (ϖ 0)`, `♯ c = ϖ 0`.

The point is that `coeff n z` is exactly the reduction of `♯ (z^{1/p^n})` mod `p`, and that
`(p) ⊆ (♯ (c^{1/p^n}))` (`p_mem_span_untilt_tiltRoot`), so membership in the principal ideal
`(♯ (c^{1/p^n}))` can be checked after reduction mod `p`.
-/

set_option linter.unusedSectionVars false

namespace Work.DSPB2

universe a

open Ideal

/-- `PreTilt.coeff n x` is the reduction mod `p` of `♯ (x ^ (1/p^n))`. -/
theorem coeff_eq_mk_untilt_tiltRoot (p : ℕ) [Fact p.Prime] (C : Type a) [CommRing C]
    [Fact ¬IsUnit (p : C)] [IsAdicComplete (Ideal.span {(p : C)}) C]
    (x : PreTilt C p) (n : ℕ) :
    PreTilt.coeff n x =
      Ideal.Quotient.mk (Ideal.span {(p : C)}) (PreTilt.untilt (tiltRoot p C x n)) := by
  rw [← coeff_zero_tiltRoot p C x n, coeff_zero_untilt]

theorem untilt_tiltRoot_mem_span (p : ℕ) [Fact p.Prime] (C : Type a) [CommRing C]
    (P : DSMap.PerfectoidData p C) [Fact ¬IsUnit (p : C)]
    [IsAdicComplete (Ideal.span {(p : C)}) C]
    (c y : PreTilt C p) (hϖ : PreTilt.untilt c = P.ϖ 0)
    (hy : PreTilt.untilt y ∈ Ideal.span {P.ϖ 0}) :
    ∀ n : ℕ, PreTilt.untilt (Work.DSPB2.tiltRoot p C y n) ∈
      Ideal.span {PreTilt.untilt (Work.DSPB2.tiltRoot p C c n)} := by
  -- Reduction of `hy` mod `p`, in the coefficient language.
  have hy' : PreTilt.coeff 0 y ∈ Ideal.span {PreTilt.coeff 0 c} := by
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hy
    have hc : PreTilt.coeff 0 c =
        Ideal.Quotient.mk (Ideal.span {(p : C)}) (P.ϖ 0) := by
      rw [coeff_zero_untilt, hϖ]
    have hy0 : PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {(p : C)}) w *
        Ideal.Quotient.mk (Ideal.span {(p : C)}) (P.ϖ 0) := by
      rw [coeff_zero_untilt, ← hw, map_mul]
    rw [hy0, hc]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  intro n
  -- The already-proved mod-`p` statement.
  have hcoeff := coeff_mem_span_coeff p C P c y hϖ hy' n
  rw [coeff_eq_mk_untilt_tiltRoot p C y n,
    coeff_eq_mk_untilt_tiltRoot p C c n] at hcoeff
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hcoeff
  obtain ⟨B, rfl⟩ := Ideal.Quotient.mk_surjective b
  -- `♯ (y^{1/p^n}) ≡ B * ♯ (c^{1/p^n})` modulo `(p)`.
  have hz : Ideal.Quotient.mk (Ideal.span {(p : C)})
      (PreTilt.untilt (tiltRoot p C y n) - B * PreTilt.untilt (tiltRoot p C c n)) = 0 := by
    rw [map_sub, map_mul, ← hb, sub_self]
  have hker : PreTilt.untilt (tiltRoot p C y n) - B * PreTilt.untilt (tiltRoot p C c n)
      ∈ Ideal.span {(p : C)} := Ideal.Quotient.eq_zero_iff_mem.mp hz
  -- `p` lies in the principal ideal `(♯ (c^{1/p^n}))`, so `(p)` does too.
  have hp : (p : C) ∈ Ideal.span {PreTilt.untilt (tiltRoot p C c n)} :=
    p_mem_span_untilt_tiltRoot p C P c hϖ n
  have hle : Ideal.span {(p : C)} ≤ Ideal.span {PreTilt.untilt (tiltRoot p C c n)} :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp)
  have hsum : (PreTilt.untilt (tiltRoot p C y n) - B * PreTilt.untilt (tiltRoot p C c n))
      + B * PreTilt.untilt (tiltRoot p C c n) ∈
      Ideal.span {PreTilt.untilt (tiltRoot p C c n)} :=
    Ideal.add_mem _ (hle hker)
      (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  rwa [sub_add_cancel] at hsum

end Work.DSPB2
