import Mathlib
import Submission.Work.DSPB2.Basic
import Submission.Work.DSPB2.Tilt

namespace Work.DSPB2

universe a

set_option linter.unusedSectionVars false

/-- The `p`-th power of the `(n+1)`-st coefficient is the `n`-th coefficient: the inverse
direction of `PreTilt.coeff_pow_p`.  Needed to descend divisibility along the `p`-power tower. -/
private theorem coeff_succ_pow (p : ℕ) [Fact p.Prime] (C : Type a) [CommRing C]
    [Fact ¬IsUnit (p : C)] [IsAdicComplete (Ideal.span {(p : C)}) C]
    (x : PreTilt C p) (n : ℕ) :
    (PreTilt.coeff (n + 1) x) ^ p = PreTilt.coeff n x := by
  rw [← coeff_zero_tiltRoot p C x (n + 1), coeff_zero_untilt, ← map_pow,
    untilt_tiltRoot_succ, ← coeff_zero_untilt, coeff_zero_tiltRoot]

set_option maxHeartbeats 1600000 in
theorem coeff_mem_span_coeff (p : ℕ) [Fact p.Prime] (C : Type a) [CommRing C]
    (P : DSMap.PerfectoidData p C) [Fact ¬IsUnit (p : C)]
    [IsAdicComplete (Ideal.span {(p : C)}) C]
    (c y : PreTilt C p) (hϖ : PreTilt.untilt c = P.ϖ 0)
    (hy : PreTilt.coeff 0 y ∈ Ideal.span {PreTilt.coeff 0 c}) :
    ∀ n : ℕ, PreTilt.coeff n y ∈ Ideal.span {PreTilt.coeff n c} := by
  intro n
  induction n with
  | zero => exact hy
  | succ n ih =>
    have hz : (PreTilt.coeff (n + 1) y) ^ p
        ∈ Ideal.span {(PreTilt.coeff (n + 1) c) ^ p} := by
      rw [coeff_succ_pow p C y n, coeff_succ_pow p C c n]
      exact ih
    have hmU : PreTilt.coeff 0 c ∈ Ideal.span {PreTilt.coeff (n + 1) c} := by
      refine Ideal.mem_span_singleton'.mpr
        ⟨(PreTilt.coeff (n + 1) c) ^ (p ^ (n + 1) - 1), ?_⟩
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos),
        pow_coeff p C c (n + 1)]
    have hm : ∀ a : ModP C p, a ^ p = 0 → a ∈ Ideal.span {PreTilt.coeff 0 c} := by
      have h0 : PreTilt.coeff 0 c = Ideal.Quotient.mk _ (P.ϖ 0) := by
        rw [coeff_zero_untilt, hϖ]
      intro a ha
      have := pow_p_eq_zero_mem_span_varpi p C P a ha
      rwa [h0]
    exact pth_root_mem p C P hm hmU hz

end Work.DSPB2
