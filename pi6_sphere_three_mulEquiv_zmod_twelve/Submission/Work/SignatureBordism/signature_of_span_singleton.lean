import Mathlib
import Submission.Work.SignatureBordism.Signature

set_option linter.style.haveILetI false

namespace Work.SignatureBordism

open QuadraticMap in
theorem signature_of_span_singleton {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] (Q : QuadraticForm 𝕜 V) (v : V)
    {a : 𝕜} (hv : Submodule.span 𝕜 {v} = ⊤) (ha : Q v = a) (ha0 : a ≠ 0) :
    Work.SignatureBordism.signature Q = if 0 < a then 1 else -1 := by
  -- `v` is nonzero, since `Q v = a ≠ 0 = Q 0`.
  have hv_ne : v ≠ 0 := fun h => ha0 (by rw [← ha, h, map_zero])
  -- `V` is one-dimensional, spanned by `v`.
  have hfinrank : Module.finrank 𝕜 V = 1 :=
    (finrank_eq_one_iff_of_nonzero v hv_ne).mpr hv
  haveI : Module.Finite 𝕜 V :=
    FiniteDimensional.of_finrank_eq_succ (n := 0) (by simpa using hfinrank)
  -- On a one-dimensional space spanned by a vector with strictly positive value, the form is
  -- positive definite and the signature is `+1`.
  have hmain : ∀ (P : QuadraticForm 𝕜 V) (b : 𝕜), 0 < b → P v = b →
      sigPos P = 1 ∧ sigNeg P = 0 := by
    intro P b hb hPb
    have hPle : sigPos P ≤ 1 := by rw [← hfinrank]; exact sigPos_le_finrank P
    have hposdef : (QuadraticMap.restrict P (𝕜 ∙ v)).PosDef := by
      intro x hx
      rw [QuadraticMap.restrict_apply]
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.2
      rw [← hc]
      have hkey : P (c • v) = (c * c) * b := by
        rw [QuadraticMap.map_smul, hPb, smul_eq_mul]
      rw [hkey]
      exact mul_pos (mul_self_pos.mpr (fun hc0 =>
        hx (Subtype.ext (by rw [← hc, hc0, zero_smul]; simp)))) hb
    have hPge : 1 ≤ sigPos P := by
      rw [← finrank_span_singleton (K := 𝕜) hv_ne]
      exact le_sigPos_of_posDef P hposdef
    have hP : sigPos P = 1 := le_antisymm hPle hPge
    refine ⟨hP, ?_⟩
    have hadd := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := P)
    rw [hP, hfinrank] at hadd
    omega
  by_cases h : 0 < a
  · rw [if_pos h]
    obtain ⟨hP, hN⟩ := hmain Q a h ha
    simp only [Work.SignatureBordism.signature, hP, hN]
    norm_num
  · rw [if_neg h]
    -- now `a < 0`, so `-a > 0` and we apply the positive case to `-Q`
    have ha_neg : a < 0 := lt_of_le_of_ne (le_of_not_gt h) ha0
    have hneg : 0 < -a := neg_pos.mpr ha_neg
    have hQv : (-Q) v = -a := by simp [ha]
    obtain ⟨hP, hN⟩ := hmain (-Q) (-a) hneg hQv
    have hsigPos : sigPos Q = 0 := by rw [← sigNeg_neg (Q := Q)]; exact hN
    have hsigNeg : sigNeg Q = 1 := by rw [← sigPos_neg (Q := Q)]; exact hP
    simp only [Work.SignatureBordism.signature, hsigPos, hsigNeg]
    norm_num

end Work.SignatureBordism
