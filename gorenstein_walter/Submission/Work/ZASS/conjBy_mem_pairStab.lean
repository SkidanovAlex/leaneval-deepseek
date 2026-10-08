import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.Zassenhaus.Basic

namespace Work.ZASS

/-- **Z6 API (HB III XI 1.5/1.7).** If `s` interchanges the points `a` and `b`, then `s`
normalizes the pointwise stabilizer `G_{ab}`: for `h` fixing `a` and `b` pointwise, `s h s⁻¹`
fixes both `a` and `b` (using `s⁻¹ • b = a` and `s⁻¹ • a = b`), hence lies in `G_{ab}` too.
In particular `N_G(G_{ab}) ⊇ G_{ab}⟨s⟩`, which is the first step of HB 1.5 (`T = N_G(H)`,
`|T : H| ≤ 2`).  No Zassenhaus hypothesis is used. -/
theorem conjBy_mem_pairStab {G X : Type} [Group G] [MulAction G X] {a b : X} {s : G}
    (hsa : s • a = b) (hsb : s • b = a) {h : G}
    (hh : h ∈ Work.Zassenhaus.pairStab G a b) :
    Work.ZASS.conjBy s h ∈ Work.Zassenhaus.pairStab G a b := by
  -- `s` interchanges `a` and `b`, so `s⁻¹` does too.
  have h1 : s⁻¹ • b = a := by rw [← hsa, inv_smul_smul]
  have h2 : s⁻¹ • a = b := by rw [← hsb, inv_smul_smul]
  -- unfold membership in the two-point stabilizer
  rw [Work.Zassenhaus.mem_pairStab_iff] at hh ⊢
  refine ⟨?_, ?_⟩
  · show (s * h * s⁻¹) • b = b
    rw [mul_smul, mul_smul, h1, hh.2, hsa]
  · show (s * h * s⁻¹) • a = a
    rw [mul_smul, mul_smul, h2, hh.1, hsb]

end Work.ZASS
