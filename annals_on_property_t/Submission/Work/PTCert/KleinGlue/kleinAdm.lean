import Mathlib
import Submission.Work.PTCert.Glue3

namespace Work.PTCert.KleinGlue

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.RouteB

/-- The base-character mask `S_k = {0, …, k-1}` is a proper `5`-bit mask for `k ≤ 5`. -/
lemma Sk_lt_thirtytwo (k : ℕ) (hk : k ≤ 5) : Sk k < 32 := by
  have h2 : 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hk
  unfold Sk
  omega

theorem kleinAdm (hCF : CodeFacts) (hA : ActSetup) (hNst : NStructure) (hN : NSem) (hBB : BitsBridge)
    (hK : ∀ k ≤ 5, KleinSem k) (k : ℕ) (hk : k ≤ 5)
    (hts : ∀ i < nK k, (ksL.getD k []).getD i 0 < 611)
    (i : ℕ) (hi : i < nK k) :
    repE (kE k i) = kE k i ∧
    (∀ a : Fin 5 → ZMod 2, actN a (kE k i) = kE k i → chiS (SkF k) a = 1) := by
  obtain ⟨-, hcov, hdist, -, -⟩ := hK k hk
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, htabN⟩ := hA
  obtain ⟨-, -, -, -, -, hrepEI⟩ := hNst
  obtain ⟨-, hzscEx, hchiBr, -, -, -⟩ := hBB
  have ht : (ksL.getD k []).getD i 0 < 611 := hts i hi
  have hiL : i < (ksL.getD k []).length := hi
  have hkE1 : (kE k i).1 = rp ((ksL.getD k []).getD i 0) := (hrepEI _ ht pt0).2
  refine ⟨(hrepEI _ ht pt0).1, ?_⟩
  intro a ha
  obtain ⟨sc, hsc, hsca⟩ := hzscEx 5 a
  have hfix : actC cmT (ntab sc) (rp ((ksL.getD k []).getD i 0)) = rp ((ksL.getD k []).getD i 0) := by
    have h1 := htabN sc hsc (kE k i)
    rw [hsca, ha] at h1
    rw [hkE1] at h1
    exact h1.symm
  have hne : cG (kwTs.getD k (NT.leaf 0)) ((ksL.getD k []).getD i 0) ≠ 0 := by
    rw [(hdist i hiL).1]
    omega
  have hchi5 : chiS5 (Sk k) sc = 1 := ((hcov _ ht).2 hne).1 sc hsc hfix
  rw [← hsca]
  show chiS (maskSet (m := 5) (Sk k)) (zOfSc sc) = 1
  rw [hchiBr (Sk k) sc (Sk_lt_thirtytwo k hk) hsc, hchi5]
  norm_num

end Work.PTCert.KleinGlue
