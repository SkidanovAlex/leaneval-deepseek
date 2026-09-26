import Mathlib
import Submission.Work.PTCert.Cert2.Setup

namespace Work.PTCert.Cert2

open scoped BigOperators

/-- Folding `+` over `List.range n` (with an arbitrary accumulator) is addition of the
`Finset.sum` over `Finset.range n`. -/
lemma foldr_range_eq_sum_aux (n : ℕ) (f : ℕ → ℤ) (z : ℤ) :
    (List.range n).foldr (fun c acc => acc + f c) z = z + ∑ i ∈ Finset.range n, f i := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil]
    rw [ih (z + f n), Finset.sum_range_succ]
    ring

/-- **Residual facts of the `C2` certificate**: the class-involution symmetry of the residual
table, the vanishing of its total sum, and the absorption bound
`16 · Σ |res| ≤ (23/100) · 2^80 · 200`.  All three are the plain meaning of the kernel checks
`resSymOK` and `resBoundOK` (namespace `Submission.PTCert.C2K`). -/
theorem resC2 :
    (∀ cl < Submission.PTCert.G.ncls,
      Work.PTCert.Cert2.resZ (Submission.PTCert.G.icls cl) = Work.PTCert.Cert2.resZ cl ∧
      Submission.PTCert.G.icls (Submission.PTCert.G.icls cl) = cl) ∧
    (Finset.sum (Finset.range Submission.PTCert.G.ncls) Work.PTCert.Cert2.resZ = 0) ∧
    16 * (Finset.sum (Finset.range Submission.PTCert.G.ncls)
        (fun cl => |(Work.PTCert.Cert2.resZ cl : ℝ)|))
      ≤ (23 / 100 : ℝ) * (Work.PTCert.Cert2.scZ : ℝ) * (Work.PTCert.Cert2.denZ : ℝ) := by
  rw [show Submission.PTCert.G.ncls = 7229 from rfl]
  have hsym :=
    (Work.PTCert.Cert2.resSymOK_iff (List.range 7229)).mp Submission.PTCert.C2K.ressym_ok
  have hbnd := (Work.PTCert.Cert2.resBoundOK_iff (List.range 7229)
      Submission.PTCert.D2.resBound).mp Submission.PTCert.C2K.resbound_ok
  refine ⟨?_, ?_, ?_⟩
  · intro cl hcl
    exact hsym cl (List.mem_range.mpr hcl)
  · have h1 : (List.range 7229).foldr (fun c acc => acc + Work.PTCert.Cert2.resZ c) 0
        = ∑ i ∈ Finset.range 7229, Work.PTCert.Cert2.resZ i := by
      simpa using foldr_range_eq_sum_aux 7229 Work.PTCert.Cert2.resZ 0
    rw [h1] at hbnd
    exact hbnd.1
  · have hleZ : (16 : ℤ) * (∑ i ∈ Finset.range 7229, |Work.PTCert.Cert2.resZ i|)
        ≤ Submission.PTCert.D2.resBound := by
      have h2 := hbnd.2
      rw [foldr_range_eq_sum_aux 7229 (fun c => |Work.PTCert.Cert2.resZ c|) 0] at h2
      simpa using h2
    have hR : ((Submission.PTCert.D2.resBound : ℤ) : ℝ)
        = (23 / 100 : ℝ) * (Work.PTCert.Cert2.scZ : ℝ) * (Work.PTCert.Cert2.denZ : ℝ) := by
      norm_num [Submission.PTCert.D2.resBound, Work.PTCert.Cert2.scZ, Work.PTCert.Cert2.denZ]
    have hS : (∑ i ∈ Finset.range 7229, |(Work.PTCert.Cert2.resZ i : ℝ)|)
        = (((∑ i ∈ Finset.range 7229, |Work.PTCert.Cert2.resZ i|) : ℤ) : ℝ) := by
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl (fun i _ => (Int.cast_abs (a := Work.PTCert.Cert2.resZ i)).symm)
    rw [hS, ← hR]
    exact_mod_cast hleZ

end Work.PTCert.Cert2
