import Mathlib
import Submission.Work.PTCert.OrbitKeysDefs

namespace Work.PTCert.OrbitKeys

/-- The word of the key `(r, g)` evaluates, in the free group, to
`f(x₀_r)⁻¹ * f(grep g)`: the letters `invL` invert the two half-codes of `x0c r`, and the
remaining two letters `grepE r g / 128`, `grepE r g % 128` are exactly the two factors of
`eltC (grepE r g)`. -/
theorem keyWordLprod (hE : Submission.PTCert.G.ESem) {r g : ℕ} (hx : Submission.PTCert.G.x0c r ∈ Submission.PTCert.G.eS) :
    Submission.PTCert.lprod 5 (Submission.PTCert.G.keyWord r g) = (Submission.PTCert.eltC (Submission.PTCert.G.x0c r))⁻¹ * Submission.PTCert.eltC (Submission.PTCert.G.grepE r g) := by
  have hxA : Submission.PTCert.G.x0c r ∈ Submission.PTCert.D.eAll :=
    (mem_eS_iff (Submission.PTCert.G.x0c r)).mp hx
  obtain ⟨hdiv, hmod, -⟩ := hE.2.2.1 (Submission.PTCert.G.x0c r) hxA
  have hdiv' : Submission.PTCert.G.x0c r / 128 < Submission.PTCert.NB1 5 := by
    rw [show Submission.PTCert.NB1 5 = 81 from by norm_num [Submission.PTCert.NB1]]; exact hdiv
  have hmod' : Submission.PTCert.G.x0c r % 128 < Submission.PTCert.NB1 5 := by
    rw [show Submission.PTCert.NB1 5 = 81 from by norm_num [Submission.PTCert.NB1]]; exact hmod
  simp only [Submission.PTCert.lprod, Submission.PTCert.G.keyWord, Submission.PTCert.eltC,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← Work.PTCert.b1_inv 5 (Submission.PTCert.G.x0c r % 128) hmod',
    ← Work.PTCert.b1_inv 5 (Submission.PTCert.G.x0c r / 128) hdiv', mul_inv_rev]
  group

end Work.PTCert.OrbitKeys
