import Mathlib
import Submission.Work.SGsep.hand.HandDefs2

namespace Work.SGsep.hand

open Work.SG Work.SG.Data Work.SGsep.Hand Work.SGsep.Hand.Data

/-- Unpacking the handedness check `Data.HandCert.chk` in the `some` case: the certificate
certifies the rotation structure of the element `i` of representative `k` — the axis `c` is
fixed by `A`, primitive (via `beta`), positively oriented, `N_A = c wᵀ`, `h = gcd w` (via `beta2`)
and `v_A = j c`. -/
theorem chk_some {k i : Nat} {c : HandCert} (h : HandCert.chk k i (some c) = true) :
    (A3n k i).det = 1 ∧ (A3n k i).ord = c.ord ∧ 3 ≤ c.ord ∧
    (A3n k i).mulV c.c = c.c ∧ V3.dot c.beta c.c = 1 ∧
    0 < M3.det (M3.ofCols (e3 c.q) ((A3n k i).mulV (e3 c.q)) c.c) ∧
    ((A3n k i).normSum c.ord).cols = [V3.smul c.w.x c.c, V3.smul c.w.y c.c, V3.smul c.w.z c.c] ∧
    0 < c.h ∧ V3.dvd (c.h : Int) c.w = true ∧
    V3.dot c.beta2 (V3.ediv c.w (c.h : Int)) = 1 ∧ vOf k i = V3.smul c.j c.c := by
  simp only [HandCert.chk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

end Work.SGsep.hand
