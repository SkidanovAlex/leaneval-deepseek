import Mathlib
import Submission.Work.Peluse.Ulower.ss_char_entry_defs
import Submission.Work.Peluse.Ulower.ss_aux_const_compare

namespace Work.Peluse.Ulower

theorem const_compare {K : ℕ} (hK : 1 ≤ K) {C δ η cmin Amax Ns D L'' : ℝ}
    (hC : 0 < C) (hcmin : 0 < cmin) (hAmax : 0 < Amax) (hδ : 0 < δ) (hD : 0 < D)
    (hη : cmin * δ ≤ η) (hNs : 0 < Ns) (hL'' : 0 < L'') (hL''Amax : L'' ≤ Amax * Ns) :
    C * cmin ^ K / Amax ^ (K - 1) * δ ^ K * (D / Ns) ^ K * Ns ≤
      C * η ^ K * (D / L'') ^ K * L'' :=
  ss_aux_const_compare hK hC hcmin hAmax hδ hD hη hNs hL'' hL''Amax

end Work.Peluse.Ulower
