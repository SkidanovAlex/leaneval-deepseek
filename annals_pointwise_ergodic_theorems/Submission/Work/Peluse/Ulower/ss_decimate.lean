import Mathlib
import Submission.Work.Peluse.Ulower.ss_aux_decimate

namespace Work.Peluse.Ulower

theorem ss_decimate {c : ℤ} (hc : c ≠ 0) {D L : ℕ} (hD : 1 ≤ D) {F : ℤ → ℂ}
    (hFs : Work.Peluse.SupportIn F L) (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1) {δ : ℝ}
    (hδ0 : 0 < δ)
    (hbox : δ ≤ Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Work.Peluse.arithIcc c D)
      (Work.Peluse.symIcc L) F) :
    ∃ r : ℕ, r < c.natAbs ∧
      ((Work.Peluse.symIcc L).card : ℝ) /
          ((c.natAbs : ℝ) * ((Work.Peluse.symIcc (max (L / c.natAbs + 1) D)).card : ℝ)) * δ ≤
        Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Work.Peluse.arithIcc 1 D)
          (Work.Peluse.symIcc (max (L / c.natAbs + 1) D)) (fun z : ℤ => F (c * z + (r : ℤ))) :=
  ss_aux_decimate hc hD hFs hF1 hδ0 hbox

end Work.Peluse.Ulower
