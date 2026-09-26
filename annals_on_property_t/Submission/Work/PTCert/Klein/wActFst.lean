import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.twistedFourierCriterion
import Submission.Work.PTCert.fourierWAct

namespace Work.PTCert.Klein

/-- Equivariance of the untwisted Fourier block `fourierW` in its first variable.
This is the `b = 0` case of `Work.PTCert.fourierWAct`. -/
theorem wActFst {m : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι) (M : Matrix ι ι ℝ)
    (S : Finset (Fin m))
    (hact : ∀ a b x, act (a + b) x = act a (act b x)) (hact0 : ∀ x, act 0 x = x)
    (hMinv : ∀ a x y, M (act a x) (act a y) = M x y)
    (ν : Fin m → ZMod 2) (u v : ι) :
    Submission.PTCert.fourierW act M S (act ν u) v
      = Submission.PTCert.chiS S ν * Submission.PTCert.fourierW act M S u v := by
  have h := Work.PTCert.fourierWAct act hact hact0 M hMinv S ν 0 u v
  rw [hact0 v, Work.PTCert.chiS_zero] at h
  rw [h]
  ring

end Work.PTCert.Klein
