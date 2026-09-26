import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.twistedFourierCriterion

open scoped BigOperators

namespace Work.PTCert.Klein

theorem wKap {m m2 : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι)
    (kap : (Fin m2 → ZMod 2) → ι → ι)
    (θ : (Fin m2 → ZMod 2) → (Fin m → ZMod 2) → (Fin m → ZMod 2))
    (M : Matrix ι ι ℝ) (S : Finset (Fin m))
    (hcomm : ∀ b a x, kap b (act a x) = act (θ b a) (kap b x)) (hθ : ∀ b a, θ b (θ b a) = a)
    (hchiθ : ∀ b a, Submission.PTCert.chiS S (θ b a) = Submission.PTCert.chiS S a)
    (hMkap : ∀ b x y, M (kap b x) (kap b y) = M x y)
    (b : Fin m2 → ZMod 2) (u v : ι) :
    Submission.PTCert.fourierW act M S (kap b u) (kap b v)
      = Submission.PTCert.fourierW act M S u v := by
  unfold Submission.PTCert.fourierW
  -- Invert the commutation relation: `kap b` intertwines `act` with `θ b`-twisted `act`.
  have h1 : ∀ a : Fin m → ZMod 2,
      Submission.PTCert.chiS S a * M (kap b u) (act a (kap b v))
        = Submission.PTCert.chiS S (θ b a) * M u (act (θ b a) v) := by
    intro a
    have hk : act a (kap b v) = kap b (act (θ b a) v) := by
      have h := hcomm b (θ b a) v
      rw [hθ b a] at h
      exact h.symm
    rw [hk, hMkap b u (act (θ b a) v), hchiθ b a]
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  -- Reindex the sum by the involution `θ b` (which permutes the group `(ℤ/2)^m`).
  exact Equiv.sum_comp ⟨θ b, θ b, hθ b, hθ b⟩
    (fun a => Submission.PTCert.chiS S a * M u (act a v))

end Work.PTCert.Klein
