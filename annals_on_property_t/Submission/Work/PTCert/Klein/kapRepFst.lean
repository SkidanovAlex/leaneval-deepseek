import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.twistedFourierCriterion

namespace Work.PTCert.Klein

theorem kapRepFst {m m2 : ℕ} {ι : Type} (act : (Fin m → ZMod 2) → ι → ι)
    (kap : (Fin m2 → ZMod 2) → ι → ι)
    (θ : (Fin m2 → ZMod 2) → (Fin m → ZMod 2) → (Fin m → ZMod 2))
    (nu : ι → (Fin m → ZMod 2)) (rep : ι → ι)
    (hact : ∀ a b x, act (a + b) x = act a (act b x))
    (hactnu : ∀ x, act (nu x) (rep x) = x) (hrepact : ∀ a x, rep (act a x) = rep x)
    (hcomm : ∀ b a x, kap b (act a x) = act (θ b a) (kap b x))
    (b : Fin m2 → ZMod 2) (u : ι) :
    rep (kap b (rep u)) = rep (kap b u) := by
  have h : kap b u = act (θ b (nu u)) (kap b (rep u)) := by
    calc kap b u
        = kap b (act (nu u) (rep u)) := by rw [hactnu u]
      _ = act (θ b (nu u)) (kap b (rep u)) := hcomm b (nu u) (rep u)
  rw [h, hrepact]

end Work.PTCert.Klein
