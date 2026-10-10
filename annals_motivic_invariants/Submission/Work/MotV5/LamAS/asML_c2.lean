import Mathlib
import Submission.Work.MotV5.LamAS.asML
import Submission.Work.MotC2.aut_functionField

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotV5.LamAS

/-- The automorphism classification (node C2, `Work.MotC2.aut_functionField`) over the two-root Artin–Schreier field `L = K⟮asRoot f₁, asRoot f₂⟯`: every `L`-algebra automorphism of `M = L(E)` is `τ_Q ∘ [-1]^ε` with `Q` an `L`-rational point of `E_L` and `ε : Fin 2`. -/
theorem asML_c2 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (f₁ f₂ : RatFunc 𝕜)
    [DecidableEq ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)]
    [hEll : (Work.MotV5.LamAS.asE2 D f₁ f₂).IsElliptic]
    (Θ : Work.MotV5.LamAS.asML D f₁ f₂ ≃ₐ[↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)]
      Work.MotV5.LamAS.asML D f₁ f₂) :
    ∃ (Q : (Work.MotV5.LamAS.asE2 D f₁ f₂).toAffine.Point) (ε : Fin 2),
      Θ = Work.MotC2.transAlgEquiv (Work.MotV5.LamAS.asE2 D f₁ f₂) Q *
        (Work.MotC2.negAlgEquiv (Work.MotV5.LamAS.asE2 D f₁ f₂)) ^ (ε : ℕ) := by
  -- `asML D f₁ f₂ = L(E_L)` with `L = ↥(asL2 f₁ f₂)` and `E_L = D.E.baseChange L`, so this is
  -- `Work.MotC2.aut_functionField` for the base-changed curve, once we know that `j(E_L) ≠ 0, 1728`.
  have hGood : Work.MotV.KleinData.Good D := hD.1
  haveI : D.E.IsElliptic := hGood.elliptic
  -- base change is `map` along the algebra map, and `j` is natural under `map`
  have hjmap : (Work.MotV5.LamAS.asE2 D f₁ f₂).j =
      algebraMap 𝕜 ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂) D.E.j := by
    simp only [Work.MotV5.LamAS.asE2, WeierstrassCurve.baseChange, WeierstrassCurve.map_j]
  have hj0 : (Work.MotV5.LamAS.asE2 D f₁ f₂).j ≠ 0 := by
    rw [hjmap]
    exact fun hh => hGood.j_ne_zero
      ((algebraMap 𝕜 ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)).injective (by simpa using hh))
  have hj1728 : (Work.MotV5.LamAS.asE2 D f₁ f₂).j ≠ 1728 := by
    rw [hjmap]
    intro hh
    exact hGood.j_ne ((algebraMap 𝕜 ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)).injective (by
      rw [map_ofNat]; exact hh))
  exact Work.MotC2.aut_functionField ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)
    (Work.MotV5.LamAS.asE2 D f₁ f₂) hj0 hj1728 Θ

end Work.MotV5.LamAS
