import Mathlib
import Submission.Work.BW.Est17Ext
import Submission.Work.BW.Kimg
import Submission.Work.BW.finrank_Kimg
import Submission.Work.BW.logHeight_intermediate
import Submission.Work.BW.logHeight_algEquiv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-- Projective heights scale by the degree in the Kummer extension: for a tuple `p` of elements
of `K`, its image in `L = ℚ(φ(K), ρ₁,…,ρ_r)` has `2^r` times the height. -/
theorem est17_height_ext {K : Type*} [Field K] [NumberField K] {r : ℕ} {φ : K →+* ℂ}
    {ρ : Fin r → ℂ} {η : Fin r → K} (hη : ∀ j, η j ≠ 0)
    (hρ : ∀ j, ρ j ^ 2 = φ (η j)) (hK : KummerCond η) [inst : NumberField (EL φ ρ)]
    {ι : Type*} [Fintype ι] (p : ι → K) :
    Height.logHeight (fun i => inclE φ ρ (p i)) = ((2 : ℝ) ^ r) * Height.logHeight p := by
  haveI hNF : NumberField (Kimg φ ρ) := Kimg_numberField φ ρ
  -- The tower `ℚ ⊆ Kimg φ ρ ⊆ EL φ ρ`, with `[EL φ ρ : Kimg φ ρ] = 2 ^ r`.
  have hdeg : Module.finrank ↥(Kimg φ ρ) (EL φ ρ) = 2 ^ r := finrank_Kimg hη hρ hK
  have h1 : Height.logHeight (fun i => ((KimgEquiv φ ρ (p i) : Kimg φ ρ) : EL φ ρ))
      = ((Module.finrank ↥(Kimg φ ρ) (EL φ ρ) : ℕ) : ℝ)
        * Height.logHeight (fun i => KimgEquiv φ ρ (p i)) :=
    logHeight_intermediate (K := EL φ ρ) (Kimg φ ρ) (x := fun i => KimgEquiv φ ρ (p i))
  -- Heights are invariant under the isomorphism `K ≃ₐ[ℚ] Kimg φ ρ`.
  have h2 : Height.logHeight (fun i => KimgEquiv φ ρ (p i)) = Height.logHeight p :=
    logHeight_algEquiv (KimgEquiv φ ρ) p
  rw [show (fun i => inclE φ ρ (p i))
        = (fun i => ((KimgEquiv φ ρ (p i) : Kimg φ ρ) : EL φ ρ)) from by
      funext i; exact (KimgEquiv_apply (p i)).symm]
  rw [h1, h2, hdeg]
  push_cast
  ring

end Work.BW
