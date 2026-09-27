import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.AssemblyDefs
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.ExtGen.r_s_bookkeeping
import Submission.Work.KT.ExtGen.bottMap_surjective
import Submission.Work.KT.ExtGen.ker_r_subset_ker_pullDn

/-!
# `Work.KT.ExtGen.ker_bottMap` — the surjectivity half of `Work.KT.fund_product`, assembled

`Work.KT.ExtGen.bottMap_surjective` gives the Bott map's surjectivity onto the classes killed by
*both* disc restrictions, from (GEN) `Work.KT.kappa_span` plus the hypothesis (D) that every
clutched class is a multiple of `β`; `Work.KT.ExtGen.ker_r_subset_ker_pullDn` (base-point
independence of the two hemispheres) and `Work.KT.ExtGen.r_zero_imp_pullUp_zero`
(`ker r = ker pullUp`) pass from the two disc restrictions to the base-point restriction `Fund.r X`.

Consequently, on `X` compact Hausdorff,
`∀ z, Fund.r X z = 0 → ∃ b, z = Fund.bottMap X μ b` — the `hker` hypothesis of the assembly
`EG.fund_product_of_bott` — holds as soon as (D) does (`EG.kappa_reduce` / `Fund.kappa_lin`).
-/

namespace Work.KT.ExtGen

open Work.KT

noncomputable section

/-- **Surjectivity of the Bott map onto `ker (Fund.r X)`**, from (D). -/
theorem ker_bottMap (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ)) (hμ : IsK0Mul μ)
    (hD : ∀ (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ),
      ∃ b : K0 C(X, ℂ),
        Work.KT.Fund.kappa X n u - cls (Mat.one C(X × S2, ℂ) n) = Work.KT.Fund.bottMap X μ b) :
    ∀ z : K0 C(X × S2, ℂ), Work.KT.Fund.r X z = 0 →
      ∃ b : K0 C(X, ℂ), z = Work.KT.Fund.bottMap X μ b :=
  fun z hz => bottMap_surjective X μ hμ hD z (r_zero_imp_pullUp_zero X z hz)
    (ker_r_subset_ker_pullDn X z hz)

end

end Work.KT.ExtGen
