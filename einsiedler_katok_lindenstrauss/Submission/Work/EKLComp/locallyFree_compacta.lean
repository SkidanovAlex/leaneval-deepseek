import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.V_open_one
import Submission.Work.EKLNonExc.DinjFacts

/-!
# `Work.EKLComp.locallyFree_compacta`

Local freeness of the `SL₃(ℝ)`-action on `X₃ = SL₃(ℝ)/SL₃(ℤ)` on compact sets (Pisa 6.1, the
fourth clause of the frozen component `Work.EKLContract.P_X3`): for every compact `K ⊆ X₃`
there is `δ > 0` such that no element of `V δ = {g | |gᵢⱼ - 1ᵢⱼ| < δ}` other than `1` fixes a
point of `K`.

This is the special case `h = 1` of `Work.EKLNonExc.Dinj δ`, the set of points at which the
orbit map `g ↦ g • x` is injective on `V δ`; the companion file `Work.EKLNonExc.DinjFacts`
(EKL L9.1 / Pisa 6.1) proves that every compact set lies in some `Dinj δ`.
-/

namespace Work.EKLComp

open Work.EKLContract

theorem locallyFree_compacta (K : Set Work.EKLContract.X3) (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ g : Work.EKLContract.SL3,
      g ∈ Work.EKLContract.V δ → g • x = x → g = 1 := by
  obtain ⟨δ, hδ, hsub⟩ := Work.EKLNonExc.compact_subset_Dinj hK
  refine ⟨δ, hδ, fun x hx g hg hgx => ?_⟩
  exact Work.EKLNonExc.mem_Dinj.mp (hsub hx) g 1 hg
    (Work.EKLContract.Lemmas.V_open_one δ hδ).2 (by rw [hgx, one_smul])

end Work.EKLComp
