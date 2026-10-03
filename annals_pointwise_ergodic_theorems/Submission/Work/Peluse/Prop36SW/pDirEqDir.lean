import Mathlib
import Submission.Work.Peluse.ladderBaseDefs
import Submission.Work.Peluse.Prop36SW.existsSlotSetEquivI

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-- **Reindexing a box-norm-power's direction family along an equivalence of the index types.**

The value does not depend on the enumerations `e`, `e'` (they enter only through the permutation
`e ∘ φ.symm ∘ e'⁻¹ ∘ cast` of `Fin (card ι)`).  This is the tool that identifies the ladder's
`FamIdx`-indexed direction family with the `D.I`-indexed family of `D.famNorm`: combine it with
`pDir_eq_dir` (which supplies `Q ∘ φ = Q'`) and the equivalence
`FamIdx (k := fun _ : D.S j => 1) (fun _ => 1) ≃ SlotSet (D.S j) (fun _ => 1) ≃ D.I j`. -/
lemma boxNormPow_family_equiv {ι ι' : Type} [Fintype ι] [Fintype ι'] (φ : ι ≃ ι')
    (Q : ι → Finset ℤ) (e : ι ≃ Fin (Fintype.card ι)) (e' : ι' ≃ Fin (Fintype.card ι'))
    (hcard : Fintype.card ι = Fintype.card ι') (S : Finset ℤ) (f : ℤ → ℂ) :
    boxNormPow (Fintype.card ι) (fun i => Q (e.symm i)) S f
      = boxNormPow (Fintype.card ι') (fun i => Q (φ.symm (e'.symm i))) S f := by
  set Q' : Fin (Fintype.card ι') → Finset ℤ := fun j => Q (φ.symm (e'.symm j)) with hQ'
  have h1 : boxNormPow (Fintype.card ι) (fun i => Q' (Fin.cast hcard i)) S f
      = boxNormPow (Fintype.card ι') Q' S f :=
    LadderA.boxNormPow_reindex hcard ((finCongr hcard).symm) Q' S f
  have h2 := BoxNorm.boxNormPow_perm ((finCongr hcard).trans (e'.symm.trans (φ.symm.trans e)))
    (fun i : Fin (Fintype.card ι) => Q (e.symm i)) S f
  have h3 : (fun i : Fin (Fintype.card ι) => Q (e.symm
        (((finCongr hcard).trans (e'.symm.trans (φ.symm.trans e))) i)))
      = (fun i => Q' (Fin.cast hcard i)) := by
    funext i
    have hsig : e.symm (((finCongr hcard).trans (e'.symm.trans (φ.symm.trans e))) i)
        = φ.symm (e'.symm (Fin.cast hcard i)) := by
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      rfl
    rw [hsig, hQ']
  rw [h3] at h2
  rw [← h2, h1]

end

end Work.Peluse.Prop36SW
