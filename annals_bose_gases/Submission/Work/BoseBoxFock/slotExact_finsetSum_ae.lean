import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.FibreProjDefs
import Submission.Work.BoseBoxFock.slotProj_finsetSum_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotExact_finsetSum_ae` — the `S`-sector is finitely additive

`slotExact e S Φ = ∑_{T ⊇ S} (-1)^{|T|−|S|} • slotProj e T Φ` (`FibreProjDefs`) is a fixed finite
`ℂ`-linear combination of the slot projections `slotProj e T`, and `slotProj e T` is itself the
Bochner integral of the kernel `∏_{i ∈ T} PV e (x i) (z i)` against the state, hence linear in the
state.  The target records that additivity a.e. on the box:

`slotExact e S (Σ_{k∈s} Θ k) =ᵐ[volume.restrict (abox n ℓ)] Σ_{k∈s} slotExact e S (Θ k)`.

The proof is a purely formal assembly of the sibling `slotProj_finsetSum_ae` (the corresponding
statement one level down): pull the finite sum over the supersets `T ⊇ S` inside, apply the
sibling at each `T` (collecting the finitely many a.e. statements with `Finset.eventually_all`),
distribute the scalar `(-1)^…` over the inner sum (`Finset.mul_sum`) and interchange the two sums
(`Finset.sum_comm`).  No hypothesis beyond `MemLp ⊤` on the modes and on the summands is used.
-/

namespace Work.BoseBoxFock

theorem slotExact_finsetSum_ae {m n : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {ι : Type*} (s : Finset ι)
    {Θ : ι → (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hΘ : ∀ k ∈ s, MeasureTheory.MemLp (Θ k) ⊤) :
    (fun x => Work.BoseBoxFock.slotExact e S (fun y => ∑ k ∈ s, Θ k y) x)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure
          (Fin n → EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => ∑ k ∈ s, Work.BoseBoxFock.slotExact e S (Θ k) x) := by
  classical
  -- the a.e. additivity of each slot projection `slotProj e T`, for all supersets `T ⊇ S` at once
  have hkey : ∀ᵐ x ∂((MeasureTheory.volume : MeasureTheory.Measure
      (Fin n → EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.abox n ℓ)),
      ∀ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
      Work.BoseBoxFock.slotProj e T (fun y => ∑ k ∈ s, Θ k y) x
        = ∑ k ∈ s, Work.BoseBoxFock.slotProj e T (Θ k) x := by
    rw [Finset.eventually_all]
    intro T _
    exact Work.BoseBoxFock.slotProj_finsetSum_ae hbdd hsupp T s hΘ
  filter_upwards [hkey] with x hx
  -- unfold `slotExact` into the pointwise finite `•`-combination of the `slotProj e T`
  simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  -- rewrite each `slotProj e T (Σ Θ)` by the sum of the `slotProj e T (Θ k)`, then swap the sums
  rw [Finset.sum_congr rfl (fun T hT => by rw [hx T hT, Finset.mul_sum])]
  exact Finset.sum_comm

end Work.BoseBoxFock
