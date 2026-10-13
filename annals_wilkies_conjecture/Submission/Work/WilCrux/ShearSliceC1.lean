import Mathlib
import Submission.Work.WilCrux.Defs
import Submission.Work.WilG4c.StepCleanDefs

namespace Work.WilCrux

/-- **N3c (the sheared slices are `C^1`).**  The shear is an affine change of the fibre variable
`u ↦ φ v + u`, so a slice of the sheared family is a slice of `g` (at the parameter `w(v)`)
precomposed with a translation; `C^1`-ness transfers.  (`hvW` is the membership `w(v) ∈ W`
needed for `hsm`; the set in the conclusion is the preimage of `U` under `u ↦ reindex (φ v + u)`.) -/
theorem ShearSliceC1 {m n1 n2 N : ℕ} (g : (Fin m → ℝ) → (Fin N → ℝ) → ℝ)
    (e : Fin N ≃ Fin (n1 + n2)) (φ : (Fin (m + n1) → ℝ) → (Fin n2 → ℝ))
    (W : Set (Fin m → ℝ)) (U : Set (Fin N → ℝ)) (hU : IsOpen U)
    (hsm : ∀ w ∈ W, ContDiffOn ℝ 1 (g w) U) (v : Fin (m + n1) → ℝ)
    (hvW : (fun i : Fin m => v (Fin.castAdd n1 i)) ∈ W) :
    ContDiffOn ℝ 1 (Work.WilCrux.shearFam g e φ v)
      {u | (fun j : Fin N => (Fin.append (fun k : Fin n1 => v (Fin.natAdd m k)) (φ v + u)) (e j))
        ∈ U} := by
  -- Write the shear as `(g w) ∘ T` with `w` the base parameter and `T` the affine reindexing.
  let w : Fin m → ℝ := fun i => v (Fin.castAdd n1 i)
  let A : Fin n1 → ℝ := fun k => v (Fin.natAdd m k)
  let b : Fin n2 → ℝ := φ v
  let T : (Fin n2 → ℝ) → (Fin N → ℝ) := fun u j => (Fin.append A (b + u)) (e j)
  have hw : w ∈ W := hvW
  -- `u ↦ Fin.append A (b + u)` is smooth: a constant tuple appended to a translated tuple.
  have hV : ContDiff ℝ 1 (fun u : Fin n2 → ℝ => Fin.append A (b + u)) := by
    rw [contDiff_pi]
    intro i
    refine Fin.addCases (motive := fun i =>
      ContDiff ℝ 1 (fun u : Fin n2 → ℝ => Fin.append A (b + u) i)) ?_ ?_ i
    · intro i'
      simpa only [Fin.append_left] using
        (contDiff_const (c := A i') : ContDiff ℝ 1 (fun _ : Fin n2 → ℝ => A i'))
    · intro j'
      rw [show (fun u : Fin n2 → ℝ => Fin.append A (b + u) (Fin.natAdd n1 j')) =
            (fun x : Fin n2 → ℝ =>
              b j' + (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n2 => ℝ) j') x) from by
          funext u; rw [Fin.append_right]; rfl]
      exact ContDiff.add (contDiff_const (c := b j'))
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n2 => ℝ) j').contDiff)
  -- Reindexing by `e` is linear (hence smooth), so `T` is smooth.
  have hT : ContDiff ℝ 1 T := by
    have hR : ContDiff ℝ 1 (fun x : Fin (n1 + n2) → ℝ => fun j : Fin N => x (e j)) :=
      (ContinuousLinearMap.pi (R := ℝ) (φ := fun _ : Fin N => ℝ)
        (fun j : Fin N => ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin (n1 + n2) => ℝ) (e j))).contDiff
    exact hR.comp hV
  -- Compose the smooth reindexing with the `C¹` slice on `U`.
  exact (hsm w hw).comp hT.contDiffOn (fun x hx => hx)

end Work.WilCrux
