import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI
import Submission.Work.ORHughesFree.NaturalExtension.ModuleDim
import Submission.Work.ORHughesFree.NaturalExtension.dimOf_principal
import Submission.Work.ORHughesFree.NaturalExtension.rdimAdditivity
import Submission.Work.ORHughesFree.NaturalExtension.dimOf_comp_le

universe u

namespace Work.Section3

open Work.ORHughesFree.NaturalExtension

theorem oneByOne_le_rdim_span {S : Type u} [Ring S] [Work.ORHughesFree.VonNeumannRegularRing S]
    (ρ : Work.ORHughesFree.SylvesterRank S) {n : ℕ} {s : S}
    (ψ : (Fin n → S) →ₗ[S] (Fin 1 → S)) (u : Fin n → S)
    (hu : ψ u = (fun _ => s)) :
    ρ.rk 1 1 (Work.ORHughesFree.oneByOne s)
      ≤ Work.ORHughesFree.NaturalExtension.rdim ρ (Submodule.span S ({u} : Set (Fin n → S))) := by
  -- The rank of the `1 × 1` matrix `(s)` is the dimension of the span of the constant vector `s`,
  -- which is `ψ u`, the image of the one-element family `u` under the linear map `ψ`; a linear
  -- image never increases dimension (`dimOf_comp_le`).
  set v : Fin 1 → (Fin n → S) := fun _ => u with hv
  have hψv : (fun j : Fin 1 => ψ (v j)) = (fun _ : Fin 1 => (fun _ : Fin 1 => s)) := by
    funext j
    rw [hv]
    exact hu
  have hspan : Set.range v = ({u} : Set (Fin n → S)) := by
    rw [hv]
    exact Set.range_const
  calc ρ.rk 1 1 (Work.ORHughesFree.oneByOne s)
      = dimOf ρ (fun _ : Fin 1 => (fun _ : Fin 1 => s)) := (dimOf_principal ρ s).symm
    _ = dimOf ρ (fun j : Fin 1 => ψ (v j)) := by rw [hψv]
    _ ≤ dimOf ρ v := dimOf_comp_le ρ ψ v
    _ = rdim ρ (Submodule.span S (Set.range v)) := (rdim_span_range ρ v).symm
    _ = rdim ρ (Submodule.span S ({u} : Set (Fin n → S))) := by rw [hspan]

end Work.Section3
