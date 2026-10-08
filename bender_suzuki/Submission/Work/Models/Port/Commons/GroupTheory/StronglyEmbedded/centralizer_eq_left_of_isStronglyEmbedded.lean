import Mathlib.Order.CompletePartialOrder
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.centralizer_le_of_isStronglyEmbedded
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.centralizer_inf_eq_sup_of_eq_sup_of_le_normalizer_of_central

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

open Commons.GroupTheory

theorem centralizer_eq_left_of_isStronglyEmbedded {G : Type*} [Group G] [Finite G]
    (M U T : Subgroup G) (hMtop : M ≠ ⊤) (hEven : Even (Nat.card M))
    (hOdd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    (hB : M = U ⊔ T) (hdisj : U ⊓ T = ⊥) (hTnorm : T ≤ Subgroup.normalizer (U : Set G))
    {u : G} (hu : u ∈ U) (hu2 : orderOf u = 2)
    (hcu : ∀ a ∈ U, a * u = u * a)
    (hfpf : ∀ t ∈ T, t ∈ Subgroup.centralizer ({u} : Set G) → t = 1) :
    Subgroup.centralizer ({u} : Set G) = U := by
  set C : Subgroup G := Subgroup.centralizer ({u} : Set G) with hC
  -- `u` lies in `M`
  have huM : u ∈ M := by rw [hB]; exact Subgroup.mem_sup_left hu
  -- the centralizer of the involution `u` is contained in `M`
  have hCM : C ≤ M :=
    centralizer_le_of_isStronglyEmbedded M hOdd huM hu2
  -- decompose `C ⊓ M` using the `U ⊔ T` structure of `M`
  have hinf : C ⊓ M = U ⊔ (T ⊓ C) :=
    Commons.GroupTheory.Subgroup.centralizer_inf_eq_sup_of_eq_sup_of_le_normalizer_of_central
      M U T hB hdisj hTnorm hu hcu
  -- the fixed-point-free condition forces `T ⊓ C = ⊥`
  have hTC : T ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    rw [Subgroup.mem_bot]
    exact hfpf x hx.1 hx.2
  have hCeq : C = C ⊓ M := (inf_eq_left.mpr hCM).symm
  rw [hCeq, hinf, hTC, sup_bot_eq]

end Commons.GroupTheory.StronglyEmbedded