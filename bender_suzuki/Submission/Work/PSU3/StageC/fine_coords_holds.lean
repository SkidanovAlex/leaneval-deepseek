import Mathlib
import Submission.Work.PSU3.FineCoords.Setup
import Submission.Work.PSU3.FineCoords.equivariant

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open scoped commutatorElement

open Work.ThmF

namespace Work.PSU3.StageC

theorem fine_coords_holds {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n)
    (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2) :
    ∃ e : Q ≃* SZ (Work.PSU3.E n), ∃ μ : (Work.PSU3.E n)ˣ,
      (∀ x : Q, (e x).x = (μ : Work.PSU3.E n) * Multiplicative.toAdd (fr.bar x)) ∧
      (∀ hs : fr.zc 1 ∈ Q, (e ⟨fr.zc 1, hs⟩).x = 0 ∧ (e ⟨fr.zc 1, hs⟩).y = 1) ∧
      (∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
        e y = SZ.torusAct (fr.κ d) (e x)) := by
  obtain ⟨μ, e₀, he₀⟩ := fr.exists_good hsq
  obtain ⟨e, he, heq⟩ := fr.exists_equivariant_good hsq μ e₀ he₀
  refine ⟨e, μ, fun x => he.xcoord x, ?_, heq⟩
  intro hs
  have hbar : fr.bar (⟨fr.zc 1, hs⟩ : Q) = 1 :=
    (fr.bar_eq_one_iff _).mpr (fr.zc_mem 1 (by simp))
  have hmem : fr.barA (⟨fr.zc 1, hs⟩ : Q) = 0 := by
    rw [show fr.barA (⟨fr.zc 1, hs⟩ : Q) =
      Multiplicative.toAdd (fr.bar (⟨fr.zc 1, hs⟩ : Q)) from rfl, hbar]
    rfl
  rw [he.kern (⟨fr.zc 1, hs⟩ : Q) hmem]
  refine ⟨rfl, ?_⟩
  show (fr.kerCoord (⟨fr.zc 1, hs⟩ : Q) hmem : E n) = 1
  have h1 : (fr.kerCoord (⟨fr.zc 1, hs⟩ : Q) hmem : Fx n) = 1 := by
    apply fr.zc_inj_Fx
    rw [fr.zc_kerCoord]
    show fr.zc 1 = fr.zc (1 : E n)
    simp
  exact congrArg Subtype.val h1

end Work.PSU3.StageC
