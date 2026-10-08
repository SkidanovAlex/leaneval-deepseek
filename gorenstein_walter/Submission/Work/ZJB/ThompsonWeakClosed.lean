import Submission.Work.ZJB.Defs
import Submission.Work.ZJB.ZJBasic

/-!
# ZJB — `J(P)` is weakly closed in `P`

The step Glauberman 1968 (p. 1119, step (II) of the proof of Theorem 5.1) calls "clear":
if `S` is a Sylow `p`-subgroup and `J(S)^b ≤ S`, then `J(S)^b = J(S)`.

The point is that no isomorphism-type argument is needed — the shape of `J` *inside* `P` is
what characterises it.  With `T := J(P)^b` (`b ∈ G` arbitrary):

* `J(T) = J(J(P)^b) = J(J(P))^b = J(P)^b = T` (Gorenstein 2.2: `J(J(P)) = J(P)`, plus
  covariance of `J` under an injective homomorphism);
* every `A ∈ A(T)` is an abelian subgroup of `T ≤ P` of order `A(J(P)) = A(P)` (conjugation
  carries `A(T)` onto `A(J(P))` with the same orders), so `A ∈ A(P)`, whence `A ≤ J(P)`;
  joining over `A ∈ A(T)` gives `T = J(T) ≤ J(P)`;
* `|T| = |J(P)|` because `T` is conjugate to `J(P)`;
* hence `T = J(P)`.
-/

namespace Work.ZJB

open Work.GW2
open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- All members of `maxAbelianIn P` have the same order. -/
theorem card_eq_of_mem_maxAbelianIn {P : Subgroup G} {A B : Subgroup G}
    (hA : A ∈ Subgroup.maxAbelianIn P) (hB : B ∈ Subgroup.maxAbelianIn P) :
    Nat.card A = Nat.card B :=
  le_antisymm (hB.2.2 A hA.1 hA.2.1) (hA.2.2 B hB.1 hB.2.1)

/-- **`A(J(P)) = A(P)`**, in the form used below: a maximal-order abelian subgroup of `J(P)`
has the same order as one of `P`.  This is Gorenstein 2.2(a) (`J(J(P)) = J(P)`), which the
library has as `Subgroup.thompsonJAbelian_eq_of_le_of_le`; here only the order consequence is
needed, and it follows directly from `J(P) ≤ P` and `A(P) ⊆ J(P)`. -/
theorem card_maxAbelianIn_thompsonJ {P : Subgroup G} (A : Subgroup G)
    (hA : A ∈ Subgroup.maxAbelianIn (Work.GW2.thompsonJ P)) (B : Subgroup G)
    (hB : B ∈ Subgroup.maxAbelianIn P) :
    Nat.card A = Nat.card B :=
  le_antisymm
    (hB.2.2 A (hA.1.trans (Work.GW2.thompsonJ_le P)) hA.2.1)
    (hA.2.2 B (Work.GW2.le_thompsonJ_of_mem_maxAbelianIn hB) hB.2.1)

/-- **`J(J(P)) = J(P)`** (Gorenstein 2.2, in the `J_a` language). -/
theorem thompsonJAbelian_thompsonJ (P : Subgroup G) :
    Subgroup.thompsonJAbelian (Work.GW2.thompsonJ P) = Work.GW2.thompsonJ P := by
  have h := Subgroup.thompsonJAbelian_eq_of_le_of_le (P := P) (Q := Work.GW2.thompsonJ P)
    (le_of_eq (Work.GW2.thompsonJ_eq_thompsonJAbelian P).symm) (Work.GW2.thompsonJ_le P)
  rw [h, Work.GW2.thompsonJ_eq_thompsonJAbelian P]

/-- **`J(P)` is weakly closed in `P`.**  If a conjugate of `J(P)` (Mathlib's conjugation,
`x ↦ b x b⁻¹`) is contained in `P`, it equals `J(P)`. -/
theorem thompsonJ_map_conj_eq_of_le (P : Subgroup G) (b : G)
    (hle : (Work.GW2.thompsonJ P).map (MulAut.conj b).toMonoidHom ≤ P) :
    (Work.GW2.thompsonJ P).map (MulAut.conj b).toMonoidHom = Work.GW2.thompsonJ P := by
  classical
  have hfinj : Function.Injective (MulAut.conj b).toMonoidHom := (MulAut.conj b).injective
  obtain ⟨B₀, hB₀⟩ := Subgroup.maxAbelianIn_nonempty P
  -- `J_a(J(P)) = J(P)`
  have hJJ := thompsonJAbelian_thompsonJ P
  -- `J_a(T) = T` for `T = J(P)^b`
  have hJaT : Subgroup.thompsonJAbelian
      ((Work.GW2.thompsonJ P).map (MulAut.conj b).toMonoidHom)
      = (Work.GW2.thompsonJ P).map (MulAut.conj b).toMonoidHom := by
    rw [Subgroup.thompsonJAbelian_map_of_injective hfinj, hJJ]
  -- every maximal-order abelian subgroup of `T` has the order of one of `P`
  have hcardT : ∀ A : Subgroup G,
      A ∈ Subgroup.maxAbelianIn ((Work.GW2.thompsonJ P).map (MulAut.conj b).toMonoidHom) →
      Nat.card A = Nat.card B₀ := by
    intro A hA
    obtain ⟨hcomap_mem, hmapcomap⟩ :=
      Subgroup.comap_mem_maxAbelianIn_of_injective hfinj
        (P := Work.GW2.thompsonJ P) hA
    have hcard : Nat.card A = Nat.card (A.comap (MulAut.conj b).toMonoidHom) := by
      conv_lhs => rw [← hmapcomap]
      exact Subgroup.card_map_of_injective hfinj
    rw [hcard]
    exact card_maxAbelianIn_thompsonJ _ hcomap_mem B₀ hB₀
  -- `T ≤ J(P)`: `T = J_a(T)` and each generator of `J_a(T)` lies in `J_a(P)`
  have hTJ : (Work.GW2.thompsonJ P).map (MulAut.conj b).toMonoidHom ≤ Work.GW2.thompsonJ P := by
    have h1 : Subgroup.thompsonJAbelian
        ((Work.GW2.thompsonJ P).map (MulAut.conj b).toMonoidHom)
        ≤ Subgroup.thompsonJAbelian P := by
      refine iSup_le fun A => iSup_le fun hA => ?_
      have hcardA : Nat.card A = Nat.card B₀ := hcardT A hA
      have hAP : A ∈ Subgroup.maxAbelianIn P :=
        ⟨hA.1.trans hle, hA.2.1,
          fun B hB hBc => hcardA.symm ▸ hB₀.2.2 B hB hBc⟩
      exact Subgroup.le_thompsonJAbelian_of_mem_maxAbelianIn hAP
    calc (Work.GW2.thompsonJ P).map (MulAut.conj b).toMonoidHom
        = Subgroup.thompsonJAbelian
            ((Work.GW2.thompsonJ P).map (MulAut.conj b).toMonoidHom) := hJaT.symm
      _ ≤ Subgroup.thompsonJAbelian P := h1
      _ = Work.GW2.thompsonJ P := (Work.GW2.thompsonJ_eq_thompsonJAbelian P).symm
  -- cardinality: `T` is conjugate to `J(P)`
  have hcard : Nat.card (Work.GW2.thompsonJ P)
      = Nat.card ((Work.GW2.thompsonJ P).map (MulAut.conj b).toMonoidHom) :=
    (Subgroup.card_map_of_injective hfinj).symm
  exact Subgroup.eq_of_le_of_card_ge hTJ hcard.le

/-- The paper's form, with Mathlib's conjugation written as a set image: `J(P)^b` is weakly
closed in `P`. -/
theorem thompsonJ_map_conj_eq_of_le' (P : Subgroup G) (b : G)
    (hle : (MulAut.conj b) '' ((Work.GW2.thompsonJ P : Set G)) ⊆ (P : Set G)) :
    (Work.GW2.thompsonJ P).map (MulAut.conj b).toMonoidHom = Work.GW2.thompsonJ P :=
  thompsonJ_map_conj_eq_of_le P b fun x hx => hle hx

end Work.ZJB
