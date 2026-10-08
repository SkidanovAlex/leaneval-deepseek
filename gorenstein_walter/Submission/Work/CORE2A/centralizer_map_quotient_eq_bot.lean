/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.perfect_hom_odd_card

/-!
# The centralizer in `K ⧸ C_K(E)` of the image of a perfect subgroup `E`

Let `K` be a finite group, let `E ≤ K` be a perfect subgroup and let `C = C_K(E)` be its
centralizer.  If `|C|` is odd — so that `C` is solvable, by the odd order theorem, which is
available in this development as the hypothesis `Work.GW2.FeitThompsonProp` — then the
centralizer in `K ⧸ C` of the image of `E` is trivial.

Proof.  Let `y = xC` centralize the image `EC/C` of `E`.  Then `⁅x, e⁆ ∈ C` for every `e ∈ E`.
The map `φ : E → C`, `e ↦ ⁅x, e⁆`, is a homomorphism: because `⁅x, g⁆ ∈ C` commutes with every
element of `E`, the standard identity
`⁅x, e * g⁆ = ⁅x, e⁆ * e * ⁅x, g⁆ * e⁻¹`
collapses to `⁅x, e * g⁆ = ⁅x, e⁆ * ⁅x, g⁆`.  The image `φ(E)` is a quotient of the perfect
group `E`, hence perfect, and it is a subgroup of the odd-order group `C`, hence solvable
(Feit–Thompson); a perfect solvable group is trivial, so `φ = 1`.  Thus `⁅x, e⁆ = 1` for every
`e ∈ E`, i.e. `x ∈ C` and `y = 1`.

## Main result

* `Work.CORE2A.centralizer_map_quotient_eq_bot`
-/

namespace Work.CORE2A

open scoped commutatorElement

/-! ## Two elementary steps -/

/-- If the coset `xC` centralizes the image of `E` in `K ⧸ C`, then `⁅x, e⁆ ∈ C` for every
`e ∈ E`. -/
private theorem commutator_mem_of_mem_quotient_centralizer_aux {K : Type} [Group K]
    (E C : Subgroup K) [hCn : C.Normal] {x : K}
    (hy : QuotientGroup.mk' C x ∈ Subgroup.centralizer
      ((E.map (QuotientGroup.mk' C) : Subgroup (K ⧸ C)) : Set (K ⧸ C))) :
    ∀ e ∈ E, ⁅x, e⁆ ∈ C := by
  intro e he
  have hmem : QuotientGroup.mk' C e ∈ E.map (QuotientGroup.mk' C) :=
    Subgroup.mem_map.mpr ⟨e, he, rfl⟩
  have hcomm := (Subgroup.mem_centralizer_iff.mp hy) (QuotientGroup.mk' C e) hmem
  rw [commutatorElement_def, ← QuotientGroup.ker_mk' C, MonoidHom.mem_ker]
  simp only [map_mul, map_inv]
  rw [← hcomm]
  group

/-- The cocycle `e ↦ ⁅x, e⁆` is multiplicative on `E`, provided all its values lie in
`C = C_K(E)`. -/
private theorem commutator_mul_of_mem_centralizer_aux {K : Type} [Group K] (E C : Subgroup K)
    (hC : C = Subgroup.centralizer (E : Set K)) (x : K)
    (hmem : ∀ e ∈ E, ⁅x, e⁆ ∈ C) {e g : K} (he : e ∈ E) (hg : g ∈ E) :
    ⁅x, e * g⁆ = ⁅x, e⁆ * ⁅x, g⁆ := by
  have hcomm : e * ⁅x, g⁆ = ⁅x, g⁆ * e :=
    (Subgroup.mem_centralizer_iff.mp (hC ▸ hmem g hg)) e he
  have hcomm' : e * ⁅x, g⁆ * e⁻¹ = ⁅x, g⁆ := by
    rw [hcomm]
    group
  rw [commutatorElement_mul_right_eq_mul_conj,
    show ⁅x, e⁆ * e * ⁅x, g⁆ * e⁻¹ = ⁅x, e⁆ * (e * ⁅x, g⁆ * e⁻¹) by group,
    hcomm']

/-! ## The main result -/

theorem centralizer_map_quotient_eq_bot {K : Type} [Group K] [Finite K] (E C : Subgroup K)
    (hC : C = Subgroup.centralizer (E : Set K)) [hCn : C.Normal]
    (hperf : ⁅E, E⁆ = E) (hft : Work.GW2.FeitThompsonProp) (hCodd : Odd (Nat.card C)) :
    Subgroup.centralizer ((E.map (QuotientGroup.mk' C) : Subgroup (K ⧸ C)) :
      Set (K ⧸ C)) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  -- it remains to show that `x` centralizes `E`
  have hmem : ∀ e ∈ E, ⁅x, e⁆ ∈ C :=
    commutator_mem_of_mem_quotient_centralizer_aux E C hy
  have hEperf : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hperf
  let φ : ↥E →* ↥C :=
    { toFun := fun e => ⟨⁅x, (e : K)⁆, hmem (e : K) e.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun e g => Subtype.ext
        (commutator_mul_of_mem_centralizer_aux E C hC x hmem e.2 g.2) }
  -- `φ` is a homomorphism from a perfect group into an odd-order group, hence trivial
  have hφ : φ = 1 := perfect_hom_odd_card hft hCodd φ
  rw [hC, Subgroup.mem_centralizer_iff]
  intro e he
  have h1 : φ ⟨e, he⟩ = 1 := by rw [hφ]; rfl
  have hval : ((φ ⟨e, he⟩ : ↥C) : K) = ⁅x, e⁆ := rfl
  have h2 : ⁅x, e⁆ = 1 := by
    have h4 : ((φ ⟨e, he⟩ : ↥C) : K) = 1 :=
      congrArg (fun z : ↥C => (z : K)) h1
    rw [hval] at h4
    exact h4
  exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm

end Work.CORE2A
