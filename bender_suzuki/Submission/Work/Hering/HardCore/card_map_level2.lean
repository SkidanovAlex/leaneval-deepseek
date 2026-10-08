import Mathlib
import Submission.Work.Hering.Config
import Submission.Work.Hering.HardCore.abelian_setup
import Submission.Work.Hering.HardCore.sq_level2_surj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The image of the second level of `C_G(V)` in `G/V` has order `8`

In the abelian configuration of the hard core of Hering's theorem,

* `V ⊴ G` is elementary abelian of order `8`,
* `C = C_G(V)` is an abelian `2`-group with `Ω₁(C) = V` (`hinv`),
* `G/C ≅ Aut(V)` (`hAut`),
* `C` is not elementary abelian (`hne`),

the image of the second level `level2 V C = {x ∈ C | x * x ∈ V}` under the quotient map
`G → G/V` has order `8`.

The proof packages the squaring map as a homomorphism `sq : C₂ → V`, `x ↦ x * x`
(`C₂` is a subgroup since `C` is abelian).  Its image is `V` (`sq_level2_surj`), and its kernel
consists of the `x ∈ C₂` with `x * x = 1`, which are exactly the elements of `V`
(`mem_V_iff`).  On the other hand the image of `C₂` in `G/V` is the range of the composite
`C₂ → G → G/V`, whose kernel is the same `V ∩ C₂ = V`.  Comparing the two descriptions of
`C₂ / V` through the first isomorphism theorem gives the result.
-/

set_option autoImplicit false

namespace Work.Hering.HardCore

open LeanEval.GroupTheory.Defs

theorem card_map_level2 {G : Type*} [Group G] [Finite G] (V C : Subgroup G) [V.Normal]
    (hcard : Nat.card V = 8) (hexp : ∀ x ∈ V, x * x = 1)
    (hC : C = Subgroup.centralizer ((V : Set G))) (hC2 : IsPGroup 2 ↥C)
    (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V)
    (hAut : ActsAsAut V (inferInstance : V.Normal))
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hne : ∃ c ∈ C, c * c ≠ 1) :
    Nat.card ↥((level2 V C hC hCab hexp).map (QuotientGroup.mk' V)) = 8 := by
  classical
  let L : Subgroup G := level2 V C hC hCab hexp
  -- the squaring map `L → V`
  let sq : ↥L →* ↥V :=
    { toFun := fun x => ⟨(x : G) * (x : G), x.2.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        have hx : (x : G) ∈ C := x.2.1
        have hy : (y : G) ∈ C := y.2.1
        have hcomm : (x : G) * (y : G) = (y : G) * (x : G) := hCab _ hx _ hy
        show ((x : G) * (y : G)) * ((x : G) * (y : G))
            = ((x : G) * (x : G)) * ((y : G) * (y : G))
        calc ((x : G) * (y : G)) * ((x : G) * (y : G))
            = (x : G) * ((y : G) * (x : G)) * (y : G) := by group
          _ = (x : G) * ((x : G) * (y : G)) * (y : G) := by rw [hcomm]
          _ = ((x : G) * (x : G)) * ((y : G) * (y : G)) := by group }
  -- squaring is onto `V`
  have hsq_surj : Function.Surjective sq := by
    intro v
    obtain ⟨x, hxL, hxv⟩ := sq_level2_surj V C hcard hexp hC hC2 hinv hAut hCab hne v.2
    exact ⟨⟨x, hxL⟩, Subtype.ext hxv⟩
  have hsq_range : sq.range = ⊤ := MonoidHom.range_eq_top_of_surjective sq hsq_surj
  -- the kernel of squaring is `V`
  have hsq_ker : sq.ker = Subgroup.comap L.subtype V := by
    ext x
    have hx : sq x = 1 ↔ ((x : G) * (x : G) : G) = 1 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [Subgroup.mem_comap, MonoidHom.mem_ker, hx]
    exact (mem_V_iff V C hexp hinv x.2.1).symm
  -- the image of `L` in `G/V`
  let f' : ↥L →* G ⧸ V := (QuotientGroup.mk' V).comp L.subtype
  have hf'ker : f'.ker = sq.ker := by
    rw [hsq_ker]
    show ((QuotientGroup.mk' V).comp L.subtype).ker = Subgroup.comap L.subtype V
    rw [← MonoidHom.comap_ker (QuotientGroup.mk' V) L.subtype, QuotientGroup.ker_mk']
  have hfr : f'.range = L.map (QuotientGroup.mk' V) := by
    show ((QuotientGroup.mk' V).comp L.subtype).range = L.map (QuotientGroup.mk' V)
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  -- both `L ⧸ V` descriptions agree with `V`, hence have `8` elements
  have key : Nat.card ↥f'.range = 8 := by
    calc Nat.card ↥f'.range
        = Nat.card (↥L ⧸ f'.ker) :=
          (Nat.card_congr (QuotientGroup.quotientKerEquivRange f').toEquiv).symm
      _ = Nat.card (↥L ⧸ sq.ker) := by rw [hf'ker]
      _ = Nat.card ↥sq.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange sq).toEquiv
      _ = Nat.card ↥(⊤ : Subgroup ↥V) := by rw [hsq_range]
      _ = Nat.card ↥V := Nat.card_congr (Subgroup.topEquiv).toEquiv
      _ = 8 := hcard
  change Nat.card ↥(L.map (QuotientGroup.mk' V)) = 8
  rw [← hfr]
  exact key

end Work.Hering.HardCore
