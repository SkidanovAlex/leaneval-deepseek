import Mathlib
import Submission.Work.Hering.Config
import Submission.Work.Hering.HardCore.abelian_setup
import Submission.Work.Hering.HardCore.level2_quotient_equiv_V

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `G/V` acts on `C₂ V / V` as all of its automorphisms

Context: the abelian configuration of the hard core of Hering's theorem.  `V ⊴ G` is elementary
abelian (`hexp`), `C = C_G(V)` is abelian (`hCab`), `Ω₁(C) = V` (`hinv`) and the squaring map
`C₂ = level2 V C = {x ∈ C | x * x ∈ V} → V`, `x ↦ x * x`, is onto (`hsq`).

Write `L = C₂` and `L̄ = L·V/V ≤ G/V` (its normality in `G/V` is the hypothesis `hVbar`).  Since
`x ↦ x * x` is a surjective homomorphism `L → V` with kernel `V`, it induces an isomorphism
`e : L̄ ≃* V` (`Work.Hering.HardCore.level2_quotient_equiv_V`), and because `C` is abelian the
squaring map is equivariant for conjugation:

  `e (ḡ x ḡ⁻¹) = g (e x) g⁻¹`  for all `g ∈ G`, `x ∈ L̄`

(`level2_quotient_equiv_equivariance` below).  Consequently the conjugation action of `G/V` on
`L̄` corresponds, under `e`, to the conjugation action of `G` on `V`; and the latter realises all
of `Aut(V)` by `hAut`.  Transferring an automorphism `φ` of `L̄` to `Aut(V)` through `e` and
applying `hAut` therefore produces `ḡ ∈ G/V` whose conjugation is `φ`:

`G/V` acts on `L̄` as all of `Aut(L̄)`, i.e. `ActsAsAut L̄ hVbar`.

This is the interface needed to apply the induction hypothesis of Peterfalvi I §3 Prop. 2 to the
smaller group `G/V`.
-/

set_option autoImplicit false

namespace Work.Hering.HardCore

open LeanEval.GroupTheory.Defs

/-- **Equivariance of the squaring isomorphism `L̄ ≃* V`.**  If `e` computes the square on the
image of the second level `L = level2 V C` (`he`), then for the conjugation actions
`e (ḡ x ḡ⁻¹) = g (e x) g⁻¹` for every `g ∈ G` and `x ∈ L̄`.

Indeed, if `x = [y]` with `y ∈ L`, then `g y g⁻¹ ∈ L` (because `C ⊴ G` and `V ⊴ G`), so `he`
computes both sides: `e [g y g⁻¹] = (g y g⁻¹)² = g y² g⁻¹ = g (e x) g⁻¹`. -/
theorem level2_quotient_equiv_equivariance {G : Type*} [Group G] [Finite G] (V C : Subgroup G)
    [V.Normal]
    (hC : C = Subgroup.centralizer ((V : Set G)))
    (hexp : ∀ x ∈ V, x * x = 1)
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hVbar : ((level2 V C hC hCab hexp).map (QuotientGroup.mk' V)).Normal)
    (e : ↥((level2 V C hC hCab hexp).map (QuotientGroup.mk' V)) ≃* ↥V)
    (he : ∀ y (hy : y ∈ level2 V C hC hCab hexp),
        e ⟨QuotientGroup.mk' V y, Subgroup.mem_map_of_mem (QuotientGroup.mk' V) hy⟩
          = ⟨y * y, hy.2⟩) :
    ∀ (g : G) (x : ↥((level2 V C hC hCab hexp).map (QuotientGroup.mk' V))),
      e ⟨QuotientGroup.mk' V g * (x : G ⧸ V) * (QuotientGroup.mk' V g)⁻¹,
          hVbar.conj_mem x x.2 (QuotientGroup.mk' V g)⟩
        = ⟨g * ((e x : ↥V) : G) * g⁻¹, (inferInstance : V.Normal).conj_mem (e x) (e x).2 g⟩ := by
  have hVn : V.Normal := inferInstance
  have hCn : C.Normal := C_normal V C hVn hC
  intro g x
  obtain ⟨y, hyL, hyx⟩ := Subgroup.mem_map.mp x.2
  have hgyC : g * y * g⁻¹ ∈ C := hCn.conj_mem y hyL.1 g
  have hgyV : (g * y * g⁻¹) * (g * y * g⁻¹) ∈ V := by
    rw [show (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ by group]
    exact hVn.conj_mem (y * y) hyL.2 g
  have hgyL : g * y * g⁻¹ ∈ level2 V C hC hCab hexp := ⟨hgyC, hgyV⟩
  have hxe : x = ⟨QuotientGroup.mk' V y, Subgroup.mem_map_of_mem (QuotientGroup.mk' V) hyL⟩ :=
    Subtype.ext hyx.symm
  have hex : e x = ⟨y * y, hyL.2⟩ := by rw [hxe, he y hyL]
  have hval : (QuotientGroup.mk' V) g * (x : G ⧸ V) * ((QuotientGroup.mk' V) g)⁻¹
      = (QuotientGroup.mk' V) (g * y * g⁻¹) := by
    rw [hxe]
    simp only [map_mul, map_inv]
  have heq : e ⟨(QuotientGroup.mk' V) g * (x : G ⧸ V) * ((QuotientGroup.mk' V) g)⁻¹,
      hVbar.conj_mem x x.2 (QuotientGroup.mk' V g)⟩
      = e ⟨QuotientGroup.mk' V (g * y * g⁻¹),
          Subgroup.mem_map_of_mem (QuotientGroup.mk' V) hgyL⟩ := by
    congr 1
    exact Subtype.ext hval
  calc e ⟨(QuotientGroup.mk' V) g * (x : G ⧸ V) * ((QuotientGroup.mk' V) g)⁻¹,
        hVbar.conj_mem x x.2 (QuotientGroup.mk' V g)⟩
      = e ⟨QuotientGroup.mk' V (g * y * g⁻¹),
          Subgroup.mem_map_of_mem (QuotientGroup.mk' V) hgyL⟩ := heq
    _ = ⟨(g * y * g⁻¹) * (g * y * g⁻¹), hgyV⟩ := he (g * y * g⁻¹) hgyL
    _ = ⟨g * ((e x : ↥V) : G) * g⁻¹, (inferInstance : V.Normal).conj_mem (e x) (e x).2 g⟩ := by
        apply Subtype.ext
        show (g * y * g⁻¹) * (g * y * g⁻¹) = g * ((e x : ↥V) : G) * g⁻¹
        rw [congrArg Subtype.val hex]
        group

/-- **`G/V` acts on `L̄ = C₂·V/V` as all of `Aut(L̄)`** in the abelian configuration of the hard
core of Hering's theorem.

Generalising an automorphism `φ` of `L̄` to `V` through the squaring isomorphism `e : L̄ ≃* V`
gives `ψ = e.symm.trans (φ.trans e) ∈ Aut(V)`; by `hAut` there is `g ∈ G` realising `ψ` by
conjugation on `V`.  The equivariance of `e` then shows that `ḡ = gV ∈ G/V` realises `φ` by
conjugation on `L̄`. -/
theorem actsAsAut_map_level2 {G : Type*} [Group G] [Finite G] (V C : Subgroup G) [V.Normal]
    (hC : C = Subgroup.centralizer ((V : Set G)))
    (hexp : ∀ x ∈ V, x * x = 1)
    (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V)
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hsq : ∀ v ∈ V, ∃ x ∈ level2 V C hC hCab hexp, x * x = v)
    (hAut : ActsAsAut V (inferInstance : V.Normal))
    (hVbar : ((level2 V C hC hCab hexp).map (QuotientGroup.mk' V)).Normal) :
    ActsAsAut ((level2 V C hC hCab hexp).map (QuotientGroup.mk' V)) hVbar := by
  classical
  obtain ⟨e, he⟩ := level2_quotient_equiv_V V C hC hexp hinv hCab hsq
  intro φ
  set ψ : MulAut ↥V := e.symm.trans (φ.trans e) with hψ
  obtain ⟨g₀, hg₀⟩ := hAut ψ
  refine ⟨QuotientGroup.mk' V g₀, fun x => ?_⟩
  have hconj : e ⟨(QuotientGroup.mk' V) g₀ * (x : G ⧸ V) * ((QuotientGroup.mk' V) g₀)⁻¹,
        hVbar.conj_mem x x.2 (QuotientGroup.mk' V g₀)⟩ = ψ (e x) := by
    rw [level2_quotient_equiv_equivariance V C hC hexp hCab hVbar e he g₀ x]
    exact (hg₀ (e x)).symm
  have hψe : ψ (e x) = e (φ x) := by
    rw [hψ]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have h4 : e.symm (ψ (e x)) = φ x := by rw [hψe, MulEquiv.symm_apply_apply]
  calc φ x = e.symm (ψ (e x)) := h4.symm
    _ = e.symm (e ⟨(QuotientGroup.mk' V) g₀ * (x : G ⧸ V) * ((QuotientGroup.mk' V) g₀)⁻¹,
          hVbar.conj_mem x x.2 (QuotientGroup.mk' V g₀)⟩) := by rw [← hconj]
    _ = ⟨(QuotientGroup.mk' V) g₀ * (x : G ⧸ V) * ((QuotientGroup.mk' V) g₀)⁻¹,
          hVbar.conj_mem x x.2 (QuotientGroup.mk' V g₀)⟩ := MulEquiv.symm_apply_apply e _

end Work.Hering.HardCore
