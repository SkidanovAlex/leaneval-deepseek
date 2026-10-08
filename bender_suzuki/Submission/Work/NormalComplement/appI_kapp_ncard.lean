import Mathlib
import Submission.Work.NormalComplement.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

theorem appI_kapp_ncard {G : Type*} [Group G] [Finite G] (t : G) (X : Subgroup G) :
    (Work.NormalComplement.Kapp t X).ncard =
      ((Subgroup.centralizer ({t} : Set G) ⊓ X).subgroupOf X).index := by
  classical
  -- `K` is the centraliser of `t` inside `X`, viewed as a subgroup of `X`.
  let C : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let K : Subgroup X := (C ⊓ X).subgroupOf X
  -- Members of `K` are exactly the elements of `X` commuting with `t`.
  have hCE : ∀ x : G, x ∈ C ↔ x * t = t * x := fun x =>
    Subgroup.mem_centralizer_singleton_iff
  have hK : ∀ a : X, a ∈ K ↔ (a : G) * t = t * (a : G) := by
    intro a
    have h1 : a ∈ K ↔ (a : G) ∈ C := by
      show a ∈ (C ⊓ X).subgroupOf X ↔ _
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, a.2⟩⟩
    exact h1.trans (hCE (a : G))
  -- The map `a ↦ t⁻¹ * a * t * a⁻¹` has image exactly `Kapp t X`.
  let g : X → ↥(Work.NormalComplement.Kapp t X) := fun a =>
    ⟨t⁻¹ * (a : G) * t * (a : G)⁻¹, by
      refine ⟨(a⁻¹ : G), (a⁻¹ : X).2, ?_⟩
      simp⟩
  -- `g` is constant on left cosets of `K`.
  have hconst : ∀ a b : X, QuotientGroup.leftRel K a b → g a = g b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have hcomm : (a : G)⁻¹ * (b : G) * t = t * ((a : G)⁻¹ * (b : G)) := by
      have := (hK (a⁻¹ * b)).mp hab
      simpa using this
    apply Subtype.ext
    have hkey : (b : G) * t * (b : G)⁻¹ = (a : G) * t * (a : G)⁻¹ := by
      calc (b : G) * t * (b : G)⁻¹
          = (a : G) * ((a : G)⁻¹ * (b : G)) * t * (b : G)⁻¹ := by group
        _ = (a : G) * (((a : G)⁻¹ * (b : G)) * t) * (b : G)⁻¹ := by group
        _ = (a : G) * (t * ((a : G)⁻¹ * (b : G))) * (b : G)⁻¹ := by rw [hcomm]
        _ = (a : G) * t * (a : G)⁻¹ := by group
    calc t⁻¹ * (a : G) * t * (a : G)⁻¹
        = t⁻¹ * ((a : G) * t * (a : G)⁻¹) := by group
      _ = t⁻¹ * ((b : G) * t * (b : G)⁻¹) := by rw [← hkey]
      _ = t⁻¹ * (b : G) * t * (b : G)⁻¹ := by group
  -- Induced map on the left-coset quotient.
  let Φ : X ⧸ K → ↥(Work.NormalComplement.Kapp t X) := Quotient.lift g hconst
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨x, hx, hzx⟩ := z.2
    refine ⟨Quotient.mk'' ((⟨x, hx⟩ : X)⁻¹), ?_⟩
    apply Subtype.ext
    show t⁻¹ * (↑((⟨x, hx⟩ : X)⁻¹) : G) * t * (↑((⟨x, hx⟩ : X)⁻¹) : G)⁻¹ = z.1
    rw [hzx]
    simp
  have hinj : Function.Injective Φ := by
    intro p q hpq
    induction p using Quotient.inductionOn' with
    | h a =>
      induction q using Quotient.inductionOn' with
      | h b =>
        rw [Quotient.eq'', QuotientGroup.leftRel_apply]
        apply (hK (a⁻¹ * b)).mpr
        have hg : g a = g b := by
          have h : Quotient.lift g hconst (Quotient.mk'' a) =
              Quotient.lift g hconst (Quotient.mk'' b) := hpq
          rwa [Quotient.lift_mk, Quotient.lift_mk] at h
        have hval : t⁻¹ * (a : G) * t * (a : G)⁻¹ =
            t⁻¹ * (b : G) * t * (b : G)⁻¹ := by
          have := congrArg Subtype.val hg
          simpa using this
        have hAB : (a : G) * t * (a : G)⁻¹ = (b : G) * t * (b : G)⁻¹ := by
          apply mul_left_cancel (a := t⁻¹)
          calc t⁻¹ * ((a : G) * t * (a : G)⁻¹) = t⁻¹ * (a : G) * t * (a : G)⁻¹ := by
                group
            _ = t⁻¹ * (b : G) * t * (b : G)⁻¹ := hval
            _ = t⁻¹ * ((b : G) * t * (b : G)⁻¹) := by group
        have hconj : ((a : G)⁻¹ * (b : G)) * t * ((a : G)⁻¹ * (b : G))⁻¹ = t := by
          calc ((a : G)⁻¹ * (b : G)) * t * ((a : G)⁻¹ * (b : G))⁻¹
              = (a : G)⁻¹ * ((b : G) * t * (b : G)⁻¹) * (a : G) := by group
            _ = (a : G)⁻¹ * ((a : G) * t * (a : G)⁻¹) * (a : G) := by rw [← hAB]
            _ = t := by group
        have hcomm : ((a : G)⁻¹ * (b : G)) * t = t * ((a : G)⁻¹ * (b : G)) := by
          calc ((a : G)⁻¹ * (b : G)) * t
              = ((a : G)⁻¹ * (b : G)) * t * ((a : G)⁻¹ * (b : G))⁻¹ *
                  ((a : G)⁻¹ * (b : G)) := by group
            _ = t * ((a : G)⁻¹ * (b : G)) := by rw [hconj]
        simpa using hcomm
  have hbij : Function.Bijective Φ := ⟨hinj, hsurj⟩
  rw [Subgroup.index_eq_card]
  rw [← Nat.card_coe_set_eq (Work.NormalComplement.Kapp t X)]
  exact (Nat.card_congr (Equiv.ofBijective Φ hbij)).symm

end Work.NormalComplement
