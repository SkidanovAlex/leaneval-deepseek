/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Linnell's Ore field of fractions statement from the division-ring property

`Work.ORFinal.OreFieldFrac K G φK` (Linnell's lemma, field (I4′b) of the Linnell datum) is proved
here from `Work.ORFinal.DivOn` alone: if the division closure `D H` of `K[H]` in `U(G)` is a
division ring for every torsion free `H`, then for `N ≤ Γ` with `Γ` torsion free and `Γ/N ≅ ℤ`,
every element of `D Γ` is a right quotient of two elements of `R = ⟨D N ∪ gen Γ⟩`.

The argument is the classical one.  Write `Γ = N ⋊ ⟨s⟩` and `R = D N[s^{±1}] ⊆ D Γ`.  The ring
`R` is the twisted Laurent polynomial ring over the division ring `D N`, hence an Ore domain
(`Work.ORFinal.OreField.ore_genSubring`), so

`Q := {a * t⁻¹ : a, t ∈ R, t ≠ 0}`

is a subring of the division ring `D Γ`, closed under inverses, and contains `R ⊇ K[Γ]`.  By
minimality of the division closure (`Work.ORBridgeLinnell.D_minimal`) we get `D Γ ≤ Q ⊆ D Γ`,
i.e. every element of `D Γ` is such a right quotient.
-/
import Mathlib
import Submission.Work.ORFinal.AnalyticInput
import Submission.Work.ORLinnell.Main
import Submission.Work.ORBridgeLinnell.Countable
import Submission.Work.ORFinal.OreField.OreFieldDefs
import Submission.Work.ORFinal.OreField.OreFieldDefs2

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORFinal.OreField

open Work.ORVonNeumann Work.ORBridgeLinnell

universe u v

theorem oreFieldFrac_of_div (K : Type*) [Field K] (G : Type*) [Group G] [Countable G]
    (φK : K →+* ℂ)
    (hdiv : ∀ H : Subgroup G, IsMulTorsionFree H →
      Work.ORFinal.DivOn K (Work.ORBridgeLinnell.countableEnvelope G) φK H) :
    Work.ORFinal.OreFieldFrac K G φK := by
  letI := kAlgebra (countableEnvelope G) φK
  intro N Γ hN htf hφ
  have hNn : (N.subgroupOf Γ).Normal := by
    obtain ⟨φ, -, hker⟩ := hφ
    rw [← hker]
    exact MonoidHom.normal_ker φ
  have htfN : IsMulTorsionFree ↥N := ⟨fun n hn a b hab =>
    Subtype.ext (congrArg (fun x : ↥Γ => (x : G)) (htf.pow_left_injective hn (by
      have h : (Subgroup.inclusion hN a) ^ n = (Subgroup.inclusion hN b) ^ n := by
        simpa only [map_pow] using congrArg (fun x : ↥N => Subgroup.inclusion hN x) hab
      exact h)))⟩
  letI : DivisionRing ↥(D (countableEnvelope G) φK Γ) :=
    DivisionRing.ofIsUnitOrEqZero (fun x => by
      rcases eq_or_ne x 0 with h | h
      · exact Or.inr h
      · exact Or.inl (hdiv Γ htf x h))
  obtain ⟨s, hs⟩ := hφ.exists_generator
  have hore := ore_genSubring (countableEnvelope G) φK (kAlgebra_compat (countableEnvelope G) φK)
    hN hNn (hdiv N htfN) hφ s hs
  -- `R = ⟨D N ∪ gen Γ⟩ ⊆ U(G)`, viewed as a subring of the division ring `D Γ`
  have hR_le_DΓ : genSubring (countableEnvelope G) φK N Γ ≤ D (countableEnvelope G) φK Γ := by
    rw [genSubring, Subring.closure_le]
    rintro x (hx | hx)
    · exact D_mono (countableEnvelope G) φK hN hx
    · obtain ⟨γ, rfl⟩ := hx
      exact gen_mem_D (countableEnvelope G) φK Γ γ
  let RΓ : Subring ↥(D (countableEnvelope G) φK Γ) :=
    (genSubring (countableEnvelope G) φK N Γ).comap
      (Subring.subtype (D (countableEnvelope G) φK Γ))
  have hR_mem : ∀ x : ↥(D (countableEnvelope G) φK Γ),
      x ∈ RΓ ↔ (x : (countableEnvelope G).U) ∈ genSubring (countableEnvelope G) φK N Γ :=
    fun x => Iff.rfl
  -- the Ore condition, transported to `RΓ`
  have horeΓ : ∀ x ∈ RΓ, x ≠ 0 → ∀ y ∈ RΓ, y ≠ 0 →
      ∃ c ∈ RΓ, c ≠ 0 ∧ ∃ d ∈ RΓ, d ≠ 0 ∧ x * c = y * d := by
    intro x hx hx0 y hy hy0
    have hx' := (hR_mem x).mp hx
    have hy' := (hR_mem y).mp hy
    have hx0' : (x : (countableEnvelope G).U) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hy0' : (y : (countableEnvelope G).U) ≠ 0 := fun h => hy0 (Subtype.ext h)
    obtain ⟨c, hc, hc0, d, hd, hd0, hcd⟩ := hore _ hx' hx0' _ hy' hy0'
    refine ⟨⟨c, hR_le_DΓ hc⟩, (hR_mem _).mpr hc, ?_, ⟨d, hR_le_DΓ hd⟩, (hR_mem _).mpr hd,
      ?_, ?_⟩
    · intro h
      exact hc0 (congrArg Subtype.val h)
    · intro h
      exact hd0 (congrArg Subtype.val h)
    · apply Subtype.ext
      simpa using hcd
  -- the quotient set `{a * b⁻¹} ⊆ D Γ`
  let S : Set ↥(D (countableEnvelope G) φK Γ) :=
    {x | ∃ a ∈ RΓ, ∃ b ∈ RΓ, b ≠ 0 ∧ x = a * b⁻¹}
  have hS : ∀ x : ↥(D (countableEnvelope G) φK Γ),
      x ∈ S ↔ ∃ a ∈ RΓ, ∃ b ∈ RΓ, b ≠ 0 ∧ x = a * b⁻¹ := fun x => Iff.rfl
  have hS0 : (0 : ↥(D (countableEnvelope G) φK Γ)) ∈ S :=
    ⟨0, RΓ.zero_mem, 1, RΓ.one_mem, one_ne_zero, by rw [zero_mul]⟩
  have hS1 : (1 : ↥(D (countableEnvelope G) φK Γ)) ∈ S :=
    ⟨1, RΓ.one_mem, 1, RΓ.one_mem, one_ne_zero, by rw [inv_one, mul_one]⟩
  have hSneg : ∀ {x}, x ∈ S → -x ∈ S := by
    rintro x ⟨a, ha, b, hb, hb0, rfl⟩
    exact ⟨-a, RΓ.neg_mem ha, b, hb, hb0, by rw [neg_mul]⟩
  have hSadd : ∀ {x y}, x ∈ S → y ∈ S → x + y ∈ S := by
    intro x y hx hy
    obtain ⟨a, ha, b, hb, hb0, rfl⟩ := hx
    obtain ⟨c, hc, d, hd, hd0, rfl⟩ := hy
    obtain ⟨c₀, hc₀, hc₀0, d₀, hd₀, hd₀0, hcd⟩ := horeΓ d hd hd0 b hb hb0
    have hT : d * c₀ ≠ 0 := mul_ne_zero hd0 hc₀0
    have key : (a * b⁻¹ + c * d⁻¹) * (d * c₀) = a * d₀ + c * c₀ := by
      rw [add_mul, mul_assoc a b⁻¹ (d * c₀), mul_assoc c d⁻¹ (d * c₀)]
      rw [show b⁻¹ * (d * c₀) = d₀ from by
            rw [hcd, ← mul_assoc, inv_mul_cancel₀ hb0, one_mul],
        show d⁻¹ * (d * c₀) = c₀ from by rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul]]
    exact ⟨a * d₀ + c * c₀, RΓ.add_mem (RΓ.mul_mem ha hd₀) (RΓ.mul_mem hc hc₀),
      d * c₀, RΓ.mul_mem hd hc₀, hT, by rw [← key, mul_assoc, mul_inv_cancel₀ hT, mul_one]⟩
  have hSmul : ∀ {x y}, x ∈ S → y ∈ S → x * y ∈ S := by
    intro x y hx hy
    obtain ⟨a, ha, b, hb, hb0, rfl⟩ := hx
    obtain ⟨c, hc, d, hd, hd0, rfl⟩ := hy
    by_cases hc0 : c = 0
    · subst hc0
      exact ⟨0, RΓ.zero_mem, 1, RΓ.one_mem, one_ne_zero, by simp⟩
    · obtain ⟨u, hu, hu0, v, hv, hv0, huv⟩ := horeΓ c hc hc0 b hb hb0
      have hT : d * u ≠ 0 := mul_ne_zero hd0 hu0
      have key : b⁻¹ * c = v * u⁻¹ := by
        have hu_eq : c * u * u⁻¹ = c := by rw [mul_assoc, mul_inv_cancel₀ hu0, mul_one]
        rw [← hu_eq, ← mul_assoc, huv, ← mul_assoc, inv_mul_cancel₀ hb0, one_mul]
      refine ⟨a * v, RΓ.mul_mem ha hv, d * u, RΓ.mul_mem hd hu, hT, ?_⟩
      rw [show a * b⁻¹ * (c * d⁻¹) = a * (b⁻¹ * c) * d⁻¹ from by noncomm_ring, key]
      rw [show a * (v * u⁻¹) * d⁻¹ = (a * v) * (d * u)⁻¹ from by
        rw [mul_inv_rev]; noncomm_ring]
  have hSinv : ∀ x ∈ S, x ≠ 0 → x⁻¹ ∈ S := by
    rintro x ⟨a, ha, b, hb, hb0, rfl⟩ hx0
    have hane : a ≠ 0 := by
      intro h0
      refine hx0 ?_
      rw [h0, zero_mul]
    exact ⟨b, hb, a, ha, hane, by rw [mul_inv_rev, inv_inv]⟩
  let QΓ : Subring ↥(D (countableEnvelope G) φK Γ) :=
    { carrier := S
      zero_mem' := hS0
      one_mem' := hS1
      add_mem' := hSadd
      neg_mem' := hSneg
      mul_mem' := hSmul }
  have hQΓ_mem : ∀ x : ↥(D (countableEnvelope G) φK Γ),
      x ∈ QΓ ↔ ∃ a ∈ RΓ, ∃ b ∈ RΓ, b ≠ 0 ∧ x = a * b⁻¹ := by
    intro x
    show x ∈ S ↔ _
    exact hS x
  let Q : Subring (countableEnvelope G).U :=
    QΓ.map (Subring.subtype (D (countableEnvelope G) φK Γ))
  have hgenSub_le_Q : ∀ r ∈ genSubring (countableEnvelope G) φK N Γ,
      r ∈ (Q : Set (countableEnvelope G).U) := by
    intro r hr
    refine Subring.mem_map.mpr ⟨⟨r, hR_le_DΓ hr⟩, ?_, rfl⟩
    exact (hQΓ_mem _).mpr ⟨⟨r, hR_le_DΓ hr⟩, (hR_mem _).mpr hr, 1, RΓ.one_mem,
      one_ne_zero, by rw [inv_one, mul_one]⟩
  have hQcle : IsDivisionClosed Q := by
    intro x hx y hxy
    obtain ⟨x₀, hx₀, hx₀eq⟩ := Subring.mem_map.mp hx
    by_cases hx0 : x₀ = 0
    · exfalso
      have h1 : (x₀ : (countableEnvelope G).U) * y = 1 := by
        rw [show (x₀ : (countableEnvelope G).U) = x from hx₀eq]; exact hxy
      have h0 : (x₀ : (countableEnvelope G).U) = 0 := by rw [hx0]; rfl
      rw [h0, zero_mul] at h1
      exact one_ne_zero h1.symm
    · have h1 : (x₀ : (countableEnvelope G).U) * y = 1 := by
        rw [show (x₀ : (countableEnvelope G).U) = x from hx₀eq]; exact hxy
      refine Subring.mem_map.mpr ⟨x₀⁻¹, (hQΓ_mem _).mpr ?_, ?_⟩
      · obtain ⟨a, ha, b, hb, hb0, rfl⟩ := (hQΓ_mem x₀).mp hx₀
        refine ⟨b, hb, a, ha, ?_, by rw [mul_inv_rev, inv_inv]⟩
        intro h0
        exact hx0 (by rw [h0, zero_mul])
      · show ((x₀⁻¹ : ↥(D (countableEnvelope G) φK Γ)) : (countableEnvelope G).U) = y
        calc ((x₀⁻¹ : ↥(D (countableEnvelope G) φK Γ)) : (countableEnvelope G).U)
            = ((x₀⁻¹ : ↥(D (countableEnvelope G) φK Γ)) : (countableEnvelope G).U) * 1 :=
              (mul_one _).symm
          _ = ((x₀⁻¹ : ↥(D (countableEnvelope G) φK Γ)) : (countableEnvelope G).U)
                * ((x₀ : (countableEnvelope G).U) * y) := by rw [h1]
          _ = (((x₀⁻¹ : ↥(D (countableEnvelope G) φK Γ)) : (countableEnvelope G).U)
                * (x₀ : (countableEnvelope G).U)) * y := by rw [mul_assoc]
          _ = (((x₀⁻¹ * x₀ : ↥(D (countableEnvelope G) φK Γ)) : (countableEnvelope G).U)) * y := by
                rw [Subring.coe_mul]
          _ = 1 * y := by rw [inv_mul_cancel₀ hx0, Subring.coe_one]
          _ = y := by rw [one_mul]
  have hrange : Set.range (toUK (countableEnvelope G) φK Γ) ⊆ (Q : Set (countableEnvelope G).U) := by
    refine toUK_mem_of_mem (countableEnvelope G) φK (A := Q) ?_ ?_
    · intro γ
      exact hgenSub_le_Q _ (Subring.subset_closure (Set.mem_union_right _ ⟨γ, rfl⟩))
    · intro k
      exact hgenSub_le_Q _ (Subring.subset_closure (Set.mem_union_left _
        (algebraMap_mem_D (countableEnvelope G) φK N k)))
  have hD_le_Q : D (countableEnvelope G) φK Γ ≤ Q :=
    D_minimal (countableEnvelope G) φK hrange hQcle
  intro e he
  obtain ⟨x₀, hx₀, hx₀eq⟩ := Subring.mem_map.mp (hD_le_Q he)
  obtain ⟨a, ha, b, hb, hb0, hab⟩ := (hQΓ_mem x₀).mp hx₀
  refine ⟨(a : (countableEnvelope G).U), (hR_mem a).mp ha,
    (b : (countableEnvelope G).U), (hR_mem b).mp hb, fun h => hb0 (Subtype.ext h), ?_⟩
  rw [show e = (x₀ : (countableEnvelope G).U) from hx₀eq.symm, hab, Subring.coe_mul, mul_assoc,
    ← Subring.coe_mul, inv_mul_cancel₀ hb0, Subring.coe_one, mul_one]

end Work.ORFinal.OreField
