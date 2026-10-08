import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.Omega1
import Submission.Work.PGroup.inf_centralizer_ne_bot_of_isPGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.LocalPrelim

open Subgroup

/-- **FT 8.3 (fixed form).**

Let `X` be a finite `p`-group, let `A₀ ≤ D` be normal subgroups of `X` with `D ≠ A₀`, and
suppose every element of `D` has `p`-th power `1`.  Then there is an element `c ∈ D \ A₀`
which is central modulo `A₀`, i.e. `c x c⁻¹ x⁻¹ ∈ A₀` for every `x ∈ X`.

Equivalently: `Z(X/A₀) ∩ (D A₀/A₀) ≠ 1`.  Indeed `X/A₀` is a finite `p`-group and
`D A₀/A₀` is a nontrivial normal subgroup of it, so it meets the center nontrivially
(`Work.PGroup.inf_omega1_center_ne_bot`). -/
theorem ft8_3_fixed {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hX : IsPGroup p X) {A0 D : Subgroup X} [hA0n : A0.Normal] [hDn : D.Normal] (hle : A0 ≤ D)
    (hne : D ≠ A0) (hexp : ∀ d ∈ D, d ^ p = 1) :
    ∃ c ∈ D, c ∉ A0 ∧ ∀ x : X, c * x * c⁻¹ * x⁻¹ ∈ A0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- The quotient map to `X ⧸ A0`.
  let q : X →* (X ⧸ A0) := QuotientGroup.mk' A0
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective A0
  have hqker : q.ker = A0 := QuotientGroup.ker_mk' A0
  haveI : Finite (X ⧸ A0) := inferInstance
  have hMp : IsPGroup p (X ⧸ A0) := hX.of_surjective q hqsurj
  -- The image of `D` in `X ⧸ A0` is a nontrivial normal subgroup.
  let N : Subgroup (X ⧸ A0) := D.map q
  have hNnorm : N.Normal := hDn.map q hqsurj
  have hNne : N ≠ ⊥ := by
    intro hbot
    apply hne
    refine le_antisymm ?_ hle
    intro d hd
    have hmem : q d ∈ N := Subgroup.mem_map.mpr ⟨d, hd, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hker : d ∈ q.ker := MonoidHom.mem_ker.mpr hmem
    rwa [hqker] at hker
  -- A nontrivial element of `N` that is central in `X ⧸ A0`.
  obtain ⟨z, hz_ne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp
      (Work.PGroup.inf_omega1_center_ne_bot hp hMp hNnorm hNne)
  obtain ⟨hzN, hzom⟩ := Subgroup.mem_inf.mp z.2
  have hzcent : (z : X ⧸ A0) ∈ Subgroup.center (X ⧸ A0) :=
    Work.PGroup.omega1_le p (Subgroup.center (X ⧸ A0)) hzom
  have hzval_ne : (z : X ⧸ A0) ≠ 1 := fun h => hz_ne (Subtype.ext h)
  -- Lift it to an element `c ∈ D`.
  obtain ⟨c, hcD, hcq⟩ := Subgroup.mem_map.mp hzN
  refine ⟨c, hcD, ?_, ?_⟩
  · -- `c ∉ A0`, since its image is `z ≠ 1`.
    intro hcA0
    have hqc1 : q c = 1 := by
      have hker : c ∈ q.ker := by rw [hqker]; exact hcA0
      exact MonoidHom.mem_ker.mp hker
    exact hzval_ne (hcq ▸ hqc1)
  · -- `c` is central modulo `A0`.
    intro x
    have hcomm : q x * (z : X ⧸ A0) = (z : X ⧸ A0) * q x :=
      Subgroup.mem_center_iff.mp hzcent (q x)
    have hkey : q (c * x * c⁻¹ * x⁻¹) = 1 := by
      simp only [map_mul, map_inv, hcq]
      rw [← hcomm]
      group
    have hker : c * x * c⁻¹ * x⁻¹ ∈ q.ker := MonoidHom.mem_ker.mpr hkey
    rwa [hqker] at hker

end Work.LocalPrelim
