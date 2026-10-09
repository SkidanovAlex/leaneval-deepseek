/-
Copyright (c) 2025. All rights reserved.

# Lifts along a surjection with abelian kernel and the vanishing of the pulled back class

Let `π : G →* Q` be a surjection (`hs : ∀ q, π (s q) = q` for a set-theoretic section `s`) with
**abelian** kernel `A = ker π`.  Conjugation by a section defines a `Q`-module structure on `A`
(`kernelAction`), and the section produces the `2`-cocycle
`s (q) * s (r) * (s (q * r))⁻¹` (`sectionCocycle`), whose class in `H²(Q, A)` is the extension
class of `π`.

For a homomorphism `ρ : H →* Q`, this file proves that `π` *lifts* `ρ` — i.e. there is a
homomorphism `ψ : H →* G` with `π ∘ ψ = ρ` — if and only if the pullback of the section cocycle
along `ρ` is a **coboundary**:

`(∃ ψ : H →* G, π.comp ψ = ρ) ↔ pullbackCocycle ρ (sectionCocycle π s hs) ∈ B²(H, A)`.

The two directions are the two halves of the same explicit computation.  Writing
`Ψ(f)(h) = (toMul (f h))⁻¹ * s (ρ h)` for a cochain `f : H → A`,

`Ψ(f) (h * h') = Ψ(f) h * Ψ(f) h'  ⟺  d¹ f = pullbackCocycle ρ (sectionCocycle π s hs)`

(the twisted product of two lifts is again a lift precisely when the pullback of the class is a
coboundary), and every lift `ψ` of `ρ` is of the form `Ψ(f)`.  The elementary algebra underlying
this equivalence is isolated in the auxiliary lemma `twist_algebra` below: for `q₁, q₂, q_r ∈ G`
and `A, B, D ∈ ker π` with `γ = q₁ B q₁⁻¹` and `C = q₁ q₂ qᵣ⁻¹` (both in `ker π`),

`D⁻¹ * q_r = A⁻¹ * q₁ * B⁻¹ * q₂  ⟺  γ * D⁻¹ * A = C`,

which uses the commutativity of `ker π` to reorder the elements of the kernel.

## Main declarations

* `Work.AbsoluteGalois.exists_hom_lift_iff_pullbackCocycle_mem_B2`
-/
import Mathlib
import Submission.Work.AbsoluteGalois.Cohomology
import Submission.Work.AbsoluteGalois.Obstruction
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteGalois

open Work.GroupCohomology

set_option linter.style.haveILetI false

/-- **Elementary algebra of the twisted product.**  Let `K ≤ G` be a subgroup whose elements
commute with one another, let `q₁ q₂ q_r ∈ G` and `A B D ∈ K`, and put
`γ = q₁ B q₁⁻¹ ∈ K` and `C = q₁ q₂ q_r⁻¹ ∈ K` (the latter because the product of two elements
that both lie in the coset `K q_r` lies in `K`).  Then the statement that `q ↦ K`-twisted
"sections" multiply, namely
`D⁻¹ * q_r = A⁻¹ * q₁ * B⁻¹ * q₂`, is equivalent to the (kernel valued) cocycle condition
`γ * D⁻¹ * A = C`.

Here `D` plays the role of the value of the cochain at `h * h'`, `A`, `B` those at `h`, `h'`,
`q₁ = s (ρ h)`, `q₂ = s (ρ h')`, `q_r = s (ρ (h * h'))` and `C` the value of the pullback of the
section cocycle. -/
private theorem twist_algebra {G : Type*} [Group G] (K : Subgroup G)
    (hcomm : ∀ a b : K, a * b = b * a) (q1 q2 qr : G) (A B D : K)
    (hγ : q1 * (B : G) * q1⁻¹ ∈ K) (hC : q1 * q2 * qr⁻¹ ∈ K) :
    ((D : G)⁻¹ * qr = (A : G)⁻¹ * q1 * (B : G)⁻¹ * q2) ↔
      (⟨q1 * (B : G) * q1⁻¹, hγ⟩ : K) * D⁻¹ * A = ⟨q1 * q2 * qr⁻¹, hC⟩ := by
  letI : CommGroup K := { (inferInstance : Group K) with mul_comm := hcomm }
  set γ : K := ⟨q1 * (B : G) * q1⁻¹, hγ⟩
  set C : K := ⟨q1 * q2 * qr⁻¹, hC⟩
  have hcoeγ : (γ : G) = q1 * (B : G) * q1⁻¹ := rfl
  have hcoeC : (C : G) = q1 * q2 * qr⁻¹ := rfl
  have hγi : (γ : G)⁻¹ = q1 * (B : G)⁻¹ * q1⁻¹ := by rw [hcoeγ]; group
  have hqq : q1 * q2 = (C : G) * qr := by rw [hcoeC]; group
  constructor
  · intro hhom
    have hD : (D⁻¹ : K) = A⁻¹ * γ⁻¹ * C := by
      apply Subtype.coe_injective
      have hG : (D : G)⁻¹ = (A : G)⁻¹ * (γ : G)⁻¹ * (C : G) := by
        calc (D : G)⁻¹ = (D : G)⁻¹ * qr * qr⁻¹ := by group
          _ = ((A : G)⁻¹ * q1 * (B : G)⁻¹ * q2) * qr⁻¹ := by rw [hhom]
          _ = (A : G)⁻¹ * (γ : G)⁻¹ * (C : G) := by rw [hγi, hcoeC]; group
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hG
    rw [hD]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · intro hd1
    have hD : (D⁻¹ : K) = A⁻¹ * γ⁻¹ * C := by
      apply Additive.ofMul.injective
      rw [← hd1]
      simp only [ofMul_mul, ofMul_inv]
      abel
    calc (D : G)⁻¹ * qr
        = ((D⁻¹ : K) : G) * qr := by rw [Subgroup.coe_inv]
      _ = ((A⁻¹ * γ⁻¹ * C : K) : G) * qr := by rw [hD]
      _ = (A : G)⁻¹ * ((γ : G)⁻¹ * (C : G)) * qr := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      _ = (A : G)⁻¹ * ((γ : G)⁻¹ * q1) * q2 := by
            rw [mul_assoc (A:G)⁻¹ ((γ:G)⁻¹ * (C:G)) qr, mul_assoc (γ:G)⁻¹ (C:G) qr, ← hqq,
              hγi]; group
      _ = (A : G)⁻¹ * q1 * (B : G)⁻¹ * q2 := by
            rw [hγi]; group

/-- **A homomorphism `ρ : H →* Q` lifts along `π` if and only if the pullback of the section
cocycle is a coboundary.**  Here `A = ker π` is abelian (`hcomm`), so that `H` acts on `A`
through `ρ` by the conjugation action of `Q`. -/
theorem exists_hom_lift_iff_pullbackCocycle_mem_B2 {G Q H : Type*} [Group G] [Group Q] [Group H]
    (π : G →* Q) (s : Q → G) (hs : ∀ q, π (s q) = q) (h1 : s 1 = 1)
    (hcomm : ∀ a b : π.ker, a * b = b * a) (ρ : H →* Q) :
    letI : CommGroup π.ker := { (inferInstance : Group π.ker) with mul_comm := hcomm }
    letI := Work.AbsoluteGalois.kernelAction π s hs h1 hcomm
    letI := DistribMulAction.compHom (Additive π.ker) ρ
    ((∃ ψ : H →* G, π.comp ψ = ρ) ↔
      Work.AbsoluteGalois.pullbackCocycle ρ (Work.AbsoluteGalois.sectionCocycle π s hs)
        ∈ Work.GroupCohomology.B2 H (Additive π.ker)) := by
  letI : CommGroup π.ker := { (inferInstance : Group π.ker) with mul_comm := hcomm }
  letI : DistribMulAction Q (Additive π.ker) := Work.AbsoluteGalois.kernelAction π s hs h1 hcomm
  letI : DistribMulAction H (Additive π.ker) := DistribMulAction.compHom (Additive π.ker) ρ
  constructor
  · -- A lift of `ρ` produces an explicit `1`-cochain whose coboundary is the pulled back cocycle.
    rintro ⟨ψ, hψ⟩
    rw [Work.GroupCohomology.mem_B2_iff]
    have hψh : ∀ h : H, π (ψ h) = ρ h := fun h => MonoidHom.ext_iff.mp hψ h
    let F : H → Additive π.ker := fun h => Additive.ofMul ⟨s (ρ h) * (ψ h)⁻¹, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψh h, hs, mul_inv_cancel]⟩
    refine ⟨F, ?_⟩
    funext p
    obtain ⟨h, h'⟩ := p
    -- The multiplication rule for the twisted sections, i.e. multiplicativity of `ψ`.
    have hG : (↑(Additive.toMul (F (h * h'))) : G)⁻¹ * s (ρ h * ρ h')
        = (↑(Additive.toMul (F h)) : G)⁻¹ * s (ρ h)
          * (↑(Additive.toMul (F h')))⁻¹ * s (ρ h') := by
      rw [← map_mul ρ h h']
      dsimp only [F]
      simp only [toMul_ofMul, Subgroup.coe_mk]
      rw [map_mul ψ h h']
      group
    have hK := (twist_algebra (π.ker) hcomm (s (ρ h)) (s (ρ h')) (s (ρ h * ρ h'))
      (Additive.toMul (F h)) (Additive.toMul (F h')) (Additive.toMul (F (h * h')))
      (conjKernelMul π (s (ρ h)) (Additive.toMul (F h'))).2
      (Additive.toMul (sectionCocycle π s hs (ρ h, ρ h'))).2).mp hG
    apply Additive.toMul.injective
    rw [show Additive.toMul (GroupCohomology.d1 H (Additive π.ker) F (h, h'))
          = Work.AbsoluteGalois.conjKernelMul π (s (ρ h)) (Additive.toMul (F h'))
            * (Additive.toMul (F (h * h')))⁻¹ * Additive.toMul (F h) from by
        simp only [GroupCohomology.d1_apply, toMul_add, toMul_sub, div_eq_mul_inv,
          MulAction.compHom_smul_def]
        rfl]
    rw [Work.AbsoluteGalois.pullbackCocycle_apply]
    exact hK
  · -- A coboundary `f` with `d¹ f = c` produces the lift `h ↦ (toMul (f h))⁻¹ * s (ρ h)`.
    intro hB2
    rw [Work.GroupCohomology.mem_B2_iff] at hB2
    obtain ⟨f, hf⟩ := hB2
    refine ⟨MonoidHom.mk' (fun h => (↑(Additive.toMul (f h)))⁻¹ * s (ρ h)) ?_, ?_⟩
    · intro h h'
      have hkey : Additive.toMul (ρ h • f h') * (Additive.toMul (f (h * h')))⁻¹
            * Additive.toMul (f h)
          = Additive.toMul (sectionCocycle π s hs (ρ h, ρ h')) := by
        have h1' := congrArg Additive.toMul (congrFun hf (h, h'))
        simpa only [GroupCohomology.d1_apply, Work.AbsoluteGalois.pullbackCocycle_apply,
          toMul_add, toMul_sub, div_eq_mul_inv, MulAction.compHom_smul_def] using h1'
      have hG := (twist_algebra (π.ker) hcomm (s (ρ h)) (s (ρ h')) (s (ρ h * ρ h'))
        (Additive.toMul (f h)) (Additive.toMul (f h')) (Additive.toMul (f (h * h')))
        (conjKernelMul π (s (ρ h)) (Additive.toMul (f h'))).2
        (Additive.toMul (sectionCocycle π s hs (ρ h, ρ h'))).2).mpr
        (show Work.AbsoluteGalois.conjKernelMul π (s (ρ h)) (Additive.toMul (f h'))
              * (Additive.toMul (f (h * h')))⁻¹ * Additive.toMul (f h)
            = Additive.toMul (Work.AbsoluteGalois.sectionCocycle π s hs (ρ h, ρ h'))
          from hkey)
      rw [map_mul ρ h h']
      simpa only [← mul_assoc] using hG
    · ext h
      show π ((↑(Additive.toMul (f h)))⁻¹ * s (ρ h)) = ρ h
      rw [map_mul, map_inv, (Additive.toMul (f h)).2, inv_one, one_mul, hs]

end Work.AbsoluteGalois
