import Mathlib
import Submission.Work.AbsoluteGalois.Cohomology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Work.AbsoluteGalois

namespace Work.SSGRoute

/-- **Elementary algebra of the twisted product.**  Let `K ≤ G` be a subgroup whose elements
commute with one another, let `q1 q2 qr ∈ G` and `A B D ∈ K`, and put
`γ = q1 B q1⁻¹ ∈ K` and `C = q1 q2 qr⁻¹ ∈ K` (the latter because the product of two elements
that both lie in the coset `K qr` lies in `K`).  Then the statement that the `K`-twisted
"sections" multiply, namely `D⁻¹ * qr = A⁻¹ * q1 * B⁻¹ * q2`, is equivalent to the
kernel-valued cocycle condition `γ * D⁻¹ * A = C`. -/
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

/-- Group-theoretic core: for a surjection `π : Γ →* Q` with commutative kernel, a normalized section `s` of `π` and a `1`-cochain `f` whose coboundary (in the twisted, kernel-valued sense of the extension `1 → π.ker → Γ → Q → 1`) is the section `2`-cocycle, the assignment `σ ↦ (toMul (f σ))⁻¹ * s (ρ σ)` is a homomorphism lifting `ρ`. -/
theorem exists_hom_lift_of_section_coboundary {Γ Q H : Type*} [Group Γ] [Group Q] [Group H]
    (π : Γ →* Q) (hcomm : ∀ a b : π.ker, a * b = b * a)
    (s : Q → Γ) (hs : ∀ q, π (s q) = q) (h1 : s 1 = 1)
    (ρ : H →* Q) (f : H → Additive π.ker)
    (hcob : ∀ σ τ : H,
      Additive.ofMul (⟨s (ρ σ) * s (ρ τ) * (s (ρ (σ * τ)))⁻¹, by
          rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hs, hs, hs]; simp⟩ : π.ker) =
      Additive.ofMul (Work.AbsoluteGalois.conjKernelMul π (s (ρ σ)) (Additive.toMul (f τ)))
        - f (σ * τ) + f σ) :
    ∃ ψ : H →* Γ, π.comp ψ = ρ ∧ ∀ σ : H, ψ σ = (Additive.toMul (f σ))⁻¹ * s (ρ σ) := by
  -- The cocycle hypothesis, transported multiplicatively into the (abelian) kernel.
  have hkey : ∀ σ τ : H,
      conjKernelMul π (s (ρ σ)) (Additive.toMul (f τ))
        * (Additive.toMul (f (σ * τ)))⁻¹ * Additive.toMul (f σ)
      = (⟨s (ρ σ) * s (ρ τ) * (s (ρ (σ * τ)))⁻¹, by
          rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hs, hs, hs]; simp⟩ : π.ker) := by
    intro σ τ
    have h := congrArg (fun z => Additive.toMul z) (hcob σ τ)
    simp only [toMul_add, toMul_sub, toMul_ofMul] at h
    simpa only [div_eq_mul_inv] using h.symm
  -- The candidate lift `σ ↦ (toMul (f σ))⁻¹ * s (ρ σ)` is multiplicative.
  let g : H → Γ := fun σ => (Additive.toMul (f σ))⁻¹ * s (ρ σ)
  have hg : ∀ σ τ : H, g (σ * τ) = g σ * g τ := by
    intro σ τ
    have hG := (twist_algebra (π.ker) hcomm (s (ρ σ)) (s (ρ τ)) (s (ρ (σ * τ)))
      (Additive.toMul (f σ)) (Additive.toMul (f τ)) (Additive.toMul (f (σ * τ)))
      (conjKernelMul π (s (ρ σ)) (Additive.toMul (f τ))).2
      (by rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hs, hs, hs]; simp)).mpr (hkey σ τ)
    simpa only [g, Subgroup.coe_inv, ← mul_assoc] using hG
  refine ⟨MonoidHom.mk' g hg, ?_, ?_⟩
  · -- the lift projects onto `ρ`
    ext σ
    change π (g σ) = ρ σ
    simp only [g, Subgroup.coe_inv]
    rw [map_mul, map_inv, (Additive.toMul (f σ)).2, inv_one, one_mul, hs]
  · -- and it is given by the prescribed formula
    intro σ
    rfl

end Work.SSGRoute
