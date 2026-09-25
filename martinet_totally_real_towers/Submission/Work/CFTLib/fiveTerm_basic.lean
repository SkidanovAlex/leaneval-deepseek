import Mathlib
import Submission.Work.CFTLib.fiveTerm_setup

/-!
# The five-term inflation–restriction sequence: first structural lemmas

* the space `Hom(G,𝔽_p)` of additive characters is finite dimensional for finite `G`, and so is
  the space `invCharSubmodule p N` of `G'`-invariant characters of a normal subgroup;
* the inflation map `alpha` on characters is injective;
* its range is the kernel of the restriction map `beta`.
-/

namespace Work.CFTLib

open CategoryTheory Representation groupCohomology
open scoped Classical

noncomputable section

section Finite

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G]

/-- The additive characters `G → 𝔽_p` are finite dimensional over `𝔽_p` for a finite group `G`:
they form a subspace of the finite-dimensional space of all functions `G → 𝔽_p`. -/
lemma finiteDimensional_addHom [Fintype G] :
    FiniteDimensional (ZMod p) (Additive G →+ ZMod p) := by
  have hinj : Function.Injective
      (fun f : (Additive G →+ ZMod p) => (f : Additive G → ZMod p)) :=
    fun f g hfg => AddMonoidHom.ext (fun x => congr_fun hfg x)
  let φ : (Additive G →+ ZMod p) →ₗ[ZMod p] (Additive G → ZMod p) :=
    { toFun := fun f => f
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
  exact FiniteDimensional.of_injective φ hinj

end Finite

section InvChar

variable {p : ℕ} [Fact p.Prime] {G' : Type} [Group G'] (N : Subgroup G') [N.Normal]

/-- The space of `G'`-invariant characters of a normal subgroup is finite dimensional whenever
the character space of the subgroup is. -/
lemma finiteDimensional_invCharSubmodule [Fintype N] :
    FiniteDimensional (ZMod p) (invCharSubmodule p N) := by
  haveI : FiniteDimensional (ZMod p) (Additive ↥N →+ ZMod p) :=
    finiteDimensional_addHom (p := p) (G := ↥N)
  haveI : FiniteDimensional (ZMod p) (⊤ : Submodule (ZMod p) (Additive ↥N →+ ZMod p)) :=
    LinearEquiv.finiteDimensional
      (Submodule.topEquiv (R := ZMod p) (M := Additive ↥N →+ ZMod p)).symm
  exact Submodule.finiteDimensional_of_le (le_top : invCharSubmodule p N ≤ ⊤)

end InvChar

section AlphaBeta

variable {p : ℕ} [Fact p.Prime] {G G' : Type} [Group G] [Group G']

/-- **The inflation map on characters is injective**: a character of `G` that vanishes after
composition with a surjection is zero. -/
lemma alpha_injective (π : G' →* G) (hπ : Function.Surjective π) :
    Function.Injective (alpha (p := p) π) := by
  intro f g hfg
  refine AddMonoidHom.ext (fun q => ?_)
  have h := congrArg (fun u : Additive G' →+ ZMod p =>
    u (Additive.ofMul (Function.surjInv hπ q.toMul))) hfg
  have h2 : π (Function.surjInv hπ q.toMul) = q.toMul := Function.surjInv_eq hπ q.toMul
  simpa [alpha_apply, h2] using h

/-- A character of `G'` restricts to zero on `N = ker π` if and only if it vanishes on `N`. -/
lemma beta_eq_zero_iff (π : G' →* G) (hπ : Function.Surjective π)
    (f : Additive G' →+ ZMod p) :
    beta (p := p) π f = 0 ↔ ∀ n : π.ker, f (Additive.ofMul (n : G')) = 0 := by
  constructor
  · intro h n
    have h2 : (beta (p := p) π f : Additive π.ker →+ ZMod p) (Additive.ofMul n) = 0 := by
      rw [show (beta (p := p) π f : Additive π.ker →+ ZMod p) = 0 from
        congrArg Subtype.val h]
      rfl
    simpa [beta_apply_coe, resHom_apply, iotaN_apply, toMul_ofMul] using h2
  · intro h
    refine Subtype.ext ?_
    refine AddMonoidHom.ext (fun x => ?_)
    show f (iotaN π x) = 0
    rw [show iotaN π x = Additive.ofMul ((x.toMul : π.ker) : G') from rfl, h x.toMul]

/-- A character of `G'` vanishing on `N = ker π` factors through `π`. -/
lemma exists_alpha_eq_of_vanish (π : G' →* G) (hπ : Function.Surjective π)
    (f : Additive G' →+ ZMod p) (hf : ∀ n : π.ker, f (Additive.ofMul (n : G')) = 0) :
    ∃ g : Additive G →+ ZMod p, alpha (p := p) π g = f := by
  refine ⟨AddMonoidHom.mk' (fun q : Additive G =>
    f (Additive.ofMul (Function.surjInv hπ q.toMul))) ?_, ?_⟩
  · intro q₁ q₂
    have hfac : (Additive.ofMul (Function.surjInv hπ q₁.toMul) : Additive G')
        + Additive.ofMul (Function.surjInv hπ q₂.toMul)
        = Additive.ofMul ((factor π hπ q₁.toMul q₂.toMul : π.ker) : G')
          + Additive.ofMul (Function.surjInv hπ (q₁.toMul * q₂.toMul)) := by
      rw [← ofMul_mul, ← factor_mul_section, ofMul_mul]
    have hzero : f (Additive.ofMul ((factor π hπ q₁.toMul q₂.toMul : π.ker) : G')) = 0 :=
      hf (factor π hπ q₁.toMul q₂.toMul)
    calc f (Additive.ofMul (Function.surjInv hπ ((q₁ + q₂).toMul)))
        = f (Additive.ofMul (Function.surjInv hπ (q₁.toMul * q₂.toMul))) := by rw [toMul_add]
      _ = f (Additive.ofMul (Function.surjInv hπ (q₁.toMul))
              + Additive.ofMul (Function.surjInv hπ (q₂.toMul))) := by
            rw [hfac, map_add, hzero, zero_add]
      _ = f (Additive.ofMul (Function.surjInv hπ (q₁.toMul)))
              + f (Additive.ofMul (Function.surjInv hπ (q₂.toMul))) := by rw [map_add]
  · refine AddMonoidHom.ext (fun x => ?_)
    have hx : (Additive.ofMul (Function.surjInv hπ (π x.toMul)) : Additive G')
        + Additive.ofMul ((⟨(Function.surjInv hπ (π x.toMul))⁻¹ * x.toMul,
            section_inv_mul_mem π hπ x.toMul⟩ : π.ker) : G') = x := by
      have hcoe : ((⟨(Function.surjInv hπ (π x.toMul))⁻¹ * x.toMul,
            section_inv_mul_mem π hπ x.toMul⟩ : π.ker) : G')
          = (Function.surjInv hπ (π x.toMul))⁻¹ * x.toMul := rfl
      rw [← ofMul_mul, hcoe, mul_inv_cancel_left, ofMul_toMul]
    have h1 : f (Additive.ofMul (Function.surjInv hπ (π x.toMul)))
        + f (Additive.ofMul ((⟨(Function.surjInv hπ (π x.toMul))⁻¹ * x.toMul,
            section_inv_mul_mem π hπ x.toMul⟩ : π.ker) : G')) = f x := by
      rw [← map_add, hx]
    have h2 : f (Additive.ofMul ((⟨(Function.surjInv hπ (π x.toMul))⁻¹ * x.toMul,
            section_inv_mul_mem π hπ x.toMul⟩ : π.ker) : G')) = 0 :=
      hf ⟨_, section_inv_mul_mem π hπ x.toMul⟩
    show f (Additive.ofMul (Function.surjInv hπ (π x.toMul))) = f x
    calc f (Additive.ofMul (Function.surjInv hπ (π x.toMul)))
        = f (Additive.ofMul (Function.surjInv hπ (π x.toMul)))
            + f (Additive.ofMul ((⟨(Function.surjInv hπ (π x.toMul))⁻¹ * x.toMul,
                section_inv_mul_mem π hπ x.toMul⟩ : π.ker) : G')) := by rw [h2, add_zero]
      _ = f x := h1

/-- **The range of the inflation map on characters is the kernel of the restriction map.** -/
lemma ker_beta_eq_range_alpha (π : G' →* G) (hπ : Function.Surjective π) :
    LinearMap.ker (beta (p := p) π) = LinearMap.range (alpha (p := p) π) := by
  ext f
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hf
    exact exists_alpha_eq_of_vanish π hπ f ((beta_eq_zero_iff π hπ f).mp hf)
  · rintro ⟨g, rfl⟩
    rw [beta_eq_zero_iff π hπ]
    intro n
    show alpha (p := p) π g (Additive.ofMul (n : G')) = 0
    rw [alpha_apply, piAdd_apply]
    have : π ((Additive.ofMul (n : G')).toMul) = 1 := by
      simpa only [toMul_ofMul, MonoidHom.mem_ker] using n.2
    rw [this, ofMul_one, map_zero]

end AlphaBeta

end

end Work.CFTLib
