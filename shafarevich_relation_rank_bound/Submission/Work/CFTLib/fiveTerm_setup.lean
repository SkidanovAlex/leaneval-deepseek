import Mathlib
import Submission.Work.CFTLib.RelShafDefs

/-!
# The five-term inflation–restriction sequence: vocabulary

Let `π : G' →* G` be a surjective homomorphism of groups with kernel `N = ker π`.  This file
fixes the vocabulary for the proof of the dimension identity of the five-term exact sequence

`H¹(G,𝔽_p) → H¹(G',𝔽_p) → H¹(N,𝔽_p)^{G'} → H²(G,𝔽_p) → H²(G',𝔽_p)`,

namely the linear maps

* `Work.CFTLib.piAdd π` — the additive homomorphism underlying `π`;
* `Work.CFTLib.iotaN π` — the inclusion `N → G'`, additively;
* `Work.CFTLib.alpha p π` — inflation on additive characters `Hom(G,𝔽_p) → Hom(G',𝔽_p)`;
* `Work.CFTLib.resHom p π` — restriction of characters to `N`;
* `Work.CFTLib.beta p π` — restriction of characters, landing in the `G'`-invariant characters
  `invCharSubmodule p N` (the model of `H¹(N,𝔽_p)^{G'}`);
* `Work.CFTLib.candFun p π hπ t` — the `2`-cochain of `G` attached to an invariant character
  `t` and a section `σ` of `π` (the transgression);
* `Work.CFTLib.auxFun p π hπ t` — the `1`-cochain on `G'` exhibiting `inf (cand t)` as a
  coboundary.

The groups are finite only where stated; the cocycle computations hold for arbitrary groups.
-/

namespace Work.CFTLib

open CategoryTheory Representation groupCohomology
open scoped Classical

noncomputable section

section Setup

variable {p : ℕ} {G G' : Type} [Group G] [Group G']

/-- The additive homomorphism underlying `π : G' →* G`. -/
def piAdd (π : G' →* G) : Additive G' →+ Additive G where
  toFun x := Additive.ofMul (π x.toMul)
  map_zero' := by simp
  map_add' x y := by
    rw [toMul_add, map_mul, ofMul_mul]

@[simp] lemma piAdd_apply (π : G' →* G) (x : Additive G') :
    piAdd π x = Additive.ofMul (π x.toMul) := rfl

/-- The inclusion of `ker π` into `G'`, as an additive homomorphism. -/
def iotaN (π : G' →* G) : Additive π.ker →+ Additive G' where
  toFun x := Additive.ofMul ((x.toMul : π.ker) : G')
  map_zero' := rfl
  map_add' x y := rfl

@[simp] lemma iotaN_apply (π : G' →* G) (x : Additive π.ker) :
    iotaN π x = Additive.ofMul ((x.toMul : π.ker) : G') := rfl

/-- In an additive character, the expression `g⁻¹ a g` may be replaced by `a`. -/
lemma addHom_conj (f : Additive G' →+ ZMod p) (g a : G') :
    f (Additive.ofMul (g⁻¹ * a * g)) = f (Additive.ofMul a) := by
  have h : (Additive.ofMul (g⁻¹ * a * g) : Additive G')
      = - Additive.ofMul g + (Additive.ofMul a + Additive.ofMul g) := by
    rw [show g⁻¹ * a * g = g⁻¹ * (a * g) from by group, ofMul_mul, ofMul_mul, ofMul_inv]
  rw [h, map_add, map_add, map_neg]
  abel

/-- **Inflation on additive characters**: `Hom(G,𝔽_p) → Hom(G',𝔽_p)`, `f ↦ f ∘ π`. -/
def alpha (π : G' →* G) : (Additive G →+ ZMod p) →ₗ[ZMod p] (Additive G' →+ ZMod p) where
  toFun f := f.comp (piAdd π)
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

/-- **Restriction of additive characters** to `N = ker π`. -/
def resHom (π : G' →* G) :
    (Additive G' →+ ZMod p) →ₗ[ZMod p] (Additive π.ker →+ ZMod p) where
  toFun f := f.comp (iotaN π)
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

@[simp] lemma alpha_apply (π : G' →* G) (f : Additive G →+ ZMod p) (x : Additive G') :
    alpha π f x = f (piAdd π x) := rfl

@[simp] lemma resHom_apply (π : G' →* G) (f : Additive G' →+ ZMod p) (x : Additive π.ker) :
    resHom π f x = f (iotaN π x) := rfl

/-- The restriction of an additive character of `G'` to `N = ker π` is invariant under
conjugation by `G'`. -/
lemma resHom_mem_invCharSubmodule (π : G' →* G) (f : Additive G' →+ ZMod p) :
    resHom π f ∈ invCharSubmodule p π.ker := by
  intro g n
  simp only [resHom_apply, iotaN_apply, toMul_ofMul]
  exact addHom_conj f g (n : G')

/-- **The restriction map on characters**, landing in the `G'`-invariant characters of `N`:
the model of `H¹(G',𝔽_p) → H¹(N,𝔽_p)^{G'}`. -/
def beta (π : G' →* G) :
    (Additive G' →+ ZMod p) →ₗ[ZMod p] invCharSubmodule p π.ker :=
  LinearMap.codRestrict (invCharSubmodule p π.ker) (resHom π)
    (resHom_mem_invCharSubmodule π)

@[simp] lemma beta_apply_coe (π : G' →* G) (f : Additive G' →+ ZMod p) :
    ((beta π f : invCharSubmodule p π.ker) : Additive π.ker →+ ZMod p) = resHom π f := rfl

end Setup

section Section

variable {G G' : Type} [Group G] [Group G'] (π : G' →* G) (hπ : Function.Surjective π)

/-- A set-theoretic section of a surjective group homomorphism. -/
abbrev sectionOf : G → G' := Function.surjInv hπ

lemma sectionOf_spec (q : G) : π (sectionOf π hπ q) = q := Function.surjInv_eq hπ q

end Section

section Candidate

variable {p : ℕ} {G G' : Type} [Group G] [Group G']

/-- The element `σ x * σ y * (σ (x*y))⁻¹ ∈ N` attached to a pair `(x,y)` of `G`. -/
def factor (π : G' →* G) (hπ : Function.Surjective π) (x y : G) : π.ker :=
  ⟨sectionOf π hπ x * sectionOf π hπ y * (sectionOf π hπ (x * y))⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, sectionOf_spec, sectionOf_spec,
      sectionOf_spec]
    simp⟩

@[simp] lemma factor_coe (π : G' →* G) (hπ : Function.Surjective π) (x y : G) :
    (factor π hπ x y : G') =
      sectionOf π hπ x * sectionOf π hπ y * (sectionOf π hπ (x * y))⁻¹ := rfl

/-- The `2`-cochain of `G` attached to an invariant character `t` of `N` and a section of `π`:
the transgression `H¹(N,𝔽_p)^{G'} → Z²(G,𝔽_p)`. -/
def candFun (π : G' →* G) (hπ : Function.Surjective π)
    (t : invCharSubmodule p π.ker) : G × G → ZMod p :=
  fun x => - (t.1 : Additive π.ker →+ ZMod p) (Additive.ofMul (factor π hπ x.1 x.2))

@[simp] lemma candFun_apply (π : G' →* G) (hπ : Function.Surjective π)
    (t : invCharSubmodule p π.ker) (x y : G) :
    candFun π hπ t (x, y) = - (t.1 : Additive π.ker →+ ZMod p)
      (Additive.ofMul (factor π hπ x y)) := rfl

/-- The `1`-cochain of `G'` exhibiting the inflation of the candidate as a coboundary. -/
def auxFun (π : G' →* G) (hπ : Function.Surjective π)
    (t : invCharSubmodule p π.ker) : G' → ZMod p :=
  fun g => (t.1 : Additive π.ker →+ ZMod p)
    (Additive.ofMul (⟨(sectionOf π hπ (π g))⁻¹ * g, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, sectionOf_spec]
      simp⟩ : π.ker))

lemma auxFun_apply (π : G' →* G) (hπ : Function.Surjective π)
    (t : invCharSubmodule p π.ker) (g : G') :
    auxFun π hπ t g = (t.1 : Additive π.ker →+ ZMod p)
      (Additive.ofMul (⟨(sectionOf π hπ (π g))⁻¹ * g, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, sectionOf_spec]
        simp⟩ : π.ker)) := rfl

section Decomp

variable {G G' : Type} [Group G] [Group G'] (π : G' →* G) (hπ : Function.Surjective π)

/-- The cocycle relation for the section: `factor x y * σ(x*y) = σ x * σ y`. -/
lemma factor_mul_section (x y : G) :
    (factor π hπ x y : G') * sectionOf π hπ (x * y) = sectionOf π hπ x * sectionOf π hπ y := by
  rw [factor_coe]
  group

/-- `σ (π g)⁻¹ * g` lies in the kernel of `π`. -/
lemma section_inv_mul_mem (g : G') : (sectionOf π hπ (π g))⁻¹ * g ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, sectionOf_spec]
  simp

/-- The decomposition `g = σ (π g) * (σ (π g))⁻¹ g` of an element of `G'`. -/
lemma section_mul_inv_mul (g : G') :
    sectionOf π hπ (π g) * ((⟨(sectionOf π hπ (π g))⁻¹ * g, section_inv_mul_mem π hπ g⟩ : π.ker) : G')
      = g := by
  rw [Subtype.coe_mk]
  group

end Decomp


/-- The transgression `H¹(N,𝔽_p)^{G'} → Z²(G,𝔽_p)` as a linear map: `t ↦ candFun t`. -/
def candLin (π : G' →* G) (hπ : Function.Surjective π) :
    invCharSubmodule p π.ker →ₗ[ZMod p] (G × G → ZMod p) where
  toFun t := candFun π hπ t
  map_add' t t' := by
    funext x
    obtain ⟨x₁, x₂⟩ := x
    rw [Pi.add_apply, candFun_apply, candFun_apply, candFun_apply,
      show (t + t').1 (Additive.ofMul (factor π hπ x₁ x₂))
        = t.1 (Additive.ofMul (factor π hπ x₁ x₂))
          + t'.1 (Additive.ofMul (factor π hπ x₁ x₂)) from rfl,
      neg_add]
  map_smul' c t := by
    funext x
    obtain ⟨x₁, x₂⟩ := x
    rw [Pi.smul_apply, candFun_apply, candFun_apply,
      show (c • t).1 (Additive.ofMul (factor π hπ x₁ x₂))
        = c • t.1 (Additive.ofMul (factor π hπ x₁ x₂)) from rfl, smul_neg]
    simp

end Candidate

section Precomp

variable {p : ℕ} {G G' : Type} [Group G] [Group G'] (π : G' →* G)

/-- Pullback of functions on `G × G` to `G' × G'` along `π`. -/
def precomp₂ : (G × G → ZMod p) →ₗ[ZMod p] (G' × G' → ZMod p) where
  toFun z := fun x => z (π x.1, π x.2)
  map_add' z z' := by ext x; rfl
  map_smul' c z := by ext x; rfl

@[simp] lemma precomp₂_apply (z : G × G → ZMod p) (x : G' × G') :
    precomp₂ π z x = z (π x.1, π x.2) := rfl

/-- Pullback of functions on `G` to `G'` along `π`. -/
def precomp₁ : (G → ZMod p) →ₗ[ZMod p] (G' → ZMod p) where
  toFun b := fun x => b (π x)
  map_add' b b' := by ext x; rfl
  map_smul' c b := by ext x; rfl

@[simp] lemma precomp₁_apply (b : G → ZMod p) (x : G') :
    precomp₁ π b x = b (π x) := rfl

end Precomp

section Cocycles

/-- `Z²(G,𝔽_p)`: the `2`-cocycles with trivial coefficients. -/
abbrev Z2 (p : ℕ) (G : Type) [Group G] : Submodule (ZMod p) (G × G → ZMod p) :=
  cocycles₂ (Rep.trivial (ZMod p) G (ZMod p))

/-- `B²(G,𝔽_p)`: the `2`-coboundaries with trivial coefficients. -/
abbrev B2 (p : ℕ) (G : Type) [Group G] : Submodule (ZMod p) (G × G → ZMod p) :=
  coboundaries₂ (Rep.trivial (ZMod p) G (ZMod p))

/-- `Z¹(G,𝔽_p)`: the `1`-cocycles with trivial coefficients. -/
abbrev Z1 (p : ℕ) (G : Type) [Group G] : Submodule (ZMod p) (G → ZMod p) :=
  cocycles₁ (Rep.trivial (ZMod p) G (ZMod p))

/-- `H²(G,𝔽_p)`: the second group cohomology with trivial coefficients. -/
abbrev H2 (p : ℕ) (G : Type) [Group G] : Type :=
  groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 2

/-- `H¹(G,𝔽_p)`: the first group cohomology with trivial coefficients. -/
abbrev H1 (p : ℕ) (G : Type) [Group G] : Type :=
  groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 1

/-- The first differential `d₁₂` on the `1`-cochains of `G`, as a linear map on function
spaces. -/
abbrev d12 (p : ℕ) (G : Type) [Group G] : (G → ZMod p) →ₗ[ZMod p] (G × G → ZMod p) :=
  (groupCohomology.d₁₂ (Rep.trivial (ZMod p) G (ZMod p))).hom

/-- The second differential `d₂₃` on the `2`-cochains of `G`, as a linear map on function
spaces. -/
abbrev d23 (p : ℕ) (G : Type) [Group G] : (G × G → ZMod p) →ₗ[ZMod p] (G × G × G → ZMod p) :=
  (groupCohomology.d₂₃ (Rep.trivial (ZMod p) G (ZMod p))).hom

/-- The quotient map `Z¹(G,𝔽_p) → H¹(G,𝔽_p)`. -/
abbrev H1pi (p : ℕ) (G : Type) [Group G] : Z1 p G →ₗ[ZMod p] H1 p G :=
  (groupCohomology.H1π (Rep.trivial (ZMod p) G (ZMod p))).hom

/-- The quotient map `Z²(G,𝔽_p) → H²(G,𝔽_p)`. -/
abbrev H2pi (p : ℕ) (G : Type) [Group G] : Z2 p G →ₗ[ZMod p] H2 p G :=
  (groupCohomology.H2π (Rep.trivial (ZMod p) G (ZMod p))).hom

/-- The `2`-coboundaries, viewed as a submodule of the `2`-cocycles of `G`. -/
abbrev Bzc (p : ℕ) (G : Type) [Group G] : Submodule (ZMod p) (Z2 p G) :=
  Submodule.comap (Z2 p G).subtype (B2 p G)

/-- The kernel of the quotient map `Z²(G) → H²(G)` is the space of coboundaries. -/
lemma H2pi_ker (p : ℕ) (G : Type) [Group G] :
    LinearMap.ker (H2pi p G) = Bzc p G := by
  ext z
  rw [LinearMap.mem_ker, Submodule.mem_comap, groupCohomology.H2π_eq_zero_iff]
  rfl

/-- The quotient map `Z²(G) → H²(G)` is surjective. -/
lemma H2pi_range (p : ℕ) (G : Type) [Group G] :
    LinearMap.range (H2pi p G) = ⊤ := by
  have h : Function.Surjective (H2pi p G) :=
    (ModuleCat.epi_iff_surjective
      (groupCohomology.H2π (Rep.trivial (ZMod p) G (ZMod p)))).mp inferInstance
  exact LinearMap.range_eq_top.mpr h

/-- The kernel of the quotient map `Z²(G) → H²(G)`, stated with the coercion to functions. -/
lemma H2pi_eq_zero_iff (p : ℕ) (G : Type) [Group G] (x : Z2 p G) :
    H2pi p G x = 0 ↔ (x : G × G → ZMod p) ∈ B2 p G := by
  rw [show H2pi p G x
      = (groupCohomology.H2π (Rep.trivial (ZMod p) G (ZMod p))) x from rfl]
  exact groupCohomology.H2π_eq_zero_iff (A := Rep.trivial (ZMod p) G (ZMod p)) x

end Cocycles

end

end Work.CFTLib
