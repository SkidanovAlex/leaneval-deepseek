import Mathlib
import Submission.Work.CFTLib.fiveTerm_setup

/-!
# The transgression is a coboundary exactly on the image of the restriction map

Let `π : G' →* G` be a surjective homomorphism of groups with kernel `N = ker π`, and let
`t : invCharSubmodule p N` be a `G'`-invariant additive character of `N` (the model of
`H¹(N,𝔽_p)^{G'}`).  The transgression attached to `t` is the `2`-cochain

`candFun π hπ t (x, y) = - t (σ x * σ y * (σ (x*y))⁻¹)`

on `G` (for a set-theoretic section `σ` of `π`), and `beta π` is the restriction map on
characters, `f ↦ f|_N`.  This file proves

`candFun π hπ t ∈ B²(G,𝔽_p) ↔ t ∈ range (beta π)`,

i.e. the exactness of the five-term inflation–restriction sequence

`H¹(G,𝔽_p) → H¹(G',𝔽_p) → H¹(N,𝔽_p)^{G'} → H²(G,𝔽_p) → H²(G',𝔽_p)`

at `H¹(N,𝔽_p)^{G'}` (trivial coefficients).

The two directions are the standard computations:

* if `t = f|_N`, then `candFun t = d₁₂ b` for `b x = - f (σ x)`;
* conversely, if `candFun t = d₁₂ b`, then `f g = t(σ (π g)⁻¹ g) - b (π g)` is an additive
  character of `G'` restricting to `t`; its additivity is exactly the cocycle identity, and
  the value on `N` uses the normalisation `b 1 = - t (σ 1)`, which is the identity at `(1,1)`.
-/

namespace Work.CFTLib

open CategoryTheory Representation groupCohomology
open scoped Classical

noncomputable section

variable {p : ℕ} {G G' : Type} [Group G] [Group G']

/-- The explicit formula for the second differential `d₁₂` of the trivial representation
`𝔽_p` of `G`. -/
private lemma candB2_d12_apply (b : G → ZMod p) (x y : G) :
    d12 p G b (x, y) = b y - b (x * y) + b x := by
  show (groupCohomology.d₁₂ (Rep.trivial (ZMod p) G (ZMod p))).hom b (x, y) = _
  rw [groupCohomology.d₁₂_hom_apply, Rep.trivial_ρ_apply]

/-- `B²(G,𝔽_p)` is the range of the second differential. -/
private lemma candB2_mem_B2_iff (z : G × G → ZMod p) :
    z ∈ B2 p G ↔ ∃ b : G → ZMod p, d12 p G b = z := by
  show z ∈ LinearMap.range (d12 p G) ↔ _
  exact LinearMap.mem_range

/-- The element `σ (π g)⁻¹ * g` of the kernel attached to `g : G'`. -/
private def nEl (π : G' →* G) (hπ : Function.Surjective π) (g : G') : π.ker :=
  ⟨(sectionOf π hπ (π g))⁻¹ * g, section_inv_mul_mem π hπ g⟩

/-- The auxiliary cochain in terms of `nEl`. -/
private lemma auxFun_eq_nEl (π : G' →* G) (hπ : Function.Surjective π)
    (t : invCharSubmodule p π.ker) (g : G') :
    auxFun π hπ t g = t.1 (Additive.ofMul (nEl π hπ g)) := rfl

/-- The element `σ 1` of the kernel. -/
private def oneKer (π : G' →* G) (hπ : Function.Surjective π) : π.ker :=
  ⟨sectionOf π hπ 1, by rw [MonoidHom.mem_ker, sectionOf_spec]⟩

/-- The special value `factor 1 1` of the cocycle. -/
private lemma factor_one_one (π : G' →* G) (hπ : Function.Surjective π) :
    factor π hπ 1 1 = oneKer π hπ := by
  apply Subtype.ext
  rw [factor_coe, oneKer]
  simp only [mul_one]
  group

/-- Conjugation of an element of the kernel by an element of `G'`. -/
private def conjKer (π : G' →* G) (g : G') (n : π.ker) : π.ker :=
  ⟨g⁻¹ * (n : G') * g, Subgroup.Normal.conj_mem' (inferInstance : π.ker.Normal) n.1 n.2 g⟩

/-- Invariance of `t` under `conjKer`. -/
private lemma conjKer_apply (π : G' →* G) (t : invCharSubmodule p π.ker) (g : G') (n : π.ker) :
    t.1 (Additive.ofMul (conjKer π g n)) = t.1 (Additive.ofMul n) := t.2 g n

/-- The factorisation of `nEl (g₁ * g₂)` used to prove multiplicativity of `auxFun`. -/
private lemma nEl_mul (π : G' →* G) (hπ : Function.Surjective π) (g₁ g₂ : G') :
    nEl π hπ (g₁ * g₂) =
      conjKer π (sectionOf π hπ (π g₁ * π g₂)) (factor π hπ (π g₁) (π g₂))
        * conjKer π (sectionOf π hπ (π g₂)) (nEl π hπ g₁) * nEl π hπ g₂ := by
  apply Subtype.ext
  simp only [nEl, conjKer, Subtype.coe_mk, Subgroup.coe_mul]
  rw [map_mul, factor_coe]
  group

/-- **Multiplicativity of the auxiliary cochain**: `auxFun` satisfies the inhomogeneous
cocycle relation up to the candidate `2`-cocycle. -/
private lemma candB2_auxFun_mul (π : G' →* G) (hπ : Function.Surjective π)
    (t : invCharSubmodule p π.ker) (g₁ g₂ : G') :
    auxFun π hπ t (g₁ * g₂) = t.1 (Additive.ofMul (factor π hπ (π g₁) (π g₂)))
      + auxFun π hπ t g₁ + auxFun π hπ t g₂ := by
  have hEq := nEl_mul π hπ g₁ g₂
  calc auxFun π hπ t (g₁ * g₂)
      = t.1 (Additive.ofMul (conjKer π (sectionOf π hπ (π g₁ * π g₂))
            (factor π hπ (π g₁) (π g₂))
          * conjKer π (sectionOf π hπ (π g₂)) (nEl π hπ g₁) * nEl π hπ g₂)) := by
        rw [auxFun_eq_nEl, hEq]
    _ = t.1 (Additive.ofMul (conjKer π (sectionOf π hπ (π g₁ * π g₂))
            (factor π hπ (π g₁) (π g₂))))
          + t.1 (Additive.ofMul (conjKer π (sectionOf π hπ (π g₂)) (nEl π hπ g₁)))
          + t.1 (Additive.ofMul (nEl π hπ g₂)) := by
        rw [ofMul_mul, ofMul_mul, map_add, map_add]
    _ = t.1 (Additive.ofMul (factor π hπ (π g₁) (π g₂)))
          + t.1 (Additive.ofMul (nEl π hπ g₁)) + t.1 (Additive.ofMul (nEl π hπ g₂)) := by
        rw [conjKer_apply, conjKer_apply]
    _ = t.1 (Additive.ofMul (factor π hπ (π g₁) (π g₂)))
          + auxFun π hπ t g₁ + auxFun π hπ t g₂ := by
        rw [auxFun_eq_nEl, auxFun_eq_nEl]

/-- **The forward direction of the computation**: if `t = f|_N` is the restriction of a
character `f` of `G'`, then `candFun t` is the coboundary of `b x = - f (σ x)`. -/
private lemma candB2_candFun_beta_eq_d12 (π : G' →* G) (hπ : Function.Surjective π)
    (f : Additive G' →+ ZMod p) :
    candFun π hπ (beta (p := p) π f) =
      d12 p G (fun x : G => - f (Additive.ofMul (sectionOf π hπ x))) := by
  funext z
  obtain ⟨x, y⟩ := z
  rw [candB2_d12_apply, candFun_apply]
  have hkey : ((beta (p := p) π f : invCharSubmodule p π.ker) : Additive π.ker →+ ZMod p)
        (Additive.ofMul (factor π hπ x y))
      = f (Additive.ofMul (sectionOf π hπ x)) + f (Additive.ofMul (sectionOf π hπ y))
        - f (Additive.ofMul (sectionOf π hπ (x * y))) := by
    rw [beta_apply_coe, resHom_apply, iotaN_apply, toMul_ofMul, factor_coe,
      ofMul_mul, ofMul_mul, ofMul_inv]
    simp only [map_add, map_neg]
    abel
  rw [hkey]
  abel

/-- **The transgression is a coboundary exactly on the image of the restriction map.** -/
theorem fiveTerm_candFun_mem_B2_iff {p : ℕ} [Fact p.Prime] {G G' : Type} [Group G] [Group G']
    (π : G' →* G) (hπ : Function.Surjective π) (t : Work.CFTLib.invCharSubmodule p π.ker) :
    Work.CFTLib.candFun π hπ t ∈ Work.CFTLib.B2 p G ↔
      t ∈ LinearMap.range (Work.CFTLib.beta π) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := (candB2_mem_B2_iff (p := p) (G := G) (candFun π hπ t)).mp h
    have hb' : ∀ x y : G, d12 p G b (x, y) = candFun π hπ t (x, y) :=
      fun x y => congrFun hb (x, y)
    -- the value of `b` at `1`, forced by the identity at `(1,1)`
    have hb1 : b 1 = - t.1 (Additive.ofMul (oneKer π hπ)) := by
      have h1 := hb' 1 1
      rw [candB2_d12_apply, candFun_apply] at h1
      rw [mul_one, factor_one_one π hπ] at h1
      simpa using h1
    -- the candidate character `f (g) = auxFun g - b (π g)`
    let F : G' → ZMod p := fun g => auxFun π hπ t g - b (π g)
    have hFadd : ∀ g₁ g₂ : G', F (g₁ * g₂) = F g₁ + F g₂ := by
      intro g₁ g₂
      have hA := candB2_auxFun_mul π hπ t g₁ g₂
      have hB := hb' (π g₁) (π g₂)
      rw [candB2_d12_apply, candFun_apply] at hB
      show auxFun π hπ t (g₁ * g₂) - b (π (g₁ * g₂)) =
        (auxFun π hπ t g₁ - b (π g₁)) + (auxFun π hπ t g₂ - b (π g₂))
      rw [map_mul, hA]
      linear_combination hB
    have hFker : ∀ m : π.ker, F ((m : π.ker) : G') = t.1 (Additive.ofMul m) := by
      intro m
      have hm : π ((m : π.ker) : G') = 1 := MonoidHom.mem_ker.mp m.2
      have hsec : sectionOf π hπ (π ((m : π.ker) : G')) = sectionOf π hπ 1 := by rw [hm]
      have hkey : nEl π hπ ((m : π.ker) : G') = (oneKer π hπ)⁻¹ * m := by
        apply Subtype.ext
        simp only [nEl, oneKer, Subtype.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv]
        simp only [hsec]
      have hval : auxFun π hπ t ((m : π.ker) : G')
          = - t.1 (Additive.ofMul (oneKer π hπ)) + t.1 (Additive.ofMul m) := by
        rw [auxFun_eq_nEl, hkey, ofMul_mul, ofMul_inv, map_add, map_neg]
      show auxFun π hπ t ((m : π.ker) : G') - b (π ((m : π.ker) : G')) = t.1 (Additive.ofMul m)
      rw [hm, hb1, hval]
      abel
    have hFone : F 1 = 0 := by
      have h1 := hFadd 1 1
      rw [mul_one] at h1
      exact add_eq_left.mp h1.symm
    let f : Additive G' →+ ZMod p :=
      { toFun := fun x => F x.toMul
        map_zero' := by
          show F (0 : Additive G').toMul = 0
          rw [show (0 : Additive G').toMul = 1 from rfl, hFone]
        map_add' := fun x y => by
          show F (x.toMul * y.toMul) = F x.toMul + F y.toMul
          rw [← toMul_add]
          exact hFadd x.toMul y.toMul }
    refine ⟨f, ?_⟩
    apply Subtype.ext
    rw [beta_apply_coe]
    apply AddMonoidHom.ext
    intro n
    rw [resHom_apply, iotaN_apply]
    change F ((n.toMul : π.ker) : G') = t.1 n
    rw [hFker n.toMul, ofMul_toMul]
  · intro ht
    obtain ⟨f, hf⟩ := ht
    refine (candB2_mem_B2_iff (p := p) (G := G) (candFun π hπ t)).mpr
      ⟨fun x : G => - f (Additive.ofMul (sectionOf π hπ x)), ?_⟩
    rw [← hf]
    exact (candB2_candFun_beta_eq_d12 π hπ f).symm

end

end Work.CFTLib
