import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.Wielandt

/-- Bender–Suzuki / Wielandt conjugation lemma.

Let `K` be a finite subgroup of a finite group `F` which is normalized by a
subgroup `P`, and suppose `K` satisfies the TI-condition relative to `P`:
`P ⊓ k⁻¹ P k = 1` for every nontrivial `k ∈ K`. Then for every nontrivial
`p ∈ P` and every `k ∈ K` there is a *unique* `x ∈ K` with
`x p x⁻¹ = k p`.

The map `K → K`, `x ↦ x p x⁻¹ p⁻¹`, is injective: `x₁ p x₁⁻¹ p⁻¹ = x₂ p x₂⁻¹ p⁻¹`
forces `a := x₂⁻¹ x₁` to commute with `p`, whence (if `a ≠ 1`) the nontrivial
element `p` lies in `P ⊓ P.map (MulAut.conj a⁻¹) = ⊥`, a contradiction.  Since
`K` is finite, injectivity upgrades to surjectivity, giving existence, and the
equation gives uniqueness. -/
theorem ConjExistUnique {F : Type*} [Group F] [Finite F] (K P : Subgroup F)
    (hnorm : ∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hTI : ∀ k ∈ K, k ≠ 1 → P ⊓ P.map (MulAut.conj k⁻¹) = ⊥)
    (p : P) (hp : (p : F) ≠ 1) (k : K) :
    ∃! x : K, (x : F) * (p : F) * (x : F)⁻¹ = (k : F) * (p : F) := by
  -- Membership in `K` of `x * p * x⁻¹ * p⁻¹`, obtained from `P` normalizing `K`.
  have hmem : ∀ x : K, (x : F) * (p : F) * (x : F)⁻¹ * (p : F)⁻¹ ∈ K := by
    intro x
    have h1 : (p : F) * (x : F)⁻¹ * (p : F)⁻¹ ∈ K :=
      hnorm (p : F) p.2 (x : F)⁻¹ (K.inv_mem x.2)
    have h2 : (x : F) * ((p : F) * (x : F)⁻¹ * (p : F)⁻¹) ∈ K := K.mul_mem x.2 h1
    simpa only [mul_assoc] using h2
  let f : K → K := fun x => ⟨(x : F) * (p : F) * (x : F)⁻¹ * (p : F)⁻¹, hmem x⟩
  have hfval : ∀ x : K, (f x : F) = (x : F) * (p : F) * (x : F)⁻¹ * (p : F)⁻¹ := fun _ => rfl
  have hinj : Function.Injective f := by
    intro x₁ x₂ h
    have h' : (x₁ : F) * (p : F) * (x₁ : F)⁻¹ * (p : F)⁻¹
        = (x₂ : F) * (p : F) * (x₂ : F)⁻¹ * (p : F)⁻¹ := by
      have := congrArg (fun y : K => (y : F)) h
      simpa only [hfval] using this
    have h2 : (x₁ : F) * (p : F) * (x₁ : F)⁻¹ = (x₂ : F) * (p : F) * (x₂ : F)⁻¹ := by
      have := congrArg (fun z => z * (p : F)) h'
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using this
    set a : K := x₂⁻¹ * x₁ with ha
    -- `a` commutes with `p`
    have hkeyF : ((x₂ : F)⁻¹ * (x₁ : F)) * (p : F) * ((x₂ : F)⁻¹ * (x₁ : F))⁻¹ = (p : F) := by
      have hh := congrArg (fun z => (x₂ : F)⁻¹ * z * (x₂ : F)) h2
      have e1 : ((x₂ : F)⁻¹ * (x₁ : F)) * (p : F) * ((x₂ : F)⁻¹ * (x₁ : F))⁻¹
          = (x₂ : F)⁻¹ * ((x₁ : F) * (p : F) * (x₁ : F)⁻¹) * (x₂ : F) := by group
      have e2 : (x₂ : F)⁻¹ * ((x₂ : F) * (p : F) * (x₂ : F)⁻¹) * (x₂ : F) = (p : F) := by
        group
      rw [e1, hh, e2]
    have hkey : (a : F) * (p : F) * (a : F)⁻¹ = (p : F) := hkeyF
    have ha1 : a = 1 := by
      by_contra hane
      have haneF : (a : F) ≠ 1 := by
        intro hc
        exact hane (Subtype.ext hc)
      have hbot := hTI (a : F) a.2 haneF
      have hpP : (p : F) ∈ P := p.2
      have hpMap : (p : F) ∈ P.map (MulAut.conj (a : F)⁻¹) := by
        rw [Subgroup.mem_map]
        refine ⟨(p : F), p.2, ?_⟩
        change (MulAut.conj (a : F)⁻¹) (p : F) = (p : F)
        rw [MulAut.conj_apply, inv_inv]
        have hkey2 : (a : F)⁻¹ * (p : F) * (a : F) = (p : F) := by
          have hh := congrArg (fun z => (a : F)⁻¹ * z * (a : F)) hkey
          have e3 : (a : F)⁻¹ * ((a : F) * (p : F) * (a : F)⁻¹) * (a : F) = (p : F) := by
            group
          rw [e3] at hh
          exact hh.symm
        exact hkey2
      have hmeminf : (p : F) ∈ P ⊓ P.map (MulAut.conj (a : F)⁻¹) :=
        Subgroup.mem_inf.mpr ⟨hpP, hpMap⟩
      rw [hbot] at hmeminf
      exact hp (Subgroup.mem_bot.mp hmeminf)
    have hx : x₂ = x₁ := by
      have : x₂⁻¹ * x₁ = 1 := by rw [← ha]; exact ha1
      exact inv_mul_eq_one.mp this
    exact hx.symm
  -- Finiteness upgrades injectivity to surjectivity.
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
  obtain ⟨x, hx⟩ := hsurj k
  have hxv : (x : F) * (p : F) * (x : F)⁻¹ * (p : F)⁻¹ = (k : F) := by
    have := congrArg (fun y : K => (y : F)) hx
    simpa only [hfval] using this
  refine ⟨x, ?_, ?_⟩
  · have := congrArg (fun z => z * (p : F)) hxv
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using this
  · intro y hy
    have hyv : (y : F) * (p : F) * (y : F)⁻¹ * (p : F)⁻¹ = (k : F) := by
      have := congrArg (fun z => z * (p : F)⁻¹) hy
      simpa only [mul_assoc, mul_inv_cancel, inv_mul_cancel, mul_one] using this
    have hxy : f y = f x := by
      apply Subtype.ext
      rw [hfval, hfval, hyv, hxv]
    exact hinj hxy

end Work.BSLit.Wielandt
