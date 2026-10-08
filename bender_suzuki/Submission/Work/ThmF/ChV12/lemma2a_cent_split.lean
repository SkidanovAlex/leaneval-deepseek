import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Ch. V §2, Lemma 2a: splitting of the centralizer along `H = Q ⋊ D`

If `Q ` is normal in `H` (`H ≤ N_G(Q)`), `Q ∩ D = 1` and `Q D = H`, and `X ≤ D`, then the
centralizer `C_G(X)` splits over the decomposition of `H`:

`H ∩ C_G(X) = (Q ∩ C_G(X)) ⊔ (D ∩ C_G(X))`.

The mathematical content is that any `h ∈ H ∩ C_G(X)` has a unique decomposition `h = q * d`
with `q ∈ Q`, `d ∈ D` (uniqueness from `Q ∩ D = 1`, existence because `Q` is normal in `H`),
and the commutation relation `h x = x h` for `x ∈ X` then forces each of `q` and `d` to commute
with `x` as well.
-/

namespace Work.ThmF.ChV12

/-- Uniqueness of the `Q * D` decomposition when `Q ∩ D = ⊥`. -/
lemma mul_decomp_unique {G : Type} [Group G] {Q D : Subgroup G} (hinf : Q ⊓ D = ⊥)
    {q₁ q₂ d₁ d₂ : G} (hq₁ : q₁ ∈ Q) (hq₂ : q₂ ∈ Q) (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D)
    (h : q₁ * d₁ = q₂ * d₂) : q₁ = q₂ ∧ d₁ = d₂ := by
  have h' : q₂⁻¹ * q₁ = d₂ * d₁⁻¹ := by
    calc q₂⁻¹ * q₁ = q₂⁻¹ * (q₁ * d₁) * d₁⁻¹ := by group
      _ = q₂⁻¹ * (q₂ * d₂) * d₁⁻¹ := by rw [h]
      _ = d₂ * d₁⁻¹ := by group
  have hmem : q₂⁻¹ * q₁ ∈ Q ⊓ D := by
    refine ⟨Q.mul_mem (Q.inv_mem hq₂) hq₁, ?_⟩
    rw [h']; exact D.mul_mem hd₂ (D.inv_mem hd₁)
  rw [hinf] at hmem
  have h1 : q₂⁻¹ * q₁ = 1 := Subgroup.mem_bot.mp hmem
  refine ⟨(inv_mul_eq_one.mp h1).symm, (mul_inv_eq_one.mp (by rw [← h', h1])).symm⟩

/-- Existence of the `Q * D` decomposition: if `Q` is normal in `H` and `Q ⊔ D = H`, then every
element of `H` is a product `q * d` with `q ∈ Q`, `d ∈ D`. -/
lemma decomp_exists {G : Type} [Group G] {H Q D : Subgroup G}
    (hQH : H ≤ Subgroup.normalizer (Q : Set G)) (hsup : Q ⊔ D = H) :
    ∀ h ∈ H, ∃ q ∈ Q, ∃ d ∈ D, h = q * d := by
  intro h hhH
  have hQH_le : Q ≤ H := hsup ▸ (le_sup_left : Q ≤ Q ⊔ D)
  have hDH_le : D ≤ H := hsup ▸ (le_sup_right : D ≤ Q ⊔ D)
  have hQnorm : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH_le).mpr hQH
  have hsup' : Q.subgroupOf H ⊔ D.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQH_le hDH_le, hsup]
    exact Subgroup.subgroupOf_self H
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := Q.subgroupOf H) (t := D.subgroupOf H)
      (x := (⟨h, hhH⟩ : ↥H))).mp (by rw [hsup']; exact Subgroup.mem_top _)
  refine ⟨(y : G), hy, (z : G), hz, ?_⟩
  have hval : (y : G) * (z : G) = h := by
    have := congrArg (Subtype.val) hyz
    simpa using this
  exact hval.symm

theorem lemma2a_cent_split {G : Type} [Group G] {H Q D X : Subgroup G} (hQH : H ≤ Subgroup.normalizer (Q : Set G)) (hinf : Q ⊓ D = ⊥) (hsup : Q ⊔ D = H) (hX : X ≤ D) : H ⊓ Subgroup.centralizer (X : Set G) = (Q ⊓ Subgroup.centralizer (X : Set G)) ⊔ (D ⊓ Subgroup.centralizer (X : Set G)) := by
  have hQH_le : Q ≤ H := hsup ▸ (le_sup_left : Q ≤ Q ⊔ D)
  have hDH_le : D ≤ H := hsup ▸ (le_sup_right : D ≤ Q ⊔ D)
  have hconj : ∀ q ∈ Q, ∀ d ∈ D, d * q * d⁻¹ ∈ Q := by
    intro q hq d hd
    have hdN : d ∈ Subgroup.normalizer (Q : Set G) := hQH (hDH_le hd)
    exact (Subgroup.mem_normalizer_iff.mp hdN q).mp hq
  apply le_antisymm
  · -- `H ∩ C_G(X) ≤ (Q ∩ C_G(X)) ⊔ (D ∩ C_G(X))`
    intro h hh
    simp only [Subgroup.mem_inf] at hh
    obtain ⟨hhH, hhC⟩ := hh
    obtain ⟨q, hq, d, hd, hdecomp⟩ := decomp_exists hQH hsup h hhH
    -- Both `q` and `d` commute with every `x ∈ X`.
    have hcomm : ∀ x ∈ X, x * q = q * x ∧ x * d = d * x := by
      intro x hx
      have hxD : x ∈ D := hX hx
      have hxc : x * h = h * x := (Subgroup.mem_centralizer_iff.mp hhC) x hx
      have hxy : x * (q * d) = (q * d) * x := by rw [hdecomp] at hxc; exact hxc
      have hxq : x * q = q * (d * x * d⁻¹) := by
        calc x * q = x * q * d * d⁻¹ := by group
          _ = x * (q * d) * d⁻¹ := by group
          _ = (q * d) * x * d⁻¹ := by rw [hxy]
          _ = q * (d * x * d⁻¹) := by group
      have heq : (x * q * x⁻¹) * x = q * (d * x * d⁻¹) := by
        have h1 : (x * q * x⁻¹) * x = x * q := by group
        rw [h1, hxq]
      obtain ⟨hq_eq, hx_eq⟩ :=
        mul_decomp_unique hinf (hconj q hq x hxD) hq hxD
          (D.mul_mem (D.mul_mem hd hxD) (D.inv_mem hd)) heq
      have hxq_comm : x * q = q * x := by
        have h := congrArg (fun t => t * x) hq_eq
        rw [show (x * q * x⁻¹) * x = x * q from by group] at h
        exact h
      have hxd_comm : x * d = d * x := by
        have h := congrArg (fun t => t * d) hx_eq
        rw [show (d * x * d⁻¹) * d = d * x from by group] at h
        exact h
      exact ⟨hxq_comm, hxd_comm⟩
    have hqC : q ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      exact fun x hx => (hcomm x hx).1
    have hdC : d ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      exact fun x hx => (hcomm x hx).2
    rw [hdecomp]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hq, hqC⟩)
      (Subgroup.mem_inf.mpr ⟨hd, hdC⟩)
  · -- `(Q ∩ C_G(X)) ⊔ (D ∩ C_G(X)) ≤ H ∩ C_G(X)`
    apply sup_le
    · exact le_inf (inf_le_left.trans hQH_le) inf_le_right
    · exact le_inf (inf_le_left.trans hDH_le) inf_le_right

end Work.ThmF.ChV12
