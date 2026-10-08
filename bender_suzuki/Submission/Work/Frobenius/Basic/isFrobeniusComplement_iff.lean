import Mathlib
import Submission.Work.Frobenius.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Frobenius complements and fixed-point-free action on the kernel

Let `K, H ≤ G` with `K` normal, `K ⊓ H = ⊥`, `K ⊔ H = ⊤`, and `H, K ≠ ⊥`.  Then `H` is a
Frobenius complement in `G` (i.e. `H ∩ H^g = 1` for every `g ∉ H`, with `H` nontrivial and
proper) if and only if `H` acts fixed-point-freely on `K` by conjugation, i.e.
`C_K(h) = 1` for every `h ∈ H`, `h ≠ 1`.

Both directions use `G = K ⋊ H`: every `g ∉ H` can be written `g = k h` with `1 ≠ k ∈ K`,
`h ∈ H`, and `H^g = H^k` because `h ∈ H` normalizes `H`.  The `K ≠ ⊥` hypothesis is what
rules out `H = ⊤`.
-/

namespace Work.Frobenius.Basic

open scoped Pointwise

/-- Core computation for the "fixed point free ⟹ Frobenius complement" direction: if
`1 ≠ k ∈ K` and `x ∈ H` is a nontrivial element of `H` which conjugates `k` into `H`
(`k⁻¹ x k ∈ H`), then the fixed-point-freeness of the `H`-action on `K` is contradicted.
Concretely it forces `x k x⁻¹ = k`. -/
theorem eq_one_of_mem_complement_of_conj_mem {G : Type*} [Group G] {K H : Subgroup G}
    (hK : K.Normal) (hinf : K ⊓ H = ⊥) {k x : G} (hk : k ∈ K) (hk1 : k ≠ 1)
    (hx : x ∈ H) (hkx : k⁻¹ * x * k ∈ H)
    (fpf : IsFixedPointFreeOn K H) : x = 1 := by
  by_contra hx1
  -- `w := k⁻¹ * x * k` lies in `H`, and `x * k * x⁻¹` lies in `K`; their quotient is
  -- `w * x⁻¹`, which therefore lies in `K ⊓ H = ⊥` and is trivial.
  have hmem : (k⁻¹ * x * k) * x⁻¹ ∈ K ⊓ H := by
    refine Subgroup.mem_inf.mpr ⟨?_, H.mul_mem hkx (H.inv_mem hx)⟩
    have hrel : k⁻¹ * (x * k * x⁻¹) = (k⁻¹ * x * k) * x⁻¹ := by group
    rw [← hrel]
    exact K.mul_mem (K.inv_mem hk) (hK.conj_mem k hk x)
  rw [hinf] at hmem
  have h1 : (k⁻¹ * x * k) * x⁻¹ = 1 := Subgroup.mem_bot.mp hmem
  have hweq : k⁻¹ * x * k = x := by
    have h1' : (k⁻¹ * x * k) * x⁻¹ = x * x⁻¹ := by rw [h1, mul_inv_cancel]
    exact mul_right_cancel h1'
  -- hence `x` commutes with `k`, giving a nontrivial fixed point of `x` on `K`
  have h3 : x * k = k * x := by
    calc x * k = k * (k⁻¹ * x * k) := by group
      _ = k * x := by rw [hweq]
  exact hk1 (fpf hx hx1 hk (by rw [h3]; group))

/-- Elements of two subgroups whose product is the whole group: if `K` is normal,
`K ⊓ H = ⊥`, `K ⊔ H = ⊤` then every `g ∈ G` is `k * h` with `k ∈ K`, `h ∈ H`. -/
theorem exists_mul_of_mem_sup_eq_top {G : Type*} [Group G] {K H : Subgroup G} (hK : K.Normal)
    (hsup : K ⊔ H = ⊤) (g : G) : ∃ k ∈ K, ∃ h ∈ H, k * h = g := by
  have : K.Normal := hK
  exact (Subgroup.mem_sup_of_normal_left (s := K) (t := H)).mp (by rw [hsup]; trivial)

theorem isFrobeniusComplement_iff {G : Type*} [Group G] {K H : Subgroup G} (hK : K.Normal)
    (hinf : K ⊓ H = ⊥) (hsup : K ⊔ H = ⊤) (hHne : H ≠ ⊥) (hKne : K ≠ ⊥) :
    IsFrobeniusComplement H ↔ IsFixedPointFreeOn K H := by
  constructor
  · -- a Frobenius complement acts fixed-point-freely on the kernel
    intro hH h hh hh1 k hk hcomm
    by_contra hk1
    -- `k⁻¹` is not in `H`, since `K ⊓ H = ⊥`
    have hkinv : k⁻¹ ∉ H := by
      intro hmem
      have hbot : k⁻¹ ∈ (⊥ : Subgroup G) := by
        have h2 : k⁻¹ ∈ K ⊓ H := Subgroup.mem_inf.mpr ⟨K.inv_mem hk, hmem⟩
        rwa [hinf] at h2
      exact hk1 (inv_eq_one.mp (Subgroup.mem_bot.mp hbot))
    -- from `h k h⁻¹ = k` we get `k h k⁻¹ = h`, so `h ∈ H ∩ H^{k⁻¹}`
    have hconj : k * h * k⁻¹ = h := by
      have h2 : k * h = h * k := by
        calc k * h = (h * k * h⁻¹) * h := by rw [hcomm]
          _ = h * k := by group
      rw [h2]; group
    have hmem : h ∈ H ⊓ (MulAut.conj k⁻¹ • H) := by
      refine Subgroup.mem_inf.mpr ⟨hh, ?_⟩
      rw [mem_conj_smul_iff]
      simpa [inv_inv, hconj] using hh
    have hti : H ⊓ (MulAut.conj k⁻¹ • H) = ⊥ := hH.ti k⁻¹ hkinv
    rw [hti] at hmem
    exact hh1 (Subgroup.mem_bot.mp hmem)
  · -- fixed-point-freeness makes `H` a Frobenius complement
    intro fpf
    refine ⟨hHne, ?_, ?_⟩
    · -- `H` is proper because `K ≠ ⊥` and `K ≤ H` would force `K ≤ K ⊓ H = ⊥`
      intro htop
      apply hKne
      refine le_antisymm ?_ bot_le
      intro x hx
      have h2 : x ∈ (⊥ : Subgroup G) := by
        have h3 : x ∈ K ⊓ H := Subgroup.mem_inf.mpr ⟨hx, by rw [htop]; trivial⟩
        rwa [hinf] at h3
      exact h2
    · intro g hg
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxH, hxconj⟩ := hx
      rw [mem_conj_smul_iff] at hxconj
      -- write `g = k * h'` with `1 ≠ k ∈ K`, `h' ∈ H`; then `g ∉ H` means `k ≠ 1`
      obtain ⟨k, hk, h', hh', hkh⟩ := exists_mul_of_mem_sup_eq_top hK hsup g
      have hk1 : k ≠ 1 := by
        rintro rfl
        exact hg (by rw [← hkh]; simpa using hh')
      -- `k⁻¹ x k ∈ H` because `g⁻¹ x g ∈ H`
      have hkx : k⁻¹ * x * k ∈ H := by
        have heq : k⁻¹ * x * k = h' * (g⁻¹ * x * g) * h'⁻¹ := by rw [← hkh]; group
        rw [heq]
        exact H.mul_mem (H.mul_mem hh' hxconj) (H.inv_mem hh')
      exact eq_one_of_mem_complement_of_conj_mem hK hinf hk hk1 hxH hkx fpf

end Work.Frobenius.Basic
