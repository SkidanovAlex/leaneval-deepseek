import Mathlib

namespace Work.CORE4

/-- If `H = U ⊔ S` with `U ⊓ S = ⊥` and `U` normal in `H`, and `s ∈ S`, then the centralizer of
`s` in `H` decomposes as the product of `C_U(s)` and `C_S(s)`.

(`U` is only assumed normal in `H`, not in the ambient group `G`; so the elementwise argument has
to be run inside `↥H`, using `Subgroup.mem_sup_of_normal_left` in the group `↥H` on the subgroups
`U.subgroupOf H`, `S.subgroupOf H`.  Key step: writing `x = u * v` with `u ∈ U`, `v ∈ S`, and
`x s x⁻¹ = s` gives `u * (v s v⁻¹) * u⁻¹ = s`; then `v s v⁻¹ ∈ S` and
`v s v⁻¹ = u⁻¹ s u ∈ sU` (as `U ⊴ H`), so `v s v⁻¹ = s` because `S ⊓ sU = {s}` by `U ⊓ S = ⊥`.
This gives `v ∈ C` and then `u ∈ C` as well, whence `x ∈ (U ⊓ C) ⊔ (S ⊓ C)`.) -/
theorem CentralizerInfEqSup {G : Type} [Group G] (U S H : Subgroup G)
    (hH : H = U ⊔ S) (hUS : U ⊓ S = ⊥) (hnorm : (U.subgroupOf H).Normal) (s : G) (hs : s ∈ S) :
    H ⊓ Subgroup.centralizer ({s} : Set G) =
      (U ⊓ Subgroup.centralizer ({s} : Set G)) ⊔
        (S ⊓ Subgroup.centralizer ({s} : Set G)) := by
  set C := Subgroup.centralizer ({s} : Set G) with hC
  have hUH : U ≤ H := le_sup_left.trans hH.symm.le
  have hSH : S ≤ H := le_sup_right.trans hH.symm.le
  have hsH : s ∈ H := hSH hs
  have hnormI : (U.subgroupOf H).Normal := hnorm
  -- `U` normal in `H` is exactly the conjugation statement needed below.
  have hnorm' : ∀ h k : G, h ∈ U → k ∈ H → k * h * k⁻¹ ∈ U :=
    (Subgroup.normal_subgroupOf_iff hUH).mp hnorm
  refine le_antisymm ?_ ?_
  · -- Hard direction: an element of `H` centralizing `s` lies in the product.
    intro x hx
    obtain ⟨hxH, hxC⟩ := hx
    have hxcent : x ∈ Subgroup.centralizer ({s} : Set G) := hC ▸ hxC
    have hxs : s * x = x * s := (Subgroup.mem_centralizer_iff.mp hxcent) s (Set.mem_singleton s)
    -- Decompose `x = u * v` with `u ∈ U`, `v ∈ S`, using normality of `U` inside `↥H`.
    have hxU : (⟨x, hxH⟩ : H) ∈ U.subgroupOf H ⊔ S.subgroupOf H := by
      rw [← Subgroup.subgroupOf_sup hUH hSH, Subgroup.mem_subgroupOf]
      simpa using (hH ▸ hxH)
    obtain ⟨u, hu, v, hv, huv⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := U.subgroupOf H) (t := S.subgroupOf H)).mp hxU
    set uG : G := (u : G) with huGdef
    set vG : G := (v : G) with hvGdef
    have huU : uG ∈ U := hu
    have hvS : vG ∈ S := hv
    have huv' : uG * vG = x := by
      have := congrArg Subtype.val huv
      simpa [uG, vG] using this
    -- The key commutator identity: `v * s * v⁻¹ = u⁻¹ * s * u`.
    have hkey : vG * s * vG⁻¹ = uG⁻¹ * s * uG := by
      have h' := congrArg (fun t => uG⁻¹ * t * vG⁻¹) hxs
      rw [← huv'] at h'
      have h1 : uG⁻¹ * (s * (uG * vG)) * vG⁻¹ = uG⁻¹ * s * uG := by group
      have h2 : uG⁻¹ * ((uG * vG) * s) * vG⁻¹ = vG * s * vG⁻¹ := by group
      rw [h1, h2] at h'
      exact h'.symm
    -- Write `u⁻¹ * s * u = s * w` with `w ∈ U`.
    have hwU : s⁻¹ * uG⁻¹ * s * uG ∈ U := by
      have h1 : s⁻¹ * uG⁻¹ * s ∈ U := by
        have := hnorm' uG⁻¹ s⁻¹ (inv_mem huU) (inv_mem hsH)
        simpa using this
      exact mul_mem h1 huU
    have hsw : uG⁻¹ * s * uG = s * (s⁻¹ * uG⁻¹ * s * uG) := by group
    -- The left side `v * s * v⁻¹` lies in `S`, so `s * w ∈ S`, hence `w ∈ S`, hence `w = 1`.
    have hLHS : vG * s * vG⁻¹ ∈ S := mul_mem (mul_mem hvS hs) (inv_mem hvS)
    have hswS : s * (s⁻¹ * uG⁻¹ * s * uG) ∈ S := by rw [← hsw, ← hkey]; exact hLHS
    have hwS : s⁻¹ * uG⁻¹ * s * uG ∈ S := by
      have hmem : s⁻¹ * (s * (s⁻¹ * uG⁻¹ * s * uG)) ∈ S := mul_mem (inv_mem hs) hswS
      simpa [mul_assoc] using hmem
    have hw1 : s⁻¹ * uG⁻¹ * s * uG = 1 := by
      have : s⁻¹ * uG⁻¹ * s * uG ∈ (⊥ : Subgroup G) := by
        rw [← hUS]; exact ⟨hwU, hwS⟩
      simpa using this
    -- Hence both `u` and `v` centralize `s`.
    have hu_h : uG⁻¹ * s * uG = s := by rw [hsw, hw1, mul_one]
    have hconjU' : uG * s * uG⁻¹ = s := by
      have h' := congrArg (fun t => uG * t * uG⁻¹) hu_h
      have h3 : uG * (uG⁻¹ * s * uG) * uG⁻¹ = s := by group
      rw [h3] at h'
      exact h'.symm
    have hu_comm : uG * s = s * uG := by
      have := congrArg (fun t => t * uG) hconjU'
      simpa [mul_assoc] using this
    have hconjV' : vG * s * vG⁻¹ = s := by rw [hkey, hsw, hw1, mul_one]
    have hv_comm : vG * s = s * vG := by
      have := congrArg (fun t => t * vG) hconjV'
      simpa [mul_assoc] using this
    have huC : uG ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hu_comm.symm
    have hvC : vG ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hv_comm.symm
    rw [← huv']
    exact mul_mem (Subgroup.mem_sup_left (show uG ∈ U ⊓ C from ⟨huU, huC⟩))
      (Subgroup.mem_sup_right (show vG ∈ S ⊓ C from ⟨hvS, hvC⟩))
  · -- Easy direction: both factors lie in `H ⊓ C`.
    exact sup_le (le_inf (inf_le_left.trans hUH) inf_le_right)
      (le_inf (inf_le_left.trans hSH) inf_le_right)

end Work.CORE4
