import Mathlib
import Submission.Work.RED.Basic

/-!
# RED: `C_G(N) ∩ P = N` for a normal four-subgroup `N` and a dihedral Sylow 2-subgroup `P`

Let `N ⊴ G` be a Klein four-group and let `P` be a Sylow 2-subgroup of `G` isomorphic to
`DihedralGroup n`, `n ≥ 2`.  Then `C_G(N) ∩ P = N`.

The mathematics is short:

* `N` is a `2`-group, so by Sylow's theorem `N ≤ P` (a normal `p`-subgroup lies in every
  Sylow `p`-subgroup).
* `N` is abelian (every element of a Klein four-group is an involution), so `N ≤ C_G(N)`.
* Conversely, transporting along the isomorphism `e : ↥P ≃* DihedralGroup n`, an element
  `x ∈ P` centralizing `N` corresponds to an element of `DihedralGroup n` centralizing the
  (normal, four-group) image of `N`.  The dihedral fact
  `DihedralFactsProp.normal_fourGroup_centralizer` -- a normal four-subgroup of a dihedral
  group is self-centralizing -- then forces `e x` to lie in the image of `N`, i.e. `x ∈ N`.

The only input beyond elementary group theory is the dihedral self-centralizing fact, which
is packaged in `Work.RED.GW2.DihedralFactsProp`.
-/

namespace Work.RED

/-- Products of two involutions that are again involutions commute: in a group, if
`x ^ 2 = 1`, `y ^ 2 = 1` and `(x * y) ^ 2 = 1` then `x * y = y * x`. -/
theorem mul_comm_of_sq_eq_one {G : Type*} [Group G] {x y : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hxy : (x * y) ^ 2 = 1) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hy)
  have h1 : x * y = (x * y)⁻¹ := by
    have h2 : (x * y) * (x * y) = 1 := by simpa [pow_two] using hxy
    exact (inv_eq_of_mul_eq_one_left h2).symm
  rw [h1, mul_inv_rev, hx', hy']

/-- A four-group is abelian: every element centralizes every other. -/
theorem le_centralizer_self_of_isFourGroup {G : Type*} [Group G] {V : Subgroup G}
    (h : Work.RED.GW2.IsFourGroup V) :
    V ≤ Subgroup.centralizer (V : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (mul_comm_of_sq_eq_one (h.2 x hx) (h.2 y hy) (h.2 (x * y) (V.mul_mem hx hy))).symm

/-- `N` is a normal four-subgroup of `G`, `P` a Sylow `2`-subgroup.  Then the elements of
`P` centralizing `N` are exactly the elements of `N`. -/
theorem centralizer_inf_sylow_eq
    (hdi : Work.RED.GW2.DihedralFactsProp)
    {G : Type*} [Group G] [Finite G] {N : Subgroup G} (hNn : N.Normal)
    (hN4 : Work.RED.GW2.IsFourGroup N)
    {n : ℕ} [NeZero n] {P : Sylow 2 G} (e : ↥(P : Subgroup G) ≃* DihedralGroup n) (hn : 2 ≤ n) :
    Subgroup.centralizer (N : Set G) ⊓ (P : Subgroup G) = N := by
  have hNnI : N.Normal := hNn
  -- `N` is a normal `2`-subgroup, hence contained in every Sylow `2`-subgroup.
  have hNP : N ≤ (P : Subgroup G) := IsPGroup.le_sylow_of_normal hN4.isPGroup_two P
  refine le_antisymm ?_ ?_
  · -- The interesting direction: `C_G(N) ∩ P ≤ N`.
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxcen, hxP⟩ := hx
    -- The image `M` of `N` inside the dihedral group `DihedralGroup n`.
    have hM4 : Work.RED.GW2.IsFourGroup ((N.subgroupOf (P : Subgroup G)).map e.toMonoidHom) := by
      rw [Work.RED.GW2.isFourGroup_map_iff]
      refine ⟨?_, ?_⟩
      · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv).trans hN4.1
      · intro v hv
        have hvN : (v : G) ∈ N := Subgroup.mem_subgroupOf.mp hv
        have hv2 : (v : G) ^ 2 = 1 := hN4.2 (v : G) hvN
        exact Subtype.ext (by simpa [Subgroup.coe_pow] using hv2)
    have hMn : ((N.subgroupOf (P : Subgroup G)).map e.toMonoidHom).Normal :=
      Subgroup.Normal.map (hNn.subgroupOf (P : Subgroup G)) e.toMonoidHom e.surjective
    -- The dihedral self-centralizing fact, transported along `e`.
    have hcen : Subgroup.centralizer
        (((N.subgroupOf (P : Subgroup G)).map e.toMonoidHom :
          Subgroup (DihedralGroup n)) : Set (DihedralGroup n))
        = (N.subgroupOf (P : Subgroup G)).map e.toMonoidHom :=
      hdi.normal_fourGroup_centralizer n _ hMn hM4
    -- `e x` centralizes the image of `N`.
    have hxmem : e ⟨x, hxP⟩ ∈ Subgroup.centralizer
        (((N.subgroupOf (P : Subgroup G)).map e.toMonoidHom :
          Subgroup (DihedralGroup n)) : Set (DihedralGroup n)) := by
      rw [Work.RED.GW2.mem_centralizer_map_iff]
      intro v hv
      have hvN : (v : G) ∈ N := Subgroup.mem_subgroupOf.mp hv
      have hcomm : (⟨x, hxP⟩ : ↥(P : Subgroup G)) * v = v * ⟨x, hxP⟩ := by
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp hxcen (v : G) hvN).symm
      calc e ⟨x, hxP⟩ * e v = e (⟨x, hxP⟩ * v) := (map_mul e _ _).symm
        _ = e (v * ⟨x, hxP⟩) := by rw [hcomm]
        _ = e v * e ⟨x, hxP⟩ := map_mul e _ _
    rw [hcen] at hxmem
    obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp hxmem
    have hwx : w = ⟨x, hxP⟩ := e.injective hwe
    have hwN : (w : G) ∈ N := Subgroup.mem_subgroupOf.mp hw
    rw [hwx] at hwN
    exact hwN
  · -- The easy direction: `N ≤ C_G(N) ∩ P`.
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨le_centralizer_self_of_isFourGroup hN4 hx, hNP hx⟩

end Work.RED
