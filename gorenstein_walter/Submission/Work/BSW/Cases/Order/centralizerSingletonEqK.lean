import Mathlib
import Submission.Work.BSW.Basic
import Submission.Work.BSW.Api.mem_centralizer_iff

namespace Work.BSW.Cases.Order

/-- In Bender's setting `BSWHyps2 G t s K`, the centralizer of any element `x ∈ K` other than
`1` and `t` is exactly `K`.

`K ≤ C_G(x)` because `K` is abelian and `x ∈ K`.  For the converse let `g ∈ C_G(x)`.  If
`g ∉ C_G(t)`, then `K ∩ K^g = ⊥` (the TI condition), while `x ∈ K` and `x = g x g⁻¹ ∈ K^g`;
so `x = 1`, a contradiction.  Hence `g ∈ C_G(t) = K⟨s⟩`, i.e. `g ∈ K` or `g = k s` with `k ∈ K`.
In the second case `g` centralizes `x`, so `(k s) x = x (k s)`; since `K` is abelian this reduces
to `s x = x s`, i.e. `x ∈ K ∩ C_G(s) = ⟨t⟩ = {1, t}`, again a contradiction. -/
theorem centralizerSingletonEqK {G : Type} [Group G] [Finite G] {t s x : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hxK : x ∈ K) (hx1 : x ≠ 1) (hxt : x ≠ t) :
    Subgroup.centralizer ({x} : Set G) = K := by
  have hcommK : ∀ a b : ↥K, a * b = b * a := (Work.BSW.isMulCommutative_K h).is_comm.comm
  apply le_antisymm
  · -- any `g` centralizing `x` lies in `K`
    intro g hg
    have hgx : g * x = x * g := ((Subgroup.mem_centralizer_iff.mp hg) x rfl).symm
    -- `g` must centralize `t`, else the TI condition forces `x = 1`
    have hgc : g ∈ Subgroup.centralizer ({t} : Set G) := by
      by_contra hgt
      have hTI := Work.BSW.TI h g hgt
      have hxconj : x ∈ Work.GW2.conjSub g K := by
        refine ⟨x, hxK, ?_⟩
        show g * x * g⁻¹ = x
        rw [hgx, mul_assoc, mul_inv_cancel, mul_one]
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        rw [← hTI]
        exact ⟨hxK, hxconj⟩
      exact hx1 (Subgroup.mem_bot.mp hxbot)
    -- normal form in `C_G(t) = K⟨s⟩`: either `g ∈ K`, or `g = k s` with `k ∈ K`
    rcases (Work.BSW.Api.mem_centralizer_iff h g).mp hgc with hgK | ⟨k, hkK, rfl⟩
    · exact hgK
    · exfalso
      have hkx : k * x = x * k := congrArg Subtype.val (hcommK ⟨k, hkK⟩ ⟨x, hxK⟩)
      have hcx : x * (k * s) = (k * s) * x := (Subgroup.mem_centralizer_iff.mp hg) x rfl
      have h1 : k * (x * s) = k * (s * x) := by
        calc k * (x * s) = (k * x) * s := by rw [mul_assoc]
          _ = (x * k) * s := by rw [hkx]
          _ = x * (k * s) := by rw [mul_assoc]
          _ = (k * s) * x := hcx
          _ = k * (s * x) := by rw [mul_assoc]
      have hxs : s * x = x * s := (mul_left_cancel h1).symm
      -- hence `x ∈ K ⊓ C_G(s) = ⟨t⟩ = {1, t}`
      have hxmem : x ∈ K ⊓ Subgroup.centralizer ({s} : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨hxK, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hxs
      have hzp : x ∈ Subgroup.zpowers t := by
        rw [← Work.BSW.K_inf_centralizer_s h]
        exact hxmem
      rcases Work.BSW.mem_zpowers_t h hzp with hc | hc
      · exact hx1 hc
      · exact hxt hc
  · -- `K` centralizes `x`, because `K` is abelian and `x ∈ K`
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact congrArg Subtype.val (hcommK ⟨x, hxK⟩ ⟨k, hk⟩)

end Work.BSW.Cases.Order
