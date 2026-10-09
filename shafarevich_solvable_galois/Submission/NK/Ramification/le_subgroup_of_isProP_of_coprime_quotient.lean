import Mathlib
import Submission.NK.LocalTame.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Ramification

/-- If `N ≤ G` is a pro-`p` group and `p` is coprime to the order of `G ⧸ H`, then `N ≤ H`.

Indeed the image of `N` in `G ⧸ H` is a quotient of the finite pro-`p` group `N` (hence has
`p`-power order), while its order divides `|G ⧸ H|`, which is prime to `p`; so the image is
trivial and `N` lies in the kernel `H` of the quotient map. -/
theorem le_subgroup_of_isProP_of_coprime_quotient {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (H N : Subgroup G) [H.Normal] [N.Normal]
    (hN : NK.LocalTame.IsProP p ↥N) (hH : Nat.Coprime p (Nat.card (G ⧸ H))) :
    N ≤ H := by
  have _ : p ≠ 1 := hp.ne_one
  let φ : G →* G ⧸ H := QuotientGroup.mk' H
  let ψ : ↥N →* G ⧸ H := φ.comp N.subtype
  -- `ψ.ker` has finite index in the finite group `↥N`
  have hfi : ψ.ker.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    exact Subgroup.index_ne_zero_of_finite
  -- pro-`p`-ness of `↥N` forces the index of the kernel `ψ.ker` to be a power of `p`
  obtain ⟨k, hk⟩ := hN ψ.ker hfi
  -- the index of the kernel is the order of the image
  have hcard : Nat.card ↥(ψ.range) = p ^ k := by
    rw [← Subgroup.index_ker ψ, hk]
  -- the image is a subgroup of `G ⧸ H`, so its order divides `|G ⧸ H|`
  have hdvd : Nat.card ↥(ψ.range) ∣ Nat.card (G ⧸ H) := Subgroup.card_subgroup_dvd_card _
  rw [hcard] at hdvd
  -- a power of `p` dividing a number coprime to `p` must be `1`
  have hcop : (p ^ k).Coprime (Nat.card (G ⧸ H)) := hH.pow_left k
  have hp1 : p ^ k = 1 := hcop.eq_one_of_dvd hdvd
  -- hence the kernel is everything, i.e. `N` maps trivially into `G ⧸ H`
  have htop : ψ.ker = ⊤ := Subgroup.index_eq_one.mp (by rw [hk, hp1])
  intro x hx
  rw [← QuotientGroup.ker_mk' H, MonoidHom.mem_ker]
  have hx' : (⟨x, hx⟩ : ↥N) ∈ ψ.ker := htop ▸ Subgroup.mem_top _
  rw [MonoidHom.mem_ker] at hx'
  exact hx'

end NK.Ramification
