import Mathlib
import Submission.Work.Frobenius.Fpf.isNilpotent_of_fpf_prime
import Submission.Work.NPC.Fpf.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.NC4

/-!
# Ch. III §4 Prop. 2 (b): the auxiliary nilpotency of `E'`

Setting: `E' ≤ G` is a finite solvable subgroup normalised by a subgroup `P` of prime order
`p`, and `C_{E'}(P) = 1`.  Then `E'` is nilpotent.

The point is that conjugation by a non-identity element `q ∈ P` is an automorphism of `E'`.
Since `|P| = p` is prime, `P = ⟨q⟩`, so the fixed points of this automorphism are exactly
`C_{E'}(⟨q⟩) = C_{E'}(P) = 1`: the automorphism is **fixed-point-free**.  It also has order
`p`, because `q ^ p = 1`.  It therefore falls under the classical theorem of Thompson in the
solvable case, available as `Work.Frobenius.Fpf.isNilpotent_of_fpf_prime`.

The automorphism itself is the image of `q` under the conjugation homomorphism
`N_G(E') →* Aut(E')` (`Subgroup.normalizerMonoidHom`).
-/

theorem prop2b_aux_nilpotent {G : Type} [Group G] [Finite G] {E' P : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hcardP : Nat.card ↥P = p)
    (hPE' : P ≤ Subgroup.normalizer (E' : Set G))
    (hC : ∀ x ∈ E', (∀ q ∈ P, x * q = q * x) → x = 1)
    (hsolv : Group.IsSolvable ↥E') : Group.IsNilpotent ↥E' := by
  classical
  -- `P` is nontrivial, so pick `q ∈ P`, `q ≠ 1`.
  have hP_ne_bot : P ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥P = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [h1] at hcardP
    exact hp.ne_one hcardP.symm
  obtain ⟨a, ha_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP_ne_bot
  set q : G := (a : G) with hq_def
  have hq_mem : q ∈ P := hq_def ▸ a.2
  have hq_ne : q ≠ 1 := by
    intro h
    apply ha_ne
    apply Subtype.ext
    show (a : G) = 1
    rw [← hq_def]; exact h
  -- `orderOf q = p`, so `q ^ p = 1`, and `P = ⟨q⟩`.
  have hord_dvd : orderOf q ∣ p := by
    have h := Subgroup.orderOf_dvd_natCard P hq_mem
    rwa [hcardP] at h
  have hord : orderOf q = p := by
    rcases (Nat.dvd_prime hp).mp hord_dvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hq_ne
    · exact h
  have hq_pow : q ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one q
  have hsub : Subgroup.zpowers q ≤ P := Subgroup.zpowers_le.mpr hq_mem
  have hgen : Subgroup.zpowers q = P := by
    apply Subgroup.eq_of_le_of_card_ge hsub
    simp [Nat.card_zpowers, hord, hcardP]
  -- The conjugation automorphism of `E'` induced by `q ∈ N_G(E')`.
  let g : Subgroup.normalizer (E' : Set G) := ⟨q, hPE' hq_mem⟩
  let α : MulAut ↥E' := Subgroup.normalizerMonoidHom E' g
  have hα_apply : ∀ x : ↥E', ((α x : ↥E') : G) = q * (x : G) * q⁻¹ := by
    intro x
    show (((Subgroup.normalizerMonoidHom E') g) x : G) = q * (x : G) * q⁻¹
    simp only [Subgroup.normalizerMonoidHom, MulDistribMulAction.toMulAut_apply,
      MulDistribMulAction.toMulEquiv_apply]
    rfl
  -- `α` is fixed-point-free: a fixed point centralises `q`, hence all of `P = ⟨q⟩`, so is `1`.
  have hfpf : Work.NPC.Fpf.IsFpf α := by
    intro x hx
    have hxG : q * (x : G) * q⁻¹ = (x : G) := by
      have h := congrArg (fun z : ↥E' => (z : G)) hx
      rwa [hα_apply x] at h
    have hcomm : Commute (x : G) q := by
      have h := congrArg (fun z : G => z * q) hxG
      simp only [mul_assoc, inv_mul_cancel, mul_one] at h
      exact h.symm
    have hcomm_all : ∀ y ∈ P, (x : G) * y = y * (x : G) := by
      intro y hy
      have hy' : y ∈ Subgroup.zpowers q := by rw [hgen]; exact hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
      rw [← hk]
      exact hcomm.zpow_right k
    exact Subtype.ext (hC (x : G) x.2 hcomm_all)
  -- `α ^ p = 1` because `q ^ p = 1`.
  have hgp : g ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, show (g : G) = q from rfl]
    exact hq_pow
  have hαp : α ^ p = 1 := by
    show (Subgroup.normalizerMonoidHom E' g) ^ p = 1
    rw [← map_pow (Subgroup.normalizerMonoidHom E') g p, hgp, map_one]
  haveI : Group.IsSolvable ↥E' := hsolv
  exact Work.Frobenius.Fpf.isNilpotent_of_fpf_prime hp hαp hfpf

end Work.NormalComplement.NC4
