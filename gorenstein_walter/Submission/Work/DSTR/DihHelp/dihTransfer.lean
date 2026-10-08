import Mathlib
import Submission.Work.DSTR.Defs

namespace Work.DSTR.DihHelp

/-- A cyclic group all of whose elements square to `1` has at most two elements.  (No finiteness
hypothesis: an infinite cyclic group would have an element of infinite order.) -/
lemma dihTransfer_cyclicOfExpTwo {G : Type*} [Group G] (hcyc : IsCyclic G)
    (h2 : ∀ g : G, g ^ 2 = 1) : Nat.card G ≤ 2 := by
  obtain ⟨g, htop⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  have horder : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (h2 g)
  calc Nat.card G = Nat.card ↥(⊤ : Subgroup G) :=
        (Nat.card_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G)).symm
    _ = Nat.card ↥(Subgroup.zpowers g) :=
        (congrArg (fun H : Subgroup G => Nat.card ↥H) htop).symm
    _ = orderOf g := Nat.card_zpowers g
    _ ≤ 2 := Nat.le_of_dvd (by norm_num) horder

/-- If `E ≤ Q` are subgroups of a group `X`, `Q` is dihedral (via an isomorphism
`e : ↥Q ≃* DihedralGroup n`), and `E` is commutative with every element squaring to `1`, then
`|E| ≤ 4`, by transporting `E` into `DihedralGroup n` and applying the rank input
`DihedralAbelianRankProp`. -/
lemma dihTransfer (hDR : Work.GW2.DihedralAbelianRankProp) {X : Type} [Group X]
    {E Q : Subgroup X} {n : ℕ} (e : ↥Q ≃* DihedralGroup n) (hle : E ≤ Q)
    (hcomm : IsMulCommutative ↥E) (h2 : ∀ x : ↥E, x ^ 2 = 1) : Nat.card ↥E ≤ 4 := by
  -- Transport `E` into `DihedralGroup n` along the isomorphism `e` restricted to `E ≤ Q`.
  let f : ↥E →* DihedralGroup n := e.toMonoidHom.comp (Subgroup.inclusion hle)
  have hf_inj : Function.Injective f := e.injective.comp (Subgroup.inclusion_injective hle)
  -- The image `A = f(E) ≤ DihedralGroup n` is abelian with all elements squaring to `1`.
  have hcommA : IsMulCommutative ↥f.range := by
    rw [isMulCommutative_iff]
    intro x y
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp y.2
    apply Subtype.ext
    show (x : DihedralGroup n) * (y : DihedralGroup n) =
      (y : DihedralGroup n) * (x : DihedralGroup n)
    rw [← ha, ← hb, ← map_mul, ← map_mul, hcomm.is_comm.comm a b]
  have h2A : ∀ x : ↥f.range, x ^ 2 = 1 := by
    intro x
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← ha, ← map_pow, h2 a, map_one]
  -- `↥E` and `↥f.range` have the same cardinality.
  have hcard : Nat.card ↥E = Nat.card ↥f.range :=
    Nat.card_congr (MulEquiv.ofBijective f.rangeRestrict
      ⟨by
        intro a b hab
        apply hf_inj
        have h := congrArg Subtype.val hab
        rwa [MonoidHom.coe_rangeRestrict f a, MonoidHom.coe_rangeRestrict f b] at h,
       f.rangeRestrict_surjective⟩)
  rcases hDR n f.range hcommA with hcyc | hle4
  · have hsmall : Nat.card ↥f.range ≤ 2 := dihTransfer_cyclicOfExpTwo hcyc h2A
    calc Nat.card ↥E = Nat.card ↥f.range := hcard
      _ ≤ 2 := hsmall
      _ ≤ 4 := by norm_num
  · rwa [hcard]

end Work.DSTR.DihHelp
