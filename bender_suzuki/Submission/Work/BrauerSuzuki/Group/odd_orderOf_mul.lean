import Mathlib
import Submission.Work.BrauerSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The product of two involutions has odd order when all Sylow `2`-subgroups have a unique
involution

`Work.BrauerSuzuki.Group.odd_orderOf_mul` is the elementary group-theoretic fact that in a
finite group `G` whose Sylow `2`-subgroups each contain exactly one involution, the product of
any two involutions has odd order.

The proof is the classical one.  Let `u`, `v` be involutions and set `g = u * v`,
`m = orderOf g`.  Suppose `m` is even (`m ≠ 0` as `G` is finite).  Then
`w = g ^ (m / 2)` has order `2`, and `u * g * u⁻¹ = g⁻¹`, `v * g * v⁻¹ = g⁻¹`
(because `u (u v) u⁻¹ = v u = (u v)⁻¹`, and likewise for `v`).  Conjugation by `u` therefore
inverts `g`, hence inverts the power `w`; as `w` is an involution this says that `u` commutes
with `w`, and symmetrically `v` commutes with `w`.  Two commuting involutions generate the
subgroup `{1, x, y, x y}`, a `2`-group, which lies in some Sylow `2`-subgroup `T`; as `T` has a
unique involution this forces `u = w` and `v = w`, whence `u = v` and `m = orderOf 1 = 1`,
contradicting that `m` is even.

The only ingredient not already in Mathlib is the elementary fact that two commuting
involutions generate a `2`-group (`isPGroup_closure_pair_of_commute` below), together with the
order computation `orderOf (g ^ (orderOf g / 2)) = 2` for `g` of even order
(`orderOf_pow_div_two`).
-/

namespace Work.BrauerSuzuki.Group

/-- **Two commuting involutions generate a `2`-group.**

Every element of `Subgroup.closure {x, y}` is a product of copies of the commuting involutions
`x`, `y`, hence squares to `1`; so the subgroup has exponent `2`, in particular it is a
`2`-group.  (It is the Klein four-group `{1, x, y, x y}` when `x ≠ y`, and `{1, x}` when
`x = y`.) -/
theorem isPGroup_closure_pair_of_commute {G : Type*} [Group G] {x y : G}
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x) :
    IsPGroup 2 (Subgroup.closure ({x, y} : Set G)) := by
  have hx2 : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    simpa [pow_two] using h
  have hy2 : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy] at h
    simpa [pow_two] using h
  -- all elements of the closure commute with one another
  have hcomm : ∀ z w : G, z ∈ Subgroup.closure ({x, y} : Set G) →
      w ∈ Subgroup.closure ({x, y} : Set G) → Commute z w := by
    intro z w hz hw
    refine Subgroup.closure_induction₂ (p := fun a b _ _ => Commute a b) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz hw
    · intro a b ha hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with h1 | h1 <;> rcases hb with h2 | h2
      · rw [h1, h2]
      · rw [h1, h2]; exact hxy
      · rw [h1, h2]; exact hxy.symm
      · rw [h1, h2]
    · intro a _; exact Commute.one_left a
    · intro a _; exact Commute.one_right a
    · intro a b c _ _ _ hab hbc; exact Commute.mul_left hab hbc
    · intro b c a _ _ _ hab hac; exact Commute.mul_right hab hac
    · intro a b _ _ hab; exact Commute.inv_left hab
    · intro a b _ _ hab; exact Commute.inv_right hab
  have hsq : ∀ z ∈ Subgroup.closure ({x, y} : Set G), z * z = 1 := by
    intro z hz
    refine Subgroup.closure_induction (p := fun g _ => g * g = 1) ?_ ?_ ?_ ?_ hz
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with h1 | h1
      · rw [h1]; exact hx2
      · rw [h1]; exact hy2
    · exact one_mul 1
    · intro a b ha hb haa hbb
      have hab : Commute a b := hcomm a b ha hb
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab.eq]
        _ = a * a * (b * b) := by group
        _ = 1 := by rw [haa, hbb, one_mul]
    · intro a ha haa
      rw [inv_eq_of_mul_eq_one_left haa, haa]
  rw [isPGroup_iff_pow_pow_eq_one]
  intro z
  refine ⟨1, ?_⟩
  rw [pow_one]
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
  exact hsq z z.2

/-- **Two commuting involutions are equal when every Sylow `2`-subgroup has a unique
involution.**

By `isPGroup_closure_pair_of_commute` the two involutions generate a `2`-subgroup, which lies in
a Sylow `2`-subgroup `T`; the images of `x` and `y` in `↥T` are both involutions, so uniqueness
forces them to be equal, hence `x = y`. -/
theorem eq_of_commute_of_unique_sylow {G : Type*} [Group G] [Finite G]
    (h : ∀ T : Sylow 2 G, Work.BrauerSuzuki.HasUniqueInvolution ↥T)
    {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x) : x = y := by
  by_contra hne
  have hP : IsPGroup 2 (Subgroup.closure ({x, y} : Set G)) :=
    isPGroup_closure_pair_of_commute hx hy hxy
  obtain ⟨T, hT⟩ := hP.exists_le_sylow
  have hxT : x ∈ T := hT (Subgroup.subset_closure (by simp))
  have hyT : y ∈ T := hT (Subgroup.subset_closure (by simp))
  obtain ⟨z, _hz2, hzuniq⟩ := h T
  have h1 : (⟨x, hxT⟩ : ↥T) = z := hzuniq ⟨x, hxT⟩ (by rw [Subgroup.orderOf_mk]; exact hx)
  have h2 : (⟨y, hyT⟩ : ↥T) = z := hzuniq ⟨y, hyT⟩ (by rw [Subgroup.orderOf_mk]; exact hy)
  exact hne (congrArg Subtype.val (h1.trans h2.symm))

/-- **The order of `z ^ (m / 2)`** when `orderOf z = m` is even and nonzero: it is `2`.

Indeed `orderOf (z ^ k) = m / gcd (m, k)` (Mathlib's `orderOf_pow`) and `gcd (m, m / 2) = m / 2`
because `m / 2 ∣ m` (as `m = 2 * (m / 2)`), so the order is `m / (m / 2) = 2`. -/
theorem orderOf_pow_div_two {G : Type*} [Group G] [Finite G] {z : G} {m : ℕ}
    (hm : Even m) (hm0 : m ≠ 0) (hz : orderOf z = m) : orderOf (z ^ (m / 2)) = 2 := by
  rw [orderOf_pow, hz]
  have hdvd : m / 2 ∣ m := ⟨2, by rw [mul_comm, Nat.two_mul_div_two_of_even hm]⟩
  rw [Nat.gcd_eq_right hdvd]
  have hpos : 0 < m / 2 := by
    by_contra hcon
    have hz0 : m / 2 = 0 := Nat.eq_zero_of_not_pos hcon
    exact hm0 (by rw [← Nat.two_mul_div_two_of_even hm, hz0, mul_zero])
  exact Nat.div_eq_of_eq_mul_left hpos (Nat.two_mul_div_two_of_even hm).symm

/-- **The product of two involutions has odd order** in a finite group all of whose Sylow
`2`-subgroups have a unique involution.  (This is the hypothesis `2`-rank `≤ 1`, in the form in
which it is used to rule out four-groups generated by two involutions.) -/
theorem odd_orderOf_mul {G : Type*} [Group G] [Finite G]
    (h : ∀ T : Sylow 2 G, Work.BrauerSuzuki.HasUniqueInvolution ↥T)
    {u v : G} (hu : orderOf u = 2) (hv : orderOf v = 2) : Odd (orderOf (u * v)) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  have hu2 : u * u = 1 := by
    have hh := pow_orderOf_eq_one u; rw [hu] at hh; simpa [pow_two] using hh
  have hv2 : v * v = 1 := by
    have hh := pow_orderOf_eq_one v; rw [hv] at hh; simpa [pow_two] using hh
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv2
  -- the order of `u * v` is nonzero, `G` being finite
  have hm0 : orderOf (u * v) ≠ 0 := by
    have hpos : 0 < Nat.card G := Nat.card_pos
    exact ne_of_gt (Nat.pos_of_dvd_of_pos (orderOf_dvd_natCard (u * v)) hpos)
  -- `w` is the involution of the cyclic group `⟨u * v⟩`
  let w : G := (u * v) ^ (orderOf (u * v) / 2)
  have hw2 : orderOf w = 2 := by
    show orderOf ((u * v) ^ (orderOf (u * v) / 2)) = 2
    exact orderOf_pow_div_two heven hm0 rfl
  have hww : w * w = 1 := by
    rw [← pow_two, ← hw2]; exact pow_orderOf_eq_one w
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_left hww
  -- conjugation by `u` (resp. `v`) inverts `u * v`
  have huzu : u * (u * v) * u⁻¹ = (u * v)⁻¹ := by
    rw [mul_inv_rev, huinv, hvinv]
    calc u * (u * v) * u = u * u * (v * u) := by group
      _ = v * u := by rw [hu2, one_mul]
  have hvzv : v * (u * v) * v⁻¹ = (u * v)⁻¹ := by
    rw [mul_inv_rev, huinv, hvinv]
    calc v * (u * v) * v = v * u * (v * v) := by group
      _ = v * u := by rw [hv2, mul_one]
  -- hence conjugation by `u` (resp. `v`) fixes `w`, as `w` is an involution
  have hconv : ∀ c : G, c * (u * v) * c⁻¹ = (u * v)⁻¹ → c * w * c⁻¹ = w := by
    intro c hc
    have hcz : MulAut.conj c (u * v) = (u * v)⁻¹ := by rw [MulAut.conj_apply]; exact hc
    have hh : MulAut.conj c w = w⁻¹ := by
      show MulAut.conj c ((u * v) ^ (orderOf (u * v) / 2)) = w⁻¹
      rw [map_pow, hcz, inv_pow]
    have hh' : c * w * c⁻¹ = w⁻¹ := by simpa [MulAut.conj_apply] using hh
    rwa [hwinv] at hh'
  have huw : Commute u w := by
    have h1 : u * w * u⁻¹ = w := hconv u huzu
    rw [Commute]
    calc u * w = u * w * u⁻¹ * u := by group
      _ = w * u := by rw [h1]
  have hvw : Commute v w := by
    have h1 : v * w * v⁻¹ = w := hconv v hvzv
    rw [Commute]
    calc v * w = v * w * v⁻¹ * v := by group
      _ = w * v := by rw [h1]
  -- uniqueness of the involution of a Sylow `2`-subgroup forces `u = w = v`
  have h1 : u = w := eq_of_commute_of_unique_sylow h hu hw2 huw.eq
  have h2 : v = w := eq_of_commute_of_unique_sylow h hv hw2 hvw.eq
  have huv : u = v := h1.trans h2.symm
  have hone : u * v = 1 := by rw [← huv, hu2]
  rw [hone, orderOf_one] at heven
  exact absurd heven (by norm_num)

end Work.BrauerSuzuki.Group
