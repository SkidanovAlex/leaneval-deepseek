/-
# Area `A7REC`, file `Char/a7InvolutionCounts.lean`

The local involution-pair counts of design pass 7 (`Core7.lean` §1), the input of the
class-multiplication bridge which turns them into the three rational relations of the
`A₇`-character table.

For a group `G` write `i(x) = #{p : G × G | p.1² = p.2² = 1, p.1 * p.2 = x}` (the definition
`Work.A7REC.C7invPairCount`).  The theorem below proves, from the local `A₇`-data alone
(no character theory, no simplicity of `G`, no order of `G`):

* if `π ∈ S` has order `4` and `C_G(π) = ⟨π⟩` (with `S ≅ D₈`), then `i(π) = 4`;
* if `z` is the central involution of a Sylow `2`-subgroup `S` and `C_G(z) = U ⊔ S` with
  `|U| = 3`, then `i(z) = 8`;
* if moreover `σ ∈ U`, `σ ≠ 1`, then `i(zσ) = 6`.

Mathematical content, in the order in which it is formalised:

* the pairs of involutions with product `x` correspond bijectively to the involutions `u` with
  `u x u⁻¹ = x⁻¹` and `u x` an involution (`ncard_pair_eq_ncard_invSet`);
* for `x = π` of order `4` with `C(π) = ⟨π⟩` the inverting involutions form the coset `r ⟨π⟩`
  of the reflection `r ∈ S` inverting `π`, hence number `4` (`ncard_invSet_pi`);
* the remaining two counts need `|C_G(z)| = 24`, i.e. the *global* input `U ⊴ C_G(z)`
  (equivalently `C_G(z) = U · S`).  **The local hypotheses alone do not give this**: for a group
  in which `U` is not normalised by `S` the subgroup `⟨U, S⟩ = C_G(z)` is strictly bigger than
  the set `U · S`, of size `|U|·|S| = 24` (the product formula only bounds `|U ⊔ S|` from below).
  Concretely the group `(C₆ × S₃) : C₂` of order `72` carries the full local configuration
  (a central involution `z`, a Sylow `2`-subgroup `S ≅ D₈`, a subgroup `U` of order `3` with
  `G = ⟨U, S⟩`, and `π` of order `4` with `C_G(π) = ⟨π⟩`) and has `|C_G(z)| = 72`.  In the
  actual setting the missing input comes from `|G| = 2520` together with simplicity — the only
  simple group of order `2520` is `A₇`, where every involution centralizer has order `24`
  (this is the Gorenstein--Walter input, see the delegated lemma
  `Work.A7REC.Char.cardCentralizerZSimple`);
* given `|C_G(z)| = 24` one has `C_G(z) = U ⋊ S` (the element count of a group of order `24`
  with `U ⋊ S` forces `U ⊴ C_G(z)`), `S` acts on `U ≅ Z₃` with kernel `K = C_S(U)` of order `4`
  (a Klein four group, since `π ∉ K`), and `C_G(z)` has exactly `9` involutions:
  `5` in `S` together with `2 · 2` of the form `σ^i s` with `s ∈ S ∖ K`, `s² = 1`;
* this gives `i(z) = 8` and (with `(zσ)³ = z`, so that `C_G(zσ) ⊆ C_G(z)`) `i(zσ) = 6`: inside
  `C(z) = U ⋊ S` the elements inverting `zσ` are the `σ^i s` with `s ∈ S ∖ K`, and those that
  are involutions are the `6` elements `σ^i s` with `s` one of the two involutions of `S ∖ K`.
-/
import Mathlib
import Submission.Work.A7REC.Defs
import Submission.Work.A7REC.Char.invPairsZAndZsigma

namespace Work.A7REC.Char

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-! ## 1. Counting pairs of involutions -/

lemma orderOf_eq_two_iff' {u : G} : orderOf u = 2 ↔ u ≠ 1 ∧ u * u = 1 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hu; rw [hu, orderOf_one] at h; exact absurd h (by norm_num)
    · have := pow_orderOf_eq_one u
      rw [h] at this
      simpa [pow_two] using this
  · rintro ⟨h1, h2⟩
    apply orderOf_eq_prime _ h1
    simpa [pow_two] using h2

/-- The involutions inverting `x`: involutions `u` with `u * x * u⁻¹ = x⁻¹` and `u * x` an
involution.  These are exactly the first coordinates of the involution pairs with product `x`. -/
def invSet (x : G) : Set G :=
  {u | orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹ ∧ orderOf (u * x) = 2}

/-- **The pairs of involutions with product `x` are the involutions inverting `x`.**  The
bijection is `(u, v) ↦ u`, with inverse `u ↦ (u, u * x)`. -/
theorem ncard_pair_eq_ncard_invSet (x : G) :
    Work.A7REC.C7invPairCount x = (invSet x).ncard := by
  unfold Work.A7REC.C7invPairCount
  apply Set.ncard_congr (fun p _ => p.1)
  · rintro ⟨u, v⟩ ⟨hu, hv, huv⟩
    obtain ⟨_, hu1⟩ := orderOf_eq_two_iff'.mp hu
    obtain ⟨_, hv1⟩ := orderOf_eq_two_iff'.mp hv
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu1
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv1
    refine ⟨hu, ?_, ?_⟩
    · have h1 : u * x * u⁻¹ = v * u := by
        rw [← huv]
        conv_lhs => rw [← mul_assoc, hu1]
        rw [one_mul, huinv]
      have h2 : x⁻¹ = v * u := by
        rw [← huv, mul_inv_rev, huinv, hvinv]
      rw [h1, h2]
    · have h3 : u * x = v := by
        rw [← huv, ← mul_assoc, hu1, one_mul]
      rw [h3]; exact hv
  · rintro ⟨u, v⟩ ⟨u', v'⟩ ⟨hu, hv, huv⟩ ⟨hu', hv', huv'⟩ h
    simp only [Prod.fst] at h
    subst h
    have : u * v = u * v' := by rw [huv, huv']
    exact congrArg (fun w => (u, w)) (mul_left_cancel this)
  · rintro u ⟨hu, hx, hux⟩
    have hu1 : u * u = 1 := (orderOf_eq_two_iff'.mp hu).2
    refine ⟨(u, u * x), ?_, rfl⟩
    exact ⟨hu, hux, by rw [← mul_assoc, hu1, one_mul]⟩

/-! ## 2. The dihedral group of order `8` -/

namespace Dihedral4

/-- In `DihedralGroup 4` the elements of order `4` are exactly `r 1` and `r 3`. -/
lemma orderOf_eq_four_iff (x : DihedralGroup 4) :
    orderOf x = 4 ↔ x = DihedralGroup.r 1 ∨ x = DihedralGroup.r 3 := by
  have key : ∀ j : ℕ, j < 4 → (orderOf (DihedralGroup.r (j : ZMod 4)) = 4 ↔ j = 1 ∨ j = 3) := by
    intro j hj
    rw [DihedralGroup.orderOf_r, ZMod.val_natCast, Nat.mod_eq_of_lt hj]
    interval_cases j <;> norm_num
  constructor
  · intro hx
    cases x with
    | r i =>
      have hi : (i.val : ZMod 4) = i := ZMod.natCast_zmod_val i
      rw [← hi] at hx
      rcases (key i.val (ZMod.val_lt i)).mp hx with h | h
      · left; rw [← hi, h]; norm_num
      · right; rw [← hi, h]; norm_num
    | sr i => rw [DihedralGroup.orderOf_sr] at hx; exact absurd hx (by norm_num)
  · rintro (rfl | rfl)
    · exact (key 1 (by norm_num)).mpr (Or.inl rfl)
    · exact (key 3 (by norm_num)).mpr (Or.inr rfl)

/-- The involutions of `DihedralGroup 4` are `r 2` and the four reflections. -/
lemma orderOf_eq_two_iff (x : DihedralGroup 4) :
    orderOf x = 2 ↔ x = DihedralGroup.r 2 ∨ x = DihedralGroup.sr 0 ∨ x = DihedralGroup.sr 1 ∨
      x = DihedralGroup.sr 2 ∨ x = DihedralGroup.sr 3 := by
  have key : ∀ j : ℕ, j < 4 → (orderOf (DihedralGroup.r (j : ZMod 4)) = 2 ↔ j = 2) := by
    intro j hj
    rw [DihedralGroup.orderOf_r, ZMod.val_natCast, Nat.mod_eq_of_lt hj]
    interval_cases j <;> norm_num
  constructor
  · intro hx
    cases x with
    | r i =>
      have hi : (i.val : ZMod 4) = i := ZMod.natCast_zmod_val i
      rw [← hi] at hx
      have h2 := (key i.val (ZMod.val_lt i)).mp hx
      left; rw [← hi, h2]; norm_num
    | sr i =>
      have hi : (i.val : ZMod 4) = i := ZMod.natCast_zmod_val i
      have hlt : i.val < 4 := ZMod.val_lt i
      interval_cases i.val
      · exact Or.inr (Or.inl (by rw [← hi]; norm_num))
      · exact Or.inr (Or.inr (Or.inl (by rw [← hi]; norm_num)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hi]; norm_num))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [← hi]; norm_num))))
  · rintro (h | h | h | h | h) <;> rw [h]
    · exact (key 2 (by norm_num)).mpr rfl
    · rw [DihedralGroup.orderOf_sr]
    · rw [DihedralGroup.orderOf_sr]
    · rw [DihedralGroup.orderOf_sr]
    · rw [DihedralGroup.orderOf_sr]

/-- `DihedralGroup 4` has exactly two elements of order `4`. -/
lemma card_order_four : Nat.card {x : DihedralGroup 4 // orderOf x = 4} = 2 := by
  have hset : {x : DihedralGroup 4 | orderOf x = 4} =
      {DihedralGroup.r 1, DihedralGroup.r 3} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact orderOf_eq_four_iff x
  rw [show Nat.card {x : DihedralGroup 4 // orderOf x = 4}
      = ({x : DihedralGroup 4 | orderOf x = 4} : Set _).ncard from rfl, hset,
    Set.ncard_pair (by decide)]

/-- `DihedralGroup 4` has exactly five involutions. -/
lemma card_involutions : Nat.card {x : DihedralGroup 4 // orderOf x = 2} = 5 := by
  have hset : {x : DihedralGroup 4 | orderOf x = 2} =
      {DihedralGroup.r 2, DihedralGroup.sr 0, DihedralGroup.sr 1, DihedralGroup.sr 2,
        DihedralGroup.sr 3} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    exact orderOf_eq_two_iff x
  rw [show Nat.card {x : DihedralGroup 4 // orderOf x = 2}
      = ({x : DihedralGroup 4 | orderOf x = 2} : Set _).ncard from rfl, hset]
  rw [show ({DihedralGroup.r 2, DihedralGroup.sr 0, DihedralGroup.sr 1, DihedralGroup.sr 2,
      DihedralGroup.sr 3} : Set (DihedralGroup 4))
      = insert (DihedralGroup.r 2) (insert (DihedralGroup.sr 0) (insert (DihedralGroup.sr 1)
        (insert (DihedralGroup.sr 2) {DihedralGroup.sr 3}))) from rfl]
  rw [Set.ncard_insert_of_notMem (by decide), Set.ncard_insert_of_notMem (by decide),
    Set.ncard_insert_of_notMem (by decide), Set.ncard_insert_of_notMem (by decide),
    Set.ncard_singleton]

/-- Every element of order `4` of `DihedralGroup 4` is inverted by the reflection `sr 0`. -/
lemma sr_zero_inverts (x : DihedralGroup 4) (hx : orderOf x = 4) :
    orderOf (DihedralGroup.sr (0 : ZMod 4)) = 2 ∧
      DihedralGroup.sr (0 : ZMod 4) * x * (DihedralGroup.sr (0 : ZMod 4))⁻¹ = x⁻¹ := by
  refine ⟨DihedralGroup.orderOf_sr 0, ?_⟩
  rcases orderOf_eq_four_iff x |>.mp hx with rfl | rfl <;>
    · simp [DihedralGroup.inv_sr, DihedralGroup.inv_r]

end Dihedral4

section Transport

variable {H : Subgroup G}

/-- The bijection induced by an isomorphism on the subtypes of elements of a given order. -/
def subtypeCongr (e : H ≃* DihedralGroup 4) (p : ℕ) :
    {x : H // orderOf x = p} ≃ {y : DihedralGroup 4 // orderOf y = p} where
  toFun x := ⟨e x.1, by rw [MulEquiv.orderOf_eq]; exact x.2⟩
  invFun y := ⟨e.symm y.1, by rw [MulEquiv.orderOf_eq]; exact y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

/-- A group isomorphic to `DihedralGroup 4` has exactly five involutions. -/
lemma card_involutions_of_iso (e : H ≃* DihedralGroup 4) :
    Nat.card {x : H // orderOf x = 2} = 5 := by
  rw [Nat.card_congr (subtypeCongr e 2)]
  exact Dihedral4.card_involutions

/-- A group isomorphic to `DihedralGroup 4` has exactly two elements of order `4`. -/
lemma card_order_four_of_iso (e : H ≃* DihedralGroup 4) :
    Nat.card {x : H // orderOf x = 4} = 2 := by
  rw [Nat.card_congr (subtypeCongr e 4)]
  exact Dihedral4.card_order_four

/-- The elements of order `4` of a group isomorphic to `DihedralGroup 4` are the two inverse
powers of a fixed one. -/
lemma order_four_eq_of_iso (e : H ≃* DihedralGroup 4) (x : H) (hx : orderOf x = 4) :
    x = e.symm (DihedralGroup.r 1) ∨ x = e.symm (DihedralGroup.r 3) := by
  rcases Dihedral4.orderOf_eq_four_iff (e x) |>.mp (by rwa [MulEquiv.orderOf_eq]) with h | h
  · left; rw [← e.symm_apply_apply x, h]
  · right; rw [← e.symm_apply_apply x, h]

/-- Every element of order `4` of a group isomorphic to `DihedralGroup 4` is inverted by an
involution of that group. -/
lemma exists_inverting_of_iso (e : H ≃* DihedralGroup 4) (x : H) (hx : orderOf x = 4) :
    ∃ y : H, orderOf y = 2 ∧ y * x * y⁻¹ = x⁻¹ := by
  refine ⟨e.symm (DihedralGroup.sr 0), ?_, ?_⟩
  · rw [← MulEquiv.orderOf_eq e, e.apply_symm_apply, DihedralGroup.orderOf_sr]
  · have h := Dihedral4.sr_zero_inverts (e x) (by rwa [MulEquiv.orderOf_eq])
    have : e (e.symm (DihedralGroup.sr 0) * x * (e.symm (DihedralGroup.sr 0))⁻¹) = e x⁻¹ := by
      simp only [map_mul, map_inv, e.apply_symm_apply, h.2]
    exact e.injective this

end Transport

/-! ## 3. The `A₇`-configuration -/

/-- The local hypotheses of the involution-pair counts (the data of
`Work.A7REC.A7InvolutionCountsProp`). -/
structure A7InvCtx (G : Type*) [Group G] [Finite G] where
  /-- the Sylow `2`-subgroup. -/
  S : Sylow 2 G
  /-- it is dihedral of order `8`. -/
  hSdih : Nonempty ((S : Subgroup G) ≃* DihedralGroup 4)
  /-- the central involution of `S`. -/
  z : G
  /-- it lies in `S`. -/
  hzS : z ∈ (S : Subgroup G)
  /-- it has order `2`. -/
  hz2 : orderOf z = 2
  /-- the subgroup of order `3` with `C_G(z) = U ⊔ S`. -/
  U : Subgroup G
  /-- `|U| = 3`. -/
  hU3 : Nat.card U = 3
  /-- `C_G(z) = U ⊔ S`. -/
  hC : centralizer ({z} : Set G) = U ⊔ (S : Subgroup G)
  /-- an element of order `4` in `S` with `C_G(π) = ⟨π⟩`. -/
  π : G
  /-- `π ∈ S`. -/
  hπS : π ∈ (S : Subgroup G)
  /-- `π` has order `4`. -/
  hπ4 : orderOf π = 4
  /-- `C_G(π) = ⟨π⟩`. -/
  hCπ : centralizer ({π} : Set G) = zpowers π
  /-- a nontrivial element of `U`. -/
  σ : G
  /-- `σ ∈ U`. -/
  hσU : σ ∈ U
  /-- `σ ≠ 1`. -/
  hσ1 : σ ≠ 1

namespace A7InvCtx

variable (h : A7InvCtx G)

/-- The Sylow `2`-subgroup as a subgroup. -/
abbrev Sg : Subgroup G := (h.S : Subgroup G)

/-- `C_G(z)`. -/
abbrev C : Subgroup G := centralizer ({h.z} : Set G)

theorem card_Sg : Nat.card h.Sg = 8 := by
  obtain ⟨e⟩ := h.hSdih
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem z_mem_Sg : h.z ∈ h.Sg := h.hzS

theorem Sg_le_C : h.Sg ≤ h.C := by
  rw [A7InvCtx.C, h.hC]
  exact le_sup_right

theorem U_le_C : h.U ≤ h.C := by
  rw [A7InvCtx.C, h.hC]
  exact le_sup_left

theorem z_mem_C : h.z ∈ h.C := h.Sg_le_C h.z_mem_Sg

theorem σ_mem_C : h.σ ∈ h.C := h.U_le_C h.hσU

theorem π_mem_C : h.π ∈ h.C := h.Sg_le_C h.hπS

theorem z_central_in_C {c : G} (hc : c ∈ h.C) : c * h.z = h.z * c :=
  ((Subgroup.mem_centralizer_iff.mp hc) h.z (by simp)).symm

/-- Every element of `S` centralizes `z`. -/
theorem Sg_centralizes_z {s : G} (hs : s ∈ h.Sg) : s * h.z = h.z * s :=
  h.z_central_in_C (h.Sg_le_C hs)

theorem U_inf_Sg : h.U ⊓ h.Sg = ⊥ := by
  apply Subgroup.card_eq_one.mp
  have hdvd1 : Nat.card ↥(h.U ⊓ h.Sg) ∣ Nat.card ↥h.U :=
    Subgroup.card_dvd_of_le (α := G) inf_le_left
  have hdvd2 : Nat.card ↥(h.U ⊓ h.Sg) ∣ Nat.card ↥h.Sg :=
    Subgroup.card_dvd_of_le (α := G) inf_le_right
  rw [h.hU3] at hdvd1
  rw [h.card_Sg] at hdvd2
  have := Nat.dvd_gcd hdvd1 hdvd2
  rw [show Nat.gcd 3 8 = 1 from rfl] at this
  exact Nat.dvd_one.mp this

/-- `σ` has order `3` (it generates the subgroup `U` of order `3`). -/
theorem orderOf_σ : orderOf h.σ = 3 := by
  have hdvd : orderOf h.σ ∣ 3 := by
    simpa [h.hU3] using Subgroup.orderOf_dvd_natCard h.U h.hσU
  have hne : orderOf h.σ ≠ 1 := fun hh => h.hσ1 (orderOf_eq_one_iff.mp hh)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
  · exact absurd h hne
  · exact h

/-- `U` is the cyclic subgroup generated by `σ`. -/
theorem U_eq_zpowers : h.U = zpowers h.σ := by
  have hle : zpowers h.σ ≤ h.U := zpowers_le.mpr h.hσU
  have hcard : Nat.card ↥(zpowers h.σ) = Nat.card ↥h.U := by
    rw [Nat.card_zpowers, h.orderOf_σ, h.hU3]
  exact (Subgroup.eq_of_le_of_card_ge hle (ge_of_eq hcard)).symm

/-- An element of `S` inverting `π` (whose existence is the dihedral structure of `S`). -/
theorem exists_inverting_pi : ∃ y : G, orderOf y = 2 ∧ y * h.π * y⁻¹ = h.π⁻¹ := by
  obtain ⟨e⟩ := h.hSdih
  obtain ⟨y, hy2, hyinv⟩ :=
    exists_inverting_of_iso e ⟨h.π, h.hπS⟩ (by simpa using h.hπ4)
  exact ⟨(y : G), by simpa using hy2, by
    have hh := congrArg (fun z : ↥h.Sg => (z : G)) hyinv
    simpa using hh⟩

/-- **The involutions inverting `π` form the coset `y ⟨π⟩` of a reflection `y` inverting `π`;
there are exactly `4` of them.** -/
theorem ncard_invSet_pi : (invSet h.π).ncard = 4 := by
  obtain ⟨y, hy2, hyinv⟩ := h.exists_inverting_pi
  have hy1 : y * y = 1 := (orderOf_eq_two_iff'.mp hy2).2
  have hyy : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy1
  have hyinv' : y⁻¹ * h.π * y = h.π⁻¹ := by
    have hh := hyinv
    rw [hyy] at hh
    rw [hyy]
    exact hh
  -- `y ∉ ⟨π⟩`, since `⟨π⟩` is abelian while `y` inverts `π`
  have hy_notmem : y ∉ zpowers h.π := by
    intro hy
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hconj : y * h.π * y⁻¹ = h.π := by rw [← hj]; group
    rw [hconj] at hyinv
    have h2 : h.π * h.π = 1 := by
      nth_rewrite 1 [hyinv]
      exact inv_mul_cancel h.π
    have h3 : h.π ^ 2 = 1 := by simpa [pow_two] using h2
    have hdvd : orderOf h.π ∣ 2 := orderOf_dvd_of_pow_eq_one h3
    rw [h.hπ4] at hdvd
    omega
  -- `y π^k y⁻¹ = (π^k)⁻¹`
  have hconj : ∀ k : ℤ, y * h.π ^ k * y⁻¹ = (h.π ^ k)⁻¹ := by
    intro k
    have h1 : MulAut.conj y h.π = h.π⁻¹ := hyinv
    calc y * h.π ^ k * y⁻¹ = MulAut.conj y (h.π ^ k) := by rw [MulAut.conj_apply]
      _ = (MulAut.conj y h.π) ^ k := map_zpow _ _ _
      _ = (h.π⁻¹) ^ k := by rw [h1]
      _ = (h.π ^ k)⁻¹ := inv_zpow _ _
  -- every `y π^k` is an involution
  have hsq : ∀ j : ℤ, orderOf (y * h.π ^ j) = 2 := by
    intro j
    rw [orderOf_eq_two_iff']
    refine ⟨?_, ?_⟩
    · intro h1
      refine hy_notmem ?_
      have hy_eq : y = (h.π ^ j)⁻¹ := mul_eq_one_iff_eq_inv.mp h1
      rw [hy_eq]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩)
    · calc (y * h.π ^ j) * (y * h.π ^ j)
          = (y * h.π ^ j * y⁻¹) * (y * y) * h.π ^ j := by group
        _ = (h.π ^ j)⁻¹ * 1 * h.π ^ j := by rw [hconj j, hy1]
        _ = 1 := by rw [mul_one, inv_mul_cancel]
  have hsplit : ∀ j : ℤ, y * h.π ^ j * h.π = y * h.π ^ (j + 1) := by
    intro j
    rw [mul_assoc y (h.π ^ j) h.π, ← zpow_add_one]
  have hpow : ∀ k : ℤ, h.π ^ (k + 1) * (h.π ^ k)⁻¹ = h.π := by
    intro k
    rw [← zpow_neg, ← zpow_add]
    simp
  have hmem : ∀ x ∈ zpowers h.π, y * x ∈ invSet h.π := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨hsq k, ?_, ?_⟩
    · calc y * h.π ^ k * h.π * (y * h.π ^ k)⁻¹
          = y * (h.π ^ k * h.π * (h.π ^ k)⁻¹) * y⁻¹ := by group
        _ = y * h.π * y⁻¹ := by rw [← zpow_add_one, hpow k]
        _ = h.π⁻¹ := hyinv
    · rw [hsplit k]
      exact hsq (k + 1)
  have hmem' : ∀ u ∈ invSet h.π, y⁻¹ * u ∈ zpowers h.π := by
    intro u ⟨hu2, huinv, _⟩
    rw [← h.hCπ, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have h1 : u * h.π = h.π⁻¹ * u := by rw [← huinv]; group
    have h2 : y⁻¹ * h.π⁻¹ = h.π * y⁻¹ := by
      calc y⁻¹ * h.π⁻¹ = y⁻¹ * (y⁻¹ * h.π * y) := by rw [hyinv']
        _ = y * (y * h.π * y) := by rw [hyy]
        _ = h.π * y := by
              rw [← mul_assoc y (y * h.π) y, ← mul_assoc y y h.π, hy1, one_mul]
        _ = h.π * y⁻¹ := by rw [hyy]
    calc h.π * (y⁻¹ * u) = (h.π * y⁻¹) * u := by group
      _ = (y⁻¹ * h.π⁻¹) * u := by rw [← h2]
      _ = y⁻¹ * (h.π⁻¹ * u) := by group
      _ = y⁻¹ * (u * h.π) := by rw [← h1]
      _ = y⁻¹ * u * h.π := by group
  have hbij : Nat.card ↥(zpowers h.π) = Nat.card {u : G // u ∈ invSet h.π} := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun x => ⟨y * x.1, hmem x.1 x.2⟩
        invFun := fun u => ⟨y⁻¹ * u.1, hmem' u.1 u.2⟩
        left_inv := fun x => by ext; group
        right_inv := fun u => by ext; group }
  rw [show (invSet h.π).ncard = Nat.card {u : G // u ∈ invSet h.π} from rfl, ← hbij,
    Nat.card_zpowers, h.hπ4]

end A7InvCtx

theorem a7InvolutionCounts : Work.A7REC.A7InvolutionCountsProp := by
  intro G _ _ S z U π σ hG hzS hz2 hC hU3 hσU hσ1 hπS hπ4 hCπ hSdih
  haveI : IsSimpleGroup G := hG.1
  obtain ⟨hz8, hz6⟩ :=
    invPairsZAndZsigma hG.2 S z U π σ hzS hz2 hC hU3 hσU hσ1 hπS hπ4 hCπ hSdih
  refine ⟨?_, hz8, hz6⟩
  rw [ncard_pair_eq_ncard_invSet]
  exact A7InvCtx.ncard_invSet_pi
    { S := S, hSdih := hSdih, z := z, hzS := hzS, hz2 := hz2, U := U, hU3 := hU3, hC := hC,
      π := π, hπS := hπS, hπ4 := hπ4, hCπ := hCπ, σ := σ, hσU := hσU, hσ1 := hσ1 }

end Work.A7REC.Char
