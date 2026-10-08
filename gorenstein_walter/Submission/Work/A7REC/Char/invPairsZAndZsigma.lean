import Mathlib
import Submission.Work.A7REC.Defs
import Submission.Work.A7REC.Char.cardCentralizerZSimple
import Submission.Work.A7REC.Char.card_count_orders_le

/-!
# Reproduction of the involution-count machinery for `invPairsZAndZsigma`

The modules `Char/a7InvolutionCounts.lean`, `Char/cardInvolutionsCentralizerNorm.lean`,
`Char/invertingSetZsigma.lean` and `Char/u_normal_of_card.lean` sit around
`a7InvolutionCounts` in the import order (they define or import `A7InvCtx`), so they cannot be
imported here without creating an import cycle.  Their arguments are reproduced verbatim below
inside the namespace `InvPairsRepro`; the proof of `invPairsZAndZsigma` at the bottom of the
file uses them.
-/

namespace Work.A7REC.Char

namespace InvPairsRepro

section FromA7InvolutionCounts

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


end FromA7InvolutionCounts

section FromCardInvolutionsCentralizerNorm

/-
# The involutions of `C_G(z)` in the `A₇`-configuration, with `U ⊴ C_G(z)`

The lemma `Work.A7REC.Char.cardInvolutionsCentralizer`
(`Submission/Work/A7REC/Char/cardInvolutionsCentralizer.lean`) claims that in every context
`h : Work.A7REC.Char.A7InvCtx G` the centralizer `h.C = C_G(z)` has exactly nine involutions.
**That statement is false as written**: an ambient group supplying the context can be the
permutation group `G = ⟨(5,6)(8,10), (2,3)(7,8)(9,10), (7,9)(8,10), (1,2,3), (4,5,6)⟩ ≤ Sym 10`
of order `72` (`SmallGroup(72,22) ≅ (C₆ × S₃) : C₂`) with
`S = ⟨(5,6)(8,10), (2,3)(7,8)(9,10), (7,9)(8,10)⟩ ≅ D₈` (a Sylow 2-subgroup),
`z = (7,9)(8,10)` (central, of order `2`), `U = ⟨(1,2,3)(4,5,6)⟩` (order `3`, `U ⊓ S = ⊥`,
`U ⊔ S = G = C_G(z)`) and `π = (2,3)(5,6)(7,8,9,10) ∈ S` of order `4` with `C_G(π) = ⟨π⟩`;
there `h.C = ⊤` has **13** involutions.  The failing step of the intended plan is the claim that
the conjugates of `S` in `C` are among `S, S^σ, S^{σ²}`: conjugation by `s ∈ S` sends `S^{σ^i}`
to `S^{s⁻¹σ^i s}`, which need only be one of the three when `s` normalizes `U`; in the example
above `n₂(C) = 9 = [C : S]`, and with `|C| = 72` there is no bound on the number of elements of
order `4` either (`G` has an `18`-element class of elements of order `4`).

The repair is to add the missing hypothesis, exactly the field `A7RecCtx.hUnorm` of the real
`A₇`-context: `U` is normal in `C_G(z)`.  Since `U ⊓ S = ⊥` (coprime orders), this makes
`C_G(z) = U ⋊ S` an internal semidirect product and the count becomes the elementary one below.
Writing `K = C_S(U)`:
* `|K| = 4`: the conjugation action of `S` on `U ≅ Z₃` has kernel `K`, so `[S : K] ≤ 2`, and
  `K ≠ S` because `π ∉ K` (else `σ ∈ C_G(π) = ⟨π⟩`, of order `4`);
* `K` contains no element of order `4` (the elements of order `4` of `S ≅ D₈` are `π, π⁻¹`), so
  `K` is a four-group: it has exactly `3` involutions, and `S ∖ K` has `5 - 3 = 2`;
* an element `u * s` (`u ∈ U`, `s ∈ S`) is an involution iff `s ^ 2 = 1` and (`u = 1` or
  `s ∉ K`), which gives `5 + 2 · 2 = 9` involutions.

With `|C| = 24` in place of the normality hypothesis the conclusion is also true — normality is
then a *consequence* of the counting (`Work.A7REC.Char.U_normal_of_card_centralizer_eq_24`).
-/

set_option linter.unusedSectionVars false


open Subgroup

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

namespace A7InvCtx

variable (h : A7InvCtx G)

/-- The kernel `C_S(U)` of the conjugation action of `S` on `U`: the elements of `S` centralizing
`U`. -/
abbrev K : Subgroup G := h.Sg ⊓ Subgroup.centralizer (h.U : Set G)

/-- The subtype of a subgroup is equivalent to the corresponding subtype of the ambient group. -/
def subtypeSubgroupEquiv {H : Subgroup G} (p : G → Prop) :
    {x : ↥H // p (x : G)} ≃ {x : G // x ∈ H ∧ p x} where
  toFun x := ⟨(x.1 : G), x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

/-- Membership in `K`, in conjugation form. -/
theorem mem_K_iff {s : G} (hs : s ∈ h.Sg) : s ∈ h.K ↔ ∀ u ∈ h.U, s * u * s⁻¹ = u := by
  constructor
  · intro hsK u hu
    have h1 : u * s = s * u := (Subgroup.mem_centralizer_iff.mp hsK.2) u hu
    calc s * u * s⁻¹ = (u * s) * s⁻¹ := by rw [h1]
      _ = u := by group
  · intro hconj
    refine ⟨hs, Subgroup.mem_centralizer_iff.mpr (fun u hu => ?_)⟩
    calc u * s = (s * u * s⁻¹) * s := by rw [hconj u hu]
      _ = s * u := by group

/-- With `U ⊴ C`, the Sylow subgroup `S ≤ C` normalizes `U`. -/
theorem Sg_le_normalizer_U (hnorm : (h.U.subgroupOf h.C).Normal) :
    h.Sg ≤ Subgroup.normalizer (h.U : Set G) :=
  le_trans h.Sg_le_C ((Subgroup.normal_subgroupOf_iff_le_normalizer h.U_le_C).mp hnorm)

/-- Conjugation by an element of `S` preserves `U`. -/
theorem conj_mem_U (hnorm : (h.U.subgroupOf h.C).Normal) {s u : G} (hs : s ∈ h.Sg)
    (hu : u ∈ h.U) : s * u * s⁻¹ ∈ h.U :=
  ((Subgroup.mem_normalizer_iff.mp (Sg_le_normalizer_U h hnorm hs)) u).mp hu

/-- `x ^ 3 = 1` gives `x ^ 4 = x`. -/
theorem pow_four_eq_self {x : G} (h3 : x ^ 3 = 1) : x ^ 4 = x := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, h3, one_mul, pow_one]

/-- `x ^ 3 = 1` gives `(x ^ 2)⁻¹ = x`. -/
theorem inv_sq_eq_self {x : G} (h3 : x ^ 3 = 1) : (x ^ 2)⁻¹ = x := by
  have h : x ^ 2 * x = 1 := by rw [← pow_succ, show 2 + 1 = 3 from rfl, h3]
  exact inv_eq_of_mul_eq_one_right h

/-- `x ^ 3 = 1` gives `x ^ 2 = x⁻¹`. -/
theorem sq_eq_inv {x : G} (h3 : x ^ 3 = 1) : x ^ 2 = x⁻¹ :=
  mul_eq_one_iff_eq_inv.mp (by rw [← pow_succ, show 2 + 1 = 3 from rfl, h3])

/-- The elements of the group `U` of order `3`. -/
theorem U_elements {u : G} (hu : u ∈ h.U) : u = 1 ∨ u = h.σ ∨ u = h.σ ^ 2 := by
  have hσ2ne : h.σ ^ 2 ≠ 1 := by
    intro h2
    have hdvd : orderOf h.σ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [h.orderOf_σ] at hdvd
    omega
  have hσ2σ : h.σ ^ 2 ≠ h.σ := by
    intro h2
    have h1 : h.σ * h.σ = h.σ * 1 := by rw [← pow_two, h2, mul_one]
    exact h.hσ1 (mul_left_cancel h1)
  have hset : ({1, h.σ, h.σ ^ 2} : Set G) = (h.U : Set G) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact h.hσU
      · exact Subgroup.pow_mem _ h.hσU 2
    · have hcardU : (h.U : Set G).ncard = 3 := by
        rw [show (h.U : Set G).ncard = Nat.card ↥h.U from rfl, h.hU3]
      have hcardS : ({1, h.σ, h.σ ^ 2} : Set G).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem (by simp [Ne.symm h.hσ1, Ne.symm hσ2ne]),
          Set.ncard_insert_of_notMem (by simp [Ne.symm hσ2σ]), Set.ncard_singleton]
      rw [hcardU, hcardS]
  have hu' : u ∈ ({1, h.σ, h.σ ^ 2} : Set G) := by rw [hset]; exact hu
  simpa using hu'

/-- `u ∈ U`, `u ≠ 1` implies `orderOf u = 3`. -/
theorem orderOf_eq_three_of_mem {u : G} (hu : u ∈ h.U) (hu1 : u ≠ 1) : orderOf u = 3 := by
  have hdvd : orderOf u ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard h.U hu
    rwa [h.hU3] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact absurd (orderOf_eq_one_iff.mp h1) hu1
  · exact h3

/-- `u ∈ U`, `u ≠ 1` implies `u * u ≠ 1`. -/
theorem sq_ne_one_of_mem {u : G} (hu : u ∈ h.U) (hu1 : u ≠ 1) : u * u ≠ 1 := by
  intro h2
  have h3 : u ^ 2 = 1 := by rw [pow_two]; exact h2
  have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h3
  rw [orderOf_eq_three_of_mem h hu hu1] at hdvd
  omega

/-- **The conjugation action of `S` on `U` is trivial or inversion.** -/
theorem conj_dichotomy (hnorm : (h.U.subgroupOf h.C).Normal) {s : G} (hs : s ∈ h.Sg) :
    (∀ u ∈ h.U, s * u * s⁻¹ = u) ∨ (∀ u ∈ h.U, s * u * s⁻¹ = u⁻¹) := by
  have hσmem : s * h.σ * s⁻¹ ∈ h.U := conj_mem_U h hnorm hs h.hσU
  have hσord : orderOf (s * h.σ * s⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.orderOf_σ]
  have hσ3 : h.σ ^ 3 = 1 := by
    rw [← h.orderOf_σ]; exact pow_orderOf_eq_one h.σ
  have hconj_sq : s * h.σ ^ 2 * s⁻¹ = (s * h.σ * s⁻¹) ^ 2 := by
    rw [pow_two, pow_two]; group
  rcases U_elements h hσmem with h1 | h2 | h3
  · rw [h1, orderOf_one] at hσord; exact absurd hσord (by norm_num)
  · refine Or.inl (fun u hu => ?_)
    rcases U_elements h hu with hu1 | hu2 | hu3
    · rw [hu1]; simp
    · rw [hu2, h2]
    · rw [hu3, hconj_sq, h2]
  · refine Or.inr (fun u hu => ?_)
    rcases U_elements h hu with hu1 | hu2 | hu3
    · rw [hu1]; simp
    · rw [hu2, h3, sq_eq_inv hσ3]
    · rw [hu3, hconj_sq, h3]
      rw [show (h.σ ^ 2) ^ 2 = h.σ from by
            rw [← pow_mul, show 2 * 2 = 4 from rfl, pow_four_eq_self hσ3],
        inv_sq_eq_self hσ3]

/-- An element of `S` outside `K` inverts `U`. -/
theorem conj_eq_inv_of_notMem_K (hnorm : (h.U.subgroupOf h.C).Normal) {s : G} (hs : s ∈ h.Sg)
    (hsK : s ∉ h.K) : ∀ u ∈ h.U, s * u * s⁻¹ = u⁻¹ := by
  rcases conj_dichotomy h hnorm hs with h1 | h2
  · exact absurd ((mem_K_iff h hs).mpr h1) hsK
  · exact h2

/-- `π ∉ C_S(U)`: `π` does not centralize `σ`, since `C_G(π) = ⟨π⟩` has order `4`. -/
theorem pi_notMem_K : h.π ∉ h.K := by
  intro hπK
  have hconj := (mem_K_iff h h.hπS).mp hπK
  have hcomm : h.π * h.σ = h.σ * h.π := by
    calc h.π * h.σ = (h.π * h.σ * h.π⁻¹) * h.π := by group
      _ = h.σ * h.π := by rw [hconj h.σ h.hσU]
  have hmem : h.σ ∈ Subgroup.zpowers h.π := by
    rw [← h.hCπ, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact hcomm
  have hle : Subgroup.zpowers h.σ ≤ Subgroup.zpowers h.π := Subgroup.zpowers_le.mpr hmem
  have hdvd : 3 ∣ 4 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, Nat.card_zpowers, h.orderOf_σ, h.hπ4] at this
  omega

/-- The number of elements of order `4` of `S` is `2`. -/
theorem card_order_four_Sg : Nat.card {x : G // x ∈ h.Sg ∧ orderOf x = 4} = 2 := by
  obtain ⟨e⟩ := h.hSdih
  rw [← card_order_four_of_iso e]
  rw [show Nat.card {x : ↥h.Sg // orderOf x = 4}
      = Nat.card {x : ↥h.Sg // orderOf ((x : G)) = 4} from
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [Subgroup.orderOf_coe]))]
  exact (Nat.card_congr (subtypeSubgroupEquiv (H := h.Sg) (p := fun x => orderOf x = 4))).symm

/-- The elements of order `4` of `S` are `π` and `π⁻¹` (`S ≅ D₈`). -/
theorem Sg_order_four_eq {x : G} (hx : x ∈ h.Sg) (hx4 : orderOf x = 4) :
    x = h.π ∨ x = h.π⁻¹ := by
  have hsub : ({h.π, h.π⁻¹} : Set G) ⊆ {y : G | y ∈ h.Sg ∧ orderOf y = 4} := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ⟨h.hπS, h.hπ4⟩
    · exact ⟨h.Sg.inv_mem h.hπS, by rw [orderOf_inv]; exact h.hπ4⟩
  have hne : h.π ≠ h.π⁻¹ := by
    intro hcon
    have h3 : h.π * h.π = 1 := by
      have h4 := mul_inv_cancel h.π
      rw [← hcon] at h4
      exact h4
    have h2 : h.π ^ 2 = 1 := by rw [pow_two]; exact h3
    have hdvd : orderOf h.π ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [h.hπ4] at hdvd
    omega
  have hn1 : ({h.π, h.π⁻¹} : Set G).ncard = 2 := Set.ncard_pair hne
  have hn2 : ({y : G | y ∈ h.Sg ∧ orderOf y = 4} : Set G).ncard = 2 := by
    rw [show ({y : G | y ∈ h.Sg ∧ orderOf y = 4} : Set G).ncard
        = Nat.card {y : G // y ∈ h.Sg ∧ orderOf y = 4} from rfl,
      card_order_four_Sg h]
  have heq : ({h.π, h.π⁻¹} : Set G) = {y : G | y ∈ h.Sg ∧ orderOf y = 4} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hn2, hn1])
  have hxmem : x ∈ ({h.π, h.π⁻¹} : Set G) := by rw [heq]; exact ⟨hx, hx4⟩
  simpa using hxmem

/-- `|C_S(U)| = 4`. -/
theorem K_card (hnorm : (h.U.subgroupOf h.C).Normal) : Nat.card ↥h.K = 4 := by
  have hKle : h.K ≤ h.Sg := inf_le_left
  have hdvd : Nat.card ↥h.K ∣ 8 := by
    have := Subgroup.card_dvd_of_le hKle
    rwa [h.card_Sg] at this
  have hπinv : ∀ u ∈ h.U, h.π⁻¹ * u * h.π = u⁻¹ := by
    intro u hu
    have h1 : h.π * u⁻¹ * h.π⁻¹ = u := by
      rw [conj_eq_inv_of_notMem_K h hnorm h.hπS (pi_notMem_K h) u⁻¹
          (Subgroup.inv_mem _ hu), inv_inv]
    have h2 : u⁻¹ = h.π⁻¹ * u * h.π := by
      calc u⁻¹ = h.π⁻¹ * (h.π * u⁻¹ * h.π⁻¹) * h.π := by group
        _ = h.π⁻¹ * u * h.π := by rw [h1]
    exact h2.symm
  have hcover : (h.Sg : Set G) ⊆ (h.K : Set G) ∪ (fun k => h.π * k) '' (h.K : Set G) := by
    intro t ht
    by_cases htK : t ∈ h.K
    · exact Or.inl htK
    · refine Or.inr ⟨h.π⁻¹ * t, ?_, ?_⟩
      · refine (mem_K_iff h (h.Sg.mul_mem (h.Sg.inv_mem h.hπS) ht)).mpr (fun u hu => ?_)
        have ht' := conj_eq_inv_of_notMem_K h hnorm ht htK u hu
        calc (h.π⁻¹ * t) * u * (h.π⁻¹ * t)⁻¹ = h.π⁻¹ * (t * u * t⁻¹) * h.π := by group
          _ = h.π⁻¹ * u⁻¹ * h.π := by rw [ht']
          _ = u := by rw [hπinv u⁻¹ (Subgroup.inv_mem _ hu), inv_inv]
      · show h.π * (h.π⁻¹ * t) = t
        group
  have hcard_le : Nat.card ↥h.Sg ≤ 2 * Nat.card ↥h.K := by
    have h1 : (h.Sg : Set G).ncard
        ≤ ((h.K : Set G) ∪ (fun k => h.π * k) '' (h.K : Set G)).ncard :=
      Set.ncard_le_ncard hcover
    have h2 : ((h.K : Set G) ∪ (fun k => h.π * k) '' (h.K : Set G)).ncard
        ≤ (h.K : Set G).ncard + ((fun k => h.π * k) '' (h.K : Set G)).ncard :=
      Set.ncard_union_le _ _
    have h3 : ((fun k => h.π * k) '' (h.K : Set G)).ncard = (h.K : Set G).ncard :=
      Set.ncard_image_of_injective _ (fun a b hab => mul_left_cancel hab)
    rw [show (h.Sg : Set G).ncard = Nat.card ↥h.Sg from rfl] at h1
    rw [show (h.K : Set G).ncard = Nat.card ↥h.K from rfl] at h2 h3
    rw [h3] at h2
    have h4 : Nat.card ↥h.Sg ≤ Nat.card ↥h.K + Nat.card ↥h.K := le_trans h1 h2
    rw [h.card_Sg] at h4
    have : Nat.card ↥h.K + Nat.card ↥h.K = 2 * Nat.card ↥h.K := by ring
    omega
  have hge : 4 ≤ Nat.card ↥h.K := by
    have := hcard_le
    rw [h.card_Sg] at this
    omega
  have hne8 : Nat.card ↥h.K ≠ 8 := by
    intro h8
    have hKS : h.K = h.Sg := Subgroup.eq_of_le_of_card_ge hKle (by rw [h8, h.card_Sg])
    exact pi_notMem_K h (hKS ▸ h.hπS)
  obtain ⟨k, hk, hk2⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card ↥h.K ∣ 2 ^ 3 by simpa using hdvd)
  have hkk : 2 ≤ k := by
    rw [hk2] at hge
    by_contra hcon
    have hk1 : k ≤ 1 := by omega
    interval_cases k <;> norm_num at hge
  have hk3 : k ≠ 3 := by
    intro h3
    exact hne8 (by rw [hk2, h3]; norm_num)
  have hk_eq : k = 2 := by omega
  rw [hk2, hk_eq]
  norm_num

/-- Every element of `K` is an involution. -/
theorem K_sq_eq_one (hnorm : (h.U.subgroupOf h.C).Normal) : ∀ x ∈ h.K, x ^ 2 = 1 := by
  intro x hxK
  have hxS : x ∈ h.Sg := hxK.1
  have hdvd : orderOf x ∣ 4 := by
    have := Subgroup.orderOf_dvd_natCard h.K hxK
    rwa [K_card h hnorm] at this
  have hx4 : orderOf x ≠ 4 := by
    intro h4
    rcases Sg_order_four_eq h hxS h4 with hx1 | hx2
    · exact pi_notMem_K h (hx1 ▸ hxK)
    · have hinv : h.π = x⁻¹ := by rw [hx2, inv_inv]
      exact pi_notMem_K h (hinv ▸ h.K.inv_mem hxK)
  have h2 : orderOf x ∣ 2 := by
    obtain ⟨k, hk, hk2⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf x ∣ 2 ^ 2 by simpa using hdvd)
    rw [hk2]
    interval_cases k
    · norm_num
    · norm_num
    · exact absurd (by rw [hk2]; norm_num) hx4
  exact orderOf_dvd_iff_pow_eq_one.mp h2

/-- The elements of `C` have a unique decomposition `u * s`, `u ∈ U`, `s ∈ S`. -/
theorem decomp (hnorm : (h.U.subgroupOf h.C).Normal) {x : G} (hx : x ∈ h.C) :
    ∃! p : G × G, p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ x = p.1 * p.2 := by
  haveI := hnorm
  have hsup : (h.U ⊔ h.Sg).subgroupOf h.C = ⊤ := by
    rw [← h.hC, Subgroup.subgroupOf_self]
  have htop : (h.U.subgroupOf h.C) ⊔ (h.Sg.subgroupOf h.C) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.U_le_C h.Sg_le_C, hsup]
  have hmem : (⟨x, hx⟩ : ↥h.C) ∈
      ((h.U.subgroupOf h.C : Set ↥h.C) * (h.Sg.subgroupOf h.C : Set ↥h.C)) := by
    rw [← Subgroup.normal_mul (h.U.subgroupOf h.C) (h.Sg.subgroupOf h.C), htop]
    exact Subgroup.mem_top _
  rw [Set.mem_mul] at hmem
  obtain ⟨u, hu, s, hs, hus⟩ := hmem
  have huG : (u : G) ∈ h.U := Subgroup.mem_subgroupOf.mp hu
  have hsG : (s : G) ∈ h.Sg := Subgroup.mem_subgroupOf.mp hs
  have hxs : x = (u : G) * (s : G) := by
    have := congrArg (fun z : ↥h.C => (z : G)) hus
    simpa using this.symm
  refine ⟨((u : G), (s : G)), ⟨huG, hsG, hxs⟩, ?_⟩
  rintro ⟨u', s'⟩ ⟨hu', hs', hxs'⟩
  have heq : (u : G) * (s : G) = u' * s' := by rw [← hxs, hxs']
  have h1 : u'⁻¹ * (u : G) = s' * (s : G)⁻¹ := by
    calc u'⁻¹ * (u : G) = u'⁻¹ * ((u : G) * (s : G)) * (s : G)⁻¹ := by group
      _ = u'⁻¹ * (u' * s') * (s : G)⁻¹ := by rw [heq]
      _ = s' * (s : G)⁻¹ := by group
  have h2 : u'⁻¹ * (u : G) ∈ h.U := h.U.mul_mem (h.U.inv_mem hu') huG
  have h3 : u'⁻¹ * (u : G) ∈ h.Sg := by rw [h1]; exact h.Sg.mul_mem hs' (h.Sg.inv_mem hsG)
  have h4 : u'⁻¹ * (u : G) ∈ (⊥ : Subgroup G) := by
    rw [← h.U_inf_Sg]; exact ⟨h2, h3⟩
  have h5 : u'⁻¹ * (u : G) = 1 := Subgroup.mem_bot.mp h4
  have hu_eq : (u : G) = u' := (inv_mul_eq_one.mp h5).symm
  have hs_eq : (s : G) = s' := by
    have hh := heq
    rw [← hu_eq] at hh
    exact mul_left_cancel hh
  exact Prod.ext hu_eq.symm hs_eq.symm

/-! ## Counting -/

/-- Splitting a set by a further predicate. -/
theorem ncard_split {α : Type*} [Finite α] (P R : α → Prop) :
    ({a : α | P a} : Set α).ncard =
      ({a : α | P a ∧ R a} : Set α).ncard + ({a : α | P a ∧ ¬R a} : Set α).ncard := by
  have h1 : ({a : α | P a ∧ R a} : Set α) ∪ {a : α | P a ∧ ¬R a} = {a : α | P a} := by
    ext a
    constructor
    · rintro (hh | hh)
      · exact hh.1
      · exact hh.1
    · intro ha
      by_cases hR : R a
      · exact Or.inl ⟨ha, hR⟩
      · exact Or.inr ⟨ha, hR⟩
  have h2 : ({a : α | P a ∧ R a} : Set α) ∩ {a : α | P a ∧ ¬R a} = ∅ := by
    ext a
    constructor
    · rintro ⟨⟨-, hR⟩, ⟨-, hnR⟩⟩; exact absurd hR hnR
    · intro hh; exact absurd hh (Set.notMem_empty a)
  have h3 := Set.ncard_union_add_ncard_inter ({a : α | P a ∧ R a} : Set α)
    ({a : α | P a ∧ ¬R a} : Set α)
  rw [h1, h2, Set.ncard_empty, add_zero] at h3
  exact h3

/-- `Nat.card` version of `ncard_split`. -/
theorem card_split {α : Type*} [Finite α] (P R : α → Prop) :
    Nat.card {a : α // P a} =
      Nat.card {a : α // P a ∧ R a} + Nat.card {a : α // P a ∧ ¬R a} := by
  have := ncard_split P R
  rwa [show ({a : α | P a} : Set α).ncard = Nat.card {a : α // P a} from rfl,
    show ({a : α | P a ∧ R a} : Set α).ncard = Nat.card {a : α // P a ∧ R a} from rfl,
    show ({a : α | P a ∧ ¬R a} : Set α).ncard = Nat.card {a : α // P a ∧ ¬R a} from rfl] at this

/-- The involutions of `S`: there are `5`. -/
theorem card_involutions_Sg : Nat.card {s : G // s ∈ h.Sg ∧ orderOf s = 2} = 5 := by
  obtain ⟨e⟩ := h.hSdih
  rw [← card_involutions_of_iso e]
  rw [show Nat.card {x : ↥h.Sg // orderOf x = 2}
      = Nat.card {x : ↥h.Sg // orderOf ((x : G)) = 2} from
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [Subgroup.orderOf_coe]))]
  exact (Nat.card_congr (subtypeSubgroupEquiv (H := h.Sg) (p := fun x => orderOf x = 2))).symm

/-- The involutions of `K`: there are `3` (a four-group). -/
theorem card_involutions_K (hnorm : (h.U.subgroupOf h.C).Normal) :
    Nat.card {x : G // x ∈ h.K ∧ orderOf x = 2} = 3 := by
  rw [show Nat.card {x : G // x ∈ h.K ∧ orderOf x = 2}
      = Nat.card {y : ↥h.K // orderOf ((y : G)) = 2} from
    (Nat.card_congr (subtypeSubgroupEquiv (H := h.K) (p := fun x => orderOf x = 2))).symm]
  rw [show Nat.card {y : ↥h.K // orderOf ((y : G)) = 2} = Nat.card {y : ↥h.K // y ≠ 1} from
    Nat.card_congr (Equiv.subtypeEquivRight (fun y => ?_))]
  · calc Nat.card {y : ↥h.K // y ≠ 1} = ({y : ↥h.K | y ≠ 1} : Set ↥h.K).ncard := rfl
      _ = ((Set.univ : Set ↥h.K) \ {(1 : ↥h.K)}).ncard := by
          rw [show ({y : ↥h.K | y ≠ 1} : Set ↥h.K) = (Set.univ : Set ↥h.K) \ {(1 : ↥h.K)}
            from by ext y; simp]
      _ = (Set.univ : Set ↥h.K).ncard - ({(1 : ↥h.K)} : Set ↥h.K).ncard :=
          Set.ncard_sdiff (Set.subset_univ _)
      _ = Nat.card ↥h.K - 1 := by rw [Set.ncard_univ, Set.ncard_singleton]
      _ = 3 := by rw [K_card h hnorm]
  · constructor
    · rintro h2 h1
      rw [h1, Subgroup.coe_one, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    · intro hy1
      rw [orderOf_eq_two_iff']
      refine ⟨fun h => hy1 (Subtype.ext (by rw [h, Subgroup.coe_one])), ?_⟩
      have hK := K_sq_eq_one h hnorm (y : G) y.2
      rw [pow_two] at hK
      exact hK

/-- The involutions of `S` outside `K`: there are `2`. -/
theorem card_involutions_Sg_notMem_K (hnorm : (h.U.subgroupOf h.C).Normal) :
    Nat.card {s : G // s ∈ h.Sg ∧ orderOf s = 2 ∧ s ∉ h.K} = 2 := by
  have hsplit := card_split (fun s : G => s ∈ h.Sg ∧ orderOf s = 2) (fun s => s ∈ h.K)
  have h1 : Nat.card {s : G // s ∈ h.Sg ∧ orderOf s = 2} = 5 := card_involutions_Sg h
  have h2 : Nat.card {s : G // (s ∈ h.Sg ∧ orderOf s = 2) ∧ s ∈ h.K} = 3 := by
    rw [show Nat.card {s : G // (s ∈ h.Sg ∧ orderOf s = 2) ∧ s ∈ h.K}
        = Nat.card {s : G // s ∈ h.K ∧ orderOf s = 2} from
      Nat.card_congr (Equiv.subtypeEquivRight (fun s => ?_))]
    · exact card_involutions_K h hnorm
    · constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩; exact ⟨⟨h3.1, h2⟩, h3⟩
  rw [show Nat.card {s : G // s ∈ h.Sg ∧ orderOf s = 2 ∧ s ∉ h.K}
      = Nat.card {s : G // (s ∈ h.Sg ∧ orderOf s = 2) ∧ ¬ (s ∈ h.K)} from
    Nat.card_congr (Equiv.subtypeEquivRight (fun s => ⟨
      fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩))]
  rw [h1, h2] at hsplit
  omega

/-- The nonidentity elements of `U`: there are `2`. -/
theorem card_nonid_U : Nat.card {u : G // u ∈ h.U ∧ u ≠ 1} = 2 := by
  rw [show Nat.card {u : G // u ∈ h.U ∧ u ≠ 1} = Nat.card {x : ↥h.U // (x : G) ≠ 1} from
    (Nat.card_congr (subtypeSubgroupEquiv (H := h.U) (p := fun x => x ≠ 1))).symm]
  rw [show Nat.card {x : ↥h.U // (x : G) ≠ 1} = Nat.card {x : ↥h.U // x ≠ 1} from
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => ⟨
      fun h h1 => h (by rw [h1, Subgroup.coe_one]),
      fun h h1 => h (Subtype.ext (by rw [h1, Subgroup.coe_one]))⟩))]
  calc Nat.card {x : ↥h.U // x ≠ 1} = ({x : ↥h.U | x ≠ 1} : Set ↥h.U).ncard := rfl
    _ = ((Set.univ : Set ↥h.U) \ {(1 : ↥h.U)}).ncard := by
        rw [show ({x : ↥h.U | x ≠ 1} : Set ↥h.U) = (Set.univ : Set ↥h.U) \ {(1 : ↥h.U)}
          from by ext y; simp]
    _ = (Set.univ : Set ↥h.U).ncard - ({(1 : ↥h.U)} : Set ↥h.U).ncard :=
        Set.ncard_sdiff (Set.subset_univ _)
    _ = Nat.card ↥h.U - 1 := by rw [Set.ncard_univ, Set.ncard_singleton]
    _ = 2 := by rw [h.hU3]

/-- **The criterion.**  `u * s` (`u ∈ U`, `s ∈ S`) is an involution iff `s` is an involution and
`u = 1` or `s` inverts `U`. -/
theorem orderOf_mul_eq_two_iff (hnorm : (h.U.subgroupOf h.C).Normal) {u s : G} (hu : u ∈ h.U)
    (hs : s ∈ h.Sg) :
    orderOf (u * s) = 2 ↔
      (u = 1 ∧ orderOf s = 2) ∨ (u ≠ 1 ∧ orderOf s = 2 ∧ s ∉ h.K) := by
  have hsq : (u * s) * (u * s) = u * (s * u * s⁻¹) * (s * s) := by group
  have hsq1 : ((u * s) * (u * s) = 1) ↔ (s * s = 1 ∧ (u = 1 ∨ s ∉ h.K)) := by
    rcases conj_dichotomy h hnorm hs with hcen | hinv
    · have hmem : s ∈ h.K := (mem_K_iff h hs).mpr hcen
      have hsq' : (u * s) * (u * s) = (u * u) * (s * s) := by rw [hsq, hcen u hu]
      by_cases hu1 : u = 1
      · subst hu1
        simp
      · have hL : ¬ ((u * s) * (u * s) = 1) := by
          intro h1
          have h2 : (u * u) * (s * s) = 1 := by rw [← hsq']; exact h1
          have heq : u * u = (s * s)⁻¹ := mul_eq_one_iff_eq_inv.mp h2
          have hmem2 : u * u ∈ h.U ⊓ h.Sg := by
            refine ⟨h.U.mul_mem hu hu, ?_⟩
            rw [heq]; exact h.Sg.inv_mem (h.Sg.mul_mem hs hs)
          have hbot : u * u ∈ (⊥ : Subgroup G) := by rw [← h.U_inf_Sg]; exact hmem2
          exact sq_ne_one_of_mem h hu hu1 (Subgroup.mem_bot.mp hbot)
        have hR : ¬ (s * s = 1 ∧ (u = 1 ∨ s ∉ h.K)) :=
          fun hc => hc.2.elim hu1 (fun hsK => hsK hmem)
        exact ⟨fun h => absurd h hL, fun h => absurd h hR⟩
    · have hsK' : s ∉ h.K := by
        intro hsK
        have h1 := (mem_K_iff h hs).mp hsK h.σ h.hσU
        have h2 := hinv h.σ h.hσU
        have h3 : s * h.σ * s⁻¹ = h.σ := h1
        rw [h2] at h3
        have heq : h.σ = h.σ⁻¹ := h3.symm
        have h4 : h.σ * h.σ = 1 := by
          have h5 := mul_inv_cancel h.σ
          rw [← heq] at h5
          exact h5
        exact sq_ne_one_of_mem h h.hσU h.hσ1 h4
      have hsq' : (u * s) * (u * s) = s * s := by rw [hsq, hinv u hu]; group
      rw [hsq']
      exact ⟨fun h => ⟨h, Or.inr hsK'⟩, fun h => h.1⟩
  rw [orderOf_eq_two_iff', hsq1]
  constructor
  · rintro ⟨hne, hs2, hdisj⟩
    by_cases hu1 : u = 1
    · refine Or.inl ⟨hu1, orderOf_eq_two_iff'.mpr ⟨?_, hs2⟩⟩
      intro hs1
      exact hne (by rw [hu1, hs1, mul_one])
    · refine Or.inr ⟨hu1, orderOf_eq_two_iff'.mpr ⟨?_, hs2⟩,
        hdisj.elim (fun h => absurd h hu1) id⟩
      intro hs1
      exact (hdisj.elim (fun h => absurd h hu1) id)
        (by rw [hs1]; exact ⟨h.Sg.one_mem, Subgroup.one_mem _⟩)
  · rintro (⟨hu1, hs2⟩ | ⟨hu1, hs2, hsK⟩)
    · subst hu1
      refine ⟨?_, (orderOf_eq_two_iff'.mp hs2).2, Or.inl rfl⟩
      intro h1
      exact (orderOf_eq_two_iff'.mp hs2).1 (by rw [one_mul] at h1; exact h1)
    · refine ⟨?_, (orderOf_eq_two_iff'.mp hs2).2, Or.inr hsK⟩
      intro h1
      have heq : u = s⁻¹ := mul_eq_one_iff_eq_inv.mp h1
      have hmem : u ∈ h.U ⊓ h.Sg := ⟨hu, by rw [heq]; exact h.Sg.inv_mem hs⟩
      have hbot : u ∈ (⊥ : Subgroup G) := by rw [← h.U_inf_Sg]; exact hmem
      exact hu1 (Subgroup.mem_bot.mp hbot)

/-- **The number of involutions of `C_G(z)`, assuming `U ⊴ C_G(z)`, is `9`.** -/
theorem cardInvolutionsCentralizer_of_normal (hnorm : (h.U.subgroupOf h.C).Normal) :
    Nat.card {x : G // x ∈ h.C ∧ orderOf x = 2} = 9 := by
  -- Step 1: the involutions of `C` are exactly the decompositions `u * s` that are involutions.
  have step1 : Nat.card {x : G // x ∈ h.C ∧ orderOf x = 2} =
      Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2} := by
    let f : {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2} →
        {x : G // x ∈ h.C ∧ orderOf x = 2} := fun p =>
      ⟨p.1.1 * p.1.2, h.C.mul_mem (h.U_le_C p.2.1) (h.Sg_le_C p.2.2.1), p.2.2.2⟩
    refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
    · intro p q hpq
      have h1 : p.1.1 * p.1.2 = q.1.1 * q.1.2 := congrArg Subtype.val hpq
      have h2 : q.1.1⁻¹ * p.1.1 = q.1.2 * p.1.2⁻¹ := by
        calc q.1.1⁻¹ * p.1.1 = q.1.1⁻¹ * (p.1.1 * p.1.2) * p.1.2⁻¹ := by group
          _ = q.1.1⁻¹ * (q.1.1 * q.1.2) * p.1.2⁻¹ := by rw [h1]
          _ = q.1.2 * p.1.2⁻¹ := by group
      have h3 : q.1.1⁻¹ * p.1.1 ∈ h.U := h.U.mul_mem (h.U.inv_mem q.2.1) p.2.1
      have h4 : q.1.1⁻¹ * p.1.1 ∈ h.Sg := by
        rw [h2]; exact h.Sg.mul_mem q.2.2.1 (h.Sg.inv_mem p.2.2.1)
      have h5 : q.1.1⁻¹ * p.1.1 = 1 := by
        have hmem : q.1.1⁻¹ * p.1.1 ∈ (⊥ : Subgroup G) := by
          rw [← h.U_inf_Sg]; exact ⟨h3, h4⟩
        exact Subgroup.mem_bot.mp hmem
      have h6 : p.1.1 = q.1.1 := (inv_mul_eq_one.mp h5).symm
      have h7 : p.1.2 = q.1.2 := by
        have hh := h1
        rw [← h6] at hh
        exact mul_left_cancel hh
      exact Subtype.ext (Prod.ext h6 h7)
    · intro x
      obtain ⟨p, hp, -⟩ := decomp h hnorm x.2.1
      refine ⟨⟨(p.1, p.2), hp.1, hp.2.1, ?_⟩, ?_⟩
      · rw [show (p.1, p.2).1 * (p.1, p.2).2 = p.1 * p.2 from rfl, ← hp.2.2]
        exact x.2.2
      · refine Subtype.ext ?_
        exact hp.2.2.symm
  -- Step 2: split off `u = 1`.
  have step2 : Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2} =
      Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2 ∧ p.1 = 1} +
      Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2 ∧ p.1 ≠ 1} :=
    by
      simpa only [and_assoc] using
        card_split (fun p : G × G => p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2)
          (fun p => p.1 = 1)
  -- The `u = 1` part: the involutions of `S` (there are `5`).
  have hP0 : Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2 ∧ p.1 = 1}
      = 5 := by
    rw [show Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧
          orderOf (p.1 * p.2) = 2 ∧ p.1 = 1} = Nat.card {s : G // s ∈ h.Sg ∧ orderOf s = 2}
        from Nat.card_congr ?_]
    · exact card_involutions_Sg h
    refine
      { toFun := fun p => ⟨p.1.2, p.2.2.1, by
          have h1 := p.2.2.2.1
          rw [p.2.2.2.2, one_mul] at h1
          exact h1⟩
        invFun := fun s => ⟨(1, s.1), h.U.one_mem, s.2.1, by rw [one_mul]; exact s.2.2, rfl⟩
        left_inv := fun p => Subtype.ext (Prod.ext p.2.2.2.2.symm rfl)
        right_inv := fun s => Subtype.ext rfl }
  -- The `u ≠ 1` part: `U ∖ {1}` times the involutions of `S ∖ K` (`2 · 2`).
  have hP1 : Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2 ∧ p.1 ≠ 1}
      = 2 * 2 := by
    rw [show Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2 ∧
          p.1 ≠ 1} = Nat.card ({u : G // u ∈ h.U ∧ u ≠ 1} ×
            {s : G // s ∈ h.Sg ∧ orderOf s = 2 ∧ s ∉ h.K}) from Nat.card_congr ?_]
    · rw [Nat.card_prod, card_nonid_U h, card_involutions_Sg_notMem_K h hnorm]
    have haux : ∀ (u s : G), u ∈ h.U → s ∈ h.Sg → u ≠ 1 → orderOf (u * s) = 2 →
        orderOf s = 2 ∧ s ∉ h.K := by
      intro u s hu' hs' hu1' hord
      rcases (orderOf_mul_eq_two_iff h hnorm hu' hs').mp hord with hh | hh
      · exact absurd hh.1 hu1'
      · exact ⟨hh.2.1, hh.2.2⟩
    refine
      { toFun := fun p => (⟨p.1.1, p.2.1, p.2.2.2.2⟩,
          ⟨p.1.2, p.2.2.1, haux p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2.2 p.2.2.2.1⟩)
        invFun := fun q => ⟨(q.1.1, q.2.1), q.1.2.1, q.2.2.1,
          (orderOf_mul_eq_two_iff h hnorm q.1.2.1 q.2.2.1).mpr
            (Or.inr ⟨q.1.2.2, q.2.2.2.1, q.2.2.2.2⟩), q.1.2.2⟩
        left_inv := fun p => Subtype.ext (Prod.ext rfl rfl)
        right_inv := fun q => Prod.ext rfl rfl }
  have hfinal : Nat.card {x : G // x ∈ h.C ∧ orderOf x = 2} = 5 + 2 * 2 := by
    rw [step1, step2, hP0, hP1]
  calc Nat.card {x : G // x ∈ h.C ∧ orderOf x = 2} = 5 + 2 * 2 := hfinal
    _ = 9 := by norm_num


/-! ## Companion count: the involutions of `C` inverting `σ` -/

/-- `U` is abelian. -/
theorem conj_eq_self_of_mem_U {u v : G} (hu : u ∈ h.U) (hv : v ∈ h.U) : u * v * u⁻¹ = v := by
  rw [h.U_eq_zpowers] at hu hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  group

/-- An element of `S` inverts `σ` iff it lies outside `K`. -/
theorem conj_σ_eq_inv_iff_notMem_K (hnorm : (h.U.subgroupOf h.C).Normal) {s : G}
    (hs : s ∈ h.Sg) : s * h.σ * s⁻¹ = h.σ⁻¹ ↔ s ∉ h.K := by
  have hσne : h.σ ≠ h.σ⁻¹ := by
    intro hcon
    have h3 : h.σ * h.σ = 1 := by
      have h4 := mul_inv_cancel h.σ
      rw [← hcon] at h4
      exact h4
    exact sq_ne_one_of_mem h h.hσU h.hσ1 h3
  constructor
  · intro hinv hsK
    have h1 := (mem_K_iff h hs).mp hsK h.σ h.hσU
    exact hσne (by rw [← hinv, h1])
  · intro hsK
    exact conj_eq_inv_of_notMem_K h hnorm hs hsK h.σ h.hσU

/-- An element `u * s` (`u ∈ U`, `s ∈ S`) inverts `σ` iff `s` does. -/
theorem conj_σ_inv_iff (hnorm : (h.U.subgroupOf h.C).Normal) {u s : G} (hu : u ∈ h.U)
    (hs : s ∈ h.Sg) :
    (u * s) * h.σ * (u * s)⁻¹ = h.σ⁻¹ ↔ s * h.σ * s⁻¹ = h.σ⁻¹ := by
  have h1 : (u * s) * h.σ * (u * s)⁻¹ = u * (s * h.σ * s⁻¹) * u⁻¹ := by group
  rw [h1, conj_eq_self_of_mem_U h hu (conj_mem_U h hnorm hs h.hσU)]

/-- **The number of involutions of `C` inverting `σ` is `6`.** -/
theorem card_involutions_inverting_σ (hnorm : (h.U.subgroupOf h.C).Normal) :
    Nat.card {a : G // a ∈ h.C ∧ orderOf a = 2 ∧ a * h.σ * a⁻¹ = h.σ⁻¹} = 6 := by
  -- Step 1: pass to the decomposition `u * s`.
  have step1 : Nat.card {a : G // a ∈ h.C ∧ orderOf a = 2 ∧ a * h.σ * a⁻¹ = h.σ⁻¹} =
      Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2 ∧
        (p.1 * p.2) * h.σ * (p.1 * p.2)⁻¹ = h.σ⁻¹} := by
    let f : {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2 ∧
        (p.1 * p.2) * h.σ * (p.1 * p.2)⁻¹ = h.σ⁻¹} →
        {a : G // a ∈ h.C ∧ orderOf a = 2 ∧ a * h.σ * a⁻¹ = h.σ⁻¹} := fun p =>
      ⟨p.1.1 * p.1.2, h.C.mul_mem (h.U_le_C p.2.1) (h.Sg_le_C p.2.2.1), p.2.2.2.1, p.2.2.2.2⟩
    refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
    · intro p q hpq
      have h1 : p.1.1 * p.1.2 = q.1.1 * q.1.2 := congrArg Subtype.val hpq
      have h2 : q.1.1⁻¹ * p.1.1 = q.1.2 * p.1.2⁻¹ := by
        calc q.1.1⁻¹ * p.1.1 = q.1.1⁻¹ * (p.1.1 * p.1.2) * p.1.2⁻¹ := by group
          _ = q.1.1⁻¹ * (q.1.1 * q.1.2) * p.1.2⁻¹ := by rw [h1]
          _ = q.1.2 * p.1.2⁻¹ := by group
      have h3 : q.1.1⁻¹ * p.1.1 ∈ h.U := h.U.mul_mem (h.U.inv_mem q.2.1) p.2.1
      have h4 : q.1.1⁻¹ * p.1.1 ∈ h.Sg := by
        rw [h2]; exact h.Sg.mul_mem q.2.2.1 (h.Sg.inv_mem p.2.2.1)
      have h5 : q.1.1⁻¹ * p.1.1 = 1 := by
        have hmem : q.1.1⁻¹ * p.1.1 ∈ (⊥ : Subgroup G) := by
          rw [← h.U_inf_Sg]; exact ⟨h3, h4⟩
        exact Subgroup.mem_bot.mp hmem
      have h6 : p.1.1 = q.1.1 := (inv_mul_eq_one.mp h5).symm
      have h7 : p.1.2 = q.1.2 := by
        have hh := h1
        rw [← h6] at hh
        exact mul_left_cancel hh
      exact Subtype.ext (Prod.ext h6 h7)
    · intro x
      obtain ⟨p, hp, -⟩ := decomp h hnorm x.2.1
      refine ⟨⟨(p.1, p.2), hp.1, hp.2.1, ?_, ?_⟩, ?_⟩
      · rw [show (p.1, p.2).1 * (p.1, p.2).2 = p.1 * p.2 from rfl, ← hp.2.2]
        exact x.2.2.1
      · rw [show (p.1, p.2).1 * (p.1, p.2).2 = p.1 * p.2 from rfl, ← hp.2.2]
        exact x.2.2.2
      · refine Subtype.ext ?_
        exact hp.2.2.symm
  -- Step 2: the pair condition is `u ∈ U`, `s ∈ S`, `s` an involution outside `K`.
  have step2 : Nat.card {p : G × G // p.1 ∈ h.U ∧ p.2 ∈ h.Sg ∧ orderOf (p.1 * p.2) = 2 ∧
        (p.1 * p.2) * h.σ * (p.1 * p.2)⁻¹ = h.σ⁻¹} =
      Nat.card ({u : G // u ∈ h.U} × {s : G // s ∈ h.Sg ∧ orderOf s = 2 ∧ s ∉ h.K}) := by
    refine Nat.card_congr ?_
    have haux : ∀ {u s : G}, u ∈ h.U → s ∈ h.Sg → orderOf (u * s) = 2 →
        (u * s) * h.σ * (u * s)⁻¹ = h.σ⁻¹ → orderOf s = 2 ∧ s ∉ h.K := by
      intro u s hu' hs' hord hinv
      have hsK : s ∉ h.K :=
        (conj_σ_eq_inv_iff_notMem_K h hnorm hs').mp
          ((conj_σ_inv_iff h hnorm hu' hs').mp hinv)
      have hsq' : (u * s) * (u * s) = s * s := by
        rw [show (u * s) * (u * s) = u * (s * u * s⁻¹) * (s * s) from by group,
          conj_eq_inv_of_notMem_K h hnorm hs' hsK u hu']
        group
      have hs2 : s * s = 1 := by
        have h1 := (orderOf_eq_two_iff'.mp hord).2
        rwa [hsq'] at h1
      refine ⟨orderOf_eq_two_iff'.mpr ⟨?_, hs2⟩, hsK⟩
      intro hs1
      exact hsK (by rw [hs1]; exact ⟨h.Sg.one_mem, Subgroup.one_mem _⟩)
    refine
      { toFun := fun p => (⟨p.1.1, p.2.1⟩,
          ⟨p.1.2, p.2.2.1, haux p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2⟩)
        invFun := fun q => by
          refine ⟨(q.1.1, q.2.1), q.1.2, q.2.2.1, ?_, ?_⟩
          · by_cases hu1 : q.1.1 = 1
            · exact (orderOf_mul_eq_two_iff h hnorm q.1.2 q.2.2.1).mpr
                (Or.inl ⟨hu1, q.2.2.2.1⟩)
            · exact (orderOf_mul_eq_two_iff h hnorm q.1.2 q.2.2.1).mpr
                (Or.inr ⟨hu1, q.2.2.2.1, q.2.2.2.2⟩)
          · exact (conj_σ_inv_iff h hnorm q.1.2 q.2.2.1).mpr
              ((conj_σ_eq_inv_iff_notMem_K h hnorm q.2.2.1).mpr q.2.2.2.2)
        left_inv := fun p => Subtype.ext (Prod.ext rfl rfl)
        right_inv := fun q => Prod.ext rfl rfl }
  have hval : Nat.card {a : G // a ∈ h.C ∧ orderOf a = 2 ∧ a * h.σ * a⁻¹ = h.σ⁻¹}
      = Nat.card {u : G // u ∈ h.U} * 2 := by
    rw [step1, step2, Nat.card_prod, card_involutions_Sg_notMem_K h hnorm]
  have hU3 : Nat.card {u : G // u ∈ h.U} = 3 := h.hU3
  calc Nat.card {a : G // a ∈ h.C ∧ orderOf a = 2 ∧ a * h.σ * a⁻¹ = h.σ⁻¹}
      = Nat.card {u : G // u ∈ h.U} * 2 := hval
    _ = 3 * 2 := by rw [hU3]
    _ = 6 := by norm_num

end A7InvCtx



end FromCardInvolutionsCentralizerNorm

section FromInvertingSetZsigma



open Subgroup

/-- Conjugating by an element that commutes with `a` fixes `a`. -/
theorem conj_eq_self_of_mul_comm {G : Type*} [Group G] {g a : G} (h : g * a = a * g) :
    g * a * g⁻¹ = a := by
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

/-- In a cyclic group of order `3` (generated by `x`), every element of order `3` is either
`x` or its inverse. -/
theorem eq_or_eq_inv_of_mem_zpowers_of_orderOf_three {G : Type*} [Group G] [Finite G] {x y : G}
    (hy : y ∈ Subgroup.zpowers x) (hx : orderOf x = 3) (hy3 : orderOf y = 3) :
    y = x ∨ y = x⁻¹ := by
  classical
  obtain ⟨i, hi, hiy⟩ :=
    Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf (x := x)).mp hy)
  have hi3 : i < 3 := by rw [hx] at hi; simpa using hi
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx2 : x ^ 2 = x⁻¹ := by
    have h : x ^ 2 * x = 1 := by rw [← pow_succ, hx3]
    exact (inv_eq_of_mul_eq_one_left h).symm
  interval_cases i
  · exfalso
    rw [pow_zero] at hiy
    rw [← hiy] at hy3
    simp at hy3
  · left; rw [pow_one] at hiy; exact hiy.symm
  · right; rw [hx2] at hiy; exact hiy.symm

variable {G : Type*} [Group G] [Finite G]

namespace A7InvCtx

variable (h : A7InvCtx G)

theorem iz_z_mul_z : h.z * h.z = 1 := (orderOf_eq_two_iff'.mp h.hz2).2

theorem iz_z_inv : h.z⁻¹ = h.z := inv_eq_of_mul_eq_one_left h.iz_z_mul_z

theorem iz_σ_pow_three : h.σ ^ 3 = 1 := by
  rw [← h.orderOf_σ]; exact pow_orderOf_eq_one h.σ

/-- `(z * σ) ^ 3 = z`. -/
theorem iz_zσ_pow_three : (h.z * h.σ) ^ 3 = h.z := by
  have hc : Commute h.z h.σ := (commute_iff_eq h.z h.σ).mpr (h.z_central_in_C h.σ_mem_C).symm
  have hz3 : h.z ^ 3 = h.z := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, h.iz_z_mul_z, one_mul]
  rw [hc.mul_pow, hz3, h.iz_σ_pow_three, mul_one]

/-- `(z * σ)⁻¹ = z * σ⁻¹`. -/
theorem iz_zσ_inv : (h.z * h.σ)⁻¹ = h.z * h.σ⁻¹ := by
  have h2 : h.σ⁻¹ * h.z = h.z * h.σ⁻¹ := by
    have := congrArg Inv.inv (h.z_central_in_C h.σ_mem_C)
    simpa [mul_inv_rev, h.iz_z_inv] using this.symm
  rw [mul_inv_rev, h.iz_z_inv]
  exact h2

/-- An element lies in `C_G(U)` exactly when it fixes `σ` by conjugation (recall
`U = zpowers σ`). -/
theorem iz_mem_centralizer_U_iff (s : G) :
    s ∈ Subgroup.centralizer (h.U : Set G) ↔ s * h.σ * s⁻¹ = h.σ := by
  have hc : Subgroup.centralizer (h.U : Set G) = Subgroup.centralizer ({h.σ} : Set G) := by
    rw [h.U_eq_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hc, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hs; rw [hs]; group
  · intro hs
    rw [show s * h.σ = (s * h.σ * s⁻¹) * s from by group, hs]

/-- Conjugating `z * σ` by `σ ^ i * s` (`s ∈ S`) computes to
`z * (σ ^ i * (s * σ * s⁻¹) * σ⁻¹ ^ i)`. -/
theorem iz_conj_calc (s : G) (hs : s ∈ h.Sg) (i : ℕ) :
    (h.σ ^ i * s) * (h.z * h.σ) * (h.σ ^ i * s)⁻¹
      = h.z * (h.σ ^ i * (s * h.σ * s⁻¹) * (h.σ ^ i)⁻¹) := by
  have hsz : s * h.z = h.z * s := h.Sg_centralizes_z hs
  have hzi : h.σ ^ i * h.z = h.z * h.σ ^ i :=
    h.z_central_in_C (h.U_le_C (h.U.pow_mem h.hσU i))
  have hgz : (h.σ ^ i * s) * h.z * (h.σ ^ i * s)⁻¹ = h.z := by
    apply conj_eq_self_of_mul_comm
    rw [mul_assoc, hsz, ← mul_assoc, hzi, mul_assoc]
  calc (h.σ ^ i * s) * (h.z * h.σ) * (h.σ ^ i * s)⁻¹
      = ((h.σ ^ i * s) * h.z * (h.σ ^ i * s)⁻¹) *
          ((h.σ ^ i * s) * h.σ * (h.σ ^ i * s)⁻¹) := by group
    _ = h.z * (h.σ ^ i * (s * h.σ * s⁻¹) * (h.σ ^ i)⁻¹) := by rw [hgz]; group

/-- Since `U ⊴ C_G(z)`, every element of `C_G(z) = U ⊔ S` is of the form `σ ^ i * s` with
`i < 3` and `s ∈ S`. -/
theorem iz_exists_pow_mul_of_mem_C (hUnorm : (h.U.subgroupOf h.C).Normal) {g : G}
    (hg : g ∈ h.C) : ∃ i : ℕ, i < 3 ∧ ∃ s : G, s ∈ h.Sg ∧ g = h.σ ^ i * s := by
  classical
  have hnorm : ∀ a b : G, a ∈ h.U → b ∈ h.C → b * a * b⁻¹ ∈ h.U :=
    (Subgroup.normal_subgroupOf_iff h.U_le_C).mp hUnorm
  have hSg_le_norm : h.Sg ≤ Subgroup.normalizer (h.U : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy; exact hnorm y s hy (h.Sg_le_C hs)
    · intro hy
      have hs' : s⁻¹ ∈ h.Sg := h.Sg.inv_mem hs
      have := hnorm (s * y * s⁻¹) s⁻¹ hy (h.Sg_le_C hs')
      rwa [show s⁻¹ * (s * y * s⁻¹) * (s⁻¹)⁻¹ = y from by group] at this
  have hsup : g ∈ h.U ⊔ h.Sg := by rw [← h.hC]; exact hg
  change g ∈ (↑(h.U ⊔ h.Sg) : Set G) at hsup
  rw [Subgroup.coe_mul_of_right_le_normalizer_left h.U h.Sg hSg_le_norm, Set.mem_mul] at hsup
  obtain ⟨u, hu, s, hs, hus⟩ := hsup
  have hu' : u ∈ Subgroup.zpowers h.σ := by rw [← h.U_eq_zpowers]; exact hu
  obtain ⟨i, hi, hiu⟩ :=
    Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf (x := h.σ)).mp hu')
  refine ⟨i, ?_, s, hs, ?_⟩
  · rw [h.orderOf_σ] at hi; simpa using hi
  · rw [← hus, ← hiu]

end A7InvCtx

/-- **The elements inverting `z * σ`.**

Context `h : Work.A7REC.Char.A7InvCtx G` (defined in
`Submission.Work.A7REC.Char.a7InvolutionCounts`) together with the two structural facts
`|C_G(z)| = 24` and `U ⊴ C_G(z)`.  Here `C := h.C = C_G(z)`, `U = h.U = zpowers h.σ` of order
`3`, `S = h.Sg` the Sylow `2`-subgroup with `S ≅ DihedralGroup 4`, `z ∈ S` of order `2`.

Claim: the set of elements conjugating `z * σ` to its inverse is exactly the set of the
elements `σ ^ i * s` with `i < 3`, `s ∈ S` and `s ∉ C_G(U)` (so `s ∉ C_S(U)`).

Sketch: `(z σ)³ = z³ σ³ = z` (`z` central of order `2` in `C`, `σ` of order `3`, and `z`,`σ`
commute), so an element `g` with `g (zσ) g⁻¹ = (zσ)⁻¹` satisfies `g z g⁻¹ = z`, i.e.
`g ∈ C = C_G(z)`.  Since `|C| = 24 = |U|·|S|` and `U ∩ S = 1`, the multiplication
`U × S → C` is a bijection, so `g = σ^i · s` with `i < 3`, `s ∈ S`.  Conjugating,
`g (zσ) g⁻¹ = z · σ^i (s σ s⁻¹) σ^{-i}`, and `s σ s⁻¹ ∈ U = {1, σ, σ²}` (as `U ⊴ C`), so this
equals `zσ` if `s ∈ C_S(U)` and `zσ⁻¹ = (zσ)⁻¹` otherwise.  Hence `g` inverts `zσ` iff
`s ∉ C_S(U) = C_G(U) ∩ S`. -/
theorem invertingSetZsigma {G : Type*} [Group G] [Finite G]
    (h : A7InvCtx G) (hcardC : Nat.card h.C = 24)
    (hUnorm : (h.U.subgroupOf h.C).Normal) :
    {g : G | g * (h.z * h.σ) * g⁻¹ = (h.z * h.σ)⁻¹}
      = {g : G | ∃ i : ℕ, i < 3 ∧ ∃ s : G, s ∈ h.Sg ∧
          s ∉ Subgroup.centralizer (h.U : Set G) ∧ g = h.σ ^ i * s} := by
  have _ := hcardC
  ext g
  simp only [Set.mem_ofPred_eq]
  constructor
  · -- an element inverting `z * σ` centralizes `z`, hence lies in `C = U ⊔ S`
    intro hg
    have hgzconj : g * h.z * g⁻¹ = h.z := by
      conv_lhs => rw [← h.iz_zσ_pow_three]
      rw [← conj_pow, hg, inv_pow, h.iz_zσ_pow_three, h.iz_z_inv]
    have hgz : g * h.z = h.z * g := by
      have := congrArg (· * g) hgzconj
      simpa [mul_assoc] using this
    have hgC : g ∈ h.C := by
      rw [A7InvCtx.C, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hgz.symm
    obtain ⟨i, hi, s, hs, hgs⟩ := h.iz_exists_pow_mul_of_mem_C hUnorm hgC
    refine ⟨i, hi, s, hs, ?_, hgs⟩
    -- the conjugate `s σ s⁻¹` must be `σ⁻¹`, so `s ∉ C_G(U)`
    intro hsU
    have hconjσ : s * h.σ * s⁻¹ = h.σ := (h.iz_mem_centralizer_U_iff s).mp hsU
    have hEq : h.z * (h.σ ^ i * (s * h.σ * s⁻¹) * (h.σ ^ i)⁻¹) = h.z * h.σ⁻¹ := by
      rw [← h.iz_conj_calc s hs i, ← hgs, hg, h.iz_zσ_inv]
    have hmid : h.σ ^ i * (s * h.σ * s⁻¹) * (h.σ ^ i)⁻¹ = h.σ⁻¹ := mul_left_cancel hEq
    have hx : s * h.σ * s⁻¹ = h.σ⁻¹ := by
      have key : s * h.σ * s⁻¹
          = (h.σ ^ i)⁻¹ * (h.σ ^ i * (s * h.σ * s⁻¹) * (h.σ ^ i)⁻¹) * h.σ ^ i := by
        group
      rw [key, hmid]; group
    rw [hconjσ] at hx
    -- `σ = σ⁻¹` contradicts `orderOf σ = 3`
    have h2 : h.σ ^ 2 = 1 := by
      have h1 : h.σ * h.σ = 1 := by
        have h1' : h.σ * h.σ = h.σ * h.σ⁻¹ := congrArg (fun y => h.σ * y) hx
        rw [h1', mul_inv_cancel]
      rw [pow_two]; exact h1
    have hdvd : orderOf h.σ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [h.orderOf_σ] at hdvd
    norm_num at hdvd
  · -- conversely `σ ^ i * s` with `s ∉ C_G(U)` inverts `z * σ`
    rintro ⟨i, hi, s, hs, hsnot, rfl⟩
    have hconjU : s * h.σ * s⁻¹ ∈ h.U :=
      (Subgroup.normal_subgroupOf_iff h.U_le_C).mp hUnorm h.σ s h.hσU (h.Sg_le_C hs)
    have horder : orderOf (s * h.σ * s⁻¹) = 3 := by
      rw [← MulAut.conj_apply s h.σ, MulEquiv.orderOf_eq (MulAut.conj s) h.σ, h.orderOf_σ]
    rcases eq_or_eq_inv_of_mem_zpowers_of_orderOf_three
        (by rw [← h.U_eq_zpowers]; exact hconjU) h.orderOf_σ horder with hh | hh
    · exact absurd hh (fun hh' => hsnot ((h.iz_mem_centralizer_U_iff s).mpr hh'))
    · calc (h.σ ^ i * s) * (h.z * h.σ) * (h.σ ^ i * s)⁻¹
          = h.z * (h.σ ^ i * (s * h.σ * s⁻¹) * (h.σ ^ i)⁻¹) := h.iz_conj_calc s hs i
        _ = h.z * h.σ⁻¹ := by rw [hh]; group
        _ = (h.z * h.σ)⁻¹ := h.iz_zσ_inv.symm



end FromInvertingSetZsigma

section FromUNormalOfCard



open Subgroup

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

namespace A7InvCtx

variable (h : A7InvCtx G)

/-- `U` viewed as a subgroup of `C = C_G(z)`. -/
abbrev Up : Subgroup ↥h.C := h.U.subgroupOf h.C

/-- `S` viewed as a subgroup of `C = C_G(z)`. -/
abbrev Sp : Subgroup ↥h.C := h.Sg.subgroupOf h.C

/-- The central involution `z` as an element of `C = C_G(z)`. -/
abbrev zp : ↥h.C := ⟨h.z, h.z_mem_C⟩

/-- The element `σ` (of order `3`) as an element of `C`. -/
abbrev σp : ↥h.C := ⟨h.σ, h.σ_mem_C⟩

/-- The element `π` (of order `4`) as an element of `C`. -/
abbrev πp : ↥h.C := ⟨h.π, h.π_mem_C⟩

/-! ## Cardinalities of `U`, `S` inside `C` -/

theorem card_Up : Nat.card ↥h.Up = 3 := by
  rw [show Nat.card ↥(h.U.subgroupOf h.C) = Nat.card ↥h.U from
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.U_le_C).toEquiv, h.hU3]

theorem card_Sp : Nat.card ↥h.Sp = 8 := by
  rw [show Nat.card ↥(h.Sg.subgroupOf h.C) = Nat.card ↥h.Sg from
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Sg_le_C).toEquiv, h.card_Sg]

theorem inf_Up_Sp : h.Up ⊓ h.Sp = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  have h1 : (x : G) ∈ h.U := Subgroup.mem_subgroupOf.mp hx.1
  have h2 : (x : G) ∈ h.Sg := Subgroup.mem_subgroupOf.mp hx.2
  have h3 : (x : G) ∈ (⊥ : Subgroup G) := by
    rw [← h.U_inf_Sg]; exact ⟨h1, h2⟩
  exact Subtype.ext (Subgroup.mem_bot.mp h3)

theorem isComplement' (hcard : Nat.card h.C = 24) : h.Up.IsComplement' h.Sp :=
  Subgroup.isComplement'_of_card_mul_and_disjoint
    (by rw [card_Up h, card_Sp h, hcard])
    (disjoint_iff.mpr (inf_Up_Sp h))

theorem sup_Up_Sp (hcard : Nat.card h.C = 24) : h.Up ⊔ h.Sp = ⊤ :=
  (isComplement' h hcard).sup_eq_top

theorem zp_mem_Sp : h.zp ∈ h.Sp := Subgroup.mem_subgroupOf.mpr h.z_mem_Sg

theorem orderOf_zp : orderOf h.zp = 2 := by
  rw [Subgroup.orderOf_mk]; exact h.hz2

theorem orderOf_σp : orderOf h.σp = 3 := by
  rw [Subgroup.orderOf_mk]; exact h.orderOf_σ

theorem orderOf_πp : orderOf h.πp = 4 := by
  rw [Subgroup.orderOf_mk]; exact h.hπ4

theorem zp_mem_center : h.zp ∈ Subgroup.center ↥h.C := by
  rw [Subgroup.mem_center_iff]
  intro c
  exact Subtype.ext (h.z_central_in_C c.2)

theorem Up_eq_zpowers : h.Up = Subgroup.zpowers h.σp := by
  apply le_antisymm
  · intro x hx
    have hxG : (x : G) ∈ h.U := Subgroup.mem_subgroupOf.mp hx
    rw [h.U_eq_zpowers] at hxG
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxG
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    exact Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)
  · refine Subgroup.zpowers_le.mpr ?_
    exact Subgroup.mem_subgroupOf.mpr h.hσU

theorem σp_mem_Up : h.σp ∈ h.Up := Subgroup.mem_subgroupOf.mpr h.hσU

/-- Cardinality of `H ⊔ K` when `K` normalizes `H` and the two meet trivially (universe-general
version of `card_sup_of_le_normalizer_of_inf_eq_bot`). -/
theorem card_sup_of_le_normalizer_of_inf_eq_bot' {M : Type*} [Group M] [Finite M]
    {H K : Subgroup M} (hn : K ≤ Subgroup.normalizer (H : Set M)) (hd : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  have hcoe : (↑(H ⊔ K) : Set M) = (H : Set M) * (K : Set M) :=
    Subgroup.coe_mul_of_right_le_normalizer_left H K hn
  have hdj : Disjoint H K := disjoint_iff.mpr hd
  have hbij : Function.Bijective
      (fun x : H × K => (⟨(x.1 : M) * x.2, Subgroup.mul_mem_sup x.1.2 x.2.2⟩ : ↥(H ⊔ K))) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      exact Subgroup.mul_injective_of_disjoint hdj (Subtype.ext_iff.mp hxy)
    · intro z
      have hz : (z : M) ∈ (H : Set M) * (K : Set M) := hcoe ▸ z.2
      obtain ⟨a, ha, b, hb, hb_eq⟩ := Set.mem_mul.mp hz
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hb_eq⟩
  calc Nat.card ↥(H ⊔ K) = Nat.card (H × K) := Nat.card_congr (Equiv.ofBijective _ hbij).symm
    _ = Nat.card ↥H * Nat.card ↥K := Nat.card_prod _ _

/-! ## The normalizer of `U` in `C` -/

/-- **`N_C(U) = U ⊔ (N_C(U) ⊓ S)`**, read through the complement `S`. -/
theorem nrmU_eq_sup (hcard : Nat.card h.C = 24) :
    Subgroup.normalizer ((h.Up : Set ↥h.C)) = h.Up ⊔ (Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp) := by
  refine le_antisymm ?_ (sup_le Subgroup.le_normalizer inf_le_left)
  intro n hn
  obtain ⟨⟨u, s⟩, hus⟩ :=
    ((Subgroup.isComplement_iff_bijective h.Up h.Sp).mp (isComplement' h hcard)).2 n
  have hsN : (s : ↥h.C) ∈ Subgroup.normalizer ((h.Up : Set ↥h.C)) := by
    have h1 : (s : ↥h.C) = (u : ↥h.C)⁻¹ * n := by rw [← hus]; group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer u.2)) hn
  rw [← hus]
  exact Subgroup.mul_mem_sup u.2 ⟨hsN, s.2⟩

theorem card_nrmU (hcard : Nat.card h.C = 24) :
    Nat.card ↥(Subgroup.normalizer ((h.Up : Set ↥h.C))) = Nat.card ↥h.Up * Nat.card ↥(Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp) := by
  have hh : Nat.card ↥(h.Up ⊔ (Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp)) = Nat.card ↥h.Up * Nat.card ↥(Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp) :=
    card_sup_of_le_normalizer_of_inf_eq_bot' (by
      intro x hx
      exact hx.1) (by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [Subgroup.mem_inf, Subgroup.mem_inf] at hx
      have hx' : x ∈ h.Up ⊓ h.Sp := ⟨hx.1, hx.2.2⟩
      rw [inf_Up_Sp h] at hx'
      exact Subgroup.mem_bot.mp hx')
  rwa [← nrmU_eq_sup h hcard] at hh

theorem card_normalizer_Up_of_not_normal (hcard : Nat.card h.C = 24)
    (hnn : ¬ h.Up.Normal) : Nat.card ↥(Subgroup.normalizer ((h.Up : Set ↥h.C))) = 6 := by
  classical
  have hcardN := card_nrmU h hcard
  have hzN : h.zp ∈ Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp :=
    ⟨Subgroup.center_le_normalizer _ (zp_mem_center h), zp_mem_Sp h⟩
  have hge2 : 2 ≤ Nat.card ↥(Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp) := by
    have hle : Subgroup.zpowers h.zp ≤ Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp := Subgroup.zpowers_le.mpr hzN
    have h2 : Nat.card ↥(Subgroup.zpowers h.zp) = 2 := by
      rw [Nat.card_zpowers, orderOf_zp h]
    calc 2 = Nat.card ↥(Subgroup.zpowers h.zp) := h2.symm
      _ ≤ Nat.card ↥(Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp) :=
          Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
  have hdvd : Nat.card ↥(Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp) ∣ 2 ^ 3 := by
    have hh := Subgroup.card_dvd_of_le (H := Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp) (K := h.Sp) inf_le_right
    rw [card_Sp h] at hh
    simpa using hh
  obtain ⟨k, hk, hk2⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk1 : 1 ≤ k := by
    rw [hk2] at hge2
    by_contra hcon
    have hk0 : k = 0 := by omega
    rw [hk0] at hge2
    norm_num at hge2
  interval_cases k
  · -- the case `|N ⊓ S| = 2`
    have hm : Nat.card ↥(Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp) = 2 := hk2.trans (by norm_num)
    have hc := hcardN
    rw [hm, card_Up h] at hc
    exact hc.trans (by norm_num)
  · -- the case `|N ⊓ S| = 4` is impossible
    exfalso
    have hm : Nat.card ↥(Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp) = 4 := hk2.trans (by norm_num)
    have hN12 : Nat.card ↥(Subgroup.normalizer ((h.Up : Set ↥h.C))) = 12 := by
      have hc := hcardN
      rw [hm, card_Up h] at hc
      exact hc.trans (by norm_num)
    have hNidx : (Subgroup.normalizer ((h.Up : Set ↥h.C))).index = 2 := by
      have hci := Subgroup.card_mul_index (Subgroup.normalizer ((h.Up : Set ↥h.C)))
      rw [hN12, hcard] at hci
      omega
    haveI hNnormal : (Subgroup.normalizer ((h.Up : Set ↥h.C))).Normal := Subgroup.normal_of_index_eq_two hNidx
    have hNne : Subgroup.normalizer ((h.Up : Set ↥h.C)) ≠ ⊤ := fun htop =>
      hnn (Subgroup.normalizer_eq_top_iff.mp htop)
    obtain ⟨c, hc⟩ : ∃ c : ↥h.C, c ∉ Subgroup.normalizer ((h.Up : Set ↥h.C)) := by
      by_contra hcon
      apply hNne
      rw [eq_top_iff]
      intro x _
      by_contra hx
      exact hcon ⟨x, hx⟩
    set U'' : Subgroup ↥h.C := h.Up.map (MulAut.conj c).toMonoidHom with hU''
    have hU''card : Nat.card ↥U'' = 3 := by
      rw [hU'', show Nat.card ↥(h.Up.map (MulAut.conj c).toMonoidHom) = Nat.card ↥h.Up from
        Nat.card_congr (Subgroup.equivMapOfInjective h.Up (MulAut.conj c).toMonoidHom
          (MulAut.conj c).injective).toEquiv.symm]
      exact card_Up h
    have hU''le : U'' ≤ Subgroup.normalizer ((h.Up : Set ↥h.C)) := by
      intro x hx
      rw [hU'', Subgroup.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rw [← hyx]
      simpa [MulAut.conj_apply] using hNnormal.conj_mem y (Subgroup.le_normalizer hy) c
    have hU''ne : U'' ≠ h.Up := by
      intro heq
      apply hc
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have : (MulAut.conj c) y ∈ U'' := Subgroup.mem_map_of_mem _ hy
        rw [heq] at this
        simpa [MulAut.conj_apply] using this
      · intro hy
        have hmem : (MulAut.conj c) y ∈ U'' := by
          rw [heq]; simpa [MulAut.conj_apply] using hy
        rw [hU'', Subgroup.mem_map] at hmem
        obtain ⟨y', hy', hyy⟩ := hmem
        rw [← (MulAut.conj c).injective hyy]
        exact hy'
    have hdis : h.Up ⊓ U'' = ⊥ := by
      apply Subgroup.card_eq_one.mp
      have hd : Nat.card ↥(h.Up ⊓ U'') ∣ 3 := by
        have hh := Subgroup.card_dvd_of_le (H := h.Up ⊓ U'') (K := h.Up) inf_le_left
        rwa [card_Up h] at hh
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
      · exact h1
      · exfalso
        have heq : h.Up ⊓ U'' = h.Up :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [h3, card_Up h]))
        have heq2 : h.Up = U'' :=
          Subgroup.eq_of_le_of_card_ge (H := h.Up) (K := U'')
            (le_trans (le_of_eq heq.symm) inf_le_right)
            (le_of_eq (by rw [card_Up h, hU''card]))
        exact hU''ne heq2.symm
    have h9 : Nat.card ↥(h.Up ⊔ U'') = 9 := by
      have hh : Nat.card ↥(h.Up ⊔ U'') = Nat.card ↥h.Up * Nat.card ↥U'' :=
        card_sup_of_le_normalizer_of_inf_eq_bot' hU''le hdis
      have hh2 : Nat.card ↥h.Up * Nat.card ↥U'' = 3 * 3 := by
        rw [card_Up h, hU''card]
      exact hh.trans (hh2.trans (by norm_num))
    have hdvd9 : 9 ∣ Nat.card ↥(Subgroup.normalizer ((h.Up : Set ↥h.C))) := by
      have hh := Subgroup.card_dvd_of_le (H := h.Up ⊔ U'') (K := Subgroup.normalizer ((h.Up : Set ↥h.C)))
        (sup_le Subgroup.le_normalizer hU''le)
      rwa [h9] at hh
    rw [hN12] at hdvd9
    norm_num at hdvd9
  · -- the case `|N ⊓ S| = 8` forces `S ≤ N`, hence `U ⊔ S = ⊤ ≤ N`
    exfalso
    have hm : Nat.card ↥(Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp) = 8 := hk2.trans (by norm_num)
    have hNsup' : Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp = h.Sp :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [hm, card_Sp h]))
    have hSpN : h.Sp ≤ Subgroup.normalizer ((h.Up : Set ↥h.C)) := le_trans (le_of_eq hNsup'.symm) inf_le_left
    have htop : (⊤ : Subgroup ↥h.C) ≤ Subgroup.normalizer ((h.Up : Set ↥h.C)) := by
      rw [← sup_Up_Sp h hcard]
      exact sup_le Subgroup.le_normalizer hSpN
    exact hnn (Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop))

theorem normalizer_Up_eq_of_not_normal (hcard : Nat.card h.C = 24)
    (hnn : ¬ h.Up.Normal) : Subgroup.normalizer ((h.Up : Set ↥h.C)) = h.Up ⊔ Subgroup.zpowers h.zp := by
  have hcardN := card_nrmU h hcard
  have h6 := card_normalizer_Up_of_not_normal h hcard hnn
  have hm : Nat.card ↥(Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp) = 2 := by
    rw [hcardN, card_Up h] at h6
    omega
  have hzN : h.zp ∈ Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp :=
    ⟨Subgroup.center_le_normalizer _ (zp_mem_center h), zp_mem_Sp h⟩
  have hzpow : Subgroup.normalizer ((h.Up : Set ↥h.C)) ⊓ h.Sp = Subgroup.zpowers h.zp :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzN)
      (le_of_eq (by rw [hm, Nat.card_zpowers, orderOf_zp h]))).symm
  rw [nrmU_eq_sup h hcard, hzpow]

/-! ## The centralizer of `σ` in `C` -/

theorem centralizer_σp_le (x : ↥h.C) (hx : x ∈ Subgroup.centralizer ({h.σp} : Set ↥h.C)) :
    x ∈ Subgroup.centralizer (h.Up : Set ↥h.C) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  rw [Up_eq_zpowers h] at hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hconj : x * h.σp * x⁻¹ = h.σp := by
    have hh := hx h.σp (Set.mem_singleton _)
    rw [← hh]; group
  have hconj_k : x * h.σp ^ k * x⁻¹ = h.σp ^ k := by
    have h1 : MulAut.conj x h.σp = h.σp := by rw [MulAut.conj_apply]; exact hconj
    calc x * h.σp ^ k * x⁻¹ = MulAut.conj x (h.σp ^ k) := by rw [MulAut.conj_apply]
      _ = (MulAut.conj x h.σp) ^ k := map_zpow _ _ _
      _ = h.σp ^ k := by rw [h1]
  calc h.σp ^ k * x = (x * h.σp ^ k * x⁻¹) * x := by rw [hconj_k]
    _ = x * h.σp ^ k := by group

theorem Up_le_centralizer_σp : h.Up ≤ Subgroup.centralizer ({h.σp} : Set ↥h.C) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst hw
  rw [Up_eq_zpowers h] at hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  simpa using (zpow_mul_comm h.σp k 1).symm

theorem zpowers_zp_le_centralizer_σp :
    Subgroup.zpowers h.zp ≤ Subgroup.centralizer ({h.σp} : Set ↥h.C) := by
  refine Subgroup.zpowers_le.mpr ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst hw
  exact Subgroup.mem_center_iff.mp (zp_mem_center h) h.σp

theorem card_sup_Up_zpowers_zp : Nat.card ↥(h.Up ⊔ Subgroup.zpowers h.zp) = 6 := by
  have hdis : h.Up ⊓ Subgroup.zpowers h.zp = ⊥ := by
    apply Subgroup.card_eq_one.mp
    have hd : Nat.card ↥(h.Up ⊓ Subgroup.zpowers h.zp) ∣ 3 := by
      have hh := Subgroup.card_dvd_of_le (H := h.Up ⊓ Subgroup.zpowers h.zp) (K := h.Up)
        inf_le_left
      rwa [card_Up h] at hh
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact h1
    · exfalso
      have h2 : Nat.card ↥(h.Up ⊓ Subgroup.zpowers h.zp) ∣
          Nat.card ↥(Subgroup.zpowers h.zp) :=
        Subgroup.card_dvd_of_le inf_le_right
      rw [h3, Nat.card_zpowers, orderOf_zp h] at h2
      norm_num at h2
  have hnorm : Subgroup.zpowers h.zp ≤ Subgroup.normalizer ((h.Up : Set ↥h.C)) :=
    Subgroup.zpowers_le.mpr (Subgroup.center_le_normalizer _ (zp_mem_center h))
  have hh : Nat.card ↥(h.Up ⊔ Subgroup.zpowers h.zp) =
      Nat.card ↥h.Up * Nat.card ↥(Subgroup.zpowers h.zp) :=
    card_sup_of_le_normalizer_of_inf_eq_bot' hnorm hdis
  have hh2 : Nat.card ↥h.Up * Nat.card ↥(Subgroup.zpowers h.zp) = 3 * 2 := by
    rw [card_Up h, Nat.card_zpowers, orderOf_zp h]
  exact hh.trans (hh2.trans (by norm_num))

theorem centralizer_σp_eq (hcard : Nat.card h.C = 24) (hnn : ¬ h.Up.Normal) :
    Subgroup.centralizer ({h.σp} : Set ↥h.C) = h.Up ⊔ Subgroup.zpowers h.zp := by
  have hNeq := normalizer_Up_eq_of_not_normal h hcard hnn
  refine le_antisymm ?_ (sup_le (Up_le_centralizer_σp h) (zpowers_zp_le_centralizer_σp h))
  calc Subgroup.centralizer ({h.σp} : Set ↥h.C)
      ≤ Subgroup.centralizer (h.Up : Set ↥h.C) := fun x hx => centralizer_σp_le h x hx
    _ ≤ Subgroup.normalizer ((h.Up : Set ↥h.C)) := Subgroup.centralizer_le_normalizer _
    _ = h.Up ⊔ Subgroup.zpowers h.zp := hNeq

theorem card_centralizer_σp (hcard : Nat.card h.C = 24) (hnn : ¬ h.Up.Normal) :
    Nat.card ↥(Subgroup.centralizer ({h.σp} : Set ↥h.C)) = 6 := by
  rw [centralizer_σp_eq h hcard hnn, card_sup_Up_zpowers_zp h]

theorem centralizer_inv_eq (a : ↥h.C) :
    Subgroup.centralizer ({a⁻¹} : Set ↥h.C) = Subgroup.centralizer ({a} : Set ↥h.C) := by
  apply Subgroup.ext
  intro z
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hh := hx a⁻¹ (Set.mem_singleton _)
    calc a * z = a * (z * a⁻¹) * a := by group
      _ = a * (a⁻¹ * z) * a := by rw [← hh]
      _ = z * a := by group
  · intro hx y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hh := hx a (Set.mem_singleton _)
    calc a⁻¹ * z = a⁻¹ * (z * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * z) * a⁻¹ := by rw [← hh]
      _ = z * a⁻¹ := by group

theorem centralizer_mul_zp_eq :
    Subgroup.centralizer ({h.σp * h.zp} : Set ↥h.C) =
      Subgroup.centralizer ({h.σp} : Set ↥h.C) := by
  have hz : ∀ g : ↥h.C, g * h.zp = h.zp * g :=
    fun g => Subgroup.mem_center_iff.mp (zp_mem_center h) g
  apply Subgroup.ext
  intro g
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hh := hx (h.σp * h.zp) (Set.mem_singleton _)
    have h2 : h.σp * g * h.zp = g * h.σp * h.zp := by
      calc h.σp * g * h.zp = h.σp * (g * h.zp) := by group
        _ = h.σp * (h.zp * g) := by rw [← hz g]
        _ = (h.σp * h.zp) * g := by group
        _ = g * (h.σp * h.zp) := hh
        _ = g * h.σp * h.zp := by group
    exact mul_right_cancel h2
  · intro hx y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hh := hx h.σp (Set.mem_singleton _)
    calc (h.σp * h.zp) * g = h.σp * (h.zp * g) := by group
      _ = h.σp * (g * h.zp) := by rw [hz g]
      _ = (h.σp * g) * h.zp := by group
      _ = (g * h.σp) * h.zp := by rw [hh]
      _ = g * (h.σp * h.zp) := by group

theorem orderOf_σp_mul_zp : orderOf (h.σp * h.zp) = 6 := by
  have hcomm : Commute h.σp h.zp := Subgroup.mem_center_iff.mp (zp_mem_center h) h.σp
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime
    (by rw [orderOf_σp h, orderOf_zp h]; norm_num), orderOf_σp h, orderOf_zp h]

theorem card_centralizer_σp_mul_zp (hcard : Nat.card h.C = 24) (hnn : ¬ h.Up.Normal) :
    Nat.card ↥(Subgroup.centralizer ({h.σp * h.zp} : Set ↥h.C)) = 6 := by
  rw [centralizer_mul_zp_eq h, card_centralizer_σp h hcard hnn]

/-! ## Conjugacy classes -/

theorem ncard_conjugatesOf_four (hcard : Nat.card h.C = 24) {x : ↥h.C}
    (hc : Nat.card ↥(Subgroup.centralizer ({x} : Set ↥h.C)) = 6) :
    (conjugatesOf x).ncard = 4 := by
  have hh := Subgroup.card_mul_index (Subgroup.centralizer ({x} : Set ↥h.C))
  rw [hc, hcard] at hh
  have hidx : (Subgroup.centralizer ({x} : Set ↥h.C)).index = 4 := by omega
  have h2 := Subgroup.index_centralizer_eq_ncard x
  rw [hidx] at h2
  exact h2.symm

theorem conjugatesOf_order_three {y : ↥h.C} (hy : y ∈ conjugatesOf h.σp) :
    orderOf y = 3 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hy
  rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_σp h]

theorem conjugatesOf_order_six {y : ↥h.C} (hy : y ∈ conjugatesOf (h.σp * h.zp)) :
    orderOf y = 6 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hy
  rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_σp_mul_zp h]

/-- `σ⁻¹` is not conjugate to `σ` (any conjugating element normalizes `U`, hence centralizes
`σ`). -/
theorem not_isConj_σp_inv (hcard : Nat.card h.C = 24) (hnn : ¬ h.Up.Normal) :
    ¬ IsConj h.σp h.σp⁻¹ := by
  intro hconj
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hmemN : c ∈ Subgroup.normalizer ((h.Up : Set ↥h.C)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Up_eq_zpowers h]
    have hconj_k : ∀ k : ℤ, c * h.σp ^ k * c⁻¹ = h.σp ^ (-k) := by
      intro k
      calc c * h.σp ^ k * c⁻¹ = MulAut.conj c (h.σp ^ k) := by rw [MulAut.conj_apply]
        _ = (MulAut.conj c h.σp) ^ k := map_zpow _ _ _
        _ = (h.σp⁻¹) ^ k := by rw [MulAut.conj_apply, hc]
        _ = h.σp ^ (-k) := by rw [inv_zpow, zpow_neg]
    have hconj_kinv : ∀ k : ℤ, c⁻¹ * h.σp ^ k * c = h.σp ^ (-k) := by
      intro k
      have hcinv : c⁻¹ * h.σp * c = h.σp⁻¹ := by
        have h2 : c⁻¹ * h.σp⁻¹ * c = h.σp := by
          calc c⁻¹ * h.σp⁻¹ * c = c⁻¹ * (c * h.σp * c⁻¹) * c := by rw [hc]
            _ = h.σp := by group
        calc c⁻¹ * h.σp * c = (c⁻¹ * h.σp⁻¹ * c)⁻¹ := by group
          _ = (h.σp)⁻¹ := by rw [h2]
          _ = h.σp⁻¹ := by group
      calc c⁻¹ * h.σp ^ k * c = MulAut.conj c⁻¹ (h.σp ^ k) := by
            rw [MulAut.conj_apply, inv_inv]
        _ = (MulAut.conj c⁻¹ h.σp) ^ k := map_zpow _ _ _
        _ = (h.σp⁻¹) ^ k := by rw [MulAut.conj_apply, inv_inv, hcinv]
        _ = h.σp ^ (-k) := by rw [inv_zpow, zpow_neg]
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact Subgroup.mem_zpowers_iff.mpr ⟨-k, (hconj_k k).symm⟩
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
      rw [← hconj_kinv k, hk]
      group
  have hcen : c ∈ Subgroup.centralizer ({h.σp} : Set ↥h.C) := by
    rw [centralizer_σp_eq h hcard hnn, ← normalizer_Up_eq_of_not_normal h hcard hnn]
    exact hmemN
  have hfix : c * h.σp * c⁻¹ = h.σp := by
    have hh := (Subgroup.mem_centralizer_iff.mp hcen) h.σp (Set.mem_singleton _)
    rw [← hh]; group
  rw [hfix] at hc
  have h2 : h.σp * h.σp = 1 := by
    have hh := mul_inv_cancel h.σp
    rwa [← hc] at hh
  have hdvd : orderOf h.σp ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact h2
  rw [orderOf_σp h] at hdvd
  omega

/-- `(σ z)⁻¹` is not conjugate to `σ z`. -/
theorem not_isConj_σpz_inv (hcard : Nat.card h.C = 24) (hnn : ¬ h.Up.Normal) :
    ¬ IsConj (h.σp * h.zp) (h.σp * h.zp)⁻¹ := by
  intro hconj
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hzc : ∀ g : ↥h.C, g * h.zp = h.zp * g :=
    fun g => Subgroup.mem_center_iff.mp (zp_mem_center h) g
  have hz_inv : h.zp⁻¹ = h.zp := by
    have h2 : h.zp * h.zp = 1 := by
      rw [← pow_two, ← orderOf_zp h]; exact pow_orderOf_eq_one _
    exact inv_eq_of_mul_eq_one_left h2
  have hcsig : c * h.σp * c⁻¹ = h.σp⁻¹ := by
    have h1 : (h.σp * h.zp)⁻¹ = h.σp⁻¹ * h.zp := by
      rw [mul_inv_rev, hz_inv]
      exact (hzc h.σp⁻¹).symm
    rw [h1] at hc
    have h2 : c * h.σp * c⁻¹ * h.zp = h.σp⁻¹ * h.zp := by
      calc c * h.σp * c⁻¹ * h.zp = c * h.σp * (c⁻¹ * h.zp) := by group
        _ = c * h.σp * (h.zp * c⁻¹) := by rw [← hzc c⁻¹]
        _ = c * (h.σp * h.zp) * c⁻¹ := by group
        _ = h.σp⁻¹ * h.zp := hc
    exact mul_right_cancel h2
  exact not_isConj_σp_inv h hcard hnn (isConj_iff.mpr ⟨c, hcsig⟩)

/-! ## The element counts -/

theorem card_order_two_ge_five : 5 ≤ Nat.card {x : ↥h.C // orderOf x = 2} := by
  have hinj : Function.Injective
      (fun s : {s : G // s ∈ h.Sg ∧ orderOf s = 2} =>
        (⟨⟨s.1, h.Sg_le_C s.2.1⟩, by rw [Subgroup.orderOf_mk]; exact s.2.2⟩ :
          {x : ↥h.C // orderOf x = 2})) := by
    intro a b hab
    have h1 : (a.1 : G) = (b.1 : G) := by
      have hh := congrArg (fun t : {x : ↥h.C // orderOf x = 2} => (((t.1 : ↥h.C) : G))) hab
      simpa using hh
    exact Subtype.ext h1
  have hh := Nat.card_le_card_of_injective _ hinj
  rwa [card_involutions_Sg h] at hh

theorem card_order_three_ge_eight (hcard : Nat.card h.C = 24) (hnn : ¬ h.Up.Normal) :
    8 ≤ Nat.card {x : ↥h.C // orderOf x = 3} := by
  have hc1 : Nat.card ↥(Subgroup.centralizer ({h.σp} : Set ↥h.C)) = 6 :=
    card_centralizer_σp h hcard hnn
  have hc2 : Nat.card ↥(Subgroup.centralizer ({h.σp⁻¹} : Set ↥h.C)) = 6 := by
    rw [centralizer_inv_eq h, hc1]
  have hA : (conjugatesOf h.σp).ncard = 4 := ncard_conjugatesOf_four h hcard hc1
  have hB : (conjugatesOf h.σp⁻¹).ncard = 4 := ncard_conjugatesOf_four h hcard hc2
  have hsub : (conjugatesOf h.σp) ∪ (conjugatesOf h.σp⁻¹) ⊆ {x : ↥h.C | orderOf x = 3} := by
    intro y hy
    rcases hy with hy | hy
    · exact conjugatesOf_order_three h hy
    · obtain ⟨c, hc⟩ := isConj_iff.mp hy
      rw [← hc]
      change orderOf (c * h.σp⁻¹ * c⁻¹) = 3
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_inv, orderOf_σp h]
  have hdis : Disjoint (conjugatesOf h.σp) (conjugatesOf h.σp⁻¹) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    refine not_isConj_σp_inv h hcard hnn ?_
    exact (show IsConj h.σp y from hy1).trans (show IsConj y h.σp⁻¹ from hy2.symm)
  have hunion : ((conjugatesOf h.σp) ∪ (conjugatesOf h.σp⁻¹)).ncard = 8 := by
    rw [Set.ncard_union_eq hdis, hA, hB]
  have hle : 8 ≤ ({x : ↥h.C | orderOf x = 3} : Set ↥h.C).ncard := by
    have hh := Set.ncard_le_ncard hsub
    rwa [hunion] at hh
  calc (8 : ℕ) ≤ ({x : ↥h.C | orderOf x = 3} : Set ↥h.C).ncard := hle
    _ = Nat.card {x : ↥h.C // orderOf x = 3} := (Nat.card_coe_set_eq _).symm

theorem card_order_six_ge_eight (hcard : Nat.card h.C = 24) (hnn : ¬ h.Up.Normal) :
    8 ≤ Nat.card {x : ↥h.C // orderOf x = 6} := by
  have hc1 : Nat.card ↥(Subgroup.centralizer ({h.σp * h.zp} : Set ↥h.C)) = 6 :=
    card_centralizer_σp_mul_zp h hcard hnn
  have hc2 : Nat.card ↥(Subgroup.centralizer ({(h.σp * h.zp)⁻¹} : Set ↥h.C)) = 6 := by
    rw [centralizer_inv_eq h, hc1]
  have hA : (conjugatesOf (h.σp * h.zp)).ncard = 4 := ncard_conjugatesOf_four h hcard hc1
  have hB : (conjugatesOf (h.σp * h.zp)⁻¹).ncard = 4 :=
    ncard_conjugatesOf_four h hcard hc2
  have hsub : (conjugatesOf (h.σp * h.zp)) ∪ (conjugatesOf (h.σp * h.zp)⁻¹) ⊆
      {x : ↥h.C | orderOf x = 6} := by
    intro y hy
    rcases hy with hy | hy
    · exact conjugatesOf_order_six h hy
    · obtain ⟨c, hc⟩ := isConj_iff.mp hy
      rw [← hc]
      change orderOf (c * (h.σp * h.zp)⁻¹ * c⁻¹) = 6
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_inv, orderOf_σp_mul_zp h]
  have hdis : Disjoint (conjugatesOf (h.σp * h.zp)) (conjugatesOf (h.σp * h.zp)⁻¹) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    refine not_isConj_σpz_inv h hcard hnn ?_
    exact (show IsConj (h.σp * h.zp) y from hy1).trans
      (show IsConj y (h.σp * h.zp)⁻¹ from hy2.symm)
  have hunion : ((conjugatesOf (h.σp * h.zp)) ∪ (conjugatesOf (h.σp * h.zp)⁻¹)).ncard = 8 := by
    rw [Set.ncard_union_eq hdis, hA, hB]
  have hle : 8 ≤ ({x : ↥h.C | orderOf x = 6} : Set ↥h.C).ncard := by
    have hh := Set.ncard_le_ncard hsub
    rwa [hunion] at hh
  calc (8 : ℕ) ≤ ({x : ↥h.C | orderOf x = 6} : Set ↥h.C).ncard := hle
    _ = Nat.card {x : ↥h.C // orderOf x = 6} := (Nat.card_coe_set_eq _).symm

theorem card_centralizer_πp (hcard : Nat.card h.C = 24) :
    Nat.card ↥(Subgroup.centralizer ({h.πp} : Set ↥h.C)) = 4 := by
  have hEq : Subgroup.centralizer ({h.πp} : Set ↥h.C) =
      (Subgroup.zpowers h.π).subgroupOf h.C := by
    ext g
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      rw [← h.hCπ, Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      have hh := congrArg (fun t : ↥h.C => (t : G)) (hg h.πp (Set.mem_singleton _))
      simpa using hh
    · intro hg
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      have hh : h.π * (g : G) = (g : G) * h.π :=
        (Subgroup.mem_centralizer_iff.mp (by rw [h.hCπ]; exact hg)) h.π (Set.mem_singleton _)
      exact Subtype.ext (by simpa using hh)
  rw [hEq, show Nat.card ↥((Subgroup.zpowers h.π).subgroupOf h.C) =
      Nat.card ↥(Subgroup.zpowers h.π) from
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr h.π_mem_C)).toEquiv,
    Nat.card_zpowers, h.hπ4]

theorem card_order_four_ge_six (hcard : Nat.card h.C = 24) :
    6 ≤ Nat.card {x : ↥h.C // orderOf x = 4} := by
  have hc : Nat.card ↥(Subgroup.centralizer ({h.πp} : Set ↥h.C)) = 4 :=
    card_centralizer_πp h hcard
  have hcardc := Subgroup.card_mul_index (Subgroup.centralizer ({h.πp} : Set ↥h.C))
  rw [hc, hcard] at hcardc
  have hidx : (Subgroup.centralizer ({h.πp} : Set ↥h.C)).index = 6 := by omega
  have hA : (conjugatesOf h.πp).ncard = 6 := by
    have h2 := Subgroup.index_centralizer_eq_ncard h.πp
    rw [hidx] at h2
    exact h2.symm
  have hsub : conjugatesOf h.πp ⊆ {x : ↥h.C | orderOf x = 4} := by
    intro y hy
    obtain ⟨c, hc'⟩ := isConj_iff.mp hy
    rw [← hc']
    change orderOf (c * h.πp * c⁻¹) = 4
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_πp h]
  have hle : 6 ≤ ({x : ↥h.C | orderOf x = 4} : Set ↥h.C).ncard := by
    have hh := Set.ncard_le_ncard hsub
    rwa [hA] at hh
  calc (6 : ℕ) ≤ ({x : ↥h.C | orderOf x = 4} : Set ↥h.C).ncard := hle
    _ = Nat.card {x : ↥h.C // orderOf x = 4} := (Nat.card_coe_set_eq _).symm

end A7InvCtx

/-- **Given `|C_G(z)| = 24`, the subgroup `U` of order `3` is normal in `C_G(z)`.**

Context `h : Work.A7REC.Char.A7InvCtx G` (so `C = h.C = U ⊔ S`, `|U| = 3`, `S ≅ D₈` with
`|S| = 8`, `U ⊓ S = ⊥`, and `π ∈ S` of order `4` with `C_G(π) = ⟨π⟩`), together with
`Nat.card h.C = 24`.

Note: the hypothesis `Nat.card h.C = 24` is NOT automatic from `A7InvCtx` (the product formula
`|U·S| = |U|·|S|/|U ⊓ S| = 24` only gives `24 ≤ |U ⊔ S| = h.C`); it is the global input supplied
by the sibling lemma `Work.A7REC.Char.cardCentralizerZSimple`.

Two valid arguments:
* (Burnside) if `U ⋬ C`, then `n₃(C) = 4`, `N_C(P) = P × ⟨z⟩ ≅ C₆` is the normalizer of a
  Sylow `3`-subgroup `P`, and Burnside's normal `p`-complement result gives `S ⊴ C`; writing
  `C = S ⋊ C₃` (with `U` a complement) the action `C₃ → Aut(D₈)` is trivial by coprimality, so
  `U ⊴ C`, contradiction;
* (element count) if `U ⋬ C` then `C` has `8` elements of order `3` and (each lying in exactly
  one of the four normalizers `≅ C₆`) `8` elements of order `6`, and no element of order `12`;
  so `#inv + #(order 4) = 24 - 1 - 8 - 8 = 7`, forcing `#inv = 5, #(order 4) = 2`; but `π` has
  `[C : C_C(π)] = 24/4 = 6` conjugates in `C`, all of order `4`, a contradiction. -/
theorem u_normal_of_card {G : Type*} [Group G] [Finite G]
    (h : A7InvCtx G) (hcard : Nat.card h.C = 24) :
    (h.U.subgroupOf h.C).Normal := by
  by_contra hnn
  have h2 := A7InvCtx.card_order_two_ge_five h
  have h3 := A7InvCtx.card_order_three_ge_eight h hcard hnn
  have h4 := A7InvCtx.card_order_four_ge_six h hcard
  have h6 := A7InvCtx.card_order_six_ge_eight h hcard hnn
  have hcount := Work.A7REC.Char.card_count_orders_le (H := ↥h.C)
  have hcard' : Nat.card ↥h.C = 24 := hcard
  omega



end FromUNormalOfCard

end InvPairsRepro

/-- **The second and third involution-pair counts** `i(z) = 8` and `i(zσ) = 6`, for the raw
data of `Work.A7REC.A7InvolutionCountsProp`.

Both counts reduce to counting involutions: `i(z) = 9 - 1` (the involutions of `C_G(z)`, minus
`z` itself) and `i(zσ) = 6` (the involutions of `C_G(z)` inverting `σ`). -/
theorem invPairsZAndZsigma {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : Nat.card G = 2520) (S : Sylow 2 G) (z : G) (U : Subgroup G) (π σ : G)
    (hzS : z ∈ (S : Subgroup G)) (hz2 : orderOf z = 2)
    (hC : Subgroup.centralizer ({z} : Set G) = U ⊔ (S : Subgroup G)) (hU3 : Nat.card U = 3)
    (hσU : σ ∈ U) (hσ1 : σ ≠ 1)
    (hπS : π ∈ (S : Subgroup G)) (hπ4 : orderOf π = 4)
    (hCπ : Subgroup.centralizer ({π} : Set G) = Subgroup.zpowers π)
    (hSdih : Nonempty ((S : Subgroup G) ≃* DihedralGroup 4)) :
    Work.A7REC.C7invPairCount z = 8 ∧ Work.A7REC.C7invPairCount (z * σ) = 6 := by
  classical
  let h : InvPairsRepro.A7InvCtx G :=
    { S := S, hSdih := hSdih, z := z, hzS := hzS, hz2 := hz2, U := U, hU3 := hU3,
      hC := hC, π := π, hπS := hπS, hπ4 := hπ4, hCπ := hCπ, σ := σ, hσU := hσU,
      hσ1 := hσ1 }
  have hcardC : Nat.card h.C = 24 :=
    Work.A7REC.Char.cardCentralizerZSimple hcard S z U hzS hz2 hC hU3 hSdih
  have hUnorm : (h.U.subgroupOf h.C).Normal :=
    InvPairsRepro.u_normal_of_card h hcardC
  have hInvC : Nat.card {x : G // x ∈ h.C ∧ orderOf x = 2} = 9 :=
    InvPairsRepro.A7InvCtx.cardInvolutionsCentralizer_of_normal h hUnorm
  have hInvσ : Nat.card {a : G // a ∈ h.C ∧ orderOf a = 2 ∧ a * h.σ * a⁻¹ = h.σ⁻¹} = 6 :=
    InvPairsRepro.A7InvCtx.card_involutions_inverting_σ h hUnorm
  constructor
  · -- ## `i(z) = 8`
    rw [InvPairsRepro.ncard_pair_eq_ncard_invSet]
    show (InvPairsRepro.invSet h.z).ncard = 8
    have hAcard : ({x : G | x ∈ h.C ∧ orderOf x = 2} : Set G).ncard = 9 := by
      rw [show ({x : G | x ∈ h.C ∧ orderOf x = 2} : Set G).ncard
          = Nat.card {x : G // x ∈ h.C ∧ orderOf x = 2} from rfl]
      exact hInvC
    have hset : InvPairsRepro.invSet h.z
        = ({x : G | x ∈ h.C ∧ orderOf x = 2} : Set G) \ {h.z} := by
      ext u
      rw [InvPairsRepro.invSet]
      simp only [Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hu2, hinv, hux⟩
        rw [h.iz_z_inv] at hinv
        have hcomm : u * h.z = h.z * u := by
          have := congrArg (· * u) hinv
          simpa [mul_assoc] using this
        refine ⟨⟨?_, hu2⟩, ?_⟩
        · exact (Subgroup.mem_centralizer_singleton_iff).mpr hcomm
        · intro huz
          rw [huz, h.iz_z_mul_z, orderOf_one] at hux
          exact absurd hux (by norm_num)
      · rintro ⟨⟨huC, hu2⟩, huz⟩
        have hcomm : u * h.z = h.z * u := (Subgroup.mem_centralizer_singleton_iff).mp huC
        have hu2m : u * u = 1 := ((InvPairsRepro.orderOf_eq_two_iff' (u := u)).mp hu2).2
        refine ⟨hu2, ?_, ?_⟩
        · have h1 : u * h.z * u⁻¹ = h.z := by
            rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
          rw [h1, h.iz_z_inv]
        · refine (InvPairsRepro.orderOf_eq_two_iff' (u := u * h.z)).mpr ⟨?_, ?_⟩
          · intro h1
            exact huz (by
              have hh := mul_eq_one_iff_eq_inv.mp h1
              rwa [h.iz_z_inv] at hh)
          · calc (u * h.z) * (u * h.z) = u * (h.z * u) * h.z := by group
              _ = u * (u * h.z) * h.z := by rw [← hcomm]
              _ = (u * u) * (h.z * h.z) := by group
              _ = 1 := by rw [hu2m, h.iz_z_mul_z, mul_one]
    have hsub : ({h.z} : Set G) ⊆ ({x : G | x ∈ h.C ∧ orderOf x = 2} : Set G) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨h.z_mem_C, h.hz2⟩
    rw [hset, Set.ncard_sdiff hsub, Set.ncard_singleton, hAcard]
  · -- ## `i(zσ) = 6`
    rw [InvPairsRepro.ncard_pair_eq_ncard_invSet]
    show (InvPairsRepro.invSet (h.z * h.σ)).ncard = 6
    have hBcard :
        ({a : G | a ∈ h.C ∧ orderOf a = 2 ∧ a * h.σ * a⁻¹ = h.σ⁻¹} : Set G).ncard = 6 := by
      rw [show ({a : G | a ∈ h.C ∧ orderOf a = 2 ∧ a * h.σ * a⁻¹ = h.σ⁻¹} : Set G).ncard
          = Nat.card {a : G // a ∈ h.C ∧ orderOf a = 2 ∧ a * h.σ * a⁻¹ = h.σ⁻¹} from rfl]
      exact hInvσ
    have hset : InvPairsRepro.invSet (h.z * h.σ)
        = {a : G | a ∈ h.C ∧ orderOf a = 2 ∧ a * h.σ * a⁻¹ = h.σ⁻¹} := by
      ext u
      rw [InvPairsRepro.invSet]
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨hu2, hinvzσ, hux⟩
        have hzσcomm : h.σ * h.z = h.z * h.σ := h.z_central_in_C h.σ_mem_C
        have hz_conj : u * h.z * u⁻¹ = h.z := by
          calc u * h.z * u⁻¹ = u * (h.z * h.σ) ^ 3 * u⁻¹ := by rw [h.iz_zσ_pow_three]
            _ = MulAut.conj u ((h.z * h.σ) ^ 3) := by rw [MulAut.conj_apply]
            _ = (MulAut.conj u (h.z * h.σ)) ^ 3 := by rw [map_pow]
            _ = (u * (h.z * h.σ) * u⁻¹) ^ 3 := by rw [MulAut.conj_apply]
            _ = ((h.z * h.σ)⁻¹) ^ 3 := by rw [hinvzσ]
            _ = ((h.z * h.σ) ^ 3)⁻¹ := by rw [inv_pow]
            _ = h.z⁻¹ := by rw [h.iz_zσ_pow_three]
            _ = h.z := h.iz_z_inv
        have hcommz : u * h.z = h.z * u := by
          have := congrArg (· * u) hz_conj
          simpa [mul_assoc] using this
        have huC : u ∈ h.C := (Subgroup.mem_centralizer_singleton_iff).mpr hcommz
        have hucz : u * h.z * u⁻¹ = h.z := by
          rw [hcommz, mul_assoc, mul_inv_cancel, mul_one]
        have hzσinvcomm : h.σ⁻¹ * h.z = h.z * h.σ⁻¹ :=
          (Subgroup.mem_centralizer_singleton_iff).mp (h.C.inv_mem h.σ_mem_C)
        have huσ_inv : u * h.σ * u⁻¹ = h.σ⁻¹ := by
          have key : u * (h.z * h.σ) * u⁻¹ = h.z * (u * h.σ * u⁻¹) := by
            calc u * (h.z * h.σ) * u⁻¹ = (u * h.z * u⁻¹) * (u * h.σ * u⁻¹) := by group
              _ = h.z * (u * h.σ * u⁻¹) := by rw [hucz]
          have h2 : h.z * (u * h.σ * u⁻¹) = h.z * h.σ⁻¹ := by
            rw [← key, hinvzσ, mul_inv_rev, h.iz_z_inv, hzσinvcomm]
          exact mul_left_cancel h2
        exact ⟨huC, hu2, huσ_inv⟩
      · rintro ⟨huC, hu2, huσ_inv⟩
        have hcommz : u * h.z = h.z * u := (Subgroup.mem_centralizer_singleton_iff).mp huC
        have hzσcomm : h.σ * h.z = h.z * h.σ := h.z_central_in_C h.σ_mem_C
        have hzσinvcomm : h.σ⁻¹ * h.z = h.z * h.σ⁻¹ :=
          (Subgroup.mem_centralizer_singleton_iff).mp (h.C.inv_mem h.σ_mem_C)
        have hu2m : u * u = 1 := ((InvPairsRepro.orderOf_eq_two_iff' (u := u)).mp hu2).2
        have hucz : u * h.z * u⁻¹ = h.z := by
          rw [hcommz, mul_assoc, mul_inv_cancel, mul_one]
        have h1zσinv : u * (h.z * h.σ) * u⁻¹ = (h.z * h.σ)⁻¹ := by
          calc u * (h.z * h.σ) * u⁻¹ = (u * h.z * u⁻¹) * (u * h.σ * u⁻¹) := by group
            _ = h.z * h.σ⁻¹ := by rw [hucz, huσ_inv]
            _ = (h.z * h.σ)⁻¹ := by rw [mul_inv_rev, h.iz_z_inv, hzσinvcomm]
        refine ⟨hu2, h1zσinv, ?_⟩
        have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2m
        have h3 : u * (h.z * h.σ) * u = (h.z * h.σ)⁻¹ := by
          calc u * (h.z * h.σ) * u = u * (h.z * h.σ) * u⁻¹ := by rw [hu_inv]
            _ = (h.z * h.σ)⁻¹ := h1zσinv
        have hsq : (u * (h.z * h.σ)) * (u * (h.z * h.σ)) = 1 := by
          rw [show (u * (h.z * h.σ)) * (u * (h.z * h.σ))
                = (u * (h.z * h.σ) * u) * (h.z * h.σ) from by group,
              h3, inv_mul_cancel]
        refine (InvPairsRepro.orderOf_eq_two_iff' (u := u * (h.z * h.σ))).mpr ⟨?_, hsq⟩
        intro h1
        have hu_eq : u = (h.z * h.σ)⁻¹ := mul_eq_one_iff_eq_inv.mp h1
        have hx2 : (h.z * h.σ) * (h.z * h.σ) = h.σ ^ 2 := by
          calc (h.z * h.σ) * (h.z * h.σ) = h.z * (h.σ * h.z) * h.σ := by group
            _ = h.z * (h.z * h.σ) * h.σ := by rw [hzσcomm]
            _ = (h.z * h.z) * (h.σ * h.σ) := by group
            _ = h.σ ^ 2 := by rw [h.iz_z_mul_z, one_mul, pow_two]
        have hx2ne : (h.z * h.σ) * (h.z * h.σ) ≠ 1 := by
          intro hh
          rw [hx2] at hh
          have hdvd : orderOf h.σ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hh
          rw [h.orderOf_σ] at hdvd
          norm_num at hdvd
        apply hx2ne
        have h2 : ((h.z * h.σ) * (h.z * h.σ))⁻¹ = 1 := by
          rw [mul_inv_rev, ← hu_eq]
          exact hu2m
        exact inv_eq_one.mp h2
    rw [hset, hBcard]

end Work.A7REC.Char
