import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.QSZ_invH_le_centerQ
import Submission.Work.ZassenhausSuzuki.QSZ_isCyclic_twoPoint
import Submission.Work.ZassenhausSuzuki.QSZ_rho_pow_eq_sigma
import Submission.Work.ZassenhausSuzuki.twoPoint_inverted
import Submission.Work.ZassenhausPSL2.Feit.qomegaData_nonempty
import Submission.Work.ZassenhausPSL2.ZData.card_dStab_eq_card_involutions
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q
import Submission.Work.ZassenhausPSL2.ZData.three_le_card_twoPoint
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.ChV12.structureIdentity
import Submission.Work.ThmF.ChV12.lemma4
import Submission.Work.ThmF.ChV12.corProp2
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.Higman.Defs
import Submission.Work.Higman.center_sq_eq_one
import Submission.Work.ThmG.rankOne_index

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-! ## Phase 1: `Inv(H) = Inv(Q)`, `Ksub = Kset = D`, and `IsSuzukiTwoGroup ↥Q` -/

/-- The involutions of `H` are exactly the involutions of `Q`. -/
theorem involutions_H_eq_involutions_Q (h : IsSplitRankOne H Q t) (h2 : IsPGroup 2 Q) :
    involutions (H : Set G) = involutions (Q : Set G) := by
  ext u
  constructor
  · intro hu
    exact ⟨(Work.ThmF.mem_centerOf.mp (QSZ_invH_le_centerQ h h2 u hu)).1, hu.2⟩
  · intro hu
    exact ⟨h.le hu.1, hu.2⟩

/-- The involutions of `H` commute pairwise. -/
theorem invH_commute (h : IsSplitRankOne H Q t) (h2 : IsPGroup 2 Q) :
    ∀ u ∈ involutions (H : Set G), ∀ v ∈ involutions (H : Set G), u * v = v * u := by
  intro u hu v hv
  have hu' := Work.ThmF.mem_centerOf.mp (QSZ_invH_le_centerQ h h2 u hu)
  have hv' := Work.ThmF.mem_centerOf.mp (QSZ_invH_le_centerQ h h2 v hv)
  exact hu'.2 v hv'.1

/-- In the Zassenhaus split rank-one setting, `Kset H t = D = twoPoint H t`. -/
theorem Kset_eq_twoPoint (h : IsSplitRankOne H Q t) (hZ : IsZassenhaus H) (h2 : IsPGroup 2 Q) :
    Work.ThmF.Kset H t = (twoPoint H t : Set G) := by
  ext x
  rw [Work.ThmF.mem_Kset_iff]
  exact ⟨fun hx => hx.1,
    fun hx => ⟨hx, twoPoint_inverted h hZ (Work.ZassenhausPSL2.Feit.Q_ne_bot_of_split h) h2 x hx⟩⟩

/-- In the Zassenhaus split rank-one setting, `Ksub H t = D = twoPoint H t`. -/
theorem mem_Ksub_iff (h : IsSplitRankOne H Q t) (hZ : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (x : G) : x ∈ Work.ThmF.Ksub H t ↔ x ∈ twoPoint H t := by
  have h1 : Work.ThmF.Ksub H t = twoPoint H t := by
    rw [Work.ThmF.Ksub, Kset_eq_twoPoint h hZ h2, Subgroup.closure_eq]
  rw [h1]

/-- `Kset H t = twoPoint H t`, elementwise. -/
theorem mem_Kset_iff (h : IsSplitRankOne H Q t) (hZ : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (x : G) : x ∈ Work.ThmF.Kset H t ↔ x ∈ twoPoint H t := by
  rw [Kset_eq_twoPoint h hZ h2, SetLike.mem_coe]

/-- In the Zassenhaus split rank-one setting, `Ksub H t = D = twoPoint H t`. -/
theorem Ksub_eq_twoPoint (h : IsSplitRankOne H Q t) (hZ : IsZassenhaus H) (h2 : IsPGroup 2 Q) :
    (Work.ThmF.Ksub H t : Set G) = (twoPoint H t : Set G) := by
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe]
  exact mem_Ksub_iff h hZ h2 x

/-- `Ksub H t = Kset H t` in the Zassenhaus split rank-one setting. -/
theorem Ksub_eq_Kset (h : IsSplitRankOne H Q t) (hZ : IsZassenhaus H) (h2 : IsPGroup 2 Q) :
    (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t := by
  rw [Ksub_eq_twoPoint h hZ h2, ← Kset_eq_twoPoint h hZ h2]

/-- **The first half of the target.**  In a simple Zassenhaus split rank-one configuration
with `Q` a non-abelian `2`-group, `Q` is a Suzuki two-group. -/
theorem isSuzukiTwoGroup_Q (hs : IsSimpleGroup G) (h : IsSplitRankOne H Q t)
    (hZ : IsZassenhaus H) (h2 : IsPGroup 2 Q) (hnab : ¬ IsAbelianSubgroup Q) :
    IsSuzukiTwoGroup ↥Q := by
  classical
  refine Work.ThmF.ChV12.isSuzukiTwoGroup_of_Ksub_cyclic H t Q h.le h2 ?_ ?_ hnab ?_ ?_ ?_
  · -- `Ksub H t` normalises `Q`
    intro k hk x hx
    rw [mem_Ksub_iff h hZ h2] at hk
    exact (Subgroup.mem_normalizer_iff.mp (h.normal (Subgroup.mem_inf.mp hk).1) x).mp hx
  · -- at least two involutions
    have hcardD : Nat.card ↥(twoPoint H t) = (involutions (Q : Set G)).ncard :=
      Work.ZassenhausPSL2.ZData.card_dStab_eq_card_involutions H Q t h hZ
        (Work.ZassenhausPSL2.Feit.Q_ne_bot_of_split h) h2
    have h3 : 3 ≤ Nat.card ↥(twoPoint H t) :=
      Work.ZassenhausPSL2.ZData.three_le_card_twoPoint h hZ
    omega
  · -- `Ksub H t` is cyclic
    let e : ↥(Work.ThmF.Ksub H t) ≃* ↥(twoPoint H t) :=
      { toFun := fun x => ⟨x.1, (mem_Ksub_iff h hZ h2 x.1).mp x.2⟩
        invFun := fun y => ⟨y.1, (mem_Ksub_iff h hZ h2 y.1).mpr y.2⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun y => Subtype.ext rfl
        map_mul' := fun x y => Subtype.ext rfl }
    exact (MulEquiv.isCyclic e).mpr (QSZ_isCyclic_twoPoint h hZ h2)
  · exact Ksub_eq_Kset h hZ h2
  · -- `Ksub H t` is transitive on `Inv(H)`
    intro a ha b hb
    obtain ⟨d, hd, hdw⟩ :=
      Work.ThmF.Bender.DTransitiveInv h.stronglyEmbedded h.invol h.not_mem a ha b hb
    exact ⟨d, (mem_Kset_iff h hZ h2 d).mpr hd, hdw⟩

/-! ## Phase 2: the order of `Q` -/

/-- The centre of a Suzuki two-group equals `Ω₁`. -/
theorem center_eq_omega1_of_suzuki {Q : Subgroup G} (hSuz : IsSuzukiTwoGroup ↥Q) :
    Subgroup.center ↥Q = Work.Higman.omega1 ↥Q := by
  obtain ⟨h2g⟩ := (Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp (P := ↥Q)).mp hSuz
  refine le_antisymm ?_ (h2g.omega1_le_center)
  intro z hz
  exact (h2g.mem_omega1).mpr (by rw [pow_two]; exact Work.Higman.center_sq_eq_one h2g z hz)

/-- The involutions of a subgroup `Q ≤ G` correspond to the involutions of `↥Q`. -/
theorem ncard_involutions_eq_ncard_Invol {Q : Subgroup G} :
    (involutions (Q : Set G)).ncard = (Work.Higman.Invol ↥Q).ncard := by
  have hmem : ∀ x : G, x ∈ involutions (Q : Set G) ↔ x ∈ (Q : Set G) ∧ orderOf x = 2 :=
    fun x => Iff.rfl
  refine Set.ncard_congr (fun (x : G) (hx : x ∈ involutions (Q : Set G)) =>
    (⟨x, (hmem x).mp hx |>.1⟩ : ↥Q)) ?_ ?_ ?_
  · intro x hx
    exact (Work.Higman.mem_Invol).mpr (by
      rw [Subgroup.orderOf_mk]; exact (hmem x).mp hx |>.2)
  · intro a b ha hb hab
    exact congrArg Subtype.val hab
  · intro b hb
    exact ⟨(b : G), (hmem (b : G)).mpr
      ⟨b.2, by rw [Subgroup.orderOf_coe]; exact (Work.Higman.mem_Invol.mp hb)⟩, Subtype.ext rfl⟩

/-- In the Zassenhaus split rank-one setting with `Q` a Suzuki two-group,
`|D| + 1 = |Z(Q)|`, i.e. `|D| = q - 1` with `q = |Z(Q)|`. -/
theorem twoPoint_card_add_one_eq_center_card (h : IsSplitRankOne H Q t) (hZ : IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hSuz : IsSuzukiTwoGroup ↥Q) :
    Nat.card ↥(twoPoint H t) + 1 = Nat.card ↥(Subgroup.center ↥Q) := by
  obtain ⟨h2g⟩ := (Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp (P := ↥Q)).mp hSuz
  have hcardD : Nat.card ↥(twoPoint H t) = (involutions (Q : Set G)).ncard :=
    Work.ZassenhausPSL2.ZData.card_dStab_eq_card_involutions H Q t h hZ
      (Work.ZassenhausPSL2.Feit.Q_ne_bot_of_split h) h2
  have h1 : (Work.Higman.Invol ↥Q).ncard + 1 = Nat.card ↥(Subgroup.center ↥Q) := by
    rw [← h2g.card_omega1, center_eq_omega1_of_suzuki hSuz]
  rw [hcardD, ncard_involutions_eq_ncard_Invol]
  exact h1

/-! ## The number theory for the `q³` case -/

/-- Elementary `ZMod 5` computations. -/
private theorem zmod5_pow4 : ((2 : ZMod 5)) ^ 4 = 1 := by decide
private theorem zmod5_pow2 : ((2 : ZMod 5)) ^ 2 = -1 := by decide
private theorem zmod5_ne1 : ((2 : ZMod 5)) ^ 1 ≠ 1 := by decide
private theorem zmod5_ne2 : ((2 : ZMod 5)) ^ 2 ≠ 1 := by decide
private theorem zmod5_ne3 : ((2 : ZMod 5)) ^ 3 ≠ 1 := by decide
private theorem zmod5_neg_one_ne_one : ((-1 : ZMod 5)) ≠ 1 := by decide
private theorem zmod3_pow2 : ((2 : ZMod 3)) ^ 2 = 1 := by decide


/-- `(a : ZMod n) = 0 ↔ n ∣ a` for natural `a`, `n`. -/
private theorem natCast_zmod_eq_zero_iff_dvd' (a n : ℕ) :
    ((a : ZMod n) = 0) ↔ n ∣ a := by
  constructor
  · intro h
    have h' : ((a : ℤ) : ZMod n) = 0 := by rw [Int.cast_natCast]; exact h
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (a : ℤ) n).mp h'
    exact_mod_cast hd
  · intro h
    have hd : (n : ℤ) ∣ (a : ℤ) := by exact_mod_cast h
    have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd (a : ℤ) n).mpr hd
    rwa [Int.cast_natCast] at h'

/-- If `q = 2^m` and `5 ∣ q^3(q-1)(q^3+1)` then `m` is even. -/
theorem two_dvd_of_five_dvd (q m : ℕ) (hq : q = 2 ^ m)
    (h : 5 ∣ q ^ 3 * (q - 1) * (q ^ 3 + 1)) : 2 ∣ m := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcop : ¬ 5 ∣ q ^ 3 := by
    intro hd
    have hq5 : 5 ∣ q := Nat.Prime.dvd_of_dvd_pow (by norm_num) hd
    rw [hq] at hq5
    have hc : Nat.Coprime 5 (2 ^ m) := (by norm_num : Nat.Coprime 5 2).pow_right m
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mp hc hq5
  have h5 : 5 ∣ q - 1 ∨ 5 ∣ q ^ 3 + 1 := by
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h with h1 | h1
    · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h1 with h3 | h3
      · exact absurd h3 hcop
      · exact Or.inl h3
    · exact Or.inr h1
  have hpow4 : ((2 : ZMod 5)) ^ 4 = 1 := zmod5_pow4
  have hpow2 : ((2 : ZMod 5)) ^ 2 = -1 := zmod5_pow2
  have hne1 : ((2 : ZMod 5)) ^ 1 ≠ 1 := zmod5_ne1
  have hne2 : ((2 : ZMod 5)) ^ 2 ≠ 1 := zmod5_ne2
  have hne3 : ((2 : ZMod 5)) ^ 3 ≠ 1 := zmod5_ne3
  have hqpos : 1 ≤ q := by rw [hq]; exact Nat.one_le_two_pow
  rcases h5 with h5 | h5
  · -- `5 ∣ q - 1`
    have h0 : ((q - 1 : ℕ) : ZMod 5) = 0 :=
      (natCast_zmod_eq_zero_iff_dvd' (q - 1) 5).mpr h5
    have h1 : ((q : ZMod 5)) - ((1 : ℕ) : ZMod 5) = 0 := by
      rw [← Nat.cast_sub hqpos]; exact h0
    have h2 : (q : ZMod 5) = 1 := by simpa using sub_eq_zero.mp h1
    have hzm : ((2 : ZMod 5)) ^ m = 1 := by
      rw [hq, Nat.cast_pow, Nat.cast_ofNat] at h2
      exact h2
    have hred : ((2 : ZMod 5)) ^ m = ((2 : ZMod 5)) ^ (m % 4) := by
      conv_lhs => rw [← Nat.div_add_mod m 4]
      rw [pow_add, pow_mul, hpow4, one_pow, one_mul]
    have h1' : ((2 : ZMod 5)) ^ (m % 4) = 1 := by rw [← hred]; exact hzm
    have hlt : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases hc : m % 4
    · exact dvd_trans (by norm_num : 2 ∣ 4) (Nat.dvd_of_mod_eq_zero hc)
    · exact absurd h1' hne1
    · exact absurd h1' hne2
    · exact absurd h1' hne3
  · -- `5 ∣ q^3 + 1`
    have h0 : ((q ^ 3 + 1 : ℕ) : ZMod 5) = 0 :=
      (natCast_zmod_eq_zero_iff_dvd' (q ^ 3 + 1) 5).mpr h5
    have hzm : ((2 : ZMod 5)) ^ (3 * m) = -1 := by
      rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, hq, Nat.cast_pow, Nat.cast_ofNat] at h0
      have h1 : ((2 : ZMod 5)) ^ (m * 3) + 1 = 0 := by rw [pow_mul]; exact h0
      rw [mul_comm 3 m]
      exact eq_neg_of_add_eq_zero_left h1
    have h6 : ((2 : ZMod 5)) ^ (6 * m) = 1 := by
      have h2 : ((2 : ZMod 5)) ^ (6 * m) = (((2 : ZMod 5)) ^ (3 * m)) ^ 2 := by
        rw [show 6 * m = 3 * m * 2 by ring, pow_mul]
      rw [h2, hzm]
      norm_num
    have hfac : ((2 : ZMod 5)) ^ (6 * m) = (-1 : ZMod 5) ^ m := by
      rw [show 6 * m = 4 * m + 2 * m by ring, pow_add, pow_mul, pow_mul, hpow4, one_pow,
        one_mul, hpow2]
    have hm1 : ((-1 : ZMod 5)) ^ m = 1 := by rw [← hfac]; exact h6
    by_contra hcon
    have hodd : Odd m := Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
    rw [Odd.neg_one_pow hodd] at hm1
    exact absurd hm1 zmod5_neg_one_ne_one

/-- If `q = 2^m` with `m` even then `3 ∣ q - 1`. -/
theorem three_dvd_of_two_dvd (q m : ℕ) (hq : q = 2 ^ m) (hm : 2 ∣ m) : 3 ∣ q - 1 := by
  obtain ⟨j, hj⟩ := hm
  have hzm : ((2 : ZMod 3)) ^ m = 1 := by
    rw [hj, pow_mul, zmod3_pow2, one_pow]
  have hqpos : 1 ≤ q := by rw [hq]; exact Nat.one_le_two_pow
  have h0 : ((q - 1 : ℕ) : ZMod 3) = 0 := by
    rw [Nat.cast_sub hqpos, hq, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, hzm, sub_self]
  exact (natCast_zmod_eq_zero_iff_dvd' (q - 1) 3).mp h0


end Work.ZassenhausSuzuki
