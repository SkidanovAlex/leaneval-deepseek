import Mathlib

set_option warn.classDefReducibility false

namespace Work.L2F.Props.oddsub

open MulAction

/-- The action of the quotient group `G ⧸ Z` on `X`, induced from a `G`-action for which the
normal subgroup `Z` acts trivially.  It is characterised by `quotientMulAction_mk_smul`. -/
noncomputable def quotientMulAction {G X : Type*} [Group G] [MulAction G X]
    (Z : Subgroup G) [Z.Normal] (h : ∀ z ∈ Z, ∀ x : X, z • x = x) : MulAction (G ⧸ Z) X :=
  MulAction.ofEndHom (QuotientGroup.lift Z (MulAction.toEndHom : G →* Function.End X) (by
    intro z hz
    rw [MonoidHom.mem_ker]
    funext x
    exact h z hz x))

lemma quotientMulAction_mk_smul {G X : Type*} [Group G] [MulAction G X]
    (Z : Subgroup G) [Z.Normal] (h : ∀ z ∈ Z, ∀ x : X, z • x = x) (g : G) (x : X) :
    @SMul.smul (G ⧸ Z) X (quotientMulAction Z h).toSMul (QuotientGroup.mk g) x = g • x := rfl

/-- Arithmetic core of the counting argument. -/
theorem arith_contra {qY q k lam : ℕ} (hq : 3 ≤ q) (hlam : lam = 1 ∨ lam = 2)
    (heq : k * q = qY + lam * (q - 1)) (h3k : 3 * k ≤ qY) (hYle : 3 * qY ≤ k * q) : False := by
  have hqpos : 0 < q := by omega
  have h2 : 2 * qY ≤ lam * (q - 1) := by
    have h : 3 * qY ≤ qY + lam * (q - 1) := by rw [← heq]; exact hYle
    omega
  rcases hlam with hlam | hlam
  · subst hlam
    have hk1 : k = 1 := by
      have hle : k ≤ 1 := by
        have hlt : k * q < 2 * q := by rw [heq]; omega
        have h' := (Nat.mul_lt_mul_right hqpos).mp hlt
        omega
      have hge : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · rw [h0, zero_mul] at heq; omega
        · omega
      omega
    have hqY : qY = 1 := by rw [hk1, one_mul] at heq; omega
    omega
  · subst hlam
    have hk2 : k = 2 := by
      have hle : k ≤ 2 := by
        have hlt : k * q < 3 * q := by rw [heq]; omega
        have h' := (Nat.mul_lt_mul_right hqpos).mp hlt
        omega
      have hge : 2 ≤ k := by
        have hlt : 1 * q < k * q := by rw [heq]; omega
        have h' := (Nat.mul_lt_mul_right hqpos).mp hlt
        omega
      omega
    have hqY : qY = 2 := by rw [hk2] at heq; omega
    omega

/-- Main counting lemma: a finite group of odd order bigger than `1`, acting on a finite type in
such a way that every nontrivial element fixes exactly `lam ∈ {1,2}` points, every point is fixed
by some nonidentity element and no point is fixed by all elements, cannot exist. -/
theorem no_odd_action {Q Y : Type*} [Group Q] [Fintype Q] [MulAction Q Y] [Fintype Y]
    (hodd : Odd (Fintype.card Q)) (hgt : 1 < Fintype.card Q) {lam : ℕ} (hlam : lam = 1 ∨ lam = 2)
    (hfix : ∀ q : Q, q ≠ 1 → (MulAction.fixedBy Y q).ncard = lam)
    (hno : ∀ y : Y, ∃ q : Q, q • y ≠ y)
    (hnonfree : ∀ y : Y, ∃ q : Q, q ≠ 1 ∧ q • y = y) : False := by
  classical
  haveI : Fintype (Quotient (MulAction.orbitRel Q Y)) := Fintype.ofFinite _
  set k : ℕ := Fintype.card (Quotient (MulAction.orbitRel Q Y)) with hk
  -- Burnside's lemma
  have hburn : (∑ q : Q, (MulAction.fixedBy Y q).ncard) = k * Fintype.card Q := by
    have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group Q Y
    rw [hk, ← hb]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  -- split off the identity
  have hY1 : (MulAction.fixedBy Y (1 : Q)).ncard = Fintype.card Y := by
    have hset : MulAction.fixedBy Y (1 : Q) = Set.univ := by
      ext y
      rw [MulAction.mem_fixedBy]
      exact ⟨fun _ => Set.mem_univ y, fun _ => one_smul Q y⟩
    rw [hset, Set.ncard_univ, Nat.card_eq_fintype_card]
  have hsplit : (∑ q : Q, (MulAction.fixedBy Y q).ncard)
      = Fintype.card Y + lam * (Fintype.card Q - 1) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : Q))]
    have hsum : ∑ x ∈ (Finset.univ : Finset Q).erase 1, (MulAction.fixedBy Y x).ncard
        = lam * ((Finset.univ : Finset Q).erase 1).card := by
      rw [show (∑ x ∈ (Finset.univ : Finset Q).erase 1, (MulAction.fixedBy Y x).ncard)
            = ∑ x ∈ (Finset.univ : Finset Q).erase 1, lam from
          Finset.sum_congr rfl (fun x hx => hfix x (Finset.mem_erase.mp hx).1)]
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hsum, hY1, Finset.card_erase_of_mem (Finset.mem_univ (1 : Q)), Finset.card_univ]
    ring
  -- class formula
  have hcf : Fintype.card Y = ∑ ω : Quotient (MulAction.orbitRel Q Y),
      Fintype.card Q / Fintype.card (MulAction.stabilizer Q ω.out) :=
    MulAction.card_eq_sum_card_group_div_card_stabilizer Q Y
  -- pointwise lower bound on stabilizers
  have hstab3 : ∀ ω : Quotient (MulAction.orbitRel Q Y),
      3 ≤ Fintype.card (MulAction.stabilizer Q ω.out) := by
    intro ω
    obtain ⟨q, hq1, hq⟩ := hnonfree ω.out
    have hmem : q ∈ MulAction.stabilizer Q ω.out := by
      rw [MulAction.mem_stabilizer_iff]; exact hq
    have hbot : MulAction.stabilizer Q ω.out ≠ ⊥ := by
      intro h
      rw [h] at hmem
      exact hq1 (Subgroup.mem_bot.mp hmem)
    have hdvd : Nat.card ↥(MulAction.stabilizer Q ω.out) ∣ Nat.card Q :=
      Subgroup.card_subgroup_dvd_card _
    have hoddH : Odd (Nat.card ↥(MulAction.stabilizer Q ω.out)) :=
      Odd.of_dvd_nat (by rwa [Nat.card_eq_fintype_card]) hdvd
    have hne1 : Nat.card ↥(MulAction.stabilizer Q ω.out) ≠ 1 :=
      fun h => hbot ((Subgroup.card_eq_one).mp h)
    rw [← Nat.card_eq_fintype_card]
    obtain ⟨t, ht⟩ := hoddH
    omega
  -- pointwise lower bound for the orbit size
  have hterm_ge : ∀ ω : Quotient (MulAction.orbitRel Q Y),
      3 ≤ Fintype.card Q / Fintype.card (MulAction.stabilizer Q ω.out) := by
    intro ω
    have hcard : Fintype.card (MulAction.stabilizer Q ω.out)
        * (MulAction.stabilizer Q ω.out).index = Fintype.card Q := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Subgroup.card_mul_index]
    have hne0 : Fintype.card (MulAction.stabilizer Q ω.out) ≠ 0 := by
      have hp : 0 < Fintype.card (MulAction.stabilizer Q ω.out) :=
        Fintype.card_pos_iff.mpr
          ⟨⟨1, by rw [MulAction.mem_stabilizer_iff]; exact one_smul Q ω.out⟩⟩
      omega
    rw [(Nat.eq_div_of_mul_eq_right hne0 hcard).symm]
    have hidx_ne1 : (MulAction.stabilizer Q ω.out).index ≠ 1 := by
      intro h
      rw [Subgroup.index_eq_one] at h
      obtain ⟨q, hq⟩ := hno ω.out
      have hmem : q ∈ MulAction.stabilizer Q ω.out := by rw [h]; exact Subgroup.mem_top q
      rw [MulAction.mem_stabilizer_iff] at hmem
      exact hq hmem
    have hidx_dvd : (MulAction.stabilizer Q ω.out).index ∣ Fintype.card Q := by
      rw [← Nat.card_eq_fintype_card]; exact Subgroup.index_dvd_card _
    have hidx_odd : Odd (MulAction.stabilizer Q ω.out).index := Odd.of_dvd_nat hodd hidx_dvd
    obtain ⟨t, ht⟩ := hidx_odd
    omega
  -- pointwise upper bound for the orbit size
  have hterm_le : ∀ ω : Quotient (MulAction.orbitRel Q Y),
      Fintype.card Q / Fintype.card (MulAction.stabilizer Q ω.out) ≤ Fintype.card Q / 3 :=
    fun ω => Nat.div_le_div_left (hstab3 ω) (by norm_num)
  -- the two inequalities on `Fintype.card Y`
  have h3k : 3 * k ≤ Fintype.card Y := by
    rw [hcf, hk]
    have h : (∑ _ω : Quotient (MulAction.orbitRel Q Y), (3 : ℕ)) ≤
        (∑ ω : Quotient (MulAction.orbitRel Q Y),
          Fintype.card Q / Fintype.card (MulAction.stabilizer Q ω.out)) :=
      Finset.sum_le_sum (fun ω _ => hterm_ge ω)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] at h
    exact h
  have hYle : 3 * Fintype.card Y ≤ k * Fintype.card Q := by
    rw [hcf, hk]
    have h : (∑ ω : Quotient (MulAction.orbitRel Q Y),
          Fintype.card Q / Fintype.card (MulAction.stabilizer Q ω.out)) ≤
        (∑ _ω : Quotient (MulAction.orbitRel Q Y), Fintype.card Q / 3) :=
      Finset.sum_le_sum (fun ω _ => hterm_le ω)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
    calc 3 * (∑ ω : Quotient (MulAction.orbitRel Q Y),
            Fintype.card Q / Fintype.card (MulAction.stabilizer Q ω.out))
        ≤ 3 * (Fintype.card (Quotient (MulAction.orbitRel Q Y)) * (Fintype.card Q / 3)) :=
          Nat.mul_le_mul_left 3 h
      _ = Fintype.card (Quotient (MulAction.orbitRel Q Y)) * (3 * (Fintype.card Q / 3)) := by
          ring
      _ ≤ Fintype.card (Quotient (MulAction.orbitRel Q Y)) * Fintype.card Q :=
          Nat.mul_le_mul_left _ (Nat.mul_div_le (Fintype.card Q) 3)
  have hQ3 : 3 ≤ Fintype.card Q := by
    obtain ⟨t, ht⟩ := hodd
    omega
  have heq : k * Fintype.card Q = Fintype.card Y + lam * (Fintype.card Q - 1) := by
    rw [← hburn, hsplit]
  exact arith_contra hQ3 hlam heq h3k hYle

/-- **Lemma.** Let `G` be a finite group, `Z ⊴ G` acting trivially on a `G`-set `X`, with `G ⧸ Z`
of odd order `> 1`.  If every `g ∉ Z` fixes exactly two points of `X`, then two distinct points of
`X` are fixed by all of `G`. -/
theorem two_fixed_points_of_odd_quotient {G X : Type*} [Group G] [Finite G]
    [MulAction G X] (Z : Subgroup G) [Z.Normal]
    (hZtriv : ∀ z ∈ Z, ∀ x : X, z • x = x)
    (hodd : Odd (Nat.card (G ⧸ Z)))
    (hgt : 1 < Nat.card (G ⧸ Z))
    (hfix : ∀ g : G, g ∉ Z → (MulAction.fixedBy X g).ncard = 2) :
    ∃ x y : X, x ≠ y ∧ (∀ g : G, g • x = x) ∧ (∀ g : G, g • y = y) := by
  classical
  letI : MulAction (G ⧸ Z) X := quotientMulAction Z hZtriv
  haveI : Fintype (G ⧸ Z) := Fintype.ofFinite _
  have hodd' : Odd (Fintype.card (G ⧸ Z)) := by rwa [Nat.card_eq_fintype_card] at hodd
  have hgt' : 1 < Fintype.card (G ⧸ Z) := by rwa [Nat.card_eq_fintype_card] at hgt
  haveI : Nontrivial (G ⧸ Z) := Fintype.one_lt_card_iff_nontrivial.mp hgt'
  obtain ⟨q₀, hq₀⟩ := exists_ne (1 : G ⧸ Z)
  have hmk₀ : (QuotientGroup.mk (Quotient.out q₀) : G ⧸ Z) = q₀ := Quotient.out_eq q₀
  have hg₀ : Quotient.out q₀ ∉ Z := by
    intro hmem
    have h1 : (QuotientGroup.mk (Quotient.out q₀) : G ⧸ Z) = 1 :=
      (QuotientGroup.eq_one_iff (Quotient.out q₀)).mpr hmem
    rw [hmk₀] at h1
    exact hq₀ h1
  -- fixed points of the quotient action
  set F : Set X := MulAction.fixedPoints (G ⧸ Z) X with hF
  have hFmem : ∀ x : X, x ∈ F ↔ ∀ g : G, g • x = x := by
    intro x
    rw [hF, MulAction.mem_fixedPoints]
    constructor
    · intro h g
      exact h (QuotientGroup.mk g)
    · intro h q
      rw [← Quotient.out_eq q]
      exact h (Quotient.out q)
  have hFfin : F.Finite :=
    Set.Finite.subset
      (Set.finite_of_ncard_ne_zero (by rw [hfix (Quotient.out q₀) hg₀]; norm_num))
      (fun x hx => by rw [MulAction.mem_fixedBy]; exact (hFmem x).mp hx (Quotient.out q₀))
  have hFle : F.ncard ≤ 2 := by
    have hsub : F ⊆ MulAction.fixedBy X (Quotient.out q₀) :=
      fun x hx => by rw [MulAction.mem_fixedBy]; exact (hFmem x).mp hx (Quotient.out q₀)
    calc F.ncard ≤ (MulAction.fixedBy X (Quotient.out q₀)).ncard :=
          Set.ncard_le_ncard hsub
            (Set.finite_of_ncard_ne_zero (by rw [hfix (Quotient.out q₀) hg₀]; norm_num))
      _ = 2 := hfix (Quotient.out q₀) hg₀
  -- suppose the conclusion fails
  by_contra hcon
  have hFsub : F.Subsingleton := by
    intro x hx y hy
    by_contra hxy
    exact hcon ⟨x, y, hxy, (hFmem x).mp hx, (hFmem y).mp hy⟩
  have hF1 : F.ncard ≤ 1 :=
    (Set.ncard_le_one hFfin).mpr (fun a ha b hb => hFsub ha hb)
  set lam : ℕ := 2 - F.ncard with hlamdef
  have hlam : lam = 1 ∨ lam = 2 := by
    have hf : F.ncard = 0 ∨ F.ncard = 1 := by omega
    rcases hf with hf | hf <;> rw [hlamdef, hf] <;> norm_num
  -- the set of points fixed by some nonidentity element
  set P : Set X := {x : X | ∃ q : G ⧸ Z, q ≠ 1 ∧ q • x = x} with hP
  have hPfin : P.Finite := by
    have hsfin : ({q : G ⧸ Z | q ≠ 1} : Set (G ⧸ Z)).Finite := by
      have h := Finset.finite_toSet (Finset.univ.filter (fun q : G ⧸ Z => q ≠ 1))
      rw [Finset.coe_filter] at h
      simpa using h
    have hb : (⋃ i ∈ ({q : G ⧸ Z | q ≠ 1} : Set (G ⧸ Z)), {x : X | i • x = x}).Finite := by
      refine Set.Finite.biUnion hsfin (fun i hi => ?_)
      have hi1 : i ≠ 1 := hi
      have hmki : (QuotientGroup.mk (Quotient.out i) : G ⧸ Z) = i := Quotient.out_eq i
      have hgi : Quotient.out i ∉ Z := by
        intro hmem
        have h1 : (QuotientGroup.mk (Quotient.out i) : G ⧸ Z) = 1 :=
          (QuotientGroup.eq_one_iff (Quotient.out i)).mpr hmem
        rw [hmki] at h1
        exact hi1 h1
      have hset : ∀ g : G, (QuotientGroup.mk g : G ⧸ Z) = i →
          ({x : X | i • x = x} : Set X) = MulAction.fixedBy X g := by
        intro g hg
        ext x
        rw [Set.mem_setOf_eq, MulAction.mem_fixedBy, ← hg]
        exact Iff.rfl
      rw [hset (Quotient.out i) hmki]
      exact Set.finite_of_ncard_ne_zero (by rw [hfix (Quotient.out i) hgi]; norm_num)
    exact hb.subset (fun x hx => by
      obtain ⟨q, hq1, hqx⟩ := hx
      exact Set.mem_biUnion hq1 hqx)
  -- the type Y of points fixed by some nonidentity element but not globally fixed
  set Y : Set X := P \ F with hY
  have hYmem : ∀ x : X, x ∈ Y ↔ x ∈ P ∧ x ∉ F := by
    intro x
    rw [hY]
    exact Iff.rfl
  have hYfin : Y.Finite := hPfin.sdiff
  have hYsmul : ∀ (x : X), x ∈ Y → ∀ q : G ⧸ Z, q • x ∈ Y := by
    intro x hx q
    obtain ⟨hxP, hxF⟩ := (hYmem x).mp hx
    obtain ⟨q₁, hq₁1, hq₁⟩ := hxP
    have hxF' : ¬ ∀ q : G ⧸ Z, q • x = x := by
      intro h
      exact hxF (by rw [hF, MulAction.mem_fixedPoints]; exact h)
    obtain ⟨q₂, hq₂⟩ := not_forall.mp hxF'
    have hconj1 : (q * q₁ * q⁻¹) • (q • x) = q • x := by
      have h1 : q⁻¹ • (q • x) = x := by rw [← mul_smul, inv_mul_cancel, one_smul]
      rw [mul_smul, mul_smul, h1, hq₁]
    have hconj2 : (q * q₂ * q⁻¹) • (q • x) ≠ q • x := by
      intro hc
      apply hq₂
      have hcomp : (q * q₂ * q⁻¹) • (q • x) = q • (q₂ • x) := by
        have h1 : q⁻¹ • (q • x) = x := by rw [← mul_smul, inv_mul_cancel, one_smul]
        rw [mul_smul, mul_smul, h1]
      rw [hcomp] at hc
      have hcc := congrArg (fun z => q⁻¹ • z) hc
      have htriple : q⁻¹ • (q • (q₂ • x)) = (q⁻¹ * q) • (q₂ • x) := by rw [← mul_smul]
      have hsingle : q⁻¹ • (q • x) = (q⁻¹ * q) • x := by rw [← mul_smul]
      rw [htriple, hsingle, inv_mul_cancel, one_smul, one_smul] at hcc
      exact hcc
    refine (hYmem (q • x)).mpr ⟨⟨q * q₁ * q⁻¹, ?_, hconj1⟩, ?_⟩
    · intro h
      apply hq₁1
      have hc := congrArg (fun z => q⁻¹ * z * q) h
      have hL : q⁻¹ * (q * q₁ * q⁻¹) * q = q₁ := by group
      rw [hL, mul_one, inv_mul_cancel] at hc
      exact hc
    · intro hmem
      have h1 : (Quotient.out (q * q₂ * q⁻¹)) • (q • x) = q • x :=
        (hFmem (q • x)).mp hmem (Quotient.out (q * q₂ * q⁻¹))
      exact hconj2 (by rw [← Quotient.out_eq (q * q₂ * q⁻¹)]; exact h1)
  let Ysm : SubMulAction (G ⧸ Z) X :=
    { carrier := Y, smul_mem' := fun q x hx => hYsmul x hx q }
  haveI : Fintype ↥Ysm := hYfin.fintype
  have hYcoe : ∀ (q : G ⧸ Z) (y : ↥Ysm), ((q • y : ↥Ysm) : X) = q • (y : X) :=
    fun q y => SubMulAction.val_smul (p := Ysm) q y
  -- the fixed points of a nontrivial element inside `Y`
  have hYfix : ∀ q : G ⧸ Z, q ≠ 1 → (MulAction.fixedBy ↥Ysm q).ncard = lam := by
    intro q hq
    have hmk : (QuotientGroup.mk (Quotient.out q) : G ⧸ Z) = q := Quotient.out_eq q
    have hg : Quotient.out q ∉ Z := by
      intro hmem
      have h1 : (QuotientGroup.mk (Quotient.out q) : G ⧸ Z) = 1 :=
        (QuotientGroup.eq_one_iff (Quotient.out q)).mpr hmem
      rw [hmk] at h1
      exact hq h1
    have hfixby : ∀ g : G, (QuotientGroup.mk g : G ⧸ Z) = q →
        MulAction.fixedBy X (QuotientGroup.mk g : G ⧸ Z) = MulAction.fixedBy X g := by
      intro g _
      ext x
      rw [MulAction.mem_fixedBy, MulAction.mem_fixedBy]
      exact Iff.rfl
    have himg : (Subtype.val '' (MulAction.fixedBy ↥Ysm q : Set ↥Ysm))
        = (MulAction.fixedBy X q : Set X) ∩ Y := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [MulAction.mem_fixedBy] at hy
        refine ⟨?_, y.2⟩
        rw [MulAction.mem_fixedBy, ← hYcoe q y]
        exact congrArg Subtype.val hy
      · rintro ⟨hx1, hx2⟩
        refine ⟨⟨x, hx2⟩, ?_, rfl⟩
        rw [MulAction.mem_fixedBy]
        refine Subtype.ext ?_
        rw [SubMulAction.val_smul]
        rw [MulAction.mem_fixedBy] at hx1
        exact hx1
    have hset : (MulAction.fixedBy X q : Set X) ∩ Y = MulAction.fixedBy X q \ F := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (hYmem x).mp h2 |>.2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (hYmem x).mpr ⟨⟨q, hq, MulAction.mem_fixedBy.mp h1⟩, h2⟩⟩
    have hsub : F ⊆ MulAction.fixedBy X q := by
      intro x hx
      rw [MulAction.mem_fixedBy, ← hmk]
      exact (hFmem x).mp hx (Quotient.out q)
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg, hset,
      Set.ncard_sdiff hsub hFfin, ← hmk, hfixby (Quotient.out q) hmk,
      hfix (Quotient.out q) hg, hlamdef]
  refine no_odd_action (Q := G ⧸ Z) (Y := ↥Ysm) hodd' hgt' hlam hYfix ?_ ?_
  · intro y
    have hyY : (y : X) ∈ Y := y.2
    have hyF : (y : X) ∉ F := ((hYmem (y : X)).mp hyY).2
    rw [hF, MulAction.mem_fixedPoints] at hyF
    obtain ⟨q, hq⟩ := not_forall.mp hyF
    exact ⟨q, fun hc => hq (by rw [← hYcoe q y]; exact congrArg Subtype.val hc)⟩
  · intro y
    have hyY : (y : X) ∈ Y := y.2
    obtain ⟨q, hq1, hq⟩ := ((hYmem (y : X)).mp hyY).1
    exact ⟨q, hq1, Subtype.ext (by rw [hYcoe q y]; exact hq)⟩

end Work.L2F.Props.oddsub
