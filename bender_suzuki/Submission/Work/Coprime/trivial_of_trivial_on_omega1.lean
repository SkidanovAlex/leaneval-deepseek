import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.commutator_normal
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.frattini_eq_agemo_sup_commutator
import Submission.Work.PGroup.pow_mem_frattiniIn

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
open scoped Pointwise commutatorElement
open Subgroup

namespace Work.Coprime

variable {A : Type*} {G : Type*} [Group A] [Group G] [MulDistribMulAction A G]

/-! ## Auxiliary lemmas for `trivial_of_trivial_on_omega1` -/

/-- The Frattini subgroup `Φ(G)` is invariant under any group acting on `G` by automorphisms. -/
instance ttoIsInvariantFrattini [Finite G] : FT.IsInvariant A (frattini G) := by
  refine ⟨fun a => ?_⟩
  rw [Subgroup.pointwise_smul_def]
  have hsurj : Function.Surjective (MulDistribMulAction.toMonoidEnd A G a) := by
    intro x
    exact ⟨a⁻¹ • x, by
      show MulDistribMulAction.toMonoidHom G a (a⁻¹ • x) = x
      rw [MulDistribMulAction.toMonoidHom_apply, smul_inv_smul]⟩
  have hsurj' : Function.Surjective (MulDistribMulAction.toMonoidEnd A G a⁻¹) := by
    intro x
    exact ⟨a • x, by
      show MulDistribMulAction.toMonoidHom G a⁻¹ (a • x) = x
      rw [MulDistribMulAction.toMonoidHom_apply, inv_smul_smul]⟩
  have h1 : frattini G ≤ Subgroup.comap (MulDistribMulAction.toMonoidEnd A G a) (frattini G) :=
    frattini_le_comap_frattini_of_surjective hsurj
  have h2 : frattini G ≤ Subgroup.comap (MulDistribMulAction.toMonoidEnd A G a⁻¹) (frattini G) :=
    frattini_le_comap_frattini_of_surjective hsurj'
  refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr h1) ?_
  intro y hy
  refine Subgroup.mem_map.mpr ⟨a⁻¹ • y, ?_, ?_⟩
  · have := h2 hy
    simpa [MulDistribMulAction.toMonoidHom_apply] using this
  · show MulDistribMulAction.toMonoidHom G a (a⁻¹ • y) = y
    rw [MulDistribMulAction.toMonoidHom_apply, smul_inv_smul]

/-- If `⁅v,u⁆` is central then shifting `u` past the power `v ^ n` costs `⁅v,u⁆ ^ n`. -/
theorem tto_pow_mul_comm_center {u v : G} (hd : ⁅v, u⁆ ∈ Subgroup.center G) (n : ℕ) :
    v ^ n * u = ⁅v, u⁆ ^ n * (u * v ^ n) := by
  have hdv : Commute ⁅v, u⁆ v := ((Subgroup.mem_center_iff.mp hd v)).symm
  have hvu : v * u = ⁅v, u⁆ * (u * v) := by rw [commutatorElement_def]; group
  induction n with
  | zero => simp
  | succ n ih =>
    have hdn : Commute (⁅v, u⁆ ^ n) v := hdv.pow_left n
    calc v ^ (n + 1) * u = v * (v ^ n * u) := by rw [pow_succ']; group
      _ = v * (⁅v, u⁆ ^ n * (u * v ^ n)) := by rw [ih]
      _ = (v * ⁅v, u⁆ ^ n) * (u * v ^ n) := by group
      _ = (⁅v, u⁆ ^ n * v) * (u * v ^ n) := by rw [hdn.eq]
      _ = ⁅v, u⁆ ^ n * ((v * u) * v ^ n) := by group
      _ = ⁅v, u⁆ ^ n * ((⁅v, u⁆ * (u * v)) * v ^ n) := by rw [hvu]
      _ = (⁅v, u⁆ ^ n * ⁅v, u⁆) * (u * (v * v ^ n)) := by group
      _ = ⁅v, u⁆ ^ (n + 1) * (u * v ^ (n + 1)) := by rw [← pow_succ, ← pow_succ']

/-- Class-two power formula: if `⁅v,u⁆` is central then
`(u * v) ^ n = ⁅v,u⁆ ^ (n.choose 2) * u ^ n * v ^ n`. -/
theorem tto_pow_mul_eq_commutator_pow {u v : G} (hd : ⁅v, u⁆ ∈ Subgroup.center G) (n : ℕ) :
    (u * v) ^ n = ⁅v, u⁆ ^ (n.choose 2) * u ^ n * v ^ n := by
  have hdu : Commute ⁅v, u⁆ u := ((Subgroup.mem_center_iff.mp hd u)).symm
  induction n with
  | zero => simp
  | succ n ih =>
    have hvn : v ^ n * u = ⁅v, u⁆ ^ n * (u * v ^ n) := tto_pow_mul_comm_center hd n
    have hdn : Commute (⁅v, u⁆ ^ n) u := hdu.pow_left n
    have hshift : u ^ n * (⁅v, u⁆ ^ n * (u * v ^ n)) = ⁅v, u⁆ ^ n * (u ^ n * (u * v ^ n)) := by
      rw [← mul_assoc, ← (hdn.pow_right n).eq, mul_assoc]
    calc (u * v) ^ (n + 1) = (u * v) ^ n * (u * v) := by rw [pow_succ]
      _ = (⁅v, u⁆ ^ (n.choose 2) * u ^ n * v ^ n) * (u * v) := by rw [ih]
      _ = ⁅v, u⁆ ^ (n.choose 2) * (u ^ n * (v ^ n * u)) * v := by group
      _ = ⁅v, u⁆ ^ (n.choose 2) * (u ^ n * (⁅v, u⁆ ^ n * (u * v ^ n))) * v := by rw [hvn]
      _ = (⁅v, u⁆ ^ (n.choose 2) * ⁅v, u⁆ ^ n) * (u ^ n * u) * (v ^ n * v) := by
            rw [hshift]; group
      _ = ⁅v, u⁆ ^ (n.choose 2 + n) * u ^ (n + 1) * v ^ (n + 1) := by
            rw [← pow_add, ← pow_succ, ← pow_succ]
      _ = ⁅v, u⁆ ^ ((n + 1).choose 2) * u ^ (n + 1) * v ^ (n + 1) := by
            rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]


/-- For `Y ∈ Φ(G)` and a commutator generator `x⁻¹ * (a • x)`, the two commute, provided the
action fixes `Φ(G)` pointwise. -/
theorem tto_commutator_gen_eq_one {a : A} {x Y : G} (hY : Y ∈ frattini G)
    (hPhi : ∀ (b : A) (y : G), y ∈ frattini G → b • y = y) :
    ⁅Y, x⁻¹ * (a • x)⁆ = 1 := by
  have hYx : ⁅Y, x⁆ ∈ frattini G := by
    have h1 : x * Y * x⁻¹ ∈ frattini G := (inferInstance : (frattini G).Normal).conj_mem Y hY x
    have h2 : (x * Y * x⁻¹)⁻¹ ∈ frattini G := (frattini G).inv_mem h1
    have h3 : Y * (x * Y * x⁻¹)⁻¹ = ⁅Y, x⁆ := by rw [commutatorElement_def]; group
    rw [← h3]; exact (frattini G).mul_mem hY h2
  have h1 : ⁅Y, a • x⁆ = ⁅Y, x⁆ := by
    have hm := map_commutatorElement (MulDistribMulAction.toMonoidHom G a) Y x
    simp only [MulDistribMulAction.toMonoidHom_apply] at hm
    rw [hPhi a Y hY] at hm
    rw [← hm, hPhi a ⁅Y, x⁆ hYx]
  rw [commutatorElement_mul_right_eq_mul_conj, commutatorElement_inv_right,
      ← commutatorElement_inv, h1]
  group

/-- If a subgroup `P` contains `[G,A]` and `A` fixes `P` pointwise, then `A` fixes `G`. -/
theorem tto_fix_of_commutator_le {p : ℕ} (P : Subgroup G)
    (hP : FT.commutator A (⊤ : Subgroup G) ≤ P)
    (hfixP : ∀ (a : A) (y : G), y ∈ P → a • y = y)
    (hpA : (Nat.card A).Coprime p) (hG : IsPGroup p G) :
    ∀ (a : A) (x : G), a • x = x := by
  intro a x
  set d : G := x⁻¹ * (a • x) with hd
  have hax : a • x = x * d := by rw [hd]; group
  have hdmem : d ∈ P := by rw [hd]; exact hP (FT.le_commutator a (Subgroup.mem_top x))
  have had : a • d = d := hfixP a d hdmem
  have horbit : ∀ k : ℕ, (a ^ k) • x = x * d ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_smul, pow_zero, mul_one]
    | succ k ih =>
      rw [pow_succ', mul_smul, ih, smul_mul', smul_pow', had, hax, mul_assoc, ← pow_succ']
  have hdm : d ^ orderOf a = 1 := by
    have h := horbit (orderOf a)
    rw [pow_orderOf_eq_one, one_smul] at h
    exact mul_left_cancel (by rw [mul_one]; exact h.symm)
  obtain ⟨j, hj⟩ := hG.exists_pow_pow_eq_one d
  have hcop : (orderOf a).Coprime (p ^ j) :=
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_natCard a) hpA).pow_right j
  have hd1 : d = 1 := by
    have h1 : d ^ (orderOf a).gcd (p ^ j) = 1 := pow_gcd_eq_one.mpr ⟨hdm, hj⟩
    rw [hcop.gcd_eq_one, pow_one] at h1
    exact h1
  rw [hax, hd1, mul_one]

/-- If `u ^ p * v ^ p = 1` and `⁅v,u⁆` is central of order dividing `p` (`p` odd), then
`(u * v) ^ p = 1`. -/
theorem tto_dpow_eq_one {p : ℕ} {u v : G} (hcenter : ⁅v, u⁆ ∈ Subgroup.center G)
    (hpow : u ^ p * v ^ p = 1) (hu : ⁅v, u⁆ ^ p = 1) (hp : p.Prime) (hpodd : p ≠ 2) :
    (u * v) ^ p = 1 := by
  rw [tto_pow_mul_eq_commutator_pow hcenter p]
  have hlt : 2 < p := by have := hp.two_le; omega
  obtain ⟨k, hk⟩ := hp.dvd_choose_self (by norm_num) hlt
  rw [hk, pow_mul, hu, one_pow, one_mul]
  exact hpow


/-- Main induction step: a `p`-group (`p` odd) on which a `p'`-group acts trivially on `Ω₁` is
acted on trivially. -/
theorem tto_main : ∀ (n : ℕ), ∀ (G : Type*) [Group G] [Finite G] (A : Type*) [Group A]
    [Finite A] [MulDistribMulAction A G] (p : ℕ), p.Prime → p ≠ 2 → IsPGroup p G →
    Nat.card G = n → (Nat.card A).Coprime p → (∀ (a : A) (x : G), x ^ p = 1 → a • x = x) →
    (∀ (a : A) (x : G), a • x = x) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih G _ _ A _ _ _ p hp hpodd hG hcard hpA htriv
  by_cases hG1 : Nat.card G = 1
  · haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hG1).1
    intro a x; exact Subsingleton.elim _ _
  · haveI : Nontrivial G :=
      not_subsingleton_iff_nontrivial.mp
        (fun hsub => hG1 (Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩))
    have hPhi_lt : frattini G < ⊤ := by
      obtain ⟨M, hM⟩ := IsCoatomic.exists_coatom (Subgroup G)
      exact lt_of_le_of_lt (frattini_le_coatom hM) (lt_of_le_of_ne le_top hM.1)
    have hPhi_fix : ∀ (a : A) (y : G), y ∈ frattini G → a • y = y := by
      have hcardPhi : Nat.card ↥(frattini G) < n := by
        have h := Subgroup.card_lt_of_lt hPhi_lt
        rw [Subgroup.card_top] at h
        rwa [← hcard]
      have htrivPhi : ∀ (a : A) (x : ↥(frattini G)), x ^ p = 1 → a • x = x := by
        intro a x hx
        apply Subtype.ext
        rw [FT.coe_subgroup_smul]
        exact htriv a x.1 (by simpa using congrArg Subtype.val hx)
      have hkey := ih (Nat.card ↥(frattini G)) hcardPhi ↥(frattini G) A p hp hpodd
        (hG.to_subgroup (frattini G)) rfl hpA htrivPhi
      intro a y hy
      exact congrArg Subtype.val (hkey a ⟨y, hy⟩)
    by_cases hUtop : frattini G ⊔ FT.commutator A (⊤ : Subgroup G) = ⊤
    · have hcommTop : FT.commutator A (⊤ : Subgroup G) = ⊤ :=
        frattini_nongenerating (by rw [sup_comm]; exact hUtop)
      have hPhiZ : frattini G ≤ Subgroup.center G := by
        have key : frattini G ≤
            Subgroup.centralizer (↑(FT.commutator A (⊤ : Subgroup G)) : Set G) := by
          intro Y hY
          rw [Subgroup.mem_centralizer_iff]
          intro m hm
          have hS : {e : G | ∃ a : A, ∃ x ∈ (⊤ : Subgroup G), e = x⁻¹ * (a • x)}
              ⊆ ↑(Subgroup.centralizer ({Y} : Set G)) := by
            rintro e ⟨a, x, -, rfl⟩
            change x⁻¹ * (a • x) ∈ Subgroup.centralizer ({Y} : Set G)
            rw [Subgroup.mem_centralizer_iff]
            intro h hh
            rw [Set.mem_singleton_iff] at hh
            subst hh
            exact commutatorElement_eq_one_iff_mul_comm.mp
              (tto_commutator_gen_eq_one hY hPhi_fix)
          have hclosure : FT.commutator A (⊤ : Subgroup G) ≤
              Subgroup.centralizer ({Y} : Set G) :=
            (Subgroup.closure_le (Subgroup.centralizer ({Y} : Set G))).mpr hS
          have := hclosure hm
          rw [Subgroup.mem_centralizer_iff] at this
          exact (this Y (Set.mem_singleton Y)).symm
        rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, ← hcommTop]
        exact key
      have hclass2 : ∀ X Y : G, ⁅X, Y⁆ ∈ Subgroup.center G := by
        intro X Y
        refine hPhiZ ?_
        have hmem : ⁅X, Y⁆ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top X) (Subgroup.mem_top Y)
        rw [Work.PGroup.frattini_eq_powClosure_sup_commutator hp hG]
        exact Subgroup.mem_sup_right hmem
      intro a x
      set y : G := a • x with hy
      set d : G := x⁻¹ * y with hd
      have hax : a • x = x * d := by rw [← hy, hd]; group
      have hxp : y ^ p = x ^ p := by
        rw [hy, ← smul_pow']
        exact hPhi_fix a (x ^ p) (Work.PGroup.pow_mem_frattini hp hG x)
      have hcenter : ⁅y, x⁻¹⁆ ∈ Subgroup.center G := by
        rw [commutatorElement_inv_right]
        have hc : ⁅x, y⁆ ∈ Subgroup.center G := hclass2 x y
        rw [mul_assoc, (Subgroup.mem_center_iff.mp hc x).symm, ← mul_assoc, inv_mul_cancel,
            one_mul]
        exact hc
      have hdp : d ^ p = 1 := by
        rw [hd]
        refine tto_dpow_eq_one hcenter ?_ ?_ hp hpodd
        · rw [inv_pow, ← hxp]; group
        · have hcomm : Commute x⁻¹ ⁅y, x⁻¹⁆ := Subgroup.mem_center_iff.mp hcenter x⁻¹
          rw [Commute.commutatorElement_pow_right hcomm p, inv_pow, ← hxp]
          exact Commute.commutator_eq ((Commute.refl y).pow_right p).inv_right
      have had : a • d = d := htriv a d hdp
      have horbit : ∀ k : ℕ, (a ^ k) • x = x * d ^ k := by
        intro k
        induction k with
        | zero => rw [pow_zero, one_smul, pow_zero, mul_one]
        | succ k ihk =>
          rw [pow_succ', mul_smul, ihk, smul_mul', smul_pow', had, hax, mul_assoc, ← pow_succ']
      have hdm : d ^ orderOf a = 1 := by
        have h := horbit (orderOf a)
        rw [pow_orderOf_eq_one, one_smul] at h
        exact mul_left_cancel (by rw [mul_one]; exact h.symm)
      obtain ⟨j, hj⟩ := hG.exists_pow_pow_eq_one d
      have hcop : (orderOf a).Coprime (p ^ j) :=
        (Nat.Coprime.coprime_dvd_left (orderOf_dvd_natCard a) hpA).pow_right j
      have hd1 : d = 1 := by
        have h1 : d ^ (orderOf a).gcd (p ^ j) = 1 := pow_gcd_eq_one.mpr ⟨hdm, hj⟩
        rw [hcop.gcd_eq_one, pow_one] at h1
        exact h1
      change a • x = x
      rw [hax, hd1, mul_one]
    · by_cases hUfr : frattini G ⊔ FT.commutator A (⊤ : Subgroup G) ≤ frattini G
      · exact tto_fix_of_commutator_le (frattini G) (fun z hz => hUfr (Subgroup.mem_sup_right hz))
          hPhi_fix hpA hG
      · have hPfix : ∀ (a : A) (y : G),
            y ∈ frattini G ⊔ FT.commutator A (⊤ : Subgroup G) → a • y = y := by
          have hcardU : Nat.card ↥(frattini G ⊔ FT.commutator A (⊤ : Subgroup G)) < n := by
            have hlt : frattini G ⊔ FT.commutator A (⊤ : Subgroup G) < ⊤ :=
              lt_of_le_of_ne le_top hUtop
            have h := Subgroup.card_lt_of_lt hlt
            rw [Subgroup.card_top] at h
            rwa [← hcard]
          have htrivU : ∀ (a : A) (x : ↥(frattini G ⊔ FT.commutator A (⊤ : Subgroup G))),
              x ^ p = 1 → a • x = x := by
            intro a x hx
            apply Subtype.ext
            rw [FT.coe_subgroup_smul]
            exact htriv a x.1 (by simpa using congrArg Subtype.val hx)
          have hkey := ih (Nat.card ↥(frattini G ⊔ FT.commutator A (⊤ : Subgroup G))) hcardU
            ↥(frattini G ⊔ FT.commutator A (⊤ : Subgroup G)) A p hp hpodd
            (hG.to_subgroup _) rfl hpA htrivU
          intro a y hy
          exact congrArg Subtype.val (hkey a ⟨y, hy⟩)
        exact tto_fix_of_commutator_le _ (fun z hz => Subgroup.mem_sup_right hz) hPfix hpA hG


/-- **Main lemma.** If a `p'`-group acts on a finite `p`-group (`p` odd) trivially on `Ω₁`, then
its action is trivial. -/
theorem trivial_of_trivial_on_omega1 (A : Type*) {G : Type*} [Group A] [Group G] [Finite A]
    [Finite G] [MulDistribMulAction A G] (hcop : (Nat.card A).Coprime (Nat.card G))
    (p : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hG : IsPGroup p G)
    (h : FT.IsTrivialOn A (FT.omega1 p G)) : FT.IsTrivialOn A G := by
  have htriv : ∀ (a : A) (x : G), x ^ p = 1 → a • x = x := by
    intro a x hx
    have h1 := h a ⟨x, FT.mem_omega1 hx⟩
    have h2 := congrArg Subtype.val h1
    rwa [FT.coe_subgroup_smul] at h2
  by_cases hG1 : Nat.card G = 1
  · haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hG1).1
    intro a x
    exact Subsingleton.elim _ _
  · haveI : Fact p.Prime := ⟨hp⟩
    have hpA : (Nat.card A).Coprime p := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hG
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hG1 hk
      have hpdvd : p ∣ Nat.card G := by rw [hk]; exact dvd_pow_self p hk0
      exact Nat.Coprime.coprime_dvd_right hpdvd hcop
    exact tto_main (Nat.card G) G A p hp hpodd hG rfl hpA htriv

end Work.Coprime
