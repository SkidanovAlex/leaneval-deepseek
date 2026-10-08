import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Field coordinates of a regular abelian action on an abelian 2-group

Let `Q` be an abelian `2`-subgroup of a finite group `G` and let `D ≤ N_G(Q)` be abelian,
acting fixed-point-freely on `Q` with `|D| = |Q| - 1`.  Then `Q` is elementary abelian and the
pair `(Q, D)` are the additive and multiplicative groups of a finite field `GF(2^n)`; the
action of `D` is multiplication.

The file first proves the abstract statement `regular_coordinates_abstract` (a finite abelian
group `V` of exponent two with a fixed-point-free abelian group `A` of automorphisms acting
regularly on `V \ {0}` is the additive group of a finite field with `A` its multiplicative
group), and then transfers it to the conjugation action.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section

namespace Work.ZassenhausPSL2.ZData

-- ============================================================================
-- Abstract core
-- ============================================================================

theorem regular_coordinates_abstract {V : Type*} [AddCommGroup V] [Finite V]
    {A : Type*} [Group A] [Finite A] [MulAction A V]
    (hcommA : ∀ a b : A, a * b = b * a)
    (hchar : ∀ x : V, x + x = 0)
    (hsmul : ∀ (a : A) (x y : V), a • (x + y) = a • x + a • y)
    (hfpf : ∀ a : A, a ≠ 1 → ∀ x : V, a • x = x → x = 0)
    (hcard : Nat.card A = Nat.card V - 1) :
    ∃ (n : ℕ) (_ : 1 ≤ n) (e : V ≃ GaloisField 2 n) (φ : A ≃* (GaloisField 2 n)ˣ),
      (∀ x y : V, e (x + y) = e x + e y) ∧
      (∀ (a : A) (x : V), e (a • x) = (φ a : GaloisField 2 n) * e x) := by
  classical
  -- 0. the action fixes zero
  have h0 : ∀ a : A, a • (0 : V) = 0 := by
    intro a
    have h : a • (0 : V) = a • (0 : V) + a • (0 : V) := by simpa using hsmul a 0 0
    have h2 : (0 : V) = a • (0 : V) :=
      add_left_cancel (show a • (0 : V) + 0 = a • (0 : V) + a • (0 : V) from by
        rw [add_zero]; exact h)
    exact h2.symm
  -- 1. an element of A is zero on x iff x = 0
  have hsmul_eq_zero : ∀ (a : A) (x : V), a • x = 0 ↔ x = 0 := by
    intro a x
    refine ⟨fun h => ?_, fun h => by rw [h, h0]⟩
    have hx : a⁻¹ • (a • x) = x := by rw [smul_smul, inv_mul_cancel, one_smul]
    rw [h, h0] at hx
    exact hx.symm
  -- 2. a nonzero base point
  have hcardA : 1 ≤ Nat.card A := by
    have : 0 < Nat.card A := Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
    omega
  have hcardV : 2 ≤ Nat.card V := by omega
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h
    push_neg at h
    have hsub : Subsingleton V := ⟨fun a b => by rw [h a, h b]⟩
    have h1 : Nat.card V = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨0⟩⟩
    omega
  -- 3. the orbit map is a bijection onto the nonzero elements
  have hinj : Function.Injective (fun a : A => a • v) := by
    intro a b hab
    have hab' : a • v = b • v := hab
    have h1 : (b⁻¹ * a) • v = v := by
      rw [mul_smul, hab', ← mul_smul, inv_mul_cancel, one_smul]
    by_contra hne
    have hb1 : b⁻¹ * a ≠ 1 := fun h => hne (by
      calc a = b * (b⁻¹ * a) := by group
        _ = b := by rw [h, mul_one])
    exact hv (hfpf (b⁻¹ * a) hb1 v h1)
  have hne0 : ∀ a : A, a • v ≠ 0 := fun a h => hv ((hsmul_eq_zero a v).mp h)
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype A := Fintype.ofFinite A
  have hcard_ne : Fintype.card {x : V // x ≠ 0} = Fintype.card V - 1 := by
    have h := Fintype.card_subtype_compl (α := V) (fun x => x = 0)
    rw [Fintype.card_subtype_eq (0 : V)] at h
    simpa using h
  have hbijf : Function.Bijective (fun a : A => (⟨a • v, hne0 a⟩ : {x : V // x ≠ 0})) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b hab => hinj (Subtype.ext_iff.mp hab), ?_⟩
    have h1 : Fintype.card A = Nat.card A := (Nat.card_eq_fintype_card).symm
    have h2 : Fintype.card V = Nat.card V := (Nat.card_eq_fintype_card).symm
    omega
  let eD : A ≃ {x : V // x ≠ 0} := Equiv.ofBijective _ hbijf
  let eDv : A → V := fun a => (eD a : V)
  have heD : ∀ a : A, eDv a = a • v := fun a => rfl
  have heDc : ∀ a : A, ((eD a : {x : V // x ≠ 0}) : V) = a • v := fun a => rfl
  have hneD : ∀ a : A, eDv a ≠ 0 := fun a => (eD a).2
  -- 4. logarithms
  let logf : V → A := fun x => if h : x = 0 then 1 else eD.symm ⟨x, h⟩
  have logf_of_ne : ∀ (x : V) (hx : x ≠ 0), logf x = eD.symm ⟨x, hx⟩ := by
    intro x hx
    show dite (x = 0) (fun _ => (1 : A)) (fun h => eD.symm ⟨x, h⟩) = eD.symm ⟨x, hx⟩
    rw [dite_eq_right hx]
  have logf_smul : ∀ (x : V) (hx : x ≠ 0), (logf x) • v = x := by
    intro x hx
    rw [logf_of_ne x hx, ← heD (eD.symm ⟨x, hx⟩)]
    exact congrArg (fun s : {x : V // x ≠ 0} => (s : V)) (Equiv.apply_symm_apply eD ⟨x, hx⟩)
  have logf_eD : ∀ a : A, logf (eDv a) = a := by
    intro a
    rw [logf_of_ne (eDv a) (hneD a)]
    exact Equiv.symm_apply_apply eD a
  have logf_smul_v : ∀ a : A, logf (a • v) = a := by
    intro a
    rw [← heD a]
    exact logf_eD a
  -- 5. the near-field multiplication
  let nmul : V → V → V := fun a b => if h : a = 0 then 0 else (eD.symm ⟨a, h⟩) • b
  have nmul_zero : ∀ b : V, nmul 0 b = 0 := by
    intro b
    show dite ((0 : V) = 0) (fun _ => (0 : V)) (fun h => (eD.symm ⟨0, h⟩) • b) = 0
    rw [dite_eq_left rfl]
  have nmul_of_ne : ∀ (a : V) (ha : a ≠ 0) (b : V),
      nmul a b = (eD.symm ⟨a, ha⟩) • b := by
    intro a ha b
    show dite (a = 0) (fun _ => (0 : V)) (fun h => (eD.symm ⟨a, h⟩) • b)
        = (eD.symm ⟨a, ha⟩) • b
    rw [dite_eq_right ha]
  have nmul_of_ne_eq : ∀ (a : V) (ha : a ≠ 0) (b : V), nmul a b = (logf a) • b := by
    intro a ha b
    rw [nmul_of_ne a ha b, logf_of_ne a ha]
  have nmul_right_zero : ∀ a : V, nmul a 0 = 0 := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · exact nmul_zero 0
    · rw [nmul_of_ne_eq a ha 0, h0 (logf a)]
  have nmul_ne_zero : ∀ (a b : V) (ha : a ≠ 0) (hb : b ≠ 0), nmul a b ≠ 0 := by
    intro a b ha hb
    rw [nmul_of_ne_eq a ha b]
    intro h
    exact hb ((hsmul_eq_zero (logf a) b).mp h)
  have logf_nmul : ∀ (a b : V) (ha : a ≠ 0) (hb : b ≠ 0),
      logf (nmul a b) = logf a * logf b := by
    intro a b ha hb
    have hne := nmul_ne_zero a b ha hb
    have hval : nmul a b = (logf a * logf b) • v := by
      calc nmul a b = (logf a) • b := nmul_of_ne_eq a ha b
        _ = (logf a) • ((logf b) • v) := by conv_lhs => rw [← logf_smul b hb]
        _ = (logf a * logf b) • v := smul_smul _ _ _
    have hsub : (⟨nmul a b, hne⟩ : {x : V // x ≠ 0}) = eD (logf a * logf b) := by
      apply Subtype.ext
      show nmul a b = ((eD (logf a * logf b) : {x : V // x ≠ 0}) : V)
      rw [hval]
      exact (heDc (logf a * logf b)).symm
    rw [logf_of_ne _ hne, hsub, Equiv.symm_apply_apply]
  -- 6. the axioms
  have h_mul_assoc : ∀ a b c : V, nmul (nmul a b) c = nmul a (nmul b c) := by
    intro a b c
    rcases eq_or_ne a 0 with rfl | ha
    · rw [nmul_zero b, nmul_zero c, nmul_zero (nmul b c)]
    · rcases eq_or_ne b 0 with rfl | hb
      · rw [nmul_right_zero a, nmul_zero c, nmul_right_zero a]
      · rcases eq_or_ne c 0 with rfl | hc
        · rw [nmul_right_zero (nmul a b), nmul_right_zero b, nmul_right_zero a]
        · rw [nmul_of_ne_eq (nmul a b) (nmul_ne_zero a b ha hb) c, logf_nmul a b ha hb,
              nmul_of_ne_eq a ha (nmul b c), nmul_of_ne_eq b hb c, smul_smul]
  have h_mul_comm : ∀ a b : V, nmul a b = nmul b a := by
    intro a b
    rcases eq_or_ne a 0 with rfl | ha
    · rw [nmul_zero b, nmul_right_zero b]
    · rcases eq_or_ne b 0 with rfl | hb
      · rw [nmul_zero a, nmul_right_zero a]
      · calc nmul a b = (logf a * logf b) • v := by
              rw [nmul_of_ne_eq a ha b]
              conv_lhs => rw [← logf_smul b hb]
              rw [smul_smul]
          _ = (logf b * logf a) • v := by rw [hcommA]
          _ = nmul b a := by
              rw [nmul_of_ne_eq b hb a]
              conv_rhs => rw [← logf_smul a ha]
              rw [smul_smul]
  have logf_v : logf v = 1 := by
    have hsub : (⟨v, hv⟩ : {x : V // x ≠ 0}) = eD 1 := by
      apply Subtype.ext
      exact ((heDc 1).trans (one_smul A v)).symm
    rw [logf_of_ne v hv, hsub, Equiv.symm_apply_apply]
  have h_one_mul : ∀ a : V, nmul v a = a := by
    intro a
    rw [nmul_of_ne_eq v hv a, logf_v, one_smul]
  have h_left_distrib : ∀ a b c : V, nmul a (b + c) = nmul a b + nmul a c := by
    intro a b c
    rcases eq_or_ne a 0 with rfl | ha
    · rw [nmul_zero (b + c), nmul_zero b, nmul_zero c, zero_add]
    · rw [nmul_of_ne_eq a ha (b + c), nmul_of_ne_eq a ha b, nmul_of_ne_eq a ha c]
      exact hsmul (logf a) b c
  -- 7. the inverse
  let ninv : V → V := fun a => if h : a = 0 then 0 else (eD (eD.symm ⟨a, h⟩)⁻¹ : {x : V // x ≠ 0})
  have ninv_zero : ninv 0 = 0 := by
    show dite ((0 : V) = 0) (fun _ => (0 : V))
        (fun h => (eD (eD.symm ⟨0, h⟩)⁻¹ : {x : V // x ≠ 0})) = 0
    rw [dite_eq_left rfl]
  have ninv_of_ne : ∀ (a : V) (ha : a ≠ 0),
      ninv a = (eD (eD.symm ⟨a, ha⟩)⁻¹ : {x : V // x ≠ 0}) := by
    intro a ha
    show dite (a = 0) (fun _ => (0 : V))
        (fun h => (eD (eD.symm ⟨a, h⟩)⁻¹ : {x : V // x ≠ 0}))
      = (eD (eD.symm ⟨a, ha⟩)⁻¹ : {x : V // x ≠ 0})
    rw [dite_eq_right ha]
  have h_mul_inv : ∀ a : V, a ≠ 0 → nmul a (ninv a) = v := by
    intro a ha
    rw [ninv_of_ne a ha, nmul_of_ne_eq a ha, logf_of_ne a ha]
    rw [heDc ((eD.symm ⟨a, ha⟩)⁻¹)]
    rw [smul_smul, mul_inv_cancel, one_smul]
  have hpair : ∃ x y : V, x ≠ y := by
    have hlt : 1 < Fintype.card V := by
      rw [Nat.card_eq_fintype_card] at hcardV
      omega
    exact Fintype.exists_pair_of_one_lt_card hlt
  -- 8. V is an elementary abelian 2-group, hence has cardinality a power of two
  have h2nsmul : ∀ x : V, 2 • x = 0 := by
    intro x
    rw [two_nsmul]
    exact hchar x
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule (n := 2) h2nsmul
  let k : ℕ := Module.finrank (ZMod 2) V
  have hcardV2 : Fintype.card V = 2 ^ k := by
    dsimp only [k]
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      rw [hk0, pow_zero] at hcardV2
      rw [Nat.card_eq_fintype_card] at hcardV
      omega
    · exact hkpos
  -- 9. assemble the field
  letI : Mul V := ⟨nmul⟩
  letI : One V := ⟨v⟩
  letI : Inv V := ⟨ninv⟩
  let CR : CommRing V :=
    CommRing.ofMinimalAxioms add_assoc zero_add neg_add_cancel h_mul_assoc h_mul_comm h_one_mul
      h_left_distrib
  let DR : DivisionRing V :=
    { CR.toRing with
      inv := ninv
      mul_inv_cancel := fun a ha => h_mul_inv a ha
      inv_zero := ninv_zero
      exists_pair_ne := hpair
      nnqsmul := _
      nnqsmul_def := fun _ _ => rfl
      qsmul := _
      qsmul_def := fun _ _ => rfl }
  let hfield : Field V :=
    { toCommRing := CR
      exists_pair_ne := hpair
      mul_inv_cancel := fun a ha => h_mul_inv a ha
      inv_zero := ninv_zero
      nnqsmul := DR.nnqsmul
      nnqsmul_def := DR.nnqsmul_def
      qsmul := DR.qsmul
      qsmul_def := DR.qsmul_def }
  letI : Field V := hfield
  have hmul_eq : ∀ a b : V, a * b = nmul a b := fun a b => rfl
  have hvone : (1 : V) = v := rfl
  -- 10. the ring isomorphism with the Galois field
  haveI : Fintype (GaloisField 2 k) := Fintype.ofFinite _
  have hcards : Fintype.card V = Fintype.card (GaloisField 2 k) := by
    rw [hcardV2, ← Nat.card_eq_fintype_card (α := GaloisField 2 k),
        GaloisField.card 2 k (by omega)]
  let hiso : V ≃+* GaloisField 2 k := FiniteField.ringEquivOfCardEq hcards
  have heD_mul : ∀ a b : A, eDv (a * b) = eDv a * eDv b := by
    intro a b
    rw [heD (a * b), heD a, heD b, hmul_eq]
    rw [nmul_of_ne_eq (a • v) (hne0 a) (b • v), logf_smul_v a]
    exact (smul_smul a b v).symm
  have heD_mul_inv : ∀ a : A, eDv a * eDv a⁻¹ = v := by
    intro a
    rw [← heD_mul a a⁻¹, mul_inv_cancel, heD 1, one_smul]
  -- 11. the multiplicative isomorphism
  let φ0 : A →* (GaloisField 2 k)ˣ :=
    { toFun := fun a => Units.mk0 (hiso (eDv a)) (by
        intro h
        have h1 : hiso (eDv a) * hiso (eDv a⁻¹) = 1 := by
          have hmm : hiso (eDv a) * hiso (eDv a⁻¹) = hiso (eDv a * eDv a⁻¹) :=
            (hiso.map_mul (eDv a) (eDv a⁻¹)).symm
          rw [hmm, heD_mul_inv a]
          exact (congrArg hiso hvone.symm).trans hiso.map_one
        rw [h, zero_mul] at h1
        exact zero_ne_one h1)
      map_one' := by
        apply Units.ext
        simp only [Units.val_mk0, Units.val_one]
        rw [heD 1, one_smul]
        exact (congrArg hiso hvone.symm).trans hiso.map_one
      map_mul' := by
        intro a b
        apply Units.ext
        simp only [Units.val_mk0, Units.val_mul]
        have hmm : hiso (eDv a) * hiso (eDv b) = hiso (eDv a * eDv b) :=
          (hiso.map_mul (eDv a) (eDv b)).symm
        rw [hmm, heD_mul a b] }
  have hφ0inj : Function.Injective φ0 := by
    intro a b hab
    have h1 : hiso (eDv a) = hiso (eDv b) := by
      have := congrArg (fun u : (GaloisField 2 k)ˣ => (u : GaloisField 2 k)) hab
      simpa [φ0, Units.val_mk0] using this
    exact eD.injective (Subtype.ext (hiso.injective h1))
  have hφbij : Function.Bijective φ0 := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hφ0inj, ?_⟩
    have h1 : Fintype.card ((GaloisField 2 k)ˣ) = Fintype.card V - 1 := by
      rw [Fintype.card_units, hcards]
    have h2 : Fintype.card A = Fintype.card V - 1 := by
      rw [← Nat.card_eq_fintype_card (α := A), hcard, Nat.card_eq_fintype_card]
    omega
  let φ : A ≃* (GaloisField 2 k)ˣ := MulEquiv.ofBijective φ0 hφbij
  have hsmul_eq_mul : ∀ (a : A) (x : V), a • x = eDv a * x := by
    intro a x
    rw [hmul_eq]
    rw [nmul_of_ne_eq (eDv a) (hneD a) x, logf_eD a]
  have hfinal : ∀ (a : A) (x : V),
      hiso (a • x) = (φ a : GaloisField 2 k) * hiso x := by
    intro a x
    rw [hsmul_eq_mul a x]
    have hmm : hiso (eDv a * x) = hiso (eDv a) * hiso x := hiso.map_mul (eDv a) x
    rw [hmm]
    congr 1
  refine ⟨k, hk1, hiso.toEquiv, φ, ?_, ?_⟩
  · intro x y
    exact hiso.map_add x y
  · intro a x
    exact hfinal a x

-- ============================================================================
-- The `2`-group `Q` has exponent two
-- ============================================================================

theorem exponent_two_of_regular {G : Type} [Group G] [Finite G] (Q D : Subgroup G)
    (h2 : IsPGroup 2 Q)
    (hDnorm : D ≤ Subgroup.normalizer (Q : Set G))
    (hfpf : ∀ d ∈ D, d ≠ 1 → ∀ x ∈ Q, d * x * d⁻¹ = x → x = 1)
    (hreg : Nat.card D = Nat.card Q - 1) :
    ∀ x ∈ Q, x ^ 2 = 1 := by
  classical
  let conjQ : ↥D → ↥Q → ↥Q := fun d x =>
    ⟨(d : G) * (x : G) * (d : G)⁻¹,
      (Subgroup.le_normalizer_iff.mp hDnorm) (d : G) d.2 (x : G) x.2⟩
  have hconj_coe : ∀ (d : ↥D) (x : ↥Q), ((conjQ d x : ↥Q) : G) = (d : G) * (x : G) * (d : G)⁻¹ :=
    fun d x => rfl
  have hfpf' : ∀ d : ↥D, d ≠ 1 → ∀ x : ↥Q, conjQ d x = x → x = 1 := by
    intro d hd x hx
    have hval : (d : G) * (x : G) * (d : G)⁻¹ = (x : G) := by
      have := congrArg (fun y : ↥Q => (y : G)) hx
      rwa [hconj_coe] at this
    exact Subtype.ext (hfpf d d.2 (fun h => hd (Subtype.ext h)) (x : G) x.2 hval)
  have hcardD : 1 ≤ Nat.card ↥D := Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
  have hcardQ : 2 ≤ Nat.card ↥Q := by omega
  obtain ⟨v, hv⟩ : ∃ v : ↥Q, v ≠ 1 := by
    by_contra h
    push_neg at h
    have hsub : Subsingleton ↥Q := ⟨fun a b => by rw [h a, h b]⟩
    have h1 : Nat.card ↥Q = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    omega
  have hinj : Function.Injective (fun d : ↥D => conjQ d v) := by
    intro a b hab
    have h1 : conjQ (b⁻¹ * a) v = v := by
      apply Subtype.ext
      have hab' : (a : G) * (v : G) * (a : G)⁻¹ = (b : G) * (v : G) * (b : G)⁻¹ := by
        have := congrArg (fun y : ↥Q => (y : G)) hab
        rwa [hconj_coe, hconj_coe] at this
      rw [hconj_coe, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((b : G)⁻¹ * (a : G)) * (v : G) * ((b : G)⁻¹ * (a : G))⁻¹
          = (b : G)⁻¹ * ((a : G) * (v : G) * (a : G)⁻¹) * (b : G) from by group]
      rw [hab']
      group
    by_contra hne
    have hb1 : b⁻¹ * a ≠ 1 := fun h => hne (by
      calc a = b * (b⁻¹ * a) := by group
        _ = b := by rw [h, mul_one])
    exact hv (hfpf' (b⁻¹ * a) hb1 v h1)
  have hne1 : ∀ d : ↥D, conjQ d v ≠ 1 := by
    intro d hcon
    have h1 : ((conjQ d v : ↥Q) : G) = 1 := by rw [hcon]; rfl
    rw [hconj_coe] at h1
    exact hv (Subtype.ext (by
      have := congrArg (fun z => (d : G)⁻¹ * z * (d : G)) h1
      simpa [mul_assoc] using this))
  haveI : Fintype ↥Q := Fintype.ofFinite _
  haveI : Fintype ↥D := Fintype.ofFinite _
  have hcard_ne : Fintype.card {x : ↥Q // x ≠ 1} = Nat.card ↥Q - 1 := by
    have h := Fintype.card_subtype_compl (α := ↥Q) (fun x => x = 1)
    rw [Fintype.card_subtype_eq (1 : ↥Q)] at h
    rw [h, Nat.card_eq_fintype_card]
  have hsurj : ∀ x : {x : ↥Q // x ≠ 1}, ∃ d : ↥D, conjQ d v = x := by
    have hbijf : Function.Bijective
        (fun d : ↥D => (⟨conjQ d v, hne1 d⟩ : {x : ↥Q // x ≠ 1})) := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨fun a b hab => hinj (Subtype.ext_iff.mp hab), ?_⟩
      rw [hcard_ne, ← hreg, Nat.card_eq_fintype_card]
    intro x
    obtain ⟨d, hd⟩ := hbijf.2 x
    exact ⟨d, congrArg Subtype.val hd⟩
  have horder : ∀ x : ↥Q, x ≠ 1 → orderOf x = orderOf v := by
    intro x hx
    obtain ⟨d, hd⟩ := hsurj ⟨x, hx⟩
    have hd' : conjQ d v = x := hd
    rw [← hd']
    have h2' : orderOf (conjQ d v) = orderOf ((conjQ d v : ↥Q) : G) :=
      (Subgroup.orderOf_coe _).symm
    have h3' : orderOf ((conjQ d v : ↥Q) : G) = orderOf (v : G) := by
      symm
      refine SemiconjBy.orderOf_eq (d : G) ?_
      show (d : G) * (v : G) = ((conjQ d v : ↥Q) : G) * (d : G)
      rw [hconj_coe]; group
    have h4' : orderOf (v : G) = orderOf v := Subgroup.orderOf_coe v
    exact h2'.trans (h3'.trans h4')
  obtain ⟨k, hk⟩ := h2.exists_orderOf_eq_pow v
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      rw [hk0, pow_zero] at hk
      exact hv (orderOf_eq_one_iff.mp hk)
    · exact hkpos
  have hk_eq : k = 1 := by
    by_contra hkne
    have hk2 : 2 ≤ k := by omega
    have hv2 : v ^ 2 ≠ 1 := by
      intro hcon
      have hdvd : orderOf v ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hcon
      rw [hk] at hdvd
      have hle : 2 ^ k ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      have hge : 4 ≤ 2 ^ k := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      omega
    have hpow : orderOf (v ^ 2) = 2 ^ k := by
      rw [horder (v ^ 2) hv2, hk]
    have hgcd : orderOf (v ^ 2) = 2 ^ k / 2 := by
      rw [orderOf_pow, hk, Nat.gcd_eq_right (dvd_pow_self 2 (by omega))]
    have heq : 2 ^ k = 2 ^ k / 2 := hpow.symm.trans hgcd
    have hlt : 2 ^ k / 2 < 2 ^ k := Nat.div_lt_self (by positivity) (by norm_num)
    omega
  intro x hx
  have hfinal : (⟨x, hx⟩ : ↥Q) ^ 2 = 1 := by
    by_cases h1 : (⟨x, hx⟩ : ↥Q) = 1
    · rw [h1]; exact one_pow 2
    · have ho : orderOf (⟨x, hx⟩ : ↥Q) = 2 := by
        rw [horder (⟨x, hx⟩ : ↥Q) h1, hk, hk_eq, pow_one]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [ho])
  have := congrArg (fun y : ↥Q => (y : G)) hfinal
  simpa using this

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem field_coordinates_of_regular {G : Type} [Group G] [Finite G] (Q D : Subgroup G)
    (h2 : IsPGroup 2 Q) (habQ : Submission.Blueprint.IsAbelianSubgroup Q)
    (habD : Submission.Blueprint.IsAbelianSubgroup D)
    (hDnorm : D ≤ Subgroup.normalizer (Q : Set G))
    (hfpf : ∀ d ∈ D, d ≠ 1 → ∀ x ∈ Q, d * x * d⁻¹ = x → x = 1)
    (hreg : Nat.card D = Nat.card Q - 1) :
    ∃ (n : ℕ) (_ : 1 ≤ n) (e : Q ≃ GaloisField 2 n) (φ : D ≃* (GaloisField 2 n)ˣ),
      (∀ x y : Q, e (x * y) = e x + e y) ∧
      (∀ (d : D) (x : Q),
        e ⟨(d : G) * (x : G) * (d : G)⁻¹,
            (Subgroup.le_normalizer_iff.mp hDnorm) (d : G) d.2 (x : G) x.2⟩
          = (φ d : GaloisField 2 n) * e x) := by
  classical
  have hcommD : ∀ a b : ↥D, a * b = b * a :=
    fun x y => Subtype.ext (by simpa using habD x x.2 y y.2)
  have hexp2 : ∀ x ∈ Q, x ^ 2 = 1 := exponent_two_of_regular Q D h2 hDnorm hfpf hreg
  let conjQ : ↥D → ↥Q → ↥Q := fun d x =>
    ⟨(d : G) * (x : G) * (d : G)⁻¹,
      (Subgroup.le_normalizer_iff.mp hDnorm) (d : G) d.2 (x : G) x.2⟩
  have hconj_coe : ∀ (d : ↥D) (x : ↥Q), ((conjQ d x : ↥Q) : G) = (d : G) * (x : G) * (d : G)⁻¹ :=
    fun d x => rfl
  have hconj_mul : ∀ (d : ↥D) (x y : ↥Q), conjQ d (x * y) = conjQ d x * conjQ d y := by
    intro d x y
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hconj_coe]
    group
  -- `↥Q` as an additive group with `+ = *` and `0 = 1`
  letI : Add ↥Q := ⟨fun x y => x * y⟩
  letI : Zero ↥Q := ⟨1⟩
  letI : Neg ↥Q := ⟨fun x => x⁻¹⟩
  let agQ : AddGroup ↥Q :=
    AddGroup.ofLeftAxioms (fun a b c : ↥Q => mul_assoc a b c)
      (fun a : ↥Q => one_mul a) (fun a : ↥Q => inv_mul_cancel a)
  letI : AddCommGroup ↥Q :=
    { agQ with
      add_comm := fun a b : ↥Q => by
        change a * b = b * a
        exact Subtype.ext (by simpa using habQ a a.2 b b.2) }
  letI : MulAction ↥D ↥Q :=
    { smul := conjQ
      one_smul := by
        intro x
        show conjQ 1 x = x
        apply Subtype.ext
        show (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
        group
      mul_smul := by
        intro d e x
        show conjQ (d * e) x = conjQ d (conjQ e x)
        apply Subtype.ext
        simp only [hconj_coe, Subgroup.coe_mul]
        group }
  have hchar : ∀ x : ↥Q, x + x = (0 : ↥Q) := by
    intro x
    show x * x = 1
    rw [← pow_two]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hexp2 (x : G) x.2
  have hsmul : ∀ (a : ↥D) (x y : ↥Q), a • (x + y) = a • x + a • y := by
    intro a x y
    show conjQ a (x * y) = conjQ a x * conjQ a y
    exact hconj_mul a x y
  have hfpf'' : ∀ a : ↥D, a ≠ 1 → ∀ x : ↥Q, conjQ a x = x → x = 1 := by
    intro a ha x hx
    have hval : (a : G) * (x : G) * (a : G)⁻¹ = (x : G) := by
      have := congrArg (fun y : ↥Q => (y : G)) hx
      rwa [hconj_coe] at this
    exact Subtype.ext (hfpf a a.2 (fun h => ha (Subtype.ext h)) (x : G) x.2 hval)
  have hfpf' : ∀ a : ↥D, a ≠ 1 → ∀ x : ↥Q, a • x = x → x = (0 : ↥Q) := by
    intro a ha x hx
    show x = 1
    exact hfpf'' a ha x hx
  have hcard' : Nat.card ↥D = Nat.card ↥Q - 1 := hreg
  obtain ⟨n, hn, e, φ, h1, h2'⟩ :=
    regular_coordinates_abstract (V := ↥Q) (A := ↥D) hcommD hchar hsmul hfpf' hcard'
  refine ⟨n, hn, e, φ, ?_, ?_⟩
  · intro x y
    exact h1 x y
  · intro d x
    have hconj : (⟨(d : G) * (x : G) * (d : G)⁻¹,
        (Subgroup.le_normalizer_iff.mp hDnorm) (d : G) d.2 (x : G) x.2⟩ : ↥Q)
        = conjQ d x := rfl
    rw [hconj]
    rw [show conjQ d x = d • x from rfl]
    exact h2' d x

end Work.ZassenhausPSL2.ZData
