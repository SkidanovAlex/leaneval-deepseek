/-
Copyright (c) 2024. All rights reserved.

# Higman (1963), §4 Lemma 6: the module-theoretic core

This file contains the module-theoretic heart of Higman's §4 Lemma 6 in the form needed for the
`C₄`-exclusion (`Work.Higman.no_square_of_maximal_new`), namely `Work.Higman.core_alt_pairing`.

* `Work.Higman.singer_data_of_transitive` — a linear automorphism of an `𝔽₂`-vector space of
  cardinality `2 ^ n` (`n ≥ 2`) which is transitive on the non-zero vectors is a Singer cycle
  (order `2 ^ n - 1`, fixed-point free).
* `Work.Higman.core_alt_pairing` — given two such `ξ`-modules `V`, `W`, a non-zero alternating
  biadditive `ξ`-equivariant `B : V × V → W`, a quadratic refinement `s` of `B` vanishing only at
  `0`, and a non-zero biadditive `ξ`-equivariant `β : V × W → W` with `β a (s a) = 0`, we reach a
  contradiction (Higman's §4 Lemma 6).
-/

import Mathlib
import Submission.Work.Higman.exists_singer_iso
import Submission.Work.Higman.bilinear_frob
import Submission.Work.Higman.monomial_form
import Submission.Work.Higman.clo_bifrob
import Submission.Work.Higman.clo_arith
import Submission.Work.Higman.bivariate_monomial_indep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open scoped commutatorElement

namespace Work.Higman

/-! ## Characteristic-two helpers -/

/-- In a module over `ZMod 2` every element is its own negative. -/
theorem add_self_eq_zero_zmod2' {W : Type} [AddCommGroup W] [Module (ZMod 2) W] (x : W) :
    x + x = 0 := by
  have h : (1 + 1 : ZMod 2) • x = x + x := by rw [add_smul, one_smul]
  rw [← h, show (1 + 1 : ZMod 2) = 0 from by decide, zero_smul]

/-- In a module over `ZMod 2` every element is its own negative. -/
theorem neg_eq_self_zmod2' {W : Type} [AddCommGroup W] [Module (ZMod 2) W] (x : W) : -x = x :=
  (eq_neg_of_add_eq_zero_left (add_self_eq_zero_zmod2' x)).symm

/-- `2 ^ m ≡ 2 ^ (m % n)` modulo `2 ^ n - 1`. -/
theorem pow_two_modEq_mod' {n m : ℕ} (hn : 1 ≤ n) :
    (2 : ℕ) ^ m ≡ 2 ^ (m % n) [MOD 2 ^ n - 1] := by
  have h2n : (2 : ℕ) ^ n ≡ 1 [MOD 2 ^ n - 1] := by
    have h2n1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    show ((2 : ℕ) ^ n) % (2 ^ n - 1) = 1 % (2 ^ n - 1)
    nth_rewrite 1 [show (2 : ℕ) ^ n = 1 + (2 ^ n - 1) from by omega]
    exact Nat.add_mod_right 1 (2 ^ n - 1)
  have hkey : ((2 : ℕ) ^ n) ^ (m / n) * 2 ^ (m % n) = 2 ^ m := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h := Nat.ModEq.mul (h2n.pow (m / n)) (Nat.ModEq.refl (2 ^ (m % n)))
  rw [one_pow, one_mul] at h
  rwa [hkey] at h

/-- Two distinct powers of two, both with exponents below `2 ^ n`, are never congruent to `1`
modulo `2 ^ n - 1`, formulated after reduction of the exponents modulo `n`. -/
theorem two_pow_sum_mod_ne_one' {n i j s : ℕ} (hn : 2 ≤ n) (hi : i < n) (hj : j < n)
    (hne : i ≠ j) :
    ¬ ((2 : ℕ) ^ ((i + s) % n) + 2 ^ ((j + s) % n) ≡ 1 [MOD 2 ^ n - 1]) := by
  refine two_pow_sum_mod_ne_one hn (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) ?_
  intro hcontra
  exact hne (Nat.ModEq.eq_of_lt_of_lt
    (Nat.ModEq.add_right_cancel' s (show i + s ≡ j + s [MOD n] from hcontra)) hi hj)


/-! ## Singer data from transitivity -/

/-- A linear automorphism of a finite `𝔽₂`-vector space of cardinality `2 ^ n` (`2 ≤ n`) which
acts transitively on the non-zero vectors has order `2 ^ n - 1` and no non-zero fixed vector. -/
theorem singer_data_of_transitive {n : ℕ} (hn : 2 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : Nat.card V = 2 ^ n) (ξ : V ≃ₗ[ZMod 2] V)
    (htrans : ∀ a b : V, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξ ^ k) a = b) :
    orderOf ξ = 2 ^ n - 1 ∧ (∀ v : V, ξ v = v → v = 0) := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
      (fun a b h => LinearEquiv.ext (fun x => congrFun h x))
  have hV' : Fintype.card V = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hV
  have hcard2 : 2 ≤ Fintype.card V := by
    rw [hV']
    have h1 : 1 < (2 : ℕ) ^ n := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  -- Powers of `ξ` fixing a non-zero vector are trivial.
  have hstab : ∀ (k : ℕ) (u : V), u ≠ 0 → (ξ ^ k) u = u → (ξ ^ k) = 1 := by
    intro k u hu hk
    refine LinearEquiv.ext (fun x => ?_)
    show (ξ ^ k) x = x
    rcases eq_or_ne x 0 with rfl | hx
    · rw [map_zero]
    · obtain ⟨j, hj⟩ := htrans u x hu hx
      have h1 : (ξ ^ k) * (ξ ^ j) = ξ ^ (k + j) := (pow_add ξ k j).symm
      have h2 : (ξ ^ j) * (ξ ^ k) = ξ ^ (j + k) := (pow_add ξ j k).symm
      have hcomm : (ξ ^ k) ((ξ ^ j) u) = (ξ ^ j) ((ξ ^ k) u) := by
        rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, h1, h2, Nat.add_comm]
      rw [← hj, hcomm, hk]
  -- the orbit of `v₀` is `V \ {0}`
  have hmem_orbit : ∀ k : ℕ, (ξ ^ k) v₀ ∈ (Finset.univ : Finset V).erase 0 := by
    intro k
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h0
    exact hv₀ ((ξ ^ k).injective (by rw [h0, map_zero]))
  have horbit_eq : Set.range (fun k : ℕ => (ξ ^ k) v₀) = {x : V | x ≠ 0} := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      simpa using hmem_orbit k
    · intro hx
      obtain ⟨k, hk⟩ := htrans v₀ x hv₀ hx
      exact ⟨k, hk⟩
  have hperiod : Set.range (fun k : ℕ => (ξ ^ k) v₀)
      = ((Finset.range (orderOf ξ)).image (fun k => (ξ ^ k) v₀) : Set V) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨k % orderOf ξ,
        Finset.mem_range.mpr (Nat.mod_lt _ (orderOf_pos ξ)), ?_⟩)
      show (ξ ^ (k % orderOf ξ)) v₀ = (ξ ^ k) v₀
      rw [pow_mod_orderOf]
    · rintro hx
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact ⟨k, rfl⟩
  -- Lower bound: `2 ^ n - 1 ≤ orderOf ξ`
  have hge : 2 ^ n - 1 ≤ orderOf ξ := by
    have hsub : (Finset.univ : Finset V).erase 0
        ⊆ (Finset.range (orderOf ξ)).image (fun k => (ξ ^ k) v₀) := by
      intro x hx
      rw [Finset.mem_erase] at hx
      obtain ⟨hx0, -⟩ := hx
      have hxr : x ∈ Set.range (fun k : ℕ => (ξ ^ k) v₀) := by
        rw [horbit_eq]; exact hx0
      rw [hperiod] at hxr
      exact Finset.mem_coe.mp hxr
    have h1 := Finset.card_le_card hsub
    have h2 : ((Finset.range (orderOf ξ)).image (fun k => (ξ ^ k) v₀)).card ≤ orderOf ξ := by
      have h := Finset.card_image_le (s := Finset.range (orderOf ξ))
        (f := fun k => (ξ ^ k) v₀)
      rwa [Finset.card_range] at h
    have h3 : ((Finset.univ : Finset V).erase 0).card = 2 ^ n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : V)), Finset.card_univ, hV']
    omega
  -- Upper bound: `orderOf ξ ≤ 2 ^ n - 1`
  have hle : orderOf ξ ≤ 2 ^ n - 1 := by
    by_contra hcon
    push_neg at hcon
    have hcard_lt : ((Finset.univ : Finset V).erase 0).card < (Finset.range (2 ^ n)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : V)), Finset.card_univ, hV',
        Finset.card_range]
      omega
    obtain ⟨a, ha, b, hb, hab, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard_lt (fun k _ => hmem_orbit k)
    rw [Finset.mem_range] at ha hb
    have key : ∀ a b : ℕ, a < 2 ^ n → b < 2 ^ n → a < b → (ξ ^ a) v₀ = (ξ ^ b) v₀ → False := by
      intro a b _ _ hlt heq
      have hpos : 0 < b - a := by omega
      have h1 : (ξ ^ (b - a)) ((ξ ^ a) v₀) = (ξ ^ a) v₀ := by
        have h2 : (ξ ^ (b - a)) ((ξ ^ a) v₀) = (ξ ^ b) v₀ := by
          rw [← LinearEquiv.mul_apply, ← pow_add, Nat.sub_add_cancel (le_of_lt hlt)]
        rw [h2, heq]
      have hne : (ξ ^ a) v₀ ≠ 0 := by
        intro h0
        exact hv₀ ((ξ ^ a).injective (by rw [h0, map_zero]))
      have hpow := hstab (b - a) ((ξ ^ a) v₀) hne h1
      have hdvd : orderOf ξ ∣ b - a := orderOf_dvd_of_pow_eq_one hpow
      have := Nat.le_of_dvd hpos hdvd
      omega
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact key a b ha hb hlt heq
    · exact key b a hb ha hgt heq.symm
  exact ⟨le_antisymm hle hge, fun v hv => by
    by_contra hv0
    have hall : ∀ b : V, b ≠ 0 → b = v := by
      intro b hb
      obtain ⟨k, hk⟩ := htrans v b hv0 hb
      have hfix : ∀ k : ℕ, (ξ ^ k) v = v := by
        intro k
        induction k with
        | zero => rfl
        | succ j ih =>
            have hstep : (ξ ^ (j + 1)) v = ξ ((ξ ^ j) v) := by
              rw [pow_succ', LinearEquiv.mul_apply]
            rw [hstep, ih, hv]
      rw [← hk]; exact hfix k
    have hsub : (Finset.univ : Finset V) ⊆ {0, v} := by
      intro x _
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (hall x hx))
    have hc := Finset.card_le_card hsub
    rw [Finset.card_univ] at hc
    have h2 : ({0, v} : Finset V).card ≤ 2 := by
      have h3 := Finset.card_insert_le (0 : V) {v}
      simp only [Finset.card_singleton] at h3
      omega
    have hVle : Fintype.card V ≤ 2 := by omega
    rw [hV'] at hVle
    have hge4 : 4 ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega⟩

/-! ## The core theorem -/

/-- **Higman (1963), §4 Lemma 6, module form.** -/
theorem core_alt_pairing {n : ℕ} (hn : 2 ≤ n)
    {V W : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (hVcard : Nat.card V = 2 ^ n) (hWcard : Nat.card W = 2 ^ n)
    (ξV : V ≃ₗ[ZMod 2] V) (ξW : W ≃ₗ[ZMod 2] W)
    (hVtrans : ∀ a b : V, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξV ^ k) a = b)
    (hWtrans : ∀ a b : W, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξW ^ k) a = b)
    (B : V → V → W) (hB1 : ∀ a b c : V, B (a + b) c = B a c + B b c)
    (hB2 : ∀ a b c : V, B a (b + c) = B a b + B a c) (hBdiag : ∀ a : V, B a a = 0)
    (hBeq : ∀ a b : V, ξW (B a b) = B (ξV a) (ξV b)) (hBne : ∃ a b : V, B a b ≠ 0)
    (s : V → W) (hs0 : s 0 = 0) (hseq : ∀ a : V, ξW (s a) = s (ξV a))
    (hspol : ∀ a b : V, s (a + b) + s a + s b = B a b)
    (hsne : ∀ a : V, a ≠ 0 → s a ≠ 0)
    (β : V → W → W) (hβ1 : ∀ a a' : V, ∀ b : W, β (a + a') b = β a b + β a' b)
    (hβ2 : ∀ a : V, ∀ b b' : W, β a (b + b') = β a b + β a b')
    (hβeq : ∀ a : V, ∀ b : W, ξW (β a b) = β (ξV a) (ξW b))
    (hβrel : ∀ a : V, β a (s a) = 0) (hβne : ∃ a : V, ∃ b : W, β a b ≠ 0) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVord, hVfree⟩ := singer_data_of_transitive hn hVcard ξV hVtrans
  obtain ⟨hWord, hWfree⟩ := singer_data_of_transitive hn hWcard ξW hWtrans
  obtain ⟨φV, ν, hνord, hνeq⟩ := exists_singer_iso (by omega : 0 < n) hVcard ξV hVord hVfree
  obtain ⟨φW, γ, hγord, hγeq⟩ := exists_singer_iso (by omega : 0 < n) hWcard ξW hWord hWfree
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hFcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 n (by omega)
  have hνF : orderOf ((ν : (GaloisField 2 n)ˣ) : GaloisField 2 n) = 2 ^ n - 1 := by
    rw [orderOf_units]; exact hνord
  have hγF : orderOf ((γ : (GaloisField 2 n)ˣ) : GaloisField 2 n) = 2 ^ n - 1 := by
    rw [orderOf_units]; exact hγord
  have hνfin : IsOfFinOrder ((ν : (GaloisField 2 n)ˣ) : GaloisField 2 n) := by
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨2 ^ n - 1, ?_, ?_⟩
    · have h1 : 1 < (2 : ℕ) ^ n := Nat.one_lt_pow (by omega) (by norm_num)
      omega
    · have h := pow_orderOf_eq_one ((ν : (GaloisField 2 n)ˣ) : GaloisField 2 n)
      rwa [hνF] at h
  have hνsymm : ∀ x : GaloisField 2 n,
      φV.symm ((ν : GaloisField 2 n) * x) = ξV (φV.symm x) := by
    intro x
    have h := congrArg φV.symm (hνeq (φV.symm x))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hγsymm : ∀ y : GaloisField 2 n,
      φW.symm ((γ : GaloisField 2 n) * y) = ξW (φW.symm y) := by
    intro y
    have h := congrArg φW.symm (hγeq (φW.symm y))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] at h
    exact h.symm
  let BV : GaloisField 2 n → GaloisField 2 n → GaloisField 2 n :=
    fun x y => φW (B (φV.symm x) (φV.symm y))
  let sV : GaloisField 2 n → GaloisField 2 n := fun x => φW (s (φV.symm x))
  let βV : GaloisField 2 n → GaloisField 2 n → GaloisField 2 n :=
    fun x y => φW (β (φV.symm x) (φW.symm y))
  have hBsym : ∀ a b : V, B a b = B b a := by
    intro a b
    have h : B a b + B b a = 0 := by
      have hh := hBdiag (a + b)
      simp only [hB1, hB2, hBdiag, zero_add, add_zero] at hh
      exact hh
    rw [eq_neg_of_add_eq_zero_left h, neg_eq_self_zmod2']
  have hBV1 : ∀ x x' y, BV (x + x') y = BV x y + BV x' y := by
    intro x x' y
    show φW (B (φV.symm (x + x')) (φV.symm y))
        = φW (B (φV.symm x) (φV.symm y)) + φW (B (φV.symm x') (φV.symm y))
    rw [map_add, hB1, map_add]
  have hBV2 : ∀ x y y', BV x (y + y') = BV x y + BV x y' := by
    intro x y y'
    show φW (B (φV.symm x) (φV.symm (y + y')))
        = φW (B (φV.symm x) (φV.symm y)) + φW (B (φV.symm x) (φV.symm y'))
    rw [map_add, hB2, map_add]
  have hBVsym : ∀ x y, BV x y = BV y x := by
    intro x y
    show φW (B (φV.symm x) (φV.symm y)) = φW (B (φV.symm y) (φV.symm x))
    rw [hBsym]
  have hBVdiag : ∀ x, BV x x = 0 := by
    intro x
    show φW (B (φV.symm x) (φV.symm x)) = 0
    rw [hBdiag, map_zero]
  have hBVeq : ∀ x y, BV ((ν : GaloisField 2 n) * x) ((ν : GaloisField 2 n) * y)
      = (γ : GaloisField 2 n) * BV x y := by
    intro x y
    show φW (B (φV.symm ((ν : GaloisField 2 n) * x)) (φV.symm ((ν : GaloisField 2 n) * y)))
        = (γ : GaloisField 2 n) * φW (B (φV.symm x) (φV.symm y))
    rw [hνsymm x, hνsymm y, ← hBeq, hγeq]
  have hBVne : ∃ x y, BV x y ≠ 0 := by
    obtain ⟨a, b, hab⟩ := hBne
    refine ⟨φV a, φV b, fun h => hab ?_⟩
    have h0 : φW (B a b) = 0 := by
      have : φW (B (φV.symm (φV a)) (φV.symm (φV b))) = 0 := h
      simpa using this
    exact φW.injective (by rw [h0, map_zero])
  have hsV0 : sV 0 = 0 := by
    show φW (s (φV.symm 0)) = 0
    rw [map_zero, hs0, map_zero]
  have hsVeq : ∀ x, sV ((ν : GaloisField 2 n) * x) = (γ : GaloisField 2 n) * sV x := by
    intro x
    show φW (s (φV.symm ((ν : GaloisField 2 n) * x)))
        = (γ : GaloisField 2 n) * φW (s (φV.symm x))
    rw [hνsymm x, ← hseq, hγeq]
  have hsVne : ∀ x, x ≠ 0 → sV x ≠ 0 := by
    intro x hx h0
    have h0' : φW (s (φV.symm x)) = 0 := h0
    have h1 : φV.symm x ≠ 0 := by
      intro h1'
      exact hx (by rw [← LinearEquiv.apply_symm_apply φV x, h1', map_zero])
    have h2 : s (φV.symm x) = 0 := φW.injective (by rw [h0', map_zero])
    exact hsne _ h1 h2
  have hsVpol : ∀ x y, sV (x + y) + sV x + sV y = BV x y := by
    intro x y
    show φW (s (φV.symm (x + y))) + φW (s (φV.symm x)) + φW (s (φV.symm y))
        = φW (B (φV.symm x) (φV.symm y))
    rw [map_add, ← map_add, ← map_add, ← hspol]
  have hsVadd1 : ∀ α α' γ', sV (α + α' + γ') + sV (α + α') + sV γ'
      = (sV (α + γ') + sV α + sV γ') + (sV (α' + γ') + sV α' + sV γ') := by
    intro α α' γ'
    have hl : sV (α + α' + γ') + sV (α + α') + sV γ' = BV (α + α') γ' := by
      rw [show α + α' + γ' = (α + α') + γ' from by abel]
      exact hsVpol (α + α') γ'
    rw [hl, hsVpol α γ', hsVpol α' γ', hBV1]
  have hsVadd2 : ∀ α γ γ', sV (α + (γ + γ')) + sV α + sV (γ + γ')
      = (sV (α + γ) + sV α + sV γ) + (sV (α + γ') + sV α + sV γ') := by
    intro α γ γ'
    have hl : sV (α + (γ + γ')) + sV α + sV (γ + γ') = BV α (γ + γ') := hsVpol α (γ + γ')
    rw [hl, hsVpol α γ, hsVpol α γ', hBV2]
  have hβV1 : ∀ x x' y, βV (x + x') y = βV x y + βV x' y := by
    intro x x' y
    show φW (β (φV.symm (x + x')) (φW.symm y))
        = φW (β (φV.symm x) (φW.symm y)) + φW (β (φV.symm x') (φW.symm y))
    rw [map_add, hβ1, map_add]
  have hβV2 : ∀ x y y', βV x (y + y') = βV x y + βV x y' := by
    intro x y y'
    show φW (β (φV.symm x) (φW.symm (y + y')))
        = φW (β (φV.symm x) (φW.symm y)) + φW (β (φV.symm x) (φW.symm y'))
    rw [map_add, hβ2, map_add]
  have hβVeq : ∀ x y, βV ((ν : GaloisField 2 n) * x) ((γ : GaloisField 2 n) * y)
      = (γ : GaloisField 2 n) * βV x y := by
    intro x y
    show φW (β (φV.symm ((ν : GaloisField 2 n) * x)) (φW.symm ((γ : GaloisField 2 n) * y)))
        = (γ : GaloisField 2 n) * φW (β (φV.symm x) (φW.symm y))
    rw [hνsymm x, hγsymm y, ← hβeq, hγeq]
  have hβVrel : ∀ x, βV x (sV x) = 0 := by
    intro x
    show φW (β (φV.symm x) (φW.symm (φW (s (φV.symm x))))) = 0
    rw [LinearEquiv.symm_apply_apply, hβrel, map_zero]
  have hβVne : ∃ x y, βV x y ≠ 0 := by
    obtain ⟨a, b, hab⟩ := hβne
    refine ⟨φV a, φW b, fun h => hab ?_⟩
    have h0 : φW (β a b) = 0 := by
      have : φW (β (φV.symm (φV a)) (φW.symm (φW b))) = 0 := h
      simpa using this
    exact φW.injective (by rw [h0, map_zero])
  -- ## Step 1: the alternating form `B`
  obtain ⟨d, hdsym, hddiag, hBexp⟩ := bilinear_frob hFcard BV (fun y x x' => hBV1 x x' y) hBV2 hBVsym hBVdiag
  have hdcond : ∀ k l : ℕ, k < n → l < n →
      d k l * ((ν : GaloisField 2 n) ^ (2 ^ k + 2 ^ l) - (γ : GaloisField 2 n)) = 0 := by
    intro k l hk hl
    refine bivariate_monomial_indep hFcard
      (fun k l => d k l * ((ν : GaloisField 2 n) ^ (2 ^ k + 2 ^ l) - (γ : GaloisField 2 n)))
      ?_ k (Finset.mem_range.mpr hk) l (Finset.mem_range.mpr hl)
    intro x y
    have he := hBVeq x y
    rw [hBexp ((ν : GaloisField 2 n) * x) ((ν : GaloisField 2 n) * y), hBexp x y] at he
    rw [← scale_rewrite d n (ν : GaloisField 2 n) (γ : GaloisField 2 n) x y, he, sub_self]
  have hd0 : ∃ k l, k < n ∧ l < n ∧ d k l ≠ 0 := by
    obtain ⟨x0, y0, hxy⟩ := hBVne
    by_contra hc
    exact hxy (by
      rw [hBexp x0 y0]
      refine Finset.sum_eq_zero (fun k hk => Finset.sum_eq_zero (fun l hl => ?_))
      have h0 : d k l = 0 := by
        by_contra hne
        exact hc ⟨k, l, Finset.mem_range.mp hk, Finset.mem_range.mp hl, hne⟩
      rw [h0]; ring)
  obtain ⟨k1, l1, hk1n, hl1n, hdk1l1⟩ := hd0
  have hγν1 : (ν : GaloisField 2 n) ^ (2 ^ k1 + 2 ^ l1) = (γ : GaloisField 2 n) := by
    have h := hdcond k1 l1 hk1n hl1n
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hdk1l1
    · rwa [sub_eq_zero] at h1
  have hk1l1 : k1 ≠ l1 := by
    intro hEq
    rw [hEq] at hdk1l1
    exact hdk1l1 (hddiag l1)
  obtain ⟨i, j, hij, hjn, hγν⟩ : ∃ i j, i < j ∧ j < n ∧
      (ν : GaloisField 2 n) ^ (2 ^ i + 2 ^ j) = (γ : GaloisField 2 n) := by
    rcases lt_or_gt_of_ne hk1l1 with hlt | hgt
    · exact ⟨k1, l1, hlt, hl1n, hγν1⟩
    · exact ⟨l1, k1, hgt, hk1n, by simpa [add_comm] using hγν1⟩
  rcases (show n = 2 ∨ 3 ≤ n by omega) with hn2 | hn3
  · -- ## `n = 2`: already impossible
    subst hn2
    exfalso
    have hi0 : i = 0 := by omega
    have hj1 : j = 1 := by omega
    have hν3 : ((ν : (GaloisField 2 2)ˣ) : GaloisField 2 2) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one ((ν : (GaloisField 2 2)ˣ) : GaloisField 2 2)
      rw [hνF] at h
      norm_num at h
      exact h
    have hγ1 : ((γ : (GaloisField 2 2)ˣ) : GaloisField 2 2) = 1 := by
      rw [← hγν, hi0, hj1, show (2 : ℕ) ^ 0 + 2 ^ 1 = 3 from by norm_num]
      exact hν3
    rw [hγ1] at hγF
    simp at hγF
  · -- ## `n ≥ 3`
    have hin : i < n := lt_trans hij hjn
    have hnotconj : ∀ t : ℕ, ((ν : (GaloisField 2 n)ˣ) : GaloisField 2 n)
        ≠ ((γ : (GaloisField 2 n)ˣ) : GaloisField 2 n) ^ 2 ^ t := by
      intro t hcontra
      have h1 : (ν : GaloisField 2 n) ^ 1
          = (ν : GaloisField 2 n) ^ ((2 ^ i + 2 ^ j) * 2 ^ t) := by
        have hh : (ν : GaloisField 2 n)
            = (ν : GaloisField 2 n) ^ ((2 ^ i + 2 ^ j) * 2 ^ t) := by
          rw [← hγν, ← pow_mul] at hcontra
          exact hcontra
        simpa using hh
      have h2 := (IsOfFinOrder.pow_eq_pow_iff_modEq hνfin).mp h1
      rw [hνF] at h2
      have hm : (2 ^ i + 2 ^ j) * 2 ^ t = 2 ^ (i + t) + 2 ^ (j + t) := by
        rw [add_mul, ← pow_add, ← pow_add]
      rw [hm] at h2
      have h3 : 2 ^ ((i + t) % n) + 2 ^ ((j + t) % n) ≡ 1 [MOD 2 ^ n - 1] := by
        exact (Nat.ModEq.add (pow_two_modEq_mod' (n := n) (m := i + t) (by omega)).symm
          (pow_two_modEq_mod' (n := n) (m := j + t) (by omega)).symm).trans h2.symm
      exact two_pow_sum_mod_ne_one' hn hin hjn hij.ne h3
    obtain ⟨i2, j2, hi2j2, hj2n, hνγ2, c, hcne, hsVmono⟩ :=
      monomial_form (by omega : 0 < n) ν γ hνord hγord hnotconj sV hsV0 hsVne hsVadd1 hsVadd2
        hsVeq
    have hi2n : i2 < n := lt_trans hi2j2 hj2n
    have hexp_eq : i2 = i ∧ j2 = j := by
      have h1 : (ν : GaloisField 2 n) ^ (2 ^ i2 + 2 ^ j2)
          = (ν : GaloisField 2 n) ^ (2 ^ i + 2 ^ j) := by rw [hνγ2, hγν]
      have h2 := (IsOfFinOrder.pow_eq_pow_iff_modEq hνfin).mp h1
      rw [hνF] at h2
      rcases two_pow_sum_modEq hi2n hj2n hin hjn h2 with h | h
      · exact h
      · exact absurd h.1 (by omega)
    obtain ⟨hii, hjj⟩ := hexp_eq
    have hsVmono' : ∀ α, sV α = c * α ^ (2 ^ i + 2 ^ j) := by
      intro α
      rw [hsVmono α, hii, hjj]
    -- ## Step 2: the bracket `β`
    obtain ⟨e, hβexp⟩ := biadditive_frob hFcard βV (fun y x x' => hβV1 x x' y) hβV2
    have hβVcond : ∀ p q : ℕ, p < n → q < n →
        e p q * ((ν : GaloisField 2 n) ^ (2 ^ p) * (γ : GaloisField 2 n) ^ (2 ^ q)
          - (γ : GaloisField 2 n)) = 0 := by
      intro p q hp hq
      refine bivariate_monomial_indep hFcard
        (fun p q => e p q * ((ν : GaloisField 2 n) ^ (2 ^ p) * (γ : GaloisField 2 n) ^ (2 ^ q)
          - (γ : GaloisField 2 n)))
        ?_ p (Finset.mem_range.mpr hp) q (Finset.mem_range.mpr hq)
      intro x y
      have he := hβVeq x y
      rw [hβexp ((ν : GaloisField 2 n) * x) ((γ : GaloisField 2 n) * y), hβexp x y] at he
      have hsplit : (∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n,
            e p q * ((ν : GaloisField 2 n) ^ (2 ^ p) * (γ : GaloisField 2 n) ^ (2 ^ q)
              - (γ : GaloisField 2 n)) * x ^ (2 ^ p) * y ^ (2 ^ q))
          = (∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n,
              e p q * ((ν : GaloisField 2 n) * x) ^ (2 ^ p)
                * ((γ : GaloisField 2 n) * y) ^ (2 ^ q))
            - (γ : GaloisField 2 n) * (∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n,
                e p q * x ^ (2 ^ p) * y ^ (2 ^ q)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [mul_pow, mul_pow]
        ring
      rw [hsplit]
      rw [he, sub_self]
    have hβ0 : ∃ p q, p < n ∧ q < n ∧ e p q ≠ 0 := by
      obtain ⟨x0, y0, hxy⟩ := hβVne
      by_contra hc
      exact hxy (by
        rw [hβexp x0 y0]
        refine Finset.sum_eq_zero (fun p hp => Finset.sum_eq_zero (fun q hq => ?_))
        have h0 : e p q = 0 := by
          by_contra hne
          exact hc ⟨p, q, Finset.mem_range.mp hp, Finset.mem_range.mp hq, hne⟩
        rw [h0]; ring)
    obtain ⟨p0, q0, hp0n, hq0n, he0⟩ := hβ0
    have hcongr : ∀ p q : ℕ, p < n → q < n → e p q ≠ 0 →
        2 ^ p + (2 ^ i + 2 ^ j) * 2 ^ q ≡ 2 ^ i + 2 ^ j [MOD 2 ^ n - 1] := by
      intro p q hp hq hepq
      have h := hβVcond p q hp hq
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 hepq
      · rw [sub_eq_zero] at h1
        have h1' : (ν : GaloisField 2 n) ^ (2 ^ p + (2 ^ i + 2 ^ j) * 2 ^ q)
            = (ν : GaloisField 2 n) ^ (2 ^ i + 2 ^ j) := by
          rw [← hγν] at h1
          rw [← pow_mul, ← pow_add] at h1
          exact h1
        have := (IsOfFinOrder.pow_eq_pow_iff_modEq hνfin).mp h1'
        rwa [hνF] at this
    have huniq : ∀ p q p' q' : ℕ, p < n → q < n → p' < n → q' < n →
        e p q ≠ 0 → e p' q' ≠ 0 → p = p' ∧ q = q' :=
      fun p q p' q' hp hq hp' hq' he he' =>
        pow_two_mod_unique_plus n i j p q p' q' hn hij hjn hp hq hp' hq'
          (hcongr p q hp hq he) (hcongr p' q' hp' hq' he')
    have hezero : ∀ p q : ℕ, p < n → q < n → (p, q) ≠ (p0, q0) → e p q = 0 := by
      intro p q hp hq hne
      by_contra hne0
      have h := huniq p q p0 q0 hp hq hp0n hq0n hne0 he0
      exact hne (Prod.ext h.1 h.2)
    have hrel1 : βV 1 (sV 1) = 0 := hβVrel 1
    rw [hβexp 1 (sV 1)] at hrel1
    have hrel1' : (∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n,
        e p q * (sV 1) ^ (2 ^ q)) = 0 := by
      simpa using hrel1
    have hsingle : (∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n,
        e p q * (sV 1) ^ (2 ^ q)) = e p0 q0 * (sV 1) ^ (2 ^ q0) := by
      rw [Finset.sum_eq_single_of_mem p0 (Finset.mem_range.mpr hp0n)]
      · rw [Finset.sum_eq_single_of_mem q0 (Finset.mem_range.mpr hq0n)]
        intro q hq hqne
        rw [hezero p0 q hp0n (Finset.mem_range.mp hq) (by simp [hqne]), zero_mul]
      · intro p hp hpne
        rw [Finset.sum_eq_zero]
        intro q hq
        rw [hezero p q (Finset.mem_range.mp hp) (Finset.mem_range.mp hq) (by simp [hpne]),
          zero_mul]
    rw [hsingle] at hrel1'
    exact he0 (by
      rcases mul_eq_zero.mp hrel1' with h | h
      · exact h
      · exact absurd h (pow_ne_zero _ (hsVne 1 one_ne_zero)))


end Work.Higman
