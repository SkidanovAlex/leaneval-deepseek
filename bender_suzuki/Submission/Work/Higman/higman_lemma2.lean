/-
Copyright (c) 2024. All rights reserved.

# Higman (1963), Lemma 2

Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), 79--96, p. 83:

> **LEMMA 2.** If `A` is an abelian normal `X`-subgroup of `G`, which is not `1`, then
> for no element `u` of `G` not in `A` is both `u² ∈ A²` and `[u, A] ⊆ A⁴`.

The proof below follows Higman's strategy, replacing the appeal to "`1 + 2α` is invertible" by a
descent along the power subgroups `A^{2^i}`.  Let `2 ^ e` be the exponent of `A` and write
`Z_i = A^{2^i}`.  The only structural input is Higman's dichotomy
(`mem_powSub_of_sq_eq_one`): *every* involution of `A` is a `2 ^ (e-1)`-st power in `A`, whence
`A[2] = Z_{e-1} ⊆ Z_i` for `i ≤ e - 1`.

Set `δ(a) = ⁅u⁻¹, a⁆ ∈ A⁴` and `F(a) = a · (u⁻¹ a u) = a² · δ(a)`.  Then

* `F` is a homomorphism `A → A` with `F(A) ⊆ A²`;
* `A[2] ⊆ ker F` (involutions of `A` are central);
* `ker F ⊆ A[2]`: if `F(a) = 1` then `δ(a) = a^{-2}`; from `a ∈ Z_k` we get
  `δ(a) ∈ δ(Z_k) ⊆ Z_{k+2}`, hence `a² ∈ Z_{k+2}`; if `k + 2 ≥ e` then `a² = 1`, otherwise the
  layer property `a² ∈ Z_{k+2} ⟹ a ∈ Z_{k+1}` (which uses `A[2] = Z_{e-1} ⊆ Z_{k+1}`) pushes `a`
  one level up.  Iterating from `a ∈ Z_0 = A` gives `a ∈ Z_e = 1`, so `a² = 1`.

Hence `|ker F| = |A[2]|`, so `|F(A)| = |A|/|A[2]| = |A²|` (the squaring map has kernel `A[2]` and
image `A²`), and as `F(A) ⊆ A²` we get `F(A) = A²`.  Since `u² ∈ A²`, there is `a ∈ A` with
`F(a) = u²`, and then `(a u⁻¹)² = F(a) u^{-2} = 1`.  So `a u⁻¹` is an involution of `P`, i.e.
lies in `Ω₁(P) ≤ A`, and therefore `u = (a u⁻¹)⁻¹ a ∈ A`, contradiction.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- **Higman (1963), Lemma 2.**  No `u ∉ A` has both `u² ∈ A²` and `[u,A] ⊆ A⁴`. -/
theorem higman_lemma2 (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A) (hOm : omega1 P ≤ A) (h1 : A ≠ ⊥) {u : P} (hu : u ∉ A) :
    ¬ (u ^ 2 ∈ powSub A 2 ∧ ∀ a ∈ A, ⁅u, a⁆ ∈ powSub A 4) := by
  rintro ⟨hu2, hcomm⟩
  classical
  have hAn : A.Normal := hA.normal
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  -- the exponent data of `A`
  obtain ⟨e, he1, he2, hkey3⟩ := mem_powSub_two_iff h hA
  have hdich : ∀ z ∈ A, z ^ 2 = 1 → z ∈ powSub A (2 ^ (e - 1)) :=
    fun z hzA hz2 => mem_powSub_of_sq_eq_one h hA he1 he2 hzA hz2
  -- dividing powers: `n ∣ m` gives `A^{2^m} ≤ A^{2^n}`
  have hpowmono : ∀ n m : ℕ, n ∣ m → powSub A m ≤ powSub A n := by
    intro n m hnm y hy
    obtain ⟨x, hxA, hx⟩ := (mem_powSub_iff hAb).mp hy
    obtain ⟨t, ht⟩ := hnm
    have hyx : y = (x ^ t) ^ n := by rw [← hx, ht, mul_comm n t, pow_mul]
    rw [hyx]
    exact pow_mem_powSub (Subgroup.pow_mem A hxA t)
  -- `Z_j = 1` for `j ≥ e`
  have hZbot : ∀ j : ℕ, e ≤ j → powSub A (2 ^ j) = ⊥ := by
    intro j hj
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨y, hyA, hy⟩ := (mem_powSub_iff hAb).mp hx
    have hsplit : 2 ^ j = 2 ^ e * 2 ^ (j - e) := by
      rw [← pow_add, Nat.add_sub_cancel' hj]
    rw [← hy, hsplit, pow_mul, he1 y hyA, one_pow]
  -- the layer property
  have hlayer : ∀ i : ℕ, 1 ≤ i → i ≤ e - 1 → ∀ x ∈ A,
      x ^ 2 ∈ powSub A (2 ^ (i + 1)) → x ∈ powSub A (2 ^ i) := by
    intro i hi1 hi2 x hxA hx
    obtain ⟨y, hyA, hy⟩ := (mem_powSub_iff hAb).mp hx
    have hyi : y ^ 2 ^ i ∈ A := Subgroup.pow_mem A hyA (2 ^ i)
    have hsq : (y ^ 2 ^ i) ^ 2 = y ^ 2 ^ (i + 1) := by
      rw [← pow_mul, show 2 ^ i * 2 = 2 ^ (i + 1) from by rw [← pow_succ]]
    have hzsq : (x * (y ^ 2 ^ i)⁻¹) ^ 2 = 1 := by
      have hc0 : Commute x (y ^ 2 ^ i) := hAb x hxA _ hyi
      have hc : Commute x ((y ^ 2 ^ i))⁻¹ := hc0.inv_right
      calc (x * (y ^ 2 ^ i)⁻¹) ^ 2 = x ^ 2 * ((y ^ 2 ^ i)⁻¹) ^ 2 := hc.mul_pow 2
        _ = x ^ 2 * ((y ^ 2 ^ i) ^ 2)⁻¹ := by rw [inv_pow]
        _ = x ^ 2 * (y ^ 2 ^ (i + 1))⁻¹ := by rw [hsq]
        _ = x ^ 2 * (x ^ 2)⁻¹ := by rw [hy]
        _ = 1 := mul_inv_cancel _
    have hzA : x * (y ^ 2 ^ i)⁻¹ ∈ A := A.mul_mem hxA (A.inv_mem hyi)
    have hz1 : x * (y ^ 2 ^ i)⁻¹ ∈ powSub A (2 ^ (e - 1)) := hdich _ hzA hzsq
    have hmono : powSub A (2 ^ (e - 1)) ≤ powSub A (2 ^ i) := by
      apply hpowmono
      exact ⟨2 ^ (e - 1 - i), by rw [← pow_add]; congr 1; omega⟩
    have hz2 : x * (y ^ 2 ^ i)⁻¹ ∈ powSub A (2 ^ i) := hmono hz1
    have hxe : x = (x * (y ^ 2 ^ i)⁻¹) * (y ^ 2 ^ i) := by group
    rw [hxe]
    exact Subgroup.mul_mem (powSub A (2 ^ i)) hz2 (pow_mem_powSub (n := 2 ^ i) hyA)
  -- `δ y = ⁅u⁻¹, y⁆ ∈ A⁴` for `y ∈ A`
  have hdelta4 : ∀ y ∈ A, ⁅u⁻¹, y⁆ ∈ powSub A 4 := by
    intro y hy
    have hxy : ⁅u⁻¹, y⁆ = u⁻¹ * (⁅u, y⁆)⁻¹ * u := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [hxy]
    obtain ⟨c, hcA, hc⟩ := (mem_powSub_iff hAb).mp (hcomm y hy)
    have hconj : u⁻¹ * c⁻¹ * u ∈ A := by
      simpa using hAn.conj_mem c⁻¹ (A.inv_mem hcA) u⁻¹
    have hpow : u⁻¹ * (c ^ 4)⁻¹ * u = (u⁻¹ * c⁻¹ * u) ^ 4 := by
      have hh : (MulAut.conj u⁻¹) (c⁻¹ ^ 4) = ((MulAut.conj u⁻¹) c⁻¹) ^ 4 :=
        map_pow (MulAut.conj u⁻¹).toMonoidHom c⁻¹ 4
      simpa [MulAut.conj_apply] using hh
    rw [← hc, hpow]
    exact pow_mem_powSub hconj
  -- multiplicativity and power rule for `δ`
  have hdmul : ∀ a ∈ A, ∀ b ∈ A, ⁅u⁻¹, a * b⁆ = ⁅u⁻¹, a⁆ * ⁅u⁻¹, b⁆ := by
    intro a ha b hb
    have hb2 : ⁅u⁻¹, b⁆ ∈ A := powSub_le (by norm_num : 0 < 4) (hdelta4 b hb)
    calc ⁅u⁻¹, a * b⁆ = ⁅u⁻¹, a⁆ * (a * ⁅u⁻¹, b⁆ * a⁻¹) := by
          rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
      _ = ⁅u⁻¹, a⁆ * ⁅u⁻¹, b⁆ := by rw [hAb a ha _ hb2]; group
  have hdpow : ∀ (y : P) (hy : y ∈ A) (n : ℕ), ⁅u⁻¹, y ^ n⁆ = ⁅u⁻¹, y⁆ ^ n := by
    intro y hy n
    induction n with
    | zero => rw [pow_zero, pow_zero, commutatorElement_def]; group
    | succ n ih =>
        rw [pow_succ, hdmul (y ^ n) (Subgroup.pow_mem A hy n) y hy, ih, pow_succ]
  -- `F : a ↦ a * (u⁻¹ a u)`
  have hFmem : ∀ a : ↥A, (a : P) * (u⁻¹ * (a : P) * u) ∈ A := by
    intro a
    exact A.mul_mem a.2 (by simpa using hAn.conj_mem (a : P) a.2 u⁻¹)
  let F : ↥A →* ↥A :=
    { toFun := fun a => ⟨(a : P) * (u⁻¹ * (a : P) * u), hFmem a⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := by
        intro a b
        apply Subtype.ext
        show ((a : P) * (b : P)) * (u⁻¹ * ((a : P) * (b : P)) * u) =
          ((a : P) * (u⁻¹ * (a : P) * u)) * ((b : P) * (u⁻¹ * (b : P) * u))
        have hca : u⁻¹ * (a : P) * u ∈ A := by simpa using hAn.conj_mem (a : P) a.2 u⁻¹
        have hcb : u⁻¹ * (b : P) * u ∈ A := by simpa using hAn.conj_mem (b : P) b.2 u⁻¹
        have hcb' : (b : P) * (u⁻¹ * (a : P) * u) = (u⁻¹ * (a : P) * u) * (b : P) :=
          hAb _ b.2 _ hca
        have hsplit : u⁻¹ * ((a : P) * (b : P)) * u =
            (u⁻¹ * (a : P) * u) * (u⁻¹ * (b : P) * u) := by group
        rw [hsplit]
        calc ((a : P) * (b : P)) * ((u⁻¹ * (a : P) * u) * (u⁻¹ * (b : P) * u))
            = (a : P) * ((b : P) * (u⁻¹ * (a : P) * u)) * (u⁻¹ * (b : P) * u) := by group
          _ = (a : P) * ((u⁻¹ * (a : P) * u) * (b : P)) * (u⁻¹ * (b : P) * u) := by rw [hcb']
          _ = ((a : P) * (u⁻¹ * (a : P) * u)) * ((b : P) * (u⁻¹ * (b : P) * u)) := by group
      }
  have hF_apply : ∀ a : ↥A, (F a : P) = (a : P) * (u⁻¹ * (a : P) * u) := fun a => rfl
  -- Step: `F a = 1` and `a ∈ Z_k` pushes `a` up one level (or gives `a² = 1`)
  have hstep : ∀ k : ℕ, ∀ a : ↥A, (a : P) ∈ powSub A (2 ^ k) → F a = 1 →
      (a : P) ^ 2 = 1 ∨ (a : P) ∈ powSub A (2 ^ (k + 1)) := by
    intro k a hak hFa
    have hconj : u⁻¹ * (a : P) * u = (a : P)⁻¹ := by
      have hthis : (a : P) * (u⁻¹ * (a : P) * u) = 1 := by
        have := congrArg (fun t : ↥A => (t : P)) hFa
        rw [hF_apply, Subgroup.coe_one] at this
        exact this
      calc u⁻¹ * (a : P) * u = (a : P)⁻¹ * ((a : P) * (u⁻¹ * (a : P) * u)) := by group
        _ = (a : P)⁻¹ * 1 := by rw [hthis]
        _ = (a : P)⁻¹ := mul_one _
    have hdelta : ⁅u⁻¹, (a : P)⁆ = ((a : P) ^ 2)⁻¹ := by
      rw [commutatorElement_def u⁻¹ (a : P), inv_inv, hconj, pow_two, mul_inv_rev]
    have hdeltaZ : ⁅u⁻¹, (a : P)⁆ ∈ powSub A (2 ^ (k + 2)) := by
      obtain ⟨y, hyA, hy⟩ := (mem_powSub_iff hAb).mp hak
      rw [← hy, hdpow y hyA (2 ^ k)]
      obtain ⟨c, hcA, hc⟩ := (mem_powSub_iff hAb).mp (hdelta4 y hyA)
      have hone : (c ^ 4) ^ (2 ^ k) = c ^ (2 ^ (k + 2)) := by
        rw [← pow_mul]
        congr 1
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        ring_nf
      rw [← hc, hone]
      exact pow_mem_powSub hcA
    by_cases hke : e ≤ k + 2
    · left
      have h2 : ((a : P) ^ 2)⁻¹ ∈ powSub A (2 ^ (k + 2)) := hdelta ▸ hdeltaZ
      have h3 : ((a : P) ^ 2)⁻¹ ∈ (⊥ : Subgroup P) := by
        rw [← hZbot _ hke]; exact h2
      simp only [Subgroup.mem_bot] at h3
      exact inv_eq_one.mp h3
    · right
      push_neg at hke
      have hsquare : (a : P) ^ 2 ∈ powSub A (2 ^ (k + 2)) := by
        have hsi : ((a : P) ^ 2)⁻¹ ∈ powSub A (2 ^ (k + 2)) := hdelta ▸ hdeltaZ
        simpa using inv_mem hsi
      have := hlayer (k + 1) (by omega) (by omega) (a : P) a.2
      rw [show k + 1 + 1 = k + 2 by ring] at this
      exact this hsquare
  -- Iterate: `F a = 1 ⟹ a² = 1`
  have hker : ∀ a : ↥A, F a = 1 → (a : P) ^ 2 = 1 := by
    intro a hFa
    have hone : (a : P) ∈ powSub A (2 ^ 0) := by
      rw [pow_zero]
      exact Subgroup.subset_closure ⟨(a : P), a.2, pow_one _⟩
    have iter : ∀ j : ℕ, j ≤ e → ((a : P) ^ 2 = 1 ∨ (a : P) ∈ powSub A (2 ^ j)) := by
      intro j hj
      induction j with
      | zero => exact Or.inr hone
      | succ j ih =>
          rcases ih (by omega) with h | h
          · exact Or.inl h
          · exact hstep j a h hFa
    rcases iter e le_rfl with h | h
    · exact h
    · rw [hZbot e le_rfl] at h
      simp only [Subgroup.mem_bot] at h
      rw [h, one_pow]
  -- `A[2] ⊆ ker F`
  have hker2 : ∀ a : ↥A, (a : P) ^ 2 = 1 → F a = 1 := by
    intro a ha
    apply Subtype.ext
    rw [hF_apply, Subgroup.coe_one]
    have hz : (a : P) ∈ Subgroup.center P := h.omega1_le_center (h.mem_omega1.mpr ha)
    have hcentral : u⁻¹ * (a : P) * u = (a : P) := by
      rw [Subgroup.mem_center_iff.mp hz u⁻¹]
      group
    rw [hcentral]
    simpa [pow_two] using ha
  -- cardinalities
  have hcard_ker : Nat.card ↥(F.ker) = Nat.card {x : ↥A | (x : P) ^ 2 = 1} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl ↥A) (fun x => ?_))
    show x ∈ F.ker ↔ (x : P) ^ 2 = 1
    exact ⟨fun hx => hker x hx, fun hx => hker2 x hx⟩
  have hcard_F : Nat.card ↥(F.ker) * Nat.card ↥(F.range) = Nat.card ↥A :=
    card_ker_mul_card_range' F
  -- the squaring map on `A`
  letI : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun x y => Subtype.ext (hAb x x.2 y y.2) }
  set sq : ↥A →* ↥A := powMonoidHom (α := ↥A) 2 with hsq
  have hcard_sq : Nat.card ↥(sq.ker) * Nat.card ↥(sq.range) = Nat.card ↥A :=
    card_ker_mul_card_range' sq
  have hsq_ker : Nat.card ↥(sq.ker) = Nat.card {x : ↥A | (x : P) ^ 2 = 1} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl ↥A) (fun x => ?_))
    show x ∈ sq.ker ↔ (x : P) ^ 2 = 1
    rw [MonoidHom.mem_ker, hsq]
    constructor
    · intro hx
      have hh := congrArg (fun t : ↥A => (t : P)) hx
      simpa [powMonoidHom_apply] using hh
    · intro hx
      apply Subtype.ext
      simpa [powMonoidHom_apply] using hx
  have hsq_range : Nat.card ↥(sq.range) = Nat.card ↥(powSub A 2) := by
    have hset : (sq.range : Set ↥A) = {x : ↥A | (x : P) ∈ powSub A 2} := by
      ext x
      show x ∈ sq.range ↔ (x : P) ∈ powSub A 2
      rw [MonoidHom.mem_range]
      constructor
      · rintro ⟨y, hy⟩
        rw [← hy, hsq, powMonoidHom_apply]
        exact pow_mem_powSub y.2
      · intro hx
        obtain ⟨y, hyA, hy⟩ := (mem_powSub_iff hAb).mp hx
        exact ⟨⟨y, hyA⟩, Subtype.ext hy⟩
    have hS : Nat.card {x : ↥A | (x : P) ∈ powSub A 2} = Nat.card ↥(powSub A 2) := by
      refine Nat.card_eq_of_bijective
        (fun y : {x : ↥A | (x : P) ∈ powSub A 2} => (⟨(y.1 : P), y.2⟩ : ↥(powSub A 2))) ?_
      constructor
      · intro y₁ y₂ hy
        exact Subtype.ext (Subtype.ext (congrArg (fun t : ↥(powSub A 2) => (t : P)) hy))
      · intro w
        exact ⟨⟨⟨(w : P), powSub_le (by norm_num : 0 < 2) w.2⟩, w.2⟩, Subtype.ext rfl⟩
    have h2 : Nat.card ↥(sq.range) = Nat.card {x : ↥A | (x : P) ∈ powSub A 2} :=
      Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl ↥A) (fun x => by
        have hh := Set.ext_iff.mp hset x
        simpa using hh))
    rw [h2, hS]
  -- `F.range ⊆ A²`
  have hFrange_le : (F.range : Set ↥A) ⊆ {x : ↥A | (x : P) ∈ powSub A 2} := by
    rintro x ⟨a, rfl⟩
    have h4 : ⁅u⁻¹, (a : P)⁆ ∈ powSub A 4 := hdelta4 _ a.2
    have hδA : u⁻¹ * (a : P) * u * (a : P)⁻¹ ∈ A := by
      have hh := powSub_le (by norm_num : 0 < 4) h4
      rwa [commutatorElement_def, inv_inv] at hh
    have h2 : (a : P) ^ 2 ∈ powSub A 2 := pow_mem_powSub a.2
    have hprod : (a : P) ^ 2 * ⁅u⁻¹, (a : P)⁆ ∈ powSub A 2 :=
      Subgroup.mul_mem (powSub A 2) h2 (hpowmono 2 4 ⟨2, by norm_num⟩ h4)
    have hconv : (a : P) * (u⁻¹ * (a : P) * u) = (a : P) ^ 2 * ⁅u⁻¹, (a : P)⁆ := by
      have hX : u⁻¹ * (a : P) * u ∈ A := by
        simpa using hAn.conj_mem (a : P) a.2 u⁻¹
      have hcommX : (a : P) * (u⁻¹ * (a : P) * u) = (u⁻¹ * (a : P) * u) * (a : P) :=
        hAb _ a.2 _ hX
      rw [commutatorElement_def, inv_inv]
      calc (a : P) * (u⁻¹ * (a : P) * u)
          = (a : P) * ((u⁻¹ * (a : P) * u) * (a : P)) * (a : P)⁻¹ := by group
        _ = (a : P) * ((a : P) * (u⁻¹ * (a : P) * u)) * (a : P)⁻¹ := by rw [hcommX]
        _ = (a : P) ^ 2 * (u⁻¹ * (a : P) * u * (a : P)⁻¹) := by rw [pow_two]; group
    show (F a : P) ∈ powSub A 2
    rw [hF_apply, hconv]
    exact hprod
  have hinj_range : Function.Injective (fun y : ↥(F.range) =>
      (⟨(y.1 : P), by
        obtain ⟨a, ha⟩ := y.2
        rw [← ha]
        exact hFrange_le ⟨a, rfl⟩⟩ : ↥(powSub A 2))) := by
    intro y₁ y₂ hy
    exact Subtype.ext (Subtype.ext (congrArg (fun t : ↥(powSub A 2) => (t : P)) hy))
  -- `u² ∈ A² = F(A)`
  have huA : u ^ 2 ∈ A := powSub_le (by norm_num : 0 < 2) hu2
  have hmem : (⟨u ^ 2, huA⟩ : ↥A) ∈ F.range := by
    have hcard_range : Nat.card ↥(F.range) = Nat.card ↥(powSub A 2) := by
      have hS : Nat.card {x : ↥A | (x : P) ^ 2 = 1} * Nat.card ↥(powSub A 2) = Nat.card ↥A := by
        rw [← hsq_ker, ← hsq_range]; exact hcard_sq
      have hF : Nat.card {x : ↥A | (x : P) ^ 2 = 1} * Nat.card ↥(F.range) = Nat.card ↥A := by
        rw [← hcard_ker]; exact hcard_F
      have hpos : 0 < Nat.card {x : ↥A | (x : P) ^ 2 = 1} :=
        Nat.card_pos_iff.mpr ⟨⟨(1 : ↥A), by simp⟩, inferInstance⟩
      exact Nat.mul_left_cancel hpos (by rw [hF, hS])
    haveI : Fintype ↥(F.range) := Fintype.ofFinite _
    haveI : Fintype ↥(powSub A 2) := Fintype.ofFinite _
    have hcard : Fintype.card ↥(F.range) = Fintype.card ↥(powSub A 2) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard_range]
    have hbij := (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj_range, hcard⟩
    obtain ⟨y, hy⟩ := hbij.2 ⟨u ^ 2, hu2⟩
    have hy1 : (y.1 : P) = u ^ 2 := congrArg (fun t : ↥(powSub A 2) => (t : P)) hy
    obtain ⟨z, hz⟩ := y.2
    exact ⟨z, Subtype.ext (by rw [hz]; exact hy1)⟩
  obtain ⟨a, ha⟩ := hmem
  -- `(a u⁻¹)² = 1`
  have hkey : ∃ a ∈ A, (a * u⁻¹) ^ 2 = 1 := by
    refine ⟨(a : P), a.2, ?_⟩
    have hFa : (F a : P) = u ^ 2 := congrArg (fun t : ↥A => (t : P)) ha
    calc ((a : P) * u⁻¹) ^ 2 = (a : P) * (u⁻¹ * (a : P) * u) * u⁻¹ * u⁻¹ := by
          rw [pow_two]; group
      _ = (F a : P) * u⁻¹ * u⁻¹ := by rw [hF_apply]
      _ = u ^ 2 * u⁻¹ * u⁻¹ := by rw [hFa]
      _ = 1 := by rw [pow_two]; group
  obtain ⟨a, haA, ha⟩ := hkey
  have hord : orderOf (a * u⁻¹) = 2 := by
    have hd : orderOf (a * u⁻¹) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr ha
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1' | h2'
    · exfalso
      exact hu (by
        have hx : a * u⁻¹ = 1 := orderOf_eq_one_iff.mp h1'
        have hux : u = a := by
          calc u = (u⁻¹)⁻¹ := (inv_inv u).symm
            _ = (a⁻¹ * (a * u⁻¹))⁻¹ := by rw [inv_mul_cancel_left]
            _ = (a⁻¹ * 1)⁻¹ := by rw [hx]
            _ = a := by simp
        rw [hux]; exact haA)
    · exact h2'
  have hmem2 : a * u⁻¹ ∈ omega1 P := h.mem_omega1.mpr (by rw [← hord]; exact pow_orderOf_eq_one _)
  have hmemA : a * u⁻¹ ∈ A := hOm hmem2
  have huA' : u ∈ A := by
    have : u = (a * u⁻¹)⁻¹ * a := by group
    rw [this]; exact A.mul_mem (A.inv_mem hmemA) haA
  exact hu huA'

end Work.Higman
