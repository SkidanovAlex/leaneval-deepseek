import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.homogeneous_structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-! ## Elementary facts about `Ω₁(P)`

`Ω₁(P) = {x | x ^ 2 = 1}` is an elementary abelian central subgroup of order `q = 2 ^ n`,
`n ≥ 2`, on which `ξ` acts irreducibly.  We record the last point as
`omega1_eq_bot_or_top_of_invariant`, the engine of everything below. -/

/-- A non-identity element of `Ω₁(P)` has order two. -/
theorem orderOf_eq_two_of_mem_omega1 (h : IsSuzuki2Grp P) {x : P} (hx : x ∈ omega1 P)
    (hx1 : x ≠ 1) : orderOf x = 2 := by
  have hd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr ((h.mem_omega1).mp hx)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact absurd (orderOf_eq_one_iff.mp h1) hx1
  · exact h2

/-- `ξ` permutes the involutions of `P`; hence it maps `Ω₁(P)` to itself. -/
theorem map_xi_omega1 (h : IsSuzuki2Grp P) :
    (omega1 P).map (h.xi : MulAut P).toMonoidHom = omega1 P := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    rw [h.mem_omega1, ← map_pow, h.mem_omega1.mp hy, map_one]
  · intro x hx
    refine ⟨(h.xi : MulAut P).symm x, ?_, by simp⟩
    rw [SetLike.mem_coe, h.mem_omega1, ← map_pow, h.mem_omega1.mp hx, map_one]

/-- `Ω₁(P)` is an irreducible `⟨ξ⟩`-module: an `⟨ξ⟩`-invariant subgroup of `Ω₁(P)` is `⊥` or
`Ω₁(P)`.  (Only transitivity of `ξ` on the involutions is used.) -/
theorem omega1_eq_bot_or_top_of_invariant (h : IsSuzuki2Grp P) {S : Subgroup P}
    (hS : S ≤ omega1 P) (hinv : S.map (h.xi : MulAut P).toMonoidHom = S) :
    S = ⊥ ∨ S = omega1 P := by
  rcases eq_or_ne S ⊥ with hbot | hne
  · exact Or.inl hbot
  right
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hxS : (x : P) ∈ S := x.2
  have hx1' : (x : P) ≠ 1 := fun hc => hx1 (Subtype.ext hc)
  have hpres : ∀ k : ℕ, ∀ y : P, y ∈ S → (h.xi ^ k) y ∈ S := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      have hz : (h.xi ^ k) y ∈ S := ih y hy
      have hgoal : (h.xi ^ (k + 1)) y = h.xi.toMonoidHom ((h.xi ^ k) y) := by
        rw [pow_succ', MulAut.mul_apply]; rfl
      rw [hgoal]
      have hmem : h.xi.toMonoidHom ((h.xi ^ k) y) ∈ S.map (h.xi : MulAut P).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hz
      rwa [hinv] at hmem
  apply le_antisymm hS
  intro y hy
  rcases eq_or_ne y 1 with rfl | hy1
  · exact S.one_mem
  · have hx2 : orderOf (x : P) = 2 := orderOf_eq_two_of_mem_omega1 h (hS hxS) hx1'
    have hy2 : orderOf y = 2 := orderOf_eq_two_of_mem_omega1 h hy hy1
    obtain ⟨k, hk⟩ := h.trans (x : P) y hx2 hy2
    rw [← hk]
    exact hpres k (x : P) hxS

/-- `Ω₁(P)` lies in the commutator subgroup `[P,P]` (Higman 1963, §2).  Indeed `[P,P]` is
`ξ`-invariant; if `[P,P] ∩ Ω₁(P)` were trivial then `[P,P]` would have no involution, hence be
trivial, making `P` abelian. -/
theorem omega1_le_commutator (h : IsSuzuki2Grp P) :
    omega1 P ≤ ⁅(⊤ : Subgroup P), ⊤⁆ := by
  have hchar : (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom
      = ⁅(⊤ : Subgroup P), ⊤⁆ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective ((h.xi : MulAut P).toMonoidHom) (h.xi : MulAut P).surjective]
  have hinf : (omega1 P ⊓ ⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P).map
        (h.xi : MulAut P).toMonoidHom = omega1 P ⊓ ⁅(⊤ : Subgroup P), ⊤⁆ := by
    rw [Subgroup.map_inf (omega1 P) (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P)
        ((h.xi : MulAut P).toMonoidHom) (h.xi : MulAut P).injective, map_xi_omega1 h, hchar]
  rcases omega1_eq_bot_or_top_of_invariant h inf_le_left hinf with hbot | htop
  · exfalso
    have hder : (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P) = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).mpr ?_
      intro x hx
      by_contra hx1
      obtain ⟨j, hj⟩ := h.isPGroup.exists_orderOf_eq_pow x
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h0 | hpos
        · rw [h0] at hj
          exact absurd (orderOf_eq_one_iff.mp hj) hx1
        · exact hpos
      have hxpow : x ^ 2 ^ j = 1 := by rw [← hj]; exact pow_orderOf_eq_one x
      have hinv2 : (x ^ 2 ^ (j - 1)) ^ 2 = 1 := by
        rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hj1]
        exact hxpow
      have hne2 : x ^ 2 ^ (j - 1) ≠ 1 := by
        intro hc
        have hdvd : 2 ^ j ∣ 2 ^ (j - 1) := by
          rw [← hj]; exact orderOf_dvd_iff_pow_eq_one.mpr hc
        have hpos : 0 < 2 ^ (j - 1) := pow_pos (by norm_num) _
        have hlt : 2 ^ (j - 1) < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) (by omega)
        exact not_le_of_gt hlt (Nat.le_of_dvd hpos hdvd)
      have hmemN : x ^ 2 ^ (j - 1) ∈ omega1 P := h.mem_omega1.mpr hinv2
      have hmemD : x ^ 2 ^ (j - 1) ∈ ⁅(⊤ : Subgroup P), ⊤⁆ := Subgroup.pow_mem _ hx _
      have hbot' : x ^ 2 ^ (j - 1) ∈ (⊥ : Subgroup P) := by
        rw [← hbot]; exact ⟨hmemN, hmemD⟩
      exact hne2 (Subgroup.mem_bot.mp hbot')
    have hcomm : ∀ a b : P, a * b = b * a := by
      intro a b
      have h1 : ⁅a, b⁆ = 1 := by
        have hmm : ⁅a, b⁆ ∈ (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P) :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [hder] at hmm
        exact Subgroup.mem_bot.mp hmm
      have h2 : a * b * a⁻¹ * b⁻¹ = 1 := h1
      have h3 : a * b * a⁻¹ = b := by
        have := congrArg (fun t : P => t * b) h2
        simpa using this
      have h4 : a * b = b * a := by
        have := congrArg (fun t : P => t * a) h3
        simpa using this
      exact h4
    obtain ⟨x, y, hxy⟩ := h.noncomm
    exact hxy (hcomm x y)
  · exact inf_eq_left.mp htop

/-! ## Commutator algebra in a group of class two

Throughout this section `A` is an abelian subgroup containing the commutator subgroup, so that
all commutators are central and the usual class-two identities hold. -/

section ClassTwo

variable {G : Type*} [Group G]

/-- `x * y * x⁻¹ = [x,y] * y`. -/
theorem mul_mul_inv_eq_commutator_mul (x y : G) : x * y * x⁻¹ = ⁅x, y⁆ * y := by
  rw [commutatorElement_def]; group

/-- In a group of class two every commutator is central, and every element commutes with it. -/
theorem commutator_central_comm
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    z * ⁅x, y⁆ = ⁅x, y⁆ * z :=
  Subgroup.mem_center_iff.mp
    (hZ (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))) z

/-- Class two: `[x,y] ^ 2 = [x ^ 2, y]`. -/
theorem commutator_sq_eq (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y : G) :
    ⁅x, y⁆ ^ 2 = ⁅x ^ 2, y⁆ := by
  have h1 : x * y * x⁻¹ = ⁅x, y⁆ * y := mul_mul_inv_eq_commutator_mul x y
  have hc : x * ⁅x, y⁆ = ⁅x, y⁆ * x := commutator_central_comm hZ x y x
  have key : ⁅x ^ 2, y⁆ = ⁅x, y⁆ ^ 2 := by
    rw [commutatorElement_def, pow_two (a := x)]
    rw [show (x * x) * y * (x * x)⁻¹ * y⁻¹ = x * (x * y * x⁻¹) * x⁻¹ * y⁻¹ by group]
    rw [h1]
    rw [show x * (⁅x, y⁆ * y) * x⁻¹ * y⁻¹
        = (x * ⁅x, y⁆) * (y * x⁻¹) * y⁻¹ by group]
    rw [hc]
    rw [show (⁅x, y⁆ * x) * (y * x⁻¹) * y⁻¹
        = ⁅x, y⁆ * (x * y * x⁻¹) * y⁻¹ by group]
    rw [h1]
    rw [show ⁅x, y⁆ * (⁅x, y⁆ * y) * y⁻¹ = ⁅x, y⁆ * ⁅x, y⁆ by group]
    rw [pow_two]
  exact key.symm

/-- Class two: `[x * y, z] = [x,z] * [y,z]`. -/
theorem commutator_mul_left (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hcy : ∀ w : G, w * ⁅y, z⁆ = ⁅y, z⁆ * w := commutator_central_comm hZ y z
  have hcx : ∀ w : G, w * ⁅x, z⁆ = ⁅x, z⁆ * w := commutator_central_comm hZ x z
  have h1 : x * z * x⁻¹ = ⁅x, z⁆ * z := mul_mul_inv_eq_commutator_mul x z
  have h2 : y * z * y⁻¹ = ⁅y, z⁆ * z := mul_mul_inv_eq_commutator_mul y z
  rw [commutatorElement_def]
  rw [show x * y * z * (x * y)⁻¹ * z⁻¹ = x * (y * z * y⁻¹) * x⁻¹ * z⁻¹ by group]
  rw [h2]
  rw [show x * (⁅y, z⁆ * z) * x⁻¹ * z⁻¹ = (x * ⁅y, z⁆) * (z * x⁻¹) * z⁻¹ by group]
  rw [hcy x]
  rw [show (⁅y, z⁆ * x) * (z * x⁻¹) * z⁻¹ = ⁅y, z⁆ * (x * z * x⁻¹) * z⁻¹ by group]
  rw [h1]
  rw [show ⁅y, z⁆ * (⁅x, z⁆ * z) * z⁻¹ = ⁅y, z⁆ * ⁅x, z⁆ by group]
  rw [hcx ⁅y, z⁆]

/-- Class two: `[x,y] ^ n = [x ^ n, y]`. -/
theorem commutator_pow_eq (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y : G) (n : ℕ) :
    ⁅x, y⁆ ^ n = ⁅x ^ n, y⁆ := by
  induction n with
  | zero => rw [pow_zero, pow_zero, commutatorElement_def]; group
  | succ n ih =>
      rw [pow_succ, ih, ← commutator_mul_left hZ, ← pow_succ]

end ClassTwo
/-! ## The assembly

Given Higman's Lemma 1 (`homogeneous_structure`), the existence of a maximal `ξ`-invariant
abelian normal subgroup `A` containing `Φ(P)` and of exponent `≤ 4`
(`maximal_abelian_invariant_ge_phi`), and the exclusion of the `C₄`-shape of the derived
subgroup (`no_square_derived`), the derived subgroup lies in `Ω₁(P)`: `P' = A ^ (2 ^ s)` for
some `s`, and since `e = log₂ (exp A) ≤ 2` we have `s ≤ e - 1 ≤ 1`. -/
theorem core {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P)
    {A : Subgroup P} (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : omega1 P ≤ A) (hDA : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A) (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : powSub A 4 = ⊥)
    {e : ℕ} (hexp : ∀ x ∈ A, x ^ 2 ^ e = 1)
    (hcard : ∀ i ≤ e, Nat.card ↥(powSub A (2 ^ i))
      = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - i))
    (htop : powSub A (2 ^ (e - 1)) = A ⊓ omega1 P)
    (hsub : ∀ B : Subgroup P, B ≤ A → B.map (h.xi : MulAut P).toMonoidHom = B →
      ∃ i : ℕ, B = powSub A (2 ^ i))
    (hnosq : ⁅(⊤ : Subgroup P), ⊤⁆ = A → powSub A 2 = omega1 P →
      Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2 → False) :
    ⁅(⊤ : Subgroup P), ⊤⁆ ≤ omega1 P := by
  have hNinf : A ⊓ omega1 P = omega1 P := inf_eq_right.mpr hNA
  have htop' : powSub A (2 ^ (e - 1)) = omega1 P := by rw [htop, hNinf]
  -- `e ≥ 1`
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · exfalso
      have hA : A = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        have := hexp x hx
        rw [h0] at this
        simpa using this
      have hN : omega1 P ≤ (⊥ : Subgroup P) := by rw [← hA]; exact hNA
      have hcard_ge := h.omega1_card_ge_four
      have : Nat.card ↥(omega1 P) = 1 := by
        rw [le_bot_iff] at hN
        rw [hN]
        simp
      omega
    · exact hpos
  -- `e ≤ 2`
  have he2 : e ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have h2e : 2 ≤ e := by omega
    have hc := hcard 2 h2e
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hA4] at hc
    have h1 : (Nat.card ↥(A ⊓ omega1 P)) ^ (e - 2) = 1 := by
      rw [← hc]; simp
    have hbase : 2 ≤ Nat.card ↥(A ⊓ omega1 P) := by
      have := h.omega1_card_ge_four
      rw [hNinf]; omega
    have hk : e - 2 = 0 := by
      by_contra hne
      have hlt : 1 ≤ e - 2 := by omega
      have : (Nat.card ↥(A ⊓ omega1 P)) ^ 1 ≤ (Nat.card ↥(A ⊓ omega1 P)) ^ (e - 2) :=
        Nat.pow_le_pow_right (by omega) hlt
      rw [pow_one, h1] at this
      omega
    omega
  -- the derived subgroup is `ξ`-invariant
  have hDxi : (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom
      = ⁅(⊤ : Subgroup P), ⊤⁆ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective ((h.xi : MulAut P).toMonoidHom)
        (h.xi : MulAut P).surjective]
  obtain ⟨s, hs⟩ := hsub ⁅(⊤ : Subgroup P), ⊤⁆ hDA hDxi
  -- `P' ≠ ⊥`
  have hDne : (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P) ≠ ⊥ := by
    intro hbot
    obtain ⟨x, y, hxy⟩ := h.noncomm
    have h1 : ⁅x, y⁆ = 1 := by
      have hmem : ⁅x, y⁆ ∈ (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have h2 : x * y * x⁻¹ * y⁻¹ = 1 := h1
    have h3 : x * y * x⁻¹ = y := by
      have := congrArg (fun t : P => t * y) h2
      simpa using this
    have h4 : x * y = y * x := by
      have := congrArg (fun t : P => t * x) h3
      simpa using this
    exact hxy h4
  -- `s ≤ e - 1`
  have hse : s ≤ e - 1 := by
    by_contra hcon
    push Not at hcon
    have hle : e ≤ s := by omega
    have hpow : powSub A (2 ^ s) ≤ powSub A (2 ^ e) :=
      powSub_le_of_dvd hAab (Nat.pow_dvd_pow 2 hle)
    have hbot : powSub A (2 ^ e) = ⊥ := powSub_eq_bot_of_exp hAab (le_refl e) hexp
    rw [← hs] at hpow
    exact hDne (le_bot_iff.mp (hbot ▸ hpow))
  -- final case analysis on `e`
  have hecases : e = 1 ∨ e = 2 := by omega
  rcases hecases with he | he
  · -- `e = 1`: `P' = A ^ (2 ^ 0) = Ω₁(P)`
    have hs0 : s = 0 := by omega
    have hAeq : A = omega1 P := by
      rw [he] at htop'
      rwa [show (2 : ℕ) ^ (1 - 1) = 1 by norm_num, powSub_one_eq] at htop'
    rw [hs, hs0, show (2 : ℕ) ^ 0 = 1 by norm_num, powSub_one_eq, hAeq]
  · -- `e = 2`
    have htop2 : powSub A 2 = omega1 P := by
      rw [he] at htop'
      simpa using htop'
    have hs1 : s ≤ 1 := by omega
    rcases Nat.eq_zero_or_pos s with hs0 | hspos
    · -- `P' = A`: excluded by `no_square_derived`
      exfalso
      have hGsA : ⁅(⊤ : Subgroup P), ⊤⁆ = A := by
        rw [hs, hs0, show (2 : ℕ) ^ 0 = 1 by norm_num, powSub_one_eq]
      have hcardA : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2 := by
        have hc0 := hcard 0 (Nat.zero_le e)
        rw [show (2 : ℕ) ^ 0 = 1 by norm_num, powSub_one_eq] at hc0
        rw [he, hNinf] at hc0
        simpa using hc0
      exact hnosq hGsA htop2 hcardA
    · -- `s = 1`: `P' = A ^ 2 = Ω₁(P)`
      have hs1' : s = 1 := by omega
      rw [hs, hs1']
      rw [show (2 : ℕ) ^ 1 = 2 by norm_num, htop2]

end Work.Higman
