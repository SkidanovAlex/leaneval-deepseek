/-
# `q2XiV` / `q2XiW`: basic dynamical facts

This file collects, for the *`q2`-convention* automorphisms `q2XiV` (on `V = P/Z(P)`) and
`q2XiW` (on `W = Z(P)`) of `Submission.Work.Higman.twoStep_q2_normal_form`, the facts needed by
`Work.Higman.Q3.L12.exists_xi_decomposition`:

* `q2Sig`, `q2Tau` (the `𝔽₂`-linear versions of `q2XiW`, `q2XiV`) have the same orbits as the
  iterates of `q2XiW`, `q2XiV`;
* `ξ` acts transitively, hence freely, on `W ∖ {0}`, and `orderOf (q2XiW) = |W| - 1`;
* `ξ` acts freely on `V ∖ {0}` (via the `ξ`-equivariance of the anisotropic squaring form);
* consequently the permutation `q2XiVPerm` of `V` has order `|W| - 1` and any power of it fixing
  a non-zero vector is the identity.

Nothing here uses `Submission.Work.Higman.Q3.induced`.
-/

import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.cocycle_setup
import Submission.Work.Higman.twoStep_q2_normal_form
import Submission.Work.Higman.Q3.orderOf_dvd_ncard_of_semiregular

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedSectionVars false

noncomputable section

namespace Work.Higman.Q3.L12

open Work.Higman

variable {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
variable [Finite V] [Finite W] {b : V → V → W} [Biadd b]

/-! ## Involutions of the two-step group -/

/-- `⟨0, v⟩` has order two for `v ≠ 0` (no hypothesis on involutions is needed). -/
theorem orderOf_zero_snd {v : W} (hv : v ≠ 0) :
    orderOf (⟨0, v⟩ : TwoStep V W b) = 2 := by
  have hsq : (⟨0, v⟩ : TwoStep V W b) ^ 2 = 1 := by
    rw [TwoStep.sq_eq, Biadd.zero_left (b := b) (0 : V)]
    rfl
  have hne : (⟨0, v⟩ : TwoStep V W b) ≠ 1 := by
    intro hcon
    exact hv (by simpa using congrArg (fun t : TwoStep V W b => t.snd) hcon)
  have hdvd : orderOf (⟨0, v⟩ : TwoStep V W b) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

section Main

variable (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
variable (ξ : MulAut (TwoStep V W b))

/-! ## The `𝔽₂`-linear versions and the iterates of `q2XiV`, `q2XiW` -/

section Linear

variable [Module (ZMod 2) V] [Module (ZMod 2) W]

include hcenter ξ

/-- The iterates of `q2Sig` are those of `q2XiW`. -/
theorem q2Sig_pow_apply (k : ℕ) (w : W) :
    (q2Sig hcenter ξ ^ k) w = ((q2XiW hcenter ξ : W → W)^[k]) w := by
  induction k with
  | zero => rw [pow_zero, Function.iterate_zero_apply]; rfl
  | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, Function.iterate_succ_apply', q2Sig_apply]

/-- The iterates of `q2Tau` are those of `q2XiV`. -/
theorem q2Tau_pow_apply (k : ℕ) (v : V) :
    (q2Tau hcenter ξ ^ k) v = ((q2XiV hcenter ξ : V → V)^[k]) v := by
  induction k with
  | zero => rw [pow_zero, Function.iterate_zero_apply]; rfl
  | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, Function.iterate_succ_apply', q2Tau_apply]

/-- `ξ` is transitive on `W ∖ {0}`, through `q2Sig`. -/
theorem q2Sig_trans
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y) :
    ∀ a d : W, a ≠ 0 → d ≠ 0 → ∃ k : ℕ, (q2Sig hcenter ξ ^ k) a = d := by
  intro a d ha hd
  obtain ⟨k, hk⟩ := htrans (⟨0, a⟩ : TwoStep V W b) ⟨0, d⟩
    (orderOf_zero_snd (b := b) ha) (orderOf_zero_snd (b := b) hd)
  refine ⟨k, ?_⟩
  have h1 := q2_xi_pow_apply_zero hcenter ξ k a
  have h2 : (⟨0, (q2Sig hcenter ξ ^ k) a⟩ : TwoStep V W b) = ⟨0, d⟩ := by
    rw [← h1]; exact hk
  simpa using congrArg (fun x : TwoStep V W b => x.snd) h2

/-- A power of `q2Sig` fixing a non-zero vector is the identity. -/
theorem q2Sig_fixed_eq_one
    (hσtrans : ∀ a d : W, a ≠ 0 → d ≠ 0 → ∃ k : ℕ, (q2Sig hcenter ξ ^ k) a = d)
    {k : ℕ} {w : W} (hw : w ≠ 0) (hfix : (q2Sig hcenter ξ ^ k) w = w) :
    q2Sig hcenter ξ ^ k = 1 := by
  ext w'
  rcases eq_or_ne w' 0 with rfl | hw'
  · simp
  · obtain ⟨j, hj⟩ := hσtrans w w' hw hw'
    calc (q2Sig hcenter ξ ^ k) w' = (q2Sig hcenter ξ ^ k) ((q2Sig hcenter ξ ^ j) w) := by
          rw [hj]
      _ = (q2Sig hcenter ξ ^ (k + j)) w := by rw [pow_add, LinearEquiv.mul_apply]
      _ = (q2Sig hcenter ξ ^ (j + k)) w := by rw [add_comm]
      _ = (q2Sig hcenter ξ ^ j) ((q2Sig hcenter ξ ^ k) w) := by
            rw [pow_add, LinearEquiv.mul_apply]
      _ = (q2Sig hcenter ξ ^ j) w := by rw [hfix]
      _ = w' := hj

/-- **`ξ` acts freely on `W ∖ {0}`.**  Both the order of `q2Sig` and the divisibility form of
freeness. -/
theorem q2Sig_orderOf_and_free (hW : 4 ≤ Nat.card W)
    (hord : orderOf ξ = Nat.card W - 1)
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y) :
    orderOf (q2Sig hcenter ξ) = Nat.card W - 1 ∧
      (∀ (k : ℕ) (w : W), w ≠ 0 → (q2Sig hcenter ξ ^ k) w = w →
        (Nat.card W - 1) ∣ k) := by
  have hσtrans := q2Sig_trans hcenter ξ htrans
  have hσord : orderOf (q2Sig hcenter ξ) = Nat.card W - 1 :=
    q2_orderOf_of_transitive_linear (q2Sig hcenter ξ) (by omega) hσtrans
  refine ⟨hσord, ?_⟩
  intro k w hw hfix
  have h1 : q2Sig hcenter ξ ^ k = 1 := q2Sig_fixed_eq_one hcenter ξ hσtrans hw hfix
  have h2 : orderOf (q2Sig hcenter ξ) ∣ k := by
    rw [orderOf_dvd_iff_pow_eq_one]; exact h1
  rwa [hσord] at h2

end Linear

/-! ## Freeness on `V ∖ {0}` -/

/-- The polar identity for a biadditive form, in additive form. -/
theorem q2_biadd_self_add (u v : V) :
    b (u + v) (u + v) + b u u + b v v + b u v + b v u = 0 := by
  have h : b (u + v) (u + v) = b u u + b u v + b v u + b v v := by
    rw [Biadd.add_left (b := b) u v (u + v), Biadd.add_right (b := b) u u v,
      Biadd.add_right (b := b) v u v]
    abel
  rw [h, show b u u + b u v + b v u + b v v + b u u + b v v + b u v + b v u =
      (b u u + b u u) + (b v v + b v v) + (b u v + b u v) + (b v u + b v u) from by abel,
    AddExpTwo.add_self (b u u), AddExpTwo.add_self (b v v), AddExpTwo.add_self (b u v),
    AddExpTwo.add_self (b v u), zero_add, zero_add, zero_add]

/-- `ξ`-equivariance of the squaring form, iterated. -/
theorem q2XiV_iterate_quad (k : ℕ) (u : V) :
    b ((q2XiV hcenter ξ : V → V)^[k] u) ((q2XiV hcenter ξ : V → V)^[k] u)
      = ((q2XiW hcenter ξ : W → W)^[k]) (b u u) := by
  induction k with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      exact q2_xiV_quad hcenter ξ _

/-- **`ξ` acts freely on `V ∖ {0}`**: a power of `q2XiV` fixing a non-zero vector is the
identity.  This is the "`α`-trick": `u + ξ^k u = 0` makes `b u u + ξ_W^k (b u u) = 0`. -/
theorem q2XiV_fix_dvd
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hW : 4 ≤ Nat.card W) (hord : orderOf ξ = Nat.card W - 1)
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y)
    (u : V) (hu : u ≠ 0) (k : ℕ) (h : ((q2XiV hcenter ξ : V → V)^[k]) u = u) :
    (Nat.card W - 1) ∣ k := by
  have hQu : b u u ≠ 0 := fun h0 => hu ((b_self_eq_zero_iff hinvol hcenter u).mp h0)
  have h2 : b (((q2XiV hcenter ξ : V → V)^[k]) u + u)
        (((q2XiV hcenter ξ : V → V)^[k]) u + u) +
      b (((q2XiV hcenter ξ : V → V)^[k]) u) (((q2XiV hcenter ξ : V → V)^[k]) u) + b u u +
      b (((q2XiV hcenter ξ : V → V)^[k]) u) u +
      b u (((q2XiV hcenter ξ : V → V)^[k]) u) = 0 :=
    q2_biadd_self_add _ _
  have h1 : b (((q2XiV hcenter ξ : V → V)^[k]) u + u)
      (((q2XiV hcenter ξ : V → V)^[k]) u + u) = 0 := by
    rw [h, AddExpTwo.add_self u]
    exact Biadd.zero_left (b := b) (0 : V)
  rw [h1, zero_add, q2XiV_iterate_quad hcenter ξ k u, h] at h2
  rw [show ((q2XiW hcenter ξ : W → W)^[k]) (b u u) + b u u + b u u + b u u =
      (((q2XiW hcenter ξ : W → W)^[k]) (b u u) + b u u) + (b u u + b u u) from by abel,
    AddExpTwo.add_self (b u u), add_zero] at h2
  have hfix : ((q2XiW hcenter ξ : W → W)^[k]) (b u u) = b u u :=
    AddExpTwo.eq_of_add_eq_zero h2
  -- transfer to `q2Sig`, where freeness was proved
  letI : Module (ZMod 2) V :=
    AddCommGroup.zmodModule fun z => by rw [two_nsmul]; exact AddExpTwo.add_self z
  letI : Module (ZMod 2) W :=
    AddCommGroup.zmodModule fun z => by rw [two_nsmul]; exact AddExpTwo.add_self z
  have hfixsig : (q2Sig hcenter ξ ^ k) (b u u) = b u u := by
    rw [q2Sig_pow_apply hcenter ξ k (b u u), hfix]
  exact (q2Sig_orderOf_and_free hcenter ξ hW hord htrans).2 k (b u u) hQu hfixsig

/-! ## The permutation of `V` and its order -/

/-- The permutation of `V` induced by `q2XiV`. -/
def q2XiVPerm : Equiv.Perm V := (q2XiV hcenter ξ).toEquiv

theorem q2XiVPerm_apply (v : V) : q2XiVPerm hcenter ξ v = q2XiV hcenter ξ v := rfl

/-- The iterates of the permutation are the iterates of `q2XiV`. -/
theorem q2XiVPerm_pow (k : ℕ) (v : V) :
    (q2XiVPerm hcenter ξ ^ k) v = ((q2XiV hcenter ξ : V → V)^[k]) v := by
  rw [Equiv.Perm.coe_pow,
    show (q2XiVPerm hcenter ξ : V → V) = (q2XiV hcenter ξ : V → V) from rfl]

/-- `q2XiV` turns multiplication of automorphisms into composition. -/
theorem q2XiV_mul (ψ : MulAut (TwoStep V W b)) (v : V) :
    q2XiV hcenter (ξ * ψ) v = q2XiV hcenter ξ (q2XiV hcenter ψ v) := by
  rw [q2XiV_apply, q2XiV_apply, q2XiV_apply]
  exact q2_xi_fst hcenter ξ _

/-- The iterates of `q2XiV` are `q2XiV` of the corresponding power of `ξ`. -/
theorem q2XiV_pow (k : ℕ) (v : V) :
    q2XiV hcenter (ξ ^ k) v = ((q2XiV hcenter ξ : V → V)^[k]) v := by
  induction k with
  | zero => rw [pow_zero, Function.iterate_zero_apply, q2XiV_apply]; rfl
  | succ k ih => rw [pow_succ', Function.iterate_succ_apply', q2XiV_mul, ih]

/-- `q2XiVPerm ξ ^ (|W| - 1)` is the identity. -/
theorem q2XiVPerm_pow_card_sub_one (hord : orderOf ξ = Nat.card W - 1) :
    q2XiVPerm hcenter ξ ^ (Nat.card W - 1) = 1 := by
  ext v
  rw [q2XiVPerm_pow, Equiv.Perm.coe_one, id_eq,
    ← q2XiV_pow hcenter ξ (Nat.card W - 1) v, ← hord, pow_orderOf_eq_one, q2XiV_apply]
  rfl

/-- A power of `q2XiVPerm` fixing a non-zero vector is the identity. -/
theorem q2XiVPerm_pow_eq_one_of_fix
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hW : 4 ≤ Nat.card W) (hord : orderOf ξ = Nat.card W - 1)
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y)
    {v : V} (hv : v ≠ 0) {k : ℕ} (h : (q2XiVPerm hcenter ξ ^ k) v = v) :
    q2XiVPerm hcenter ξ ^ k = 1 := by
  have hfix : ((q2XiV hcenter ξ : V → V)^[k]) v = v := by
    rw [← q2XiVPerm_pow hcenter ξ k v]; exact h
  have hdvd : (Nat.card W - 1) ∣ k := q2XiV_fix_dvd hcenter ξ hinvol hW hord htrans v hv k hfix
  have hmod : k % (Nat.card W - 1) = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  have hdecomp : k = (Nat.card W - 1) * (k / (Nat.card W - 1)) + k % (Nat.card W - 1) :=
    (Nat.div_add_mod k (Nat.card W - 1)).symm
  have hpow : q2XiVPerm hcenter ξ ^ ((Nat.card W - 1) * (k / (Nat.card W - 1))) =
      (q2XiVPerm hcenter ξ ^ (Nat.card W - 1)) ^ (k / (Nat.card W - 1)) :=
    pow_mul (q2XiVPerm hcenter ξ) (Nat.card W - 1) (k / (Nat.card W - 1))
  rw [hdecomp, pow_add, hpow, q2XiVPerm_pow_card_sub_one hcenter ξ hord, one_pow, one_mul, hmod,
    pow_zero]

/-- **The order of the permutation induced by `ξ`** is `|W| - 1`. -/
theorem orderOf_q2XiVPerm
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hW : 4 ≤ Nat.card W) (hord : orderOf ξ = Nat.card W - 1)
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y)
    (hcardV : Nat.card V = Nat.card W ^ 2) :
    orderOf (q2XiVPerm hcenter ξ) = Nat.card W - 1 := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Nontrivial V := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hcardV]
    nlinarith [hW]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine Nat.dvd_antisymm ?_ ?_
  · rw [orderOf_dvd_iff_pow_eq_one]
    exact q2XiVPerm_pow_card_sub_one hcenter ξ hord
  · have hfix : ((q2XiV hcenter ξ : V → V)^[orderOf (q2XiVPerm hcenter ξ)]) v = v := by
      rw [← q2XiVPerm_pow hcenter ξ (orderOf (q2XiVPerm hcenter ξ)) v, pow_orderOf_eq_one]
      rfl
    exact q2XiV_fix_dvd hcenter ξ hinvol hW hord htrans v hv _ hfix

end Main

end Work.Higman.Q3.L12
