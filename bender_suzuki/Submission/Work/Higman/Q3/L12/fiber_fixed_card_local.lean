/-
# Counting the fixed points of an isometry of `V` by fibres of the squaring form

`V`, `W` are elementary abelian `2`-groups with a biadditive cocycle `b : V → V → W`,
`|V| = |W|²`, `4 ≤ |W|`, all involutions of `P = TwoStep V W b` central and `Z(P) = kerFst`.
`ξ : MulAut P` is transitive on the involutions, `β : V ≃+ V` an additive automorphism
commuting with the automorphism `xiV ξ` of `V = P / Z(P)` induced by `ξ`.

The squaring form is `Q v = b v v`.  Writing `S = Fix β` for the fixed space of `β` (an
`𝔽₂`-subspace of `V`) and `F w = {v : β v = v, Q v = w}`, anisotropy gives
`F 0 = {0}`, so

`|S| - 1 = |S \ {0}| = ∑_{w ≠ 0} |F w|`.

Since `Q` is `ξ`-equivariant (`Q (xiV ξ u) = xiW ξ (Q u)`) and `β` commutes with `xiV ξ`,
the iterate `(xiV ξ)^{2k}` maps `F a` onto `F c` for any two non-zero `a`, `c` (choose `k`
with `(xiW ξ)^k a = c`, using the transitivity of `ξ` on the involutions `⟨0, w⟩`).  Hence
all the non-zero fibres `F w` are equinumerous and

`|S| - 1 = (|W| - 1) · |F w₀|`.
-/

import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.cocycle_setup
import Submission.Work.Higman.Q3.L12.induced_local

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.Higman.Q3

theorem fiber_fixed_card
    {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    {b : V → V → W} [Biadd b]
    (hcardV : Nat.card V = Nat.card W ^ 2) (hW : 4 ≤ Nat.card W)
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b))
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y)
    (β : V ≃+ V)
    (hβQ : ∀ v : V, b (β v) (β v) = b v v)
    (hcomm : ∀ v : V, β ((ξ (⟨v, 0⟩ : TwoStep V W b)).fst) = (ξ (⟨β v, 0⟩ : TwoStep V W b)).fst)
    (w₀ : W) (hw₀ : w₀ ≠ 0) :
    Nat.card {v : V // β v = v} - 1 =
      (Nat.card W - 1) * Nat.card {v : V // b v v = w₀ ∧ β v = v} := by
  classical
  haveI : Finite W := finite_of_hW hW
  haveI : Finite V := finite_V_of_hcardV hcardV hW
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype W := Fintype.ofFinite W
  -- The squaring form is anisotropic: `b v v = 0 ↔ v = 0`.
  have haniso : ∀ v : V, b v v = 0 ↔ v = 0 := fun v => b_self_eq_zero_iff hinvol hcenter v
  -- The `W`-coordinate of `ξ ^ k` on the involutions: `ξ ^ k ⟨0,w⟩ = ⟨0, (xiW ξ)^[k] w⟩`.
  have hxi_iter : ∀ (k : ℕ) (w : W),
      (ξ ^ k) (⟨0, w⟩ : TwoStep V W b) = ⟨0, (xiW hcenter ξ)^[k] w⟩ := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ, MulAut.mul_apply, xi_apply_zero, Function.iterate_succ_apply]
      exact ih (xiW hcenter ξ w)
  -- `xiW ξ` is transitive on `W \ {0}`.
  have htransW : ∀ a c : W, a ≠ 0 → c ≠ 0 → ∃ k : ℕ, (xiW hcenter ξ)^[k] a = c := by
    intro a c ha hc
    have h2a : orderOf (⟨0, a⟩ : TwoStep V W b) = 2 :=
      (orderOf_eq_two_iff hinvol hcenter _).mpr ⟨rfl, ha⟩
    have h2c : orderOf (⟨0, c⟩ : TwoStep V W b) = 2 :=
      (orderOf_eq_two_iff hinvol hcenter _).mpr ⟨rfl, hc⟩
    obtain ⟨k, hk⟩ := htrans _ _ h2a h2c
    refine ⟨k, ?_⟩
    have h := hxi_iter k a
    have h2 : (⟨0, (xiW hcenter ξ)^[k] a⟩ : TwoStep V W b) = ⟨0, c⟩ := by rw [← h]; exact hk
    simpa using congrArg (fun x : TwoStep V W b => x.snd) h2
  -- Equivariance of the squaring form under iterates of `xiV ξ`.
  have hquad : ∀ (k : ℕ) (v : V),
      b ((xiV hcenter ξ)^[k] v) ((xiV hcenter ξ)^[k] v) = (xiW hcenter ξ)^[k] (b v v) := by
    intro k v
    induction k with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (xiV_quad hcenter ξ ((xiV hcenter ξ)^[n] v)).trans (congrArg (xiW hcenter ξ) ih)
  -- `β` commutes with iterates of `xiV ξ`.
  have hbeta : ∀ (k : ℕ) (v : V), β ((xiV hcenter ξ)^[k] v) = (xiV hcenter ξ)^[k] (β v) := by
    intro k v
    induction k with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      exact hcomm ((xiV hcenter ξ)^[n] v)
  -- All non-zero fibres of `Q v = b v v` have the same number of `β`-fixed points.
  have key : ∀ a c : W, a ≠ 0 → c ≠ 0 →
      Nat.card {v : V // β v = v ∧ b v v = a} ≤ Nat.card {v : V // β v = v ∧ b v v = c} := by
    intro a c ha hc
    obtain ⟨k, hk⟩ := htransW a c ha hc
    refine Nat.card_le_card_of_injective
      (fun u : {v : V // β v = v ∧ b v v = a} =>
        (⟨(xiV hcenter ξ)^[k] u.1, ?_, ?_⟩ : {v : V // β v = v ∧ b v v = c})) ?_
    · exact (hbeta k u.1).trans (by rw [u.2.1])
    · exact (hquad k u.1).trans (by rw [u.2.2, hk])
    · intro u u' huv
      exact Subtype.ext
        ((Function.Injective.iterate (xiV hcenter ξ).injective k) (congrArg Subtype.val huv))
  have hcardF : ∀ a c : W, a ≠ 0 → c ≠ 0 →
      Nat.card {v : V // β v = v ∧ b v v = a} = Nat.card {v : V // β v = v ∧ b v v = c} :=
    fun a c ha hc => le_antisymm (key a c ha hc) (key c a hc ha)
  -- `|Fix β| - 1` counts the non-zero fixed points.
  have hS0 : Nat.card {v : V // β v = v} - 1 = Nat.card {v : V // β v = v ∧ v ≠ 0} := by
    have h0 : β (0 : V) = 0 := map_zero β
    have h := card_subtype_ne_zero {v : V // β v = v} (⟨0, h0⟩)
    rw [← h]
    refine Nat.card_congr ?_
    refine
      { toFun := fun x => ⟨x.1.1, x.1.2, fun hx => x.2 (Subtype.ext hx)⟩
        invFun := fun v => ⟨⟨v.1, v.2.1⟩, fun hx => v.2.2 (congrArg Subtype.val hx)⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro x; exact Subtype.ext (Subtype.ext rfl)
    · intro v; exact Subtype.ext rfl
  -- Partition the non-zero fixed points by the value of the squaring form.
  set T : Finset W := (Finset.univ : Finset W).filter (fun w => w ≠ 0) with hT
  have mem_T : ∀ w : W, w ∈ T ↔ w ≠ 0 := by intro w; rw [hT]; simp
  have hpart : Nat.card {v : V // β v = v ∧ v ≠ 0}
      = ∑ w ∈ T, Nat.card {v : V // β v = v ∧ b v v = w} := by
    set s : Finset V := (Finset.univ : Finset V).filter (fun v => β v = v ∧ v ≠ 0) with hs
    have h3 : Nat.card {v : V // β v = v ∧ v ≠ 0} = s.card := by
      rw [hs, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h1 : s.card = ∑ w ∈ T, (s.filter (fun v => b v v = w)).card := by
      refine Finset.card_eq_sum_card_fiberwise ?_
      intro v hv
      rw [Finset.mem_coe, hs, Finset.mem_filter] at hv
      simp only [Finset.mem_univ, true_and] at hv
      rw [Finset.mem_coe, mem_T]
      exact fun h => hv.2 ((haniso v).mp h)
    have h2 : ∀ w ∈ T, (s.filter (fun v => b v v = w)).card
        = Nat.card {v : V // β v = v ∧ b v v = w} := by
      intro w hw
      have hw0 : w ≠ 0 := (mem_T w).mp hw
      have hset : s.filter (fun v => b v v = w)
          = (Finset.univ : Finset V).filter (fun v => β v = v ∧ b v v = w) := by
        ext v
        simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨hbv, _⟩, hw'⟩; exact ⟨hbv, hw'⟩
        · rintro ⟨hbv, hw'⟩
          exact ⟨⟨hbv, fun hv0 => hw0 (by rw [← hw', hv0]; exact Biadd.zero_left (0 : V))⟩,
            hw'⟩
      rw [hset, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h3, h1]
    exact Finset.sum_congr rfl h2
  have htcard : T.card = Nat.card W - 1 := by
    have ht2 : T.card = Nat.card {w : W // w ≠ 0} := by
      rw [hT, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [ht2]; exact card_subtype_ne_zero W (0 : W)
  have hsum : ∑ w ∈ T, Nat.card {v : V // β v = v ∧ b v v = w}
      = T.card * Nat.card {v : V // β v = v ∧ b v v = w₀} := by
    refine Finset.sum_const_nat ?_
    intro w hw
    exact hcardF w w₀ ((mem_T w).mp hw) hw₀
  have hw₀F : Nat.card {v : V // b v v = w₀ ∧ β v = v}
      = Nat.card {v : V // β v = v ∧ b v v = w₀} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun v => and_comm))
  rw [hS0, hpart, hsum, htcard, ← hw₀F]

end Work.Higman.Q3
