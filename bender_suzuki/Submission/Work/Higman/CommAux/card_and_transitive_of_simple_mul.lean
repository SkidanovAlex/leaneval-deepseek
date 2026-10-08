import Mathlib
import Submission.Work.Higman.SZ.model
import Submission.Work.Higman.h8_core
import Submission.Work.Higman.H8.card_pow_of_irreducible

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.CommAux

/-- **Elementary abelian `2`-groups with an irreducible Singer-type automorphism.**

Let `V` be a finite commutative group of exponent two (equivalently, a finite `𝔽₂`-vector space
written multiplicatively) and `ξ` a multiplicative automorphism of `V` of order `2 ^ n - 1`
(`n ≥ 2`) whose only `ξ`-invariant subgroups are `⊥` and `⊤`.  Then `|V| = 2 ^ n` and `ξ` acts
transitively on `V ∖ {1}`.

The proof transports everything to the additive setting: `Additive V` becomes an
`𝔽₂`-vector space on which `ξ` acts as an `𝔽₂`-linear automorphism `ξl` of order `2 ^ n - 1`
with only the trivial `ξl`-invariant subspaces.  The cardinality statement is
`Work.Higman.H8.card_pow_of_irreducible`; the transitivity then follows from
`Work.Higman.transitive_of_singer_data` (the "converse" of `exists_singer_iso`), for which we also
supply the fixed-point-freeness of `ξ`. -/
theorem card_and_transitive_of_simple_mul {n : ℕ} (hn : 2 ≤ n)
    {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v * v = 1)
    (ξ : MulAut V)
    (hsimple : ∀ W : Subgroup V, (∀ v ∈ W, ξ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hord : orderOf ξ = 2 ^ n - 1) :
    Nat.card V = 2 ^ n ∧ ∀ a b : V, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (ξ ^ k) a = b := by
  classical
  -- ## `V` as an `𝔽₂`-vector space
  have h2 : ∀ v : Additive V, (2 : ℕ) • v = 0 := by
    intro v
    rw [← ofMul_toMul v, ← ofMul_pow, ofMul_eq_zero, pow_two]
    exact hV2 (Additive.toMul v)
  haveI hmod : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2
  -- ## `ξ` as an `𝔽₂`-linear automorphism `ξl`
  let ξl : Additive V ≃ₗ[ZMod 2] Additive V :=
    LinearEquiv.ofBijective
      (AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive ξ).toAddMonoidHom)
      (MulEquiv.toAdditive ξ).bijective
  have hξl_apply : ∀ x : Additive V, ξl x = Additive.ofMul (ξ (Additive.toMul x)) :=
    fun _ => rfl
  have hξl_pow : ∀ (k : ℕ) (x : Additive V),
      (ξl ^ k) x = Additive.ofMul ((ξ ^ k) (Additive.toMul x)) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      have h1 : (ξl ^ (k + 1)) x = ξl ((ξl ^ k) x) := by
        rw [pow_succ', LinearEquiv.mul_apply]
      have h2 : (ξ ^ (k + 1)) (Additive.toMul x) = ξ ((ξ ^ k) (Additive.toMul x)) := by
        rw [pow_succ', MulAut.mul_apply]
      rw [h1, ih x, h2, hξl_apply (Additive.ofMul ((ξ ^ k) (Additive.toMul x)))]
      simp only [toMul_ofMul]
  have hiff : ∀ k : ℕ, (ξl ^ k = 1) ↔ (ξ ^ k = 1) := by
    intro k
    constructor
    · intro h
      ext v
      have hv := congrArg (fun f : Additive V ≃ₗ[ZMod 2] Additive V =>
        f (Additive.ofMul v)) h
      rw [hξl_pow k (Additive.ofMul v), toMul_ofMul] at hv
      have hv' : Additive.ofMul ((ξ ^ k) v) = Additive.ofMul v := by simpa using hv
      exact Additive.ofMul.injective hv'
    · intro h
      ext x
      rw [hξl_pow k x, h]
      simp
  have hξl_order : orderOf ξl = 2 ^ n - 1 := by
    have h : orderOf ξl = orderOf ξ := orderOf_eq_orderOf_iff.mpr hiff
    rw [h, hord]
  -- ## Irreducibility transfers to the linear setting
  have hirr : ∀ U : Submodule (ZMod 2) (Additive V),
      (∀ v ∈ U, ξl v ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    let W : Subgroup V :=
      { carrier := {x : V | Additive.ofMul x ∈ U},
        one_mem' := by
          show Additive.ofMul (1 : V) ∈ U
          rw [ofMul_one]
          exact U.zero_mem,
        mul_mem' := by
          intro a b ha hb
          show Additive.ofMul (a * b) ∈ U
          rw [ofMul_mul]
          exact U.add_mem ha hb,
        inv_mem' := by
          intro a ha
          show Additive.ofMul a⁻¹ ∈ U
          rw [ofMul_inv]
          exact U.neg_mem ha }
    have hWinv : ∀ v ∈ W, ξ v ∈ W := by
      intro v hv
      show Additive.ofMul (ξ v) ∈ U
      have h1 : ξl (Additive.ofMul v) = Additive.ofMul (ξ v) := hξl_apply (Additive.ofMul v)
      rw [← h1]
      exact hU (Additive.ofMul v) hv
    rcases hsimple W hWinv with hbot | htop
    · left
      rw [Submodule.eq_bot_iff]
      intro y hy
      have hmem : Additive.toMul y ∈ W := by
        show Additive.ofMul (Additive.toMul y) ∈ U
        rw [ofMul_toMul]
        exact hy
      rw [hbot] at hmem
      have hy1 : Additive.toMul y = 1 := Subgroup.mem_bot.mp hmem
      rw [← ofMul_toMul y, hy1, ofMul_one]
    · right
      rw [Submodule.eq_top_iff']
      intro y
      have hmem : Additive.toMul y ∈ W := by rw [htop]; exact Subgroup.mem_top _
      show y ∈ U
      rw [← ofMul_toMul y]
      exact hmem
  -- ## `V` is non-trivial
  haveI hVnt : Nontrivial V := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    haveI : Subsingleton V := hsub
    have hξ1 : ξ = 1 := by
      apply MulEquiv.ext
      intro v
      exact Subsingleton.elim (ξ v) ((1 : MulAut V) v)
    rw [hξ1, orderOf_one] at hord
    have hge : 3 ≤ 2 ^ n - 1 := by
      have h4 : (4 : ℕ) ≤ 2 ^ n := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    omega
  -- ## Cardinality
  have hcard_add : Nat.card (Additive V) = 2 ^ n :=
    Work.Higman.H8.card_pow_of_irreducible (by omega : 1 ≤ n) ξl hξl_order hirr
  have hcard : Nat.card V = 2 ^ n := hcard_add
  -- ## `ξ` has no non-zero fixed point
  have hfree : ∀ v : Additive V, ξl v = v → v = 0 := by
    intro v hv
    by_contra hv0
    let U : Submodule (ZMod 2) (Additive V) :=
      { carrier := {w | ξl w = w},
        zero_mem' := by simp,
        add_mem' := by
          intro a b ha hb
          change ξl a = a at ha
          change ξl b = b at hb
          show ξl (a + b) = a + b
          rw [map_add, ha, hb],
        smul_mem' := by
          intro c a ha
          change ξl a = a at ha
          show ξl (c • a) = c • a
          rw [map_smul, ha] }
    have hinv : ∀ w ∈ U, ξl w ∈ U := by
      intro w hw
      change ξl (ξl w) = ξl w
      exact congrArg ξl hw
    rcases hirr U hinv with h | h
    · have hvU : v ∈ U := hv
      rw [h] at hvU
      exact hv0 ((Submodule.mem_bot (ZMod 2)).mp hvU)
    · have hξl1 : ξl = 1 := by
        ext w
        have hw : w ∈ U := by rw [h]; exact Submodule.mem_top
        show ξl w = w
        exact hw
      have hone : orderOf ξl = 1 := by rw [hξl1]; exact orderOf_one
      rw [hξl_order] at hone
      have hge : 3 ≤ 2 ^ n - 1 := by
        have h4 : (4 : ℕ) ≤ 2 ^ n := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        omega
      omega
  -- ## Transitivity in the additive setting, transferred back
  have htransa : ∀ a b : Additive V, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξl ^ k) a = b :=
    Work.Higman.transitive_of_singer_data hn hcard_add ξl hξl_order hfree
  refine ⟨hcard, ?_⟩
  intro a b ha hb
  have ha' : Additive.ofMul a ≠ 0 := fun h => ha (ofMul_eq_zero.mp h)
  have hb' : Additive.ofMul b ≠ 0 := fun h => hb (ofMul_eq_zero.mp h)
  obtain ⟨k, hk⟩ := htransa (Additive.ofMul a) (Additive.ofMul b) ha' hb'
  refine ⟨k, ?_⟩
  rw [hξl_pow k (Additive.ofMul a), toMul_ofMul] at hk
  exact Additive.ofMul.injective hk

end Work.Higman.CommAux
