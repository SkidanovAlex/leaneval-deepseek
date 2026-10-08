import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.B_normalizes_K
import Submission.Work.BG.thmCSec3
import Submission.Work.GLUE.Defs

/-!
# `B₂ = B` under the hypotheses of Bender–Glauberman's Theorem C

Notation (`Work.GW2.BGData`): `H = C_G(t)`, `U = O(H)`,
`B₁ = U ⊓ C_G(t₁)`, `B₂ = U ⊓ C_G(t₂)` and `B = B₁ ⊓ B₂`.  The claim of this file is that
the hypotheses of Theorem C force `B₂ = B`, equivalently `B₂ ≤ B₁`, i.e. every element of `U`
centralized by `t₂` is centralized by `t₁` as well.

The mathematical content is that `B` exhausts the `t₂`-fixed part of `U`.  Write
`K = K₁ ⊓ K₂` and `A = B₁ ⊓ K₂`; the direct decomposition hypothesis reads
`U = A ⊔ C` with `C = B ⊔ K`, `A ⊓ C = ⊥` and `A` centralizing `C`.  Since `t₂` centralizes
`B ≤ B₂` and inverts `K ≤ K₂`, conjugation by `t₂` preserves `C`, and `C` is the set product
`B * K` because `B` normalizes `K`.

* `C ⊓ B₂ = B`: for `x = b k ∈ C` (`b ∈ B`, `k ∈ K`) fixed by `t₂`, the equality
  `b k = b k⁻¹` forces `k² = 1`, and `k` has odd order, so `k = 1`.
* `B₂ ≤ C`: for `x ∈ B₂ ⊆ U = A ⊔ C`, say `x = a c`, the fixed point relation gives
  `a² = (t₂ c t₂⁻¹) c⁻¹ ∈ A ⊓ C = ⊥`, so `a² = 1`, and `a` has odd order, so `a = 1`.

Hence `B₂ = B₂ ⊓ C = B`.
-/

namespace Work.BG

open scoped Pointwise

/-! ### Elementary group-theoretic helpers -/

/-- An element commuting with `s` is fixed by conjugation by `s`. -/
private lemma conj_mul_inv_eq_self_of_mem_centralizer {G : Type*} [Group G] {s x : G}
    (h : x ∈ Subgroup.centralizer ({s} : Set G)) : s * x * s⁻¹ = x := by
  have hc : s * x = x * s := Subgroup.mem_centralizer_iff.mp h s (by simp)
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

/-- An element of odd order whose square is `1` is trivial. -/
private lemma eq_one_of_odd_orderOf_of_sq_eq_one {G : Type*} [Group G] {x : G}
    (hodd : Odd (orderOf x)) (hx : x ^ 2 = 1) : x = 1 := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx
  obtain ⟨m, hm⟩ := hodd
  have hle : orderOf x ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  exact orderOf_eq_one_iff.mp (by omega)

/-- An element of a subgroup of odd order has odd order. -/
private lemma odd_orderOf_of_mem {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (hH : Odd (Nat.card H)) (hx : x ∈ H) : Odd (orderOf x) :=
  Odd.of_dvd_nat hH <| by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx)

/-- An element of a subgroup of odd order whose square is `1` is trivial. -/
private lemma eq_one_of_mem_of_sq_eq_one {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (hH : Odd (Nat.card H)) (hx : x ∈ H) (h : x ^ 2 = 1) : x = 1 :=
  eq_one_of_odd_orderOf_of_sq_eq_one (odd_orderOf_of_mem hH hx) h

/-- Decomposition of an element of a set-theoretic product. -/
private lemma exists_mul_of_mem_mul {G : Type*} [Group G] {s t : Set G} {x : G}
    (h : x ∈ s * t) : ∃ a ∈ s, ∃ b ∈ t, a * b = x :=
  Set.mem_mul.mp h

/-- `B₂ = B` under the hypotheses of Theorem C of Bender–Glauberman: the `t₂`-fixed part of
`U = O(C_G(t))` is already centralized by `t₁`. -/
theorem B2_eq_B {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G)
    (K1 K2 : Subgroup G) (hHyps : Work.GW2.C16.ThmCHyps D K1 K2) :
    D.B2 = D.B := by
  obtain ⟨h1, h2, hdir, hcop, hB', hfr⟩ := hHyps
  set K : Subgroup G := K1 ⊓ K2 with hKdef
  set C : Subgroup G := D.B ⊔ K with hCdef
  set A : Subgroup G := D.B1 ⊓ K2 with hAdef
  -- `K` and `A` have odd order.
  have hK_le_K1 : K ≤ K1 := hKdef.le.trans inf_le_left
  have hK_le_K2 : K ≤ K2 := hKdef.le.trans inf_le_right
  have hA_le_K2 : A ≤ K2 := hAdef.le.trans inf_le_right
  have hK_odd : Odd (Nat.card K) := Odd.of_dvd_nat h1.2.1 (Subgroup.card_dvd_of_le hK_le_K1)
  have hA_odd : Odd (Nat.card A) := Odd.of_dvd_nat h2.2.1 (Subgroup.card_dvd_of_le hA_le_K2)
  -- Containments between `B`, `K`, `C` and `U = A ⊔ C`.
  have hK_le_C : K ≤ C := le_sup_right
  have hB_le_C : D.B ≤ C := le_sup_left
  have hC_le_U : C ≤ D.U := by rw [← hdir.1]; exact le_sup_right
  -- `B ⊓ K = ⊥`: an element of `B ≤ C_G(t₁)` lying in `K ≤ K₁` is centralized *and*
  -- inverted by `t₁`.
  have hBK_inf : D.B ⊓ K = ⊥ := by
    rw [hKdef]
    exact le_bot_iff.mp ((inf_le_inf_left D.B inf_le_left).trans
      (le_of_eq (thmCSec3_B_inf_K1 D K1 h1)))
  -- `B` and `K` normalize `K`, so `C ≤ N_G(K)` and `C` is the set product `B * K`.
  have hnormB : D.B ≤ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    simpa [hKdef] using B_normalizes_K D K1 K2 h1 h2
  have hnormC : C ≤ Subgroup.normalizer (K : Set G) := by
    rw [hCdef]
    exact sup_le hnormB Subgroup.le_normalizer
  have hC_mul : (↑C : Set G) = (D.B : Set G) * (K : Set G) := by
    rw [hCdef]
    exact Subgroup.coe_mul_of_left_le_normalizer_right D.B K hnormB
  have hC_decomp : ∀ x ∈ C, ∃ b ∈ D.B, ∃ k ∈ K, b * k = x := by
    intro x hx
    have hx' : x ∈ (D.B : Set G) * (K : Set G) := by rw [← hC_mul]; exact hx
    exact exists_mul_of_mem_mul hx'
  -- `A` centralizes `C`, hence `A ≤ N_G(C)` and `A ⊔ C = A * C`.
  have hA_le_NC : A ≤ Subgroup.normalizer (C : Set G) := by
    refine (show A ≤ Subgroup.centralizer (C : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer (C : Set G))
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (hdir.2.2 a ha c hc).symm
  have hAC_mul : (↑(A ⊔ C) : Set G) = (A : Set G) * (C : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A C hA_le_NC
  have hAC_decomp : ∀ x ∈ A ⊔ C, ∃ a ∈ A, ∃ c ∈ C, a * c = x := by
    intro x hx
    have hx' : x ∈ (A : Set G) * (C : Set G) := by rw [← hAC_mul]; exact hx
    exact exists_mul_of_mem_mul hx'
  -- Conjugation by `t₂` preserves `C = B * K` (`B ≤ B₂` is centralized, `K ≤ K₂` inverted).
  have hconjC : ∀ c ∈ C, D.t2 * c * D.t2⁻¹ ∈ C := by
    intro c hc
    obtain ⟨b, hb, k, hk, hbk⟩ := hC_decomp c hc
    have hbB2 : b ∈ D.B2 := (Subgroup.mem_inf.mp hb).2
    have hbfix : D.t2 * b * D.t2⁻¹ = b :=
      conj_mul_inv_eq_self_of_mem_centralizer hbB2.2
    have hkinv : D.t2 * k * D.t2⁻¹ = k⁻¹ := h2.2.2.1 k (hK_le_K2 hk)
    have hstep : D.t2 * (b * k) * D.t2⁻¹ = b * k⁻¹ := by
      calc D.t2 * (b * k) * D.t2⁻¹
          = (D.t2 * b * D.t2⁻¹) * (D.t2 * k * D.t2⁻¹) := by group
        _ = b * k⁻¹ := by rw [hbfix, hkinv]
    rw [← hbk, hstep]
    exact C.mul_mem (hB_le_C hb) (hK_le_C (K.inv_mem hk))
  -- **Step 1:** `C ⊓ B₂ = B`.
  have hCinfB2 : C ⊓ D.B2 = D.B := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxC, hxB2⟩ := hx
      obtain ⟨b, hb, k, hk, hbk⟩ := hC_decomp x hxC
      have hxfix : D.t2 * x * D.t2⁻¹ = x :=
        conj_mul_inv_eq_self_of_mem_centralizer hxB2.2
      have hbB2 : b ∈ D.B2 := (Subgroup.mem_inf.mp hb).2
      have hbfix : D.t2 * b * D.t2⁻¹ = b :=
        conj_mul_inv_eq_self_of_mem_centralizer hbB2.2
      have hkinv : D.t2 * k * D.t2⁻¹ = k⁻¹ := h2.2.2.1 k (hK_le_K2 hk)
      have hstep : D.t2 * x * D.t2⁻¹ = b * k⁻¹ := by
        rw [← hbk]
        calc D.t2 * (b * k) * D.t2⁻¹
            = (D.t2 * b * D.t2⁻¹) * (D.t2 * k * D.t2⁻¹) := by group
          _ = b * k⁻¹ := by rw [hbfix, hkinv]
      have hkeq : k = 1 := by
        have h1' : b * k⁻¹ = b * k := by rw [← hstep, hxfix, hbk]
        have h2' : k⁻¹ = k := mul_left_cancel h1'
        have hk2 : k ^ 2 = 1 := by
          rw [pow_two]
          exact eq_inv_iff_mul_eq_one.mp h2'.symm
        exact eq_one_of_mem_of_sq_eq_one hK_odd hk hk2
      rw [show x = b by rw [← hbk, hkeq, mul_one]]
      exact hb
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hB_le_C hx, (Subgroup.mem_inf.mp hx).2⟩
  -- **Step 2:** `B₂ ≤ C`.
  have hB2_le_C : D.B2 ≤ C := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxU, hxcent⟩ := hx
    have hxAC : x ∈ A ⊔ C := by rw [hdir.1]; exact hxU
    obtain ⟨a, ha, c, hc, hac⟩ := hAC_decomp x hxAC
    have hxfix : D.t2 * x * D.t2⁻¹ = x :=
      conj_mul_inv_eq_self_of_mem_centralizer hxcent
    have hainv : D.t2 * a * D.t2⁻¹ = a⁻¹ := h2.2.2.1 a (hA_le_K2 ha)
    -- the fixed point relation, read on the decomposition `x = a * c`
    have hkey : a ^ 2 = (D.t2 * c * D.t2⁻¹) * c⁻¹ := by
      have h1' : D.t2 * x * D.t2⁻¹ = a⁻¹ * (D.t2 * c * D.t2⁻¹) := by
        rw [← hac]
        calc D.t2 * (a * c) * D.t2⁻¹
            = (D.t2 * a * D.t2⁻¹) * (D.t2 * c * D.t2⁻¹) := by group
          _ = a⁻¹ * (D.t2 * c * D.t2⁻¹) := by rw [hainv]
      rw [hxfix, ← hac] at h1'
      have h2' : a * a = (D.t2 * c * D.t2⁻¹) * c⁻¹ := by
        calc a * a = (a * (a * c)) * c⁻¹ := by group
          _ = (a * (a⁻¹ * (D.t2 * c * D.t2⁻¹))) * c⁻¹ := by rw [h1']
          _ = (D.t2 * c * D.t2⁻¹) * c⁻¹ := by group
      rwa [pow_two]
    have ha2A : a ^ 2 ∈ A := by rw [pow_two]; exact A.mul_mem ha ha
    have ha2C : a ^ 2 ∈ C := by
      rw [hkey]
      exact C.mul_mem (hconjC c hc) (C.inv_mem hc)
    have ha2one : a ^ 2 = 1 := by
      have hmem : a ^ 2 ∈ A ⊓ C := Subgroup.mem_inf.mpr ⟨ha2A, ha2C⟩
      rw [hdir.2.1] at hmem
      simpa using hmem
    have haone : a = 1 := eq_one_of_mem_of_sq_eq_one hA_odd ha ha2one
    rw [show x = c by rw [← hac, haone, one_mul]]
    exact hc
  -- Conclude: `B₂ = B₂ ⊓ C = B`.
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxC : x ∈ C := hB2_le_C hx
    have hx' : x ∈ C ⊓ D.B2 := Subgroup.mem_inf.mpr ⟨hxC, hx⟩
    rwa [hCinfB2] at hx'
  · exact fun x hx => (Subgroup.mem_inf.mp hx).2

end Work.BG
