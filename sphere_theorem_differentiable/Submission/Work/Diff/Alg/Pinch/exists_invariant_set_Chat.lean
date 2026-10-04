import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Strict
import Submission.Work.Diff.Alg.Pinch.Chat
import Submission.Work.Diff.Alg.Pinch.Ccone_transversal_a_aux
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic
import Submission.Work.Diff.Alg.Pinch.inPIC2_comp_bound
import Submission.Work.Diff.Alg.Pinch.ChatDefs
import Submission.Work.Diff.Alg.Pinch.FeasibleCone
import Submission.Work.Diff.Alg.Pinch.infDist_le_of_mem_feasibleCone
import Submission.Work.Diff.Alg.Pinch.le_of_dini_right
import Submission.Work.Diff.Alg.Pinch.norm_sub_sub_smul_le
import Submission.Work.Diff.Alg.Pinch.Q_lipschitz_local
import Submission.Work.Diff.Alg.Pinch.continuous_of_ball_lipschitz
import Submission.Work.Diff.Alg.Pinch.rot_knProd
import Submission.Work.Diff.Alg.Pinch.rot_knProd_id2
import Submission.Work.Diff.Alg.Pinch.rot_toolkit
import Submission.Work.Diff.Alg.Pinch.ric_rot
import Submission.Work.Diff.Alg.Pinch.scalAlg_rot
import Submission.Work.Diff.Alg.Pinch.isAlgCurv_rot
import Submission.Work.Diff.Alg.Pinch.EFun_rot
import Submission.Work.Diff.Alg.Pinch.chat_rot
import Submission.Work.Diff.Alg.Pinch.EFun_X_aux
import Submission.Work.Diff.Alg.Pinch.Chat_family_structure
import Submission.Work.Diff.Alg.Pinch.Chat_margin
import Submission.Work.Diff.Alg.Pinch.Chat_inclusion_global
import Submission.Work.Diff.Alg.Pinch.Chat_room_global
import Submission.Work.Diff.Alg.Pinch.Chat_room_global

/-!
# An invariant set for the Brendle–Schoen pinching family `Ĉ(s)`

The Böhm–Wilking / Brendle–Schoen cone family `Chat n s = Ĉ(s)` consists of the images under the
linear Böhm–Wilking transform `ell a b` of the cone
`Dpic p = {R | IsAlgCurv R ∧ InPIC2 R ∧ RicPinch p R}`.

This file collects the *structural* facts about `Chat n s` on which the construction of an
`ODEInvariant` set containing `Chat n ε ∩ {scalAlg R ≤ h₀}` rests: `Chat n s` is a closed convex
cone of algebraic curvature tensors, invariant under `O(n)`, containing the round sphere `Iso n`
as an interior point.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## The set of algebraic curvature tensors -/

/-- `IsAlgCurv` is a closed condition. -/
theorem isClosed_isAlgCurv (n : ℕ) : IsClosed {R : Curv4 n | IsAlgCurv R} := by
  have h : {R : Curv4 n | IsAlgCurv R} =
      ({R : Curv4 n | ∀ i j k l, R j i k l = - R i j k l} ∩
        {R : Curv4 n | ∀ i j k l, R k l i j = R i j k l}) ∩
        {R : Curv4 n | ∀ i j k l, R i j k l + R j k i l + R k i j l = 0} := by
    ext R
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, IsAlgCurv]
    tauto
  rw [h]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · rw [show {R : Curv4 n | ∀ i j k l, R j i k l = - R i j k l}
        = ⋂ i, ⋂ j, ⋂ k, ⋂ l, {R : Curv4 n | R j i k l = - R i j k l} from by
      ext R; simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun k =>
      isClosed_iInter fun l => isClosed_eq (by fun_prop) (by fun_prop)
  · rw [show {R : Curv4 n | ∀ i j k l, R k l i j = R i j k l}
        = ⋂ i, ⋂ j, ⋂ k, ⋂ l, {R : Curv4 n | R k l i j = R i j k l} from by
      ext R; simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun k =>
      isClosed_iInter fun l => isClosed_eq (by fun_prop) (by fun_prop)
  · rw [show {R : Curv4 n | ∀ i j k l, R i j k l + R j k i l + R k i j l = 0}
        = ⋂ i, ⋂ j, ⋂ k, ⋂ l, {R : Curv4 n | R i j k l + R j k i l + R k i j l = 0} from by
      ext R; simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun k =>
      isClosed_iInter fun l => isClosed_eq (by fun_prop) (by fun_prop)

/-- `IsAlgCurv` is closed under convex combinations. -/
theorem convex_isAlgCurv (n : ℕ) : Convex ℝ {R : Curv4 n | IsAlgCurv R} := by
  intro R hR S hS a b ha hb hab
  have h1 : IsAlgCurv (a • R) := isAlgCurv_smul a hR
  have h2 : IsAlgCurv (b • S) := isAlgCurv_smul b hS
  exact isAlgCurv_add h1 h2

/-! ## `RicPinch p` is a closed convex cone condition -/

/-- The linear functional whose nonpositivity is `RicPinch` in the direction `v`. -/
noncomputable def ricPinchFun (p : ℝ) (v : Fin n → ℝ) (R : Curv4 n) : ℝ :=
  (p * scalAlg R / (n : ℝ)) * (∑ i, v i * v i) - ∑ i, ∑ j, ric R i j * v i * v j

theorem ricPinchFun_add (p : ℝ) (v : Fin n → ℝ) (R S : Curv4 n) :
    ricPinchFun p v (R + S) = ricPinchFun p v R + ricPinchFun p v S := by
  have hric : (∑ i, ∑ j, ric (R + S) i j * v i * v j)
      = (∑ i, ∑ j, ric R i j * v i * v j) + (∑ i, ∑ j, ric S i j * v i * v j) := by
    simp only [ric_add, add_mul, Finset.sum_add_distrib]
  simp only [ricPinchFun, scalAlg_add, hric]
  ring

theorem ricPinchFun_smul (p : ℝ) (v : Fin n → ℝ) (c : ℝ) (R : Curv4 n) :
    ricPinchFun p v (c • R) = c * ricPinchFun p v R := by
  have hric : (∑ i, ∑ j, ric (c • R) i j * v i * v j)
      = c * (∑ i, ∑ j, ric R i j * v i * v j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [ric_smul]
    ring
  simp only [ricPinchFun, scalAlg_smul, hric]
  ring

theorem ricPinch_iff (p : ℝ) (R : Curv4 n) :
    RicPinch p R ↔ ∀ v : Fin n → ℝ, ricPinchFun p v R ≤ 0 := by
  simp only [RicPinch, ricPinchFun]
  constructor <;> intro h v <;> linarith [h v]

@[fun_prop]
theorem continuous_scalAlg : Continuous fun R : Curv4 n => scalAlg R := by
  simp only [scalAlg]; fun_prop

@[fun_prop]
theorem continuous_ric_apply (i j : Fin n) : Continuous fun R : Curv4 n => ric R i j := by
  simp only [ric]; fun_prop

theorem continuous_ricPinchFun (p : ℝ) (v : Fin n → ℝ) :
    Continuous fun R : Curv4 n => ricPinchFun p v R := by
  have h1 : Continuous fun R : Curv4 n => (p / (n : ℝ)) * scalAlg R * (∑ i, v i * v i) :=
    ((continuous_scalAlg.const_mul _).mul_const _)
  have h2 : Continuous fun R : Curv4 n => ∑ i, ∑ j, ric R i j * v i * v j := by
    simp only [ric]; fun_prop
  have : (fun R : Curv4 n => ricPinchFun p v R)
      = fun R => (p / (n : ℝ)) * scalAlg R * (∑ i, v i * v i)
          - ∑ i, ∑ j, ric R i j * v i * v j := by
    funext R
    simp only [ricPinchFun]
    ring
  rw [this]
  exact h1.sub h2

theorem isClosed_ricPinch (n : ℕ) (p : ℝ) : IsClosed {R : Curv4 n | RicPinch p R} := by
  rw [show {R : Curv4 n | RicPinch p R}
      = ⋂ v : Fin n → ℝ, {R : Curv4 n | ricPinchFun p v R ≤ 0} from by
    ext R; simp only [Set.mem_setOf_eq, Set.mem_iInter, ricPinch_iff]]
  exact isClosed_iInter fun v =>
    IsClosed.preimage (continuous_ricPinchFun p v) isClosed_Iic

theorem ricPinch_convex' {p : ℝ} {R S : Curv4 n} (hR : RicPinch p R) (hS : RicPinch p S)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : RicPinch p (a • R + b • S) := by
  rw [ricPinch_iff] at hR hS ⊢
  intro v
  rw [show ricPinchFun p v (a • R + b • S)
      = a * ricPinchFun p v R + b * ricPinchFun p v S by
    rw [ricPinchFun_add, ricPinchFun_smul, ricPinchFun_smul]]
  nlinarith [hR v, hS v, ha, hb]

theorem convex_ricPinch (n : ℕ) (p : ℝ) : Convex ℝ {R : Curv4 n | RicPinch p R} :=
  fun _ hR _ hS _ _ ha hb hab => ricPinch_convex' hR hS ha hb hab

theorem ricPinch_smul' {p c : ℝ} (hc : 0 ≤ c) {R : Curv4 n} (hR : RicPinch p R) :
    RicPinch p (c • R) := by
  rw [ricPinch_iff] at hR ⊢
  intro v
  rw [ricPinchFun_smul]
  nlinarith [hR v, hc]

/-! ## `Dpic p` -/

theorem isClosed_dpic (n : ℕ) (p : ℝ) : IsClosed (Dpic (n := n) p) := by
  have h : Dpic (n := n) p
      = ({R : Curv4 n | IsAlgCurv R} ∩ {R : Curv4 n | InPIC2 R}) ∩
        {R : Curv4 n | RicPinch p R} := by
    ext R; simp only [Dpic, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [h]
  exact (IsClosed.inter (isClosed_isAlgCurv n) (Cone.isClosed_inPIC2 n)).inter
    (isClosed_ricPinch n p)

theorem convex_dpic (n : ℕ) (p : ℝ) : Convex ℝ (Dpic (n := n) p) := by
  have h : Dpic (n := n) p
      = ({R : Curv4 n | IsAlgCurv R} ∩ {R : Curv4 n | InPIC2 R}) ∩
        {R : Curv4 n | RicPinch p R} := by
    ext R; simp only [Dpic, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [h]
  exact ((convex_isAlgCurv n).inter (Cone.convex_inPIC2 n)).inter (convex_ricPinch n p)

/-! ## The explicit inverse of the Böhm–Wilking transform -/

/-- The explicit inverse of `ell a b` on algebraic curvature tensors. -/
noncomputable def invEll (a b : ℝ) (Y : Curv4 n) : Curv4 n :=
  Y - (b / (1 + ((n : ℝ) - 2) * b)) • knProd (ric0 Y) (id2 n)
    - ((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg Y) • knProd (id2 n) (id2 n)

theorem continuous_ric0_apply (i j : Fin n) : Continuous fun R : Curv4 n => ric0 R i j := by
  simp only [ric0, ric, scalAlg, id2]; fun_prop

theorem continuous_invEll (a b : ℝ) : Continuous fun Y : Curv4 n => invEll a b Y := by
  rw [continuous_pi_iff]; intro i
  rw [continuous_pi_iff]; intro j
  rw [continuous_pi_iff]; intro k
  rw [continuous_pi_iff]; intro l
  simp only [invEll, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, knProd, ric0, ric, scalAlg, id2]
  fun_prop

theorem invEll_add (a b : ℝ) (Y Z : Curv4 n) :
    invEll a b (Y + Z) = invEll a b Y + invEll a b Z := by
  simp only [invEll, ric0_add, scalAlg_add, knProd_add_left]
  rw [smul_add, mul_add, add_smul]
  abel

theorem invEll_smul (a b c : ℝ) (Y : Curv4 n) :
    invEll a b (c • Y) = c • invEll a b Y := by
  simp only [invEll, ric0_smul, scalAlg_smul, knProd_smul_left]
  rw [smul_sub, smul_sub, smul_smul, smul_smul]
  module

/-- `invEll` is a left inverse of `ell` on algebraic curvature tensors. -/
theorem ell_invEll (n : ℕ) {a b : ℝ} (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((n : ℝ) - 2) * b ≠ 0) {Y : Curv4 n} (hY : IsAlgCurv Y) :
    ell a b (invEll a b Y) = Y :=
  ell_inv n ha hb hY

/-- `invEll` is a right inverse of `ell` on algebraic curvature tensors. -/
theorem invEll_ell (n : ℕ) {a b : ℝ} (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((n : ℝ) - 2) * b ≠ 0) {S : Curv4 n} (hS : IsAlgCurv S) :
    invEll a b (ell a b S) = S :=
  ell_injective a b ha hb (by rw [ell_invEll n ha hb (ell_isAlgCurv n a b hS)])

/-! ## `Ccone a b p` as the preimage of `Dpic p` -/

theorem ccone_eq (n : ℕ) (a b p : ℝ)
    (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0) (hb : 1 + ((n : ℝ) - 2) * b ≠ 0) :
    Ccone (n := n) a b p = {R : Curv4 n | IsAlgCurv R ∧ invEll a b R ∈ Dpic (n := n) p} := by
  ext R
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨ell_isAlgCurv n a b hS.1, by rw [invEll_ell n ha hb hS.1]; exact hS⟩
  · rintro ⟨hR, hT⟩
    exact ⟨invEll a b R, hT, ell_invEll n ha hb hR⟩

theorem isClosed_ccone (n : ℕ) (a b p : ℝ)
    (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0) (hb : 1 + ((n : ℝ) - 2) * b ≠ 0) :
    IsClosed (Ccone (n := n) a b p) := by
  rw [ccone_eq n a b p ha hb]
  exact (isClosed_isAlgCurv n).inter
    (IsClosed.preimage (continuous_invEll a b) (isClosed_dpic n p))

theorem convex_ccone (n : ℕ) (a b p : ℝ)
    (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0) (hb : 1 + ((n : ℝ) - 2) * b ≠ 0) :
    Convex ℝ (Ccone (n := n) a b p) := by
  intro R hR S hS u v hu hv huv
  rw [ccone_eq n a b p ha hb] at hR hS ⊢
  obtain ⟨h1, h2⟩ := hR
  obtain ⟨h3, h4⟩ := hS
  have hkey : invEll a b (u • R + v • S) = u • invEll a b R + v • invEll a b S := by
    rw [invEll_add, invEll_smul, invEll_smul]
  refine ⟨?_, ?_⟩
  · exact convex_isAlgCurv n h1 h3 hu hv huv
  · rw [hkey]; exact convex_dpic n p h2 h4 hu hv huv

theorem ccone_smul (n : ℕ) (a b p : ℝ) {c : ℝ} (hc : 0 ≤ c) {R : Curv4 n}
    (hR : R ∈ Ccone (n := n) a b p) : c • R ∈ Ccone (n := n) a b p := by
  obtain ⟨S, hS, rfl⟩ := hR
  exact ⟨c • S, ⟨isAlgCurv_smul c hS.1, Cone.inPIC2_smul hS.2.1 hc, ricPinch_smul' hc hS.2.2⟩,
    by rw [ell_smul]⟩


/-! ## `Chat n s` is a closed convex cone of algebraic curvature tensors -/

theorem mev_chat_isAlgCurv {s : ℝ} {R : Curv4 n} (hR : R ∈ Chat n s) : IsAlgCurv R := by
  rw [Chat] at hR
  split_ifs at hR with h
  · obtain ⟨S, hS, rfl⟩ := hR; exact ell_isAlgCurv n _ _ hS.1
  · obtain ⟨S, hS, rfl⟩ := hR; exact ell_isAlgCurv n _ _ hS.1

theorem chat_denom₁ (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) :
    1 + 2 * ((n : ℝ) - 1) * chatA n s ≠ 0 := by
  have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have ha : 0 ≤ chatA n s := chatA_nonneg hn hs.le
  nlinarith [ha, h1]

theorem chat_denom₂ (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) :
    1 + ((n : ℝ) - 2) * s ≠ 0 := by
  have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  nlinarith

theorem isClosed_chat {s : ℝ} (hn : 2 ≤ n) (hs : 0 < s) : IsClosed (Chat n s) := by
  rw [Chat]
  split_ifs with h
  · have ha : (0 : ℝ) ≤ (2 * s + ((n : ℝ) - 2) * s ^ 2) / (2 * (1 + ((n : ℝ) - 2) * s ^ 2)) := by
      rw [← chatA]; exact chatA_nonneg hn hs.le
    exact isClosed_ccone n _ s _ (by
      have h1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      nlinarith [ha, h1]) (chat_denom₂ n hn hs)
  · have hs' : 1 / 2 < s := not_le.mp h
    refine isClosed_ccone n s (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * s)) ?_ ?_
    · have h1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      nlinarith
    · have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
      nlinarith

theorem convex_chat {s : ℝ} (hn : 2 ≤ n) (hs : 0 < s) : Convex ℝ (Chat n s) := by
  rw [Chat]
  split_ifs with h
  · have ha : (0 : ℝ) ≤ (2 * s + ((n : ℝ) - 2) * s ^ 2) / (2 * (1 + ((n : ℝ) - 2) * s ^ 2)) := by
      rw [← chatA]; exact chatA_nonneg hn hs.le
    exact convex_ccone n _ s _ (by
      have h1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      nlinarith [ha, h1]) (chat_denom₂ n hn hs)
  · have hs' : 1 / 2 < s := not_le.mp h
    refine convex_ccone n s (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * s)) ?_ ?_
    · have h1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      nlinarith
    · have h2 : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
      nlinarith

theorem mev_chat_smul_mem {s c : ℝ} (hc : 0 ≤ c) {R : Curv4 n} (hR : R ∈ Chat n s) :
    c • R ∈ Chat n s := by
  rw [Chat] at hR ⊢
  split_ifs at hR ⊢ with h
  · exact ccone_smul n _ s _ hc hR
  · exact ccone_smul n s (1 / 2) _ hc hR

theorem iso_mem_chat (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) : Iso n ∈ Chat n s := by
  rw [Chat]
  split_ifs with h
  · have ha : (0 : ℝ) ≤ (2 * s + ((n : ℝ) - 2) * s ^ 2) / (2 * (1 + ((n : ℝ) - 2) * s ^ 2)) := by
      rw [← chatA]; exact chatA_nonneg hn hs.le
    have hden : 1 + 2 * ((n : ℝ) - 1) *
        ((2 * s + ((n : ℝ) - 2) * s ^ 2) / (2 * (1 + ((n : ℝ) - 2) * s ^ 2))) ≠ 0 := by
      rw [← chatA]; exact chat_denom₁ n hn hs
    have hp : 1 - 1 / (1 + ((n : ℝ) - 2) * s ^ 2) ≤ 1 := by
      have hd : 0 < 1 + ((n : ℝ) - 2) * s ^ 2 := by
        have := chat_c_nonneg hn; nlinarith [sq_nonneg s]
      have : 0 ≤ 1 / (1 + ((n : ℝ) - 2) * s ^ 2) := by positivity
      linarith
    have h1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hc : 0 < 1 / (1 + 2 * ((n : ℝ) - 1) *
        ((2 * s + ((n : ℝ) - 2) * s ^ 2) / (2 * (1 + ((n : ℝ) - 2) * s ^ 2)))) := by
      apply div_pos (by norm_num)
      nlinarith [ha, h1]
    refine ⟨(1 / (1 + 2 * ((n : ℝ) - 1) *
      ((2 * s + ((n : ℝ) - 2) * s ^ 2) / (2 * (1 + ((n : ℝ) - 2) * s ^ 2))))) • Iso n,
      ⟨isAlgCurv_smul _ (Iso_algCurv n),
       Cone.inPIC2_smul (Cone.inPIC2_iso n) hc.le,
       RicPinch_smul hc.le (ricPinch_iso n hp)⟩, ?_⟩
    rw [ell_smul, ell_iso, smul_smul]
    rw [show (1 + 2 * ((2 * s + ((n : ℝ) - 2) * s ^ 2) / (2 * (1 + ((n : ℝ) - 2) * s ^ 2))) *
          ((n : ℝ) - 1))
        = (1 + 2 * ((n : ℝ) - 1) *
          ((2 * s + ((n : ℝ) - 2) * s ^ 2) / (2 * (1 + ((n : ℝ) - 2) * s ^ 2)))) by ring]
    rw [one_div, inv_mul_cancel₀ hden, one_smul]
  · have hs' : 1 / 2 < s := not_le.mp h
    have hden : 1 + 2 * ((n : ℝ) - 1) * s ≠ 0 := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      nlinarith
    have hp : 1 - 4 / ((n : ℝ) - 2 + 8 * s) ≤ 1 := by
      have hd : 0 < (n : ℝ) - 2 + 8 * s := by
        have := chat_c_nonneg hn; linarith
      have : 0 ≤ 4 / ((n : ℝ) - 2 + 8 * s) := by positivity
      linarith
    have h1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hc : 0 < 1 / (1 + 2 * ((n : ℝ) - 1) * s) := by
      apply div_pos (by norm_num)
      nlinarith [hs, h1]
    refine ⟨(1 / (1 + 2 * ((n : ℝ) - 1) * s)) • Iso n,
      ⟨isAlgCurv_smul _ (Iso_algCurv n),
       Cone.inPIC2_smul (Cone.inPIC2_iso n) hc.le,
       RicPinch_smul hc.le (ricPinch_iso n hp)⟩, ?_⟩
    rw [ell_smul, ell_iso, smul_smul]
    rw [show (1 + 2 * s * ((n : ℝ) - 1)) = (1 + 2 * ((n : ℝ) - 1) * s) by ring]
    rw [one_div, inv_mul_cancel₀ hden, one_smul]

/-! ## The ODE invariance criterion (maximum principle) -/

lemma cbi_odeInv_one_add_mul_exp_neg_le_one (x : ℝ) : (1 + x) * Real.exp (-x) ≤ 1 := by
  have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have h2 : 0 < Real.exp x := Real.exp_pos x
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one h2]
  linarith

lemma cbi_odeInv_exp_neg_le_one {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ 1 := by
  rw [Real.exp_le_one_iff]; linarith

lemma cbi_odeInv_mul_sq_le_of_le_div {ε hh c : ℝ} (hc : 0 ≤ c) (_hε : 0 < ε) (hh0 : 0 < hh)
    (hhc : hh ≤ ε / (2 * (c + 1))) : c * hh ^ 2 ≤ (ε / 2) * hh := by
  have h2 : hh * (c + 1) ≤ ε / 2 := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * (c + 1))] at hhc
    linarith
  have h3 : c * hh ≤ ε / 2 := by nlinarith [h2, hc, hh0]
  nlinarith [h3, hh0]

lemma cbi_odeInv_combine_step {g T ρ hh L Qb ε : ℝ}
    (hAB : g ≤ T + ρ + (L * hh * ρ + ε / 2 * hh)) (hT : T ≤ L * Qb * hh ^ 2) :
    g ≤ ρ + L * hh * ρ + (ε / 2) * hh + L * Qb * hh ^ 2 := by linarith

/-- A single step of the weighted Gronwall comparison: if the distance `g` at time `t + hh` is
bounded by `(1 + L hh)` times the distance `ρ` at time `t`, plus the weighted error terms, and the
weight `A · e^{-L hh}` is at most `1`, then the weighted distance increases by at most `ε hh`. -/
lemma cbi_odeInv_weighted_step {g ρ A ε hh L Qb : ℝ} (hL0 : 0 ≤ L) (hQb0 : 0 ≤ Qb)
    (hρ0 : 0 ≤ ρ) (hA0 : 0 ≤ A) (hε : 0 < ε) (hh0 : 0 < hh)
    (hA1 : A * Real.exp (-(L * hh)) ≤ 1)
    (hstep : g ≤ ρ + L * hh * ρ + (ε / 2) * hh + L * Qb * hh ^ 2)
    (hhQ : hh ≤ ε / (2 * (L * Qb + 1))) :
    g * (A * Real.exp (-(L * hh))) ≤ ρ * A + ε * hh := by
  have hexp1 : (1 + L * hh) * Real.exp (-(L * hh)) ≤ 1 := cbi_odeInv_one_add_mul_exp_neg_le_one (L * hh)
  have hE0 : 0 ≤ Real.exp (-(L * hh)) := Real.exp_nonneg _
  have k2 : L * Qb * hh ^ 2 ≤ (ε / 2) * hh :=
    cbi_odeInv_mul_sq_le_of_le_div (mul_nonneg hL0 hQb0) hε hh0 hhQ
  have hnn : 0 ≤ (ε / 2) * hh + L * Qb * hh ^ 2 := by
    have h1 : 0 ≤ (ε / 2) * hh := mul_nonneg (by linarith) (le_of_lt hh0)
    have h2 : 0 ≤ L * Qb * hh ^ 2 := mul_nonneg (mul_nonneg hL0 hQb0) (sq_nonneg hh)
    linarith
  calc g * (A * Real.exp (-(L * hh)))
      ≤ (ρ + L * hh * ρ + (ε / 2) * hh + L * Qb * hh ^ 2) * (A * Real.exp (-(L * hh))) :=
        mul_le_mul_of_nonneg_right hstep (mul_nonneg hA0 hE0)
    _ = ρ * A * ((1 + L * hh) * Real.exp (-(L * hh)))
        + ((ε / 2) * hh + L * Qb * hh ^ 2) * (A * Real.exp (-(L * hh))) := by ring
    _ ≤ ρ * A * 1 + ((ε / 2) * hh + L * Qb * hh ^ 2) * 1 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hexp1 (mul_nonneg hρ0 hA0)
        · exact mul_le_mul_of_nonneg_left hA1 hnn
    _ ≤ ρ * A + ε * hh := by nlinarith [k2]

/-- One-step distance estimate: a feasible direction moves a point of `F` into a point at distance
`o(s)` from `F`. -/
theorem infDist_add_smul_le_of_feasible {n : ℕ} {F : Set (Curv4 n)} (hFcv : Convex ℝ F)
    (h : ∀ R ∈ F, Submission.Diff.Alg.Q R ∈ closure (feasibleCone F R))
    {x : Curv4 n} (hx : x ∈ F) (v : Curv4 n) :
    ∀ ε > 0, ∃ δ > 0, ∀ s : ℝ, 0 < s → s ≤ δ →
      Metric.infDist (x + s • v) F ≤ s * (‖v - Submission.Diff.Alg.Q x‖ + ε) := by
  intro ε hε
  obtain ⟨d, hd, hdist⟩ := Metric.mem_closure_iff.mp (h x hx) ε hε
  obtain ⟨δ, hδ, hb⟩ := infDist_le_of_mem_feasibleCone hFcv hx v hd
  refine ⟨δ, hδ, fun s hs hss => ?_⟩
  have hqd : ‖Submission.Diff.Alg.Q x - d‖ < ε := by
    simpa [dist_eq_norm] using hdist
  have h2 : ‖v - d‖ ≤ ‖v - Submission.Diff.Alg.Q x‖ + ε := by
    calc ‖v - d‖ = ‖(v - Submission.Diff.Alg.Q x) + (Submission.Diff.Alg.Q x - d)‖ := by
          congr 1; abel
      _ ≤ ‖v - Submission.Diff.Alg.Q x‖ + ‖Submission.Diff.Alg.Q x - d‖ := norm_add_le _ _
      _ ≤ ‖v - Submission.Diff.Alg.Q x‖ + ε := by linarith
  calc Metric.infDist (x + s • v) F ≤ s * ‖v - d‖ := hb s hs hss
    _ ≤ s * (‖v - Submission.Diff.Alg.Q x‖ + ε) := by
        have h0 : 0 ≤ ‖v - Submission.Diff.Alg.Q x‖ + ε := by positivity
        exact mul_le_mul_of_nonneg_left h2 hs.le

theorem odeInvariant_of_feasible (n : ℕ) {F : Set (Curv4 n)} (hFc : IsClosed F)
    (hFcv : Convex ℝ F)
    (h : ∀ R ∈ F, Submission.Diff.Alg.Q R ∈ closure (feasibleCone F R)) :
    ∀ (T : ℝ) (R : ℝ → Curv4 n), R 0 ∈ F →
      (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt R (Submission.Diff.Alg.Q (R t)) (Set.Ico 0 T) t) →
      ∀ t ∈ Set.Ico 0 T, R t ∈ F := by
  intro T R hR0 hder t ht
  obtain ⟨ht0, htT⟩ := ht
  have hFne : F.Nonempty := ⟨R 0, hR0⟩
  have hQcont : Continuous (Submission.Diff.Alg.Q (n := n)) := continuous_of_ball_lipschitz (fun M => Q_lipschitz_local n M)
  -- `R` is continuous on `[0,t]`.
  have hsub : Set.Icc (0:ℝ) t ⊆ Set.Ico (0:ℝ) T :=
    fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 htT⟩
  have hcontR : ContinuousOn R (Set.Icc (0:ℝ) t) :=
    fun s hs => (hder s (hsub hs)).continuousWithinAt.mono hsub
  have hcontg : ContinuousOn (fun s => Metric.infDist (R s) F) (Set.Icc (0:ℝ) t) :=
    (Metric.continuous_infDist_pt F).comp_continuousOn hcontR
  -- Bounds for the trajectory and for `Q ∘ R` on `[0,t]`.
  obtain ⟨s₀, -, hs₀max⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr ht0) hcontR.norm
  set Mb : ℝ := ‖R s₀‖ with hMbdef
  have hMb0 : 0 ≤ Mb := norm_nonneg _
  have hRle : ∀ s ∈ Set.Icc (0:ℝ) t, ‖R s‖ ≤ Mb := fun s hs => hs₀max hs
  set ρb : ℝ := Mb + ‖R 0‖ with hρbdef
  have hρb0 : 0 ≤ ρb := by rw [hρbdef]; positivity
  have hgle : ∀ s ∈ Set.Icc (0:ℝ) t, Metric.infDist (R s) F ≤ ρb := by
    intro s hs
    calc Metric.infDist (R s) F ≤ dist (R s) (R 0) := Metric.infDist_le_dist_of_mem hR0
      _ ≤ ‖R s‖ + ‖R 0‖ := dist_le_norm_add_norm _ _
      _ ≤ ρb := by rw [hρbdef]; linarith [hRle s hs]
  set M : ℝ := Mb + ρb + 1 with hMdef
  obtain ⟨C₀, hC₀⟩ := Q_lipschitz_local n M
  set L : ℝ := max C₀ 0 with hLdef
  have hL0 : 0 ≤ L := le_max_right _ _
  have hCL : ∀ p q : Curv4 n, ‖p‖ ≤ M → ‖q‖ ≤ M →
      ‖Submission.Diff.Alg.Q p - Submission.Diff.Alg.Q q‖ ≤ L * ‖p - q‖ := by
    intro p q hp hq
    exact (hC₀ p q hp hq).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hMbM : Mb ≤ M := by rw [hMdef]; linarith
  have hcontQR : ContinuousOn (fun s => Q (R s)) (Set.Icc (0:ℝ) t) :=
    hQcont.comp_continuousOn hcontR
  obtain ⟨s₁, -, hs₁max⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr ht0) hcontQR.norm
  set Qb : ℝ := ‖Q (R s₁)‖ with hQbdef
  have hQb0 : 0 ≤ Qb := norm_nonneg _
  have hQle : ∀ s ∈ Set.Icc (0:ℝ) t, ‖Q (R s)‖ ≤ Qb := fun s hs => hs₁max hs
  have hLQb0 : 0 ≤ L * Qb := mul_nonneg hL0 hQb0
  set φ : ℝ → ℝ := fun s => Metric.infDist (R s) F * Real.exp (-(L * s)) with hφdef
  have hcontφ : ContinuousOn φ (Set.Icc (0:ℝ) t) := by
    have h1 : Continuous fun s : ℝ => Real.exp (-(L * s)) := by
      apply Real.continuous_exp.comp
      fun_prop
    rw [hφdef]
    exact hcontg.mul h1.continuousOn
  -- The right Dini derivative of `φ` is `≤ 0`.
  have hDini : ∀ τ ∈ Set.Ico (0:ℝ) t, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ hh : ℝ, 0 < hh → hh ≤ δ →
      φ (τ + hh) ≤ φ τ + ε * hh := by
    intro τ hτ ε hε
    obtain ⟨hτ0, hτt⟩ := hτ
    set ρ : ℝ := Metric.infDist (R τ) F with hρdef
    set v : Curv4 n := Submission.Diff.Alg.Q (R τ) with hvdef
    -- a nearest point of `F` to `R τ`
    obtain ⟨x', hx'F, hx'e⟩ := IsClosed.exists_infDist_eq_dist hFc hFne (R τ)
    have hx' : ‖R τ - x'‖ = ρ := by rw [hρdef, hx'e, dist_eq_norm]
    have hRτM : ‖R τ‖ ≤ M := le_trans (hRle τ ⟨hτ0, le_of_lt hτt⟩) hMbM
    have hx'M : ‖x'‖ ≤ M := by
      have h1 : ‖x'‖ ≤ ‖R τ‖ + ‖R τ - x'‖ := by
        have hh2 := norm_sub_le (R τ) (R τ - x')
        rwa [sub_sub_self] at hh2
      rw [hx'] at h1
      have h2 : ρ ≤ ρb := hgle τ ⟨hτ0, le_of_lt hτt⟩
      linarith [h1, hRle τ ⟨hτ0, le_of_lt hτt⟩, h2, hMdef]
    have hQdiff : ‖v - Submission.Diff.Alg.Q x'‖ ≤ L * ρ := by
      have hh2 := hCL (R τ) x' hRτM hx'M
      rw [hx'] at hh2
      rwa [hvdef]
    -- the one-step tangent-cone estimate at `x'`
    obtain ⟨δ₁, hδ₁0, hδ₁⟩ :=
      infDist_add_smul_le_of_feasible hFcv h hx'F v (ε/2) (by linarith)
    let δ : ℝ := min (min (t - τ) δ₁) (ε / (2 * (L * Qb + 1)))
    have hδpos : 0 < δ := by
      simp only [δ]
      exact lt_min (lt_min (sub_pos.mpr hτt) hδ₁0) (div_pos hε (by linarith [hLQb0]))
    refine ⟨δ, hδpos, ?_⟩
    intro hh hh0 hhδ
    have hδa : δ ≤ min (t - τ) δ₁ := by simp only [δ]; exact min_le_left _ _
    have hδb : δ ≤ ε / (2 * (L * Qb + 1)) := by simp only [δ]; exact min_le_right _ _
    have hhδ₁ : hh ≤ δ₁ := le_trans (le_trans hhδ hδa) (min_le_right _ _)
    have hhtτ : hh ≤ t - τ := le_trans (le_trans hhδ hδa) (min_le_left _ _)
    have hhQ : hh ≤ ε / (2 * (L * Qb + 1)) := le_trans hhδ hδb
    have hτh : τ + hh ≤ t := by linarith
    have hhle : τ ≤ τ + hh := by linarith
    have hτh0 : 0 ≤ τ + hh := by linarith
    have hτhh : ∀ s ∈ Set.Icc τ (τ + hh), s ∈ Set.Icc (0:ℝ) t :=
      fun s hs => ⟨le_trans hτ0 hs.1, le_trans hs.2 hτh⟩
    -- `O(hh²)` Taylor remainder of the flow
    have htaylor : ‖R (τ + hh) - (R τ + hh • v)‖ ≤ L * Qb * hh ^ 2 := by
      have h1 : ∀ s ∈ Set.Icc τ (τ + hh),
          HasDerivWithinAt R (Submission.Diff.Alg.Q (R s)) (Set.Icc τ (τ + hh)) s := by
        intro s hs
        exact (hder s (hsub (hτhh s hs))).mono (fun u hu => hsub (hτhh u hu))
      have h2 : ∀ s ∈ Set.Icc τ (τ + hh), ‖Q (R s)‖ ≤ Qb := fun s hs => hQle s (hτhh s hs)
      have h3 : ∀ s ∈ Set.Icc τ (τ + hh), ‖Submission.Diff.Alg.Q (R s) - Submission.Diff.Alg.Q (R τ)‖ ≤ L * ‖R s - R τ‖ :=
        fun s hs => hCL (R s) (R τ) (le_trans (hRle s (hτhh s hs)) hMbM) hRτM
      have h4 := norm_sub_sub_smul_le R (Submission.Diff.Alg.Q (n := n)) (a := τ) (b := τ + hh) hhle hQb0 hL0 h1 h2 h3
      rwa [add_sub_cancel_left, ← hvdef, sub_sub] at h4
    have hkg : Metric.infDist (x' + hh • v) F ≤ hh * (L * ρ + ε/2) := by
      refine (hδ₁ hh hh0 hhδ₁).trans ?_
      have hh2 : ‖v - Submission.Diff.Alg.Q x'‖ + ε/2 ≤ L * ρ + ε/2 := by linarith [hQdiff]
      exact mul_le_mul_of_nonneg_left hh2 (le_of_lt hh0)
    have hA : Metric.infDist (R (τ + hh)) F ≤
        ‖R (τ + hh) - (R τ + hh • v)‖ + Metric.infDist (R τ + hh • v) F := by
      have hh2 := Metric.infDist_le_infDist_add_dist (x := R (τ + hh)) (y := R τ + hh • v) (s := F)
      rw [dist_eq_norm] at hh2
      linarith
    have hB : Metric.infDist (R τ + hh • v) F ≤ ρ + Metric.infDist (x' + hh • v) F := by
      have hh2 := Metric.infDist_le_infDist_add_dist (x := R τ + hh • v) (y := x' + hh • v) (s := F)
      rw [dist_eq_norm, add_sub_add_right_eq_sub, hx'] at hh2
      linarith
    have hAB : Metric.infDist (R (τ + hh)) F ≤
        ‖R (τ + hh) - (R τ + hh • v)‖ + ρ + hh * (L * ρ + ε/2) := by
      linarith [hA, hB, hkg]
    have hd : hh * (L * ρ + ε / 2) = L * hh * ρ + (ε / 2) * hh := by ring
    have hstep : Metric.infDist (R (τ + hh)) F ≤ ρ + L * hh * ρ + (ε/2) * hh + L * Qb * hh^2 := by
      rw [hd] at hAB
      exact cbi_odeInv_combine_step hAB htaylor
    have hexp : Real.exp (-(L * τ)) * Real.exp (-(L * hh)) = Real.exp (-(L * (τ + hh))) := by
      rw [← Real.exp_add]; congr 1; ring
    have hA1 : Real.exp (-(L * τ)) * Real.exp (-(L * hh)) ≤ 1 := by
      rw [hexp]
      exact cbi_odeInv_exp_neg_le_one (mul_nonneg hL0 hτh0)
    have hmain := cbi_odeInv_weighted_step (g := Metric.infDist (R (τ + hh)) F) (ρ := ρ)
      (A := Real.exp (-(L * τ))) (ε := ε) (hh := hh) (L := L) (Qb := Qb)
      hL0 hQb0 Metric.infDist_nonneg (le_of_lt (Real.exp_pos _)) hε hh0 hA1 hstep hhQ
    rw [hφdef]
    dsimp only
    rw [← hexp]
    simpa only [hρdef] using hmain
  -- comparison of the weighted distance
  have hfin : φ t ≤ φ 0 := le_of_dini_right φ ht0 hcontφ hDini
  have hgt : Metric.infDist (R t) F = 0 := by
    have hφ0 : φ 0 = 0 := by
      have h0 : Metric.infDist (R 0) F = 0 := by
        refine le_antisymm ?_ Metric.infDist_nonneg
        calc Metric.infDist (R 0) F ≤ dist (R 0) (R 0) := Metric.infDist_le_dist_of_mem hR0
          _ = 0 := dist_self _
      rw [hφdef]
      simp [h0]
    have hφt : 0 ≤ φ t := by
      rw [hφdef]; exact mul_nonneg Metric.infDist_nonneg (Real.exp_nonneg _)
    have h2 : Metric.infDist (R t) F * Real.exp (-(L * t)) = 0 := by
      have h3 : φ t = 0 := le_antisymm (hfin.trans_eq hφ0) hφt
      rw [hφdef] at h3
      exact h3
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd h3 (ne_of_gt (Real.exp_pos _))
  exact (IsClosed.mem_iff_infDist_zero hFc hFne).mpr hgt


/-- The maximum principle: a closed convex set in which `Q R` is always a feasible direction is
forward invariant under Hamilton's ODE. -/
theorem ODEInvariant_of_feasible (n : ℕ) {F : Set (Curv4 n)} (hFc : IsClosed F)
    (hFcv : Convex ℝ F)
    (h : ∀ R ∈ F, Submission.Diff.Alg.Q R ∈ closure (feasibleCone F R)) :
    Submission.Diff.Alg.ODEInvariant F :=
  odeInvariant_of_feasible n hFc hFcv h

/-! ## Rotation invariance bookkeeping

Two elementary facts about the `O(n)`-action `rot` on curvature arrays that the construction of an
`O(n)`-invariant set needs: `rot` is linear in the tensor, and it fixes the round sphere. -/

theorem rot_add (A : Matrix (Fin n) (Fin n) ℝ) (R S : Curv4 n) :
    rot A (R + S) = rot A R + rot A S := by
  ext i j k l
  simp only [rot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem rot_smul (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (R : Curv4 n) :
    rot A (c • R) = c • rot A R := by
  ext i j k l
  simp only [rot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro c' _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro d _
  ring


/-!
## Status and the assembly plan (corrected, for the next stretch of work)

### What is proved

*In this file* (all sorry-free): `isClosed_isAlgCurv`, `convex_isAlgCurv`, the `ricPinchFun`
linear-functional kit (`ricPinchFun_add`, `ricPinchFun_smul`, `ricPinch_iff`,
`continuous_scalAlg`, `continuous_ric_apply`, `isClosed_ricPinch`, `convex_ricPinch`,
`ricPinch_convex'`, `ricPinch_smul'`), `isClosed_dpic`, `convex_dpic`, the explicit inverse
`invEll` and its calculus (`invEll_add`, `invEll_smul`, `ell_invEll`, `invEll_ell`),
`ccone_eq`, `isClosed_ccone`, `convex_ccone`, `ccone_smul`, `mev_chat_isAlgCurv`, `chat_denom₁/₂`,
`isClosed_chat`, `convex_chat`, `mev_chat_smul_mem`, `iso_mem_chat`, the maximum principle
`infDist_add_smul_le_of_feasible` + `odeInvariant_of_feasible` / `ODEInvariant_of_feasible`
(closed + convex + every `Q R` feasible ⟹ `ODEInvariant`), `rot_add`, `rot_smul`, and the
`O(n)`-equivariance batch `rot2_id2`, `ric0_rot`, `rot_Iso_orth`, `rot_transpose_rot`,
`transpose_mem_orthogonalGroup`, `ell_rot`.

*Elsewhere, import freely*: `Work.Diff.Alg.Pinch.Chat_transversal` (BS Props 13/14: for
`X ∈ Chat n s`, `X ≠ 0` there is `h > 0` with `X + t • Q X ∈ ChatS n s` for `0 < t ≤ h`) —
**proved, sorry-free**; `Work.Diff.Alg.Pinch.Chat_ray_thin` (proved);
`Work.Diff.Alg.Pinch.Chat_margin` (proved).  In flight: `Chat_shifted_transversal` (BS Prop 16,
the shifted one-step with the `scalAlg` cutoff).

⚠️ **Import clash (workspace-wide).** `Ccone_transversal_a_aux` and `Ccone_transversal_b`
(introduced transitively by `Chat_transversal`) both declare `ric_zero`, and
`Ccone_transversal_a_aux` and `linv_Q_ell` both declare `ric_ell`.  Consequently **no module may
import `Chat_transversal` together with `Ccone_transversal_a_aux`** (nor `Chat_margin`,

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
`Chat_ray_thin`, `Chat_shifted_transversal`, which pull `_a_aux`).  This file currently imports
`Ccone_transversal_a_aux` (for the basic algebra lemmas `ric_add`, `scalAlg_add`, `ell_smul`,
`Iso_algCurv`, `ell_injective`, `RicPinch_smul`, …) and therefore CANNOT yet import
`Chat_transversal`.  Someone must rename one of the duplicate declarations before the two halves
can be used together; alternatively the basic lemmas have to be re-proved locally (they are all
elementary; `Linv.lean` already has `ric_add_linv`, `scalAlg_add_linv`, `ric_smul_linv`,
`scalAlg_smul_linv`, `ric0_add'`, `ric0_smul'`, `knProd_add_left_linv`, `knProd_smul_left_linv`).

### The assembly (this IS Böhm–Wilking Theorem 4.1, i.e. BS Prop. 17)

`Chat n s` is ODE-invariant for every `s > 0`: by `Chat_transversal` (one step into `ChatS ⊆ Chat`)
and `ODEInvariant_of_feasible`.  Hence `Chat n ε` is an admissible set below, and the clean
route is BW's "minimal set":

* `F := ⋂ {F' | IsClosed F' ∧ Convex ℝ F' ∧ (∀ R ∈ F', IsAlgCurv R) ∧ O(n)-invariant ∧
  ODEInvariant F' ∧ K ⊆ F'}` with `K := Chat n ε ∩ {scalAlg R ≤ h₀}`.
  Closed, convex, algebraic, `O(n)`-invariant, `K ⊆ F`, and `ODEInvariant` hold BY CONSTRUCTION
  (`Set.univ` shows the family is non-empty; `{IsAlgCurv}` and `Chat n ε` are test sets).  This is
  the whole of the target except the boundedness, and it needs no analysis.
* The boundedness `F ∖ Chat n s` bounded (`s ≥ ε`) is the only hard part; it is BW's `s₀`
  argument.  **Warning:** the naive route is FALSE.  Two reviewers verified with a rational
  counterexample (`n = 6`, `s = 3/10`, `X = ell (6/17) (3/10) CERm0` with `CERm0` Ricci-tight,
  shift `c = 1`) that the *un-truncated* translate `{R | R + c • Iso ∈ Chat n s}` is NOT
  ODE-invariant; `Chat_shifted_transversal`'s cutoff `N ≤ scalAlg X` is essential.  (The failure
  is exactly the `-2c·B(X, Iso)` perturbation of the direction, which pushes the traceless-Ricci
  part through the `RicPinch` boundary; the cutoff keeps `c / scalAlg (R + c • Iso)` below the
  room of the normalized slice.)
* So the boundedness must use the truncated translate
  `TC(s,c,h̄) := {R | R + c • Iso n ∈ Chat n s ∧ h̄ ≤ scalAlg R}`,
  which IS ODE-invariant for `h̄ ≥ N(s,c) - c·n(n-1)` (from `Chat_shifted_transversal`, since
  `scalAlg (R + c • Iso) ≥ h̄ + c·n(n-1)`), together with the trace-monotonicity
  `scalAlg (Q R) ≥ 0` (`scalAlg_Q`: `scalAlg (Q R) = 2 ∑ (ric R)ᵢⱼ²`).  `K ∋ 0` meets no cutoff,
  which is why a bare minimality argument on `TC` cannot work and one needs either BW's
  "`F' = (F ∩ {scal ≤ kh̄}) ∪ (F ∩ k·TC)` is convex + invariant, hence `= F`" or the
  Brendle–Schoen Prop. 16 first-exit-time induction over a sequence `s_j → ∞`.
* The boundedness conclusion then follows from `Chat_ray_thin`: if `R ∈ F ∖ Chat n s` then
  `\hat R := R / scalAlg R ∈ Chat n ε` with `scalAlg \hat R = 1` and `\hat R ∉ Chat n s`, and
  `dist(\hat R, Chat n s) ≥ δ(s) > 0` by compactness of the normalized slice; the constraint
  `\hat R + (c/scalAlg R) • Iso ∈ Chat n s` then gives `scalAlg R ≤ c‖Iso‖/δ(s)`.
-/
/-! ## The translate of a cone, and the assembly of the pinching set

Notation: `C s := Chat n s`, `I := Iso n`, `σ := scalAlg`, and `T (s,c) := {R | R + c • I ∈ C s}`.

The assembly below is the Böhm–Wilking / Brendle–Schoen pinching-set construction.  It rests on
the following analytic inputs, all of which are proved (or being proved) elsewhere in the
workspace:

* `hroom` — the *robust shifted transversality* (BS Props. 13/14 plus the scaling step of
  Prop. 16), with a threshold constant `K` that is uniform in `s ≥ ε`;
* `hinc` — the *shift inclusion* (BS Prop. 16(i)) with the level `2K+2` and the increment `δ`,
  again uniform in `s ≥ ε`;
* `hbase` — `ODEInvariant (Chat n ε)`, the base invariance; proved *in this file* as
  `chat_odeInvariant_of_room` (from the room lemma alone, by a limiting argument);
* `hmono`, `hray`, `hslice`, `hmargin` — the structural facts used in the boundedness argument.

The set is `F := ⋂ j, F j` with `F 0 = C ε` and
`F (j+1) = F j ∩ T (ε + (j+1) δ, 2^{j+1} c₀)`, where `c₀ = max 1 h₀`.  Each `F j` is closed,
convex, `O(n)`-invariant, consists of algebraic curvature tensors, contains
`K = C ε ∩ {σ ≤ h₀}` and is `ODEInvariant`; the inductive step is the first-exit-time argument
of BS Prop. 16.  Since `ε + j δ → ∞`, the boundedness of `F ∖ C s` follows from `hslice`,
`hmono` and `hray` exactly as in the proof of BW Theorem 4.1. -/

/-- The translate `{R | R + c • Iso n ∈ Chat n s}` of the pinching cone `Chat n s`. -/
def transSet (s c : ℝ) : Set (Curv4 n) := {R : Curv4 n | R + c • Iso n ∈ Chat n s}

theorem isClosed_transSet (n : ℕ) (hn : 2 ≤ n) {s c : ℝ} (hs : 0 < s) :
    IsClosed (transSet (n := n) s c) := by
  have hcont : Continuous fun R : Curv4 n => R + c • Iso n := continuous_id.add continuous_const
  exact (isClosed_chat (n := n) hn hs).preimage hcont

theorem convex_transSet (n : ℕ) (hn : 2 ≤ n) {s c : ℝ} (hs : 0 < s) :
    Convex ℝ (transSet (n := n) s c) := by
  intro R hR S hS a b ha hb hab
  have h1 : a • (R + c • Iso n) + b • (S + c • Iso n) ∈ Chat n s :=
    convex_chat hn hs hR hS ha hb hab
  have h2 : a • (R + c • Iso n) + b • (S + c • Iso n) = (a • R + b • S) + c • Iso n := by
    have key : c • Iso n = a • (c • Iso n) + b • (c • Iso n) := by
      rw [← add_smul, hab, one_smul]
    conv_rhs => rw [key]
    rw [smul_add, smul_add]
    abel
  rw [h2] at h1
  exact h1

theorem transSet_isAlgCurv {s c : ℝ} {R : Curv4 n} (hR : R ∈ transSet s c) : IsAlgCurv R := by
  have h1 : IsAlgCurv (R + c • Iso n) := mev_chat_isAlgCurv hR
  have h2 : IsAlgCurv (c • Iso n) := isAlgCurv_smul c (Iso_algCurv n)
  have h3 : R = (R + c • Iso n) - c • Iso n := by abel
  rw [h3]
  exact isAlgCurv_sub h1 h2

/-- `0 ∈ Chat n s`. -/
theorem zero_mem_chat (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) : (0 : Curv4 n) ∈ Chat n s := by
  have h := mev_chat_smul_mem (s := s) (c := 0) (le_refl 0) (iso_mem_chat n hn hs)
  simpa using h

/-- `Chat n s` is closed under addition. -/
theorem chat_add_mem {s : ℝ} (hn : 2 ≤ n) (hs : 0 < s) {R S : Curv4 n}
    (hR : R ∈ Chat n s) (hS : S ∈ Chat n s) : R + S ∈ Chat n s := by
  have h := convex_chat hn hs (x := R) (y := S) hR hS (a := 1 / 2) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  have h2 : (2 : ℝ) • ((1 / 2 : ℝ) • R + (1 / 2 : ℝ) • S) = R + S := by module
  rw [← h2]
  exact mev_chat_smul_mem (by norm_num) h

/-- Adding a nonnegative multiple of the round sphere preserves `Chat n s`. -/
theorem chat_add_smul_Iso_mem {s : ℝ} (hn : 2 ≤ n) (hs : 0 < s) {R : Curv4 n}
    (hR : R ∈ Chat n s) {c : ℝ} (hc : 0 ≤ c) : R + c • Iso n ∈ Chat n s := by
  refine chat_add_mem hn hs hR ?_
  have h2 : c • Iso n ∈ Chat n s :=
    mev_chat_smul_mem (s := s) (c := c) hc (iso_mem_chat n hn hs)
  exact h2

/-! ### The base invariance of `Chat n ε`

`Chat n ε` is forward invariant under Hamilton's ODE.  The room lemma `Chat_room_global` is applied
at the shifted points `X - c • Iso n` (the shift being allowed since `X = (X - c • Iso n) + c • Iso n`
lies in the cone): for `X ∈ Chat n ε` and every small `c > 0` it produces `h > 0` with

`X + h • Q (X - c • Iso n) ∈ Chat n ε`,

i.e. `Q (X - c • Iso n)` is a *feasible direction* of `Chat n ε` at `X`.  Letting `c → 0⁺` gives
`Q X ∈ closure (feasibleCone (Chat n ε) X)` -- the limit is needed because the shifted statement
alone cannot be un-shifted -- and the maximum principle `ODEInvariant_of_feasible` concludes. -/

/-- **Base invariance**: Hamilton's ODE leaves the cone `Ĉ(ε) = Chat n ε` forward invariant for
every `ε > 0`. -/
theorem chat_odeInvariant_of_room (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ODEInvariant (Chat n ε) := by
  obtain ⟨K, hK, hroom⟩ := Chat_room_global n hn ε hε
  obtain ⟨⟨C, hCpos, hC⟩, -, -⟩ := Chat_family_structure n hn ε hε
  have hQcont : Continuous (Q (n := n)) :=
    continuous_of_ball_lipschitz (fun M => Q_lipschitz_local n M)
  have hσnn : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    nlinarith
  refine ODEInvariant_of_feasible n (isClosed_chat hn hε) (convex_chat hn hε) (fun X hX => ?_)
  by_cases hX0 : X = 0
  · subst hX0
    rw [Q_zero]
    exact subset_closure (zero_mem_feasibleCone (zero_mem_chat n hn hε))
  · -- `scalAlg` is positive on the nonzero part of the cone
    have hσX0 : 0 ≤ scalAlg X := by
      by_contra hcon
      push Not at hcon
      have h1 := hC X hX
      nlinarith [norm_nonneg X]
    have hσpos : 0 < scalAlg X := by
      rcases lt_or_eq_of_le hσX0 with h | h
      · exact h
      · exfalso
        have h1 := hC X hX
        rw [← h] at h1
        simp only [mul_zero] at h1
        exact hX0 (norm_eq_zero.mp (le_antisymm h1 (norm_nonneg X)))
    -- the scale of the shifts
    set c₀ : ℝ := scalAlg X / (2 * (K + (n : ℝ) * ((n : ℝ) - 1) + 1)) with hc0
    have hden : (0 : ℝ) < K + (n : ℝ) * ((n : ℝ) - 1) + 1 := by linarith
    have hc0pos : 0 < c₀ := by
      rw [hc0]
      exact div_pos hσpos (by linarith)
    have hc₀key : c₀ * (2 * (K + (n : ℝ) * ((n : ℝ) - 1) + 1)) = scalAlg X := by
      rw [hc0]
      exact div_mul_cancel₀ _ (ne_of_gt (by linarith : (0 : ℝ) < 2 * (K + (n : ℝ) * ((n : ℝ) - 1) + 1)))
    set c : ℕ → ℝ := fun m => c₀ / ((m : ℝ) + 1) with hc
    have hcpos : ∀ m : ℕ, 0 < c m := fun m => by
      rw [hc]
      exact div_pos hc0pos (by positivity)
    -- `c m` is small enough for the room
    have hcm_bound : ∀ m : ℕ, c m * (2 * (K + (n : ℝ) * ((n : ℝ) - 1) + 1)) ≤ scalAlg X := by
      intro m
      rw [hc, div_mul_eq_mul_div, hc₀key]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
      have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      exact le_mul_of_one_le_right hσpos.le hm1
    have hKc : ∀ m : ℕ, K * c m ≤ scalAlg (X - c m • Iso n) := by
      intro m
      have hb := hcm_bound m
      have hscal : scalAlg (X - c m • Iso n)
          = scalAlg X - c m * ((n : ℝ) * ((n : ℝ) - 1)) := by
        rw [scalAlg_sub, scalAlg_smul, scalAlg_iso]
      rw [hscal]
      nlinarith [hb, hcpos m, hσnn]
    -- the room turns the shifts into feasible directions
    have hfeas : ∀ m : ℕ, Q (X - c m • Iso n) ∈ feasibleCone (Chat n ε) X := by
      intro m
      have hcm : 0 < c m := hcpos m
      have hRmem : (X - c m • Iso n) + c m • Iso n ∈ Chat n ε := by
        rw [sub_add_cancel]
        exact hX
      have halg : IsAlgCurv (X - c m • Iso n) :=
        isAlgCurv_sub (mev_chat_isAlgCurv hX) (isAlgCurv_smul _ (Iso_algCurv n))
      obtain ⟨h, hh, ρ, hρ, hroom'⟩ :=
        hroom ε le_rfl (X - c m • Iso n) (c m) hcm hRmem (hKc m)
      refine ⟨h, hh, ?_⟩
      have hkey := hroom' h hh le_rfl (Q (X - c m • Iso n)) (Q_isAlgCurv n halg)
        (by simp [hρ.le])
      have heq : (X - c m • Iso n) + h • Q (X - c m • Iso n) + c m • Iso n
          = X + h • Q (X - c m • Iso n) := by abel
      rwa [heq] at hkey
    -- the limit `c → 0⁺`
    have hcm : Filter.Tendsto c Filter.atTop (nhds 0) := by
      rw [hc]
      exact tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hlim : Filter.Tendsto (Q ∘ fun m : ℕ => X - c m • Iso n) Filter.atTop (nhds (Q X)) := by
      have h1 : Filter.Tendsto (fun m : ℕ => X - c m • Iso n) Filter.atTop
          (nhds (X - (0 : ℝ) • Iso n)) :=
        tendsto_const_nhds.sub (hcm.smul_const (Iso n))
      have h2 := (hQcont.tendsto (X - (0 : ℝ) • Iso n)).comp h1
      rwa [zero_smul, sub_zero] at h2
    exact mem_closure_of_tendsto hlim (Filter.Eventually.of_forall hfeas)

/-! ### The inductive step: Brendle–Schoen Prop. 16

If `F` is ODE-invariant, consists of algebraic curvature tensors and satisfies the *previous*
translate condition `R + c₀ • Iso ∈ C s₀` for all `R ∈ F`, then
`F ∩ T (s₀ + δ, 2 c₀)` is ODE-invariant, provided the robust shifted transversality at `s₀ + δ`
(with threshold constant `K`) and the shift inclusion at `(s₀, 2K+2, δ)` hold. -/
theorem odeInvariant_shift_step (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hroom : ∀ s : ℝ, ε ≤ s → ∀ R : Curv4 n, ∀ c : ℝ, 0 < c →
      R + c • Iso n ∈ Chat n s → K * c ≤ scalAlg R →
      ∃ h : ℝ, 0 < h ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, 0 < t → t ≤ h → ∀ v : Curv4 n,
        IsAlgCurv v → ‖v - Q R‖ ≤ ρ → R + t • v + c • Iso n ∈ Chat n s)
    (hinc : ∀ s : ℝ, ε ≤ s → ∀ c : ℝ, 0 < c → ∀ R : Curv4 n,
      R + c • Iso n ∈ Chat n s → scalAlg R ≤ (2 * K + 2) * c →
      R + (2 * c) • Iso n ∈ Chat n (s + δ))
    {F : Set (Curv4 n)} (hFinv : ODEInvariant F) (hFalg : ∀ R ∈ F, IsAlgCurv R)
    (s₀ c₀ : ℝ) (hs₀ : ε ≤ s₀) (hc₀ : 0 < c₀)
    (hprev : ∀ R ∈ F, R + c₀ • Iso n ∈ Chat n s₀) :
    ODEInvariant (F ∩ transSet (s₀ + δ) (2 * c₀)) := by
  intro T R hR0 hder t ht
  have ht' : t ∈ Set.Ico (0 : ℝ) T := ht
  obtain ⟨ht0, htT⟩ := ht
  have hFt : R t ∈ F := hFinv T R hR0.1 hder t ht'
  refine ⟨hFt, ?_⟩
  have hc₀' : (0 : ℝ) < 2 * c₀ := by linarith
  have hsd : 0 < s₀ + δ := by linarith
  have hcontR : ∀ u ∈ Set.Ico (0 : ℝ) T, ContinuousWithinAt R (Set.Ico (0 : ℝ) T) u :=
    fun u hu => (hder u hu).continuousWithinAt
  have hmain : ∀ u ∈ Set.Ico (0 : ℝ) T, R u + (2 * c₀) • Iso n ∈ Chat n (s₀ + δ) := by
    intro u hu
    obtain ⟨hu0, huT⟩ := hu
    set B : Set ℝ := {v : ℝ | 0 ≤ v ∧ v ≤ u ∧ ∀ w : ℝ, w ∈ Set.Ico (0 : ℝ) T → w ≤ v →
      R w + (2 * c₀) • Iso n ∈ Chat n (s₀ + δ)} with hBdef
    have hB0 : (0 : ℝ) ∈ B := by
      refine ⟨le_refl 0, hu0, fun w hw hw0 => ?_⟩
      have hw0' : w = 0 := le_antisymm hw0 hw.1
      subst hw0'
      simpa only [transSet, Set.mem_setOf_eq] using hR0.2
    have hB_ne : B.Nonempty := ⟨0, hB0⟩
    have hB_bdd : BddAbove B := ⟨u, fun v hv => hv.2.1⟩
    have hstep : ∀ v ∈ B, v < u → ∃ d : ℝ, 0 < d ∧
        ∀ w : ℝ, w ∈ Set.Ico (0 : ℝ) T → v < w → w < v + d →
          R w + (2 * c₀) • Iso n ∈ Chat n (s₀ + δ) := by
      intro v hvB hvu
      have hv0 : 0 ≤ v := hvB.1
      have hvT : v < T := lt_of_le_of_lt hvB.2.1 huT
      have hvI : v ∈ Set.Ico (0 : ℝ) T := ⟨hv0, hvT⟩
      have hvp : R v + (2 * c₀) • Iso n ∈ Chat n (s₀ + δ) := hvB.2.2 v hvI le_rfl
      have hRvF : R v ∈ F := hFinv T R hR0.1 hder v hvI
      have hvcont : ContinuousWithinAt R (Set.Ico (0 : ℝ) T) v := hcontR v hvI
      by_cases hcase : K * (2 * c₀) ≤ scalAlg (R v)
      · obtain ⟨h, hh, ρ, hρ, hroom'⟩ :=
          hroom (s₀ + δ) (by linarith) (R v) (2 * c₀) hc₀' hvp hcase
        have hslope : Filter.Tendsto (slope R v) (nhdsWithin v (Set.Ico (0 : ℝ) T \ {v}))
            (nhds (Q (R v))) :=
          (hasDerivWithinAt_iff_tendsto_slope).mp (hder v hvI)
        obtain ⟨d₁, hd₁, hd₁'⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hslope) ρ hρ
        refine ⟨min d₁ h, lt_min hd₁ hh, fun w hw hvw hwv => ?_⟩
        have hwne : w ≠ v := ne_of_gt hvw
        have hmem : w ∈ Set.Ico (0 : ℝ) T \ {v} := ⟨hw, by simpa using hwne⟩
        have hwmin : w - v < min d₁ h := by linarith
        have hdist : dist w v < d₁ := by
          rw [Real.dist_eq, abs_of_pos (by linarith : (0 : ℝ) < w - v)]
          linarith [min_le_left d₁ h]
        have hsl := hd₁' hmem hdist
        rw [dist_eq_norm] at hsl
        have hwt : w - v ≤ h := by linarith [min_le_right d₁ h]
        have halg : IsAlgCurv (slope R v w) := by
          have h1 : IsAlgCurv (R w) := hFalg (R w) (hFinv T R hR0.1 hder w hw)
          have h2 : IsAlgCurv (R v) := hFalg (R v) hRvF
          have h3 : slope R v w = (w - v)⁻¹ • (R w - R v) := rfl
          rw [h3]
          exact isAlgCurv_smul _ (isAlgCurv_sub h1 h2)
        have hkey := hroom' (w - v) (by linarith) hwt (slope R v w) halg (le_of_lt hsl)
        have hid : R v + (w - v) • slope R v w + (2 * c₀) • Iso n
            = R w + (2 * c₀) • Iso n := by
          have h1 : (w - v) • slope R v w = R w - R v := by
            rw [show slope R v w = (w - v)⁻¹ • (R w - R v) from rfl,
              smul_inv_smul₀ (sub_ne_zero.mpr hwne)]
          rw [h1]; abel
        rwa [hid] at hkey
      · push Not at hcase
        have hbound : scalAlg (R v) < (2 * K + 2) * c₀ := by
          have h1 : K * (2 * c₀) = (2 * K) * c₀ := by ring
          rw [h1] at hcase
          nlinarith [hc₀]
        have hcontscal : ContinuousWithinAt (fun w : ℝ => scalAlg (R w)) (Set.Ico (0 : ℝ) T) v :=
          (continuous_scalAlg.continuousWithinAt (s := Set.univ)).comp (x := v) hvcont
            (fun w _ => trivial)
        obtain ⟨d₂, hd₂, hd₂'⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hcontscal.tendsto)
          ((2 * K + 2) * c₀ - scalAlg (R v)) (by linarith)
        refine ⟨d₂, hd₂, fun w hw hvw hwv => ?_⟩
        have hwne : w ≠ v := ne_of_gt hvw
        have hmem : w ∈ Set.Ico (0 : ℝ) T \ {v} := ⟨hw, by simpa using hwne⟩
        have hdist : dist w v < d₂ := by
          rw [Real.dist_eq, abs_of_pos (by linarith : (0 : ℝ) < w - v)]
          linarith
        have hsc := hd₂' hw hdist
        rw [Real.dist_eq, abs_lt] at hsc
        have hle : scalAlg (R w) ≤ (2 * K + 2) * c₀ := by linarith [hsc.2]
        have hmemF : R w ∈ F := hFinv T R hR0.1 hder w hw
        exact hinc s₀ hs₀ c₀ hc₀ (R w) (hprev (R w) hmemF) hle
    have hτ0 : 0 ≤ sSup B := le_csSup hB_bdd hB0
    have hτle : sSup B ≤ u := csSup_le hB_ne (fun v hv => hv.2.1)
    have hbelow : ∀ w : ℝ, w ∈ Set.Ico (0 : ℝ) T → w < sSup B →
        R w + (2 * c₀) • Iso n ∈ Chat n (s₀ + δ) := by
      intro w hw hwτ
      obtain ⟨v, hvB, hwv⟩ := exists_lt_of_lt_csSup hB_ne hwτ
      exact hvB.2.2 w hw (le_of_lt hwv)
    have hτmem : R (sSup B) + (2 * c₀) • Iso n ∈ Chat n (s₀ + δ) := by
      have hseq : ∀ k : ℕ, ∃ v : ℝ, v ∈ B ∧ sSup B - 1 / ((k : ℝ) + 1) < v := by
        intro k
        have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        obtain ⟨v, hvB, hv⟩ :=
          exists_lt_of_lt_csSup hB_ne (show sSup B - 1 / ((k : ℝ) + 1) < sSup B by linarith)
        exact ⟨v, hvB, hv⟩
      choose v hvB hvlt using hseq
      have hvle : ∀ k, v k ≤ u := fun k => (hvB k).2.1
      have hvsup : ∀ k, v k ≤ sSup B := fun k => le_csSup hB_bdd (hvB k)
      have hvI : ∀ k, v k ∈ Set.Ico (0 : ℝ) T :=
        fun k => ⟨(hvB k).1, lt_of_le_of_lt (hvle k) huT⟩
      have hvtend : Filter.Tendsto v Filter.atTop (nhds (sSup B)) := by
        rw [Metric.tendsto_atTop]
        intro e he
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt he
        refine ⟨k, fun m hm => ?_⟩
        have h1 : 1 / ((m : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.succ_le_succ hm
        have h2 := hvlt m
        have h3 := hvsup m
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith
      have hvI' : Filter.Tendsto v Filter.atTop (nhdsWithin (sSup B) (Set.Ico (0 : ℝ) T)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hvtend, Filter.Eventually.of_forall hvI⟩
      have hτI : sSup B ∈ Set.Ico (0 : ℝ) T := ⟨hτ0, lt_of_le_of_lt hτle huT⟩
      have hcontW : ContinuousWithinAt (fun x : ℝ => R x + (2 * c₀) • Iso n)
          (Set.Ico (0 : ℝ) T) (sSup B) := (hcontR (sSup B) hτI).add continuousWithinAt_const
      have htendW : Filter.Tendsto (fun k => R (v k) + (2 * c₀) • Iso n) Filter.atTop
          (nhds (R (sSup B) + (2 * c₀) • Iso n)) := hcontW.tendsto.comp hvI'
      refine (isClosed_chat hn hsd).mem_of_tendsto htendW ?_
      exact Filter.Eventually.of_forall (fun k => (hvB k).2.2 (v k) (hvI k) le_rfl)
    have hτB : sSup B ∈ B := ⟨hτ0, hτle, fun w hw hwτ =>
      (lt_or_eq_of_le hwτ).elim (fun h => hbelow w hw h) (fun h => h ▸ hτmem)⟩
    have hτu : sSup B = u := by
      by_contra hne
      have hlt : sSup B < u := lt_of_le_of_ne hτle hne
      obtain ⟨d, hd, hd'⟩ := hstep (sSup B) hτB hlt
      have he0 : 0 < min d (u - sSup B) := lt_min hd (by linarith)
      have he0' : 0 ≤ sSup B + min d (u - sSup B) / 2 := by
        have h := le_of_lt he0; linarith
      have heu : sSup B + min d (u - sSup B) / 2 ≤ u := by
        have h := min_le_right d (u - sSup B); linarith
      have hvB' : (sSup B + min d (u - sSup B) / 2) ∈ B := by
        refine ⟨he0', heu, fun w hw hwv => ?_⟩
        rcases lt_trichotomy w (sSup B) with h | h | h
        · exact hbelow w hw h
        · rw [h]; exact hτmem
        · have h1 : min d (u - sSup B) / 2 < d := by
            have h2 := min_le_left d (u - sSup B)
            have h3 := le_of_lt he0
            linarith
          exact hd' w hw h (by linarith)
      have := le_csSup hB_bdd hvB'
      linarith [he0]
    rw [hτu] at hτmem
    exact hτmem
  exact hmain t ht'

/-! ### The construction: `F j = C ε ∩ ⋂_{i<j} T (ε + i δ, 2^i c₀)` -/

/-- The shift sequence `2^j c₀`, `c₀ = max 1 h₀`. -/
noncomputable def cand (h₀ : ℝ) (j : ℕ) : ℝ := (2 : ℝ) ^ j * max 1 h₀

/-- The cone-parameter sequence `ε + j δ`. -/
noncomputable def sand (ε δ : ℝ) (j : ℕ) : ℝ := ε + (j : ℝ) * δ

/-- The decreasing sequence of translates whose intersection is the pinching set. -/
noncomputable def Fgen (ε h₀ δ : ℝ) : ℕ → Set (Curv4 n)
  | 0 => Chat n ε
  | (j + 1) => Fgen ε h₀ δ j ∩ transSet (sand ε δ (j + 1)) (cand h₀ (j + 1))

theorem cand_pos (h₀ : ℝ) (j : ℕ) : 0 < cand h₀ j := by
  rw [cand]
  exact mul_pos (pow_pos (by norm_num) j) (lt_of_lt_of_le one_pos (le_max_left 1 h₀))

theorem cand_succ (h₀ : ℝ) (j : ℕ) : cand h₀ (j + 1) = 2 * cand h₀ j := by
  rw [cand, cand, pow_succ]; ring

theorem cand_ge_h₀ (h₀ : ℝ) (j : ℕ) : h₀ ≤ cand h₀ j := by
  rw [cand]
  have h1 : h₀ ≤ max 1 h₀ := le_max_right 1 h₀
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have h3 : (0 : ℝ) < max 1 h₀ := lt_of_lt_of_le one_pos (le_max_left 1 h₀)
  nlinarith [h1, h2, h3]

theorem sand_ge (ε δ : ℝ) (hδ : 0 < δ) (j : ℕ) : ε ≤ sand ε δ j := by
  rw [sand]
  have h : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith

theorem sand_succ (ε δ : ℝ) (j : ℕ) : sand ε δ (j + 1) = sand ε δ j + δ := by
  rw [sand, sand]; push_cast; ring

theorem Fgen_zero (ε h₀ δ : ℝ) : Fgen (n := n) ε h₀ δ 0 = Chat n ε := rfl

theorem Fgen_succ (ε h₀ δ : ℝ) (j : ℕ) :
    Fgen (n := n) ε h₀ δ (j + 1)
      = Fgen (n := n) ε h₀ δ j ∩ transSet (sand ε δ (j + 1)) (cand h₀ (j + 1)) := rfl

theorem Fgen_props (n : ℕ) (hn : 2 ≤ n) (ε h₀ : ℝ) (hε : 0 < ε) (hh : 0 < h₀)
    (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hroom : ∀ s : ℝ, ε ≤ s → ∀ R : Curv4 n, ∀ c : ℝ, 0 < c →
      R + c • Iso n ∈ Chat n s → K * c ≤ scalAlg R →
      ∃ h : ℝ, 0 < h ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, 0 < t → t ≤ h → ∀ v : Curv4 n,
        IsAlgCurv v → ‖v - Q R‖ ≤ ρ → R + t • v + c • Iso n ∈ Chat n s)
    (hinc : ∀ s : ℝ, ε ≤ s → ∀ c : ℝ, 0 < c → ∀ R : Curv4 n,
      R + c • Iso n ∈ Chat n s → scalAlg R ≤ (2 * K + 2) * c →
      R + (2 * c) • Iso n ∈ Chat n (s + δ))
    (hbase : ODEInvariant (Chat n ε)) (j : ℕ) :
    ODEInvariant (Fgen (n := n) ε h₀ δ j) ∧ Fgen (n := n) ε h₀ δ j ⊆ Chat n ε ∧
      (∀ R ∈ Fgen (n := n) ε h₀ δ j, IsAlgCurv R) ∧
      (∀ R ∈ Fgen (n := n) ε h₀ δ j, R + cand h₀ j • Iso n ∈ Chat n (sand ε δ j)) ∧
      (Chat n ε ∩ {R : Curv4 n | scalAlg R ≤ h₀} ⊆ Fgen (n := n) ε h₀ δ j) := by
  induction j with
  | zero =>
    refine ⟨hbase, subset_rfl, ?_, ?_, ?_⟩
    · intro R hR; exact mev_chat_isAlgCurv hR
    · intro R hR
      have h0 : cand h₀ 0 = max 1 h₀ := by rw [cand, pow_zero, one_mul]
      have hs : sand ε δ 0 = ε := by rw [sand]; simp
      rw [hs, h0]
      exact chat_add_smul_Iso_mem hn hε hR (le_of_lt (lt_of_lt_of_le one_pos (le_max_left 1 h₀)))
    · intro R hR; exact hR.1
  | succ j ih =>
    obtain ⟨ihinv, ihsub, ihalg, ihprev, ihK⟩ := ih
    have hs : sand ε δ (j + 1) = sand ε δ j + δ := sand_succ ε δ j
    have hc : cand h₀ (j + 1) = 2 * cand h₀ j := cand_succ h₀ j
    have hinv := odeInvariant_shift_step n hn ε hε K δ hK hδ hroom hinc ihinv
      (fun R hR => mev_chat_isAlgCurv (ihsub hR)) (sand ε δ j) (cand h₀ j)
      (sand_ge ε δ hδ j) (cand_pos h₀ j) ihprev
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Fgen_succ, hs, hc]; exact hinv
    · intro R hR; exact ihsub hR.1
    · intro R hR; exact mev_chat_isAlgCurv (ihsub hR.1)
    · intro R hR; exact hR.2
    · intro R hR
      have hRj : R ∈ Fgen (n := n) ε h₀ δ j := ihK hR
      have hprev' : R + cand h₀ j • Iso n ∈ Chat n (sand ε δ j) := ihprev R hRj
      have hscal : scalAlg R ≤ (2 * K + 2) * cand h₀ j := by
        have h1 : scalAlg R ≤ h₀ := hR.2
        have h2 : h₀ ≤ cand h₀ j := cand_ge_h₀ h₀ j
        have h3 : (1 : ℝ) ≤ 2 * K + 2 := by linarith
        have h4 : 0 < cand h₀ j := cand_pos h₀ j
        nlinarith [h1, h2, h3, h4]
      have hres := hinc (sand ε δ j) (sand_ge ε δ hδ j) (cand h₀ j) (cand_pos h₀ j) R
        hprev' hscal
      refine ⟨hRj, ?_⟩
      rw [hs, hc]
      exact hres


/-- Rotation equivariance of a translate. -/
theorem transSet_rot (n : ℕ) (hn : 2 ≤ n) {s c : ℝ} (hs : 0 < s)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    {R : Curv4 n} (hR : R ∈ transSet s c) : rot A R ∈ transSet s c := by
  have h1 : rot A (R + c • Iso n) ∈ Chat n s := (chat_rot n hn A hA hs).mpr hR
  rwa [rot_add, rot_smul, rot_Iso_of_orthogonal A hA] at h1

/-- Rotation equivariance of the sequence `Fgen`. -/
theorem Fgen_rot (n : ℕ) (hn : 2 ≤ n) (ε h₀ : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    ∀ j : ℕ, ∀ R ∈ Fgen (n := n) ε h₀ δ j, rot A R ∈ Fgen (n := n) ε h₀ δ j := by
  intro j
  induction j with
  | zero => intro R hR; exact (chat_rot n hn A hA hε).mpr hR
  | succ j ih =>
    intro R hR
    obtain ⟨h1, h2⟩ := hR
    exact ⟨ih R h1, transSet_rot n hn
      (lt_of_lt_of_le hε (sand_ge ε δ hδ (j + 1))) hA h2⟩

theorem Fgen_closed (n : ℕ) (hn : 2 ≤ n) (ε h₀ : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∀ j : ℕ, IsClosed (Fgen (n := n) ε h₀ δ j) := by
  intro j
  induction j with
  | zero => rw [Fgen_zero]; exact isClosed_chat hn hε
  | succ j ih =>
    rw [Fgen_succ]
    exact ih.inter (isClosed_transSet n hn (lt_of_lt_of_le hε (sand_ge ε δ hδ (j + 1))))

theorem Fgen_convex (n : ℕ) (hn : 2 ≤ n) (ε h₀ : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∀ j : ℕ, Convex ℝ (Fgen (n := n) ε h₀ δ j) := by
  intro j
  induction j with
  | zero => rw [Fgen_zero]; exact convex_chat hn hε
  | succ j ih =>
    rw [Fgen_succ]
    exact ih.inter (convex_transSet n hn (lt_of_lt_of_le hε (sand_ge ε δ hδ (j + 1))))

/-- **The boundedness of `F ∖ Ĉ(s)`** (the analytic heart of Böhm–Wilking Thm. 4.1). -/
theorem Fgen_diff_bounded (n : ℕ) (hn : 2 ≤ n) (ε h₀ : ℝ) (hε : 0 < ε) (hh : 0 < h₀)
    (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hroom : ∀ s : ℝ, ε ≤ s → ∀ R : Curv4 n, ∀ c : ℝ, 0 < c →
      R + c • Iso n ∈ Chat n s → K * c ≤ scalAlg R →
      ∃ h : ℝ, 0 < h ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, 0 < t → t ≤ h → ∀ v : Curv4 n,
        IsAlgCurv v → ‖v - Q R‖ ≤ ρ → R + t • v + c • Iso n ∈ Chat n s)
    (hinc : ∀ s : ℝ, ε ≤ s → ∀ c : ℝ, 0 < c → ∀ R : Curv4 n,
      R + c • Iso n ∈ Chat n s → scalAlg R ≤ (2 * K + 2) * c →
      R + (2 * c) • Iso n ∈ Chat n (s + δ))
    (hbase : ODEInvariant (Chat n ε))
    (hmono : ∀ s s' : ℝ, 1 / 2 ≤ s → s ≤ s' → Chat n s' ⊆ Chat n s)
    (hray : ∀ R : Curv4 n, (∀ s : ℝ, 1 ≤ s → R ∈ Chat n s) → ∃ c : ℝ, 0 ≤ c ∧ R = c • Iso n)
    (hslice : ∃ C : ℝ, 0 ≤ C ∧ ∀ R ∈ Chat n ε, ‖R‖ ≤ C * scalAlg R)
    (hσ : ∀ R ∈ Chat n ε, 0 ≤ scalAlg R)
    (hmargin : ∀ s : ℝ, 0 < s → ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : Curv4 n, IsAlgCurv R →
      ‖R - Iso n‖ ≤ ρ → R ∈ Chat n s)
    (s : ℝ) (hs : ε ≤ s) :
    Bornology.IsBounded ((⋂ j, Fgen (n := n) ε h₀ δ j) \ Chat n s) := by
  have hprops := fun j : ℕ => Fgen_props n hn ε h₀ hε hh K δ hK hδ hroom hinc hbase j
  set F : Set (Curv4 n) := ⋂ j, Fgen (n := n) ε h₀ δ j with hFdef
  have hFsub : F ⊆ Chat n ε := fun R hR => (hprops 0).2.1 (Set.mem_iInter.mp hR 0)
  obtain ⟨C, hC0, hC⟩ := hslice
  obtain ⟨ρ, hρ0, hmargin'⟩ := hmargin s (lt_of_lt_of_le hε hs)
  have hρpos : 0 < ρ := hρ0
  -- Step 1: `scalAlg` is bounded on `F ∖ Chat n s`
  have hscalbdd : ∃ M : ℝ, ∀ R ∈ F \ Chat n s, scalAlg R ≤ M := by
    by_contra hcon
    push Not at hcon
    have hchoice : ∀ k : ℕ, ∃ R : Curv4 n, R ∈ F \ Chat n s ∧ (k : ℝ) < scalAlg R :=
      fun k => hcon (k : ℝ)
    choose R hRS hRgt using hchoice
    have hRgen : ∀ k j, R k ∈ Fgen (n := n) ε h₀ δ j :=
      fun k j => Set.mem_iInter.mp (hRS k).1 j
    have hpos : ∀ k, 0 < scalAlg (R k) := fun k =>
      lt_of_le_of_lt (Nat.cast_nonneg k) (hRgt k)
    set rhat : ℕ → Curv4 n := fun k => (scalAlg (R k))⁻¹ • R k with hrhat
    have hKmem : ∀ k, rhat k ∈ {R : Curv4 n | R ∈ Chat n ε ∧ scalAlg R = 1} := by
      intro k
      refine ⟨?_, ?_⟩
      · have h1 : R k ∈ Chat n ε := hFsub (hRS k).1
        have h2 : (0 : ℝ) ≤ (scalAlg (R k))⁻¹ := inv_nonneg.mpr (le_of_lt (hpos k))
        simpa only [hrhat] using mev_chat_smul_mem h2 h1
      · rw [hrhat]
        simp only [scalAlg_smul]
        exact inv_mul_cancel₀ (ne_of_gt (hpos k))
    have hcompact : IsCompact ({R : Curv4 n | R ∈ Chat n ε ∧ scalAlg R = 1}) := by
      refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
      · exact (isClosed_chat hn hε).inter (isClosed_eq continuous_scalAlg continuous_const)
      · refine Metric.isBounded_iff_subset_closedBall 0 |>.mpr ⟨C + 1, fun x hx => ?_⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        have h1 := hC x hx.1
        rw [hx.2, mul_one] at h1
        linarith
    obtain ⟨a, ha, φ, hφmono, hφtend⟩ := hcompact.tendsto_subseq hKmem
    have haσ : scalAlg a = 1 := ha.2
    -- `a` lies in every cone `Chat n (sand ε δ j)`
    have haj : ∀ j : ℕ, a ∈ Chat n (sand ε δ j) := by
      intro j
      have hmemj : ∀ k, rhat (φ k) + (((scalAlg (R (φ k)))⁻¹ * cand h₀ j)) • Iso n
          ∈ Chat n (sand ε δ j) := by
        intro k
        have h1 : R (φ k) + cand h₀ j • Iso n ∈ Chat n (sand ε δ j) :=
          (hprops j).2.2.2.1 (R (φ k)) (hRgen (φ k) j)
        have h2 : (0 : ℝ) ≤ (scalAlg (R (φ k)))⁻¹ := inv_nonneg.mpr (le_of_lt (hpos (φ k)))
        have h3 : (scalAlg (R (φ k)))⁻¹ • (R (φ k) + cand h₀ j • Iso n)
            ∈ Chat n (sand ε δ j) := mev_chat_smul_mem h2 h1
        have h4 : (scalAlg (R (φ k)))⁻¹ • (R (φ k) + cand h₀ j • Iso n)
            = rhat (φ k) + (((scalAlg (R (φ k)))⁻¹ * cand h₀ j)) • Iso n := by
          rw [hrhat, smul_add, smul_smul]
        rwa [h4] at h3
      have hlim : Filter.Tendsto (fun k => rhat (φ k)
          + (((scalAlg (R (φ k)))⁻¹ * cand h₀ j)) • Iso n) Filter.atTop (nhds a) := by
        have h1 : Filter.Tendsto (fun k => rhat (φ k)) Filter.atTop (nhds a) := hφtend
        have h2 : Filter.Tendsto (fun k => (scalAlg (R (φ k)))⁻¹ * cand h₀ j)
            Filter.atTop (nhds 0) := by
          rw [Metric.tendsto_atTop]
          intro e he
          have hcj : 0 < cand h₀ j := cand_pos h₀ j
          obtain ⟨N, hN⟩ := exists_nat_gt (cand h₀ j / e)
          refine ⟨max N 1, fun k hk => ?_⟩
          have hk1 : (1 : ℕ) ≤ k := le_trans (le_max_right N 1) hk
          have hkN : N ≤ k := le_trans (le_max_left N 1) hk
          have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
          have hσk : (k : ℝ) < scalAlg (R (φ k)) := by
            have h1 : (k : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast hφmono.id_le k
            linarith [hRgt (φ k)]
          have hσpos : 0 < scalAlg (R (φ k)) := lt_of_le_of_lt (Nat.cast_nonneg k) hσk
          have hbound : (scalAlg (R (φ k)))⁻¹ * cand h₀ j ≤ (k : ℝ)⁻¹ * cand h₀ j := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hcj)
            exact inv_anti₀ (by linarith) hσk.le
          have h2 : (k : ℝ)⁻¹ * cand h₀ j < e := by
            rw [inv_mul_lt_iff₀ hkpos]
            have h3 : cand h₀ j < e * (N : ℝ) := by
              rw [div_lt_iff₀ he] at hN
              linarith [hN]
            have h4 : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkN
            nlinarith [h3, h4, he]
          have hnonneg : 0 ≤ (scalAlg (R (φ k)))⁻¹ * cand h₀ j :=
            mul_nonneg (le_of_lt (inv_pos.mpr hσpos)) (le_of_lt hcj)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
          exact lt_of_le_of_lt hbound h2
        have h3 : Filter.Tendsto (fun k => rhat (φ k)
            + (((scalAlg (R (φ k)))⁻¹ * cand h₀ j)) • Iso n) Filter.atTop
            (nhds (a + (0 : ℝ) • Iso n)) := h1.add (h2.smul_const (Iso n))
        simpa using h3
      have hmem' : a ∈ Chat n (sand ε δ j) :=
        (isClosed_chat hn (lt_of_lt_of_le hε (sand_ge ε δ hδ j))).mem_of_tendsto hlim
          (Filter.Eventually.of_forall hmemj)
      exact hmem'
    -- `a` lies in every cone `Chat n s'` with `s' ≥ 1`
    have hall : ∀ s' : ℝ, 1 ≤ s' → a ∈ Chat n s' := by
      intro s' hs'
      obtain ⟨j, hj⟩ : ∃ j : ℕ, s' ≤ sand ε δ j := by
        obtain ⟨j, hj⟩ := exists_nat_ge ((s' - ε) / δ)
        refine ⟨j, ?_⟩
        rw [sand]
        push_cast
        rw [div_le_iff₀ hδ] at hj
        linarith [hj]
      exact hmono s' (sand ε δ j) (by linarith) hj (haj j)
    obtain ⟨c, hc0, hca⟩ := hray a hall
    have hnpos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    have hcpos : 0 < c := by
      have h1 : scalAlg a = c * scalAlg (Iso n) := by rw [hca, scalAlg_smul]
      rw [haσ, scalAlg_iso] at h1
      nlinarith [h1, hnpos]
    -- contradiction: `rhat (φ k) ∈ Chat n s` for large `k`
    have hnear : ∀ᶠ k in Filter.atTop, rhat (φ k) ∈ Chat n s := by
      have hev : ∀ᶠ k in Filter.atTop, dist (rhat (φ k)) a < c * ρ :=
        (Metric.tendsto_nhds.mp hφtend (c * ρ) (by positivity))
      filter_upwards [hev] with k hk
      have h1 : ‖(c⁻¹) • rhat (φ k) - Iso n‖ ≤ ρ := by
        have h2 : (c⁻¹) • rhat (φ k) - Iso n = c⁻¹ • (rhat (φ k) - a) := by
          rw [hca, smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ (ne_of_gt hcpos), one_smul]
        rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos)]
        rw [dist_eq_norm] at hk
        rw [inv_mul_le_iff₀ hcpos]
        exact le_of_lt hk
      have h3 : IsAlgCurv ((c⁻¹) • rhat (φ k)) :=
        isAlgCurv_smul _ (mev_chat_isAlgCurv (hKmem (φ k)).1)
      have h4 : (c⁻¹) • rhat (φ k) ∈ Chat n s := hmargin' _ h3 h1
      have h5 : rhat (φ k) = c • ((c⁻¹) • rhat (φ k)) := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hcpos), one_smul]
      rw [h5]
      exact mev_chat_smul_mem (le_of_lt hcpos) h4
    obtain ⟨k, hk⟩ := Filter.Eventually.exists hnear
    have h6 : R (φ k) = scalAlg (R (φ k)) • rhat (φ k) := by
      rw [hrhat, smul_smul, mul_inv_cancel₀ (ne_of_gt (hpos (φ k))), one_smul]
    have h7 : R (φ k) ∈ Chat n s := by
      rw [h6]
      exact mev_chat_smul_mem (le_of_lt (hpos (φ k))) hk
    exact (hRS (φ k)).2 h7
  obtain ⟨M, hM⟩ := hscalbdd
  refine Metric.isBounded_iff_subset_closedBall 0 |>.mpr ⟨max (C * M) 0 + 1, fun R hR => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have h2 : R ∈ Chat n ε := hFsub hR.1
  have h3 := hC R h2
  have h4 := hM R hR
  have h6 : C * scalAlg R ≤ C * M := mul_le_mul_of_nonneg_left h4 hC0
  have h7 : ‖R‖ ≤ C * M := le_trans h3 h6
  have h8 : ‖R‖ ≤ max (C * M) 0 := le_trans h7 (le_max_left _ _)
  linarith

/-- **Böhm–Wilking Theorem 4.1 / Brendle–Schoen Prop. 17**, assembled from its analytic inputs. -/
theorem exists_invariant_set_Chat_of_inputs (n : ℕ) (hn : 2 ≤ n) (ε h₀ : ℝ) (hε : 0 < ε)
    (hh : 0 < h₀) (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hroom : ∀ s : ℝ, ε ≤ s → ∀ R : Curv4 n, ∀ c : ℝ, 0 < c →
      R + c • Iso n ∈ Chat n s → K * c ≤ scalAlg R →
      ∃ h : ℝ, 0 < h ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, 0 < t → t ≤ h → ∀ v : Curv4 n,
        IsAlgCurv v → ‖v - Q R‖ ≤ ρ → R + t • v + c • Iso n ∈ Chat n s)
    (hinc : ∀ s : ℝ, ε ≤ s → ∀ c : ℝ, 0 < c → ∀ R : Curv4 n,
      R + c • Iso n ∈ Chat n s → scalAlg R ≤ (2 * K + 2) * c →
      R + (2 * c) • Iso n ∈ Chat n (s + δ))
    (hbase : ODEInvariant (Chat n ε))
    (hmono : ∀ s s' : ℝ, 1 / 2 ≤ s → s ≤ s' → Chat n s' ⊆ Chat n s)
    (hray : ∀ R : Curv4 n, (∀ s : ℝ, 1 ≤ s → R ∈ Chat n s) → ∃ c : ℝ, 0 ≤ c ∧ R = c • Iso n)
    (hslice : ∃ C : ℝ, 0 ≤ C ∧ ∀ R ∈ Chat n ε, ‖R‖ ≤ C * scalAlg R)
    (hσ : ∀ R ∈ Chat n ε, 0 ≤ scalAlg R)
    (hmargin : ∀ s : ℝ, 0 < s → ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : Curv4 n, IsAlgCurv R →
      ‖R - Iso n‖ ≤ ρ → R ∈ Chat n s) :
    ∃ F : Set (Curv4 n),
      IsClosed F ∧ Convex ℝ F ∧
      (∀ R ∈ F, IsAlgCurv R) ∧
      (∀ A : Matrix (Fin n) (Fin n) ℝ, A ∈ Matrix.orthogonalGroup (Fin n) ℝ →
        ∀ R ∈ F, rot A R ∈ F) ∧
      ODEInvariant F ∧
      (Chat n ε ∩ {R : Curv4 n | scalAlg R ≤ h₀} ⊆ F) ∧
      (∀ s : ℝ, ε ≤ s → Bornology.IsBounded (F \ Chat n s)) := by
  have hprops := fun j : ℕ => Fgen_props n hn ε h₀ hε hh K δ hK hδ hroom hinc hbase j
  have hFsub : (⋂ j, Fgen (n := n) ε h₀ δ j) ⊆ Chat n ε := fun R hR =>
    (hprops 0).2.1 (Set.mem_iInter.mp hR 0)
  refine ⟨⋂ j, Fgen (n := n) ε h₀ δ j, isClosed_iInter (Fgen_closed n hn ε h₀ hε δ hδ),
    convex_iInter (Fgen_convex n hn ε h₀ hε δ hδ), ?_, ?_, ?_, ?_, ?_⟩
  · intro R hR; exact mev_chat_isAlgCurv (hFsub hR)
  · intro A hA R hR
    exact Set.mem_iInter.mpr fun j => Fgen_rot n hn ε h₀ hε δ hδ A hA j R
      (Set.mem_iInter.mp hR j)
  · intro T R hR0 hder t ht
    exact Set.mem_iInter.mpr fun j =>
      (hprops j).1 T R (Set.mem_iInter.mp hR0 j) hder t ht
  · intro R hR
    exact Set.mem_iInter.mpr fun j => (hprops j).2.2.2.2 hR
  · exact Fgen_diff_bounded n hn ε h₀ hε hh K δ hK hδ hroom hinc hbase hmono hray hslice hσ
      hmargin

/-- **The target theorem, reduced to three inputs.**  Given the robust shifted transversality and
the shift inclusion (with their uniformity constants `K`, `δ`) and the ODE-invariance of the cone
`Chat n ε`, the structural inputs come from the proved `Chat_family_structure` and `Chat_margin`. -/
theorem exists_invariant_set_Chat_of_three (n : ℕ) (hn : 2 ≤ n) (ε h₀ : ℝ) (hε : 0 < ε)
    (hh : 0 < h₀) (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hroom : ∀ s : ℝ, ε ≤ s → ∀ R : Curv4 n, ∀ c : ℝ, 0 < c →
      R + c • Iso n ∈ Chat n s → K * c ≤ scalAlg R →
      ∃ h : ℝ, 0 < h ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, 0 < t → t ≤ h → ∀ v : Curv4 n,
        IsAlgCurv v → ‖v - Q R‖ ≤ ρ → R + t • v + c • Iso n ∈ Chat n s)
    (hinc : ∀ s : ℝ, ε ≤ s → ∀ c : ℝ, 0 < c → ∀ R : Curv4 n,
      R + c • Iso n ∈ Chat n s → scalAlg R ≤ (2 * K + 2) * c →
      R + (2 * c) • Iso n ∈ Chat n (s + δ))
    (hbase : ODEInvariant (Chat n ε)) :
    ∃ F : Set (Curv4 n),
      IsClosed F ∧ Convex ℝ F ∧
      (∀ R ∈ F, IsAlgCurv R) ∧
      (∀ A : Matrix (Fin n) (Fin n) ℝ, A ∈ Matrix.orthogonalGroup (Fin n) ℝ →
        ∀ R ∈ F, rot A R ∈ F) ∧
      ODEInvariant F ∧
      (Chat n ε ∩ {R : Curv4 n | scalAlg R ≤ h₀} ⊆ F) ∧
      (∀ s : ℝ, ε ≤ s → Bornology.IsBounded (F \ Chat n s)) := by
  obtain ⟨⟨C, hCpos, hC⟩, hmono, hray⟩ := Chat_family_structure n hn ε hε
  have hσ : ∀ R ∈ Chat n ε, 0 ≤ scalAlg R := by
    intro R hR
    by_contra h
    push Not at h
    have h1 := hC R hR
    have h2 : C * scalAlg R < 0 := mul_neg_of_pos_of_neg hCpos h
    linarith [norm_nonneg R]
  exact exists_invariant_set_Chat_of_inputs n hn ε h₀ hε hh K δ hK hδ hroom hinc hbase
    hmono hray ⟨C, le_of_lt hCpos, hC⟩ hσ (Chat_margin n hn)

/-- **The target theorem, reduced to the two transversality inputs.**  The base invariance
`ODEInvariant (Chat n ε)` is `Work.Diff.Alg.Pinch.chat_odeInvariant_of_room`, proved above from the
room lemma. -/
theorem exists_invariant_set_Chat_of_two (n : ℕ) (hn : 2 ≤ n) (ε h₀ : ℝ) (hε : 0 < ε)
    (hh : 0 < h₀) (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hroom : ∀ s : ℝ, ε ≤ s → ∀ R : Curv4 n, ∀ c : ℝ, 0 < c →
      R + c • Iso n ∈ Chat n s → K * c ≤ scalAlg R →
      ∃ h : ℝ, 0 < h ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, 0 < t → t ≤ h → ∀ v : Curv4 n,
        IsAlgCurv v → ‖v - Q R‖ ≤ ρ → R + t • v + c • Iso n ∈ Chat n s)
    (hinc : ∀ s : ℝ, ε ≤ s → ∀ c : ℝ, 0 < c → ∀ R : Curv4 n,
      R + c • Iso n ∈ Chat n s → scalAlg R ≤ (2 * K + 2) * c →
      R + (2 * c) • Iso n ∈ Chat n (s + δ)) :
    ∃ F : Set (Curv4 n),
      IsClosed F ∧ Convex ℝ F ∧
      (∀ R ∈ F, IsAlgCurv R) ∧
      (∀ A : Matrix (Fin n) (Fin n) ℝ, A ∈ Matrix.orthogonalGroup (Fin n) ℝ →
        ∀ R ∈ F, rot A R ∈ F) ∧
      ODEInvariant F ∧
      (Chat n ε ∩ {R : Curv4 n | scalAlg R ≤ h₀} ⊆ F) ∧
      (∀ s : ℝ, ε ≤ s → Bornology.IsBounded (F \ Chat n s)) :=
  exists_invariant_set_Chat_of_three n hn ε h₀ hε hh K δ hK hδ hroom hinc
    (chat_odeInvariant_of_room n hn ε hε)

/-- **Auxiliary invariant set for the Brendle–Schoen family `Ĉ(s)`** (Böhm–Wilking pinching-set
construction, Brendle–Schoen Prop. 17).  The set `F` is the intersection of the translates
`{R | R + c j • Iso n ∈ Chat n (s j)}` along a sequence `s j → ∞`, `c j → ∞`. -/
theorem exists_invariant_set_Chat (n : ℕ) (hn : 2 ≤ n) (ε h₀ : ℝ) (hε : 0 < ε) (hh : 0 < h₀) :
    ∃ F : Set (Submission.Diff.Alg.Curv4 n),
      IsClosed F ∧ Convex ℝ F ∧
      (∀ R ∈ F, Submission.Diff.Alg.IsAlgCurv R) ∧
      (∀ A : Matrix (Fin n) (Fin n) ℝ, A ∈ Matrix.orthogonalGroup (Fin n) ℝ →
        ∀ R ∈ F, Submission.Diff.Alg.rot A R ∈ F) ∧
      Submission.Diff.Alg.ODEInvariant F ∧
      (Work.Diff.Alg.Pinch.Chat n ε ∩ {R | Submission.Diff.Alg.scalAlg R ≤ h₀} ⊆ F) ∧
      (∀ s : ℝ, ε ≤ s → Bornology.IsBounded (F \ Work.Diff.Alg.Pinch.Chat n s)) := by
  obtain ⟨K, hK, hroom⟩ := Chat_room_global n hn ε hε
  obtain ⟨δ, hδ, hinc⟩ := Chat_inclusion_global n hn ε hε (2 * K + 2) (by linarith)
  exact exists_invariant_set_Chat_of_two n hn ε h₀ hε hh K δ hK hδ hroom hinc

end Work.Diff.Alg.Pinch


/-!
## STATUS (read this first): COMPLETE -- the target is proved

Everything below the line `## PLAN UPDATE` is historical.  The **current** state of this file:

The target `Work.Diff.Alg.Pinch.exists_invariant_set_Chat` is **proved** at the end of the code
above, from the two fleet lemmas `Chat_room_global` and `Chat_inclusion_global` (both proved,
axiom-clean) and the base invariance `chat_odeInvariant_of_room`, which is proved *in this file*
(see below).  `#print axioms` of the target is `[propext, Classical.choice, Quot.sound]`.

### Proved here (sorry-free)

* `transSet s c = {R | R + c • Iso n ∈ Chat n s}`: `isClosed_transSet`, `convex_transSet`,
  `transSet_isAlgCurv`, `transSet_rot`; `zero_mem_chat`, `chat_add_mem`, `chat_add_smul_Iso_mem`.
* **`odeInvariant_shift_step`** — the first-exit-time argument of Brendle–Schoen Prop. 16: if `F`
  is `ODEInvariant`, consists of algebraic tensors and satisfies the *previous* translate condition
  `R + c₀ • Iso ∈ Chat n s₀`, then `F ∩ transSet (s₀+δ) (2c₀)` is `ODEInvariant`, given the robust
  shifted transversality at `s₀+δ` (constant `K`) and the shift inclusion at `(s₀, 2K+2, δ)`.
* `cand`, `sand`, `Fgen` (the sequence `F j = Chat n ε ∩ ⋂_{i<j} transSet (ε+iδ) (2^i c₀)`),
  `Fgen_props` (each `F j` is `ODEInvariant`, `⊆ Chat n ε`, all-algebraic, satisfies the translate
  condition, and contains `K`), `Fgen_closed`, `Fgen_convex`, `Fgen_rot`.
* **`Fgen_diff_bounded`** — the boundedness of `F ∖ Chat n s` (BW Thm. 4.1's compactness argument:
  normalise, pass to a subsequence of the compact slice, use `Chat_margin` + monotonicity + the ray
  statement).
* **`exists_invariant_set_Chat_of_inputs`** — the full target statement, from eight explicit
  inputs; and **`exists_invariant_set_Chat_of_three`** — the same from *three* inputs only, since
  the four structural ones come from the proved `Work.Diff.Alg.Pinch.Chat_family_structure` and
  `Work.Diff.Alg.Pinch.Chat_margin` (both imported above and used).

* **`chat_odeInvariant_of_room`** — the base invariance `ODEInvariant (Chat n ε)`, proved here from
  the room lemma *without* any transversality input: for `X ∈ Chat n ε` and small `c > 0` the room
  applied at `X - c • Iso n` with shift `c` shows that `Q (X - c • Iso n)` is a feasible direction
  at `X`; letting `c → 0⁺` gives `Q X ∈ closure (feasibleCone (Chat n ε) X)`, and
  `ODEInvariant_of_feasible` concludes.  (This replaces the earlier plan of importing the
  BW-clan `Chat_base_invariant`, which is incompatible with the `linv_Q_ell`-clan modules
  `Chat_room_global`/`chat_shift_strict` used here because of duplicate declarations such as
  `bwDef`/`bwB`.)
* **`exists_invariant_set_Chat`** — the target, assembled as
  `obtain ⟨K, hK, hroom⟩ := Chat_room_global n hn ε hε;
   obtain ⟨δ, hδ, hinc⟩ := Chat_inclusion_global n hn ε hε (2 * K + 2) (by linarith);
   exact exists_invariant_set_Chat_of_two n hn ε h₀ hε hh K δ hK hδ hroom hinc`.

### The fleet inputs (all proved, axiom-clean)

1. `Work.Diff.Alg.Pinch.Chat_room_global` (`Diff/Alg/Pinch/Chat_room_global.lean`):
   `∀ ε > 0, ∃ K > 0, ∀ s ≥ ε, ∀ R c (0 < c), R + c • Iso ∈ Chat n s → K c ≤ scalAlg R →
   ∃ h > 0, ∃ ρ > 0, ∀ t ∈ (0,h], ∀ v algebraic, ‖v − Q R‖ ≤ ρ → R + t v + c • Iso ∈ Chat n s`.
   (BS Props. 13/14 + the scaling step of Prop. 16, *uniformly* in `s ≥ ε`; the ball in the
   direction is what the trajectory argument needs — the pointwise version without the ball is
   FALSE at `R = 0, c = 0`, which is why `0 < c` is a hypothesis.)
2. `Work.Diff.Alg.Pinch.Chat_inclusion_global` (`Diff/Alg/Pinch/Chat_inclusion_global.lean`):
   `∀ ε > 0, ∀ N > 0, ∃ δ > 0, ∀ s ≥ ε, ∀ c > 0, ∀ R, R + c • Iso ∈ Chat n s → scalAlg R ≤ N c →
   R + 2c • Iso ∈ Chat n (s+δ)`.  (BS Prop. 16(i), uniform in `s ≥ ε`.)
3. `Work.Diff.Alg.Pinch.Chat_family_structure` and `Chat_margin` supply the structural facts
   (slice bound, restricted monotonicity, the ray statement, and the interiority of `Iso n`).

-/

/-!
## PLAN UPDATE (historical)

Notation: `C s := Chat n s`, `I := Iso n`, `σ := scalAlg` (`σ (Q R) = 2∑ric² ≥ 0`, so `σ` is
nondecreasing along the ODE), `T (s,c) := {R | R + c • I ∈ C s}`.

### The three critical-path facts, all delegated (see their files)

* `Work.Diff.Alg.Pinch.Chat_shift_room` (**the "room"**, in flight):
  `∀ s₀ > 0, ∀ T ≥ s₀, ∃ K > 0, ∀ s ∈ [s₀,T], ∀ R c, 0 ≤ c → R + c • I ∈ C s → K * c ≤ σ R →
  ∃ h > 0, ∀ t ∈ (0,h], R + t • Q R + c • I ∈ C s`.
  This is BS Props. 13/14 (transversal invariance of `Ĉ(s)`) *plus* the scaling/compactness step
  of BS Prop. 16, in the threshold form "`σ R ≥ K(s) · c`" which is exactly what the maximum
  principle `chat_translate_invariant_trunc` needs (and, crucially, `K` is uniform on the compact
  window `[s₀,T]`, which is what makes the induction below non-circular).
* `Work.Diff.Alg.Pinch.Chat_shift_inclusion_any` (**the shift inclusion**, in flight):
  `∀ N > 0, ∀ s > 0, ∃ δ > 0, ∀ R, R + I ∈ C s → σ R ≤ N → R + 2 • I ∈ C (s + δ)`.
  This is the "compactness observation" in BS Prop. 16.  Note the level `N` is *arbitrary*:
  `δ` shrinks like `1/N`, and that is what my induction needs.
* `Work.Diff.Alg.Pinch.Chat_family_structure` (in flight), a triple:
  (1) `∃ C > 0, ∀ R ∈ C ε, ‖R‖ ≤ C * σ R` (the normalized slice is compact);
  (2) `∀ s s', 1/2 ≤ s → s ≤ s' → C s' ⊆ C s` (`Chat_mono` is FALSE for `s < 1/2`; for `s ≥ 1/2`
      it is true — this replaces the missing monotonicity everywhere below);
  (3) `∀ R, (∀ s ≥ 1, R ∈ C s) → ∃ c ≥ 0, R = c • I`.

### The construction (BS Prop. 16/17, with the thresholds made consistent)

`σ`-cutoff form of the translate: `TC (s,c,N) := {R | R + c • I ∈ C s ∧ N * c ≤ σ R}`.

Fix `ε > 0`, `h₀ > 0`, `K := C ε ∩ {σ ≤ h₀}`.  Choose `c 0` so large that

  `∀ j, ∀ R ∈ C ε, σ R ≤ N j * c j → R + c (j+1) • I ∈ C (s (j+1))`   (∗)

(possible because `{R ∈ C ε | σ R ≤ bound}` is compact and `c j = 2^j * c 0` grows exponentially
while `s j ≤ ε + j`), with `N j` the level below.  Recursion:

* `s 0 = ε`, `F 0 := C ε` (closed, convex, `O(n)`-invariant, ODE-invariant by `chat_odeInvariant`,
  `K ⊆ F 0`);
* at step `j+1`: let `K j` be the room constant over the window `[s j, s j + 1]`
  (`Chat_shift_room`), put `N j := 2 * K j`, take `δ j ∈ (0,1]` from
  `Chat_shift_inclusion_any` at level `N j` for `s j` (reduce a larger `δ` to `1` using (2)),
  `s (j+1) := s j + δ j` (so `s j ≤ ε + j`, `s j → ∞`, and `s (j+1) ∈ [s j, s j+1]`, so `K j` is
  still an admissible room constant at `s (j+1)`), `c (j+1) := 2 * c j`,
  `F (j+1) := F j ∩ T (s (j+1), c (j+1))`.

Then `K ⊆ F j` for every `j`: indeed `K ⊆ F j` and `K ⊆ {σ ≤ h₀} ⊆ {σ ≤ N j * c j}`, and by (∗)
every `R ∈ F j` with `σ R ≤ N j * c j` lies in `T (s (j+1), c (j+1))`.

*Invariance of `F (j+1)`* (the only analytic step): take `R(0) ∈ F (j+1)`, let `τ` be the first
time with `R(τ) + c (j+1) • I ∉ C (s (j+1))`.  At `τ`, `R(τ) ∈ F j` (invariance of `F j`) and
`σ R(τ) > N j * c j`: otherwise `R(τ) ∈ F j ∩ {σ ≤ N j * c j} ⊆ F (j+1)` and, by (∗) applied to
the nearby points `R(t)` (whose `σ` stays `≤ N j * c j` for small `t - τ`), the trajectory does not
leave `F (j+1)`.  So `σ R(τ) ≥ N j * c j = 2 K j * c j = K j * c (j+1)`, `R(τ) + c (j+1) • I ∈ C (s (j+1))`
by closedness, and the room at `s (j+1)` (constant `K j` ≤ `K (s (j+1))`) gives
`R(τ) + t • Q R(τ) + c (j+1) • I ∈ C (s (j+1))` for small `t > 0`; by continuity of `R(·)` the
trajectory stays inside `F (j+1)` just after `τ` — contradiction.
(Formally: apply `odeInvariant_of_feasible`, which is already proved in this file, to `F (j+1)`;
the feasible-cone condition at `R ∈ F (j+1)` is `Q R` either above the cutoff (the room) or below
it (then `R` lies in `{σ ≤ N j * c j}` and (∗) gives the translate membership directly).)

### Boundedness

`F := ⋂ j F j` (closed, convex, `O(n)`-invariant — the intersection of ODE-invariant sets is
ODE-invariant; `K ⊆ F`; `F ⊆ C ε`; and `F ⊆ T (s j, c j)` for all `j` with `s j → ∞`).

Fix `s' > 0` and suppose `R k ∈ F ∖ C s'` with `σ R k → ∞`.  Then `R̂ k := R k / σ R k` lies in
`C ε ∩ {σ = 1}`, which is compact by (1), so a subsequence converges to some `R̂`.  For each `j`,
`R̂ k + (c j / σ R k) • I ∈ C (s j)`, hence `R̂ ∈ C (s j)`; since `s j → ∞` and (2) is available,
`R̂ ∈ C s` for every `s ≥ 1`, so `R̂ = c • I` with `c ≥ 0` by (3), and `σ R̂ = 1` forces
`c = 1 / σ I > 0`.  Now `R̂ ∈ C s'` and `Chat_margin` (proved) upgraded along `R̂ k → R̂` gives
`R̂ k ∈ C s'` for large `k`, whence `R k = σ R k • R̂ k ∈ C s'` (cone) — contradiction.  So
`F ∖ C s'` is contained in `{σ ≤ M}` for some `M`, hence is bounded by (1).

### What remains to be written in this file

1. `zero_mem_chat`, `chat_scalAlg_nonneg` (`C s ⊆ InPIC2`, `inPIC2_metric_basic`), `I ∈ int C s`.
2. `odeInvariant_translate_halfspace`: `F j ∩ T (s,c) ∩ ...` invariance, i.e. the induction step
   with `Chat_shift_room` and `Chat_shift_inclusion_any` as *hypotheses* (so this file compiles
   before the children land).
3. The recursion (`Nat.rec` / `Classical.choose`) producing `s j, c j, F j` and the invariant
   `K ⊆ F j`, `F j ⊆ T (s j, c j)`, plus `s j → ∞`.
4. The boundedness argument above, again with `Chat_family_structure` as a hypothesis.
5. Final assembly: apply the three delegated lemmas (drop the hypotheses) to obtain
   `exists_invariant_set_Chat` unchanged.
-/
