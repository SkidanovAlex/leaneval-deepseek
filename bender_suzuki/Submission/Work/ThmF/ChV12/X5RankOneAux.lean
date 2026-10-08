import Mathlib
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.L5Struct
import Submission.Work.ThmF.ChV12.Lemma5Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.X5RankOneAux` — the split rank-one structure of `X = ⟨Q₀,K,t⟩`

Auxiliary, sorry-free facts about `B = Q0sub H ⊔ Ksub H t` (the "Borel" of `X = X5 H t`) used
by `X5_rankOne_of`:

* `B ≤ H`, `B ≤ X`; `Kset` is closed under inverses;
* `B ⊓ B^t = K` (the two-point stabiliser of `B` in `X`);
* `Q₀sub ⊓ Ksub = ⊥`, `B ≤ N(Q₀sub)`;
* `|B|` is even; the element `tX` has order `2`;
* the Bruhat decomposition in membership form and the `f`-relation of Lemma 5(b);
* `C_{Ksub}(Q₀sub) = ⊥` (conditional on `Ksub = Kset`, i.e. on Ch. V §1 Prop. 2).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open scoped Pointwise

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.L5

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-! ## `B = Q₀K` is contained in `H` and in `X = ⟨Q₀,K,t⟩` -/

theorem bor_le_H (h : Work.ThmF.Lemma5.Hyp5 H Q t s) : bor H t ≤ H :=
  sup_le (Work.ThmF.Q0sub_le H) ((Work.ThmF.Ksub_le_twoPoint (H := H) t).trans inf_le_left)

theorem Ksub_le_H (h : Work.ThmF.Lemma5.Hyp5 H Q t s) : Work.ThmF.Ksub H t ≤ H :=
  (Work.ThmF.Ksub_le_twoPoint (H := H) t).trans inf_le_left

theorem bor_le_X5 : bor H t ≤ Work.ThmF.Lemma5.X5 H t := by
  refine sup_le ?_ ?_
  · exact (Subgroup.closure_le _).mpr (fun z hz => Work.ThmF.Lemma5.Q0_subset_X5 H t hz)
  · exact (Subgroup.closure_le _).mpr (fun z hz => Work.ThmF.Lemma5.Kset_subset_X5 H t hz)

theorem Q0sub_le_X5 : Work.ThmF.Q0sub H ≤ Work.ThmF.Lemma5.X5 H t :=
  le_trans (le_sup_left : (Work.ThmF.Q0sub H : Subgroup G) ≤ bor H t) bor_le_X5

theorem Ksub_le_X5 : Work.ThmF.Ksub H t ≤ Work.ThmF.Lemma5.X5 H t :=
  le_trans (le_sup_right : (Work.ThmF.Ksub H t : Subgroup G) ≤ bor H t) bor_le_X5

theorem Kset_le_X5 : Work.ThmF.Kset H t ⊆ (Work.ThmF.Lemma5.X5 H t : Set G) :=
  fun _ hx => Ksub_le_X5 (Work.ThmF.Kset_le_Ksub H t hx)

/-! ## `K` is closed under inverses -/

theorem Kset_inv_mem' {a : G} (ha : a ∈ Work.ThmF.Kset H t) : a⁻¹ ∈ Work.ThmF.Kset H t := by
  obtain ⟨haD, haI⟩ := Work.ThmF.mem_Kset_iff.mp ha
  refine Work.ThmF.mem_Kset_iff.mpr ⟨(twoPoint H t).inv_mem haD, ?_⟩
  have h1 : t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
  rw [h1, haI, inv_inv]

/-! ## `B ⊓ B^t = K` -/

/-- `B ⊓ B^t = K`: the two-point stabiliser of `B` inside `X`. -/
theorem twoPoint_bor_eq_Ksub (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s) :
    bor H t ⊓ Submission.Blueprint.conj t (bor H t) = Work.ThmF.Ksub H t := by
  have hBH := bor_le_H h
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxB, hxBt⟩ := Subgroup.mem_inf.mp hx
    rw [Work.Models.mem_conj_iff] at hxBt
    have hxtD : x ∈ twoPoint H t := by
      refine Subgroup.mem_inf.mpr ⟨hBH hxB, ?_⟩
      rw [Work.Models.mem_conj_iff]
      exact hBH hxBt
    exact (D_inf_bor hC4 h) ▸ (Subgroup.mem_inf.mpr ⟨hxB, hxtD⟩)
  · intro k hk
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hk, ?_⟩
    rw [Work.Models.mem_conj_iff]
    have h1 : t⁻¹ * k * t ∈ Work.ThmF.Ksub H t := by
      rw [ht_inv h]; exact t_conj_Ksub_mem h hk
    exact Subgroup.mem_sup_right h1

theorem Q0sub_inf_Ksub_eq_bot (h : Work.ThmF.Lemma5.Hyp5 H Q t s) :
    Work.ThmF.Q0sub H ⊓ Work.ThmF.Ksub H t = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxQ, hxK⟩ := Subgroup.mem_inf.mp hx
  have h1 : x ∈ Q ⊓ twoPoint H t :=
    ⟨Q0sub_le_Q h hxQ, Work.ThmF.Ksub_le_twoPoint (H := H) t hxK⟩
  rw [h.split.inf_eq] at h1
  exact Subgroup.mem_bot.mp h1

theorem subgroupOf_inf_eq (A B K : Subgroup G) :
    (A ⊓ B).subgroupOf K = A.subgroupOf K ⊓ B.subgroupOf K := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]

/-- Conjugation inside the subgroup `M` corresponds to conjugation in the ambient group. -/
theorem conj_subgroupOf {M : Subgroup G} {g : G} (hg : g ∈ M) (S : Subgroup G) :
    Submission.Blueprint.conj (⟨g, hg⟩ : ↥M) (S.subgroupOf M)
      = (Submission.Blueprint.conj g S).subgroupOf M := by
  ext y
  constructor
  · intro hy
    rw [Work.Models.mem_conj_iff, Subgroup.mem_subgroupOf] at hy
    rw [Subgroup.mem_subgroupOf, Work.Models.mem_conj_iff]
    simpa using hy
  · intro hy
    rw [Subgroup.mem_subgroupOf, Work.Models.mem_conj_iff] at hy
    rw [Work.Models.mem_conj_iff, Subgroup.mem_subgroupOf]
    simpa using hy

/-- The two-point stabiliser of `B` inside `X` is `K` (as a subgroup of `X`). -/
theorem twoPoint_bor_subgroupOf (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s) :
    twoPoint ((bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) (Work.ThmF.Lemma5.tX H t)
      = (Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Lemma5.X5 H t) := by
  have hconj : Submission.Blueprint.conj (Work.ThmF.Lemma5.tX H t)
        ((bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t))
      = (Submission.Blueprint.conj t (bor H t)).subgroupOf (Work.ThmF.Lemma5.X5 H t) := by
    have hcoe : ((Work.ThmF.Lemma5.tX H t : ↥(Work.ThmF.Lemma5.X5 H t)) : G) = t := rfl
    ext y
    constructor
    · intro hy
      rw [Work.Models.mem_conj_iff, Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_subgroupOf, Work.Models.mem_conj_iff]
      simpa [hcoe] using hy
    · intro hy
      rw [Subgroup.mem_subgroupOf, Work.Models.mem_conj_iff] at hy
      rw [Work.Models.mem_conj_iff, Subgroup.mem_subgroupOf]
      simpa [hcoe] using hy
  show (bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t) ⊓
      Submission.Blueprint.conj (Work.ThmF.Lemma5.tX H t)
        ((bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) = _
  rw [hconj, ← subgroupOf_inf_eq, twoPoint_bor_eq_Ksub hC4 h]

/-! ## `B` normalises `Q₀sub` -/

theorem bor_le_normalizer_Q0sub (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s) :
    bor H t ≤ Subgroup.normalizer (Work.ThmF.Q0sub H : Set G) :=
  sup_le Subgroup.le_normalizer (Ksub_le_normalizer_Q0sub hC4 h)

theorem subgroupOf_bor_le_normalizer_subgroupOf (hC4 : ChIIFourProp)
    (h : Work.ThmF.Lemma5.Hyp5 H Q t s) :
    (bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t) ≤
      Subgroup.normalizer (((Work.ThmF.Q0sub H).subgroupOf (Work.ThmF.Lemma5.X5 H t) :
        Subgroup ↥(Work.ThmF.Lemma5.X5 H t)) : Set ↥(Work.ThmF.Lemma5.X5 H t)) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  simp only [Subgroup.mem_subgroupOf] at hx hy ⊢
  have h1 : (x : G) ∈ Subgroup.normalizer (Work.ThmF.Q0sub H : Set G) :=
    bor_le_normalizer_Q0sub hC4 h hx
  have h2 : (x : G) * (y : G) * (x : G)⁻¹ ∈ Work.ThmF.Q0sub H :=
    (Subgroup.mem_normalizer_iff.mp h1 (y : G)).mp hy
  simpa using h2

/-! ## Cardinalities -/

theorem s_mem_Q0sub (h : Work.ThmF.Lemma5.Hyp5 H Q t s) : s ∈ Work.ThmF.Q0sub H :=
  Work.ThmF.Q0_le_Q0sub H (Or.inl (s_mem_involutions h))

theorem even_card_Q0sub (h : Work.ThmF.Lemma5.Hyp5 H Q t s) :
    Even (Nat.card ↥(Work.ThmF.Q0sub H)) := by
  have hdvd : orderOf s ∣ Nat.card ↥(Work.ThmF.Q0sub H) :=
    Subgroup.orderOf_dvd_natCard _ (s_mem_Q0sub h)
  rw [h.s_inv] at hdvd
  exact even_iff_two_dvd.mpr hdvd

theorem even_card_bor (h : Work.ThmF.Lemma5.Hyp5 H Q t s) : Even (Nat.card ↥(bor H t)) := by
  have h2 : 2 ∣ Nat.card ↥(Work.ThmF.Q0sub H) := even_iff_two_dvd.mp (even_card_Q0sub h)
  exact even_iff_two_dvd.mpr
    (h2.trans (Subgroup.card_dvd_of_le (le_sup_left :
      (Work.ThmF.Q0sub H : Subgroup G) ≤ bor H t)))

/-! ## The element `tX ∈ X` -/

theorem orderOf_tX (h : Work.ThmF.Lemma5.Hyp5 H Q t s) :
    orderOf (Work.ThmF.Lemma5.tX H t) = 2 :=
  (Subgroup.orderOf_mk t (Work.ThmF.Lemma5.t_mem_X5 H t)).trans h.split.invol

theorem tX_ne_one (h : Work.ThmF.Lemma5.Hyp5 H Q t s) : Work.ThmF.Lemma5.tX H t ≠ 1 := by
  intro h1
  have h2 : t = 1 := by
    have : (Work.ThmF.Lemma5.tX H t : G) = 1 := by rw [h1]; rfl
    exact this
  have h4 := h.split.invol
  rw [h2, orderOf_one] at h4
  exact absurd h4 (by norm_num)

theorem nontrivial_X5 (h : Work.ThmF.Lemma5.Hyp5 H Q t s) :
    Nontrivial ↥(Work.ThmF.Lemma5.X5 H t) :=
  ⟨⟨Work.ThmF.Lemma5.tX H t, 1, tX_ne_one h⟩⟩

theorem tX_notMem_bor (h : Work.ThmF.Lemma5.Hyp5 H Q t s) :
    Work.ThmF.Lemma5.tX H t ∉ (bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t) := by
  intro hx
  rw [Subgroup.mem_subgroupOf] at hx
  exact h.split.not_mem (bor_le_H h hx)

theorem bor_subgroupOf_ne_top (h : Work.ThmF.Lemma5.Hyp5 H Q t s) :
    (bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t) ≠ ⊤ := by
  intro htop
  refine tX_notMem_bor h ?_
  rw [htop]
  exact Subgroup.mem_top _

/-! ## The Bruhat decomposition, in membership form -/

theorem mem_bor_or_btb (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    {g : G} (hg : g ∈ Work.ThmF.Lemma5.X5 H t) :
    g ∈ bor H t ∨ ∃ b₁ ∈ bor H t, ∃ b₂ ∈ bor H t, g = b₁ * t * b₂ := by
  have hz : g ∈ Zset H t := by rw [← X5_eq_Zset hC4 h]; exact hg
  exact hz

/-! ## The `f`-relation -/

/-- Lemma 5(b), third clause: `t (k⁻¹ s k) t ∈ B · t · (k s k⁻¹)`. -/
theorem f_relation (h : Work.ThmF.Lemma5.Hyp5 H Q t s) :
    ∀ k ∈ Work.ThmF.Kset H t, ∃ m ∈ bor H t,
      t * (k⁻¹ * s * k) * t = m * t * (k * s * k⁻¹) := by
  intro k hk
  have htmul := ht_mul_self h
  have htk : t * k * t = k⁻¹ := t_conj_Kset h hk
  have htinv : t⁻¹ = t := ht_inv h
  have htik : t * k⁻¹ * t = k := by
    have h1 : (t * k * t)⁻¹ = k := by rw [htk]; simp
    have h2 : (t * k * t)⁻¹ = t * k⁻¹ * t := by
      rw [mul_inv_rev, mul_inv_rev, htinv]
      group
    exact h2.symm.trans h1
  have hkt : k * t = t * k⁻¹ := by
    have h1 : t * (k * t) = k⁻¹ := by rw [← mul_assoc]; exact htk
    have h2 : t * (t * k⁻¹) = k⁻¹ := by rw [← mul_assoc, htmul, one_mul]
    exact mul_left_cancel (h1.trans h2.symm)
  have hsts : t * s * t = s * t * s := Work.ThmF.Lemma5.tst_eq_sts h
  refine ⟨k * s * k, ?_, ?_⟩
  · have hkK : k ∈ Work.ThmF.Ksub H t := Work.ThmF.Kset_le_Ksub H t hk
    have hk2 : k ^ 2 ∈ Work.ThmF.Ksub H t := (Work.ThmF.Ksub H t).pow_mem hkK 2
    have hQ : k⁻¹ * s * k ∈ Work.ThmF.Q0sub H := by
      have h1 := conj_s_mem_Q0sub h (Kset_inv_mem h hk)
      rwa [inv_inv] at h1
    have hm : k ^ 2 * (k⁻¹ * s * k) ∈ bor H t :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right hk2) (Subgroup.mem_sup_left hQ)
    rwa [show k ^ 2 * (k⁻¹ * s * k) = k * s * k by group] at hm
  · have eA : t * (k⁻¹ * s * k) * t = t * k⁻¹ * s * k * t := by group
    have g1 : (t * k⁻¹ * t) * (t * s * t) * (t * k * t)
        = t * k⁻¹ * (t * t) * s * (t * t) * k * t := by group
    have g2 : t * k⁻¹ * (t * t) * s * (t * t) * k * t = t * k⁻¹ * s * k * t := by
      rw [htmul]
      simp only [mul_one, one_mul]
    have e1 : (t * k⁻¹ * t) * (t * s * t) * (t * k * t) = t * k⁻¹ * s * k * t :=
      g1.trans g2
    have eC : (t * k⁻¹ * t) * (t * s * t) * (t * k * t) = k * s * t * s * k⁻¹ := by
      rw [htik, hsts, htk]; group
    have key : t * (k⁻¹ * s * k) * t = k * s * t * s * k⁻¹ :=
      eA.trans (e1.symm.trans eC)
    have f1 : (k * s * k) * t * (k * s * k⁻¹) = k * s * (k * t) * (k * s * k⁻¹) := by group
    have f2 : k * s * (k * t) * (k * s * k⁻¹) = k * s * (t * k⁻¹) * (k * s * k⁻¹) := by
      rw [hkt]
    have f3 : k * s * (t * k⁻¹) * (k * s * k⁻¹) = k * s * t * s * k⁻¹ := by group
    have key2 : (k * s * k) * t * (k * s * k⁻¹) = k * s * t * s * k⁻¹ :=
      f1.trans (f2.trans f3)
    rw [key, key2]

/-! ## `C_{Ksub}(Q₀sub) = ⊥`, conditional on `K = Kset` -/

theorem centralizer_Ksub_Q0sub_eq_bot (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) :
    Work.ThmF.Ksub H t ⊓ Subgroup.centralizer ((Work.ThmF.Q0sub H : Set G)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_centralizer_iff] at hxC
  have hxK' : x ∈ Work.ThmF.Kset H t := hKsub ▸ hxK
  have hxs : x * s * x⁻¹ = s := by
    have h1 : s * x = x * s := hxC s (s_mem_Q0sub h)
    rw [← h1]; group
  obtain ⟨k0, _, huniq⟩ :=
    Kset_regular h.split s (s_mem_involutions h) s (s_mem_involutions h)
  have hk01 : k0 = 1 := (huniq 1 ⟨Work.ThmF.one_mem_Kset H t, by simp⟩).symm
  exact (huniq x ⟨hxK', hxs⟩).trans hk01

end Work.ThmF.L5
