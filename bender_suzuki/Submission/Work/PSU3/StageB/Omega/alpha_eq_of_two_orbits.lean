import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.Seq
import Submission.Work.PSU3.StageB.Omega.beta_pow_m_eq_one
import Submission.Work.PSU3.StageB.Omega.beta_pow_setup
import Submission.Work.PSU3.StageB.Omega.uSeq_div
import Submission.Work.PSU3.StageB.Omega.exists_beta
import Submission.Work.PSU3.StageB.Omega.count_le
import Submission.Work.PSU3.StageB.Omega.count_le_self
import Submission.Work.PSU3.StageB.Omega.orbE_card
import Submission.Work.PSU3.StageB.Omega.exists_coset_zeta
import Submission.Work.PSU3.StageB.Omega.fcan_step10
import Submission.Work.PSU3.StageB.Omega.step9_of_coset
import Submission.Work.PSU3.StageB.Omega.cross_orbit_datum
import Submission.Work.PSU3.StageB.Omega.exists_zcQF_eq_of_mem_Q0

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## Elementary `qconj` lemmas -/

/-- `qconj` is multiplicative in its `D`-argument. -/
lemma qconj_mul' (h : IsSplitRankOne H Q t) (a b : ↥(twoPoint H t)) (x : ↥Q) :
    qconj h a (qconj h b x) = qconj h (b * a) x := by
  apply Subtype.ext
  simp only [qconj_coe, Subgroup.coe_mul]
  group

/-- `qconj` is multiplicative in its second argument. -/
lemma qconj_mul_apply (h : IsSplitRankOne H Q t) (a : ↥(twoPoint H t)) (x y : ↥Q) :
    qconj h a (x * y) = qconj h a x * qconj h a y := by
  apply Subtype.ext
  simp only [qconj_coe, Subgroup.coe_mul]
  group

/-- `qconj a x * y = qconj a (x * (a y a⁻¹))`. -/
lemma qconj_mul_right (h : IsSplitRankOne H Q t) (a : ↥(twoPoint H t)) (x y : ↥Q) :
    qconj h a x * y = qconj h a (x * qconj h a⁻¹ y) := by
  apply Subtype.ext
  simp only [qconj_coe, Subgroup.coe_mul, Subgroup.coe_inv]
  group

/-- `qconj` by the identity is the identity. -/
lemma qconj_one_eq (h : IsSplitRankOne H Q t) (x : ↥Q) :
    qconj h (1 : ↥(twoPoint H t)) x = x := by
  apply Subtype.ext
  simp [qconj_coe]

/-- `qconj a (qconj a⁻¹ x) = x`. -/
lemma qconj_inv_cancel (h : IsSplitRankOne H Q t) (a : ↥(twoPoint H t)) (x : ↥Q) :
    qconj h a (qconj h a⁻¹ x) = x := by
  rw [qconj_mul']
  have : (a⁻¹ * a) = (1 : ↥(twoPoint H t)) := inv_mul_cancel a
  rw [this]
  exact qconj_one_eq h x

/-- The `bar`-image of a `KW`-conjugate. -/
lemma bar_qconj (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW) (x : ↥Q) :
    Multiplicative.toAdd (fr.bar (qconj hS.split ⟨(d : G), fr.KW_le d.2⟩ x)) =
      (fr.κ d : E n) * Multiplicative.toAdd (fr.bar x) :=
  fr.act_bar d x (qconj hS.split ⟨(d : G), fr.KW_le d.2⟩ x) (by rw [qconj_coe])

/-- `kact` in terms of `qconj`. -/
lemma kact_eq_qconj' (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW) (x : ↥Q) :
    kact hS fr d x = qconj hS.split ⟨(d : G), fr.KW_le d.2⟩ x := rfl

/-! ## The element `A(u) = kElF fr (τ u)` and its action on `Q₀` -/

/-- `A(u)²` conjugates `zc u` to `zc u⁻¹`. -/
lemma kElF_tau_sq_conj (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    (((kElF fr (tau hS fr u) : fr.KW) : G)) ^ 2 * (zcQF fr u : G) *
        ((((kElF fr (tau hS fr u) : fr.KW) : G)) ^ 2)⁻¹ = (zcQF fr u⁻¹ : G) := by
  have h1 := (zcQF_eq_sconjF hS fr u).1
  have h2 := (zcQF_eq_sconjF hS fr u).2
  rw [h1, h2]
  group

/-- `A(u⁻¹) = A(u)⁻¹`. -/
lemma kElF_tau_inv_eq (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    kElF fr (tau hS fr u⁻¹) = (kElF fr (tau hS fr u))⁻¹ := by
  rw [map_inv (tau hS fr) u, kElF_inv]

/-! ## The reversal of a `qconj`-relation under `fcan` -/

/-- Applying `fcan` to a `qconj`-relation with `D` produces the same relation with the `t`-inverse
of `D`. -/
lemma fcan_qconj_rev (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {a b : ↥Q} {D E : fr.KW} (ha1 : (a : G) ≠ 1) (hb1 : (b : G) ≠ 1)
    (hE : ((E⁻¹ : fr.KW) : G) = t * ((D : fr.KW) : G) * t)
    (h : fcan hS.split a = qconj hS.split ⟨(D : G), fr.KW_le D.2⟩ b) :
    fcan hS.split b = qconj hS.split ⟨(E : G), fr.KW_le E.2⟩ a := by
  have h1 : (fcan hS.split (qconj hS.split ⟨(D : G), fr.KW_le D.2⟩ b) : G) =
      (t * (D : G) * t)⁻¹ * (fcan hS.split b : G) * (t * (D : G) * t) :=
    fcan_qconj hS.split hb1 ⟨(D : G), fr.KW_le D.2⟩
  have h2 : (fcan hS.split (fcan hS.split a) : G) = (a : G) := (fcan_fcan hS.split ha1).1
  rw [← h, h2] at h1
  apply Subtype.ext
  rw [qconj_coe]
  have hE3 : (E : G) = (t * (D : G) * t)⁻¹ := by
    have hc : (E : G)⁻¹ = t * (D : G) * t := by
      rw [← hE]
      exact (Subgroup.coe_inv fr.KW E).symm
    rw [← hc, inv_inv]
  rw [hE3, h1]
  group

/-! ## The `KW`-element `A(u)²ζ^{±1}k` has `K`-coset behaviour -/

/-- The `σE`-twisted value of `κ` of `A(u)`. -/
lemma sigma_kElF_tau (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    σE (((fr.κ (kElF fr (tau hS fr u)) : (E n)ˣ)) : E n) =
      (((fr.κ (kElF fr (tau hS fr u)) : (E n)ˣ)) : E n) :=
  (fr.mem_K_iff (kElF fr (tau hS fr u))).mp (kElF_mem_Ksub fr (tau hS fr u))

/-- `σE` of the `κ`-value of `ζ` is its inverse. -/
lemma sigma_kappa_zeta (fr : CoarseFrame H Q t n) :
    σE (((fr.κ fr.ζ : (E n)ˣ)) : E n) = ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹ :=
  eq_inv_of_mul_eq_one_right fr.ζ_norm

/-- A `kact`-conjugate of an element of `Q₀` lies in `Q₀`. -/
lemma kact_mem_Q0 (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW) {Y : ↥Q}
    (hY : (Y : G) ∈ fr.Q0) : ((kact hS fr d Y : ↥Q) : G) ∈ fr.Q0 := by
  rw [kact_eq_qconj']
  have h := conj_mem_Q0_of_mem_D hS fr (fr.KW_le (d⁻¹).2) hY
  rwa [Subgroup.coe_inv, inv_inv] at h

/-- `zcQF fr u⁻¹ ∈ Q₀`. -/
lemma zcQF_inv_mem_Q0 (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    ((zcQF fr u⁻¹ : ↥Q) : G) ∈ fr.Q0 := by
  rw [zcQF_coe]
  exact fr.zc_mem _ (by rw [fval_inv, map_inv₀, u.2])

/-- The frame's `nm` recovers `fval` from `τ u`. -/
lemma nm_fval_tau (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    ((fr.nm ((tau hS fr u).1) : (E n)ˣ) : E n) = fval u := by
  have h := congrArg (fun z : ↥(FX n) => ((z : (E n)ˣ) : E n)) (nm_tau hS fr u)
  simp only [nmF_coe] at h
  exact h

/-! ## The one-step computation (Peterfalvi II, Ch. VII §2 (19)) -/

/-- Peterfalvi II, Ch. VII §2 (19)a): the one-step computation.  Given the connecting relation
`f(ω A₁) = (b Y)^k` (`k ∈ K`), a value of `f` on the `ω`-coset and a `D ∈ KW`, the value of `f`
at the corresponding `b`-coset is computed. -/
theorem one_step (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {b : ↥Q} (hbQ : (b : G) ∉ fr.Q0)
    {A₁ Y : ↥Q} (hA₁ : (A₁ : G) ∈ fr.Q0) (hY : (Y : G) ∈ fr.Q0)
    {k : fr.KW} (hk : ((k : G) ∈ Ksub H t))
    (hψ : fcan hS.split (ω * A₁) =
      qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ (b * Y))
    {u : ↥(FX n)} {D : fr.KW} {Y₁ : ↥Q} (hY₁ : (Y₁ : G) ∈ fr.Q0)
    (hseq : fcan hS.split (ω * A₁ * zcQF fr u) =
      qconj hS.split ⟨(D : G), fr.KW_le D.2⟩ (ω * Y₁)) :
    fcan hS.split (b * Y * kact hS fr k⁻¹ (zcQF fr u⁻¹)) =
      qconj hS.split
        (⟨((D * kElF fr (tau hS fr u) ^ 2 * k : fr.KW) : G),
          fr.KW_le (D * kElF fr (tau hS fr u) ^ 2 * k).2⟩ :
            ↥(Submission.Blueprint.twoPoint H t))
        (ω * Y₁ * kact hS fr D⁻¹ (zcQF fr u⁻¹)) := by
  set x : ↥Q := ω * A₁ with hx
  set Z : ↥Q := b * Y * kact hS fr k⁻¹ (zcQF fr u⁻¹) with hZ
  set A : fr.KW := kElF fr (tau hS fr u) with hA
  have huz : (zcQF fr u : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem (fval u) u.2
  have huzi : (zcQF fr u⁻¹ : G) ∈ fr.Q0 := by
    rw [zcQF_coe]; exact fr.zc_mem (fval u⁻¹) u⁻¹.2
  have hx1 : (x : G) ≠ 1 := by
    intro hc
    have hb : fr.bar x = 1 := (fr.bar_eq_one_iff x).mpr (by rw [hc]; exact Q0_one_mem fr)
    rw [hx, map_mul, bar_eq_one_of_mem_Q0 fr hA₁, mul_one] at hb
    exact bar_ne_one_of_not_mem_Q0 fr hω hb
  have hkactQ : (kact hS fr k⁻¹ (zcQF fr u⁻¹) : G) ∈ fr.Q0 := by
    show ((k⁻¹ : fr.KW) : G)⁻¹ * (zcQF fr u⁻¹ : G) * ((k⁻¹ : fr.KW) : G) ∈ fr.Q0
    rw [Subgroup.coe_inv, inv_inv]
    exact conj_mem_Q0_of_mem_D hS fr (fr.KW_le k.2) huzi
  have hZ1 : (Z : G) ≠ 1 := by
    have hbZ : fr.bar Z = fr.bar b := by
      rw [hZ, map_mul, map_mul, bar_eq_one_of_mem_Q0 fr hY,
        bar_eq_one_of_mem_Q0 fr hkactQ, mul_one, mul_one]
    intro hc
    have hb : fr.bar Z = 1 := by rw [show Z = 1 from Subtype.ext hc]; exact bar_one fr
    rw [hbZ] at hb
    exact bar_ne_one_of_not_mem_Q0 fr hbQ hb
  have hqk : qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ Z =
      fcan hS.split x * zcQF fr u⁻¹ := by
    have h1 : qconj hS.split ⟨(k : G), fr.KW_le k.2⟩
        (kact hS fr k⁻¹ (zcQF fr u⁻¹)) = zcQF fr u⁻¹ := by
      rw [kact_eq_qconj', qconj_mul']
      have h2 : (⟨((k⁻¹ : fr.KW) : G), fr.KW_le (k⁻¹).2⟩ : ↥(twoPoint H t)) *
          ⟨(k : G), fr.KW_le k.2⟩ = 1 := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_one]
        exact inv_mul_cancel (k : G)
      rw [h2, qconj_one_eq]
    have h3 : qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ (b * Y) = fcan hS.split x := by
      rw [← hψ, hx]
    rw [hZ, qconj_mul_apply, qconj_mul_apply, h1, ← qconj_mul_apply, h3]
  have step1 : fcan hS.split Z =
      qconj hS.split ⟨(k : G), fr.KW_le k.2⟩
        (fcan hS.split (fcan hS.split x * zcQF fr u⁻¹)) := by
    have h3 := fcan_qconj hS.split hZ1 ⟨(k : G), fr.KW_le k.2⟩
    rw [tconj_eq_inv hS.split fr hk, hqk] at h3
    apply Subtype.ext
    rw [qconj_coe]
    rw [h3]
    simp only [Subgroup.coe_inv, Subgroup.coe_mul]
    group
  have hxQ0 : (x : G) ∉ fr.Q0 := by
    intro hc
    have hb : fr.bar x = 1 := (fr.bar_eq_one_iff x).mpr hc
    rw [hx, map_mul, bar_eq_one_of_mem_Q0 fr hA₁, mul_one] at hb
    exact bar_ne_one_of_not_mem_Q0 fr hω hb
  have hfxQ : (fcan hS.split x : G) ∉ fr.Q0 :=
    fun hc => hxQ0 ((fcan_mem_Q0_iff hS fr x).mp hc)
  have hxu1 : ((fcan hS.split x * zcQF fr u⁻¹ : ↥Q) : G) ≠ 1 := by
    intro hc
    have hb : fr.bar (fcan hS.split x * zcQF fr u⁻¹) = 1 :=
      (fr.bar_eq_one_iff _).mpr (by rw [hc]; exact Q0_one_mem fr)
    rw [map_mul, bar_eq_one_of_mem_Q0 fr huzi, mul_one] at hb
    exact bar_ne_one_of_not_mem_Q0 fr hfxQ hb
  have step2 : fcan hS.split (fcan hS.split x * zcQF fr u⁻¹) =
      qconj hS.split ⟨(((D * A ^ 2 : fr.KW)) : G), fr.KW_le (D * A ^ 2).2⟩
        (ω * Y₁) * zcQF fr u := by
    have hff : fcan hS.split (fcan hS.split x) = x := Subtype.ext (fcan_fcan hS.split hx1).1
    have hfm := fcan_mul_zcQF_A hS fr (ω := fcan hS.split x) (fcan_ne_one hS.split hx1) u⁻¹ hxu1
    rw [inv_inv] at hfm
    rw [hff] at hfm
    rw [show ((kElF fr (tau hS fr u⁻¹) : fr.KW) : G) = ((A⁻¹ : fr.KW) : G) from
      congrArg (fun z : fr.KW => (z : G)) (kElF_tau_inv_eq hS fr u)] at hfm
    have hxzu : x * zcQF fr u = ω * A₁ * zcQF fr u := by rw [hx]
    rw [hxzu] at hfm
    have hseqG : (fcan hS.split (ω * A₁ * zcQF fr u) : G) =
        (D : G)⁻¹ * ((ω : G) * (Y₁ : G)) * (D : G) := by
      have hh := congrArg Subtype.val hseq
      rw [qconj_coe, Subgroup.coe_mul] at hh
      exact hh
    rw [hseqG] at hfm
    apply Subtype.ext
    rw [Subgroup.coe_mul, qconj_coe, hfm]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv]
    group
  rw [step1, step2]
  have hAsq : ((A : G)) ^ 2 * (zcQF fr u : G) * (((A : G)) ^ 2)⁻¹ = (zcQF fr u⁻¹ : G) := by
    rw [show ((A : fr.KW) : G) = ((kElF fr (tau hS fr u) : fr.KW) : G) from
      congrArg (fun z : fr.KW => (z : G)) hA]
    exact kElF_tau_sq_conj hS fr u
  have hce : qconj hS.split
      ((⟨((D * A ^ 2 : fr.KW) : G), fr.KW_le (D * A ^ 2).2⟩ : ↥(twoPoint H t))⁻¹)
      (zcQF fr u) = kact hS fr D⁻¹ (zcQF fr u⁻¹) := by
    apply Subtype.ext
    rw [qconj_coe, kact_eq_qconj', qconj_coe]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, mul_inv_rev, inv_inv]
    rw [← hAsq]
    group
  rw [qconj_mul_right, hce, qconj_mul']
  apply Subtype.ext
  simp only [qconj_coe, Subgroup.coe_mul, Subgroup.coe_pow]

/-! ## The end-game: `f (ω · zc α) = ω^{ζ⁻¹}` -/

/-- **Peterfalvi II, Ch. VII §2 (15), key line.**  If `f(ω) = (ω · zc α)^ζ` with `ω ∉ Q₀`, then
`f(ω · zc α) = ω^{ζ⁻¹}`. -/
theorem fcan_zcQF_alpha (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(FX n)}
    (hωf : fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α)) :
    fcan hS.split (ω * zcQF fr α) =
      qconj hS.split
        (⟨(fr.ζ : G)⁻¹, (twoPoint H t).inv_mem (zeta_mem_D fr)⟩ : ↥(twoPoint H t)) ω := by
  have hω1 : (ω : G) ≠ 1 := fun hc => hω (by rw [hc]; exact Q0_one_mem fr)
  have hz : (zcQF fr α : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem (fval α) α.2
  have hx1 : ((ω * zcQF fr α : ↥Q) : G) ≠ 1 := by
    intro hc
    have h2 : (ω : G) = ((ω * zcQF fr α : ↥Q) : G) * (zcQF fr α : G)⁻¹ := by
      rw [Subgroup.coe_mul]; group
    exact hω (by rw [h2, hc, one_mul]; exact fr.Q0.inv_mem hz)
  have h2 : fcan hS.split (qconj hS.split (zetaD fr) (ω * zcQF fr α)) = ω := by
    rw [← hωf]
    exact Subtype.ext (fcan_fcan hS.split hω1).1
  have h2' :
      ((fcan hS.split (qconj hS.split (zetaD fr) (ω * zcQF fr α)) : ↥Q) : G) = (ω : G) :=
    congrArg Subtype.val h2
  have h3 : (fr.ζ : G)⁻¹ * ((fcan hS.split (ω * zcQF fr α) : ↥Q) : G) * (fr.ζ : G) = (ω : G) := by
    have h := fcan_qconj hS.split hx1 (zetaD fr)
    rw [show (zetaD fr : G) = (fr.ζ : G) from rfl, t_zeta_t hS.split fr] at h
    rw [← h, h2']
  apply Subtype.ext
  simp only [qconj_coe]
  show (fcan hS.split (ω * zcQF fr α) : G) = ((fr.ζ : G)⁻¹)⁻¹ * (ω : G) * (fr.ζ : G)⁻¹
  rw [inv_inv]
  calc (fcan hS.split (ω * zcQF fr α) : G)
      = (fr.ζ : G) * ((fr.ζ : G)⁻¹ * (fcan hS.split (ω * zcQF fr α) : G) * (fr.ζ : G)) *
          (fr.ζ : G)⁻¹ := by group
    _ = (fr.ζ : G) * (ω : G) * (fr.ζ : G)⁻¹ := by rw [h3]

/-! ## The main theorem -/

theorem alpha_eq_of_two_orbits {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω₁ ω₂ : ↥Q} (h₁ : (ω₁ : G) ∉ fr.Q0) (h₂ : (ω₂ : G) ∉ fr.Q0)
    {α₁ α₂ : ↥(Work.PSU3.StageB.FX n)}
    (hf₁ : Work.PSU3.StageB.fcan hS.split ω₁ =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
        (ω₁ * Work.PSU3.StageB.zcQF fr α₁))
    (hf₂ : Work.PSU3.StageB.fcan hS.split ω₂ =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
        (ω₂ * Work.PSU3.StageB.zcQF fr α₂))
    (horb : Multiplicative.toAdd (fr.bar ω₁) ∉
      Work.PSU3.StageB.orbE fr (Multiplicative.toAdd (fr.bar ω₂))) :
    Work.PSU3.StageB.fval α₁ = Work.PSU3.StageB.fval α₂ := by
  have hzα₁Q : (zcQF fr α₁ : G) ∈ fr.Q0 := by
    rw [zcQF_coe]; exact fr.zc_mem (fval α₁) α₁.2
  have hzα₂Q : (zcQF fr α₂ : G) ∈ fr.Q0 := by
    rw [zcQF_coe]; exact fr.zc_mem (fval α₂) α₂.2
  -- ## Step 0: `bar (f ω₁) ∉ orbE (bar ω₂)`
  have hbar1 : Multiplicative.toAdd (fr.bar (fcan hS.split ω₁)) ∉
      orbE fr (Multiplicative.toAdd (fr.bar ω₂)) := by
    intro hcon
    have hmem1 : Multiplicative.toAdd (fr.bar (fcan hS.split ω₁)) ∈
        orbE fr (Multiplicative.toAdd (fr.bar ω₁)) := by
      refine ⟨fr.ζ, ?_⟩
      have hbarζ : Multiplicative.toAdd
          (fr.bar (qconj hS.split (zetaD fr) (ω₁ * zcQF fr α₁))) =
          (fr.κ fr.ζ : E n) * Multiplicative.toAdd (fr.bar ω₁) := by
        rw [show qconj hS.split (zetaD fr) (ω₁ * zcQF fr α₁) =
            qconj hS.split ⟨(fr.ζ : G), fr.KW_le fr.ζ.2⟩ (ω₁ * zcQF fr α₁) from rfl,
          qconj_mul_apply]
        have hz : qconj hS.split ⟨(fr.ζ : G), fr.KW_le fr.ζ.2⟩ (zcQF fr α₁) = zcQF fr α₁ := by
          apply Subtype.ext
          rw [qconj_coe]
          exact fr.act_zc_ζ (fval α₁) α₁.2
        rw [hz, map_mul, bar_eq_one_of_mem_Q0 fr hzα₁Q, mul_one]
        exact fr.act_bar fr.ζ ω₁ (qconj hS.split ⟨(fr.ζ : G), fr.KW_le fr.ζ.2⟩ ω₁)
          (by rw [qconj_coe])
      rw [hf₁]
      exact hbarζ
    have he1 : orbE fr (Multiplicative.toAdd (fr.bar (fcan hS.split ω₁))) =
        orbE fr (Multiplicative.toAdd (fr.bar ω₁)) := orbE_eq_of_mem fr hmem1
    have he2 : orbE fr (Multiplicative.toAdd (fr.bar (fcan hS.split ω₁))) =
        orbE fr (Multiplicative.toAdd (fr.bar ω₂)) := orbE_eq_of_mem fr hcon
    have heq : orbE fr (Multiplicative.toAdd (fr.bar ω₁)) =
        orbE fr (Multiplicative.toAdd (fr.bar ω₂)) := he1.symm.trans he2
    exact horb (by rw [← heq]; exact orbE_refl fr _)
  -- ## Step 1: the connecting datum
  obtain ⟨X₁, y₂, hy₂, k, hk, hψ⟩ := cross_orbit_datum hS fr h₁ h₂ horb hbar1
  have hzX₁Q : (zcQF fr X₁ : G) ∈ fr.Q0 := by
    rw [zcQF_coe]; exact fr.zc_mem (fval X₁) X₁.2
  -- ## Step 2: `y₂ ≠ 1` and the swapped relation
  have hω₁1 : (ω₁ : G) ≠ 1 := fun hc => h₁ (by rw [hc]; exact Q0_one_mem fr)
  have hω₂1 : (ω₂ : G) ≠ 1 := fun hc => h₂ (by rw [hc]; exact Q0_one_mem fr)
  have hx₁1 : ((ω₁ * zcQF fr X₁ : ↥Q) : G) ≠ 1 := by
    intro hc
    have hb : fr.bar (ω₁ * zcQF fr X₁) = 1 :=
      (fr.bar_eq_one_iff _).mpr (by rw [hc]; exact Q0_one_mem fr)
    rw [map_mul, bar_eq_one_of_mem_Q0 fr hzX₁Q, mul_one] at hb
    exact bar_ne_one_of_not_mem_Q0 fr h₁ hb
  have hω₂y₂1 : ((ω₂ * y₂ : ↥Q) : G) ≠ 1 := by
    intro hc
    have hb : fr.bar (ω₂ * y₂) = 1 :=
      (fr.bar_eq_one_iff _).mpr (by rw [hc]; exact Q0_one_mem fr)
    rw [map_mul, bar_eq_one_of_mem_Q0 fr hy₂, mul_one] at hb
    exact bar_ne_one_of_not_mem_Q0 fr h₂ hb
  have hψ₂ : fcan hS.split (ω₂ * y₂) =
      qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ (ω₁ * zcQF fr X₁) := by
    have hq : fcan hS.split (qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ (ω₂ * y₂)) =
        ω₁ * zcQF fr X₁ := by
      rw [← hψ]
      exact Subtype.ext (fcan_fcan hS.split hx₁1).1
    have h2 : fcan hS.split (qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ (ω₂ * y₂)) =
        qconj hS.split ((⟨(k : G), fr.KW_le k.2⟩ : ↥(twoPoint H t))⁻¹)
          (fcan hS.split (ω₂ * y₂)) := by
      have h := fcan_qconj hS.split hω₂y₂1 ⟨(k : G), fr.KW_le k.2⟩
      rw [tconj_eq_inv hS.split fr hk] at h
      apply Subtype.ext
      simpa [qconj_coe, Subgroup.coe_inv] using h
    rw [h2] at hq
    have h3 := congrArg (qconj hS.split ⟨(k : G), fr.KW_le k.2⟩) hq
    rw [qconj_inv_cancel] at h3
    exact h3
  have hy₂ne : y₂ ≠ 1 := by
    intro hy1
    have hmemZ : Multiplicative.toAdd (fr.bar (fcan hS.split ω₂)) ∈
        orbE fr (Multiplicative.toAdd (fr.bar ω₂)) := by
      refine ⟨fr.ζ, ?_⟩
      have hbarζ : Multiplicative.toAdd
          (fr.bar (qconj hS.split (zetaD fr) (ω₂ * zcQF fr α₂))) =
          (fr.κ fr.ζ : E n) * Multiplicative.toAdd (fr.bar ω₂) := by
        rw [show qconj hS.split (zetaD fr) (ω₂ * zcQF fr α₂) =
            qconj hS.split ⟨(fr.ζ : G), fr.KW_le fr.ζ.2⟩ (ω₂ * zcQF fr α₂) from rfl,
          qconj_mul_apply]
        have hz : qconj hS.split ⟨(fr.ζ : G), fr.KW_le fr.ζ.2⟩ (zcQF fr α₂) = zcQF fr α₂ := by
          apply Subtype.ext
          rw [qconj_coe]
          exact fr.act_zc_ζ (fval α₂) α₂.2
        rw [hz, map_mul, bar_eq_one_of_mem_Q0 fr hzα₂Q, mul_one]
        exact fr.act_bar fr.ζ ω₂ (qconj hS.split ⟨(fr.ζ : G), fr.KW_le fr.ζ.2⟩ ω₂)
          (by rw [qconj_coe])
      rw [hf₂]
      exact hbarζ
    have hmemK : Multiplicative.toAdd (fr.bar (fcan hS.split ω₂)) ∈
        orbE fr (Multiplicative.toAdd (fr.bar ω₁)) := by
      have hbarx : fr.bar (ω₁ * zcQF fr X₁) = fr.bar ω₁ := by
        rw [map_mul, bar_eq_one_of_mem_Q0 fr hzX₁Q, mul_one]
      have hval : Multiplicative.toAdd (fr.bar (fcan hS.split ω₂)) =
          (fr.κ k : E n) * Multiplicative.toAdd (fr.bar ω₁) := by
        rw [show fcan hS.split ω₂ = fcan hS.split (ω₂ * y₂) from by rw [hy1, mul_one], hψ₂,
          bar_qconj hS fr k (ω₁ * zcQF fr X₁), hbarx]
      exact ⟨k, hval⟩
    have heq1 : orbE fr (Multiplicative.toAdd (fr.bar (fcan hS.split ω₂))) =
        orbE fr (Multiplicative.toAdd (fr.bar ω₂)) := orbE_eq_of_mem fr hmemZ
    have heq2 : orbE fr (Multiplicative.toAdd (fr.bar (fcan hS.split ω₂))) =
        orbE fr (Multiplicative.toAdd (fr.bar ω₁)) := orbE_eq_of_mem fr hmemK
    have heq : orbE fr (Multiplicative.toAdd (fr.bar ω₁)) =
        orbE fr (Multiplicative.toAdd (fr.bar ω₂)) := heq2.symm.trans heq1
    exact horb (by rw [← heq]; exact orbE_refl fr _)
  obtain ⟨X₂, hX₂⟩ := exists_zcQF_eq_of_mem_Q0 fr hy₂ hy₂ne
  have hzX₂Q : (zcQF fr X₂ : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem (fval X₂) X₂.2
  have hψ₂' : fcan hS.split (ω₂ * zcQF fr X₂) =
      qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ (ω₁ * zcQF fr X₁) := by
    rw [hX₂]; exact hψ₂
  -- ## Step 3: the FX-elements `uA` and `uB`
  have hξ₁α₁ : fval X₁ + fval α₁ ≠ 0 := by
    intro h0
    have hXα : zcQF fr X₁ = zcQF fr α₁ := by
      apply Subtype.ext
      rw [zcQF_coe, zcQF_coe]
      congr 1
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h0
      exact h0
    have hsame : fcan hS.split (ω₁ * zcQF fr α₁) =
        qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ (ω₂ * y₂) := by
      rw [← hXα]; exact hψ
    have hmemZ : Multiplicative.toAdd (fr.bar (fcan hS.split (ω₁ * zcQF fr α₁))) ∈
        orbE fr (Multiplicative.toAdd (fr.bar ω₂)) := by
      rw [hsame]
      have hbarY : fr.bar (ω₂ * y₂) = fr.bar ω₂ := by
        rw [map_mul, bar_eq_one_of_mem_Q0 fr hy₂, mul_one]
      exact ⟨k, by rw [bar_qconj hS fr k (ω₂ * y₂), hbarY]⟩
    have hmem1 : Multiplicative.toAdd (fr.bar (fcan hS.split (ω₁ * zcQF fr α₁))) ∈
        orbE fr (Multiplicative.toAdd (fr.bar ω₁)) := by
      have hE : (⟨(fr.ζ : G)⁻¹, (twoPoint H t).inv_mem (zeta_mem_D fr)⟩ : ↥(twoPoint H t)) =
          (⟨((fr.ζ⁻¹ : fr.KW) : G), fr.KW_le (fr.ζ⁻¹).2⟩ : ↥(twoPoint H t)) :=
        Subtype.ext (Subgroup.coe_inv fr.KW fr.ζ)
      rw [fcan_zcQF_alpha hS fr h₁ hf₁, hE]
      exact ⟨fr.ζ⁻¹, bar_qconj hS fr (fr.ζ⁻¹) ω₁⟩
    have he1 := orbE_eq_of_mem fr hmem1
    have he2 := orbE_eq_of_mem fr hmemZ
    have heq : orbE fr (Multiplicative.toAdd (fr.bar ω₁)) =
        orbE fr (Multiplicative.toAdd (fr.bar ω₂)) := he1.symm.trans he2
    exact horb (by rw [← heq]; exact orbE_refl fr _)
  let uA : ↥(FX n) := mkFX (fval X₁ + fval α₁) (by rw [map_add, X₁.2, α₁.2]) hξ₁α₁
  have huA : fval uA = fval X₁ + fval α₁ := rfl
  have hξ₂α₂ : fval X₂ + fval α₂ ≠ 0 := by
    intro h0
    have hXα : zcQF fr X₂ = zcQF fr α₂ := by
      apply Subtype.ext
      rw [zcQF_coe, zcQF_coe]
      congr 1
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h0
      exact h0
    have hsame : fcan hS.split (ω₂ * zcQF fr α₂) =
        qconj hS.split ⟨(k : G), fr.KW_le k.2⟩ (ω₁ * zcQF fr X₁) := by
      rw [← hXα]; exact hψ₂'
    have hmemK : Multiplicative.toAdd (fr.bar (fcan hS.split (ω₂ * zcQF fr α₂))) ∈
        orbE fr (Multiplicative.toAdd (fr.bar ω₁)) := by
      rw [hsame]
      have hbarX : fr.bar (ω₁ * zcQF fr X₁) = fr.bar ω₁ := by
        rw [map_mul, bar_eq_one_of_mem_Q0 fr hzX₁Q, mul_one]
      exact ⟨k, by rw [bar_qconj hS fr k (ω₁ * zcQF fr X₁), hbarX]⟩
    have hmem2 : Multiplicative.toAdd (fr.bar (fcan hS.split (ω₂ * zcQF fr α₂))) ∈
        orbE fr (Multiplicative.toAdd (fr.bar ω₂)) := by
      have hE : (⟨(fr.ζ : G)⁻¹, (twoPoint H t).inv_mem (zeta_mem_D fr)⟩ : ↥(twoPoint H t)) =
          (⟨((fr.ζ⁻¹ : fr.KW) : G), fr.KW_le (fr.ζ⁻¹).2⟩ : ↥(twoPoint H t)) :=
        Subtype.ext (Subgroup.coe_inv fr.KW fr.ζ)
      rw [fcan_zcQF_alpha hS fr h₂ hf₂, hE]
      exact ⟨fr.ζ⁻¹, bar_qconj hS fr (fr.ζ⁻¹) ω₂⟩
    have he1 := orbE_eq_of_mem fr hmem2
    have he2 := orbE_eq_of_mem fr hmemK
    have heq : orbE fr (Multiplicative.toAdd (fr.bar ω₂)) =
        orbE fr (Multiplicative.toAdd (fr.bar ω₁)) := he1.symm.trans he2
    have heq' : orbE fr (Multiplicative.toAdd (fr.bar ω₁)) =
        orbE fr (Multiplicative.toAdd (fr.bar ω₂)) := heq.symm
    exact horb (by rw [← heq']; exact orbE_refl fr _)
  let uB : ↥(FX n) := mkFX (fval X₂ + fval α₂) (by rw [map_add, X₂.2, α₂.2]) hξ₂α₂
  have huB : fval uB = fval X₂ + fval α₂ := rfl
  -- ## Step 4: the four one-step instances
  have hz1Q : ((1 : ↥Q) : G) ∈ fr.Q0 := Q0_one_mem fr
  have hsqX₁ : zcQF fr X₁ * zcQF fr X₁ = (1 : ↥Q) := by
    have h := fr.zc_add (fval X₁) (fval X₁) X₁.2 X₁.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, zcQF_coe, ← h,
      CharTwo.add_self_eq_zero, zc_zero]
  have hsqX₂ : zcQF fr X₂ * zcQF fr X₂ = (1 : ↥Q) := by
    have h := fr.zc_add (fval X₂) (fval X₂) X₂.2 X₂.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, zcQF_coe, ← h,
      CharTwo.add_self_eq_zero, zc_zero]
  have hseqA1 : fcan hS.split (ω₁ * zcQF fr X₁ * zcQF fr X₁) =
      qconj hS.split ⟨(fr.ζ : G), fr.KW_le fr.ζ.2⟩ (ω₁ * zcQF fr α₁) := by
    rw [show ω₁ * zcQF fr X₁ * zcQF fr X₁ = ω₁ from by rw [mul_assoc, hsqX₁, mul_one]]
    exact hf₁
  have hseqB1 : fcan hS.split (ω₂ * zcQF fr X₂ * zcQF fr X₂) =
      qconj hS.split ⟨(fr.ζ : G), fr.KW_le fr.ζ.2⟩ (ω₂ * zcQF fr α₂) := by
    rw [show ω₂ * zcQF fr X₂ * zcQF fr X₂ = ω₂ from by rw [mul_assoc, hsqX₂, mul_one]]
    exact hf₂
  have hseqA2 : fcan hS.split (ω₁ * zcQF fr X₁ * zcQF fr uA) =
      qconj hS.split ⟨((fr.ζ⁻¹ : fr.KW) : G), fr.KW_le (fr.ζ⁻¹).2⟩ (ω₁ * 1) := by
    have hzc : zcQF fr X₁ * zcQF fr uA = zcQF fr α₁ := by
      have hfix : σE (fval X₁ + fval α₁) = fval X₁ + fval α₁ := by rw [map_add, X₁.2, α₁.2]
      apply Subtype.ext
      rw [Subgroup.coe_mul, zcQF_coe, zcQF_coe, zcQF_coe, huA,
        ← fr.zc_add (fval X₁) (fval X₁ + fval α₁) X₁.2 hfix]
      congr 1
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    rw [show ω₁ * zcQF fr X₁ * zcQF fr uA = ω₁ * zcQF fr α₁ from by rw [mul_assoc, hzc]]
    have hE : (⟨(fr.ζ : G)⁻¹, (twoPoint H t).inv_mem (zeta_mem_D fr)⟩ : ↥(twoPoint H t)) =
        (⟨((fr.ζ⁻¹ : fr.KW) : G), fr.KW_le (fr.ζ⁻¹).2⟩ : ↥(twoPoint H t)) :=
      Subtype.ext (Subgroup.coe_inv fr.KW fr.ζ)
    have hend := fcan_zcQF_alpha hS fr h₁ hf₁
    rw [hE] at hend
    rw [hend, mul_one]
  have hseqB2 : fcan hS.split (ω₂ * zcQF fr X₂ * zcQF fr uB) =
      qconj hS.split ⟨((fr.ζ⁻¹ : fr.KW) : G), fr.KW_le (fr.ζ⁻¹).2⟩ (ω₂ * 1) := by
    have hzc : zcQF fr X₂ * zcQF fr uB = zcQF fr α₂ := by
      have hfix : σE (fval X₂ + fval α₂) = fval X₂ + fval α₂ := by rw [map_add, X₂.2, α₂.2]
      apply Subtype.ext
      rw [Subgroup.coe_mul, zcQF_coe, zcQF_coe, zcQF_coe, huB,
        ← fr.zc_add (fval X₂) (fval X₂ + fval α₂) X₂.2 hfix]
      congr 1
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    rw [show ω₂ * zcQF fr X₂ * zcQF fr uB = ω₂ * zcQF fr α₂ from by rw [mul_assoc, hzc]]
    have hE : (⟨(fr.ζ : G)⁻¹, (twoPoint H t).inv_mem (zeta_mem_D fr)⟩ : ↥(twoPoint H t)) =
        (⟨((fr.ζ⁻¹ : fr.KW) : G), fr.KW_le (fr.ζ⁻¹).2⟩ : ↥(twoPoint H t)) :=
      Subtype.ext (Subgroup.coe_inv fr.KW fr.ζ)
    have hend := fcan_zcQF_alpha hS fr h₂ hf₂
    rw [hE] at hend
    rw [hend, mul_one]
  have hOSA1 := one_step hS fr (ω := ω₁) (b := ω₂) (A₁ := zcQF fr X₁) (Y := y₂)
    h₁ h₂ hzX₁Q hy₂ (k := k) hk hψ (u := X₁) (D := fr.ζ) (Y₁ := zcQF fr α₁) hzα₁Q hseqA1
  have hOSA2 := one_step hS fr (ω := ω₁) (b := ω₂) (A₁ := zcQF fr X₁) (Y := y₂)
    h₁ h₂ hzX₁Q hy₂ (k := k) hk hψ (u := uA) (D := fr.ζ⁻¹) (Y₁ := 1) hz1Q hseqA2
  have hOSB1 := one_step hS fr (ω := ω₂) (b := ω₁) (A₁ := zcQF fr X₂) (Y := zcQF fr X₁)
    h₂ h₁ hzX₂Q hzX₁Q (k := k) hk hψ₂' (u := X₂) (D := fr.ζ) (Y₁ := zcQF fr α₂) hzα₂Q hseqB1
  have hOSB2 := one_step hS fr (ω := ω₂) (b := ω₁) (A₁ := zcQF fr X₂) (Y := zcQF fr X₁)
    h₂ h₁ hzX₂Q hzX₁Q (k := k) hk hψ₂' (u := uB) (D := fr.ζ⁻¹) (Y₁ := 1) hz1Q hseqB2
  -- ## Step 5: the exponents
  have hkl1 : ((kElF fr (tau hS fr X₁) : fr.KW) : G) ∈ Ksub H t :=
    kElF_mem_Ksub fr (tau hS fr X₁)
  have hkl2 : ((kElF fr (tau hS fr X₂) : fr.KW) : G) ∈ Ksub H t :=
    kElF_mem_Ksub fr (tau hS fr X₂)
  have hkla : ((kElF fr (tau hS fr uA) : fr.KW) : G) ∈ Ksub H t :=
    kElF_mem_Ksub fr (tau hS fr uA)
  have hklb : ((kElF fr (tau hS fr uB) : fr.KW) : G) ∈ Ksub H t :=
    kElF_mem_Ksub fr (tau hS fr uB)
  set D₁ : fr.KW := fr.ζ * kElF fr (tau hS fr X₁) ^ 2 * k with hD₁
  set D₂ : fr.KW := fr.ζ⁻¹ * kElF fr (tau hS fr uB) ^ 2 * k with hD₂
  set D₃ : fr.KW := fr.ζ⁻¹ * kElF fr (tau hS fr uA) ^ 2 * k with hD₃
  set D₄ : fr.KW := fr.ζ * kElF fr (tau hS fr X₂) ^ 2 * k with hD₄
  set Er₁ : fr.KW := k * kElF fr (tau hS fr X₁) ^ 2 * fr.ζ⁻¹ with hEr₁
  set Er₃ : fr.KW := k * kElF fr (tau hS fr uA) ^ 2 * fr.ζ with hEr₃
  have hA1' : fcan hS.split (ω₂ * y₂ * kact hS fr k⁻¹ (zcQF fr X₁⁻¹)) =
      qconj hS.split ⟨(D₁ : G), fr.KW_le D₁.2⟩
        (ω₁ * zcQF fr α₁ * kact hS fr (fr.ζ)⁻¹ (zcQF fr X₁⁻¹)) := by
    rw [hD₁]; exact hOSA1
  have hA2' : fcan hS.split (ω₂ * y₂ * kact hS fr k⁻¹ (zcQF fr uA⁻¹)) =
      qconj hS.split ⟨(D₃ : G), fr.KW_le D₃.2⟩
        (ω₁ * 1 * kact hS fr (fr.ζ⁻¹)⁻¹ (zcQF fr uA⁻¹)) := by
    rw [hD₃]; exact hOSA2
  have hB1' : fcan hS.split (ω₁ * zcQF fr X₁ * kact hS fr k⁻¹ (zcQF fr X₂⁻¹)) =
      qconj hS.split ⟨(D₄ : G), fr.KW_le D₄.2⟩
        (ω₂ * zcQF fr α₂ * kact hS fr (fr.ζ)⁻¹ (zcQF fr X₂⁻¹)) := by
    rw [hD₄]; exact hOSB1
  have hB2' : fcan hS.split (ω₁ * zcQF fr X₁ * kact hS fr k⁻¹ (zcQF fr uB⁻¹)) =
      qconj hS.split ⟨(D₂ : G), fr.KW_le D₂.2⟩
        (ω₂ * 1 * kact hS fr (fr.ζ⁻¹)⁻¹ (zcQF fr uB⁻¹)) := by
    rw [hD₂]; exact hOSB2
  -- ## Step 6: the `t`-conjugation identities for the exponents
  have ht : t * t = 1 := mul_self_eq_one hS.split
  have hζt : t * (fr.ζ : G) * t = (fr.ζ : G) := t_zeta_t hS.split fr
  have hζit : t * (fr.ζ : G)⁻¹ * t = (fr.ζ : G)⁻¹ := t_zeta_inv_t hS.split fr
  have hAt : t * ((kElF fr (tau hS fr X₁) : fr.KW) : G) * t =
      ((kElF fr (tau hS fr X₁) : fr.KW) : G)⁻¹ := tconj_eq_inv hS.split fr hkl1
  have hat : t * ((kElF fr (tau hS fr uA) : fr.KW) : G) * t =
      ((kElF fr (tau hS fr uA) : fr.KW) : G)⁻¹ := tconj_eq_inv hS.split fr hkla
  have hkt : t * (k : G) * t = (k : G)⁻¹ := tconj_eq_inv hS.split fr hk
  have hEr₁' : ((Er₁⁻¹ : fr.KW) : G) = t * ((D₁ : fr.KW) : G) * t := by
    have hR : t * ((D₁ : fr.KW) : G) * t =
        (fr.ζ : G) * ((kElF fr (tau hS fr X₁) : fr.KW) : G)⁻¹ *
          ((kElF fr (tau hS fr X₁) : fr.KW) : G)⁻¹ * (k : G)⁻¹ := by
      rw [hD₁]
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, pow_two]
      rw [conj_mul_self ht ((fr.ζ : G) * (((kElF fr (tau hS fr X₁) : fr.KW) : G) *
              ((kElF fr (tau hS fr X₁) : fr.KW) : G))) (k : G),
          conj_mul_self ht (fr.ζ : G) (((kElF fr (tau hS fr X₁) : fr.KW) : G) *
              ((kElF fr (tau hS fr X₁) : fr.KW) : G)),
          conj_mul_self ht ((kElF fr (tau hS fr X₁) : fr.KW) : G)
            ((kElF fr (tau hS fr X₁) : fr.KW) : G), hζt, hAt, hkt]
      group
    have hL : ((Er₁⁻¹ : fr.KW) : G) =
        (fr.ζ : G) * ((kElF fr (tau hS fr X₁) : fr.KW) : G)⁻¹ *
          ((kElF fr (tau hS fr X₁) : fr.KW) : G)⁻¹ * (k : G)⁻¹ := by
      rw [hEr₁]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, pow_two]
      group
    rw [hL, hR]
  have hEr₃' : ((Er₃⁻¹ : fr.KW) : G) = t * ((D₃ : fr.KW) : G) * t := by
    have hR : t * ((D₃ : fr.KW) : G) * t =
        (fr.ζ : G)⁻¹ * ((kElF fr (tau hS fr uA) : fr.KW) : G)⁻¹ *
          ((kElF fr (tau hS fr uA) : fr.KW) : G)⁻¹ * (k : G)⁻¹ := by
      rw [hD₃]
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, pow_two]
      rw [conj_mul_self ht ((fr.ζ : G)⁻¹ * (((kElF fr (tau hS fr uA) : fr.KW) : G) *
              ((kElF fr (tau hS fr uA) : fr.KW) : G))) (k : G),
          conj_mul_self ht ((fr.ζ : G)⁻¹) (((kElF fr (tau hS fr uA) : fr.KW) : G) *
              ((kElF fr (tau hS fr uA) : fr.KW) : G)),
          conj_mul_self ht ((kElF fr (tau hS fr uA) : fr.KW) : G)
            ((kElF fr (tau hS fr uA) : fr.KW) : G), hζit, hat, hkt]
      group
    have hL : ((Er₃⁻¹ : fr.KW) : G) =
        (fr.ζ : G)⁻¹ * ((kElF fr (tau hS fr uA) : fr.KW) : G)⁻¹ *
          ((kElF fr (tau hS fr uA) : fr.KW) : G)⁻¹ * (k : G)⁻¹ := by
      rw [hEr₃]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, pow_two]
      group
    rw [hL, hR]
  -- ## Step 7: the reversed relations
  have hbar1_mul : ∀ Z : ↥Q, (Z : G) ∈ fr.Q0 → ((ω₁ * Z : ↥Q) : G) ≠ 1 := by
    intro Z hZ hc
    have hb : fr.bar (ω₁ * Z) = 1 := (fr.bar_eq_one_iff _).mpr (by rw [hc]; exact Q0_one_mem fr)
    rw [map_mul, bar_eq_one_of_mem_Q0 fr hZ, mul_one] at hb
    exact bar_ne_one_of_not_mem_Q0 fr h₁ hb
  have hbar2_mul : ∀ Z : ↥Q, (Z : G) ∈ fr.Q0 → ((ω₂ * Z : ↥Q) : G) ≠ 1 := by
    intro Z hZ hc
    have hb : fr.bar (ω₂ * Z) = 1 := (fr.bar_eq_one_iff _).mpr (by rw [hc]; exact Q0_one_mem fr)
    rw [map_mul, bar_eq_one_of_mem_Q0 fr hZ, mul_one] at hb
    exact bar_ne_one_of_not_mem_Q0 fr h₂ hb
  have hA1rev : fcan hS.split (ω₁ * zcQF fr α₁ * kact hS fr (fr.ζ)⁻¹ (zcQF fr X₁⁻¹)) =
      qconj hS.split ⟨(Er₁ : G), fr.KW_le Er₁.2⟩
        (ω₂ * y₂ * kact hS fr k⁻¹ (zcQF fr X₁⁻¹)) := by
    refine fcan_qconj_rev hS fr ?_ ?_ hEr₁' hA1'
    · rw [mul_assoc]
      exact hbar2_mul (y₂ * kact hS fr k⁻¹ (zcQF fr X₁⁻¹))
        (by rw [Subgroup.coe_mul]
            exact fr.Q0.mul_mem hy₂ (kact_mem_Q0 hS fr k⁻¹ (zcQF_inv_mem_Q0 fr X₁)))
    · rw [mul_assoc]
      exact hbar1_mul (zcQF fr α₁ * kact hS fr (fr.ζ⁻¹) (zcQF fr X₁⁻¹))
        (by rw [Subgroup.coe_mul]
            exact fr.Q0.mul_mem hzα₁Q (kact_mem_Q0 hS fr (fr.ζ⁻¹) (zcQF_inv_mem_Q0 fr X₁)))
  have hA2rev : fcan hS.split (ω₁ * 1 * kact hS fr ((fr.ζ⁻¹)⁻¹) (zcQF fr uA⁻¹)) =
      qconj hS.split ⟨(Er₃ : G), fr.KW_le Er₃.2⟩
        (ω₂ * y₂ * kact hS fr k⁻¹ (zcQF fr uA⁻¹)) := by
    refine fcan_qconj_rev hS fr ?_ ?_ hEr₃' hA2'
    · rw [mul_assoc]
      exact hbar2_mul (y₂ * kact hS fr k⁻¹ (zcQF fr uA⁻¹))
        (by rw [Subgroup.coe_mul]
            exact fr.Q0.mul_mem hy₂ (kact_mem_Q0 hS fr k⁻¹ (zcQF_inv_mem_Q0 fr uA)))
    · rw [mul_assoc]
      exact hbar1_mul (1 * kact hS fr (fr.ζ⁻¹)⁻¹ (zcQF fr uA⁻¹))
        (by rw [Subgroup.coe_mul]
            exact fr.Q0.mul_mem (Q0_one_mem fr) (kact_mem_Q0 hS fr (fr.ζ⁻¹)⁻¹ (zcQF_inv_mem_Q0 fr uA)))
  -- ## Step 8: the two comparisons
  -- (I) `A1`-reversed against `B2`
  have hmemI : ((Er₁⁻¹ * D₂ : fr.KW) : G) ∈ Ksub H t := by
    have hX : Er₁⁻¹ * D₂ =
        (kElF fr (tau hS fr X₁))⁻¹ ^ 2 * (kElF fr (tau hS fr uB)) ^ 2 := by
      apply fr.κ_injective
      refine Units.ext ?_
      simp only [Er₁, D₂, map_mul, map_inv, map_pow, kElF_kappa, Units.val_mul,
        Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      field_simp
    rw [hX]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv]
    exact (Ksub H t).mul_mem
      ((Ksub H t).pow_mem ((Ksub H t).inv_mem (kElF_mem_Ksub fr (tau hS fr X₁))) 2)
      ((Ksub H t).pow_mem (kElF_mem_Ksub fr (tau hS fr uB)) 2)
  have hmemx₁I : ((zcQF fr α₁ * kact hS fr (fr.ζ⁻¹) (zcQF fr X₁⁻¹) : ↥Q) : G) ∈ fr.Q0 := by
    rw [Subgroup.coe_mul]
    exact fr.Q0.mul_mem hzα₁Q (kact_mem_Q0 hS fr (fr.ζ⁻¹) (zcQF_inv_mem_Q0 fr X₁))
  have hmemx₂I : ((zcQF fr X₁ * kact hS fr k⁻¹ (zcQF fr uB⁻¹) : ↥Q) : G) ∈ fr.Q0 := by
    rw [Subgroup.coe_mul]
    exact fr.Q0.mul_mem hzX₁Q (kact_mem_Q0 hS fr k⁻¹ (zcQF_inv_mem_Q0 fr uB))
  have hmemI' : ((y₂ * kact hS fr k⁻¹ (zcQF fr X₁⁻¹) : ↥Q) : G) ∈ fr.Q0 := by
    rw [Subgroup.coe_mul]
    exact fr.Q0.mul_mem hy₂ (kact_mem_Q0 hS fr k⁻¹ (zcQF_inv_mem_Q0 fr X₁))
  have hmemI'' : ((1 * kact hS fr ((fr.ζ⁻¹)⁻¹) (zcQF fr uB⁻¹) : ↥Q) : G) ∈ fr.Q0 := by
    rw [Subgroup.coe_mul]
    exact fr.Q0.mul_mem (Q0_one_mem fr) (kact_mem_Q0 hS fr ((fr.ζ⁻¹)⁻¹) (zcQF_inv_mem_Q0 fr uB))
  have hshiftI : (zcQF fr α₁ * kact hS fr (fr.ζ⁻¹) (zcQF fr X₁⁻¹) : ↥Q) =
      (zcQF fr X₁ * kact hS fr k⁻¹ (zcQF fr uB⁻¹) : ↥Q) := by
    by_contra hne
    have hrel₁ : fcan hS.split (ω₁ * (zcQF fr α₁ * kact hS fr (fr.ζ⁻¹) (zcQF fr X₁⁻¹))) =
        qconj hS.split ⟨(Er₁ : G), fr.KW_le Er₁.2⟩
          (ω₂ * (y₂ * kact hS fr k⁻¹ (zcQF fr X₁⁻¹))) := by
      rw [← mul_assoc, ← mul_assoc]
      exact hA1rev
    have hrel₂ : fcan hS.split (ω₁ * (zcQF fr X₁ * kact hS fr k⁻¹ (zcQF fr uB⁻¹))) =
        qconj hS.split ⟨(D₂ : G), fr.KW_le D₂.2⟩
          (ω₂ * (1 * kact hS fr ((fr.ζ⁻¹)⁻¹) (zcQF fr uB⁻¹))) := by
      rw [← mul_assoc, ← mul_assoc]
      exact hB2'
    have hnot := coset_sep_KW hS fr (ω := ω₁) (ω' := ω₂) h₁ h₂ hmemx₁I hmemx₂I hne
      hmemI' hmemI'' hrel₁ hrel₂
    exact hnot (by rw [← Subgroup.coe_inv, ← Subgroup.coe_mul]; exact hmemI)
  have hr₁I : fcan hS.split (ω₁ * (zcQF fr α₁ * kact hS fr (fr.ζ⁻¹) (zcQF fr X₁⁻¹))) =
      qconj hS.split ⟨(Er₁ : G), fr.KW_le Er₁.2⟩
        (ω₂ * (y₂ * kact hS fr k⁻¹ (zcQF fr X₁⁻¹))) := by
    rw [← mul_assoc, ← mul_assoc]
    exact hA1rev
  have hr₂I : fcan hS.split (ω₁ * (zcQF fr X₁ * kact hS fr k⁻¹ (zcQF fr uB⁻¹))) =
      qconj hS.split ⟨(D₂ : G), fr.KW_le D₂.2⟩
        (ω₂ * (1 * kact hS fr ((fr.ζ⁻¹)⁻¹) (zcQF fr uB⁻¹))) := by
    rw [← mul_assoc, ← mul_assoc]
    exact hB2'
  have hEqI : qconj hS.split ⟨(Er₁ : G), fr.KW_le Er₁.2⟩
        (ω₂ * (y₂ * kact hS fr k⁻¹ (zcQF fr X₁⁻¹))) =
      qconj hS.split ⟨(D₂ : G), fr.KW_le D₂.2⟩
        (ω₂ * (1 * kact hS fr ((fr.ζ⁻¹)⁻¹) (zcQF fr uB⁻¹))) := by
    rw [← hr₁I, ← hr₂I, hshiftI]
  have hkappaI : (fr.κ Er₁ : E n) = (fr.κ D₂ : E n) := by
    have h1 := congrArg (fun z : ↥Q => Multiplicative.toAdd (fr.bar z)) hEqI
    rw [bar_qconj hS fr Er₁ (ω₂ * (y₂ * kact hS fr k⁻¹ (zcQF fr X₁⁻¹))),
      bar_qconj hS fr D₂ (ω₂ * (1 * kact hS fr ((fr.ζ⁻¹)⁻¹) (zcQF fr uB⁻¹)))] at h1
    have hb₁ : fr.bar (ω₂ * (y₂ * kact hS fr k⁻¹ (zcQF fr X₁⁻¹))) = fr.bar ω₂ := by
      rw [map_mul, map_mul, bar_eq_one_of_mem_Q0 fr hy₂,
        bar_eq_one_of_mem_Q0 fr (kact_mem_Q0 hS fr k⁻¹ (zcQF_inv_mem_Q0 fr X₁)), mul_one, mul_one]
    have hb₂ : fr.bar (ω₂ * (1 * kact hS fr ((fr.ζ⁻¹)⁻¹) (zcQF fr uB⁻¹))) = fr.bar ω₂ := by
      rw [map_mul, map_mul, bar_one fr,
        bar_eq_one_of_mem_Q0 fr (kact_mem_Q0 hS fr ((fr.ζ⁻¹)⁻¹) (zcQF_inv_mem_Q0 fr uB)),
        one_mul, mul_one]
    rw [hb₁, hb₂] at h1
    exact mul_right_cancel₀ (toAdd_bar_ne_zero fr h₂) h1
  have hsqI : (fval (tau hS fr X₁)) ^ 2 = (fval (tau hS fr uB)) ^ 2 := by
    have h := hkappaI
    rw [hEr₁, hD₂] at h
    simp only [map_mul, map_inv, map_pow, kElF_kappa, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val] at h
    have hk0 : (((fr.κ k : (E n)ˣ)) : E n) ≠ 0 := Units.ne_zero _
    have hz0 : (((fr.κ fr.ζ : (E n)ˣ)) : E n) ≠ 0 := Units.ne_zero _
    have h4 := congrArg (fun z : E n => z * (((fr.κ fr.ζ : (E n)ˣ)) : E n)) h
    simp only [mul_assoc, inv_mul_cancel₀ hz0, mul_one] at h4
    have h5 : (((fr.κ k : (E n)ˣ)) : E n) * (fval (tau hS fr X₁)) ^ 2 =
        (fval (tau hS fr uB)) ^ 2 * (((fr.κ k : (E n)ˣ)) : E n) := by
      rw [h4]
      field_simp
    have h6 : (fval (tau hS fr X₁)) ^ 2 * (((fr.κ k : (E n)ˣ)) : E n) =
        (fval (tau hS fr uB)) ^ 2 * (((fr.κ k : (E n)ˣ)) : E n) := by
      rw [← h5]; ring
    exact mul_right_cancel₀ hk0 h6
  have hα₂ : fval α₂ = fval X₁ + fval X₂ := by
    have htau : fval (tau hS fr X₁) = fval (tau hS fr uB) := by
      have hsum : (fval (tau hS fr X₁) + fval (tau hS fr uB)) *
          (fval (tau hS fr X₁) + fval (tau hS fr uB)) = 0 := by
        rw [← pow_two, CharTwo.add_sq, hsqI, CharTwo.add_self_eq_zero]
      have h0 := mul_self_eq_zero.mp hsum
      rwa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h0
    have hfin : fval X₁ = fval uB := by
      have h1 := nm_fval_tau hS fr X₁
      have h2 := nm_fval_tau hS fr uB
      have h3 : ((tau hS fr X₁ : ↥(FX n)) : (E n)ˣ) = ((tau hS fr uB : ↥(FX n)) : (E n)ˣ) :=
        Units.ext htau
      rw [← h1, ← h2, h3]
    have h : fval X₁ = fval X₂ + fval α₂ := by rw [hfin, huB]
    rw [h]
    rw [show fval X₂ + fval α₂ + fval X₂ = fval α₂ + (fval X₂ + fval X₂) from by ring,
      CharTwo.add_self_eq_zero, add_zero]
  -- (II) `A2`-reversed against `B1`
  have hmemII : ((Er₃⁻¹ * D₄ : fr.KW) : G) ∈ Ksub H t := by
    have hX : Er₃⁻¹ * D₄ =
        (kElF fr (tau hS fr uA))⁻¹ ^ 2 * (kElF fr (tau hS fr X₂)) ^ 2 := by
      apply fr.κ_injective
      refine Units.ext ?_
      simp only [Er₃, D₄, map_mul, map_inv, map_pow, kElF_kappa, Units.val_mul,
        Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      field_simp
    rw [hX]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv]
    exact (Ksub H t).mul_mem
      ((Ksub H t).pow_mem ((Ksub H t).inv_mem (kElF_mem_Ksub fr (tau hS fr uA))) 2)
      ((Ksub H t).pow_mem (kElF_mem_Ksub fr (tau hS fr X₂)) 2)
  have hmemx₁II : ((1 * kact hS fr ((fr.ζ⁻¹)⁻¹) (zcQF fr uA⁻¹) : ↥Q) : G) ∈ fr.Q0 := by
    rw [Subgroup.coe_mul]
    exact fr.Q0.mul_mem (Q0_one_mem fr) (kact_mem_Q0 hS fr ((fr.ζ⁻¹)⁻¹) (zcQF_inv_mem_Q0 fr uA))
  have hmemx₂II : ((zcQF fr X₁ * kact hS fr k⁻¹ (zcQF fr X₂⁻¹) : ↥Q) : G) ∈ fr.Q0 := by
    rw [Subgroup.coe_mul]
    exact fr.Q0.mul_mem hzX₁Q (kact_mem_Q0 hS fr k⁻¹ (zcQF_inv_mem_Q0 fr X₂))
  have hmemII' : ((y₂ * kact hS fr k⁻¹ (zcQF fr uA⁻¹) : ↥Q) : G) ∈ fr.Q0 := by
    rw [Subgroup.coe_mul]
    exact fr.Q0.mul_mem hy₂ (kact_mem_Q0 hS fr k⁻¹ (zcQF_inv_mem_Q0 fr uA))
  have hmemII'' : ((zcQF fr α₂ * kact hS fr (fr.ζ⁻¹) (zcQF fr X₂⁻¹) : ↥Q) : G) ∈ fr.Q0 := by
    rw [Subgroup.coe_mul]
    exact fr.Q0.mul_mem hzα₂Q (kact_mem_Q0 hS fr (fr.ζ⁻¹) (zcQF_inv_mem_Q0 fr X₂))
  have hr₁II : fcan hS.split (ω₁ * (1 * kact hS fr ((fr.ζ⁻¹)⁻¹) (zcQF fr uA⁻¹))) =
      qconj hS.split ⟨(Er₃ : G), fr.KW_le Er₃.2⟩
        (ω₂ * (y₂ * kact hS fr k⁻¹ (zcQF fr uA⁻¹))) := by
    rw [← mul_assoc, ← mul_assoc]
    exact hA2rev
  have hr₂II : fcan hS.split (ω₁ * (zcQF fr X₁ * kact hS fr k⁻¹ (zcQF fr X₂⁻¹))) =
      qconj hS.split ⟨(D₄ : G), fr.KW_le D₄.2⟩
        (ω₂ * (zcQF fr α₂ * kact hS fr (fr.ζ⁻¹) (zcQF fr X₂⁻¹))) := by
    rw [← mul_assoc, ← mul_assoc]
    exact hB1'
  have hshiftII : (1 * kact hS fr ((fr.ζ⁻¹)⁻¹) (zcQF fr uA⁻¹) : ↥Q) =
      (zcQF fr X₁ * kact hS fr k⁻¹ (zcQF fr X₂⁻¹) : ↥Q) := by
    by_contra hne
    have hnot := coset_sep_KW hS fr (ω := ω₁) (ω' := ω₂) h₁ h₂ hmemx₁II hmemx₂II hne
      hmemII' hmemII'' hr₁II hr₂II
    exact hnot (by rw [← Subgroup.coe_inv, ← Subgroup.coe_mul]; exact hmemII)
  have hEqII : qconj hS.split ⟨(Er₃ : G), fr.KW_le Er₃.2⟩
        (ω₂ * (y₂ * kact hS fr k⁻¹ (zcQF fr uA⁻¹))) =
      qconj hS.split ⟨(D₄ : G), fr.KW_le D₄.2⟩
        (ω₂ * (zcQF fr α₂ * kact hS fr (fr.ζ⁻¹) (zcQF fr X₂⁻¹))) := by
    rw [← hr₁II, ← hr₂II, hshiftII]
  have hkappaII : (fr.κ Er₃ : E n) = (fr.κ D₄ : E n) := by
    have h1 := congrArg (fun z : ↥Q => Multiplicative.toAdd (fr.bar z)) hEqII
    rw [bar_qconj hS fr Er₃ (ω₂ * (y₂ * kact hS fr k⁻¹ (zcQF fr uA⁻¹))),
      bar_qconj hS fr D₄ (ω₂ * (zcQF fr α₂ * kact hS fr (fr.ζ⁻¹) (zcQF fr X₂⁻¹)))] at h1
    have hb₁ : fr.bar (ω₂ * (y₂ * kact hS fr k⁻¹ (zcQF fr uA⁻¹))) = fr.bar ω₂ := by
      rw [map_mul, map_mul, bar_eq_one_of_mem_Q0 fr hy₂,
        bar_eq_one_of_mem_Q0 fr (kact_mem_Q0 hS fr k⁻¹ (zcQF_inv_mem_Q0 fr uA)), mul_one, mul_one]
    have hb₂ : fr.bar (ω₂ * (zcQF fr α₂ * kact hS fr (fr.ζ⁻¹) (zcQF fr X₂⁻¹))) =
        fr.bar ω₂ := by
      rw [map_mul, map_mul, bar_eq_one_of_mem_Q0 fr hzα₂Q,
        bar_eq_one_of_mem_Q0 fr (kact_mem_Q0 hS fr (fr.ζ⁻¹) (zcQF_inv_mem_Q0 fr X₂)),
        mul_one, mul_one]
    rw [hb₁, hb₂] at h1
    exact mul_right_cancel₀ (toAdd_bar_ne_zero fr h₂) h1
  have hα₁ : fval α₁ = fval X₁ + fval X₂ := by
    have hsq : (fval (tau hS fr uA)) ^ 2 = (fval (tau hS fr X₂)) ^ 2 := by
      have h := hkappaII
      rw [hEr₃, hD₄] at h
      simp only [map_mul, map_inv, map_pow, kElF_kappa, Units.val_mul,
        Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val] at h
      have hk0 : (((fr.κ k : (E n)ˣ)) : E n) ≠ 0 := Units.ne_zero _
      have hz0 : (((fr.κ fr.ζ : (E n)ˣ)) : E n) ≠ 0 := Units.ne_zero _
      have h5 : (((fr.κ k : (E n)ˣ)) : E n) * (fval (tau hS fr uA)) ^ 2 *
            (((fr.κ fr.ζ : (E n)ˣ)) : E n) =
          (fval (tau hS fr X₂)) ^ 2 * (((fr.κ k : (E n)ˣ)) : E n) *
            (((fr.κ fr.ζ : (E n)ˣ)) : E n) := by
        rw [h]; ring
      have h6 : (((fr.κ k : (E n)ˣ)) : E n) * (fval (tau hS fr uA)) ^ 2 =
          (fval (tau hS fr X₂)) ^ 2 * (((fr.κ k : (E n)ˣ)) : E n) :=
        mul_right_cancel₀ hz0 h5
      have h7 : (fval (tau hS fr uA)) ^ 2 * (((fr.κ k : (E n)ˣ)) : E n) =
          (fval (tau hS fr X₂)) ^ 2 * (((fr.κ k : (E n)ˣ)) : E n) := by
        rw [← h6]; ring
      exact mul_right_cancel₀ hk0 h7
    have htau : fval (tau hS fr uA) = fval (tau hS fr X₂) := by
      have hsum : (fval (tau hS fr uA) + fval (tau hS fr X₂)) *
          (fval (tau hS fr uA) + fval (tau hS fr X₂)) = 0 := by
        rw [← pow_two, CharTwo.add_sq, hsq, CharTwo.add_self_eq_zero]
      have h0 := mul_self_eq_zero.mp hsum
      rwa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h0
    have hfin : fval uA = fval X₂ := by
      have h1 := nm_fval_tau hS fr uA
      have h2 := nm_fval_tau hS fr X₂
      have h3 : ((tau hS fr uA : ↥(FX n)) : (E n)ˣ) = ((tau hS fr X₂ : ↥(FX n)) : (E n)ˣ) :=
        Units.ext htau
      rw [← h1, ← h2, h3]
    have h : fval X₁ + fval α₁ = fval X₂ := by rw [← huA, hfin]
    rw [← h]
    rw [show fval X₁ + (fval X₁ + fval α₁) = fval α₁ + (fval X₁ + fval X₁) from by ring,
      CharTwo.add_self_eq_zero, add_zero]
  -- ## Step 9: conclusion
  rw [hα₁, hα₂]


end Work.PSU3.StageB.Omega
