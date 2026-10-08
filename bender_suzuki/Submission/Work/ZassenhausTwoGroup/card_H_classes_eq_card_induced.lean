import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.ZassenhausTwoGroup.normalizer_Q_eq
import Submission.Work.ZassenhausTwoGroup.zetaStar_aux
import Submission.Work.ZassenhausTwoGroup.indFun_Q_apply_mem_Q
import Submission.Work.ZassenhausTwoGroup.orbitData
import Submission.Work.CharCore.Main
import Submission.Work.Induction.All
import Submission.Work.Clifford.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausTwoGroup

open Submission.Blueprint
open Classical

set_option maxHeartbeats 1000000

/-! ## Coercions for subgroup elements -/

section Coercions

variable {G : Type} [Group G]

@[simp] theorem coe_inv_subtype {Q : Subgroup G} (g : ↥Q) : ((g⁻¹ : ↥Q) : G) = ((g : G))⁻¹ := rfl
@[simp] theorem coe_mul_subtype {Q : Subgroup G} (g h : ↥Q) :
    ((g * h : ↥Q) : G) = (g : G) * (h : G) := rfl

end Coercions

/-- The value of the conjugation automorphism of `Q` attached to `g ∈ N_G(Q)`. -/
theorem normalizerMonoidHom_coe {G : Type} [Group G] (Q : Subgroup G)
    (g : ↥(Subgroup.normalizer (Q : Set G))) (q : ↥Q) :
    (((Subgroup.normalizerMonoidHom Q g) q : ↥Q) : G) = (g : G) * (q : G) * (g : G)⁻¹ := rfl


/-! ## Orbit sums of irreducible characters -/

section OrbitSum

variable {G : Type} [Group G] [Fintype G]

/-- The inner product of the `D`-orbit sum `∑_{d ∈ D} ζ^d` of an irreducible character with an
irreducible character `ψ` is the number of `d` with `ζ^d = ψ` (as a complex number). -/
theorem cfInner_orbitSum {H Q : Subgroup G} [Fintype ↥Q] {t : G} (h : IsSplitRankOne H Q t)
    {η ψ : ↥Q → ℂ} (hη : η ∈ Work.Clifford.Irr ↥Q) (hψ : ψ ∈ Work.Clifford.Irr ↥Q) :
    Work.CharCore.cfInner (∑ d : ↥(twoPoint H t), conjIrrD h d η) ψ
      = ((Finset.univ.filter (fun d : ↥(twoPoint H t) => conjIrrD h d η = ψ)).card : ℂ) := by
  classical
  rw [Work.CharCore.cfInner_sum_left]
  have hterm : ∀ d : ↥(twoPoint H t),
      Work.CharCore.cfInner (conjIrrD h d η) ψ
        = (if conjIrrD h d η = ψ then (1 : ℂ) else 0) := by
    intro d
    exact Work.CharCore.irr_orthonormal _ _ (charCore_mem_iff_clifford _ |>.mpr
      (conjIrrD_mem_Irr h d hη)) (charCore_mem_iff_clifford _ |>.mpr hψ)
  rw [Finset.sum_congr rfl (fun d _ => hterm d)]
  rw [Finset.sum_boole]

end OrbitSum

/-! ## Injectivity of induction on the non-trivial irreducible characters -/

section Injectivity

variable {G : Type} [Group G] [Fintype G]

/-- The inversion bijection of a group, used to reindex sums over `D`. -/
private def invEquiv (α : Type) [Group α] : α ≃ α where
  toFun a := a⁻¹
  invFun a := a⁻¹
  left_inv a := by simp
  right_inv a := by simp

/-- `∑_{d ∈ D} ζ^d` takes the value `0` at the trivial character when `ζ ≠ 1`. -/
theorem cfInner_orbitSum_principal {H Q : Subgroup G} [Fintype ↥Q] {t : G} (h : IsSplitRankOne H Q t)
    {η : ↥Q → ℂ} (hη : η ∈ Work.Clifford.Irr ↥Q) (hη1 : η ≠ 1) :
    Work.CharCore.cfInner (∑ d : ↥(twoPoint H t), conjIrrD h d η)
      (Work.Clifford.principalChar ↥Q) = 0 := by
  classical
  rw [cfInner_orbitSum h hη (Work.Clifford.principalChar_mem_Irr (G := ↥Q))]
  have hone : (1 : ↥Q → ℂ) = Work.Clifford.principalChar ↥Q := by
    ext x
    rfl
  have hfilter : (Finset.univ.filter
      (fun d : ↥(twoPoint H t) => conjIrrD h d η = Work.Clifford.principalChar ↥Q)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro d _
    rw [← hone, conjIrrD_eq_one_iff]
    exact hη1
  rw [hfilter]
  simp

/-- **Injectivity of `ζ ↦ Ind_Q^G ζ` modulo `D`-conjugation, for non-trivial irreducible
characters of `Q`.** -/
theorem indFun_inj_of_mem_Irr {H Q : Subgroup G} [Fintype ↥Q] {t : G}
    (h : IsSplitRankOne H Q t)
    (hval : ∀ (ζ : ↥Q → ℂ), Work.CharCore.IsClassFun ζ → ∀ q : ↥Q, q ≠ 1 →
      Work.Induction.indFun Q ζ (q : G)
        = ∑ d : ↥(twoPoint H t), ζ (conjQD h d q))
    {ζ ζ' : ↥Q → ℂ} (hζ : ζ ∈ Work.Clifford.Irr ↥Q) (hζ' : ζ' ∈ Work.Clifford.Irr ↥Q)
    (hζ1 : ζ ≠ 1) (hζ'1 : ζ' ≠ 1)
    (heq : Work.Induction.indFun Q ζ = Work.Induction.indFun Q ζ') :
    ∃ d : ↥(twoPoint H t), ζ' = conjIrrD h d ζ := by
  classical
  have hζc : Work.CharCore.IsClassFun ζ := Work.Clifford.IsClassFun.of_mem_Irr hζ
  have hζc' : Work.CharCore.IsClassFun ζ' := Work.Clifford.IsClassFun.of_mem_Irr hζ'
  set F₁ : ↥Q → ℂ := ∑ d : ↥(twoPoint H t), conjIrrD h d ζ with hF₁
  set F₂ : ↥Q → ℂ := ∑ d : ↥(twoPoint H t), conjIrrD h d ζ' with hF₂
  -- 1. `F₁` and `F₂` agree off `1`
  have hoff : ∀ q : ↥Q, q ≠ 1 → F₁ q = F₂ q := by
    intro q hq
    have h₁ : F₁ q = ∑ e : ↥(twoPoint H t), ζ (conjQD h e q) := by
      rw [hF₁, Finset.sum_apply]
      refine Eq.trans (Finset.sum_congr rfl (fun d _ => conjIrrD_apply h d ζ q)) ?_
      exact Fintype.sum_equiv (invEquiv ↥(twoPoint H t)) _ _ (fun d => rfl)
    have h₂ : F₂ q = ∑ e : ↥(twoPoint H t), ζ' (conjQD h e q) := by
      rw [hF₂, Finset.sum_apply]
      refine Eq.trans (Finset.sum_congr rfl (fun d _ => conjIrrD_apply h d ζ' q)) ?_
      exact Fintype.sum_equiv (invEquiv ↥(twoPoint H t)) _ _ (fun d => rfl)
    rw [h₁, h₂, ← hval ζ hζc q hq, ← hval ζ' hζc' q hq]
    exact congrFun heq (q : G)
  -- 2. `F₁ - F₂` is concentrated at `1`
  have hsub : F₁ - F₂
      = (F₁ 1 - F₂ 1) • (fun q : ↥Q => if q = 1 then (1 : ℂ) else 0) := by
    funext q
    by_cases hq : q = 1
    · subst hq
      simp
    · rw [Pi.sub_apply, hoff q hq]
      simp [hq]
  -- 3. the inner products with the trivial character vanish
  have hone : (1 : ↥Q → ℂ) = Work.Clifford.principalChar ↥Q := by
    ext x
    rfl
  have htriv₁ : Work.CharCore.cfInner F₁ (1 : ↥Q → ℂ) = 0 := by
    rw [hone, hF₁]
    exact cfInner_orbitSum_principal h hζ hζ1
  have htriv₂ : Work.CharCore.cfInner F₂ (1 : ↥Q → ℂ) = 0 := by
    rw [hone, hF₂]
    exact cfInner_orbitSum_principal h hζ' hζ'1
  -- 4. the inner product of the indicator of `1` with the trivial character
  have hdelta : Work.CharCore.cfInner (fun q : ↥Q => if q = 1 then (1 : ℂ) else 0)
      (1 : ↥Q → ℂ) = ((Nat.card ↥Q : ℂ))⁻¹ := by
    rw [Work.CharCore.cfInner_apply, Nat.card_eq_fintype_card]
    have h1 : (∑ x : ↥Q,
        (if x = 1 then (1 : ℂ) else 0) * starRingEnd ℂ ((1 : ↥Q → ℂ) x)) = 1 := by
      rw [Finset.sum_eq_single (1 : ↥Q)]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hcon
        exact absurd (Finset.mem_univ (1 : ↥Q)) hcon
    rw [h1, mul_one]
  -- 5. the two constants agree
  have hc : F₁ 1 - F₂ 1 = 0 := by
    have h₂ := congrArg (fun f : ↥Q → ℂ => Work.CharCore.cfInner f (1 : ↥Q → ℂ)) hsub
    rw [Work.CharCore.cfInner_sub_left, htriv₁, htriv₂, sub_zero,
      Work.CharCore.cfInner_smul_left, hdelta] at h₂
    rcases mul_eq_zero.mp h₂.symm with h3 | h3
    · exact h3
    · exact absurd h3 (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)))
  have hFeq : F₁ = F₂ := by
    have hzero : F₁ - F₂ = 0 := by
      rw [hsub, hc]
      simp
    exact sub_eq_zero.mp hzero
  -- 6. count the orbit of `ζ`
  have hcount₁ : Work.CharCore.cfInner F₁ ζ
      = ((Finset.univ.filter (fun d : ↥(twoPoint H t) => conjIrrD h d ζ = ζ)).card : ℂ) := by
    rw [hF₁]
    exact cfInner_orbitSum h hζ hζ
  have hcount₂ : Work.CharCore.cfInner F₂ ζ
      = ((Finset.univ.filter (fun d : ↥(twoPoint H t) => conjIrrD h d ζ' = ζ)).card : ℂ) := by
    rw [hF₂]
    exact cfInner_orbitSum h hζ' hζ
  have hpos : 0 < (Finset.univ.filter (fun d : ↥(twoPoint H t) =>
      conjIrrD h d ζ = ζ)).card := by
    refine Finset.card_pos.mpr ⟨1, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ 1, conjIrrD_one h ζ⟩
  have hne : (Finset.univ.filter (fun d : ↥(twoPoint H t) =>
      conjIrrD h d ζ' = ζ)).Nonempty := by
    rw [← Finset.card_pos]
    have hcard : (Finset.univ.filter (fun d : ↥(twoPoint H t) =>
          conjIrrD h d ζ = ζ)).card
        = (Finset.univ.filter (fun d : ↥(twoPoint H t) =>
          conjIrrD h d ζ' = ζ)).card := by
      have hcast : ((Finset.univ.filter (fun d : ↥(twoPoint H t) =>
            conjIrrD h d ζ = ζ)).card : ℂ)
          = ((Finset.univ.filter (fun d : ↥(twoPoint H t) =>
            conjIrrD h d ζ' = ζ)).card : ℂ) := by
        rw [← hcount₁, ← hcount₂, hFeq]
      exact Nat.cast_injective hcast
    rw [← hcard]
    exact hpos
  obtain ⟨d, hd⟩ := hne
  rw [Finset.mem_filter] at hd
  refine ⟨d⁻¹, ?_⟩
  have h2 := congrArg (conjIrrD h d⁻¹) hd.2
  rwa [conjIrrD_inv_conjIrrD] at h2

end Injectivity

/-! ## `H`-classes inside `Q` and orbits of `N_G(Q)` on the classes of `Q` -/

section HClasses

variable {G : Type} [Group G] [Fintype G]

/-- The action of `N_G(Q)` on `Q` is conjugation. -/
theorem normalizer_smul_Q (Q : Subgroup G)
    (g : ↥(Subgroup.normalizer (Q : Set G))) (x : ↥Q) :
    g • x = Subgroup.normalizerMonoidHom Q g x := Subtype.ext rfl

/-- The action of `N_G(Q)` on `Q` and on its conjugacy classes are compatible. -/
theorem normalizer_smul_conjClasses (Q : Subgroup G)
    (g : ↥(Subgroup.normalizer (Q : Set G))) (x : ↥Q) :
    g • ConjClasses.mk x = ConjClasses.mk (g • x) := by
  rw [instMAConjClasses_smul, Work.Clifford.conjClasses_map_mk]
  congr 1

/-- **The `H`-classes of `H` meeting `Q` are the orbits of `N_G(Q)` on the conjugacy classes of
`Q`.** -/
theorem card_hClasses_eq_card_normalizerOrbits {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) :
    Nat.card {c : ConjClasses ↥H // ∃ x ∈ c.carrier, (x : G) ∈ Q}
      = Nat.card (Quotient (MulAction.orbitRel ↥(Subgroup.normalizer (Q : Set G))
          (ConjClasses ↥Q))) := by
  classical
  let repr : {c : ConjClasses ↥H // ∃ x ∈ c.carrier, (x : G) ∈ Q} → ↥H :=
    fun c => Classical.choose c.2
  have repr_mem : ∀ c, repr c ∈ c.1.carrier ∧ ((repr c : G) ∈ Q) :=
    fun c => Classical.choose_spec c.2
  have c_eq : ∀ c, c.1 = ConjClasses.mk (repr c) :=
    fun c => (ConjClasses.mem_carrier_iff_mk_eq.mp (repr_mem c).1).symm
  let xq : {c : ConjClasses ↥H // ∃ x ∈ c.carrier, (x : G) ∈ Q} → ↥Q :=
    fun c => ⟨(repr c : G), (repr_mem c).2⟩
  have xq_coe : ∀ c, (xq c : G) = (repr c : G) := fun c => rfl
  let Φ : {c : ConjClasses ↥H // ∃ x ∈ c.carrier, (x : G) ∈ Q} →
      Quotient (MulAction.orbitRel ↥(Subgroup.normalizer (Q : Set G)) (ConjClasses ↥Q)) :=
    fun c => Quotient.mk _ (ConjClasses.mk (xq c))
  have hsurj : Function.Surjective Φ := by
    intro q
    obtain ⟨C, hC⟩ := Quotient.exists_rep q
    obtain ⟨x, hx⟩ := ConjClasses.exists_rep C
    set xH : ↥H := ⟨(x : G), h.le x.2⟩ with hxH
    set c₀ : {c : ConjClasses ↥H // ∃ x ∈ c.carrier, (x : G) ∈ Q} :=
      ⟨ConjClasses.mk xH, ⟨xH, ConjClasses.mem_carrier_mk, x.2⟩⟩ with hc₀
    refine ⟨c₀, ?_⟩
    show Quotient.mk _ (ConjClasses.mk (xq c₀)) = q
    rw [← hC, ← hx]
    have hmem : repr c₀ ∈ (ConjClasses.mk xH).carrier := by
      have h1 := (repr_mem c₀).1
      rwa [hc₀] at h1
    have hisconj : IsConj (repr c₀) xH :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (ConjClasses.mem_carrier_iff_mk_eq.mp hmem)
    obtain ⟨k, hk⟩ := isConj_iff.mp hisconj
    have hkG : (k : G) * (repr c₀ : G) * (k : G)⁻¹ = (x : G) := by
      have h2 := congrArg (fun y : ↥H => (y : G)) hk
      rwa [hxH, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    have hkG' : (k : G)⁻¹ * (x : G) * (k : G) = (repr c₀ : G) := by
      have h3 : (k : G)⁻¹ * ((k : G) * (repr c₀ : G) * (k : G)⁻¹) * (k : G)
          = (repr c₀ : G) := by group
      rw [hkG] at h3
      exact h3
    refine Quotient.sound
      (s := MulAction.orbitRel ↥(Subgroup.normalizer (Q : Set G)) (ConjClasses ↥Q))
      ⟨⟨(k : G)⁻¹, (Subgroup.normalizer (Q : Set G)).inv_mem (h.normal k.2)⟩, ?_⟩
    change (⟨(k : G)⁻¹, (Subgroup.normalizer (Q : Set G)).inv_mem (h.normal k.2)⟩
        : ↥(Subgroup.normalizer (Q : Set G))) • ConjClasses.mk x
      = ConjClasses.mk (xq c₀)
    rw [normalizer_smul_conjClasses]
    congr 1
    apply Subtype.ext
    rw [normalizer_smul_Q, normalizerMonoidHom_coe, xq_coe]
    simpa only [inv_inv] using hkG'
  have hinj : Function.Injective Φ := by
    intro c c' hcc'
    have hrel := Quotient.exact hcc'
    obtain ⟨g, hg⟩ := hrel
    have hgs : g • ConjClasses.mk (xq c') = ConjClasses.mk (xq c) := hg
    rw [normalizer_smul_conjClasses] at hgs
    have hisconj : IsConj (g • xq c') (xq c) := ConjClasses.mk_eq_mk_iff_isConj.mp hgs
    obtain ⟨n, hn⟩ := isConj_iff.mp hisconj
    have hgQ : ((g • xq c' : ↥Q) : G) = (g : G) * (xq c' : G) * (g : G)⁻¹ := by
      rw [normalizer_smul_Q, normalizerMonoidHom_coe]
    have hnG : (n : G) * ((g : G) * (xq c' : G) * (g : G)⁻¹) * (n : G)⁻¹ = (xq c : G) := by
      have h2 := congrArg (fun y : ↥Q => (y : G)) hn
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
      rw [hgQ] at h2
      exact h2
    by_cases h1 : (xq c' : G) = 1
    · have h2 : (xq c : G) = 1 := by
        rw [h1] at hnG
        simpa using hnG.symm
      apply Subtype.ext
      rw [c_eq c, c_eq c']
      congr 1
      apply Subtype.ext
      rw [← xq_coe c, ← xq_coe c', h2, h1]
    · have hgH : (g : G) ∈ H := by
        refine conj_mem_Q_iff h (xq c').2 h1 (g : G) ?_
        have h3 := (g • xq c').2
        rwa [normalizer_smul_Q, normalizerMonoidHom_coe] at h3
      apply Subtype.ext
      rw [c_eq c, c_eq c']
      symm
      refine ConjClasses.mk_eq_mk_iff_isConj.mpr ?_
      refine isConj_iff.mpr ⟨⟨(n : G) * (g : G), H.mul_mem (h.le n.2) hgH⟩, ?_⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (n : G) * (g : G) * (repr c' : G) * ((n : G) * (g : G))⁻¹
          = (n : G) * ((g : G) * (repr c' : G) * (g : G)⁻¹) * (n : G)⁻¹ := by group
        _ = (n : G) * ((g : G) * (xq c' : G) * (g : G)⁻¹) * (n : G)⁻¹ := by rw [xq_coe c']
        _ = (xq c : G) := hnG
        _ = (repr c : G) := xq_coe c
  exact Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)

end HClasses

/-! ## Feit's value formula for class functions -/

section ValueFormula

variable {G : Type} [Group G] [Fintype G]

/-- Feit's value formula `Ind_Q^G ζ(q) = ∑_{d ∈ D} ζ (d q d⁻¹)` for `1 ≠ q ∈ Q` and an
arbitrary class function `ζ` on `Q`. -/
theorem indFun_Q_apply_mem_Q_classFun {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (ζ : ↥Q → ℂ) (hζ : Work.CharCore.IsClassFun ζ) {q : ↥Q}
    (hq : q ≠ 1) :
    Work.Induction.indFun Q ζ (q : G)
      = ∑ d : ↥(twoPoint H t), ζ (conjQD h d q) := by
  have hqG : (q : G) ≠ 1 := fun hh => hq (Subtype.ext hh)
  have hcard : (Nat.card Q : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  rw [Work.Induction.indFun_apply_def]
  have hstep : ∀ x : G,
      (if hx : x * (q : G) * x⁻¹ ∈ Q then ζ ⟨x * (q : G) * x⁻¹, hx⟩ else 0)
      = (if hx : x ∈ H then ζ (conjQ h ⟨x, hx⟩ q) else 0) := by
    intro x
    by_cases hxH : x ∈ H
    · have hxQ : x * (q : G) * x⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (h.normal hxH) (q : G)).mp q.2
      rw [dite_eq_left hxQ, dite_eq_left hxH]
      exact congrArg ζ (Subtype.ext rfl)
    · have hxQ : x * (q : G) * x⁻¹ ∉ Q :=
        fun hc => hxH (conj_mem_Q_iff h q.2 hqG x hc)
      rw [dite_eq_right hxQ, dite_eq_right hxH]
  rw [Finset.sum_congr rfl (fun x _ => hstep x)]
  rw [Work.Induction.sum_dite_mem_subgroup H (fun y : ↥H => ζ (conjQ h y q))]
  rw [sum_H_eq h (fun y : ↥H => ζ (conjQ h y q))]
  have hinner : ∀ a : ↥Q,
      (∑ d : ↥(twoPoint H t), ζ (conjQ h (qdEquiv h (a, d)) q))
      = ∑ d : ↥(twoPoint H t), ζ (conjQD h d q) := by
    intro a
    refine Finset.sum_congr rfl (fun d _ => ?_)
    have hconj : conjQ h (qdEquiv h (a, d)) q = a * conjQD h d q * a⁻¹ := by
      apply Subtype.ext
      simp only [conjQ_coe, qdEquiv_coe, conjQD_coe, coe_mul_subtype, coe_inv_subtype]
      group
    rw [hconj]
    exact hζ (conjQD h d q) a
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  have hsum : (∑ _a : ↥Q, ∑ d : ↥(twoPoint H t), ζ (conjQD h d q))
      = (Nat.card Q : ℂ) * ∑ d : ↥(twoPoint H t), ζ (conjQD h d q) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end ValueFormula

/-! ## Conjugation by the normaliser and invariance of `indFun` -/

section NormalizerConj

variable {G : Type} [Group G]


theorem normalizerMonoidHom_symm_coe (Q : Subgroup G)
    (g : ↥(Subgroup.normalizer (Q : Set G))) (q : ↥Q) :
    (((Subgroup.normalizerMonoidHom Q g).symm q : ↥Q) : G) = (g : G)⁻¹ * (q : G) * (g : G) := by
  have h1 : (Subgroup.normalizerMonoidHom Q g).symm = Subgroup.normalizerMonoidHom Q g⁻¹ := by
    rw [← MulAut.inv_def, map_inv]
  rw [h1, normalizerMonoidHom_coe]
  simp

theorem inv_mem_normalizer (Q : Subgroup G) (g : ↥(Subgroup.normalizer (Q : Set G))) :
    (g : G)⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
  (Subgroup.normalizer (Q : Set G)).inv_mem g.2

theorem normalizerConjFun_eq_conjFun (Q : Subgroup G)
    (g : ↥(Subgroup.normalizer (Q : Set G))) (ζ : ↥Q → ℂ) :
    normalizerConjFun Q g ζ = Work.Induction.conjFun Q ⟨(g : G)⁻¹, inv_mem_normalizer Q g⟩ ζ := by
  ext q
  rw [normalizerConjFun_apply, Work.Induction.conjFun_apply]
  congr 1

theorem indFun_normalizerConjFun (Q : Subgroup G) [Fintype G]
    (g : ↥(Subgroup.normalizer (Q : Set G))) (ζ : ↥Q → ℂ) :
    Work.Induction.indFun Q (normalizerConjFun Q g ζ) = Work.Induction.indFun Q ζ := by
  rw [normalizerConjFun_eq_conjFun]
  exact Work.Induction.indFun_conjFun Q _ ζ

theorem indFun_conjIrrD {H Q : Subgroup G} [Fintype ↥Q] {t : G} (h : IsSplitRankOne H Q t)
    [Fintype G] (d : ↥(twoPoint H t)) (ζ : ↥Q → ℂ) :
    Work.Induction.indFun Q (conjIrrD h d ζ) = Work.Induction.indFun Q ζ := by
  rw [conjIrrD_eq_normalizerConjFun]
  exact indFun_normalizerConjFun Q (dToNormalizer h d) ζ

end NormalizerConj




/-! ## Assembly of the count -/

section Assembly

variable {G : Type} [Group G] [Fintype G]

/-- The inner product of the indicator of `1` with a function on `Q`. -/
theorem cfInner_delta (Q : Subgroup G) [Fintype ↥Q] (ψ : ↥Q → ℂ) :
    Work.CharCore.cfInner (fun q : ↥Q => if q = 1 then (1 : ℂ) else 0) ψ
      = (Nat.card ↥Q : ℂ)⁻¹ * starRingEnd ℂ (ψ 1) := by
  rw [Work.CharCore.cfInner_apply, Nat.card_eq_fintype_card]
  have h1 : (∑ x : ↥Q, (if x = 1 then (1 : ℂ) else 0) * starRingEnd ℂ (ψ x))
      = starRingEnd ℂ (ψ 1) := by
    rw [Finset.sum_eq_single (1 : ↥Q)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hcon
      exact absurd (Finset.mem_univ (1 : ↥Q)) hcon
  rw [h1]

/-- The image of a function is the quotient of its domain by the kernel relation. -/
noncomputable def equivRangeQuotientKer {α β : Type*} (f : α → β) :
    Set.range f ≃ Quotient (Setoid.ker f) where
  toFun w := Quotient.mk _ w.2.choose
  invFun q := Quotient.liftOn q (fun a => (⟨f a, a, rfl⟩ : Set.range f))
    (fun a b hab => Subtype.ext hab)
  left_inv w := by
    apply Subtype.ext
    exact w.2.choose_spec
  right_inv q := by
    induction q using Quotient.ind
    refine Quotient.sound ?_
    exact (⟨f ‹_›, ‹_›, rfl⟩ : Set.range f).2.choose_spec

/-- The irreducible characters of `Q`, as a type. -/
abbrev IrrT (Q : Subgroup G) [Fintype ↥Q] : Type := {ζ : ↥Q → ℂ // ζ ∈ Work.Clifford.Irr ↥Q}

/-- The trivial character of `Q` is an irreducible character. -/
theorem one_mem_cliffordIrr (Q : Subgroup G) [Fintype ↥Q] :
    (1 : ↥Q → ℂ) ∈ Work.Clifford.Irr ↥Q := by
  have h : (1 : ↥Q → ℂ) = Work.Clifford.principalChar ↥Q := funext fun x => rfl
  rw [h]
  exact Work.Clifford.principalChar_mem_Irr (G := ↥Q)

/-- The trivial character of `Q`. -/
noncomputable def trivIrr (Q : Subgroup G) [Fintype ↥Q] : IrrT Q :=
  ⟨1, one_mem_cliffordIrr Q⟩

/-- **The trivial character is alone in its fibre of `ζ ↦ Ind_Q^G ζ`.** -/
theorem indFun_ne_indFun_one {H Q : Subgroup G} [Fintype ↥Q] {t : G} (h : IsSplitRankOne H Q t)
    (hval : ∀ (ζ : ↥Q → ℂ), Work.CharCore.IsClassFun ζ → ∀ q : ↥Q, q ≠ 1 →
      Work.Induction.indFun Q ζ (q : G)
        = ∑ d : ↥(twoPoint H t), ζ (conjQD h d q))
    {ζ : ↥Q → ℂ} (hζ : ζ ∈ Work.Clifford.Irr ↥Q) (hζ1 : ζ ≠ 1) :
    Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q (1 : ↥Q → ℂ) := by
  classical
  intro heq
  have hζc : Work.CharCore.IsClassFun ζ := Work.Clifford.IsClassFun.of_mem_Irr hζ
  have honec : Work.CharCore.IsClassFun (1 : ↥Q → ℂ) :=
    Work.Clifford.IsClassFun.of_mem_Irr (one_mem_cliffordIrr Q)
  set F₁ : ↥Q → ℂ := ∑ d : ↥(twoPoint H t), conjIrrD h d ζ with hF₁
  set F₂ : ↥Q → ℂ := ∑ d : ↥(twoPoint H t), conjIrrD h d (1 : ↥Q → ℂ) with hF₂
  have hF₂c : F₂ = (Nat.card ↥(twoPoint H t) : ℂ) • (1 : ↥Q → ℂ) := by
    funext q
    rw [hF₂, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun d _ => by rw [conjIrrD_const_one])]
    simp
  have hoff : ∀ q : ↥Q, q ≠ 1 → F₁ q = F₂ q := by
    intro q hq
    have h1 : F₁ q = ∑ e : ↥(twoPoint H t), ζ (conjQD h e q) := by
      rw [hF₁, Finset.sum_apply]
      refine Eq.trans (Finset.sum_congr rfl (fun d _ => conjIrrD_apply h d ζ q)) ?_
      exact Fintype.sum_equiv (invEquiv ↥(twoPoint H t)) _ _ (fun d => rfl)
    have h2 : F₂ q = ∑ e : ↥(twoPoint H t), (1 : ↥Q → ℂ) (conjQD h e q) := by
      rw [hF₂, Finset.sum_apply]
      refine Eq.trans (Finset.sum_congr rfl
        (fun d _ => conjIrrD_apply h d (1 : ↥Q → ℂ) q)) ?_
      exact Fintype.sum_equiv (invEquiv ↥(twoPoint H t)) _ _ (fun d => rfl)
    rw [h1, h2, ← hval ζ hζc q hq, ← hval (1 : ↥Q → ℂ) honec q hq]
    exact congrFun heq (q : G)
  have hsub : F₁ - F₂
      = (F₁ 1 - F₂ 1) • (fun q : ↥Q => if q = 1 then (1 : ℂ) else 0) := by
    funext q
    by_cases hq : q = 1
    · subst hq
      simp
    · rw [Pi.sub_apply, hoff q hq]
      simp [hq]
  -- inner products
  have h1_1 : Work.CharCore.cfInner F₁ (1 : ↥Q → ℂ) = 0 := by
    rw [hF₁]
    exact cfInner_orbitSum_principal h hζ hζ1
  have h2_1 : Work.CharCore.cfInner F₂ (1 : ↥Q → ℂ)
      = (Nat.card ↥(twoPoint H t) : ℂ) := by
    rw [hF₂c, Work.CharCore.cfInner_smul_left]
    rw [Work.CharCore.irr_orthonormal _ _ (charCore_mem_iff_clifford _ |>.mpr
      (one_mem_cliffordIrr Q)) (charCore_mem_iff_clifford _ |>.mpr (one_mem_cliffordIrr Q))]
    rw [if_pos rfl, mul_one]
  have h1_ζ : Work.CharCore.cfInner F₁ ζ
      = ((Finset.univ.filter (fun d : ↥(twoPoint H t) => conjIrrD h d ζ = ζ)).card : ℂ) := by
    rw [hF₁]
    exact cfInner_orbitSum h hζ hζ
  have h2_ζ : Work.CharCore.cfInner F₂ ζ = 0 := by
    rw [hF₂c, Work.CharCore.cfInner_smul_left]
    rw [Work.CharCore.irr_orthonormal _ _ (charCore_mem_iff_clifford _ |>.mpr
      (one_mem_cliffordIrr Q)) (charCore_mem_iff_clifford _ |>.mpr hζ)]
    rw [if_neg (fun h : (1 : ↥Q → ℂ) = ζ => hζ1 h.symm), mul_zero]
  have hq : (Nat.card ↥Q : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hc : F₁ 1 - F₂ 1 = -((Nat.card ↥(twoPoint H t) : ℂ) * (Nat.card ↥Q : ℂ)) := by
    have h₂ := congrArg (fun f : ↥Q → ℂ => Work.CharCore.cfInner f (1 : ↥Q → ℂ)) hsub
    rw [Work.CharCore.cfInner_sub_left, h1_1, h2_1, zero_sub,
      Work.CharCore.cfInner_smul_left, cfInner_delta Q (1 : ↥Q → ℂ)] at h₂
    simp only [Pi.one_apply, map_one, mul_one] at h₂
    have h₃ := congrArg (fun x : ℂ => x * (Nat.card ↥Q : ℂ)) h₂
    rw [mul_assoc, inv_mul_cancel₀ hq, mul_one] at h₃
    rw [← h₃]
    ring_nf
  have hm : ((Finset.univ.filter (fun d : ↥(twoPoint H t) => conjIrrD h d ζ = ζ)).card : ℂ)
      = -((Nat.card ↥(twoPoint H t) : ℂ) * (Work.CharCore.irrDeg ζ : ℂ)) := by
    have h₂ := congrArg (fun f : ↥Q → ℂ => Work.CharCore.cfInner f ζ) hsub
    rw [Work.CharCore.cfInner_sub_left, h1_ζ, h2_ζ, sub_zero,
      Work.CharCore.cfInner_smul_left, cfInner_delta Q ζ] at h₂
    have hdeg : ζ 1 = (Work.CharCore.irrDeg ζ : ℂ) :=
      Work.CharCore.irrDeg_spec (charCore_mem_iff_clifford ζ |>.mpr hζ)
    rw [hdeg] at h₂
    simp only [map_natCast] at h₂
    rw [hc] at h₂
    rw [h₂]
    field_simp
  have hk : 0 < (Finset.univ.filter (fun d : ↥(twoPoint H t) => conjIrrD h d ζ = ζ)).card := by
    refine Finset.card_pos.mpr ⟨1, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ 1, conjIrrD_one h ζ⟩
  have hnat : (((Finset.univ.filter (fun d : ↥(twoPoint H t) =>
        conjIrrD h d ζ = ζ)).card : ℂ)
      + ((Nat.card ↥(twoPoint H t) * Work.CharCore.irrDeg ζ : ℕ) : ℂ)) = 0 := by
    rw [hm]
    push_cast
    ring
  have hzero : (Finset.univ.filter (fun d : ↥(twoPoint H t) => conjIrrD h d ζ = ζ)).card
      + Nat.card ↥(twoPoint H t) * Work.CharCore.irrDeg ζ = 0 := by
    exact_mod_cast hnat
  omega

end Assembly



/-! ## Counting the fibres of `ζ ↦ Ind_Q^G ζ` -/

section Counting

variable {G : Type} [Group G] [Fintype G]

/-- The kernel of `ζ ↦ Ind_Q^G ζ` on the irreducible characters of `Q` is the orbit relation of
the conjugation action of `N_G(Q)`. -/
theorem ker_indFun_eq_orbitRel {H Q : Subgroup G} [Fintype ↥Q] {t : G} (h : IsSplitRankOne H Q t)
    (hval : ∀ (ζ : ↥Q → ℂ), Work.CharCore.IsClassFun ζ → ∀ q : ↥Q, q ≠ 1 →
      Work.Induction.indFun Q ζ (q : G)
        = ∑ d : ↥(twoPoint H t), ζ (conjQD h d q)) :
    Setoid.ker (fun ζ : IrrT Q => Work.Induction.indFun Q ζ.1)
      = MulAction.orbitRel ↥(Subgroup.normalizer (Q : Set G)) (IrrT Q) := by
  classical
  ext ζ ζ'
  constructor
  · intro hker
    have hker' : Work.Induction.indFun Q ζ.1 = Work.Induction.indFun Q ζ'.1 := hker
    by_cases h1 : ζ'.1 = 1
    · by_cases h2 : ζ.1 = 1
      · refine ⟨1, ?_⟩
        change (1 : ↥(Subgroup.normalizer (Q : Set G))) • ζ' = ζ
        rw [one_smul]
        exact Subtype.ext (by rw [h1, h2])
      · rw [h1] at hker'
        exact absurd hker' (indFun_ne_indFun_one h hval ζ.2 h2)
    · by_cases h2 : ζ.1 = 1
      · rw [h2] at hker'
        exact absurd hker'.symm (indFun_ne_indFun_one h hval ζ'.2 h1)
      · obtain ⟨d, hd⟩ := indFun_inj_of_mem_Irr h hval ζ.2 ζ'.2 h2 h1 hker'
        refine ⟨dToNormalizer h d⁻¹, ?_⟩
        apply Subtype.ext
        have h3 := congrArg (conjIrrD h d⁻¹) hd
        rw [conjIrrD_inv_conjIrrD] at h3
        exact h3
  · rintro ⟨g, hg⟩
    show Work.Induction.indFun Q ζ.1 = Work.Induction.indFun Q ζ'.1
    have hcoe : (g • ζ').1 = normalizerConjFun Q g ζ'.1 := rfl
    rw [← hg, hcoe]
    exact indFun_normalizerConjFun Q g ζ'.1

/-- The number of orbits of `N_G(Q)` on the irreducible characters of `Q` is the number of
distinct induced functions `Ind_Q^G ζ`. -/
theorem card_quotient_irr_eq_card_range {H Q : Subgroup G} [Fintype ↥Q] {t : G} (h : IsSplitRankOne H Q t)
    (hval : ∀ (ζ : ↥Q → ℂ), Work.CharCore.IsClassFun ζ → ∀ q : ↥Q, q ≠ 1 →
      Work.Induction.indFun Q ζ (q : G)
        = ∑ d : ↥(twoPoint H t), ζ (conjQD h d q)) :
    Nat.card (Quotient (MulAction.orbitRel ↥(Subgroup.normalizer (Q : Set G)) (IrrT Q)))
      = Nat.card (Set.range (fun ζ : IrrT Q => Work.Induction.indFun Q ζ.1)) := by
  rw [← ker_indFun_eq_orbitRel h hval]
  exact (Nat.card_congr (equivRangeQuotientKer
    (fun ζ : IrrT Q => Work.Induction.indFun Q ζ.1))).symm

/-- The image of `Ind_Q^G` on the non-trivial irreducible characters, computed on the finset
`(Work.CharCore.Irr ↥Q).filter (· ≠ 1)`. -/
theorem range_indFun_neOne_eq_image (Q : Subgroup G) [Fintype ↥Q] :
    Set.range (fun ζ : {ζ : ↥Q → ℂ // ζ ∈ Work.Clifford.Irr ↥Q ∧ ζ ≠ 1} =>
        Work.Induction.indFun Q ζ.1)
      = ↑(((Work.CharCore.Irr ↥Q).filter (fun ζ => ζ ≠ 1)).image
          (fun ζ => Work.Induction.indFun Q ζ)) := by
  ext y
  constructor
  · rintro ⟨ζ, rfl⟩
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨ζ.1, by
      rw [Finset.mem_filter]
      exact ⟨(charCore_mem_iff_clifford ζ.1).mpr ζ.2.1, ζ.2.2⟩, rfl⟩
  · intro hy
    rw [Finset.mem_coe, Finset.mem_image] at hy
    obtain ⟨ζ, hζ, rfl⟩ := hy
    rw [Finset.mem_filter] at hζ
    exact ⟨⟨ζ, (charCore_mem_iff_clifford ζ).mp hζ.1, hζ.2⟩, rfl⟩

/-- The image of `Ind_Q^G` on all of `Irr Q` is the image on the non-trivial characters together
with the value at the trivial character. -/
theorem range_indFun_eq_insert {H Q : Subgroup G} [Fintype ↥Q] {t : G} (h : IsSplitRankOne H Q t) :
    Set.range (fun ζ : IrrT Q => Work.Induction.indFun Q ζ.1)
      = insert (Work.Induction.indFun Q (1 : ↥Q → ℂ))
        ↑(((Work.CharCore.Irr ↥Q).filter (fun ζ => ζ ≠ 1)).image
          (fun ζ => Work.Induction.indFun Q ζ)) := by
  classical
  rw [← range_indFun_neOne_eq_image Q]
  ext y
  constructor
  · rintro ⟨ζ, rfl⟩
    by_cases h1 : ζ.1 = 1
    · refine Or.inl ?_
      show Work.Induction.indFun Q ζ.1 = Work.Induction.indFun Q (1 : ↥Q → ℂ)
      rw [h1]
    · exact Or.inr ⟨⟨ζ.1, ζ.2, h1⟩, rfl⟩
  · rintro (hy | ⟨ζ, rfl⟩)
    · exact ⟨trivIrr Q, hy.symm⟩
    · exact ⟨⟨ζ.1, ζ.2.1⟩, rfl⟩

/-- The trivial character gives a value of `Ind_Q^G` which is not attained on the non-trivial
irreducible characters. -/
theorem indFun_one_notMem_image {H Q : Subgroup G} [Fintype ↥Q] {t : G} (h : IsSplitRankOne H Q t)
    (hval : ∀ (ζ : ↥Q → ℂ), Work.CharCore.IsClassFun ζ → ∀ q : ↥Q, q ≠ 1 →
      Work.Induction.indFun Q ζ (q : G)
        = ∑ d : ↥(twoPoint H t), ζ (conjQD h d q)) :
    Work.Induction.indFun Q (1 : ↥Q → ℂ)
      ∉ (↑(((Work.CharCore.Irr ↥Q).filter (fun ζ => ζ ≠ 1)).image
          (fun ζ => Work.Induction.indFun Q ζ)) : Set (G → ℂ)) := by
  intro hy
  rw [← range_indFun_neOne_eq_image Q, Set.mem_range] at hy
  obtain ⟨ζ, hζ⟩ := hy
  exact indFun_ne_indFun_one h hval ζ.2.1 ζ.2.2 hζ

/-- Removing the trivial character removes exactly one value of `Ind_Q^G`. -/
theorem card_range_indFun_succ {H : Subgroup G} (Q : Subgroup G) [Fintype ↥Q] {t : G} (h : IsSplitRankOne H Q t)
    (hval : ∀ (ζ : ↥Q → ℂ), Work.CharCore.IsClassFun ζ → ∀ q : ↥Q, q ≠ 1 →
      Work.Induction.indFun Q ζ (q : G)
        = ∑ d : ↥(twoPoint H t), ζ (conjQD h d q)) :
    Nat.card (Set.range (fun ζ : IrrT Q => Work.Induction.indFun Q ζ.1))
      = Nat.card (↑(((Work.CharCore.Irr ↥Q).filter (fun ζ => ζ ≠ 1)).image
          (fun ζ => Work.Induction.indFun Q ζ)) : Set (G → ℂ)) + 1 := by
  classical
  rw [range_indFun_eq_insert h]
  rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem (indFun_one_notMem_image h hval)
    (Finset.finite_toSet _), Nat.card_coe_set_eq]

/-- The classes of `H` meeting `Q` are the classes meeting `Q ∖ 1` plus the class of `1`. -/
theorem card_classes_meets_succ {H Q : Subgroup G} :
    Nat.card {c : ConjClasses ↥H // ∃ x ∈ c.carrier, (x : G) ∈ Q ∧ x ≠ 1} + 1
      = Nat.card {c : ConjClasses ↥H // ∃ x ∈ c.carrier, (x : G) ∈ Q} := by
  classical
  have h₁ : Nat.card {c : ConjClasses ↥H // ∃ x ∈ c.carrier, (x : G) ∈ Q ∧ x ≠ 1}
      = (Finset.univ.filter (fun c : ConjClasses ↥H =>
          ∃ x ∈ c.carrier, (x : G) ∈ Q ∧ x ≠ 1)).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  have h₂ : Nat.card {c : ConjClasses ↥H // ∃ x ∈ c.carrier, (x : G) ∈ Q}
      = (Finset.univ.filter (fun c : ConjClasses ↥H =>
          ∃ x ∈ c.carrier, (x : G) ∈ Q)).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  rw [h₁, h₂]
  have hset : (Finset.univ.filter (fun c : ConjClasses ↥H => ∃ x ∈ c.carrier, (x : G) ∈ Q))
      = insert (ConjClasses.mk (1 : ↥H))
        (Finset.univ.filter (fun c : ConjClasses ↥H =>
          ∃ x ∈ c.carrier, (x : G) ∈ Q ∧ x ≠ 1)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨x, hx, hxQ⟩
      by_cases hx1 : x = 1
      · exact Or.inl (by rw [← ConjClasses.mem_carrier_iff_mk_eq.mp hx, hx1])
      · exact Or.inr ⟨x, hx, hxQ, hx1⟩
    · rintro (hceq | ⟨x, hx, hxQ, -⟩)
      · rw [hceq]
        exact ⟨1, ConjClasses.mem_carrier_mk, Q.one_mem⟩
      · exact ⟨x, hx, hxQ⟩
  have hnot : ConjClasses.mk (1 : ↥H) ∉
      (Finset.univ.filter (fun c : ConjClasses ↥H =>
        ∃ x ∈ c.carrier, (x : G) ∈ Q ∧ x ≠ 1)) := by
    rw [Finset.mem_filter]
    rintro ⟨-, x, hx, -, hx1⟩
    exact hx1 (isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp
      (ConjClasses.mem_carrier_iff_mk_eq.mp hx)))
  rw [hset, Finset.card_insert_of_notMem hnot]

end Counting

theorem card_H_classes_eq_card_induced {G : Type} [Group G] [Fintype G] (H Q : Subgroup G) [Fintype ↥Q] (t : G)
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H) :
    Nat.card {c : ConjClasses H // ∃ x ∈ c.carrier, (x : G) ∈ Q ∧ x ≠ 1} =
      Nat.card ((((Work.CharCore.Irr ↥Q).filter (fun ζ => ζ ≠ 1)).image
        (fun ζ => Work.Induction.indFun Q ζ)) : Set (G → ℂ)) := by
  classical
  have hval : ∀ (ζ : ↥Q → ℂ), Work.CharCore.IsClassFun ζ → ∀ q : ↥Q, q ≠ 1 →
      Work.Induction.indFun Q ζ (q : G)
        = ∑ d : ↥(twoPoint H t), ζ (conjQD h d q) :=
    fun ζ hζ q hq => indFun_Q_apply_mem_Q_classFun h ζ hζ hq
  refine Nat.succ.inj ?_
  rw [Nat.succ_eq_add_one]
  rw [card_classes_meets_succ (H := H) (Q := Q)]
  rw [card_hClasses_eq_card_normalizerOrbits (H := H) (Q := Q) h]
  rw [card_quotient_classes_eq_card_quotient_irr Q]
  rw [card_quotient_irr_eq_card_range (Q := Q) h hval]
  show Nat.card (Set.range (fun ζ : IrrT Q => Work.Induction.indFun Q ζ.1))
      = (Nat.card (↑(((Work.CharCore.Irr ↥Q).filter (fun ζ => ζ ≠ 1)).image
          (fun ζ => Work.Induction.indFun Q ζ)) : Set (G → ℂ))).succ
  exact card_range_indFun_succ (Q := Q) h hval

end Work.ZassenhausTwoGroup
