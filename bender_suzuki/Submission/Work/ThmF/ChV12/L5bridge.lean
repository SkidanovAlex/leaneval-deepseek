import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV12.Lemma5Defs
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.L5Struct
import Submission.Work.ThmF.ChV12.L5Aux
import Submission.Work.ThmF.ChV12.X5RankOneAux
import Submission.Work.ThmF.ChV12.L5crux
import Submission.Work.ThmF.ChV12.L5cruxAux
import Submission.Work.ThmF.Bender.cardInvertedMulCardCentralizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.L5bridge` — the crux from the classical closure statement

`Work.ThmF.ChV12.L5crux` (the single remaining input of `Work.ThmF.ChV12.lemma5`) is reduced here
to the classical statement `Work.ThmF.ChV12.SharpInvertingClosed`:

*an elementary abelian `2`-group `A` (`|A| = 2ⁿ`), a subgroup `D ≤ N(A)` of **odd** order acting
faithfully on `A`, a subset `K ⊆ D` of size `|A| - 1` containing `1` and acting **sharply
transitively** on `A ∖ {1}`, and an involution `τ` normalising `D` and inverting `K` elementwise
(`τ k τ = k⁻¹`) with `D = ⟨K⟩`: then `K·K ⊆ K`.*

Why this is exactly the crux (all steps below are proved, most in `L5cruxAux.lean`): in the case
`X5 H t = ⊤` one has `Q = Q0sub H`, `D = twoPoint H t = Ksub H t = ⟨Kset H t⟩` and — assuming
`V = centD H t ≠ ⊥` — `W = ⊥` and `D ⊓ C_G(Q0sub H) = ⊥`.  With
`A := Q0sub H` (elementary abelian, `|A| = |Inv H| + 1`), `K := Kset H t` (sharply transitive on
`A∖{1}` by `L5.Kset_regular`, `|K| = |Inv H| = |A| - 1` by `Bender.cardKsetEqInv`) and `τ := t`
(`t K t = K⁻¹`), the closure statement gives that `Kset H t` is a subgroup, i.e.
`Ksub H t = Kset H t`; but then `|Ksub| = |Kset| = |A| - 1` while
`|Ksub| = |D| = |V| · |Kset|` with `|V| ≥ 3` — a contradiction.  Hence `V = ⊥`, i.e. `L5crux`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV12

open Submission.Blueprint

/-- **The classical closure statement** (the remaining mathematical input), in group-theoretic
form so that it applies verbatim to `(A, D, K, τ) = (Q0sub H, Ksub H t, Kset H t, t)`. -/
def SharpInvertingClosed : Prop :=
  ∀ (G : Type) [Group G], ∀ (A D : Subgroup G) (K : Set G) (τ : G),
    (∀ x ∈ A, x * x = 1) →
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
    D ≤ Subgroup.normalizer (A : Set G) →
    Subgroup.closure K = D →
    K ⊆ (D : Set G) →
    (1 : G) ∈ K →
    (∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 → ∃! k : G, k ∈ K ∧ k * a * k⁻¹ = b) →
    K.ncard + 1 = Nat.card ↥A →
    Odd (Nat.card ↥D) →
    τ * τ = 1 →
    τ ∈ Subgroup.normalizer (D : Set G) →
    (∀ k ∈ K, τ * k * τ⁻¹ = k⁻¹) →
    D ⊓ Subgroup.centralizer (A : Set G) = ⊥ →
    ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ * k₂ ∈ K

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-- **The crux from the classical closure statement.** -/
theorem L5cruxProp_of_sharpInvertingClosed (h : SharpInvertingClosed) : L5cruxProp := by
  intro G _ _ H Q t s hC4 hyp hQ
  by_cases hX : Work.ThmF.Lemma5.X5 H t = ⊤
  · refine Or.inr ?_
    by_contra hV
    -- the case's structural facts
    have hDK : Submission.Blueprint.twoPoint H t = Work.ThmF.Ksub H t :=
      X5_eq_top_imp_twoPoint_eq_Ksub hC4 hyp hX
    have hW : Work.ThmF.W H t = ⊥ :=
      X5_eq_top_imp_centD_ne_bot_imp_W_eq_bot hC4 hyp hX hV
    have hcent : Submission.Blueprint.twoPoint H t ⊓
        Subgroup.centralizer (Work.ThmF.Q0sub H : Set G) = ⊥ :=
      X5_eq_top_imp_centD_ne_bot_imp_centralizer_eq_bot hC4 hyp hX hV
    -- the classical input
    have hcomm := Work.ThmF.L5.involutions_commute hyp.sit hC4 hyp.split
    have hAelem : ∀ x ∈ Work.ThmF.Q0sub H, x * x = 1 := by
      intro x hx
      have hxQ0 : x ∈ Work.ThmF.Q0 H := (Work.ThmF.L5.mem_Q0sub_iff hC4 hyp x).mp hx
      rcases Work.ThmF.mem_Q0_iff.mp hxQ0 with ⟨-, hord⟩ | rfl
      · have h2 : x ^ 2 = 1 := by
          have := pow_orderOf_eq_one x
          rwa [hord] at this
        simpa [pow_two] using h2
      · simp
    have hAcomm : ∀ x ∈ Work.ThmF.Q0sub H, ∀ y ∈ Work.ThmF.Q0sub H, x * y = y * x := by
      intro x hx y hy
      have hxI : x ∈ Work.ThmF.Q0 H := (Work.ThmF.L5.mem_Q0sub_iff hC4 hyp x).mp hx
      have hyI : y ∈ Work.ThmF.Q0 H := (Work.ThmF.L5.mem_Q0sub_iff hC4 hyp y).mp hy
      rcases Work.ThmF.mem_Q0_iff.mp hxI with hx' | rfl
      · rcases Work.ThmF.mem_Q0_iff.mp hyI with hy' | rfl
        · exact hcomm x hx' y hy'
        · simp
      · simp
    have hnormal : Work.ThmF.Ksub H t ≤
        Subgroup.normalizer (Work.ThmF.Q0sub H : Set G) :=
      Work.ThmF.L5.Ksub_le_normalizer_Q0sub hC4 hyp
    have hspan : Subgroup.closure (Work.ThmF.Kset H t) = Work.ThmF.Ksub H t := rfl
    have hKsub : (Work.ThmF.Kset H t : Set G) ⊆ (Work.ThmF.Ksub H t : Set G) :=
      Work.ThmF.Kset_le_Ksub H t
    have h1 : (1 : G) ∈ Work.ThmF.Kset H t := Work.ThmF.one_mem_Kset H t
    have hsharp : ∀ a ∈ Work.ThmF.Q0sub H, a ≠ 1 → ∀ b ∈ Work.ThmF.Q0sub H, b ≠ 1 →
        ∃! k : G, k ∈ Work.ThmF.Kset H t ∧ k * a * k⁻¹ = b := by
      intro a ha ha1 b hb hb1
      have haI : a ∈ involutions (H : Set G) := by
        have h0 := (Work.ThmF.L5.mem_Q0sub_iff hC4 hyp a).mp ha
        rcases Work.ThmF.mem_Q0_iff.mp h0 with h' | h'
        · exact h'
        · exact absurd h' ha1
      have hbI : b ∈ involutions (H : Set G) := by
        have h0 := (Work.ThmF.L5.mem_Q0sub_iff hC4 hyp b).mp hb
        rcases Work.ThmF.mem_Q0_iff.mp h0 with h' | h'
        · exact h'
        · exact absurd h' hb1
      exact Work.ThmF.L5.Kset_regular hyp.split a haI b hbI
    have hcard : (Work.ThmF.Kset H t).ncard + 1 = Nat.card ↥(Work.ThmF.Q0sub H) := by
      have h1 := Work.ThmF.L5.card_Q0sub_eq hcomm
      have h2 := Work.ThmF.Bender.cardKsetEqInv hyp.split.stronglyEmbedded hyp.split.invol
        hyp.split.not_mem
      omega
    have hodd : Odd (Nat.card ↥(Work.ThmF.Ksub H t)) := Work.ThmF.ChV12.L5oddKsub hyp
    have ht2 : t * t = 1 := Work.ThmF.L5.ht_mul_self hyp
    have htN : t ∈ Subgroup.normalizer ((Work.ThmF.Ksub H t) : Set G) := by
      rw [Subgroup.mem_normalizer_iff'']
      intro x
      constructor
      · intro hx
        rw [Work.ThmF.L5.ht_inv hyp]
        exact Work.ThmF.L5.t_conj_Ksub_mem hyp hx
      · intro hx
        have hthis : t * (t⁻¹ * x * t) * t ∈ Work.ThmF.Ksub H t :=
          Work.ThmF.L5.t_conj_Ksub_mem hyp hx
        have h2 : t * (t⁻¹ * x * t) * t = x := by
          calc t * (t⁻¹ * x * t) * t = (t * t⁻¹) * x * (t * t) := by group
            _ = 1 * x * 1 := by rw [mul_inv_cancel t, ht2]
            _ = x := by group
        rw [← h2]
        exact hthis
    have htinv : ∀ k ∈ Work.ThmF.Kset H t, t * k * t⁻¹ = k⁻¹ := by
      intro k hk
      rw [Work.ThmF.L5.ht_inv hyp]
      exact Work.ThmF.L5.t_conj_Kset hyp hk
    have hfaith : Work.ThmF.Ksub H t ⊓
        Subgroup.centralizer (Work.ThmF.Q0sub H : Set G) = ⊥ := by
      simpa [hDK] using hcent
    have hclosed : ∀ a b : G, a ∈ Work.ThmF.Kset H t → b ∈ Work.ThmF.Kset H t →
        a * b ∈ Work.ThmF.Kset H t := by
      intro a b ha hb
      exact h G (Work.ThmF.Q0sub H) (Work.ThmF.Ksub H t) (Work.ThmF.Kset H t) t
        hAelem hAcomm hnormal hspan hKsub h1 hsharp hcard hodd ht2 htN htinv hfaith a ha b hb
    -- hence `Kset H t` is a subgroup: every element of `Ksub H t` lies in `Kset H t`
    have hmem : ∀ x ∈ Work.ThmF.Ksub H t, x ∈ Work.ThmF.Kset H t := by
      intro x hx
      refine Subgroup.closure_induction (k := Work.ThmF.Kset H t)
        (p := fun y _ => y ∈ Work.ThmF.Kset H t) ?_ ?_ ?_ ?_ hx
      · intro y hy
        exact hy
      · exact h1
      · intro y z hy hz ihy ihz
        exact hclosed y z ihy ihz
      · intro y hy ihy
        exact Work.ThmF.L5.Kset_inv_mem hyp ihy
    have hcard_le : Nat.card ↥(Work.ThmF.Ksub H t) ≤ (Work.ThmF.Kset H t).ncard := by
      have hinj : Function.Injective (fun x : ↥(Work.ThmF.Ksub H t) =>
          (⟨(x : G), hmem (x : G) x.2⟩ : {y : G // y ∈ Work.ThmF.Kset H t})) := by
        intro x y hxy
        exact Subtype.ext (congrArg (fun z : {y : G // y ∈ Work.ThmF.Kset H t} => (z : G)) hxy)
      calc Nat.card ↥(Work.ThmF.Ksub H t)
          ≤ Nat.card {y : G // y ∈ Work.ThmF.Kset H t} :=
            Nat.card_le_card_of_injective
              (f := fun x : ↥(Work.ThmF.Ksub H t) =>
                (⟨(x : G), hmem (x : G) x.2⟩ : {y : G // y ∈ Work.ThmF.Kset H t})) hinj
        _ = (Work.ThmF.Kset H t).ncard := (Nat.card_coe_set_eq _).symm
    have hcard_eq : Nat.card ↥(Submission.Blueprint.twoPoint H t) = (Work.ThmF.Kset H t).ncard := by
      rw [hDK]
      refine le_antisymm hcard_le ?_
      have := Nat.card_le_card_of_injective
        (f := fun x : ↥(Work.ThmF.Kset H t) =>
          (⟨(x : G), hKsub x.2⟩ : ↥(Work.ThmF.Ksub H t)))
        (by intro a b hab
            exact Subtype.ext (congrArg (fun z : ↥(Work.ThmF.Ksub H t) => (z : G)) hab))
      simpa using this

    -- `|Ksub| = |D| = |V|·|Kset|` with `|V| ≥ 3`
    have hVcard : 3 ≤ Nat.card ↥(centD H t) := by
      have hne1 : Nat.card ↥(centD H t) ≠ 1 := fun hc =>
        hV (Subgroup.card_eq_one.mp hc)
      have hodd : Odd (Nat.card ↥(centD H t)) :=
        (Work.ThmF.split_odd_card_twoPoint hyp.split).of_dvd_nat
          (Subgroup.card_dvd_of_le
            (inf_le_left : centD H t ≤ Submission.Blueprint.twoPoint H t))
      obtain ⟨k, hk⟩ := hodd
      omega
    have hmul := Work.ThmF.card_centD_mul_card_Kset (H := H) (t := t)
      (Work.ThmF.IsSplitRankOne.toData hyp.split)
    rw [hcard_eq] at hmul
    have hKset_pos : 0 < (Work.ThmF.Kset H t).ncard := by
      obtain ⟨x, hx, -⟩ := Work.ThmF.L5.exists_mem_Kset_ne_one hyp.sit hyp.split
      exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨x, hx⟩
    have h2 : 2 * (Work.ThmF.Kset H t).ncard ≤ (Work.ThmF.Kset H t).ncard := by
      calc 2 * (Work.ThmF.Kset H t).ncard
          ≤ Nat.card ↥(centD H t) * (Work.ThmF.Kset H t).ncard :=
            Nat.mul_le_mul_right _ (by omega)
        _ = (Work.ThmF.Kset H t).ncard := hmul
    omega
  · exact Or.inl hX

/-- The classical input in `J`-form: the set of elements of an odd-order group inverted by an
involutory automorphism is closed under multiplication, as soon as it is a regular (sharply
transitive) transversal on the non-zero elements of an elementary abelian 2-group.  This is the
statement recorded at `Work.ThmF.ChV12.sharpTransitiveInvertingClosed_Jform` (reviewed twice:
"looks correct as stated"); it is strictly weaker than `SharpInvertingClosed` above. -/
def JFormClosed : Prop :=
  ∀ (G : Type) [Group G], ∀ (A D : Subgroup G) (τ : G),
    (∀ x ∈ A, x * x = 1) →
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
    D ≤ Subgroup.normalizer (A : Set G) →
    Odd (Nat.card ↥D) →
    τ * τ = 1 →
    τ ∈ Subgroup.normalizer (D : Set G) →
    (∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
      ∃! j : G, (j ∈ D ∧ τ * j * τ⁻¹ = j⁻¹) ∧ j * a * j⁻¹ = b) →
    D ⊓ Subgroup.centralizer (A : Set G) = ⊥ →
    ∀ j₁ ∈ D, τ * j₁ * τ⁻¹ = j₁⁻¹ → ∀ j₂ ∈ D, τ * j₂ * τ⁻¹ = j₂⁻¹ →
      τ * (j₁ * j₂) * τ⁻¹ = (j₁ * j₂)⁻¹

/-- **The crux from the `J`-form of the classical statement.**  In the remaining case
(`Q = Q0sub H`, `X5 H t = ⊤`) the inverted set `J = Kset H t` is a subgroup; since it generates
`twoPoint H t` there, it equals `twoPoint H t`; every element of `twoPoint H t` is then inverted by
`t`, so `centD H t = C_{twoPoint H t}(t) = ⊥`, contradicting `V ≠ 1`. -/
theorem L5cruxProp_of_JFormClosed (h : JFormClosed) : L5cruxProp := by
  intro G _ _ H Q t s hC4 hyp hQ
  by_cases hX : Work.ThmF.Lemma5.X5 H t = ⊤
  · refine Or.inr ?_
    by_contra hV
    have hDK : twoPoint H t = Work.ThmF.Ksub H t :=
      X5_eq_top_imp_twoPoint_eq_Ksub hC4 hyp hX
    have hCent : twoPoint H t ⊓
        Subgroup.centralizer (Work.ThmF.Q0sub H : Set G) = ⊥ :=
      X5_eq_top_imp_centD_ne_bot_imp_centralizer_eq_bot hC4 hyp hX hV
    have hcomm := Work.ThmF.L5.involutions_commute hyp.sit hC4 hyp.split
    have hA2 : ∀ x ∈ Work.ThmF.Q0sub H, x * x = 1 := by
      intro x hx
      have hxQ0 : x ∈ Work.ThmF.Q0 H := (Work.ThmF.L5.mem_Q0sub_iff hC4 hyp x).mp hx
      rcases Work.ThmF.mem_Q0_iff.mp hxQ0 with ⟨-, hord⟩ | rfl
      · have h2 : x ^ 2 = 1 := by
          have := pow_orderOf_eq_one x
          rwa [hord] at this
        simpa [pow_two] using h2
      · simp
    have hAc : ∀ x ∈ Work.ThmF.Q0sub H, ∀ y ∈ Work.ThmF.Q0sub H, x * y = y * x := by
      intro x hx y hy
      have hxI : x ∈ Work.ThmF.Q0 H := (Work.ThmF.L5.mem_Q0sub_iff hC4 hyp x).mp hx
      have hyI : y ∈ Work.ThmF.Q0 H := (Work.ThmF.L5.mem_Q0sub_iff hC4 hyp y).mp hy
      rcases Work.ThmF.mem_Q0_iff.mp hxI with hx' | rfl
      · rcases Work.ThmF.mem_Q0_iff.mp hyI with hy' | rfl
        · exact hcomm x hx' y hy'
        · simp
      · simp
    have hDN : twoPoint H t ≤ Subgroup.normalizer (Work.ThmF.Q0sub H : Set G) := by
      rw [hDK]; exact Work.ThmF.L5.Ksub_le_normalizer_Q0sub hC4 hyp
    have hodd : Odd (Nat.card ↥(twoPoint H t)) := by
      rw [hDK]; exact L5oddKsub hyp
    have ht2 : t * t = 1 := Work.ThmF.L5.ht_mul_self hyp
    have htN : t ∈ Subgroup.normalizer ((twoPoint H t) : Set G) :=
      Work.ThmF.normalizes_twoPoint_of_data (Work.ThmF.IsSplitRankOne.toData hyp.split)
    have htrans : ∀ a ∈ Work.ThmF.Q0sub H, a ≠ 1 → ∀ b ∈ Work.ThmF.Q0sub H, b ≠ 1 →
        ∃! j : G, (j ∈ twoPoint H t ∧ t * j * t⁻¹ = j⁻¹) ∧ j * a * j⁻¹ = b := by
      intro a ha ha1 b hb hb1
      have haI : a ∈ involutions (H : Set G) := by
        have h0 := (Work.ThmF.L5.mem_Q0sub_iff hC4 hyp a).mp ha
        rcases Work.ThmF.mem_Q0_iff.mp h0 with h' | h'
        · exact h'
        · exact absurd h' ha1
      have hbI : b ∈ involutions (H : Set G) := by
        have h0 := (Work.ThmF.L5.mem_Q0sub_iff hC4 hyp b).mp hb
        rcases Work.ThmF.mem_Q0_iff.mp h0 with h' | h'
        · exact h'
        · exact absurd h' hb1
      obtain ⟨k, hk, huniq⟩ := Work.ThmF.L5.Kset_regular hyp.split a haI b hbI
      refine ⟨k, ⟨?_, hk.2⟩, ?_⟩
      · exact hk.1
      · intro y hy
        exact huniq y ⟨hy.1, hy.2⟩
    have hcl := h G (Work.ThmF.Q0sub H) (twoPoint H t) t
      hA2 hAc hDN hodd ht2 htN htrans hCent
    -- the inverted set is a subgroup of `twoPoint H t`, and it generates it
    let Jset : Set G := {j : G | j ∈ twoPoint H t ∧ t * j * t⁻¹ = j⁻¹}
    have h1J : (1 : G) ∈ Jset := ⟨(twoPoint H t).one_mem, by simp⟩
    have hmulJ : ∀ x ∈ Jset, ∀ y ∈ Jset, x * y ∈ Jset := by
      intro x hx y hy
      exact ⟨(twoPoint H t).mul_mem hx.1 hy.1, hcl x hx.1 hx.2 y hy.1 hy.2⟩
    have hinvJ : ∀ x ∈ Jset, x⁻¹ ∈ Jset := by
      intro x hx
      refine ⟨(twoPoint H t).inv_mem hx.1, ?_⟩
      have h' : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
      rw [h', hx.2, inv_inv]
    have hKsubJ : ∀ x ∈ Work.ThmF.Ksub H t, x ∈ Jset := by
      intro x hx
      refine Subgroup.closure_induction (k := Work.ThmF.Kset H t) (p := fun y _ => y ∈ Jset)
        ?_ ?_ ?_ ?_ hx
      · intro y hy
        exact hy
      · exact h1J
      · intro y z hy hz ihy ihz
        exact hmulJ y ihy z ihz
      · intro y hy ihy
        exact hinvJ y ihy
    have hJeq : Jset = (twoPoint H t : Set G) := by
      refine Set.Subset.antisymm (fun x hx => hx.1) ?_
      intro x hx
      exact hKsubJ x (by rw [← hDK]; exact hx)
    have hbot : centD H t = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro d hd
      obtain ⟨hdD, hdC⟩ := Subgroup.mem_inf.mp hd
      have hinv : t * d * t⁻¹ = d⁻¹ := by
        have hdJ : d ∈ Jset := by rw [hJeq]; exact hdD
        exact hdJ.2
      have hfix : t * d * t⁻¹ = d := by
        have h' := (Subgroup.mem_centralizer_iff.mp hdC) t (Set.mem_singleton t)
        have htd : t * d = d * t := by first | exact h' | exact h'.symm
        rw [htd, mul_assoc, mul_inv_cancel, mul_one]
      have h3 : d = d⁻¹ := by
        calc d = t * d * t⁻¹ := hfix.symm
          _ = d⁻¹ := hinv
      have hdd : d * d = 1 := by
        have h5 : d * d = d * d⁻¹ := congrArg (fun z => d * z) h3
        rw [h5, mul_inv_cancel]
      have hdd' : (⟨d, hdD⟩ : ↥(twoPoint H t)) * ⟨d, hdD⟩ = 1 := by
        ext
        simpa using hdd
      have h2' : orderOf (⟨d, hdD⟩ : ↥(twoPoint H t)) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hdd')
      have hN' : orderOf (⟨d, hdD⟩ : ↥(twoPoint H t)) ∣
          Nat.card ↥(twoPoint H t) := orderOf_dvd_natCard _
      have hoddord : Odd (orderOf (⟨d, hdD⟩ : ↥(twoPoint H t))) := hodd.of_dvd_nat hN'
      rcases (Nat.dvd_prime Nat.prime_two).mp h2' with h1 | h1
      · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
      · obtain ⟨k, hk⟩ := hoddord
        omega
    exact hV hbot
  · exact Or.inl hX

end Work.ThmF.ChV12
