
/-
# PORT NOTE (S5K): verbatim copy of `NC4/prop2d_step.lean` into the `sec4_P2d` world.

`Work.NormalComplement.normalizedBy_twoPoint` is defined both in
`Submission/Work/NormalComplement/sec2_one.lean` and in
`Submission/Work/NormalComplement/sec4_P2d.lean`, so Lean refuses to have both modules in one
environment.  The §4 chain `NC4.prop2cd` sits in the `sec2_one` world, while §4 Prop. 2 (b)
(`NC4.prop2b`) sits in the `sec4_P2d` world, and the assembly of `Setup5` needs both.  This file is
the copy of `NC4/prop2d_step.lean` relocated to the `sec4_P2d` world; only the imports are changed (they point at
the other copies in `S5K/`), the mathematics is untouched.
-/
import Mathlib
import Submission.Work.NormalComplement.NC4.Defs
import Submission.Work.NormalComplement.NC4.nilpotent_split
import Submission.Work.NormalComplement.NC4.kset_decomp
import Submission.Work.NormalComplement.NC4.centralizer_of_fixed
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.normal_pSubgroup_of_dvd_fitting
import Submission.Work.Fitting.fitting_isNilpotent
import Submission.Work.NormalComplement.S5K.sec2_lemma1_w2
import Submission.Work.NormalComplement.S5K.card_centD_w2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement.NC4

/-! ## Auxiliary lemmas -/

/-- `Kset` is monotone in the subgroup. -/
lemma kset_mono_l {G : Type} [Group G] {D₁ D₂ : Subgroup G} (h : D₁ ≤ D₂) (t : G) :
    Work.NormalComplement.Kset D₁ t ⊆ Work.NormalComplement.Kset D₂ t :=
  fun _ hx => ⟨h hx.1, hx.2⟩

/-- If `Kset D t ⊆ X` and `X ≤ D`, then `Kset X t = Kset D t`. -/
lemma kset_eq_of_subset_l {G : Type} [Group G] {D X : Subgroup G} {t : G} (hXD : X ≤ D)
    (h : Work.NormalComplement.Kset D t ⊆ (X : Set G)) :
    Work.NormalComplement.Kset X t = Work.NormalComplement.Kset D t :=
  Set.Subset.antisymm (fun _ hx => ⟨hXD hx.1, hx.2⟩) fun _ hx => ⟨h hx, hx.2⟩

/-- A normal `q`-subgroup `R` of `V` of index prime to `q` contains every `q`-subgroup of `V`. -/
theorem q_le_normal_sylow {G : Type} [Group G] [Finite G]
    {V R X : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hRleV : R ≤ V) (hRV : V ≤ Subgroup.normalizer (R : Set G))
    (hRq : IsPGroup q ↥R) (hRidx : ¬ q ∣ R.relIndex V)
    (hXleV : X ≤ V) (hXq : IsPGroup q ↥X) : X ≤ R := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hXRq : IsPGroup q ↥(X ⊔ R) :=
    IsPGroup.to_sup_of_normal_right' hXq hRq (hXleV.trans hRV)
  have hle : R ≤ X ⊔ R := le_sup_right
  have hsupV : X ⊔ R ≤ V := sup_le hXleV hRleV
  have hprod : R.relIndex (X ⊔ R) * (X ⊔ R).relIndex V = R.relIndex V :=
    Subgroup.relIndex_mul_relIndex R (X ⊔ R) V hle hsupV
  obtain ⟨k, hk⟩ := hXRq.exists_card_eq
  have hdvd : R.relIndex (X ⊔ R) ∣ q ^ k := by
    rw [← hk]
    exact Subgroup.index_dvd_card (R.subgroupOf (X ⊔ R))
  have hcop : Nat.Coprime (R.relIndex (X ⊔ R)) (R.relIndex V) :=
    Nat.Coprime.of_dvd_left hdvd (hq.coprime_pow_of_not_dvd (m := k) hRidx).symm
  have hone : R.relIndex (X ⊔ R) = 1 := hcop.eq_one_of_dvd ⟨_, hprod.symm⟩
  have htop : X ⊔ R ≤ R :=
    Subgroup.subgroupOf_eq_top.mp
      (Subgroup.index_eq_one.mp (show (R.subgroupOf (X ⊔ R)).index = 1 from hone))
  exact le_sup_left.trans htop

/-- If `A ≤ V` has prime index `p` in `V` and `X ≤ V` normalizes `A` (so that
`|A ⊔ X| * |A ⊓ X| = |A| * |X|`), then `X ≤ A` provided `p ∤ |X|`. -/
theorem le_of_index_prime_not_dvd {G : Type} [Group G] [Finite G]
    {A V X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hAV : A ≤ V) (hXleV : X ≤ V) (hXNA : X ≤ Subgroup.normalizer (A : Set G))
    (hidx : A.relIndex V = p) (hpdvd : ¬ p ∣ Nat.card ↥X) : X ≤ A := by
  by_contra hXA
  have hsupV : A ⊔ X ≤ V := sup_le hAV hXleV
  have hprod : A.relIndex (A ⊔ X) * (A ⊔ X).relIndex V = p := by
    rw [Subgroup.relIndex_mul_relIndex A (A ⊔ X) V le_sup_left hsupV, hidx]
  have hdvd : A.relIndex (A ⊔ X) ∣ p := ⟨_, hprod.symm⟩
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
  · have htop : A ⊔ X ≤ A :=
      Subgroup.subgroupOf_eq_top.mp
        (Subgroup.index_eq_one.mp (show (A.subgroupOf (A ⊔ X)).index = 1 from h1))
    exact hXA (le_sup_right.trans htop)
  · have hVeq : A ⊔ X = V := by
      have h1 : (A ⊔ X).relIndex V = 1 := by
        have h2 := hprod
        rw [hp'] at h2
        exact Nat.mul_left_cancel hp.pos (by rw [h2, mul_one])
      exact le_antisymm hsupV
        (Subgroup.subgroupOf_eq_top.mp
          (Subgroup.index_eq_one.mp (show ((A ⊔ X).subgroupOf V).index = 1 from h1)))
    have hcard := Work.NormalComplement.card_sup_mul_card_inf (H := A) (K := X) hXNA
    rw [hVeq] at hcard
    have hVcard : Nat.card ↥V = p * Nat.card ↥A := by
      have h := Work.NormalComplement.relIndex_mul_card_of_le' hAV
      rw [hidx] at h
      exact h.symm
    rw [hVcard, mul_assoc] at hcard
    have hkey : Nat.card ↥A * (p * Nat.card ↥(A ⊓ X)) = Nat.card ↥A * Nat.card ↥X := by
      rw [← hcard]; ring
    exact hpdvd ⟨Nat.card ↥(A ⊓ X), (Nat.mul_left_cancel Nat.card_pos hkey).symm⟩

/-- The `q`-split of a finite nilpotent subgroup `E`, with the extra information that the
normalizer of `E` (in the ambient group) normalizes both factors. -/
theorem nilpotent_qsplit_norm {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hnil : Group.IsNilpotent ↥E) {q : ℕ} (hq : q.Prime) :
    ∃ S T : Subgroup G, S ≤ E ∧ T ≤ E ∧ S ⊔ T = E ∧ S ⊓ T = ⊥ ∧
      (∀ s ∈ S, ∀ u ∈ T, s * u = u * s) ∧
      Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (S : Set G) ∧
      Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (T : Set G) ∧
      IsPGroup q ↥S ∧ ¬ q ∣ Nat.card ↥T := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨S₀, T₀, hS₀char, hT₀char, hS₀norm, hT₀norm, hS₀P, hqT₀, hS₀T₀sup, hS₀T₀inf⟩ :=
    exists_nilpotent_q_split hnil hq
  have key : ∀ {W₀ : Subgroup ↥E}, W₀.Characteristic → Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (W₀.map E.subtype : Set G) := by
    intro W₀ hW₀ x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hψ : Subgroup.map (↑(Subgroup.normalizerMonoidHom E ⟨x, hx⟩)) W₀ = W₀ :=
      Subgroup.characteristic_iff_map_eq.mp hW₀ (Subgroup.normalizerMonoidHom E ⟨x, hx⟩)
    have hcomp : (↑(MulAut.conj x) : G →* G).comp E.subtype =
        E.subtype.comp (↑(Subgroup.normalizerMonoidHom E ⟨x, hx⟩) : ↥E →* ↥E) := by
      ext y
      show (MulAut.conj x) (E.subtype y) = E.subtype ((Subgroup.normalizerMonoidHom E ⟨x, hx⟩) y)
      rw [MulAut.conj_apply]
      rw [Subgroup.normalizerMonoidHom]
      simp only [MulDistribMulAction.toMulAut_apply]
      rfl
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hψ]
  haveI := hS₀norm
  haveI := hT₀norm
  refine ⟨S₀.map E.subtype, T₀.map E.subtype, Subgroup.map_subtype_le _,
    Subgroup.map_subtype_le _, ?_, ?_, ?_, key hS₀char, key hT₀char,
    hS₀P.map E.subtype, ?_⟩
  · rw [← Subgroup.map_sup, hS₀T₀sup, Subgroup.map_top, Subgroup.range_subtype]
  · obtain ⟨k, hk⟩ := hS₀P.exists_card_eq
    have hcop' : Nat.Coprime (Nat.card ↥S₀) (Nat.card ↥T₀) := by
      rw [hk]
      exact (hq.coprime_pow_of_not_dvd (m := k) hqT₀).symm
    exact (Subgroup.disjoint_of_coprime_natCard (by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective E),
        Subgroup.card_map_of_injective (Subgroup.subtype_injective E)]
      exact hcop')).eq_bot
  · intro s hs u hu
    rw [Subgroup.mem_map] at hs hu
    obtain ⟨s', hs', rfl⟩ := hs
    obtain ⟨u', hu', rfl⟩ := hu
    exact ((Subgroup.commute_of_normal_of_disjoint S₀ T₀ hS₀norm hT₀norm
      (disjoint_iff.mpr hS₀T₀inf) s' u' hs' hu').map E.subtype).eq
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective E)]
    exact hqT₀

/-! ## The main theorem -/

theorem prop2d_step (hFT : Submission.Blueprint.FeitThompsonProp)
    {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (h1d : Work.NormalComplement.NC4.Lemma1dConc H t W p P A)
    (hP1 : Work.NormalComplement.NC4.Prop1Conc H t W p P A)
    (h2a : Work.NormalComplement.NC4.Prop2aConc H t W p P A)
    (h2b : Work.NormalComplement.NC4.Prop2bConc H t W p P A)
    (q : ℕ) (hq : q.Prime)
    (hqK : q ∣ (Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t).ncard)
    (hRp : IsPGroup q ↥(Work.NormalComplement.Design.Ecomm H t W
      ⊓ Submission.Blueprint.centD H t)) :
    Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t)
        = Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t ∧
      Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t) ≠ ⊥ ∧
      Work.NormalComplement.IsSylowIn q
        (Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t))
        (Submission.Blueprint.centD H t) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨h.prime⟩
  -- ## standing facts
  have ht : orderOf t = 2 := h.invol
  have hD_odd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := h.se.2.2 t h.notMem
  have hV_le_D : Submission.Blueprint.centD H t ≤ Submission.Blueprint.twoPoint H t := inf_le_left
  have hP_le_V : P ≤ Submission.Blueprint.centD H t := h.P_le.trans inf_le_right
  have hsec2 := sec2_lemma1_w2 hFT h.toSetup3
  have hKsub : Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t ⊆
      (Work.NormalComplement.Design.Ecomm H t W : Set G) := hsec2.1
  have hE_tinv : ∀ e ∈ Work.NormalComplement.Design.Egrp H t W,
      t * e * t⁻¹ ∈ Work.NormalComplement.Design.Egrp H t W := hsec2.2.1
  have hE'_le_D : Work.NormalComplement.Design.Ecomm H t W ≤
      Submission.Blueprint.twoPoint H t :=
    Subgroup.commutator_le_of_le inf_le_right inf_le_right
  have htV : ∀ v ∈ Submission.Blueprint.centD H t, t * v * t⁻¹ = v := by
    intro v hv
    have h1 : v * t = t * v :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hv).2
    rw [h1.symm]; group
  have hE'_tinv : Work.NormalComplement.NormalizedBy t
      (Work.NormalComplement.Design.Ecomm H t W) := by
    intro x hx
    have hmapE : (Work.NormalComplement.Design.Egrp H t W).map
        (MulAut.conj t).toMonoidHom = Work.NormalComplement.Design.Egrp H t W := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rw [Subgroup.map_le_iff_le_comap]
        intro y hy
        simpa [MulAut.conj_apply] using hE_tinv y hy
      · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
    have hmap : (Work.NormalComplement.Design.Ecomm H t W).map
        (MulAut.conj t).toMonoidHom = Work.NormalComplement.Design.Ecomm H t W := by
      have hE' : Work.NormalComplement.Design.Ecomm H t W =
          ⁅Work.NormalComplement.Design.Egrp H t W,
            Work.NormalComplement.Design.Egrp H t W⁆ := rfl
      rw [hE', Subgroup.map_commutator, hmapE]
    have hx' : (MulAut.conj t) x ∈ (Work.NormalComplement.Design.Ecomm H t W).map
        (MulAut.conj t).toMonoidHom := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hmap] at hx'
    simpa [MulAut.conj_apply] using hx'
  -- ## `E'` is normalised by `D`, hence by `V`
  have hD_le_NE' : Submission.Blueprint.twoPoint H t ≤
      Subgroup.normalizer (Work.NormalComplement.Design.Ecomm H t W : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hdH : d ∈ H := hd.1
    have hmapW : Subgroup.map (MulAut.conj d).toMonoidHom W = W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.normal hdH)
    have hmapD : Subgroup.map (MulAut.conj d).toMonoidHom (Submission.Blueprint.twoPoint H t) =
        Submission.Blueprint.twoPoint H t :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hd)
    have hmapE : Subgroup.map (MulAut.conj d).toMonoidHom
        (Work.NormalComplement.Design.Egrp H t W) =
        Work.NormalComplement.Design.Egrp H t W := by
      show Subgroup.map (MulAut.conj d).toMonoidHom
          (W ⊓ Submission.Blueprint.twoPoint H t) =
          W ⊓ Submission.Blueprint.twoPoint H t
      rw [Subgroup.map_inf _ _ _ (MulAut.conj d).injective, hmapW, hmapD]
    have hmapE' : Subgroup.map (MulAut.conj d).toMonoidHom
        ⁅Work.NormalComplement.Design.Egrp H t W,
          Work.NormalComplement.Design.Egrp H t W⁆ =
        ⁅Work.NormalComplement.Design.Egrp H t W,
          Work.NormalComplement.Design.Egrp H t W⁆ := by
      rw [Subgroup.map_commutator, hmapE]
    exact hmapE'
  have hVle_NE' : Submission.Blueprint.centD H t ≤
      Subgroup.normalizer (Work.NormalComplement.Design.Ecomm H t W : Set G) :=
    hV_le_D.trans hD_le_NE'
  -- ## `R = E' ⊓ V = [A,P]`
  have hRle_E' : Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t ≤
      Work.NormalComplement.Design.Ecomm H t W := inf_le_left
  have hRle_V : Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t ≤
      Submission.Blueprint.centD H t := inf_le_right
  have hReqM : Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t =
      Work.NormalComplement.Design.commSub A P := h2a.2.2
  have hRle_A : Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t ≤ A := by
    rw [hReqM]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hP_le_V.trans h.A_normal)
  have hRne : Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t ≠ ⊥ :=
    h.d2.2.2
  have hR_normV : Submission.Blueprint.centD H t ≤ Subgroup.normalizer
      (↑(Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t) : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj v).injective]
    have h1 : Subgroup.map (↑(MulAut.conj v)) (Work.NormalComplement.Design.Ecomm H t W) =
        Work.NormalComplement.Design.Ecomm H t W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hVle_NE' hv)
    have h2 : Subgroup.map (↑(MulAut.conj v)) (Submission.Blueprint.centD H t) =
        Submission.Blueprint.centD H t :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hv)
    rw [h1, h2]
  -- ## `q ≠ p`
  have hPleD : P ≤ Submission.Blueprint.twoPoint H t := h1d.1.2.1
  have hPleE : P ≤ Work.NormalComplement.Design.Egrp H t W := by
    rw [← h1d.2.2]; exact le_sup_right
  have hE_le_NE' : Work.NormalComplement.Design.Egrp H t W ≤
      Subgroup.normalizer (Work.NormalComplement.Design.Ecomm H t W : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : Subgroup.map (MulAut.conj e).toMonoidHom
        (Work.NormalComplement.Design.Egrp H t W) =
        Work.NormalComplement.Design.Egrp H t W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer he)
    have h2 : Subgroup.map (MulAut.conj e).toMonoidHom
        ⁅Work.NormalComplement.Design.Egrp H t W,
          Work.NormalComplement.Design.Egrp H t W⁆ =
        ⁅Work.NormalComplement.Design.Egrp H t W,
          Work.NormalComplement.Design.Egrp H t W⁆ := by
      rw [Subgroup.map_commutator, h1]
    exact h2
  have hEcard : Nat.card ↥(Work.NormalComplement.Design.Egrp H t W) =
      Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W) * p := by
    have h1 := Work.NormalComplement.card_sup_mul_card_inf
      (H := Work.NormalComplement.Design.Ecomm H t W) (K := P)
      (hPleE.trans hE_le_NE')
    rw [h1d.2.2, h1d.2.1, Subgroup.card_bot, mul_one, h.P_card] at h1
    exact h1
  have hE'card : Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W) =
      P.relIndex (Work.NormalComplement.Design.Egrp H t W) := by
    have h1 := Work.NormalComplement.relIndex_mul_card_of_le' hPleE
    rw [h.P_card, hEcard] at h1
    exact (Nat.mul_right_cancel h.prime.pos h1).symm
  have hp_not_dvd_E' : ¬ p ∣ Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W) := by
    rw [hE'card]
    intro hdvd
    have hprod : P.relIndex (Work.NormalComplement.Design.Egrp H t W) *
        (Work.NormalComplement.Design.Egrp H t W).relIndex
          (Submission.Blueprint.twoPoint H t) =
        P.relIndex (Submission.Blueprint.twoPoint H t) :=
      Subgroup.relIndex_mul_relIndex P (Work.NormalComplement.Design.Egrp H t W)
        (Submission.Blueprint.twoPoint H t) hPleE inf_le_right
    exact h1d.1.2.2 (show p ∣ P.relIndex (Submission.Blueprint.twoPoint H t) from
      hprod ▸ hdvd.mul_right _)
  have hq_dvd_E' : q ∣ Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W) :=
    (h2b.2.2 q hq).mpr hqK
  have hq_ne_p : q ≠ p := fun hqp => hp_not_dvd_E' (hqp ▸ hq_dvd_E')
  -- ## prime divisors of `C = C_A(P)`
  have hq_not_C : ¬ q ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) := fun hdvd =>
    (hP1.1 q hq hdvd).2.2.2 hqK
  have hp_not_C : ¬ p ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) := fun hdvd =>
    (hP1.1 p h.prime hdvd).2.2.1 rfl
  have hp_not_dvd_R : ¬ p ∣ Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W ⊓
      Submission.Blueprint.centD H t) := by
    obtain ⟨m, hm⟩ := hRp.exists_card_eq
    rw [hm]
    intro hdvd
    exact hq_ne_p ((hq.eq_one_or_self_of_dvd p (h.prime.dvd_of_dvd_pow hdvd)).resolve_left
      h.prime.ne_one).symm
  -- ## `q`-Sylow of `V`
  have hVcard : Nat.card ↥(Submission.Blueprint.centD H t) =
      Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t) * p *
        Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) :=
    card_centD h h1d hP1 h2a
  have hArelV : A.relIndex (Submission.Blueprint.centD H t) = p := by
    have h1 := Work.NormalComplement.card_sup_mul_card_inf (H := A) (K := P)
      (hP_le_V.trans h.A_normal)
    rw [h.A_sup, h.A_inf, Subgroup.card_bot, mul_one, h.P_card] at h1
    have h2 := Work.NormalComplement.relIndex_mul_card_of_le' h.A_le
    rw [h1] at h2
    exact Nat.mul_right_cancel Nat.card_pos (by rw [h2, mul_comm])
  have hRrelV : (Work.NormalComplement.Design.Ecomm H t W ⊓
        Submission.Blueprint.centD H t).relIndex (Submission.Blueprint.centD H t) =
      p * Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) := by
    have h1 := Work.NormalComplement.relIndex_mul_card_of_le' hRle_V
    exact Nat.mul_right_cancel Nat.card_pos (by rw [h1, hVcard]; ring)
  have hSyl : Work.NormalComplement.IsSylowIn q
      (Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t)
      (Submission.Blueprint.centD H t) := by
    refine ⟨hRp, hRle_V, ?_⟩
    change ¬ q ∣ (Work.NormalComplement.Design.Ecomm H t W ⊓
      Submission.Blueprint.centD H t).relIndex (Submission.Blueprint.centD H t)
    rw [hRrelV]
    intro hdvd
    rcases hq.dvd_mul.mp hdvd with h' | h'
    · exact hq_ne_p ((h.prime.eq_one_or_self_of_dvd q h').resolve_left hq.ne_one)
    · exact hq_not_C h'
  -- ## `R ≤ F(V)`
  have hRnil : Group.IsNilpotent ↥(Work.NormalComplement.Design.Ecomm H t W ⊓
      Submission.Blueprint.centD H t) := IsPGroup.isNilpotent hRp
  haveI hRsubNormal : ((Work.NormalComplement.Design.Ecomm H t W ⊓
      Submission.Blueprint.centD H t).subgroupOf (Submission.Blueprint.centD H t)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRle_V).mpr hR_normV
  have hRnil_sub : Group.IsNilpotent
      ↥((Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t).subgroupOf
        (Submission.Blueprint.centD H t)) :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hRle_V).symm).mp hRnil
  have hRle_FV : Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t ≤
      Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t) := by
    rw [Work.NormalComplement.Design.fitSub]
    intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hRle_V hx⟩, ?_, rfl⟩
    exact Work.Fitting.le_fitting hRsubNormal hRnil_sub (Subgroup.mem_subgroupOf.mpr hx)
  -- ## `F(V)` facts
  have hFV_le_V : Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t) ≤
      Submission.Blueprint.centD H t := Subgroup.map_subtype_le _
  have hFV_tinv : Work.NormalComplement.NormalizedBy t
      (Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t)) := by
    intro x hx
    have hxV : x ∈ Submission.Blueprint.centD H t := hFV_le_V hx
    rw [htV x hxV]
    exact hx
  have hFV_nil : Group.IsNilpotent ↥
      (Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t)) := by
    haveI : Group.IsNilpotent ↥(Work.Fitting.fitting ↥(Submission.Blueprint.centD H t)) :=
      Work.Fitting.fitting_isNilpotent ↥(Submission.Blueprint.centD H t)
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective (Work.Fitting.fitting ↥(Submission.Blueprint.centD H t))
        (Submission.Blueprint.centD H t).subtype (Subgroup.subtype_injective _))
  -- ## `p ∤ |F(V)|`
  have hp_not_FV : ¬ p ∣ Nat.card ↥
      (Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t)) := by
    intro hdvd
    obtain ⟨X, hXV, hVNX, hXp, hXne⟩ :=
      normal_pSubgroup_of_dvd_fitting (V := Submission.Blueprint.centD H t) h.prime hdvd
    obtain ⟨k, hk⟩ := hXp.exists_card_eq
    have hpsq : ¬ p ^ 2 ∣ Nat.card ↥(Submission.Blueprint.centD H t) := by
      intro hd
      rw [hVcard] at hd
      have hd2 : p ^ 2 ∣ p * (Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W ⊓
          Submission.Blueprint.centD H t) *
            Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G))) := by
        rwa [show Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W ⊓
              Submission.Blueprint.centD H t) * p *
              Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) =
            p * (Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W ⊓
              Submission.Blueprint.centD H t) *
              Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G))) from by ring] at hd
      have hd3 : p ∣ Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W ⊓
          Submission.Blueprint.centD H t) *
            Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) := by
        rw [pow_two] at hd2
        exact Nat.dvd_of_mul_dvd_mul_left h.prime.pos hd2
      rcases h.prime.dvd_mul.mp hd3 with h' | h'
      · exact hp_not_dvd_R h'
      · exact hp_not_C h'
    have hk1 : k = 1 := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, pow_zero] at hk
        exact absurd (Subgroup.card_eq_one.mp hk) hXne
      · by_contra hkne
        have hk2 : 2 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hkpos (Ne.symm hkne))
        exact hpsq (Nat.pow_dvd_pow p hk2 |>.trans
          (by rw [← hk]; exact Subgroup.card_dvd_of_le hXV))
    have hXcard : Nat.card ↥X = p := by rw [hk, hk1, pow_one]
    have hXi : ¬ p ∣ X.relIndex (Submission.Blueprint.centD H t) := by
      intro hd
      obtain ⟨m, hm⟩ := hd
      refine hpsq ⟨m, ?_⟩
      have hVi : p * X.relIndex (Submission.Blueprint.centD H t) =
          Nat.card ↥(Submission.Blueprint.centD H t) := by
        rw [← hXcard, mul_comm]
        exact Work.NormalComplement.relIndex_mul_card_of_le' hXV
      rw [pow_two]
      rw [hm] at hVi
      rw [mul_assoc]
      exact hVi.symm
    have hPX : P = X := by
      have hPleX : P ≤ X :=
        q_le_normal_sylow h.prime hXV hVNX hXp hXi hP_le_V h1d.1.1
      exact Subgroup.eq_of_le_of_card_ge hPleX (by rw [hXcard, h.P_card])
    have hRP : Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t ≤ P := by
      rw [hReqM, hPX]
      exact (Subgroup.commutator_le).mpr (fun a ha b hb => by
        show a * b * a⁻¹ * b⁻¹ ∈ X
        exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVNX (h.A_le ha)) b).mp hb)
          (X.inv_mem hb))
    refine hRne (le_bot_iff.mp ?_)
    rw [← h.A_inf]
    exact le_inf hRle_A hRP
  -- ## the `q`-split of `F(V)`
  obtain ⟨S', T', hS'_le, hT'_le, hS'T'_sup, hS'T'_inf, hS'T'_comm, hNF_le_NS', _hNF_le_NT',
    hS'p, hqT'⟩ := nilpotent_qsplit_norm hFV_nil hq
  have hS'_le_V : S' ≤ Submission.Blueprint.centD H t := hS'_le.trans hFV_le_V
  have hT'_le_V : T' ≤ Submission.Blueprint.centD H t := hT'_le.trans hFV_le_V
  -- ## `S' = R`
  have hS'_le_R : S' ≤ Work.NormalComplement.Design.Ecomm H t W ⊓
      Submission.Blueprint.centD H t :=
    q_le_normal_sylow hq hRle_V hR_normV hRp hSyl.2.2 hS'_le_V hS'p
  have hF_le_NS' : Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t) ≤
      Subgroup.normalizer (S' : Set G) :=
    Subgroup.le_normalizer.trans hNF_le_NS'
  have hS'relF : S'.relIndex (Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t)) =
      Nat.card ↥T' := by
    have hcard : Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t)) =
        Nat.card ↥S' * Nat.card ↥T' := by
      have h := Work.NormalComplement.card_sup_mul_card_inf (H := S') (K := T')
        (hT'_le.trans (Subgroup.le_normalizer.trans hNF_le_NS'))
      rw [hS'T'_sup, hS'T'_inf, Subgroup.card_bot, mul_one] at h
      exact h
    have hidx := Work.NormalComplement.relIndex_mul_card_of_le' hS'_le
    rw [hcard] at hidx
    exact Nat.mul_right_cancel Nat.card_pos (by rw [hidx]; ring)
  have hR_le_S' : Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t ≤ S' :=
    q_le_normal_sylow hq hS'_le hF_le_NS' hS'p (by rw [hS'relF]; exact hqT') hRle_FV hRp
  have hS'R_eq : S' = Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t :=
    le_antisymm hS'_le_R hR_le_S'
  -- ## `T' ≤ A`
  have hT'_le_A : T' ≤ A :=
    le_of_index_prime_not_dvd h.prime h.A_le hT'_le_V (hT'_le_V.trans h.A_normal) hArelV
      (fun hd => hp_not_FV (hd.trans (Subgroup.card_dvd_of_le hT'_le)))
  -- ## the `q`-split of `E'`
  have htNE' : t ∈ Subgroup.normalizer (Work.NormalComplement.Design.Ecomm H t W : Set G) :=
    mem_normalizer_of_normalizedBy hE'_tinv
  obtain ⟨S, T, hS_le, hT_le, hST_sup, hST_inf, hST_comm, hNE'_le_NS, hNE'_le_NT, hSp, hqT⟩ :=
    nilpotent_qsplit_norm h2b.1 hq
  have htS : Work.NormalComplement.NormalizedBy t S := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hNE'_le_NS htNE') y).mp hy
  have htT : Work.NormalComplement.NormalizedBy t T := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hNE'_le_NT htNE') y).mp hy
  have hKset_E' : Work.NormalComplement.Kset (Work.NormalComplement.Design.Ecomm H t W) t =
      Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t :=
    kset_eq_of_subset_l hE'_le_D hKsub
  have hK_sup := kset_sup_eq hS_le hT_le hST_sup hST_inf hST_comm htS htT
  have hR_le_S : Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t ≤ S := by
    refine q_le_normal_sylow hq hS_le (Subgroup.le_normalizer.trans hNE'_le_NS) hSp ?_
      hRle_E' hRp
    have hcard : Nat.card ↥(Work.NormalComplement.Design.Ecomm H t W) =
        Nat.card ↥S * Nat.card ↥T := by
      have h := Work.NormalComplement.card_sup_mul_card_inf (H := S) (K := T)
        (hT_le.trans (Subgroup.le_normalizer.trans hNE'_le_NS))
      rw [hST_sup, hST_inf, Subgroup.card_bot, mul_one] at h
      exact h
    have hidx := Work.NormalComplement.relIndex_mul_card_of_le' hS_le
    rw [hcard] at hidx
    have hSrelE : S.relIndex (Work.NormalComplement.Design.Ecomm H t W) = Nat.card ↥T :=
      Nat.mul_right_cancel Nat.card_pos (by rw [hidx, mul_comm (Nat.card ↥S) (Nat.card ↥T)])
    rw [hSrelE]
    exact hqT
  -- ## `T'` centralises `C_S(R)` (Thompson fixed points)
  have hY_odd : Odd (Nat.card ↥(S ⊓ Subgroup.centralizer
      (Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t : Set G))) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hD_odd
      (Subgroup.card_dvd_of_le (hS_le.trans hE'_le_D))) (Subgroup.card_dvd_of_le inf_le_left)
  have hY_tinv : Work.NormalComplement.NormalizedBy t
      (S ⊓ Subgroup.centralizer (Work.NormalComplement.Design.Ecomm H t W ⊓
        Submission.Blueprint.centD H t : Set G)) := by
    intro y hy
    obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨htS y hyS, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro r hr
    have hry : r * y = y * r := hyC r hr
    have hrt : t⁻¹ * r * t = r := by
      have h2 : t * r = r * t := by
        calc t * r = (t * r * t⁻¹) * t := by group
          _ = r * t := by rw [htV r (hRle_V hr)]
      calc t⁻¹ * r * t = t⁻¹ * (r * t) := by group
        _ = t⁻¹ * (t * r) := by rw [h2]
        _ = r := by group
    calc r * (t * y * t⁻¹) = t * ((t⁻¹ * r * t) * y) * t⁻¹ := by group
      _ = t * (r * y) * t⁻¹ := by rw [hrt]
      _ = t * (y * r) * t⁻¹ := by rw [hry]
      _ = (t * y * t⁻¹) * (t * r * t⁻¹) := by group
      _ = (t * y * t⁻¹) * r := by rw [htV r (hRle_V hr)]
  have hYcop : Nat.Coprime (Nat.card ↥(S ⊓ Subgroup.centralizer
      (Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t : Set G))) 2 :=
    Nat.coprime_two_right.mpr hY_odd
  have hfix : ∀ y ∈ S, (∀ r ∈ Work.NormalComplement.Design.Ecomm H t W ⊓
      Submission.Blueprint.centD H t, r * y * r⁻¹ = y) → ∀ x ∈ T', x * y * x⁻¹ = y := by
    intro y hyS hyfix x hx
    obtain ⟨hKapp_eq, huniq⟩ := (appI_one (d := 2) Nat.prime_two ht hY_tinv hYcop).2 rfl
    have hyY : y ∈ S ⊓ Subgroup.centralizer (Work.NormalComplement.Design.Ecomm H t W ⊓
        Submission.Blueprint.centD H t : Set G) :=
      Subgroup.mem_inf.mpr ⟨hyS, Subgroup.mem_centralizer_iff.mpr (fun r hr => by
        have h2 : r * y = y * r := by
          calc r * y = (r * y * r⁻¹) * r := by group
            _ = y * r := by rw [hyfix r hr]
        exact h2)⟩
    obtain ⟨⟨c, k⟩, ⟨hcC, hcY, hkKapp, hck⟩, -⟩ := huniq y hyY
    obtain ⟨hcS, hcCR⟩ := Subgroup.mem_inf.mp hcY
    have hkKset : k ∈ Work.NormalComplement.Kset (S ⊓ Subgroup.centralizer
        (Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t : Set G)) t := by
      rw [← hKapp_eq]; exact hkKapp
    obtain ⟨hkS, hkCR⟩ := Subgroup.mem_inf.mp hkKset.1
    have hcR : c ∈ Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t :=
      Subgroup.mem_inf.mpr ⟨hS_le hcS, Subgroup.mem_inf.mpr ⟨hE'_le_D (hS_le hcS), hcC⟩⟩
    have hkD : k ∈ Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t :=
      kset_mono_l (hS_le.trans hE'_le_D) t (kset_mono_l inf_le_left t hkKset)
    have hkCK_R : k ∈ Work.NormalComplement.Design.CK H t
        (Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t) :=
      ⟨hkD, hkCR⟩
    have hkCK_A : k ∈ Work.NormalComplement.Design.CK H t A := by
      rw [← h.A_B (Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t)
        hRne hRle_A (hP_le_V.trans hR_normV)]
      exact hkCK_R
    have hkCGA : k ∈ Subgroup.centralizer (A : Set G) := hkCK_A.2
    have hkc : x * c * x⁻¹ = c := by
      have hcx : c * x = x * c := hS'T'_comm c (by rw [hS'R_eq]; exact hcR) x hx
      rw [show x * c * x⁻¹ = c from by rw [← hcx]; group]
    have hxk : x * k * x⁻¹ = k := by
      have hkx : x * k = k * x := (Subgroup.mem_centralizer_iff.mp hkCGA) x (hT'_le_A hx)
      rw [show x * k * x⁻¹ = k from by rw [hkx]; group]
    rw [← hck, show x * (c * k) * x⁻¹ = (x * c * x⁻¹) * (x * k * x⁻¹) from by group, hkc, hxk]
  -- ## Thompson's `P × Q` lemma
  have hcopS : Nat.Coprime (Nat.card ↥T') (Nat.card ↥S) := by
    obtain ⟨k, hk⟩ := hSp.exists_card_eq
    rw [hk]
    exact hq.coprime_pow_of_not_dvd (m := k) hqT'
  have hRS_le_NS : Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t ≤
      Subgroup.normalizer (S : Set G) :=
    hRle_E'.trans (Subgroup.le_normalizer.trans hNE'_le_NS)
  have hT'_le_NS : T' ≤ Subgroup.normalizer (S : Set G) :=
    hT'_le_V.trans (hVle_NE'.trans hNE'_le_NS)
  have hRT'_comm : ∀ r ∈ Work.NormalComplement.Design.Ecomm H t W ⊓
      Submission.Blueprint.centD H t, ∀ x ∈ T', r * x = x * r := fun r hr x hx =>
    hS'T'_comm r (by rw [hS'R_eq]; exact hr) x hx
  have hT'_cent_S : ∀ x ∈ T', ∀ y ∈ S, x * y * x⁻¹ = y :=
    centralizer_of_fixed hq hRS_le_NS hT'_le_NS hRT'_comm hRp hqT' hSp hcopS hfix
  -- ## `T' ≤ C_V(K) = ⊥`
  have hT'_cent_K : ∀ x ∈ T', ∀ z ∈ Work.NormalComplement.Kset
      (Submission.Blueprint.twoPoint H t) t, x * z * x⁻¹ = z := by
    intro x hx z hz
    rw [← hKset_E'] at hz
    rw [hK_sup] at hz
    obtain ⟨s, hs, u, hu, rfl⟩ := hz
    have hs_cent : x * s * x⁻¹ = s := hT'_cent_S x hx s hs.1
    have huA : u ∈ Subgroup.centralizer (A : Set G) := by
      have huCK_R : u ∈ Work.NormalComplement.Design.CK H t
          (Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t) :=
        ⟨kset_mono_l (hT_le.trans hE'_le_D) t hu,
          Subgroup.mem_centralizer_iff.mpr (fun r hr =>
            hST_comm r (hR_le_S hr) u hu.1)⟩
      have huCK_A : u ∈ Work.NormalComplement.Design.CK H t A := by
        rw [← h.A_B (Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t)
          hRne hRle_A (hP_le_V.trans hR_normV)]
        exact huCK_R
      exact huCK_A.2
    have hu_cent : x * u * x⁻¹ = u := by
      have hux : x * u = u * x := (Subgroup.mem_centralizer_iff.mp huA) x (hT'_le_A hx)
      rw [show x * u * x⁻¹ = u from by rw [hux]; group]
    rw [show x * (s * u) * x⁻¹ = (x * s * x⁻¹) * (x * u * x⁻¹) from by group, hs_cent, hu_cent]
  have hT'_le_cent : T' ≤ Subgroup.centralizer
      (Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    calc z * x = (x * z * x⁻¹) * x := by rw [hT'_cent_K x hx z hz]
      _ = x * z := by group
  have hT'_le_bot : T' = ⊥ := by
    have hle : T' ≤ Submission.Blueprint.centD H t ⊓ Subgroup.centralizer
        (Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t : Set G) :=
      le_inf hT'_le_V hT'_le_cent
    rw [h.d2.2.1] at hle
    exact le_bot_iff.mp hle
  -- ## conclusion
  have hFV_eq : Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t) =
      Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t := by
    rw [← hS'T'_sup, hT'_le_bot, sup_bot_eq, hS'R_eq]
  exact ⟨hFV_eq, by rw [hFV_eq]; exact hRne, by rw [hFV_eq]; exact hSyl⟩

end Work.NormalComplement.NC4
