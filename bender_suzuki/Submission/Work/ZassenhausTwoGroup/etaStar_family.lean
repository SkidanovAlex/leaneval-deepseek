import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.etaStar_data
import Submission.Work.ZassenhausTwoGroup.inflateFun_mem_Irr_triv
import Submission.Work.ZassenhausTwoGroup.card_H_eq
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.etaStar_family` (Feit 1960, §3, displays (18) and (19))

In the split rank-one Zassenhaus set-up `IsSplitRankOne H Q t` with `H = Q ⋊ D`,
`D = twoPoint H t = H ∩ Hᵗ`, the quotient `H / Q ≅ D` is abelian of odd order `|D|` as soon as
`⁅H, H⁆ ≤ Q` (`hH'`).  Hence `H/Q` has exactly `|D|` irreducible characters — all of them linear
— and exactly `|D| - 1` of them are non-trivial; complex conjugation pairs them up without fixed
points.  A half-transversal of that pairing therefore has `(|D| - 1)/2` elements, and the induced
characters `Ind_H^G η` of the corresponding non-trivial characters `η` of `H/Q` are pairwise
distinct irreducible characters of `G` of degree `|Q| + 1` which take the value `1` on `Q ∖ 1`.

The mathematics is Feit's displays (18) and (19); the induced-character facts are
`Work.ZassenhausTwoGroup.etaStar_data` (Feit's (18) together with the orthogonality (19)), and
the counting is done by the elementary lemmas below.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open Classical
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

noncomputable section

/-! ## Combinatorics: a half-transversal for a fixed point free involution -/

/-- Given a finite set `T` and an involution `σ` on the ambient type which maps `T` into itself
without fixed points on `T`, there is `S ⊆ T` with `|S| * 2 = |T|` and `σ a ∉ S` for `a ∈ S`, i.e.
a transversal of the pairs `{a, σ a}` inside `T`. -/
theorem halfTransversal_exists {α : Type*} [DecidableEq α] (T : Finset α) (σ : α → α)
    (hσT : ∀ a ∈ T, σ a ∈ T) (hσ2 : ∀ a : α, σ (σ a) = a) (hfix : ∀ a ∈ T, σ a ≠ a) :
    ∃ S : Finset α, S ⊆ T ∧ S.card * 2 = T.card ∧ ∀ a ∈ S, σ a ∉ S := by
  classical
  let P : ℕ → Prop := fun n => ∀ T : Finset α, T.card = n → (∀ a ∈ T, σ a ∈ T) →
    (∀ a : α, σ (σ a) = a) → (∀ a ∈ T, σ a ≠ a) →
    ∃ S : Finset α, S ⊆ T ∧ S.card * 2 = T.card ∧ ∀ a ∈ S, σ a ∉ S
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hT hσT hσ2 hfix
      by_cases hne : T = ∅
      · subst hne
        exact ⟨∅, by simp⟩
      · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hσaT : σ a ∈ T := hσT a ha
        have hσane : σ a ≠ a := hfix a ha
        have haσa : a ≠ σ a := fun h => hσane h.symm
        have hcard2 : 2 ≤ T.card := by
          have hsub : ({a, σ a} : Finset α) ⊆ T := by
            intro x hx
            rcases Finset.mem_insert.mp hx with hx | hx
            · exact hx ▸ ha
            · rw [Finset.mem_singleton] at hx; exact hx ▸ hσaT
          have hc : ({a, σ a} : Finset α).card = 2 := by
            rw [Finset.card_insert_of_notMem, Finset.card_singleton]
            simp [haσa]
          calc 2 = ({a, σ a} : Finset α).card := hc.symm
            _ ≤ T.card := Finset.card_le_card hsub
        set T' : Finset α := (T.erase a).erase (σ a) with hT'def
        have haT' : a ∉ T' := by
          rw [hT'def, Finset.mem_erase, Finset.mem_erase]; tauto
        have hσaT' : σ a ∉ T' := by
          rw [hT'def]; exact Finset.notMem_erase (σ a) (T.erase a)
        have hT'sub : T' ⊆ T := by
          intro x hx
          rw [hT'def, Finset.mem_erase, Finset.mem_erase] at hx
          exact hx.2.2
        have hT'card : T'.card = T.card - 2 := by
          rw [hT'def, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hσane, hσaT⟩),
            Finset.card_erase_of_mem ha]
          omega
        have hσT' : ∀ b ∈ T', σ b ∈ T' := by
          intro b hb
          have hb' : b ≠ σ a ∧ b ≠ a ∧ b ∈ T := by
            rw [hT'def, Finset.mem_erase, Finset.mem_erase] at hb
            exact ⟨hb.1, hb.2.1, hb.2.2⟩
          obtain ⟨hbσa, hba, hbT⟩ := hb'
          have hσbT : σ b ∈ T := hσT b hbT
          rw [hT'def, Finset.mem_erase, Finset.mem_erase]
          exact ⟨fun h => hba (by rw [← hσ2 b, h, hσ2 a]),
            fun h => hbσa (by rw [← hσ2 b, h]), hσbT⟩
        have hT'lt : T'.card < n := by omega
        obtain ⟨S', hS'T', hS'card, hS'σ⟩ :=
          ih T'.card hT'lt T' rfl hσT' hσ2 (fun b hb => hfix b (hT'sub hb))
        refine ⟨insert a S', ?_, ?_, ?_⟩
        · intro b hb
          rcases Finset.mem_insert.mp hb with rfl | hb
          · exact ha
          · exact hT'sub (hS'T' hb)
        · have haS' : a ∉ S' := fun h => haT' (hS'T' h)
          rw [Finset.card_insert_of_notMem haS']
          omega
        · intro b hb
          rcases Finset.mem_insert.mp hb with rfl | hbS'
          · rw [Finset.mem_insert]
            intro h
            rcases h with h | h
            · exact hσane h
            · exact hσaT' (hS'T' h)
          · have hbT' : b ∈ T' := hS'T' hbS'
            have hbσa : b ≠ σ a := by
              rw [hT'def, Finset.mem_erase, Finset.mem_erase] at hbT'
              exact hbT'.1
            rw [Finset.mem_insert]
            intro h
            rcases h with h | h
            · exact hbσa (by rw [← hσ2 b, h])
            · exact hS'σ b hbS' h
  exact hP T.card T rfl hσT hσ2 hfix

/-! ## Characters of a finite abelian group -/

/-- A finite abelian group has exactly `|A|` irreducible complex characters (they are all
linear). -/
theorem card_Irr_eq_card_of_commutative {A : Type} [Group A] [Fintype A] [IsMulCommutative A] :
    (Work.CharCore.Irr A).card = Nat.card A := by
  classical
  rw [Work.CharCore.card_irr]
  have hbij : Function.Bijective (ConjClasses.mk : A → ConjClasses A) := by
    refine ⟨fun x y h => ?_, ConjClasses.mk_surjective⟩
    have hxy : IsConj x y := ConjClasses.mk_eq_mk_iff_isConj.mp h
    rw [isConj_iff] at hxy
    obtain ⟨g, hg⟩ := hxy
    rw [← hg, mul_comm' g x, mul_assoc, mul_inv_cancel, mul_one]
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

/-- The complex conjugate of an irreducible character of a finite abelian group is again an
irreducible character. -/
theorem star_mem_Irr_of_commutative {A : Type} [Group A] [Fintype A] [IsMulCommutative A]
    {β : A → ℂ} (hβ : β ∈ Work.CharCore.Irr A) :
    (fun a : A => star (β a)) ∈ Work.CharCore.Irr A := by
  classical
  have hdeg : Work.CharCore.irrDeg β = 1 := Work.CharCore.irrDeg_eq_one_of_commutative hβ
  obtain ⟨φ, hφ⟩ := (Work.CharCore.linear_char_iff_deg_one hβ).mp hdeg
  obtain ⟨χ, hχ, hχeq⟩ := Work.CharCore.exists_irr_of_monoidHom (φ⁻¹)
  rw [show (fun a : A => star (β a)) = χ from funext fun a => ?_]
  · exact hχ
  · have hstar : star (β a) = β a⁻¹ := Work.CharCore.star_Irr β hβ a
    rw [hstar, hφ a⁻¹, hχeq a, MonoidHom.map_inv φ a, MonoidHom.inv_apply φ a,
      Units.val_inv_eq_inv_val]

/-- For `|A|` odd, the complex conjugate of a non-trivial irreducible character of an abelian
group `A` is different from it. -/
theorem star_ne_self_of_odd {A : Type} [Group A] [Fintype A] [IsMulCommutative A]
    (hodd : Odd (Nat.card A)) {β : A → ℂ} (hβ : β ∈ Work.CharCore.Irr A)
    (hβ1 : β ≠ (fun _ : A => (1 : ℂ))) :
    (fun a : A => star (β a)) ≠ β := by
  classical
  intro hcon
  have hdeg : Work.CharCore.irrDeg β = 1 := Work.CharCore.irrDeg_eq_one_of_commutative hβ
  obtain ⟨φ, hφ⟩ := (Work.CharCore.linear_char_iff_deg_one hβ).mp hdeg
  refine hβ1 (funext fun a => ?_)
  have hstar : star (β a) = β a⁻¹ := Work.CharCore.star_Irr β hβ a
  have h' : β a = β a⁻¹ := ((congrFun hcon a).symm).trans hstar
  have hequnits : φ a = φ a⁻¹ := by
    apply Units.ext
    rw [← hφ a, ← hφ a⁻¹]
    exact h'
  have hunit : (φ a)⁻¹ = φ a := by
    rw [← MonoidHom.map_inv φ a]
    exact hequnits.symm
  have h2 : (φ a) ^ 2 = 1 := by
    rw [pow_two]
    exact inv_eq_iff_mul_eq_one.mp hunit
  have hAa : a ^ (Nat.card A) = 1 := by
    rw [Nat.card_eq_fintype_card]; exact pow_card_eq_one
  have hpow : (φ a) ^ (Nat.card A) = 1 := by
    rw [← map_pow, hAa, map_one]
  have hφa : φ a = 1 := eq_one_of_sq_eq_one_of_odd_pow_eq_one h2 hodd hpow
  rw [hφ a, hφa]
  rfl

/-! ## The order of `H / Q` -/

/-- `|H : Q| = |D|` for `H = Q ⋊ D` with `D = twoPoint H t`: `H/Q ≅ D` by the second
isomorphism theorem, in cardinality form. -/
theorem card_quotient_subgroupOf {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) [hN : (Q.subgroupOf H).Normal] :
    Nat.card (↥H ⧸ Q.subgroupOf H) = Nat.card (Submission.Blueprint.twoPoint H t) := by
  have hlag := Subgroup.card_mul_index (Q.subgroupOf H)
  rw [Subgroup.index_eq_card] at hlag
  have hsub : Nat.card ↥(Q.subgroupOf H) = Nat.card ↥Q :=
    Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), x.2⟩
        invFun := fun q => ⟨⟨(q : G), h.le q.2⟩, q.2⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun q => by ext; rfl }
  rw [hsub, card_H_eq h] at hlag
  exact Nat.mul_left_cancel (Nat.card_pos (α := ↥Q)) hlag

/-! ## The induced characters of a character of `H/Q` -/

/-- `Ind_H^G` of the inflation to `H` of a function on `H ⧸ Q`. -/
noncomputable def inflInd {G : Type} [Group G] [Fintype G] {H Q : Subgroup G}
    [hN : (Q.subgroupOf H).Normal] (β : (↥H ⧸ Q.subgroupOf H) → ℂ) : G → ℂ :=
  Work.Induction.indFun H (fun x : ↥H => β (QuotientGroup.mk x))

/-- **Feit (19)** for the characters of `H/Q` with `⁅H,H⁆ ≤ Q`: for two non-trivial irreducible
characters `β, β'` of `H/Q` with `β'` not the complex conjugate of `β`, the induced characters
`Ind_H^G β`, `Ind_H^G β'` are orthogonal, equal only when `β = β'`. -/
theorem cfInner_inflInd {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (hQ : Q ≠ ⊥)
    (hH' : _root_.commutator ↥H ≤ Q.subgroupOf H) [hN : (Q.subgroupOf H).Normal]
    {β β' : (↥H ⧸ Q.subgroupOf H) → ℂ}
    (hβ : β ∈ Work.CharCore.Irr (↥H ⧸ Q.subgroupOf H))
    (hβ1 : β ≠ (fun _ : ↥H ⧸ Q.subgroupOf H => (1 : ℂ)))
    (hβ' : β' ∈ Work.CharCore.Irr (↥H ⧸ Q.subgroupOf H))
    (hβ'1 : β' ≠ (fun _ : ↥H ⧸ Q.subgroupOf H => (1 : ℂ)))
    (hne : β' ≠ (fun a => star (β a))) :
    Work.CharCore.cfInner (inflInd (H := H) (Q := Q) β) (inflInd (H := H) (Q := Q) β')
      = (if β = β' then (1 : ℂ) else 0) := by
  classical
  obtain ⟨hηIrr, hηQ⟩ := inflateFun_mem_Irr_triv (H := H) (Q := Q) hH' hβ
  obtain ⟨hη'Irr, hη'Q⟩ := inflateFun_mem_Irr_triv (H := H) (Q := Q) hH' hβ'
  have hη1 : (fun x : ↥H => β (QuotientGroup.mk x)) ≠ (fun _ : ↥H => (1 : ℂ)) := by
    intro hh
    refine hβ1 (funext fun a => ?_)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    simpa using congrFun hh x
  have hη'1 : (fun x : ↥H => β' (QuotientGroup.mk x)) ≠ (fun _ : ↥H => (1 : ℂ)) := by
    intro hh
    refine hβ'1 (funext fun a => ?_)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    simpa using congrFun hh x
  have hηne : (fun x : ↥H => β' (QuotientGroup.mk x))
      ≠ (fun x : ↥H => star ((fun x : ↥H => β (QuotientGroup.mk x)) x)) := by
    intro hh
    refine hne (funext fun a => ?_)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    simpa using congrFun hh x
  have hkey := (etaStar_data h hz hQ hηIrr hηQ hη1).2.2.2
    (fun x : ↥H => β' (QuotientGroup.mk x)) hη'Irr hη'Q hη'1 hηne
  simp only [inflInd]
  rw [hkey]
  by_cases hb : β = β'
  · rw [if_pos hb, if_pos (funext fun x => congrFun hb (QuotientGroup.mk x))]
  · rw [if_neg hb, if_neg (fun hh => hb (funext fun a => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      simpa using congrFun hh x))]

/-! ## The family of `η_i^*` -/

theorem etaStar_family {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} (t : G)
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (hQ : Q ≠ ⊥) (hH' : _root_.commutator ↥H ≤ Q.subgroupOf H) :
    ∃ η : Fin ((Nat.card (Submission.Blueprint.twoPoint H t) - 1) / 2) → G → ℂ,
      (∀ i, η i ∈ Work.CharCore.Irr G) ∧
      (∀ i, η i 1 = (Nat.card Q : ℂ) + 1) ∧
      Function.Injective η ∧
      (∀ i, ∀ y : G, y ∈ Q → y ≠ 1 → η i y = 1) := by
  classical
  haveI hN : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := Q) (K := H) h.le).mpr h.normal
  haveI hcomm : IsMulCommutative (↥H ⧸ Q.subgroupOf H) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hH'
  have hoddD : Odd (Nat.card (Submission.Blueprint.twoPoint H t)) :=
    h.stronglyEmbedded.2.2 t h.not_mem
  have hcardA : Nat.card (↥H ⧸ Q.subgroupOf H) = Nat.card (Submission.Blueprint.twoPoint H t) :=
    card_quotient_subgroupOf h
  have hoddA : Odd (Nat.card (↥H ⧸ Q.subgroupOf H)) := hcardA ▸ hoddD
  -- the non-trivial irreducible characters of `H ⧸ Q`
  set L : Finset ((↥H ⧸ Q.subgroupOf H) → ℂ) :=
    (Work.CharCore.Irr (↥H ⧸ Q.subgroupOf H)).erase (fun _ => (1 : ℂ)) with hLdef
  have hLmem : ∀ β, β ∈ L ↔ β ∈ Work.CharCore.Irr (↥H ⧸ Q.subgroupOf H) ∧
      β ≠ (fun _ : ↥H ⧸ Q.subgroupOf H => (1 : ℂ)) := by
    intro β
    rw [hLdef, Finset.mem_erase]
    exact ⟨fun h' => ⟨h'.2, h'.1⟩, fun h' => ⟨h'.2, h'.1⟩⟩
  have hLcard : L.card = Nat.card (Submission.Blueprint.twoPoint H t) - 1 := by
    rw [hLdef, Finset.card_erase_of_mem Work.CharCore.principalChar_mem_Irr,
      card_Irr_eq_card_of_commutative, hcardA]
  -- complex conjugation is a fixed point free involution on `L`
  have hσL : ∀ β ∈ L, (fun a => star (β a)) ∈ L := by
    intro β hβ
    obtain ⟨hβIrr, hβne⟩ := (hLmem β).mp hβ
    rw [hLmem (fun a => star (β a))]
    refine ⟨star_mem_Irr_of_commutative hβIrr, fun hh => hβne (funext fun a => ?_)⟩
    have h1 := congrFun hh a
    simpa using congrArg star h1
  have hfixL : ∀ β ∈ L, (fun a => star (β a)) ≠ β := by
    intro β hβ
    obtain ⟨hβIrr, hβne⟩ := (hLmem β).mp hβ
    exact star_ne_self_of_odd hoddA hβIrr hβne
  obtain ⟨S, hSL, hScard, hSσ⟩ := halfTransversal_exists L (fun β a => star (β a)) hσL
    (fun β => by funext a; simp) hfixL
  have hScard2 : S.card * 2 = Nat.card (Submission.Blueprint.twoPoint H t) - 1 := by
    rw [hScard, hLcard]
  have hn : (Nat.card (Submission.Blueprint.twoPoint H t) - 1) / 2 = S.card := by omega
  -- the induced characters of the elements of `L`
  have hβfacts : ∀ β ∈ L,
      inflInd (H := H) (Q := Q) β ∈ Work.CharCore.Irr G ∧
      inflInd (H := H) (Q := Q) β 1 = (Nat.card Q : ℂ) + 1 ∧
      (∀ y : G, y ∈ Q → y ≠ 1 → inflInd (H := H) (Q := Q) β y = 1) := by
    intro β hβ
    obtain ⟨hβIrr, hβne⟩ := (hLmem β).mp hβ
    obtain ⟨hηIrr, hηQ⟩ := inflateFun_mem_Irr_triv (H := H) (Q := Q) hH' hβIrr
    have hη1 : (fun x : ↥H => β (QuotientGroup.mk x)) ≠ (fun _ : ↥H => (1 : ℂ)) := by
      intro hh
      refine hβne (funext fun a => ?_)
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      simpa using congrFun hh x
    obtain ⟨h1, h2, h3, -⟩ := etaStar_data h hz hQ hηIrr hηQ hη1
    exact ⟨h1, h2, fun y hy hy1 => h3 ⟨y, hy⟩ (by simpa using hy1)⟩
  have hfinj : Set.InjOn (inflInd (H := H) (Q := Q))
      (↑S : Set ((↥H ⧸ Q.subgroupOf H) → ℂ)) := by
    intro β hβS β' hβ'S heq
    by_contra hne
    have hβL : β ∈ L := hSL hβS
    have hβ'L : β' ∈ L := hSL hβ'S
    obtain ⟨hβIrr, hβne⟩ := (hLmem β).mp hβL
    obtain ⟨hβ'Irr, hβ'ne⟩ := (hLmem β').mp hβ'L
    have hneconj : β' ≠ (fun a => star (β a)) := fun hh => hSσ β hβS (hh ▸ hβ'S)
    have hkey := cfInner_inflInd h hz hQ hH' hβIrr hβne hβ'Irr hβ'ne hneconj
    rw [if_neg hne] at hkey
    have hone : Work.CharCore.cfInner (inflInd (H := H) (Q := Q) β)
        (inflInd (H := H) (Q := Q) β') = 1 := by
      rw [heq, Work.CharCore.irr_orthonormal (inflInd (H := H) (Q := Q) β')
        (inflInd (H := H) (Q := Q) β') (hβfacts β' hβ'L).1 (hβfacts β' hβ'L).1]
      exact if_pos rfl
    rw [hkey] at hone
    exact one_ne_zero hone.symm
  refine ⟨fun i => inflInd (H := H) (Q := Q)
      ((S.equivFin.symm (Fin.cast hn i) : ↥S) : (↥H ⧸ Q.subgroupOf H) → ℂ), ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hβfacts _ (hSL (S.equivFin.symm (Fin.cast hn i)).2)).1
  · intro i
    exact (hβfacts _ (hSL (S.equivFin.symm (Fin.cast hn i)).2)).2.1
  · intro i j hij
    have h1 : (S.equivFin.symm (Fin.cast hn i) : ↥S) = (S.equivFin.symm (Fin.cast hn j) : ↥S) :=
      Subtype.ext (hfinj (S.equivFin.symm (Fin.cast hn i)).2
        (S.equivFin.symm (Fin.cast hn j)).2 hij)
    exact Fin.cast_injective hn (S.equivFin.symm.injective h1)
  · intro i y hy hy1
    exact (hβfacts _ (hSL (S.equivFin.symm (Fin.cast hn i)).2)).2.2 y hy hy1

end

end Work.ZassenhausTwoGroup
