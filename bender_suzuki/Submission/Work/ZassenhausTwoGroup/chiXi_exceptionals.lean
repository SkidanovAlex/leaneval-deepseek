import Mathlib
import Submission.Work.ZassenhausTwoGroup.FeitThm2
import Submission.Work.CharCore.Main
import Submission.Work.Induction.All
import Submission.Work.ZassenhausTwoGroup.zetaStar_norm
import Submission.Work.ZassenhausTwoGroup.bf35_chars
import Submission.Work.ZassenhausTwoGroup.hchi_orb
import Submission.Work.ZassenhausTwoGroup.etaStar_data
import Submission.Work.ZassenhausTwoGroup.orbitData
import Submission.Work.ZassenhausTwoGroup.chiXi_not_const
import Submission.Work.ZassenhausTwoGroup.even_card_Q
import Submission.Work.ZassenhausTwoGroup.good_card_ge
import Submission.Work.ZassenhausTwoGroup.good_is_constituent
import Submission.Work.ZassenhausTwoGroup.exists_exceptional_constituent
import Submission.Work.ZassenhausTwoGroup.ind_one_constituent_const
import Submission.Work.ZassenhausTwoGroup.commutator_HQ
import Submission.Work.ZassenhausTwoGroup.counting_abstract

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausTwoGroup

set_option maxHeartbeats 1000000

/-- Feit's construction `(21)`-`(24)`: in the split rank-one Zassenhaus set-up with `Q` not a
`2`-group and `|twoPoint H t| ≠ |Q| - 1`, the induced character `Ind_Q^G ζ₁` of a non-trivial
linear character `ζ₁` of `Q` has a *unique* exceptional irreducible constituent `χ_κ`, appearing
with multiplicity one, whose complement `Ind_Q^G ζ₁ - χ_κ` is a character of norm `|twoPoint H t|`
which is constant on `Q ∖ 1`, and `χ_κ` is orthogonal to `Ind_Q^G 1_Q`. -/
theorem chiXi_exceptionals {G : Type} [Group G] [Fintype G] [IsSimpleGroup G] (H Q : Subgroup G) [Fintype ↥Q] (t : G)
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (hQ2 : ¬ IsPGroup 2 Q) (hne : Nat.card (Submission.Blueprint.twoPoint H t) ≠ Nat.card Q - 1)
    (h2 : FeitThm2Prop)
    {ζ₁ : ↥Q → ℂ} (hζ : ζ₁ ∈ Work.CharCore.Irr ↥Q) (hζ1 : ζ₁ ≠ 1) (hlin : ζ₁ 1 = 1) :
    ∃ (χκ : G → ℂ) (γ : ℂ),
      χκ ∈ Work.CharCore.Irr G ∧
      Work.CharCore.cfInner χκ (Work.Induction.indFun Q ζ₁) = 1 ∧
      Work.CharCore.IsChar (Work.Induction.indFun Q ζ₁ - χκ) ∧
      Work.CharCore.cfInner (Work.Induction.indFun Q ζ₁ - χκ)
        (Work.Induction.indFun Q ζ₁ - χκ) = (Nat.card (Submission.Blueprint.twoPoint H t) : ℂ) ∧
      (∀ y : ↥Q, y ≠ 1 → (Work.Induction.indFun Q ζ₁ - χκ) (y : G) = γ) ∧
      Work.CharCore.cfInner χκ (Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ))) = 0 := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite ↥H
  -- `Work.CharCore.Irr ↥Q` does not depend on the chosen `Fintype` instance
  have hIrrQ : ∀ {i j : Fintype ↥Q} {χ : ↥Q → ℂ},
      (χ ∈ @Work.CharCore.Irr ↥Q _ i) → (χ ∈ @Work.CharCore.Irr ↥Q _ j) :=
    fun {i j χ} hh => (Work.ZassenhausTwoGroup.mem_Irr_of_fintype_iff i j).mp hh
  -- ## Feit's Theorem 2 data (rewritten in the local `Fintype ↥Q` instance)
  obtain ⟨ε, hε, c, χ₀, hχirr₀, hdiff, hvan, hval, hconst⟩ := h2 G H Q t h hZ hQ2 hne
  have hχirr₀' : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → χ₀ ζ ∈ Work.CharCore.Irr G :=
    fun ζ hζm hζn => hχirr₀ ζ (hIrrQ hζm) hζn
  have hdiff' : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
      Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' → ∀ g : G,
        (ζ' 1) * Work.Induction.indFun Q ζ g - (ζ 1) * Work.Induction.indFun Q ζ' g
          = (ε : ℂ) * ((ζ' 1) * χ₀ ζ g - (ζ 1) * χ₀ ζ' g) :=
    fun ζ hζm hζn ζ' hζ'm hζ'n hNI g => hdiff ζ (hIrrQ hζm) hζn ζ' (hIrrQ hζ'm) hζ'n hNI g
  have hvan' : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
      Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' → ∀ g : G,
        (¬ ∃ x : G, x * g * x⁻¹ ∈ Q ∧ x * g * x⁻¹ ≠ 1) →
          (ζ' 1) * χ₀ ζ g - (ζ 1) * χ₀ ζ' g = 0 :=
    fun ζ hζm hζn ζ' hζ'm hζ'n hNI g hg =>
      hvan ζ (hIrrQ hζm) hζn ζ' (hIrrQ hζ'm) hζ'n hNI g hg
  have hval' : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ y : G, y ∈ Q → y ≠ 1 →
      χ₀ ζ y = (ε : ℂ) * Work.Induction.indFun Q ζ y + (ζ 1) * (c : ℂ) :=
    fun ζ hζm hζn y hy hy1 => hval ζ (hIrrQ hζm) hζn y hy hy1
  have hconst' : ∀ φ ∈ Work.CharCore.Irr G,
      (∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → φ ≠ χ₀ ζ) →
      ∀ y : G, y ∈ Q → y ≠ 1 → ∀ y' : G, y' ∈ Q → y' ≠ 1 → φ y = φ y' :=
    fun φ hφ h y hy hy1 y' hy' hy'1 =>
      hconst φ hφ (fun ζ hζm hζn => h ζ (hIrrQ hζm) hζn) y hy hy1 y' hy' hy'1
  -- ## Notation
  set q : ℕ := Nat.card ↥(Submission.Blueprint.twoPoint H t) with hq
  set Ξ : G → ℂ := Work.Induction.indFun Q ζ₁ with hΞ
  set Ξ₀ : G → ℂ := Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ)) with hΞ₀
  -- `Q ≠ ⊥`
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have hev : Even (Nat.card ↥Q) := even_card_Q h
    rw [hbot] at hev
    simp at hev
  -- ## `Ξ` is a character of norm `q + 1`
  have hΞchar : Work.CharCore.IsChar Ξ := Work.Induction.isChar_indFun_irr (hIrrQ hζ)
  have hΞnorm : Work.CharCore.cfInner Ξ Ξ = (q : ℂ) + 1 := zetaStar_norm h hZ hζ hζ1 hlin
  -- ## the coefficients of `Ξ` in the basis `Irr G`
  obtain ⟨cf, hcf⟩ := Work.CharCore.isChar_iff_exists_nat_coeffs.mp hΞchar
  have hcfspec : ∀ x : ↥(Work.CharCore.Irr G),
      Work.CharCore.cfInner Ξ (x : G → ℂ) = (cf x : ℂ) := by
    intro x
    rw [hcf, Work.CharCore.cfInner_irr_sum_smul_left]
    refine (Finset.sum_eq_single x ?_ ?_).trans ?_
    · intro y _ hy
      rw [Work.CharCore.irr_orthonormal (y : G → ℂ) (x : G → ℂ) y.2 x.2,
        if_neg (fun hh => hy (Subtype.ext hh)), mul_zero]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
    · rw [Work.CharCore.irr_orthonormal (x : G → ℂ) (x : G → ℂ) x.2 x.2, if_pos rfl, mul_one]
  -- the norm in terms of the squares of the coefficients
  have hsumC : (∑ x : ↥(Work.CharCore.Irr G), ((cf x : ℂ)) ^ 2) = (q : ℂ) + 1 := by
    have hsumZ : (∑ x : ↥(Work.CharCore.Irr G), (((cf x : ℤ)) : ℂ) ^ 2) = (q : ℂ) + 1 := by
      have hsq := Work.CharCore.cfInner_eq_sum_sq (s := Work.CharCore.Irr G)
        (fun _ hx => hx) (fun x : ↥(Work.CharCore.Irr G) => (cf x : ℤ))
      have h1 : Ξ = ∑ x : ↥(Work.CharCore.Irr G), (((cf x : ℤ)) : ℂ) • (x : G → ℂ) := by
        rw [hcf]
        exact Finset.sum_congr rfl (fun x _ => by simp)
      rw [h1] at hΞnorm
      rw [hsq] at hΞnorm
      exact hΞnorm
    rw [← hsumZ]
    exact Finset.sum_congr rfl (fun x _ => by push_cast; ring)
  have hsumN : (∑ x : ↥(Work.CharCore.Irr G), (cf x) ^ 2) = q + 1 := by
    have hcast : ((∑ x : ↥(Work.CharCore.Irr G), (cf x) ^ 2 : ℕ) : ℂ) = ((q + 1 : ℕ) : ℂ) := by
      push_cast
      simpa using hsumC
    exact Nat.cast_injective hcast
  -- ## the "good" (non-exceptional, non-trivial) characters
  set Sg : Finset (G → ℂ) := (Work.CharCore.Irr G).filter
    (fun ψ => ψ ≠ (fun _ : G => (1 : ℂ)) ∧
      ∀ κ ∈ Work.CharCore.Irr ↥Q, κ ≠ 1 → ψ ≠ χ₀ κ) with hSg
  set A : Finset ↥(Work.CharCore.Irr G) :=
    Finset.univ.filter (fun x => (x : G → ℂ) ∈ Sg) with hA
  set B : Finset ↥(Work.CharCore.Irr G) := Finset.univ.filter
    (fun x => (∃ κ ∈ Work.CharCore.Irr ↥Q, κ ≠ 1 ∧ (x : G → ℂ) = χ₀ κ) ∧ cf x ≠ 0) with hB
  have memSg : ∀ ψ : G → ℂ, ψ ∈ Sg ↔ ψ ∈ Work.CharCore.Irr G ∧ ψ ≠ (fun _ : G => (1 : ℂ)) ∧
      (∀ κ ∈ Work.CharCore.Irr ↥Q, κ ≠ 1 → ψ ≠ χ₀ κ) := by
    intro ψ
    rw [hSg]
    simp only [Finset.mem_filter]
  have memA : ∀ x : ↥(Work.CharCore.Irr G), x ∈ A ↔ (x : G → ℂ) ∈ Sg := by
    intro x
    rw [hA]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have memB : ∀ x : ↥(Work.CharCore.Irr G), x ∈ B ↔
      (∃ κ ∈ Work.CharCore.Irr ↥Q, κ ≠ 1 ∧ (x : G → ℂ) = χ₀ κ) ∧ cf x ≠ 0 := by
    intro x
    rw [hB]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- ## Feit's Lemma 3.5 (character form) for this exceptional family
  have hq_le_Sg : q ≤ Sg.card :=
    good_card_ge H Q t h hZ hQ2 hne hχirr₀' hdiff' hε hvan' hval'
  have hAcard_eq : A.card = Sg.card := by
    refine Finset.card_bij (fun x (_ : x ∈ A) => (x : G → ℂ)) ?_ ?_ ?_
    · intro x hx
      exact (memA x).mp hx
    · intro x hx y hy hxy
      exact Subtype.ext hxy
    · intro y hy
      exact ⟨⟨y, ((memSg y).mp hy).1⟩, (memA _).mpr hy, rfl⟩
  have hAcard : q ≤ A.card := by rw [hAcard_eq]; exact hq_le_Sg
  -- every good character is a constituent of `Ξ`
  have hAc : ∀ a ∈ A, 1 ≤ cf a := by
    intro a ha
    have haSg : (a : G → ℂ) ∈ Sg := (memA a).mp ha
    obtain ⟨haIrr, ha1, haexc⟩ := (memSg (a : G → ℂ)).mp haSg
    have hne : Work.CharCore.cfInner (a : G → ℂ) Ξ ≠ 0 :=
      good_is_constituent h hZ hζ hζ1 hlin hconst' a.2 ha1 haexc
    have hcc : Work.CharCore.cfInner (a : G → ℂ) Ξ = (cf a : ℂ) := by
      rw [Work.CharCore.cfInner_conj_symm, hcfspec a]
      simp
    rw [hcc] at hne
    exact Nat.one_le_iff_ne_zero.mpr (fun hz => hne (by rw [hz]; norm_num))
  -- there is at least one exceptional constituent
  have hBne : B.Nonempty := by
    obtain ⟨κ, hκ, hκ1, hcon⟩ :=
      exists_exceptional_constituent h hZ hζ hζ1 hlin hconst'
        (chiXi_not_const h hZ hne hζ hζ1 hlin)
    refine ⟨⟨χ₀ κ, hχirr₀' κ hκ hκ1⟩, ?_⟩
    rw [memB]
    refine ⟨⟨κ, hκ, hκ1, rfl⟩, ?_⟩
    intro hzero
    refine hcon ?_
    rw [Work.CharCore.cfInner_conj_symm, hcfspec ⟨χ₀ κ, hχirr₀' κ hκ hκ1⟩, hzero]
    simp
  have hBc : ∀ b ∈ B, 1 ≤ cf b := by
    intro b hb
    exact Nat.one_le_iff_ne_zero.mpr ((memB b).mp hb).2
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have h1 : (x : G → ℂ) ∈ Sg := (memA x).mp hxA
    have h2 := (memSg (x : G → ℂ)).mp h1
    obtain ⟨κ, hκ, hκ1, hκeq⟩ := ((memB x).mp hxB).1
    exact h2.2.2 κ hκ hκ1 hκeq
  -- ## the count
  obtain ⟨hAcard', hBcard, hAc1, hBc1, hzero⟩ :=
    counting_abstract cf A B q hsumN hdisj hAcard hAc hBne hBc
  -- ## the unique exceptional constituent
  obtain ⟨hb, hBeq⟩ := Finset.card_eq_one.mp hBcard
  have hb_mem : hb ∈ B := by rw [hBeq]; exact Finset.mem_singleton_self hb
  have hb_coeff : cf hb = 1 := hBc1 hb hb_mem
  have hcouple : Work.CharCore.cfInner (hb : G → ℂ) Ξ = 1 := by
    rw [Work.CharCore.cfInner_conj_symm, hcfspec hb, hb_coeff]
    simp
  -- the full decomposition `Ξ = ∑_{A} χ + hb`
  have hdecomp : Ξ = (∑ x ∈ A, (x : G → ℂ)) + (hb : G → ℂ) := by
    conv_lhs => rw [hcf]
    rw [← Finset.sum_subset (Finset.subset_univ (A ∪ B)) (fun x _ hx => by
      rw [hzero x (fun hxA => hx (Finset.mem_union_left B hxA))
        (fun hxB => hx (Finset.mem_union_right A hxB))]
      simp)]
    rw [Finset.sum_union hdisj]
    congr 1
    · exact Finset.sum_congr rfl (fun x hx => by rw [hAc1 x hx]; simp)
    · rw [hBeq, Finset.sum_singleton, hb_coeff]; simp
  have hdecomp' : Ξ - (hb : G → ℂ) = ∑ x ∈ A, (x : G → ℂ) := by
    rw [hdecomp, add_sub_cancel_right]
  -- ## the constant value on `Q ∖ 1`
  obtain ⟨y₀, hy₀⟩ : ∃ y : ↥Q, y ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hcard : Nat.card ↥Q ≤ 1 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_le_one_iff.mpr (fun a b => by rw [hcon a, hcon b])
    have hev : Even (Nat.card ↥Q) := even_card_Q h
    obtain ⟨k, hk⟩ := hev
    have hpos : 0 < Nat.card ↥Q := Nat.card_pos
    omega
  set γ : ℂ := Ξ (y₀ : G) - (hb : G → ℂ) (y₀ : G) with hγ
  have hconstA : ∀ x ∈ A, ∀ y : ↥Q, y ≠ 1 →
      (x : G → ℂ) (y : G) = (x : G → ℂ) (y₀ : G) := by
    intro x hx y hy
    have hxSg : (x : G → ℂ) ∈ Sg := (memA x).mp hx
    obtain ⟨-, -, hxexc⟩ := (memSg (x : G → ℂ)).mp hxSg
    exact hconst' (x : G → ℂ) x.2 hxexc (y : G) y.2 (fun hh => hy (Subtype.ext hh)) (y₀ : G) y₀.2
      (fun hh => hy₀ (Subtype.ext hh))
  have hconst_val : ∀ y : ↥Q, y ≠ 1 → (Ξ - (hb : G → ℂ)) (y : G) = γ := by
    intro y hy
    have h1 : (Ξ - (hb : G → ℂ)) (y : G) = ∑ x ∈ A, (x : G → ℂ) (y : G) := by
      rw [hdecomp', Finset.sum_apply]
    have h2 : γ = ∑ x ∈ A, (x : G → ℂ) (y₀ : G) := by
      rw [hγ, ← Pi.sub_apply, hdecomp', Finset.sum_apply]
    rw [h1, h2]
    exact Finset.sum_congr rfl (fun x hx => hconstA x hx y hy)
  -- ## non-constancy of `hb`
  have hb_nonconst : ∃ y y' : ↥Q, y ≠ 1 ∧ y' ≠ 1 ∧
      (hb : G → ℂ) (y : G) ≠ (hb : G → ℂ) (y' : G) := by
    obtain ⟨y, y', hy, hy', hxy⟩ := chiXi_not_const h hZ hne hζ hζ1 hlin
    refine ⟨y, y', hy, hy', fun hh => hxy ?_⟩
    have h1 := hconst_val y hy
    have h2 := hconst_val y' hy'
    rw [Pi.sub_apply] at h1 h2
    rw [hh] at h1
    have h4 : Ξ (y : G) - (hb : G → ℂ) (y' : G) = Ξ (y' : G) - (hb : G → ℂ) (y' : G) :=
      h1.trans h2.symm
    have h5 : Ξ (y : G) - Ξ (y' : G) = 0 := by
      have h6 : (Ξ (y : G) - (hb : G → ℂ) (y' : G))
          - (Ξ (y' : G) - (hb : G → ℂ) (y' : G)) = 0 := sub_eq_zero.mpr h4
      ring_nf at h6
      exact h6
    exact sub_eq_zero.mp h5
  -- ## `Ξ - hb` is a character, of norm `q`
  have hischar : Work.CharCore.IsChar (Ξ - (hb : G → ℂ)) := by
    rw [hdecomp']
    exact Work.CharCore.IsChar.sum (fun x _ => Work.CharCore.IsChar.of_mem_Irr x.2)
  have hinner' : Work.CharCore.cfInner Ξ (hb : G → ℂ) = 1 := by
    rw [Work.CharCore.cfInner_conj_symm, hcouple]
    simp
  have hnorm : Work.CharCore.cfInner (Ξ - (hb : G → ℂ)) (Ξ - (hb : G → ℂ)) = (q : ℂ) := by
    have h1 : Work.CharCore.cfInner (Ξ - (hb : G → ℂ)) (Ξ - (hb : G → ℂ))
        = Work.CharCore.cfInner Ξ Ξ - Work.CharCore.cfInner (hb : G → ℂ) Ξ
          - (Work.CharCore.cfInner Ξ (hb : G → ℂ)
            - Work.CharCore.cfInner (hb : G → ℂ) (hb : G → ℂ)) := by
      rw [Work.CharCore.cfInner_sub_right, Work.CharCore.cfInner_sub_left,
        Work.CharCore.cfInner_sub_left]
    rw [h1, hΞnorm, hcouple, hinner',
      Work.CharCore.irr_orthonormal (hb : G → ℂ) (hb : G → ℂ) hb.2 hb.2, if_pos rfl]
    ring
  -- ## `hb` is orthogonal to `Ind_Q^G 1_Q`
  have hortho : Work.CharCore.cfInner (hb : G → ℂ) Ξ₀ = 0 := by
    by_contra hne0
    have hH' : _root_.commutator ↥H ≤ Q.subgroupOf H := commutator_HQ h hZ
    have hcst : ∀ y y' : ↥Q, y ≠ 1 → y' ≠ 1 → (hb : G → ℂ) (y : G) = (hb : G → ℂ) (y' : G) :=
      ind_one_constituent_const h hZ hQne hH' hb.2 hne0
    obtain ⟨y, y', hy, hy', hxy⟩ := hb_nonconst
    exact hxy (hcst y y' hy hy')
  -- ## conclusion
  refine ⟨(hb : G → ℂ), γ, hb.2, hcouple, hischar, hnorm, hconst_val, hortho⟩

end Work.ZassenhausTwoGroup
