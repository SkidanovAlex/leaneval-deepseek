import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.chiXi_exceptionals
import Submission.Work.ZassenhausTwoGroup.zetaStar_norm
import Submission.Work.ZassenhausTwoGroup.etaStar_data
import Submission.Work.ZassenhausTwoGroup.chiXi_Xi0_inner
import Submission.Work.ZassenhausTwoGroup.chiGamma_inner
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausTwoGroup

set_option maxHeartbeats 1000000

/-- **Feit (21)–(24) in the shape needed by the assembly.**  From Feit's Theorem 2 data (the
exceptional-character map `χ₀` with its sign `ε` and its constant `c`, i.e. the conjunction
proved by `FeitThm2Prop` at this set-up) there is a non-trivial irreducible character `κ` of `Q`
whose exceptional character `χ₀ κ` has degree `|D| = |twoPoint H t|`.

The proof repeats the constituent analysis of `chiXi_exceptionals` (the induced character
`Ξ = Ind_Q^G ζ₁` has exactly `|D|` non-exceptional irreducible constituents with multiplicity one
and exactly one exceptional constituent, which is a `χ₀ κ`) and then the degree computation of
`chi1_degree_eq`: the difference `Ξ - χ₀ κ` is a class function of norm `|D|` which is constant
on `Q ∖ 1` and orthogonal to `Ind_Q^G 1_Q`, and two Frobenius-reciprocity identities
(`chiGamma_inner`) together with `⟨Ξ, Ind_Q^G 1_Q⟩ = |D|` (`chiXi_Xi0_inner`) force that constant
to vanish and give `(χ₀ κ)(1) = |D|`. -/
theorem exists_exceptional_orbit_deg {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (H Q : Subgroup G) [Fintype ↥Q] (t : G)
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (hQ2 : ¬ IsPGroup 2 Q)
    (hne : Nat.card (Submission.Blueprint.twoPoint H t) ≠ Nat.card Q - 1)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {c : ℤ} {χ₀ : (↥Q → ℂ) → G → ℂ}
    (hχirr : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → χ₀ ζ ∈ Work.CharCore.Irr G)
    (hdiff : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
      Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' → ∀ g : G,
        (ζ' 1) * Work.Induction.indFun Q ζ g - (ζ 1) * Work.Induction.indFun Q ζ' g
          = (ε : ℂ) * ((ζ' 1) * χ₀ ζ g - (ζ 1) * χ₀ ζ' g))
    (hvan : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
      Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' → ∀ g : G,
        (¬ ∃ x : G, x * g * x⁻¹ ∈ Q ∧ x * g * x⁻¹ ≠ 1) →
          (ζ' 1) * χ₀ ζ g - (ζ 1) * χ₀ ζ' g = 0)
    (hval : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ y : G, y ∈ Q → y ≠ 1 →
      χ₀ ζ y = (ε : ℂ) * Work.Induction.indFun Q ζ y + (ζ 1) * (c : ℂ))
    (hconst : ∀ φ ∈ Work.CharCore.Irr G,
      (∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → φ ≠ χ₀ ζ) →
      ∀ y : G, y ∈ Q → y ≠ 1 → ∀ y' : G, y' ∈ Q → y' ≠ 1 → φ y = φ y')
    {ζ₁ : ↥Q → ℂ} (hζ : ζ₁ ∈ Work.CharCore.Irr ↥Q) (hζ1 : ζ₁ ≠ 1) (hlin : ζ₁ 1 = 1) :
    ∃ κ : ↥Q → ℂ, κ ∈ Work.CharCore.Irr ↥Q ∧ κ ≠ 1 ∧
      (χ₀ κ) 1 = (Nat.card (Submission.Blueprint.twoPoint H t) : ℂ) := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite ↥H
  have hZ : Submission.Blueprint.IsZassenhaus H := hz
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
  -- `Work.CharCore.Irr ↥Q` does not depend on the chosen `Fintype ↥Q` instance
  have hIrrQ : ∀ {i j : Fintype ↥Q} {χ : ↥Q → ℂ},
      (χ ∈ @Work.CharCore.Irr ↥Q _ i) → (χ ∈ @Work.CharCore.Irr ↥Q _ j) :=
    fun {i j χ} hh => (Work.ZassenhausTwoGroup.mem_Irr_of_fintype_iff i j).mp hh
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
    good_card_ge H Q t h hZ hQ2 hne hχirr hdiff hε hvan hval
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
    have hne' : Work.CharCore.cfInner (a : G → ℂ) Ξ ≠ 0 :=
      good_is_constituent h hZ hζ hζ1 hlin hconst a.2 ha1 haexc
    have hcc : Work.CharCore.cfInner (a : G → ℂ) Ξ = (cf a : ℂ) := by
      rw [Work.CharCore.cfInner_conj_symm, hcfspec a]
      simp
    rw [hcc] at hne'
    exact Nat.one_le_iff_ne_zero.mpr (fun hz => hne' (by rw [hz]; norm_num))
  -- there is at least one exceptional constituent
  have hBne : B.Nonempty := by
    obtain ⟨κ, hκ, hκ1, hcon⟩ :=
      exists_exceptional_constituent h hZ hζ hζ1 hlin hconst
        (chiXi_not_const h hZ hne hζ hζ1 hlin)
    refine ⟨⟨χ₀ κ, hχirr κ hκ hκ1⟩, ?_⟩
    rw [memB]
    refine ⟨⟨κ, hκ, hκ1, rfl⟩, ?_⟩
    intro hzero
    refine hcon ?_
    rw [Work.CharCore.cfInner_conj_symm, hcfspec ⟨χ₀ κ, hχirr κ hκ hκ1⟩, hzero]
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
    exact hconst (x : G → ℂ) x.2 hxexc (y : G) y.2 (fun hh => hy (Subtype.ext hh)) (y₀ : G) y₀.2
      (fun hh => hy₀ (Subtype.ext hh))
  have hconst_val : ∀ y : ↥Q, y ≠ 1 → (Ξ - (hb : G → ℂ)) (y : G) = γ := by
    intro y hy
    have h1 : (Ξ - (hb : G → ℂ)) (y : G) = ∑ x ∈ A, (x : G → ℂ) (y : G) := by
      rw [hdecomp', Finset.sum_apply]
    have h2 : γ = ∑ x ∈ A, (x : G → ℂ) (y₀ : G) := by
      rw [hγ, ← Pi.sub_apply, hdecomp', Finset.sum_apply]
    rw [h1, h2]
    exact Finset.sum_congr rfl (fun x hx => hconstA x hx y hy)
  -- ## `hb` is orthogonal to `Ind_Q^G 1_Q`
  have hortho : Work.CharCore.cfInner (hb : G → ℂ) Ξ₀ = 0 := by
    by_contra hne0
    have hH' : _root_.commutator ↥H ≤ Q.subgroupOf H := commutator_HQ h hZ
    have hcst : ∀ y y' : ↥Q, y ≠ 1 → y' ≠ 1 →
        (hb : G → ℂ) (y : G) = (hb : G → ℂ) (y' : G) :=
      ind_one_constituent_const h hZ hQne hH' hb.2 hne0
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
    obtain ⟨y, y', hy, hy', hxy⟩ := hb_nonconst
    exact hxy (hcst y y' hy hy')
  -- ## `hb` is an exceptional character `χ₀ κ`
  obtain ⟨⟨κ, hκ, hκ1, hκeq⟩, -⟩ := (memB hb).mp hb_mem
  -- ## the degree computation: `(χ₀ κ) 1 = q`
  have hself : Work.CharCore.cfInner Ξ Ξ = (q : ℂ) + 1 := hΞnorm
  have hX0 : Work.CharCore.cfInner Ξ Ξ₀ = (q : ℂ) := by
    rw [hq, hΞ, hΞ₀]
    exact chiXi_Xi0_inner h hZ hζ hζ1 hlin
  have hclassX : Work.CharCore.IsClassFun Ξ := by
    rw [hΞ]; exact Work.Induction.isClassFun_indFun Q ζ₁
  have hclassG : Work.CharCore.IsClassFun (Ξ - (hb : G → ℂ)) :=
    hclassX.sub (Work.CharCore.isClassFun_of_mem_Irr hb.2)
  have hGXi : Work.CharCore.cfInner (Ξ - (hb : G → ℂ)) Ξ = (q : ℂ) := by
    rw [Work.CharCore.cfInner_sub_left, hself, hcouple]; ring
  have hGX0 : Work.CharCore.cfInner (Ξ - (hb : G → ℂ)) Ξ₀ = (q : ℂ) := by
    rw [Work.CharCore.cfInner_sub_left, hX0, hortho]; ring
  obtain ⟨hid1, hid2⟩ :=
    chiGamma_inner h hζ hζ1 hlin hclassG hconst_val
  have hmnz : (Nat.card ↥Q : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hkey1 : (Nat.card ↥Q : ℂ) * (q : ℂ) = (Ξ - (hb : G → ℂ)) 1 - γ := by
    rw [← hGXi]; exact hid1
  have hkey2 : (Nat.card ↥Q : ℂ) * (q : ℂ)
      = (Ξ - (hb : G → ℂ)) 1 + ((Nat.card ↥Q : ℂ) - 1) * γ := by
    rw [← hGX0]; exact hid2
  have hγ0 : γ = 0 := by
    have hsub : (Ξ - (hb : G → ℂ)) 1 - γ
        = (Ξ - (hb : G → ℂ)) 1 + ((Nat.card ↥Q : ℂ) - 1) * γ := hkey1.symm.trans hkey2
    have hmul : (Nat.card ↥Q : ℂ) * γ = 0 := by linear_combination -hsub
    exact (mul_eq_zero.mp hmul).resolve_left hmnz
  have hXi1 : Ξ 1 = ((Nat.card ↥Q : ℂ) + 1) * (q : ℂ) := by
    rw [hΞ, Work.Induction.indFun_apply_one, hlin, mul_one, hq, Q_index_eq_of_isSplitRankOne h]
    push_cast
    ring
  have hΓ1 : (Ξ - (hb : G → ℂ)) 1 = (Nat.card ↥Q : ℂ) * (q : ℂ) := by
    have hh := hkey1
    rw [hγ0, sub_zero] at hh
    exact hh.symm
  have hχ1 : (hb : G → ℂ) 1 = (q : ℂ) := by
    have hd : (Ξ - (hb : G → ℂ)) 1 = Ξ 1 - (hb : G → ℂ) 1 := rfl
    rw [hΓ1, hXi1] at hd
    linear_combination hd
  refine ⟨κ, hκ, hκ1, ?_⟩
  rw [← hκeq]
  have hqcast : (q : ℂ) = (Nat.card (Submission.Blueprint.twoPoint H t) : ℂ) := by
    rw [hq]
  rw [← hqcast]
  exact hχ1

end Work.ZassenhausTwoGroup
