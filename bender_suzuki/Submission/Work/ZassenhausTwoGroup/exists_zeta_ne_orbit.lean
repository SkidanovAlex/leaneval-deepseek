import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.card_H_classes_eq_card_induced
import Submission.Work.ZassenhausTwoGroup.fpf_on_Q
import Submission.Work.ZassenhausTwoGroup.card_twoPoint_dvd
import Submission.Work.ZassenhausTwoGroup.even_card_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausTwoGroup

open Submission.Blueprint
open Classical

set_option linter.style.haveILetI false

/-!
# A second non-trivial `Q`-character with a different induced character

In the split rank-one Zassenhaus set-up `H = Q ⋊ D`, `D = twoPoint H t`, the induction map
`ζ ↦ Ind_Q^G ζ` is not constant on the non-trivial irreducible characters of `Q`, *provided*
`|D| ≠ |Q| - 1`.

The argument is the standard orbit count, in the form in which the area's
`card_H_classes_eq_card_induced` makes it available:

* if `Ind_Q^G` were constant on `Irr Q ∖ 1`, then the image of `ζ ↦ Ind_Q^G ζ` on `Irr Q ∖ 1`
  would be a singleton, so by `card_H_classes_eq_card_induced` the group `H` would have exactly
  one conjugacy class meeting `Q ∖ 1`, i.e. `H` acts transitively by conjugation on `Q ∖ 1`;
* then the `H`-class of any `1 ≠ x ∈ Q` is all of `Q ∖ 1`, so `|Q| - 1` (the size of that class)
  divides `|H| = |Q| · |D|` (`card_eq_mul_card_twoPoint`);
* as `gcd (|Q| - 1) |Q| = 1`, this gives `|Q| - 1 ∣ |D|`, and `card_twoPoint_dvd` gives
  `|D| ∣ |Q| - 1`, so `|D| = |Q| - 1`, contradicting `hne`.

The orbit–stabiliser step is proved as an explicit bijection
`H ≃ (Q ∖ 1) × (stabiliser of x₀)` (`card_dvd_of_conj_transitive`), so that no `MulAction`
instance on the subgroup `Q` is required.
-/

/-! ## Auxiliary lemmas -/

/-- **Orbit–stabiliser count.**  Let `Q` be normalised by `H` and let `x₀ ∈ Q ∖ 1`. If every
element of `Q ∖ 1` is `H`-conjugate to `x₀`, then the `H`-conjugacy class of `x₀` is all of
`Q ∖ 1`; its cardinality is the index of the stabiliser of `x₀`, whence `|Q| - 1 ∣ |H|`.

The proof builds the bijection `k ↦ (k x₀ k⁻¹, σ(k x₀ k⁻¹)⁻¹ k)` explicitly, with `σ` a section
of the (surjective) conjugation map `H → Q ∖ 1`. -/
private theorem card_dvd_of_conj_transitive {G : Type} [Group G] [Fintype G]
    {H Q : Subgroup G} (hQN : H ≤ Subgroup.normalizer (Q : Set G))
    {x₀ : G} (hx₀ : x₀ ∈ Q) (hx₀1 : x₀ ≠ 1)
    (htrans : ∀ y : G, y ∈ Q → y ≠ 1 → ∃ k : G, k ∈ H ∧ k * x₀ * k⁻¹ = y) :
    Nat.card Q - 1 ∣ Nat.card H := by
  classical
  let ψ : ↥H → ↥Q := fun k => ⟨(k : G) * x₀ * (k : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hQN k.2) x₀).mp hx₀⟩
  have hψ_ne : ∀ k, ψ k ≠ 1 := by
    intro k h
    apply hx₀1
    have hc := congrArg (fun z : ↥Q => (z : G)) h
    simp only [ψ, Subgroup.coe_one] at hc
    have : x₀ = (k : G)⁻¹ * 1 * (k : G) := by rw [← hc]; group
    simpa using this
  let φ : ↥H → {y : ↥Q // y ≠ 1} := fun k => ⟨ψ k, hψ_ne k⟩
  have hφ_iff : ∀ k j : ↥H, φ k = φ j ↔ ψ k = ψ j := fun k j => Subtype.ext_iff
  have hsurj : Function.Surjective φ := by
    intro y
    have hyQ : (y.1 : G) ∈ Q := y.1.2
    have hy1 : (y.1 : G) ≠ 1 := fun h => y.2 (Subtype.ext h)
    obtain ⟨k, hkH, hk⟩ := htrans (y.1 : G) hyQ hy1
    refine ⟨⟨k, hkH⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    simpa only [φ, ψ, Subgroup.coe_mk] using hk
  let σ : {y : ↥Q // y ≠ 1} → ↥H := fun y => Classical.choose (hsurj y)
  have hσ : ∀ y, φ (σ y) = y := fun y => Classical.choose_spec (hsurj y)
  have hmem : ∀ k : ↥H, φ ((σ (φ k))⁻¹ * k) = φ 1 := by
    intro k
    rw [hφ_iff]
    apply Subtype.ext
    have hψ1 : (ψ (1 : ↥H) : G) = x₀ := by simp [ψ]
    rw [hψ1]
    have hψσ : ψ (σ (φ k)) = ψ k := congrArg Subtype.val (hσ (φ k))
    calc (ψ ((σ (φ k))⁻¹ * k) : G)
        = ((σ (φ k) : ↥H) : G)⁻¹ * (ψ k : G) * ((σ (φ k) : ↥H) : G) := by
          simp only [ψ, Subgroup.coe_mul, Subgroup.coe_inv]; group
      _ = ((σ (φ k) : ↥H) : G)⁻¹ * (ψ (σ (φ k)) : G) * ((σ (φ k) : ↥H) : G) := by
          rw [hψσ]
      _ = x₀ := by simp only [ψ]; group
  have hfirst : ∀ p : {y : ↥Q // y ≠ 1} × {c : ↥H // φ c = φ 1},
      φ (σ p.1 * p.2.1) = p.1 := by
    intro p
    have hp2 : ψ p.2.1 = ψ (1 : ↥H) := (hφ_iff p.2.1 1).mp p.2.2
    have key : φ (σ p.1 * p.2.1) = φ (σ p.1) := by
      rw [hφ_iff]
      apply Subtype.ext
      calc (ψ (σ p.1 * p.2.1) : G)
          = ((σ p.1 : ↥H) : G) * (ψ p.2.1 : G) * ((σ p.1 : ↥H) : G)⁻¹ := by
            simp only [ψ, Subgroup.coe_mul]; group
        _ = ((σ p.1 : ↥H) : G) * (ψ (1 : ↥H) : G) * ((σ p.1 : ↥H) : G)⁻¹ := by rw [hp2]
        _ = (ψ (σ p.1) : G) := by simp only [ψ, Subgroup.coe_one]; group
    rw [key, hσ p.1]
  let e : ↥H ≃ ({y : ↥Q // y ≠ 1} × {c : ↥H // φ c = φ 1}) :=
  { toFun := fun k => (φ k, ⟨(σ (φ k))⁻¹ * k, hmem k⟩)
    invFun := fun p => σ p.1 * p.2.1
    left_inv := by
      intro k
      show σ (φ k) * ((σ (φ k))⁻¹ * k) = k
      group
    right_inv := by
      intro p
      apply Prod.ext
      · exact hfirst p
      · apply Subtype.ext
        change (σ (φ (σ p.1 * p.2.1)))⁻¹ * (σ p.1 * p.2.1) = p.2.1
        rw [hfirst p]
        group }
  have hcard : Nat.card ↥H = Nat.card ({y : ↥Q // y ≠ 1} × {c : ↥H // φ c = φ 1}) :=
    Nat.card_congr e
  have hS : Nat.card {y : ↥Q // y ≠ 1} = Nat.card ↥Q - 1 := by
    have h : Fintype.card {y : ↥Q // y ≠ 1} = Fintype.card ↥Q - 1 := by
      have hq := Fintype.card_subtype_compl (fun y : ↥Q => y = 1)
      rw [Fintype.card_subtype_eq (1 : ↥Q)] at hq
      exact hq
    rw [Nat.card_eq_fintype_card, h, Nat.card_eq_fintype_card]
  rw [← hS, hcard, Nat.card_prod]
  exact dvd_mul_right _ _

/-- **From one `H`-class meeting `Q ∖ 1` to transitivity.**  If `H` has exactly one conjugacy
class meeting `Q ∖ 1`, then all elements of `Q ∖ 1` are pairwise `H`-conjugate. -/
private theorem conj_transitive_of_card_classes_eq_one {G : Type} [Group G] [Fintype G]
    {H Q : Subgroup G} (hQH : Q ≤ H)
    (h1 : Nat.card {c : ConjClasses ↥H // ∃ x ∈ c.carrier, (x : G) ∈ Q ∧ x ≠ 1} = 1) :
    ∃ x₀ : G, x₀ ∈ Q ∧ x₀ ≠ 1 ∧
      ∀ y : G, y ∈ Q → y ≠ 1 → ∃ k : G, k ∈ H ∧ k * x₀ * k⁻¹ = y := by
  classical
  obtain ⟨hsub, ⟨c₀, hc₀⟩⟩ := Nat.card_eq_one_iff_unique.mp h1
  obtain ⟨x, -, hxQ, hx1⟩ := hc₀
  refine ⟨(x : G), hxQ, fun h => hx1 (Subtype.ext h), ?_⟩
  intro y hyQ hy1
  let make : (z : G) → z ∈ Q → z ≠ 1 →
      {c : ConjClasses ↥H // ∃ x ∈ c.carrier, (x : G) ∈ Q ∧ x ≠ 1} :=
    fun z hzQ hz1 =>
      ⟨ConjClasses.mk ⟨z, hQH hzQ⟩,
        ⟨⟨z, hQH hzQ⟩, ConjClasses.mem_carrier_mk, hzQ,
          fun hzero => hz1 (Subtype.ext_iff.mp hzero)⟩⟩
  have hxy : make (x : G) hxQ (fun h => hx1 (Subtype.ext h)) = make y hyQ hy1 :=
    Subsingleton.elim _ _
  have hcls : ConjClasses.mk (⟨(x : G), hQH hxQ⟩ : ↥H) = ConjClasses.mk ⟨y, hQH hyQ⟩ := by
    have := congrArg Subtype.val hxy
    simpa [make] using this
  have hconj : IsConj (⟨(x : G), hQH hxQ⟩ : ↥H) ⟨y, hQH hyQ⟩ :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hcls
  obtain ⟨k, hk⟩ := isConj_iff.mp hconj
  refine ⟨(k : G), k.2, ?_⟩
  have := congrArg (fun z : ↥H => (z : G)) hk
  simpa using this

/-! ## The main lemma -/

theorem exists_zeta_ne_orbit {G : Type} [Group G] [Fintype G] (H Q : Subgroup G) [Fintype ↥Q]
    (t : G) (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (hne : Nat.card (Submission.Blueprint.twoPoint H t) ≠ Nat.card Q - 1)
    {κ : ↥Q → ℂ} (hκ : κ ∈ Work.CharCore.Irr ↥Q) (hκ1 : κ ≠ 1) :
    ∃ ζ₂ : ↥Q → ℂ, ζ₂ ∈ Work.CharCore.Irr ↥Q ∧ ζ₂ ≠ 1 ∧
      Work.Induction.indFun Q ζ₂ ≠ Work.Induction.indFun Q κ := by
  classical
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ ζ₂, ζ₂ ∈ Irr Q → ζ₂ ≠ 1 → Ind_Q^G ζ₂ = Ind_Q^G κ`.
  -- Step 1: the image of `ζ ↦ Ind_Q^G ζ` on `Irr Q ∖ 1` is a singleton.
  have himg : ((Work.CharCore.Irr ↥Q).filter (fun ζ => ζ ≠ 1)).image
        (fun ζ => Work.Induction.indFun Q ζ) = {Work.Induction.indFun Q κ} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨Finset.mem_image.mpr ⟨κ, Finset.mem_filter.mpr ⟨hκ, hκ1⟩, rfl⟩, ?_⟩
    intro x hx
    obtain ⟨ζ, hζ, hζx⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_filter] at hζ
    rw [← hζx, hcon ζ hζ.1 hζ.2]
  have hS : Nat.card (↑(((Work.CharCore.Irr ↥Q).filter (fun ζ => ζ ≠ 1)).image
        (fun ζ => Work.Induction.indFun Q ζ)) : Set (G → ℂ)) = 1 := by
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, himg]
    simp
  -- Step 2: `H` has a single class meeting `Q ∖ 1`.
  have hH1 : Nat.card {c : ConjClasses ↥H // ∃ x ∈ c.carrier, (x : G) ∈ Q ∧ x ≠ 1} = 1 := by
    rw [card_H_classes_eq_card_induced H Q t h hz]
    exact hS
  -- Step 3: `H` acts transitively on `Q ∖ 1`.
  obtain ⟨x₀, hx₀Q, hx₀1, htrans⟩ := conj_transitive_of_card_classes_eq_one h.le hH1
  -- Step 4: `|Q| - 1 ∣ |H| = |Q| · |D|`.
  have hdvd : Nat.card Q - 1 ∣ Nat.card H :=
    card_dvd_of_conj_transitive h.normal hx₀Q hx₀1 htrans
  have hHcard : Nat.card H = Nat.card Q * Nat.card (Submission.Blueprint.twoPoint H t) :=
    card_eq_mul_card_twoPoint h
  -- Step 5: cancel the coprime factor `|Q|`, then use `|D| ∣ |Q| - 1`.
  have h1Q : 1 ≤ Nat.card Q := by
    haveI : Nonempty ↥Q := ⟨1⟩
    exact Nat.card_pos
  have hcop : Nat.Coprime (Nat.card Q - 1) (Nat.card Q) := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_self_sub_left h1Q]
    simp
  have hdvdD : Nat.card Q - 1 ∣ Nat.card (Submission.Blueprint.twoPoint H t) :=
    hcop.dvd_of_dvd_mul_left (hHcard ▸ hdvd)
  have hqdvd : Nat.card (Submission.Blueprint.twoPoint H t) ∣ Nat.card Q - 1 :=
    card_twoPoint_dvd h hz
  exact hne (Nat.dvd_antisymm hqdvd hdvdD)

end Work.ZassenhausTwoGroup
