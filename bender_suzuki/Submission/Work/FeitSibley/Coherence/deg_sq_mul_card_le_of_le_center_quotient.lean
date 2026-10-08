import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Coherence.exists_indQH_of_mem_scriptSR_le_Q
import Submission.Work.FeitSibley.Coherence.commutator_S_Q_le_commutator_S_S
import Submission.Work.FeitSibley.Coherence.commutator_Z_Q_le_Q3_of_le_center_quotient
import Submission.Work.FeitSibley.Coherence.le_normalizer_commutator
import Submission.Work.FeitSibley.CharQ.exists_prodChar_of_mem_Irr
import Submission.Work.CharPrelim.ft4_1
import Submission.Work.CohApps.sum_irr_deg_sq_le_ker

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.deg_sq_mul_card_le_of_le_center_quotient`

Peterfalvi II, Appendice XII, step (1) uses the bound

  `ψ(1)² ≤ d² · |Q₁/Z|`,  where  `Z/Q₃ = Z(Q₁/Q₃)`

for a character `ψ ∈ 𝒮(S'Q₃)` (the displayed equation (1-2) of the source, obtained there from
Isaacs 2.30 applied in `Q/S'Q₃`).  In the form needed by `Coherence/step1.lean` this is the
statement proved here: for `χ ∈ 𝒮(S' ⊔ Q₃)` and any subgroup `Z ≤ Q₁` whose image in `Q₁/Q₃` is
central (`[Z,Q₁] ≤ Q₃`),

  `χ(1)² · |Z| ≤ |D|² · |Q₁|`.

## The argument

`χ = Ind_Q^H φ` with `φ ∈ Irr Q` trivial on `R := S' ⊔ Q₃` and `χ(1) = |D|·φ(1)`
(`exists_indQH_of_mem_scriptSR_le_Q`).  So it suffices to show `φ(1)² · |Z| ≤ |Q₁|`, and this is
Isaacs 2.30 (in the counting form of `Work.CharPrelim.ft4_1`) applied in `Q/R`:

* `R ⊴ Q` (both `S'` and `Q₃` are normalised by `Q ≤ H`);
* the images in `Q/R` of `S` and of `Z` are central: `[S,Q] ≤ S' ≤ R` (`S` commutes with `Q₁`
  and `Q = S·Q₁`) and `[Z,Q] ≤ Q₃ ≤ R` (hypothesis, plus `S` centralising `Q₁`), so `φ'` — the
  deflation of `φ` to `Q/R` — has modulus `φ(1)` on every product `s·z` with `s ∈ S`, `z ∈ Z`;
* the `|S|·|Z|` products `s·z` are distinct (`S ⊓ Z ≤ S ⊓ Q₁ = 1`), so comparing
  `∑_{s,z} ‖φ(s z)‖² = |S|·|Z|·φ(1)²` with `∑_{q ∈ Q} ‖φ q‖² = |Q| = |S|·|Q₁|` gives
  `|Z|·φ(1)² ≤ |Q₁|`.

The two group-theoretic inputs (`[S,Q] ≤ S'` and `[Z,Q] ≤ Q₃`) are the separate lemmas
`commutator_S_Q_le_commutator_S_S` and `commutator_Z_Q_le_Q3_of_le_center_quotient`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.FeitSibley.Coherence

/-- **Isaacs 2.30 in `Q`, with a central section of `Q/S'Q₃`.**  Let `φ ∈ Irr Q` be trivial on
`R = S' ⊔ Q₃` and let `Z ≤ Q₁` satisfy `[Z,Q₁] ≤ Q₃`.  Then `φ(1)² · |Z| ≤ |Q₁|`.

The heart of `deg_sq_mul_card_le_of_le_center_quotient`, obtained by counting the `|S|·|Z|`
distinct products `s·z` (`s ∈ S`, `z ∈ Z`), whose images in `Q/R` are central, against
`∑_{q ∈ Q} ‖φ q‖² = |Q| = |S|·|Q₁|`. -/
theorem irrDeg_sq_mul_card_le_card_Q1_of_le_center_quotient {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) (Z Q3 : Subgroup G) (hZQ1 : Z ≤ h.Q1) (hQ3 : Q3 ≤ h.Q1)
    (hQ3n : h.H ≤ Subgroup.normalizer (Q3 : Set G))
    (hZcen : ∀ x : G, x ∈ Z → ∀ y : G, y ∈ h.Q1 → x * y * x⁻¹ * y⁻¹ ∈ Q3)
    {φ : ↥h.Q → ℂ} (hφ : φ ∈ Work.CharCore.Irr ↥h.Q)
    (htriv : ∀ x : ↥h.Q, (x : G) ∈ FSScomm h ⊔ Q3 → φ x = φ 1) :
    (Work.CharCore.irrDeg φ : ℝ) ^ 2 * (Nat.card ↥Z : ℝ) ≤ (Nat.card ↥h.Q1 : ℝ) := by
  classical
  letI : Bracket ↥h.Q ↥h.Q := commutatorElement
  letI : Bracket G G := commutatorElement
  -- `Z ≤ Q` and `Q₃ ≤ Q`
  have hZQ : Z ≤ h.Q := hZQ1.trans h.Q1_le_Q
  have hQ3Q : Q3 ≤ h.Q := hQ3.trans h.Q1_le_Q
  -- **(0)** `S' ≤ S ≤ Q`
  have hS'leS : FSScomm h ≤ h.S := by
    rw [FSScomm]
    exact (Subgroup.commutator_le_sup h.S h.S).trans (le_of_eq (sup_idem h.S))
  -- **(1)** `R = S' ⊔ Q₃` is normal in `Q`
  have hQnS : h.Q ≤ Subgroup.normalizer (h.S : Set G) := h.Q_le_H.trans h.S_normal_in_H
  have hQnS' : h.Q ≤ Subgroup.normalizer (FSScomm h : Set G) :=
    le_normalizer_commutator hQnS hQnS
  have hQnQ3 : h.Q ≤ Subgroup.normalizer (Q3 : Set G) := h.Q_le_H.trans hQ3n
  haveI hRQN : ((FSScomm h ⊔ Q3).subgroupOf h.Q).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((le_inf hQnS' hQnQ3).trans (Subgroup.inf_normalizer_le_normalizer_sup (FSScomm h) Q3))
  -- **(2)** deflate `φ` to `Q/R`
  haveI hQfin : Fintype (↥h.Q ⧸ (FSScomm h ⊔ Q3).subgroupOf h.Q) := QuotientGroup.fintype _
  obtain ⟨φ', hφ', hφ'infl⟩ :=
    Work.CohApps.exists_irr_quotient_of_le_ker ((FSScomm h ⊔ Q3).subgroupOf h.Q) hφ
      (fun x hx => htriv x (Subgroup.mem_subgroupOf.mp hx))
  have hφ'deg : Work.CharCore.irrDeg φ' = Work.CharCore.irrDeg φ := by
    rw [← Work.CohApps.irrDeg_inflateFun ((FSScomm h ⊔ Q3).subgroupOf h.Q) hφ', hφ'infl]
  have hφ'infl' : ∀ w : ↥h.Q,
      φ w = φ' (QuotientGroup.mk' ((FSScomm h ⊔ Q3).subgroupOf h.Q) w) :=
    fun w => by rw [← hφ'infl]; rfl
  -- **(3)** the images of `S` and of `Z` in `Q/R` are central
  have hScent : ∀ x : ↥h.Q, x ∈ h.S.subgroupOf h.Q → ∀ y : ↥h.Q,
      QuotientGroup.mk' ((FSScomm h ⊔ Q3).subgroupOf h.Q) x
          * QuotientGroup.mk' ((FSScomm h ⊔ Q3).subgroupOf h.Q) y
        = QuotientGroup.mk' ((FSScomm h ⊔ Q3).subgroupOf h.Q) y
          * QuotientGroup.mk' ((FSScomm h ⊔ Q3).subgroupOf h.Q) x := by
    intro x hx y
    have hxy : ⁅x, y⁆ ∈ (FSScomm h ⊔ Q3).subgroupOf h.Q := by
      rw [Subgroup.mem_subgroupOf]
      show ⁅(x : G), (y : G)⁆ ∈ FSScomm h ⊔ Q3
      exact Subgroup.mem_sup_left (commutator_S_Q_le_commutator_S_S h
        (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hx) y.2))
    have hk : QuotientGroup.mk' ((FSScomm h ⊔ Q3).subgroupOf h.Q) ⁅x, y⁆ = 1 :=
      (QuotientGroup.eq_one_iff (N := (FSScomm h ⊔ Q3).subgroupOf h.Q) ⁅x, y⁆).mpr hxy
    rw [map_commutatorElement] at hk
    exact commutatorElement_eq_one_iff_mul_comm.mp hk
  have hZcent : ∀ z : ↥h.Q, z ∈ Z.subgroupOf h.Q → ∀ y : ↥h.Q,
      QuotientGroup.mk' ((FSScomm h ⊔ Q3).subgroupOf h.Q) z
          * QuotientGroup.mk' ((FSScomm h ⊔ Q3).subgroupOf h.Q) y
        = QuotientGroup.mk' ((FSScomm h ⊔ Q3).subgroupOf h.Q) y
          * QuotientGroup.mk' ((FSScomm h ⊔ Q3).subgroupOf h.Q) z := by
    intro z hz y
    have hzy : ⁅z, y⁆ ∈ (FSScomm h ⊔ Q3).subgroupOf h.Q := by
      rw [Subgroup.mem_subgroupOf]
      show ⁅(z : G), (y : G)⁆ ∈ FSScomm h ⊔ Q3
      exact Subgroup.mem_sup_right
        (commutator_Z_Q_le_Q3_of_le_center_quotient h Z Q3 hZQ1 hQ3n hZcen
          (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hz) y.2))
    have hk : QuotientGroup.mk' ((FSScomm h ⊔ Q3).subgroupOf h.Q) ⁅z, y⁆ = 1 :=
      (QuotientGroup.eq_one_iff (N := (FSScomm h ⊔ Q3).subgroupOf h.Q) ⁅z, y⁆).mpr hzy
    rw [map_commutatorElement] at hk
    exact commutatorElement_eq_one_iff_mul_comm.mp hk
  -- **(4)** `‖φ (s · z)‖ = φ(1)` for all `s ∈ S`, `z ∈ Z`
  have hval : ∀ (x : ↥h.Q), x ∈ h.S.subgroupOf h.Q → ∀ (z : ↥h.Q),
      z ∈ Z.subgroupOf h.Q → ‖φ (x * z)‖ = (Work.CharCore.irrDeg φ : ℝ) := by
    intro x hx z hz
    have hcentral : QuotientGroup.mk' ((FSScomm h ⊔ Q3).subgroupOf h.Q) (x * z) ∈
        Subgroup.center (↥h.Q ⧸ (FSScomm h ⊔ Q3).subgroupOf h.Q) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective ((FSScomm h ⊔ Q3).subgroupOf h.Q) y
      rw [map_mul]
      have h1 : Commute (QuotientGroup.mk' ((FSScomm h ⊔ Q3).subgroupOf h.Q) x) y₀ :=
        hScent x hx y₀
      have h2 : Commute (QuotientGroup.mk' ((FSScomm h ⊔ Q3).subgroupOf h.Q) z) y₀ :=
        hZcent z hz y₀
      exact (h1.mul_left h2).eq.symm
    rw [hφ'infl' (x * z),
      Work.CharPrelim.norm_char_eq_irrDeg_of_mem_center hφ' hcentral, hφ'deg]
  -- **(5)** `S ⊓ Z = 1`, so the products `s · z` are `|S| · |Z|` distinct elements of `Q`
  have hbot : h.S.subgroupOf h.Q ⊓ Z.subgroupOf h.Q = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxS, hxZ⟩ := Subgroup.mem_inf.mp hx
    have h1 : (x : G) ∈ h.S ⊓ h.Q1 :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hxS,
        hZQ1 (Subgroup.mem_subgroupOf.mp hxZ)⟩
    rw [h.S_inf_Q1] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp h1))
  have hinj : ∀ p q : ↥(h.S.subgroupOf h.Q) × ↥(Z.subgroupOf h.Q),
      ((p.1 : ↥h.Q) * (p.2 : ↥h.Q)) = ((q.1 : ↥h.Q) * (q.2 : ↥h.Q)) → p = q := by
    rintro ⟨t1, z1⟩ ⟨t2, z2⟩ heq
    have h1 : (t2 : ↥h.Q)⁻¹ * (t1 : ↥h.Q)
        = (z2 : ↥h.Q) * (z1 : ↥h.Q)⁻¹ := by
      calc (t2 : ↥h.Q)⁻¹ * (t1 : ↥h.Q)
          = (t2 : ↥h.Q)⁻¹ * (t1 : ↥h.Q) * ((z1 : ↥h.Q) * (z1 : ↥h.Q)⁻¹) := by group
        _ = (t2 : ↥h.Q)⁻¹ * ((t1 : ↥h.Q) * (z1 : ↥h.Q)) * (z1 : ↥h.Q)⁻¹ := by group
        _ = (t2 : ↥h.Q)⁻¹ * ((t2 : ↥h.Q) * (z2 : ↥h.Q)) * (z1 : ↥h.Q)⁻¹ := by rw [heq]
        _ = (z2 : ↥h.Q) * (z1 : ↥h.Q)⁻¹ := by group
    have hmem : (t2 : ↥h.Q)⁻¹ * (t1 : ↥h.Q)
        ∈ h.S.subgroupOf h.Q ⊓ Z.subgroupOf h.Q := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ t2.2) t1.2, ?_⟩
      show (((t2 : ↥h.Q)⁻¹ * (t1 : ↥h.Q) : ↥h.Q) : G) ∈ Z
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.mem_subgroupOf.mp z2.2)
        (Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.mp z1.2))
    rw [hbot] at hmem
    have ht : (t2 : ↥h.Q)⁻¹ * (t1 : ↥h.Q) = 1 := Subgroup.mem_bot.mp hmem
    have ht12 : t1 = t2 := by
      apply Subtype.ext
      simpa using congrArg (fun w => (t2 : ↥h.Q) * w) ht
    have ht12' : (t1 : ↥h.Q) = (t2 : ↥h.Q) :=
      congrArg (fun w : ↥(h.S.subgroupOf h.Q) => (w : ↥h.Q)) ht12
    have hz12 : z1 = z2 := by
      apply Subtype.ext
      have h2 : (t1 : ↥h.Q) * (z1 : ↥h.Q) = (t1 : ↥h.Q) * (z2 : ↥h.Q) := by
        have hh := heq
        rw [← ht12'] at hh
        exact hh
      exact mul_left_cancel h2
    exact Prod.ext ht12 hz12
  -- **(6)** the counting
  have hle' : (∑ g ∈ ((Finset.univ : Finset ↥(h.S.subgroupOf h.Q)).product
        (Finset.univ : Finset ↥(Z.subgroupOf h.Q))).image
        (fun p => (p.1 : ↥h.Q) * (p.2 : ↥h.Q)), ‖φ g‖ ^ 2) ≤ (Nat.card ↥h.Q : ℝ) := by
    have hsub : (∑ g ∈ ((Finset.univ : Finset ↥(h.S.subgroupOf h.Q)).product
          (Finset.univ : Finset ↥(Z.subgroupOf h.Q))).image
          (fun p => (p.1 : ↥h.Q) * (p.2 : ↥h.Q)), ‖φ g‖ ^ 2)
        ≤ ∑ g : ↥h.Q, ‖φ g‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun g _ _ => by positivity)
    rwa [Work.CharPrelim.sum_normSq_eq_card hφ] at hsub
  have hsum : (∑ g ∈ ((Finset.univ : Finset ↥(h.S.subgroupOf h.Q)).product
        (Finset.univ : Finset ↥(Z.subgroupOf h.Q))).image
        (fun p => (p.1 : ↥h.Q) * (p.2 : ↥h.Q)), ‖φ g‖ ^ 2)
      = (Fintype.card ↥(h.S.subgroupOf h.Q) : ℝ)
        * ((Fintype.card ↥(Z.subgroupOf h.Q) : ℝ)
          * (Work.CharCore.irrDeg φ : ℝ) ^ 2) := by
    rw [Finset.sum_image (fun p _ q _ hpq => hinj p q hpq)]
    rw [Finset.product_eq_sprod, Finset.sum_product]
    have hinner : ∀ x : ↥(h.S.subgroupOf h.Q),
        (∑ y ∈ (Finset.univ : Finset ↥(Z.subgroupOf h.Q)),
            ‖φ ((x : ↥h.Q) * (y : ↥h.Q))‖ ^ 2)
          = (Fintype.card ↥(Z.subgroupOf h.Q) : ℝ)
            * (Work.CharCore.irrDeg φ : ℝ) ^ 2 := by
      intro x
      rw [Finset.sum_congr rfl (fun y _ => by rw [hval x x.2 y y.2])]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun x _ => hinner x)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcS : (Fintype.card ↥(h.S.subgroupOf h.Q) : ℝ) = (Nat.card h.S : ℝ) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.S_le_Q).toEquiv,
      ← Nat.card_eq_fintype_card]
  have hcZ : (Fintype.card ↥(Z.subgroupOf h.Q) : ℝ) = (Nat.card ↥Z : ℝ) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv,
      ← Nat.card_eq_fintype_card]
  rw [hcS, hcZ] at hsum
  -- **(7)** `|Q| = |S| · |Q₁|` and conclusion
  have hQcard : (Nat.card h.Q : ℝ) = (Nat.card h.S : ℝ) * (Nat.card h.Q1 : ℝ) := by
    have hsup := Work.PGroup.card_sup_mul_card_inf h.S h.Q1 h.commute
    rw [h.S_sup_Q1, h.S_inf_Q1] at hsup
    have hnat : Nat.card ↥h.Q = Nat.card h.S * Nat.card h.Q1 := by simpa using hsup
    rw [hnat]
    push_cast
    ring
  have hSpos : (0 : ℝ) < (Nat.card h.S : ℝ) := by
    haveI : Nonempty ↥h.S := ⟨1, h.S.one_mem⟩
    exact_mod_cast Nat.card_pos
  have key : (Nat.card h.S : ℝ) * ((Nat.card ↥Z : ℝ)
        * (Work.CharCore.irrDeg φ : ℝ) ^ 2) ≤ (Nat.card h.S : ℝ) * (Nat.card ↥h.Q1 : ℝ) := by
    rw [← hsum, ← hQcard]
    exact hle'
  have hdiv : (Nat.card ↥Z : ℝ) * (Work.CharCore.irrDeg φ : ℝ) ^ 2
      ≤ (Nat.card ↥h.Q1 : ℝ) := le_of_mul_le_mul_left key hSpos
  nlinarith [hdiv]

/-- **The degree bound of Peterfalvi II, Appendice XII, step (1).**  Let `Q₃ ≤ Q₁` be
normalised by `H`, let `Z ≤ Q₁` satisfy `[Z,Q₁] ≤ Q₃` (i.e. `Z/Q₃ ≤ Z(Q₁/Q₃)`), and let
`χ ∈ 𝒮(S'Q₃)`.  Then `χ(1)² · |Z| ≤ |D|² · |Q₁|`.

This is the bound `ψ(1)² ≤ d²|Q₁/Z|` used in step (1) of the source (via Isaacs 2.30 in
`Q/S'Q₃`): write `χ = Ind_Q^H φ` with `φ ∈ Irr Q` trivial on `S'Q₃` and `χ(1) = |D|·φ(1)`, and
apply `irrDeg_sq_mul_card_le_card_Q1_of_le_center_quotient`. -/
theorem deg_sq_mul_card_le_of_le_center_quotient {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) (Z Q3 : Subgroup G) (hZQ1 : Z ≤ h.Q1) (hQ3 : Q3 ≤ h.Q1)
    (hQ3n : h.H ≤ Subgroup.normalizer (Q3 : Set G))
    (hZcen : ∀ x : G, x ∈ Z → ∀ y : G, y ∈ h.Q1 → x * y * x⁻¹ * y⁻¹ ∈ Q3)
    {χ : ↥h.H → ℂ} (hχ : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Q3)) :
    (Work.CharCore.irrDeg χ : ℝ)^2 * (Nat.card ↥Z : ℝ)
      ≤ (Nat.card h.D : ℝ)^2 * (Nat.card ↥h.Q1 : ℝ) := by
  classical
  have hR : FSScomm h ⊔ Q3 ≤ h.Q := by
    rw [FSScomm]
    refine sup_le ?_ (hQ3.trans h.Q1_le_Q)
    exact ((Subgroup.commutator_le_sup h.S h.S).trans (le_of_eq (sup_idem h.S))).trans h.S_le_Q
  obtain ⟨φ, hφ, htriv, -, hdeg⟩ :=
    exists_indQH_of_mem_scriptSR_le_Q h hR hχ
  have hmain := irrDeg_sq_mul_card_le_card_Q1_of_le_center_quotient h Z Q3 hZQ1 hQ3 hQ3n hZcen
    hφ htriv
  rw [hdeg]
  calc ((Nat.card h.D : ℝ) * (Work.CharCore.irrDeg φ : ℝ)) ^ 2 * (Nat.card ↥Z : ℝ)
      = (Nat.card h.D : ℝ) ^ 2
        * ((Work.CharCore.irrDeg φ : ℝ) ^ 2 * (Nat.card ↥Z : ℝ)) := by ring
    _ ≤ (Nat.card h.D : ℝ) ^ 2 * (Nat.card ↥h.Q1 : ℝ) :=
        mul_le_mul_of_nonneg_left hmain (sq_nonneg _)

end Work.FeitSibley.Coherence
