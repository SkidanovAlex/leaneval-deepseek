import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.CharQ.scriptS_eq_image
import Submission.Work.CharPrelim.ft4_1
import Submission.Work.FeitSibley.GroupTheory.S_Q1
import Submission.Work.FeitSibley.Coherence.deg_sq_le_of_mem_scriptSR

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.deg_sq_le_of_mem_scriptSR_center`

The bound `deg_sq_le_of_mem_scriptSR`, with the centre `Z(Q₁)` of `Q₁` in place of
`Z = [Q₁,Q₁] ⊓ Z(Q₁)`.

Since `FSZ h ≤ h.centerQ1`, this is the *stronger* form of the estimate: the `Z` that the
counting argument actually needs is `Z(Q₁)`.

## The mathematics

The proof is Isaacs 2.30 for a central section, run with `Z = Z(Q₁)`.  Two facts about `Z(Q₁)`
replace the two facts that made `Z = [Q₁,Q₁] ⊓ Z(Q₁)` work in
`irrDeg_sq_mul_card_le_card_Q`:

* `Z(Q₁) ≤ Z(Q)`: an element of `Z(Q₁)` centralises `Q₁` by definition and `S` because `S` and
  `Q₁` commute elementwise (`FSData.commute`), while `Q = S · Q₁`;
* `Z(Q₁) ⊓ T = 1` for `T ≤ S`: `Z(Q₁) ≤ Q₁` and `S ⊓ Q₁ = 1`.

Everything else — `[Q,T] ≤ R`, `R ⊴ Q`, the descent of `φ` to `Q/R`, the centrality of the
images of `T` and of `Z` in `Q/R`, `‖φ (t · z)‖ = φ(1)`, and the final count of the
`|T| · |Z(Q₁)|` distinct products — is identical.
-/

namespace Work.FeitSibley.Coherence

set_option linter.style.haveILetI false

/-- **`Z(Q₁)` is central in `Q`.**  An element `z` of `Z(Q₁)` centralises `Q₁` by definition,
and centralises `S` because `S` and `Q₁` commute elementwise; since `Q = S · Q₁`, it centralises
all of `Q`. -/
theorem centerQ1_subgroupOf_le_center {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) :
    (h.centerQ1).subgroupOf h.Q ≤ Subgroup.center ↥h.Q := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨hzQ1, hzc⟩ := h.mem_centerQ1.mp (Subgroup.mem_subgroupOf.mp hz)
  obtain ⟨s, hs, q1, hq1, hsq1⟩ := h.mem_Q_decomp y.2
  apply Subtype.ext
  show (y : G) * (z : G) = (z : G) * (y : G)
  rw [hsq1]
  have h1 : Commute s (z : G) := h.commute s hs (z : G) hzQ1
  have h2 : Commute q1 (z : G) := (hzc q1 hq1).symm
  exact (Commute.mul_left h1 h2).eq

/-- **`Z(Q₁)` meets `T ≤ S` trivially**: `Z(Q₁) ≤ Q₁` and `S ⊓ Q₁ = 1`. -/
theorem centerQ1_inf_T_subgroupOf_eq_bot {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {T : Subgroup G} (hT : T ≤ h.S) :
    (h.centerQ1).subgroupOf h.Q ⊓ T.subgroupOf h.Q = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxZ, hxT⟩ := Subgroup.mem_inf.mp hx
  have h1 : (x : G) ∈ h.S ⊓ h.Q1 :=
    Subgroup.mem_inf.mpr
      ⟨hT (Subgroup.mem_subgroupOf.mp hxT),
       h.centerQ1_le_Q1 (Subgroup.mem_subgroupOf.mp hxZ)⟩
  rw [h.S_inf_Q1] at h1
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp h1))

/-- **Isaacs 2.30 with the centre of `Q₁` as central section.**  Let `φ ∈ Irr Q` be trivial on
`R ≤ Q` and let `T ≤ S` satisfy `⁅S,T⁆ ≤ R`.  Then `φ(1)² · |T| · |Z(Q₁)| ≤ |Q|`.

The image of `T` in `Q/R` is central (`[Q,T] ≤ R`: `Q = S·Q₁`, `[S,T] ≤ R` by hypothesis and
`Q₁` commutes with `T ≤ S`), and so is the image of `Z(Q₁)` (`Z(Q₁) ≤ Z(Q)`), and the two
intersect trivially (`Z(Q₁) ⊓ S ≤ Q₁ ⊓ S = 1`).  Passing to `Q/R`, where `φ` becomes an
irreducible character of degree `φ(1)`, its modulus is `φ(1)` on every central element
(`Work.CharPrelim.norm_char_eq_irrDeg_of_mem_center`), hence on all `|T|·|Z(Q₁)|` products
`t·z`; comparing with `∑_{q ∈ Q} ‖φ q‖² = |Q|` gives the claim. -/
theorem irrDeg_sq_mul_card_le_card_Q_center {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G)
    (R T : Subgroup G) (hT : T ≤ h.S) (hRT : R ≤ T) (hcent : ⁅h.S, T⁆ ≤ R)
    {φ : ↥h.Q → ℂ} (hφ : φ ∈ Work.CharCore.Irr ↥h.Q)
    (htriv : ∀ x : ↥h.Q, (x : G) ∈ R → φ x = φ 1) :
    (Work.CharCore.irrDeg φ : ℝ) ^ 2 *
      ((Nat.card T : ℝ) * (Nat.card h.centerQ1 : ℝ)) ≤ (Nat.card h.Q : ℝ) := by
  classical
  -- elementwise commutators inside `Q` and inside `G`
  letI : Bracket ↥h.Q ↥h.Q := commutatorElement
  letI : Bracket G G := commutatorElement
  -- `Z(Q₁) ≤ Q₁ ≤ Q`
  have hZQ1 : h.centerQ1 ≤ h.Q1 := h.centerQ1_le_Q1
  have hZQ : h.centerQ1 ≤ h.Q := hZQ1.trans h.Q1_le_Q
  -- **(1)** `[Q,T] ≤ R`
  have hQT : ⁅h.Q, T⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro q hq t ht
    obtain ⟨s, hs, q1, hq1, hsq1⟩ := h.mem_Q_decomp hq
    have h1 : ⁅q1, t⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (h.commute t (hT ht) q1 hq1).symm
    rw [hsq1, commutatorElement_mul_left_eq_conj_mul, h1, mul_one]
    have h2 := hcent (Subgroup.commutator_mem_commutator hs ht)
    convert h2 using 1
    group
  have hTQ : ⁅T, h.Q⁆ ≤ R := by rw [Subgroup.commutator_comm]; exact hQT
  -- **(2)** `R ⊴ Q`
  have hQR : ⁅h.Q, R⁆ ≤ R := (Subgroup.commutator_mono_right hRT).trans hQT
  haveI hRgN : (R.subgroupOf h.Q).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (by
      rw [Subgroup.le_normalizer_iff_commutator_le_left, Subgroup.commutator_comm]
      exact hQR)
  -- **(3)** `Z(Q₁) ≤ Z(Q)`
  have hZcen : (h.centerQ1).subgroupOf h.Q ≤ Subgroup.center ↥h.Q :=
    centerQ1_subgroupOf_le_center h
  -- **(4)** descend `φ` to `Q/R`
  haveI hQfin : Fintype (↥h.Q ⧸ R.subgroupOf h.Q) := QuotientGroup.fintype _
  obtain ⟨φ', hφ', hφ'infl⟩ :=
    Work.CohApps.exists_irr_quotient_of_le_ker (R.subgroupOf h.Q) hφ
      (fun x hx => htriv x (Subgroup.mem_subgroupOf.mp hx))
  have hφ'deg : Work.CharCore.irrDeg φ' = Work.CharCore.irrDeg φ := by
    rw [← Work.CohApps.irrDeg_inflateFun (R.subgroupOf h.Q) hφ', hφ'infl]
  have hφ'infl' : ∀ w : ↥h.Q, φ w = φ' (QuotientGroup.mk' (R.subgroupOf h.Q) w) :=
    fun w => by rw [← hφ'infl]; rfl
  -- **(5)** `T` and `Z(Q₁)` have central image in `Q/R`
  have hTcent : ∀ x : ↥h.Q, x ∈ T.subgroupOf h.Q → ∀ y : ↥h.Q,
      QuotientGroup.mk' (R.subgroupOf h.Q) x * QuotientGroup.mk' (R.subgroupOf h.Q) y
        = QuotientGroup.mk' (R.subgroupOf h.Q) y * QuotientGroup.mk' (R.subgroupOf h.Q) x := by
    intro x hx y
    have hxy : ⁅x, y⁆ ∈ R.subgroupOf h.Q := by
      rw [Subgroup.mem_subgroupOf]
      show ⁅(x : G), (y : G)⁆ ∈ R
      exact hTQ (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hx) y.2)
    have hk : QuotientGroup.mk' (R.subgroupOf h.Q) ⁅x, y⁆ = 1 :=
      (QuotientGroup.eq_one_iff (N := R.subgroupOf h.Q) ⁅x, y⁆).mpr hxy
    rw [map_commutatorElement] at hk
    exact commutatorElement_eq_one_iff_mul_comm.mp hk
  have hZcent : ∀ z : ↥h.Q, z ∈ (h.centerQ1).subgroupOf h.Q → ∀ y : ↥h.Q,
      QuotientGroup.mk' (R.subgroupOf h.Q) z * QuotientGroup.mk' (R.subgroupOf h.Q) y
        = QuotientGroup.mk' (R.subgroupOf h.Q) y * QuotientGroup.mk' (R.subgroupOf h.Q) z := by
    intro z hz y
    have hzy : y * z = z * y := Subgroup.mem_center_iff.mp (hZcen hz) y
    calc QuotientGroup.mk' (R.subgroupOf h.Q) z * QuotientGroup.mk' (R.subgroupOf h.Q) y
        = QuotientGroup.mk' (R.subgroupOf h.Q) (z * y) := (map_mul _ z y).symm
      _ = QuotientGroup.mk' (R.subgroupOf h.Q) (y * z) := by rw [← hzy]
      _ = QuotientGroup.mk' (R.subgroupOf h.Q) y * QuotientGroup.mk' (R.subgroupOf h.Q) z :=
            map_mul _ y z
  -- **(6)** `‖φ (t · z)‖ = φ(1)` for all `t ∈ T`, `z ∈ Z(Q₁)`
  have hval : ∀ (x : ↥h.Q), x ∈ T.subgroupOf h.Q → ∀ (z : ↥h.Q),
      z ∈ (h.centerQ1).subgroupOf h.Q → ‖φ (x * z)‖ = (Work.CharCore.irrDeg φ : ℝ) := by
    intro x hx z hz
    have hcentral : QuotientGroup.mk' (R.subgroupOf h.Q) (x * z) ∈
        Subgroup.center (↥h.Q ⧸ R.subgroupOf h.Q) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf h.Q) y
      rw [map_mul]
      have h1 : Commute (QuotientGroup.mk' (R.subgroupOf h.Q) x) y₀ := hTcent x hx y₀
      have h2 : Commute (QuotientGroup.mk' (R.subgroupOf h.Q) z) y₀ := hZcent z hz y₀
      exact (h1.mul_left h2).eq.symm
    rw [hφ'infl' (x * z),
      Work.CharPrelim.norm_char_eq_irrDeg_of_mem_center hφ' hcentral, hφ'deg]
  -- **(7)** `T ⊓ Z(Q₁) = 1`, so the products `t · z` are `|T| · |Z(Q₁)|` distinct elements of `Q`
  have hbot : (h.centerQ1).subgroupOf h.Q ⊓ T.subgroupOf h.Q = ⊥ :=
    centerQ1_inf_T_subgroupOf_eq_bot h hT
  have hinj : ∀ p q : ↥(T.subgroupOf h.Q) × ↥((h.centerQ1).subgroupOf h.Q),
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
        ∈ T.subgroupOf h.Q ⊓ (h.centerQ1).subgroupOf h.Q := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ t2.2) t1.2, ?_⟩
      show (((t2 : ↥h.Q)⁻¹ * (t1 : ↥h.Q) : ↥h.Q) : G) ∈ h.centerQ1
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.mem_subgroupOf.mp z2.2)
        (Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.mp z1.2))
    rw [inf_comm, hbot] at hmem
    have ht : (t2 : ↥h.Q)⁻¹ * (t1 : ↥h.Q) = 1 := Subgroup.mem_bot.mp hmem
    have ht12 : t1 = t2 := by
      apply Subtype.ext
      simpa using congrArg (fun w => (t2 : ↥h.Q) * w) ht
    have ht12' : (t1 : ↥h.Q) = (t2 : ↥h.Q) :=
      congrArg (fun w : ↥(T.subgroupOf h.Q) => (w : ↥h.Q)) ht12
    have hz12 : z1 = z2 := by
      apply Subtype.ext
      have h2 : (t1 : ↥h.Q) * (z1 : ↥h.Q) = (t1 : ↥h.Q) * (z2 : ↥h.Q) := by
        have hh := heq
        rw [← ht12'] at hh
        exact hh
      exact mul_left_cancel h2
    exact Prod.ext ht12 hz12
  -- **(8)** the counting
  have hle' : (∑ g ∈ ((Finset.univ : Finset ↥(T.subgroupOf h.Q)).product
        (Finset.univ : Finset ↥((h.centerQ1).subgroupOf h.Q))).image
        (fun p => (p.1 : ↥h.Q) * (p.2 : ↥h.Q)), ‖φ g‖ ^ 2)
      ≤ ∑ g : ↥h.Q, ‖φ g‖ ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun g _ _ => by positivity)
  rw [Work.CharPrelim.sum_normSq_eq_card hφ] at hle'
  have hsum : (∑ g ∈ ((Finset.univ : Finset ↥(T.subgroupOf h.Q)).product
        (Finset.univ : Finset ↥((h.centerQ1).subgroupOf h.Q))).image
        (fun p => (p.1 : ↥h.Q) * (p.2 : ↥h.Q)), ‖φ g‖ ^ 2)
      = (Fintype.card ↥(T.subgroupOf h.Q) : ℝ) * (Fintype.card ↥((h.centerQ1).subgroupOf h.Q) : ℝ)
        * (Work.CharCore.irrDeg φ : ℝ) ^ 2 := by
    rw [Finset.sum_image (fun p _ q _ hpq => hinj p q hpq)]
    rw [Finset.product_eq_sprod, Finset.sum_product]
    have hinner : ∀ x : ↥(T.subgroupOf h.Q),
        (∑ y ∈ (Finset.univ : Finset ↥((h.centerQ1).subgroupOf h.Q)),
            ‖φ ((x : ↥h.Q) * (y : ↥h.Q))‖ ^ 2)
          = (Fintype.card ↥((h.centerQ1).subgroupOf h.Q) : ℝ)
            * (Work.CharCore.irrDeg φ : ℝ) ^ 2 := by
      intro x
      rw [Finset.sum_congr rfl (fun y _ => by rw [hval x x.2 y y.2])]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun x _ => hinner x)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hcT : (Fintype.card ↥(T.subgroupOf h.Q) : ℝ) = (Nat.card T : ℝ) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hT.trans h.S_le_Q)).toEquiv,
      ← Nat.card_eq_fintype_card]
  have hcZ : (Fintype.card ↥((h.centerQ1).subgroupOf h.Q) : ℝ) = (Nat.card h.centerQ1 : ℝ) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv,
      ← Nat.card_eq_fintype_card]
  rw [hcT, hcZ] at hsum
  nlinarith [hsum, hle']

/-- **The degree bound with the centre of `Q₁`.**  For `χ ∈ 𝒮(R)` and `T ≤ S` with
`⁅S,T⁆ ≤ R`, one has `χ(1)² ≤ |D|² · [S : T] · |Q₁| / |Z(Q₁)|`.

This is `deg_sq_le_of_mem_scriptSR` with the central section `Z(Q₁)` in place of
`[Q₁,Q₁] ⊓ Z(Q₁)`; the extra strength comes from `irrDeg_sq_mul_card_le_card_Q_center`. -/
theorem deg_sq_le_of_mem_scriptSR_center {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (R T : Subgroup G) (hR : R ≤ h.S) (hT : T ≤ h.S) (hRT : R ≤ T) (hcent : ⁅h.S, T⁆ ≤ R)
    {χ : ↥h.H → ℂ} (hχ : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 R) :
    ((Work.CharCore.irrDeg χ : ℝ)) ^ 2 ≤ (Nat.card h.D : ℝ) ^ 2 *
      (((T.subgroupOf h.S).index : ℕ) : ℝ) *
      ((Nat.card h.Q1 : ℝ) / (Nat.card h.centerQ1 : ℝ)) := by
  classical
  obtain ⟨φ, hφ, htriv, hχeq, hdeg⟩ := exists_indQH_of_mem_scriptSR h hR hχ
  have hcrux := irrDeg_sq_mul_card_le_card_Q_center h R T hT hRT hcent hφ htriv
  -- `|Q| = |S| · |Q₁|`
  have hQcard : (Nat.card h.Q : ℝ) = (Nat.card h.S : ℝ) * (Nat.card h.Q1 : ℝ) := by
    have hsup := Work.PGroup.card_sup_mul_card_inf h.S h.Q1 h.commute
    rw [h.S_sup_Q1, h.S_inf_Q1] at hsup
    have hnat : Nat.card ↥h.Q = Nat.card h.S * Nat.card h.Q1 := by simpa using hsup
    rw [hnat]
    push_cast
    ring
  -- `|S| = [S : T] · |T|`
  have hSsplit : (Nat.card h.S : ℝ) = (((T.subgroupOf h.S).index : ℕ) : ℝ) * (Nat.card T : ℝ) := by
    have h1 : Nat.card ↥(T.subgroupOf h.S) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv
    have h2 : Nat.card h.S = Nat.card T * (T.subgroupOf h.S).index := by
      rw [← h1]
      exact (Subgroup.card_mul_index (T.subgroupOf h.S)).symm
    rw [h2]
    push_cast
    ring
  have hTpos : (0 : ℝ) < (Nat.card T : ℝ) := by
    haveI : Nonempty ↥T := ⟨1, T.one_mem⟩
    exact_mod_cast Nat.card_pos
  have hZpos : (0 : ℝ) < (Nat.card h.centerQ1 : ℝ) := by
    haveI : Nonempty ↥h.centerQ1 := ⟨1, h.centerQ1.one_mem⟩
    exact_mod_cast Nat.card_pos
  -- divide the bound on `φ` by `|Z(Q₁)|`
  have hφbound : (Work.CharCore.irrDeg φ : ℝ) ^ 2 ≤
      (((T.subgroupOf h.S).index : ℕ) : ℝ) * (Nat.card h.Q1 : ℝ)
        / (Nat.card h.centerQ1 : ℝ) := by
    rw [le_div_iff₀ hZpos]
    nlinarith [hcrux, hQcard, hSsplit, hTpos]
  rw [hdeg]
  have hmul := mul_le_mul_of_nonneg_left hφbound (sq_nonneg (Nat.card h.D : ℝ))
  calc ((Nat.card h.D : ℝ) * (Work.CharCore.irrDeg φ : ℝ)) ^ 2
      = (Nat.card h.D : ℝ) ^ 2 * (Work.CharCore.irrDeg φ : ℝ) ^ 2 := by ring
    _ ≤ (Nat.card h.D : ℝ) ^ 2 * ((((T.subgroupOf h.S).index : ℕ) : ℝ)
          * (Nat.card h.Q1 : ℝ) / (Nat.card h.centerQ1 : ℝ)) := hmul
    _ = (Nat.card h.D : ℝ) ^ 2 * (((T.subgroupOf h.S).index : ℕ) : ℝ)
          * ((Nat.card h.Q1 : ℝ) / (Nat.card h.centerQ1 : ℝ)) := by
        rw [div_eq_mul_inv]
        ring

end Work.FeitSibley.Coherence
