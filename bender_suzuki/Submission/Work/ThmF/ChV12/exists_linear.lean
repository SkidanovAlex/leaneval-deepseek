import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.exists_linear` — Peterfalvi II, Ch. VI §1, p. 258

In the split rank-one situation `H = Q ⋊ D` with `D = H ⊓ H^t = twoPoint H t` and `t` an
involution outside `H`, if `G` is *not* a Zassenhaus group on `G ⧸ H`, then `H` has a linear
character `λ ≠ 1_H` with `Q ⊆ ker λ`.

The paper's argument reads: `H/QK ≅ V = C_D(t) ≠ 1` is solvable, so it has a nontrivial linear
character, which pulls back to `H` and is trivial on `QK ⊇ Q`.  The two mathematical inputs are

* **`D ≠ 1`** (in particular `V = C_D(t) ≠ 1`) comes from the Zassenhaus property: if
  `D = H ⊓ H^t = 1` then every element of `G` fixing two distinct points of `G ⧸ H` is trivial
  (the two-point stabiliser of a pair of distinct points is a conjugate of `D`, by
  2-transitivity), so the pointwise stabiliser of three points is trivial and `G` *is*
  Zassenhaus.  Hence `¬ IsZassenhaus H` forces `D ≠ 1`
  (`twoPoint_ne_bot_of_not_isZassenhaus`).
* **solvability** of `D`: `D` has odd order (strong embeddedness of `H`, `t ∉ H`), so
  Feit–Thompson applies.  The quotient `H ⧸ Q` is a quotient of `D` (the map `d ↦ dQ` is
  surjective because `H = D·Q`), hence nontrivial solvable; a nontrivial finite solvable group
  has a nontrivial homomorphism into `ℂˣ` (`exists_monoidHom_units_ne_one`).

Composing that homomorphism with `H →* H ⧸ Q` and applying
`Work.CharCore.exists_irr_of_monoidHom` (a linear character is irreducible) gives the required
`λ`.

Everything used from the paper (Ch. V §1–2) is elementary; the hypotheses `hC4`, `hS`, `hD`,
`hKcyc`, `hKset` of the statement are not needed for this particular consequence.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF

variable {G : Type*} [Group G]

/-! ## The point stabilisers in `G ⧸ H` -/

/-- In the action of `G` on `G ⧸ H`, the point `H` is fixed exactly by `H`. -/
theorem smul_one_eq_one_iff {H : Subgroup G} {g : G} :
    g • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) ↔ g ∈ H := by
  rw [show g • ((1 : G) : G ⧸ H) = ((g * 1 : G) : G ⧸ H) from rfl, QuotientGroup.eq]
  simp [H.inv_mem_iff]

/-- In the action of `G` on `G ⧸ H`, the point `tH` is fixed exactly by the conjugate
`conj t H = t H t⁻¹` of `H`. -/
theorem smul_t_eq_t_iff {H : Subgroup G} {t g : G} :
    g • (t : G ⧸ H) = (t : G ⧸ H) ↔ g ∈ conj t H := by
  rw [show g • (t : G ⧸ H) = ((g * t : G) : G ⧸ H) from rfl, QuotientGroup.eq,
    Work.Models.mem_conj_iff, show (g * t)⁻¹ * t = (t⁻¹ * g * t)⁻¹ from by group, H.inv_mem_iff]

/-! ## `D = 1` implies the Zassenhaus property -/

/-- If the two-point stabiliser `twoPoint H t = H ⊓ conj t H` is trivial and `G` is
2-transitive on `G ⧸ H`, then `G` is a Zassenhaus group on `G ⧸ H`: the pointwise stabiliser of
any three points is trivial.

Indeed the stabiliser of the pair `(H, tH)` of distinct points is exactly `twoPoint H t`, and by
2-transitivity every two-point stabiliser is a `G`-conjugate of it. -/
theorem isZassenhaus_of_twoPoint_eq_bot {H : Subgroup G} {t : G}
    (htrans : IsTwoTransitiveOn H) (ht : t ∉ H) (hbot : twoPoint H t = ⊥) :
    IsZassenhaus H := by
  intro a b c hab hac hbc g hga hgb hgc
  have h1t : ((1 : G) : G ⧸ H) ≠ (t : G ⧸ H) := by
    intro h
    exact ht (by simpa using (QuotientGroup.eq.mp h : (1 : G)⁻¹ * t ∈ H))
  have h2 : ∀ {p q r s : G ⧸ H}, p ≠ q → r ≠ s → ∃ g : G, g • p = r ∧ g • q = s :=
    MulAction.is_two_pretransitive_iff.mp htrans
  obtain ⟨m, hm1, hm2⟩ := h2 (p := ((1 : G) : G ⧸ H)) (q := (t : G ⧸ H))
    (r := a) (s := b) h1t hab
  have hfix1 : (m⁻¹ * g * m) • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
    rw [mul_smul, mul_smul, hm1, hga, ← hm1, ← mul_smul, inv_mul_cancel, one_smul]
  have hfix2 : (m⁻¹ * g * m) • (t : G ⧸ H) = (t : G ⧸ H) := by
    rw [mul_smul, mul_smul, hm2, hgb, ← hm2, ← mul_smul, inv_mul_cancel, one_smul]
  have hmem : m⁻¹ * g * m ∈ twoPoint H t := by
    rw [twoPoint, Subgroup.mem_inf]
    exact ⟨smul_one_eq_one_iff.mp hfix1, smul_t_eq_t_iff.mp hfix2⟩
  rw [hbot] at hmem
  have hgm : m⁻¹ * g * m = 1 := Subgroup.mem_bot.mp hmem
  calc g = m * (m⁻¹ * g * m) * m⁻¹ := by group
    _ = 1 := by rw [hgm]; group

/-- If `H` is not a Zassenhaus subgroup in the split rank-one situation, then the two-point
stabiliser `D = H ⊓ H^t` is nontrivial. -/
theorem twoPoint_ne_bot_of_not_isZassenhaus {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (hZ : ¬ IsZassenhaus H) : twoPoint H t ≠ ⊥ :=
  fun hbot => hZ (isZassenhaus_of_twoPoint_eq_bot h.twoTransitive h.not_mem hbot)

/-! ## Existence of a nontrivial homomorphism `A →* ℂˣ` for `A` finite solvable nontrivial -/

/-- The principal character has degree one. -/
theorem irrDeg_principal (A : Type*) [Group A] [Fintype A] :
    Work.CharCore.irrDeg (fun _ : A => (1 : ℂ)) = 1 := by
  have hmem : (fun _ : A => (1 : ℂ)) ∈ Work.CharCore.Irr A :=
    Work.CharCore.principalChar_mem_Irr
  have h := Work.CharCore.irrDeg_spec hmem
  have h1 : ((Work.CharCore.irrDeg (fun _ : A => (1 : ℂ)) : ℕ) : ℂ) = 1 := by simpa using h.symm
  exact_mod_cast h1

/-- **A nontrivial finite solvable group has a nontrivial homomorphism into `ℂˣ`.**

The number of irreducible characters of degree one equals the order of the abelianisation
(`Work.CharCore.card_irr_deg_one`), which is `≥ 2` for a nontrivial solvable group
(`Group.IsSolvable.commutator_lt_top_of_nontrivial`).  As the principal character has degree one,
there is a second degree-one irreducible character `χ ≠ 1`, which is the character of a
one-dimensional representation, i.e. `χ = fun a => (φ a : ℂ)` for some `φ : A →* ℂˣ`, and
`χ ≠ 1` forces `φ ≠ 1` (`Work.CharCore.linear_char_iff_deg_one`). -/
theorem exists_monoidHom_units_ne_one {A : Type*} [Group A] [Fintype A] [Group.IsSolvable A]
    (hnt : Nontrivial A) : ∃ φ : A →* ℂˣ, φ ≠ 1 := by
  classical
  -- the abelianisation of a nontrivial solvable group is nontrivial
  have hlt : commutator A < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial A
  haveI hntq : Nontrivial (A ⧸ commutator A) := by
    have hex : ∃ a : A, a ∉ commutator A := by
      by_contra hc
      push_neg at hc
      exact ne_of_lt hlt ((Subgroup.eq_top_iff' (commutator A)).mpr hc)
    obtain ⟨a, ha⟩ := hex
    refine ⟨1, (QuotientGroup.mk' (commutator A)) a, ?_⟩
    intro hcon
    rw [QuotientGroup.mk'_apply] at hcon
    exact ha ((QuotientGroup.eq_one_iff a).mp hcon.symm)
  -- hence there are at least two irreducible characters of degree one
  have hcard : 2 ≤ ((Work.CharCore.Irr A).filter
      (fun χ => Work.CharCore.irrDeg χ = 1)).card := by
    rw [Work.CharCore.card_irr_deg_one, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card_iff_nontrivial.mpr hntq
  -- the principal character is one of them, so there is a non-principal one
  have hprin : (fun _ : A => (1 : ℂ)) ∈
      (Work.CharCore.Irr A).filter (fun χ => Work.CharCore.irrDeg χ = 1) :=
    Finset.mem_filter.mpr ⟨Work.CharCore.principalChar_mem_Irr, irrDeg_principal A⟩
  have hex : ∃ χ ∈ (Work.CharCore.Irr A).filter
      (fun χ => Work.CharCore.irrDeg χ = 1), χ ≠ (fun _ : A => (1 : ℂ)) := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Work.CharCore.Irr A).filter (fun χ => Work.CharCore.irrDeg χ = 1) ⊆
        {(fun _ : A => (1 : ℂ))} := fun χ hχ => Finset.mem_singleton.mpr (hcon χ hχ)
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    omega
  obtain ⟨χ, hχmem, hχne⟩ := hex
  have hχirr : χ ∈ Work.CharCore.Irr A := (Finset.mem_filter.mp hχmem).1
  have hχdeg : Work.CharCore.irrDeg χ = 1 := (Finset.mem_filter.mp hχmem).2
  obtain ⟨φ, hφ⟩ := (Work.CharCore.linear_char_iff_deg_one hχirr).mp hχdeg
  refine ⟨φ, fun h1 => hχne (funext fun a => ?_)⟩
  simp [hφ a, h1]

/-! ## The theorem -/

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem exists_linear {G : Type} [Group G] [Fintype G] (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (H Q : Subgroup G) (t : G) (hS : Situation G) (h : IsSplitRankOne H Q t) (hZ : ¬ IsZassenhaus H) (hD : ∀ a ∈ involutions (H : Set G), ∀ b ∈ involutions (H : Set G), ∃ d ∈ twoPoint H t, d * a * d⁻¹ = b) (hKcyc : IsCyclic ↥(Ksub H t)) (hKset : (Ksub H t : Set G) = Kset H t) : ∃ lam : H → ℂ, lam ∈ Work.CharCore.Irr H ∧ lam 1 = 1 ∧ lam ≠ (fun _ : H => (1 : ℂ)) ∧ (∀ x : H, (x : G) ∈ Q → lam x = 1) := by
  classical
  -- `D = H ⊓ H^t` is nontrivial
  have hDne : twoPoint H t ≠ ⊥ := twoPoint_ne_bot_of_not_isZassenhaus h hZ
  -- `D` has odd order, hence is solvable (Feit–Thompson)
  haveI hsolvD : Group.IsSolvable ↥(twoPoint H t) :=
    hFT ↥(twoPoint H t) (split_odd_card_twoPoint h)
  -- `Q ⊴ H`
  haveI hnorm : (Q.subgroupOf H).Normal := split_Q_normal_in_H h
  -- the natural map `D →* H ⧸ Q` is surjective
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (Q.subgroupOf H)).comp
        (Subgroup.inclusion (inf_le_left : twoPoint H t ≤ H))) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf H) y
    obtain ⟨p, hp, -⟩ := split_exists_unique_factor h x.2
    obtain ⟨hp1, hp2, hp3⟩ := hp
    refine ⟨⟨p.1, hp1⟩, ?_⟩
    have hxeq : x = Subgroup.inclusion (inf_le_left : twoPoint H t ≤ H) ⟨p.1, hp1⟩ *
        (⟨p.2, h.le hp2⟩ : ↥H) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]
      exact hp3.symm
    show (QuotientGroup.mk' (Q.subgroupOf H))
        (Subgroup.inclusion (inf_le_left : twoPoint H t ≤ H) ⟨p.1, hp1⟩)
      = (QuotientGroup.mk' (Q.subgroupOf H)) x
    rw [hxeq, map_mul]
    have hone : (QuotientGroup.mk' (Q.subgroupOf H)) (⟨p.2, h.le hp2⟩ : ↥H) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hp2)
    rw [hone, mul_one]
  -- so `H ⧸ Q` is solvable and nontrivial
  have hsolvQ : Group.IsSolvable (↥H ⧸ Q.subgroupOf H) :=
    Group.isSolvable_of_surjective hsurj
  have hntQ : Nontrivial (↥H ⧸ Q.subgroupOf H) := by
    obtain ⟨dt, hdt1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
    have hdH : (dt : G) ∈ H := (Subgroup.mem_inf.mp dt.2).1
    have hdQ : (dt : G) ∉ Q := by
      intro hdQ
      have hmem : (dt : G) ∈ Q ⊓ twoPoint H t := ⟨hdQ, dt.2⟩
      rw [h.inf_eq] at hmem
      exact hdt1 (Subtype.ext (Subgroup.mem_bot.mp hmem))
    let dH : ↥H := ⟨(dt : G), hdH⟩
    refine ⟨1, (QuotientGroup.mk' (Q.subgroupOf H)) dH, ?_⟩
    intro hcon
    rw [QuotientGroup.mk'_apply] at hcon
    have hmem : dH ∈ Q.subgroupOf H := (QuotientGroup.eq_one_iff dH).mp hcon.symm
    exact hdQ (Subgroup.mem_subgroupOf.mp hmem)
  -- a nontrivial homomorphism out of the quotient, pulled back to `H`
  obtain ⟨ψ, hψne⟩ := exists_monoidHom_units_ne_one hntQ
  let φ : ↥H →* ℂˣ := ψ.comp (QuotientGroup.mk' (Q.subgroupOf H))
  have hφQ : ∀ x : ↥H, (x : G) ∈ Q → φ x = 1 := by
    intro x hx
    have hx1 : (QuotientGroup.mk' (Q.subgroupOf H)) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr hx)
    rw [show φ x = ψ ((QuotientGroup.mk' (Q.subgroupOf H)) x) from rfl, hx1, map_one]
  have hφne : φ ≠ 1 := by
    intro h1
    refine hψne (MonoidHom.ext fun y => ?_)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf H) y
    have hxy : φ x = 1 := DFunLike.congr_fun h1 x
    simpa [φ] using hxy
  -- a linear character is irreducible
  obtain ⟨lam, hlam, hlamval⟩ := Work.CharCore.exists_irr_of_monoidHom φ
  refine ⟨lam, hlam, ?_, ?_, ?_⟩
  · rw [hlamval 1]; simp
  · intro hcon
    have hex : ∃ x : ↥H, φ x ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hφne (MonoidHom.ext fun x => by rw [hc x]; rfl)
    obtain ⟨x, hx⟩ := hex
    refine hx (Units.val_eq_one.mp ?_)
    show ((φ x : ℂˣ) : ℂ) = 1
    rw [← hlamval x, hcon]
  · intro x hx
    rw [hlamval x, hφQ x hx]
    simp

end Work.ThmF.ChV12
