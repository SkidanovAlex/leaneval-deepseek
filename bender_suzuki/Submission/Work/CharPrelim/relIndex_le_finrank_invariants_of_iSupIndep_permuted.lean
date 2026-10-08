import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.CharPrelim

open scoped QuotientGroup

theorem relIndex_le_finrank_invariants_of_iSupIndep_permuted {L : Type*} [Field L] {E : Type*}
    [Group E] [Fintype E] {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (ρ : Representation L E V) (W : E → Submodule L V) (hind : iSupIndep W)
    (hsup : ⨆ e : E, W e = ⊤) (hperm : ∀ (e h : E), Submodule.map (ρ e) (W h) = W (e * h))
    (hne : W 1 ≠ ⊥) (E₀ : Subgroup E) :
    E₀.index ≤ Module.finrank L ↥(Representation.invariants (ρ.comp E₀.subtype)) := by
  classical
  -- Basic pointwise multiplication rule for the representation.
  have hmul : ∀ (x y : E) (v : V), ρ x (ρ y v) = ρ (x * y) v := by
    intro x y v
    show (ρ x * ρ y) v = ρ (x * y) v
    rw [← map_mul]
  -- Every `W e` is nonzero.
  have hWe : ∀ e : E, W e ≠ ⊥ := by
    intro e hbot
    have h1 : W 1 = Submodule.map (ρ e⁻¹) (W e) := by
      rw [hperm e⁻¹ e, inv_mul_cancel]
    rw [h1, hbot, Submodule.map_bot] at hne
    exact hne rfl
  -- A nonzero vector of `W 1`.
  obtain ⟨w, hwmem, hwne⟩ := (Submodule.ne_bot_iff (W 1)).mp hne
  have hmem : ∀ g : E, (ρ g) w ∈ W g := by
    intro g
    have h1 := hperm g 1
    rw [mul_one] at h1
    rw [← h1]
    exact Submodule.mem_map_of_mem hwmem
  have hρw : ∀ g : E, ρ g w ≠ 0 := by
    intro g hz
    have h1 : ρ g⁻¹ (ρ g w) = w := by rw [hmul, inv_mul_cancel]; simp
    rw [hz, map_zero] at h1
    exact hwne h1.symm
  -- The "orbit sum" map.
  let S : E → V := fun h => ∑ e : E₀, ρ ((e : E) * h) w
  -- `S h` is fixed by `E₀`.
  have hSinv : ∀ h : E, S h ∈ Representation.invariants (ρ.comp E₀.subtype) := by
    intro h
    rw [Representation.mem_invariants]
    intro a
    show ρ (a : E) (∑ e : E₀, ρ ((e : E) * h) w) = ∑ e : E₀, ρ ((e : E) * h) w
    rw [map_sum]
    rw [show (∑ e : E₀, ρ (a : E) (ρ ((e : E) * h) w)) =
        ∑ e : E₀, ρ (((a : E) * (e : E)) * h) w from by
      apply Finset.sum_congr rfl; intro e _; rw [hmul, mul_assoc]]
    rw [show (∑ e : E₀, ρ (((a : E) * (e : E)) * h) w) =
        ∑ e : E₀, ρ ((e : E) * h) w from by
      have h2 := Equiv.sum_comp (Equiv.mulLeft a) (fun e : E₀ => ρ ((e : E) * h) w)
      simpa using h2]
  -- `S` is constant on right cosets of `E₀`.
  have hSconst : ∀ (a : E₀) (h : E), S ((a : E) * h) = S h := by
    intro a h
    show (∑ e : E₀, ρ ((e : E) * ((a : E) * h)) w) = ∑ e : E₀, ρ ((e : E) * h) w
    rw [show (∑ e : E₀, ρ ((e : E) * ((a : E) * h)) w) =
        ∑ e : E₀, ρ (((e : E) * (a : E)) * h) w from by
      apply Finset.sum_congr rfl; intro e _; rw [mul_assoc]]
    rw [show (∑ e : E₀, ρ (((e : E) * (a : E)) * h) w) =
        ∑ e : E₀, ρ ((e : E) * h) w from by
      have h2 := Equiv.sum_comp (Equiv.mulRight a) (fun e : E₀ => ρ ((e : E) * h) w)
      simpa using h2]
  -- Distinct right cosets give distinct values: the support of `S h` is the coset.
  have lemma3 : ∀ (h h' : E), S h = S h' → h' * h⁻¹ ∈ E₀ := by
    intro h h' heq
    by_contra hmem'
    let μ : E₀ ⊕ E₀ → E := Sum.elim (fun e : E₀ => (e : E) * h) (fun e : E₀ => (e : E) * h')
    have hμ : Function.Injective μ := by
      intro i j hij
      cases i with
      | inl a =>
        cases j with
        | inl b =>
          simp only [μ, Sum.elim_inl] at hij
          have : (a : E) = (b : E) := mul_right_cancel hij
          exact congrArg Sum.inl (Subtype.ext this)
        | inr b =>
          exfalso
          simp only [μ, Sum.elim_inl, Sum.elim_inr] at hij
          apply hmem'
          have h2 : (b : E)⁻¹ * ((a : E) * h) = h' := by rw [hij]; group
          have hb : h' * h⁻¹ = (b : E)⁻¹ * (a : E) := by rw [← h2]; group
          rw [hb]
          exact E₀.mul_mem (E₀.inv_mem b.2) a.2
      | inr a =>
        cases j with
        | inl b =>
          exfalso
          simp only [μ, Sum.elim_inl, Sum.elim_inr] at hij
          apply hmem'
          have h2 : (a : E)⁻¹ * ((b : E) * h) = h' := by rw [← hij]; group
          have hb : h' * h⁻¹ = (a : E)⁻¹ * (b : E) := by rw [← h2]; group
          rw [hb]
          exact E₀.mul_mem (E₀.inv_mem a.2) b.2
        | inr b =>
          simp only [μ, Sum.elim_inr] at hij
          have : (a : E) = (b : E) := mul_right_cancel hij
          exact congrArg Sum.inr (Subtype.ext this)
    have hindμ : iSupIndep (W ∘ μ) := hind.comp hμ
    let u : E₀ ⊕ E₀ → V :=
      Sum.elim (fun e : E₀ => ρ ((e : E) * h) w) (fun e : E₀ => -ρ ((e : E) * h') w)
    have hmem_u : ∀ i ∈ (Finset.univ : Finset (E₀ ⊕ E₀)), u i ∈ (W ∘ μ) i := by
      intro i _
      cases i with
      | inl e => exact hmem ((e : E) * h)
      | inr e => exact Submodule.neg_mem _ (hmem ((e : E) * h'))
    have hsum_u : ∑ i : E₀ ⊕ E₀, u i = 0 := by
      rw [Fintype.sum_sum_type]
      simp only [u, Sum.elim_inl, Sum.elim_inr]
      rw [Finset.sum_neg_distrib]
      change S h + -S h' = 0
      rw [heq]; simp
    have hdec := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (W ∘ μ)).mp hindμ
      (Finset.univ) u hmem_u hsum_u
    have h0 : u (Sum.inl (1 : E₀)) = 0 := hdec (Sum.inl 1) (Finset.mem_univ _)
    apply hρw h
    simpa [u] using h0
  -- The values `S h` form a linearly independent family in `V`.
  have lemma4 : LinearIndependent L (fun y : ↥(Set.range S) => (y.1 : V)) := by
    rw [linearIndependent_iff']
    intro s g hsum
    let f : ↥(Set.range S) → E := fun y => Classical.choose y.2
    have hf : ∀ y : ↥(Set.range S), S (f y) = y.1 := fun y => Classical.choose_spec y.2
    let ν : ↥(Set.range S) × E₀ → E := fun x => (x.2 : E) * f x.1
    have hν : Function.Injective ν := by
      intro x y hxy
      obtain ⟨x1, xe⟩ := x
      obtain ⟨y1, ye⟩ := y
      simp only [ν] at hxy
      have h2 : ((ye : E)⁻¹ * (xe : E)) * f x1 = f y1 := by rw [mul_assoc, hxy]; group
      have ha : (ye : E)⁻¹ * (xe : E) ∈ E₀ := E₀.mul_mem (E₀.inv_mem ye.2) xe.2
      have hS : S (f y1) = S (f x1) := by
        rw [← h2]
        exact hSconst ⟨_, ha⟩ (f x1)
      have hy : y1 = x1 := Subtype.ext (by rw [← hf y1, hS, hf x1])
      subst hy
      have : (xe : E) = (ye : E) := mul_right_cancel hxy
      exact Prod.ext rfl (Subtype.ext this)
    let u : ↥(Set.range S) × E₀ → V := fun x => g x.1 • ρ ((x.2 : E) * f x.1) w
    have hmem_u : ∀ x ∈ (s ×ˢ Finset.univ : Finset (↥(Set.range S) × E₀)), u x ∈ (W ∘ ν) x := by
      intro x _
      exact Submodule.smul_mem _ (g x.1) (hmem _)
    have hinner : ∀ y : ↥(Set.range S),
        (∑ e ∈ (Finset.univ : Finset E₀), u (y, e)) = g y • (y.1 : V) := by
      intro y
      simp only [u]
      rw [← Finset.smul_sum]
      congr 1
      rw [← hf y]
    have hsum_u : ∑ x ∈ (s ×ˢ Finset.univ : Finset (↥(Set.range S) × E₀)), u x = 0 := by
      rw [Finset.sum_product]
      rw [Finset.sum_congr rfl (fun y _ => hinner y)]
      exact hsum
    have hdec := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (W ∘ ν)).mp (hind.comp hν)
      (s ×ˢ Finset.univ) u hmem_u hsum_u
    intro y hy
    have h1 : u (y, 1) = 0 := hdec (y, 1) (Finset.mem_product.mpr ⟨hy, Finset.mem_univ _⟩)
    have h2 : g y • ρ (f y) w = 0 := by simpa [u] using h1
    by_contra hgy
    have h3 : (g y)⁻¹ • (g y • ρ (f y) w) = ρ (f y) w := by
      rw [← mul_smul, inv_mul_cancel₀ hgy, one_smul]
    rw [h2, smul_zero] at h3
    exact hρw (f y) h3.symm
  -- The number of distinct values of `S` is the index of `E₀`.
  haveI : Fintype ↥(Set.range S) := (Set.finite_range S).fintype
  have lemma5 : Fintype.card ↥(Set.range S) = E₀.index := by
    have hwd : ∀ x y : E, (QuotientGroup.rightRel E₀) x y → S x = S y := by
      intro x y hxy
      rw [QuotientGroup.rightRel_apply] at hxy
      have hy : y = (y * x⁻¹) * x := by group
      rw [hy]
      exact (hSconst ⟨y * x⁻¹, hxy⟩ x).symm
    let S' : Quotient (QuotientGroup.rightRel E₀) → V := Quotient.lift S hwd
    have hS' : ∀ a, S' ⟦a⟧ = S a := fun a => Quotient.lift_mk S hwd a
    have hinj : Function.Injective S' := by
      intro p q hpq
      induction p using Quotient.inductionOn with
      | h a =>
        induction q using Quotient.inductionOn with
        | h b =>
          rw [hS' a, hS' b] at hpq
          exact Quotient.sound (show (QuotientGroup.rightRel E₀) a b from
            (QuotientGroup.rightRel_apply).mpr (lemma3 a b hpq))
    have hrange : Set.range S = Set.range S' := by
      apply Set.ext
      intro v
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨⟦a⟧, hS' a⟩
      · rintro ⟨q, rfl⟩
        induction q using Quotient.inductionOn with
        | h a => exact ⟨a, (hS' a).symm⟩
    haveI : Fintype ↥(Set.range S') := (Set.finite_range S').fintype
    calc Fintype.card ↥(Set.range S) = Fintype.card ↥(Set.range S') :=
          Fintype.card_congr (Set.equivOfEq hrange)
      _ = Fintype.card (Quotient (QuotientGroup.rightRel E₀)) :=
          Fintype.card_congr (Equiv.ofInjective S' hinj).symm
      _ = Fintype.card (E ⧸ E₀) := QuotientGroup.card_quotient_rightRel E₀
      _ = E₀.index := by rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  -- Assemble.
  have hb : Fintype.card ↥(Set.range S) ≤
      Module.finrank L ↥(Representation.invariants (ρ.comp E₀.subtype)) := by
    have hli : LinearIndependent L (fun y : ↥(Set.range S) =>
        (⟨y.1, by rw [← Classical.choose_spec y.2]; exact hSinv (Classical.choose y.2)⟩ :
          ↥(Representation.invariants (ρ.comp E₀.subtype)))) :=
      LinearIndependent.of_comp (Submodule.subtype _) (by
        show LinearIndependent L (fun y : ↥(Set.range S) => (y.1 : V))
        exact lemma4)
    exact hli.fintype_card_le_finrank
  rw [← lemma5]
  exact hb

end Work.CharPrelim
