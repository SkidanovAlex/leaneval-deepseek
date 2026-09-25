import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Injectivity of the inflation map in degree 2

Let `S ◁ G` be a normal subgroup, `k` a commutative ring and `A` a `k`-linear `G`-representation.
The inflation map
`inf : H²(G ⧸ S, A^S) ⟶ H²(G, A)`
has kernel the image of the transgression `H¹(S, A)^(G ⧸ S) ⟶ H²(G ⧸ S, A^S)`, i.e. the exactness
of the five-term inflation-restriction sequence.  In particular, if `H¹(S, A) = 0` then
`inf` is injective.  This file proves the latter statement directly on the level of cocycles.

## Main results

* `Commons.RepresentationTheory.GroupCohomology.exists_sub_eq_of_subsingleton_H1`: if `H¹(S, A)`
  is a subsingleton then every `1`-cocycle on `S` is a coboundary.
* `Commons.RepresentationTheory.GroupCohomology.exists_coboundary_of_cochainsMap₂_eq_d₁₂`: the
  cocycle-level form of the five-term exact sequence: if the inflation of a `2`-cocycle `x` of
  `G ⧸ S` is a coboundary on `G`, and `H¹(S, A) = 0`, then `x` is a coboundary.
* `Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1`: the
  headline statement.
-/

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory Representation

universe u

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

/-- If `H¹(S, A)` is a subsingleton, then every `1`-cocycle `ψ` on `S` with values in `A` is a
coboundary: `ψ s = s • α - α` for some `α : A`. -/
lemma exists_sub_eq_of_subsingleton_H1 (S : Subgroup G) [S.Normal] (A : Rep k G)
    (h : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (ψ : S → A) (hψ : ψ ∈ groupCohomology.cocycles₁ (Rep.res S.subtype A)) :
    ∃ α : A, ∀ s : S, A.ρ s.1 α - α = ψ s := by
  have h0 : groupCohomology.H1π (Rep.res S.subtype A) ⟨ψ, hψ⟩ = 0 := Subsingleton.elim _ _
  rw [groupCohomology.H1π_eq_zero_iff] at h0
  rw [groupCohomology.coboundaries₁] at h0
  obtain ⟨α, hα⟩ := h0
  exact ⟨α, fun s => congr_fun hα s⟩

set_option maxHeartbeats 1600000 in
/-- **The cocycle-level five-term exact sequence.**  Let `S ◁ G`, let `x` be a `2`-cocycle of
`G ⧸ S` with values in the invariants `A^S`, and suppose that an inhomogeneous `1`-cochain `y` on
`G` satisfies `d y = infl x`, i.e. `y` exhibits the inflation of `x` as a coboundary.  If
`H¹(S, A) = 0`, then `x` itself is a coboundary on `G ⧸ S` with values in `A^S`. -/
lemma exists_coboundary_of_cochainsMap₂_eq_d₁₂ (S : Subgroup G) [S.Normal] (A : Rep k G)
    (h : Subsingleton (groupCohomology (Rep.res S.subtype A) 1))
    (x : groupCohomology.cocycles₂ (A.quotientToInvariants S))
    (y : G → A)
    (hy : ∀ g h', A.ρ g (y h') - y (g * h') + y g
        = (x (QuotientGroup.mk' S g, QuotientGroup.mk' S h') : A)) :
    ∃ z : G ⧸ S → (A.quotientToInvariants S).V,
      (groupCohomology.d₁₂ (A.quotientToInvariants S)) z = ⇑x := by
  let a : A := (x (1, 1) : A)
  have ha_mem : ∀ s : S, A.ρ s.1 a = a := by
    intro s
    have hx := (x (1, 1)).2 s
    simp only [a]
    simpa using hx
  have hx1snd : ∀ g : G, (x (QuotientGroup.mk' S g, 1) : A) = A.ρ g a := by
    intro g
    have h1 := groupCohomology.cocycles₂_map_one_snd x (QuotientGroup.mk' S g)
    have h2 := congrArg (fun z : (A.quotientToInvariants S).V => (z : A)) h1
    simp only at h2
    rw [h2]
    simp only [a]
    simp
  have hx1fst : ∀ q : G ⧸ S, (x (1, q) : A) = a := by
    intro q
    have h1 := groupCohomology.cocycles₂_map_one_fst x q
    exact congrArg (fun z : (A.quotientToInvariants S).V => (z : A)) h1
  have hmem : ∀ s : S, QuotientGroup.mk' S s.1 = 1 := by
    intro s
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (s : G)).2 s.2
  let ψ : S → A := fun s => y s.1 - a
  have hψmem : ψ ∈ groupCohomology.cocycles₁ (Rep.res S.subtype A) := by
    rw [groupCohomology.mem_cocycles₁_def]
    intro s t
    show A.ρ s.1 (y t.1 - a) - (y (s.1 * t.1) - a) + (y s.1 - a) = 0
    have h1 : A.ρ s.1 (y t.1) - y (s.1 * t.1) + y s.1 = a := by
      have hh := hy s.1 t.1
      rw [hmem s, hmem t] at hh
      exact hh.trans (hx1fst 1)
    have hgoal : A.ρ s.1 (y t.1 - a) - (y (s.1 * t.1) - a) + (y s.1 - a)
        = (A.ρ s.1 (y t.1) - y (s.1 * t.1) + y s.1) - A.ρ s.1 a := by
      rw [map_sub]; abel
    rw [hgoal, h1, ha_mem s, sub_self]
  obtain ⟨α, hα⟩ := exists_sub_eq_of_subsingleton_H1 S A h ψ hψmem
  have hys : ∀ s : S, y s.1 = a + (A.ρ s.1 α - α) := by
    intro s
    have hh : A.ρ s.1 α - α = y s.1 - a := hα s
    have h2 : y s.1 = (A.ρ s.1 α - α) + a := sub_eq_iff_eq_add.mp hh.symm
    rw [h2]; abel
  let zfun : G → A := fun g => y g - (A.ρ g α - α)
  have hz_right : ∀ (g : G) (s : S), zfun (g * s.1) = zfun g := by
    intro g s
    have h1 : A.ρ g (y s.1) - y (g * s.1) + y g = A.ρ g a := by
      have hh := hy g s.1
      rw [hmem s, hx1snd g] at hh
      exact hh
    have h4 : A.ρ g (y s.1) = A.ρ g a + (A.ρ (g * s.1) α - A.ρ g α) := by
      rw [hys s, map_add, map_sub]
      simp only [Module.End.mul_apply, map_mul]
    rw [h4] at h1
    have h10 : A.ρ (g * s.1) α - A.ρ g α + y g = y (g * s.1) := by
      have hX : A.ρ g a + (A.ρ (g * s.1) α - A.ρ g α + y g - y (g * s.1))
          = A.ρ g a + 0 := by
        conv_rhs => rw [← h1]
        abel
      have hY : A.ρ (g * s.1) α - A.ρ g α + y g - y (g * s.1) = 0 := add_left_cancel hX
      exact sub_eq_zero.mp hY
    show y (g * s.1) - (A.ρ (g * s.1) α - α) = y g - (A.ρ g α - α)
    rw [← h10]
    abel
  have hz_inv : ∀ g : G, ∀ t : S, A.ρ t.1 (zfun g) = zfun g := by
    intro g t
    have h1 : A.ρ t.1 (y g) - y (t.1 * g) + y t.1 = a := by
      have hh := hy t.1 g
      rw [hmem t, hx1fst (QuotientGroup.mk' S g)] at hh
      exact hh
    rw [hys t] at h1
    have h2 : A.ρ t.1 (y g) + (A.ρ t.1 α - α) = y (t.1 * g) := by
      have hX : A.ρ t.1 (y g) + (A.ρ t.1 α - α) - y (t.1 * g) + a = 0 + a := by
        conv_rhs => rw [← h1]
        abel
      have hY : A.ρ t.1 (y g) + (A.ρ t.1 α - α) - y (t.1 * g) = 0 := add_right_cancel hX
      exact sub_eq_zero.mp hY
    have h5 : A.ρ t.1 (y g - (A.ρ g α - α)) = A.ρ t.1 (y g) + A.ρ t.1 α - A.ρ (t.1 * g) α := by
      rw [map_sub, map_sub, ← Module.End.mul_apply, ← map_mul]
      abel
    have h3 : zfun (t.1 * g) = zfun g := by
      have htg : t.1 * g = g * (g⁻¹ * t.1 * g) := by group
      rw [htg, hz_right g ⟨g⁻¹ * t.1 * g, Subgroup.Normal.conj_mem' ‹S.Normal› t.1 t.2 g⟩]
    show A.ρ t.1 (zfun g) = zfun g
    have h6 : A.ρ t.1 (zfun g) = zfun (t.1 * g) := by
      show A.ρ t.1 (y g - (A.ρ g α - α)) = y (t.1 * g) - (A.ρ (t.1 * g) α - α)
      rw [h5, ← h2]
      abel
    rw [h6, h3]
  let zf : G ⧸ S → (A.quotientToInvariants S).V :=
    fun q => q.liftOn' (fun g => (⟨zfun g, hz_inv g⟩ : (Rep.res S.subtype A).ρ.invariants))
      (fun a b hab => by
        rw [QuotientGroup.leftRel_apply] at hab
        refine Subtype.ext ?_
        show zfun a = zfun b
        have hb : b = a * (a⁻¹ * b) := by group
        rw [hb, hz_right a ⟨a⁻¹ * b, hab⟩])
  have hzf : ∀ g : G, zf (QuotientGroup.mk' S g) = ⟨zfun g, hz_inv g⟩ := by
    intro g
    rw [QuotientGroup.mk'_apply]
    exact Quotient.liftOn'_mk g _ _
  refine ⟨zf, ?_⟩
  funext q
  obtain ⟨q₁, q₂⟩ := q
  induction q₁ using QuotientGroup.induction_on with | _ g =>
  induction q₂ using QuotientGroup.induction_on with | _ h =>
  refine Subtype.ext ?_
  have hzz : A.ρ g (zfun h) - zfun (g * h) + zfun g
      = (x (QuotientGroup.mk' S g, QuotientGroup.mk' S h) : A) := by
    have hz : groupCohomology.d₁₂ A zfun = groupCohomology.d₁₂ A y := by
      have hsub : zfun = y - (groupCohomology.d₀₁ A) α := by
        funext g
        show y g - (A.ρ g α - α) = y g - (groupCohomology.d₀₁ A) α g
        rfl
      rw [hsub, map_sub, groupCohomology.d₀₁_comp_d₁₂_apply A α, sub_zero]
    have hy2 : A.ρ g (y h) - y (g * h) + y g
        = (x (QuotientGroup.mk' S g, QuotientGroup.mk' S h) : A) := hy g h
    have h2 : A.ρ g (zfun h) - zfun (g * h) + zfun g
        = (groupCohomology.d₁₂ A zfun) (g, h) := rfl
    rw [h2, hz]
    exact hy2
  have hL : ((groupCohomology.d₁₂ (A.quotientToInvariants S)) zf
      (QuotientGroup.mk' S g, QuotientGroup.mk' S h) : A)
      = A.ρ g (zfun h) - zfun (g * h) + zfun g := by
    rw [groupCohomology.d₁₂_hom_apply]
    rw [hzf h, hzf g]
    have e3 : QuotientGroup.mk' S g * QuotientGroup.mk' S h = QuotientGroup.mk' S (g * h) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.mk_mul]
    rw [e3, hzf (g * h)]
    simp
  exact hL.trans hzz

/-- **Injectivity of the inflation map in degree 2.**  If `H¹(S, A) = 0` for a normal subgroup
`S ◁ G`, then the inflation map `H²(G ⧸ S, A^S) ⟶ H²(G, A)` is injective. -/
theorem H2_inflation_injective_of_subsingleton_H1_general (S : Subgroup G) [S.Normal] (A : Rep k G)
    (h : Subsingleton (groupCohomology (Rep.res S.subtype A) 1)) :
    Function.Injective ((groupCohomology.infNatTrans k S 2).app A).hom := by
  set φ : Rep.res (QuotientGroup.mk' S) (A.quotientToInvariants S) ⟶ A :=
    Rep.ofHom (A.ρ.quotientToInvariants_lift S)
  change Function.Injective (groupCohomology.map (QuotientGroup.mk' S) φ 2)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  induction x using groupCohomology.H2_induction_on with | h x₀ =>
  have hstep : groupCohomology.H2π A
      (groupCohomology.mapCocycles₂ (QuotientGroup.mk' S) φ x₀) = 0 := by
    rw [← groupCohomology.H2π_comp_map_apply (QuotientGroup.mk' S) φ x₀]
    exact hx
  have hmem : (⇑(groupCohomology.mapCocycles₂ (QuotientGroup.mk' S) φ x₀) : G × G → A)
      ∈ groupCohomology.coboundaries₂ A := (groupCohomology.H2π_eq_zero_iff _).1 hstep
  rw [groupCohomology.coboundaries₂] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hy'' : ∀ g h', A.ρ g (y h') - y (g * h') + y g
      = (x₀ (QuotientGroup.mk' S g, QuotientGroup.mk' S h') : A) := by
    intro g h'
    have hA : A.ρ g (y h') - y (g * h') + y g = (groupCohomology.d₁₂ A) y (g, h') := rfl
    have hB : (⇑(groupCohomology.mapCocycles₂ (QuotientGroup.mk' S) φ x₀) : G × G → A) (g, h')
        = (x₀ (QuotientGroup.mk' S g, QuotientGroup.mk' S h') : A) := by
      rw [groupCohomology.coe_mapCocycles₂]
      rfl
    rw [hA, ← hB]
    exact congr_fun hy (g, h')
  obtain ⟨z, hz⟩ := exists_coboundary_of_cochainsMap₂_eq_d₁₂ S A h x₀ y hy''
  have hfin : groupCohomology.H2π (A.quotientToInvariants S) x₀ = 0 :=
    (groupCohomology.H2π_eq_zero_iff x₀).2 ⟨z, hz⟩
  exact hfin

/-- **Injectivity of the inflation map in degree 2** (CoNF XII, proof of (12.2.1)): if `H¹(S, A)`
is trivial for a normal subgroup `S ◁ G`, then the inflation map `H²(G ⧸ S, A^S) ⟶ H²(G, A)` of
`ℤ`-representations is injective. -/
theorem H2_inflation_injective_of_subsingleton_H1 {G : Type} [Group G] (S : Subgroup G) [S.Normal]
    (A : Rep ℤ G) (h : Subsingleton (groupCohomology (Rep.res S.subtype A) 1)) :
    Function.Injective ((groupCohomology.infNatTrans ℤ S 2).app A).hom :=
  H2_inflation_injective_of_subsingleton_H1_general S A h


end Commons.RepresentationTheory.GroupCohomology
