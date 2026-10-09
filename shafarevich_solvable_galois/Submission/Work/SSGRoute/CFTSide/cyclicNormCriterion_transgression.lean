import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.phi1_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.CFTSide

open CategoryTheory
open scoped BigOperators

/-- The coefficient ring of the `Ext` core (`SSGRoute.PTExt.Coeff = ULift ℤ`), locally. -/
abbrev CycCoeff : Type := SSGRoute.PTExt.Coeff

/-! ## Telescoping lemmas for the transgression of a `2`-cocycle

These are the general (coefficient-free) facts used by the transgression argument: the sum of
`d₁₂ e` over the powers of a generator of a finite group is the norm of `e` at the generator. -/

section Telescoping

variable {G : Type} [Group G] [Fintype G]

private lemma pow_injOn (p : ℕ) (hp : Fintype.card G = p) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Set.InjOn (fun t : ℕ => g ^ t) ↑(Finset.range p) := by
  have hord : orderOf g = p := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hp]
  intro a ha b hb hab
  have h1 : a ≡ b [MOD orderOf g] := pow_eq_pow_iff_modEq.mp hab
  rw [hord] at h1
  exact Nat.ModEq.eq_of_lt_of_lt h1 (Finset.mem_range.mp ha) (Finset.mem_range.mp hb)

private lemma pow_image_eq_univ [DecidableEq G] (p : ℕ) (hp : Fintype.card G = p) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Finset.image (fun t : ℕ => g ^ t) (Finset.range p) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn (pow_injOn p hp g hg), Finset.card_range, hp]

lemma sum_range_pow_eq_sum (p : ℕ) (hp : Fintype.card G = p) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) {M : Type*} [AddCommMonoid M] (f : G → M) :
    (∑ t ∈ Finset.range p, f (g ^ t)) = ∑ x : G, f x := by
  classical
  rw [← Finset.sum_image (pow_injOn p hp g hg), pow_image_eq_univ p hp g hg]

/-- The norm is the sum of the action: `A.norm a = ∑_g g · a`. -/
lemma norm_apply_eq_sum {k : Type} [CommRing k] (A : Rep k G) (a : A.V) :
    A.norm.hom a = ∑ g : G, A.ρ g a := by
  rw [Rep.norm_apply, Representation.norm]
  exact LinearMap.sum_apply Finset.univ (fun g : G => A.ρ g) a

/-- **Telescoping identity for the transgression**: for a generator `g` of a finite group `G` of
order `p` and a `1`-cochain `e` of a representation `A`, the sum of `d₁₂ e` over the powers of `g`
is the norm of `e g`. -/
lemma sum_range_d12_eq_norm {k : Type} [CommRing k] (p : ℕ) (hp : Fintype.card G = p)
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (e : G → A.V) :
    (∑ t ∈ Finset.range p, (groupCohomology.d₁₂ A e) (g ^ t, g)) = A.norm.hom (e g) := by
  have hgn : g ^ p = 1 := by rw [← hp]; exact pow_card_eq_one
  have hterm : ∀ t : ℕ, (groupCohomology.d₁₂ A e) (g ^ t, g)
      = A.ρ (g ^ t) (e g) + (e (g ^ t) - e (g ^ (t + 1))) := by
    intro t
    rw [groupCohomology.d₁₂_hom_apply, pow_succ]
    abel
  have htel : (∑ t ∈ Finset.range p, (e (g ^ t) - e (g ^ (t + 1)))) = 0 := by
    rw [Finset.sum_range_sub', hgn]
    simp
  rw [Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_add_distrib, htel, add_zero]
  rw [show (∑ t ∈ Finset.range p, A.ρ (g ^ t) (e g)) = ∑ x : G, A.ρ x (e g) from
    sum_range_pow_eq_sum p hp g hg (fun x => A.ρ x (e g))]
  exact (norm_apply_eq_sum A (e g)).symm

end Telescoping

/-! ## The transgression of the integral "carry" cocycle -/

/-- **The transgression of the integral `p`-torsion "carry" cocycle.**

For a finite group `G` of order `p` (prime), a generator `g₀`, a nonzero character
`f : Additive G →+ ZMod p` and an integral lift `Y : G → ℤ` of `f`, there is an integral
`2`-cochain `Z` with `(p : ℤ) * Z (g, h) = Y h - Y (g * h) + Y g` (the "carry" of the coboundary
of `Y` along the coefficient sequence `0 → ℤ --p--> ℤ → 𝔽_p → 0`), its transgression over the
powers of the generator telescopes to `Y g₀`, and `Y g₀` is coprime to `p`. -/
theorem transgression_carry (G : Type) [Group G] [Fintype G] (p : ℕ) [Fact p.Prime]
    (g₀ : G) (hg₀ : ∀ x, x ∈ Subgroup.zpowers g₀) (hp : Fintype.card G = p)
    (f : Additive G →+ ZMod p) (hf : f ≠ 0) (Y : G → ℤ)
    (hY : ∀ g, ((Y g : ℤ) : ZMod p) = f (Additive.ofMul g)) :
    ∃ Z : G × G → ℤ,
      (∀ g h, (p : ℤ) * Z (g, h) = Y h - Y (g * h) + Y g) ∧
      (∑ t ∈ Finset.range p, Z (g₀ ^ t, g₀)) = Y g₀ ∧
      ¬ ((p : ℤ) ∣ Y g₀) ∧
      ∃ j l : ℤ, j * Y g₀ + l * (p : ℤ) = 1 := by
  classical
  have hp0 : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hfg₀ : f (Additive.ofMul g₀) ≠ 0 := by
    intro h0
    apply hf
    refine AddMonoidHom.ext fun x => ?_
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ (Additive.toMul x))
    have hx : m • Additive.ofMul g₀ = x := by rw [← ofMul_zpow, hm]; rfl
    rw [← hx, AddMonoidHom.map_zsmul, h0, smul_zero, AddMonoidHom.zero_apply]
  have hndvd : ¬ ((p : ℤ) ∣ Y g₀) := by
    intro hdiv
    apply hfg₀
    rw [← hY g₀]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (Y g₀) p).mpr hdiv
  have hdvd : ∀ g h : G, (p : ℤ) ∣ (Y h - Y (g * h) + Y g) := by
    intro g h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hY h, hY (g * h), hY g]
    rw [show Additive.ofMul (g * h) = Additive.ofMul g + Additive.ofMul h from rfl, map_add]
    ring
  refine ⟨fun q : G × G => (Y q.2 - Y (q.1 * q.2) + Y q.1) / (p : ℤ), ?_, ?_, hndvd, ?_⟩
  · intro g h
    exact Int.mul_ediv_cancel' (hdvd g h)
  · have hgp : g₀ ^ p = 1 := by rw [← hp]; exact pow_card_eq_one
    have hstep : ∀ t : ℕ,
        (p : ℤ) * (fun q : G × G => (Y q.2 - Y (q.1 * q.2) + Y q.1) / (p : ℤ)) (g₀ ^ t, g₀)
          = Y g₀ - Y (g₀ ^ (t + 1)) + Y (g₀ ^ t) := by
      intro t
      show (p : ℤ) * ((Y g₀ - Y (g₀ ^ t * g₀) + Y (g₀ ^ t)) / (p : ℤ)) = _
      rw [Int.mul_ediv_cancel' (hdvd (g₀ ^ t) g₀), pow_succ]
    have hsum : (∑ t ∈ Finset.range p, Y (g₀ ^ (t + 1))) = ∑ t ∈ Finset.range p, Y (g₀ ^ t) := by
      have h0 : Y (g₀ ^ p) - Y (g₀ ^ 0) = 0 := by rw [hgp]; simp
      have h1 := Finset.sum_range_sub (fun t => Y (g₀ ^ t)) p
      rw [h0] at h1
      rw [Finset.sum_sub_distrib] at h1
      linarith
    have hmain : (p : ℤ) * (∑ t ∈ Finset.range p,
          (fun q : G × G => (Y q.2 - Y (q.1 * q.2) + Y q.1) / (p : ℤ)) (g₀ ^ t, g₀))
        = (p : ℤ) * Y g₀ := by
      rw [Finset.mul_sum, Finset.sum_congr rfl (fun t _ => hstep t)]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      ring
    have hzero : (p : ℤ) * ((∑ t ∈ Finset.range p,
          (fun q : G × G => (Y q.2 - Y (q.1 * q.2) + Y q.1) / (p : ℤ)) (g₀ ^ t, g₀)) - Y g₀) = 0 := by
      rw [mul_sub, hmain, sub_self]
    rcases mul_eq_zero.mp hzero with h1 | h1
    · exact absurd h1 hp0
    · linarith
  · have hunit : ((Y g₀ : ℤ) : ZMod p) ≠ 0 := by
      intro h0
      exact hndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd (Y g₀) p).mp h0)
    obtain ⟨j, hj⟩ := ZMod.intCast_surjective (((Y g₀ : ℤ) : ZMod p))⁻¹
    have h1 : ((j * Y g₀ : ℤ) : ZMod p) = 1 := by
      rw [Int.cast_mul, hj, inv_mul_cancel₀ hunit]
    have h2 : (p : ℤ) ∣ (j * Y g₀ - 1) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_one, h1, sub_self]
    obtain ⟨l, hl⟩ := h2
    exact ⟨j, -l, by linear_combination hl⟩

/-! ## A nonzero class in `H¹(G, 𝔽_p)` as a character with integral lift -/

/-- **A nonzero class in `H¹(G, 𝔽_p)` is a nonzero character, with an integral lift.**

For a group `G`, an element `g₀` generating `G`, and a nonzero class `h ∈ H¹(G, 𝔽_p)`
(`𝔽_p = ZMod p` trivial, coefficients `CycCoeff = ULift ℤ`), there are an additive character
`f : Additive G →+ ZMod p` with `f (Additive.ofMul g₀) ≠ 0` and an integral lift `Y` of `f` such
that `h` is the class of the cocycle `g ↦ f (Additive.ofMul g)`. -/
theorem exists_lift_and_hom_of_ne_zero (G : Type) [Group G] (p : ℕ) (g₀ : G)
    (hg₀ : ∀ x, x ∈ Subgroup.zpowers g₀)
    (h : groupCohomology (Rep.trivial CycCoeff G (ZMod p)) 1) (hne : h ≠ 0) :
    ∃ (f : Additive G →+ ZMod p) (Y : G → ℤ), f ≠ 0 ∧ f (Additive.ofMul g₀) ≠ 0 ∧
      (∀ g, ((Y g : ℤ) : ZMod p) = f (Additive.ofMul g)) ∧
      h = groupCohomology.H1π (Rep.trivial CycCoeff G (ZMod p))
            ⟨f ∘ Additive.ofMul,
              groupCohomology.mem_cocycles₁_of_addMonoidHom
                (A := Rep.trivial CycCoeff G (ZMod p)) f⟩ := by
  classical
  let A : Rep CycCoeff G := Rep.trivial CycCoeff G (ZMod p)
  let e := groupCohomology.H1IsoOfIsTrivial A
  let f : Additive G →+ ZMod p := e.hom h
  let z : groupCohomology.cocycles₁ A :=
    ⟨f ∘ Additive.ofMul, groupCohomology.mem_cocycles₁_of_addMonoidHom (A := A) f⟩
  have hz : (CategoryTheory.ConcreteCategory.hom (groupCohomology.cocycles₁IsoOfIsTrivial A).inv)
      f = z := by
    apply Subtype.ext
    rfl
  have hh : h = groupCohomology.H1π A z := by
    have h2 : e.inv f = h := by
      have h3 := CategoryTheory.Iso.hom_inv_id_apply e h
      rwa [show e.hom h = f from rfl] at h3
    rw [← h2, groupCohomology.H1IsoOfIsTrivial_inv_apply, hz]
  have hfne : f ≠ 0 := by
    intro hf
    have hz0 : z = 0 := by
      apply Subtype.ext
      funext g
      show f (Additive.ofMul g) = (0 : groupCohomology.cocycles₁ A) g
      rw [hf]
      rfl
    exact hne (by rw [hh, hz0, map_zero])
  have hfg₀ : f (Additive.ofMul g₀) ≠ 0 := by
    intro h0
    apply hfne
    refine AddMonoidHom.ext fun x => ?_
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ (Additive.toMul x))
    have hx : m • Additive.ofMul g₀ = x := by rw [← ofMul_zpow, hm]; rfl
    rw [← hx, AddMonoidHom.map_zsmul, h0, smul_zero, AddMonoidHom.zero_apply]
  exact ⟨f, fun g => Classical.choose (ZMod.intCast_surjective (f (Additive.ofMul g))),
    hfne, hfg₀,
    fun g => Classical.choose_spec (ZMod.intCast_surjective (f (Additive.ofMul g))), hh⟩

/-! ## The connecting map computed on the carry cocycle -/

/-- **`δ` on `H¹(G, 𝔽_p)` computed by the carry cocycle.** If `h ∈ H¹(G, 𝔽_p)` is the class of the
cocycle attached to `f`, and `X` is a `CycCoeff`-valued `2`-cochain whose `p`-multiple is the
coboundary of the `CycCoeff`-valued lift `y` of `f` (so that `X` is a cocycle), then the connecting
map of `0 → ℤ --p--> ℤ → 𝔽_p → 0` applied to `h` is the class of `X`. -/
theorem coeffSES_delta_eq_H2π_carry (G : Type) [Group G] (p : ℕ) [Fact p.Prime]
    (f : Additive G →+ ZMod p) (Y : G → ℤ)
    (hY : ∀ g, ((Y g : ℤ) : ZMod p) = f (Additive.ofMul g))
    (Z : G × G → ℤ)
    (h : groupCohomology (Rep.trivial CycCoeff G (ZMod p)) 1)
    (hh : h = groupCohomology.H1π (Rep.trivial CycCoeff G (ZMod p))
            ⟨f ∘ Additive.ofMul,
              groupCohomology.mem_cocycles₁_of_addMonoidHom
                (A := Rep.trivial CycCoeff G (ZMod p)) f⟩)
    (hX : (⇑(Rep.Hom.hom (SSGRoute.Phi1.coeffSES G p).f)) ∘
          (fun q : G × G => (ULift.up (Z q) : CycCoeff))
        = ⇑(groupCohomology.d₁₂ (Rep.trivial CycCoeff G CycCoeff))
            (fun g : G => (ULift.up (Y g) : CycCoeff))) :
    (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom h =
      groupCohomology.H2π (Rep.trivial CycCoeff G CycCoeff)
        ⟨fun q : G × G => (ULift.up (Z q) : CycCoeff),
          groupCohomology.mem_cocycles₂_of_comp_eq_d₁₂
            (SSGRoute.Phi1.coeffSES_shortExact G p) hX⟩ := by
  rw [hh]
  refine groupCohomology.δ₁_apply (SSGRoute.Phi1.coeffSES_shortExact G p) _ _ ?_ _ hX
  ext g
  exact hY g

/-- The equation `p · X = d₁₂ y` for the `CycCoeff`-valued carry cocycle `X q = ↑(Z q)` attached to
`(Y, Z)` with `p · Z (g,h) = Y h - Y (g*h) + Y g`. -/
lemma carryCocycle_compat (G : Type) [Group G] (p : ℕ) (Y : G → ℤ) (Z : G × G → ℤ)
    (hZ : ∀ g h, (p : ℤ) * Z (g, h) = Y h - Y (g * h) + Y g) :
    (⇑(Rep.Hom.hom (SSGRoute.Phi1.coeffSES G p).f)) ∘
        (fun q : G × G => (ULift.up (Z q) : CycCoeff))
      = ⇑(groupCohomology.d₁₂ (Rep.trivial CycCoeff G CycCoeff))
          (fun g : G => (ULift.up (Y g) : CycCoeff)) := by
  funext q
  obtain ⟨g₁, g₂⟩ := q
  show (p : CycCoeff) * ULift.up (Z (g₁, g₂)) =
    (groupCohomology.d₁₂ (Rep.trivial CycCoeff G CycCoeff))
      (fun g : G => (ULift.up (Y g) : CycCoeff)) (g₁, g₂)
  rw [groupCohomology.d₁₂_hom_apply, Rep.trivial_ρ_apply]
  apply ULift.ext
  simp only [ULift.mul_down, ULift.add_down, ULift.sub_down]
  rw [show (((p : CycCoeff)).down : ℤ) = (p : ℤ) from rfl, hZ g₁ g₂]

/-! ## The cyclic norm criterion: the transgression half -/

/-- **The transgression half of the cyclic norm criterion** (`C_L` coefficients).

For a finite Galois extension `L/k` of number fields with `Gal(L/k)` cyclic of prime order `p`, an
element `a` of `C_L` fixed by `Gal(L/k)` and a nonzero character
`h ∈ H¹(Gal(L/k), 𝔽_p)`: if the cup product class
`groupCohomology.map (id) (powHomCls a) 2 (δ h)` (with `δ` the connecting map of
`SSGRoute.Phi1.coeffSES`, i.e. the Bockstein) vanishes, then `a` is a norm from `L`, i.e. lies in
the image of the norm endomorphism of the representation `classesK k L`.

Route (coefficient-module version of `NK.NUV2.RouteC.map_powHom_eq_zero_iff_of_isCyclic`, which is
proved for units coefficients): represent `δ h` by the integral "carry" 2-cocycle
`z (g₁, g₂) = (ȳ g₂ - ȳ (g₁ * g₂) + ȳ g₁) / p` attached to a set-theoretic lift `ȳ : G → ℤ` of `h`
(legal because `h` is a homomorphism into `𝔽_p`); the transgression
`T = Σ_{t < p} z (g₀ ^ t, g₀)` evaluated at a generator `g₀ ∉ ker h` equals `ȳ g₀`, so
`gcd (T, p) = 1`; the vanishing of the class says (telescoping, as in Route C's
`sum_range_d12_eq_norm`) that `T • a` is a norm, and `p • a` is a norm too, so Bézout's identity
gives `a` itself as a norm. -/
theorem cyclicNormCriterion_transgression (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (p : ℕ) [Fact p.Prime] (hcyc : IsCyclic (L ≃ₐ[k] L)) (hcard : Nat.card (L ≃ₐ[k] L) = p)
    (a : SSGRoute.PTExt.classesK k L)
    (hafix : ∀ σ : L ≃ₐ[k] L, (SSGRoute.PTExt.classesK k L).ρ σ a = a)
    (h : groupCohomology (Rep.trivial SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) (ZMod p)) 1) (hne : h ≠ 0)
    (hvan : groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L))
      (SSGRoute.Phi1.powHomCls k L a hafix) 2
      ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p) 1 2 rfl).hom h) = 0) :
    a ∈ Set.range ((SSGRoute.PTExt.classesK k L).norm.hom) := by
  classical
  haveI : IsCyclic (L ≃ₐ[k] L) := hcyc
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := L ≃ₐ[k] L)
  have hcard' : Fintype.card (L ≃ₐ[k] L) = p := by
    rw [← Nat.card_eq_fintype_card, hcard]
  -- the character and its integral lift
  obtain ⟨f, Y, hfne, hfg₀, hY, hhπ⟩ :=
    exists_lift_and_hom_of_ne_zero (L ≃ₐ[k] L) p g₀ hg₀ h hne
  -- the carry cocycle and its transgression
  obtain ⟨Z, hZ, hZsum, -, ⟨j, l, hjl⟩⟩ :=
    transgression_carry (L ≃ₐ[k] L) p g₀ hg₀ hcard' f hfne Y hY
  have hX : (⇑(Rep.Hom.hom (SSGRoute.Phi1.coeffSES (L ≃ₐ[k] L) p).f)) ∘
        (fun q : (L ≃ₐ[k] L) × (L ≃ₐ[k] L) => (ULift.up (Z q) : CycCoeff))
      = ⇑(groupCohomology.d₁₂ (Rep.trivial CycCoeff (L ≃ₐ[k] L) CycCoeff))
          (fun g : L ≃ₐ[k] L => (ULift.up (Y g) : CycCoeff)) :=
    carryCocycle_compat (L ≃ₐ[k] L) p Y Z hZ
  set zc : groupCohomology.cocycles₂ (Rep.trivial CycCoeff (L ≃ₐ[k] L) CycCoeff) :=
    ⟨fun q : (L ≃ₐ[k] L) × (L ≃ₐ[k] L) => (ULift.up (Z q) : CycCoeff),
      groupCohomology.mem_cocycles₂_of_comp_eq_d₁₂
        (SSGRoute.Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p) hX⟩ with hzc
  -- `δ h` is the class of the carry cocycle
  have hδ : (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p) 1 2 rfl).hom h
      = groupCohomology.H2π (Rep.trivial CycCoeff (L ≃ₐ[k] L) CycCoeff) zc :=
    coeffSES_delta_eq_H2π_carry (L ≃ₐ[k] L) p f Y hY Z h hhπ hX
  -- the vanishing hypothesis, rewritten
  have hvan1 : groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L))
        (SSGRoute.Phi1.powHomCls k L a hafix) 2
        (groupCohomology.H2π (Rep.trivial CycCoeff (L ≃ₐ[k] L) CycCoeff) zc) = 0 := by
    rw [← hδ]
    exact hvan
  -- naturality of `H2π`
  have hnat : (groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L))
        (SSGRoute.Phi1.powHomCls k L a hafix) 2)
        (groupCohomology.H2π (Rep.trivial CycCoeff (L ≃ₐ[k] L) CycCoeff) zc)
      = groupCohomology.H2π (SSGRoute.PTExt.classesK k L)
          (groupCohomology.mapCocycles₂ (MonoidHom.id (L ≃ₐ[k] L))
            (SSGRoute.Phi1.powHomCls k L a hafix) zc) :=
    congrArg (fun m => m zc)
      (groupCohomology.H2π_comp_map (A := Rep.trivial CycCoeff (L ≃ₐ[k] L) CycCoeff)
        (B := SSGRoute.PTExt.classesK k L) (MonoidHom.id (L ≃ₐ[k] L))
        (SSGRoute.Phi1.powHomCls k L a hafix))
  rw [hnat, groupCohomology.H2π_eq_zero_iff, groupCohomology.coboundaries₂] at hvan1
  obtain ⟨e, he⟩ := hvan1
  -- the transported cocycle is `q ↦ (Z q) • a`
  have hxa : ∀ q : (L ≃ₐ[k] L) × (L ≃ₐ[k] L),
      (groupCohomology.mapCocycles₂ (MonoidHom.id (L ≃ₐ[k] L))
        (SSGRoute.Phi1.powHomCls k L a hafix) zc) q = (Z q) • a := by
    intro q
    show (Rep.Hom.hom (SSGRoute.Phi1.powHomCls k L a hafix)) (zc q) = (Z q) • a
    rw [SSGRoute.Phi1.powHomCls_apply, ULift.smul_def, hzc]
    rfl
  have he' : (groupCohomology.d₁₂ (SSGRoute.PTExt.classesK k L)).hom e
      = fun q : (L ≃ₐ[k] L) × (L ≃ₐ[k] L) => (Z q) • a :=
    he.trans (funext hxa)
  -- the transgression of the vanishing class is a norm
  have hsum2 : (∑ t ∈ Finset.range p,
        ((fun q : (L ≃ₐ[k] L) × (L ≃ₐ[k] L) => (Z q) • a) (g₀ ^ t, g₀)))
      = (SSGRoute.PTExt.classesK k L).norm.hom (e g₀) := by
    rw [← sum_range_d12_eq_norm p hcard' g₀ hg₀ (SSGRoute.PTExt.classesK k L) e]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    exact (congrFun he' (g₀ ^ t, g₀)).symm
  have hTz_a : (∑ t ∈ Finset.range p, Z (g₀ ^ t, g₀)) • a
      = (SSGRoute.PTExt.classesK k L).norm.hom (e g₀) := by
    rw [← hsum2, Finset.sum_smul]
  have hYa : (Y g₀) • a ∈ Set.range (Rep.Hom.hom (SSGRoute.PTExt.classesK k L).norm) := by
    rw [← hZsum]
    exact ⟨e g₀, hTz_a.symm⟩
  -- `p • a` is a norm too
  have hpa : ((p : ℤ)) • a = (SSGRoute.PTExt.classesK k L).norm.hom a := by
    rw [norm_apply_eq_sum]
    rw [Finset.sum_congr rfl (fun σ _ => hafix σ), Finset.sum_const, Finset.card_univ, hcard',
      Nat.cast_smul_eq_nsmul ℤ p a]
  have hpa' : ((p : ℤ)) • a ∈ Set.range (Rep.Hom.hom (SSGRoute.PTExt.classesK k L).norm) := by
    rw [hpa]
    exact ⟨a, rfl⟩
  -- Bézout
  obtain ⟨w₁, hw₁⟩ := hYa
  obtain ⟨w₂, hw₂⟩ := hpa'
  refine ⟨j • w₁ + l • w₂, ?_⟩
  rw [map_add, map_zsmul, map_zsmul, hw₁, hw₂]
  rw [smul_smul, smul_smul, ← add_zsmul]
  rw [show j * (Y g₀) + l * (p : ℤ) = 1 from hjl, one_zsmul]

end Work.SSGRoute.CFTSide
