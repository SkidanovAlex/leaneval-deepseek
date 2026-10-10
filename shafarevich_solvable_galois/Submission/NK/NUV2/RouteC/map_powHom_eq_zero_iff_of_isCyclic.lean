import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Submission.NK.NUV2.RouteC.Invariant
import Submission.NK.NUV2.RouteC.map_powHom_eq_zero_of_mem_normGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cyclic character criterion: `a ∪ δχ = 0` iff `a` is a norm

For a finite Galois extension `E / F` with **cyclic** Galois group `G = Gal(E/F)`, a character
`χ : G → ℚ/ℤ` of order `|G|` (i.e. a faithful character, equivalently `δχ` generates
`H²(G, ℤ) ≅ ℤ/|G|`) and `a ∈ Fˣ`, the cup product

`a ∪ δχ = map (MonoidHom.id G) (powHom a) 2 (δχ) ∈ H²(G, Eˣ)`

vanishes **iff** `a` is a norm from `E`, i.e. lies in the image of `N_{E/F} : Eˣ → Fˣ`.

The direction `⟸` ("`θ` kills norms") is
`NK.NUV2.RouteC.map_powHom_eq_zero_of_mem_normGroup`.

For `⟹`, write `G = ⟨g₀⟩` and lift `χ` to `y : G → ℚ` (`y g` represents `χ g` modulo `ℤ`); then

`x (g, h) := y h - y (g * h) + y g ∈ ℤ`

is a 2-cocycle on `G` with trivial coefficients whose class is `δχ`; this is the concrete form of
the connecting map `δ : H¹(G, ℚ/ℤ) → H²(G, ℤ)` (Mathlib's `groupCohomology.δ₁_apply`).  By
naturality of `H2π` (`H2π_comp_map`) the class `a ∪ δχ` is represented by the cocycle
`p ↦ a ^ {x p}`, and its **transgression** `T = ∑_{t<|G|} x (g₀ ^ t, g₀)` computes `a ^ T`:

* `T (d₁₂ e) = (∑_σ ρ_σ) e (g₀)` for every 1-cochain `e` (the telescoping of the middle terms),
  so if `a ∪ δχ = 0` then `a ^ T` is a norm;
* `T = |G| · y g₀`, and `y g₀` represents an element of order `|G|` in `ℚ/ℤ`, so `gcd (T, |G|) = 1`;
* `a ^ {|G|} = N (a)` is a norm as well, so Bézout's identity puts `a` itself in the norm group.

This is the cyclic case of Tate's theorem, in the explicit form needed by the local reciprocity
law (`NK.NUV2.RouteD`'s L6).
-/

open CategoryTheory
open scoped BigOperators

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.NUV2.RouteC

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
lemma qmodZ_lift_add_zero (χ : Additive G →+ qmodZ) (y : G → ℚ)
    (hy : ∀ g, ((y g : ℚ) : qmodZ) = χ (Additive.ofMul g)) (g h : G) :
    ((y h - y (g * h) + y g : ℚ) : qmodZ) = 0 := by
  have key : ratToQmodZ (y h - y (g * h) + y g)
      = χ (Additive.ofMul h) - χ (Additive.ofMul (g*h)) + χ (Additive.ofMul g) := by
    have hy' : ∀ t : G, ratToQmodZ (y t) = χ (Additive.ofMul t) := fun t => hy t
    rw [map_add, map_sub, hy' h, hy' (g*h), hy' g]
  change ratToQmodZ (y h - y (g * h) + y g) = 0
  rw [key, show Additive.ofMul (g * h) = Additive.ofMul g + Additive.ofMul h from rfl, map_add]
  abel

omit [Fintype G] in
lemma exists_int_lift (χ : Additive G →+ qmodZ) (y : G → ℚ)
    (hy : ∀ g, ((y g : ℚ) : qmodZ) = χ (Additive.ofMul g)) (g h : G) :
    ∃ m : ℤ, (m : ℚ) = y h - y (g * h) + y g :=
  ratToQmodZ_eq_zero_iff _ |>.mp (qmodZ_lift_add_zero χ y hy g h)

/-- The explicit integer 2-cocycle attached to a lift `y` of `χ`. -/
noncomputable def chiCocycle (χ : Additive G →+ qmodZ) (y : G → ℚ)
    (hy : ∀ g, ((y g : ℚ) : qmodZ) = χ (Additive.ofMul g)) : G × G → ℤ :=
  fun p => Classical.choose (exists_int_lift χ y hy p.1 p.2)

omit [Fintype G] in
lemma chiCocycle_spec (χ : Additive G →+ qmodZ) (y : G → ℚ)
    (hy : ∀ g, ((y g : ℚ) : qmodZ) = χ (Additive.ofMul g)) (g h : G) :
    ((chiCocycle χ y hy (g, h) : ℤ) : ℚ) = y h - y (g * h) + y g :=
  Classical.choose_spec (exists_int_lift χ y hy g h)

omit [Fintype G] in
lemma chiCocycle_d_eq (χ : Additive G →+ qmodZ) (y : G → ℚ)
    (hy : ∀ g, ((y g : ℚ) : qmodZ) = χ (Additive.ofMul g)) :
    ⇑(coeffF G).hom ∘ chiCocycle χ y hy
      = groupCohomology.d₁₂ (Rep.trivial ℤ G ℚ) y := by
  funext p
  obtain ⟨g, h⟩ := p
  show ((chiCocycle χ y hy (g, h) : ℤ) : ℚ) = groupCohomology.d₁₂ (Rep.trivial ℤ G ℚ) y (g, h)
  rw [groupCohomology.d₁₂_hom_apply, trivialRep_ρ_apply]
  exact chiCocycle_spec χ y hy g h

lemma deltaHomChar_eq_H2π (χ : Additive G →+ qmodZ) (y : G → ℚ)
    (hy : ∀ g, ratToQmodZ (y g) = χ (Additive.ofMul g)) :
    deltaHomChar G χ = groupCohomology.H2π (Rep.trivial ℤ G ℤ)
      ⟨chiCocycle χ y hy,
        groupCohomology.mem_cocycles₂_of_comp_eq_d₁₂ (coeffSes_shortExact G)
          (chiCocycle_d_eq χ y hy)⟩ := by
  rw [show deltaHomChar G χ = groupCohomology.δ (coeffSes_shortExact G) 1 2 rfl
      (groupCohomology.H1π (Rep.trivial ℤ G qmodZ) (homCocycle G qmodZ χ)) from rfl]
  have shy : ⇑(Rep.Hom.hom (coeffSes G).g) ∘ y = ⇑(homCocycle G qmodZ χ) := by
    funext g
    show ratToQmodZ (y g) = χ (Additive.ofMul g)
    exact hy g
  rw [groupCohomology.δ₁_apply (hX := coeffSes_shortExact G) (z := homCocycle G qmodZ χ)
    (y := y) (hy := shy) (x := chiCocycle χ y hy) (hx := chiCocycle_d_eq χ y hy)]

private lemma pow_injOn (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Set.InjOn (fun t : ℕ => g ^ t) ↑(Finset.range (Fintype.card G)) := by
  have hord : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  intro a ha b hb hab
  have h1 : a ≡ b [MOD orderOf g] := pow_eq_pow_iff_modEq.mp hab
  rw [hord] at h1
  exact Nat.ModEq.eq_of_lt_of_lt h1 (Finset.mem_range.mp ha) (Finset.mem_range.mp hb)

private lemma pow_image_eq_univ [DecidableEq G] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Finset.image (fun t : ℕ => g ^ t) (Finset.range (Fintype.card G)) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn (pow_injOn g hg), Finset.card_range]

lemma sum_range_pow_eq_sum (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {M : Type*} [AddCommMonoid M] (f : G → M) :
    (∑ t ∈ Finset.range (Fintype.card G), f (g ^ t)) = ∑ x : G, f x := by
  classical
  rw [← Finset.sum_image (pow_injOn g hg), pow_image_eq_univ g hg]

lemma sum_range_shift {M : Type*} [AddCommGroup M] (f : ℕ → M) (n : ℕ) (h : f 0 = f n) :
    (∑ t ∈ Finset.range n, f (t + 1)) = ∑ t ∈ Finset.range n, f t := by
  have h1 : (∑ t ∈ Finset.range n, (f (t + 1) - f t)) = f n - f 0 := Finset.sum_range_sub f n
  rw [Finset.sum_sub_distrib, h, sub_self] at h1
  exact sub_eq_zero.mp h1

theorem sum_range_d12_eq_norm (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {k : Type} [CommRing k] (A : Rep k G) (e : G → A.V) :
    (∑ t ∈ Finset.range (Fintype.card G),
        (groupCohomology.d₁₂ A e) (g ^ t, g)) = A.norm.hom (e g) := by
  have hgn : g ^ Fintype.card G = 1 := pow_card_eq_one
  have hterm : ∀ t : ℕ, (groupCohomology.d₁₂ A e) (g ^ t, g)
      = A.ρ (g ^ t) (e g) + (e (g ^ t) - e (g ^ (t + 1))) := by
    intro t
    rw [groupCohomology.d₁₂_hom_apply, pow_succ]
    abel
  have htel : (∑ t ∈ Finset.range (Fintype.card G),
      (e (g ^ t) - e (g ^ (t + 1)))) = 0 := by
    rw [Finset.sum_range_sub', hgn]
    simp
  rw [Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_add_distrib, htel, add_zero]
  rw [show (∑ t ∈ Finset.range (Fintype.card G), A.ρ (g ^ t) (e g))
      = ∑ x : G, A.ρ x (e g) from sum_range_pow_eq_sum g hg (fun x => A.ρ x (e g))]
  exact (norm_apply_eq_sum (A := A) (e g)).symm

omit [Fintype G] in
lemma addOrderOf_addMonoidHom_eq_of_generator {M : Type} [AddCommGroup M]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (χ : Additive G →+ M) :
    addOrderOf χ = addOrderOf (χ (Additive.ofMul g)) := by
  refine Nat.dvd_antisymm ?_ ?_
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    refine AddMonoidHom.ext (fun x => ?_)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg (Additive.toMul x))
    have hx : m • Additive.ofMul g = x := by
      rw [← ofMul_zpow, hm]
      rfl
    rw [AddMonoidHom.nsmul_apply, AddMonoidHom.zero_apply, ← hx, map_zsmul, smul_comm,
      addOrderOf_nsmul_eq_zero, smul_zero]
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    rw [← AddMonoidHom.nsmul_apply, addOrderOf_nsmul_eq_zero, AddMonoidHom.zero_apply]

lemma addOrderOf_zmodToQmodZ {n : ℕ} (hn : n ≠ 0) (k : ZMod n) :
    addOrderOf (zmodToQmodZ n k) = addOrderOf k :=
  addOrderOf_injective _ (zmodToQmodZ_injective hn) k

lemma exists_zsmul_combination {n : ℕ} (hn : n ≠ 0) {t : ℚ} {T : ℤ}
    (hT : (T : ℚ) = n * t) (ht : addOrderOf (((t : ℚ) : qmodZ)) = n) :
    ∃ j l : ℤ, j * T + l * (n : ℤ) = 1 := by
  have hquot : (T : ℚ) / (n : ℚ) = t := by
    rw [hT]
    field_simp
  have hTn : zmodToQmodZ n (T : ZMod n) = ((t : ℚ) : qmodZ) := by
    rw [zmodToQmodZ_intCast, hquot]
    rfl
  haveI : NeZero n := ⟨hn⟩
  have hcard : Nat.card (ZMod n) = n := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hord : addOrderOf ((T : ℤ) : ZMod n) = Nat.card (ZMod n) := by
    rw [← addOrderOf_zmodToQmodZ hn ((T : ℤ) : ZMod n), hTn, ht, hcard]
  have htop := zmultiples_eq_top_of_addOrderOf_eq_card ((T : ℤ) : ZMod n) hord
  have h1 : (1 : ZMod n) ∈ AddSubgroup.zmultiples ((T : ℤ) : ZMod n) := by rw [htop]; trivial
  obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp h1
  have h2 : (((j * T - 1 : ℤ)) : ZMod n) = 0 := by
    have h3 : ((j * T : ℤ) : ZMod n) = 1 := by
      rw [Int.cast_mul, mul_comm, ← zsmul_eq_mul', hj]
    rw [Int.cast_sub, h3, Int.cast_one, sub_self]
  have h4 : (n : ℤ) ∣ (j * T - 1) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp h2
  obtain ⟨l, hl⟩ := h4
  exact ⟨j, -l, by linear_combination hl⟩

end NK.NUV2.RouteC

namespace NK.NUV2.RouteC

set_option backward.isDefEq.respectTransparency false

theorem map_powHom_eq_zero_iff_of_isCyclic {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (hcyc : IsCyclic (E ≃ₐ[F] E))
    (χ : Additive (E ≃ₐ[F] E) →+ NK.NUV2.RouteC.qmodZ)
    (hχ : addOrderOf χ = Nat.card (E ≃ₐ[F] E)) (a : Fˣ) :
    (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
        (NK.NUV2.RouteC.powHom (F := F) (E := E) a) 2
        (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) χ) = 0)
      ↔ a ∈ MonoidHom.range (Units.map (Algebra.norm F : E →* F)) := by
  classical
  constructor
  · intro hzero
    obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
    -- the lift of `χ` to `ℚ`
    let y : (E ≃ₐ[F] E) → ℚ := fun g => Quotient.out (χ (Additive.ofMul g))
    have hy : ∀ g, ((y g : ℚ) : qmodZ) = χ (Additive.ofMul g) := fun g => Quotient.out_eq _
    -- the integer cocycle
    let z : groupCohomology.cocycles₂ (Rep.trivial ℤ (E ≃ₐ[F] E) ℤ) :=
      ⟨chiCocycle χ y hy,
        groupCohomology.mem_cocycles₂_of_comp_eq_d₁₂ (coeffSes_shortExact (E ≃ₐ[F] E))
          (chiCocycle_d_eq χ y hy)⟩
    have hdelta : deltaHomChar (E ≃ₐ[F] E) χ
        = groupCohomology.H2π (Rep.trivial ℤ (E ≃ₐ[F] E) ℤ) z :=
      deltaHomChar_eq_H2π χ y hy
    rw [hdelta] at hzero
    -- naturality of `H2π`
    have hnat : (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
          (powHom (F := F) (E := E) a) 2)
            (groupCohomology.H2π (Rep.trivial ℤ (E ≃ₐ[F] E) ℤ) z)
        = groupCohomology.H2π (Rep.ofAlgebraAutOnUnits F E)
          (groupCohomology.mapCocycles₂ (MonoidHom.id (E ≃ₐ[F] E))
            (powHom (F := F) (E := E) a) z) :=
      congrArg (fun m => m z)
        (groupCohomology.H2π_comp_map (k := ℤ) (G := E ≃ₐ[F] E)
          (A := Rep.trivial ℤ (E ≃ₐ[F] E) ℤ) (B := Rep.ofAlgebraAutOnUnits F E)
          (MonoidHom.id (E ≃ₐ[F] E)) (powHom (F := F) (E := E) a))
    rw [hnat, groupCohomology.H2π_eq_zero_iff, groupCohomology.coboundaries₂] at hzero
    obtain ⟨e, he⟩ := hzero
    -- the underlying function of the transported cocycle
    have hxa : ⇑(groupCohomology.mapCocycles₂ (MonoidHom.id (E ≃ₐ[F] E))
        (powHom (F := F) (E := E) a) z)
        = fun p : (E ≃ₐ[F] E) × (E ≃ₐ[F] E) => (powHom (F := F) (E := E) a).hom (z p) := by
      rw [groupCohomology.coe_mapCocycles₂]
      funext p
      rfl
    have he' : (groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits F E)).hom e
        = fun p : (E ≃ₐ[F] E) × (E ≃ₐ[F] E) => (powHom (F := F) (E := E) a).hom (z p) :=
      he.trans hxa
    -- the telescoping identity
    have hTel : (∑ t ∈ Finset.range (Fintype.card (E ≃ₐ[F] E)),
          (powHom (F := F) (E := E) a).hom (z (g₀ ^ t, g₀)))
        = (Rep.ofAlgebraAutOnUnits F E).norm.hom (e g₀) := by
      rw [← sum_range_d12_eq_norm g₀ hg₀ (Rep.ofAlgebraAutOnUnits F E) e]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      exact (congrFun he' (g₀ ^ t, g₀)).symm
    -- the value of `powHom a` on `m`
    let ā : Additive Eˣ := Additive.ofMul (Units.map (algebraMap F E).toMonoidHom a)
    have hpow : ∀ m : ℤ, (powHom (F := F) (E := E) a).hom m = m • ā := by
      intro m
      unfold powHom
      simp only [Rep.hom_ofHom]
      rfl
    let T : ℤ := ∑ t ∈ Finset.range (Fintype.card (E ≃ₐ[F] E)),
      chiCocycle χ y hy (g₀ ^ t, g₀)
    have hsum_xa : (∑ t ∈ Finset.range (Fintype.card (E ≃ₐ[F] E)),
          (powHom (F := F) (E := E) a).hom (z (g₀ ^ t, g₀))) = T • ā := by
      rw [Finset.sum_congr rfl (fun t _ => hpow (z (g₀ ^ t, g₀)))]
      exact (Finset.sum_smul (R := ℤ) (M := Additive Eˣ)
        (f := fun t : ℕ => z (g₀ ^ t, g₀)) (x := ā)).symm
    have hTX : (Rep.ofAlgebraAutOnUnits F E).norm.hom (e g₀) = T • ā := hTel.symm.trans hsum_xa
    -- `T` as a rational number
    have hT_rat : (T : ℚ) = (Fintype.card (E ≃ₐ[F] E) : ℚ) * y g₀ := by
      have h1 : (T : ℚ) = ∑ t ∈ Finset.range (Fintype.card (E ≃ₐ[F] E)),
          ((chiCocycle χ y hy (g₀ ^ t, g₀) : ℤ) : ℚ) := by
        simp [T, Int.cast_sum]
      rw [h1]
      have h2 : ∀ t : ℕ, ((chiCocycle χ y hy (g₀ ^ t, g₀) : ℤ) : ℚ)
          = y g₀ + (y (g₀ ^ t) - y (g₀ ^ (t + 1))) := by
        intro t
        rw [chiCocycle_spec χ y hy (g₀ ^ t) g₀, pow_succ]
        ring
      rw [Finset.sum_congr rfl (fun t _ => h2 t), Finset.sum_add_distrib]
      have h3 : (∑ t ∈ Finset.range (Fintype.card (E ≃ₐ[F] E)),
            (y (g₀ ^ t) - y (g₀ ^ (t + 1)))) = 0 := by
        rw [Finset.sum_range_sub', pow_card_eq_one]
        simp
      rw [h3, add_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    -- the order of `y g₀` in `ℚ/ℤ`
    have hord : addOrderOf (((y g₀ : ℚ)) : qmodZ) = Fintype.card (E ≃ₐ[F] E) := by
      rw [hy g₀, ← addOrderOf_addMonoidHom_eq_of_generator g₀ hg₀ χ, hχ,
        Nat.card_eq_fintype_card]
    -- Bezout
    obtain ⟨j, l, hjl⟩ := exists_zsmul_combination Fintype.card_ne_zero hT_rat hord
    -- `ā` is `G`-fixed and `n • ā` is a norm
    have hafix : ∀ σ : E ≃ₐ[F] E, (Rep.ofAlgebraAutOnUnits F E).ρ σ ā = ā := by
      intro σ
      apply Additive.ofMul.injective
      apply Units.ext
      show σ ((Units.map (algebraMap F E).toMonoidHom a : Eˣ) : E)
        = ((Units.map (algebraMap F E).toMonoidHom a : Eˣ) : E)
      rw [show ((Units.map (algebraMap F E).toMonoidHom a : Eˣ) : E) = algebraMap F E a from rfl]
      exact σ.commutes a
    have hnorm_a : (Rep.ofAlgebraAutOnUnits F E).norm.hom ā
        = (Fintype.card (E ≃ₐ[F] E) : ℤ) • ā := by
      rw [norm_apply_eq_sum, Finset.sum_congr rfl (fun σ _ => hafix σ), Finset.sum_const,
        Finset.card_univ]
      exact (Nat.cast_smul_eq_nsmul ℤ _ ā).symm
    -- conclude `ā` is a norm
    have hmem : ā ∈ Set.range ⇑((Rep.ofAlgebraAutOnUnits F E).norm.hom) := by
      obtain ⟨w₁, hw₁⟩ : T • ā ∈ Set.range ⇑((Rep.ofAlgebraAutOnUnits F E).norm.hom) :=
        ⟨e g₀, hTX⟩
      obtain ⟨w₂, hw₂⟩ : (Fintype.card (E ≃ₐ[F] E) : ℤ) • ā
          ∈ Set.range ⇑((Rep.ofAlgebraAutOnUnits F E).norm.hom) := ⟨ā, hnorm_a⟩
      refine ⟨j • w₁ + l • w₂, ?_⟩
      rw [map_add, map_zsmul, map_zsmul, hw₁, hw₂, smul_smul, smul_smul, ← add_smul, hjl,
        one_smul]
    -- convert to the statement
    obtain ⟨w, hw⟩ := hmem
    let y' : Eˣ := Additive.toMul w
    have hwy : Additive.ofMul y' = w := rfl
    have h1 : Additive.ofMul (Units.map (algebraMap F E).toMonoidHom
          (Units.map (Algebra.norm F) y'))
        = Additive.ofMul (Units.map (algebraMap F E).toMonoidHom a) := by
      rw [← norm_hom_ofMul_eq (F := F) (E := E) y', hwy]
      exact hw
    have h2 : Units.map (algebraMap F E).toMonoidHom (Units.map (Algebra.norm F) y')
        = Units.map (algebraMap F E).toMonoidHom a := Additive.ofMul.injective h1
    have h3 : Units.map (Algebra.norm F) y' = a :=
      Units.map_injective (FaithfulSMul.algebraMap_injective F E) h2
    exact ⟨y', h3⟩
  · intro ha
    exact map_powHom_eq_zero_of_mem_normGroup χ a ha

end NK.NUV2.RouteC
