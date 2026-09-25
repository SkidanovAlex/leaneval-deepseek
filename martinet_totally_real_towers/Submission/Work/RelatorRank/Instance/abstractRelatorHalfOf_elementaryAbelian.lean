import Mathlib
import Submission.Work.RelatorRank.API

/-!
# `Work.RelatorRank.Instance.abstractRelatorHalfOf_elementaryAbelian`

**Namespace** `Work.RelatorRank.Instance`; module
`Submission.Work.RelatorRank.Instance.abstractRelatorHalfOf_elementaryAbelian`.

The elementary abelian `2`-group `G = (ℤ/2)^d = (Fin d → Multiplicative (ZMod 2))` satisfies the
*abstract* (topology-free, presentation-independent) relation bound

`AbstractRelatorHalfOf G d (d + d * (d - 1) / 2)`,

i.e. **every** generating `d`-family `gen` of `G` admits a relator set of at most
`d + d(d-1)/2` elements presenting `G` on `gen`.

This is the sanity instance of the chapter: it shows that `AbstractRelatorHalfOf` is *not* an
empty predicate, and it exhibits the mechanism by which a `∀ gen`-statement can be true even
though the minimal relator count is a presentation invariant (`r = dim H²(G) = d + d(d-1)/2` here
-- the presentation of choice is the standard one, `x_i²` and `[x_i, x_j]`).

The mathematics: the images of the free generators in `F ⧸ N` (where `N` is the normal closure of
the `d` squares and the `d(d-1)/2` commutators) are commuting involutions generating that group,
so every element of `F ⧸ N` is a product over a subset of the generators -- in particular `F ⧸ N`
is a quotient of `(ℤ/2)^d`, and the explicit map `stdMap : (ℤ/2)^d →* F ⧸ N` constructed here (from
the universal property of a product of cyclic groups of order two, `MonoidHom.noncommPiCoprod`) has
this quotient property.  The composite `F ⧸ N → G` (induced by `FreeGroup.lift gen`, since
`N ≤ ker`) is surjective; the composite `G → F ⧸ N → G` is a surjective endomorphism of the finite
group `G`, hence injective, which forces both composites to be injective and `ker (FreeGroup.lift
gen) = N`.

## Main result

* `abstractRelatorHalfOf_elementaryAbelian`
-/

open scoped commutatorElement

namespace Work.RelatorRank.Instance

open Work.RelatorRank

/-! ## Elements of `Multiplicative (ZMod 2)` -/

/-- In `ZMod 2` every element is `0` or `1`. -/
theorem zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h : (x.val : ZMod 2) = x := ZMod.natCast_zmod_val x
  have h2 : x.val < 2 := ZMod.val_lt x
  interval_cases h3 : x.val
  · left; rw [← h]; simp
  · right; rw [← h]; simp

/-- `ZMod 2` has characteristic two. -/
theorem zmod_two_add_self (x : ZMod 2) : x + x = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  calc x + x = 2 * x := by rw [two_mul]
    _ = 0 := by rw [h, zero_mul]

/-! ## The cyclic group of order two mapping a two-torsion element -/

/-- **The homomorphism `ℤ/2 →* A` determined by a two-torsion element.**  Given `x : A` with
`x ^ 2 = 1`, the unique homomorphism `Multiplicative (ZMod 2) →* A` sending the non-identity
element `ofAdd 1` to `x`. -/
noncomputable def cycHom {A : Type*} [Group A] (x : A) (hx : x ^ 2 = 1) :
    Multiplicative (ZMod 2) →* A where
  toFun y := if y = 1 then 1 else x
  map_one' := by simp
  map_mul' y z := by
    by_cases hy : y = 1
    · subst hy; simp
    by_cases hz : z = 1
    · subst hz; simp
    have hy1 : y.toAdd = 1 := by
      rcases zmod_two_eq_zero_or_one y.toAdd with h | h
      · exact absurd (toAdd_eq_zero.mp h) hy
      · exact h
    have hz1 : z.toAdd = 1 := by
      rcases zmod_two_eq_zero_or_one z.toAdd with h | h
      · exact absurd (toAdd_eq_zero.mp h) hz
      · exact h
    have hyz : y * z = 1 := by
      rw [← toAdd_eq_zero, toAdd_mul, hy1, hz1, zmod_two_add_self]
    simp only [hy, hz, hyz, ite_true, ite_false]
    simpa [pow_two] using hx.symm

/-- The values of `cycHom x hx` are `1` and `x`. -/
theorem cycHom_eq_one_or {A : Type*} [Group A] (x : A) (hx : x ^ 2 = 1)
    (y : Multiplicative (ZMod 2)) : cycHom x hx y = 1 ∨ cycHom x hx y = x := by
  by_cases h : y = 1
  · left; simp [cycHom, h]
  · right; simp [cycHom, h]

@[simp]
theorem cycHom_apply_one {A : Type*} [Group A] (x : A) (hx : x ^ 2 = 1) :
    cycHom x hx 1 = 1 := map_one _

/-- `cycHom` sends the non-identity element to `x`. -/
@[simp]
theorem cycHom_ofAdd_one {A : Type*} [Group A] (x : A) (hx : x ^ 2 = 1) :
    cycHom x hx (Multiplicative.ofAdd 1) = x := by
  simp [cycHom]

/-- Two such homomorphisms have commuting images as soon as the two-torsion elements commute. -/
theorem cycHom_commute {A : Type*} [Group A] {x y : A} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hxy : Commute x y) (a b : Multiplicative (ZMod 2)) :
    Commute (cycHom x hx a) (cycHom y hy b) := by
  by_cases ha : a = 1
  · rw [ha, cycHom_apply_one]
    exact Commute.one_left _
  by_cases hb : b = 1
  · rw [hb, cycHom_apply_one]
    exact Commute.one_right _
  · rw [show cycHom x hx a = x from by simp [cycHom, ha],
        show cycHom y hy b = y from by simp [cycHom, hb]]
    exact hxy

/-! ## The standard relator set of `(ℤ/2)^d` -/

/-- **The standard relators of the elementary abelian `2`-group of rank `d`**: the `d` squares
`x_i²` and the `d(d-1)/2` commutators `[x_i, x_j]` (`i < j`), viewed in the free group on
`Fin d` generators. -/
noncomputable def stdRelators (d : ℕ) : Finset (FreeGroup (Fin d)) := by
  classical
  exact ((Finset.univ : Finset (Fin d)).image (fun i => FreeGroup.of i ^ 2)) ∪
    (((Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.1 < p.2)).image
      (fun p => ⁅FreeGroup.of p.1, FreeGroup.of p.2⁆))

/-- The standard relator set has at most `d + d * (d - 1) / 2` elements. -/
theorem stdRelators_card_le (d : ℕ) : (stdRelators d).card ≤ d + d * (d - 1) / 2 := by
  classical
  have h1 : ((Finset.univ : Finset (Fin d)).image (fun i => FreeGroup.of i ^ 2)).card ≤ d := by
    calc _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_image_le
      _ = d := by simp
  have h2 : ((((Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.1 < p.2)).image
      (fun p => ⁅FreeGroup.of p.1, FreeGroup.of p.2⁆))).card ≤ d * (d - 1) / 2 := by
    calc _ ≤ ((Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.1 < p.2)).card :=
          Finset.card_image_le
      _ = d * (d - 1) / 2 := by rw [Fintype.card_product_filter_lt, Nat.choose_two_right]; simp
  calc (stdRelators d).card ≤ _ + _ := Finset.card_union_le _ _
    _ ≤ d + d * (d - 1) / 2 := by omega

/-- The normal closure of the standard relators in the free group on `Fin d` generators. -/
def stdSubgroup (d : ℕ) : Subgroup (FreeGroup (Fin d)) :=
  Subgroup.normalClosure ((stdRelators d : Finset (FreeGroup (Fin d))) : Set (FreeGroup (Fin d)))

instance stdSubgroup_normal (d : ℕ) : (stdSubgroup d).Normal := Subgroup.normalClosure_normal

/-- The images of the free generators in `FreeGroup (Fin d) ⧸ stdSubgroup d`. -/
noncomputable def stdGen (d : ℕ) : Fin d → (FreeGroup (Fin d) ⧸ stdSubgroup d) :=
  fun i => QuotientGroup.mk' (stdSubgroup d) (FreeGroup.of i)

theorem of_pow_mem_stdRelators (d : ℕ) (i : Fin d) :
    FreeGroup.of i ^ 2 ∈ stdRelators d := by
  classical
  show _ ∈ ((Finset.univ : Finset (Fin d)).image (fun i => FreeGroup.of i ^ 2)) ∪ _
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

theorem commutator_mem_stdRelators (d : ℕ) {i j : Fin d} (h : i < j) :
    ⁅FreeGroup.of i, FreeGroup.of j⁆ ∈ stdRelators d := by
  classical
  show _ ∈ ((Finset.univ : Finset (Fin d)).image (fun i => FreeGroup.of i ^ 2)) ∪ _
  exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
    ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩))

/-- The images of the free generators generate `FreeGroup (Fin d) ⧸ stdSubgroup d`. -/
theorem closure_range_stdGen (d : ℕ) : Subgroup.closure (Set.range (stdGen d)) = ⊤ := by
  have hmap : Subgroup.map (QuotientGroup.mk' (stdSubgroup d))
      (Subgroup.closure (Set.range (FreeGroup.of : Fin d → FreeGroup (Fin d))))
      = Subgroup.closure (Set.range (stdGen d)) := by
    rw [MonoidHom.map_closure]
    congr 1
    exact (Set.range_comp _ _).symm
  rw [← hmap, FreeGroup.closure_range_of,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (stdSubgroup d))]

/-- The images of the free generators are two-torsion. -/
theorem stdGen_pow (d : ℕ) (i : Fin d) : (stdGen d i) ^ 2 = 1 := by
  have h : (QuotientGroup.mk' (stdSubgroup d)) (FreeGroup.of i ^ 2) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.subset_normalClosure (of_pow_mem_stdRelators d i)
  simpa only [map_pow, stdGen] using h

/-- The images of the free generators in `FreeGroup (Fin d) ⧸ stdSubgroup d` commute. -/
theorem stdGen_commute (d : ℕ) (i j : Fin d) : Commute (stdGen d i) (stdGen d j) := by
  rcases eq_or_ne i j with rfl | hij
  · exact Commute.refl _
  · have hmem : ⁅FreeGroup.of i, FreeGroup.of j⁆ ∈ stdSubgroup d := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact Subgroup.subset_normalClosure (commutator_mem_stdRelators d h)
      · have h' : ⁅FreeGroup.of j, FreeGroup.of i⁆ ∈ stdSubgroup d :=
          Subgroup.subset_normalClosure (commutator_mem_stdRelators d h)
        rw [← commutatorElement_inv]
        exact (stdSubgroup d).inv_mem h'
    have h1 : ⁅stdGen d i, stdGen d j⁆ = 1 := by
      have h2 : ⁅stdGen d i, stdGen d j⁆
          = (QuotientGroup.mk' (stdSubgroup d)) ⁅FreeGroup.of i, FreeGroup.of j⁆ := by
        simp only [stdGen]
        exact (map_commutatorElement _ _ _).symm
      rw [h2, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hmem
    exact commutatorElement_eq_one_iff_commute.mp h1

/-! ## The quotient map `(ℤ/2)^d →* FreeGroup (Fin d) ⧸ stdSubgroup d` -/

theorem stdMap_hcomm (d : ℕ) : Pairwise fun i j => ∀ a b : Multiplicative (ZMod 2),
    Commute (cycHom (stdGen d i) (stdGen_pow d i) a) (cycHom (stdGen d j) (stdGen_pow d j) b) :=
  fun i j _ a b => cycHom_commute (stdGen_pow d i) (stdGen_pow d j) (stdGen_commute d i j) a b

/-- **The canonical map `(ℤ/2)^d →* FreeGroup (Fin d) ⧸ stdSubgroup d`** sending the `i`-th
standard basis vector to the image of the `i`-th free generator.  It exists because those images
are commuting involutions. -/
noncomputable def stdMap (d : ℕ) :
    (Fin d → Multiplicative (ZMod 2)) →* (FreeGroup (Fin d) ⧸ stdSubgroup d) :=
  MonoidHom.noncommPiCoprod (fun i => cycHom (stdGen d i) (stdGen_pow d i)) (stdMap_hcomm d)

theorem stdMap_mulSingle (d : ℕ) (i : Fin d) :
    stdMap d (Pi.mulSingle i (Multiplicative.ofAdd 1)) = stdGen d i := by
  rw [show (stdMap d) (Pi.mulSingle i (Multiplicative.ofAdd 1)) =
      MonoidHom.noncommPiCoprod (fun i => cycHom (stdGen d i) (stdGen_pow d i)) (stdMap_hcomm d)
        (Pi.mulSingle i (Multiplicative.ofAdd 1)) from rfl]
  rw [MonoidHom.noncommPiCoprod_mulSingle, cycHom_ofAdd_one]

/-- `stdMap` is surjective: its image contains the generators of `FreeGroup (Fin d) ⧸
stdSubgroup d`. -/
theorem stdMap_surjective (d : ℕ) : Function.Surjective (stdMap d) := by
  rw [← MonoidHom.range_eq_top]
  have hle : Subgroup.closure (Set.range (stdGen d)) ≤ (stdMap d).range := by
    rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    exact ⟨Pi.mulSingle i (Multiplicative.ofAdd 1), stdMap_mulSingle d i⟩
  rw [closure_range_stdGen] at hle
  exact top_le_iff.mp hle

/-! ## The instance -/

theorem abstractRelatorHalfOf_elementaryAbelian (d : ℕ) :
    AbstractRelatorHalfOf (Fin d → Multiplicative (ZMod 2)) d (d + d * (d - 1) / 2) := by
  classical
  intro gen hgen
  refine ⟨stdRelators d, stdRelators_card_le d, ?_⟩
  have hsq : ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1 := by
    intro x
    rw [← toAdd_eq_zero, toAdd_pow, two_nsmul, zmod_two_add_self]
  have hsqG : ∀ y : (Fin d → Multiplicative (ZMod 2)), y ^ 2 = 1 := by
    intro y
    funext j
    simpa using hsq (y j)
  have hNK : stdSubgroup d ≤ (FreeGroup.lift gen).ker := by
    refine Subgroup.normalClosure_le_normal ?_
    intro x hx
    have hx₁ : x ∈ stdRelators d := Finset.mem_coe.mp hx
    have hx₂ : x ∈ ((Finset.univ : Finset (Fin d)).image (fun i => FreeGroup.of i ^ 2)) ∪
        (((Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.1 < p.2)).image
          (fun p => ⁅FreeGroup.of p.1, FreeGroup.of p.2⁆)) := by
      simpa only [stdRelators] using hx₁
    rw [Finset.mem_union] at hx₂
    rcases hx₂ with hx₂ | hx₂
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx₂
      show FreeGroup.of i ^ 2 ∈ (FreeGroup.lift gen).ker
      rw [MonoidHom.mem_ker, map_pow, FreeGroup.lift_apply_of]
      exact hsqG (gen i)
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx₂
      show ⁅FreeGroup.of p.1, FreeGroup.of p.2⁆ ∈ (FreeGroup.lift gen).ker
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  let q := QuotientGroup.mk' (stdSubgroup d)
  let fbar : (FreeGroup (Fin d) ⧸ stdSubgroup d) →* (Fin d → Multiplicative (ZMod 2)) :=
    QuotientGroup.lift (stdSubgroup d) (FreeGroup.lift gen) hNK
  have hfbar_q : ∀ w : FreeGroup (Fin d), fbar (q w) = FreeGroup.lift gen w := fun w =>
    QuotientGroup.lift_mk' (stdSubgroup d) hNK w
  have hfbar_surj : Function.Surjective fbar := by
    intro y
    have hlift : Function.Surjective (FreeGroup.lift gen) :=
      FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr hgen
    obtain ⟨w, hw⟩ := hlift y
    exact ⟨q w, by rw [hfbar_q w, hw]⟩
  have hT_inj : Function.Injective (fbar.comp (stdMap d)) :=
    (hfbar_surj.comp (stdMap_surjective d)).injective_of_finite (Equiv.refl _)
  have hfbar_inj : Function.Injective fbar := by
    intro u v huv
    obtain ⟨x, rfl⟩ := stdMap_surjective d u
    obtain ⟨y, rfl⟩ := stdMap_surjective d v
    have hxy : (fbar.comp (stdMap d)) x = (fbar.comp (stdMap d)) y := by
      simp only [MonoidHom.coe_comp, Function.comp_apply, huv]
    exact congrArg (stdMap d) (hT_inj hxy)
  have hKN : (FreeGroup.lift gen).ker ≤ stdSubgroup d := by
    intro w hw
    have h1 : fbar (q w) = 1 := by rw [hfbar_q w, hw]
    have h2 : q w = 1 := hfbar_inj (by rw [h1, map_one])
    have h3 : w ∈ (QuotientGroup.mk' (stdSubgroup d)).ker := MonoidHom.mem_ker.mpr h2
    rwa [QuotientGroup.ker_mk' (stdSubgroup d)] at h3
  exact le_antisymm hKN hNK

end Work.RelatorRank.Instance
