/-
# Decomposition of `Kset E t` along a commuting direct decomposition `E = S × T`

Peterfalvi I Ch. III §4 (`Setup45A`) uses the following elementary fact about the set
`Kset X t = {x ∈ X | t * x * t⁻¹ = x⁻¹}`: if `E = S ⊔ T` with `S ⊓ T = ⊥` and `S`, `T` elementwise
commuting, and `t` normalises both factors, then `Kset E t` is the *direct* product
`Kset S t · Kset T t`, so that `|Kset E t| = |Kset S t| · |Kset T t|`.  Moreover, if the factor
`Kset T t` consists of elements centralising a subgroup `Q`, then the elements of `Kset E t` that
centralise `Q` are exactly the products `s * u` with `s ∈ Kset S t` centralising `Q` and
`u ∈ Kset T t`, whence `|Kset E t ∩ C_G(Q)| = |Kset S t ∩ C_G(Q)| · |Kset T t|`.

The work splits into

* `kset_sup_eq` — `Kset E t` is exactly the set of such products (uses that `t` inverts both
  factors, and that the product of two commuting inverted elements is inverted);
* `ncard_mul_decomp` — since `S ⊓ T = ⊥` the product map `Kset S t × Kset T t → Kset E t` is
  bijective (`mul_eq_mul_unique`), so it multiplies cardinalities.

This file assembles them into `kset_decomp`.
-/
import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.NC4.ncard_mul_decomp
import Submission.Work.NormalComplement.NC4.kset_sup_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.NC4

theorem kset_decomp {G : Type} [Group G] [Finite G] {t : G} {E S T Q : Subgroup G}
    (hS : S ≤ E) (hT : T ≤ E) (hsup : S ⊔ T = E) (hinf : S ⊓ T = ⊥)
    (hcomm : ∀ s ∈ S, ∀ u ∈ T, s * u = u * s)
    (htS : Work.NormalComplement.NormalizedBy t S)
    (htT : Work.NormalComplement.NormalizedBy t T)
    (hQT : Work.NormalComplement.Kset T t ⊆ (Subgroup.centralizer (Q : Set G) : Set G)) :
    (Work.NormalComplement.Kset E t).ncard = (Work.NormalComplement.Kset S t).ncard *
        (Work.NormalComplement.Kset T t).ncard ∧
      (∀ z ∈ Work.NormalComplement.Kset E t, ∃ s ∈ Work.NormalComplement.Kset S t,
        ∃ u ∈ Work.NormalComplement.Kset T t, z = s * u) ∧
      (∀ s ∈ Work.NormalComplement.Kset S t, ∀ u ∈ Work.NormalComplement.Kset T t,
        s * u ∈ Work.NormalComplement.Kset E t) ∧
      (Work.NormalComplement.Kset E t ∩ (Subgroup.centralizer (Q : Set G) : Set G)).ncard =
        (Work.NormalComplement.Kset S t ∩ (Subgroup.centralizer (Q : Set G) : Set G)).ncard *
          (Work.NormalComplement.Kset T t).ncard := by
  -- `Kset E t` is exactly the set of products of an element of `Kset S t` and one of `Kset T t`.
  have hE : Work.NormalComplement.Kset E t =
      {z : G | ∃ s ∈ Work.NormalComplement.Kset S t,
        ∃ u ∈ Work.NormalComplement.Kset T t, z = s * u} :=
    kset_sup_eq hS hT hsup hinf hcomm htS htT
  have hSK : Work.NormalComplement.Kset S t ⊆ S := fun _ hx => hx.1
  have hTK : Work.NormalComplement.Kset T t ⊆ T := fun _ hx => hx.1
  -- Both inclusions between `Kset E t` and the product set.
  have hmaps : ∀ s ∈ Work.NormalComplement.Kset S t, ∀ u ∈ Work.NormalComplement.Kset T t,
      s * u ∈ Work.NormalComplement.Kset E t := by
    intro s hs u hu
    rw [hE]
    exact ⟨s, hs, u, hu, rfl⟩
  have hdecomp : ∀ z ∈ Work.NormalComplement.Kset E t,
      ∃ s ∈ Work.NormalComplement.Kset S t, ∃ u ∈ Work.NormalComplement.Kset T t, z = s * u := by
    intro z hz
    rw [hE] at hz
    exact hz
  refine ⟨ncard_mul_decomp hinf hSK hTK hmaps hdecomp, hdecomp, hmaps, ?_⟩
  -- The centre of attention: the elements of `Kset E t` centralising `Q`.  Since `Kset T t`
  -- centralises `Q`, an element `s * u` (with `s ∈ Kset S t`, `u ∈ Kset T t`) centralises `Q`
  -- exactly when its `S`-part does.
  let C : Subgroup G := Subgroup.centralizer (Q : Set G)
  refine ncard_mul_decomp hinf (X := Work.NormalComplement.Kset S t ∩ (C : Set G))
    (Y := Work.NormalComplement.Kset T t) (Z := Work.NormalComplement.Kset E t ∩ (C : Set G))
    ?_ hTK ?_ ?_
  · rintro x ⟨hx, _⟩
    exact hx.1
  · rintro x ⟨hx, hxC⟩ y hy
    exact ⟨hmaps x hx y hy, C.mul_mem hxC (hQT hy)⟩
  · rintro z ⟨hz, hzC⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hdecomp z hz
    refine ⟨x, ⟨hx, ?_⟩, y, hy, hxy⟩
    have hx_eq : x = z * y⁻¹ := by rw [hxy]; group
    rw [hx_eq]
    exact C.mul_mem hzC (C.inv_mem (hQT hy))

end Work.NormalComplement.NC4
