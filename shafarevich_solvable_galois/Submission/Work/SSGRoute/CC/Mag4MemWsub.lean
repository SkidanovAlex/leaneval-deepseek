import Mathlib
import Submission.Work.SSGRoute.CC.MagFourDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.CC

/-!
# `mag4` of an element of `γ₄` is a degree-`4` Lie element

`mag4 X z` is the mod-`2` degree-`4` component of the Magnus image of `z` at truncation `5`; `Wsub X`
is the `𝔽₂`-span of the degree-`4` left-nested brackets `brk4 X (x, y, z, w) = [[[[x,y],z],w]]`
(with `brk a b = a*b + b*a`, the characteristic-`2` form of the ring commutator).

The proof assembles the following pieces.

* `prop5.magLead_mem_nestedImage` puts `magLead 5 z`, for `z ∈ γ₄`, in the image of the *integral*
  nested span `prop5.nestedSpan 4` (the `ℤ`-span of the left-nested bracket monomials
  `lnMon w = [[[[x₁,x₂],x₃],x₄]]`, `|w| = 4`, built with `a*b - b*a`), so that
  `mag4 X z = red2 X (degPart 4 a)` with `a ∈ prop5.nestedSpan 4`.
* Every `lnMon w` with `|w| = 4` is homogeneous of degree `4` (`lnMon_mem_wordSpan`,
  `alFold_mem_wordSpan`), so `degPart 4 a = a` (`degPart_four_eq_self_of_mem_nestedSpan`).
* `red2` is a ring homomorphism and `-1 = 1` in `ZMod 2`, so it turns the integral left-nested
  monomials into the mod-`2` left-nested brackets: `red2 X (lnMon [x,y,z,t]) = brk4 X (x,y,z,t)`
  (`red2_lnMon_four`).  Hence `red2` maps `nestedSpan 4` into `Wsub X`
  (`red2_mem_Wsub_of_mem_nestedSpan`).

The auxiliary lemmas are collected in the sub-namespace `Work.SSGRoute.mag4mem` so that this file
can be imported alongside the other `SSGRoute` files about `mag4` without name clashes.
-/

open scoped commutatorElement

noncomputable section

variable {X : Type}

namespace mag4mem

/-! ## `red2` and the integral left-nested monomials -/

/-- `red2` is a ring homomorphism, and `-1 = 1` in characteristic `2`, so `red2` converts the
integral ring commutator `a*b - b*a` into the mod-`2` bracket `brk`. -/
theorem red2_mul_sub_mul (a b : prop5.FreeAssoc X) :
    red2 X (a * b - b * a) = brk X (red2 X a) (red2 X b) := by
  rw [map_sub, map_mul, map_mul, brk, sub_eq_add_neg, neg_eq_self_zmodTwo]

/-- `red2` of the basis element attached to a single letter. -/
theorem red2_wordEl (x : X) :
    red2 X (prop5.wordEl [x]) = MonoidAlgebra.single (FreeMonoid.of x) (1 : ZMod 2) := by
  rw [prop5.wordEl, red2_single]
  simp

/-- The bracketing fold commutes with `red2`: the integral fold `[[·,x],y],…` (which uses
`a*b - b*a`) maps to the mod-`2` fold built from `brk`. -/
theorem red2_foldl_bracket (a : prop5.FreeAssoc X) (vs : List X) :
    red2 X (vs.foldl (fun acc y => acc * prop5.wordEl [y] - prop5.wordEl [y] * acc) a)
      = vs.foldl (fun acc y => brk X acc (MonoidAlgebra.single (FreeMonoid.of y) (1 : ZMod 2)))
          (red2 X a) := by
  induction vs generalizing a with
  | nil => rfl
  | cons y vs ih =>
      simp only [List.foldl_cons]
      rw [ih, red2_mul_sub_mul, red2_wordEl]

/-- **`red2` of a degree-`4` left-nested monomial is the corresponding bracket.** -/
theorem red2_lnMon_four (x y z t : X) :
    red2 X (prop5.lnMon [x, y, z, t]) = brk4 X (x, y, z, t) := by
  have h := red2_foldl_bracket (prop5.wordEl [x]) [y, z, t]
  rw [red2_wordEl] at h
  simp only [prop5.lnMon, brk4, brk, List.foldl_cons, List.foldl_nil] at h ⊢
  exact h

/-- `red2` is `ℤ`-linear, in the sense that a `ℤ`-multiple in `FreeAssoc X` becomes the
corresponding `ZMod 2`-multiple. -/
theorem red2_smul_int (c : ℤ) (x : prop5.FreeAssoc X) :
    red2 X (c • x) = (c : ZMod 2) • red2 X x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  exact RingHom.congr_fun (MonoidAlgebra.mapRingHom_comp_algebraMap (M := FreeMonoid X)
    (Int.castRingHom (ZMod 2))) c

/-! ## The integral left-nested monomials are homogeneous -/

/-- The algebra fold `alFold` preserves the "degree filtration" on the word span: folding a
`p`-homogeneous element by a list `vs` produces a `(p + |vs|)`-homogeneous element. -/
theorem alFold_mem_wordSpan (vs : List X) :
    ∀ {p : ℕ} {a : prop5.FreeAssoc X}, a ∈ prop5.wordSpan p →
      prop5.alFold a vs ∈ prop5.wordSpan (p + vs.length) := by
  induction vs with
  | nil => intro p a ha; simpa [prop5.alFold] using ha
  | cons y vs ih =>
      intro p a ha
      have hy : prop5.wordEl [y] ∈ prop5.wordSpan (1 : ℕ) :=
        Submodule.subset_span ⟨[y], rfl, rfl⟩
      have hstep : a * prop5.wordEl [y] - prop5.wordEl [y] * a ∈ prop5.wordSpan (p + 1) :=
        Submodule.sub_mem _
          (prop5.wordSpan_mul_mem ha hy)
          (by have h := prop5.wordSpan_mul_mem hy ha
              rwa [show (1 : ℕ) + p = p + 1 from by omega] at h)
      have h := ih (p := p + 1) hstep
      have hlen : (p + 1) + vs.length = p + (vs.length + 1) := by omega
      rw [hlen] at h
      rw [prop5.alFold, List.foldl_cons, List.length_cons]
      exact h

/-- **A left-nested bracket monomial is homogeneous of the length of its word.** -/
theorem lnMon_mem_wordSpan : ∀ w : List X,
    prop5.lnMon w ∈ prop5.wordSpan w.length := by
  intro w
  cases w with
  | nil => rw [prop5.lnMon]; exact Submodule.zero_mem _
  | cons x rest =>
      rw [prop5.lnMon_eq_alFold]
      have hy : prop5.wordEl [x] ∈ prop5.wordSpan (1 : ℕ) :=
        Submodule.subset_span ⟨[x], rfl, rfl⟩
      have h := alFold_mem_wordSpan rest hy
      have hlen : 1 + rest.length = rest.length + 1 := by omega
      rw [hlen] at h
      rw [List.length_cons]
      exact h

/-- The integral nested span of degree `j` consists of elements homogeneous of degree `j`. -/
theorem nestedSpan_le_wordSpan (j : ℕ) :
    prop5.nestedSpan (X := X) j ≤ prop5.wordSpan (X := X) j := by
  rw [prop5.nestedSpan]
  refine Submodule.span_le.mpr ?_
  rintro a ⟨w, hw, rfl⟩
  rw [← hw]
  exact lnMon_mem_wordSpan w

/-! ## The main reductions -/

/-- **`red2` maps the integral nested span of degree `4` into `Wsub X`.** -/
theorem red2_mem_Wsub_of_mem_nestedSpan {a : prop5.FreeAssoc X}
    (ha : a ∈ prop5.nestedSpan 4) : red2 X a ∈ Wsub X := by
  refine Submodule.span_induction (p := fun a _ => red2 X a ∈ Wsub X) ?_ ?_ ?_ ?_ ha
  · rintro a ⟨w, hw, rfl⟩
    obtain ⟨x, y, z, t, rfl⟩ := List.length_eq_four.mp hw
    rw [red2_lnMon_four]
    exact Submodule.subset_span ⟨(x, y, z, t), rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [red2_smul_int]; exact Submodule.smul_mem _ _ hx

/-- An element of the integral nested span of degree `4` is its own degree-`4` part. -/
theorem degPart_four_eq_self_of_mem_nestedSpan {a : prop5.FreeAssoc X}
    (ha : a ∈ prop5.nestedSpan 4) : prop5.degPart 4 a = a :=
  prop5.degPart_eq_self_of_mem_wordSpan (nestedSpan_le_wordSpan 4 ha)

end mag4mem

/-! ## The target -/

/-- **`mag4` of an element of `γ₄` is a degree-`4` Lie element.**

`mag4 X z` (defined in `Submission/Work/SSGRoute/magFourDefs.lean`) is the mod-`2` degree-`4`
component of the Magnus image of `z` at truncation `5`.  For `z ∈ γ₄ = lowerCentralSeries 3` it
lies in `Wsub X`, the `𝔽₂`-span of the degree-`4` left-nested brackets
`brk4 X (x, y, z, w) = [[[[x,y],z],w]]` (`free_lie_four_defs.lean`).

Proof route: `prop5.magLead_mem_nestedImage X 4 (by norm_num) z hz` gives
`∃ a ∈ prop5.nestedSpan 4, Ideal.Quotient.mk (fil X 5) a = magLead 5 z`.  Then
`mag4 X z = red2 X (degPart 4 a)` by `mag4_eq_of_mk`.  Every `lnMon w` with `w.length = 4` is
homogeneous of degree `4`, so `degPart 4 a = a` for `a ∈ nestedSpan 4`; and
`red2 X (lnMon w) = brk4 X (w[0], w[1], w[2], w[3])` because `red2` is a ring hom, `alFold` uses
`A * B - B * A` while `brk` uses `A * B + B * A`, and `-1 = 1` in `ZMod 2`. -/
theorem mag4_mem_Wsub {X : Type} {z : FreeGroup X}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3) :
    mag4 X z ∈ Wsub X := by
  obtain ⟨a, ha, haeq⟩ := prop5.magLead_mem_nestedImage X 4 (by norm_num) z hz
  rw [mag4_eq_of_mk haeq, mag4mem.degPart_four_eq_self_of_mem_nestedSpan ha]
  exact mag4mem.red2_mem_Wsub_of_mem_nestedSpan ha

end

end Work.SSGRoute.CC
