import Mathlib
import Submission.Work.SSGRoute.CC.MagFourDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Surjectivity of `mag4` onto `Wsub`

`mag4 X z` is the mod-`2` degree-`4` component of the Magnus image of `z` at truncation `5`, and
`Wsub X` is the `𝔽₂`-span of the degree-`4` left-nested brackets `brk4 X (x, y, z, w)`.  This file
proves that `mag4` maps `γ₄ = lowerCentralSeries 3` onto `Wsub X`.

The proof has three ingredients, all proved here:

* the mod-`2` reduction of the left-nested bracket monomial `lnMon` of a word of length `4` is the
  `𝔽₂`-bracket `brk4 X` of the four letters (`red2_lnMon_four`), and `lnMon` of such a word is
  homogeneous of degree `4` (`lnMon_mem_wordSpan`);
* for `w = [x₁,x₂,x₃,x₄]` the left-nested *group* commutator `lc w` lies in `γ₄` and its Magnus
  leading term at truncation `5` equals the image of `lnMon w` (`magLead_lc_congr`, plus the fact
  that `filq X 5 5 = ⊥`);
* hence `mag4 X (lc w) = brk4 X (x₁,x₂,x₃,x₄)`, and the general statement follows from additivity
  of `mag4` on `γ₄` (`mag4_mul`) by a span induction.
-/

namespace Work.SSGRoute.CC

open Work.SSGRoute.prop5

open scoped commutatorElement

noncomputable section

variable {X : Type}

/-! ## The mod-`2` reduction of the left-nested bracket monomial -/

theorem red2_wordEl_single (X : Type) (y : X) :
    red2 X (wordEl [y]) = MonoidAlgebra.single (FreeMonoid.of y) (1 : ZMod 2) := by
  simp [wordEl]

/-- In characteristic `2`, `a - b = a + b`. -/
theorem sub_eq_add_charTwo {M : Type*} (a b : MonoidAlgebra (ZMod 2) M) : a - b = a + b := by
  rw [sub_eq_add_neg, neg_eq_self_zmodTwo]

/-- One step of the left-nested bracket fold, after reduction mod `2`. -/
theorem red2_mul_sub (X : Type) (a : FreeAssoc X) (y : X) :
    red2 X (a * wordEl [y] - wordEl [y] * a)
      = brk X (red2 X a) (MonoidAlgebra.single (FreeMonoid.of y) (1 : ZMod 2)) := by
  rw [map_sub, map_mul, map_mul, red2_wordEl_single, brk, sub_eq_add_charTwo]

/-- Reduction mod `2` converts the `ℤ`-fold `alFold` (bracketing with `A*B - B*A`) into the
`𝔽₂`-fold built from `brk`. -/
theorem red2_alFold (X : Type) (a : FreeAssoc X) (l : List X) :
    red2 X (alFold a l)
      = l.foldl (fun acc (y : X) =>
          brk X acc (MonoidAlgebra.single (FreeMonoid.of y) (1 : ZMod 2))) (red2 X a) := by
  induction l generalizing a with
  | nil => simp [alFold]
  | cons y l ih =>
      have h : alFold a (y :: l) = alFold (a * wordEl [y] - wordEl [y] * a) l := rfl
      rw [h, ih, red2_mul_sub, List.foldl_cons]

/-- `brk4` is the `brk`-fold over the last three letters. -/
theorem brk4_eq_fold (X : Type) (t : X × X × X × X) :
    brk4 X t = List.foldl (fun acc (y : X) =>
        brk X acc (MonoidAlgebra.single (FreeMonoid.of y) (1 : ZMod 2)))
      (MonoidAlgebra.single (FreeMonoid.of t.1) 1) [t.2.1, t.2.2.1, t.2.2.2] := by
  simp [brk4, brk, List.foldl_cons]

/-- The mod-`2` reduction of the degree-`4` left-nested bracket monomial is the `𝔽₂`-bracket
`brk4`. -/
theorem red2_lnMon_four (X : Type) (x1 x2 x3 x4 : X) :
    red2 X (lnMon [x1, x2, x3, x4]) = brk4 X (x1, x2, x3, x4) := by
  rw [show lnMon [x1, x2, x3, x4] = alFold (wordEl [x1]) [x2, x3, x4] from rfl,
    red2_alFold, brk4_eq_fold, red2_wordEl_single]

/-! ## Homogeneity of `lnMon` -/

/-- `alFold` preserves the word span, raising the degree by `l.length`. -/
theorem alFold_mem_wordSpan (X : Type) (a : FreeAssoc X) (l : List X) (p : ℕ)
    (ha : a ∈ wordSpan (X := X) p) : alFold a l ∈ wordSpan (X := X) (p + l.length) := by
  induction l generalizing a p with
  | nil => simpa [alFold] using ha
  | cons y l ih =>
      have h : alFold a (y :: l) = alFold (a * wordEl [y] - wordEl [y] * a) l := rfl
      rw [h, show p + (y :: l).length = (p + 1) + l.length from by
        simp only [List.length_cons]; omega]
      refine ih _ _ ?_
      have hy : wordEl [y] ∈ wordSpan (X := X) 1 := Submodule.subset_span ⟨[y], rfl, rfl⟩
      have h1 : a * wordEl [y] ∈ wordSpan (X := X) (p + 1) :=
        wordSpan_mul_mem (p := p) (q := 1) ha hy
      have h2 : wordEl [y] * a ∈ wordSpan (X := X) (p + 1) := by
        have := wordSpan_mul_mem (p := 1) (q := p) hy ha
        rwa [Nat.add_comm] at this
      exact Submodule.sub_mem _ h1 h2

/-- `lnMon` of a word of length `j` is homogeneous of degree `j`. -/
theorem lnMon_mem_wordSpan {X : Type} {w : List X} {j : ℕ} (hw : w.length = j) :
    lnMon w ∈ wordSpan (X := X) j := by
  cases w with
  | nil =>
      have hj : j = 0 := by simpa using hw.symm
      subst hj
      simp [lnMon]
  | cons x rest =>
      have h : lnMon (x :: rest) = alFold (wordEl [x]) rest := rfl
      rw [h]
      have h1 := alFold_mem_wordSpan (X := X) (wordEl [x]) rest 1
        (Submodule.subset_span ⟨[x], rfl, rfl⟩)
      rw [show 1 + rest.length = (x :: rest).length from by
        simp only [List.length_cons]; omega] at h1
      rwa [hw] at h1

/-! ## The left-nested group commutator -/

/-- `lc w` lies in `γ_{|w|}`. -/
theorem lc_mem_lowerCentralSeries {X : Type} {w : List X} (hw : 1 ≤ w.length) :
    lc w ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (w.length - 1) := by
  cases w with
  | nil => simp at hw
  | cons x rest =>
      rw [lc_eq_gpFold]
      have hmem := gpFold_mem (X := X) rest 1 le_rfl (u := FreeGroup.of x) (Subgroup.mem_top _)
      rw [show (x :: rest).length - 1 = 1 + rest.length - 1 from by
        simp only [List.length_cons]; omega]
      exact hmem

/-! ## `mag4` on the generators of `Wsub` -/

theorem mag4_one (X : Type) : mag4 X 1 = 0 := by
  rw [mag4, magLead_one]
  rw [show (0 : FreeAssoc X ⧸ fil X 5)
      = Ideal.Quotient.mk (fil X 5) (0 : FreeAssoc X) from (map_zero _).symm]
  rw [degq_mk (j := 4) (by norm_num) X]
  simp

/-- `mag4` of the left-nested commutator attached to a `4`-tuple is the corresponding generator of
`Wsub`. -/
theorem mag4_lc_tuple (X : Type) (t : X × X × X × X) :
    mag4 X (lc [t.1, t.2.1, t.2.2.1, t.2.2.2]) = brk4 X t := by
  obtain ⟨x1, x2, x3, x4⟩ := t
  have hlen : ([x1, x2, x3, x4] : List X).length = 4 := rfl
  have h1 : Ideal.Quotient.mk (fil X 5) (lnMon [x1, x2, x3, x4])
      = magLead (X := X) 5 (lc [x1, x2, x3, x4]) := by
    have h := magLead_lc_congr (X := X) 5 (w := [x1, x2, x3, x4]) (by simp) (by simp)
    rw [show ([x1, x2, x3, x4] : List X).length + 1 = 5 from rfl] at h
    exact (sub_eq_zero.mp (mem_filq_self_eq_zero' h)).symm
  rw [mag4_eq_of_mk (X := X) h1,
    degPart_eq_self_of_mem_wordSpan (X := X) (lnMon_mem_wordSpan (X := X) hlen),
    red2_lnMon_four]

/-! ## The two elements of `ZMod 2` -/

/-- Every element of `ZMod 2` is `0` or `1`. -/
theorem zmodTwo_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  have h : c.val < 2 := ZMod.val_lt c
  have h2 : c.val = 0 ∨ c.val = 1 := by interval_cases c.val <;> simp
  rcases h2 with h0 | h1
  · left; rw [← ZMod.natCast_zmod_val c, h0]; simp
  · right; rw [← ZMod.natCast_zmod_val c, h1]; simp

/-! ## The main statement -/

/-- **Surjectivity of `mag4` onto `Wsub`.**

`mag4 X z` (defined in `Submission/Work/SSGRoute/magFourDefs.lean`) is the mod-`2` degree-`4`
component of the Magnus image of `z` at truncation `5`.  Every element of `Wsub X` — the `𝔽₂`-span
of the degree-`4` left-nested brackets `brk4 X (x, y, z, w)` — is `mag4 X z` for some
`z ∈ γ₄ = lowerCentralSeries 3`.

Proof route: for a list `w = [x1,x2,x3,x4]` of length `4`, put `z := prop5.lc w`, the left-nested
group commutator `⁅⁅⁅of x1, of x2⁆, of x3⁆, of x4⁆`.  Then `z ∈ γ₄`, and
`prop5.magLead_lc_congr 5 (by simp) (by simp)` gives `magLead 5 (lc w) = mk (lnMon w)` (the
difference lies in `filq X 5 5 = ⊥`), so `mag4 X (lc w) = red2 X (degPart 4 (lnMon w)) =
red2 X (lnMon w) = brk4 X (x1,x2,x3,x4)` (homogeneity of `lnMon` in degree `4`, and
`A * B - B * A` vs `A * B + B * A` over `ZMod 2`).  A general `w ∈ Wsub X` is a finite `𝔽₂`-sum
of such `brk4`s; take the product of the corresponding `lc w`'s in `FreeGroup X` and use
additivity of `mag4` on `γ₄` (`mag4_mul`). -/
theorem mag4_surjective {X : Type} {w : MonoidAlgebra (ZMod 2) (FreeMonoid X)}
    (hw : w ∈ Wsub X) :
    ∃ z : FreeGroup X, z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3 ∧ mag4 X z = w := by
  have hw' : w ∈ Submodule.span (ZMod 2) (Set.range (brk4 X)) := hw
  refine Submodule.span_induction (p := fun v _ => ∃ z : FreeGroup X,
      z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 3 ∧ mag4 X z = v) ?_ ?_ ?_ ?_ hw'
  · rintro v ⟨t, rfl⟩
    refine ⟨lc [t.1, t.2.1, t.2.2.1, t.2.2.2], ?_, mag4_lc_tuple X t⟩
    have hmem := lc_mem_lowerCentralSeries (X := X)
      (w := [t.1, t.2.1, t.2.2.1, t.2.2.2]) (by simp)
    rwa [show ([t.1, t.2.1, t.2.2.1, t.2.2.2] : List X).length - 1 = 3 from rfl] at hmem
  · exact ⟨1, Subgroup.one_mem _, mag4_one X⟩
  · rintro v₁ v₂ _ _ ⟨z₁, h₁, e₁⟩ ⟨z₂, h₂, e₂⟩
    exact ⟨z₁ * z₂, Subgroup.mul_mem _ h₁ h₂, by rw [mag4_mul h₁ h₂, e₁, e₂]⟩
  · rintro c v _ ⟨z, h, e⟩
    have hc : c = 0 ∨ c = 1 := zmodTwo_eq_zero_or_one c
    rcases hc with rfl | rfl
    · exact ⟨1, Subgroup.one_mem _, by rw [zero_smul, mag4_one]⟩
    · exact ⟨z, h, by rw [one_smul, e]⟩

end

end Work.SSGRoute.CC
