/-
Area DSCOH — the boundary of a prescribed family of chart coordinates.

This file contains the construction used by `Work.DSCOH.exists_boundary_of_coeffs`: given a family
`N` of coefficients, indexed by a Laurent exponent `β` and a chart `U` containing `Zset β`, whose
support in `β` is contained in a finite set `F` (and whose exponents all have total degree `-d`),
it builds the Čech cochain `b` of `S(-d)` whose `U`-component is the sum
`∑_{β ∈ F, Zset β ⊆ U} N β ⟨U, _⟩ • B U β` in the monomial basis, and computes the coordinates of
`b` and of `cechDiff b`.
-/
import Mathlib
import Submission.Work.DSCOH.coordToolkit
import Submission.Work.DSCOH.Cech

open MvPolynomial Module

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ} {d : ℕ} {q : ℕ}

/-- The chart indices of the chart `U` whose Laurent exponent lies in the finite set `F`. -/
noncomputable def tSetEmb (F : Finset (Fin n → ℤ)) (U : Finset (Fin n)) :
    ↥(F.filter (fun β => ∀ i, i ∉ U → 0 ≤ β i)) ↪
      {β : Fin n → ℤ // ∀ i, i ∉ U → 0 ≤ β i} :=
  { toFun := fun v => ⟨v.1, (Finset.mem_filter.mp v.2).2⟩
    inj' := fun _ _ h =>
      Subtype.ext (congrArg (fun x : {β : Fin n → ℤ // ∀ i, i ∉ U → 0 ≤ β i} => x.1) h) }

/-- The Finset of monomial-basis indices of the chart `U` whose exponent lies in `F`. -/
noncomputable def tSet (F : Finset (Fin n → ℤ)) (U : Finset (Fin n)) :
    Finset {β : Fin n → ℤ // ∀ i, i ∉ U → 0 ≤ β i} :=
  (F.filter (fun β => ∀ i, i ∉ U → 0 ≤ β i)).attach.map (tSetEmb F U)

lemma mem_tSet {F : Finset (Fin n → ℤ)} {U : Finset (Fin n)}
    {w : {β : Fin n → ℤ // ∀ i, i ∉ U → 0 ≤ β i}} :
    w ∈ tSet F U ↔ w.1 ∈ F := by
  unfold tSet
  rw [Finset.mem_map]
  constructor
  · rintro ⟨v, _, hvw⟩
    simp only [tSetEmb] at hvw
    rw [← Subtype.ext_iff.mp hvw]
    exact (Finset.mem_filter.mp v.2).1
  · intro hw
    exact ⟨⟨w.1, Finset.mem_filter.mpr ⟨hw, w.2⟩⟩, Finset.mem_attach _ _, by
      simp only [tSetEmb]; exact Subtype.ext rfl⟩

/-- The coefficient attached to the monomial basis index `w` of the chart `U`: `N w` if `w` occurs
in `F`, and `0` otherwise. -/
noncomputable def bCoef
    (N : (β : Fin n → ℤ) → {U : Finset (Fin n) // Zset β ⊆ U ∧ U.card + 1 = q + 2} → A)
    (F : Finset (Fin n → ℤ)) (U : Finset (Fin n)) (hc : U.card + 1 = q + 2)
    (w : {β : Fin n → ℤ // ∀ i, i ∉ U → 0 ≤ β i}) : A :=
  if h : w.1 ∈ F then N w.1 ⟨U, (Zset_subset_iff U w.1).mpr w.2, hc⟩ else 0

/-- The underlying element of the `U`-component of the constructed Čech cochain. -/
noncomputable def bLoc
    (B : (S : Finset (Fin n)) →
      Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))
    (N : (β : Fin n → ℤ) → {U : Finset (Fin n) // Zset β ⊆ U ∧ U.card + 1 = q + 2} → A)
    (F : Finset (Fin n → ℤ)) (U : Finset (Fin n)) (hc : U.card + 1 = q + 2) :
    locAt (A := A) (M := Poly A n) U :=
  ∑ w ∈ tSet F U, bCoef N F U hc w • B U w

/-- The coordinates of `bLoc` in the monomial basis. -/
lemma bLoc_repr
    (B : (S : Finset (Fin n)) →
      Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))
    (N : (β : Fin n → ℤ) → {U : Finset (Fin n) // Zset β ⊆ U ∧ U.card + 1 = q + 2} → A)
    (F : Finset (Fin n → ℤ)) (U : Finset (Fin n)) (hc : U.card + 1 = q + 2)
    (w : {β : Fin n → ℤ // ∀ i, i ∉ U → 0 ≤ β i}) :
    ((B U).repr (bLoc B N F U hc)) w = bCoef N F U hc w := by
  rw [bLoc]
  have h1 : (B U).repr (∑ w ∈ tSet F U, bCoef N F U hc w • B U w)
      = ∑ w ∈ tSet F U, Finsupp.single w (bCoef N F U hc w) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_smul, Basis.repr_self, Finsupp.smul_single]
    simp
  rw [h1, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq']
  by_cases hw : w.1 ∈ F
  · rw [if_pos (mem_tSet.mpr hw)]
  · rw [if_neg (fun h => hw (mem_tSet.mp h)), bCoef, dif_neg hw]

/-- `bLoc` lies in the degree-zero part of the chart localization. -/
lemma bLoc_mem
    (B : (S : Finset (Fin n)) →
      Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))
    (N : (β : Fin n → ℤ) → {U : Finset (Fin n) // Zset β ⊆ U ∧ U.card + 1 = q + 2} → A)
    (F : Finset (Fin n → ℤ))
    (hB3 : ∀ (S : Finset (Fin n)),
      degZero (A := A) (M := Poly A n) (shift (A := A) (n := n) d) S =
        Submodule.span A {y | ∃ β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i},
          (∑ i, β.1 i) = -(d : ℤ) ∧ y = B S β})
    (hNdeg : ∀ (β : Fin n → ℤ), β ∈ F → (∑ i, β i) = -(d : ℤ))
    (U : Finset (Fin n)) (hc : U.card + 1 = q + 2) :
    bLoc B N F U hc ∈ degZero (A := A) (M := Poly A n) (shift (A := A) (n := n) d) U := by
  rw [hB3 U]
  rw [bLoc]
  refine Submodule.sum_mem _ (fun w hw => ?_)
  refine Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨w, hNdeg w.1 (mem_tSet.mp hw), rfl⟩

/-- The Čech cochain of `S(-d)` whose chart coordinates are prescribed by `N`. -/
noncomputable def bCech
    (B : (S : Finset (Fin n)) →
      Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))
    (N : (β : Fin n → ℤ) → {U : Finset (Fin n) // Zset β ⊆ U ∧ U.card + 1 = q + 2} → A)
    (F : Finset (Fin n → ℤ))
    (hB3 : ∀ (S : Finset (Fin n)),
      degZero (A := A) (M := Poly A n) (shift (A := A) (n := n) d) S =
        Submodule.span A {y | ∃ β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i},
          (∑ i, β.1 i) = -(d : ℤ) ∧ y = B S β})
    (hNdeg : ∀ (β : Fin n → ℤ), β ∈ F → (∑ i, β i) = -(d : ℤ)) :
    CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q :=
  fun S => ⟨bLoc B N F S.1 (by have := S.2; omega),
            bLoc_mem B N F hB3 hNdeg S.1 (by have := S.2; omega)⟩

/-- **The coordinates of the constructed cochain `bCech`.**  On a chart `U` of cardinality
`q + 1`, the `β`-coordinate of the `U`-component of `bCech` is `N β` if `β` occurs in `F`, and
vanishes otherwise by the support hypothesis `hN0`. -/
lemma bCech_coeff
    (B : (S : Finset (Fin n)) →
      Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))
    (N : (β : Fin n → ℤ) → {U : Finset (Fin n) // Zset β ⊆ U ∧ U.card + 1 = q + 2} → A)
    (F : Finset (Fin n → ℤ))
    (hB3 : ∀ (S : Finset (Fin n)),
      degZero (A := A) (M := Poly A n) (shift (A := A) (n := n) d) S =
        Submodule.span A {y | ∃ β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i},
          (∑ i, β.1 i) = -(d : ℤ) ∧ y = B S β})
    (hNdeg : ∀ (β : Fin n → ℤ), β ∈ F → (∑ i, β i) = -(d : ℤ))
    (hN0 : ∀ (β : Fin n → ℤ), β ∉ F →
      ∀ (U : Finset (Fin n)) (hU : Zset β ⊆ U) (hc : U.card + 1 = q + 2), N β ⟨U, hU, hc⟩ = 0)
    (U : Finset (Fin n)) (hU : U.card = q + 1) (β : Fin n → ℤ) (hβ : Zset β ⊆ U) :
    ((B U).repr
      (cechCoeff (bCech B N F hB3 hNdeg) U hU)) ⟨β, (Zset_subset_iff U β).mp hβ⟩ =
      N β ⟨U, hβ, by omega⟩ := by
  simp only [cechCoeff, bCech]
  rw [bLoc_repr]
  rw [bCoef]
  split_ifs with hβF
  · exact congrArg (N β) (Subtype.ext rfl)
  · exact (hN0 β hβF U hβ (by omega)).symm

/-- **The coordinates of the Čech differential of the constructed cochain.**  On a chart `T` of
cardinality `q + 2`, the `β`-coordinate of the `T`-component of `cechDiff bCech` is the alternating
sum over `i ∈ T` of `N β` at the chart `T \ {i}`, the term being dropped when `β` is not a
legitimate exponent there. -/
lemma diff_coeff_eq
    (B : (S : Finset (Fin n)) →
      Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))
    (hB2 : ∀ (S T : Finset (Fin n)) (h : S ⊆ T) (β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i}),
      resAt (M := Poly A n) h (B S β) = B T ⟨β.1, fun i hi => β.2 i (fun hmem => hi (h hmem))⟩)
    (N : (β : Fin n → ℤ) → {U : Finset (Fin n) // Zset β ⊆ U ∧ U.card + 1 = q + 2} → A)
    (F : Finset (Fin n → ℤ))
    (hB3 : ∀ (S : Finset (Fin n)),
      degZero (A := A) (M := Poly A n) (shift (A := A) (n := n) d) S =
        Submodule.span A {y | ∃ β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i},
          (∑ i, β.1 i) = -(d : ℤ) ∧ y = B S β})
    (hNdeg : ∀ (β : Fin n → ℤ), β ∈ F → (∑ i, β i) = -(d : ℤ))
    (hN0 : ∀ (β : Fin n → ℤ), β ∉ F →
      ∀ (U : Finset (Fin n)) (hU : Zset β ⊆ U) (hc : U.card + 1 = q + 2), N β ⟨U, hU, hc⟩ = 0)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)]
    (T : Finset (Fin n)) (hT : T.card = q + 1 + 1) (β : Fin n → ℤ) (hβ : Zset β ⊆ T) :
    ((B T).repr
      ((cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q
        (bCech B N F hB3 hNdeg)) ⟨T, hT⟩).1) ⟨β, (Zset_subset_iff T β).mp hβ⟩ =
      ∑ i ∈ T.attach, ((-1 : ℤ) ^ ((T.filter (fun x => x < i.1)).card)) •
        (if h : ∀ j, j ∉ T.erase i.1 → 0 ≤ β j
          then N β ⟨T.erase i.1, (Zset_subset_iff (T.erase i.1) β).mpr h, by
            rw [Finset.card_erase_of_mem i.2]; omega⟩
          else 0) := by
  rw [coord_cechDiff (B := B) (d := d) (hB2 := hB2) (q := q)
    (a := bCech B N F hB3 hNdeg) (T := ⟨T, hT⟩) (β := ⟨β, (Zset_subset_iff T β).mp hβ⟩)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  by_cases h : ∀ j, j ∉ T.erase i.1 → 0 ≤ β j
  · conv_lhs => rw [dite_eq_left h]
    conv_rhs => rw [dite_eq_left h]
    simp only [bCech]
    rw [bLoc_repr]
    rw [bCoef]
    split_ifs with hβF
    · exact congrArg (N β) (Subtype.ext rfl)
    · exact (hN0 β hβF (T.erase i.1) ((Zset_subset_iff (T.erase i.1) β).mpr h)
        (by have hmem : i.1 ∈ T := i.2
            rw [Finset.card_erase_of_mem hmem]
            have := hT; omega)).symm
  · conv_lhs => rw [dite_eq_right h]
    conv_rhs => rw [dite_eq_right h]

end Work.DSCOH
