/-
Area DSCOH — the exactness of the chart Čech complex of the shifted free module `S(-d)`.

This is the main argument of `Work.DSCOH.chartCech_shift_vanishing`: the chart Čech complex of
`S(-d)` has no cohomology in the middle degrees.  It is assembled from

* the monomial basis of the chart localizations (`locAt_monomial_basis`),
* the simplex acyclicity for each Laurent piece (`simplex_cech_lift_level`),
* the cycle conditions read in coordinates (`cycle_piece_conditions`),
* the realisation of finitely supported coefficient families by Čech cochains
  (`exists_boundary_of_coeffs`),
* the vanishing of coordinates outside the relevant degree
  (`cechCoeff_coord_eq_zero_of_ne_deg`).

The statement itself takes the basis family `B` and its two compatibility properties as
hypotheses, so that this file is independent of the construction of the basis.
-/
import Mathlib
import Submission.Work.DSCOH.coordToolkit
import Submission.Work.DSCOH.Cech
import Submission.Work.DSCOH.Chart
import Submission.Work.DSCOH.shift_gradedSMul
import Submission.Work.DSCOH.shiftVanishingAux
import Submission.Work.DSCOH.dsCruxPieces
import Submission.Work.DSCOH.cycle_piece_conditions
import Submission.Work.DSCOH.cechCoeff_coord_eq_zero_of_ne_deg

open Module MvPolynomial

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ} {d : ℕ}

/-- The `β`-piece data of a Čech cochain at level `q + 1`: the `β`-coordinates of its components
at the charts of cardinality `q + 2` that contain `Z(β)`. -/
noncomputable def pieceCoeff {q : ℕ}
    (B : (S : Finset (Fin n)) →
      Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))
    (a : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) (q + 1))
    (β : Fin n → ℤ) (S : pieceChart β q) : A :=
  ((B S.1).repr (cechCoeff a S.1 (by have h := S.2.2; omega)))
    ⟨β, (Zset_subset_iff S.1 β).mp S.2.1⟩

/-- Two chart coordinates that differ only in the proofs of the index conditions agree. -/
lemma cechCoeff_coord_congr {r : ℕ}
    (B : (S : Finset (Fin n)) →
      Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))
    (a : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) r)
    {S : Finset (Fin n)} (h1 h2 : S.card = r + 1) {β : Fin n → ℤ}
    (e1 e2 : ∀ i, i ∉ S → 0 ≤ β i) :
    ((B S).repr (cechCoeff a S h1)) ⟨β, e1⟩ = ((B S).repr (cechCoeff a S h2)) ⟨β, e2⟩ :=
  rfl

/-- A Čech cochain is determined by its chart coordinates. -/
lemma cechTerm_ext {r : ℕ}
    (B : (S : Finset (Fin n)) →
      Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))
    {x y : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) r}
    (h : ∀ (S : {S : Finset (Fin n) // S.card = r + 1}) (β : Fin n → ℤ) (hβ : Zset β ⊆ S.1),
      ((B S.1).repr (x S).1) ⟨β, (Zset_subset_iff S.1 β).mp hβ⟩ =
        ((B S.1).repr (y S).1) ⟨β, (Zset_subset_iff S.1 β).mp hβ⟩) : x = y := by
  funext S
  apply Subtype.ext
  apply (B S.1).repr.injective
  apply Finsupp.ext
  intro β
  have hβeq : β = (⟨β.1, (Zset_subset_iff S.1 β.1).mp ((Zset_subset_iff S.1 β.1).mpr β.2)⟩ :
      {β : Fin n → ℤ // ∀ i, i ∉ S.1 → 0 ≤ β i}) := Subtype.ext rfl
  rw [hβeq]
  exact h S β.1 ((Zset_subset_iff S.1 β.1).mpr β.2)

/-- The cycle condition of a Čech cocycle at level `q + 1`, read in the piece data attached to
`β`: at every chart `T` of cardinality `q + 3` containing `Z(β)`, the alternating sum of the
`(T \ {i})`-coordinates of the piece data vanishes. -/
lemma pieceCoeff_cycle_zero {q : ℕ}
    (B : (S : Finset (Fin n)) →
      Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))
    (hB2 : ∀ (S T : Finset (Fin n)) (h : S ⊆ T)
      (β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i}),
      resAt (M := Poly A n) h (B S β) = B T ⟨β.1, fun i hi => β.2 i (fun hmem => hi (h hmem))⟩)
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)]
    (a : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) (q + 1))
    (ha : cechDiff (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) (q + 1) a = 0)
    (β : Fin n → ℤ) (T : Finset (Fin n)) (hZT : Zset β ⊆ T) (hcardT : T.card = q + 3) :
    (∑ i ∈ (T \ Zset β).attach,
      (((-1 : ℤ) ^ ((T.filter (fun x => x < i.1)).card)) •
        (pieceCoeff B a β) ⟨T.erase i.1,
          (fun j hj => Finset.mem_erase.mpr
            ⟨fun hji => (Finset.mem_sdiff.mp i.2).2 (hji ▸ hj), hZT hj⟩),
          (by rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp i.2).1]; omega)⟩)) = 0 := by
  have hcyc' := (cycle_piece_conditions (d := d) B hB2 q a ha).1 β T hZT hcardT
  have hpt : (∑ i ∈ (T \ Zset β).attach,
      (((-1 : ℤ) ^ ((T.filter (fun x => x < i.1)).card)) •
        (pieceCoeff B a β) ⟨T.erase i.1,
          (fun j hj => Finset.mem_erase.mpr
            ⟨fun hji => (Finset.mem_sdiff.mp i.2).2 (hji ▸ hj), hZT hj⟩),
          (by rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp i.2).1]; omega)⟩))
    = (∑ i ∈ (T \ Zset β).attach,
      (((-1 : ℤ) ^ ((T.filter (fun x => x < i.1)).card)) •
        ((B (T.erase i.1)).repr (cechCoeff a (T.erase i.1)
          (card_erase_of_mem' (Finset.mem_sdiff.mp i.2).1
            (by have h := hcardT; omega : T.card = q + 3))))
          ⟨β, Zset_index_erase hZT (Finset.mem_sdiff.mp i.2).1 (Finset.mem_sdiff.mp i.2).2⟩)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold pieceCoeff
    exact congrArg (fun x : A => (((-1 : ℤ) ^ ((T.filter (fun x => x < i.1)).card)) • x))
      (cechCoeff_coord_congr B a _ _ _ _)
  exact hpt.trans hcyc'

/-- **The chart Čech complex of `S(-d)` is exact in the middle degrees.**  For `q + 3 ≤ n`, the
`(q+1)`-st cohomology of the chart Čech complex of the shifted free module `S(-d)` vanishes, i.e.
every Čech cocycle in degree `q+1` is a coboundary. -/
theorem chartCechShift_exact (q : ℕ) (hqn : q + 3 ≤ n)
    (B : (S : Finset (Fin n)) →
      Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))
    (hB2 : ∀ (S T : Finset (Fin n)) (h : S ⊆ T)
      (β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i}),
      resAt (M := Poly A n) h (B S β) = B T ⟨β.1, fun i hi => β.2 i (fun hmem => hi (h hmem))⟩)
    (hB3 : ∀ (S : Finset (Fin n)),
      degZero (A := A) (M := Poly A n) (shift (A := A) (n := n) d) S =
        Submodule.span A {y | ∃ β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i},
          (∑ i, β.1 i) = -(d : ℤ) ∧ y = B S β})
    [SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d)] :
    LinearMap.range (cechDiff (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) d) q) =
      LinearMap.ker (cechDiff (A := A) (n := n) (M := Poly A n)
        (shift (A := A) (n := n) d) (q + 1)) := by
  classical
  refine le_antisymm ?_ ?_
  · rw [LinearMap.range_le_ker_iff]
    exact cechDiff_comp (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q
  · intro a ha
    rw [LinearMap.mem_range]
    have hcyc := cycle_piece_conditions (d := d) B hB2 q a ha
    set F : Finset (Fin n → ℤ) := pieceSupport (B := B) a with hF
    -- For every exponent `β`, the simplex acyclicity solves the `β`-piece of the complex.
    have hsol : ∀ β : Fin n → ℤ, ∃ S0 : pieceSol β q → A,
        ∀ (T : Finset (Fin n)) (hZT : Zset β ⊆ T) (hcardT : T.card = q + 2),
          (∑ i ∈ (T \ Zset β).attach,
            (((-1 : ℤ) ^ ((T.filter (fun x => x < i.1)).card)) •
              S0 ⟨T.erase i.1,
                (Zset_subset_iff (T.erase i.1) β).mpr
                  (Zset_index_erase hZT (Finset.mem_sdiff.mp i.2).1 (Finset.mem_sdiff.mp i.2).2),
                by rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp i.2).1]; omega⟩)) =
          pieceCoeff B a β ⟨T, hZT, hcardT⟩ := by
      intro β
      by_cases hcard : (Zset β).card + 1 ≤ q + 2
      · -- the piece has relative degree at least one: solve it by simplex acyclicity
        obtain ⟨L, hL⟩ := dsSimplexCechLiftLevel (A := A) (V := Fin n) (Zset β) (q + 2) hcard
        refine ⟨L (pieceCoeff B a β), ?_⟩
        intro T hZT hcardT
        have h0 := fun T' : {T' : Finset (Fin n) // Zset β ⊆ T' ∧ T'.card = q + 2 + 1} =>
          pieceCoeff_cycle_zero (d := d) B hB2 a ha β T'.1 T'.2.1
            (by have h := T'.2.2; omega : T'.1.card = q + 3)
        have hmain := hL (pieceCoeff B a β) h0 ⟨T, hZT, hcardT⟩
        rw [← hmain]
      · -- the piece has relative degree at most zero: it contributes nothing
        refine ⟨fun _ => 0, ?_⟩
        intro T hZT hcardT
        have hcardZ : (Zset β).card = q + 2 := by
          have h1 : (Zset β).card ≤ q + 2 := (Finset.card_le_card hZT).trans (le_of_eq hcardT)
          omega
        have hT : T = Zset β := (Finset.eq_of_subset_of_card_le hZT (by rw [hcardZ, hcardT])).symm
        subst hT
        simp only [smul_zero, Finset.sum_const_zero]
        exact (hcyc.2 β hcardZ hqn).symm
    choose sol hsol' using hsol
    -- The glued coefficient family: the piece solutions on the exponents occurring in `a`.
    set N : (β : Fin n → ℤ) → pieceSol β q → A :=
      (fun β U => if β ∈ F then sol β U else 0) with hN
    have hNapply : ∀ (β : Fin n → ℤ) (U : pieceSol β q), N β U = if β ∈ F then sol β U else 0 :=
      fun _ _ => rfl
    obtain ⟨b, hb1, hb2, hb3⟩ := dsExistsBoundaryOfCoeffs (d := d) q B hB2 hB3 N F
      (fun β hβ U hU hc => by
        show (if β ∈ F then sol β ⟨U, hU, hc⟩ else 0) = 0
        rw [if_neg hβ])
      (fun β hβ => by
        rw [hF] at hβ
        rw [mem_pieceSupport B a] at hβ
        obtain ⟨S, hβ', hne⟩ := hβ
        by_contra hcon
        exact hne (cechCoeff_coord_eq_zero_of_ne_deg (d := d) (q + 1) B hB3 a S.1 S.2 ⟨β, hβ'⟩ hcon))
    refine ⟨b, ?_⟩
    apply cechTerm_ext (d := d) B
    intro S β hβ
    have hZT : Zset β ⊆ S.1 := hβ
    have hcardT : S.1.card = q + 2 := by omega
    have key := hb3 S.1 S.2 β hZT
    -- the RHS of `key` is the sum of the glued coefficients
    have hsum : (∑ i ∈ (S.1 \ Zset β).attach,
        (((-1 : ℤ) ^ ((S.1.filter (fun x => x < i.1)).card)) •
          N β ⟨S.1.erase i.1,
            (Zset_subset_iff (S.1.erase i.1) β).mpr
              (Zset_index_erase hZT (Finset.mem_sdiff.mp i.2).1 (Finset.mem_sdiff.mp i.2).2),
            by rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp i.2).1]; omega⟩))
      = pieceCoeff B a β ⟨S.1, hZT, hcardT⟩ := by
      by_cases hbF : β ∈ F
      · rw [← hsol' β S.1 hZT hcardT]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hNapply, if_pos hbF]
      · have hmem : β ∉ pieceSupport (B := B) a := by rw [← hF]; exact hbF
        have hcoord : pieceCoeff B a β ⟨S.1, hZT, hcardT⟩ = 0 := by
          have h1 : ((B S.1).repr (cechCoeff a S.1 S.2))
              ⟨β, (Zset_subset_iff S.1 β).mp hβ⟩ = 0 := by
            by_contra hne
            exact hmem ((mem_pieceSupport B a).mpr ⟨S, (Zset_subset_iff S.1 β).mp hβ, hne⟩)
          exact h1
        have hzero2 : (∑ i ∈ (S.1 \ Zset β).attach,
            (((-1 : ℤ) ^ ((S.1.filter (fun x => x < i.1)).card)) •
              N β ⟨S.1.erase i.1,
                (Zset_subset_iff (S.1.erase i.1) β).mpr
                  (Zset_index_erase hZT (Finset.mem_sdiff.mp i.2).1 (Finset.mem_sdiff.mp i.2).2),
                by rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp i.2).1]; omega⟩)) = 0 := by
          refine Finset.sum_eq_zero (fun i _ => ?_)
          rw [hNapply, if_neg hbF, smul_zero]
        rw [hzero2, hcoord]
    exact key.trans hsum

end Work.DSCOH
