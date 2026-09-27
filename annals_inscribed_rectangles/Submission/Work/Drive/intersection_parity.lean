import Mathlib
import Submission.Work.Drive.boxParity
import Submission.Work.Drive.cofactor_restrict_surjective

/-!
# The mod-2 intersection pairing of a 2-chain and a 3-chain in `ℝ⁴`

The engine of the chain route to Hugelmeyer's geometric core (`Work.Drive.chainParity`) is a
*mod-2 intersection count*: the cohomological evaluations `⟨ω_P, [γ]⟩` of the paper's classes are
replaced by the parity of the number of points in which an explicit chain meets an explicit loop
(see `Submission/Work/Drive/CHAIN_ROUTE_NOTES.md`).  The abstract contract for such counts is
`Submission.Drive.ParityProp` — "a compact 1-manifold has an even number of boundary points", in the
concrete form of `Work.Drive.boxParity` — and this file is its intersection-theoretic corollary, the
**Leibniz rule for the mod-2 intersection pairing**:

> the transverse intersection of a 2-chain `D` and a 3-chain `N` in `ℝ⁴` is a compact 1-manifold
> whose boundary is the disjoint union of `∂D ⋔ N` (the loop `∂D` meets the 3-chain `N`) and
> `D ⋔ ∂N` (the surface `D` meets the boundary 2-chain of `N`); hence those two counts have the same
> parity.

Concretely we model the two chains by maps

* `D : ℝ² → ℝ⁴` on the unit square (the 2-chain; its boundary loop is the restriction of `D` to
  `∂[0,1]²`), and
* `N : ℝ³ → ℝ⁴` on the unit cube (the 3-chain; its boundary 2-chain is the restriction to
  `∂[0,1]³`),

and we apply `Work.Drive.boxParity` to the *difference map*

`chainDiff D N : ℝ⁵ → ℝ⁴,  (s,t) ↦ D s - N t`

(square block first, cube block last) on the five-dimensional unit box `[0,1]² × [0,1]³`.  Its zero
set in the box is (generically) the 1-manifold `D ⋔ N`, and the boundary zeros split into the two
blocks: those with `s ∈ ∂[0,1]²` (`loopMeet`, the count of `∂D ⋔ N`) and those with `t ∈ ∂[0,1]³`
(`solidMeet`, the count of `D ⋔ ∂N`).  `Work.Drive.boxParity` says the total number of boundary zeros
is even, whence

* `even_ncard_loopMeet_add_solidMeet` : `#(∂D ⋔ N) + #(D ⋔ ∂N)` is even;
* `even_ncard_loopMeet_of_boundary_disjoint` : if the boundary 2-chain of `N` misses the surface `D`
  (for instance because `N` is constant on `∂[0,1]³`, i.e. represents a *closed* 3-chain), then
  `#(∂D ⋔ N)` is even — the well-definedness of the mod-2 count of a bounding loop against a closed
  chain;
* `even_ncard_solidMeet_of_loop_disjoint` : if the loop `∂D` misses the 3-chain `N`, then
  `#(D ⋔ ∂N)` is even.

The transversality of the model is exactly encoded in the three hypotheses of
`Submission.Drive.ParityProp`, which are the hypotheses `hF`, `hreg`, `hface` of the theorems below.
-/

namespace Work.Drive

open Submission.Drive
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## The five-dimensional box `[0,1]² × [0,1]³` -/

/-- The two coordinates of the five-box that parametrise the 2-chain (the "square" block). -/
def sqIdx (i : Fin 2) : Fin 5 := Fin.castAdd 3 i

/-- The three coordinates of the five-box that parametrise the 3-chain (the "cube" block). -/
def cbIdx (j : Fin 3) : Fin 5 := Fin.natAdd 2 j

@[simp] lemma sqIdx_val (i : Fin 2) : (sqIdx i).val = i.val := rfl

@[simp] lemma cbIdx_val (j : Fin 3) : (cbIdx j).val = 2 + j.val := rfl

lemma sqIdx_lt_two (i : Fin 2) : (sqIdx i).val < 2 := i.isLt

lemma two_le_cbIdx (j : Fin 3) : 2 ≤ (cbIdx j).val := by simp

/-- The two blocks of coordinates are disjoint. -/
lemma sqIdx_ne_cbIdx (i : Fin 2) (j : Fin 3) : sqIdx i ≠ cbIdx j := by
  intro h
  have h' := congrArg Fin.val h
  simp only [sqIdx_val, cbIdx_val] at h'
  omega

/-- **Splitting the coordinates of the five-box.**  Every coordinate lies in one of the two blocks. -/
lemma exists_fin_five_iff (P : Fin 5 → Prop) :
    (∃ i, P i) ↔ (∃ i : Fin 2, P (sqIdx i)) ∨ (∃ j : Fin 3, P (cbIdx j)) := by
  constructor
  · rintro ⟨i, hi⟩
    revert hi
    refine Fin.addCases (m := 2) (n := 3) (motive := fun i => P i → _) ?_ ?_ i
    · intro i hi; exact Or.inl ⟨i, hi⟩
    · intro j hj; exact Or.inr ⟨j, hj⟩
  · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · exact ⟨sqIdx i, hi⟩
    · exact ⟨cbIdx j, hj⟩

/-- The projection of the five-box onto its "square" block. -/
def sqPart (x : EuclideanSpace ℝ (Fin 5)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun i => x (sqIdx i)

/-- The projection of the five-box onto its "cube" block. -/
def cbPart (x : EuclideanSpace ℝ (Fin 5)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun j => x (cbIdx j)

@[simp] lemma sqPart_apply (x : EuclideanSpace ℝ (Fin 5)) (i : Fin 2) :
    sqPart x i = x (sqIdx i) := rfl

@[simp] lemma cbPart_apply (x : EuclideanSpace ℝ (Fin 5)) (j : Fin 3) :
    cbPart x j = x (cbIdx j) := rfl

/-- The "square face" condition: one of the two coordinates of the square block is at the boundary. -/
def onSqFace (x : EuclideanSpace ℝ (Fin 5)) : Prop :=
  ∃ i : Fin 2, x (sqIdx i) = 0 ∨ x (sqIdx i) = 1

/-- The "cube face" condition: one of the three coordinates of the cube block is at the boundary. -/
def onCubeFace (x : EuclideanSpace ℝ (Fin 5)) : Prop :=
  ∃ j : Fin 3, x (cbIdx j) = 0 ∨ x (cbIdx j) = 1

/-- The five-box is the product of the square and the cube. -/
lemma mem_unitBox_five_iff (x : EuclideanSpace ℝ (Fin 5)) :
    x ∈ unitBox 4 ↔ sqPart x ∈ unitBox 1 ∧ cbPart x ∈ unitBox 2 := by
  constructor
  · intro h
    exact ⟨fun i => h (sqIdx i), fun j => h (cbIdx j)⟩
  · rintro ⟨h1, h2⟩ i
    revert i
    refine Fin.addCases (m := 2) (n := 3) (motive := fun i => x i ∈ Set.Icc (0 : ℝ) 1) ?_ ?_ 
    · intro i; exact h1 i
    · intro j; exact h2 j

/-- The boundary of the five-box is the union of the "square faces" and the "cube faces". -/
lemma mem_unitBoxBdry_five_iff (x : EuclideanSpace ℝ (Fin 5)) :
    x ∈ unitBoxBdry 4 ↔ x ∈ unitBox 4 ∧ (onSqFace x ∨ onCubeFace x) := by
  constructor
  · rintro ⟨hbox, i, hi⟩
    refine ⟨hbox, ?_⟩
    revert hi
    refine Fin.addCases (m := 2) (n := 3) (motive := fun i => (x i = 0 ∨ x i = 1) → _) ?_ ?_ i
    · intro i hi; exact Or.inl ⟨i, hi⟩
    · intro j hj; exact Or.inr ⟨j, hj⟩
  · rintro ⟨hbox, h | h⟩
    · obtain ⟨i, hi⟩ := h
      exact ⟨hbox, sqIdx i, hi⟩
    · obtain ⟨j, hj⟩ := h
      exact ⟨hbox, cbIdx j, hj⟩

/-! ## The intersection count of two chains -/

/-- **The difference map of a 2-chain and a 3-chain.**  Its zeros in the box `[0,1]² × [0,1]³` are
the intersections of the surface `D` (parametrised by the square) with the solid `N` (parametrised by
the cube). -/
def chainDiff (D : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (N : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 5) → EuclideanSpace ℝ (Fin 4) :=
  fun x => D (sqPart x) - N (cbPart x)

/-- The set of intersections of the boundary loop of the 2-chain `D` with the 3-chain `N`; as a
subset of the five-box it is the set of pairs `(s,t)` with `s` on the boundary of the square and
`D s = N t`. -/
def loopMeet (D : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (N : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4)) :
    Set (EuclideanSpace ℝ (Fin 5)) :=
  {x | x ∈ unitBox 4 ∧ onSqFace x ∧ chainDiff D N x = 0}

/-- The set of intersections of the 2-chain `D` with the boundary 2-chain of the 3-chain `N`; as a
subset of the five-box it is the set of pairs `(s,t)` with `t` on the boundary of the cube and
`D s = N t`. -/
def solidMeet (D : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (N : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4)) :
    Set (EuclideanSpace ℝ (Fin 5)) :=
  {x | x ∈ unitBox 4 ∧ onCubeFace x ∧ chainDiff D N x = 0}

/-- **Smoothness of the difference map.**  The difference of a smooth 2-chain and a smooth 3-chain is
smooth, so that the hypotheses of `Submission.Drive.ParityProp` make sense for it. -/
theorem contDiff_chainDiff
    (D : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (N : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) N) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chainDiff D N) := by
  unfold chainDiff
  fun_prop

/-- **The boundary of the intersection is the sum of the two boundary intersections.**  The zeros of
`chainDiff D N` on the boundary of the five-box are exactly the elements of `loopMeet D N` together
with the elements of `solidMeet D N`; this is the set-theoretic content of the Leibniz rule
`∂(D ⋔ N) = ∂D ⋔ N + D ⋔ ∂N`. -/
theorem bdyZeros_chainDiff_eq (D : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (N : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4)) :
    bdyZeros (chainDiff D N) = loopMeet D N ∪ solidMeet D N := by
  ext x
  simp only [bdyZeros, loopMeet, solidMeet, Set.mem_ofPred_eq, Set.mem_union]
  rw [mem_unitBoxBdry_five_iff x]
  tauto

/-! ## The Leibniz rule -/

/-- **The mod-2 Leibniz rule for the intersection pairing.**  Let `D` be a 2-chain and `N` a 3-chain
in `ℝ⁴` (modelled on the unit square and the unit cube), meeting transversally in the sense of the
three hypotheses of `Submission.Drive.ParityProp`.  Then the number of intersections of the boundary
loop of `D` with `N` and the number of intersections of `D` with the boundary 2-chain of `N` have the
same parity.  Equivalently, their sum is even — it is the number of boundary points of the compact
1-manifold `D ⋔ N`. -/
theorem even_ncard_loopMeet_add_solidMeet
    (D : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (N : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chainDiff D N))
    (hreg : ∀ x ∈ unitBox 4, chainDiff D N x = 0 →
      Function.Surjective (fderiv ℝ (chainDiff D N) x))
    (hface : ∀ x ∈ unitBoxBdry 4, chainDiff D N x = 0 → ∃ i : Fin (4 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
        fderiv ℝ (chainDiff D N) x v.1)) :
    Even ((loopMeet D N).ncard + (solidMeet D N).ncard) := by
  obtain ⟨hfin, heven⟩ := boxParity 4 (chainDiff D N) hF hreg hface
  have hfin' : (bdyZeros (chainDiff D N)).Finite := hfin
  have heven' : Even (bdyZeros (chainDiff D N)).ncard := heven
  rw [bdyZeros_chainDiff_eq] at hfin' heven'
  have hdisj : Disjoint (loopMeet D N) (solidMeet D N) := by
    rw [Set.disjoint_left]
    rintro x hx hy
    obtain ⟨hxbox, hxsq, hxF⟩ := hx
    obtain ⟨-, hccb, -⟩ := hy
    have hxbdy : x ∈ unitBoxBdry 4 :=
      (mem_unitBoxBdry_five_iff x).mpr ⟨hxbox, Or.inl hxsq⟩
    obtain ⟨i, hi, hother, -⟩ := hface x hxbdy hxF
    obtain ⟨i₀, hi₀⟩ := hxsq
    obtain ⟨j₀, hj₀⟩ := hccb
    have hi₀eq : sqIdx i₀ = i := by
      by_contra hne
      have hmem := hother (sqIdx i₀) hne
      rcases hi₀ with h | h
      · rw [h] at hmem
        exact absurd hmem.1 (by norm_num)
      · rw [h] at hmem
        exact absurd hmem.2 (by norm_num)
    have hj₀eq : cbIdx j₀ = i := by
      by_contra hne
      have hmem := hother (cbIdx j₀) hne
      rcases hj₀ with h | h
      · rw [h] at hmem
        exact absurd hmem.1 (by norm_num)
      · rw [h] at hmem
        exact absurd hmem.2 (by norm_num)
    exact sqIdx_ne_cbIdx i₀ j₀ (by rw [hi₀eq, hj₀eq])
  rw [Set.ncard_union_eq hdisj (hfin'.subset Set.subset_union_left)
    (hfin'.subset Set.subset_union_right)] at heven'
  exact heven'

/-- **Finiteness of the two boundary intersection sets.**  Under the transversality hypotheses of
`Submission.Drive.ParityProp` both `loopMeet` and `solidMeet` are finite, so that the parity statement
of `Work.Drive.even_ncard_loopMeet_add_solidMeet` is a statement about two natural numbers and not a
vacuous one (`Set.ncard` of an infinite set is `0`). -/
theorem finite_loopMeet_and_solidMeet
    (D : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (N : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hF : ContDiff ℝ Ctop (chainDiff D N))
    (hreg : ∀ x ∈ unitBox 4, chainDiff D N x = 0 →
      Function.Surjective (fderiv ℝ (chainDiff D N) x))
    (hface : ∀ x ∈ unitBoxBdry 4, chainDiff D N x = 0 → ∃ i : Fin (4 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
        fderiv ℝ (chainDiff D N) x v.1)) :
    (loopMeet D N).Finite ∧ (solidMeet D N).Finite := by
  obtain ⟨hfin, -⟩ := boxParity 4 (chainDiff D N) hF hreg hface
  have hfin' : (bdyZeros (chainDiff D N)).Finite := hfin
  rw [bdyZeros_chainDiff_eq] at hfin'
  exact ⟨hfin'.subset (fun x hx => by simp only [Set.mem_union]; exact Or.inl hx),
    hfin'.subset (fun x hx => by simp only [Set.mem_union]; exact Or.inr hx)⟩

/-- **The Leibniz rule in the cofactor form of the face hypothesis.**  The third hypothesis of
`Submission.Drive.ParityProp` is a restricted surjectivity of the derivative at every boundary zero;
by `Work.Drive.surjective_domRestrict_iff_cofactorVec_ne_zero` it is equivalent to the *scalar*
condition that the tangential direction of the intersection 1-manifold at the zero — the cofactor
vector of the derivative, which spans its kernel — is not tangent to the face.  This is the form in
which the hypothesis is meant to be checked in applications. -/
theorem even_ncard_loopMeet_add_solidMeet_cofactor
    (D : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (N : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chainDiff D N))
    (hreg : ∀ x ∈ unitBox 4, chainDiff D N x = 0 →
      Function.Surjective (fderiv ℝ (chainDiff D N) x))
    (hface : ∀ x ∈ unitBoxBdry 4, chainDiff D N x = 0 → ∃ i : Fin (4 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      cofactorVectorF (chainDiff D N) x i ≠ 0) :
    Even ((loopMeet D N).ncard + (solidMeet D N).ncard) :=
  even_ncard_loopMeet_add_solidMeet D N hF hreg fun x hx h0 =>
    let ⟨i, hi, hoth, hne⟩ := hface x hx h0
    ⟨i, hi, hoth, (surjective_domRestrict_iff_cofactorVec_ne_zero
      (fderiv ℝ (chainDiff D N) x) (hreg x hx.1 h0) i).mpr hne⟩

/-- **The count of `∂D ⋔ N` is even when `N` has no boundary on `D`.**  If the boundary 2-chain of
the 3-chain `N` misses the surface `D` — for instance because `N` is constant on the boundary of the
cube, i.e. represents a *closed* 3-chain — then the number of intersections of the boundary loop of
`D` with `N` is even.  This is the well-definedness of the mod-2 intersection number of a bounding
loop with a closed 3-chain. -/
theorem even_ncard_loopMeet_of_boundary_disjoint
    (D : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (N : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chainDiff D N))
    (hreg : ∀ x ∈ unitBox 4, chainDiff D N x = 0 →
      Function.Surjective (fderiv ℝ (chainDiff D N) x))
    (hface : ∀ x ∈ unitBoxBdry 4, chainDiff D N x = 0 → ∃ i : Fin (4 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
        fderiv ℝ (chainDiff D N) x v.1))
    (hdisj : ∀ x, x ∈ unitBox 4 → onCubeFace x → chainDiff D N x ≠ 0) :
    Even (loopMeet D N).ncard := by
  have hempty : solidMeet D N = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hcf, hFx⟩
    exact hdisj x hx hcf hFx
  have h := even_ncard_loopMeet_add_solidMeet D N hF hreg hface
  rw [hempty, Set.ncard_empty, add_zero] at h
  exact h

/-- **The count of `D ⋔ ∂N` is even when the loop `∂D` misses `N`.**  If the boundary loop of the
2-chain `D` is disjoint from the 3-chain `N`, then the number of intersections of the surface `D` with
the boundary 2-chain of `N` is even; this is the dual form of the previous corollary. -/
theorem even_ncard_solidMeet_of_loop_disjoint
    (D : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (N : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chainDiff D N))
    (hreg : ∀ x ∈ unitBox 4, chainDiff D N x = 0 →
      Function.Surjective (fderiv ℝ (chainDiff D N) x))
    (hface : ∀ x ∈ unitBoxBdry 4, chainDiff D N x = 0 → ∃ i : Fin (4 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
        fderiv ℝ (chainDiff D N) x v.1))
    (hdisj : ∀ x, x ∈ unitBox 4 → onSqFace x → chainDiff D N x ≠ 0) :
    Even (solidMeet D N).ncard := by
  have hempty : loopMeet D N = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hsf, hFx⟩
    exact hdisj x hx hsf hFx
  have h := even_ncard_loopMeet_add_solidMeet D N hF hreg hface
  rw [hempty, Set.ncard_empty, zero_add] at h
  exact h

end

end Work.Drive
