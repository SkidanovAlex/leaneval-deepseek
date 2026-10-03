import Mathlib
import Submission.Work.Peluse.UControl.levRoundBase
import Submission.Work.Peluse.UControl.levStepRef
import Submission.Work.Peluse.UControl.levInv2Defs

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

attribute [local instance] Classical.propDecidable

/-! ## Two elementary lemmas used by the initial invariant -/

/-- `liftSub` at `r = 0` is `subSum`: the renaming along `Fin.castLE (L ≤ L + 0)` is the identity
(in fact definitionally so, since `L + 0` is definitionally `L`). -/
lemma liftSub_zero {L : ℕ} {A : Finset (Fin L)} {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ}
    (ω : Finset (Fin L)) : liftSub A atoms 0 ω = subSum A atoms ω := by
  rw [liftSub]
  have h : (Fin.castLE (Nat.le_add_right L 0) : Fin L → Fin (L + 0)) = id := rfl
  rw [h]
  exact MvPolynomial.rename_id_apply _

/-- A history of the punctured sub-cube `cubeSet L A f₀ \ {f₀}` is true at some parameter of `A`,
provided `f₀` is false on `A`. -/
lemma exists_true_of_mem_cubeSet_ne {L : ℕ} {A : Finset (Fin L)} {f₀ h : Fin L → Bool}
    (h0 : ∀ i ∈ A, f₀ i = false) (hh : h ∈ cubeSet L A f₀) (hne : h ≠ f₀) :
    ∃ i ∈ A, h i = true := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  refine hne (funext fun i => ?_)
  by_cases hi : i ∈ A
  · have hnt : h i ≠ true := hcon i hi
    cases hb : h i
    · exact (h0 i hi).symm
    · exact absurd hb hnt
  · exact (Finset.mem_filter.mp hh).2 i hi

/-- **The initial invariant of the round**: a `LevCube`-state of degree `D` is a `LevInv`-state with
`r = 0`, the classes the *nonempty subsets of `A`*, and the trivial shift `σ = fun _ => ∅`.

Context (`Submission/Work/Peluse/UControl/levCubeDefs.lean`, `levRoundDefs.lean`).  A `LevCube` state
`X : HistData d L` of degree `D` has live slots `X.H = LevH d L A f₀` (the punctured cube
`cubeSet L A f₀ \ {f₀}`, `P`-tagged) and every live slot has `natDegree = D` and leading coefficient
`atomSum A atoms h`.

Assertion.  If the atoms are independent (`LevIndep L A atoms`), `1 ≤ D` and `A` is nonempty, then
`X` satisfies `LevInv d D A f₀ atoms 0 K₀ (fun _ => ∅)` with
`K₀ = Finset.univ.filter (fun ω : Finset (Fin L) => ω ⊆ A ∧ ω.Nonempty)`.

## Proof route

1. **First derive `f₀ = false` on `A`.**  The history `h* := histOf A f₀ ∅` (which is `false` on `A`
   and `f₀` off `A`) lies in `cubeSet L A f₀` (`histOf_mem_cube`).  If `h* ≠ f₀`, `hX` gives
   `(X.Q (Sum.inr 0) h*).natDegree = D` and `leadingCoeff = atomSum A atoms h* = 0` (an empty sum),
   contradicting `0 < D ≤ natDegree` (`Polynomial.leadingCoeff_eq_zero`).  Hence `h* = f₀`, i.e.
   `f₀ i = false` for `i ∈ A`.
2. Because of 1, `histOf A f₀ ω = f₀ ↔ ω = ∅` (`histOf_eq_zero_iff`), and `histOf` is injective on
   the subsets of `A` (`histOf_inj`), so the live slots `X.H = LevH d L A f₀` are exactly the
   `(Sum.inr 0, histOf A f₀ ω)` with `ω ⊆ A` nonempty (`mem_LevH`).
3. The fields of `LevInv`:
   * `subK`, `nonemptyK`, `memA` (`A ≠ ∅`), `sigma_zero` (`fun _ => ∅` at `0`), `sigma_sub`
     (`∅ ⊆ A`), `sigma_ne` (`∅ ≠ A`);
   * `degLe` (`(X.Q x.1 x.2).natDegree ≤ D`: every live slot has degree exactly `D` by `hX`);
   * `top_mem` for `ω ∈ K₀`: `slotHist … 0 w = histOf A f₀ ω` definitionally, so the slot is live
     with degree `D` and leading coefficient `atomSum A atoms (histOf A f₀ ω) = subSum A atoms ω`
     (`subSum_eq_atomSum`) `= liftSub A atoms 0 ω - liftSub A atoms 0 ∅`;
   * `top_only`: a live slot `x` is `(Sum.inr 0, h)` with `h ∈ cubeSet L A f₀`, `h ≠ f₀`; take
     `ω := {i ∈ A | h i = true}` and show `histOf A f₀ ω = h` and `ω ∈ K₀` (nonempty because
     `h ≠ f₀` and `f₀` is `false` on `A`);
   * `coeff_diff` at `r = 0`: `Fin 0 → Bool` is a subsingleton and `slotHist … 0 _ = histOf A f₀ A`
     definitionally, so both sides are `0` (`Finset.sum_empty`).

Useful lemmas: `histOf_mem_cube`, `histOf_apply`, `histOf_inj`, `histOf_eq_zero_iff`,
`subSum_eq_atomSum`, `mem_LevH`, `LevH`, `cubeSet`, `atomSum`, `subSum`, `liftSub`, `slotHist`
(all in `levRoundDefs.lean` / `levCubeDefs.lean`); `Polynomial.leadingCoeff_eq_zero`,
`Polynomial.coeff_natDegree`. -/
theorem levInvInit {d D L : ℕ} {A : Finset (Fin L)} {f₀ : Fin L → Bool}
    {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ}
    (hind : LevIndep L A atoms) (hD : 1 ≤ D) (hA : A.Nonempty)
    {X : HistData d L} (hX : LevCube d D L A f₀ atoms X) :
    LevInv d D A f₀ atoms 0 (Finset.univ.filter (fun ω : Finset (Fin L) => ω ⊆ A ∧ ω.Nonempty))
      (fun _ => ∅) X := by
  classical
  -- Note: the independence hypothesis `hind` is *not* used: the compatibility of the initial state
  -- only needs the degree/leading-coefficient clause of `LevCube` and `1 ≤ D`.
  -- ### Step 1: `f₀` is `false` on `A`.
  --
  -- The history `histOf A f₀ ∅` (which is `false` on `A` and `f₀` outside `A`) lies in the cube
  -- `cubeSet L A f₀`.  If it differed from `f₀` it would be a live slot, hence have degree `D` and
  -- leading coefficient `atomSum A atoms (histOf A f₀ ∅) = 0`, contradicting `0 < D ≤ natDegree`.
  have h0 : ∀ i ∈ A, f₀ i = false := by
    have hmem : histOf A f₀ (∅ : Finset (Fin L)) ∈ cubeSet L A f₀ := histOf_mem_cube ∅
    have hzero : atomSum A atoms (histOf A f₀ (∅ : Finset (Fin L))) = 0 := by
      simp only [atomSum]
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [histOf_apply s.2, decide_eq_false (Finset.notMem_empty (s : Fin L))]
      simp
    have hfeq : histOf A f₀ (∅ : Finset (Fin L)) = f₀ := by
      by_contra hne
      obtain ⟨hdeg, hlc⟩ := hX.2 (histOf A f₀ (∅ : Finset (Fin L))) hmem hne
      rw [hzero] at hlc
      have hp : X.Q (Sum.inr 0 : InitIdx d) (histOf A f₀ (∅ : Finset (Fin L))) = 0 :=
        Polynomial.leadingCoeff_eq_zero.mp hlc
      rw [hp, Polynomial.natDegree_zero] at hdeg
      omega
    intro i hi
    have h2 := congrFun hfeq i
    rw [histOf, if_pos hi, decide_eq_false (Finset.notMem_empty i)] at h2
    exact h2.symm
  -- ### Step 2: the fields of `LevInv`.
  refine
    { subK := ?_
      nonemptyK := ?_
      memA := ?_
      sigma_zero := ?_
      sigma_sub := ?_
      sigma_ne := ?_
      degLe := ?_
      top_mem := ?_
      top_only := ?_
      coeff_diff := ?_ }
  · intro ω hω
    exact (Finset.mem_filter.mp hω).2.1
  · intro ω hω
    exact (Finset.mem_filter.mp hω).2.2
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ A, Finset.Subset.refl A, hA⟩
  · rfl
  · intro j
    exact Finset.empty_subset A
  · intro j h
    exact (Finset.nonempty_iff_ne_empty.mp hA) h.symm
  · intro x hx
    have hx' : x ∈ LevH d L A f₀ := by
      rw [← hX.1]
      exact hx
    obtain ⟨h1, h2, h3⟩ := mem_LevH.mp hx'
    rw [h1]
    exact le_of_eq (hX.2 x.2 h2 h3).1
  · intro ω hω w
    obtain ⟨hωA, hωne⟩ := (Finset.mem_filter.mp hω).2
    have hωne' : ω ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hωne
    have hf0 : histOf A f₀ ω ≠ f₀ := fun hc => hωne' ((histOf_eq_zero_iff h0 hωA).mp hc)
    refine ⟨?_, ?_, ?_⟩
    · have hmem : ((Sum.inr 0 : InitIdx d), slotHist (histOf A f₀ ω) 0 w) ∈ LevH d L A f₀ :=
        mem_LevH.mpr ⟨rfl, histOf_mem_cube ω, hf0⟩
      rw [← hX.1] at hmem
      exact hmem
    · exact (hX.2 (histOf A f₀ ω) (histOf_mem_cube ω) hf0).1
    · rw [show (X.Q (Sum.inr 0 : InitIdx d) (slotHist (histOf A f₀ ω) 0 w)).leadingCoeff
          = (X.Q (Sum.inr 0 : InitIdx d) (histOf A f₀ ω)).leadingCoeff from rfl,
        (hX.2 (histOf A f₀ ω) (histOf_mem_cube ω) hf0).2, subSum_eq_atomSum,
        liftSub_zero ω, liftSub_zero (∅ : Finset (Fin L))]
      simp [subSum]
  · intro x hx hxdeg
    have hx' : x ∈ LevH d L A f₀ := by
      rw [← hX.1]
      exact hx
    obtain ⟨h1, h2, h3⟩ := mem_LevH.mp hx'
    obtain ⟨i, hiA, hix⟩ := exists_true_of_mem_cubeSet_ne h0 h2 h3
    refine ⟨h1, ?_⟩
    refine ⟨A.filter (fun i => x.2 i), ?_, (0 : Fin 0 → Bool), ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro j hj
        exact (Finset.mem_filter.mp hj).1
      · exact ⟨i, Finset.mem_filter.mpr ⟨hiA, hix⟩⟩
    · show x.2 = histOf A f₀ (histCls A x.2)
      exact (histOf_histCls h2).symm
  · intro w
    have h : (X.Q (Sum.inr 0 : InitIdx d) (slotHist (histOf A f₀ A) 0 w)).coeff (D - 1)
        = (X.Q (Sum.inr 0 : InitIdx d) (slotHist (histOf A f₀ A) 0 0)).coeff (D - 1) := rfl
    rw [h, sub_self, Finset.sum_eq_zero (fun j _ => absurd j.2 (Nat.not_lt_zero j.1))]

end Work.Peluse.UControl
