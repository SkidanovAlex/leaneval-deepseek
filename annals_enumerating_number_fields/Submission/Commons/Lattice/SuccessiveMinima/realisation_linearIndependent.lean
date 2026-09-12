import Mathlib
import Submission.Commons.Lattice.SuccessiveMinima.Basic

/-!
# Realisation of successive minima by independent vectors (shared commons)

For a full `ℤ`-lattice `L` in a finite-dimensional real normed space, every `ε > 0` admits
`ℤ`-linearly (hence `ℝ`-linearly) independent lattice vectors `v₁, …, vₘ` with
`‖vᵢ‖ ≤ λᵢ(L) + ε` (`m = finrank ℤ L`).  This is the standard "realisation lemma" used in
geometry of numbers (Minkowski's second theorem and its successors): it turns the
`infimum`-definition of the successive minima into actual independent vectors.

Structure of the proof:
- `basis_expansion_int`: any `ℤ`-basis of `L` expands lattice elements in the ambient space
  (a `ℤ`-linear combination of the basis images);
- `linearIndependent_real_of_linearIndependent_int`: a `ℤ`-linearly independent family of
  lattice points is `ℝ`-linearly independent — any `ℤ`-basis of `L` is an `ℝ`-basis of the
  ambient space (`Module.Basis.ofZLatticeBasis`), so integer relations generate all real
  relations (`linearIndependent_algebraMap_comp_iff` over `ℤ → ℚ → ℝ`);
- `exists_linearIndependent_of_successiveMinimum`: the realisation theorem, by induction on
  the size `i` of the family: at radius `λᵢ + ε` the lattice contains `i` `ℤ`-independent
  points (`exists_linearIndependent_of_successiveMinimum_lt`); they are `ℝ`-independent, so
  one of them lies outside the span of the previously chosen `i-1` vectors
  (`linearIndependent_finSnoc`); appending it keeps the bounds because every lattice point
  of norm `< λᵢ` in a ZLattice is realised within the ball of radius `λᵢ + ε`.

All declarations are Mathlib-only apart from the Commons successive-minima API.
-/

noncomputable section

open Set Filter Metric MeasureTheory Module BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Commons.Lattice.SuccessiveMinima

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Expansion of a lattice element in a `ℤ`-basis, pushed into the ambient space. -/
lemma basis_expansion_int (L : Submodule ℤ E) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ L) (x : L) :
    (x : E) = ∑ i : ι, (b.repr x) i • (b i : E) := by
  classical
  have hx : (x : E) = (b.repr.symm (b.repr x) : L) := by
    exact congrArg Subtype.val (show x = b.repr.symm (b.repr x) from
      (b.repr.symm_apply_apply x).symm)
  calc
    (x : E) = (b.repr.symm (b.repr x) : L) := hx
    _ = (Finsupp.linearCombination ℤ b (b.repr x) : L) := by
          rw [Module.Basis.repr_symm_apply (b := b)]
    _ = ∑ i : ι, (b.repr x) i • (b i : E) := by
          rw [Finsupp.linearCombination_apply]
          rw [Finsupp.sum_fintype (f := b.repr x) (g := fun i a => (a • b i : L))
            (by intro i; simp)]
          rw [Submodule.coe_sum]
          apply Finset.sum_congr rfl
          intro i hi
          simp

/-- A `ℤ`-linearly independent family of elements of a lattice is `ℝ`-linearly independent
(any `ℤ`-basis of the lattice is an `ℝ`-basis of the ambient space). -/
lemma linearIndependent_real_of_linearIndependent_int (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] {ι : Type*} [Fintype ι] (f : ι → L)
    (h : LinearIndependent ℤ (fun j : ι => (f j : E))) :
    LinearIndependent ℝ (fun j : ι => (f j : E)) := by
  classical
  letI : Module.Free ℤ L := ZLattice.module_free ℝ L
  letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let n : ℕ := Module.finrank ℤ L
  let b : Module.Basis (Fin n) ℤ L := Module.finBasis ℤ L
  let c : ι → Fin n → ℤ := fun j k => (b.repr (f j)) k
  have hc : LinearIndependent ℤ c := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : (∑ j : ι, g j • (f j : E)) = 0 := by
      calc
        (∑ j : ι, g j • (f j : E)) = ∑ j : ι, ∑ k : Fin n, (g j * (b.repr (f j)) k) • (b k : E) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [basis_expansion_int L b (f j)]
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          rw [smul_smul]
        _ = ∑ k : Fin n, ∑ j : ι, (g j * (b.repr (f j)) k) • (b k : E) := by
          rw [Finset.sum_comm]
        _ = ∑ k : Fin n, (∑ j : ι, g j * (b.repr (f j)) k) • (b k : E) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [← Finset.sum_smul]
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hgk : (∑ j : ι, g j * (b.repr (f j)) k) = 0 := by
            calc
              (∑ j : ι, g j * (b.repr (f j)) k) = ∑ j : ι, (g j • c j) k := by
                apply Finset.sum_congr rfl
                intro j hj
                simp [c, Pi.smul_apply]
              _ = 0 := by
                have hk0 := congrFun hg k
                rw [Finset.sum_apply] at hk0
                exact hk0
          simp [hgk]
    intro j
    exact (Fintype.linearIndependent_iff.mp h) g hsum j
  let cQ : ι → Fin n → ℚ := fun j k => (c j k : ℚ)
  have hfam : (fun i : ι => algebraMap ℤ ℚ ∘ c i) = cQ := by
    ext j k
    simp [cQ]
  have hq : LinearIndependent ℚ cQ := by
    have hq' := (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ) (v := c)).mpr hc
    rwa [hfam] at hq'
  have hcR : LinearIndependent ℝ (fun j : ι => fun k : Fin n => ((cQ j k) : ℝ)) := by
    have hfam2 : (fun i : ι => algebraMap ℚ ℝ ∘ cQ i) =
        (fun j : ι => fun k : Fin n => ((cQ j k) : ℝ)) := by
      ext j k
      simp
    have h := (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℝ) (v := cQ)).mpr hq
    rwa [hfam2] at h
  rw [Fintype.linearIndependent_iff]
  intro r hr
  have hcoef : ∀ k : Fin n, (∑ j : ι, r j * ((c j k : ℤ) : ℝ)) = 0 := by
    intro k
    have hbE : LinearIndependent ℝ (fun k : Fin n => (b k : E)) := by
      have hbE' : LinearIndependent ℝ (fun k : Fin n => (Module.Basis.ofZLatticeBasis ℝ L b) k) :=
        (Module.Basis.ofZLatticeBasis ℝ L b).linearIndependent
      simpa [Module.Basis.ofZLatticeBasis_apply] using hbE'
    have hrel : (∑ k0 : Fin n, (∑ j : ι, r j * ((c j k0 : ℤ) : ℝ)) • (b k0 : E)) = 0 := by
      calc
        (∑ k0 : Fin n, (∑ j : ι, r j * ((c j k0 : ℤ) : ℝ)) • (b k0 : E))
            = ∑ k0 : Fin n, ∑ j : ι, (r j * ((c j k0 : ℤ) : ℝ)) • (b k0 : E) := by
                apply Finset.sum_congr rfl
                intro k0 hk0
                rw [Finset.sum_smul]
        _ = ∑ j : ι, ∑ k0 : Fin n, (r j * ((c j k0 : ℤ) : ℝ)) • (b k0 : E) := by
                rw [Finset.sum_comm]
        _ = ∑ j : ι, r j • (f j : E) := by
                apply Finset.sum_congr rfl
                intro j hj
                calc
                  (∑ k0 : Fin n, (r j * ((c j k0 : ℤ) : ℝ)) • (b k0 : E))
                      = r j • (∑ k0 : Fin n, ((c j k0 : ℤ) : ℝ) • (b k0 : E)) := by
                          rw [Finset.smul_sum]
                          apply Finset.sum_congr rfl
                          intro k0 hk0
                          rw [mul_smul]
                  _ = r j • (f j : E) := by
                          have hz := basis_expansion_int L b (f j)
                          have hsums : (∑ k0 : Fin n, ((c j k0 : ℤ) : ℝ) • (b k0 : E)) =
                              (∑ i : Fin n, (b.repr (f j)) i • (b i : E)) := by
                            apply Finset.sum_congr rfl
                            intro k0 hk0
                            rw [Int.cast_smul_eq_zsmul ℝ (c j k0)]
                          calc
                            r j • (∑ k0 : Fin n, ((c j k0 : ℤ) : ℝ) • (b k0 : E))
                                = r j • (∑ i : Fin n, (b.repr (f j)) i • (b i : E)) := by rw [hsums]
                            _ = r j • (f j : E) := by rw [hz]
        _ = 0 := hr
    exact (Fintype.linearIndependent_iff.mp hbE)
      (fun k0 : Fin n => (∑ j : ι, r j * ((c j k0 : ℤ) : ℝ))) hrel k
  have hr0 : ∀ j : ι, r j = 0 := by
    have hh : (∑ j : ι, r j • (fun k : Fin n => ((cQ j k) : ℝ))) = 0 := by
      ext k
      have hk := hcoef k
      -- (∑ j, r j • (fun k => (cQ j k : ℝ))) k = ∑ j, r j * (cQ j k : ℝ) = ∑ r j * (c j k : ℝ)
      have hk0 : (∑ j : ι, r j * ((cQ j k) : ℝ)) = 0 := by
        simpa [cQ] using hk
      simpa [Pi.smul_apply, smul_eq_mul] using hk0
    exact (Fintype.linearIndependent_iff.mp hcR) r hh
  intro j
  exact hr0 j

/-- **Realisation of successive minima by independent vectors**: for a full lattice `L` of
`ℤ`-rank `m`, every `ε > 0` admits independent lattice vectors `v₁, …, vₘ`
(`ℤ`-independence, hence `ℝ`-independence, of the ambient-space images) with
`‖vᵢ‖ ≤ λᵢ(L) + ε`. -/
theorem exists_linearIndependent_of_successiveMinimum (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (m : ℕ) (hm : Module.finrank ℤ L = m) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Fin m → L,
      LinearIndependent ℝ (fun j : Fin m => (v j : E)) ∧
      ∀ j : Fin m, ‖(v j : E)‖ ≤ successiveMinimum L (j.val + 1) + ε := by
  classical
  let P : ℕ → Prop := fun i => i ≤ m → ∃ v : Fin i → L,
      LinearIndependent ℝ (fun j : Fin i => (v j : E)) ∧
      ∀ j : Fin i, ‖(v j : E)‖ ≤ successiveMinimum L (j.val + 1) + ε
  have hP0 : P 0 := by
    intro hi
    refine ⟨fun j => 0, ?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg j
      exact False.elim (Nat.not_lt_zero j.val j.isLt)
    · intro j
      exact False.elim (Nat.not_lt_zero j.val j.isLt)
  have hstep : ∀ i : ℕ, P i → P (i + 1) := by
    intro i hPi hsucc
    rcases hPi (le_trans (Nat.le_succ i) hsucc) with ⟨v, hvLI, hvbd⟩
    have hri : successiveMinimum L (i + 1) < successiveMinimum L (i + 1) + ε := by linarith
    have hi_fin : i + 1 ≤ Module.finrank ℤ L := by
      rw [hm]
      exact hsucc
    rcases exists_linearIndependent_of_successiveMinimum_lt L (i + 1) hi_fin hri with
      ⟨y, hyLI, hybd⟩
    have yLIr : LinearIndependent ℝ (fun j : Fin (i + 1) => (y j : E)) :=
      linearIndependent_real_of_linearIndependent_int L y hyLI
    let W : Submodule ℝ E := Submodule.span ℝ (Set.range (fun k : Fin i => (v k : E)))
    have hfinW : Module.finrank ℝ W = i := by
      rw [finrank_span_eq_card (R := ℝ) (b := fun k : Fin i => (v k : E)) hvLI]
      simp
    have hnotW : ∃ j : Fin (i + 1), (y j : E) ∉ W := by
      by_contra hnone
      have hmem : ∀ j : Fin (i + 1), (y j : E) ∈ W := by
        intro j
        by_contra hn
        exact hnone ⟨j, hn⟩
      let yW : Fin (i + 1) → W := fun j => ⟨(y j : E), hmem j⟩
      have yWLI : LinearIndependent ℝ yW := LinearIndependent.of_comp W.subtype yLIr
      haveI : Module.Finite ℝ W := by infer_instance
      have hcard := LinearIndependent.fintype_card_le_finrank yWLI
      rw [hfinW] at hcard
      simp at hcard
    rcases hnotW with ⟨j₀, hj₀W⟩
    let x : L := y j₀
    let v' : Fin (i + 1) → L := Fin.snoc v x
    have hv'LI : LinearIndependent ℝ (fun j : Fin (i + 1) => (v' j : E)) := by
      have hE : (fun j : Fin (i + 1) => (v' j : E)) =
          Fin.snoc (fun k : Fin i => (v k : E)) (x : E) := by
        ext j
        cases j using Fin.lastCases with
        | last =>
            simp [v']
        | cast k =>
            simp [v']
      rw [hE]
      have hsnoc := (linearIndependent_finSnoc (K := ℝ) (x := (x : E))
        (v := fun k : Fin i => (v k : E))).2
      exact hsnoc ⟨hvLI, hj₀W⟩
    have hv'bd : ∀ j : Fin (i + 1), ‖(v' j : E)‖ ≤ successiveMinimum L (j.val + 1) + ε := by
      intro j
      by_cases hjeq : j.val = i
      · have hjl : j = Fin.last i := by apply Fin.ext; exact hjeq
        have hxbd : ‖(x : E)‖ ≤ successiveMinimum L (i + 1) + ε := hybd j₀
        rw [hjl]
        simpa [v', x, Fin.snoc_last, Fin.val_last] using hxbd
      · have hjlt : j.val < i := lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt) (by
          intro h
          exact hjeq h)
        let k : Fin i := ⟨j.val, hjlt⟩
        have hk : j = k.castSucc := by apply Fin.ext; rfl
        have hbk := hvbd k
        have hvj : v' j = v k := by
          rw [hk]
          exact Fin.snoc_castSucc (α := fun _ : Fin (i + 1) => L) (x := x) (p := v) (i := k)
        simpa [v', hvj] using hbk
    exact ⟨v', hv'LI, hv'bd⟩
  have hPm : P m := Nat.rec hP0 hstep m
  exact hPm (le_refl m)
