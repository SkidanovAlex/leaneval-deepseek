import Mathlib
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Lattice.SuccessiveMinima.realisation_linearIndependent

/-!
# Exact realisation of the successive minima (shared commons)

For a full `ℤ`-lattice `L` of `ℤ`-rank `m` in a finite-dimensional real normed space, the
successive minima `λᵢ(L)` are **attained**: the closed ball of radius `λᵢ` contains `i`
`ℤ`-linearly independent lattice points (`exists_linearIndependent_eq`), and — building a
single nested family greedily — there is a family `v₁, …, vₘ` of independent lattice vectors
with `‖vⱼ‖ ≤ λⱼ(L)` for every `j` (`exact_realization`, the theorem requested by the
Minkowski/covering-radius development).  This upgrades the approximate realisation
`exists_linearIndependent_of_successiveMinimum` (realisation radius `λᵢ + ε`) to the exact
infimum.

Proof route:
- `finite_lattice_in_ball`: the lattice is a closed discrete subset of the (proper) ambient
  space (`AddSubgroup.isClosed_of_discrete`), so it meets every closed ball in a finite set;
- `exists_linearIndependent_eq`: among all witnesses `f : Fin i → L` of `ℤ`-independence with
  norms `≤ λᵢ + 1` (a finite family, by the previous lemma) pick one minimising
  `maxⱼ ‖f j‖` (`Finset.exists_min_image`).  That minimum must be `≤ λᵢ`, for otherwise a
  witness for any radius in `(λᵢ, min)` — which exists by the infimum definition — would
  contradict minimality.  Hence the minimum equals `λᵢ` and is attained;
- `exact_realization`: induction on the size `i` of the family, exactly as in the
  `ε`-realisation theorem, but inserting the vector of norm `≤ λᵢ₊₁` supplied by the
  attainment lemma instead of one of norm `≤ λᵢ₊₁ + ε`.

All declarations are Mathlib-only apart from the Commons successive-minima API.
-/

noncomputable section

open Set Filter Metric
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Commons.Lattice.SuccessiveMinima

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Lattice points in a closed ball form a finite set (the lattice is closed and discrete,
and closed balls of the finite-dimensional normed space `E` are compact). -/
lemma finite_lattice_in_ball (L : Submodule ℤ E) [DiscreteTopology L]
    (R : ℝ) : Set.Finite {x : L | ‖(x : E)‖ ≤ R} := by
  have hclosed : IsClosed (L : Set E) := by
    exact @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
  have hset : Set.Finite ((Metric.closedBall (0 : E) R) ∩ (L : Set E)) :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall hclosed
  exact hset.of_injOn (f := (Subtype.val : L → E))
    (s := {x : L | ‖(x : E)‖ ≤ R}) (t := (Metric.closedBall (0 : E) R) ∩ (L : Set E))
    (by
      intro x hx
      constructor
      · simpa [dist_eq_norm] using hx
      · exact x.2)
    (by
      intro x _ y _ hxy
      exact Subtype.val_injective hxy)

/-- **Exact realisation of the `i`-th successive minimum** (attainment of the infimum):
for `1 ≤ i ≤ finrank ℤ L`, the closed ball of radius `λᵢ = successiveMinimum L i` contains
`i` `ℤ`-linearly independent lattice points. -/
lemma exists_linearIndependent_eq (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ Module.finrank ℤ L) :
    ∃ f : Fin i → L, LinearIndependent ℤ (fun j : Fin i => (f j : E)) ∧
      ∀ j : Fin i, ‖(f j : E)‖ ≤ successiveMinimum L i := by
  classical
  let mu : ℝ := successiveMinimum L i
  let R : ℝ := mu + 1
  have hS : (successiveMinimumSet L i).Nonempty := nonempty_successiveMinimumSet L i hi
  have hmuR : mu < R := by
    have hmu0 : 0 ≤ mu := successiveMinimum_nonneg L i hi
    dsimp [R]
    linarith
  rcases mem_successiveMinimumSet_of_sInf_lt L i hmuR hS with ⟨hR0, f0, hLI0, hbd0⟩
  let B := {x : L // ‖(x : E)‖ ≤ R}
  haveI : Fintype B := Set.Finite.fintype (finite_lattice_in_ball L R)
  let W := {f : Fin i → L // LinearIndependent ℤ (fun j : Fin i => (f j : E)) ∧
    ∀ j : Fin i, ‖(f j : E)‖ ≤ R}
  haveI : Fintype W := by
    refine Fintype.ofInjective (fun f : W => fun j : Fin i => (⟨f.1 j, (f.2).2 j⟩ : B)) ?_
    intro a b h
    refine Subtype.ext ?_
    funext j
    exact congrArg Subtype.val (congrFun h j)
  have hWne : Nonempty W := ⟨⟨f0, hLI0, hbd0⟩⟩
  haveI : Nonempty W := hWne
  have hne : (Finset.univ : Finset (Fin i)).Nonempty := by
    haveI : Nonempty (Fin i) := ⟨⟨0, hi0⟩⟩
    exact Finset.univ_nonempty
  let δ : W → ℝ := fun f => (Finset.univ.sup' hne (fun j : Fin i => ‖(f.1 j : E)‖))
  rcases Finset.exists_min_image (s := (Finset.univ : Finset W)) δ (Finset.univ_nonempty (α := W)) with
    ⟨fstar, _hfstar_mem, hfstar_min⟩
  let fs : Fin i → L := fstar.1
  have hfs_δle : ∀ j : Fin i, ‖(fs j : E)‖ ≤ δ fstar := by
    intro j
    dsimp [δ, fs]
    exact Finset.le_sup' (s := Finset.univ) (f := fun j : Fin i => ‖(fstar.1 j : E)‖)
      (b := j) (by simp)
  have hδR : δ fstar ≤ R := by
    dsimp [δ]
    exact Finset.sup'_le hne (fun j : Fin i => ‖(fstar.1 j : E)‖)
      (by intro b _; exact fstar.2.2 b)
  have δle_mu : δ fstar ≤ mu := by
    by_contra hnot
    have hgt : mu < δ fstar := lt_of_not_ge hnot
    let s : ℝ := (mu + δ fstar) / 2
    have hmus : mu < s := by dsimp [s]; linarith
    have hsδ : s < δ fstar := by dsimp [s]; linarith
    have hsR : s ≤ R := by
      calc
        s ≤ δ fstar := le_of_lt hsδ
        _ ≤ R := hδR
    rcases mem_successiveMinimumSet_of_sInf_lt L i hmus hS with ⟨_hs0, f_s, hLIs, hbds⟩
    let g : W := ⟨f_s, hLIs, (fun j => le_trans (hbds j) hsR)⟩
    have hgmin : δ fstar ≤ δ g := hfstar_min g (by simp)
    have hgδs : δ g ≤ s := by
      dsimp [δ]
      exact Finset.sup'_le hne (fun j : Fin i => ‖(g.1 j : E)‖)
        (by intro b _; exact hbds b)
    linarith
  refine ⟨fs, ?_, ?_⟩
  · exact fstar.2.1
  · intro j
    exact le_trans (hfs_δle j) δle_mu

/-- **Exact realisation of all successive minima by one nested family**: a full-rank lattice
of `ℤ`-rank `m` admits `m` independent lattice vectors `v₁, …, vₘ` with
`‖vⱼ‖ ≤ λⱼ(L)` where `λⱼ` is the `j`-th successive minimum (indices `j : Fin m` give
`λ` at `j.val + 1`). -/
theorem exact_realization {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (m : ℕ) (hm : Module.finrank ℤ L = m) :
    ∃ v : Fin m → L, LinearIndependent ℝ (fun j : Fin m => (v j : E)) ∧
      ∀ j : Fin m, ‖(v j : E)‖ ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum L (j.val + 1) := by
  classical
  let P : ℕ → Prop := fun i => i ≤ m → ∃ v : Fin i → L,
      LinearIndependent ℝ (fun j : Fin i => (v j : E)) ∧
      ∀ j : Fin i, ‖(v j : E)‖ ≤ successiveMinimum L (j.val + 1)
  have hP0 : P 0 := by
    intro _hi
    refine ⟨fun j => 0, ?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g _hg j
      exact False.elim (Nat.not_lt_zero j.val j.isLt)
    · intro j
      exact False.elim (Nat.not_lt_zero j.val j.isLt)
  have hstep : ∀ i : ℕ, P i → P (i + 1) := by
    intro i hPi hsucc
    rcases hPi (le_trans (Nat.le_succ i) hsucc) with ⟨v, hvLI, hvbd⟩
    have hi_fin : i + 1 ≤ Module.finrank ℤ L := by
      rw [hm]
      exact hsucc
    rcases exists_linearIndependent_eq L (i + 1) (by omega) hi_fin with ⟨y, hyLI, hybd⟩
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
    have hv'bd : ∀ j : Fin (i + 1), ‖(v' j : E)‖ ≤ successiveMinimum L (j.val + 1) := by
      intro j
      by_cases hjeq : j.val = i
      · have hjl : j = Fin.last i := by apply Fin.ext; exact hjeq
        have hxbd : ‖(x : E)‖ ≤ successiveMinimum L (i + 1) := hybd j₀
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

end Commons.Lattice.SuccessiveMinima
