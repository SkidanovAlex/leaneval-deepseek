import Mathlib
import Submission.Subspace.RealRank.CompoundRank
import Submission.Subspace.RealRank.WedgeCoords
import Submission.Subspace.RealRank.Annihilator
import Submission.Subspace.RealRank.Reindex
import Submission.Subspace.RealRank.CaseA

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Submission.Subspace.RealRank

/-- **Rescaling the exponents** (arbitrary index type). -/
lemma approxBox_rpow_div_gen {σ : Type*} [Fintype σ] (L : σ → σ → ℂ) (c : σ → ℝ) {s Q : ℝ}
    (hs : 0 < s) (hQ : 0 < Q) :
    approxBox L c Q = approxBox L (fun i => c i / s) (Q ^ s) := by
  ext y
  simp only [approxBox, Set.mem_ofPred_eq]
  exact forall_congr' fun i => by
    rw [← Real.rpow_mul hQ.le, mul_div_cancel₀ (c i) (ne_of_gt hs)]

/-- **Finitely many maximal-rank compound spaces.**  For a fixed exponent vector `xbar` with
negative sum, the maximal-rank (`finrank = card ι - 1`) approximation spaces
`approxSpace L xbar Q`, `Q` large, take only finitely many values. -/
theorem maximal_rank_finiteness_spaces {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Matrix ι ι ℂ) (hL : L.det ≠ 0) (hLa : ∀ i j, IsAlgebraic ℚ (L i j))
    (xbar : ι → ℝ) (hxbar : ∑ i, xbar i < 0) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∃ S : Set (Submodule ℚ (ι → ℚ)), S.Finite ∧
      ∀ Q : ℝ, Q₀ ≤ Q → Module.finrank ℚ (approxSpace L xbar Q) = Fintype.card ι - 1 →
        approxSpace L xbar Q ∈ S := by
  classical
  have hne : (Finset.univ : Finset ι).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    by_contra h
    rw [not_nonempty_iff] at h
    haveI := h
    simp at hxbar
  set s : ℝ := max 1 ((Finset.univ : Finset ι).sup' hne xbar) with hsdef
  have hs1 : 1 ≤ s := le_max_left _ _
  have hspos : 0 < s := lt_of_lt_of_le one_pos hs1
  have hsx : ∀ i : ι, xbar i ≤ s := fun i =>
    le_trans (Finset.le_sup' (s := (Finset.univ : Finset ι)) (f := xbar) (Finset.mem_univ i))
      (le_max_right _ _)
  set γ : ι → ℝ := fun i => xbar i / s with hγdef
  have hγ1 : ∀ i, γ i ≤ 1 := by
    intro i
    rw [hγdef, div_le_one hspos]
    exact hsx i
  have hγsum : ∑ i, γ i < 0 := by
    rw [hγdef, ← Finset.sum_div]
    exact div_neg_of_neg_of_pos hxbar hspos
  obtain ⟨Q₀, hQ₀1, S, hSfin, hS⟩ := maximal_rank_finiteness_reindex L hL hLa γ hγ1 hγsum
  refine ⟨max 1 (Q₀ ^ (1 / s)), le_max_left _ _, S, hSfin, fun Q hQ hfr => ?_⟩
  have hQ1 : 1 ≤ Q := le_trans (le_max_left _ _) hQ
  have hQpos : 0 < Q := lt_of_lt_of_le one_pos hQ1
  have hQQ : Q₀ ^ (1 / s) ≤ Q := le_trans (le_max_right _ _) hQ
  have hQspos : Q₀ ≤ Q ^ s := by
    have h1 : (Q₀ ^ (1 / s)) ^ s ≤ Q ^ s :=
      Real.rpow_le_rpow (Real.rpow_nonneg (le_trans zero_le_one hQ₀1) _) hQQ hspos.le
    rwa [← Real.rpow_mul (le_trans zero_le_one hQ₀1), one_div_mul_cancel (ne_of_gt hspos),
      Real.rpow_one] at h1
  have heq : approxSpace L xbar Q = approxSpace L γ (Q ^ s) := by
    unfold approxSpace
    rw [approxBox_rpow_div_gen L xbar hspos hQpos]
  have hfr' : Module.finrank ℚ (approxSpace L γ (Q ^ s)) = Fintype.card ι - 1 := by
    rw [← heq]; exact hfr
  rw [heq]
  exact hS (Q ^ s) hQspos hfr'

/-- The compound box of a real matrix spans the same space as the `approxSpace` of its
complexification. -/
lemma approxSpace_toC_compBox_eq {N r : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (xbar : Idx N r → ℝ)
    (Q : ℝ) :
    approxSpace (toC (Commons.LinearAlgebra.Matrix.compound r M)) xbar Q
      = Submodule.span ℚ (intCastVec '' compBox r M xbar Q) := by
  unfold approxSpace
  rw [approxBox_toC]
  rfl

/-! ## The `Idx`/`Set.powersetCard` bridge -/

/-- A `Set.powersetCard` element as an `Idx`. -/
def ofPC {N r : ℕ} (S : Set.powersetCard (Fin N) r) : Idx N r := ⟨S.1, S.2⟩

/-- An `Idx` element as a `Set.powersetCard` element. -/
def toPC {N r : ℕ} (S : Idx N r) : Set.powersetCard (Fin N) r := ⟨S.1, S.2⟩

/-- The `S`-th column of the compound matrix, indexed by `Set.powersetCard`. -/
noncomputable def compoundCol {N r : ℕ} (Vmat : Matrix (Fin N) (Fin N) ℚ)
    (S : Set.powersetCard (Fin N) r) : Idx N r → ℚ :=
  fun T => (Commons.LinearAlgebra.Matrix.compound r Vmat) T (ofPC S)

lemma wedgeEquiv_compoundCol {N r : ℕ} (Vmat : Matrix (Fin N) (Fin N) ℚ)
    (S : Set.powersetCard (Fin N) r) :
    wedgeEquiv N r (compoundCol Vmat S)
      = exteriorPower.ιMulti_family ℚ r (fun j : Fin N => fun i : Fin N => Vmat i j) S :=
  wedgeEquiv_compound_col Vmat (ofPC S)

/-- The span of the compound columns, in the two index spellings. -/
lemma span_compoundCol_eq {N r : ℕ} (Vmat : Matrix (Fin N) (Fin N) ℚ)
    (Tstar : Set.powersetCard (Fin N) r) :
    Submodule.span ℚ (Set.range (fun S : {S : Set.powersetCard (Fin N) r // S ≠ Tstar} =>
      compoundCol Vmat S))
    = Submodule.span ℚ (Set.range (fun S : {S : Idx N r // S ≠ ofPC Tstar} =>
      (fun T => (Commons.LinearAlgebra.Matrix.compound r Vmat) T S))) := by
  rw [show (fun S : {S : Set.powersetCard (Fin N) r // S ≠ Tstar} => compoundCol Vmat S)
      = (fun S : {S : Idx N r // S ≠ ofPC Tstar} =>
          (fun T => (Commons.LinearAlgebra.Matrix.compound r Vmat) T S)) from rfl]
  rfl

/-- The annihilator kernel of the wedge of the first `k` columns is the `wedgeEquiv`-image of the
span of the compound columns. -/
theorem ker_eq_span_wedge {N r k : ℕ} (hrk : r + k = N)
    (Vmat : Matrix (Fin N) (Fin N) ℚ) (hV : Vmat.det ≠ 0)
    (Tstar : Set.powersetCard (Fin N) r) (t : Set.powersetCard (Fin N) k)
    (ht : (↑t : Finset (Fin N)) = (↑Tstar)ᶜ) :
    LinearMap.ker (wedgePairLinLeft hrk (exteriorPower.ιMulti_family ℚ k
        (fun j : Fin N => fun i : Fin N => Vmat i j) t))
      = Submodule.span ℚ (Set.range (fun S : {S : Set.powersetCard (Fin N) r // S ≠ Tstar} =>
          exteriorPower.ιMulti_family ℚ r (fun j : Fin N => fun i : Fin N => Vmat i j)
            (S : Set.powersetCard (Fin N) r))) := by
  have hli : LinearIndependent ℚ (fun j : Fin N => fun i : Fin N => Vmat i j) := by
    have hunit : IsUnit Vmat := (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hV)
    exact Matrix.linearIndependent_cols_iff_isUnit.mpr hunit
  exact ker_wedgePairLinLeft_eq_span hrk (fun j : Fin N => fun i : Fin N => Vmat i j) hli
    Tstar t ht

lemma map_wedgeEquiv_span_compoundCol {N r : ℕ} (Vmat : Matrix (Fin N) (Fin N) ℚ)
    (Tstar : Set.powersetCard (Fin N) r) :
    Submodule.map ((wedgeEquiv N r : (Idx N r → ℚ) →ₗ[ℚ] (⋀[ℚ]^r (Fin N → ℚ))))
      (Submodule.span ℚ (Set.range
        (fun S : {S : Set.powersetCard (Fin N) r // S ≠ Tstar} =>
          compoundCol Vmat (S : Set.powersetCard (Fin N) r))))
    = Submodule.span ℚ (Set.range (fun S : {S : Set.powersetCard (Fin N) r // S ≠ Tstar} =>
        exteriorPower.ιMulti_family ℚ r (fun j : Fin N => fun i : Fin N => Vmat i j)
          (S : Set.powersetCard (Fin N) r))) := by
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨S, rfl⟩, rfl⟩
    exact ⟨S, (wedgeEquiv_compoundCol Vmat (S : Set.powersetCard (Fin N) r)).symm⟩
  · rintro ⟨S, rfl⟩
    exact ⟨compoundCol Vmat S, ⟨⟨S, S.2⟩, rfl⟩,
      wedgeEquiv_compoundCol Vmat (S : Set.powersetCard (Fin N) r)⟩

/-- **The compound hyperplane determines the descended space.**  If two invertible integer
matrices give the same span of compound columns, then the spans of their first `k` columns (the
"descended spaces" `W`) agree. -/
theorem wedgeSpan_eq_of_compoundSpan_eq {N r k : ℕ} (hrk : r + k = N)
    (Vmat Vmat' : Matrix (Fin N) (Fin N) ℚ) (hV : Vmat.det ≠ 0) (hV' : Vmat'.det ≠ 0)
    (Tstar : Set.powersetCard (Fin N) r) (t : Set.powersetCard (Fin N) k)
    (ht : (↑t : Finset (Fin N)) = (↑Tstar)ᶜ)
    (heq : Submodule.span ℚ (Set.range (fun S : {S : Set.powersetCard (Fin N) r // S ≠ Tstar} =>
              compoundCol Vmat (S : Set.powersetCard (Fin N) r)))
          = Submodule.span ℚ (Set.range (fun S : {S : Set.powersetCard (Fin N) r // S ≠ Tstar} =>
              compoundCol Vmat' (S : Set.powersetCard (Fin N) r)))) :
    Submodule.span ℚ ((fun j : Fin N => fun i : Fin N => Vmat i j) '' (↑t : Set (Fin N)))
      = Submodule.span ℚ ((fun j : Fin N => fun i : Fin N => Vmat' i j) '' (↑t : Set (Fin N))) := by
  have hli : LinearIndependent ℚ (fun j : Fin N => fun i : Fin N => Vmat i j) := by
    have hunit : IsUnit Vmat := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hV)
    exact Matrix.linearIndependent_cols_iff_isUnit.mpr hunit
  have hli' : LinearIndependent ℚ (fun j : Fin N => fun i : Fin N => Vmat' i j) := by
    have hunit : IsUnit Vmat' := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hV')
    exact Matrix.linearIndependent_cols_iff_isUnit.mpr hunit
  have hker : LinearMap.ker (wedgePairLinLeft hrk (exteriorPower.ιMulti_family ℚ k
        (fun j : Fin N => fun i : Fin N => Vmat i j) t))
      = LinearMap.ker (wedgePairLinLeft hrk (exteriorPower.ιMulti_family ℚ k
        (fun j : Fin N => fun i : Fin N => Vmat' i j) t)) := by
    calc LinearMap.ker (wedgePairLinLeft hrk (exteriorPower.ιMulti_family ℚ k
            (fun j : Fin N => fun i : Fin N => Vmat i j) t))
        = Submodule.span ℚ (Set.range (fun S : {S : Set.powersetCard (Fin N) r // S ≠ Tstar} =>
            exteriorPower.ιMulti_family ℚ r (fun j : Fin N => fun i : Fin N => Vmat i j)
              (S : Set.powersetCard (Fin N) r))) :=
          ker_eq_span_wedge hrk Vmat hV Tstar t ht
      _ = Submodule.map ((wedgeEquiv N r : (Idx N r → ℚ) →ₗ[ℚ] (⋀[ℚ]^r (Fin N → ℚ))))
            (Submodule.span ℚ (Set.range
              (fun S : {S : Set.powersetCard (Fin N) r // S ≠ Tstar} =>
                compoundCol Vmat (S : Set.powersetCard (Fin N) r)))) :=
          (map_wedgeEquiv_span_compoundCol Vmat Tstar).symm
      _ = Submodule.map ((wedgeEquiv N r : (Idx N r → ℚ) →ₗ[ℚ] (⋀[ℚ]^r (Fin N → ℚ))))
            (Submodule.span ℚ (Set.range
              (fun S : {S : Set.powersetCard (Fin N) r // S ≠ Tstar} =>
                compoundCol Vmat' (S : Set.powersetCard (Fin N) r)))) := by
          rw [heq]
      _ = Submodule.span ℚ (Set.range (fun S : {S : Set.powersetCard (Fin N) r // S ≠ Tstar} =>
            exteriorPower.ιMulti_family ℚ r (fun j : Fin N => fun i : Fin N => Vmat' i j)
              (S : Set.powersetCard (Fin N) r))) :=
          map_wedgeEquiv_span_compoundCol Vmat' Tstar
      _ = LinearMap.ker (wedgePairLinLeft hrk (exteriorPower.ιMulti_family ℚ k
            (fun j : Fin N => fun i : Fin N => Vmat' i j) t)) :=
          (ker_eq_span_wedge hrk Vmat' hV' Tstar t ht).symm
  exact span_image_eq_of_ker_eq hrk _ _ hli hli' Tstar t ht hker

/-- A function constant on the fibres of a function with finite range has finite range. -/
lemma range_finite_of_key {α β γ : Type*} (f : α → β) (g : α → γ)
    (hfin : (Set.range f).Finite) (key : ∀ a b, f a = f b → g a = g b) :
    (Set.range g).Finite := by
  classical
  haveI : Fintype (Set.range f) := hfin.fintype
  set F : Set.range f → γ := fun x => g (Classical.choose x.2) with hF
  have hFspec : ∀ x : Set.range f, f (Classical.choose x.2) = (x : β) :=
    fun x => Classical.choose_spec x.2
  have hsub : Set.range g ⊆ Set.range F := by
    rintro z ⟨a, rfl⟩
    refine ⟨⟨f a, a, rfl⟩, ?_⟩
    rw [hF]
    exact key _ a (hFspec ⟨f a, a, rfl⟩)
  exact (Set.finite_range F).subset hsub

end Submission.Subspace.RealRank
