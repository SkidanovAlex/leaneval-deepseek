import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.LogDefs
import Submission.NK.GlobalCFTdeep.Herbrand.finrank_tUnits
import Submission.NK.GlobalCFTdeep.LogLattice.InfSumZero
import Submission.NK.GlobalCFTdeep.LogLattice.sum_logVec_eq_zero
import Submission.NK.GlobalCFTdeep.LogLattice.finite_ker_logVecLin
import Submission.NK.GlobalCFTdeep.LogLattice.span_unitsToTUnits_logVecLin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.LogLattice

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- At a finite place lying in `T`, a `T`-unit whose `q`-adic valuation vanishes has vanishing log
coordinate: a local unit has normalized absolute value `1`. -/
theorem logVec_ofFinite_eq_zero_of_expUnit_eq_zero
    (T : Set (Place L)) (a : Lˣ) (q : HeightOneSpectrum (𝓞 L)) (hq : Place.ofFinite q ∈ T)
    (h : NK.GlobalCFTdeep.expUnit q a = 0) :
    NK.GlobalCFTdeep.logVec (L := L) T a ⟨Place.ofFinite q, hq⟩ = 0 := by
  rw [show NK.GlobalCFTdeep.logVec (L := L) T a ⟨Place.ofFinite q, hq⟩ =
    Real.log ((Idele.localAbs L (Place.ofFinite q)
      (Idele.principalIdele L a (Place.ofFinite q)) : ℝˣ) : ℝ) from rfl]
  rw [Idele.principalIdele_apply,
    Idele.localAbs_ofFinite_eq_one
      ((NK.GlobalCFTdeep.expUnit_eq_zero_iff_mem_localUnits q a).mp h)]
  simp

/-- **The finite places contribute triangular log vectors.**  For every finite place `q` lying in
`T` there is a `T`-unit whose log vector is non-zero at `q` and vanishes at every other finite
place of `T`.

Indeed, the ideal class group of `L` is finite, so some positive power `q ^ N` of `q` is principal;
a generator `a` of `q ^ N` has `q`-adic valuation `N ≠ 0` and vanishing valuation at every other
finite place, i.e. is a `T`-unit (`NK.GlobalCFTdeep.tUnits_family_diag`), and the log coordinate
at a finite place vanishes exactly when the valuation does
(`NK.GlobalCFTdeep.LogLattice.expUnit_eq_zero_of_logVec_eq_zero` and
`NK.GlobalCFTdeep.LogLattice.logVec_ofFinite_eq_zero_of_expUnit_eq_zero`). -/
theorem exists_triangular_logVec {K : Type} [Field K] [NumberField K] [Algebra K L]
    (T : Set (Place L)) [Finite T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) :
    ∃ a : NK.GlobalCFTdeep.SSet T → NK.GlobalCFTdeep.TUnits T,
      (∀ q : NK.GlobalCFTdeep.SSet T,
        NK.GlobalCFTdeep.logVec (L := L) T ((a q : NK.GlobalCFTdeep.TUnits T) : Lˣ)
          ⟨Place.ofFinite q.1, NK.GlobalCFTdeep.mem_SSet.mp q.2⟩ ≠ 0) ∧
      (∀ q q' : NK.GlobalCFTdeep.SSet T, q' ≠ q →
        NK.GlobalCFTdeep.logVec (L := L) T ((a q : NK.GlobalCFTdeep.TUnits T) : Lˣ)
          ⟨Place.ofFinite q'.1, NK.GlobalCFTdeep.mem_SSet.mp q'.2⟩ = 0) := by
  classical
  obtain ⟨N, hN, adiag, hdiagN, hdiag0⟩ :=
    NK.GlobalCFTdeep.tUnits_family_diag (L := L) T
      (fun q => NK.GlobalCFTdeep.Herbrand.exists_expUnit_eq_single q)
  refine ⟨adiag, fun q => ?_, fun q q' hne => ?_⟩
  · intro hz
    have h0 := expUnit_eq_zero_of_logVec_eq_zero (K := K) T
      (((adiag q : NK.GlobalCFTdeep.TUnits T)) : Lˣ) q.1 (NK.GlobalCFTdeep.mem_SSet.mp q.2) hz
    rw [hdiagN q] at h0
    exact (Nat.cast_ne_zero.mpr hN.ne') h0
  · exact logVec_ofFinite_eq_zero_of_expUnit_eq_zero T _ q'.1
      (NK.GlobalCFTdeep.mem_SSet.mp q'.2) (hdiag0 q q' hne)

/-- **The `S`-unit statement in lattice form** (Milne, *CFT*, Chapter VII §3, the input of
Proposition 3.1): the `ℝ`-span of the log lattice of the `T`-units, together with the all-ones
vector `e`, is the whole space `↥T → ℝ`.  Equivalently the log lattice is a *full* lattice in the
sum-zero hyperplane, i.e. the `T`-units have the largest possible rank `|T| - 1`.

The proof (formalized below) establishes the two steps:

* **Step 1** (`span ℝ (range logVecLin) = sumZero T`).  `NK.GlobalCFTdeep.sumZero T` is the
  sum-zero hyperplane.  The inclusion `⊆` is the product formula
  (`NK.GlobalCFTdeep.LogLattice.sum_logVec_eq_zero`); for the reverse inclusion, Dirichlet's unit
  theorem in lattice form
  (`NK.GlobalCFTdeep.LogLattice.span_unitsToTUnits_logVecLin`) supplies the purely infinite part
  (`NK.GlobalCFTdeep.LogLattice.infSumZero T`) of the log lattice, while the finite places are
  handled by the triangular family of `T`-units with a single non-vanishing valuation
  (`NK.GlobalCFTdeep.LogLattice.exists_triangular_logVec`, from the finiteness of the class
  group): any vector of the sum-zero hyperplane can be matched in its finite coordinates by an
  `ℝ`-combination of the log lattice, and the difference lies in the purely infinite part.
* **Step 2** (`sumZero T ⊔ ℝ ∙ oneVec T = ⊤`).  `oneVec T ∉ sumZero T` (the sum of its coordinates
  is `Nat.card T ≠ 0`, since `T` contains all infinite places and there is at least one), so
  `v - (∑ v / |T|) • oneVec T ∈ sumZero T` and
  `Submodule.span ℝ (S ∪ {oneVec T}) = span ℝ S ⊔ span ℝ {oneVec T}`. -/
theorem span_logVecLin_oneVec {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (T : Set (NK.GlobalCFT.Place L)) [Finite T]
    (hTinf : ∀ w : NK.GlobalCFT.Place L, w.IsInfinite → w ∈ T) :
    Submodule.span ℝ (Set.range (NK.GlobalCFTdeep.logVecLin (L := L) T) ∪
      {NK.GlobalCFTdeep.oneVec T}) = ⊤ := by
  classical
  haveI : Fintype ↥T := Fintype.ofFinite T
  haveI : Fintype (NK.GlobalCFTdeep.SSet T) := Fintype.ofFinite _
  -- `T` is nonempty: it contains every infinite place, and there is at least one.
  have hTne : Nonempty ↥T := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace L))
    exact ⟨⟨Place.ofInfinite w, hTinf _ trivial⟩⟩
  have hTnz : (Nat.card ↥T : ℝ) ≠ 0 := by
    have h : Nat.card ↥T ≠ 0 := Nat.card_ne_zero.mpr ⟨hTne, inferInstance⟩
    exact_mod_cast h
  -- The log lattice lies in the sum-zero hyperplane (product formula).
  have hle : Submodule.span ℝ (Set.range (NK.GlobalCFTdeep.logVecLin (L := L) T)) ≤
      NK.GlobalCFTdeep.sumZero (L := L) T := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine NK.GlobalCFTdeep.mem_sumZero.mpr ?_
    rw [NK.GlobalCFTdeep.logVecLin_apply]
    exact sum_logVec_eq_zero (K := K) T hTinf
      (((Additive.toMul a : NK.GlobalCFTdeep.TUnits T)) : Lˣ) (Additive.toMul a).2
  -- The units span the purely infinite sum-zero subspace (Dirichlet).
  have hinf_le : infSumZero (L := L) T ≤
      Submodule.span ℝ (Set.range (NK.GlobalCFTdeep.logVecLin (L := L) T)) := by
    rw [← span_unitsToTUnits_logVecLin (K := K) T hTinf]
    refine Submodule.span_mono ?_
    rintro _ ⟨u, rfl⟩
    exact ⟨NK.GlobalCFTdeep.unitsToTUnits (L := L) T u, rfl⟩
  -- **Step 1**: the log lattice spans the whole sum-zero hyperplane.
  have hW : Submodule.span ℝ (Set.range (NK.GlobalCFTdeep.logVecLin (L := L) T)) =
      NK.GlobalCFTdeep.sumZero (L := L) T := by
    refine le_antisymm hle ?_
    intro v hv
    obtain ⟨a, ha0, ha1⟩ := exists_triangular_logVec (K := K) T hTinf
    set lam : NK.GlobalCFTdeep.SSet T → ℝ := fun q =>
      v ⟨Place.ofFinite q.1, NK.GlobalCFTdeep.mem_SSet.mp q.2⟩ /
        NK.GlobalCFTdeep.logVec (L := L) T ((a q : NK.GlobalCFTdeep.TUnits T) : Lˣ)
          ⟨Place.ofFinite q.1, NK.GlobalCFTdeep.mem_SSet.mp q.2⟩ with hlam
    set x : ↥T → ℝ := ∑ q : NK.GlobalCFTdeep.SSet T,
      lam q • NK.GlobalCFTdeep.logVecLin (L := L) T (Additive.ofMul (a q)) with hx
    have hxW : x ∈ Submodule.span ℝ (Set.range (NK.GlobalCFTdeep.logVecLin (L := L) T)) := by
      rw [hx]
      refine Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span ⟨Additive.ofMul (a q), rfl⟩
    -- `x` agrees with `v` at the finite places of `T`.
    have hxfin : ∀ q₀ : NK.GlobalCFTdeep.SSet T,
        x ⟨Place.ofFinite q₀.1, NK.GlobalCFTdeep.mem_SSet.mp q₀.2⟩ =
          v ⟨Place.ofFinite q₀.1, NK.GlobalCFTdeep.mem_SSet.mp q₀.2⟩ := by
      intro q₀
      rw [hx, Finset.sum_apply, Finset.sum_eq_single q₀]
      · rw [Pi.smul_apply, smul_eq_mul, hlam]
        exact div_mul_cancel₀ _ (ha0 q₀)
      · intro q _ hne
        rw [Pi.smul_apply, smul_eq_mul]
        exact mul_eq_zero_of_right _ (ha1 q q₀ hne.symm)
      · intro h; exact absurd (Finset.mem_univ q₀) h
    have hxsum : ∑ w : ↥T, x w = 0 := NK.GlobalCFTdeep.mem_sumZero.mp (hle hxW)
    have hvsum : ∑ w : ↥T, v w = 0 := NK.GlobalCFTdeep.mem_sumZero.mp hv
    have hdiff : v - x ∈ infSumZero (L := L) T := by
      refine ⟨fun q => ?_, ?_⟩
      · rw [Pi.sub_apply, hxfin q, sub_self]
      · simp only [Pi.sub_apply]
        rw [Finset.sum_sub_distrib, hvsum, hxsum, sub_zero]
    have : v = x + (v - x) := by abel
    rw [this]
    exact Submodule.add_mem _ hxW (hinf_le hdiff)
  -- **Step 2**: adjoining the all-ones vector gives the whole space.
  have hone : ∀ v : ↥T → ℝ, v ∈ NK.GlobalCFTdeep.sumZero (L := L) T ⊔
      Submodule.span ℝ ({NK.GlobalCFTdeep.oneVec (L := L) T} : Set (↥T → ℝ)) := by
    intro v
    have hsum1 : (∑ w : ↥T, NK.GlobalCFTdeep.oneVec (L := L) T w) = (Nat.card ↥T : ℝ) := by
      simp [NK.GlobalCFTdeep.oneVec]
    have h1ne : (∑ w : ↥T, NK.GlobalCFTdeep.oneVec (L := L) T w) ≠ 0 := by
      rw [hsum1]; exact hTnz
    have hsub : v - ((∑ w : ↥T, v w) / (∑ w : ↥T, NK.GlobalCFTdeep.oneVec (L := L) T w)) •
        NK.GlobalCFTdeep.oneVec (L := L) T ∈ NK.GlobalCFTdeep.sumZero (L := L) T := by
      rw [NK.GlobalCFTdeep.mem_sumZero]
      simp only [Pi.sub_apply]
      rw [Finset.sum_sub_distrib]
      rw [show (∑ w : ↥T, (((∑ w : ↥T, v w) /
          (∑ w : ↥T, NK.GlobalCFTdeep.oneVec (L := L) T w)) •
            NK.GlobalCFTdeep.oneVec (L := L) T) w) =
          ((∑ w : ↥T, v w) / (∑ w : ↥T, NK.GlobalCFTdeep.oneVec (L := L) T w)) *
            ∑ w : ↥T, NK.GlobalCFTdeep.oneVec (L := L) T w from ?_]
      · rw [div_mul_cancel₀ _ h1ne, sub_self]
      · simp only [Pi.smul_apply, smul_eq_mul]
        exact (Finset.mul_sum _ _ _).symm
    refine Submodule.mem_sup.mpr ⟨_, hsub,
      ((∑ w : ↥T, v w) / (∑ w : ↥T, NK.GlobalCFTdeep.oneVec (L := L) T w)) •
        NK.GlobalCFTdeep.oneVec (L := L) T,
      Submodule.smul_mem
        (Submodule.span ℝ ({NK.GlobalCFTdeep.oneVec (L := L) T} : Set (↥T → ℝ))) _
        (Submodule.subset_span (Set.mem_singleton _)), by abel⟩
  have htop : NK.GlobalCFTdeep.sumZero (L := L) T ⊔
      Submodule.span ℝ ({NK.GlobalCFTdeep.oneVec (L := L) T} : Set (↥T → ℝ)) = ⊤ :=
    eq_top_iff.mpr fun v _ => hone v
  rw [Submodule.span_union, hW, htop]

end NK.GlobalCFTdeep.LogLattice
