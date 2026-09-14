import Mathlib
import Submission.Subspace.RankDescent
import Submission.Subspace.KTransfer
import Submission.Commons.LinearAlgebra.Matrix.transversal_real_basis_fintype
import Submission.Commons.NumberTheory.Algebraic.complex_re_im_isAlgebraic

/-!
# The complex rank descent follows from the real rank descent

The rank descent `Submission.Subspace.RankDescent L` is stated for a complex system of linear
forms `L : σ → σ → ℂ`.  All the *analytic* difficulties of the complex case (the straightening
step of Davenport's lemma and the volume bookkeeping for boxes defined by complex forms)
disappear over `ℝ`: for real forms the straightening needs only the nearest-integer rounding and
the volume of the box of `N` independent real forms is the naive one.

This file performs the (elementary) reduction.  Given a *transversal real basis* of `L` -- for
each `i`, one of `Re L i`, `Im L i`, chosen so that the resulting real matrix is invertible (the
commons lemma `Commons.LinearAlgebra.Matrix.transversal_real_basis`) -- the box of `L` is
contained in the box of the real system, because `|Re z| ≤ |z|` and `|Im z| ≤ |z|`.  Hence every
solution of the `L`-problem is a solution of the real problem.

The only extra point is the hypothesis "all form values are nonzero" appearing in `RankDescent`:
the real values may vanish on some solutions.  If infinitely many solutions had `M i x = 0` for
one fixed `i`, then `|σ|` of them would lie in the proper subspace `ker (M i ·)` and would be
dependent, contradicting `GenPos`.  Removing finitely many points therefore leaves an infinite
general-position subfamily on which all real values are nonzero, and `RankDescent` for the real
system applies.
-/

open scoped BigOperators

namespace Submission.Subspace

variable {σ : Type*} [Fintype σ]

/-- The real system obtained from the complex system `L` by taking, in row `i`, the real part
(`s i = 0`) or the imaginary part (`s i = 1`). -/
noncomputable def transversalMat (L : σ → σ → ℂ) (s : σ → Fin 2) : σ → σ → ℝ :=
  fun i k => if s i = 0 then (L i k).re else (L i k).im

/-- The rank descent for a *real* system (viewed as a complex system).  This is the statement
that the whole challenge reduces to: over `ℝ` the straightening needs only the nearest-integer
rounding and the box volume is the naive one, so no complex-form obstruction arises. -/
def RankDescentReal (M : σ → σ → ℝ) : Prop := RankDescent (fun i k => (M i k : ℂ))

lemma re_sum_univ' (f : σ → ℂ) : (∑ k, f k).re = ∑ k, (f k).re :=
  map_sum Complex.reCLM f Finset.univ

lemma im_sum_univ' (f : σ → ℂ) : (∑ k, f k).im = ∑ k, (f k).im :=
  map_sum Complex.imCLM f Finset.univ

/-- A value of the transversal system is bounded by the modulus of the corresponding value of
the complex system. -/
lemma transversalMat_apply_le (L : σ → σ → ℂ) (s : σ → Fin 2) (x : σ → ℤ) (i : σ) :
    |∑ k, transversalMat L s i k * (x k : ℝ)| ≤ ‖(∑ k, L i k * (x k : ℂ) : ℂ)‖ := by
  rcases eq_or_ne (s i) (0 : Fin 2) with h | h
  · have h1 : ∀ k, transversalMat L s i k * (x k : ℝ) = (L i k).re * (x k : ℝ) := by
      intro k; simp [transversalMat, h]
    have hsum : ∑ k, transversalMat L s i k * (x k : ℝ) = (∑ k, L i k * (x k : ℂ)).re := by
      rw [Finset.sum_congr rfl (fun k _ => h1 k), re_sum_univ']
      exact Finset.sum_congr rfl fun k _ => by rw [Complex.mul_re]; simp
    rw [hsum]
    exact Complex.abs_re_le_norm _
  · have h1 : ∀ k, transversalMat L s i k * (x k : ℝ) = (L i k).im * (x k : ℝ) := by
      intro k; simp [transversalMat, h]
    have hsum : ∑ k, transversalMat L s i k * (x k : ℝ) = (∑ k, L i k * (x k : ℂ)).im := by
      rw [Finset.sum_congr rfl (fun k _ => h1 k), im_sum_univ']
      exact Finset.sum_congr rfl fun k _ => by rw [Complex.mul_im]; simp
    rw [hsum]
    exact Complex.abs_im_le_norm _

/-- The complex cast of a real value has modulus equal to its absolute value. -/
lemma norm_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h3 : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]
    ring
  calc ‖((r : ℝ) : ℂ)‖ = Real.sqrt (‖((r : ℝ) : ℂ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [h3]
    _ = |r| := Real.sqrt_sq_eq_abs r

/-- The modulus of a transversal value. -/
lemma norm_transversalMat_apply (L : σ → σ → ℂ) (s : σ → Fin 2) (x : σ → ℤ) (i : σ) :
    ‖(∑ k, ((transversalMat L s i k : ℝ) : ℂ) * (x k : ℂ) : ℂ)‖
      = |∑ k, transversalMat L s i k * (x k : ℝ)| := by
  have hcast : (∑ k, ((transversalMat L s i k : ℝ) : ℂ) * (x k : ℂ) : ℂ)
      = ((∑ k, transversalMat L s i k * (x k : ℝ) : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hcast, norm_ofReal]

/-- **The rank descent for `L` follows from the rank descent for a transversal real system.**
The hypothesis `hrow` says that no row of the transversal system vanishes identically (true for
an invertible transversal choice). -/
theorem rankDescent_of_transversal (L : σ → σ → ℂ) (s : σ → Fin 2)
    (hrow : ∀ i : σ, ∃ k : σ, transversalMat L s i k ≠ 0)
    (hRD : RankDescent (fun i k => ((transversalMat L s i k : ℝ) : ℂ))) :
    RankDescent L := by
  classical
  intro c hc hY
  obtain ⟨Y, hYinf, hYgp, hYnz, hYb⟩ := hY
  -- the transversal bounds
  have hMb : ∀ x ∈ Y, ∀ i : σ,
      ‖(∑ k, ((transversalMat L s i k : ℝ) : ℂ) * (x k : ℂ) : ℂ)‖ ≤ ‖x‖ ^ (c i) := by
    intro x hx i
    rw [norm_transversalMat_apply]
    exact (transversalMat_apply_le L s x i).trans (hYb x hx i)
  -- the "bad" set for a fixed row is finite, else `GenPos` is violated
  have hfin : ∀ i : σ,
      {x ∈ Y | ∑ k, transversalMat L s i k * (x k : ℝ) = 0}.Finite := by
    intro i
    by_contra hinf
    -- the `i`-th real form, as a `ℚ`-linear functional on `ℚ^σ`
    let Ψq : (σ → ℚ) →ₗ[ℚ] ℝ :=
      { toFun := fun v => ∑ k, transversalMat L s i k * ((v k : ℚ) : ℝ)
        map_add' := by
          intro a b
          simp only [Pi.add_apply, Rat.cast_add, mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro a b
          show (∑ k, transversalMat L s i k * (((a * b k : ℚ)) : ℝ))
              = (a : ℝ) * (∑ k, transversalMat L s i k * ((b k : ℚ) : ℝ))
          push_cast
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring }
    have hval : Ψq (fun k => if k = i then (1 : ℚ) else 0) = transversalMat L s i i := by
      have hsingle : ∀ k, transversalMat L s i k * (((if k = i then (1 : ℚ) else 0 : ℚ)) : ℝ)
          = if k = i then transversalMat L s i i else 0 := by
        intro k
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      show (∑ k, transversalMat L s i k * (((if k = i then (1 : ℚ) else 0 : ℚ)) : ℝ)) = _
      rw [Finset.sum_congr rfl (fun k _ => hsingle k)]
      simp
    have hWne : LinearMap.ker Ψq ≠ ⊤ := by
      rcases eq_or_ne (transversalMat L s i i) 0 with h0 | h0
      · obtain ⟨k0, hk0⟩ := hrow i
        have hval' : Ψq (fun k => if k = k0 then (1 : ℚ) else 0) = transversalMat L s i k0 := by
          have hsingle : ∀ k,
              transversalMat L s i k * (((if k = k0 then (1 : ℚ) else 0 : ℚ)) : ℝ)
                = if k = k0 then transversalMat L s i k0 else 0 := by
            intro k
            by_cases hk : k = k0
            · subst hk; simp
            · simp [hk]
          show (∑ k, transversalMat L s i k * (((if k = k0 then (1 : ℚ) else 0 : ℚ)) : ℝ)) = _
          rw [Finset.sum_congr rfl (fun k _ => hsingle k)]
          simp
        intro htop
        have hmem : (fun k => if k = k0 then (1 : ℚ) else 0) ∈ LinearMap.ker Ψq := by
          rw [htop]; trivial
        rw [LinearMap.mem_ker, hval'] at hmem
        exact hk0 hmem
      · intro htop
        have hmem : (fun k => if k = i then (1 : ℚ) else 0) ∈ LinearMap.ker Ψq := by
          rw [htop]; trivial
        rw [LinearMap.mem_ker, hval] at hmem
        exact h0 hmem
    have hlt : Module.finrank ℚ (LinearMap.ker Ψq) < Fintype.card σ := by
      have h1 : Module.finrank ℚ (LinearMap.ker Ψq) < Module.finrank ℚ (σ → ℚ) :=
        Submodule.finrank_lt hWne
      rwa [Module.finrank_fintype_fun_eq_card] at h1
    -- choose `|σ|` distinct points of the bad set
    set S : Set (σ → ℤ) := {x ∈ Y | ∑ k, transversalMat L s i k * (x k : ℝ) = 0} with hSdef
    have hSinf : S.Infinite := hinf
    obtain ⟨T, hTS, hTcard⟩ := hSinf.exists_subset_card_eq (Fintype.card σ)
    have hli := hYgp T (fun x hx => (hTS hx).1) (le_of_eq hTcard)
    have hker : ∀ x : T,
        (fun k => ((((x : σ → ℤ) k : ℤ)) : ℚ)) ∈ LinearMap.ker Ψq := by
      intro x
      have hxS : (x : σ → ℤ) ∈ S := hTS x.2
      have h0 : ∑ k, transversalMat L s i k * (((x : σ → ℤ) k : ℤ) : ℝ) = 0 := hxS.2
      show (∑ k, transversalMat L s i k * (((((x : σ → ℤ) k : ℤ)) : ℚ) : ℝ)) = 0
      simpa using h0
    have hliW : LinearIndependent ℚ
        (fun x : T => (⟨fun k => ((((x : σ → ℤ) k : ℤ)) : ℚ), hker x⟩ : LinearMap.ker Ψq)) :=
      LinearIndependent.of_comp (f := Submodule.subtype (LinearMap.ker Ψq)) hli
    have hle := hliW.fintype_card_le_finrank
    rw [Fintype.card_coe, hTcard] at hle
    omega
  -- remove the finitely many points where some transversal value vanishes
  set Z : Set (σ → ℤ) := ⋃ i : σ, {x ∈ Y | ∑ k, transversalMat L s i k * (x k : ℝ) = 0}
    with hZdef
  have hZfin : Z.Finite := Set.finite_iUnion fun i => hfin i
  refine hRD c hc ⟨Y \ Z, hYinf.sdiff hZfin, ?_, ?_, ?_⟩
  · exact fun T hT => hYgp T (fun x hx => (hT hx).1)
  · intro x hx i
    have hxnot : x ∉ Z := hx.2
    have hne : ∑ k, transversalMat L s i k * (x k : ℝ) ≠ 0 := by
      intro hzero
      exact hxnot (Set.mem_iUnion.mpr ⟨i, ⟨hx.1, hzero⟩⟩)
    have hcastne : (∑ k, ((transversalMat L s i k : ℝ) : ℂ) * (x k : ℂ) : ℂ) ≠ 0 := by
      intro hz
      apply hne
      have hre := congrArg Complex.re hz
      rw [re_sum_univ', Complex.zero_re] at hre
      have hterm : ∀ k, (((transversalMat L s i k : ℝ) : ℂ) * (x k : ℂ)).re
          = transversalMat L s i k * (x k : ℝ) := by
        intro k
        rw [Complex.mul_re]
        simp
      rw [Finset.sum_congr rfl (fun k _ => hterm k)] at hre
      exact hre
    exact hcastne
  · intro x hx i
    exact hMb x hx.1 i

variable [DecidableEq σ]

/-- A complex system with independent rows admits a transversal choice whose real matrix is
invertible (the commons transversal-basis lemma). -/
theorem exists_transversalMat_det_ne_zero (L : σ → σ → ℂ) (hL : LinearIndependent ℂ L) :
    ∃ s : σ → Fin 2, (Matrix.of (transversalMat L s)).det ≠ 0 := by
  have hdet : (Matrix.of L).det ≠ 0 := by
    have hrow : LinearIndependent ℂ (Matrix.of L).row := by
      simpa using hL
    have hunit : IsUnit (Matrix.of L) := Matrix.linearIndependent_rows_iff_isUnit.mp hrow
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det (Matrix.of L)).mp hunit)
  obtain ⟨s, hs⟩ :=
    Commons.LinearAlgebra.Matrix.transversal_real_basis_fintype (Matrix.of L) hdet
  exact ⟨s, hs⟩

omit [DecidableEq σ] in
/-- **Assembly of the reduction**: if the rank descent holds for every real algebraic invertible
system, then it holds for `L`. -/
theorem rankDescent_of_rankDescentReal (L : σ → σ → ℂ) (s : σ → Fin 2)
    (hrow : ∀ i : σ, ∃ k : σ, transversalMat L s i k ≠ 0)
    (hRD : RankDescentReal (transversalMat L s)) : RankDescent L :=
  rankDescent_of_transversal L s hrow hRD

/-- **The complex rank descent follows from the real rank descent.**  Any complex algebraic
independent system has a transversal real basis `M` (algebraic, invertible); its box contains the
box of `L`, so `RankDescent L` follows from `RankDescent` for the real system `M`. -/
theorem rankDescent_of_rankDescentReal_algebraic (L : σ → σ → ℂ)
    (alg : ∀ i j, IsAlgebraic ℚ (L i j)) (ind : LinearIndependent ℂ L)
    (hRD : ∀ M : σ → σ → ℝ, (∀ i j, IsAlgebraic ℚ (M i j)) → (Matrix.of M).det ≠ 0 →
      RankDescentReal M) :
    RankDescent L := by
  classical
  obtain ⟨s, hs⟩ := exists_transversalMat_det_ne_zero L ind
  refine rankDescent_of_transversal L s ?_ ?_
  · intro i
    by_contra hcon
    have hzero : ∀ k : σ, transversalMat L s i k = 0 := by
      intro k
      by_contra hk
      exact hcon ⟨k, hk⟩
    exact hs (Matrix.det_eq_zero_of_row_eq_zero i hzero)
  · refine hRD (transversalMat L s) ?_ hs
    intro i j
    rcases eq_or_ne (s i) 0 with h | h
    · simpa [transversalMat, h] using
        (Commons.NumberTheory.Algebraic.complex_re_im_isAlgebraic (alg i j)).1
    · simpa [transversalMat, h] using
        (Commons.NumberTheory.Algebraic.complex_re_im_isAlgebraic (alg i j)).2

end Submission.Subspace
