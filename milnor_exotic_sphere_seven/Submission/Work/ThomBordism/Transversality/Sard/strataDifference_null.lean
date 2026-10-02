import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.Strat
import Submission.Work.ThomBordism.Transversality.Sard.scalarPartial
import Submission.Work.ThomBordism.Transversality.Sard.criticalSet_closed
import Submission.Work.ThomBordism.Transversality.Sard.levelSet_null
import Submission.Work.ThomBordism.Transversality.Sard.volume_image_null_of_local

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The vanishing strata of the critical set are null (the hypersurface step of Sard's theorem)

The stratification of the critical set of a `C^∞` map `f : ℝ^{n+1} → ℝ^m` is
`Zk f 1 ⊇ Zk f 2 ⊇ …` with `Zk f k` the set of points at which all iterated derivatives of `f` of
orders `1, …, k` vanish.  This file proves that the image of each **stratum difference**
`Zk f k \ Zk f (k+1)` (`k ≥ 1`) is Lebesgue-null, **given** Sard's theorem for `C^∞` maps
`ℝ^n → ℝ^m` (`SardEuclidOn n m`) — the induction hypothesis with the *source* dimension lowered by
one.  Together with the non-flat piece and the flat piece, this is one of the three steps consumed
by `Sard.SardSteps` / `Sard.sardEuclidOn_of_steps`.

## The mathematics

Fix `x ∈ Zk f k \ Zk f (k+1)` inside the open set `U`.  Since the derivatives of orders `≤ k` vanish
at `x` but those of order `k+1` do not, there is a scalar function `σ` of the form

`σ(y) = v (D^k f(y) (w₁, …, w_k))`

(a coordinate of the `k`-th iterated derivative of `f` evaluated on fixed vectors) with

* `σ` is `C^∞` near `x` (a composition of continuous linear maps with `y ↦ D^k f(y)`, which is
  `C^∞` because `f` is),
* `σ` vanishes identically on `Zk f k` (all derivatives of order `k` vanish there), and
* `fderiv ℝ σ x ≠ 0` (this is the explicit computation identifying `dσ_x` with the `(k+1)`-st
  derivative of `f` at `x`, exactly as in `Sard.scalarPartial`).

Hence `Zk f k \ Zk f (k+1)` lies, near `x`, in the regular level set `{σ = 0}` — a smooth
hypersurface — and the restriction of `f` to that hypersurface is a `C^∞` map on an
`n`-dimensional space on which the points of the stratum are still critical (they are critical for
`f` itself, because `Zk f k ⊆ Zk f 1 = {fderiv f = 0}`).  Sard's theorem in the *lower* dimension
`n`, i.e. the induction hypothesis, applied to the restriction gives the nullity of the image
locally; a countable-cover argument globalizes.

The ingredients, in the order in which they are used:

* `Sard.scalarVanishingHypersurface` — the local scalar `σ` above, together with the open set on
  which its derivative does not vanish (this is `Sard.scalarPartial` with the global smoothness
  hypothesis localized, plus the openness of `{dσ ≠ 0}`);
* `Sard.isCriticalPoint_of_mem_Zk_one` — a point of `Zk f 1` is critical when the target is
  non-trivial;
* `Sard.levelSet_null` — the image of a critical set inside a regular level set is null (proved
  from the induction hypothesis by straightening the hypersurface).

The degenerate case `m = 0` (the target is a point, so `f` is constant and every `Zk f k` is
everything) is handled by `Sard.Zk_eq_univ_of_subsingleton`.

All statements are for the concrete spaces `EuclideanSpace ℝ (Fin _)`.
-/

open scoped ContDiff MeasureTheory
open MeasureTheory Set

namespace Work.ThomBordism.Transversality.Sard

open Work.ThomBordism.Transversality (CInf CInfOn VanishToOrder Zk IsCriticalPoint SardEuclidOn)

noncomputable section

set_option maxHeartbeats 800000

/-! ## Elementary bookkeeping about the strata -/

/-- **In a subsingleton target every iterated derivative vanishes.** -/
theorem iteratedFDeriv_eq_zero_of_subsingleton {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [Subsingleton F]
    (f : E → F) (j : ℕ) (x : E) : iteratedFDeriv ℝ j f x = 0 := by
  ext m
  exact Subsingleton.elim _ _

/-- **If the target is a subsingleton, all the strata `Zk f k` are everything.** -/
theorem Zk_eq_univ_of_subsingleton {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [Subsingleton F]
    (f : E → F) (k : ℕ) : Zk f k = univ := by
  ext x
  simp only [mem_Zk, Set.mem_univ, iff_true]
  intro j _ _
  exact iteratedFDeriv_eq_zero_of_subsingleton f j x

/-- **The failing order is the top one.**  If `x ∈ Zk f k` but `x ∉ Zk f (k+1)`, then the
`(k+1)`-st iterated derivative of `f` at `x` does not vanish: the derivatives of orders `1, …, k`
already do, so the order at which `VanishToOrder f (k+1)` fails must be `k+1`. -/
theorem iteratedFDeriv_succ_ne_zero_of_mem_Zk_diff {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {k : ℕ} {x : E} (hxk : x ∈ Zk f k) (hxk' : x ∉ Zk f (k+1)) :
    iteratedFDeriv ℝ (k+1) f x ≠ 0 := by
  intro h
  refine hxk' fun j hj1 hjk => ?_
  rcases lt_or_eq_of_le hjk with hlt | heq
  · exact hxk j hj1 (by omega)
  · exact heq ▸ h

/-- **Points with vanishing derivative are critical when the target is non-trivial.** -/
theorem isCriticalPoint_of_mem_Zk_one {n m : ℕ} (hm : 1 ≤ m)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Zk f 1) : IsCriticalPoint f x := by
  have hzero : fderiv ℝ f x = 0 := (vanishToOrder_one_iff).mp hx
  intro hsurj
  have hsub : Subsingleton (EuclideanSpace ℝ (Fin m)) :=
    ⟨fun a b => by
      obtain ⟨v, hv⟩ := hsurj a
      obtain ⟨w, hw⟩ := hsurj b
      rw [hzero] at hv hw
      simp only [ContinuousLinearMap.zero_apply] at hv hw
      rw [← hv, ← hw]⟩
  have hnt : Nontrivial (EuclideanSpace ℝ (Fin m)) := by
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    infer_instance
  exact (not_subsingleton_iff_nontrivial.mpr hnt) hsub

/-! ## The local scalar vanishing on a stratum, with non-vanishing derivative -/

/-- **The vanishing-stratum hypersurface.**  Let `f : ℝⁿ → ℝᵐ` be `C^∞` on an open set `U` and let
`x ∈ U` be a point of the stratum difference `Zk f k \ Zk f (k+1)`, `k ≥ 1`.  Then there are a
scalar function `σ` and an open neighbourhood `W ⊆ U` of `x` such that `σ` is `C^∞` on `W`,
vanishes on `Zk f k ∩ W`, and has non-vanishing derivative at every point of `W`.

The construction is that of `Sard.scalarPartial`: `σ` is a coordinate of the `k`-th iterated
derivative of `f` evaluated on fixed vectors, so it vanishes wherever the `k`-th derivative does;
`dσ_x` is the `(k+1)`-st derivative of `f` at `x` on the fixed vectors, hence non-zero.  As `dσ` is
continuous, `{dσ ≠ 0}` is an open neighbourhood of `x`, and `W` is its intersection with `U`. -/
theorem scalarVanishingHypersurface {n m k : ℕ} (hk : 1 ≤ k)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : CInfOn f U)
    {x : EuclideanSpace ℝ (Fin n)} (hxU : x ∈ U)
    (hxk : x ∈ Zk f k) (hxk' : x ∉ Zk f (k+1)) :
    ∃ (σ : EuclideanSpace ℝ (Fin n) → ℝ) (W : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ CInfOn σ W ∧
      (∀ y ∈ W, y ∈ Zk f k → σ y = 0) ∧ ∀ y ∈ W, fderiv ℝ σ y ≠ 0 := by
  classical
  have hfd : iteratedFDeriv ℝ (k+1) f x ≠ 0 :=
    iteratedFDeriv_succ_ne_zero_of_mem_Zk_diff hxk hxk'
  -- a non-vanishing value of the `(k+1)`-st derivative, and one of its coordinates
  obtain ⟨mm, hm⟩ : ∃ mm : Fin (k+1) → EuclideanSpace ℝ (Fin n),
      (iteratedFDeriv ℝ (k+1) f x) mm ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hfd (ContinuousMultilinearMap.ext hc)
  obtain ⟨j, hj⟩ : ∃ j : Fin m, ((iteratedFDeriv ℝ (k+1) f x) mm).ofLp j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hm (PiLp.ext fun i => by simpa using hc i)
  -- the two continuous linear maps appearing in the scalar partial
  set A : ContinuousMultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin m)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin m)) (Fin.tail mm) with hA
  set v : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin m => ℝ) j with hv
  set σ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => v (A (iteratedFDeriv ℝ k f y)) with hσdef
  -- `y ↦ D^k f(y)` is `C^∞` at every point of `U`
  have hΦat : ∀ y ∈ U, ContDiffAt ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin n) => iteratedFDeriv ℝ k f y) y := by
    intro y hy
    exact (hf.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right (m := ∞) (i := k)
      (by exact le_of_eq rfl)
  -- hence so is `σ`
  have hσat : ∀ y ∈ U, ContDiffAt ℝ ∞ σ y := by
    intro y hy
    rw [hσdef]
    exact (v.contDiff.contDiffAt).comp y ((A.contDiff.contDiffAt).comp y (hΦat y hy))
  -- `σ` vanishes on the stratum
  have hσvan : ∀ y, VanishToOrder f k y → σ y = 0 := by
    intro y hy
    have h0 : iteratedFDeriv ℝ k f y = 0 := hy k hk le_rfl
    rw [hσdef]
    simp [h0]
  -- and its derivative at `x` does not vanish
  have hσ'x : fderiv ℝ σ x ≠ 0 := by
    rw [hσdef]
    have hΦ : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => iteratedFDeriv ℝ k f y)
        (fderiv ℝ (iteratedFDeriv ℝ k f) x) x :=
      ((hf.contDiffAt (hU.mem_nhds hxU)).iteratedFDeriv_right (m := smoothHeight) (i := k)
        (by exact le_of_eq rfl)).hasStrictFDerivAt (n := smoothHeight) (by simp) |>.hasFDerivAt
    have h1 : HasFDerivAt (A ∘ fun y : EuclideanSpace ℝ (Fin n) => iteratedFDeriv ℝ k f y)
        (A ∘SL fderiv ℝ (iteratedFDeriv ℝ k f) x) x :=
      (ContinuousLinearMap.hasFDerivAt A).comp x hΦ
    have h2 : HasFDerivAt (fun y => v (A (iteratedFDeriv ℝ k f y)))
        (v ∘SL (A ∘SL fderiv ℝ (iteratedFDeriv ℝ k f) x)) x :=
      HasFDerivAt.comp x (ContinuousLinearMap.hasFDerivAt v) h1
    rw [h2.fderiv]
    have hval : (v ∘SL (A ∘SL fderiv ℝ (iteratedFDeriv ℝ k f) x)) (mm 0)
        = ((iteratedFDeriv ℝ (k+1) f x) mm).ofLp j := by
      simp only [ContinuousLinearMap.comp_apply, hA, hv, PiLp.proj_apply,
        ContinuousMultilinearMap.apply_apply, iteratedFDeriv_succ_apply_left]
    intro hzero
    have h1 := congrArg (fun (g : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) => g (mm 0)) hzero
    simp only [ContinuousLinearMap.zero_apply] at h1
    rw [hval] at h1
    exact hj h1
  -- the open set where the derivative of `σ` does not vanish
  have hcont : ContinuousOn (fun y => fderiv ℝ σ y) U := fun y hy =>
    ((hσat y hy).continuousAt_fderiv (by simp)).continuousWithinAt
  set W : Set (EuclideanSpace ℝ (Fin n)) :=
    U ∩ (fun y => fderiv ℝ σ y) ⁻¹' {L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ | L ≠ 0} with hWdef
  have hWopen : IsOpen W := hcont.isOpen_inter_preimage hU isOpen_ne
  have hxW : x ∈ W := ⟨hxU, hσ'x⟩
  refine ⟨σ, W, hWopen, hxW, Set.inter_subset_left, ?_, ?_, ?_⟩
  · rw [CInfOn, show (smoothHeight : ℕ∞ω) = ∞ from rfl]
    exact hWopen.contDiffOn_iff.mpr fun y hy => hσat y hy.1
  · intro y _ hyk
    exact hσvan y hyk
  · intro y hy
    exact hy.2

/-! ## The stratum differences are null -/

/-- **The image of a stratum difference is Lebesgue-null** (the vanishing-stratum step of Sard's
theorem).  For `k ≥ 1` and `f : ℝ^{n+1} → ℝ^m` of class `C^∞` on an open set `U`, the image of
`(Zk f k \ Zk f (k+1)) ∩ U` is null, assuming Sard's theorem for `C^∞` maps `ℝ^n → ℝ^m`.

Around each point of the stratum, `scalarVanishingHypersurface` produces a scalar `σ` vanishing on
the stratum with non-vanishing derivative, so the stratum lies in the smooth hypersurface
`{σ = 0}`; the points of the stratum are critical for `f` (`Zk f k ⊆ Zk f 1 = {fderiv f = 0}`), and
`levelSet_null` — Sard's theorem in the dimension `n` of the hypersurface — makes the image of the
part of the stratum in the neighbourhood of the point null.  A countable cover
(`volume_image_null_of_local`) globalizes over `U`. -/
theorem strataDifference_null {n m k : ℕ} (hk : 1 ≤ k)
    (hIH : Work.ThomBordism.Transversality.SardEuclidOn n m)
    {f : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin m)}
    {U : Set (EuclideanSpace ℝ (Fin (n+1)))} (hU : IsOpen U)
    (hf : Work.ThomBordism.Transversality.CInfOn f U) :
    MeasureTheory.volume (f '' ((Work.ThomBordism.Transversality.Zk f k
      \ Work.ThomBordism.Transversality.Zk f (k+1)) ∩ U)) = 0 := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- the target is a point: `f` is constant, all its strata are everything, the difference empty
    subst hm
    haveI : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance
    have hZ : Zk f (k+1) = univ := Zk_eq_univ_of_subsingleton f (k+1)
    rw [show Zk f k \ Zk f (k+1) = ∅ by rw [hZ, Set.sdiff_univ], Set.empty_inter,
      Set.image_empty, MeasureTheory.measure_empty]
  · -- the target is non-trivial: cover the stratum by the hypersurface neighbourhoods
    refine volume_image_null_of_local (f := f)
      (S := (Zk f k \ Zk f (k+1)) ∩ U) ?_
    rintro x ⟨⟨hxk, hxk'⟩, hxU⟩
    obtain ⟨σ, W, hWopen, hxW, hWU, hσsm, hσvan, hσ'⟩ :=
      scalarVanishingHypersurface hk hU hf hxU hxk hxk'
    exact ⟨W, hWopen, hxW,
      levelSet_null hIH hWopen (hf.mono hWU) hσsm
        Set.inter_subset_right
        (fun y hy => hσvan y hy.2 hy.1.1.1)
        (fun y hy => hσ' y hy.2)
        (fun y hy => isCriticalPoint_of_mem_Zk_one hm (Zk_antitone hk hy.1.1.1))⟩

end

end Work.ThomBordism.Transversality.Sard
