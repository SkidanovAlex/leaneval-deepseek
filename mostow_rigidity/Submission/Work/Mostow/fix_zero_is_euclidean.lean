import Mathlib
import Submission.Work.Mostow.ematSpec
import Submission.Work.Mostow.ellipticDefs

/-!
# An isometry of `ℍⁿ` fixing the base point acts linearly

Let `g ∈ PO(n,1)` fix the base point `0` of the chart (the hyperboloid point `(0,1)`).
Then `g` is the *linear* isometry of the chart `E n ≅ ℝⁿ` given by the spatial block of
its effective matrix `emat g = tsign (rep g) • mat (rep g)`:

`Work.Mostow.fix_zero_is_euclidean` : there is `A : E n ≃ₗᵢ[ℝ] E n` with `g • u = A u`
for all `u`.

The proof: `ematSpec` gives `emat g *ᵥ hlift u = hlift (g • u)` and that `emat g`
preserves the Minkowski form `mink`.  Since `hlift 0 = etime` and `g` fixes `0`, the time
vector `etime` is fixed by `M = emat g`; consequently `M` preserves the spacelike subspace
(`x (inr 0) = 0`), because the time coordinate is read off by `- mink x etime`.  Hence the
spatial part `spat (M *ᵥ wvec u)` is a linear map of `E n` preserving the inner product
(the Minkowski form restricts to `inner` on the spacelike subspace), so it is a linear
isometry, bijective by finite dimension.  Finally `hlift u = wvec u + tpart u • etime` and
`M etime = etime` give `g • u = spat (M *ᵥ hlift u) = spat (M *ᵥ wvec u)`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-- `wvec` is additive. -/
lemma wvec_add (u v : E n) : wvec (u + v) = wvec u + wvec v := by
  funext z
  rcases z with i | j
  · simp [wvec]
  · fin_cases j; simp [wvec]

/-- `wvec` is homogeneous. -/
lemma wvec_smul (r : ℝ) (u : E n) : wvec (r • u) = r • wvec u := by
  funext z
  rcases z with i | j
  · simp [wvec]
  · fin_cases j; simp [wvec]

/-- The time coordinate of `wvec u` vanishes. -/
lemma wvec_time (u : E n) : (wvec u) (Sum.inr 0) = 0 := by
  simp [wvec]

/-- `spat` is additive. -/
lemma spat_add (a b : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.spat (a + b) = Hyper.spat a + Hyper.spat b := rfl

/-- `spat` is homogeneous. -/
lemma spat_smul (r : ℝ) (a : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.spat (r • a) = r • Hyper.spat a := rfl

/-- The spatial part of the time vector is zero. -/
lemma spat_etime : Hyper.spat (Hyper.etime n) = (0 : E n) := by
  ext i
  simp [Hyper.spat, Hyper.etime]

/-- The Minkowski pairing with the time vector is (minus) the time coordinate. -/
lemma mink_etime_right (x : Fin n ⊕ Fin 1 → ℝ) : mink x (Hyper.etime n) = - x (Sum.inr 0) := by
  simp [mink, Hyper.etime]

/-- The hyperboloid lift splits as the spacelike part plus the time part. -/
lemma hlift_eq_wvec_add_smul_etime (u : E n) :
    hlift u = wvec u + tpart u • Hyper.etime n := by
  funext z
  rcases z with i | j
  · simp [wvec, hlift, Hyper.etime, Sum.inl_ne_inr]
  · fin_cases j; simp [wvec, hlift, Hyper.etime]

/-- The Minkowski form through the spatial part and the time coordinate. -/
lemma mink_eq_inner_spat_time (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink x y = inner ℝ (Hyper.spat x) (Hyper.spat y) - x (Sum.inr 0) * y (Sum.inr 0) := by
  rw [mink, Hyper.inner_eq_sum]
  simp only [Hyper.spat, PiLp.toLp_apply]

/-- **An isometry of `ℍⁿ` fixing the base point is linear in the chart.**
If `g • 0 = 0` there is a linear isometry `A` of `E n` with `g • u = A u` for all `u`. -/
theorem fix_zero_is_euclidean (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (g : LeanEval.Geometry.MostowRigidity.PO n 1)
    (hg : g • (0 : Submission.Mostow.E n) = 0) :
    ∃ A : Submission.Mostow.E n ≃ₗᵢ[ℝ] Submission.Mostow.E n, ∀ u : Submission.Mostow.E n, g • u = A u := by
  have _ := hA
  have _ := hI
  obtain ⟨hsheet, hisom, _⟩ := ematSpec g
  set M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ := emat g with hM
  -- `M` fixes the time vector
  have hetime : M *ᵥ Hyper.etime n = Hyper.etime n := by
    have h := hsheet 0
    rw [hg, Hyper.hlift_zero] at h
    simpa [hM] using h
  -- hence `M` preserves the spacelike subspace
  have htime : ∀ x : Fin n ⊕ Fin 1 → ℝ, x (Sum.inr 0) = 0 → (M *ᵥ x) (Sum.inr 0) = 0 := by
    intro x hx
    have h1 : mink (M *ᵥ x) (Hyper.etime n) = mink x (Hyper.etime n) := by
      have h2 := hisom x (Hyper.etime n)
      rwa [hetime, hM] at h2
    rw [mink_etime_right, mink_etime_right, hx, neg_zero] at h1
    exact neg_eq_zero.mp h1
  -- on the spacelike subspace the Minkowski form is the Euclidean inner product
  have hinner : ∀ u v : E n,
      inner ℝ (Hyper.spat (M *ᵥ wvec u)) (Hyper.spat (M *ᵥ wvec v)) = inner ℝ u v := by
    intro u v
    have h1 : mink (M *ᵥ wvec u) (M *ᵥ wvec v) = mink (wvec u) (wvec v) := by
      have h2 := hisom (wvec u) (wvec v)
      rwa [hM] at h2
    rw [mink_eq_inner_spat_time, htime (wvec u) (wvec_time u), htime (wvec v) (wvec_time v),
      mul_zero, sub_zero] at h1
    rw [mink_eq_inner_spat_time, wvec_time u, wvec_time v, mul_zero, sub_zero] at h1
    rw [h1]
    simp only [Hyper.spat, wvec, Sum.elim_inl]
  -- the spatial part of `M` as a linear map
  let Alin : E n →ₗ[ℝ] E n :=
    { toFun := fun u => Hyper.spat (M *ᵥ wvec u)
      map_add' := fun u v => by rw [wvec_add, Matrix.mulVec_add, spat_add]
      map_smul' := fun r u => by
        rw [wvec_smul, Matrix.mulVec_smul, spat_smul, RingHom.id_apply] }
  have hAlin : ∀ u : E n, Alin u = Hyper.spat (M *ᵥ wvec u) := fun u => rfl
  have hinner' : ∀ u v : E n, inner ℝ (Alin u) (Alin v) = inner ℝ u v := by
    intro u v
    show inner ℝ (Hyper.spat (M *ᵥ wvec u)) (Hyper.spat (M *ᵥ wvec v)) = inner ℝ u v
    exact hinner u v
  have hlip : ∀ u : E n, ‖Alin u‖ = ‖u‖ := by
    intro u
    have h := hinner' u u
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (Alin u), norm_nonneg u]
  have hinj : Function.Injective Alin := by
    intro u v huv
    have hz : Alin (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have h2 : ‖u - v‖ = 0 := by rw [← hlip (u - v), hz, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp h2)
  have hsurj : Function.Surjective Alin :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (rfl : Module.finrank ℝ (E n) = Module.finrank ℝ (E n))).mp hinj
  refine ⟨LinearIsometryEquiv.ofSurjective (LinearMap.isometryOfInner Alin hinner') hsurj,
    fun u => ?_⟩
  have hcu : g • u = Alin u := by
    have h1 : Hyper.spat (M *ᵥ hlift u) = g • u := by
      rw [hsheet u, Hyper.spat_hlift]
    rw [← h1, hlift_eq_wvec_add_smul_etime, Matrix.mulVec_add, Matrix.mulVec_smul, hetime,
      spat_add, spat_smul, spat_etime, smul_zero, add_zero]
    exact (hAlin u).symm
  exact hcu

end

end Work.Mostow
