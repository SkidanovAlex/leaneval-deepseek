import Mathlib
import Submission.Work.Whitney.CutPush.transport_of_plane_family
import Submission.Work.Drive.Push.planeFamilyQ
import Submission.Work.Drive.Push.transportInvariantSubmodule

namespace Work.Drive.Push

/-- **Aligning a smooth plane family along the interval `[0,1]` by a family of linear
automorphisms fixing a vector `e` and preserving `eᗮ`.** -/
theorem planeFamilyAlignment {N k : ℕ}
    (P : ℝ → EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (hPsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) => P p.1 p.2))
    (hidem : ∀ t, P t * P t = P t)
    (hsa : ∀ t (x y : EuclideanSpace ℝ (Fin N)), inner ℝ (P t x) y = inner ℝ x (P t y))
    (hrank : ∀ t, Module.finrank ℝ (LinearMap.range (P t).toLinearMap) = k)
    (e : EuclideanSpace ℝ (Fin N)) (he : e ≠ 0)
    (hPe : ∀ t, P t e ≠ 0)
    (he01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, P t e = e) :
    ∃ M : ℝ → EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => M p.1 p.2) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => (M p.1).symm p.2) ∧
      (∀ t, M t e = e) ∧
      (∀ t (u : EuclideanSpace ℝ (Fin N)), inner ℝ u e = 0 → inner ℝ (M t u) e = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : EuclideanSpace ℝ (Fin N),
        P 0 (M t (P t y)) = M t (P t y)) := by
  classical
  -- The auxiliary family `Q t = P t - proj_{P t e}`, of constant rank `k - 1`, jointly smooth,
  -- whose range is `range (P t) ∩ (P t e)ᗮ`.
  obtain ⟨Q, hQsm, hQidem, hQrank, hQe, hQperp, hQformula, hQfix⟩ :=
    planeFamilyQ P hPsm hidem hsa hrank e he hPe
  -- The invariant subspace `K = eᗮ`.
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin N)) := (ℝ ∙ e)ᗮ with hKdef
  have hKmem : ∀ u : EuclideanSpace ℝ (Fin N), u ∈ K ↔ inner ℝ u e = 0 := by
    intro u
    rw [hKdef, Submodule.mem_orthogonal_singleton_iff_inner_left]
  have hQK : ∀ t : ℝ, ∀ y : EuclideanSpace ℝ (Fin N), y ∈ K → Q t y ∈ K := by
    intro t y hy
    rw [hKmem] at hy ⊢
    exact hQperp t y hy
  -- The transport of the plane field, preserving `eᗮ`.
  obtain ⟨Λ, Λinv, hΛsm, hΛinvsm, hΛleft, hΛright, hΛrange, hΛK, hΛinvK⟩ :=
    transportInvariantSubmodule Q hQsm hQidem hQrank K hQK
  -- The orthogonal projection onto `span e`.
  set P_e : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    (ℝ ∙ e).starProjection with hP_edef
  have hP_e_formula : ∀ x : EuclideanSpace ℝ (Fin N),
      P_e x = (inner ℝ e x / ‖e‖ ^ 2) • e := by
    intro x; rw [hP_edef]; exact Submodule.starProjection_singleton ℝ x
  have hP_e_self : ∀ x, P_e (P_e x) = P_e x := by
    intro x
    rw [hP_edef]
    exact Submodule.starProjection_mem_subspace_eq_self ⟨(ℝ ∙ e).starProjection x,
      Submodule.starProjection_apply_mem _ x⟩
  have hP_e_zero : ∀ z : EuclideanSpace ℝ (Fin N), z ∈ K → P_e z = 0 := by
    intro z hz
    rw [hKdef] at hz
    rw [hP_edef, Submodule.starProjection_apply_eq_zero_iff]
    exact hz
  have hP_e_e : P_e e = e := by
    rw [hP_edef, Submodule.starProjection_eq_self_iff]
    exact Submodule.mem_span_singleton_self e
  have hperp_mem : ∀ x : EuclideanSpace ℝ (Fin N), x - P_e x ∈ K := by
    intro x
    rw [hKdef, hP_edef]
    exact Submodule.sub_starProjection_mem_orthogonal x
  -- A `K`-preserving endomorphism `A` acts on the `eᗮ` summand, so the composites multiply.
  have hblk : ∀ (A B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)),
      (∀ y ∈ K, A y ∈ K) → (∀ y ∈ K, B y ∈ K) →
      (P_e + A * (1 - P_e)) * (P_e + B * (1 - P_e)) = P_e + A * B * (1 - P_e) := by
    intro A B hA hB
    ext x
    have hBz : B (x - P_e x) ∈ K := hB _ (hperp_mem x)
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [map_add, hP_e_self x, hP_e_zero _ hBz, add_zero,
      show (P_e x + B (x - P_e x)) - P_e x = B (x - P_e x) from by abel]
  let Mfun : ℝ → EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    fun t => P_e + Λ t * (1 - P_e)
  let Minv : ℝ → EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    fun t => P_e + Λinv t * (1 - P_e)
  have hcomp₁ : ∀ t, Mfun t * Minv t = 1 := by
    intro t
    have h := hblk (Λ t) (Λinv t) (fun y hy => hΛK t y hy) (fun y hy => hΛinvK t y hy)
    have h2 : Λ t * Λinv t = 1 := ContinuousLinearMap.ext (fun y => by simpa using hΛright t y)
    rw [show Mfun t * Minv t
        = (P_e + Λ t * (1 - P_e)) * (P_e + Λinv t * (1 - P_e)) from rfl, h, h2, one_mul]
    abel
  have hcomp₂ : ∀ t, Minv t * Mfun t = 1 := by
    intro t
    have h := hblk (Λinv t) (Λ t) (fun y hy => hΛinvK t y hy) (fun y hy => hΛK t y hy)
    have h2 : Λinv t * Λ t = 1 := ContinuousLinearMap.ext (fun y => by simpa using hΛleft t y)
    rw [show Minv t * Mfun t
        = (P_e + Λinv t * (1 - P_e)) * (P_e + Λ t * (1 - P_e)) from rfl, h, h2, one_mul]
    abel
  have hstep : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) => (p.1, (1 - P_e) p.2)) :=
    contDiff_fst.prodMk ((contDiff_const.sub contDiff_const).clm_apply contDiff_snd)
  have hMfun_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) => Mfun p.1 p.2) := by
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => Λ p.1 ((1 - P_e) p.2)) := hΛsm.comp hstep
    have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => P_e p.2) :=
      contDiff_const.clm_apply contDiff_snd
    exact h4.add h3
  have hMinv_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) => Minv p.1 p.2) := by
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => Λinv p.1 ((1 - P_e) p.2)) :=
      hΛinvsm.comp hstep
    have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => P_e p.2) :=
      contDiff_const.clm_apply contDiff_snd
    exact h4.add h3
  refine ⟨fun t => ContinuousLinearEquiv.equivOfInverse' (Mfun t) (Minv t) (hcomp₁ t) (hcomp₂ t),
    hMfun_sm, ?_, ?_, ?_, ?_⟩
  · show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) => Minv p.1 p.2)
    exact hMinv_sm
  · intro t
    show Mfun t e = e
    simp only [Mfun, ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hP_e_e, sub_self,
      ContinuousLinearMap.map_zero, add_zero]
  · intro t u hu
    have hz : u ∈ K := by rw [hKmem]; exact hu
    have hPeu : P_e u = 0 := hP_e_zero u hz
    have hΛu : Λ t u ∈ K := hΛK t u hz
    rw [hKmem] at hΛu
    show inner ℝ (Mfun t u) e = 0
    simp only [Mfun, ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hPeu, sub_zero, zero_add]
    exact hΛu
  · intro t ht y
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hte : P t e = e := he01 t ht
    have h0e : P 0 e = e := he01 0 h0
    have hidem0 : ∀ z, P 0 (P 0 z) = P 0 z := by
      intro z
      have h := congrArg
        (fun (f : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) => f z) (hidem 0)
      simpa [ContinuousLinearMap.mul_apply] using h
    have hidemt : ∀ z, P t (P t z) = P t z := by
      intro z
      have h := congrArg
        (fun (f : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) => f z) (hidem t)
      simpa [ContinuousLinearMap.mul_apply] using h
    -- Decompose `P t y` as `α • e + v` with `v ∈ eᗮ`.
    set x : EuclideanSpace ℝ (Fin N) := P t y with hx
    set α : ℝ := inner ℝ e x / ‖e‖ ^ 2 with hα
    set v : EuclideanSpace ℝ (Fin N) := x - α • e with hv
    have hvmem : inner ℝ v e = 0 := by
      rw [hv, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hα]
      rw [real_inner_comm x e]
      have he2 : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr he)
      field_simp
      ring
    have hxv : P t v = v := by
      have h1 : P t x = x := by rw [hx]; exact hidemt y
      have h2 : P t (α • e) = α • e := by rw [map_smul, hte]
      rw [hv, map_sub, h1, h2]
    have hQv : Q t v = v := hQfix t v hxv (by rw [hte]; exact hvmem)
    have hΛv : Λ t v ∈ LinearMap.range (Q 0).toLinearMap := by
      rw [← hΛrange t ht]
      exact ⟨v, by show (Λ t) ((Q t) v) = (Λ t) v; rw [hQv]⟩
    obtain ⟨w, hw⟩ := hΛv
    have hmem0 : Λ t v ∈ LinearMap.range (P 0).toLinearMap := by
      rw [← hw]
      change Q 0 w ∈ LinearMap.range (P 0).toLinearMap
      rw [hQformula 0 w, h0e]
      exact Submodule.sub_mem _ ⟨w, rfl⟩ (Submodule.smul_mem _ _ ⟨e, h0e⟩)
    have hMx : Mfun t x = α • e + Λ t v := by
      have h1 : P_e x = α • e := by rw [hP_e_formula, hα]
      show P_e x + Λ t ((1 - P_e) x) = α • e + Λ t v
      rw [h1, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, h1, ← hv]
    have htarget : Mfun t x ∈ LinearMap.range (P 0).toLinearMap := by
      rw [hMx]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ ⟨e, h0e⟩) hmem0
    obtain ⟨w', hw'⟩ := htarget
    show P 0 (Mfun t x) = Mfun t x
    rw [← hw']
    exact hidem0 w'

end Work.Drive.Push
