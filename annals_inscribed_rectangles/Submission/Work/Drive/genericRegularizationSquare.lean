import Mathlib
import Submission.Work.Drive.exists_forall_good_on_compact
import Submission.Work.Drive.exists_forall_good_on_compact_ball

/-!
# Generic regularization in the *square* case (as many unknowns as equations)

`Submission/Work/Drive/exists_forall_good_on_compact.lean` proves the parametric-Sard statement in the
shape `Φ : ℝ^m × ℝ^{n+1} → ℝ^n`: *one more unknown than equations*.  The genericity design of the
counting route also needs the **square** case — as many unknowns as equations, which is exactly the
shape in which the regularity of a *class-triple point* appears (three class coordinates equal to a
common class is `6` equations in the `6` parameters of the three plane presentations).  The square case
is not an instance of the `n+1` statement, and the naive Baire argument for it needs an extra
non-degeneracy input (`Submission/Work/Drive/L5_PLAN_GAP.md`).

**The point of this file is that the extra input is not needed**: the square case reduces to the proved
`n+1` case by *adding a dummy unknown* that the system ignores.  The bad condition ("the `z`-derivative
is not surjective") has codimension `n+1` in the space of derivatives for the `n+1`-unknown shape, and
the dummy variable supplies exactly that codimension, so the machinery applies verbatim.  The conclusion
transfers back because the dummy coordinate contributes nothing to the derivative.

Concretely, for `Ψ : ℝ^m × ℝ^n → ℝ^n` put `Φ (p, z) := Ψ (p, sqProj z)` where `sqProj : ℝ^{n+1} → ℝ^n`
drops the last coordinate.  Zeros of `Φ (p, ·)` are `sqProj`-preimages of zeros of `Ψ (p, ·)`, and
`fderiv (Φ (p, ·)) z = (fderiv (Ψ (p, ·)) (sqProj z)).comp sqProj` with `sqProj` surjective, so the
`z`-derivative is surjective on the nose for the two systems.
-/

namespace Work.Drive

open scoped ContDiff Topology
open Set Metric Filter

noncomputable section

/-- The unit box of the *square* coordinate space `Tgt n = ℝ^n` (`Submission.Drive.unitBox` lives in
`Amb n = ℝ^{n+1}`). -/
def tgtBox (n : ℕ) : Set (Tgt n) := {y | ∀ i, y i ∈ Set.Icc (0 : ℝ) 1}

lemma tgtBox_subset_preimage (n : ℕ) :
    tgtBox n = {y : Tgt n | ∀ i, y i ∈ Set.Icc (0 : ℝ) 1} := rfl

/-- The linear projection of `ℝ^{n+1}` onto its first `n` coordinates. -/
def sqProj (n : ℕ) : Amb n →L[ℝ] Tgt n :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm :
      ((i : Fin n) → ℝ) →L[ℝ] Tgt n).comp
    (ContinuousLinearMap.pi (fun i : Fin n =>
      PiLp.proj 2 (fun _ : Fin (n + 1) => ℝ) (Fin.castSucc i)))

lemma sqProj_apply (n : ℕ) (z : Amb n) (i : Fin n) :
    sqProj n z i = z (Fin.castSucc i) := by
  simp only [sqProj, ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
    PiLp.proj_apply, ContinuousLinearEquiv.coe_coe]
  rfl

/-- The section of `sqProj`: the vector with `y` in the first `n` coordinates and `0` in the last. -/
def sqSnoc (n : ℕ) (y : Tgt n) : Amb n :=
  WithLp.toLp 2 (fun i : Fin (n + 1) => if h : (i : ℕ) < n then y ⟨i, h⟩ else 0)

lemma sqProj_sqSnoc (n : ℕ) (y : Tgt n) : sqProj n (sqSnoc n y) = y := by
  ext i
  rw [sqProj_apply]
  show (WithLp.toLp 2 (fun i : Fin (n + 1) =>
      if h : (i : ℕ) < n then y ⟨i, h⟩ else 0)).ofLp (Fin.castSucc i) = y i
  rw [WithLp.ofLp_toLp, Fin.val_castSucc]
  rw [dif_pos i.isLt]

lemma sqSnoc_mem_unitBox {n : ℕ} {y : Tgt n} (hy : y ∈ tgtBox n) :
    sqSnoc n y ∈ Submission.Drive.unitBox n := by
  intro i
  show (WithLp.toLp 2 (fun i : Fin (n + 1) =>
      if h : (i : ℕ) < n then y ⟨i, h⟩ else 0)).ofLp i ∈ Set.Icc (0 : ℝ) 1
  rw [WithLp.ofLp_toLp]
  split_ifs with h
  · exact hy ⟨i, h⟩
  · exact ⟨le_refl 0, zero_le_one⟩

/-- **Parametric Sard in the square case, on a compact set of unknowns.**

For a smooth square system `Ψ : ℝ^m × ℝ^n → ℝ^n` whose *parameter* derivative is surjective at every
zero lying in the compact set `K`, there are parameters of arbitrarily small norm at which the
*unknown* derivative is surjective at every zero in `K`.

`hKbox` (`K` inside the unit box of `ℝ^n`) is only used to make the dummy construction land in the unit
box of `ℝ^{n+1}`; it costs nothing in the applications, where `K` is (part of) the design's box. -/
theorem exists_forall_good_square_on_compact (m n : ℕ) (K : Set (Tgt n)) (hK : IsCompact K)
    (hKbox : K ⊆ tgtBox n)
    (ε : ℝ) (hε : 0 < ε)
    (Ψ : EuclideanSpace ℝ (Fin m) × Tgt n → Tgt n)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hsurj : ∀ (p : EuclideanSpace ℝ (Fin m)) (z : Tgt n), z ∈ K → Ψ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Ψ (p', z)) p)) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε ∧
      ∀ z ∈ K, Ψ (p, z) = 0 →
        Function.Surjective (fderiv ℝ (fun z' : Tgt n => Ψ (p, z')) z) := by
  -- the compact set of the dummy variable
  set K' : Set (Amb n) := {z | sqProj n z ∈ K ∧ z ∈ Submission.Drive.unitBox n} with hK'
  have hK'compact : IsCompact K' := by
    rw [hK']
    have hclosed1 : IsClosed {z : Amb n | sqProj n z ∈ K} :=
      hK.isClosed.preimage (sqProj n).continuous
    exact IsCompact.of_isClosed_subset (isCompact_unitBox n)
      (hclosed1.inter (isClosed_unitBox n)) (fun z hz => hz.2)
  -- the dummy extension of the system
  have hsurj' : ∀ (p : EuclideanSpace ℝ (Fin m)) (z : Amb n),
      z ∈ K' → Ψ (p, sqProj n z) = 0 →
      Function.Surjective
        (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Ψ (p', sqProj n z)) p) := by
    intro p z hz h0
    exact hsurj p (sqProj n z) hz.1 h0
  obtain ⟨p, hpball, hp⟩ :=
    exists_forall_good_on_compact m n K' hK'compact ε hε
      (fun x : EuclideanSpace ℝ (Fin m) × Amb n => Ψ (x.1, sqProj n x.2))
      (hΨ.comp (contDiff_fst.prodMk ((sqProj n).contDiff.comp contDiff_snd))) hsurj'
  refine ⟨p, hpball, ?_⟩
  intro y hy hy0
  have hy' : sqSnoc n y ∈ K' :=
    ⟨by rw [sqProj_sqSnoc]; exact hy, sqSnoc_mem_unitBox (hKbox hy)⟩
  have hy0' : Ψ (p, sqProj n (sqSnoc n y)) = 0 := by rw [sqProj_sqSnoc]; exact hy0
  have hsurjz := hp (sqSnoc n y) hy' hy0'
  -- the derivative of the dummy system
  have hΦderiv : fderiv ℝ (fun z' : Amb n => Ψ (p, sqProj n z')) (sqSnoc n y)
      = (fderiv ℝ (fun z' : Tgt n => Ψ (p, z')) (sqProj n (sqSnoc n y))).comp (sqProj n) := by
    have hd : DifferentiableAt ℝ Ψ (p, sqProj n (sqSnoc n y)) :=
      (hΨ.differentiable (by simp)).differentiableAt
    have hin : HasFDerivAt (fun z' : Amb n => (p, sqProj n z'))
        ((ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (Tgt n)).comp (sqProj n))
        (sqSnoc n y) := by
      have h := (((ContinuousLinearMap.hasFDerivAt
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (Tgt n)))).const_add
            (p, 0)).comp (sqSnoc n y) ((sqProj n).hasFDerivAt)
      simpa [Function.comp_def] using h
    have hcomp := hd.hasFDerivAt.comp (sqSnoc n y) hin
    have hgoal : fderiv ℝ (fun z' : Amb n => Ψ (p, sqProj n z')) (sqSnoc n y)
        = ((fderiv ℝ Ψ (p, sqProj n (sqSnoc n y))).comp
            (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (Tgt n))).comp (sqProj n) := by
      rw [show (fun z' : Amb n => Ψ (p, sqProj n z'))
          = (Ψ ∘ fun z' : Amb n => (p, sqProj n z')) from rfl, hcomp.fderiv]
      rfl
    rw [hgoal, Work.MetricSquare.fd_comp_inr Ψ hΨ p (sqProj n (sqSnoc n y))]
  rw [hΦderiv] at hsurjz
  -- transfer the surjectivity back along the (surjective) projection
  have hsplit : Function.Surjective
      ((fderiv ℝ (fun z' : Tgt n => Ψ (p, z')) (sqProj n (sqSnoc n y))).comp (sqProj n)) := hsurjz
  have htarget : fderiv ℝ (fun z' : Tgt n => Ψ (p, z')) (sqProj n (sqSnoc n y))
      = fderiv ℝ (fun z' : Tgt n => Ψ (p, z')) y := by rw [sqProj_sqSnoc]
  rw [htarget] at hsplit
  intro w
  obtain ⟨v, hv⟩ := hsplit w
  refine ⟨sqProj n v, ?_⟩
  have hv' : (fderiv ℝ (fun z' : Tgt n => Ψ (p, z')) y) (sqProj n v) = w := hv
  exact hv'

/-- **Parametric Sard in the square case, with the parameter restricted to a ball.**

The same statement as `exists_forall_good_square_on_compact`, but the hypothesis on the parameter
derivative is only required on the closed ball of radius `ε₀` — which is exactly what a *perturbation
family* whose values are invertible only near the origin can supply. -/
theorem exists_forall_good_square_on_compact_ball (m n : ℕ) (K : Set (Tgt n)) (hK : IsCompact K)
    (hKbox : K ⊆ tgtBox n) (ε₀ ε : ℝ) (hε₀ : 0 < ε₀) (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (Ψ : EuclideanSpace ℝ (Fin m) × Tgt n → Tgt n)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hsurj : ∀ (p : EuclideanSpace ℝ (Fin m)) (z : Tgt n), ‖p‖ ≤ ε₀ → z ∈ K → Ψ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Ψ (p', z)) p)) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε ∧
      ∀ z ∈ K, Ψ (p, z) = 0 →
        Function.Surjective (fderiv ℝ (fun z' : Tgt n => Ψ (p, z')) z) := by
  set K' : Set (Amb n) := {z | sqProj n z ∈ K ∧ z ∈ Submission.Drive.unitBox n} with hK'
  have hK'compact : IsCompact K' := by
    rw [hK']
    have hclosed1 : IsClosed {z : Amb n | sqProj n z ∈ K} :=
      hK.isClosed.preimage (sqProj n).continuous
    exact IsCompact.of_isClosed_subset (isCompact_unitBox n)
      (hclosed1.inter (isClosed_unitBox n)) (fun z hz => hz.2)
  have hsurj' : ∀ (p : EuclideanSpace ℝ (Fin m)) (z : Amb n), ‖p‖ ≤ ε₀ → z ∈ K' →
      Ψ (p, sqProj n z) = 0 →
      Function.Surjective
        (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Ψ (p', sqProj n z)) p) := by
    intro p z hp hz h0
    exact hsurj p (sqProj n z) hp hz.1 h0
  obtain ⟨p, hpball, hp⟩ :=
    exists_forall_good_on_compact_ball m n K' hK'compact ε₀ ε hε₀ hε hεε₀
      (fun x : EuclideanSpace ℝ (Fin m) × Amb n => Ψ (x.1, sqProj n x.2))
      (hΨ.comp (contDiff_fst.prodMk ((sqProj n).contDiff.comp contDiff_snd))) hsurj'
  refine ⟨p, hpball, ?_⟩
  intro y hy hy0
  have hy' : sqSnoc n y ∈ K' :=
    ⟨by rw [sqProj_sqSnoc]; exact hy, sqSnoc_mem_unitBox (hKbox hy)⟩
  have hy0' : Ψ (p, sqProj n (sqSnoc n y)) = 0 := by rw [sqProj_sqSnoc]; exact hy0
  have hsurjz := hp (sqSnoc n y) hy' hy0'
  have hΦderiv : fderiv ℝ (fun z' : Amb n => Ψ (p, sqProj n z')) (sqSnoc n y)
      = (fderiv ℝ (fun z' : Tgt n => Ψ (p, z')) (sqProj n (sqSnoc n y))).comp (sqProj n) := by
    have hd : DifferentiableAt ℝ Ψ (p, sqProj n (sqSnoc n y)) :=
      (hΨ.differentiable (by simp)).differentiableAt
    have hin : HasFDerivAt (fun z' : Amb n => (p, sqProj n z'))
        ((ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (Tgt n)).comp (sqProj n))
        (sqSnoc n y) := by
      have h := (((ContinuousLinearMap.hasFDerivAt
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (Tgt n)))).const_add
            (p, 0)).comp (sqSnoc n y) ((sqProj n).hasFDerivAt)
      simpa [Function.comp_def] using h
    have hcomp := hd.hasFDerivAt.comp (sqSnoc n y) hin
    have hgoal : fderiv ℝ (fun z' : Amb n => Ψ (p, sqProj n z')) (sqSnoc n y)
        = ((fderiv ℝ Ψ (p, sqProj n (sqSnoc n y))).comp
            (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (Tgt n))).comp (sqProj n) := by
      rw [show (fun z' : Amb n => Ψ (p, sqProj n z'))
          = (Ψ ∘ fun z' : Amb n => (p, sqProj n z')) from rfl, hcomp.fderiv]
      rfl
    rw [hgoal, Work.MetricSquare.fd_comp_inr Ψ hΨ p (sqProj n (sqSnoc n y))]
  rw [hΦderiv] at hsurjz
  have htarget : fderiv ℝ (fun z' : Tgt n => Ψ (p, z')) (sqProj n (sqSnoc n y))
      = fderiv ℝ (fun z' : Tgt n => Ψ (p, z')) y := by rw [sqProj_sqSnoc]
  rw [htarget] at hsurjz
  intro w
  obtain ⟨v, hv⟩ := hsurjz w
  exact ⟨sqProj n v, hv⟩

end

end Work.Drive
