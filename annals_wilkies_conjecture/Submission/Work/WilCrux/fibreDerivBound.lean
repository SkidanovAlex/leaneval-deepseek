import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.C1Direct.FibrePartialBoundClosed

set_option autoImplicit false

namespace Work.WilCrux

/-- `famFun G` evaluated at `Fin.append w z` is `G w z`: the parameters are `w`, the fibre
coordinates are `z`. -/
lemma famFun_append {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (w : Fin a → ℝ)
    (z' : Fin b → ℝ) : Work.WilG4c.famFun G (Fin.append w z') = G w z' := by
  simp [Work.WilG4c.famFun]

/-- The slice `z' ↦ G w z'` is differentiable wherever `famFun G` is, because it is the
composition of `famFun G` with the (differentiable) map `z' ↦ Fin.append w z'`. -/
lemma slice_differentiableAt {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (w : Fin a → ℝ)
    (z : Fin b → ℝ) (hd : DifferentiableAt ℝ (Work.WilG4c.famFun G) (Fin.append w z)) :
    DifferentiableAt ℝ (G w) z := by
  have hφdiff : DifferentiableAt ℝ (fun z' : Fin b → ℝ => Fin.append w z') z := by
    rw [differentiableAt_pi]
    intro i
    refine Fin.addCases (fun k => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      exact differentiableAt_const (w k)
    · simp only [Fin.append_right]
      exact differentiableAt_apply j z
  have heq : G w = (Work.WilG4c.famFun G) ∘ (fun z' : Fin b → ℝ => Fin.append w z') := by
    funext z'
    rw [Function.comp_apply, famFun_append]
  rw [heq]
  exact hd.comp z hφdiff

/-- **Chain rule identity for the fibre direction.**  If `famFun G` is differentiable at
`Fin.append w z`, then its derivative there in the pure fibre direction `Fin.append 0 v` is the
derivative of the slice `G w` at `z`, applied to `v`.  (There is no need for a
`C¹`-hypothesis beyond differentiability: the curve `t ↦ Fin.append w (z + t • v)` has derivative
`Fin.append 0 v` at `0`, so the chain rule identifies both sides with the derivative of
`t ↦ famFun G (Fin.append w (z + t • v)) = G w (z + t • v)` at `0`.) -/
lemma fderiv_famFun_fibre {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (w : Fin a → ℝ)
    (z v : Fin b → ℝ) (hd : DifferentiableAt ℝ (Work.WilG4c.famFun G) (Fin.append w z)) :
    fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (Fin.append 0 v)
      = fderiv ℝ (G w) z v := by
  have hcurve1 : HasDerivAt (fun t : ℝ => Fin.append w (z + t • v)) (Fin.append 0 v) 0 := by
    rw [hasDerivAt_pi]
    intro i
    refine Fin.addCases (fun k => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      simpa using hasDerivAt_const (0 : ℝ) (w k)
    · simp only [Fin.append_right, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (z j))
  have hcomp1 : HasDerivAt (fun t : ℝ => G w (z + t • v))
      (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (Fin.append 0 v)) 0 := by
    have hfd' : HasFDerivAt (Work.WilG4c.famFun G)
        (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z))
        ((fun t : ℝ => Fin.append w (z + t • v)) 0) := by
      show HasFDerivAt (Work.WilG4c.famFun G)
        (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)) (Fin.append w (z + (0 : ℝ) • v))
      rw [zero_smul, add_zero]
      exact hd.hasFDerivAt
    have h := hfd'.comp_hasDerivAt (0 : ℝ) hcurve1
    have hh : HasDerivAt (fun t : ℝ => Work.WilG4c.famFun G (Fin.append w (z + t • v)))
        (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (Fin.append 0 v)) 0 := by
      simpa [Function.comp_def] using h
    have heq : (fun t : ℝ => Work.WilG4c.famFun G (Fin.append w (z + t • v)))
        = fun t : ℝ => G w (z + t • v) := by
      funext t; exact famFun_append G w (z + t • v)
    rwa [heq] at hh
  have hcurve2 : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z)
  have hdiff_G : DifferentiableAt ℝ (G w) z := slice_differentiableAt G w z hd
  have hcomp2 : HasDerivAt (fun t : ℝ => G w (z + t • v)) (fderiv ℝ (G w) z v) 0 := by
    have hfd' : HasFDerivAt (G w) (fderiv ℝ (G w) z) ((fun t : ℝ => z + t • v) 0) := by
      show HasFDerivAt (G w) (fderiv ℝ (G w) z) (z + (0 : ℝ) • v)
      rw [zero_smul, add_zero]
      exact hdiff_G.hasFDerivAt
    have h := hfd'.comp_hasDerivAt (0 : ℝ) hcurve2
    simpa [Function.comp_def] using h
  exact hcomp1.unique hcomp2

/-- A continuous linear map on `ℝ^n` (with the sup norm, as everywhere in this development) is
recovered from its values on the coordinate basis vectors: `L v = ∑ k, v k • L (single k 1)`. -/
lemma clm_apply_eq_sum_single {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : (Fin n → ℝ) →L[ℝ] F) (v : Fin n → ℝ) :
    L v = ∑ k, v k • L (Pi.single k (1 : ℝ)) := by
  have hv : v = ∑ k, v k • (Pi.single k (1 : ℝ) : Fin n → ℝ) := by
    funext i
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      rw [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne (Ne.symm hk), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul]

/-- The fibre-direction derivative of `famFun G` at a smooth point is bounded by the fibre
Lipschitz constant times the ℓ¹-norm of the direction: writing `famFun G` for the uncurried
`G` on `ℝ^{a+b}`, its derivative in the direction `(0, v)` is the derivative of the slice
`G w` at `z`, and the slice partials are `≤ M` in absolute value by `hLip` (via the proven
`Work.WilG4c.C1Direct.FibrePartialBoundClosed`), on the closed `τ`-ball.

NOTE: the result must be axiom-clean.  Do NOT use `Work.WilG4c.C1Direct.fderiv_famFun_fibre`
(and anything else in the workspace that currently has a `sorry`): that declaration is
sorry-ed *and* is false as stated without a differentiability hypothesis.  Prove the chain-rule
identity yourself from `hC1` (the map `z' ↦ Fin.append w z'` is smooth, so `hC1` gives
`DifferentiableAt ℝ (G w) z` and identifies `fderiv (famFun G) (append w z) (append 0 v)` with
`fderiv (G w) z v`), then expand `v` in the coordinate basis. -/
theorem fibreDerivBound {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (w : Fin a → ℝ)
    (z v : Fin b → ℝ) {τ M : ℝ} (hM : 0 ≤ M) (hτ : 0 < τ) (hz : ‖z‖ ≤ τ)
    (hC1 : ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z))
    (hLip : ∀ z z' : Fin b → ℝ, ‖z‖ ≤ τ → ‖z'‖ ≤ τ → |G w z - G w z'| ≤ M * ‖z - z'‖) :
    |fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (Fin.append 0 v)| ≤ M * ∑ k, |v k| := by
  have hd : DifferentiableAt ℝ (Work.WilG4c.famFun G) (Fin.append w z) :=
    hC1.differentiableAt (by norm_num)
  have hdiff_G : DifferentiableAt ℝ (G w) z := slice_differentiableAt G w z hd
  -- The chain-rule identity: the fibre derivative is the slice derivative.
  rw [fderiv_famFun_fibre G w z v hd]
  -- Each fibre partial of the slice is bounded by `M` on the closed `τ`-ball.
  have hbound : ∀ k : Fin b, |fderiv ℝ (G w) z (Pi.single k (1 : ℝ))| ≤ M := by
    intro k
    have h := (Work.WilG4c.C1Direct.FibrePartialBoundClosed
        (fun (_ : Fin a → ℝ) (x : Fin b → ℝ) => G w x) hM hτ
        (fun _ z z' hz hz' => hLip z z' hz hz')) w z k hz hdiff_G
    simpa using h
  -- Expand `v` in the coordinate basis and take absolute values.
  have hsum : fderiv ℝ (G w) z v
      = ∑ k, v k * fderiv ℝ (G w) z (Pi.single k (1 : ℝ)) := by
    simpa [smul_eq_mul] using clm_apply_eq_sum_single (fderiv ℝ (G w) z) v
  rw [hsum]
  calc |∑ k, v k * fderiv ℝ (G w) z (Pi.single k (1 : ℝ))|
      ≤ ∑ k, |v k * fderiv ℝ (G w) z (Pi.single k (1 : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |v k| * |fderiv ℝ (G w) z (Pi.single k (1 : ℝ))| := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [abs_mul]
    _ ≤ ∑ k, |v k| * M :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hbound k) (abs_nonneg _))
    _ = (∑ k, |v k|) * M := by rw [Finset.sum_mul]
    _ = M * ∑ k, |v k| := by ring

end Work.WilCrux
