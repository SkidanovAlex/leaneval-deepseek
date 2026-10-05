import Mathlib
import Submission.Work.RPA3.follow_family_defs
import Submission.Work.RPA3.theta_std
import Submission.Work.RPA3.theta_per
import Submission.Work.RPA3.theta_coord_bounds
import Submission.Work.RPA3.lagrangian_orthogonal
import Submission.Work.RPA3.sliceDeriv_periodic
import Submission.Work.RPA3.exists_bound_of_periodic_of_std
import Submission.Work.RPA3.exists_lower_of_periodic_of_std
import Submission.Work.RPA3.Ycoef_norm_bound

/-!
# RPA3: boundedness of the tangential correction field `Y` on a `τ`-strip

The correction field
`Yfield L H τ q = Ycoef L H τ q.1 q.2`
is the solution of the Gram system

`Y₁ ∂_xℓ + Y₂ ∂_tℓ = W`,  `W = X_H(ℓ τ (x,t)) - ∂_τℓ(τ,x,t)`

(Gram matrix `gramA, gramB, gramC`, determinant `gramDet`).  Its boundedness for `τ ∈ [-2,3]` and
all `(x,t) ∈ ℝ²` follows from three uniform estimates together with the *algebraic* bound
`Ycoef_norm_bound`:

* `‖∂_xℓ‖`, `‖∂_tℓ‖`, `‖∂_τℓ‖` are uniformly bounded:  off the compact strip `|x| ≤ X₀` the
  family is the zero section, so the three vectors are the *constants* `(1,0,0,0)`, `(0,1,0,0)`,
  `0`;  on the strip, the slices are `C⁷`, the family is `2π`-periodic in the angle `t`, and
  `τ ∈ [-2,3]` is compact, so the (jointly continuous) slices are bounded there.  This is the
  content of `exists_bound_of_periodic_of_std`, applied to `dX`, `dT`, `dTau`.
* `gramDet` is uniformly bounded away from `0`: it is `> 0` everywhere (`gramDet_pos`, from the
  linear independence of the two slice derivatives), it is *equal to `1`* off the compact strip
  (where the slice derivatives are the standard basis vectors), so on the compact set
  `[-2,3] × [-max X₀ 0, max X₀ 0] × [0,2π]` it has a positive minimum.  This is
  `exists_lower_of_periodic_of_std`, applied to `gramDet`.
* `‖W‖ ≤ M₀ + ‖∂_τℓ‖`, where `M₀` bounds the Hamiltonian field (`hbdd`).

Nothing here uses the regularity of `H` beyond the given `hbdd`: `hH` is carried along but not
needed.
-/

set_option autoImplicit false
noncomputable section

namespace Work.RPA3

/-! ## Elementary continuity and standard-region facts -/

/-- The inner product `ip` is continuous. -/
theorem yf_continuous_ip : Continuous fun z : PS × PS => ip z.1 z.2 := by
  simp only [ip]; fun_prop

/-- `(τ,x,t) ↦ ∂_xℓ(τ,x,t)` is continuous (it is `C⁷`). -/
theorem yf_continuous_dX (L : LagFamilyAll) :
    Continuous (fun p : ℝ × ℝ × ℝ => dX L p.1 p.2.1 p.2.2) := by
  simpa only [dX] using (contDiff_sliceDerivX L).continuous

/-- `(τ,x,t) ↦ ∂_tℓ(τ,x,t)` is continuous (it is `C⁷`). -/
theorem yf_continuous_dT (L : LagFamilyAll) :
    Continuous (fun p : ℝ × ℝ × ℝ => dT L p.1 p.2.1 p.2.2) := by
  simpa only [dT] using (contDiff_sliceDerivT L).continuous

/-- `(τ,x,t) ↦ ∂_τℓ(τ,x,t)` is continuous (it is `C⁷`). -/
theorem yf_continuous_dTau (L : LagFamilyAll) :
    Continuous (fun p : ℝ × ℝ × ℝ => dTau L p.1 p.2.1 p.2.2) := by
  simpa only [dTau] using (contDiff_sliceDerivTau L).continuous

/-- In the standard region `|x| ≥ X₀`, `∂_xℓ = (1,0,0,0)`. -/
theorem yf_dX_std (L : LagFamilyAll) (τ x t : ℝ) (hx : L.X0 ≤ |x|) :
    dX L τ x t = ((1, 0), (0, 0)) := by
  simpa only [dX] using deriv_slice_x L τ t x hx

/-- In the standard region `|x| ≥ X₀`, `∂_tℓ = (0,1,0,0)`. -/
theorem yf_dT_std (L : LagFamilyAll) (τ x t : ℝ) (hx : L.X0 ≤ |x|) :
    dT L τ x t = ((0, 1), (0, 0)) := by
  simpa only [dT] using deriv_slice_t L τ x t hx

/-- In the standard region `|x| ≥ X₀`, `∂_τℓ = 0`. -/
theorem yf_dTau_std (L : LagFamilyAll) (τ x t : ℝ) (hx : L.X0 ≤ |x|) :
    dTau L τ x t = 0 := by
  simp only [dTau]
  rw [show (fun σ : ℝ => L.ℓ σ (x, t)) = fun _ => stdZ x t from
    funext (fun σ => L.std σ x t hx)]
  simp

/-- In the standard region `|x| ≥ X₀`, the Gram determinant is `1`. -/
theorem yf_gramDet_std (L : LagFamilyAll) (τ x t : ℝ) (hx : L.X0 ≤ |x|) :
    gramDet L τ x t = 1 := by
  simp only [gramDet, gramA, gramB, gramC, yf_dX_std L τ x t hx, yf_dT_std L τ x t hx, ip]
  norm_num

/-- `(τ,x,t) ↦ gramDet L τ x t` is continuous. -/
theorem yf_continuous_gramDet (L : LagFamilyAll) :
    Continuous (fun p : ℝ × ℝ × ℝ => gramDet L p.1 p.2.1 p.2.2) := by
  simp only [gramDet, gramA, gramB, gramC]
  have hA : Continuous fun p : ℝ × ℝ × ℝ =>
      ip (dX L p.1 p.2.1 p.2.2) (dX L p.1 p.2.1 p.2.2) :=
    yf_continuous_ip.comp ((yf_continuous_dX L).prodMk (yf_continuous_dX L))
  have hB : Continuous fun p : ℝ × ℝ × ℝ =>
      ip (dX L p.1 p.2.1 p.2.2) (dT L p.1 p.2.1 p.2.2) :=
    yf_continuous_ip.comp ((yf_continuous_dX L).prodMk (yf_continuous_dT L))
  have hC : Continuous fun p : ℝ × ℝ × ℝ =>
      ip (dT L p.1 p.2.1 p.2.2) (dT L p.1 p.2.1 p.2.2) :=
    yf_continuous_ip.comp ((yf_continuous_dT L).prodMk (yf_continuous_dT L))
  exact (hA.mul hC).sub (hB.pow 2)

/-- `gramDet` is `2π`-periodic in the angle `t`. -/
theorem yf_gramDet_per (L : LagFamilyAll) (τ x t : ℝ) :
    gramDet L τ x (t + 2 * Real.pi) = gramDet L τ x t := by
  have hx := (sliceDeriv_periodic L τ x t).1
  have ht := (sliceDeriv_periodic L τ x t).2.1
  simp only [gramDet, gramA, gramB, gramC, hx, ht]

/-! ## Uniform bounds on the strip `τ ∈ [-2,3]` -/

/-- `‖∂_xℓ‖` is uniformly bounded on `τ ∈ [-2,3]`, `(x,t) ∈ ℝ²`. -/
theorem yf_dX_bounded (L : LagFamilyAll) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (-2 : ℝ) 3, ∀ x t : ℝ, ‖dX L τ x t‖ ≤ M :=
  exists_bound_of_periodic_of_std L.X0 (fun τ x t => dX L τ x t) ((1, 0), (0, 0))
    (yf_continuous_dX L)
    (fun τ x t => (sliceDeriv_periodic L τ x t).1)
    (fun τ x t hx => yf_dX_std L τ x t hx.le)

/-- `‖∂_tℓ‖` is uniformly bounded on `τ ∈ [-2,3]`, `(x,t) ∈ ℝ²`. -/
theorem yf_dT_bounded (L : LagFamilyAll) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (-2 : ℝ) 3, ∀ x t : ℝ, ‖dT L τ x t‖ ≤ M :=
  exists_bound_of_periodic_of_std L.X0 (fun τ x t => dT L τ x t) ((0, 1), (0, 0))
    (yf_continuous_dT L)
    (fun τ x t => (sliceDeriv_periodic L τ x t).2.1)
    (fun τ x t hx => yf_dT_std L τ x t hx.le)

/-- `‖∂_τℓ‖` is uniformly bounded on `τ ∈ [-2,3]`, `(x,t) ∈ ℝ²`. -/
theorem yf_dTau_bounded (L : LagFamilyAll) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (-2 : ℝ) 3, ∀ x t : ℝ, ‖dTau L τ x t‖ ≤ M :=
  exists_bound_of_periodic_of_std L.X0 (fun τ x t => dTau L τ x t) 0
    (yf_continuous_dTau L)
    (fun τ x t => (sliceDeriv_periodic L τ x t).2.2)
    (fun τ x t hx => yf_dTau_std L τ x t hx.le)

/-- `gramDet` is uniformly bounded below on `τ ∈ [-2,3]`, `(x,t) ∈ ℝ²`. -/
theorem yf_gramDet_lower (L : LagFamilyAll) :
    ∃ c : ℝ, 0 < c ∧ ∀ τ ∈ Set.Icc (-2 : ℝ) 3, ∀ x t : ℝ, c ≤ gramDet L τ x t :=
  exists_lower_of_periodic_of_std L.X0 (fun τ x t => gramDet L τ x t)
    (yf_continuous_gramDet L) (yf_gramDet_per L) (fun τ x t => gramDet_pos L τ x t)
    (fun τ x t hx => yf_gramDet_std L τ x t hx.le)

/-! ## The target -/

theorem Yfield_bounded (L : LagFamilyAll) (H : ℝ → PS → ℝ)
    (hH : ContDiff ℝ 4 (fun z : ℝ × PS => H z.1 z.2))
    (hbdd : ∃ M : ℝ, ∀ t x, ‖hamVF (H t) x‖ ≤ M) :
    ∃ M : ℝ, ∀ τ ∈ Set.Icc (-2 : ℝ) 3, ∀ q : ℝ × ℝ, ‖Yfield L H τ q‖ ≤ M := by
  obtain ⟨M0, hM0⟩ := hbdd
  obtain ⟨mx, hmx0, hmx⟩ := yf_dX_bounded L
  obtain ⟨mt, hmt0, hmt⟩ := yf_dT_bounded L
  obtain ⟨mu, hmu0, hmu⟩ := yf_dTau_bounded L
  obtain ⟨c, hcpos, hc⟩ := yf_gramDet_lower L
  refine ⟨32 * mx * mt * (max M0 0 + mu) * (mx + mt) / c, ?_⟩
  intro τ hτ q
  have h := Ycoef_norm_bound L H τ q.1 q.2 (max M0 0) mx mt mu c
    (le_trans (hM0 τ (L.ℓ τ (q.1, q.2))) (le_max_left M0 0))
    (hmx τ hτ q.1 q.2) (hmt τ hτ q.1 q.2) (hmu τ hτ q.1 q.2) (hc τ hτ q.1 q.2) hcpos
    (le_max_right M0 0) hmx0 hmt0 hmu0
  simpa only [Yfield_apply] using h

end Work.RPA3
