import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.dentDeform_homeomorph

/-!
# The deformed surface is again the surface of a diffeomorphism

`Work.Drive.Final.AnyDentDatum.deform` is the deformation `z ↦ z + a'·χ(‖z − centre‖/r)·d` of a
dent at an event of the tilted sweep.  This file proves the lemma `exists_dentSurface` which the
(L)-route uses when it replaces the sweep's surface `F = ψ(F_std)` by the *dented* surface: the
deformed surface is again the image of the standard torus under a diffeomorphism `ψ'` of `ℝ³`, and
the parametrisation of `ψ'` is the deformation of the parametrisation of `ψ`.

The mathematical content is that `deform` is a **diffeomorphism** of `ℝ³`:

* the cutoff `χ` is analytic (`ContDiff ℝ ⊤ D.χ`) and *constant `1` on a neighbourhood of `0`*
  (`D.χ_eq_one_near`, here `hχ1 : |t| ≤ 1/2 → χ t = 1`), so the radial profile
  `z ↦ χ(‖z − centre‖/r)` is analytic: it is locally constant around the centre, where the norm is
  not differentiable, and a composition of analytic maps away from it
  (`contDiff_comp_norm_chi`);
* the flip `F z = (a'·χ(‖z − centre‖/r))·d` is Lipschitz of constant `κ‖a'‖/r < 1` (the mean value
  theorem for `χ`, exactly as in `dentDeform_homeomorph`), hence `‖fderiv ℝ F x‖ ≤ κ|a'|/r < 1` at
  every point (`norm_fderiv_dentFlip_lt_one`): the derivative of `deform` is everywhere an
  isomorphism "close to the identity";
* consequently `deform` is a *bijection* (`dentDeform_homeomorph`) that is `C^∞` with invertible
  derivative everywhere, and its inverse — the unique solution map — is `C^∞` by the inverse
  function theorem (`contDiff_of_inverse_add`).

The last step is the classical statement that the global inverse of a `D²`-smooth bijection with
everywhere invertible derivative is smooth: at a point `y = deform x` the local inverse supplied by
`ContDiffAt.to_localInverse` is smooth, and it agrees near `y` with the (globally defined) inverse
because the local inverse is a right inverse of `deform` and `deform` is injective.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Final

noncomputable section

/-- **The radial profile of an analytic cutoff is analytic.**  If `χ` is analytic on `ℝ` and is
equal to `1` on a neighbourhood of `0`, then `z ↦ χ(‖z − centre‖/r)` is analytic on `ℝ³`
(`r ≠ 0`): it is locally constant near `centre` — where `‖· − centre‖` fails to be differentiable —
and a composition of analytic maps everywhere else. -/
theorem contDiff_comp_norm_chi {χ : ℝ → ℝ} {centre : R3} {r : ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hε : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| ≤ ε → χ t = 1) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : R3 => χ (‖z - centre‖ / r)) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  rcases eq_or_ne z centre with h | hz
  · subst h
    refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (1 : ℝ))) ?_
    obtain ⟨ε, hε0, hε1⟩ := hε
    filter_upwards [Metric.ball_mem_nhds (z : R3) (by positivity : (0 : ℝ) < ε * r)] with y hy
    have hy' : ‖y - z‖ < ε * r := by
      rw [Metric.mem_ball, dist_eq_norm] at hy
      simpa using hy
    have hle : ‖y - z‖ / r ≤ ε := by rw [div_le_iff₀ hr]; linarith
    have h1 : |‖y - z‖ / r| ≤ ε := by
      rw [abs_of_nonneg (by positivity)]
      exact hle
    exact hε1 _ h1
  · have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : R3 => ‖y - centre‖) z :=
      ContDiffAt.norm ℝ ((contDiffAt_id (x := z)).sub contDiffAt_const) (sub_ne_zero.mpr hz)
    have hdiv : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : R3 => ‖y - centre‖ / r) z := hnorm.div_const r
    have := hχ.contDiffAt.comp z hdiv
    simpa [Function.comp_def] using this

/-- **The flip of a dent is analytic.**  The perturbation `z ↦ (a'·χ(‖z − centre‖/r))·d` of the
identity is analytic whenever the cutoff is. -/
theorem contDiff_dentFlip {χ : ℝ → ℝ} {centre d : R3} {r a' : ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hε : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| ≤ ε → χ t = 1) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : R3 => (a' * χ (‖z - centre‖ / r)) • d) :=
  ((contDiff_const.mul (contDiff_comp_norm_chi hχ hε hr)).smul_const d)

/-- **The derivative of the flip is a strict contraction.**  With `χ` differentiable, `|χ'| ≤ κ`,
`‖d‖ ≤ 1`, `0 < r` and `|a'|·κ < r`, the flip `z ↦ (a'·χ(‖z − centre‖/r))·d` is Lipschitz of
constant `κ|a'|/r < 1`; by the mean value inequality its derivative has norm `< 1` everywhere.
(No differentiability of the flip is needed: `fderiv` is `0` where the map is not differentiable,
and the bound is then trivial.) -/
theorem norm_fderiv_dentFlip_lt_one {χ : ℝ → ℝ} {centre d : R3} {r a' κ : ℝ}
    (hr : 0 < r) (hd : ‖d‖ ≤ 1) (hχdiff : Differentiable ℝ χ)
    (hχb : ∀ t : ℝ, |deriv χ t| ≤ κ) (ha' : |a'| * κ < r) (x : R3) :
    ‖fderiv ℝ (fun z : R3 => (a' * χ (‖z - centre‖ / r)) • d) x‖ < 1 := by
  have hκ0 : 0 ≤ κ := (abs_nonneg (deriv χ 0)).trans (hχb 0)
  have hχlip : LipschitzWith (NNReal.mk κ hκ0) χ := by
    apply lipschitzWith_of_nnnorm_deriv_le hχdiff
    intro t
    rw [← NNReal.coe_le_coe, NNReal.coe_mk]
    simpa [Real.norm_eq_abs] using hχb t
  have hmain : ∀ z : R3,
      ‖(a' * χ (‖z - centre‖ / r)) • d - (a' * χ (‖x - centre‖ / r)) • d‖
        ≤ (κ * |a'| / r) * ‖z - x‖ := by
    intro z
    have hsub : (a' * χ (‖z - centre‖ / r)) • d - (a' * χ (‖x - centre‖ / r)) • d
        = (a' * (χ (‖z - centre‖ / r) - χ (‖x - centre‖ / r))) • d := by
      rw [mul_sub, sub_smul]
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_mul]
    have h2 : |χ (‖z - centre‖ / r) - χ (‖x - centre‖ / r)|
        ≤ κ * |‖z - centre‖ / r - ‖x - centre‖ / r| := by
      have h := hχlip.dist_le_mul (‖z - centre‖ / r) (‖x - centre‖ / r)
      rw [Real.dist_eq] at h
      simpa only [Real.dist_eq, NNReal.coe_mk] using h
    have h3 : |‖z - centre‖ / r - ‖x - centre‖ / r| ≤ ‖z - x‖ / r := by
      rw [div_sub_div_same, abs_div, abs_of_pos hr]
      have h4 : |‖z - centre‖ - ‖x - centre‖| ≤ ‖z - x‖ := by
        have h := abs_norm_sub_norm_le (z - centre) (x - centre)
        rwa [show (z - centre) - (x - centre) = z - x by abel] at h
      exact div_le_div_of_nonneg_right h4 hr.le
    calc |a'| * |χ (‖z - centre‖ / r) - χ (‖x - centre‖ / r)| * ‖d‖
        ≤ |a'| * (κ * (‖z - x‖ / r)) * ‖d‖ := by
          gcongr
          exact h2.trans (mul_le_mul_of_nonneg_left h3 hκ0)
      _ ≤ |a'| * (κ * (‖z - x‖ / r)) * 1 := by
          gcongr
      _ = (κ * |a'| / r) * ‖z - x‖ := by ring
  have hC0 : (0 : ℝ) ≤ κ * |a'| / r := by positivity
  have h1 := norm_fderiv_le_of_lip' ℝ hC0 (Filter.Eventually.of_forall hmain)
  have h2 : κ * |a'| / r < 1 := by
    rw [div_lt_one hr]
    have h3 : κ * |a'| < r := by rw [mul_comm]; exact ha'
    simpa using h3
  linarith

set_option synthInstance.maxHeartbeats 200000 in
/-- **The inverse of a strictly contracting perturbation of the identity is smooth.**  Let
`F : ℝ³ → ℝ³` be analytic with `‖fderiv ℝ F x‖ < 1` everywhere, and let `g` be a two-sided inverse
of `x ↦ x + F x`.  Then `g` is analytic.

At a point `y`, put `x = g y`.  The map `x ↦ x + F x` is analytic at `x` and its derivative there is
`1 + fderiv ℝ F x`, the sum of the identity and a linear contraction; it is therefore invertible, and
the inverse function theorem gives a smooth local inverse `φ` at `y`.  Since `g` is a left inverse of
`x ↦ x + F x`, the two agree *eventually* near `y` (both are left inverses of a locally invertible
map), so `g` is smooth at `y`. -/
theorem contDiff_of_inverse_add {F : R3 → R3} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hgrad : ∀ x : R3, ‖fderiv ℝ F x‖ < 1) {g : R3 → R3}
    (hright : ∀ y : R3, g y + F (g y) = y) (hleft : ∀ x : R3, g (x + F x) = x) :
    ContDiff ℝ (⊤ : ℕ∞) g := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have hfc : ContDiff ℝ (⊤ : ℕ∞) (fun u : R3 => u + F u) := by
    have h := hF.add contDiff_id
    simpa [add_comm] using h
  have hfdiff : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : R3 => u + F u) (g y) := hfc.contDiffAt
  have hFder : HasFDerivAt F (fderiv ℝ F (g y)) (g y) :=
    (hF.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have hfder : HasFDerivAt (fun u : R3 => u + F u)
      (1 + fderiv ℝ F (g y)) (g y) :=
    (hasFDerivAt_id (g y)).add hFder
  set T : R3 →L[ℝ] R3 := fderiv ℝ F (g y) with hT
  have hTlt : ‖T‖ < 1 := hgrad (g y)
  have hnegT : ‖(-T)‖ < 1 := by simpa using hTlt
  have hev : (ContinuousLinearEquiv.ofUnit (Units.oneSub (-T) hnegT) : R3 →L[ℝ] R3) = 1 + T := by
    show (↑(Units.oneSub (-T) hnegT) : R3 →L[ℝ] R3) = 1 + T
    rw [Units.val_oneSub, sub_neg_eq_add]
  have hfder' : HasFDerivAt (fun u : R3 => u + F u)
      (ContinuousLinearEquiv.ofUnit (Units.oneSub (-T) hnegT) : R3 →L[ℝ] R3) (g y) := by
    rw [hev]; exact hfder
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hstrict : HasStrictFDerivAt (fun u : R3 => u + F u)
      (ContinuousLinearEquiv.ofUnit (Units.oneSub (-T) hnegT) : R3 →L[ℝ] R3) (g y) :=
    hfdiff.hasStrictFDerivAt' hfder' hn
  have huniq : ∀ᶠ z in nhds ((fun u : R3 => u + F u) (g y)),
      g z = hfdiff.localInverse hfder' hn z :=
    HasStrictFDerivAt.localInverse_unique hstrict
      (Filter.Eventually.of_forall (fun u : R3 => hleft u))
  have hcont : ContDiffAt ℝ (⊤ : ℕ∞) (hfdiff.localInverse hfder' hn) (g y + F (g y)) := by
    have h := hfdiff.to_localInverse hfder' hn
    simpa using h
  rw [hright y] at hcont
  simp only [hright y] at huniq
  exact hcont.congr_of_eventuallyEq huniq

/-- **The dent deformation is a diffeomorphism of `ℝ³`.**  Under the standing hypotheses of the
design — analytic cutoff, constant `1` on a neighbourhood of `0`, `‖d‖ = 1`, `0 < r`, `0 < κ`,
`|χ'| ≤ κ`, `|a'|·κ < r` — the dent deformation
`z ↦ z + a'·χ(‖z − centre‖/r)·d` is a diffeomorphism of `ℝ³`. -/
theorem exists_diffeo_dentDeform {χ : ℝ → ℝ} {centre d : R3} {r a' κ : ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hε : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| ≤ ε → χ t = 1)
    (hκ : 0 < κ) (hr : 0 < r) (hd : ‖d‖ ≤ 1) (hχdiff : Differentiable ℝ χ)
    (hχb : ∀ t : ℝ, |deriv χ t| ≤ κ) (ha' : |a'| * κ < r) :
    ∃ Ψ : Submission.Diffeo, ∀ z : R3, Ψ z = dentDeform χ centre d r a' z := by
  obtain ⟨Φ, hΦ⟩ := dentDeform_homeomorph (χ := χ) (centre := centre) (d := d) (r := r)
    (a' := a') hκ hr hd hχdiff hχb ha'
  set F : R3 → R3 := fun z => (a' * χ (‖z - centre‖ / r)) • d with hFdef
  have hFcd : ContDiff ℝ (⊤ : ℕ∞) F := contDiff_dentFlip hχ hε hr
  have hgrad : ∀ x : R3, ‖fderiv ℝ F x‖ < 1 :=
    fun x => norm_fderiv_dentFlip_lt_one hr hd hχdiff hχb ha' x
  have hdeform : ∀ z : R3, Φ z = z + F z := by
    intro z
    rw [hΦ z]
    simp only [hFdef, dentDeform]
  have hleft : ∀ x : R3, Φ.symm (x + F x) = x := by
    intro x
    rw [← hdeform x]
    exact Φ.left_inv x
  have hright : ∀ y : R3, Φ.symm y + F (Φ.symm y) = y := by
    intro y
    rw [← hdeform (Φ.symm y)]
    exact Φ.right_inv y
  have hginv : ContDiff ℝ (⊤ : ℕ∞) Φ.symm := contDiff_of_inverse_add hFcd hgrad hright hleft
  have hfcd : ContDiff ℝ (⊤ : ℕ∞) (fun z : R3 => z + F z) := by
    have h := hFcd.add contDiff_id
    simpa [add_comm] using h
  refine ⟨{ toFun := fun z => z + F z
            invFun := Φ.symm
            smooth_toFun := hfcd
            smooth_invFun := hginv
            left_inv := hleft
            right_inv := hright }, ?_⟩
  intro z
  simp only [hFdef, dentDeform]

/-- **Pardon's dented surface is again a `ψ'(F_std)`.**  Given an `AnyDentDatum` whose cutoff is
analytic and constant `1` on `[-1/2, 1/2]` and whose depth satisfies `a'·κ < r`, the deformed
surface `deform '' (ψ(F_std))` is the surface of a diffeomorphism `ψ'` of `ℝ³` whose parametrisation
is the deformation of the parametrisation of `ψ`:

`par ψ' = deform ∘ par ψ`,  `(torusOf ψ').carrier = deform '' (torusOf ψ).carrier`.

The diffeomorphism is `ψ' = deform ∘ ψ` (with inverse `ψ⁻¹ ∘ deform⁻¹`), which makes sense because
`deform` is a diffeomorphism of `ℝ³` by `exists_diffeo_dentDeform`. -/
theorem exists_dentSurface {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) D.χ) (hχ1 : ∀ t : ℝ, |t| ≤ 1 / 2 → D.χ t = 1)
    (ha : D.a' * D.κ < D.r) :
    ∃ ψ' : Submission.Diffeo,
      (∀ q : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ' q = D.deform (Work.BoxShrink.Pinch.par ψ q)) ∧
      (Work.Drive.EpsSphere.torusOf ψ').carrier =
        D.deform '' (Work.Drive.EpsSphere.torusOf ψ).carrier := by
  obtain ⟨Ψ, hΨ⟩ := exists_diffeo_dentDeform (χ := D.χ) (centre := D.centre) (d := D.d)
    (r := D.r) (a' := D.a') (κ := D.κ) hχ ⟨1 / 2, by norm_num, hχ1⟩ D.κ_pos D.r_pos
    D.d_norm.le (hχ.differentiable (by simp)) D.χ_deriv_bound
    (by rw [abs_of_pos D.a'_pos]; exact ha)
  let ψ' : Submission.Diffeo :=
    { toFun := fun z => Ψ (ψ z)
      invFun := fun y => ψ.invFun (Ψ.invFun y)
      smooth_toFun := Ψ.smooth_toFun.comp ψ.smooth_toFun
      smooth_invFun := ψ.smooth_invFun.comp Ψ.smooth_invFun
      left_inv := by
        intro z
        show ψ.invFun (Ψ.invFun (Ψ (ψ z))) = z
        rw [Ψ.left_inv (ψ z), ψ.left_inv z]
      right_inv := by
        intro y
        show Ψ (ψ (ψ.invFun (Ψ.invFun y))) = y
        rw [ψ.right_inv (Ψ.invFun y), Ψ.right_inv y] }
  have hpar : ∀ q : ℝ × ℝ,
      Work.BoxShrink.Pinch.par ψ' q = D.deform (Work.BoxShrink.Pinch.par ψ q) := by
    intro q
    obtain ⟨x, y⟩ := q
    simp only [Work.BoxShrink.Pinch.par_apply]
    exact hΨ _
  refine ⟨ψ', hpar, ?_⟩
  have hrange : Set.range (Work.BoxShrink.Pinch.par ψ') =
      D.deform '' Set.range (Work.BoxShrink.Pinch.par ψ) := by
    rw [show Work.BoxShrink.Pinch.par ψ' =
        D.deform ∘ Work.BoxShrink.Pinch.par ψ from funext hpar]
    exact Set.range_comp D.deform (Work.BoxShrink.Pinch.par ψ)
  change (Work.Smooth.Morse.torus ψ').carrier = D.deform '' (Work.Smooth.Morse.torus ψ).carrier
  rw [Work.BoxShrink.Pinch.carrier_eq_range ψ', Work.BoxShrink.Pinch.carrier_eq_range ψ]
  exact hrange

end

end Work.Drive.Final
