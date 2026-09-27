import Mathlib
import Submission.Work.Drive.N2Lead.mobiusUpperCoreKit
import Submission.Work.Drive.N2C.mobiusBridgeCurveRow
import Submission.Work.Drive.N2Lead.mobiusArcPicSymm

/-!
# The polar curve row on the whole `π`-zone `{|φ - k π| ≤ φE}`

The target lemma `Work.Drive.N2Lead.polarRowZone` is the *curve* row of the marked component of the
anchor level of the Möbius certificate, for **every** polar angle `φ` within `φE` of an integral
multiple of `π` — not only on the bridge zone `[-φE, φE]` handled by
`Work.Drive.N2C.mobiusBridgeCurveRow`.  The extra zone is reached by two exact symmetries of the
picture `W z = pushY Dp εp 1 (twistX ε (-1) (cE3 z))`:

* `Work.Drive.N2Lead.mobiusArcPicSymm` (the antipodal and the conjugation symmetry of the pushed arc)
  combined gives `proj2 (W (-z)) = -star (proj2 (W z))`;
* the polar point at `φ + π` is `-z` with `z = r φ · e^{iφ}` (`hrpi` and `exp (iπ) = -1`), so
  `polarPic (φ + π) = -star (polarPic φ)`;
* differentiating that identity (`deriv_comp_add_const` + `HasDerivAt.star`) gives
  `deriv polarPic (φ + π) = -star (deriv polarPic φ)`.

Since `star (-star v) * (-star d) = v * star d` and `(v * star d).im = -(star v * d).im`, the two
rows are literally preserved by the `π`-shift; the `π`-shifts therefore generate the whole zone.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-- The two pointwise rows of the polar picture at the angle `φ`: the picture does not vanish and
its angular rate about the origin does not vanish. -/
def polarRows (r : ℝ → ℝ) (Dp εp ε φ : ℝ) : Prop :=
  polarPic r Dp εp ε φ ≠ 0 ∧
    (star (polarPic r Dp εp ε φ) * deriv (polarPic r Dp εp ε) φ).im ≠ 0

/-- For complex numbers `w, w'`: `Im (w · star w') = - Im (star w · w')`. -/
theorem star_mul_star_im (w w' : ℂ) : (w * star w').im = -(star w * w').im := by
  simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- **The antipodal reflection** of the pushed, twisted picture: the polar point of `-z` projects to
the conjugate of the negative of the projection of `z`.  It is the composition of the two symmetries
of `Work.Drive.N2Lead.mobiusArcPicSymm` (`z ↦ -star z` is `z ↦ -star (star z)`). -/
theorem proj2_pushY_twistX_cE3_neg {ε εp Dp : ℝ} (hε : 0 < ε) (hεp : 0 < εp) (z : ℂ) :
    proj2 (pushY Dp εp 1 (twistX ε (-1) (Work.Drive.N2.cE3 (-z))))
      = -star (proj2 (pushY Dp εp 1 (twistX ε (-1) (Work.Drive.N2.cE3 z)))) := by
  have h1 := (mobiusArcPicSymm (ε := ε) (εp := εp) (Dp := Dp) hε hεp (star z)).1
  have h2 := (mobiusArcPicSymm (ε := ε) (εp := εp) (Dp := Dp) hε hεp z).2
  have hzz : -star (star z) = -z := by rw [star_star]
  rw [hzz] at h1
  rw [h1, h2]

/-- The derivative of `y ↦ -star (f y)`. -/
theorem deriv_of_neg_star {f : ℝ → ℂ} {x : ℝ} (hd : DifferentiableAt ℝ f x) :
    deriv (fun y => -(star (f y))) x = -(star (deriv f x)) := by
  have h : HasDerivAt (fun y : ℝ => -(star (f y))) (-(star (deriv f x))) x :=
    hd.hasDerivAt.star.neg
  simpa using h.deriv

/-- The polar picture is differentiable as soon as the profile is (through its explicit model
`Work.Drive.N2C.brM`). -/
theorem differentiableAt_polarPic {r : ℝ → ℝ} {Dp εp ε : ℝ}
    (hrdiff : ∀ x : ℝ, DifferentiableAt ℝ r x) (x : ℝ) :
    DifferentiableAt ℝ (polarPic r Dp εp ε) x := by
  have hfun : polarPic r Dp εp ε = Work.Drive.N2C.brM r Dp εp ε :=
    funext (fun ψ => Work.Drive.N2C.pushTwist_proj2_eq r Dp εp ε ψ)
  rw [hfun]
  exact (Work.Drive.N2C.hasDerivAt_brM r Dp εp ε x (hrdiff x)).differentiableAt

/-- **The `π`-shift of the polar picture**: with a `π`-periodic profile, the picture at `φ + π` is the
conjugate of the negative of the picture at `φ`. -/
theorem polarPic_add_pi {r : ℝ → ℝ} (hrpi : ∀ φ : ℝ, r (φ + Real.pi) = r φ) {Dp εp ε : ℝ}
    (hε : 0 < ε) (hεp : 0 < εp) (φ : ℝ) :
    polarPic r Dp εp ε (φ + Real.pi) = -star (polarPic r Dp εp ε φ) := by
  have hexp : Complex.exp ((((φ + Real.pi : ℝ)) : ℂ) * Complex.I)
      = -Complex.exp (((φ : ℝ) : ℂ) * Complex.I) := by
    have hs : (((φ + Real.pi : ℝ)) : ℂ) * Complex.I
        = (φ : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by push_cast; ring
    rw [hs, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  simp only [polarPic]
  rw [hrpi φ, hexp, mul_neg]
  exact proj2_pushY_twistX_cE3_neg hε hεp _

/-- The derivative form of `Work.Drive.N2Lead.polarPic_add_pi`. -/
theorem deriv_polarPic_add_pi {r : ℝ → ℝ} (hrpi : ∀ φ : ℝ, r (φ + Real.pi) = r φ) {Dp εp ε : ℝ}
    (hε : 0 < ε) (hεp : 0 < εp) (hrdiff : ∀ x : ℝ, DifferentiableAt ℝ r x) (φ : ℝ) :
    deriv (polarPic r Dp εp ε) (φ + Real.pi) = -star (deriv (polarPic r Dp εp ε) φ) := by
  have hfun : (fun y : ℝ => polarPic r Dp εp ε (y + Real.pi))
      = fun y : ℝ => -(star (polarPic r Dp εp ε y)) :=
    funext (fun y => polarPic_add_pi hrpi hε hεp y)
  rw [← deriv_comp_add_const (f := polarPic r Dp εp ε) (a := Real.pi) (x := φ), hfun,
    deriv_of_neg_star (differentiableAt_polarPic hrdiff φ)]

/-- **The rows are invariant under the `π`-shift.** -/
theorem polarRows_add_pi {r : ℝ → ℝ} {Dp εp ε : ℝ}
    (hrpi : ∀ φ : ℝ, r (φ + Real.pi) = r φ) (hε : 0 < ε) (hεp : 0 < εp)
    (hrdiff : ∀ x : ℝ, DifferentiableAt ℝ r x) (ψ : ℝ) :
    polarRows r Dp εp ε (ψ + Real.pi) ↔ polarRows r Dp εp ε ψ := by
  unfold polarRows
  set v : ℂ := polarPic r Dp εp ε ψ with hv
  set d : ℂ := deriv (polarPic r Dp εp ε) ψ with hd
  have hval : polarPic r Dp εp ε (ψ + Real.pi) = -star v := by
    rw [hv]
    exact polarPic_add_pi hrpi hε hεp ψ
  have hder : deriv (polarPic r Dp εp ε) (ψ + Real.pi) = -star d := by
    rw [hd]
    exact deriv_polarPic_add_pi hrpi hε hεp hrdiff ψ
  have hne : (-star v) ≠ 0 ↔ v ≠ 0 := by
    constructor
    · intro h h0
      exact h (by rw [h0]; simp)
    · intro h h0
      exact h (by have := congrArg star h0; simpa using this)
  have hrate : (star (-star v) * (-star d)).im ≠ 0 ↔ (star v * d).im ≠ 0 := by
    have hterm : star (-star v) * (-star d) = v * star d := by
      rw [star_neg, star_star]; ring
    rw [hterm, star_mul_star_im]
    exact neg_ne_zero
  rw [hval, hder]
  exact and_congr hne hrate

theorem polarRowZone {ηs m φE ε εp Dp : ℝ} {r : ℝ → ℝ} (hηs : 0 < ηs)
    (hφE : φE = Work.Drive.N2Lead.mobiusPhiE ηs m) (hε : 0 < ε) (hεp : 0 < εp) (hDp : 0 ≤ Dp)
    (hrsm : ContDiff ℝ 1 r) (hrpos : ∀ φ : ℝ, 0 < r φ) (hrev : ∀ φ : ℝ, r (-φ) = r φ)
    (hrpi : ∀ φ : ℝ, r (φ + Real.pi) = r φ)
    (hlo : ∀ φ ∈ Set.Icc (0 : ℝ) φE, Real.sqrt (ηs ^ 2 + m ^ 2) ≤ r φ ^ 2)
    (hrdec : ∀ φ ∈ Set.Icc (0 : ℝ) φE, deriv r φ ≤ 0)
    (hεsmall : ∀ φ ∈ Set.Icc (-φE) φE, ε ≤ r φ * Real.cos φ) :
    ∀ φ : ℝ, (∃ k : ℤ, |φ - (k : ℝ) * Real.pi| ≤ φE) →
      Work.Drive.N2Lead.polarPic r Dp εp ε φ ≠ 0 ∧
      (star (Work.Drive.N2Lead.polarPic r Dp εp ε φ)
        * deriv (Work.Drive.N2Lead.polarPic r Dp εp ε) φ).im ≠ 0 := by
  have hrdiff : ∀ x : ℝ, DifferentiableAt ℝ r x :=
    fun x => (hrsm.differentiable (by simp)).differentiableAt
  have hbridge := Work.Drive.N2C.mobiusBridgeCurveRow hηs hφE hε hεp hDp hrsm hrpos hrev hlo
    hrdec hεsmall
  have hbase : ∀ ψ ∈ Set.Icc (-φE) φE, polarRows r Dp εp ε ψ :=
    fun ψ hψ => hbridge ψ hψ
  have hshift : ∀ ψ : ℝ, polarRows r Dp εp ε (ψ + Real.pi) ↔ polarRows r Dp εp ε ψ :=
    fun ψ => polarRows_add_pi hrpi hε hεp hrdiff ψ
  have hnat : ∀ n : ℕ, ∀ ψ : ℝ,
      polarRows r Dp εp ε (ψ + (n : ℝ) * Real.pi) ↔ polarRows r Dp εp ε ψ := by
    intro n
    induction n with
    | zero => intro ψ; simp
    | succ k ih =>
      intro ψ
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have h1 : ψ + ((k : ℝ) + 1) * Real.pi = (ψ + (k : ℝ) * Real.pi) + Real.pi := by ring
      rw [hcast, h1, hshift, ih ψ]
  intro φ hk
  show polarRows r Dp εp ε φ
  obtain ⟨k, hkabs⟩ := hk
  have hδmem : (φ - (k : ℝ) * Real.pi) ∈ Set.Icc (-φE) φE := by
    have h := abs_le.mp hkabs
    exact ⟨h.1, h.2⟩
  have hδrow : polarRows r Dp εp ε (φ - (k : ℝ) * Real.pi) := hbase _ hδmem
  rcases lt_or_ge k 0 with hkneg | hk0
  · have hkR : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
      have h : ((k.natAbs : ℤ)) = -k := by
        rw [← Int.natAbs_neg k, Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ -k)]
      rw [← Int.cast_natCast, h]
      push_cast
      ring
    have hnatk := hnat k.natAbs φ
    have hδeq : φ + ((k.natAbs : ℕ) : ℝ) * Real.pi = φ - (k : ℝ) * Real.pi := by
      rw [hkR]; ring
    exact hnatk.mp (hδeq ▸ hδrow)
  · have hkR : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
      have h : ((k.toNat : ℤ)) = k := Int.toNat_of_nonneg hk0
      rw [← Int.cast_natCast, h]
    have hnatk := hnat k.toNat (φ - (k : ℝ) * Real.pi)
    have hφeq : φ = (φ - (k : ℝ) * Real.pi) + ((k.toNat : ℕ) : ℝ) * Real.pi := by
      rw [hkR]; ring
    rw [hφeq]
    exact hnatk.mpr hδrow

end

end Work.Drive.N2Lead
