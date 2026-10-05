import Mathlib
import Submission.Work.RPB.Port.Drive.rot90

/-!
# Straightening a smooth plane curve near a regular point

Let `G : ℝ → ℝ × ℝ` be a smooth parametrisation of a plane curve with `G'(0) ≠ 0`.  The map

`z ↦ G z.1 + z.2 • rot90 (G' 0)`

sends the vertical line over `t` to the normal line of the curve at `G t`; its derivative at `0` is
the linear map `z ↦ z.1 • G' 0 + z.2 • rot90 (G' 0)`, whose matrix has determinant `‖G' 0‖² > 0`.
Hence it is invertible, and the inverse function theorem exhibits it as an `OpenPartialHomeomorph`
near the origin: this is `curve_straightening`, the local trivialisation of a regular curve used to
put a smooth Jordan curve into the normal form "graph of a function over its tangent line" near
each point.

The proof is a direct application of the inverse function theorem in Mathlib
(`ContDiffAt.toOpenPartialHomeomorph`), together with the elementary fact that `v` and `rot90 v` are
linearly independent for `v ≠ 0`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.RPB.Port.Drive

/-- The derivative at `0` of the straightening map `z ↦ G z.1 + z.2 • rot90 (G' 0)`, as a
continuous linear endomorphism of `ℝ × ℝ`.  It sends `z ↦ z.1 • v + z.2 • rot90 v`; note that the
`toSpanSingleton` form below is the one produced by `HasFDerivAt.comp` for the `G z.1` summand. -/
def straightenLin (v : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.toSpanSingleton ℝ v).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (rot90 v)

lemma straightenLin_apply (v z : ℝ × ℝ) :
    straightenLin v z = z.1 • v + z.2 • rot90 v := by
  simp [straightenLin, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.toSpanSingleton_apply]

/-- `v` and its right-angle rotation are linearly independent for `v ≠ 0`: the only combination
`a • v + b • rot90 v` vanishing is the trivial one. -/
lemma smul_add_smul_rot90_eq_zero {v : ℝ × ℝ} (hv : v ≠ 0) {a b : ℝ}
    (h : a • v + b • rot90 v = 0) : a = 0 ∧ b = 0 := by
  have h1 : a * v.1 + b * (-v.2) = 0 := by
    have := congrArg Prod.fst h
    simpa [rot90] using this
  have h2 : a * v.2 + b * v.1 = 0 := by
    have := congrArg Prod.snd h
    simpa [rot90] using this
  have hc : v.1 ^ 2 + v.2 ^ 2 ≠ 0 := by
    intro hc
    apply hv
    have h1' : v.1 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg v.2]
    have h2' : v.2 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg v.2]
    exact Prod.ext h1' h2'
  have e1 : a * v.1 = b * v.2 := by linarith
  have e2 : a * v.2 = -(b * v.1) := by linarith
  have e3 : b * v.2 = a * v.1 := by linarith
  have e4 : b * v.1 = -(a * v.2) := by linarith
  constructor
  · have key : a * (v.1 ^ 2 + v.2 ^ 2) = 0 := by
      calc a * (v.1 ^ 2 + v.2 ^ 2) = (a * v.1) * v.1 + (a * v.2) * v.2 := by ring
        _ = (b * v.2) * v.1 + (-(b * v.1)) * v.2 := by rw [e1, e2]
        _ = 0 := by ring
    exact (mul_eq_zero.mp key).resolve_right hc
  · have key : b * (v.1 ^ 2 + v.2 ^ 2) = 0 := by
      calc b * (v.1 ^ 2 + v.2 ^ 2) = (b * v.1) * v.1 + (b * v.2) * v.2 := by ring
        _ = (-(a * v.2)) * v.1 + (a * v.1) * v.2 := by rw [e4, e3]
        _ = 0 := by ring
    exact (mul_eq_zero.mp key).resolve_right hc

lemma straightenLin_injective {v : ℝ × ℝ} (hv : v ≠ 0) : Function.Injective (straightenLin v) := by
  intro p q hpq
  have hz : straightenLin v (p - q) = 0 := by rw [map_sub, hpq, sub_self]
  rw [straightenLin_apply] at hz
  obtain ⟨h1, h2⟩ := smul_add_smul_rot90_eq_zero hv hz
  have hp : p.1 = q.1 := sub_eq_zero.mp (by simpa using h1)
  have hq : p.2 = q.2 := sub_eq_zero.mp (by simpa using h2)
  exact Prod.ext hp hq

/-- **Straightening a smooth curve at a regular point.**  If `G : ℝ → ℝ × ℝ` is smooth with
`G'(0) ≠ 0`, the map `z ↦ G z.1 + z.2 • rot90 (G' 0)` (the curve translated along its normal
direction) is an open partial homeomorphism near `0`: there is `r > 0` such that the ball of radius
`r` around `0` lies in its source. -/
theorem curve_straightening (G : ℝ → ℝ × ℝ) (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    (hder : deriv G 0 ≠ 0) :
    ∃ (r : ℝ) (Φ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)), 0 < r ∧
      (∀ z : ℝ × ℝ, z ∈ Metric.ball (0 : ℝ × ℝ) r → z ∈ Φ.source) ∧
      (∀ z : ℝ × ℝ, Φ z = G z.1 + z.2 • Work.RPB.Port.Drive.rot90 (deriv G 0)) := by
  have hdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℝ × ℝ => G z.1 + z.2 • rot90 (deriv G 0)) := by fun_prop
  have hderiv : HasFDerivAt (fun z : ℝ × ℝ => G z.1 + z.2 • rot90 (deriv G 0))
      (straightenLin (deriv G 0)) 0 := by
    have hG₀ : HasFDerivAt G (ContinuousLinearMap.toSpanSingleton ℝ (deriv G 0)) 0 := by
      have hdiffG : DifferentiableAt ℝ G 0 := (hG.contDiffAt).differentiableAt (by simp)
      exact (hdiffG.hasDerivAt).hasFDerivAt
    have h1 := hG₀.comp 0 ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := (0 : ℝ × ℝ)))
    have h2 : HasFDerivAt (fun z : ℝ × ℝ => z.2 • rot90 (deriv G 0))
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (rot90 (deriv G 0))) 0 :=
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)
        (rot90 (deriv G 0))).hasFDerivAt
    exact h1.add h2
  have hinj : Function.Injective (straightenLin (deriv G 0)) := straightenLin_injective hder
  have hker : (straightenLin (deriv G 0)).toLinearMap.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hsurj : Function.Surjective (straightenLin (deriv G 0)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := ℝ) (V := ℝ × ℝ) (V₂ := ℝ × ℝ) rfl).mp hinj
  have hrange : (straightenLin (deriv G 0)).toLinearMap.range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  let e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearEquiv.ofBijective (straightenLin (deriv G 0)) hker hrange
  have hderiv' : HasFDerivAt (fun z : ℝ × ℝ => G z.1 + z.2 • rot90 (deriv G 0))
      ((e : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) 0 := hderiv
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  let Φ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    ContDiffAt.toOpenPartialHomeomorph (fun z : ℝ × ℝ => G z.1 + z.2 • rot90 (deriv G 0))
      hdiff.contDiffAt hderiv' hn
  have hΦcoe : ⇑Φ = (fun z : ℝ × ℝ => G z.1 + z.2 • rot90 (deriv G 0)) :=
    ContDiffAt.toOpenPartialHomeomorph_coe _ _ _
  have h0mem : (0 : ℝ × ℝ) ∈ Φ.source := ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Φ.open_source.mem_nhds h0mem)
  exact ⟨r, Φ, hr, fun z hz => hball hz, fun z => by rw [hΦcoe]⟩

end Work.RPB.Port.Drive
