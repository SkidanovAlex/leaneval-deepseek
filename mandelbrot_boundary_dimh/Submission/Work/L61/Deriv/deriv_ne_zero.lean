import Mathlib
import Submission.Work.L61.Basic
import Submission.Work.L61.Deriv.E_deriv_ne_zero

/-!
# Lemma 6.1 (Shishikura §6): `deriv g ≠ 0` off the critical values of the horn map

`g = pushdown Ẽ_{f₀}` is the pushed-down horn map of §6, with domain
`gdom = {0} ∪ π(B^u ∪ B^ℓ)` and critical value `π v`.  The paper needs to know that `g` has
nonzero derivative at every point of its domain except the critical values of the *iterates* of
`g`; in particular at every point `ζ ∈ gdom` with `g ζ ≠ π v`.

The point is that `g` has a unique critical value in the cylinder: the covering computation
`ζ ↦ π(E(log ζ / 2πi))` gives, at `ζ = π w` with `w` a lift of `ζ`,

  `g'(ζ) = g(ζ) · Ẽ'(w) / ζ`,

so `g'(ζ) = 0 ↔ Ẽ'(w) = 0`; and `Ẽ` has zero derivative exactly at the lifts of `π v`
(`HornData.crit`).  The main lemma below, `hasDerivAt_pushdown`, computes this derivative; the
target lemma `deriv_ne_zero` combines it with the hypothesis `hE` (the contrapositive of
`HornData.crit`) and with `HornData.g_deriv`, which handles the point `0`.

Everything is proved from the `ParabData`/`HornData` interface fields alone.
-/

namespace Work.L61.Deriv

open MandelDim Set Function Metric Filter
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

/-! ## Elementary facts about `π(w) = exp(2πiw)` -/

/-- `π(a + b) = π a · π b`. -/
theorem piExp_mul (a b : ℂ) : piExp (a + b) = piExp a * piExp b := by
  rw [MandelDim.piExp, MandelDim.piExp, MandelDim.piExp, ← Complex.exp_add]
  congr 1
  ring

/-- `π` has derivative `2πi π` everywhere. -/
theorem hasDerivAt_piExp (u : ℂ) : HasDerivAt piExp (2 * ↑Real.pi * Complex.I * piExp u) u := by
  have hlin : HasDerivAt (fun t : ℂ => 2 * ↑Real.pi * Complex.I * t) (2 * ↑Real.pi * Complex.I) u := by
    simpa using (hasDerivAt_id u).const_mul (2 * ↑Real.pi * Complex.I)
  have h : HasDerivAt (fun t : ℂ => Complex.exp (2 * ↑Real.pi * Complex.I * t))
      (Complex.exp (2 * ↑Real.pi * Complex.I * u) * (2 * ↑Real.pi * Complex.I)) u :=
    (Complex.hasDerivAt_exp _).comp u hlin
  have hval : 2 * ↑Real.pi * Complex.I * piExp u =
      Complex.exp (2 * ↑Real.pi * Complex.I * u) * (2 * ↑Real.pi * Complex.I) := by
    rw [MandelDim.piExp]; ring
  rw [hval]
  exact h

/-- Unfolding of `pushdown` away from `0`. -/
theorem pushdown_of_ne' (E : ℂ → ℂ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    pushdown E ζ = piExp (E (Complex.log ζ / (2 * ↑Real.pi * Complex.I))) := by
  simp [MandelDim.pushdown, hζ]

/-- The local lift `γ ζ = w + log(ζ/π w)/(2πi)` differs from the principal lift by an integer. -/
theorem gamma_lift_sub_int (w ζ : ℂ) (hζ : ζ ≠ 0) :
    ∃ n : ℤ, w + Complex.log (ζ / piExp w) / (2 * ↑Real.pi * Complex.I) =
      Complex.log ζ / (2 * ↑Real.pi * Complex.I) + n := by
  have hwr : piExp w ≠ 0 := Work.L61.piExp_ne_zero w
  have h1 : piExp (w + Complex.log (ζ / piExp w) / (2 * ↑Real.pi * Complex.I)) = ζ := by
    rw [piExp_mul, Work.L61.piExp_log_div (ζ / piExp w) (div_ne_zero hζ hwr)]
    exact mul_div_cancel₀ ζ hwr
  refine Work.L61.piExp_eq_iff.mp ?_
  rw [h1, Work.L61.piExp_log_div ζ hζ]

/-! ## The lifted horn map is holomorphic on `DE = φ₀⁻¹(basin)` -/

theorem differentiableOn_E (d : ParabData f₀ D₀) : DifferentiableOn ℂ d.E d.DE := by
  intro w hw
  rw [Work.L61.mem_DE] at hw
  have hmap : MapsTo d.φ d.DE (ParabolicBasin f₀ D₀) :=
    fun x hx => (Work.L61.mem_DE (d := d)).mp hx |>.2
  have hφ : DifferentiableWithinAt ℂ d.φ d.DE w :=
    (d.φ_holo w hw.1).mono (fun x hx => (Work.L61.mem_DE (d := d)).mp hx |>.1)
  have hΦ : DifferentiableWithinAt ℂ d.Φ (ParabolicBasin f₀ D₀) (d.φ w) :=
    d.Φ_holo (d.φ w) hw.2
  exact hΦ.comp w hφ hmap

/-! ## The derivative of the pushed-down horn map

At a point `ζ = π w` the pushed-down map is `ζ ↦ π(Ẽ(γ ζ))` with `γ` the local lift, whence
`(pushdown E)'(π w) = π(E w) · E'(w) / π w`. -/

theorem hasDerivAt_pushdown {E : ℂ → ℂ} {DR : Set ℂ} (hDR : IsOpen DR)
    (heq : IsTEquivariantOn E DR) (hdiff : DifferentiableOn ℂ E DR) {w : ℂ} (hw : w ∈ DR) :
    HasDerivAt (pushdown E) (piExp (E w) * deriv E w / piExp w) (piExp w) := by
  have hEadd : ∀ v ∈ DR, v + 1 ∈ DR → E (v + 1) = E v + 1 := fun v hv _ => heq.2 v hv
  have hwne : piExp w ≠ 0 := Work.L61.piExp_ne_zero w
  -- the local lift `γ` of the identity, based at `π w`, with `γ (π w) = w`
  have hγc : w + Complex.log (piExp w / piExp w) / (2 * ↑Real.pi * Complex.I) = w := by
    simp [div_self hwne]
  have hγder : HasDerivAt (fun ζ : ℂ => w + Complex.log (ζ / piExp w) / (2 * ↑Real.pi * Complex.I))
      ((1 / piExp w) / (2 * ↑Real.pi * Complex.I)) (piExp w) := by
    have h1 : HasDerivAt (fun ζ : ℂ => ζ / piExp w) (1 / piExp w) (piExp w) := by
      simpa using (hasDerivAt_id (piExp w)).div_const (piExp w)
    have h2 : HasDerivAt (fun ζ : ℂ => Complex.log (ζ / piExp w))
        ((1 / piExp w) / (piExp w / piExp w)) (piExp w) :=
      h1.clog (by rw [div_self hwne]; exact Complex.one_mem_slitPlane)
    have h3 : HasDerivAt (fun ζ : ℂ => Complex.log (ζ / piExp w)) (1 / piExp w) (piExp w) := by
      simpa [div_self hwne] using h2
    have h4 : HasDerivAt (fun ζ : ℂ => Complex.log (ζ / piExp w) / (2 * ↑Real.pi * Complex.I))
        ((1 / piExp w) / (2 * ↑Real.pi * Complex.I)) (piExp w) := h3.div_const _
    exact h4.const_add w
  -- derivative of `E` at `w`, transported to the base point `γ (π w)`
  have hEder : HasDerivAt E (deriv E w) w := (hdiff.differentiableAt (hDR.mem_nhds hw)).hasDerivAt
  have hEder' : HasDerivAt E (deriv E w)
      (w + Complex.log (piExp w / piExp w) / (2 * ↑Real.pi * Complex.I)) := by
    rw [hγc]; exact hEder
  -- derivative of `π` at `E w`, transported to the base point `E (γ (π w))`
  have hpi' : HasDerivAt piExp (2 * ↑Real.pi * Complex.I * piExp (E w))
      (E (w + Complex.log (piExp w / piExp w) / (2 * ↑Real.pi * Complex.I))) := by
    rw [show E (w + Complex.log (piExp w / piExp w) / (2 * ↑Real.pi * Complex.I)) = E w by
      rw [hγc]]
    exact hasDerivAt_piExp (E w)
  -- chain rule: `pushdown E` agrees with `ζ ↦ π (E (γ ζ))` near `π w`
  have hF : HasDerivAt (fun ζ : ℂ =>
        piExp (E (w + Complex.log (ζ / piExp w) / (2 * ↑Real.pi * Complex.I))))
      (2 * ↑Real.pi * Complex.I * piExp (E w) *
        (deriv E w * ((1 / piExp w) / (2 * ↑Real.pi * Complex.I)))) (piExp w) := by
    have h1 : HasDerivAt (fun ζ : ℂ => E (w + Complex.log (ζ / piExp w) / (2 * ↑Real.pi * Complex.I)))
        (deriv E w * ((1 / piExp w) / (2 * ↑Real.pi * Complex.I))) (piExp w) := by
      have hc := hEder'.comp (piExp w) hγder
      simpa [Function.comp_def] using hc
    have h2 := hpi'.comp (piExp w) h1
    simpa [Function.comp_def] using h2
  have hconst : 2 * ↑Real.pi * Complex.I * piExp (E w) *
        (deriv E w * ((1 / piExp w) / (2 * ↑Real.pi * Complex.I)))
      = piExp (E w) * deriv E w / piExp w := by
    have h2pi : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    field_simp
  have hmain : HasDerivAt (fun ζ : ℂ =>
        piExp (E (w + Complex.log (ζ / piExp w) / (2 * ↑Real.pi * Complex.I))))
      (piExp (E w) * deriv E w / piExp w) (piExp w) := by
    rw [hconst] at hF
    exact hF
  refine HasDerivAt.congr_of_eventuallyEq hmain ?_
  -- eventual equality: near `π w` the principal lift of `ζ` lies in `DR`, so it differs from `γ ζ`
  -- by an integer and `π ∘ E` is insensitive to that
  have hγc_mem : w + Complex.log (piExp w / piExp w) / (2 * ↑Real.pi * Complex.I) ∈ DR := by
    rw [hγc]; exact hw
  have hev1 : ∀ᶠ ζ in 𝓝 (piExp w),
      w + Complex.log (ζ / piExp w) / (2 * ↑Real.pi * Complex.I) ∈ DR :=
    hγder.continuousAt.eventually (hDR.mem_nhds hγc_mem)
  have hev2 : ∀ᶠ ζ in 𝓝 (piExp w), ζ ≠ 0 := eventually_ne_nhds hwne
  filter_upwards [hev1, hev2] with ζ hγmem hζne
  obtain ⟨n, hn⟩ := gamma_lift_sub_int w ζ hζne
  have hγeq : w + Complex.log (ζ / piExp w) / (2 * ↑Real.pi * Complex.I) =
      Complex.log ζ / (2 * ↑Real.pi * Complex.I) + n := hn
  have hLmem : Complex.log ζ / (2 * ↑Real.pi * Complex.I) ∈ DR := by
    have h1 := Work.L61.IsTInvariant.add_int heq.1 hγmem (-n)
    simpa [hγeq] using h1
  have hEshift : E (w + Complex.log (ζ / piExp w) / (2 * ↑Real.pi * Complex.I)) =
      E (Complex.log ζ / (2 * ↑Real.pi * Complex.I)) + n := by
    rw [hγeq, Work.L61.E_add_int heq.1 hEadd hLmem n]
  rw [pushdown_of_ne' E hζne, hEshift, Work.L61.piExp_add_intCast]

/-! ## The target lemma -/

theorem deriv_ne_zero {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀} (hd : MandelDim.HornData d)
    (hE : ∀ w : ℂ, w ∈ hd.Bu ∪ hd.Bl → (∀ k : ℤ, d.E w ≠ hd.v + k) → deriv d.E w ≠ 0)
    {ζ : ℂ} (hζ : ζ ∈ Work.L61.gdom d hd) (h : Work.L61.g d ζ ≠ Work.L61.critVal hd) :
    deriv (Work.L61.g d) ζ ≠ 0 := by
  rw [Work.L61.gdom, Set.mem_insert_iff] at hζ
  rcases hζ with h0 | hπ
  · -- the point `0`: `HornData.g_deriv` gives `g'(0) = 1`
    subst h0
    have h1 : deriv (Work.L61.g d) 0 = deriv (pushdown d.E) 0 := rfl
    rw [h1, hd.g_deriv]
    exact one_ne_zero
  · -- a point `π w`, `w ∈ B^u ∪ B^ℓ`
    obtain ⟨w, hw, rfl⟩ := hπ
    have hgw : Work.L61.g d (piExp w) = piExp (d.E w) := Work.L61.g_piExp d hd hw
    have hEw : ∀ k : ℤ, d.E w ≠ hd.v + k := by
      intro k hk
      refine h ?_
      rw [hgw, hk, Work.L61.piExp_add_intCast]
      rfl
    have hderE : deriv d.E w ≠ 0 := hE w hw hEw
    have hT : IsTInvariant (hd.Bu ∪ hd.Bl) := fun v => by
      simp only [Set.mem_union, hd.Bu_T v, hd.Bl_T v]
    have heq : IsTEquivariantOn d.E (hd.Bu ∪ hd.Bl) :=
      ⟨hT, fun v hv => Work.L61.E_add_one d (hd.sub hv) (hd.sub ((hT v).mp hv))⟩
    have hdiffE : DifferentiableOn ℂ d.E (hd.Bu ∪ hd.Bl) := (differentiableOn_E d).mono hd.sub
    have hHd := hasDerivAt_pushdown (E := d.E) (DR := hd.Bu ∪ hd.Bl)
      (hd.Bu_open.union hd.Bl_open) heq hdiffE hw
    have hval : deriv (Work.L61.g d) (piExp w) = piExp (d.E w) * deriv d.E w / piExp w :=
      hHd.deriv
    rw [hval]
    exact div_ne_zero (mul_ne_zero (Work.L61.piExp_ne_zero (d.E w)) hderE)
      (Work.L61.piExp_ne_zero w)

end

end Work.L61.Deriv
