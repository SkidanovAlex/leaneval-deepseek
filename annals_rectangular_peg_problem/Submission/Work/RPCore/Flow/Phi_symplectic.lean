import Mathlib
import Submission.Work.RPCore.Flow.HamFlow
import Submission.Work.RPCore.Flow.flow_variational_eq
import Submission.Work.RPCore.Flow.symp_hamVF_fderiv
import Submission.Work.RPCore.Flow.clampHam_contDiff
import Submission.Work.RPCore.Flow.clampedField_fderiv_inr_snd
import Submission.Work.RPCore.Flow.isIntegralCurve_neg_clampFlow

/-!
# `Phi_symplectic`: the two-time Hamiltonian flow preserves `ω` (`Work.RPCore.Flow.Phi_symplectic`)

For a compactly supported, `2π`-periodic Hamiltonian `Hh` and `a, b ∈ [-1,2]`, the time-`b` map
`Phi Hh a b` of the (clamped) Hamiltonian flow preserves the symplectic form `ω = symp`.

## Strategy

The clamped flow is the flow of the autonomous field `V = clampedField Hh = (1, X)` on `ℝ × PS`,
for which the *variational equation* is available (`flow_variational_eq`): for small positive times
the derivative `M t = fderiv ℝ (clampFlow Hh t) z₀` of the flow in the initial condition exists and
solves `M'(t) = DV(Φ_t z₀) ∘ M(t)`, `M 0 = 1`.  Writing `D t = (M t (0, δ))₂` for the "spatial"
block of `M t`, the structure of `V` gives

* `(M t v).1 = v.1` (the first coordinate of the flow is affine), hence `M t (0, δ) = (0, D t δ)`;
* `(DV(z) w).1 = 0` and `(DV(z)(0, δ))₂ = fderiv ℝ (hamVF (clampHam Hh z.1)) z.2 δ`,

so the ODE for `D` reads `D'(t) = G_t ∘ D t` with
`G_t = fderiv ℝ (hamVF (clampHam Hh z.1)) z.2` at `z = Φ_t z₀`.  Since `G_t` is *skew* for `ω`
(`symp_hamVF_fderiv`, using that each slice `clampHam Hh t` is `C²`), the function
`t ↦ ω(D t u, D t w)` has vanishing derivative and is therefore constant, equal to `ω(u, w)` at
`t = 0` (where `D 0 = 1`).

All of this is packaged in the abstract lemma `flow_snd_symplectic_local`, which we apply twice:
once to `V = clampedField Hh` (positive times) and once to `-V` (negative times, via the
time-reversed flow `t ↦ clampFlow Hh (-t)`).  Chaining finitely many small steps gives the result
for arbitrary `a, b`.
-/

open RectangularPegProblem Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPCore.Flow

open Work.RPV

/-! ## Elementary symplectic algebra -/

/-- `symp` is a bilinear form, so it satisfies the product rule: differentiating
`symp (u y) (v y)` gives `symp u' (v x) + symp (u x) v'`. -/
theorem hasDerivAt_symp_rpv {u v : ℝ → PS} {u' v' : PS} {x : ℝ}
    (hu : HasDerivAt u u' x) (hv : HasDerivAt v v' x) :
    HasDerivAt (fun y => symp (u y) (v y)) (symp u' (v x) + symp (u x) v') x := by
  have h11u : HasDerivAt (fun y => (u y).1.1) u'.1.1 x := (hu.fst).fst
  have h12u : HasDerivAt (fun y => (u y).1.2) u'.1.2 x := (hu.fst).snd
  have h21u : HasDerivAt (fun y => (u y).2.1) u'.2.1 x := (hu.snd).fst
  have h22u : HasDerivAt (fun y => (u y).2.2) u'.2.2 x := (hu.snd).snd
  have h11v : HasDerivAt (fun y => (v y).1.1) v'.1.1 x := (hv.fst).fst
  have h12v : HasDerivAt (fun y => (v y).1.2) v'.1.2 x := (hv.fst).snd
  have h21v : HasDerivAt (fun y => (v y).2.1) v'.2.1 x := (hv.snd).fst
  have h22v : HasDerivAt (fun y => (v y).2.2) v'.2.2 x := (hv.snd).snd
  have hA := h21u.mul h11v
  have hB := h22u.mul h12v
  have hC := h11u.mul h21v
  have hD := h12u.mul h22v
  have h := ((hA.add hB).sub hC).sub hD
  simp only [symp]
  convert h using 1
  ring

theorem symp_neg_left (a b : PS) : symp (-a) b = - symp a b := by
  simp only [symp, Prod.fst_neg, Prod.snd_neg]; ring

theorem symp_neg_right (a b : PS) : symp a (-b) = - symp a b := by
  simp only [symp, Prod.fst_neg, Prod.snd_neg]; ring

/-! ## Closure properties of `IsSymplectic` -/

/-- A map whose differential preserves `ω` is differentiable: if it were not, `fderiv` would be
`0` and the defining identity would fail on the pair `(e_{p₁}, e_{q₁})`. -/
theorem isSymplectic_differentiableAt {ψ : PS → PS} (h : Work.RPCore.IsSymplectic ψ) (x : PS) :
    DifferentiableAt ℝ ψ x := by
  by_contra hx
  have h0 : fderiv ℝ ψ x = 0 := fderiv_zero_of_not_differentiableAt hx
  have h1 := h x ((0, 0), (1, 0)) ((1, 0), (0, 0))
  rw [h0] at h1
  simp only [zero_apply, symp] at h1
  norm_num at h1

theorem isSymplectic_comp {ψ₁ ψ₀ : PS → PS} (h₁ : Work.RPCore.IsSymplectic ψ₁)
    (h₀ : Work.RPCore.IsSymplectic ψ₀) : Work.RPCore.IsSymplectic (ψ₁ ∘ ψ₀) := by
  intro x u w
  have d₀ : DifferentiableAt ℝ ψ₀ x := isSymplectic_differentiableAt h₀ x
  have d₁ : DifferentiableAt ℝ ψ₁ (ψ₀ x) := isSymplectic_differentiableAt h₁ (ψ₀ x)
  rw [fderiv_comp x d₁ d₀]
  exact (h₁ (ψ₀ x) (fderiv ℝ ψ₀ x u) (fderiv ℝ ψ₀ x w)).trans (h₀ x u w)

theorem isSymplectic_id : Work.RPCore.IsSymplectic (id : PS → PS) := by
  intro x u w
  simp

/-! ## The `t`-slice form of `Phi` -/

theorem Phi_eq_slice (Hh : CptPerHam) (a t : ℝ) :
    Work.RPCore.Phi Hh a (a + t) = fun y : PS => (Work.RPCore.clampFlow Hh t (a, y)).2 := by
  funext y
  simp only [Work.RPCore.Phi]
  rw [show a + t - a = t by ring]

theorem Phi_eq_slice_neg (Hh : CptPerHam) (a t : ℝ) :
    Work.RPCore.Phi Hh a (a - t) = fun y : PS => (Work.RPCore.clampFlow Hh (-t) (a, y)).2 := by
  funext y
  simp only [Work.RPCore.Phi]
  rw [show a - t - a = -t by ring]

/-! ## The abstract local argument -/

/-- If `Φ` is the flow of a `C¹` field `Y` on `ℝ × PS` whose first component is constant along
the flow (`(Φ t y).1 = y.1 + c t`) and whose vertical derivative is `G`, skew for `ω`, then the
"spatial part" `x ↦ (Φ t (a, x)).2` of the flow preserves `ω` for small positive `t`. -/
theorem flow_snd_symplectic_local
    (Y : ℝ × PS → ℝ × PS) (hY : ContDiff ℝ 1 Y)
    (K : ℝ) (hK : ∀ z, ‖fderiv ℝ Y z‖ ≤ K)
    (Φ : ℝ → (ℝ × PS) → (ℝ × PS))
    (hΦ : ∀ t y, ∃ γ : ℝ → ℝ × PS, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => Y z) ∧ γ t = Φ t y)
    (G : ℝ × PS → PS →L[ℝ] PS)
    (c : ℝ) (hΦfst : ∀ t y, (Φ t y).1 = y.1 + c * t)
    (hYder : ∀ z, (ContinuousLinearMap.snd ℝ ℝ PS) ∘L fderiv ℝ Y z ∘L
        (ContinuousLinearMap.inr ℝ ℝ PS) = G z)
    (hskew : ∀ z u w, symp (G z u) w + symp u (G z w) = 0) :
    ∃ δ > 0, ∀ t ∈ Set.Icc 0 δ, ∀ a : ℝ,
      Work.RPCore.IsSymplectic (fun y : PS => (Φ t (a, y)).2) := by
  classical
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ Y 0)).trans (hK 0)
  set δ : ℝ := 1 / (2 * (K + 1)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδK : δ * K < 1 := by
    rw [hδdef, div_mul_eq_mul_div, div_lt_one (by positivity)]
    linarith
  refine ⟨δ, hδpos, ?_⟩
  intro t ht a x u w
  obtain ⟨M, hM0, hMder, hMF, -⟩ := flow_variational_eq Y hY K hK Φ hΦ hδpos hδK (a, x)
  have hDfd : fderiv ℝ (fun y : PS => (Φ t (a, y)).2) x
      = (ContinuousLinearMap.snd ℝ ℝ PS) ∘L M t ∘L (ContinuousLinearMap.inr ℝ ℝ PS) := by
    have h1 : HasFDerivAt (fun y : PS => Φ t (a, y))
        (M t ∘L (ContinuousLinearMap.inr ℝ ℝ PS)) x :=
      (hMF t ht).comp x (hasFDerivAt_prodMk_right a x)
    exact h1.snd.fderiv
  have hMfst : ∀ s ∈ Set.Icc 0 δ, ∀ v : ℝ × PS, (M s v).1 = v.1 := by
    intro s hs v
    have h1 : HasFDerivAt (fun y : ℝ × PS => (Φ s y).1)
        ((ContinuousLinearMap.fst ℝ ℝ PS) ∘L M s) (a, x) := (hMF s hs).fst
    have h2fun : (fun y : ℝ × PS => (Φ s y).1) = (fun y : ℝ × PS => y.1 + c * s) := by
      funext y; exact hΦfst s y
    rw [h2fun] at h1
    have h3 : HasFDerivAt (fun y : ℝ × PS => y.1 + c * s)
        (ContinuousLinearMap.fst ℝ ℝ PS) (a, x) :=
      ((ContinuousLinearMap.fst ℝ ℝ PS).hasFDerivAt).add_const (c * s)
    have heq : (ContinuousLinearMap.fst ℝ ℝ PS) ∘L M s = ContinuousLinearMap.fst ℝ ℝ PS :=
      h1.unique h3
    have := congrArg (fun (L : ℝ × PS →L[ℝ] ℝ) => L v) heq
    simpa [ContinuousLinearMap.comp_apply] using this
  set f : ℝ → ℝ := fun s => symp ((M s (ContinuousLinearMap.inr ℝ ℝ PS u)).2)
      ((M s (ContinuousLinearMap.inr ℝ ℝ PS w)).2) with hfdef
  have hf : ∀ s ∈ Set.Icc 0 δ, HasDerivAt f 0 s := by
    intro s hs
    have hMs : HasDerivAt M (fderiv ℝ Y (Φ s (a, x)) ∘L M s) s := hMder s hs
    have hpu : HasDerivAt (fun r : ℝ => M r (ContinuousLinearMap.inr ℝ ℝ PS u))
        (fderiv ℝ Y (Φ s (a, x)) (M s (ContinuousLinearMap.inr ℝ ℝ PS u))) s := by
      have h := hMs.clm_apply (hasDerivAt_const (x := s) (ContinuousLinearMap.inr ℝ ℝ PS u))
      simpa [ContinuousLinearMap.comp_apply] using h
    have hpw : HasDerivAt (fun r : ℝ => M r (ContinuousLinearMap.inr ℝ ℝ PS w))
        (fderiv ℝ Y (Φ s (a, x)) (M s (ContinuousLinearMap.inr ℝ ℝ PS w))) s := by
      have h := hMs.clm_apply (hasDerivAt_const (x := s) (ContinuousLinearMap.inr ℝ ℝ PS w))
      simpa [ContinuousLinearMap.comp_apply] using h
    have hpu2 : HasDerivAt (fun r : ℝ => (M r (ContinuousLinearMap.inr ℝ ℝ PS u)).2)
        ((fderiv ℝ Y (Φ s (a, x)) (M s (ContinuousLinearMap.inr ℝ ℝ PS u))).2) s := hpu.snd
    have hpw2 : HasDerivAt (fun r : ℝ => (M r (ContinuousLinearMap.inr ℝ ℝ PS w)).2)
        ((fderiv ℝ Y (Φ s (a, x)) (M s (ContinuousLinearMap.inr ℝ ℝ PS w))).2) s := hpw.snd
    have hsw := hasDerivAt_symp_rpv hpu2 hpw2
    have hMu1 : (M s (ContinuousLinearMap.inr ℝ ℝ PS u)).1 = 0 :=
      (hMfst s hs (ContinuousLinearMap.inr ℝ ℝ PS u)).trans rfl
    have hMu_eq : M s (ContinuousLinearMap.inr ℝ ℝ PS u)
        = ContinuousLinearMap.inr ℝ ℝ PS ((M s (ContinuousLinearMap.inr ℝ ℝ PS u)).2) :=
      Prod.ext (by rw [hMu1]; rfl) rfl
    have hMw1 : (M s (ContinuousLinearMap.inr ℝ ℝ PS w)).1 = 0 :=
      (hMfst s hs (ContinuousLinearMap.inr ℝ ℝ PS w)).trans rfl
    have hMw_eq : M s (ContinuousLinearMap.inr ℝ ℝ PS w)
        = ContinuousLinearMap.inr ℝ ℝ PS ((M s (ContinuousLinearMap.inr ℝ ℝ PS w)).2) :=
      Prod.ext (by rw [hMw1]; rfl) rfl
    have hA1 : (fderiv ℝ Y (Φ s (a, x)) (M s (ContinuousLinearMap.inr ℝ ℝ PS u))).2
        = G (Φ s (a, x)) ((M s (ContinuousLinearMap.inr ℝ ℝ PS u)).2) := by
      have hthis := congrArg (fun (L : PS →L[ℝ] PS) =>
        L ((M s (ContinuousLinearMap.inr ℝ ℝ PS u)).2)) (hYder (Φ s (a, x)))
      simp only [ContinuousLinearMap.comp_apply] at hthis
      rw [← hMu_eq] at hthis
      exact hthis
    have hA2 : (fderiv ℝ Y (Φ s (a, x)) (M s (ContinuousLinearMap.inr ℝ ℝ PS w))).2
        = G (Φ s (a, x)) ((M s (ContinuousLinearMap.inr ℝ ℝ PS w)).2) := by
      have hthis := congrArg (fun (L : PS →L[ℝ] PS) =>
        L ((M s (ContinuousLinearMap.inr ℝ ℝ PS w)).2)) (hYder (Φ s (a, x)))
      simp only [ContinuousLinearMap.comp_apply] at hthis
      rw [← hMw_eq] at hthis
      exact hthis
    have hzero : symp (fderiv ℝ Y (Φ s (a, x))
            (M s (ContinuousLinearMap.inr ℝ ℝ PS u))).2
          ((M s (ContinuousLinearMap.inr ℝ ℝ PS w)).2)
        + symp ((M s (ContinuousLinearMap.inr ℝ ℝ PS u)).2)
          (fderiv ℝ Y (Φ s (a, x)) (M s (ContinuousLinearMap.inr ℝ ℝ PS w))).2 = 0 := by
      rw [hA1, hA2]
      exact hskew (Φ s (a, x)) _ _
    rw [hzero] at hsw
    simpa [hfdef] using hsw
  have hft : f t = f 0 := by
    have hbound := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := f) (s := Set.Icc (0:ℝ) δ) (x := 0) (y := t) (C := 0)
      (fun r hr => (hf r hr).differentiableAt)
      (fun r hr => by rw [(hf r hr).deriv]; simp)
      (convex_Icc 0 δ) (Set.left_mem_Icc.mpr hδpos.le) ht
    have h0 : ‖f t - f 0‖ ≤ 0 := by simpa using hbound
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h0 (norm_nonneg _)))
  have hf0 : f 0 = symp u w := by
    simp [hfdef, hM0]
  have hft' : f t = symp ((M t (ContinuousLinearMap.inr ℝ ℝ PS u)).2)
      ((M t (ContinuousLinearMap.inr ℝ ℝ PS w)).2) := rfl
  rw [hDfd]
  change symp ((M t (ContinuousLinearMap.inr ℝ ℝ PS u)).2)
      ((M t (ContinuousLinearMap.inr ℝ ℝ PS w)).2) = symp u w
  rw [← hft', hft, hf0]

/-! ## The two instantiations: positive and negative times -/

/-- Positive times: `Phi Hh a (a + t)` preserves `ω` for small `t ≥ 0`. -/
theorem Phi_symplectic_forward_local (Hh : CptPerHam) :
    ∃ δ > 0, ∀ t ∈ Set.Icc 0 δ, ∀ a : ℝ,
      Work.RPCore.IsSymplectic (Work.RPCore.Phi Hh a (a + t)) := by
  obtain ⟨δ, hδ, hloc⟩ := flow_snd_symplectic_local
    (Work.RPCore.clampedField Hh) ((Work.RPCore.clampedField_contDiff_three Hh).of_le (by norm_num))
    (Work.RPCore.clampedData Hh).K (Work.RPCore.clampedData Hh).hK
    (Work.RPCore.clampFlow Hh)
    (fun t y => ⟨fun s => Work.RPCore.clampFlow Hh s y, Work.RPCore.clampFlow_zero Hh y,
      Work.RPCore.clampFlow_curve Hh y, rfl⟩)
    (fun z => fderiv ℝ (hamVF (Work.RPCore.clampHam Hh z.1)) z.2) 1
    (fun t y => by rw [Work.RPCore.clampFlow_fst]; ring)
    (fun z => ContinuousLinearMap.ext (clampedField_fderiv_inr_snd Hh z))
    (fun z u w => symp_hamVF_fderiv (Work.RPCore.clampHam Hh z.1)
      (clampHam_contDiff Hh z.1) z.2 u w)
  refine ⟨δ, hδ, ?_⟩
  intro t ht a
  have h := hloc t ht a
  rw [← Phi_eq_slice Hh a t] at h
  exact h

/-- Negative times: `Phi Hh a (a - t)` preserves `ω` for small `t ≥ 0`. -/
theorem Phi_symplectic_backward_local (Hh : CptPerHam) :
    ∃ δ > 0, ∀ t ∈ Set.Icc 0 δ, ∀ a : ℝ,
      Work.RPCore.IsSymplectic (Work.RPCore.Phi Hh a (a - t)) := by
  obtain ⟨δ, hδ, hloc⟩ := flow_snd_symplectic_local
    (fun z : ℝ × PS => -Work.RPCore.clampedField Hh z)
    (((Work.RPCore.clampedField_contDiff_three Hh).of_le (by norm_num)).neg)
    (Work.RPCore.clampedData Hh).K
    (fun z => by
      rw [show (fun z : ℝ × PS => -Work.RPCore.clampedField Hh z)
            = -Work.RPCore.clampedField Hh from rfl, fderiv_neg, norm_neg]
      exact (Work.RPCore.clampedData Hh).hK z)
    (fun t z => Work.RPCore.clampFlow Hh (-t) z)
    (fun t y => ⟨fun s => Work.RPCore.clampFlow Hh (-s) y,
      by show Work.RPCore.clampFlow Hh (-(0:ℝ)) y = y
         rw [neg_zero, Work.RPCore.clampFlow_zero],
      isIntegralCurve_neg_clampFlow Hh y, rfl⟩)
    (fun z => -fderiv ℝ (hamVF (Work.RPCore.clampHam Hh z.1)) z.2) (-1)
    (fun t y => by rw [Work.RPCore.clampFlow_fst]; ring)
    (fun z => ContinuousLinearMap.ext (fun δ => by
      show (fderiv ℝ (fun z : ℝ × PS => -Work.RPCore.clampedField Hh z) z
            ((ContinuousLinearMap.inr ℝ ℝ PS) δ)).2
          = (-(fderiv ℝ (hamVF (Work.RPCore.clampHam Hh z.1)) z.2)) δ
      rw [show (fun z : ℝ × PS => -Work.RPCore.clampedField Hh z)
            = -Work.RPCore.clampedField Hh from rfl, fderiv_neg, neg_apply, Prod.snd_neg,
        clampedField_fderiv_inr_snd Hh z δ]
      simp only [neg_apply]))
    (fun z u w => by
      have h := symp_hamVF_fderiv (Work.RPCore.clampHam Hh z.1) (clampHam_contDiff Hh z.1) z.2 u w
      show symp ((-(fderiv ℝ (hamVF (Work.RPCore.clampHam Hh z.1)) z.2)) u) w
        + symp u ((-(fderiv ℝ (hamVF (Work.RPCore.clampHam Hh z.1)) z.2)) w) = 0
      rw [neg_apply, neg_apply, symp_neg_left, symp_neg_right]
      linarith)
  refine ⟨δ, hδ, ?_⟩
  intro t ht a
  have h := hloc t ht a
  rw [← Phi_eq_slice_neg Hh a t] at h
  exact h

/-! ## Chaining and the final theorem -/

/-- The set of symplectic time parameters is "additively complete": from a local step of size
`≤ δ` in either direction, every two-time flow `Phi Hh a b` is symplectic. -/
theorem Phi_symplectic_chain (Hh : CptPerHam) (δ : ℝ) (hδ : 0 < δ)
    (hloc : ∀ s, |s| ≤ δ → ∀ a : ℝ, Work.RPCore.IsSymplectic (Work.RPCore.Phi Hh a (a + s))) :
    ∀ a b : ℝ, Work.RPCore.IsSymplectic (Work.RPCore.Phi Hh a b) := by
  intro a b
  obtain ⟨N, hN1, hNabs⟩ : ∃ N : ℕ, 1 ≤ N ∧ |b - a| ≤ (N:ℝ) * δ := by
    obtain ⟨n, hn⟩ := exists_nat_gt (|b - a| / δ)
    refine ⟨max 1 n, le_max_left 1 n, ?_⟩
    have hlt : |b - a| / δ < ((max 1 n : ℕ) : ℝ) :=
      lt_of_lt_of_le hn (by exact_mod_cast le_max_right 1 n)
    rw [div_lt_iff₀ hδ] at hlt
    exact le_of_lt hlt
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  set σ : ℝ := (b - a) / N with hσdef
  have hσabs : |σ| ≤ δ := by
    rw [hσdef, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    linarith [hNabs]
  have hmain : ∀ k : ℕ, k ≤ N → Work.RPCore.IsSymplectic (Work.RPCore.Phi Hh a (a + (k:ℝ) * σ)) := by
    intro k
    induction k with
    | zero =>
        intro _
        have hid : Work.RPCore.Phi Hh a (a + ((0:ℕ):ℝ) * σ) = id := by
          funext x
          simpa using Work.RPCore.Phi_self Hh a x
        rw [hid]; exact isSymplectic_id
    | succ k ih =>
        intro hk
        have hkN : k < N := Nat.lt_of_succ_le hk
        have h1 : Work.RPCore.IsSymplectic (Work.RPCore.Phi Hh a (a + (k:ℝ) * σ)) :=
          ih (Nat.le_of_lt hkN)
        have h2 : Work.RPCore.IsSymplectic
            (Work.RPCore.Phi Hh (a + (k:ℝ) * σ) (a + (k:ℝ) * σ + σ)) :=
          hloc σ hσabs _
        have hcomp := isSymplectic_comp h2 h1
        have heq : (Work.RPCore.Phi Hh (a + (k:ℝ) * σ) (a + (k:ℝ) * σ + σ))
              ∘ (Work.RPCore.Phi Hh a (a + (k:ℝ) * σ))
            = Work.RPCore.Phi Hh a (a + ((k:ℝ) + 1) * σ) := by
          funext x
          simp only [Function.comp_apply]
          rw [show a + (k:ℝ) * σ + σ = a + ((k:ℝ) + 1) * σ by ring]
          exact Work.RPCore.Phi_add Hh a (a + (k:ℝ) * σ) (a + ((k:ℝ) + 1) * σ) x
        rw [show a + ((k + 1 : ℕ) : ℝ) * σ = a + ((k:ℝ) + 1) * σ by push_cast; ring, ← heq]
        exact hcomp
  have hfinal := hmain N le_rfl
  have : a + (N:ℝ) * σ = b := by
    rw [hσdef, mul_div_cancel₀ (b - a) (ne_of_gt hNpos)]
    ring
  rwa [this] at hfinal

/-- **The two-time flow of a compactly supported periodic Hamiltonian preserves `ω`.**
(Stated with the hypotheses `a, b ∈ [-1,2]` under which `Phi Hh a b` is the genuine
time-dependent Hamiltonian flow of `Hh.H`; the proof actually works for all `a, b`.) -/
theorem Phi_symplectic (Hh : Work.RPV.CptPerHam) {a b : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 2)
    (hb : b ∈ Set.Icc (-1 : ℝ) 2) :
    Work.RPCore.IsSymplectic (Work.RPCore.Phi Hh a b) := by
  obtain ⟨δf, hδf, hlocf⟩ := Phi_symplectic_forward_local Hh
  obtain ⟨δb, hδb, hlocb⟩ := Phi_symplectic_backward_local Hh
  refine Phi_symplectic_chain Hh (min δf δb) (lt_min hδf hδb) ?_ a b
  intro s hs a'
  by_cases h : (0:ℝ) ≤ s
  · exact hlocf s ⟨h, (abs_of_nonneg h ▸ hs).trans (min_le_left _ _)⟩ a'
  · have hsneg : s < 0 := not_le.mp h
    have h2 : (0:ℝ) ≤ -s := by linarith
    have h3 : -s ≤ δb := by
      have hs' := hs
      rw [abs_of_neg hsneg] at hs'
      linarith [min_le_right δf δb]
    have hh := hlocb (-s) ⟨h2, h3⟩ a'
    rwa [show a' - -s = a' + s by ring] at hh

end Work.RPCore.Flow
