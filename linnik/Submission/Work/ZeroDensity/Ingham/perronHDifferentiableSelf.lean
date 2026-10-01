import Mathlib
import Submission.Work.ZeroDensity.Ingham.zetaPerronDefs

/-!
# Holomorphy of the patched Perron integrand `perronH`

`perronH K Y ρ = dslope (perronM K Y ρ) (1-ρ)`, where
`perronM K Y ρ w = Γ(w+1)·dslope (ζ₁(ρ+·)) 0 w·Y^w·M_K(ρ+w)`.

Each factor of `perronM` is complex differentiable on the open half-plane `{w | -1 < w.re}`:
`Γ(w+1)` has its poles at `w = -1,-2,…`; the divided difference of the entire function `ζ₁(ρ+·)`
with base point `0` is entire; `Y^w` is entire because `Y ≠ 0`; and `M_K(ρ+·)` is a finite sum of
`μ(n)·n^{-(ρ+w)}`, hence entire.  Since the open half-plane is contained in `{Re > -1}` and
contains the base point `1-ρ` (`Re(1-ρ) = 1 - Re ρ > -1`), the difference quotient is then
differentiable on every rectangle `[p,q] × [-R,R]` with `p, q > -1`.
-/

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators

/-- If `f` is complex differentiable on an open set `V` containing `c`, then the difference
quotient `dslope f c` (which equals `deriv f c` at `c`) is complex differentiable on any subset
of `V`. -/
lemma differentiableOn_dslope_of_isOpen_mem {f : ℂ → ℂ} {V s : Set ℂ} {c : ℂ}
    (hV : IsOpen V) (hsub : s ⊆ V) (hc : c ∈ V) (hf : DifferentiableOn ℂ f V) :
    DifferentiableOn ℂ (dslope f c) s := by
  have hds : DifferentiableOn ℂ (dslope f c) V :=
    (Complex.differentiableOn_dslope (f := f) (c := c) (s := V) (hV.mem_nhds hc)).mpr hf
  intro p hp
  by_cases hpc : p = c
  · rw [hpc]
    exact (hds.differentiableAt (hV.mem_nhds hc)).differentiableWithinAt
  · exact (differentiableWithinAt_dslope_of_ne (f := f) (a := c) (s := s) hpc).mpr
      ((hf.mono hsub) p hp)

/-- `perronM K Y ρ` is complex differentiable on the open half-plane `{w | -1 < w.re}`. -/
lemma differentiableOn_perronM (K : ℕ) (Y : ℝ) (hY : 0 < Y) (ρ : ℂ) :
    DifferentiableOn ℂ (perronM K Y ρ) {w : ℂ | -1 < w.re} := by
  intro w hw
  have hw' : (-1 : ℝ) < w.re := hw
  have hG : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + 1)) w := by
    refine (Complex.differentiableAt_Gamma (w + 1) ?_).comp w (differentiableAt_id.add_const 1)
    intro m hm
    have hre : (w + 1).re = -(m : ℝ) := by rw [hm]; simp
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [Complex.add_re, Complex.one_re] at hre
    linarith
  have hD : DifferentiableAt ℂ
      (fun z : ℂ => dslope (fun t : ℂ => riemannZeta₁ (ρ + t)) 0 z) w := by
    have hz1 : Differentiable ℂ (fun t : ℂ => riemannZeta₁ (ρ + t)) :=
      differentiable_riemannZeta₁.comp
        ((differentiable_const (c := ρ)).add differentiable_id)
    have hds := (Complex.differentiableOn_dslope
      (f := fun t : ℂ => riemannZeta₁ (ρ + t)) (c := 0) (s := Set.univ)
      Filter.univ_mem).mpr hz1.differentiableOn
    exact hds.differentiableAt Filter.univ_mem
  have hYc : DifferentiableAt ℂ (fun z : ℂ => (Y : ℂ) ^ z) w :=
    differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hY.ne'))
  have hMK : DifferentiableAt ℂ (fun z : ℂ => MK K (ρ + z)) w := by
    have hMKa : Differentiable ℂ (MK K) := by
      rw [show MK K = (fun s : ℂ => ∑ n ∈ Finset.Icc 1 K,
        (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)) from funext (MK_apply K)]
      apply Differentiable.fun_sum
      intro n hn
      have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by
        have := (Finset.mem_Icc.mp hn).1
        omega)
      have h1 : Differentiable ℂ (fun s : ℂ => (n : ℂ) ^ (-s)) :=
        (differentiable_id.neg).const_cpow (Or.inl hn0)
      exact (differentiable_const (c := (ArithmeticFunction.moebius n : ℂ))).mul h1
    exact hMKa.differentiableAt.comp w ((differentiableAt_const ρ).add differentiableAt_id)
  have hperM : DifferentiableAt ℂ (perronM K Y ρ) w := by
    change DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + 1)
      * dslope (fun t : ℂ => riemannZeta₁ (ρ + t)) 0 z * (Y : ℂ) ^ z * MK K (ρ + z)) w
    exact ((hG.mul hD).mul hYc).mul hMK
  exact hperM.differentiableWithinAt

theorem perronHDifferentiableSelf (K : ℕ) (Y : ℝ) (hY : 0 < Y) (ρ : ℂ) {p q R : ℝ}
    (hp : -1 < p) (hq : -1 < q) (hρ : ρ.re < 2) :
    DifferentiableOn ℂ (Work.ZeroDensity.Ingham.perronH K Y ρ)
      (Set.uIcc p q ×ℂ Set.uIcc (-R) R) := by
  have hVopen : IsOpen {w : ℂ | -1 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hsub : (Set.uIcc p q ×ℂ Set.uIcc (-R) R) ⊆ {w : ℂ | -1 < w.re} := by
    intro w hw
    obtain ⟨hre, -⟩ := Complex.mem_reProdIm.mp hw
    exact (Set.ordConnected_Ioi (a := (-1 : ℝ))).uIcc_subset hp hq hre
  have hcV : (1 - ρ) ∈ {w : ℂ | -1 < w.re} := by
    show (-1 : ℝ) < (1 - ρ).re
    rw [Complex.sub_re, Complex.one_re]
    linarith
  exact differentiableOn_dslope_of_isOpen_mem hVopen hsub hcV
    (differentiableOn_perronM K Y hY ρ)

end Work.ZeroDensity.Ingham
