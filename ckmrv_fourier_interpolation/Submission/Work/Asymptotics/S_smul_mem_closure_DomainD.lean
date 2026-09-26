/-
# The closure of the `Γ(2)`-fundamental domain `𝒟` is invariant under `S : z ↦ -1/z`

CKMRV (proof of Prop. 3.2(1)) use that the propagation of a holomorphic function from the
`Γ(2)`-fundamental domain `𝒟` (their (3.12)) to `ℍ` can be organised along the `SL(2,ℤ)`-orbit
of `𝒟`.  The present file records the most elementary instance of that invariance: the Möbius
transformation `S = (0 -1; 1 0)`, acting by `z ↦ -1/z`, maps the closed region `closure 𝒟`
into itself, so that a bound (or any other property) valid on `𝒟̄` can be re-read on `S • 𝒟̄`.

The proof does *not* use the tiling of `𝒟` by translates of the standard fundamental domain;
it is a direct computation.  Writing `w = S • z = -1/z`, one has

* `Re w = -Re z / |z|²`, and both arcs `|z ∓ 1/2| > 1/2` occurring in the definition of `𝒟`
  give `|z|² > |Re z|` (more precisely `Im z² > Re z - Re z²` from `|z - 1/2| > 1/2` and
  `Im z² > -Re z - Re z²` from `|z + 1/2| > 1/2`), whence `|Re w| < 1`;
* `|w - 1/2| = |z + 2| / (2|z|) > 1/2`, since `|z + 2| > |z| ↔ Re z > -1`;
* `|w + 1/2| = |z - 2| / (2|z|) > 1/2`, since `|z - 2| > |z| ↔ Re z < 1`.

Since `z ↦ S • z` is continuous, the corresponding statement for the closure follows formally.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD

set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-- The Möbius map `S : z ↦ -1/z` preserves the `Γ(2)`-fundamental domain `𝒟`:  this is a
direct computation from the two "arc" conditions in the definition of `𝒟` (no use of the
tiling by translates of the standard fundamental domain is needed). -/
private theorem S_smul_mem_DomainD_of_mem {u : ℍ} (hu : u ∈ DomainD) : S • u ∈ DomainD := by
  rw [mem_DomainD] at hu ⊢
  obtain ⟨hx1, hx2, h3, h4⟩ := hu
  have hne : (u : ℂ) ≠ 0 := u.ne_zero
  have hNpos : 0 < Complex.normSq (u : ℂ) := Complex.normSq_pos.mpr hne
  -- coordinate formula `S • u = -1/u`
  have hcoe : ((S • u : ℍ) : ℂ) = -((u : ℂ))⁻¹ := by
    rw [modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  -- the real part of `-1/u`
  have hre : (S • u).re = -u.re / Complex.normSq (u : ℂ) := by
    rw [← UpperHalfPlane.coe_re, hcoe, Complex.neg_re, Complex.inv_re, UpperHalfPlane.coe_re]
    rw [← neg_div]
  -- the two quotients appearing in `|S • u ∓ 1/2|`
  have hsub : -(u : ℂ)⁻¹ - (1 / 2 : ℂ) = -((u : ℂ) + 2) / (2 * (u : ℂ)) := by
    field_simp; ring
  have hadd : -(u : ℂ)⁻¹ + (1 / 2 : ℂ) = ((u : ℂ) - 2) / (2 * (u : ℂ)) := by
    field_simp; ring
  -- the two arc conditions, read off `|u - 1/2| > 1/2` and `|u + 1/2| > 1/2`
  have harcR : u.re - u.re ^ 2 < u.im ^ 2 := by
    have h : (1 / 4 : ℝ) < Complex.normSq ((u : ℂ) - (1 / 2 : ℂ)) := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg ((u : ℂ) - (1 / 2 : ℂ))]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im] at h
    norm_num at h
    nlinarith
  have harcL : -u.re - u.re ^ 2 < u.im ^ 2 := by
    have h : (1 / 4 : ℝ) < Complex.normSq ((u : ℂ) + (1 / 2 : ℂ)) := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg ((u : ℂ) + (1 / 2 : ℂ))]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im] at h
    norm_num at h
    nlinarith
  have hNsq : Complex.normSq (u : ℂ) = u.re * u.re + u.im * u.im := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  -- `|Re u| < |u|²`, the form of the two arc conditions needed for `Re (-1/u)`
  have habs : |u.re| < Complex.normSq (u : ℂ) := by
    rw [hNsq]
    rcases le_or_gt 0 u.re with h | h
    · rw [abs_of_nonneg h]; nlinarith
    · rw [abs_of_neg h]; nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `-1 < Re (-1/u)`
    rw [hre, neg_div, neg_lt_neg_iff, div_lt_one hNpos]
    exact (abs_lt.mp habs).2
  · -- `Re (-1/u) < 1`
    rw [hre, neg_div, neg_lt, lt_div_iff₀ hNpos]
    linarith [(abs_lt.mp habs).1]
  · -- `1/2 < |(-1/u) - 1/2|`
    rw [hcoe, hsub, norm_div, norm_neg, norm_mul, Complex.norm_ofNat]
    rw [lt_div_iff₀ (by positivity)]
    have hkey : ‖(u : ℂ)‖ < ‖(u : ℂ) + 2‖ := by
      have hsq : ‖(u : ℂ)‖ ^ 2 < ‖(u : ℂ) + 2‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        rw [Complex.add_re, Complex.add_im, show ((2 : ℂ)).re = 2 from by norm_num,
          show ((2 : ℂ)).im = 0 from by norm_num, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        nlinarith [hx1]
      nlinarith [hsq, norm_nonneg (u : ℂ), norm_nonneg ((u : ℂ) + 2)]
    linarith [hkey]
  · -- `1/2 < |(-1/u) + 1/2|`
    rw [hcoe, hadd, norm_div, norm_mul, Complex.norm_ofNat]
    rw [lt_div_iff₀ (by positivity)]
    have hkey : ‖(u : ℂ)‖ < ‖(u : ℂ) - 2‖ := by
      have hsq : ‖(u : ℂ)‖ ^ 2 < ‖(u : ℂ) - 2‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        rw [Complex.sub_re, Complex.sub_im, show ((2 : ℂ)).re = 2 from by norm_num,
          show ((2 : ℂ)).im = 0 from by norm_num, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        nlinarith [hx2]
      nlinarith [hsq, norm_nonneg (u : ℂ), norm_nonneg ((u : ℂ) - 2)]
    linarith [hkey]

/-- **CKMRV (proof of Prop. 3.2(1))**: the Möbius transformation `S : z ↦ -1/z` maps the
closure of the `Γ(2)`-fundamental domain `𝒟` into itself.  Equivalently, every point of `𝒟̄`
has its `S`-translate in `𝒟̄`, so that a function (or bound) propagated from `𝒟̄` can be
evaluated at `S • z` without leaving `𝒟̄`.

The proof is the continuity of `z ↦ S • z` together with the open statement
`S_smul_mem_DomainD_of_mem : S • 𝒟 ⊆ 𝒟`, which gives `S • 𝒟̄ ⊆ closure (S • 𝒟) ⊆ 𝒟̄`. -/
theorem S_smul_mem_closure_DomainD {z : UpperHalfPlane}
    (hz : z ∈ closure Work.Asymptotics.DomainD) :
    ModularGroup.S • z ∈ closure Work.Asymptotics.DomainD := by
  haveI : ContinuousSMul SL(2, ℤ) ℍ :=
    MulAction.continuousSMul_compHom (f := SpecialLinearGroup.mapGL ℝ)
      continuous_of_discreteTopology
  have hcont : Continuous fun σ : ℍ => (ModularGroup.S : SL(2, ℤ)) • σ :=
    continuous_const_smul ModularGroup.S
  have hclosed : IsClosed {σ : ℍ | (ModularGroup.S : SL(2, ℤ)) • σ ∈ closure DomainD} :=
    isClosed_closure.preimage hcont
  have hsub : DomainD ⊆ {σ : ℍ | (ModularGroup.S : SL(2, ℤ)) • σ ∈ closure DomainD} :=
    fun σ hσ => subset_closure (S_smul_mem_DomainD_of_mem hσ)
  exact closure_minimal hsub hclosed hz

end Work.Asymptotics
