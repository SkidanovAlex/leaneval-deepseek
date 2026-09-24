import Mathlib
import Submission.Conjugate
import Submission.PackagingOpen

/-!
# Periodic harmonic functions on a half-plane are real parts of periodic holomorphic functions

Let `U : ℂ → ℝ` be harmonic on the half-plane `{ζ : ℂ | ζ.re < L}` and `2πi`-periodic there.
Then there are `γ : ℝ` and `G : ℂ → ℂ`, holomorphic and `2πi`-periodic on that half-plane, with
`(G ζ).re = U ζ - γ * ζ.re`.

The half-plane is convex, hence simply connected, so the project's global existence theorem for
harmonic conjugates `Submission.exists_holomorphicOnX_re_of_harmonic` applies to the half-plane
bundled as an open subset of `ℂ`.  This produces a holomorphic `G₀` with `Re G₀ = U`; the
monodromy of `G₀` with respect to the translation `ζ ↦ ζ + 2πi` is the holomorphic function
`ζ ↦ G₀ (ζ + 2πi) - G₀ ζ`, whose real part vanishes by the periodicity of `U`, so it is constant
`i·γ` with `γ` real, and `G := G₀ - γ ζ` is the function sought.
-/

open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set

namespace Work.Potential

/-- The half-plane `{ζ : ℂ | ζ.re < L}`, bundled as an open subset of `ℂ`. -/
def halfPlane (L : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨{ζ : ℂ | ζ.re < L}, isOpen_lt Complex.continuous_re continuous_const⟩

@[simp] theorem coe_halfPlane (L : ℝ) : (halfPlane L : Set ℂ) = {ζ : ℂ | ζ.re < L} := rfl

theorem harmonic_halfplane_periodic_conjugate
    {L : ℝ} {U : ℂ → ℝ}
    (hU : ∀ ζ : ℂ, ζ.re < L → InnerProductSpace.HarmonicAt U ζ)
    (hper : ∀ ζ : ℂ, ζ.re < L → U (ζ + 2 * Real.pi * Complex.I) = U ζ) :
    ∃ (γ : ℝ) (G : ℂ → ℂ),
      (∀ ζ : ℂ, ζ.re < L → AnalyticAt ℂ G ζ) ∧
      (∀ ζ : ℂ, ζ.re < L → G (ζ + 2 * Real.pi * Complex.I) = G ζ) ∧
      (∀ ζ : ℂ, ζ.re < L → (G ζ).re = U ζ - γ * ζ.re) := by
  classical
  set τ : ℂ := 2 * Real.pi * Complex.I with hτdef
  have hτre : τ.re = 0 := by simp [hτdef]
  -- the half-plane is convex, non-empty, hence contractible and simply connected
  have hconv : Convex ℝ (halfPlane L : Set ℂ) := by
    rw [coe_halfPlane]; exact convex_halfSpace_re_lt L
  have hne : (halfPlane L : Set ℂ).Nonempty :=
    ⟨((L - 1 : ℝ) : ℂ), by
      show (((L - 1 : ℝ) : ℂ)).re < L
      simp⟩
  haveI hcontr : ContractibleSpace (halfPlane L) := hconv.contractibleSpace hne
  haveI hconn : ConnectedSpace (halfPlane L) := inferInstance
  -- a base point
  let x₀ : halfPlane L := ⟨((L - 1 : ℝ) : ℂ), by
    show (((L - 1 : ℝ) : ℂ)).re < L
    simp⟩
  haveI hsub : Subsingleton (Additive (FundamentalGroup (halfPlane L) x₀) →+ ℝ) :=
    ⟨fun f g => AddMonoidHom.ext fun a => by
      rw [show a = 0 from Subsingleton.elim a 0, map_zero, map_zero]⟩
  -- the restricted function is harmonic on the open subset
  have hHarm : Submission.HarmonicOnX (fun z : halfPlane L => U z.1) Set.univ := by
    intro z _
    show InnerProductSpace.HarmonicAt
      ((fun z : halfPlane L => U z.1) ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z)
    rw [Submission.opens_chartAt_apply (halfPlane L) z]
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr (hU z.1 z.2)
    filter_upwards [(halfPlane L).2.mem_nhds z.2] with w hw
    simp only [Function.comp_apply]
    have hw' : ((chartAt ℂ z).symm w : halfPlane L) = ⟨w, hw⟩ :=
      Subtype.ext (Submission.opens_chartAt_symm_apply_cast (halfPlane L) hw)
    show U (((chartAt ℂ z).symm w : halfPlane L) : ℂ) = U w
    rw [hw']
  -- a global holomorphic conjugate of `U` on the half-plane
  obtain ⟨F, hFhol, hFre⟩ :=
    Submission.exists_holomorphicOnX_re_of_harmonic (X := halfPlane L) x₀
      (h := fun z : halfPlane L => U z.1) hHarm
  have hFre' : ∀ z : halfPlane L, (F z).re = U z.1 := fun z => hFre z
  -- an ambient version of `F`
  set G₀ : ℂ → ℂ := fun ζ => if h : ζ.re < L then F ⟨ζ, h⟩ else 0 with hG₀def
  have hG₀apply : ∀ ζ (hζ : ζ.re < L), G₀ ζ = F ⟨ζ, hζ⟩ := by
    intro ζ hζ
    rw [hG₀def]
    simp only [dif_pos hζ]
  have hG₀re : ∀ ζ (hζ : ζ.re < L), (G₀ ζ).re = U ζ := by
    intro ζ hζ
    rw [hG₀apply ζ hζ]
    exact hFre' ⟨ζ, hζ⟩
  have hG₀an : ∀ ζ (hζ : ζ.re < L), AnalyticAt ℂ G₀ ζ := by
    intro ζ hζ
    have h1 : AnalyticAt ℂ (F ∘ (chartAt ℂ (⟨ζ, hζ⟩ : halfPlane L)).symm)
        ((chartAt ℂ (⟨ζ, hζ⟩ : halfPlane L)) ⟨ζ, hζ⟩) :=
      hFhol ⟨ζ, hζ⟩ (Set.mem_univ _)
    rw [Submission.opens_chartAt_apply (halfPlane L) ⟨ζ, hζ⟩] at h1
    refine h1.congr ?_
    filter_upwards [(halfPlane L).2.mem_nhds (show ζ ∈ (halfPlane L : Set ℂ) from hζ)] with w hw
    simp only [Function.comp_apply]
    have hw' : ((chartAt ℂ (⟨ζ, hζ⟩ : halfPlane L)).symm w : halfPlane L) = ⟨w, hw⟩ :=
      Subtype.ext (Submission.opens_chartAt_symm_apply_cast (halfPlane L) hw)
    show F ((chartAt ℂ (⟨ζ, hζ⟩ : halfPlane L)).symm w) = G₀ w
    rw [hw', hG₀apply w hw]
  -- the `2πi`-period of `G₀`
  have hPan : AnalyticOnNhd ℂ (fun ζ => G₀ (ζ + τ) - G₀ ζ) {ζ : ℂ | ζ.re < L} := by
    intro ζ hζ
    have hζτ : (ζ + τ).re < L := by rw [Complex.add_re, hτre, add_zero]; exact hζ
    refine AnalyticAt.sub ?_ (hG₀an ζ hζ)
    refine (hG₀an (ζ + τ) hζτ).comp (f := fun w : ℂ => w + τ) (x := ζ) ?_
    refine (analyticAt_id.add (analyticAt_const (v := τ))).congr ?_
    filter_upwards with w
    simp only [Pi.add_apply, id_eq]
  have hPre : ∀ ζ ∈ {ζ : ℂ | ζ.re < L}, ((fun ζ => G₀ (ζ + τ) - G₀ ζ) ζ).re = 0 := by
    intro ζ hζ
    have hζτ : (ζ + τ).re < L := by rw [Complex.add_re, hτre, add_zero]; exact hζ
    change (G₀ (ζ + τ) - G₀ ζ).re = 0
    rw [Complex.sub_re, hG₀re (ζ + τ) hζτ, hG₀re ζ hζ, hper ζ hζ, sub_self]
  obtain ⟨c, hc⟩ := AnalyticOnNhd.eq_const_of_re_eq_const hPan hPre
    (isOpen_lt Complex.continuous_re continuous_const) (isConnected_iff_connectedSpace.mpr hconn)
  have hcre : c.re = 0 := by
    have h := hPre ((L - 1 : ℝ) : ℂ) (by simp)
    have h2 : G₀ (((L - 1 : ℝ) : ℂ) + τ) - G₀ ((L - 1 : ℝ) : ℂ) = c := hc _ (by simp)
    change (G₀ (((L - 1 : ℝ) : ℂ) + τ) - G₀ ((L - 1 : ℝ) : ℂ)).re = 0 at h
    rw [h2] at h
    exact h
  have hcim : c = (c.im : ℂ) * Complex.I := by
    have h := Complex.re_add_im c
    rw [hcre] at h
    simpa using h.symm
  have hγτ : ((c.im / (2 * Real.pi) : ℝ) : ℂ) * τ = (c.im : ℂ) * Complex.I := by
    have h2pi : (2 * Real.pi) ≠ 0 := by positivity
    have step : ((c.im / (2 * Real.pi) : ℝ) : ℂ) * τ
        = (((c.im / (2 * Real.pi)) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      rw [hτdef]
      push_cast
      ring
    rw [step, div_mul_cancel₀ c.im h2pi]
  refine ⟨c.im / (2 * Real.pi),
    fun ζ => G₀ ζ - ((c.im / (2 * Real.pi) : ℝ) : ℂ) * ζ, ?_, ?_, ?_⟩
  · intro ζ hζ
    exact (hG₀an ζ hζ).sub (analyticAt_const.mul analyticAt_id)
  · intro ζ hζ
    have h1 : G₀ (ζ + τ) = c + G₀ ζ := sub_eq_iff_eq_add.mp (hc ζ hζ)
    have h5 : c - ((c.im / (2 * Real.pi) : ℝ) : ℂ) * τ = 0 := by
      rw [hγτ, ← hcim, sub_self]
    change G₀ (ζ + τ) - ((c.im / (2 * Real.pi) : ℝ) : ℂ) * (ζ + τ)
      = G₀ ζ - ((c.im / (2 * Real.pi) : ℝ) : ℂ) * ζ
    rw [h1]
    linear_combination h5
  · intro ζ hζ
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, hG₀re ζ hζ]

end Work.Potential
