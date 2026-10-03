import Submission.Work.Fatou.DevH.global

/-!
# The Riemann surface `XF` of a near-translation

Given a near-translation `F` on an admissible region `Qreg b₁ b₂`, the unfolding
`devH x₀ F` (`Setup.lean`) is a globally expanding homeomorphism of `ℂ` with the equivariance
`devH (ζ+1) = F (devH ζ)` on the central strip.  We put on the plane the complex structure whose
charts are the maps `ζ ↦ devH (ζ - n)` (`n : ℤ`) defined on the strips `n - 1/8 < Re ζ < n + 9/8`.
The transition maps are then `id`, `F` and `F⁻¹`, and the deck transformation `ζ ↦ ζ+1` is
holomorphic (it is the identity in charts).

The surface is packaged as the type synonym `XF D` (definitionally `ℂ`) so that `ℂ`'s own
`ChartedSpace` instance is not visible; the maps `toℂ`/`ofℂ` convert between the synonym and `ℂ`.
-/

namespace Work.Fatou

open MandelDim Filter Set Metric
open scoped Topology

noncomputable section

/-- Data of a near-translation on an admissible Shishikura region, together with the quantitative
properties of the unfolding `devH` (provided by `DevH/devH_deriv.lean`). -/
structure FatouData where
  b₁ : Option ℂ
  b₂ : Option ℂ
  F : ℂ → ℂ
  adm : QAdm b₁ b₂
  nt : NearTranslationOn F (Qreg b₁ b₂)
  devB : DevHBound (xOf b₁ b₂) F

namespace FatouData

/-- The unfolding map of `D`. -/
def devH (D : FatouData) : ℂ → ℂ := Work.Fatou.devH (xOf D.b₁ D.b₂) D.F

@[simp] theorem devH_eq (D : FatouData) (ζ : ℂ) :
    D.devH ζ = Work.Fatou.devH (xOf D.b₁ D.b₂) D.F ζ := rfl

/-- A global inverse choice of `devH` (unique on the image, by injectivity). -/
def devHI (D : FatouData) : ℂ → ℂ := Function.invFun D.devH

theorem devHI_apply_devH (D : FatouData) {ζ : ℂ} : D.devHI (D.devH ζ) = ζ := by
  have h : D.devH (D.devHI (D.devH ζ)) = D.devH ζ := Function.invFun_eq ⟨ζ, rfl⟩
  exact devH_injective D.devB h

theorem devH_apply_devHI (D : FatouData) {w : ℂ} (hw : w ∈ Set.range D.devH) :
    D.devH (D.devHI w) = w :=
  Function.invFun_eq hw

/-- The surface `XF D`: the plane, with the complex structure given by the charts `chart D n`. -/
def XF (D : FatouData) : Type := ℂ

instance (D : FatouData) : TopologicalSpace D.XF := inferInstanceAs (TopologicalSpace ℂ)
instance (D : FatouData) : T2Space D.XF := inferInstanceAs (T2Space ℂ)
instance (D : FatouData) : ConnectedSpace D.XF := inferInstanceAs (ConnectedSpace ℂ)
instance (D : FatouData) : SecondCountableTopology D.XF :=
  inferInstanceAs (SecondCountableTopology ℂ)
instance (D : FatouData) : NoncompactSpace D.XF := inferInstanceAs (NoncompactSpace ℂ)
instance (D : FatouData) : PathConnectedSpace D.XF := inferInstanceAs (PathConnectedSpace ℂ)
instance (D : FatouData) : LocallyCompactSpace D.XF := inferInstanceAs (LocallyCompactSpace ℂ)
instance (D : FatouData) : SimplyConnectedSpace D.XF := inferInstanceAs (SimplyConnectedSpace ℂ)

/-- The identity of `XF D` with `ℂ`. -/
def toℂ (D : FatouData) (u : D.XF) : ℂ := u

/-- The inverse of `toℂ`. -/
def ofℂ (D : FatouData) (z : ℂ) : D.XF := z

@[simp] theorem toℂ_ofℂ (D : FatouData) (z : ℂ) : D.toℂ (D.ofℂ z) = z := rfl
@[simp] theorem ofℂ_toℂ (D : FatouData) (u : D.XF) : D.ofℂ (D.toℂ u) = u := rfl
theorem continuous_toℂ (D : FatouData) : Continuous D.toℂ := continuous_id
theorem continuous_ofℂ (D : FatouData) : Continuous D.ofℂ := continuous_id

/-- The source strip of the chart of index `n`, as a subset of the surface. -/
def chartSource (D : FatouData) (n : ℤ) : Set D.XF :=
  {u : D.XF | (n : ℝ) - 1 / 8 < (D.toℂ u).re ∧ (D.toℂ u).re < (n : ℝ) + 9 / 8}

theorem mem_chartSource {D : FatouData} {n : ℤ} {u : D.XF} :
    u ∈ D.chartSource n ↔ (n : ℝ) - 1 / 8 < (D.toℂ u).re ∧ (D.toℂ u).re < (n : ℝ) + 9 / 8 :=
  Iff.rfl

/-- The underlying partial equivariant of the chart of index `n`. -/
def chartEquiv (D : FatouData) (n : ℤ) : PartialEquiv D.XF ℂ where
  toFun u := D.devH (D.toℂ u - (n : ℂ))
  invFun w := D.ofℂ (D.devHI w + (n : ℂ))
  source := D.chartSource n
  target := D.devH '' Sigma
  map_source' := by
    intro u hu
    rw [mem_chartSource] at hu
    refine ⟨D.toℂ u - (n : ℂ), ?_, rfl⟩
    rw [mem_Sigma]
    have h : (D.toℂ u - (n : ℂ)).re = (D.toℂ u).re - (n : ℝ) := by simp
    rw [h]
    constructor <;> linarith
  map_target' := by
    intro w hw
    obtain ⟨ζ, hζ, rfl⟩ := hw
    rw [mem_chartSource]
    have h2 : D.toℂ (D.ofℂ (D.devHI (D.devH ζ) + (n : ℂ))) = ζ + (n : ℂ) := by
      rw [D.toℂ_ofℂ, D.devHI_apply_devH]
    rw [h2]
    have h3 : (ζ + (n : ℂ)).re = ζ.re + (n : ℝ) := by simp
    rw [h3]
    exact ⟨by linarith [hζ.1], by linarith [hζ.2]⟩
  left_inv' := by
    intro u hu
    show D.ofℂ (D.devHI (D.devH (D.toℂ u - (n : ℂ))) + (n : ℂ)) = u
    rw [D.devHI_apply_devH]
    show D.ofℂ (D.toℂ u - (n : ℂ) + (n : ℂ)) = u
    rw [sub_add_cancel, D.ofℂ_toℂ]
  right_inv' := by
    intro w hw
    obtain ⟨ζ, hζ, rfl⟩ := hw
    show D.devH (D.toℂ (D.ofℂ (D.devHI (D.devH ζ) + (n : ℂ))) - (n : ℂ)) = D.devH ζ
    rw [D.toℂ_ofℂ, D.devHI_apply_devH]
    ring_nf

/-- The chart of index `n` of the surface `XF D`. -/
def chart (D : FatouData) (n : ℤ) : OpenPartialHomeomorph D.XF ℂ :=
  OpenPartialHomeomorph.ofContinuousOpen (D.chartEquiv n)
    (by
      change ContinuousOn (fun u : D.XF => D.devH (D.toℂ u - (n : ℂ))) (D.chartSource n)
      exact (D.devB.contDiff.continuous.comp
        (D.continuous_toℂ.sub continuous_const)).continuousOn)
    (by
      change IsOpenMap (fun u : D.XF => D.devH (D.toℂ u - (n : ℂ)))
      have hshift : IsOpenMap (fun u : ℂ => u - (n : ℂ)) := by
        have h1 : (fun u : ℂ => u - (n : ℂ)) = fun u : ℂ => -((n : ℂ)) + u := by
          funext u; ring
        rw [h1]
        exact (Homeomorph.addLeft _).isOpenMap
      exact ((isOpenMap_devH D.devB).comp hshift).comp IsOpenMap.id)
    (by
      change IsOpen (D.chartSource n)
      have hopen : IsOpen {z : ℂ | (n : ℝ) - 1 / 8 < z.re ∧ z.re < (n : ℝ) + 9 / 8} :=
        (isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const)
      have hpre : D.chartSource n = D.toℂ ⁻¹' {z : ℂ |
          (n : ℝ) - 1 / 8 < z.re ∧ z.re < (n : ℝ) + 9 / 8} := rfl
      rw [hpre]
      exact hopen.preimage D.continuous_toℂ)

@[simp] theorem chart_source (D : FatouData) (n : ℤ) : (D.chart n).source = D.chartSource n := rfl
@[simp] theorem chart_target (D : FatouData) (n : ℤ) : (D.chart n).target = D.devH '' Sigma := rfl

theorem chart_apply (D : FatouData) (n : ℤ) (u : D.XF) :
    D.chart n u = D.devH (D.toℂ u - (n : ℂ)) := rfl

end FatouData

open FatouData

variable (D : FatouData)

/-- The charts of `XF D`, as a charted space. -/
instance chartedSpaceXF : ChartedSpace ℂ D.XF where
  atlas := Set.range (D.chart ·)
  chartAt := fun u => D.chart ⌊(D.toℂ u).re⌋
  mem_chart_source := by
    intro u
    rw [D.chart_source, mem_chartSource]
    have h1 : ((⌊(D.toℂ u).re⌋ : ℤ) : ℝ) ≤ (D.toℂ u).re := Int.floor_le _
    have h2 : (D.toℂ u).re < ((⌊(D.toℂ u).re⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    constructor <;> linarith
  chart_mem_atlas := fun u => ⟨_, rfl⟩

end

end Work.Fatou
