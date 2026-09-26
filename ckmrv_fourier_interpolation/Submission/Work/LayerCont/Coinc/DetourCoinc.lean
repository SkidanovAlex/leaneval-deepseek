/-
# The left detour equals the replaced interval integral, coincidence case

The **main deliverable** of this layer: `Work.Asymptotics.detourLeftC_eq_interval_of_noOrbit`
evaluates the left detour against the axis interval whenever the swept rectangle `[-ξ,0] ×
[c-A,c+A]` contains no point of the `SL(2,ℤ)`-orbit of `τ`.  On the *far* side of the line
`Re τ = 1` (i.e. for `Re τ > 1`) at the coincidence height `c = t₀⁻¹ = 1/τ.im` the rectangle
contains **exactly one** orbit point: the removable coincidence `z₀ = coincℂ τ = ST⁻¹τ`, whose
residue vanishes.  The same Cauchy–Goursat statement therefore holds, with the point `z₀` playing
the role of the (absent) pole:

* `Work.LayerCont.Coinc.detourLeftC_eq_interval_of_coinc`.

Hypotheses (all "for `τ` in the ball `B(1 + i t₀, ε)`"):

* `hclean` — the rectangle minus the coincidence is `j`-clean;
* `hcoinc` — the coincidence really lies in the *open* rectangle (this is the geometric
  hypothesis forcing `1 < τ.re`);
* `hdeg` — `j'(τ) ≠ 0`, so that the residue statement `hasResidue_Kfun_coinc` applies.

The continuity/holomorphy inputs come from the `z₀`-generic cleanliness lemmas
(`Work.LayerCont.Coinc.dlcc_continuousOn_generic`, `dlcc_differentiableAt_generic`) and the
residue limit from `Work.LayerCont.Coinc.tendsto_coinc_residue`; the rectangle theorem itself is
`Work.Asymptotics.rectInt_eq_residue`.
-/
import Mathlib
import Submission.Work.LayerCont.Coinc.DlccGeneric
import Submission.Work.LayerCont.Coinc.Residue
import Submission.Work.Asymptotics.rectInt_eq_residue

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

namespace Work.LayerCont.Coinc

open Work.Asymptotics

/-- **The left detour equals the replaced interval integral at a residue-free coincidence.**

This is `Work.Asymptotics.detourLeftC_eq_interval_of_noOrbit` with the excluded interior point
`z₀ = coincℂ τ` (which is now genuinely inside the rectangle, `hcoinc`): the residue there vanishes
(`Work.LayerCont.hasResidue_Kfun_coinc`), so the rectangle integral is still `0` and the detour
still equals `∫_{I} edgeV`. -/
theorem detourLeftC_eq_interval_of_coinc (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    {r c A ξ ε t₀ : ℝ} (ht₀ : 0 < t₀) (hε : 0 < ε) (hA : 0 < A) (hξ : 0 < ξ) (hcA : 0 < c - A)
    (hclean : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
      ∀ z : ℂ, z ∈ leftRectℂ c A ξ → z ≠ coincℂ τ →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z))
    (hcoinc : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
      coincℂ τ ∈ openLeftRectℂ c A ξ)
    (hdeg : ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
      Work.Residues.jprime τ ≠ 0) :
    ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
      detourLeftC ℓ d r c A ξ τ
        = ∫ v in Set.Ioo (c - A) (c + A), edgeV ℓ d r τ 0 v := by
  intro τ hτball
  by_cases hd : d = 8 ∨ d = 24
  · set z₀ : ℂ := coincℂ τ with hz₀
    have hclean' : ∀ z : ℂ, z ∈ leftRectℂ c A ξ → z ≠ z₀ →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z) :=
      fun z hz hz' => hclean τ hτball z hz (by rwa [hz₀] at hz')
    have hmem : z₀ ∈ openLeftRectℂ c A ξ := by rw [hz₀]; exact hcoinc τ hτball
    simp only [openLeftRectℂ, Set.mem_ofPred_eq] at hmem
    obtain ⟨hre₁, hre₂, him₁, him₂⟩ := hmem
    have hcont : ContinuousOn (kerForm ℓ d r τ) (leftRectℂ c A ξ \ {z₀}) :=
      dlcc_continuousOn_generic ℓ d hd r τ c A ξ z₀ hcA hclean'
    have hhol : ∀ z : ℂ, (-ξ) < z.re → z.re < 0 → c - A < z.im → z.im < c + A → z ≠ z₀ →
        DifferentiableAt ℂ (kerForm ℓ d r τ) z :=
      fun z h1 h2 h3 h4 hz =>
        dlcc_differentiableAt_generic ℓ d hd r τ c A ξ z₀ hcA hclean' z ⟨h1, h2, h3, h4⟩ hz
    have hres : Filter.Tendsto (fun z : ℂ => (z - z₀) * kerForm ℓ d r τ z)
        (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) := by
      simpa only [← hz₀] using tendsto_coinc_residue ℓ d hd r τ (hdeg τ hτball)
    have hrect := rectInt_eq_residue (kerForm ℓ d r τ) z₀ 0 (-ξ) 0 (c - A) (c + A)
      hre₁ hre₂ him₁ him₂ hcont hhol hres
    rw [mul_zero] at hrect
    rw [dlcc_integral_edgeV ℓ d r τ 0 (c - A) (c + A) hcA (by linarith)]
    rw [detourLeftC,
      dlcc_integral_edgeH_neg ℓ d r τ ξ (c - A) hξ hcA,
      dlcc_integral_edgeV ℓ d r τ (-ξ) (c - A) (c + A) hcA (by linarith),
      dlcc_integral_edgeH_neg ℓ d r τ ξ (c + A) hξ (by linarith)]
    linear_combination -hrect
  · simp only [not_or] at hd
    have hK (w : UpperHalfPlane) : Work.Kernels.Kfun ℓ d τ w = 0 :=
      Kfun_eq_zero_of_ne hd.1 hd.2 ℓ τ w
    have hdet : detourLeftC ℓ d r c A ξ τ = 0 := by
      simp [detourLeftC, edgeH, edgeV, hK]
    have hint : (∫ v in Set.Ioo (c - A) (c + A), edgeV ℓ d r τ 0 v) = 0 := by
      simp [edgeV, hK]
    rw [hdet, hint]

end Work.LayerCont.Coinc
