/-
The coordinate bridge between the weak formulation on `ℝ × ℝ` (`Q0.StripWeakRR`, the
`(σ,θ)`-coordinates with the `deriv`-level operator `kopD`) and the weak formulation on
`E2 = EuclideanSpace ℝ (Fin 2)` (`Q0.StripWeakQ0`/`StripWeakC`, with the operator `Kop`).

The map `coords : ℝ × ℝ → E2` is a homeomorphism with `coords σ θ = (σ,θ)`, it is
measure preserving (`VT.coords_measurePreserving`) and a measurable embedding
(`VT.coords_measurableEmbedding`).  Concretely:

* `∫ x : E2, g x = ∫ q : ℝ × ℝ, g (coords q.1 q.2)` (`coordsIntegral`);
* `Kop ψ (coords σ θ) = kopD (fun σ θ => ψ (coords σ θ)) σ θ` (`kopD_coords_aux`);
* the transported unknowns/sources agree pointwise:
  `VRR α Ψ σ θ = Vf α Ψ (coords σ θ)` and `GRR α F σ θ = Gf α F (coords σ θ)`;
* a test function on `E2` supported in the strip pulls back to one supported in `stripRR`
  (`uncurryCoords_aux`).

The statement `stripWeakQ0_of_RR` is the resulting implication between the two weak
formulations.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.InteriorRegularity.Q0.RRDefs
import Submission.Work.EllipticEst.InteriorRegularity.Q0.Defs
import Submission.Work.EllipticEst.InteriorRegularity.curryC_bridge
import Submission.Work.EllipticEst.InteriorRegularity.Strip
import Submission.Work.EllipticEst.InteriorRegularity.VT.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

/-! ### Elementary facts about `coords` and the strip -/

/-- The coordinate map is a bijection: `coords (x 0) (x 1) = x`. -/
lemma coords_mk (x : E2) : coords (x 0) (x 1) = x := by
  ext i
  fin_cases i <;> simp [coords]

/-- Membership in the strip, in terms of the second coordinate. -/
lemma mem_stripE_iff (σ θ : ℝ) :
    coords σ θ ∈ stripE ↔ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  simp only [stripE, Set.mem_setOf_eq, VT.coords_one]

/-- The preimage of the strip `stripE ⊆ E2` under `coords` is the half-strip `stripRR`. -/
lemma preimage_stripE : (fun q : ℝ × ℝ => coords q.1 q.2) ⁻¹' stripE = stripRR := by
  ext q
  simp only [Set.mem_preimage, mem_stripE_iff, stripRR, Set.mem_prod, Set.mem_univ, true_and]

/-- The image of the half-strip `stripRR` under `coords` is the strip `stripE`. -/
lemma image_stripE : (fun q : ℝ × ℝ => coords q.1 q.2) '' stripRR = stripE := by
  rw [← preimage_stripE]
  exact Set.image_preimage_eq _ (fun x => ⟨(x 0, x 1), coords_mk x⟩)

/-! ### The transported data agree on the strip -/

/-- The transported unknown `VRR` is the pull-back of `Vf` along `coords`. -/
lemma VRR_eq_Vf (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (σ θ : ℝ) :
    VRR α Ψ σ θ = Vf α Ψ (coords σ θ) := by
  by_cases hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  · rw [VRR, if_pos hθ]
    rw [Vf, Set.indicator_of_mem ((mem_stripE_iff σ θ).mpr hθ)]
    simp only [wt, wtRR, VT.coords_zero, VT.coords_one]
  · rw [VRR, if_neg hθ]
    rw [Vf, Set.indicator_of_notMem (fun h => hθ ((mem_stripE_iff σ θ).mp h))]

/-- The transported source `GRR` is the pull-back of `Gf` along `coords`. -/
lemma GRR_eq_Gf (α : ℝ) (F : ℝ → ℝ → ℝ) (σ θ : ℝ) :
    GRR α F σ θ = Gf α F (coords σ θ) := by
  by_cases hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  · rw [GRR, if_pos hθ]
    rw [Gf, Set.indicator_of_mem ((mem_stripE_iff σ θ).mpr hθ)]
    simp only [wt, wtRR, VT.coords_zero, VT.coords_one]
  · rw [GRR, if_neg hθ]
    rw [Gf, Set.indicator_of_notMem (fun h => hθ ((mem_stripE_iff σ θ).mp h))]

/-! ### The change of variables `ℝ × ℝ ↔ E2` -/

/-- The coordinate map `q ↦ coords q.1 q.2` is smooth at every order. -/
lemma contDiff_coords : ∀ n : ℕ, ContDiff ℝ n (fun q : ℝ × ℝ => coords q.1 q.2) := by
  intro n
  have h1 : ContDiff ℝ n (fun q : ℝ × ℝ => (fun i : Fin 2 => if i = 0 then q.1 else q.2)) := by
    refine contDiff_pi' (fun i => ?_)
    fin_cases i
    · simpa using (contDiff_fst : ContDiff ℝ n (Prod.fst : ℝ × ℝ → ℝ))
    · simpa using (contDiff_snd : ContDiff ℝ n (Prod.snd : ℝ × ℝ → ℝ))
  have h2 : ContDiff ℝ n (WithLp.toLp 2 : (Fin 2 → ℝ) → E2) := PiLp.contDiff_toLp
  exact h2.comp h1

/-- **Change of variables for the integral.**  Since `coords` is a measure-preserving
measurable embedding `ℝ × ℝ → E2`, the integral over `E2` equals the integral over
`ℝ × ℝ` of the pull-back. -/
lemma coordsIntegral (g : E2 → ℂ) :
    ∫ q : ℝ × ℝ, g (coords q.1 q.2) = ∫ x : E2, g x :=
  MeasureTheory.MeasurePreserving.integral_comp VT.coords_measurePreserving
    VT.coords_measurableEmbedding g

/-! ### The operator identity -/

/-- **The two forms of `bslOp` agree.**  For a smooth `ψ : E2 → ℂ`, the `deriv`-level operator
`kopD` applied to the pull-back `(σ,θ) ↦ ψ (coords σ θ)` is `Kop ψ` evaluated at
`coords σ θ`. -/
lemma kopD_coords_aux {ψ : E2 → ℂ} (hψ : ∀ n : ℕ, ContDiff ℝ n ψ) (σ θ : ℝ) :
    kopD (fun σ θ => ψ (coords σ θ)) σ θ = Kop ψ (coords σ θ) := by
  have hsm : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry (fun σ θ : ℝ => ψ (coords σ θ))) := by
    intro n
    exact (hψ n).comp (contDiff_coords n)
  have hcur : curryC (fun σ θ : ℝ => ψ (coords σ θ)) = ψ := by
    funext x
    simp only [curryC]
    rw [coords_mk]
  obtain ⟨-, hd0, hd1, hd2⟩ := curryC_bridge hsm
  have h0 := hd0 (coords σ θ)
  have h1 := hd1 (coords σ θ)
  have h2 := hd2 (coords σ θ)
  simp only [hcur] at h0 h1 h2
  rw [VT.coords_zero, VT.coords_one] at h0 h1 h2
  have hA : d0 ψ (coords σ θ) = deriv (fun s => ψ (coords s θ)) σ := h0
  have hB : d1 ψ (coords σ θ) = deriv (fun θ' => ψ (coords σ θ')) θ := h1
  have hAB : d0 (d0 ψ) (coords σ θ) + d1 (d1 ψ) (coords σ θ)
      = deriv (fun s => deriv (fun s' => ψ (coords s' θ)) s) σ
        + deriv (fun θ' => deriv (fun θ'' => ψ (coords σ θ'')) θ') θ := h2
  simp only [kopD, Kop]
  rw [VT.coords_one]
  rw [← hA, ← hB]
  linear_combination hAB

/-! ### Pulling a test function back to the half-strip -/

/-- Every smooth compactly supported `ψ : E2 → ℂ` whose topological support lies in `stripE`
pulls back along `coords` to a smooth compactly supported `φ : ℝ → ℝ → ℂ` whose topological
support lies in the half-strip `stripRR`. -/
lemma uncurryCoords_aux {ψ : E2 → ℂ} (hψ : ∀ n : ℕ, ContDiff ℝ n ψ)
    (hc : HasCompactSupport ψ) (hts : tsupport ψ ⊆ stripE) :
    ∃ φ : ℝ → ℝ → ℂ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) ∧
      HasCompactSupport (Function.uncurry φ) ∧
      tsupport (Function.uncurry φ) ⊆ stripRR ∧
      (∀ σ θ, φ σ θ = ψ (coords σ θ)) := by
  have hfinv_cont : Continuous (fun x : E2 => (x 0, x 1)) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2)).prodMk
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (1 : Fin 2))
  have hsub : tsupport (fun q : ℝ × ℝ => ψ (coords q.1 q.2))
      ⊆ (fun q : ℝ × ℝ => coords q.1 q.2) ⁻¹' tsupport ψ := by
    rw [tsupport]
    refine closure_minimal ?_ (isClosed_closure.preimage VT.continuous_coords)
    intro q hq
    have hq' : ψ (coords q.1 q.2) ≠ 0 := by simpa [Function.mem_support] using hq
    exact subset_tsupport ψ (by simpa [Function.mem_support] using hq')
  refine ⟨fun σ θ => ψ (coords σ θ), ?_, ?_, ?_, fun σ θ => rfl⟩
  · intro n
    exact (hψ n).comp (contDiff_coords n)
  · rw [HasCompactSupport]
    refine IsCompact.of_isClosed_subset (hc.image hfinv_cont) isClosed_closure ?_
    intro q hq
    refine ⟨(fun q : ℝ × ℝ => coords q.1 q.2) q, hsub hq, ?_⟩
    simp [VT.coords_zero, VT.coords_one]
  · intro q hq
    have h1 : q ∈ (fun q : ℝ × ℝ => coords q.1 q.2) ⁻¹' stripE :=
      preimage_mono hts (hsub hq)
    rwa [preimage_stripE] at h1

/-! ### The main implication -/

theorem stripWeakQ0_of_RR {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.EllipticEst.InteriorRegularity.Q0.StripWeakRR
      (fun σ θ => (Work.EllipticEst.InteriorRegularity.Q0.VRR α Ψ σ θ : ℂ))
      (fun σ θ => (Work.EllipticEst.InteriorRegularity.Q0.GRR α F σ θ : ℂ))) :
    Work.EllipticEst.InteriorRegularity.Q0.StripWeakQ0 α
      (Work.EllipticEst.InteriorRegularity.Q0.Vf α Ψ)
      (Work.EllipticEst.InteriorRegularity.Q0.Gf α F) := by
  intro ψ hψ hc hts
  obtain ⟨φ, hφsm, hφc, hφts, hφeq⟩ := uncurryCoords_aux hψ hc hts
  have hφfun : φ = fun σ θ => ψ (coords σ θ) := funext fun σ => funext fun θ => hφeq σ θ
  have hRR := h φ hφsm hφc hφts
  have hptL : ∀ q : ℝ × ℝ, (VRR α Ψ q.1 q.2 : ℂ) * kopD φ q.1 q.2
      = (Vf α Ψ (coords q.1 q.2) : ℂ) * Kop ψ (coords q.1 q.2) := by
    intro q
    rw [VRR_eq_Vf, hφfun, kopD_coords_aux hψ q.1 q.2]
  have hptR : ∀ q : ℝ × ℝ, (GRR α F q.1 q.2 : ℂ) * φ q.1 q.2
      = (Gf α F (coords q.1 q.2) : ℂ) * ψ (coords q.1 q.2) := by
    intro q
    rw [GRR_eq_Gf, hφeq q.1 q.2]
  have hL : (∫ q : ℝ × ℝ, (VRR α Ψ q.1 q.2 : ℂ) * kopD φ q.1 q.2)
      = ∫ x : E2, (Vf α Ψ x : ℂ) * Kop ψ x := by
    rw [show (∫ q : ℝ × ℝ, (VRR α Ψ q.1 q.2 : ℂ) * kopD φ q.1 q.2)
        = ∫ q : ℝ × ℝ, (Vf α Ψ (coords q.1 q.2) : ℂ) * Kop ψ (coords q.1 q.2)
        from MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptL)]
    exact coordsIntegral (fun x : E2 => (Vf α Ψ x : ℂ) * Kop ψ x)
  have hR : (∫ q : ℝ × ℝ, (GRR α F q.1 q.2 : ℂ) * φ q.1 q.2)
      = ∫ x : E2, (Gf α F x : ℂ) * ψ x := by
    rw [show (∫ q : ℝ × ℝ, (GRR α F q.1 q.2 : ℂ) * φ q.1 q.2)
        = ∫ q : ℝ × ℝ, (Gf α F (coords q.1 q.2) : ℂ) * ψ (coords q.1 q.2)
        from MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptR)]
    exact coordsIntegral (fun x : E2 => (Gf α F x : ℂ) * ψ x)
  rw [← hL, ← hR]
  exact hRR

end Work.EllipticEst.InteriorRegularity.Q0
