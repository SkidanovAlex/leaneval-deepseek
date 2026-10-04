import Mathlib
import Submission.Diff.Grad
import Submission.Work.Diff.GE.Gest.Base
import Submission.Work.Diff.GE.Gest.lapl_affine
import Submission.Work.Diff.GE.Gest.lapl_mul
import Submission.Work.Diff.GE.Gest.lapl_sq
import Submission.Work.Diff.GE.Gest.grad_affine
import Submission.Work.Diff.GE.Gest.ricSq_le_frobSq
import Submission.Work.Diff.GE.Gest.poly_tail_bound
import Submission.Work.Diff.GE.Gest.sum_mul_abs_le
import Submission.Work.Diff.GE.Gest.hess_mul_field
import Submission.Work.Diff.GE.Gest.lapl_cube
import Submission.Work.Diff.GE.Gest.mvfderiv_comb

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Hamilton's gradient estimate on a pinched Ricci flow (Brendle–Schoen)

Contract `GradientEstimate` of `Submission/Diff/Grad.lean`, proved from the frozen evolution
contracts `EvolRmNormSq`, `EvolDRmNormSq`, `EvolScal`, the smoothness contract `NormsSmooth`,
Bianchi + Kato `BianchiKato`, the pinching-set algebra `PinchingAlgebra` and the scalar maximum
principle `ScalarMaxPrinciple`, by applying the maximum principle to
`Ψ = |∇Rm|² + N (scal + K₀) |Rm°|² − η (scal + K₀)³`.

The auxiliary Laplacian calculus and the pure real-algebra lemmas used here live in the namespace
`Work.Diff.GE.Gest`.
-/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]

/-- Slices of a jointly smooth function on `Ico 0 T ×ˢ univ` are smooth on `M`. -/
theorem cmd_slice {T : ℝ} {u : ℝ × M → ℝ}
    (h : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ u (Ico 0 T ×ˢ univ))
    {t : ℝ} (ht : t ∈ Ico 0 T) : CMDiff ∞ (fun y : M => u (t, y)) := by
  have hmk : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (fun y : M => (t, y)) :=
    contMDiff_const.prodMk contMDiff_id
  have h2 : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => u ((t, y))) :=
    h.comp_contMDiff hmk (fun _ => ⟨ht, mem_univ _⟩)
  simpa using h2

/-- The joint smoothness of the maximum-principle function `Ψ`. -/
theorem contMDiffOn_psi (hREG : NormsSmooth I M) {G : ℝ → SMet I M} {T : ℝ}
    (hflow : IsRicciFlow G T) (K₀ N η : ℝ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => dRmNormSq (G p.1) p.2
        + N * ((scalAt (G p.1) p.2 + K₀) * rmoNormSq (G p.1) p.2)
        - η * (scalAt (G p.1) p.2 + K₀) ^ 3) (Ico 0 T ×ˢ univ) := by
  have hJdrm := hREG G T hflow dRmNormSq (by simp)
  have hJscal := hREG G T hflow scalAt (by simp)
  have hJrm := hREG G T hflow rmNormSq (by simp)
  have hJscal2 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (scalAt (G p.1) p.2) ^ 2) (Ico 0 T ×ˢ univ) := hJscal.pow 2
  have hJ1 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => 2 * (scalAt (G p.1) p.2) ^ 2
        / (((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)))) (Ico 0 T ×ˢ univ) :=
    (contMDiffOn_const.mul hJscal2).div_const _
  have hJ2 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => rmNormSq (G p.1) p.2 - 2 * (scalAt (G p.1) p.2) ^ 2
        / (((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)))) (Ico 0 T ×ˢ univ) :=
    hJrm.sub hJ1
  have hJrmo : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => rmoNormSq (G p.1) p.2) (Ico 0 T ×ˢ univ) :=
    hJ2.congr (fun p _ => (Gest.rmoNormSq_eq (G p.1) p.2))
  have hJsigma : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => scalAt (G p.1) p.2 + K₀) (Ico 0 T ×ˢ univ) :=
    hJscal.add contMDiffOn_const
  exact (hJdrm.add (contMDiffOn_const.mul (hJsigma.mul hJrmo))).sub
    (contMDiffOn_const.mul (hJsigma.pow 3))

/-- `(a+b)³ ≤ 8a³ + 8b³` for `a, b ≥ 0`. -/
theorem add_cube_le_eight (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 8 * a ^ 3 + 8 * b ^ 3 := by
  have h1 : 3 * a ^ 2 * b ≤ 2 * a ^ 3 + b ^ 3 := by
    have h : 0 ≤ (a - b) ^ 2 * (2 * a + b) := mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith [h]
  have h2 : 3 * a * b ^ 2 ≤ a ^ 3 + 2 * b ^ 3 := by
    have h : 0 ≤ (a - b) ^ 2 * (a + 2 * b) := mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith [h]
  nlinarith [h1, h2]


/-- `laplAt` is additive. -/
private theorem lapl_add_p [T2Space M] {g : SMet I M} {u v : M → ℝ}
    (hu : CMDiff ∞ u) (hv : CMDiff ∞ v) (x : M) :
    laplAt g (fun y => u y + v y) x = laplAt g u x + laplAt g v x := by
  have hval : ∀ (y : M) (Z : TangentSpace I y),
      mvfderiv I (fun z => u z + v z) y Z = mvfderiv I u y Z + mvfderiv I v y Z := by
    intro y Z
    have h2 : mvfderiv I (fun z => u z + v z) y = mvfderiv I (u + v) y := by
      congr 1
    rw [h2]
    have h := congrArg (fun (L : TangentSpace I y →L[ℝ] ℝ) => L Z)
      (mvfderiv_add (hu.mdifferentiableAt (by simp)) (hv.mdifferentiableAt (by simp)))
    simpa using h
  have hhess : ∀ d : TangentSpace I x,
      hessAt g (fun y => u y + v y) x d d = hessAt g u x d d + hessAt g v x d d := by
    intro d
    have hW : CMDiff ∞ (T% (smoothExt x d)) := Gest.smoothExt_contMDiff x d
    have hGu : CMDiff ∞ (fun y : M => mvfderiv I u y (smoothExt x d y)) :=
      Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hu hW
    have hGv : CMDiff ∞ (fun y : M => mvfderiv I v y (smoothExt x d y)) :=
      Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hv hW
    have h2 : mvfderiv I (fun y : M => mvfderiv I (fun z => u z + v z) y (smoothExt x d y)) x d
        = (mvfderiv I (fun y : M => mvfderiv I u y (smoothExt x d y)) x d)
          + (mvfderiv I (fun y : M => mvfderiv I v y (smoothExt x d y)) x d) := by
      have heq : (fun y : M => mvfderiv I (fun z => u z + v z) y (smoothExt x d y))
          = (fun y : M => mvfderiv I u y (smoothExt x d y))
            + (fun y : M => mvfderiv I v y (smoothExt x d y)) := by
        funext y; rw [hval y (smoothExt x d y)]; rfl
      rw [heq]
      have h := congrArg (fun (L : TangentSpace I x →L[ℝ] ℝ) => L d)
        (mvfderiv_add (hGu.mdifferentiableAt (by simp)) (hGv.mdifferentiableAt (by simp)))
      simpa using h
    have h3 : mvfderiv I (fun z => u z + v z) x (lcOf g (smoothExt x d) x d)
        = mvfderiv I u x (lcOf g (smoothExt x d) x d)
          + mvfderiv I v x (lcOf g (smoothExt x d) x d) := hval x _
    simp only [hessAt]
    rw [h2, h3]
    ring
  simp only [laplAt]
  rw [Finset.sum_congr rfl (fun i _ => hhess (onFrame g x i)), Finset.sum_add_distrib]

/-- `laplAt` of `u + N v - η w`. -/
private theorem lapl_comb_p [T2Space M] {g : SMet I M} {u v w : M → ℝ}
    (hu : CMDiff ∞ u) (hv : CMDiff ∞ v) (hw : CMDiff ∞ w) (N η : ℝ) (x : M) :
    laplAt g (fun y => u y + N * v y - η * w y) x
      = laplAt g u x + N * laplAt g v x - η * laplAt g w x := by
  have hval : ∀ (y : M) (Z : TangentSpace I y),
      mvfderiv I (fun z => u z + N * v z - η * w z) y Z
        = mvfderiv I u y Z + N * mvfderiv I v y Z - η * mvfderiv I w y Z := by
    intro y Z
    have h1 : (fun z : M => u z + N * v z - η * w z)
        = fun z : M => 1 * u z + N * v z + (-η) * w z := by funext z; ring
    rw [h1, Gest.mvfderiv_comb 1 N (-η) hu hv hw y Z]
    ring
  have hhess : ∀ d : TangentSpace I x,
      hessAt g (fun y => u y + N * v y - η * w y) x d d
        = hessAt g u x d d + N * hessAt g v x d d - η * hessAt g w x d d := by
    intro d
    have hW : CMDiff ∞ (T% (smoothExt x d)) := Gest.smoothExt_contMDiff x d
    have hGu : CMDiff ∞ (fun y : M => mvfderiv I u y (smoothExt x d y)) :=
      Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hu hW
    have hGv : CMDiff ∞ (fun y : M => mvfderiv I v y (smoothExt x d y)) :=
      Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hv hW
    have hGw : CMDiff ∞ (fun y : M => mvfderiv I w y (smoothExt x d y)) :=
      Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hw hW
    have h2 : mvfderiv I (fun y : M => mvfderiv I (fun z => u z + N * v z - η * w z) y
          (smoothExt x d y)) x d
        = (mvfderiv I (fun y : M => mvfderiv I u y (smoothExt x d y)) x d)
          + N * (mvfderiv I (fun y : M => mvfderiv I v y (smoothExt x d y)) x d)
          - η * (mvfderiv I (fun y : M => mvfderiv I w y (smoothExt x d y)) x d) := by
      have heq : (fun y : M => mvfderiv I (fun z => u z + N * v z - η * w z) y
            (smoothExt x d y))
          = fun y : M => 1 * (mvfderiv I u y (smoothExt x d y))
              + N * (mvfderiv I v y (smoothExt x d y))
              + (-η) * (mvfderiv I w y (smoothExt x d y)) := by
        funext y; rw [hval y (smoothExt x d y)]; ring
      rw [heq, Gest.mvfderiv_comb 1 N (-η) hGu hGv hGw x d]
      ring
    have h3 : mvfderiv I (fun z => u z + N * v z - η * w z) x (lcOf g (smoothExt x d) x d)
        = mvfderiv I u x (lcOf g (smoothExt x d) x d)
          + N * mvfderiv I v x (lcOf g (smoothExt x d) x d)
          - η * mvfderiv I w x (lcOf g (smoothExt x d) x d) := hval x _
    simp only [hessAt]
    rw [h2, h3]
    ring
  simp only [laplAt]
  rw [Finset.sum_congr rfl (fun i _ => hhess (onFrame g x i))]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

set_option maxHeartbeats 30000000 in
theorem gradient_estimate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hn : 3 ≤ Module.finrank ℝ E)
    (hEV1 : EvolRmNormSq I M) (hEV2 : EvolDRmNormSq I M) (hEV3 : EvolScal I M)
    (hREG : NormsSmooth I M) (hBK : BianchiKato I M) (hPA : PinchingAlgebra (Module.finrank ℝ E))
    (hSMP : ScalarMaxPrinciple I M) :
    GradientEstimate I M := by
  intro G T F hT hflow hF hCurv η hη
  -- ## We run the maximum principle with `η' = η / 8`.
  set η' : ℝ := η / 8 with hη'def
  have hη'pos : 0 < η' := by rw [hη'def]; linarith
  have hη'ex : η = 8 * η' := by rw [hη'def]; ring
  -- dimension facts
  have hnR3 : (3 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hn
  have hnRpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by linarith
  have hnnpos : 0 < (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) := by nlinarith
  -- ## Unpacking the contracts.
  obtain ⟨c₁, hc₁0, hEV2'⟩ := hEV2
  obtain ⟨K, hK0, hBK'⟩ := hBK
  obtain ⟨hPA1, hPA2, hPA3⟩ := hPA
  obtain ⟨hp1, hp2⟩ := hPA1 F hF
  obtain ⟨c, C₀, hcpos, hbound⟩ := hp1
  obtain ⟨c₂, hc₂⟩ := hPA2
  obtain ⟨-, -, hAlgF, -, -⟩ := hF.1
  -- ## The constants.
  set K₀ : ℝ := C₀ / c + 1 with hK₀def
  set Am : ℝ := 1 + 2 * K / ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1))
    with hAmdef
  have hAm1 : 1 ≤ Am := by
    rw [hAmdef]
    have : 0 ≤ 2 * K / ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)) :=
      div_nonneg (by linarith) hnnpos.le
    linarith
  have hAmpos : 0 < Am := lt_of_lt_of_le one_pos hAm1
  set N : ℝ := Am * (c₁ * c + 6 * η' * K + 1) with hNdef
  have hNpos : 0 < N := by
    rw [hNdef]
    have h1 : 0 ≤ c₁ * c := mul_nonneg hc₁0 hcpos.le
    have h2 : 0 ≤ 6 * η' * K := by positivity
    exact mul_pos hAmpos (by linarith)
  have hNge : c₁ * c + 6 * η' * K + 1 ≤ N := by
    rw [hNdef]
    have h1 : 0 ≤ c₁ * c := mul_nonneg hc₁0 hcpos.le
    have h2 : 0 ≤ 6 * η' * K := by positivity
    nlinarith [hAm1]
  set c₂' : ℝ := max c₂ 0 with hc₂'def
  have hc₂'0 : 0 ≤ c₂' := le_max_right _ _
  have hc₂'val : c₂ ≤ c₂' := le_max_left _ _
  set c₅ : ℝ := 2 * c₂' * c + 2 * (Module.finrank ℝ E : ℝ) * c ^ 2 with hc₅def
  have hc₅0 : 0 ≤ c₅ := by
    rw [hc₅def]
    have h1 : 0 ≤ 2 * c₂' * c := by positivity
    have h2 : 0 ≤ 2 * (Module.finrank ℝ E : ℝ) * c ^ 2 := by positivity
    linarith
  set Q : ℝ := 4 * N * Real.sqrt K * c with hQdef
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    have : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
    positivity
  set δ : ℝ := min (1 / (Q + 1))
    (Real.sqrt (3 * η' / (2 * (Module.finrank ℝ E : ℝ) * (2 * N * c₅ * c ^ 2 + 1))))
    with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    refine lt_min ?_ ?_
    · positivity
    · apply Real.sqrt_pos.2
      have h1 : 0 < 2 * (Module.finrank ℝ E : ℝ) * (2 * N * c₅ * c ^ 2 + 1) := by
        have : 0 < 2 * N * c₅ * c ^ 2 + 1 := by
          have : 0 ≤ 2 * N * c₅ * c ^ 2 := by positivity
          linarith
        positivity
      exact div_pos (by positivity) h1
  have hδ1 : Q * δ ≤ 1 := by
    have h : δ ≤ 1 / (Q + 1) := by rw [hδdef]; exact min_le_left _ _
    have hQ1 : 0 < Q + 1 := by linarith
    calc Q * δ ≤ Q * (1 / (Q + 1)) := mul_le_mul_of_nonneg_left h hQ0
      _ = Q / (Q + 1) := by ring
      _ ≤ 1 := by rw [div_le_one hQ1]; linarith
  have hδ2 : 2 * N * c₅ * c ^ 2 * δ ^ 2 ≤ 3 * η' / (2 * (Module.finrank ℝ E : ℝ)) := by
    have hδle : δ ≤ Real.sqrt
        (3 * η' / (2 * (Module.finrank ℝ E : ℝ) * (2 * N * c₅ * c ^ 2 + 1))) :=
      min_le_right _ _
    have hrad : 0 ≤ 3 * η' / (2 * (Module.finrank ℝ E : ℝ) * (2 * N * c₅ * c ^ 2 + 1)) := by
      have h1 : 0 < 2 * (Module.finrank ℝ E : ℝ) * (2 * N * c₅ * c ^ 2 + 1) := by
        have : 0 < 2 * N * c₅ * c ^ 2 + 1 := by
          have : 0 ≤ 2 * N * c₅ * c ^ 2 := by positivity
          linarith
        positivity
      exact div_nonneg (by positivity) h1.le
    have hsq : δ ^ 2 ≤ 3 * η' / (2 * (Module.finrank ℝ E : ℝ) * (2 * N * c₅ * c ^ 2 + 1)) := by
      calc δ ^ 2 ≤ (Real.sqrt (3 * η' / (2 * (Module.finrank ℝ E : ℝ)
              * (2 * N * c₅ * c ^ 2 + 1)))) ^ 2 := pow_le_pow_left₀ hδpos.le hδle 2
        _ = 3 * η' / (2 * (Module.finrank ℝ E : ℝ) * (2 * N * c₅ * c ^ 2 + 1)) :=
            Real.sq_sqrt hrad
    have hden : 0 < 2 * (Module.finrank ℝ E : ℝ) * (2 * N * c₅ * c ^ 2 + 1) := by
      have : 0 < 2 * N * c₅ * c ^ 2 + 1 := by
        have : 0 ≤ 2 * N * c₅ * c ^ 2 := by positivity
        linarith
      positivity
    have hkey : 2 * N * c₅ * c ^ 2
        / (2 * (Module.finrank ℝ E : ℝ) * (2 * N * c₅ * c ^ 2 + 1))
        ≤ 1 / (2 * (Module.finrank ℝ E : ℝ)) := by
      rw [div_le_iff₀ hden]
      field_simp
      ring_nf
      linarith
    calc 2 * N * c₅ * c ^ 2 * δ ^ 2
        ≤ 2 * N * c₅ * c ^ 2 * (3 * η' / (2 * (Module.finrank ℝ E : ℝ)
            * (2 * N * c₅ * c ^ 2 + 1))) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 3 * η' * (2 * N * c₅ * c ^ 2
            / (2 * (Module.finrank ℝ E : ℝ) * (2 * N * c₅ * c ^ 2 + 1))) := by ring
      _ ≤ 3 * η' * (1 / (2 * (Module.finrank ℝ E : ℝ))) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 3 * η' / (2 * (Module.finrank ℝ E : ℝ)) := by ring
  obtain ⟨Cδ₀, hCδ₀⟩ := hp2 δ hδpos
  set Cδ : ℝ := max Cδ₀ 0 with hCδdef
  have hCδ0 : 0 ≤ Cδ := le_max_right _ _
  have hCδbound : ∀ R ∈ F, Real.sqrt (frobSqTF R) ≤ δ * Real.sqrt (frobSq R) + Cδ := by
    intro R hR
    have h := hCδ₀ R hR
    have hle : Cδ₀ ≤ Cδ := le_max_left _ _
    linarith
  set L : ℝ := 4 * N * Real.sqrt K * Cδ with hLdef
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    have : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
    positivity
  set L₁ : ℝ := max (L - 1) 0 with hL₁def
  have hL₁0 : 0 ≤ L₁ := le_max_right _ _
  have hL₁val : L - 1 ≤ L₁ := le_max_left _ _
  set M₀ : ℝ := 2 * N * c₅ * Cδ ^ 2 + (6 * η' / (Module.finrank ℝ E : ℝ)) * K₀ ^ 2
    with hM₀def
  have hM₀0 : 0 ≤ M₀ := by
    rw [hM₀def]
    have h1 : 0 ≤ 2 * N * c₅ * Cδ ^ 2 := by positivity
    have h2 : 0 ≤ (6 * η' / (Module.finrank ℝ E : ℝ)) * K₀ ^ 2 := by positivity
    linarith
  obtain ⟨C₂, hC₂0, hC₂⟩ := Gest.poly_tail_bound (3 * η' / (2 * (Module.finrank ℝ E : ℝ)))
    (L₁ * η') M₀ (by positivity) (by positivity) hM₀0
  set C₁ : ℝ := L₁ with hC₁def
  have hC₁0 : 0 ≤ C₁ := hL₁0
  -- ## Pointwise facts following from the hypotheses.
  have hmemF : ∀ t ∈ Ico 0 T, ∀ x : M, rmC (G t) x ∈ F := by
    intro t ht x
    exact hCurv t ht x (onFrame (G t) x) (Gest.isONFrame_onFrame (G t) x)
  have hAlg : ∀ t ∈ Ico 0 T, ∀ x : M, IsAlgCurv (rmC (G t) x) :=
    fun t ht x => hAlgF _ (hmemF t ht x)
  have hO0 : ∀ t ∈ Ico 0 T, ∀ x : M, 0 ≤ rmoNormSq (G t) x := by
    intro t ht x
    simpa only [rmoNormSq] using (hPA3 (rmC (G t) x) (hAlg t ht x)).2
  have hS2ric : ∀ t ∈ Ico 0 T, ∀ x : M,
      (scalAt (G t) x) ^ 2 ≤ (Module.finrank ℝ E : ℝ) * ricNormSq (G t) x := by
    intro t ht x
    simpa only [rmC, scalAt, ricNormSq, scalAlg, ricSq] using (hPA3 (rmC (G t) x) (hAlg t ht x)).1
  have hric : ∀ t ∈ Ico 0 T, ∀ x : M,
      ricNormSq (G t) x ≤ (Module.finrank ℝ E : ℝ) * rmNormSq (G t) x := by
    intro t ht x
    simpa only [rmC, ricNormSq, rmNormSq] using Gest.ricSq_le_frobSq (rmC (G t) x)
  have hsqrt_rm : ∀ t ∈ Ico 0 T, ∀ x : M,
      Real.sqrt (rmNormSq (G t) x) ≤ c * scalAt (G t) x + C₀ := by
    intro t ht x
    simpa only [rmC, rmNormSq, scalAt, scalAlg] using hbound (rmC (G t) x) (hmemF t ht x)
  have hσ1 : ∀ t ∈ Ico 0 T, ∀ x : M, 1 ≤ scalAt (G t) x + K₀ := by
    intro t ht x
    have h1 := hsqrt_rm t ht x
    have h2 : 0 ≤ c * scalAt (G t) x + C₀ := le_trans (Real.sqrt_nonneg _) h1
    have h3 : 0 ≤ scalAt (G t) x + C₀ / c := by
      have hid : scalAt (G t) x + C₀ / c = (c * scalAt (G t) x + C₀) / c := by
        field_simp
      rw [hid]
      exact div_nonneg h2 hcpos.le
    rw [hK₀def]
    linarith
  have hr_le : ∀ t ∈ Ico 0 T, ∀ x : M,
      Real.sqrt (rmNormSq (G t) x) ≤ c * (scalAt (G t) x + K₀) := by
    intro t ht x
    have h1 := hsqrt_rm t ht x
    have h2 : c * (scalAt (G t) x + K₀) = c * scalAt (G t) x + C₀ + c := by
      rw [hK₀def]
      field_simp
      ring
    have h3 : 0 ≤ c := hcpos.le
    rw [h2]
    linarith
  have hsqrt_O : ∀ t ∈ Ico 0 T, ∀ x : M,
      Real.sqrt (rmoNormSq (G t) x) ≤ δ * Real.sqrt (rmNormSq (G t) x) + Cδ := by
    intro t ht x
    simpa only [rmC, rmoNormSq, rmNormSq, frobSqTF, frobSq] using hCδbound (rmC (G t) x) (hmemF t ht x)
  have hsgF : ∀ t ∈ Ico 0 T, ∀ x : M,
      gradSq (G t) (scalAt (G t)) x ≤ K * drmoNormSq (G t) x :=
    fun t _ x => (hBK' (G t) x).1
  have hogF : ∀ t ∈ Ico 0 T, ∀ x : M,
      gradSq (G t) (rmoNormSq (G t)) x ≤ 4 * rmoNormSq (G t) x * drmoNormSq (G t) x :=
    fun t _ x => (hBK' (G t) x).2
  have hqpF : ∀ t ∈ Ico 0 T, ∀ x : M,
      qPairAt (G t) x - 4 * scalAt (G t) x
          / ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)) * ricNormSq (G t) x
        ≤ c₂' * rmoNormSq (G t) x * Real.sqrt (rmNormSq (G t) x) := by
    intro t ht x
    have h := hc₂ (rmC (G t) x) (hAlg t ht x)
    have hX : 0 ≤ rmoNormSq (G t) x * Real.sqrt (rmNormSq (G t) x) :=
      mul_nonneg (hO0 t ht x) (Real.sqrt_nonneg _)
    have hle : c₂ * rmoNormSq (G t) x * Real.sqrt (rmNormSq (G t) x)
        ≤ c₂' * rmoNormSq (G t) x * Real.sqrt (rmNormSq (G t) x) := by
      calc c₂ * rmoNormSq (G t) x * Real.sqrt (rmNormSq (G t) x)
          = c₂ * (rmoNormSq (G t) x * Real.sqrt (rmNormSq (G t) x)) := by ring
        _ ≤ c₂' * (rmoNormSq (G t) x * Real.sqrt (rmNormSq (G t) x)) :=
            mul_le_mul_of_nonneg_right hc₂'val hX
        _ = c₂' * rmoNormSq (G t) x * Real.sqrt (rmNormSq (G t) x) := by ring
    refine le_trans ?_ hle
    simpa only [rmC, qPairAt, scalAt, ricNormSq, rmoNormSq, rmNormSq, frobSqTF, frobSq] using h
  -- ## The maximum-principle function.
  let Ψ : ℝ → M → ℝ := fun t y => dRmNormSq (G t) y
    + N * ((scalAt (G t) y + K₀) * rmoNormSq (G t) y) - η' * (scalAt (G t) y + K₀) ^ 3
  have hJΨ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => Ψ p.1 p.2) (Ico 0 T ×ˢ univ) := contMDiffOn_psi hREG hflow K₀ N η'
  -- ## The pointwise differential inequality.
  have hpoint : ∀ t ∈ Ico 0 T, ∀ x : M, ∃ D : ℝ,
      HasDerivWithinAt (fun s => Ψ s x) D (Ico 0 T) t ∧
      D ≤ laplAt (G t) (Ψ t) x + C₁ * max (Ψ t x) 0 + C₂ := by
    intro t ht x
    -- ## Slices of the jointly smooth quantities.
    have hud : CMDiff ∞ (fun y : M => dRmNormSq (G t) y) :=
      cmd_slice (hREG G T hflow dRmNormSq (by simp)) ht
    have hsc : CMDiff ∞ (fun y : M => scalAt (G t) y) :=
      cmd_slice (hREG G T hflow scalAt (by simp)) ht
    have hrm : CMDiff ∞ (fun y : M => rmNormSq (G t) y) :=
      cmd_slice (hREG G T hflow rmNormSq (by simp)) ht
    have hσfun : CMDiff ∞ (fun y : M => scalAt (G t) y + K₀) := hsc.add contMDiff_const
    have hofun : CMDiff ∞ (fun y : M => rmoNormSq (G t) y) := by
      rw [show (fun y : M => rmoNormSq (G t) y) = fun y : M => rmNormSq (G t) y
            - 2 * (scalAt (G t) y) ^ 2
              / ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)) from by
        funext y; rw [Gest.rmoNormSq_eq]]
      exact hrm.sub ((contMDiff_const.mul (hsc.pow 2)).div_const _)
    have hsqfun : CMDiff ∞ (fun y : M => (scalAt (G t) y) ^ 2) := hsc.pow 2
    -- ## The values at `(t,x)`.
    set A : ℝ := dRmNormSq (G t) x with hA
    set R2 : ℝ := rmNormSq (G t) x with hR2
    set S : ℝ := scalAt (G t) x with hS
    set O : ℝ := rmoNormSq (G t) x with hO
    set Ad : ℝ := drmoNormSq (G t) x with hAd
    set ric2 : ℝ := ricNormSq (G t) x with hric2
    set qp : ℝ := qPairAt (G t) x with hset_qp
    set sg : ℝ := gradSq (G t) (scalAt (G t)) x with hset_sg
    set og : ℝ := gradSq (G t) (rmoNormSq (G t)) x with hset_og
    set LR2 : ℝ := laplAt (G t) (rmNormSq (G t)) x with hLR2
    set LA : ℝ := laplAt (G t) (dRmNormSq (G t)) x with hLA
    set LS : ℝ := laplAt (G t) (scalAt (G t)) x with hLS
    set LO : ℝ := laplAt (G t) (rmoNormSq (G t)) x with hLO
    set σ : ℝ := S + K₀ with hσ
    set nn : ℝ := (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) with hnn
    set X : ℝ := ∑ i, mvfderiv I (fun y : M => scalAt (G t) y + K₀) x (onFrame (G t) x i)
        * mvfderiv I (fun y : M => rmoNormSq (G t) y) x (onFrame (G t) x i) with hX
    -- ## The time derivatives coming from the contracts.
    obtain ⟨DA, hDA, hDAle⟩ := hEV2' G T hflow t ht x
    have hR2d := hEV1 G T hflow t ht x
    have hSd := hEV3 G T hflow t ht x
    set DR2 : ℝ := LR2 - 2 * A + 2 * qp with hDR2
    set DS : ℝ := LS + 2 * ric2 with hDS
    set DO : ℝ := DR2 - 2 * (2 * S * DS) / nn with hDO
    set Dψ : ℝ := DA + N * (DS * O + σ * DO) - η' * (3 * σ ^ 2 * DS) with hDψ
    have hDAle' : DA ≤ LA + c₁ * Real.sqrt R2 * A := by
      rw [hLA, hA, hR2]; exact hDAle
    have hR2d' : HasDerivWithinAt (fun s => rmNormSq (G s) x) DR2 (Ico 0 T) t := by
      rw [hDR2, hLR2, hA, hset_qp]; exact hR2d
    have hSd' : HasDerivWithinAt (fun s => scalAt (G s) x) DS (Ico 0 T) t := by
      rw [hDS, hLS, hric2]; exact hSd
    -- the derivative of `rmoNormSq`
    have hOd : HasDerivWithinAt (fun s => rmoNormSq (G s) x) DO (Ico 0 T) t := by
      have hsq : HasDerivWithinAt (fun s => (scalAt (G s) x) ^ 2) (2 * S * DS) (Ico 0 T) t := by
        convert hSd'.pow 2 using 1
        rw [hS]; ring_nf
      have hmain := hR2d'.sub ((hsq.const_mul 2).div_const nn)
      have hfun : (fun s => rmoNormSq (G s) x)
          = fun s => rmNormSq (G s) x - 2 * (scalAt (G s) x) ^ 2 / nn := by
        funext s
        rw [Gest.rmoNormSq_eq, hnn]
      rw [hfun]
      exact hmain
    -- the derivative of `σ · o`
    have hσOd : HasDerivWithinAt (fun s => (scalAt (G s) x + K₀) * rmoNormSq (G s) x)
        (DS * O + σ * DO) (Ico 0 T) t := by
      have h1 : HasDerivWithinAt (fun s => scalAt (G s) x + K₀) DS (Ico 0 T) t :=
        hSd'.add_const K₀
      have hh := h1.mul hOd
      rw [hO, hσ]
      exact hh
    -- the derivative of `σ³`
    have hσ3d : HasDerivWithinAt (fun s => (scalAt (G s) x + K₀) ^ 3) (3 * σ ^ 2 * DS)
        (Ico 0 T) t := by
      have h1 : HasDerivWithinAt (fun s => scalAt (G s) x + K₀) DS (Ico 0 T) t :=
        hSd'.add_const K₀
      convert h1.pow 3 using 1
    have hψd : HasDerivWithinAt (fun s => Ψ s x) Dψ (Ico 0 T) t := by
      have hStep1 : HasDerivWithinAt (fun s => N * ((scalAt (G s) x + K₀) * rmoNormSq (G s) x))
          (N * (DS * O + σ * DO)) (Ico 0 T) t := hσOd.const_mul N
      have hStep2 : HasDerivWithinAt (fun s => η' * ((scalAt (G s) x + K₀) ^ 3))
          (η' * (3 * σ ^ 2 * DS)) (Ico 0 T) t := hσ3d.const_mul η'
      have h1 := (hDA.add hStep1).sub hStep2
      have hfun : (fun s => Ψ s x) = fun s => dRmNormSq (G s) x
          + N * ((scalAt (G s) x + K₀) * rmoNormSq (G s) x)
          - η' * (scalAt (G s) x + K₀) ^ 3 := rfl
      rw [hfun]
      convert h1 using 1
    refine ⟨Dψ, hψd, ?_⟩
    -- ## The Laplacian of `Ψ`.
    have hLsig : laplAt (G t) (fun y : M => scalAt (G t) y + K₀) x = LS := by
      show laplAt (G t) (fun y : M => scalAt (G t) y + K₀) x = laplAt (G t) (scalAt (G t)) x
      have hh := Gest.lapl_affine (g := G t) (u := fun y : M => scalAt (G t) y) hsc 1 K₀ x
      have hfun : (fun y : M => scalAt (G t) y + K₀)
          = fun y : M => 1 * scalAt (G t) y + K₀ := by funext y; ring
      rw [hfun, hh]
      rw [show (fun y : M => scalAt (G t) y) = scalAt (G t) from rfl]
      ring
    have hLgradσ : gradSq (G t) (fun y : M => scalAt (G t) y + K₀) x = sg := by
      show gradSq (G t) (fun y : M => scalAt (G t) y + K₀) x
        = gradSq (G t) (scalAt (G t)) x
      have hh := Gest.grad_affine (g := G t) (u := fun y : M => scalAt (G t) y) hsc 1 K₀ x
      have hfun : (fun y : M => scalAt (G t) y + K₀)
          = fun y : M => 1 * scalAt (G t) y + K₀ := by funext y; ring
      rw [hfun, hh]
      rw [show (fun y : M => scalAt (G t) y) = scalAt (G t) from rfl]
      ring_nf
    have hLOfun : LO = LR2 + (-(2 / nn)) * (2 * S * LS + 2 * sg) := by
      have hcomb := lapl_comb_p (g := G t) (u := fun y : M => rmNormSq (G t) y)
        (v := fun y : M => (scalAt (G t) y) ^ 2) (w := fun _ : M => (0 : ℝ))
        hrm hsqfun contMDiff_const (-(2 / nn)) 0 x
      have hfun1 : rmoNormSq (G t)
          = fun y : M => rmNormSq (G t) y - 2 * (scalAt (G t) y) ^ 2 / nn := by
        funext y; rw [Gest.rmoNormSq_eq, hnn]
      have hfun2 : (fun y : M => rmNormSq (G t) y - 2 * (scalAt (G t) y) ^ 2 / nn)
          = fun y : M => rmNormSq (G t) y + (-(2 / nn)) * (scalAt (G t) y) ^ 2 - 0 * 0 := by
        funext y; ring
      rw [hLO, hfun1, hfun2, hcomb, Gest.lapl_sq (g := G t) hsc x]
      rw [show (fun y : M => scalAt (G t) y) = scalAt (G t) from rfl,
        show (fun y : M => rmNormSq (G t) y) = rmNormSq (G t) from rfl]
      ring
    have hLσO : laplAt (G t) (fun y : M => (scalAt (G t) y + K₀) * rmoNormSq (G t) y) x
        = σ * LO + O * LS + 2 * X := by
      have hh := Gest.lapl_mul (g := G t) (u := fun y : M => scalAt (G t) y + K₀)
        (v := fun y : M => rmoNormSq (G t) y) hσfun hofun x
      rw [hh, hLsig]
    have hLσ3 : laplAt (G t) (fun y : M => (scalAt (G t) y + K₀) ^ 3) x
        = 3 * σ ^ 2 * LS + 6 * σ * sg := by
      have hh := Gest.lapl_cube (g := G t) (u := fun y : M => scalAt (G t) y + K₀) hσfun x
      rw [hh, hLsig, hLgradσ]
      try ring
    have hLaunch : laplAt (G t) (Ψ t) x
        = LA + N * (σ * LO + O * LS + 2 * X) - η' * (3 * σ ^ 2 * LS + 6 * σ * sg) := by
      have hcomb := lapl_comb_p (g := G t) (u := fun y : M => dRmNormSq (G t) y)
        (v := fun y : M => (scalAt (G t) y + K₀) * rmoNormSq (G t) y)
        (w := fun y : M => (scalAt (G t) y + K₀) ^ 3) hud (hσfun.mul hofun) (hσfun.pow 3) N η' x
      have hfun : Ψ t = fun y : M => dRmNormSq (G t) y
          + N * ((scalAt (G t) y + K₀) * rmoNormSq (G t) y)
          - η' * (scalAt (G t) y + K₀) ^ 3 := rfl
      rw [hfun, hcomb, hLA, hLσO, hLσ3]
    -- ## Pointwise inputs from the contracts.
    have hAeq : A = Ad + 2 * sg / nn := by
      show dRmNormSq (G t) x = drmoNormSq (G t) x + 2 * gradSq (G t) (scalAt (G t)) x / nn
      linarith [Gest.drmoNormSq_eq (G t) x]
    have hA0 : 0 ≤ A := Gest.dRmNormSq_nonneg (G t) x
    have hO0' : 0 ≤ O := hO0 t ht x
    have hσ1' : 1 ≤ σ := hσ1 t ht x
    have hσ0 : 0 ≤ σ := by linarith
    have hsg0 : 0 ≤ sg := by
      show 0 ≤ gradSq (G t) (scalAt (G t)) x
      rw [gradSq]
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hAd_le_A : Ad ≤ A := by
      show Ad ≤ A
      rw [hAeq]
      exact le_add_of_nonneg_right (div_nonneg (by linarith only [hsg0]) hnnpos.le)
    have hbkK : sg ≤ K * Ad := hsgF t ht x
    have hA_le_Am : A ≤ Am * Ad := by
      have h4 := mul_le_mul_of_nonneg_left hbkK (show (0:ℝ) ≤ 2 / nn by positivity)
      have h1 : 2 * sg / nn ≤ 2 * (K * Ad) / nn := by
        calc 2 * sg / nn = (2 / nn) * sg := by ring
          _ ≤ (2 / nn) * (K * Ad) := h4
          _ = 2 * (K * Ad) / nn := by ring
      rw [hAeq, hAmdef]
      have h1' : 2 * sg / nn ≤ 2 * K / nn * Ad := by
        calc 2 * sg / nn ≤ 2 * (K * Ad) / nn := h1
          _ = 2 * K / nn * Ad := by ring
      nlinarith only [h1']
    have hric2S : S ^ 2 ≤ (Module.finrank ℝ E : ℝ) * ric2 := hS2ric t ht x
    have hric2le : ric2 ≤ (Module.finrank ℝ E : ℝ) * R2 := hric t ht x
    have hric20 : 0 ≤ ric2 := by
      have h2 : (0:ℝ) < (Module.finrank ℝ E : ℝ) := hnRpos
      nlinarith only [hric2S, sq_nonneg S, h2]
    have hOg : og ≤ 4 * O * Ad := hogF t ht x
    have hr_le' : Real.sqrt R2 ≤ c * σ := by
      have h := hr_le t ht x
      have h2 : c * (scalAt (G t) x + K₀) = c * σ := by rw [hσ, hS]
      rw [h2] at h
      exact h
    have hR20 : 0 ≤ R2 := Gest.rmNormSq_nonneg (G t) x
    have hsqrtR20 : 0 ≤ Real.sqrt R2 := Real.sqrt_nonneg _
    have hR2sq : R2 = (Real.sqrt R2) ^ 2 := by rw [Real.sq_sqrt hR20]
    have hσR2 : R2 ≤ (c * σ) ^ 2 := by
      rw [hR2sq]; exact pow_le_pow_left₀ hsqrtR20 hr_le' 2
    have hsqrtO : Real.sqrt O ≤ δ * Real.sqrt R2 + Cδ := hsqrt_O t ht x
    have hO_le : O ≤ 2 * δ ^ 2 * R2 + 2 * Cδ ^ 2 := by
      have h2 : O = (Real.sqrt O) ^ 2 := by rw [Real.sq_sqrt hO0']
      have h5 := pow_le_pow_left₀ (Real.sqrt_nonneg O) hsqrtO 2
      have h6 : (δ * Real.sqrt R2 + Cδ) ^ 2
          = δ ^ 2 * R2 + 2 * (δ * Real.sqrt R2) * Cδ + Cδ ^ 2 := by
        nlinarith only [hR2sq]
      have h7 : 2 * (δ * Real.sqrt R2) * Cδ ≤ δ ^ 2 * R2 + Cδ ^ 2 := by
        nlinarith only [sq_nonneg (δ * Real.sqrt R2 - Cδ), hR2sq]
      rw [h2]
      calc (Real.sqrt O) ^ 2 ≤ (δ * Real.sqrt R2 + Cδ) ^ 2 := h5
        _ = δ ^ 2 * R2 + 2 * (δ * Real.sqrt R2) * Cδ + Cδ ^ 2 := h6
        _ ≤ δ ^ 2 * R2 + (δ ^ 2 * R2 + Cδ ^ 2) + Cδ ^ 2 := by linarith only [h7]
        _ = 2 * δ ^ 2 * R2 + 2 * Cδ ^ 2 := by ring
    have hS2K : σ ^ 2 / 2 - K₀ ^ 2 ≤ S ^ 2 := by
      have h : σ = S + K₀ := hσ
      nlinarith only [hσ, sq_nonneg (S - K₀), sq_nonneg S]
    have hΨA : A ≤ max (Ψ t x) 0 + η' * σ ^ 3 := by
      have hno : 0 ≤ N * (σ * O) := mul_nonneg hNpos.le (mul_nonneg hσ0 hO0')
      show A ≤ max (dRmNormSq (G t) x + N * ((scalAt (G t) x + K₀) * rmoNormSq (G t) x)
          - η' * (scalAt (G t) x + K₀) ^ 3) 0 + η' * σ ^ 3
      have h3 := le_max_left (dRmNormSq (G t) x
        + N * ((scalAt (G t) x + K₀) * rmoNormSq (G t) x)
        - η' * (scalAt (G t) x + K₀) ^ 3) 0
      have hXdef : dRmNormSq (G t) x + N * ((scalAt (G t) x + K₀) * rmoNormSq (G t) x)
          - η' * (scalAt (G t) x + K₀) ^ 3 = A + N * (σ * O) - η' * σ ^ 3 := by ring
      linarith only [hno, h3, hXdef]
    -- ## The pointwise inequality.
    have hDS_LS : DS - LS = 2 * ric2 := by rw [hDS]; ring
    have hDOLO : DO - LO ≤ -2 * Ad + 2 * c₂' * O * Real.sqrt R2 := by
      have h1 : DO - LO = -2 * A + 2 * qp - 2 * (2 * S * DS) / nn
          + (2 / nn) * (2 * S * LS + 2 * sg) := by
        rw [hDO, hLOfun]; ring
      rw [h1]
      have h2 : -2 * A + 2 * qp - 2 * (2 * S * DS) / nn + (2 / nn) * (2 * S * LS + 2 * sg)
          = -2 * Ad + 2 * (qp - 4 * S * ric2 / nn) := by
        rw [hAeq, hDS]; ring
      rw [h2]
      have h3 : qp - 4 * S * ric2 / nn ≤ c₂' * O * Real.sqrt R2 := by
        have h := hqpF t ht x
        convert h using 1 <;> ring
      linarith only [h3]
    have hσDOLO : σ * (DO - LO) ≤ -2 * σ * Ad + 2 * c₂' * c * σ ^ 2 * O := by
      calc σ * (DO - LO) ≤ σ * (-2 * Ad + 2 * c₂' * O * Real.sqrt R2) :=
            mul_le_mul_of_nonneg_left hDOLO hσ0
        _ = -2 * σ * Ad + 2 * c₂' * σ * O * Real.sqrt R2 := by ring
        _ ≤ -2 * σ * Ad + 2 * c₂' * σ * O * (c * σ) := by
            have h4 : 0 ≤ 2 * c₂' * σ * O := by positivity
            have h5 := mul_le_mul_of_nonneg_left hr_le' h4
            linarith only [h5]
        _ = -2 * σ * Ad + 2 * c₂' * c * σ ^ 2 * O := by ring
    have hσAd : -2 * σ * Ad ≤ -(2 / Am) * σ * A := by
      have h1 : A / Am ≤ Ad := by
        rw [div_le_iff₀ hAmpos]
        linarith only [hA_le_Am]
      have h4 : 0 ≤ 2 * σ := by linarith only [hσ0]
      have h5 := mul_le_mul_of_nonneg_left h1 h4
      have h6 : 2 * σ * (A / Am) = (2 / Am) * σ * A := by field_simp
      linarith only [h5, h6]
    have hOric : O * (DS - LS) ≤ 2 * (Module.finrank ℝ E : ℝ) * c ^ 2 * σ ^ 2 * O := by
      have h0 : O * (DS - LS) = 2 * O * ric2 := by rw [hDS_LS]; ring
      rw [h0]
      calc 2 * O * ric2 ≤ 2 * O * ((Module.finrank ℝ E : ℝ) * R2) :=
            mul_le_mul_of_nonneg_left hric2le (by positivity)
        _ ≤ 2 * O * ((Module.finrank ℝ E : ℝ) * (c * σ) ^ 2) := by
            have h2 : 0 ≤ 2 * O * (Module.finrank ℝ E : ℝ) := by positivity
            have h3 := mul_le_mul_of_nonneg_left hσR2 h2
            linarith only [h3]
        _ = 2 * (Module.finrank ℝ E : ℝ) * c ^ 2 * σ ^ 2 * O := by ring
    have hXle : -(2 * X) ≤ 4 * Real.sqrt K * Real.sqrt O * max Ad 0 := by
      have hCS := Gest.sum_mul_abs_le
        (fun i => mvfderiv I (fun y : M => scalAt (G t) y + K₀) x (onFrame (G t) x i))
        (fun i => mvfderiv I (fun y : M => rmoNormSq (G t) y) x (onFrame (G t) x i))
      have hXabs : |X| ≤ Real.sqrt sg * Real.sqrt og := by
        have h1 : |X| ≤ Real.sqrt (gradSq (G t) (fun y : M => scalAt (G t) y + K₀) x)
            * Real.sqrt (gradSq (G t) (rmoNormSq (G t)) x) := by
          simpa only [hX, gradSq] using hCS
        rw [hLgradσ] at h1
        exact h1
      have h2 : Real.sqrt sg ≤ Real.sqrt K * Real.sqrt (max Ad 0) := by
        rw [← Real.sqrt_mul hK0]
        apply Real.sqrt_le_sqrt
        calc sg ≤ K * Ad := hbkK
          _ ≤ K * max Ad 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hK0
      have h3 : Real.sqrt og ≤ 2 * Real.sqrt O * Real.sqrt (max Ad 0) := by
        have hAdp : 0 ≤ max Ad 0 := le_max_right _ _
        have h4 : og ≤ 4 * O * max Ad 0 := by
          calc og ≤ 4 * O * Ad := hOg
            _ ≤ 4 * O * max Ad 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
        calc Real.sqrt og ≤ Real.sqrt (4 * O * max Ad 0) := Real.sqrt_le_sqrt h4
          _ = Real.sqrt (4 * O) * Real.sqrt (max Ad 0) := by rw [Real.sqrt_mul (by positivity)]
          _ = (Real.sqrt 4 * Real.sqrt O) * Real.sqrt (max Ad 0) := by
              rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
          _ = 2 * Real.sqrt O * Real.sqrt (max Ad 0) := by
              rw [show Real.sqrt 4 = 2 by
                rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      have h5 : Real.sqrt sg * Real.sqrt og
          ≤ (Real.sqrt K * Real.sqrt (max Ad 0)) * (2 * Real.sqrt O * Real.sqrt (max Ad 0)) :=
        mul_le_mul h2 h3 (Real.sqrt_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      have h6 : (Real.sqrt K * Real.sqrt (max Ad 0)) * (2 * Real.sqrt O * Real.sqrt (max Ad 0))
          = 2 * Real.sqrt K * Real.sqrt O * (max Ad 0) := by
        have hs : Real.sqrt (max Ad 0) * Real.sqrt (max Ad 0) = max Ad 0 := by
          rw [← sq, Real.sq_sqrt (le_max_right Ad 0)]
        rw [show (Real.sqrt K * Real.sqrt (max Ad 0)) * (2 * Real.sqrt O * Real.sqrt (max Ad 0))
            = 2 * Real.sqrt K * Real.sqrt O
              * (Real.sqrt (max Ad 0) * Real.sqrt (max Ad 0)) by ring, hs]
      have h7 : -(2 * X) ≤ 2 * (Real.sqrt sg * Real.sqrt og) := by
        have h8 := mul_le_mul_of_nonneg_left (neg_le_abs X) (by norm_num : (0:ℝ) ≤ 2)
        linarith only [h8, hXabs]
      linarith only [h5, h6, h7]
    have hXb : -(2 * X) ≤ (4 * Real.sqrt K * δ * c) * σ * A + (4 * Real.sqrt K * Cδ) * A := by
      have hAdp_le_A : max Ad 0 ≤ A := max_le hAd_le_A hA0
      have hsqrtK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
      have h1 : Real.sqrt O * max Ad 0 ≤ (δ * c * σ + Cδ) * A := by
        have h2 : Real.sqrt O * max Ad 0 ≤ (δ * Real.sqrt R2 + Cδ) * A :=
          mul_le_mul hsqrtO hAdp_le_A (le_max_right Ad 0)
            (le_trans (Real.sqrt_nonneg O) hsqrtO)
        have h3 : δ * Real.sqrt R2 + Cδ ≤ δ * c * σ + Cδ := by
          have h4 : δ * Real.sqrt R2 ≤ δ * (c * σ) := mul_le_mul_of_nonneg_left hr_le' hδpos.le
          linarith only [h4]
        have h5 := mul_le_mul_of_nonneg_right h3 hA0
        linarith only [h2, h5]
      calc -(2 * X) ≤ 4 * Real.sqrt K * Real.sqrt O * max Ad 0 := hXle
        _ = 4 * Real.sqrt K * (Real.sqrt O * max Ad 0) := by ring
        _ ≤ 4 * Real.sqrt K * ((δ * c * σ + Cδ) * A) := by
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (4 * Real.sqrt K * δ * c) * σ * A + (4 * Real.sqrt K * Cδ) * A := by ring
    have hηric : -6 * η' * σ ^ 2 * ric2 ≤ -(6 * η' / (Module.finrank ℝ E : ℝ)) * σ ^ 2 * S ^ 2 := by
      have h1 : S ^ 2 / (Module.finrank ℝ E : ℝ) ≤ ric2 := by
        rw [div_le_iff₀ hnRpos]; linarith only [hric2S]
      have h4 : 0 ≤ 6 * η' * σ ^ 2 := by positivity
      have h5 := mul_le_mul_of_nonneg_left h1 h4
      have h6 : 6 * η' * σ ^ 2 * (S ^ 2 / (Module.finrank ℝ E : ℝ))
          = (6 * η' / (Module.finrank ℝ E : ℝ)) * σ ^ 2 * S ^ 2 := by field_simp
      linarith only [h5, h6]
    have hηsg : 6 * η' * σ * sg ≤ 6 * η' * K * σ * A := by
      have h1 : sg ≤ K * A := le_trans hbkK (mul_le_mul_of_nonneg_left hAd_le_A hK0)
      have h2 : 0 ≤ 6 * η' * σ := by positivity
      have h3 := mul_le_mul_of_nonneg_left h1 h2
      have h4 : 6 * η' * σ * (K * A) = 6 * η' * K * σ * A := by ring
      linarith only [h3, h4]
    have hDψ_sub : Dψ - (LA + N * (σ * LO + O * LS + 2 * X) - η' * (3 * σ ^ 2 * LS + 6 * σ * sg))
        = (DA - LA) + N * (σ * (DO - LO) + O * (DS - LS) - 2 * X)
          - η' * (3 * σ ^ 2 * (DS - LS) - 6 * σ * sg) := by
      rw [hDψ]; ring
    have hcombine : Dψ - laplAt (G t) (Ψ t) x
        ≤ σ * A * (c₁ * c + 6 * η' * K - 2 * N / Am + 4 * N * Real.sqrt K * δ * c)
          + (N * (2 * c₂' * c) + N * (2 * (Module.finrank ℝ E : ℝ) * c ^ 2)) * σ ^ 2 * O
          + (4 * N * Real.sqrt K * Cδ) * A
          - (6 * η' / (Module.finrank ℝ E : ℝ)) * σ ^ 2 * S ^ 2 := by
      have hDA_LA : DA - LA ≤ c₁ * c * σ * A := by
        have h2 : c₁ * Real.sqrt R2 * A ≤ c₁ * (c * σ) * A := by
          have h4 : 0 ≤ c₁ * A := mul_nonneg hc₁0 hA0
          calc c₁ * Real.sqrt R2 * A = (c₁ * A) * Real.sqrt R2 := by ring
            _ ≤ (c₁ * A) * (c * σ) := mul_le_mul_of_nonneg_left hr_le' h4
            _ = c₁ * (c * σ) * A := by ring
        linarith only [hDAle', h2]
      have hN1 := mul_le_mul_of_nonneg_left hσDOLO hNpos.le
      have hN2 := mul_le_mul_of_nonneg_left hOric hNpos.le
      have hN3 := mul_le_mul_of_nonneg_left hXb hNpos.le
      have hbr : η' * (3 * σ ^ 2 * (DS - LS) - 6 * σ * sg)
          = 6 * η' * σ ^ 2 * ric2 - 6 * η' * σ * sg := by rw [hDS_LS]; ring
      rw [hLaunch, hDψ_sub, hbr]
      have hσAdN : -2 * N * σ * Ad ≤ -(2 * N / Am) * σ * A := by
        have h7 : N * (-2 * σ * Ad) ≤ N * (-(2 / Am) * σ * A) :=
          mul_le_mul_of_nonneg_left hσAd hNpos.le
        have h8 : N * (-2 * σ * Ad) = -2 * N * σ * Ad := by ring
        have h9 : N * (-(2 / Am) * σ * A) = -(2 * N / Am) * σ * A := by ring
        linarith only [h7, h8, h9]
      have hdist : (DA - LA) + N * (σ * (DO - LO) + O * (DS - LS) - 2 * X)
            - (6 * η' * σ ^ 2 * ric2 - 6 * η' * σ * sg)
          = (DA - LA) + N * (σ * (DO - LO)) + N * (O * (DS - LS)) + N * (-(2 * X))
            - 6 * η' * σ ^ 2 * ric2 + 6 * η' * σ * sg := by ring
      rw [hdist]
      have hd1 : N * (-2 * σ * Ad + 2 * c₂' * c * σ ^ 2 * O)
          = -2 * N * σ * Ad + 2 * N * c₂' * c * σ ^ 2 * O := by ring
      have hd2 : N * (2 * (Module.finrank ℝ E : ℝ) * c ^ 2 * σ ^ 2 * O)
          = 2 * N * (Module.finrank ℝ E : ℝ) * c ^ 2 * σ ^ 2 * O := by ring
      have hd3 : N * ((4 * Real.sqrt K * δ * c) * σ * A + (4 * Real.sqrt K * Cδ) * A)
          = 4 * N * Real.sqrt K * δ * c * σ * A + 4 * N * Real.sqrt K * Cδ * A := by ring
      have hsum : (DA - LA) + N * (σ * (DO - LO)) + N * (O * (DS - LS)) + N * (-(2 * X))
            - 6 * η' * σ ^ 2 * ric2 + 6 * η' * σ * sg
          ≤ c₁ * c * σ * A + (-(2 * N / Am) * σ * A + 2 * N * c₂' * c * σ ^ 2 * O)
            + 2 * N * (Module.finrank ℝ E : ℝ) * c ^ 2 * σ ^ 2 * O
            + (4 * N * Real.sqrt K * δ * c * σ * A + 4 * N * Real.sqrt K * Cδ * A)
            - (6 * η' / (Module.finrank ℝ E : ℝ)) * σ ^ 2 * S ^ 2 + 6 * η' * K * σ * A := by
        rw [hd1] at hN1
        rw [hd2] at hN2
        rw [hd3] at hN3
        nlinarith only [hDA_LA, hN1, hN2, hN3, hσAdN, hηric, hηsg]
      have hgoal : c₁ * c * σ * A + (-(2 * N / Am) * σ * A + 2 * N * c₂' * c * σ ^ 2 * O)
            + 2 * N * (Module.finrank ℝ E : ℝ) * c ^ 2 * σ ^ 2 * O
            + (4 * N * Real.sqrt K * δ * c * σ * A + 4 * N * Real.sqrt K * Cδ * A)
            - (6 * η' / (Module.finrank ℝ E : ℝ)) * σ ^ 2 * S ^ 2 + 6 * η' * K * σ * A
          = σ * A * (c₁ * c + 6 * η' * K - 2 * N / Am + 4 * N * Real.sqrt K * δ * c)
            + (N * (2 * c₂' * c) + N * (2 * (Module.finrank ℝ E : ℝ) * c ^ 2)) * σ ^ 2 * O
            + (4 * N * Real.sqrt K * Cδ) * A
            - (6 * η' / (Module.finrank ℝ E : ℝ)) * σ ^ 2 * S ^ 2 := by
        ring
      linarith only [hsum, hgoal]
    have hcoef : c₁ * c + 6 * η' * K - 2 * N / Am + 4 * N * Real.sqrt K * δ * c ≤ -1 := by
      have hNAm : N / Am = c₁ * c + 6 * η' * K + 1 := by
        rw [hNdef]; field_simp
      have hQ : 4 * N * Real.sqrt K * δ * c = Q * δ := by rw [hQdef]; ring
      have h1 : 4 * N * Real.sqrt K * δ * c ≤ 1 := by rw [hQ]; exact hδ1
      have h2 : 0 ≤ c₁ * c := mul_nonneg hc₁0 hcpos.le
      have h3 : 0 ≤ 6 * η' * K := by positivity
      have h4 : 2 * N / Am = 2 * (c₁ * c + 6 * η' * K + 1) := by
        rw [← hNAm]; ring
      linarith only [h1, h2, h3, h4]
    have hstep1 : Dψ - laplAt (G t) (Ψ t) x
        ≤ -σ * A + (N * (2 * c₂' * c) + N * (2 * (Module.finrank ℝ E : ℝ) * c ^ 2)) * σ ^ 2 * O
          + (4 * N * Real.sqrt K * Cδ) * A - (6 * η' / (Module.finrank ℝ E : ℝ)) * σ ^ 2 * S ^ 2 := by
      have h1 : σ * A * (c₁ * c + 6 * η' * K - 2 * N / Am + 4 * N * Real.sqrt K * δ * c) ≤ -σ * A := by
        have h2 : 0 ≤ σ * A := mul_nonneg hσ0 hA0
        nlinarith only [hcoef, h2]
      linarith only [hcombine, h1]
    have hc₅ : N * (2 * c₂' * c) + N * (2 * (Module.finrank ℝ E : ℝ) * c ^ 2)
        = N * c₅ := by rw [hc₅def]; ring
    have hstep2 : (N * c₅) * σ ^ 2 * O
        ≤ (2 * N * c₅ * δ ^ 2 * c ^ 2) * σ ^ 4 + (2 * N * c₅ * Cδ ^ 2) * σ ^ 2 := by
      have h1 : σ ^ 2 * O ≤ σ ^ 2 * (2 * δ ^ 2 * R2 + 2 * Cδ ^ 2) :=
        mul_le_mul_of_nonneg_left hO_le (sq_nonneg σ)
      have h2 : σ ^ 2 * (2 * δ ^ 2 * R2 + 2 * Cδ ^ 2)
          ≤ σ ^ 2 * (2 * δ ^ 2 * (c * σ) ^ 2 + 2 * Cδ ^ 2) := by
        have h3 : 0 ≤ 2 * δ ^ 2 * σ ^ 2 := by positivity
        have h4 := mul_le_mul_of_nonneg_left hσR2 h3
        have h5 : 2 * δ ^ 2 * σ ^ 2 * R2 = σ ^ 2 * (2 * δ ^ 2 * R2) := by ring
        have h6 : 2 * δ ^ 2 * σ ^ 2 * (c * σ) ^ 2 = σ ^ 2 * (2 * δ ^ 2 * (c * σ) ^ 2) := by ring
        linarith only [h4, h5, h6]
      have h5 : N * c₅ * (σ ^ 2 * (2 * δ ^ 2 * (c * σ) ^ 2 + 2 * Cδ ^ 2))
          = (2 * N * c₅ * δ ^ 2 * c ^ 2) * σ ^ 4 + (2 * N * c₅ * Cδ ^ 2) * σ ^ 2 := by
        ring
      have h6 : 0 ≤ N * c₅ := mul_nonneg hNpos.le hc₅0
      have h7 : N * c₅ * (σ ^ 2 * O)
          ≤ N * c₅ * (σ ^ 2 * (2 * δ ^ 2 * (c * σ) ^ 2 + 2 * Cδ ^ 2)) :=
        mul_le_mul_of_nonneg_left (le_trans h1 h2) h6
      have h8 : N * c₅ * (σ ^ 2 * O) = (N * c₅) * σ ^ 2 * O := by ring
      rw [h5, h8] at h7
      exact h7
    have hstep3 : (2 * N * c₅ * δ ^ 2 * c ^ 2) * σ ^ 4 - (6 * η' / (Module.finrank ℝ E : ℝ)) * σ ^ 2 * S ^ 2
        ≤ -(3 * η' / (2 * (Module.finrank ℝ E : ℝ))) * σ ^ 4
          + (6 * η' / (Module.finrank ℝ E : ℝ)) * K₀ ^ 2 * σ ^ 2 := by
      have h1 : (6 * η' / (Module.finrank ℝ E : ℝ)) * σ ^ 2 * (σ ^ 2 / 2 - K₀ ^ 2)
          ≤ (6 * η' / (Module.finrank ℝ E : ℝ)) * σ ^ 2 * S ^ 2 := by
        have h2 : 0 ≤ (6 * η' / (Module.finrank ℝ E : ℝ)) * σ ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left hS2K h2
      have h3 : 2 * N * c₅ * δ ^ 2 * c ^ 2 * σ ^ 4 ≤ (3 * η' / (2 * (Module.finrank ℝ E : ℝ))) * σ ^ 4 := by
        have h4 : 0 ≤ σ ^ 4 := by positivity
        have h5 := mul_le_mul_of_nonneg_right hδ2 h4
        have h6 : 2 * N * c₅ * c ^ 2 * δ ^ 2 * σ ^ 4 = 2 * N * c₅ * δ ^ 2 * c ^ 2 * σ ^ 4 := by ring
        linarith only [h5, h6]
      have h7 : 0 ≤ (2 * N * c₅ * Cδ ^ 2) * σ ^ 2 := by positivity
      have hkey : 3 * η' / (Module.finrank ℝ E : ℝ)
          = 2 * (3 * η' / (2 * (Module.finrank ℝ E : ℝ))) := by field_simp
      have h8 : 0 ≤ 3 * η' / (2 * (Module.finrank ℝ E : ℝ)) * σ ^ 4 := by positivity
      ring_nf at h1 h3 hkey ⊢
      linarith only [h1, h3, hkey, h8]
    have hstep4 : -σ * A + (4 * N * Real.sqrt K * Cδ) * A
        ≤ L₁ * max (Ψ t x) 0 + L₁ * η' * σ ^ 3 := by
      have h1 : -σ * A + (4 * N * Real.sqrt K * Cδ) * A = (L - σ) * A := by rw [hLdef]; ring
      have h2 : (L - σ) * A ≤ L₁ * A := by
        have h3 : L - σ ≤ L₁ := le_trans (by linarith [hσ1']) hL₁val
        exact mul_le_mul_of_nonneg_right h3 hA0
      have h4 : L₁ * A ≤ L₁ * (max (Ψ t x) 0 + η' * σ ^ 3) :=
        mul_le_mul_of_nonneg_left hΨA hL₁0
      calc -σ * A + (4 * N * Real.sqrt K * Cδ) * A = (L - σ) * A := h1
        _ ≤ L₁ * A := h2
        _ ≤ L₁ * (max (Ψ t x) 0 + η' * σ ^ 3) := h4
        _ = L₁ * max (Ψ t x) 0 + L₁ * η' * σ ^ 3 := by ring
    have hstep5 : L₁ * η' * σ ^ 3 + (2 * N * c₅ * Cδ ^ 2) * σ ^ 2
        - (3 * η' / (2 * (Module.finrank ℝ E : ℝ))) * σ ^ 4
        + (6 * η' / (Module.finrank ℝ E : ℝ)) * K₀ ^ 2 * σ ^ 2 ≤ C₂ := by
      have h1 : 2 * N * c₅ * Cδ ^ 2 + (6 * η' / (Module.finrank ℝ E : ℝ)) * K₀ ^ 2 = M₀ := by
        rw [hM₀def]
      have h2 := hC₂ σ hσ1'
      have h3 : L₁ * η' * σ ^ 3 + (2 * N * c₅ * Cδ ^ 2) * σ ^ 2
          - (3 * η' / (2 * (Module.finrank ℝ E : ℝ))) * σ ^ 4
          + (6 * η' / (Module.finrank ℝ E : ℝ)) * K₀ ^ 2 * σ ^ 2
          = L₁ * η' * σ ^ 3 + M₀ * σ ^ 2 - (3 * η' / (2 * (Module.finrank ℝ E : ℝ))) * σ ^ 4 := by
        rw [← h1]; ring
      rw [h3]
      exact h2
    -- assemble
    have hbig : Dψ - laplAt (G t) (Ψ t) x ≤ C₁ * max (Ψ t x) 0 + C₂ := by
      have hA := hstep1
      have hB := hstep2
      have hC := hstep3
      have hD := hstep4
      have hE := hstep5
      rw [hc₅] at hA
      rw [hC₁def]
      have h9 : 0 ≤ (2 * N * c₅ * Cδ ^ 2) * σ ^ 2 := by positivity
      ring_nf at hA hB hC hD hE h9 ⊢
      linarith only [hA, hB, hC, hD, hE, h9]
    linarith only [hbig]
  -- ## The maximum principle.
  let d : ℝ → M → ℝ := fun t x =>
    if ht : t ∈ Ico 0 T then Classical.choose (hpoint t ht x) else 0
  have hd : ∀ t ∈ Ico 0 T, ∀ x : M,
      HasDerivWithinAt (fun s => Ψ s x) (d t x) (Ico 0 T) t ∧
      d t x ≤ laplAt (G t) (Ψ t) x + C₁ * max (Ψ t x) 0 + C₂ := by
    intro t ht x
    have hspec := Classical.choose_spec (hpoint t ht x)
    rw [show d t x = Classical.choose (hpoint t ht x) from dif_pos ht]
    exact hspec
  -- ## The initial bound (continuity on the compact manifold `M`).
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x : M, Ψ 0 x ≤ B := by
    have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_refl 0, hT⟩
    have hcont : Continuous (fun x : M => Ψ 0 x) := (cmd_slice hJΨ h0).continuous
    obtain ⟨B, hB⟩ := ((isCompact_univ (X := M)).image hcont).bddAbove
    exact ⟨B, fun x => hB ⟨x, mem_univ x, rfl⟩⟩
  have hSMPapp : ∀ t ∈ Ico 0 T, ∀ x : M,
      Ψ t x ≤ Real.exp (C₁ * t) * (max B 0 + C₂ * t) :=
    hSMP G T Ψ d C₁ C₂ B hflow.1 hC₁0 hC₂0 hJΨ hd hB
  -- ## Conclusion.
  set C₃ : ℝ := Real.exp (C₁ * T) * (max B 0 + C₂ * T) with hC₃def
  refine ⟨η * |K₀| ^ 3 + C₃, ?_⟩
  intro t ht x
  have hTS : t ≤ T := ht.2.le
  have hΨC : Ψ t x ≤ C₃ := by
    have h1 := hSMPapp t ht x
    have hexp : Real.exp (C₁ * t) ≤ Real.exp (C₁ * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hTS hC₁0)
    have hlin : max B 0 + C₂ * t ≤ max B 0 + C₂ * T := by
      have h2 : C₂ * t ≤ C₂ * T := mul_le_mul_of_nonneg_left hTS hC₂0
      linarith
    have hnn : 0 ≤ max B 0 + C₂ * t := by
      have h3 : 0 ≤ max B 0 := le_max_right B 0
      have h4 : 0 ≤ C₂ * t := mul_nonneg hC₂0 ht.1
      linarith
    calc Ψ t x ≤ Real.exp (C₁ * t) * (max B 0 + C₂ * t) := h1
      _ ≤ Real.exp (C₁ * T) * (max B 0 + C₂ * T) :=
          mul_le_mul hexp hlin hnn (Real.exp_nonneg _)
      _ = C₃ := hC₃def.symm
  have hA_le : dRmNormSq (G t) x ≤ Ψ t x + η' * (scalAt (G t) x + K₀) ^ 3 := by
    have hno : 0 ≤ N * ((scalAt (G t) x + K₀) * rmoNormSq (G t) x) := by
      have h1 : 0 ≤ scalAt (G t) x + K₀ := by linarith [hσ1 t ht x]
      have h2 : 0 ≤ rmoNormSq (G t) x := hO0 t ht x
      exact mul_nonneg hNpos.le (mul_nonneg h1 h2)
    show dRmNormSq (G t) x
      ≤ (dRmNormSq (G t) x + N * ((scalAt (G t) x + K₀) * rmoNormSq (G t) x)
          - η' * (scalAt (G t) x + K₀) ^ 3) + η' * (scalAt (G t) x + K₀) ^ 3
    linarith
  have hσ3 : (scalAt (G t) x + K₀) ^ 3
      ≤ 8 * |scalAt (G t) x| ^ 3 + 8 * |K₀| ^ 3 := by
    have hσpos : 0 ≤ scalAt (G t) x + K₀ := by linarith [hσ1 t ht x]
    have hs : scalAt (G t) x + K₀ ≤ |scalAt (G t) x| + |K₀| := by
      have h1 := le_abs_self (scalAt (G t) x)
      have h2 := le_abs_self K₀
      linarith
    have h1 : (scalAt (G t) x + K₀) ^ 3 ≤ (|scalAt (G t) x| + |K₀|) ^ 3 :=
      pow_le_pow_left₀ hσpos hs 3
    have h2 := add_cube_le_eight |scalAt (G t) x| |K₀| (abs_nonneg _) (abs_nonneg _)
    linarith
  have hmain : dRmNormSq (G t) x
      ≤ Ψ t x + η' * (8 * |scalAt (G t) x| ^ 3 + 8 * |K₀| ^ 3) := by
    have := mul_le_mul_of_nonneg_left hσ3 hη'pos.le
    linarith
  have hform : Ψ t x + η' * (8 * |scalAt (G t) x| ^ 3 + 8 * |K₀| ^ 3)
      = (Ψ t x + η * |K₀| ^ 3) + η * |scalAt (G t) x| ^ 3 := by
    rw [hη'ex]; ring
  calc dRmNormSq (G t) x ≤ Ψ t x + η' * (8 * |scalAt (G t) x| ^ 3 + 8 * |K₀| ^ 3) := hmain
    _ = (Ψ t x + η * |K₀| ^ 3) + η * |scalAt (G t) x| ^ 3 := hform
    _ ≤ (C₃ + η * |K₀| ^ 3) + η * |scalAt (G t) x| ^ 3 := by linarith [hΨC]
    _ = η * |scalAt (G t) x| ^ 3 + (η * |K₀| ^ 3 + C₃) := by ring

end Work.Diff.GE
