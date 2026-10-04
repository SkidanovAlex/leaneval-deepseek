import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.sum_bilin_eq_of_isonframe
import Submission.Work.Diff.STE.B3.hasFDerivWithinAt_coord_pt
import Submission.Work.Diff.STE.B3.dens_transition
import Submission.Work.Diff.STE.B3.Rstar_apply
import Submission.Work.Diff.STE.B3.BPairSmooth
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.B3.integrable_of_continuousOn_of_bound
import Submission.Work.Diff.STE.B3.integrableOn_Cpair_term
import Submission.Work.Diff.STE.B3.integrableOn_Npair_term
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.EXT.sum_inner_smul_eq_self_of_isONFrame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the adjunction `BPair (Rstar i u) k = CPair i u (R i k)`

This is the crux of Layer B3 (see `DESIGN.md`, SESSION 7): the reconstruction `Rstar i` is the
adjoint of the component map `R i` for the composite pairing of the global Galerkin scheme.

The proof is the *chart transfer*: for every chart `j`, the `j`-th component of `BPair` is rewritten
in the chart `j` and then transported to the chart `i` by the flat transition
`T y = coord j (pt i y)` (change of variables, with the Jacobian identity `dens_transition`); the
sum over `j` is then collapsed with the normalisation `Σ_j ζ_j ^ 2 = 1`.  The right-hand side is the
same integral read in the chart `i`.

The junk of `extChartAt`/its inverse off `source`/`target` is harmless: `ψ j = χ j · ζ j ∘ pt j`
together with `hχtsup` shows that wherever `ψ j ≠ 0` the chart `j` is genuine, so every integrand
is supported where all the charts involved are genuine (see `B3/BPairDefs.lean`).
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter MeasureTheory

namespace Work.Diff.STE.B3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]

section Algebra

variable {g₀ : Submission.Diff.SMet I M} {p : M}

/-- **The orthonormal expansion of a bilinear form.**  If `e` is a `g₀`-orthonormal frame of `TₚM`
then every bilinear form is the sum of its matrix entries against the coefficient functionals. -/
lemma bilin_eq_sum_of_isONFrame {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : Submission.Diff.IsONFrame g₀ p e)
    (B : TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) (X Y : TangentSpace I p) :
    B X Y = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      g₀.inner p X (e a) * g₀.inner p Y (e b) * B (e a) (e b) := by
  have hX : X = ∑ a : Fin (Module.finrank ℝ E), g₀.inner p X (e a) • e a :=
    (Work.EXT.sum_inner_smul_eq_self_of_isONFrame g₀ p e hON X).symm
  have hY : ∀ Z : TangentSpace I p, Z = ∑ b : Fin (Module.finrank ℝ E),
      g₀.inner p Z (e b) • e b := fun Z =>
    (Work.EXT.sum_inner_smul_eq_self_of_isONFrame g₀ p e hON Z).symm
  have hYX : (B X) Y = ∑ b : Fin (Module.finrank ℝ E),
      g₀.inner p Y (e b) * (B X) (e b) := by
    conv_lhs => rw [hY Y]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  have hBX : B X = ∑ a : Fin (Module.finrank ℝ E), g₀.inner p X (e a) • B (e a) := by
    conv_lhs => rw [hX]
    rw [map_sum]
    simp only [map_smul]
  rw [hYX, hBX]
  simp only [sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_congr rfl fun b _ => by ring

/-- Collapsing a double sum against an orthonormal frame: the two coefficient functionals see only
the diagonal term. -/
lemma sum_orth_of_isONFrame {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : Submission.Diff.IsONFrame g₀ p e)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (a b : Fin (Module.finrank ℝ E)) :
    (∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
        F a' b' * g₀.inner p (e a) (e a') * g₀.inner p (e b) (e b')) = F a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · rw [hON a a, hON b b]
      simp
    · intro b' _ hb'
      have h : g₀.inner p (e b) (e b') = 0 := by
        rw [hON b b']
        simp [Ne.symm hb']
      simp [h]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · intro a' _ ha'
    have h : g₀.inner p (e a) (e a') = 0 := by
      rw [hON a a']
      simp [Ne.symm ha']
    simp [h]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

end Algebra

section Pointwise

variable {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
variable (D : B3Data (I := I) (M := M) ι₀ g₀)

/-- **The intrinsic contraction in an orthonormal frame.**  At a point `p` of the chart source of
`x₀ i` where the frame `e i` is `g₀`-orthonormal, `Phi D i u k p` is the coefficient
`ζ i p · χ i (coord i p) · (√(dens i (coord i p)))⁻¹` times the contraction of `u` against `k` in the
frame `e i`. -/
lemma Phi_apply_frame {i : ι₀}
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Bil (I := I) (M := M)) {p : M}
    (hON : IsONFrame g₀ p (fun a => D.e i a p))
    (hsrc : p ∈ (extChartAt I (D.x₀ i)).source) :
    Phi D i u k p
      = (D.ζ i p * D.χ i (coord (I := I) (D.x₀ i) p)
          * (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p)))⁻¹)
        * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            u a b (coord (I := I) (D.x₀ i) p) * k p (D.e i a p) (D.e i b p)) := by
  have hcoeff : ∀ a b : Fin (Module.finrank ℝ E),
      D.Rstar i u p (D.e i a p) (D.e i b p)
        = (D.ζ i p * D.χ i (coord (I := I) (D.x₀ i) p)
            * (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) p)))⁻¹)
          * u a b (coord (I := I) (D.x₀ i) p) := by
    intro a b
    rw [Rstar_apply D i u p (D.e i a p) (D.e i b p)]
    congr 1
    exact sum_orth_of_isONFrame (g₀ := g₀) (p := p) hON
      (fun a' b' => u a' b' (coord (I := I) (D.x₀ i) p)) a b
  simp only [Phi, hcoeff]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- **Frame independence for `Phi`.**  In any two orthonormal frames at `p`, the full contraction
of `Rstar i u p` against `k p` in the pattern `(a,b,a,b)` is the same; in particular `Phi` (which is
defined in the frame `e i`) equals the contraction in the frame `e j`. -/
lemma Phi_eq_sum_other_frame {i j : ι₀}
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Bil (I := I) (M := M)) {p : M}
    (hONj : IsONFrame g₀ p (fun a => D.e j a p))
    (hONi : IsONFrame g₀ p (fun a => D.e i a p)) :
    Phi D i u k p
      = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          D.Rstar i u p (D.e j a p) (D.e j b p) * k p (D.e j a p) (D.e j b p) := by
  simp only [Phi]
  exact (sum_bilin_eq_of_isonframe g₀ p (fun a => D.e j a p) (fun a => D.e i a p) hONj hONi
    (D.Rstar i u p) (k p)).symm

/-- `s * s * s⁻¹ = s`. -/
lemma sq_mul_inv (s : ℝ) : s * s * s⁻¹ = s := by
  rcases eq_or_ne s 0 with h | h
  · rw [h]; ring
  · rw [mul_assoc, mul_inv_cancel₀ h, mul_one]

/-- `d * (√d)⁻¹ = √d` for every real `d`. -/
lemma mul_inv_sqrt_eq_sqrt (d : ℝ) : d * (Real.sqrt d)⁻¹ = Real.sqrt d := by
  rcases eq_or_ne (Real.sqrt d) 0 with h | h
  · rw [h, inv_zero, mul_zero]
  · have hd : 0 ≤ d :=
      le_of_lt (Real.sqrt_pos.mp (lt_of_le_of_ne (Real.sqrt_nonneg d) (Ne.symm h)))
    nth_rewrite 1 [show d = Real.sqrt d * Real.sqrt d from by
      rw [← sq]; exact (Real.sq_sqrt hd).symm]
    exact sq_mul_inv (Real.sqrt d)

/-- `(ψ √d X) * (ψ √d Y) = ψ^2 * d * (X * Y)` for `d ≥ 0`. -/
lemma mul_sqrt_sqrt_fac {d : ℝ} (hd : 0 ≤ d) (ψ X Y : ℝ) :
    (ψ * Real.sqrt d * X) * (ψ * Real.sqrt d * Y) = ψ ^ 2 * d * (X * Y) := by
  conv_rhs =>
    rw [show d = (Real.sqrt d) ^ 2 from (Real.sq_sqrt hd).symm]
  ring

variable {i : ι₀}

/-- The volume density is nonnegative. -/
lemma dens_nonneg' (z : Fin (Module.finrank ℝ E) → ℝ) : 0 ≤ D.dens i z := by
  rw [B3Data.dens]
  exact Real.sqrt_nonneg _

/-- `d · (ζ · 1 · (√d)⁻¹ · S) = (ζ · √d) · S` for `d ≥ 0`. -/
lemma dens_sqrt_fac {d ζ S : ℝ} (hd : 0 ≤ d) :
    d * (ζ * 1 * (Real.sqrt d)⁻¹ * S) = (ζ * Real.sqrt d) * S := by
  rcases eq_or_ne (Real.sqrt d) 0 with h | h
  · rw [h]; ring
  · have hsq : d = Real.sqrt d * Real.sqrt d := by
      rw [← sq]; exact (Real.sq_sqrt hd).symm
    calc d * (ζ * 1 * (Real.sqrt d)⁻¹ * S)
        = (Real.sqrt d * Real.sqrt d) * (ζ * 1 * (Real.sqrt d)⁻¹ * S) := by
            nth_rewrite 1 [hsq]
            rfl
      _ = ((Real.sqrt d * Real.sqrt d) * (Real.sqrt d)⁻¹) * (ζ * S) := by ring
      _ = Real.sqrt d * (ζ * S) := by rw [sq_mul_inv]
      _ = (ζ * Real.sqrt d) * S := by ring

/-- **The pointwise identity for the `j`-th component of `BPair`.** -/
lemma Rpair_sum_eq {i j : ι₀}
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Bil (I := I) (M := M)) (z : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        D.R j (D.Rstar i u) a b z * D.R j k a b z)
      = (D.psi j z) ^ 2 * D.dens j z * Phi D i u k (D.pt j z) := by
  by_cases hψ : D.psi j z = 0
  · simp [B3Data.R, hψ]
  · have hONj := isONFrame_of_psi_ne_zero D hψ
    by_cases hζ : D.ζ i (D.pt j z) = 0
    · have hR : D.Rstar i u (D.pt j z) = 0 := Rstar_eq_zero_of_zeta_eq_zero D u hζ
      have hΦ : Phi D i u k (D.pt j z) = 0 := Phi_eq_zero_of_zeta_eq_zero D u k hζ
      rw [hΦ, mul_zero]
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      simp [B3Data.R, B3Data.mat, hR]
    · have hONi : IsONFrame g₀ (D.pt j z) (fun a => D.e i a (D.pt j z)) := by
        obtain ⟨hsrc, hlt⟩ := D.hζsupp i _ hζ
        have heq : D.pt i (coord (I := I) (D.x₀ i) (D.pt j z)) = D.pt j z := D.pt_coord i hsrc
        rw [← heq]
        exact D.heON i _ (by have := D.hσ i; linarith)
      rw [Phi_eq_sum_other_frame D u k hONj hONi]
      simp only [B3Data.R, B3Data.mat]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      exact mul_sqrt_sqrt_fac (d := D.dens j z) (dens_nonneg' D z) (D.psi j z) _ _

/-- **The pointwise identity for the right-hand side.**  On the `σ i`-ball the density times `Phi`
is exactly the contraction that defines `CPair i u (R i k)`. -/
lemma dens_mul_Phi_eq {i : ι₀}
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Bil (I := I) (M := M)) {y : Fin (Module.finrank ℝ E) → ℝ}
    (hy : ‖y‖ < D.σ i) :
    D.dens i y * Phi D i u k (D.pt i y)
      = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          u a b y * D.R i k a b y := by
  have hle : ‖y‖ ≤ 2 * D.σ i := by have := D.hσ i; linarith
  have hsrc : D.pt i y ∈ (extChartAt I (D.x₀ i)).source :=
    PartialEquiv.map_target (extChartAt I (D.x₀ i)) (D.htarget i y hle)
  have hcoord : coord (I := I) (D.x₀ i) (D.pt i y) = y := D.coord_pt i hle
  have hON : IsONFrame g₀ (D.pt i y) (fun a => D.e i a (D.pt i y)) := D.heON i y hle
  have hchi : D.χ i y = 1 := D.hχ1 i y (le_of_lt hy)
  have hPhi := Phi_apply_frame D (i := i) u k hON hsrc
  rw [hPhi, hcoord]
  simp only [B3Data.R, B3Data.mat, B3Data.psi, hchi, one_mul]
  have hsum : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        u a b y * (D.ζ i (D.pt i y) * Real.sqrt (D.dens i y)
          * k (D.pt i y) (D.e i a (D.pt i y)) (D.e i b (D.pt i y))))
      = (D.ζ i (D.pt i y) * Real.sqrt (D.dens i y))
        * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            u a b y * k (D.pt i y) (D.e i a (D.pt i y)) (D.e i b (D.pt i y))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsum]
  exact dens_sqrt_fac (d := D.dens i y) (ζ := D.ζ i (D.pt i y)) (S := _)
    (dens_nonneg' D y)

end Pointwise

section Geometric

variable {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
variable (D : B3Data (I := I) (M := M) ι₀ g₀) {i j : ι₀}
variable {y : Fin (Module.finrank ℝ E) → ℝ}

/-- The derivative of the chart transition `T y = coord j (pt i y)`, in flat coordinates: the
`tangentCoordChange` conjugated by the `finBasis`-identification. -/
def transDeriv (i j : ι₀) (y : Fin (Module.finrank ℝ E) → ℝ) :
    (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
  ((Module.finBasis ℝ E).equivFun.toContinuousLinearMap) ∘L
    (tangentCoordChange (I := I) (D.x₀ i) (D.x₀ j) (D.pt i y)) ∘L
    ((Module.finBasis ℝ E).equivFun.symm.toContinuousLinearMap)

/-- The centred cube is measurable. -/
lemma measurableSet_centreCube : MeasurableSet (B3Data.centreCube (E := E)) := by
  rw [B3Data.centreCube]
  exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Ioc)

/-- `pt i` is continuous on the flat ball of radius `σ i` (where the chart `i` is genuine). -/
lemma continuousOn_pt_sigmaBall :
    ContinuousOn (fun y => D.pt i y) (sigmaBall D i) := by
  have hsym : ContinuousOn (fun z : E => (extChartAt I (D.x₀ i)).symm z)
      (extChartAt I (D.x₀ i)).target :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ((⊤ : ENat) : WithTop ENat))
      (D.x₀ i)).continuousOn
  have hflat : Continuous (flatToE (I := I) (D.x₀ i)) := by
    have h1 : Continuous fun z : Fin (Module.finrank ℝ E) → ℝ =>
        (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)) + z :=
      continuous_const.add continuous_id
    have h2 : Continuous fun w : Fin (Module.finrank ℝ E) → ℝ =>
        (Module.finBasis ℝ E).equivFun.symm w :=
      (((Module.finBasis ℝ E).equivFun.symm :
        (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E).toContinuousLinearMap).continuous
    exact h2.comp h1
  have hmaps : MapsTo (flatToE (I := I) (D.x₀ i)) (sigmaBall D i)
      (extChartAt I (D.x₀ i)).target := by
    intro z hz
    refine D.htarget i z ?_
    have hz' : ‖z‖ < D.σ i := hz
    have := D.hσ i
    linarith
  simpa only [B3Data.pt, Function.comp_def] using hsym.comp hflat.continuousOn hmaps

/-- The flat ball is open. -/
lemma isOpen_sigmaBall : IsOpen (sigmaBall D i) := by
  have : sigmaBall D i = Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i) := by
    ext z; simp only [sigmaBall, Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right]
  rw [this]; exact Metric.isOpen_ball

lemma measurableSet_sigmaBall : MeasurableSet (sigmaBall D i) :=
  (isOpen_sigmaBall D).measurableSet

/-- The domain of the chart transfer is open. -/
lemma isOpen_overlapSet : IsOpen (overlapSet D i j) := by
  have h1 : IsOpen (sigmaBall D i) := isOpen_sigmaBall D
  have h2 : IsOpen (Function.support (D.ζ j)) := by
    have hcl : IsClosed ((D.ζ j) ⁻¹' ({0} : Set ℝ)) :=
      isClosed_singleton.preimage (D.hζsm j).continuous
    rw [show Function.support (D.ζ j) = ((D.ζ j) ⁻¹' ({0} : Set ℝ))ᶜ from by
      ext x; simp [Function.mem_support]]
    exact hcl.isOpen_compl
  have h3 : IsOpen (sigmaBall D i ∩ (fun y => D.pt i y) ⁻¹' (Function.support (D.ζ j))) :=
    ContinuousOn.isOpen_inter_preimage (continuousOn_pt_sigmaBall D) h1 h2
  convert h3 using 1
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Function.mem_support, overlapSet,
    mem_sigmaBall, Set.mem_setOf_eq]

/-- On the overlap, the flat coordinate of `pt i y` in chart `i` is `y`. -/
lemma coord_pt_of_mem_overlap (hy : y ∈ overlapSet D i j) :
    coord (I := I) (D.x₀ i) (D.pt i y) = y :=
  D.coord_pt i (by have := D.hσ i; linarith [hy.1])

lemma pt_i_mem_source_of_mem_overlap (hy : y ∈ overlapSet D i j) :
    D.pt i y ∈ (extChartAt I (D.x₀ i)).source := by
  have hle : ‖y‖ ≤ 2 * D.σ i := by have := D.hσ i; linarith [hy.1]
  exact PartialEquiv.map_target (extChartAt I (D.x₀ i)) (D.htarget i y hle)

lemma pt_i_mem_source_j_of_mem_overlap (hy : y ∈ overlapSet D i j) :
    D.pt i y ∈ (extChartAt I (D.x₀ j)).source :=
  (D.hζsupp j _ hy.2).1

lemma norm_transMap_lt (hy : y ∈ overlapSet D i j) : ‖transMap D i j y‖ < D.σ j :=
  (D.hζsupp j _ hy.2).2

lemma pt_j_transMap (hy : y ∈ overlapSet D i j) :
    D.pt j (transMap D i j y) = D.pt i y :=
  D.pt_coord j (pt_i_mem_source_j_of_mem_overlap D hy)

lemma chi_j_transMap (hy : y ∈ overlapSet D i j) : D.χ j (transMap D i j y) = 1 :=
  D.hχ1 j _ (le_of_lt (norm_transMap_lt D hy))

lemma psi_j_transMap (hy : y ∈ overlapSet D i j) :
    D.psi j (transMap D i j y) = D.ζ j (D.pt i y) := by
  rw [B3Data.psi, chi_j_transMap D hy, pt_j_transMap D hy, one_mul]

/-- The chart transition is injective on the overlap. -/
lemma injOn_transMap : Set.InjOn (transMap D i j) (overlapSet D i j) := by
  intro y hy y' hy' h
  have h1 : (extChartAt I (D.x₀ j)) (D.pt i y) = (extChartAt I (D.x₀ j)) (D.pt i y') := by
    have h2 : coord (I := I) (D.x₀ j) (D.pt i y) = coord (I := I) (D.x₀ j) (D.pt i y') := h
    simp only [coord, sub_left_inj] at h2
    exact (Module.finBasis ℝ E).equivFun.injective h2
  have h3 : D.pt i y = D.pt i y' := by
    have h4 := congrArg (extChartAt I (D.x₀ j)).symm h1
    rwa [(extChartAt I (D.x₀ j)).left_inv (pt_i_mem_source_j_of_mem_overlap D hy),
      (extChartAt I (D.x₀ j)).left_inv (pt_i_mem_source_j_of_mem_overlap D hy')] at h4
  have h5 : coord (I := I) (D.x₀ i) (D.pt i y) = coord (I := I) (D.x₀ i) (D.pt i y') := by
    rw [h3]
  rwa [coord_pt_of_mem_overlap D hy, coord_pt_of_mem_overlap D hy'] at h5

/-- The transition map is differentiable within the overlap, with derivative `transDeriv`. -/
lemma hasFDerivWithinAt_transMap (hy : y ∈ overlapSet D i j) :
    HasFDerivWithinAt (transMap D i j) (transDeriv D i j y) (overlapSet D i j) y :=
  hasFDerivWithinAt_coord_pt D i j (overlapSet D i j)
    (fun y' hy' => ⟨by
      rw [D.hχ1 i y' (le_of_lt hy'.1)]
      exact one_ne_zero, hy'.2⟩) hy

/-- The determinant of the derivative of the chart transition is the determinant of
`tangentCoordChange`. -/
lemma det_transDeriv (y : Fin (Module.finrank ℝ E) → ℝ) :
    (transDeriv D i j y).det
      = (tangentCoordChange (I := I) (D.x₀ i) (D.x₀ j) (D.pt i y)).det := by
  rw [transDeriv]
  exact LinearMap.det_conj _ ((Module.finBasis ℝ E).equivFun)

/-- The change of flat coordinates: `|det D(T)| · dens j (T y) = dens i y` on the overlap. -/
lemma abs_det_mul_dens_transMap (hy : y ∈ overlapSet D i j) :
    |(transDeriv D i j y).det| * D.dens j (transMap D i j y) = D.dens i y := by
  have hdt := dens_transition D i j (D.pt i y) (pt_i_mem_source_of_mem_overlap D hy)
    (pt_i_mem_source_j_of_mem_overlap D hy)
  simp only [transMap]
  rw [det_transDeriv D, ← hdt]
  congr 1
  exact coord_pt_of_mem_overlap D hy

/-- The image of the overlap lies in the centred cube. -/
lemma transMap_mem_centreCube (hy : y ∈ overlapSet D i j) :
    transMap D i j y ∈ B3Data.centreCube (E := E) := by
  have h := norm_transMap_lt D hy
  have hσ : 2 * D.σ j ≤ (1 / 2 : ℝ) := by have := D.hσ2 j; linarith
  intro k _
  simp only [Set.mem_Ioc]
  have hk : |transMap D i j y k| ≤ ‖transMap D i j y‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (transMap D i j y) k
  constructor <;> linarith [abs_le.mp hk]

/-- **The support of the `j`-th integrand is carried by the overlap.** -/
lemma support_subset_transMap_image
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (k : Bil (I := I) (M := M)) :
    ∀ z, (D.psi j z) ^ 2 * D.dens j z * Phi D i u k (D.pt j z) ≠ 0 →
      z ∈ transMap D i j '' overlapSet D i j := by
  intro z hz
  have hψ : D.psi j z ≠ 0 := by
    intro h0
    exact hz (by rw [h0]; ring)
  have hΦ : Phi D i u k (D.pt j z) ≠ 0 := by
    intro h0
    exact hz (by rw [h0, mul_zero])
  have hζi : D.ζ i (D.pt j z) ≠ 0 := fun h0 =>
    hΦ (Phi_eq_zero_of_zeta_eq_zero D u k h0)
  set p := D.pt j z with hp
  have hsrc_i : p ∈ (extChartAt I (D.x₀ i)).source := (D.hζsupp i p hζi).1
  have hlt_i : ‖coord (I := I) (D.x₀ i) p‖ < D.σ i := (D.hζsupp i p hζi).2
  have hζj : D.ζ j p ≠ 0 := zeta_ne_zero_of_psi_ne_zero D hψ
  have hcoord : D.pt i (coord (I := I) (D.x₀ i) p) = p := D.pt_coord i hsrc_i
  refine ⟨coord (I := I) (D.x₀ i) p, ⟨by simpa only [mem_sigmaBall] using hlt_i, ?_⟩, ?_⟩
  · rw [hcoord]; exact hζj
  · simp only [transMap]
    rw [hcoord, hp]
    exact coord_pt_of_psi_ne_zero D hψ

/-- **The pointwise form of the transferred integrand.** -/
lemma integrand_transfer
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (k : Bil (I := I) (M := M))
    (hy : y ∈ overlapSet D i j) :
    |(transDeriv D i j y).det|
        * ((D.psi j (transMap D i j y)) ^ 2 * D.dens j (transMap D i j y)
            * Phi D i u k (D.pt j (transMap D i j y)))
      = (D.ζ j (D.pt i y)) ^ 2 * D.dens i y * Phi D i u k (D.pt i y) := by
  rw [psi_j_transMap D hy, pt_j_transMap D hy]
  have h := abs_det_mul_dens_transMap D hy
  calc |(transDeriv D i j y).det|
        * ((D.ζ j (D.pt i y)) ^ 2 * D.dens j (transMap D i j y) * Phi D i u k (D.pt i y))
      = (D.ζ j (D.pt i y)) ^ 2 * Phi D i u k (D.pt i y)
          * (|(transDeriv D i j y).det| * D.dens j (transMap D i j y)) := by ring
    _ = (D.ζ j (D.pt i y)) ^ 2 * D.dens i y * Phi D i u k (D.pt i y) := by rw [h]; ring

/-- **The chart transfer.**  The `j`-th contribution to the composite pairing, read in the chart
`i`. -/
lemma integral_transfer
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (k : Bil (I := I) (M := M)) :
    ∫ z in B3Data.centreCube (E := E),
        ((D.psi j z) ^ 2 * D.dens j z * Phi D i u k (D.pt j z))
      = ∫ y in sigmaBall D i,
          (D.ζ j (D.pt i y)) ^ 2 * D.dens i y * Phi D i u k (D.pt i y) := by
  set g : (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
    fun z => (D.psi j z) ^ 2 * D.dens j z * Phi D i u k (D.pt j z) with hg
  have hU : MeasurableSet (overlapSet D i j) := (isOpen_overlapSet D).measurableSet
  have himg : transMap D i j '' overlapSet D i j ⊆ B3Data.centreCube (E := E) := by
    rintro z ⟨y, hy, rfl⟩
    exact transMap_mem_centreCube D hy
  have hzero : ∀ z ∈ B3Data.centreCube (E := E) \ (transMap D i j '' overlapSet D i j),
      g z = 0 := by
    intro z hz
    by_contra h
    exact hz.2 (support_subset_transMap_image D u k z h)
  have hstep1 : ∫ z in B3Data.centreCube (E := E), g z
      = ∫ z in transMap D i j '' overlapSet D i j, g z :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_centreCube (E := E)) himg
      hzero
  have hstep2 : ∫ z in transMap D i j '' overlapSet D i j, g z
      = ∫ y in overlapSet D i j, |(transDeriv D i j y).det| • g (transMap D i j y) :=
    integral_image_eq_integral_abs_det_fderiv_smul volume hU
      (fun y hy => hasFDerivWithinAt_transMap D hy) (injOn_transMap D) g
  have hstep3 : ∫ y in overlapSet D i j, |(transDeriv D i j y).det| • g (transMap D i j y)
      = ∫ y in overlapSet D i j,
          (D.ζ j (D.pt i y)) ^ 2 * D.dens i y * Phi D i u k (D.pt i y) := by
    refine setIntegral_congr_fun hU fun y hy => ?_
    show |(transDeriv D i j y).det| * g (transMap D i j y) = _
    rw [hg]
    exact integrand_transfer D u k hy
  have hstep4 : ∫ y in sigmaBall D i,
        (D.ζ j (D.pt i y)) ^ 2 * D.dens i y * Phi D i u k (D.pt i y)
      = ∫ y in overlapSet D i j,
          (D.ζ j (D.pt i y)) ^ 2 * D.dens i y * Phi D i u k (D.pt i y) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_sigmaBall D)
      (fun y hy => hy.1) (fun y hy => by
        obtain ⟨hyball, hyU⟩ := hy
        have hζ : D.ζ j (D.pt i y) = 0 := by
          by_contra h
          exact hyU ⟨hyball, h⟩
        rw [hζ]; ring)
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4.symm))

end Geometric

section Assembly

variable {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
variable (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
variable (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
  (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
variable (k : Bil (I := I) (M := M))

/-- **The adjunction, conditional on the integrability of the three families of integrands.** -/
theorem BPair_Rstar_of_integrable
    (hintR : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      IntegrableOn (fun z => D.R j (D.Rstar i u) a b z * D.R j k a b z)
        (B3Data.centreCube (E := E)))
    (hintC : ∀ (a b : Fin (Module.finrank ℝ E)),
      IntegrableOn (fun y => u a b y * D.R i k a b y) (B3Data.centreCube (E := E)))
    (hintN : ∀ j : ι₀,
      IntegrableOn (fun y => (D.ζ j (D.pt i y)) ^ 2 * D.dens i y * Phi D i u k (D.pt i y))
        (sigmaBall D i)) :
    D.BPair (D.Rstar i u) k = B3Data.CPair i u (D.R i k) := by
  -- contribution of the `j`-th chart to the composite pairing
  have hCPair (j : ι₀) : B3Data.CPair j (D.R j (D.Rstar i u)) (D.R j k)
      = ∫ y in sigmaBall D i,
          (D.ζ j (D.pt i y)) ^ 2 * D.dens i y * Phi D i u k (D.pt i y) := by
    rw [B3Data.CPair]
    rw [show (∑ a, ∑ b, ∫ z in B3Data.centreCube (E := E),
            D.R j (D.Rstar i u) a b z * D.R j k a b z)
        = ∫ z in B3Data.centreCube (E := E),
            ∑ a, ∑ b, D.R j (D.Rstar i u) a b z * D.R j k a b z from by
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun a _ => ?_
        rw [MeasureTheory.integral_finsetSum]
        exact fun b _ => hintR j a b
      · intro a _
        exact (integrable_finsetSum' Finset.univ (fun b _ => hintR j a b)).congr
          (Filter.Eventually.of_forall fun z => by simp only [Finset.sum_apply])]
    rw [setIntegral_congr_fun (measurableSet_centreCube (E := E))
      (fun z _ => Rpair_sum_eq D u k z)]
    exact integral_transfer D u k
  have hRHS : B3Data.CPair i u (D.R i k)
      = ∫ y in sigmaBall D i, D.dens i y * Phi D i u k (D.pt i y) := by
    rw [B3Data.CPair]
    rw [show (∑ a, ∑ b, ∫ y in B3Data.centreCube (E := E), u a b y * D.R i k a b y)
        = ∫ y in B3Data.centreCube (E := E),
            ∑ a, ∑ b, u a b y * D.R i k a b y from by
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun a _ => ?_
        rw [MeasureTheory.integral_finsetSum]
        exact fun b _ => hintC a b
      · intro a _
        exact (integrable_finsetSum' Finset.univ (fun b _ => hintC a b)).congr
          (Filter.Eventually.of_forall fun y => by simp only [Finset.sum_apply])]
    rw [show ∫ y in B3Data.centreCube (E := E), ∑ a, ∑ b, u a b y * D.R i k a b y
        = ∫ y in sigmaBall D i, ∑ a, ∑ b, u a b y * D.R i k a b y from
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_centreCube (E := E))
        (fun y hy => by
          have hσ : D.σ i ≤ (1 / 2 : ℝ) := by have := D.hσ2 i; linarith
          have hy' : ‖y‖ < D.σ i := hy
          intro j _
          simp only [Set.mem_Ioc]
          have hk : |y j| ≤ ‖y‖ := by
            simpa only [Real.norm_eq_abs] using norm_le_pi_norm y j
          constructor <;> linarith [abs_le.mp hk])
        (fun y hy => by
          refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
          rw [B3Data.R, B3Data.mat]
          have hpsi : D.psi i y = 0 := by
            by_contra h
            exact hy.2 (norm_lt_sigma_of_psi_ne_zero D h)
          rw [hpsi]; ring)]
    exact (setIntegral_congr_fun (measurableSet_sigmaBall D)
      (fun y hy => dens_mul_Phi_eq D u k hy)).symm
  rw [B3Data.BPair, Finset.sum_congr rfl fun j _ => hCPair j]
  rw [show (∑ j : ι₀, ∫ y in sigmaBall D i,
        (D.ζ j (D.pt i y)) ^ 2 * D.dens i y * Phi D i u k (D.pt i y))
      = ∫ y in sigmaBall D i,
          ∑ j : ι₀, (D.ζ j (D.pt i y)) ^ 2 * D.dens i y * Phi D i u k (D.pt i y) from by
    rw [MeasureTheory.integral_finsetSum]
    exact fun j _ => hintN j]
  have hsum : ∀ y : Fin (Module.finrank ℝ E) → ℝ,
      (∑ j : ι₀, (D.ζ j (D.pt i y)) ^ 2 * D.dens i y * Phi D i u k (D.pt i y))
        = D.dens i y * Phi D i u k (D.pt i y) := by
    intro y
    rw [show (∑ j : ι₀, (D.ζ j (D.pt i y)) ^ 2 * D.dens i y * Phi D i u k (D.pt i y))
        = (∑ j : ι₀, (D.ζ j (D.pt i y)) ^ 2) * (D.dens i y * Phi D i u k (D.pt i y)) from by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring]
    rw [D.hζsq (D.pt i y), one_mul]
  rw [setIntegral_congr_fun (measurableSet_sigmaBall D) (fun y _ => hsum y)]
  exact hRHS.symm

end Assembly

section RpairIntegrable

variable {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- `coord x₀` is continuous at every point of the chart source. -/
lemma rp_continuousAt_coord (x₀ : M) {p : M} (hp : p ∈ (extChartAt I x₀).source) :
    ContinuousAt (coord (I := I) x₀) p := by
  have h1 : ContinuousAt (extChartAt I x₀) p := continuousAt_extChartAt' hp
  have h2 : ContinuousAt (fun v : E => (Module.finBasis ℝ E).equivFun v
      - (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)) ((extChartAt I x₀) p) :=
    (((continuous_equivFun_basis (Module.finBasis ℝ E)).sub continuous_const).continuousAt)
  change ContinuousAt (fun q : M => (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) q)
    - (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)) p
  simpa only [Function.comp_def] using h2.comp h1

/-- The metric pairing of two smooth fields is smooth. -/
lemma rp_contMDiffAt_metric_pairing_field (g : Submission.Diff.SMet I M)
    {Y Z : Π y : M, TangentSpace I y} {p : M}
    (hY : Work.Diff.EXT.SmoothFieldAt I M Y p) (hZ : Work.Diff.EXT.SmoothFieldAt I M Z p) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat)
      (fun q : M => g.inner q (Y q) (Z q)) p := by
  have hres := Work.Diff.STE.B3.contMDiffAt_metric_pairing' (I := I) (G := fun _ : ℝ => g)
    (J := Set.univ) isOpen_univ (jointSmooth_const' g) (Set.mem_univ (0 : ℝ)) hY hZ
  have hc : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ((⊤ : ENat) : WithTop ENat)
      (fun q : M => ((0 : ℝ), q)) p :=
    (contMDiffAt_const : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) _
      (fun _ : M => (0 : ℝ)) p).prodMk contMDiffAt_id
  simpa only [Function.comp_def] using hres.comp p hc

/-- A finite family of functions continuous on a compact set is uniformly bounded. -/
lemma rp_exists_bound_of_forall_continuousOn {ι : Type*} [Fintype ι] {n : ℕ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (f : ι → (Fin n → ℝ) → ℝ)
    (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : ι) (y : Fin n → ℝ), y ∈ K → |f i y| ≤ C := by
  choose B hB using fun i => hK.exists_bound_of_continuousOn (hf i)
  refine ⟨∑ i : ι, |B i|, Finset.sum_nonneg (fun i _ => abs_nonneg _), fun i y hy => ?_⟩
  have h1 : ‖f i y‖ ≤ B i := hB i y hy
  have h2 : |f i y| ≤ B i := by rwa [Real.norm_eq_abs] at h1
  exact h2.trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun j : ι => |B j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)))

/-- **The reconstruction in the frame of chart `j`.**  Evaluating `Rstar i u` at `pt j z` in the
frame of chart `j` is given by the explicit formula of `Rstar_apply`. -/
lemma rp_mat_rstar_apply
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (a b : Fin (Module.finrank ℝ E))
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    D.mat j (D.Rstar i u) a b z =
      (D.ζ i (D.pt j z) * D.χ i (coord (I := I) (D.x₀ i) (D.pt j z))
        * (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) (D.pt j z))))⁻¹)
      * (∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
          u a' b' (coord (I := I) (D.x₀ i) (D.pt j z))
          * g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i a' (D.pt j z))
          * g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i b' (D.pt j z))) := by
  rw [B3Data.mat]
  exact Rstar_apply D i u (D.pt j z) (D.e j a (D.pt j z)) (D.e j b (D.pt j z))

theorem rp_integrableOn_Rpair_term
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Work.Diff.STE.Bil (I := I) (M := M))
    (hu : ∀ a b : Fin (Module.finrank ℝ E), Continuous (u a b))
    (hk : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContinuousOn (D.mat j k a b) {z : Fin (Module.finrank ℝ E) → ℝ | D.χ j z ≠ 0})
    (hdens : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (i : ι₀)
      (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i → c ≤ D.dens i z ∧ D.dens i z ≤ C)
    (j : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    MeasureTheory.IntegrableOn
      (fun z => D.R j (D.Rstar i u) a b z * D.R j k a b z)
      (Work.Diff.STE.B3Data.centreCube (E := E)) MeasureTheory.volume := by
  classical
  obtain ⟨c, C, hcpos, hCpos, hdensb⟩ := hdens
  -- the open set on which both charts are simultaneously genuine
  set W : Set (Fin (Module.finrank ℝ E) → ℝ) :=
    sigmaBall D j ∩ {z | D.ζ i (D.pt j z) ≠ 0} with hWdef
  have hmemW : ∀ z, z ∈ W ↔ ‖z‖ < D.σ j ∧ D.ζ i (D.pt j z) ≠ 0 := by
    intro z
    rw [hWdef]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_sigmaBall]
  have hptW : ContinuousOn (fun z => D.pt j z) W :=
    (continuousOn_pt_sigmaClosedBall' D j).mono (fun z hz => le_of_lt ((hmemW z).mp hz).1)
  have hWopen : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hz' := (hmemW z).mp hz
    rw [hWdef]
    refine Filter.inter_mem ((isOpen_sigmaBall' D j).mem_nhds hz'.1) ?_
    have hpt : ContinuousAt (fun z => D.pt j z) z :=
      (continuousAt_extChartAt_symm'' (D.htarget j z (by
        have := D.hσ j; linarith [hz'.1]))).comp
        (continuous_flatToE (I := I) (D.x₀ j)).continuousAt
    have hζ : ContinuousAt (fun z => D.ζ i (D.pt j z)) z :=
      (D.hζsm i).continuous.continuousAt.comp hpt
    exact hζ.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hz'.2)
  have hWbdd : Bornology.IsBounded W :=
    (isBounded_sigmaBall' D j).subset (fun z hz => ((hmemW z).mp hz).1)
  -- the integrand vanishes off `W`
  have hzero : ∀ z ∉ W, D.R j (D.Rstar i u) a b z * D.R j k a b z = 0 := by
    intro z hz
    rw [hmemW] at hz
    by_cases hA : ‖z‖ < D.σ j
    · have hB : D.ζ i (D.pt j z) = 0 := by
        by_contra hB
        exact hz ⟨hA, hB⟩
      have hR : D.Rstar i u (D.pt j z) = 0 := Rstar_eq_zero_of_zeta_eq_zero D u hB
      have hmat : D.mat j (D.Rstar i u) a b z = 0 := by
        simp only [B3Data.mat, hR, ContinuousLinearMap.zero_apply]
      simp only [B3Data.R, hmat, mul_zero, zero_mul]
    · have hψ : D.psi j z = 0 := by
        by_contra h
        exact absurd (norm_lt_sigma_of_psi_ne_zero D h) hA
      simp only [B3Data.R, hψ, zero_mul, mul_zero]
  -- continuity of the reconstruction in the frame of chart `j`
  have hFexp_cont : ContinuousOn (fun z =>
      (D.ζ i (D.pt j z) * D.χ i (coord (I := I) (D.x₀ i) (D.pt j z))
        * (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) (D.pt j z))))⁻¹)
      * (∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
          u a' b' (coord (I := I) (D.x₀ i) (D.pt j z))
          * g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i a' (D.pt j z))
          * g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i b' (D.pt j z)))) W := by
    have hcoord : ContinuousOn (fun z => coord (I := I) (D.x₀ i) (D.pt j z)) W :=
      ContinuousOn.comp
        (fun p hp =>
          (rp_continuousAt_coord (I := I) (D.x₀ i) (D.hζsupp i p hp).1).continuousWithinAt)
        hptW (fun z hz => ((hmemW z).mp hz).2)
    have hζ : ContinuousOn (fun z => D.ζ i (D.pt j z)) W :=
      (D.hζsm i).continuous.comp_continuousOn hptW
    have hχ : ContinuousOn (fun z => D.χ i (coord (I := I) (D.x₀ i) (D.pt j z))) W :=
      (D.hχsm i).continuous.comp_continuousOn hcoord
    have hdensi : ContinuousOn (fun z => D.dens i (coord (I := I) (D.x₀ i) (D.pt j z))) W := by
      refine ContinuousOn.comp
        (f := fun z => coord (I := I) (D.x₀ i) (D.pt j z))
        (g := fun y : Fin (Module.finrank ℝ E) → ℝ => D.dens i y)
        (s := W) (t := flatToE (I := I) (D.x₀ i) ⁻¹' (extChartAt I (D.x₀ i)).target)
        (fun y hy => (dens_continuousAt_of_mem_target D i hy).continuousWithinAt) hcoord ?_
      intro z hz
      change flatToE (I := I) (D.x₀ i) (coord (I := I) (D.x₀ i) (D.pt j z))
        ∈ (extChartAt I (D.x₀ i)).target
      rw [flatToE_coord (I := I) (D.x₀ i) (D.pt j z)]
      exact (extChartAt I (D.x₀ i)).map_source ((D.hζsupp i _ ((hmemW z).mp hz).2).1)
    have hinv : ContinuousOn
        (fun z => (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) (D.pt j z))))⁻¹) W :=
      (Real.continuous_sqrt.comp_continuousOn hdensi).inv₀ (fun z hz => by
        refine ne_of_gt (Real.sqrt_pos.mpr ?_)
        exact lt_of_lt_of_le hcpos (hdensb i _ ((D.hζsupp i _ ((hmemW z).mp hz).2).2.le)).1)
    have hpair1 (a' : Fin (Module.finrank ℝ E)) : ContinuousOn (fun z =>
        g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i a' (D.pt j z))) W :=
      ContinuousOn.comp (fun q _ => ((rp_contMDiffAt_metric_pairing_field g₀
        (D.hesm j a).contMDiffAt (D.hesm i a').contMDiffAt).continuousAt).continuousWithinAt)
        hptW (fun z _ => Set.mem_univ _)
    have hpair2 (b' : Fin (Module.finrank ℝ E)) : ContinuousOn (fun z =>
        g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i b' (D.pt j z))) W :=
      ContinuousOn.comp (fun q _ => ((rp_contMDiffAt_metric_pairing_field g₀
        (D.hesm j b).contMDiffAt (D.hesm i b').contMDiffAt).continuousAt).continuousWithinAt)
        hptW (fun z _ => Set.mem_univ _)
    have hsum : ContinuousOn (fun z => ∑ a' : Fin (Module.finrank ℝ E),
        ∑ b' : Fin (Module.finrank ℝ E),
          u a' b' (coord (I := I) (D.x₀ i) (D.pt j z))
          * g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i a' (D.pt j z))
          * g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i b' (D.pt j z))) W := by
      refine continuousOn_finsetSum Finset.univ (fun a' _ => ?_)
      refine continuousOn_finsetSum Finset.univ (fun b' _ => ?_)
      exact (((hu a' b').comp_continuousOn hcoord).mul (hpair1 a')).mul (hpair2 b')
    refine ((hζ.mul (hχ.mul hinv)).mul hsum).congr (fun z hz => ?_)
    simp only [Pi.mul_apply]
    ring
  have hmatRstar_cont : ContinuousOn (fun z => D.mat j (D.Rstar i u) a b z) W :=
    hFexp_cont.congr (fun z _ => rp_mat_rstar_apply D i j u a b z)
  have hpsi : ContinuousOn (fun z => D.psi j z) W := by
    refine ContinuousOn.congr
      (((D.hχsm j).continuous.continuousOn).mul
        ((D.hζsm j).continuous.comp_continuousOn hptW)) (fun z _ => ?_)
    simp only [B3Data.psi, Pi.mul_apply, Function.comp_apply]
  have hsdens : ContinuousOn (fun z => Real.sqrt (D.dens j z)) W :=
    Real.continuous_sqrt.comp_continuousOn
      ((continuousOn_dens_closed D j).mono (fun z hz => le_of_lt ((hmemW z).mp hz).1))
  have hmatk_cont : ContinuousOn (fun z => D.mat j k a b z) W :=
    (hk j a b).mono (fun z hz => chi_ne_zero_of_norm_le_sigma D (le_of_lt ((hmemW z).mp hz).1))
  have hR1 : ContinuousOn (fun z => D.R j (D.Rstar i u) a b z) W := by
    refine ((hpsi.mul hsdens).mul hmatRstar_cont).congr (fun z _ => ?_)
    simp only [B3Data.R, Pi.mul_apply]
  have hR2 : ContinuousOn (fun z => D.R j k a b z) W := by
    refine ((hpsi.mul hsdens).mul hmatk_cont).congr (fun z _ => ?_)
    simp only [B3Data.R, Pi.mul_apply]
  have hcont : ContinuousOn (fun z => D.R j (D.Rstar i u) a b z * D.R j k a b z) W :=
    hR1.mul hR2
  -- uniform bounds
  obtain ⟨Mu, hMu0, hMu⟩ := rp_exists_bound_of_forall_continuousOn (isCompact_sigmaClosedBall' D i)
    (f := fun ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
      fun y => u ab.1 ab.2 y) (fun ab => (hu ab.1 ab.2).continuousOn)
  obtain ⟨Mg1, hMg10, hMg1⟩ := rp_exists_bound_of_forall_continuousOn (isCompact_sigmaClosedBall' D j)
    (f := fun a' : Fin (Module.finrank ℝ E) => fun z =>
      g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i a' (D.pt j z)))
    (fun a' => ContinuousOn.comp (fun q _ => ((rp_contMDiffAt_metric_pairing_field g₀
      (D.hesm j a).contMDiffAt (D.hesm i a').contMDiffAt).continuousAt).continuousWithinAt)
      (continuousOn_pt_sigmaClosedBall' D j) (fun z _ => Set.mem_univ _))
  obtain ⟨Mg2, hMg20, hMg2⟩ := rp_exists_bound_of_forall_continuousOn (isCompact_sigmaClosedBall' D j)
    (f := fun b' : Fin (Module.finrank ℝ E) => fun z =>
      g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i b' (D.pt j z)))
    (fun b' => ContinuousOn.comp (fun q _ => ((rp_contMDiffAt_metric_pairing_field g₀
      (D.hesm j b).contMDiffAt (D.hesm i b').contMDiffAt).continuousAt).continuousWithinAt)
      (continuousOn_pt_sigmaClosedBall' D j) (fun z _ => Set.mem_univ _))
  obtain ⟨Mk, hMk⟩ := (isCompact_sigmaClosedBall' D j).exists_bound_of_continuousOn
    ((hk j a b).mono (fun z hz => chi_ne_zero_of_norm_le_sigma D hz))
  set K₁ : ℝ := (Real.sqrt c)⁻¹ * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)
    * (Mu * Mg1 * Mg2)) with hK₁
  have hK₁nn : 0 ≤ K₁ := by
    rw [hK₁]
    have : (0:ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    positivity
  set Kb : ℝ := (Real.sqrt C * K₁) * (Real.sqrt C * |Mk|) + 1 with hKb
  have hKbnn : 0 ≤ Kb := by
    rw [hKb]
    have := Real.sqrt_nonneg C
    have := Real.sqrt_nonneg C
    positivity
  -- the bound on the reconstruction in the frame of chart `j`
  have hmatRstar_bound : ∀ z, ‖z‖ < D.σ j → D.ζ i (D.pt j z) ≠ 0 →
      ‖D.mat j (D.Rstar i u) a b z‖ ≤ K₁ := by
    intro z hz hζ
    have hci : ‖coord (I := I) (D.x₀ i) (D.pt j z)‖ ≤ D.σ i :=
      le_of_lt (D.hζsupp i _ hζ).2
    have hlej : ‖z‖ ≤ D.σ j := le_of_lt hz
    have hcoeff : ‖D.ζ i (D.pt j z) * D.χ i (coord (I := I) (D.x₀ i) (D.pt j z))
        * (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) (D.pt j z))))⁻¹‖ ≤ (Real.sqrt c)⁻¹ := by
      have hχ1 : D.χ i (coord (I := I) (D.x₀ i) (D.pt j z)) = 1 := D.hχ1 i _ hci
      have hsq : Real.sqrt c ≤ Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) (D.pt j z))) :=
        Real.sqrt_le_sqrt (hdensb i _ hci).1
      have hinv : (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) (D.pt j z))))⁻¹
          ≤ (Real.sqrt c)⁻¹ :=
        (inv_le_inv₀ (Real.sqrt_pos.mpr (lt_of_lt_of_le hcpos (hdensb i _ hci).1))
          (Real.sqrt_pos.mpr hcpos)).mpr hsq
      have hinvnn : 0 ≤ (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) (D.pt j z))))⁻¹ :=
        inv_nonneg.mpr (Real.sqrt_nonneg _)
      rw [hχ1, mul_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hinvnn]
      calc |D.ζ i (D.pt j z)| * (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) (D.pt j z))))⁻¹
          ≤ 1 * (Real.sqrt c)⁻¹ := mul_le_mul (abs_zeta_le_one D i _) hinv hinvnn zero_le_one
        _ = (Real.sqrt c)⁻¹ := one_mul _
    have hterm : ∀ a' b' : Fin (Module.finrank ℝ E),
        |u a' b' (coord (I := I) (D.x₀ i) (D.pt j z))
          * g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i a' (D.pt j z))
          * g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i b' (D.pt j z))|
        ≤ Mu * Mg1 * Mg2 := by
      intro a' b'
      rw [abs_mul, abs_mul]
      exact mul_le_mul
        (mul_le_mul (hMu (a', b') _ hci) (hMg1 a' z hlej) (abs_nonneg _) hMu0)
        (hMg2 b' z hlej) (abs_nonneg _) (mul_nonneg hMu0 hMg10)
    have hsum : ‖(∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
          u a' b' (coord (I := I) (D.x₀ i) (D.pt j z))
          * g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i a' (D.pt j z))
          * g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i b' (D.pt j z)))‖
        ≤ (Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * (Mu * Mg1 * Mg2) := by
      calc ‖(∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
            u a' b' (coord (I := I) (D.x₀ i) (D.pt j z))
            * g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i a' (D.pt j z))
            * g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i b' (D.pt j z)))‖
          = |(∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
            u a' b' (coord (I := I) (D.x₀ i) (D.pt j z))
            * g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i a' (D.pt j z))
            * g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i b' (D.pt j z)))| :=
              Real.norm_eq_abs _
        _ ≤ ∑ a' : Fin (Module.finrank ℝ E),
              |∑ b' : Fin (Module.finrank ℝ E),
                u a' b' (coord (I := I) (D.x₀ i) (D.pt j z))
                * g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i a' (D.pt j z))
                * g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i b' (D.pt j z))| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
              |u a' b' (coord (I := I) (D.x₀ i) (D.pt j z))
                * g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i a' (D.pt j z))
                * g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i b' (D.pt j z))| :=
              Finset.sum_le_sum (fun a' _ => Finset.abs_sum_le_sum_abs _ _)
        _ ≤ ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
              Mu * Mg1 * Mg2 :=
              Finset.sum_le_sum (fun a' _ =>
                Finset.sum_le_sum (fun b' _ => hterm a' b'))
        _ = (Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * (Mu * Mg1 * Mg2) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              ring
    calc ‖D.mat j (D.Rstar i u) a b z‖
        = ‖(D.ζ i (D.pt j z) * D.χ i (coord (I := I) (D.x₀ i) (D.pt j z))
            * (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) (D.pt j z))))⁻¹)
          * (∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
              u a' b' (coord (I := I) (D.x₀ i) (D.pt j z))
              * g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i a' (D.pt j z))
              * g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i b' (D.pt j z)))‖ := by
          rw [rp_mat_rstar_apply]
      _ = _ := norm_mul _ _
      _ ≤ (Real.sqrt c)⁻¹ * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)
            * (Mu * Mg1 * Mg2)) :=
          mul_le_mul hcoeff hsum (norm_nonneg _)
            (by have := Real.sqrt_nonneg c; positivity)
      _ = K₁ := hK₁.symm
  -- the global bound
  have hbound : ∀ z, ‖D.R j (D.Rstar i u) a b z * D.R j k a b z‖ ≤ Kb := by
    intro z
    by_cases hz : z ∈ W
    · have hz' := (hmemW z).mp hz
      have hlej : ‖z‖ ≤ D.σ j := le_of_lt hz'.1
      have hpsi_le : |D.psi j z| ≤ 1 := by
        rw [B3Data.psi, D.hχ1 j z hlej, one_mul]
        exact abs_zeta_le_one D j _
      have hdens_le : Real.sqrt (D.dens j z) ≤ Real.sqrt C :=
        Real.sqrt_le_sqrt (hdensb j z hlej).2
      have hR1 : ‖D.R j (D.Rstar i u) a b z‖ ≤ Real.sqrt C * K₁ := by
        show ‖D.psi j z * Real.sqrt (D.dens j z) * D.mat j (D.Rstar i u) a b z‖ ≤ _
        rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        calc |D.psi j z| * Real.sqrt (D.dens j z) * |D.mat j (D.Rstar i u) a b z|
            ≤ 1 * Real.sqrt C * K₁ :=
              mul_le_mul (mul_le_mul hpsi_le hdens_le (Real.sqrt_nonneg _) zero_le_one)
                (hmatRstar_bound z hz'.1 hz'.2) (abs_nonneg _) (by positivity)
          _ = Real.sqrt C * K₁ := by ring
      have hR2 : ‖D.R j k a b z‖ ≤ Real.sqrt C * |Mk| := by
        show ‖D.psi j z * Real.sqrt (D.dens j z) * D.mat j k a b z‖ ≤ _
        rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        calc |D.psi j z| * Real.sqrt (D.dens j z) * |D.mat j k a b z|
            ≤ 1 * Real.sqrt C * |Mk| :=
              mul_le_mul (mul_le_mul hpsi_le hdens_le (Real.sqrt_nonneg _) zero_le_one)
                ((hMk z hlej).trans (le_abs_self _)) (abs_nonneg _) (by positivity)
          _ = Real.sqrt C * |Mk| := by ring
      calc ‖D.R j (D.Rstar i u) a b z * D.R j k a b z‖
          = ‖D.R j (D.Rstar i u) a b z‖ * ‖D.R j k a b z‖ := norm_mul _ _
        _ ≤ (Real.sqrt C * K₁) * (Real.sqrt C * |Mk|) :=
            mul_le_mul hR1 hR2 (norm_nonneg _)
              (by have := Real.sqrt_nonneg C; positivity)
        _ ≤ Kb := by rw [hKb]; linarith
    · rw [hzero z hz]
      simpa only [norm_zero] using hKbnn
  exact (integrable_of_continuousOn_of_bound hWopen hWbdd hcont hzero hbound).integrableOn

end RpairIntegrable

theorem BPair_Rstar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Work.Diff.STE.Bil (I := I) (M := M))
    (hu : ∀ a b : Fin (Module.finrank ℝ E), Continuous (u a b))
    (hk : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContinuousOn (D.mat j k a b) {z : Fin (Module.finrank ℝ E) → ℝ | D.χ j z ≠ 0}) :
    D.BPair (D.Rstar i u) k = Work.Diff.STE.B3Data.CPair i u (D.R i k) := by
  exact BPair_Rstar_of_integrable D i u k
    (fun j a b => rp_integrableOn_Rpair_term D i u k hu hk (dens_bound_sigma D) j a b)
    (fun a b => integrableOn_Cpair_term D i u k hu hk (dens_bound_sigma D) a b)
    (fun j => integrableOn_Npair_term D i u k hu hk (dens_bound_sigma D) j)

end Work.Diff.STE.B3
