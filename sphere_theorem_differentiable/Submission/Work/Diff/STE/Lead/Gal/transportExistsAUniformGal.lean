import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.CoeffDefs
import Submission.Work.Diff.STE.B3.MatGlob.abs_bilin_le_of_sandwich
import Submission.Work.Diff.STE.B3.transport_exists_cutoff
import Submission.Work.Diff.STE.B3.perR_props
import Submission.Work.Diff.STE.B3.perR_jet_bound
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.B3.iteratedFDeriv_le_of_pdVec
import Submission.Work.Diff.STE.B3.bg_window_aux
import Submission.Work.Diff.STE.Lead.Gal.clampedInvSymGal
import Submission.Work.Diff.STE.Lead.Gal.gfPairJetBoundGal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.Lead.Gal

open Work.Diff.STE.B3

set_option linter.unusedSectionVars false

section Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The coordinate-frame chart matrix of `h` is the value of `h` at the point `D.pt j z` on the
coordinate-frame vectors (definitional). -/
lemma Gf_eq_bilin (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b
      = h (D.pt j z) (cFrameAt (I := I) (M := M) D j z a) (cFrameAt (I := I) (M := M) D j z b) :=
  rfl

/-- The coordinate-frame chart matrix of the *background* `g₀` is the value of `g₀` at the point
`D.pt j z` on the coordinate-frame vectors (definitional). -/
lemma G0f_eq_bilin (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b
      = g₀.inner (D.pt j z) (cFrameAt (I := I) (M := M) D j z a)
          (cFrameAt (I := I) (M := M) D j z b) :=
  rfl

/-- The quadratic form of the coordinate-frame chart matrix of `h` is the value of `h` on the vector
`∑ a, ξ a • ∂_a`. -/
lemma Gf_quadForm (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (ξ : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ a, ∑ b, Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b * ξ a * ξ b)
      = h (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
          (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b) := by
  simp only [Gf_eq_bilin, map_sum, ContinuousLinearMap.sum_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The quadratic form of the coordinate-frame chart matrix of `g₀` is the value of `g₀` on the
vector `∑ a, ξ a • ∂_a`. -/
lemma G0f_quadForm (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (ξ : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b)
      = g₀.inner (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
          (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b) := by
  simp only [G0f_eq_bilin, map_sum, ContinuousLinearMap.sum_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **The window of `h`'s coordinate-frame chart matrix**, from the pinching `lam g₀ ≤ h ≤ K g₀` and
the two-sided bounds `mlo`, `Mhi` for the background chart matrix. -/
lemma Gf_window (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) {lam K mlo Mhi : ℝ} (hlam : 0 ≤ lam)
    (hK : 0 ≤ K)
    (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
    (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
    (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ)
    (hlo : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ, mlo * ∑ i, (ξ i) ^ 2
      ≤ ∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b)
    (hhi : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      (∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b)
        ≤ Mhi * ∑ i, (ξ i) ^ 2)
    (ξ : Fin (Module.finrank ℝ E) → ℝ) :
    (lam * mlo) * ∑ i, (ξ i) ^ 2
        ≤ ∑ a, ∑ b, Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b * ξ a * ξ b
      ∧ (∑ a, ∑ b, Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b * ξ a * ξ b)
        ≤ (K * Mhi) * ∑ i, (ξ i) ^ 2 := by
  have hV := Gf_quadForm (I := I) (M := M) D h j z ξ
  have hV0 := G0f_quadForm (I := I) (M := M) D j z ξ
  constructor
  · rw [hV]
    calc (lam * mlo) * ∑ i, (ξ i) ^ 2
        = lam * (mlo * ∑ i, (ξ i) ^ 2) := by ring
      _ ≤ lam * (∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b) :=
          mul_le_mul_of_nonneg_left (hlo ξ) hlam
      _ = lam * g₀.inner (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
            (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b) := by rw [hV0]
      _ ≤ h (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
            (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b) :=
          hell (D.pt j z) _
  · rw [hV]
    calc h (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
          (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b)
        ≤ K * g₀.inner (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
            (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b) := hub (D.pt j z) _
      _ = K * (∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b) := by rw [hV0]
      _ ≤ K * (Mhi * ∑ i, (ξ i) ^ 2) := mul_le_mul_of_nonneg_left (hhi ξ) hK
      _ = (K * Mhi) * ∑ i, (ξ i) ^ 2 := by ring

/-- The sum of the squares of the coordinates of a standard basis vector is `1`. -/
lemma sum_single_sq {n : ℕ} (a : Fin n) :
    (∑ i, ((Pi.single a (1 : ℝ) : Fin n → ℝ) i) ^ 2) = 1 := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro i _ hi; rw [Pi.single_eq_of_ne hi]; norm_num
  · intro h; exact absurd (Finset.mem_univ a) h

/-- A double sum against a standard basis vector collapses to the corresponding entry. -/
lemma sum_single_single {n : ℕ} (G : Fin n → Fin n → ℝ) (a : Fin n) :
    (∑ i, ∑ j, G i j * (Pi.single a (1 : ℝ) : Fin n → ℝ) i
        * (Pi.single a (1 : ℝ) : Fin n → ℝ) j) = G a a := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single a]
    · simp
    · intro j _ hj; rw [Pi.single_eq_of_ne hj]; ring
    · intro h; exact absurd (Finset.mem_univ a) h
  · intro i _ hi; rw [Pi.single_eq_of_ne hi]; simp
  · intro h; exact absurd (Finset.mem_univ a) h

/-- The sum of a standard basis vector against the coordinate frame is the corresponding frame
vector. -/
lemma sum_single_smul_cFrame (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (a : Fin (Module.finrank ℝ E)) :
    (∑ i, (Pi.single a (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ) i
        • cFrameAt (I := I) (M := M) D j z i)
      = cFrameAt (I := I) (M := M) D j z a := by
  classical
  rw [Finset.sum_eq_single a]
  · simp
  · intro i _ hi; rw [Pi.single_eq_of_ne hi]; simp
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **An entrywise bound for the coordinate-frame chart matrix of `h`**, from the pinching and the
upper bound `Mhi` for the background chart matrix. -/
lemma Gf_entry_bound (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    {lam K Mhi : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K)
    (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
    (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
    (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ)
    (hhi : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      (∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b)
        ≤ Mhi * ∑ i, (ξ i) ^ 2) :
    ∀ a b : Fin (Module.finrank ℝ E),
      |Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b| ≤ 2 * K * Mhi := by
  intro a b
  have hsand := Work.Diff.STE.B3.MatGlob.abs_bilin_le_of_sandwich (I := I) (M := M)
    (g₀ := g₀) (h := h) (le_of_lt hlam) hK hsym hell hub (D.pt j z)
    (cFrameAt (I := I) (M := M) D j z a) (cFrameAt (I := I) (M := M) D j z b)
  have hdiag : ∀ c : Fin (Module.finrank ℝ E),
      g₀.inner (D.pt j z) (cFrameAt (I := I) (M := M) D j z c)
        (cFrameAt (I := I) (M := M) D j z c) ≤ Mhi := by
    intro c
    have hξ := hhi (Pi.single c (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ)
    rw [G0f_quadForm (I := I) (M := M) D j z (Pi.single c (1 : ℝ)),
      sum_single_smul_cFrame, sum_single_sq, mul_one] at hξ
    exact hξ
  have h1 := hdiag a
  have h2 := hdiag b
  calc |Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b|
      = |h (D.pt j z) (cFrameAt (I := I) (M := M) D j z a)
          (cFrameAt (I := I) (M := M) D j z b)| := by
        rw [Gf_eq_bilin]
    _ ≤ K * (g₀.inner (D.pt j z) (cFrameAt (I := I) (M := M) D j z a)
            (cFrameAt (I := I) (M := M) D j z a)
          + g₀.inner (D.pt j z) (cFrameAt (I := I) (M := M) D j z b)
            (cFrameAt (I := I) (M := M) D j z b)) := hsand
    _ ≤ K * (Mhi + Mhi) := by
        have : (0 : ℝ) ≤ K := hK
        nlinarith
    _ = 2 * K * Mhi := by ring

/-- **Smoothness of the coordinate-frame chart matrix of `h` in the chart at `x₀ j`**, on the
region where the chart inverse is genuine. -/
lemma Gf_contDiffOn_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b)
      {z : Fin (Module.finrank ℝ E) → ℝ |
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target} := by
  let F : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun y i j' => h ((extChartAt I (D.x₀ j)).symm y)
      (Submission.Geodesic.frameVector (I := I) (D.x₀ j) ((extChartAt I (D.x₀ j)).symm y)
        (Work.Diff.EXT.bB (E := E) i))
      (Submission.Geodesic.frameVector (I := I) (D.x₀ j) ((extChartAt I (D.x₀ j)).symm y)
        (Work.Diff.EXT.bB (E := E) j'))
  have h0 : ContDiffOn ℝ (⊤ : ℕ∞) F (extChartAt I (D.x₀ j)).target := hsmooth (D.x₀ j)
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : E => F y a) (extChartAt I (D.x₀ j)).target :=
    (contDiffOn_pi.mp h0) a
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : E => F y a b) (extChartAt I (D.x₀ j)).target :=
    (contDiffOn_pi.mp h1) b
  refine h2.comp ?_ ?_
  · exact (contDiff_flatToE (I := I) (x₀ := D.x₀ j)).contDiffOn
  · intro z hz
    simpa only [Set.mem_setOf_eq, Work.Diff.STE.B3.yf] using hz

/-- At every point, one of the normalised weights is at least `1 / √(card ι₀)`. -/
lemma exists_zeta_dominant (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j₀ : ι₀)
    (p : M) : ∃ j : ι₀, 1 / Real.sqrt (Fintype.card ι₀) ≤ D.ζ j p := by
  classical
  by_contra hcon
  push_neg at hcon
  have hcard : 0 < Fintype.card ι₀ := Fintype.card_pos_iff.mpr ⟨j₀⟩
  have hcardR : (0 : ℝ) < (Fintype.card ι₀ : ℝ) := by exact_mod_cast hcard
  have htpos : 0 < 1 / Real.sqrt (Fintype.card ι₀) :=
    one_div_pos.mpr (Real.sqrt_pos.mpr hcardR)
  have hlt : ∑ j : ι₀, (D.ζ j p) ^ 2 < ∑ _j : ι₀, (1 / Real.sqrt (Fintype.card ι₀)) ^ 2 := by
    refine Finset.sum_lt_sum (fun j _ => ?_) ⟨j₀, Finset.mem_univ _, ?_⟩
    · exact le_of_lt (pow_lt_pow_left₀ (hcon j) (D.hζnn j p) (by norm_num))
    · exact pow_lt_pow_left₀ (hcon j₀) (D.hζnn j₀ p) (by norm_num)
  have hsum : ∑ _j : ι₀, (1 / Real.sqrt (Fintype.card ι₀)) ^ 2 = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hne : (Fintype.card ι₀ : ℝ) ≠ 0 := ne_of_gt hcardR
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hcardR)]
    field_simp
  rw [hsum] at hlt
  have hsq := D.hζsq p
  linarith

/-- Iterated derivatives of a `C^∞` function are uniformly bounded on a compact set. -/
lemma exists_bound_iteratedFDeriv_compact {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : (Fin n → ℝ) → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) :
    ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : ℕ), i ≤ m → ∀ z ∈ K, ‖iteratedFDeriv ℝ i f z‖ ≤ C := by
  intro m
  have hcont : ∀ i : ℕ, Continuous fun z : Fin n → ℝ => ‖iteratedFDeriv ℝ i f z‖ := fun i =>
    (hf.continuous_iteratedFDeriv
      (WithTop.coe_le_coe.mpr le_top : ((i : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).norm
  choose B hB using fun i : ℕ => hK.exists_bound_of_continuousOn (hcont i).continuousOn
  refine ⟨∑ i ∈ Finset.range (m + 1), |B i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro i hi z hz
  have hb : ‖iteratedFDeriv ℝ i f z‖ ≤ B i := by
    have h := hB i z hz
    rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
  exact (hb.trans (le_abs_self (B i))).trans
    (Finset.single_le_sum (f := fun i => |B i|) (fun j _ => abs_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))

/-- A product of a function that is `C^∞` on an open set with a globally `C^∞` function whose
closed support lies in that set is globally `C^∞`. -/
lemma contDiff_mul_of_tsupport_subset' {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {f g : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hsupp : tsupport g ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => f z * g z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ U
  · exact (hf.contDiffAt (hU.mem_nhds hz)).mul hg.contDiffAt
  · have hg0 : g =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      have hz' : z ∉ tsupport g := fun h => hz (hsupp h)
      filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hz'] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hfg : (fun y => f y * g y) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [hg0] with y hy
      rw [hy, mul_zero]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hfg

/-- A smooth bump equal to `1` on the closed ball of radius `r` and supported in the open ball of
radius `R > r`. -/
lemma exists_smooth_bump (n : ℕ) {r R : ℝ} (hrR : r < R) :
    ∃ θ : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ ∧ (∀ z, 0 ≤ θ z) ∧
      (∀ z : Fin n → ℝ, ‖z‖ ≤ r → θ z = 1) ∧
      tsupport θ ⊆ Metric.ball (0 : Fin n → ℝ) R := by
  obtain ⟨η, hsm, hnn, hone, hsupp⟩ := transport_exists_cutoff
    (K := Metric.closedBall (0 : Fin n → ℝ) r) (U := Metric.ball (0 : Fin n → ℝ) R)
    (isCompact_closedBall _ _) Metric.isOpen_ball (by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]
      linarith)
  exact ⟨η, hsm, hnn, fun z hz => hone z (by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hz), hsupp⟩

/-- The iterated derivatives of a constant function are bounded by the norm of the constant. -/
lemma norm_iteratedFDeriv_const_le {n m : ℕ} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] (c : W) (z : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ m (fun _ : Fin n → ℝ => c) z‖ ≤ ‖c‖ := by
  rcases m with _ | m
  · refine ContinuousMultilinearMap.opNorm_le_bound (M := ‖c‖) (by positivity) fun v => ?_
    rw [iteratedFDeriv_zero_apply (𝕜 := ℝ) (f := fun _ : Fin n → ℝ => c) (x := z)]
    simp
  · rw [iteratedFDeriv_succ_const]
    simp

/-- **From `pdVec`-bounds to `iteratedFDeriv`-bounds** at a point, for a complex-valued function
that is smooth there. -/
lemma iteratedFDeriv_le_of_pdVec_bound_at {n m : ℕ} {f : (Fin n → ℝ) → ℂ} {z : Fin n → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (β : Fin m → Fin n), ‖pdVec m β f z‖ ≤ C) :
    ‖iteratedFDeriv ℝ m f z‖ ≤ (n : ℝ) ^ m * C := by
  refine norm_multilinear_le_of_basis (iteratedFDeriv ℝ m f z) hC ?_
  intro γ
  rw [← pdVec_eq_iteratedFDeriv_at hf m γ]
  exact h γ

/-- **The jet bound for the coordinate-frame chart matrix of `h` on the enlarged ball**, by the
covering argument: at every point one of the normalised weights is at least `1/√(card ι₀)`. -/
lemma Gf_jet_bound_ball
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (htgt : ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + ρ →
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (K : ℝ) (hK : 0 ≤ K)
        (hjet : ∀ (i : ι₀) (m : ℕ) (hm : m ≤ k + 1)
          (β : Fin m → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ) (c d : Fin (Module.finrank ℝ E)),
          ‖z‖ ≤ 2 * D.σ i →
          ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K),
        ∀ (j : ι₀) (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)),
          ‖z‖ ≤ 2 * D.σ j + ρ →
          ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b : ℝ) : ℂ)) z‖ ≤ C * K := by
  classical
  have hpair : ∀ j j' : ι₀, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (K : ℝ) (hK : 0 ≤ K)
        (hjet : ∀ (i : ι₀) (m : ℕ) (hm : m ≤ k + 1)
          (β : Fin m → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ) (c d : Fin (Module.finrank ℝ E)),
          ‖z‖ ≤ 2 * D.σ i →
          ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K),
        ∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)),
          ‖z‖ ≤ 2 * D.σ j + ρ →
          1 / Real.sqrt (Fintype.card ι₀) ≤ D.ζ j' (D.pt j z) →
          ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b : ℝ) : ℂ)) z‖ ≤ C * K := by
    intro j j'
    exact Gf_pair_jet_bound (I := I) (M := M) D k j j' ρ hρ (fun z hz => htgt j z hz)
  choose Cpair hCpair using hpair
  refine ⟨∑ j : ι₀, ∑ j' : ι₀, Cpair j j', ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun j' _ => (hCpair j j').1
  · intro h hsym hsmooth K hK hjet j m hm β z a b hz
    obtain ⟨j', hj'⟩ := exists_zeta_dominant (I := I) (M := M) D j (D.pt j z)
    have h1 := (hCpair j j').2 h hsym hsmooth K hK hjet m hm β z a b hz hj'
    have h2 : Cpair j j' ≤ ∑ j : ι₀, ∑ j' : ι₀, Cpair j j' := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => ∑ j' : ι₀, Cpair j j')
        (fun j _ => Finset.sum_nonneg fun j' _ => (hCpair j j').1) (Finset.mem_univ j))
      exact Finset.single_le_sum (f := fun j' => Cpair j j')
        (fun j' _ => (hCpair j j').1) (Finset.mem_univ j')
    calc ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b : ℝ) : ℂ)) z‖
        ≤ Cpair j j' * K := h1
      _ ≤ (∑ j : ι₀, ∑ j' : ι₀, Cpair j j') * K :=
          mul_le_mul_of_nonneg_right h2 hK

/-- Jet congruence: functions that agree near a point have the same iterated derivatives there. -/
lemma iteratedFDeriv_congr_W {n m : ℕ} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {f g : (Fin n → ℝ) → W} {z : Fin n → ℝ} (h : f =ᶠ[𝓝 z] g) :
    iteratedFDeriv ℝ m f z = iteratedFDeriv ℝ m g z :=
  (h.iteratedFDeriv ℝ m).eq_of_nhds

/-- The norm of the `0`-th iterated derivative is the norm of the function. -/
lemma norm_iteratedFDeriv_zero_eq {n : ℕ} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] (f : (Fin n → ℝ) → W) (z : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ 0 f z‖ = ‖f z‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousMultilinearMap.opNorm_le_bound (M := ‖f z‖) (by positivity) fun v => ?_
    rw [iteratedFDeriv_zero_apply (𝕜 := ℝ) (f := f) (x := z)]
    simp
  · have h := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ 0 f z)
      (fun i : Fin 0 => Fin.elim0 i)
    rw [iteratedFDeriv_zero_apply (𝕜 := ℝ) (f := f) (x := z)] at h
    simpa using h

/-- Jet bound for a product from jet bounds of the two factors. -/
lemma norm_iteratedFDeriv_mul_le_of_bounds {n m : ℕ} {f g : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {M N : ℝ} (hM : ∀ i : ℕ, i ≤ m → ‖iteratedFDeriv ℝ i f z‖ ≤ M)
    (hN : ∀ i : ℕ, i ≤ m → ‖iteratedFDeriv ℝ i g z‖ ≤ N) :
    ‖iteratedFDeriv ℝ m (fun y => f y * g y) z‖ ≤ 2 ^ m * M * N := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le m))
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (Nat.zero_le m))
  refine (norm_iteratedFDeriv_mul_le hf hg z
    (WithTop.coe_le_coe.mpr le_top : ((m : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).trans ?_
  have hterm : ∀ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f z‖
      * ‖iteratedFDeriv ℝ (m - i) g z‖ ≤ (m.choose i : ℝ) * (M * N) := by
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : (0 : ℝ) ≤ (m.choose i : ℝ) := by positivity
    calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f z‖ * ‖iteratedFDeriv ℝ (m - i) g z‖
        ≤ (m.choose i : ℝ) * M * N :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hM i hi') h1) (hN (m - i) (by omega))
            (norm_nonneg _) (by positivity)
      _ = (m.choose i : ℝ) * (M * N) := by ring
  calc ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f z‖
        * ‖iteratedFDeriv ℝ (m - i) g z‖
      ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (M * N) :=
        Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) * (M * N) := by
        rw [Finset.sum_mul]
    _ = 2 ^ m * (M * N) := by
        rw [← Nat.cast_sum, Nat.sum_range_choose]
        norm_num
    _ = 2 ^ m * M * N := by ring

/-- The complexification of a real function has the same jet norms. -/
lemma norm_iteratedFDeriv_ofReal_eq {n m : ℕ} {f : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) :
    ‖iteratedFDeriv ℝ m (fun y => ((f y : ℝ) : ℂ)) z‖ = ‖iteratedFDeriv ℝ m f z‖ := by
  have hfun : (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) = ⇑Complex.ofRealLI ∘ f := by
    funext y
    exact (Complex.ofRealLI_apply (f y)).symm
  have h1 := LinearIsometry.norm_iteratedFDeriv_comp_left (g := Complex.ofRealLI) (f := f) hf
    (WithTop.coe_le_coe.mpr le_top : ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  rw [hfun]
  exact h1

/-- Reindexing: the quadratic form of a finite sum of matrices is the sum of the quadratic
forms. -/
lemma sum_sum_mul_eq {n : ℕ} {ι : Type*} (s : Finset ι)
    (c : ι → Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) :
    (∑ p, ∑ q, (∑ m ∈ s, c m p q) * ξ p * ξ q)
      = ∑ m ∈ s, ∑ p, ∑ q, c m p q * ξ p * ξ q := by
  have h1 : (∑ p, ∑ q, (∑ m ∈ s, c m p q) * ξ p * ξ q)
      = (∑ p, ∑ q, ∑ m ∈ s, c m p q * ξ p * ξ q) :=
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
      rw [Finset.sum_mul, Finset.sum_mul]
  have h2 : (∑ p, ∑ q, ∑ m ∈ s, c m p q * ξ p * ξ q)
      = (∑ q, ∑ p, ∑ m ∈ s, c m p q * ξ p * ξ q) :=
    Finset.sum_comm (f := fun p q => ∑ m ∈ s, c m p q * ξ p * ξ q)
  have h3 : (∑ q, ∑ p, ∑ m ∈ s, c m p q * ξ p * ξ q)
      = (∑ q, ∑ m ∈ s, ∑ p, c m p q * ξ p * ξ q) :=
    Finset.sum_congr rfl fun q _ => Finset.sum_comm (f := fun p m => c m p q * ξ p * ξ q)
  have h4 : (∑ q, ∑ m ∈ s, ∑ p, c m p q * ξ p * ξ q)
      = (∑ m ∈ s, ∑ q, ∑ p, c m p q * ξ p * ξ q) :=
    Finset.sum_comm (f := fun q m => ∑ p, c m p q * ξ p * ξ q)
  have h5 : (∑ m ∈ s, ∑ q, ∑ p, c m p q * ξ p * ξ q)
      = (∑ m ∈ s, ∑ p, ∑ q, c m p q * ξ p * ξ q) :=
    Finset.sum_congr rfl fun m _ => Finset.sum_comm (f := fun q p => c m p q * ξ p * ξ q)
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- The quadratic form of the identity matrix is the sum of the squares. -/
lemma sum_ite_mul_eq {n : ℕ} (c : ℝ) (ξ : Fin n → ℝ) :
    (∑ p, ∑ q, (if p = q then c else 0) * ξ p * ξ q) = c * ∑ i, (ξ i) ^ 2 := by
  calc (∑ p, ∑ q, (if p = q then c else 0) * ξ p * ξ q)
      = ∑ p, c * ξ p * ξ p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_eq_single p]
        · simp
        · intro q _ hq; rw [if_neg (Ne.symm hq)]; ring
        · intro h; exact absurd (Finset.mem_univ p) h
    _ = c * ∑ i, (ξ i) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring

/-- **Localisation of the lattice translates** (copy of the private version of
`Work.Diff.STE.B3.perR_jet_bound`). -/
lemma perR_tsum_local_W {n : ℕ} {R : ℝ} (hR : R ≤ 1/2) {f : (Fin n → ℝ) → ℝ}
    (hsupp : Function.support f ⊆ Metric.ball 0 R) {z z' : Fin n → ℝ}
    (hz' : z' ∈ Metric.ball z (1/2)) {m : Fin n → ℤ} (hm : m ∉ perRbox z) :
    f (z' + perRlattice m) = 0 := by
  by_contra hne
  have hmem : z' + perRlattice m ∈ Function.support f := hne
  have hlt : ‖z' + perRlattice m‖ < R := by
    have h := hsupp hmem
    simpa [Metric.mem_ball, dist_eq_norm] using h
  have hz'l : ‖z' - z‖ < 1/2 := by
    have h := hz'
    simpa [Metric.mem_ball, dist_eq_norm] using h
  refine hm ?_
  rw [perRbox_mem]
  intro i
  have h1' : |z' i + (m i : ℝ)| < R := by
    have h := norm_le_pi_norm (z' + perRlattice m) i
    rw [Real.norm_eq_abs] at h
    have := lt_of_le_of_lt h hlt
    simpa [perRlattice] using this
  have h2' : |z' i - z i| < 1/2 := by
    have h := norm_le_pi_norm (z' - z) i
    rw [Real.norm_eq_abs] at h
    have := lt_of_le_of_lt h hz'l
    simpa using this
  have hA : |z i - z' i| < 1/2 := by rw [abs_sub_comm]; exact h2'
  have h3 : |z i + (m i : ℝ)| < 1 := by
    have heq : z i + (m i : ℝ) = (z i - z' i) + (z' i + (m i : ℝ)) := by ring
    rw [heq]
    calc |(z i - z' i) + (z' i + (m i : ℝ))|
        ≤ |z i - z' i| + |z' i + (m i : ℝ)| := abs_add_le _ _
      _ < R + 1/2 := by linarith [add_lt_add hA h1']
      _ ≤ 1 := by linarith
  have hlo : ((-Int.floor (z i) - 2 : ℤ) : ℝ) < (m i : ℝ) := by
    have h := (abs_lt.mp h3).1
    have hf := Int.lt_floor_add_one (z i)
    push_cast
    linarith
  have hhi : (m i : ℝ) < ((-Int.floor (z i) + 1 : ℤ) : ℝ) := by
    have h := (abs_lt.mp h3).2
    have hf := Int.floor_le (z i)
    push_cast
    linarith
  constructor
  · have hh : (-Int.floor (z i) - 2 : ℤ) < m i := by exact_mod_cast hlo
    omega
  · have hh : m i < (-Int.floor (z i) + 1 : ℤ) := by exact_mod_cast hhi
    omega

/-- The norm of a standard basis vector of `Fin n → ℝ` in the sup norm. -/
lemma norm_pi_single {n : ℕ} (i : Fin n) (c : ℝ) :
    ‖(Pi.single i c : Fin n → ℝ)‖ = ‖c‖ := by
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg c)).mpr fun j => ?_
    by_cases h : j = i
    · subst h; simp
    · rw [Pi.single_eq_of_ne h]; simp
  · have h := norm_le_pi_norm (Pi.single i c : Fin n → ℝ) i
    simpa using h

/-- The projection of a matrix onto one entry, as a continuous linear map. -/
noncomputable def projCLM {n : ℕ} (a b : Fin n) : (Fin n → Fin n → ℝ) →L[ℝ] ℝ :=
  ((LinearMap.proj (φ := fun _ : Fin n => ℝ) b).comp
      (LinearMap.proj (φ := fun _ : Fin n => Fin n → ℝ) a)).toContinuousLinearMap

lemma projCLM_apply {n : ℕ} (a b : Fin n) (M : Fin n → Fin n → ℝ) : projCLM a b M = M a b :=
  rfl

/-- The jet norm of a Pi-type-valued function is bounded by the jet norms of its components. -/
lemma iteratedFDeriv_pi_le {N n : ℕ} {g : (Fin N → ℝ) → (Fin n → Fin n → ℝ)}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {z : Fin N → ℝ} {i : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ (a b : Fin n), ‖iteratedFDeriv ℝ i (fun y => g y a b) z‖ ≤ B) :
    ‖iteratedFDeriv ℝ i g z‖ ≤ B := by
  have hproj : ∀ (a b : Fin n), iteratedFDeriv ℝ i (fun y => g y a b) z
      = (projCLM a b).compContinuousMultilinearMap (iteratedFDeriv ℝ i g z) := by
    intro a b
    rw [show (fun y : Fin N → ℝ => g y a b) = ⇑(projCLM a b) ∘ g from rfl]
    exact ContinuousLinearMap.iteratedFDeriv_comp_left (projCLM a b) (f := g) (x := z) hg.contDiffAt
      (WithTop.coe_le_coe.mpr le_top : ((i : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  refine ContinuousMultilinearMap.opNorm_le_bound (M := B) hB fun v => ?_
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hB (Finset.prod_nonneg fun i _ => norm_nonneg _))]
  intro a
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hB (Finset.prod_nonneg fun i _ => norm_nonneg _))]
  intro b
  have hval : (iteratedFDeriv ℝ i g z v) a b
      = (iteratedFDeriv ℝ i (fun y => g y a b) z) v := by
    rw [hproj a b]
    rfl
  rw [hval]
  exact le_trans (ContinuousMultilinearMap.le_opNorm _ v)
    (mul_le_mul_of_nonneg_right (h a b) (Finset.prod_nonneg fun j _ => norm_nonneg _))

/-- **The chain rule bound for a smooth matrix-valued function composed with a smooth function of
the entries**: the jets of `z ↦ Φ (f z) p q` are bounded by a constant times the jets of `Φ` on the
entry box and the (entrywise) jets of `f`. -/
theorem matrix_comp_jet_le_W (n N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ)) (p q : Fin n)
        (hΦ : ContDiff ℝ (⊤ : ℕ∞) (fun G => Φ G p q))
        (E CΦ B : ℝ) (hE : 0 ≤ E) (hCΦ : 0 ≤ CΦ) (hB : 1 ≤ B)
        (f : (Fin N → ℝ) → (Fin n → Fin n → ℝ))
        (hf : ∀ a b : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun z => f z a b))
        (z : Fin N → ℝ)
        (hΦjet : ∀ (G : Fin n → Fin n → ℝ), (∀ a b, |G a b| ≤ E) →
            ∀ j : ℕ, j ≤ k → ‖iteratedFDeriv ℝ j (fun G' => Φ G' p q) G‖ ≤ CΦ)
        (hfjet : ∀ (a b : Fin n) (j : ℕ), j ≤ k →
            ‖iteratedFDeriv ℝ j (fun y => f y a b) z‖ ≤ B)
        (hfB : ∀ a b : Fin n, |f z a b| ≤ E)
        (j : ℕ) (hj : j ≤ k),
        ‖iteratedFDeriv ℝ j (fun z => Φ (f z) p q) z‖ ≤ C * CΦ * B ^ k := by
  refine ⟨(Nat.factorial k : ℝ) + 1, by positivity, ?_⟩
  intro Φ p q hΦ E CΦ B hE hCΦ hB f hf z hΦjet hfjet hfB j hj
  have hfM : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_pi' fun a => contDiff_pi' fun b => hf a b
  have hMjet : ∀ i : ℕ, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i f z‖ ≤ B ^ i := by
    intro i hi hij
    have h1 : ‖iteratedFDeriv ℝ i f z‖ ≤ B :=
      iteratedFDeriv_pi_le hfM (by linarith) (fun a b => hfjet a b i (by omega))
    calc ‖iteratedFDeriv ℝ i f z‖ ≤ B := h1
      _ = B ^ 1 := (pow_one B).symm
      _ ≤ B ^ i := pow_le_pow_right₀ hB hi
  have hmain := norm_iteratedFDeriv_comp_le (𝕜 := ℝ)
    (g := fun G : (Fin n → Fin n → ℝ) => Φ G p q) (f := f) hΦ hfM
    (WithTop.coe_le_coe.mpr le_top : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
    z (C := CΦ) (D := B) (fun i hi => hΦjet (f z) hfB i (by omega)) hMjet
  have hjR : (Nat.factorial j : ℝ) ≤ (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_le hj
  have hBk : (0:ℝ) ≤ B ^ k := by positivity
  calc ‖iteratedFDeriv ℝ j (fun z => Φ (f z) p q) z‖
        ≤ (Nat.factorial j : ℝ) * CΦ * B ^ j := hmain
    _ ≤ (Nat.factorial k : ℝ) * CΦ * B ^ k := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hjR hCΦ)
          (pow_le_pow_right₀ hB hj) (by positivity) (by positivity)
    _ ≤ ((Nat.factorial k : ℝ) + 1) * CΦ * B ^ k := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hCΦ) hBk
        linarith

end Aux

theorem transport_exists_A_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) :
    ∀ (lam K : ℝ), 0 < lam → 0 < K →
      ∃ (lam' C : ℝ), 0 < lam' ∧ 0 ≤ C ∧
        ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
          (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
          (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
          (j : ι₀)
          (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
          (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
          (hjet : ∀ (i : ι₀) (m : ℕ) (hm : m ≤ k + 1)
            (β : Fin m → Fin (Module.finrank ℝ E))
            (z : Fin (Module.finrank ℝ E) → ℝ) (c d : Fin (Module.finrank ℝ E)),
            ‖z‖ ≤ 2 * D.σ i →
            ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K),
          ∃ (A : (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) →
              Fin (Module.finrank ℝ E) → ℝ),
            (∀ z p q, A z p q = A z q p) ∧
            (∀ z (ξ : Fin (Module.finrank ℝ E) → ℝ),
              lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ p, ∑ q, A z p q * ξ p * ξ q) ∧
            (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin (Module.finrank ℝ E))
              (z : Fin (Module.finrank ℝ E) → ℝ) (p q : Fin (Module.finrank ℝ E)),
              ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                ((A y p q : ℝ) : ℂ)) z‖ ≤ C) ∧
            ContDiff ℝ ((⊤ : ENat) : WithTop ENat) A ∧
            Work.Diff.STE.Periodic1 A ∧
            (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j → ∀ p q,
              A z p q = ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q) := by
  classical
  intro lam K hlam hK
  -- the uniform background window
  obtain ⟨δ₀, mlo, Mhi, hδ₀pos, hmlopos, hMhipos, htgt₀, hlo₀, hhi₀⟩ :=
    bg_window_aux (I := I) (M := M) D
  set δ : ℝ := min δ₀ (1 / 8) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos (by norm_num)
  have hδle₀ : δ ≤ δ₀ := min_le_left _ _
  have hδle8 : δ ≤ 1 / 8 := min_le_right _ _
  have htgtδ : ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target :=
    fun j z hz => htgt₀ j z (by linarith)
  have htgtG : ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ / 2 →
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target :=
    fun j z hz => htgtδ j z (by linarith)
  obtain ⟨CJ, hCJnn, hCJ⟩ := Gf_jet_bound_ball (I := I) (M := M) D k (δ / 2) (by positivity) htgtG
  -- the cut-off functions, chosen once and for all as functions of the chart index
  have hb0 : ∀ j : ι₀, ∃ θ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) θ ∧ (∀ z, 0 ≤ θ z) ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j → θ z = 1) ∧
      tsupport θ ⊆ Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ / 2) :=
    fun j => exists_smooth_bump (Module.finrank ℝ E) (r := 2 * D.σ j) (R := 2 * D.σ j + δ / 2)
      (by linarith [hδpos])
  choose θ0 hθ0sm hθ0nn hθ0one hθ0tsup using hb0
  have hb1 : ∀ j : ι₀, ∃ θ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) θ ∧ (∀ z, 0 ≤ θ z) ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + 3 * δ / 4 → θ z = 1) ∧
      tsupport θ ⊆ Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ) :=
    fun j => exists_smooth_bump (Module.finrank ℝ E) (r := 2 * D.σ j + 3 * δ / 4)
      (R := 2 * D.σ j + δ) (by linarith [hδpos])
  choose θ1 hθ1sm hθ1nn hθ1one hθ1tsup using hb1
  -- jet and value bounds for the cut-offs
  have hM0e : ∀ j : ι₀, ∃ M : ℝ, 0 ≤ M ∧ ∀ (i : ℕ), i ≤ k →
      ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ / 2 →
        ‖iteratedFDeriv ℝ i (θ0 j) z‖ ≤ M := by
    intro j
    obtain ⟨M, hMnn, hM⟩ := exists_bound_iteratedFDeriv_compact (hθ0sm j)
      (isCompact_closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ / 2)) k
    exact ⟨M, hMnn, fun i hi z hz => hM i hi z (by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hz)⟩
  choose Mθ0 hMθ0nn hMθ0 using hM0e
  have hM1e : ∀ j : ι₀, ∃ M : ℝ, 0 ≤ M ∧ ∀ (i : ℕ), i ≤ k →
      ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ / 2 →
        ‖iteratedFDeriv ℝ i (θ1 j) z‖ ≤ M := by
    intro j
    obtain ⟨M, hMnn, hM⟩ := exists_bound_iteratedFDeriv_compact (hθ1sm j)
      (isCompact_closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ / 2)) k
    exact ⟨M, hMnn, fun i hi z hz => hM i hi z (by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hz)⟩
  choose Mθ1 hMθ1nn hMθ1 using hM1e
  have hM1ve : ∀ j : ι₀, ∃ M : ℝ, 0 ≤ M ∧ ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      ‖z‖ ≤ 2 * D.σ j + δ / 2 → |θ1 j z| ≤ M := by
    intro j
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Fin (Module.finrank ℝ E) → ℝ)
      (2 * D.σ j + δ / 2)).exists_bound_of_continuousOn
        (continuous_abs.comp (hθ1sm j).continuous).continuousOn
    exact ⟨|M|, abs_nonneg _, fun z hz => by
      have h := hM z (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz)
      have h' : |θ1 j z| ≤ M := by simpa using h
      exact h'.trans (le_abs_self M)⟩
  choose Mθ1v hMθ1vnn hMθ1v using hM1ve
  set M0 : ℝ := ∑ j : ι₀, Mθ0 j with hM0def
  set M1 : ℝ := ∑ j : ι₀, Mθ1 j with hM1def
  set M1v : ℝ := ∑ j : ι₀, Mθ1v j with hM1vdef
  have hM0nn : 0 ≤ M0 := by rw [hM0def]; exact Finset.sum_nonneg fun j _ => hMθ0nn j
  have hM1nn : 0 ≤ M1 := by rw [hM1def]; exact Finset.sum_nonneg fun j _ => hMθ1nn j
  have hM1vnn : 0 ≤ M1v := by rw [hM1vdef]; exact Finset.sum_nonneg fun j _ => hMθ1vnn j
  have hM0le : ∀ j : ι₀, Mθ0 j ≤ M0 := fun j => by
    rw [hM0def]
    exact Finset.single_le_sum (f := Mθ0) (fun i _ => hMθ0nn i) (Finset.mem_univ j)
  have hM1le : ∀ j : ι₀, Mθ1 j ≤ M1 := fun j => by
    rw [hM1def]
    exact Finset.single_le_sum (f := Mθ1) (fun i _ => hMθ1nn i) (Finset.mem_univ j)
  have hM1vle : ∀ j : ι₀, Mθ1v j ≤ M1v := fun j => by
    rw [hM1vdef]
    exact Finset.single_le_sum (f := Mθ1v) (fun i _ => hMθ1vnn i) (Finset.mem_univ j)
  -- the clamped inverse on the Loewner window
  obtain ⟨Kc, lam', CK, hlam'pos, hCKnn, hKcsm, hKcinv, hKcell, hKcsym, hKcjet⟩ :=
    clampedInv_sym_gal (Module.finrank ℝ E) k (lam * mlo) (K * Mhi) (M1v * (2 * K * Mhi))
      (mul_pos hlam hmlopos) (mul_pos hK hMhipos) (by positivity)
  obtain ⟨Ccomp, hCcompnn, hCcomp⟩ :=
    matrix_comp_jet_le_W (Module.finrank ℝ E) (Module.finrank ℝ E) k
  obtain ⟨Cper, hCpernn, hCper⟩ := perR_jet_bound (Module.finrank ℝ E) k
  set Cn : ℝ := ∑ i ∈ Finset.range (k + 1), (Module.finrank ℝ E : ℝ) ^ i with hCndef
  have hCnnn : 0 ≤ Cn := by rw [hCndef]; exact Finset.sum_nonneg fun i _ => by positivity
  have hCnle : ∀ m : ℕ, m ≤ k → (Module.finrank ℝ E : ℝ) ^ m ≤ Cn := fun m hm => by
    rw [hCndef]
    exact Finset.single_le_sum (f := fun i => (Module.finrank ℝ E : ℝ) ^ i)
      (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  set CG : ℝ := Cn * (CJ * K) with hCGdef
  have hCGnn : 0 ≤ CG := by rw [hCGdef]; positivity
  set BG : ℝ := max 1 (2 ^ k * M1 * CG) with hBGdef
  have hBGnn : 0 ≤ BG := le_trans zero_le_one (le_max_left _ _)
  have hBG1 : 1 ≤ BG := le_max_left _ _
  have hBGge : 2 ^ k * M1 * CG ≤ BG := le_max_right _ _
  set Bf : ℝ := 2 ^ k * M0 * (Ccomp * CK * BG ^ k + |lam'|) with hBfdef
  have hBfnn : 0 ≤ Bf := by rw [hBfdef]; positivity
  set Cfin : ℝ := |lam'| + Cper * Bf with hCfindef
  refine ⟨lam', Cfin, hlam'pos, ?_, ?_⟩
  · rw [hCfindef]; positivity
  · intro h hsym hsmooth j hell hub hjet
    set R : ℝ := 2 * D.σ j + δ / 2 with hRdef
    have hRhalf : R ≤ 1 / 2 := by
      rw [hRdef]; have hσ2 := D.hσ2 j; linarith
    have hRtgt : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ R →
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target :=
      fun z hz => htgtG j z (by rw [hRdef] at hz; linarith)
    have hU : IsOpen {z : Fin (Module.finrank ℝ E) → ℝ |
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target} :=
      (isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
        (contDiff_flatToE (I := I) (x₀ := D.x₀ j)).continuous
    have hθ1tgt : tsupport (θ1 j) ⊆ {z : Fin (Module.finrank ℝ E) → ℝ |
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target} := by
      intro z hz
      have hz' := hθ1tsup j hz
      rw [Metric.mem_ball, dist_zero_right] at hz'
      exact htgtδ j z (le_of_lt hz')
    have hθ1oneR : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ R → θ1 j z = 1 := by
      intro z hz
      refine hθ1one j z ?_
      rw [hRdef] at hz; linarith
    have hθ1oneN : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + 3 * δ / 4 →
        θ1 j z = 1 := hθ1one j
    obtain ⟨hper_cd, hper_per, hper_eq⟩ := perR_props (n := Module.finrank ℝ E) R hRhalf
    have hGfsm : ∀ a b, ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b)
        {z : Fin (Module.finrank ℝ E) → ℝ |
          Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target} :=
      fun a b => Gf_contDiffOn_target (I := I) (M := M) D h hsmooth j a b
    have hGgsm : ∀ a b, ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          θ1 j z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b) :=
      fun a b => by
        have h := contDiff_mul_of_tsupport_subset' (f := fun z : Fin (Module.finrank ℝ E) → ℝ =>
          Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b) (g := θ1 j) hU
          (hGfsm a b) (hθ1sm j) hθ1tgt
        simpa only [mul_comm] using h
    have hGfent : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ R → ∀ a b,
        |Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b| ≤ 2 * K * Mhi := by
      intro z hz a b
      refine Gf_entry_bound (I := I) (M := M) D h hsym hlam (le_of_lt hK) hell hub j z ?_ a b
      intro ξ
      exact hhi₀ j z (by rw [hRdef] at hz; linarith) ξ
    have hGfwin : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ R →
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          (lam * mlo) * ∑ i, (ξ i) ^ 2
              ≤ ∑ a, ∑ b, Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b * ξ a * ξ b ∧
            (∑ a, ∑ b, Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b * ξ a * ξ b)
              ≤ (K * Mhi) * ∑ i, (ξ i) ^ 2 := by
      intro z hz ξ
      refine Gf_window (I := I) (M := M) D h (le_of_lt hlam) (le_of_lt hK) hell hub j z ?_ ?_ ξ
      · intro ξ'; exact hlo₀ j z (by rw [hRdef] at hz; linarith) ξ'
      · intro ξ'; exact hhi₀ j z (by rw [hRdef] at hz; linarith) ξ'
    -- the jet bound for the chart matrix, complexified
    have hGfjetC : ∀ (m : ℕ), m ≤ k → ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ R →
        ∀ a b, ‖iteratedFDeriv ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b : ℝ) : ℂ)) z‖ ≤ CG := by
      intro m hm z hz a b
      have hcat : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b : ℝ) : ℂ)) z :=
        ((Complex.ofRealCLM.contDiff.contDiffOn).comp (hGfsm a b)
          (fun y _ => Set.mem_univ _)).contDiffAt (hU.mem_nhds (hRtgt z hz))
      have hpd : ∀ β : Fin m → Fin (Module.finrank ℝ E),
          ‖pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b : ℝ) : ℂ)) z‖ ≤ CJ * K := by
        intro β
        exact hCJ h hsym hsmooth K (le_of_lt hK) hjet j m hm β z a b
          (by rw [hRdef] at hz; linarith)
      calc ‖iteratedFDeriv ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b : ℝ) : ℂ)) z‖
          ≤ (Module.finrank ℝ E : ℝ) ^ m * (CJ * K) :=
            iteratedFDeriv_le_of_pdVec_bound_at hcat (by positivity) hpd
        _ ≤ Cn * (CJ * K) := mul_le_mul_of_nonneg_right (hCnle m hm) (by positivity)
        _ = CG := by rw [hCGdef]
    have hGfjet : ∀ (m : ℕ), m ≤ k → ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ R →
        ∀ a b, ‖iteratedFDeriv ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b) z‖ ≤ CG := by
      intro m hm z hz a b
      have hcat : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b) z :=
        (hGfsm a b).contDiffAt (hU.mem_nhds (hRtgt z hz))
      rw [← norm_iteratedFDeriv_ofReal_eq (m := m) (z := z) hcat]
      exact hGfjetC m hm z hz a b
    -- the jet bound for the globalised chart matrix
    have hGgjet : ∀ (m : ℕ), m ≤ k → ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ R →
        ∀ a b, ‖iteratedFDeriv ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b) z‖ ≤ BG := by
      intro m hm z hz a b
      have hzn : ‖z‖ < 2 * D.σ j + 3 * δ / 4 := by rw [hRdef] at hz; linarith
      have hzR : ‖z‖ ≤ 2 * D.σ j + δ / 2 := by rw [hRdef] at hz; linarith
      have hzev1 : ∀ᶠ y in 𝓝 z, θ1 j y = 1 := by
        filter_upwards [Metric.isOpen_ball.mem_nhds (show z ∈ Metric.ball
          (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 3 * δ / 4) by
            rw [Metric.mem_ball, dist_zero_right]; exact hzn)] with y hy
        exact hθ1oneN y (le_of_lt (by rw [Metric.mem_ball, dist_zero_right] at hy; exact hy))
      have hev1 : (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            θ1 j y * (θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b))
          =ᶠ[𝓝 z] (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b) := by
        filter_upwards [hzev1] with y hy
        rw [hy, one_mul]
      have hprod : ‖iteratedFDeriv ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          θ1 j y * (θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b)) z‖
            ≤ 2 ^ m * M1 * CG := by
        refine norm_iteratedFDeriv_mul_le_of_bounds (hθ1sm j) (hGgsm a b) ?_ ?_
        · intro i hi
          exact le_trans (hMθ1 j i (by omega) z hzR) (hM1le j)
        · intro i hi
          have hzev : (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b)
              =ᶠ[𝓝 z] (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b) := by
            filter_upwards [hzev1] with y hy
            rw [hy, one_mul]
          rw [iteratedFDeriv_congr_W hzev]
          exact hGfjet i (by omega) z hz a b
      rw [← iteratedFDeriv_congr_W hev1]
      refine hprod.trans ?_
      have hp : (2:ℝ) ^ m ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
      have h1 : (2:ℝ) ^ m * M1 * CG ≤ 2 ^ k * M1 * CG :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hM1nn) hCGnn
      exact h1.trans hBGge
    -- the jet bound for the clamped inverse
    have hKczjet : ∀ (m : ℕ), m ≤ k → ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ R →
        ∀ p q, ‖iteratedFDeriv ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            Kc (fun a b => θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b) p q) z‖
          ≤ Ccomp * CK * BG ^ k := by
      intro m hm z hz p q
      refine hCcomp (Kc) p q (hKcsm p q) (M1v * (2 * K * Mhi)) CK BG (by positivity) hCKnn hBG1
        (fun y a b => θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b)
        (fun a b => hGgsm a b) z ?_ ?_ ?_ m hm
      · intro G hG i hi
        exact hKcjet G hG i hi p q
      · intro a b i hi
        exact hGgjet i hi z hz a b
      · intro a b
        have h1 : |θ1 j z| ≤ M1v :=
          le_trans (hMθ1v j z (by rw [hRdef] at hz; linarith)) (hM1vle j)
        have h2 : |Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b| ≤ 2 * K * Mhi :=
          hGfent z hz a b
        calc |θ1 j z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b|
            = |θ1 j z| * |Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b| := abs_mul _ _
          _ ≤ M1v * (2 * K * Mhi) := mul_le_mul h1 h2 (abs_nonneg _) hM1vnn
    -- the coefficient matrix
    set cc : (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
      fun y p q => θ0 j y * (Kc (fun a b =>
        θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b) p q
          - (if p = q then lam' else 0)) with hccdef
    have hcc_sm : ∀ p q, ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin (Module.finrank ℝ E) → ℝ => cc y p q) := by
      intro p q
      rw [hccdef]
      refine (hθ0sm j).mul ?_
      refine ContDiff.sub ?_ contDiff_const
      exact (hKcsm p q).comp (contDiff_pi' fun a => contDiff_pi' fun b => hGgsm a b)
    have hcc_supp : ∀ p q, Function.support (fun y : Fin (Module.finrank ℝ E) → ℝ => cc y p q)
        ⊆ Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) R := by
      intro p q y hy
      have hy0 : θ0 j y ≠ 0 := by
        intro h0
        exact hy (by simp only [hccdef, h0, zero_mul])
      have h1 : y ∈ tsupport (θ0 j) := subset_closure hy0
      have h2 := hθ0tsup j h1
      rwa [hRdef]
    have hKcinner_sm : ∀ p q, ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          Kc (fun a b => θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b) p q) :=
      fun p q => (hKcsm p q).comp (contDiff_pi' fun a => contDiff_pi' fun b => hGgsm a b)
    have hcc_inner_sm : ∀ p q, ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          Kc (fun a b => θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b) p q
            - (if p = q then lam' else 0)) :=
      fun p q => (hKcinner_sm p q).sub contDiff_const
    have hcc_jet : ∀ p q, ∀ (m : ℕ), m ≤ k → ∀ w : Fin (Module.finrank ℝ E) → ℝ,
        ‖iteratedFDeriv ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ => cc y p q) w‖ ≤ Bf := by
      intro p q m hm w
      by_cases hw : ‖w‖ ≤ R
      · rw [hccdef]
        have hinner : ∀ (i : ℕ), i ≤ m → ‖iteratedFDeriv ℝ i
            (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              Kc (fun a b => θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b) p q
                - (if p = q then lam' else 0)) w‖ ≤ Ccomp * CK * BG ^ k + |lam'| := by
          intro i hi
          have h1 : (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              Kc (fun a b => θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b) p q
                - (if p = q then lam' else 0))
              = (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  Kc (fun a b => θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b) p q)
                + (fun _ : Fin (Module.finrank ℝ E) → ℝ => -((if p = q then lam' else 0))) := by
            funext y
            simp only [Pi.add_apply, sub_eq_add_neg]
          rw [h1, iteratedFDeriv_add_apply
            ((hKcinner_sm p q).contDiffAt.of_le
              (WithTop.coe_le_coe.mpr le_top : ((i : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)))
            ((contDiffAt_const (c := -((if p = q then lam' else 0)))).of_le
              (WithTop.coe_le_coe.mpr le_top : ((i : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)))]
          refine (norm_add_le _ _).trans ?_
          have h2 : ‖iteratedFDeriv ℝ i (fun _ : Fin (Module.finrank ℝ E) → ℝ =>
              -((if p = q then lam' else 0))) w‖ ≤ |lam'| := by
            refine (norm_iteratedFDeriv_const_le (-((if p = q then lam' else 0))) w).trans ?_
            rw [Real.norm_eq_abs, abs_neg]
            by_cases hpq : p = q
            · rw [if_pos hpq]
            · rw [if_neg hpq]; simpa using abs_nonneg lam'
          exact add_le_add (hKczjet i (by omega) w hw p q) h2
        calc ‖iteratedFDeriv ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ => θ0 j y *
              (Kc (fun a b => θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b) p q
                - (if p = q then lam' else 0))) w‖
            ≤ 2 ^ m * M0 * (Ccomp * CK * BG ^ k + |lam'|) :=
              norm_iteratedFDeriv_mul_le_of_bounds (hθ0sm j)
                (hcc_inner_sm p q) (fun i hi => le_trans
                  (hMθ0 j i (by omega) w (by rw [hRdef] at hw; linarith)) (hM0le j))
                (fun i hi => hinner i hi)
          _ ≤ 2 ^ k * M0 * (Ccomp * CK * BG ^ k + |lam'|) := by
              have h2m : (2:ℝ) ^ m ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
              have hb : 0 ≤ Ccomp * CK * BG ^ k + |lam'| := by positivity
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2m hM0nn) hb
          _ = Bf := by rw [hBfdef]
      · -- outside: the coefficient vanishes near `w`
        have hw' : R < ‖w‖ := lt_of_not_ge hw
        have hsub : ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖y - w‖ < ‖w‖ - R → cc y p q = 0 := by
          intro y hy
          by_contra hne
          have h1 : y ∈ tsupport (θ0 j) := by
            refine subset_closure ?_
            exact fun h0 => hne (by simp only [hccdef, h0, zero_mul])
          have h2 := hθ0tsup j h1
          rw [Metric.mem_ball, dist_zero_right] at h2
          have h3 : ‖w‖ - ‖y‖ ≤ ‖y - w‖ := by
            have h4 : ‖w‖ ≤ ‖y - w‖ + ‖y‖ := by
              calc ‖w‖ = ‖(w - y) + y‖ := by rw [sub_add_cancel]
                _ ≤ ‖w - y‖ + ‖y‖ := norm_add_le _ _
                _ = ‖y - w‖ + ‖y‖ := by rw [norm_sub_rev]
            linarith
          linarith
        have hev : (fun y : Fin (Module.finrank ℝ E) → ℝ => cc y p q) =ᶠ[𝓝 w] fun _ => 0 := by
          filter_upwards [Metric.ball_mem_nhds w (by linarith : (0:ℝ) < ‖w‖ - R)] with y hy
          exact hsub y (by rwa [Metric.mem_ball, dist_eq_norm] at hy)
        rw [iteratedFDeriv_congr_W hev]
        refine (norm_iteratedFDeriv_const_le (0 : ℝ) w).trans ?_
        simpa using hBfnn
    -- the pointwise finite-sum form of the periodisation
    have hcc_fin : ∀ (z : Fin (Module.finrank ℝ E) → ℝ) (p q : Fin (Module.finrank ℝ E)),
        perR (fun y => cc y p q) z = ∑ m ∈ perRbox z, cc (z + perRlattice m) p q := by
      intro z p q
      rw [perR_apply]
      exact tsum_eq_sum (s := perRbox z)
        (fun m hm => perR_tsum_local_W hRhalf (hcc_supp p q) (by simp) hm)
    refine ⟨fun z p q => (if p = q then lam' else 0) + perR (fun y => cc y p q) z, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- symmetry
      intro z p q
      have hKsym : ∀ y, Kc (fun a b => θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b) p q
          = Kc (fun a b => θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b) q p := by
        intro y
        exact hKcsym (fun a b => θ1 j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b)
          (fun a b => by rw [Gf_eq_bilin, Gf_eq_bilin, hsym]) p q
      have hsymA : (fun y => cc y p q) = (fun y => cc y q p) := by
        funext y
        simp only [hccdef]
        rw [hKsym y]
        by_cases hpq : p = q
        · rw [if_pos hpq, if_pos hpq.symm]
        · rw [if_neg hpq, if_neg (Ne.symm hpq)]
      show (if p = q then lam' else 0) + perR (fun y => cc y p q) z
          = (if q = p then lam' else 0) + perR (fun y => cc y q p) z
      rw [hsymA]
      simp only [eq_comm]
    · -- ellipticity
      intro z ξ
      have hquad : ∑ p, ∑ q, (perR (fun y => cc y p q) z) * ξ p * ξ q
          = ∑ m ∈ perRbox z, ∑ p, ∑ q, cc (z + perRlattice m) p q * ξ p * ξ q := by
        have h1 : ∀ p q, perR (fun y => cc y p q) z
            = ∑ m ∈ perRbox z, cc (z + perRlattice m) p q := fun p q => hcc_fin z p q
        simp only [h1]
        exact sum_sum_mul_eq (perRbox z) (fun m p q => cc (z + perRlattice m) p q) ξ
      have hQ : 0 ≤ ∑ p, ∑ q, (perR (fun y => cc y p q) z) * ξ p * ξ q := by
        rw [hquad]
        refine Finset.sum_nonneg fun m _ => ?_
        simp only [hccdef]
        have hfac : ∑ p, ∑ q, θ0 j (z + perRlattice m) *
              (Kc (fun a b => θ1 j (z + perRlattice m) *
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j (z + perRlattice m) a b) p q
                  - (if p = q then lam' else 0)) * ξ p * ξ q
            = θ0 j (z + perRlattice m) * (∑ p, ∑ q,
                (Kc (fun a b => θ1 j (z + perRlattice m) *
                  Work.Diff.STE.B3.Gf (I := I) (M := M) D h j (z + perRlattice m) a b) p q
                    - (if p = q then lam' else 0)) * ξ p * ξ q) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q _ => by ring
        rw [hfac]
        have hsplit : ∑ p, ∑ q,
              (Kc (fun a b => θ1 j (z + perRlattice m) *
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j (z + perRlattice m) a b) p q
                  - (if p = q then lam' else 0)) * ξ p * ξ q
            = (∑ p, ∑ q, Kc (fun a b => θ1 j (z + perRlattice m) *
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j (z + perRlattice m) a b) p q
                  * ξ p * ξ q)
              - (∑ p, ∑ q, (if p = q then lam' else 0) * ξ p * ξ q) := by
          have h1 : (∑ p, ∑ q,
                (Kc (fun a b => θ1 j (z + perRlattice m) *
                  Work.Diff.STE.B3.Gf (I := I) (M := M) D h j (z + perRlattice m) a b) p q
                    - (if p = q then lam' else 0)) * ξ p * ξ q)
              = ∑ p, ∑ q, ((Kc (fun a b => θ1 j (z + perRlattice m) *
                    Work.Diff.STE.B3.Gf (I := I) (M := M) D h j (z + perRlattice m) a b) p q
                      * ξ p * ξ q)
                  - ((if p = q then lam' else 0) * ξ p * ξ q)) :=
            Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
          have h2 : (∑ p, ∑ q, ((Kc (fun a b => θ1 j (z + perRlattice m) *
                    Work.Diff.STE.B3.Gf (I := I) (M := M) D h j (z + perRlattice m) a b) p q
                      * ξ p * ξ q)
                  - ((if p = q then lam' else 0) * ξ p * ξ q)))
              = (∑ p, ∑ q, Kc (fun a b => θ1 j (z + perRlattice m) *
                    Work.Diff.STE.B3.Gf (I := I) (M := M) D h j (z + perRlattice m) a b) p q
                      * ξ p * ξ q)
                - (∑ p, ∑ q, (if p = q then lam' else 0) * ξ p * ξ q) := by
            rw [show (∑ p, ∑ q, ((Kc (fun a b => θ1 j (z + perRlattice m) *
                      Work.Diff.STE.B3.Gf (I := I) (M := M) D h j (z + perRlattice m) a b) p q
                        * ξ p * ξ q)
                    - ((if p = q then lam' else 0) * ξ p * ξ q)))
                = ∑ p, ((∑ q, Kc (fun a b => θ1 j (z + perRlattice m) *
                        Work.Diff.STE.B3.Gf (I := I) (M := M) D h j (z + perRlattice m) a b) p q
                          * ξ p * ξ q)
                    - ∑ q, (if p = q then lam' else 0) * ξ p * ξ q) from by
                  refine Finset.sum_congr rfl fun p _ => ?_
                  rw [Finset.sum_sub_distrib]]
            rw [Finset.sum_sub_distrib]
          exact h1.trans h2
        rw [hsplit, sum_ite_mul_eq lam' ξ]
        refine mul_nonneg (hθ0nn j _) (sub_nonneg.mpr ?_)
        exact hKcell (fun a b => θ1 j (z + perRlattice m) *
          Work.Diff.STE.B3.Gf (I := I) (M := M) D h j (z + perRlattice m) a b) ξ
      have hconst : ∑ p, ∑ q, (if p = q then lam' else 0) * ξ p * ξ q
          = lam' * ∑ i, (ξ i) ^ 2 := sum_ite_mul_eq lam' ξ
      have hA : ∑ p, ∑ q, ((if p = q then lam' else 0) + perR (fun y => cc y p q) z)
            * ξ p * ξ q
          = (∑ p, ∑ q, (if p = q then lam' else 0) * ξ p * ξ q)
            + (∑ p, ∑ q, (perR (fun y => cc y p q) z) * ξ p * ξ q) := by
        have h1 : (∑ p, ∑ q, ((if p = q then lam' else 0) + perR (fun y => cc y p q) z)
              * ξ p * ξ q)
            = ∑ p, ∑ q, (((if p = q then lam' else 0) * ξ p * ξ q)
                + (perR (fun y => cc y p q) z * ξ p * ξ q)) :=
          Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
        have h2 : (∑ p, ∑ q, (((if p = q then lam' else 0) * ξ p * ξ q)
                + (perR (fun y => cc y p q) z * ξ p * ξ q)))
            = (∑ p, ∑ q, (if p = q then lam' else 0) * ξ p * ξ q)
              + (∑ p, ∑ q, (perR (fun y => cc y p q) z) * ξ p * ξ q) := by
          rw [show (∑ p, ∑ q, (((if p = q then lam' else 0) * ξ p * ξ q)
                  + (perR (fun y => cc y p q) z * ξ p * ξ q)))
              = ∑ p, ((∑ q, (if p = q then lam' else 0) * ξ p * ξ q)
                  + ∑ q, (perR (fun y => cc y p q) z * ξ p * ξ q)) from
                Finset.sum_congr rfl fun p _ => Finset.sum_add_distrib]
          exact Finset.sum_add_distrib
        exact h1.trans h2
      rw [hA, hconst]
      exact le_add_of_nonneg_right hQ
    · -- jets
      intro m hm β z p q
      have hPsm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((perR (fun y' => cc y' p q) y : ℝ) : ℂ)) z := by
        have h1 := hper_cd (fun y' => cc y' p q) (hcc_sm p q) (hcc_supp p q)
        have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((perR (fun y' => cc y' p q) y : ℝ) : ℂ)) := by
          rw [show (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                ((perR (fun y' => cc y' p q) y : ℝ) : ℂ))
              = ⇑Complex.ofRealCLM ∘ (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                (perR (fun y' => cc y' p q) y : ℝ)) from rfl]
          exact Complex.ofRealCLM.contDiff.comp h1
        exact h2.contDiffAt
      have hsmA : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            (((if p = q then lam' else 0) + perR (fun y' => cc y' p q) y : ℝ) : ℂ)) z := by
        have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((if p = q then lam' else 0) + perR (fun y' => cc y' p q) y : ℝ)) :=
          contDiff_const.add (hper_cd (fun y' => cc y' p q) (hcc_sm p q) (hcc_supp p q))
        exact (Complex.ofRealCLM.contDiff.comp h3).contDiffAt
      have h1 : ‖pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            (((if p = q then lam' else 0) + perR (fun y' => cc y' p q) y : ℝ) : ℂ)) z‖
          ≤ ‖iteratedFDeriv ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              (((if p = q then lam' else 0) + perR (fun y' => cc y' p q) y : ℝ) : ℂ)) z‖ := by
        rw [pdVec_eq_iteratedFDeriv_at hsmA m β]
        have h2 := ContinuousMultilinearMap.le_opNorm
          (iteratedFDeriv ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            (((if p = q then lam' else 0) + perR (fun y' => cc y' p q) y : ℝ) : ℂ)) z)
          (fun i : Fin m => (Pi.single (β i) (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ))
        have h3 : (∏ i : Fin m, ‖(fun j : Fin m =>
            (Pi.single (β j) (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ)) i‖) = 1 := by
          refine Finset.prod_eq_one fun i _ => ?_
          rw [norm_pi_single, norm_one]
        simpa [h3] using h2
      refine h1.trans ?_
      have hsplit : (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            (((if p = q then lam' else 0) + perR (fun y' => cc y' p q) y : ℝ) : ℂ))
          = (fun _ : Fin (Module.finrank ℝ E) → ℝ => (((if p = q then lam' else 0) : ℝ) : ℂ))
            + (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((perR (fun y' => cc y' p q) y : ℝ) : ℂ)) := by
        funext y
        push_cast
        rfl
      have hadd : iteratedFDeriv ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            (((if p = q then lam' else 0) + perR (fun y' => cc y' p q) y : ℝ) : ℂ)) z
          = iteratedFDeriv ℝ m (fun _ : Fin (Module.finrank ℝ E) → ℝ =>
              (((if p = q then lam' else 0) : ℝ) : ℂ)) z
            + iteratedFDeriv ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((perR (fun y' => cc y' p q) y : ℝ) : ℂ)) z := by
        rw [hsplit]
        exact iteratedFDeriv_add_apply
          ((contDiffAt_const (c := (((if p = q then lam' else 0) : ℝ) : ℂ))).of_le
            (WithTop.coe_le_coe.mpr le_top : ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)))
          (hPsm.of_le
            (WithTop.coe_le_coe.mpr le_top : ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)))
      rw [hadd]
      refine (norm_add_le _ _).trans ?_
      have hconst : ‖iteratedFDeriv ℝ m (fun _ : Fin (Module.finrank ℝ E) → ℝ =>
          (((if p = q then lam' else 0) : ℝ) : ℂ)) z‖ ≤ |lam'| := by
        refine (norm_iteratedFDeriv_const_le (((if p = q then lam' else 0) : ℝ) : ℂ) z).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
        by_cases hpq : p = q
        · rw [if_pos hpq]
        · rw [if_neg hpq]; simpa using abs_nonneg lam'
      have hP : ‖iteratedFDeriv ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((perR (fun y' => cc y' p q) y : ℝ) : ℂ)) z‖ ≤ Cper * Bf := by
        rw [norm_iteratedFDeriv_ofReal_eq (m := m) (z := z)
          ((hper_cd (fun y' => cc y' p q) (hcc_sm p q) (hcc_supp p q)).contDiffAt)]
        exact hCper R Bf hRhalf hBfnn (fun y' => cc y' p q) (hcc_sm p q)
          (hcc_supp p q) (hcc_jet p q) m hm z
      rw [hCfindef]
      linarith [hconst, hP]
    · -- smoothness
      refine contDiff_pi' fun p => contDiff_pi' fun q => ?_
      show ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        (if p = q then lam' else 0) + perR (fun y => cc y p q) z)
      exact contDiff_const.add (hper_cd (fun y => cc y p q) (hcc_sm p q) (hcc_supp p q))
    · -- periodicity
      intro i z
      show (fun p q => (if p = q then lam' else 0) + perR (fun y => cc y p q) (z + Pi.single i 1))
          = fun p q => (if p = q then lam' else 0) + perR (fun y => cc y p q) z
      funext p q
      rw [hper_per (fun y => cc y p q) i z]
    · -- the value on the `2σ`-ball
      intro z hz p q
      have hzR : ‖z‖ ≤ R := by rw [hRdef]; linarith
      have hθ0z : θ0 j z = 1 := hθ0one j z hz
      have hθ1z : θ1 j z = 1 := hθ1oneR z hzR
      have hperz : perR (fun y => cc y p q) z = cc z p q :=
        hper_eq (fun y => cc y p q) (hcc_supp p q) z hzR
      have hwind := hGfwin z hzR
      have hsumeq : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          (∑ a, ∑ b, (fun a b => θ1 j z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b)
              a b * ξ a * ξ b)
            = (∑ a, ∑ b, Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b * ξ a * ξ b) := by
        intro ξ
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        simp only [hθ1z, one_mul]
      have hsymm : ∀ a b : Fin (Module.finrank ℝ E),
          θ1 j z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b
            = θ1 j z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z b a := by
        intro a b
        simp only [hθ1z, one_mul, Gf_eq_bilin, hsym]
      have hloG : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ, (lam * mlo) * ∑ i, (ξ i) ^ 2
          ≤ ∑ a, ∑ b, (fun a b => θ1 j z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b)
              a b * ξ a * ξ b := fun ξ => by rw [hsumeq ξ]; exact (hwind ξ).1
      have hhiG : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          (∑ a, ∑ b, (fun a b => θ1 j z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b)
              a b * ξ a * ξ b) ≤ (K * Mhi) * ∑ i, (ξ i) ^ 2 :=
        fun ξ => by rw [hsumeq ξ]; exact (hwind ξ).2
      have hKcval := hKcinv (fun a b => θ1 j z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b)
        hsymm hloG hhiG
      have hgoal : ((if p = q then lam' else 0) + perR (fun y => cc y p q) z)
          = ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q := by
        rw [hperz]
        simp only [hccdef, hθ0z, one_mul]
        rw [hKcval]
        simp only [hθ1z, one_mul]
        ring_nf
      exact hgoal

end Work.Diff.STE.Lead.Gal
