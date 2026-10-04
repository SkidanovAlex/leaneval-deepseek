import Mathlib
import Submission.Work.Diff.STE.B3.LowJetDefs
import Submission.Work.Diff.STE.B3.LowJetAux
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.flat.det_ne_zero_of_quadForm_le
import Submission.Work.Diff.STE.flat.compact_iteratedFDeriv_bound
import Submission.Work.Diff.STE.B3.Pointwise
import Submission.Work.Diff.STE.Lead.Gal.nresSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Two auxiliary bounds for the uniform low-order jet estimate

`Work.Diff.STE.Lead.Gal.lowJetBoundGal` (the uniform jet bound for `residualLow`) uses two facts
about the nominal residual that are proved here:

* `Mf_sandwich_gal` — the orthonormal-frame chart matrix `Mf` of an admissible section is symmetric,
  elliptic, entrywise bounded by `K` and nonsingular on the closed `2σ j`-ball;
* `nres_jet_bound_compact_gal` — the iterated derivatives (within `lowJetDom`) of the nominal
  residual `nresC` are bounded on the set `lowJetBall` of admissible states, which follows from the
  smoothness `Work.Diff.STE.Lead.Gal.nresSmooth` and compactness.
-/

namespace Work.Diff.STE.Lead.Gal

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

local notation "Idx" => Fin (Module.finrank ℝ E)

/-- The squared sup norm of a finite family is at most the sum of the squares. -/
lemma sq_norm_le_sum_sq_gal {n : ℕ} (x : Fin n → ℝ) :
    ‖x‖ ^ 2 ≤ ∑ a, (x a) ^ 2 := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · simp [Subsingleton.elim x 0, norm_zero]
  · obtain ⟨a₀, -, ha₀⟩ :=
      Finset.exists_max_image (Finset.univ : Finset (Fin n)) (fun a => |x a|)
        ⟨Classical.arbitrary (Fin n), Finset.mem_univ _⟩
    have hle : ‖x‖ ≤ |x a₀| := by
      rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
      intro b
      rw [Real.norm_eq_abs]
      exact ha₀ b (Finset.mem_univ b)
    have h1 : ‖x‖ ^ 2 ≤ (x a₀) ^ 2 := by
      have h := pow_le_pow_left₀ (norm_nonneg x) hle 2
      rwa [sq_abs] at h
    have h2 : (x a₀) ^ 2 ≤ ∑ a, (x a) ^ 2 :=
      Finset.single_le_sum (fun a _ => sq_nonneg _) (Finset.mem_univ a₀)
    linarith

/-- **The sandwich properties of the orthonormal-frame chart matrix.** -/
theorem Mf_sandwich_gal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
    (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
    (z : Idx → ℝ) (hz : ‖z‖ ≤ 2 * D.σ j) :
    (∀ a b, Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b
        = Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z b a) ∧
    (∀ x : Idx → ℝ,
        lam * ‖x‖ ^ 2 ≤ ∑ a, ∑ b,
          x a * Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b * x b) ∧
    (∀ x : Idx → ℝ,
        lam * ∑ a, (x a) ^ 2 ≤ ∑ a, ∑ b,
          x a * Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b * x b) ∧
    (∀ a b, |Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b| ≤ K) ∧
    (Matrix.of (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z)).det ≠ 0 := by
  classical
  have hON : Submission.Diff.IsONFrame g₀ (D.pt j z) (fun a => D.e j a (D.pt j z)) := D.heON j z hz
  have hMf : ∀ a b, Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b
      = h (D.pt j z) (D.e j a (D.pt j z)) (D.e j b (D.pt j z)) := fun a b => rfl
  have hnn : ∀ v : TangentSpace I (D.pt j z), 0 ≤ h (D.pt j z) v v := by
    intro v
    by_cases hv : v = 0
    · rw [hv]; simp
    · exact le_trans (mul_nonneg hlam.le (le_of_lt (g₀.pos (D.pt j z) v hv)))
        (hell (D.pt j z) v)
  -- the quadratic-form (ℓ²) form of the ellipticity
  have hell3 : ∀ ξ : Idx → ℝ,
      lam * ∑ a, (ξ a) ^ 2 ≤ ∑ a, ∑ b,
        Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b * ξ a * ξ b := by
    intro ξ
    set v : TangentSpace I (D.pt j z) := ∑ a, ξ a • D.e j a (D.pt j z) with hv
    have hexp : ∑ a, ∑ b, Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b * ξ a * ξ b
        = h (D.pt j z) v v := by
      rw [hv]
      simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      simp only [Work.Diff.STE.B3.Mf, Work.Diff.STE.B3Data.mat]
      rw [hsym (D.pt j z) (D.e j b (D.pt j z)) (D.e j a (D.pt j z))]
      ring
    have hcoef : ∀ a : Idx,
        g₀.inner (D.pt j z) v (D.e j a (D.pt j z)) = ξ a := by
      intro a
      rw [hv]
      simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      rw [Finset.sum_eq_single a]
      · rw [hON a a, if_pos rfl, mul_one]
      · intro b _ hb
        rw [hON b a, if_neg hb, mul_zero]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    have hvnorm : g₀.inner (D.pt j z) v v = ∑ a, (ξ a) ^ 2 := by
      rw [← D.sum_inner_sq j hON v]
      exact Finset.sum_congr rfl (fun a _ => by rw [hcoef a])
    rw [hexp, ← hvnorm]
    exact hell (D.pt j z) v
  have hell2 : ∀ ξ : Idx → ℝ,
      lam * ∑ a, (ξ a) ^ 2 ≤ ∑ a, ∑ b,
        ξ a * Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b * ξ b := by
    intro ξ
    refine le_trans (hell3 ξ) (le_of_eq ?_)
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    rw [hMf a b, hMf b a, hsym]
  · intro x
    have h1 := hell2 x
    have h2 : ‖x‖ ^ 2 ≤ ∑ a, (x a) ^ 2 := sq_norm_le_sum_sq_gal x
    refine le_trans (mul_le_mul_of_nonneg_left h2 hlam.le) ?_
    simpa only [mul_assoc] using h1
  · intro x
    simpa only [mul_assoc] using hell2 x
  · -- entrywise bound, by polarisation
    intro a b
    set u : TangentSpace I (D.pt j z) := D.e j a (D.pt j z) with hu
    set v : TangentSpace I (D.pt j z) := D.e j b (D.pt j z) with hv
    have hsymm : h (D.pt j z) v u = h (D.pt j z) u v := hsym (D.pt j z) v u
    have hsum : h (D.pt j z) (u + v) (u + v)
        = h (D.pt j z) u u + 2 * h (D.pt j z) u v + h (D.pt j z) v v := by
      simp only [map_add, ContinuousLinearMap.add_apply]
      rw [hsymm]; ring
    have hdif : h (D.pt j z) (u - v) (u - v)
        = h (D.pt j z) u u - 2 * h (D.pt j z) u v + h (D.pt j z) v v := by
      simp only [map_sub, ContinuousLinearMap.sub_apply]
      rw [hsymm]; ring
    have h1 : 0 ≤ h (D.pt j z) u u + 2 * h (D.pt j z) u v + h (D.pt j z) v v := by
      rw [← hsum]; exact hnn _
    have h2 : 0 ≤ h (D.pt j z) u u - 2 * h (D.pt j z) u v + h (D.pt j z) v v := by
      rw [← hdif]; exact hnn _
    have huK : h (D.pt j z) u u ≤ K := by
      have := hub (D.pt j z) u
      rw [hu, hON a a, if_pos rfl, mul_one] at this
      exact this
    have hvK : h (D.pt j z) v v ≤ K := by
      have := hub (D.pt j z) v
      rw [hv, hON b b, if_pos rfl, mul_one] at this
      exact this
    rw [hMf a b, ← hu, ← hv]
    rw [abs_le]
    constructor <;> linarith
  · -- nonsingularity
    have hquad : ∀ ξ : Idx → ℝ,
        lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ k,
          (Matrix.of (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z)) i k * ξ i * ξ k := by
      intro ξ
      have h1 := hell2 ξ
      have h2 : (∑ a, ∑ b, ξ a * Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b * ξ b)
          = (∑ i, ∑ k, (Matrix.of (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z)) i k
              * ξ i * ξ k) := by
        simp only [Matrix.of_apply]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      rw [h2] at h1
      exact h1
    exact Work.Diff.STE.flat.det_ne_zero_of_quadForm_le _ hlam hquad

/-- The set of admissible bounded states *with the `ℓ²`-ellipticity of the chart matrix*: this is
the form in which the section's orthonormal-frame chart matrix is uniformly elliptic (and hence
uniformly invertible with bounded jets). -/
def lowJetBall2Gal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (lam K : ℝ) :
    Set ((Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ)) :=
  Work.Diff.STE.B3.lowJetBall (I := I) (M := M) D j lam K ∩
    {p | ∀ ξ : Idx → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ ∑ a, ∑ b, ξ a * p.2.1 a b * ξ b}

/-- The set of admissible states is closed. -/
theorem isClosed_lowJetBall_gal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K) :
    IsClosed (Work.Diff.STE.B3.lowJetBall (I := I) (M := M) D j lam K) := by
  classical
  have hset : Work.Diff.STE.B3.lowJetBall (I := I) (M := M) D j lam K =
      ({p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) | ‖p.1‖ ≤ 2 * D.σ j} ∩
        {p | ∀ a b, p.2.1 a b = p.2.1 b a} ∩
        {p | ∀ ξ : Idx → ℝ, lam * ‖ξ‖ ^ 2 ≤ ∑ a, ∑ b, ξ a * p.2.1 a b * ξ b} ∩
        {p | ∀ a b, |p.2.1 a b| ≤ K} ∩
        {p | ∀ c a b, |p.2.2 c a b| ≤ K}) := by
    ext p
    simp only [Work.Diff.STE.B3.lowJetBall, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  have hA : IsClosed ({p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
      ‖p.1‖ ≤ 2 * D.σ j}) :=
    isClosed_le (continuous_norm.comp continuous_fst) continuous_const
  have hB : IsClosed {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
      ∀ a b, p.2.1 a b = p.2.1 b a} := by
    rw [show {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
        ∀ a b, p.2.1 a b = p.2.1 b a}
        = ⋂ a : Idx, ⋂ b : Idx,
          {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) | p.2.1 a b = p.2.1 b a}
        from by ext p; simp]
    refine isClosed_iInter (fun a => isClosed_iInter (fun b => ?_))
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hC : IsClosed {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
      ∀ ξ : Idx → ℝ, lam * ‖ξ‖ ^ 2 ≤ ∑ a, ∑ b, ξ a * p.2.1 a b * ξ b} := by
    rw [show {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
        ∀ ξ : Idx → ℝ, lam * ‖ξ‖ ^ 2 ≤ ∑ a, ∑ b, ξ a * p.2.1 a b * ξ b}
        = ⋂ ξ : Idx → ℝ, {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
            lam * ‖ξ‖ ^ 2 ≤ ∑ a, ∑ b, ξ a * p.2.1 a b * ξ b} from by ext p; simp]
    exact isClosed_iInter (fun ξ => isClosed_le continuous_const (by fun_prop))
  have hD : IsClosed {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
      ∀ a b, |p.2.1 a b| ≤ K} := by
    rw [show {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
        ∀ a b, |p.2.1 a b| ≤ K}
        = ⋂ a : Idx, ⋂ b : Idx,
          {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) | |p.2.1 a b| ≤ K}
        from by ext p; simp]
    exact isClosed_iInter (fun a => isClosed_iInter (fun b =>
      isClosed_le (by fun_prop) continuous_const))
  have hE : IsClosed {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
      ∀ c a b, |p.2.2 c a b| ≤ K} := by
    rw [show {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
        ∀ c a b, |p.2.2 c a b| ≤ K}
        = ⋂ c : Idx, ⋂ a : Idx, ⋂ b : Idx,
          {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) | |p.2.2 c a b| ≤ K}
        from by ext p; simp]
    exact isClosed_iInter (fun c => isClosed_iInter (fun a => isClosed_iInter (fun b =>
      isClosed_le (by fun_prop) continuous_const)))
  rw [hset]
  exact IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter hA hB) hC) hD) hE

/-- The admissible states are bounded. -/
theorem isBounded_lowJetBall_gal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K) :
    Bornology.IsBounded (Work.Diff.STE.B3.lowJetBall (I := I) (M := M) D j lam K) := by
  refine (Metric.isBounded_closedBall (x := (0 : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ)))
    (r := max (2 * D.σ j) K)).subset ?_
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right]
  have h21 : ‖p.2.1‖ ≤ K := by
    rw [pi_norm_le_iff_of_nonneg hK.le]
    intro a
    rw [pi_norm_le_iff_of_nonneg hK.le]
    intro b
    rw [Real.norm_eq_abs]
    exact hp.2.2.2.1 a b
  have h22 : ‖p.2.2‖ ≤ K := by
    rw [pi_norm_le_iff_of_nonneg hK.le]
    intro c
    rw [pi_norm_le_iff_of_nonneg hK.le]
    intro a
    rw [pi_norm_le_iff_of_nonneg hK.le]
    intro b
    rw [Real.norm_eq_abs]
    exact hp.2.2.2.2 c a b
  show ‖p‖ ≤ max (2 * D.σ j) K
  rw [Prod.norm_def]
  refine max_le (le_trans hp.1 (le_max_left _ _)) ?_
  rw [Prod.norm_def]
  exact max_le (le_trans h21 (le_max_right _ _)) (le_trans h22 (le_max_right _ _))

/-- **`lowJetBall2Gal` is compact.** -/
theorem isCompact_lowJetBall2_gal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K) : IsCompact (lowJetBall2Gal (I := I) (M := M) D j lam K) := by
  have h1 : IsClosed (lowJetBall2Gal (I := I) (M := M) D j lam K) := by
    refine IsClosed.inter (isClosed_lowJetBall_gal (I := I) (M := M) D j lam K hlam hK) ?_
    rw [show {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
        ∀ ξ : Idx → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ ∑ a, ∑ b, ξ a * p.2.1 a b * ξ b}
        = ⋂ ξ : Idx → ℝ, {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
            lam * ∑ i, (ξ i) ^ 2 ≤ ∑ a, ∑ b, ξ a * p.2.1 a b * ξ b} from by ext p; simp]
    exact isClosed_iInter (fun ξ => isClosed_le continuous_const (by fun_prop))
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨h1, (isBounded_lowJetBall_gal (I := I) (M := M) D j lam K hlam hK).subset Set.inter_subset_left⟩

/-- **`lowJetBall2Gal` is contained in the state domain.** -/
theorem lowJetBall2_subset_lowJetDom_gal
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K) :
    lowJetBall2Gal (I := I) (M := M) D j lam K ⊆
      Work.Diff.STE.B3.lowJetDom (I := I) (M := M) D j := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  have hz : ‖p.1‖ ≤ 2 * D.σ j := hp1.1
  refine ⟨D.htarget j p.1 hz, Work.Diff.STE.B3.det_Ff_ne_zero (I := I) (M := M) D j hz, ?_⟩
  refine Work.Diff.STE.flat.det_ne_zero_of_quadForm_le _ hlam ?_
  intro ξ
  refine le_trans (hp2 ξ) (le_of_eq ?_)
  simp only [Matrix.of_apply]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))

/-- **The iterated derivatives of the nominal residual are bounded on the admissible states.** -/
theorem nres_jet_bound_compact_gal
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (k : ℕ) :
    ∀ (lam K : ℝ), 0 < lam → 0 < K →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a b : Idx)
          (p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ)),
          p ∈ lowJetBall2Gal (I := I) (M := M) D j lam K →
          ∀ m : ℕ, m ≤ k →
            ‖iteratedFDerivWithin ℝ m (Work.Diff.STE.B3.nresC (I := I) (M := M) D j a b)
              (Work.Diff.STE.B3.lowJetDom (I := I) (M := M) D j) p‖ ≤ C := by
  classical
  intro lam K hlam hK
  have hC := isCompact_lowJetBall2_gal (I := I) (M := M) D j lam K hlam hK
  have hCU := lowJetBall2_subset_lowJetDom_gal (I := I) (M := M) D j lam K hlam hK
  choose C hC0 hCb using fun a b : Idx =>
    Work.Diff.STE.flat.compact_iteratedFDeriv_bound
      (Work.Diff.STE.B3.nresC (I := I) (M := M) D j a b)
      (Work.Diff.STE.B3.isOpen_lowJetDom (I := I) (M := M) D j)
      (nresSmooth (I := I) (M := M) D j a b) hC hCU k
  refine ⟨∑ a : Idx, ∑ b : Idx, C a b,
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hC0 a b)), ?_⟩
  intro a b p hp m hm
  refine le_trans ?_ (Finset.single_le_sum (f := fun a' => ∑ b' : Idx, C a' b')
    (fun a' _ => Finset.sum_nonneg (fun b' _ => hC0 a' b')) (Finset.mem_univ a))
  refine le_trans ?_ (Finset.single_le_sum (f := fun b' => C a b')
    (fun b' _ => hC0 a b') (Finset.mem_univ b))
  rw [iteratedFDerivWithin_of_isOpen m
    (Work.Diff.STE.B3.isOpen_lowJetDom (I := I) (M := M) D j) (hCU hp)]
  exact hCb a b p hp m hm

end

end Work.Diff.STE.Lead.Gal
