import Mathlib
import Submission.Work.Diff.STE.B3.LowJetDefs
import Submission.Work.Diff.STE.B3.tmNom_aux
import Submission.Work.Diff.STE.B3.secOp_weight_sum_eq
import Submission.Work.Diff.STE.B3.LowJetAux
import Submission.Work.Diff.STE.B3.nresC_contDiffOn

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

Orphan re-dispatch by the lead, at a new path because the old file is kept: the previous owner of B3/nres_jet_bound_compact (H10-L2569) was cancelled, but B3/transport_low_jet_bound_uniform needs this statement and will import THIS module, which sits in the import closure of gal_uniform_v2 with a sorry. The statement is unchanged. Route: nresC D j a b is ContDiffOn ⊤ on the open set lowJetDom D j (B3/nresC_contDiffOn). Then show lowJetBall D j lam K is a compact subset of lowJetDom (closed and bounded in finite dimensions; positivity/det conditions with margins lam, K). A C^∞-on-open function has continuous iteratedFDerivWithin on that open set (ContDiffOn.continuousOn_iteratedFDerivWithin, using uniqueDiffOn of the open set), so it is bounded on the compact set (IsCompact.exists_bound_of_continuousOn). Take the max over m ≤ k and over a, b.

## What is proved here

* `norm_le_of_forall_norm_le` — the sup-norm bound on a finite `Pi` type: entrywise bounds give a norm
  bound.
* `dotProduct_mulVec_quadform` — `star v ⬝ᵥ (Matrix.of V).mulVec v` is the explicit quadratic form
  `∑ a, ∑ b, v a * V a b * v b`.
* `det_ne_zero_of_quadform` — a symmetric matrix whose quadratic form dominates `lam * ‖x‖^2` with
  `lam > 0` is positive definite, hence has nonzero determinant.
* `isClosed_lowJetBall` / `isCompact_lowJetBall` — `lowJetBall D j lam K` is closed (a finite
  intersection of closed conditions; the ellipticity condition is an intersection over all `x`, which
  is closed because arbitrary intersections of closed sets are closed) and bounded (it is contained in
  the closed ball of radius `max (2 σ j) K`), hence compact.
* `lowJetBall_subset_lowJetDom` — `lowJetBall D j lam K ⊆ lowJetDom D j`: the `2σ` ball lies in the
  chart target (`B3Data.htarget`), `Ff` is invertible there (`det_Ff_ne_zero`), and the ellipticity of
  the state matrix makes it invertible.
* `nresC_continuousOn_iteratedFDerivWithin` — the `m`-th iterated derivative of `nresC` on
  `lowJetDom` is continuous there.
* `le_sum_Cf` / `jet_bound_lowJetBall_aux` — the uniform bound, obtained as a finite sum of the
  individual compactness bounds.

The target `nres_jet_bound_compact_v2` is then the one-line instantiation of the auxiliary statement.
-/

namespace Work.Diff.STE.B3

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

local notation "Idx" => Fin (Module.finrank ℝ E)

/-! ## Elementary norm and matrix facts -/

/-- **The sup-norm bound on a finite `Pi` type**: if all the components of `f` are bounded by `K`,
then so is `f`.  (On a finite `Pi` type Mathlib's norm is the supremum norm.) -/
private lemma norm_le_of_forall_norm_le {ι : Type*} [Fintype ι]
    {G : ι → Type*} [∀ i, SeminormedAddCommGroup (G i)]
    {f : (i : ι) → G i} {K : ℝ} (hK : 0 ≤ K) (h : ∀ i, ‖f i‖ ≤ K) : ‖f‖ ≤ K := by
  rw [Pi.norm_def, ← Real.coe_toNNReal K hK]
  exact_mod_cast (Finset.sup_le (fun i _ => by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal K hK]
    simpa using h i) :
      (Finset.univ.sup fun b => ‖f b‖₊) ≤ K.toNNReal)

/-- `star v ⬝ᵥ (Matrix.of V).mulVec v` is the explicit quadratic form `∑ a, ∑ b, v a * V a b * v b`. -/
private lemma dotProduct_mulVec_quadform {ι : Type*} [Fintype ι]
    (V : ι → ι → ℝ) (v : ι → ℝ) :
    star v ⬝ᵥ (Matrix.of V).mulVec v = ∑ a, ∑ b, v a * V a b * v b := by
  simp only [dotProduct, Matrix.mulVec_apply, Matrix.row_apply, Matrix.of_apply,
    Finset.mul_sum, star_trivial]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- **A symmetric matrix whose quadratic form dominates `lam * ‖x‖ ^ 2` with `lam > 0` is positive
definite**, hence has nonzero determinant. -/
private lemma det_ne_zero_of_quadform {lam : ℝ} (hlam : 0 < lam) {V : Idx → Idx → ℝ}
    (hsymm : ∀ a b, V a b = V b a)
    (h : ∀ x : Idx → ℝ, lam * ‖x‖ ^ 2 ≤ ∑ a, ∑ b, x a * V a b * x b) :
    (Matrix.of V).det ≠ 0 := by
  have hpd : (Matrix.of V).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
    · refine Matrix.IsHermitian.ext (fun i j => ?_)
      simp only [Matrix.of_apply, star_trivial]
      exact (hsymm i j).symm
    · rw [dotProduct_mulVec_quadform V x]
      exact lt_of_lt_of_le (mul_pos hlam (pow_pos (norm_pos_iff.mpr hx) 2)) (h x)
  have hunit : IsUnit (Matrix.of V) := hpd.isUnit
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

/-! ## `lowJetBall` is closed and compact -/

/-- `lowJetBall D j lam K` is closed: it is a finite intersection of closed conditions.  The
ellipticity condition is an intersection over *all* `x` of closed sets, which is closed because
arbitrary intersections of closed sets are closed (no countability is needed). -/
private lemma isClosed_lowJetBall (D : B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (lam K : ℝ) : IsClosed (lowJetBall (I := I) (M := M) D j lam K) := by
  have h1 : IsClosed {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
      ‖p.1‖ ≤ 2 * D.σ j} :=
    isClosed_le (continuous_norm.comp continuous_fst) continuous_const
  have h2 : IsClosed {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
      ∀ a b : Idx, p.2.1 a b = p.2.1 b a} := by
    rw [show {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
        ∀ a b : Idx, p.2.1 a b = p.2.1 b a}
        = ⋂ (a : Idx), ⋂ (b : Idx),
          {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
            p.2.1 a b = p.2.1 b a} by
      ext p; simp]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (by fun_prop) (by fun_prop)
  have h3 : IsClosed {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
      ∀ x : Idx → ℝ, lam * ‖x‖ ^ 2 ≤ ∑ a : Idx, ∑ b : Idx, x a * p.2.1 a b * x b} := by
    rw [show {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
        ∀ x : Idx → ℝ, lam * ‖x‖ ^ 2 ≤ ∑ a : Idx, ∑ b : Idx, x a * p.2.1 a b * x b}
        = ⋂ (x : Idx → ℝ), {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
          lam * ‖x‖ ^ 2 ≤ ∑ a : Idx, ∑ b : Idx, x a * p.2.1 a b * x b} by
      ext p; simp]
    exact isClosed_iInter fun x => isClosed_le continuous_const (by fun_prop)
  have h4 : IsClosed {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
      ∀ a b : Idx, |p.2.1 a b| ≤ K} := by
    rw [show {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
        ∀ a b : Idx, |p.2.1 a b| ≤ K}
        = ⋂ (a : Idx), ⋂ (b : Idx),
          {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
            |p.2.1 a b| ≤ K} by
      ext p; simp]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le (by fun_prop) continuous_const
  have h5 : IsClosed {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
      ∀ c a b : Idx, |p.2.2 c a b| ≤ K} := by
    rw [show {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
        ∀ c a b : Idx, |p.2.2 c a b| ≤ K}
        = ⋂ (c : Idx), ⋂ (a : Idx), ⋂ (b : Idx),
          {p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
            |p.2.2 c a b| ≤ K} by
      ext p; simp]
    exact isClosed_iInter fun c => isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le (by fun_prop) continuous_const
  exact h1.inter (h2.inter (h3.inter (h4.inter h5)))

/-- `lowJetBall D j lam K` is bounded and closed, hence compact: it is contained in the closed ball
of radius `max (2 σ j) K`, since `‖p.1‖ ≤ 2 σ j` and the entrywise bounds on the two matrices give
norm bounds on them. -/
private lemma isCompact_lowJetBall (D : B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {lam K : ℝ} (hK : 0 < K) : IsCompact (lowJetBall (I := I) (M := M) D j lam K) := by
  have hK0 : (0:ℝ) ≤ K := le_of_lt hK
  set R : ℝ := max (2 * D.σ j) K with hR
  refine IsCompact.of_isClosed_subset
    (isCompact_closedBall (0 : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ)) R)
    (isClosed_lowJetBall (I := I) (M := M) D j lam K) ?_
  intro p hp
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  have h21 : ‖p.2.1‖ ≤ K :=
    norm_le_of_forall_norm_le hK0 (f := p.2.1)
      (fun a => norm_le_of_forall_norm_le hK0 (f := p.2.1 a)
        (fun b => by simpa [Real.norm_eq_abs] using h4 a b))
  have h22 : ‖p.2.2‖ ≤ K :=
    norm_le_of_forall_norm_le hK0 (f := p.2.2)
      (fun c => norm_le_of_forall_norm_le hK0 (f := p.2.2 c)
        (fun a => norm_le_of_forall_norm_le hK0 (f := p.2.2 c a)
          (fun b => by simpa [Real.norm_eq_abs] using h5 c a b)))
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Prod.norm_def]
  exact max_le (le_trans h1 (le_max_left _ _))
    (max_le (le_trans h21 (le_max_right _ _)) (le_trans h22 (le_max_right _ _)))

/-- **`lowJetBall` is contained in the (open) domain `lowJetDom`.**  The `2σ` ball lies in the chart
target, the frame matrix `Ff` is invertible there, and the ellipticity condition with `lam > 0` makes
the state matrix invertible. -/
private lemma lowJetBall_subset_lowJetDom (D : B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {lam K : ℝ} (hlam : 0 < lam) (hK : 0 < K) :
    lowJetBall (I := I) (M := M) D j lam K ⊆ lowJetDom (I := I) (M := M) D j := by
  intro p hp
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  exact ⟨D.htarget j p.1 h1, det_Ff_ne_zero (I := I) (M := M) D j h1,
    det_ne_zero_of_quadform hlam h2 h3⟩

/-! ## Continuity of the iterated derivatives -/

/-- The `m`-th iterated derivative of `nresC D j a b` on the open set `lowJetDom D j` is continuous
there, since `nresC` is `C^∞` there. -/
private lemma nresC_continuousOn_iteratedFDerivWithin (D : B3Data (I := I) (M := M) ι₀ g₀)
    (j : ι₀) (a b : Idx) (m : ℕ) :
    ContinuousOn (fun p => iteratedFDerivWithin ℝ m (nresC (I := I) (M := M) D j a b)
      (lowJetDom (I := I) (M := M) D j) p) (lowJetDom (I := I) (M := M) D j) :=
  (nresC_contDiffOn (I := I) (M := M) D j a b).continuousOn_iteratedFDerivWithin
    (by simp) (isOpen_lowJetDom (I := I) (M := M) D j).uniqueDiffOn

/-! ## The uniform bound -/

/-- A single term of the finite sum of bounds is dominated by the whole sum (all terms are
nonnegative). -/
private lemma le_sum_Cf (k : ℕ) (Cf : ℕ → Idx → Idx → ℝ) (hCf0 : ∀ m a b, 0 ≤ Cf m a b)
    {m : ℕ} (hm : m ≤ k) (a b : Idx) :
    Cf m a b ≤ ∑ m' ∈ Finset.range (k + 1), ∑ a' : Idx, ∑ b' : Idx, Cf m' a' b' := by
  have hm' : m ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
  refine le_trans (Finset.single_le_sum (f := fun b' : Idx => Cf m a b')
    (fun b' _ => hCf0 m a b') (Finset.mem_univ b)) ?_
  refine le_trans (Finset.single_le_sum (f := fun a' : Idx => ∑ b' : Idx, Cf m a' b')
    (fun a' _ => Finset.sum_nonneg (fun b' _ => hCf0 m a' b')) (Finset.mem_univ a)) ?_
  exact Finset.single_le_sum (f := fun m' : ℕ => ∑ a' : Idx, ∑ b' : Idx, Cf m' a' b')
    (fun m' _ => Finset.sum_nonneg (fun a' _ => Finset.sum_nonneg (fun b' _ => hCf0 m' a' b'))) hm'

/-- **The uniform jet bound on `lowJetBall`**, in the shape of the target statement (with the index
type spelled through the local notation `Idx`).  For each `(m, a, b)` the function is bounded on the
compact set `lowJetBall` (it is continuous there since it is continuous on the larger open set
`lowJetDom`), and the uniform bound is the finite sum of the individual bounds. -/
private lemma jet_bound_lowJetBall_aux (D : B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (k : ℕ) :
    ∀ (lam K : ℝ), 0 < lam → 0 < K →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a b : Idx) (p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ)),
          p ∈ lowJetBall (I := I) (M := M) D j lam K →
          ∀ m : ℕ, m ≤ k →
            ‖iteratedFDerivWithin ℝ m (nresC (I := I) (M := M) D j a b)
              (lowJetDom (I := I) (M := M) D j) p‖ ≤ C := by
  intro lam K hlam hK
  have hsub := lowJetBall_subset_lowJetDom (I := I) (M := M) D j hlam hK
  have hcompact := isCompact_lowJetBall (I := I) (M := M) D j (lam := lam) hK
  have hbdd : ∀ (m : ℕ) (a b : Idx), ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ lowJetBall (I := I) (M := M) D j lam K,
        ‖iteratedFDerivWithin ℝ m (nresC (I := I) (M := M) D j a b)
          (lowJetDom (I := I) (M := M) D j) p‖ ≤ C := by
    intro m a b
    obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
      ((nresC_continuousOn_iteratedFDerivWithin (I := I) (M := M) D j a b m).mono hsub)
    exact ⟨max C 0, le_max_right _ _, fun p hp => le_trans (hC p hp) (le_max_left _ _)⟩
  let Cf : ℕ → Idx → Idx → ℝ := fun m a b => Classical.choose (hbdd m a b)
  have hCf0 : ∀ m a b, 0 ≤ Cf m a b :=
    fun m a b => (Classical.choose_spec (hbdd m a b)).1
  have hCfb : ∀ m a b, ∀ p ∈ lowJetBall (I := I) (M := M) D j lam K,
      ‖iteratedFDerivWithin ℝ m (nresC (I := I) (M := M) D j a b)
        (lowJetDom (I := I) (M := M) D j) p‖ ≤ Cf m a b :=
    fun m a b => (Classical.choose_spec (hbdd m a b)).2
  refine ⟨∑ m ∈ Finset.range (k + 1), ∑ a : Idx, ∑ b : Idx, Cf m a b, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun m _ => Finset.sum_nonneg
      (fun a _ => Finset.sum_nonneg (fun b _ => hCf0 m a b)))
  · exact fun a b p hp m hm => le_trans (hCfb m a b p hp) (le_sum_Cf k Cf hCf0 hm a b)

end

theorem nres_jet_bound_compact_v2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (k : ℕ) :
    ∀ (lam K : ℝ), 0 < lam → 0 < K →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a b : Fin (Module.finrank ℝ E))
          (p : (Fin (Module.finrank ℝ E) → ℝ) ×
            (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ×
            (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)),
          p ∈ Work.Diff.STE.B3.lowJetBall (I := I) (M := M) D j lam K →
          ∀ m : ℕ, m ≤ k →
            ‖iteratedFDerivWithin ℝ m (Work.Diff.STE.B3.nresC (I := I) (M := M) D j a b)
              (Work.Diff.STE.B3.lowJetDom (I := I) (M := M) D j) p‖ ≤ C := by
  intro lam K hlam hK
  exact jet_bound_lowJetBall_aux (I := I) (M := M) D j k lam K hlam hK

end Work.Diff.STE.B3
