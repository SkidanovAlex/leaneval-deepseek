import Mathlib
import Submission.Work.RPA3.TubularHDefs
import Submission.Work.RPA3.theta_coord_bounds
import Submission.Work.RPA3.int_tendsto_eventually_const
import Submission.Work.RPA3.theta_std
import Submission.Work.RPA3.theta_per_int
import Submission.Work.RPA3.closure_theta_smallStrip

/-!
# RPA3: the closure of the small tubular strip (with the time variable) lies in the witness set

For a fixed `τ ∈ [-1,2]` the lemma `closure_theta_smallStrip` shows that the closure of the strip
`‖ξ‖ < ε/2` at time `τ` is contained in the set of points having a witness at time `τ`.  Here we
upgrade it to the *joint* statement in the time variable `τ`:

`closure {(τ,z) | τ ∈ [-1,2], ∃ w, ‖w.2‖ < ε/2, θ(τ,w) = z} ⊆ {(τ,z) | HasWitness L T τ z}`.

This is the form used by the assembly: the point `(τ,z)` may be a limit of strip points whose time
parameter converges to `τ` as well.

The proof is the same two-block decomposition as in `closure_theta_smallStrip`, carrying the time
coordinate `τ` along.

* **Near block** `|x| ≤ X₀+1`.  The configuration `(τ, x, t mod 2π, ξ)` runs over the compact set
  `C = [-1,2] × ([-(X₀+1),X₀+1] × [0,2π]) × closedBall 0 (ε/2)`.  The map
  `thetaAngles : (τ,w) ↦ (τ, angleProj (θ(τ,w)))` collapses the integral shifts of the angle, so
  `A := thetaAngles '' C` is compact, hence closed; the preimage `tauAngles ⁻¹' A` is a closed set
  containing the near block, and every point of it is a `Tk`-shift of `θ` at a point of `C`, hence
  has a witness.

* **Far block** `|x| > X₀+1`.  There `θ(τ,x,t,ξ) = ((x,t),(-ξ₁,-ξ₂))` (`theta_std`), so its closure
  lies in the closed set `{τ ∈ [-1,2]} ∩ {X₀ ≤ |q₁|} ∩ {‖p‖ ≤ ε/2}`, and every point of that set has
  a witness (`HasWitness_std`).
-/

open scoped Topology
open Set

set_option autoImplicit false
noncomputable section

namespace Work.RPA3

/-! ## The angle projections carrying the time variable -/

/-- The `τ`-augmented version of `angleProj ∘ θ`: `(τ, w) ↦ (τ, angleProj (θ(τ,w)))`. -/
def thetaAngles (L : LagFamilyAll) :
    ℝ × PS → ℝ × ((ℝ × AddCircle (2 * Real.pi)) × (ℝ × ℝ)) :=
  fun p => (p.1, angleProj (thetaZ L p.1 p.2))

/-- The `τ`-augmented angle projection `(τ, z) ↦ (τ, angleProj z)`, the map whose preimages of the
compact images of `thetaAngles` are the closed sets used in the near block. -/
def tauAngles : ℝ × PS → ℝ × ((ℝ × AddCircle (2 * Real.pi)) × (ℝ × ℝ)) :=
  fun q => (q.1, angleProj q.2)

theorem continuous_thetaAngles (L : LagFamilyAll) : Continuous (thetaAngles L) := by
  unfold thetaAngles
  exact continuous_fst.prodMk (continuous_angleProj.comp (continuous_thetaZ L))

theorem continuous_tauAngles : Continuous tauAngles := by
  unfold tauAngles
  exact continuous_fst.prodMk (continuous_angleProj.comp continuous_snd)

/-- If two points of the phase space have the same image under `angleProj`, they differ by an integral
shift `Tk k` of the angle: `y = Tk k z`. -/
theorem eq_Tk_of_angleProj_eq {z y : PS} (h : angleProj z = angleProj y) :
    ∃ k : ℤ, y = Tk k z := by
  have h1 : z.1.1 = y.1.1 := by
    simpa [angleProj] using congrArg (fun t : (ℝ × AddCircle (2 * Real.pi)) × (ℝ × ℝ) => t.1.1) h
  have h2 : (z.1.2 : AddCircle (2 * Real.pi)) = (y.1.2 : AddCircle (2 * Real.pi)) := by
    simpa [angleProj] using congrArg (fun t : (ℝ × AddCircle (2 * Real.pi)) × (ℝ × ℝ) => t.1.2) h
  have h3 : z.2 = y.2 := by
    simpa [angleProj] using congrArg (fun t : (ℝ × AddCircle (2 * Real.pi)) × (ℝ × ℝ) => t.2) h
  obtain ⟨k, hk⟩ := exists_int_of_angle_eq h2
  refine ⟨-k, ?_⟩
  rw [Prod.ext_iff]
  refine ⟨?_, ?_⟩
  · rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · rw [Tk_fst_fst]; exact h1.symm
    · rw [Tk_fst_snd]
      push_cast
      linarith [hk]
  · rw [Tk_snd]; exact h3.symm

/-! ## The closure of the strip -/

theorem closure_theta_smallStrip_Icc (L : Work.RPA3.LagFamilyAll) (T : Work.RPA3.TubularData L) :
    closure {q : ℝ × Work.RPA3.PS | q.1 ∈ Set.Icc (-1 : ℝ) 2 ∧
        ∃ w : Work.RPA3.PS, ‖w.2‖ < T.ε / 2 ∧
          Work.RPA3.theta L q.1 w.1.1 w.1.2 w.2 = q.2}
      ⊆ {q : ℝ × Work.RPA3.PS | Work.RPA3.HasWitness L T q.1 q.2} := by
  -- the strip, split according to whether `|x|` stays below `X₀ + 1`
  set S : Set (ℝ × PS) :=
    {q : ℝ × PS | q.1 ∈ Set.Icc (-1 : ℝ) 2 ∧
      ∃ w : PS, ‖w.2‖ < T.ε / 2 ∧ theta L q.1 w.1.1 w.1.2 w.2 = q.2} with hS
  set S₁ : Set (ℝ × PS) :=
    {q : ℝ × PS | q.1 ∈ Set.Icc (-1 : ℝ) 2 ∧
      ∃ w : PS, |w.1.1| ≤ L.X0 + 1 ∧ ‖w.2‖ < T.ε / 2 ∧
        theta L q.1 w.1.1 w.1.2 w.2 = q.2} with hS₁
  set S₂ : Set (ℝ × PS) :=
    {q : ℝ × PS | q.1 ∈ Set.Icc (-1 : ℝ) 2 ∧
      ∃ w : PS, L.X0 + 1 < |w.1.1| ∧ ‖w.2‖ < T.ε / 2 ∧
        theta L q.1 w.1.1 w.1.2 w.2 = q.2} with hS₂
  have hdecomp : S = S₁ ∪ S₂ := by
    rw [hS, hS₁, hS₂]
    ext q
    constructor
    · rintro ⟨hτ, w, hξ, hθ⟩
      by_cases h : |w.1.1| ≤ L.X0 + 1
      · exact Or.inl ⟨hτ, w, h, hξ, hθ⟩
      · exact Or.inr ⟨hτ, w, not_le.mp h, hξ, hθ⟩
    · rintro (⟨hτ, w, -, hξ, hθ⟩ | ⟨hτ, w, -, hξ, hθ⟩)
      · exact ⟨hτ, w, hξ, hθ⟩
      · exact ⟨hτ, w, hξ, hθ⟩
  rw [hdecomp, closure_union]
  refine union_subset ?_ ?_
  · -- ### The near block `|x| ≤ X₀ + 1`
    -- the compact block of configurations `(τ,x,t,ξ)` in the strip
    set C : Set (ℝ × PS) := Set.Icc (-1 : ℝ) 2 ×ˢ
      ((Set.Icc (-(L.X0 + 1)) (L.X0 + 1) ×ˢ Set.Icc 0 (2 * Real.pi)) ×ˢ
        Metric.closedBall (0 : ℝ × ℝ) (T.ε / 2)) with hC
    have hCcompact : IsCompact C := by
      rw [hC]
      exact isCompact_Icc.prod
        ((isCompact_Icc.prod isCompact_Icc).prod (isCompact_closedBall _ _))
    -- its image in the `τ`-augmented angle-modulo-`2π` space is compact, hence closed
    have hAclosed : IsClosed (thetaAngles L '' C) :=
      (hCcompact.image (continuous_thetaAngles L)).isClosed
    have hGclosed : IsClosed (tauAngles ⁻¹' (thetaAngles L '' C)) :=
      hAclosed.preimage continuous_tauAngles
    -- every point of the near block lies in that preimage
    have hsub : S₁ ⊆ tauAngles ⁻¹' (thetaAngles L '' C) := by
      rintro q ⟨hτ, w, hx, hξ, hθ⟩
      obtain ⟨t', ht', k, htk⟩ := exists_shift_two_pi_Ico w.1.2
      have hmem : (q.1, ((w.1.1, t'), w.2)) ∈ C := by
        rw [hC]
        refine ⟨hτ, ⟨?_, Set.Ico_subset_Icc_self ht'⟩, ?_⟩
        · rw [Set.mem_Icc]; exact abs_le.mp hx
        · rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hξ
      have hΦeq : thetaAngles L (q.1, ((w.1.1, t'), w.2)) = tauAngles q := by
        have hθk : q.2 = Tk k (theta L q.1 w.1.1 t' w.2) := by
          rw [← hθ, htk]
          exact theta_per_int L q.1 w.1.1 t' w.2 k
        have hang : angleProj (theta L q.1 w.1.1 t' w.2) = angleProj q.2 := by
          rw [hθk, angleProj_Tk]
        simp only [thetaAngles, tauAngles, thetaZ_apply]
        rw [hang]
      exact ⟨_, hmem, hΦeq⟩
    refine subset_trans (closure_mono hsub) ?_
    rw [hGclosed.closure_eq]
    -- every point of the preimage is a `Tk`-shift of `θ` at a point of the compact block, hence has
    -- a witness
    rintro q ⟨p, hp, hpq⟩
    simp only [Set.mem_setOf_eq]
    have hp1 : p.1 = q.1 := by
      simpa [thetaAngles, tauAngles] using congrArg Prod.fst hpq
    have hang : angleProj (thetaZ L p.1 p.2) = angleProj q.2 := by
      simpa [thetaAngles, tauAngles] using congrArg Prod.snd hpq
    rw [hp1] at hang
    have hξle : ‖p.2.2‖ ≤ T.ε / 2 := by
      rw [hC] at hp
      have h2 := hp.2.2
      rwa [Metric.mem_closedBall, dist_zero_right] at h2
    have hξε : ‖p.2.2‖ < T.ε := lt_of_le_of_lt hξle (by linarith [T.εpos])
    obtain ⟨k, hk⟩ := eq_Tk_of_angleProj_eq hang
    have hwit : HasWitness L T q.1 (thetaZ L q.1 p.2) := ⟨p.2, hξε, rfl⟩
    rw [hk]
    exact HasWitness_Tk' L T q.1 k (thetaZ L q.1 p.2) hwit
  · -- ### The far block `|x| > X₀ + 1`
    -- there `θ` is the explicit map `((x,t),(-ξ₁,-ξ₂))`
    have hsub₂ : S₂ ⊆ {q : ℝ × PS | q.1 ∈ Set.Icc (-1 : ℝ) 2} ∩
        {q : ℝ × PS | L.X0 ≤ |q.2.1.1|} ∩ {q : ℝ × PS | ‖q.2.2‖ ≤ T.ε / 2} := by
      rintro q ⟨hτ, w, hx, hξ, hθ⟩
      have hxX0 : L.X0 ≤ |w.1.1| := by linarith
      have hz : q.2 = ((w.1.1, w.1.2), (-w.2.1, -w.2.2)) := by
        rw [← hθ, theta_std L q.1 w.1.1 w.1.2 w.2 hxX0]
      refine ⟨⟨hτ, ?_⟩, ?_⟩
      · simp only [Set.mem_setOf_eq]
        rw [hz]; simpa using hxX0
      · simp only [Set.mem_setOf_eq]
        rw [hz]
        have h2n : ‖(-w.2.1, -w.2.2)‖ = ‖w.2‖ := by
          rw [Prod.norm_def, Prod.norm_def, norm_neg, norm_neg]
        rw [h2n]; exact le_of_lt hξ
    have hclosed : IsClosed ({q : ℝ × PS | q.1 ∈ Set.Icc (-1 : ℝ) 2} ∩
        {q : ℝ × PS | L.X0 ≤ |q.2.1.1|} ∩ {q : ℝ × PS | ‖q.2.2‖ ≤ T.ε / 2}) := by
      have h1 : IsClosed {q : ℝ × PS | q.1 ∈ Set.Icc (-1 : ℝ) 2} :=
        isClosed_Icc.preimage continuous_fst
      have h2 : IsClosed {q : ℝ × PS | L.X0 ≤ |q.2.1.1|} :=
        isClosed_le continuous_const (by fun_prop : Continuous (fun q : ℝ × PS => |q.2.1.1|))
      have h3 : IsClosed {q : ℝ × PS | ‖q.2.2‖ ≤ T.ε / 2} :=
        isClosed_le (by fun_prop : Continuous (fun q : ℝ × PS => ‖q.2.2‖)) continuous_const
      exact (h1.inter h2).inter h3
    refine subset_trans (closure_mono hsub₂) ?_
    rw [hclosed.closure_eq]
    rintro q ⟨⟨hτ, hx⟩, hξ⟩
    simp only [Set.mem_setOf_eq] at hτ hx hξ
    simp only [Set.mem_setOf_eq]
    have hξε : ‖(-q.2.2.1, -q.2.2.2)‖ < T.ε := by
      have h2n : ‖(-q.2.2.1, -q.2.2.2)‖ = ‖q.2.2‖ := by
        rw [Prod.norm_def, Prod.norm_def, norm_neg, norm_neg]
      rw [h2n]; linarith [T.εpos]
    have hwit := HasWitness_std L T q.1 q.2.1.1 q.2.1.2 (-q.2.2.1, -q.2.2.2) hx hξε
    simpa using hwit

end Work.RPA3
