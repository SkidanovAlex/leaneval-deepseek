import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.init_data
import Submission.Work.Diff.C.ray_cap_algebra
import Submission.Work.Diff.C.ray_cover
import Submission.Work.Diff.C.ray_model_stay
import Submission.Work.Diff.C.psi_estimates
import Submission.Work.Diff.C.gp_helpers
import Submission.Work.Diff.C.rgrad_fcos_eikonal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C


/-! ## Auxiliary lemmas for the crux

These are the elementary pieces of the reduction of `dip_equator_crux` to geometric input; they are
proved here (they need no curvature input). -/

/-- **The numerical hypothesis forces `α ≥ √(6c)`.**  From `3c ≤ 1 - cos α` and the quadratic
upper bound `1 - cos α ≤ α²/2`.  Consequently the right hand side of the crux's bound,
`100 (finrank ℝ E + 2) (ε₁π + α + √c)`, is at least `1000 √c` (see `target_rhs_ge`); this is the
slack that lets the crude geometric inputs suffice. -/
theorem sqrt_six_mul_c_le_alpha {α c : ℝ} (hα : 0 < α) (hnum1 : 3 * c ≤ 1 - Real.cos α) :
    Real.sqrt (6 * c) ≤ α := by
  have h1 : 1 - Real.cos α ≤ α ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := α)]
  have h2 : 6 * c ≤ α ^ 2 := by linarith
  calc Real.sqrt (6 * c) ≤ Real.sqrt (α ^ 2) := Real.sqrt_le_sqrt h2
    _ = α := Real.sqrt_sq (le_of_lt hα)

/-- **The crux's right hand side dominates `1000 √c`.** -/
theorem target_rhs_ge {n : ℕ} (hn : 1 ≤ n) {α c ε₁ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hc : 0 < c) (hε₁ : 0 ≤ ε₁) (hnum1 : 3 * c ≤ 1 - Real.cos α) :
    1000 * Real.sqrt c ≤ 100 * ((n : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c) := by
  have h6 : Real.sqrt (6 * c) ≤ α := sqrt_six_mul_c_le_alpha hα hnum1
  have hcn : (0:ℝ) ≤ Real.sqrt c := Real.sqrt_nonneg c
  have hr6 : Real.sqrt (6 * c) = Real.sqrt 6 * Real.sqrt c := Real.sqrt_mul (by norm_num) c
  have h6' : (2.4:ℝ) ≤ Real.sqrt 6 := by
    have h24 : (2.4:ℝ) ^ 2 ≤ 6 := by norm_num
    calc (2.4:ℝ) = Real.sqrt ((2.4:ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 6 := Real.sqrt_le_sqrt h24
  have hn3 : (3:ℝ) ≤ (n : ℝ) + 2 := by
    have h1n : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have h5 : Real.sqrt 6 * Real.sqrt c + Real.sqrt c ≤ ε₁ * Real.pi + α + Real.sqrt c := by
    have hα' : Real.sqrt 6 * Real.sqrt c ≤ α := hr6 ▸ h6
    have hpi : 0 ≤ ε₁ * Real.pi := mul_nonneg hε₁ Real.pi_pos.le
    linarith
  have h4 : (3:ℝ) * (Real.sqrt 6 * Real.sqrt c + Real.sqrt c)
      ≤ ((n:ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c) := by
    have hnn : 0 ≤ ε₁ * Real.pi + α + Real.sqrt c := by positivity
    calc (3:ℝ) * (Real.sqrt 6 * Real.sqrt c + Real.sqrt c)
        ≤ 3 * (ε₁ * Real.pi + α + Real.sqrt c) := by linarith
      _ ≤ ((n:ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c) :=
          mul_le_mul_of_nonneg_right hn3 hnn
  have hconst : (1000:ℝ) ≤ 100 * (3 * (Real.sqrt 6 + 1)) := by nlinarith [h6']
  calc (1000:ℝ) * Real.sqrt c ≤ 100 * (3 * (Real.sqrt 6 + 1)) * Real.sqrt c :=
        mul_le_mul_of_nonneg_right hconst hcn
    _ = 100 * (3 * (Real.sqrt 6 * Real.sqrt c + Real.sqrt c)) := by ring
    _ ≤ 100 * (((n:ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c)) :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = 100 * ((n : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c) := by ring


open Bundle in
/-- **The ray from `p` in the unit direction `u` is minimising up to the time `s`.**
If `rdist p (GExp p (s • u)) = s` then `rdist p (GExp p (σ • u)) = σ` for every `σ ∈ [0,s]`, and
the sub-arcs are minimising: `rdist (GExp p (σ • u)) (GExp p (τ • u)) = τ - σ` for `0 ≤ σ ≤ τ ≤ s`.

This is the "minimising ray" fact that every route to `dip_equator_crux` uses: the hypothesis
`hray` of the crux gives it at the endpoint, the triangle inequality and the length bound
`eik_rdist_GExp_ray_sub_le` transport it back to all earlier times. -/
theorem rdist_GExp_ray_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0) {p : M}
    {u : TangentSpace I p} (hu : Inner.inner ℝ u u = 1) {s : ℝ} (hs0 : 0 ≤ s)
    (hray : rdist (I := I) (M := M) p (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) = s) :
    (∀ σ ∈ Set.Icc (0 : ℝ) s,
      rdist (I := I) (M := M) p (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) = σ) ∧
    (∀ σ ∈ Set.Icc (0 : ℝ) s, ∀ τ ∈ Set.Icc (0 : ℝ) s, σ ≤ τ →
      rdist (I := I) (M := M) (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) = τ - σ) := by
  have hu' : ‖u‖ = 1 := by
    have h : ‖u‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq u]; exact hu
    nlinarith [norm_nonneg u]
  have hpt : ∀ σ ∈ Set.Icc (0 : ℝ) s,
      rdist (I := I) (M := M) p (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) = σ := by
    intro σ hσ
    have hle : rdist (I := I) (M := M) p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) ≤ σ * ‖u‖ :=
      eik_rdist_GExp_smul_le (I := I) (M := M) (cov := cov) hmet p u hσ.1
    rw [hu', mul_one] at hle
    have hsub : rdist (I := I) (M := M) (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) ≤ s - σ :=
      eik_rdist_GExp_ray_sub_le (I := I) (M := M) (cov := cov) hmet p hu' hσ.1 hσ.2
    have htri := eik_rdist_triangle_le (I := I) (M := M) (cov := cov) hmet htor p
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))
    rw [hray] at htri
    linarith
  refine ⟨hpt, ?_⟩
  intro σ hσ τ hτ hστ
  have hle : rdist (I := I) (M := M) (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) ≤ τ - σ :=
    eik_rdist_GExp_ray_sub_le (I := I) (M := M) (cov := cov) hmet p hu' hσ.1 hστ
  have hge : τ - σ ≤ rdist (I := I) (M := M)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) := by
    have htri1 := eik_rdist_triangle_le (I := I) (M := M) (cov := cov) hmet htor p
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
    rw [hpt σ hσ, hpt τ hτ] at htri1
    linarith
  linarith



/-- **The final trigonometry of the crux.**  Suppose the endpoint time `s` of the ray lies in
`[π/2 - 4√c, π/2 + X]`, where `X` bounds the total length of the "dips" of the function
(`X = 4(√c + √(ε₁π)) + 256(√c + ε₁π)` in the application: `4√c` for the first-dip correction and
`256(√c + ε₁π)` for the far-ball diameter; the arithmetic turning that into `X ≤ 260√c + 300ε₁π`
is done in the application with `4ε₁π < c`).  Then

  `|cos s| ≤ 1000 √c + 300 ε₁ π`.

This is the last step of the reduction: pure trigonometry (`cos` is decreasing on `[0,π]`, and
`|cos|` is maximal at the endpoints of the interval). -/
theorem dip_final_trig {s X c ε₁ : ℝ} (hc : 0 < c) (hcq : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hs0 : 0 ≤ s) (hXnn : 0 ≤ X)
    (hlo : Real.pi / 2 - 4 * Real.sqrt c ≤ s) (hhi : s ≤ Real.pi / 2 + X)
    (hX : X ≤ 260 * Real.sqrt c + 300 * ε₁ * Real.pi) :
    |Real.cos s| ≤ 1000 * Real.sqrt c + 300 * ε₁ * Real.pi := by
  have hc0 : (0 : ℝ) ≤ Real.sqrt c := Real.sqrt_nonneg c
  have hε1π : 0 ≤ 300 * ε₁ * Real.pi := by positivity
  rcases lt_or_ge (4 * Real.sqrt c) (Real.pi / 2) with hsmall | hbig
  · -- the interesting case: `π/2 - 4√c ≥ 0`
    have h4 : (0 : ℝ) ≤ 4 * Real.sqrt c := by positivity
    have h4nonneg : 0 ≤ Real.pi / 2 - 4 * Real.sqrt c := by linarith [Real.pi_pos]
    have hsinX : |Real.sin X| ≤ X := by
      rcases lt_or_ge X 1 with h | h
      · have hXpi : X ≤ Real.pi := by linarith [Real.pi_gt_three]
        have hsin : 0 ≤ Real.sin X := Real.sin_nonneg_of_nonneg_of_le_pi hXnn hXpi
        rw [abs_of_nonneg hsin]
        exact Real.sin_le hXnn
      · have h1 := Real.sin_le_one X
        have h2 := Real.neg_one_le_sin X
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
    have hkey : |Real.cos s| ≤ max (Real.sin (4 * Real.sqrt c)) X := by
      rcases lt_or_ge s (Real.pi / 2) with hs | hs
      · have hspi : s ≤ Real.pi := by linarith [Real.pi_pos]
        have hcs : 0 ≤ Real.cos s :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, h4nonneg, hlo], hs.le⟩
        rw [abs_of_nonneg hcs]
        have hmono : Real.cos s ≤ Real.cos (Real.pi / 2 - 4 * Real.sqrt c) :=
          Real.cos_le_cos_of_nonneg_of_le_pi h4nonneg hspi hlo
        rw [Real.cos_pi_div_two_sub] at hmono
        exact hmono.trans (le_max_left _ _)
      · rcases lt_or_ge X 1 with hX1 | hX1
        · have hspi : s ≤ Real.pi := by linarith [hhi, hX1, Real.pi_gt_three]
          have hX2 : Real.pi / 2 + X ≤ Real.pi := by linarith [hX1, Real.pi_gt_three]
          have hcs : Real.cos s ≤ 0 :=
            Real.cos_nonpos_of_pi_div_two_le_of_le hs (by linarith [Real.pi_pos])
          rw [abs_of_nonpos hcs]
          have hmono : Real.cos (Real.pi / 2 + X) ≤ Real.cos s :=
            Real.cos_le_cos_of_nonneg_of_le_pi hs0 hX2 hhi
          rw [show Real.pi / 2 + X = X + Real.pi / 2 by ring, Real.cos_add_pi_div_two] at hmono
          have : -Real.cos s ≤ Real.sin X := by linarith
          exact this.trans ((le_abs_self (Real.sin X)).trans (hsinX.trans (le_max_right _ _)))
        · have h1 : |Real.cos s| ≤ 1 := Real.abs_cos_le_one s
          exact h1.trans (le_trans hX1 (le_max_right _ _))
    have hfin : max (Real.sin (4 * Real.sqrt c)) X ≤ 1000 * Real.sqrt c + 300 * ε₁ * Real.pi := by
      rw [max_le_iff]
      exact ⟨by linarith [Real.sin_le h4, h4, hc0, hε1π], by linarith [hX]⟩
    linarith [hkey, hfin]
  · -- the trivial case: `4√c ≥ π/2`, hence `1000√c ≥ 375 ≥ 1`
    have h1 : (1 : ℝ) ≤ 1000 * Real.sqrt c := by
      nlinarith [Real.pi_gt_three, hbig, hc0]
    linarith [Real.abs_cos_le_one s, h1, hε1π]


open Bundle in
/-- **Basic geometry of the crux's configuration.**

With `q := qpt hmet p e (Fin.succ k)` (so `q = GExp p ((π/2) • e k)` and `rdist p q = π/2`, from
`hinit` and `hON`), and `y := GExp p (s • u)` with `rdist p y = s ≤ π` (`hray`, `hsπ`) and
`fcos q y ≤ -1+c` (`hdip`), the distance `L := rdist q y` satisfies

`π - arccos (1-c) ≤ L ≤ π + arccos (1-c)`.

Indeed `cos L ≤ -(1-c) = cos (π - arccos (1-c))`, and `L ≤ rdist p q + rdist p y ≤ 3π/2`; on
`[0,π]` the cosine is strictly decreasing (giving the lower bound) and on `[π,3π/2]` one has
`cos (L-π) = -cos L`, which is `< 1-c` as soon as `L > π + arccos (1-c)` (giving the upper
bound). -/
theorem dip_basic_geometry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    (hdiam : ∀ y : M, rdist (I := I) (M := M) p y ≤ Real.pi)
    {u : TangentSpace I p} (hu : Inner.inner ℝ u u = 1) {s : ℝ} (hs0 : 0 ≤ s)
    (hsπ : s ≤ Real.pi)
    (hray : rdist (I := I) (M := M) p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) = s)
    {k : Fin (Module.finrank ℝ E)}
    (hdip : fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) ≤ -1 + c) :
    rdist (I := I) (M := M) p (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
        = Real.pi / 2 ∧
    Real.pi - Real.arccos (1 - c)
        ≤ rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
            (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) ∧
    rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))
      ≤ Real.pi + Real.arccos (1 - c) := by
  classical
  have rnn : ∀ x z : M, 0 ≤ rdist (I := I) (M := M) x z := by
    intro x z; rw [rdist]; exact ENNReal.toReal_nonneg
  have rcomm : ∀ x z : M, rdist (I := I) (M := M) x z = rdist (I := I) (M := M) z x := by
    intro x z
    rw [rdist, rdist, Manifold.riemannianEDist_comm]
  have hδmem : Real.arccos (1 - c) ∈ Set.Icc 0 Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  -- `rdist p q ≤ π/2`
  have hek : Inner.inner ℝ (e k) (e k) = 1 := by simpa using hON k k
  have hnorm : ‖e k‖ = 1 := by
    have h2 : ‖e k‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq (e k)]; exact hek
    nlinarith [norm_nonneg (e k)]
  have hqle : rdist (I := I) (M := M) p (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
      ≤ Real.pi / 2 := by
    have h := eik_rdist_GExp_smul_le (I := I) (M := M) (cov := cov) hmet p (e k)
      (t := Real.pi / 2) (by positivity)
    rwa [hnorm, mul_one] at h
  have hqval : fcos (I := I) (M := M)
      (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) p = 0 := (hinit.2.2 k).1
  have hpq0 : rdist (I := I) (M := M) p (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
      = Real.pi / 2 := by
    have hcos : Real.cos (rdist (I := I) (M := M) p
        (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))) = 0 := by
      have h2 := hqval
      change Real.cos (rdist (I := I) (M := M)
        (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) p) = 0 at h2
      rw [rcomm (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) p] at h2
      exact h2
    have hmem1 : rdist (I := I) (M := M) p
        (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) ∈ Set.Icc 0 Real.pi :=
      ⟨rnn _ _, by linarith [hqle, Real.pi_pos]⟩
    have hmem2 : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    refine Real.strictAntiOn_cos.injOn hmem1 hmem2 ?_
    rw [hcos, Real.cos_pi_div_two]
  -- the value `L` and its cosine bound
  have hcosL : Real.cos (rdist (I := I) (M := M)
      (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))) ≤ -(1 - c) := by
    have h2 := hdip
    rw [fFam] at h2
    rw [fcos] at h2
    linarith
  have hLtri : rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))
      ≤ rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) p
        + rdist (I := I) (M := M) p (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) :=
    eik_rdist_triangle_le (I := I) (M := M) (cov := cov) hmet htor _ p _
  have hL32 : rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) ≤ 3 * Real.pi / 2 := by
    rw [rcomm _ p, hpq0, hray] at hLtri
    linarith
  have hδcos : Real.cos (Real.pi - Real.arccos (1 - c)) = -(1 - c) := by
    rw [Real.cos_pi_sub, Real.cos_arccos (by linarith) (by linarith)]
  refine ⟨hpq0, ?_, ?_⟩
  · by_cases hle : rdist (I := I) (M := M)
        (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) ≤ Real.pi
    · by_contra hcon
      push_neg at hcon
      have hLnn : 0 ≤ rdist (I := I) (M := M)
          (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
          (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) := rnn _ _
      have hmem : Real.pi - Real.arccos (1 - c) ∈ Set.Icc 0 Real.pi :=
        ⟨by linarith [hδmem.1, Real.pi_pos], by linarith [hδmem.1]⟩
      have hmono := Real.cos_lt_cos_of_nonneg_of_le_pi hLnn hmem.2 hcon
      rw [hδcos] at hmono
      linarith
    · push_neg at hle
      linarith [hδmem.1]
  · by_cases hle : rdist (I := I) (M := M)
        (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) ≤ Real.pi
    · linarith [hδmem.1]
    · push_neg at hle
      by_contra hcon
      push_neg at hcon
      have hδpos : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
      have hshift : Real.arccos (1 - c) < rdist (I := I) (M := M)
          (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
          (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) - Real.pi := by linarith
      have hle2 : rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
          (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) - Real.pi ≤ Real.pi / 2 := by
        linarith
      have hcosδ : Real.cos (Real.arccos (1 - c)) = 1 - c :=
        Real.cos_arccos (by linarith) (by linarith)
      have hmono := Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hδpos)
        (by linarith [Real.pi_pos]) hshift
      rw [hcosδ] at hmono
      have hsh : Real.cos (rdist (I := I) (M := M)
            (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
            (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) - Real.pi)
          = -Real.cos (rdist (I := I) (M := M)
            (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
            (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))) := Real.cos_sub_pi _
      rw [hsh] at hmono
      linarith

open Bundle in
/-- ROUTE.  Write `q := qpt hmet p e (Fin.succ k)`, so `fFam hmet p e (Fin.succ k) = fcos q = cos ∘ d(q,·)`
and `q = GExp p ((π/2) • e k)`; put `y := GExp p (s • u)` (the point `x` of the application).

(0) `d(p,q) = π/2`: `InitData` gives `fcos q p = 0 = cos (rdist p q)` and `rdist p q ≤ π/2` (the ray from
    `p` in direction `e k` of length `π/2` reaches `q`).  Also `‖e k‖ = 1` and `fcos q p = 0` (both from
    `hinit`/`hON`).

(1) `d(q,y) ∈ [π-δ,π+δ]`, `cos δ = 1-c`: from `hdip`, writing `L := rdist q y`, we get `Real.cos L ≤ -1+c`
    and `L ≤ rdist q p + rdist p y ≤ π/2 + s ≤ 3π/2` (using `hray`); the latter excludes the other branch of
    `cos ≤ -1+c`, so `L ∈ [π-δ, π+δ]`.

(2) Let `η : ℝ → M` be a *minimising* geodesic from `q` to `y` with `η 0 = q`, `η L = y`
    (`Submission.HopfRinow.exists_geodesic_riemannianEDist_eq` gives `v` with `GExp q v = y` and
    `riemannianEDist q y = ‖v‖`; take `η t = GExp q (t • unitOf v)` and use the minimising identity on
    sub-arcs).  Put `g t := rdist p (η t)` and `h t := fcos p (η t) = Real.cos (g t)`.  Then `h 0 = 0`
    (step 0) and `h L = Real.cos s` (step 0 of the application: `hray` says `rdist p y = s`).

(3) Wherever `h t > -1+c` (equivalently `g t < π-δ`): `h` is `C^∞` near `t` (`hsmC` for the centre `p`,
    composed with the smooth `η`), `h'' t = -h t + E t` with `|E t| ≤ ε₁` (`hHess` for the centre `p` on
    `η'(t)`), and `|h' t| ≤ 1` (`hgrad` for the centre `p`, plus `h' = ⟪∇ fcos p, η'⟫`).

(4) Hence on that region `h` is an approximate sinusoid: with `Λ t := h t^2 + (h' t)^2`,
    `Λ' = 2 h' (h''+h) = 2 h' E`, so, starting from `Λ 0 = (h' 0)^2 ≤ 1`, the energy can grow at most like
    `2 ε₁` per unit time; equivalently `h t = A cos t + B sin t + O(ε₁)` with `A = h 0 = 0`,
    `B = h' 0`, `A^2+B^2 ≤ 1 + O(ε₁)`.  In particular (chain rule `h' = -sin g · g'`) the quantity
    `g` cannot leave `[arcsin √(1-Λ₀), π - arcsin √(1-Λ₀)]` on the region, and since `h` is differentiable
    at every point with `h ≥ -1+c` (step 3), the set `{h ≤ -1+c}` is at most an isolated set of tangency
    points: the sinusoid comparison therefore integrates over all of `[0,L]`.

(5) Conclude `|Real.cos s| = |h L| = |B sin L| + O(ε₁) ≤ |sin L| + O(ε₁) ≤ δ + O(ε₁) ≤ √(3c) + O(ε₁)`,
    which is dominated by `100 (finrank ℝ E + 2) (ε₁π + α + √c)` since `finrank ℝ E + 2 ≥ 4`.
    (Any cruder bound on `|Real.cos s|` that still fits under `100 (n+2) (ε₁π+α+√c)` is equally fine.) -/
theorem dip_equator_crux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {α c ε₁ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hε₁ : 0 ≤ ε₁) (hnum1 : 3 * c ≤ 1 - Real.cos α) (hnum2 : 4 * ε₁ * Real.pi < c)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    (hdiam : ∀ y : M, rdist (I := I) (M := M) p y ≤ Real.pi)
    {u : TangentSpace I p} (hu : Inner.inner ℝ u u = 1) {s : ℝ} (hs0 : 0 ≤ s)
    (hsπ : s ≤ Real.pi)
    (hray : rdist (I := I) (M := M) p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) = s)
    {k : Fin (Module.finrank ℝ E)} (hbad : Inner.inner ℝ (e k) u ≤ -Real.cos α)
    (hdip : fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) ≤ -1 + c) :
    |Real.cos s| ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2)
        * (ε₁ * Real.pi + α + Real.sqrt c) := by
  sorry

end Work.Diff.C
