import Mathlib
import Submission.Work.ManifoldParity.exists_continuous_tangent_field

/-!
# The tangent field of a compact locally-graph subset of `ℝⁿ`

We prove `Work.ManifoldParity.graph_tangent_field`: a compact `K ⊆ ℝⁿ` which is *locally the graph
of a smooth function over a coordinate axis* admits a smooth compactly supported `V : ℝⁿ → ℝⁿ`
which is nowhere zero on `K` and parallel to the graph tangent at every point of `K`.

The proof has two parts.

* **The geometric core** (`Work.ManifoldParity.exists_continuous_tangent_field`, a companion chapter):
  such a `K` is a compact `1`-manifold, hence a finite union of circles, and admits a *continuous*
  nowhere-zero tangent field `U` (in the strong chartwise sense).
* **Smoothing and gluing** (`graph_tangent_field_of_continuous`, this file): from such a continuous
  `U` we build a *smooth compactly supported* `V` with the same properties.  Cover `K` by finitely
  many graph patches; on the patch at `p` the graph tangent field `W_p = z ↦ eᵢ + η'(zᵢ)(1)` is
  smooth and nowhere zero, the sign `σ_p` of `⟪U, W_p⟫` is locally constant on a small ball, and
  `σ_p • W_p / ⟪W_p, W_p⟫` is a positive multiple of `U` there; gluing these local fields with
  smooth cut-offs gives `V`.

-/

namespace Work.ManifoldParity

open scoped Topology InnerProductSpace
open Set Metric

variable {n : ℕ}

/-! ## The graph tangent field of a chart -/

/-- The graph tangent field `z ↦ eᵢ + η'(zᵢ)(1)` of the chart `η` over the coordinate `i`. -/
noncomputable def chartField (i : Fin n) (η : ℝ → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun z => EuclideanSpace.single i (1 : ℝ) + (fderiv ℝ η (z i)) (1 : ℝ)

/-- The coordinate projection as a continuous linear map. -/
noncomputable def coordCLM (i : Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin n => ℝ) i

@[simp] theorem coordCLM_apply (i : Fin n) (z : EuclideanSpace ℝ (Fin n)) :
    coordCLM i z = z i := rfl

theorem chartField_smooth (i : Fin n) (η : ℝ → EuclideanSpace ℝ (Fin n))
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chartField i η) := by
  unfold chartField
  refine ContDiff.add contDiff_const ?_
  have huncurry : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (fun (_ : EuclideanSpace ℝ (Fin n)) => η)) := hη.comp contDiff_snd
  have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin n) => fderiv ℝ η (z i)) :=
    ContDiff.fderiv (𝕜 := ℝ) (f := fun (_ : EuclideanSpace ℝ (Fin n)) => η)
      (g := fun z : EuclideanSpace ℝ (Fin n) => z i) huncurry (coordCLM i).contDiff (by simp)
  exact hfd.clm_apply contDiff_const

/-- The `i`-th coordinate of `(fderiv ℝ η t) 1` vanishes when `η` takes values in `{v | v i = 0}`. -/
theorem chartField_fderiv_coord_eq_zero (i : Fin n) (η : ℝ → EuclideanSpace ℝ (Fin n))
    (hη : ∀ t, η t i = 0) {t : ℝ} (hd : DifferentiableAt ℝ η t) :
    ((fderiv ℝ η t) (1 : ℝ)) i = 0 := by
  have h1 : HasDerivAt η (deriv η t) t := hd.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (coordCLM i) (η s))
      (0 + (coordCLM i) (deriv η t)) t :=
    (hasDerivAt_const (x := t) (c := coordCLM i)).clm_apply h1
  have h3 : HasDerivAt (fun s : ℝ => (coordCLM i) (η s)) 0 t := by
    have hc : (fun s : ℝ => (coordCLM i) (η s)) = fun _ : ℝ => (0:ℝ) := by
      funext s; simpa using hη s
    rw [hc]; exact hasDerivAt_const (x := t) (c := (0:ℝ))
  have h4 : 0 + (coordCLM i) (deriv η t) = 0 := h2.unique h3
  have h5 : (coordCLM i) (deriv η t) = 0 := by simpa using h4
  have h6 : (deriv η t) i = 0 := by simpa using h5
  exact h6

theorem chartField_ne_zero (i : Fin n) (η : ℝ → EuclideanSpace ℝ (Fin n))
    (hη : ∀ t, η t i = 0) {z : EuclideanSpace ℝ (Fin n)} (hd : DifferentiableAt ℝ η (z i)) :
    chartField i η z ≠ 0 := by
  intro h
  have hcoord : chartField i η z i = 0 := by rw [h]; simp
  have h1 : chartField i η z i = 1 := by
    simp only [chartField, PiLp.add_apply, PiLp.single_apply, chartField_fderiv_coord_eq_zero i η hη hd,
      add_zero]
    simp
  rw [h1] at hcoord
  exact one_ne_zero hcoord

/-- **Same-sign lemma.**  If `g` is continuous on `K` and `g y ≠ 0` at `y ∈ K`, then near `y` (in
`K`) the sign of `g` is the sign of `g y`. -/
theorem eventually_sign_eq (K : Set (EuclideanSpace ℝ (Fin n))) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ContinuousOn g K) {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ K) (hgy : g y ≠ 0) :
    ∃ ρ > 0, ∀ z ∈ K, dist z y < ρ →
      0 < (if 0 < g y then (1 : ℝ) else -1) * g z := by
  have hε : (0 : ℝ) < |g y| := abs_pos.mpr hgy
  obtain ⟨δ, hδ, hδ'⟩ :=
    Metric.continuousWithinAt_iff.mp (hg.continuousWithinAt hy) |g y| hε
  refine ⟨δ, hδ, fun z hz hzd => ?_⟩
  have hdist : |g z - g y| < |g y| := by
    have := hδ' hz hzd
    rwa [Real.dist_eq] at this
  rcases lt_or_gt_of_ne hgy.symm with hpos | hneg
  · rw [if_pos hpos]
    have := (abs_lt.mp hdist).1
    linarith [abs_of_pos hpos]
  · rw [if_neg (not_lt.mpr hneg.le)]
    have := (abs_lt.mp hdist).2
    have : |g y| = -g y := abs_of_neg hneg
    linarith
/-- **Gluing lemma.**  From a *continuous* nowhere-zero tangent field `U₀` along a compact
locally-graph set `K` build a smooth compactly supported field with the same properties. -/
theorem graph_tangent_field_of_continuous (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K)
    (hgra : ∀ x ∈ K, ∃ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
        (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧
          (∀ t, (η t) i = 0) ∧
          ∀ y ∈ U, (y ∈ K ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i)))
    (U₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hU₀cont : ContinuousOn U₀ K)
    (hU₀ne : ∀ x ∈ K, U₀ x ≠ 0)
    (hU₀par : ∀ x ∈ K, ∀ (i : Fin n) (V : Set (EuclideanSpace ℝ (Fin n)))
        (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen V → x ∈ V → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η →
        (∀ t, (η t) i = 0) →
        (∀ y ∈ V, (y ∈ K ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i))) →
        ∃ c : ℝ, c ≠ 0 ∧ U₀ x = c • (EuclideanSpace.single i (1:ℝ) + (fderiv ℝ η (x i)) (1:ℝ)))
    : ∃ V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧ HasCompactSupport V ∧
        (∀ x ∈ K, V x ≠ 0) ∧
        (∀ x ∈ K, ∀ (i : Fin n) (V' : Set (EuclideanSpace ℝ (Fin n)))
            (η : ℝ → EuclideanSpace ℝ (Fin n)),
          IsOpen V' → x ∈ V' → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η →
          (∀ t, (η t) i = 0) →
          (∀ y ∈ V', (y ∈ K ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i))) →
          ∃ c : ℝ, c ≠ 0 ∧
            V x = c • (EuclideanSpace.single i (1:ℝ) + (fderiv ℝ η (x i)) (1:ℝ))) := by
  classical
  -- ## Step 1: at every point of `K` pick a graph chart, a ball and a locally constant sign.
  have hdata : ∀ p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K},
      ∃ (idx : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (η : ℝ → EuclideanSpace ℝ (Fin n))
        (ρ : ℝ) (σ : ℝ),
        0 < ρ ∧ IsOpen S ∧ p.1 ∈ S ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧
        (∀ t, η t idx = 0) ∧
        (∀ y ∈ S, (y ∈ K ↔ y = (y idx) • EuclideanSpace.single idx (1:ℝ) + η (y idx))) ∧
        Metric.closedBall p.1 (2 * ρ) ⊆ S ∧
        (σ = 1 ∨ σ = -1) ∧
        (∀ z ∈ K, dist z p.1 ≤ 2 * ρ → 0 < σ * ⟪U₀ z, chartField idx η z⟫_ℝ) := by
    intro p
    obtain ⟨i, S, η, hSopen, hpS, hηsmooth, hη0, hgraph⟩ := hgra p.1 p.2
    obtain ⟨c, hc, hpar⟩ := hU₀par p.1 p.2 i S η hSopen hpS hηsmooth hη0 hgraph
    have hWne : chartField i η p.1 ≠ 0 :=
      chartField_ne_zero i η hη0 (hηsmooth.differentiable (by simp)).differentiableAt
    have hin : (0 : ℝ) < ⟪chartField i η p.1, chartField i η p.1⟫_ℝ := real_inner_self_pos.mpr hWne
    have hg_ne : ⟪U₀ p.1, chartField i η p.1⟫_ℝ ≠ 0 := by
      rw [hpar, real_inner_smul_left]
      exact mul_ne_zero hc (ne_of_gt hin)
    have hcont : ContinuousOn (fun z => ⟪U₀ z, chartField i η z⟫_ℝ) K :=
      hU₀cont.inner (chartField_smooth i η hηsmooth).continuous.continuousOn
    obtain ⟨δ, hδ, hsign⟩ := eventually_sign_eq K hcont p.2 hg_ne
    obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.mp hSopen p.1 hpS
    refine ⟨i, S, η, min (ε / 4) (δ / 4),
      if 0 < ⟪U₀ p.1, chartField i η p.1⟫_ℝ then 1 else -1,
      lt_min (by linarith) (by linarith), hSopen, hpS, hηsmooth, hη0, hgraph, ?_, ?_, ?_⟩
    · intro z hz
      refine hεS ?_
      have h2 : 2 * min (ε / 4) (δ / 4) ≤ ε / 2 := by
        have := min_le_left (ε / 4) (δ / 4); linarith
      have h3 : dist z p.1 ≤ 2 * min (ε / 4) (δ / 4) := Metric.mem_closedBall.mp hz
      have : dist z p.1 < ε := lt_of_le_of_lt (le_trans h3 h2) (by linarith)
      simpa [Metric.mem_ball, dist_comm] using this
    · split_ifs <;> simp
    · intro z hz hzd
      refine hsign z hz ?_
      have h2 : 2 * min (ε / 4) (δ / 4) < δ := by
        have := min_le_right (ε / 4) (δ / 4); linarith
      exact lt_of_le_of_lt hzd h2
  choose idx S η ρ σ hρ hSopen hpS hηsmooth hη0 hgraph hball hσ hsign using hdata
  -- ## Step 2: finitely many patches cover `K`.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K} =>
      Metric.ball p.1 (ρ p)) (fun p => Metric.isOpen_ball) (fun x hx => by
        refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
        exact Metric.mem_ball_self (hρ ⟨x, hx⟩))
  -- ## Step 3: the cut-off bumps and the local fields.
  let bump : ∀ p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K}, ContDiffBump p.1 := fun p =>
    ⟨ρ p, 2 * ρ p, hρ p, by linarith [hρ p]⟩
  let χ : ∀ p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K}, EuclideanSpace ℝ (Fin n) → ℝ :=
    fun p => (bump p : EuclideanSpace ℝ (Fin n) → ℝ)
  let Wf : {x : EuclideanSpace ℝ (Fin n) // x ∈ K} → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) := fun p => chartField (idx p) (η p)
  let Ŵ : {x : EuclideanSpace ℝ (Fin n) // x ∈ K} → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) := fun p z => (⟪Wf p z, Wf p z⟫_ℝ)⁻¹ • Wf p z
  let V₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z => ∑ p ∈ t, χ p z • (σ p • Ŵ p z)
  have hWfsmooth : ∀ p, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Wf p) := fun p =>
    chartField_smooth (idx p) (η p) (hηsmooth p)
  have hWfne : ∀ p z, Wf p z ≠ 0 := fun p z => by
    rw [show Wf p z = chartField (idx p) (η p) z from rfl]
    exact chartField_ne_zero (idx p) (η p) (hη0 p)
      ((hηsmooth p).differentiable (by simp)).differentiableAt
  have hV₀smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V₀ := by
    refine ContDiff.sum (f := fun (p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K})
      (z : EuclideanSpace ℝ (Fin n)) => χ p z • (σ p • Ŵ p z)) fun p hp => ?_
    refine ContDiff.smul ((bump p).contDiff (n := ⊤)) ?_
    refine ContDiff.const_smul (σ p) ?_
    have hinv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (⟪Wf p z, Wf p z⟫_ℝ)⁻¹) :=
      (ContDiff.inner ℝ (hWfsmooth p) (hWfsmooth p)).inv
        (fun z => inner_self_ne_zero.mpr (hWfne p z))
    exact hinv.smul (hWfsmooth p)
  -- ## Step 4: for `x ∈ K`, `V₀ x` is a *positive* multiple of `U₀ x`.
  have hmultiples : ∀ x ∈ K, ∃ a : ℝ, 0 < a ∧ V₀ x = a • U₀ x := by
    intro x hx
    have key : ∀ p ∈ t, ∃ μ : ℝ, 0 ≤ μ ∧ (χ p x ≠ 0 → 0 < μ) ∧
        χ p x • (σ p • Ŵ p x) = (χ p x * μ) • U₀ x := by
      intro p hp
      by_cases hχ : χ p x = 0
      · exact ⟨0, le_refl 0, fun h => (h hχ).elim, by rw [hχ, zero_mul, zero_smul, zero_smul]⟩
      · have hxts : x ∈ tsupport (χ p) := subset_tsupport _ (Function.mem_support.mpr hχ)
        rw [show tsupport (χ p) = Metric.closedBall p.1 (2 * ρ p) from
          ContDiffBump.tsupport_eq (bump p)] at hxts
        have hxd : dist x p.1 ≤ 2 * ρ p := Metric.mem_closedBall.mp hxts
        have hxS : x ∈ S p := hball p (Metric.mem_closedBall.mpr hxd)
        obtain ⟨c, hc, hpar⟩ := hU₀par x hx (idx p) (S p) (η p) (hSopen p) hxS
          (hηsmooth p) (hη0 p) (hgraph p)
        have hWne : Wf p x ≠ 0 := hWfne p x
        have hin : (0 : ℝ) < ⟪Wf p x, Wf p x⟫_ℝ := real_inner_self_pos.mpr hWne
        have hpos : 0 < σ p * (c * ⟪Wf p x, Wf p x⟫_ℝ) := by
          have h1 := hsign p x hx hxd
          rwa [show ⟪U₀ x, Wf p x⟫_ℝ = c * ⟪Wf p x, Wf p x⟫_ℝ by
            rw [show U₀ x = c • Wf p x from hpar, real_inner_smul_left]] at h1
        have hsc : 0 < σ p * c := by
          have h2 : 0 < (σ p * c) * ⟪Wf p x, Wf p x⟫_ℝ := by rw [mul_assoc]; exact hpos
          rcases mul_pos_iff.mp h2 with ⟨h, _⟩ | ⟨h, hlt⟩
          · exact h
          · exact absurd hlt (not_lt.mpr hin.le)
        have hcpos : 0 < σ p * c⁻¹ := by
          rcases lt_trichotomy c 0 with hneg | hzero | hpos
          · have hσ : σ p < 0 := by
              by_contra h
              push_neg at h
              exact absurd hsc (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos h hneg.le))
            exact mul_pos_of_neg_of_neg hσ (inv_neg''.mpr hneg)
          · exact (hc hzero).elim
          · have hσ : 0 < σ p := by
              by_contra h
              push_neg at h
              exact absurd hsc (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg h hpos.le))
            exact mul_pos hσ (inv_pos.mpr hpos)
        have hWs : Wf p x = c⁻¹ • U₀ x := by
          conv_rhs => rw [hpar]
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
          rfl
        refine ⟨(σ p * c⁻¹) * (⟪Wf p x, Wf p x⟫_ℝ)⁻¹, ?_, fun _ => ?_, ?_⟩
        · exact (mul_pos hcpos (inv_pos.mpr hin)).le
        · exact mul_pos hcpos (inv_pos.mpr hin)
        · simp only [Ŵ, hWs, smul_smul]
          congr 1
          ring
    choose μ hμ hμpos hμeq using key
    set M : {x : EuclideanSpace ℝ (Fin n) // x ∈ K} → ℝ :=
      fun p => if hp : p ∈ t then μ p hp else 0 with hM
    have hMapp : ∀ (p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K}) (hp : p ∈ t), M p = μ p hp :=
      fun p hp => by simp only [hM, dif_pos hp]
    have hxcover : x ∈ ⋃ p ∈ t, Metric.ball p.1 (ρ p) := ht hx
    simp only [mem_iUnion, exists_prop] at hxcover
    obtain ⟨p₀, hp₀t, hp₀x⟩ := hxcover
    have hχp₀ : χ p₀ x = 1 := by
      refine ContDiffBump.one_of_mem_closedBall (bump p₀) ?_
      exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp hp₀x).le
    have h1 : ∀ p ∈ t, χ p x • (σ p • Ŵ p x) = (χ p x * M p) • U₀ x := by
      intro p hp
      rw [hMapp p hp]
      exact hμeq p hp
    have hV₀x : V₀ x = (∑ p ∈ t, χ p x * M p) • U₀ x := by
      show (∑ p ∈ t, χ p x • (σ p • Ŵ p x)) = (∑ p ∈ t, χ p x * M p) • U₀ x
      rw [Finset.sum_congr rfl h1, Finset.sum_smul]
    have hcoeff : 0 < ∑ p ∈ t, χ p x * M p := by
      refine Finset.sum_pos' (fun q hq => mul_nonneg (bump q).nonneg ?_) ⟨p₀, hp₀t, ?_⟩
      · rw [hMapp q hq]; exact hμ q hq
      · rw [hχp₀, one_mul, hMapp p₀ hp₀t]
        exact hμpos p₀ hp₀t (by rw [hχp₀]; norm_num)
    exact ⟨_, hcoeff, hV₀x⟩
  -- ## Step 5: the compactly supported global cut-off.
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn)
  have hR' : ∀ x ∈ K, ‖x‖ ≤ R := fun x hx => by simpa using hR x hx
  let βb : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨|R| + 3, |R| + 4, by positivity, by linarith⟩
  let β : EuclideanSpace ℝ (Fin n) → ℝ := (βb : EuclideanSpace ℝ (Fin n) → ℝ)
  have hβone : ∀ x ∈ K, β x = 1 := by
    intro x hx
    have h1 : dist x (0 : EuclideanSpace ℝ (Fin n)) ≤ |R| + 3 := by
      rw [dist_zero_right]
      have h2 : ‖x‖ ≤ |R| := le_trans (hR' x hx) (le_abs_self R)
      linarith
    refine ContDiffBump.one_of_mem_closedBall βb ?_
    simpa [Metric.mem_closedBall] using h1
  have hsupp : HasCompactSupport (β • V₀) := βb.hasCompactSupport.smul_right
  refine ⟨β • V₀, ContDiff.smul βb.contDiff hV₀smooth, hsupp, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, haeq⟩ := hmultiples x hx
    show β x • V₀ x ≠ 0
    rw [hβone x hx, one_smul, haeq]
    exact smul_ne_zero (ne_of_gt ha) (hU₀ne x hx)
  · intro x hx i V' η hV'open hxV' hηsmooth' hη0' hgraph'
    obtain ⟨a, ha, haeq⟩ := hmultiples x hx
    obtain ⟨c, hc, hpar⟩ := hU₀par x hx i V' η hV'open hxV' hηsmooth' hη0' hgraph'
    refine ⟨a * c, mul_ne_zero (ne_of_gt ha) hc, ?_⟩
    show β x • V₀ x = (a * c) • (EuclideanSpace.single i (1:ℝ) + (fderiv ℝ η (x i)) (1:ℝ))
    rw [hβone x hx, one_smul, haeq, hpar, smul_smul]

/-- **The requested lemma.**  A compact subset of `ℝⁿ` which is locally the graph of a smooth
function over a coordinate axis admits a smooth compactly supported vector field which is nowhere
zero on `K` and parallel to the graph tangent at every point of `K`. -/
theorem graph_tangent_field {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K)
    (hgra : ∀ x ∈ K, ∃ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
        (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧
          (∀ t, (η t) i = 0) ∧
          ∀ y ∈ U, (y ∈ K ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i)))
    : ∃ V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧ HasCompactSupport V ∧
        (∀ x ∈ K, V x ≠ 0) ∧
        (∀ x ∈ K, ∀ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
            (η : ℝ → EuclideanSpace ℝ (Fin n)),
          IsOpen U → x ∈ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η →
          (∀ t, (η t) i = 0) →
          (∀ y ∈ U, (y ∈ K ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i))) →
          ∃ c : ℝ, c ≠ 0 ∧
            V x = c • (EuclideanSpace.single i (1:ℝ) + (fderiv ℝ η (x i)) (1:ℝ))) := by
  obtain ⟨U, hcont, hne, htan⟩ := exists_continuous_tangent_field K hK hgra
  exact graph_tangent_field_of_continuous K hK hgra U hcont hne htan

end Work.ManifoldParity
