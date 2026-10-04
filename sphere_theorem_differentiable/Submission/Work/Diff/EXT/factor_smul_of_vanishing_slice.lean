import Mathlib
import Submission.Work.Diff.EXT.hasFDerivWithinAt_intervalIntegral_of_lipschitz
import Submission.Work.Diff.EXT.exists_bound_near_compact_of_continuousWithinAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Hadamard's lemma on a slab: division by the time variable

`factor_smul_of_vanishing_slice`: if `G : ℝ × E → Z` is `C^∞` on the slab `(Ico 0 T) ×ˢ U`
(`T > 0`, `U` open) and vanishes on the initial slice `{0} × U`, then `G = p.1 • Ψ p` for some
`Ψ` which is `C^∞` on the same slab.

The proof is Hadamard's classical argument: for `p ∈ s := (Ico 0 T) ×ˢ U` put

`Ψ p = ∫ s in 0..1, ∂_t G (p.1 * s, p.2) ds`

(the mean value of the time derivative along the ray from the seam point `(0, p.2)` to `p`).  Then
the fundamental theorem of calculus gives `p.1 • Ψ p = G p - G (0, p.2) = G p`, and `Ψ` is smooth
on the slab.

Smoothness of the parameter dependent ray integral

`rayInt M p = ∫ s in 0..1, M ((p.1 * s, p.2), s) ds`

is proved by induction on the order of differentiability: at every point of the slab the function
`rayInt M` has within-slab derivative `rayInt (rayDeriv M)`, where `rayDeriv M` is again a `C^∞`
family (with values in the space of continuous linear maps), so that the induction can be
restarted.  The single differentiation step uses differentiation under the integral sign for a
parameter restricted to a subset `B` (`hasFDerivWithinAt_intervalIntegral_of_lipschitz`), with the
Lipschitz bound obtained from the mean value theorem on a convex set `B ⊆ s`.

Note on universes: the induction applies the statement to the derivative family, whose values
live in `(ℝ × E) →L[ℝ] W`; hence the induction is first carried out for targets in the universe
`max u v` of the domain (where `W ↦ (ℝ × E) →L[ℝ] W` is stable), and the general case is reduced
to that one by a single step.
-/

open Set Metric Filter
open scoped Topology ContDiff Interval MeasureTheory

universe u v

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The linear map `v ↦ (s * v.1, v.2)` on `ℝ × E`. -/
noncomputable def rayL (s : ℝ) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  (s • ContinuousLinearMap.fst ℝ ℝ E).prod (ContinuousLinearMap.snd ℝ ℝ E)

@[simp]
theorem rayL_apply (s : ℝ) (v : ℝ × E) : rayL (E := E) s v = (s * v.1, v.2) := rfl

theorem rayL_eq (s : ℝ) : rayL (E := E) s =
    s • ((ContinuousLinearMap.fst ℝ ℝ E).prod 0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
      ((0 : (ℝ × E) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ E)) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [rayL, ContinuousLinearMap.prod_apply, add_apply, smul_apply, zero_apply]
  exact Prod.ext (by simp [smul_eq_mul]) (by simp)

theorem norm_rayL_le_one {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : ‖rayL (E := E) s‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [rayL_apply, Prod.norm_def]
  refine max_le ?_ ?_
  · have h1' : ‖s * v.1‖ ≤ ‖v‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, ← Real.norm_eq_abs]
      calc s * ‖v.1‖ ≤ 1 * ‖v.1‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖v.1‖ := one_mul _
        _ ≤ ‖v‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    calc ‖s * v.1‖ ≤ ‖v‖ := h1'
      _ = 1 * ‖v‖ := (one_mul _).symm
  · have h2' : ‖v.2‖ ≤ ‖v‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    calc ‖v.2‖ ≤ ‖v‖ := h2'
      _ = 1 * ‖v‖ := (one_mul _).symm

theorem contDiff_rayL : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => rayL (E := E) s) := by
  have hA : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => s • ((ContinuousLinearMap.fst ℝ ℝ E).prod 0 :
        (ℝ × E) →L[ℝ] (ℝ × E)) +
        ((0 : (ℝ × E) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ E))) :=
    (contDiff_id.smul contDiff_const).add contDiff_const
  rw [show (fun s : ℝ => rayL (E := E) s) = fun s : ℝ =>
      s • ((ContinuousLinearMap.fst ℝ ℝ E).prod 0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
        ((0 : (ℝ × E) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ E)) from
    funext rayL_eq]
  exact hA

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **Ray integral**: `rayInt M p = ∫ s in 0..1, M ((p.1 * s, p.2), s)`. -/
noncomputable def rayInt (M : (ℝ × E) × ℝ → Z) : ℝ × E → Z :=
  fun p => ∫ s in (0 : ℝ)..1, M ((s * p.1, p.2), s)

/-- The partial derivative of `M` in the first (space–time) variable. -/
noncomputable def rayPartial (K : Set ((ℝ × E) × ℝ)) (M : (ℝ × E) × ℝ → Z) :
    (ℝ × E) × ℝ → ((ℝ × E) →L[ℝ] Z) :=
  fun qs => (fderivWithin ℝ M K qs).comp (ContinuousLinearMap.inl ℝ (ℝ × E) ℝ)

/-- The formal derivative of the family `M` under the ray integral: the partial derivative in the
first (space–time) variable, composed with `v ↦ (s * v.1, v.2)`. -/
noncomputable def rayDeriv (K : Set ((ℝ × E) × ℝ)) (M : (ℝ × E) × ℝ → Z) :
    (ℝ × E) × ℝ → ((ℝ × E) →L[ℝ] Z) :=
  fun qs => (rayPartial K M qs).comp (rayL (E := E) qs.2)

variable {T : ℝ} {U : Set E}

/-- `(Ico 0 T) ×ˢ U` is a set of unique differentiability. -/
theorem uniqueDiffOn_slab (hU : IsOpen U) : UniqueDiffOn ℝ (Set.Ico 0 T ×ˢ U) :=
  (uniqueDiffOn_Ico 0 T).prod hU.uniqueDiffOn

theorem contDiffOn_fderivWithin_slab {K : Set ((ℝ × E) × ℝ)} {M : (ℝ × E) × ℝ → Z}
    (hM : ContDiffOn ℝ (⊤ : ℕ∞) M K) (hK : UniqueDiffOn ℝ K) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun qs => fderivWithin ℝ M K qs) K :=
  fun qs hqs => (hM.contDiffWithinAt hqs).fderivWithin_right hK (by simp) hqs

theorem contDiffOn_rayPartial {K : Set ((ℝ × E) × ℝ)} {M : (ℝ × E) × ℝ → Z}
    (hM : ContDiffOn ℝ (⊤ : ℕ∞) M K) (hK : UniqueDiffOn ℝ K) :
    ContDiffOn ℝ (⊤ : ℕ∞) (rayPartial K M) K := by
  have hD : ContDiffOn ℝ (⊤ : ℕ∞) (fun qs => fderivWithin ℝ M K qs) K :=
    contDiffOn_fderivWithin_slab hM hK
  have hfun : rayPartial K M = fun qs : (ℝ × E) × ℝ =>
      (fderivWithin ℝ M K qs).comp (ContinuousLinearMap.inl ℝ (ℝ × E) ℝ) := rfl
  rw [hfun]
  exact hD.clm_comp contDiffOn_const

theorem contDiffOn_rayDeriv {K : Set ((ℝ × E) × ℝ)} {M : (ℝ × E) × ℝ → Z}
    (hM : ContDiffOn ℝ (⊤ : ℕ∞) M K) (hK : UniqueDiffOn ℝ K) :
    ContDiffOn ℝ (⊤ : ℕ∞) (rayDeriv K M) K := by
  have hP : ContDiffOn ℝ (⊤ : ℕ∞) (rayPartial K M) K := contDiffOn_rayPartial hM hK
  have hL : ContDiffOn ℝ (⊤ : ℕ∞) (fun qs : (ℝ × E) × ℝ => rayL (E := E) qs.2) K :=
    (contDiff_rayL (E := E)).comp_contDiffOn contDiffOn_snd
  have hfun : rayDeriv K M = fun qs : (ℝ × E) × ℝ =>
      (rayPartial K M qs).comp (rayL (E := E) qs.2) := rfl
  rw [hfun]
  exact hP.clm_comp hL

/-- **Single-step differentiation of the ray integral.**  At every point `p` of the slab, `rayInt M`
has within-slab derivative `rayInt (rayDeriv M)` evaluated at `p`. -/
theorem hasFDerivWithinAt_rayInt (hT : 0 < T) (hU : IsOpen U)
    {M : (ℝ × E) × ℝ → Z} [CompleteSpace Z]
    (hM : ContDiffOn ℝ (⊤ : ℕ∞) M ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∀ p ∈ (Set.Ico 0 T ×ˢ U),
      HasFDerivWithinAt (rayInt M)
        (rayInt (rayDeriv ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1) M) p)
        (Set.Ico 0 T ×ˢ U) p := by
  intro p₀ hp₀
  obtain ⟨ht₀, hy₀⟩ := hp₀
  obtain ⟨ρ, hρpos, hρU⟩ : ∃ ρ > 0, Metric.ball p₀.2 ρ ⊆ U :=
    Metric.isOpen_iff.mp hU p₀.2 hy₀
  set K : Set ((ℝ × E) × ℝ) := (Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1 with hK
  have hK_unique : UniqueDiffOn ℝ K :=
    (uniqueDiffOn_slab (T := T) hU).prod (uniqueDiffOn_Icc zero_lt_one)
  -- the compact family of base points of the rays through `p₀`
  set Cfam : Set ((ℝ × E) × ℝ) :=
    (fun a : ℝ => ((p₀.1 * a, p₀.2), a)) '' (Set.Icc (0 : ℝ) 1) with hCfam
  have hCfam_ne : Cfam.Nonempty :=
    ⟨((p₀.1 * 0, p₀.2), 0), 0, ⟨le_refl 0, zero_le_one⟩, rfl⟩
  have hCfam_sub : Cfam ⊆ K := by
    rw [hK, hCfam]
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨⟨⟨mul_nonneg ht₀.1 ha.1,
      lt_of_le_of_lt (mul_le_of_le_one_right ht₀.1 ha.2) ht₀.2⟩, hy₀⟩, ha⟩
  have hCfam_cpt : IsCompact Cfam := by
    rw [hCfam]
    exact IsCompact.image isCompact_Icc
      (((continuous_const.mul continuous_id).prodMk continuous_const).prodMk continuous_id)
  obtain ⟨rb, hrb, M₀, hM₀⟩ := exists_bound_near_compact_of_continuousWithinAt hCfam_ne
    hCfam_sub hCfam_cpt
    (fun qs hqs => (contDiffOn_fderivWithin_slab hM hK_unique).contDiffWithinAt hqs
      |>.continuousWithinAt)
  set C₀ : ℝ := max M₀ 0 + 1 with hC₀
  -- the convex set `B` on which the slices are controlled
  set B : Set (ℝ × E) :=
    ((Set.Ico 0 T ×ˢ (Set.univ : Set E)) ∩ (Set.univ ×ˢ Metric.ball p₀.2 ρ)) ∩ Metric.ball p₀ rb
    with hB
  have hBmem : ∀ x : ℝ × E, x ∈ B ↔
      x.1 ∈ Set.Ico 0 T ∧ x.2 ∈ Metric.ball p₀.2 ρ ∧ x ∈ Metric.ball p₀ rb := by
    intro x
    rw [hB]
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]
    tauto
  have hBconv : Convex ℝ B := by
    rw [hB]
    exact Convex.inter (Convex.inter ((convex_Ico (0:ℝ) T).prod convex_univ)
      (convex_univ.prod (convex_ball _ _))) (convex_ball _ _)
  have hB_sub : B ⊆ Set.Ico 0 T ×ˢ U := by
    intro x hx
    obtain ⟨hxI, hxρ, -⟩ := (hBmem x).mp hx
    exact ⟨hxI, hρU hxρ⟩
  have hp₀B : p₀ ∈ B := by
    rw [hBmem]
    exact ⟨ht₀, Metric.mem_ball_self hρpos, Metric.mem_ball_self hrb⟩
  have hB_nhds : B ∈ 𝓝[Set.Ico 0 T ×ˢ U] p₀ := by
    have hV : Metric.ball p₀ rb ∩ (Set.univ ×ˢ Metric.ball p₀.2 ρ) ∈ 𝓝 p₀ :=
      Filter.inter_mem (Metric.ball_mem_nhds p₀ hrb)
        ((isOpen_univ.prod Metric.isOpen_ball).mem_nhds
          ⟨trivial, Metric.mem_ball_self hρpos⟩)
    refine mem_of_superset (inter_mem_nhdsWithin _ hV) ?_
    rintro x ⟨hxS, hxb, hxρ⟩
    rw [hBmem]
    exact ⟨hxS.1, hxρ.2, hxb⟩
  -- the family and its formal derivative
  set F : (ℝ × E) → ℝ → Z := fun x a => M ((a * x.1, x.2), a) with hF
  set F' : ℝ → (ℝ × E) →L[ℝ] Z := fun a => rayDeriv K M ((a * p₀.1, p₀.2), a) with hF'
  -- the norm bound on the formal derivative
  have hray_bound : ∀ (x : ℝ × E) (a : ℝ), x ∈ B → a ∈ Set.Icc (0:ℝ) 1 →
      ‖rayDeriv K M ((a * x.1, x.2), a)‖ ≤ C₀ := by
    intro x a hxB ha
    obtain ⟨hxI, hxρ, hxb⟩ := (hBmem x).mp hxB
    have hmemC : ((p₀.1 * a, p₀.2), a) ∈ Cfam := by rw [hCfam]; exact ⟨a, ha, rfl⟩
    have hx0 : ‖x - p₀‖ < rb := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hxb
    have hd : dist ((a * x.1, x.2), a) ((p₀.1 * a, p₀.2), a) < rb := by
      have h1 : ‖a * x.1 - p₀.1 * a‖ ≤ ‖x - p₀‖ := by
        rw [show a * x.1 - p₀.1 * a = a * (x.1 - p₀.1) by ring, Real.norm_eq_abs, abs_mul]
        refine le_trans (mul_le_of_le_one_left (abs_nonneg _) ?_) ?_
        · rw [abs_of_nonneg ha.1]; exact ha.2
        · rw [← Real.norm_eq_abs, Prod.norm_def]
          exact le_max_left _ _
      have h2 : ‖x.2 - p₀.2‖ ≤ ‖x - p₀‖ := by
        rw [Prod.norm_def]; exact le_max_right _ _
      rw [dist_eq_norm, Prod.norm_def, Prod.norm_def]
      exact max_lt (max_lt (lt_of_le_of_lt h1 hx0) (lt_of_le_of_lt h2 hx0)) (by simpa using hrb)
    have hxK : ((a * x.1, x.2), a) ∈ K := by
      rw [hK]
      exact ⟨⟨⟨mul_nonneg ha.1 hxI.1,
        lt_of_le_of_lt (mul_le_of_le_one_left hxI.1 ha.2) hxI.2⟩, hρU hxρ⟩, ha⟩
    have hDbound : ‖fderivWithin ℝ M K ((a * x.1, x.2), a)‖ ≤ M₀ := hM₀ _ hxK ⟨_, hmemC, hd⟩
    have hray : rayDeriv K M ((a * x.1, x.2), a)
        = ((fderivWithin ℝ M K ((a * x.1, x.2), a)).comp
            (ContinuousLinearMap.inl ℝ (ℝ × E) ℝ)).comp (rayL (E := E) a) := rfl
    rw [hray]
    calc ‖((fderivWithin ℝ M K ((a * x.1, x.2), a)).comp
            (ContinuousLinearMap.inl ℝ (ℝ × E) ℝ)).comp (rayL (E := E) a)‖
        ≤ ‖(fderivWithin ℝ M K ((a * x.1, x.2), a)).comp
            (ContinuousLinearMap.inl ℝ (ℝ × E) ℝ)‖ * ‖rayL (E := E) a‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖(fderivWithin ℝ M K ((a * x.1, x.2), a)).comp
            (ContinuousLinearMap.inl ℝ (ℝ × E) ℝ)‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_rayL_le_one ha.1 ha.2) (norm_nonneg _)
      _ = ‖(fderivWithin ℝ M K ((a * x.1, x.2), a)).comp
            (ContinuousLinearMap.inl ℝ (ℝ × E) ℝ)‖ := mul_one _
      _ ≤ ‖fderivWithin ℝ M K ((a * x.1, x.2), a)‖ * ‖ContinuousLinearMap.inl ℝ (ℝ × E) ℝ‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderivWithin ℝ M K ((a * x.1, x.2), a)‖ * 1 :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℝ (ℝ × E) ℝ) (norm_nonneg _)
      _ = ‖fderivWithin ℝ M K ((a * x.1, x.2), a)‖ := mul_one _
      _ ≤ M₀ := hDbound
      _ ≤ C₀ := by rw [hC₀]; linarith [le_max_left M₀ 0, le_max_right M₀ 0]
  -- the chain rule for the slices
  have hchain : ∀ (x : ℝ × E) (a : ℝ), x ∈ B → a ∈ Set.Icc (0:ℝ) 1 →
      HasFDerivWithinAt (fun x' : ℝ × E => M ((rayL (E := E) a x', a)))
        (rayDeriv K M ((a * x.1, x.2), a)) B x := by
    intro x a hxB ha
    obtain ⟨hxI, hxρ, -⟩ := (hBmem x).mp hxB
    have hq : ((a * x.1, x.2), a) ∈ K := by
      rw [hK]
      exact ⟨⟨⟨mul_nonneg ha.1 hxI.1,
        lt_of_le_of_lt (mul_le_of_le_one_left hxI.1 ha.2) hxI.2⟩, hρU hxρ⟩, ha⟩
    have hMK : HasFDerivWithinAt M (fderivWithin ℝ M K ((a * x.1, x.2), a)) K
        ((a * x.1, x.2), a) :=
      ((hM.contDiffWithinAt hq).differentiableWithinAt (by simp)).hasFDerivWithinAt
    have hψ : HasFDerivWithinAt (fun x' : ℝ × E => (rayL (E := E) a x', a))
        ((rayL (E := E) a).prod 0) B x :=
      ((rayL (E := E) a).hasFDerivWithinAt).prodMk (hasFDerivWithinAt_const a x B)
    have hmap : MapsTo (fun x' : ℝ × E => (rayL (E := E) a x', a)) B K := by
      intro x' hx'B
      obtain ⟨hx'I, hx'ρ, -⟩ := (hBmem x').mp hx'B
      rw [hK]
      refine ⟨⟨?_, ?_⟩, ha⟩
      · simp only [rayL_apply]
        exact ⟨mul_nonneg ha.1 hx'I.1,
          lt_of_le_of_lt (mul_le_of_le_one_left hx'I.1 ha.2) hx'I.2⟩
      · simp only [rayL_apply]
        exact hρU hx'ρ
    have hcomp : HasFDerivWithinAt (fun x' : ℝ × E => M ((rayL (E := E) a x', a)))
        ((fderivWithin ℝ M K ((a * x.1, x.2), a)).comp ((rayL (E := E) a).prod 0)) B x :=
      HasFDerivWithinAt.comp (f := fun x' : ℝ × E => (rayL (E := E) a x', a)) (g := M)
        (x := x) hMK hψ hmap
    have hder : (fderivWithin ℝ M K ((a * x.1, x.2), a)).comp ((rayL (E := E) a).prod 0)
        = rayDeriv K M ((a * x.1, x.2), a) := by
      refine ContinuousLinearMap.ext fun w => ?_
      simp only [rayDeriv, rayPartial, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.prod_apply, rayL_apply, ContinuousLinearMap.inl_apply, zero_apply]
    rwa [hder] at hcomp
  -- the slices are continuous (hence interval integrable) and satisfy the Lipschitz bound
  have hF_int : ∀ x ∈ B, IntervalIntegrable (F x) MeasureTheory.volume (0 : ℝ) 1 := by
    intro x hxB
    have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => ((a * x.1, x.2), a)) :=
      ((contDiff_id.mul contDiff_const).prodMk contDiff_const).prodMk contDiff_id
    have hmap : MapsTo (fun a : ℝ => ((a * x.1, x.2), a)) (Set.uIcc (0:ℝ) 1) K := by
      intro a ha
      obtain ⟨hxI, hxρ, -⟩ := (hBmem x).mp hxB
      rw [Set.uIcc_of_le zero_le_one] at ha
      rw [hK]
      exact ⟨⟨⟨mul_nonneg ha.1 hxI.1,
        lt_of_le_of_lt (mul_le_of_le_one_left hxI.1 ha.2) hxI.2⟩, hρU hxρ⟩, ha⟩
    have hcomp := hM.comp hφ.contDiffOn hmap
    have hcont : ContinuousOn (fun a : ℝ => F x a) (Set.uIcc (0:ℝ) 1) :=
      hcomp.continuousOn.congr (fun a _ => by simp only [hF, Function.comp_apply])
    exact hcont.intervalIntegrable
  have hlip : ∀ a ∈ Set.Icc (0:ℝ) 1, ∀ x ∈ B, ‖F x a - F p₀ a‖ ≤ C₀ * ‖x - p₀‖ := by
    intro a ha x hxB
    have hderiv : ∀ x' ∈ B, HasFDerivWithinAt (fun x' : ℝ × E => F x' a)
        (rayDeriv K M ((a * x'.1, x'.2), a)) B x' := by
      intro x' hx'B
      have h := hchain x' a hx'B ha
      simpa only [hF, rayL_apply] using h
    have hmvt := hBconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv
      (fun x' hx'B => hray_bound x' a hx'B ha) hp₀B hxB
    simpa only [hF] using hmvt
  have hcont_F' : ContinuousOn F' (Set.uIcc (0:ℝ) 1) := by
    have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => ((a * p₀.1, p₀.2), a)) :=
      ((contDiff_id.mul contDiff_const).prodMk contDiff_const).prodMk contDiff_id
    have hmap : MapsTo (fun a : ℝ => ((a * p₀.1, p₀.2), a)) (Set.uIcc (0:ℝ) 1) K := by
      intro a ha
      rw [Set.uIcc_of_le zero_le_one] at ha
      rw [hK]
      exact ⟨⟨⟨mul_nonneg ha.1 ht₀.1,
        lt_of_le_of_lt (mul_le_of_le_one_left ht₀.1 ha.2) ht₀.2⟩, hy₀⟩, ha⟩
    have hRD : ContDiffOn ℝ (⊤ : ℕ∞) (rayDeriv K M) K := contDiffOn_rayDeriv hM hK_unique
    exact ((hRD.comp hφ.contDiffOn hmap).continuousOn).congr
      (fun a _ => by simp only [hF', Function.comp_apply])
  have hF'_int : IntervalIntegrable F' MeasureTheory.volume (0 : ℝ) 1 := hcont_F'.intervalIntegrable
  have hF'_meas : MeasureTheory.AEStronglyMeasurable F'
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (0 : ℝ) 1)) := by
    have h := hF'_int.aestronglyMeasurable
    rw [Set.uIoc_of_le zero_le_one]
    exact h
  have huIcc : ∀ a : ℝ, a ∈ Set.uIoc (0:ℝ) 1 → a ∈ Set.Icc (0:ℝ) 1 := by
    intro a ha
    rw [Set.uIoc_of_le zero_le_one] at ha
    exact ⟨le_of_lt ha.1, ha.2⟩
  have hae : ∀ (P : ℝ → Prop), (∀ a ∈ Set.uIoc (0:ℝ) 1, P a) →
      Filter.Eventually P (MeasureTheory.ae
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (0 : ℝ) 1))) := by
    intro P hP
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    exact Filter.Eventually.of_forall fun a ha => hP a ha
  have h_lip : Filter.Eventually
      (fun a : ℝ => ∀ x ∈ B, ‖F x a - F p₀ a‖ ≤ (fun _ : ℝ => C₀) a * ‖x - p₀‖)
      (MeasureTheory.ae ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
        (Set.uIoc (0 : ℝ) 1))) :=
    hae _ (fun a ha => hlip a (huIcc a ha))
  have h_diff : Filter.Eventually
      (fun a : ℝ => HasFDerivWithinAt (fun x => F x a) (F' a) B p₀)
      (MeasureTheory.ae ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
        (Set.uIoc (0 : ℝ) 1))) := by
    refine hae _ (fun a ha => ?_)
    have h := hchain p₀ a hp₀B (huIcc a ha)
    simpa only [hF, hF', rayL_apply] using h
  have hbound_int : IntervalIntegrable (fun _ : ℝ => C₀) MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_const
  have hmain := hasFDerivWithinAt_intervalIntegral_of_lipschitz (B := B) (x₀ := p₀)
    (F := F) (F' := F') (bound := fun _ : ℝ => C₀) hF_int hF'_int hF'_meas h_lip hbound_int h_diff
  have hfilter : 𝓝[B] p₀ = 𝓝[Set.Ico 0 T ×ˢ U] p₀ := by
    have h := nhdsWithin_inter_of_mem' hB_nhds
    rwa [Set.inter_eq_right.mpr hB_sub] at h
  have hgoal : HasFDerivWithinAt
      (fun x => intervalIntegral (fun a => F x a) (0 : ℝ) 1 MeasureTheory.volume)
      (intervalIntegral F' (0 : ℝ) 1 MeasureTheory.volume) (Set.Ico 0 T ×ˢ U) p₀ := by
    simpa only [HasFDerivWithinAt, hfilter] using hmain
  have h1 : (fun x : ℝ × E => intervalIntegral (fun a => F x a) (0 : ℝ) 1 MeasureTheory.volume)
      = rayInt M := by
    funext x
    simp only [rayInt, intervalIntegral, hF]
  have h2 : intervalIntegral F' (0 : ℝ) 1 MeasureTheory.volume
      = rayInt (rayDeriv ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1) M) p₀ := by
    rw [hF']
    simp only [rayInt, intervalIntegral, hK]
  rw [h1, h2] at hgoal
  exact hgoal

/-- **Smoothness of the ray integral**, stable form: the target lives in the universe of the
domain, which makes the induction step applicable to itself. -/
theorem contDiffOn_rayInt_nat_stable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {U : Set E} (hT : 0 < T) (hU : IsOpen U) :
    ∀ (n : ℕ) (W : Type (max u v)) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (M : (ℝ × E) × ℝ → W),
      ContDiffOn ℝ (⊤ : ℕ∞) M ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1) →
      ContDiffOn ℝ (n : ℕ∞) (rayInt M) (Set.Ico 0 T ×ˢ U) := by
  intro n
  induction n with
  | zero =>
    intro W _ _ _ M hM
    exact (contDiffOn_zero (𝕜 := ℝ)).2 fun p hp =>
      (hasFDerivWithinAt_rayInt hT hU hM p hp).continuousWithinAt
  | succ n ih =>
    intro W _ _ _ M hM
    have hK_unique : UniqueDiffOn ℝ ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1) :=
      (uniqueDiffOn_slab (T := T) hU).prod (uniqueDiffOn_Icc zero_lt_one)
    have hMderiv : ContDiffOn ℝ (⊤ : ℕ∞)
        (rayDeriv ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1) M)
        ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1) := contDiffOn_rayDeriv hM hK_unique
    have ih' := ih ((ℝ × E) →L[ℝ] W)
      (rayDeriv ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1) M) hMderiv
    rw [show ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 from by push_cast; ring]
    intro p hp
    refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := (n : ℕ∞)) (by simp)).2
      ⟨Set.Ico 0 T ×ˢ U, ?_, subset_insert _ _, fun h => absurd h (by simp),
        fun x => rayInt (rayDeriv ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1) M) x, ?_, ?_⟩
    · rw [insert_eq_of_mem hp]; exact self_mem_nhdsWithin
    · intro x hx
      exact hasFDerivWithinAt_rayInt hT hU hM x hx
    · exact ih'.contDiffWithinAt hp

/-- **Smoothness of the ray integral** in every finite order, for a target space in an arbitrary
universe.  The induction step applies the stable form to the derivative family, whose target
`(ℝ × E) →L[ℝ] W` lies in the universe `max u v`. -/
theorem contDiffOn_rayInt_nat {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {U : Set E} (hT : 0 < T) (hU : IsOpen U) :
    ∀ (n : ℕ) (W : Type v) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (M : (ℝ × E) × ℝ → W),
      ContDiffOn ℝ (⊤ : ℕ∞) M ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1) →
      ContDiffOn ℝ (n : ℕ∞) (rayInt M) (Set.Ico 0 T ×ˢ U) := by
  intro n
  induction n with
  | zero =>
    intro W _ _ _ M hM
    exact (contDiffOn_zero (𝕜 := ℝ)).2 fun p hp =>
      (hasFDerivWithinAt_rayInt hT hU hM p hp).continuousWithinAt
  | succ n _ih =>
    intro W _ _ _ M hM
    have hK_unique : UniqueDiffOn ℝ ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1) :=
      (uniqueDiffOn_slab (T := T) hU).prod (uniqueDiffOn_Icc zero_lt_one)
    have hMderiv : ContDiffOn ℝ (⊤ : ℕ∞)
        (rayDeriv ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1) M)
        ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1) := contDiffOn_rayDeriv hM hK_unique
    have ih' := contDiffOn_rayInt_nat_stable (E := E) hT hU n ((ℝ × E) →L[ℝ] W)
      (rayDeriv ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1) M) hMderiv
    rw [show ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 from by push_cast; ring]
    intro p hp
    refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := (n : ℕ∞)) (by simp)).2
      ⟨Set.Ico 0 T ×ˢ U, ?_, subset_insert _ _, fun h => absurd h (by simp),
        fun x => rayInt (rayDeriv ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1) M) x, ?_, ?_⟩
    · rw [insert_eq_of_mem hp]; exact self_mem_nhdsWithin
    · intro x hx
      exact hasFDerivWithinAt_rayInt hT hU hM x hx
    · exact ih'.contDiffWithinAt hp

/-- **Smoothness of the ray integral.** -/
theorem contDiffOn_rayInt {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {U : Set E} (hT : 0 < T) (hU : IsOpen U)
    {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {M : (ℝ × E) × ℝ → W}
    (hM : ContDiffOn ℝ (⊤ : ℕ∞) M ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (rayInt M) (Set.Ico 0 T ×ˢ U) := by
  rw [contDiffOn_infty]
  intro n
  exact contDiffOn_rayInt_nat hT hU n W M hM

/-- The time derivative of `G` along the slab, as a function on `slab × [0,1]`. -/
noncomputable def timeDerivFamily (T : ℝ) (U : Set E) (G : ℝ × E → Z) :
    (ℝ × E) × ℝ → Z :=
  fun qs => fderivWithin ℝ G (Set.Ico 0 T ×ˢ U) qs.1 (1, 0)

theorem contDiffOn_timeDerivFamily (hT : 0 < T) (hU : IsOpen U) {G : ℝ × E → Z}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G (Set.Ico 0 T ×ˢ U)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (timeDerivFamily T U G)
      ((Set.Ico 0 T ×ˢ U) ×ˢ Set.Icc (0 : ℝ) 1) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × E => fderivWithin ℝ G (Set.Ico 0 T ×ˢ U) q (1, 0))
      (Set.Ico 0 T ×ˢ U) :=
    fun q hq => (hG.contDiffWithinAt hq).fderivWithin_right_apply contDiffWithinAt_const
      (uniqueDiffOn_slab (T := T) hU) (by simp) hq
  exact h1.comp contDiffOn_fst (fun qs hqs => hqs.1)

theorem factor_smul_of_vanishing_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U) (G : ℝ × E → Z)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G ((Set.Ico 0 T) ×ˢ U))
    (h0 : ∀ y ∈ U, G (0, y) = 0) :
    ∃ Ψ : ℝ × E → Z, ContDiffOn ℝ (⊤ : ℕ∞) Ψ ((Set.Ico 0 T) ×ˢ U) ∧
      ∀ p ∈ (Set.Ico 0 T) ×ˢ U, G p = p.1 • Ψ p := by
  have hρ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × E => fderivWithin ℝ G (Set.Ico 0 T ×ˢ U) q (1, 0))
      (Set.Ico 0 T ×ˢ U) :=
    fun q hq => (hG.contDiffWithinAt hq).fderivWithin_right_apply contDiffWithinAt_const
      (uniqueDiffOn_slab (T := T) hU) (by simp) hq
  refine ⟨rayInt (timeDerivFamily T U G),
    contDiffOn_rayInt hT hU (contDiffOn_timeDerivFamily hT hU hG), ?_⟩
  intro p hp
  obtain ⟨ht, hy⟩ := hp
  by_cases hp0 : p.1 = 0
  · have hp' : p = (0, p.2) := by rw [← hp0]
    rw [hp', zero_smul]
    exact h0 p.2 hy
  · have hpos : 0 < p.1 := lt_of_le_of_ne ht.1 (Ne.symm hp0)
    -- the fundamental theorem of calculus on the time interval `[0, p.1]`
    have hcont : ContinuousOn (fun u : ℝ => G (u, p.2)) (Set.Icc 0 p.1) :=
      hG.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun u hu => ⟨⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩, hy⟩)
    have hderiv : ∀ u ∈ Set.Ioo 0 p.1, HasDerivAt (fun u : ℝ => G (u, p.2))
        (fderivWithin ℝ G (Set.Ico 0 T ×ˢ U) (u, p.2) (1, 0)) u := by
      intro u hu
      have hq : (u, p.2) ∈ Set.Ico 0 T ×ˢ U :=
        ⟨⟨le_of_lt hu.1, lt_trans hu.2 ht.2⟩, hy⟩
      have hnbhd : Set.Ico 0 T ×ˢ U ∈ 𝓝 (u, p.2) := by
        have hV : Set.Ioo 0 T ×ˢ U ∈ 𝓝 (u, p.2) :=
          (isOpen_Ioo.prod hU).mem_nhds ⟨⟨hu.1, lt_trans hu.2 ht.2⟩, hy⟩
        exact mem_of_superset hV fun x hx => ⟨⟨le_of_lt hx.1.1, hx.1.2⟩, hx.2⟩
      have hAt : ContDiffAt ℝ (⊤ : ℕ∞) G (u, p.2) :=
        (hG.contDiffWithinAt hq).contDiffAt hnbhd
      have hfderiv : HasFDerivAt G (fderiv ℝ G (u, p.2)) (u, p.2) :=
        (hAt.differentiableAt (by simp)).hasFDerivAt
      have hcurve : HasDerivAt (fun u : ℝ => (u, p.2)) (1, 0) u := by
        simpa using (hasDerivAt_id u).prodMk (hasDerivAt_const u p.2)
      have hcomp := hfderiv.comp_hasDerivAt u hcurve
      have hfw : fderivWithin ℝ G (Set.Ico 0 T ×ˢ U) (u, p.2) = fderiv ℝ G (u, p.2) :=
        fderivWithin_of_mem_nhds hnbhd
      simp only [hfw]
      exact hcomp
    have hint : IntervalIntegrable
        (fun u : ℝ => fderivWithin ℝ G (Set.Ico 0 T ×ˢ U) (u, p.2) (1, 0))
        MeasureTheory.volume 0 p.1 := by
      refine ContinuousOn.intervalIntegrable ?_
      refine hρ.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn ?_
      intro u hu
      rw [Set.uIcc_of_le (le_of_lt hpos)] at hu
      exact ⟨⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩, hy⟩
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hpos) hcont hderiv hint
    -- the substitution `u = p.1 * s`
    have hsub : p.1 • rayInt (timeDerivFamily T U G) p
        = ∫ u in (0 : ℝ)..p.1,
            fderivWithin ℝ G (Set.Ico 0 T ×ˢ U) (u, p.2) (1, 0) := by
      have h := intervalIntegral.smul_integral_comp_mul_right
        (f := fun u : ℝ => fderivWithin ℝ G (Set.Ico 0 T ×ˢ U) (u, p.2) (1, 0)) p.1
        (a := (0 : ℝ)) (b := (1 : ℝ))
      simpa only [rayInt, timeDerivFamily, zero_mul, one_mul] using h
    rw [hsub, hFTC]
    simp only [h0 p.2 hy, sub_zero]

end Work.Diff.EXT
