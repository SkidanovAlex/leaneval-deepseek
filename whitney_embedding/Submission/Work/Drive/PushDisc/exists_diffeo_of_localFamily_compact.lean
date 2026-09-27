import Mathlib
import Submission.Work.Drive.PushDisc.localIsotopyGlobalisation
import Submission.Work.Whitney.CutPush.flow_of_compactSupport
import Submission.Work.ODE.GlobalFlow

/-!
# Globalising a local family along a *compact set* (value form)

`Work.Drive.PushDisc.exists_diffeo_of_localFamily_compact` is the compact-set version of
`Work.Drive.PushDisc.exists_diffeo_of_localInverseData` /
`Work.PushDisc.exists_diffeo_of_localInverseData_value`: instead of a single arc `γ : ℝ → ℝ^m`
(`t ∈ [0,1]`) one is given a *compact set* `K`, the trail is the image of `Icc 0 1 ×ˢ K` under
`(lam, x) ↦ (lam, F lam x)`, and the conclusion is the value clause `A (F 0 x) = F 1 x` for
`x ∈ K`.

The proof is the classical one, verbatim: the material velocity field
`X lam z = ∑_j ψ_j lam z • vel lam (par_j lam z)` patched from the local inverses, cut off in the
parameter (`arcBump`) and in space (`χ`, supported in the prescribed open set `U`), and flowed; the
flow's time-one slice is the required diffeomorphism, it is the identity off `U` because the field
vanishes there, and it maps `F 0 x` to `F 1 x` because the curve `u ↦ (u, F u x)` is an integral
curve of the (uniquely determined) flow of the product field `(1, V)`.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set Topology Filter MeasureTheory

theorem exists_diffeo_of_localFamily_compact {m : ℕ}
    (F : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K)
    (U : Set (EuclideanSpace ℝ (Fin m))) (hU : IsOpen U)
    (hFsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin m) => F p.1 p.2))
    (htrail : ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ K, F lam y ∈ U)
    (Ω : Set (EuclideanSpace ℝ (Fin m))) (hΩopen : IsOpen Ω) (hΩK : K ⊆ Ω)
    (hΩinj : ∀ lam ∈ Set.Icc (0:ℝ) 1, Set.InjOn (F lam) Ω)
    {ι : Type} [Fintype ι]
    (Olam : ι → Set ℝ) (Osrc : ι → Set (EuclideanSpace ℝ (Fin m)))
    (Otgt : ι → Set (EuclideanSpace ℝ (Fin m)))
    (par : ι → ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hOopen : ∀ j, IsOpen (Olam j)) (hSopen : ∀ j, IsOpen (Osrc j)) (hTopen : ∀ j, IsOpen (Otgt j))
    (hSΩ : ∀ j, Osrc j ⊆ Ω)
    (hparsm : ∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (par j)) (Olam j ×ˢ Otgt j))
    (hparR : ∀ j, ∀ lam ∈ Olam j, ∀ z ∈ Otgt j, par j lam z ∈ Osrc j ∧ F lam (par j lam z) = z)
    (hcover : ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ K, ∃ j, lam ∈ Olam j ∧ F lam y ∈ Otgt j) :
    ∃ (A Ainv : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
      Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
      (∀ y, y ∉ U → A y = y) ∧
      (∀ x ∈ K, A (F 0 x) = F 1 x) := by
  classical
  -- ## the trail of the compact set and its image
  let T : Set (ℝ × EuclideanSpace ℝ (Fin m)) :=
    {q | ∃ lam ∈ Set.Icc (0 : ℝ) 1, ∃ x ∈ K, q = (lam, F lam x)}
  have hTcomp : IsCompact T := by
    have hcont : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin m) => (p.1, F p.1 p.2)) :=
      continuous_fst.prodMk hFsm.continuous
    have himg : T = (fun p : ℝ × EuclideanSpace ℝ (Fin m) => (p.1, F p.1 p.2)) ''
        (Set.Icc (0 : ℝ) 1 ×ˢ K) := by
      ext q
      constructor
      · rintro ⟨lam, hlam, x, hx, rfl⟩
        exact ⟨(lam, x), ⟨hlam, hx⟩, rfl⟩
      · rintro ⟨⟨lam, x⟩, ⟨hlam, hx⟩, rfl⟩
        exact ⟨lam, hlam, x, hx, rfl⟩
    rw [himg]
    exact (isCompact_Icc.prod hK).image hcont
  let Timg : Set (EuclideanSpace ℝ (Fin m)) :=
    {z | ∃ lam ∈ Set.Icc (0 : ℝ) 1, ∃ x ∈ K, z = F lam x}
  have hTimgcomp : IsCompact Timg := by
    have hcont : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin m) => F p.1 p.2) :=
      hFsm.continuous
    have himg : Timg = (fun p : ℝ × EuclideanSpace ℝ (Fin m) => F p.1 p.2) ''
        (Set.Icc (0 : ℝ) 1 ×ˢ K) := by
      ext z
      constructor
      · rintro ⟨lam, hlam, x, hx, rfl⟩
        exact ⟨(lam, x), ⟨hlam, hx⟩, rfl⟩
      · rintro ⟨⟨lam, x⟩, ⟨hlam, hx⟩, rfl⟩
        exact ⟨lam, hlam, x, hx, rfl⟩
    rw [himg]
    exact (isCompact_Icc.prod hK).image hcont
  have hTimgU : Timg ⊆ U := by
    rintro z ⟨lam, hlam, x, hx, rfl⟩
    exact htrail lam hlam x hx
  -- ## the partition of unity and the bumps
  have hTcov : T ⊆ ⋃ j, Olam j ×ˢ Otgt j := by
    rintro q ⟨lam, hlam, x, hx, rfl⟩
    obtain ⟨j, hj1, hj2⟩ := hcover lam hlam x hx
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_prod.mpr ⟨hj1, hj2⟩⟩
  obtain ⟨ψ, δ, hδpos, hψsm, hψnn, hψtsupp, hψsum⟩ :=
    exists_partitionOfUnity_compact T hTcomp Olam hOopen Otgt hTopen hTcov
  obtain ⟨χ, hχsm, hχnn, ⟨δχ, hδχpos, hχone⟩, hχsupp, hχcs⟩ :=
    exists_contDiff_bump_compact Timg hTimgcomp U hU hTimgU
  -- ## the material velocity field
  let vel : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun lam y => fderiv ℝ (fun p : ℝ × EuclideanSpace ℝ (Fin m) => F p.1 p.2) (lam, y) (1, 0)
  have hvelsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin m) => vel p.1 p.2) := by
    have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
          fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin m) => F q.1 q.2) p) := by
      have h := (contDiffOn_infty_iff_fderiv_of_isOpen (𝕜 := ℝ)
        (f := fun q : ℝ × EuclideanSpace ℝ (Fin m) => F q.1 q.2) (s := Set.univ) isOpen_univ).mp
        (hFsm.contDiffOn (s := Set.univ))
      exact contDiffOn_univ.mp h.2
    exact hfd.clm_apply (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : ℝ × EuclideanSpace ℝ (Fin m) => ((1:ℝ), (0 : EuclideanSpace ℝ (Fin m)))))
  let X : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun lam z => ∑ j, ψ j lam z • vel lam (par j lam z)
  have hXsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin m) => X p.1 p.2) := by
    have hfun : (fun p : ℝ × EuclideanSpace ℝ (Fin m) => X p.1 p.2)
        = fun p : ℝ × EuclideanSpace ℝ (Fin m) => ∑ j, ψ j p.1 p.2 • vel p.1 (par j p.1 p.2) := rfl
    rw [hfun]
    refine ContDiff.sum (fun j _ => ?_)
    refine Work.Whitney.CutPush.contDiff_smul_of_tsupport
      (f := fun p : ℝ × EuclideanSpace ℝ (Fin m) => ψ j p.1 p.2)
      (U := Olam j ×ˢ Otgt j) (hψsm j) ?_ ((hOopen j).prod (hTopen j)) (hψtsupp j)
    have hpair : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin m) => (p.1, par j p.1 p.2)) (Olam j ×ˢ Otgt j) :=
      ContDiffOn.prodMk contDiffOn_fst (hparsm j)
    exact hvelsm.contDiffOn.comp hpair (fun p _ => Set.mem_univ _)
  -- ## the cutoffs: in time (`arcBump`) and in space (`χ`)
  have harcBump_cs : HasCompactSupport Work.Whitney.CutPush.arcBump := by
    have hsub : tsupport Work.Whitney.CutPush.arcBump ⊆ Set.Icc (-2 : ℝ) 3 := by
      refine closure_minimal (fun t ht => ?_) isClosed_Icc
      rw [Set.mem_Icc]
      constructor
      · by_contra h
        exact ht (Work.Whitney.CutPush.arcBump_eq_zero_of_le (le_of_lt (not_le.mp h)))
      · by_contra h
        exact ht (Work.Whitney.CutPush.arcBump_eq_zero_of_ge (le_of_lt (not_le.mp h)))
    exact IsCompact.of_isClosed_subset (s := Set.Icc (-2 : ℝ) 3) isCompact_Icc
      (isClosed_tsupport _) hsub
  let V : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun lam z => (Work.Whitney.CutPush.arcBump lam * χ z) • X lam z
  have hVsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin m) => Work.Whitney.CutPush.arcBump p.1 * χ p.2) :=
      (Work.Whitney.CutPush.arcBump_contDiff.comp contDiff_fst).mul (hχsm.comp contDiff_snd)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
          (Work.Whitney.CutPush.arcBump p.1 * χ p.2) • X p.1 p.2) := h1.smul hXsm
    simpa [V] using h2
  have hVcs : HasCompactSupport (fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2) := by
    have hsupp : Function.support (fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2) ⊆
        Function.support Work.Whitney.CutPush.arcBump ×ˢ Function.support χ := by
      intro p hp
      have h1 : Work.Whitney.CutPush.arcBump p.1 ≠ 0 := by
        intro h; exact hp (by simp [V, h])
      have h2 : χ p.2 ≠ 0 := by
        intro h; exact hp (by simp [V, h])
      exact ⟨h1, h2⟩
    refine IsCompact.of_isClosed_subset
      (s := tsupport Work.Whitney.CutPush.arcBump ×ˢ tsupport χ)
      (harcBump_cs.isCompact.prod hχcs.isCompact) (isClosed_tsupport _) ?_
    refine closure_minimal (fun x hx =>
      ⟨subset_tsupport _ (hsupp hx).1, subset_tsupport _ (hsupp hx).2⟩) ?_
    exact (isClosed_tsupport _).prod (isClosed_tsupport _)
  -- ## the material identity at the trail points
  have hmat : ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, V lam (F lam x) = vel lam x := by
    intro lam hlam x hx
    have hmemT : (lam, F lam x) ∈ Metric.thickening δ T :=
      Metric.self_subset_thickening hδpos T ⟨lam, hlam, x, hx, rfl⟩
    have hmemχ : F lam x ∈ Metric.thickening δχ Timg :=
      Metric.self_subset_thickening hδχpos Timg ⟨lam, hlam, x, hx, rfl⟩
    have hsum1 : ∑ j, ψ j lam (F lam x) = 1 := hψsum (lam, F lam x) hmemT
    have hXval : X lam (F lam x) = vel lam x := by
      have hterm : ∀ j, ψ j lam (F lam x) • vel lam (par j lam (F lam x))
          = ψ j lam (F lam x) • vel lam x := by
        intro j
        by_cases h : ψ j lam (F lam x) = 0
        · rw [h, zero_smul, zero_smul]
        · have hmemψ : (lam, F lam x) ∈
              tsupport (fun p : ℝ × EuclideanSpace ℝ (Fin m) => ψ j p.1 p.2) :=
            subset_tsupport _ (by simpa using h)
          obtain ⟨hlO, hlT⟩ := Set.mem_prod.mp (hψtsupp j hmemψ)
          obtain ⟨hsrc, heq⟩ := hparR j lam hlO (F lam x) hlT
          have : par j lam (F lam x) = x :=
            hΩinj lam hlam (hSΩ j hsrc) (hΩK hx) heq
          rw [this]
      calc X lam (F lam x) = ∑ j, ψ j lam (F lam x) • vel lam (par j lam (F lam x)) := rfl
        _ = ∑ j, ψ j lam (F lam x) • vel lam x := Finset.sum_congr rfl (fun j _ => hterm j)
        _ = (∑ j, ψ j lam (F lam x)) • vel lam x := (Finset.sum_smul).symm
        _ = vel lam x := by rw [hsum1, one_smul]
    have hχ1 : χ (F lam x) = 1 := hχone _ hmemχ
    have ha1 : Work.Whitney.CutPush.arcBump lam = 1 :=
      Work.Whitney.CutPush.arcBump_eq_one ⟨by linarith [hlam.1], by linarith [hlam.2]⟩
    simp only [V, hχ1, ha1, mul_one, one_smul]
    exact hXval
  -- ## the product field and its flow
  let Xhat : ℝ × EuclideanSpace ℝ (Fin m) → ℝ × EuclideanSpace ℝ (Fin m) :=
    fun p => ((1:ℝ), V p.1 p.2)
  have hXhat_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Xhat := by
    have h := (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : ℝ × EuclideanSpace ℝ (Fin m) => (1:ℝ))).prodMk hVsm
    simpa [Xhat] using h
  have hVd_cs : HasCompactSupport (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
      fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin m) => V q.1 q.2) p) := hVcs.fderiv (𝕜 := ℝ)
  obtain ⟨Lv, hLv⟩ := Work.ODE.exists_nnnorm_le_of_hasCompactSupport
    (hVsm.continuous_fderiv (by norm_num)) hVd_cs
  have hV_lip : LipschitzWith Lv (fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2) :=
    lipschitzWith_of_nnnorm_fderiv_le (hVsm.differentiable (by norm_num)) hLv
  obtain ⟨Mv, _hMv0, hMv⟩ := Work.ODE.exists_norm_le_of_hasCompactSupport
    (f := fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2) hVsm.continuous hVcs
  have hXhat_lip : LipschitzWith (max 0 Lv) Xhat := by
    refine LipschitzWith.of_dist_le_mul (fun p q => ?_)
    have h1 : dist (Xhat p).1 (Xhat q).1 = 0 := by simp [Xhat]
    have h2 : dist (Xhat p).2 (Xhat q).2 ≤ (Lv : ℝ) * dist p q := by
      simpa [Xhat] using hV_lip.dist_le_mul p q
    have h2' : dist (Xhat p).2 (Xhat q).2 ≤ (Lv : ℝ) * max (dist p.1 q.1) (dist p.2 q.2) := by
      rw [show max (dist p.1 q.1) (dist p.2 q.2) = dist p q from Prod.dist_eq.symm]
      exact h2
    rw [Prod.dist_eq, Prod.dist_eq, h1, max_eq_right (by positivity)]
    exact le_trans h2' (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_right (0 : NNReal) Lv) (by positivity))
  have hXhat_bd : ∀ z, ‖Xhat z‖ ≤ max 1 Mv := by
    intro z
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · simpa [Xhat] using le_max_left (1 : ℝ) Mv
    · simpa [Xhat] using le_trans (hMv z) (le_max_right (1 : ℝ) Mv)
  have hXhat_db : ∀ z, ‖fderiv ℝ Xhat z‖ ≤ ((max 0 Lv : NNReal) : ℝ) :=
    fun z => norm_fderiv_le_of_lipschitz ℝ hXhat_lip
  obtain ⟨FL, δf, hδfpos, hFL0, hFLsem, hFLint, hFLsmooth⟩ :=
    Work.Whitney.CutPush.exists_flow_of_lipschitz Xhat hXhat_sm hXhat_lip hXhat_bd hXhat_db
  have hFLfst : ∀ s p, (FL s p).1 = p.1 + s := by
    intro s p
    have hY : LipschitzWith 0 (fun _ : ℝ => (1:ℝ)) := LipschitzWith.const 1
    have hcurve1 : IsIntegralCurve (fun u : ℝ => (FL u p).1) (fun _ z => (1:ℝ)) := by
      intro u
      have h2 := ((hFLint p u).hasFDerivAt.fst).hasDerivAt
      simpa [Xhat] using h2
    have hcurve2 : IsIntegralCurve (fun u : ℝ => p.1 + u) (fun _ z => (1:ℝ)) := by
      intro u
      simpa using (hasDerivAt_id u).const_add p.1
    have heq := Work.ODE.eq_of_isIntegralCurve (X := fun _ : ℝ => (1:ℝ)) (L := 0) hY
      hcurve1 hcurve2 (t := 0) (by simp [hFL0])
    have := congrFun heq s
    simpa using this
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδfpos
  have hstep : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL ((1:ℝ) / ((n:ℝ) + 1))) :=
    hFLsmooth _ (by rw [abs_of_pos (by positivity)]; exact le_of_lt hn)
  have hstepneg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL (-((1:ℝ) / ((n:ℝ) + 1)))) :=
    hFLsmooth _ (by rw [abs_neg, abs_of_pos (by positivity)]; exact le_of_lt hn)
  have hiter : ∀ (k : ℕ) (r : ℝ) p, FL ((k:ℝ) * r) p = (FL r)^[k] p := by
    intro k
    induction k with
    | zero => intro r p; simp [hFL0]
    | succ k ih =>
      intro r p
      have h1 : ((k:ℝ) + 1) * r = r + (k:ℝ) * r := by ring
      rw [Nat.cast_succ, h1, hFLsem, ih, Function.iterate_succ_apply']
  have hFL1_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL 1) := by
    have hpow : (FL 1) = (FL ((1:ℝ)/((n:ℝ)+1)))^[n+1] := by
      funext p
      have h1 : ((n:ℝ) + 1) * ((1:ℝ)/((n:ℝ)+1)) = 1 := by field_simp
      have h2 : ((n:ℝ) + 1) = (((n+1 : ℕ)) : ℝ) := by push_cast; ring
      calc FL 1 p = FL ((((n+1 : ℕ)) : ℝ) * ((1:ℝ)/((n:ℝ)+1))) p := by rw [← h2, h1]
        _ = (FL ((1:ℝ)/((n:ℝ)+1)))^[n+1] p := hiter (n+1) _ p
    rw [hpow]
    exact Work.Whitney.contDiff_iterate (n+1) hstep
  have hFLneg1_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL (-1)) := by
    have hpow : (FL (-1)) = (FL (-((1:ℝ)/((n:ℝ)+1))))^[n+1] := by
      funext p
      have h1 : ((n:ℝ) + 1) * (-((1:ℝ)/((n:ℝ)+1))) = -1 := by field_simp
      have h2 : ((n:ℝ) + 1) = (((n+1 : ℕ)) : ℝ) := by push_cast; ring
      calc FL (-1) p = FL ((((n+1 : ℕ)) : ℝ) * (-((1:ℝ)/((n:ℝ)+1)))) p := by rw [← h2, h1]
        _ = (FL (-((1:ℝ)/((n:ℝ)+1))))^[n+1] p := hiter (n+1) _ p
    rw [hpow]
    exact Work.Whitney.contDiff_iterate (n+1) hstepneg
  let A : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) := fun y => (FL 1 ((0:ℝ), y)).2
  let Ainv : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun y => (FL (-1) ((1:ℝ), y)).2
  have hA_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (FL 1 ((0:ℝ), y)).2)
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin m) => FL 1 ((0:ℝ), y)) :=
      hFL1_sm.comp (contDiff_const.prodMk contDiff_id)
    exact h1.snd
  have hAinv_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (FL (-1) ((1:ℝ), y)).2)
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin m) => FL (-1) ((1:ℝ), y)) :=
      hFLneg1_sm.comp (contDiff_const.prodMk contDiff_id)
    exact h1.snd
  have hleft : Function.LeftInverse Ainv A := by
    intro y
    show (FL (-1) ((1:ℝ), (FL 1 ((0:ℝ), y)).2)).2 = y
    have h1 : FL 1 ((0:ℝ), y) = (1, (FL 1 ((0:ℝ), y)).2) := by
      refine Prod.ext ?_ rfl
      rw [hFLfst]; norm_num
    rw [← h1]
    have h2 := hFLsem (-1) 1 ((0:ℝ), y)
    rw [show (-1:ℝ) + 1 = 0 by norm_num, hFL0] at h2
    exact (congrArg Prod.snd h2).symm
  have hright : Function.RightInverse Ainv A := by
    intro y
    show (FL 1 ((0:ℝ), (FL (-1) ((1:ℝ), y)).2)).2 = y
    have h1 : FL (-1) ((1:ℝ), y) = (0, (FL (-1) ((1:ℝ), y)).2) := by
      refine Prod.ext ?_ rfl
      rw [hFLfst]; norm_num
    rw [← h1]
    have h2 := hFLsem 1 (-1) ((1:ℝ), y)
    rw [show (1:ℝ) + -1 = 0 by norm_num, hFL0] at h2
    exact (congrArg Prod.snd h2).symm
  -- ## the diffeomorphism is the identity off `U`
  have hVzero : ∀ z, z ∉ U → ∀ lam, V lam z = 0 := by
    intro z hzU lam
    have hχz : χ z = 0 := by
      by_contra hne
      exact hzU (hχsupp (subset_tsupport _ hne))
    simp [V, hχz]
  have hAoff : ∀ y, y ∉ U → A y = y := by
    intro y hy
    have hcurve : IsIntegralCurve (fun s : ℝ => (s, y)) (fun _ z => Xhat z) := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ => (s, y)) (1, (0 : EuclideanSpace ℝ (Fin m))) s :=
        (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
      have h1' : HasDerivAt (fun s : ℝ => (s, y)) (Xhat (s, y)) s := by
        simpa [Xhat, hVzero y hy s] using h1
      exact h1'
    have hflow : IsIntegralCurve (fun s : ℝ => FL s ((0:ℝ), y)) (fun _ z => Xhat z) :=
      hFLint ((0:ℝ), y)
    have hagree : (fun s : ℝ => (s, y)) 0 = (fun s : ℝ => FL s ((0:ℝ), y)) 0 := by simp [hFL0]
    have heq := Work.ODE.eq_of_isIntegralCurve hXhat_lip hcurve hflow hagree
    have hval := congrFun heq 1
    show (FL (1:ℝ) ((0:ℝ), y)).2 = y
    have := congrArg Prod.snd hval
    simpa using this.symm
  -- ## the value clause on the compact set
  have hval : ∀ x ∈ K, A (F 0 x) = F 1 x := by
    intro x hx
    have hcurve : ∀ u ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun u : ℝ => (u, F u x)) (Xhat ((u, F u x))) u := by
      intro u hu
      have h1 : HasDerivAt (fun u : ℝ => F u x) (vel u x) u :=
        hasDerivAt_section (fun p : ℝ × EuclideanSpace ℝ (Fin m) => F p.1 p.2) x
          (hFsm.differentiable (by simp) (u, x))
      have h2 : HasDerivAt (fun u : ℝ => (u, F u x)) ((1:ℝ), vel u x) u :=
        (hasDerivAt_id u).prodMk h1
      have h3 : ((1:ℝ), vel u x) = Xhat ((u, F u x)) := by
        have h4 := hmat u hu x hx
        simp only [Xhat]
        rw [h4]
      rw [← h3]
      exact h2
    have hf : ∀ u ∈ Set.Ico (0 : ℝ) 1,
        HasDerivWithinAt (fun u : ℝ => (u, F u x)) (Xhat ((u, F u x))) (Set.Ici u) u :=
      fun u hu => (hcurve u (Set.Ico_subset_Icc_self hu)).hasDerivWithinAt
    have hg : ∀ u ∈ Set.Ico (0 : ℝ) 1,
        HasDerivWithinAt (fun u : ℝ => FL u ((0:ℝ), F 0 x))
          (Xhat (FL u ((0:ℝ), F 0 x))) (Set.Ici u) u :=
      fun u _ => (hFLint ((0:ℝ), F 0 x) u).hasDerivWithinAt
    have hcont_f : ContinuousOn (fun u : ℝ => (u, F u x)) (Set.Icc (0 : ℝ) 1) := by
      refine Continuous.continuousOn ?_
      exact continuous_id.prodMk
        (hFsm.continuous.comp (continuous_id.prodMk continuous_const))
    have hcont_g : ContinuousOn (fun u : ℝ => FL u ((0:ℝ), F 0 x)) (Set.Icc (0 : ℝ) 1) := by
      refine Continuous.continuousOn ?_
      rw [continuous_iff_continuousAt]
      intro u
      exact (hFLint ((0:ℝ), F 0 x) u).differentiableAt.continuousAt
    have heq := ODE_solution_unique (v := fun _ z => Xhat z) (K := max 0 Lv)
      (f := fun u : ℝ => (u, F u x)) (g := fun u : ℝ => FL u ((0:ℝ), F 0 x))
      (a := 0) (b := 1) (fun _ => hXhat_lip) hcont_f hf hcont_g hg (by simp [hFL0])
    have h1 : ((1:ℝ), F 1 x) = FL 1 ((0:ℝ), F 0 x) :=
      heq (by norm_num : (1:ℝ) ∈ Set.Icc (0 : ℝ) 1)
    show (FL (1:ℝ) ((0:ℝ), F 0 x)).2 = F 1 x
    exact (congrArg Prod.snd h1).symm
  exact ⟨A, Ainv, hA_sm, hAinv_sm, hleft, hright, hAoff, hval⟩

end Work.Drive.PushDisc
