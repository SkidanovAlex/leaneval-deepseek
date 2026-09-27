import Mathlib
import Submission.Work.Drive.BoxParityDefs

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


namespace Work.Drive

open scoped ContDiff Topology
open Set Filter

noncomputable section

/-- The `i`-th coordinate functional on `Amb m`, as a continuous linear map. -/
def coordL {m : ℕ} (i : Fin (m + 1)) : Amb m →L[ℝ] ℝ :=
  PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + 1) => ℝ) i

@[simp] lemma coordL_apply {m : ℕ} (i : Fin (m + 1)) (x : Amb m) :
    coordL i x = x i := by
  rw [coordL, PiLp.proj_apply]

lemma coordL_contDiff {m : ℕ} (i : Fin (m + 1)) : ContDiff ℝ ∞ (coordL i) :=
  (coordL i).contDiff (n := ∞)

lemma coordL_hasFDerivAt {m : ℕ} (i : Fin (m + 1)) (x : Amb m) :
    HasFDerivAt (fun y : Amb m => y i) (coordL i) x :=
  PiLp.hasFDerivAt_apply (𝕜 := ℝ) (E := fun _ : Fin (m + 1) => ℝ) 2 x i

theorem exists_local_normalForm {m : ℕ} {F : Work.Drive.Amb m → Work.Drive.Tgt m}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) {p : Work.Drive.Amb m} (hp : F p = 0)
    (i : Fin (m + 1))
    (hsurj : Function.Surjective (fun v : {v : Work.Drive.Amb m // v i = 0} => fderiv ℝ F p v.1)) :
    ∃ (δ ρ : ℝ) (η : ℝ → Work.Drive.Amb m), 0 < δ ∧ 0 < ρ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ u, η u i = 0) ∧
      η (p i) = p - (p i) • EuclideanSpace.single i 1 ∧
      (∀ u, |u - p i| < δ → F (u • EuclideanSpace.single i 1 + η u) = 0 ∧
        Function.Surjective (fun v : {v : Work.Drive.Amb m // v i = 0} =>
          fderiv ℝ F (u • EuclideanSpace.single i 1 + η u) v.1)) ∧
      (∀ x, |x i - p i| < δ → ‖x - (x i) • EuclideanSpace.single i 1 - η (x i)‖ < ρ →
        (F x = 0 ↔ x = (x i) • EuclideanSpace.single i 1 + η (x i))) := by
  have hF' : ContDiff ℝ ∞ F := hF
  let T : Amb m →L[ℝ] Tgt m := fderiv ℝ F p
  let P : Amb m →L[ℝ] ℝ := coordL i
  let G : Amb m → ℝ × Tgt m := fun x => (coordL i x, F x)
  let G' : Amb m →L[ℝ] ℝ × Tgt m := P.prod T
  have hT : HasFDerivAt F T p :=
    ((hF'.differentiable (by decide)).differentiableAt).hasFDerivAt
  have hGcd : ContDiff ℝ ∞ G := by
    have h1 : ContDiff ℝ ∞ (fun x : Amb m => coordL i x) := (coordL i).contDiff (n := ∞)
    have h2 : ContDiff ℝ ∞ (fun x : Amb m => F x) := hF'
    have h := h1.prodMk h2
    simpa [G] using h
  have hGfd : HasFDerivAt G G' p := by
    have h1 : HasFDerivAt (fun x : Amb m => coordL i x) (coordL i) p := (coordL i).hasFDerivAt
    have h2 : HasFDerivAt (fun x : Amb m => F x) T p := hT
    have h := h1.prodMk h2
    simpa [G, G', P] using h
  have hGfderiv : ∀ y : Amb m, fderiv ℝ G y = (coordL i).prod (fderiv ℝ F y) := by
    intro y
    have h1 : HasFDerivAt (fun x : Amb m => coordL i x) (coordL i) y := (coordL i).hasFDerivAt
    have h2 : HasFDerivAt F (fderiv ℝ F y) y :=
      (hF'.contDiffAt.differentiableAt (by decide)).hasFDerivAt
    have h := (h1.prodMk h2).fderiv
    simpa [G, P] using h

  have hsurj' : Function.Surjective G' := by
    intro y
    obtain ⟨a, b⟩ := y
    obtain ⟨w, hw⟩ := hsurj (b - a • T (EuclideanSpace.single i (1:ℝ)))
    refine ⟨a • EuclideanSpace.single i (1:ℝ) + (w : Amb m), ?_⟩
    have hPe : P (EuclideanSpace.single i (1:ℝ)) = 1 := by simp [P]
    have hPw : P (w : Amb m) = 0 := by simpa only [P, coordL_apply] using w.2
    have hw' : T (w : Amb m) = b - a • T (EuclideanSpace.single i (1:ℝ)) := hw
    change (P.prod T) (a • EuclideanSpace.single i (1:ℝ) + (w : Amb m)) = (a, b)
    rw [ContinuousLinearMap.prod_apply]
    have h1 : P (a • EuclideanSpace.single i (1:ℝ) + (w : Amb m)) = a := by
      simp only [map_add, map_smul, hPe, hPw, smul_eq_mul, mul_one, add_zero]
    have h2 : T (a • EuclideanSpace.single i (1:ℝ) + (w : Amb m)) = b := by
      rw [map_add, map_smul, hw']
      abel
    rw [h1, h2]
  have hfin : Module.finrank ℝ (Amb m) ≤ Module.finrank ℝ (ℝ × Tgt m) := by
    rw [finrank_euclideanSpace_fin, Module.finrank_prod, finrank_euclideanSpace_fin,
      Module.finrank_self]
    omega
  have hbij : Function.Bijective (G' : Amb m →ₗ[ℝ] ℝ × Tgt m) :=
    OrzechProperty.bijective_of_surjective_of_finrank_le (G' : Amb m →ₗ[ℝ] ℝ × Tgt m) hsurj' hfin
  let A : Amb m ≃L[ℝ] ℝ × Tgt m :=
    (LinearEquiv.ofBijective (G' : Amb m →ₗ[ℝ] ℝ × Tgt m) hbij).toContinuousLinearEquiv
  have hA : (A : Amb m →L[ℝ] ℝ × Tgt m) = G' := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have hGfdA : HasFDerivAt G (A : Amb m →L[ℝ] ℝ × Tgt m) p := by
    rw [hA]; exact hGfd
  have hne : (∞ : ℕ∞ω) ≠ 0 := by decide
  let g : ℝ × Tgt m → Amb m := (hGcd.contDiffAt).localInverse hGfdA hne
  have hg_cont : ContDiffAt ℝ ∞ g (G p) := (hGcd.contDiffAt).to_localInverse hGfdA hne
  let hst : HasStrictFDerivAt G (A : Amb m →L[ℝ] ℝ × Tgt m) p :=
    (hGcd.contDiffAt).hasStrictFDerivAt' hGfdA hne
  let Φ : OpenPartialHomeomorph (Amb m) (ℝ × Tgt m) := hst.toOpenPartialHomeomorph G
  have hΦsymm : Φ.symm = g := rfl
  have hp_src : p ∈ Φ.source := hst.mem_toOpenPartialHomeomorph_source
  have hGp_tgt : G p ∈ Φ.target := hst.image_mem_toOpenPartialHomeomorph_target
  have hleft : ∀ x ∈ Φ.source, g (G x) = x := by
    intro x hx
    have h := Φ.left_inv hx
    rwa [hΦsymm] at h
  have hright : ∀ y ∈ Φ.target, G (g y) = y := by
    intro y hy
    have h := Φ.right_inv hy
    rwa [hΦsymm] at h
  have hGp : G p = (p i, 0) := by
    change (coordL i p, F p) = (p i, 0)
    rw [hp, coordL_apply]

  have hg1 : ContDiffAt ℝ (1 : ℕ) g (G p) := (contDiffAt_infty.mp hg_cont) 1
  have hg1_ev : ∀ᶠ y in 𝓝 (G p), ContDiffAt ℝ (1 : ℕ) g y :=
    hg1.eventually (by decide)
  have hInv_nhds : ∀ᶠ x in 𝓝 p, (fderiv ℝ G x).IsInvertible := by
    have hcont : ContinuousAt G p := (hGcd.contDiffAt).continuousAt
    have hpre : ∀ᶠ x in 𝓝 p, ContDiffAt ℝ (1 : ℕ) g (G x) :=
      hcont.tendsto.eventually hg1_ev
    filter_upwards [Φ.open_source.mem_nhds hp_src, hpre] with x hxsrc hx1'
    have hev : id =ᶠ[𝓝 x] (fun y => g (G y)) := by
      filter_upwards [Φ.open_source.mem_nhds hxsrc] with y hy
      exact (hleft y hy).symm
    have hGd : HasFDerivAt G (fderiv ℝ G x) x :=
      (hGcd.contDiffAt.differentiableAt (by decide)).hasFDerivAt
    have hgd : HasFDerivAt g (fderiv ℝ g (G x)) (G x) :=
      (hx1'.differentiableAt (by decide)).hasFDerivAt
    have heq1 : (fderiv ℝ g (G x)) ∘L (fderiv ℝ G x) = 1 := by
      have h := ((hgd.comp x hGd).congr_of_eventuallyEq hev).fderiv
      rw [fderiv_id] at h
      exact h.symm
    have hGxtgt : G x ∈ Φ.target := Φ.map_source hxsrc
    have hr : id =ᶠ[𝓝 (G x)] (fun y => G (g y)) := by
      filter_upwards [Φ.open_target.mem_nhds hGxtgt] with y hy
      exact (hright y hy).symm
    have hgx : g (G x) = x := hleft x hxsrc
    have heq2 : fderiv ℝ G x ∘L (fderiv ℝ g (G x)) = 1 := by
      have hGgd : HasFDerivAt G (fderiv ℝ G (g (G x))) (g (G x)) :=
        (hGcd.contDiffAt.differentiableAt (by decide)).hasFDerivAt
      have h := ((hGgd.comp (G x) hgd).congr_of_eventuallyEq hr).fderiv
      rw [fderiv_id, hgx] at h
      exact h.symm
    exact ContinuousLinearMap.IsInvertible.of_inverse heq2 heq1

  have hgGp : g (G p) = p := hleft p hp_src
  have htend_g : Tendsto g (𝓝 (G p)) (𝓝 p) := by
    simpa only [hgGp] using hg_cont.continuousAt.tendsto
  have hW : ∀ᶠ y in 𝓝 (G p), (fderiv ℝ G (g y)).IsInvertible := htend_g.eventually hInv_nhds
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.mem_nhds_iff.mp hW
  have hVopen : IsOpen (Φ.target ∩ Metric.ball (G p) ε₁) :=
    Φ.open_target.inter Metric.isOpen_ball
  have hGpV : G p ∈ Φ.target ∩ Metric.ball (G p) ε₁ :=
    ⟨hGp_tgt, Metric.mem_ball_self hε₁pos⟩
  have hVcd : ∀ a ∈ Φ.target ∩ Metric.ball (G p) ε₁, ContDiffAt ℝ ∞ g a := by
    intro a ha
    have hInva : (fderiv ℝ G (g a)).IsInvertible := hε₁ ha.2
    obtain ⟨e, he⟩ := hInva
    have hfd : HasFDerivAt G (e : Amb m →L[ℝ] ℝ × Tgt m) (g a) := by
      have h1 : HasFDerivAt G (fderiv ℝ G (g a)) (g a) :=
        (hGcd.contDiffAt.differentiableAt (by decide)).hasFDerivAt
      rwa [← he] at h1
    have h := Φ.contDiffAt_symm ha.1 hfd (hGcd.contDiffAt)
    rwa [hΦsymm] at h
  obtain ⟨r_sm, hr_sm_pos, hr_sm⟩ := Metric.isOpen_iff.mp hVopen (G p) hGpV

  obtain ⟨r_src, hr_src_pos, hr_src⟩ := Metric.isOpen_iff.mp Φ.open_source p hp_src
  obtain ⟨r_tgt, hr_tgt_pos, hr_tgt⟩ := Metric.isOpen_iff.mp Φ.open_target (G p) hGp_tgt
  have hd_eq : ∀ u : ℝ, dist (u, (0 : Tgt m)) (G p) = |u - p i| := by
    intro u
    rw [hGp, Prod.dist_eq, Real.dist_eq, dist_self, max_eq_left (abs_nonneg _)]
  have htgt_mem : ∀ u : ℝ, |u - p i| < r_tgt → (u, (0 : Tgt m)) ∈ Φ.target := by
    intro u hu
    exact hr_tgt (by rw [Metric.mem_ball, hd_eq]; exact hu)
  have hcu0 : ContinuousAt g ((p i), (0 : Tgt m)) := by simpa [hGp] using hg_cont.continuousAt
  have hcu : ContinuousAt (fun u : ℝ => g (u, (0 : Tgt m))) (p i) := by
    have hq : ContinuousAt (fun u : ℝ => (u, (0 : Tgt m))) (p i) := by fun_prop
    exact hcu0.comp (f := fun u : ℝ => (u, (0 : Tgt m))) hq
  have hcu_val : g ((p i), (0 : Tgt m)) = p := by simpa [hGp] using hgGp
  have htend_cu : Tendsto (fun u : ℝ => g (u, (0 : Tgt m))) (𝓝 (p i)) (𝓝 p) := by
    simpa only [hcu_val] using hcu.tendsto
  have hev_inv : ∀ᶠ u in 𝓝 (p i), (fderiv ℝ G (g (u, (0 : Tgt m)))).IsInvertible :=
    htend_cu.eventually hInv_nhds
  have hev_src : ∀ᶠ u in 𝓝 (p i), ‖g (u, (0 : Tgt m)) - p‖ < r_src / 2 := by
    have hb : Metric.ball p (r_src / 2) ∈ 𝓝 p := Metric.ball_mem_nhds p (by linarith)
    filter_upwards [htend_cu.eventually hb] with u hu
    simpa [dist_eq_norm] using hu
  have hev_tgt : ∀ᶠ u in 𝓝 (p i), (u, (0 : Tgt m)) ∈ Φ.target := by
    filter_upwards [Metric.ball_mem_nhds (p i) hr_tgt_pos] with u hu
    rw [Metric.mem_ball, Real.dist_eq] at hu
    exact htgt_mem u hu
  have hgood : ∀ᶠ u in 𝓝 (p i),
      (u, (0 : Tgt m)) ∈ Φ.target ∧ (fderiv ℝ G (g (u, (0 : Tgt m)))).IsInvertible ∧
        ‖g (u, (0 : Tgt m)) - p‖ < r_src / 2 :=
    (hev_tgt.and (hev_inv.and hev_src)).mono fun u h => ⟨h.1, h.2.1, h.2.2⟩
  obtain ⟨r_good, hr_good_pos, hr_good⟩ := Metric.mem_nhds_iff.mp hgood
  have hr_sm3_pos : 0 < r_sm / 3 := by linarith
  have hmin_pos : 0 < min r_good (r_sm / 3) := lt_min hr_good_pos hr_sm3_pos
  set δ : ℝ := min r_good (r_sm / 3) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδ_lt_good : δ < r_good := by
    have h1 : min r_good (r_sm / 3) ≤ r_good := min_le_left _ _
    rw [hδdef]; linarith
  have h3δ_lt_sm : 3 * δ < r_sm := by
    have h1 : min r_good (r_sm / 3) ≤ r_sm / 3 := min_le_right _ _
    have h2 : min r_good (r_sm / 3) ≤ r_good := min_le_left _ _
    rw [hδdef]; nlinarith [hr_good_pos, hr_sm_pos]
  set ρ : ℝ := r_src / 4 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  let b : ContDiffBump (p i : ℝ) := ⟨2 * δ, 3 * δ, by linarith, by linarith⟩
  have hbIn : b.rIn = 2 * δ := rfl
  have hbOut : b.rOut = 3 * δ := rfl
  let w₀ : Amb m := p - (p i) • EuclideanSpace.single i (1:ℝ)
  let hgt : ℝ → Amb m :=
    fun u => g (u, (0 : Tgt m)) - (g (u, (0 : Tgt m))) i • EuclideanSpace.single i (1:ℝ)
  let η : ℝ → Amb m := fun u => b u • hgt u + (1 - b u) • w₀
  have hηi : ∀ u : ℝ, η u i = 0 := by
    intro u
    have h1 : hgt u i = 0 := by simp [hgt]
    have h2 : w₀ i = 0 := by simp [w₀]
    simp [η, h1, h2]
  have hηpi : η (p i) = p - (p i) • EuclideanSpace.single i (1:ℝ) := by
    have hb1 : b (p i) = 1 := by
      apply b.one_of_mem_closedBall
      rw [Metric.mem_closedBall, hbIn, Real.dist_eq, sub_self, abs_zero]
      linarith
    have hthis : hgt (p i) = p - (p i) • EuclideanSpace.single i (1:ℝ) := by
      simp only [hgt, hcu_val]
    simp [η, hb1, hthis]
  have hkey : ∀ u : ℝ, |u - p i| < δ →
      u • EuclideanSpace.single i (1:ℝ) + η u = g (u, (0 : Tgt m)) := by
    intro u hu
    have hu_ball : u ∈ Metric.ball (p i) r_good := by
      rw [Metric.mem_ball, Real.dist_eq]; exact lt_trans hu hδ_lt_good
    obtain ⟨htgt, -, -⟩ := hr_good hu_ball
    have hcoord : (g (u, (0 : Tgt m))) i = u := by
      have hrightu : G (g (u, (0 : Tgt m))) = (u, 0) := hright (u, (0 : Tgt m)) htgt
      have := congrArg Prod.fst hrightu
      simpa [G, coordL_apply] using this
    have hbu : b u = 1 := by
      apply b.one_of_mem_closedBall
      rw [Metric.mem_closedBall, hbIn, Real.dist_eq]
      linarith
    have hηu : η u = g (u, (0 : Tgt m)) - u • EuclideanSpace.single i (1:ℝ) := by
      have hthis : hgt u = g (u, (0 : Tgt m))
          - (g (u, (0 : Tgt m))) i • EuclideanSpace.single i (1:ℝ) := rfl
      rw [show η u = b u • hgt u + (1 - b u) • w₀ from rfl, hbu, one_smul, sub_self, zero_smul,
        hthis, hcoord, add_zero]
    rw [hηu]
    abel
  have hLcd : ContDiff ℝ ∞ (ContinuousLinearMap.id ℝ (Amb m)
      - (coordL i).smulRight (EuclideanSpace.single i (1:ℝ))) :=
    (ContinuousLinearMap.id ℝ (Amb m)
      - (coordL i).smulRight (EuclideanSpace.single i (1:ℝ))).contDiff (n := ∞)
  have hgs_s : ContDiffOn ℝ ∞ (fun u : ℝ => g (u, (0 : Tgt m))) (Metric.ball (p i) r_sm) := by
    rw [Metric.isOpen_ball.contDiffOn_iff]
    intro u hu
    have huV : (u, (0 : Tgt m)) ∈ Φ.target ∩ Metric.ball (G p) ε₁ :=
      hr_sm (by rw [Metric.mem_ball, hd_eq]; rw [Metric.mem_ball, Real.dist_eq] at hu; exact hu)
    exact (hVcd (u, (0 : Tgt m)) huV).comp u (by fun_prop)
  have hgt_s : ContDiffOn ℝ ∞ hgt (Metric.ball (p i) r_sm) := by
    have h1 : ContDiffOn ℝ ∞
        (fun u : ℝ => (ContinuousLinearMap.id ℝ (Amb m)
          - (coordL i).smulRight (EuclideanSpace.single i (1:ℝ))) (g (u, (0 : Tgt m))))
        (Metric.ball (p i) r_sm) :=
      hLcd.comp_contDiffOn hgs_s
    refine h1.congr ?_
    intro u hu
    simp [hgt, ContinuousLinearMap.smulRight_apply, coordL_apply]
  have hη_s : ContDiffOn ℝ ∞ η (Metric.ball (p i) r_sm) := by
    have hb_s : ContDiffOn ℝ ∞ (fun u : ℝ => b u) (Metric.ball (p i) r_sm) :=
      b.contDiff.contDiffOn
    have h1 : ContDiffOn ℝ ∞ (fun u : ℝ => b u • hgt u) (Metric.ball (p i) r_sm) :=
      hb_s.smul hgt_s
    have h2 : ContDiffOn ℝ ∞ (fun u : ℝ => (1 - b u) • w₀) (Metric.ball (p i) r_sm) :=
      ((contDiffOn_const.sub hb_s).smul contDiffOn_const)
    exact h1.add h2
  have ht_open : IsOpen {u : ℝ | 3 * δ < dist u (p i)} :=
    isOpen_lt continuous_const (continuous_id.dist continuous_const)
  have hη_t : ContDiffOn ℝ ∞ η {u : ℝ | 3 * δ < dist u (p i)} := by
    have hw : ∀ u : ℝ, 3 * δ < dist u (p i) → η u = w₀ := by
      intro u hu
      have hb0 : b u = 0 := by
        apply b.zero_of_le_dist
        rw [hbOut]
        exact le_of_lt hu
      simp [η, hb0]
    refine ContDiffOn.congr (contDiffOn_const (c := w₀)) ?_
    intro u hu
    exact hw u hu
  have hcover : Metric.ball (p i) r_sm ∪ {u : ℝ | 3 * δ < dist u (p i)} = univ := by
    ext u
    constructor
    · intro _; trivial
    · intro _
      by_cases h : u ∈ Metric.ball (p i) r_sm
      · exact Or.inl h
      · right
        show 3 * δ < dist u (p i)
        rw [Metric.mem_ball, Real.dist_eq] at h
        have hle : r_sm ≤ |u - p i| := not_lt.mp h
        rw [Real.dist_eq]
        linarith [h3δ_lt_sm, hle]
  have hη_cd : ContDiff ℝ ∞ η :=
    contDiff_of_contDiffOn_union_of_isOpen hη_s hη_t hcover Metric.isOpen_ball ht_open
  refine ⟨δ, ρ, η, hδpos, hρpos, hη_cd, hηi, hηpi, ?_, ?_⟩
  · intro u hu
    refine ⟨?_, ?_⟩
    · rw [hkey u hu]
      have hu_ball : u ∈ Metric.ball (p i) r_good := by
        rw [Metric.mem_ball, Real.dist_eq]; exact lt_trans hu hδ_lt_good
      obtain ⟨htgt, -, -⟩ := hr_good hu_ball
      have hrightu : G (g (u, (0 : Tgt m))) = (u, 0) := hright (u, (0 : Tgt m)) htgt
      have := congrArg Prod.snd hrightu
      simpa [G] using this
    · intro b0
      have hu_ball : u ∈ Metric.ball (p i) r_good := by
        rw [Metric.mem_ball, Real.dist_eq]; exact lt_trans hu hδ_lt_good
      obtain ⟨htgt, hinv, -⟩ := hr_good hu_ball
      obtain ⟨e, he⟩ := hinv
      refine ⟨⟨e.symm (0, b0), ?_⟩, ?_⟩
      · have h1 : (e : Amb m →L[ℝ] ℝ × Tgt m) (e.symm (0, b0)) = (0, b0) :=
          e.apply_symm_apply (0, b0)
        rw [he, hGfderiv, ContinuousLinearMap.prod_apply] at h1
        have := congrArg Prod.fst h1
        simpa [coordL_apply] using this
      · rw [hkey u hu]
        have h1 : (e : Amb m →L[ℝ] ℝ × Tgt m) (e.symm (0, b0)) = (0, b0) :=
          e.apply_symm_apply (0, b0)
        rw [he, hGfderiv, ContinuousLinearMap.prod_apply] at h1
        have := congrArg Prod.snd h1
        simpa using this
  · intro x hx hxρ
    set u : ℝ := x i with hu
    have huδ : |u - p i| < δ := by rw [hu]; exact hx
    have hu_ball : u ∈ Metric.ball (p i) r_good := by
      rw [Metric.mem_ball, Real.dist_eq]; exact lt_trans huδ hδ_lt_good
    obtain ⟨htgt, -, hdist⟩ := hr_good hu_ball
    have hcoord : (g (u, (0 : Tgt m))) i = u := by
      have hrightu : G (g (u, (0 : Tgt m))) = (u, 0) := hright (u, (0 : Tgt m)) htgt
      have := congrArg Prod.fst hrightu
      simpa [G, coordL_apply] using this
    have hbu : b u = 1 := by
      apply b.one_of_mem_closedBall
      rw [Metric.mem_closedBall, hbIn, Real.dist_eq]
      linarith
    have heta : η u = g (u, (0 : Tgt m)) - u • EuclideanSpace.single i (1:ℝ) := by
      have hthis : hgt u = g (u, (0 : Tgt m))
          - (g (u, (0 : Tgt m))) i • EuclideanSpace.single i (1:ℝ) := rfl
      rw [show η u = b u • hgt u + (1 - b u) • w₀ from rfl, hbu, one_smul, sub_self, zero_smul,
        hthis, hcoord, add_zero]
    have hsub : x - (x i) • EuclideanSpace.single i (1:ℝ) - η (x i) = x - g (u, (0 : Tgt m)) := by
      rw [heta]
      abel
    rw [hsub] at hxρ
    have hxsrc : x ∈ Φ.source := by
      apply hr_src
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖x - p‖ ≤ ‖x - g (u, (0 : Tgt m))‖ + ‖g (u, (0 : Tgt m)) - p‖ := by
            rw [show x - p = (x - g (u, (0 : Tgt m))) + (g (u, (0 : Tgt m)) - p) by abel]
            exact norm_add_le _ _
        _ < ρ + r_src / 2 := by linarith [hxρ, hdist]
        _ < r_src := by rw [hρdef]; linarith
    have hxG : G x = (x i, F x) := by
      change (coordL i x, F x) = (x i, F x)
      rw [coordL_apply]
    constructor
    · intro hFx
      have h1 : g (u, (0 : Tgt m)) = x := by
        have hl : g (G x) = x := hleft x hxsrc
        rw [show G x = (u, F x) from by rw [hxG, hu], hFx] at hl
        exact hl
      have hgoal : x = u • EuclideanSpace.single i (1:ℝ) + η u := by
        rw [← h1, heta]
        abel
      exact hgoal
    · intro hxeq
      have hgx : x = g (u, (0 : Tgt m)) := by
        rw [hxeq, heta]
        abel
      have hFu : F (g (u, (0 : Tgt m))) = 0 := by
        have := congrArg Prod.snd (hright (u, (0 : Tgt m)) htgt)
        simpa [G] using this
      rw [hgx, hFu]

end

end Work.Drive
