import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.TParity.Basic

/-!
# The good parameter set is open

The two conditions on a parameter `t` that this file is about are

* every zero `y` in the compact set `K` (inside the nine-box) is a *regular* zero of `Ψ (t, ·)`, i.e.
  `∂₂Ψ (t, y)` is surjective, and
* every boundary zero in `K` lies on *exactly one* face — the face coordinate `bIdx k i` is `0` or `1`
  and the eight other coordinates are strictly interior — and the derivative restricted to the
  coordinate hyperplane `{v | v (bIdx k i) = 0}` is still surjective.

Both are *open* conditions in `t` for a fixed compact `K`: this is the content of
`Work.Drive.goodParamsOpen` below.  The mechanism is that both conditions are statements about the
pair `(t, y)` which are open in the pair (surjectivity of a continuous linear map is an open
condition, and the "exactly one face" shape is locally rigid once the eight other coordinates are
strictly interior), together with a compactness argument: a sequence of violating zeros would
subconverge to a zero of the limiting parameter, where the condition holds, contradicting openness
of the pair-level condition.
-/

namespace Work.Drive

open Filter Metric Set
open scoped Topology

noncomputable section

/-! ## Preliminaries: openness of surjectivity for continuous linear maps -/

/-- **Surjectivity is an open condition** for continuous linear maps with finite-dimensional target.
If `f` is surjective, pick a right inverse `g` of `f`; then for every `h` with `‖h ∘ g - 1‖ < 1` the
map `h ∘ g : F → F` is injective (the usual Neumann argument), hence bijective by finite
dimensionality, and therefore `h` is surjective. -/
private lemma isOpen_setOf_surjective_clm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] :
    IsOpen {f : E →L[ℝ] F | Function.Surjective f} := by
  rw [isOpen_iff_mem_nhds]
  intro f hf
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  have hcont : Continuous fun h : E →L[ℝ] F => ‖h.comp g - ContinuousLinearMap.id ℝ F‖ :=
    ((continuous_id.clm_comp_const g).sub continuous_const).norm
  have hmem : (fun h : E →L[ℝ] F => ‖h.comp g - ContinuousLinearMap.id ℝ F‖) f < 1 := by
    simp [hg]
  have hopen : {h : E →L[ℝ] F | ‖h.comp g - ContinuousLinearMap.id ℝ F‖ < 1} ∈ 𝓝 f :=
    (isOpen_Iio.preimage hcont).mem_nhds hmem
  refine mem_of_superset hopen ?_
  intro h hh
  set u : F →L[ℝ] F := h.comp g with hu
  have hker : ∀ z : F, u z = 0 → z = 0 := by
    intro z hz
    by_contra hz0
    have hpos : 0 < ‖z‖ := by rwa [norm_pos_iff]
    have hd : (u - ContinuousLinearMap.id ℝ F) z = -z := by
      rw [sub_apply, ContinuousLinearMap.id_apply, hz, zero_sub]
    have hle : ‖z‖ ≤ ‖u - ContinuousLinearMap.id ℝ F‖ * ‖z‖ := by
      calc ‖z‖ = ‖(u - ContinuousLinearMap.id ℝ F) z‖ := by rw [hd, norm_neg]
        _ ≤ _ := (u - ContinuousLinearMap.id ℝ F).le_opNorm z
    have hlt : ‖u - ContinuousLinearMap.id ℝ F‖ < 1 := by rw [hu]; exact hh
    have hlt2 : ‖u - ContinuousLinearMap.id ℝ F‖ * ‖z‖ < ‖z‖ :=
      mul_lt_of_lt_one_left hpos hlt
    exact absurd (lt_of_le_of_lt hle hlt2) (lt_irrefl _)
  have hinj : Function.Injective u := by
    intro x y hxy
    have h1 : u (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hker (x - y) h1)
  have hsurj : Function.Surjective u := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (V := F) (V₂ := F)
      (rfl : Module.finrank ℝ F = Module.finrank ℝ F)).mp ?_
    exact hinj
  intro z
  obtain ⟨w, hw⟩ := hsurj z
  exact ⟨g w, by rw [← hw]; rfl⟩

/-- The same for the restriction of `f` to a subspace: `f ↦ f ∘ subtypeL` is continuous and the
previous lemma applies to the resulting continuous linear map `S →L F`. -/
private lemma isOpen_setOf_restrict_surjective {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (S : Submodule ℝ E) :
    IsOpen {f : E →L[ℝ] F | Function.Surjective (fun v : S => f v.1)} := by
  have hcont : Continuous fun f : E →L[ℝ] F => f.comp S.subtypeL :=
    continuous_id.clm_comp_const S.subtypeL
  have h := (isOpen_setOf_surjective_clm (E := S) (F := F)).preimage hcont
  have hset : ((fun f : E →L[ℝ] F => f.comp S.subtypeL) ⁻¹' {g : S →L[ℝ] F | Function.Surjective g})
      = {f : E →L[ℝ] F | Function.Surjective (fun v : S => f v.1)} := by
    ext f
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    have hfun : (f.comp S.subtypeL : S → F) = fun v : S => f v.1 := by funext v; rfl
    rw [hfun]
  rwa [hset] at h

/-! ## The joint derivative of the family -/

/-- The coordinate hyperplane `{v | v c = 0}` of the nine-box, as a submodule. -/
private def coordKer (c : Fin 9) : Submodule ℝ (EuclideanSpace ℝ (Fin 9)) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 9 => ℝ) c).ker

/-- The derivative of `Ψ` in the *second* variable, as a function of the pair `(t, y)`. -/
private def sndFDeriv (m : ℕ)
    (Ψ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8)) :
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) →
      (EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 8)) :=
  fun p => fderiv ℝ (fun y' => Ψ (p.1, y')) p.2

/-- The partial derivative in the second variable is the full derivative composed with the
inclusion of the second factor. -/
private lemma sndFDeriv_eq {m : ℕ}
    {Ψ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8)}
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9)) :
    sndFDeriv m Ψ p = (fderiv ℝ Ψ p).comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 9))) := by
  have hd : DifferentiableAt ℝ Ψ p := (hΨ.contDiffAt).differentiableAt (by simp)
  have houter : HasFDerivAt Ψ (fderiv ℝ Ψ p) p := hd.hasFDerivAt
  have hinner : HasFDerivAt (fun y' : EuclideanSpace ℝ (Fin 9) => (p.1, y'))
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 9))) p.2 :=
    hasFDerivAt_prodMk_right p.1 p.2
  have h := (houter.comp p.2 hinner).fderiv
  simpa [sndFDeriv, Function.comp_def] using h

/-- `(t, y) ↦ ∂₂Ψ (t, y)` is continuous for a smooth `Ψ`. -/
private lemma continuous_sndFDeriv {m : ℕ}
    {Ψ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8)}
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) :
    Continuous (sndFDeriv m Ψ) := by
  have hc : Continuous
      (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) => fderiv ℝ Ψ p) :=
    hΨ.continuous_fderiv (by simp)
  have h2 : Continuous (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
      (fderiv ℝ Ψ p).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 9)))) :=
    hc.clm_comp_const _
  have heq : sndFDeriv m Ψ = fun p => (fderiv ℝ Ψ p).comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 9))) :=
    funext (sndFDeriv_eq hΨ)
  rw [heq]
  exact h2

/-! ## The local rigidity of the "exactly one face" shape -/

/-- **The shape of a zero on exactly one face.**  The face coordinate `bIdx k i` is `0` or `1`, the
two other coordinates of the `k`-th block, and all coordinates of the other two blocks, are strictly
interior. -/
private def faceShape (k i : Fin 3) (y : EuclideanSpace ℝ (Fin 9)) : Prop :=
  (y (Work.Drive.bIdx k i) = 0 ∨ y (Work.Drive.bIdx k i) = 1) ∧
  (∀ j : Fin 3, j ≠ i → y (Work.Drive.bIdx k j) ∈ Set.Ioo (0:ℝ) 1) ∧
  (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, y (Work.Drive.bIdx k' j) ∈ Set.Ioo (0:ℝ) 1)

/-- **The shape condition is rigid along a convergent sequence of boundary points.**  If the `y n`
are boundary points converging to `a`, the shape of `a` is inherited by `y n` eventually: the eight
coordinates other than the face coordinate are strictly interior for `a`, hence for `y n` (open
condition), and then the witness coordinate of the boundary condition of `y n` must be the face
coordinate, since all the others are interior. -/
private lemma eventually_faceShape {y : ℕ → EuclideanSpace ℝ (Fin 9)}
    {a : EuclideanSpace ℝ (Fin 9)}
    (hy : Tendsto y atTop (𝓝 a)) {k i : Fin 3} (ha : faceShape k i a)
    (hb : ∀ n, y n ∈ Submission.Drive.unitBoxBdry 8) :
    ∀ᶠ n in atTop, faceShape k i (y n) := by
  have h2 : ∀ᶠ n in atTop, ∀ j : Fin 3, j ≠ i →
      y n (Work.Drive.bIdx k j) ∈ Set.Ioo (0:ℝ) 1 := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = i
    · exact Eventually.of_forall fun n => by simp [hj]
    · have hmem : a (Work.Drive.bIdx k j) ∈ Set.Ioo (0:ℝ) 1 := ha.2.1 j hj
      have htend : Tendsto (fun n => y n (Work.Drive.bIdx k j)) atTop
          (𝓝 (a (Work.Drive.bIdx k j))) :=
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 9 => ℝ) (Work.Drive.bIdx k j)).continuous.tendsto a).comp hy
      exact (htend.eventually (isOpen_Ioo.mem_nhds hmem)).mono (fun n hn _ => hn)
  have h3 : ∀ᶠ n in atTop, ∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3,
      y n (Work.Drive.bIdx k' j) ∈ Set.Ioo (0:ℝ) 1 := by
    rw [Filter.eventually_all]
    intro k'
    by_cases hk' : k' = k
    · exact Eventually.of_forall fun n => by simp [hk']
    · have hinner : ∀ᶠ n in atTop, ∀ j : Fin 3,
          y n (Work.Drive.bIdx k' j) ∈ Set.Ioo (0:ℝ) 1 := by
        rw [Filter.eventually_all]
        intro j
        have hmem : a (Work.Drive.bIdx k' j) ∈ Set.Ioo (0:ℝ) 1 := ha.2.2 k' hk' j
        have htend : Tendsto (fun n => y n (Work.Drive.bIdx k' j)) atTop
            (𝓝 (a (Work.Drive.bIdx k' j))) :=
          ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 9 => ℝ) (Work.Drive.bIdx k' j)).continuous.tendsto a).comp hy
        exact htend.eventually (isOpen_Ioo.mem_nhds hmem)
      exact hinner.mono (fun n hn _ => hn)
  have h1 : ∀ᶠ n in atTop, (y n (Work.Drive.bIdx k i) = 0 ∨ y n (Work.Drive.bIdx k i) = 1) := by
    filter_upwards [h2, h3] with n hn2 hn3
    obtain ⟨j, hj⟩ := (hb n).2
    by_cases hji : j = Work.Drive.bIdx k i
    · rwa [hji] at hj
    · exfalso
      obtain ⟨k', j', hkj⟩ : ∃ (k' : Fin 3) (j' : Fin 3), Work.Drive.bIdx k' j' = j :=
        ⟨⟨j.val / 3, by omega⟩, ⟨j.val % 3, by omega⟩, by
          ext; rw [Work.Drive.bIdx_val, Nat.mod_add_div]⟩
      have hmem : y n j ∈ Set.Ioo (0:ℝ) 1 := by
        rw [← hkj]
        by_cases hk' : k' = k
        · rw [hk']
          exact hn2 j' (fun h => hji (by rw [← hkj, hk', h]))
        · exact hn3 k' hk' j'
      rcases hj with h0 | h1
      · exact absurd h0 (ne_of_gt hmem.1)
      · exact absurd h1 (ne_of_lt hmem.2)
  filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
  exact ⟨hn1, hn2, hn3⟩

/-! ## The theorem -/

/-- **The parameter set on which a smooth system has only regular zeros in a compact set, with every
boundary zero on exactly one face and the face-restricted derivative onto, is open.**

This is the openness half of the count-the-parameters step of the capping route: the good parameter set
of `Work.Drive.exists_meet3Data_of_good_family` (`exists_meet3Data_of_good_family.lean`), i.e. the set of
`t` for which the conclusion of that statement holds on a fixed compact `K`, is open in `t` — which is
what makes it possible to combine the conclusions of several charts (each contributing an open dense set
of parameters) into one parameter. -/
theorem goodParamsOpen (m : ℕ)
    (Ψ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8))
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) :
    IsOpen {t : EuclideanSpace ℝ (Fin m) |
      (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 → Ψ (t, y) = 0 →
        Function.Surjective (fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) => Ψ (t, y')) y)) ∧
      (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 → Ψ (t, y) = 0 →
        y ∈ Submission.Drive.unitBoxBdry 8 →
        ∃ (k : Fin 3) (i : Fin 3),
          (y (Work.Drive.bIdx k i) = 0 ∨ y (Work.Drive.bIdx k i) = 1) ∧
          (∀ j : Fin 3, j ≠ i → y (Work.Drive.bIdx k j) ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, y (Work.Drive.bIdx k' j) ∈ Set.Ioo (0 : ℝ) 1) ∧
          Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v (Work.Drive.bIdx k i) = 0} =>
            fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) => Ψ (t, y')) y v.1))} := by
  -- Openness of both pair-level conditions
  have hOpenSnd : IsOpen {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
      Function.Surjective (sndFDeriv m Ψ p)} :=
    (isOpen_setOf_surjective_clm (E := EuclideanSpace ℝ (Fin 9))
      (F := EuclideanSpace ℝ (Fin 8))).preimage (continuous_sndFDeriv hΨ)
  have hOpenFace : ∀ (k i : Fin 3),
      IsOpen {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v (Work.Drive.bIdx k i) = 0} =>
          sndFDeriv m Ψ p v.1)} := by
    intro k i
    exact (isOpen_setOf_restrict_surjective (S := coordKer (Work.Drive.bIdx k i))
      (F := EuclideanSpace ℝ (Fin 8))).preimage (continuous_sndFDeriv hΨ)
  -- the first clause
  have hAopen : IsOpen {t : EuclideanSpace ℝ (Fin m) |
      ∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 → Ψ (t, y) = 0 →
        Function.Surjective (fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) => Ψ (t, y')) y)} := by
    rw [isOpen_iff_mem_nhds]
    intro t₀ ht₀
    by_contra hnot
    -- a sequence of bad parameters ...
    have hseq : ∀ n : ℕ, ∃ t ∈ Metric.ball t₀ (1 / ((n:ℝ) + 1)),
        ¬ (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 → Ψ (t, y) = 0 →
          Function.Surjective (fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) => Ψ (t, y')) y)) := by
      intro n
      by_contra hcon
      have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := one_div_pos.mpr (by positivity)
      refine hnot (mem_of_superset (Metric.ball_mem_nhds t₀ hpos) ?_)
      intro t ht
      by_contra htbad'
      exact hcon ⟨t, ht, htbad'⟩
    choose t htball htbad using hseq
    have htend : Tendsto t atTop (𝓝 t₀) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h := htball n
      rw [Metric.mem_ball] at h
      exact le_of_lt h
    -- ... a bad zero for each of them ...
    have hy : ∀ n : ℕ, ∃ y : EuclideanSpace ℝ (Fin 9),
        y ∈ K ∧ y ∈ Submission.Drive.unitBox 8 ∧ Ψ (t n, y) = 0 ∧
        ¬ Function.Surjective (sndFDeriv m Ψ (t n, y)) := by
      intro n
      by_contra hcon
      apply htbad n
      intro y hyK hybox hyPsi
      by_contra hex
      exact hcon ⟨y, hyK, hybox, hyPsi, hex⟩
    choose y hy using hy
    -- ... and a limit point of the bad zeros
    have hKbox : IsCompact (K ∩ Submission.Drive.unitBox 8) :=
      hK.inter_right (Work.Drive.isClosed_unitBox 8)
    obtain ⟨a, ha, φ, hφmono, hφtend⟩ :=
      hKbox.tendsto_subseq (fun n => ⟨(hy n).1, (hy n).2.1⟩)
    have hpair : Tendsto (fun n => (t (φ n), y (φ n))) atTop (𝓝 (t₀, a)) :=
      (htend.comp hφmono.tendsto_atTop).prodMk_nhds hφtend
    have hPsi0 : Ψ (t₀, a) = 0 := by
      have h1 : Tendsto (fun n => Ψ (t (φ n), y (φ n))) atTop (𝓝 (Ψ (t₀, a))) :=
        (hΨ.continuous.continuousAt.tendsto).comp hpair
      have h2 : (fun n => Ψ (t (φ n), y (φ n))) =
          fun _ => (0 : EuclideanSpace ℝ (Fin 8)) :=
        funext fun n => (hy (φ n)).2.2.1
      rw [h2] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    have hA0 : Function.Surjective (sndFDeriv m Ψ (t₀, a)) := ht₀ a ha.1 ha.2 hPsi0
    -- contradiction with the openness of the pair-level condition
    have hev : ∀ᶠ n in atTop, Function.Surjective (sndFDeriv m Ψ (t (φ n), y (φ n))) :=
      hpair.eventually (hOpenSnd.mem_nhds hA0)
    have hnev : ∀ᶠ n in atTop, ¬ Function.Surjective (sndFDeriv m Ψ (t (φ n), y (φ n))) :=
      Eventually.of_forall fun n => (hy (φ n)).2.2.2
    obtain ⟨n, h1, h2⟩ := (hev.and hnev).exists
    exact h2 h1
  -- the second clause
  have hBopen : IsOpen {t : EuclideanSpace ℝ (Fin m) |
      ∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 → Ψ (t, y) = 0 →
        y ∈ Submission.Drive.unitBoxBdry 8 →
        ∃ (k : Fin 3) (i : Fin 3),
          (y (Work.Drive.bIdx k i) = 0 ∨ y (Work.Drive.bIdx k i) = 1) ∧
          (∀ j : Fin 3, j ≠ i → y (Work.Drive.bIdx k j) ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, y (Work.Drive.bIdx k' j) ∈ Set.Ioo (0 : ℝ) 1) ∧
          Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v (Work.Drive.bIdx k i) = 0} =>
            fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) => Ψ (t, y')) y v.1)} := by
    rw [isOpen_iff_mem_nhds]
    intro t₀ ht₀
    by_contra hnot
    have hseq : ∀ n : ℕ, ∃ t ∈ Metric.ball t₀ (1 / ((n:ℝ) + 1)),
        ¬ (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 → Ψ (t, y) = 0 →
          y ∈ Submission.Drive.unitBoxBdry 8 →
          ∃ (k : Fin 3) (i : Fin 3),
            (y (Work.Drive.bIdx k i) = 0 ∨ y (Work.Drive.bIdx k i) = 1) ∧
            (∀ j : Fin 3, j ≠ i → y (Work.Drive.bIdx k j) ∈ Set.Ioo (0 : ℝ) 1) ∧
            (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3,
              y (Work.Drive.bIdx k' j) ∈ Set.Ioo (0 : ℝ) 1) ∧
            Function.Surjective
              (fun v : {v : EuclideanSpace ℝ (Fin 9) // v (Work.Drive.bIdx k i) = 0} =>
                fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) => Ψ (t, y')) y v.1)) := by
      intro n
      by_contra hcon
      have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := one_div_pos.mpr (by positivity)
      refine hnot (mem_of_superset (Metric.ball_mem_nhds t₀ hpos) ?_)
      intro t ht
      by_contra htbad'
      exact hcon ⟨t, ht, htbad'⟩
    choose t htball htbad using hseq
    have htend : Tendsto t atTop (𝓝 t₀) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h := htball n
      rw [Metric.mem_ball] at h
      exact le_of_lt h
    have hy : ∀ n : ℕ, ∃ y : EuclideanSpace ℝ (Fin 9),
        y ∈ K ∧ y ∈ Submission.Drive.unitBox 8 ∧ Ψ (t n, y) = 0 ∧
        y ∈ Submission.Drive.unitBoxBdry 8 ∧
        ¬ (∃ (k : Fin 3) (i : Fin 3),
          (y (Work.Drive.bIdx k i) = 0 ∨ y (Work.Drive.bIdx k i) = 1) ∧
          (∀ j : Fin 3, j ≠ i → y (Work.Drive.bIdx k j) ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3,
            y (Work.Drive.bIdx k' j) ∈ Set.Ioo (0 : ℝ) 1) ∧
          Function.Surjective
            (fun v : {v : EuclideanSpace ℝ (Fin 9) // v (Work.Drive.bIdx k i) = 0} =>
              sndFDeriv m Ψ (t n, y) v.1)) := by
      intro n
      by_contra hcon
      apply htbad n
      intro y hyK hybox hyPsi hybdry
      by_contra hex
      exact hcon ⟨y, hyK, hybox, hyPsi, hybdry, hex⟩
    choose y hy using hy
    have hKbox : IsCompact
        ((K ∩ Submission.Drive.unitBox 8) ∩ Submission.Drive.unitBoxBdry 8) :=
      (hK.inter_right (Work.Drive.isClosed_unitBox 8)).inter_right
        (Work.Drive.isClosed_unitBoxBdry 8)
    obtain ⟨a, ha, φ, hφmono, hφtend⟩ :=
      hKbox.tendsto_subseq (fun n => ⟨⟨(hy n).1, (hy n).2.1⟩, (hy n).2.2.2.1⟩)
    have hpair : Tendsto (fun n => (t (φ n), y (φ n))) atTop (𝓝 (t₀, a)) :=
      (htend.comp hφmono.tendsto_atTop).prodMk_nhds hφtend
    have hPsi0 : Ψ (t₀, a) = 0 := by
      have h1 : Tendsto (fun n => Ψ (t (φ n), y (φ n))) atTop (𝓝 (Ψ (t₀, a))) :=
        (hΨ.continuous.continuousAt.tendsto).comp hpair
      have h2 : (fun n => Ψ (t (φ n), y (φ n))) =
          fun _ => (0 : EuclideanSpace ℝ (Fin 8)) :=
        funext fun n => (hy (φ n)).2.2.1
      rw [h2] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    -- the limiting boundary zero lies on exactly one face
    obtain ⟨k, i, hA, hB, hC, hD⟩ := ht₀ a ha.1.1 ha.1.2 hPsi0 ha.2
    -- and then so do the nearby bad zeros, with the same face
    have hevshape : ∀ᶠ n in atTop,
        ((y (φ n) (Work.Drive.bIdx k i) = 0 ∨ y (φ n) (Work.Drive.bIdx k i) = 1) ∧
        (∀ j : Fin 3, j ≠ i → y (φ n) (Work.Drive.bIdx k j) ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3,
          y (φ n) (Work.Drive.bIdx k' j) ∈ Set.Ioo (0 : ℝ) 1)) :=
      eventually_faceShape hφtend ⟨hA, hB, hC⟩ (fun n => (hy (φ n)).2.2.2.1)
    have hevsurj : ∀ᶠ n in atTop,
        Function.Surjective
          (fun v : {v : EuclideanSpace ℝ (Fin 9) // v (Work.Drive.bIdx k i) = 0} =>
            sndFDeriv m Ψ (t (φ n), y (φ n)) v.1) :=
      hpair.eventually ((hOpenFace k i).mem_nhds hD)
    have hev : ∀ᶠ n in atTop,
        ∃ (k : Fin 3) (i : Fin 3),
          (y (φ n) (Work.Drive.bIdx k i) = 0 ∨ y (φ n) (Work.Drive.bIdx k i) = 1) ∧
          (∀ j : Fin 3, j ≠ i → y (φ n) (Work.Drive.bIdx k j) ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3,
            y (φ n) (Work.Drive.bIdx k' j) ∈ Set.Ioo (0 : ℝ) 1) ∧
          Function.Surjective
            (fun v : {v : EuclideanSpace ℝ (Fin 9) // v (Work.Drive.bIdx k i) = 0} =>
              sndFDeriv m Ψ (t (φ n), y (φ n)) v.1) := by
      filter_upwards [hevshape, hevsurj] with n hn1 hn2
      exact ⟨k, i, hn1.1, hn1.2.1, hn1.2.2, hn2⟩
    have hnev : ∀ᶠ n in atTop,
        ¬ (∃ (k : Fin 3) (i : Fin 3),
          (y (φ n) (Work.Drive.bIdx k i) = 0 ∨ y (φ n) (Work.Drive.bIdx k i) = 1) ∧
          (∀ j : Fin 3, j ≠ i → y (φ n) (Work.Drive.bIdx k j) ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3,
            y (φ n) (Work.Drive.bIdx k' j) ∈ Set.Ioo (0 : ℝ) 1) ∧
          Function.Surjective
            (fun v : {v : EuclideanSpace ℝ (Fin 9) // v (Work.Drive.bIdx k i) = 0} =>
              sndFDeriv m Ψ (t (φ n), y (φ n)) v.1)) :=
      Eventually.of_forall fun n => (hy (φ n)).2.2.2.2
    obtain ⟨n, h1, h2⟩ := (hev.and hnev).exists
    exact h2 h1
  exact hAopen.inter hBopen

end

end Work.Drive
