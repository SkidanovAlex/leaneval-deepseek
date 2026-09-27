import Mathlib
import Submission.Work.Whitney.isClosed_setOf_norm_le
import Submission.Work.Embedding.immersion_locally_injective

open Set Filter Topology
open scoped Manifold ContDiff

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.Whitney

/-- **Extending a chart off its source.**  The values of an `OpenPartialHomeomorph` outside its
source are irrelevant: given any value `ψ` and any "default point" `p : M`, one can replace the
chart off its source by the constant `ψ`, keeping the source, the target, the values on the source
and the inverse on the target.  This is the device that makes the junk values of the modified chart
in `exists_clean_ball` harmless: they can be chosen to have arbitrarily large norm. -/
theorem exists_junk_extension {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (ψ : EuclideanSpace ℝ (Fin n)) (p : M) :
    ∃ c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      c'.source = c.source ∧ c'.target = c.target ∧
      (∀ y : M, y ∈ c.source → c' y = c y) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), u ∈ c.target → c'.symm u = c.symm u) ∧
      (∀ y : M, y ∉ c.source → c' y = ψ) := by
  classical
  refine ⟨{
    toFun := fun x => if x ∈ c.source then c x else ψ
    invFun := fun y => if y ∈ c.target then c.symm y else p
    source := c.source
    target := c.target
    map_source' := fun x hx => by rw [if_pos hx]; exact c.map_source hx
    map_target' := fun y hy => by rw [if_pos hy]; exact c.map_target hy
    left_inv' := fun x hx => by rw [if_pos hx, if_pos (c.map_source hx), c.left_inv hx]
    right_inv' := fun y hy => by rw [if_pos hy, if_pos (c.map_target hy), c.right_inv hy]
    open_source := c.open_source
    open_target := c.open_target
    continuousOn_toFun := by
      show ContinuousOn (fun x => if x ∈ c.source then c x else ψ) c.source
      exact ContinuousOn.congr c.continuousOn (fun x hx => by rw [if_pos hx])
    continuousOn_invFun := by
      show ContinuousOn (fun y => if y ∈ c.target then c.symm y else p) c.target
      exact ContinuousOn.congr c.continuousOn_symm (fun y hy => by rw [if_pos hy]) },
    rfl, rfl, (fun y hy => by show (if y ∈ c.source then c y else ψ) = c y; rw [if_pos hy]),
    (fun u hu => by show (if u ∈ c.target then c.symm u else p) = c.symm u; rw [if_pos hu]),
    (fun y hy => by show (if y ∈ c.source then c y else ψ) = ψ; rw [if_neg hy])⟩

/-- **Separation of the inner ball from the outer annulus.**  Let `f : M → ℝ^{2n}` be a continuous
map of a compact Hausdorff manifold, `c` a chart with `0 ∈ c.target`, and `c'` a chart agreeing with
`c` on `c.source` whose off-source values all equal a fixed vector `ψ` of norm `> 1`.  Assume that
`f` is injective on some neighbourhood `U` of `c.symm 0` and that the value `f (c.symm 0)` is not
attained at any double point of `f`.  Then, for all small enough positive `R`, a point carried by
`c'` into the ball of radius `R` has `f`-value different from that of any point carried by `c'`
outside the ball of radius `2R`. -/
theorem exists_separated_radius {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : Continuous f)
    (c c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc'app : ∀ y : M, y ∈ c.source → c' y = c y)
    (ψ : EuclideanSpace ℝ (Fin n)) (hψ : 1 < ‖ψ‖)
    (hc'junk : ∀ y : M, y ∉ c.source → c' y = ψ)
    (hclean0 : ∀ y z : M, y ≠ z → f y = f z → f (c.symm 0) ≠ f y)
    (hcontAt : ContinuousAt c.symm 0)
    (U : Set M) (hUopen : IsOpen U) (hUinj : Set.InjOn f U) (hpU : c.symm 0 ∈ U) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R ≤ R₀ →
      ∀ y z : M, ‖c' y‖ ≤ R → 2 * R ≤ ‖c' z‖ → f y ≠ f z := by
  classical
  by_contra hcon
  have hcon' : ∀ R₀ : ℝ, 0 < R₀ → ∃ R : ℝ, ∃ y z : M,
      0 < R ∧ R ≤ R₀ ∧ ‖c' y‖ ≤ R ∧ 2 * R ≤ ‖c' z‖ ∧ f y = f z := by
    intro R₀ hR₀
    by_contra h
    exact hcon ⟨R₀, hR₀,
      fun R hR hRR y z hy hz hyz => h ⟨R, y, z, hR, hRR, hy, hz, hyz⟩⟩
  have key : ∀ k : ℕ, ∃ R : ℝ, ∃ y z : M,
      0 < R ∧ R ≤ 1 / ((k : ℝ) + 1) ∧ ‖c' y‖ ≤ R ∧ 2 * R ≤ ‖c' z‖ ∧ f y = f z :=
    fun k => hcon' (1 / ((k : ℝ) + 1)) (by positivity)
  choose R y z hkey using key
  have hRpos : ∀ k : ℕ, 0 < R k := fun k => (hkey k).1
  have hRle : ∀ k : ℕ, R k ≤ 1 / ((k : ℝ) + 1) := fun k => (hkey k).2.1
  have hy : ∀ k : ℕ, ‖c' (y k)‖ ≤ R k := fun k => (hkey k).2.2.1
  have hz : ∀ k : ℕ, 2 * R k ≤ ‖c' (z k)‖ := fun k => (hkey k).2.2.2.1
  have hyz : ∀ k : ℕ, f (y k) = f (z k) := fun k => (hkey k).2.2.2.2
  have hRtend : Tendsto R atTop (𝓝 0) :=
    squeeze_zero (fun k => le_of_lt (hRpos k)) hRle tendsto_one_div_add_atTop_nhds_zero_nat
  -- `y k` tends to `p = c.symm 0`
  have hy_tend : Tendsto y atTop (𝓝 (c.symm 0)) := by
    have hev_src : ∀ᶠ k in atTop, y k ∈ c.source := by
      filter_upwards [hRtend.eventually (Iio_mem_nhds (show (0 : ℝ) < ‖ψ‖ by linarith))] with k hk
      by_contra hys
      have hle := hy k
      rw [hc'junk (y k) hys] at hle
      linarith
    have hcy : Tendsto (fun k => c (y k)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => c' (y k)) atTop (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.mpr
          (squeeze_zero (fun k => norm_nonneg _) hy hRtend)
      exact h1.congr' (by
        filter_upwards [hev_src] with k hk
        exact hc'app (y k) hk)
    have h2 : Tendsto (fun k => c.symm (c (y k))) atTop (𝓝 (c.symm 0)) :=
      hcontAt.tendsto.comp hcy
    have h3 : (fun k => c.symm (c (y k))) =ᶠ[atTop] y := by
      filter_upwards [hev_src] with k hk
      exact c.left_inv hk
    exact h2.congr' h3
  -- extract a convergent subsequence of `z`
  obtain ⟨z_star, φ, hφmono, hφtend⟩ := CompactSpace.tendsto_subseq z
  have hytend : Tendsto (fun k => y (φ k)) atTop (𝓝 (c.symm 0)) :=
    hy_tend.comp (StrictMono.tendsto_atTop hφmono)
  have hfz : Tendsto (fun k => f (z (φ k))) atTop (𝓝 (f z_star)) :=
    hf.continuousAt.tendsto.comp hφtend
  have hfy : Tendsto (fun k => f (y (φ k))) atTop (𝓝 (f (c.symm 0))) :=
    hf.continuousAt.tendsto.comp hytend
  have heq : f z_star = f (c.symm 0) := by
    have hfy' : Tendsto (fun k => f (y (φ k))) atTop (𝓝 (f z_star)) :=
      hfz.congr' (by
        filter_upwards with k
        exact (hyz (φ k)).symm)
    exact tendsto_nhds_unique hfy' hfy
  by_cases hzp : z_star = c.symm 0
  · -- both sequences tend to `p`, where `f` is injective
    have hzt : Tendsto (fun k => z (φ k)) atTop (𝓝 (c.symm 0)) := hzp ▸ hφtend
    have hev_eq : ∀ᶠ k in atTop, y (φ k) = z (φ k) := by
      filter_upwards [hytend.eventually (hUopen.mem_nhds hpU),
        hzt.eventually (hUopen.mem_nhds hpU)] with k h1 h2
      exact hUinj h1 h2 (hyz (φ k))
    have hcontra : ∀ᶠ k : ℕ in atTop, False := by
      filter_upwards [hev_eq] with k hk
      have h1 := hy (φ k)
      have h2 := hz (φ k)
      rw [← hk] at h2
      linarith [hRpos (φ k)]
    obtain ⟨k, hk⟩ := hcontra.exists
    exact hk
  · -- otherwise the value of `p` is attained at a double point, contrary to `hclean0`
    exact absurd rfl (hclean0 (c.symm 0) z_star (fun h => hzp h.symm) heq.symm)

/-- **A positive minimum is attained.**  If `f : M → F` is continuous on a compact Hausdorff space
`M` and two closed sets `K`, `Z` have no pair of points with equal `f`-values, then the `f`-values of
`K` and `Z` are separated by a positive constant. -/
theorem exists_pos_le_norm_sub {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F] {f : M → F} (hf : Continuous f) {K Z : Set M}
    (hK : IsClosed K) (hZ : IsClosed Z) (hsep : ∀ y ∈ K, ∀ z ∈ Z, f y ≠ f z) :
    ∃ η : ℝ, 0 < η ∧ ∀ y ∈ K, ∀ z ∈ Z, η ≤ ‖f y - f z‖ := by
  have hphi : Continuous fun q : M × M => ‖f q.1 - f q.2‖ :=
    ((hf.comp continuous_fst).sub (hf.comp continuous_snd)).norm
  by_cases hne : (K ×ˢ Z).Nonempty
  · obtain ⟨q, hq, hqmin⟩ :=
      (hK.isCompact.prod hZ.isCompact).exists_isMinOn hne hphi.continuousOn
    refine ⟨‖f q.1 - f q.2‖, ?_, ?_⟩
    · exact norm_pos_iff.mpr (sub_ne_zero.mpr (hsep q.1 hq.1 q.2 hq.2))
    · intro y hy z hz
      exact hqmin (show (y, z) ∈ K ×ˢ Z from ⟨hy, hz⟩)
  · refine ⟨1, one_pos, ?_⟩
    intro y hy z hz
    exact absurd ⟨(y, z), hy, hz⟩ hne

/-- **The clean-ball lemma.**  Around a "clean" point `p = c.symm 0` of an immersion
`f : M → ℝ^{2n}` (a point whose value is not taken by any double point of `f`) there is a chart `c'`
with the same source and target as `c`, an explicit radius `R > 0` such that `f` is injective on the
part of `M` carried by `c'` into the ball of radius `2R`, and a positive `η` separating the
`f`-values of the inner ball of radius `R` from those outside the ball of radius `2R`. -/
theorem exists_clean_ball {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ c.target)
    (hcsm : ∀ y : M, y ∈ c.source →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y)
    (hcinv : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c.target →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm u)
    (hclean0 : ∀ y z : M, y ≠ z → f y = f z → f (c.symm 0) ≠ f y) :
    ∃ (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (R η : ℝ),
      0 < R ∧ 0 < η ∧
      c'.source = c.source ∧ c'.target = c.target ∧
      (∀ y : M, y ∈ c.source → c' y = c y) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), u ∈ c.target → c'.symm u = c.symm u) ∧
      Metric.ball 0 (3 * R) ⊆ c'.target ∧
      (∀ y : M, ‖c' y‖ ≤ 3 * R → y ∈ c'.source) ∧
      (∀ y z : M, ‖c' y‖ ≤ 2 * R → ‖c' z‖ ≤ 2 * R → f y = f z → y = z) ∧
      (∀ y z : M, ‖c' y‖ ≤ R → 2 * R ≤ ‖c' z‖ → η ≤ ‖f y - f z‖) := by
  classical
  set p : M := c.symm 0 with hp
  have hpsrc : p ∈ c.source := by rw [hp]; exact c.map_target h0
  have hfcont : Continuous f := hf.continuous
  obtain ⟨U, hUopen, hpU, hUinj⟩ := Work.Embedding.immersion_locally_injective f hf himm p
  have hcontAt : ContinuousAt c.symm 0 :=
    c.continuousOn_symm.continuousAt (c.open_target.mem_nhds h0)
  have hnhds : c.symm ⁻¹' U ∩ c.target ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)) :=
    Filter.inter_mem (hcontAt.preimage_mem_nhds (hUopen.mem_nhds hpU))
      (c.open_target.mem_nhds h0)
  obtain ⟨ε, hεpos, hεball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hεU : ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ < ε → c.symm u ∈ U := by
    intro u hu
    exact (hεball (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hu)).1
  have hεtgt : ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ < ε → u ∈ c.target := by
    intro u hu
    exact (hεball (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hu)).2
  by_cases hSing : Subsingleton (EuclideanSpace ℝ (Fin n))
  · -- Degenerate case: the model space is a point, so `n = 0`, `f` is constant and `M` a point.
    have hn0 : n = 0 := by
      haveI : Subsingleton (EuclideanSpace ℝ (Fin n)) := hSing
      have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = 0 :=
        Module.finrank_zero_of_subsingleton
      rw [finrank_euclideanSpace, Fintype.card_fin] at hfr
      exact hfr
    subst hn0
    haveI hEsub : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance
    haveI hFsub : Subsingleton (EuclideanSpace ℝ (Fin (2 * 0))) := inferInstance
    have hMsub : Subsingleton M := ⟨fun y z => by
      by_contra hne
      exact absurd (Subsingleton.elim (f (c.symm 0)) (f y))
        (hclean0 y z hne (Subsingleton.elim (f y) (f z)))⟩
    haveI := hMsub
    refine ⟨c, 1, 1, one_pos, one_pos, rfl, rfl, (fun y hy => rfl), (fun u hu => rfl),
      ?_, ?_, ?_, ?_⟩
    · intro u hu
      have : u = 0 := Subsingleton.elim u 0
      rw [this]; exact h0
    · intro y hy
      have : y = p := Subsingleton.elim y p
      rw [this]; exact hpsrc
    · intro y z hy hz hyz
      exact Subsingleton.elim y z
    · intro y z hy hz
      have hz0 : ‖c z‖ = 0 := by
        have : c z = 0 := Subsingleton.elim (c z) 0
        rw [this, norm_zero]
      linarith
  · -- Main case: a vector of norm `> 1` makes the junk values of the modified chart large.
    obtain ⟨a, b, hab⟩ : ∃ a b : EuclideanSpace ℝ (Fin n), a ≠ b := by
      by_contra h
      push Not at h
      exact hSing ⟨fun x y => h x y⟩
    have hv : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hvpos : 0 < ‖a - b‖ := norm_pos_iff.mpr hv
    set ψ : EuclideanSpace ℝ (Fin n) := (2 / ‖a - b‖) • (a - b) with hψdef
    have hψ : (1 : ℝ) < ‖ψ‖ := by
      rw [hψdef, norm_smul, Real.norm_of_nonneg (by positivity),
        div_mul_cancel₀ _ (ne_of_gt hvpos)]
      norm_num
    obtain ⟨c', hc'src, hc'tgt, hc'app, hc'symm, hc'junk⟩ := exists_junk_extension c ψ p
    obtain ⟨R₀, hR₀pos, hQ⟩ :=
      exists_separated_radius f hfcont c c' hc'app ψ hψ hc'junk hclean0 hcontAt U hUopen
        hUinj (by rw [← hp]; exact hpU)
    set R : ℝ := min (min R₀ (ε / 8)) (1 / 6) with hRdef
    have hRpos : 0 < R := by
      rw [hRdef]; exact lt_min (lt_min hR₀pos (by linarith)) (by norm_num)
    have hRle₀ : R ≤ R₀ := by
      rw [hRdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hRleε : R ≤ ε / 8 := by
      rw [hRdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hRle6 : R ≤ 1 / 6 := by rw [hRdef]; exact min_le_right _ _
    have h3Rε : 3 * R < ε := by linarith
    have h2Rε : 2 * R < ε := by linarith
    have h3Rψ : 3 * R < ‖ψ‖ := by linarith
    have hsrc3 : ∀ y : M, ‖c' y‖ < 3 * R → y ∈ c'.source := by
      intro y hy'
      by_contra hys
      have hys' : y ∉ c.source := by simpa [hc'src] using hys
      have hle := hy'
      rw [hc'junk y hys'] at hle
      linarith
    have hsrc3le : ∀ y : M, ‖c' y‖ ≤ 3 * R → y ∈ c'.source := by
      intro y hy'
      by_contra hys
      have hys' : y ∉ c.source := by simpa [hc'src] using hys
      have hle := hy'
      rw [hc'junk y hys'] at hle
      linarith
    have hball3 : Metric.ball 0 (3 * R) ⊆ c'.target := by
      rw [hc'tgt]
      intro u hu
      have hu' : ‖u‖ < 3 * R := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hu; exact hu
      exact hεtgt u (by linarith)
    have hmemU : ∀ y : M, ‖c' y‖ ≤ 2 * R → y ∈ U := by
      intro y hy'
      have hys : y ∈ c.source := by
        have h1 := hsrc3le y (by linarith)
        simpa [hc'src] using h1
      have hnorm : ‖c y‖ < ε := by
        rw [← hc'app y hys]; linarith
      have h2 := hεU (c y) hnorm
      rwa [c.left_inv hys] at h2
    have hinj_ball : ∀ y z : M, ‖c' y‖ ≤ 2 * R → ‖c' z‖ ≤ 2 * R → f y = f z → y = z :=
      fun y z hy' hz' hyz' => hUinj (hmemU y hy') (hmemU z hz') hyz'
    let K1 : Set M := {y : M | ‖c' y‖ ≤ R}
    let K2 : Set M := {z : M | 2 * R ≤ ‖c' z‖}
    have hmemK1 : ∀ y : M, y ∈ K1 ↔ ‖c' y‖ ≤ R := fun y => Iff.rfl
    have hmemK2 : ∀ z : M, z ∈ K2 ↔ 2 * R ≤ ‖c' z‖ := fun z => Iff.rfl
    have hK1closed : IsClosed K1 :=
      isClosed_setOf_norm_le c' (R := R) (r := R) (by linarith) hsrc3 hball3
    have hK2closed : IsClosed K2 := by
      have hopen : IsOpen {z : M | ‖c' z‖ < 2 * R} := by
        have hset : {z : M | ‖c' z‖ < 2 * R} = c.symm '' Metric.ball 0 (2 * R) := by
          ext z
          constructor
          · intro hz'
            have hz2 : ‖c' z‖ < 2 * R := hz'
            have hzs : z ∈ c.source := by
              have h1 : ‖c' z‖ < 3 * R := by linarith
              have h2 := hsrc3 z h1
              simpa [hc'src] using h2
            refine ⟨c z, ?_, ?_⟩
            · rw [Metric.mem_ball, dist_eq_norm, sub_zero, ← hc'app z hzs]; exact hz2
            · exact c.left_inv hzs
          · rintro ⟨u, hu, rfl⟩
            have hu2 : ‖u‖ < 2 * R := by
              rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hu; exact hu
            have hutgt : u ∈ c.target := hεtgt u (by linarith)
            have h1 : c'.symm u = c.symm u := hc'symm u hutgt
            have h2 : c' (c'.symm u) = u := c'.right_inv (by rw [hc'tgt]; exact hutgt)
            show ‖c' (c.symm u)‖ < 2 * R
            rw [← h1, h2]
            exact hu2
        rw [hset]
        exact c.symm.isOpen_image_of_subset_source Metric.isOpen_ball (by
          intro u hu
          have hu2 : ‖u‖ < 2 * R := by
            rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hu; exact hu
          exact hεtgt u (by linarith))
      have hset2 : K2 = {z : M | ‖c' z‖ < 2 * R}ᶜ := by
        ext z
        show 2 * R ≤ ‖c' z‖ ↔ ¬ ‖c' z‖ < 2 * R
        exact not_lt.symm
      rw [hset2]
      exact hopen.isClosed_compl
    obtain ⟨η, hηpos, hη⟩ := exists_pos_le_norm_sub hfcont hK1closed hK2closed
      (fun y hy z hz => hQ R hRpos hRle₀ y z ((hmemK1 y).mp hy) ((hmemK2 z).mp hz))
    exact ⟨c', R, η, hRpos, hηpos, hc'src, hc'tgt, hc'app, hc'symm, hball3, hsrc3le,
      hinj_ball, fun y z hy' hz' => hη y ((hmemK1 y).mpr hy') z ((hmemK2 z).mpr hz')⟩

end Work.Whitney
