import Mathlib

/-!
# Arcs in an open path-connected subset of a topological manifold

Given an open subset `W` of a topological manifold `M` which is path connected, and two
distinct points `x y ∈ W`, there is a continuous map `γ : ℝ → M` which is injective on
`[0,1]`, satisfies `γ 0 = x`, `γ 1 = y` and maps `[0,1]` into `W`.

The proof is the standard "open and closed" argument: the set of points which can be joined to
`x` by an injective arc inside `W` is both open and closed in `W` and contains `x`; since `W` is
preconnected it is all of `W`.  The geometric input is that a chart ball contained in `W` is
convex, so that segments in chart coordinates give arcs, and that a path entering such a ball
can be truncated at its first entry point.
-/

namespace Work.Whitney.PathTools

open Set Topology Filter

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ### The clamp map onto `[0,1]` -/

/-- The projection of `ℝ` onto the unit interval, viewed as a real number. -/
noncomputable def clamp (t : ℝ) : ℝ := (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ)

@[simp] lemma clamp_zero : clamp 0 = 0 := by simp [clamp]

@[simp] lemma clamp_one : clamp 1 = 1 := by simp [clamp]

lemma continuous_clamp : Continuous clamp :=
  continuous_subtype_val.comp continuous_projIcc

lemma clamp_mem (t : ℝ) : clamp t ∈ Set.Icc (0 : ℝ) 1 := (Set.projIcc _ _ _ t).2

lemma clamp_nonneg (t : ℝ) : 0 ≤ clamp t := (clamp_mem t).1

lemma clamp_le_one (t : ℝ) : clamp t ≤ 1 := (clamp_mem t).2

lemma clamp_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : clamp t = t := by
  rw [clamp, Set.projIcc_of_mem zero_le_one ht]

/-! ### Chart balls -/

/-- A chart of `M`, together with a closed ball (in chart coordinates) around `z` whose inverse
image is contained in a prescribed set `W`. -/
structure ChartBall (n : ℕ) (M : Type*) [TopologicalSpace M] (W : Set M) (z : M) where
  /-- The chart. -/
  c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  /-- The radius of the ball. -/
  ρ : ℝ
  hρ : 0 < ρ
  hz : z ∈ c.source
  hclosed : Metric.closedBall (c z) ρ ⊆ c.target
  hW : ∀ v ∈ Metric.closedBall (c z) ρ, c.symm v ∈ W

section Helpers

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

section ChartBallSection

variable {W : Set M} {z : M} (b : ChartBall n M W z)

namespace ChartBall

lemma symm_injOn : Set.InjOn (b.c.symm : EuclideanSpace ℝ (Fin n) → M)
    (Metric.closedBall (b.c z) b.ρ) :=
  (b.c.symm.injOn).mono (by rw [OpenPartialHomeomorph.symm_source]; exact b.hclosed)

/-- The closed chart ball around `z`, as a subset of `M`. -/
def K : Set M := b.c.symm '' Metric.closedBall (b.c z) b.ρ

lemma mem_K {v : M} : v ∈ b.K ↔ ∃ w ∈ Metric.closedBall (b.c z) b.ρ, b.c.symm w = v :=
  Iff.rfl

lemma K_subset_source : b.K ⊆ b.c.source := by
  rintro v ⟨w, hw, rfl⟩
  exact b.c.map_target (b.hclosed hw)

lemma K_subset_W : b.K ⊆ W := by
  rintro v ⟨w, hw, rfl⟩
  exact b.hW w hw

lemma isClosed_K : IsClosed b.K :=
  ((isCompact_closedBall (b.c z) b.ρ).image_of_continuousOn
    (b.c.continuousOn_symm.mono b.hclosed)).isClosed

lemma self_mem_K : z ∈ b.K :=
  ⟨b.c z, Metric.mem_closedBall.mpr (by rw [dist_self]; exact b.hρ.le), b.c.left_inv b.hz⟩

lemma ballImage_open : IsOpen (b.c.symm '' Metric.ball (b.c z) b.ρ) :=
  b.c.isOpen_image_symm_of_subset_target Metric.isOpen_ball
    (fun v hv => b.hclosed (Metric.ball_subset_closedBall hv))

lemma self_mem_ballImage : z ∈ b.c.symm '' Metric.ball (b.c z) b.ρ :=
  ⟨b.c z, Metric.mem_ball.mpr (by rw [dist_self]; exact b.hρ), b.c.left_inv b.hz⟩

lemma ballImage_subset_K : b.c.symm '' Metric.ball (b.c z) b.ρ ⊆ b.K := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, Metric.ball_subset_closedBall hv, rfl⟩

lemma mem_closedBall_seg {v w : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Metric.closedBall (b.c z) b.ρ) (hw : w ∈ Metric.closedBall (b.c z) b.ρ)
    (t : ℝ) : v + clamp t • (w - v) ∈ Metric.closedBall (b.c z) b.ρ := by
  have h2 : v + (w - v) ∈ Metric.closedBall (b.c z) b.ρ := by
    have h3 : v + (w - v) = w := by abel
    rwa [h3]
  exact (convex_closedBall (b.c z) b.ρ).add_smul_mem hv h2 (clamp_mem t)

lemma continuous_seg {v w : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Metric.closedBall (b.c z) b.ρ) (hw : w ∈ Metric.closedBall (b.c z) b.ρ) :
    Continuous fun t : ℝ => b.c.symm (v + clamp t • (w - v)) :=
  (b.c.continuousOn_symm.mono b.hclosed).comp_continuous
    (continuous_const.add (continuous_clamp.smul continuous_const))
    (fun t => b.mem_closedBall_seg hv hw t)

lemma seg_zero (v w : EuclideanSpace ℝ (Fin n)) :
    (fun t : ℝ => b.c.symm (v + clamp t • (w - v))) 0 = b.c.symm v := by simp

lemma seg_one (v w : EuclideanSpace ℝ (Fin n)) :
    (fun t : ℝ => b.c.symm (v + clamp t • (w - v))) 1 = b.c.symm w := by simp

lemma seg_injOn {v w : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Metric.closedBall (b.c z) b.ρ) (hw : w ∈ Metric.closedBall (b.c z) b.ρ)
    (hvw : v ≠ w) :
    Set.InjOn (fun t : ℝ => b.c.symm (v + clamp t • (w - v))) (Set.Icc (0 : ℝ) 1) := by
  intro s hs u hu hsu
  have hs' : clamp s = s := clamp_of_mem hs
  have hu' : clamp u = u := clamp_of_mem hu
  have h : v + clamp s • (w - v) = v + clamp u • (w - v) :=
    b.symm_injOn (b.mem_closedBall_seg hv hw s) (b.mem_closedBall_seg hv hw u) hsu
  rw [hs', hu'] at h
  have h' : s • (w - v) = u • (w - v) := by simpa using h
  have key : (s - u) • (w - v) = 0 := by rw [sub_smul]; exact sub_eq_zero.mpr h'
  rcases smul_eq_zero.mp key with h0 | h0
  · linarith
  · exact absurd (sub_eq_zero.mp h0).symm hvw

end ChartBall

end ChartBallSection

/-! ### Arcs -/

/-- `γ` is a continuous arc from `x` to `y` lying in `W`, injective on `[0,1]`. -/
def IsArcTo (W : Set M) (x y : M) (γ : ℝ → M) : Prop :=
  Continuous γ ∧ Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧ γ 0 = x ∧ γ 1 = y ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ W

/-- The set of points reachable from `x` inside `W` by an injective arc (`x` included). -/
def Reached (W : Set M) (x : M) : Set M := {y | y = x ∨ ∃ γ, IsArcTo W x y γ}

lemma IsArcTo.trunc {W : Set M} {x y : M} {γ : ℝ → M} (hγ : IsArcTo W x y γ) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hs0 : 0 < s) : IsArcTo W x (γ s) (fun t => γ (t * s)) := by
  refine ⟨hγ.1.comp (continuous_id.mul continuous_const), ?_, ?_, ?_, ?_⟩
  · intro a ha c hc hac
    exact mul_right_cancel₀ (ne_of_gt hs0)
      (hγ.2.1 ⟨by nlinarith [ha.1, hs.1], by nlinarith [ha.1, ha.2, hs.1, hs.2]⟩
        ⟨by nlinarith [hc.1, hs.1], by nlinarith [hc.1, hc.2, hs.1, hs.2]⟩ hac)
  · simp [hγ.2.2.1]
  · simp
  · intro t ht
    exact hγ.2.2.2.2 (t * s) ⟨by nlinarith [ht.1, hs.1], by nlinarith [ht.1, ht.2, hs.1, hs.2]⟩

lemma Reached.of_mem_range {W : Set M} {x y z' : M} {γ : ℝ → M} (hγ : IsArcTo W x y γ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (hzs : γ s = z') (hz'x : z' ≠ x) :
    Reached W x z' := by
  have hs0 : 0 < s := by
    by_contra h
    have hs' : s = 0 := le_antisymm (not_lt.mp h) hs.1
    rw [hs', hγ.2.2.1] at hzs
    exact hz'x hzs.symm
  refine Or.inr ⟨fun t => γ (t * s), ?_⟩
  have h := hγ.trunc hs hs0
  rwa [hzs] at h

/-! ### Reachability and the open/closed argument -/

section Reach

namespace ChartBall

variable {W : Set M} {z : M} (b : ChartBall n M W z)

lemma reached_of_mem_self {x : M} (hxK : x ∈ b.K) : ∀ z' ∈ b.K, Reached W x z' := by
  intro z' hz'
  obtain ⟨v, hv, hxv⟩ := hxK
  obtain ⟨v', hv', hzv'⟩ := hz'
  rcases eq_or_ne z' x with h | h
  · exact Or.inl h
  · refine Or.inr ⟨fun t : ℝ => b.c.symm (v + clamp t • (v' - v)), b.continuous_seg hv hv',
      ?_, ?_, ?_, ?_⟩
    · refine b.seg_injOn hv hv' ?_
      intro hvv
      exact h (by rw [← hzv', ← hvv, hxv])
    · simpa using (b.seg_zero v v').trans hxv
    · simpa using (b.seg_one v v').trans hzv'
    · intro t _
      exact b.hW _ (b.mem_closedBall_seg hv hv' t)

lemma reached_of_mem {x w₀ : M} {γ : ℝ → M} (hγ : IsArcTo W x w₀ γ) (hw₀ : w₀ ∈ b.K) :
    ∀ z' ∈ b.K, Reached W x z' := by
  intro z' hz'
  by_cases hxK : x ∈ b.K
  · exact b.reached_of_mem_self hxK z' hz'
  by_cases hzγ : ∃ s ∈ Set.Icc (0 : ℝ) 1, γ s = z'
  · obtain ⟨s, hs, hzs⟩ := hzγ
    exact Reached.of_mem_range hγ hs hzs (fun h => hxK (h ▸ hz'))
  · have hz'γ : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ≠ z' := fun t ht h => hzγ ⟨t, ht, h⟩
    let S : Set ℝ := {t | t ∈ Set.Icc (0 : ℝ) 1 ∧ γ t ∈ b.K}
    have hSclosed : IsClosed S := by
      have hSeq : S = Set.Icc (0 : ℝ) 1 ∩ γ ⁻¹' b.K := rfl
      rw [hSeq]
      exact isClosed_Icc.inter (b.isClosed_K.preimage hγ.1)
    have hSne : S.Nonempty := ⟨1, ⟨by norm_num, by rw [hγ.2.2.2.1]; exact hw₀⟩⟩
    have hbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
    let t₀ : ℝ := sInf S
    have ht₀S : t₀ ∈ S := hSclosed.csInf_mem hSne hbdd
    have ht₀min : ∀ t ∈ S, t₀ ≤ t := fun t ht => csInf_le hbdd ht
    have ht₀I : t₀ ∈ Set.Icc (0 : ℝ) 1 := ht₀S.1
    have ht₀K : γ t₀ ∈ b.K := ht₀S.2
    have ht₀pos : 0 < t₀ := by
      rcases lt_or_eq_of_le ht₀I.1 with h | h
      · exact h
      · exact absurd (hγ.2.2.1 ▸ (h ▸ ht₀K)) hxK
    obtain ⟨v, hv, hpv⟩ := ht₀K
    obtain ⟨v', hv', hzv'⟩ := hz'
    have hvv' : v ≠ v' := by
      intro hvv
      exact hz'γ t₀ ht₀I (by rw [← hpv, hvv, hzv'])
    have huniq : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ (t * t₀) ∈ b.K → t = 1 := by
      intro t ht htK
      have htI : t * t₀ ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by nlinarith [ht.1, ht₀I.1], by nlinarith [ht.1, ht.2, ht₀I.1, ht₀I.2]⟩
      have h1 : t₀ ≤ t * t₀ := ht₀min _ ⟨htI, htK⟩
      have h2 : t * t₀ ≤ t₀ := by nlinarith [ht.2, ht₀I.1]
      have h3 : t * t₀ = t₀ := le_antisymm h2 h1
      exact mul_right_cancel₀ (ne_of_gt ht₀pos) (by rw [h3, one_mul])
    let α : ℝ → M := fun t => γ (t * t₀)
    let σ : ℝ → M := fun t => b.c.symm (v + clamp t • (v' - v))
    let F : ℝ → M := fun t => if 2 * t ≤ 1 then α (2 * t) else σ (2 * t - 1)
    have hα_cont : Continuous α := hγ.1.comp (continuous_id.mul continuous_const)
    have hσ_cont : Continuous σ := b.continuous_seg hv hv'
    have hα_inj : Set.InjOn α (Set.Icc (0 : ℝ) 1) := (hγ.trunc ht₀I ht₀pos).2.1
    have hα_one : α 1 = γ t₀ := by simp [α]
    have hσ_zero : σ 0 = γ t₀ := by simp [σ, hpv]
    have hKσ : ∀ t : ℝ, σ t ∈ b.K := fun t =>
      ⟨v + clamp t • (v' - v), b.mem_closedBall_seg hv hv' t, rfl⟩
    have hF_cont : Continuous F := by
      dsimp only [F]
      refine Continuous.if_le (hα_cont.comp (continuous_const.mul continuous_id))
        (hσ_cont.comp ((continuous_const.mul continuous_id).sub continuous_const))
        (continuous_const.mul continuous_id) continuous_const ?_
      intro t ht
      rw [ht]
      simp only [sub_self, hα_one, hσ_zero]
    have hF_zero : F 0 = x := by
      dsimp only [F, α]
      rw [if_pos (by norm_num : (2 : ℝ) * 0 ≤ 1)]
      simp only [mul_zero, zero_mul, hγ.2.2.1]
    have hF_one : F 1 = z' := by
      dsimp only [F, σ]
      rw [if_neg (by norm_num : ¬ ((2 : ℝ) * 1 ≤ 1))]
      rw [show (2 : ℝ) * 1 - 1 = 1 by norm_num, clamp_one, one_smul,
        show v + (v' - v) = v' by abel, hzv']
    have hF_img : ∀ t ∈ Set.Icc (0 : ℝ) 1, F t ∈ W := by
      intro t ht
      by_cases ht' : 2 * t ≤ 1
      · dsimp only [F, α]
        rw [if_pos ht']
        exact hγ.2.2.2.2 ((2 * t) * t₀)
          ⟨by nlinarith [ht.1, ht₀I.1], by nlinarith [ht', ht.1, ht₀I.1, ht₀I.2]⟩
      · dsimp only [F, σ]
        rw [if_neg ht']
        exact b.hW _ (b.mem_closedBall_seg hv hv' (2 * t - 1))
    have hF_inj : Set.InjOn F (Set.Icc (0 : ℝ) 1) := by
      intro a ha c hc hac
      dsimp only [F, α, σ] at hac ⊢
      by_cases ha' : 2 * a ≤ 1
      · by_cases hc' : 2 * c ≤ 1
        · rw [if_pos ha', if_pos hc'] at hac
          have h2a : 2 * a ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ha.1], ha'⟩
          have h2c : 2 * c ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hc.1], hc'⟩
          have h := hα_inj h2a h2c hac
          linarith
        · rw [if_pos ha', if_neg hc'] at hac
          have h2a : 2 * a ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ha.1], ha'⟩
          have h2a1 : 2 * a = 1 := huniq (2 * a) h2a (by rw [hac]; exact hKσ (2 * c - 1))
          have hc'' : 1 < 2 * c := lt_of_not_ge hc'
          have h2c1 : 2 * c - 1 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hc.2]⟩
          have hσ_eq : b.c.symm (v + clamp (2 * c - 1) • (v' - v)) =
              b.c.symm (v + clamp 0 • (v' - v)) := by
            rw [← hac, h2a1, one_mul, ← hpv]
            simp
          have h := b.seg_injOn hv hv' hvv' h2c1 (by norm_num) hσ_eq
          linarith
      · by_cases hc' : 2 * c ≤ 1
        · rw [if_neg ha', if_pos hc'] at hac
          have ha'' : 1 < 2 * a := lt_of_not_ge ha'
          have h2a1 : 2 * a - 1 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ha.2]⟩
          have h2c : 2 * c ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hc.1], hc'⟩
          have h2c1 : 2 * c = 1 := huniq (2 * c) h2c (by rw [← hac]; exact hKσ (2 * a - 1))
          have hσ_eq : b.c.symm (v + clamp (2 * a - 1) • (v' - v)) =
              b.c.symm (v + clamp 0 • (v' - v)) := by
            rw [hac, h2c1, one_mul, ← hpv]
            simp
          have h := b.seg_injOn hv hv' hvv' h2a1 (by norm_num) hσ_eq
          linarith
        · rw [if_neg ha', if_neg hc'] at hac
          have ha'' : 1 < 2 * a := lt_of_not_ge ha'
          have hc'' : 1 < 2 * c := lt_of_not_ge hc'
          have h2a1 : 2 * a - 1 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ha.2]⟩
          have h2c1 : 2 * c - 1 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hc.2]⟩
          have h := b.seg_injOn hv hv' hvv' h2a1 h2c1 hac
          linarith
    exact Or.inr ⟨F, hF_cont, hF_inj, hF_zero, hF_one, hF_img⟩

end ChartBall

/-- Around every point of an open set there is a chart ball contained in the open set. -/
lemma exists_chartBall {W : Set M} (hW : IsOpen W) {z : M} (hz : z ∈ W) :
    Nonempty (ChartBall n M W z) := by
  let c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) z
  have hzsrc : z ∈ c.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) z
  have hmem : W ∩ c.source ∈ 𝓝 z :=
    Filter.inter_mem (hW.mem_nhds hz) (c.open_source.mem_nhds hzsrc)
  obtain ⟨ρ, hρ, hρball⟩ := Metric.mem_nhds_iff.mp (c.image_mem_nhds hzsrc hmem)
  have hlt : ρ / 2 < ρ := by linarith
  refine ⟨⟨c, ρ / 2, by linarith, hzsrc, Subset.trans (Metric.closedBall_subset_ball hlt) ?_,
    ?_⟩⟩
  · intro v hv
    obtain ⟨w, hw, hwv⟩ := hρball hv
    rw [← hwv]
    exact c.map_source hw.2
  · intro v hv
    obtain ⟨w, hw, hwv⟩ := hρball (Metric.closedBall_subset_ball hlt hv)
    rw [← hwv, c.left_inv hw.2]
    exact hw.1

/-- The set of points reachable from `x` by an arc inside `W` is open. -/
lemma isOpen_reached {W : Set M} {x : M} (hx : x ∈ W)
    (hball : ∀ z : M, z ∈ W → Nonempty (ChartBall n M W z)) : IsOpen (Reached W x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  by_cases hyx : y = x
  · rw [hyx]
    obtain ⟨b⟩ := hball x hx
    exact Filter.mem_of_superset (b.ballImage_open.mem_nhds b.self_mem_ballImage)
      (Subset.trans b.ballImage_subset_K (b.reached_of_mem_self b.self_mem_K))
  · rcases (show y = x ∨ ∃ γ : ℝ → M, IsArcTo W x y γ from hy) with h | ⟨γ, hγ⟩
    · exact absurd h hyx
    · have hyW : y ∈ W := hγ.2.2.2.1 ▸ hγ.2.2.2.2 1 (by norm_num)
      obtain ⟨b⟩ := hball y hyW
      exact Filter.mem_of_superset (b.ballImage_open.mem_nhds b.self_mem_ballImage)
        (Subset.trans b.ballImage_subset_K (b.reached_of_mem hγ b.self_mem_K))

/-- The set of points reachable from `x` by an arc inside `W` is closed in `W`. -/
lemma closure_reached_subset {W : Set M} {x : M}
    (hball : ∀ z : M, z ∈ W → Nonempty (ChartBall n M W z)) :
    closure (Reached W x) ∩ W ⊆ Reached W x := by
  rintro z ⟨hzcl, hzW⟩
  rcases eq_or_ne z x with rfl | hzx
  · exact Or.inl rfl
  · obtain ⟨b⟩ := hball z hzW
    by_cases hxK : x ∈ b.K
    · exact b.reached_of_mem_self hxK z b.self_mem_K
    · have hne : (b.c.symm '' Metric.ball (b.c z) b.ρ ∩ Reached W x).Nonempty :=
        (mem_closure_iff_nhds.mp hzcl) _ (b.ballImage_open.mem_nhds b.self_mem_ballImage)
      obtain ⟨w, hwV, hwR⟩ := hne
      have hwK : w ∈ b.K := b.ballImage_subset_K hwV
      have hwx : w ≠ x := fun h => hxK (h ▸ hwK)
      rcases (show w = x ∨ ∃ γ : ℝ → M, IsArcTo W x w γ from hwR) with h | ⟨γ, hγ⟩
      · exact absurd h hwx
      · exact b.reached_of_mem hγ hwK z b.self_mem_K

end Reach

end Helpers

theorem exists_arc_of_isPathConnected {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {W : Set M} (hW : IsOpen W) (hWc : IsPathConnected W) {x y : M} (hx : x ∈ W) (hy : y ∈ W)
    (hxy : x ≠ y) :
    ∃ γ : ℝ → M, Continuous γ ∧ Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧ γ 0 = x ∧ γ 1 = y ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ W := by
  have hsub : W ⊆ Reached W x :=
    hWc.isConnected.isPreconnected.subset_of_closure_inter_subset
      (isOpen_reached (n := n) (M := M) hx (fun z hz => exists_chartBall (n := n) (M := M) hW hz))
      ⟨x, hx, Or.inl rfl⟩
      (closure_reached_subset (n := n) (M := M)
        (fun z hz => exists_chartBall (n := n) (M := M) hW hz))
  rcases (show y = x ∨ ∃ γ : ℝ → M, IsArcTo W x y γ from hsub hy) with h | ⟨γ, hγ⟩
  · exact absurd h.symm hxy
  · exact ⟨γ, hγ⟩

end Work.Whitney.PathTools
