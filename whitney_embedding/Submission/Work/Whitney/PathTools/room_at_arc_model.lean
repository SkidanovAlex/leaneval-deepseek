import Mathlib
import Submission.Work.Whitney.PathTools.isPathConnected_compl_finite
import Submission.Work.Whitney.PathTools.isPreconnected_sdiff_of_local_room
import Submission.Work.Whitney.PathTools.local_room_compact_arc_like

/-!
# Room around an arc (the Euclidean model)

We prove `Work.Whitney.PathTools.room_at_arc_model`.
-/

open Set Metric Topology

namespace Work.Whitney.PathTools

set_option maxHeartbeats 800000

variable {E : Type*}

/-- **No continuous injection of a `> 1`-dimensional ball into `ℝ`.** -/
lemma no_contInj_ball_to_real [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hrank : 1 < Module.rank ℝ E) (f : E → ℝ)
    (hfcont : ContinuousOn f (Metric.ball (0:E) 1))
    (hfinj : Set.InjOn f (Metric.ball (0:E) 1)) : False := by
  have hnt : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans hrank)
  obtain ⟨v, hv⟩ : ∃ v : E, v ≠ 0 := by
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    exact ⟨a - b, sub_ne_zero.mpr hab⟩
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    rw [show u = ‖v‖⁻¹ • v from rfl, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hu_ne : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  have hp0 : (0:E) ∈ Metric.ball (0:E) 1 := by simp
  have hp1 : (2:ℝ)⁻¹ • u ∈ Metric.ball (0:E) 1 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul, hu, mul_one,
      Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    norm_num
  have hp_ne : (0:E) ≠ (2:ℝ)⁻¹ • u := by
    intro h
    have h2 : (2:ℝ)⁻¹ • u = 0 := h.symm
    rcases smul_eq_zero.mp h2 with h3 | h3
    · norm_num at h3
    · exact hu_ne h3
  set S : Set ℝ := f '' Metric.ball (0:E) 1 with hSdef
  have hSpre : IsPreconnected S := isPreconnected_ball.image f hfcont
  have hSoc : S.OrdConnected := hSpre.ordConnected
  have hx0 : f 0 ∈ S := ⟨0, hp0, rfl⟩
  have hx1 : f ((2:ℝ)⁻¹ • u) ∈ S := ⟨_, hp1, rfl⟩
  have hxne : f 0 ≠ f ((2:ℝ)⁻¹ • u) := fun h => hp_ne (hfinj hp0 hp1 h)
  have key : ∀ lo hi : ℝ, lo ∈ S → hi ∈ S → lo < hi → False := by
    intro lo hi hlo hhi hlt
    set m : ℝ := (lo+hi)/2 with hm
    have hm_mem : m ∈ S := hSoc.out hlo hhi (by
      simp only [hm, Set.mem_Icc]; constructor <;> linarith)
    obtain ⟨z, hz_ball, hz⟩ := hm_mem
    have hdz : dist z 0 < 1 := by rwa [Metric.mem_ball] at hz_ball
    have hball_diff : IsPreconnected (Metric.ball (0:E) 1 \ {z}) := by
      refine isPreconnected_diff_singleton (isPreconnected_ball (x := (0:E)) (r := 1))
        Metric.isOpen_ball isClosed_singleton (V := Metric.ball z ((1 - dist z 0)/2))
        Metric.isOpen_ball (Metric.mem_ball_self (by linarith)) ?_
        (isPreconnected_ball_diff_singleton hrank z (r := (1 - dist z 0)/2))
      intro x hx
      rw [Metric.mem_ball] at hx ⊢
      calc dist x 0 ≤ dist x z + dist z 0 := dist_triangle _ _ _
        _ < (1 - dist z 0)/2 + dist z 0 := by linarith
        _ ≤ 1 := by linarith
    have heq : S \ {m} = f '' (Metric.ball (0:E) 1 \ {z}) := by
      ext x
      constructor
      · rintro ⟨hxS, hxm⟩
        obtain ⟨w, hw, hwx⟩ := hxS
        refine ⟨w, ⟨hw, ?_⟩, hwx⟩
        intro hwz
        have hwzeq : w = z := Set.mem_singleton_iff.mp hwz
        exact hxm (Set.mem_singleton_iff.mpr (by rw [← hwx, hwzeq, hz]))
      · rintro ⟨w, ⟨hw, hwz⟩, hwx⟩
        refine ⟨⟨w, hw, hwx⟩, ?_⟩
        intro hxm
        have hxmeq : x = m := Set.mem_singleton_iff.mp hxm
        have hwzeq : w = z := hfinj hw hz_ball (by rw [hwx, hxmeq, hz])
        exact hwz (Set.mem_singleton_iff.mpr hwzeq)
    have hnotpre : ¬ IsPreconnected (S \ {m}) := by
      intro hpre
      have hoc := hpre.ordConnected
      have hlom : lo ≠ m := by simp only [hm]; linarith
      have him : hi ≠ m := by simp only [hm]; linarith
      have h1 : lo ∈ S \ {m} := ⟨hlo, by simpa [Set.mem_singleton_iff] using hlom⟩
      have h2 : hi ∈ S \ {m} := ⟨hhi, by simpa [Set.mem_singleton_iff] using him⟩
      have h3 : m ∈ S \ {m} := hoc.out h1 h2 (by
        simp only [hm, Set.mem_Icc]; constructor <;> linarith)
      exact h3.2 (by simp)
    rw [heq] at hnotpre
    refine hnotpre (hball_diff.image f (hfcont.mono Set.sdiff_subset))
  rcases lt_or_gt_of_ne hxne with h | h
  · exact key _ _ hx0 hx1 h
  · exact key _ _ hx1 hx0 h

theorem room_at_arc_model {n : ℕ} (hn : 3 ≤ n) {K : Set ℝ} (hK : IsCompact K)
    {h : ℝ → EuclideanSpace ℝ (Fin n)} (hh : ContinuousOn h K) (hinj : Set.InjOn h K)
    {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ h '' K) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ IsPathConnected (Metric.ball p r \ h '' K) := by
  have hKc : IsCompact (h '' K) := hK.image_of_continuousOn hh
  set r : ℝ := min ε 1 / 2 with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    have h1 : 0 < min ε 1 := lt_min hε one_pos
    linarith
  have hrlt : r < ε := by
    rw [hrdef]
    have h1 : min ε 1 ≤ ε := min_le_left _ _
    linarith
  refine ⟨r, hrpos, hrlt, ?_⟩
  have hpre : IsPreconnected (Metric.ball p r \ h '' K) :=
    isPreconnected_sdiff_of_local_room (isPreconnected_ball (x := p) (r := r))
      Metric.isOpen_ball hKc.isClosed
      (fun y hy N hN => local_room_compact_arc_like hn hK hh hinj hy hN)
  have hne : (Metric.ball p r \ h '' K).Nonempty := by
    obtain ⟨O, _hOo, _hyO, hOsub, hOne, _hOpre⟩ :=
      local_room_compact_arc_like hn hK hh hinj hp
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrpos))
    exact hOne.mono fun x hx => ⟨hOsub hx.1, hx.2⟩
  have hopen : IsOpen (Metric.ball p r \ h '' K) := Metric.isOpen_ball.sdiff hKc.isClosed
  exact (hopen.isConnected_iff_isPathConnected).mp ⟨hne, hpre⟩

end Work.Whitney.PathTools
