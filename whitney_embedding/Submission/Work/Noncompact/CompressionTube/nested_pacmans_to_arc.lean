import Mathlib
import Submission.Work.Whitney.PathTools.path_to_arc

/-!
# From a nested sequence of path-connected "pacmans" shrinking to `0` to an arc

`Work.Noncompact.CompressionTube.nested_pacmans_to_arc`: if `V 0 ⊇ V 1 ⊇ ⋯` are path-connected
sets avoiding a set `K ∋ 0`, contained in `ball 0 (r n)` with `r n → 0`, then there is an injective
arc from `0` into `ball 0 ε` avoiding `K` (except at time `0`).

The construction (following the workspace's `Whitney/PathTools/nested_pacmans_to_arc.lean`) picks
`z n ∈ V n`, glues paths `z n → z (n+1)` inside `V n` into a path `F` on `[0,∞)` with
`F s ∈ V ⌊s⌋₊`, reparametrises to `G s = F (1/s)` for `s > 0`, `G s = 0` for `s ≤ 0` (so
`G 0 = 0` and `G` is continuous by `r n → 0`), and extracts an injective arc inside `G`'s image
with `Work.Whitney.PathTools.exists_arc_of_path`.
-/

namespace Work.Noncompact.CompressionTube

open Set Metric Filter
open scoped Topology

theorem nested_pacmans_to_arc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {ε : ℝ} (hε : 0 < ε) (h0K : (0:E) ∈ K) (V : ℕ → Set E) (r : ℕ → ℝ)
    (hopen : ∀ n, IsOpen (V n)) (hpath : ∀ n, IsPathConnected (V n))
    (hsub : ∀ n, V n ⊆ Kᶜ) (hballε : ∀ n, V n ⊆ Metric.ball (0:E) ε)
    (hball : ∀ n, V n ⊆ Metric.ball (0:E) (r n))
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hcl : ∀ n, (0:E) ∈ closure (V n)) (hmono : ∀ n, V (n+1) ⊆ V n) :
    ∃ v : ℝ → E, Continuous v ∧ Set.InjOn v (Set.Icc (0:ℝ) 1) ∧ v 0 = 0 ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, v t ∈ Metric.ball (0:E) ε) ∧
      ∀ t ∈ Set.Ioc (0:ℝ) 1, v t ∉ K := by
  classical
  have hne : ∀ n, (V n).Nonempty := fun n => (hpath n).nonempty
  choose z hz using hne
  have hzK : ∀ n, z n ∉ K := fun n => hsub n (hz n)
  have hz0 : ∀ n, z n ≠ 0 := fun n h => hzK n (by rw [h]; exact h0K)
  have hex : ∀ n, ∃ γp : Path (z n) (z (n+1)), ∀ t, γp t ∈ V n := fun n =>
    (hpath n).joinedIn (z n) (hz n) (z (n+1)) (hmono n (hz (n+1)))
  choose p hp using hex
  let q : ℕ → ℝ → E := fun n u => p n (Set.projIcc 0 1 (zero_le_one : (0:ℝ) ≤ 1) u)
  let F : ℝ → E := fun s => q ⌊s⌋₊ (s - (⌊s⌋₊ : ℝ))
  have hF_mem : ∀ s, 0 ≤ s → F s ∈ V ⌊s⌋₊ := fun s _ => hp ⌊s⌋₊ _
  have hF_norm : ∀ s, 0 ≤ s → ‖F s‖ < r ⌊s⌋₊ := fun s hs => by
    simpa only [Metric.mem_ball, dist_zero_right] using hball ⌊s⌋₊ (hF_mem s hs)
  have hF_normK : ∀ s, 0 ≤ s → F s ∉ K := fun s hs => hsub ⌊s⌋₊ (hF_mem s hs)
  have hF_ballε : ∀ s, 0 ≤ s → F s ∈ Metric.ball (0:E) ε :=
    fun s hs => hballε ⌊s⌋₊ (hF_mem s hs)
  have hq_cont : ∀ n, Continuous (q n) := fun n => (p n).continuous.comp continuous_projIcc
  have hq0 : ∀ n, q n 0 = z n := by
    intro n
    show p n (Set.projIcc 0 1 (zero_le_one : (0:ℝ) ≤ 1) 0) = z n
    rw [Set.projIcc_of_mem zero_le_one (by norm_num : (0:ℝ) ∈ Set.Icc 0 1)]
    exact Path.source (p n)
  have hq1 : ∀ n, q n 1 = z (n+1) := by
    intro n
    show p n (Set.projIcc 0 1 (zero_le_one : (0:ℝ) ≤ 1) 1) = z (n+1)
    rw [Set.projIcc_of_mem zero_le_one (by norm_num : (1:ℝ) ∈ Set.Icc 0 1)]
    exact Path.target (p n)
  have hagree : ∀ n, Set.EqOn F (fun s : ℝ => q n (s - (n:ℝ))) (Set.Icc (n:ℝ) ((n:ℝ)+1)) := by
    intro n s hs
    rcases eq_or_lt_of_le hs.2 with h | h
    · rw [h]
      show q ⌊((n:ℝ)+1)⌋₊ (((n:ℝ)+1) - (⌊((n:ℝ)+1)⌋₊ : ℝ)) = q n (((n:ℝ)+1) - (n:ℝ))
      have h1 : ⌊((n:ℝ)+1)⌋₊ = n+1 := by
        rw [show ((n:ℝ)+1) = ((n+1 : ℕ) : ℝ) by push_cast; ring]
        exact Nat.floor_natCast (n+1)
      rw [h1]
      have h2 : ((n:ℝ)+1) - (((n+1:ℕ)) : ℝ) = 0 := by push_cast; ring
      rw [h2, hq0]
      have h3 : ((n:ℝ)+1) - (n:ℝ) = 1 := by ring
      rw [h3, hq1]
    · have hidx : ⌊s⌋₊ = n := Nat.floor_eq_on_Ico n s ⟨hs.1, h⟩
      show q ⌊s⌋₊ (s - (⌊s⌋₊ : ℝ)) = q n (s - (n:ℝ))
      rw [hidx]
  have hcont_Icc : ∀ n : ℕ, ContinuousOn F (Set.Icc (n:ℝ) ((n:ℝ)+1)) := fun n =>
    ((hq_cont n).comp (continuous_id.sub continuous_const)).continuousOn.congr (hagree n)
  have hcont_0N : ∀ N : ℕ, ContinuousOn F (Set.Icc (0:ℝ) (N:ℝ)) := by
    intro N
    induction N with
    | zero =>
      rw [Nat.cast_zero, Set.Icc_self]
      exact continuousOn_singleton F 0
    | succ N ih =>
      have h2 : ContinuousOn F (Set.Icc (N:ℝ) ((N:ℝ)+1)) := hcont_Icc N
      have h3 : ContinuousOn F (Set.Icc (0:ℝ) (N:ℝ) ∪ Set.Icc (N:ℝ) ((N:ℝ)+1)) :=
        ih.union_of_isClosed h2 isClosed_Icc isClosed_Icc
      have hun : Set.Icc (0:ℝ) (N:ℝ) ∪ Set.Icc (N:ℝ) ((N:ℝ)+1) = Set.Icc (0:ℝ) ((N:ℝ)+1) := by
        ext x
        simp only [Set.mem_union, Set.mem_Icc]
        constructor
        · rintro (⟨h1,h2⟩ | ⟨h1,h2⟩)
          · exact ⟨h1, by linarith⟩
          · exact ⟨by linarith, h2⟩
        · intro ⟨h1,h2⟩
          rcases le_or_gt x (N:ℝ) with h | h
          · exact Or.inl ⟨h1, h⟩
          · exact Or.inr ⟨le_of_lt h, h2⟩
      rw [hun] at h3
      have hcast : ((N:ℝ)+1) = ((N+1 : ℕ) : ℝ) := by push_cast; ring
      rw [← hcast]
      exact h3
  -- `F 1 = z 1` and `F 0 = z 0`
  have hF1 : F 1 = z 1 := by
    show q ⌊(1:ℝ)⌋₊ ((1:ℝ) - (⌊(1:ℝ)⌋₊ : ℝ)) = z 1
    rw [Nat.floor_one]
    norm_num
    exact hq0 1
  have hF0 : F 0 = z 0 := by
    show q ⌊(0:ℝ)⌋₊ ((0:ℝ) - (⌊(0:ℝ)⌋₊ : ℝ)) = z 0
    rw [Nat.floor_zero]
    norm_num
    exact hq0 0
  -- the tail reparametrisation: `G s = F (1/s)` for `s > 0`, `G s = 0` for `s ≤ 0`
  let G : ℝ → E := fun s => if s ≤ 0 then 0 else F (1/s)
  have hG0 : G 0 = 0 := by simp [G]
  have hG1 : G 1 = z 1 := by
    have h1 : ¬ ((1:ℝ) ≤ 0) := by norm_num
    show (if (1:ℝ) ≤ 0 then (0:E) else F (1/1)) = z 1
    rw [if_neg h1, show (1:ℝ)/1 = 1 by norm_num]
    exact hF1
  have hGne : ∀ s : ℝ, G s ≠ 0 → 0 < s := by
    intro s hs
    by_contra h
    exact hs (by simp only [G, if_pos (not_lt.mp h)])
  have hG_ball : ∀ s : ℝ, G s ≠ 0 → G s ∈ Metric.ball (0:E) ε := by
    intro s hs
    have hs0 : 0 < s := hGne s hs
    have h1 : G s = F (1/s) := by simp only [G, if_neg (not_le.mpr hs0)]
    rw [h1]
    exact hF_ballε (1/s) (by positivity)
  have hG_K : ∀ s : ℝ, G s ≠ 0 → G s ∉ K := by
    intro s hs
    have hs0 : 0 < s := hGne s hs
    have h1 : G s = F (1/s) := by simp only [G, if_neg (not_le.mpr hs0)]
    rw [h1]
    exact hF_normK (1/s) (by positivity)
  -- `G 1 ≠ G 0`
  have hG10 : G 0 ≠ G 1 := by
    rw [hG0, hG1]
    exact fun h => hz0 1 h.symm
  -- continuity of `G`
  have hG_cont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro s
    rcases lt_trichotomy s 0 with hs | hs | hs
    · refine ContinuousAt.congr (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:E)) s) ?_
      filter_upwards [isOpen_Iio.mem_nhds hs] with t ht
      have ht' : t ≤ 0 := le_of_lt (Set.mem_Iio.mp ht)
      exact (show G t = 0 from by simp only [G, if_pos ht']).symm
    · subst hs
      rw [ContinuousAt, hG0]
      rw [Metric.tendsto_nhds]
      intro δ hδ
      rw [Metric.tendsto_atTop] at hr
      obtain ⟨N, hN⟩ := hr δ hδ
      refine Filter.mem_of_superset
        (Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0) (by positivity : (0:ℝ) < 1/((N:ℝ)+1))) ?_
      intro t ht
      show dist (G t) 0 < δ
      rw [dist_zero_right]
      rcases le_or_gt t 0 with ht0 | ht0
      · rw [show G t = 0 by simp only [G, if_pos ht0]]
        simpa using hδ
      · have ht1 : t < 1/((N:ℝ)+1) := ht.2
        have hint : t * ((N:ℝ) + 1) ≤ 1 := by
          have hmul := mul_lt_mul_of_pos_right ht1 (by positivity : (0:ℝ) < (N:ℝ) + 1)
          have hcancel : (1 / ((N:ℝ) + 1)) * ((N:ℝ) + 1) = 1 := by field_simp
          linarith [hmul, hcancel]
        have hinv : (N:ℝ) + 1 ≤ 1/t := by
          have htne : t ≠ 0 := ne_of_gt ht0
          rw [le_div_iff₀ ht0]
          linarith [hint, mul_comm t ((N:ℝ) + 1)]
        have hfloor : N ≤ ⌊1/t⌋₊ := by
          have h1 : ⌊((N:ℝ))⌋₊ ≤ ⌊1/t⌋₊ := Nat.floor_mono (by linarith [hinv])
          rwa [Nat.floor_natCast] at h1
        have hlt := hF_norm (1/t) (by positivity)
        have hrδ := hN ⌊1/t⌋₊ hfloor
        rw [Real.dist_eq, sub_zero] at hrδ
        have h2 : r ⌊1/t⌋₊ < δ := lt_of_le_of_lt (le_abs_self _) hrδ
        have h3 : G t = F (1/t) := by simp only [G, if_neg (not_le.mpr ht0)]
        rw [h3]
        exact lt_trans hlt h2
    · have hinv : ContinuousAt (fun t : ℝ => 1/t) s :=
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (1:ℝ)) s).div continuousAt_id (ne_of_gt hs)
      obtain ⟨N, hN⟩ := exists_nat_gt (1/s)
      have hle : (0:ℝ) < 1/s := by positivity
      have hmem : Set.Icc (0:ℝ) (N:ℝ) ∈ nhds (1/s) :=
        Filter.mem_of_superset (Ioo_mem_nhds hle hN)
          (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
      have hF_at : ContinuousAt F (1/s) :=
        (hcont_0N N).continuousAt (s := Set.Icc (0:ℝ) (N:ℝ)) hmem
      refine ContinuousAt.congr (hF_at.comp hinv) ?_
      filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
      have ht' : ¬ (t ≤ 0) := not_le.mpr (Set.mem_Ioi.mp ht)
      show F (1/t) = G t
      simp only [G, if_neg ht']
  -- packaging: extract an injective arc inside the image of `G`
  set f : ℝ → ↥(Set.range G) := fun t => ⟨G t, t, rfl⟩ with hf
  have hf_cont : Continuous f := Continuous.subtype_mk hG_cont fun t => ⟨t, rfl⟩
  have hf_ne : f 0 ≠ f 1 := by
    intro hc
    refine hG10 ?_
    exact congrArg Subtype.val hc
  obtain ⟨γ, hγc, hγinj, hγ0, hγ1⟩ := Work.Whitney.PathTools.exists_arc_of_path hf_cont hf_ne
  have hv0 : (γ 0 : E) = 0 := by
    rw [hγ0]
    exact hG0
  refine ⟨fun t : ℝ => (γ t : E), continuous_subtype_val.comp hγc, ?_, hv0, ?_, ?_⟩
  · intro a ha b hb hab
    exact hγinj ha hb (Subtype.coe_injective hab)
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]
      exact hv0 ▸ Metric.mem_ball_self hε
    · have hne : (γ t : E) ≠ 0 := by
        intro hc
        refine absurd (hγinj ht (by norm_num : (0:ℝ) ∈ Set.Icc 0 1) ?_) (ne_of_gt h)
        refine Subtype.ext ?_
        rw [hγ0, hc]
        simpa [hf] using hG0.symm
      obtain ⟨s, hs⟩ := (γ t).2
      have hne' : G s ≠ 0 := by rw [hs]; exact hne
      change (γ t : E) ∈ Metric.ball (0:E) ε
      rw [← hs]
      exact hG_ball s hne'
  · intro t ht
    have hne : (γ t : E) ≠ 0 := by
      intro hc
      refine absurd (hγinj ⟨le_of_lt ht.1, ht.2⟩ (by norm_num : (0:ℝ) ∈ Set.Icc 0 1) ?_)
        (ne_of_gt ht.1)
      refine Subtype.ext ?_
      rw [hγ0, hc]
      simpa [hf] using hG0.symm
    obtain ⟨s, hs⟩ := (γ t).2
    have hne' : G s ≠ 0 := by rw [hs]; exact hne
    change (γ t : E) ∉ K
    rw [← hs]
    exact hG_K s hne'

end Work.Noncompact.CompressionTube
