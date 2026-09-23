import Mathlib
import Submission.Work.OddBound.design.MountainPass
import Submission.Work.OddBound.mountainPass.isConnected_iInter_of_antitone
import Submission.Work.OddBound.mountainPass.exists_sublevel_near_of_negDefPlane
import Submission.Work.OddBound.mountainPass.local_joinedIn_of_negDefPlane
import Submission.Work.OddBound.mountainPass.local_joinedIn_of_fderiv_ne_zero

namespace Work.OddBound.mountainPass

open scoped ContDiff
open Set

/-- `z` is a *bad* point for the index bound: the second derivative at `z` is negative definite on
a two-dimensional plane. -/
def IsBad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (z : E) : Prop :=
  ∃ v w : E, ∀ c d : ℝ, (c, d) ≠ 0 →
    (fderiv ℝ (fderiv ℝ f) z) (c • v + d • w) (c • v + d • w) < 0

/-! ## Local structure lemmas (delegated to colleagues) -/

/-- **Mountain-pass with the index bound.**  For a `C²` function on a finite-dimensional real
inner product space all of whose sublevel sets are compact, the minimax level of the family of
paths joining two strictly lower points is attained at a critical point at which the second
derivative is *not* negative definite on any two-dimensional subspace. -/
theorem exists_critical_index_le_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hcomp : ∀ c : ℝ, IsCompact {x : E | f x ≤ c})
    {a b : E}
    (hpath : ∃ σ : ℝ → E, ContinuousOn σ (Set.Icc (0 : ℝ) 1) ∧ σ 0 = a ∧ σ 1 = b)
    {Λ : ℝ}
    (hΛ : Λ = sInf {m : ℝ | ∃ σ : ℝ → E, ContinuousOn σ (Set.Icc (0 : ℝ) 1) ∧
      σ 0 = a ∧ σ 1 = b ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, f (σ t) ≤ m})
    (hlt : max (f a) (f b) < Λ) :
    ∃ p : E, f p = Λ ∧ fderiv ℝ f p = 0 ∧
      ∀ v w : E, ∃ c d : ℝ, (c, d) ≠ 0 ∧
        0 ≤ (fderiv ℝ (fderiv ℝ f) p) (c • v + d • w) (c • v + d • w) := by
  classical
  -- ## Step 1: the competitor set and basic order facts
  set S : Set ℝ := {m : ℝ | ∃ σ : ℝ → E, ContinuousOn σ (Icc (0 : ℝ) 1) ∧ σ 0 = a ∧ σ 1 = b ∧
      ∀ t ∈ Icc (0 : ℝ) 1, f (σ t) ≤ m} with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨σ, hσc, hσ0, hσ1⟩ := hpath
    obtain ⟨t₀, ht₀, htmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
      ⟨0, left_mem_Icc.mpr zero_le_one⟩ (hf.continuous.comp_continuousOn hσc)
    exact ⟨f (σ t₀), σ, hσc, hσ0, hσ1, fun t ht => htmax ht⟩
  have hSle_a : ∀ m ∈ S, f a ≤ m := by
    intro m hm
    obtain ⟨σ, _, h0, _, hle⟩ := hm
    rw [← h0]
    exact hle 0 (left_mem_Icc.mpr zero_le_one)
  have hbdd : BddBelow S := ⟨f a, hSle_a⟩
  have hfa : f a ≤ Λ := by rw [hΛ]; exact le_csInf hSne hSle_a
  have hfb : f b ≤ Λ := by
    rw [hΛ]
    refine le_csInf hSne fun m hm => ?_
    obtain ⟨σ, _, _, h1, hle⟩ := hm
    rw [← h1]
    exact hle 1 (right_mem_Icc.mpr zero_le_one)
  have hfa' : f a < Λ := lt_of_le_of_lt (le_max_left _ _) hlt
  have hfb' : f b < Λ := lt_of_le_of_lt (le_max_right _ _) hlt
  -- every level strictly above `Λ` is a competitor
  have hmemS_of_gt : ∀ {c : ℝ}, Λ < c → c ∈ S := by
    intro c hc
    obtain ⟨m, hmS, hmc⟩ := (csInf_lt_iff hbdd hSne).mp (by rw [← hΛ]; exact hc)
    obtain ⟨σ, hσc, hσ0, hσ1, hle⟩ := hmS
    exact ⟨σ, hσc, hσ0, hσ1, fun t ht => le_trans (hle t ht) hmc.le⟩
  -- ## Step 2: `a` and `b` are not joined inside the strict sublevel set
  set U : Set E := {x : E | f x < Λ} with hUdef
  have hUopen : IsOpen U := isOpen_lt hf.continuous continuous_const
  have hnotJoined : ¬ JoinedIn U a b := by
    rintro ⟨γ, hγ⟩
    let σ : ℝ → E := fun t => γ (Set.projIcc 0 1 zero_le_one t)
    have hσc : ContinuousOn σ (Icc (0 : ℝ) 1) :=
      (γ.continuous.comp continuous_projIcc).continuousOn
    have hσ0 : σ 0 = a := by
      simp only [σ, Set.projIcc_left]
      exact γ.source
    have hσ1 : σ 1 = b := by
      simp only [σ, Set.projIcc_right]
      exact γ.target
    obtain ⟨t₀, ht₀, htmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
      ⟨0, left_mem_Icc.mpr zero_le_one⟩ (hf.continuous.comp_continuousOn hσc)
    have hmS : f (σ t₀) ∈ S := ⟨σ, hσc, hσ0, hσ1, fun t ht => htmax ht⟩
    have hmlt : f (σ t₀) < Λ := hγ (Set.projIcc 0 1 zero_le_one t₀)
    have hle := csInf_le hbdd hmS
    rw [← hΛ] at hle
    linarith
  -- ## Step 3: the nested sublevel components and their intersection `Z`
  let lev : ℕ → Set E := fun n => {x : E | f x ≤ Λ + 1 / ((n : ℝ) + 1)}
  have hlev_comp : ∀ n, IsCompact (lev n) := fun n => hcomp _
  have hlev_closed : ∀ n, IsClosed (lev n) := fun n =>
    isClosed_le hf.continuous continuous_const
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hmem_lev : ∀ n, a ∈ lev n := fun n => by
    simp only [lev, mem_ofPred_eq]
    linarith [hfa', hpos n]
  have hlev_mono : ∀ n, lev (n + 1) ⊆ lev n := by
    intro n x hx
    simp only [lev, mem_ofPred_eq] at hx ⊢
    have h2 : (1 : ℝ) / ((n : ℝ) + 1 + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le <;> push_cast <;> linarith
    have hx' : f x ≤ Λ + 1 / ((n : ℝ) + 1 + 1) := by push_cast at hx ⊢; exact hx
    linarith
  let comp : ℕ → Set E := fun n => connectedComponentIn (lev n) a
  have hcomp_sub : ∀ n, comp n ⊆ lev n := fun n => connectedComponentIn_subset _ _
  have hcomp_ne : ∀ n, (comp n).Nonempty := fun n =>
    connectedComponentIn_nonempty_iff.mpr (hmem_lev n)
  have hcomp_conn : ∀ n, IsConnected (comp n) := fun n =>
    ⟨hcomp_ne n, isPreconnected_connectedComponentIn⟩
  have hcomp_closed : ∀ n, IsClosed (comp n) := by
    intro n
    rw [← closure_subset_iff_isClosed]
    refine IsPreconnected.subset_connectedComponentIn
      isPreconnected_connectedComponentIn.closure ?_ ?_
    · exact subset_closure (mem_connectedComponentIn (hmem_lev n))
    · calc closure (comp n) ⊆ closure (lev n) := closure_mono (hcomp_sub n)
        _ = lev n := (hlev_closed n).closure_eq
  have hcomp_compact : ∀ n, IsCompact (comp n) := fun n =>
    IsCompact.of_isClosed_subset (hlev_comp n) (hcomp_closed n) (hcomp_sub n)
  have hcomp_mono : ∀ n, comp (n + 1) ⊆ comp n := fun n =>
    IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_connectedComponentIn (hmem_lev (n + 1))) ((hcomp_sub (n + 1)).trans (hlev_mono n))
  set Z : Set E := ⋂ n, comp n with hZdef
  have hZconn : IsConnected Z := isConnected_iInter_of_antitone hcomp_compact hcomp_conn hcomp_mono
  have haZ : a ∈ Z := mem_iInter.mpr fun n => mem_connectedComponentIn (hmem_lev n)
  have hbZ : b ∈ Z := by
    refine mem_iInter.mpr fun n => ?_
    have hltn : Λ < Λ + 1 / ((n : ℝ) + 1) := by linarith [hpos n]
    obtain ⟨σ, hσc, hσ0, hσ1, hle⟩ := hmemS_of_gt hltn
    have hpre : IsPreconnected (σ '' Icc (0 : ℝ) 1) := isPreconnected_Icc.image σ hσc
    have hain : a ∈ σ '' Icc (0 : ℝ) 1 := ⟨0, left_mem_Icc.mpr zero_le_one, hσ0⟩
    have hbin : b ∈ σ '' Icc (0 : ℝ) 1 := ⟨1, right_mem_Icc.mpr zero_le_one, hσ1⟩
    have hsub : σ '' Icc (0 : ℝ) 1 ⊆ lev n := by
      rintro y ⟨t, ht, rfl⟩
      simp only [lev, mem_ofPred_eq]
      exact hle t ht
    exact IsPreconnected.subset_connectedComponentIn hpre hain hsub hbin
  have hZle : Z ⊆ {x : E | f x ≤ Λ} := by
    intro z hz
    simp only [mem_setOf_eq]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have hzcomp : z ∈ comp n := mem_iInter.mp hz n
    have h1 : f z ≤ Λ + 1 / ((n : ℝ) + 1) := by
      have := hcomp_sub n hzcomp
      simpa only [lev, mem_setOf_eq] using this
    linarith
  -- ## Step 4: the final argument
  by_contra hcon
  -- `hcon` negated is the negation of the conclusion
  have hall : ∀ p : E, f p = Λ → fderiv ℝ f p = 0 → IsBad f p := by
    intro p hp hdp
    by_contra hnb
    apply hcon
    refine ⟨p, hp, hdp, fun v w => ?_⟩
    by_contra h
    push_neg at h
    exact hnb ⟨v, w, h⟩
  let Comp : E → Set E := fun x => {y : E | JoinedIn U x y}
  have hComp_sub_U : ∀ x : E, Comp x ⊆ U := by
    intro x y hy
    obtain ⟨γ, hγ⟩ := hy
    rw [← γ.target]
    exact hγ 1
  have hComp_open : ∀ x ∈ U, IsOpen (Comp x) := by
    intro x hx
    refine Metric.isOpen_iff.mpr fun y hy => ?_
    have hyU : y ∈ U := by
      obtain ⟨γ, hγ⟩ := hy
      rw [← γ.target]
      exact hγ 1
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen y hyU
    refine ⟨ε, hε, fun y' hy' => ?_⟩
    have hjoin : JoinedIn (Metric.ball y ε) y y' :=
      ((convex_ball y ε).isPathConnected ⟨y, Metric.mem_ball_self hε⟩).joinedIn
        y (Metric.mem_ball_self hε) y' hy'
    exact JoinedIn.trans hy (JoinedIn.mono hjoin hball)
  -- (A) every point of `Z` lies in the closure of `U`
  have hZclU : Z ⊆ closure U := by
    intro z hz
    by_contra hzc
    obtain ⟨ε, hε, hεz⟩ : ∃ ε > 0, ∀ b : E, b ∈ U → ε ≤ dist z b := by
      rw [Metric.mem_closure_iff] at hzc
      push_neg at hzc
      exact hzc
    have hzge : Λ ≤ f z := by
      by_contra hconz
      push_neg at hconz
      have hzU : f z < Λ := hconz
      have := hεz z hzU
      rw [dist_self] at this
      linarith
    have hzeq : f z = Λ := le_antisymm (hZle hz) hzge
    have hmin : IsLocalMin f z := by
      rw [IsLocalMin]
      refine Filter.Eventually.mono (Metric.ball_mem_nhds z hε) fun y hy => ?_
      by_contra hconz
      push_neg at hconz
      have hyU : f y < Λ := by rw [← hzeq]; exact hconz
      have h1 := hεz y hyU
      rw [dist_comm] at h1
      linarith
    have hdz : fderiv ℝ f z = 0 := hmin.fderiv_eq_zero
    have hbad : IsBad f z := hall z hzeq hdz
    obtain ⟨x, hxdist, hxsub⟩ := exists_sublevel_near_of_negDefPlane hf hzeq hdz hbad ε hε
    have hxU : x ∈ U := hxsub
    have := hεz x hxU
    rw [dist_comm] at this
    linarith
  -- (B) local connectedness of the strict sublevel set near points of `Z`
  have hLocal : ∀ z ∈ Z, ∃ ρ > 0, ∀ x y : E,
      dist x z < ρ → dist y z < ρ → f x < Λ → f y < Λ → JoinedIn U x y := by
    intro z hz
    have hzle : f z ≤ Λ := hZle hz
    rcases lt_or_eq_of_le hzle with hlt' | heq
    · have hzU : z ∈ U := hlt'
      obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp (hComp_open z hzU) z (JoinedIn.refl hzU)
      refine ⟨ρ, hρ, fun x y hdx hdy hx hy => ?_⟩
      have hx' : x ∈ Comp z := hsub (by rw [Metric.mem_ball]; exact hdx)
      have hy' : y ∈ Comp z := hsub (by rw [Metric.mem_ball]; exact hdy)
      exact JoinedIn.trans (JoinedIn.symm hx') hy'
    · by_cases hgrad : fderiv ℝ f z = 0
      · exact local_joinedIn_of_negDefPlane hf heq hgrad (hall z heq hgrad)
      · exact local_joinedIn_of_fderiv_ne_zero (hf.of_le (by norm_num)) heq hgrad
  -- (C) the minimal closed separation
  set TA : Set E := closure (Comp a) with hTAdef
  set TB : Set E := closure (U \ Comp a) with hTBdef
  have hZunion : Z ⊆ TA ∪ TB := by
    intro z hz
    have hzcl : z ∈ closure U := hZclU hz
    have hdecomp : U = Comp a ∪ (U \ Comp a) := by
      ext y
      constructor
      · intro hy
        by_cases h : y ∈ Comp a
        · exact Or.inl h
        · exact Or.inr ⟨hy, h⟩
      · rintro (h | h)
        · exact hComp_sub_U a h
        · exact h.1
    rw [hdecomp, closure_union] at hzcl
    exact hzcl
  have hZdisj : Z ∩ (TA ∩ TB) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨z, hzZ, hzTA, hzTB⟩
    obtain ⟨ρ, hρ, hloc⟩ := hLocal z hzZ
    obtain ⟨x₁, hx1c, hx1d⟩ : ∃ x₁ ∈ Comp a, dist z x₁ < ρ := by
      rw [Metric.mem_closure_iff] at hzTA
      exact hzTA ρ hρ
    obtain ⟨x₂, hx2c, hx2d⟩ : ∃ x₂ ∈ U \ Comp a, dist z x₂ < ρ := by
      rw [Metric.mem_closure_iff] at hzTB
      exact hzTB ρ hρ
    have hjoin := hloc x₁ x₂ (by rw [dist_comm]; exact hx1d) (by rw [dist_comm]; exact hx2d)
      (hComp_sub_U a hx1c) hx2c.1
    exact hx2c.2 (JoinedIn.trans hx1c hjoin)
  -- the dichotomy
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hZconn.2) TA TB
      isClosed_closure isClosed_closure hZunion hZdisj with hTA | hTB
  · have hbTB : b ∈ TB := subset_closure ⟨hfb', hnotJoined⟩
    have hbTA : b ∈ TA := hTA hbZ
    have hmem : b ∈ Z ∩ (TA ∩ TB) := ⟨hbZ, hbTA, hbTB⟩
    rw [hZdisj] at hmem
    exact hmem
  · have haTA : a ∈ TA := subset_closure (JoinedIn.refl hfa')
    have haTB : a ∈ TB := hTB haZ
    have hmem : a ∈ Z ∩ (TA ∩ TB) := ⟨haZ, haTA, haTB⟩
    rw [hZdisj] at hmem
    exact hmem

end Work.OddBound.mountainPass
