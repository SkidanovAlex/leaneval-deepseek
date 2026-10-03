import Mathlib
import Submission.Lib.Unif2.Work.Drive.cBallDefs
import Submission.Lib.Unif2.Work.Drive.isPreconnected_sdiff_finite
import Submission.Lib.Unif2.Work.Topology.Surface.exists_injective_path_in_is_open_connected

/-!
# A fine chain from a point of a cover element to the next one

The lemma `Work.Drive.exists_phase_plan`: inside one coordinate ball `U (v j)` of a cover, with
finitely many points `F` removed, any point `p` can be joined to a point `q` of the *next* cover
element `U (v (j+1))` by an injective path, and this path can be sampled finely enough that
consecutive samples are much closer than the distance from the earlier sample to the boundary of
the model ball.  The result is a `FineChain` from `p` to `q`, as required by the chain construction
of the phase `Θ` of the paper (Hubbard, Chapter 1).

## Contents

* the elementary list bookkeeping `samplePrefix`, `FineChain.append_singleton`,
  `samplePrefix_fineChain` which turns a "locally fine" sampled sequence into a `FineChain`;
* the topological input: a nonempty open subset of a `ℂ`-charted space has points outside any
  finite set (`exists_mem_notMem_of_isOpen`), a coordinate ball is preconnected
  (`isPreconnected_cBall`), and `U (v j) \ F` is therefore an open connected (= arc connected)
  set containing both `p` and a suitable `q`.
-/

open Set Metric
open scoped Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Work.Drive

section Basic

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Every euclidean ball in `ℂ` is infinite. -/
theorem infinite_ball_complex (a : ℂ) {ε : ℝ} (hε : 0 < ε) : (Metric.ball a ε).Infinite := by
  have h1 : (Set.Ioo (0:ℝ) ε).Infinite := Set.Ioo_infinite hε
  have hinj : Set.InjOn (fun t : ℝ => a + (t : ℂ)) (Set.Ioo (0:ℝ) ε) :=
    fun t _ t' _ h => Complex.ofReal_injective (by simpa using h)
  have himg : ((fun t : ℝ => a + (t : ℂ)) '' Set.Ioo (0:ℝ) ε).Infinite :=
    Set.Infinite.image hinj h1
  refine himg.mono ?_
  rintro w ⟨t, ht, rfl⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have hsub : a + (t:ℂ) - a = (t:ℂ) := by ring
  rw [hsub]
  simpa [Complex.normSq_eq_norm_sq, abs_of_pos ht.1] using ht.2

/-- **A nonempty open subset of a `ℂ`-charted space is not contained in a finite set.**  The chart
at a point of the open set maps a neighbourhood of that point onto a euclidean ball, which is
infinite; a finite set cannot exhaust it. -/
theorem exists_mem_notMem_of_isOpen {O : Set X} (hO : IsOpen O) (hOn : O.Nonempty)
    (S : Set X) (hS : S.Finite) : ∃ q ∈ O, q ∉ S := by
  obtain ⟨z, hzO⟩ := hOn
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ z
  have hzsrc : z ∈ c.source := mem_chart_source ℂ z
  have hopen : IsOpen (c '' (c.source ∩ O)) := c.isOpen_image_source_inter hO
  have hmem : c z ∈ c '' (c.source ∩ O) := ⟨z, ⟨hzsrc, hzO⟩, rfl⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen (c z) hmem
  have hinf : (Metric.ball (c z) ε).Infinite := infinite_ball_complex (c z) hε
  obtain ⟨w, hwball, hwS⟩ := (hinf.sdiff (hS.image c)).nonempty
  obtain ⟨y, hyO, hyw⟩ := hεsub hwball
  exact ⟨y, hyO.2, fun hyS => hwS ⟨y, hyS, hyw⟩⟩

/-- **A coordinate ball is the image of the model ball.**  If the closed model ball of radius `r`
lies in the target of the chart `c`, then the `c`-coordinate ball of radius `r` around `x` is the
image of the open model ball under `c.symm`. -/
theorem cBall_eq_image {c : OpenPartialHomeomorph X ℂ} {x : X} {r : ℝ}
    (hroom : Metric.closedBall (c x) r ⊆ c.target) :
    cBall c x r = c.symm '' Metric.ball (c x) r := by
  ext z
  constructor
  · rintro ⟨hzsrc, hzball⟩
    exact ⟨c z, hzball, c.left_inv hzsrc⟩
  · rintro ⟨w, hw, rfl⟩
    have hwt : w ∈ c.target := hroom (Metric.ball_subset_closedBall hw)
    refine ⟨c.map_target hwt, ?_⟩
    rwa [c.right_inv hwt]

/-- **A coordinate ball is preconnected**: it is the continuous image of a euclidean ball. -/
theorem isPreconnected_cBall {c : OpenPartialHomeomorph X ℂ} {x : X} {r : ℝ}
    (hroom : Metric.closedBall (c x) r ⊆ c.target) : IsPreconnected (cBall c x r) := by
  rw [cBall_eq_image hroom]
  exact (Metric.isPreconnected_ball (x := c x) (r := r)).image c.symm
    (c.continuousOn_symm.mono fun w hw => hroom (Metric.ball_subset_closedBall hw))

end Basic

/-! ## Sampling a sequence at the integers -/

section Sampling

variable {X : Type*} [TopologicalSpace X]

/-- The prefix `[a, g 1, g 2, …, g m]` of a sequence sampled at the integers `1, …, m`. -/
def samplePrefix {α : Type*} (a : α) (g : ℕ → α) : ℕ → List α
  | 0 => [a]
  | (m+1) => samplePrefix a g m ++ [g (m+1)]

variable {a : X} {g : ℕ → X}

theorem samplePrefix_zero : samplePrefix a g 0 = [a] := rfl

theorem samplePrefix_succ (m : ℕ) : samplePrefix a g (m+1) = samplePrefix a g m ++ [g (m+1)] :=
  rfl

theorem samplePrefix_head? (m : ℕ) : (samplePrefix a g m).head? = some a := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [samplePrefix_succ]
      simp only [List.head?_append, ih]
      rfl

theorem samplePrefix_getLast? (m : ℕ) : (samplePrefix a g (m+1)).getLast? = some (g (m+1)) := by
  rw [samplePrefix_succ]
  exact List.getLast?_concat

theorem samplePrefix_mem {y : X} {m : ℕ} (hy : y ∈ samplePrefix a g m) :
    y = a ∨ ∃ k, k ≤ m ∧ y = g k := by
  induction m with
  | zero => exact Or.inl (by simpa [samplePrefix_zero] using hy)
  | succ m ih =>
      rw [samplePrefix_succ, List.mem_append] at hy
      rcases hy with hy | hy
      · rcases ih hy with h | ⟨k, hk, hgk⟩
        · exact Or.inl h
        · exact Or.inr ⟨k, Nat.le_succ_of_le hk, hgk⟩
      · refine Or.inr ⟨m+1, le_rfl, ?_⟩
        simpa only [List.mem_singleton] using hy

theorem samplePrefix_nodup {m : ℕ} (ha : a = g 0)
    (hinj : ∀ k l, k ≤ m → l ≤ m → g k = g l → k = l) :
    (samplePrefix a g m).Nodup := by
  induction m with
  | zero =>
      rw [ha, samplePrefix_zero]
      exact List.nodup_singleton (g 0)
  | succ m ih =>
      rw [samplePrefix_succ]
      refine List.Nodup.append
        (ih (fun k l hk hl h => hinj k l (Nat.le_succ_of_le hk) (Nat.le_succ_of_le hl) h))
        (List.nodup_singleton _) ?_
      intro y hy hy'
      have hy'eq : y = g (m+1) := List.mem_singleton.mp hy'
      rcases samplePrefix_mem hy with h | ⟨l, hl, hl'⟩
      · rw [h, ha] at hy'eq
        exact absurd (hinj 0 (m+1) (Nat.zero_le _) le_rfl hy'eq) (by omega)
      · rw [hl'] at hy'eq
        exact absurd (hinj l (m+1) (Nat.le_succ_of_le hl) le_rfl hy'eq) (by omega)

end Sampling

/-! ## Appending one point to a `FineChain` -/

section Append

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Appending a point to the end of a `FineChain`, provided the new step is small. -/
theorem fineChain_append_singleton {c : OpenPartialHomeomorph X ℂ} {x : X} {r : ℝ}
    {l : List X} {u v : X} (hfc : FineChain c x r l) (hl : l.getLast? = some u)
    (hstep : dist (c v) (c u) < (r - dist (c u) (c x)) / 8) :
    FineChain c x r (l ++ [v]) := by
  induction l with
  | nil => simp at hl
  | cons a t ih =>
      cases t with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hl
          subst hl
          simp only [List.cons_append, List.nil_append]
          exact ⟨hstep, trivial⟩
      | cons b t' =>
          simp only [List.getLast?_cons_cons] at hl
          have hrec := ih hfc.2 hl
          simp only [List.cons_append] at hrec ⊢
          exact ⟨hfc.1, hrec⟩

/-- A sampled sequence whose consecutive steps are small is a `FineChain`. -/
theorem samplePrefix_fineChain {c : OpenPartialHomeomorph X ℂ} {x : X} {r : ℝ}
    {a : X} {g : ℕ → X} {m : ℕ} (ha : a = g 0)
    (hstep : ∀ k, k < m → dist (c (g (k+1))) (c (g k)) < (r - dist (c (g k)) (c x)) / 8) :
    FineChain c x r (samplePrefix a g m) := by
  induction m with
  | zero =>
      rw [show samplePrefix a g 0 = [g 0] by rw [ha, samplePrefix_zero]]
      exact trivial
  | succ n ih =>
      rw [samplePrefix_succ]
      cases n with
      | zero =>
          rw [show samplePrefix a g 0 = [g 0] by rw [ha, samplePrefix_zero],
            List.singleton_append]
          exact ⟨hstep 0 (by omega), trivial⟩
      | succ n =>
          have hl : (samplePrefix a g (n+1)).getLast? = some (g (n+1)) :=
            samplePrefix_getLast? (a := a) (g := g) n
          have hfc := ih (fun k hk => hstep k (by omega))
          exact fineChain_append_singleton hfc hl (hstep (n+1) (by omega))

end Append

/-! ## The main construction -/

section Main

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- Given the data of a locally finite cover by open coordinate balls `U n` (centres `c₀ n`, radii
`r₀ n`, whose *closed* model balls lie in the chart targets), two consecutive cover indices `v j`,
`v (j+1)` meeting each other, a point `p ∈ U (v j)` avoiding a finite set `F`, produce a point `q` in
the intersection `U (v j) ∩ U (v (j+1))` off `F ∪ {p}`, and a list starting at `p` and ending at `q`,
with no repetitions, all its points in `U (v j) ∖ F`, which is a `FineChain` for the chart of `v j`:
that is, each step is smaller than one eighth of the distance from the previous point's coordinate to
the boundary of the model ball of radius `r₀ (v j)`.

Route: `U (v j) \ F` is open (`hUo`, `F` finite) and preconnected (`isPreconnected_sdiff_finite`),
hence arc-connected (`exists_injective_path_in_is_open_connected`), so `p` and a suitable `q` are
joined by an injective path inside it; then sample the path: the room function
`z ↦ (r₀ (v j) - dist ((chartAt ℂ (c₀ (v j))) z) ((chartAt ℂ (c₀ (v j))) (c₀ (v j)))) / 8` is
continuous and positive on the compact image, so it has a positive lower bound `ρ` there, and uniform
continuity of the chart-image of the path gives `δ > 0` with steps less than `ρ`. -/
theorem exists_phase_plan {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (U : ℕ → Set X) (hUo : ∀ n, IsOpen (U n))
    (c₀ : ℕ → X) (r₀ : ℕ → ℝ)
    (hU : ∀ n, U n = (chartAt ℂ (c₀ n)).symm '' Metric.ball ((chartAt ℂ (c₀ n)) (c₀ n)) (r₀ n))
    (hroom : ∀ n, Metric.closedBall ((chartAt ℂ (c₀ n)) (c₀ n)) (r₀ n) ⊆
      (chartAt ℂ (c₀ n)).target)
    {v : ℕ → ℕ} {j : ℕ} {p : X} {F : Finset X}
    (hp : p ∈ U (v j)) (hpF : p ∉ (F : Set X)) (hadj : (U (v j) ∩ U (v (j + 1))).Nonempty) :
    ∃ z : X × List X, z.1 ∈ U (v j) ∩ U (v (j + 1)) ∧ z.1 ∉ (F : Set X) ∧ z.1 ≠ p ∧
      z.2.head? = some p ∧ z.2.getLast? = some z.1 ∧ z.2.Nodup ∧
      (∀ y ∈ z.2, y ∈ U (v j) ∧ y ∉ (F : Set X)) ∧
      Work.Drive.FineChain (chartAt ℂ (c₀ (v j))) (c₀ (v j)) (r₀ (v j)) z.2 := by
  classical
  -- ## Notation
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ (c₀ (v j)) with hc
  set x : X := c₀ (v j) with hx
  set r : ℝ := r₀ (v j) with hr
  have hroom' : Metric.closedBall (c x) r ⊆ c.target := by
    rw [hc, hx, hr]
    exact hroom (v j)
  have hUj : U (v j) = cBall c x r := by
    have h1 : U (v j) = c.symm '' Metric.ball (c x) r := by
      rw [hU (v j), ← hc, ← hx, ← hr]
    rw [h1, cBall_eq_image hroom']
  have hmemj : ∀ {y : X}, y ∈ U (v j) ↔ y ∈ cBall c x r := fun {y} => by rw [hUj]
  -- ## The point `p`
  have hpball : p ∈ cBall c x r := (hmemj.mp hp)
  have hpsrc : p ∈ c.source := hpball.1
  have hpc : dist (c p) (c x) < r := hpball.2
  have hrpos : 0 < r := lt_of_le_of_lt dist_nonneg hpc
  -- ## A point `q` of the next cover element, off `F ∪ {p}`
  have hIopen : IsOpen (U (v j) ∩ U (v (j + 1))) := (hUo (v j)).inter (hUo (v (j + 1)))
  have hSfin : ((F : Set X) ∪ {p}).Finite := F.finite_toSet.union (Set.finite_singleton p)
  obtain ⟨q, hqI, hqS⟩ := exists_mem_notMem_of_isOpen hIopen hadj _ hSfin
  have hqF : q ∉ (F : Set X) := fun h => hqS (Or.inl h)
  have hqp : q ≠ p := fun h => hqS (Or.inr (by simp [h]))
  have hqV : q ∈ U (v j) \ (F : Set X) := ⟨hqI.1, hqF⟩
  have hpV : p ∈ U (v j) \ (F : Set X) := ⟨hp, hpF⟩
  -- ## An injective path from `p` to `q` inside `U (v j) \ F`
  have hpre : IsPreconnected (U (v j)) := by
    rw [hUj]
    exact isPreconnected_cBall hroom'
  have hVpre : IsPreconnected (U (v j) \ (F : Set X)) :=
    isPreconnected_sdiff_finite (hUo (v j)) hpre (F : Set X) F.finite_toSet
  have hVopen : IsOpen (U (v j) \ (F : Set X)) :=
    (hUo (v j)).sdiff F.finite_toSet.isClosed
  have hVconn : IsConnected (U (v j) \ (F : Set X)) := ⟨⟨p, hpV⟩, hVpre⟩
  obtain ⟨γ, hγV, hγinj⟩ :=
    Work.Topology.Surface.exists_injective_path_in_is_open_connected (x := p) (y := q)
      hVopen hVconn hpV hqV hqp.symm
  -- ## The chart image of the path
  have hγsrc : ∀ t : unitInterval, ((γ t : X)) ∈ c.source := fun t => by
    have h1 : (γ t : X) ∈ cBall c x r := hmemj.mp (hγV t).1
    exact h1.1
  have hγball : ∀ t : unitInterval, c (γ t) ∈ Metric.ball (c x) r := fun t => by
    have h1 : (γ t : X) ∈ cBall c x r := hmemj.mp (hγV t).1
    exact h1.2
  set room : ℂ → ℝ := fun w => (r - dist w (c x)) / 8 with hroomdef
  have hroomcont : Continuous room := by
    rw [hroomdef]
    fun_prop
  have hfcont : Continuous (fun t : unitInterval => c (γ t)) :=
    c.continuousOn.comp_continuous γ.continuous hγsrc
  have hroompos : ∀ t : unitInterval, 0 < room (c (γ t)) := by
    intro t
    have h1 : dist (c (γ t)) (c x) < r := hγball t
    have h2 : 0 < r - dist (c (γ t)) (c x) := by linarith
    have h3 : (0:ℝ) < 8 := by norm_num
    simpa [room] using div_pos h2 h3
  -- ## A positive lower bound `ρ` of the room function on the path
  obtain ⟨t₀, -, hmin₀⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty :
      (Set.univ : Set unitInterval).Nonempty) ((hroomcont.comp hfcont).continuousOn)
  rw [isMinOn_iff] at hmin₀
  have hρpos : 0 < room (c (γ t₀)) := hroompos t₀
  have hmin : ∀ t : unitInterval, room (c (γ t₀)) ≤ room (c (γ t)) := fun t => hmin₀ t trivial
  -- ## Uniform continuity gives a step size `δ`
  have hunif : UniformContinuousOn (fun t : unitInterval => c (γ t)) Set.univ :=
    isCompact_univ.uniformContinuousOn_of_continuous hfcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hunif
  obtain ⟨δ, hδpos, hδ⟩ := hunif (room (c (γ t₀))) hρpos
  obtain ⟨N, hNlt⟩ := exists_nat_one_div_lt hδpos
  -- ## The sampled parameter values `u k = k / (N+1)`
  have hNposR : (0:ℝ) < (N:ℝ) + 1 := by positivity
  let u : ℕ → unitInterval := fun k =>
    ⟨min ((k:ℝ) / ((N:ℝ) + 1)) 1,
      ⟨le_min (div_nonneg (Nat.cast_nonneg k) (le_of_lt hNposR)) zero_le_one,
        min_le_right _ _⟩⟩
  have hu_eq : ∀ k ≤ N + 1, ((u k : unitInterval) : ℝ) = (k:ℝ) / ((N:ℝ) + 1) := by
    intro k hk
    have h1 : ((u k : unitInterval) : ℝ) = min ((k:ℝ) / ((N:ℝ) + 1)) 1 := rfl
    rw [h1, min_eq_left]
    rw [div_le_one hNposR]
    exact_mod_cast hk
  have hu_one : u (N + 1) = 1 := by
    apply Subtype.ext
    rw [hu_eq (N+1) le_rfl]
    field_simp
    push_cast
    ring
  -- ## Consecutive samples are closer than `ρ`
  have hstep : ∀ k < N + 1, dist (c (γ (u (k+1)))) (c (γ (u k))) < room (c (γ (u k))) := by
    intro k hk
    have hdist : dist (u (k+1)) (u k) < δ := by
      rw [dist_comm, Subtype.dist_eq, hu_eq k (by omega), hu_eq (k+1) hk, Real.dist_eq]
      have hcalc : (k:ℝ) / ((N:ℝ) + 1) - ((k+1 : ℕ) : ℝ) / ((N:ℝ) + 1)
          = -(1 / ((N:ℝ) + 1)) := by
        rw [← sub_div]
        push_cast
        ring
      rw [hcalc, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / ((N:ℝ) + 1))]
      exact hNlt
    have h2 := hδ (u (k+1)) trivial (u k) trivial hdist
    exact lt_of_lt_of_le h2 (hmin (u k))
  -- ## The sampled list
  set g : ℕ → X := fun k => γ (u k) with hg
  have hu0 : u 0 = (0 : unitInterval) := by
    apply Subtype.ext
    rw [hu_eq 0 (Nat.zero_le _)]
    simp
  have hg0 : p = g 0 := by
    show p = γ (u 0)
    rw [hu0, γ.source]
  have hnodup : (samplePrefix p g (N+1)).Nodup := by
    refine samplePrefix_nodup hg0 ?_
    intro k l hk hl hkl
    have hkl' : γ (u k) = γ (u l) := by
      rw [hg] at hkl
      exact hkl
    have h3 : u k = u l := hγinj hkl'
    have h4 : ((u k : unitInterval) : ℝ) = ((u l : unitInterval) : ℝ) := congrArg Subtype.val h3
    rw [hu_eq k hk, hu_eq l hl] at h4
    have hD : ((N:ℝ) + 1) ≠ 0 := by positivity
    rw [div_eq_div_iff hD hD] at h4
    have h5 : (k:ℝ) = (l:ℝ) := mul_right_cancel₀ hD h4
    exact_mod_cast h5
  refine ⟨(q, samplePrefix p g (N+1)), hqI, hqF, hqp, ?_, ?_, hnodup, ?_, ?_⟩
  · -- `head?`
    exact samplePrefix_head? (a := p) (g := g) (N+1)
  · -- `getLast?`
    have hlast := samplePrefix_getLast? (a := p) (g := g) N
    have hq : g (N+1) = q := by
      show γ (u (N+1)) = q
      rw [hu_one, γ.target]
    rw [hq] at hlast
    exact hlast
  · -- membership of all the points of the list
    intro y hy
    rcases samplePrefix_mem hy with h | ⟨k, hk, hgk⟩
    · rw [h]
      exact ⟨hp, hpF⟩
    · rw [hgk, hg]
      exact ⟨(hγV (u k)).1, (hγV (u k)).2⟩
  · -- the fine chain
    have hfc := samplePrefix_fineChain (c := c) (x := x) (r := r) (a := p) (g := g) hg0
      (fun k hk => hstep k hk)
    simpa only [hc, hx, hr] using hfc

end Main

end Work.Drive
