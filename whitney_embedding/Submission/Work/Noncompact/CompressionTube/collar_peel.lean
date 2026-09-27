import Mathlib
import Submission.Work.Noncompact.CompressionTube.exists_level_arc_of_collar_shell
import Submission.Work.Noncompact.CompressionTube.peel_carrier_remove
import Submission.Work.Noncompact.CompressionTube.exit_tail_mem_frontier
import Submission.Work.Noncompact.CompressionTube.exists_side_arc_of_arc_end

/-!
# The peel lemma: one level's `(EXIT)` arcs out of a collar, with the previous spikes removed

Given a closed "previous collar" `P` (pocket free), a collar `L` with its set `U` and its shell, a
finite family of start points `s i ∈ interior L ∖ P` with pairwise disjoint avoidance sets `F i`,
obstacles `β`, and --- for the strands already present at the previous level --- *slits* `slt j`
(the previous level's spikes: free ended curves inside `Pᶜ` whose tips are the start points), this
lemma produces one `(EXIT)` arc `α i` per strand.

The proof peels the strands one at a time.  The carrier of the strand at `p` is the component
`connectedComponentIn (Pᶜ) p` of `Pᶜ` with the *inside pieces* of the arcs already routed and the
*bodies* of all the slits removed.  When `p` is not the tip of a slit, `p` itself is a point of this
carrier and the per-strand `(EXIT)` arc of `exists_level_arc_of_collar_shell` can be started there
directly.  When `p` *is* the tip of a slit, it is removed together with the slit body, and the arc
is instead started at a nearby point `y` of the carrier, reached from `p` by a *side arc* `κ` which
meets the own slit only at `p` (`exists_side_arc_of_arc_end`); the two arcs are then glued along the
last point where the level arc meets `κ` (`trim_arc`).  The old collars' exterior pieces are handed
to the level arc as *obstacles* `β'`, and the old tips enter the finite avoidance set.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace Work.Noncompact.CompressionTube

open Set Topology

/-- The right endpoint of a path whose open part lies in `U` is in the closure of `U`. -/
lemma endpoint_mem_closure {M : Type*} [TopologicalSpace M] {U : Set M} {β : ℝ → M}
    (hβc : Continuous β) (hβsub : β '' Set.Ioc (0:ℝ) 1 ⊆ U) : β 1 ∈ closure U :=
  map_mem_closure hβc (by rw [closure_Ioc (by norm_num)]; norm_num)
    (fun t ht => hβsub ⟨t, ht, rfl⟩)

/-- A "spike" into `U` cannot have an interior point of `L` (with `U ∩ L = ∅`) on its image,
when that point is not its start. -/
lemma spike_notMem_of_mem_interior {M : Type*} [TopologicalSpace M] {U L : Set M}
    (hUL : Disjoint U L) {β : ℝ → M}
    (hβc : Continuous β) (hβsub : β '' Set.Ioc (0:ℝ) 1 ⊆ U) {p : M} (hp : p ∈ interior L)
    (h0 : β 0 ≠ p) : p ∉ β '' Set.Icc (0:ℝ) 1 := by
  rintro ⟨t, ht, htp⟩
  rcases eq_or_lt_of_le ht.1 with h | h
  · exact h0 (by rw [← htp, h])
  · rcases eq_or_lt_of_le ht.2 with h1 | h1
    · have : p ∈ closure U := by rw [← htp, h1]; exact endpoint_mem_closure hβc hβsub
      obtain ⟨y, hy1, hy2⟩ := (mem_closure_iff.mp this) (interior L) isOpen_interior hp
      exact Set.disjoint_left.mp hUL hy2 (interior_subset hy1)
    · exact Set.disjoint_left.mp hUL (hβsub ⟨t, ⟨h, h1.le⟩, rfl⟩)
        (by rw [htp]; exact interior_subset hp)

/-- **The trimmed arc.**  Two arcs `κ` (from `p` to `y`) and `α'` (from `y`) meeting in a single
point `κ t₀ = α' τ`, with `τ` the *last* time `α'` meets `κ '' [0,1]`, glue to an arc from `p`
which follows `κ` up to the cut and `α'` afterwards. -/
theorem trim_arc {M : Type*} [TopologicalSpace M]
    {κ α' : ℝ → M} {p y : M} {τ t₀ : ℝ}
    (hκc : Continuous κ) (hκi : Set.InjOn κ (Set.Icc (0:ℝ) 1)) (hκ0 : κ 0 = p)
    (hκ1 : κ 1 = y)
    (hα'c : Continuous α') (hα'i : Set.InjOn α' (Set.Icc (0:ℝ) 1)) (hα'0 : α' 0 = y)
    (hκy : κ t₀ = α' τ) (ht₀ : t₀ ∈ Set.Icc (0:ℝ) 1) (hτ : τ ∈ Set.Icc (0:ℝ) 1)
    (ht₀pos : 0 < t₀) (hτlt : τ < 1)
    (hmax : ∀ t ∈ Set.Icc (0:ℝ) 1, τ < t → α' t ∉ κ '' Set.Icc (0:ℝ) 1)
    (hα'p : ∀ t ∈ Set.Icc (0:ℝ) 1, α' t ≠ p) :
    ∃ w : ℝ → M, Continuous w ∧ Set.InjOn w (Set.Icc (0:ℝ) 1) ∧ w 0 = p ∧ w 1 = α' 1 ∧
      (∀ u ∈ Set.Icc (0:ℝ) (1/2), w u ∈ κ '' Set.Icc (0:ℝ) 1) ∧
      (∀ u ∈ Set.Icc (1/2) 1, w u = α' (τ + (2*u-1)*(1-τ))) ∧
      (∀ u ∈ Set.Ioc (0:ℝ) 1, w u ≠ p) := by
  classical
  have hcont : Continuous
      (fun u : ℝ => if u ≤ 1/2 then κ (2*t₀*u) else α' (τ + (2*u-1)*(1-τ))) := by
    refine Continuous.if_le (f := fun u : ℝ => u) (g := fun _ : ℝ => (1/2:ℝ))
      (f' := fun u : ℝ => κ (2*t₀*u)) (g' := fun u : ℝ => α' (τ + (2*u-1)*(1-τ)))
      ?_ ?_ continuous_id continuous_const ?_
    · exact hκc.comp (by fun_prop)
    · exact hα'c.comp (by fun_prop)
    · intro x hx
      have hx' : x = 1/2 := hx
      subst hx'
      have h1 : κ (2*t₀*(1/2)) = κ t₀ := by rw [show 2*t₀*(1/2) = t₀ by ring]
      have h2 : α' (τ + (2*(1/2)-1)*(1-τ)) = α' τ := by
        rw [show 2*(1/2:ℝ)-1 = 0 by norm_num, zero_mul, add_zero]
      rw [h1, h2, hκy]
  have hb1 : ∀ u ∈ Set.Icc (0:ℝ) (1/2), 2*t₀*u ∈ Set.Icc (0:ℝ) 1 := by
    intro u hu
    exact ⟨by nlinarith [hu.1, ht₀.1], by nlinarith [hu.2, ht₀.2]⟩
  have hb2 : ∀ u ∈ Set.Icc (1/2:ℝ) 1, τ + (2*u-1)*(1-τ) ∈ Set.Icc (0:ℝ) 1 := by
    intro u hu
    exact ⟨by nlinarith [hu.1, hτ.1, hτlt], by nlinarith [hu.2, hτ.1, hτlt]⟩
  have hb2gt : ∀ u ∈ Set.Icc (1/2:ℝ) 1, (1/2:ℝ) < u → τ < τ + (2*u-1)*(1-τ) := by
    intro u hu hu1
    have h2 : 0 < 2*u-1 := by linarith
    nlinarith [hτlt, h2]
  have hinj : Set.InjOn
      (fun u : ℝ => if u ≤ 1/2 then κ (2*t₀*u) else α' (τ + (2*u-1)*(1-τ)))
      (Set.Icc (0:ℝ) 1) := by
    intro u hu u' hu' heq
    change (if u ≤ 1/2 then κ (2*t₀*u) else α' (τ + (2*u-1)*(1-τ)))
      = (if u' ≤ 1/2 then κ (2*t₀*u') else α' (τ + (2*u'-1)*(1-τ))) at heq
    by_cases h : u ≤ 1/2
    · by_cases h' : u' ≤ 1/2
      · rw [if_pos h, if_pos h'] at heq
        have h1 := hκi (hb1 u ⟨hu.1, h⟩) (hb1 u' ⟨hu'.1, h'⟩) heq
        nlinarith [ht₀pos, h1]
      · rw [if_pos h, if_neg h'] at heq
        exact absurd ⟨2*t₀*u, hb1 u ⟨hu.1, h⟩, heq⟩
          (hmax _ (hb2 u' ⟨le_of_lt (not_le.mp h'), hu'.2⟩)
            (hb2gt u' ⟨le_of_lt (not_le.mp h'), hu'.2⟩ (not_le.mp h')))
    · by_cases h' : u' ≤ 1/2
      · rw [if_neg h, if_pos h'] at heq
        exact absurd ⟨2*t₀*u', hb1 u' ⟨hu'.1, h'⟩, heq.symm⟩
          (hmax _ (hb2 u ⟨le_of_lt (not_le.mp h), hu.2⟩)
            (hb2gt u ⟨le_of_lt (not_le.mp h), hu.2⟩ (not_le.mp h)))
      · rw [if_neg h, if_neg h'] at heq
        have h1 := hα'i (hb2 u ⟨le_of_lt (not_le.mp h), hu.2⟩)
          (hb2 u' ⟨le_of_lt (not_le.mp h'), hu'.2⟩) heq
        nlinarith [hτlt, h1]
  have hw0 : (fun u : ℝ => if u ≤ 1/2 then κ (2*t₀*u) else α' (τ + (2*u-1)*(1-τ))) 0 = p := by
    change (if (0:ℝ) ≤ 1/2 then κ (2*t₀*0) else α' (τ + (2*0-1)*(1-τ))) = p
    rw [if_pos (by norm_num : (0:ℝ) ≤ 1/2), show 2*t₀*0 = 0 by ring, hκ0]
  have hw1 : (fun u : ℝ => if u ≤ 1/2 then κ (2*t₀*u) else α' (τ + (2*u-1)*(1-τ))) 1 = α' 1 := by
    change (if (1:ℝ) ≤ 1/2 then κ (2*t₀*1) else α' (τ + (2*1-1)*(1-τ))) = α' 1
    rw [if_neg (by norm_num : ¬ ((1:ℝ) ≤ 1/2))]
    congr 1
    ring
  have hmem : ∀ u ∈ Set.Icc (0:ℝ) (1/2),
      (fun u : ℝ => if u ≤ 1/2 then κ (2*t₀*u) else α' (τ + (2*u-1)*(1-τ))) u
        ∈ κ '' Set.Icc (0:ℝ) 1 := by
    intro u hu
    change (if u ≤ 1/2 then κ (2*t₀*u) else α' (τ + (2*u-1)*(1-τ))) ∈ κ '' Set.Icc (0:ℝ) 1
    rw [if_pos hu.2]
    exact ⟨2*t₀*u, hb1 u hu, rfl⟩
  have hformula : ∀ u ∈ Set.Icc (1/2:ℝ) 1,
      (fun u : ℝ => if u ≤ 1/2 then κ (2*t₀*u) else α' (τ + (2*u-1)*(1-τ))) u
        = α' (τ + (2*u-1)*(1-τ)) := by
    intro u hu
    change (if u ≤ 1/2 then κ (2*t₀*u) else α' (τ + (2*u-1)*(1-τ)))
      = α' (τ + (2*u-1)*(1-τ))
    rcases eq_or_lt_of_le hu.1 with h | h
    · subst h
      rw [if_pos le_rfl, show 2*t₀*(1/2) = t₀ by ring, hκy]
      rw [show 2*(1/2:ℝ)-1 = 0 by norm_num, zero_mul, add_zero]
    · rw [if_neg (not_le.mpr h)]
  have hne : ∀ u ∈ Set.Ioc (0:ℝ) 1,
      (fun u : ℝ => if u ≤ 1/2 then κ (2*t₀*u) else α' (τ + (2*u-1)*(1-τ))) u ≠ p := by
    intro u hu
    change (if u ≤ 1/2 then κ (2*t₀*u) else α' (τ + (2*u-1)*(1-τ))) ≠ p
    by_cases h : u ≤ 1/2
    · rw [if_pos h]
      intro hcon
      have hzero : 2*t₀*u = 0 :=
        hκi (hb1 u ⟨hu.1.le, h⟩) ⟨le_rfl, zero_le_one⟩ (by rw [hcon, hκ0])
      nlinarith [hu.1, ht₀pos, hzero]
    · rw [if_neg h]
      exact hα'p _ (hb2 u ⟨le_of_lt (not_le.mp h), hu.2⟩)
  exact ⟨_, hcont, hinj, hw0, hw1, hmem, hformula, hne⟩

/-- The data of a partially peeled level: the arcs `α i` with their exit times `σ i`, the start
points `g i`, the avoidance sets `Fg i`, the obstacles `β`, the slits `slt` and the set `R` of all
the start points of the level. -/
structure PeelPrefix {M : Type*} [TopologicalSpace M] (P L U Shell R : Set M)
    {k m r : ℕ} (g : Fin k → M) (Fg : Fin k → Set M) (β : Fin m → ℝ → M)
    (slt : Fin r → ℝ → M) (α : Fin k → ℝ → M) (σ : Fin k → ℝ) : Prop where
  cont : ∀ i, Continuous (α i)
  injOn : ∀ i, Set.InjOn (α i) (Set.Icc (0:ℝ) 1)
  zero : ∀ i, α i 0 = g i
  sigma_mem : ∀ i, σ i ∈ Set.Ioo (0:ℝ) 1
  inside_mem : ∀ i u, u ∈ Set.Icc (0:ℝ) (σ i) → α i u ∈ L
  outside_notMem : ∀ i u, u ∈ Set.Ioc (σ i) 1 → α i u ∉ L
  outside_mem_U : ∀ i u, u ∈ Set.Ioc (σ i) 1 → α i u ∈ U
  outside_mem_Shell : ∀ i u, u ∈ Set.Ioc (σ i) 1 → α i u ∈ Shell
  tip_mem_Shell : ∀ i, α i 1 ∈ Shell
  tip_mem_U : ∀ i, α i 1 ∈ U
  tip_notMem : ∀ i, α i 1 ∉ Fg i
  arc_subset : ∀ i u, u ∈ Set.Icc (0:ℝ) 1 → α i u ∈ connectedComponentIn (Pᶜ) (g i) ∪ U
  inside_mem_comp : ∀ i u, u ∈ Set.Icc (0:ℝ) (σ i) → α i u ∈ connectedComponentIn (Pᶜ) (g i)
  arc_notMem : ∀ i u, u ∈ Set.Icc (0:ℝ) 1 → α i u ∉ Fg i
  arc_avoids_β : ∀ i u, u ∈ Set.Icc (0:ℝ) 1 → ∀ j, α i u ∉ β j '' Set.Icc (0:ℝ) 1
  arc_avoids_slt_other : ∀ i u, u ∈ Set.Icc (0:ℝ) 1 → ∀ j, slt j 1 ≠ g i →
    α i u ∉ slt j '' Set.Icc (0:ℝ) 1
  arc_avoids_slt_own : ∀ i u, u ∈ Set.Ioo (0:ℝ) 1 → ∀ j, slt j 1 = g i →
    α i u ∉ slt j '' Set.Icc (0:ℝ) 1
  pair_disjoint : ∀ i i', i ≠ i' → Disjoint (α i '' Set.Icc (0:ℝ) 1) (α i' '' Set.Icc (0:ℝ) 1)
  start_avoid : ∀ i u, u ∈ Set.Icc (0:ℝ) 1 → α i u ∉ R \ {g i}

/-- **The peeling step.**  Add one strand (at the start point `p`) to a family indexed by `Fin k`. -/
theorem peel_step {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {P L K U Shell : Set M} (hPc : IsClosed P)
    (hPpf : ∀ x : M, x ∉ P → ¬ IsCompact (closure (connectedComponentIn (Pᶜ) x)))
    (hLc : IsClosed L) (hKc : IsCompact K) (hLK : L ⊆ K)
    (hUo : IsOpen U) (hUL : Disjoint U L)
    (hShellO : IsOpen Shell) (hfrontShell : frontier L ⊆ Shell)
    (hpieces : ∀ z ∈ frontier L, ∃ (x : M) (b : Work.Whitney.PathTools.ChartBall n M Set.univ x),
      z ∈ b.K ∧ b.c.symm '' Metric.ball (b.c x) b.ρ ⊆ U)
    {k m r : ℕ} {g : Fin k → M} {Fg : Fin k → Set M} {R : Set M}
    {β : Fin m → ℝ → M} {slt : Fin r → ℝ → M} {α₀ : Fin k → ℝ → M} {σ₀ : Fin k → ℝ}
    (hOld : PeelPrefix P L U Shell R g Fg β slt α₀ σ₀)
    {p : M} (hpR : p ∈ R) (hgp : ∀ i, g i ≠ p) (hpP : p ∈ Pᶜ) (hpsint : p ∈ interior L)
    (hsltc : ∀ j, Continuous (slt j)) (hsltinj : ∀ j, Set.InjOn (slt j) (Set.Icc (0:ℝ) 1))
    (hsltbody : ∀ j, slt j '' Set.Ioc (0:ℝ) 1 ⊆ Pᶜ)
    (hsltroot : ∀ j, slt j 0 ∉ Pᶜ)
    (hsltdisj : ∀ j j', j ≠ j' →
      Disjoint (slt j '' Set.Icc (0:ℝ) 1) (slt j' '' Set.Icc (0:ℝ) 1))
    (hsltU : ∀ j, Disjoint (slt j '' Set.Icc (0:ℝ) 1) U)
    (hsltR : ∀ j, slt j 1 ∈ R)
    (hnotslt : ∀ j, slt j 1 ≠ p → p ∉ slt j '' Set.Icc (0:ℝ) 1)
    {Fp : Set M} (hFp : Fp.Finite) (hpsFp : p ∉ Fp) (hRsub : R \ {p} ⊆ Fp)
    (hβc : ∀ j, Continuous (β j)) (hβsub : ∀ j, β j '' Set.Ioc (0:ℝ) 1 ⊆ U)
    (hβ0F : ∀ j, β j 0 ∈ Fp)
    (hβfront : ∀ j, ∀ z ∈ frontier L, z ∈ closure (β j '' Set.Icc (0:ℝ) 1) → z ∈ Fp) :
    ∃ (α : Fin (k+1) → ℝ → M) (σ : Fin (k+1) → ℝ),
      PeelPrefix P L U Shell R (Fin.snoc g p) (Fin.snoc Fg Fp) β slt α σ := by
  classical
  haveI : LocallyPathConnectedSpace M :=
    Work.Whitney.PathTools.locallyPathConnectedSpace_chartedSpace (n := n)
  haveI : LocallyConnectedSpace M := inferInstance
  have hg0 : ∀ i : Fin k, g i = α₀ i 0 := fun i => (hOld.zero i).symm
  have hCxopen : IsOpen (connectedComponentIn (Pᶜ) p) := hPc.isOpen_compl.connectedComponentIn
  -- the carrier of a strand: the component of `Pᶜ`, minus the inside pieces of the routed arcs
  -- and the bodies of all the slits
  have hcarrier := peel_carrier_remove (n := n) hn hPc hpP (hPpf p hpP) hOld.cont hOld.injOn
    hOld.sigma_mem (fun i u hu => hg0 i ▸ hOld.inside_mem_comp i u hu)
    (fun i i' hne => (hOld.pair_disjoint i i' hne).mono
      (Set.image_mono (Set.Icc_subset_Icc le_rfl (hOld.sigma_mem i).2.le))
      (Set.image_mono (Set.Icc_subset_Icc le_rfl (hOld.sigma_mem i').2.le)))
    hsltc hsltinj hsltbody hsltroot hsltdisj
    (fun i u hu j hne => hOld.arc_avoids_slt_other i u hu j (fun hc => hne (hg0 i ▸ hc)))
    (fun i u hu j hcl => hOld.arc_avoids_slt_own i u hu j (hg0 i ▸ hcl))
  set O : Set M := connectedComponentIn (Pᶜ) p \ ((⋃ i : Fin k, α₀ i '' Set.Icc (0:ℝ) (σ₀ i)) ∪ (⋃ j : Fin r, slt j '' Set.Ioc (0:ℝ) 1)) with hOdef
  have hOopen : IsOpen O := by rw [hOdef]; exact hcarrier.1
  have hOpre : IsPreconnected O := by rw [hOdef]; exact hcarrier.2.1
  have hOnt : ¬ IsCompact (closure O) := by rw [hOdef]; exact hcarrier.2.2
  have hOsub : O ⊆ connectedComponentIn (Pᶜ) p := by rw [hOdef]; exact Set.sdiff_subset
  -- the avoidance set of the new strand: the prescribed one, plus the old tips (so that the old
  -- exterior pieces, handed over as obstacles, start inside it)
  set Fa : Set M := Fp ∪ Set.range (fun i : Fin k => α₀ i (σ₀ i)) with hFadef
  have hFa_fin : Fa.Finite := hFp.union (Set.finite_range _)
  have hFp_sub : Fp ⊆ Fa := by intro x hx; rw [hFadef]; exact Or.inl hx
  have htail_mem : ∀ i, α₀ i (σ₀ i) ∈ Fa := fun i => by rw [hFadef]; exact Or.inr ⟨i, rfl⟩
  -- the obstacles: the old exterior pieces, reparametrised
  set β' : Fin (m + k) → ℝ → M :=
    Fin.append β (fun i u => α₀ i (σ₀ i + (1 - σ₀ i) * u)) with hβ'def
  have hβ'imgIcc : ∀ i : Fin k, (fun u : ℝ => σ₀ i + (1 - σ₀ i) * u) '' Set.Icc (0:ℝ) 1
      = Set.Icc (σ₀ i) 1 := by
    intro i
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨by nlinarith [hu.1, (hOld.sigma_mem i).2], by nlinarith [hu.2, (hOld.sigma_mem i).2]⟩
    · intro hx
      have h1 : (0:ℝ) < 1 - σ₀ i := by linarith [(hOld.sigma_mem i).2]
      refine ⟨(x - σ₀ i) / (1 - σ₀ i), ⟨?_, ?_⟩, ?_⟩
      · exact div_nonneg (by linarith [hx.1]) h1.le
      · rw [div_le_one h1]; linarith [hx.2]
      · field_simp
        ring
  have hβ'iocImg : ∀ i : Fin k, (fun u : ℝ => σ₀ i + (1 - σ₀ i) * u) '' Set.Ioc (0:ℝ) 1
      = Set.Ioc (σ₀ i) 1 := by
    intro i
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨by nlinarith [hu.1, (hOld.sigma_mem i).2], by nlinarith [hu.2, (hOld.sigma_mem i).2]⟩
    · intro hx
      have h1 : (0:ℝ) < 1 - σ₀ i := by linarith [(hOld.sigma_mem i).2]
      refine ⟨(x - σ₀ i) / (1 - σ₀ i), ⟨?_, ?_⟩, ?_⟩
      · exact div_pos (by linarith [hx.1]) h1
      · rw [div_le_one h1]; linarith [hx.2]
      · field_simp
        ring
  have hβ'c : ∀ j, Continuous (β' j) := by
    refine Fin.addCases (motive := fun j => Continuous (β' j)) (fun j' => ?_) (fun i => ?_)
    · rw [hβ'def, Fin.append_left]; exact hβc j'
    · rw [hβ'def, Fin.append_right]; exact (hOld.cont i).comp (by fun_prop)
  have hβ'sub : ∀ j, β' j '' Set.Ioc (0:ℝ) 1 ⊆ U := by
    refine Fin.addCases (motive := fun j => β' j '' Set.Ioc (0:ℝ) 1 ⊆ U) (fun j' => ?_) (fun i => ?_)
    · rw [hβ'def, Fin.append_left]; exact hβsub j'
    · rw [hβ'def, Fin.append_right, ← Set.image_image, hβ'iocImg i]
      rintro x ⟨u, hu, rfl⟩
      exact hOld.outside_mem_U i u hu
  have hβ'0 : ∀ j, β' j 0 ∈ Fa := by
    refine Fin.addCases (motive := fun j => β' j 0 ∈ Fa) (fun j' => ?_) (fun i => ?_)
    · rw [hβ'def, Fin.append_left]; exact hFp_sub (hβ0F j')
    · rw [hβ'def, Fin.append_right]
      show α₀ i (σ₀ i + (1 - σ₀ i) * 0) ∈ Fa
      rw [mul_zero, add_zero]; exact htail_mem i
  have hβ'front : ∀ j, ∀ z ∈ frontier L, z ∈ closure (β' j '' Set.Icc (0:ℝ) 1) → z ∈ Fa := by
    intro j
    refine Fin.addCases
      (motive := fun j => ∀ z ∈ frontier L, z ∈ closure (β' j '' Set.Icc (0:ℝ) 1) → z ∈ Fa)
      (fun j' => ?_) (fun i => ?_) j
    · intro z hz hzcl
      rw [hβ'def, Fin.append_left] at hzcl
      exact hFp_sub (hβfront j' z hz hzcl)
    · intro z hz hzcl
      rw [hβ'def, Fin.append_right] at hzcl
      have himg : (fun u : ℝ => α₀ i (σ₀ i + (1 - σ₀ i) * u)) '' Set.Icc (0:ℝ) 1
          = α₀ i '' Set.Icc (σ₀ i) 1 := by
        rw [← Set.image_image, hβ'imgIcc i]
      rw [himg, (isCompact_Icc.image (hOld.cont i)).isClosed.closure_eq] at hzcl
      obtain ⟨v, hv, hveq⟩ := hzcl
      have hzL : z ∈ L := hLc.closure_eq ▸ frontier_subset_closure hz
      rcases eq_or_lt_of_le hv.1 with h0 | h0
      · rw [← hveq, ← h0]; exact htail_mem i
      · have hU : z ∈ U := by rw [← hveq]; exact hOld.outside_mem_U i v ⟨h0, hv.2⟩
        exact absurd hzL (Set.disjoint_left.mp hUL hU)
  -- `p` is not on an already routed arc, and not in `Fa`
  have hp_ins : ∀ i, p ∉ α₀ i '' Set.Icc (0:ℝ) (σ₀ i) := by
    intro i
    rintro ⟨u, hu, hpu⟩
    have huI : u ∈ Set.Icc (0:ℝ) 1 := ⟨hu.1, le_trans hu.2 (hOld.sigma_mem i).2.le⟩
    have hR : α₀ i u ∈ R := by rw [hpu]; exact hpR
    have hne : α₀ i u ≠ g i := fun hc => hgp i (hc.symm.trans hpu)
    exact hOld.start_avoid i u huI ⟨hR, hne⟩
  have hp_tail : ∀ i, p ∉ α₀ i '' Set.Icc (σ₀ i) 1 := by
    intro i
    rintro ⟨u, hu, hpu⟩
    rcases eq_or_lt_of_le hu.1 with h0 | h0
    · have hf : α₀ i (σ₀ i) ∈ frontier L :=
        exit_tail_mem_frontier hLc (hOld.cont i) (hOld.sigma_mem i).1.le (hOld.sigma_mem i).2
          (hOld.inside_mem i) (hOld.outside_notMem i)
      rw [hLc.frontier_eq] at hf
      exact hf.2 (by rw [h0, hpu]; exact hpsint)
    · have hpU : p ∈ U := by rw [← hpu]; exact hOld.outside_mem_U i u ⟨h0, hu.2⟩
      exact Set.disjoint_left.mp hUL hpU (interior_subset hpsint)
  have hpFa : p ∉ Fa := by
    rw [hFadef]
    intro hmem
    rcases hmem with h | h
    · exact hpsFp h
    · obtain ⟨i, hi⟩ := h
      exact hp_tail i ⟨σ₀ i, ⟨le_rfl, (hOld.sigma_mem i).2.le⟩, hi⟩
  have hp_arc : ∀ i, p ∉ α₀ i '' Set.Icc (0:ℝ) 1 := by
    intro i
    rintro ⟨u, hu, hpu⟩
    rcases le_or_gt u (σ₀ i) with h | h
    · exact hp_ins i ⟨u, ⟨hu.1, h⟩, hpu⟩
    · exact hp_tail i ⟨u, ⟨le_of_lt h, hu.2⟩, hpu⟩
  have hp_β : ∀ j : Fin m, p ∉ β j '' Set.Icc (0:ℝ) 1 := fun j =>
    spike_notMem_of_mem_interior hUL (hβc j) (hβsub j) hpsint
      (fun hc => hpsFp (hc ▸ hβ0F j))
  -- the new strand
  have key : ∃ (anew : ℝ → M) (σnew : ℝ),
      Continuous anew ∧ Set.InjOn anew (Set.Icc (0:ℝ) 1) ∧ anew 0 = p ∧
      σnew ∈ Set.Ioo (0:ℝ) 1 ∧
      (∀ u ∈ Set.Icc (0:ℝ) σnew, anew u ∈ L) ∧
      (∀ u ∈ Set.Ioc σnew 1, anew u ∉ L) ∧
      (∀ u ∈ Set.Ioc σnew 1, anew u ∈ U) ∧
      (∀ u ∈ Set.Ioc σnew 1, anew u ∈ Shell) ∧
      anew 1 ∈ Shell ∧ anew 1 ∈ U ∧ anew 1 ∉ Fp ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, anew u ∈ connectedComponentIn (Pᶜ) p ∪ U) ∧
      (∀ u ∈ Set.Icc (0:ℝ) σnew, anew u ∈ connectedComponentIn (Pᶜ) p) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, anew u ∉ Fp) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j : Fin m, anew u ∉ β j '' Set.Icc (0:ℝ) 1) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j : Fin r, slt j 1 ≠ p →
        anew u ∉ slt j '' Set.Icc (0:ℝ) 1) ∧
      (∀ u ∈ Set.Ioo (0:ℝ) 1, ∀ j : Fin r, slt j 1 = p →
        anew u ∉ slt j '' Set.Icc (0:ℝ) 1) ∧
      (∀ i : Fin k, Disjoint (anew '' Set.Icc (0:ℝ) 1) (α₀ i '' Set.Icc (0:ℝ) 1)) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, anew u ∉ R \ {p}) := by
    by_cases hown : ∃ j : Fin r, slt j 1 = p
    · -- Case B: a slit ends at `p`.  Route the new arc from a nearby point of the carrier.
      obtain ⟨j0, hj0⟩ := hown
      have huniq : ∀ j : Fin r, slt j 1 = p → j = j0 := by
        intro j hj
        by_contra hne
        exact Set.disjoint_left.mp (hsltdisj j j0 hne)
          ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩ ⟨1, ⟨zero_le_one, le_rfl⟩, hj0.trans hj.symm⟩
      -- the set of points the side arc has to avoid
      set Z : Set M := (⋃ i : Fin k, α₀ i '' Set.Icc (0:ℝ) 1) ∪
        (⋃ j : Fin m, β j '' Set.Icc (0:ℝ) 1) ∪
        (⋃ j : {j : Fin r // slt j 1 ≠ p}, slt j.1 '' Set.Icc (0:ℝ) 1) ∪ Fa with hZdef
      have hZclosed : IsClosed Z := by
        rw [hZdef]
        refine IsClosed.union (IsClosed.union (IsClosed.union ?_ ?_) ?_) hFa_fin.isClosed
        · exact (isCompact_iUnion fun i : Fin k => isCompact_Icc.image (hOld.cont i)).isClosed
        · exact (isCompact_iUnion fun j : Fin m => isCompact_Icc.image (hβc j)).isClosed
        · exact (isCompact_iUnion fun j : {j : Fin r // slt j 1 ≠ p} =>
            isCompact_Icc.image (hsltc j.1)).isClosed
      have hZarc : ∀ i : Fin k, α₀ i '' Set.Icc (0:ℝ) 1 ⊆ Z := by
        intro i x hx
        rw [hZdef]
        exact Or.inl (Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨i, hx⟩)))
      have hZβ : ∀ j : Fin m, β j '' Set.Icc (0:ℝ) 1 ⊆ Z := by
        intro j x hx
        rw [hZdef]
        exact Or.inl (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨j, hx⟩)))
      have hZslt : ∀ j : Fin r, slt j 1 ≠ p → slt j '' Set.Icc (0:ℝ) 1 ⊆ Z := by
        intro j hj x hx
        rw [hZdef]
        exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hx⟩))
      have hZFa : Fa ⊆ Z := by intro x hx; rw [hZdef]; exact Or.inr hx
      have hZR : R \ {p} ⊆ Z := (hRsub.trans hFp_sub).trans hZFa
      have hpZ : p ∉ Z := by
        rw [hZdef]
        intro hmem
        rcases hmem with h | h
        · rcases h with h | h
          · rcases h with h | h
            · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
              exact hp_arc i hi
            · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
              exact hp_β j hj
          · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
            exact hnotslt j.1 j.2 hj
        · exact hpFa h
      -- the entry ball
      set B : Set M := (connectedComponentIn (Pᶜ) p ∩ interior L) \ Z with hBdef
      have hBopen : IsOpen B := (hCxopen.inter isOpen_interior).sdiff hZclosed
      have hpB : p ∈ B := by
        rw [hBdef]
        exact ⟨⟨mem_connectedComponentIn hpP, hpsint⟩, hpZ⟩
      have hBsub : B ⊆ connectedComponentIn (Pᶜ) p := by
        intro x hx; rw [hBdef] at hx; exact hx.1.1
      have hBL : B ⊆ L := by
        intro x hx; rw [hBdef] at hx; exact interior_subset hx.1.2
      have hBZ : ∀ {x : M}, x ∈ B → x ∉ Z := by intro x hx; rw [hBdef] at hx; exact hx.2
      -- the side arc from `p` into the carrier
      obtain ⟨y, hyB, hyp, κ, hκc, hκi, hκ0, hκ1, hκB, hκav⟩ :=
        exists_side_arc_of_arc_end (n := n) hn (hsltc j0) (hsltinj j0) hj0 hBopen hpB
      have hyCx : y ∈ connectedComponentIn (Pᶜ) p := hBsub hyB
      have hyint : y ∈ interior L := by
        rw [hBdef] at hyB; exact hyB.1.2
      have hyZ : y ∉ Z := hBZ hyB
      have hyFa : y ∉ Fa := fun h => hyZ (hZFa h)
      have hyO : y ∈ O := by
        rw [hOdef]
        refine ⟨hyCx, ?_⟩
        intro hmem
        rcases hmem with h | h
        · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
          obtain ⟨x, hx, hxeq⟩ := hi
          exact hyZ (hZarc i ⟨x, ⟨hx.1, le_trans hx.2 (hOld.sigma_mem i).2.le⟩, hxeq⟩)
        · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
          obtain ⟨x, hx, hxeq⟩ := hj
          by_cases hjp : slt j 1 = p
          · have hjj : j = j0 := huniq j hjp
            rw [hjj] at hxeq
            rcases hκav 1 ⟨zero_le_one, le_rfl⟩ x ⟨hx.1.le, hx.2⟩ with hne | heq
            · exact hne (by rw [hκ1, ← hxeq])
            · exact hyp (hκ1 ▸ heq)
          · exact hyZ (hxeq ▸ hZslt j hjp ⟨x, ⟨hx.1.le, hx.2⟩, rfl⟩)
      -- the level arc from `y`
      obtain ⟨α', σ', hα'c, hα'i, hα'0, hα'σI, hα'L, hα'nL, hα'U, hα'Sh1, hα'U1, hα'F1, hα'CU,
        hα'F, hα'β, hα'σ0, hα'σ1, hα'Sh⟩ :=
        exists_level_arc_of_collar_shell (n := n) (C := O) (K := K) (L := L) (U := U)
          (Shell := Shell) (F := Fa) (β := β') hn hOopen hOpre hLc hKc hLK hUo hUL hShellO
          hfrontShell hpieces hyO hyint hOnt hFa_fin hyFa hβ'c hβ'sub hβ'0 hβ'front
      have hκBL : κ '' Set.Icc (0:ℝ) 1 ⊆ L := by
        rintro x ⟨t, ht, rfl⟩
        exact hBL (hκB t ht)
      have hα'ne_p : ∀ t ∈ Set.Icc (0:ℝ) 1, α' t ≠ p := by
        intro t ht hc
        rcases hα'CU t ht with h | h
        · rw [hc] at h
          rw [hOdef] at h
          exact h.2 (Or.inr (Set.mem_iUnion.mpr ⟨j0, ⟨1, ⟨by norm_num, le_rfl⟩, hj0⟩⟩))
        · rw [hc] at h
          exact Set.disjoint_left.mp hUL h (interior_subset hpsint)
      -- the trimming
      set T : Set ℝ := {t | t ∈ Set.Icc (0:ℝ) 1 ∧ α' t ∈ κ '' Set.Icc (0:ℝ) 1} with hTdef
      have hTne : T.Nonempty :=
        ⟨0, ⟨⟨le_rfl, zero_le_one⟩, by rw [hα'0, ← hκ1]; exact ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩⟩⟩
      have hTcl : IsClosed T := by
        rw [hTdef]
        exact isClosed_Icc.inter ((isCompact_Icc.image hκc).isClosed.preimage hα'c)
      have hTbdd : BddAbove T := ⟨1, fun t ht => ht.1.2⟩
      have hτmem : sSup T ∈ T := hTcl.csSup_mem hTne hTbdd
      set τ : ℝ := sSup T with hτdef
      have hτI : τ ∈ Set.Icc (0:ℝ) 1 := hτmem.1
      have hτκ : α' τ ∈ κ '' Set.Icc (0:ℝ) 1 := hτmem.2
      have hmax : ∀ t ∈ Set.Icc (0:ℝ) 1, τ < t → α' t ∉ κ '' Set.Icc (0:ℝ) 1 := by
        intro t ht hlt hmem
        have h1 : t ∈ T := ⟨ht, hmem⟩
        have h2 : t ≤ sSup T := le_csSup hTbdd h1
        rw [hτdef] at hlt
        exact absurd h2 (not_le.mpr hlt)
      have hτκ' : α' τ ∈ κ '' Set.Icc (0:ℝ) 1 := hτκ
      obtain ⟨t₀, ht₀I, ht₀eq⟩ := hτκ
      have hτlt : τ < 1 := by
        by_contra h
        have h1 : τ = 1 := le_antisymm hτI.2 (not_lt.mp h)
        have hL : α' τ ∈ L := hκBL hτκ'
        rw [h1] at hL
        exact Set.disjoint_left.mp hUL hα'U1 hL
      have hτleσ : τ ≤ σ' := by
        by_contra h
        exact (hα'nL τ ⟨not_le.mp h, hτI.2⟩) (hκBL hτκ')
      have ht₀pos : 0 < t₀ := by
        rcases lt_or_eq_of_le ht₀I.1 with h | h
        · exact h
        · exact absurd (by rw [← h, hκ0] at ht₀eq; exact ht₀eq.symm) (hα'ne_p τ hτI)
      obtain ⟨w, hwc, hwi, hw0, hw1, hwhalf, hwform, hwne⟩ :=
        trim_arc hκc hκi hκ0 hκ1 hα'c hα'i hα'0 ht₀eq ht₀I hτI ht₀pos hτlt hmax hα'ne_p
      have hwhalfB : ∀ u ∈ Set.Icc (0:ℝ) (1/2), w u ∈ B := by
        rintro u hu
        obtain ⟨t, ht, htw⟩ := hwhalf u hu
        rw [← htw]
        exact hκB t ht
      have h1τ : 0 < 1 - τ := by linarith
      have hden : 0 < 2 * (1 - τ) := by linarith
      set σnew : ℝ := 1/2 + (σ' - τ) / (2 * (1 - τ)) with hσnewdef
      have hσnew_ge : (1/2:ℝ) ≤ σnew := by
        rw [hσnewdef]
        have h2 : 0 ≤ (σ' - τ) / (2 * (1 - τ)) := div_nonneg (by linarith) hden.le
        linarith
      have hσnew_lt : σnew < 1 := by
        rw [hσnewdef]
        have h2 : (σ' - τ) / (2 * (1 - τ)) < 1/2 := by
          rw [div_lt_iff₀ hden]
          nlinarith [hα'σ1, hτI.1]
        linarith
      have hσnewI : σnew ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, hσnew_lt⟩
      have hkey_v : ∀ u : ℝ, (1/2:ℝ) ≤ u → (τ + (2*u-1)*(1-τ) ≤ σ' ↔ u ≤ σnew) := by
        intro u hu
        have e1 : τ + (2*u-1)*(1-τ) ≤ σ' ↔ (2*u-1)*(1-τ) ≤ σ' - τ := by
          constructor <;> intro h <;> linarith
        have e2 : (2*u-1)*(1-τ) ≤ σ' - τ ↔ 2*u-1 ≤ (σ'-τ)/(1-τ) :=
          (le_div_iff₀ h1τ).symm
        have e3 : (2*u-1 ≤ (σ'-τ)/(1-τ)) ↔ (u - 1/2 ≤ (σ'-τ)/(2*(1-τ))) := by
          constructor
          · intro h
            rw [le_div_iff₀ hden]
            have h' := mul_le_mul_of_nonneg_right h h1τ.le
            rw [div_mul_cancel₀ _ (ne_of_gt h1τ)] at h'
            nlinarith [h']
          · intro h
            rw [le_div_iff₀ h1τ]
            rw [le_div_iff₀ hden] at h
            nlinarith [h]
        have e4 : (u - 1/2 ≤ (σ'-τ)/(2*(1-τ))) ↔ u ≤ σnew := by
          rw [hσnewdef]; constructor <;> intro h <;> linarith
        exact e1.trans (e2.trans (e3.trans e4))
      have hkey_v' : ∀ u : ℝ, (1/2:ℝ) ≤ u → (σ' < τ + (2*u-1)*(1-τ) ↔ σnew < u) := by
        intro u hu
        rw [← not_le, ← not_le]
        exact not_congr (hkey_v u hu)
      have hvIcc : ∀ u ∈ Set.Icc (1/2:ℝ) 1,
          τ + (2*u-1)*(1-τ) ∈ Set.Icc (0:ℝ) 1 := by
        intro u hu
        constructor
        · nlinarith [hu.1, hτI.1, h1τ]
        · nlinarith [hu.2, hτI.1, h1τ]
      refine ⟨w, σnew, hwc, hwi, hw0, hσnewI, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_⟩
      · -- inside `L`
        intro u hu
        rcases le_or_gt u (1/2) with h | h
        · exact hκBL (hwhalf u ⟨hu.1, h⟩)
        · rw [hwform u ⟨le_of_lt h, le_trans hu.2 hσnew_lt.le⟩]
          exact hα'L _ ⟨by nlinarith [hτI.1, h1τ], (hkey_v u (le_of_lt h)).mpr hu.2⟩
      · -- outside `L`
        intro u hu
        have h2 : (1/2:ℝ) < u := lt_of_le_of_lt hσnew_ge hu.1
        rw [hwform u ⟨le_of_lt h2, hu.2⟩]
        exact hα'nL _ ⟨(hkey_v' u (le_of_lt h2)).mpr hu.1,
          (hvIcc u ⟨le_of_lt h2, hu.2⟩).2⟩
      · -- in `U`
        intro u hu
        have h2 : (1/2:ℝ) < u := lt_of_le_of_lt hσnew_ge hu.1
        rw [hwform u ⟨le_of_lt h2, hu.2⟩]
        exact hα'U _ ⟨(hkey_v' u (le_of_lt h2)).mpr hu.1,
          (hvIcc u ⟨le_of_lt h2, hu.2⟩).2⟩
      · -- in `Shell`
        intro u hu
        have h2 : (1/2:ℝ) < u := lt_of_le_of_lt hσnew_ge hu.1
        rw [hwform u ⟨le_of_lt h2, hu.2⟩]
        exact hα'Sh _ ⟨(hkey_v' u (le_of_lt h2)).mpr hu.1,
          (hvIcc u ⟨le_of_lt h2, hu.2⟩).2⟩
      · rw [hw1]; exact hα'Sh1
      · rw [hw1]; exact hα'U1
      · rw [hw1]; exact fun h => hα'F1 (hFp_sub h)
      · -- in `Cx ∪ U`
        intro u hu
        rcases le_or_gt u (1/2) with h | h
        · exact Or.inl (hBsub (hwhalfB u ⟨hu.1, h⟩))
        · rw [hwform u ⟨le_of_lt h, hu.2⟩]
          rcases hα'CU _ (hvIcc u ⟨le_of_lt h, hu.2⟩) with h' | h'
          · exact Or.inl (hOsub h')
          · exact Or.inr h'
      · -- in `Cx` up to the exit
        intro u hu
        rcases le_or_gt u (1/2) with h | h
        · exact hBsub (hwhalfB u ⟨hu.1, h⟩)
        · have hu1 : u ≤ 1 := le_trans hu.2 hσnew_lt.le
          have hv := hvIcc u ⟨le_of_lt h, hu1⟩
          have hvL : α' _ ∈ L := hα'L _ ⟨hv.1, (hkey_v u (le_of_lt h)).mpr hu.2⟩
          rw [hwform u ⟨le_of_lt h, hu1⟩]
          rcases hα'CU _ hv with h' | h'
          · exact hOsub h'
          · exact absurd hvL (fun hL => Set.disjoint_left.mp hUL h' hL)
      · -- avoids `Fp`
        intro u hu
        rcases le_or_gt u (1/2) with h | h
        · intro hx
          exact hBZ (hwhalfB u ⟨hu.1, h⟩) (hZFa (hFp_sub hx))
        · rw [hwform u ⟨le_of_lt h, hu.2⟩]
          intro hx
          exact hα'F _ (hvIcc u ⟨le_of_lt h, hu.2⟩) (hFp_sub hx)
      · -- avoids the obstacles `β`
        intro u hu j
        rcases le_or_gt u (1/2) with h | h
        · intro hx
          exact hBZ (hwhalfB u ⟨hu.1, h⟩) (hZβ j hx)
        · rw [hwform u ⟨le_of_lt h, hu.2⟩]
          intro hx
          refine hα'β _ (hvIcc u ⟨le_of_lt h, hu.2⟩) (Fin.castAdd k j) ?_
          rw [hβ'def, Fin.append_left]
          exact hx
      · -- avoids the other slits
        intro u hu j hj
        rcases le_or_gt u (1/2) with h | h
        · intro hx
          exact hBZ (hwhalfB u ⟨hu.1, h⟩) (hZslt j hj hx)
        · rw [hwform u ⟨le_of_lt h, hu.2⟩]
          intro hx
          rcases hα'CU _ (hvIcc u ⟨le_of_lt h, hu.2⟩) with h' | h'
          · rw [hOdef] at h'
            obtain ⟨x, hxI, hxeq⟩ := hx
            rcases eq_or_lt_of_le hxI.2 with heq | hlt
            · have hmemFa : slt j 1 ∈ Fa := hFp_sub (hRsub ⟨hsltR j, hj⟩)
              exact hα'F _ (hvIcc u ⟨le_of_lt h, hu.2⟩)
                (by rw [← hxeq, heq]; exact hmemFa)
            · rcases eq_or_lt_of_le hxI.1 with h0 | h0
              · refine absurd (connectedComponentIn_subset (Pᶜ) p h'.1) ?_
                intro hc
                exact hsltroot j (by rw [h0, hxeq]; exact hc)
              · exact h'.2 (Or.inr (hxeq ▸ (Set.mem_iUnion.mpr
                  ⟨j, ⟨x, ⟨h0, hlt.le⟩, rfl⟩⟩)))
          · exact Set.disjoint_left.mp (hsltU j) hx h'
      · -- avoids its own slit
        intro u hu j hj
        have hjj : j = j0 := huniq j hj
        rcases le_or_gt u (1/2) with h | h
        · intro hx
          have hwκ : w u ∈ κ '' Set.Icc (0:ℝ) 1 := hwhalf u ⟨hu.1.le, h⟩
          have hne : w u ≠ p := hwne u ⟨hu.1, hu.2.le⟩
          obtain ⟨s, hs, hseq⟩ := hwκ
          obtain ⟨t, ht, ht2⟩ := hx
          rcases hκav s hs t ht with hne2 | heq
          · exact hne2 (hjj ▸ (hseq.trans ht2.symm))
          · exact hne (hseq.symm.trans heq)
        · have hu1 : u ≤ 1 := hu.2.le
          rw [hwform u ⟨le_of_lt h, hu1⟩]
          intro hx
          rw [hjj] at hx
          rcases hα'CU _ (hvIcc u ⟨le_of_lt h, hu1⟩) with h' | h'
          · rw [hOdef] at h'
            obtain ⟨x, hxI, hxeq⟩ := hx
            rcases eq_or_lt_of_le hxI.2 with heq | hlt
            · exact hα'ne_p _ (hvIcc u ⟨le_of_lt h, hu1⟩)
                (by rw [← hxeq, heq]; exact hj0)
            · rcases eq_or_lt_of_le hxI.1 with h0 | h0
              · refine absurd (connectedComponentIn_subset (Pᶜ) p h'.1) ?_
                intro hc
                exact hsltroot j0 (by rw [h0, hxeq]; exact hc)
              · exact h'.2 (Or.inr (hxeq ▸ (Set.mem_iUnion.mpr
                  ⟨j0, ⟨x, ⟨h0, hlt.le⟩, rfl⟩⟩)))
          · exact Set.disjoint_left.mp (hsltU j0) hx h'
      · -- disjoint from the old arcs
        intro i
        rw [Set.disjoint_left]
        rintro z ⟨u, hu, rfl⟩ ⟨x, hx, hxeq⟩
        rcases le_or_gt u (1/2) with h | h
        · have hzZ : w u ∉ Z := hBZ (hwhalfB u ⟨hu.1, h⟩)
          refine hzZ (hZarc i ?_)
          rw [← hxeq]
          exact ⟨x, hx, rfl⟩
        · rw [hwform u ⟨le_of_lt h, hu.2⟩] at hxeq
          rcases hα'CU _ (hvIcc u ⟨le_of_lt h, hu.2⟩) with h' | h'
          · rw [hOdef] at h'
            rcases lt_or_ge x (σ₀ i) with hlt | hge
            · exact h'.2 (Or.inl (Set.mem_iUnion.mpr ⟨i, ⟨x, ⟨hx.1, hlt.le⟩, hxeq⟩⟩))
            · refine hα'β _ (hvIcc u ⟨le_of_lt h, hu.2⟩) (Fin.natAdd m i) ?_
              rw [hβ'def, Fin.append_right, ← Set.image_image, hβ'imgIcc i]
              exact ⟨x, ⟨hge, hx.2⟩, hxeq⟩
          · rcases lt_or_ge x (σ₀ i) with hlt | hge
            · have hL : α₀ i x ∈ L := hOld.inside_mem i x ⟨hx.1, hlt.le⟩
              rw [hxeq] at hL
              exact Set.disjoint_left.mp hUL h' hL
            · refine hα'β _ (hvIcc u ⟨le_of_lt h, hu.2⟩) (Fin.natAdd m i) ?_
              rw [hβ'def, Fin.append_right, ← Set.image_image, hβ'imgIcc i]
              exact ⟨x, ⟨hge, hx.2⟩, hxeq⟩
      · -- avoids the other start points
        intro u hu
        rcases le_or_gt u (1/2) with h | h
        · intro hx
          exact hBZ (hwhalfB u ⟨hu.1, h⟩) (hZR hx)
        · rw [hwform u ⟨le_of_lt h, hu.2⟩]
          intro hx
          exact hα'F _ (hvIcc u ⟨le_of_lt h, hu.2⟩) (hRsub.trans hFp_sub hx)
    · -- Case A: no slit ends at `p`; the carrier already contains `p`.
      have hp_sltIoc : ∀ j : Fin r, p ∉ slt j '' Set.Ioc (0:ℝ) 1 := by
        intro j hmem
        exact hnotslt j (fun hc => hown ⟨j, hc⟩) (Set.image_mono Set.Ioc_subset_Icc_self hmem)
      have hpO : p ∈ O := by
        rw [hOdef]
        refine ⟨mem_connectedComponentIn hpP, ?_⟩
        intro hmem
        rcases hmem with h | h
        · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
          exact hp_ins i hi
        · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
          exact hp_sltIoc j hj
      obtain ⟨anew, σnew, hnewc, hnewi, hnew0, hnewσI, hnewL, hnewnL, hnewU, hnewSh1, hnewU1,
        hnewF1, hnewCU, hnewF, hnewβ, hnewσ0, hnewσ1, hnewSh⟩ :=
        exists_level_arc_of_collar_shell (n := n) (C := O) (K := K) (L := L) (U := U)
          (Shell := Shell) (F := Fa) (β := β') hn hOopen hOpre hLc hKc hLK hUo hUL hShellO
          hfrontShell hpieces hpO hpsint hOnt hFa_fin hpFa hβ'c hβ'sub hβ'0 hβ'front
      have hslt_other : ∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j : Fin r, slt j 1 ≠ p →
          anew u ∉ slt j '' Set.Icc (0:ℝ) 1 := by
        intro u hu j hj hmem
        rcases hnewCU u hu with h | h
        · rw [hOdef] at h
          obtain ⟨x, hx, hxeq⟩ := hmem
          rcases eq_or_lt_of_le hx.2 with heq | hlt
          · have hmemFa : slt j 1 ∈ Fa := hFp_sub (hRsub ⟨hsltR j, hj⟩)
            exact hnewF u hu (by rw [← hxeq, heq]; exact hmemFa)
          · rcases eq_or_lt_of_le hx.1 with h0 | h0
            · refine absurd (connectedComponentIn_subset (Pᶜ) p h.1) ?_
              intro hc
              exact hsltroot j (by rw [h0, hxeq]; exact hc)
            · exact h.2 (Or.inr (hxeq ▸ (Set.mem_iUnion.mpr
                ⟨j, ⟨x, ⟨h0, hlt.le⟩, rfl⟩⟩)))
        · exact Set.disjoint_left.mp (hsltU j) hmem h
      have hslt_own : ∀ u ∈ Set.Ioo (0:ℝ) 1, ∀ j : Fin r, slt j 1 = p →
          anew u ∉ slt j '' Set.Icc (0:ℝ) 1 := by
        intro u hu j hj
        exact absurd hj (fun hc => hown ⟨j, hc⟩)
      have hdisj : ∀ i : Fin k,
          Disjoint (anew '' Set.Icc (0:ℝ) 1) (α₀ i '' Set.Icc (0:ℝ) 1) := by
        intro i
        rw [Set.disjoint_left]
        rintro z ⟨u, hu, rfl⟩ ⟨x, hx, hxeq⟩
        rcases lt_or_ge x (σ₀ i) with hlt | hge
        · rcases hnewCU u hu with h | h
          · rw [hOdef] at h
            exact h.2 (Or.inl (Set.mem_iUnion.mpr ⟨i, ⟨x, ⟨hx.1, hlt.le⟩, hxeq⟩⟩))
          · have hL : α₀ i x ∈ L := hOld.inside_mem i x ⟨hx.1, hlt.le⟩
            rw [hxeq] at hL
            exact Set.disjoint_left.mp hUL h hL
        · refine hnewβ u hu (Fin.natAdd m i) ?_
          rw [hβ'def, Fin.append_right, ← Set.image_image, hβ'imgIcc i]
          exact ⟨x, ⟨hge, hx.2⟩, hxeq⟩
      refine ⟨anew, σnew, hnewc, hnewi, hnew0, ⟨hnewσ0, hnewσ1⟩, hnewL, hnewnL, hnewU, hnewSh,
        hnewSh1, hnewU1, fun h => hnewF1 (hFp_sub h), ?_, ?_, fun u hu h => hnewF u hu (hFp_sub h),
        ?_, hslt_other, hslt_own, hdisj, ?_⟩
      · intro u hu
        rcases hnewCU u hu with h | h
        · exact Or.inl (hOsub h)
        · exact Or.inr h
      · intro u hu
        rcases hnewCU u ⟨hu.1, le_trans hu.2 hnewσ1.le⟩ with h | h
        · exact hOsub h
        · exact absurd (hnewL u hu) (fun hL => Set.disjoint_left.mp hUL h hL)
      · intro u hu j
        refine fun hx => hnewβ u hu (Fin.castAdd k j) ?_
        rw [hβ'def, Fin.append_left]
        exact hx
      · intro u hu hx
        exact hnewF u hu (hRsub.trans hFp_sub hx)
  obtain ⟨anew, σnew, hnewc, hnewi, hnew0, hnewσ, hnewL, hnewnL, hnewU, hnewSh, hnewSh1,
    hnewU1, hnewFp1, hnewCU, hnewCx, hnewFp, hnewβ, hnew_sltother, hnew_sltown, hnew_disj,
    hnewR⟩ := key
  -- assembly
  refine ⟨Fin.snoc α₀ anew, Fin.snoc σ₀ σnew, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using hOld.cont j
    · simpa only [Fin.snoc_last] using hnewc
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using hOld.injOn j
    · simpa only [Fin.snoc_last] using hnewi
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using hOld.zero j
    · simpa only [Fin.snoc_last] using hnew0
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using hOld.sigma_mem j
    · simpa only [Fin.snoc_last] using hnewσ
  · intro i u hu
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using
        hOld.inside_mem j u (by simpa only [Fin.snoc_castSucc] using hu)
    · simpa only [Fin.snoc_last] using hnewL u (by simpa only [Fin.snoc_last] using hu)
  · intro i u hu
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using
        hOld.outside_notMem j u (by simpa only [Fin.snoc_castSucc] using hu)
    · simpa only [Fin.snoc_last] using hnewnL u (by simpa only [Fin.snoc_last] using hu)
  · intro i u hu
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using
        hOld.outside_mem_U j u (by simpa only [Fin.snoc_castSucc] using hu)
    · simpa only [Fin.snoc_last] using hnewU u (by simpa only [Fin.snoc_last] using hu)
  · intro i u hu
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using
        hOld.outside_mem_Shell j u (by simpa only [Fin.snoc_castSucc] using hu)
    · simpa only [Fin.snoc_last] using hnewSh u (by simpa only [Fin.snoc_last] using hu)
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using hOld.tip_mem_Shell j
    · simpa only [Fin.snoc_last] using hnewSh1
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using hOld.tip_mem_U j
    · simpa only [Fin.snoc_last] using hnewU1
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using hOld.tip_notMem j
    · simpa only [Fin.snoc_last] using hnewFp1
  · intro i u hu
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using
        hOld.arc_subset j u (by simpa only [Fin.snoc_castSucc] using hu)
    · simpa only [Fin.snoc_last] using hnewCU u hu
  · intro i u hu
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using
        hOld.inside_mem_comp j u (by simpa only [Fin.snoc_castSucc] using hu)
    · simpa only [Fin.snoc_last] using hnewCx u (by simpa only [Fin.snoc_last] using hu)
  · intro i u hu
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using
        hOld.arc_notMem j u (by simpa only [Fin.snoc_castSucc] using hu)
    · simp only [Fin.snoc_last]
      exact hnewFp u hu
  · intro i u hu j
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j', rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using hOld.arc_avoids_β j' u hu j
    · simp only [Fin.snoc_last]
      exact hnewβ u hu j
  · intro i u hu j hne
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j', rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using
        hOld.arc_avoids_slt_other j' u hu j (by simpa only [Fin.snoc_castSucc] using hne)
    · simp only [Fin.snoc_last] at hne ⊢
      exact hnew_sltother u hu j hne
  · intro i u hu j hcl
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j', rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using
        hOld.arc_avoids_slt_own j' u hu j (by simpa only [Fin.snoc_castSucc] using hcl)
    · simp only [Fin.snoc_last] at hcl ⊢
      exact hnew_sltown u hu j hcl
  · intro i i' hne
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last i' with ⟨j', rfl⟩ | rfl
      · simpa only [Fin.snoc_castSucc] using hOld.pair_disjoint j j'
          (fun hc => hne (congrArg Fin.castSucc hc))
      · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using (hnew_disj j).symm
    · rcases Fin.eq_castSucc_or_eq_last i' with ⟨j', rfl⟩ | rfl
      · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hnew_disj j'
      · exact absurd rfl hne
  · intro i u hu
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa only [Fin.snoc_castSucc] using
        hOld.start_avoid j u (by simpa only [Fin.snoc_castSucc] using hu)
    · simp only [Fin.snoc_last]
      exact hnewR u hu

lemma snoc_castLE_eq {K k : ℕ} {M : Type*} {s : Fin K → M} (hk : k + 1 ≤ K) :
    Fin.snoc (fun i : Fin k => s (Fin.castLE (Nat.le_of_succ_le hk) i)) (s ⟨k, hk⟩) =
      (fun i : Fin (k+1) => s (Fin.castLE hk i)) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]
    exact congrArg s (Fin.ext rfl)
  · rw [Fin.snoc_last]
    exact congrArg s (Fin.ext rfl)

/-- The peel, for the prefixes of a level with `K` strands. -/
theorem exists_prefix_peel {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {P L Kset U Shell : Set M} (hPc : IsClosed P)
    (hPpf : ∀ x : M, x ∉ P → ¬ IsCompact (closure (connectedComponentIn (Pᶜ) x)))
    (hLc : IsClosed L) (hKc : IsCompact Kset) (hLK : L ⊆ Kset)
    (hUo : IsOpen U) (hUL : Disjoint U L)
    (hShellO : IsOpen Shell) (hfrontShell : frontier L ⊆ Shell)
    (hpieces : ∀ z ∈ frontier L, ∃ (x : M) (b : Work.Whitney.PathTools.ChartBall n M Set.univ x),
      z ∈ b.K ∧ b.c.symm '' Metric.ball (b.c x) b.ρ ⊆ U)
    {K : ℕ} {s : Fin K → M} (hsinj : Function.Injective s)
    (hsint : ∀ i, s i ∈ interior L) (hsP : ∀ i, s i ∉ P)
    {F : Fin K → Set M} (hF : ∀ i, (F i).Finite) (hsF : ∀ i, s i ∉ F i)
    (hFs : ∀ i i', i ≠ i' → s i' ∈ F i)
    {m : ℕ} {β : Fin m → ℝ → M} (hβc : ∀ j, Continuous (β j))
    (hβsub : ∀ j, β j '' Set.Ioc (0:ℝ) 1 ⊆ U)
    (hβ0F : ∀ i j, β j 0 ∈ F i)
    (hβfront : ∀ i j, ∀ z ∈ frontier L, z ∈ closure (β j '' Set.Icc (0:ℝ) 1) → z ∈ F i)
    {r : ℕ} {slt : Fin r → ℝ → M} (hsltc : ∀ j, Continuous (slt j))
    (hsltinj : ∀ j, Set.InjOn (slt j) (Set.Icc (0:ℝ) 1))
    (hsltbody : ∀ j, slt j '' Set.Ioc (0:ℝ) 1 ⊆ Pᶜ)
    (hsltroot : ∀ j, slt j 0 ∉ Pᶜ)
    (hsltU : ∀ j, Disjoint (slt j '' Set.Icc (0:ℝ) 1) U)
    (hsltdisj : ∀ j j', j ≠ j' →
      Disjoint (slt j '' Set.Icc (0:ℝ) 1) (slt j' '' Set.Icc (0:ℝ) 1))
    {clip : Fin r → Fin K} (hclip : ∀ j, slt j 1 = s (clip j))
    (hsnotslt : ∀ i j, clip j ≠ i → s i ∉ slt j '' Set.Icc (0:ℝ) 1)
    (k : ℕ) (hk : k ≤ K) :
    ∃ (α : Fin k → ℝ → M) (σ : Fin k → ℝ),
      PeelPrefix P L U Shell (Set.range s) (fun i => s (Fin.castLE hk i))
        (fun i => F (Fin.castLE hk i)) β slt α σ := by
  induction k with
  | zero =>
    refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨α₀, σ₀, hOld⟩ := ih (Nat.le_of_succ_le hk)
    let ık : Fin K := ⟨k, hk⟩
    have hgp : ∀ i : Fin k, s (Fin.castLE (Nat.le_of_succ_le hk) i) ≠ s ık := by
      intro i h
      have h1 : Fin.castLE (Nat.le_of_succ_le hk) i = ık := hsinj h
      have h2 : (Fin.castLE (Nat.le_of_succ_le hk) i).val = ık.val := congrArg Fin.val h1
      simp only [Fin.val_castLE, ık, Fin.val_mk] at h2
      omega
    have hRsub : Set.range s \ {s ık} ⊆ F ık := by
      rintro x ⟨⟨i, rfl⟩, hx⟩
      have hne : i ≠ ık := fun hc => hx (by simp [hc])
      exact hFs ık i (Ne.symm hne)
    have hsltR : ∀ j : Fin r, slt j 1 ∈ Set.range s := fun j => ⟨clip j, (hclip j).symm⟩
    obtain ⟨α, σ, hNew⟩ := peel_step (n := n) hn hPc hPpf hLc hKc hLK hUo hUL hShellO
      hfrontShell hpieces hOld ⟨ık, rfl⟩ hgp (hsP ık) (hsint ık) hsltc hsltinj hsltbody
      hsltroot hsltdisj hsltU hsltR
      (fun j hj => hsnotslt ık j (fun hc => hj (by rw [hclip j, hc]))) (hF ık) (hsF ık) hRsub
      hβc hβsub (fun j => hβ0F ık j) (fun j z hz hzcl => hβfront ık j z hz hzcl)
    refine ⟨α, σ, ?_⟩
    have hık : ık = (⟨k, hk⟩ : Fin K) := rfl
    rw [hık, snoc_castLE_eq (s := s) hk, snoc_castLE_eq (s := F) hk] at hNew
    exact hNew

/-- **The peel lemma.** -/
theorem peel_arcs {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {P L K U Shell : Set M} (hPc : IsClosed P)
    (hPpf : ∀ x : M, x ∉ P → ¬ IsCompact (closure (connectedComponentIn (Pᶜ) x)))
    (hLc : IsClosed L) (hKc : IsCompact K) (hLK : L ⊆ K)
    (hUo : IsOpen U) (hUL : Disjoint U L)
    (hShellO : IsOpen Shell) (hfrontShell : frontier L ⊆ Shell)
    (hpieces : ∀ z ∈ frontier L, ∃ (x : M) (b : Work.Whitney.PathTools.ChartBall n M Set.univ x),
      z ∈ b.K ∧ b.c.symm '' Metric.ball (b.c x) b.ρ ⊆ U)
    {k : ℕ} (s : Fin k → M) (hsint : ∀ i, s i ∈ interior L) (hsinj : Function.Injective s)
    (hsP : ∀ i, s i ∉ P)
    {F : Fin k → Set M} (hF : ∀ i, (F i).Finite) (hsF : ∀ i, s i ∉ F i)
    (hFs : ∀ i i', i ≠ i' → s i' ∈ F i)
    {r : ℕ} {slt : Fin r → ℝ → M} (hsltc : ∀ j, Continuous (slt j))
    (hsltinj : ∀ j, Set.InjOn (slt j) (Set.Icc (0:ℝ) 1))
    (hsltbody : ∀ j, slt j '' Set.Ioc (0:ℝ) 1 ⊆ Pᶜ)
    (hsltroot : ∀ j, slt j 0 ∉ Pᶜ)
    (hsltU : ∀ j, Disjoint (slt j '' Set.Icc (0:ℝ) 1) U)
    (hsltdisj : ∀ j j', j ≠ j' →
      Disjoint (slt j '' Set.Icc (0:ℝ) 1) (slt j' '' Set.Icc (0:ℝ) 1))
    (clip : Fin r → Fin k) (hclip : ∀ j, slt j 1 = s (clip j))
    (hsnotslt : ∀ i j, clip j ≠ i → s i ∉ slt j '' Set.Icc (0:ℝ) 1)
    {m : ℕ} {β : Fin m → ℝ → M} (hβc : ∀ j, Continuous (β j))
    (hβsub : ∀ j, β j '' Set.Ioc (0:ℝ) 1 ⊆ U)
    (hβ0F : ∀ i j, β j 0 ∈ F i)
    (hβfront : ∀ i j, ∀ z ∈ frontier L, z ∈ closure (β j '' Set.Icc (0:ℝ) 1) → z ∈ F i) :
    ∃ (α : Fin k → ℝ → M) (σ : Fin k → ℝ),
      (∀ i, Continuous (α i)) ∧ (∀ i, Set.InjOn (α i) (Set.Icc (0:ℝ) 1)) ∧
      (∀ i, α i 0 = s i) ∧ (∀ i, σ i ∈ Set.Ioo (0:ℝ) 1) ∧
      (∀ i u, u ∈ Set.Icc (0:ℝ) (σ i) → α i u ∈ L) ∧
      (∀ i u, u ∈ Set.Ioc (σ i) 1 → α i u ∉ L) ∧
      (∀ i u, u ∈ Set.Ioc (σ i) 1 → α i u ∈ U) ∧
      (∀ i u, u ∈ Set.Ioc (σ i) 1 → α i u ∈ Shell) ∧
      (∀ i, α i 1 ∈ Shell) ∧ (∀ i, α i 1 ∈ U) ∧ (∀ i, α i 1 ∉ F i) ∧
      (∀ i u, u ∈ Set.Icc (0:ℝ) 1 → α i u ∈ connectedComponentIn (Pᶜ) (s i) ∪ U) ∧
      (∀ i u, u ∈ Set.Icc (0:ℝ) (σ i) → α i u ∈ connectedComponentIn (Pᶜ) (s i)) ∧
      (∀ i u, u ∈ Set.Icc (0:ℝ) 1 → α i u ∉ F i) ∧
      (∀ i u, u ∈ Set.Icc (0:ℝ) 1 → ∀ j, α i u ∉ β j '' Set.Icc (0:ℝ) 1) ∧
      (∀ i u, u ∈ Set.Icc (0:ℝ) 1 → ∀ j, clip j ≠ i → α i u ∉ slt j '' Set.Icc (0:ℝ) 1) ∧
      (∀ i u, u ∈ Set.Ioo (0:ℝ) 1 → ∀ j, clip j = i →
        α i u ∉ slt j '' Set.Icc (0:ℝ) 1) ∧
      (∀ i i', i ≠ i' → Disjoint (α i '' Set.Icc (0:ℝ) 1) (α i' '' Set.Icc (0:ℝ) 1)) ∧
      (∀ i i', i ≠ i' → ∀ u, u ∈ Set.Icc (0:ℝ) 1 → α i u ≠ s i') := by
  classical
  obtain ⟨α, σ, h⟩ := exists_prefix_peel (n := n) hn hPc hPpf hLc hKc hLK hUo hUL hShellO
    hfrontShell hpieces hsinj hsint hsP hF hsF hFs hβc hβsub hβ0F hβfront hsltc hsltinj
    hsltbody hsltroot hsltU hsltdisj hclip hsnotslt k le_rfl
  have hg : (fun i : Fin k => s (Fin.castLE (le_refl k) i)) = s := by
    funext i
    exact congrArg s (Fin.ext (by simp))
  have hFg : (fun i : Fin k => F (Fin.castLE (le_refl k) i)) = F := by
    funext i
    exact congrArg F (Fin.ext (by simp))
  rw [hg, hFg] at h
  refine ⟨α, σ, h.cont, h.injOn, h.zero, h.sigma_mem, h.inside_mem, h.outside_notMem,
    h.outside_mem_U, h.outside_mem_Shell, h.tip_mem_Shell, h.tip_mem_U, h.tip_notMem, h.arc_subset,
    h.inside_mem_comp, h.arc_notMem, h.arc_avoids_β, ?_, ?_, h.pair_disjoint, ?_⟩
  · intro i u hu j hne hmem
    exact h.arc_avoids_slt_other i u hu j (fun hc => hne (hsinj (by rw [← hclip j, hc]))) hmem
  · intro i u hu j hcl hmem
    exact h.arc_avoids_slt_own i u hu j (by rw [hclip j, hcl]) hmem
  · intro i i' hne u hu hpu
    exact h.start_avoid i u hu
      ⟨⟨i', hpu.symm⟩, fun hc => hne (hsinj (hpu.symm.trans hc)).symm⟩

end Work.Noncompact.CompressionTube
