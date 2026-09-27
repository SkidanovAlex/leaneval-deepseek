import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.CorridorDefs
import Submission.Work.Noncompact.CompressionTube.LaneData
import Submission.Work.Noncompact.CompressionTube.laneData
import Submission.Work.Noncompact.CompressionTube.corridorChain_of_spine
import Submission.Work.Noncompact.CompressionTube.thinPairwiseDisjointNhd
import Submission.Work.Noncompact.Routing.exists_arc_in_preconnected
import Submission.Work.Noncompact.Canals.ArcTool
import Submission.Work.Noncompact.Routing.exhaustion_tools

namespace Work.CompressionTube

open Set Topology

noncomputable section

/-!
# The corridor chain of a canal datum

The canal datum of the compression tube (`W` open preconnected, `K` a compact exhaustion of the
ambient manifold, `D` a nested family of open preconnected subsets of `W` escaping every level and
with non-compact closure, plus the seed points `b ∈ D N` and `z i ∈ D (N + i)`) determines a
*corridor chain* through `b` inside `W` together with the junction shape data and the spine arcs.

The construction is intrinsic: the canals `D j` all lie in a single component `E m` of `W \ K m`
(because they are preconnected and nested), and these components are *nested* and *escaping*.
Since `E m` is open preconnected in a manifold, any two of its points are joined by an arc inside
it, and a compact arc lies inside some `int K l`; hence from a junction `Q ∈ E α` one may pass to a
junction `Q' ∈ E α'` with `α'` large, using a corridor
`C = component of Q in E α ∩ interior (K β)`, and simultaneously arrange the interlacing of the
levels which makes non-adjacent corridors disjoint.  The junction shape facts (`Q i ∉ C (i+1)` and
the neighbourhood of `Q i` avoiding all `C k`, `k ≥ i+1`) come from the level bookkeeping, and the
spine arcs from the path connectedness of the corridors.
-/

/-! ## The `E`-filtration of a canal datum -/

/-- The base point of the level `m` of the `E`-filtration: a point of the canal `D (m+1)`. -/
def Ebase {M : Type*} (z : ℕ → M) (N m : ℕ) : M := z (m + 1 - N)

/-- `E m` is the component of `W \ K m` which carries the canals. -/
def Eset {M : Type*} [TopologicalSpace M] (K : ℕ → Set M) (W : Set M) (z : ℕ → M)
    (N m : ℕ) : Set M :=
  connectedComponentIn (W \ K m) (Ebase z N m)

/-- A decreasing sequence of sets is antitone. -/
lemma antitone_of_succ_subset {α : Type*} {D : ℕ → Set α} (h : ∀ i, D (i + 1) ⊆ D i) :
    Antitone D := by
  intro i j hij
  induction hij with
  | refl => exact subset_rfl
  | step hk ih => exact (h _).trans ih

/-- The base point of level `m` lies in the canal `D (m+1)`. -/
lemma Ebase_mem_D {M : Type*} {D : ℕ → Set M} {z : ℕ → M} {N : ℕ}
    (hzD : ∀ i, z i ∈ D (N + i)) (hDmono : ∀ i, D (i + 1) ⊆ D i) (m : ℕ) :
    Ebase z N m ∈ D (m + 1) := by
  simp only [Ebase]
  by_cases h : N ≤ m + 1
  · have h' : N + (m + 1 - N) = m + 1 := Nat.add_sub_cancel' h
    simpa only [h'] using hzD (m + 1 - N)
  · have hlt : m + 1 < N := Nat.lt_of_not_le h
    have h0 : m + 1 - N = 0 := Nat.sub_eq_zero_of_le (le_of_lt hlt)
    rw [h0]
    exact (antitone_of_succ_subset hDmono (le_of_lt hlt)) (by simpa using hzD 0)

/-- The base point of level `m` lies in `W \ K m`. -/
lemma Ebase_mem_sdiff {M : Type*} [TopologicalSpace M] {W : Set M} {K : ℕ → Set M}
    {D : ℕ → Set M} {z : ℕ → M} {N : ℕ}
    (hDW : ∀ i, D i ⊆ W) (hDK : ∀ i, D i ⊆ (K i)ᶜ)
    (hKsub : ∀ i, K i ⊆ interior (K (i + 1)))
    (hzD : ∀ i, z i ∈ D (N + i)) (hDmono : ∀ i, D (i + 1) ⊆ D i) (m : ℕ) :
    Ebase z N m ∈ W \ K m := by
  have h1 : Ebase z N m ∈ D (m + 1) := Ebase_mem_D hzD hDmono m
  refine ⟨hDW _ h1, fun hc => (hDK _ h1) ?_⟩
  exact (hKsub m).trans interior_subset hc

/-- The `E`-sets are open. -/
lemma isOpen_Eset {M : Type*} [TopologicalSpace M] [T2Space M] [LocallyConnectedSpace M]
    {W : Set M} {K : ℕ → Set M} {z : ℕ → M} {N : ℕ}
    (hWo : IsOpen W) (hKc : ∀ i, IsCompact (K i)) (m : ℕ) :
    IsOpen (Eset K W z N m) :=
  (hWo.sdiff (hKc m).isClosed).connectedComponentIn

/-- The `E`-sets are preconnected. -/
lemma isPreconnected_Eset {M : Type*} [TopologicalSpace M]
    {K : ℕ → Set M} {W : Set M} {z : ℕ → M} {N : ℕ} (m : ℕ) :
    IsPreconnected (Eset K W z N m) :=
  isPreconnected_connectedComponentIn

/-- The `E`-sets are contained in `W \ K m`. -/
lemma Eset_subset_sdiff {M : Type*} [TopologicalSpace M]
    {K : ℕ → Set M} {W : Set M} {z : ℕ → M} {N : ℕ} (m : ℕ) :
    Eset K W z N m ⊆ W \ K m :=
  connectedComponentIn_subset _ _

/-- Every canal of level at least `m + 1` lies in `E m`. -/
lemma D_subset_Eset {M : Type*} [TopologicalSpace M] {W : Set M} {K : ℕ → Set M}
    {D : ℕ → Set M} {z : ℕ → M} {N : ℕ}
    (hDpc : ∀ i, IsPreconnected (D i)) (hDW : ∀ i, D i ⊆ W)
    (hDK : ∀ i, D i ⊆ (K i)ᶜ) (hKsub : ∀ i, K i ⊆ interior (K (i + 1)))
    (hzD : ∀ i, z i ∈ D (N + i)) (hDmono : ∀ i, D (i + 1) ⊆ D i)
    {m j : ℕ} (hj : m + 1 ≤ j) : D j ⊆ Eset K W z N m := by
  have hKmono : K m ⊆ K (m + 1) := (hKsub m).trans interior_subset
  have hsub : D (m + 1) ⊆ W \ K m := by
    intro x hx
    exact ⟨hDW _ hx, fun hc => (hDK _ hx) (hKmono hc)⟩
  have hbase : Ebase z N m ∈ D (m + 1) := Ebase_mem_D hzD hDmono m
  exact (antitone_of_succ_subset hDmono hj).trans
    (IsPreconnected.subset_connectedComponentIn (hDpc (m + 1)) hbase hsub)

/-- The `E`-sets are nested. -/
lemma Eset_succ_subset {M : Type*} [TopologicalSpace M] {W : Set M} {K : ℕ → Set M}
    {D : ℕ → Set M} {z : ℕ → M} {N : ℕ}
    (hDpc : ∀ i, IsPreconnected (D i)) (hDW : ∀ i, D i ⊆ W)
    (hDK : ∀ i, D i ⊆ (K i)ᶜ) (hKsub : ∀ i, K i ⊆ interior (K (i + 1)))
    (hzD : ∀ i, z i ∈ D (N + i)) (hDmono : ∀ i, D (i + 1) ⊆ D i) (m : ℕ) :
    Eset K W z N (m + 1) ⊆ Eset K W z N m := by
  have hKmono : K m ⊆ K (m + 1) := (hKsub m).trans interior_subset
  have hsub : Eset K W z N (m + 1) ⊆ W \ K m := by
    intro x hx
    obtain ⟨h1, h2⟩ := Eset_subset_sdiff (K := K) (W := W) (z := z) (N := N) (m + 1) hx
    exact ⟨h1, fun hc => h2 (hKmono hc)⟩
  have hpt : Ebase z N (m + 1) ∈ Eset K W z N m :=
    D_subset_Eset hDpc hDW hDK hKsub hzD hDmono (le_refl (m + 1))
      (hDmono (m + 1) (Ebase_mem_D hzD hDmono (m + 1)))
  have hcomp : Eset K W z N (m + 1) ⊆
      connectedComponentIn (W \ K m) (Ebase z N (m + 1)) :=
    IsPreconnected.subset_connectedComponentIn (isPreconnected_Eset (K := K) (W := W)
      (z := z) (N := N) (m + 1))
      (mem_connectedComponentIn (Ebase_mem_sdiff hDW hDK hKsub hzD hDmono (m + 1))) hsub
  have heq : Eset K W z N m = connectedComponentIn (W \ K m) (Ebase z N (m + 1)) := by
    simpa only [Eset] using connectedComponentIn_eq hpt
  rw [heq]
  exact hcomp

/-- The base point `b` of the datum lies in `E 0`. -/
lemma b_mem_Eset_zero {M : Type*} [TopologicalSpace M] {W : Set M} {K : ℕ → Set M}
    {D : ℕ → Set M} {z : ℕ → M} {N : ℕ} {b : M}
    (hDpc : ∀ i, IsPreconnected (D i)) (hDW : ∀ i, D i ⊆ W)
    (hDK : ∀ i, D i ⊆ (K i)ᶜ) (hKsub : ∀ i, K i ⊆ interior (K (i + 1)))
    (hzD : ∀ i, z i ∈ D (N + i)) (hDmono : ∀ i, D (i + 1) ⊆ D i) (hb : b ∈ D N) :
    b ∈ Eset K W z N 0 := by
  have hKmono : Monotone K := monotone_nat_of_le_succ
    (fun i => (hKsub i).trans interior_subset)
  have hk : min N 1 ≤ N := min_le_left _ _
  have hk1 : min N 1 ≤ 1 := min_le_right _ _
  have hsub : D (min N 1) ⊆ W \ K 0 := by
    intro x hx
    refine ⟨hDW _ hx, fun hc => (hDK _ hx) ?_⟩
    exact hKmono (by omega) hc
  have hpt : Ebase z N 0 ∈ D (min N 1) :=
    antitone_of_succ_subset hDmono hk1 (Ebase_mem_D hzD hDmono 0)
  exact IsPreconnected.subset_connectedComponentIn (hDpc _) hpt hsub
    (antitone_of_succ_subset hDmono hk hb)

/-- Every compact subset of the ambient space lies in some `interior (K m)`. -/
lemma exists_subset_interior_K {M : Type*} [TopologicalSpace M] {K : ℕ → Set M}
    (hKsub : ∀ i, K i ⊆ interior (K (i + 1))) (hKuniv : (⋃ i, K i) = (Set.univ : Set M))
    {C : Set M} (hC : IsCompact C) : ∃ m, C ⊆ interior (K m) := by
  obtain ⟨I, hI⟩ := Work.Noncompact.Routing.exists_avoid_level
    (fun i => (hKsub i).trans interior_subset) hKsub hKuniv hC
  exact ⟨I + 1, hI.trans (hKsub I)⟩

/-! ## The state of the corridor recursion -/

/-- The state of the corridor recursion: a junction `Q ∈ E α` together with the ceiling `βp` of
the previous corridor. -/
structure CorridorState {M : Type*} [TopologicalSpace M] (K : ℕ → Set M) (W : Set M)
    (z : ℕ → M) (N : ℕ) where
  /-- the level of the junction -/
  α : ℕ
  /-- the ceiling level of the previous corridor (the `β (i-1)` of the construction) -/
  βp : ℕ
  /-- the junction -/
  Q : M
  /-- the junction lies in the canal region of level `α` -/
  hQ : Q ∈ Eset K W z N α

/-- **The corridor recursion.**  From a state `(α, βp, Q)` one passes to a state `(α', β, Q')`
with `α'` beyond both `α` and `βp`, `β` beyond both `βp` and the level hosting a connecting arc,
`Q' ∈ E α'`, `Q' ≠ Q` in the sense that `Q' ∈ interior (K β)` while `Q` lies in no
`E`-level beyond `βp`, and `Q'` lying in the same component of `E α ∩ interior (K β)` as `Q`. -/
theorem exists_corridorSeq {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    {W : Set M} {K : ℕ → Set M} {z : ℕ → M} {N : ℕ} {b : M}
    (hWo : IsOpen W) (hKc : ∀ i, IsCompact (K i))
    (hKsub : ∀ i, K i ⊆ interior (K (i + 1))) (hKuniv : (⋃ i, K i) = (Set.univ : Set M))
    (hEne : ∀ m, (Eset K W z N m).Nonempty)
    (hEnest : ∀ m, Eset K W z N (m + 1) ⊆ Eset K W z N m)
    {Mb : ℕ} (hbK : b ∈ K Mb) (hbE : b ∈ Eset K W z N 0) :
    ∃ S : ℕ → CorridorState K W z N,
      (S 0).α = 0 ∧ (S 0).βp = Mb ∧ (S 0).Q = b ∧
      (∀ i, (S i).α + 1 ≤ (S (i + 1)).α) ∧
      (∀ i, (S i).βp ≤ (S (i + 1)).α) ∧
      (∀ i, (S i).βp ≤ (S (i + 1)).βp) ∧
      (∀ i, (S (i + 1)).Q ∈ interior (K (S (i + 1)).βp)) ∧
      (∀ i, (S i).Q ∈ interior (K (S (i + 1)).βp)) ∧
      (∀ i, (S (i + 1)).Q ∈ connectedComponentIn
        (Eset K W z N (S i).α ∩ interior (K (S (i + 1)).βp)) (S i).Q) ∧
      (∀ i, ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (ρ ρ' : ℝ),
        0 < ρ ∧ ρ < ρ' ∧ (S i).Q ∈ c.source ∧
        c.symm '' Metric.closedBall (c ((S i).Q)) ρ' ⊆
          Eset K W z N ((S i).α) ∩ interior (K ((S (i + 1)).βp))) := by
  classical
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  have hKmono : Monotone K := monotone_nat_of_le_succ
    (fun i => (hKsub i).trans interior_subset)
  have hEmono : ∀ {a b : ℕ}, a ≤ b → Eset K W z N b ⊆ Eset K W z N a := by
    intro a b hab
    induction hab with
    | refl => exact subset_rfl
    | step hk ih => exact (hEnest _).trans ih
  have hstep : ∀ s : CorridorState K W z N, ∃ s' : CorridorState K W z N,
      s.α + 1 ≤ s'.α ∧ s.βp ≤ s'.α ∧ s.βp ≤ s'.βp ∧
      s'.Q ∈ interior (K s'.βp) ∧ s.Q ∈ interior (K s'.βp) ∧
      s'.Q ∈ connectedComponentIn (Eset K W z N s.α ∩ interior (K s'.βp)) s.Q := by
    intro s
    set α' : ℕ := max (s.α + 1) s.βp with hα'def
    have hα's : s.α + 1 ≤ α' := le_max_left _ _
    have hβpα' : s.βp ≤ α' := le_max_right _ _
    obtain ⟨Q', hQ'⟩ := hEne α'
    have hEo : IsOpen (Eset K W z N s.α) := isOpen_Eset hWo hKc s.α
    have hEp : IsPreconnected (Eset K W z N s.α) := isPreconnected_Eset s.α
    have hQ's : Q' ∈ Eset K W z N s.α := hEmono (le_trans (Nat.le_succ s.α) hα's) hQ'
    obtain ⟨σ, hσc, hσ0, hσ1, hσmem⟩ :=
      Work.Noncompact.Routing.exists_arc_in_preconnected (n := n) (M := M)
        hEo hEp s.hQ hQ's
    obtain ⟨Ml, hMl⟩ := exists_subset_interior_K hKsub hKuniv (isCompact_Icc.image hσc)
    set β : ℕ := max Ml s.βp with hβdef
    have hMlβ : Ml ≤ β := le_max_left _ _
    have hβpβ : s.βp ≤ β := le_max_right _ _
    have hσamb : σ '' Set.Icc (0 : ℝ) 1 ⊆ Eset K W z N s.α ∩ interior (K β) := by
      rintro x ⟨t, ht, rfl⟩
      exact ⟨hσmem t ht, interior_mono (hKmono hMlβ) (hMl ⟨t, ht, rfl⟩)⟩
    have hQ'int : Q' ∈ interior (K β) := (hσamb ⟨1, by norm_num, hσ1⟩).2
    have hQint : s.Q ∈ interior (K β) := (hσamb ⟨0, by norm_num, hσ0⟩).2
    have hQcomp : Q' ∈ connectedComponentIn (Eset K W z N s.α ∩ interior (K β)) s.Q :=
      IsPreconnected.subset_connectedComponentIn (isPreconnected_Icc.image _ hσc.continuousOn)
        ⟨0, by norm_num, hσ0⟩ hσamb ⟨1, by norm_num, hσ1⟩
    exact ⟨⟨α', β, Q', hQ'⟩, hα's, hβpα', hβpβ, hQ'int, hQint, hQcomp⟩
  choose f hf using hstep
  let base : CorridorState K W z N := ⟨0, Mb, b, hbE⟩
  let S : ℕ → CorridorState K W z N := fun i => f^[i] base
  have hS0 : S 0 = base := Function.iterate_zero_apply f base
  have hSsucc : ∀ i, S (i + 1) = f (S i) := fun i => Function.iterate_succ_apply' f i base
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hS0]
  · rw [hS0]
  · rw [hS0]
  · intro i
    have h := (hf (S i)).1
    rwa [← hSsucc i] at h
  · intro i
    have h := (hf (S i)).2.1
    rwa [← hSsucc i] at h
  · intro i
    have h := (hf (S i)).2.2.1
    rwa [← hSsucc i] at h
  · intro i
    have h := (hf (S i)).2.2.2.1
    rwa [← hSsucc i] at h
  · intro i
    have h := (hf (S i)).2.2.2.2.1
    rwa [← hSsucc i] at h
  · intro i
    have h := (hf (S i)).2.2.2.2.2
    rwa [← hSsucc i] at h
  · intro i
    have hUo : IsOpen (Eset K W z N ((S i).α) ∩ interior (K ((S (i + 1)).βp))) :=
      (isOpen_Eset hWo hKc ((S i).α)).inter isOpen_interior
    have hQint : (S i).Q ∈ interior (K ((S (i + 1)).βp)) := by
      have h := (hf (S i)).2.2.2.2.1
      rwa [← hSsucc i] at h
    have hQU : (S i).Q ∈ Eset K W z N ((S i).α) ∩ interior (K ((S (i + 1)).βp)) :=
      ⟨(S i).hQ, hQint⟩
    set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
      chartAt (EuclideanSpace ℝ (Fin n)) ((S i).Q) with hcdef
    have hcsrc : (S i).Q ∈ c.source := mem_chart_source _ _
    have hctgt : c ((S i).Q) ∈ c.target := c.map_source hcsrc
    have hcont : ContinuousAt (⇑c.symm) (c ((S i).Q)) :=
      c.continuousOn_symm.continuousAt (c.open_target.mem_nhds hctgt)
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
      (hcont.preimage_mem_nhds (by rw [c.left_inv hcsrc]; exact hUo.mem_nhds hQU))
    have hρ : 0 < ε / 4 := by linarith
    have hρ' : ε / 4 < ε / 2 := by linarith
    refine ⟨c, ε / 4, ε / 2, hρ, hρ', hcsrc, ?_⟩
    rintro y ⟨y₀, hy₀, rfl⟩
    have hsub : Metric.closedBall (c ((S i).Q)) (ε / 2) ⊆ Metric.ball (c ((S i).Q)) ε :=
      Metric.closedBall_subset_ball (by linarith [hε])
    exact hεsub (hsub hy₀)

/-! ## The corridor chain of the canal datum -/

theorem corridorChain_of_canalData {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {W : Set M} (hW : IsOpen W) (hWc : IsPreconnected W)
    {K : ℕ → Set M} (hKc : ∀ i, IsCompact (K i))
    (hKsub : ∀ i, K i ⊆ interior (K (i + 1))) (hKuniv : (⋃ i, K i) = (Set.univ : Set M))
    {D : ℕ → Set M} (hDo : ∀ i, IsOpen (D i)) (hDpc : ∀ i, IsPreconnected (D i))
    (hDne : ∀ i, (D i).Nonempty) (hDmono : ∀ i, D (i + 1) ⊆ D i)
    (hDW : ∀ i, D i ⊆ W) (hDK : ∀ i, D i ⊆ (K i)ᶜ)
    (hDnc : ∀ i, ¬ IsCompact (closure (D i)))
    {N : ℕ} {b : M} (hb : b ∈ D N) (hbcl : b ∉ closure (D (N + 2)))
    {z : ℕ → M} (hzD : ∀ i, z i ∈ D (N + i))
    (hzcl : ∀ i, z i ∉ closure (D (N + i + 2)))
    (hznot : ∀ i, z i ∉ D (N + i + 1)) :
    ∃ (h : Work.Noncompact.CompressionTube.CorridorChain b W) (spine : ℕ → ℝ → M) (germ : ℕ → Set M) (Gann : ℕ → Set M),
      (∀ i, h.Q i ∉ h.C (i + 1)) ∧
      (∀ i, IsOpen (Gann i)) ∧
      (∀ i, h.Q (i + 1) ∈ Gann i) ∧
      (∀ i, h.C i ∩ h.C (i + 1) ⊆ Gann i) ∧
      (∀ i, IsOpen (germ i)) ∧
      (∀ i, IsPreconnected (germ i)) ∧
      (∀ i, h.Q (i + 1) ∈ germ i) ∧
      (∀ i, germ i ⊆ h.C i ∩ h.C (i + 1)) ∧
      (∀ i, 1 ≤ i → ∃ Nh : Set M, IsOpen Nh ∧ h.Q i ∈ Nh ∧
        ∀ k : ℕ, i + 1 ≤ k → Disjoint Nh (h.C k)) ∧
      (∀ i, Continuous (spine i)) ∧
      (∀ i, Set.InjOn (spine i) (Set.Icc (0:ℝ) 1)) ∧
      (∀ i t, t ∈ Set.Icc (0:ℝ) 1 → spine i t ∈ h.C i) ∧
      (∀ i, spine i 0 = h.Q i) ∧ (∀ i, spine i 1 = h.Q (i + 1)) := by
  classical
  haveI hLC : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  haveI hLPC : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  have hKmono : Monotone K := monotone_nat_of_le_succ
    (fun i => (hKsub i).trans interior_subset)
  have hEnest : ∀ m, Eset K W z N (m + 1) ⊆ Eset K W z N m :=
    Eset_succ_subset hDpc hDW hDK hKsub hzD hDmono
  have hbE : b ∈ Eset K W z N 0 := b_mem_Eset_zero hDpc hDW hDK hKsub hzD hDmono hb
  have hEne : ∀ m, (Eset K W z N m).Nonempty := fun m =>
    ⟨Ebase z N m, mem_connectedComponentIn (Ebase_mem_sdiff hDW hDK hKsub hzD hDmono m)⟩
  obtain ⟨Mb, hbK⟩ : ∃ Mb, b ∈ K Mb := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (show b ∈ ⋃ i, K i by rw [hKuniv]; exact Set.mem_univ b)
    exact ⟨i, hi⟩
  obtain ⟨S, hS0α, hS0β, hS0Q, hαmono, hβleα, hβmono, hQsucc_int, hQ_int, hQcomp, _hroom⟩ :=
    exists_corridorSeq (n := n) (M := M) hW hKc hKsub hKuniv hEne hEnest hbK hbE
  let Cfun : ℕ → Set M := fun i => connectedComponentIn
    (Eset K W z N ((S i).α) ∩ interior (K ((S (i + 1)).βp))) ((S i).Q)
  have hCopen : ∀ i, IsOpen (Cfun i) := fun i =>
    ((isOpen_Eset hW hKc ((S i).α)).inter isOpen_interior).connectedComponentIn
  have hCpc : ∀ i, IsPreconnected (Cfun i) := fun _ => isPreconnected_connectedComponentIn
  have hCsubE : ∀ i, Cfun i ⊆ Eset K W z N ((S i).α) := fun i =>
    (connectedComponentIn_subset _ _).trans Set.inter_subset_left
  have hCsubK : ∀ i, Cfun i ⊆ interior (K ((S (i + 1)).βp)) := fun i =>
    (connectedComponentIn_subset _ _).trans Set.inter_subset_right
  have hCsubW : ∀ i, Cfun i ⊆ W := fun i =>
    (hCsubE i).trans (fun x hx =>
      (Eset_subset_sdiff (K := K) (W := W) (z := z) (N := N) ((S i).α) hx).1)
  have hQmemC : ∀ i, (S i).Q ∈ Cfun i := fun i =>
    mem_connectedComponentIn ⟨(S i).hQ, hQ_int i⟩
  have hQmemCsucc : ∀ i, (S (i + 1)).Q ∈ Cfun i := fun i => hQcomp i
  have hαmono' : Monotone (fun i => (S i).α) :=
    monotone_nat_of_le_succ (fun i => le_trans (Nat.le_succ ((S i).α)) (hαmono i))
  have hβmono' : Monotone (fun i => (S i).βp) := monotone_nat_of_le_succ hβmono
  have hαge : ∀ i, i ≤ (S i).α := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ k ih => exact le_trans (Nat.succ_le_succ ih) (hαmono k)
  have hseed : ∀ i, (S i).Q ∉ Cfun (i + 1) := by
    intro i hmem
    have hmemE : (S i).Q ∈ Eset K W z N ((S (i + 1)).α) := hCsubE (i + 1) hmem
    have hmemK : (S i).Q ∈ K ((S (i + 1)).α) := by
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0
        rw [hS0Q]
        refine hKmono ?_ hbK
        rw [← hS0β]
        exact hβleα 0
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        exact hKmono (hβleα (k + 1)) (interior_subset (hQsucc_int k))
    exact (Eset_subset_sdiff (K := K) (W := W) (z := z) (N := N)
      ((S (i + 1)).α) hmemE).2 hmemK
  have hnhd : ∀ i, 1 ≤ i → ∃ Nh : Set M, IsOpen Nh ∧ (S i).Q ∈ Nh ∧
      ∀ k : ℕ, i + 1 ≤ k → Disjoint Nh (Cfun k) := by
    intro i hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    refine ⟨interior (K ((S (j + 1)).βp)), isOpen_interior, hQsucc_int j, ?_⟩
    intro k hk
    refine Set.disjoint_left.mpr fun x hxN hxC => ?_
    have hxK : x ∈ K ((S (j + 1 + 1)).α) :=
      hKmono (hβleα (j + 1)) (interior_subset hxN)
    have hxk : x ∈ (K ((S k).α))ᶜ :=
      (Eset_subset_sdiff (K := K) (W := W) (z := z) (N := N) ((S k).α) (hCsubE k hxC)).2
    exact hxk (hKmono (hαmono' (by omega)) hxK)
  have hdisj : ∀ i j, 2 ≤ Nat.dist i j → Disjoint (Cfun i) (Cfun j) := by
    intro i j hij
    have hcases : i + 2 ≤ j ∨ j + 2 ≤ i := by
      rcases lt_or_ge i j with hlt | hge
      · left
        have hd : Nat.dist i j = j - i := Nat.dist_eq_sub_of_le (le_of_lt hlt)
        omega
      · right
        have hd : Nat.dist i j = i - j := Nat.dist_eq_sub_of_le_right hge
        omega
    rcases hcases with h2 | h2
    · refine Set.disjoint_left.mpr fun x hx1 hx2 => ?_
      have hxK : x ∈ K ((S j).α) :=
        hKmono (le_trans (hβleα (i + 1)) (hαmono' (by omega)))
          (interior_subset (hCsubK i hx1))
      exact (Eset_subset_sdiff (K := K) (W := W) (z := z) (N := N)
        ((S j).α) (hCsubE j hx2)).2 hxK
    · refine Set.disjoint_left.mpr fun x hx1 hx2 => ?_
      have hxK : x ∈ K ((S i).α) :=
        hKmono (le_trans (hβleα (j + 1)) (hαmono' (by omega)))
          (interior_subset (hCsubK j hx2))
      exact (Eset_subset_sdiff (K := K) (W := W) (z := z) (N := N)
        ((S i).α) (hCsubE i hx1)).2 hxK
  have hneck : ∀ i, ∃ V : Set M, IsOpen V ∧ (S (i + 1)).Q ∈ V ∧
      Cfun i ∩ Cfun (i + 1) ⊆ V ∧
      (∀ k, k ≠ i → k ≠ i + 1 → Disjoint V (Cfun k)) := by
    intro i
    refine ⟨interior (K ((S (i + 1)).βp)) ∩ (K ((S (i + 1)).α))ᶜ,
      isOpen_interior.inter ((hKc _).isClosed.isOpen_compl), ?_, ?_, ?_⟩
    · exact ⟨hQsucc_int i,
        (Eset_subset_sdiff (K := K) (W := W) (z := z) (N := N)
          ((S (i + 1)).α) (S (i + 1)).hQ).2⟩
    · intro x hx
      exact ⟨hCsubK i hx.1,
        (Eset_subset_sdiff (K := K) (W := W) (z := z) (N := N)
          ((S (i + 1)).α) (hCsubE (i + 1) hx.2)).2⟩
    · intro k hk1 hk2
      rcases lt_or_gt_of_ne hk1 with hlt | hgt
      · refine Set.disjoint_left.mpr fun x hxV hxC => ?_
        have hle : k + 2 ≤ i + 1 := by omega
        exact hxV.2 (hKmono (le_trans (hβleα (k + 1)) (hαmono' hle))
          (interior_subset (hCsubK k hxC)))
      · refine Set.disjoint_left.mpr fun x hxV hxC => ?_
        have hle : i + 2 ≤ k := by omega
        exact (Eset_subset_sdiff (K := K) (W := W) (z := z) (N := N)
          ((S k).α) (hCsubE k hxC)).2
          (hKmono (le_trans (hβleα (i + 1)) (hαmono' hle)) (interior_subset hxV.1))
  have hescape : ∀ K' : Set M, IsCompact K' → ∃ I, ∀ i, I ≤ i → Disjoint (Cfun i) K' := by
    intro K' hK'
    obtain ⟨m, hm⟩ := exists_subset_interior_K hKsub hKuniv hK'
    refine ⟨m, fun i hi => Set.disjoint_left.mpr fun x hxC hxK => ?_⟩
    have hx : x ∈ (K ((S i).α))ᶜ :=
      (Eset_subset_sdiff (K := K) (W := W) (z := z) (N := N) ((S i).α) (hCsubE i hxC)).2
    exact hx (hKmono (le_trans hi (hαge i)) (interior_subset (hm hxK)))
  have hQne : ∀ i, (S i).Q ≠ (S (i + 1)).Q := by
    intro i h
    have hmem : (S i).Q ∈ Cfun (i + 1) := by
      rw [h]
      exact hQmemC (i + 1)
    exact hseed i hmem
  have hspineEx : ∀ i, ∃ γ : ℝ → M, Continuous γ ∧ Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧
      γ 0 = (S i).Q ∧ γ 1 = (S (i + 1)).Q ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Cfun i := by
    intro i
    have hpc : IsPathConnected (Cfun i) :=
      (hCopen i).isConnected_iff_isPathConnected.mp ⟨⟨_, hQmemC i⟩, hCpc i⟩
    exact Work.Noncompact.Canals.ArcTool.exists_arc_of_isPathConnected (n := n) (M := M)
      (hCopen i) hpc (hQmemC i) (hQmemCsucc i) (hQne i)
  choose spine hspine using hspineEx
  have hEanti : ∀ {a b : ℕ}, a ≤ b → Eset K W z N b ⊆ Eset K W z N a := by
    intro a b hab
    induction hab with
    | refl => exact subset_rfl
    | step hk ih => exact (hEnest _).trans ih
  -- **The canonical neck germ**: the component of the junction in its own `E`-level and ceiling.
  let germ : ℕ → Set M := fun i => connectedComponentIn
    (Eset K W z N ((S (i + 1)).α) ∩ interior (K ((S (i + 1)).βp))) ((S (i + 1)).Q)
  have hgerm_open : ∀ i, IsOpen (germ i) := fun i =>
    ((isOpen_Eset hW hKc ((S (i + 1)).α)).inter isOpen_interior).connectedComponentIn
  have hgerm_pc : ∀ i, IsPreconnected (germ i) := fun _ => isPreconnected_connectedComponentIn
  have hgerm_mem : ∀ i, (S (i + 1)).Q ∈ germ i := fun i =>
    mem_connectedComponentIn ⟨(S (i + 1)).hQ, hQsucc_int i⟩
  have hgerm_subE : ∀ i, germ i ⊆ Eset K W z N ((S (i + 1)).α) := fun i =>
    (connectedComponentIn_subset _ _).trans Set.inter_subset_left
  have hgerm_subK : ∀ i, germ i ⊆ interior (K ((S (i + 1)).βp)) := fun i =>
    (connectedComponentIn_subset _ _).trans Set.inter_subset_right
  have hgerm_sub : ∀ i, germ i ⊆ Cfun i ∩ Cfun (i + 1) := by
    intro i x hx
    refine ⟨?_, ?_⟩
    · have hsub : germ i ⊆ Eset K W z N ((S i).α) ∩ interior (K ((S (i + 1)).βp)) :=
        fun y hy => ⟨hEanti (hαmono' (Nat.le_succ i)) (hgerm_subE i hy),
          hgerm_subK i hy⟩
      have h1 : x ∈ connectedComponentIn
          (Eset K W z N ((S i).α) ∩ interior (K ((S (i + 1)).βp))) ((S (i + 1)).Q) :=
        (isPreconnected_connectedComponentIn).subset_connectedComponentIn (hgerm_mem i) hsub hx
      rwa [show connectedComponentIn
          (Eset K W z N ((S i).α) ∩ interior (K ((S (i + 1)).βp))) ((S (i + 1)).Q) = Cfun i from
        (connectedComponentIn_eq (hQmemCsucc i)).symm] at h1
    · have hsub : germ i ⊆ Eset K W z N ((S (i + 1)).α) ∩
          interior (K ((S (i + 1 + 1)).βp)) :=
        fun y hy => ⟨hgerm_subE i hy, interior_mono (hKmono (hβmono (i + 1))) (hgerm_subK i hy)⟩
      exact (isPreconnected_connectedComponentIn).subset_connectedComponentIn
        (hgerm_mem i) hsub hx
  -- **The neck annulus**: the open set in which consecutive corridors meet.
  let Gann : ℕ → Set M := fun i =>
    interior (K ((S (i + 1)).βp)) ∩ (K ((S (i + 1)).α))ᶜ
  have hGann_open : ∀ i, IsOpen (Gann i) := fun i =>
    isOpen_interior.inter ((hKc _).isClosed.isOpen_compl)
  have hGann_mem : ∀ i, (S (i + 1)).Q ∈ Gann i := fun i =>
    ⟨hQsucc_int i,
      (Eset_subset_sdiff (K := K) (W := W) (z := z) (N := N) ((S (i + 1)).α)
        (S (i + 1)).hQ).2⟩
  have hGann_sub : ∀ i, Cfun i ∩ Cfun (i + 1) ⊆ Gann i := by
    intro i x hx
    exact ⟨hCsubK i hx.1,
      (Eset_subset_sdiff (K := K) (W := W) (z := z) (N := N) ((S (i + 1)).α)
        (hCsubE (i + 1) hx.2)).2⟩
  exact ⟨{ Q := fun i => (S i).Q
           C := Cfun
           base := hS0Q
           isOpen_C := hCopen
           isPreconnected_C := hCpc
           subset_W := hCsubW
           mem_Q := hQmemC
           mem_Q_succ := hQmemCsucc
           disjoint := hdisj
           neck := hneck
           escape := hescape },
    spine, germ, Gann, hseed, hGann_open, hGann_mem, hGann_sub, hgerm_open, hgerm_pc, hgerm_mem, hgerm_sub, hnhd,
    (fun i => (hspine i).1),
    (fun i => (hspine i).2.1),
    (fun i t ht => (hspine i).2.2.2.2 t ht),
    (fun i => (hspine i).2.2.1),
    (fun i => (hspine i).2.2.2.1)⟩

end

end Work.CompressionTube
