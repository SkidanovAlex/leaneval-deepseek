import Mathlib
import Submission.Work.RatHurewicz.finiteGraphDefs

/-!
# Arc chains in the finite graph quotient are homotopic to formal edge paths

This file proves `Work.RatHurewicz.GraphPi.arcChainEdgePath`: every arc chain between two vertices
of the graph quotient `GraphX a b` is homotopic (rel endpoints) to the path of a formal edge path.

The argument runs an accumulator through the chain.  The accumulator is a single
`ArcPiece` from the initial vertex to the current junction; at each step the *next* piece decides
the case:

* if its initial parameter `sg 0` is `0` (resp. `1`), the junction is the `a`-end (resp. the
  `b`-end) of the edge, and the accumulator is closed off by `piece_vertex` (a single arc piece
  whose endpoints are vertices is homotopic to a formal edge path);
* otherwise the junction is an interior point of the edge, so the two pieces lie on a common edge
  with matching lifts (`gq_inr_inr_interior`) and are merged into one piece by `mergePiece`.

The key auxiliary facts about paths are: any two paths in the unit interval with the same endpoints
are homotopic (it is contractible), mapping along the edge parametrisation turns this into the
comparison of `psiPath`s, and the four endpoint cases `(0,0)`, `(0,1)`, `(1,0)`, `(1,1)` identify a
`psiPath` with `Path.refl`, `edgePath`, `(edgePath).symm`, `Path.refl` respectively.
-/

namespace Work.RatHurewicz.GraphPi

open scoped unitInterval Topology

variable {E V : Type} [Fintype E] [Fintype V] [TopologicalSpace E] [DiscreteTopology E]
  [TopologicalSpace V] [DiscreteTopology V] (a b : E → V)

set_option autoImplicit false

theorem contractible_unitInterval : ContractibleSpace unitInterval :=
  Convex.contractibleSpace (convex_Icc (0:ℝ) 1) (Set.nonempty_Icc.mpr zero_le_one)

theorem homotopic_of_apply_eq {X : Type*} [TopologicalSpace X] {x y : X} {p q : Path x y}
    (h : ∀ t, p t = q t) : p.Homotopic q :=
  ⟨(Path.Homotopy.refl p).cast rfl (Path.ext (γ₂ := q) (funext h))⟩

theorem homotopic_of_apply_eq_cast {X : Type*} [TopologicalSpace X] {x y x' y' : X}
    {p : Path x y} {q : Path x' y'} (hx : x = x') (hy : y = y') (h : ∀ t, p t = q t) :
    p.Homotopic (q.cast hx hy) :=
  homotopic_of_apply_eq (fun t => (h t).trans (by rw [Path.cast_coe]))

theorem homotopic_cast_cast {X : Type*} [TopologicalSpace X] {x y x₁ y₁ x₂ y₂ : X}
    {γ : Path x y} (A : x₁ = x) (B : y₁ = y) (C : x₂ = x₁) (D : y₂ = y₁) :
    ((γ.cast A B).cast C D).Homotopic (γ.cast (C.trans A) (D.trans B)) :=
  homotopic_of_apply_eq (fun t => by simp only [Path.cast_coe])

theorem homotopic_cast_comp {X : Type*} [TopologicalSpace X] {x₀ y₀ x₁ y₁ x₂ y₂ : X}
    {γ₀ : Path x₀ y₀} {γ₁ : Path x₁ y₁} {γ₂ : Path x₂ y₂}
    (A : x₀ = x₁) (B : y₀ = y₁) (C : x₁ = x₂) (D : y₁ = y₂)
    (h1 : γ₀.Homotopic (γ₁.cast A B)) (h2 : γ₁.Homotopic (γ₂.cast C D)) :
    γ₀.Homotopic (γ₂.cast (A.trans C) (B.trans D)) :=
  h1.trans ((Path.Homotopic.pathCast h2 A B).trans (homotopic_cast_cast C D A B))

def pathOf (sg : C(I, I)) : Path (sg 0) (sg 1) where
  toContinuousMap := sg
  source' := rfl
  target' := rfl

@[simp] lemma pathOf_coe (sg : C(I,I)) : ⇑(pathOf sg) = ⇑sg := rfl

def psiPath (e : E) (sg : C(I,I)) : Path (psiFunGraph a b e (sg 0)) (psiFunGraph a b e (sg 1)) where
  toFun := fun t => psiFunGraph a b e (sg t)
  continuous_toFun := (psi_cont a b e).comp sg.continuous
  source' := rfl
  target' := rfl

@[simp] lemma psiPath_apply (e : E) (sg : C(I,I)) (t : I) :
    psiPath a b e sg t = psiFunGraph a b e (sg t) := rfl

theorem psiPath_homotopic_of_endpoints (e : E) (sg tg : C(I,I)) (h0 : sg 0 = tg 0) (h1 : sg 1 = tg 1) :
    (psiPath a b e sg).Homotopic
      ((psiPath a b e tg).cast (congrArg (psiFunGraph a b e) h0) (congrArg (psiFunGraph a b e) h1)) := by
  haveI := contractible_unitInterval
  have H : (pathOf sg).Homotopic ((pathOf tg).cast h0 h1) :=
    SimplyConnectedSpace.paths_homotopic _ _
  have H2 := H.map ⟨psiFunGraph a b e, psi_cont a b e⟩
  refine (homotopic_of_apply_eq ?_).trans (H2.trans (homotopic_of_apply_eq ?_))
  · intro t; simp [Path.map_coe, pathOf_coe]
  · intro t; simp [Path.map_coe, Path.cast_coe, psiPath_apply]



@[simp] theorem ArcChain.toPath_nil (x : GraphX a b) :
    ArcChain.toPath a b (ArcChain.nil x) = Path.refl x := rfl

@[simp] theorem ArcChain.toPath_cons {x z y : GraphX a b} (p : ArcPiece a b x z)
    (rest : ArcChain a b z y) :
    ArcChain.toPath a b (ArcChain.cons p rest) = p.c.trans (ArcChain.toPath a b rest) := rfl

@[simp] theorem EdgePath.toPath_refl (v : V) :
    EdgePath.toPath a b (EdgePath.refl v) = Path.refl (gq a b (Sum.inl v)) := rfl

@[simp] theorem EdgePath.toPath_fwd (e : E) :
    EdgePath.toPath a b (EdgePath.fwd e) = edgePath a b e := rfl

@[simp] theorem EdgePath.toPath_bwd (e : E) :
    EdgePath.toPath a b (EdgePath.bwd e) = (edgePath a b e).symm := rfl

@[simp] theorem EdgePath.toPath_trans {u v w : V} (c₁ : EdgePath a b u v) (c₂ : EdgePath a b v w) :
    EdgePath.toPath a b (EdgePath.trans c₁ c₂) =
      (EdgePath.toPath a b c₁).trans (EdgePath.toPath a b c₂) := rfl

/-- Case (0,0). -/
theorem psiPath_refl_left (e : E) (sg : C(I,I)) (h0 : sg 0 = 0) (h1 : sg 1 = 0) :
    (psiPath a b e sg).Homotopic
      ((Path.refl (gq a b (Sum.inl (a e)))).cast
        ((congrArg (psiFunGraph a b e) h0).trans (rel_ae a b e))
        ((congrArg (psiFunGraph a b e) h1).trans (rel_ae a b e))) := by
  have hQ := psiPath_homotopic_of_endpoints a b e sg (ContinuousMap.const I (0 : I)) h0 h1
  have hR : (psiPath a b e (ContinuousMap.const I (0 : I))).Homotopic
      ((Path.refl (gq a b (Sum.inl (a e)))).cast (rel_ae a b e) (rel_ae a b e)) := by
    apply homotopic_of_apply_eq_cast _ _
    intro t
    exact rel_ae a b e
  have hA : sg 0 = (ContinuousMap.const I (0 : I)) 0 := h0
  have hB : sg 1 = (ContinuousMap.const I (0 : I)) 1 := h1
  refine (homotopic_cast_comp (congrArg (psiFunGraph a b e) hA) (congrArg (psiFunGraph a b e) hB)
    (rel_ae a b e) (rel_ae a b e) hQ hR).trans ?_
  exact homotopic_of_apply_eq (fun t => by simp)

/-- Case (0,1). -/
theorem psiPath_fwd (e : E) (sg : C(I,I)) (h0 : sg 0 = 0) (h1 : sg 1 = 1) :
    (psiPath a b e sg).Homotopic
      ((edgePath a b e).cast
        ((congrArg (psiFunGraph a b e) h0).trans (rel_ae a b e))
        ((congrArg (psiFunGraph a b e) h1).trans (rel_be a b e))) := by
  have hQ := psiPath_homotopic_of_endpoints a b e sg (ContinuousMap.id I) h0 h1
  have hR : (psiPath a b e (ContinuousMap.id I)).Homotopic
      ((edgePath a b e).cast (rel_ae a b e) (rel_be a b e)) := by
    apply homotopic_of_apply_eq_cast _ _
    intro t
    rfl
  have hA : sg 0 = (ContinuousMap.id I) 0 := h0
  have hB : sg 1 = (ContinuousMap.id I) 1 := h1
  refine (homotopic_cast_comp (congrArg (psiFunGraph a b e) hA) (congrArg (psiFunGraph a b e) hB)
    (rel_ae a b e) (rel_be a b e) hQ hR).trans ?_
  exact homotopic_of_apply_eq (fun t => by simp)

/-- Case (1,0). -/
theorem psiPath_bwd (e : E) (sg : C(I,I)) (h0 : sg 0 = 1) (h1 : sg 1 = 0) :
    (psiPath a b e sg).Homotopic
      (((edgePath a b e).symm).cast
        ((congrArg (psiFunGraph a b e) h0).trans (rel_be a b e))
        ((congrArg (psiFunGraph a b e) h1).trans (rel_ae a b e))) := by
  set tg : C(I,I) := ⟨unitInterval.symm, unitInterval.continuous_symm⟩ with htg
  have hz0 : tg 0 = 1 := unitInterval.symm_zero
  have hz1 : tg 1 = 0 := unitInterval.symm_one
  have hA : sg 0 = tg 0 := h0.trans hz0.symm
  have hB : sg 1 = tg 1 := h1.trans hz1.symm
  have hQ := psiPath_homotopic_of_endpoints a b e sg tg hA hB
  have hR : (psiPath a b e tg).Homotopic
      (((edgePath a b e).symm).cast
        ((congrArg (psiFunGraph a b e) hz0).trans (rel_be a b e))
        ((congrArg (psiFunGraph a b e) hz1).trans (rel_ae a b e))) := by
    apply homotopic_of_apply_eq_cast _ _
    intro t
    rfl
  refine (homotopic_cast_comp (congrArg (psiFunGraph a b e) hA) (congrArg (psiFunGraph a b e) hB)
    ((congrArg (psiFunGraph a b e) hz0).trans (rel_be a b e))
    ((congrArg (psiFunGraph a b e) hz1).trans (rel_ae a b e)) hQ hR).trans ?_
  exact homotopic_of_apply_eq (fun t => by simp)

/-- Case (1,1). -/
theorem psiPath_refl_right (e : E) (sg : C(I,I)) (h0 : sg 0 = 1) (h1 : sg 1 = 1) :
    (psiPath a b e sg).Homotopic
      ((Path.refl (gq a b (Sum.inl (b e)))).cast
        ((congrArg (psiFunGraph a b e) h0).trans (rel_be a b e))
        ((congrArg (psiFunGraph a b e) h1).trans (rel_be a b e))) := by
  have hQ := psiPath_homotopic_of_endpoints a b e sg (ContinuousMap.const I (1 : I)) h0 h1
  have hR : (psiPath a b e (ContinuousMap.const I (1 : I))).Homotopic
      ((Path.refl (gq a b (Sum.inl (b e)))).cast (rel_be a b e) (rel_be a b e)) := by
    apply homotopic_of_apply_eq_cast _ _
    intro t
    exact rel_be a b e
  have hA : sg 0 = (ContinuousMap.const I (1 : I)) 0 := h0
  have hB : sg 1 = (ContinuousMap.const I (1 : I)) 1 := h1
  refine (homotopic_cast_comp (congrArg (psiFunGraph a b e) hA) (congrArg (psiFunGraph a b e) hB)
    (rel_be a b e) (rel_be a b e) hQ hR).trans ?_
  exact homotopic_of_apply_eq (fun t => by simp)

/-- Helper A: a single arc piece whose endpoints are vertices is homotopic to a formal edge path. -/
theorem piece_vertex {u w : V} {x z : GraphX a b} (p : ArcPiece a b x z)
    (hx : x = gq a b (Sum.inl u)) (hz : z = gq a b (Sum.inl w)) :
    ∃ c' : EdgePath a b u w, p.c.Homotopic ((EdgePath.toPath a b c').cast hx hz) := by
  have hp : p.c.Homotopic ((psiPath a b p.e p.sg).cast (p.c.source.symm.trans (p.hc 0))
      (p.c.target.symm.trans (p.hc 1))) := by
    apply homotopic_of_apply_eq_cast _ _
    intro t
    exact p.hc t
  have h0 : gq a b (Sum.inl u) = psiFunGraph a b p.e (p.sg 0) := by
    rw [← hx, ← p.hc 0]; exact p.c.source.symm
  have h1 : gq a b (Sum.inl w) = psiFunGraph a b p.e (p.sg 1) := by
    rw [← hz, ← p.hc 1]; exact p.c.target.symm
  rcases gq_inl_inr a b h0 with ⟨hs0, hu⟩ | ⟨hs0, hu⟩ <;>
    rcases gq_inl_inr a b h1 with ⟨hs1, hw⟩ | ⟨hs1, hw⟩
  · subst hu; subst hw
    refine ⟨EdgePath.refl (a p.e), ?_⟩
    refine (homotopic_cast_comp (A := p.c.source.symm.trans (p.hc 0)) (B := p.c.target.symm.trans (p.hc 1))
      (C := (congrArg (psiFunGraph a b p.e) hs0).trans (rel_ae a b p.e))
      (D := (congrArg (psiFunGraph a b p.e) hs1).trans (rel_ae a b p.e)) hp
      (psiPath_refl_left a b p.e p.sg hs0 hs1)).trans ?_
    exact homotopic_of_apply_eq (fun t => by simp)
  · subst hu; subst hw
    refine ⟨EdgePath.fwd p.e, ?_⟩
    refine (homotopic_cast_comp (A := p.c.source.symm.trans (p.hc 0)) (B := p.c.target.symm.trans (p.hc 1))
      (C := (congrArg (psiFunGraph a b p.e) hs0).trans (rel_ae a b p.e))
      (D := (congrArg (psiFunGraph a b p.e) hs1).trans (rel_be a b p.e)) hp
      (psiPath_fwd a b p.e p.sg hs0 hs1)).trans ?_
    exact homotopic_of_apply_eq (fun t => by simp)
  · subst hu; subst hw
    refine ⟨EdgePath.bwd p.e, ?_⟩
    refine (homotopic_cast_comp (A := p.c.source.symm.trans (p.hc 0)) (B := p.c.target.symm.trans (p.hc 1))
      (C := (congrArg (psiFunGraph a b p.e) hs0).trans (rel_be a b p.e))
      (D := (congrArg (psiFunGraph a b p.e) hs1).trans (rel_ae a b p.e)) hp
      (psiPath_bwd a b p.e p.sg hs0 hs1)).trans ?_
    exact homotopic_of_apply_eq (fun t => by simp)
  · subst hu; subst hw
    refine ⟨EdgePath.refl (b p.e), ?_⟩
    refine (homotopic_cast_comp (A := p.c.source.symm.trans (p.hc 0)) (B := p.c.target.symm.trans (p.hc 1))
      (C := (congrArg (psiFunGraph a b p.e) hs0).trans (rel_be a b p.e))
      (D := (congrArg (psiFunGraph a b p.e) hs1).trans (rel_be a b p.e)) hp
      (psiPath_refl_right a b p.e p.sg hs0 hs1)).trans ?_
    exact homotopic_of_apply_eq (fun t => by simp)

def cmOfPath {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y) : C(I, X) where
  toFun := γ
  continuous_toFun := γ.continuous

@[simp] lemma cmOfPath_apply {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y) (t : I) :
    cmOfPath γ t = γ t := rfl

/-- The concatenation of a path with a cast path (useful for `Path.trans` computations). -/
theorem trans_cast_rfl {X : Type*} [TopologicalSpace X] {x y Z Z' : X}
    (γ : Path x y) (δ : Path y Z) (hz : Z' = Z) :
    (γ.trans (δ.cast rfl hz)).Homotopic ((γ.trans δ).cast rfl hz) :=
  homotopic_of_apply_eq (fun t => by
    simp only [Path.cast_coe, Path.trans_apply])

/-- Merge two consecutive arc pieces lying on a common edge with matching lifts. -/
noncomputable def mergePiece {x z z' : GraphX a b} (p : ArcPiece a b x z) (q : ArcPiece a b z z')
    (he : q.e = p.e) (hs : q.sg 0 = p.sg 1) : ArcPiece a b x z' where
  e := p.e
  sg := cmOfPath ((pathOf p.sg).trans ((pathOf q.sg).cast hs.symm rfl))
  c := p.c.trans q.c
  hc := by
    intro t
    rw [cmOfPath_apply]
    rw [Path.trans_apply p.c q.c t]
    rw [Path.trans_apply (pathOf p.sg) ((pathOf q.sg).cast hs.symm rfl) t]
    split_ifs with h
    · exact p.hc _
    · rw [Path.cast_coe, ← he]
      exact q.hc _

omit [Fintype E] [Fintype V] [DiscreteTopology E] [DiscreteTopology V] in
lemma mergePiece_c {x z z' : GraphX a b} (p : ArcPiece a b x z) (q : ArcPiece a b z z')
    (he : q.e = p.e) (hs : q.sg 0 = p.sg 1) :
    (mergePiece a b p q he hs).c = p.c.trans q.c := rfl


/-- Pushing casts through a concatenation of paths. -/
theorem cast_trans_cast {X : Type*} [TopologicalSpace X] {x y z x' y' z' : X}
    {γ : Path x y} {δ : Path y z} (A : x' = x) (B : y' = y) (C : z' = z) :
    ((γ.cast A B).trans (δ.cast B C)).Homotopic ((γ.trans δ).cast A C) :=
  homotopic_of_apply_eq (fun t => by simp only [Path.cast_coe, Path.trans_apply])

/-- The main recursion: an accumulated arc piece with start point `xq = gq a b (Sum.inl u)`,
followed by a chain ending at a vertex, is homotopic to a formal edge path from `u`. -/
noncomputable def acc (u : V) (xq : GraphX a b) (zq : GraphX a b) (p : ArcPiece a b xq zq)
    (hxq : xq = gq a b (Sum.inl u)) (y : GraphX a b) (rest : ArcChain a b zq y) (w : V)
    (hy : y = gq a b (Sum.inl w)) :
    ∃ c' : EdgePath a b u w,
      (p.c.trans (ArcChain.toPath a b rest)).Homotopic ((EdgePath.toPath a b c').cast hxq hy) := by
  induction rest generalizing u xq hxq w with
  | nil x =>
    obtain ⟨c₁, hp⟩ := piece_vertex a b p hxq hy
    exact ⟨c₁, (Path.Homotopic.trans_refl p.c).trans hp⟩
  | cons q r ih =>
    have hgs0 := q.c.source.symm.trans ((q.hc 0).trans
      (show psiFunGraph a b q.e (q.sg 0) = gq a b (Sum.inr (q.e, q.sg 0)) from rfl))
    by_cases hq0 : (q.sg 0 : ℝ) = 0
    · -- the junction is the `a`-end of `q.e`
      have hz := hgs0.trans (show gq a b (Sum.inr (q.e, q.sg 0)) = gq a b (Sum.inl (a q.e)) from
        (by rw [show q.sg 0 = (0 : I) from Subtype.ext hq0]; exact rel_ae a b q.e))
      obtain ⟨c₁, hp⟩ := piece_vertex a b p hxq hz
      obtain ⟨c₂, hc₂⟩ := ih (a q.e) _ q hz w hy
      refine ⟨EdgePath.trans c₁ c₂, ?_⟩
      exact (Path.Homotopic.hcomp hp hc₂).trans (cast_trans_cast hxq hz hy)
    · by_cases hq1 : (q.sg 0 : ℝ) = 1
      · -- the junction is the `b`-end of `q.e`
        have hz := hgs0.trans (show gq a b (Sum.inr (q.e, q.sg 0)) = gq a b (Sum.inl (b q.e)) from
          (by rw [show q.sg 0 = (1 : I) from Subtype.ext hq1]; exact rel_be a b q.e))
        obtain ⟨c₁, hp⟩ := piece_vertex a b p hxq hz
        obtain ⟨c₂, hc₂⟩ := ih (b q.e) _ q hz w hy
        refine ⟨EdgePath.trans c₁ c₂, ?_⟩
        exact (Path.Homotopic.hcomp hp hc₂).trans (cast_trans_cast hxq hz hy)
      · -- interior junction: merge the two pieces
        have hq0pos : 0 < (q.sg 0 : ℝ) :=
          lt_of_le_of_ne (q.sg 0).2.1 (fun hh => hq0 hh.symm)
        have hq0lt : (q.sg 0 : ℝ) < 1 :=
          lt_of_le_of_ne (q.sg 0).2.2 hq1
        have hgg := (q.hc 0).symm.trans (q.c.source.trans (p.c.target.symm.trans (p.hc 1)))
        obtain ⟨he, hs⟩ := gq_inr_inr_interior a b hq0pos hq0lt hgg
        obtain ⟨c'', hc''⟩ := ih u xq (mergePiece a b p q he hs) hxq w hy
        refine ⟨c'', ?_⟩
        exact (Path.Homotopic.trans_assoc p.c q.c (ArcChain.toPath a b r)).symm.trans hc''

/-- Every arc chain from a vertex to an arbitrary point whose endpoint is a vertex is homotopic
(rel endpoints) to a formal edge path. -/
theorem arcChainEdgePath_aux (u : V) (y : GraphX a b)
    (c : ArcChain a b (gq a b (Sum.inl u)) y) (w : V) (hy : y = gq a b (Sum.inl w)) :
    ∃ c' : EdgePath a b u w,
      (ArcChain.toPath a b c).Homotopic ((EdgePath.toPath a b c').cast rfl hy) := by
  cases c with
  | nil x =>
    have huv : u = w := gq_inl_inj a b hy
    subst huv
    refine ⟨EdgePath.refl u, ?_⟩
    exact homotopic_of_apply_eq (fun t => by simp)
  | cons p rest =>
    exact acc a b u _ _ p rfl _ rest w hy


/-- Every arc chain between two vertices is homotopic (rel endpoints) to a formal edge path.

Suggested route: induct on the chain, peeling off the maximal initial run of pieces whose
junctions are *non-vertices* (those pieces all lie in one edge, and their lifts `sg` agree at the
junctions by `gq_inr_inr_same`).  The run's composite is a concatenation of `psiFunGraph e ∘ sg_j`, so
it equals `psiFunGraph e ∘ (concatenated lifts)`, a path in `I` which is homotopic rel endpoints (by
`SimplyConnectedSpace.paths_homotopic` for `unitInterval`, via `Convex.contractibleSpace`) to the
straight path between two parameters that are either equal or `0` and `1` (`gq_inl_inr` shows the
junctions at vertices have parameters `0` or `1`).  Mapping along the continuous map `psiFunGraph a b e`
(`Path.Homotopic.map`) identifies the run with `Path.refl`, `edgePath e` or `(edgePath e).symm`,
i.e. with `.refl v`, `.fwd e` or `.bwd e`; then use the induction hypothesis on the remaining
chain and concatenate. -/
theorem arcChainEdgePath {E V : Type} [Fintype E] [Fintype V] [TopologicalSpace E] [DiscreteTopology E] [TopologicalSpace V] [DiscreteTopology V] (a b : E → V) (u w : V)
    (c : Work.RatHurewicz.ArcChain a b (Work.RatHurewicz.gq a b (Sum.inl u)) (Work.RatHurewicz.gq a b (Sum.inl w))) :
    ∃ c' : Work.RatHurewicz.EdgePath a b u w,
      (Work.RatHurewicz.ArcChain.toPath a b c).Homotopic (Work.RatHurewicz.EdgePath.toPath a b c') := by
  obtain ⟨c', hc'⟩ := arcChainEdgePath_aux a b u _ c w rfl
  exact ⟨c', hc'.trans (homotopic_of_apply_eq (fun t => by rw [Path.cast_coe]))⟩

end Work.RatHurewicz.GraphPi
