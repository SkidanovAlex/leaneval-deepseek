import Mathlib
import Submission.Work.RatHurewicz.finiteGraphDefs
import Submission.Work.RatHurewicz.GraphPi.spiderLocal
import Submission.Work.RatHurewicz.GraphPi.spiderContractible
import Submission.Work.RatHurewicz.GraphPi.midArcLift

namespace Work.RatHurewicz.GraphPi

open scoped unitInterval Topology
open Set

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

variable {E V : Type} [Fintype E] [Fintype V] [TopologicalSpace E] [DiscreteTopology E]
  [TopologicalSpace V] [DiscreteTopology V]

/-! ## A. Elementary path tools -/

theorem homotopic_of_apply_eq {X : Type*} [TopologicalSpace X] {x y : X} {p q : Path x y}
    (h : ∀ t, p t = q t) : p.Homotopic q :=
  ⟨(Path.Homotopy.refl p).cast rfl (Path.ext (funext h))⟩

theorem homotopic_of_apply_eq_cast {X : Type*} [TopologicalSpace X] {x y x' y' : X}
    {p : Path x y} {q : Path x' y'} (hx : x = x') (hy : y = y') (h : ∀ t, p t = q t) :
    p.Homotopic (q.cast hx hy) :=
  homotopic_of_apply_eq (fun t => (h t).trans (by rw [Path.cast_coe]))

theorem homotopic_trans_congr {X : Type*} [TopologicalSpace X] {x y z : X}
    {p₁ p₂ : Path x y} {q₁ q₂ : Path y z} (h₁ : p₁.Homotopic p₂) (h₂ : q₁.Homotopic q₂) :
    (p₁.trans q₁).Homotopic (p₂.trans q₂) :=
  Path.Homotopic.hcomp h₁ h₂

theorem trans_mem {X : Type*} [TopologicalSpace X] {w x z : X} {S : Set X}
    {p : Path w x} {q : Path x z} (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) :
    ∀ t, (p.trans q) t ∈ S := by
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

theorem convexComb_mem_Icc {u v r : I} (h : u ≤ v) :
    Icc.convexComb u v r ∈ Set.Icc u v := by
  have huv : (u : ℝ) ≤ (v : ℝ) := h
  constructor
  · rw [← Subtype.coe_le_coe, Icc.coe_convexComb]
    nlinarith [r.2.1, r.2.2, huv, mul_nonneg r.2.1 (sub_nonneg.mpr huv)]
  · rw [← Subtype.coe_le_coe, Icc.coe_convexComb]
    nlinarith [r.2.1, r.2.2, huv, mul_nonneg (sub_nonneg.mpr r.2.2) (sub_nonneg.mpr huv)]

/-! ## B. Concatenation and transfer of arc chains -/

variable {a b : E → V}

def arcChainAppend : ∀ {x y z : GraphX a b},
    ArcChain a b x y → ArcChain a b y z → ArcChain a b x z
  | _, _, _, .nil _, d => d
  | _, _, _, .cons p rest, d => .cons p (arcChainAppend rest d)

theorem arcChainAppend_toPath : ∀ {x y z : GraphX a b} (c : ArcChain a b x y)
    (d : ArcChain a b y z),
    (arcChainAppend c d).toPath.Homotopic ((c.toPath).trans d.toPath)
  | _, _, _, .nil _, d => ⟨(Path.Homotopy.reflTrans d.toPath).symm⟩
  | _, _, _, .cons p rest, d =>
      (Path.Homotopic.hcomp (Path.Homotopic.refl p.c) (arcChainAppend_toPath rest d)).trans
        (Path.Homotopic.trans_assoc p.c (ArcChain.toPath a b rest) d.toPath).symm

def arcPieceCast {x y x' y' : GraphX a b} (p : ArcPiece a b x y)
    (hx : x' = x) (hy : y' = y) : ArcPiece a b x' y' :=
  { e := p.e
    sg := p.sg
    c := p.c.cast hx hy
    hc := fun t => (congrFun (Path.cast_coe p.c hx hy) t).trans (p.hc t) }

def arcChainCastEnds {x y x' y' : GraphX a b} (c : ArcChain a b x y)
    (hx : x' = x) (hy : y' = y) : ArcChain a b x' y' :=
  hx.symm ▸ hy.symm ▸ c

theorem arcChainCastEnds_toPath {x y x' y' : GraphX a b} (c : ArcChain a b x y)
    (hx : x' = x) (hy : y' = y) :
    (arcChainCastEnds c hx hy).toPath.Homotopic ((c.toPath).cast hx hy) := by
  subst hx
  subst hy
  exact Path.Homotopic.refl _

def chainConcatNat (M : ℕ) {x y : GraphX a b} (γ : Path x y) (u : ℕ → I)
    (G : (k : ℕ) → k < M → ArcChain a b (γ (u k)) (γ (u (k+1)))) :
    ArcChain a b (γ (u 0)) (γ (u M)) :=
  match M with
  | 0 => ArcChain.nil (γ (u 0))
  | j+1 => arcChainAppend (chainConcatNat j γ u (fun k hk => G k (Nat.lt_succ_of_lt hk)))
      (G j (Nat.lt_succ_self j))

theorem chainConcatNat_homotopic (M : ℕ) {x y : GraphX a b} (γ : Path x y) (u : ℕ → I)
    (G : (k : ℕ) → k < M → ArcChain a b (γ (u k)) (γ (u (k+1))))
    (hG : ∀ k (hk : k < M), (γ.subpath (u k) (u (k+1))).Homotopic ((G k hk).toPath)) :
    (chainConcatNat M γ u G).toPath.Homotopic (γ.subpath (u 0) (u M)) := by
  induction M with
  | zero =>
      show (ArcChain.nil (γ (u 0))).toPath.Homotopic (γ.subpath (u 0) (u 0))
      rw [Path.subpath_self]
      exact Path.Homotopic.refl _
  | succ j ih =>
      show (arcChainAppend (chainConcatNat j γ u (fun k hk => G k (Nat.lt_succ_of_lt hk)))
        (G j (Nat.lt_succ_self j))).toPath.Homotopic (γ.subpath (u 0) (u (j+1)))
      refine (arcChainAppend_toPath
        (chainConcatNat j γ u (fun k hk => G k (Nat.lt_succ_of_lt hk)))
        (G j (Nat.lt_succ_self j))).trans ?_
      refine (homotopic_trans_congr
        (ih (fun k hk => G k (Nat.lt_succ_of_lt hk)) (fun k hk => hG k (Nat.lt_succ_of_lt hk)))
        (hG j (Nat.lt_succ_self j)).symm).trans ?_
      exact ⟨Path.Homotopy.subpathTransSubpath γ (u 0) (u j) (u (j+1))⟩

/-! ## C. The legs of the spider -/

lemma bdd_sgDown (s t : I) : (s : ℝ) * (1 - (t : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨mul_nonneg s.2.1 (by linarith [t.2.2]), ?_⟩
  calc (s : ℝ) * (1 - (t : ℝ)) ≤ 1 * 1 :=
        mul_le_mul s.2.2 (by linarith [t.2.1]) (by linarith [t.2.2]) zero_le_one
    _ = 1 := by ring

/-- Parameter map running linearly from `s` down to `0`. -/
def sgDown (s : I) : C(I, I) where
  toFun t := ⟨(s : ℝ) * (1 - (t : ℝ)), bdd_sgDown s t⟩
  continuous_toFun := Continuous.subtype_mk (f := fun t : I => (s : ℝ) * (1 - (t : ℝ)))
    (by fun_prop) (fun t => bdd_sgDown s t)

@[simp] lemma sgDown_zero (s : I) : sgDown s 0 = s := Subtype.ext (by simp [sgDown])
@[simp] lemma sgDown_one (s : I) : sgDown s 1 = 0 := Subtype.ext (by simp [sgDown])
@[simp] lemma sgDown_coe (s t : I) : (sgDown s t : ℝ) = (s : ℝ) * (1 - (t : ℝ)) := rfl

lemma bdd_sgUp (s t : I) : (s : ℝ) + (t : ℝ) * (1 - (s : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 : (0 : ℝ) ≤ 1 - (s : ℝ) := by linarith [s.2.2]
  refine ⟨by nlinarith [mul_nonneg t.2.1 h1, s.2.1], ?_⟩
  have h2 : (t : ℝ) * (1 - (s : ℝ)) ≤ 1 * (1 - (s : ℝ)) := mul_le_mul_of_nonneg_right t.2.2 h1
  linarith

/-- Parameter map running linearly from `s` up to `1`. -/
def sgUp (s : I) : C(I, I) where
  toFun t := ⟨(s : ℝ) + (t : ℝ) * (1 - (s : ℝ)), bdd_sgUp s t⟩
  continuous_toFun := Continuous.subtype_mk (f := fun t : I => (s : ℝ) + (t : ℝ) * (1 - (s : ℝ)))
    (by fun_prop) (fun t => bdd_sgUp s t)

@[simp] lemma sgUp_zero (s : I) : sgUp s 0 = s := Subtype.ext (by simp [sgUp])
@[simp] lemma sgUp_one (s : I) : sgUp s 1 = 1 := Subtype.ext (by simp [sgUp])
@[simp] lemma sgUp_coe (s t : I) : (sgUp s t : ℝ) = (s : ℝ) + (t : ℝ) * (1 - (s : ℝ)) := rfl

lemma bdd_sgUp0 (s t : I) : (t : ℝ) * (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨mul_nonneg t.2.1 s.2.1, ?_⟩
  calc (t : ℝ) * (s : ℝ) ≤ 1 * (s : ℝ) := mul_le_mul_of_nonneg_right t.2.2 s.2.1
    _ = (s : ℝ) := by ring
    _ ≤ 1 := s.2.2

/-- Parameter map running linearly from `0` up to `s`. -/
def sgUp0 (s : I) : C(I, I) where
  toFun t := ⟨(t : ℝ) * (s : ℝ), bdd_sgUp0 s t⟩
  continuous_toFun := Continuous.subtype_mk (f := fun t : I => (t : ℝ) * (s : ℝ))
    (by fun_prop) (fun t => bdd_sgUp0 s t)

@[simp] lemma sgUp0_zero (s : I) : sgUp0 s 0 = 0 := Subtype.ext (by simp [sgUp0])
@[simp] lemma sgUp0_one (s : I) : sgUp0 s 1 = s := Subtype.ext (by simp [sgUp0])
@[simp] lemma sgUp0_coe (s t : I) : (sgUp0 s t : ℝ) = (t : ℝ) * (s : ℝ) := rfl

lemma bdd_sgDown1 (s t : I) : 1 - (t : ℝ) * (1 - (s : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 : (0 : ℝ) ≤ 1 - (s : ℝ) := by linarith [s.2.2]
  have h2 : (t : ℝ) * (1 - (s : ℝ)) ≤ 1 - (s : ℝ) := by
    calc (t : ℝ) * (1 - (s : ℝ)) ≤ 1 * (1 - (s : ℝ)) := mul_le_mul_of_nonneg_right t.2.2 h1
      _ = 1 - (s : ℝ) := by ring
  exact ⟨by linarith [s.2.1], by nlinarith [mul_nonneg t.2.1 h1]⟩

/-- Parameter map running linearly from `1` down to `s`. -/
def sgDown1 (s : I) : C(I, I) where
  toFun t := ⟨1 - (t : ℝ) * (1 - (s : ℝ)), bdd_sgDown1 s t⟩
  continuous_toFun := Continuous.subtype_mk (f := fun t : I => 1 - (t : ℝ) * (1 - (s : ℝ)))
    (by fun_prop) (fun t => bdd_sgDown1 s t)

@[simp] lemma sgDown1_zero (s : I) : sgDown1 s 0 = 1 := Subtype.ext (by simp [sgDown1])
@[simp] lemma sgDown1_one (s : I) : sgDown1 s 1 = s := Subtype.ext (by simp [sgDown1])
@[simp] lemma sgDown1_coe (s t : I) : (sgDown1 s t : ℝ) = 1 - (t : ℝ) * (1 - (s : ℝ)) := rfl

/-- Build an arc piece on the edge `e` from a parameter map and endpoint identifications. -/
def mkArcPiece {x y : GraphX a b} (e : E) (sg : C(I, I))
    (hsrc : psiFunGraph a b e (sg 0) = x) (htgt : psiFunGraph a b e (sg 1) = y) : ArcPiece a b x y :=
  { e := e
    sg := sg
    c := { toFun := fun t => psiFunGraph a b e (sg t)
           continuous_toFun := (psi_cont a b e).comp sg.continuous
           source' := hsrc
           target' := htgt }
    hc := fun t => rfl }

theorem spiderLegA {v : V} {e : E} (hae : a e = v) {s : I} (hs : (s : ℝ) < 1/3) :
    ∃ p : ArcPiece a b (psiFunGraph a b e s) (gq a b (Sum.inl v)),
      ∀ t, p.c t ∈ spider a b v := by
  refine ⟨mkArcPiece e (sgDown s) ?_ ?_, ?_⟩
  · rw [sgDown_zero]
  · rw [sgDown_one]
    exact (rel_ae a b e).trans (by rw [hae])
  · intro t
    have ht : (sgDown s t : ℝ) < 1/3 := by
      rw [sgDown_coe]
      nlinarith [hs, t.2.1, s.2.1, mul_nonneg s.2.1 t.2.1]
    have hmem : psiFunGraph a b e (sgDown s t) ∈ spider a b v := by
      rw [show v = a e from hae.symm]
      exact mem_spider_of_a a b e ht
    exact hmem

theorem spiderLegB {v : V} {e : E} (hbe : b e = v) {s : I} (hs : 2/3 < (s : ℝ)) :
    ∃ p : ArcPiece a b (psiFunGraph a b e s) (gq a b (Sum.inl v)),
      ∀ t, p.c t ∈ spider a b v := by
  refine ⟨mkArcPiece e (sgUp s) ?_ ?_, ?_⟩
  · rw [sgUp_zero]
  · rw [sgUp_one]
    exact (rel_be a b e).trans (by rw [hbe])
  · intro t
    have ht : 2/3 < (sgUp s t : ℝ) := by
      rw [sgUp_coe]
      nlinarith [hs, t.2.1, s.2.1, mul_nonneg t.2.1 (sub_nonneg.mpr s.2.2)]
    have hmem : psiFunGraph a b e (sgUp s t) ∈ spider a b v := by
      rw [show v = b e from hbe.symm]
      exact mem_spider_of_b a b e ht
    exact hmem

theorem spiderLegRevA {v : V} {e : E} (hae : a e = v) {s : I} (hs : (s : ℝ) < 1/3) :
    ∃ p : ArcPiece a b (gq a b (Sum.inl v)) (psiFunGraph a b e s),
      ∀ t, p.c t ∈ spider a b v := by
  refine ⟨mkArcPiece e (sgUp0 s) ?_ ?_, ?_⟩
  · rw [sgUp0_zero]
    change gq a b (Sum.inr (e, 0)) = gq a b (Sum.inl v)
    exact (rel_ae a b e).trans (by rw [hae])
  · rw [sgUp0_one]
  · intro t
    have ht : (sgUp0 s t : ℝ) < 1/3 := by
      rw [sgUp0_coe]
      nlinarith [hs, t.2.2, s.2.1]
    have hmem : psiFunGraph a b e (sgUp0 s t) ∈ spider a b v := by
      rw [show v = a e from hae.symm]
      exact mem_spider_of_a a b e ht
    exact hmem

theorem spiderLegRevB {v : V} {e : E} (hbe : b e = v) {s : I} (hs : 2/3 < (s : ℝ)) :
    ∃ p : ArcPiece a b (gq a b (Sum.inl v)) (psiFunGraph a b e s),
      ∀ t, p.c t ∈ spider a b v := by
  refine ⟨mkArcPiece e (sgDown1 s) ?_ ?_, ?_⟩
  · rw [sgDown1_zero]
    change gq a b (Sum.inr (e, 1)) = gq a b (Sum.inl v)
    exact (rel_be a b e).trans (by rw [hbe])
  · rw [sgDown1_one]
  · intro t
    have ht : 2/3 < (sgDown1 s t : ℝ) := by
      rw [sgDown1_coe]
      have h1 : (0 : ℝ) ≤ 1 - (s : ℝ) := by linarith [s.2.2]
      have h2 : (t : ℝ) * (1 - (s : ℝ)) ≤ 1 - (s : ℝ) := by
        calc (t : ℝ) * (1 - (s : ℝ)) ≤ 1 * (1 - (s : ℝ)) := mul_le_mul_of_nonneg_right t.2.2 h1
          _ = 1 - (s : ℝ) := by ring
      linarith
    have hmem : psiFunGraph a b e (sgDown1 s t) ∈ spider a b v := by
      rw [show v = b e from hbe.symm]
      exact mem_spider_of_b a b e ht
    exact hmem

/-! ## D. The geodesic through the vertex and the spider case -/

theorem spiderGeodesic {v : V} {x y : GraphX a b} (hx : x ∈ spider a b v)
    (hy : y ∈ spider a b v) :
    ∃ c : ArcChain a b x y, ∀ t, (ArcChain.toPath a b c) t ∈ spider a b v := by
  rcases hx with hx | ⟨e, hae, s, hs, hxs⟩ | ⟨e, hbe, s, hs, hxs⟩
  · subst hx
    rcases hy with hy | ⟨f, haf, u, hu, hyu⟩ | ⟨f, hbf, u, hu, hyu⟩
    · subst hy
      exact ⟨ArcChain.nil _, fun t => mem_spider_center a b v⟩
    · subst hyu
      obtain ⟨p, hp⟩ := spiderLegRevA (v := v) haf hu
      refine ⟨ArcChain.cons p (ArcChain.nil _), trans_mem hp ?_⟩
      intro t
      rw [show v = a f from haf.symm]
      exact mem_spider_of_a a b f hu
    · subst hyu
      obtain ⟨p, hp⟩ := spiderLegRevB (v := v) hbf hu
      refine ⟨ArcChain.cons p (ArcChain.nil _), trans_mem hp ?_⟩
      intro t
      rw [show v = b f from hbf.symm]
      exact mem_spider_of_b a b f hu
  · subst hxs
    rcases hy with hy | ⟨f, haf, u, hu, hyu⟩ | ⟨f, hbf, u, hu, hyu⟩
    · subst hy
      obtain ⟨p, hp⟩ := spiderLegA (v := v) hae hs
      exact ⟨ArcChain.cons p (ArcChain.nil _),
        trans_mem hp (fun t => mem_spider_center a b v)⟩
    · subst hyu
      obtain ⟨p₁, hp₁⟩ := spiderLegA (v := v) hae hs
      obtain ⟨p₂, hp₂⟩ := spiderLegRevA (v := v) haf hu
      refine ⟨ArcChain.cons p₁ (ArcChain.cons p₂ (ArcChain.nil _)),
        trans_mem hp₁ (trans_mem hp₂ ?_)⟩
      intro t
      rw [show v = a f from haf.symm]
      exact mem_spider_of_a a b f hu
    · subst hyu
      obtain ⟨p₁, hp₁⟩ := spiderLegA (v := v) hae hs
      obtain ⟨p₂, hp₂⟩ := spiderLegRevB (v := v) hbf hu
      refine ⟨ArcChain.cons p₁ (ArcChain.cons p₂ (ArcChain.nil _)),
        trans_mem hp₁ (trans_mem hp₂ ?_)⟩
      intro t
      rw [show v = b f from hbf.symm]
      exact mem_spider_of_b a b f hu
  · subst hxs
    rcases hy with hy | ⟨f, haf, u, hu, hyu⟩ | ⟨f, hbf, u, hu, hyu⟩
    · subst hy
      obtain ⟨p, hp⟩ := spiderLegB (v := v) hbe hs
      exact ⟨ArcChain.cons p (ArcChain.nil _),
        trans_mem hp (fun t => mem_spider_center a b v)⟩
    · subst hyu
      obtain ⟨p₁, hp₁⟩ := spiderLegB (v := v) hbe hs
      obtain ⟨p₂, hp₂⟩ := spiderLegRevA (v := v) haf hu
      refine ⟨ArcChain.cons p₁ (ArcChain.cons p₂ (ArcChain.nil _)),
        trans_mem hp₁ (trans_mem hp₂ ?_)⟩
      intro t
      rw [show v = a f from haf.symm]
      exact mem_spider_of_a a b f hu
    · subst hyu
      obtain ⟨p₁, hp₁⟩ := spiderLegB (v := v) hbe hs
      obtain ⟨p₂, hp₂⟩ := spiderLegRevB (v := v) hbf hu
      refine ⟨ArcChain.cons p₁ (ArcChain.cons p₂ (ArcChain.nil _)),
        trans_mem hp₁ (trans_mem hp₂ ?_)⟩
      intro t
      rw [show v = b f from hbf.symm]
      exact mem_spider_of_b a b f hu

/-- A path contained in a spider is homotopic to a chain of edge arcs through the vertex. -/
theorem arcChain_of_spider {v : V} {x y : GraphX a b} (δ : Path x y)
    (hδ : ∀ t, δ t ∈ spider a b v) :
    ∃ c : ArcChain a b x y, δ.Homotopic c.toPath := by
  have hx : x ∈ spider a b v := by rw [← δ.source]; exact hδ 0
  have hy : y ∈ spider a b v := by rw [← δ.target]; exact hδ 1
  obtain ⟨g, hg⟩ := spiderGeodesic (a := a) (b := b) hx hy
  have hsc : SimplyConnectedSpace ↥(spider a b v) :=
    @SimplyConnectedSpace.ofContractible _ _ (spiderContractible a b v)
  let δ' : Path (⟨x, hx⟩ : ↥(spider a b v)) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨δ t, hδ t⟩
      continuous_toFun := Continuous.subtype_mk δ.continuous hδ
      source' := Subtype.ext δ.source
      target' := Subtype.ext δ.target }
  let g' : Path (⟨x, hx⟩ : ↥(spider a b v)) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨(ArcChain.toPath a b g) t, hg t⟩
      continuous_toFun := Continuous.subtype_mk (ArcChain.toPath a b g).continuous hg
      source' := Subtype.ext (ArcChain.toPath a b g).source
      target' := Subtype.ext (ArcChain.toPath a b g).target }
  let incl : C(↥(spider a b v), GraphX a b) := ⟨Subtype.val, continuous_subtype_val⟩
  have hsub : (δ'.map incl.continuous).Homotopic (g'.map incl.continuous) :=
    (@SimplyConnectedSpace.paths_homotopic _ _ hsc _ _ δ' g').map incl
  have h1 : δ.Homotopic (δ'.map incl.continuous) :=
    ⟨(Path.Homotopy.refl δ).cast rfl (Path.ext (funext fun t => rfl))⟩
  have h2 : (ArcChain.toPath a b g).Homotopic (g'.map incl.continuous) :=
    ⟨(Path.Homotopy.refl (ArcChain.toPath a b g)).cast rfl
      (Path.ext (funext fun t => rfl))⟩
  exact ⟨g, h1.trans (hsub.trans h2.symm)⟩

/-- A path whose image lies in a middle arc of an edge. -/
theorem arcChain_of_midArc {e : E} {x y : GraphX a b} (c : Path x y)
    (hc : ∀ t, c t ∈ midArc a b e) :
    ∃ c' : ArcChain a b x y, c.Homotopic c'.toPath := by
  obtain ⟨sg, hsg, -⟩ := midArcLift a b c hc
  exact ⟨ArcChain.cons ⟨e, sg, c, hsg⟩ (ArcChain.nil y), ⟨(Path.Homotopy.transRefl c).symm⟩⟩

/-! ## E. Subdivision and assembly -/

theorem subpath_cast_homotopic {x y : GraphX a b} (γ : Path x y) (u : ℕ → I) (M : ℕ)
    (h0 : u 0 = 0) (hM : u M = 1) (hx : x = γ (u 0)) (hy : y = γ (u M)) :
    γ.Homotopic ((γ.subpath (u 0) (u M)).cast hx hy) := by
  refine homotopic_of_apply_eq_cast hx hy (fun s => ?_)
  show γ s = γ (Icc.convexComb (u 0) (u M) s)
  rw [h0, hM]
  simp

theorem exists_arcChain_subdiv {x y : GraphX a b} (γ : Path x y) (u : ℕ → I) (M : ℕ)
    (h0 : u 0 = 0) (hM : u M = 1)
    (G : (k : ℕ) → k < M → ArcChain a b (γ (u k)) (γ (u (k+1))))
    (hG : ∀ k (hk : k < M), (γ.subpath (u k) (u (k+1))).Homotopic ((G k hk).toPath)) :
    ∃ c : ArcChain a b x y, γ.Homotopic (c.toPath) := by
  have hxC : x = γ (u 0) := γ.source.symm.trans (congrArg γ h0).symm
  have hyC : y = γ (u M) := γ.target.symm.trans (congrArg γ hM).symm
  have hκ : (chainConcatNat M γ u G).toPath.Homotopic (γ.subpath (u 0) (u M)) :=
    chainConcatNat_homotopic M γ u G hG
  have hcast : ((chainConcatNat M γ u G).toPath).cast hxC hyC
      |>.Homotopic ((γ.subpath (u 0) (u M)).cast hxC hyC) :=
    Path.Homotopic.pathCast hκ hxC hyC
  refine ⟨arcChainCastEnds (chainConcatNat M γ u G) hxC hyC, ?_⟩
  refine (subpath_cast_homotopic γ u M h0 hM hxC hyC).trans ?_
  refine hcast.symm.trans ?_
  exact (arcChainCastEnds_toPath (chainConcatNat M γ u G) hxC hyC).symm


/-! ## F. The edge-path theorem, decomposition half -/

/-- The edge-path theorem, decomposition half: every path between two vertices is homotopic
(rel endpoints) to an arc chain.

Suggested route: `midArc` and `spider` form a finite open cover (`RatHurewicz/GraphPi/spiderLocal`);
take a Lebesgue number `δ` for the pulled-back cover of `unitInterval` and subdivide into intervals
of length `< δ`.  Each sub-path then has its image in one `midArc e` — giving an `ArcPiece` by
`RatHurewicz/GraphPi/midArcLift` — or in one `spider v`, where it is homotopic rel endpoints (by
`SimplyConnectedSpace.paths_homotopic`, using `RatHurewicz/GraphPi/spiderContractible`) to the
two-piece "geodesic" through the vertex: each leg of the spider is a sub-arc of `imEdge e`
(parametrised by `s ↦ psiFunGraph a b e s` with `s < 1/3`, or `s ↦ psiFunGraph a b e (1 - s * (1/3))`) and
hence is an `ArcPiece` for that edge.  Concatenating the pieces (using `Path.Homotopic.hcomp`)
gives an `ArcChain` homotopic to the original path. -/
theorem arcChainExists {E V : Type} [Fintype E] [Fintype V] [TopologicalSpace E] [DiscreteTopology E] [TopologicalSpace V] [DiscreteTopology V] (a b : E → V) {u w : V}
    (γ : Path (Work.RatHurewicz.gq a b (Sum.inl u)) (Work.RatHurewicz.gq a b (Sum.inl w))) :
    ∃ c : Work.RatHurewicz.ArcChain a b (Work.RatHurewicz.gq a b (Sum.inl u)) (Work.RatHurewicz.gq a b (Sum.inl w)),
      γ.Homotopic (Work.RatHurewicz.ArcChain.toPath a b c) := by
  classical
  let cov : (E ⊕ V) → Set I := fun i =>
    Sum.rec (fun e => γ ⁻¹' midArc a b e) (fun v => γ ⁻¹' spider a b v) i
  have hcovopen : ∀ i, IsOpen (cov i) := by
    intro i
    rcases i with e | v
    · exact IsOpen.preimage γ.continuous ((spiderLocal a b).2.1 e)
    · exact IsOpen.preimage γ.continuous ((spiderLocal a b).1 v)
  have hcovcover : (Set.univ : Set I) ⊆ ⋃ i, cov i := by
    intro s _
    rw [Set.mem_iUnion]
    have h : γ s ∈ (⋃ e : E, midArc a b e) ∪ (⋃ v : V, spider a b v) := by
      rw [(spiderLocal a b).2.2]
      exact Set.mem_univ _
    rcases h with h | h
    · rw [Set.mem_iUnion] at h
      obtain ⟨e, he⟩ := h
      exact ⟨Sum.inl e, he⟩
    · rw [Set.mem_iUnion] at h
      obtain ⟨v, hv⟩ := h
      exact ⟨Sum.inr v, hv⟩
  obtain ⟨δ, hδpos, hδ⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hcovopen hcovcover
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδpos
  set M := n + 1 with hMdef
  have hMδ : 1 / (M : ℝ) < δ := by
    rw [hMdef]
    push_cast
    exact hn
  have hMRpos : (0 : ℝ) < (M : ℝ) := by
    rw [hMdef]; push_cast; exact Nat.cast_add_one_pos n
  let g : ℕ → I := fun k => ⟨min ((k : ℝ) / M) 1, by
    exact ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩⟩
  have hgcoe : ∀ k, k ≤ M → ((g k : I) : ℝ) = (k : ℝ) / M := by
    intro k hk
    have hle : (k : ℝ) / (M : ℝ) ≤ 1 := by
      rw [div_le_one hMRpos]
      exact_mod_cast hk
    show min ((k : ℝ) / M) 1 = (k : ℝ) / M
    exact min_eq_left hle
  have hg0 : g 0 = 0 := by
    have h := hgcoe 0 (Nat.zero_le M)
    have h1 : ((g 0 : I) : ℝ) = 0 := by rw [h]; simp
    exact Subtype.ext h1
  have hgM : g M = 1 := by
    have h := hgcoe M le_rfl
    have h1 : ((g M : I) : ℝ) = 1 := by
      rw [h, div_self (ne_of_gt hMRpos)]
    exact Subtype.ext h1
  have hgstep : ∀ k, k < M → ((g (k+1) : I) : ℝ) - ((g k : I) : ℝ) = 1 / (M : ℝ) := by
    intro k hk
    rw [hgcoe (k+1) (by omega), hgcoe k (le_of_lt hk)]
    have hne : (M : ℝ) ≠ 0 := ne_of_gt hMRpos
    field_simp
    push_cast
    ring
  have hgmono : ∀ k, k < M → g k ≤ g (k+1) := by
    intro k hk
    have hk1 : ((g k : I) : ℝ) ≤ ((g (k+1) : I) : ℝ) := by
      rw [hgcoe k (le_of_lt hk), hgcoe (k+1) (by omega)]
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ k) (le_of_lt hMRpos)
    exact hk1
  have hpiece : ∀ k : ℕ, k < M → ∃ i : E ⊕ V,
      ∀ s ∈ Set.Icc (g k) (g (k+1)), s ∈ cov i := by
    intro k hk
    obtain ⟨i, hi⟩ := hδ (g k) (Set.mem_univ _)
    refine ⟨i, fun s hs => hi ?_⟩
    rw [Metric.mem_ball]
    have hs1 : ((g k : I) : ℝ) ≤ (s : ℝ) := hs.1
    have hs2 : (s : ℝ) ≤ ((g (k+1) : I) : ℝ) := hs.2
    have hd : dist (s : I) (g k) = ((s : ℝ) - ((g k : I) : ℝ)) := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
      linarith
    rw [hd]
    have hstep := hgstep k hk
    linarith
  let pick : (k : ℕ) → k < M → (E ⊕ V) := fun k hk => Classical.choose (hpiece k hk)
  have hpick : ∀ k (hk : k < M) (s : I), s ∈ Set.Icc (g k) (g (k+1)) → s ∈ cov (pick k hk) :=
    fun k hk => Classical.choose_spec (hpiece k hk)
  have hG : ∀ k : ℕ, k < M → ∃ c : ArcChain a b (γ (g k)) (γ (g (k+1))),
      (γ.subpath (g k) (g (k+1))).Homotopic (ArcChain.toPath a b c) := by
    intro k hk
    have hmem : ∀ r : I, Icc.convexComb (g k) (g (k+1)) r ∈ cov (pick k hk) :=
      fun r => hpick k hk (Icc.convexComb (g k) (g (k+1)) r)
        (convexComb_mem_Icc (u := g k) (v := g (k+1)) (r := r) (hgmono k hk))
    rcases hik : pick k hk with e | v
    · refine arcChain_of_midArc (e := e) _ ?_
      intro r
      have hr := hmem r
      rw [hik] at hr
      show γ (Icc.convexComb (g k) (g (k+1)) r) ∈ midArc a b e
      exact hr
    · refine arcChain_of_spider (v := v) _ ?_
      intro r
      have hr := hmem r
      rw [hik] at hr
      show γ (Icc.convexComb (g k) (g (k+1)) r) ∈ spider a b v
      exact hr
  let Gp : (k : ℕ) → k < M → ArcChain a b (γ (g k)) (γ (g (k+1))) :=
    fun k hk => Classical.choose (hG k hk)
  have hGp : ∀ k (hk : k < M), (γ.subpath (g k) (g (k+1))).Homotopic ((Gp k hk).toPath) :=
    fun k hk => Classical.choose_spec (hG k hk)
  obtain ⟨c, hc⟩ := exists_arcChain_subdiv γ g M hg0 hgM Gp hGp
  exact ⟨c, hc⟩


end

end Work.RatHurewicz.GraphPi
