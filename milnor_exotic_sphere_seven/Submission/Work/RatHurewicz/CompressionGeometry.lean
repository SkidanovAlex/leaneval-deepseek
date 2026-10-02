import Mathlib
import Submission.Work.RatHurewicz.CompressionDefs
import Submission.Work.RatHurewicz.exists_pinchContraction
import Submission.Work.RatHurewicz.hepCube
import Submission.Work.ThomBordism.TwoSet.ConeDescent

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Geometry of the compression property

The geometric lemmas behind `Work.RatHurewicz.compression_of_relPiVanishing` (the equivalence
(3) ⟺ (1) of tom Dieck, *Algebraic Topology*, Proposition 6.7.5).  The vocabulary is in
`Submission/Work/RatHurewicz/CompressionDefs.lean`.

* `hepCubeNat` is the homotopy extension property of the cube pair `(I^n, ∂I^n)`;
* `exists_pinch` homotopes an arbitrary map of pairs `(I^{e+1}, ∂I^{e+1}) → (Y,A)` *through maps of
  pairs* to a map pinched at `f (pinchBase e)` (tom Dieck (6.7.3): a map of pairs is homotoped to a
  map of triples).
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Topology unitInterval
open Work.ThomBordism.TwoSet (rad bpt)

namespace Work.RatHurewicz

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {A : Set Y}
variable {e : ℕ}

/-- The homotopy extension property for the cube of any dimension (including `0`, where the
boundary is empty), deduced from `Work.RatHurewicz.hepCube`. -/
theorem hepCubeNat (n : ℕ) {Z : Type} [TopologicalSpace Z] (f : C(ICube n, Z))
    (h : C(↥(Cube.boundary (Fin n)) × unitInterval, Z))
    (h0 : ∀ x : ↥(Cube.boundary (Fin n)), h (x, 0) = f x.1) :
    ∃ H : C(ICube n × unitInterval, Z), (∀ x, H (x, 0) = f x) ∧
      (∀ x : ↥(Cube.boundary (Fin n)), ∀ τ : unitInterval, H (x.1, τ) = h (x, τ)) := by
  rcases Nat.eq_zero_or_pos n with hz | hn
  · cases hz
    refine ⟨⟨fun p => f p.1, f.continuous.comp continuous_fst⟩, fun x => rfl, fun x τ => ?_⟩
    exact absurd x.2 (by rintro ⟨i, -⟩; exact i.elim0)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
    exact hepCube k f h h0

/-- A point of `∂I^{e+1}` whose last coordinate is not `1` lies in `PinchSet e`. -/
theorem mem_pinchSet_of_mem_boundary_of_last_ne_one {x : ICube (e + 1)}
    (hx : x ∈ Cube.boundary (Fin (e + 1))) (h1 : x (Fin.last e) ≠ 1) : x ∈ PinchSet e := by
  obtain ⟨i, hi | hi⟩ := hx
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Or.inr ⟨j, Or.inl hi⟩
    · exact Or.inl hi
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Or.inr ⟨j, Or.inr hi⟩
    · exact absurd hi h1

theorem isClosed_pinchSet (e : ℕ) : IsClosed (PinchSet e) := by
  have hset : PinchSet e = {x : ICube (e + 1) | x (Fin.last e) = 0} ∪
      ⋃ i : Fin e, ({x : ICube (e + 1) | x (Fin.castSucc i) = 0} ∪
        {x : ICube (e + 1) | x (Fin.castSucc i) = 1}) := by
    ext x
    simp only [PinchSet, Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion]
  rw [hset]
  refine IsClosed.union ?_ ?_
  · exact isClosed_eq (continuous_apply (Fin.last e)) continuous_const
  · refine isClosed_iUnion_of_finite fun i => ?_
    exact (isClosed_eq (continuous_apply (Fin.castSucc i)) continuous_const).union
      (isClosed_eq (continuous_apply (Fin.castSucc i)) continuous_const)

theorem continuous_snocOne (e : ℕ) :
    Continuous fun u : ICube e => (Fin.snoc u 1 : ICube (e + 1)) := by
  refine continuous_pi fun i => ?_
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp only [Fin.snoc_castSucc]
    exact continuous_apply j
  · simp only [Fin.snoc_last]
    exact continuous_const

theorem continuous_init (e : ℕ) : Continuous fun x : ICube (e + 1) => Fin.init x := by
  refine continuous_pi fun j => ?_
  exact continuous_apply (Fin.castSucc j)

/-- A point `Fin.snoc u s` of `I^{e+1}` whose first `e` coordinates contain a `0` or a `1` lies in
the pinched part. -/
theorem snoc_mem_pinchSet (e : ℕ) (u : ICube e) (hu : ∃ i : Fin e, u i = 0 ∨ u i = 1)
    (s : unitInterval) : (Fin.snoc u s : ICube (e + 1)) ∈ PinchSet e := by
  obtain ⟨i, hi⟩ := hu
  exact Or.inr ⟨i, by rw [Fin.snoc_castSucc]; exact hi⟩

theorem snocOne_mem_pinchSet (e : ℕ) (u : ICube e) (hu : ∃ i : Fin e, u i = 0 ∨ u i = 1) :
    (Fin.snoc u 1 : ICube (e + 1)) ∈ PinchSet e := snoc_mem_pinchSet e u hu 1

/-- Reassembling the coordinates of a cube from its first `e` coordinates and a last coordinate
equal to `1`. -/
theorem snoc_init_eq {x : ICube (e + 1)} (h : x (Fin.last e) = 1) : Fin.snoc (Fin.init x) 1 = x := by
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]
    rfl
  · rw [Fin.snoc_last, h]

/-- **Making a map of pairs pinched** (tom Dieck (6.7.3)).  Every map of pairs
`f : (I^{e+1}, ∂I^{e+1}) → (Y,A)` is homotopic *through maps of pairs* to a map pinched at
`f (pinchBase e) ∈ A`. -/
theorem exists_pinch (e : ℕ) (f : C(ICube (e + 1), Y))
    (hf : ∀ x, x ∈ Cube.boundary (Fin (e + 1)) → f x ∈ A) :
    ∃ H1 : C(ICube (e + 1) × unitInterval, Y),
      (∀ x, H1 (x, 0) = f x) ∧
      (∀ x, x ∈ Cube.boundary (Fin (e + 1)) → ∀ τ : unitInterval, H1 (x, τ) ∈ A) ∧
      IsPinchedAt e ⟨fun x => H1 (x, 1), by fun_prop⟩ (f (pinchBase e)) := by
  classical
  obtain ⟨κ, hκ0, hκ1, hκbd⟩ := exists_pinchContraction e
  -- the homotopy on the pinched part `J`, with values in `A`
  set hJcm : C(↥(PinchSet e) × unitInterval, ↥A) :=
    ⟨fun p => ⟨f (κ p), hf _ (hκbd p.1 p.2)⟩,
      Continuous.subtype_mk (f.continuous.comp κ.continuous) (fun p => hf _ (hκbd p.1 p.2))⟩
    with hJcm_def
  -- the rim of the top face, as a subspace of the pinched part
  set hrim : C(↥(Cube.boundary (Fin e)) × unitInterval, ↥(PinchSet e)) :=
    ⟨fun p => ⟨Fin.snoc p.1.1 1, snocOne_mem_pinchSet e p.1.1 p.1.2⟩,
      Continuous.subtype_mk ((continuous_snocOne e).comp (continuous_subtype_val.comp continuous_fst))
        (fun p => snocOne_mem_pinchSet e p.1.1 p.1.2)⟩ with hrim_def
  -- the top face
  set hTcm : C(ICube e, ↥A) :=
    ⟨fun u => ⟨f (Fin.snoc u 1), hf _ ⟨Fin.last e, Or.inr (Fin.snoc_last ..)⟩⟩,
      Continuous.subtype_mk (f.continuous.comp (continuous_snocOne e))
        (fun u => hf _ ⟨Fin.last e, Or.inr (Fin.snoc_last ..)⟩)⟩ with hTcm_def
  -- the prescribed homotopy on the rim
  set hRcm : C(↥(Cube.boundary (Fin e)) × unitInterval, ↥A) :=
    ⟨fun p => ⟨f (κ (hrim p, p.2)), hf _ (hκbd (hrim p) p.2)⟩,
      Continuous.subtype_mk (f.continuous.comp (κ.continuous.comp
        (hrim.continuous.prodMk continuous_snd)))
        (fun p => hf _ (hκbd (hrim p) p.2))⟩ with hRcm_def
  have hR0 : ∀ q : ↥(Cube.boundary (Fin e)), hRcm (q, 0) = hTcm q.1 := by
    intro q
    apply Subtype.ext
    rw [hRcm_def, hrim_def, hTcm_def]
    simp only [ContinuousMap.coe_mk]
    rw [hκ0]
  -- the homotopy on the top face extending the rim motion
  obtain ⟨HT, hT0, hTbd⟩ := hepCubeNat e hTcm hRcm hR0
  -- the values of `HT` on the rim, in terms of the contraction
  have hagree : ∀ (q : ↥(Cube.boundary (Fin e))) (τ : unitInterval),
      HT (q.1, τ) = hJcm (⟨Fin.snoc q.1 1, snocOne_mem_pinchSet e q.1 q.2⟩, τ) := by
    intro q τ
    rw [hTbd q τ, hRcm_def, hrim_def, hJcm_def]
    simp only [ContinuousMap.coe_mk]
  -- the glued boundary homotopy `∂I^{e+1} × I → A`
  set hbdA : ↥(Cube.boundary (Fin (e + 1))) × unitInterval → ↥A := fun p =>
    if h : p.1.1 (Fin.last e) = 1 then HT (Fin.init p.1.1, p.2)
    else hJcm (⟨p.1.1, mem_pinchSet_of_mem_boundary_of_last_ne_one p.1.2 h⟩, p.2)
    with hbdA_def
  have hbdA_pos : ∀ (p : ↥(Cube.boundary (Fin (e + 1))) × unitInterval)
      (h : p.1.1 (Fin.last e) = 1), hbdA p = HT (Fin.init p.1.1, p.2) := by
    intro p h
    rw [hbdA_def]
    exact dif_pos h
  have hbdA_neg : ∀ (p : ↥(Cube.boundary (Fin (e + 1))) × unitInterval)
      (h : ¬ p.1.1 (Fin.last e) = 1),
      hbdA p = hJcm (⟨p.1.1, mem_pinchSet_of_mem_boundary_of_last_ne_one p.1.2 h⟩, p.2) := by
    intro p h
    rw [hbdA_def]
    exact dif_neg h
  have hA1 : IsClosed {p : ↥(Cube.boundary (Fin (e + 1))) × unitInterval |
      p.1.1 (Fin.last e) = 1} :=
    isClosed_eq ((continuous_apply (Fin.last e)).comp
      (continuous_subtype_val.comp continuous_fst)) continuous_const
  have hA2 : IsClosed {p : ↥(Cube.boundary (Fin (e + 1))) × unitInterval |
      (p.1.1 : ICube (e + 1)) ∈ PinchSet e} :=
    (isClosed_pinchSet e).preimage (continuous_subtype_val.comp continuous_fst)
  have hcont1 : ContinuousOn hbdA {p : ↥(Cube.boundary (Fin (e + 1))) × unitInterval |
      p.1.1 (Fin.last e) = 1} := by
    have hc : Continuous fun q : ↥({p : ↥(Cube.boundary (Fin (e + 1))) × unitInterval |
        p.1.1 (Fin.last e) = 1}) => HT (Fin.init q.1.1.1, q.1.2) :=
      HT.continuous.comp (Continuous.prodMk ((continuous_init e).comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)))
        (continuous_snd.comp continuous_subtype_val))
    have h1 : Set.domRestrict {p : ↥(Cube.boundary (Fin (e + 1))) × unitInterval |
        p.1.1 (Fin.last e) = 1} hbdA
        = fun q : ↥({p : ↥(Cube.boundary (Fin (e + 1))) × unitInterval |
            p.1.1 (Fin.last e) = 1}) => HT (Fin.init q.1.1.1, q.1.2) := by
      funext q
      exact hbdA_pos q.1 q.2
    rw [continuousOn_iff_continuous_domRestrict, h1]
    exact hc
  have hcont2 : ContinuousOn hbdA {p : ↥(Cube.boundary (Fin (e + 1))) × unitInterval |
      (p.1.1 : ICube (e + 1)) ∈ PinchSet e} := by
    have hc : Continuous fun q : ↥({p : ↥(Cube.boundary (Fin (e + 1))) × unitInterval |
        (p.1.1 : ICube (e + 1)) ∈ PinchSet e}) =>
        hJcm (⟨q.1.1.1, q.2⟩, q.1.2) :=
      hJcm.continuous.comp (Continuous.prodMk
        (Continuous.subtype_mk (continuous_subtype_val.comp
          (continuous_fst.comp continuous_subtype_val)) (fun q => q.2))
        (continuous_snd.comp continuous_subtype_val))
    have h1 : Set.domRestrict {p : ↥(Cube.boundary (Fin (e + 1))) × unitInterval |
        (p.1.1 : ICube (e + 1)) ∈ PinchSet e} hbdA
        = fun q : ↥({p : ↥(Cube.boundary (Fin (e + 1))) × unitInterval |
            (p.1.1 : ICube (e + 1)) ∈ PinchSet e}) => hJcm (⟨q.1.1.1, q.2⟩, q.1.2) := by
      funext q
      change hbdA q.1 = hJcm (⟨q.1.1.1, q.2⟩, q.1.2)
      by_cases h : q.1.1.1 (Fin.last e) = 1
      · have hwit : ∃ j : Fin e, Fin.init q.1.1.1 j = 0 ∨ Fin.init q.1.1.1 j = 1 := by
          rcases q.2 with h0 | ⟨j, hj⟩
          · exact absurd (h0 ▸ h : (0 : unitInterval) = 1) zero_ne_one
          · exact ⟨j, hj⟩
        have h2 := hagree ⟨Fin.init q.1.1.1, hwit⟩ q.1.2
        have harg : (⟨Fin.snoc (Fin.init q.1.1.1) 1,
              snocOne_mem_pinchSet e (Fin.init q.1.1.1) hwit⟩ : ↥(PinchSet e))
            = ⟨q.1.1.1, q.2⟩ := Subtype.ext (snoc_init_eq h)
        rw [hbdA_pos q.1 h]
        exact h2.trans (congrArg (fun z => hJcm (z, q.1.2)) harg)
      · exact hbdA_neg q.1 h
    rw [continuousOn_iff_continuous_domRestrict, h1]
    exact hc
  have hbdA_cont : Continuous hbdA := by
    have hcov : {p : ↥(Cube.boundary (Fin (e + 1))) × unitInterval | p.1.1 (Fin.last e) = 1} ∪
        {p : ↥(Cube.boundary (Fin (e + 1))) × unitInterval |
          (p.1.1 : ICube (e + 1)) ∈ PinchSet e} = Set.univ := by
      ext p
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      by_cases h : p.1.1 (Fin.last e) = 1
      · exact Or.inl h
      · exact Or.inr (mem_pinchSet_of_mem_boundary_of_last_ne_one p.1.2 h)
    have hall := ContinuousOn.union_of_isClosed hcont1 hcont2 hA1 hA2
    rw [hcov] at hall
    exact continuousOn_univ.mp hall
  -- the boundary homotopy as a map into `Y`
  set hbd : C(↥(Cube.boundary (Fin (e + 1))) × unitInterval, Y) :=
    ⟨fun p => (hbdA p : Y), continuous_subtype_val.comp hbdA_cont⟩ with hbd_def
  have hbdval : ∀ p : ↥(Cube.boundary (Fin (e + 1))) × unitInterval, hbd p = (hbdA p : Y) :=
    fun p => rfl
  have hbd0 : ∀ x : ↥(Cube.boundary (Fin (e + 1))), hbd (x, 0) = f x.1 := by
    intro x
    rw [hbdval]
    by_cases h : x.1 (Fin.last e) = 1
    · rw [hbdA_pos (x, 0) h, hT0, hTcm_def]
      simp only [ContinuousMap.coe_mk]
      rw [snoc_init_eq h]
    · rw [hbdA_neg (x, 0) h, hJcm_def]
      simp only [ContinuousMap.coe_mk]
      rw [hκ0]
  obtain ⟨H1, hH10, hH1bd⟩ := hepCube e f hbd hbd0
  refine ⟨H1, hH10, fun x hx τ => ?_, ?_, ?_⟩
  · -- values on the boundary
    rw [hH1bd ⟨x, hx⟩ τ, hbdval]
    by_cases h : x (Fin.last e) = 1
    · rw [hbdA_pos (⟨x, hx⟩, τ) h]
      exact (HT (Fin.init x, τ)).2
    · rw [hbdA_neg (⟨x, hx⟩, τ) h]
      exact (hJcm (⟨x, mem_pinchSet_of_mem_boundary_of_last_ne_one hx h⟩, τ)).2
  · -- the bottom face
    intro u
    have hx : (Fin.snoc u (0 : unitInterval) : ICube (e + 1)) ∈ Cube.boundary (Fin (e + 1)) :=
      ⟨Fin.last e, Or.inl (Fin.snoc_last ..)⟩
    have hne : (Fin.snoc u (0 : unitInterval) : ICube (e + 1)) (Fin.last e) ≠ 1 := by
      rw [Fin.snoc_last]
      exact zero_ne_one
    simp only [ContinuousMap.coe_mk]
    rw [hH1bd ⟨Fin.snoc u (0 : unitInterval), hx⟩ 1, hbdval,
      hbdA_neg (⟨Fin.snoc u (0 : unitInterval), hx⟩, 1) hne, hJcm_def]
    simp only [ContinuousMap.coe_mk]
    rw [hκ1]
  · -- the side faces
    intro u s hu
    have hx : (Fin.snoc u s : ICube (e + 1)) ∈ Cube.boundary (Fin (e + 1)) := by
      obtain ⟨i, hi⟩ := hu
      exact ⟨Fin.castSucc i, by rw [Fin.snoc_castSucc]; exact hi⟩
    by_cases hs : s = 1
    · have hinit : Fin.init (Fin.snoc u s : ICube (e + 1)) = u := by
        funext j
        show (Fin.snoc u s : ICube (e + 1)) (Fin.castSucc j) = u j
        rw [Fin.snoc_castSucc]
      have hlast : (Fin.snoc u s : ICube (e + 1)) (Fin.last e) = 1 := by
        rw [Fin.snoc_last]
        exact hs
      simp only [ContinuousMap.coe_mk]
      rw [hH1bd ⟨Fin.snoc u s, hx⟩ 1, hbdval,
        hbdA_pos (⟨Fin.snoc u s, hx⟩, 1) hlast]
      rw [hinit, hagree ⟨u, hu⟩ 1, hJcm_def]
      simp only [ContinuousMap.coe_mk]
      rw [hκ1]
    · have hne : (Fin.snoc u s : ICube (e + 1)) (Fin.last e) ≠ 1 := by
        rw [Fin.snoc_last]
        exact hs
      simp only [ContinuousMap.coe_mk]
      rw [hH1bd ⟨Fin.snoc u s, hx⟩ 1, hbdval,
        hbdA_neg (⟨Fin.snoc u s, hx⟩, 1) hne, hJcm_def]
      simp only [ContinuousMap.coe_mk]
      rw [hκ1]

end

end Work.RatHurewicz
