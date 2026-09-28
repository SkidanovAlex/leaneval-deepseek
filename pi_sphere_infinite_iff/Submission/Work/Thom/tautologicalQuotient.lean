import Mathlib
import Submission.Work.Thom.QuotientLin
import Submission.Work.Thom.realification
import Submission.Work.Thom.Basic
import Submission.Work.TangentClasses.Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSimpArgs false

/-!
# The tautological quotient bundle `π*V / ℂ·s` over the complement of the zero section

This is the algebraic-geometric content of the Thom chapter's *tautological quotient*: for a complex
vector bundle `Z` of rank `n+1` over `B`, the total space of the realification of `Z` (with the
zero section removed) carries the tautological sub-line bundle `ℂ·s`, and the quotient
`π*V / ℂ·s` is again a complex vector bundle, of rank `n`.

Concretely we build the gluing data (`VectorBundleCore`) of that quotient.  Its cover is indexed by
`ι × Fin (n+1)`: over the chart where the pair `(i,k)` is chosen, the `k`-th coordinate of the
tautological section is invertible in the chart `i`, and the trivialization of `Q` is given by the
"quotient projection along the tautological section"

`(z) ↦ quoFun k w (Z.coordChange i j b (fillFun k z))`,

`Work.Thom.quoFun`/`Work.Thom.fillFun` being the splitting of `Work.Thom.QuotientLin`.  The three
properties proved about the constructed core are exactly the interface the rest of the chapter
(`H^n(E,E∖0)` of the resulting `S^n`-fibration) needs: the cover, the chosen index, and the
transition functions.
-/

open scoped RealInnerProductSpace

namespace Work.Thom

noncomputable section

/-! ## The linear algebra of the coordinate splitting, as continuous linear maps -/

variable {n : ℕ}

theorem fillFun_add (k : Fin (n + 1)) (z z' : EuclideanSpace ℂ (Fin n)) :
    fillFun k (z + z') = fillFun k z + fillFun k z' := by
  simp only [fillFun, WithLp.ofLp_add, Pi.add_apply, add_smul]
  rw [Finset.sum_add_distrib]

theorem fillFun_smul (k : Fin (n + 1)) (c : ℂ) (z : EuclideanSpace ℂ (Fin n)) :
    fillFun k (c • z) = c • fillFun k z := by
  simp only [fillFun, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
  rw [Finset.smul_sum]

/-- The **filling** `ℂ^n → ℂ^{n+1}` as a continuous linear map. -/
def fillCLM (k : Fin (n + 1)) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin (n + 1)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fillFun k, map_add' := fillFun_add k, map_smul' := fillFun_smul k }

theorem fillCLM_apply (k : Fin (n + 1)) (z : EuclideanSpace ℂ (Fin n)) :
    fillCLM k z = fillFun k z := rfl

/-- The **forgetting of the `k`-th coordinate** `ℂ^{n+1} → ℂ^n` as a continuous linear map. -/
def dropCLM (k : Fin (n + 1)) : EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := dropFun k, map_add' := dropFun_add k, map_smul' := dropFun_smul k }

theorem dropCLM_apply (k : Fin (n + 1)) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    dropCLM k u = dropFun k u := rfl

/-- The `l`-th coordinate as a continuous linear functional. -/
def evalCLM (l : Fin (n + 1)) : EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => u l, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem evalCLM_apply (l : Fin (n + 1)) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    evalCLM l u = u l := rfl

theorem quoFun_add (k : Fin (n + 1)) (w u v : EuclideanSpace ℂ (Fin (n + 1))) :
    quoFun k w (u + v) = quoFun k w u + quoFun k w v := by
  ext m
  simp only [quoFun_apply, WithLp.ofLp_add, Pi.add_apply]
  ring

theorem quoFun_smul (k : Fin (n + 1)) (w u : EuclideanSpace ℂ (Fin (n + 1))) (c : ℂ) :
    quoFun k w (c • u) = c • quoFun k w u := by
  ext m
  simp only [quoFun_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- The **quotient projection along `w`** as a continuous linear map. -/
def quoCLM (l : Fin (n + 1)) (w : EuclideanSpace ℂ (Fin (n + 1))) :
    EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := quoFun l w, map_add' := quoFun_add l w, map_smul' := fun m x => quoFun_smul l w x m }

theorem quoCLM_apply (l : Fin (n + 1)) (w u : EuclideanSpace ℂ (Fin (n + 1))) :
    quoCLM l w u = quoFun l w u := rfl

/-- `quoFun` as a function of `w`, in the form used to discuss its continuity. -/
theorem quoCLM_eq (l : Fin (n + 1)) (w : EuclideanSpace ℂ (Fin (n + 1))) :
    quoCLM l w = dropCLM l - (evalCLM l).smulRight ((w l)⁻¹ • dropFun l w) := by
  ext u
  simp only [quoCLM_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
    dropCLM_apply, evalCLM_apply, quoFun, div_eq_mul_inv, smul_smul]

theorem quoCLM_eq' (l : Fin (n + 1)) (w : EuclideanSpace ℂ (Fin (n + 1))) :
    quoCLM l w = dropCLM l - (evalCLM l).smulRight ((evalCLM l w)⁻¹ • dropFun l w) := by
  rw [quoCLM_eq l w]
  simp only [evalCLM_apply]

/-- **The transport identity at the heart of the cocycle condition.**  If `A w = w'` and `w' o ≠ 0`,
then the class of `A u` modulo the line `ℂ w'` only depends on the class of `u` modulo `ℂ w`. -/
theorem quoFun_transport (l o : Fin (n + 1))
    (A : EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (n + 1)))
    (wj wm u : EuclideanSpace ℂ (Fin (n + 1)))
    (hwj : wj l ≠ 0) (hwm : wm o ≠ 0) (hA : A wj = wm) :
    quoFun o wm (A u) = quoFun o wm (A (fillFun l (quoFun l wj u))) := by
  have h1 : A u - A (fillFun l (quoFun l wj u)) = (u l / wj l) • wm := by
    rw [← map_sub, sub_fillFun_quoFun l wj u hwj, map_smul, hA]
  have hA2 : A u = A (fillFun l (quoFun l wj u)) + (u l / wj l) • wm :=
    sub_eq_iff_eq_add'.mp h1
  rw [hA2, quoFun_add, quoFun_smul, quoFun_self o wm hwm, smul_zero, add_zero]

/-! ## The gluing data of the tautological quotient -/

variable {B : Type} [TopologicalSpace B] {ι : Type}
variable (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι)

/-- The chart of the tautological quotient indexed by `(i,k)`: the base points of the chart `i` of
`Z` at which the `k`-th coordinate of (the tautological section read in the chart `i`) does not
vanish. -/
def tqBaseSet (i : ι) (k : Fin (n + 1)) : Set ↥(zeroComplement (realification Z)) :=
  {p | ((p : (realification Z).TotalSpace).1) ∈ Z.baseSet i ∧
       (Z.localTriv i (p : (realification Z).TotalSpace)).2 k ≠ 0}

/-- The local trivializations of the realification and of `Z` have the same second component. -/
theorem localTriv_snd_eq (i : ι) (q : (realification Z).TotalSpace) :
    ((realification Z).localTriv i q).2 = (Z.localTriv i q).2 := by
  rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply]
  rw [realification_indexAt, realification_coordChange]

/-- The second component of a local trivialization is continuous (on its source). -/
theorem continuousOn_localTriv_snd_realification (j : ι) :
    ContinuousOn (fun q : (realification Z).TotalSpace => (((realification Z).localTriv j q)).2)
      ((realification Z).localTriv j).source := by
  refine (continuous_snd.comp_continuousOn
    ((realification Z).localTriv j).continuousOn_toFun).congr ?_
  intro q hq
  rfl

theorem exists_coord_ne_zero_aux (v : EuclideanSpace ℂ (Fin (n + 1))) (hv : v ≠ 0) :
    ∃ k : Fin (n + 1), v k ≠ 0 := by
  by_contra h
  push Not at h
  exact hv (by ext i; simpa using h i)

theorem localTriv_snd_ne_zero (q : (realification Z).TotalSpace)
    (hq : (show EuclideanSpace ℂ (Fin (n + 1)) from q.2) ≠ 0) :
    (Z.localTriv (Z.indexAt q.1) q).2 ≠ 0 := by
  intro h
  apply hq
  rw [VectorBundleCore.localTriv_apply] at h
  simpa only [Z.coordChange_self (Z.indexAt q.1) q.1 (Z.mem_baseSet_at q.1)] using h

/-- In the complement of the zero section, the tautological section has a non-vanishing coordinate
in the preferred chart of the base point. -/
theorem exists_coord_ne_zero_localTriv (p : ↥(zeroComplement (realification Z))) :
    ∃ k : Fin (n + 1),
      (Z.localTriv (Z.indexAt ((p : (realification Z).TotalSpace).1))
        (p : (realification Z).TotalSpace)).2 k ≠ 0 := by
  have hq : (show EuclideanSpace ℂ (Fin (n + 1)) from
      ((p : (realification Z).TotalSpace)).2) ≠ 0 :=
    (mem_zeroComplement _).mp p.2
  exact exists_coord_ne_zero_aux _ (localTriv_snd_ne_zero Z _ hq)

/-- The chosen non-vanishing coordinate of the tautological section at a point of the complement of
the zero section. -/
noncomputable def tqCoord (p : ↥(zeroComplement (realification Z))) : Fin (n + 1) :=
  Classical.choose (exists_coord_ne_zero_localTriv Z p)

theorem tqCoord_spec (p : ↥(zeroComplement (realification Z))) :
    (Z.localTriv (Z.indexAt ((p : (realification Z).TotalSpace).1))
      (p : (realification Z).TotalSpace)).2 (tqCoord Z p) ≠ 0 :=
  Classical.choose_spec (exists_coord_ne_zero_localTriv Z p)

/-- The transition function composed with the local trivialization is the local trivialization. -/
theorem coordChange_localTriv_snd (j m : ι) (q : (realification Z).TotalSpace)
    (hj : q.1 ∈ Z.baseSet j) (hm : q.1 ∈ Z.baseSet m) :
    (Z.coordChange j m q.1) ((Z.localTriv j q).2) = (Z.localTriv m q).2 := by
  rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply]
  exact Z.coordChange_comp (Z.indexAt q.1) j m q.1 ⟨⟨Z.mem_baseSet_at q.1, hj⟩, hm⟩ q.2

/-- **Continuity of the transition functions** of the tautological quotient, in terms of the
trivializations of the realification. -/
theorem continuousOn_coordChange_aux (i j : ι) (k l : Fin (n + 1)) :
    ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      (quoCLM l (((realification Z).localTriv j (p : (realification Z).TotalSpace))).2).comp
        ((Z.coordChange i j ((p : (realification Z).TotalSpace)).1).comp (fillCLM k)))
      (tqBaseSet Z i k ∩ tqBaseSet Z j l) := by
  have hW : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      (((realification Z).localTriv j (p : (realification Z).TotalSpace))).2)
      (tqBaseSet Z i k ∩ tqBaseSet Z j l) := by
    refine (continuousOn_localTriv_snd_realification Z j).comp
      continuous_subtype_val.continuousOn ?_
    intro p hp
    rw [VectorBundleCore.mem_localTriv_source, realification_baseSet]
    exact hp.2.1
  have hWl : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      ((evalCLM l) ((((realification Z).localTriv j (p : (realification Z).TotalSpace))).2))⁻¹)
      (tqBaseSet Z i k ∩ tqBaseSet Z j l) := by
    refine (((evalCLM l).continuous.comp_continuousOn hW)).inv₀ ?_
    intro p hp
    simp only [Function.comp_apply, evalCLM_apply,
      localTriv_snd_eq Z j (p : (realification Z).TotalSpace)]
    exact hp.2.2
  have hdrop : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      dropFun l ((((realification Z).localTriv j (p : (realification Z).TotalSpace))).2))
      (tqBaseSet Z i k ∩ tqBaseSet Z j l) := by
    refine ((dropCLM l).continuous.comp_continuousOn hW).congr ?_
    intro p hp
    simp only [Function.comp_apply, dropCLM_apply]
  have hK : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      ((evalCLM l) ((((realification Z).localTriv j (p : (realification Z).TotalSpace))).2))⁻¹ •
      (dropFun l ((((realification Z).localTriv j (p : (realification Z).TotalSpace))).2)))
      (tqBaseSet Z i k ∩ tqBaseSet Z j l) := hWl.smul hdrop
  have hsm : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      (evalCLM l).smulRight
        (((evalCLM l) ((((realification Z).localTriv j (p : (realification Z).TotalSpace))).2))⁻¹ •
        (dropFun l ((((realification Z).localTriv j (p : (realification Z).TotalSpace))).2))))
      (tqBaseSet Z i k ∩ tqBaseSet Z j l) := by
    refine ((ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin (n + 1)))
      (EuclideanSpace ℂ (Fin n)) (evalCLM l)).continuous.comp_continuousOn hK).congr ?_
    intro p hp
    dsimp only
    exact ContinuousLinearMap.smulRightL_apply_apply ℂ (EuclideanSpace ℂ (Fin (n + 1)))
      (EuclideanSpace ℂ (Fin n)) (evalCLM l) _
  have hG : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      dropCLM l - (evalCLM l).smulRight
        (((evalCLM l) ((((realification Z).localTriv j
          (p : (realification Z).TotalSpace))).2))⁻¹ •
        (dropFun l ((((realification Z).localTriv j (p : (realification Z).TotalSpace))).2))))
      (tqBaseSet Z i k ∩ tqBaseSet Z j l) := continuousOn_const.sub hsm
  have hb : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      ((p : (realification Z).TotalSpace)).1) (tqBaseSet Z i k ∩ tqBaseSet Z j l) := by
    refine (((realification Z).continuous_proj.comp continuous_subtype_val).continuousOn).congr ?_
    intro p hp
    rfl
  have hA : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      Z.coordChange i j ((p : (realification Z).TotalSpace)).1)
      (tqBaseSet Z i k ∩ tqBaseSet Z j l) := by
    refine ((Z.continuousOn_coordChange i j).comp hb ?_).congr ?_
    · intro p hp
      exact ⟨hp.1.1, hp.2.1⟩
    · intro p hp
      rfl
  have hF : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      (Z.coordChange i j ((p : (realification Z).TotalSpace)).1).comp (fillCLM k))
      (tqBaseSet Z i k ∩ tqBaseSet Z j l) := by
    refine (hA.clm_comp (continuousOn_const :
      ContinuousOn (fun _ : ↥(zeroComplement (realification Z)) => fillCLM k) _)).congr ?_
    intro p hp
    rfl
  refine (hG.clm_comp hF).congr ?_
  intro p hp
  dsimp only
  rw [quoCLM_eq' l (((realification Z).localTriv j (p : (realification Z).TotalSpace))).2]

/-- Continuity of the transition functions of the tautological quotient, in the form in which the
core is defined. -/
theorem continuousOn_coordChange_tq (i j : ι) (k l : Fin (n + 1)) :
    ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      (quoCLM l ((Z.localTriv j (p : (realification Z).TotalSpace)).2)).comp
        ((Z.coordChange i j ((p : (realification Z).TotalSpace)).1).comp (fillCLM k)))
      (tqBaseSet Z i k ∩ tqBaseSet Z j l) := by
  refine (continuousOn_coordChange_aux Z i j k l).congr ?_
  intro p hp
  dsimp only
  rw [← localTriv_snd_eq Z j (p : (realification Z).TotalSpace)]

/-- The charts of the tautological quotient are open. -/
theorem isOpen_tqBaseSet (i : ι) (k : Fin (n + 1)) : IsOpen (tqBaseSet Z i k) := by
  have hopen : IsOpen {v : EuclideanSpace ℂ (Fin (n + 1)) | v k ≠ 0} := by
    have hset : {v : EuclideanSpace ℂ (Fin (n + 1)) | v k ≠ 0}
        = (⇑(evalCLM k) ⁻¹' {0})ᶜ := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        evalCLM_apply]
    rw [hset]
    exact (isClosed_singleton.preimage (evalCLM k).continuous).isOpen_compl
  have hpre : tqBaseSet Z i k =
      (fun p : ↥(zeroComplement (realification Z)) => (p : (realification Z).TotalSpace)) ⁻¹'
        (((realification Z).localTriv i).source ∩
          ↑((realification Z).localTriv i) ⁻¹'
            (Set.univ ×ˢ {v : EuclideanSpace ℂ (Fin (n + 1)) | v k ≠ 0})) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod,
      Set.mem_univ, true_and, VectorBundleCore.mem_localTriv_source, realification_baseSet]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [localTriv_snd_eq Z i (p : (realification Z).TotalSpace)]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← localTriv_snd_eq Z i (p : (realification Z).TotalSpace)]; exact h2⟩
  rw [hpre]
  exact IsOpen.preimage continuous_subtype_val
    (((realification Z).localTriv i).isOpen_inter_preimage (isOpen_univ.prod hopen))

/-! ## The tautological quotient -/

/-- **The tautological quotient bundle** `π*V / ℂ·s` of a complex vector bundle `Z` of rank `n+1`
over its total space with the zero section removed: a complex vector bundle of rank `n`, on the
cover indexed by `(i,k)` consisting of the points where the `k`-th coordinate of the tautological
section in the chart `i` is invertible, with transition functions the quotient projections
`quoFun`. -/
theorem tautologicalQuotient
    {B : Type} [TopologicalSpace B] {ι : Type} {n : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι) :
    ∃ Q : VectorBundleCore ℂ ↥(Work.Thom.zeroComplement (Work.Thom.realification Z))
        (EuclideanSpace ℂ (Fin n)) (ι × Fin (n + 1)),
      (∀ (i : ι) (k : Fin (n + 1)),
        Q.baseSet (i, k) = {p : ↥(Work.Thom.zeroComplement (Work.Thom.realification Z)) |
          ((p : (Work.Thom.realification Z).TotalSpace).1) ∈ Z.baseSet i ∧
            (Z.localTriv i ((p : (Work.Thom.realification Z).TotalSpace))).2 k ≠ 0}) ∧
      (∀ (p : ↥(Work.Thom.zeroComplement (Work.Thom.realification Z))),
        (Q.indexAt p).1 = Z.indexAt ((p : (Work.Thom.realification Z).TotalSpace).1) ∧
          (Z.localTriv (Z.indexAt ((p : (Work.Thom.realification Z).TotalSpace).1))
            ((p : (Work.Thom.realification Z).TotalSpace))).2 (Q.indexAt p).2 ≠ 0) ∧
      (∀ (i j : ι) (k l : Fin (n + 1))
        (p : ↥(Work.Thom.zeroComplement (Work.Thom.realification Z)))
        (z : EuclideanSpace ℂ (Fin n)),
        Q.coordChange (i, k) (j, l) p z =
          Work.Thom.quoFun l ((Z.localTriv j (p : (Work.Thom.realification Z).TotalSpace)).2)
            (Z.coordChange i j ((p : (Work.Thom.realification Z).TotalSpace)).1
              (Work.Thom.fillFun k z))) := by
  refine ⟨{ baseSet := fun ik => tqBaseSet Z ik.1 ik.2
            isOpen_baseSet := fun ik => isOpen_tqBaseSet Z ik.1 ik.2
            indexAt := fun p => (Z.indexAt ((p : (realification Z).TotalSpace).1),
              tqCoord Z p)
            mem_baseSet_at := fun p => ⟨Z.mem_baseSet_at _, tqCoord_spec Z p⟩
            coordChange := fun ik jl p =>
              (quoCLM jl.2 ((Z.localTriv jl.1 (p : (realification Z).TotalSpace)).2)).comp
                ((Z.coordChange ik.1 jl.1
                  ((p : (realification Z).TotalSpace)).1).comp (fillCLM ik.2))
            coordChange_self := ?_
            continuousOn_coordChange := ?_
            coordChange_comp := ?_ }, ?_, ?_, ?_⟩
  · rintro ⟨i, k⟩ x hx v
    show (quoCLM k ((Z.localTriv i (x : (realification Z).TotalSpace)).2))
        ((Z.coordChange i i ((x : (realification Z).TotalSpace)).1) (fillCLM k v)) = v
    rw [fillCLM_apply, Z.coordChange_self i _ hx.1, quoCLM_apply]
    exact quoFun_fillFun k _ v hx.2
  · rintro ⟨i, k⟩ ⟨j, l⟩
    exact continuousOn_coordChange_tq Z i j k l
  · rintro ⟨i, k⟩ ⟨j, l⟩ ⟨m, o⟩ x hx v
    show (quoCLM o ((Z.localTriv m (x : (realification Z).TotalSpace)).2))
        ((Z.coordChange j m ((x : (realification Z).TotalSpace)).1)
          (fillCLM l ((quoCLM l ((Z.localTriv j (x : (realification Z).TotalSpace)).2))
            ((Z.coordChange i j ((x : (realification Z).TotalSpace)).1) (fillCLM k v))))) =
      (quoCLM o ((Z.localTriv m (x : (realification Z).TotalSpace)).2))
        ((Z.coordChange i m ((x : (realification Z).TotalSpace)).1) (fillCLM k v))
    simp only [quoCLM_apply, fillCLM_apply]
    have hA : Z.coordChange j m ((x : (realification Z).TotalSpace)).1
        ((Z.localTriv j (x : (realification Z).TotalSpace)).2) =
        (Z.localTriv m (x : (realification Z).TotalSpace)).2 :=
      coordChange_localTriv_snd Z j m _ hx.1.2.1 hx.2.1
    rw [← quoFun_transport l o (Z.coordChange j m ((x : (realification Z).TotalSpace)).1)
      ((Z.localTriv j (x : (realification Z).TotalSpace)).2)
      ((Z.localTriv m (x : (realification Z).TotalSpace)).2)
      (Z.coordChange i j ((x : (realification Z).TotalSpace)).1 (fillFun k v))
      hx.1.2.2 hx.2.2 hA,
      Z.coordChange_comp i j m ((x : (realification Z).TotalSpace)).1
        ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2.1⟩ (fillFun k v)]
  · intro i k
    rfl
  · intro p
    exact ⟨rfl, tqCoord_spec Z p⟩
  · intro i j k l p z
    rfl

end

end Work.Thom
