import Mathlib
import Submission.Work.SSSR.Serre.E2bDefs
import Submission.Work.SSSR.Serre.E0SbdryMatching
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Serre
variable {R : Type} [CommRing R] [Nontrivial R]

set_option maxHeartbeats 800000

open scoped Topology unitInterval Simplicial
open CategoryTheory AlgebraicTopology
namespace Work.SSSR.Serre

noncomputable section

open Work.SSSR.RatHurewicz.Bridge
/-- The underlying simplex point of a point of the hat `sHat (k+2)`. -/
def hatPt {k : ℕ} (q : ↥(sHat (k+2))) : ↥(stdSimplex ℝ (Fin (k+3))) := q.1.1

/-- The second coordinate of a point of the hat. -/
def hatTm {k : ℕ} (q : ↥(sHat (k+2))) : unitInterval := q.1.2

theorem continuous_hatPt {k : ℕ} : Continuous (hatPt (k := k)) :=
  continuous_fst.comp continuous_subtype_val

theorem continuous_hatTm {k : ℕ} : Continuous (hatTm (k := k)) :=
  continuous_snd.comp continuous_subtype_val

/-- A fixed point of the standard `(k+1)`-simplex, used as a junk value. -/
def ptSimplex (k : ℕ) : ↥(stdSimplex ℝ (Fin (k+1))) :=
  ⟨fun _ => 1 / (k + 1), ⟨fun _ => by positivity, by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp⟩⟩

/-- **Agreement of the face homotopies on the overlaps of the hat.** -/
theorem shat_agree {X : Type} [TopologicalSpace X] {k : ℕ}
    (G : (i : Fin (k+3)) → C(↥(stdSimplex ℝ (Fin (k+2))) × unitInterval, X))
    (hcomp : ∀ (i j : Fin (k+3)) (hij : i < j),
      (G j).comp ((coface k ⟨i.val, by have h : i.val < j.val := hij; omega⟩).prodMap
          (ContinuousMap.id unitInterval))
        = (G i).comp ((coface k ⟨j.val - 1, by omega⟩).prodMap
            (ContinuousMap.id unitInterval)))
    (i j : Fin (k+3)) (hij : i < j) (z : ↥(stdSimplex ℝ (Fin (k+3))))
    (hi : z.1 i = 0) (hj : z.1 j = 0) (t : unitInterval) :
    G i (⟨uncoface (k+1) i z, uncoface_mem (k+1) i z hi⟩, t)
      = G j (⟨uncoface (k+1) j z, uncoface_mem (k+1) j z hj⟩, t) := by
  have hslice : ∀ (a b : Fin (k+3)) (hab : a < b),
      ((⟨fun x => G b (x, t), by fun_prop⟩ :
          C(↥(stdSimplex ℝ (Fin (k+2))), X))).comp
          (coface k ⟨a.val, by have h : a.val < b.val := hab; omega⟩)
        = ((⟨fun x => G a (x, t), by fun_prop⟩ :
          C(↥(stdSimplex ℝ (Fin (k+2))), X))).comp
          (coface k ⟨b.val - 1, by omega⟩) := by
    intro a b hab
    ext x
    change G b ((coface k ⟨a.val, by have h : a.val < b.val := hab; omega⟩) x, t)
      = G a ((coface k ⟨b.val - 1, by omega⟩) x, t)
    have h := congrFun (congrArg DFunLike.coe (hcomp a b hab)) (x, t)
    simpa only [ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
      ContinuousMap.id_apply, Prod.map_apply] using h
  have := uncoface_agree (m := k) (fun i => (⟨fun x => G i (x, t), by fun_prop⟩ :
    C(↥(stdSimplex ℝ (Fin (k+2))), X))) hslice i j hij z hi hj
  simpa only [ContinuousMap.coe_mk] using this

/-- **Gluing the face homotopies into the hat data.** -/
theorem exists_sHatData {X : Type} [TopologicalSpace X] {k : ℕ}
    (G : (i : Fin (k+3)) → C(↥(stdSimplex ℝ (Fin (k+2))) × unitInterval, X))
    (s : C(↥(stdSimplex ℝ (Fin (k+3))), X))
    (hcomp : ∀ (i j : Fin (k+3)) (hij : i < j),
      (G j).comp ((coface k ⟨i.val, by have h : i.val < j.val := hij; omega⟩).prodMap
          (ContinuousMap.id unitInterval))
        = (G i).comp ((coface k ⟨j.val - 1, by omega⟩).prodMap
            (ContinuousMap.id unitInterval)))
    (h0 : ∀ (i : Fin (k+3)) (x : ↥(stdSimplex ℝ (Fin (k+2)))),
      G i (x, 0) = s ((coface (k+1) i) x)) :
    ∃ f : C(↥(sHat (k+2)), X),
      (∀ (q : ↥(sHat (k+2))), hatTm q = 0 → f q = s (hatPt q)) ∧
      (∀ (i : Fin (k+3)) (q : ↥(sHat (k+2)))
        (h : (hatPt q).1 i = 0),
        f q = G i (⟨uncoface (k+1) i (hatPt q),
          uncoface_mem (k+1) i (hatPt q) h⟩, hatTm q)) := by
  classical
  -- the lateral pieces
  let sideFun : (i : Fin (k+3)) → (↥(sHat (k+2)) → X) := fun i q =>
    G i (if h : (hatPt q).1 i = 0
      then ⟨uncoface (k+1) i (hatPt q), uncoface_mem (k+1) i (hatPt q) h⟩
      else ptSimplex (k+1), hatTm q)
  let bpiece : ↥(sHat (k+2)) → X := fun q => s (hatPt q)
  have hex : ∀ q : ↥(sHat (k+2)), hatTm q ≠ 0 → ∃ i : Fin (k+3), (hatPt q).1 i = 0 := by
    intro q hq
    rcases q.2 with h0 | hb
    · exact absurd h0 hq
    · exact hb
  let E0 : Set ↥(sHat (k+2)) := {q | hatTm q = 0}
  let E : (i : Fin (k+3)) → Set ↥(sHat (k+2)) := fun i => {q | (hatPt q).1 i = 0}
  let ffun : ↥(sHat (k+2)) → X := fun q =>
    if hq : hatTm q = 0 then bpiece q else sideFun (Classical.choose (hex q hq)) q
  classical
  -- the lateral pieces
  let sideFun : (i : Fin (k+3)) → (↥(sHat (k+2)) → X) := fun i q =>
    G i (if h : (hatPt q).1 i = 0
      then ⟨uncoface (k+1) i (hatPt q), uncoface_mem (k+1) i (hatPt q) h⟩
      else ptSimplex (k+1), hatTm q)
  let bpiece : ↥(sHat (k+2)) → X := fun q => s (hatPt q)
  have hex : ∀ q : ↥(sHat (k+2)), hatTm q ≠ 0 → ∃ i : Fin (k+3), (hatPt q).1 i = 0 := by
    intro q hq
    rcases q.2 with h0 | hb
    · exact absurd h0 hq
    · exact hb
  let E0 : Set ↥(sHat (k+2)) := {q | hatTm q = 0}
  let E : (i : Fin (k+3)) → Set ↥(sHat (k+2)) := fun i => {q | (hatPt q).1 i = 0}
  let ffun : ↥(sHat (k+2)) → X := fun q =>
    if hq : hatTm q = 0 then bpiece q else sideFun (Classical.choose (hex q hq)) q
  -- the value of the lateral piece `i` at a point with vanishing `i`-th coordinate
  have sideFun_eq : ∀ (i : Fin (k+3)) (q : ↥(sHat (k+2))) (h : (hatPt q).1 i = 0),
      sideFun i q = G i (⟨uncoface (k+1) i (hatPt q),
        uncoface_mem (k+1) i (hatPt q) h⟩, hatTm q) := by
    intro i q h
    simp only [sideFun, dif_pos h]
  -- the lateral pieces agree wherever two coordinates vanish
  have hsideVal : ∀ (a b : Fin (k+3)) (q : ↥(sHat (k+2)))
      (ha : (hatPt q).1 a = 0) (hb : (hatPt q).1 b = 0),
      G a (⟨uncoface (k+1) a (hatPt q), uncoface_mem (k+1) a (hatPt q) ha⟩, hatTm q)
        = G b (⟨uncoface (k+1) b (hatPt q), uncoface_mem (k+1) b (hatPt q) hb⟩, hatTm q) := by
    intro a b q ha hb
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact shat_agree G hcomp a b hlt (hatPt q) ha hb (hatTm q)
    · subst heq
      exact congrArg (fun w : ↥(stdSimplex ℝ (Fin (k+2))) => G a (w, hatTm q))
        (Subtype.ext rfl)
    · exact (shat_agree G hcomp b a hgt (hatPt q) hb ha (hatTm q)).symm
  -- the lateral pieces are continuous on the corresponding lateral faces
  have hsidecont : ∀ i : Fin (k+3), ContinuousOn (sideFun i) (E i) := by
    intro i
    rw [continuousOn_iff_continuous_domRestrict]
    have hpiece : ∀ q : ↥(E i),
        sideFun i q.1 = G i (⟨uncoface (k+1) i (hatPt q.1),
          uncoface_mem (k+1) i (hatPt q.1) q.2⟩, hatTm q.1) := by
      intro q
      simp only [sideFun, dif_pos (show (hatPt q.1).1 i = 0 from q.2)]
    refine Continuous.congr ?_ (fun q => (hpiece q).symm)
    refine (G i).continuous.comp (Continuous.prodMk ?_ ?_)
    · refine Continuous.subtype_mk (f := fun q : ↥(E i) => uncoface (k+1) i (hatPt q.1)) ?_ _
      refine continuous_pi (fun j => ?_)
      exact (continuous_apply (Fin.succAbove i j)).comp (continuous_subtype_val.comp
        ((continuous_hatPt (k := k)).comp continuous_subtype_val))
    · exact (continuous_hatTm (k := k)).comp continuous_subtype_val
  -- the glued function agrees with the lateral pieces
  have hffun_side : ∀ (i : Fin (k+3)) (q : ↥(sHat (k+2))),
      (hatPt q).1 i = 0 → ffun q = sideFun i q := by
    intro i q hi
    by_cases hq : hatTm q = 0
    · have hb : ffun q = bpiece q := by simp only [ffun, dif_pos hq]
      have hs : sideFun i q = bpiece q := by
        rw [sideFun_eq i q hi, hq,
          h0 i ⟨uncoface (k+1) i (hatPt q), uncoface_mem (k+1) i (hatPt q) hi⟩,
          coface_uncoface (k+1) i (hatPt q) hi]
      rw [hb, hs]
    · have h1 : ffun q = sideFun (Classical.choose (hex q hq)) q := by
        simp only [ffun, dif_neg hq]
      rw [h1, sideFun_eq (Classical.choose (hex q hq)) q
          (Classical.choose_spec (hex q hq)), sideFun_eq i q hi]
      exact hsideVal _ _ q (Classical.choose_spec (hex q hq)) hi
  -- the values on the bottom face
  have hval_bottom : ∀ (q : ↥(sHat (k+2))), hatTm q = 0 → ffun q = s (hatPt q) :=
    fun q hq => by simp only [ffun, dif_pos hq, bpiece]
  -- continuity of the glued map
  have hcont : Continuous ffun := by
    rw [continuous_iff_isClosed]
    intro T hT
    have hsub : ffun ⁻¹' T = (E0 ∩ bpiece ⁻¹' T) ∪
        (⋃ i : Fin (k+3), (E i ∩ sideFun i ⁻¹' T)) := by
      ext q
      constructor
      · intro hq
        rw [Set.mem_preimage] at hq
        by_cases h0q : hatTm q = 0
        · refine Or.inl ⟨h0q, ?_⟩
          show bpiece q ∈ T
          rwa [show bpiece q = ffun q from (hval_bottom q h0q).symm]
        · refine Or.inr (Set.mem_iUnion.mpr ⟨Classical.choose (hex q h0q), ?_⟩)
          refine ⟨Classical.choose_spec (hex q h0q), ?_⟩
          show sideFun (Classical.choose (hex q h0q)) q ∈ T
          rwa [show sideFun (Classical.choose (hex q h0q)) q = ffun q
            from (hffun_side _ q (Classical.choose_spec (hex q h0q))).symm]
      · intro hq
        rw [Set.mem_preimage]
        rcases hq with ⟨h0q, hq⟩ | hq
        · rw [Set.mem_preimage] at hq
          rwa [show ffun q = bpiece q from hval_bottom q h0q]
        · rw [Set.mem_iUnion] at hq
          obtain ⟨i, hi, hq⟩ := hq
          rw [Set.mem_preimage] at hq
          rwa [show ffun q = sideFun i q from hffun_side i q hi]
    rw [hsub]
    refine IsClosed.union ?_ ?_
    · exact (isClosed_eq (continuous_hatTm (k := k)) continuous_const).inter
        (hT.preimage (s.continuous.comp (continuous_hatPt (k := k))))
    · refine isClosed_iUnion_of_finite (fun i => ?_)
      have hEclosed : IsClosed (E i) := isClosed_eq ((continuous_apply i).comp
        (continuous_subtype_val.comp (continuous_hatPt (k := k)))) continuous_const
      obtain ⟨U, hU, hUeq⟩ := (continuousOn_iff_isClosed.mp (hsidecont i)) T hT
      have hset : E i ∩ sideFun i ⁻¹' T = U ∩ E i := by
        rw [Set.inter_comm (E i) (sideFun i ⁻¹' T), hUeq]
      rw [hset]
      exact hU.inter hEclosed
  refine ⟨⟨ffun, hcont⟩, ?_, ?_⟩
  · intro q hq
    change ffun q = s (hatPt q)
    exact hval_bottom q hq
  · intro i q hi
    change ffun q = G i (⟨uncoface (k+1) i (hatPt q),
      uncoface_mem (k+1) i (hatPt q) hi⟩, hatTm q)
    rw [hffun_side i q hi, sideFun_eq i q hi]

end

end Work.SSSR.Serre
