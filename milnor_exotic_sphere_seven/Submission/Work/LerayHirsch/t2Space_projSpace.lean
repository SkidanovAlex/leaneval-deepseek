import Mathlib
import Submission.Work.LerayHirsch.Punctum
import Submission.Work.LerayHirsch.TautLine
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_bundleComap_subtype
import Submission.Work.LerayHirsch.exists_smulPunct_of_chartCoord_eq_smul

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The projectivisation of a complex gluing-data bundle over a Hausdorff base is Hausdorff

Let `Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι` be a complex bundle in the gluing-data
model and `P(E) = Work.LerayHirsch.ProjSpace Z = (E∖0)/ℂˣ` its projectivisation
(`Submission/Work/LerayHirsch/Punctum.lean`).  This module proves that `P(E)` is Hausdorff as soon
as the base `B` is.

## The route

The quotient map `q = Work.LerayHirsch.mkProj Z` is continuous, **open**
(`Work.LerayHirsch.isOpenMap_mkProj`, because the `ℂˣ`-action on the punctured total space is by
homeomorphisms) and surjective.  For an open quotient map, the quotient is Hausdorff exactly when
the kernel relation `{(p,q) | q p = q q} = {(p,q) | projRel Z p q}` is closed in `X × X`
(`t2Space_of_isClosed_ker`: `q × q` is again an open quotient map, so the diagonal of `P(E)` is
closed iff its preimage — the kernel relation — is).

The kernel relation is proved closed locally, over the open cover of `X × X` by the complements of
`{(p,q) | π p = π q}` together with the pieces `punctPiece Z i ×ˢ punctPiece Z i`.  On such a piece
both points are read in the *same* chart `i`, where `projRel` becomes the proportionality of the two
chart coordinates (`projRel_iff_propPairs`), and proportionality is a closed condition on
`ℂ^m × ℂ^m` (`isClosed_propPairs`).  Closedness is local for an open cover
(`isClosed_of_isOpen_cover_subtype`).

The letter `P` of `P(E)` being Hausdorff is one of the two topological instances that make the
splitting principle `Work.LerayHirsch.splitsOverProj_of_paracompact` applicable.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- The **punctured total space** of (the realification of) a complex gluing-data bundle: the
complement of the zero section, whose quotient by the `ℂˣ`-action is `ProjSpace Z`. -/
abbrev Punct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) : Type _ :=
  ↥(zeroComplement (realification Z))

/-! ## General topology -/

/-- **A quotient by a closed kernel relation is Hausdorff.**  If `q : X → Y` is continuous, open and
surjective and the kernel relation `{(x,y) | q x = q y}` is closed, then `Y` is Hausdorff.

Indeed `Prod.map q q : X × X → Y × Y` is again continuous, open and surjective, hence a quotient
map (this is where openness is used: a product of quotient maps need not be a quotient map), the
kernel relation is the preimage of the diagonal of `Y`, and `Y` is Hausdorff iff its diagonal is
closed. -/
theorem t2Space_of_isClosed_ker {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {q : X → Y} (hc : Continuous q) (hopen : IsOpenMap q) (hsurj : Function.Surjective q)
    (hker : IsClosed {z : X × X | q z.1 = q z.2}) : T2Space Y := by
  rw [t2_iff_isClosed_diagonal]
  have hq : Topology.IsQuotientMap (Prod.map q q) :=
    (hopen.prodMap hopen).isQuotientMap (hc.prodMap hc) (hsurj.prodMap hsurj)
  rw [← hq.isCoinducing.isClosed_preimage]
  convert hker using 2
  ext z
  simp [Prod.map]

/-- **Closedness is local for an open cover.**  If `U i` is an open cover of `X` and the trace of
`s` on each piece `U i` is closed *in that piece*, then `s` is closed in `X`: the complement of `s`
is the union of the pieces of `U i ∖ (s ∩ U i)`, each open because `U i` is open. -/
theorem isClosed_of_isOpen_cover_subtype {X : Type*} [TopologicalSpace X] {κ : Type}
    {U : κ → Set X} (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ) {s : Set X}
    (h : ∀ i, IsClosed ((Subtype.val : ↥(U i) → X) ⁻¹' s)) : IsClosed s := by
  have key : ∀ i, ∃ W : Set X, IsOpen W ∧ Subtype.val ⁻¹' W = {x : ↥(U i) | (x : X) ∈ s}ᶜ := by
    intro i
    have h1 : IsOpen ({x : ↥(U i) | (x : X) ∈ s}ᶜ) := (h i).isOpen_compl
    exact (isOpen_induced_iff (f := (Subtype.val : ↥(U i) → X))).mp h1
  choose W hWopen hWeq using key
  have hcompl : sᶜ = ⋃ i, (U i ∩ W i) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := Set.iUnion_eq_univ_iff.mp hcov x
      refine Set.mem_iUnion.mpr ⟨i, hi, ?_⟩
      have h2 : (⟨x, hi⟩ : ↥(U i)) ∈ Subtype.val ⁻¹' W i := by
        rw [hWeq i]
        exact hx
      exact h2
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hiU, hiW⟩ := hx
      have h2 : (⟨x, hiU⟩ : ↥(U i)) ∈ Subtype.val ⁻¹' W i := hiW
      rw [hWeq i] at h2
      exact h2
  rw [← isOpen_compl_iff, hcompl]
  exact isOpen_iUnion fun i => (hU i).inter (hWopen i)

/-! ## Proportional pairs in the model fibre -/

/-- The pairs of vectors of the model fibre which are **linearly dependent**: the closed condition
`⟪w,w⟫ v = ⟪w,v⟫ w` (for `w ≠ 0` it says `v ∈ ℂ·w`). -/
def propPairs (m : ℕ) : Set (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :=
  {z | (inner ℂ z.2 z.2) • z.1 = (inner ℂ z.2 z.1) • z.2}

theorem isClosed_propPairs (m : ℕ) : IsClosed (propPairs m) := by
  have hcont : Continuous (fun z : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m) =>
      (inner ℂ z.2 z.2) • z.1 - (inner ℂ z.2 z.1) • z.2) := by fun_prop
  have hset : {z : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m) |
      (inner ℂ z.2 z.2) • z.1 - (inner ℂ z.2 z.1) • z.2 = 0} = propPairs m := by
    ext z
    simp only [Set.mem_ofPred_eq, propPairs, sub_eq_zero]
  rw [← hset]
  exact isClosed_singleton.preimage hcont

/-- On the pairs with second component nonzero, `propPairs` is exactly proportionality. -/
theorem mem_propPairs_iff {m : ℕ} {v w : EuclideanSpace ℂ (Fin m)} (hw : w ≠ 0) :
    (v, w) ∈ propPairs m ↔ ∃ c : ℂ, v = c • w := by
  have hI : inner ℂ w w ≠ 0 := inner_self_ne_zero.mpr hw
  constructor
  · intro h
    refine ⟨(inner ℂ w w)⁻¹ * inner ℂ w v, ?_⟩
    have h' : (inner ℂ w w) • v = (inner ℂ w v) • w := h
    calc v = ((inner ℂ w w)⁻¹ * inner ℂ w w) • v := by rw [inv_mul_cancel₀ hI, one_smul]
      _ = (inner ℂ w w)⁻¹ • ((inner ℂ w w) • v) := (smul_smul _ _ _).symm
      _ = (inner ℂ w w)⁻¹ • ((inner ℂ w v) • w) := by rw [h']
      _ = ((inner ℂ w w)⁻¹ * inner ℂ w v) • w := smul_smul _ _ _
  · rintro ⟨c, rfl⟩
    change (inner ℂ w w) • (c • w) = (inner ℂ w (c • w)) • w
    rw [inner_smul_right, smul_smul, mul_comm]

/-! ## The chart coordinate determines the point on a chart -/

/-- The `i`-th chart coordinate of a point over `Z.baseSet i` is recovered by the inverse transition
function from the point's fibre component. -/
theorem coordChange_chartCoord (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι)
    (r : Punct Z) (hr : r.1.proj ∈ Z.baseSet i) :
    (Z.coordChange i (Z.indexAt r.1.proj) r.1.proj) (chartCoord Z i r)
      = (show EuclideanSpace ℂ (Fin m) from r.1.2) := by
  rw [chartCoord_def]
  rw [Z.coordChange_comp (Z.indexAt r.1.proj) i (Z.indexAt r.1.proj) r.1.proj
    ⟨⟨Z.mem_baseSet_at r.1.proj, hr⟩, Z.mem_baseSet_at r.1.proj⟩]
  exact Z.coordChange_self (Z.indexAt r.1.proj) r.1.proj (Z.mem_baseSet_at r.1.proj) _

/-- **The chart coordinate determines the point on a chart**: two points of the punctured total
space lying over the same base point of `Z.baseSet i` with equal `i`-th chart coordinate are
equal. -/
theorem eq_of_chartCoord_eq (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) {i : ι}
    {p q : Punct Z} (hp : p.1.proj ∈ Z.baseSet i) (hq : q.1.proj ∈ Z.baseSet i)
    (hb : p.1.proj = q.1.proj) (h : chartCoord Z i p = chartCoord Z i q) : p = q := by
  have hp' := coordChange_chartCoord Z i p hp
  have hq' := coordChange_chartCoord Z i q hq
  have h2 : (show EuclideanSpace ℂ (Fin m) from p.1.2)
      = (show EuclideanSpace ℂ (Fin m) from q.1.2) := by
    rw [← hp', ← hq', hb, h]
  exact Subtype.ext (Bundle.TotalSpace.ext hb (heq_of_eq h2))

/-! ## The kernel relation in chart coordinates -/

/-- **`projRel` in a chart**: two points of the punctured total space over `Z.baseSet i` are in the
`ℂˣ`-orbit relation exactly when their `i`-th chart coordinates are proportional and their base
points agree. -/
theorem projRel_iff_propPairs (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι)
    {p q : Punct Z} (hp : p.1.proj ∈ Z.baseSet i) (hq : q.1.proj ∈ Z.baseSet i) :
    projRel Z p q ↔ ((chartCoord Z i p, chartCoord Z i q) ∈ propPairs m
      ∧ p.1.proj = q.1.proj) := by
  constructor
  · rintro ⟨d, hd⟩
    have hcoord : chartCoord Z i p = (d : ℂ) • chartCoord Z i q := by
      rw [← hd, chartCoord_smulPunct]
    refine ⟨?_, ?_⟩
    · show (inner ℂ (chartCoord Z i q) (chartCoord Z i q)) • chartCoord Z i p
        = (inner ℂ (chartCoord Z i q) (chartCoord Z i p)) • chartCoord Z i q
      rw [hcoord, inner_smul_right, smul_smul,
        mul_comm (inner ℂ (chartCoord Z i q) (chartCoord Z i q)) (d : ℂ)]
    · rw [← hd, smulPunct_proj]
  · rintro ⟨hmem, hb⟩
    have hqnz : chartCoord Z i q ≠ 0 := chartCoord_ne_zero_of_mem_baseSet Z i q hq
    obtain ⟨c, hc⟩ := (mem_propPairs_iff hqnz).mp hmem
    obtain ⟨d, hd⟩ := exists_smulPunct_of_chartCoord_eq_smul Z i hp hq hb hc
    exact ⟨d, hd.symm⟩

/-! ## The kernel relation is closed -/

/-- The chart piece of the punctured total space over `Z.baseSet i`. -/
def punctPiece (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι) : Set (Punct Z) :=
  {p | p.1.proj ∈ Z.baseSet i}

/-- The open cover of `X × X` on which the kernel relation is analysed: the complement of the
"same base" set together with the pieces on which a single chart is available in both variables. -/
def projCover (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Option ι → Set (Punct Z × Punct Z)
  | none => {z | ¬ (z.1.1.proj = z.2.1.proj)}
  | some i => punctPiece Z i ×ˢ punctPiece Z i

theorem isOpen_punctPiece (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι) :
    IsOpen (punctPiece Z i) :=
  (Z.isOpen_baseSet i).preimage
    (((bundleProj (realification Z)).comp (subtypeMap (zeroComplement (realification Z)))).continuous)

/-- **The kernel relation of `E∖0 → P(E)` is closed** over a Hausdorff base. -/
theorem isClosed_projRel (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [T2Space B] :
    IsClosed {z : Punct Z × Punct Z | projRel Z z.1 z.2} := by
  have hproj : Continuous (fun p : Punct Z => p.1.proj) :=
    ((bundleProj (realification Z)).comp (subtypeMap (zeroComplement (realification Z)))).continuous
  refine isClosed_of_isOpen_cover_subtype (U := projCover Z) ?_ ?_ ?_
  · -- openness of the cover
    rintro (_ | i)
    · exact (isClosed_eq (hproj.comp continuous_fst) (hproj.comp continuous_snd)).isOpen_compl
    · exact (isOpen_punctPiece Z i).prod (isOpen_punctPiece Z i)
  · -- the cover covers
    rw [Set.iUnion_eq_univ_iff]
    rintro ⟨p, q⟩
    by_cases h : p.1.proj = q.1.proj
    · refine ⟨some (Z.indexAt p.1.proj), ?_⟩
      have hp : p.1.proj ∈ Z.baseSet (Z.indexAt p.1.proj) := Z.mem_baseSet_at p.1.proj
      have hq : q.1.proj ∈ Z.baseSet (Z.indexAt p.1.proj) := by rw [← h]; exact hp
      exact ⟨hp, hq⟩
    · exact ⟨none, h⟩
  · -- closedness on each piece
    rintro (_ | i)
    · -- the "different base" piece: the relation is empty there
      have hempty : (Subtype.val ⁻¹'
          {z : Punct Z × Punct Z | projRel Z z.1 z.2} : Set ↥(projCover Z none)) = ∅ := by
        ext z
        constructor
        · intro hrel
          obtain ⟨c, hc⟩ := hrel
          exact z.2 (by rw [← hc, smulPunct_proj])
        · intro h
          exact absurd h (by simp)
      rw [hempty]
      exact isClosed_empty
    · -- a chart piece
      -- the chart coordinates give a continuous map to the model space of pairs
      have hcont1 : Continuous (fun z : ↥(punctPiece Z i ×ˢ punctPiece Z i) =>
          chartCoord Z i z.1.1) :=
        (continuousOn_chartCoord Z i).comp_continuous
          (continuous_fst.comp continuous_subtype_val)
          (fun z => (Set.mem_prod.mp z.2).1)
      have hcont2 : Continuous (fun z : ↥(punctPiece Z i ×ˢ punctPiece Z i) =>
          chartCoord Z i z.1.2) :=
        (continuousOn_chartCoord Z i).comp_continuous
          (continuous_snd.comp continuous_subtype_val)
          (fun z => (Set.mem_prod.mp z.2).2)
      have hcont3 : Continuous (fun z : ↥(punctPiece Z i ×ˢ punctPiece Z i) => z.1.1.1.proj) :=
        hproj.comp (continuous_fst.comp continuous_subtype_val)
      have hcont4 : Continuous (fun z : ↥(punctPiece Z i ×ˢ punctPiece Z i) => z.1.2.1.proj) :=
        hproj.comp (continuous_snd.comp continuous_subtype_val)
      have hθ : Continuous (fun z : ↥(punctPiece Z i ×ˢ punctPiece Z i) =>
          ((chartCoord Z i z.1.1, chartCoord Z i z.1.2), (z.1.1.1.proj, z.1.2.1.proj))) :=
        (hcont1.prodMk hcont2).prodMk (hcont3.prodMk hcont4)
      have hK : IsClosed {w : (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) × (B × B) |
          w.1 ∈ propPairs m ∧ w.2.1 = w.2.2} :=
        (isClosed_propPairs m).preimage continuous_fst |>.inter
          (isClosed_eq (continuous_fst.comp continuous_snd)
            (continuous_snd.comp continuous_snd))
      have hset : (Subtype.val ⁻¹' {z : Punct Z × Punct Z | projRel Z z.1 z.2} :
          Set ↥(punctPiece Z i ×ˢ punctPiece Z i))
          = {z : ↥(punctPiece Z i ×ˢ punctPiece Z i) |
              ((chartCoord Z i z.1.1, chartCoord Z i z.1.2), (z.1.1.1.proj, z.1.2.1.proj)) ∈
                {w : (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) × (B × B) |
                  w.1 ∈ propPairs m ∧ w.2.1 = w.2.2}} := by
        ext z
        exact projRel_iff_propPairs Z i (Set.mem_prod.mp z.2).1 (Set.mem_prod.mp z.2).2
      have hgoal : IsClosed ((Subtype.val ⁻¹' {z : Punct Z × Punct Z | projRel Z z.1 z.2}) :
          Set ↥(punctPiece Z i ×ˢ punctPiece Z i)) := by
        rw [hset]
        exact hK.preimage hθ
      exact hgoal

/-! ## The main theorem -/

/-- **The projectivisation of a complex gluing-data bundle over a Hausdorff base is Hausdorff.**
`Work.LerayHirsch.ProjSpace Z` is the quotient `(E∖0)/ℂˣ` of the punctured total space by the
fibrewise action of the units of `ℂ`; over a Hausdorff base the quotient map is open and its kernel
relation is closed, so the quotient is Hausdorff.

This is one of the two topological instances that make the splitting principle
`Work.LerayHirsch.splitsOverProj_of_paracompact` applicable: it supplies
`[T2Space (ProjSpace Z)]`. -/
theorem t2Space_projSpace {m : ℕ} {B : Type} [TopologicalSpace B] [T2Space B] {ι : Type}
    [Fintype ι] (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    T2Space (Work.LerayHirsch.ProjSpace Z) := by
  refine t2Space_of_isClosed_ker (continuous_mkProj Z) (isOpenMap_mkProj Z) (surjective_mkProj Z) ?_
  have hset : {z : Punct Z × Punct Z | mkProj Z z.1 = mkProj Z z.2}
      = {z : Punct Z × Punct Z | projRel Z z.1 z.2} := by
    ext z
    exact mkProj_eq_iff Z
  rw [hset]
  exact isClosed_projRel Z

end

end Work.LerayHirsch
