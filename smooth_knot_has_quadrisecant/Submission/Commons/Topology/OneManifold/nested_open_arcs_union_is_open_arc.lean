import Mathlib
import Submission.Commons.Topology.Homeomorph.open_interval_affine
import Submission.Commons.Topology.Homeomorph.subtype_preimage_homeo
import Submission.Commons.Topology.ConnectedReal.preconnected_inter_of_homeoUnit
import Submission.Commons.Topology.OneManifold.union_two_open_arcs_connected_overlap_interval
import Submission.Commons.Topology.OneManifold.chart_pullback_interval_shape
import Submission.Commons.Topology.Homeomorph.intervalHomeo_extend

universe u

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.Topology.OneManifold

/-!
# nested_open_arcs_union_is_open_arc

If `V n` are nested open subsets of a Hausdorff space `X`, each
homeomorphic to the open unit interval `(0,1)`, then their union is
homeomorphic to `(0,1)`.

Strategy: re-chart each level so that the coordinate charts AGREE on the
common part: inductively build charts `e n : V n ≃ₜ (c n, d n)` onto open
real intervals with `e (n+1)` extending `e n` (and `(c n,d n) ⊆
(c (n+1),d (n+1))`).  The per-step extension is the two-sided interval
extension: an open sub-arc of an open arc sits at coordinates `(a,b)`
(`chart_pullback_interval_shape`), and an interval homeomorphism
`(a,b) ≃ (c,d)` extends over `(0,1)` (`intervalHomeo_extend`).  The
compatible charts paste to a homeomorphism of `⋃ V n` onto the open
preconnected set `⋃ n, (c n, d n) ⊆ ℝ`, which is `≃ₜ (0,1)`.
-/

/-- The open unit interval `(0,1)` as a type. -/
abbrev ORI₁ : Type := {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}

/-- The open interval `(c,d)` as a type. -/
abbrev IV (c d : ℝ) : Type := {t : ℝ // t ∈ Set.Ioo c d}

/-- The open unit interval is connected (it is homeomorphic to `ℝ`). -/
theorem ori_connected : ConnectedSpace ORI₁ := by
  rcases Commons.Topology.OneManifold.ArcGlue.homeo_real_openUnit with ⟨eR⟩
  exact (eR.symm.connectedSpace_iff).mpr inferInstance

/-- Every nonempty open preconnected subset of ℝ is homeomorphic to `(0,1)`
(the union-assembly end step). -/
theorem open_preconn_homeo_unit {S : Set ℝ} (hS : IsOpen S) (hpc : IsPreconnected S)
    (hne : S.Nonempty) : Nonempty ({t : ℝ // t ∈ S} ≃ₜ ORI₁) := by
  exact Commons.Topology.OneManifold.ArcGlue.open_connected_ℝ_homeo_openUnit hS hpc hne

/-- Membership of `(a,b)` in `(0,1)` under `0 ≤ a < b ≤ 1`. -/
lemma mem_unit_of_mem_ab {a b : ℝ} (h0a : 0 ≤ a) (hb1 : b ≤ 1) {t : ℝ}
    (ht : t ∈ Set.Ioo a b) : t ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨lt_of_le_of_lt h0a ht.1, lt_of_lt_of_le ht.2 hb1⟩

/-- A connected open subset `U` of an open arc `W` (chart `χ`), occupying
coordinates `(a,b)` (per `chart_pullback_interval_shape`), is
homeomorphic to the interval subtype `IV a b` via the chart restriction
`r ↦ χ r`; the evaluation law is returned explicitly. -/
theorem chart_restrict_homeo {X : Type*} [TopologicalSpace X] {U W : Set X}
    (hUopen : IsOpen U) (hUconn : ConnectedSpace {x : X // x ∈ U}) (hUW : U ⊆ W)
    (χ : ORI₁ ≃ₜ {x : X // x ∈ W})
    {a b : ℝ} (h0a : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hmem : ∀ t : ORI₁, ((χ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo a b) :
    ∃ ι : IV a b ≃ₜ {x : X // x ∈ U},
      ∀ r : IV a b, (ι r : X) = (χ ⟨r.1, mem_unit_of_mem_ab h0a hb1 r.2⟩ : X) := by
  classical
  let A : Type := {t : ORI₁ // ((χ t) : X) ∈ U}
  let vF : IV a b → ORI₁ := fun r => ⟨r.1, mem_unit_of_mem_ab h0a hb1 r.2⟩
  have hvFc : Continuous vF := by
    dsimp [vF]
    exact Continuous.subtype_mk continuous_subtype_val
      (by intro r; exact mem_unit_of_mem_ab h0a hb1 r.2)
  let F : IV a b → A := fun r => ⟨vF r, (hmem (vF r)).mpr r.2⟩
  let G : A → IV a b := fun t => ⟨(((t : ORI₁) : ℝ)), (hmem (t : ORI₁)).mp t.2⟩
  have hFc : Continuous F := by
    dsimp [F]
    exact Continuous.subtype_mk hvFc (by intro r; exact (hmem (vF r)).mpr r.2)
  have hGc : Continuous G := by
    dsimp [G]
    exact Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val)
      (by intro t; exact (hmem (t : ORI₁)).mp t.2)
  have hFG : Function.LeftInverse G F := by
    intro r
    apply Subtype.ext
    dsimp [G, F, vF]
  have hGF : Function.RightInverse G F := by
    intro t
    apply Subtype.ext
    apply Subtype.ext
    dsimp [G, F, vF]
  let eAB : IV a b ≃ A := { toFun := F, invFun := G, left_inv := hFG, right_inv := hGF }
  let hAB : IV a b ≃ₜ A := Homeomorph.mk eAB hFc hGc
  let hA : A ≃ₜ {x : X // x ∈ W ∩ U} := by
    dsimp [A]
    exact Commons.Topology.OneManifold.ArcGlue.overlapPullbackHomeo (U := W) (V := U) χ
  have hWU : W ∩ U = U := by
    ext x
    constructor
    · intro hx; exact hx.2
    · intro hx; exact ⟨hUW hx, hx⟩
  let hWU2 : {x : X // x ∈ W ∩ U} ≃ₜ {x : X // x ∈ U} :=
    Commons.Topology.OneManifold.ArcGlue.setEqSubtypeHomeoX hWU
  let hfin : IV a b ≃ₜ {x : X // x ∈ U} := hAB.trans (hA.trans hWU2)
  refine ⟨hfin, ?_⟩
  intro r
  have h1 : ((hfin r : {x : X // x ∈ U}) : X) = ((hA.trans hWU2) (hAB r) : X) := by
    rfl
  have h2 : ((hA.trans hWU2) (hAB r) : X) = ((hA (hAB r) : {x : X // x ∈ W ∩ U}) : X) := by
    change ((hWU2 (hA (hAB r)) : {x : X // x ∈ U}) : X) =
      ((hA (hAB r) : {x : X // x ∈ W ∩ U}) : X)
    exact Commons.Topology.OneManifold.ArcGlue.setEqSubtypeHomeoX_apply_val hWU (hA (hAB r))
  have h3 : ((hA (hAB r) : {x : X // x ∈ W ∩ U}) : X) = (χ (hAB r : ORI₁) : X) := by
    change ((Commons.Topology.OneManifold.ArcGlue.overlapPullbackHomeo (U := W) (V := U) χ (hAB r) :
      {x : X // x ∈ W ∩ U}) : X) = (χ (hAB r : ORI₁) : X)
    exact Commons.Topology.OneManifold.ArcGlue.overlapPullbackHomeo_apply_val (U := W) (V := U) χ (hAB r)
  have h4 : (χ (hAB r : ORI₁) : X) = (χ (vF r) : X) := by
    rw [show ((hAB r : A) : ORI₁) = vF r by dsimp [hAB, eAB, F, vF]]
  rw [h1, h2, h3, h4]

/-- Result data of one chart-extension step: a larger interval `(c',d')`
with `(c,d) ⊆ (c',d')` and a chart `e' : W ≃ₜ (c',d')` agreeing with `e`
on `U`. -/
structure ArcChartExt {X : Type*} [TopologicalSpace X] {U W : Set X} {c d : ℝ}
    (hUW : U ⊆ W) (e : {x : X // x ∈ U} ≃ₜ IV c d) where
  c' : ℝ
  d' : ℝ
  hc'c : c' ≤ c
  hdd' : d ≤ d'
  hlt : c' < d'
  e' : {x : X // x ∈ W} ≃ₜ IV c' d'
  agre : ∀ x : {x : X // x ∈ U},
    ((e' ⟨(x : X), hUW x.2⟩ : IV c' d') : ℝ) = ((e x : IV c d) : ℝ)

/-- **Space-level chart extension**: given an open arc `W ⊇ U` (both open in
`X`, `U` connected), any chart `e : U ≃ₜ (c,d)` extends to a chart
`e' : W ≃ₜ (c',d')` agreeing with `e` on `U`, with `(c,d) ⊆ (c',d')`. -/
noncomputable def open_arc_chart_extension {X : Type*} [TopologicalSpace X] {U W : Set X}
    (hUopen : IsOpen U) (hUconn : ConnectedSpace {x : X // x ∈ U}) (hUW : U ⊆ W)
    (hWchart : Nonempty (ORI₁ ≃ₜ {x : X // x ∈ W}))
    {c d : ℝ} (hcd : c < d) (e : {x : X // x ∈ U} ≃ₜ IV c d) :
    ArcChartExt (hUW := hUW) (e := e) := by
  classical
  let χ : ORI₁ ≃ₜ {x : X // x ∈ W} := Classical.choice hWchart
  let shp := chart_pullback_interval_shape (X := X) hUopen hUconn hUW χ
  let a : ℝ := Classical.choose shp
  let shp1 := Classical.choose_spec shp
  let b : ℝ := Classical.choose shp1
  let shp2 := Classical.choose_spec shp1
  let h0a : 0 ≤ a := shp2.1
  let hab : a < b := shp2.2.1
  let hb1 : b ≤ 1 := shp2.2.2.1
  let hmem : ∀ t : ORI₁, ((χ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo a b := shp2.2.2.2
  let hcr := chart_restrict_homeo (X := X) (U := U) (W := W) hUopen hUconn hUW χ h0a hab hb1 hmem
  let ι : IV a b ≃ₜ {x : X // x ∈ U} := Classical.choose hcr
  let hιeval := Classical.choose_spec hcr
  let F : IV a b ≃ₜ IV c d := ι.trans e
  let hext := Commons.Topology.Homeomorph.intervalHomeo_extend h0a hab hb1 hcd F
  let c' : ℝ := Classical.choose hext
  let hext1 := Classical.choose_spec hext
  let d' : ℝ := Classical.choose hext1
  let hext2 := Classical.choose_spec hext1
  let hc'c : c' ≤ c := hext2.1
  let hdd' : d ≤ d' := hext2.2.1
  let hc'd' : c' < d' := hext2.2.2.1
  let hhex := hext2.2.2.2
  let G : ORI₁ ≃ₜ IV c' d' := Classical.choose hhex
  let hG := Classical.choose_spec hhex
  let eNew : {x : X // x ∈ W} ≃ₜ IV c' d' := (χ.symm).trans G
  refine { c' := c', d' := d', hc'c := hc'c, hdd' := hdd', hlt := hc'd', e' := eNew, agre := ?_ }
  intro x
  let z : {x : X // x ∈ W} := ⟨(x : X), hUW x.2⟩
  let ω : ORI₁ := χ.symm z
  have hωab : (ω : ℝ) ∈ Set.Ioo a b := by
    dsimp [ω, z]
    have hχ : ((χ (χ.symm ⟨(x : X), hUW x.2⟩) : {x : X // x ∈ W}) : X) ∈ U := by
      have hz' : (χ (χ.symm ⟨(x : X), hUW x.2⟩) : {x : X // x ∈ W}) = ⟨(x : X), hUW x.2⟩ :=
        χ.apply_symm_apply ⟨(x : X), hUW x.2⟩
      rw [hz']
      exact x.2
    exact (hmem (χ.symm ⟨(x : X), hUW x.2⟩)).mp hχ
  have hιx : ι ⟨(ω : ℝ), hωab⟩ = x := by
    apply Subtype.ext
    rw [hιeval]
    dsimp [ω, z] at hωab ⊢
    change ((χ ⟨(ω : ℝ), mem_unit_of_mem_ab h0a hb1 hωab⟩ : {x : X // x ∈ W}) : X) = x.1
    have hχ : χ ⟨(ω : ℝ), mem_unit_of_mem_ab h0a hb1 hωab⟩ = χ (χ.symm ⟨(x : X), hUW x.2⟩) := by
      apply congrArg χ
      apply Subtype.ext
      dsimp [ω]
    rw [hχ]
    exact congrArg (fun q : {x : X // x ∈ W} => (q : X)) (χ.apply_symm_apply ⟨(x : X), hUW x.2⟩)
  have h1 : ((eNew ⟨(x : X), hUW x.2⟩ : IV c' d') : ℝ) = ((G ω : IV c' d') : ℝ) := by
    dsimp [eNew, z, ω]
  have h2 : ((G ω : IV c' d') : ℝ) = ((e x : IV c d) : ℝ) := by
    have p01 : (ω : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_lt h0a hωab.1, lt_of_lt_of_le hωab.2 hb1⟩
    have hGeq : G ω = G ⟨(ω : ℝ), p01⟩ := by
      apply congrArg G
      apply Subtype.ext
      rfl
    have hG' : ((G ⟨(ω : ℝ), p01⟩ : IV c' d') : ℝ) =
        ((F ⟨(ω : ℝ), hωab⟩ : IV c d) : ℝ) := hG (ω : ℝ) hωab
    rw [hGeq, hG']
    dsimp [F]
    rw [hιx]
  rw [h1, h2]

/-- Level data: an open interval `(c,d)` together with a chart of `V n`. -/
structure NestedArcChart {X : Type u} [TopologicalSpace X] (V : ℕ → Set X) (n : ℕ) where
  c : ℝ
  d : ℝ
  hlt : c < d
  e : {x : X // x ∈ V n} ≃ₜ IV c d

/-- **Compatible nested interval charts of a nested open-arc family.**  If
`V n ⊆ V (n+1)` are open and each carries an `ORI₁`-chart, then there are
open real intervals `(c n, d n)` and charts `e n : V n ≃ₜ (c n,d n)` such
that `e (n+1)` extends `e n` on `V n` and the intervals are nested
`(c n,d n) ⊆ (c (n+1),d (n+1))`.  The agreement is as real coordinate
values. -/
theorem nested_open_arcs_charts {X : Type u} [TopologicalSpace X]
    (V : ℕ → Set X) (hVopen : ∀ n, IsOpen (V n)) (hnest : ∀ n, V n ⊆ V (n + 1))
    (hconn : ∀ n, ConnectedSpace {x : X // x ∈ V n})
    (hchart : ∀ n, Nonempty (ORI₁ ≃ₜ {x : X // x ∈ V n})) :
    ∃ (c d : ℕ → ℝ) (e : ∀ n, {x : X // x ∈ V n} ≃ₜ IV (c n) (d n)),
      (∀ n, c n < d n) ∧
      (∀ n, c (n + 1) ≤ c n ∧ d n ≤ d (n + 1)) ∧
      (∀ m n, (hmn : m ≤ n) → ∀ x : X, (hx : x ∈ V m) →
          ((e n ⟨x, monotone_nat_of_le_succ hnest hmn hx⟩ : IV (c n) (d n)) : ℝ) =
            ((e m ⟨x, hx⟩ : IV (c m) (d m)) : ℝ)) := by
  classical
  let hVmono : Monotone V := monotone_nat_of_le_succ hnest
  let stepData : ∀ (n : ℕ) (st : NestedArcChart V n),
      { ns : NestedArcChart V (n + 1) // (ns.c ≤ st.c ∧ st.d ≤ ns.d) ∧
        ∀ x : {x : X // x ∈ V n},
          (((ns.e ⟨(x : X), hnest n x.2⟩ : IV ns.c ns.d) : ℝ) =
            ((st.e x : IV st.c st.d) : ℝ)) } := by
    intro n st
    rcases open_arc_chart_extension (U := V n) (W := V (n + 1)) (hVopen n) (hconn n)
      (hnest n) (hchart (n + 1)) st.hlt st.e with ⟨c', d', hc'c, hdd', hc'd', e', hagr⟩
    refine ⟨⟨c', d', hc'd', e'⟩, ⟨⟨hc'c, hdd'⟩, hagr⟩⟩
  let fam : ∀ n : ℕ, NestedArcChart V n :=
    Nat.rec (motive := fun n : ℕ => NestedArcChart V n)
      ⟨0, 1, (by norm_num : (0 : ℝ) < 1), (Classical.choice (hchart 0)).symm⟩
      (fun n st => (stepData n st).1)
  let cN : ℕ → ℝ := fun n => (fam n).c
  let dN : ℕ → ℝ := fun n => (fam n).d
  let eN : ∀ n : ℕ, {x : X // x ∈ V n} ≃ₜ IV (cN n) (dN n) := fun n => (fam n).e
  have hfam_succ : ∀ n, fam (n + 1) = (stepData n (fam n)).1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rfl
  have hcpos : ∀ n, cN n < dN n := by
    intro n
    dsimp [cN, dN]
    exact (fam n).hlt
  have hgrowth : ∀ n, cN (n + 1) ≤ cN n ∧ dN n ≤ dN (n + 1) := by
    intro n
    have h := (stepData n (fam n)).2.1
    dsimp [cN, dN]
    rw [hfam_succ n]
    exact h
  have hagr : ∀ n, ∀ x : {x : X // x ∈ V n},
      ((eN (n + 1) ⟨(x : X), hnest n x.2⟩ : IV (cN (n + 1)) (dN (n + 1))) : ℝ) =
        ((eN n x : IV (cN n) (dN n)) : ℝ) := by
    intro n x
    have h := (stepData n (fam n)).2.2 x
    simpa [cN, dN, eN, hfam_succ n] using h
  have hpair : ∀ m n, (hmn : m ≤ n) → ∀ x : X, (hx : x ∈ V m) →
      ((eN n ⟨x, hVmono hmn hx⟩ : IV (cN n) (dN n)) : ℝ) = ((eN m ⟨x, hx⟩ : IV (cN m) (dN m)) : ℝ) := by
    intro m n hmn x hx
    let P : (k : ℕ) → m ≤ k → Prop := fun k hk =>
      ((eN k ⟨x, hVmono hk hx⟩ : IV (cN k) (dN k)) : ℝ) = ((eN m ⟨x, hx⟩ : IV (cN m) (dN m)) : ℝ)
    have hbase : P m (le_refl m) := by
      dsimp [P]
    have hsucc : ∀ (k : ℕ) (hk : m ≤ k), P k hk → P (k + 1) (le_trans hk (Nat.le_succ k)) := by
      intro k hk ih
      dsimp [P]
      rw [← ih]
      have hstep := hagr k ⟨x, hVmono hk hx⟩
      dsimp [cN, dN, eN] at hstep ⊢
      convert hstep using 2
    exact Nat.le_induction (m := m) (P := P) hbase hsucc n hmn
  exact ⟨cN, dN, eN, hcpos, hgrowth, hpair⟩


/-- Compatible nested interval charts paste to a homeomorphism of
`⋃ n, V n` onto `⋃ n, (c n, d n)`.  (The union of the interval sets is an
open connected subset of ℝ and will be identified with `(0,1)` next.) -/
theorem nested_open_arcs_union_homeo_interval {X : Type u} [TopologicalSpace X]
    (V : ℕ → Set X) (hVopen : ∀ n, IsOpen (V n)) (hnest : ∀ n, V n ⊆ V (n + 1))
    (c d : ℕ → ℝ) (e : ∀ n, {x : X // x ∈ V n} ≃ₜ IV (c n) (d n))
    (hcd : ∀ n, c n < d n) (hgrowth : ∀ n, c (n + 1) ≤ c n ∧ d n ≤ d (n + 1))
    (hagr : ∀ m n, (hmn : m ≤ n) → ∀ x : X, (hx : x ∈ V m) →
        ((e n ⟨x, monotone_nat_of_le_succ hnest hmn hx⟩ : IV (c n) (d n)) : ℝ) =
          ((e m ⟨x, hx⟩ : IV (c m) (d m)) : ℝ)) :
    Nonempty (({x : X // x ∈ ⋃ n, V n}) ≃ₜ
      {t : ℝ // t ∈ ⋃ n, Set.Ioo (c n) (d n)}) := by
  classical
  let U : Set X := ⋃ n, V n
  let J : ℕ → Set ℝ := fun n => Set.Ioo (c n) (d n)
  let hVmono : Monotone V := monotone_nat_of_le_succ hnest
  have hJsub : ∀ n, J n ⊆ J (n + 1) := by
    intro n x hx
    rcases hgrowth n with ⟨h1, h2⟩
    exact ⟨lt_of_le_of_lt h1 hx.1, lt_of_lt_of_le hx.2 h2⟩
  let hJmono : Monotone J := monotone_nat_of_le_succ hJsub
  let Utyp := {x : X // x ∈ U}
  let Rtyp := {t : ℝ // t ∈ ⋃ j, J j}
  -- membership witnesses
  let vMem : ∀ x : Utyp, ∃ n : ℕ, x.1 ∈ V n := fun x =>
    Set.mem_iUnion.mp (by change x.1 ∈ (⋃ n, V n); dsimp [U]; exact x.2)
  let tMem : ∀ t : Rtyp, ∃ n : ℕ, t.1 ∈ J n := fun t =>
    Set.mem_iUnion.mp (by change t.1 ∈ (⋃ j, J j); exact t.2)
  -- the pasted coordinate map
  let F : Utyp → Rtyp := fun x =>
    let m : ℕ := Classical.choose (vMem x)
    let hm : x.1 ∈ V m := Classical.choose_spec (vMem x)
    let v := (e m ⟨x.1, hm⟩ : IV (c m) (d m))
    ⟨(v : ℝ), Set.mem_iUnion.mpr ⟨m, by simpa [J] using v.2⟩⟩
  have F_eq : ∀ (x : Utyp) (n : ℕ) (hx : x.1 ∈ V n),
      ((F x : Rtyp) : ℝ) = ((e n ⟨x.1, hx⟩ : IV (c n) (d n)) : ℝ) := by
    intro x n hx
    let m : ℕ := Classical.choose (vMem x)
    let hm : x.1 ∈ V m := Classical.choose_spec (vMem x)
    dsimp [F]
    by_cases hmn : m ≤ n
    · have hagr' := hagr m n hmn x.1 hm
      calc
        ((e m ⟨x.1, hm⟩ : IV (c m) (d m)) : ℝ)
            = ((e n ⟨x.1, hVmono hmn hm⟩ : IV (c n) (d n)) : ℝ) := hagr'.symm
        _ = ((e n ⟨x.1, hx⟩ : IV (c n) (d n)) : ℝ) := by
            apply congrArg (fun q : IV (c n) (d n) => (q : ℝ))
            apply congrArg (e n)
            apply Subtype.ext
            rfl
    · have hnm : n ≤ m := le_of_lt (lt_of_not_ge hmn)
      have hagr' := hagr n m hnm x.1 hx
      calc
        ((e m ⟨x.1, hm⟩ : IV (c m) (d m)) : ℝ)
            = ((e m ⟨x.1, hVmono hnm hx⟩ : IV (c m) (d m)) : ℝ) := by
                apply congrArg (fun q : IV (c m) (d m) => (q : ℝ))
                apply congrArg (e m)
                apply Subtype.ext
                rfl
        _ = ((e n ⟨x.1, hx⟩ : IV (c n) (d n)) : ℝ) := hagr'
  -- F is injective
  have hF_inj : Function.Injective F := by
    intro x y hxy
    have hval : ((F x : Rtyp) : ℝ) = ((F y : Rtyp) : ℝ) :=
      congrArg (fun q : Rtyp => (q : ℝ)) hxy
    let mx : ℕ := Classical.choose (vMem x)
    let my : ℕ := Classical.choose (vMem y)
    let hmx : x.1 ∈ V mx := Classical.choose_spec (vMem x)
    let hmy : y.1 ∈ V my := Classical.choose_spec (vMem y)
    let k : ℕ := max mx my
    have hxVk : x.1 ∈ V k := hVmono (le_max_left mx my) hmx
    have hyVk : y.1 ∈ V k := hVmono (le_max_right mx my) hmy
    have hxeq : ((F x : Rtyp) : ℝ) = ((e k ⟨x.1, hxVk⟩ : IV (c k) (d k)) : ℝ) := F_eq x k hxVk
    have hyeq : ((F y : Rtyp) : ℝ) = ((e k ⟨y.1, hyVk⟩ : IV (c k) (d k)) : ℝ) := F_eq y k hyVk
    have heqk : (e k ⟨x.1, hxVk⟩ : IV (c k) (d k)) = e k ⟨y.1, hyVk⟩ := by
      apply Subtype.ext
      exact hxeq.symm.trans (hval.trans hyeq)
    have harg : (⟨x.1, hxVk⟩ : {x : X // x ∈ V k}) = (⟨y.1, hyVk⟩ : {x : X // x ∈ V k}) :=
      (e k).injective heqk
    have hxval : x.1 = y.1 := congrArg (fun q : {x : X // x ∈ V k} => (q : X)) harg
    apply Subtype.ext
    exact hxval
  -- the explicit inverse
  let G : Rtyp → Utyp := fun t =>
    let n : ℕ := Classical.choose (tMem t)
    let ht : t.1 ∈ J n := Classical.choose_spec (tMem t)
    let y : {x : X // x ∈ V n} := (e n).symm ⟨t.1, ht⟩
    ⟨y.1, by
      change y.1 ∈ (⋃ n, V n)
      exact Set.mem_iUnion.mpr ⟨n, y.2⟩⟩
  have F_G : ∀ t : Rtyp, F (G t) = t := by
    intro t
    apply Subtype.ext
    let n : ℕ := Classical.choose (tMem t)
    let ht : t.1 ∈ J n := Classical.choose_spec (tMem t)
    let y : {x : X // x ∈ V n} := (e n).symm ⟨t.1, ht⟩
    have hFpre : ((F (G t) : Rtyp) : ℝ) = ((e n ⟨y.1, y.2⟩ : IV (c n) (d n)) : ℝ) := by
      dsimp [G]
      exact F_eq ⟨y.1, (by change y.1 ∈ (⋃ n, V n); exact Set.mem_iUnion.mpr ⟨n, y.2⟩)⟩ n y.2
    calc
      ((F (G t) : Rtyp) : ℝ) = ((e n ⟨y.1, y.2⟩ : IV (c n) (d n)) : ℝ) := hFpre
      _ = (t.1 : ℝ) := by
        have hy : (e n) ⟨y.1, y.2⟩ = (e n) y :=
          congrArg (e n) (by apply Subtype.ext; rfl)
        have heny : (e n) y = ⟨t.1, ht⟩ := by
          dsimp [y]
          exact (e n).apply_symm_apply ⟨t.1, ht⟩
        rw [hy, heny]
  have G_F : ∀ x : Utyp, G (F x) = x := by
    intro x
    exact hF_inj (F_G (F x))
  -- open slices of Utyp (over V n) and Rtyp (over J n)
  let Sn : ℕ → Set Utyp := fun n => {y : Utyp | (y : X) ∈ V n}
  have hSn_open : ∀ n, IsOpen (Sn n) := by
    intro n
    rw [show Sn n = (fun y : Utyp => (y : X)) ⁻¹' V n by
      ext y; simp [Sn]]
    exact (hVopen n).preimage continuous_subtype_val
  let Tn : ℕ → Set Rtyp := fun n => {y : Rtyp | (y : ℝ) ∈ J n}
  have hTn_open : ∀ n, IsOpen (Tn n) := by
    intro n
    rw [show Tn n = (fun y : Rtyp => (y : ℝ)) ⁻¹' (Set.Ioo (c n) (d n)) by
      ext y; simp [Tn, J]]
    exact isOpen_Ioo.preimage continuous_subtype_val
  -- continuity of F
  have hVUn : ∀ n, V n ⊆ U := by
    intro n x hx
    dsimp [U]
    exact Set.mem_iUnion.mpr ⟨n, hx⟩
  -- the slice {z : Utyp // z ∈ Sn n} is homeomorphic to {x : X // x ∈ V n}
  have hSliceF : ∀ n, Nonempty ({x : X // x ∈ V n} ≃ₜ {z : Utyp // z ∈ Sn n}) := by
    intro n
    let A := {x : X // x ∈ V n}
    let B := {z : Utyp // z ∈ Sn n}
    let Fn : A → B := fun x => ⟨⟨(x : X), hVUn n x.2⟩, x.2⟩
    let Gn : B → A := fun z => ⟨((z : Utyp).1), z.2⟩
    have hFG : Function.LeftInverse Gn Fn := by
      intro x
      apply Subtype.ext
      rfl
    have hGF : Function.RightInverse Gn Fn := by
      intro z
      apply Subtype.ext
      rfl
    have hFc : Continuous Fn := by
      dsimp [Fn]
      exact Continuous.subtype_mk
        (Continuous.subtype_mk continuous_subtype_val (by intro x; exact hVUn n x.2))
        (by intro x; exact x.2)
    have hGc : Continuous Gn := by
      dsimp [Gn]
      exact Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val)
        (by intro z; exact z.2)
    let e : A ≃ B := { toFun := Fn, invFun := Gn, left_inv := hFG, right_inv := hGF }
    exact ⟨Homeomorph.mk e hFc hGc⟩
  have hF_on : ∀ n, ContinuousOn F (Sn n) := by
    intro n
    rw [continuousOn_iff_continuous_domRestrict]
    let liftn : {z : Utyp // z ∈ Sn n} → {x : X // x ∈ V n} :=
      fun z => ⟨((z : Utyp).1), z.2⟩
    have hliftn_cont : Continuous (fun z : {q : Utyp // q ∈ Sn n} => liftn z) := by
      dsimp [liftn]
      exact Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val)
        (by intro z; exact z.2)
    let ψ : {z : Utyp // z ∈ Sn n} → Rtyp := fun z =>
      ⟨((e n) (liftn z) : ℝ), Set.mem_iUnion.mpr ⟨n, by simpa [J] using ((e n) (liftn z)).2⟩⟩
    have hψ_cont : Continuous ψ := by
      dsimp [ψ]
      exact Continuous.subtype_mk
        (continuous_subtype_val.comp ((e n).continuous.comp hliftn_cont))
        (by intro z; exact Set.mem_iUnion.mpr ⟨n, by simpa [J] using ((e n) (liftn z)).2⟩)
    have hdom : (Sn n).domRestrict F = ψ := by
      funext z
      apply Subtype.ext
      dsimp [Set.domRestrict, ψ, liftn]
      exact F_eq z.val n z.2
    rw [hdom]
    exact hψ_cont
  have hF_cont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases vMem x with ⟨n, hxn⟩
    exact (hF_on n).continuousAt (by
      exact (hSn_open n).mem_nhds (by simp [Sn]; exact hxn))
  have hG_on : ∀ n, ContinuousOn G (Tn n) := by
    intro n
    rw [continuousOn_iff_continuous_domRestrict]
    let Rn : {z : Rtyp // z ∈ Tn n} → IV (c n) (d n) :=
      fun z => ⟨((z : Rtyp).1), by simpa [Tn, J] using z.2⟩
    have hRn_cont : Continuous (fun z : {q : Rtyp // q ∈ Tn n} => Rn z) := by
      dsimp [Rn]
      exact Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val)
        (by intro z; simpa [Tn, J] using z.2)
    let θ : {z : Rtyp // z ∈ Tn n} → Utyp := fun z =>
      let w : {x : X // x ∈ V n} := (e n).symm (Rn z)
      ⟨(w : X), by change (w : X) ∈ (⋃ n, V n); exact Set.mem_iUnion.mpr ⟨n, w.2⟩⟩
    have hθ_cont : Continuous θ := by
      dsimp [θ]
      exact Continuous.subtype_mk
        (continuous_subtype_val.comp ((e n).symm.continuous.comp hRn_cont))
        (by intro z; exact Set.mem_iUnion.mpr ⟨n, (((e n).symm (Rn z)) : {x : X // x ∈ V n}).2⟩)
    have hθG : ∀ z : {r : Rtyp // r ∈ Tn n}, G (z : Rtyp) = θ z := by
      intro z
      apply hF_inj
      have hFθ : F (θ z) = (z : Rtyp) := by
        apply Subtype.ext
        let w : {x : X // x ∈ V n} := (e n).symm (Rn z)
        let memU : (w : X) ∈ (⋃ n, V n) := Set.mem_iUnion.mpr ⟨n, w.2⟩
        have hθx : θ z = ⟨(w : X), memU⟩ := by
          apply Subtype.ext
          dsimp [θ]
        rw [hθx]
        have h1 := F_eq ⟨(w : X), memU⟩ n w.2
        rw [h1]
        have hw : ((e n) ⟨(w : X), w.2⟩ : IV (c n) (d n)) = (e n) w := by
          apply congrArg (e n)
          apply Subtype.ext
          rfl
        rw [hw]
        have hw2 : (e n) w = Rn z := by
          dsimp [w]
          exact (e n).apply_symm_apply (Rn z)
        rw [hw2]
      calc
        F (G (z : Rtyp)) = (z : Rtyp) := F_G (z : Rtyp)
        _ = F (θ z) := hFθ.symm
    have hdom : (Tn n).domRestrict G = θ := by
      funext z
      dsimp [Set.domRestrict]
      exact hθG z
    rw [hdom]
    exact hθ_cont
  have hG_cont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro t
    rcases tMem t with ⟨n, htn⟩
    exact (hG_on n).continuousAt (by
      exact (hTn_open n).mem_nhds (by simp [Tn, J]; exact htn))
  let eEq : Utyp ≃ Rtyp :=
    { toFun := F, invFun := G, left_inv := G_F, right_inv := F_G }
  exact ⟨Homeomorph.mk eEq hF_cont hG_cont⟩


/-- **Main assembly**: a nested family of open arcs (each connected and
carrying an `(0,1)`-chart) has an `(0,1)`-chart on its union.  The
compatible interval charts of `nested_open_arcs_charts` paste to a
homeomorphism onto the open connected subset `⋃ n, (c n, d n)` of ℝ
(`nested_open_arcs_union_homeo_interval`), which is `≃ₜ (0,1)` because it
is a nonempty open preconnected subset of ℝ. -/
theorem nested_open_arcs_union_is_open_arc_general {X : Type u} [TopologicalSpace X]
    (V : ℕ → Set X) (hVopen : ∀ n, IsOpen (V n)) (hnest : ∀ n, V n ⊆ V (n + 1))
    (hconn : ∀ n, ConnectedSpace {x : X // x ∈ V n})
    (hchart : ∀ n, Nonempty (ORI₁ ≃ₜ {x : X // x ∈ V n})) :
    Nonempty (ORI₁ ≃ₜ {x : X // x ∈ (⋃ n, V n)}) := by
  classical
  rcases nested_open_arcs_charts (X := X) V hVopen hnest hconn hchart with ⟨c, d, e, hcd, hgrowth, hagr⟩
  rcases nested_open_arcs_union_homeo_interval (X := X) V hVopen hnest c d e hcd hgrowth hagr with ⟨emb⟩
  let J : ℕ → Set ℝ := fun n => Set.Ioo (c n) (d n)
  have hJopen : IsOpen (⋃ n, J n) := by
    exact isOpen_iUnion (fun n => isOpen_Ioo (α := ℝ))
  have hJsub : ∀ n, J n ⊆ J (n + 1) := by
    intro n x hx
    rcases hgrowth n with ⟨h1, h2⟩
    exact ⟨lt_of_le_of_lt h1 hx.1, lt_of_lt_of_le hx.2 h2⟩
  have hJpc : IsPreconnected (⋃ n, J n) := by
    have hpc1 : ∀ n, IsPreconnected (J n) := fun n => isPreconnected_Ioo (α := ℝ)
    have hne : ∀ n, (J n).Nonempty := fun n => by
      refine ⟨(c n + d n) / 2, ?_⟩
      have h := hcd n
      constructor <;> linarith
    have hov : ∀ n, (J n ∩ J (Nat.succ n)).Nonempty := by
      intro n
      rw [show Nat.succ n = n + 1 by omega]
      rcases hne n with ⟨x, hx⟩
      exact ⟨x, hx, hJsub n hx⟩
    simpa [Nat.succ_eq_add_one] using (IsPreconnected.iUnion_of_chain (s := J) hpc1 hov)
  have hJne : (⋃ n, J n).Nonempty := by
    have h0 : (J 0).Nonempty := by
      refine ⟨(c 0 + d 0) / 2, ?_⟩
      have h := hcd 0
      constructor <;> linarith
    rcases h0 with ⟨x, hx⟩
    exact ⟨x, Set.mem_iUnion.mpr ⟨0, hx⟩⟩
  rcases open_preconn_homeo_unit hJopen hJpc hJne with ⟨toUnit⟩
  exact ⟨(emb.trans toUnit).symm⟩

/-- **nested_open_arcs_union_is_open_arc**: the union of a nested family of
open arcs (each open in `X` and `≃ₜ (0,1)`) is again an open arc
`≃ₜ (0,1)`. -/
theorem nested_open_arcs_union_is_open_arc {X : Type*} [TopologicalSpace X] [T2Space X]
    (V : ℕ → Set X) (hVopen : ∀ n, IsOpen (V n)) (hnest : ∀ n, V n ⊆ V (n + 1))
    (hchart : ∀ n, Nonempty ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} ≃ₜ V n)) :
    Nonempty ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} ≃ₜ (⋃ n, V n)) := by
  have hconn : ∀ n, ConnectedSpace {x : X // x ∈ V n} := fun n => by
    rcases hchart n with ⟨e⟩
    exact (e.connectedSpace_iff).mp ori_connected
  exact nested_open_arcs_union_is_open_arc_general (X := X) V hVopen hnest hconn hchart

end Commons.Topology.OneManifold

end
