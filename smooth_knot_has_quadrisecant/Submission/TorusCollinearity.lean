import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.KnotMap
import Submission.CollinearityMap
import Submission.TrisecantClosed
import Submission.TrisecantLocus
import Submission.TrisecantCurve
import Submission.LocalCurve

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology

/-!
# Layer A (viii) — the torus-level collinearity map and the lift of Milestone 1

Milestone 1 (`LocalSmoothCurveTheorem`, `Submission/LocalCurve.lean`) proved,
at every general-position collinear off-diagonal real triple `(a,b,m)`, that
the local zero set of the collinearity map `Φ` is a `C¹` curve through the
triple.  The trisecant locus is, however, a quotient object: the knot is a
*circle* (`KnotParam = AddCircle period`), so collinearity data live on the
three-torus `T³ = KnotParamTriple`.  This module

1. constructs the **torus-level collinearity map**
   `torusCollinearity r (a,b,m) = (K a − K b) × (K a − K m)` with
   `K = knotMap r` (the same cross product as on the real cube, but in the
   circle parameters), proves it continuous and that its zero set in `T³`
   is **closed and compact** (the compactness of the trisecant data over the
   period torus);
2. proves the bridge `torusCollinearity r (π₃ w) = collinearityMap r w` for
   every real triple `w` (where `π₃ : ℝ³ → T³` is the coordinate-wise
   period quotient) — the real and torus pictures carry identical
   collinearity information;
3. proves that the **strict trisecant data** (`openMiddleData r`, the
   attached middle point strictly between the chord endpoints) lie inside
   the collinearity zero set, and (when the chord endpoints are distinct)
   inside the off-diagonal locus — the zero set really contains the
   genuine trisecants, not merely degenerate ones;
4. **lifts Milestone 1 to the torus**: at a torus-level collinear
   off-diagonal triple `p ∈ T³` whose fundamental-domain representatives
   are in general position, the torus zero set near `p` is the projection
   of a real local curve: a continuous curve in `T³` through `p`, contained
   in the zero/off-diagonal locus, covering every torus-level zero in a
   torus neighbourhood of `p`, and injective on a subinterval (the
   quotient `π₃` is a local injection on fundamental boxes, since two
   parameters that agree modulo the period and lie less than a period
   apart must be equal).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-! ## 1. The knot on the circle

The map `r : ℝ → Space` is `period`-periodic (`IsSmoothKnot.periodic`), so
its values on the real line depend only on the class in
`KnotParam = AddCircle period`.  The next lemma records this: `knotMap r`
applied to the class of `x` is exactly `r x`.  (This is *not* the same as
`knotMap_coe`, which requires `x ∈ Ico 0 period`; here `x` is arbitrary and
the equality uses the periodicity of `r`.) -/

/-- A class congruence `(x : KnotParam) = (y : KnotParam)` means `x − y` is
an integer multiple of the period. -/
lemma zmultiples_of_coe_eq {x y : ℝ} (h : (x : KnotParam) = (y : KnotParam)) :
    x - y ∈ AddSubgroup.zmultiples period := by
  exact (QuotientAddGroup.eq_iff_sub_mem).mp h

/-- Two congruent reals have equal knot values (they differ by an integer
multiple of the period, and `r` is `period`-periodic). -/
lemma r_eq_of_coe_eq {r : ℝ → Space} (h : IsSmoothKnot r) {x y : ℝ} (hxy : (x : KnotParam) = (y : KnotParam)) :
    r x = r y := by
  have hz := zmultiples_of_coe_eq hxy
  rcases (AddSubgroup.mem_zmultiples_iff).mp hz with ⟨k, hk⟩
  have hx : x = y + k • period := by
    exact (sub_eq_iff_eq_add.mp hk.symm).trans (add_comm (k • period) y)
  have hper : Function.Periodic r (k • period) := (h.periodic.zsmul k)
  rw [hx]
  exact hper y

/-- **The knot on the circle**: `knotMap r` evaluated at the class of a real
parameter `x` equals `r x` (for *any* real `x`, by periodicity). -/
lemma knotMap_eq_r {r : ℝ → Space} (h : IsSmoothKnot r) (x : ℝ) : knotMap r (x : KnotParam) = r x := by
  rcases knotMap_representative (x : KnotParam) with ⟨t, htI, ht⟩
  rw [← ht]
  rw [knotMap_coe r htI]
  exact r_eq_of_coe_eq h ht

/-! ## 2. The torus-level collinearity map

The real collinearity map `Φ` is `period`-periodic in each argument
(`periodic_collinearity_arg1/2/3`), so it really lives on the three-torus
`KnotParamTriple`.  Rather than re-quotienting, we define the torus map
directly through `knotMap r` (which is exactly `r` on the circle by
`knotMap_eq_r`). -/

/-- The coordinate-wise period quotient `ℝ³ → T³`. -/
abbrev torusQuotient (q : RealParamTriple) : KnotParamTriple :=
  Prod.map (fun x : ℝ => (x : KnotParam))
    (Prod.map (fun y : ℝ => (y : KnotParam)) (fun z : ℝ => (z : KnotParam))) q

/-- The torus quotient map is open (a product of the open quotient maps
`ℝ → AddCircle period`). -/
lemma isOpenMap_torusQuotient : IsOpenMap (torusQuotient : RealParamTriple → KnotParamTriple) := by
  change IsOpenMap (Prod.map (fun x : ℝ => (x : KnotParam))
    (Prod.map (fun y : ℝ => (y : KnotParam)) (fun z : ℝ => (z : KnotParam))))
  exact (QuotientAddGroup.isOpenMap_coe (N := AddSubgroup.zmultiples period)).prodMap
    ((QuotientAddGroup.isOpenMap_coe (N := AddSubgroup.zmultiples period)).prodMap
      (QuotientAddGroup.isOpenMap_coe (N := AddSubgroup.zmultiples period)))

/-- The torus quotient map is continuous. -/
lemma continuous_torusQuotient : Continuous (torusQuotient : RealParamTriple → KnotParamTriple) := by
  change Continuous (Prod.map (fun x : ℝ => (x : KnotParam))
    (Prod.map (fun y : ℝ => (y : KnotParam)) (fun z : ℝ => (z : KnotParam))))
  fun_prop

/-- **The torus-level collinearity map**: for circle parameters `a b m`,
`(K a − K b) × (K a − K m)` with `K = knotMap r`.  By `knotMap_eq_r` this
carries exactly the same collinearity information as the real map `Φ`. -/
def torusCollinearity (r : ℝ → Space) (p : KnotParamTriple) : Space :=
  cross3 (knotMap r p.1 - knotMap r p.2.1) (knotMap r p.1 - knotMap r p.2.2)

/-- **The bridge**: on the quotient of a real triple, the torus map agrees
with the real map. -/
lemma torusCollinearity_quotient {r : ℝ → Space} (h : IsSmoothKnot r) (w : RealParamTriple) :
    torusCollinearity r (torusQuotient w) = collinearityMap r w := by
  simp [torusCollinearity, collinearityMap, torusQuotient, knotMap_eq_r h]

/-- The torus-level collinearity map is continuous. -/
lemma continuous_torusCollinearity {r : ℝ → Space} (h : IsSmoothKnot r) :
    Continuous (torusCollinearity r) := by
  unfold torusCollinearity
  have hk : Continuous (knotMap r) := IsSmoothKnot.knotMap_continuous h
  have hf : Continuous (fun p : KnotParamTriple => knotMap r p.1 - knotMap r p.2.1) := by
    refine Continuous.sub ?_ ?_
    · exact hk.comp continuous_fst
    · exact hk.comp (Continuous.fst continuous_snd)
  have hg : Continuous (fun p : KnotParamTriple => knotMap r p.1 - knotMap r p.2.2) := by
    refine Continuous.sub ?_ ?_
    · exact hk.comp continuous_fst
    · exact hk.comp (Continuous.snd continuous_snd)
  exact continuous_cross3.comp (Continuous.prodMk hf hg)

/-- The zero set of the torus collinearity map is closed. -/
theorem isClosed_torusCollinearityZero {r : ℝ → Space} (h : IsSmoothKnot r) :
    IsClosed {p : KnotParamTriple | torusCollinearity r p = 0} := by
  have hset : {p : KnotParamTriple | torusCollinearity r p = 0} =
      (torusCollinearity r ⁻¹' ({0} : Set Space)) := by
    ext p
    simp
  rw [hset]
  exact (isClosed_singleton (x := (0 : Space))).preimage (continuous_torusCollinearity h)

/-- The zero set of the torus collinearity map is compact (closed inside the
compact three-torus). -/
theorem isCompact_torusCollinearityZero {r : ℝ → Space} (h : IsSmoothKnot r) :
    IsCompact {p : KnotParamTriple | torusCollinearity r p = 0} := by
  exact (isClosed_torusCollinearityZero h).isCompact

/-! ## 3. Off-diagonal triples and the strict trisecant data on the torus -/

/-- A torus triple of parameters whose three knot points are pairwise
distinct (the torus analogue of `RealOffDiagonalTriples`). -/
def TorusOffDiag (r : ℝ → Space) : Set KnotParamTriple :=
  {p | knotMap r p.1 ≠ knotMap r p.2.1 ∧ knotMap r p.1 ≠ knotMap r p.2.2 ∧
    knotMap r p.2.1 ≠ knotMap r p.2.2}

/-- Knot points pairwise distinct is the same as parameters pairwise
distinct (`knotMap` is injective on the whole circle). -/
lemma knotMap_inj_iff {r : ℝ → Space} (h : IsSmoothKnot r) {x y : KnotParam} :
    knotMap r x = knotMap r y ↔ x = y := (knotMap_injective h).eq_iff

/-- Knot points pairwise distinct is the same as parameters pairwise
distinct (`knotMap` is injective on the whole circle). -/
lemma TorusOffDiag_iff_params {r : ℝ → Space} (h : IsSmoothKnot r) (p : KnotParamTriple) :
    p ∈ TorusOffDiag r ↔ p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 := by
  constructor
  · intro hp
    rcases hp with ⟨h1, h2, h3⟩
    constructor
    · exact fun hpp => h1 ((knotMap_inj_iff h).mpr hpp)
    · constructor
      · exact fun hpp => h2 ((knotMap_inj_iff h).mpr hpp)
      · exact fun hpp => h3 ((knotMap_inj_iff h).mpr hpp)
  · intro hp
    rcases hp with ⟨h1, h2, h3⟩
    constructor
    · exact fun hk => h1 ((knotMap_inj_iff h).mp hk)
    · constructor
      · exact fun hk => h2 ((knotMap_inj_iff h).mp hk)
      · exact fun hk => h3 ((knotMap_inj_iff h).mp hk)

/-- The strict-middle condition on the quotient of a real triple agrees with
the real strict-middle condition on the values of `r`. -/
lemma IsMiddleOnOpenChord_quotient {r : ℝ → Space} (h : IsSmoothKnot r) (w : RealParamTriple) :
    IsMiddleOnOpenChord r (torusQuotient w).1 (torusQuotient w).2.1 (torusQuotient w).2.2 ↔
      knotMap r (torusQuotient w).2.2 ∈ openSegment ℝ (r w.1) (r w.2.1) := by
  simp [IsMiddleOnOpenChord, torusQuotient, knotMap_eq_r h]

/-- A point strictly between two others has zero cross product with the
chord direction: strict betweenness forces collinearity. -/
lemma mem_openSegment_cross3 {u v w : Space} (hw : w ∈ openSegment ℝ u v) :
    cross3 (u - v) (u - w) = 0 := by
  rcases hw with ⟨a, b, ha, hb, hab, hw⟩
  have hsub : u - w = b • (u - v) := by
    rw [← hw]
    calc
      u - (a • u + b • v) = (a + b) • u - (a • u + b • v) := by
        rw [hab]
        simp
      _ = (a • u + b • u) - (a • u + b • v) := by rw [add_smul]
      _ = b • u - b • v := by abel
      _ = b • (u - v) := by rw [smul_sub]
  rw [hsub, cross3_smul_right, cross3_self]
  simp

/-- **Strict trisecant data lie in the torus collinearity zero set**: a
middle point strictly between the chord endpoints is collinear with them,
so every strict trisecant triple is a zero of `torusCollinearity`. -/
lemma openMiddleData_subset_collinearity_zero (r : ℝ → Space) :
    openMiddleData r ⊆ {p : KnotParamTriple | torusCollinearity r p = 0} := by
  intro p hp
  unfold torusCollinearity
  exact mem_openSegment_cross3 hp

/-- A strict middle point with distinct chord endpoints gives an
off-diagonal torus triple: all three knot points are pairwise distinct. -/
lemma openMiddleData_offDiag_of_endpoints_ne (r : ℝ → Space) {p : KnotParamTriple}
    (hp : p ∈ openMiddleData r) (hab : knotMap r p.1 ≠ knotMap r p.2.1) : p ∈ TorusOffDiag r := by
  have hm : knotMap r p.2.2 ∈ openSegment ℝ (knotMap r p.1) (knotMap r p.2.1) := hp
  rcases ne_left_right_of_mem_openSegment (E := Space) hab hm with ⟨h1, h2⟩
  simp [TorusOffDiag, hab, h1.symm, h2.symm]

/-- The closure of the strict trisecant data is contained in the torus
collinearity zero set (the zero set is closed). -/
lemma closure_openMiddleData_subset_collinearity_zero {r : ℝ → Space} (h : IsSmoothKnot r) :
    closure (openMiddleData r) ⊆ {p : KnotParamTriple | torusCollinearity r p = 0} := by
  exact closure_minimal (openMiddleData_subset_collinearity_zero r)
    (isClosed_torusCollinearityZero h)

/-- The strict trisecant data are *bounded* by the compact zero set, hence
their closure is compact. -/
theorem isCompact_closure_openMiddleData {r : ℝ → Space} (h : IsSmoothKnot r) :
    IsCompact (closure (openMiddleData r)) := by
  exact (isClosed_torusCollinearityZero h).isCompact.of_isClosed_subset
    (isClosed_closure)
    (closure_openMiddleData_subset_collinearity_zero h)

/-- The quotient of a real triple is off-diagonal at the torus level exactly
when the real triple is off-diagonal (knot values of the classes are the
real values, by `knotMap_eq_r`). -/
lemma TorusOffDiag_quotient_iff {r : ℝ → Space} (h : IsSmoothKnot r) (w : RealParamTriple) :
    torusQuotient w ∈ TorusOffDiag r ↔ RealOffDiagonalTriples r w := by
  have h1 : knotMap r (w.1 : KnotParam) ≠ knotMap r (w.2.1 : KnotParam) ↔ r w.1 ≠ r w.2.1 := by
    rw [knotMap_eq_r h, knotMap_eq_r h]
  have h2 : knotMap r (w.1 : KnotParam) ≠ knotMap r (w.2.2 : KnotParam) ↔ r w.1 ≠ r w.2.2 := by
    rw [knotMap_eq_r h, knotMap_eq_r h]
  have h3 : knotMap r (w.2.1 : KnotParam) ≠ knotMap r (w.2.2 : KnotParam) ↔ r w.2.1 ≠ r w.2.2 := by
    rw [knotMap_eq_r h, knotMap_eq_r h]
  unfold TorusOffDiag RealOffDiagonalTriples torusQuotient
  constructor
  · intro h
    rcases h with ⟨h₁, h₂, h₃⟩
    constructor
    · exact sub_ne_zero.mpr (h1.mp h₁)
    · constructor
      · exact sub_ne_zero.mpr (h2.mp h₂)
      · exact sub_ne_zero.mpr (ne_comm.mp (h3.mp h₃))
  · intro h
    rcases h with ⟨h₁, h₂, h₃⟩
    constructor
    · exact h1.mpr (sub_ne_zero.mp h₁)
    · constructor
      · exact h2.mpr (sub_ne_zero.mp h₂)
      · exact h3.mpr (ne_comm.mpr (sub_ne_zero.mp h₃))

/-! ## 4. Injectivity of the torus quotient on fundamental boxes

The quotient map `ℝ → KnotParam` identifies reals that differ by an integer
multiple of the period.  On an open interval of width strictly less than a
period there can be no such pair, so the quotient is injective there; the
three-torus quotient is consequently injective on any box whose sides are
shorter than the period.  This is what makes the projection of the real
local curves an *embedded* (injective) curve in the torus. -/

/-- A (strictly less than the period) integer multiple of the period with
absolute value smaller than the period is zero. -/
lemma abs_zsmul_lt_of_lt {k : ℤ} {p : ℝ} (hp : 0 < p) (h : |k • p| < p) : k = 0 := by
  rw [zsmul_eq_mul] at h
  have h' : |(k : ℝ)| * p < p := by
    simpa [abs_mul, abs_of_pos hp] using h
  have hk' : |(k : ℝ)| < 1 := by
    have hm : |(k : ℝ)| * p < (1 : ℝ) * p := by simpa using h'
    exact (mul_lt_mul_iff_of_pos_right hp).mp hm
  rw [abs_lt] at hk'
  have hlow : (-1 : ℤ) < k := by exact_mod_cast hk'.1
  have hhigh : k < 1 := by exact_mod_cast hk'.2
  omega

/-- The period quotient is injective on any open interval of width strictly
less than the period. -/
lemma coe_injOn_Ioo {c η : ℝ} (h2 : 2 * η < period) :
    Set.InjOn (fun x : ℝ => (x : KnotParam)) (Set.Ioo (c - η) (c + η)) := by
  intro x hx y hy hxy
  have hz : x - y ∈ AddSubgroup.zmultiples period := (QuotientAddGroup.eq_iff_sub_mem).mp hxy
  rcases (AddSubgroup.mem_zmultiples_iff).mp hz with ⟨k, hk⟩
  have hlt2 : |k • (period : ℝ)| < period := by
    rw [hk]
    have hxy1 : x - y < 2 * η := by
      calc x - y < (c + η) - (c - η) := sub_lt_sub hx.2 hy.1
        _ = 2 * η := by ring
    have hyx1 : y - x < 2 * η := by
      calc y - x < (c + η) - (c - η) := sub_lt_sub hy.2 hx.1
        _ = 2 * η := by ring
    rw [abs_lt]
    constructor <;> linarith
  have hk0 := abs_zsmul_lt_of_lt (k := k) (p := period) period_pos hlt2
  subst k
  simp at hk
  linarith

/-- A product of three intervals of width strictly less than the period
(around a real triple) maps injectively into the torus. -/
lemma torusQuotient_injOn_box {a b m η : ℝ} (h2 : 2 * η < period) :
    Set.InjOn (torusQuotient : RealParamTriple → KnotParamTriple)
      {w : RealParamTriple | w.1 ∈ Set.Ioo (a - η) (a + η) ∧
        w.2.1 ∈ Set.Ioo (b - η) (b + η) ∧ w.2.2 ∈ Set.Ioo (m - η) (m + η)} := by
  intro w hw w' hw' hqq
  -- per-coordinate class equality
  have hc1 : (w.1 : KnotParam) = (w'.1 : KnotParam) := by
    have := congrArg Prod.fst hqq
    simpa [torusQuotient] using this
  have hc2 : (w.2.1 : KnotParam) = (w'.2.1 : KnotParam) := by
    have h0 := congrArg (fun p : KnotParamTriple => p.2.1) hqq
    simpa [torusQuotient] using h0
  have hc3 : (w.2.2 : KnotParam) = (w'.2.2 : KnotParam) := by
    have h0 := congrArg (fun p : KnotParamTriple => p.2.2) hqq
    simpa [torusQuotient] using h0
  have h1 := coe_injOn_Ioo (c := a) (η := η) h2 hw.1 hw'.1 hc1
  have h2' := coe_injOn_Ioo (c := b) (η := η) h2 hw.2.1 hw'.2.1 hc2
  have h3 := coe_injOn_Ioo (c := m) (η := η) h2 hw.2.2 hw'.2.2 hc3
  -- w = (w.1, (w.2.1, w.2.2)) and same for w'
  cases w with
  | mk w1 w23 =>
    cases w23 with
    | mk w2 w3 =>
      cases w' with
      | mk w1' w23' =>
        cases w23' with
        | mk w2' w3' =>
          have hw1 : w1 = w1' := by simpa using h1
          have hw2 : w2 = w2' := by simpa using h2'
          have hw3 : w3 = w3' := by simpa using h3
          simp [hw1, hw2, hw3]

/-! ## 5. Milestone 1 lifted to the torus

We record the local structure of the torus zero set that Milestone 1
(`smooth_local_curve_of_general_position`) provides after pushing down the
period quotient: near a torus-level collinear off-diagonal triple with
general-position fundamental-domain representatives there is a continuous
curve in `T³` through the triple, lying in the zero/off-diagonal locus,
covering every torus zero in a torus neighbourhood, and injective on a
subinterval. -/

/-- A real triple together with fundamental-domain representatives: the
`η`-box around the representatives sits inside the torus injectively
provided `2η < period`. -/
def FundBox (a b m η : ℝ) : Set RealParamTriple :=
  {w : RealParamTriple | w.1 ∈ Set.Ioo (a - η) (a + η) ∧
    w.2.1 ∈ Set.Ioo (b - η) (b + η) ∧ w.2.2 ∈ Set.Ioo (m - η) (m + η)}

/-- The fundamental box is open. -/
lemma isOpen_FundBox (a b m η : ℝ) : IsOpen (FundBox a b m η) := by
  unfold FundBox
  have hf1 : Continuous (fun w : RealParamTriple => w.1) := by fun_prop
  have hf2 : Continuous (fun w : RealParamTriple => w.2.1) := by fun_prop
  have hf3 : Continuous (fun w : RealParamTriple => w.2.2) := by fun_prop
  exact (isOpen_Ioo.preimage hf1).inter ((isOpen_Ioo.preimage hf2).inter (isOpen_Ioo.preimage hf3))

/-- The torus quotient maps the fundamental box injectively (its sides are
`2η < period`). -/
lemma injOn_torusQuotient_FundBox {a b m η : ℝ} (h2 : 2 * η < period) :
    Set.InjOn (torusQuotient : RealParamTriple → KnotParamTriple) (FundBox a b m η) := by
  simpa [FundBox] using torusQuotient_injOn_box (a := a) (b := b) (m := m) (η := η) h2

/-- **The main theorem (Milestone 1 on the torus).**  Let `p : T³` be a
collinear off-diagonal triple (three distinct knot points, collinear
images), and suppose its fundamental-domain representatives are in general
position (`TrisecantGeneralPosition`).  Then near `p` the torus zero set of
`torusCollinearity` is the projection of a real local curve: there is a
continuous curve in `T³` through `p`, contained in the zero/off-diagonal
locus, which covers every torus-level off-diagonal zero in a torus
neighbourhood `V` of `p`; the curve is injective on a subinterval around
`0`. -/
theorem torus_local_structure_of_general_position (r : ℝ → Space) (h : IsSmoothKnot r)
    (p : KnotParamTriple) (hpZ : torusCollinearity r p = 0) (hpOff : p ∈ TorusOffDiag r)
    (hgp : ∃ a b m : ℝ, a ∈ Set.Ico 0 period ∧ b ∈ Set.Ico 0 period ∧ m ∈ Set.Ico 0 period ∧
      (a : KnotParam) = p.1 ∧ (b : KnotParam) = p.2.1 ∧ (m : KnotParam) = p.2.2 ∧
      TrisecantGeneralPosition r a b m) :
    ∃ V : Set KnotParamTriple, IsOpen V ∧ p ∈ V ∧
      ∃ lo hi : ℝ, lo < 0 ∧ 0 < hi ∧ ∃ γ : ℝ → KnotParamTriple,
        ContinuousOn γ (Set.Ioo lo hi) ∧ γ 0 = p ∧
        (∀ t ∈ Set.Ioo lo hi, torusCollinearity r (γ t) = 0 ∧ γ t ∈ TorusOffDiag r) ∧
        (∀ q ∈ V, torusCollinearity r q = 0 → q ∈ TorusOffDiag r →
          ∃ t ∈ Set.Ioo lo hi, γ t = q) ∧
        (∃ lo' hi' : ℝ, lo ≤ lo' ∧ lo' < 0 ∧ 0 < hi' ∧ hi' ≤ hi ∧
          Set.InjOn γ (Set.Ioo lo' hi') ∧ ∀ t ∈ Set.Ioo lo' hi', γ t ∈ V) := by
  rcases hgp with ⟨a, b, m, ha, hb, hm, hpa, hpb, hpm, hgpGP⟩
  let p0 : RealParamTriple := (a, (b, m))
  have hpq : torusQuotient p0 = p := by
    simp [p0, torusQuotient, hpa, hpb, hpm]
  -- real zero from torus zero
  have hpZreal : collinearityMap r p0 = 0 := by
    rw [← hpq] at hpZ
    rw [torusCollinearity_quotient h p0] at hpZ
    exact hpZ
  -- real off-diagonal from torus off-diagonal
  have hpOffReal : p0 ∈ RealOffDiagonalTriples r := by
    rw [← hpq] at hpOff
    exact (TorusOffDiag_quotient_iff h p0).mp hpOff
  -- Milestone 1 on the real triple
  have hloc := smooth_local_curve_of_general_position r h a b m hgpGP (by
    simpa [p0, collinearityMap, collinearityValue_eq] using hpZreal)
  rcases hloc with ⟨_hColl0, _hOff0, _hR1⟩
  rcases _hR1 with ⟨U, hUo, hUp, _hR2⟩
  rcases _hR2 with ⟨lo, hi, hlo, hhi, _hR3⟩
  rcases _hR3 with ⟨γ, hγCd, hγInj, hγ0, hγgood, hcover⟩
  have hγc : ContinuousOn γ (Set.Ioo lo hi) := ContDiffOn.continuousOn hγCd
  -- the fundamental box radius
  let η : ℝ := period / 4
  have hηpos : 0 < η := by
    dsimp [η]
    exact div_pos period_pos (by norm_num)
  have h2η : 2 * η < period := by
    dsimp [η]
    have hper : 0 < period := period_pos
    nlinarith
  let B : Set RealParamTriple := FundBox a b m η
  have hBo : IsOpen B := isOpen_FundBox a b m η
  have hBp0 : p0 ∈ B := by
    unfold B FundBox p0
    simp only [Set.mem_ofPred_eq]
    constructor
    · constructor <;> linarith
    · constructor
      · constructor <;> linarith
      · constructor <;> linarith
  -- the neighbourhood W = U ∩ B
  let W : Set RealParamTriple := U ∩ B
  have hWo : IsOpen W := hUo.inter hBo
  have hWp0 : p0 ∈ W := ⟨hUp, hBp0⟩
  -- torus neighbourhood V
  let V : Set KnotParamTriple := torusQuotient '' W
  have hVo : IsOpen V := by
    dsimp [V]
    exact isOpenMap_torusQuotient W hWo
  have hVp : p ∈ V := by
    refine ⟨p0, hWp0, hpq⟩
  -- the torus curve
  let γt : ℝ → KnotParamTriple := fun t => torusQuotient (γ t)
  have hγtc : ContinuousOn γt (Set.Ioo lo hi) := by
    exact continuous_torusQuotient.comp_continuousOn hγc
  have hγt0 : γt 0 = p := by
    dsimp [γt]
    rw [hγ0, hpq]
  have hγtgood : ∀ t ∈ Set.Ioo lo hi, torusCollinearity r (γt t) = 0 ∧ γt t ∈ TorusOffDiag r := by
    intro t ht
    have hg := hγgood t ht
    rcases hg with ⟨hU, hΦ, hOff⟩
    constructor
    · rw [torusCollinearity_quotient h (γ t)]
      exact hΦ
    · exact (TorusOffDiag_quotient_iff h (γ t)).mpr hOff
  -- covering
  have hcoverT : ∀ q ∈ V, torusCollinearity r q = 0 → q ∈ TorusOffDiag r →
      ∃ t ∈ Set.Ioo lo hi, γt t = q := by
    intro q hqV hqZ hqOff
    rcases hqV with ⟨w, hwW, hwq⟩
    have hwU : w ∈ U := hwW.1
    have hwB : w ∈ B := hwW.2
    have hqZreal : collinearityMap r w = 0 := by
      rw [← hwq] at hqZ
      rw [torusCollinearity_quotient h w] at hqZ
      exact hqZ
    have hqOffReal : w ∈ RealOffDiagonalTriples r := by
      rw [← hwq] at hqOff
      exact (TorusOffDiag_quotient_iff h w).mp hqOff
    rcases hcover w hwU hqZreal hqOffReal with ⟨t, ht, hγt⟩
    refine ⟨t, ht, ?_⟩
    dsimp [γt]
    rw [hγt, hwq]
  -- injectivity on a subinterval
  have hcat0 : ContinuousAt γ 0 := by
    exact hγc.continuousAt (isOpen_Ioo.mem_nhds ⟨hlo, hhi⟩)
  have hγ0B : γ 0 ∈ B := by
    rw [hγ0]
    exact hBp0
  have hpre : {t | γ t ∈ B} ∈ 𝓝 (0 : ℝ) := by
    exact hcat0.preimage_mem_nhds (hBo.mem_nhds hγ0B)
  rcases exists_Ioo_subset_of_mem_nhds hpre with ⟨a0, b0, ha0, hb0, hab0⟩
  let lo' : ℝ := max a0 lo
  let hi' : ℝ := min b0 hi
  have hllo' : lo ≤ lo' := by dsimp [lo']; exact le_max_right a0 lo
  have hlo'0 : lo' < 0 := by
    dsimp [lo']
    exact max_lt ha0 hlo
  have h0hi' : 0 < hi' := by
    dsimp [hi']
    exact lt_min hb0 hhi
  have hhi'h : hi' ≤ hi := by dsimp [hi']; exact min_le_right b0 hi
  have hγtB : ∀ t ∈ Set.Ioo lo' hi', γ t ∈ B := by
    intro t ht
    have ht1 : t ∈ Set.Ioo a0 b0 := by
      constructor
      · exact lt_of_le_of_lt (le_max_left a0 lo) (by simpa [lo'] using ht.1)
      · exact lt_of_lt_of_le (by simpa [hi'] using ht.2) (min_le_left b0 hi)
    have ht2 : t ∈ Set.Ioo lo hi := by
      constructor
      · exact lt_of_le_of_lt (le_max_right a0 lo) (by simpa [lo'] using ht.1)
      · exact lt_of_lt_of_le (by simpa [hi'] using ht.2) (min_le_right b0 hi)
    simpa using hab0 ht1
  have hγtinj : Set.InjOn γt (Set.Ioo lo' hi') := by
    intro t₁ ht₁ t₂ ht₂ h
    apply hγInj
    · exact (Set.Ioo_subset_Ioo (show lo ≤ lo' by exact hllo') (show hi' ≤ hi by exact hhi'h)) ht₁
    · exact (Set.Ioo_subset_Ioo (show lo ≤ lo' by exact hllo') (show hi' ≤ hi by exact hhi'h)) ht₂
    · have h1 : γ t₁ ∈ B := hγtB t₁ ht₁
      have h2 : γ t₂ ∈ B := hγtB t₂ ht₂
      have hq1 : torusQuotient (γ t₁) ∈ torusQuotient '' B := ⟨γ t₁, h1, rfl⟩
      have hq2 : torusQuotient (γ t₂) ∈ torusQuotient '' B := ⟨γ t₂, h2, rfl⟩
      have hinjB : Set.InjOn torusQuotient B := by
        simpa [B] using (injOn_torusQuotient_FundBox (a := a) (b := b) (m := m) (η := η) h2η)
      have hγ12 : γ t₁ = γ t₂ := by
        apply hinjB h1 h2
        simpa [γt] using h
      exact hγ12
  -- the injective sub-arc stays inside V (its real preimage stays in the
  -- fundamental box W, whose torus projection is V)
  have hγtV : ∀ t ∈ Set.Ioo lo' hi', γt t ∈ V := by
    intro t ht
    have htin : t ∈ Set.Ioo lo hi := (Set.Ioo_subset_Ioo hllo' hhi'h) ht
    have hg := hγgood t htin
    dsimp [γt, V]
    refine ⟨γ t, ⟨hg.1, hγtB t ht⟩, rfl⟩
  exact ⟨V, hVo, hVp, lo, hi, hlo, hhi, γt, hγtc, hγt0, hγtgood, hcoverT,
    ⟨lo', hi', hllo', hlo'0, h0hi', hhi'h, hγtinj, hγtV⟩⟩

/-! ### Consequences

The uniform statement: if *every* off-diagonal collinear torus triple is in
general position, then every such triple has the local structure above.  We
record the packaged form. -/

/-- A torus-level general-position hypothesis: at every collinear
off-diagonal triple the fundamental-domain representatives are in general
position. -/
def TorusGeneralPosition (r : ℝ → Space) : Prop :=
  ∀ p : KnotParamTriple, torusCollinearity r p = 0 → p ∈ TorusOffDiag r →
    ∃ a b m : ℝ, a ∈ Set.Ico 0 period ∧ b ∈ Set.Ico 0 period ∧ m ∈ Set.Ico 0 period ∧
      (a : KnotParam) = p.1 ∧ (b : KnotParam) = p.2.1 ∧ (m : KnotParam) = p.2.2 ∧
      TrisecantGeneralPosition r a b m

/-- Under the torus-level general-position hypothesis every collinear
off-diagonal torus triple has the local curve structure of
`torus_local_structure_of_general_position`. -/
theorem torus_local_structure_of_general_position_all (r : ℝ → Space) (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (p : KnotParamTriple)
    (hpZ : torusCollinearity r p = 0) (hpOff : p ∈ TorusOffDiag r) :
    ∃ V : Set KnotParamTriple, IsOpen V ∧ p ∈ V ∧
      ∃ lo hi : ℝ, lo < 0 ∧ 0 < hi ∧ ∃ γ : ℝ → KnotParamTriple,
        ContinuousOn γ (Set.Ioo lo hi) ∧ γ 0 = p ∧
        (∀ t ∈ Set.Ioo lo hi, torusCollinearity r (γ t) = 0 ∧ γ t ∈ TorusOffDiag r) ∧
        (∀ q ∈ V, torusCollinearity r q = 0 → q ∈ TorusOffDiag r →
          ∃ t ∈ Set.Ioo lo hi, γ t = q) ∧
        (∃ lo' hi' : ℝ, lo ≤ lo' ∧ lo' < 0 ∧ 0 < hi' ∧ hi' ≤ hi ∧
          Set.InjOn γ (Set.Ioo lo' hi') ∧ ∀ t ∈ Set.Ioo lo' hi', γ t ∈ V) := by
  exact torus_local_structure_of_general_position r h p hpZ hpOff (hgp p hpZ hpOff)

end LeanEval.KnotTheory.Quadrisecant
