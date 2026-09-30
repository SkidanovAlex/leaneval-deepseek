import Mathlib
import Submission.Work.SymQuot.DivOf.powMapAux
import Submission.Work.SymQuot.DivOf.notMem_iUnion_intermediateField
import Submission.Work.SymQuot.DivOf.mem_placeIdeal_valAt_sub
import Submission.Work.SymQuot.DivOf.placeIdeal_isMaximal
import Submission.Work.SymQuot.DivOf.isDedekindDomain_sections
import Submission.Work.SymQuot.DivOf.exists_mem_placeIdeal_notMem_sq
import Submission.Work.SymQuot.DivOf.exists_valAt_ne
import Submission.Work.SymQuot.DivOf.valAt_algebraMap
import Submission.Work.CurveBasics.BaseChange.range_germ_baseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SymQuot.DivOf

open Work.CurveBasics
open Work.SpecLin (CurveFPt ptToPoint ptLeft)

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ} [NeZero n]
  [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]

/-! ## The value of a chart section at an `F`-point -/

/-- **The prime ideal of the underlying point of an `F`-point** `x m` in the chart ring
`Γ(C, d.V)`. -/
noncomputable def Pt {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) (x : Fin n → CurveFPt C F)
    (hs : ∀ m : Fin n, Set.range (x m).left.base ⊆ (d.V : Set C.left)) (m : Fin n) :
    Ideal (C.left.presheaf.obj (Opposite.op d.V)) :=
  (d.isAffineOpen_V.primeIdealOf
    ⟨(x m).left.base (IsLocalRing.closedPoint F),
      hs m ⟨IsLocalRing.closedPoint F, rfl⟩⟩).asIdeal

/-- The value of a chart section at the `F`-point `x m` vanishes if and only if the section lies
in the prime ideal of the underlying point of `x m`. -/
theorem valAt_eq_zero_iff {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) (x : Fin n → CurveFPt C F)
    (h : LandsInChart d x)
    (hs : ∀ m : Fin n, Set.range (x m).left.base ⊆ (d.V : Set C.left)) (m : Fin n)
    (b : C.left.presheaf.obj (Opposite.op d.V)) :
    valAt d x h m b = 0 ↔ b ∈ Pt d x hs m := by
  have hsle : ⊤ ≤ (x m).left ⁻¹ᵁ d.V := fun y _ => hs m ⟨y, rfl⟩
  rw [valAt_eq_GammaSpecIso_apply d x h m hsle b]
  exact (mem_primeIdealOf_iff_appLE_GammaSpecIso_eq_zero d.V d.isAffineOpen_V (x m).left
    hsle b).symm

/-- `ptToPoint` of an `F`-point whose image lies in `d.V` lies in the base-changed open. -/
theorem ptToPoint_mem_bcOpens {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) (s : CurveFPt C F)
    (hm : s.left.base (IsLocalRing.closedPoint F) ∈ (d.V : Set C.left)) :
    ptToPoint s ∈ C.bcOpens F d.V := by
  show (C.baseChangeFst F) (ptToPoint s) ∈ (d.V : Set C.left)
  rw [Work.SpecLin.Alt.baseChangeFst_ptToPoint]
  exact hm

/-- **The evaluation ring hom at the point of `C_F` lying over the `F`-point `s`** of `C`. -/
noncomputable abbrev ev {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) (s : CurveFPt C F)
    (hm : ptToPoint s ∈ C.bcOpens F d.V) :
    Γ((C.baseChange F).left, C.bcOpens F d.V) →+* F :=
  (((ptLeft s).appLE (C.bcOpens F d.V) ⊤ (fun y _ => by
      rw [show y = IsLocalRing.closedPoint F from Subsingleton.elim _ _]; exact hm)) ≫
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom

theorem ev_secConst {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) (s : CurveFPt C F)
    (hm : ptToPoint s ∈ C.bcOpens F d.V) (c : F) :
    ev d s hm (secConst C F d.V c) = c :=
  eval_sectionsAlgebraMap (C.bcOpens F d.V) (ptLeft s) _
    (Work.SpecLin.Points.ptLeft_comp_hom s) c

theorem ev_secAlpha {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) (x : Fin n → CurveFPt C F) (h : LandsInChart d x)
    (hs : ∀ m : Fin n, Set.range (x m).left.base ⊆ (d.V : Set C.left)) (m : Fin n)
    (b : C.left.presheaf.obj (Opposite.op d.V)) :
    ev d (x m) (ptToPoint_mem_bcOpens d (x m) (hs m ⟨_, rfl⟩))
        (secAlpha C F d.V b) = valAt d x h m b := by
  have hsle : ⊤ ≤ (x m).left ⁻¹ᵁ d.V := fun y _ => hs m ⟨y, rfl⟩
  have hσ : ⊤ ≤ ptLeft (x m) ⁻¹ᵁ C.bcOpens F d.V := fun y _ => by
    rw [show y = IsLocalRing.closedPoint F from Subsingleton.elim _ _]
    exact ptToPoint_mem_bcOpens d (x m) (hs m ⟨_, rfl⟩)
  exact (eval_secAlpha_eq_GammaSpecIso_apply d.V (x m) hsle hσ b).trans
    (valAt_eq_GammaSpecIso_apply d x h m hsle b).symm

theorem ev_eq_zero_iff {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) (s : CurveFPt C F)
    (hm : ptToPoint s ∈ C.bcOpens F d.V)
    (a : Γ((C.baseChange F).left, C.bcOpens F d.V)) :
    ev d s hm a = 0 ↔ a ∈ placeIdeal (C.baseChange F) (C.bcOpens F d.V)
      ⟨ptToPoint s, Work.SpecLin.Points.ptToPoint_isClosed s⟩ hm := by
  haveI : Nonempty (C.bcOpens F d.V) := ⟨⟨ptToPoint s, hm⟩⟩
  have hσ : ⊤ ≤ ptLeft s ⁻¹ᵁ C.bcOpens F d.V := fun y _ => by
    rw [show y = IsLocalRing.closedPoint F from Subsingleton.elim _ _]; exact hm
  rw [placeIdeal_eq_primeIdealOf
    (Work.CurveBasics.BaseChange.isAffineOpen_bcOpens F d.V d.isAffineOpen_V)
    ⟨ptToPoint s, Work.SpecLin.Points.ptToPoint_isClosed s⟩ hm]
  exact (mem_primeIdealOf_iff_appLE_GammaSpecIso_eq_zero _ _ _ hσ a).symm

/-! ## The `δ`-invariant and the existence of a chart section with simple vanishing -/

/-- The maximal ideal of the point of `C_F` lying over `s`, inside `Γ(C_F, V_F)`. -/
noncomputable abbrev Pzero {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) (s : CurveFPt C F) (hm : ptToPoint s ∈ C.bcOpens F d.V) :
    Ideal Γ((C.baseChange F).left, C.bcOpens F d.V) :=
  placeIdeal (C.baseChange F) (C.bcOpens F d.V)
    ⟨ptToPoint s, Work.SpecLin.Points.ptToPoint_isClosed s⟩ hm

/-- The class of `a - s (ev a)` in `Γ(C_F,V_F)/𝔭²`; its nonvanishing is the condition that the
chart section `a` has a simple zero at the point over `s`. -/
noncomputable abbrev delta {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) (s : CurveFPt C F) (hm : ptToPoint s ∈ C.bcOpens F d.V)
    (a : Γ((C.baseChange F).left, C.bcOpens F d.V)) :
    Γ((C.baseChange F).left, C.bcOpens F d.V) ⧸ (Pzero d s hm) ^ 2 :=
  Ideal.Quotient.mk _ (a - secConst C F d.V (ev d s hm a))

variable {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
  (d : ChartPt C n p) (s : CurveFPt C F) (hm : ptToPoint s ∈ C.bcOpens F d.V)

theorem delta_add (a b : Γ((C.baseChange F).left, C.bcOpens F d.V)) :
    delta d s hm (a + b) = delta d s hm a + delta d s hm b := by
  simp only [delta, map_add, map_sub]
  ring

theorem delta_zero : delta d s hm 0 = 0 := by
  rw [delta, map_zero (ev d s hm), map_zero (secConst C F d.V), sub_zero]
  exact map_zero _

theorem delta_neg (a : Γ((C.baseChange F).left, C.bcOpens F d.V)) :
    delta d s hm (-a) = -delta d s hm a := by
  have h1 : -a - -(secConst C F d.V (ev d s hm a))
      = -(a - secConst C F d.V (ev d s hm a)) := by ring
  rw [delta, delta, map_neg (ev d s hm), map_neg (secConst C F d.V), h1, map_neg]

theorem delta_one : delta d s hm 1 = 0 := by
  rw [delta, map_one (ev d s hm), map_one (secConst C F d.V), sub_self]
  exact map_zero _

theorem delta_secConst (c : F) : delta d s hm (secConst C F d.V c) = 0 := by
  rw [delta, ev_secConst, sub_self]
  exact map_zero _

/-- The derivation rule for `δ`: `δ (a * b) = c (ev a) * δ b + c (ev b) * δ a`
(with `c` the constant section). -/
theorem delta_mul (a b : Γ((C.baseChange F).left, C.bcOpens F d.V)) :
    delta d s hm (a * b) =
      Ideal.Quotient.mk _ (secConst C F d.V (ev d s hm a)) * delta d s hm b +
      Ideal.Quotient.mk _ (secConst C F d.V (ev d s hm b)) * delta d s hm a := by
  have hz_mem : ∀ x : Γ((C.baseChange F).left, C.bcOpens F d.V),
      x - secConst C F d.V (ev d s hm x) ∈ Pzero d s hm := by
    intro x
    rw [show Pzero d s hm = placeIdeal (C.baseChange F) (C.bcOpens F d.V)
      ⟨ptToPoint s, Work.SpecLin.Points.ptToPoint_isClosed s⟩ hm from rfl]
    rw [← ev_eq_zero_iff d s hm]
    simp only [map_sub, ev_secConst, sub_self]
  have hmem_a := hz_mem a
  have hmem_b := hz_mem b
  have hz : Ideal.Quotient.mk ((Pzero d s hm) ^ 2)
      ((a - secConst C F d.V (ev d s hm a)) * (b - secConst C F d.V (ev d s hm b))) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_two]
    exact Ideal.mul_mem_mul hmem_a hmem_b
  have hrep : a * b - secConst C F d.V (ev d s hm (a * b))
      = secConst C F d.V (ev d s hm a) * (b - secConst C F d.V (ev d s hm b))
        + secConst C F d.V (ev d s hm b) * (a - secConst C F d.V (ev d s hm a))
        + (a - secConst C F d.V (ev d s hm a)) * (b - secConst C F d.V (ev d s hm b)) := by
    rw [map_mul (ev d s hm), map_mul (secConst C F d.V)]
    ring
  rw [delta, delta, delta, hrep, map_add, map_add, map_mul, map_mul, hz, add_zero]

/-- If `δ a = 0` and `δ b = 0` then `δ (a * b) = 0`. -/
theorem delta_mul_eq_zero (a b : Γ((C.baseChange F).left, C.bcOpens F d.V))
    (ha : delta d s hm a = 0) (hb : delta d s hm b = 0) :
    delta d s hm (a * b) = 0 := by
  rw [delta_mul, ha, hb, mul_zero, mul_zero, add_zero]

/-- The subring of `Γ(C_F,V_F)` on which `δ` vanishes. -/
noncomputable def deltaKer : Subring Γ((C.baseChange F).left, C.bcOpens F d.V) where
  carrier := {a | delta d s hm a = 0}
  mul_mem' := by
    intro a b ha hb
    exact delta_mul_eq_zero d s hm a b ha hb
  one_mem' := delta_one d s hm
  add_mem' := by
    intro a b ha hb
    have ha' : delta d s hm a = 0 := ha
    have hb' : delta d s hm b = 0 := hb
    show delta d s hm (a + b) = 0
    rw [delta_add, ha', hb', add_zero]
  zero_mem' := delta_zero d s hm
  neg_mem' := by
    intro a ha
    have ha' : delta d s hm a = 0 := ha
    show delta d s hm (-a) = 0
    rw [delta_neg, ha', neg_zero]


/-! ## Congruence lemmas (the auxiliary membership proofs are irrelevant) -/

theorem Pzero_congr {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) (s : CurveFPt C F)
    (hm hm' : ptToPoint s ∈ C.bcOpens F d.V) :
    Pzero d s hm = Pzero d s hm' := by
  have h : hm = hm' := Subsingleton.elim _ _
  rw [h]

theorem ev_congr {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) (s : CurveFPt C F)
    (hm hm' : ptToPoint s ∈ C.bcOpens F d.V) :
    ev d s hm = ev d s hm' := by
  have h : hm = hm' := Subsingleton.elim _ _
  rw [h]

theorem delta_congr {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) (s : CurveFPt C F)
    (hm hm' : ptToPoint s ∈ C.bcOpens F d.V)
    (a : Γ((C.baseChange F).left, C.bcOpens F d.V)) :
    delta d s hm a = delta d s hm' a := by
  have h : hm = hm' := Subsingleton.elim _ _
  rw [h]

/-! ## The dictionary between the chart ring and `C_F` -/

/-- **A chart section vanishes at the point over `x m`** exactly when it lies in the prime ideal
of the underlying point of `x m`. -/
theorem secAlpha_mem_Pzero_iff {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) (x : Fin n → CurveFPt C F) (h : LandsInChart d x)
    (hs : ∀ m : Fin n, Set.range (x m).left.base ⊆ (d.V : Set C.left)) (m : Fin n)
    (hm : ptToPoint (x m) ∈ C.bcOpens F d.V) (b : C.left.presheaf.obj (Opposite.op d.V)) :
    secAlpha C F d.V b ∈ Pzero d (x m) hm ↔ b ∈ Pt d x hs m := by
  have hmcanon := ptToPoint_mem_bcOpens d (x m) (hs m ⟨_, rfl⟩)
  rw [Pzero_congr d (x m) hm hmcanon]
  rw [← ev_eq_zero_iff d (x m) hmcanon (secAlpha C F d.V b)]
  rw [show ev d (x m) hmcanon (secAlpha C F d.V b) = valAt d x h m b from
    ev_secAlpha d x h hs m b]
  exact valAt_eq_zero_iff d x h hs m b

/-! ## A chart section with simple vanishing at the point over `x m₀` -/

/-- **There is a chart section whose pullback to `C_F` has a simple zero at the point over
`x m₀`** (condition (I)), i.e. `δ ≠ 0` for some `b`. -/
theorem exists_delta_secAlpha_ne_zero {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : ChartPt C n p) (x : Fin n → CurveFPt C F) (h : LandsInChart d x)
    (hs : ∀ m : Fin n, Set.range (x m).left.base ⊆ (d.V : Set C.left)) (m₀ : Fin n)
    (hmem : ptToPoint (x m₀) ∈ C.bcOpens F d.V) :
    ∃ b : C.left.presheaf.obj (Opposite.op d.V),
      delta d (x m₀) hmem (secAlpha C F d.V b) ≠ 0 := by
  classical
  by_contra hall
  push_neg at hall
  have hgen : Set.range (secAlpha C F d.V) ∪ Set.range (secConst C F d.V) ⊆
      (deltaKer d (x m₀) hmem : Set _) := by
    intro a ha
    rcases ha with ⟨b, rfl⟩ | ⟨c, rfl⟩
    · exact hall b
    · exact delta_secConst d (x m₀) hmem c
  have hle : Subring.closure (Set.range (secAlpha C F d.V) ∪ Set.range (secConst C F d.V)) ≤
      deltaKer d (x m₀) hmem := Subring.closure_le.mpr hgen
  have hrange1 : Set.range (secAlpha C F d.V) =
      Set.range ((C.baseChangeFst F).app d.V).hom := by
    ext y
    constructor <;> rintro ⟨b, rfl⟩ <;> exact ⟨b, by rw [secAlpha_eq_app]⟩
  have hrange2 : Set.range (secConst C F d.V) =
      Set.range (algebraMap F Γ((C.baseChange F).left, C.bcOpens F d.V)) := by
    ext y
    constructor <;> rintro ⟨c, rfl⟩ <;> exact ⟨c, rfl⟩
  have htop : Subring.closure (Set.range (secAlpha C F d.V) ∪ Set.range (secConst C F d.V)) = ⊤ := by
    rw [hrange1, hrange2]
    exact Work.CurveBasics.BaseChange.closure_range_union_range_eq_top_bcOpens C F d.V d.isAffineOpen_V
  have hallzero : ∀ a : Γ((C.baseChange F).left, C.bcOpens F d.V),
      delta d (x m₀) hmem a = 0 := fun a =>
    hle (by rw [htop]; exact Subring.mem_top a)
  obtain ⟨a, ha1, ha2⟩ := exists_mem_placeIdeal_notMem_sq (C.bcOpens F d.V)
    (Work.CurveBasics.BaseChange.isAffineOpen_bcOpens F d.V d.isAffineOpen_V)
    ⟨ptToPoint (x m₀), Work.SpecLin.Points.ptToPoint_isClosed (x m₀)⟩ hmem
  have heva : ev d (x m₀) hmem a = 0 := by
    rw [ev_eq_zero_iff d (x m₀) hmem a]
    rw [show placeIdeal (C.baseChange F) (C.bcOpens F d.V)
      ⟨ptToPoint (x m₀), Work.SpecLin.Points.ptToPoint_isClosed (x m₀)⟩ hmem =
      Pzero d (x m₀) hmem from rfl]
    exact ha1
  have hz : delta d (x m₀) hmem a = Ideal.Quotient.mk _ a := by
    rw [delta, heva, map_zero (secConst C F d.V), sub_zero]
  have h0 := hallzero a
  rw [hz, Ideal.Quotient.eq_zero_iff_mem] at h0
  exact ha2 h0


end Work.SymQuot.DivOf
