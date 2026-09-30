import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.polyrel_basic
import Submission.Work.BMF.top_coeff_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# N5 `adi_cycles`: the quadruple graph and its labelled walks (definitions)

Combinatorial objects for the counting argument of `Work.BMF.adi_cycles`
(MRT §4, MRTTZ Prop. 3.7).

Conventions.  The vertices are the intervals of the family `D.fam`.  The subgraph
`GAdjQ D q` keeps the arcs whose attached prime set contains a fixed prime `q`.  For a
step `x → y` of a walk, `stepWit` is a witnessing edge of `D.edges`, traversed in the
direction `x → y` (possibly backwards, see `stepFwd`); then

  `(1/stepV)_* φ_x  ~_{1/p}  (1/stepU)_* φ_y`   for every `p ∈ stepS`

where `stepV` is the prime multiplying the phase at the source `x`, `stepU` at the
target `y`, and `stepS` is the prime set attached to the witnessing edge
(`step_rel`).  The geometry of a step is `x ≈ (stepV/stepU) y` (`stepGeom`).
-/

namespace Work.BMF

open Polynomial Finset Real

variable {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}

/-- The vertices of the quadruple graph: the members of the family. -/
abbrev GVert (D : QuadData k f c C X L P₁ P₂) : Type _ := {x : ℝ // x ∈ D.fam}

instance (D : QuadData k f c C X L P₁ P₂) : Fintype (GVert D) := inferInstance

/-- The prime set attached to an edge by `QuadData.rel` (junk value outside `D.edges`). -/
noncomputable def edgeS (D : QuadData k f c C X L P₁ P₂) (e : Edge) : Finset ℕ := by
  classical
  exact if h : e ∈ D.edges then (D.rel e h).choose else ∅

lemma edgeS_eq (D : QuadData k f c C X L P₁ P₂) {e : Edge} (he : e ∈ D.edges) :
    edgeS D e = (D.rel e he).choose := by
  classical
  unfold edgeS
  exact dif_pos he

lemma edgeS_subset (D : QuadData k f c C X L P₁ P₂) {e : Edge} (he : e ∈ D.edges)
    {p : ℕ} (hp : p ∈ edgeS D e) : IsPrimeIn (P₂ / 2) P₂ p := by
  rw [edgeS_eq D he] at hp
  exact ((D.rel e he).choose_spec).1 p hp

lemma edgeS_card (D : QuadData k f c C X L P₁ P₂) {e : Edge} (he : e ∈ D.edges) :
    c * pi0 P₂ ≤ ((edgeS D e).card : ℝ) := by
  rw [edgeS_eq D he]
  exact ((D.rel e he).choose_spec).2.1

lemma edgeS_rel (D : QuadData k f c C X L P₁ P₂) {e : Edge} (he : e ∈ D.edges)
    {p : ℕ} (hp : p ∈ edgeS D e) : EdgeRel k C (1 / (p : ℝ)) L D.pol e := by
  rw [edgeS_eq D he] at hp
  exact ((D.rel e he).choose_spec).2.2 p hp

lemma EdgeGeom.x₂_mem {S : Finset ℝ} {P L : ℝ} {e : Edge} (h : EdgeGeom S P L e) :
    e.x₂ ∈ S := h.2.1
lemma EdgeGeom.x₁_ne {S : Finset ℝ} {P L : ℝ} {e : Edge} (h : EdgeGeom S P L e) :
    e.x₁ ≠ e.x₂ := h.2.2.1
lemma EdgeGeom.p_ne {S : Finset ℝ} {P L : ℝ} {e : Edge} (h : EdgeGeom S P L e) :
    e.p₁ ≠ e.p₂ := h.2.2.2.1
lemma EdgeGeom.prime_p₁ {S : Finset ℝ} {P L : ℝ} {e : Edge} (h : EdgeGeom S P L e) :
    IsPrimeIn P (2 * P) e.p₁ := h.2.2.2.2.1
lemma EdgeGeom.prime_p₂ {S : Finset ℝ} {P L : ℝ} {e : Edge} (h : EdgeGeom S P L e) :
    IsPrimeIn P (2 * P) e.p₂ := h.2.2.2.2.2.1
lemma EdgeGeom.geom {S : Finset ℝ} {P L : ℝ} {e : Edge} (h : EdgeGeom S P L e) :
    |e.x₁ - ((e.p₂ : ℝ) / e.p₁) * e.x₂| ≤ 100 * L := h.2.2.2.2.2.2

/-- The (symmetric) adjacency of the subgraph of arcs whose prime set contains `q`. -/
def GAdjQ (D : QuadData k f c C X L P₁ P₂) (q : ℕ) (x y : GVert D) : Prop :=
  ∃ e ∈ D.edges, q ∈ edgeS D e ∧
    ((e.x₁ = x.1 ∧ e.x₂ = y.1) ∨ (e.x₁ = y.1 ∧ e.x₂ = x.1))

noncomputable instance (D : QuadData k f c C X L P₁ P₂) (q : ℕ) :
    DecidableRel (GAdjQ (P₂ := P₂) D q) :=
  fun x y => Classical.dec _

lemma GAdjQ_symm (D : QuadData k f c C X L P₁ P₂) (q : ℕ) (x y : GVert D) :
    GAdjQ D q x y ↔ GAdjQ D q y x := by
  constructor
  · rintro ⟨e, he, hq, h | h⟩
    · exact ⟨e, he, hq, Or.inr h⟩
    · exact ⟨e, he, hq, Or.inl h⟩
  · rintro ⟨e, he, hq, h | h⟩
    · exact ⟨e, he, hq, Or.inr h⟩
    · exact ⟨e, he, hq, Or.inl h⟩

/-- A chosen edge witnessing an ordered arc `x → y`. -/
noncomputable def arcWit (D : QuadData k f c C X L P₁ P₂) (x y : ℝ) : Edge := by
  classical
  exact if h : ∃ e ∈ D.edges, e.x₁ = x ∧ e.x₂ = y then Classical.choose h else ⟨0, 0, 0, 0⟩

lemma arcWit_spec (D : QuadData k f c C X L P₁ P₂) {x y : ℝ}
    (h : ∃ e ∈ D.edges, e.x₁ = x ∧ e.x₂ = y) :
    arcWit D x y ∈ D.edges ∧ (arcWit D x y).x₁ = x ∧ (arcWit D x y).x₂ = y := by
  classical
  have hc := Classical.choose_spec h
  rw [arcWit, dif_pos h]
  exact hc

/-- An arc `x → y` is witnessed in the forward direction. -/
def stepFwd (D : QuadData k f c C X L P₁ P₂) (x y : GVert D) : Prop :=
  ∃ e ∈ D.edges, e.x₁ = x.1 ∧ e.x₂ = y.1

noncomputable instance (D : QuadData k f c C X L P₁ P₂) (x y : GVert D) :
    Decidable (stepFwd (P₂ := P₂) D x y) := Classical.dec _

/-- The witnessing edge of the step `x → y`. -/
noncomputable def stepWit (D : QuadData k f c C X L P₁ P₂) (x y : GVert D) : Edge := by
  classical
  exact if stepFwd D x y then arcWit D x.1 y.1 else arcWit D y.1 x.1

/-- The prime dividing the phase at the source `x` of the step `x → y`. -/
noncomputable def stepV (D : QuadData k f c C X L P₁ P₂) (x y : GVert D) : ℕ := by
  classical
  exact if stepFwd D x y then (arcWit D x.1 y.1).p₂ else (arcWit D y.1 x.1).p₁

/-- The prime dividing the phase at the target `y` of the step `x → y`. -/
noncomputable def stepU (D : QuadData k f c C X L P₁ P₂) (x y : GVert D) : ℕ := by
  classical
  exact if stepFwd D x y then (arcWit D x.1 y.1).p₁ else (arcWit D y.1 x.1).p₂

/-- The prime set attached to the step `x → y`. -/
noncomputable def stepS (D : QuadData k f c C X L P₁ P₂) (x y : GVert D) : Finset ℕ :=
  edgeS D (stepWit D x y)

lemma stepV_fwd (D : QuadData k f c C X L P₁ P₂) {x y : GVert D} (h : stepFwd D x y) :
    stepV D x y = (arcWit D x.1 y.1).p₂ := by
  classical
  unfold stepV
  rw [if_pos h]

lemma stepU_fwd (D : QuadData k f c C X L P₁ P₂) {x y : GVert D} (h : stepFwd D x y) :
    stepU D x y = (arcWit D x.1 y.1).p₁ := by
  classical
  unfold stepU
  rw [if_pos h]

lemma stepWit_fwd (D : QuadData k f c C X L P₁ P₂) {x y : GVert D} (h : stepFwd D x y) :
    stepWit D x y = arcWit D x.1 y.1 := by
  classical
  unfold stepWit
  rw [if_pos h]

lemma stepV_rev (D : QuadData k f c C X L P₁ P₂) {x y : GVert D} (h : ¬ stepFwd D x y) :
    stepV D x y = (arcWit D y.1 x.1).p₁ := by
  classical
  unfold stepV
  rw [if_neg h]

lemma stepU_rev (D : QuadData k f c C X L P₁ P₂) {x y : GVert D} (h : ¬ stepFwd D x y) :
    stepU D x y = (arcWit D y.1 x.1).p₂ := by
  classical
  unfold stepU
  rw [if_neg h]

lemma stepWit_rev (D : QuadData k f c C X L P₁ P₂) {x y : GVert D} (h : ¬ stepFwd D x y) :
    stepWit D x y = arcWit D y.1 x.1 := by
  classical
  unfold stepWit
  rw [if_neg h]

/-- The reverse-arc existence is forced when the forward one fails. -/
lemma stepFwd_or_rev {D : QuadData k f c C X L P₁ P₂} {q : ℕ} {x y : GVert D}
    (hxy : GAdjQ D q x y) (h : ¬ stepFwd D x y) :
    ∃ e ∈ D.edges, e.x₁ = y.1 ∧ e.x₂ = x.1 := by
  obtain ⟨e, he, hq, hh | hh⟩ := hxy
  · exact absurd ⟨e, he, hh.1, hh.2⟩ h
  · exact ⟨e, he, hh.1, hh.2⟩

/-- The prime set of a step, unfolded. -/
lemma stepS_eq (D : QuadData k f c C X L P₁ P₂) (x y : GVert D) :
    stepS D x y = edgeS D (stepWit D x y) := rfl

/-- The two primes of a step of a `q`-arc lie in `[P₁, 2P₁]`. -/
lemma stepV_prime (D : QuadData k f c C X L P₁ P₂) {q : ℕ} {x y : GVert D}
    (hxy : GAdjQ D q x y) : IsPrimeIn P₁ (2 * P₁) (stepV D x y) := by
  classical
  by_cases h : stepFwd D x y
  · rw [stepV_fwd D h]
    exact EdgeGeom.prime_p₂ (D.geom _ (arcWit_spec D h).1)
  · rw [stepV_rev D h]
    exact EdgeGeom.prime_p₁ (D.geom _ (arcWit_spec D (stepFwd_or_rev hxy h)).1)

lemma stepU_prime (D : QuadData k f c C X L P₁ P₂) {q : ℕ} {x y : GVert D}
    (hxy : GAdjQ D q x y) : IsPrimeIn P₁ (2 * P₁) (stepU D x y) := by
  classical
  by_cases h : stepFwd D x y
  · rw [stepU_fwd D h]
    exact EdgeGeom.prime_p₁ (D.geom _ (arcWit_spec D h).1)
  · rw [stepU_rev D h]
    exact EdgeGeom.prime_p₂ (D.geom _ (arcWit_spec D (stepFwd_or_rev hxy h)).1)

/-- Swapping the roles of `x` and `y` in the step geometry, at the cost of the factor `2`
coming from `v/u ≤ 2`. -/
lemma geom_swap {x y u v L : ℝ} (hu : 0 < u) (hv : 0 < v) (hvu : v / u ≤ 2)
    (h : |y - (u / v) * x| ≤ 100 * L) (hL : 0 ≤ L) :
    |x - (v / u) * y| ≤ 200 * L := by
  have key : x - (v / u) * y = -((v / u) * (y - (u / v) * x)) := by
    field_simp
    ring
  rw [key, abs_neg, abs_mul, abs_of_nonneg (div_nonneg hv.le hu.le)]
  calc (v / u) * |y - (u / v) * x| ≤ 2 * (100 * L) :=
        mul_le_mul hvu h (abs_nonneg _) (by norm_num)
    _ = 200 * L := by ring

/-- Geometry of a step: `x ≈ (stepV/stepU) y`. -/
lemma stepGeom (D : QuadData k f c C X L P₁ P₂) {q : ℕ} {x y : GVert D}
    (hxy : GAdjQ D q x y) (hP : 0 < P₁) (hL : 0 < L) :
    |x.1 - ((stepV D x y : ℝ) / (stepU D x y : ℝ)) * y.1| ≤ 200 * L := by
  classical
  by_cases h : stepFwd D x y
  · have hspec := arcWit_spec D h
    have hg := EdgeGeom.geom (D.geom _ hspec.1)
    rw [hspec.2.1, hspec.2.2] at hg
    rw [stepV_fwd D h, stepU_fwd D h]
    linarith [hg, hP, hL]
  · have hrev := stepFwd_or_rev hxy h
    have hspec := arcWit_spec D hrev
    have hg := EdgeGeom.geom (D.geom _ hspec.1)
    rw [hspec.2.1, hspec.2.2] at hg
    rw [stepV_rev D h, stepU_rev D h]
    have hUpos : 0 < (((arcWit D y.1 x.1).p₂ : ℕ) : ℝ) := by
      have hh := (EdgeGeom.prime_p₂ (D.geom _ hspec.1)).2.1
      linarith [hP, hh]
    have hVpos : 0 < (((arcWit D y.1 x.1).p₁ : ℕ) : ℝ) := by
      have hh := (EdgeGeom.prime_p₁ (D.geom _ hspec.1)).2.1
      linarith [hP, hh]
    have h1 : (((arcWit D y.1 x.1).p₁ : ℕ) : ℝ) ≤ 2 * P₁ :=
      (EdgeGeom.prime_p₁ (D.geom _ hspec.1)).2.2
    have h2 : P₁ ≤ (((arcWit D y.1 x.1).p₂ : ℕ) : ℝ) :=
      (EdgeGeom.prime_p₂ (D.geom _ hspec.1)).2.1
    have hvu : (((arcWit D y.1 x.1).p₁ : ℕ) : ℝ) / (((arcWit D y.1 x.1).p₂ : ℕ) : ℝ) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    exact geom_swap hUpos hVpos hvu hg hL.le

/-- Two elements of the family closer than `500 L` coincide. -/
lemma fam_eq_of_lt (D : QuadData k f c C X L P₁ P₂) (hL : 0 < L) {y y' : GVert D}
    (h : |y.1 - y'.1| < 500 * L) : y = y' := by
  by_contra hne
  have hsep := D.isFam.2 y.1 y.2 y'.1 y'.2 (fun hh => hne (Subtype.ext hh))
  linarith

/-- The reverse form of the step geometry: `y ≈ (stepU/stepV) x`. -/
lemma stepGeom' (D : QuadData k f c C X L P₁ P₂) {q : ℕ} {x y : GVert D}
    (hxy : GAdjQ D q x y) (hP : 0 < P₁) (hL : 0 < L) :
    |y.1 - ((stepU D x y : ℝ) / (stepV D x y : ℝ)) * x.1| ≤ 200 * L := by
  classical
  have hu : (0:ℝ) < (stepU D x y : ℝ) := by
    have := (stepU_prime D hxy).2.1; linarith [hP]
  have hv : (0:ℝ) < (stepV D x y : ℝ) := by
    have := (stepV_prime D hxy).2.1; linarith [hP]
  have hvu : ((stepU D x y : ℝ) / (stepV D x y : ℝ)) ≤ 2 := by
    have h1 : (stepU D x y : ℝ) ≤ 2 * P₁ := (stepU_prime D hxy).2.2
    have h2 : P₁ ≤ (stepV D x y : ℝ) := (stepV_prime D hxy).2.1
    rw [div_le_iff₀ (by linarith)]; linarith
  by_cases h : stepFwd D x y
  · have hspec := arcWit_spec D h
    have hg := EdgeGeom.geom (D.geom _ hspec.1)
    rw [hspec.2.1, hspec.2.2] at hg
    have hgl : |x.1 - ((stepV D x y : ℝ) / (stepU D x y : ℝ)) * y.1| ≤ 100 * L := by
      rw [stepV_fwd D h, stepU_fwd D h]; exact hg
    have key : y.1 - ((stepU D x y : ℝ) / (stepV D x y : ℝ)) * x.1
        = -(((stepU D x y : ℝ) / (stepV D x y : ℝ)) *
            (x.1 - ((stepV D x y : ℝ) / (stepU D x y : ℝ)) * y.1)) := by
      field_simp
      ring
    rw [key, abs_neg, abs_mul, abs_of_nonneg (div_nonneg hu.le hv.le)]
    calc ((stepU D x y : ℝ) / (stepV D x y : ℝ)) *
          |x.1 - ((stepV D x y : ℝ) / (stepU D x y : ℝ)) * y.1|
        ≤ 2 * (100 * L) := mul_le_mul hvu hgl (abs_nonneg _) (by norm_num)
      _ = 200 * L := by ring
  · have hspec := arcWit_spec D (stepFwd_or_rev hxy h)
    have hg := EdgeGeom.geom (D.geom _ hspec.1)
    rw [hspec.2.1, hspec.2.2] at hg
    have hgl : |y.1 - ((stepU D x y : ℝ) / (stepV D x y : ℝ)) * x.1| ≤ 100 * L := by
      rw [stepU_rev D h, stepV_rev D h]; exact hg
    linarith [hgl, hP, hL]

/-- The labels of a step determine the next vertex. -/
lemma step_unique (D : QuadData k f c C X L P₁ P₂) (hP : 0 < P₁) (hL : 0 < L) {q : ℕ}
    {x y y' : GVert D} (hxy : GAdjQ D q x y) (hxy' : GAdjQ D q x y')
    (h1 : stepV D x y = stepV D x y') (h2 : stepU D x y = stepU D x y') : y = y' := by
  set M : ℝ := ((stepU D x y : ℝ) / (stepV D x y : ℝ)) * x.1 with hM
  have hA : |y.1 - M| ≤ 200 * L := by
    rw [hM]; exact stepGeom' D hxy hP hL
  have hB : |y'.1 - M| ≤ 200 * L := by
    have hh := stepGeom' D hxy' hP hL
    rw [← h1, ← h2] at hh
    rw [hM]
    exact hh
  have key : |y.1 - y'.1| ≤ |y.1 - M| + |y'.1 - M| := by
    have h := abs_sub_le y.1 M y'.1
    have h2 : |M - y'.1| = |y'.1 - M| := abs_sub_comm M y'.1
    linarith [h, h2]
  refine fam_eq_of_lt D hL ?_
  linarith

/-- The relation carried by a step, at modulus `1/p` for `p` in its prime set. -/
lemma step_rel (D : QuadData k f c C X L P₁ P₂) (hC : 0 < C) (hL : 0 < L) (hP : 0 < P₁)
    {q p : ℕ} {x y : GVert D} (hxy : GAdjQ D q x y) (hp : p ∈ stepS D x y) :
    PolyRel k (max C (symmConst k C)) (1 / (p : ℝ))
      (x.1 / (stepV D x y : ℝ)) (L / (stepV D x y : ℝ))
        (dil (stepV D x y : ℝ) (D.pol x.1))
      (y.1 / (stepU D x y : ℝ)) (L / (stepU D x y : ℝ))
        (dil (stepU D x y : ℝ) (D.pol y.1)) := by
  classical
  have hm : C ≤ max C (symmConst k C) := le_max_left _ _
  have hVpos : (0 : ℝ) < (stepV D x y : ℝ) := by
    have := (stepV_prime D hxy).2.1; linarith [hP]
  have hUpos : (0 : ℝ) < (stepU D x y : ℝ) := by
    have := (stepU_prime D hxy).2.1; linarith [hP]
  by_cases h : stepFwd D x y
  · have hspec := arcWit_spec D h
    have hp' : p ∈ edgeS D (arcWit D x.1 y.1) := by
      rw [stepS_eq, stepWit_fwd D h] at hp; exact hp
    have hrel := edgeS_rel D hspec.1 hp'
    rw [EdgeRel] at hrel
    rw [hspec.2.1, hspec.2.2] at hrel
    rw [stepV_fwd D h, stepU_fwd D h]
    have hp₂ : (0 : ℝ) < (((arcWit D x.1 y.1).p₂ : ℕ) : ℝ) := by
      have hh := (EdgeGeom.prime_p₂ (D.geom _ hspec.1)).2.1; linarith [hP, hh]
    have hp₁ : (0 : ℝ) < (((arcWit D x.1 y.1).p₁ : ℕ) : ℝ) := by
      have hh := (EdgeGeom.prime_p₁ (D.geom _ hspec.1)).2.1; linarith [hP, hh]
    exact PolyRel.mono hrel hm (div_nonneg hL.le hp₂.le) (div_nonneg hL.le hp₁.le)
  · have hrev := stepFwd_or_rev hxy h
    have hspec := arcWit_spec D hrev
    have hp' : p ∈ edgeS D (arcWit D y.1 x.1) := by
      rw [stepS_eq, stepWit_rev D h] at hp; exact hp
    have hrel := edgeS_rel D hspec.1 hp'
    rw [EdgeRel] at hrel
    rw [hspec.2.1, hspec.2.2] at hrel
    rw [stepV_rev D h, stepU_rev D h]
    have hp₂ : (0 : ℝ) < (((arcWit D y.1 x.1).p₂ : ℕ) : ℝ) := by
      have hh := (EdgeGeom.prime_p₂ (D.geom _ hspec.1)).2.1; linarith [hP, hh]
    have hp₁ : (0 : ℝ) < (((arcWit D y.1 x.1).p₁ : ℕ) : ℝ) := by
      have hh := (EdgeGeom.prime_p₁ (D.geom _ hspec.1)).2.1; linarith [hP, hh]
    have hsym := PolyRel.symm hrel hC (div_pos hL hp₂) (div_pos hL hp₁)
    exact PolyRel.mono hsym (le_max_right _ _) (div_nonneg hL.le hp₁.le) (div_nonneg hL.le hp₂.le)

/-! ## Uniqueness of the witnessing edge -/

/-- Distinct primes in `[P,2P]` with the same ratio coincide. -/
lemma prime_ratio_inj {p₁ p₂ p₃ p₄ : ℕ} (h1 : Nat.Prime p₁) (h2 : Nat.Prime p₂)
    (h3 : Nat.Prime p₃) (h12 : p₁ ≠ p₂) (h : (p₂ : ℝ) / p₁ = (p₄ : ℝ) / p₃) :
    p₁ = p₃ ∧ p₂ = p₄ := by
  have h1n : (p₁:ℝ) ≠ 0 := by exact_mod_cast h1.ne_zero
  have h3n : (p₃:ℝ) ≠ 0 := by exact_mod_cast h3.ne_zero
  have hmul : (p₂ : ℝ) * p₃ = (p₄ : ℝ) * p₁ := (div_eq_div_iff h1n h3n).mp h
  have hmuln : p₂ * p₃ = p₄ * p₁ := by exact_mod_cast hmul
  have hdiv : p₁ ∣ p₂ * p₃ := ⟨p₄, by rw [hmuln, mul_comm]⟩
  rcases h1.dvd_mul.mp hdiv with hd | hd
  · exact absurd ((h2.dvd_iff_eq h1.ne_one).mp hd).symm h12
  · have hp13 : p₁ = p₃ := (h3.dvd_iff_eq h1.ne_one).mp hd |>.symm
    refine ⟨hp13, ?_⟩
    rw [hp13] at hmuln
    exact Nat.mul_right_cancel (Nat.pos_of_ne_zero h3.ne_zero) hmuln

/-- Two primes in `[P,2P]` can only have equal ratio if they are equal, when `X/L ≫ P²`. -/
lemma step_ratio_eq {P X L : ℝ} (hP : 0 < P) (hL : 0 < L) (hX : 0 < X)
    {p₁ p₂ p₃ p₄ : ℕ} {x₂ : ℝ} (hx2 : X / 10 ≤ x₂)
    (hr1 : P ≤ (p₁:ℝ)) (hr1' : (p₁:ℝ) ≤ 2*P) (hr3 : P ≤ (p₃:ℝ)) (hr3' : (p₃:ℝ) ≤ 2*P)
    (hbd : |(p₂:ℝ)/p₁ - (p₄:ℝ)/p₃| * x₂ ≤ 200 * L)
    (hbig : 8000 * P^2 < X / L) :
    (p₂:ℝ)/p₁ = (p₄:ℝ)/p₃ := by
  by_contra hne
  have hp1 : (0:ℝ) < p₁ := by linarith
  have hp3 : (0:ℝ) < p₃ := by linarith
  have hx2pos : 0 < x₂ := by linarith
  have hle : |(p₂:ℝ)/p₁ - (p₄:ℝ)/p₃| ≤ 2000 * L / X := by
    have h1' : |(p₂:ℝ)/p₁ - (p₄:ℝ)/p₃| ≤ 200 * L / x₂ := by
      rw [le_div_iff₀ hx2pos]; linarith
    have h2' : 200 * L / x₂ ≤ 200 * L / (X/10) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hx2
    have h3' : 200 * L / (X/10) = 2000 * L / X := by field_simp; ring
    linarith
  have hlow : (1 : ℝ) / (4 * P ^ 2) ≤ |(p₂:ℝ)/p₁ - (p₄:ℝ)/p₃| := by
    have hz : (p₂ : ℝ) * p₃ - (p₄ : ℝ) * p₁ ≠ 0 := by
      intro hz
      refine hne ((div_eq_div_iff (ne_of_gt hp1) (ne_of_gt hp3)).mpr ?_)
      linarith
    have hnum : (1:ℝ) ≤ |(p₂ : ℝ) * p₃ - (p₄ : ℝ) * p₁| := by
      have hne2 : p₂ * p₃ ≠ p₄ * p₁ := by
        intro hh
        apply hz
        have hcast : ((p₂ * p₃ : ℕ) : ℝ) = ((p₄ * p₁ : ℕ) : ℝ) := by rw [hh]
        push_cast at hcast ⊢
        linarith [hcast]
      have h := one_le_abs_cast_sub_nat hne2
      push_cast at h
      simpa using h
    have hden : (p₁ : ℝ) * p₃ ≤ 4 * P ^ 2 := by
      have h2 : (0:ℝ) ≤ p₃ := by positivity
      calc (p₁ : ℝ) * p₃ ≤ (2*P) * (2*P) := mul_le_mul hr1' hr3' h2 (by linarith)
        _ = 4 * P^2 := by ring
    have hdenpos : 0 < (p₁ : ℝ) * p₃ := by positivity
    have key : (p₂:ℝ)/p₁ - (p₄:ℝ)/p₃
        = ((p₂ : ℝ) * p₃ - (p₄ : ℝ) * p₁) / ((p₁ : ℝ) * p₃) := by
      field_simp
    rw [key, abs_div, abs_of_pos hdenpos]
    calc 1 / (4 * P ^ 2) ≤ 1 / ((p₁ : ℝ) * p₃) :=
          div_le_div_of_nonneg_left (by norm_num) hdenpos hden
      _ ≤ |(p₂ : ℝ) * p₃ - (p₄ : ℝ) * p₁| / ((p₁ : ℝ) * p₃) :=
          div_le_div_of_nonneg_right hnum hdenpos.le
  have hfin : (1:ℝ) / (4 * P ^ 2) ≤ 2000 * L / X := le_trans hlow hle
  have h1'' : X / (4 * P ^ 2) ≤ 2000 * L := by
    have h := (le_div_iff₀ hX).mp hfin
    have h' : X / (4 * P^2) = 1 / (4*P^2) * X := by ring
    rw [h']; exact h
  have h3'' : X / L ≤ 8000 * P ^ 2 := by
    rw [div_le_iff₀ hL]
    have h2'' : X ≤ 2000 * L * (4 * P^2) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * P ^ 2)] at h1''
      linarith [h1'']
    linarith [h2'']
  linarith [hbig, h3'']

/-- Distinct edges of `D` with the same ordered arc coincide (given `X/L ≫ P₁²`). -/
lemma edge_ext (D : QuadData k f c C X L P₁ P₂) (hP : 0 < P₁) (hL : 0 < L)
    (hbig : 8000 * P₁ ^ 2 < X / L) {e e' : Edge} (he : e ∈ D.edges) (he' : e' ∈ D.edges)
    (h1 : e.x₁ = e'.x₁) (h2 : e.x₂ = e'.x₂) : e = e' := by
  classical
  have hgem := D.geom e he
  have hgem' := D.geom e' he'
  have hx2mem : e.x₂ ∈ D.fam := hgem.x₂_mem
  have hx2 : X / 10 ≤ e.x₂ := (D.isFam.1 e.x₂ hx2mem).1
  have hX : 0 < X := by
    have h0 : 0 < 8000 * P₁ ^ 2 := by positivity
    have h1 : 0 < X / L := lt_of_lt_of_le h0 (le_of_lt hbig)
    exact (div_pos_iff_of_pos_right hL).mp h1
  have hb1 : |e.x₁ - ((e.p₂ : ℝ) / e.p₁) * e.x₂| ≤ 100 * L := hgem.geom
  have hb2 : |e'.x₁ - ((e'.p₂ : ℝ) / e'.p₁) * e'.x₂| ≤ 100 * L := hgem'.geom
  have hrat : (e.p₂ : ℝ) / e.p₁ = (e'.p₂ : ℝ) / e'.p₁ := by
    refine step_ratio_eq hP hL hX hx2 (hgem.prime_p₁).2.1 (hgem.prime_p₁).2.2
      (hgem'.prime_p₁).2.1 (hgem'.prime_p₁).2.2 ?_ hbig
    have hx2pos : 0 < e.x₂ := by linarith
    have hA : |e.x₁ - ((e'.p₂ : ℝ) / e'.p₁) * e.x₂| ≤ 100 * L := by
      rw [← h1, ← h2] at hb2; exact hb2
    have key : ((e.p₂ : ℝ) / e.p₁ - (e'.p₂ : ℝ) / e'.p₁) * e.x₂
        = (e.x₁ - ((e'.p₂ : ℝ) / e'.p₁) * e.x₂) - (e.x₁ - ((e.p₂ : ℝ) / e.p₁) * e.x₂) := by
      ring
    have h2' : |(e.x₁ - ((e'.p₂ : ℝ) / e'.p₁) * e.x₂) - (e.x₁ - ((e.p₂ : ℝ) / e.p₁) * e.x₂)|
        ≤ 200 * L := by
      have hAB := abs_sub_le (e.x₁ - ((e'.p₂ : ℝ) / e'.p₁) * e.x₂) (0:ℝ)
        (e.x₁ - ((e.p₂ : ℝ) / e.p₁) * e.x₂)
      have hAB' : |(e.x₁ - ((e'.p₂ : ℝ) / e'.p₁) * e.x₂) - (e.x₁ - ((e.p₂ : ℝ) / e.p₁) * e.x₂)|
          ≤ |e.x₁ - ((e'.p₂ : ℝ) / e'.p₁) * e.x₂| + |e.x₁ - ((e.p₂ : ℝ) / e.p₁) * e.x₂| := by
        rw [sub_zero] at hAB
        rw [show (0:ℝ) - (e.x₁ - ((e.p₂ : ℝ) / e.p₁) * e.x₂)
            = -(e.x₁ - ((e.p₂ : ℝ) / e.p₁) * e.x₂) by ring, abs_neg] at hAB
        exact hAB
      linarith [hAB', hA, hb1]
    calc |(e.p₂ : ℝ) / e.p₁ - (e'.p₂ : ℝ) / e'.p₁| * e.x₂
        = |((e.p₂ : ℝ) / e.p₁ - (e'.p₂ : ℝ) / e'.p₁) * e.x₂| := by
          rw [abs_mul, abs_of_pos hx2pos]
      _ = |(e.x₁ - ((e'.p₂ : ℝ) / e'.p₁) * e.x₂) - (e.x₁ - ((e.p₂ : ℝ) / e.p₁) * e.x₂)| := by
          rw [key]
      _ ≤ 200 * L := h2'
  have hfin := prime_ratio_inj (hgem.prime_p₁).1 (hgem.prime_p₂).1 (hgem'.prime_p₁).1
    hgem.p_ne hrat
  cases e; cases e'; simp_all

/-! ## Walks, closed walks and bicycles -/

/-- All walks of length `ℓ` in the `q`-subgraph. -/
noncomputable def walkSet (D : QuadData k f c C X L P₁ P₂) (q ℓ : ℕ) :
    Finset (Fin (ℓ + 1) → GVert D) :=
  (Finset.univ : Finset (Fin (ℓ + 1) → GVert D)).filter
    (fun W => ∀ j : Fin ℓ, GAdjQ D q (W j.castSucc) (W j.succ))

/-- Closed walks of length `ℓ` whose base point is the interval with left endpoint `x`. -/
noncomputable def closedWalkVal (D : QuadData k f c C X L P₁ P₂) (q ℓ : ℕ) (x : ℝ) :
    Finset (Fin (ℓ + 1) → GVert D) :=
  (walkSet D q ℓ).filter
    (fun W => W 0 = W ⟨ℓ, Nat.lt_succ_self ℓ⟩ ∧ (W 0).1 = x)

/-- A bicycle: an arc `e` of the `q`-subgraph with a closed walk through each endpoint.
It is a sigma type, so that its cardinality is the sum over the arcs of the products. -/
noncomputable def bikeSet (D : QuadData k f c C X L P₁ P₂) (q ℓ : ℕ) :
    Finset (Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) := by
  classical
  exact (D.edges.filter (fun e => q ∈ edgeS D e)).sigma (fun e =>
    (closedWalkVal D q ℓ e.x₁).product (closedWalkVal D q ℓ e.x₂))

/-- The number of bicycles is the sum over the arcs of the products of the numbers of closed
walks through the two endpoints. -/
lemma card_bikeSet (D : QuadData k f c C X L P₁ P₂) (q ℓ : ℕ) :
    (bikeSet D q ℓ).card =
      ∑ e ∈ D.edges.filter (fun e => q ∈ edgeS D e),
        (closedWalkVal D q ℓ e.x₁).card * (closedWalkVal D q ℓ e.x₂).card := by
  classical
  rw [bikeSet, Finset.card_sigma]
  exact Finset.sum_congr rfl (fun e _ => Finset.card_product ..)

/-- The bicycle over a fixed arc. -/
noncomputable def bikeFiber (D : QuadData k f c C X L P₁ P₂) (q ℓ : ℕ) (e : Edge) :
    Finset ((Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) :=
  (closedWalkVal D q ℓ e.x₁).product (closedWalkVal D q ℓ e.x₂)

lemma card_bikeFiber (D : QuadData k f c C X L P₁ P₂) (q ℓ : ℕ) (e : Edge) :
    (bikeFiber D q ℓ e).card =
      (closedWalkVal D q ℓ e.x₁).card * (closedWalkVal D q ℓ e.x₂).card :=
  Finset.card_product ..

/-- The product of the source primes around a walk. -/
noncomputable def walkProdV (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ)
    (W : Fin (ℓ + 1) → GVert D) : ℕ :=
  ∏ j : Fin ℓ, stepV D (W j.castSucc) (W j.succ)

/-- The product of the target primes around a walk. -/
noncomputable def walkProdU (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ)
    (W : Fin (ℓ + 1) → GVert D) : ℕ :=
  ∏ j : Fin ℓ, stepU D (W j.castSucc) (W j.succ)

/-- The primes common to all `2ℓ + 1` arcs of a bicycle. -/
noncomputable def bikePrimes (D : QuadData k f c C X L P₁ P₂) (q ℓ : ℕ)
    (t : Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) : Finset ℕ := by
  classical
  exact (primesIn (P₂ / 2) P₂).filter (fun p => p ∈ edgeS D t.1 ∧
    (∀ j : Fin ℓ, p ∈ stepS D (t.2.1 j.castSucc) (t.2.1 j.succ)) ∧
    (∀ j : Fin ℓ, p ∈ stepS D (t.2.2 j.castSucc) (t.2.2 j.succ)))

/-- A bicycle is degenerate if one of its two closed walks has nearly equal source- and
target-products (a near-degenerate cycle). -/
def degenerateAt (N c₅ P₁ : ℝ) (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ)
    (W : Fin (ℓ + 1) → GVert D) : Prop :=
  |((walkProdV D ℓ W : ℕ) : ℝ) - ((walkProdU D ℓ W : ℕ) : ℝ)| ≤ c₅ * P₁ ^ ℓ / N

/-- A bicycle is very good if the prime set common to all its arcs is large. -/
def veryGoodAt (D : QuadData k f c C X L P₁ P₂) (q ℓ : ℕ) (δ : ℝ)
    (t : Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) : Prop :=
  δ * pi0 P₂ < ((bikePrimes D q ℓ t).card : ℝ)

/-- A bicycle is bad if it is degenerate on one side, or not very good. -/
def badAt (N c₅ P₁ δ : ℝ) (D : QuadData k f c C X L P₁ P₂) (q ℓ : ℕ)
    (t : Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) : Prop :=
  degenerateAt N c₅ P₁ D ℓ t.2.1 ∨ degenerateAt N c₅ P₁ D ℓ t.2.2 ∨
    ¬ veryGoodAt D q ℓ δ t

end Work.BMF
