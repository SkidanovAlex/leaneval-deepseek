import Mathlib
import Submission.Work.SeedSimple2.Defs
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.paramRay_subset_pairSideNear

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedSimple2.Unlinked

variable {c : ℂ} {φ : ℂ → ℂ}

/-! ## 1. Angle arithmetic

The predicate `Work.EL.InArc x a b` describes the open counterclockwise arc from `a` to `b`.
For angles which are not congruent modulo `ℤ` to either endpoint, membership in the arc is
decided by comparing the two fractional parts `fract (x - a)` and `fract (x - b)`; in
particular, when the arc `(a, b)` is nondegenerate, "not in the arc `(a, b)`" is the same as
"in the complementary arc `(b, a + 1)`". -/

/-- If `x` is congruent to `a` modulo `ℤ` then `Int.fract (x - a) = 0`, so distinctness modulo
`ℤ` gives `Int.fract (x - a) ≠ 0`. -/
theorem fract_sub_ne_zero_of_ne {x a : ℝ} (h : ∀ k : ℤ, x ≠ a + (k : ℝ)) :
    Int.fract (x - a) ≠ 0 := by
  intro h0
  obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp h0
  exact h z (by linarith [hz])

/-- **The angle criterion for an arc.**  If `x` is not congruent to `a` modulo `ℤ`, then `x`
lies in the open arc `(a, b)` exactly when the fractional part of `x - a` is smaller than that
of `x - b`: walking counterclockwise from `a` one meets `x` no later than `b`. -/
theorem InArc_iff_fract_lt {x a b : ℝ} (hxa : Int.fract (x - a) ≠ 0) :
    Work.EL.InArc x a b ↔ Int.fract (x - a) < Int.fract (x - b) := by
  have hp0 : 0 < Int.fract (x - a) :=
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hxa)
  have hp1 : Int.fract (x - a) < 1 := Int.fract_lt_one _
  have hq0 : 0 ≤ Int.fract (x - b) := Int.fract_nonneg _
  have hq1 : Int.fract (x - b) < 1 := Int.fract_lt_one _
  have hfr : Work.EL.arcLen a b
      = Int.fract (Int.fract (x - a) - Int.fract (x - b)) := by
    have h1 : b - a = (Int.fract (x - a) - Int.fract (x - b))
        + (((⌊x - a⌋ - ⌊x - b⌋ : ℤ)) : ℝ) := by
      have ha := Int.fract_add_floor (x - a)
      have hb := Int.fract_add_floor (x - b)
      push_cast
      linarith
    rw [Work.EL.arcLen, h1, Int.fract_add_intCast]
  rw [Work.EL.InArc, hfr]
  constructor
  · intro h
    rcases lt_trichotomy (Int.fract (x - a)) (Int.fract (x - b)) with hlt | heq | hgt
    · exact hlt
    · exfalso
      have h0 : Int.fract (Int.fract (x - a) - Int.fract (x - b)) = 0 := by
        rw [heq, sub_self, Int.fract_zero]
      linarith [h.1, h.2, h0]
    · exfalso
      have h0 : Int.fract (Int.fract (x - a) - Int.fract (x - b))
          = Int.fract (x - a) - Int.fract (x - b) :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      rw [h0] at h
      linarith [h.2]
  · intro hlt
    refine ⟨hp0, ?_⟩
    have h0 : Int.fract (Int.fract (x - a) - Int.fract (x - b))
        = Int.fract (x - a) - Int.fract (x - b) + 1 := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
    rw [h0]
    linarith

/-- **The complementary arc.**  If `x` is congruent modulo `ℤ` to neither endpoint of a
nondegenerate arc, then `x` fails to lie in the open arc `(a, b)` exactly when it lies in the
complementary open arc `(b, a + 1)`. -/
theorem not_InArc_iff_InArc_near {x a b : ℝ} (hnd : Work.EL.arcLen a b ≠ 0)
    (hxa : Int.fract (x - a) ≠ 0) (hxb : Int.fract (x - b) ≠ 0) :
    ¬ Work.EL.InArc x a b ↔ Work.EL.InArc x b (a + 1) := by
  have hswap : ¬ Work.EL.InArc x a b ↔ Work.EL.InArc x b a := by
    rw [InArc_iff_fract_lt (x := x) (a := a) (b := b) hxa,
      InArc_iff_fract_lt (x := x) (a := b) (b := a) hxb]
    constructor
    · intro h
      have hle : Int.fract (x - b) ≤ Int.fract (x - a) := le_of_not_gt h
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · exfalso
        apply hnd
        rw [Work.EL.arcLen]
        have h1 : b - a = (Int.fract (x - a) - Int.fract (x - b))
            + (((⌊x - a⌋ - ⌊x - b⌋ : ℤ)) : ℝ) := by
          have hb := Int.fract_add_floor (x - b)
          have ha := Int.fract_add_floor (x - a)
          push_cast
          linarith
        rw [h1, Int.fract_add_intCast, heq, sub_self, Int.fract_zero]
    · intro h hc
      linarith
  rw [hswap]
  have harc : Work.EL.InArc x b (a + 1) ↔ Work.EL.InArc x b a := by
    simp only [Work.EL.InArc, Work.ELTop.arcLen_add_one_at]
  exact harc.symm

/-- Distinctness of the fractional parts of `a` and `b` makes the arc `(a, b)`
nondegenerate. -/
theorem arcLen_ne_zero_of_fract_ne {a b : ℝ} (h : Int.fract a ≠ Int.fract b) :
    Work.EL.arcLen a b ≠ 0 := by
  intro h0
  have h1 : b - a = (Int.fract b - Int.fract a) + ((⌊b⌋ - ⌊a⌋ : ℤ) : ℝ) := by
    have hb := Int.fract_add_floor b
    have ha := Int.fract_add_floor a
    push_cast
    linarith
  rw [Work.EL.arcLen, h1, Int.fract_add_intCast] at h0
  obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp h0
  have hz1 : (z : ℝ) < 1 := by linarith [hz, Int.fract_lt_one b, Int.fract_nonneg a]
  have hz2 : (-1 : ℝ) < (z : ℝ) := by linarith [hz, Int.fract_lt_one a, Int.fract_nonneg b]
  have hz3 : z < (1 : ℤ) := by exact_mod_cast hz1
  have hz4 : (-1 : ℤ) < z := by exact_mod_cast hz2
  have hz0 : z = 0 := by omega
  rw [hz0] at hz
  simp only [Int.cast_zero] at hz
  exact h (by linarith [hz])

/-! ## 2. Plane topology of the two sides of a co-landing pair -/

/-- The landing point of a ray is a limit point of the ray. -/
theorem mem_closure_paramRay_of_landsN (hN : Work.EL.DynB c φ) {θ : ℝ} {y : ℂ}
    (h : Work.EL.LandsN hN θ y) : y ∈ closure (Work.EL.paramRay hN θ) :=
  mem_closure_of_tendsto h (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Work.EL.rayPt_mem_paramRay hN ht)

/-- The pair curve of a co-landing pair meets the filled Julia set only in the landing point:
the rays avoid `K c` and the landing point lies in it. -/
theorem pairCurve_inter_K_subset (hN : Work.EL.DynB c φ) (P : Work.EL.CoPair hN) :
    Work.EL.pairCurve P ∩ Work.EL.K c ⊆ {P.y} := by
  intro z hz
  obtain ⟨hzC, hzK⟩ := hz
  rw [Work.EL.mem_pairCurve_iff] at hzC
  rcases hzC with h | h | h
  · exact absurd hzK (Work.EL.paramRay_subset_compl hN P.a h)
  · exact Set.mem_singleton_iff.mpr h
  · exact absurd hzK (Work.EL.paramRay_subset_compl hN P.b h)

/-- **The closures of the two sides meet exactly in the pair curve.**  Both sides are open
components of the complement of the pair curve and have the pair curve as frontier; two disjoint
open sets with the same frontier have closures meeting precisely in that frontier. -/
theorem closure_inter_pairSides (hN : Work.EL.DynB c φ) (hJ : Work.Top.JordanForm)
    (P : Work.EL.CoPair hN) (hnd : Work.EL.arcLen P.a P.b ≠ 0) :
    closure (Work.EL.pairSide P) ∩ closure (Work.EL.pairSideNear P) = Work.EL.pairCurve P := by
  obtain ⟨-, hdisj, hfrA, hfrB⟩ := Work.ELTop.pairSides_decomposition hN hJ P hnd
  have hAopen : IsOpen (Work.EL.pairSide P) :=
    IsOpen.connectedComponentIn (Work.ELTop.isClosed_pairCurve hN P).isOpen_compl
  have hBopen : IsOpen (Work.EL.pairSideNear P) :=
    IsOpen.connectedComponentIn (Work.ELTop.isClosed_pairCurve hN P).isOpen_compl
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨hzA, hzB⟩ := hz
    by_contra hzc
    have hzA' : z ∈ Work.EL.pairSide P := by
      by_contra h
      exact hzc (by rw [← hfrA, hAopen.frontier_eq]; exact ⟨hzA, h⟩)
    have hzB' : z ∈ Work.EL.pairSideNear P := by
      by_contra h
      exact hzc (by rw [← hfrB, hBopen.frontier_eq]; exact ⟨hzB, h⟩)
    exact Set.disjoint_left.mp hdisj hzA' hzB'
  · intro z hz
    have hzA : z ∈ frontier (Work.EL.pairSide P) := by rwa [hfrA]
    have hzB : z ∈ frontier (Work.EL.pairSideNear P) := by rwa [hfrB]
    exact ⟨frontier_subset_closure hzA, frontier_subset_closure hzB⟩

/-- **A ray of the far arc and a ray of the near arc cannot end at a common point.**  If the
ray of angle `θ₁` lies in the far arc of `P` and the ray of angle `θ₂` in the near arc, and
both rays land at the same point `y ≠ P.y`, we reach a contradiction: `y` would be a limit point
of both sides, hence lie on the pair curve, but the pair curve meets `K c` — where `y` lies —
only in `P.y`. -/
theorem false_of_farArc_nearArc (hN : Work.EL.DynB c φ) (hJ : Work.Top.JordanForm)
    (P : Work.EL.CoPair hN) (hnd : Work.EL.arcLen P.a P.b ≠ 0)
    {θ₁ θ₂ : ℝ} {y : ℂ} (h1 : Work.EL.LandsN hN θ₁ y) (h2 : Work.EL.LandsN hN θ₂ y)
    (hne : y ≠ P.y) (hfar : Work.EL.InArc θ₁ P.a P.b)
    (hnear : Work.EL.InArc θ₂ P.b (P.a + 1)) : False := by
  have hA : Work.EL.paramRay hN θ₁ ⊆ Work.EL.pairSide P :=
    Work.ELTop.paramRay_subset_pairSide hN hJ P hfar
  have hB : Work.EL.paramRay hN θ₂ ⊆ Work.EL.pairSideNear P :=
    Work.ELTop.paramRay_subset_pairSideNear hN hJ P hnear
  have hyA : y ∈ closure (Work.EL.pairSide P) :=
    closure_mono hA (mem_closure_paramRay_of_landsN hN h1)
  have hyB : y ∈ closure (Work.EL.pairSideNear P) :=
    closure_mono hB (mem_closure_paramRay_of_landsN hN h2)
  have hyC : y ∈ Work.EL.pairCurve P := by
    rw [← closure_inter_pairSides hN hJ P hnd]
    exact ⟨hyA, hyB⟩
  have hyK : y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN h1
  have hy := pairCurve_inter_K_subset hN P ⟨hyC, hyK⟩
  exact hne (Set.mem_singleton_iff.mp hy)

/-- **The unlinkedness step `U`.**  If the pairs `(θ₁, θ₂)` and `(P.a, P.b)` both co-land, at
distinct points, and the angles `θ₁`, `θ₂` are congruent modulo `ℤ` to neither `P.a` nor `P.b`,
then `θ₁` and `θ₂` lie in the same one of the two arcs of `(P.a, P.b)`. -/
theorem InArc_iff_of_coLands (hN : Work.EL.DynB c φ) (hJ : Work.Top.JordanForm)
    (P : Work.EL.CoPair hN) (hnd : Work.EL.arcLen P.a P.b ≠ 0)
    {θ₁ θ₂ : ℝ} {y : ℂ} (h1 : Work.EL.LandsN hN θ₁ y) (h2 : Work.EL.LandsN hN θ₂ y)
    (hne : y ≠ P.y)
    (hθ₁a : ∀ k : ℤ, θ₁ ≠ P.a + (k : ℝ)) (hθ₁b : ∀ k : ℤ, θ₁ ≠ P.b + (k : ℝ))
    (hθ₂a : ∀ k : ℤ, θ₂ ≠ P.a + (k : ℝ)) (hθ₂b : ∀ k : ℤ, θ₂ ≠ P.b + (k : ℝ)) :
    (Work.EL.InArc θ₁ P.a P.b ↔ Work.EL.InArc θ₂ P.a P.b) := by
  constructor
  · intro hfar
    by_contra hcon
    refine false_of_farArc_nearArc hN hJ P hnd h1 h2 hne hfar ?_
    exact (not_InArc_iff_InArc_near hnd (fract_sub_ne_zero_of_ne hθ₂a)
      (fract_sub_ne_zero_of_ne hθ₂b)).mp hcon
  · intro hfar
    by_contra hcon
    exact false_of_farArc_nearArc hN hJ P hnd h2 h1 hne hfar
      ((not_InArc_iff_InArc_near hnd (fract_sub_ne_zero_of_ne hθ₁a)
        (fract_sub_ne_zero_of_ne hθ₁b)).mp hcon)

/-! ## 3. The unlinked lemma -/

theorem unlinked_of_coLands {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (hJ : Work.Top.JordanForm)
    {a b a' b' : ℝ} {w w' : ℂ} (hne : w ≠ w')
    (ha : a ∈ Set.Ico 0 1) (hb : b ∈ Set.Ico 0 1) (ha' : a' ∈ Set.Ico 0 1)
    (hb' : b' ∈ Set.Ico 0 1)
    (h1 : Work.EL.LandsN hN a w) (h2 : Work.EL.LandsN hN b w)
    (h3 : Work.EL.LandsN hN a' w') (h4 : Work.EL.LandsN hN b' w')
    (hd : Work.SeedSimple2.PairwiseDistinct4 a b a' b') :
    Work.ELPull.Unlinked a b a' b' := by
  obtain ⟨hab, haa', hab', hba', hbb', ha'b'⟩ := hd
  let P : Work.EL.CoPair hN := { toRawPair := ⟨a, b, w⟩, lands_a := h1, lands_b := h2 }
  let P' : Work.EL.CoPair hN := { toRawPair := ⟨a', b', w'⟩, lands_a := h3, lands_b := h4 }
  have hndP : Work.EL.arcLen P.a P.b ≠ 0 := arcLen_ne_zero_of_fract_ne hab
  have hndP' : Work.EL.arcLen P'.a P'.b ≠ 0 := arcLen_ne_zero_of_fract_ne ha'b'
  have key1 : Work.EL.InArc a' P.a P.b ↔ Work.EL.InArc b' P.a P.b :=
    InArc_iff_of_coLands hN hJ P hndP h3 h4 (Ne.symm hne)
      (fun k hk => haa' (by rw [hk, Int.fract_add_intCast]))
      (fun k hk => hba' (by rw [hk, Int.fract_add_intCast]))
      (fun k hk => hab' (by rw [hk, Int.fract_add_intCast]))
      (fun k hk => hbb' (by rw [hk, Int.fract_add_intCast]))
  have key2 : Work.EL.InArc a P'.a P'.b ↔ Work.EL.InArc b P'.a P'.b :=
    InArc_iff_of_coLands hN hJ P' hndP' h1 h2 hne
      (fun k hk => haa' (by rw [hk, Int.fract_add_intCast]))
      (fun k hk => hab' (by rw [hk, Int.fract_add_intCast]))
      (fun k hk => hba' (by rw [hk, Int.fract_add_intCast]))
      (fun k hk => hbb' (by rw [hk, Int.fract_add_intCast]))
  exact ⟨key1, key2⟩

end Work.SeedSimple2.Unlinked
