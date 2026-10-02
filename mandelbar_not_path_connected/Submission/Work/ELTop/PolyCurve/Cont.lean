/-
# Continuity and periodicity of the polygon parametrization

This module proves that the block maps `cycBlock D R k` are continuous on `[0,1]` (their
three pieces are the ray arc, the equipotential arc and the reversed ray arc, glued at
`σ = 1/3` and `σ = 2/3`), and that consequently the parametrization `cycParam D R` of the
whole polygon is continuous on `[0,1]` and invariant under `s ↦ s + 1`.
-/
import Mathlib
import Submission.Work.ELTop.PolyCurve.Defs
import Submission.Work.ELTop.PolyCurve.Blocks
import Submission.Work.ELTop.PolyCurve.rayArc_facts
import Submission.Work.ELTop.PolyCurve.eqArcPt_facts

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

variable {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}

/-- A ray point of angle `θ - 1` is the ray point of angle `θ`. -/
theorem rayPt_sub_one (hN : Work.EL.DynB c φ) (θ t : ℝ) :
    Work.EL.rayPt hN (θ - 1) t = Work.EL.rayPt hN θ t := by
  have h := Work.ELTop.rayPt_add_int hN (θ - 1) t 1
  simpa using h.symm

/-- An interval is the union of its two halves. -/
theorem Icc_split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    Set.Icc a b ∪ Set.Icc b c = Set.Icc a c := by
  ext x
  simp only [Set.mem_Icc, Set.mem_union]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, le_trans h2 hbc⟩
    · exact ⟨le_trans hab h1, h2⟩
  · intro hx
    rcases le_total x b with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2⟩

/-! ## Shifting the index of a block -/

/-- Shifting the index of a block by `m` lowers its external angle by `1` (and keeps the
potential level). -/
theorem CycLift.blkAng_sub_m (D : CycLift hN) (k : ℤ) (σ : ℝ) :
    blkAng D (k - (D.m : ℤ)) σ = blkAng D k σ - 1 := by
  have h1 : (k - (D.m : ℤ)) - 1 = (k - 1) - (D.m : ℤ) := by ring
  by_cases hle : σ ≤ 1 / 3
  · rw [blkAng_branch1 hle, blkAng_branch1 hle, D.A_sub_m]
  · by_cases hle2 : σ ≤ 2 / 3
    · rw [blkAng_branch2 hle hle2, blkAng_branch2 hle hle2, h1, D.A_sub_m, D.B_sub_m]
      ring
    · rw [blkAng_branch3 hle hle2, blkAng_branch3 hle hle2, h1, D.B_sub_m]

/-- A block starts at the landing point of its pair. -/
theorem CycLift.cycBlock_zero (D : CycLift hN) (R : ℝ) (k : ℤ) : cycBlock D R k 0 = D.Y k := by
  rw [cycBlock, if_pos (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  have h : 1 + 3 * 0 * (R - 1) = 1 := by ring
  rw [h, rayArc, if_pos rfl]

/-- A block ends at the landing point of the previous pair. -/
theorem CycLift.cycBlock_one (D : CycLift hN) (R : ℝ) (k : ℤ) : cycBlock D R k 1 = D.Y (k - 1) := by
  rw [cycBlock, if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 3),
    if_neg (by norm_num : ¬ (1 : ℝ) ≤ 2 / 3)]
  have h : 1 + (3 - 3 * (1 : ℝ)) * (R - 1) = 1 := by ring
  rw [h, rayArc, if_pos rfl]

/-- Shifting the index of a block by `m` does not change the block: the block map is periodic
of period `m` in the index, up to the trivial `1`-periodicity of the external angle. -/
theorem CycLift.cycBlock_sub_m (D : CycLift hN) {R : ℝ} (hR : 1 < R) (k : ℤ) {σ : ℝ}
    (hσ : σ ∈ Set.Icc 0 1) : cycBlock D R (k - (D.m : ℤ)) σ = cycBlock D R k σ := by
  rcases eq_or_lt_of_le hσ.2 with h1 | h1
  · subst h1
    rw [D.cycBlock_one R (k - (D.m : ℤ)), D.cycBlock_one R k,
      show k - (D.m : ℤ) - 1 = (k - 1) - (D.m : ℤ) from by ring, D.Y_sub_m (k - 1)]
  · have hσ' : σ ∈ Set.Ico 0 1 := ⟨hσ.1, h1⟩
    rw [cycBlock_eq_blk D hR hσ', cycBlock_eq_blk D hR hσ']
    by_cases h0 : σ = 0
    · rw [ite_eq_left h0, ite_eq_left h0, D.Y_sub_m k]
    · rw [ite_eq_right h0, ite_eq_right h0, D.blkAng_sub_m k σ, rayPt_sub_one hN]

/-! ## Continuity of a block -/

/-- The map `σ ↦ 1 + 3 σ (R-1)` sends `[0,1/3]` into `[1,R]`. -/
theorem mapsTo_lev1 {R : ℝ} (hR : 1 < R) :
    Set.MapsTo (fun σ : ℝ => 1 + 3 * σ * (R - 1)) (Set.Icc 0 (1 / 3)) (Set.Icc 1 R) := by
  intro σ hσ
  constructor
  · nlinarith [hσ.1]
  · nlinarith [hσ.2]

/-- The map `σ ↦ 1 + (3-3σ)(R-1)` sends `[2/3,1]` into `[1,R]`. -/
theorem mapsTo_lev3 {R : ℝ} (hR : 1 < R) :
    Set.MapsTo (fun σ : ℝ => 1 + (3 - 3 * σ) * (R - 1)) (Set.Icc (2 / 3) 1) (Set.Icc 1 R) := by
  intro σ hσ
  constructor
  · nlinarith [hσ.2]
  · nlinarith [hσ.1]

/-- Each block is continuous on `[0,1]`. -/
theorem CycLift.continuousOn_cycBlock (D : CycLift hN) {R : ℝ} (hR : 1 < R) (k : ℤ)
    (hA : Work.EL.LandsN hN (D.A k) (D.Y k))
    (hB : Work.EL.LandsN hN (D.B (k - 1)) (D.Y (k - 1))) :
    ContinuousOn (cycBlock D R k) (Set.Icc 0 1) := by
  set f1 : ℝ → ℂ := fun σ => rayArc hN (D.A k) (D.Y k) (1 + 3 * σ * (R - 1)) with hf1
  set f2 : ℝ → ℂ := fun σ => eqArcPt hN (D.A k) (D.B (k - 1)) R (3 * σ - 1) with hf2
  set f3 : ℝ → ℂ := fun σ => rayArc hN (D.B (k - 1)) (D.Y (k - 1))
    (1 + (3 - 3 * σ) * (R - 1)) with hf3
  have hcont1 : ContinuousOn f1 (Set.Icc 0 (1 / 3)) := by
    have hinner : ContinuousOn (fun σ : ℝ => 1 + 3 * σ * (R - 1)) (Set.Icc 0 (1 / 3)) := by
      fun_prop
    exact (PolyCurve.rayArc_facts hN hR hA).1.comp hinner (mapsTo_lev1 hR)
  have hcont2 : ContinuousOn f2 (Set.Icc (1 / 3) (2 / 3)) := by
    have hc : Continuous (eqArcPt hN (D.A k) (D.B (k - 1)) R) :=
      (PolyCurve.eqArcPt_facts hN hR (D.A k) (D.B (k - 1))).1
    have hinner : ContinuousOn (fun σ : ℝ => 3 * σ - 1) (Set.Icc (1 / 3) (2 / 3)) := by
      fun_prop
    have hcomp : ContinuousOn (fun σ : ℝ => eqArcPt hN (D.A k) (D.B (k - 1)) R (3 * σ - 1))
        (Set.Icc (1 / 3) (2 / 3)) := hc.comp_continuousOn hinner
    exact hcomp
  have hcont3 : ContinuousOn f3 (Set.Icc (2 / 3) 1) := by
    have hinner : ContinuousOn (fun σ : ℝ => 1 + (3 - 3 * σ) * (R - 1)) (Set.Icc (2 / 3) 1) := by
      fun_prop
    exact (PolyCurve.rayArc_facts hN hR hB).1.comp hinner (mapsTo_lev3 hR)
  have hagr1 : Set.EqOn (cycBlock D R k) f1 (Set.Icc 0 (1 / 3)) := by
    intro σ hσ
    simp only [hf1, cycBlock, if_pos hσ.2]
  have hagr2 : Set.EqOn (cycBlock D R k) f2 (Set.Icc (1 / 3) (2 / 3)) := by
    intro σ hσ
    by_cases hone : σ = 1 / 3
    · subst hone
      simp only [hf2, cycBlock, if_pos (le_refl (1 / 3 : ℝ)), rayArc, eqArcPt]
      have h3 : (1 : ℝ) + 3 * (1 / 3) * (R - 1) = R := by ring
      rw [h3, ite_eq_right (ne_of_gt hR)]
      congr 2
      ring
    · have h1 : ¬ σ ≤ 1 / 3 := by
        intro hle
        exact hone (le_antisymm hle hσ.1)
      simp only [hf2, cycBlock, if_neg h1, if_pos hσ.2]
  have hagr3 : Set.EqOn (cycBlock D R k) f3 (Set.Icc (2 / 3) 1) := by
    intro σ hσ
    by_cases hone : σ = 2 / 3
    · subst hone
      have h1 : ¬ (2 / 3 : ℝ) ≤ 1 / 3 := by norm_num
      simp only [hf3, cycBlock, if_neg h1, if_pos (le_refl (2 / 3 : ℝ)), rayArc, eqArcPt]
      have h3 : (1 : ℝ) + (3 - 3 * (2 / 3)) * (R - 1) = R := by ring
      rw [h3, ite_eq_right (ne_of_gt hR)]
      congr 2
      ring
    · have h1 : ¬ σ ≤ 1 / 3 := by linarith [hσ.1]
      have h2 : ¬ σ ≤ 2 / 3 := by
        intro hle
        exact hone (le_antisymm hle hσ.1)
      simp only [hf3, cycBlock, if_neg h1, if_neg h2]
  rw [show Set.Icc (0 : ℝ) 1
      = Set.Icc 0 (1 / 3) ∪ (Set.Icc (1 / 3) (2 / 3) ∪ Set.Icc (2 / 3) 1) from by
    rw [← Set.union_assoc,
      Icc_split (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) ≤ 2 / 3)]
    exact (Icc_split (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) ≤ 1)).symm]
  refine (continuousOn_union_iff_of_isClosed (s := Set.Icc 0 (1 / 3))
    (t := Set.Icc (1 / 3) (2 / 3) ∪ Set.Icc (2 / 3) 1) isClosed_Icc
    (isClosed_Icc.union isClosed_Icc)).mpr ⟨hcont1.congr hagr1, ?_⟩
  refine (continuousOn_union_iff_of_isClosed (s := Set.Icc (1 / 3) (2 / 3))
    (t := Set.Icc (2 / 3) 1) isClosed_Icc isClosed_Icc).mpr
    ⟨hcont2.congr hagr2, hcont3.congr hagr3⟩

/-! ## Continuity of the unrolled parametrization -/

/-- A function which is continuous on each of the unit intervals `[ℓ, ℓ+1]`, `ℓ < M`, is
continuous on `[0,M]`. -/
theorem continuousOn_Icc_of_unit_pieces {f : ℝ → ℂ} {M : ℕ} (hM : 0 < M)
    (h : ∀ ℓ : ℕ, ℓ < M → ContinuousOn f (Set.Icc (ℓ : ℝ) ((ℓ : ℝ) + 1))) :
    ContinuousOn f (Set.Icc 0 (M : ℝ)) := by
  have hcast : ∀ k : ℕ, (((k : ℕ) + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by
    intro k; push_cast; ring
  have hstep : ∀ n : ℕ, n < M → ContinuousOn f (Set.Icc 0 ((n : ℝ) + 1)) := by
    intro n hn
    induction n with
    | zero => simpa using h 0 hM
    | succ k ih =>
        have hk : k < M := by omega
        have ih' := ih hk
        have hl : ContinuousOn f (Set.Icc ((k : ℝ) + 1) (((k : ℝ) + 1) + 1)) := by
          have := h (k + 1) (by omega)
          simpa only [Nat.cast_add, Nat.cast_one] using this
        rw [hcast k,
          ← Icc_split (a := (0 : ℝ)) (b := (k : ℝ) + 1) (c := ((k : ℝ) + 1) + 1)
            (by positivity) (by linarith)]
        exact (continuousOn_union_iff_of_isClosed (s := Set.Icc 0 ((k : ℝ) + 1))
          (t := Set.Icc ((k : ℝ) + 1) (((k : ℝ) + 1) + 1)) isClosed_Icc isClosed_Icc).mpr
          ⟨ih', hl⟩
  have hfinal := hstep (M - 1) (by omega)
  rw [show (((M - 1 : ℕ) : ℝ) + 1) = (M : ℝ) from by
    have h1 : M - 1 + 1 = M := Nat.sub_add_cancel (by omega)
    rw [← h1]; push_cast; ring] at hfinal
  exact hfinal

/-- The "unrolled" parametrization `u ↦ cycBlock D R (-⌊u⌋) (u - ⌊u⌋)` is continuous on
`[0,m]`. -/
theorem CycLift.continuousOn_cycUnroll (D : CycLift hN) {R : ℝ} (hR : 1 < R)
    (hL : ∀ k : ℤ, Work.EL.LandsN hN (D.A k) (D.Y k) ∧ Work.EL.LandsN hN (D.B k) (D.Y k)) :
    ContinuousOn (fun u : ℝ => cycBlock D R (-⌊u⌋) (u - ⌊u⌋)) (Set.Icc 0 (D.m : ℝ)) := by
  refine continuousOn_Icc_of_unit_pieces D.hm ?_
  intro ℓ hℓ
  have hp : ContinuousOn (fun u : ℝ => cycBlock D R (-(ℓ : ℤ)) (u - (ℓ : ℝ)))
      (Set.Icc (ℓ : ℝ) ((ℓ : ℝ) + 1)) := by
    refine (D.continuousOn_cycBlock hR (-(ℓ : ℤ)) ?_ ?_).comp (by fun_prop) ?_
    · simpa using (hL (-(ℓ : ℤ))).1
    · simpa using (hL (-(ℓ : ℤ) - 1)).2
    · intro u hu
      rw [Set.mem_Icc] at hu ⊢
      constructor <;> linarith [hu.1, hu.2]
  refine hp.congr fun u hu => ?_
  dsimp only
  rw [Set.mem_Icc] at hu
  by_cases hend : u = (ℓ : ℝ) + 1
  · subst hend
    have hfloor : ⌊(ℓ : ℝ) + 1⌋ = (ℓ : ℤ) + 1 := by
      rw [show (1 : ℝ) = ((1 : ℤ) : ℝ) by norm_num, Int.floor_add_intCast, Int.floor_natCast]
    have h0 : (ℓ : ℝ) + 1 - ((((ℓ : ℤ) + 1 : ℤ)) : ℝ) = 0 := by push_cast; ring
    have h1 : (ℓ : ℝ) + 1 - (ℓ : ℝ) = 1 := by ring
    rw [hfloor, h0, h1, D.cycBlock_zero R (-((ℓ : ℤ) + 1)), D.cycBlock_one R (-(ℓ : ℤ))]
    congr 1
    ring
  · have hfloor : ⌊u⌋ = (ℓ : ℤ) := by
      rw [Int.floor_eq_iff]
      refine ⟨by exact_mod_cast hu.1, ?_⟩
      have hlt : u < (ℓ : ℝ) + 1 := lt_of_le_of_ne hu.2 hend
      exact_mod_cast hlt
    rw [hfloor]
    simp only [Int.cast_natCast]

/-- The parametrization is continuous on `[0,1]`, provided the rays of all the pairs land at
the points `Y`. -/
theorem CycLift.continuousOn_cycParam (D : CycLift hN) {R : ℝ} (hR : 1 < R)
    (hL : ∀ k : ℤ, Work.EL.LandsN hN (D.A k) (D.Y k) ∧ Work.EL.LandsN hN (D.B k) (D.Y k)) :
    ContinuousOn (cycParam D R) (Set.Icc 0 1) := by
  have h := D.continuousOn_cycUnroll (R := R) hR hL
  have hmaps : Set.MapsTo (fun s : ℝ => (D.m : ℝ) * s) (Set.Icc 0 1) (Set.Icc 0 (D.m : ℝ)) := by
    intro s hs
    rw [Set.mem_Icc] at hs ⊢
    constructor
    · have hmR : (0 : ℝ) ≤ (D.m : ℝ) := by positivity
      nlinarith [hs.1, hmR]
    · have hmR : (0 : ℝ) ≤ (D.m : ℝ) := by positivity
      nlinarith [hs.2, hmR]
  refine (h.comp (by fun_prop : ContinuousOn (fun s : ℝ => (D.m : ℝ) * s) (Set.Icc 0 1))
    hmaps).congr ?_
  intro s _
  rfl

/-- The parametrization is periodic with period `1`. -/
theorem CycLift.cycParam_add_one (D : CycLift hN) {R : ℝ} (hR : 1 < R) (s : ℝ) :
    cycParam D R (s + 1) = cycParam D R s := by
  have h1 : (D.m : ℝ) * (s + 1) = (D.m : ℝ) * s + (D.m : ℤ) := by push_cast; ring
  have hfr : (D.m : ℝ) * s - ⌊(D.m : ℝ) * s⌋ ∈ Set.Icc 0 1 := by
    constructor
    · have h := Int.fract_nonneg ((D.m : ℝ) * s)
      have h' := Int.fract_add_floor ((D.m : ℝ) * s)
      linarith
    · have h := Int.fract_lt_one ((D.m : ℝ) * s)
      have h' := Int.fract_add_floor ((D.m : ℝ) * s)
      linarith
  unfold cycParam
  rw [h1, Int.floor_add_intCast]
  rw [show (D.m : ℝ) * s + ((D.m : ℤ) : ℝ) - (((⌊(D.m : ℝ) * s⌋ + (D.m : ℤ)) : ℤ) : ℝ)
      = (D.m : ℝ) * s - ((⌊(D.m : ℝ) * s⌋ : ℤ) : ℝ) from by push_cast; ring]
  rw [show -(⌊(D.m : ℝ) * s⌋ + (D.m : ℤ)) = -⌊(D.m : ℝ) * s⌋ - (D.m : ℤ) from by ring]
  exact D.cycBlock_sub_m hR (-⌊(D.m : ℝ) * s⌋) hfr

end Work.ELTop
