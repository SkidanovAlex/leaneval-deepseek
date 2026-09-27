import Mathlib
import Submission.Work.Mostow.ellipticGapAux
import Submission.Work.Mostow.stabFlatActionCanon
import Submission.Work.Mostow.zassenhausNilpotent
import Submission.Work.Mostow.nilp_torsionGen_finite
import Submission.Work.Mostow.boundedTorsionAux
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.cuspZ2Defs

/-!
# Vocabulary for `Work.Mostow.cuspEllipticGap`

The target `Work.Mostow.cuspEllipticGap` is the "elliptic gap" of the cusp stabiliser of a
lattice `Γ ≤ PO n 1` at a parabolic fixed point `ξ`: the linear parts `flatLin ξ (Λσ)` of the
elliptic elements `σ ∈ Γ_ξ` are bounded away from the identity, as linear maps of `ξ^⊥`.

This file fixes the vocabulary of the argument (definitions only) plus two elementary lemmas
that all the later pieces use:

* `cegUnit ξ` — the unit vectors of `ξ^⊥`;
* `cegRot ξ σ` — the rotation displacement `sup ‖flatLin ξ (Λσ) y − y‖` over `cegUnit ξ`;
* `cegSmall ξ θ σ` — the statement that `σ` rotates `ξ^⊥` by at most `θ`;
* `cegBad Γ ξ θ` — the set of *small-rotation elliptic* elements of the stabiliser `Γ_ξ`.
* `cegIsOfFinOrder` — an elliptic element of a discrete subgroup has finite order;
* `cegStabFinite` — the setwise stabiliser of a point in a discrete subgroup is finite.

The plan of the proof of the target is:

1. `cegRotSpec`: `cegRot ξ σ` is an upper bound for `‖flatLin ξ (Λσ) y − y‖` for every
   `y ∈ ξ^⊥`, and every `θ ≤ cegRot ξ σ` is realised by a unit vector of `ξ^⊥`.
2. `cegDeepPoint`: there is `θ₀ > 0` such that every *finite* set `S` of `θ₀`-small
   `ξ`-stabilising elements of `Γ` is `NearIdAt z η` for a suitable point `z` of `ℍⁿ`.
3. `cegBadFinite`: `cegBad Γ ξ θ₀` is finite (Zassenhaus' theorem + a descending-chain
   argument on the fixed subspaces in the hyperboloid model).
4. Assembly: `cegBad` is finite, so `min (θ₀) (min_{σ ∈ cegBad} cegRot ξ σ)` is positive; every
   small-rotation elliptic is in `cegBad`, and every other elliptic fixing `ξ` has rotation
   displacement `> θ₀`, so this `θ` is the required gap.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The unit vectors of the flat space `ξ^⊥` of the boundary point `ξ`. -/
def cegUnit (ξ : E n) : Set (E n) := {y | inner ℝ y ξ = 0 ∧ ‖y‖ = 1}

/-- The **rotation displacement** of `σ` at `ξ`: the supremum of `‖flatLin ξ (Λσ) y − y‖` over
the unit vectors `y ⊥ ξ`. -/
def cegRot (ξ : E n) (σ : PO n 1) : ℝ :=
  sSup ((fun y : E n => ‖flatLin ξ (LambdaMat σ) y - y‖) '' cegUnit ξ)

/-- `σ` rotates the flat space `ξ^⊥` by at most `θ`. -/
def cegSmall (ξ : E n) (θ : ℝ) (σ : PO n 1) : Prop :=
  ∀ y : E n, inner ℝ y ξ = 0 → ‖flatLin ξ (LambdaMat σ) y - y‖ ≤ θ * ‖y‖

/-- The **small-rotation elliptic elements** of the stabiliser `Γ_ξ`: the non-trivial elements of
`Γ` fixing `ξ` which have a fixed point in `ℍⁿ` and whose flat rotation is `cegSmall`. -/
def cegBad (Γ : Subgroup (PO n 1)) (ξ : E n) (θ : ℝ) : Set Γ :=
  {σ | bd (σ : PO n 1) ξ = ξ ∧ σ ≠ 1 ∧ (∃ p : E n, (σ : PO n 1) • p = p) ∧
    cegSmall ξ θ (σ : PO n 1)}

lemma mem_cegBad {Γ : Subgroup (PO n 1)} {ξ : E n} {θ : ℝ} {σ : Γ} :
    σ ∈ cegBad Γ ξ θ ↔ bd (σ : PO n 1) ξ = ξ ∧ σ ≠ 1 ∧
      (∃ p : E n, (σ : PO n 1) • p = p) ∧ cegSmall ξ θ (σ : PO n 1) := Iff.rfl

/-! ## Elementary consequences of discreteness -/

/-- An **elliptic** element `σ` of a discrete subgroup `Γ ≤ PO n 1` (one with a fixed point in
`ℍⁿ`) has finite order: the powers of `σ` displace `0` by at most `2 hdist 0 p`. -/
theorem cegIsOfFinOrder {Γ : Subgroup (PO n 1)} (hA : POActionProp n) (hI : HypIsometryProp n)
    (hdisc : IsDiscrete (SetLike.coe Γ)) (σ : Γ)
    (hell : ∃ p : E n, (σ : PO n 1) • p = p) : IsOfFinOrder σ := by
  obtain ⟨p, hp⟩ := hell
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have hAb : POBasic n := POBasic.ofProp hA
  -- every `ℕ`-power of `σ` fixes `p`
  have hfix : ∀ k : ℕ, ((σ ^ k : Γ) : PO n 1) • p = p := by
    intro k
    induction k with
    | zero => simpa using hAb.one_smul p
    | succ k ih =>
        have hcoe : ((σ ^ (k + 1) : Γ) : PO n 1)
            = ((σ ^ k : Γ) : PO n 1) * (σ : PO n 1) := by
          rw [pow_succ]; rfl
        rw [hcoe, hAb.mul_smul, hp, ih]
  -- the displacement of `0` stays bounded
  have hbdd : ∀ k : ℕ, hdist (0 : E n) (((σ ^ k : Γ) : PO n 1) • (0 : E n))
      ≤ 2 * hdist (0 : E n) p := by
    intro k
    have htri1 := hId.triangle (0 : E n) p (((σ ^ k : Γ) : PO n 1) • (0 : E n))
    have htri2 := hId.triangle p (((σ ^ k : Γ) : PO n 1) • p)
      (((σ ^ k : Γ) : PO n 1) • (0 : E n))
    have hiso : hdist (((σ ^ k : Γ) : PO n 1) • p) (((σ ^ k : Γ) : PO n 1) • (0 : E n))
        = hdist p (0 : E n) := hId.isom_smul _ _ _
    have hzero : hdist p (((σ ^ k : Γ) : PO n 1) • p) = 0 :=
      (hId.eq_zero _ _).mpr (hfix k).symm
    rw [hiso, hzero, zero_add] at htri2
    calc hdist (0 : E n) (((σ ^ k : Γ) : PO n 1) • (0 : E n))
        ≤ hdist (0 : E n) p + hdist p (((σ ^ k : Γ) : PO n 1) • (0 : E n)) := htri1
      _ ≤ hdist (0 : E n) p + hdist p (0 : E n) := by linarith
      _ = 2 * hdist (0 : E n) p := by rw [hId.symm p (0 : E n)]; ring
  -- finitely many powers
  have hfin : {γ : Γ | hdist (0 : E n) ((γ : Γ) • (0 : E n)) ≤ 2 * hdist (0 : E n) p}.Finite :=
    finite_nearStab hAb hId hdisc _
  have hrange : (Set.range (fun k : ℕ => σ ^ k)).Finite :=
    hfin.subset (fun x hx => by
      obtain ⟨k, rfl⟩ := hx
      exact hbdd k)
  rw [isOfFinOrder_iff_pow_eq_one]
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun k : ℕ => σ ^ k) := by
    intro a b hab
    have hab' : σ ^ a = σ ^ b := hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hd : 0 < b - a := Nat.sub_pos_of_lt h
      have : σ ^ (b - a) = 1 := by
        have h1 : σ ^ b = σ ^ a * σ ^ (b - a) := by
          rw [← pow_add]; congr 1; omega
        rw [← hab'] at h1
        exact mul_left_cancel (a := σ ^ a) (by simpa using h1.symm)
      exact hcon (b - a) hd this
    · have hd : 0 < a - b := Nat.sub_pos_of_lt h
      have : σ ^ (a - b) = 1 := by
        have h1 : σ ^ a = σ ^ b * σ ^ (a - b) := by
          rw [← pow_add]; congr 1; omega
        rw [← hab'] at h1
        exact mul_left_cancel (a := σ ^ b) (by simpa using h1.symm)
      exact hcon (a - b) hd this
  exact Set.infinite_range_of_injective hinj hrange

/-- The setwise stabiliser of a point `p` in a discrete subgroup `Γ ≤ PO n 1` is finite. -/
theorem cegStabFinite {Γ : Subgroup (PO n 1)} (hA : POActionProp n) (hI : HypIsometryProp n)
    (hdisc : IsDiscrete (SetLike.coe Γ)) (p : E n) :
    {γ : Γ | (γ : PO n 1) • p = p}.Finite := by
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have hAb : POBasic n := POBasic.ofProp hA
  refine (finite_nearStab hAb hId hdisc (2 * hdist (0 : E n) p)).subset ?_
  intro γ hγ
  have htri1 := hId.triangle (0 : E n) p ((γ : PO n 1) • (0 : E n))
  have htri2 := hId.triangle p ((γ : PO n 1) • p) ((γ : PO n 1) • (0 : E n))
  have hiso : hdist ((γ : PO n 1) • p) ((γ : PO n 1) • (0 : E n)) = hdist p (0 : E n) :=
    hId.isom_smul _ _ _
  have hzero : hdist p ((γ : PO n 1) • p) = 0 := (hId.eq_zero _ _).mpr hγ.symm
  rw [hiso, hzero, zero_add] at htri2
  calc hdist (0 : E n) ((γ : PO n 1) • (0 : E n))
      ≤ hdist (0 : E n) p + hdist p ((γ : PO n 1) • (0 : E n)) := htri1
    _ ≤ hdist (0 : E n) p + hdist p (0 : E n) := by linarith
    _ = 2 * hdist (0 : E n) p := by rw [hId.symm p (0 : E n)]; ring

end

end Work.Mostow
