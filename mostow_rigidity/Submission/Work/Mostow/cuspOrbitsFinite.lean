import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.horoballOverlapCriterion
import Submission.Work.Mostow.BaryContinuity
import Submission.Work.Mostow.hrayOutsideHoroballs
import Submission.Work.Mostow.horoballLevelSeparation
import Submission.Work.Mostow.separatedFinite

/-!
# Finitely many orbits of a horoball packing (`Work.Mostow.cuspOrbitsFinite`)

Let `Γ ≤ PO n 1`, let `P ⊆ Sph n` be a `Γ`-invariant set of boundary points with a `Γ`-equivariant
height function `ht`, and suppose

* the horoballs `horoball ξ (ht ξ)`, `ξ ∈ P`, are pairwise disjoint, and
* the complement of their union is `Γ`-cocompact: there is a compact `K` such that every point
  lying outside all the horoballs is moved into `K` by some element of `Γ`.

Then `P` is covered by finitely many `Γ`-orbits.

## The argument

All the analytic input is in three auxiliary lemmas proved in this workspace:

* `Work.Mostow.hrayOutsideHoroballs`: for `ξ ∈ P` the point `hray ξ (-(ht ξ)) = sinh (-(ht ξ)) • ξ`
  has Busemann level exactly `ht ξ` at `ξ`, hence lies on the boundary horosphere
  `∂ horoball ξ (ht ξ)`; that point is outside *every* horoball of the family (disjointness plus the
  overlap criterion and the sharp Minkowski inequality for a point of the boundary horosphere).
* `Work.Mostow.horoballLevelSeparation`: two distinct horoballs with levels bounded by `R` have base
  points at distance at least `2 * exp (-R)` (again the overlap criterion, plus `Sph n ⊆ ‖·‖ = 1`).
* `Work.Mostow.separatedFinite`: a separated subset of a compact set is finite.

* *Level bound.*  Cocompactness puts some `Γ`-translate of `hray ξ (-(ht ξ))` into `K`; equivariance
  of `ht` shows that its Busemann level at `bd γ ξ` is `ht (bd γ ξ)`, so `|ht (bd γ ξ)| ≤ R` for any
  `R` bounding `hdist 0` on `K`.  Hence **every** orbit of `P` meets `A := {ξ ∈ P | |ht ξ| ≤ R}`.
* *`A` is finite.*  By `horoballLevelSeparation` it is separated by `δ = 2 * exp (-R)` inside the
  compact sphere `Sph n`, so `separatedFinite` finishes.
* Enumerating `A` by a finite list gives the claim: the inverse of the element of `Γ` bringing an
  arbitrary `ξ ∈ P` into `A` provides the required element of `Γ`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-- The Busemann function along the geodesic ray towards `ξ`: `β_ξ (sinh s • ξ) = -s`. -/
lemma busemann_hray (ξ : E n) (hξ : ξ ∈ Sph n) (s : ℝ) :
    busemann ξ (hray ξ s) = -s := by
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  rw [busemann_eq_log, hray]
  rw [show tpart (Real.sinh s • ξ) = Real.cosh s from ?_]
  · rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hξn]
    simp only [one_pow, mul_one, Real.cosh_sub_sinh, Real.log_exp]
  · rw [tpart, norm_smul, Real.norm_eq_abs, hξn, mul_one, sq_abs, ← Real.cosh_sq']
    exact Real.sqrt_sq (le_of_lt (Real.cosh_pos s))

theorem cuspOrbitsFinite (n : ℕ) (hA : Work.Mostow.POBasic n) (hI : Work.Mostow.HypIsoData n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    {P : Set (Submission.Mostow.E n)} {ht : Submission.Mostow.E n → ℝ}
    (hPsub : P ⊆ Submission.Mostow.Sph n)
    (heq : Work.Mostow.IsEquivHeight Γ P ht)
    (hPinv : ∀ (γ : Γ) (ξ : Submission.Mostow.E n), ξ ∈ P →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ ∈ P)
    (hdisj : P.Pairwise (fun ξ η => Disjoint (Submission.Mostow.horoball ξ (ht ξ))
      (Submission.Mostow.horoball η (ht η))))
    (hK : ∃ K : Set (Submission.Mostow.E n), IsCompact K ∧ ∀ u : Submission.Mostow.E n,
      (∀ ξ ∈ P, u ∉ Submission.Mostow.horoball ξ (ht ξ)) →
        ∃ γ : Γ, (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u ∈ K) :
    ∃ (m : ℕ) (ξs : Fin m → Submission.Mostow.E n), (∀ i, ξs i ∈ P) ∧
      ∀ ξ ∈ P, ∃ (i : Fin m) (γ : Γ),
        Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) (ξs i) = ξ := by
  obtain ⟨K, hKc, hK⟩ := hK
  -- a radius `R` bounding `hdist 0` on the compact set `K`
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ w ∈ K, hdist 0 w ≤ R := by
    have hcont : Continuous (fun w : E n => hdist (0 : E n) w) := continuous_hdist_zero
    have hcomp : IsCompact ((fun w : E n => hdist (0 : E n) w) '' K) := hKc.image hcont
    obtain ⟨a, ha⟩ : ∃ a : ℝ, ∀ b ∈ (fun w : E n => hdist (0 : E n) w) '' K, b ≤ a := by
      simpa [bddAbove_def] using hcomp.bddAbove
    exact ⟨a, fun w hw => ha _ (Set.mem_image_of_mem _ hw)⟩
  -- every orbit of `P` meets the set of points of `P` whose level is bounded by `R`
  have hlevel : ∀ ξ ∈ P, ∃ γ : Γ, |ht (bd (γ : PO n 1) ξ)| ≤ R := by
    intro ξ hξ
    have hξS : ξ ∈ Sph n := hPsub hξ
    obtain ⟨γ, hγ⟩ := hK (hray ξ (-(ht ξ))) (hrayOutsideHoroballs n P ht hPsub hdisj ξ hξ)
    have hmem : bd (γ : PO n 1) ξ ∈ Sph n := hA.bd_mem (γ : PO n 1) ξ hξS
    have hlev : busemann (bd (γ : PO n 1) ξ) ((γ : PO n 1) • hray ξ (-(ht ξ)))
        = ht (bd (γ : PO n 1) ξ) := by
      rw [hI.busemann_cocycle (γ : PO n 1) ξ (hray ξ (-(ht ξ))) hξS, busemann_hray ξ hξS,
        neg_neg]
      exact (heq γ ξ hξ).symm
    refine ⟨γ, ?_⟩
    have h := abs_busemann_le_hdist_zero (bd (γ : PO n 1) ξ) hmem ((γ : PO n 1) • hray ξ (-(ht ξ)))
    rw [hlev] at h
    exact le_trans h (hR _ hγ)
  -- points of `P` with level bounded by `R` are `δ`-separated in the compact sphere
  have hAfin : ({ξ : E n | ξ ∈ P ∧ |ht ξ| ≤ R}).Finite := by
    refine separatedFinite (s := Sph n) (A := {ξ : E n | ξ ∈ P ∧ |ht ξ| ≤ R})
      (δ := 2 * Real.exp (-R)) (isCompact_sphere (0 : E n) 1) ?_ ?_ ?_
    · intro ξ hξ
      exact hPsub hξ.1
    · exact mul_pos two_pos (Real.exp_pos (-R))
    · intro ξ hξ η hη hne
      exact horoballLevelSeparation n P ht hPsub hdisj hξ.1 hη.1 hne hξ.2 hη.2
  -- enumerate the finite set
  let F : Finset (E n) := hAfin.toFinset
  have hF : (F : Set (E n)) = {ξ : E n | ξ ∈ P ∧ |ht ξ| ≤ R} := hAfin.coe_toFinset
  refine ⟨F.card, fun i => ((F.equivFin.symm i : F) : E n), ?_, ?_⟩
  · intro i
    have hmem : ((F.equivFin.symm i : F) : E n) ∈ (F : Set (E n)) := (F.equivFin.symm i).2
    rw [hF, Set.mem_ofPred_eq] at hmem
    exact hmem.1
  · intro ξ hξ
    obtain ⟨γ, hγ⟩ := hlevel ξ hξ
    have hmemF : bd (γ : PO n 1) ξ ∈ (F : Set (E n)) := by
      rw [hF, Set.mem_ofPred_eq]
      exact ⟨hPinv γ ξ hξ, hγ⟩
    refine ⟨F.equivFin ⟨bd (γ : PO n 1) ξ, hmemF⟩, ⟨γ⁻¹, ?_⟩⟩
    change bd ((γ⁻¹ : Γ) : PO n 1)
      ((F.equivFin.symm (F.equivFin ⟨bd (γ : PO n 1) ξ, hmemF⟩) : F) : E n) = ξ
    rw [show ((F.equivFin.symm (F.equivFin ⟨bd (γ : PO n 1) ξ, hmemF⟩) : F) : E n)
        = bd (γ : PO n 1) ξ from by simp [Equiv.symm_apply_apply]]
    rw [show ((γ⁻¹ : Γ) : PO n 1) = (γ : PO n 1)⁻¹ from rfl]
    rw [← hA.bd_mul ((γ : PO n 1))⁻¹ (γ : PO n 1) ξ (hPsub hξ), inv_mul_cancel,
      hA.bd_one ξ (hPsub hξ)]

end

end Work.Mostow
