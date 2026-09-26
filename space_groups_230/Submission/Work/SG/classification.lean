import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.AffCoord
import Submission.Work.SG.affEquiv_facts
import Submission.Work.SG.exists_normal_form
import Submission.Work.SG.exists_realization
import Submission.Work.SG.conj_sgSet_integral
import Submission.Work.SG.exists_conj_of_intEquiv
import Submission.Work.SG.intEquiv_transport
import Submission.Work.SG.exists_conj_into_sellingStab
import Submission.Work.SG.conj_to_arithRep
import Submission.Work.SG.exists_sgRep_of_cocycle
import Submission.Work.SG.sgRep_intEquiv_iff
import Submission.Work.SG.sg_data_facts
import Submission.Work.SG.conjSet_glue_affOP
import Submission.Work.SG.conjSet_glue_aff
import Submission.Work.SG.sgSet_det_of_mem
import Submission.Work.SG.sgSet_exists_det_mem

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SG/DESIGN.md (§ classification) first. This is the ASSEMBLY of lemmas 2–13: write it against their statements now; the four still in progress (conj_to_arithRep, exists_sgRep_of_cocycle, sgRep_intEquiv_iff, sg_data_facts) are in depends_on and will be filled in by their owners. Do not re-prove them. Do not edit Defs.lean or Data/*.

# classification — assembly (medium, ~500–900 lines)

**Claim.** There are 230 crystallographic groups `G k`. They cover every class up to
`AffOPEquivalent`, are pairwise inequivalent, their affine equivalence is
`sgAffClass k = sgAffClass l`, and `G k` is Sohncke iff `arithRep (sgArith k) ⊆ SL₃(ℤ)`.

**Sketch.** First a helper:
`conjSet ψ₂ (conjSet ψ₁ S) = conjSet (ψ₂ ψ₁) S`, and
`conjSet φ (affImage G) = affImage H ↔` the `AffinelyEquivalent` set equality (unfold).
* `G k`, `φ_k` := `exists_realization` applied to `(arithRep (sgArith k), sgTau k)`
  (valid by `sg_data_facts`).
* **Cover.** For `H`:
  1. `exists_normal_form` gives `(P, τ, φ)`.
  2. `exists_conj_into_sellingStab` gives `U₁`. Then `intEquiv_transport` and
     `conj_to_arithRep` give `U₂`, `j`. Transport again; the image set equals `arithRep j` by the
     `∀ A, A ∈ … ↔ …` clause.
  3. `exists_sgRep_of_cocycle` gives `k`, `U₃`, `s₃`.
  4. `exists_conj_of_intEquiv` turns each step into an affine conjugacy of determinant `1`.
  5. Compose everything with `φ_k⁻¹`. The determinant is positive.
* **Separation (OP).** Compose with `φ_k`, `φ_l` to get a conjugacy between `sgSet`s of positive
  determinant. `conj_sgSet_integral` gives `U` with `det U = det φ > 0`, so `det U = 1`
  (a unit of `ℤ`). Then `sgRep_intEquiv_iff`.
* **Affine.** The same with `IsUnit`. For `←`, `sgRep_intEquiv_iff` +
  `exists_conj_of_intEquiv`.
* **Sohncke.** Under `conjSet φ_k`, each `g ∈ G k` corresponds to an element of `sgSet` with
  linear part `toLin' A`, `A ∈ arithRep`. Conjugation preserves `det`. So `IsOrientationPreserving`
  ⇔ `det A > 0` ⇔ `det A = 1`.

**Challenge from here (checked, see DESIGN §7):** `encard_classes_eq` three times.
* OP: `ι = κ = Fin 230`, `π = id`.
* Affine: `π = sgAffClass`, using `sg_data_facts` for surjectivity.
* Sohncke: `ι = κ = {k | …}` of `ncard` 65. The cover uses `affEquiv_facts` (iii) to show the
  representative of a Sohncke group is Sohncke.
-/

namespace Work.SG

/-! ### Assembly status

The assembly is complete and rests on the exact statements of its inputs:
`Work.SG.conj_to_arithRep` (Selling reduction + 73 arithmetic classes) and
`Work.SG.sgRep_intEquiv_iff` (separation of the 230 representatives), the Sohncke determinant
facts `Work.SG.sgSet_det_of_mem` / `Work.SG.sgSet_exists_det_mem`, and the two gluing lemmas
`Work.SG.conjSet_glue_affOP` / `Work.SG.conjSet_glue_aff`; everything is imported and used
directly, with no local stand-in.  (An earlier version of this file carried stand-ins for the two
inputs that were not yet available, including during the `Work.SG.IVec` collision between
`SGsepDefs.lean` and `SellingDefs.lean`; see `Submission/Work/SG/BLOCKER_IVec_collision.md`.)

`Work.SG.exists_sgRep_of_cocycle` and `Work.SG.sg_data_facts` are referenced directly as well.
-/

open LeanEval.Geometry.SpaceGroupsProblem
open scoped Matrix

noncomputable section

/-! ### Conjugacy calculus for `conjSet`, determinants, and the three gluing steps -/

theorem conjSet_eq_conjAct (φ : AffineGroup 3) (S : Set (AffineGroup 3)) :
    conjSet φ S = AffFacts.conjAct φ S := rfl

theorem conjSet_mul (ψ φ : AffineGroup 3) (S : Set (AffineGroup 3)) :
    conjSet (ψ * φ) S = conjSet ψ (conjSet φ S) :=
  (conjAct_action 3).2 ψ φ S

theorem conjSet_one (S : Set (AffineGroup 3)) : conjSet 1 S = S :=
  (conjAct_action 3).1 S

theorem conjSet_inv_conjSet (φ : AffineGroup 3) (S : Set (AffineGroup 3)) :
    conjSet φ⁻¹ (conjSet φ S) = S := by
  rw [← conjSet_mul, inv_mul_cancel, conjSet_one]

theorem conjSet_conjSet_inv (φ : AffineGroup 3) (S : Set (AffineGroup 3)) :
    conjSet φ (conjSet φ⁻¹ S) = S := by
  rw [← conjSet_mul, mul_inv_cancel, conjSet_one]

theorem det_mul3 (a b c : AffineGroup 3) :
    ((a * b * c).linear.det : ℝ) =
      (a.linear.det : ℝ) * (b.linear.det : ℝ) * (c.linear.det : ℝ) := by
  rw [AffFacts.det_mul, AffFacts.det_mul]

theorem det_pos_mul {a b : AffineGroup 3} (ha : 0 < (a.linear.det : ℝ))
    (hb : 0 < (b.linear.det : ℝ)) : 0 < ((a * b).linear.det : ℝ) := by
  rw [AffFacts.det_mul]; exact mul_pos ha hb

theorem det_pos_inv {a : AffineGroup 3} (ha : 0 < (a.linear.det : ℝ)) :
    0 < ((a⁻¹).linear.det : ℝ) := by
  rw [AffFacts.det_inv]; exact inv_pos.mpr ha

theorem det_conj_inv (φ g : AffineGroup 3) :
    ((φ⁻¹ * g * φ).linear.det : ℝ) = (g.linear.det : ℝ) := by
  rw [← AffFacts.det_conj (φ⁻¹) g, inv_inv]

/-- `IntEquiv` of data with `U.det = 1` gives an affine conjugacy of determinant `1`. -/
theorem exists_conjSet_det1 {P P' : Set IMat} {τ τ' : IMat → Fin 3 → ℝ}
    (hP : IsIntPointGroup P) (hτ : IsIntCocycle P τ) {U : IMat} (hU : U.det = 1)
    {s : Fin 3 → ℝ} (h : IntEquiv P τ P' τ' U s) :
    ∃ θ : AffineGroup 3, (θ.linear.det : ℝ) = 1 ∧ conjSet θ (sgSet P τ) = sgSet P' τ' := by
  obtain ⟨θ, hθdet, hθ⟩ := exists_conj_of_intEquiv hP hτ (by rw [hU]; exact isUnit_one) h
  exact ⟨θ, by rw [hθdet, hU]; norm_num, hθ⟩

/-- The classification: 230 crystallographic groups, pairwise not orientation-preserving
affinely equivalent and covering everything; affine equivalence among them is `sgAffClass`;
the Sohncke ones are those whose arithmetic class lies in `SL₃(ℤ)`. -/
theorem classification :
    ∃ G : Fin 230 → CrystallographicGroup 3,
      (∀ H : CrystallographicGroup 3, ∃ k, AffOPEquivalent (G k).1 H.1) ∧
      (∀ k l, AffOPEquivalent (G k).1 (G l).1 ↔ k = l) ∧
      (∀ k l, AffinelyEquivalent (G k).1 (G l).1 ↔ sgAffClass k = sgAffClass l) ∧
      (∀ k, (∀ g ∈ (G k).1, IsOrientationPreservingIsom g) ↔
        ∀ A ∈ arithRep (sgArith k), A.det = 1) := by
  classical
  -- `Work.SG.conj_to_arithRep` (Selling reduction + arithmetic classes) is imported
  -- and used directly below.
  -- `Work.SG.sgRep_intEquiv_iff` is imported and used directly below.
  -- #### inputs from the data facts and the equivalence lemmas ####
  obtain ⟨hPG, hCoc, hSurj, h65⟩ := sg_data_facts
  obtain ⟨hAEeq, hOPeq, hOPhpres⟩ := affEquiv_facts 3
  obtain ⟨hConjActId, hAEiff, hOPiff⟩ := affinelyEquivalent_conjAct 3
  -- #### the 230 representatives ####
  have hreal : ∀ k : Fin 230, ∃ (G : CrystallographicGroup 3) (φ : AffineGroup 3),
      0 < (φ.linear.det : ℝ) ∧
        conjSet φ (affImage G.1) = sgSet (arithRep (sgArith k)) (sgTau k) :=
    fun k => exists_realization (hPG (sgArith k)) (hCoc k)
  choose Gk φk hφkpos hφk using hreal
  refine ⟨Gk, ?_, ?_, ?_, ?_⟩
  · -- cover
    intro H
    obtain ⟨P, τ, hP, hτ, ψ, hψpos, hψ⟩ := exists_normal_form H
    obtain ⟨U₁, hU₁det, i, hU₁sub⟩ := exists_conj_into_sellingStab hP
    set P₁ : Set IMat := {A | ∃ B ∈ P, A = U₁ * B * U₁⁻¹} with hP₁def
    obtain ⟨τ₁, hP₁, hτ₁, hIE₁⟩ := intEquiv_transport hP hτ (by rw [hU₁det]; exact isUnit_one)
    have hP₁sub : ∀ A ∈ P₁, A ∈ sellingStab (sellingGraph i) := by
      intro A hA
      obtain ⟨B, hB, rfl⟩ := hA
      exact hU₁sub B hB
    obtain ⟨j, U₂, hU₂det, hU₂map⟩ := conj_to_arithRep hP₁ hP₁sub
    set P₂ : Set IMat := {A | ∃ B ∈ P₁, A = U₂ * B * U₂⁻¹} with hP₂def
    obtain ⟨τ₂, hP₂, hτ₂, hIE₂⟩ := intEquiv_transport hP₁ hτ₁ (by rw [hU₂det]; exact isUnit_one)
    have hP₂eq : arithRep j = P₂ := Set.ext fun A => hU₂map A
    have hτ₂' : IsIntCocycle (arithRep j) τ₂ := by rw [hP₂eq]; exact hτ₂
    have hIE₂' : IntEquiv P₁ τ₁ (arithRep j) τ₂ U₂ 0 := by rw [hP₂eq]; exact hIE₂
    obtain ⟨k, hk, U₃, hU₃det, s₃, hIE₃⟩ := exists_sgRep_of_cocycle j hτ₂'
    obtain ⟨θ₁, hθ₁det, hθ₁⟩ := exists_conjSet_det1 hP hτ hU₁det hIE₁
    obtain ⟨θ₂, hθ₂det, hθ₂⟩ := exists_conjSet_det1 hP₁ hτ₁ hU₂det hIE₂'
    obtain ⟨θ₃, hθ₃det, hθ₃⟩ := exists_conjSet_det1 (hPG j) hτ₂' hU₃det hIE₃
    have hθ : conjSet (θ₃ * θ₂ * θ₁) (sgSet P τ) = sgSet (arithRep j) (sgTau k) := by
      rw [conjSet_mul, conjSet_mul, hθ₁, hθ₂, hθ₃]
    have hθpos : 0 < ((θ₃ * θ₂ * θ₁).linear.det : ℝ) := by
      rw [det_mul3, hθ₃det, hθ₂det, hθ₁det]; norm_num
    have hφk' : conjSet (φk k) (affImage (Gk k).1) = sgSet (arithRep j) (sgTau k) := by
      rw [hφk k, hk]
    exact ⟨k, hOPeq.symm (conjSet_glue_affOP hψ hφk' hθ hψpos (hφkpos k) hθpos)⟩
  · -- separation, orientation preserving
    intro k l
    refine ⟨?_, ?_⟩
    · intro hop
      obtain ⟨χ, hχpos, hχ⟩ := (hOPiff (Gk k).1 (Gk l).1).mp hop
      have hχ' : conjSet χ (affImage (Gk k).1) = affImage (Gk l).1 := hχ
      have h1 : conjSet (φk k)⁻¹ (sgSet (arithRep (sgArith k)) (sgTau k)) =
          affImage (Gk k).1 := by
        rw [← hφk k, conjSet_inv_conjSet]
      have hθ : conjSet (φk l * χ * (φk k)⁻¹)
          (sgSet (arithRep (sgArith k)) (sgTau k)) =
          sgSet (arithRep (sgArith l)) (sgTau l) := by
        rw [conjSet_mul, conjSet_mul, h1, hχ', hφk l]
      obtain ⟨U, hUunit, hUdet, s, hrepr, hIE⟩ :=
        conj_sgSet_integral (hPG (sgArith k)) (hCoc k) (hPG (sgArith l)) (hCoc l) hθ
      have hp : 0 < (((φk l * χ) * (φk k)⁻¹).linear.det : ℝ) :=
        det_pos_mul (det_pos_mul (hφkpos l) hχpos) (det_pos_inv (hφkpos k))
      have hUp : (0 : ℝ) < (U.det : ℝ) := by
        rw [← hUdet]; exact hp
      have hUdet1 : U.det = 1 := by
        rcases Int.isUnit_iff.mp hUunit with h | h
        · exact h
        · exfalso; rw [h] at hUp; norm_num at hUp
      exact (sgRep_intEquiv_iff k l).1.mp ⟨U, hUdet1, s, hIE⟩
    · intro hkl
      rw [hkl]
      exact hOPeq.refl (Gk l)
  · -- separation, affine
    intro k l
    refine ⟨?_, ?_⟩
    · intro hae
      obtain ⟨χ, hχ⟩ := (hAEiff (Gk k).1 (Gk l).1).mp hae
      have hχ' : conjSet χ (affImage (Gk k).1) = affImage (Gk l).1 := hχ
      have h1 : conjSet (φk k)⁻¹ (sgSet (arithRep (sgArith k)) (sgTau k)) =
          affImage (Gk k).1 := by
        rw [← hφk k, conjSet_inv_conjSet]
      have hθ : conjSet (φk l * χ * (φk k)⁻¹)
          (sgSet (arithRep (sgArith k)) (sgTau k)) =
          sgSet (arithRep (sgArith l)) (sgTau l) := by
        rw [conjSet_mul, conjSet_mul, h1, hχ', hφk l]
      obtain ⟨U, hUunit, -, s, -, hIE⟩ :=
        conj_sgSet_integral (hPG (sgArith k)) (hCoc k) (hPG (sgArith l)) (hCoc l) hθ
      exact (sgRep_intEquiv_iff k l).2.mp ⟨U, hUunit, s, hIE⟩
    · intro hc
      obtain ⟨U, hUunit, s, hIE⟩ := (sgRep_intEquiv_iff k l).2.mpr hc
      obtain ⟨θ, hθdet, hθ⟩ := exists_conj_of_intEquiv (hPG (sgArith k)) (hCoc k) hUunit hIE
      exact conjSet_glue_aff (hφk k) (hφk l) hθ
  · -- Sohncke
    intro k
    refine ⟨?_, ?_⟩
    · intro hall A hA
      obtain ⟨g, hg, hgdet⟩ := sgSet_exists_det_mem (hPG (sgArith k)) hA
      have hpre : (φk k)⁻¹ * g * (φk k) ∈ affImage (Gk k).1 := by
        have hmem : (φk k)⁻¹ * g * (φk k) ∈
            conjSet (φk k)⁻¹ (sgSet (arithRep (sgArith k)) (sgTau k)) := ⟨g, hg, rfl⟩
        rwa [← hφk k, conjSet_inv_conjSet] at hmem
      obtain ⟨x, hx, hxeq⟩ := hpre
      have hdetx : (x.toAffineEquiv.linear.det : ℝ) = (A.det : ℝ) := by
        rw [← hxeq, det_conj_inv (φk k) g, hgdet]
      have hpos : 0 < (x.toAffineEquiv.linear.det : ℝ) := hall x hx
      have hApos : (0 : ℝ) < (A.det : ℝ) := by rw [← hdetx]; exact hpos
      rcases Int.isUnit_iff.mp ((hPG (sgArith k)).2.2.2 A hA) with h | h
      · exact h
      · exfalso; rw [h] at hApos; norm_num at hApos
    · intro hdet1 g hg
      have hmem : φk k * g.toAffineEquiv * (φk k)⁻¹ ∈
          sgSet (arithRep (sgArith k)) (sgTau k) := by
        rw [← hφk k]
        exact ⟨g.toAffineEquiv, ⟨g, hg, rfl⟩, rfl⟩
      obtain ⟨A, hA, hAdet⟩ := sgSet_det_of_mem hmem
      have hAg : ((g.toAffineEquiv).linear.det : ℝ) = (A.det : ℝ) := by
        rw [← AffFacts.det_conj (φk k) g.toAffineEquiv, hAdet]
      show 0 < ((g.toAffineEquiv).linear.det : ℝ)
      rw [hAg, hdet1 A hA]
      norm_num


end

end Work.SG
