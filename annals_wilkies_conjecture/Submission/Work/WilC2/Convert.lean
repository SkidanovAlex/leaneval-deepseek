/-
  Area C2 (WilC2): the passage from the raw semantics of `sliceSent` (with the assignment
  functions produced by the quantifier blocks) to the clean semantics `SliceGoodQ`.
-/
import Submission.Work.WilC2.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

variable {M : Type*} {n K : ℕ}

theorem sliceRaw_iff_sliceGoodQ {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) {n : ℕ} (K : ℕ) (φ : ParamFormula n) :
    SliceRaw K φ M ↔ SliceGoodQ K φ M := by
  haveI : ringToLRc.IsExpansionOn M := instRingToLRcIsExpansionOn M
  constructor
  · intro h p
    obtain ⟨y, hy⟩ := h p
    refine ⟨y, fun i j hij => ?_, fun q hu hv hb hc => ?_⟩
    · have h1 := (hy (fun _ : Fin 3 => 0)).1 ⟨(i, j), hij⟩
      rw [rawV_comp_vec2_cut] at h1
      simp only [LHom.realize_onFormula] at h1
      exact (leF_realize_le hsq (y i) (y j)).mp h1
    · have hA : φ.Realize (rawV (default : Empty → M) p y q ∘
          Sum.elim (fun i => paramVar (K := K) i) (fun _ : Fin 1 => ptVar (n := n) 0)) := by
        rw [rawV_comp_param_pt]
        exact hu
      have hB : φ.Realize (rawV (default : Empty → M) p y q ∘
          Sum.elim (fun i => paramVar (K := K) i) (fun _ : Fin 1 => ptVar (n := n) 2)) := by
        rw [rawV_comp_param_pt]
        exact hv
      have hC : (ringToLRc.onFormula btwF).Realize (rawV (default : Empty → M) p y q ∘
          ![ptVar (n := n) 0, ptVar (n := n) 1, ptVar (n := n) 2]) := by
        rw [rawV_comp_vec3_pt]
        rw [LHom.realize_onFormula]
        exact (btwF_realize_btw hsq (q 0) (q 1) (q 2)).mpr hb
      have hD : ∀ j : Fin K, ¬(ringToLRc.onFormula btwF).Realize
          (rawV (default : Empty → M) p y q ∘
            ![ptVar (n := n) 0, cutVar (n := n) j, ptVar (n := n) 2]) := by
        intro j hj
        rw [rawV_comp_vec3_cut] at hj
        rw [LHom.realize_onFormula] at hj
        exact hc j ((btwF_realize_btw hsq (q 0) (y j) (q 2)).mp hj)
      have h5 := (hy q).2 ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩
      rw [rawV_comp_param_pt] at h5
      exact h5
  · intro h p
    obtain ⟨y, hy⟩ := h p
    refine ⟨y, fun q => ⟨fun b => ?_, fun hc => ?_⟩⟩
    · rw [rawV_comp_vec2_cut]
      rw [LHom.realize_onFormula]
      exact (leF_realize_le hsq (y b.1.1) (y b.1.2)).mpr (hy.1 b.1.1 b.1.2 b.2)
    · have hb : ((q 0 < q 1 ∧ q 1 < q 2) ∨ (q 2 < q 1 ∧ q 1 < q 0)) := by
        have h1 := hc.1.2
        rw [rawV_comp_vec3_pt] at h1
        rw [LHom.realize_onFormula] at h1
        exact (btwF_realize_btw hsq (q 0) (q 1) (q 2)).mp h1
      have hcu : ∀ j : Fin K, ¬((q 0 < y j ∧ y j < q 2) ∨ (q 2 < y j ∧ y j < q 0)) := by
        intro j hj
        apply hc.2 j
        rw [rawV_comp_vec3_cut]
        rw [LHom.realize_onFormula]
        exact (btwF_realize_btw hsq (q 0) (y j) (q 2)).mpr hj
      have hu : φ.Realize (Sum.elim p (fun _ => q 0)) := by
        have h1 := hc.1.1.1
        rw [rawV_comp_param_pt] at h1
        exact h1
      have hv : φ.Realize (Sum.elim p (fun _ => q 2)) := by
        have h1 := hc.1.1.2
        rw [rawV_comp_param_pt] at h1
        exact h1
      have h5 := hy.2 q hu hv hb hcu
      rw [rawV_comp_param_pt]
      exact h5

/-- The `Fin 3`-indexed and the `(u,w,v)`-indexed forms of the slice semantics agree. -/
theorem sliceGoodQ_iff_sliceGood {M : Type} [LRc.Structure M] [Preorder M] {n : ℕ} (K : ℕ)
    (φ : ParamFormula n) : SliceGoodQ K φ M ↔ SliceGood K φ M := by
  constructor
  · intro h p
    obtain ⟨y, hy⟩ := h p
    refine ⟨y, hy.1, fun u w v hu hv hb hc => ?_⟩
    have hb' : ((![u, w, v] 0 < ![u, w, v] 1 ∧ ![u, w, v] 1 < ![u, w, v] 2) ∨
        (![u, w, v] 2 < ![u, w, v] 1 ∧ ![u, w, v] 1 < ![u, w, v] 0)) := by
      simpa using hb
    have hc' : ∀ j : Fin K, ¬((![u, w, v] 0 < y j ∧ y j < ![u, w, v] 2) ∨
        (![u, w, v] 2 < y j ∧ y j < ![u, w, v] 0)) := by
      intro j hj
      exact hc j (by simpa using hj)
    have := hy.2 ![u, w, v] (by simpa using hu) (by simpa using hv) hb' hc'
    simpa using this
  · intro h p
    obtain ⟨y, hy⟩ := h p
    refine ⟨y, hy.1, fun q hu hv hb hc => ?_⟩
    have hb' : ((q 0 < q 1 ∧ q 1 < q 2) ∨ (q 2 < q 1 ∧ q 1 < q 0)) := hb
    have hc' : ∀ j : Fin K, ¬((q 0 < y j ∧ y j < q 2) ∨ (q 2 < y j ∧ y j < q 0)) := hc
    have := hy.2 (q 0) (q 1) (q 2) hu hv hb' hc'
    simpa using this

end Work.WilC2
