import Mathlib
import Submission.Work.Pi6.MSS.e2Bar
import Submission.Work.Pi6.MSS.d1Cycle_lift
import Submission.Work.Pi6.MSS.evZ_transpose
import Submission.Work.Pi6.MSS.e2Pairing_descent
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

/-- The evaluation pairing `e2L0` on representatives, unfolded: for `x ∈ Z_2^s` and a `d¹`-cycle
`v` of `E¹_{s,q}` it is the evaluation of the `E¹`-functional of `x` on the class of `v` read in
`Z_{s+q}(gr_s) ⧸ B_{s+q}(gr_s) ≈ H_{s+q}(gr_s)`. -/
private lemma e2L0_apply_unfold (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (s q : ℕ)
    (x : ↥(pZ 𝕜 (Wc 𝕜 p) 2 s (s + q))) (v : ↥(e2KerD 𝕜 p s q)) :
    e2L0 𝕜 E B p s q x v = evZ 𝕜 p s (s + q) (hannSerre 𝕜 p)
      (LinearMap.codRestrict (pZ 𝕜 (Wc 𝕜 p) 1 s (s + q)) (pZ 𝕜 (Wc 𝕜 p) 2 s (s + q)).subtype
        (fun y => pZ_two_le_one 𝕜 p s (s + q) y.2) x)
      ((e2Hb 𝕜 (Kg 𝕜 p s) (s + q)).hom.hom ((e2KerD 𝕜 p s q).subtype v)) := rfl

theorem e2Lbar_exists (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s q : ℕ) :
    ∃ L : ↥(Work.Pi6.MSS.pEraw 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 s (s + q)) →ₗ[𝕜]
        (↥(Work.Pi6.MSS.e2KerD 𝕜 p s q) →ₗ[𝕜] 𝕜),
      ∀ x : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 s (s + q)),
        L (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 s (s + q)).comap
            (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 s (s + q)).subtype) x)
          = Work.Pi6.MSS.e2L0 𝕜 E B p s q x := by
  refine ⟨Submodule.liftQ ((pDen 𝕜 (Wc 𝕜 p) 2 s (s + q)).comap
      (pZ 𝕜 (Wc 𝕜 p) 2 s (s + q)).subtype) (e2L0 𝕜 E B p s q) ?_, ?_⟩
  · -- `e2L0` vanishes on `pDen 2 ∩ pZ 2`: the representative of the `d¹`-cycle is lifted to a
    -- chain, where the descent lemma `e2Pairing_descent` applies.
    intro x hx
    rw [LinearMap.mem_ker]
    ext v
    obtain ⟨w, hw⟩ := Submodule.mkQ_surjective (Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) (s + q))
      ((e2Hb 𝕜 (Kg 𝕜 p s) (s + q)).hom.hom ((e2KerD 𝕜 p s q).subtype v))
    rw [e2L0_apply_unfold, ← hw, evZ_apply]
    have hxx : ((LinearMap.codRestrict (pZ 𝕜 (Wc 𝕜 p) 1 s (s + q))
          (pZ 𝕜 (Wc 𝕜 p) 2 s (s + q)).subtype
          (fun y => pZ_two_le_one 𝕜 p s (s + q) y.2) x : ↥(pZ 𝕜 (Wc 𝕜 p) 1 s (s + q))) :
        (Wc 𝕜 p).C.X (s + q)) = (x : (Wc 𝕜 p).C.X (s + q)) := rfl
    rw [hxx]
    -- the cycle `w` represents `v ∈ ker d¹`, so the chain lift condition of `d1Cycle_lift` holds
    have he1 : e1elt 𝕜 p s q w = (e2KerD 𝕜 p s q).subtype v := by
      rw [e1elt, hw]
      have h := congrArg ModuleCat.Hom.hom
        (CategoryTheory.Iso.hom_inv_id (e2Hb 𝕜 (Kg 𝕜 p s) (s + q)))
      rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
      exact LinearMap.congr_fun h ((e2KerD 𝕜 p s q).subtype v)
    have hd1 : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d s (s - 1) (e1elt 𝕜 p s q w) = 0 := by
      rw [he1]
      exact v.2
    obtain ⟨Y, Z, hYZ⟩ := d1Cycle_lift 𝕜 E B p s q w hd1
    exact e2Pairing_descent 𝕜 E B p s q x (Submodule.mem_comap.mp hx)
      (grSecX 𝕜 p s (s + q) (w : (Kg 𝕜 p s).X (s + q))) ⟨Y, Z, hYZ⟩
  · -- the computation rule on representatives
    intro x
    exact Submodule.liftQ_apply _ _ _

end Work.Pi6.MSS
