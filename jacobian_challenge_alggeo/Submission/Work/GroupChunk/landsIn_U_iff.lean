import Mathlib
import Submission.Work.GroupChunk.Defs
import Submission.Work.GroupChunk.landsIn_aux
import Submission.Work.GroupChunk.exists_factor_resPt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.GroupChunk

open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory
open scoped Work.GCBasics

universe u

open Work.GCBasics

namespace LandsInUAux

open Work.GCBasics

variable {K : Type u} [Field K]

/-- The `K`-algebra structure maps of a field extension compose trivially. -/
theorem comp_ofId_eq {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') : e.comp (Algebra.ofId K F) = Algebra.ofId K F' :=
  AlgHom.ext (fun k => e.commutes k)

end LandsInUAux

noncomputable section

theorem landsIn_U_iff {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    [D : Work.GroupChunk.Input C P0] (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : Work.GCBasics.FPt (Work.GCBasics.Opens.toOver D.V) F) :
    Work.GCBasics.RPt.LandsIn p (Work.GroupChunk.U i j) ↔
      D.InChart j (D.picOf i (p ≫ Work.GCBasics.Opens.ιOver D.V)) := by
  constructor
  · -- ⇒ : a point of `U i j` has its class represented by its `σ i j`-value, which lies in `V`
    intro hp
    have hqW : RPt.LandsIn (p ≫ Opens.ιOver D.V) (W i j) :=
      (RPt.landsIn_preimage (p := p) (f := Opens.ιOver D.V) (V := W i j)).mpr
        (by simpa only [Opens.ιOver_left, U] using hp)
    have hqdom : RPt.LandsIn (p ≫ Opens.ιOver D.V) (σ i j).domain := W_le_domain i j hqW
    obtain ⟨Q, hQ, -⟩ :=
      FPt.factor_of_landsIn (σ i j).domain (p ≫ Opens.ιOver D.V) hqdom
    have hQV := σPM_hom_mem_V_of_landsIn_W i j (p ≫ Opens.ιOver D.V) hqW Q hQ
    have hval := σVal_eq_of_factor i j (p ≫ Opens.ιOver D.V) hqdom Q hQ
    have hcls : D.picOf j (σVal i j (p ≫ Opens.ιOver D.V) hqdom)
        = D.picOf i (p ≫ Opens.ιOver D.V) :=
      (picOf_eq_iff' j i (σVal i j (p ≫ Opens.ιOver D.V) hqdom) (p ≫ Opens.ιOver D.V)).mpr
        (by simpa only [← Input.EF_divOf] using σ_value i j (p ≫ Opens.ιOver D.V) hqdom)
    refine ⟨σVal i j (p ≫ Opens.ιOver D.V) hqdom, ?_, hcls⟩
    show (σVal i j (p ≫ Opens.ιOver D.V) hqdom).left (IsLocalRing.closedPoint F) ∈ D.V
    rw [hval]
    exact hQV
  · -- ⇐ : if the class of `p` is represented by a point of `V` with base divisor `E j`,
    -- then `p` lies in the domain of `σ i j` and its value lies in `V`
    intro h
    obtain ⟨y, hyV, hycls⟩ := h
    -- F-level: `ℓ (divOf q + E j - E i) = 1`
    have h0 : LinEquiv C (D.divOf D.g y - D.divOf D.g (D.EF j))
        (D.divOf D.g (p ≫ Opens.ιOver D.V) - D.divOf D.g (D.EF i)) :=
      (picOf_eq_iff j i y (p ≫ Opens.ιOver D.V)).mp hycls
    have h1 : LinEquiv C (D.divOf D.g (p ≫ Opens.ιOver D.V) + D.divOf D.g (D.EF j))
        (D.divOf D.g y + D.divOf D.g (D.EF i)) :=
      (linEquiv_add_iff_sub (D.divOf D.g (p ≫ Opens.ιOver D.V)) (D.divOf D.g y)
        (D.divOf D.g (D.EF j)) (D.divOf D.g (D.EF i))).mp h0.symm
    have hAF : LinEquiv C (AF i j (p ≫ Opens.ιOver D.V)) (D.divOf D.g y) := by
      have h2 : LinEquiv C (D.divOf D.g (p ≫ Opens.ιOver D.V) + bcKF F (D.EDiv j))
          (D.divOf D.g y + bcKF F (D.EDiv i)) := by
        simpa only [Input.EF_divOf] using h1
      have key := (LinEquiv.sub_iff (D.divOf D.g (p ≫ Opens.ιOver D.V) + bcKF F (D.EDiv j))
        (D.divOf D.g y + bcKF F (D.EDiv i)) (bcKF F (D.EDiv i))).mpr h2
      rw [show (D.divOf D.g y + bcKF F (D.EDiv i)) - bcKF F (D.EDiv i)
        = D.divOf D.g y by abel] at key
      exact key
    have hellF : ell C (AF i j (p ≫ Opens.ιOver D.V)) = 1 := by
      rw [ell_eq_of_linEquiv hAF, ell_of_landsIn_V y hyV]
    -- factor `p ≫ ιOver D.V` through the residue field of its image point
    obtain ⟨e, he⟩ := exists_factor_resPt (X := D.Sym D.g) (p := p ≫ Opens.ιOver D.V)
    -- the base change of the `κ(x)`-level divisor is the `F`-level one
    have hdiv : SpecLin.DivBase.bc e
        (D.divOf D.g (resPt (D.Sym D.g)
          ((p ≫ Opens.ιOver D.V).left (IsLocalRing.closedPoint F))))
        = D.divOf D.g (p ≫ Opens.ιOver D.V) := by
      rw [← divOf_map' D.g e (resPt (D.Sym D.g)
        ((p ≫ Opens.ιOver D.V).left (IsLocalRing.closedPoint F)))]
      rw [← he]
    have hE (k : D.Idx) : SpecLin.DivBase.bc e
        (bcKF (resK (p ≫ Opens.ιOver D.V)) (D.EDiv k)) = bcKF F (D.EDiv k) := by
      have hcomp := SpecLin.DivBase.bc_comp
        (Algebra.ofId K (resK (p ≫ Opens.ιOver D.V))) e (D.EDiv k)
      rw [LandsInUAux.comp_ofId_eq e] at hcomp
      exact hcomp.symm
    have hbc : SpecLin.DivBase.bc e (Aκ i j (p ≫ Opens.ιOver D.V))
        = AF i j (p ≫ Opens.ιOver D.V) := by
      simp only [Aκ, AF]
      rw [sub_eq_add_neg, sub_eq_add_neg, SpecLin.DivBase.bc_add, SpecLin.DivBase.bc_add,
        SpecLin.DivBase.bc_neg, hdiv, hE j, hE i]
    -- transfer `ℓ = 1` to the residue field
    have hdeg : Ddeg C (resK (p ≫ Opens.ιOver D.V)) (Aκ i j (p ≫ Opens.ιOver D.V))
        = (D.g : ℤ) := by
      have h1' : Ddeg C (resK (p ≫ Opens.ιOver D.V))
          (D.divOf D.g (resPt (D.Sym D.g)
            ((p ≫ Opens.ιOver D.V).left (IsLocalRing.closedPoint F)))) = (D.g : ℤ) :=
        (D.symGeom D.g).divOf_deg _
      have h2 : Ddeg C (resK (p ≫ Opens.ιOver D.V)) (bcKF (resK (p ≫ Opens.ιOver D.V))
          (D.EDiv j)) = (D.g : ℤ) :=
        (SpecLin.DivBase.deg_bc (Algebra.ofId K (resK (p ≫ Opens.ιOver D.V)))
          (D.EDiv j)).trans (D.EDiv_deg j)
      have h3 : Ddeg C (resK (p ≫ Opens.ιOver D.V)) (bcKF (resK (p ≫ Opens.ιOver D.V))
          (D.EDiv i)) = (D.g : ℤ) :=
        (SpecLin.DivBase.deg_bc (Algebra.ofId K (resK (p ≫ Opens.ιOver D.V)))
          (D.EDiv i)).trans (D.EDiv_deg i)
      simp only [Aκ, map_sub, map_add]
      rw [h1', h2, h3]
      ring
    have hAκ : ell C (Aκ i j (p ≫ Opens.ιOver D.V)) = 1 :=
      ell_eq_one_of_bc e _ hdeg (by rw [hbc]; exact hellF)
    -- hence `p` is in the domain of `σ i j`
    have hxdom : (p ≫ Opens.ιOver D.V).left (IsLocalRing.closedPoint F)
        ∈ (σ i j).domain := σ_mem_domain i j _ hAκ
    have hqdom : RPt.LandsIn (p ≫ Opens.ιOver D.V) (σ i j).domain := hxdom
    obtain ⟨Q, hQ, -⟩ :=
      FPt.factor_of_landsIn (σ i j).domain (p ≫ Opens.ιOver D.V) hqdom
    -- the value of `σ i j` at `p` is the given witness `y`
    have hy' : σVal i j (p ≫ Opens.ιOver D.V) hqdom = y := by
      have hsv : LinEquiv C (D.divOf D.g (σVal i j (p ≫ Opens.ιOver D.V) hqdom)
          + D.divOf D.g (D.EF i)) (D.divOf D.g (p ≫ Opens.ιOver D.V) + D.divOf D.g (D.EF j)) :=
        (by simpa only [← Input.EF_divOf] using σ_value i j (p ≫ Opens.ιOver D.V) hqdom)
      have h4 : LinEquiv C (D.divOf D.g (σVal i j (p ≫ Opens.ιOver D.V) hqdom)
          + D.divOf D.g (D.EF i)) (D.divOf D.g y + D.divOf D.g (D.EF i)) := hsv.trans h1
      have h5 : LinEquiv C (D.divOf D.g (σVal i j (p ≫ Opens.ιOver D.V) hqdom))
          (D.divOf D.g y) := by
        have key := (LinEquiv.sub_iff (D.divOf D.g (σVal i j (p ≫ Opens.ιOver D.V) hqdom)
          + D.divOf D.g (D.EF i)) (D.divOf D.g y + D.divOf D.g (D.EF i))
          (D.divOf D.g (D.EF i))).mpr h4
        rw [show (D.divOf D.g (σVal i j (p ≫ Opens.ιOver D.V) hqdom)
            + D.divOf D.g (D.EF i)) - D.divOf D.g (D.EF i)
            = D.divOf D.g (σVal i j (p ≫ Opens.ιOver D.V) hqdom) by abel,
          show (D.divOf D.g y + D.divOf D.g (D.EF i)) - D.divOf D.g (D.EF i)
            = D.divOf D.g y by abel] at key
        exact key
      have h6 : D.divOf D.g y = D.divOf D.g (σVal i j (p ≫ Opens.ιOver D.V) hqdom) :=
        linEquiv_eq_of_ell_eq_one ((D.symGeom D.g).divOf_isEffective y)
          (ell_of_landsIn_V y hyV)
          ((D.symGeom D.g).divOf_isEffective (σVal i j (p ≫ Opens.ιOver D.V) hqdom)) h5.symm
      exact ((D.symGeom D.g).divOf_injective y (σVal i j (p ≫ Opens.ιOver D.V) hqdom) h6).symm
    have hQV : (σPM i j).hom (Q.left (IsLocalRing.closedPoint F)) ∈ D.V := by
      rw [← σVal_eq_of_factor i j (p ≫ Opens.ιOver D.V) hqdom Q hQ, hy']
      exact hyV
    have hqW : RPt.LandsIn (p ≫ Opens.ιOver D.V) (W i j) :=
      landsIn_W_of_σPM_hom_mem_V i j (p ≫ Opens.ιOver D.V) Q hQ hQV
    exact (RPt.landsIn_preimage (p := p) (f := Opens.ιOver D.V) (V := W i j)).mp
      (by simpa only [Opens.ιOver_left, U] using hqW)

end

end Work.GroupChunk
