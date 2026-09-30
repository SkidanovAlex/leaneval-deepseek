import Mathlib
import Submission.Work.Pi6.MSS.evSaux
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Descent of the `E_2` pairing: a page-two element of the denominator kills the `d_1`-cycles

Let `W = Wc 𝕜 p` be the Serre cochain filtration of `p : E → B` and let `c ∈ Z_2^s C^{s+q}` be a
page-two cycle which also lies in the denominator `pDen 2 s (s+q) = Z_1^{s+1} + B_2^s`, so that its
class in `E_2^{s,s+q}` vanishes.  For a chain `C ∈ C_{s+q}(A_{s+1})` whose boundary satisfies the
`d_1`-cycle condition `∂C = Y + ∂Z` with `Y ∈ C_{s+q-1}(A_{s-1})` and `Z ∈ C_{s+q}(A_s)`, the
evaluation of `c` on the inclusion of `C` into the chains of `E` vanishes:

`cochainFun c (inclL_{s+1} C) = 0`.

Indeed, splitting `c = a + b` with `a ∈ Z_1^{s+1}` and `b ∈ B_2^s = F^s ∩ d(F^{s-1})`:

* `a ∈ F^{s+1}` kills the chains of `A_{s+1}`, hence `a(C) = 0`;
* writing `b = δb'` with `b' ∈ F^{s-1}`, the Leibniz rule gives `b(C) = b'(∂C)`, which splits as
  `b'(Y) + b'(∂Z)`; the first term vanishes because `b' ∈ F^{s-1}` kills `A_{s-1}`, and the second
  because `b'(∂Z) = b(Z)` and `b ∈ F^s` kills `A_s`.

This is the well-definedness half of the perfect pairing `E_2^{s,q} × E^2_{s,q} → 𝕜` used for
`Work.Pi6.MSS.e2Psi_bij`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Pi6.MSS

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The adjunction between the predecessor coboundary `dPrev` of the Serre cochain filtration and
the boundary of the singular chains: `(δb')(w) = b'(∂w)`.  -/
lemma e2pd_dPrev (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (n : ℕ)
    (y : (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X (n-1) →ₗ[𝕜] 𝕜)
    (w : ↥((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X n)) :
    cochainFun 𝕜 p n ((Wc 𝕜 p).dPrev n y) w =
      y (((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d n (n-1)).hom w) := by
  rcases n with _ | m
  · show cochainFun 𝕜 p 0 (((Wc 𝕜 p).C.d 0 0).hom y) w =
      y (((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d 0 0).hom w)
    rw [HomologicalComplex.shape (Wc 𝕜 p).C 0 0 (by simp [ComplexShape.up_Rel]),
      HomologicalComplex.shape (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)) 0 0
        (by simp [ComplexShape.down])]
    simp only [cochainFun, ModuleCat.hom_zero, LinearMap.zero_apply, LinearMap.map_zero]
  · show cochainFun 𝕜 p (m+1) (((Wc 𝕜 p).d m) y) w =
      y (((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (m+1) m).hom w)
    rw [Wc_d_apply 𝕜 p m]
    rfl

/-- Naturality of the inclusion `inclL k` with respect to the boundary: `∂(inclL_k z) =
inclL_k(∂z)`. -/
lemma e2pd_inclL_d (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (k n : ℕ) (z : (Cc 𝕜 p k).X n) :
    ((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d n (n-1)).hom (((inclL 𝕜 p k).f n).hom z)
      = ((inclL 𝕜 p k).f (n-1)).hom (((Cc 𝕜 p k).d n (n-1)).hom z) := by
  have h := congrArg (fun (g : (Cc 𝕜 p k).X n ⟶
      (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X (n-1)) => g.hom z)
      ((inclL 𝕜 p k).comm n (n-1))
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    LinearMap.comp_apply] at h
  exact h

theorem e2Pairing_descent (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s q : ℕ)
    (c : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 s (s+q)))
    (hc : (c : (Work.Pi6.MSS.Wc 𝕜 p).C.X (s+q)) ∈
      Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 s (s+q))
    (C : ↥((Work.Pi6.MSS.Cc 𝕜 p (s+1)).X (s+q)))
    (hC : ∃ Y : ↥((Work.Pi6.MSS.Cc 𝕜 p (s-1)).X (s+q-1)),
      ∃ Z : ↥((Work.Pi6.MSS.Cc 𝕜 p s).X (s+q)),
        (Work.Pi6.MSS.inclL 𝕜 p (s+1)).f (s+q-1)
            (((Work.Pi6.MSS.Cc 𝕜 p (s+1)).d (s+q) (s+q-1)).hom C)
          = (Work.Pi6.MSS.inclL 𝕜 p (s-1)).f (s+q-1) Y
            + (Work.Pi6.MSS.inclL 𝕜 p s).f (s+q-1)
                (((Work.Pi6.MSS.Cc 𝕜 p s).d (s+q) (s+q-1)).hom Z)) :
    Work.Pi6.MSS.cochainFun 𝕜 p (s+q) c.1
      ((Work.Pi6.MSS.inclL 𝕜 p (s+1)).f (s+q) C) = 0 := by
  have hann : ∀ s n, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n :=
    fun s n => coFiltAnn 𝕜 (sF p) s n
  -- split `c` along the denominator `Z_1^{s+1} + B_2^s`
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hc
  have haF : a ∈ (Wc 𝕜 p).F (s+1) (s+q) := ((mem_pZ_one (Wc 𝕜 p) (s+1) (s+q) a).mp ha).1
  have hbF : b ∈ (Wc 𝕜 p).F s (s+q) := (Submodule.mem_inf.mp hb).1
  obtain ⟨b', hb'F, hb'b⟩ := Submodule.mem_map.mp (Submodule.mem_inf.mp hb).2
  have hs2 : s + 1 - 2 = s - 1 := by omega
  have hb'F' : b' ∈ (Wc 𝕜 p).F (s-1) (s+q-1) := by rw [← hs2]; exact hb'F
  obtain ⟨Y, Z, hYZ⟩ := hC
  -- the `Z_1^{s+1}`-part kills the chains of `A_{s+1}`
  have haC : cochainFun 𝕜 p (s+q) a ((inclL 𝕜 p (s+1)).f (s+q) C) = 0 :=
    ((mem_F_iff 𝕜 p (s+1) (s+q) hann a).mp haF) C
  -- the `B_2^s`-part integrates by parts against the boundary condition
  have hbC : cochainFun 𝕜 p (s+q) b ((inclL 𝕜 p (s+1)).f (s+q) C) = 0 := by
    have h1 : cochainFun 𝕜 p (s+q) b ((inclL 𝕜 p (s+1)).f (s+q) C)
        = cochainFun 𝕜 p (s+q-1) b'
            (((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (s+q) (s+q-1)).hom
              ((inclL 𝕜 p (s+1)).f (s+q) C)) := by
      rw [← hb'b]
      exact e2pd_dPrev 𝕜 p (s+q) b' ((inclL 𝕜 p (s+1)).f (s+q) C)
    rw [h1, e2pd_inclL_d 𝕜 p (s+1) (s+q) C, hYZ, map_add]
    have hY0 : cochainFun 𝕜 p (s+q-1) b' ((inclL 𝕜 p (s-1)).f (s+q-1) Y) = 0 :=
      ((mem_F_iff 𝕜 p (s-1) (s+q-1) hann b').mp hb'F') Y
    have hZ0 : cochainFun 𝕜 p (s+q-1) b'
        ((inclL 𝕜 p s).f (s+q-1) (((Cc 𝕜 p s).d (s+q) (s+q-1)).hom Z)) = 0 := by
      rw [← e2pd_inclL_d 𝕜 p s (s+q) Z]
      change ((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (s+q) (s+q-1)).hom
        ((inclL 𝕜 p s).f (s+q) Z) ∈ LinearMap.ker b'
      rw [LinearMap.mem_ker, ← e2pd_dPrev 𝕜 p (s+q) b' ((inclL 𝕜 p s).f (s+q) Z)]
      rw [hb'b]
      exact ((mem_F_iff 𝕜 p s (s+q) hann b).mp hbF) Z
    rw [hY0, hZ0, add_zero]
  rw [show cochainFun 𝕜 p (s+q) c.1 ((inclL 𝕜 p (s+1)).f (s+q) C)
      = cochainFun 𝕜 p (s+q) a ((inclL 𝕜 p (s+1)).f (s+q) C)
        + cochainFun 𝕜 p (s+q) b ((inclL 𝕜 p (s+1)).f (s+q) C) by
        rw [← hab]; rfl]
  rw [haC, hbC, add_zero]

end

end Work.Pi6.MSS
