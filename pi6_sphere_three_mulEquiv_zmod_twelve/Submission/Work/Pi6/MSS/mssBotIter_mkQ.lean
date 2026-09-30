import Mathlib
import Submission.Work.Pi6.MSS.e2Aux
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The iterated bottom-row projection fixes representatives that survive

`Work.Pi6.MSS.mssBotIter 𝕜 E B p s s : E_2^{s,0} → E_{s+2}^{s,0}` is the iterated bottom-row
projection of the Serre spectral sequence.  On the class of a cycle `x` which survives to the page
`s+2` (that is, `x ∈ Z_r^s` for every `r ≥ 2`), it is the class of the same representative `x`.

This is the geometric content of the "row map" edge `H^s(B;𝕜) → E_2^{s,0}` of
`Submission/Work/Pi6/MSS/e2Row_exists.lean`: the class of a skeletal cocycle dies at the edge
exactly when its pullback vanishes.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜)

/-! ## 1. The projection on the concrete pages sends a surviving cycle to its own class -/

/-- The projection `ker d_r → E_{r+1}` sends the class of a cycle `x ∈ Z_r ∩ Z_{r+1}` (viewed as an
element of the cycles of `d_r`) to the class of the *same* representative in `E_{r+1}`. -/
theorem pd_proj_eq_mkQ (r s n : ℕ) (x : W.C.X n) (hx : x ∈ pZ 𝕜 W r s n)
    (hx' : x ∈ pZ 𝕜 W (r+1) s n)
    (hz : (pD 𝕜 W r s n).hom
      (Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) ⟨x, hx⟩) = 0) :
    pd_proj 𝕜 W r s n
        ⟨Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) ⟨x, hx⟩, hz⟩
      = Submodule.mkQ ((pDen 𝕜 W (r+1) s n).comap (pZ 𝕜 W (r+1) s n).subtype) ⟨x, hx'⟩ := by
  have hPhi : pd_Phi 𝕜 W r s n ⟨x, pd_pZ_succ_le_K r s n hx'⟩
      = ⟨Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) ⟨x, hx⟩, hz⟩ := by
    refine Subtype.ext ?_
    rw [pd_Phi_apply]
    exact congrArg (Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype))
      (Subtype.ext rfl)
  rw [← hPhi, pd_proj_eq_of 𝕜 W r s n ⟨x, pd_pZ_succ_le_K r s n hx'⟩]
  exact pd_pFun_eq_of 𝕜 W r s n ⟨x, pd_pZ_succ_le_K r s n hx'⟩ ⟨x, hx'⟩ (by
    show (⟨x, pd_pZ_succ_le_K r s n hx'⟩ : ↥(pd_K 𝕜 W r s n)).1 - x ∈ pDen 𝕜 W r s n
    rw [show (⟨x, pd_pZ_succ_le_K r s n hx'⟩ : ↥(pd_K 𝕜 W r s n)).1 = x from rfl, sub_self]
    exact Submodule.zero_mem _)

/-! ## 2. The bottom-row map on the bidegree-indexed page -/

/-- The inclusion of the whole page in the cycles of `d_r` at the bottom row does not change the
representative. -/
theorem mssTopIncl_coe (r : ℕ) (a : ℤ × ℤ)
    (h : LinearMap.ker (mssD 𝕜 W r a (a + vr r)).hom = ⊤) (y : mssE 𝕜 W r a) :
    ((mssTopIncl 𝕜 W r a h y : ↥(LinearMap.ker (mssD 𝕜 W r a (a + vr r)).hom)) : mssE 𝕜 W r a)
      = y := rfl

/-- The projection of the concrete `ker d_r → E_{r+1}` on a cycle is `pd_proj` on the underlying
element. -/
theorem mssProjAux_eq_pd_proj (r : ℕ) (hr : 2 ≤ r) (a : ℤ × ℤ)
    (v : ↥(LinearMap.ker (mssDMain 𝕜 W r a).hom)) :
    mssProjAux 𝕜 W r hr a v
      = pd_proj 𝕜 W r (EI a) (EN a) ⟨v.1, mssProjAux_mem 𝕜 W r hr a v⟩ := rfl

/-- The bottom-row projection at the bidegree `(s,0)`: the class of a cycle which survives one more
page is the class of the same representative. -/
theorem mssBot_eq_mkQ (r : ℕ) (hr : 2 ≤ r) (s : ℕ) (x : W.C.X s)
    (hx : x ∈ pZ 𝕜 W r s s) (hx' : x ∈ pZ 𝕜 W (r+1) s s) :
    mssBot 𝕜 W r (s : ℤ)
        (Submodule.mkQ ((pDen 𝕜 W r s s).comap (pZ 𝕜 W r s s).subtype) ⟨x, hx⟩)
      = Submodule.mkQ ((pDen 𝕜 W (r+1) s s).comap (pZ 𝕜 W (r+1) s s).subtype) ⟨x, hx'⟩ := by
  have h1 : mssBot 𝕜 W r (s : ℤ)
      (Submodule.mkQ ((pDen 𝕜 W r s s).comap (pZ 𝕜 W r s s).subtype) ⟨x, hx⟩)
      = mssProj 𝕜 W r ((s : ℤ), (0 : ℤ))
          (mssTopIncl 𝕜 W r ((s : ℤ), (0 : ℤ)) (ker_mssD_bot 𝕜 W r hr s)
            (Submodule.mkQ ((pDen 𝕜 W r s s).comap (pZ 𝕜 W r s s).subtype) ⟨x, hx⟩)) :=
    mssBot_spec 𝕜 W r (s : ℤ) hr
      (mssTopIncl 𝕜 W r ((s : ℤ), (0 : ℤ)) (ker_mssD_bot 𝕜 W r hr s)
        (Submodule.mkQ ((pDen 𝕜 W r s s).comap (pZ 𝕜 W r s s).subtype) ⟨x, hx⟩))
  rw [h1, mssProj_apply 𝕜 W r ((s : ℤ), (0 : ℤ)) hr, mssProjAux_eq_pd_proj]
  exact pd_proj_eq_mkQ 𝕜 W r s s x hx hx' _

/-! ## 3. The iterated bottom-row projection -/

/-- The iterated bottom-row projection `E_2^{s,0} → E_{s+2}^{s,0}` sends the class of a cycle which
survives to the page `s+2` to the class of the same representative. -/
theorem mssBotIter_mkQ (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s : ℕ) (x : (Work.Pi6.MSS.serreCF 𝕜 E B p).C.X s)
    (hx : ∀ r : ℕ, 2 ≤ r → x ∈ Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) r s s) :
    Work.Pi6.MSS.mssBotIter 𝕜 E B p s s
        (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 s s).comap
          (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 s s).subtype)
          ⟨x, hx 2 (by norm_num)⟩) =
      Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) (s + 2) s s).comap
        (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) (s + 2) s s).subtype)
        ⟨x, hx (s + 2) (by omega)⟩ := by
  have key : ∀ k : ℕ, mssBotIter 𝕜 E B p s k
      (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 s s).comap
        (pZ 𝕜 (serreCF 𝕜 E B p) 2 s s).subtype) ⟨x, hx 2 (by norm_num)⟩)
      = Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) (k + 2) s s).comap
        (pZ 𝕜 (serreCF 𝕜 E B p) (k + 2) s s).subtype) ⟨x, hx (k + 2) (by omega)⟩ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have step : mssBot 𝕜 (serreCF 𝕜 E B p) (k + 2) (s : ℤ)
          (mssBotIter 𝕜 E B p s k
            (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 s s).comap
              (pZ 𝕜 (serreCF 𝕜 E B p) 2 s s).subtype) ⟨x, hx 2 (by norm_num)⟩))
          = Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) (k + 3) s s).comap
              (pZ 𝕜 (serreCF 𝕜 E B p) (k + 3) s s).subtype) ⟨x, hx (k + 3) (by omega)⟩ := by
        rw [ih]
        exact mssBot_eq_mkQ 𝕜 (serreCF 𝕜 E B p) (k + 2) (by omega) s x
          (hx (k + 2) (by omega)) (hx (k + 3) (by omega))
      exact step
  exact key s

end

end Work.Pi6.MSS
