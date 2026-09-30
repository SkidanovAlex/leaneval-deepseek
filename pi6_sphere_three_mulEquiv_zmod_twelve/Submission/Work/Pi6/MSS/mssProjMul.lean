import Mathlib
import Submission.Work.Pi6.MSS.AssembleCore
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The projection `ker d_r → E_{r+1}` is multiplicative

`Work.Pi6.MSS.mssProjMul`: the descent of the product through the projection of the pages,

`mssProj (z) = mssProj x · mssProj y`  whenever  `z = x · y`  on `E_r`,

is the bidegree-indexed form of the concrete statement `Work.Pi6.MSS.pd_proj_mul` about the
subquotient model `E_r^s = Z_r^s/D_r^s` of `Submission/Work/Pi6/MSS/pagesData.lean`.

The bridge between the two index conventions is:

* `Work.Pi6.MSS.mssProj_val` — `mssProj` is `pd_proj` on the underlying concrete page;
* `Work.Pi6.MSS.mssProjMul_mul_rfl` and `Work.Pi6.MSS.mssProjMul_mul_step` — `mssMul` at a
  reflexive index is the concrete product `pd_mul`, transported along the identification
  `EI (a+b) = EI a + EI b`, `EN (a+b) = EN a + EN b` of the two index conventions;
* `Work.Pi6.MSS.mssProjMul_pd_proj_pCast` — `pd_proj` commutes with the index transports;
* `Work.Pi6.MSS.mssProjMul_pD_pCast_eq_zero` — the transports preserve cycles.
-/

set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜)

/-- The projection of the bidegree-indexed pages, unfolded into the concrete model. -/
theorem mssProjMul_proj_val (r : ℕ) (hr : 2 ≤ r) (a : ℤ × ℤ)
    (x : ↥(LinearMap.ker (mssD 𝕜 W r a (a + Work.Pi6.vr r)).hom)) :
    mssProj 𝕜 W r a x = pd_proj 𝕜 W r (EI a) (EN a)
      ⟨(x : mssE 𝕜 W r a), mssProjAux_mem 𝕜 W r hr a (mssKerIncl 𝕜 W r a x)⟩ := by
  rw [mssProj_apply 𝕜 W r a hr]
  rfl

/-- The product on the pages at a reflexive index `a + b = a + b` is the raw product. -/
theorem mssProjMul_mul_rfl (r : ℕ) (a b : ℤ × ℤ) :
    mssMul 𝕜 W r a b (a + b) (rfl : a + b = a + b) = mssMulRaw 𝕜 W r a b := by
  rw [mssMul, mssCast_rfl]
  rfl

/-- The product on the pages, in the first quadrant, is the concrete product `pd_mul`, seen
through the index identification `EI (a+b) = EI a + EI b`, `EN (a+b) = EN a + EN b`. -/
theorem mssProjMul_mul_step (r : ℕ) {a b : ℤ × ℤ} (ha : Enn a) (hb : Enn b)
    (x : mssE 𝕜 W r a) (y : mssE 𝕜 W r b) :
    mssMul 𝕜 W r a b (a + b) (rfl : a + b = a + b) x y
      = pCast 𝕜 W r (EI_add ha hb) (EN_add ha hb)
          (pd_mul r (EI a) (EN a) (EI b) (EN b) x y) := by
  rw [mssProjMul_mul_rfl 𝕜 W r a b, mssMulRaw_pos 𝕜 W r ha hb]
  rfl

/-- The projection `pd_proj : ker d_r → E_{r+1}` commutes with the transports of both indices. -/
theorem mssProjMul_pd_proj_pCast (r : ℕ) {s s' n n' : ℕ} (h1 : s = s') (h2 : n = n')
    (x : ↥(LinearMap.ker (pD 𝕜 W r s n).hom)) (y : ↥(LinearMap.ker (pD 𝕜 W r s' n').hom))
    (hy : (y : pEraw 𝕜 W r s' n') = pCast 𝕜 W r h1 h2 x) :
    pd_proj 𝕜 W r s' n' y = pCast 𝕜 W (r+1) h1 h2 (pd_proj 𝕜 W r s n x) := by
  cases h1
  cases h2
  rw [pCast_apply_self] at hy
  obtain rfl : y = x := Subtype.ext hy
  rw [pCast_apply_self]

/-- The index transports preserve cycles of the differential. -/
theorem mssProjMul_pD_pCast_eq_zero (r : ℕ) {s s' n n' : ℕ} (h1 : s = s') (h2 : n = n')
    (x : pEraw 𝕜 W r s n) (hx : (pD 𝕜 W r s n).hom x = 0) :
    (pD 𝕜 W r s' n').hom (pCast 𝕜 W r h1 h2 x) = 0 := by
  cases h1
  cases h2
  rw [pCast_apply_self, hx]

theorem mssProjMul (𝕜 : Type) [Field 𝕜] (W : Work.Pi6.MSS.CohFilt 𝕜) (r : ℕ) (hr : 2 ≤ r)
    (a b c : ℤ × ℤ) (h : a + b = c)
    (x : ↥(LinearMap.ker (Work.Pi6.MSS.mssD 𝕜 W r a (a + Work.Pi6.vr r)).hom))
    (y : ↥(LinearMap.ker (Work.Pi6.MSS.mssD 𝕜 W r b (b + Work.Pi6.vr r)).hom))
    (z : ↥(LinearMap.ker (Work.Pi6.MSS.mssD 𝕜 W r c (c + Work.Pi6.vr r)).hom))
    (hz : (z : Work.Pi6.MSS.mssE 𝕜 W r c) = Work.Pi6.MSS.mssMul 𝕜 W r a b c h x y) :
    Work.Pi6.MSS.mssProj 𝕜 W r c z
      = Work.Pi6.MSS.mssMul 𝕜 W (r + 1) a b c h (Work.Pi6.MSS.mssProj 𝕜 W r a x)
          (Work.Pi6.MSS.mssProj 𝕜 W r b y) := by
  obtain rfl : c = a + b := h.symm
  rw [mssMul_congr 𝕜 W r a b (a + b) h rfl x y] at hz
  rw [mssMul_congr 𝕜 W (r + 1) a b (a + b) h rfl (mssProj 𝕜 W r a x) (mssProj 𝕜 W r b y)]
  by_cases ha : Enn a
  · by_cases hb : Enn b
    · -- the two products are honest products of the first quadrant
      have hxmem : x.1 ∈ LinearMap.ker (pD 𝕜 W r (EI a) (EN a)).hom :=
        mssProjAux_mem 𝕜 W r hr a (mssKerIncl 𝕜 W r a x)
      have hymem : y.1 ∈ LinearMap.ker (pD 𝕜 W r (EI b) (EN b)).hom :=
        mssProjAux_mem 𝕜 W r hr b (mssKerIncl 𝕜 W r b y)
      have hxker : (pD 𝕜 W r (EI a) (EN a)).hom x.1 = 0 := LinearMap.mem_ker.mp hxmem
      have hyker : (pD 𝕜 W r (EI b) (EN b)).hom y.1 = 0 := LinearMap.mem_ker.mp hymem
      have hwmem : (pD 𝕜 W r (EI a + EI b) (EN a + EN b)).hom
          (pd_mul r (EI a) (EN a) (EI b) (EN b) x.1 y.1) = 0 := by
        rw [pd_mul_leib r (EI a) (EN a) (EI b) (EN b) (by omega) (by omega) (by omega) (by omega)
          x.1 y.1, hxker, hyker]
        simp
      have hzsrc : (z : pEraw 𝕜 W r (EI (a+b)) (EN (a+b)))
          = pCast 𝕜 W r (EI_add ha hb) (EN_add ha hb)
              (pd_mul r (EI a) (EN a) (EI b) (EN b) x.1 y.1) := by
        rw [hz]
        exact mssProjMul_mul_step 𝕜 W r ha hb x y
      have hzpD : (pD 𝕜 W r (EI (a+b)) (EN (a+b))).hom
          (z : pEraw 𝕜 W r (EI (a+b)) (EN (a+b))) = 0 := by
        rw [hzsrc]
        exact mssProjMul_pD_pCast_eq_zero 𝕜 W r (EI_add ha hb) (EN_add ha hb)
          ((pd_mul r (EI a) (EN a) (EI b) (EN b)) x.1 y.1) hwmem
      have hL : mssProj 𝕜 W r (a+b) z
          = pCast 𝕜 W (r+1) (EI_add ha hb) (EN_add ha hb)
              (pd_proj 𝕜 W r (EI a + EI b) (EN a + EN b)
                ⟨(pd_mul r (EI a) (EN a) (EI b) (EN b)) x.1 y.1, hwmem⟩) := by
        rw [mssProjMul_proj_val 𝕜 W r hr (a+b) z]
        exact mssProjMul_pd_proj_pCast 𝕜 W r (EI_add ha hb) (EN_add ha hb)
          ⟨(pd_mul r (EI a) (EN a) (EI b) (EN b)) x.1 y.1, hwmem⟩
          ⟨(z : pEraw 𝕜 W r (EI (a+b)) (EN (a+b))), hzpD⟩ hzsrc
      have hR : mssMul 𝕜 W (r+1) a b (a+b) rfl (mssProj 𝕜 W r a x) (mssProj 𝕜 W r b y)
          = pCast 𝕜 W (r+1) (EI_add ha hb) (EN_add ha hb)
              (pd_mul (r+1) (EI a) (EN a) (EI b) (EN b)
                (pd_proj 𝕜 W r (EI a) (EN a) ⟨x.1, hxmem⟩)
                (pd_proj 𝕜 W r (EI b) (EN b) ⟨y.1, hymem⟩)) := by
        rw [mssProjMul_proj_val 𝕜 W r hr a x, mssProjMul_proj_val 𝕜 W r hr b y]
        rw [mssProjMul_mul_step 𝕜 W (r + 1) ha hb _ _]
      have hpm := pd_proj_mul (𝕜 := 𝕜) (W := W) r hr (EI a) (EN a) (EI b) (EN b)
        ⟨x.1, hxmem⟩ ⟨y.1, hymem⟩
        ⟨(pd_mul r (EI a) (EN a) (EI b) (EN b)) x.1 y.1, hwmem⟩ rfl
      have hcast := congrArg (fun t => pCast 𝕜 W (r+1) (EI_add ha hb) (EN_add ha hb) t) hpm
      rw [hL, hR]
      exact hcast
    · -- the right factor is outside the first quadrant: both products vanish
      have hz0 : (z : mssE 𝕜 W r (a + b)) = 0 := by
        rw [hz, mssProjMul_mul_rfl 𝕜 W r a b, mssMulRaw_neg' 𝕜 W r ha hb]
        rfl
      rw [show z = 0 from Subtype.ext hz0, map_zero, mssProjMul_mul_rfl 𝕜 W (r + 1) a b,
        mssMulRaw_neg' 𝕜 W (r + 1) ha hb]
      rfl
  · -- the left factor is outside the first quadrant: both products vanish
    have hz0 : (z : mssE 𝕜 W r (a + b)) = 0 := by
      rw [hz, mssProjMul_mul_rfl 𝕜 W r a b, mssMulRaw_neg 𝕜 W r ha]
      rfl
    rw [show z = 0 from Subtype.ext hz0, map_zero, mssProjMul_mul_rfl 𝕜 W (r + 1) a b,
      mssMulRaw_neg 𝕜 W (r + 1) ha]
    rfl

end

end Work.Pi6.MSS
