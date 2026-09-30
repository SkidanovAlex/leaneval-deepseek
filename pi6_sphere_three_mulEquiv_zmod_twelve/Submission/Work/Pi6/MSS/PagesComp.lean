import Mathlib
import Submission.Work.Pi6.MSS.pagesData
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The page-1 row complex `E1Row`

* `Work.Pi6.MSS.pD_comp` — the differential of the pages squares to zero.
* `Work.Pi6.MSS.E1Row 𝕜 W q` — the row complex `s ↦ E_1^{s,q}` of the spectral sequence of a
  filtered cochain complex with a product, with differential `d_1 = pD 1`, in total degree `s + q`.
  The cohomological degree is written `q + s` (rather than `s + q`) so that the differential is
  cast-free.
-/

set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜}

/-- **The differential of the pages squares to zero.** -/
theorem pD_comp (r s n : ℕ) :
    pD 𝕜 W r s n ≫ pD 𝕜 W r (s + r) (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ :=
    Submodule.mkQ_surjective ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) y
  show (pD 𝕜 W r (s + r) (n + 1)).hom
      ((pD 𝕜 W r s n).hom
        (Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) x)) = 0
  rw [pd_pD_apply (𝕜 := 𝕜) (W := W) r s n x,
    pd_pD_apply (𝕜 := 𝕜) (W := W) r (s + r) (n + 1) (pZmap 𝕜 W r s n x)]
  have hz : pZmap 𝕜 W r (s + r) (n + 1) (pZmap 𝕜 W r s n x) = 0 := by
    apply Subtype.ext
    rw [pd_pZmap_apply (𝕜 := 𝕜) (W := W) r (s + r) (n + 1) (pZmap 𝕜 W r s n x),
      pd_pZmap_apply (𝕜 := 𝕜) (W := W) r s n x]
    exact pd_d_comp_d_apply (W := W) n (x : W.C.X n)
  rw [hz]
  rfl

/-- **The `E_1` row complex** `s ↦ E_1^{s,q}` (in total degree `q + s`), with differential `d_1`. -/
def E1Row (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (q : ℕ) : CochainComplex (ModuleCat 𝕜) ℕ :=
  CochainComplex.of (fun s => pEraw 𝕜 W 1 s (q + s))
    (fun s => pD 𝕜 W 1 s (q + s))
    (fun s => pD_comp (𝕜 := 𝕜) (W := W) 1 s (q + s))

@[simp] theorem E1Row_X (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (q s : ℕ) :
    (E1Row 𝕜 W q).X s = pEraw 𝕜 W 1 s (q + s) := rfl

@[simp] theorem E1Row_d (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (q s : ℕ) :
    (E1Row 𝕜 W q).d s (s + 1) = pD 𝕜 W 1 s (q + s) := by
  simp only [E1Row, CochainComplex.of_d]

end

end Work.Pi6.MSS
