/-
# `SZ(GF(2^(2n))) ≅ Ū ≤ PSU(3,2ⁿ)` (design node D1b)

The Sylow `2`-subgroup `Ū` of `PSU(3, 2ⁿ)` is the image of the unipotent radical
`U ≤ SU(3,2ⁿ)` under the projection `SU(3,2ⁿ) → PSU(3,2ⁿ)`.  The matrix model of the
Bender–Suzuki group of case c (`Work.PSU3.matGL`, `Work.PSU3.pglHom`) sends
`p = (x,y) ∈ SZ E` to the unitriangular matrix `A(x,y) = !![1,x,y; 0,1,x^q; 0,0,1]`,
which is exactly `suUmat n x y`; the Hermitian relation `y + y^q = x^{1+q}` is precisely the
condition defining `suU n`.  Since `pglHom` is injective (`pglHom_injective`) and every element
of `suU n` is of the shape `suUmat n b c`, the map is a bijection onto `Ū`, hence an
isomorphism `SZ E ≃* Ū`.

The isomorphism is the `MonoidHom` `uEquivHom`, obtained by restricting `pglHom` first to
`PSU3Model n` and then to `psu3U n`; injectivity comes from `pglHom_injective` and
surjectivity from the explicit parametrisation of `suU n` by `(b,c)`.
-/
import Mathlib
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.PSU3.ModelGL
import Submission.Work.PSU3.ModelGL.Injectivity
import Submission.Work.PSU3.GaloisField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs

namespace Work.PSU3.Model

/-- The distinguished Frobenius involution of `E = GF(2^(2n))` is `x ↦ x^(2ⁿ)`; the equality is
definitional, `σE = iterateFrobenius E 2 n = powMonoidHom (2^n)`. -/
lemma sigmaE_eq_pow (n : ℕ) (x : GaloisField 2 (2 * n)) : σE x = x ^ 2 ^ n := rfl

/-- The matrix `matOfXY x y` of the `SZ` model is the matrix `suUmat n x y` of the `PSU3` model:
both are `!![1, x, y; 0, 1, x^(2^n); 0, 0, 1]`. -/
lemma matOfXY_eq_suUmat (n : ℕ) (x y : GaloisField 2 (2 * n)) :
    matOfXY x y = Submission.PSU3.suUmat n x y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matOfXY, Submission.PSU3.suUmat, sigmaE_eq_pow]

/-- The matrix of `⟨x,y,h⟩ ∈ SZ E` is `suUg n x y`. -/
lemma matGL_mk_eq_suUg (n : ℕ) (x y : GaloisField 2 (2 * n))
    (h : y + σE y = x * σE x) :
    matGL (⟨x, y, h⟩ : SZ (GaloisField 2 (2 * n))) = Submission.PSU3.suUg n x y := by
  apply Units.ext
  simp only [matGL_coe, matFun_apply, Submission.PSU3.suUg_coe, matOfXY_eq_suUmat]

/-- The matrix model of `SZ E` lands in the unipotent radical `U ≤ SU(3,2ⁿ)`: the Hermitian
relation `y + y^q = x^{1+q}` of `SZ E` is exactly the condition `suU n` imposes on the
parameters `(b,c) = (x,y)`. -/
lemma matGL_mem_suU (n : ℕ) (p : SZ (GaloisField 2 (2 * n))) :
    matGL p ∈ Submission.PSU3.suU n := by
  refine ⟨p.x, p.y, ?_, ?_⟩
  · simpa [pow_succ', sigmaE_eq_pow] using p.herm
  · have : p = ⟨p.x, p.y, p.herm⟩ := rfl
    rw [this]
    exact matGL_mk_eq_suUg n p.x p.y p.herm

/-- `pglHom` lands in `PSU3Model n`. -/
lemma pglHom_mem_PSU3Model (n : ℕ) (p : SZ (GaloisField 2 (2 * n))) :
    pglHom p ∈ PSU3Model n := by
  rw [Submission.PSU3.PSU3Model_eq_map_SU3]
  exact Subgroup.mem_map.mpr ⟨matGL p, Submission.PSU3.suU_le_SU3 n (matGL_mem_suU n p),
    (pglHom_apply p).symm⟩

/-- `pglHom` lands in the Sylow `2`-subgroup `Ū = psu3U n` of `PSU(3,2ⁿ)`. -/
lemma pglHom_mem_psu3U (n : ℕ) (p : SZ (GaloisField 2 (2 * n))) :
    (⟨pglHom p, pglHom_mem_PSU3Model n p⟩ : ↥(PSU3Model n)) ∈ Submission.PSU3.psu3U n := by
  refine Subgroup.mem_map.mpr ⟨⟨matGL p, Submission.PSU3.suU_le_SU3 n (matGL_mem_suU n p)⟩,
    ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact matGL_mem_suU n p
  · apply Subtype.ext
    show ProjGenLinGroup.mk (matGL p) = pglHom p
    rw [pglHom_apply]

/-- The matrix model restricted to `Ū ≤ PSU(3,2ⁿ)`, as a monoid homomorphism
`SZ E →* Ū`. -/
noncomputable def uEquivHom (n : ℕ) :
    SZ (GaloisField 2 (2 * n)) →* ↥(Submission.PSU3.psu3U n) :=
  ((pglHom.codRestrict (PSU3Model n) (pglHom_mem_PSU3Model n)).codRestrict
    (Submission.PSU3.psu3U n) (pglHom_mem_psu3U n))

/-- The underlying element of `uEquivHom n p` in `PGL(3,E)` is `pglHom p`. -/
lemma uEquivHom_apply (n : ℕ) (p : SZ (GaloisField 2 (2 * n))) :
    ((uEquivHom n p : ↥(Submission.PSU3.psu3U n)) :
        ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * n))) = pglHom p := rfl

/-- **`SZ(GF(2^(2n)))` is isomorphic to the unipotent radical `Ū` of `PSU(3,2ⁿ)`** (design
node D1b).  The isomorphism is the injective matrix model `pglHom`, whose image is precisely
`Ū` by the explicit parametrisation of the unipotent radical. -/
theorem psu3_uEquiv (n : ℕ) (hn : 2 ≤ n) :
    Nonempty (SZ (GaloisField 2 (2 * n)) ≃* (Submission.PSU3.psu3BenderPair n hn).U) := by
  change Nonempty (SZ (GaloisField 2 (2 * n)) ≃* ↥(Submission.PSU3.psu3U n))
  refine ⟨MulEquiv.ofBijective (uEquivHom n) ⟨?_, ?_⟩⟩
  · intro p q hpq
    apply pglHom_injective
    rw [← uEquivHom_apply n p, ← uEquivHom_apply n q, hpq]
  · intro g
    obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.mp g.2
    obtain ⟨b, c, hcond, hyb⟩ := (Subgroup.mem_subgroupOf.mp hy :
      (y : GL (Fin 3) (GaloisField 2 (2 * n))) ∈ Submission.PSU3.suU n)
    have hh : c + σE c = b * σE b := by
      show c + c ^ 2 ^ n = b * b ^ 2 ^ n
      simpa [pow_succ'] using hcond
    refine ⟨⟨b, c, hh⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [uEquivHom_apply, pglHom_apply, matGL_mk_eq_suUg n b c hh]
    rw [← hyb, ← congrArg Subtype.val hys, Submission.PSU3.psu3Hom_apply]

end Work.PSU3.Model
