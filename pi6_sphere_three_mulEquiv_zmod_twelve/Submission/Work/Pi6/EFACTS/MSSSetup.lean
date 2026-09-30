import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EFACTS.Basic
import Submission.Work.RatHurewicz.isEMSpaceUpTo_pi_fin
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The setup of the Serre spectral sequence of `proj g3 : Ecov g3 → SphModel 3`

`Work.Pi6.MSSHolds` produces a spectral sequence for a Serre fibration `p : E → B` at a *chosen*
point `e₀ : E`, whose fibre is `Work.StemsB.fibre p (p e₀)`.  Downstream we want to use the fibre
facts available for `Work.Pi6.EFACTS.fib g3 = (proj g3) ⁻¹' {∞}`, which is only *propositionally*
the fibre over `proj g3 (mssPt g3)` (the two subtypes have the same underlying set but different
proof terms in the predicate).

This file fixes the base point `mssPt g3` (the underlying point of `fibPt g3`), names the fibre
`mssFib g3` of the spectral sequence, and records the canonical homeomorphism
`mssFib g3 ≃ₜ fib g3`.  It also contains two generic facts about the abstract `CohSS` interface:
the column-`0` maps `col` are injective (they are sections of `proj`), and so are their iterates
`colTo`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EFACTS

noncomputable section

/-- The base point of `Ecov g3` at which the Serre spectral sequence of `proj g3` is set up: the
underlying point of the chosen point `fibPt g3` of the fibre over `∞`. -/
def mssPt {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3)) : Work.Pi6.Ecov g3 :=
  (fibPt g3).1

/-- `mssPt g3` projects to `∞`, hence `fib g3` is propositionally the fibre over it. -/
theorem mssPt_proj {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3)) :
    proj g3 (mssPt g3) = OnePoint.infty :=
  (fibPt g3).2

/-- The fibre in which the Serre spectral sequence of `proj g3` over `mssPt g3` lives. -/
abbrev mssFib {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3)) : Type :=
  Work.StemsB.fibre (proj g3) (proj g3 (mssPt g3))

/-- The base point of `mssFib g3`, i.e. the fibre point of `mssPt g3`. -/
def mssFibPt {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3)) : mssFib g3 :=
  Work.StemsB.fibrePoint (proj g3) (mssPt g3)

/-- **The canonical homeomorphism `mssFib g3 ≃ₜ fib g3`**: the two subtypes have the same
underlying set, because `proj g3 (mssPt g3) = ∞`. -/
def mssFibHomeo {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3)) :
    mssFib g3 ≃ₜ fib g3 where
  toFun q := ⟨q.1, by simpa using q.2.trans (mssPt_proj g3)⟩
  invFun q := ⟨q.1, by simpa using q.2.trans (mssPt_proj g3).symm⟩
  left_inv q := Subtype.ext rfl
  right_inv q := Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val _

/-- The homeomorphism `mssFib g3 ≃ₜ fib g3` sends `mssFibPt g3` to `fibPt g3`. -/
theorem mssFibHomeo_mssFibPt {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3)) :
    mssFibHomeo g3 (mssFibPt g3) = fibPt g3 :=
  Subtype.ext rfl

/-- **The `K(ℤ,2)`-structure of the fibre transports to `mssFib g3`.** -/
theorem mssFibModel {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3))
    (hfib : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 11 (fib g3) (fibPt g3)) :
    Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 11 (mssFib g3) (mssFibPt g3) := by
  have h := Work.RatHurewicz.isEMSpaceUpTo_of_homeomorph (A := ℤ) (k := 2) (N := 11)
    (by norm_num) (mssFibHomeo g3).symm (fibPt g3) hfib
  have hpt : (mssFibHomeo g3).symm (fibPt g3) = mssFibPt g3 := by
    rw [← mssFibHomeo_mssFibPt g3, Homeomorph.symm_apply_apply]
  rwa [hpt] at h

end

end Work.Pi6.EFACTS

namespace Work.Pi6

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CohSS

variable {𝕜 : Type} [Field 𝕜]

/-- The column-`0` map `col r q` is injective: it is a section of `proj`. -/
theorem col_injective (S : CohSS 𝕜) (r : ℕ) (hr : 2 ≤ r) (q : ℤ) :
    Function.Injective (S.col r q).hom := by
  intro y y' hyy
  -- write `y = proj x`, `y' = proj x'` for cycles `x`, `x'`
  obtain ⟨x, hx⟩ := S.proj_surj r (0, q) hr y
  obtain ⟨x', hx'⟩ := S.proj_surj r (0, q) hr y'
  have h1 : (S.col r q).hom y = (x : S.E r (0, q)) := by
    rw [← hx, S.col_spec r q x hr]
  have h2 : (S.col r q).hom y' = (x' : S.E r (0, q)) := by
    rw [← hx', S.col_spec r q x' hr]
  have hxx' : x = x' := Subtype.ext (by rw [← h1, ← h2, hyy])
  rw [← hx, ← hx', hxx']

/-- The iterated column-`0` maps `colTo q k : E_{k+2}^{0,q} → E_2^{0,q}` are injective. -/
theorem colTo_injective (S : CohSS 𝕜) (q : ℤ) (k : ℕ) :
    Function.Injective (S.colTo q k).hom := by
  induction k with
  | zero => intro x y h; exact h
  | succ k ih =>
      have hstep : (S.colTo q (k + 1)).hom
          = (S.colTo q k).hom ∘ (S.col (k + 2) q).hom := rfl
      rw [hstep]
      exact ih.comp (S.col_injective (k + 2) (by omega) q)

end CohSS

end

end Work.Pi6
