import Mathlib
import Submission.Work.ZassenhausSuzuki.ttc_defs
import Submission.Work.ZassenhausSuzuki.TitsAux
import Submission.Work.ZassenhausSuzuki.torusLambda_surjective_of_split

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

open Submission.Blueprint

/-- **The `TorusCoords` scalar is determined by the action.**  If `d ∈ D` acts on `Q` through
`h_λ` *in the sense of `torusLambda_surjective_of_split`* (i.e. `e.symm ∘ h_λ ∘ e` is the
conjugation by `d`), then the scalar `lamOf hsplit htorus ⟨d, hdD⟩` attached to `d` at the value
`⟨d, hdD⟩` of `htorus` is `λ`.  Compare the two actions at `e.symm ⟨1,0⟩` and read off the
`a`-coordinate (`SzA.hLam_a`). -/
theorem lamOf_eq_of_action {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m}
    {e : Q ≃* SzA (GaloisField 2 m) θ}
    (hsplit : IsSplitRankOne H Q t)
    (htorus : TorusCoords (GaloisField 2 m) θ H Q t e)
    {d : G} (hdD : d ∈ twoPoint H t) {lam : (GaloisField 2 m)ˣ}
    (hdact : ∀ x : Q, (((e.symm (SzA.hLam θ (lam : GaloisField 2 m) (e x)) : Q)) : G)
      = d * (x : G) * d⁻¹) :
    lamOf hsplit htorus (⟨d, hdD⟩ : ↥(twoPoint H t)) = lam := by
  apply Units.ext
  have hkey : SzA.hLam θ ((lamOf hsplit htorus (⟨d, hdD⟩ : ↥(twoPoint H t)) : GaloisField 2 m))
        (⟨1, 0⟩ : SzA (GaloisField 2 m) θ)
      = SzA.hLam θ (lam : GaloisField 2 m) (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) := by
    have hx := hdact (e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ))
    simp only [MulEquiv.apply_symm_apply] at hx
    have hx' : e.symm (SzA.hLam θ (lam : GaloisField 2 m) (⟨1, 0⟩ : SzA (GaloisField 2 m) θ))
        = conjQ hsplit (⟨d, hdD⟩ : ↥(twoPoint H t))
            (e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ)) := by
      apply Subtype.ext
      rw [hx, conjQ_coe]
    have h2 := congrArg e hx'
    rw [MulEquiv.apply_symm_apply, lamOf_spec hsplit htorus (⟨d, hdD⟩ : ↥(twoPoint H t))
      (e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ)), MulEquiv.apply_symm_apply] at h2
    exact h2.symm
  have h := congrArg SzA.a hkey
  simpa using h

/-- **Every non-zero index is a `D`-multiplier.**  For `w ≠ 0` there is `d ∈ D = twoPoint H t`
with `mulD hsplit htorus d = w` (the multiplier of `d` on the centre `Z(Q)`, `ttc_defs`).

Route: `units_mul_map_surjective θ hθodd` (`Submission/Work/ZassenhausSuzuki/TitsAux.lean`,
available with exactly the hypothesis `Odd (orderOf θ)`) gives `λ ∈ Kˣ` with `λ·θλ = w`; then
`torusLambda_surjective_of_split` (`Submission/Work/ZassenhausSuzuki/torusLambda_surjective_of_split.lean`,
needs `hsplit, hzass, h2, htorus`) gives `d ∈ D` acting on `Q` through `h_λ`.  For such a `d`,
`lamOf_eq_of_action` above shows `lamOf hsplit htorus d = λ`, so
`mulD hsplit htorus d = λ·θλ = w`. -/
theorem exists_mulD_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {w : GaloisField 2 m} (hw : w ≠ 0) :
    ∃ d : Submission.Blueprint.twoPoint H t, Work.ZassenhausSuzuki.mulD hsplit htorus d = w := by
  classical
  -- (1) a unit `λ` with `λ · θ λ = w` (surjectivity of the `θ`-norm on `Kˣ`).
  obtain ⟨lam, hlam⟩ := units_mul_map_surjective θ hθodd (Units.mk0 w hw)
  have hlamK : (lam : GaloisField 2 m) * θ (lam : GaloisField 2 m) = w := by
    have h := congrArg (fun u : (GaloisField 2 m)ˣ => (u : GaloisField 2 m)) hlam
    simpa [Units.val_mul, Units.coe_map] using h
  -- (2) an element `d ∈ D` acting on `Q` through `h_λ`.
  obtain ⟨d, hdD, hdact⟩ := torusLambda_surjective_of_split hsplit hzass h2 htorus lam
  refine ⟨⟨d, hdD⟩, ?_⟩
  -- (3) the `TorusCoords` scalar of `d` is `λ`, hence `mulD d = λ · θ λ = w`.
  have hlamOf := lamOf_eq_of_action hsplit htorus hdD hdact
  unfold mulD
  rw [hlamOf, hlamK]

end Work.ZassenhausSuzuki
