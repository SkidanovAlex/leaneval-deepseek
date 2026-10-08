import Mathlib
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.torusLambda_surjective_of_split

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The central involutions `zc e b` (b ≠ 0) are conjugate under `D = twoPoint H t`

In a split rank-one Zassenhaus configuration whose root group `Q` is coordinatised as Higman's
group `A(K,θ) = SzA K θ` (`K = GF(2^m)`, `θ ≠ 1` of odd order) and in which the two-point
stabiliser `D = H ⊓ H^t` acts on `Q` through the torus `Λ = h(Kˣ)` (`htorus`), the *central*
involutions of `Q` are the elements `zc e b` with `b ∈ Kˣ`, and any two of them are conjugate
by an element of `D`.

Indeed the torus element `h_λ` acts on the centre by `h_λ (0,b) = (0, λ·θλ·b)`, and
`λ ↦ λ·θλ` is a bijection of `Kˣ` (`TitsAux.units_mul_map_surjective`, via
`units_mul_map_injective` with `orderOf θ` odd); so choosing `λ` with `λ·θλ = b / b₀` and
transporting `λ` to an element `d ∈ D` (`torusLambda_surjective_of_split`) conjugates
`zc e b₀` into `zc e b`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

theorem szTildeConjZc {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {b0 b : GaloisField 2 m} (hb0 : b0 ≠ 0) (hb : b ≠ 0) :
    ∃ d : G, d ∈ Submission.Blueprint.twoPoint H t ∧
      ((Work.ZassenhausSuzuki.zc e b : Q) : G) = d * ((Work.ZassenhausSuzuki.zc e b0 : Q) : G) * d⁻¹ := by
  classical
  -- The torus parameter `λ` with `λ · θ λ = b / b₀`: the map `λ ↦ λ·θλ` is surjective on `Kˣ`.
  obtain ⟨lam, hlam⟩ :=
    units_mul_map_surjective θ hθodd (Units.mk0 (b / b0) (div_ne_zero hb hb0))
  have hlamK : (lam : GaloisField 2 m) * θ (lam : GaloisField 2 m) = b / b0 := by
    have h := congrArg (fun u : (GaloisField 2 m)ˣ => (u : GaloisField 2 m)) hlam
    simpa [Units.val_mul] using h
  have hvalK : (lam : GaloisField 2 m) * θ (lam : GaloisField 2 m) * b0 = b := by
    rw [hlamK, div_mul_cancel₀ b hb0]
  -- Transport `λ` to an element `d ∈ D` realising `h_λ` on `Q`.
  obtain ⟨d, hd, hdact⟩ :=
    torusLambda_surjective_of_split hsplit hzass h2 (K := GaloisField 2 m) (θ := θ) (e := e)
      htorus lam
  refine ⟨d, hd, ?_⟩
  -- `h_λ` fixes the centre up to the factor `λ·θλ`, so it sends `zc e b₀` to `zc e b`.
  have hkey : e.symm (SzA.hLam θ (lam : GaloisField 2 m) (e (zc e b0))) = zc e b := by
    rw [zc_coe e b0]
    have h2 : SzA.hLam θ (lam : GaloisField 2 m) (⟨0, b0⟩ : SzA (GaloisField 2 m) θ) = ⟨0, b⟩ := by
      ext <;> simp [SzA.hLam_a, SzA.hLam_b, hvalK]
    rw [h2]
    rfl
  rw [← hkey]
  exact hdact (zc e b0)

end Work.ZassenhausSuzuki
