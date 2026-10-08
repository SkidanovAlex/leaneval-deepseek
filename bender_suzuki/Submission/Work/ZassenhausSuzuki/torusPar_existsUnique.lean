import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.suzukiFProp
import Submission.Work.ZassenhausSuzuki.SzA.hLamHom_injective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- **Existence and uniqueness of the torus parameter with prescribed conjugating action.**

Under the torus hypothesis `htorus` on the coordinatisation `e : Q ≃* A(K,θ)`, every element
`d` of the two-point stabiliser `D = twoPoint H t` acts on `Q` (transported to `A(K,θ)` by `e`)
through the standard torus; the parameter `λ ∈ Kˣ` is determined by `d`.

* Existence is exactly the content of `TorusCoords`: the witness `y` supplied there for the
  element `x` is `e.symm (h_λ (e x))`, because `e` is a bijection.
* Uniqueness: two parameters `λ, μ` inducing the same action on all of `Q` induce the same
  action of `h_λ` and `h_μ` on all of `A(K,θ)` (since `e` is surjective), and evaluating at
  `(1,0)` gives `λ = μ` — the same argument as `SzA.hLamHom_injective`. -/
theorem torusPar_existsUnique {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K} {e : Q ≃* Work.ZassenhausSuzuki.SzA K θ}
    (htorus : Work.ZassenhausSuzuki.TorusCoords K θ H Q t e) {d : G}
    (hd : d ∈ Submission.Blueprint.twoPoint H t) :
    ∃! lam : Kˣ, ∀ x : Q,
      (((e.symm (Work.ZassenhausSuzuki.SzA.hLam θ (lam : K) (e x)) : Q)) : G)
        = d * (x : G) * d⁻¹ := by
  obtain ⟨lam, hlam⟩ := htorus d hd
  have hP : ∀ x : Q,
      (((e.symm (SzA.hLam θ (lam : K) (e x)) : Q)) : G) = d * (x : G) * d⁻¹ := by
    intro x
    obtain ⟨y, hy, hye⟩ := hlam x
    have hys : e.symm (SzA.hLam θ (lam : K) (e x)) = y := by
      rw [← hye, MulEquiv.symm_apply_apply]
    rw [hys]; exact hy
  refine ⟨lam, hP, ?_⟩
  intro mu hmu
  have hkey : ∀ z : SzA K θ, SzA.hLam θ (mu : K) z = SzA.hLam θ (lam : K) z := by
    intro z
    have heq : e.symm (SzA.hLam θ (mu : K) (e (e.symm z)))
        = e.symm (SzA.hLam θ (lam : K) (e (e.symm z))) :=
      Subtype.ext (by rw [hmu (e.symm z), hP (e.symm z)])
    have := congrArg e heq
    simpa using this
  have hz := hkey (⟨1, 0⟩ : SzA K θ)
  have : (mu : K) = (lam : K) := by
    simpa using congrArg SzA.a hz
  exact Units.ext this

end Work.ZassenhausSuzuki
