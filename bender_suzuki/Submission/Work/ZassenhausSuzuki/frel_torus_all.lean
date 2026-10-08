import Mathlib
import Submission.Work.ZassenhausSuzuki.CoreV3
import Submission.Work.ZassenhausSuzuki.suzukiFProp
import Submission.Work.ZassenhausSuzuki.twoPoint_card_eq_involutions
import Submission.Work.ZassenhausSuzuki.twoPoint_inverted
import Submission.Work.ZassenhausSuzuki.frel_torus_inv
import Submission.Work.ZassenhausSuzuki.SzA.ncard_orderOf_eq_two
import Submission.Work.ZassenhausSuzuki.ncard_involutions_of_mulEquiv
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q
import Submission.Work.RankOneUniqueness.f_exists
import Submission.Work.RankOneUniqueness.f_unique
import Submission.Work.ZassenhausSuzuki.SzA.sq_eq
import Submission.Work.ZassenhausSuzuki.SzA.mem_center_iff
import Submission.Work.ZassenhausSuzuki.SzA.hLamHom_injective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `frel_torus_all`: the book's `f`-relation is equivariant under the whole torus `Kˣ`

The target is the "all in one" form of `Work.ZassenhausSuzuki.frel_torus_inv`.  The hypothesis
`TorusCoords K θ H Q t e` only records that every `d ∈ D = twoPoint H t` acts on the root group
`Q` through *some* torus element `h_λ` (`λ = λ(d)`, a map `D → Kˣ`); it does **not** say that
this map is surjective.  The point of this file is the missing rigidity:

> `|D| = #Inv(Q) = |K| - 1 = |Kˣ|` (`twoPoint_card_eq_involutions` plus the count of involutions
> of `A(K,θ)`, which are the `⟨0,b⟩`, `b ≠ 0`), and the map `d ↦ λ(d)` is injective
> (`h_λ` determines `λ` by `SzA.hLamHom_injective`, and `d` is determined by its action on `Q`
> by `dStab_fpf_on_Q`); hence it is **bijective**.

So for *every* `λ` there is `d ∈ D` realising `h_λ` on `Q` (`torusLambda_surjective`), and the
torus equivariance of `f` is `frel_torus_inv` (`frel_conj` + `hLam_inv_act`):
`FRel H t x y → FRel H t (h_λ x) (h_{λ⁻¹} y)`.

`Q ≠ ⊥` is not a hypothesis: `Q ≃* A(K,θ)` shows that `SzA K θ` is finite (so `K` is a finite
field of characteristic two) and non-trivial, whence `Q` is.  Likewise `IsPGroup 2 Q` needs no
hypothesis: `A(K,θ)` has exponent `4` in characteristic two (`x² = ⟨0, a·θ a⟩` is an
involution), and `IsPGroup` transports along `e`.
-/

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-! ## Surjectivity of the torus map `D → Kˣ` -/

/-- **Every torus element is realised on `Q` by an element of `D = twoPoint H t`.**

The map `d ↦ λ(d)` supplied by `TorusCoords` is injective: `h_λ = h_μ` forces `λ = μ`
(`SzA.hLamHom_injective`), and if two elements of `D` induce the same automorphism of `Q` then
their quotient centralises `Q` and hence is trivial (`dStab_fpf_on_Q`, using `Q ≠ ⊥`).  It is
therefore a bijection between the finite sets `D` and `Kˣ` (of equal cardinality `|D| = |Kˣ|`),
so it is onto. -/
theorem torusLambda_surjective {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    {K : Type} [Field K] [Finite K] {θ : K ≃+* K} {e : Q ≃* SzA K θ}
    (htorus : TorusCoords K θ H Q t e) (hQ : Q ≠ ⊥)
    (hcard : Nat.card ↥(twoPoint H t) = Nat.card Kˣ) (lam : Kˣ) :
    ∃ d ∈ twoPoint H t, ∀ x : Q,
      (((e.symm (SzA.hLam θ (lam : K) (e x)) : Q)) : G) = d * (x : G) * d⁻¹ := by
  classical
  haveI : Finite Kˣ :=
    Finite.of_injective (fun u : Kˣ => (u : K)) (fun a b hab => Units.ext hab)
  -- the map `D → Kˣ` extracted from the torus condition
  let φ : ↥(twoPoint H t) → Kˣ := fun d => Classical.choose (htorus (d : G) d.2)
  have hφ : ∀ d : ↥(twoPoint H t), ∀ x : Q, ∃ y : Q,
      (y : G) = (d : G) * (x : G) * (d : G)⁻¹ ∧
        e y = SzA.hLam θ ((φ d : Kˣ) : K) (e x) :=
    fun d => Classical.choose_spec (htorus (d : G) d.2)
  -- `φ d` realises `h_{φ d}` by conjugation with `d`
  have hact : ∀ d : ↥(twoPoint H t), ∀ x : Q,
      (((e.symm (SzA.hLam θ ((φ d : Kˣ) : K) (e x)) : Q)) : G)
        = (d : G) * (x : G) * (d : G)⁻¹ := by
    intro d x
    obtain ⟨y, hy, hye⟩ := hφ d x
    have hyy : e.symm (SzA.hLam θ ((φ d : Kˣ) : K) (e x)) = y := by
      rw [← hye]
      exact e.symm_apply_apply y
    rw [hyy]
    simpa using hy
  -- `d` is determined by its action on `Q`
  have hinj : Function.Injective φ := by
    intro d d' hdd
    have hactG : ∀ x : G, x ∈ Q →
        (d : G) * x * (d : G)⁻¹ = (d' : G) * x * (d' : G)⁻¹ := by
      intro x hx
      have h1 := hact d ⟨x, hx⟩
      have h2 := hact d' ⟨x, hx⟩
      rw [hdd] at h1
      exact h1.symm.trans h2
    have hcen : ∀ x : G, x ∈ Q →
        ((d' : G)⁻¹ * (d : G)) * x * ((d' : G)⁻¹ * (d : G))⁻¹ = x := by
      intro x hx
      have h := hactG x hx
      calc ((d' : G)⁻¹ * (d : G)) * x * ((d' : G)⁻¹ * (d : G))⁻¹
          = (d' : G)⁻¹ * ((d : G) * x * (d : G)⁻¹) * (d' : G) := by group
        _ = (d' : G)⁻¹ * ((d' : G) * x * (d' : G)⁻¹) * (d' : G) := by rw [h]
        _ = x := by group
    by_cases hc : (d' : G)⁻¹ * (d : G) = 1
    · apply Subtype.ext
      exact (inv_mul_eq_one.mp hc).symm
    · exfalso
      obtain ⟨x₀, hx₀Q, hx₀ne⟩ : ∃ x : G, x ∈ Q ∧ x ≠ 1 := by
        by_contra hcon
        push_neg at hcon
        exact hQ (Subgroup.eq_bot_iff_forall Q |>.mpr (fun x hx => hcon x hx))
      exact hx₀ne (Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q H Q t hsplit hzass
        ((d' : G)⁻¹ * (d : G))
        ((twoPoint H t).mul_mem ((twoPoint H t).inv_mem d'.2) d.2) hc x₀ hx₀Q
        (hcen x₀ hx₀Q))
  -- equal finite cardinalities turn the injection into a surjection
  have hsurj : Function.Surjective φ := by
    have hrange : (Set.range φ).ncard = Nat.card Kˣ := by
      rw [← Nat.card_coe_set_eq (Set.range φ)]
      rw [show Nat.card ↑(Set.range φ) = Nat.card ↥(twoPoint H t) from
        (Nat.card_congr (Equiv.ofInjective φ hinj)).symm]
      exact hcard
    have hrange_univ : Set.range φ = Set.univ := by
      by_contra hne
      have hssub : Set.range φ ⊂ (Set.univ : Set Kˣ) := Set.ssubset_univ_iff.mpr hne
      have hlt := Set.ncard_lt_ncard hssub
      rw [hrange, Set.ncard_univ] at hlt
      exact lt_irrefl _ hlt
    intro μ
    have hmem : μ ∈ Set.range φ := by
      rw [hrange_univ]
      exact Set.mem_univ μ
    exact Set.mem_range.mp hmem
  obtain ⟨d, hd⟩ := hsurj lam
  refine ⟨(d : G), d.2, fun x => ?_⟩
  have hx := hact d x
  rw [hd] at hx
  simpa using hx

/-! ## The target -/

theorem frel_torus_all {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K} (hθ : Work.ZassenhausSuzuki.IsTitsTheta θ)
    (e : Q ≃* Work.ZassenhausSuzuki.SzA K θ)
    (htorus : Work.ZassenhausSuzuki.TorusCoords K θ H Q t e)
    {lam : Kˣ} {x y : Q} (hxy : Work.RankOneUniqueness.FRel H t (x : G) (y : G)) :
    Work.RankOneUniqueness.FRel H t
      (((e.symm (Work.ZassenhausSuzuki.SzA.hLam θ (lam : K) (e x)) : Q) : G))
      (((e.symm (Work.ZassenhausSuzuki.SzA.hLam θ ((lam⁻¹ : Kˣ) : K) (e y)) : Q) : G)) := by
  classical
  -- `Q ≃* A(K,θ)` makes `K × K` finite, hence `K` (a finite field of characteristic two) is.
  haveI : Finite ↥Q := Subtype.finite
  haveI hSzA : Finite (SzA K θ) := Finite.of_equiv ↥Q e.toEquiv
  haveI hK : Finite K :=
    Finite.of_injective (fun k : K => (⟨k, 0⟩ : SzA K θ))
      (fun a b hab => by simpa using congrArg SzA.a hab)
  haveI hKunits : Finite Kˣ :=
    Finite.of_injective (fun u : Kˣ => (u : K)) (fun a b hab => Units.ext hab)
  -- `Q ≠ ⊥`, since `A(K,θ)` is non-trivial.
  have hQ : Q ≠ ⊥ := by
    intro hbot
    have h1 : (e.symm (⟨1, 0⟩ : SzA K θ) : Q) = 1 := by
      apply Subtype.ext
      exact Subgroup.mem_bot.mp (hbot ▸ (e.symm (⟨1, 0⟩ : SzA K θ)).2)
    have h2 : (⟨1, 0⟩ : SzA K θ) = 1 := by
      have := congrArg (fun q : Q => e q) h1
      simpa using this
    have h10 : (1 : K) = 0 := by simpa using congrArg SzA.a h2
    exact one_ne_zero h10
  -- `Q` is a `2`-group: `A(K,θ)` has exponent `4` in characteristic two.
  have h2grp : IsPGroup 2 Q := by
    have hsz : IsPGroup 2 (SzA K θ) := by
      intro u
      refine ⟨2, ?_⟩
      have h3 : (⟨0, u.a * θ u.a⟩ : SzA K θ) ^ 2 = 1 := by
        rw [pow_two]
        ext <;> simp [SzA.mul_a, SzA.mul_b, SzA.one_a, SzA.one_b, CharTwo.add_self_eq_zero]
      have h4 : u ^ 4 = 1 := by
        have h2 : u ^ 2 = (⟨0, u.a * θ u.a⟩ : SzA K θ) := by
          rw [pow_two]
          exact SzA.sq_eq θ u
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h2]
        exact h3
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      exact h4
    exact hsz.of_equiv e.symm
  -- `|D| = #Inv(Q) = |K| - 1 = |Kˣ|`
  have hcard : Nat.card ↥(twoPoint H t) = Nat.card Kˣ := by
    rw [twoPoint_card_eq_involutions hsplit hzass h2grp]
    rw [show (involutions (Q : Set G)) = {x : G | x ∈ Q ∧ orderOf x = 2} from rfl]
    rw [ncard_involutions_of_mulEquiv (Q := Q) e]
    rw [SzA.ncard_orderOf_eq_two θ, Nat.card_units K]
  obtain ⟨d, hdD, hdact⟩ := torusLambda_surjective hsplit hzass htorus hQ hcard lam
  exact frel_torus_inv hsplit hzass hQ h2grp θ e hdD lam hdact hxy

end Work.ZassenhausSuzuki
