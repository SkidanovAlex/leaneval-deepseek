import Mathlib
import Submission.Work.ZassenhausSuzuki.partitionszA.hLam_orbit_iff
import Submission.Work.ZassenhausSuzuki.frel_torus_all
import Submission.Work.ZassenhausSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `orbit_criterion`: the `Λ`-orbit criterion for the structure element (HB XI 11.11)

This is the combinatorial heart of the normalisation of the Suzuki structure element
(`structure_value_normalisation`, HB III XI 11.12).  In the coordinates `e : Q ≃* A(K,θ)`,
let `g = e⁻¹ ⟨1,p⟩` and let `L ∈ K ∖ {0,1}` be the parameter of the Weyl involution
(`hact`: `h ∈ D` acts on `Q` as `h_L`).  The element `g⁻¹ · h_{L⁻¹}(g)` of `Q` lies in the
`D`-orbit of `g` (i.e. is `D`-conjugate to `g`) if and only if the field identity

`p·L⁻¹ + (p+1)·θ(L⁻¹) = 1`

holds.  The `⇒` direction is the coordinate computation of HB XI 11.11 (b); the `⇐` direction
uses the surjectivity of the torus map `D → Kˣ` (`torusLambda_surjective`, which needs only
`IsSplitRankOne`, `IsZassenhaus` and `IsPGroup 2 Q`) to realise the required scalar `1 + L⁻¹`.

## Main results

* `hLam_conj_criterion` — the pure `A(K,θ)` coordinate identity underlying the criterion.
* `orbit_criterion` — the orbit/field-identity equivalence.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- **The coordinate form of HB XI 11.11 (b).**  In `A(K,θ)` over a field of characteristic two,
for `x = ⟨1,p⟩`, the equation `h_λ x = x⁻¹ · h_{L⁻¹} x` (relating the torus element `λ` to
`L⁻¹`) is equivalent to the pair of identities `λ = 1 + L⁻¹` and `p·L⁻¹ + (p+1)·θ L⁻¹ = 1`.

Indeed `x⁻¹ = ⟨1, p+1⟩` (characteristic two) and `h_{L⁻¹} x = ⟨L⁻¹, L⁻¹·θL⁻¹·p⟩`, so the
`a`-coordinate forces `λ = 1 + L⁻¹`, after which the `b`-coordinate reduces to the displayed
field identity. -/
theorem hLam_conj_criterion {K : Type} [Field K] [CharP K 2] (θ : K ≃+* K) (p L lam : K) :
    SzA.hLam θ lam (⟨1, p⟩ : SzA K θ)
      = (⟨1, p⟩ : SzA K θ)⁻¹ * SzA.hLam θ L⁻¹ (⟨1, p⟩ : SzA K θ)
    ↔ lam = 1 + L⁻¹ ∧ p * L⁻¹ + (p + 1) * θ L⁻¹ = 1 := by
  constructor
  · intro h
    have h1 := congrArg SzA.a h
    have h2 := congrArg SzA.b h
    simp only [SzA.hLam_a, SzA.hLam_b, SzA.mul_a, SzA.mul_b, SzA.inv_a, SzA.inv_b] at h1 h2
    simp only [mul_one, one_mul, map_one, CharTwo.neg_eq] at h1 h2
    refine ⟨h1, ?_⟩
    rw [h1] at h2
    simp only [map_add, map_one] at h2
    have h2' : p * L⁻¹ + p * θ L⁻¹ = 1 + θ L⁻¹ := by linear_combination h2
    calc p * L⁻¹ + (p + 1) * θ L⁻¹
        = p * L⁻¹ + p * θ L⁻¹ + θ L⁻¹ := by ring
      _ = (1 + θ L⁻¹) + θ L⁻¹ := by rw [h2']
      _ = 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rintro ⟨h1, hcon⟩
    ext <;> simp only [SzA.hLam_a, SzA.hLam_b, SzA.mul_a, SzA.mul_b, SzA.inv_a, SzA.inv_b]
    · rw [h1]; simp only [mul_one, CharTwo.neg_eq]
    · rw [h1]
      simp only [map_add, map_one, mul_one, one_mul, CharTwo.neg_eq]
      have e : (p + 1) * θ L⁻¹ = p * θ L⁻¹ + θ L⁻¹ := by ring
      rw [e] at hcon
      rw [← add_assoc] at hcon
      have hc : p * L⁻¹ + p * θ L⁻¹ = 1 + θ L⁻¹ := by
        rw [← hcon]
        simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [show (1 + L⁻¹) * (1 + θ L⁻¹) * p
          = p + (p * L⁻¹ + p * θ L⁻¹) + L⁻¹ * θ L⁻¹ * p from by ring, hc]
      ring

/-- **HB XI 11.11 (b), orbit form.**  With `H = Q ⋊ D` a Zassenhaus split rank-one
configuration, `Q ≅ A(K,θ)` through `e`, `g = e⁻¹⟨1,p⟩`, `D` acting on `Q` through the
standard torus and `h ∈ D` realising `h_L` (`L ≠ 0, 1`), the element `g⁻¹·h_{L⁻¹}(g)` is
`D`-conjugate to `g` exactly when `p·L⁻¹ + (p+1)·θ L⁻¹ = 1`.

The proof reduces both sides to the coordinate identity `hLam_conj_criterion`; the `⇐`
direction realises the scalar `1 + L⁻¹` by an element of `D`, which needs the surjectivity
of the torus map `D → Kˣ` supplied by `torusLambda_surjective` (whose extra hypotheses
`Q ≠ ⊥` and `|D| = |Kˣ|` are derived here from `e` and `IsPGroup 2 Q`). -/
theorem orbit_criterion {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {K : Type} [Field K] [CharP K 2]
    {θ : K ≃+* K} {e : Q ≃* Work.ZassenhausSuzuki.SzA K θ}
    (htorus : Work.ZassenhausSuzuki.TorusCoords K θ H Q t e)
    {g : Q} {p L : K} (hg : e g = (⟨1, p⟩ : Work.ZassenhausSuzuki.SzA K θ))
    (hL : L ≠ 0) (hL1 : L ≠ 1)
    {h : G} (hhD : h ∈ Submission.Blueprint.twoPoint H t) (hh1 : h ≠ 1)
    (hact : ∀ x : Q,
      (((e.symm (Work.ZassenhausSuzuki.SzA.hLam θ L (e x)) : Q)) : G) = h * (x : G) * h⁻¹) :
    (∃ d ∈ Submission.Blueprint.twoPoint H t,
        (g : G)⁻¹ * (((e.symm (Work.ZassenhausSuzuki.SzA.hLam θ L⁻¹ (e g)) : Q)) : G)
          = d * (g : G) * d⁻¹)
      ↔ p * L⁻¹ + (p + 1) * θ L⁻¹ = 1 := by
  classical
  -- `K` is finite (via `Q ≃* A(K,θ)`), and `Q` is non-trivial.
  haveI : Finite ↥Q := Subtype.finite
  haveI hSzA : Finite (SzA K θ) := Finite.of_equiv ↥Q e.toEquiv
  haveI hK : Finite K :=
    Finite.of_injective (fun k : K => (⟨k, 0⟩ : SzA K θ))
      (fun a b hab => by simpa using congrArg SzA.a hab)
  have hQ : Q ≠ ⊥ := by
    intro hbot
    have h1 : (e.symm (⟨1, 0⟩ : SzA K θ) : Q) = 1 :=
      Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ (e.symm (⟨1, 0⟩ : SzA K θ)).2))
    have h2' : (⟨1, 0⟩ : SzA K θ) = 1 := by
      have := congrArg (fun q : Q => e q) h1
      simpa using this
    exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrArg SzA.a h2')
  -- `|D| = #Inv(Q) = |K| - 1 = |Kˣ|`: the torus map `D → Kˣ` is a bijection.
  have hcard : Nat.card ↥(Submission.Blueprint.twoPoint H t) = Nat.card Kˣ := by
    rw [twoPoint_card_eq_involutions hsplit hzass h2]
    rw [show (involutions (Q : Set G)) = {x : G | x ∈ Q ∧ orderOf x = 2} from rfl]
    rw [ncard_involutions_of_mulEquiv (Q := Q) e]
    rw [SzA.ncard_orderOf_eq_two θ, Nat.card_units K]
  constructor
  · -- `⇒`: some `d ∈ D` conjugates `g` to `g⁻¹ · h_{L⁻¹}(g)`; read off the coordinates.
    rintro ⟨d, hdD, hd⟩
    obtain ⟨lam, hlam⟩ := htorus d hdD
    obtain ⟨y, hy, hye⟩ := hlam g
    have hy_eq : y = (g⁻¹ : Q) * e.symm (SzA.hLam θ L⁻¹ (e g)) := by
      apply Subtype.ext
      rw [hy, ← hd]
      rfl
    have key : SzA.hLam θ lam (e g) = (e g)⁻¹ * SzA.hLam θ L⁻¹ (e g) := by
      rw [← hye, hy_eq]
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [hg] at key
    exact ((hLam_conj_criterion θ p L lam).mp key).2
  · -- `⇐`: realise the scalar `1 + L⁻¹` by an element of `D`.
    intro hcon
    have hmu0 : (1 : K) + L⁻¹ ≠ 0 := by
      intro hh
      have h1 : L⁻¹ = -1 := eq_neg_of_add_eq_zero_right hh
      rw [CharTwo.neg_eq] at h1
      exact hL1 (by rw [← inv_inv L, h1, inv_one])
    obtain ⟨d, hdD, hdact⟩ :=
      torusLambda_surjective hsplit hzass htorus hQ hcard (Units.mk0 ((1 : K) + L⁻¹) hmu0)
    refine ⟨d, hdD, ?_⟩
    rw [← hdact g]
    have hQeq : (g⁻¹ : Q) * e.symm (SzA.hLam θ L⁻¹ (e g))
        = e.symm (SzA.hLam θ ((Units.mk0 ((1 : K) + L⁻¹) hmu0 : Kˣ) : K) (e g)) := by
      apply e.injective
      rw [map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      rw [hg]
      simpa using ((hLam_conj_criterion θ p L (1 + L⁻¹)).mpr ⟨rfl, hcon⟩).symm
    have hcoe := congrArg (fun z : Q => (z : G)) hQeq
    simpa using hcoe

end Work.ZassenhausSuzuki
