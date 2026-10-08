import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.twoPoint_inverted
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The book's `f`-relation is `Λ`-equivariant (BG 3.1 / 4.6 (c))

The target lemma `Work.ZassenhausSuzuki.frel_torus_inv` says that the map `f` defined by the
rank-one relation `FRel H t x y` (`t x t = m · t · y`, `m ∈ H`; Peterfalvi II Ch. VII §1)
is compatible with the conjugation action of `D = H ∩ H^t` on `Q`: if conjugation by `d ∈ D`
realises the torus element `h_λ` on `Q` (transported by the coordinatisation `e`), then

`FRel H t x y → FRel H t (d x d⁻¹) (d⁻¹ y d)`,

i.e. `f (h_λ x) = h_{λ⁻¹} (f x)` — the equivariance `σ ∘ h_λ = h_{λ⁻¹} ∘ σ` of the Suzuki map.

The proof splits into two independent pieces, both proved below:

* `frel_conj` — pure group theory: `FRel` is preserved when both arguments are conjugated by
  an element `d ∈ H` inverted by the Weyl involution (`t d t = d⁻¹`).  The witness is
  `m' = d⁻¹ m d⁻¹`; the key algebra is `t (d z d⁻¹) t = d⁻¹ (t z t) d` and `d⁻¹ t d⁻¹ = t`.
* `hLam_inv_act` — the transport of the hypothesis `hact` through the inversion of the torus
  element: `h_λ` is realised by `d`, hence `h_{λ⁻¹} = h_λ⁻¹` is realised by `d⁻¹`.

Then `frel_torus_inv` is the assembly: rewrite the two arguments of the goal by `hact` and
`hLam_inv_act` and apply `frel_conj` with `t d t = d⁻¹` (`twoPoint_inverted`, L1).
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- **`FRel` is preserved by conjugation by an element of `H` inverted by `t`.**

If `t x t = m · t · y` with `m ∈ H`, `d ∈ H` and `t d t = d⁻¹` (so `t` inverts `d`), then
`t (d x d⁻¹) t = (d⁻¹ m d⁻¹) · t · (d⁻¹ y d)`, with `d⁻¹ m d⁻¹ ∈ H`.

The element `d⁻¹ m d⁻¹` is not `d⁻¹ m d`: the asymmetric shape is exactly what the relation
`d⁻¹ t d⁻¹ = t` (equivalent to `t d t = d⁻¹` together with `t² = 1`) provides. -/
theorem frel_conj {G : Type*} [Group G] {H : Subgroup G} {t d x y : G}
    (hd : d ∈ H) (ht2 : t * t = 1) (hdt : t * d * t = d⁻¹)
    (hxy : Work.RankOneUniqueness.FRel H t x y) :
    Work.RankOneUniqueness.FRel H t (d * x * d⁻¹) (d⁻¹ * y * d) := by
  obtain ⟨m, hmH, hm⟩ := hxy
  refine ⟨d⁻¹ * m * d⁻¹, H.mul_mem (H.mul_mem (H.inv_mem hd) hmH) (H.inv_mem hd), ?_⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hconj : ∀ z : G, t * z * t = (MulAut.conj t) z := by
    intro z
    rw [MulAut.conj_apply, htinv]
  have hcd : (MulAut.conj t) d = d⁻¹ := by
    rw [MulAut.conj_apply, htinv]
    exact hdt
  have hcdi : (MulAut.conj t) d⁻¹ = d := by
    rw [map_inv, hcd, inv_inv]
  have htd : d⁻¹ * t * d⁻¹ = t := by
    have h1 : t * d = d⁻¹ * t := by
      calc t * d = (t * d) * (t * t) := by rw [ht2, mul_one]
        _ = (t * d * t) * t := by group
        _ = d⁻¹ * t := by rw [hdt]
    calc d⁻¹ * t * d⁻¹ = (t * d) * d⁻¹ := by rw [h1]
      _ = t := by group
  rw [hconj (d * x * d⁻¹), map_mul, map_mul, hcd, hcdi, ← hconj x, hm]
  rw [show (d⁻¹ * m * d⁻¹) * t * (d⁻¹ * y * d) = d⁻¹ * m * (d⁻¹ * t * d⁻¹) * y * d
      from by group, htd]
  group

/-- **The inverse torus element is realised by the inverse conjugating element.**

If conjugation by `d` realises `h_λ` on `Q` (`hact`), then conjugation by `d⁻¹` realises
`h_{λ⁻¹}` — because `h_{λ⁻¹}` is the inverse of `h_λ` on `A(K,θ)`
(`SzA.hLam_mul` + `SzA.hLam_one`). -/
theorem hLam_inv_act {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t)
    {K : Type*} [Field K] (θ : K ≃+* K) (e : Q ≃* SzA K θ)
    {d : G} (hd : d ∈ H) (lam : Kˣ)
    (hact : ∀ x : Q,
      (((e.symm (SzA.hLam θ (lam : K) (e x)) : Q)) : G)
        = d * (x : G) * d⁻¹)
    (y : Q) :
    (((e.symm (SzA.hLam θ ((lam⁻¹ : Kˣ) : K) (e y)) : Q)) : G)
        = d⁻¹ * (y : G) * d := by
  -- `h_λ ∘ h_{λ⁻¹} = id` on `A(K,θ)`
  have hcomp : (lam : K) * ((lam⁻¹ : Kˣ) : K) = 1 := by simp
  have hkey : ∀ u : SzA K θ, SzA.hLam θ (lam : K) (SzA.hLam θ ((lam⁻¹ : Kˣ) : K) u) = u := by
    intro u
    rw [← SzA.hLam_mul, hcomp, SzA.hLam_one]
  have h := hact (e.symm (SzA.hLam θ ((lam⁻¹ : Kˣ) : K) (e y)))
  rw [MulEquiv.apply_symm_apply, hkey (e y), MulEquiv.symm_apply_apply] at h
  rw [h]
  group

theorem frel_torus_inv {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (hQ : Q ≠ ⊥)
    (h2 : IsPGroup 2 Q) {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K)
    (e : Q ≃* Work.ZassenhausSuzuki.SzA K θ) {d : G} (hd : d ∈ Submission.Blueprint.twoPoint H t)
    (lam : Kˣ)
    (hact : ∀ x : Q,
      (((e.symm (Work.ZassenhausSuzuki.SzA.hLam θ (lam : K) (e x)) : Q)) : G)
        = d * (x : G) * d⁻¹)
    {x y : Q} (hxy : Work.RankOneUniqueness.FRel H t (x : G) (y : G)) :
    Work.RankOneUniqueness.FRel H t
      ((((e.symm (Work.ZassenhausSuzuki.SzA.hLam θ (lam : K) (e x)) : Q)) : G))
      ((((e.symm (Work.ZassenhausSuzuki.SzA.hLam θ ((lam⁻¹ : Kˣ) : K) (e y)) : Q)) : G)) := by
  have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hsplit
  have hdH : d ∈ H := (Work.RankOneUniqueness.mem_twoPoint_iff.mp hd).1
  have hdt : t * d * t = d⁻¹ := by
    have h := twoPoint_inverted hsplit hzass hQ h2 d hd
    rwa [Work.RankOneUniqueness.inv_eq_self hsplit] at h
  have hY : (((e.symm (SzA.hLam θ ((lam⁻¹ : Kˣ) : K) (e y)) : Q)) : G)
      = d⁻¹ * (y : G) * d := hLam_inv_act hsplit θ e hdH lam hact y
  rw [hact x, hY]
  exact frel_conj hdH ht2 hdt hxy

end Work.ZassenhausSuzuki
