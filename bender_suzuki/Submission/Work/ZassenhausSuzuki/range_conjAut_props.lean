import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The image of the conjugation action of `D = twoPoint H t` in `Aut A(K,θ)`

Let `G` be a finite group with a split rank-one Zassenhaus configuration
(`IsSplitRankOne H Q t`, `IsZassenhaus H`, `Q ≠ ⊥`), and let `e0 : ↥Q ≃* A(K,θ)` coordinatise
the root group as Higman's group `SzA K θ` (`K = GF(2^m)`).  Let `φ : D →* MulAut ↥Q` be the
conjugation action of `D = twoPoint H t` on the normal subgroup `Q`, and let
`Φ = (MulAut.congr e0).toMonoidHom.comp φ : D →* MulAut (SzA K θ)` be the same action after
translation along `e0`.

* `D` acts fixed point freely on `Q#` (`ZData.dStab_fpf_on_Q`), so `φ`, and hence `Φ`, is
  injective; its kernel is trivial because `d x d⁻¹ = x` for some `x ≠ 1` in `Q` forces `d = 1`.
* The image of a homomorphism out of a cyclic group is cyclic, and by injectivity its
  cardinality is that of its domain: `|D| = 2^m - 1`.
* Finally, if `z = Φ d` fixes `x`, then conjugating back gives `d (e0.symm x) d⁻¹ = e0.symm x`,
  so `e0.symm x = 1` and `x = 1`: every non-identity element of the range fixes *no* point of
  `SzA K θ` (in particular no involution — this is the fixed-point-freeness of Suzuki 1962,
  Lemma 6, used to identify the Hua subgroup with the torus `Λ`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

theorem range_conjAut_props {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hZ : Submission.Blueprint.IsZassenhaus H) (hQne : Q ≠ ⊥)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m}
    (e0 : ↥Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)
    (φ : ↥(Submission.Blueprint.twoPoint H t) →* MulAut ↥Q)
    (hφ : ∀ (d : ↥(Submission.Blueprint.twoPoint H t)) (x : ↥Q),
        ((φ d x : ↥Q) : G) = (d : G) * (x : G) * (d : G)⁻¹)
    (hcyc : IsCyclic ↥(Submission.Blueprint.twoPoint H t))
    (hcard : Nat.card ↥(Submission.Blueprint.twoPoint H t) = 2 ^ m - 1) :
    IsCyclic ((MulAut.congr e0).toMonoidHom.comp φ).range ∧
    Nat.card ((MulAut.congr e0).toMonoidHom.comp φ).range = 2 ^ m - 1 ∧
    (∀ z ∈ ((MulAut.congr e0).toMonoidHom.comp φ).range, z ≠ 1 →
      ∀ x : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ, x * x = 1 → z x = x → x = 1) := by
  classical
  set Φ : ↥(Submission.Blueprint.twoPoint H t) →* MulAut (SzA (GaloisField 2 m) θ) :=
    (MulAut.congr e0).toMonoidHom.comp φ with hΦ
  -- `D` acts fixed point freely on `Q#` (the three-point Zassenhaus argument)
  have hfpf : ∀ d : G, d ∈ twoPoint H t → d ≠ 1 → ∀ x : G, x ∈ Q → d * x * d⁻¹ = x → x = 1 :=
    Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q H Q t hsplit hZ
  -- `φ` has trivial kernel
  have hker : ∀ d : ↥(twoPoint H t), φ d = 1 → d = 1 := by
    intro d hd
    by_contra hdne
    obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQne
    have hconj : (d : G) * (x : G) * (d : G)⁻¹ = (x : G) := by
      have h := hφ d x
      rw [hd] at h
      simpa using h.symm
    have hx1 : ((x : ↥Q) : G) = 1 :=
      hfpf (d : G) d.2 (fun h1 => hdne (Subtype.ext h1)) (x : G) x.2 hconj
    exact hxne (Subtype.ext hx1)
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : φ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hker _ h1)
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have h : MulAut.congr e0 (φ a) = MulAut.congr e0 (φ b) := by
      simpa [hΦ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hab
    exact hφinj ((MulAut.congr e0).injective h)
  -- the range is cyclic, being the image of the cyclic group `D`
  have hcycΦ : IsCyclic ↥Φ.range :=
    isCyclic_of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  -- ... and has the cardinality of `D`
  have hcardΦ : Nat.card ↥Φ.range = 2 ^ m - 1 := by
    have hbij : Function.Bijective Φ.rangeRestrict :=
      ⟨fun a b hab => hΦinj (congrArg Subtype.val hab), Φ.rangeRestrict_surjective⟩
    exact (Nat.card_congr (Equiv.ofBijective Φ.rangeRestrict hbij)).symm.trans hcard
  refine ⟨hcycΦ, hcardΦ, ?_⟩
  -- non-identity elements of the range have no fixed point on `SzA K θ`
  intro z hz hz1 x _hxx hzx
  obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hz
  have hdne : d ≠ 1 := by
    intro hd1
    exact hz1 (by rw [← hd, hd1]; exact map_one Φ)
  have hfix : (MulAut.congr e0) (φ d) x = x := by
    have h1 : (Φ d) x = x := by rw [hd]; exact hzx
    simpa [hΦ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using h1
  have h3 : e0 (φ d (e0.symm x)) = x := by
    simpa [MulAut.congr_apply, MulEquiv.trans_apply] using hfix
  have key : φ d (e0.symm x) = e0.symm x :=
    e0.injective (h3.trans (e0.apply_symm_apply x).symm)
  have hconj : (d : G) * ((e0.symm x : ↥Q) : G) * (d : G)⁻¹ = ((e0.symm x : ↥Q) : G) := by
    have h := hφ d (e0.symm x)
    rw [key] at h
    exact h.symm
  have hy1 : ((e0.symm x : ↥Q) : G) = 1 :=
    hfpf (d : G) d.2 (fun h1 => hdne (Subtype.ext h1)) ((e0.symm x : ↥Q) : G) (e0.symm x).2 hconj
  calc x = e0 (e0.symm x) := (e0.apply_symm_apply x).symm
    _ = e0 1 := by rw [show e0.symm x = 1 from Subtype.ext hy1]
    _ = 1 := map_one e0

end Work.ZassenhausSuzuki
