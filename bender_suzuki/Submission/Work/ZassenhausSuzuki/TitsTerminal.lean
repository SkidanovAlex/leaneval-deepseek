import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsAux
import Submission.Work.ZassenhausSuzuki.TitsCoordAux
import Submission.Work.ZassenhausSuzuki.TitsCoordIdentities
import Submission.Work.ZassenhausSuzuki.frel_axis
import Submission.Work.ZassenhausSuzuki.frel_generic_coords
import Submission.Work.ZassenhausSuzuki.frel_product_at_j
import Submission.Work.ZassenhausSuzuki.coords_poly_of_eq
import Submission.Work.ZassenhausSuzuki.tits_of_poly

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The terminal computation of `suzukiTitsOfFix` (Suzuki 1962 §5 / HB III XI 11.13–11.14)

**The heart of the proof.**  Assume the split rank-one Zassenhaus configuration
`(H,Q,t)` carries coordinates `e : Q ≃* A(K,θ)` (`K = GF(2^m)`) in which the two-point
stabiliser `D = twoPoint H t` acts through the torus `Λ = h(Kˣ)`, and that there is a
**structure element** `g ∈ Q` with `e g = ⟨1,1⟩ = ⟨1,0⟩⁻¹` and

`t · g² · t = g · t · g⁻¹`  (so `e (g²) = ⟨0,1⟩`, `e (g⁻¹) = ⟨1,0⟩`).

Then `θ` is a Tits endomorphism: `θ(θ x) = x²`.

The proof is Suzuki's §§4–5 (HB III XI 11.13(b) + 11.14).  Writing
`ν ∈ K ∖ {0,1}`, `t = θν`, `s = t/(1+t)`, and `α ∈ Kˣ` with `α·θα = s` (possible because
`x ↦ x·θx` is onto `Kˣ` when `θ` has odd order), the product relation
`Work.ZassenhausSuzuki.frel_product` of the (ZT)-functional equation, evaluated at the pair
`(e.symm ⟨α⁻¹,0⟩ , g)` — so that `x₁·x₂ = e.symm ⟨α⁻¹,1⟩` and
`f(x₁)·g = e.symm ⟨1,1+s⟩` — says

`f ⟨α⁻¹,1⟩ = f ⟨1,1+s⟩ · g⁻¹`,

and both values are known: the axis value `f ⟨α⁻¹,0⟩ = ⟨0,s⟩` (`frel_axis`), and the
generic values `f ⟨α⁻¹,1⟩ = h_{λ⁻¹}(Xval θ ν ξ)`, `f ⟨1,1+s⟩ = h_{λ⁻¹}(Xval θ ν⁻¹ (νξ))`
(HB 11.13 (b), `frel_generic_value_eps`, transported along the torus —
`frel_generic_coords`).  Comparing the two values of `f ⟨α⁻¹,1⟩` (`frel_unique`) gives a
coordinate identity in `A(K,θ)` whose `b`-coordinate forces the polynomial identity of
`Work.ZassenhausSuzuki.tits_of_poly` (`coords_poly_of_eq`), hence `θ(θ ν) = ν²` for every
`ν ∉ {0,1}`, and then for every `ν`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- **The terminal step of `suzukiTitsOfFix`** (Suzuki 1962 §5, HB III XI 11.13–11.14):
in the normalisation `e g = ⟨1,1⟩` of a structure element `g` (`t g² t = g t g⁻¹`), the
coordinatising automorphism `θ` is a Tits endomorphism. -/
theorem tits_of_normalised {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1)
    (hθodd : Odd (orderOf θ))
    (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {e : Q ≃* SzA (GaloisField 2 m) θ}
    (htorus : TorusCoords (GaloisField 2 m) θ H Q t e)
    {g : Q} (hg : e g = (⟨1, 1⟩ : SzA (GaloisField 2 m) θ))
    (hstruct : t * (((g ^ 2 : Q)) : G) * t = (g : G) * t * (((g⁻¹ : Q)) : G)) :
    IsTitsTheta θ := by
  classical
  refine ⟨hθ1, tits_of_poly θ ?_⟩
  intro ν hν0 hν1
  -- ## the field parameter `s = θν/(1+θν)`, with `θν·(1+s) = s` and `s·(1+θν) = θν`
  have hθν0 : θ ν ≠ 0 := fun h => hν0 (θ.injective (by rw [h, map_zero]))
  have hθν1 : θ ν ≠ 1 := fun h => hν1 (θ.injective (by rw [h, map_one]))
  have h1θν : (1 : GaloisField 2 m) + θ ν ≠ 0 := by
    intro h
    exact hθν1 (by
      have h' : θ ν = -(1 : GaloisField 2 m) := eq_neg_of_add_eq_zero_right h
      rwa [CharTwo.neg_eq] at h')
  have h1ν : (1 : GaloisField 2 m) + ν ≠ 0 := by
    intro h
    exact hν1 (by
      have h' : ν = -(1 : GaloisField 2 m) := eq_neg_of_add_eq_zero_right h
      rwa [CharTwo.neg_eq] at h')
  set s : GaloisField 2 m := θ ν / (1 + θ ν) with hsdef
  have hs0 : s ≠ 0 := by rw [hsdef]; exact div_ne_zero hθν0 h1θν
  have hsmul : s * (1 + θ ν) = θ ν := by
    rw [hsdef]; exact div_mul_cancel₀ _ h1θν
  have hts : θ ν * (1 + s) = s := by
    rw [hsdef]
    field_simp
    exact add_add_self (1 : GaloisField 2 m) (θ ν)
  -- ## the units `α` (with `α·θα = s`) and `ξ` (with `ξ·θξ = 1 + ν⁻¹·θν⁻¹`)
  obtain ⟨α, hα⟩ := units_mul_map_surjective θ hθodd (Units.mk0 s hs0)
  have hαK : (α : GaloisField 2 m) * θ (α : GaloisField 2 m) = s := by
    have h := congrArg (fun u : (GaloisField 2 m)ˣ => (u : GaloisField 2 m)) hα
    simpa [Units.val_mul] using h
  have hα0 : (α : GaloisField 2 m) ≠ 0 := Units.ne_zero α
  have hξne : (1 : GaloisField 2 m) + ν⁻¹ * θ ν⁻¹ ≠ 0 := by
    intro h
    have h1 : ν⁻¹ * θ ν⁻¹ = 1 := by
      have h' : ν⁻¹ * θ ν⁻¹ = -(1 : GaloisField 2 m) := eq_neg_of_add_eq_zero_right h
      rwa [CharTwo.neg_eq] at h'
    have hνinv : ν⁻¹ = 1 := eq_one_of_mul_map_eq_one θ hθodd (inv_ne_zero hν0) h1
    exact hν1 (inv_eq_one.mp hνinv)
  obtain ⟨ξ, hξ⟩ := units_mul_map_surjective θ hθodd (Units.mk0 _ hξne)
  have hξK : (ξ : GaloisField 2 m) * θ (ξ : GaloisField 2 m) = 1 + ν⁻¹ * θ ν⁻¹ := by
    have h := congrArg (fun u : (GaloisField 2 m)ˣ => (u : GaloisField 2 m)) hξ
    simpa [Units.val_mul] using h
  -- ## the torus parameters `λ₁ = α⁻¹/(1+ν)`, `λ₂ = ν/(1+ν)`
  have hlam1 : (α : GaloisField 2 m)⁻¹ / (1 + ν) ≠ 0 :=
    div_ne_zero (inv_ne_zero hα0) h1ν
  have hlam2 : ν / (1 + ν) ≠ 0 := div_ne_zero hν0 h1ν
  have hla : ((α : GaloisField 2 m)⁻¹ / (1 + ν)) * (1 + ν) = (α : GaloisField 2 m)⁻¹ :=
    div_mul_cancel₀ _ h1ν
  have hlb : (ν / (1 + ν)) * (1 + ν⁻¹) = 1 := by
    rw [div_mul_eq_mul_div, mul_add, mul_one, mul_inv_cancel₀ hν0, add_comm,
      div_self h1ν]
  -- ## the two generic orbit representatives
  have hX1 : SzA.hLam θ ((α : GaloisField 2 m)⁻¹ / (1 + ν))
      (Xrep θ ν) = (⟨(α : GaloisField 2 m)⁻¹, 1⟩ : SzA (GaloisField 2 m) θ) :=
    (TitsCoordIdentities θ).2.1 _ ν s hα0 h1ν hαK.symm hts
  have hX2 : SzA.hLam θ (ν / (1 + ν))
      (Xrep θ (ν⁻¹)) = (⟨1, 1 + s⟩ : SzA (GaloisField 2 m) θ) :=
    (TitsCoordIdentities θ).2.2.1 ν s hν0 h1ν hsmul
  -- ## the values of the book's map `f` at the four relevant elements
  have hAxis : RankOneUniqueness.FRel H t
      (((e.symm (⟨(α : GaloisField 2 m)⁻¹, 0⟩ : SzA (GaloisField 2 m) θ)) : Q) : G)
      (((e.symm (⟨0, s⟩ : SzA (GaloisField 2 m) θ)) : Q) : G) := by
    have h := frel_axis (hsplit := hsplit) (hzass := hzass) (h2 := h2) (e := e) htorus hg
      hstruct (u := (α : GaloisField 2 m)⁻¹) (inv_ne_zero hα0)
    have hcoe : (((α : GaloisField 2 m)⁻¹)⁻¹ * θ (((α : GaloisField 2 m)⁻¹)⁻¹)) = s := by
      rw [inv_inv]; exact hαK
    rwa [hcoe] at h
  have hGen1 : RankOneUniqueness.FRel H t
      (((e.symm (⟨(α : GaloisField 2 m)⁻¹, 1⟩ : SzA (GaloisField 2 m) θ)) : Q) : G)
      (((e.symm (SzA.hLam θ (((α : GaloisField 2 m)⁻¹ / (1 + ν))⁻¹)
        (Xval θ ν (ξ : GaloisField 2 m))) : Q)) : G) :=
    frel_generic_coords (hsplit := hsplit) (hzass := hzass) (h2 := h2) (e := e) htorus hg
      hstruct (Units.mk0 ν hν0) hν1 ξ hX1 hlam1 hξK
  have hξ2 : ((ν : GaloisField 2 m) * (ξ : GaloisField 2 m))
      * θ ((ν : GaloisField 2 m) * (ξ : GaloisField 2 m)) = 1 + ν * θ ν :=
    (TitsCoordIdentities θ).2.2.2 ν (ξ : GaloisField 2 m) hν0 hξK
  have hnuinv1 : (((Units.mk0 ν hν0)⁻¹ : (GaloisField 2 m)ˣ) : GaloisField 2 m) ≠ 1 := by
    rw [show (((Units.mk0 ν hν0)⁻¹ : (GaloisField 2 m)ˣ) : GaloisField 2 m) = ν⁻¹ from by simp]
    intro h
    exact hν1 (inv_eq_one.mp h)
  have hGen2 : RankOneUniqueness.FRel H t
      (((e.symm (⟨1, 1 + s⟩ : SzA (GaloisField 2 m) θ)) : Q) : G)
      (((e.symm (SzA.hLam θ (ν / (1 + ν))⁻¹
        (Xval θ ν⁻¹ (ν * (ξ : GaloisField 2 m)))) : Q)) : G) := by
    have hraw := frel_generic_coords (hsplit := hsplit) (hzass := hzass) (h2 := h2) (e := e)
      htorus hg hstruct ((Units.mk0 ν hν0)⁻¹) hnuinv1 (Units.mk0 ν hν0 * ξ) hX2 hlam2 ?_
    · simpa using hraw
    · simpa [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, inv_inv] using hξ2
  -- ## the product relation at `x₂ = g²`
  have hg2ne : g ^ 2 ≠ 1 := by
    intro h
    have h1 : e (g ^ 2) = (⟨0, 1⟩ : SzA (GaloisField 2 m) θ) := by
      rw [map_pow, hg, one_one_sq]
    rw [h, map_one] at h1
    exact (one_ne_zero : (1 : GaloisField 2 m) ≠ 0) (by simpa using congrArg SzA.b h1)
  have hx1g2 : (((e.symm (⟨(α : GaloisField 2 m)⁻¹, 0⟩ : SzA (GaloisField 2 m) θ)) : Q) : G)
      * (((g ^ 2 : Q)) : G)
      = (((e.symm (⟨(α : GaloisField 2 m)⁻¹, 1⟩ : SzA (GaloisField 2 m) θ)) : Q) : G) := by
    have hQ : (e.symm (⟨(α : GaloisField 2 m)⁻¹, 0⟩ : SzA (GaloisField 2 m) θ) * g ^ 2 : Q)
        = e.symm (⟨(α : GaloisField 2 m)⁻¹, 1⟩ : SzA (GaloisField 2 m) θ) := by
      apply e.injective
      simp only [map_mul, map_pow, MulEquiv.apply_symm_apply, hg, one_one_sq,
        mk_mul_mk_zero_one]
    rw [← Subgroup.coe_mul, hQ]
  have hne1 : (((e.symm (⟨(α : GaloisField 2 m)⁻¹, 0⟩ : SzA (GaloisField 2 m) θ)) : Q) : G)
      * (((g ^ 2 : Q)) : G) ≠ 1 := by
    rw [hx1g2]
    intro h
    have h1 : (⟨(α : GaloisField 2 m)⁻¹, 1⟩ : SzA (GaloisField 2 m) θ) = 1 := by
      have h2 := congrArg e (Subtype.ext h :
        (e.symm (⟨(α : GaloisField 2 m)⁻¹, 1⟩ : SzA (GaloisField 2 m) θ) : Q) = 1)
      simpa using h2
    exact (inv_ne_zero hα0) (by simpa using congrArg SzA.a h1)
  have hGen2' : RankOneUniqueness.FRel H t
      ((((e.symm (⟨0, s⟩ : SzA (GaloisField 2 m) θ)) : Q) : G) * (g : G))
      (((e.symm (SzA.hLam θ (ν / (1 + ν))⁻¹
        (Xval θ ν⁻¹ (ν * (ξ : GaloisField 2 m)))) : Q)) : G) := by
    have hQ : (e.symm (⟨0, s⟩ : SzA (GaloisField 2 m) θ) * g : Q)
        = e.symm (⟨1, 1 + s⟩ : SzA (GaloisField 2 m) θ) := by
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply, hg, zero_one_mul_one_one]
    rw [← Subgroup.coe_mul, hQ]
    exact hGen2
  have hProd := frel_product_at_j (hsplit := hsplit) (hzass := hzass) (h2 := h2) (g := g)
    hg2ne hstruct hAxis hGen2' hne1
  rw [hx1g2] at hProd
  -- ## uniqueness of the value of `f` at `⟨α⁻¹,1⟩`
  have huniq := frel_unique hsplit hGen1 hProd (Subtype.coe_prop _) (Subtype.coe_prop _)
  -- ## the resulting coordinate identity in `A(K,θ)`
  have heeq : SzA.hLam θ (((α : GaloisField 2 m)⁻¹ / (1 + ν))⁻¹)
        (Xval θ ν (ξ : GaloisField 2 m))
      = SzA.hLam θ (ν / (1 + ν))⁻¹ (Xval θ ν⁻¹ (ν * (ξ : GaloisField 2 m)))
        * (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) := by
    have h := congrArg e (Subtype.ext huniq :
      (e.symm (SzA.hLam θ (((α : GaloisField 2 m)⁻¹ / (1 + ν))⁻¹)
        (Xval θ ν (ξ : GaloisField 2 m))) : Q)
        = ((e.symm (SzA.hLam θ (ν / (1 + ν))⁻¹
            (Xval θ ν⁻¹ (ν * (ξ : GaloisField 2 m)))) : Q) * g⁻¹ : Q))
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hg, inv_one_one] at h
    exact h
  exact coords_poly_of_eq θ hν1 hαK.symm hla hlb hts hξK heeq

end Work.ZassenhausSuzuki
