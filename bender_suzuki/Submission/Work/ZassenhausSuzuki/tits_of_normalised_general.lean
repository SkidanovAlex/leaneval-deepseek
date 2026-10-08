import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsTerminal
import Submission.Work.ZassenhausSuzuki.TitsAux
import Submission.Work.ZassenhausSuzuki.SzASymmIso

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-!
# Transport of the normalised Tits computation to an arbitrary finite field

`Work.ZassenhausSuzuki.tits_of_normalised` proves HB III XI 11.13–11.14 (Suzuki 1962 §5) for
`K = GaloisField 2 m`.  Here we deduce the general statement for any finite field `K` of
characteristic two: we transport the whole configuration along a ring isomorphism
`φ : K ≃+* GaloisField 2 (Module.finrank (ZMod 2) K)` (which exists by uniqueness of the finite
field of a given cardinality), and pull the conclusion back.

The transport needs one new ingredient, recorded in this file: for a ring isomorphism
`φ : K ≃+* L` (in practice `L = GaloisField 2 n`, `θ' = φ.symm.trans (θ.trans φ)`) the
coordinatewise map `⟨a,b⟩ ↦ ⟨φ a, φ b⟩` is a group isomorphism
`SzA.congr θ θ' φ h : A(K,θ) ≃* A(L,θ')`, compatible with the tori `h_λ` (so that
`TorusCoords` transports) and with the normalisation `e g = ⟨1,1⟩`.
-/

namespace SzA

variable {K L : Type*} [Field K] [Field L]

/-- **Change of the ground field.**  A ring isomorphism `φ : K ≃+* L` compatible with the
endomorphisms `θ` on `K` and `θ'` on `L` (`θ' ∘ φ = φ ∘ θ`, hypothesis `h`) induces the
coordinatewise group isomorphism `A(K,θ) ≃* A(L,θ')`, `⟨a,b⟩ ↦ ⟨φ a, φ b⟩`. -/
def congr (θ : K ≃+* K) (θ' : L ≃+* L) (φ : K ≃+* L)
    (h : ∀ x, θ' (φ x) = φ (θ x)) : SzA K θ ≃* SzA L θ' where
  toFun x := ⟨φ x.a, φ x.b⟩
  invFun y := ⟨φ.symm y.a, φ.symm y.b⟩
  left_inv x := by ext <;> simp
  right_inv y := by ext <;> simp
  map_mul' x y := by
    ext <;> simp only [SzA.mul_a, SzA.mul_b, map_add, map_mul, h y.a]

@[simp] theorem congr_a (θ : K ≃+* K) (θ' : L ≃+* L) (φ : K ≃+* L)
    (h : ∀ x, θ' (φ x) = φ (θ x)) (x : SzA K θ) : (congr θ θ' φ h x).a = φ x.a := rfl

@[simp] theorem congr_b (θ : K ≃+* K) (θ' : L ≃+* L) (φ : K ≃+* L)
    (h : ∀ x, θ' (φ x) = φ (θ x)) (x : SzA K θ) : (congr θ θ' φ h x).b = φ x.b := rfl

/-- `SzA.congr` carries the torus automorphism `h_λ` of `A(K,θ)` to `h_{φ λ}` of `A(L,θ')`. -/
theorem congr_hLam_unit (θ : K ≃+* K) (θ' : L ≃+* L) (φ : K ≃+* L)
    (h : ∀ x, θ' (φ x) = φ (θ x)) (mu : Kˣ) (x : SzA K θ) :
    congr θ θ' φ h (hLam θ (mu : K) x)
      = hLam θ' ((Units.map φ.toMonoidHom mu : Lˣ) : L) (congr θ θ' φ h x) := by
  ext <;> simp [h]

/-- `SzA.congr` preserves the normalisation element `⟨1,1⟩`. -/
theorem congr_one_one (θ : K ≃+* K) (θ' : L ≃+* L) (φ : K ≃+* L)
    (h : ∀ x, θ' (φ x) = φ (θ x)) :
    congr θ θ' φ h (⟨1, 1⟩ : SzA K θ) = (⟨1, 1⟩ : SzA L θ') := by
  ext <;> simp

end SzA

/-- Conjugation by `φ` is an injective homomorphism of the groups of ring automorphisms,
`θ ↦ φ.symm.trans (θ.trans φ)`.  It is used to transport `Odd (orderOf θ)` to the
`GaloisField`-model. -/
def ringConjHom {K L : Type*} [Field K] [Field L] (φ : K ≃+* L) :
    (K ≃+* K) →* (L ≃+* L) where
  toFun θ := φ.symm.trans (θ.trans φ)
  map_one' := by ext x; simp
  map_mul' θ₁ θ₂ := by ext x; simp [RingEquiv.trans_apply]

theorem ringConjHom_injective {K L : Type*} [Field K] [Field L] (φ : K ≃+* L) :
    Function.Injective (ringConjHom φ) := by
  intro θ₁ θ₂ h
  ext x
  have hx : ringConjHom φ θ₁ (φ x) = ringConjHom φ θ₂ (φ x) := by rw [h]
  exact φ.injective (by simpa [ringConjHom] using hx)

/-- Generalisation of `Work.ZassenhausSuzuki.tits_of_normalised` (Suzuki 1962 §5 / HB III XI
11.13–11.14) from `GaloisField 2 m` to an arbitrary finite field `K` of characteristic two:
in the normalisation `e g = ⟨1,1⟩` of the structure element `g` (`t g² t = g t g⁻¹`), the
coordinatising automorphism `θ` is a Tits endomorphism.

Recommended route: transport to `GaloisField 2 (Module.finrank (ZMod 2) K)` along
`FiniteField.ringEquivOfCardEq` (with `GaloisField.pow_finrank_eq_natCard` and
`GaloisField.card`), defining `SzA.map φ : SzA K θ ≃* SzA (GaloisField 2 n) (φ * θ * φ.symm)`,
checking that `TorusCoords`, `e g = ⟨1,1⟩` and the structure equation are preserved, and then
applying the existing `Work.ZassenhausSuzuki.tits_of_normalised` before pulling
`IsTitsTheta (φ * θ * φ.symm)` back to `IsTitsTheta θ`.  (Alternatively, generalise the
existing GaloisField proof of `tits_of_normalised`/`frel_axis`/`frel_generic_coords`/
`exists_torus_action` line by line to `[Field K] [CharP K 2] [Finite K]`.) -/
theorem tits_of_normalised_general {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {K : Type} [Field K] [CharP K 2] [Finite K] {θ : K ≃+* K} (hθ1 : θ ≠ 1)
    (hθodd : Odd (orderOf θ))
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {e : Q ≃* Work.ZassenhausSuzuki.SzA K θ}
    (htorus : Work.ZassenhausSuzuki.TorusCoords K θ H Q t e)
    {g : Q} (hg : e g = (⟨1, 1⟩ : Work.ZassenhausSuzuki.SzA K θ))
    (hstruct : t * (((g ^ 2 : Q)) : G) * t = (g : G) * t * (((g⁻¹ : Q)) : G)) :
    Work.ZassenhausSuzuki.IsTitsTheta θ := by
  classical
  -- ## the `ZMod 2`-algebra (hence module) structure and `n = [K : F₂]`
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  haveI : Fintype K := Fintype.ofFinite K
  set n : ℕ := Module.finrank (ZMod 2) K with hn
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hn0 : n ≠ 0 := by
    intro h
    have h1 : 2 ^ n = Fintype.card K := by
      rw [hn]; exact FiniteField.pow_finrank_eq_card 2 K
    rw [h, pow_zero] at h1
    have h2 : Fintype.card K ≤ 1 := by omega
    have : Subsingleton K := Fintype.card_le_one_iff_subsingleton.mp h2
    exact zero_ne_one (Subsingleton.elim (0 : K) 1)
  -- ## the model field `GaloisField 2 n` and the isomorphism `φ`
  obtain ⟨φ⟩ : Nonempty (K ≃+* GaloisField 2 n) := by
    refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
    rw [← FiniteField.pow_finrank_eq_card 2 K, ← hn]
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n hn0]
  -- ## the transported endomorphism `θ' = φ * θ * φ.symm`
  set θ' : GaloisField 2 n ≃+* GaloisField 2 n := φ.symm.trans (θ.trans φ) with hθ'def
  have hφθ : ∀ x : K, θ' (φ x) = φ (θ x) := by intro x; simp [hθ'def]
  let F : SzA K θ ≃* SzA (GaloisField 2 n) θ' := SzA.congr θ θ' φ hφθ
  let e' : Q ≃* SzA (GaloisField 2 n) θ' := e.trans F
  -- ## `θ' ≠ 1`
  have hθ'1 : θ' ≠ 1 := by
    intro h
    apply hθ1
    ext x
    have hx : θ' (φ x) = φ x := by rw [h]; rfl
    exact φ.injective (by simpa [hθ'def] using hx)
  -- ## `Odd (orderOf θ')`
  have hθ'odd : Odd (orderOf θ') := by
    have h := orderOf_injective (ringConjHom φ) (ringConjHom_injective φ) θ
    rw [show θ' = ringConjHom φ θ from rfl, h]
    exact hθodd
  -- ## the normalisation `e' g = ⟨1,1⟩` is preserved
  have hg' : e' g = (⟨1, 1⟩ : SzA (GaloisField 2 n) θ') := by
    show F (e g) = (⟨1, 1⟩ : SzA (GaloisField 2 n) θ')
    rw [hg]
    exact SzA.congr_one_one θ θ' φ hφθ
  -- ## the torus equivariance is preserved
  have htorus' : TorusCoords (GaloisField 2 n) θ' H Q t e' := by
    intro d hd
    obtain ⟨lam, hlam⟩ := htorus d hd
    refine ⟨Units.map φ.toMonoidHom lam, fun x => ?_⟩
    obtain ⟨y, hy, hye⟩ := hlam x
    refine ⟨y, hy, ?_⟩
    have hy' : e' y = F (e y) := rfl
    have hx' : e' x = F (e x) := rfl
    rw [hy', hx', hye]
    exact SzA.congr_hLam_unit θ θ' φ hφθ lam (e x)
  -- ## the GaloisField computation (`hsplit`, `hzass`, `h2`, `hstruct` are field-independent)
  have hres : IsTitsTheta θ' :=
    tits_of_normalised (m := n) hθ'1 hθ'odd hsplit hzass h2 htorus' hg' hstruct
  -- ## pull the conclusion back along `φ`
  refine ⟨hθ1, fun x => ?_⟩
  have hx := hres.2 (φ x)
  have key : φ (θ (θ x)) = φ (x ^ 2) := by
    rw [map_pow]
    rw [← hx]
    simp [hθ'def]
  exact φ.injective key

end Work.ZassenhausSuzuki
