import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsAux
import Submission.Work.ZassenhausSuzuki.SzA.orbit_covering
import Submission.Work.ZassenhausSuzuki.frel_generic_value_eps
import Submission.Work.ZassenhausSuzuki.frel_torus_inv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

open Submission.Blueprint

/-! ## Auxiliary lemmas for the spreading of `f` along the `D`-orbits -/

section FieldAux

variable {K : Type*} [Field K] [CharP K 2]

/-- `⟨1,1⟩ * ⟨1,1⟩ = ⟨0,1⟩` in `A(K,θ)` (characteristic two). -/
private lemma szA_one_one_sq (θ : K ≃+* K) : (⟨1, 1⟩ : SzA K θ) ^ 2 = ⟨0, 1⟩ := by
  rw [pow_two]
  ext <;> simp [SzA.mul_a, SzA.mul_b, CharTwo.add_self_eq_zero, map_one]

/-- `⟨1,1⟩⁻¹ = ⟨1,0⟩` in `A(K,θ)` (characteristic two). -/
private lemma szA_one_one_inv (θ : K ≃+* K) : (⟨1, 1⟩ : SzA K θ)⁻¹ = ⟨1, 0⟩ := by
  ext <;> simp [SzA.inv_a, SzA.inv_b, CharTwo.neg_eq, CharTwo.add_self_eq_zero, map_one]

/-- The generic orbit representative `⟨1+μ⁻¹, μ⁻¹(θμ)⁻¹(1+μ)⟩` of HB 11.11 is `Xrep` at the
inverse parameter. -/
private lemma Xrep_inv_eq (θ : K ≃+* K) {mu : K} (hmu0 : mu ≠ 0) :
    Xrep θ mu⁻¹ = (⟨1 + mu⁻¹, mu⁻¹ * (θ mu)⁻¹ * (1 + mu)⟩ : SzA K θ) := by
  ext
  · simp [Xrep]
  · simp only [Xrep_b, map_inv₀]
    rw [show (1 : K) + mu⁻¹ = mu⁻¹ * (1 + mu) from by
      rw [mul_add, mul_one, inv_mul_cancel₀ hmu0]
      ring]
    ring

/-- If `h_λ x = y` with `λ ≠ 0`, then `x = h_{λ⁻¹} y`. -/
private lemma eq_hLam_inv_of_eq (θ : K ≃+* K) {lam : K} (hlam : lam ≠ 0) {x y : SzA K θ}
    (h : SzA.hLam θ lam x = y) : x = SzA.hLam θ lam⁻¹ y := by
  have h2 := congrArg (SzA.hLam θ lam⁻¹) h
  rw [← SzA.hLam_mul θ lam⁻¹ lam x, inv_mul_cancel₀ hlam, SzA.hLam_one] at h2
  exact h2

/-- `1 + μ·θμ ≠ 0` for `μ ∉ {0,1}` and `θ` of odd order (characteristic two). -/
private lemma one_add_mul_theta_ne_zero (θ : K ≃+* K) (hodd : Odd (orderOf θ)) {mu : K}
    (hmu0 : mu ≠ 0) (hmu1 : mu ≠ 1) : 1 + mu * θ mu ≠ 0 := by
  intro h
  have h1 : mu * θ mu = 1 := by
    have hx : mu * θ mu = -(1 : K) := eq_neg_of_add_eq_zero_right h
    rw [hx, neg_eq_iff_add_eq_zero]
    exact CharTwo.add_self_eq_zero 1
  exact hmu1 (eq_one_of_mul_map_eq_one θ hodd hmu0 h1)

/-- Existence of the auxiliary unit `ξ` with `ξ·θξ = 1 + μ·θμ`, using that
`x ↦ x·θx` is onto `Kˣ` for `θ` of odd order. -/
private lemma exists_xi_mul_theta [Finite K] (θ : K ≃+* K) (hodd : Odd (orderOf θ)) {mu : K}
    (hmu0 : mu ≠ 0) (hmu1 : mu ≠ 1) :
    ∃ xi : Kˣ, (xi : K) * θ (xi : K) = 1 + mu * θ mu := by
  have hne := one_add_mul_theta_ne_zero θ hodd hmu0 hmu1
  obtain ⟨xi, hxi⟩ := units_mul_map_surjective θ hodd (Units.mk0 (1 + mu * θ mu) hne)
  refine ⟨xi, ?_⟩
  have hc := congrArg (fun u : Kˣ => (u : K)) hxi
  simpa [Units.val_mul] using hc

/-- The two field facts used in the generic case of `frel_spread`: the HB 11.11 orbit
representative is `Xrep θ μ⁻¹`, and the auxiliary unit `ξ` with `ξ·θξ = 1 + μ·θμ` exists. -/
private lemma Xrep_inv_and_exists_xi [Finite K] (θ : K ≃+* K) (hodd : Odd (orderOf θ)) {mu : K}
    (hmu0 : mu ≠ 0) (hmu1 : mu ≠ 1) :
    Xrep θ mu⁻¹ = (⟨1 + mu⁻¹, mu⁻¹ * (θ mu)⁻¹ * (1 + mu)⟩ : SzA K θ) ∧
      ∃ xi : Kˣ, (xi : K) * θ (xi : K) = 1 + mu * θ mu :=
  ⟨Xrep_inv_eq θ hmu0, exists_xi_mul_theta θ hodd hmu0 hmu1⟩

end FieldAux

/-- `Q ≠ ⊥` for a subgroup carrying coordinates in Higman's group `A(K,θ)`. -/
private theorem Q_ne_bot_of_mulEquiv {G : Type} [Group G] {Q : Subgroup G}
    {K : Type*} [Field K] (θ : K ≃+* K) (e : Q ≃* SzA K θ) : Q ≠ ⊥ := by
  intro hbot
  have hmem : ((e.symm (⟨1, 0⟩ : SzA K θ) : Q) : G) ∈ (⊥ : Subgroup G) := by
    rw [← hbot]
    exact (e.symm (⟨1, 0⟩ : SzA K θ)).2
  have h1 : (e.symm (⟨1, 0⟩ : SzA K θ) : Q) = 1 := Subtype.ext (Subgroup.mem_bot.mp hmem)
  have h2 : (⟨1, 0⟩ : SzA K θ) = 1 := by
    have hc := congrArg (fun q : Q => e q) h1
    simpa using hc
  exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrArg SzA.a h2)

/-- **Transport of the book's `f`-relation along the torus action of `D`** (HB 11.13):
if `f (e.symm v) = e.symm w` and `e x = h_λ v`, then `f x = h_{λ⁻¹} w`. -/
private theorem frel_transport {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} {e : Q ≃* SzA (GaloisField 2 m) θ}
    (hreal : ∀ lam : (GaloisField 2 m)ˣ, ∃ d : G, d ∈ twoPoint H t ∧ ∀ x : Q,
      (((e.symm (SzA.hLam θ (lam : GaloisField 2 m) (e x)) : Q)) : G) = d * (x : G) * d⁻¹)
    (lam : (GaloisField 2 m)ˣ) {v w : SzA (GaloisField 2 m) θ} {x : Q}
    (hex : e x = SzA.hLam θ (lam : GaloisField 2 m) v)
    (hxy : RankOneUniqueness.FRel H t (((e.symm v : Q)) : G) (((e.symm w : Q)) : G)) :
    RankOneUniqueness.FRel H t (x : G)
      (((e.symm (SzA.hLam θ ((lam : GaloisField 2 m))⁻¹ w) : Q)) : G) := by
  have hQ : Q ≠ ⊥ := Q_ne_bot_of_mulEquiv θ e
  obtain ⟨d, hdD, hdact⟩ := hreal lam
  have hmain := frel_torus_inv hsplit hzass hQ h2 θ e hdD lam hdact hxy
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at hmain
  have hxe : (e.symm (SzA.hLam θ (lam : GaloisField 2 m) v) : Q) = x := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply, hex]
  rw [hxe] at hmain
  simpa only [Units.val_inv_eq_inv_val] using hmain

/-- **HB 11.13 (a) at the three special representatives**, in the coordinates `e`. -/
private theorem frel_rep_values {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} {e : Q ≃* SzA (GaloisField 2 m) θ}
    {g : Q} (hg : e g = (⟨1, 1⟩ : SzA (GaloisField 2 m) θ))
    (hstruct : t * (((g ^ 2 : Q)) : G) * t = (g : G) * t * (((g⁻¹ : Q)) : G)) :
    RankOneUniqueness.FRel H t
        (((e.symm (⟨0, 1⟩ : SzA (GaloisField 2 m) θ) : Q)) : G)
        (((e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) : Q)) : G) ∧
    RankOneUniqueness.FRel H t
        (((e.symm (⟨1, 1⟩ : SzA (GaloisField 2 m) θ) : Q)) : G)
        (((e.symm (⟨1, 1⟩ : SzA (GaloisField 2 m) θ) : Q)) : G) ∧
    RankOneUniqueness.FRel H t
        (((e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) : Q)) : G)
        (((e.symm (⟨0, 1⟩ : SzA (GaloisField 2 m) θ) : Q)) : G) := by
  have hge : e.symm (⟨1, 1⟩ : SzA (GaloisField 2 m) θ) = g := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply, hg]
  have hg2e : e (g ^ 2) = (⟨0, 1⟩ : SzA (GaloisField 2 m) θ) := by
    rw [map_pow, hg, szA_one_one_sq θ]
  have hg2 : e.symm (⟨0, 1⟩ : SzA (GaloisField 2 m) θ) = g ^ 2 := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply, hg2e]
  have hgine : e (g⁻¹) = (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) := by
    rw [map_inv, hg, szA_one_one_inv θ]
  have hginv : e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) = g⁻¹ := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply, hgine]
  have hg2ne : g ^ 2 ≠ 1 := by
    intro h
    have h1 : e (g ^ 2) = 1 := by rw [h, map_one]
    rw [hg2e] at h1
    exact (one_ne_zero : (1 : GaloisField 2 m) ≠ 0) (by simpa using congrArg SzA.b h1)
  obtain ⟨hf1, hf2, hf3⟩ := frel_structure_values hsplit hg2ne hstruct
  exact ⟨by rw [hg2, hginv]; exact hf1, by rw [hge]; exact hf2,
    by rw [hginv, hg2]; exact hf3⟩

/-- **HB 11.13 (a)+(b) spread along the `D`-orbits: the book's map `f` on all of `Q^#`.**

In the normalisation `e g = (1,1)` of the structure element (`g² = e.symm (0,1)`,
`g = e.symm (1,1)`, `g⁻¹ = e.symm (1,0)`), the `D`-orbit representatives of `Q^#` are these three
elements together with the generic ones `e.symm (Xrep θ ν)`, `ν ≠ 1`, where
`Xrep θ ν = (1+ν, θν·(1+ν))` (the coordinate form of `g⁻¹d⁻¹gd` for `d ∈ D` realising `h_ν`).
The book's map `f` is known at the representatives:

* HB 11.13 (a) (`frel_structure_values`, in `TitsAux`): `f (g²) = ⟨1,0⟩`, `f g = ⟨1,1⟩`,
  `f (g⁻¹) = ⟨0,1⟩`;
* HB 11.13 (b) (`frel_generic_value_eps`): for `ξ` with `ξ·θξ = 1 + ν⁻¹·θ(ν⁻¹)`,
  `f (e.symm (Xrep θ ν)) = e.symm (Xval θ ν ξ)`, `Xval θ ν ξ = (ν⁻²ξ⁻¹+ν⁻¹, θ(ν⁻¹)(ν⁻²ξ⁻¹+ν⁻¹))`;

and `f` is anti-equivariant (`frel_torus_inv`: `f (h_λ y) = h_{λ⁻¹} (f y)`).

Claim: every `x ∈ Q^#` is `h_λ` of one of the representatives, and its value under `f` is the
transported representative value: there are `λ ∈ Kˣ` and elements `v, w` with `e x = h_λ v`,
`FRel H t x (e.symm (h_{λ⁻¹} w))`, and `(v,w)` one of the four cases (the three special
representatives paired with their HB 11.13 (a) values, or `v = Xrep θ ν`, `w = Xval θ ν ξ` for a
generic `ν ≠ 1`).

Ingredients: `SzA/orbit_covering` (the coordinate half of HB 11.11, transported along `e`;
it needs `Odd (orderOf θ)`, which is the hypothesis `hθodd` below) gives the parametrisation of
`e x` as `h_λ` of a representative; `frel_structure_values` and `frel_generic_value_eps` give the
representative values; `exists_torus_action` (in `TitsAux`) supplies the `d ∈ D` realising each
`h_λ` that `frel_torus_inv` consumes; and `units_mul_map_surjective` (needed for `ξ`, and for the
centre case of the covering) needs `Odd (orderOf θ)` as well.  No `σ` is involved: the spreading
uses the equivariance of `f`, which holds unconditionally. -/
theorem frel_spread {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1)
    (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {g : Q} (hg : e g = ⟨1, 1⟩)
    (hstruct : t * (((g ^ 2 : Q)) : G) * t = (g : G) * t * (((g⁻¹ : Q)) : G))
    (x : Q) (hx : x ≠ 1) :
    ∃ lam : (GaloisField 2 m)ˣ, ∃ v w : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ,
      e x = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) v ∧
      Work.RankOneUniqueness.FRel H t (x : G)
        (((e.symm (Work.ZassenhausSuzuki.SzA.hLam θ ((lam : GaloisField 2 m))⁻¹ w) : Q)) : G) ∧
      ((v = (⟨0, 1⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) ∧
        w = (⟨1, 0⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)) ∨
       (v = (⟨1, 1⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) ∧
        w = (⟨1, 1⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)) ∨
       (v = (⟨1, 0⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) ∧
        w = (⟨0, 1⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)) ∨
       (∃ nu xi : (GaloisField 2 m)ˣ,
          (xi : GaloisField 2 m) * θ (xi : GaloisField 2 m)
              = 1 + ((nu : GaloisField 2 m))⁻¹ * θ (((nu : GaloisField 2 m))⁻¹) ∧
          (nu : GaloisField 2 m) ≠ 1 ∧
          v = Work.ZassenhausSuzuki.Xrep θ (nu : GaloisField 2 m) ∧
          w = Work.ZassenhausSuzuki.Xval θ (nu : GaloisField 2 m) (xi : GaloisField 2 m))) := by
  classical
  -- `e x ≠ 1`, hence its coordinates are not both zero
  have hne : ((e x).a, (e x).b) ≠ (0, 0) := by
    intro h
    have h0 : e x = 1 := by
      apply SzA.ext
      · simpa using congrArg Prod.fst h
      · simpa using congrArg Prod.snd h
    exact hx (e.injective (by rw [h0, map_one]))
  -- the three special values of `f` at the representatives
  obtain ⟨hf1, hf2, hf3⟩ := frel_rep_values hsplit hg hstruct
  -- every torus element is realised by an element of `D = twoPoint H t`
  have hreal : ∀ lam : (GaloisField 2 m)ˣ, ∃ d : G, d ∈ twoPoint H t ∧ ∀ y : Q,
      (((e.symm (SzA.hLam θ (lam : GaloisField 2 m) (e y)) : Q)) : G) = d * (y : G) * d⁻¹ :=
    fun lam => exists_torus_action hsplit hzass htorus lam
  rcases SzA.orbit_covering θ hθodd hne with
      ⟨lam, hlam0, heq⟩ | ⟨lam, hlam0, heq⟩ | ⟨lam, hlam0, heq⟩
    | ⟨lam, mu, hlam0, hmu0, hmu1, heq⟩
  · -- the orbit of the centre `⟨0,1⟩`, with value `⟨1,0⟩`
    have hkey : SzA.hLam θ lam (e x) = (⟨0, 1⟩ : SzA (GaloisField 2 m) θ) := by
      simpa only [SzA.hLam] using heq
    refine ⟨Units.mk0 lam⁻¹ (inv_ne_zero hlam0), (⟨0, 1⟩ : SzA (GaloisField 2 m) θ),
      (⟨1, 0⟩ : SzA (GaloisField 2 m) θ), ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
    · exact eq_hLam_inv_of_eq θ hlam0 hkey
    · exact frel_transport hsplit hzass h2 hreal (Units.mk0 lam⁻¹ (inv_ne_zero hlam0))
        (eq_hLam_inv_of_eq θ hlam0 hkey) hf1
  · -- the orbit of `⟨1,0⟩`, with value `⟨0,1⟩`
    have hkey : SzA.hLam θ lam (e x) = (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) := by
      simpa only [SzA.hLam] using heq
    refine ⟨Units.mk0 lam⁻¹ (inv_ne_zero hlam0), (⟨1, 0⟩ : SzA (GaloisField 2 m) θ),
      (⟨0, 1⟩ : SzA (GaloisField 2 m) θ), ?_, ?_,
      Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact eq_hLam_inv_of_eq θ hlam0 hkey
    · exact frel_transport hsplit hzass h2 hreal (Units.mk0 lam⁻¹ (inv_ne_zero hlam0))
        (eq_hLam_inv_of_eq θ hlam0 hkey) hf3
  · -- the orbit of `⟨1,1⟩`, with value `⟨1,1⟩`
    have hkey : SzA.hLam θ lam (e x) = (⟨1, 1⟩ : SzA (GaloisField 2 m) θ) := by
      simpa only [SzA.hLam] using heq
    refine ⟨Units.mk0 lam⁻¹ (inv_ne_zero hlam0), (⟨1, 1⟩ : SzA (GaloisField 2 m) θ),
      (⟨1, 1⟩ : SzA (GaloisField 2 m) θ), ?_, ?_, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact eq_hLam_inv_of_eq θ hlam0 hkey
    · exact frel_transport hsplit hzass h2 hreal (Units.mk0 lam⁻¹ (inv_ne_zero hlam0))
        (eq_hLam_inv_of_eq θ hlam0 hkey) hf2
  · -- the generic orbit: HB 11.13 (b)
    obtain ⟨hXrep, xi, hxi⟩ := Xrep_inv_and_exists_xi θ hθodd hmu0 hmu1
    let nu : (GaloisField 2 m)ˣ := Units.mk0 mu⁻¹ (inv_ne_zero hmu0)
    have hnuval : (nu : GaloisField 2 m) = mu⁻¹ := rfl
    have hnu_ne : (nu : GaloisField 2 m) ≠ 1 := by
      rw [hnuval]
      intro h
      apply hmu1
      have h3 : mu * mu⁻¹ = mu * 1 := congrArg (fun z : GaloisField 2 m => mu * z) h
      rw [mul_inv_cancel₀ hmu0, mul_one] at h3
      exact h3.symm
    have hxi' : (xi : GaloisField 2 m) * θ (xi : GaloisField 2 m)
        = 1 + ((nu : GaloisField 2 m))⁻¹ * θ (((nu : GaloisField 2 m))⁻¹) := by
      rw [hnuval, inv_inv]
      exact hxi
    have hkey : SzA.hLam θ lam (e x) = Xrep θ (nu : GaloisField 2 m) := by
      have h : SzA.hLam θ lam (e x) = Xrep θ mu⁻¹ := by
        simpa only [SzA.hLam] using heq.trans hXrep.symm
      simpa only [hnuval] using h
    have hxy : RankOneUniqueness.FRel H t
        (((e.symm (Xrep θ (nu : GaloisField 2 m)) : Q)) : G)
        (((e.symm (Xval θ (nu : GaloisField 2 m) (xi : GaloisField 2 m)) : Q)) : G) := by
      simpa only [Xrep, Xval] using
        frel_generic_value_eps hsplit hzass h2 htorus hg hstruct nu hnu_ne xi hxi'
    refine ⟨Units.mk0 lam⁻¹ (inv_ne_zero hlam0), Xrep θ (nu : GaloisField 2 m),
      Xval θ (nu : GaloisField 2 m) (xi : GaloisField 2 m), ?_, ?_,
      Or.inr (Or.inr (Or.inr ⟨nu, xi, hxi', hnu_ne, rfl, rfl⟩))⟩
    · exact eq_hLam_inv_of_eq θ hlam0 hkey
    · exact frel_transport hsplit hzass h2 hreal (Units.mk0 lam⁻¹ (inv_ne_zero hlam0))
        (eq_hLam_inv_of_eq θ hlam0 hkey) hxy

end Work.ZassenhausSuzuki
