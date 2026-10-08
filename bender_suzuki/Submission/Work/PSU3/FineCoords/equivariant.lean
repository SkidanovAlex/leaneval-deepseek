/-
# `Work.PSU3.FineCoords.equivariant`

The fine coordinates of `Q` are the isomorphisms `e : Q ≃* SZ (E n)` compatible with
`x ↦ μ · bar x` on the quotient and with `zc` on the centre ("good" isomorphisms,
`Work.PSU3.CoarseFrame.Good`).  The group `KW` acts on this set by
`e ↦ torusAct (κ d)⁻¹ ∘ e ∘ (conj by d)` (`fr.actIso`), and `fr.actIso d e` is again good.

An element `d ∈ KW` satisfies `nm (κ d) = (κ d) · σ (κ d)`: this follows from `KW_gen`,
`hsq` on `Ksub` (`nm` is `a ↦ a²` there) and `ζ_norm` (`κ ζ · σ (κ ζ) = 1`).

The good isomorphisms with a fixed `μ` form a torsor under `Hom (E n) F`: two of them
differ by a shift `p ↦ (p.x, p.y + ε p.x)` (`difHom`, `difHom_spec`).  Consequently the
`KW`-action is affine,
`actIso d (shiftIso ε e) = shiftIso (ρ_d ε) (actIso d e)` with
`ρ_d ε (a) = N (κ d)⁻¹ · ε (κ d · a)`,
and the element `η_d` realising `actIso d e₀ = shiftIso (η_d) e₀` is a 1-cocycle
`η_{d d'} = η_d + ρ_d η_{d'}`.  Averaging `η` over the odd-order group `KW`,
`ε* = ∑_d η_d`, gives a fixed point `ρ_d ε* + η_d = ε*`, hence `e = shiftIso ε* e₀` is
good and `KW`-equivariant.
-/
import Mathlib
import Submission.Work.PSU3.FineCoords.Setup
import Submission.Work.PSU3.FineCoords.card_KW_odd
import Submission.Work.PSU3.FineCoords.good_exists

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped commutatorElement

open Work.ThmF

namespace Work.PSU3.CoarseFrame

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## The difference of two good isomorphisms -/

/-- The `F`-coordinate of the difference of two isomorphisms with the same quotient
coordinate. -/
noncomputable def difVal (e e' : Q ≃* SZ (E n)) (x : Q) (h : (e x).x = (e' x).x) : Fx n :=
  ⟨(e x).y + (e' x).y, by
    have h1 := (e x).herm
    have h2' : (e' x).y + σE (e' x).y = (e x).x * σE (e x).x := by
      rw [h]
      exact (e' x).herm
    refine CharTwo.add_eq_zero.mp ?_
    rw [map_add]
    calc σE (e x).y + σE (e' x).y + ((e x).y + (e' x).y)
        = ((e x).y + σE (e x).y) + ((e' x).y + σE (e' x).y) := by abel
      _ = (e x).x * σE (e x).x + (e x).x * σE (e x).x := by rw [h1, h2']
      _ = 0 := CharTwo.add_self_eq_zero _⟩

@[simp] lemma difVal_coe (e e' : Q ≃* SZ (E n)) (x : Q) (h : (e x).x = (e' x).x) :
    ((difVal e e' x h : Fx n) : E n) = (e x).y + (e' x).y := rfl

/-- Two good isomorphisms with the same `μ` have equal quotient coordinates. -/
lemma good_xcoord_eq (fr : CoarseFrame H Q t n) {μ : (E n)ˣ} {e e' : Q ≃* SZ (E n)}
    (he : Good fr μ e) (he' : Good fr μ e') (x : Q) : (e x).x = (e' x).x := by
  rw [he.xcoord x, he'.xcoord x]

/-- The difference only depends on the class in `Q/Q₀`. -/
lemma difVal_eq_of_barA_eq (fr : CoarseFrame H Q t n) {μ : (E n)ˣ} {e e' : Q ≃* SZ (E n)}
    (he : Good fr μ e) (he' : Good fr μ e') {x x' : Q} (hb : fr.barA x = fr.barA x') :
    difVal e e' x (fr.good_xcoord_eq he he' x) = difVal e e' x' (fr.good_xcoord_eq he he' x') := by
  obtain ⟨z, hz⟩ := fr.exists_Q0_mul_of_barA_eq hb.symm
  have hq : (fr.Q0toQ z : Q) ∈ fr.bar.ker := (fr.bar_eq_one_iff _).mpr z.2
  have hkz : fr.barA (fr.Q0toQ z) = 0 := fr.barA_of_mem_ker hq
  have hex : x = fr.Q0toQ z * x' := Subtype.ext hz
  apply Subtype.ext
  rw [difVal_coe, difVal_coe, hex, map_mul, map_mul]
  rw [he.kern _ hkz, he'.kern _ hkz]
  simp only [SZ.mul_y, SZ.mul_x, gEl_x, gEl_y, zero_mul, add_zero]
  rw [show ((fr.kerCoord (fr.Q0toQ z) hkz : E n) + (e x').y)
        + ((fr.kerCoord (fr.Q0toQ z) hkz : E n) + (e' x').y)
      = ((fr.kerCoord (fr.Q0toQ z) hkz : E n) + (fr.kerCoord (fr.Q0toQ z) hkz : E n))
        + ((e x').y + (e' x').y) from by abel]
  rw [CharTwo.add_self_eq_zero, zero_add]

/-- The additive hom giving the shift from `e` to `e'` (two good isomorphisms). -/
noncomputable def difHom (fr : CoarseFrame H Q t n) (μ : (E n)ˣ) (e e' : Q ≃* SZ (E n))
    (he : Good fr μ e) (he' : Good fr μ e') : E n →+ Fx n where
  toFun a := difVal e e' (fr.sect ((μ : E n)⁻¹ * a)) (fr.good_xcoord_eq he he' _)
  map_zero' := by
    apply Subtype.ext
    rw [difVal_coe, ZeroMemClass.coe_zero]
    have hk : fr.barA (fr.sect ((μ : E n)⁻¹ * 0)) = 0 := by rw [mul_zero, fr.sect_barA]
    rw [he.kern _ hk, he'.kern _ hk]
    simp only [gEl_y]
    exact CharTwo.add_self_eq_zero _
  map_add' a a' := by
    set x := fr.sect ((μ : E n)⁻¹ * a) with hx
    set x' := fr.sect ((μ : E n)⁻¹ * a') with hx'
    set y := fr.sect ((μ : E n)⁻¹ * (a + a')) with hy
    have hbb : fr.barA y = fr.barA (x * x') := by
      rw [show fr.barA y = (μ : E n)⁻¹ * (a + a') from fr.sect_barA ((μ : E n)⁻¹ * (a + a')),
        show fr.barA (x * x') = fr.barA x + fr.barA x' from fr.barA_mul x x',
        show fr.barA x = (μ : E n)⁻¹ * a from fr.sect_barA ((μ : E n)⁻¹ * a),
        show fr.barA x' = (μ : E n)⁻¹ * a' from fr.sect_barA ((μ : E n)⁻¹ * a'), mul_add]
    rw [show difVal e e' y (fr.good_xcoord_eq he he' y)
        = difVal e e' (x * x') (fr.good_xcoord_eq he he' (x * x')) from
      fr.difVal_eq_of_barA_eq he he' hbb]
    apply Subtype.ext
    show (e (x * x')).y + (e' (x * x')).y
        = ((difVal e e' x (fr.good_xcoord_eq he he' x) : Fx n) : E n)
          + ((difVal e e' x' (fr.good_xcoord_eq he he' x') : Fx n) : E n)
    rw [difVal_coe, difVal_coe]
    simp only [e.map_mul, e'.map_mul, SZ.mul_x, SZ.mul_y]
    rw [show (e' x).x * σE (e' x').x = (e x).x * σE (e x').x from by
      rw [fr.good_xcoord_eq he he' x, fr.good_xcoord_eq he he' x']]
    rw [show (e x).y + (e x').y + (e x).x * σE (e x').x
          + ((e' x).y + (e' x').y + (e x).x * σE (e x').x)
        = ((e x).y + (e x').y + ((e' x).y + (e' x').y))
          + ((e x).x * σE (e x').x + (e x).x * σE (e x').x) from by abel]
    rw [CharTwo.add_self_eq_zero, add_zero]
    abel

/-- The shift from `e` to `e'` realises `difHom`. -/
lemma difHom_spec (fr : CoarseFrame H Q t n) {μ : (E n)ˣ} {e e' : Q ≃* SZ (E n)}
    (he : Good fr μ e) (he' : Good fr μ e') (x : Q) :
    e' x = shiftFun (fr.difHom μ e e' he he') (e x) := by
  have h1 : fr.difHom μ e e' he he' ((e x).x)
      = difVal e e' x (fr.good_xcoord_eq he he' x) := by
    apply fr.difVal_eq_of_barA_eq he he'
    rw [show fr.barA (fr.sect ((μ : E n)⁻¹ * (e x).x)) = (μ : E n)⁻¹ * (e x).x from
        fr.sect_barA _,
      show fr.barA x = (μ : E n)⁻¹ * ((e x).x) from by
        rw [he.xcoord x, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero μ), one_mul]]
  apply SZ.ext
  · rw [shiftFun_x]
    exact (fr.good_xcoord_eq he he' x).symm
  · rw [shiftFun_y, h1, difVal_coe]
    rw [show (e x).y + ((e x).y + (e' x).y) = ((e x).y + (e x).y) + (e' x).y from by abel,
      CharTwo.add_self_eq_zero, zero_add]

/-! ## Shifting a good isomorphism -/

/-- The shift of an isomorphism by an element of `Hom(E n, F)`. -/
noncomputable def shiftIso (ε : E n →+ Fx n) (e : Q ≃* SZ (E n)) : Q ≃* SZ (E n) :=
  e.trans (shiftEquiv ε)

@[simp] lemma shiftIso_apply (ε : E n →+ Fx n) (e : Q ≃* SZ (E n)) (x : Q) :
    shiftIso ε e x = shiftFun ε (e x) := rfl

lemma shiftFun_comp (ε η : E n →+ Fx n) (p : SZ (E n)) :
    shiftFun ε (shiftFun η p) = shiftFun (η + ε) p := by
  apply SZ.ext
  · simp only [shiftFun_x]
  · show (p.y + (η p.x : E n)) + (ε p.x : E n) = p.y + ((η p.x : E n) + (ε p.x : E n))
    ring

lemma shiftIso_comp (ε η : E n →+ Fx n) (e : Q ≃* SZ (E n)) :
    shiftIso ε (shiftIso η e) = shiftIso (η + ε) e := by
  apply MulEquiv.ext
  intro x
  exact shiftFun_comp ε η (e x)

lemma good_shiftIso (fr : CoarseFrame H Q t n) {μ : (E n)ˣ} {e : Q ≃* SZ (E n)}
    (he : Good fr μ e) (ε : E n →+ Fx n) : Good fr μ (shiftIso ε e) := by
  refine ⟨?_, ?_⟩
  · intro x
    show (shiftFun ε (e x)).x = _
    rw [shiftFun_x, he.xcoord x]
  · intro z hz
    show shiftFun ε (e z) = fr.gEl z hz
    rw [he.kern z hz]
    apply SZ.ext
    · rw [shiftFun_x, gEl_x]
    · rw [shiftFun_y, gEl_x, map_zero, ZeroMemClass.coe_zero, add_zero]

/-- `shiftIso` is injective in the shift. -/
lemma shiftIso_injective (fr : CoarseFrame H Q t n) (e : Q ≃* SZ (E n))
    {ε ε' : E n →+ Fx n} (h : shiftIso ε e = shiftIso ε' e) : ε = ε' := by
  apply AddMonoidHom.ext
  intro a
  set x : Q := e.symm (fr.szSect a) with hx
  have hxa : (e x).x = a := by
    rw [hx, MulEquiv.apply_symm_apply, fr.szSect_x]
  have h2 : (e x).y + ↑(ε (e x).x) = (e x).y + ↑(ε' (e x).x) := by
    have hc := congrArg (fun f : Q ≃* SZ (E n) => f x) h
    have hc2 := congrArg (fun p : SZ (E n) => p.y) hc
    simpa only [shiftIso_apply, shiftFun_y] using hc2
  rw [hxa] at h2
  exact Subtype.ext (add_left_cancel h2)

/-! ## The affine action of `Eˣ` -/

/-- The scalar `ρ_c (ε) (a) = N(c)⁻¹ · ε (c · a)`, where `N(c) = c · σ c`. -/
noncomputable def rhoFunC (c : (E n)ˣ) (ε : E n →+ Fx n) : E n →+ Fx n where
  toFun a := (⟨((c : E n) * σE (c : E n))⁻¹, by
      show σE (((c : E n) * σE (c : E n))⁻¹) = ((c : E n) * σE (c : E n))⁻¹
      rw [map_inv₀, map_mul, σE_σE]
      exact congrArg Inv.inv (mul_comm (σE (c : E n)) (c : E n))⟩ : Fx n)
    * ε ((c : E n) * a)
  map_zero' := by simp
  map_add' a a' := by
    show (⟨((c : E n) * σE (c : E n))⁻¹, _⟩ : Fx n) * ε ((c : E n) * (a + a'))
        = (⟨((c : E n) * σE (c : E n))⁻¹, _⟩ : Fx n) * ε ((c : E n) * a)
          + (⟨((c : E n) * σE (c : E n))⁻¹, _⟩ : Fx n) * ε ((c : E n) * a')
    rw [mul_add, map_add, mul_add]

/-- `ρ_d = ρ_{κ d}` as an additive endomorphism of `Hom(E n, F)`. -/
noncomputable def rho (fr : CoarseFrame H Q t n) (d : fr.KW) :
    (E n →+ Fx n) →+ (E n →+ Fx n) where
  toFun ε := rhoFunC (fr.κ d) ε
  map_zero' := by
    apply AddMonoidHom.ext
    intro a
    simp [rhoFunC]
  map_add' ε ε' := by
    apply AddMonoidHom.ext
    intro a
    simp only [rhoFunC, AddMonoidHom.add_apply, mul_add]
    rfl

lemma rho_apply (fr : CoarseFrame H Q t n) (d : fr.KW) (ε : E n →+ Fx n) :
    fr.rho d ε = rhoFunC (fr.κ d) ε := rfl

/-- Moving a shift past the torus action. -/
lemma shiftFun_torusAct_inv (ε : E n →+ Fx n) (c : (E n)ˣ) (p : SZ (E n)) :
    SZ.torusAct c⁻¹ (shiftFun ε p) = shiftFun (rhoFunC c ε) (SZ.torusAct c⁻¹ p) := by
  apply SZ.ext
  · simp only [SZ.torusAct_x, shiftFun_x]
  · rw [SZ.torusAct_y, shiftFun_y, shiftFun_y, SZ.torusAct_x, SZ.torusAct_y]
    have hv1 : ((c⁻¹ : (E n)ˣ) : E n) = (c : E n)⁻¹ := Units.val_inv_eq_inv_val c
    rw [hv1, map_inv₀]
    rw [show (((rhoFunC c ε) ((c : E n)⁻¹ * p.x) : Fx n) : E n)
        = ((c : E n) * σE (c : E n))⁻¹
          * ↑(ε ((c : E n) * ((c : E n)⁻¹ * p.x))) from rfl]
    rw [show (c : E n) * ((c : E n)⁻¹ * p.x) = p.x from by
      rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero c), one_mul]]
    rw [show (c : E n)⁻¹ * (σE (c : E n))⁻¹ = ((c : E n) * σE (c : E n))⁻¹ from by
      rw [mul_inv]]
    ring

/-! ## The `KW`-action on good isomorphisms -/

/-- `actIso` is a group action (in that order). -/
lemma actIso_mul (fr : CoarseFrame H Q t n) (d d' : fr.KW) (e : Q ≃* SZ (E n)) :
    fr.actIso d (fr.actIso d' e) = fr.actIso (d * d') e := by
  apply MulEquiv.ext
  intro x
  simp only [fr.actIso_apply]
  rw [FMap.torusAct_mul]
  rw [show (fr.κ (d * d') : (E n)ˣ)⁻¹
        = (fr.κ d : (E n)ˣ)⁻¹ * (fr.κ d' : (E n)ˣ)⁻¹ from by rw [map_mul, mul_inv]]
  rw [show fr.conjQ d' (fr.conjQ d x) = fr.conjQ (d * d') x from
      Subtype.ext (by simp only [fr.conjQ_coe, Subgroup.coe_mul]; group)]

lemma actIso_shiftIso (fr : CoarseFrame H Q t n) (d : fr.KW) (ε : E n →+ Fx n)
    (e : Q ≃* SZ (E n)) :
    fr.actIso d (shiftIso ε e) = shiftIso (rhoFunC (fr.κ d) ε) (fr.actIso d e) := by
  apply MulEquiv.ext
  intro x
  rw [fr.actIso_apply, shiftIso_apply, shiftIso_apply, fr.actIso_apply]
  exact shiftFun_torusAct_inv ε (fr.κ d) (e (fr.conjQ d x))

/-! ## `nm (κ d) = (κ d) σ (κ d)` and the centre computation -/

/-- Conjugation by a power of `ζ` is trivial on any point fixed by `ζ`'s conjugation. -/
lemma conj_zeta_pow (fr : CoarseFrame H Q t n) (j : ℕ) (w : G)
    (hw : (fr.ζ : G)⁻¹ * w * (fr.ζ : G) = w) :
    ((fr.ζ : G) ^ j)⁻¹ * w * (fr.ζ : G) ^ j = w := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, mul_inv_rev,
        show (fr.ζ : G)⁻¹ * ((fr.ζ : G) ^ j)⁻¹ * w * ((fr.ζ : G) ^ j * (fr.ζ : G))
            = (fr.ζ : G)⁻¹ * (((fr.ζ : G) ^ j)⁻¹ * w * (fr.ζ : G) ^ j) * (fr.ζ : G)
          from by group,
        ih, hw]

/-- Conjugation of `Q₀ ≅ F` by `d ∈ KW` is multiplication by `(κ d) · σ (κ d)`. -/
lemma act_zc_KW (fr : CoarseFrame H Q t n)
    (hsq : ∀ a : (E n)ˣ, σE (a : E n) = a → (fr.nm a : E n) = (a : E n) ^ 2)
    (d : fr.KW) (y : E n) (hy : σE y = y) :
    (d : G)⁻¹ * fr.zc y * (d : G) =
      fr.zc (((fr.κ d : E n) * σE (fr.κ d : E n)) * y) := by
  obtain ⟨k, hkK, j, hdj⟩ := fr.KW_gen d
  have hκk : σE ((fr.κ k : (E n)ˣ) : E n) = (fr.κ k : E n) := (fr.mem_K_iff k).mp hkK
  have hnmk : (fr.nm (fr.κ k) : E n) = ((fr.κ k : E n)) ^ 2 := hsq (fr.κ k) hκk
  have hfixed : σE (((fr.κ k : E n)) ^ 2 * y) = ((fr.κ k : E n)) ^ 2 * y := by
    rw [map_mul, map_pow, hκk, hy]
  have hk : (k : G)⁻¹ * fr.zc y * (k : G) = fr.zc (((fr.κ k : E n)) ^ 2 * y) := by
    rw [fr.act_zc_K k hkK y hy, hnmk]
  have hκd : (fr.κ d : E n) * σE (fr.κ d : E n) = ((fr.κ k : E n)) ^ 2 := by
    have hζ : (fr.κ fr.ζ : E n) * σE (fr.κ fr.ζ : E n) = 1 := fr.ζ_norm
    have hcm : (fr.κ d : E n) = (fr.κ k : E n) * (fr.κ fr.ζ : E n) ^ j := by
      rw [hdj, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    rw [hcm, show σE ((fr.κ k : E n) * (fr.κ fr.ζ : E n) ^ j)
          = (fr.κ k : E n) * (σE (fr.κ fr.ζ : E n)) ^ j from by
        rw [map_mul, map_pow, hκk]]
    rw [show ((fr.κ k : E n) * (fr.κ fr.ζ : E n) ^ j)
            * ((fr.κ k : E n) * (σE (fr.κ fr.ζ : E n)) ^ j)
          = ((fr.κ k : E n)) ^ 2
            * ((fr.κ fr.ζ : E n) * σE (fr.κ fr.ζ : E n)) ^ j from by ring_nf,
      hζ, one_pow, mul_one]
  rw [show (d : G)⁻¹ * fr.zc y * (d : G)
      = ((fr.ζ : G) ^ j)⁻¹ * ((k : G)⁻¹ * fr.zc y * (k : G)) * (fr.ζ : G) ^ j from by
        rw [show (d : G) = (k : G) * (fr.ζ : G) ^ j from by rw [hdj]; push_cast; ring]
        group,
    hk]
  rw [conj_zeta_pow fr j _ (fr.act_zc_ζ _ hfixed)]
  rw [← hκd]

/-- The `F`-coordinate of `conjQ d z` is `N(κ d)` times that of `z`. -/
lemma kerCoord_conjQ (fr : CoarseFrame H Q t n)
    (hsq : ∀ a : (E n)ˣ, σE (a : E n) = a → (fr.nm a : E n) = (a : E n) ^ 2)
    (d : fr.KW) (z : Q) (hz : fr.barA z = 0)
    (hz' : fr.barA (fr.conjQ d z) = 0) :
    (fr.kerCoord (fr.conjQ d z) hz' : Fx n)
      = (⟨(fr.κ d : E n) * σE (fr.κ d : E n), by
            show σE ((fr.κ d : E n) * σE (fr.κ d : E n))
                = (fr.κ d : E n) * σE (fr.κ d : E n)
            rw [map_mul, σE_σE]; exact mul_comm _ _⟩ : Fx n) * fr.kerCoord z hz := by
  apply fr.zc_inj_Fx
  change fr.zc ↑(fr.kerCoord (fr.conjQ d z) hz')
      = fr.zc ((fr.κ d : E n) * σE (fr.κ d : E n) * ↑(fr.kerCoord z hz))
  rw [fr.zc_kerCoord]
  rw [← fr.act_zc_KW hsq d _ (fr.kerCoord z hz).2, fr.zc_kerCoord]
  rfl

/-- The `KW`-action preserves goodness. -/
lemma good_actIso (fr : CoarseFrame H Q t n)
    (hsq : ∀ a : (E n)ˣ, σE (a : E n) = a → (fr.nm a : E n) = (a : E n) ^ 2)
    {μ : (E n)ˣ} {e : Q ≃* SZ (E n)} (he : Good fr μ e) (d : fr.KW) :
    Good fr μ (fr.actIso d e) := by
  refine ⟨?_, ?_⟩
  · intro x
    rw [fr.actIso_apply, SZ.torusAct_x, he.xcoord (fr.conjQ d x), fr.barA_conjQ]
    rw [Units.val_inv_eq_inv_val]
    rw [show ((fr.κ d : (E n)ˣ) : E n)⁻¹
          * ((μ : E n) * (((fr.κ d : (E n)ˣ) : E n) * fr.barA x))
        = ((fr.κ d : (E n)ˣ) : E n)⁻¹ * ((fr.κ d : (E n)ˣ) : E n)
          * ((μ : E n) * fr.barA x) from by ring]
    rw [inv_mul_cancel₀ (Units.ne_zero (fr.κ d)), one_mul]
  · intro z hz
    have hz' : fr.barA (fr.conjQ d z) = 0 := by rw [fr.barA_conjQ, hz, mul_zero]
    rw [fr.actIso_apply, he.kern (fr.conjQ d z) hz']
    apply SZ.ext
    · rw [SZ.torusAct_x, gEl_x, gEl_x, mul_zero]
    · rw [SZ.torusAct_y, gEl_y, gEl_y]
      rw [show (((fr.kerCoord (fr.conjQ d z) hz' : Fx n)) : E n)
          = (fr.κ d : E n) * σE (fr.κ d : E n) * ↑(fr.kerCoord z hz) from by
        rw [fr.kerCoord_conjQ hsq d z hz hz']; rfl]
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      rw [show ((fr.κ d : (E n)ˣ) : E n)⁻¹ * (σE ((fr.κ d : (E n)ˣ) : E n))⁻¹
          = (((fr.κ d : (E n)ˣ) : E n) * σE ((fr.κ d : (E n)ˣ) : E n))⁻¹ from by rw [mul_inv]]
      have hc : ((fr.κ d : (E n)ˣ) : E n) * σE ((fr.κ d : (E n)ˣ) : E n) ≠ 0 := by
        apply mul_ne_zero (Units.ne_zero (fr.κ d))
        intro h
        exact Units.ne_zero (fr.κ d) (by
          have h2 : σE (σE ((fr.κ d : (E n)ˣ) : E n)) = σE 0 := congrArg σE h
          rwa [σE_σE, map_zero] at h2)
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-! ## Averaging the cocycle -/

/-- **The main existence theorem.**  Given a good isomorphism `e₀` (with parameter `μ`), there
is a good isomorphism `e` which is `KW`-equivariant: `e (d⁻¹ x d) = torusAct (κ d) (e x)`. -/
theorem exists_equivariant_good (fr : CoarseFrame H Q t n)
    (hsq : ∀ a : (E n)ˣ, σE (a : E n) = a → (fr.nm a : E n) = (a : E n) ^ 2)
    (μ : (E n)ˣ) (e₀ : Q ≃* SZ (E n)) (he₀ : Good fr μ e₀) :
    ∃ e : Q ≃* SZ (E n), Good fr μ e ∧
      ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
        e y = SZ.torusAct (fr.κ d) (e x) := by
  classical
  letI : Fintype fr.KW := Fintype.ofFinite fr.KW
  have h2 : ∀ η : E n →+ Fx n, η + η = 0 := by
    intro η
    apply AddMonoidHom.ext
    intro a
    rw [AddMonoidHom.add_apply, AddMonoidHom.zero_apply]
    apply Subtype.ext
    show (η a : E n) + (η a : E n) = 0
    exact CharTwo.add_self_eq_zero _
  have hNodd : Odd (Fintype.card fr.KW) := by
    rw [← Nat.card_eq_fintype_card]
    exact Work.PSU3.FineCoords.card_KW_odd fr
  have hcard : ∀ x : E n →+ Fx n, (Fintype.card fr.KW + 1) • x = 0 := by
    intro x
    obtain ⟨m, hm⟩ := hNodd
    have hc : Fintype.card fr.KW + 1 = (m + 1) + (m + 1) := by rw [hm]; ring
    rw [hc, add_nsmul, h2]
  set eta : fr.KW → (E n →+ Fx n) :=
    fun d => fr.difHom μ e₀ (fr.actIso d e₀) he₀ (fr.good_actIso hsq he₀ d) with heta
  have heta_spec : ∀ d : fr.KW, fr.actIso d e₀ = shiftIso (eta d) e₀ := by
    intro d
    apply MulEquiv.ext
    intro x
    rw [shiftIso_apply]
    exact fr.difHom_spec he₀ (fr.good_actIso hsq he₀ d) x
  have hcoc : ∀ d₀ d : fr.KW, eta (d₀ * d) = eta d₀ + fr.rho d₀ (eta d) := by
    intro d₀ d
    apply shiftIso_injective fr e₀
    calc shiftIso (eta (d₀ * d)) e₀
        = fr.actIso (d₀ * d) e₀ := (heta_spec (d₀ * d)).symm
      _ = fr.actIso d₀ (fr.actIso d e₀) := (actIso_mul fr d₀ d e₀).symm
      _ = fr.actIso d₀ (shiftIso (eta d) e₀) := by rw [heta_spec d]
      _ = shiftIso (rhoFunC (fr.κ d₀) (eta d)) (fr.actIso d₀ e₀) :=
          actIso_shiftIso fr d₀ (eta d) e₀
      _ = shiftIso (rhoFunC (fr.κ d₀) (eta d)) (shiftIso (eta d₀) e₀) := by
          rw [heta_spec d₀]
      _ = shiftIso (eta d₀ + rhoFunC (fr.κ d₀) (eta d)) e₀ := shiftIso_comp _ _ _
      _ = shiftIso (eta d₀ + fr.rho d₀ (eta d)) e₀ := by rw [fr.rho_apply]
  have hcoc' : ∀ d₀ d : fr.KW, fr.rho d₀ (eta d) = eta (d₀ * d) + eta d₀ := by
    intro d₀ d
    rw [hcoc d₀ d]
    rw [show eta d₀ + fr.rho d₀ (eta d) + eta d₀ = fr.rho d₀ (eta d) from by
      rw [add_comm (eta d₀) (fr.rho d₀ (eta d)), add_assoc, h2, add_zero]]
  set eps : E n →+ Fx n := ∑ d : fr.KW, eta d with heps
  have hfix : ∀ d₀ : fr.KW, fr.rho d₀ eps + eta d₀ = eps := by
    intro d₀
    rw [heps, map_sum]
    rw [Finset.sum_congr rfl (fun d _ => hcoc' d₀ d), Finset.sum_add_distrib]
    rw [show (∑ d : fr.KW, eta (d₀ * d)) = ∑ e : fr.KW, eta e from
        Fintype.sum_equiv (Equiv.mulLeft d₀) (fun d => eta (d₀ * d)) eta (fun d => rfl)]
    rw [Finset.sum_const, Finset.card_univ, add_assoc]
    rw [show (Fintype.card fr.KW) • eta d₀ + eta d₀
        = (Fintype.card fr.KW + 1) • eta d₀ from by rw [add_nsmul, one_nsmul]]
    rw [hcard (eta d₀), add_zero]
  refine ⟨shiftIso eps e₀, fr.good_shiftIso he₀ eps, ?_⟩
  intro d x y hy
  have hconj : fr.conjQ d x = y := Subtype.ext (by rw [fr.conjQ_coe]; exact hy.symm)
  have hA : fr.actIso d (shiftIso eps e₀) = shiftIso eps e₀ := by
    rw [actIso_shiftIso, heta_spec d, shiftIso_comp]
    rw [show eta d + rhoFunC (fr.κ d) eps = eps from by
      rw [add_comm, ← fr.rho_apply]
      exact hfix d]
  have h0 : ∀ p : SZ (E n), SZ.torusAct (fr.κ d) (SZ.torusAct (fr.κ d)⁻¹ p) = p := by
    intro p
    rw [FMap.torusAct_mul, mul_inv_cancel]
    ext <;> simp
  have hx : SZ.torusAct (fr.κ d)⁻¹ ((shiftIso eps e₀) (fr.conjQ d x))
      = (shiftIso eps e₀) x := by
    have hc := congrArg (fun f : Q ≃* SZ (E n) => f x) hA
    simpa only [fr.actIso_apply] using hc
  rw [← hconj]
  calc (shiftIso eps e₀) (fr.conjQ d x)
      = SZ.torusAct (fr.κ d)
          (SZ.torusAct (fr.κ d)⁻¹ ((shiftIso eps e₀) (fr.conjQ d x))) := (h0 _).symm
    _ = SZ.torusAct (fr.κ d) ((shiftIso eps e₀) x) := by rw [hx]

end Work.PSU3.CoarseFrame
