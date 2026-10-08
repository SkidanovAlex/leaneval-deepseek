import Mathlib
import Submission.Work.PSU3.FineCoords.Setup
import Submission.Work.PSU3.FineCoords.bilinear_invariant_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open scoped commutatorElement

open Work.ThmF

namespace Work.PSU3.CoarseFrame

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## The element `u = κ ζ` of `E`

`E = GF(q²)`, `q = 2ⁿ`, and `u = κ ζ` is an element of `E^×` of norm one that is not fixed by
`σ`.  Its companion `γ = u + σu` lies in `F^×`, and `u² = γu + 1`, so `{1, u}` is an `F`-basis
of `E`: every element of `E` is `a + bu` with `a b ∈ F`. -/

/-- In a field of characteristic two, the only square root of `1` is `1`. -/
lemma mul_self_eq_one_of_char_two {K : Type*} [Field K] [CharP K 2] {x : K} (h : x * x = 1) :
    x = 1 := by
  have hq : (x + 1) * (x + 1) = 2 * (x + 1) := by
    have h1 : (x + 1) * (x + 1) = x * x + 2 * x + 1 := by ring
    rw [h1, h]
    ring
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h0 : (x + 1) * (x + 1) = 0 := by rw [hq, h2, zero_mul]
  exact CharTwo.add_eq_zero.mp (mul_self_eq_zero.mp h0)

/-- `u = κ ζ`. -/
def uK (fr : CoarseFrame H Q t n) : E n := (fr.κ fr.ζ : E n)

lemma uK_mul_sigma (fr : CoarseFrame H Q t n) : fr.uK * σE fr.uK = 1 := fr.ζ_norm

lemma uK_sigma (fr : CoarseFrame H Q t n) : σE fr.uK = (fr.uK)⁻¹ := by
  have hne : fr.uK ≠ 0 := (fr.κ fr.ζ).ne_zero
  have h := fr.uK_mul_sigma
  calc σE fr.uK = 1 * σE fr.uK := (one_mul _).symm
    _ = ((fr.uK)⁻¹ * fr.uK) * σE fr.uK := by rw [inv_mul_cancel₀ hne]
    _ = (fr.uK)⁻¹ * (fr.uK * σE fr.uK) := by rw [mul_assoc]
    _ = (fr.uK)⁻¹ * 1 := by rw [h]
    _ = (fr.uK)⁻¹ := mul_one _

lemma uK_not_fixed (fr : CoarseFrame H Q t n) : σE fr.uK ≠ fr.uK := by
  intro h
  have h1 : fr.uK * fr.uK = 1 := by
    have h' := fr.uK_mul_sigma
    rw [h] at h'
    exact h'
  have h2 : fr.uK = 1 := mul_self_eq_one_of_char_two h1
  have h3 : fr.κ fr.ζ = 1 := Units.ext h2
  exact fr.ζ_ne_one (fr.κ_injective (by rw [h3, map_one]))

/-- `γ = u + σu`. -/
noncomputable def gam (fr : CoarseFrame H Q t n) : E n := fr.uK + σE fr.uK

lemma gam_apply (fr : CoarseFrame H Q t n) : fr.gam = fr.uK + σE fr.uK := rfl

lemma gam_fixed (fr : CoarseFrame H Q t n) : σE fr.gam = fr.gam := by
  rw [gam_apply, map_add, σE_σE, add_comm]

lemma gam_ne_zero (fr : CoarseFrame H Q t n) : fr.gam ≠ 0 := by
  intro h
  exact fr.uK_not_fixed (CharTwo.add_eq_zero.mp h).symm

/-- `γ` as an element of `F`. -/
noncomputable def gamF (fr : CoarseFrame H Q t n) : Fx n := ⟨fr.gam, fr.gam_fixed⟩

@[simp] lemma gamF_coe (fr : CoarseFrame H Q t n) : ((fr.gamF : Fx n) : E n) = fr.gam := rfl

lemma gamF_ne_zero (fr : CoarseFrame H Q t n) : fr.gamF ≠ 0 := by
  intro h
  exact fr.gam_ne_zero (congrArg Subtype.val h)

lemma gam_mul_uK (fr : CoarseFrame H Q t n) : fr.gam * fr.uK + 1 = fr.uK * fr.uK := by
  have h := fr.uK_mul_sigma
  have h2 : (2 : E n) = 0 := CharTwo.two_eq_zero
  rw [gam_apply]
  linear_combination h + h2

lemma uK_sq (fr : CoarseFrame H Q t n) : fr.uK ^ 2 = fr.gam * fr.uK + 1 := by
  rw [pow_two, ← fr.gam_mul_uK]

/-- Every element of `E` is `a + b u` with `a b ∈ F`. -/
lemma exists_Fx_add_mul_uK (fr : CoarseFrame H Q t n) (x : E n) :
    ∃ a b : Fx n, x = (a : E n) + (b : E n) * fr.uK := by
  refine ⟨⟨x + (x + σE x) * fr.gam⁻¹ * fr.uK, ?_⟩, ⟨(x + σE x) * fr.gam⁻¹, ?_⟩, ?_⟩
  · have hb : σE ((x + σE x) * fr.gam⁻¹) = (x + σE x) * fr.gam⁻¹ := by
      rw [map_mul, map_inv₀, fr.gam_fixed, map_add, σE_σE, add_comm]
    have hbγ : (x + σE x) * fr.gam⁻¹ * fr.gam = x + σE x := by
      rw [mul_assoc, inv_mul_cancel₀ fr.gam_ne_zero, mul_one]
    have hbu : (x + σE x) * fr.gam⁻¹ * (fr.uK + fr.uK⁻¹) = x + σE x := by
      have h1 : fr.uK + fr.uK⁻¹ = fr.gam := by rw [gam_apply, fr.uK_sigma]
      rw [h1, hbγ]
    refine CharTwo.add_eq_zero.mp ?_
    rw [map_add, map_mul, hb, fr.uK_sigma]
    calc σE x + (x + σE x) * fr.gam⁻¹ * fr.uK⁻¹ + (x + (x + σE x) * fr.gam⁻¹ * fr.uK)
        = (x + σE x) + ((x + σE x) * fr.gam⁻¹ * fr.uK⁻¹
            + (x + σE x) * fr.gam⁻¹ * fr.uK) := by abel
      _ = (x + σE x) + (x + σE x) * fr.gam⁻¹ * (fr.uK⁻¹ + fr.uK) := by ring
      _ = (x + σE x) + (x + σE x) * fr.gam⁻¹ * (fr.uK + fr.uK⁻¹) := by rw [add_comm (fr.uK⁻¹)]
      _ = (x + σE x) + (x + σE x) := by rw [hbu]
      _ = 0 := CharTwo.add_self_eq_zero _
  · show σE ((x + σE x) * fr.gam⁻¹) = (x + σE x) * fr.gam⁻¹
    rw [map_mul, map_inv₀, fr.gam_fixed, map_add, σE_σE, add_comm]
  · show x = (x + (x + σE x) * fr.gam⁻¹ * fr.uK) + (x + σE x) * fr.gam⁻¹ * fr.uK
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-! ## `bet` is homogeneous of degree two over `F` -/

lemma bet_zero_left (fr : CoarseFrame H Q t n) (c : E n) : fr.bet 0 c = 0 := by
  apply fr.zc0_injective
  rw [fr.zc0_bet, fr.zc0_zero]
  apply Subtype.ext
  exact fr.commutator_eq_one_Q0_G (fr.sect c).2
    ((fr.barA_eq_zero_iff _).mp (by rw [fr.sect_barA]))

lemma bet_zero_right (fr : CoarseFrame H Q t n) (a : E n) : fr.bet a 0 = 0 := by
  apply fr.zc0_injective
  rw [fr.zc0_bet, fr.zc0_zero]
  apply Subtype.ext
  exact fr.commutator_Q0_eq_one_G ((fr.barA_eq_zero_iff _).mp (by rw [fr.sect_barA]))
    (fr.sect a).2

lemma bet_smul (fr : CoarseFrame H Q t n)
    (hsq : ∀ a : (E n)ˣ, σE (a : E n) = a → (fr.nm a : E n) = (a : E n) ^ 2)
    (s : Fx n) (a c : E n) :
    fr.bet ((s : E n) * a) ((s : E n) * c) = sqFx s * fr.bet a c := by
  rcases eq_or_ne (s : E n) 0 with h0 | h0
  · have hs0 : s = 0 := Subtype.ext h0
    rw [hs0, show ((0 : Fx n) : E n) = (0 : E n) from rfl, zero_mul, zero_mul,
      fr.bet_zero_left, sqFx_zero, zero_mul]
  · obtain ⟨d, hd⟩ := fr.K_surj (Units.mk0 (s : E n) h0) s.2
    have hdval : (fr.κ d : E n) = (s : E n) := by rw [hd, Units.val_mk0]
    have hκd : σE ((fr.κ d : (E n)ˣ) : E n) = ((fr.κ d : (E n)ˣ) : E n) := by
      rw [hdval]; exact s.2
    have hdK : (d : G) ∈ Ksub H t := (fr.mem_K_iff d).mpr hκd
    have hnm : (fr.nm (fr.κ d) : E n) = (s : E n) ^ 2 := by
      rw [hsq (fr.κ d) hκd, hdval]
    have hba : fr.barA (fr.conjQ d (fr.sect a)) = (s : E n) * a := by
      rw [fr.barA_conjQ, fr.sect_barA, hdval]
    have hbc : fr.barA (fr.conjQ d (fr.sect c)) = (s : E n) * c := by
      rw [fr.barA_conjQ, fr.sect_barA, hdval]
    have hL : fr.zc (fr.bet ((s : E n) * a) ((s : E n) * c) : E n)
        = ⁅((fr.sect ((s : E n) * c) : Q) : G), ((fr.sect ((s : E n) * a) : Q) : G)⁆ :=
      congrArg Subtype.val (fr.zc0_bet _ _)
    have hc : ⁅((fr.sect ((s : E n) * c) : Q) : G), ((fr.sect ((s : E n) * a) : Q) : G)⁆
        = ⁅((fr.conjQ d (fr.sect c) : Q) : G), ((fr.conjQ d (fr.sect a) : Q) : G)⁆ :=
      fr.commutator_eq_of_barA_eq (hbc.trans (fr.sect_barA _).symm)
        (hba.trans (fr.sect_barA _).symm)
    have hconj : ⁅((fr.conjQ d (fr.sect c) : Q) : G), ((fr.conjQ d (fr.sect a) : Q) : G)⁆
        = (d : G)⁻¹ * ⁅((fr.sect c : Q) : G), ((fr.sect a : Q) : G)⁆ * (d : G) := by
      rw [conjQ_coe, conjQ_coe]
      group
    have hR : ⁅((fr.sect c : Q) : G), ((fr.sect a : Q) : G)⁆
        = fr.zc (fr.bet a c : E n) := (congrArg Subtype.val (fr.zc0_bet a c)).symm
    have hmain : fr.zc (fr.bet ((s : E n) * a) ((s : E n) * c) : E n)
        = (d : G)⁻¹ * fr.zc (fr.bet a c : E n) * (d : G) := by
      rw [hL, hc, hconj, hR]
    have hact : (d : G)⁻¹ * fr.zc (fr.bet a c : E n) * (d : G)
        = fr.zc ((fr.nm (fr.κ d) : E n) * (fr.bet a c : E n)) :=
      fr.act_zc_K d hdK (fr.bet a c : E n) (fr.bet a c).2
    have hfin : fr.zc ((fr.nm (fr.κ d) : E n) * (fr.bet a c : E n))
        = fr.zc ((sqFx s * fr.bet a c : Fx n) : E n) := by
      rw [hnm]
      rfl
    apply fr.zc_inj_Fx
    rw [hmain, hact, hfin]

/-! ## The bilinear form `φ(a, b) = bet a (b u)` -/

/-- `φ(a,b) = bet a (b u)`, an `F`-bilinear form which is determined up to a scalar. -/
noncomputable def phi (fr : CoarseFrame H Q t n) (a b : Fx n) : Fx n :=
  fr.bet (a : E n) ((b : E n) * fr.uK)

lemma phi_add_left (fr : CoarseFrame H Q t n) (a a' b : Fx n) :
    fr.phi (a + a') b = fr.phi a b + fr.phi a' b := by
  show fr.bet ((a + a' : Fx n) : E n) ((b : E n) * fr.uK) = _
  rw [show ((a + a' : Fx n) : E n) = (a : E n) + (a' : E n) from rfl, fr.bet_add_left]
  rfl

lemma phi_add_right (fr : CoarseFrame H Q t n) (a b b' : Fx n) :
    fr.phi a (b + b') = fr.phi a b + fr.phi a b' := by
  show fr.bet (a : E n) (((b + b' : Fx n) : E n) * fr.uK) = _
  rw [show (((b + b' : Fx n) : E n) * fr.uK)
      = (b : E n) * fr.uK + (b' : E n) * fr.uK from by
    rw [show ((b + b' : Fx n) : E n) = (b : E n) + (b' : E n) from rfl]; ring]
  rw [fr.bet_add_right]
  rfl

lemma phi_hinv (fr : CoarseFrame H Q t n)
    (hsq : ∀ a : (E n)ˣ, σE (a : E n) = a → (fr.nm a : E n) = (a : E n) ^ 2)
    (tt a b : Fx n) : fr.phi (tt * a) (tt * b) = tt ^ 2 * fr.phi a b := by
  show fr.bet ((tt * a : Fx n) : E n) (((tt * b : Fx n) : E n) * fr.uK) = _
  rw [show ((tt * a : Fx n) : E n) = (tt : E n) * (a : E n) from rfl,
    show ((tt * b : Fx n) : E n) = (tt : E n) * (b : E n) from rfl,
    show (tt : E n) * (b : E n) * fr.uK = (tt : E n) * ((b : E n) * fr.uK) from by ring]
  rw [fr.bet_smul hsq tt (a : E n) ((b : E n) * fr.uK)]
  rfl

lemma phi_eq (fr : CoarseFrame H Q t n)
    (hsq : ∀ a : (E n)ˣ, σE (a : E n) = a → (fr.nm a : E n) = (a : E n) ^ 2)
    (a b : Fx n) : fr.phi a b = fr.phi 1 1 * (a * b) :=
  FineCoords.bilinear_invariant_eq fr.phi fr.phi_add_left fr.phi_add_right (fr.phi_hinv hsq) a b

/-! ## `ψ` is `ψ(1)` times the norm -/

/-- In `F`, the "square" of an element is its second power. -/
lemma sqFx_eq_pow (tt : Fx n) : sqFx tt = tt ^ 2 := Subtype.ext rfl

lemma psi_F (fr : CoarseFrame H Q t n)
    (hsq : ∀ a : (E n)ˣ, σE (a : E n) = a → (fr.nm a : E n) = (a : E n) ^ 2) (tt : Fx n) :
    (fr.psi (tt : E n) : Fx n) = tt ^ 2 * fr.psi 1 := by
  rw [← mul_one (tt : E n), fr.psi_F_smul hsq tt 1, sqFx_eq_pow]

theorem psi_eq_mul_self (fr : CoarseFrame H Q t n)
    (hsq : ∀ a : (E n)ˣ, σE (a : E n) = a → (fr.nm a : E n) = (a : E n) ^ 2)
    (x : E n) : (fr.psi x : E n) = (fr.psi 1 : E n) * (x * σE x) := by
  have hwu : (fr.psi fr.uK : Fx n) = fr.psi 1 := by
    have h := fr.psi_zeta (1 : E n)
    rw [mul_one] at h
    exact h
  have hgamE : (fr.gamF : E n) = fr.uK + σE fr.uK := by
    rw [show (fr.gamF : E n) = fr.gam from rfl, gam_apply]
  -- `u * u = 1 + γ u`
  have hu2 : fr.uK * fr.uK = 1 + (fr.gamF : E n) * fr.uK := by
    have h := fr.uK_sq
    rw [pow_two, ← fr.gamF_coe] at h
    rw [show (fr.gamF : E n) * fr.uK + 1 = 1 + (fr.gamF : E n) * fr.uK from
      add_comm _ _] at h
    exact h
  -- `ξ γ = γ² w` from the `ζ`-invariance at `u`
  have hζ : fr.psi ((1 : E n) + (fr.gamF : E n) * fr.uK) = fr.psi 1 := by
    have h : fr.psi ((fr.κ fr.ζ : E n) * (fr.κ fr.ζ : E n)) = fr.psi (fr.κ fr.ζ : E n) :=
      fr.psi_zeta (fr.κ fr.ζ : E n)
    have h2 : (1 : E n) + (fr.gamF : E n) * fr.uK
        = (fr.κ fr.ζ : E n) * (fr.κ fr.ζ : E n) := by
      show (1 : E n) + (fr.gamF : E n) * fr.uK = fr.uK * fr.uK
      rw [hu2]
    rw [h2, h, show (fr.κ fr.ζ : E n) = fr.uK from rfl, hwu]
  have hkey : fr.bet (1 : E n) ((fr.gamF : E n) * fr.uK) + fr.psi 1
      + fr.psi ((fr.gamF : E n) * fr.uK) = fr.psi 1 := by
    rw [← fr.psi_add (1 : E n) ((fr.gamF : E n) * fr.uK), hζ]
  have hγw : fr.phi 1 fr.gamF + fr.gamF ^ 2 * fr.psi 1 = 0 := by
    rw [fr.psi_F_smul hsq fr.gamF fr.uK, hwu, sqFx_eq_pow] at hkey
    rw [show fr.bet (1 : E n) ((fr.gamF : E n) * fr.uK) + fr.psi 1 + fr.gamF ^ 2 * fr.psi 1
        = (fr.bet (1 : E n) ((fr.gamF : E n) * fr.uK) + fr.gamF ^ 2 * fr.psi 1) + fr.psi 1
        from by abel] at hkey
    have h' : (fr.bet (1 : E n) ((fr.gamF : E n) * fr.uK) + fr.gamF ^ 2 * fr.psi 1)
        + fr.psi 1 = (0 : Fx n) + fr.psi 1 := by rw [zero_add]; exact hkey
    exact add_right_cancel h'
  have hxi : fr.phi 1 1 = fr.gamF * fr.psi 1 := by
    have h := hγw
    rw [show fr.phi 1 fr.gamF = fr.phi 1 1 * (1 * fr.gamF) from fr.phi_eq hsq 1 fr.gamF,
      one_mul] at h
    have h2 : fr.phi 1 1 * fr.gamF = (fr.gamF * fr.psi 1) * fr.gamF := by
      rw [CharTwo.add_eq_zero.mp h]; ring
    exact mul_right_cancel₀ fr.gamF_ne_zero h2
  -- a general element `a + b u`
  obtain ⟨a, b, rfl⟩ := fr.exists_Fx_add_mul_uK x
  have h1 : (fr.psi ((a : E n) + (b : E n) * fr.uK) : Fx n)
      = fr.psi 1 * (a ^ 2 + fr.gamF * a * b + b ^ 2) := by
    rw [fr.psi_add, fr.psi_F hsq a, fr.psi_F_smul hsq b fr.uK, hwu, sqFx_eq_pow,
      show fr.bet (a : E n) ((b : E n) * fr.uK) = fr.phi a b from rfl, fr.phi_eq hsq a b, hxi]
    ring
  have hxx : ((a : E n) + (b : E n) * fr.uK) * σE ((a : E n) + (b : E n) * fr.uK)
      = (a : E n) ^ 2 + (fr.gamF : E n) * (a : E n) * (b : E n) + (b : E n) ^ 2 := by
    rw [map_add, map_mul, a.2, b.2, hgamE]
    linear_combination ((b : E n) ^ 2) * fr.uK_mul_sigma
  rw [h1, hxx]
  push_cast
  ring

end Work.PSU3.CoarseFrame
