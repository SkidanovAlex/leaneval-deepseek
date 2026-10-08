import Mathlib
import Submission.Work.ThreePoints.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi I, Appendix I (1) (b): the decomposition `X = C_X(t) · J(X,t)`

For an involution `t` normalising a subgroup `X` of odd order, the multiplication map
`(v, x) ↦ v * x` is a bijection `C_X(t) × J(X,t) → X`, where `J(X,t) = {x ∈ X | x^t = x⁻¹}`;
equivalently `|X| = |C_X(t)| · |J(X,t)|`.

The proof follows Peterfalvi, *Le théorème de Bender–Suzuki I*, Appendix I (1): the map
`θ : X → G`, `θ(x) = x⁻¹ x^t`, takes its values in `J(X,t)` and every element of `J(X,t)`
has a (unique, as `|X|` is odd) square root which again lies in `J(X,t)`; this produces an
explicit two-sided inverse of `(v, x) ↦ v * x`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Submission.Blueprint

namespace Work.ThreePoints

variable {G : Type} [Group G]

/-- `θ(x) = x⁻¹ x^t = x⁻¹ · t x t⁻¹`.  If `t` normalises `X` and `t² = 1`, then `θ` maps
`X` into `J(X,t) = {y ∈ X | y^t = y⁻¹}`; this is the map used in Peterfalvi I App. I (1). -/
def thetaInverted (X : Subgroup G) (t : G) (x : X) : G :=
  (x : G)⁻¹ * (t * (x : G) * t⁻¹)

/-- Peterfalvi I Appendix I (1) (b): if the involution `t` normalises a subgroup `X` of odd order,
then `|X| = |C_X(t)| · |J(X,t)|` where `J(X,t) = {x ∈ X | x^t = x⁻¹}`; equivalently the map
`(v, x) ↦ v * x` is a bijection `C_X(t) × J(X,t) → X`. -/
theorem card_eq_mul_ncard_invertedBy {G : Type} [Group G] [Finite G] {X : Subgroup G} {t : G}
    (ht : orderOf t = 2) (hodd : Odd (Nat.card X))
    (hnt : t ∈ Subgroup.normalizer (X : Set G)) :
    Nat.card X = Nat.card (X ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) *
      (Submission.Blueprint.invertedBy X t).ncard := by
  classical
  -- work with an explicit `Fintype` structure so that `pow_card_eq_one` applies.
  haveI : Fintype G := Fintype.ofFinite G
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, pow_two] at h
    exact h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  -- `J = J(X,t)` and `V = C_X(t)`.
  set J : Set G := invertedBy X t with hJ
  set V : Subgroup G := (X ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) with hV
  have memJ : ∀ g : G, g ∈ J ↔ g ∈ X ∧ t * g * t⁻¹ = g⁻¹ := by
    intro g; rw [hJ]; exact Iff.rfl
  have memV : ∀ g : G, g ∈ V ↔ g ∈ X ∧ g * t = t * g := by
    intro g
    simp only [hV, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hJleX : ∀ g : G, g ∈ J → g ∈ X := fun g hg => (memJ g).mp hg |>.1
  -- squaring on `X` is bijective because `|X|` is odd.
  obtain ⟨k, hk⟩ := hodd
  have hXcard : Fintype.card X = 2 * k + 1 := by
    rw [← Nat.card_eq_fintype_card]; exact hk
  have h2k : 2 * (k + 1) = Fintype.card X + 1 := by rw [hXcard]; ring
  have h2k' : (k + 1) * 2 = Fintype.card X + 1 := by rw [Nat.mul_comm]; exact h2k
  have hinjX : Function.Injective (fun y : X => y ^ 2) := by
    intro a b hab
    have hab' : a ^ 2 = b ^ 2 := hab
    calc a = (a ^ 2) ^ (k + 1) := by rw [← pow_mul, h2k, pow_succ, pow_card_eq_one, one_mul]
      _ = (b ^ 2) ^ (k + 1) := by rw [hab']
      _ = b := by rw [← pow_mul, h2k, pow_succ, pow_card_eq_one, one_mul]
  have hsurjX : ∀ y : X, ∃ z : X, z ^ 2 = y := by
    intro y
    exact ⟨y ^ (k + 1), by rw [← pow_mul, h2k', pow_succ, pow_card_eq_one, one_mul]⟩
  -- `t` acts as an automorphism of `X`.
  have hconjX : ∀ x : G, x ∈ X → t * x * t⁻¹ ∈ X :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hnt x).mp hx
  have hcc : ∀ x : G, t * (t * x * t⁻¹) * t⁻¹ = x := by
    intro x
    rw [show t⁻¹ = t from htinv]
    calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht2]; simp
  -- `θ` takes values in `J`.
  have theta_mem : ∀ x : X, thetaInverted X t x ∈ J := by
    intro x
    refine (memJ _).mpr ⟨X.mul_mem (X.inv_mem x.2) (hconjX _ x.2), ?_⟩
    show t * ((x : G)⁻¹ * (t * (x : G) * t⁻¹)) * t⁻¹ = ((x : G)⁻¹ * (t * (x : G) * t⁻¹))⁻¹
    calc t * ((x : G)⁻¹ * (t * (x : G) * t⁻¹)) * t⁻¹
        = (t * (x : G)⁻¹ * t⁻¹) * (t * (t * (x : G) * t⁻¹) * t⁻¹) := by group
      _ = (t * (x : G) * t⁻¹)⁻¹ * (x : G) := by rw [hcc]; group
      _ = ((x : G)⁻¹ * (t * (x : G) * t⁻¹))⁻¹ := by group
  -- every element of `J` has a square root in `J` (Peterfalvi's counting, made effective).
  have hsqrtJ : ∀ x : X, ∃ j : G, j ∈ J ∧ j ^ 2 = (thetaInverted X t x)⁻¹ := by
    intro x
    have hxJ : thetaInverted X t x ∈ J := theta_mem x
    obtain ⟨y, hy⟩ := hsurjX ⟨(thetaInverted X t x)⁻¹, X.inv_mem (hJleX _ hxJ)⟩
    have hyG : (y : G) * (y : G) = (thetaInverted X t x)⁻¹ := by
      have h := congrArg Subtype.val hy
      simpa [Subgroup.coe_pow, pow_two] using h
    refine ⟨(y : G), ?_, by rw [pow_two]; exact hyG⟩
    refine (memJ (y : G)).mpr ⟨y.2, ?_⟩
    -- `t y t⁻¹` and `y⁻¹` are both square roots of `θ(x)`, hence equal.
    have hzt : t * (y : G) * t⁻¹ ∈ X := hconjX _ y.2
    have hsq : (t * (y : G) * t⁻¹) * (t * (y : G) * t⁻¹) = ((y : G)⁻¹) * ((y : G)⁻¹) := by
      have h1 : (t * (y : G) * t⁻¹) * (t * (y : G) * t⁻¹) = thetaInverted X t x := by
        calc (t * (y : G) * t⁻¹) * (t * (y : G) * t⁻¹)
            = t * ((y : G) * (y : G)) * t⁻¹ := by group
          _ = t * (thetaInverted X t x)⁻¹ * t⁻¹ := by rw [hyG]
          _ = (t * (thetaInverted X t x) * t⁻¹)⁻¹ := by group
          _ = ((thetaInverted X t x)⁻¹)⁻¹ := by rw [((memJ _).mp hxJ).2]
          _ = thetaInverted X t x := by rw [inv_inv]
      have h2 : ((y : G)⁻¹) * ((y : G)⁻¹) = thetaInverted X t x := by
        rw [← mul_inv_rev, hyG, inv_inv]
      rw [h1, h2]
    have h2 : (⟨t * (y : G) * t⁻¹, hzt⟩ : X) ^ 2 = (⟨(y : G)⁻¹, X.inv_mem y.2⟩ : X) ^ 2 := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow, pow_two] using hsq
    simpa using congrArg Subtype.val (hinjX h2)
  let jfun : X → G := fun x => Classical.choose (hsqrtJ x)
  have jfun_mem : ∀ x : X, jfun x ∈ J := fun x => (Classical.choose_spec (hsqrtJ x)).1
  have jfun_sq : ∀ x : X, (jfun x) ^ 2 = (thetaInverted X t x)⁻¹ :=
    fun x => (Classical.choose_spec (hsqrtJ x)).2
  -- the square root in `J` is unique.
  have huniq : ∀ a b : G, a ∈ J → b ∈ J → a ^ 2 = b ^ 2 → a = b := by
    intro a b ha hb hab
    have haX : a ∈ X := (memJ a).mp ha |>.1
    have hbX : b ∈ X := (memJ b).mp hb |>.1
    have h2 : (⟨a, haX⟩ : X) ^ 2 = (⟨b, hbX⟩ : X) ^ 2 := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow] using hab
    simpa using congrArg Subtype.val (hinjX h2)
  have hJinv : ∀ g : G, g ∈ J → t * g * t⁻¹ = g⁻¹ := fun g hg => (memJ g).mp hg |>.2
  have hJconj_inv : ∀ g : G, g ∈ J → t * g⁻¹ * t⁻¹ = g := by
    intro g hg
    calc t * g⁻¹ * t⁻¹ = (t * g * t⁻¹)⁻¹ := by group
      _ = (g⁻¹)⁻¹ := by rw [hJinv g hg]
      _ = g := by rw [inv_inv]
  have hVconj : ∀ g : G, g ∈ V → t * g * t⁻¹ = g := by
    intro g hg
    have hgt : g * t = t * g := (memV g).mp hg |>.2
    calc t * g * t⁻¹ = (g * t) * t⁻¹ := by rw [← hgt]
      _ = g := by group
  -- the explicit bijection `X ≃ C_X(t) × J(X,t)`.
  let e : X ≃ V × ↥J :=
    { toFun := fun x => (⟨(x : G) * (jfun x)⁻¹, by
          refine (memV _).mpr ⟨X.mul_mem x.2 (X.inv_mem (hJleX _ (jfun_mem x))), ?_⟩
          have hjinv := hJconj_inv _ (jfun_mem x)
          have hkey : (t * (x : G) * t⁻¹) * (thetaInverted X t x)⁻¹ = (x : G) := by
            show (t * (x : G) * t⁻¹) * ((x : G)⁻¹ * (t * (x : G) * t⁻¹))⁻¹ = (x : G)
            group
          have hmid : (t * (x : G) * t⁻¹) * (jfun x) = (x : G) * (jfun x)⁻¹ := by
            calc (t * (x : G) * t⁻¹) * (jfun x)
                = (t * (x : G) * t⁻¹) * ((jfun x * jfun x) * (jfun x)⁻¹) := by group
              _ = (t * (x : G) * t⁻¹) * ((thetaInverted X t x)⁻¹ * (jfun x)⁻¹) := by
                    rw [← pow_two (jfun x), jfun_sq x]
              _ = ((t * (x : G) * t⁻¹) * (thetaInverted X t x)⁻¹) * (jfun x)⁻¹ := by group
              _ = (x : G) * (jfun x)⁻¹ := by rw [hkey]
          have hcont : t * ((x : G) * (jfun x)⁻¹) * t⁻¹ = (x : G) * (jfun x)⁻¹ := by
            calc t * ((x : G) * (jfun x)⁻¹) * t⁻¹
                = (t * (x : G) * t⁻¹) * (t * (jfun x)⁻¹ * t⁻¹) := by group
              _ = (t * (x : G) * t⁻¹) * (jfun x) := by rw [hjinv]
              _ = (x : G) * (jfun x)⁻¹ := hmid
          calc ((x : G) * (jfun x)⁻¹) * t
              = (t * ((x : G) * (jfun x)⁻¹) * t⁻¹) * t := by rw [hcont]
            _ = t * ((x : G) * (jfun x)⁻¹) := by group⟩,
        ⟨jfun x, jfun_mem x⟩)
      invFun := fun p => ⟨(p.1 : G) * (p.2 : G),
        X.mul_mem ((memV _).mp p.1.2).1 ((memJ _).mp p.2.2).1⟩
      left_inv := by
        intro x
        apply Subtype.ext
        show ((x : G) * (jfun x)⁻¹) * (jfun x) = (x : G)
        group
      right_inv := by
        intro p
        set y : X := ⟨(p.1 : G) * (p.2 : G),
          X.mul_mem ((memV _).mp p.1.2).1 ((memJ _).mp p.2.2).1⟩ with hy
        have htheta : thetaInverted X t y = (p.2 : G)⁻¹ * (p.2 : G)⁻¹ := by
          show ((p.1 : G) * (p.2 : G))⁻¹ * (t * ((p.1 : G) * (p.2 : G)) * t⁻¹)
            = (p.2 : G)⁻¹ * (p.2 : G)⁻¹
          have hc : t * (p.1 : G) * t⁻¹ = (p.1 : G) := hVconj _ p.1.2
          have hj : t * (p.2 : G) * t⁻¹ = (p.2 : G)⁻¹ := hJinv _ p.2.2
          rw [show t * ((p.1 : G) * (p.2 : G)) * t⁻¹
                = (t * (p.1 : G) * t⁻¹) * (t * (p.2 : G) * t⁻¹) from by group, hc, hj]
          group
        have hjeq : jfun y = (p.2 : G) := by
          refine huniq _ _ (jfun_mem y) p.2.2 ?_
          rw [jfun_sq, htheta]
          group
        refine Prod.ext ?_ ?_
        · apply Subtype.ext
          show ((p.1 : G) * (p.2 : G)) * (jfun y)⁻¹ = (p.1 : G)
          rw [hjeq]
          group
        · apply Subtype.ext
          exact hjeq }
  have hcard : Nat.card X = Nat.card V * Nat.card ↥J := by
    rw [Nat.card_congr e, Nat.card_prod]
  rw [hcard, Nat.card_coe_set_eq]

end Work.ThreePoints
