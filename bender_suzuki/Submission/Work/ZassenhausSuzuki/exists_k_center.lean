import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.suzukiFProp
import Submission.Work.ZassenhausSuzuki.SzA.mem_center_iff
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q
import Submission.Work.ThmF.Bender.DTransitiveInv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.exists_k_center`

Given a Zassenhaus split rank-one configuration `H = Q ⋊ D` (`D = twoPoint H t = H ∩ Hᵗ`) with
`Q` a `2`-group, coordinated with Higman's group `A(K,θ) = SzA K θ` by an isomorphism
`e : Q ≃* A(K,θ)` through which the two-point stabiliser `D` acts by the standard torus
(`TorusCoords K θ H Q t e`), we prove:

for every `s ∈ Z(Q) ∖ {1}` and every `h ∈ D ∖ {1}` there is `k ∈ D` with
`k⁻¹ s k = h⁻¹ * (h⁻¹ * s * h * s) * h`.

The element `R = h⁻¹ * (h⁻¹ * s * h * s) * h` is shown to be an involution of `H`: writing
`e s = (0,b)` (`s` is central in `Q`, so its image lies in the centre `{(0,c)}` of `A(K,θ)`)
and `λ = lamOf h` for the scalar by which `h` acts on `Q`, the conjugation formula of
`TorusCoords` gives

`e R = (0, μ⁻¹(μ⁻¹+1)·b)` with `μ = λ·θλ`,

whose second coordinate is non-zero because `λ ≠ 1` (`TorusCoords` is faithful, by
fixed-point-freeness of `D` on `Q^#` and Zassenhausness) and `ν·θν = 1 → ν = 1`.  Hence
`R ∈ Inv(H)`; as `s ∈ Inv(H)` too and `D` is transitive on `Inv(H)`, some `k ∈ D` conjugates
`s` to `R`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- Conjugates of elements of the root group `Q` by elements of the two-point stabiliser
`D = twoPoint H t` remain in `Q` (because `Q` is normal in `H`). -/
theorem mem_conj_mem (hsplit : IsSplitRankOne H Q t) {d : G} (hd : d ∈ twoPoint H t)
    {x : G} (hx : x ∈ Q) : d * x * d⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp (hsplit.normal (Subgroup.mem_inf.mp hd).1) x).mp hx

/-- The conjugate of `x : ↥Q` by `d ∈ D`, as an element of `Q`. -/
def conjQ (hsplit : IsSplitRankOne H Q t) (d : ↥(twoPoint H t)) (x : ↥Q) : ↥Q :=
  ⟨(d : G) * (x : G) * (d : G)⁻¹, mem_conj_mem hsplit d.2 x.2⟩

@[simp] theorem conjQ_coe (hsplit : IsSplitRankOne H Q t) (d : ↥(twoPoint H t)) (x : ↥Q) :
    ((conjQ hsplit d x : ↥Q) : G) = (d : G) * (x : G) * (d : G)⁻¹ := rfl

theorem conjQ_mul (hsplit : IsSplitRankOne H Q t) (d d' : ↥(twoPoint H t)) (x : ↥Q) :
    conjQ hsplit (d * d') x = conjQ hsplit d (conjQ hsplit d' x) := by
  apply Subtype.ext
  simp only [conjQ_coe, Subgroup.coe_mul]
  group

variable {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K} {e : Q ≃* SzA K θ}

/-- `λ_d`: the scalar by which `d ∈ D` acts on the root group `Q` in the coordinates `e`
(`TorusCoords`). -/
noncomputable def lamOf (hsplit : IsSplitRankOne H Q t) (htorus : TorusCoords K θ H Q t e)
    (d : ↥(twoPoint H t)) : Kˣ := Classical.choose (htorus (d : G) d.2)

theorem lamOf_spec (hsplit : IsSplitRankOne H Q t) (htorus : TorusCoords K θ H Q t e)
    (d : ↥(twoPoint H t)) (x : ↥Q) :
    e (conjQ hsplit d x) = SzA.hLam θ ((lamOf hsplit htorus d : K)) (e x) := by
  obtain ⟨y, hy, hye⟩ := (Classical.choose_spec (htorus (d : G) d.2)) x
  have hys : y = conjQ hsplit d x := Subtype.ext hy
  rwa [hys] at hye

theorem lamOf_one (hsplit : IsSplitRankOne H Q t) (htorus : TorusCoords K θ H Q t e) :
    lamOf hsplit htorus (1 : ↥(twoPoint H t)) = 1 := by
  refine Units.ext ?_
  have hspec := lamOf_spec hsplit htorus (1 : ↥(twoPoint H t)) (e.symm (⟨1, 0⟩ : SzA K θ))
  have hleft : conjQ hsplit (1 : ↥(twoPoint H t)) (e.symm (⟨1, 0⟩ : SzA K θ))
      = e.symm (⟨1, 0⟩ : SzA K θ) := by
    apply Subtype.ext
    simp [conjQ]
  rw [hleft, MulEquiv.apply_symm_apply] at hspec
  have h := congrArg SzA.a hspec
  simpa [SzA.hLam_a] using h.symm

theorem lamOf_mul (hsplit : IsSplitRankOne H Q t) (htorus : TorusCoords K θ H Q t e)
    (d d' : ↥(twoPoint H t)) :
    lamOf hsplit htorus (d * d') = lamOf hsplit htorus d * lamOf hsplit htorus d' := by
  have key : SzA.hLam θ ((lamOf hsplit htorus (d * d') : K)) (e (e.symm (⟨1, 0⟩ : SzA K θ)))
      = SzA.hLam θ (((lamOf hsplit htorus d * lamOf hsplit htorus d' : Kˣ) : K))
          (e (e.symm (⟨1, 0⟩ : SzA K θ))) := by
    rw [← lamOf_spec hsplit htorus (d * d') (e.symm (⟨1, 0⟩ : SzA K θ)), conjQ_mul, Units.val_mul,
      SzA.hLam_mul, ← lamOf_spec hsplit htorus d' (e.symm (⟨1, 0⟩ : SzA K θ)),
      ← lamOf_spec hsplit htorus d (conjQ hsplit d' (e.symm (⟨1, 0⟩ : SzA K θ)))]
  rw [MulEquiv.apply_symm_apply] at key
  have h := congrArg SzA.a key
  rw [SzA.hLam_a, SzA.hLam_a] at h
  exact Units.ext (by simpa using h)

theorem lamOf_inv (hsplit : IsSplitRankOne H Q t) (htorus : TorusCoords K θ H Q t e)
    (d : ↥(twoPoint H t)) : lamOf hsplit htorus d⁻¹ = (lamOf hsplit htorus d)⁻¹ := by
  have h : lamOf hsplit htorus d * lamOf hsplit htorus d⁻¹ = 1 := by
    rw [← lamOf_mul, mul_inv_cancel, lamOf_one]
  have hcongr := congrArg (fun x : Kˣ => (lamOf hsplit htorus d)⁻¹ * x) h
  simpa [mul_assoc] using hcongr

/-- The coordinate map `d ↦ λ_d` is faithful: `d` acts trivially on `Q` only for `d = 1`
(fixed-point-freeness of `D` on `Q^#`, i.e. Zassenhausness). -/
theorem lamOf_eq_one_iff (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (htorus : TorusCoords K θ H Q t e) {s : G} (hsQ : s ∈ Q) (hs1 : s ≠ 1)
    (d : ↥(twoPoint H t)) : lamOf hsplit htorus d = 1 ↔ d = 1 := by
  constructor
  · intro h
    by_contra hd1
    have hconj : (d : G) * s * (d : G)⁻¹ = s := by
      have hspec := lamOf_spec hsplit htorus d ⟨s, hsQ⟩
      rw [h] at hspec
      simp only [Units.val_one, SzA.hLam_one] at hspec
      have h2 := congrArg Subtype.val (e.injective hspec)
      simpa [conjQ_coe] using h2
    exact hs1 (Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q H Q t hsplit hzass (d : G) d.2
      (fun hc => hd1 (Subtype.ext hc)) s hsQ hconj)
  · intro h
    rw [h]
    exact lamOf_one hsplit htorus

/-- Conjugation of a central element of `Q` by `d ∈ D`, in the coordinates `e`: the scalar
`λ_d·θλ_d` acts on the centre `{(0,c)}` of `A(K,θ)`. -/
theorem conjQ_center_spec (hsplit : IsSplitRankOne H Q t) (htorus : TorusCoords K θ H Q t e)
    (d : ↥(twoPoint H t)) {z : ↥Q} {c : K} (hz : e z = (⟨0, c⟩ : SzA K θ)) :
    e (conjQ hsplit d z)
      = (⟨0, ((lamOf hsplit htorus d : K) * θ (lamOf hsplit htorus d : K)) * c⟩ :
          SzA K θ) := by
  rw [lamOf_spec hsplit htorus d z, hz]
  ext <;> simp only [SzA.hLam_a, SzA.hLam_b]
  ring

/-- Conjugation of a central element of `Q` by `d⁻¹ ∈ D`, in the coordinates `e`. -/
theorem conjQ_inv_center_spec (hsplit : IsSplitRankOne H Q t) (htorus : TorusCoords K θ H Q t e)
    (d : ↥(twoPoint H t)) {z : ↥Q} {c : K} (hz : e z = (⟨0, c⟩ : SzA K θ)) :
    e (conjQ hsplit d⁻¹ z)
      = (⟨0, (((lamOf hsplit htorus d : K) * θ (lamOf hsplit htorus d : K))⁻¹) * c⟩ :
          SzA K θ) := by
  rw [lamOf_spec hsplit htorus d⁻¹ z, lamOf_inv hsplit htorus d, hz]
  ext <;> simp only [SzA.hLam_a, SzA.hLam_b, Units.val_inv_eq_inv_val, map_inv₀, mul_inv]
  ring

theorem exists_k_center {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K}
    (hθ : Work.ZassenhausSuzuki.IsTitsTheta θ) {e : Q ≃* Work.ZassenhausSuzuki.SzA K θ}
    (htorus : Work.ZassenhausSuzuki.TorusCoords K θ H Q t e)
    {s : G} (hsQ : s ∈ Q) (hs1 : s ≠ 1) (hsc : ∀ x ∈ Q, s * x = x * s)
    {h : G} (hhD : h ∈ Submission.Blueprint.twoPoint H t) (hh1 : h ≠ 1) :
    ∃ k ∈ Submission.Blueprint.twoPoint H t,
      k⁻¹ * s * k = h⁻¹ * (h⁻¹ * s * h * s) * h := by
  classical
  have hθne : θ ≠ 1 := hθ.1
  -- ## Step 1: `e s` is central in `A(K,θ)`, so `e s = (0,b)`
  have hsc_center : e ⟨s, hsQ⟩ ∈ Subgroup.center (SzA K θ) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ : ∃ x : ↥Q, e x = y := ⟨e.symm y, MulEquiv.apply_symm_apply e y⟩
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hsc (x : G) x.2).symm)
  have ha0 : (e ⟨s, hsQ⟩).a = 0 := (SzA.mem_center_iff θ hθne _).mp hsc_center
  set b : K := (e ⟨s, hsQ⟩).b with hb
  have he_s : e ⟨s, hsQ⟩ = (⟨0, b⟩ : SzA K θ) := by ext <;> simp [b, ha0]
  have hb0 : b ≠ 0 := by
    intro hb0
    have h1 : e ⟨s, hsQ⟩ = 1 := by rw [he_s, hb0]; rfl
    have h2 : (⟨s, hsQ⟩ : ↥Q) = 1 := e.injective (by rw [h1]; exact (map_one e).symm)
    exact hs1 (by simpa using congrArg Subtype.val h2)
  -- ## Step 2: `s` is an involution of `H`
  have hss : s * s = 1 := by
    have h1 : e (⟨s, hsQ⟩ * ⟨s, hsQ⟩) = 1 := by
      rw [map_mul, he_s]
      ext <;> simp [SzA.mul_a, SzA.mul_b, CharTwo.add_self_eq_zero]
    have h2 : (⟨s, hsQ⟩ : ↥Q) * ⟨s, hsQ⟩ = 1 := e.injective (by rw [h1, map_one])
    simpa using congrArg Subtype.val h2
  have hs_inv : s ∈ involutions (H : Set G) :=
    ⟨hsplit.le hsQ, orderOf_eq_prime (by simpa [pow_two] using hss) hs1⟩
  -- ## Step 3: the torus scalar of `h`
  set dh : ↥(twoPoint H t) := ⟨h, hhD⟩ with hdh
  set zs : ↥Q := ⟨s, hsQ⟩ with hzs
  set lamH : Kˣ := lamOf hsplit htorus dh with hlamH
  set mu : K := (lamH : K) * θ (lamH : K) with hmu
  have hdhne : dh ≠ 1 := by
    intro hc
    have h1 : (dh : G) = 1 := by rw [hc]; exact Subgroup.coe_one _
    exact hh1 (by simpa [hdh] using h1)
  have hlamHne : lamH ≠ 1 := by
    intro hc
    have h1 : lamOf hsplit htorus dh = 1 := by rw [← hlamH]; exact hc
    exact hdhne ((lamOf_eq_one_iff hsplit hzass htorus hsQ hs1 dh).mp h1)
  have hmu0 : mu ≠ 0 := by
    rw [hmu]
    exact mul_ne_zero (Units.ne_zero lamH)
      (fun hc => Units.ne_zero lamH (θ.injective (by simpa using hc)))
  have hmu1 : mu ≠ 1 := by
    intro hc
    have h2 : (lamH : K) * θ (lamH : K) = 1 := by rw [← hmu]; exact hc
    exact hlamHne (Units.ext (mul_theta_eq_one θ hθ h2))
  have hmuinv1 : mu⁻¹ + 1 ≠ 0 := by
    intro hc
    have h3 : mu⁻¹ = -1 := eq_neg_of_add_eq_zero_left hc
    rw [CharTwo.neg_eq] at h3
    exact hmu1 (by simpa using congrArg (fun x : K => x⁻¹) h3)
  -- ## Step 4: the conjugate `R` of `s` by `h`
  set u1 : ↥Q := conjQ hsplit dh⁻¹ zs with hu1
  set u2 : ↥Q := u1 * zs with hu2
  set u3 : ↥Q := conjQ hsplit dh⁻¹ u2 with hu3
  have he_u1 : e u1 = (⟨0, mu⁻¹ * b⟩ : SzA K θ) := by
    rw [hu1]
    have h := conjQ_inv_center_spec hsplit htorus dh he_s
    rwa [← hlamH, ← hmu] at h
  have he_u2 : e u2 = (⟨0, (mu⁻¹ + 1) * b⟩ : SzA K θ) := by
    rw [hu2, map_mul, he_u1, he_s]
    ext <;> simp only [SzA.mul_a, SzA.mul_b, zero_mul, zero_add, add_zero]
    ring
  have he_u3 : e u3 = (⟨0, mu⁻¹ * ((mu⁻¹ + 1) * b)⟩ : SzA K θ) := by
    rw [hu3]
    have h := conjQ_inv_center_spec hsplit htorus dh he_u2
    rwa [← hlamH, ← hmu] at h
  have hc0 : mu⁻¹ * ((mu⁻¹ + 1) * b) ≠ 0 :=
    mul_ne_zero (inv_ne_zero hmu0) (mul_ne_zero hmuinv1 hb0)
  have hu3_ne : u3 ≠ 1 := by
    intro hc
    have h1 : (⟨0, mu⁻¹ * ((mu⁻¹ + 1) * b)⟩ : SzA K θ) = 1 := by
      rw [← he_u3, hc, map_one]
    exact hc0 (by simpa using congrArg SzA.b h1)
  have hu3_sq : u3 * u3 = 1 := by
    refine e.injective ?_
    rw [map_mul, he_u3, map_one]
    ext <;> simp [SzA.mul_a, SzA.mul_b, CharTwo.add_self_eq_zero]
  have hu3_val : (u3 : G) = h⁻¹ * (h⁻¹ * s * h * s) * h := by
    simp only [hu3, hu2, hu1, conjQ, hdh, hzs, Subtype.coe_mk, Subgroup.coe_mul,
      Subgroup.coe_inv]
    group
  -- ## Step 5: `R ∈ Inv(H)` and `D` is transitive on `Inv(H)`
  have hR_inv : (u3 : G) ∈ involutions (H : Set G) :=
    ⟨hsplit.le u3.2,
      orderOf_eq_prime (by simpa [pow_two] using congrArg Subtype.val hu3_sq)
        (fun hc => hu3_ne (Subtype.ext hc))⟩
  obtain ⟨d, hdD, hdconj⟩ :=
    Work.ThmF.Bender.DTransitiveInv hsplit.stronglyEmbedded hsplit.invol hsplit.not_mem
      s hs_inv (u3 : G) hR_inv
  exact ⟨d⁻¹, (twoPoint H t).inv_mem hdD, by rw [inv_inv, hdconj, hu3_val]⟩

end Work.ZassenhausSuzuki
