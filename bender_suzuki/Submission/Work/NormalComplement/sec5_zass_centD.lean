import Mathlib
import Submission.Work.NormalComplement.Design.Extra

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- In a finite group of odd order, the only element of order dividing `2` is `1`:
if `z * z = 1` then `z = 1`. -/
private lemma eq_one_of_mul_self_eq_one_of_odd_card {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hodd : Odd (Nat.card ↥H)) {z : G} (hz : z ∈ H) (hz2 : z * z = 1) :
    z = 1 := by
  have hdvd : orderOf (⟨z, hz⟩ : ↥H) ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (by simpa [pow_two] using hz2)
  have hodd' : Odd (orderOf (⟨z, hz⟩ : ↥H)) :=
    Odd.of_dvd_nat hodd (orderOf_dvd_natCard _)
  have hone : orderOf (⟨z, hz⟩ : ↥H) = 1 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two _ hdvd with h | h
    · exact h
    · rw [h] at hodd'
      norm_num at hodd'
  have : (⟨z, hz⟩ : ↥H) = 1 := orderOf_eq_one_iff.mp hone
  simpa using congrArg (fun w : ↥H => (w : G)) this

/-- **§5 (Zassenhaus step).**  Let `φ : F →* Y` be surjective with `ker φ = Z(F)`, with `Z(F)` of
odd order, let `Z(F) ≤ L ≤ F` and let `t ∈ F` be an involution.  If
`C_F(t) ∩ (L ∩ L^t) ≤ Z(F)`, then `C_{L̄}(t̄) ∩ L̄ ∩ L̄^{t̄} = 1` in `Y` (where `L̄ = L.map φ`,
`t̄ = φ t`), i.e. the "root subgroup" of the Zassenhaus group `Y = F/Z(F)` is trivial.

The point is that an element `x ∈ F` with `φ x ∈ L̄ ∩ L̄^{t̄}` lies in `L Z(F) ∩ L^t Z(F) = L ∩ L^t`
(as `Z(F) ≤ L ∩ L^t`), and `φ x` centralising `φ t` means `[x,t] ∈ Z(F)`; but then `[x,t] · t`,
being conjugate to the involution `t`, is itself an involution of order `2`, and since `[x,t]` is
central, `([x,t] · t)² = [x,t]² · t² = [x,t]²`; so `[x,t]² = 1`, whence `[x,t] = 1` as `Z(F)` has odd
order.  Thus `x ∈ C_F(t) ∩ (L ∩ L^t) ≤ Z(F)`, i.e. `φ x = 1`. -/
theorem sec5_zass_centD {F Y : Type} [Group F] [Finite F] [Group Y]
    (φ : F →* Y) (hsurj : Function.Surjective φ)
    (hker : φ.ker = Subgroup.center F) (hoddZ : Odd (Nat.card ↥(Subgroup.center F)))
    {L : Subgroup F} (hZL : Subgroup.center F ≤ L) {t : F} (ht2 : orderOf t = 2)
    (hcent : Subgroup.centralizer ({t} : Set F) ⊓ (L ⊓ L.map (MulAut.conj t).toMonoidHom) ≤
      Subgroup.center F) :
    Submission.Blueprint.centD (L.map φ) (φ t) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  simp only [Submission.Blueprint.centD, Submission.Blueprint.twoPoint,
    Submission.Blueprint.conj, Subgroup.mem_inf, Subgroup.mem_map] at hy
  obtain ⟨⟨⟨l, hlL, hlφ⟩, ⟨a, ⟨l', hl'L, hl'φ⟩, haφ⟩⟩, hyc⟩ := hy
  obtain ⟨x, hxy⟩ := hsurj y
  -- `x ∈ L`
  have hxZ₁ : x * l⁻¹ ∈ Subgroup.center F := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hxy, hlφ, mul_inv_cancel]
  have hxL : x ∈ L := by
    have h := hZL hxZ₁
    rw [show x = (x * l⁻¹) * l from by group]
    exact mul_mem h hlL
  -- `x ∈ L^t`
  have hZle : Subgroup.center F ≤ L.map (MulAut.conj t).toMonoidHom := by
    intro z hz
    refine ⟨z, hZL hz, ?_⟩
    rw [show (MulEquiv.toMonoidHom (MulAut.conj t)) z = t * z * t⁻¹ from MulAut.conj_apply t z]
    rw [Subgroup.mem_center_iff.mp hz t, mul_assoc, mul_inv_cancel, mul_one]
  have hm_mem : t * l' * t⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom :=
    ⟨l', hl'L, MulAut.conj_apply t l'⟩
  have hmφ : φ (t * l' * t⁻¹) = y := by
    have h1 : φ (t * l' * t⁻¹) = (MulAut.conj (φ t)) (φ l') := by
      simp [MulAut.conj_apply]
    rw [h1, hl'φ]
    exact haφ
  have hxZ₂ : x * (t * l' * t⁻¹)⁻¹ ∈ Subgroup.center F := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hxy, hmφ, mul_inv_cancel]
  have hxLt : x ∈ L.map (MulAut.conj t).toMonoidHom := by
    have h1 : x * (t * l' * t⁻¹)⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom := hZle hxZ₂
    have h2 : (x * (t * l' * t⁻¹)⁻¹) * (t * l' * t⁻¹) ∈ L.map (MulAut.conj t).toMonoidHom :=
      Subgroup.mul_mem _ h1 hm_mem
    rwa [show (x * (t * l' * t⁻¹)⁻¹) * (t * l' * t⁻¹) = x from by group] at h2
  -- `t` is an involution
  have ht2' : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  -- `φ x` commutes with `φ t`, so `[x,t] ∈ Z(F)`, and `[x,t]` is an involution
  have hyc' : φ x ∈ Subgroup.centralizer ({φ t} : Set Y) := by rwa [← hxy] at hyc
  have hcomm : φ x * φ t = φ t * φ x := Subgroup.mem_centralizer_singleton_iff.mp hyc'
  have hwker : x * t * x⁻¹ * t⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  have hwZ : x * t * x⁻¹ * t⁻¹ ∈ Subgroup.center F := by rw [← hker]; exact hwker
  have hwt : x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t := by group
  have hsq : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
    rw [show x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ from by group, ht2']
    group
  have hwsq : (x * t * x⁻¹ * t⁻¹) * (x * t * x⁻¹ * t⁻¹) = 1 := by
    have h1 : (x * t * x⁻¹ * t⁻¹) * t * ((x * t * x⁻¹ * t⁻¹) * t) = 1 := by
      rw [← hwt]; exact hsq
    have h2 : (x * t * x⁻¹ * t⁻¹) * t * ((x * t * x⁻¹ * t⁻¹) * t)
        = (x * t * x⁻¹ * t⁻¹) * (x * t * x⁻¹ * t⁻¹) := by
      calc (x * t * x⁻¹ * t⁻¹) * t * ((x * t * x⁻¹ * t⁻¹) * t)
          = (x * t * x⁻¹ * t⁻¹) * (t * (x * t * x⁻¹ * t⁻¹)) * t := by group
        _ = (x * t * x⁻¹ * t⁻¹) * ((x * t * x⁻¹ * t⁻¹) * t) * t := by
              rw [Subgroup.mem_center_iff.mp hwZ t]
        _ = (x * t * x⁻¹ * t⁻¹) * (x * t * x⁻¹ * t⁻¹) * (t * t) := by group
        _ = (x * t * x⁻¹ * t⁻¹) * (x * t * x⁻¹ * t⁻¹) := by rw [ht2', mul_one]
    rw [h2] at h1
    exact h1
  have hw1 : x * t * x⁻¹ * t⁻¹ = 1 :=
    eq_one_of_mul_self_eq_one_of_odd_card hoddZ hwZ hwsq
  have hconj : x * t * x⁻¹ = t := by rw [hwt, hw1, one_mul]
  have hxt : x * t = t * x := by
    calc x * t = (x * t * x⁻¹) * x := by group
      _ = t * x := by rw [hconj]
  have hmemC : x ∈ Subgroup.centralizer ({t} : Set F) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxt
  have hxZ : x ∈ Subgroup.center F := hcent ⟨hmemC, hxL, hxLt⟩
  rw [← hxy, ← MonoidHom.mem_ker, hker]
  exact hxZ

end Work.NormalComplement
