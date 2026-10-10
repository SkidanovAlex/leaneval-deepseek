import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_iff
import Submission.NK.NUV2.RouteB.Unif.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transfer of the ray-class equidistribution from a finer subgroup to a coarser one

(GENERIC part of `NK.NUV2.RouteB.sharp_rayClassCount_coprime`, re-based on the clash-free
imports `Unif.Defs` so that it can be used together with the `RayModulus` vocabulary.)

For subgroups `V ≤ W` of the ideles, the ray class group of `W` is a quotient of that of `V`; the
fibres of the quotient map are cosets of one subgroup (hence of equal size) and the class counts of
`W` are the sums of the class counts of `V` over the fibres.  Consequently a power-saving bound of
the form `|N_{c₁} - N_{c₂}| ≤ C X^θ` for the finer subgroup `V` transfers to the coarser one `W`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors

noncomputable section

namespace NK.NUV2.RouteB

open NK.GlobalCFT (Idele IdeleClassGroup)

variable {K : Type} [Field K] [NumberField K]

/-! ## The quotient map of ray class groups attached to nested subgroups -/

/-- For subgroups `V ≤ W` of the idèles, the canonical surjection
`𝕀 K ⧸ (Kˣ·V) →* 𝕀 K ⧸ (Kˣ·W)` (a coarser quotient of a finer one). -/
noncomputable def rayClassMapOfLe (V W : Subgroup (Idele K)) (hVW : V ≤ W) :
    IdeleClassGroup.rayClassGroup K V →* IdeleClassGroup.rayClassGroup K W :=
  haveI : (Idele.principalSubgroup K ⊔ V).Normal := Subgroup.normal_of_isMulCommutative _
  haveI : (Idele.principalSubgroup K ⊔ W).Normal := Subgroup.normal_of_isMulCommutative _
  QuotientGroup.map (Idele.principalSubgroup K ⊔ V) (Idele.principalSubgroup K ⊔ W)
    (MonoidHom.id (Idele K)) (by rw [Subgroup.comap_id]; exact sup_le_sup_left hVW _)

theorem rayClassMapOfLe_mk (V W : Subgroup (Idele K)) (hVW : V ≤ W) (x : Idele K) :
    rayClassMapOfLe V W hVW (QuotientGroup.mk' (Idele.principalSubgroup K ⊔ V) x)
      = QuotientGroup.mk' (Idele.principalSubgroup K ⊔ W) x := by
  haveI : (Idele.principalSubgroup K ⊔ V).Normal := Subgroup.normal_of_isMulCommutative _
  haveI : (Idele.principalSubgroup K ⊔ W).Normal := Subgroup.normal_of_isMulCommutative _
  exact QuotientGroup.map_mk' _ _ _ _ x

/-- The quotient map of ray class groups is compatible with `classOfIdeal`. -/
theorem rayClassMapOfLe_classOfIdeal (V W : Subgroup (Idele K)) (hVW : V ≤ W)
    (𝔞 : Ideal (𝓞 K)) :
    rayClassMapOfLe V W hVW (NK.HeckeL.classOfIdeal K V 𝔞)
      = NK.HeckeL.classOfIdeal K W 𝔞 := by
  rw [NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_mk (U := V) (I := 𝔞),
    NK.NUV2.RouteB.RayModulus.classOfIdeal_eq_mk (U := W) (I := 𝔞)]
  exact rayClassMapOfLe_mk V W hVW _

theorem rayClassMapOfLe_surjective (V W : Subgroup (Idele K)) (hVW : V ≤ W) :
    Function.Surjective (rayClassMapOfLe V W hVW) := by
  haveI : (Idele.principalSubgroup K ⊔ W).Normal := Subgroup.normal_of_isMulCommutative _
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Idele.principalSubgroup K ⊔ W) y
  refine ⟨QuotientGroup.mk' (Idele.principalSubgroup K ⊔ V) x, ?_⟩
  rw [rayClassMapOfLe_mk, hx]

/-! ## The class counts of a coarser ray class group are sums over the fibres -/

/-- **The fibre decomposition of the ray class counts.**  For `V ≤ W`, the number of ideals
coprime to `S` of norm `≤ N` in a class of `𝕀 K ⧸ (Kˣ·W)` is the sum, over the classes of
`𝕀 K ⧸ (Kˣ·V)` mapping to it, of the corresponding numbers. -/
theorem rayCnt_eq_sum_fiber (V W : Subgroup (Idele K)) (hVW : V ≤ W)
    [Fintype (IdeleClassGroup.rayClassGroup K V)]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (c : IdeleClassGroup.rayClassGroup K W) (N : ℕ) :
    rayCnt W S c N
      = ∑ c' ∈ Finset.univ.filter
          (fun c' : IdeleClassGroup.rayClassGroup K V => rayClassMapOfLe V W hVW c' = c),
        rayCnt V S c' N := by
  classical
  set t : Finset (IdeleClassGroup.rayClassGroup K V) :=
    Finset.univ.filter (fun c' => rayClassMapOfLe V W hVW c' = c) with ht
  have hfiber : ∀ c' ∈ t,
      (rayFinset W S c N).filter (fun 𝔞 => NK.HeckeL.classOfIdeal K V 𝔞 = c')
        = rayFinset V S c' N := by
    intro c' hc'
    rw [ht, Finset.mem_filter] at hc'
    obtain ⟨-, hc'⟩ := hc'
    rw [rayFinset, rayFinset, Finset.filter_filter]
    refine Finset.filter_congr ?_
    intro 𝔞 h𝔞
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at h𝔞
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
      exact ⟨h1, h2, h5, h4⟩
    · rintro ⟨h1, h2, h5, h4⟩
      exact ⟨⟨h1, h2, by rw [← rayClassMapOfLe_classOfIdeal V W hVW 𝔞, h5, hc'], h4⟩, h5⟩
  show (rayFinset W S c N).card = ∑ c' ∈ t, (rayFinset V S c' N).card
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun 𝔞 : Ideal (𝓞 K) => NK.HeckeL.classOfIdeal K V 𝔞) ?_]
  · exact Finset.sum_congr rfl (fun c' hc' => by rw [hfiber c' hc'])
  · intro 𝔞 h𝔞
    rw [Finset.mem_coe] at h𝔞 ⊢
    obtain ⟨h1, h2, h3, h4⟩ := (mem_rayFinset W S c N 𝔞).mp h𝔞
    rw [ht, Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      by
        change rayClassMapOfLe V W hVW (NK.HeckeL.classOfIdeal K V 𝔞) = c
        rw [rayClassMapOfLe_classOfIdeal V W hVW 𝔞, h3]⟩

/-! ## The sharp-count predicate and its transfer along inclusions -/

/-- **The sharp equidistribution of ideals in the ray classes of `W`, in `rayCnt` form.** -/
def SharpCount (K : Type) [Field K] [NumberField K] (W : Subgroup (Idele K))
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ c₁ c₂ : IdeleClassGroup.rayClassGroup K W,
    |((rayCnt W S c₁ N : ℝ) - (rayCnt W S c₂ N : ℝ))| ≤ C * (N : ℝ) ^ θ

/-- The `Nat.card`/real-`X` form of the sharp count implies the `rayCnt` form. -/
theorem SharpCount.of_natCard {W : Subgroup (Idele K)}
    {S : Finset (NK.HeckeL.PrimeIdeal K)} {θ : ℝ}
    (h : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ c₁ c₂ : IdeleClassGroup.rayClassGroup K W,
      |((Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
          NK.HeckeL.classOfIdeal K W 𝔞 = c₁ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ X} : ℝ)
        - (Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
          NK.HeckeL.classOfIdeal K W 𝔞 = c₂ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ X} : ℝ))|
        ≤ C * X ^ θ) : SharpCount K W S θ := by
  obtain ⟨C, hCpos, hC⟩ := h
  refine ⟨C, hCpos, fun N hN c₁ c₂ => ?_⟩
  rw [rayCnt_eq_natCard_real, rayCnt_eq_natCard_real]
  exact hC (N : ℝ) (by exact_mod_cast hN) c₁ c₂

/-- The `rayCnt` form of the sharp count implies the `Nat.card`/real-`X` form. -/
theorem SharpCount.to_natCard {W : Subgroup (Idele K)}
    {S : Finset (NK.HeckeL.PrimeIdeal K)} {θ : ℝ} (h : SharpCount K W S θ) (hθ : 0 ≤ θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ c₁ c₂ : IdeleClassGroup.rayClassGroup K W,
      |((Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
          NK.HeckeL.classOfIdeal K W 𝔞 = c₁ ∧ Ideal.absNorm 𝔞 ≤ X} : ℝ)
        - (Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
          NK.HeckeL.classOfIdeal K W 𝔞 = c₂ ∧ Ideal.absNorm 𝔞 ≤ X} : ℝ))|
        ≤ C * X ^ θ := by
  obtain ⟨C, hCpos, hC⟩ := h
  refine ⟨C, hCpos, fun X hX c₁ c₂ => ?_⟩
  have hX0 : (0 : ℝ) ≤ X := le_trans zero_le_one hX
  have hN : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa using hX)
  rw [← rayCnt_eq_natCard_le W S c₁ X hX0, ← rayCnt_eq_natCard_le W S c₂ X hX0]
  refine le_trans (hC ⌊X⌋₊ hN c₁ c₂) ?_
  refine mul_le_mul_of_nonneg_left ?_ hCpos.le
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hX0) hθ

/-- **Transfer of the sharp count from a finer subgroup to a coarser one.**  If `V ≤ W` and the
sharp count holds for `V`, then it holds for `W`, with constant multiplied by the (finite) order
of the kernel of the quotient map. -/
theorem SharpCount.of_le {V W : Subgroup (Idele K)} (hVW : V ≤ W)
    [Finite (IdeleClassGroup.rayClassGroup K V)]
    {S : Finset (NK.HeckeL.PrimeIdeal K)} {θ : ℝ} (h : SharpCount K V S θ) :
    SharpCount K W S θ := by
  classical
  haveI : Fintype (IdeleClassGroup.rayClassGroup K V) := Fintype.ofFinite _
  obtain ⟨C, hCpos, hC⟩ := h
  refine ⟨(Fintype.card (IdeleClassGroup.rayClassGroup K V) : ℝ) * C, by positivity, ?_⟩
  intro N hN c₁ c₂
  obtain ⟨u, hu⟩ := rayClassMapOfLe_surjective V W hVW (c₂ * c₁⁻¹)
  set s₁ : Finset (IdeleClassGroup.rayClassGroup K V) :=
    Finset.univ.filter (fun c' => rayClassMapOfLe V W hVW c' = c₁) with hs₁
  set s₂ : Finset (IdeleClassGroup.rayClassGroup K V) :=
    Finset.univ.filter (fun c' => rayClassMapOfLe V W hVW c' = c₂) with hs₂
  have hmem₁ : ∀ c' ∈ s₁, u * c' ∈ s₂ := by
    intro c' hc'
    rw [hs₂, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hs₁, Finset.mem_filter] at hc'
    rw [map_mul, hc'.2, hu]
    group
  have hmem₂ : ∀ c' ∈ s₂, u⁻¹ * c' ∈ s₁ := by
    intro c' hc'
    rw [hs₁, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hs₂, Finset.mem_filter] at hc'
    rw [map_mul, map_inv, hc'.2, hu]
    group
  -- the two sums
  have hsum₁ : rayCnt W S c₁ N = ∑ c' ∈ s₁, rayCnt V S c' N := by
    rw [hs₁]; exact rayCnt_eq_sum_fiber V W hVW S c₁ N
  have hsum₂₀ : rayCnt W S c₂ N = ∑ c' ∈ s₂, rayCnt V S c' N := by
    rw [hs₂]; exact rayCnt_eq_sum_fiber V W hVW S c₂ N
  have hreindex : (∑ c' ∈ s₁, rayCnt V S (u * c') N) = ∑ c' ∈ s₂, rayCnt V S c' N := by
    refine Finset.sum_bij (fun c' _ => u * c') hmem₁ ?_ ?_ ?_
    · intro a₁ ha₁ a₂ ha₂ h
      exact mul_left_cancel h
    · intro b hb
      exact ⟨u⁻¹ * b, hmem₂ b hb, by group⟩
    · intro a ha
      rfl
  have hsum₂ : rayCnt W S c₂ N = ∑ c' ∈ s₁, rayCnt V S (u * c') N :=
    hsum₂₀.trans hreindex.symm
  rw [hsum₁, hsum₂]
  simp only [Nat.cast_sum]
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ c' ∈ s₁,
      |(rayCnt V S c' N : ℝ) - (rayCnt V S (u * c') N : ℝ)| ≤ C * (N : ℝ) ^ θ :=
    fun c' _ => hC N hN c' (u * c')
  refine le_trans (le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)) ?_
  rw [Finset.sum_const, nsmul_eq_mul, hs₁]
  have hcard : ((Finset.univ.filter
      (fun c' => rayClassMapOfLe V W hVW c' = c₁)).card : ℝ)
      ≤ (Fintype.card (IdeleClassGroup.rayClassGroup K V) : ℝ) := by
    exact_mod_cast Finset.card_le_univ _
  have hnn : 0 ≤ (N : ℝ) ^ θ := Real.rpow_nonneg (Nat.cast_nonneg N) θ
  calc ((Finset.univ.filter (fun c' => rayClassMapOfLe V W hVW c' = c₁)).card : ℝ)
        * (C * (N : ℝ) ^ θ)
      ≤ (Fintype.card (IdeleClassGroup.rayClassGroup K V) : ℝ) * (C * (N : ℝ) ^ θ) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hCpos.le hnn)
    _ = (Fintype.card (IdeleClassGroup.rayClassGroup K V) : ℝ) * C * (N : ℝ) ^ θ := by ring

