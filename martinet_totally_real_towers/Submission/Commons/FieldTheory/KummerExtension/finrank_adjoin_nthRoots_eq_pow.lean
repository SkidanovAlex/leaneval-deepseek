import Mathlib.FieldTheory.KummerExtension
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.FieldTheory.KummerExtension.rootsOfUnity_mem_map_of_isPrimitiveRoot

namespace Commons.FieldTheory.KummerExtension

open Polynomial IntermediateField

open scoped IsMulCommutative

set_option linter.style.haveILetI false

noncomputable section

variable {k M : Type*} [Field k] [Field M] [Algebra k M]

/-- Two `k`-algebra homs agreeing on `Set.range β` agree, provided
`Algebra.adjoin k (Set.range β) = ⊤`. -/
private lemma algHom_ext_of_adjoin_eq_top {ι : Type*} (β : ι → M)
    (hgenA : Algebra.adjoin k (Set.range β) = ⊤)
    {f g : M →ₐ[k] M} (h : ∀ i, f (β i) = g (β i)) : f = g :=
  AlgHom.ext_of_adjoin_eq_top hgenA (by rintro _ ⟨i, rfl⟩; exact h i)

/-- Two `k`-algebra equivs agreeing on `Set.range β` agree. -/
private lemma algEquiv_ext_of_adjoin_eq_top {ι : Type*} (β : ι → M)
    (hgenA : Algebra.adjoin k (Set.range β) = ⊤)
    {f g : M ≃ₐ[k] M} (h : ∀ i, f (β i) = g (β i)) : f = g := by
  apply AlgEquiv.ext
  intro x
  exact congrArg (fun φ : M →ₐ[k] M => φ x)
    (algHom_ext_of_adjoin_eq_top β hgenA (f := (f : M →ₐ[k] M)) (g := (g : M →ₐ[k] M)) h)

end

theorem finrank_adjoin_nthRoots_eq_pow
    {k M : Type*} [Field k] [Field M] [Algebra k M] [FiniteDimensional k M]
    (n : ℕ) [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n)
    {ι : Type*} [Fintype ι] (β : ι → M) {b : ι → k}
    (hb : ∀ i, b i ≠ 0) (hβ : ∀ i, (β i) ^ n = algebraMap k M (b i))
    (hind : ∀ j : ι → ℕ, (∃ c : k, ∏ i, b i ^ (j i) = c ^ n) → ∀ i, n ∣ j i)
    (hgen : IntermediateField.adjoin k (Set.range β) = ⊤) :
    Module.finrank k M = n ^ Fintype.card ι := by
  classical
  have hn : n ≠ 0 := NeZero.ne n
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hnk : (n : k) ≠ 0 := (hζ.neZero').ne
  haveI hAlg : Algebra.IsAlgebraic k M := Algebra.IsAlgebraic.of_finite k M
  have hbM : ∀ i, algebraMap k M (b i) ≠ 0 := fun i h =>
    hb i ((algebraMap k M).injective (by rw [h, map_zero]))
  have hβne : ∀ i, β i ≠ 0 := fun i h => hbM i (by rw [← hβ i, h]; exact zero_pow hn)
  have hgenA : Algebra.adjoin k (Set.range β) = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff).mp hgen
  -- ### Separability
  have hsep : Algebra.IsSeparable k M := by
    have h1 : Algebra.IsSeparable k ↥(IntermediateField.adjoin k (Set.range β)) := by
      rw [IntermediateField.isSeparable_adjoin_iff_isSeparable]
      rintro x ⟨i, rfl⟩
      exact (Polynomial.separable_X_pow_sub_C (b i) hnk (hb i)).of_dvd
        (minpoly.dvd k (β i) (by simp [hβ i]))
    rw [hgen] at h1
    exact (IntermediateField.isSeparable_top k M).mp h1
  -- ### Normality
  have hnormal : Normal k M := by
    rw [normal_iff]
    intro x
    refine ⟨IsIntegral.of_finite k x, ?_⟩
    have hxmem : x ∈ IntermediateField.adjoin k (Set.range β) := by rw [hgen]; trivial
    refine IntermediateField.splits_of_mem_adjoin k M (S := Set.range β) (fun y hy => ?_) hxmem
    obtain ⟨i, rfl⟩ := hy
    refine ⟨?_, ?_⟩
    · refine ⟨X ^ n - C (b i), Polynomial.monic_X_pow_sub_C (b i) hn, ?_⟩
      simp [hβ i]
    · have hsplit : (Polynomial.X ^ n - Polynomial.C (algebraMap k M (b i)) : M[X]).Splits :=
        X_pow_sub_C_splits_of_isPrimitiveRoot
          (hζ.map_of_injective (algebraMap k M).injective) (hβ i)
      have hmap : (Polynomial.X ^ n - Polynomial.C (b i) : k[X]).map (algebraMap k M) =
          Polynomial.X ^ n - Polynomial.C (algebraMap k M (b i)) := by simp
      refine Splits.of_dvd hsplit (Polynomial.X_pow_sub_C_ne_zero hnpos _) ?_
      rw [← hmap]
      exact Polynomial.map_dvd _ (minpoly.dvd k (β i) (by simp [hβ i]))
  -- ### Galois
  haveI : IsGalois k M := isGalois_iff.mpr ⟨hsep, hnormal⟩
  have hcard : Nat.card (M ≃ₐ[k] M) = Module.finrank k M := IsGalois.card_aut_eq_finrank k M
  -- ### The Kummer "ratio" units
  let U : (M ≃ₐ[k] M) → ι → Mˣ := fun σ i =>
    Units.mk0 (σ (β i) / β i)
      (div_ne_zero (fun h => hβne i (σ.injective (by rw [h, map_zero]))) (hβne i))
  have Uval : ∀ σ i, (U σ i : M) = σ (β i) / β i := fun σ i => Units.val_mk0 _
  have Un : ∀ σ i, (U σ i) ^ n = 1 := by
    intro σ i
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Uval]
    rw [div_pow, ← map_pow, hβ i, AlgEquiv.commutes, div_self (hbM i)]
  have UnM : ∀ σ i, (U σ i : M) ^ n = 1 := fun σ i => by
    have h := congrArg (fun u : Mˣ => (u : M)) (Un σ i)
    simpa using h
  have Umem : ∀ σ i, U σ i ∈ rootsOfUnity n M :=
    fun σ i => (mem_rootsOfUnity n (U σ i)).mpr (Un σ i)
  have Ufix : ∀ (σ' σ : M ≃ₐ[k] M) i, σ' (U σ i : M) = (U σ i : M) := by
    intro σ' σ i
    obtain ⟨η₀, hη₀⟩ :=
      rootsOfUnity_mem_map_of_isPrimitiveRoot (k := k) (M := M) n hζ (U σ i) (Umem σ i)
    have hcoe : (U σ i : M) = algebraMap k M ((η₀ : kˣ) : k) := by
      rw [← hη₀]; simp
    rw [hcoe, AlgEquiv.commutes]
  have Uone : ∀ i, U 1 i = 1 := by
    intro i
    apply Units.ext
    rw [Uval, AlgEquiv.one_apply, Units.val_one, div_self (hβne i)]
  have Uβmul : ∀ (σ : M ≃ₐ[k] M) i, (U σ i : M) * β i = σ (β i) := by
    intro σ i
    rw [Uval, div_mul_cancel₀ _ (hβne i)]
  have Umul : ∀ (σ τ : M ≃ₐ[k] M) i, U (σ * τ) i = U σ i * U τ i := by
    intro σ τ i
    apply Units.ext
    have hL : (U (σ * τ) i : M) = (U τ i : M) * (U σ i : M) := by
      calc (U (σ * τ) i : M) = (σ * τ) (β i) / β i := Uval _ _
        _ = σ (τ (β i)) / β i := by rw [AlgEquiv.mul_apply]
        _ = σ ((U τ i : M) * β i) / β i := by rw [← Uβmul τ i]
        _ = (σ (U τ i : M) * σ (β i)) / β i := by rw [map_mul]
        _ = ((U τ i : M) * σ (β i)) / β i := by rw [Ufix σ τ i]
        _ = (U τ i : M) * (σ (β i) / β i) := by rw [mul_div_assoc]
        _ = (U τ i : M) * (U σ i : M) := by rw [Uval σ i]
    have hR : ((U σ i * U τ i : Mˣ) : M) = (U τ i : M) * (U σ i : M) := by
      rw [Units.val_mul, mul_comm]
    rw [hL, hR]
  -- ### The pairing `P σ a = ∏ᵢ (σ(βᵢ)/βᵢ) ^ (aᵢ).val`
  let P : (M ≃ₐ[k] M) → (ι → Multiplicative (ZMod n)) → Mˣ :=
    fun σ a => ∏ i, (U σ i) ^ ((a i).toAdd).val
  have Pone : ∀ a, P 1 a = 1 := by
    intro a
    simp only [P]
    exact Finset.prod_eq_one (fun i _ => by rw [Uone i, one_pow])
  have Pmul : ∀ (σ τ : M ≃ₐ[k] M) a, P (σ * τ) a = P σ a * P τ a := by
    intro σ τ a
    simp only [P]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => by rw [Umul σ τ i, mul_pow])
  have Paone : ∀ σ, P σ 1 = 1 := by
    intro σ
    simp only [P]
    refine Finset.prod_eq_one (fun i _ => ?_)
    simp
  have Pamul : ∀ σ (a a' : ι → Multiplicative (ZMod n)), P σ (a * a') = P σ a * P σ a' := by
    intro σ a a'
    simp only [P]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have h1 : ((a * a') i).toAdd = (a i).toAdd + (a' i).toAdd := by simp
    rw [h1, ZMod.val_add, ← pow_add,
      ← pow_eq_pow_mod ((a i).toAdd.val + (a' i).toAdd.val) (Un σ i)]
  let Ψ : (ι → Multiplicative (ZMod n)) →* ((M ≃ₐ[k] M) →* Mˣ) :=
    { toFun := fun a =>
        { toFun := fun σ => P σ a
          map_one' := Pone a
          map_mul' := fun σ τ => Pmul σ τ a }
      map_one' := MonoidHom.ext (fun σ => Paone σ)
      map_mul' := fun a a' => MonoidHom.ext (fun σ => Pamul σ a a') }
  -- ### roots of unity transfer to `M`
  haveI hERU : HasEnoughRootsOfUnity M n :=
    ⟨⟨algebraMap k M ζ, hζ.map_of_injective (algebraMap k M).injective⟩, rootsOfUnity.isCyclic M n⟩
  have hexpA : Monoid.exponent (ι → Multiplicative (ZMod n)) ∣ n := by
    rw [Monoid.exponent_dvd]
    intro a
    rw [orderOf_dvd_iff_pow_eq_one]
    funext i
    change (a i) ^ n = 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow]
    simp [nsmul_eq_mul]
  have hσpow : ∀ σ : M ≃ₐ[k] M, σ ^ n = 1 := by
    intro σ
    apply algEquiv_ext_of_adjoin_eq_top β hgenA
    intro i
    have hk : ∀ m : ℕ, (σ ^ m) (β i) = (U σ i : M) ^ m * β i := by
      intro m
      induction m with
      | zero => simp only [pow_zero, AlgEquiv.one_apply, one_mul]
      | succ m ih =>
        rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, Ufix σ σ i, ← Uβmul σ i,
          pow_succ]
        ring
    rw [hk n, UnM σ i, one_mul, AlgEquiv.one_apply]
  have hexpG : Monoid.exponent (M ≃ₐ[k] M) ∣ n := by
    rw [Monoid.exponent_dvd]
    intro σ
    exact (orderOf_dvd_iff_pow_eq_one).mpr (hσpow σ)
  have hcomm : ∀ σ τ : M ≃ₐ[k] M, σ * τ = τ * σ := by
    intro σ τ
    apply algEquiv_ext_of_adjoin_eq_top β hgenA
    intro i
    have h1 : (σ * τ) (β i) = (U τ i : M) * (U σ i : M) * β i := by
      rw [AlgEquiv.mul_apply, ← Uβmul τ i, map_mul, Ufix σ τ i, ← Uβmul σ i, mul_assoc]
    have h2 : (τ * σ) (β i) = (U σ i : M) * (U τ i : M) * β i := by
      rw [AlgEquiv.mul_apply, ← Uβmul σ i, map_mul, Ufix τ σ i, ← Uβmul τ i, mul_assoc]
    rw [h1, h2, mul_comm (U τ i : M) (U σ i : M)]
  haveI : IsMulCommutative (M ≃ₐ[k] M) := ⟨⟨hcomm⟩⟩
  haveI hERUG : HasEnoughRootsOfUnity M (Monoid.exponent (M ≃ₐ[k] M)) :=
    HasEnoughRootsOfUnity.of_dvd M hexpG
  haveI hERUA : HasEnoughRootsOfUnity M (Monoid.exponent (ι → Multiplicative (ZMod n))) :=
    HasEnoughRootsOfUnity.of_dvd M hexpA
  have hcardHomG : Nat.card ((M ≃ₐ[k] M) →* Mˣ) = Nat.card (M ≃ₐ[k] M) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (M ≃ₐ[k] M) M
  have hcardHomA : Nat.card ((ι → Multiplicative (ZMod n)) →* Mˣ)
      = Nat.card (ι → Multiplicative (ZMod n)) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (ι → Multiplicative (ZMod n)) M
  -- ### Injectivity of `Ψ` (the lower bound `n ^ #ι ≤ |G|`)
  have hker : ∀ a : ι → Multiplicative (ZMod n), Ψ a = 1 → a = 1 := by
    intro a ha
    have hP : ∀ σ, P σ a = 1 := by
      intro σ
      have h := congrArg (fun f : (M ≃ₐ[k] M) →* Mˣ => f σ) ha
      simpa [Ψ] using h
    set ba : M := ∏ i, β i ^ ((a i).toAdd).val with hbadef
    have hfix : ∀ σ : M ≃ₐ[k] M, σ ba = ba := by
      intro σ
      have key : σ ba = (∏ i, (U σ i : M) ^ ((a i).toAdd).val) * ba := by
        rw [hbadef, map_prod]
        calc ∏ x, σ (β x ^ ((a x).toAdd).val)
            = ∏ x, (σ (β x)) ^ ((a x).toAdd).val :=
              Finset.prod_congr rfl (fun x _ => by rw [map_pow])
          _ = ∏ x, ((U σ x : M) * β x) ^ ((a x).toAdd).val :=
              Finset.prod_congr rfl (fun x _ => by rw [← Uβmul σ x])
          _ = ∏ x, ((U σ x : M) ^ ((a x).toAdd).val * β x ^ ((a x).toAdd).val) :=
              Finset.prod_congr rfl (fun x _ => by rw [mul_pow])
          _ = (∏ x, (U σ x : M) ^ ((a x).toAdd).val) * (∏ x, β x ^ ((a x).toAdd).val) :=
              Finset.prod_mul_distrib
          _ = (∏ x, (U σ x : M) ^ ((a x).toAdd).val) * ba := by rw [hbadef]
      rw [key]
      have hone : (∏ i, (U σ i : M) ^ ((a i).toAdd).val) = 1 := by
        have h' := hP σ
        have := congrArg (fun u : Mˣ => (u : M)) h'
        simpa [P] using this
      rw [hone, one_mul]
    have hmem : ba ∈ (⊥ : IntermediateField k M) :=
      (IsGalois.mem_bot_iff_fixed ba).mpr hfix
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
    have hcan : (∏ i, b i ^ ((a i).toAdd).val) = c ^ n := by
      apply (algebraMap k M).injective
      calc algebraMap k M (∏ i, b i ^ ((a i).toAdd).val)
          = ∏ i, algebraMap k M (b i ^ ((a i).toAdd).val) := map_prod _ _ _
        _ = ∏ i, (β i ^ ((a i).toAdd).val) ^ n := by
            refine Finset.prod_congr rfl (fun i _ => ?_)
            rw [map_pow, ← hβ i, ← pow_mul, ← pow_mul, Nat.mul_comm n]
        _ = (∏ i, β i ^ ((a i).toAdd).val) ^ n := Finset.prod_pow _ _ _
        _ = ba ^ n := by rw [hbadef]
        _ = (algebraMap k M c) ^ n := by rw [hc]
        _ = algebraMap k M (c ^ n) := by rw [map_pow]
    have hval0 : ∀ i, (a i).toAdd.val = 0 := fun i =>
      Nat.eq_zero_of_dvd_of_lt (hind _ ⟨c, hcan⟩ i) (ZMod.val_lt _)
    funext i
    apply Multiplicative.toAdd.injective
    simpa using hval0 i
  have hinjΨ : Function.Injective Ψ := by
    intro a a' h
    have h2 : a * a'⁻¹ = 1 := hker (a * a'⁻¹) (by rw [map_mul, h, map_inv, mul_inv_cancel])
    exact mul_inv_eq_one.mp h2
  have hA : Nat.card (ι → Multiplicative (ZMod n)) = n ^ Fintype.card ι := by
    rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_eq_fintype_card]
  have hlower : n ^ Fintype.card ι ≤ Nat.card (M ≃ₐ[k] M) := by
    have h1 : Nat.card (ι → Multiplicative (ZMod n))
        ≤ Nat.card ((M ≃ₐ[k] M) →* Mˣ) := Nat.card_le_card_of_injective Ψ hinjΨ
    rw [hA, hcardHomG] at h1
    exact h1
  -- ### Injectivity of `Ω` (the upper bound `|G| ≤ n ^ #ι`)
  have hupper : Nat.card (M ≃ₐ[k] M) ≤ n ^ Fintype.card ι := by
    let Om : (M ≃ₐ[k] M) → (ι → rootsOfUnity n M) := fun σ i => ⟨U σ i, Umem σ i⟩
    have hinjOm : Function.Injective Om := by
      intro σ τ h
      apply algEquiv_ext_of_adjoin_eq_top β hgenA
      intro i
      have h1 : (U σ i : M) = (U τ i : M) := by
        have h2 := congrFun h i
        have h3 := congrArg (fun u : rootsOfUnity n M => ((u : Mˣ) : M)) h2
        simpa [Om] using h3
      rw [← Uβmul σ i, ← Uβmul τ i, h1]
    calc Nat.card (M ≃ₐ[k] M) ≤ Nat.card (ι → rootsOfUnity n M) :=
          Nat.card_le_card_of_injective Om hinjOm
      _ = n ^ Fintype.card ι := by
          rw [Nat.card_fun, HasEnoughRootsOfUnity.natCard_rootsOfUnity M n, Nat.card_eq_fintype_card]
  rw [← hcard]
  exact le_antisymm hupper hlower

end Commons.FieldTheory.KummerExtension