import Mathlib
import Submission.Work.WilC5.StepSeqCutBigAux
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.Bridge

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- An `LRc`-embedding commutes with the symbol application. -/
theorem sscb_emb_funMap {M N : Type} [LRc.Structure M] [LRc.Structure N]
    (e : LRc.Embedding M N) {n : ℕ} (f : LRc.Functions n) (xs : Fin n → M) :
    e (@FirstOrder.Language.Structure.funMap LRc M _ n f xs)
      = @FirstOrder.Language.Structure.funMap LRc N _ n f (fun i => e (xs i)) :=
  e.map_fun f xs

/-- The element `1` of a substructure is the ring unit. -/
theorem sscb_sub_one {M : Type} [LEc.Structure M] [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hone : (Work.WilC5.oneE : M) = 1)
    {F : WilkiesDesign.CG.LRc.Substructure M} (h : (1 : M) ∈ (F : Set M)) :
    (⟨(1 : M), h⟩ : ↥F) = (Work.WilC5.oneEL : ↥F) := by
  apply Subtype.ext
  change (1 : M) = ((@FirstOrder.Language.Structure.funMap LRc ↥F _ 0
    (Sum.inl (Sum.inl Ring.oneFunc)) (![] : Fin 0 → ↥F) : ↥F) : M)
  rw [sscb_sub_coe (Sum.inl (Sum.inl Ring.oneFunc)) (![] : Fin 0 → ↥F)]
  rw [show (fun i : Fin 0 => ((![] : Fin 0 → ↥F) i : M)) = (default : Fin 0 → M) from
    Subsingleton.elim _ _]
  rw [← hone]
  rfl

/-- The element `0` of a substructure is the ring zero. -/
theorem sscb_sub_zero {M : Type} [LEc.Structure M] [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hzero : (Work.WilC5.zeroE : M) = 0)
    {F : WilkiesDesign.CG.LRc.Substructure M} (h : (0 : M) ∈ (F : Set M)) :
    (⟨(0 : M), h⟩ : ↥F) = (Work.WilC5.zeroEL : ↥F) := by
  apply Subtype.ext
  change (0 : M) = ((@FirstOrder.Language.Structure.funMap LRc ↥F _ 0
    (Sum.inl (Sum.inl Ring.zeroFunc)) (![] : Fin 0 → ↥F) : ↥F) : M)
  rw [sscb_sub_coe (Sum.inl (Sum.inl Ring.zeroFunc)) (![] : Fin 0 → ↥F)]
  rw [show (fun i : Fin 0 => ((![] : Fin 0 → ↥F) i : M)) = (default : Fin 0 → M) from
    Subsingleton.elim _ _]
  rw [← hzero]
  rfl

/-- A substructure embedding commutes with addition. -/
theorem sscb_emb_add {K L : Type} [LEc.Structure K] [LEc.Structure L] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    {F : WilkiesDesign.CG.LRc.Substructure K}
    (hFa : ∀ a b : K, a ∈ (F : Set K) → b ∈ (F : Set K) → a + b ∈ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding ↥F L) :
    ∀ (a b : K) (ha : a ∈ (F : Set K)) (hb : b ∈ (F : Set K)),
      σ ⟨a + b, hFa a b ha hb⟩ = (σ ⟨a, ha⟩ : L) + (σ ⟨b, hb⟩ : L) := by
  intro a b ha hb
  have h1 : (⟨a + b, hFa a b ha hb⟩ : ↥F)
      = (Work.WilC5.addEL ⟨a, ha⟩ ⟨b, hb⟩ : ↥F) := by
    apply Subtype.ext
    change (a + b : K) = ((Work.WilC5.addEL ⟨a, ha⟩ ⟨b, hb⟩ : ↥F) : K)
    rw [sscb_coe_add (M := K) haddK ⟨a, ha⟩ ⟨b, hb⟩]
  have h2 := sscb_emb_funMap σ (Sum.inl (Sum.inl Ring.addFunc)) ![⟨a, ha⟩, ⟨b, hb⟩]
  have harg : (fun i : Fin 2 => σ (![⟨a, ha⟩, ⟨b, hb⟩] i)) = ![σ ⟨a, ha⟩, σ ⟨b, hb⟩] := by
    funext i; fin_cases i <;> rfl
  rw [h1]
  change σ (@FirstOrder.Language.Structure.funMap LRc ↥F _ 2
    (Sum.inl (Sum.inl Ring.addFunc)) ![⟨a, ha⟩, ⟨b, hb⟩]) = _
  rw [h2, harg]
  exact haddL _ _

/-- A substructure embedding commutes with multiplication. -/
theorem sscb_emb_mul {K L : Type} [LEc.Structure K] [LEc.Structure L] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y)
    {F : WilkiesDesign.CG.LRc.Substructure K}
    (hFm : ∀ a b : K, a ∈ (F : Set K) → b ∈ (F : Set K) → a * b ∈ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding ↥F L) :
    ∀ (a b : K) (ha : a ∈ (F : Set K)) (hb : b ∈ (F : Set K)),
      σ ⟨a * b, hFm a b ha hb⟩ = (σ ⟨a, ha⟩ : L) * (σ ⟨b, hb⟩ : L) := by
  intro a b ha hb
  have h1 : (⟨a * b, hFm a b ha hb⟩ : ↥F)
      = (Work.WilC5.mulEL ⟨a, ha⟩ ⟨b, hb⟩ : ↥F) := by
    apply Subtype.ext
    change (a * b : K) = ((Work.WilC5.mulEL ⟨a, ha⟩ ⟨b, hb⟩ : ↥F) : K)
    rw [sscb_coe_mul (M := K) hmulK ⟨a, ha⟩ ⟨b, hb⟩]
  have h2 := sscb_emb_funMap σ (Sum.inl (Sum.inl Ring.mulFunc)) ![⟨a, ha⟩, ⟨b, hb⟩]
  have harg : (fun i : Fin 2 => σ (![⟨a, ha⟩, ⟨b, hb⟩] i)) = ![σ ⟨a, ha⟩, σ ⟨b, hb⟩] := by
    funext i; fin_cases i <;> rfl
  rw [h1]
  change σ (@FirstOrder.Language.Structure.funMap LRc ↥F _ 2
    (Sum.inl (Sum.inl Ring.mulFunc)) ![⟨a, ha⟩, ⟨b, hb⟩]) = _
  rw [h2, harg]
  exact hmulL _ _

/-- A substructure embedding commutes with negation. -/
theorem sscb_emb_neg {K L : Type} [LEc.Structure K] [LEc.Structure L] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (hnegK : ∀ x : K, Work.WilC5.negE x = -x)
    (hnegL : ∀ x : L, Work.WilC5.negE x = -x)
    {F : WilkiesDesign.CG.LRc.Substructure K}
    (hFn : ∀ a : K, a ∈ (F : Set K) → -a ∈ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding ↥F L) :
    ∀ (a : K) (ha : a ∈ (F : Set K)),
      σ ⟨-a, hFn a ha⟩ = -(σ ⟨a, ha⟩ : L) := by
  intro a ha
  have h1 : (⟨-a, hFn a ha⟩ : ↥F) = (Work.WilC5.negEL ⟨a, ha⟩ : ↥F) := by
    apply Subtype.ext
    change (-a : K) = ((Work.WilC5.negEL ⟨a, ha⟩ : ↥F) : K)
    rw [sscb_coe_neg (M := K) hnegK ⟨a, ha⟩]
  have h2 := sscb_emb_funMap σ (Sum.inl (Sum.inl Ring.negFunc)) ![⟨a, ha⟩]
  have harg : (fun i : Fin 1 => σ (![⟨a, ha⟩] i)) = ![σ ⟨a, ha⟩] := by
    funext i; fin_cases i <;> rfl
  rw [h1]
  change σ (@FirstOrder.Language.Structure.funMap LRc ↥F _ 1
    (Sum.inl (Sum.inl Ring.negFunc)) ![⟨a, ha⟩]) = _
  rw [h2, harg]
  exact hnegL _

/-- A substructure embedding sends `1` to `1`. -/
theorem sscb_emb_one {K L : Type} [LEc.Structure K] [LEc.Structure L] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (honeK : (Work.WilC5.oneE : K) = 1) (honeL : (Work.WilC5.oneE : L) = 1)
    {F : WilkiesDesign.CG.LRc.Substructure K} (h1 : (1 : K) ∈ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding ↥F L) :
    σ ⟨(1 : K), h1⟩ = (1 : L) := by
  rw [sscb_sub_one honeK h1]
  change σ (@FirstOrder.Language.Structure.funMap LRc ↥F _ 0
    (Sum.inl (Sum.inl Ring.oneFunc)) (![] : Fin 0 → ↥F)) = (1 : L)
  rw [sscb_emb_funMap σ (Sum.inl (Sum.inl Ring.oneFunc)) (![] : Fin 0 → ↥F)]
  rw [show (fun i : Fin 0 => σ ((![] : Fin 0 → ↥F) i)) = (default : Fin 0 → L) from
    Subsingleton.elim _ _]
  rw [← honeL]
  rfl

/-- A substructure embedding sends `0` to `0`. -/
theorem sscb_emb_zero {K L : Type} [LEc.Structure K] [LEc.Structure L] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (hzeroK : (Work.WilC5.zeroE : K) = 0) (hzeroL : (Work.WilC5.zeroE : L) = 0)
    {F : WilkiesDesign.CG.LRc.Substructure K} (h0 : (0 : K) ∈ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding ↥F L) :
    σ ⟨(0 : K), h0⟩ = (0 : L) := by
  rw [sscb_sub_zero hzeroK h0]
  change σ (@FirstOrder.Language.Structure.funMap LRc ↥F _ 0
    (Sum.inl (Sum.inl Ring.zeroFunc)) (![] : Fin 0 → ↥F)) = (0 : L)
  rw [sscb_emb_funMap σ (Sum.inl (Sum.inl Ring.zeroFunc)) (![] : Fin 0 → ↥F)]
  rw [show (fun i : Fin 0 => σ ((![] : Fin 0 → ↥F) i)) = (default : Fin 0 → L) from
    Subsingleton.elim _ _]
  rw [← hzeroL]
  rfl

/-- A substructure embedding commutes with natural powers. -/
theorem sscb_emb_pow_nat {K L : Type} [LEc.Structure K] [LEc.Structure L] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (honeK : (Work.WilC5.oneE : K) = 1)
    (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y)
    (honeL : (Work.WilC5.oneE : L) = 1)
    {F : WilkiesDesign.CG.LRc.Substructure K}
    (hF1 : (1 : K) ∈ (F : Set K))
    (hFm : ∀ a b : K, a ∈ (F : Set K) → b ∈ (F : Set K) → a * b ∈ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding ↥F L)
    (a : K) (ha : a ∈ (F : Set K)) (hmem : ∀ n : ℕ, a ^ n ∈ (F : Set K)) (n : ℕ) :
    σ ⟨a ^ n, hmem n⟩ = (σ ⟨a, ha⟩ : L) ^ n := by
  induction n with
  | zero =>
      have heq : (⟨a ^ 0, hmem 0⟩ : ↥F) = ⟨(1 : K), hF1⟩ := by
        apply Subtype.ext
        show a ^ 0 = (1 : K)
        rw [pow_zero]
      rw [congrArg σ heq, sscb_emb_one honeK honeL hF1 σ, pow_zero]
  | succ n ih =>
      have heq : (⟨a ^ (n + 1), hmem (n + 1)⟩ : ↥F)
          = ⟨a ^ n * a, hFm _ _ (hmem n) ha⟩ := by
        apply Subtype.ext
        show a ^ (n + 1) = a ^ n * a
        rw [pow_succ]
      rw [congrArg σ heq, sscb_emb_mul hmulK hmulL hFm σ _ _ (hmem n) ha, ih, pow_succ]

/-- A substructure embedding commutes with integer powers of nonzero elements. -/
theorem sscb_emb_zpow {K L : Type} [LEc.Structure K] [LEc.Structure L] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (honeK : (Work.WilC5.oneE : K) = 1)
    (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y)
    (honeL : (Work.WilC5.oneE : L) = 1)
    {F : WilkiesDesign.CG.LRc.Substructure K}
    (hF1 : (1 : K) ∈ (F : Set K))
    (hFm : ∀ a b : K, a ∈ (F : Set K) → b ∈ (F : Set K) → a * b ∈ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding ↥F L)
    (a : K) (ha : a ∈ (F : Set K)) (ha0 : a ≠ 0)
    (hmemN : ∀ n : ℕ, a ^ n ∈ (F : Set K)) (hmemZ : ∀ z : ℤ, a ^ z ∈ (F : Set K))
    (z : ℤ) :
    σ ⟨a ^ z, hmemZ z⟩ = (σ ⟨a, ha⟩ : L) ^ z := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · have heq : (⟨a ^ (↑n : ℤ), hmemZ (↑n)⟩ : ↥F) = ⟨a ^ n, hmemN n⟩ := by
      apply Subtype.ext
      show a ^ (↑n : ℤ) = a ^ n
      rw [zpow_natCast]
    rw [congrArg σ heq, sscb_emb_pow_nat honeK hmulK hmulL honeL hF1 hFm σ a ha hmemN n,
      zpow_natCast]
  · have hmem_inv : (a ^ n)⁻¹ ∈ (F : Set K) := by
      have h := hmemZ (-(n : ℤ))
      rwa [zpow_neg, zpow_natCast] at h
    have heq : (⟨a ^ (-(n : ℤ)), hmemZ (-(n : ℤ))⟩ : ↥F) = ⟨(a ^ n)⁻¹, hmem_inv⟩ := by
      apply Subtype.ext
      show a ^ (-(n : ℤ)) = (a ^ n)⁻¹
      rw [zpow_neg, zpow_natCast]
    rw [congrArg σ heq, zpow_neg, zpow_natCast]
    have huv : (⟨(a ^ n)⁻¹ * a ^ n, hFm _ _ hmem_inv (hmemN n)⟩ : ↥F)
        = ⟨(1 : K), hF1⟩ := by
      apply Subtype.ext
      show (a ^ n)⁻¹ * a ^ n = (1 : K)
      rw [inv_mul_cancel₀ (pow_ne_zero n ha0)]
    have hone : σ ⟨(a ^ n)⁻¹ * a ^ n, hFm _ _ hmem_inv (hmemN n)⟩ = (1 : L) := by
      rw [congrArg σ huv, sscb_emb_one honeK honeL hF1 σ]
    have hmulstep := sscb_emb_mul hmulK hmulL hFm σ (a ^ n)⁻¹ (a ^ n) hmem_inv (hmemN n)
    have hmulone : ((σ ⟨(a ^ n)⁻¹, hmem_inv⟩ : L)) * ((σ ⟨a ^ n, hmemN n⟩ : L)) = 1 := by
      rw [← hmulstep]; exact hone
    have hfinal : (σ ⟨(a ^ n)⁻¹, hmem_inv⟩ : L) = ((σ ⟨a, ha⟩ : L) ^ n)⁻¹ := by
      rw [eq_inv_of_mul_eq_one_left hmulone,
        sscb_emb_pow_nat honeK hmulK hmulL honeL hF1 hFm σ a ha hmemN n]
    rw [hfinal]

/-- A substructure embedding sends the numerals to the numerals. -/
theorem sscb_emb_natCast {K L : Type} [LEc.Structure K] [LEc.Structure L] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    (hzeroK : (Work.WilC5.zeroE : K) = 0) (hzeroL : (Work.WilC5.zeroE : L) = 0)
    (honeK : (Work.WilC5.oneE : K) = 1) (honeL : (Work.WilC5.oneE : L) = 1)
    {F : WilkiesDesign.CG.LRc.Substructure K}
    (hF0 : (0 : K) ∈ (F : Set K)) (hF1 : (1 : K) ∈ (F : Set K))
    (hFa : ∀ a b : K, a ∈ (F : Set K) → b ∈ (F : Set K) → a + b ∈ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding ↥F L)
    (hmem : ∀ n : ℕ, (n : K) ∈ (F : Set K)) (n : ℕ) :
    σ ⟨(n : K), hmem n⟩ = (n : L) := by
  induction n with
  | zero =>
      have heq : (⟨((0 : ℕ) : K), hmem 0⟩ : ↥F) = ⟨(0 : K), hF0⟩ := by
        apply Subtype.ext
        show (((0 : ℕ) : K)) = (0 : K)
        rw [Nat.cast_zero]
      rw [congrArg σ heq, sscb_emb_zero hzeroK hzeroL hF0 σ, Nat.cast_zero]
  | succ n ih =>
      have heq : (⟨(((n + 1 : ℕ)) : K), hmem (n + 1)⟩ : ↥F) = ⟨(n : K) + 1, hFa _ _ (hmem n) hF1⟩ := by
        apply Subtype.ext
        show (((n + 1 : ℕ)) : K) = (n : K) + 1
        push_cast; ring
      rw [congrArg σ heq, sscb_emb_add haddK haddL hFa σ _ _ (hmem n) hF1, ih,
        sscb_emb_one honeK honeL hF1 σ]
      push_cast; ring

-- TEMPORARILY DISABLED (under development)

/-- A substructure embedding commutes with finite products of integer powers. -/
theorem sscb_emb_prod_zpow {K L : Type} [LEc.Structure K] [LEc.Structure L] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (honeK : (Work.WilC5.oneE : K) = 1)
    (hmulK : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hmulL : ∀ x y : L, Work.WilC5.mulE x y = x * y)
    (honeL : (Work.WilC5.oneE : L) = 1)
    {F : WilkiesDesign.CG.LRc.Substructure K}
    (hF1 : (1 : K) ∈ (F : Set K))
    (hFm : ∀ a b : K, a ∈ (F : Set K) → b ∈ (F : Set K) → a * b ∈ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding ↥F L)
    {ι : Type*} (f : ι → K) (hf : ∀ i, f i ∈ (F : Set K)) (hf0 : ∀ i, f i ≠ 0)
    (hmemN : ∀ i, ∀ n : ℕ, f i ^ n ∈ (F : Set K))
    (hmemZ : ∀ i, ∀ z : ℤ, f i ^ z ∈ (F : Set K))
    (g : ι → ℤ) :
    ∀ (s : Finset ι), ∀ (hprod : (∏ i ∈ s, f i ^ (g i)) ∈ (F : Set K)),
      σ ⟨∏ i ∈ s, f i ^ (g i), hprod⟩ = ∏ i ∈ s, (σ ⟨f i, hf i⟩ : L) ^ (g i) := by
  classical
  intro s
  induction s using Finset.induction with
  | empty =>
      intro hprod
      have heq : (⟨∏ i ∈ (∅ : Finset ι), f i ^ (g i), hprod⟩ : ↥F) = ⟨(1 : K), hF1⟩ := by
        apply Subtype.ext
        show (∏ i ∈ (∅ : Finset ι), f i ^ (g i)) = (1 : K)
        simp
      rw [congrArg σ heq, sscb_emb_one honeK honeL hF1 σ]
      simp
  | insert a s ha ih =>
      intro hprod
      have hP : (∏ i ∈ s, f i ^ (g i)) ∈ (F : Set K) := by
        refine Finset.prod_induction _ _ (fun x y hx hy => hFm x y hx hy) hF1 ?_
        intro i hi
        exact hmemZ i (g i)
      have hstep : (∏ i ∈ insert a s, f i ^ (g i)) = f a ^ (g a) * (∏ i ∈ s, f i ^ (g i)) :=
        Finset.prod_insert ha
      have heq : (⟨∏ i ∈ insert a s, f i ^ (g i), hprod⟩ : ↥F)
          = ⟨f a ^ (g a) * (∏ i ∈ s, f i ^ (g i)), hFm _ _ (hmemZ a (g a)) hP⟩ := by
        apply Subtype.ext
        show (∏ i ∈ insert a s, f i ^ (g i)) = f a ^ (g a) * (∏ i ∈ s, f i ^ (g i))
        rw [hstep]
      rw [congrArg σ heq,
        sscb_emb_mul hmulK hmulL hFm σ _ _ (hmemZ a (g a)) hP,
        sscb_emb_zpow honeK hmulK hmulL honeL hF1 hFm σ (f a) (hf a) (hf0 a)
          (hmemN a) (hmemZ a) (g a),
        ih hP, Finset.prod_insert ha]

/-- A substructure embedding sends integer numerals to integer numerals. -/
theorem sscb_emb_intCast {K L : Type} [LEc.Structure K] [LEc.Structure L] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    (haddK : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (haddL : ∀ x y : L, Work.WilC5.addE x y = x + y)
    (hzeroK : (Work.WilC5.zeroE : K) = 0) (hzeroL : (Work.WilC5.zeroE : L) = 0)
    (honeK : (Work.WilC5.oneE : K) = 1) (honeL : (Work.WilC5.oneE : L) = 1)
    (hnegK : ∀ x : K, Work.WilC5.negE x = -x) (hnegL : ∀ x : L, Work.WilC5.negE x = -x)
    {F : WilkiesDesign.CG.LRc.Substructure K}
    (hF0 : (0 : K) ∈ (F : Set K)) (hF1 : (1 : K) ∈ (F : Set K))
    (hFneg : ∀ x ∈ (F : Set K), -x ∈ (F : Set K))
    (hFa : ∀ x ∈ (F : Set K), ∀ y ∈ (F : Set K), x + y ∈ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding ↥F L)
    (hmem : ∀ k : ℤ, (k : K) ∈ (F : Set K)) :
    ∀ k : ℤ, σ ⟨(k : K), hmem k⟩ = (k : L) := by
  intro k
  have hmemN : ∀ m : ℕ, (m : K) ∈ (F : Set K) := fun m => by simpa using hmem (m : ℤ)
  have hnat : ∀ m : ℕ, σ ⟨(m : K), hmemN m⟩ = (m : L) := fun m =>
    sscb_emb_natCast haddK haddL hzeroK hzeroL honeK honeL hF0 hF1
      (fun a b ha hb => hFa a ha b hb) σ hmemN m
  rcases Int.eq_nat_or_neg k with ⟨n, hn | hn⟩
  · rw [hn]
    simpa using hnat n
  · rw [hn]
    have h2 : (⟨(((-(n : ℤ)) : ℤ) : K), hmem (-(n : ℤ))⟩ : ↥F)
        = ⟨-((n : K)), hFneg _ (hmemN n)⟩ := by
      apply Subtype.ext
      show (((-(n : ℤ)) : ℤ) : K) = -((n : K))
      push_cast; ring
    rw [h2, sscb_emb_neg hnegK hnegL hFneg σ ((n : K)) (hmemN n), hnat n]
    push_cast; ring

end Work.WilC5
