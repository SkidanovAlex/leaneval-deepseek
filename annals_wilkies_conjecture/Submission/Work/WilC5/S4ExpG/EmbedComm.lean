import Submission.Work.WilC5.S4ExpG.LrcBridge
import Mathlib
import Submission.Work.WilC5.S4OnePoint
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.logFun_one_add_rexp
import Submission.Work.WilC5.logFun_eq_of_rexp_eq
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.expE_add_of_model
import Submission.Work.WilC5.decomposition_of_same_value
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.S4ExpF.logclosure_exp
import Submission.Work.WilC5.S4ExpF.logFun_zpow
import Submission.Work.WilC5.S4ExpF.logFun_eq_zero_of_not_pos
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.tr_leE_axioms
import Submission.Work.WilC2.Dcl

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilC5.S4ExpG

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 4. `LRc`-embeddings of `rexp`-reducts commute with the field operations -/

section EmbedComm

variable {K L : Type}
  [LEc.Structure K] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [FirstOrder.Ring.CompatibleRing K] [WilkiesDesign.CG.rexpL.Structure K]
  [(FirstOrder.Language.constantsOn ℝ).Structure K]
  [LEc.Structure L] [Field L] [LinearOrder L] [IsStrictOrderedRing L]
  [FirstOrder.Ring.CompatibleRing L] [WilkiesDesign.CG.rexpL.Structure L]
  [(FirstOrder.Language.constantsOn ℝ).Structure L]

variable {T : WilkiesDesign.CG.LRc.Substructure K}
variable {f : WilkiesDesign.CG.LRc.Embedding ↥T L}

theorem lpEmbed_funMap_add (T : WilkiesDesign.CG.LRc.Substructure K)
    (f : WilkiesDesign.CG.LRc.Embedding ↥T L) (x y : ↥T) :
    f (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 2
        (Sum.inl (Sum.inl Ring.addFunc)) ![x, y]) = f x + f y := by
  rw [@FirstOrder.Language.Embedding.map_fun WilkiesDesign.CG.LRc ↥T L _ _ f 2
    (Sum.inl (Sum.inl Ring.addFunc)) (![x, y])]
  have h2 : (⇑f ∘ ![x, y] : Fin 2 → L) = ![f x, f y] := by
    funext i; fin_cases i <;> rfl
  rw [h2, lpLrcFunMap_add]

theorem lpEmbed_funMap_mul (T : WilkiesDesign.CG.LRc.Substructure K)
    (f : WilkiesDesign.CG.LRc.Embedding ↥T L) (x y : ↥T) :
    f (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 2
        (Sum.inl (Sum.inl Ring.mulFunc)) ![x, y]) = f x * f y := by
  rw [@FirstOrder.Language.Embedding.map_fun WilkiesDesign.CG.LRc ↥T L _ _ f 2
    (Sum.inl (Sum.inl Ring.mulFunc)) (![x, y])]
  have h2 : (⇑f ∘ ![x, y] : Fin 2 → L) = ![f x, f y] := by
    funext i; fin_cases i <;> rfl
  rw [h2, lpLrcFunMap_mul]

theorem lpEmbed_funMap_neg (T : WilkiesDesign.CG.LRc.Substructure K)
    (f : WilkiesDesign.CG.LRc.Embedding ↥T L) (x : ↥T) :
    f (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 1
        (Sum.inl (Sum.inl Ring.negFunc)) ![x]) = -f x := by
  rw [@FirstOrder.Language.Embedding.map_fun WilkiesDesign.CG.LRc ↥T L _ _ f 1
    (Sum.inl (Sum.inl Ring.negFunc)) (![x])]
  have h2 : (⇑f ∘ ![x] : Fin 1 → L) = ![f x] := by
    funext i; fin_cases i <;> rfl
  rw [h2, lpLrcFunMap_neg]

theorem lpEmbed_funMap_one (T : WilkiesDesign.CG.LRc.Substructure K)
    (f : WilkiesDesign.CG.LRc.Embedding ↥T L) :
    f (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 0
        (Sum.inl (Sum.inl Ring.oneFunc)) (![] : Fin 0 → ↥T)) = (1 : L) := by
  rw [@FirstOrder.Language.Embedding.map_fun WilkiesDesign.CG.LRc ↥T L _ _ f 0
    (Sum.inl (Sum.inl Ring.oneFunc)) (![] : Fin 0 → ↥T)]
  have h2 : (⇑f ∘ (![] : Fin 0 → ↥T) : Fin 0 → L) = (![] : Fin 0 → L) := by
    funext i; exact Fin.elim0 i
  rw [h2, lpLrcFunMap_one]

theorem lpEmbed_funMap_zero (T : WilkiesDesign.CG.LRc.Substructure K)
    (f : WilkiesDesign.CG.LRc.Embedding ↥T L) :
    f (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 0
        (Sum.inl (Sum.inl Ring.zeroFunc)) (![] : Fin 0 → ↥T)) = (0 : L) := by
  rw [@FirstOrder.Language.Embedding.map_fun WilkiesDesign.CG.LRc ↥T L _ _ f 0
    (Sum.inl (Sum.inl Ring.zeroFunc)) (![] : Fin 0 → ↥T)]
  have h2 : (⇑f ∘ (![] : Fin 0 → ↥T) : Fin 0 → L) = (![] : Fin 0 → L) := by
    funext i; exact Fin.elim0 i
  rw [h2, lpLrcFunMap_zero]

theorem lpEmbed_funMap_rexp
    (hrexpL : ∀ x : L, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL L _ 1
      WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (T : WilkiesDesign.CG.LRc.Substructure K) (f : WilkiesDesign.CG.LRc.Embedding ↥T L)
    (y : ↥T) :
    f (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 1
        (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) ![y])
      = Work.WilC5.rexpFromExp (f y) := by
  rw [@FirstOrder.Language.Embedding.map_fun WilkiesDesign.CG.LRc ↥T L _ _ f 1
    (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) (![y])]
  have h2 : (⇑f ∘ ![y] : Fin 1 → L) = ![f y] := by
    funext i; fin_cases i <;> rfl
  rw [h2, lpLrcFunMap_rexp hrexpL]

/-! ### In the value form -/

/-- The `rexp` symbol in the value form, with `rexpFromExp` in place of the symbol. -/
theorem lpEmbed_rexpFromExp
    (hrexpK : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
      WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hrexpL : ∀ x : L, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL L _ 1
      WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (T : WilkiesDesign.CG.LRc.Substructure K) (f : WilkiesDesign.CG.LRc.Embedding ↥T L)
    (y : ↥T) (hmem : Work.WilC5.rexpFromExp (y : K) ∈ T) :
    f ⟨Work.WilC5.rexpFromExp (y : K), hmem⟩ = Work.WilC5.rexpFromExp (f y) := by
  rw [show (⟨Work.WilC5.rexpFromExp (y : K), hmem⟩ : ↥T)
      = (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc ↥T _ 1
          (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp)) ![y]) from
      Subtype.ext (lpSubFunMap_rexp hrexpK T y).symm]
  exact lpEmbed_funMap_rexp hrexpL T f y

theorem lpEmbed_add (T : WilkiesDesign.CG.LRc.Substructure K) (f : WilkiesDesign.CG.LRc.Embedding ↥T L)
    (x y : ↥T) (h : (x : K) + (y : K) ∈ T) :
    f ⟨(x : K) + (y : K), h⟩ = f x + f y := by
  rw [lpSubElem_add T x y h]
  exact lpEmbed_funMap_add T f x y

theorem lpEmbed_mul (T : WilkiesDesign.CG.LRc.Substructure K) (f : WilkiesDesign.CG.LRc.Embedding ↥T L)
    (x y : ↥T) (h : (x : K) * (y : K) ∈ T) :
    f ⟨(x : K) * (y : K), h⟩ = f x * f y := by
  rw [lpSubElem_mul T x y h]
  exact lpEmbed_funMap_mul T f x y

theorem lpEmbed_neg (T : WilkiesDesign.CG.LRc.Substructure K) (f : WilkiesDesign.CG.LRc.Embedding ↥T L)
    (x : ↥T) (h : -(x : K) ∈ T) :
    f ⟨-(x : K), h⟩ = -f x := by
  rw [lpSubElem_neg T x h]
  exact lpEmbed_funMap_neg T f x

theorem lpEmbed_one (T : WilkiesDesign.CG.LRc.Substructure K) (f : WilkiesDesign.CG.LRc.Embedding ↥T L)
    (h : (1 : K) ∈ T) : f ⟨(1 : K), h⟩ = (1 : L) := by
  rw [lpSubElem_one T h]
  exact lpEmbed_funMap_one T f

theorem lpEmbed_zero (T : WilkiesDesign.CG.LRc.Substructure K) (f : WilkiesDesign.CG.LRc.Embedding ↥T L)
    (h : (0 : K) ∈ T) : f ⟨(0 : K), h⟩ = (0 : L) := by
  rw [lpSubElem_zero T h]
  exact lpEmbed_funMap_zero T f

/-! ### Natural and integral casts -/

theorem lpEmbed_natCast (T : WilkiesDesign.CG.LRc.Substructure K)
    (f : WilkiesDesign.CG.LRc.Embedding ↥T L)
    (hmem : ∀ n : ℕ, (((n : ℕ) : K)) ∈ T) (n : ℕ) :
    f ⟨(((n : ℕ) : K)), hmem n⟩ = (((n : ℕ) : L)) := by
  induction n with
  | zero =>
      have h0 : (0 : K) ∈ T := by simpa using hmem 0
      have hval : (((0 : ℕ) : K)) = (0 : K) := by push_cast; ring
      have heq : (⟨(((0 : ℕ) : K)), hmem 0⟩ : ↥T) = ⟨(0 : K), h0⟩ :=
        Subtype.ext hval
      rw [show f (⟨(((0 : ℕ) : K)), hmem 0⟩ : ↥T) = f ⟨(0 : K), h0⟩ from
          congrArg f heq,
        lpEmbed_zero T f h0]
      simp
  | succ n ih =>
      have h1 : (1 : K) ∈ T := by simpa using hmem 1
      have hmem' : ((n : K)) + (1 : K) ∈ T := by
        rw [← Nat.cast_succ n]; exact hmem (n + 1)
      have hval : (((n + 1 : ℕ) : K)) = ((n : K)) + (1 : K) := by push_cast; ring
      have heq : (⟨(((n + 1 : ℕ) : K)), hmem (n + 1)⟩ : ↥T)
          = ⟨((n : K)) + (1 : K), hmem'⟩ :=
        Subtype.ext hval
      rw [show f (⟨(((n + 1 : ℕ) : K)), hmem (n + 1)⟩ : ↥T)
            = f ⟨((n : K)) + (1 : K), hmem'⟩ from congrArg f heq,
        lpEmbed_add T f ⟨((n : K)), hmem n⟩ ⟨(1 : K), h1⟩ hmem', ih, lpEmbed_one T f h1]
      push_cast
      ring

theorem lpEmbed_intCast (T : WilkiesDesign.CG.LRc.Substructure K)
    (f : WilkiesDesign.CG.LRc.Embedding ↥T L)
    (hmem : ∀ z : ℤ, ((z : ℤ) : K) ∈ T) (z : ℤ) :
    f ⟨((z : ℤ) : K), hmem z⟩ = ((z : ℤ) : L) := by
  have hmemN : ∀ m : ℕ, (((m : ℕ) : K)) ∈ T := fun m => by
    have h := hmem (m : ℤ)
    rwa [Int.cast_natCast] at h
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · have hval : (((↑n : ℤ) : K)) = (((n : ℕ) : K)) := by push_cast; ring
    have heq : (⟨(((↑n : ℤ) : K)), hmem (↑n)⟩ : ↥T)
        = ⟨(((n : ℕ) : K)), hmemN n⟩ := Subtype.ext hval
    rw [show f (⟨(((↑n : ℤ) : K)), hmem (↑n)⟩ : ↥T)
          = f ⟨(((n : ℕ) : K)), hmemN n⟩ from congrArg f heq,
      lpEmbed_natCast T f hmemN n]
    push_cast
    ring
  · have hneg : -(((n : ℕ) : K)) ∈ T := by
      have h := hmem (-(n : ℤ))
      rwa [Int.cast_neg, Int.cast_natCast] at h
    have hval : ((↑(-(n : ℤ)) : ℤ) : K) = -(((n : ℕ) : K)) := by push_cast; ring
    have heq : (⟨((↑(-(n : ℤ)) : ℤ) : K), hmem (-(n : ℤ))⟩ : ↥T)
        = ⟨-(((n : ℕ) : K)), hneg⟩ := Subtype.ext hval
    rw [show f (⟨((↑(-(n : ℤ)) : ℤ) : K), hmem (-(n : ℤ))⟩ : ↥T)
          = f ⟨-(((n : ℕ) : K)), hneg⟩ from congrArg f heq,
      lpEmbed_neg T f ⟨(((n : ℕ) : K)), hmemN n⟩ hneg, lpEmbed_natCast T f hmemN n]
    push_cast
    ring

/-! ### Powers and inverses -/

theorem lpEmbed_pow_nat (T : WilkiesDesign.CG.LRc.Substructure K)
    (f : WilkiesDesign.CG.LRc.Embedding ↥T L) (x : ↥T)
    (hmem : ∀ n : ℕ, (x : K) ^ n ∈ T) (n : ℕ) :
    f ⟨(x : K) ^ n, hmem n⟩ = (f x) ^ n := by
  induction n with
  | zero =>
      have hone : (1 : K) ∈ T := by rw [← pow_zero (x : K)]; exact hmem 0
      have hval : (x : K) ^ 0 = (1 : K) := by rw [pow_zero]
      have heq : (⟨(x : K) ^ 0, hmem 0⟩ : ↥T) = ⟨(1 : K), hone⟩ :=
        Subtype.ext hval
      rw [show f (⟨(x : K) ^ 0, hmem 0⟩ : ↥T) = f ⟨(1 : K), hone⟩ from
          congrArg f heq,
        lpEmbed_one T f hone, pow_zero]
  | succ n ih =>
      have hmem' : (x : K) ^ n * (x : K) ∈ T := by
        rw [← pow_succ]; exact hmem (n + 1)
      have hval : (x : K) ^ (n + 1) = (x : K) ^ n * (x : K) := pow_succ (x : K) n
      have heq : (⟨(x : K) ^ (n + 1), hmem (n + 1)⟩ : ↥T)
          = ⟨(x : K) ^ n * (x : K), hmem'⟩ := Subtype.ext hval
      rw [show f (⟨(x : K) ^ (n + 1), hmem (n + 1)⟩ : ↥T)
            = f ⟨(x : K) ^ n * (x : K), hmem'⟩ from congrArg f heq,
        lpEmbed_mul T f ⟨(x : K) ^ n, hmem n⟩ x hmem', ih, pow_succ]

theorem lpEmbed_inv (T : WilkiesDesign.CG.LRc.Substructure K)
    (f : WilkiesDesign.CG.LRc.Embedding ↥T L) (x : ↥T) (hx0 : (x : K) ≠ 0)
    (hmem : (x : K)⁻¹ ∈ T) (hone : (1 : K) ∈ T) :
    f ⟨(x : K)⁻¹, hmem⟩ = (f x)⁻¹ := by
  have hmem' : (x : K) * (x : K)⁻¹ ∈ T := by
    rw [mul_inv_cancel₀ hx0]; exact hone
  have h := lpEmbed_mul T f x ⟨(x : K)⁻¹, hmem⟩ hmem'
  have hval : (x : K) * (x : K)⁻¹ = (1 : K) := mul_inv_cancel₀ hx0
  have h1 : (⟨(x : K) * (x : K)⁻¹, hmem'⟩ : ↥T) = ⟨(1 : K), hone⟩ :=
    Subtype.ext hval
  rw [h1, lpEmbed_one T f hone] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem lpEmbed_zpow (T : WilkiesDesign.CG.LRc.Substructure K)
    (f : WilkiesDesign.CG.LRc.Embedding ↥T L) (x : ↥T) (hx0 : (x : K) ≠ 0)
    (hmemZ : ∀ z : ℤ, (x : K) ^ z ∈ T) (hmemN : ∀ n : ℕ, (x : K) ^ n ∈ T)
    (hone : (1 : K) ∈ T) (z : ℤ) :
    f ⟨(x : K) ^ z, hmemZ z⟩ = (f x) ^ z := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · have hval : (x : K) ^ (↑n : ℤ) = (x : K) ^ n := zpow_natCast (x : K) n
    have heq : (⟨(x : K) ^ (↑n : ℤ), hmemZ (↑n)⟩ : ↥T)
        = ⟨(x : K) ^ n, hmemN n⟩ := Subtype.ext hval
    rw [show f (⟨(x : K) ^ (↑n : ℤ), hmemZ (↑n)⟩ : ↥T)
          = f ⟨(x : K) ^ n, hmemN n⟩ from congrArg f heq,
      lpEmbed_pow_nat T f x hmemN n, zpow_natCast]
  · have hmem' : ((x : K) ^ n)⁻¹ ∈ T := by
      have h := hmemZ (-(↑n : ℤ))
      rwa [zpow_neg, zpow_natCast] at h
    have hval : (x : K) ^ (-(↑n : ℤ)) = ((x : K) ^ n)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    have heq : (⟨(x : K) ^ (-(↑n : ℤ)), hmemZ (-(↑n : ℤ))⟩ : ↥T)
        = ⟨((x : K) ^ n)⁻¹, hmem'⟩ := Subtype.ext hval
    rw [show f (⟨(x : K) ^ (-(↑n : ℤ)), hmemZ (-(↑n : ℤ))⟩ : ↥T)
          = f ⟨((x : K) ^ n)⁻¹, hmem'⟩ from congrArg f heq,
      lpEmbed_inv T f ⟨(x : K) ^ n, hmemN n⟩ (pow_ne_zero n hx0) hmem' hone,
      lpEmbed_pow_nat T f x hmemN n]
    rw [zpow_neg, zpow_natCast]

end EmbedComm

end Work.WilC5.S4ExpG
