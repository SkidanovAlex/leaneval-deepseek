import Mathlib
import Submission.Work.WilVP.Defs
import Submission.Work.WilVP.isRpow_eq_rpow

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilVP

/-! ## 0. The ring symbols of `LRc` and the coordinate-`0` term

`LRc = (ring ⊕ rexpL)[[ℝ]]` has a constant symbol for every real (`Sum.inr σ`), so the
polynomial expression `v 2 + σ * v 0` is a term of `LRc` and hence a `∅`-definable function. -/

/-- The addition symbol of `LRc = (ring ⊕ rexpL)[[ℝ]]`. -/
abbrev shift_lrcAdd : LRc.Functions 2 := Sum.inl (Sum.inl FirstOrder.Ring.addFunc)

/-- The multiplication symbol of `LRc = (ring ⊕ rexpL)[[ℝ]]`. -/
abbrev shift_lrcMul : LRc.Functions 2 := Sum.inl (Sum.inl FirstOrder.Ring.mulFunc)

/-- The constant `σ` of `ℝ` as a term of `LRc` (via its constant symbol `Sum.inr σ`). -/
def shift_cTerm {α : Type*} (σ : ℝ) : LRc.Term α := (LR.con σ).term

theorem shift_cTerm_realize {α : Type*} (σ : ℝ) (v : α → ℝ) :
    (shift_cTerm σ : LRc.Term α).realize v = σ := by
  rw [shift_cTerm, Term.realize_constants]
  rfl

/-- The `LRc`-term `σ * v j`. -/
def shift_mulTerm {α : Type*} (σ : ℝ) (j : α) : LRc.Term α :=
  Term.func shift_lrcMul (![shift_cTerm σ, Term.var j] : Fin 2 → LRc.Term α)

theorem shift_mulTerm_realize {α : Type*} (σ : ℝ) (v : α → ℝ) (j : α) :
    (shift_mulTerm σ j).realize v = σ * v j := by
  rw [shift_mulTerm, Term.realize_func]
  have h : (fun k : Fin 2 => Term.realize v
      ((![shift_cTerm σ, Term.var j] : Fin 2 → LRc.Term α) k)) = ![σ, v j] := by
    funext k; fin_cases k
    · exact shift_cTerm_realize σ v
    · rfl
  rw [h]; rfl

/-- The `LRc`-term `v i + σ * v j`. -/
def shift_addMulTerm {α : Type*} (σ : ℝ) (i j : α) : LRc.Term α :=
  Term.func shift_lrcAdd (![Term.var i, shift_mulTerm σ j] : Fin 2 → LRc.Term α)

theorem shift_addMulTerm_realize {α : Type*} (σ : ℝ) (v : α → ℝ) (i j : α) :
    (shift_addMulTerm σ i j).realize v = v i + σ * v j := by
  rw [shift_addMulTerm, Term.realize_func]
  have h : (fun k : Fin 2 => Term.realize v
      ((![Term.var i, shift_mulTerm σ j] : Fin 2 → LRc.Term α) k)) = ![v i, σ * v j] := by
    funext k; fin_cases k
    · rfl
    · exact shift_mulTerm_realize σ v j
  rw [h]; rfl

/-- The function `v ↦ v i + σ * v j` is `∅`-definable in `LRc`. -/
theorem shift_definableFun_add_mul {α : Type*} (σ : ℝ) (i j : α) :
    (∅ : Set ℝ).DefinableFun LRc (fun v : α → ℝ => v i + σ * v j) := by
  have h := Term.definableFun_realize (L := LRc) (M := ℝ) (α := α) (shift_addMulTerm σ i j)
  rw [show (fun v : α → ℝ => v i + σ * v j) = fun v => (shift_addMulTerm σ i j).realize v from
    funext (fun v => (shift_addMulTerm_realize σ v i j).symm)]
  exact h

/-! ## 1. The recentring map and the definability of `shiftFam` -/

/-- The polynomial map whose preimage of `Y` is the recentred family `Work.WilVP.shiftFam Y σ`:
`v ↦ (v 2 + σ * v 0, v 1, v 3, v 4, …)`. -/
def shiftMap {k : ℕ} (σ : ℝ) : (Fin ((k + 1) + 2) → ℝ) → (Fin (k + 2) → ℝ) :=
  fun v => Fin.cons (v 2 + σ * v 0) (Fin.cons (v 1) (Fin.tail (Fin.tail (Fin.tail v))))

theorem shiftFam_eq_preimage_shiftMap {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (σ : ℝ) :
    shiftFam Y σ = shiftMap (k := k) σ ⁻¹' Y := rfl

theorem shiftMap_apply_zero {k : ℕ} (σ : ℝ) (v : Fin ((k + 1) + 2) → ℝ) :
    shiftMap (k := k) σ v 0 = v 2 + σ * v 0 := by
  simp [shiftMap, Fin.cons_zero]

theorem shiftMap_apply_one {k : ℕ} (σ : ℝ) (v : Fin ((k + 1) + 2) → ℝ) :
    shiftMap (k := k) σ v 1 = v 1 := by
  simp [shiftMap, Fin.cons_zero]

theorem shiftMap_apply_succ_succ {k : ℕ} (σ : ℝ) (v : Fin ((k + 1) + 2) → ℝ) (j : Fin k) :
    shiftMap (k := k) σ v (Fin.succ (Fin.succ j)) = v (Fin.succ (Fin.succ (Fin.succ j))) := by
  simp [shiftMap, Fin.cons_succ, Fin.tail]

/-- Each coordinate of the recentring map is `∅`-definable in `LRc`. -/
theorem shiftMap_definableMap {k : ℕ} (σ : ℝ) :
    (∅ : Set ℝ).DefinableMap LRc (shiftMap (k := k) σ) := by
  intro i
  induction i using Fin.cases with
  | zero =>
    have h := shift_definableFun_add_mul (α := Fin ((k + 1) + 2)) (i := 2) (j := 0) σ
    rw [show (fun v : Fin ((k + 1) + 2) → ℝ => shiftMap (k := k) σ v 0)
        = (fun v : Fin ((k + 1) + 2) → ℝ => v 2 + σ * v 0) from
      funext (fun v => shiftMap_apply_zero σ v)]
    exact h
  | succ i1 =>
    induction i1 using Fin.cases with
    | zero =>
      have h := Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ))
        (α := Fin ((k + 1) + 2)) (i := (1 : Fin ((k + 1) + 2)))
      rw [show (fun v : Fin ((k + 1) + 2) → ℝ => shiftMap (k := k) σ v (Fin.succ 0))
          = (fun v : Fin ((k + 1) + 2) → ℝ => v 1) from
        funext (fun v => shiftMap_apply_one σ v)]
      exact h
    | succ j =>
      have h := Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ))
        (α := Fin ((k + 1) + 2)) (i := Fin.succ (Fin.succ (Fin.succ j)))
      rw [show (fun v : Fin ((k + 1) + 2) → ℝ => shiftMap (k := k) σ v (Fin.succ (Fin.succ j)))
          = (fun v : Fin ((k + 1) + 2) → ℝ => v (Fin.succ (Fin.succ (Fin.succ j)))) from
        funext (fun v => shiftMap_apply_succ_succ σ v j)]
      exact h

/-- **The recentred family is `∅`-definable.** `shiftFam Y σ` is the preimage of `Y` under the
polynomial map `shiftMap σ`, whose coordinates are `∅`-definable. -/
theorem shiftFam_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) (σ : ℝ) :
    (∅ : Set ℝ).Definable LRc (shiftFam Y σ) := by
  rw [shiftFam_eq_preimage_shiftMap Y σ]
  exact hY.preimage_map (shiftMap_definableMap (k := k) σ)

/-- ULPM data transported to the recentred family `t ↦ F_c(p + σ t)` (`Work.WilVP.shiftFam`,
σ = ±1).  Apply `Work.WilC4.Route.ModelULPM ℝ` to `Work.WilVP.shiftFam Y σ`, then rewrite
`Work.WilVP.mem_shiftFam'` to replace the recentred coordinates by `p + σ * x` and convert the
existential `Work.WilC4.IsRpow x q t` into `t = x ^ (q:ℝ)` with `Work.WilVP.isRpow_eq_rpow`
(possible since `x₁, x₂ > 0`).  `B` is the breakpoint family of the recentred family, with
parameters `(p, c) : Fin (k+1)`.
Needed along the way (both provable here, `Work.WilVP` already has `shiftFam_fun`):
`shiftFam Y σ` is `∅`-definable, as the preimage of `Y` under the polynomial map
`v ↦ Fin.cons (v 2 + σ * v 0) (Fin.cons (v 1) (Fin.tail (Fin.tail (Fin.tail v))))`
(`Set.Definable.preimage_map` with `Set.DefinableMap`/`fun_prop`, the constant `σ` coming from the
constant symbol `Sum.inr σ` of `LRc`). -/
theorem shift_ulpm_data {k : ℕ} (hU : Work.WilC4.Route.ModelULPM ℝ)
    {Y : Set (Fin (k + 2) → ℝ)} (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
      Fin.cons x (Fin.cons y' c) ∈ Y → y = y') (σ : ℝ) :
    ∃ N : ℕ, 0 < N ∧ ∃ Qs : Finset ℚ, ∃ B : Set (Fin (k + 2) → ℝ),
      (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B ∧
      (∀ cc : Fin (k + 1) → ℝ, {t : ℝ | Fin.cons t cc ∈ B}.encard ≤ N) ∧
      ∀ (p : ℝ) (c : Fin k → ℝ) (x₁ x₂ : ℝ), 0 < x₁ → 0 < x₂ →
        Work.WilC4.Route.SameSide N {t : ℝ | Fin.cons t (Fin.cons p c) ∈ B} x₁ x₂ →
        ((∃ y : ℝ, Fin.cons (p + σ * x₁) (Fin.cons y c) ∈ Y) ↔
          (∃ y : ℝ, Fin.cons (p + σ * x₂) (Fin.cons y c) ∈ Y)) ∧
        ∀ y₁ y₂ : ℝ, Fin.cons (p + σ * x₁) (Fin.cons y₁ c) ∈ Y →
          Fin.cons (p + σ * x₂) (Fin.cons y₂ c) ∈ Y →
          ∃ q ∈ Qs, |y₂| * x₁ ^ (q : ℝ) ≤ (N : ℝ) * (|y₁| * x₂ ^ (q : ℝ)) ∧
            |y₁| * x₂ ^ (q : ℝ) ≤ (N : ℝ) * (|y₂| * x₁ ^ (q : ℝ)) := by
  -- Apply `ModelULPM ℝ` to the recentred family `shiftFam Y σ` (a family of graphs with
  -- parameters `Fin (k+1) → ℝ`).
  obtain ⟨N, hN, Qs, B, hBdef, hmain⟩ :=
    hU (k + 1) (shiftFam Y σ) (shiftFam_definable hY σ) (shiftFam_fun hfun)
  refine ⟨N, hN, Qs, B, hBdef, fun cc => (hmain cc).1, ?_⟩
  intro p c x₁ x₂ hx₁ hx₂ hss
  obtain ⟨hdom, hval⟩ := (hmain (Fin.cons p c)).2 x₁ x₂ hx₁ hx₂ hss
  constructor
  · -- the domain statuses agree
    have h₁ := exists_congr (fun y : ℝ => (mem_shiftFam Y σ x₁ y p c).symm)
    have h₂ := exists_congr (fun y : ℝ => (mem_shiftFam Y σ x₂ y p c).symm)
    exact h₁.trans (hdom.trans h₂.symm)
  · -- the values are log-piecewise-monomially comparable, with the genuine real powers
    intro y₁ y₂ hy₁ hy₂
    have h₁ : Fin.cons x₁ (Fin.cons y₁ (Fin.cons p c)) ∈ shiftFam Y σ :=
      (mem_shiftFam Y σ x₁ y₁ p c).mpr hy₁
    have h₂ : Fin.cons x₂ (Fin.cons y₂ (Fin.cons p c)) ∈ shiftFam Y σ :=
      (mem_shiftFam Y σ x₂ y₂ p c).mpr hy₂
    obtain ⟨q, hq, t₁, t₂, hr₁, hr₂, hle₁, hle₂⟩ := hval y₁ y₂ h₁ h₂
    rw [isRpow_eq_rpow hx₁ hr₁, isRpow_eq_rpow hx₂ hr₂] at hle₁ hle₂
    exact ⟨q, hq, hle₁, hle₂⟩

end Work.WilVP
