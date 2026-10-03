import Mathlib
import Submission.Work.Peluse.UControl.HistInv
import Submission.Work.Peluse.UControl.LevelOne
import Submission.Work.Peluse.UControl.HistEval
import Submission.Work.Peluse.UControl.linFamAvg_zero_term

/-!
# The vocabulary of the level-one comparison

This file collects the objects that the comparison
`Work.Peluse.UControl.level1Compare` needs: the identification of the terminal state of the
phase-1 chain of Peluse's §4 (a `HistData 2 n` satisfying `Phase1Terminal`) with the level-`1`
datum of the paper's nested family (`levelOneDatum n`).

* `boolOfFinset`/`finsetOfBool` — the Boolean function of a finite set and back (a nonempty
  finite set of `Fin n` is the same thing as a nonzero Boolean function);
* `i1Symm`, `levelSlotBool`, `levelSlot` — the `i`-th slot of the terminal state: the terminal
  live slots are exactly the `(P, h)` with `h ≠ 0`, so the level-`1` index `i : Fin |I 1|`
  names the slot `(P, boolOfFinset (i1Symm n i))`;
* `winValInv`, `towerOf` — the inverse of the window parametrisation, and the tower point with
  prescribed window parameters;
* `idxPair`, `towerIdx` — the level-`2` parameter family attached to a window-tower point
  (`towerIdx H n (k,t)` has level-`1` part `WinTower.param H n t` and level-`0` part `boxVal H k`);
* `sGOf`, `bOf` — the Boolean family `b` of `linFamAvg`: the flag distinguishing `G i = Ftop`
  from `G i = star Ftop`, flipped when the base function uses the conjugate;
* `levelBeta` — the constant term `β` of the comparison (the paper's `p'_i(a)`);
* `histCorr` — the (complex) correlation of the terminal state at a tower point.

The direction identity `petDir_levelOne` (the terminal direction is `2·lc·Σ_{s ∈ ω} a₁ s`) is
recorded here too, since it is what makes the level-`1` datum the right one.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Boolean functions and finite sets -/

/-- The Boolean function of a finite set of `Fin n`. -/
def boolOfFinset {n : ℕ} (w : Finset (Fin n)) : Fin n → Bool := fun s => decide (s ∈ w)

/-- The finite set of a Boolean function on `Fin n`. -/
def finsetOfBool {n : ℕ} (h : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun s => h s)

lemma finsetOfBool_boolOfFinset {n : ℕ} (w : Finset (Fin n)) :
    finsetOfBool (boolOfFinset w) = w := by
  ext s; simp [finsetOfBool, boolOfFinset]

lemma boolOfFinset_finsetOfBool {n : ℕ} (h : Fin n → Bool) :
    boolOfFinset (finsetOfBool h) = h := by
  funext s
  simp only [boolOfFinset, finsetOfBool, Finset.mem_filter, Finset.mem_univ, true_and]
  cases h s <;> simp

lemma finsetOfBool_zero {n : ℕ} : finsetOfBool (0 : Fin n → Bool) = ∅ := by
  ext s; simp [finsetOfBool]

lemma boolOfFinset_empty {n : ℕ} : boolOfFinset (∅ : Finset (Fin n)) = 0 := by
  funext s
  show decide (s ∈ (∅ : Finset (Fin n))) = false
  simp

lemma boolOfFinset_ne_zero_iff {n : ℕ} (w : Finset (Fin n)) :
    boolOfFinset w ≠ 0 ↔ w.Nonempty := by
  constructor
  · intro h
    rw [Finset.nonempty_iff_ne_empty]
    intro hw
    exact h (by rw [hw]; exact boolOfFinset_empty)
  · intro h hb
    exact h.ne_empty (by rw [← finsetOfBool_boolOfFinset w, hb, finsetOfBool_zero])

/-! ## The window tower -/

/-- The (modular) inverse of the window parametrisation `k ↦ `winVal H k = k - H``; it is the
genuine inverse on `[-H, H]`. -/
def winValInv (H : ℕ) (v : ℤ) : Fin (2 * H + 1) :=
  ⟨Int.toNat (v + H) % (2 * H + 1), Nat.mod_lt _ (by omega)⟩

/-- The tower point with prescribed window parameters (garbage outside `[-H,H]^n`). -/
def towerOf (H : ℕ) : ∀ n, (Fin n → ℤ) → WinTower H n
  | 0, _ => (0 : Fin 1)
  | (n + 1), u => (towerOf H n (fun i => u i.castSucc), winValInv H (u (Fin.last n)))

lemma winVal_winValInv {H : ℕ} {v : ℤ} (h1 : -(H : ℤ) ≤ v) (h2 : v ≤ (H : ℤ)) :
    PetStep.winVal H (winValInv H v) = v := by
  have h0 : (0 : ℤ) ≤ v + H := by omega
  have h3 : v + H ≤ ((2 * H : ℕ) : ℤ) := by push_cast; omega
  have h4 : Int.toNat (v + H) ≤ 2 * H := by
    have h5 : ((Int.toNat (v + H) : ℕ) : ℤ) ≤ ((2 * H : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h0]; exact h3
    exact_mod_cast h5
  have h6 : Int.toNat (v + H) % (2 * H + 1) = Int.toNat (v + H) :=
    Nat.mod_eq_of_lt (by omega)
  have h7 : ((Int.toNat (v + H) : ℕ) : ℤ) = v + H := Int.toNat_of_nonneg h0
  simp only [winValInv, h6, PetStep.winVal]
  omega

lemma param_towerOf : ∀ (H n : ℕ) (u : Fin n → ℤ),
    (∀ s, -(H : ℤ) ≤ u s ∧ u s ≤ H) → WinTower.param H n (towerOf H n u) = u := by
  intro H n
  induction n with
  | zero => intro u _; funext s; exact s.elim0
  | succ n ih =>
    intro u hu
    have h1 : towerOf H (n + 1) u
        = (towerOf H n (fun i => u i.castSucc), winValInv H (u (Fin.last n))) := rfl
    rw [h1]
    funext s
    refine Fin.lastCases ?_ (fun i => ?_) s
    · rw [WinTower.param_last]
      exact winVal_winValInv (hu (Fin.last n)).1 (hu (Fin.last n)).2
    · rw [WinTower.param_castSucc]
      exact congrFun (ih (fun i => u i.castSucc) (fun i => hu i.castSucc)) i

lemma winVal_injective (H : ℕ) : Function.Injective (PetStep.winVal H) := by
  intro a b h
  have h' : (a : ℤ) = (b : ℤ) := by
    simp only [PetStep.winVal] at h
    omega
  exact Fin.ext (by exact_mod_cast h')

lemma param_injective (H : ℕ) : ∀ n, Function.Injective (WinTower.param H n) := by
  intro n
  induction n with
  | zero =>
    intro a b _
    have : Subsingleton (WinTower H 0) := inferInstanceAs (Subsingleton (Fin 1))
    exact Subsingleton.elim a b
  | succ n ih =>
    intro a b h
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    have h1 : a2 = b2 := winVal_injective H (by
      have := congrFun h (Fin.last n)
      rw [WinTower.param_last, WinTower.param_last] at this
      exact this)
    have h2 : a1 = b1 := ih (by
      funext i
      have := congrFun h (Fin.castSucc i)
      rw [WinTower.param_castSucc, WinTower.param_castSucc] at this
      exact this)
    exact Prod.ext h2 h1

lemma param_abs_le (H : ℕ) : ∀ (n : ℕ) (t : WinTower H n) (s : Fin n),
    |WinTower.param H n t s| ≤ (H : ℤ) := by
  intro n
  induction n with
  | zero => intro t s; exact s.elim0
  | succ n ih =>
    intro t s
    obtain ⟨t', k⟩ := t
    refine Fin.lastCases ?_ (fun i => ?_) s
    · rw [WinTower.param_last]
      exact abs_le.mpr (PetStep.winVal_mem H k)
    · rw [WinTower.param_castSucc]
      exact ih t' i

lemma param_bounds (H : ℕ) (n : ℕ) (t : WinTower H n) :
    ∀ s, -(H : ℤ) ≤ WinTower.param H n t s ∧ WinTower.param H n t s ≤ H :=
  fun s => abs_le.mp (param_abs_le H n t s)

/-- `towerOf` is the inverse of the window parametrisation. -/
lemma towerOf_param (H n : ℕ) (t : WinTower H n) :
    towerOf H n (WinTower.param H n t) = t :=
  param_injective H n (by rw [param_towerOf H n _ (param_bounds H n t)])

/-! ## The level-one index and the terminal slots -/

/-- The level-`(l-1)` index set of the level-one datum, unrolled as a nonempty set of `Fin n`. -/
def i1Symm (n : ℕ) (i : Fin (Fintype.card ((levelOneDatum n).I 1))) :
    {T : Finset (Fin n) // T.Nonempty} :=
  (Fintype.equivFin ((levelOneDatum n).I 1)).symm i

/-- The Boolean history attached to the level-`1` index `i`. -/
def levelSlotBool (n : ℕ) (i : Fin (Fintype.card ((levelOneDatum n).I 1))) : Fin n → Bool :=
  boolOfFinset (i1Symm n i).val

/-- The slot of the terminal state attached to the level-`1` index `i`. -/
def levelSlot {n : ℕ} (lc : ℤ) (Y : HistData 2 n) (hT : Phase1Terminal 2 n lc Y)
    (i : Fin (Fintype.card ((levelOneDatum n).I 1))) : (Y.toSym).S.ι :=
  ⟨((Sum.inr 0 : InitIdx 2), levelSlotBool n i),
    hT.2 (levelSlotBool n i) ((boolOfFinset_ne_zero_iff _).mpr (i1Symm n i).2)⟩

@[simp] lemma levelSlot_val {n : ℕ} (lc : ℤ) (Y : HistData 2 n)
    (hT : Phase1Terminal 2 n lc Y) (i : Fin (Fintype.card ((levelOneDatum n).I 1))) :
    (levelSlot lc Y hT i).1 = ((Sum.inr 0 : InitIdx 2), levelSlotBool n i) := rfl

/-! ## The level-two parameter family attached to a tower point -/

/-- The level-`2` parameter family with prescribed level-`0` and level-`1` parts. -/
def idxPair (n : ℕ) (v0 : PUnit → ℤ) (v1 : Fin n → ℤ) : (levelOneDatum n).Idx 2 :=
  (piFinTwoEquiv (fun j : Fin 2 => levelOneS n (j : ℕ) → ℤ)).symm (v0, v1)

@[simp] lemma idxPair_zero (n : ℕ) (v0 : PUnit → ℤ) (v1 : Fin n → ℤ) :
    (idxPair n v0 v1) 0 = v0 := by
  have h := Equiv.apply_symm_apply
    (piFinTwoEquiv (fun j : Fin 2 => levelOneS n (j : ℕ) → ℤ)) (v0, v1)
  have h2 : ((piFinTwoEquiv (fun j : Fin 2 => levelOneS n (j : ℕ) → ℤ))
      ((piFinTwoEquiv (fun j : Fin 2 => levelOneS n (j : ℕ) → ℤ)).symm (v0, v1))).1 = v0 := by
    rw [h]
  exact h2

@[simp] lemma idxPair_one (n : ℕ) (v0 : PUnit → ℤ) (v1 : Fin n → ℤ) :
    (idxPair n v0 v1) 1 = v1 := by
  have h := Equiv.apply_symm_apply
    (piFinTwoEquiv (fun j : Fin 2 => levelOneS n (j : ℕ) → ℤ)) (v0, v1)
  have h2 : ((piFinTwoEquiv (fun j : Fin 2 => levelOneS n (j : ℕ) → ℤ))
      ((piFinTwoEquiv (fun j : Fin 2 => levelOneS n (j : ℕ) → ℤ)).symm (v0, v1))).2 = v1 := by
    rw [h]
  exact h2

/-- The level-`2` parameter family attached to a point of the window tower: the level-`1` part is
the tower parameter and the level-`0` part is the free window position `k`. -/
def towerIdx (H n : ℕ) (p : Fin (2 * H + 1) × WinTower H n) : (levelOneDatum n).Idx 2 :=
  idxPair n (fun _ => IdxDatum.boxVal H p.1) (WinTower.param H n p.2)

@[simp] lemma towerIdx_one (H n : ℕ) (p : Fin (2 * H + 1) × WinTower H n) :
    (towerIdx H n p) 1 = WinTower.param H n p.2 :=
  idxPair_one n (fun _ => IdxDatum.boxVal H p.1) (WinTower.param H n p.2)

@[simp] lemma towerIdx_zero (H n : ℕ) (p : Fin (2 * H + 1) × WinTower H n) :
    (towerIdx H n p) 0 = fun _ => IdxDatum.boxVal H p.1 :=
  idxPair_zero n (fun _ => IdxDatum.boxVal H p.1) (WinTower.param H n p.2)

lemma towerIdx_injective (H n : ℕ) : Function.Injective (towerIdx H n) := by
  intro p q h
  have h0 := congrFun h (0 : Fin 2)
  have h1 := congrFun h 1
  simp only [towerIdx_one, towerIdx_zero] at h0 h1
  have hk : p.1 = q.1 := by
    have := congrFun h0 PUnit.unit
    simp only [IdxDatum.boxVal] at this
    omega
  have ht : p.2 = q.2 := param_injective H n h1
  exact Prod.ext hk ht

/-! ## The constant term `β` and the Boolean family `b` -/

/-- The constant term of the slot `i` of the terminal state, evaluated at the window parameters
of the level-`1` part of `a`.  This is the paper's `p'_i(a)`. -/
def levelBeta {n : ℕ} (Y : HistData 2 n) (H : ℕ) (a : (levelOneDatum n).Idx 2)
    (i : Fin (Fintype.card ((levelOneDatum n).I 1))) : ℤ :=
  MvPolynomial.eval (WinTower.param H n (towerOf H n (fun s : Fin n => a 1 s)))
    ((Y.Q (Sum.inr 0 : InitIdx 2) (levelSlotBool n i)).coeff 0)

/-- The flag telling whether the slot function `G i` is `Ftop` or its conjugate. -/
def sGOf {n : ℕ} {Y : HistData 2 n} (Ftop : ℤ → ℂ) (G : (Y.toSym).S.ι → ℤ → ℂ)
    (i : (Y.toSym).S.ι) : Bool := if ∀ x, G i x = Ftop x then false else true

/-- The Boolean family `b` of `linFamAvg`: the flag of `G i`, flipped when the base function `g`
is the conjugate of `Ftop`. -/
def bOf {n : ℕ} {lc : ℤ} {Y : HistData 2 n} (hT : Phase1Terminal 2 n lc Y) (c₀ : Bool)
    (Ftop : ℤ → ℂ) (G : (Y.toSym).S.ι → ℤ → ℂ)
    (i : Fin (Fintype.card ((levelOneDatum n).I 1))) : Bool :=
  bif c₀ then !(sGOf Ftop G (levelSlot lc Y hT i)) else sGOf Ftop G (levelSlot lc Y hT i)

@[simp] lemma bOf_false {n : ℕ} {lc : ℤ} {Y : HistData 2 n} (hT : Phase1Terminal 2 n lc Y)
    (Ftop : ℤ → ℂ) (G : (Y.toSym).S.ι → ℤ → ℂ)
    (i : Fin (Fintype.card ((levelOneDatum n).I 1))) :
    bOf hT false Ftop G i = sGOf Ftop G (levelSlot lc Y hT i) := rfl

@[simp] lemma bOf_true {n : ℕ} {lc : ℤ} {Y : HistData 2 n} (hT : Phase1Terminal 2 n lc Y)
    (Ftop : ℤ → ℂ) (G : (Y.toSym).S.ι → ℤ → ℂ)
    (i : Fin (Fintype.card ((levelOneDatum n).I 1))) :
    bOf hT true Ftop G i = !(sGOf Ftop G (levelSlot lc Y hT i)) := rfl

lemma sGOf_spec {n : ℕ} {Y : HistData 2 n} (Ftop : ℤ → ℂ) (G : (Y.toSym).S.ι → ℤ → ℂ)
    (htop : ∀ i, (∀ x, G i x = Ftop x) ∨ (∀ x, G i x = star (Ftop x)))
    (i : (Y.toSym).S.ι) (z : ℤ) :
    G i z = if sGOf Ftop G i then star (Ftop z) else Ftop z := by
  by_cases h : ∀ x, G i x = Ftop x
  · simp [sGOf, h, h z]
  · have h2 : ∀ x, G i x = star (Ftop x) := (htop i).resolve_left h
    simp [sGOf, h, h2 z]

/-! ## The correlation of the terminal state -/

/-- The (complex) correlation of the terminal state at the tower point `t`: the paper's
`(NM)⁻¹ Σ_x g_t(x) Σ_{y∈[M]} ∏_i G_i(x + Q_i(t,y))`.  Its modulus is the summand of the state's
`lam`, and the comparison identifies it with `linCore`. -/
def histCorr {n : ℕ} (Y : HistData 2 n) (H N M : ℕ) (G : (Y.toSym).S.ι → ℤ → ℂ)
    (g : WinTower H n → ℤ → ℂ) (t : WinTower H n) : ℂ :=
  ((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, g t x *
    ∑ y ∈ Finset.Icc 1 M, ∏ i : (Y.toSym).S.ι,
      G i (x + ((((Y.toSym).S.P i).map
        (MvPolynomial.eval (WinTower.param H n t))).eval (y : ℤ)))

/-- The state's `lam` is the `ν`-average of the moduli of the correlations. -/
lemma toPetP_lam_eq {n : ℕ} (Y : HistData 2 n) (H N M : ℕ) (G : (Y.toSym).S.ι → ℤ → ℂ)
    (g : WinTower H n → ℤ → ℂ) :
    ((Y.toSym).S.toPetP H G g).toState.lam N M
      = ∑ t : WinTower H n, WinTower.nu H n t * ‖histCorr Y H N M G g t‖ := rfl

/-! ## The direction of the level-one datum -/

lemma IdxDatum.dir_succ (D : IdxDatum) (l : ℕ) (c : ℤ) (j : ℕ) (w : D.I (j+1))
    (a : (j : ℕ) → D.S j → ℤ) :
    D.dir l c (j+1) w a
      = ∑ s ∈ w.val, ((l : ℤ) - (j : ℤ)) * D.dir l c j (D.par j s) a * a (j+1) s := by
  simp only [IdxDatum.dir]

lemma IdxDatum.dir_one (D : IdxDatum) (l : ℕ) (c : ℤ) (w : D.I 1)
    (a : (j : ℕ) → D.S j → ℤ) :
    D.dir l c 1 w a = ((l : ℤ)) * c * ∑ s ∈ w.val, a 1 s := by
  rw [IdxDatum.dir_succ D l c 0 w a, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have h0 : D.dir l c 0 (D.par 0 s) a = c := by simp only [IdxDatum.dir]
  rw [h0]
  ring

/-- **The direction identity.**  The direction attached by the level-one datum to its level-`1`
index `i` is `2·lc` times the sum of the level-`1` parameters over the set `i1Symm n i` — which is
exactly the leading coefficient of the terminal slot `levelSlot i`. -/
lemma petDir_levelOne (n : ℕ) (lc : ℤ) (a : (levelOneDatum n).Idx 2)
    (i : Fin (Fintype.card ((levelOneDatum n).I 1))) :
    petDir (levelOneDatum n) 2 lc a i = 2 * lc * ∑ s ∈ (i1Symm n i).val, a 1 s := by
  have hsum : ∀ s ∈ (i1Symm n i).val, ((levelOneDatum n).pad 2 a) 1 s = a 1 s := fun s _ => by
    simp [IdxDatum.pad]
  have h1 : petDir (levelOneDatum n) 2 lc a i
      = 2 * lc * ∑ s ∈ (i1Symm n i).val, ((levelOneDatum n).pad 2 a) 1 s := by
    show (levelOneDatum n).dir 2 lc 1 (i1Symm n i) ((levelOneDatum n).pad 2 a) = _
    exact IdxDatum.dir_one (levelOneDatum n) 2 lc (i1Symm n i) ((levelOneDatum n).pad 2 a)
  rw [h1, Finset.sum_congr rfl hsum]

end

end Work.Peluse.UControl
