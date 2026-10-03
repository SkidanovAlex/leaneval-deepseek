import Mathlib
import Submission.Work.Peluse.UControl.levCubeDefs
import Submission.Work.Peluse.UControl.level1Compare

/-!
# The terminal comparison of the level chain, in the general (`d ≥ 3`) form

This file proves `Work.Peluse.UControl.levelCompareGen` (the statement is repeated verbatim as
`levelCompareGenHolds` here, and the two are the same theorem): the comparison of the terminal state
of the `d ≥ 3` level chain — a `HistData dd L` satisfying `LevCube dd 1 L A f₀ atoms` — with the
datum's `linFamAvg`.

It is the `dd ≥ 3` generalisation of `level1Compare_aux` (`level1Compare.lean`), where the terminal
state *is* the level-`1` datum.  The three ingredients are

* the *reindexing* `islot` of the state's live slots onto `Fin (card (D.I (dd-1)))`, together with
  the evaluation identity `heval` (the paper's `Q_i(t,y) = p_i(a)·y + p'_i(a)`);
* the *independence of the level-`0` direction*: `petDir` depends only on the coordinates `j ≠ 0`
  (`IdxDatum.dir_pad_congr`), which is what allows the average over the window tower
  `Fin (2H+1) × WinTower H L` to be dominated by the average over the parameter box;
* the weight bound `ν ≤ (3/(2H+1))^L` (`nu_le_three_lv`, valid also for `H = 0`), which turns the
  `ν`-weighted tower sum into `(2H+1)^{-L}` times the unweighted one.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The flag of a slot function, and the Boolean family of `linFamAvg` -/

/-- The flag telling whether the slot function `G i` is `Ftop` or its conjugate. -/
def lvFlag {dd L : ℕ} {Y : HistData dd L} (Ftop : ℤ → ℂ) (G : (Y.toSym).S.ι → ℤ → ℂ)
    (i : (Y.toSym).S.ι) : Bool := if ∀ x, G i x = Ftop x then false else true

lemma lvFlag_spec {dd L : ℕ} {Y : HistData dd L} (Ftop : ℤ → ℂ) (G : (Y.toSym).S.ι → ℤ → ℂ)
    (htop : ∀ i, (∀ x, G i x = Ftop x) ∨ (∀ x, G i x = star (Ftop x)))
    (i : (Y.toSym).S.ι) (z : ℤ) :
    G i z = if lvFlag Ftop G i then star (Ftop z) else Ftop z := by
  by_cases h : ∀ x, G i x = Ftop x
  · simp [lvFlag, h]
  · have h2 : ∀ x, G i x = star (Ftop x) := (htop i).resolve_left h
    simp [lvFlag, h, h2 z]

/-- The Boolean family of `linFamAvg`: the flag of the slot `islot.symm j`, flipped when the base
function `g` is the conjugate of `Ftop`. -/
def lvB {dd L : ℕ} (D : IdxDatum) {Y : HistData dd L} (c₀ : Bool) (Ftop : ℤ → ℂ)
    (G : (Y.toSym).S.ι → ℤ → ℂ)
    (islot : (Y.toSym).S.ι ≃ Fin (Fintype.card (D.I (dd - 1)))) :
    Fin (Fintype.card (D.I (dd - 1))) → Bool :=
  fun j => if c₀ then !(lvFlag Ftop G (islot.symm j)) else lvFlag Ftop G (islot.symm j)

@[simp] lemma lvB_false {dd L : ℕ} (D : IdxDatum) {Y : HistData dd L} (Ftop : ℤ → ℂ)
    (G : (Y.toSym).S.ι → ℤ → ℂ)
    (islot : (Y.toSym).S.ι ≃ Fin (Fintype.card (D.I (dd - 1)))) :
    lvB D false Ftop G islot = fun j => lvFlag Ftop G (islot.symm j) := by
  funext j; simp [lvB]

@[simp] lemma lvB_true {dd L : ℕ} (D : IdxDatum) {Y : HistData dd L} (Ftop : ℤ → ℂ)
    (G : (Y.toSym).S.ι → ℤ → ℂ)
    (islot : (Y.toSym).S.ι ≃ Fin (Fintype.card (D.I (dd - 1)))) :
    lvB D true Ftop G islot = fun j => !(lvFlag Ftop G (islot.symm j)) := by
  funext j; simp [lvB]

/-! ## The correlation of the history state -/

/-- The correlation of the history state `Y` at the tower point `t`: the inner expression of
`(histPet Y H G g).lam`, of which `lam` takes the `ν`-average of the moduli.  (It is written with
`Y.Q i.1.1 i.1.2`, the polynomial of the slot `i`, rather than with the projection
`(Y.toSym).S.P i`, so that the `ℤ`-indexed parameter `WinTower.param H L t` has the right type by
reduction.) -/
def lvCorr {dd L : ℕ} (H N M : ℕ) (Y : HistData dd L)
    (G : (Y.toSym).S.ι → ℤ → ℂ) (g : WinTower H L → ℤ → ℂ) (t : WinTower H L) : ℂ :=
  ((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, g t x *
    ∑ y ∈ Finset.Icc 1 M, ∏ i : (Y.toSym).S.ι,
      G i (x + ((Y.Q i.1.1 i.1.2).map
        (MvPolynomial.eval (WinTower.param H L t))).eval (y : ℤ))

/-- The state's `lam` is the `ν`-average of the moduli of the correlations. -/
lemma lvLam_eq {dd L : ℕ} (H N M : ℕ) (Y : HistData dd L)
    (G : (Y.toSym).S.ι → ℤ → ℂ) (g : WinTower H L → ℤ → ℂ) :
    (histPet Y H G g).toState.lam N M
      = ∑ t : WinTower H L, WinTower.nu H L t * ‖lvCorr H N M Y G g t‖ := by
  rw [PetStep.PetStateP.lam_eq]
  rfl

/-- The conjugate of the correlation, in the form in which the `c₀ = true` case of the comparison
is proved. -/
lemma star_lvCorr {dd L : ℕ} (H N M : ℕ) (Y : HistData dd L)
    (G : (Y.toSym).S.ι → ℤ → ℂ) (g : WinTower H L → ℤ → ℂ) (t : WinTower H L) :
    star (lvCorr H N M Y G g t)
      = ((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, star (g t x) *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : (Y.toSym).S.ι,
            star (G i (x + ((Y.Q i.1.1 i.1.2).map
              (MvPolynomial.eval (WinTower.param H L t))).eval (y : ℤ))) := by
  have hterm : ∀ x : ℤ,
      star (g t x * (∑ y ∈ Finset.Icc 1 M, ∏ i : (Y.toSym).S.ι,
        G i (x + ((Y.Q i.1.1 i.1.2).map
          (MvPolynomial.eval (WinTower.param H L t))).eval (y : ℤ))))
      = star (g t x) * (∑ y ∈ Finset.Icc 1 M, ∏ i : (Y.toSym).S.ι,
        star (G i (x + ((Y.Q i.1.1 i.1.2).map
          (MvPolynomial.eval (WinTower.param H L t))).eval (y : ℤ)))) := by
    intro x
    rw [star_mul', star_sum]
    refine congrArg (fun z => star (g t x) * z) ?_
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [star_prod]
  unfold lvCorr
  rw [star_mul', tsum_star]
  rw [show star (((N : ℂ) * (M : ℂ))⁻¹) = ((N : ℂ) * (M : ℂ))⁻¹ from by simp]
  rw [tsum_congr hterm]

/-- **The comparison of the correlations.**  The modulus of the state's correlation at the tower
point `t` is the modulus of `linCore` at the parameter family `towerIdx (0,t)`, with the Boolean
family `lvB` and the constant family `β' a i = β a (islot.symm i)`. -/
lemma lvCorr_eq_linCore {dd L : ℕ} (H N M : ℕ) (D : IdxDatum) (lc : ℤ) (Y : HistData dd L)
    (Ftop : ℤ → ℂ) (G : (Y.toSym).S.ι → ℤ → ℂ) (g : WinTower H L → ℤ → ℂ) (c₀ : Bool)
    (htop : ∀ i, (∀ x, G i x = Ftop x) ∨ (∀ x, G i x = star (Ftop x)))
    (hg : ∀ a x, g a x = (if c₀ then star (Ftop x) else Ftop x))
    (islot : (Y.toSym).S.ι ≃ Fin (Fintype.card (D.I (dd - 1))))
    (β : ((j : Fin dd) → D.S j → ℤ) → (Y.toSym).S.ι → ℤ)
    (towerIdx : Fin (2 * H + 1) × WinTower H L → ((j : Fin dd) → D.S j → ℤ))
    (heval : ∀ (i : (Y.toSym).S.ι) (t : WinTower H L) (y : ℤ),
      ((Polynomial.map (MvPolynomial.eval (WinTower.param H L t)) (Y.Q i.1.1 i.1.2)).eval y)
        = petDir D dd lc (towerIdx (0, t)) (islot i) * y + β (towerIdx (0, t)) i)
    (t : WinTower H L) :
    lvCorr H N M Y G g t
        = linCore D dd lc N M Ftop (lvB D c₀ Ftop G islot) (fun a i => β a (islot.symm i))
            (towerIdx (0, t))
      ∨ star (lvCorr H N M Y G g t)
        = linCore D dd lc N M Ftop (lvB D c₀ Ftop G islot) (fun a i => β a (islot.symm i))
            (towerIdx (0, t)) := by
  cases c₀ with
  | false =>
    left
    have hgx : ∀ x, g t x = Ftop x := fun x => by simpa using hg t x
    unfold lvCorr linCore
    simp only [lvB_false]
    refine congrArg (fun z => ((N : ℂ) * (M : ℂ))⁻¹ * z) ?_
    refine tsum_congr (fun x => ?_)
    rw [hgx x]
    refine congrArg (fun z => Ftop x * z) ?_
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [Fintype.prod_equiv islot
      (fun i : (Y.toSym).S.ι => G i (x + ((Y.Q i.1.1 i.1.2).map
        (MvPolynomial.eval (WinTower.param H L t))).eval (y : ℤ)))
      (fun j : Fin (Fintype.card (D.I (dd - 1))) =>
        G (islot.symm j) (x + ((Y.Q (islot.symm j).1.1 (islot.symm j).1.2).map
          (MvPolynomial.eval (WinTower.param H L t))).eval (y : ℤ)))
      (fun i => by simp)]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [lvFlag_spec Ftop G htop (islot.symm j) (x + ((Y.Q (islot.symm j).1.1
        (islot.symm j).1.2).map (MvPolynomial.eval (WinTower.param H L t))).eval (y : ℤ))]
    rw [heval (islot.symm j) t y, Equiv.apply_symm_apply]
  | true =>
    right
    have hgx : ∀ x, star (g t x) = Ftop x := fun x => by rw [hg t x]; simp
    rw [star_lvCorr]
    unfold linCore
    simp only [lvB_true]
    refine congrArg (fun z => ((N : ℂ) * (M : ℂ))⁻¹ * z) ?_
    refine tsum_congr (fun x => ?_)
    rw [hgx x]
    refine congrArg (fun z => Ftop x * z) ?_
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [Fintype.prod_equiv islot
      (fun i : (Y.toSym).S.ι => star (G i (x + ((Y.Q i.1.1 i.1.2).map
        (MvPolynomial.eval (WinTower.param H L t))).eval (y : ℤ))))
      (fun j : Fin (Fintype.card (D.I (dd - 1))) =>
        star (G (islot.symm j) (x + ((Y.Q (islot.symm j).1.1 (islot.symm j).1.2).map
          (MvPolynomial.eval (WinTower.param H L t))).eval (y : ℤ))))
      (fun i => by simp)]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [lvFlag_spec Ftop G htop (islot.symm j) (x + ((Y.Q (islot.symm j).1.1
        (islot.symm j).1.2).map (MvPolynomial.eval (WinTower.param H L t))).eval (y : ℤ)),
      star_ite, heval (islot.symm j) t y, Equiv.apply_symm_apply]

/-! ## The independence of the level-`0` coordinate -/

lemma lv_fin_ne_zero_iff {d : ℕ} (hdd : 0 < d) {j : Fin d} :
    j ≠ ⟨0, hdd⟩ ↔ (j : ℕ) ≠ 0 := by
  constructor
  · intro h hj; exact h (Fin.ext hj)
  · intro h hj; exact h (by rw [hj])

/-- **The level-`0` coordinate is invisible to `dir`.**  The recursion `A_j` reads only the
parameters of the levels `1,…,j`. -/
lemma IdxDatum.dir_pad_congr (D : IdxDatum) (l : ℕ) (c : ℤ) {a a' : D.Idx l}
    (h : ∀ j : Fin l, (j : ℕ) ≠ 0 → a j = a' j) :
    ∀ (k : ℕ) (w : D.I k), D.dir l c k w (D.pad l a) = D.dir l c k w (D.pad l a') := by
  intro k
  induction k with
  | zero => intro w; rfl
  | succ k ih =>
    intro w
    rw [IdxDatum.dir_succ, IdxDatum.dir_succ]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have hdir := ih (D.par k s)
    have hpad : (D.pad l a) (k + 1) s = (D.pad l a') (k + 1) s := by
      simp only [IdxDatum.pad]
      by_cases hk : k + 1 < l
      · rw [dif_pos hk, dif_pos hk]
        exact congrFun (h ⟨k + 1, hk⟩ (by simp)) s
      · rw [dif_neg hk, dif_neg hk]
    rw [hdir, hpad]

/-- The direction `petDir` is unchanged by modifying the level-`0` parameter. -/
lemma petDir_lv_congr {dd : ℕ} (D : IdxDatum) (lc : ℤ) {a a' : D.Idx dd}
    (h : ∀ j : Fin dd, (j : ℕ) ≠ 0 → a j = a' j)
    (i : Fin (Fintype.card (D.I (dd - 1)))) :
    petDir D dd lc a i = petDir D dd lc a' i := by
  unfold petDir
  exact IdxDatum.dir_pad_congr D dd lc h (dd - 1) _

/-- `linCore` is unchanged by modifying the level-`0` parameter, provided `β` is. -/
lemma linCore_lv_indep {dd : ℕ} (D : IdxDatum) (lc : ℤ) (N M : ℕ) (Ftop : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (dd - 1))) → Bool)
    (β : D.Idx dd → Fin (Fintype.card (D.I (dd - 1))) → ℤ)
    (hβ : ∀ a a' : D.Idx dd, (∀ j : Fin dd, (j : ℕ) ≠ 0 → a j = a' j) → ∀ i, β a i = β a' i)
    {a a' : D.Idx dd} (h : ∀ j : Fin dd, (j : ℕ) ≠ 0 → a j = a' j) :
    linCore D dd lc N M Ftop b β a = linCore D dd lc N M Ftop b β a' := by
  unfold linCore
  refine congrArg (fun z => ((N : ℂ) * (M : ℂ))⁻¹ * z) ?_
  refine tsum_congr (fun x => ?_)
  refine congrArg (fun z => Ftop x * z) ?_
  refine Finset.sum_congr rfl (fun y _ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [petDir_lv_congr D lc h i, hβ a a' h i]

/-! ## The weight bound -/

lemma muL_zero (x : ℤ) : Work.Peluse.muL 0 x = 0 := by
  simp [Work.Peluse.muL]

lemma nu_zero_of_pos {L : ℕ} (hL : 0 < L) (t : WinTower 0 L) : WinTower.nu 0 L t = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  rw [WinTower.nu, muL_zero, mul_zero]

/-- The window weight is at most `(3/(2H+1))^L`, for every `H` (including `H = 0`, where both
sides vanish for `L ≥ 1`). -/
lemma nu_le_three_lv (H L : ℕ) (t : WinTower H L) :
    WinTower.nu H L t ≤ (3 : ℝ) ^ L / (2 * (H : ℝ) + 1) ^ L := by
  rcases eq_or_ne H 0 with rfl | hH
  · rcases eq_or_ne L 0 with rfl | hL
    · simp [WinTower.nu]
    · rw [nu_zero_of_pos (Nat.pos_of_ne_zero hL) t]
      positivity
  · exact nu_le_three H (Nat.one_le_iff_ne_zero.mpr hH) L t

/-! ## The parameter box dominates the tower sum -/

/-- A canonical point of the window tower (needed only to know that the parameter box is
nonempty). -/
def winTowerZero (H : ℕ) : ∀ L, WinTower H L
  | 0 => (0 : Fin 1)
  | (L + 1) => (winTowerZero H L, ⟨0, by omega⟩)

/-- **The parameter box dominates `(2H+1)` copies of the tower sum.** -/
lemma sum_parBox_ge_lv {dd L : ℕ} (hdd : 0 < dd) (H : ℕ) (D : IdxDatum) (lc : ℤ) (N M : ℕ)
    (Ftop : ℤ → ℂ) (b : Fin (Fintype.card (D.I (dd - 1))) → Bool)
    (β : D.Idx dd → Fin (Fintype.card (D.I (dd - 1))) → ℤ)
    (hβ : ∀ a a' : D.Idx dd, (∀ j : Fin dd, j ≠ ⟨0, hdd⟩ → a j = a' j) → ∀ i, β a i = β a' i)
    (towerIdx : Fin (2 * H + 1) × WinTower H L → D.Idx dd)
    (htower_indep : ∀ (k k' : Fin (2 * H + 1)) (t : WinTower H L),
      ∀ j : Fin dd, j ≠ ⟨0, hdd⟩ → towerIdx (k, t) j = towerIdx (k', t) j)
    (htower_mem : ∀ p : Fin (2 * H + 1) × WinTower H L, towerIdx p ∈ D.parBox dd H)
    (htower_inj : Function.Injective towerIdx) :
    (2 * (H : ℝ) + 1) * ∑ t : WinTower H L,
        ‖linCore D dd lc N M Ftop b β (towerIdx (0, t))‖
      ≤ ∑ a ∈ D.parBox dd H, ‖linCore D dd lc N M Ftop b β a‖ := by
  classical
  have hsub : Finset.univ.image towerIdx ⊆ D.parBox dd H := by
    intro a ha
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp ha
    exact htower_mem p
  have hstep1 : ∑ a ∈ Finset.univ.image towerIdx, ‖linCore D dd lc N M Ftop b β a‖
      ≤ ∑ a ∈ D.parBox dd H, ‖linCore D dd lc N M Ftop b β a‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => norm_nonneg _)
  have hsum_image : (∑ a ∈ Finset.univ.image towerIdx, ‖linCore D dd lc N M Ftop b β a‖)
      = ∑ p : Fin (2 * H + 1) × WinTower H L,
          ‖linCore D dd lc N M Ftop b β (towerIdx p)‖ :=
    Finset.sum_image (f := fun a : D.Idx dd => ‖linCore D dd lc N M Ftop b β a‖)
      (s := (Finset.univ : Finset (Fin (2 * H + 1) × WinTower H L)))
      (g := towerIdx) (fun x _ y _ hxy => htower_inj hxy)
  have hprod : (∑ p : Fin (2 * H + 1) × WinTower H L,
        ‖linCore D dd lc N M Ftop b β (towerIdx p)‖)
      = ∑ k : Fin (2 * H + 1), ∑ t : WinTower H L,
          ‖linCore D dd lc N M Ftop b β (towerIdx (k, t))‖ :=
    Fintype.sum_prod_type _
  have hindep : ∀ k : Fin (2 * H + 1), (∑ t : WinTower H L,
        ‖linCore D dd lc N M Ftop b β (towerIdx (k, t))‖)
      = ∑ t : WinTower H L,
          ‖linCore D dd lc N M Ftop b β (towerIdx (0, t))‖ := by
    intro k
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [linCore_lv_indep D lc N M Ftop b β
      (fun a a' hh i => hβ a a' (fun j hj => hh j ((lv_fin_ne_zero_iff hdd).mp hj)) i)
      (fun j hj => htower_indep k 0 t j ((lv_fin_ne_zero_iff hdd).mpr hj))]
  have hconst : (∑ _k : Fin (2 * H + 1), (∑ t : WinTower H L,
        ‖linCore D dd lc N M Ftop b β (towerIdx (0, t))‖))
      = (2 * (H : ℝ) + 1) * ∑ t : WinTower H L,
          ‖linCore D dd lc N M Ftop b β (towerIdx (0, t))‖ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  calc (2 * (H : ℝ) + 1) * ∑ t : WinTower H L,
        ‖linCore D dd lc N M Ftop b β (towerIdx (0, t))‖
      = ∑ _k : Fin (2 * H + 1), ∑ t : WinTower H L,
          ‖linCore D dd lc N M Ftop b β (towerIdx (0, t))‖ := hconst.symm
    _ = ∑ k : Fin (2 * H + 1), ∑ t : WinTower H L,
          ‖linCore D dd lc N M Ftop b β (towerIdx (k, t))‖ :=
        Finset.sum_congr rfl (fun k _ => (hindep k).symm)
    _ = ∑ p : Fin (2 * H + 1) × WinTower H L,
          ‖linCore D dd lc N M Ftop b β (towerIdx p)‖ := hprod.symm
    _ = ∑ a ∈ Finset.univ.image towerIdx, ‖linCore D dd lc N M Ftop b β a‖ := hsum_image.symm
    _ ≤ ∑ a ∈ D.parBox dd H, ‖linCore D dd lc N M Ftop b β a‖ := hstep1

/-- The shift bound of the history state, in the form of the slot polynomials of `Y`. -/
lemma histPet_SB_apply {dd L : ℕ} (Y : HistData dd L) (H N M c Dsb : ℕ)
    (G : (Y.toSym).S.ι → ℤ → ℂ) (g : WinTower H L → ℤ → ℂ)
    (hSB : (histPet Y H G g).toState.ShiftBound N M c Dsb)
    (i : (Y.toSym).S.ι) (t : WinTower H L) (z : ℤ) (hz : |z| ≤ (c : ℤ) * (M : ℤ)) :
    |((Y.Q i.1.1 i.1.2).map (MvPolynomial.eval (WinTower.param H L t))).eval z|
      ≤ (Dsb : ℤ) * (N : ℤ) :=
  hSB i t z hz

/-! ## The comparison theorem -/

theorem levelCompareGenHolds {dd L : Nat} (hdd : 0 < dd) (H : Nat)
    (D : Work.Peluse.UControl.IdxDatum) (lc : Int)
    (A : Finset (Fin L)) (f0 : Fin L -> Bool)
    (atoms : {x : Fin L // x ∈ A} -> MvPolynomial (Fin L) Int)
    (Y : Work.Peluse.UControl.HistData dd L)
    (hY : Work.Peluse.UControl.LevCube dd 1 L A f0 atoms Y)
    (towerIdx : Fin (2 * H + 1) × Work.Peluse.UControl.WinTower H L ->
      ((j : Fin dd) -> D.S j -> Int))
    (htower0 : ∀ p : Fin (2 * H + 1) × Work.Peluse.UControl.WinTower H L,
      towerIdx p ⟨0, hdd⟩ = fun _ => Work.Peluse.UControl.IdxDatum.boxVal H p.1)
    (htower_indep : ∀ (k k' : Fin (2 * H + 1)) (t : Work.Peluse.UControl.WinTower H L),
      ∀ j : Fin dd, j ≠ ⟨0, hdd⟩ → towerIdx (k, t) j = towerIdx (k', t) j)
    (htower_mem : ∀ p : Fin (2 * H + 1) × Work.Peluse.UControl.WinTower H L,
      towerIdx p ∈ D.parBox dd H)
    (htower_surj : ∀ a ∈ D.parBox dd H, ∃ p : Fin (2 * H + 1) ×
      Work.Peluse.UControl.WinTower H L, towerIdx p = a)
    (htower_inj : Function.Injective towerIdx)
    (hcard : (D.parBox dd H).card ≤ (2 * H + 1) ^ (L + 1))
    (N M : Nat) (Ftop : Int -> Complex) (G : (Y.toSym).S.ι -> Int -> Complex)
    (g : Work.Peluse.UControl.WinTower H L -> Int -> Complex)
    (htop : ∀ i : (Y.toSym).S.ι, (∀ x, G i x = Ftop x) ∨ (∀ x, G i x = star (Ftop x)))
    (hg : ∃ c0 : Bool, ∀ a x, g a x = (if c0 then star (Ftop x) else Ftop x))
    (islot : (Y.toSym).S.ι ≃ Fin (Fintype.card (D.I (dd - 1))))
    (β : ((j : Fin dd) -> D.S j -> Int) -> (Y.toSym).S.ι -> Int)
    (hβ0 : ∀ a a' : (j : Fin dd) -> D.S j -> Int,
      (∀ (j : Fin dd), j ≠ ⟨0, hdd⟩ → a j = a' j) → ∀ i : (Y.toSym).S.ι, β a i = β a' i)
    (heval : ∀ (i : (Y.toSym).S.ι) (t : Work.Peluse.UControl.WinTower H L) (y : Int),
      ((Polynomial.map (MvPolynomial.eval (Work.Peluse.UControl.WinTower.param H L t))
          (Y.Q i.1.1 i.1.2)).eval y)
        = Work.Peluse.UControl.petDir D dd lc (towerIdx (0, t)) (islot i) * y
            + β (towerIdx (0, t)) i)
    {c Dsb : Nat} (hSB : (Work.Peluse.UControl.histPet Y H G g).toState.ShiftBound N M c Dsb)
    (hc : 1 ≤ c) {B : Real}
    (hlam : B ≤ (Work.Peluse.UControl.histPet Y H G g).toState.lam N M) :
    ∃ b : Fin (Fintype.card (D.I (dd - 1))) -> Bool,
      (∀ a ∈ D.parBox dd H, ∀ i : Fin (Fintype.card (D.I (dd - 1))),
          ∀ y ∈ Finset.Icc 1 M,
        |Work.Peluse.UControl.petDir D dd lc a i * (y : Int) + β a (islot.symm i)|
          ≤ (Dsb : Int) * (N : Int)) ∧
      B ≤ (3 : Real) ^ L * Work.Peluse.UControl.linFamAvg D dd lc N M H Ftop b
        (fun a i => β a (islot.symm i)) := by
  classical
  obtain ⟨c₀, hg₀⟩ := hg
  refine ⟨lvB D c₀ Ftop G islot, ?hshift, ?havg⟩
  · intro a ha i y hy
    obtain ⟨⟨k, t⟩, hp⟩ := htower_surj a ha
    have hdir : petDir D dd lc a i = petDir D dd lc (towerIdx (0, t)) i := by
      rw [← hp]
      exact petDir_lv_congr D lc
        (fun j hj => htower_indep k 0 t j ((lv_fin_ne_zero_iff hdd).mpr hj)) i
    have hbeta : β a (islot.symm i) = β (towerIdx (0, t)) (islot.symm i) := by
      rw [← hp]
      exact hβ0 (towerIdx (k, t)) (towerIdx (0, t))
        (fun j hj => htower_indep k 0 t j hj) (islot.symm i)
    rw [hdir, hbeta]
    have hy1 : (1 : ℤ) ≤ (y : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp hy).1
    have hy2 : (y : ℤ) ≤ (M : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp hy).2
    have hz : |(y : ℤ)| ≤ (c : ℤ) * (M : ℤ) := by
      rw [abs_of_nonneg (by omega)]
      have hc1 : (1 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc
      have hM0 : (0 : ℤ) ≤ (M : ℤ) := by omega
      nlinarith
    have hb := histPet_SB_apply Y H N M c Dsb G g hSB (islot.symm i) t (y : ℤ) hz
    rw [heval (islot.symm i) t (y : ℤ), Equiv.apply_symm_apply] at hb
    simpa using hb
  · have hlam' : B ≤ ∑ t : WinTower H L, WinTower.nu H L t * ‖lvCorr H N M Y G g t‖ := by
      rw [lvLam_eq H N M Y G g] at hlam
      exact hlam
    have hX : ∀ t : WinTower H L, ‖lvCorr H N M Y G g t‖
        = ‖linCore D dd lc N M Ftop (lvB D c₀ Ftop G islot)
            (fun a i => β a (islot.symm i)) (towerIdx (0, t))‖ := by
      intro t
      rcases lvCorr_eq_linCore H N M D lc Y Ftop G g c₀ htop hg₀ islot β towerIdx heval t
        with h | h
      · rw [h]
      · rw [← h, norm_star]
    have hstep2 : (∑ t : WinTower H L, WinTower.nu H L t * ‖lvCorr H N M Y G g t‖)
        ≤ ((3 : ℝ) ^ L / (2 * (H : ℝ) + 1) ^ L) *
            ∑ t : WinTower H L, ‖lvCorr H N M Y G g t‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun t _ => ?_)
      exact mul_le_mul_of_nonneg_right (nu_le_three_lv H L t) (norm_nonneg _)
    have hstep3 : (∑ t : WinTower H L, ‖lvCorr H N M Y G g t‖)
        = ∑ t : WinTower H L, ‖linCore D dd lc N M Ftop (lvB D c₀ Ftop G islot)
              (fun a i => β a (islot.symm i)) (towerIdx (0, t))‖ :=
      Finset.sum_congr rfl (fun t _ => hX t)
    have hpar := sum_parBox_ge_lv hdd H D lc N M Ftop (lvB D c₀ Ftop G islot)
      (fun a i => β a (islot.symm i))
      (fun a a' h i => hβ0 a a' h (islot.symm i))
      towerIdx htower_indep htower_mem htower_inj
    have hcard_pos : (0 : ℝ) < (((D.parBox dd H).card : ℕ) : ℝ) := by
      have hmem : towerIdx (0, winTowerZero H L) ∈ D.parBox dd H := htower_mem _
      have : 0 < (D.parBox dd H).card := Finset.card_pos.mpr ⟨_, hmem⟩
      exact_mod_cast this
    have hcard_le : (((D.parBox dd H).card : ℕ) : ℝ) ≤ (2 * (H : ℝ) + 1) ^ (L + 1) := by
      have hcast : ((((2 * H + 1) ^ (L + 1) : ℕ) : ℝ)) = (2 * (H : ℝ) + 1) ^ (L + 1) := by
        push_cast
        ring
      rw [← hcast]
      exact_mod_cast hcard
    have hinv : ((2 * (H : ℝ) + 1) ^ (L + 1))⁻¹
        ≤ ((((D.parBox dd H).card : ℕ) : ℝ))⁻¹ := by
      simpa using one_div_le_one_div_of_le hcard_pos hcard_le
    have hlin : linFamAvg D dd lc N M H Ftop (lvB D c₀ Ftop G islot)
          (fun a i => β a (islot.symm i))
        = ((((D.parBox dd H).card : ℕ) : ℝ))⁻¹ *
            ∑ a ∈ D.parBox dd H, ‖linCore D dd lc N M Ftop (lvB D c₀ Ftop G islot)
              (fun a i => β a (islot.symm i)) a‖ :=
      linFamAvg_eq_card_mul_sum D dd lc N M H Ftop (lvB D c₀ Ftop G islot)
        (fun a i => β a (islot.symm i))
    have hlast : (3 : ℝ) ^ L / (2 * (H : ℝ) + 1) ^ L *
          ∑ t : WinTower H L, ‖linCore D dd lc N M Ftop (lvB D c₀ Ftop G islot)
                (fun a i => β a (islot.symm i)) (towerIdx (0, t))‖
        ≤ (3 : ℝ) ^ L * linFamAvg D dd lc N M H Ftop (lvB D c₀ Ftop G islot)
            (fun a i => β a (islot.symm i)) := by
      rw [hlin]
      have hSnn : (0 : ℝ) ≤ ∑ a ∈ D.parBox dd H,
          ‖linCore D dd lc N M Ftop (lvB D c₀ Ftop G islot)
            (fun a i => β a (islot.symm i)) a‖ :=
        Finset.sum_nonneg (fun a _ => norm_nonneg _)
      have hstepA : (3 : ℝ) ^ L / (2 * (H : ℝ) + 1) ^ L *
            ∑ t : WinTower H L, ‖linCore D dd lc N M Ftop (lvB D c₀ Ftop G islot)
                  (fun a i => β a (islot.symm i)) (towerIdx (0, t))‖
          = (3 : ℝ) ^ L * ((2 * (H : ℝ) + 1) ^ (L + 1))⁻¹ *
              ((2 * (H : ℝ) + 1) * ∑ t : WinTower H L,
                ‖linCore D dd lc N M Ftop (lvB D c₀ Ftop G islot)
                  (fun a i => β a (islot.symm i)) (towerIdx (0, t))‖) := by
        rw [pow_succ]
        field_simp
      rw [hstepA]
      refine le_trans (mul_le_mul_of_nonneg_left hpar (by positivity)) ?_
      refine le_trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv (by positivity)) hSnn) ?_
      rw [mul_assoc]
    calc B ≤ ∑ t : WinTower H L, WinTower.nu H L t * ‖lvCorr H N M Y G g t‖ := hlam'
      _ ≤ ((3 : ℝ) ^ L / (2 * (H : ℝ) + 1) ^ L) *
            ∑ t : WinTower H L, ‖lvCorr H N M Y G g t‖ := hstep2
      _ = ((3 : ℝ) ^ L / (2 * (H : ℝ) + 1) ^ L) *
            ∑ t : WinTower H L, ‖linCore D dd lc N M Ftop (lvB D c₀ Ftop G islot)
                  (fun a i => β a (islot.symm i)) (towerIdx (0, t))‖ := by rw [hstep3]
      _ ≤ (3 : ℝ) ^ L * linFamAvg D dd lc N M H Ftop (lvB D c₀ Ftop G islot)
            (fun a i => β a (islot.symm i)) := hlast

end

end Work.Peluse.UControl
