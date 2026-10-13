/-
  WilE9 / Sharp / ExFst — the two points of the `exSemiPf_fst` construction.

  The *forward* direction of the extended system (`exSemiPf_fst`) has to produce, for a point `w`
  of an effectively smooth stratum whose projection is the `ψ`-image of `(x, f x)`, a point `z` of
  the extended semi-Pfaffian set whose `(y,σ)`-projection is the `ψ`-image of `(x, ∂_L f x)`.

  Two points are involved:

  * `exPt w x sval σ`, the point `z` of the extended ambient `ℝ^{Next n m}`.  Its `y`- and
    `(τ,aux)`-coordinates are those of `w` (so that the stratum's own equations hold there by
    `E.Good`), its `w`-coordinates are `psig (x i)`, its `u`-coordinate `psig sval` (`sval = f x`),
    its `τ`-coordinate is `wTau w = ψ (f x)`, its output is `σ` with `υ = psig σ`;
  * `pbPt z`, the corresponding point of the *pulled-back* ambient `ℝ^{Npb n m}`, obtained from
    `z` by the substitution `x i ↦ z (exY i)/z (exW i)`, `s ↦ z (exT)/z (exU)`: precisely the
    substitution that `clearPb`/`clearNumDen` clear the denominators of.

  The coordinate lemmas below identify the coordinates of `pbPt (exPt w x (f x) σ)` with the
  `pbX/pbS/pbY/pbW/pbT/pbU/pbA` coordinates (assuming the `y`-coordinates of `w` are `ψ (x i)`,
  which is the hypothesis `hbase` of the target).
-/
import Mathlib
import Submission.Work.WilE9.Sharp.Vocab
import Submission.Work.WilE9.Sharp.clearNumDen_eval
import Submission.Work.WilE9.Sharp.eaEval_pbRaise
import Submission.Work.WilE9.Sharp.eaD_pbRaise
import Submission.Work.WilE9.Psi.psi_psig_algebra

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-! ## 1. The `y`, `τ` and `aux` coordinates of a stratum point

A point of the stratum's ambient is `Fin (n + (1 + m)) → ℝ`, with the `n` `y`-coordinates first,
then `τ`, then the `m` auxiliary coordinates.  The three helpers below extract them without
proof obligations in the *statements* of the lemmas. -/

/-- The `y`-coordinates of a stratum point. -/
def wY {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) (i : Fin n) : ℝ :=
  w ⟨i.val, by have := i.isLt; omega⟩

/-- The `τ`-coordinate of a stratum point. -/
def wTau {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) : ℝ := w ⟨n, by omega⟩

/-- The auxiliary coordinates of a stratum point. -/
def wAux {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) (a : Fin m) : ℝ :=
  w ⟨n + 1 + a.val, by have := a.isLt; omega⟩

/-- `stratProj` reads off the `y`-coordinate. -/
theorem stratProj_wY {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) (i : Fin n) :
    stratProj w (Fin.castSucc i) = wY w i := rfl

/-- `stratProj` reads off `τ` at the last coordinate. -/
theorem stratProj_wTau {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) :
    stratProj w (Fin.last n) = wTau w := rfl

/-- The `y`-coordinates of `w` are `ψ (x i)` if the projection of `w` is the `ψ`-image of the
graph of a function taking the value `τ` at `x`. -/
theorem wY_of_hbase {n m : ℕ} {w : Fin (n + (1 + m)) → ℝ} {x : Fin n → ℝ} {τ : ℝ}
    (hbase : stratProj w = Fin.snoc (WilkiesDesign.E.psiV x) τ) (i : Fin n) :
    wY w i = WilkiesDesign.E.psi (x i) := by
  have h := congrFun hbase (Fin.castSucc i)
  rw [Fin.snoc_castSucc] at h
  rw [stratProj_wY] at h
  exact h

/-- The `τ`-coordinate of `w` if the projection of `w` is the `ψ`-image of `(x, τ)`. -/
theorem wTau_of_hbase {n m : ℕ} {w : Fin (n + (1 + m)) → ℝ} {x : Fin n → ℝ} {τ : ℝ}
    (hbase : stratProj w = Fin.snoc (WilkiesDesign.E.psiV x) τ) :
    wTau w = τ := by
  have h := congrFun hbase (Fin.last n)
  rw [Fin.snoc_last] at h
  rw [stratProj_wTau] at h
  exact h

/-! ## 2. Unfolding the substitution maps `sNum`, `sDen`, `sRest` -/

theorem sNum_of_lt {n m : ℕ} {b : Fin (n + 1)} (h : (b : ℕ) < n) :
    sNum n m b = exY n m ⟨(b : ℕ), h⟩ := by
  simp only [sNum, dif_pos h]

theorem sNum_of_not_lt {n m : ℕ} {b : Fin (n + 1)} (h : ¬ (b : ℕ) < n) :
    sNum n m b = exT n m := by
  simp only [sNum, dif_neg h]

theorem sDen_of_lt {n m : ℕ} {b : Fin (n + 1)} (h : (b : ℕ) < n) :
    sDen n m b = exW n m ⟨(b : ℕ), h⟩ := by
  simp only [sDen, dif_pos h]

theorem sDen_of_not_lt {n m : ℕ} {b : Fin (n + 1)} (h : ¬ (b : ℕ) < n) :
    sDen n m b = exU n m := by
  simp only [sDen, dif_neg h]

theorem sRest_of_lt {n m : ℕ} {k : Fin (2 * n + m + 2)} (h : (k : ℕ) < n) :
    sRest n m k = exY n m ⟨(k : ℕ), h⟩ := by
  simp only [sRest, dif_pos h]

theorem sRest_of_lt2 {n m : ℕ} {k : Fin (2 * n + m + 2)} (h1 : ¬ (k : ℕ) < n)
    (h : (k : ℕ) < 2 * n) :
    sRest n m k = exW n m ⟨(k : ℕ) - n, by omega⟩ := by
  simp only [sRest, dif_neg h1, dif_pos h]

theorem sRest_of_eq {n m : ℕ} {k : Fin (2 * n + m + 2)} (h1 : ¬ (k : ℕ) < n)
    (h2 : ¬ (k : ℕ) < 2 * n) (h : (k : ℕ) = 2 * n) : sRest n m k = exT n m := by
  simp only [sRest, dif_neg h1, dif_neg h2, dif_pos h]

theorem sRest_of_eq1 {n m : ℕ} {k : Fin (2 * n + m + 2)} (h1 : ¬ (k : ℕ) < n)
    (h2 : ¬ (k : ℕ) < 2 * n) (h3 : ¬ (k : ℕ) = 2 * n) (h : (k : ℕ) = 2 * n + 1) :
    sRest n m k = exU n m := by
  simp only [sRest, dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h]

theorem sRest_of_aux {n m : ℕ} {k : Fin (2 * n + m + 2)} (h1 : ¬ (k : ℕ) < n)
    (h2 : ¬ (k : ℕ) < 2 * n) (h3 : ¬ (k : ℕ) = 2 * n) (h4 : ¬ (k : ℕ) = 2 * n + 1) :
    sRest n m k = exA n m ⟨(k : ℕ) - (2 * n + 2), by omega⟩ := by
  simp only [sRest, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4]

/-! ## 3. The extended ambient point -/

/-- **The extended ambient point**: `y` and `(τ,aux)` from `w`, `w i = psig (x i)`,
`u = psig sval`, output `σ`, `υ = psig σ`. -/
def exPt {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) (x : Fin n → ℝ) (sval σ : ℝ) :
    Fin (Next n m) → ℝ := fun k =>
  if h1 : (k : ℕ) < n then w ⟨(k : ℕ), by have := k.isLt; simp only [Next] at this; omega⟩
  else if h2 : (k : ℕ) = n then WilkiesDesign.E.psi σ
  else if h3 : (k : ℕ) < 2 * n + 1 then Work.WilE9.psig (x ⟨(k : ℕ) - (n + 1), by omega⟩)
  else if h4 : (k : ℕ) = 2 * n + 1 then Work.WilE9.psig sval
  else if h5 : (k : ℕ) = 2 * n + 2 then w ⟨n, by omega⟩
  else if h6 : (k : ℕ) < 2 * n + 3 + m then
    w ⟨n + 1 + ((k : ℕ) - (2 * n + 3)), by omega⟩
  else Work.WilE9.psig σ

/-- The `y`-coordinate. -/
theorem exPt_exY {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) (x : Fin n → ℝ) (sval σ : ℝ)
    (i : Fin n) : exPt w x sval σ (exY n m i) = wY w i := by
  simp only [exPt]
  rw [dif_pos (show ((exY n m i : ℕ) < n) from by show (i : ℕ) < n; exact i.isLt)]
  rfl

/-- The output coordinate. -/
theorem exPt_exSig {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) (x : Fin n → ℝ) (sval σ : ℝ) :
    exPt w x sval σ (exSig n m) = WilkiesDesign.E.psi σ := by
  simp only [exPt]
  rw [dif_neg (show ¬ (((exSig n m : Fin (Next n m)) : ℕ) < n) from by
      show ¬ (n < n); omega),
    dif_pos (show (((exSig n m : Fin (Next n m)) : ℕ) = n) from rfl)]

/-- The `w`-coordinate. -/
theorem exPt_exW {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) (x : Fin n → ℝ) (sval σ : ℝ)
    (i : Fin n) : exPt w x sval σ (exW n m i) = Work.WilE9.psig (x i) := by
  simp only [exPt]
  rw [dif_neg (show ¬ (((exW n m i : Fin (Next n m)) : ℕ) < n) from by
      show ¬ (n + 1 + (i : ℕ) < n); omega),
    dif_neg (show ¬ (((exW n m i : Fin (Next n m)) : ℕ) = n) from by
      show ¬ (n + 1 + (i : ℕ) = n); omega),
    dif_pos (show (((exW n m i : Fin (Next n m)) : ℕ) < 2 * n + 1) from by
      show n + 1 + (i : ℕ) < 2 * n + 1; have := i.isLt; omega)]
  congr 1
  congr 1
  apply Fin.ext
  show n + 1 + (i : ℕ) - (n + 1) = i.val
  omega

/-- The `u`-coordinate. -/
theorem exPt_exU {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) (x : Fin n → ℝ) (sval σ : ℝ) :
    exPt w x sval σ (exU n m) = Work.WilE9.psig sval := by
  simp only [exPt]
  rw [dif_neg (show ¬ (((exU n m : Fin (Next n m)) : ℕ) < n) from by
      show ¬ (2 * n + 1 < n); omega),
    dif_neg (show ¬ (((exU n m : Fin (Next n m)) : ℕ) = n) from by
      show ¬ (2 * n + 1 = n); omega),
    dif_neg (show ¬ (((exU n m : Fin (Next n m)) : ℕ) < 2 * n + 1) from by
      show ¬ (2 * n + 1 < 2 * n + 1); omega),
    dif_pos (show (((exU n m : Fin (Next n m)) : ℕ) = 2 * n + 1) from rfl)]

/-- The `τ`-coordinate. -/
theorem exPt_exT {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) (x : Fin n → ℝ) (sval σ : ℝ) :
    exPt w x sval σ (exT n m) = wTau w := by
  simp only [exPt]
  rw [dif_neg (show ¬ (((exT n m : Fin (Next n m)) : ℕ) < n) from by
      show ¬ (2 * n + 2 < n); omega),
    dif_neg (show ¬ (((exT n m : Fin (Next n m)) : ℕ) = n) from by
      show ¬ (2 * n + 2 = n); omega),
    dif_neg (show ¬ (((exT n m : Fin (Next n m)) : ℕ) < 2 * n + 1) from by
      show ¬ (2 * n + 2 < 2 * n + 1); omega),
    dif_neg (show ¬ (((exT n m : Fin (Next n m)) : ℕ) = 2 * n + 1) from by
      show ¬ (2 * n + 2 = 2 * n + 1); omega),
    dif_pos (show (((exT n m : Fin (Next n m)) : ℕ) = 2 * n + 2) from rfl)]
  rfl

/-- The auxiliary coordinates. -/
theorem exPt_exA {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) (x : Fin n → ℝ) (sval σ : ℝ)
    (a : Fin m) : exPt w x sval σ (exA n m a) = wAux w a := by
  simp only [exPt]
  rw [dif_neg (show ¬ (((exA n m a : Fin (Next n m)) : ℕ) < n) from by
      show ¬ (2 * n + 3 + (a : ℕ) < n); omega),
    dif_neg (show ¬ (((exA n m a : Fin (Next n m)) : ℕ) = n) from by
      show ¬ (2 * n + 3 + (a : ℕ) = n); omega),
    dif_neg (show ¬ (((exA n m a : Fin (Next n m)) : ℕ) < 2 * n + 1) from by
      show ¬ (2 * n + 3 + (a : ℕ) < 2 * n + 1); omega),
    dif_neg (show ¬ (((exA n m a : Fin (Next n m)) : ℕ) = 2 * n + 1) from by
      show ¬ (2 * n + 3 + (a : ℕ) = 2 * n + 1); omega),
    dif_neg (show ¬ (((exA n m a : Fin (Next n m)) : ℕ) = 2 * n + 2) from by
      show ¬ (2 * n + 3 + (a : ℕ) = 2 * n + 2); omega),
    dif_pos (show (((exA n m a : Fin (Next n m)) : ℕ) < 2 * n + 3 + m) from by
      show 2 * n + 3 + (a : ℕ) < 2 * n + 3 + m; have := a.isLt; omega)]
  congr 1
  apply Fin.ext
  show n + 1 + (2 * n + 3 + (a : ℕ) - (2 * n + 3)) = n + 1 + a.val
  omega

/-- The `υ`-coordinate. -/
theorem exPt_exV {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) (x : Fin n → ℝ) (sval σ : ℝ) :
    exPt w x sval σ (exV n m) = Work.WilE9.psig σ := by
  simp only [exPt]
  rw [dif_neg (show ¬ (((exV n m : Fin (Next n m)) : ℕ) < n) from by
      show ¬ (2 * n + 3 + m < n); omega),
    dif_neg (show ¬ (((exV n m : Fin (Next n m)) : ℕ) = n) from by
      show ¬ (2 * n + 3 + m = n); omega),
    dif_neg (show ¬ (((exV n m : Fin (Next n m)) : ℕ) < 2 * n + 1) from by
      show ¬ (2 * n + 3 + m < 2 * n + 1); omega),
    dif_neg (show ¬ (((exV n m : Fin (Next n m)) : ℕ) = 2 * n + 1) from by
      show ¬ (2 * n + 3 + m = 2 * n + 1); omega),
    dif_neg (show ¬ (((exV n m : Fin (Next n m)) : ℕ) = 2 * n + 2) from by
      show ¬ (2 * n + 3 + m = 2 * n + 2); omega),
    dif_neg (show ¬ (((exV n m : Fin (Next n m)) : ℕ) < 2 * n + 3 + m) from by
      show ¬ (2 * n + 3 + m < 2 * n + 3 + m); omega)]

/-- **The stratum coordinates of the extended point are those of `w`.** -/
theorem exStrat_exPt {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) (x : Fin n → ℝ) (sval σ : ℝ) :
    exStrat (exPt w x sval σ) = w := by
  funext i
  by_cases h1 : (i : ℕ) < n
  · have hs : sIdxE n m i = exY n m ⟨(i : ℕ), h1⟩ := by simp only [sIdxE, dif_pos h1]
    rw [exStrat, hs, exPt_exY]
    exact congrArg w (Fin.ext rfl)
  · by_cases h2 : (i : ℕ) = n
    · have hs : sIdxE n m i = exT n m := by simp only [sIdxE, dif_neg h1, dif_pos h2]
      rw [exStrat, hs, exPt_exT, wTau]
      exact congrArg w (Fin.ext h2.symm)
    · have hs : sIdxE n m i = exA n m ⟨(i : ℕ) - (n + 1), by have hi := i.isLt; omega⟩ := by
        simp only [sIdxE, dif_neg h1, dif_neg h2]
      rw [exStrat, hs, exPt_exA, wAux]
      exact congrArg w (Fin.ext (by show n + 1 + ((i : ℕ) - (n + 1)) = (i : ℕ); omega))

/-- `psig` is bounded by one. -/
theorem abs_psig_le_one (a : ℝ) : |Work.WilE9.psig a| ≤ 1 := by
  rw [abs_of_pos (Work.WilE9.Psi.psig_pos a), Work.WilE9.psig,
    div_le_one (Work.WilE9.Psi.sqrt_one_add_sq_pos a)]
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg a])

/-- The extended point lies in the closed cube as soon as `w` does. -/
theorem exPt_mem_cube {n m : ℕ} {w : Fin (n + (1 + m)) → ℝ} (x : Fin n → ℝ) (sval σ : ℝ)
    (hw : w ∈ cubeC (n + (1 + m))) : exPt w x sval σ ∈ cubeC (Next n m) := by
  intro k
  simp only [exPt]
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact hw _
  · exact psi_abs_le_one σ
  · exact abs_psig_le_one _
  · exact abs_psig_le_one _
  · exact hw _
  · exact hw _
  · exact abs_psig_le_one _

/-! ## 4. The pulled-back point -/

/-- The variable map of `pbEquiv`, on the left summand. -/
theorem pbEquiv_inl {n m : ℕ} {i : Fin (Npb n m)} (h : (i : ℕ) < n + 1) :
    pbEquiv n m i = Sum.inl ⟨(i : ℕ), h⟩ := by
  rw [pbEquiv, Equiv.trans_apply, finCongr_apply]
  rw [Equiv.symm_apply_eq, finSumFinEquiv_apply_left]
  exact Fin.ext rfl

/-- The variable map of `pbEquiv`, on the right summand. -/
theorem pbEquiv_inr {n m : ℕ} {i : Fin (Npb n m)} (h : ¬ (i : ℕ) < n + 1) :
    pbEquiv n m i = Sum.inr ⟨(i : ℕ) - (n + 1),
      by have hi := i.isLt; simp only [Npb, qpb] at hi; omega⟩ := by
  rw [pbEquiv, Equiv.trans_apply, finCongr_apply]
  rw [Equiv.symm_apply_eq, finSumFinEquiv_apply_right]
  apply Fin.ext
  simp only [Fin.val_cast, Fin.val_natAdd]
  omega

/-- **The pulled-back point of `z`**: the substitution `x i ↦ z (exY i)/z (exW i)`,
`s ↦ z (exT)/z (exU)` of the pulled-back system's ambient. -/
def pbPt {n m : ℕ} (z : Fin (Next n m) → ℝ) : Fin (Npb n m) → ℝ := fun i =>
  if h : (i : ℕ) < n + 1 then z (sNum n m ⟨(i : ℕ), h⟩) / z (sDen n m ⟨(i : ℕ), h⟩)
  else z (sRest n m ⟨(i : ℕ) - (n + 1),
    by have hi := i.isLt; simp only [Npb, qpb] at hi; omega⟩)

/-- Restating `pbPt` through the equivalence `pbEquiv`. -/
theorem pbPt_apply_pbEquiv {n m : ℕ} (z : Fin (Next n m) → ℝ) (i : Fin (Npb n m)) :
    pbPt z i = Sum.elim (fun b => z (sNum n m b) / z (sDen n m b)) (fun k => z (sRest n m k))
      (pbEquiv n m i) := by
  rw [pbPt]
  by_cases h : (i : ℕ) < n + 1
  · rw [dif_pos h, pbEquiv_inl h]
    rfl
  · rw [dif_neg h, pbEquiv_inr h]
    rfl

/-- The value of `pbPt` at the `x`/`s`-coordinates. -/
theorem pbPt_at_lt {n m : ℕ} (z : Fin (Next n m) → ℝ) {i : Fin (Npb n m)}
    (h : (i : ℕ) < n + 1) :
    pbPt z i = z (sNum n m ⟨(i : ℕ), h⟩) / z (sDen n m ⟨(i : ℕ), h⟩) := by
  rw [pbPt, dif_pos h]

/-- The value of `pbPt` at the remaining coordinates. -/
theorem pbPt_at_ge {n m : ℕ} (z : Fin (Next n m) → ℝ) {i : Fin (Npb n m)}
    (h : ¬ (i : ℕ) < n + 1) :
    pbPt z i = z (sRest n m ⟨(i : ℕ) - (n + 1),
      by have hi := i.isLt; simp only [Npb, qpb] at hi; omega⟩) := by
  rw [pbPt, dif_neg h]

/-! ## 5. The output of the extended ambient point -/

/-- The output of the extended point is `Fin.snoc (psiV x) (psi σ)`, provided the `y`-coordinates
of `w` are the `ψ`-images of the `x`-coordinates. -/
theorem exOut_exPt {n m : ℕ} {w : Fin (n + (1 + m)) → ℝ} {x : Fin n → ℝ} (sval σ : ℝ)
    (hY : ∀ i : Fin n, wY w i = WilkiesDesign.E.psi (x i)) :
    exOut (exPt w x sval σ) = Fin.snoc (WilkiesDesign.E.psiV x) (WilkiesDesign.E.psi σ) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp only [exOut, projFirst]
    rw [show (Fin.castAdd (n + m + 3) (Fin.last n) : Fin (Next n m)) = exSig n m from Fin.ext rfl]
    rw [exPt_exSig, Fin.snoc_last]
  · intro j
    simp only [exOut, projFirst]
    rw [show (Fin.castAdd (n + m + 3) (Fin.castSucc j) : Fin (Next n m)) = exY n m j from
      Fin.ext rfl]
    rw [exPt_exY, hY j, Fin.snoc_castSucc]
    rfl

end Work.WilE9.Sharp
