/-
  WilE9 / Sharp — the reconstruction map from the extended ambient to the pulled-back ambient.

  A point `z` of the extended ambient `ℝ^{Next n m}` carries the coordinates

  * `y i = z (exY i)`, `σ = z (exSig)`, `w i = z (exW i)`, `u = z (exU)`, `τ = z (exT)`,
    `aux a = z (exA a)`, `υ = z (exV)`;

  and the equations of the extended system are the equations of the *pulled-back* system
  `pbF` with the substitution `x i ↦ y i / w i`, `s ↦ τ / u` (cleared).  This file defines the
  point of the pulled-back ambient that the substitution produces,

      `exSub z : Fin (Npb n m) → ℝ`,

  by reading it through the coordinate identification `pbEquiv` used by `clearPb`: on the block
  `(x, s)` it is `(y i / w i, τ / u)` (i.e. `psiInv` of the corresponding ψ-coordinate, since
  `w i = psig (psiInv (y i))` on the good locus), and on the block `(y, w, τ, u, aux)` it is `z`
  itself read at the corresponding extended coordinate.

  The two facts proved here and used by the rest of the development are

  * `pbStrat (exSub z) = exStrat z` — reading the reconstructed point in the stratum's own
    coordinates gives back the stratum coordinates of `z`, so the stratum's equations of the
    pulled-back system are exactly the ones of the extended system;
  * `exSub_eq_append` — with the split of the ambient of the implicit function theorem
    (base `x`, fibre `(s,y,w,τ,u,aux)`), `exSub z` is `Fin.append` of its two blocks.

  The clearing identity relating `eaEval (exChain c) (clearPb …) z` to
  `eaEval (pbChain c) … (exSub z)` is `Work.WilE9.Sharp.clearPb_eval`.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.Vocab

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-! ## The coordinate identification `pbEquiv` at the named coordinates -/

lemma finSumFinEquiv_symm_of_lt {m n : ℕ} (k : Fin (m+n)) (h : k.val < m) :
    finSumFinEquiv.symm k = Sum.inl (⟨k.val, h⟩ : Fin m) := by
  change Fin.addCases Sum.inl Sum.inr (Fin.castAdd n (⟨k.val, h⟩ : Fin m))
    = Sum.inl (⟨k.val, h⟩ : Fin m)
  rw [Fin.addCases_left]

lemma finSumFinEquiv_symm_of_le {m n : ℕ} (k : Fin (m+n)) (h : m ≤ k.val) :
    finSumFinEquiv.symm k = Sum.inr (⟨k.val - m, by omega⟩ : Fin n) := by
  have hk : k = Fin.natAdd m (⟨k.val - m, by omega⟩ : Fin n) :=
    Fin.ext (by simp only [Fin.natAdd]; omega)
  conv_lhs => rw [hk]
  rw [finSumFinEquiv_symm_apply_natAdd]

lemma pbEquiv_val_lt {n m : ℕ} (l : Fin (Npb n m)) (h : l.val < n+1) :
    pbEquiv n m l = Sum.inl (⟨l.val, h⟩ : Fin (n+1)) := by
  simp only [pbEquiv, Equiv.trans_apply]
  rw [finSumFinEquiv_symm_of_lt _ (by rw [finCongr_apply_coe]; exact h)]
  simp only [finCongr_apply_coe]

lemma pbEquiv_val_le {n m : ℕ} (l : Fin (Npb n m)) (h : n+1 ≤ l.val) :
    pbEquiv n m l =
      Sum.inr (⟨l.val - (n+1), by simp [Npb, qpb] at *; omega⟩ : Fin (2*n+m+2)) := by
  simp only [pbEquiv, Equiv.trans_apply]
  rw [finSumFinEquiv_symm_of_le _ (by rw [finCongr_apply_coe]; exact h)]
  simp only [finCongr_apply_coe]

theorem pbEquiv_pbX {n m : ℕ} (i : Fin n) : pbEquiv n m (pbX n m i) = Sum.inl (Fin.castSucc i) := by
  rw [pbEquiv_val_lt _ (by simp [pbX])]
  first | rfl | exact congrArg Sum.inl (Fin.ext rfl)

theorem pbEquiv_pbS {n m : ℕ} : pbEquiv n m (pbS n m) = Sum.inl (Fin.last n) := by
  rw [pbEquiv_val_lt _ (by simp [pbS])]
  first | rfl | exact congrArg Sum.inl (Fin.ext rfl)

theorem pbEquiv_pbY {n m : ℕ} (i : Fin n) :
    pbEquiv n m (pbY n m i) = Sum.inr (⟨i.val, by omega⟩ : Fin (2*n+m+2)) := by
  rw [pbEquiv_val_le _ (by simp [pbY, Npb, qpb])]
  exact congrArg Sum.inr (Fin.ext (by simp [pbY, Npb]))

theorem pbEquiv_pbW {n m : ℕ} (i : Fin n) :
    pbEquiv n m (pbW n m i) = Sum.inr (⟨n+i.val, by omega⟩ : Fin (2*n+m+2)) := by
  rw [pbEquiv_val_le _ (by simp [pbW, Npb, qpb]; omega)]
  exact congrArg Sum.inr (Fin.ext (by simp [pbW, Npb]; omega))

theorem pbEquiv_pbT {n m : ℕ} :
    pbEquiv n m (pbT n m) = Sum.inr (⟨2*n, by omega⟩ : Fin (2*n+m+2)) := by
  rw [pbEquiv_val_le _ (by simp [pbT, Npb, qpb]; omega)]
  exact congrArg Sum.inr (Fin.ext (by simp [pbT, Npb]; omega))

theorem pbEquiv_pbU {n m : ℕ} :
    pbEquiv n m (pbU n m) = Sum.inr (⟨2*n+1, by omega⟩ : Fin (2*n+m+2)) := by
  rw [pbEquiv_val_le _ (by simp [pbU, Npb, qpb]; omega)]
  exact congrArg Sum.inr (Fin.ext (by simp [pbU, Npb]; omega))

theorem pbEquiv_pbA {n m : ℕ} (a : Fin m) :
    pbEquiv n m (pbA n m a)
      = Sum.inr (⟨2*n+2+a.val, by have := a.isLt; omega⟩ : Fin (2*n+m+2)) := by
  rw [pbEquiv_val_le _ (by simp [pbA, Npb, qpb]; omega)]
  exact congrArg Sum.inr (Fin.ext (by simp [pbA, Npb]; omega))

/-! ## The values of `sNum`, `sDen`, `sRest` at the named pulled-back coordinates -/

lemma sNum_castSucc {n m : ℕ} (i : Fin n) : sNum n m (Fin.castSucc i) = exY n m i := by
  rw [sNum, dif_pos (by simpa using i.isLt)]
  first | rfl | exact congrArg (exY n m) (Fin.ext rfl)

lemma sDen_castSucc {n m : ℕ} (i : Fin n) : sDen n m (Fin.castSucc i) = exW n m i := by
  rw [sDen, dif_pos (by simpa using i.isLt)]
  first | rfl | exact congrArg (exW n m) (Fin.ext rfl)

lemma sNum_last {n m : ℕ} : sNum n m (Fin.last n) = exT n m := by
  rw [sNum, dif_neg (by simp)]

lemma sDen_last {n m : ℕ} : sDen n m (Fin.last n) = exU n m := by
  rw [sDen, dif_neg (by simp)]

lemma sRest_eq_exY {n m : ℕ} (i : Fin n) :
    sRest n m (⟨i.val, by omega⟩ : Fin (2*n+m+2)) = exY n m i := by
  rw [sRest, dif_pos i.isLt]

lemma sRest_eq_exW {n m : ℕ} (i : Fin n) :
    sRest n m (⟨n+i.val, by omega⟩ : Fin (2*n+m+2)) = exW n m i := by
  have h1 : ¬ (n + i.val : ℕ) < n := by omega
  have h2 : (n + i.val : ℕ) < 2*n := by omega
  rw [sRest, dif_neg h1, dif_pos h2]
  exact congrArg (exW n m) (Fin.ext (by simp only [Fin.val_mk]; omega))

lemma sRest_eq_exT {n m : ℕ} :
    sRest n m (⟨2*n, by omega⟩ : Fin (2*n+m+2)) = exT n m := by
  have h1 : ¬ (2*n : ℕ) < n := by omega
  have h2 : ¬ (2*n : ℕ) < 2*n := by omega
  have h3 : (2*n : ℕ) = 2*n := rfl
  rw [sRest, dif_neg h1, dif_neg h2, dif_pos h3]

lemma sRest_eq_exU {n m : ℕ} :
    sRest n m (⟨2*n+1, by omega⟩ : Fin (2*n+m+2)) = exU n m := by
  have h1 : ¬ (2*n+1 : ℕ) < n := by omega
  have h2 : ¬ (2*n+1 : ℕ) < 2*n := by omega
  have h3 : ¬ (2*n+1 : ℕ) = 2*n := by omega
  have h4 : (2*n+1 : ℕ) = 2*n+1 := rfl
  rw [sRest, dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]

lemma sRest_eq_exA {n m : ℕ} (a : Fin m) :
    sRest n m (⟨2*n+2+a.val, by have := a.isLt; omega⟩ : Fin (2*n+m+2)) = exA n m a := by
  have h1 : ¬ (2*n+2+a.val : ℕ) < n := by omega
  have h2 : ¬ (2*n+2+a.val : ℕ) < 2*n := by omega
  have h3 : ¬ (2*n+2+a.val : ℕ) = 2*n := by omega
  have h4 : ¬ (2*n+2+a.val : ℕ) = 2*n+1 := by omega
  rw [sRest, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4]
  exact congrArg (exA n m) (Fin.ext (by simp only [Fin.val_mk]; omega))

/-! ## The reconstruction map -/

/-- **The pulled-back point reconstructed from a point of the extended ambient.**  Reading `z`
through the coordinate identification `pbEquiv` of `clearPb`: on the block `(x, s)` it gives the
quotients `y i / w i` and `τ / u` (the `psiInv`-coordinates), on the block `(y, w, τ, u, aux)` it
is `z` itself. -/
def exSub {n m : ℕ} (z : Fin (Next n m) → ℝ) : Fin (Npb n m) → ℝ := fun l =>
  Sum.elim (fun b : Fin (n+1) => z (sNum n m b) / z (sDen n m b))
    (fun k : Fin (2*n+m+2) => z (sRest n m k)) (pbEquiv n m l)

/-- The base block `x : ℝⁿ` of the reconstructed point. -/
def exBase {n m : ℕ} (z : Fin (Next n m) → ℝ) : Fin n → ℝ :=
  fun i => z (exY n m i) / z (exW n m i)

/-- The fibre block `(s, y, w, τ, u, aux)` of the reconstructed point. -/
def exFib {n m : ℕ} (z : Fin (Next n m) → ℝ) : Fin (qpb n m) → ℝ :=
  fun j => exSub z (Fin.natAdd n j)

@[simp] theorem exSub_pbX {n m : ℕ} (z : Fin (Next n m) → ℝ) (i : Fin n) :
    exSub z (pbX n m i) = z (exY n m i) / z (exW n m i) := by
  simp only [exSub, pbEquiv_pbX, Sum.elim_inl, sNum_castSucc, sDen_castSucc]

@[simp] theorem exSub_pbS {n m : ℕ} (z : Fin (Next n m) → ℝ) :
    exSub z (pbS n m) = z (exT n m) / z (exU n m) := by
  simp only [exSub, pbEquiv_pbS, Sum.elim_inl, sNum_last, sDen_last]

@[simp] theorem exSub_pbY {n m : ℕ} (z : Fin (Next n m) → ℝ) (i : Fin n) :
    exSub z (pbY n m i) = z (exY n m i) := by
  simp only [exSub, pbEquiv_pbY, Sum.elim_inr, sRest_eq_exY]

@[simp] theorem exSub_pbW {n m : ℕ} (z : Fin (Next n m) → ℝ) (i : Fin n) :
    exSub z (pbW n m i) = z (exW n m i) := by
  simp only [exSub, pbEquiv_pbW, Sum.elim_inr, sRest_eq_exW]

@[simp] theorem exSub_pbT {n m : ℕ} (z : Fin (Next n m) → ℝ) :
    exSub z (pbT n m) = z (exT n m) := by
  simp only [exSub, pbEquiv_pbT, Sum.elim_inr, sRest_eq_exT]

@[simp] theorem exSub_pbU {n m : ℕ} (z : Fin (Next n m) → ℝ) :
    exSub z (pbU n m) = z (exU n m) := by
  simp only [exSub, pbEquiv_pbU, Sum.elim_inr, sRest_eq_exU]

@[simp] theorem exSub_pbA {n m : ℕ} (z : Fin (Next n m) → ℝ) (a : Fin m) :
    exSub z (pbA n m a) = z (exA n m a) := by
  simp only [exSub, pbEquiv_pbA, Sum.elim_inr, sRest_eq_exA]

@[simp] theorem exBase_apply {n m : ℕ} (z : Fin (Next n m) → ℝ) (i : Fin n) :
    exBase z i = z (exY n m i) / z (exW n m i) := rfl

@[simp] theorem exSub_castAdd {n m : ℕ} (z : Fin (Next n m) → ℝ) (i : Fin n) :
    exSub z (Fin.castAdd (qpb n m) i) = exBase z i := by
  have h : (Fin.castAdd (qpb n m) i : Fin (Npb n m)) = pbX n m i := Fin.ext rfl
  rw [h, exSub_pbX, exBase_apply]

lemma natAdd_fY {n m : ℕ} (i : Fin n) : Fin.natAdd n (fY n m i) = pbY n m i := by
  ext; simp only [Fin.natAdd, fY, pbY]; omega

lemma natAdd_fW {n m : ℕ} (i : Fin n) : Fin.natAdd n (fW n m i) = pbW n m i := by
  ext; simp only [Fin.natAdd, fW, pbW]; omega

lemma natAdd_fT {n m : ℕ} : Fin.natAdd n (fT n m) = pbT n m := by
  ext; simp only [Fin.natAdd, fT, pbT]; omega

lemma natAdd_fU {n m : ℕ} : Fin.natAdd n (fU n m) = pbU n m := by
  ext; simp only [Fin.natAdd, fU, pbU]; omega

lemma natAdd_fA {n m : ℕ} (a : Fin m) : Fin.natAdd n (fA n m a) = pbA n m a := by
  ext; simp only [Fin.natAdd, fA, pbA]; omega

lemma natAdd_fS {n m : ℕ} : Fin.natAdd n (fS n m) = pbS n m := by
  ext; simp only [Fin.natAdd, fS, pbS]; omega

@[simp] theorem exFib_fS {n m : ℕ} (z : Fin (Next n m) → ℝ) :
    exFib z (fS n m) = z (exT n m) / z (exU n m) := by
  rw [exFib, natAdd_fS, exSub_pbS]

@[simp] theorem exFib_fY {n m : ℕ} (z : Fin (Next n m) → ℝ) (i : Fin n) :
    exFib z (fY n m i) = z (exY n m i) := by
  rw [exFib, natAdd_fY, exSub_pbY]

@[simp] theorem exFib_fW {n m : ℕ} (z : Fin (Next n m) → ℝ) (i : Fin n) :
    exFib z (fW n m i) = z (exW n m i) := by
  rw [exFib, natAdd_fW, exSub_pbW]

@[simp] theorem exFib_fT {n m : ℕ} (z : Fin (Next n m) → ℝ) :
    exFib z (fT n m) = z (exT n m) := by
  rw [exFib, natAdd_fT, exSub_pbT]

@[simp] theorem exFib_fU {n m : ℕ} (z : Fin (Next n m) → ℝ) :
    exFib z (fU n m) = z (exU n m) := by
  rw [exFib, natAdd_fU, exSub_pbU]

@[simp] theorem exFib_fA {n m : ℕ} (z : Fin (Next n m) → ℝ) (a : Fin m) :
    exFib z (fA n m a) = z (exA n m a) := by
  rw [exFib, natAdd_fA, exSub_pbA]

/-- The split of the reconstructed point into the base `x` and the fibre
`(s, y, w, τ, u, aux)` of the implicit function theorem. -/
theorem exSub_eq_append {n m : ℕ} (z : Fin (Next n m) → ℝ) :
    exSub z = Fin.append (exBase z) (exFib z) := by
  funext l
  refine Fin.addCases (fun i => ?_) (fun j => ?_) l
  · rw [Fin.append_left]; exact exSub_castAdd z i
  · rw [Fin.append_right]; rfl

/-- The stratum coordinates of the reconstructed point are the stratum coordinates of `z`. -/
theorem pbStrat_exSub {n m : ℕ} (z : Fin (Next n m) → ℝ) :
    pbStrat (exSub z) = exStrat z := by
  funext i
  have hL : pbStrat (exSub z) i = exSub z (sIdxPb n m i) := rfl
  have hR : exStrat z i = z (sIdxE n m i) := rfl
  rw [hL, hR, sIdxPb, sIdxE]
  split_ifs with h1 h2
  · rw [exSub_pbY]
  · rw [exSub_pbT]
  · rw [exSub_pbA]

end Work.WilE9.Sharp
