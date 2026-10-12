import ChallengeDeps
import Submission.Work.BoseRowQ2.GchiIdentify
import Submission.Work.BoseRowQ2.tail_eq_tsum
import Submission.Work.BoseRowQ2.tail_quad_le
import Submission.Work.BoseRowQ2.vec_labVec_sub_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseRowQ2/maskSharpCore.lean` — the one-body core of the sharp mask row

This is the one-body linear algebra that reduces `GchiAtMask` (FS l.3253, the *sharp* mask
row with `Cχ = 96/π` and a tail slot `δ ≍ ℓ⁻²/(μa)`) to the two analytic inputs of
`maskTailDefs` (`chatSq_form_le`, `tail_quad_le`, `chatTail_quad_le`, `tail_eq_tsum`).

The dictionary (`w = Dv` the masked `θ`-coordinates, `w'` the mask complement, `v_i = ⟨g_i,u⟩`,
`z = u − Σ_{i∈exc}v_i g_i`, `h_k = f_k − Σ_{i∈exc}χ̂(K_k−K_i) g_i`):

* `⟨u, GchiA u⟩ = ⟨w, Mc w⟩ = ‖Cw‖² + ⟨w, Tail w⟩`,
* `⟨u, GchiF u⟩ = Σ_k (⟨f_k,u⟩)² = Σ_k(b_k + b'_k + ⟨h_k,z⟩)²`,
* `⟨u, Dmask u⟩ = Σ_{i∈exc}(1−c_i)²v_i² = ‖w'‖²`,
* `‖u‖² = Σ_{i∈exc}v_i² + ‖z‖² ≥ ‖w‖² + ‖w'‖² + ‖z‖²`.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseB4
open Work.BoseGateFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

section Honest

variable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
  {fc fu : Work.BoseBoxFix.LowCut}

/-- **The mask-complement matrix** `Σ_{s∈excited}(1−f_L s)² g_s ⊗ g_s`, whose `besselOpMat`
is the mask-complement number `maskNum`. -/
noncomputable def Dmask (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    Fin (HM μ).m → Fin (HM μ).m → ℝ :=
  fun l l' => ∑ s ∈ excited (Lab (HM μ).N),
    (1 - (Work.BoseRowsFS.honE v h fc fu HM μ).fL s) ^ 2 * ((HM μ).g s l * (HM μ).g s l')

/-- `besselOpMat` of `Dmask` is the mask-complement number of `maskNum`. -/
theorem besselOpMat_Dmask (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    besselOpMat (HM μ).m (Dmask (v := v) (h := h) (fc := fc) (fu := fu) HM μ)
      = (Work.BoseRowsFS.honT v h fc fu HM μ).maskNum
          (Work.BoseRowsFS.honE v h fc fu HM μ) := by
  show besselOpMat (HM μ).m (fun l l' => ∑ s ∈ excited (Lab (HM μ).N),
      (1 - (Work.BoseRowsFS.honE v h fc fu HM μ).fL s) ^ 2 * ((HM μ).g s l * (HM μ).g s l'))
      = ∑ s ∈ excited (Lab (HM μ).N),
          ((1 - (Work.BoseRowsFS.honE v h fc fu HM μ).fL s) ^ 2)
            • ((Work.BoseRowsFS.honT v h fc fu HM μ).taDag s
                ∘ₗ (Work.BoseRowsFS.honT v h fc fu HM μ).ta s)
  rw [besselOpMat_sum_finset]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show (fun l l' => (1 - (Work.BoseRowsFS.honE v h fc fu HM μ).fL s) ^ 2
        * ((HM μ).g s l * (HM μ).g s l'))
      = ((1 - (Work.BoseRowsFS.honE v h fc fu HM μ).fL s) ^ 2)
        • (fun l l' => (HM μ).g s l * (HM μ).g s l') from by
    funext l l'; simp [Pi.smul_apply]]
  rw [besselOpMat_smul]
  congr 1
  rw [Work.BoseRowQ2.honT_taDag, Work.BoseRowQ2.honT_ta]
  exact (creOf_comp_annOf_eq_besselOpMat (fun l => (HM μ).g s l) (fun l => (HM μ).g s l)).symm

/-- The `g`-coordinates of a one-body vector. -/
noncomputable def gcoord (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (u : Fin (HM μ).m → ℝ) (i : Lab (HM μ).N) : ℝ :=
  gram ((HM μ).g i) u

/-- The projection of `u` onto the span of the excited `θ`-modes. -/
noncomputable def uP (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (u : Fin (HM μ).m → ℝ) : Fin (HM μ).m → ℝ :=
  ∑ i ∈ excited (Lab (HM μ).N), gcoord HM μ u i • (HM μ).g i

/-- The component of `u` orthogonal to the excited `θ`-modes. -/
noncomputable def zvec (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (u : Fin (HM μ).m → ℝ) : Fin (HM μ).m → ℝ :=
  u - uP HM μ u

/-- The masked `θ`-coordinates. -/
noncomputable def wfun (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (u : Fin (HM μ).m → ℝ) : Lab (HM μ).N → ℝ :=
  fun i => if i ∈ excited (Lab (HM μ).N)
    then (Work.BoseRowsFS.honE v h fc fu HM μ).fL i
      * gcoord HM μ u i
    else 0

/-- The mask complement of the `θ`-coordinates. -/
noncomputable def wpfun (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (u : Fin (HM μ).m → ℝ) : Lab (HM μ).N → ℝ :=
  fun i => if i ∈ excited (Lab (HM μ).N)
    then (1 - (Work.BoseRowsFS.honE v h fc fu HM μ).fL i)
      * gcoord HM μ u i
    else 0

/-- **`h_k`**: the orthogonal complement of `f_k` in the excited `θ`-span. -/
noncomputable def hvec (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (k : Lab (HM μ).N) : Fin (HM μ).m → ℝ :=
  fun l => (HM μ).f k l - ∑ i ∈ excited (Lab (HM μ).N),
    Chat (HM μ).N k i * (HM μ).g i l

/-- `Cw`: the `χ`-coordinates of the masked part. -/
noncomputable def bfun (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (u : Fin (HM μ).m → ℝ) (k : Lab (HM μ).N) : ℝ :=
  ∑ i : Lab (HM μ).N,
    wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i * Chat (HM μ).N k i

/-- `Cw'`. -/
noncomputable def bpfun (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (u : Fin (HM μ).m → ℝ) (k : Lab (HM μ).N) : ℝ :=
  ∑ i : Lab (HM μ).N,
    wpfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i * Chat (HM μ).N k i


/-! ## 2. Bilinearity of `gram` and the orthogonal decomposition -/

lemma gram_add_l {m : ℕ} (a b c : Fin m → ℝ) : gram (a + b) c = gram a c + gram b c := by
  simp only [gram, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma gram_add_r {m : ℕ} (a b c : Fin m → ℝ) : gram a (b + c) = gram a b + gram a c := by
  simp only [gram, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma gram_sub_l {m : ℕ} (a b c : Fin m → ℝ) : gram (a - b) c = gram a c - gram b c := by
  simp only [gram, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma gram_sub_r {m : ℕ} (a b c : Fin m → ℝ) : gram a (b - c) = gram a b - gram a c := by
  simp only [gram, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma gram_sum_smul_l {m : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ) (w : ι → Fin m → ℝ)
    (b : Fin m → ℝ) :
    gram (∑ i ∈ s, c i • w i) b = ∑ i ∈ s, c i * gram (w i) b := by
  simp only [gram, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

lemma gram_sum_smul_r {m : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ) (w : ι → Fin m → ℝ)
    (a : Fin m → ℝ) :
    gram a (∑ i ∈ s, c i • w i) = ∑ i ∈ s, c i * gram a (w i) := by
  simp only [gram, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

/-- **The `z`-component is orthogonal to every excited `θ`-mode.** -/
theorem gram_g_zvec (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ)
    (i : Lab (HM μ).N) (hi : i ∈ excited (Lab (HM μ).N)) :
    gram ((HM μ).g i) (zvec HM μ u) = 0 := by
  have hzi : i ≠ 0 := Finset.ne_of_mem_erase hi
  rw [zvec, uP, gram_sub_r,
    gram_sum_smul_r (excited (Lab (HM μ).N)) (fun j => gcoord HM μ u j) (fun j => (HM μ).g j)
      ((HM μ).g i)]
  have h1 : ∀ j ∈ excited (Lab (HM μ).N),
      gram ((HM μ).g i) ((HM μ).g j) = if i = j then 1 else 0 :=
    fun j hj => (HM μ).hg i j hzi (Finset.ne_of_mem_erase hj)
  rw [Finset.sum_congr rfl (fun j hj => by rw [h1 j hj])]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, mul_one, gcoord]; ring
  · intro j hj hji; rw [if_neg (Ne.symm hji), mul_zero]
  · intro hi'; exact absurd hi hi'

/-- `⟨uP, u⟩ = Σ_{i∈exc} (⟨g_i,u⟩)² = ⟨uP, uP⟩`. -/
theorem gram_uP_self (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ) :
    gram (uP HM μ u) (uP HM μ u)
      = ∑ i ∈ excited (Lab (HM μ).N), (gcoord HM μ u i) ^ 2 := by
  rw [uP, gram_sum_smul_l]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hzi : i ≠ 0 := Finset.ne_of_mem_erase hi
  rw [gram_sum_smul_r]
  have h1 : ∀ j ∈ excited (Lab (HM μ).N),
      gram ((HM μ).g i) ((HM μ).g j) = if i = j then 1 else 0 :=
    fun j hj => (HM μ).hg i j hzi (Finset.ne_of_mem_erase hj)
  rw [Finset.sum_congr rfl (fun j hj => by rw [h1 j hj])]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, mul_one]; ring
  · intro j hj hji; rw [if_neg (Ne.symm hji), mul_zero]
  · intro hi'; exact absurd hi hi'

/-- `⟨uP, z⟩ = 0`. -/
theorem gram_uP_zvec (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ) :
    gram (uP HM μ u) (zvec HM μ u) = 0 := by
  rw [uP, gram_sum_smul_l]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [gram_g_zvec HM μ u i hi, mul_zero]

/-- **The orthogonal decomposition of `‖u‖²`.** -/
theorem sq_decomp (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ) :
    (∑ l : Fin (HM μ).m, u l ^ 2)
      = (∑ i ∈ excited (Lab (HM μ).N), (gcoord HM μ u i) ^ 2)
        + ∑ l : Fin (HM μ).m, (zvec HM μ u l) ^ 2 := by
  have huz : u = uP HM μ u + zvec HM μ u := by
    rw [zvec]; abel
  have h1 : (∑ l : Fin (HM μ).m, u l ^ 2) = gram u u := by
    rw [gram]; exact Finset.sum_congr rfl fun l _ => by rw [pow_two]
  have h2 : gram u u = gram (uP HM μ u) (uP HM μ u)
      + gram (zvec HM μ u) (zvec HM μ u) := by
    conv_lhs => rw [huz]
    rw [gram_add_l, gram_add_r, gram_uP_zvec, gram_add_r,
      gram_comm (zvec HM μ u) (uP HM μ u), gram_uP_zvec, add_zero, zero_add]
  rw [h1, h2, gram_uP_self]
  congr 1
  rw [gram]; exact Finset.sum_congr rfl fun l _ => by rw [pow_two]


/-! ## 3. The lattice pin of the `χ̂²` kernel at masked labels -/

/-- **At masked labels the mode-indexed `χ̂²` is the lattice kernel `Mc`.**
`f_L a ≠ 0` forces `‖kmom a‖ ≤ 2κ`, so `vec (labVec N (a−b)) = vec (labVec N a) − vec (labVec N b)`. -/
theorem hatChiSq_sub_eq_Mc (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v)
    (hN : 2 * RowGchiMaskRowAux.honCutRad v μ / Real.pi ≤ ((HM μ).N : ℝ))
    (a b : Lab (HM μ).N)
    (ha : (Work.BoseRowsFS.honE v h fc fu HM μ).fL a ≠ 0)
    (hb : (Work.BoseRowsFS.honE v h fc fu HM μ).fL b ≠ 0) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).hatChiSq (a - b) = Mc (HM μ).N a b := by
  have hnorm : ∀ c : Lab (HM μ).N, (Work.BoseRowsFS.honE v h fc fu HM μ).fL c ≠ 0 →
      ‖Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N c)‖ ≤ 2 * RowGchiMaskRowAux.honCutRad v μ := by
    intro c hc
    have h1 : ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom c‖ ≤ 2 * RowGchiMaskRowAux.honKap v μ :=
      RowGchiMaskRowAux.honE_fL_supp HM hμ hav c hc
    have h2 : Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N c)
        = Work.BoseBoxFock.ellH v μ • (Work.BoseRowsFS.honF v h fc fu HM μ).kmom c := by
      rw [show (Work.BoseRowsFS.honF v h fc fu HM μ).kmom
          = Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N from rfl]
      exact (RowGchiMaskRowAux.smul_kmomLab_eq (ne_of_gt (Work.BoseBoxFock.ellH_pos v μ))
        (HM μ).N c).symm
    rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos (Work.BoseBoxFock.ellH_pos v μ)]
    calc Work.BoseBoxFock.ellH v μ
          * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom c‖
        ≤ Work.BoseBoxFock.ellH v μ * (2 * RowGchiMaskRowAux.honKap v μ) :=
          mul_le_mul_of_nonneg_left h1 (Work.BoseBoxFock.ellH_pos v μ).le
      _ = 2 * RowGchiMaskRowAux.honCutRad v μ := by
          rw [RowGchiMaskRowAux.honCutRad]; ring
  have hSub := Work.BoseRowQ2.vec_labVec_sub_eq (N := (HM μ).N) (s := b) (s' := a)
    (L := 2 * RowGchiMaskRowAux.honCutRad v μ) (le_of_lt (mul_pos two_pos (by
      rw [RowGchiMaskRowAux.honCutRad]
      exact mul_pos (Work.BoseBoxFock.ellH_pos v μ) (RowGchiMaskRowAux.honKap_pos hav hμ))))
    (hnorm b hb) (hnorm a ha) hN
  show (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq (a - b) = Mc (HM μ).N a b
  rw [Work.BoseBoxFock.honest_hatChiSq_eq v h fc fu HM μ
    (Work.BoseBox.sideAt_pos hμ hav) (a - b)]
  have harg : Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N a
        - Work.BoseBoxFock.labVec (HM μ).N b)
      = Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N a)
        - Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N b) := by
    rw [sub_eq_add_neg, Work.BoseRowQ2.vec_add, Work.BoseBoxFock.vec_neg, sub_eq_add_neg]
  rw [Mc, hSub, chiHatSq, harg]


/-! ## 4. The `Chat`-`gram` pin -/

/-- `Chat` is the `gram` of `g` against `f`. -/
theorem gram_g_f_eq_chat (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (k i : Lab (HM μ).N) :
    gram ((HM μ).g i) ((HM μ).f k) = Chat (HM μ).N k i := by
  have h1 : gram ((HM μ).g i) ((HM μ).f k)
      = Work.BoseK15.corpusBox.hatChi (Work.BoseBoxFock.ellH v μ •
          (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k
            - Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N i)) :=
    HM μ |>.hcross i k
  rw [h1]
  simp only [Chat, chiHat]
  congr 1
  rw [smul_sub,
    RowGchiMaskRowAux.smul_kmomLab_eq (ne_of_gt (Work.BoseBoxFock.ellH_pos v μ)) (HM μ).N k,
    RowGchiMaskRowAux.smul_kmomLab_eq (ne_of_gt (Work.BoseBoxFock.ellH_pos v μ)) (HM μ).N i]
  rw [show Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N k
        - Work.BoseBoxFock.labVec (HM μ).N i)
      = Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N k)
        + -Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N i) from by
    rw [sub_eq_add_neg, Work.BoseRowQ2.vec_add, Work.BoseBoxFock.vec_neg]]
  rw [sub_eq_add_neg]


/-! ## 1b. The quadratic forms of the three matrices -/

/-- Exchange of a triple sum. -/
lemma triple_sum_comm {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (F : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ c, ∑ a, ∑ b, F a b c := by
  have h1 : (∑ a, ∑ b, ∑ c, F a b c) = ∑ a, ∑ c, ∑ b, F a b c :=
    Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [h1, Finset.sum_comm]

/-- Exchange of a triple sum, the innermost over a `Finset`. -/
lemma triple_sum_comm_finset {α β : Type*} [Fintype α] [Fintype β] {γ : Type*} (s : Finset γ)
    (F : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c ∈ s, F a b c) = ∑ c ∈ s, ∑ a, ∑ b, F a b c := by
  have h1 : (∑ a, ∑ b, ∑ c ∈ s, F a b c) = ∑ a, ∑ c ∈ s, ∑ b, F a b c :=
    Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [h1, Finset.sum_comm]

/-- Factoring a constant out of a double sum. -/
lemma mul_sum_sum {α β : Type*} [Fintype α] [Fintype β] (k : ℝ) (Y : α → β → ℝ) :
    k * (∑ a, ∑ b, Y a b) = ∑ a, ∑ b, k * Y a b := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.mul_sum Finset.univ (fun b => Y a b) k

/-- The squared `ℓ²`-norm of a vector as a double sum. -/
lemma sq_eq_sum_sum_sq {α : Type*} [Fintype α] (Y : α → ℝ) :
    (∑ a, Y a) ^ 2 = ∑ a, ∑ b, Y a * Y b := by
  rw [pow_two, Finset.sum_mul_sum]

/-- **`⟨u, GchiF u⟩ = Σ_k (⟨f_k, u⟩)²`.** -/
theorem form_GchiF (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ) :
    (∑ l : Fin (HM μ).m, ∑ l' : Fin (HM μ).m, u l * GchiF HM μ l l' * u l')
      = ∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2 := by
  have h1 : ∀ l l' : Fin (HM μ).m,
      u l * GchiF HM μ l l' * u l'
        = ∑ k : Lab (HM μ).N, u l * ((HM μ).f k l * (HM μ).f k l') * u l' := by
    intro l l'
    rw [GchiF, Finset.mul_sum, Finset.sum_mul]
  simp_rw [h1]
  rw [triple_sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [gram, sq_eq_sum_sum_sq]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by ring

/-- **`⟨u, Dmask u⟩ = Σ_{i∈excited} ((1−f_L i)·⟨g_i,u⟩)²`.** -/
theorem form_Dmask (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ) :
    (∑ l : Fin (HM μ).m, ∑ l' : Fin (HM μ).m,
        u l * Dmask (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l' * u l')
      = ∑ i ∈ excited (Lab (HM μ).N),
          ((1 - (Work.BoseRowsFS.honE v h fc fu HM μ).fL i) * gcoord HM μ u i) ^ 2 := by
  have h1 : ∀ l l' : Fin (HM μ).m,
      u l * Dmask (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l' * u l'
        = ∑ i ∈ excited (Lab (HM μ).N),
            ((1 - (Work.BoseRowsFS.honE v h fc fu HM μ).fL i) ^ 2)
              * (u l * ((HM μ).g i l * (HM μ).g i l') * u l') := by
    intro l l'
    rw [Dmask, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [h1]
  rw [triple_sum_comm_finset]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_sum_sum]
  rw [show ((1 - (Work.BoseRowsFS.honE v h fc fu HM μ).fL i) * gcoord HM μ u i) ^ 2
      = ((1 - (Work.BoseRowsFS.honE v h fc fu HM μ).fL i) ^ 2)
          * (gcoord HM μ u i) ^ 2 from by ring]
  congr 1
  rw [gcoord, gram, sq_eq_sum_sum_sq]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by ring

end Honest

end Work.BoseRowQ2
