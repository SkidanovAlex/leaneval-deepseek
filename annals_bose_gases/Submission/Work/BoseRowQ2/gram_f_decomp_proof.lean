import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseRowQ2.maskSharpCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseRowQ2/gram_f_decomp_proof.lean`

The orthogonal decomposition of `⟨f k, u⟩` behind the *sharp* mask row
(`Work.BoseRowQ2.gram_f_decomp`, FS l.3253).

Let `U = span{g i : i ∈ excited (Lab N)}` be the span of the excited `θ`-modes (`g` is
orthonormal on the excited labels, `HonestModes.hg`, and `⟨g i, f k⟩ = χ̂(K k − K i) =
Chat N k i`, `gram_g_f_eq_chat`).  Splitting

* `f k = h k + Σ_{i ∈ excited} Chat k i • g i`, i.e. `hvec k = h k ⊥ U` (`hvec_add`),
* `u = uP u + zvec u` with `uP u ∈ U`, `zvec u ⊥ U` (the coordinates of `u` along `g i`
  are `gcoord i = ⟨g i, u⟩`),

and writing the masked / mask-complement coordinates of `u` as

* `wfun i = f_L i · gcoord i` (zero off the excited labels),
* `wpfun i = (1 − f_L i) · gcoord i` (zero off the excited labels),

so that `bfun u k = ⟨w, C_k⟩` and `bpfun u k = ⟨w', C_k⟩` are the two masks of the
`χ̂`-row, the identity is the expansion

  `⟨f k, u⟩ = Σ_{i∈excited} Chat k i ⟨g i, u⟩ + ⟨h k, zvec u⟩`
            `= (bfun u k + bpfun u k) + Σ_l hvec k l · zvec u l`,

because `⟨h k, g i⟩ = 0` for `i ∈ excited`, so only the `zvec u` component of `u`
contributes to `⟨h k, u⟩`.
-/

namespace Work.BoseRowQ2

open Work.BoseB4 Work.BoseB7 Work.BoseBoxFock

variable {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}

/-! ## 1. The splitting of `f k` -/

/-- `f k = hvec k + Σ_{i∈excited} Chat k i • g i : the definition of `hvec`, read
off pointwise. -/
lemma gram_f_decomp_f_eq (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (k : Lab (HM μ).N) :
    (HM μ).f k
      = hvec HM μ k
        + ∑ i ∈ excited (Lab (HM μ).N), Chat (HM μ).N k i • (HM μ).g i := by
  funext l
  simp only [hvec, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## 2. The sum of the two masked coordinates -/

/-- The two masks of the excited coordinate `gcoord i` add up to `gcoord i`. -/
lemma gram_f_decomp_wfun_add_wpfun (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (u : Fin (HM μ).m → ℝ) (i : Lab (HM μ).N) :
    wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i
      + wpfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i
      = if i ∈ excited (Lab (HM μ).N) then gcoord HM μ u i else 0 := by
  rw [wfun, wpfun]
  split_ifs with hi <;> ring

/-- **`bfun u k + bpfun u k = Σ_{i∈excited} Chat k i · gcoord i`.** -/
lemma gram_f_decomp_bfun_add_bpfun (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (u : Fin (HM μ).m → ℝ) (k : Lab (HM μ).N) :
    bfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u k
      + bpfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u k
      = ∑ i ∈ excited (Lab (HM μ).N), Chat (HM μ).N k i * gcoord HM μ u i := by
  rw [bfun, bpfun, ← Finset.sum_add_distrib]
  have hz : ∀ x ∈ (Finset.univ : Finset (Lab (HM μ).N)), x ∉ excited (Lab (HM μ).N) →
      wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u x * Chat (HM μ).N k x
        + wpfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u x * Chat (HM μ).N k x = 0 := by
    intro x _ hx
    rw [← add_mul, gram_f_decomp_wfun_add_wpfun HM μ u x, if_neg hx, zero_mul]
  have h1 := (Finset.sum_subset (Finset.subset_univ (excited (Lab (HM μ).N))) hz).symm
  rw [h1]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← add_mul, gram_f_decomp_wfun_add_wpfun HM μ u i, if_pos hi]
  ring

/-! ## 3. `hvec k` is orthogonal to the excited modes -/

/-- **`⟨hvec k, g i⟩ = 0` for `i ∈ excited`**, i.e. `hvec k = f k − Σ_{i∈excited} Chat k i • g i`
is the component of `f k` orthogonal to the excited span. -/
lemma gram_f_decomp_gram_hvec_g (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (k : Lab (HM μ).N)
    (i : Lab (HM μ).N) (hi : i ∈ excited (Lab (HM μ).N)) :
    gram (hvec HM μ k) ((HM μ).g i) = 0 := by
  have hsplit : hvec HM μ k
      = (HM μ).f k - ∑ j ∈ excited (Lab (HM μ).N), Chat (HM μ).N k j • (HM μ).g j := by
    funext l
    simp only [hvec, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hzi : i ≠ 0 := Finset.ne_of_mem_erase hi
  rw [hsplit, gram_sub_l, gram_sum_smul_l]
  have h1 : ∀ j ∈ excited (Lab (HM μ).N),
      gram ((HM μ).g j) ((HM μ).g i) = if j = i then 1 else 0 :=
    fun j hj => (HM μ).hg j i (Finset.ne_of_mem_erase hj) hzi
  rw [Finset.sum_congr rfl (fun j hj => by rw [h1 j hj])]
  rw [Finset.sum_eq_single i (fun j hj hji => by rw [if_neg hji, mul_zero])
        (fun hi' => absurd hi hi'), if_pos rfl, mul_one]
  rw [gram_comm, gram_g_f_eq_chat, sub_self]

/-- `⟨hvec k, uP u⟩ = 0` (`uP u` lies in the excited span). -/
lemma gram_f_decomp_gram_hvec_uP (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (u : Fin (HM μ).m → ℝ) (k : Lab (HM μ).N) :
    gram (hvec HM μ k) (uP HM μ u) = 0 := by
  rw [uP, gram_sum_smul_r]
  exact Finset.sum_eq_zero fun i hi => by
    rw [gram_f_decomp_gram_hvec_g HM μ k i hi, mul_zero]

/-- **`⟨hvec k, u⟩ = Σ_l hvec k l · zvec u l`**: only the `zvec u` component of `u`
contributes. -/
lemma gram_f_decomp_gram_hvec_eq (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (u : Fin (HM μ).m → ℝ) (k : Lab (HM μ).N) :
    gram (hvec HM μ k) u = ∑ l : Fin (HM μ).m, hvec HM μ k l * zvec HM μ u l := by
  have huz : u = uP HM μ u + zvec HM μ u := by rw [zvec]; abel
  conv_lhs => rw [huz]
  rw [gram_add_r, gram_f_decomp_gram_hvec_uP, zero_add, gram]

/-! ## 4. The expansion of `⟨f k, u⟩` -/

/-- **`⟨f k, u⟩ = ⟨hvec k, u⟩ + Σ_{i∈excited} Chat k i · gcoord i`.** -/
lemma gram_f_decomp_gram_f_eq (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (u : Fin (HM μ).m → ℝ) (k : Lab (HM μ).N) :
    gram ((HM μ).f k) u = gram (hvec HM μ k) u
      + ∑ i ∈ excited (Lab (HM μ).N), Chat (HM μ).N k i * gcoord HM μ u i := by
  rw [gram_f_decomp_f_eq HM μ k, gram_add_l, gram_sum_smul_l]
  simp only [gcoord]

/-! ## 5. The target -/

theorem gram_f_decomp_proof {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ)
    (k : Work.BoseBoxFock.Lab (HM μ).N) :
    Work.BoseB4.gram ((HM μ).f k) u
      = Work.BoseRowQ2.bfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u k
        + Work.BoseRowQ2.bpfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u k
        + ∑ l : Fin (HM μ).m,
            Work.BoseRowQ2.hvec HM μ k l * Work.BoseRowQ2.zvec HM μ u l := by
  have hA := gram_f_decomp_bfun_add_bpfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u k
  have hB := gram_f_decomp_gram_f_eq HM μ u k
  have hC := gram_f_decomp_gram_hvec_eq HM μ u k
  rw [hB, hC, hA]
  ring

end Work.BoseRowQ2
