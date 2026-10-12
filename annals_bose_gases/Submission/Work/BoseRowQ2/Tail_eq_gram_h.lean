import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.ValMinAbs
import Submission.Work.BoseRowQ2.maskTailDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.Tail_eq_gram_h` — the Gram form of the lattice tail matrix

The lattice tail matrix of the sharp mask row is

    `Tail N i j = Mc N i j − ∑ k : Lab N, Chat N k i · Chat N k j`,
    `Mc N i j = χ̂²(vec (K i − K j))`,   `Chat N k i = χ̂(vec (K k − K i))`
    (`K = labVec`).

This module identifies it with the *Gram product of the two deviations*

    `h_k := f_k − ∑_{s ≠ 0} Chat N k s · g_s`

of the honest mode family:  with `f` the χ-mode coordinates and `g` the θ-mode coordinates of
`HonestModes` (`⟨g_s, g_t⟩ = δ_{st}`, `⟨g_s, f_k⟩ = Chat N k s`,
`⟨f_i, f_j⟩ = Mc N i j − Chat N i 0 · Chat N j 0` — the last identity being the definition of
`ccrKernel` at the condensate label), the two `Fin m`-coordinate vectors `h_k`, `h_j` have Gram
product exactly `Tail N k j`:

    `Tail N k j = ∑_l (f k l − ∑_{i ≠ 0} Chat N k i · g i l) · (f j l − ∑_{i ≠ 0} Chat N j i · g i l)`.

The reason is that `∑_{s ≠ 0} Chat N k s · g_s` is the orthogonal projection of `f_k` onto the
θ-fibre `span{g_s : s ≠ 0}` (the `g_s` being orthonormal), so the deviation is orthogonal to that
fibre and

    `⟨h_k, h_j⟩ = ⟨f_k, f_j⟩ − ∑_{s ≠ 0} Chat N k s · Chat N j s`.

Adding back the missing label `0` through `⟨f_k, f_j⟩ = Mc N k j − Chat N k 0 · Chat N j 0` and the
symmetry of `Chat` turns this into `Mc N k j − ∑_{l : Lab N} Chat N l k · Chat N l j = Tail N k j`.

This is the identity `⟨h_k, h_j⟩ = Tail_{kj}` recorded in
`Submission/Work/BoseRowQ2/FINDING_rowGchiMaskSharp.md` §2, which the sharp mask row uses to
contract the Schwartz tail of `χ̂`; it is pure finite-dimensional algebra, no analysis.

## Contents

* the bilinearity of `Work.BoseB4.gram` on `Fin m → ℝ` (`gram_sub_l`, `gram_sub_r`,
  `gram_sum_smul_l`, `gram_sum_smul_r`) — private copies, since `Work.BoseB4` has only
  `gram_smul_smul`;
* `Tail_eq_gram_gen` — the identity for an abstract orthonormal θ-fibre;
* `honest_gram_f_Mc`, `honest_gram_gf`, `honest_gram_gg` — the three Gram pins of `HonestModes`
  in the `Mc`/`Chat` normalisation;
* `Tail_eq_gram_h` — the requested statement.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowQ2

open Work.BoseBoxFock

/-! ## 1. Bilinearity of the coordinate Gram product -/

private lemma gram_sub_l {m : ℕ} (a b c : Fin m → ℝ) :
    Work.BoseB4.gram (a - b) c = Work.BoseB4.gram a c - Work.BoseB4.gram b c := by
  simp only [Work.BoseB4.gram, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma gram_sub_r {m : ℕ} (a b c : Fin m → ℝ) :
    Work.BoseB4.gram a (b - c) = Work.BoseB4.gram a b - Work.BoseB4.gram a c := by
  simp only [Work.BoseB4.gram, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- `gram` is linear in its first argument over finite sums of rescaled vectors. -/
private lemma gram_sum_smul_l {m : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (h : ι → Fin m → ℝ) (z : Fin m → ℝ) :
    Work.BoseB4.gram (∑ i ∈ s, c i • h i) z
      = ∑ i ∈ s, c i * Work.BoseB4.gram (h i) z := by
  simp only [Work.BoseB4.gram, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- `gram` is linear in its second argument over finite sums of rescaled vectors. -/
private lemma gram_sum_smul_r {m : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (h : ι → Fin m → ℝ) (z : Fin m → ℝ) :
    Work.BoseB4.gram z (∑ i ∈ s, c i • h i)
      = ∑ i ∈ s, c i * Work.BoseB4.gram z (h i) := by
  simp only [Work.BoseB4.gram, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

/-! ## 2. The `Chat` calculus at the lattice labels -/

/-- `vec` is additive on differences of lattice vectors. -/
private theorem vec_sub_aux (a b : Fin 3 → ℤ) :
    Work.BoseB4.vec (a - b) = Work.BoseB4.vec a - Work.BoseB4.vec b := by
  ext i
  simp only [Work.BoseB4.vec, WithLp.ofLp_sub, WithLp.ofLp_toLp, Pi.sub_apply]
  push_cast
  ring

/-- The condensate label has vanishing lattice vector. -/
private theorem labVec_zero_aux (N : ℕ) :
    Work.BoseBoxFock.labVec N (0 : Lab N) = 0 := by
  funext i
  simp [Work.BoseBoxFock.labVec]

/-- `Chat N i 0 = χ̂(vec (K i))` (the condensate row of the θ/χ overlap matrix). -/
private theorem Chat_zero_aux (N : ℕ) (i : Lab N) :
    Chat N i 0 = chiHat (Work.BoseB4.vec (Work.BoseBoxFock.labVec N i)) := by
  rw [Chat, labVec_zero_aux, sub_zero]

/-- `ℓ • kmomLab ℓ N s = vec (K s)`: the box momentum of a label is its lattice vector. -/
private theorem smul_kmomLab_aux {ℓ : ℝ} (hℓ : ℓ ≠ 0) (N : ℕ) (s : Lab N) :
    ℓ • Work.BoseBoxFock.kmomLab ℓ N s = Work.BoseB4.vec (Work.BoseBoxFock.labVec N s) := by
  rw [Work.BoseBoxFock.kmomLab, smul_smul, mul_inv_cancel₀ hℓ, one_smul]

/-- **The momentum difference of two labels is the lattice vector of their difference**
(`ℓ = ellH v μ` is the box side; the honest momenta are `kmomLab`). -/
theorem ellH_smul_kmomLab_sub (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (N : ℕ)
    (k s : Lab N) :
    Work.BoseBoxFock.ellH v μ •
        (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k
          - Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s)
      = Work.BoseB4.vec (Work.BoseBoxFock.labVec N k - Work.BoseBoxFock.labVec N s) := by
  have hℓ : Work.BoseBoxFock.ellH v μ ≠ 0 := ne_of_gt (Work.BoseBoxFock.ellH_pos v μ)
  rw [smul_sub, smul_kmomLab_aux (ℓ := Work.BoseBoxFock.ellH v μ) hℓ N k,
    smul_kmomLab_aux (ℓ := Work.BoseBoxFock.ellH v μ) hℓ N s, ← vec_sub_aux]

/-- **`Chat` is symmetric** (the corpus `χ̂` is even). -/
theorem Chat_symm (N : ℕ) (i j : Lab N) : Chat N i j = Chat N j i := by
  rw [Chat, Chat]
  have h : Work.BoseB4.vec (Work.BoseBoxFock.labVec N j - Work.BoseBoxFock.labVec N i)
      = - Work.BoseB4.vec (Work.BoseBoxFock.labVec N i - Work.BoseBoxFock.labVec N j) := by
    rw [← Work.BoseBoxFock.vec_neg]
    congr 1
    ext t; simp [Pi.sub_apply]
  rw [h, chiHat_neg]

/-! ## 3. The Gram identity for an abstract orthonormal θ-fibre -/

/-- **The tail matrix is the Gram product of the two deviations.**  Let `f` be the χ-mode
coordinates and `g` the θ-mode coordinates of an `HonestModes`-type family in `Fin m → ℝ`, with
the three Gram pins `⟨f i, f j⟩ = Mc N i j − Chat N i 0 · Chat N j 0`,
`⟨g s, g t⟩ = δ_{st}` (`s, t ≠ 0`) and `⟨g s, f k⟩ = Chat N k s` (`s ≠ 0`).  Then, subtracting
from `f k` its orthogonal projection `∑_{s ≠ 0} Chat N k s · g s` onto the θ-fibre,

    `Tail N k j = ∑_l (f k l − ∑_{i ≠ 0} Chat N k i · g i l) · (f j l − ∑_{i ≠ 0} Chat N j i · g i l)`. -/
theorem Tail_eq_gram_gen {N : ℕ} {m : ℕ} (f g : Lab N → Fin m → ℝ)
    (hf : ∀ i j, Work.BoseB4.gram (f i) (f j) = Mc N i j - Chat N i 0 * Chat N j 0)
    (hg : ∀ s t, s ≠ 0 → t ≠ 0 →
      Work.BoseB4.gram (g s) (g t) = if s = t then (1 : ℝ) else 0)
    (hcross : ∀ s k, s ≠ 0 → Work.BoseB4.gram (g s) (f k) = Chat N k s)
    (k j : Lab N) :
    Tail N k j
      = ∑ l : Fin m, (f k l - ∑ i ∈ Work.BoseB7.excited (Lab N), Chat N k i * g i l)
        * (f j l - ∑ i ∈ Work.BoseB7.excited (Lab N), Chat N j i * g i l) := by
  set S : Finset (Lab N) := Work.BoseB7.excited (Lab N) with hS
  have hmem : ∀ i : Lab N, i ∈ S ↔ i ≠ 0 := by
    intro i
    rw [hS, Work.BoseB7.excited, Finset.mem_erase]
    simp
  have hne : ∀ i ∈ S, i ≠ 0 := fun i hi => (hmem i).1 hi
  -- the right-hand side is the Gram product of the deviations
  have hR : (∑ l : Fin m, (f k l - ∑ i ∈ S, Chat N k i * g i l)
        * (f j l - ∑ i ∈ S, Chat N j i * g i l))
      = Work.BoseB4.gram (f k - ∑ i ∈ S, Chat N k i • g i)
          (f j - ∑ i ∈ S, Chat N j i • g i) := by
    simp only [Work.BoseB4.gram, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hA : Work.BoseB4.gram (f k) (∑ i ∈ S, Chat N j i • g i)
      = ∑ i ∈ S, Chat N j i * Chat N k i := by
    rw [gram_sum_smul_r]
    exact Finset.sum_congr rfl fun i hi =>
      by rw [Work.BoseB4.gram_comm, hcross i k (hne i hi)]
  have hB : Work.BoseB4.gram (∑ i ∈ S, Chat N k i • g i) (f j)
      = ∑ i ∈ S, Chat N k i * Chat N j i := by
    rw [gram_sum_smul_l]
    exact Finset.sum_congr rfl fun i hi => by rw [hcross i j (hne i hi)]
  have hC : Work.BoseB4.gram (∑ i ∈ S, Chat N k i • g i) (∑ i ∈ S, Chat N j i • g i)
      = ∑ i ∈ S, Chat N k i * Chat N j i := by
    rw [gram_sum_smul_l]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [gram_sum_smul_r]
    rw [Finset.sum_eq_single i]
    · rw [hg i i (hne i hi) (hne i hi)]
      simp
    · intro b hb hbi
      rw [hg i b (hne i hi) (hne b hb), if_neg (fun h : i = b => hbi h.symm)]
      ring
    · intro hi'
      exact absurd hi hi'
  have hcombo : Work.BoseB4.gram (f k - ∑ i ∈ S, Chat N k i • g i)
        (f j - ∑ i ∈ S, Chat N j i • g i)
      = Work.BoseB4.gram (f k) (f j) - ∑ i ∈ S, Chat N k i * Chat N j i := by
    rw [gram_sub_l, gram_sub_r, gram_sub_r, hA, hB, hC]
    have hswap : (∑ i ∈ S, Chat N j i * Chat N k i)
        = ∑ i ∈ S, Chat N k i * Chat N j i :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [hswap]
    ring
  -- the left-hand side, with the condensate label `0` restored
  have hMc : Mc N k j = Work.BoseB4.gram (f k) (f j) + Chat N k 0 * Chat N j 0 := by
    linarith [hf k j]
  have hsplit : (∑ i : Lab N, Chat N i k * Chat N i j)
      = Chat N k 0 * Chat N j 0 + ∑ i ∈ S, Chat N k i * Chat N j i := by
    have h1 : (∑ i ∈ S, Chat N i k * Chat N i j) + Chat N 0 k * Chat N 0 j
        = ∑ i : Lab N, Chat N i k * Chat N i j := by
      rw [hS, Work.BoseB7.excited]
      exact Finset.sum_erase_add _ _ (Finset.mem_univ 0)
    have h2 : (∑ x ∈ S, Chat N x k * Chat N x j) = ∑ x ∈ S, Chat N k x * Chat N j x :=
      Finset.sum_congr rfl fun x _ => by rw [Chat_symm N x k, Chat_symm N x j]
    have h3 : Chat N 0 k * Chat N 0 j = Chat N k 0 * Chat N j 0 := by
      rw [Chat_symm N 0 k, Chat_symm N 0 j]
    rw [h2, h3] at h1
    linarith [h1]
  have hL : Tail N k j
      = Work.BoseB4.gram (f k) (f j) - ∑ i ∈ S, Chat N k i * Chat N j i := by
    simp only [Tail]
    rw [hMc, hsplit]
    ring
  rw [hL, hR, hcombo]

/-! ## 4. The three Gram pins of the honest mode family -/

/-- **The χ-mode Gram pin**: `⟨f i, f j⟩ = Mc N i j − Chat N i 0 · Chat N j 0`.  This is
`HonestModes.hf` with the box kernel `ccrKernel` written in the lattice vocabulary. -/
theorem honest_gram_f_Mc {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (HM : Work.BoseBoxFock.HonestModes v μ) (i j : Lab HM.N) :
    Work.BoseB4.gram (HM.f i) (HM.f j) = Mc HM.N i j - Chat HM.N i 0 * Chat HM.N j 0 := by
  have hℓ : Work.BoseBoxFock.ellH v μ ≠ 0 := ne_of_gt (Work.BoseBoxFock.ellH_pos v μ)
  rw [HM.hf i j, Work.BoseB7.ccrKernel, ellH_smul_kmomLab_sub v μ HM.N i j,
    smul_kmomLab_aux (ℓ := Work.BoseBoxFock.ellH v μ) hℓ HM.N i,
    smul_kmomLab_aux (ℓ := Work.BoseBoxFock.ellH v μ) hℓ HM.N j,
    Chat_zero_aux HM.N i, Chat_zero_aux HM.N j]
  simp only [Mc, chiHatSq, chiHat]

/-- **The θ/χ cross Gram pin**: `⟨g s, f k⟩ = Chat N k s` for `s ≠ 0`. -/
theorem honest_gram_gf {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (HM : Work.BoseBoxFock.HonestModes v μ) (s k : Lab HM.N) :
    Work.BoseB4.gram (HM.g s) (HM.f k) = Chat HM.N k s := by
  rw [HM.hcross s k, ellH_smul_kmomLab_sub v μ HM.N k s]
  rfl

/-- **The θ-fibre Gram pin**: `⟨g s, g t⟩ = δ_{st}` on the excited labels. -/
theorem honest_gram_gg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (HM : Work.BoseBoxFock.HonestModes v μ) (s t : Lab HM.N) (hs : s ≠ 0) (ht : t ≠ 0) :
    Work.BoseB4.gram (HM.g s) (HM.g t) = if s = t then (1 : ℝ) else 0 :=
  HM.hg s t hs ht

/-- **The requested statement**: the lattice tail matrix is the Gram product of the deviations
of the χ-modes from the (θ-fibre) condensate. -/
theorem Tail_eq_gram_h {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ)
    (k j : Work.BoseBoxFock.Lab (HM μ).N) :
    Work.BoseRowQ2.Tail (HM μ).N k j
      = ∑ l : Fin (HM μ).m,
          ((HM μ).f k l - ∑ i ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
              Work.BoseRowQ2.Chat (HM μ).N k i * (HM μ).g i l)
          * ((HM μ).f j l - ∑ i ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
              Work.BoseRowQ2.Chat (HM μ).N j i * (HM μ).g i l) :=
  Tail_eq_gram_gen (N := (HM μ).N) (m := (HM μ).m) (HM μ).f (HM μ).g
    (fun i j => honest_gram_f_Mc (HM μ) i j)
    (fun s t hs ht => honest_gram_gg (HM μ) s t hs ht)
    (fun s k' _ => honest_gram_gf (HM μ) s k') k j

end Work.BoseRowQ2
