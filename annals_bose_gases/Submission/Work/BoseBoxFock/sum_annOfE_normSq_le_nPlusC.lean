import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.kafzFockBounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sum_annOfE_normSq_le_nPlusC`

Bessel-type bound for the superposed annihilation operators of an **orthonormal family**
of one-particle modes in the spectator Fock space `cfock (Excited m)`:

`Σ_{s∈S} ‖a(φ_s) w‖² ≤ ⟪w, n₊ w⟫`  for `φ : X → Fin m → ℝ` with `gram (φ s) (φ t) = δ_{st}`.

## The argument

1. **The coordinate family.**  `evVec w : Fin m → cfock (Excited m)` is `a_l w` in the
   excited coordinate `l` and `0` in the condensate coordinate.  It is the section of the
   map `φ ↦ annOfE φ w` along the coordinate functions: `∑_l φ_l • evVec w l = annOfE φ w`
   (`evVec_sum_smul`), and `∑_l ‖evVec w l‖² = ⟪w, n₊ w⟫` (`evVec_sum_normSq`).

2. **Bessel for an orthonormal family** (`orthFam_sumNormSq_le_fin`).  If
   `ψ : κ → Fin m → ℝ` has orthonormal Gram matrix and `u : Fin m → H`, then
   `Σ_s ‖Σ_l ψ_s(l) • u_l‖² ≤ Σ_l ‖u_l‖²`.  The proof expands the left side as the
   quadratic form of the Gram matrix `G_{ll'} = Σ_s ψ_s(l) ψ_s(l')` of the family
   (`inner_smul_sum_re`), and writes the complementary projection as a sum of squares:
   with `W_{pl} = δ_{lp} − G_{lp}`, the idempotency
   `Σ_p W_{pl} W_{pl'} = (δ − G)_{ll'}` (`BoseB4.bessel_gram_factor`) gives
   `Σ_{ll'} (δ − G)_{ll'} ⟪u_l, u_{l'}⟫ = Σ_p ‖Σ_l W_{pl} • u_l‖² ≥ 0`, i.e. the
   quadratic form of `G` is at most `Σ_l ‖u_l‖²`.

3. Feeding `ψ := φ`, `u := evVec w` into (2) (with `κ` the subtype `{s // s ∈ S}`) and
   using (1) gives the theorem.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

/-! ## 1. The coordinate family of `cfock (Excited m)` -/

/-- The coordinate decomposition of the spectator Fock space `cfock (Excited m)`:
`evVec w l` is `a_l w` in the excited coordinate `l` and `0` in the condensate
coordinate `0`.  It is the section of `φ ↦ annOfE φ w` along the coordinate functions,
`∑_l φ_l • evVec w l = annOfE φ w` (`evVec_sum_smul`). -/
noncomputable def evVec {m : ℕ} [NeZero m] (w : cfock (Excited m)) :
    Fin m → cfock (Excited m) :=
  fun l => if h : l = 0 then 0 else annC (Excited m) ⟨l, h⟩ w

@[simp] lemma evVec_zero {m : ℕ} [NeZero m] (w : cfock (Excited m)) : evVec w 0 = 0 := by
  simp [evVec]

lemma evVec_excited {m : ℕ} [NeZero m] (w : cfock (Excited m)) (l : Excited m) :
    evVec w l.1 = annC (Excited m) l w := by
  rw [evVec, dif_neg l.2]

lemma evVec_sum_smul {m : ℕ} [NeZero m] (φ : Fin m → ℝ) (w : cfock (Excited m)) :
    (∑ l : Fin m, ((φ l : ℝ) : ℂ) • evVec w l) = annOfE φ w := by
  rw [sum_univ_eq_zero_add (fun l => ((φ l : ℝ) : ℂ) • evVec w l)]
  rw [evVec_zero, smul_zero, zero_add]
  rw [kfb_annOfE_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [evVec_excited w l]

lemma evVec_sum_normSq {m : ℕ} [NeZero m] (w : cfock (Excited m)) :
    (∑ l : Fin m, ‖evVec w l‖ ^ 2) = (inner ℂ w (nPlusC w)).re := by
  rw [kfb_re_inner_nPlusC_self]
  rw [sum_univ_eq_zero_add (fun l => ‖evVec w l‖ ^ 2)]
  rw [evVec_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [evVec_excited w l]

/-- `‖x‖²` is the real part of `⟪x, x⟫` in the spectator space. -/
lemma evVec_normSq_eq_re_inner {X : Type*} [DecidableEq X] (x : cfock X) :
    ‖x‖ ^ 2 = (inner ℂ x x).re := by
  rw [kfb_inner_self_re, Complex.ofReal_re]

/-! ## 2. Bessel's inequality for an orthonormal family of real coordinate vectors -/

/-- The sesquilinear expansion of a pairing of two superpositions, with **real**
coefficients: the quadratic form of the rank-one matrix `a bᵀ`. -/
lemma inner_smul_sum_re {ι : Type*} [Fintype ι] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (a b : ι → ℝ) (u : ι → H) :
    (inner ℂ (∑ l, ((a l : ℝ) : ℂ) • u l) (∑ l, ((b l : ℝ) : ℂ) • u l)).re
      = ∑ l, ∑ l', a l * b l' * (inner ℂ (u l) (u l')).re := by
  rw [sum_inner, Complex.re_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Bessel's inequality for an orthonormal family of real coordinate vectors.**
If `∑_l ψ_s(l) ψ_t(l) = δ_{st}`, then for every family of vectors `u` of a complex
Hilbert space, `Σ_s ‖Σ_l ψ_s(l) • u_l‖² ≤ Σ_l ‖u_l‖²`.

The left side is the quadratic form of the Gram matrix `G_{ll'} = Σ_s ψ_s(l)ψ_s(l')` of
the family, which is the orthogonal projection onto `span{ψ_s}`; the difference
`δ − G` is the complementary projection, written as a sum of squares with
`Work.BoseB4.bessel_gram_factor`. -/
lemma orthFam_sumNormSq_le_fin {m : ℕ} [NeZero m] {κ : Type*} [Fintype κ]
    [DecidableEq κ] (ψ : κ → Fin m → ℝ)
    (hψ : ∀ s t, ∑ l : Fin m, ψ s l * ψ t l = if s = t then 1 else 0)
    (u : Fin m → cfock (Excited m)) :
    (∑ s : κ, ‖∑ l : Fin m, ((ψ s l : ℝ) : ℂ) • u l‖ ^ 2) ≤ ∑ l : Fin m, ‖u l‖ ^ 2 := by
  classical
  -- the Gram matrix of the family and the columns of the complementary projection
  set P : Fin m → Fin m → ℝ := fun l l' => ∑ s : κ, ψ s l * ψ s l' with hPdef
  set W : Fin m → Fin m → ℝ :=
    fun p l => (if l = p then (1 : ℝ) else 0) - ∑ s : κ, ψ s l * ψ s p with hWdef
  -- `δ - G` is a sum of rank-one matrices
  have hfac : ∀ l l',
      (if l = l' then (1 : ℝ) else 0) - P l l' = ∑ p : Fin m, W p l * W p l' := by
    intro l l'
    rw [hPdef, hWdef]
    exact (bessel_gram_factor ψ Finset.univ (fun s _ t _ => hψ s t) l l').symm
  -- the left side is the quadratic form of `P`
  have hL : (∑ s : κ, ‖∑ l : Fin m, ((ψ s l : ℝ) : ℂ) • u l‖ ^ 2)
      = ∑ l, ∑ l', P l l' * (inner ℂ (u l) (u l')).re := by
    have h1 : ∀ s : κ, ‖∑ l : Fin m, ((ψ s l : ℝ) : ℂ) • u l‖ ^ 2
        = ∑ l, ∑ l', ψ s l * ψ s l' * (inner ℂ (u l) (u l')).re := by
      intro s
      rw [evVec_normSq_eq_re_inner, inner_smul_sum_re (ψ s) (ψ s) u]
    rw [Finset.sum_congr rfl (fun s _ => h1 s)]
    conv_rhs => rw [hPdef]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [Finset.sum_mul]
  -- the right side is the quadratic form of the identity matrix
  have hR : (∑ l : Fin m, ‖u l‖ ^ 2)
      = ∑ l, ∑ l', (if l = l' then (1 : ℝ) else 0) * (inner ℂ (u l) (u l')).re := by
    have h1 : ∀ l : Fin m,
        (∑ l' : Fin m, (if l = l' then (1 : ℝ) else 0) * (inner ℂ (u l) (u l')).re)
          = ‖u l‖ ^ 2 := by
      intro l
      rw [evVec_normSq_eq_re_inner]
      rw [Finset.sum_congr rfl (fun l' _ => by rw [ite_mul, one_mul, zero_mul])]
      rw [Finset.sum_ite_eq Finset.univ l (fun l' => (inner ℂ (u l) (u l')).re)]
      simp
    rw [← Finset.sum_congr rfl (fun l _ => h1 l)]
  -- the quadratic form of `δ - P` is a sum of squares, hence nonnegative
  have hnonneg : 0 ≤ ∑ l, ∑ l',
      ((if l = l' then (1 : ℝ) else 0) - P l l') * (inner ℂ (u l) (u l')).re := by
    calc 0 ≤ ∑ p : Fin m, ‖∑ l : Fin m, ((W p l : ℝ) : ℂ) • u l‖ ^ 2 :=
          Finset.sum_nonneg fun p _ => sq_nonneg _
      _ = ∑ p : Fin m, (∑ l, ∑ l', W p l * W p l' * (inner ℂ (u l) (u l')).re) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [evVec_normSq_eq_re_inner, inner_smul_sum_re (W p) (W p) u]
      _ = ∑ l, ∑ l',
            ((if l = l' then (1 : ℝ) else 0) - P l l') * (inner ℂ (u l) (u l')).re := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l' _ => ?_
          rw [← Finset.sum_mul, ← hfac l l']
  -- split the quadratic form of `δ - P`
  have hsplit : (∑ l, ∑ l',
        ((if l = l' then (1 : ℝ) else 0) - P l l') * (inner ℂ (u l) (u l')).re)
      = (∑ l, ∑ l', (if l = l' then (1 : ℝ) else 0) * (inner ℂ (u l) (u l')).re)
        - ∑ l, ∑ l', P l l' * (inner ℂ (u l) (u l')).re := by
    have hinner : ∀ l : Fin m,
        (∑ l', ((if l = l' then (1 : ℝ) else 0) - P l l') * (inner ℂ (u l) (u l')).re)
          = (∑ l', (if l = l' then (1 : ℝ) else 0) * (inner ℂ (u l) (u l')).re)
            - ∑ l', P l l' * (inner ℂ (u l) (u l')).re := by
      intro l
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l' _ => by rw [sub_mul]
    rw [Finset.sum_congr rfl (fun l _ => hinner l), Finset.sum_sub_distrib]
  have hle : (∑ l, ∑ l', P l l' * (inner ℂ (u l) (u l')).re)
      ≤ ∑ l, ∑ l', (if l = l' then (1 : ℝ) else 0) * (inner ℂ (u l) (u l')).re := by
    rw [hsplit] at hnonneg
    linarith
  rw [hL, hR]
  exact hle

/-! ## 3. The main theorem -/

theorem sum_annOfE_normSq_le_nPlusC {m : ℕ} [NeZero m] {X : Type*} [DecidableEq X]
    (S : Finset X) (φ : X → Fin m → ℝ)
    (h : ∀ s ∈ S, ∀ t ∈ S, Work.BoseB4.gram (φ s) (φ t) = if s = t then 1 else 0)
    (w : Work.BoseB4.cfock (Work.BoseB4.Excited m)) :
    (∑ s ∈ S, ‖Work.BoseBoxFock.annOfE (φ s) w‖ ^ 2)
      ≤ (inner ℂ w (Work.BoseBoxFock.nPlusC (m := m) w)).re := by
  classical
  -- the orthonormality hypothesis, reindexed by the subtype `{s // s ∈ S}`
  have hgram : ∀ s t : {s // s ∈ S},
      ∑ l : Fin m, φ s.1 l * φ t.1 l = if s = t then 1 else 0 := by
    intro s t
    have hs := h s.1 s.2 t.1 t.2
    rw [gram] at hs
    have hst : (if s = t then (1 : ℝ) else 0)
        = (if (s.1 : X) = t.1 then (1 : ℝ) else 0) := by
      by_cases hh : s = t
      · subst hh; simp
      · have hh' : ¬ (s.1 = t.1) := fun hc => hh (Subtype.ext hc)
        simp [hh, hh']
    rw [hst, ← hs]
  -- Bessel for the orthonormal family, applied to the coordinate family `evVec w`
  have key := orthFam_sumNormSq_le_fin (fun s : {s // s ∈ S} => φ s.1) hgram (evVec w)
  rw [Finset.sum_congr rfl (fun s _ => by rw [evVec_sum_smul (φ s.1) w])] at key
  rw [evVec_sum_normSq w] at key
  rw [Finset.sum_subtype S (fun x => Iff.rfl) (fun s => ‖annOfE (φ s) w‖ ^ 2)]
  exact key

end Work.BoseBoxFock
