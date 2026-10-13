/-
  WilE9 / Sharp — the chain rule for `eaD` under the pulled-back reindexing `pbRaise`.

  The pulled-back system is the stratum's system with its ambient coordinates `(y, τ, aux)`
  placed at `pbY`, `pbT`, `pbA` inside `ℝ^{Npb n m}` and with the chain `pbChain c` whose
  coefficients are the corresponding sums of the stratum's coefficients.  Consequently, for a
  polynomial `P` of the stratum the pulled-back polynomial `pbRaise P` is `P` with its variables
  renamed along `sIdxPb`, and every symbolic derivative of `pbRaise P` in a *pulled-back*
  direction is the sum of the derivatives of `P` in the stratum directions that map to it:

      `eaD (pbChain c) l (pbRaise P) = ∑_i [sIdxPb i = l] · pbRaise (eaD c i P)`

  which is the identity proved here, at the level of the evaluation points
  `pbEvalW c z = (z, exp ∘ (pbChain c).ell z)` and `pbEvalW0 c z = (pbStrat z, exp ∘ c.ell (pbStrat z))`
  (they correspond under the reindexing, `pbEvalW_comp`).

  The technical core is `eval_pderiv_rename_sum`: the chain rule
  `∂_k (P ∘ φ) = ∑_i (∂_i P ∘ φ) · [k = φ i]` for the formal partial derivatives of a
  multivariate polynomial, valid for an *arbitrary* (not necessarily injective) variable map `φ`;
  Mathlib only has the injective case (`MvPolynomial.pderiv_rename`).
-/
import Mathlib
import Submission.Work.WilE9.Sharp.PbSystem

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-! ## Evaluation of a partial derivative at one variable -/

private lemma eval_pderiv_X_aux {σ : Type*} [DecidableEq σ] (i j : σ) (u : σ → ℝ) :
    MvPolynomial.eval u (MvPolynomial.pderiv i (MvPolynomial.X j)) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; simp
  · simp [MvPolynomial.pderiv_X_of_ne (Ne.symm h), h]

/-! ## The chain rule for `pderiv` under `rename` -/

/-- **The chain rule for formal partial derivatives under a variable renaming.**
For an arbitrary map `φ : σ → τ` of variable indices and an evaluation point `v : τ → ℝ`,
the `k`-th partial derivative of `P.rename φ` is the sum of the `i`-th partial derivatives of
`P`, read at `v ∘ φ`, weighted by `[k = φ i]`.  No injectivity of `φ` is assumed. -/
private lemma eval_pderiv_rename_sum {σ τ : Type*} [Fintype σ] [DecidableEq τ]
    (φ : σ → τ) (k : τ) (P : MvPolynomial σ ℝ) (v : τ → ℝ) :
    MvPolynomial.eval v (MvPolynomial.pderiv k (MvPolynomial.rename φ P)) =
      ∑ i : σ, MvPolynomial.eval (v ∘ φ) (MvPolynomial.pderiv i P) *
        (if k = φ i then (1 : ℝ) else 0) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simp only [map_add, hp, hq, Finset.sum_add_distrib, MvPolynomial.eval_add, add_mul]
  | mul_X p j hp =>
      have hren : MvPolynomial.rename φ (p * MvPolynomial.X j)
          = MvPolynomial.rename φ p * MvPolynomial.X (φ j) := by
        rw [map_mul, MvPolynomial.rename_X]
      have hterm : ∀ i : σ, MvPolynomial.eval (v ∘ φ)
            (MvPolynomial.pderiv i (p * MvPolynomial.X j)) *
            (if k = φ i then (1:ℝ) else 0)
          = MvPolynomial.eval (v ∘ φ) (MvPolynomial.pderiv i p) * (v (φ j)) *
              (if k = φ i then (1:ℝ) else 0)
            + MvPolynomial.eval (v ∘ φ) p * (if i = j then (1:ℝ) else 0) *
              (if k = φ i then (1:ℝ) else 0) := by
        intro i
        rw [MvPolynomial.pderiv_mul, MvPolynomial.eval_add, MvPolynomial.eval_mul,
          MvPolynomial.eval_mul, MvPolynomial.eval_X, Function.comp_apply, eval_pderiv_X_aux]
        ring
      have hR : (∑ i : σ, MvPolynomial.eval (v ∘ φ)
              (MvPolynomial.pderiv i (p * MvPolynomial.X j)) *
            (if k = φ i then (1:ℝ) else 0))
          = (∑ i : σ, MvPolynomial.eval (v ∘ φ) (MvPolynomial.pderiv i p) *
                (if k = φ i then (1:ℝ) else 0)) * (v (φ j))
            + MvPolynomial.eval (v ∘ φ) p * (if k = φ j then (1:ℝ) else 0) := by
        rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_congr rfl (fun i _ => by ring : ∀ i ∈ Finset.univ,
              MvPolynomial.eval (v ∘ φ) (MvPolynomial.pderiv i p) * (v (φ j)) *
                (if k = φ i then (1:ℝ) else 0)
              = (MvPolynomial.eval (v ∘ φ) (MvPolynomial.pderiv i p) *
                (if k = φ i then (1:ℝ) else 0)) * (v (φ j))), ← Finset.sum_mul]
        · rw [Finset.sum_eq_single j]
          · rw [if_pos rfl]; ring
          · intro b _ hb
            rw [if_neg hb]; ring
          · intro hj; exact absurd (Finset.mem_univ j) hj
      rw [hren, MvPolynomial.pderiv_mul, MvPolynomial.eval_add, MvPolynomial.eval_mul,
        MvPolynomial.eval_mul, MvPolynomial.eval_X, eval_pderiv_X_aux, hp,
        MvPolynomial.eval_rename, hR]

/-! ## The reindexing data of the pulled-back system -/

/-- The variable map of `pbRaise`: the stratum's variable `i` is read at the pulled-back
coordinate `sIdxPb i`, the exponential atoms are untouched. -/
private def pbPhi (n m r : ℕ) : (Fin (n + (1 + m)) ⊕ Fin r) → (Fin (Npb n m) ⊕ Fin r) :=
  Sum.map (sIdxPb n m) id

private lemma pbRaise_eq_rename {n m r : ℕ} (P : EAPoly (n + (1 + m)) r) :
    pbRaise (n := n) (m := m) (r := r) P = P.rename (pbPhi n m r) := rfl

/-- The evaluation point of the pulled-back system: `pbChain c`'s branch map at `z`. -/
private def pbEvalW {n m r : ℕ} (c : EAChain (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ) :
    Fin (Npb n m) ⊕ Fin r → ℝ :=
  Sum.elim z (fun j => Real.exp ((pbChain c).ell j z))

/-- The evaluation point of the stratum's system: `c`'s branch map at `pbStrat z`. -/
private def pbEvalW0 {n m r : ℕ} (c : EAChain (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ) :
    Fin (n + (1 + m)) ⊕ Fin r → ℝ :=
  Sum.elim (pbStrat z) (fun j => Real.exp (c.ell j (pbStrat z)))

private lemma pbChain_ell_aux {n m r : ℕ} (c : EAChain (n + (1 + m)) r) (j : Fin r)
    (z : Fin (Npb n m) → ℝ) :
    (pbChain c).ell j z = c.ell j (pbStrat z) := by
  simp only [EAChain.ell, pbChain, pbStrat]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (sIdxPb n m i)]
  · simp
  · intro b _ hb; rw [if_neg (Ne.symm hb)]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The two evaluation points correspond under the reindexing `pbPhi`. -/
private lemma pbEvalW_comp {n m r : ℕ} (c : EAChain (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ) :
    pbEvalW c z ∘ pbPhi n m r = pbEvalW0 c z := by
  funext x
  cases x with
  | inl i => rfl
  | inr j =>
    simp only [Function.comp_apply, pbPhi, Sum.map_inr, id_eq, pbEvalW, pbEvalW0, Sum.elim_inr]
    rw [pbChain_ell_aux]

/-- The exponential part of the two evaluation points agrees at the atoms. -/
private lemma pbEvalW_inr {n m r : ℕ} (c : EAChain (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ)
    (j : Fin r) : pbEvalW c z (Sum.inr j) = pbEvalW0 c z (Sum.inr j) := by
  simp only [pbEvalW, pbEvalW0, Sum.elim_inr, pbChain_ell_aux]

/-! ## The pulled-back coefficients -/

private lemma pbChain_a_eq {n m r : ℕ} (c : EAChain (n + (1 + m)) r) (j : Fin r)
    (l : Fin (Npb n m)) :
    (pbChain c).a j l =
      ∑ i : Fin (n + (1 + m)), (if l = sIdxPb n m i then (1 : ℝ) else 0) * c.a j i := by
  simp only [pbChain]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : sIdxPb n m i = l
  · rw [if_pos h, if_pos h.symm, one_mul]
  · rw [if_neg h, if_neg (fun h' => h h'.symm), zero_mul]

/-! ## The chain rule for the pulled-back polynomials -/

/-- The `x`-directions: `∂` of `pbRaise P` in a pulled-back direction is the sum of the
stratum derivatives in the directions that `sIdxPb` sends to it. -/
private lemma eval_pderiv_inl_pbRaise {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (P : EAPoly (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ) (l : Fin (Npb n m)) :
    MvPolynomial.eval (pbEvalW c z) (MvPolynomial.pderiv (Sum.inl l) (pbRaise P))
      = ∑ i : Fin (n + (1 + m)), MvPolynomial.eval (pbEvalW0 c z)
            (MvPolynomial.pderiv (Sum.inl i) P) * (if l = sIdxPb n m i then (1:ℝ) else 0) := by
  rw [pbRaise_eq_rename,
    eval_pderiv_rename_sum (pbPhi n m r) (Sum.inl l) P (pbEvalW c z), pbEvalW_comp,
    Fintype.sum_sum_type]
  rw [show (∑ j : Fin r, MvPolynomial.eval (pbEvalW0 c z) (MvPolynomial.pderiv (Sum.inr j) P)
        * (if Sum.inl l = pbPhi n m r (Sum.inr j) then (1:ℝ) else 0)) = 0 from by
      simp only [pbPhi, Sum.map_inr, id_eq, Sum.inl_ne_inr, if_false, mul_zero,
        Finset.sum_const_zero], add_zero]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pbPhi, Sum.map_inl, Sum.inl.injEq]

/-- The `exp`-directions: `pbRaise` does not touch the atoms, so their derivatives agree. -/
private lemma eval_pderiv_inr_pbRaise {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (P : EAPoly (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ) (j : Fin r) :
    MvPolynomial.eval (pbEvalW c z) (MvPolynomial.pderiv (Sum.inr j) (pbRaise P))
      = MvPolynomial.eval (pbEvalW0 c z) (MvPolynomial.pderiv (Sum.inr j) P) := by
  rw [pbRaise_eq_rename,
    eval_pderiv_rename_sum (pbPhi n m r) (Sum.inr j) P (pbEvalW c z), pbEvalW_comp,
    Fintype.sum_sum_type]
  rw [show (∑ i : Fin (n + (1 + m)), MvPolynomial.eval (pbEvalW0 c z)
        (MvPolynomial.pderiv (Sum.inl i) P) *
        (if Sum.inr j = pbPhi n m r (Sum.inl i) then (1:ℝ) else 0)) = 0 from by
      simp only [pbPhi, Sum.map_inl, Sum.inr_ne_inl, if_false, mul_zero,
        Finset.sum_const_zero], zero_add]
  simp only [pbPhi, Sum.map_inr, id_eq, Sum.inr.injEq, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ j)]

/-! ## A linear-algebra normalisation -/

/-- Bookkeeping lemma: with `A j = ∑ i, m i * c i j` the two expressions
`∑_i F_i m_i + ∑_j A_j E_j G_j` and `∑_i m_i (F_i + ∑_j c_{ij} E_j G_j)` coincide. -/
private lemma sum_product_algebra {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι → ℝ) (G : κ → ℝ) (E : κ → ℝ) (m : ι → ℝ) (A : κ → ℝ) (cc : ι → κ → ℝ)
    (hA : ∀ j, A j = ∑ i, m i * cc i j) :
    (∑ i, F i * m i) + (∑ j, A j * E j * G j)
      = ∑ i, m i * (F i + ∑ j, cc i j * E j * G j) := by
  rw [Finset.sum_congr rfl (fun i _ => mul_add (m i) (F i) (∑ j, cc i j * E j * G j)),
    Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · have h1 : ∀ j, A j * E j * G j = ∑ i, (m i * cc i j) * (E j * G j) := by
      intro j
      rw [hA j, mul_assoc, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-! ## The main identity -/

theorem eaD_pbRaise {n m r : ℕ} (c : WilkiesDesign.E.EAChain (n + (1 + m)) r)
    (P : WilkiesDesign.E.EAPoly (n + (1 + m)) r) (z : Fin (Work.WilE9.Sharp.Npb n m) → ℝ)
    (l : Fin (Work.WilE9.Sharp.Npb n m)) :
    WilkiesDesign.E.eaEval (Work.WilE9.Sharp.pbChain c)
        (WilkiesDesign.E.eaD (Work.WilE9.Sharp.pbChain c) l (Work.WilE9.Sharp.pbRaise P)) z =
      ∑ i : Fin (n + (1 + m)),
        if Work.WilE9.Sharp.sIdxPb n m i = l then
          WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i P) (Work.WilE9.Sharp.pbStrat z)
        else 0 := by
  classical
  -- the pulled-back chain evaluated at `z`
  have hL : eaEval (pbChain c) (eaD (pbChain c) l (pbRaise P)) z
      = MvPolynomial.eval (pbEvalW c z) (MvPolynomial.pderiv (Sum.inl l) (pbRaise P))
        + ∑ j : Fin r, (pbChain c).a j l * pbEvalW c z (Sum.inr j) *
            MvPolynomial.eval (pbEvalW c z)
              (MvPolynomial.pderiv (Sum.inr j) (pbRaise P)) := by
    simp only [eaEval, pbEvalW, eaD, map_add, map_sum, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Sum.elim_inr]
  -- the stratum's chain evaluated at `pbStrat z`
  have hR : (∑ i : Fin (n + (1 + m)),
        if sIdxPb n m i = l then eaEval c (eaD c i P) (pbStrat z) else 0)
      = ∑ i : Fin (n + (1 + m)), (if l = sIdxPb n m i then (1 : ℝ) else 0) *
          (MvPolynomial.eval (pbEvalW0 c z) (MvPolynomial.pderiv (Sum.inl i) P)
            + ∑ j : Fin r, c.a j i * pbEvalW0 c z (Sum.inr j) *
                MvPolynomial.eval (pbEvalW0 c z)
                  (MvPolynomial.pderiv (Sum.inr j) P)) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : sIdxPb n m i = l
    · rw [if_pos h, if_pos h.symm, one_mul]
      simp only [eaEval, pbEvalW0, eaD, map_add, map_sum, map_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_X, Sum.elim_inr]
    · rw [if_neg h, if_neg (fun h' => h h'.symm), zero_mul]
  -- the two are the same expression
  have halg : (∑ i : Fin (n + (1 + m)), MvPolynomial.eval (pbEvalW0 c z)
          (MvPolynomial.pderiv (Sum.inl i) P) * (if l = sIdxPb n m i then (1 : ℝ) else 0))
        + (∑ j : Fin r, (pbChain c).a j l * pbEvalW0 c z (Sum.inr j) *
            MvPolynomial.eval (pbEvalW0 c z) (MvPolynomial.pderiv (Sum.inr j) P))
      = ∑ i : Fin (n + (1 + m)), (if l = sIdxPb n m i then (1 : ℝ) else 0) *
          (MvPolynomial.eval (pbEvalW0 c z) (MvPolynomial.pderiv (Sum.inl i) P)
            + ∑ j : Fin r, c.a j i * pbEvalW0 c z (Sum.inr j) *
                MvPolynomial.eval (pbEvalW0 c z)
                  (MvPolynomial.pderiv (Sum.inr j) P)) := by
    exact sum_product_algebra
      (fun i : Fin (n + (1 + m)) =>
        MvPolynomial.eval (pbEvalW0 c z) (MvPolynomial.pderiv (Sum.inl i) P))
      (fun j : Fin r => MvPolynomial.eval (pbEvalW0 c z) (MvPolynomial.pderiv (Sum.inr j) P))
      (fun j : Fin r => pbEvalW0 c z (Sum.inr j))
      (fun i : Fin (n + (1 + m)) => if l = sIdxPb n m i then (1 : ℝ) else 0)
      (fun j : Fin r => (pbChain c).a j l)
      (fun (i : Fin (n + (1 + m))) (j : Fin r) => c.a j i)
      (fun j => pbChain_a_eq c j l)
  rw [hL, hR]
  rw [eval_pderiv_inl_pbRaise]
  simp only [eval_pderiv_inr_pbRaise, pbEvalW_inr]
  exact halg

end Work.WilE9.Sharp
