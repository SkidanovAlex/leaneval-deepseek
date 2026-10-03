import Mathlib
import Submission.Work.Peluse.Ulower.iterDefs
import Submission.Work.Peluse.Ulower.rankInduction
import Submission.Work.Peluse.Ulower.boxSumPow_split

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## The tuple of shifts cut out by the peeling -/

/-- A tuple of pairs of elements of `A`, read as a tuple of integer pairs. -/
private def pairV {A : Finset ℤ} {k : ℕ} (t : Fin k → ↥A × ↥A) : Fin k → ℤ × ℤ :=
  fun i => ((t i).1.1, (t i).2.1)

private lemma pairV_cons {A : Finset ℤ} {k : ℕ} (q : ↥A × ↥A) (t : Fin k → ↥A × ↥A) :
    pairV (Fin.cons q t) = Fin.cons (q.1.1, q.2.1) (pairV t) := by
  funext i
  cases i using Fin.cases <;> simp [pairV, Fin.cons_zero, Fin.cons_succ]

/-! ## Finite support is preserved -/

private lemma finSuppZ_DeltaP {a b : ℤ} {G : ℤ → ℂ} (h : Work.Peluse.FinSuppZ G) :
    Work.Peluse.FinSuppZ (Work.Peluse.DeltaP a b G) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + a.natAbs + b.natAbs, fun x hx => ?_⟩
  have hxa : G (x + a) = 0 := by
    refine hN _ ?_
    have htri : x.natAbs ≤ (x + a).natAbs + a.natAbs := by
      have h := Int.natAbs_add_le (x + a) (-a)
      rw [Int.natAbs_neg] at h
      simpa using h
    omega
  simp [Work.Peluse.DeltaP, hxa]

private lemma finSuppZ_iterDelta' : ∀ (k : ℕ) (sh : Fin k → ℤ × ℤ) (F : ℤ → ℂ),
    Work.Peluse.FinSuppZ F → Work.Peluse.FinSuppZ (Work.Peluse.Ulower.iterDelta' k sh F) := by
  intro k
  induction k with
  | zero => intro sh F h; exact h
  | succ k ih =>
      intro sh F h
      rw [show Work.Peluse.Ulower.iterDelta' (k + 1) sh F
          = Work.Peluse.DeltaP (sh 0).1 (sh 0).2
              (Work.Peluse.Ulower.iterDelta' k (fun i => sh i.succ) F) from rfl]
      exact finSuppZ_DeltaP (ih (fun i => sh i.succ) F h)

/-! ## Commutation of the peel step with the iterated difference -/

private lemma DeltaP_comm (a b c d : ℤ) (F : ℤ → ℂ) :
    Work.Peluse.DeltaP a b (Work.Peluse.DeltaP c d F)
      = Work.Peluse.DeltaP c d (Work.Peluse.DeltaP a b F) := by
  funext x
  simp only [Work.Peluse.DeltaP, star_mul, star_star]
  ring_nf

private lemma DeltaP_iterDelta'_comm (a b : ℤ) : ∀ (k : ℕ) (sh : Fin k → ℤ × ℤ) (F : ℤ → ℂ),
    Work.Peluse.Ulower.iterDelta' k sh (Work.Peluse.DeltaP a b F)
      = Work.Peluse.DeltaP a b (Work.Peluse.Ulower.iterDelta' k sh F) := by
  intro k
  induction k with
  | zero => intro sh F; rfl
  | succ k ih =>
      intro sh F
      rw [show Work.Peluse.Ulower.iterDelta' (k + 1) sh (Work.Peluse.DeltaP a b F)
            = Work.Peluse.DeltaP (sh 0).1 (sh 0).2
                (Work.Peluse.Ulower.iterDelta' k (fun i => sh i.succ) (Work.Peluse.DeltaP a b F))
            from rfl,
        ih (fun i => sh i.succ) F]
      rw [show Work.Peluse.DeltaP (sh 0).1 (sh 0).2
            (Work.Peluse.DeltaP a b (Work.Peluse.Ulower.iterDelta' k (fun i => sh i.succ) F))
          = Work.Peluse.DeltaP a b (Work.Peluse.DeltaP (sh 0).1 (sh 0).2
              (Work.Peluse.Ulower.iterDelta' k (fun i => sh i.succ) F)) from
        DeltaP_comm (sh 0).1 (sh 0).2 a b (Work.Peluse.Ulower.iterDelta' k (fun i => sh i.succ) F)]
      rfl

private lemma iterDelta'_cons (k : ℕ) (q : ℤ × ℤ) (sh : Fin k → ℤ × ℤ) (F : ℤ → ℂ) :
    Work.Peluse.DeltaP q.1 q.2 (Work.Peluse.Ulower.iterDelta' k sh F)
      = Work.Peluse.Ulower.iterDelta' (k + 1)
          (Fin.cons (α := fun _ : Fin (k + 1) => ℤ × ℤ) q sh) F := by
  have htail : (fun i : Fin k =>
      (Fin.cons (α := fun _ : Fin (k + 1) => ℤ × ℤ) q sh) i.succ) = sh := by
    funext i
    rw [Fin.cons_succ]
  have h0 : (((Fin.cons (α := fun _ : Fin (k + 1) => ℤ × ℤ) q sh :
      Fin (k + 1) → ℤ × ℤ)) 0).1 = q.1 := by rw [Fin.cons_zero]
  have h0' : (((Fin.cons (α := fun _ : Fin (k + 1) => ℤ × ℤ) q sh :
      Fin (k + 1) → ℤ × ℤ)) 0).2 = q.2 := by rw [Fin.cons_zero]
  funext x
  show Work.Peluse.DeltaP q.1 q.2 (Work.Peluse.Ulower.iterDelta' k sh F) x = _
  rw [show Work.Peluse.Ulower.iterDelta' (k + 1)
        (Fin.cons (α := fun _ : Fin (k + 1) => ℤ × ℤ) q sh) F
      = fun x => star (Work.Peluse.Ulower.iterDelta' k (fun i =>
            (Fin.cons (α := fun _ : Fin (k + 1) => ℤ × ℤ) q sh) i.succ) F
              (x + (((Fin.cons (α := fun _ : Fin (k + 1) => ℤ × ℤ) q sh :
                Fin (k + 1) → ℤ × ℤ)) 0).1)) *
          Work.Peluse.Ulower.iterDelta' k (fun i =>
            (Fin.cons (α := fun _ : Fin (k + 1) => ℤ × ℤ) q sh) i.succ) F
              (x + (((Fin.cons (α := fun _ : Fin (k + 1) => ℤ × ℤ) q sh :
                Fin (k + 1) → ℤ × ℤ)) 0).2) from rfl,
    htail, h0, h0']
  simp only [Work.Peluse.DeltaP]

/-! ## Reindexing `Fin.cons` -/

private lemma sum_over_cons {k : ℕ} {A : Finset ℤ} {M : Type*} [AddCommMonoid M]
    (g : (Fin (k + 1) → ↥A × ↥A) → M) :
    (∑ q : ↥A × ↥A, ∑ t : Fin k → ↥A × ↥A, g (Fin.cons q t))
      = ∑ u : Fin (k + 1) → ↥A × ↥A, g u := by
  have h1 : (∑ q : ↥A × ↥A, ∑ t : Fin k → ↥A × ↥A, g (Fin.cons q t))
      = ∑ x : (↥A × ↥A) × (Fin k → ↥A × ↥A), g (Fin.cons x.1 x.2) :=
    (Fintype.sum_prod_type (f := fun x : (↥A × ↥A) × (Fin k → ↥A × ↥A) =>
      g (Fin.cons x.1 x.2))).symm
  rw [h1]
  refine Finset.sum_bij (fun x _ => Fin.cons x.1 x.2) (fun x _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro x₁ _ x₂ _ h
    refine Prod.ext ?_ ?_
    · have h0 := congrFun h 0
      simpa [Fin.cons_zero] using h0
    · funext i
      have hi := congrFun h i.succ
      simpa [Fin.cons_succ] using hi
  · intro u _
    exact ⟨(u 0, fun i => u i.succ), Finset.mem_univ _, Fin.cons_self_tail u⟩
  · intro x _
    rfl

/-! ## The iterated peel identity at the level of the complex box sum -/

private lemma boxSumPow_peel_iter' : ∀ (k : ℕ) (A S : Finset ℤ) (F : ℤ → ℂ),
    Work.Peluse.boxSumPow (k + 2) (fun _ : Fin (k + 2) => A) S F
      = ((((A.card : ℂ)) ^ 2)⁻¹) ^ k *
        ∑ t : Fin k → ↥A × ↥A, Work.Peluse.boxSumPow 2 (fun _ : Fin 2 => A) S
          (Work.Peluse.Ulower.iterDelta' k (pairV t) F) := by
  intro k
  induction k with
  | zero =>
      intro A S F
      rw [pow_zero, one_mul]
      have hsum : (∑ t : Fin 0 → ↥A × ↥A, Work.Peluse.boxSumPow 2 (fun _ : Fin 2 => A) S
          (Work.Peluse.Ulower.iterDelta' 0 (pairV t) F))
          = Work.Peluse.boxSumPow 2 (fun _ : Fin 2 => A) S F := by
        rw [Finset.sum_congr rfl (fun t _ => by
          rw [show Work.Peluse.Ulower.iterDelta' 0 (pairV t) F = F from rfl])]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
        simp
      rw [hsum]
  | succ k ih =>
      intro A S F
      have hsplit : Work.Peluse.boxSumPow (k + 1 + 2) (fun _ : Fin (k + 1 + 2) => A) S F
          = (((A.card : ℂ)) ^ 2)⁻¹ *
            ∑ a : ↥A, ∑ b : ↥A, Work.Peluse.boxSumPow (k + 2) (fun _ : Fin (k + 2) => A) S
              (Work.Peluse.DeltaP a.1 b.1 F) := by
        have h := Work.Peluse.Ulower.boxSumPow_split (k + 2) (fun _ : Fin (k + 2 + 1) => A) S F
        simpa using h
      rw [hsplit]
      have hstep : ∀ (a b : ↥A) (t : Fin k → ↥A × ↥A),
          Work.Peluse.Ulower.iterDelta' k (pairV t) (Work.Peluse.DeltaP a.1 b.1 F)
            = Work.Peluse.Ulower.iterDelta' (k + 1) (pairV (Fin.cons (a, b) t)) F := by
        intro a b t
        rw [DeltaP_iterDelta'_comm a.1 b.1 k (pairV t) F, pairV_cons]
        exact iterDelta'_cons k (a.1, b.1) (pairV t) F
      rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
        ih A S (Work.Peluse.DeltaP a.1 b.1 F)))]
      simp only [← Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
        Finset.sum_congr rfl (fun t _ =>
          congrArg (fun G => Work.Peluse.boxSumPow 2 (fun _ : Fin 2 => A) S G)
            (hstep a b t))))]
      have hmid : (∑ a : ↥A, ∑ b : ↥A, ∑ t : Fin k → ↥A × ↥A,
            Work.Peluse.boxSumPow 2 (fun _ : Fin 2 => A) S
              (Work.Peluse.Ulower.iterDelta' (k + 1) (pairV (Fin.cons (a, b) t)) F))
          = ∑ u : Fin (k + 1) → ↥A × ↥A, Work.Peluse.boxSumPow 2 (fun _ : Fin 2 => A) S
              (Work.Peluse.Ulower.iterDelta' (k + 1) (pairV u) F) := by
        refine (Fintype.sum_prod_type (f := fun q : ↥A × ↥A => ∑ t : Fin k → ↥A × ↥A,
          Work.Peluse.boxSumPow 2 (fun _ : Fin 2 => A) S
            (Work.Peluse.Ulower.iterDelta' (k + 1) (pairV (Fin.cons q t)) F))).symm.trans ?_
        exact sum_over_cons (g := fun u : Fin (k + 1) → ↥A × ↥A =>
          Work.Peluse.boxSumPow 2 (fun _ : Fin 2 => A) S
            (Work.Peluse.Ulower.iterDelta' (k + 1) (pairV u) F))
      rw [hmid, pow_succ]
      ring

/-! ## Norms -/

private lemma norm_sum_ofReal {ι : Type*} [Fintype ι] (r : ι → ℝ) (h : ∀ i, 0 ≤ r i) :
    ‖∑ i, ((r i : ℝ) : ℂ)‖ = ∑ i, r i := by
  rw [← Complex.ofReal_sum, Complex.norm_of_nonneg (Finset.sum_nonneg (fun i _ => h i))]

/-! ## The `piFinset` reindexing -/

private lemma sum_piFinset_prod {k : ℕ} (A : Finset ℤ) (g : (Fin k → ℤ × ℤ) → ℝ) :
    (∑ H ∈ Fintype.piFinset (fun _ : Fin k => A.product A), g H)
      = ∑ t : Fin k → ↥A × ↥A, g (fun i => ((t i).1.1, (t i).2.1)) := by
  classical
  refine Finset.sum_bij
    (fun (H : Fin k → ℤ × ℤ) (hH : H ∈ Fintype.piFinset (fun _ : Fin k => A.product A)) =>
      (fun i : Fin k =>
        (⟨(H i).1, (Finset.mem_product.mp (Fintype.mem_piFinset.mp hH i)).1⟩,
         ⟨(H i).2, (Finset.mem_product.mp (Fintype.mem_piFinset.mp hH i)).2⟩)))
    (fun H hH => Finset.mem_univ _) ?_ ?_ ?_
  · intro H₁ h₁ H₂ h₂ h
    funext i
    have hi := congrFun h i
    have h1 : ((H₁ i).1 : ℤ) = (H₂ i).1 := by
      have := congrArg (fun p : ↥A × ↥A => (p.1 : ℤ)) hi
      simpa using this
    have h2 : ((H₁ i).2 : ℤ) = (H₂ i).2 := by
      have := congrArg (fun p : ↥A × ↥A => (p.2 : ℤ)) hi
      simpa using this
    exact Prod.ext h1 h2
  · intro t _
    refine ⟨(fun i => ((t i).1.1, (t i).2.1)), ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      exact Finset.mem_product.mpr ⟨(t i).1.2, (t i).2.2⟩
    · exact funext fun i => rfl
  · intro H hH
    congr 1

/-! ## The main theorem -/

theorem boxNormPow_eq_peel_two {t : ℕ} (ht : 2 ≤ t) (Q S : Finset ℤ) (F : ℤ → ℂ)
    (hfin : Work.Peluse.FinSuppZ F) (hQ : Q.Nonempty) :
    Work.Peluse.boxNormPow t (fun _ : Fin t => Q) S F =
      (((Q.card : ℝ))⁻¹) ^ (2 * (t - 2)) *
        ∑ H ∈ Fintype.piFinset (fun _ : Fin (t - 2) => Q.product Q),
          Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S (Work.Peluse.Ulower.iterDelta' (t - 2) H F) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
  have hk : k + 2 - 2 = k := by omega
  rw [hk]
  have hpeel := boxSumPow_peel_iter' k Q S F
  have hc : ‖((((Q.card : ℂ)) ^ 2)⁻¹) ^ k‖ = ((Q.card : ℝ)⁻¹) ^ (2 * k) := by
    rw [norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
    rw [show (((Q.card : ℝ)) ^ 2)⁻¹ = (((Q.card : ℝ))⁻¹) ^ 2 from (inv_pow _ 2).symm, ← pow_mul]
  have hsum : ‖∑ t : Fin k → ↥Q × ↥Q, Work.Peluse.boxSumPow 2 (fun _ : Fin 2 => Q) S
        (Work.Peluse.Ulower.iterDelta' k (pairV t) F)‖
      = ∑ t : Fin k → ↥Q × ↥Q, Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S
        (Work.Peluse.Ulower.iterDelta' k (pairV t) F) := by
    have hterm : ∀ t : Fin k → ↥Q × ↥Q,
        Work.Peluse.boxSumPow 2 (fun _ : Fin 2 => Q) S
          (Work.Peluse.Ulower.iterDelta' k (pairV t) F)
        = ((Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S
          (Work.Peluse.Ulower.iterDelta' k (pairV t) F) : ℝ) : ℂ) :=
      fun t => Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow (t := 2) (by norm_num)
        (finSuppZ_iterDelta' k (pairV t) F hfin)
    rw [Finset.sum_congr rfl (fun t _ => hterm t)]
    exact norm_sum_ofReal _ (fun t => norm_nonneg _)
  have hreindex : (∑ t : Fin k → ↥Q × ↥Q, Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S
        (Work.Peluse.Ulower.iterDelta' k (pairV t) F))
      = ∑ H ∈ Fintype.piFinset (fun _ : Fin k => Q.product Q),
          Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S
            (Work.Peluse.Ulower.iterDelta' k H F) :=
    (sum_piFinset_prod Q (fun H => Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S
      (Work.Peluse.Ulower.iterDelta' k H F))).symm
  have key : ‖Work.Peluse.boxSumPow (k + 2) (fun _ : Fin (k + 2) => Q) S F‖
      = ((Q.card : ℝ)⁻¹) ^ (2 * k) *
        ∑ H ∈ Fintype.piFinset (fun _ : Fin k => Q.product Q),
          Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Q) S
            (Work.Peluse.Ulower.iterDelta' k H F) := by
    rw [hpeel, norm_mul, hc, hsum, hreindex]
  exact key

end

end Work.Peluse.Ulower
