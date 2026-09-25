import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Analysis.ExponentialSums.norm_sum_sq_le_shift_conj
import Submission.Commons.Algebra.Polynomial.signed_sum_pow_linear
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

namespace Commons.Analysis.ExponentialSums

open Finset
open scoped BigOperators Topology ComplexConjugate

/-! ## Auxiliary definitions for the differencing argument -/

/-- The unit exponential `exp(I * ψ x)` of a real-valued phase on `ℤ`. -/
noncomputable def Ephase (ψ : ℤ → ℝ) : ℤ → ℂ := fun x => Complex.exp ((ψ x : ℂ) * Complex.I)

/-- The shifted conjugate `x ↦ f (x + h) * conj (f x)`. -/
noncomputable def shConj (h : ℤ) (f : ℤ → ℂ) : ℤ → ℂ := fun x => f (x + h) * conj (f x)

/-- Iterated shifted conjugate over a tuple of shifts. -/
noncomputable def iterSh (f : ℤ → ℂ) : (r : ℕ) → (Fin r → ℤ) → ℤ → ℂ
  | 0, _ => f
  | (r + 1), h => shConj (h (Fin.last r)) (iterSh f r (fun i => h i.castSucc))

/-- Iterated finite difference of a real-valued function over a tuple of shifts. -/
noncomputable def iterDiff (g : ℤ → ℝ) : (r : ℕ) → (Fin r → ℤ) → ℤ → ℝ
  | 0, _ => g
  | (r + 1), h => fun x =>
      iterDiff g r (fun i => h i.castSucc) (x + h (Fin.last r)) -
        iterDiff g r (fun i => h i.castSucc) x

/-! ## Basic properties -/

lemma shConj_periodic {n : ℕ} {f : ℤ → ℂ} (hf : ∀ x : ℤ, f (x + n) = f x) (h : ℤ) :
    ∀ x : ℤ, shConj h f (x + n) = shConj h f x := by
  intro x
  simp only [shConj]
  rw [show x + (n : ℤ) + h = x + h + n by ring, hf, hf]

lemma iterSh_periodic {n : ℕ} {f : ℤ → ℂ} (hf : ∀ x : ℤ, f (x + n) = f x) :
    ∀ (r : ℕ) (h : Fin r → ℤ) (x : ℤ), iterSh f r h (x + n) = iterSh f r h x := by
  intro r
  induction r with
  | zero => intro h x; exact hf x
  | succ r ih =>
      intro h x
      exact (shConj_periodic (ih (fun i => h i.castSucc)) (h (Fin.last r))) x

lemma shConj_Ephase (h : ℤ) (ψ : ℤ → ℝ) :
    shConj h (Ephase ψ) = Ephase (fun x => ψ (x + h) - ψ x) := by
  funext x
  rw [shConj, Ephase, Ephase]
  have hconj : conj (Complex.exp ((ψ x : ℂ) * Complex.I)) =
      Complex.exp (-((ψ x : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [map_mul]
  rw [hconj, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma iterSh_Ephase (ψ : ℤ → ℝ) :
    ∀ (r : ℕ) (h : Fin r → ℤ), iterSh (Ephase ψ) r h = Ephase (iterDiff ψ r h) := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
      intro h
      rw [iterSh, ih (fun i => h i.castSucc), shConj_Ephase]
      rfl

lemma iterDiff_const_mul (c : ℝ) (g : ℤ → ℝ) :
    ∀ (r : ℕ) (h : Fin r → ℤ),
      iterDiff (fun x => c * g x) r h = fun x => c * iterDiff g r h x := by
  intro r
  induction r with
  | zero => intro h; rfl
  | succ r ih =>
      intro h
      funext x
      simp only [iterDiff]
      rw [ih (fun i => h i.castSucc)]
      ring


section Bridge

/-- The powerset of the image of `s` under an embedding is the image of the powerset. -/
lemma powerset_map {α β : Type*} (s : Finset α) (e : α ↪ β) :
    (s.map e).powerset = s.powerset.map (Finset.mapEmbedding e).toEmbedding := by
  classical
  ext T
  constructor
  · intro hT
    rw [Finset.mem_powerset] at hT
    rw [Finset.mem_map]
    refine ⟨s.filter (fun a => e a ∈ T), Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
    show (s.filter (fun a => e a ∈ T)).map e = T
    ext b
    constructor
    · intro hb
      obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp hb
      rw [← hae]
      exact (Finset.mem_filter.mp ha).2
    · intro hb
      obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp (hT hb)
      exact Finset.mem_map.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hae.symm ▸ hb⟩, hae⟩
  · intro hT
    rw [Finset.mem_powerset]
    rw [Finset.mem_map] at hT
    obtain ⟨S, hS, hST⟩ := hT
    intro b hb
    have hmap : (Finset.mapEmbedding e).toEmbedding S = S.map e := rfl
    have hb' : b ∈ S.map e := by
      rw [hST.symm, hmap] at hb
      exact hb
    obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp hb'
    exact Finset.mem_map.mpr ⟨a, (Finset.mem_powerset.mp hS) ha, hae⟩

/-- Splitting a sum over all subsets of `Fin (r+1)` according to whether the last element
belongs to the subset. -/
lemma sum_finset_succ {r : ℕ} (F : Finset (Fin (r + 1)) → ℝ) :
    (∑ T : Finset (Fin (r + 1)), F T)
      = (∑ S : Finset (Fin r), F (S.map Fin.castSuccEmb))
        + ∑ S : Finset (Fin r), F (insert (Fin.last r) (S.map Fin.castSuccEmb)) := by
  classical
  set M : Finset (Fin (r + 1)) := (Finset.univ : Finset (Fin r)).map Fin.castSuccEmb with hM
  have huniv : (Finset.univ : Finset (Fin (r + 1))) = insert (Fin.last r) M := by
    ext i
    constructor
    · intro _
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩))
      · exact Finset.mem_insert.mpr (Or.inl rfl)
    · intro _; exact Finset.mem_univ i
  have hlastM : Fin.last r ∉ M := by
    rw [hM, Finset.mem_map]
    rintro ⟨j, -, hj⟩
    exact Fin.castSucc_ne_last j hj
  have hunivpow : (Finset.univ : Finset (Finset (Fin (r + 1))))
      = (Finset.univ : Finset (Fin (r + 1))).powerset := by
    ext T; simp
  have hdisj : Disjoint M.powerset (M.powerset.image (insert (Fin.last r))) := by
    rw [Finset.disjoint_left]
    intro T hT hT'
    obtain ⟨T', hT'pow, hT'eq⟩ := Finset.mem_image.mp hT'
    have hsub : T ⊆ M := Finset.mem_powerset.mp hT
    have : Fin.last r ∈ T := hT'eq ▸ Finset.mem_insert_self _ _
    exact hlastM (hsub this)
  have hinj : ∀ T1 ∈ M.powerset, ∀ T2 ∈ M.powerset,
      insert (Fin.last r) T1 = insert (Fin.last r) T2 → T1 = T2 := by
    intro T1 h1 T2 h2 heq
    have h1' : Fin.last r ∉ T1 := Finset.notMem_of_mem_powerset_of_notMem h1 hlastM
    have h2' : Fin.last r ∉ T2 := Finset.notMem_of_mem_powerset_of_notMem h2 hlastM
    have := congrArg (fun s => s.erase (Fin.last r)) heq
    simpa only [Finset.erase_insert h1', Finset.erase_insert h2'] using this
  have hMpow : M.powerset
      = ((Finset.univ : Finset (Fin r)).powerset).map
          (Finset.mapEmbedding Fin.castSuccEmb).toEmbedding := by
    rw [hM, powerset_map]
  have hunivpow' : ((Finset.univ : Finset (Fin r)).powerset : Finset (Finset (Fin r)))
      = Finset.univ := by
    ext T; simp
  calc (∑ T : Finset (Fin (r + 1)), F T)
      = ∑ T ∈ (Finset.univ : Finset (Fin (r + 1))).powerset, F T := by rw [hunivpow]
    _ = ∑ T ∈ (insert (Fin.last r) M).powerset, F T := by rw [huniv]
    _ = ∑ T ∈ M.powerset ∪ M.powerset.image (insert (Fin.last r)), F T := by
          rw [Finset.powerset_insert]
    _ = (∑ T ∈ M.powerset, F T) + ∑ T ∈ M.powerset.image (insert (Fin.last r)), F T := by
          rw [Finset.sum_union hdisj]
    _ = (∑ S : Finset (Fin r), F (S.map Fin.castSuccEmb))
          + ∑ S : Finset (Fin r), F (insert (Fin.last r) (S.map Fin.castSuccEmb)) := by
          have h1 : (∑ T ∈ M.powerset, F T)
              = ∑ S : Finset (Fin r), F (S.map Fin.castSuccEmb) := by
            rw [hMpow, Finset.sum_map, hunivpow']
            exact Finset.sum_congr rfl (fun S _ => rfl)
          have h2 : (∑ T ∈ M.powerset.image (insert (Fin.last r)), F T)
              = ∑ S : Finset (Fin r),
                  F (insert (Fin.last r) (S.map Fin.castSuccEmb)) := by
            rw [Finset.sum_image hinj, hMpow, Finset.sum_map, hunivpow']
            exact Finset.sum_congr rfl (fun S _ => rfl)
          rw [h1, h2]

/-- The iterated finite difference is given by the signed inclusion–exclusion sum over subsets. -/
lemma iterDiff_eq_sum (g : ℤ → ℝ) :
    ∀ (r : ℕ) (h : Fin r → ℤ) (x : ℤ),
      iterDiff g r h x
        = ∑ S : Finset (Fin r), (-1 : ℝ) ^ (r - S.card) * g (x + ∑ i ∈ S, h i) := by
  intro r
  induction r with
  | zero =>
      intro h x
      rw [iterDiff]
      rw [Finset.sum_eq_single (∅ : Finset (Fin 0))]
      · simp
      · intro b _ hb
        exact absurd (Finset.eq_empty_iff_forall_notMem.mpr (fun i _ => Fin.elim0 i)) hb
      · intro h
        exact absurd (Finset.mem_univ (∅ : Finset (Fin 0))) h
  | succ r ih =>
      intro h x
      change iterDiff g r (fun i => h i.castSucc) (x + h (Fin.last r))
        - iterDiff g r (fun i => h i.castSucc) x
        = ∑ S : Finset (Fin (r + 1)), (-1 : ℝ) ^ (r + 1 - S.card) * g (x + ∑ i ∈ S, h i)
      rw [ih (fun i => h i.castSucc) (x + h (Fin.last r)),
        ih (fun i => h i.castSucc) x]
      have hcard : ∀ S : Finset (Fin r), S.card ≤ r := by
        intro S
        simpa using Finset.card_le_univ S
      rw [sum_finset_succ (fun T : Finset (Fin (r + 1)) =>
        (-1 : ℝ) ^ (r + 1 - T.card) * g (x + ∑ i ∈ T, h i))]
      have h1 : (∑ S : Finset (Fin r),
            (-1 : ℝ) ^ (r + 1 - (S.map Fin.castSuccEmb).card)
              * g (x + ∑ i ∈ S.map Fin.castSuccEmb, h i))
          = -∑ S : Finset (Fin r),
              (-1 : ℝ) ^ (r - S.card) * g (x + ∑ i ∈ S, h i.castSucc) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro S _
        rw [Finset.card_map, Finset.sum_map]
        simp only [Fin.castSuccEmb_apply]
        rw [show r + 1 - S.card = (r - S.card) + 1 by have := hcard S; omega, pow_succ]
        ring
      have h2 : (∑ S : Finset (Fin r),
            (-1 : ℝ) ^ (r + 1 - (insert (Fin.last r) (S.map Fin.castSuccEmb)).card)
              * g (x + ∑ i ∈ insert (Fin.last r) (S.map Fin.castSuccEmb), h i))
          = ∑ S : Finset (Fin r),
              (-1 : ℝ) ^ (r - S.card) * g (x + h (Fin.last r) + ∑ i ∈ S, h i.castSucc) := by
        apply Finset.sum_congr rfl
        intro S _
        have hnot : Fin.last r ∉ S.map Fin.castSuccEmb := by
          rw [Finset.mem_map]
          rintro ⟨j, -, hj⟩
          exact Fin.castSucc_ne_last j hj
        rw [Finset.card_insert_of_notMem hnot, Finset.card_map, Finset.sum_insert hnot,
          Finset.sum_map]
        simp only [Fin.castSuccEmb_apply, add_assoc]
        rw [show r + 1 - (S.card + 1) = r - S.card by have := hcard S; omega]
      rw [h1, h2]
      ring

/-- Splitting a sum over tuples `Fin (r+1) → Fin n` into a sum over `Fin r → Fin n` and an
extra coordinate. -/
lemma sum_fun_succ {r n : ℕ} (F : (Fin (r + 1) → Fin n) → ℝ) :
    (∑ h : Fin (r + 1) → Fin n, F h)
      = ∑ h : Fin r → Fin n, ∑ j : Fin n, F (Fin.snoc h j) := by
  have h1 : (∑ h : Fin (r + 1) → Fin n, F h)
      = ∑ p : Fin n × (Fin r → Fin n), F (Fin.snoc p.2 p.1) := by
    refine Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (r + 1) => Fin n)).symm F
      (fun p : Fin n × (Fin r → Fin n) => F (Fin.snoc p.2 p.1)) ?_
    intro hs
    simp [Fin.snocEquiv, Fin.snoc_init_self]
  rw [h1, Fintype.sum_prod_type, Finset.sum_comm]

/-- The iterated shift-conjugate over a tuple extended by one coordinate. -/
lemma iterSh_snoc {r : ℕ} (f : ℤ → ℂ) (h : Fin r → ℤ) (j : ℤ) :
    iterSh f (r + 1) (Fin.snoc h j) = shConj j (iterSh f r h) := by
  simp only [iterSh]
  congr 2
  · exact Fin.snoc_last ..
  · funext i
    simp [Fin.snoc_castSucc]

/-- The iterated shift-conjugate over a tuple extended by one coordinate (`Fin`-valued shifts). -/
lemma iterSh_snoc_fin {r n : ℕ} (f : ℤ → ℂ) (h : Fin r → Fin n) (j : Fin n) :
    iterSh f (r + 1) (fun i => ((Fin.snoc (α := fun _ : Fin (r + 1) => Fin n) h j i : Fin n) : ℤ))
      = shConj (j : ℤ) (iterSh f r (fun i => ((h i : Fin n) : ℤ))) := by
  have hcongr :
      (fun i : Fin (r + 1) =>
          ((Fin.snoc (α := fun _ : Fin (r + 1) => Fin n) h j i : Fin n) : ℤ))
      = Fin.snoc (fun i : Fin r => ((h i : Fin n) : ℤ)) ((j : Fin n) : ℤ) := by
    funext i
    induction i using Fin.lastCases with
    | cast i => simp [Fin.snoc_castSucc]
    | last => simp [Fin.snoc_last]
  rw [hcongr]
  exact iterSh_snoc f (fun i => ((h i : Fin n) : ℤ)) ((j : Fin n) : ℤ)

/-- Elementary exponent identity used in the differencing induction. -/
lemma two_pow_succ_sub (r : ℕ) :
    2 ^ (r + 1) - (r + 1) - 1 = 2 * (2 ^ r - r - 1) + r := by
  have hle : r + 1 ≤ 2 ^ r := by
    induction r with
    | zero => simp
    | succ r ihr => rw [pow_succ]; omega
  omega

end Bridge


section Differencing

/-- Iterated Weyl differencing for a complete residue system. -/
theorem norm_sum_pow_le_diff (n r : ℕ) (hn : 0 < n) (f : ℤ → ℂ)
    (hf : ∀ x : ℤ, f (x + n) = f x) :
    ‖∑ x ∈ Finset.range n, f x‖ ^ (2 ^ r)
      ≤ (n : ℝ) ^ (2 ^ r - r - 1)
        * ∑ h : Fin r → Fin n,
            ‖∑ x ∈ Finset.range n, iterSh f r (fun i => (h i : ℤ)) x‖ := by
  induction r with
  | zero =>
      have hterm : ∀ h : Fin 0 → Fin n,
          ‖∑ x ∈ Finset.range n, iterSh f 0 (fun i => (h i : ℤ)) x‖
            = ‖∑ x ∈ Finset.range n, f x‖ := fun h => by simp [iterSh]
      rw [Finset.sum_congr rfl (fun h _ => hterm h)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin]
      simp
  | succ r ih =>
      set S : ℂ := ∑ x ∈ Finset.range n, f x with hS
      set T : (Fin r → Fin n) → ℝ := fun h =>
        ‖∑ x ∈ Finset.range n, iterSh f r (fun i => (h i : ℤ)) x‖ with hT
      have hIH : ‖S‖ ^ (2 ^ r) ≤ (n : ℝ) ^ (2 ^ r - r - 1) * ∑ h : Fin r → Fin n, T h := ih
      have hCS : (∑ h : Fin r → Fin n, T h) ^ 2
          ≤ (n : ℝ) ^ r * ∑ h : Fin r → Fin n, (T h) ^ 2 := by
        have h0 := sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset (Fin r → Fin n))) (f := T)
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h0
        simpa [Nat.cast_pow] using h0
      have hstep : ∀ h : Fin r → Fin n, (T h) ^ 2
          ≤ ∑ j : Fin n,
              ‖∑ x ∈ Finset.range n, shConj (j : ℤ) (iterSh f r (fun i => (h i : ℤ))) x‖ := by
        intro h
        have hper := iterSh_periodic hf r (fun i => (h i : ℤ))
        have hmain := norm_sum_sq_le_shift_conj n hn (iterSh f r (fun i => (h i : ℤ))) hper
        rw [hT]
        have hconv : (∑ k ∈ Finset.range n,
              ‖∑ x ∈ Finset.range n,
                iterSh f r (fun i => (h i : ℤ)) (↑(x + k)) *
                  conj (iterSh f r (fun i => (h i : ℤ)) ↑x)‖)
            = ∑ j : Fin n,
                ‖∑ x ∈ Finset.range n,
                  shConj (j : ℤ) (iterSh f r (fun i => (h i : ℤ))) ↑x‖ := by
          rw [← Fin.sum_univ_eq_sum_range
            (f := fun k : ℕ => ‖∑ x ∈ Finset.range n,
                iterSh f r (fun i => (h i : ℤ)) (↑(x + k)) *
                  conj (iterSh f r (fun i => (h i : ℤ)) ↑x)‖)]
          apply Finset.sum_congr rfl
          intro j _
          congr 1
        exact hmain.trans (le_of_eq hconv)
      have key : (∑ h : Fin r → Fin n, (T h) ^ 2)
          ≤ ∑ hs : Fin (r + 1) → Fin n,
              ‖∑ x ∈ Finset.range n, iterSh f (r + 1) (fun i => (hs i : ℤ)) x‖ := by
        rw [sum_fun_succ (F := fun hs : Fin (r + 1) → Fin n =>
          ‖∑ x ∈ Finset.range n, iterSh f (r + 1) (fun i => (hs i : ℤ)) x‖)]
        apply Finset.sum_le_sum
        intro h _
        refine (hstep h).trans_eq ?_
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        rw [← iterSh_snoc_fin f h j]
      have hexp := two_pow_succ_sub r
      have hS2 : ‖S‖ ^ (2 ^ (r + 1)) = (‖S‖ ^ (2 ^ r)) ^ 2 := by
        rw [← pow_mul, pow_succ]
      rw [hS2, hexp]
      calc (‖S‖ ^ 2 ^ r) ^ 2
          ≤ ((n : ℝ) ^ (2 ^ r - r - 1) * ∑ h : Fin r → Fin n, T h) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hIH 2
        _ = (n : ℝ) ^ (2 * (2 ^ r - r - 1)) * (∑ h : Fin r → Fin n, T h) ^ 2 := by
            rw [mul_pow, ← pow_mul]
            congr 1
            ring
        _ ≤ (n : ℝ) ^ (2 * (2 ^ r - r - 1))
              * ((n : ℝ) ^ r * ∑ h : Fin r → Fin n, (T h) ^ 2) :=
            mul_le_mul_of_nonneg_left hCS (by positivity)
        _ = (n : ℝ) ^ (2 * (2 ^ r - r - 1) + r) * ∑ h : Fin r → Fin n, (T h) ^ 2 := by
            rw [pow_add]
            ring
        _ ≤ (n : ℝ) ^ (2 * (2 ^ r - r - 1) + r)
              * ∑ hs : Fin (r + 1) → Fin n,
                  ‖∑ x ∈ Finset.range n, iterSh f (r + 1) (fun i => (hs i : ℤ)) x‖ :=
            mul_le_mul_of_nonneg_left key (by positivity)

end Differencing

/-! ## The affine shape of the iterated difference, and the geometric sum -/

/-- The `(k-1)`-fold finite difference of `x ↦ x^k` is affine with slope `k! · ∏ hᵢ`. -/
lemma iterDiff_pow_affine (k : ℕ) (hk : 2 ≤ k) (h : Fin (k - 1) → ℤ) :
    ∃ c : ℤ, ∀ x : ℤ,
      iterDiff (fun y : ℤ => (y : ℝ) ^ k) (k - 1) h x
        = (k.factorial : ℝ) * (∏ i : Fin (k - 1), (h i : ℝ)) * (x : ℝ) + (c : ℝ) := by
  obtain ⟨c, hc⟩ := Commons.Algebra.Polynomial.signed_sum_pow_linear k hk h
  refine ⟨c, fun x => ?_⟩
  rw [iterDiff_eq_sum]
  have hh := congrArg (fun z : ℤ => (z : ℝ)) (hc x)
  push_cast at hh
  rw [show (∑ S : Finset (Fin (k - 1)),
        (-1 : ℝ) ^ ((k - 1) - S.card) * (fun y : ℤ => (y : ℝ) ^ k) (x + ∑ i ∈ S, h i))
      = ∑ S : Finset (Fin (k - 1)),
          (-1 : ℝ) ^ ((k - 1) - S.card) * ((x : ℝ) + ∑ i ∈ S, (h i : ℝ)) ^ k from by
    apply Finset.sum_congr rfl
    intro S _
    congr 1
    simp only []
    have h1 : (((x + ∑ i ∈ S, h i : ℤ)) : ℝ) = (x : ℝ) + ∑ i ∈ S, (h i : ℝ) := by
      push_cast
      ring
    rw [h1]]
  exact hh

/-- A complete geometric sum of a root of unity of order dividing `n`. -/
lemma sum_range_pow_eq (n : ℕ) {ζ : ℂ} (hζ : ζ ^ n = 1) :
    (∑ x ∈ Finset.range n, ζ ^ x) = if ζ = 1 then (n : ℂ) else 0 := by
  by_cases h : ζ = 1
  · subst h
    simp
  · rw [if_neg h]
    have hmul := geom_sum_mul ζ n
    rw [hζ, sub_self] at hmul
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr h)


/-! ## The counting bound for tuples with divisible product -/

/-- Number of `m`-tuples of residues mod `n` whose product times `c` is divisible by `n`,
counted as a real number. -/
noncomputable def cntN (n m c : ℕ) : ℝ :=
  ∑ h : Fin m → Fin n, if n ∣ c * ∏ i, (h i : ℕ) then (1 : ℝ) else 0

lemma cntN_eq_card (n m c : ℕ) :
    cntN n m c = (((Finset.univ : Finset (Fin m → Fin n)).filter
      (fun h : Fin m → Fin n => n ∣ c * ∏ i, (h i : ℕ))).card : ℝ) := by
  simp only [cntN, Finset.sum_boole]

lemma cntN_one_eq (n c : ℕ) :
    cntN n 1 c = ∑ x : Fin n, (if n ∣ c * x then (1 : ℝ) else 0) := by
  rw [cntN]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)) _ _ (fun h => ?_)
  have h1 : (Equiv.funUnique (Fin 1) (Fin n)) h = h 0 := rfl
  rw [h1, Fin.prod_univ_one]

/-- The number of `x : Fin n` with `n ∣ c * x` is at most `gcd n c`. -/
lemma card_dvd_mul_le_gcd (n c : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter (fun x : Fin n => n ∣ c * x)).card
      ≤ Nat.gcd n c := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : (Finset.univ : Finset (Fin 0)) = ∅ := by simp
    rw [this]
    simp
  · set g := Nat.gcd n c with hgdef
    have hg : 0 < g := by rw [hgdef]; exact Nat.gcd_pos_of_pos_left c hn
    set m := n / g with hmdef
    have hgm : g * m = n := by rw [hmdef]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left n c)
    have hmpos : 0 < m := by
      rw [hmdef]
      exact Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_left n c)) hg
    have hcop : m.Coprime (c / g) := by
      have h := Nat.coprime_div_gcd_div_gcd (m := n) (n := c) (by rw [← hgdef]; exact hg)
      simpa [hmdef, hgdef] using h
    have hmem : ∀ x : Fin n, n ∣ c * x.val → m ∣ x.val := by
      intro x hx
      have hc : c = g * (c / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right n c)).symm
      have h1 : g * m ∣ g * ((c / g) * x.val) := by
        rw [hgm, ← mul_assoc, ← hc]
        exact hx
      exact hcop.dvd_of_dvd_mul_left ((Nat.mul_dvd_mul_iff_left hg).mp h1)
    have hle2 : ((Finset.univ : Finset (Fin n)).filter (fun x : Fin n => m ∣ x.val)).card
        ≤ g := by
      have hinj : Set.InjOn (fun x : Fin n => x.val / m)
          ↑((Finset.univ : Finset (Fin n)).filter (fun x : Fin n => m ∣ x.val)) := by
        intro x hx y hy hxy
        have hxy' : x.val / m = y.val / m := hxy
        have hx' : x ∈ (Finset.univ : Finset (Fin n)).filter (fun x : Fin n => m ∣ x.val) := by
          simpa using hx
        have hy' : y ∈ (Finset.univ : Finset (Fin n)).filter (fun x : Fin n => m ∣ x.val) := by
          simpa using hy
        have hx2 : m ∣ x.val := (Finset.mem_filter.mp hx').2
        have hy2 : m ∣ y.val := (Finset.mem_filter.mp hy').2
        have hxy2 : x.val = y.val := by
          rw [← Nat.mul_div_cancel' hx2, ← Nat.mul_div_cancel' hy2, hxy']
        exact Fin.ext hxy2
      have hmap : Set.MapsTo (fun x : Fin n => x.val / m)
          ↑((Finset.univ : Finset (Fin n)).filter (fun x : Fin n => m ∣ x.val))
          ↑(Finset.range g) := by
        intro x _
        simp only [Finset.mem_coe, Finset.mem_range]
        rw [Nat.div_lt_iff_lt_mul hmpos, hgm]
        exact x.isLt
      calc ((Finset.univ : Finset (Fin n)).filter (fun x : Fin n => m ∣ x.val)).card
          ≤ (Finset.range g).card := Finset.card_le_card_of_injOn _ hmap hinj
        _ = g := Finset.card_range g
    refine le_trans (Finset.card_le_card ?_) hle2
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,
      hmem x (Finset.mem_filter.mp hx).2⟩

lemma cntN_one_le (n c : ℕ) : cntN n 1 c ≤ (Nat.gcd n c : ℝ) := by
  rw [cntN_one_eq]
  have h1 : (∑ x : Fin n, (if n ∣ c * x then (1 : ℝ) else 0))
      = (((Finset.univ : Finset (Fin n)).filter (fun x : Fin n => n ∣ c * x)).card : ℝ) := by
    simp only [Finset.sum_boole]
  rw [h1]
  exact_mod_cast card_dvd_mul_le_gcd n c

/-- Iterating the last-coordinate count. -/
lemma cntN_succ (n m c : ℕ) :
    cntN n (m + 1) c = ∑ h' : Fin m → Fin n, cntN n 1 (c * ∏ i, (h' i : ℕ)) := by
  rw [cntN, sum_fun_succ (F := fun h : Fin (m + 1) → Fin n =>
    if n ∣ c * ∏ i, (h i : ℕ) then (1 : ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro h' _
  rw [cntN_one_eq]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  have hprod : (∏ i : Fin (m + 1),
        (((Fin.snoc (α := fun _ : Fin (m + 1) => Fin n) h' x) i : Fin n) : ℕ))
      = (∏ i : Fin m, (h' i : ℕ)) * (x : ℕ) := by
    rw [Fin.prod_univ_castSucc]
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      rw [Fin.snoc_castSucc]
    · rw [Fin.snoc_last]
  rw [hprod, mul_assoc]

lemma gcd_mul_le (n a b : ℕ) : Nat.gcd n (a * b) ≤ Nat.gcd n a * Nat.gcd n b := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have h := Nat.gcd_mul_left_dvd_mul_gcd n a b
    rw [Nat.gcd_comm (a * b) n, Nat.gcd_comm a n, Nat.gcd_comm b n] at h
    exact Nat.le_of_dvd
      (Nat.mul_pos (Nat.gcd_pos_of_pos_left a hn) (Nat.gcd_pos_of_pos_left b hn)) h

lemma gcd_prod_le (n : ℕ) {m : ℕ} (x : Fin m → ℕ) :
    Nat.gcd n (∏ i, x i) ≤ ∏ i, Nat.gcd n (x i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
      calc Nat.gcd n ((∏ i : Fin m, x i.castSucc) * x (Fin.last m))
          ≤ Nat.gcd n (∏ i : Fin m, x i.castSucc) * Nat.gcd n (x (Fin.last m)) := gcd_mul_le ..
        _ ≤ (∏ i : Fin m, Nat.gcd n (x i.castSucc)) * Nat.gcd n (x (Fin.last m)) :=
            Nat.mul_le_mul_right _ (ih (fun i => x i.castSucc))

lemma sum_prod_gcd (n m : ℕ) :
    (∑ h : Fin m → Fin n, ∏ i, (Nat.gcd n (h i) : ℝ))
      = (∑ x : Fin n, (Nat.gcd n x : ℝ)) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [sum_fun_succ (F := fun h : Fin (m + 1) → Fin n =>
        ∏ i, (Nat.gcd n (h i) : ℝ))]
      have hx : ∀ h' : Fin m → Fin n, ∀ x : Fin n,
          (∏ i : Fin (m + 1),
            (Nat.gcd n ((Fin.snoc (α := fun _ : Fin (m + 1) => Fin n) h' x) i) : ℝ))
            = (∏ i : Fin m, (Nat.gcd n (h' i) : ℝ)) * (Nat.gcd n x : ℝ) := by
        intro h' x
        rw [Fin.prod_univ_castSucc]
        congr 1
        · apply Finset.prod_congr rfl
          intro i _
          rw [Fin.snoc_castSucc]
        · rw [Fin.snoc_last]
      calc (∑ h' : Fin m → Fin n, ∑ x : Fin n,
              ∏ i : Fin (m + 1),
                (Nat.gcd n ((Fin.snoc (α := fun _ : Fin (m + 1) => Fin n) h' x) i) : ℝ))
          = ∑ h' : Fin m → Fin n, ∑ x : Fin n,
              (∏ i : Fin m, (Nat.gcd n (h' i) : ℝ)) * (Nat.gcd n x : ℝ) := by
            apply Finset.sum_congr rfl
            intro h' _
            apply Finset.sum_congr rfl
            intro x _
            exact hx h' x
        _ = ∑ h' : Fin m → Fin n,
              (∏ i : Fin m, (Nat.gcd n (h' i) : ℝ)) * (∑ x : Fin n, (Nat.gcd n x : ℝ)) := by
            apply Finset.sum_congr rfl
            intro h' _
            rw [Finset.mul_sum]
        _ = (∑ h' : Fin m → Fin n, ∏ i : Fin m, (Nat.gcd n (h' i) : ℝ))
              * (∑ x : Fin n, (Nat.gcd n x : ℝ)) := by
            rw [Finset.sum_mul]
        _ = (∑ x : Fin n, (Nat.gcd n x : ℝ)) ^ m * (∑ x : Fin n, (Nat.gcd n x : ℝ)) := by
            rw [ih]
        _ = (∑ x : Fin n, (Nat.gcd n x : ℝ)) ^ (m + 1) := by
            rw [pow_succ]

lemma cntN_le (n m c : ℕ) (hn : 0 < n) :
    cntN n (m + 1) c ≤ (Nat.gcd n c : ℝ) * (∑ x : Fin n, (Nat.gcd n x : ℝ)) ^ m := by
  rw [cntN_succ]
  calc (∑ h' : Fin m → Fin n, cntN n 1 (c * ∏ i, (h' i : ℕ)))
      ≤ ∑ h' : Fin m → Fin n, (Nat.gcd n (c * ∏ i, (h' i : ℕ)) : ℝ) :=
        Finset.sum_le_sum (fun h' _ => cntN_one_le n _)
    _ ≤ ∑ h' : Fin m → Fin n,
          (Nat.gcd n c : ℝ) * ∏ i, (Nat.gcd n (h' i) : ℝ) := by
        apply Finset.sum_le_sum
        intro h' _
        have h1 : (Nat.gcd n (c * ∏ i, (h' i : ℕ)) : ℝ)
            ≤ (Nat.gcd n c : ℝ) * (Nat.gcd n (∏ i, (h' i : ℕ)) : ℝ) := by
          exact_mod_cast gcd_mul_le n c (∏ i, (h' i : ℕ))
        have h2 : (Nat.gcd n (∏ i, (h' i : ℕ)) : ℝ)
            ≤ ∏ i, (Nat.gcd n (h' i) : ℝ) := by
          exact_mod_cast gcd_prod_le n (fun i => (h' i : ℕ))
        calc (Nat.gcd n (c * ∏ i, (h' i : ℕ)) : ℝ)
            ≤ (Nat.gcd n c : ℝ) * (Nat.gcd n (∏ i, (h' i : ℕ)) : ℝ) := h1
          _ ≤ (Nat.gcd n c : ℝ) * ∏ i, (Nat.gcd n (h' i) : ℝ) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (Nat.gcd n c : ℝ) * (∑ x : Fin n, (Nat.gcd n x : ℝ)) ^ m := by
        rw [← Finset.mul_sum, ← sum_prod_gcd]

/-- The number of multiples of `d` among `Fin n` is at most `n / d + 1`. -/
lemma card_filter_dvd_le (n d : ℕ) (hd : 0 < d) :
    ((Finset.univ : Finset (Fin n)).filter (fun x : Fin n => d ∣ x.val)).card
      ≤ n / d + 1 := by
  have hinj : Set.InjOn (fun x : Fin n => x.val / d)
      ↑((Finset.univ : Finset (Fin n)).filter (fun x : Fin n => d ∣ x.val)) := by
    intro x hx y hy hxy
    have hxy' : x.val / d = y.val / d := hxy
    have hx' : x ∈ (Finset.univ : Finset (Fin n)).filter (fun x : Fin n => d ∣ x.val) := by
      simpa using hx
    have hy' : y ∈ (Finset.univ : Finset (Fin n)).filter (fun x : Fin n => d ∣ x.val) := by
      simpa using hy
    have hx2 : d ∣ x.val := (Finset.mem_filter.mp hx').2
    have hy2 : d ∣ y.val := (Finset.mem_filter.mp hy').2
    have hxy2 : x.val = y.val := by
      rw [← Nat.mul_div_cancel' hx2, ← Nat.mul_div_cancel' hy2, hxy']
    exact Fin.ext hxy2
  have hmap : Set.MapsTo (fun x : Fin n => x.val / d)
      ↑((Finset.univ : Finset (Fin n)).filter (fun x : Fin n => d ∣ x.val))
      ↑(Finset.range (n / d + 1)) := by
    intro x _
    simp only [Finset.mem_coe, Finset.mem_range]
    have h1 : x.val / d ≤ (n - 1) / d := Nat.div_le_div_right (by omega)
    have h2 : (n - 1) / d ≤ n / d := Nat.div_le_div_right (by omega)
    omega
  calc ((Finset.univ : Finset (Fin n)).filter (fun x : Fin n => d ∣ x.val)).card
      ≤ (Finset.range (n / d + 1)).card :=
        Finset.card_le_card_of_injOn (fun x : Fin n => x.val / d) hmap hinj
    _ = n / d + 1 := Finset.card_range _

lemma sum_gcd_le (n : ℕ) :
    (∑ x : Fin n, (Nat.gcd n x : ℝ)) ≤ 2 * (n : ℝ) * (n.divisors.card : ℝ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have h1 : ∀ x : Fin n, (Nat.gcd n x.val : ℝ)
      ≤ ∑ d ∈ n.divisors, if d ∣ x.val then (d : ℝ) else 0 := by
    intro x
    have hmem : Nat.gcd n x.val ∈ n.divisors.filter (fun d : ℕ => d ∣ x.val) := by
      rw [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨Nat.gcd_dvd_left n x.val, by omega⟩, Nat.gcd_dvd_right n x.val⟩
    have hle := Finset.single_le_sum (s := n.divisors.filter (fun d : ℕ => d ∣ x.val))
      (f := fun d : ℕ => (d : ℝ)) (fun d _ => by positivity) hmem
    calc (Nat.gcd n x.val : ℝ)
        ≤ ∑ d ∈ n.divisors.filter (fun d : ℕ => d ∣ x.val), (d : ℝ) := hle
      _ = ∑ d ∈ n.divisors, if d ∣ x.val then (d : ℝ) else 0 := by rw [Finset.sum_filter]
  calc (∑ x : Fin n, (Nat.gcd n x : ℝ))
      ≤ ∑ x : Fin n, ∑ d ∈ n.divisors, (if d ∣ x.val then (d : ℝ) else 0) :=
        Finset.sum_le_sum (fun x _ => h1 x)
    _ = ∑ d ∈ n.divisors, ∑ x : Fin n, (if d ∣ x.val then (d : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ n.divisors,
          (d : ℝ) * (((Finset.univ : Finset (Fin n)).filter
            (fun x : Fin n => d ∣ x.val)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [show (∑ x : Fin n, (if d ∣ x.val then (d : ℝ) else 0))
            = (d : ℝ) * ∑ x : Fin n, (if d ∣ x.val then (1 : ℝ) else 0) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          by_cases h : d ∣ x.val <;> simp [h]]
        rw [show (∑ x : Fin n, (if d ∣ x.val then (1 : ℝ) else 0))
            = (((Finset.univ : Finset (Fin n)).filter
                (fun x : Fin n => d ∣ x.val)).card : ℝ) by
          simp only [Finset.sum_boole]]
    _ ≤ ∑ d ∈ n.divisors, 2 * (n : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
        have hcard : ((Finset.univ : Finset (Fin n)).filter
            (fun x : Fin n => d ∣ x.val)).card ≤ n / d + 1 := card_filter_dvd_le n d hdpos
        have hnat : d * (n / d + 1) ≤ 2 * n := by
          have h1 : d * (n / d) = n := Nat.mul_div_cancel' hdn
          have h2 : d ≤ n := Nat.le_of_dvd hn hdn
          calc d * (n / d + 1) = d * (n / d) + d := by ring
            _ = n + d := by rw [h1]
            _ ≤ 2 * n := by omega
        calc (d : ℝ) * (((Finset.univ : Finset (Fin n)).filter
              (fun x : Fin n => d ∣ x.val)).card : ℝ)
            ≤ (d : ℝ) * ((n / d + 1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by positivity)
          _ = ((d * (n / d + 1) : ℕ) : ℝ) := by push_cast; ring
          _ ≤ 2 * (n : ℝ) := by exact_mod_cast hnat
    _ = 2 * (n : ℝ) * (n.divisors.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

lemma cntN_factorial_le (k : ℕ) (hk : 2 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      cntN n (k - 1) k.factorial ≤ C * (n : ℝ) ^ ((k : ℝ) - 2 + ε) := by
  rcases eq_or_lt_of_le hk with h2 | h3
  · subst h2
    refine ⟨2, by norm_num, fun n hn => ?_⟩
    have key : cntN n 1 2 ≤ 2 := le_trans (cntN_one_le n 2) (by
      exact_mod_cast Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right n 2))
    refine le_trans key ?_
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn1 hε.le
    have h2' : (2 : ℝ) * (n : ℝ) ^ ε ≤ 2 * (n : ℝ) ^ (((2 : ℕ) : ℝ) - 2 + ε) := by
      have he : (((2 : ℕ) : ℝ) - 2 + ε) = ε := by norm_num
      rw [he]
    linarith
  · have hk3 : 3 ≤ k := h3
    have hk2pos : (0 : ℝ) < (k : ℝ) - 2 := by
      have : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      linarith
    obtain ⟨C0, hC0pos, hC0⟩ := Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
      (ε / ((k : ℝ) - 2)) (by positivity)
    refine ⟨(k.factorial : ℝ) * (2 * C0) ^ (k - 2), by positivity, fun n hn => ?_⟩
    have hk1 : k - 1 = (k - 2) + 1 := by omega
    have hgcd : (Nat.gcd n k.factorial : ℝ) ≤ (k.factorial : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos k) (Nat.gcd_dvd_right n k.factorial)
    have hS := sum_gcd_le n
    have htau := hC0 n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by positivity
    have hS2 : (∑ x : Fin n, (Nat.gcd n x : ℝ))
        ≤ 2 * C0 * (n : ℝ) ^ (1 + ε / ((k:ℝ) - 2)) := by
      calc (∑ x : Fin n, (Nat.gcd n x : ℝ)) ≤ 2 * (n : ℝ) * (n.divisors.card : ℝ) := hS
        _ ≤ 2 * (n : ℝ) * (C0 * (n : ℝ) ^ (ε / ((k:ℝ) - 2))) :=
            mul_le_mul_of_nonneg_left htau (by positivity)
        _ = 2 * C0 * ((n : ℝ) * (n : ℝ) ^ (ε / ((k:ℝ) - 2))) := by ring
        _ = 2 * C0 * (n : ℝ) ^ (1 + ε / ((k:ℝ) - 2)) := by
            rw [Real.rpow_add hnpos, Real.rpow_one]
    have hcnt : cntN n (k - 1) k.factorial
        ≤ (Nat.gcd n k.factorial : ℝ) * (∑ x : Fin n, (Nat.gcd n x : ℝ)) ^ (k - 2) := by
      have h := cntN_le n (k - 2) k.factorial hn
      rw [← hk1] at h
      exact h
    have hpow : (2 * C0 * (n : ℝ) ^ (1 + ε / ((k:ℝ) - 2))) ^ (k - 2)
        = (2 * C0) ^ (k - 2)
          * (n : ℝ) ^ ((1 + ε / ((k:ℝ) - 2)) * (((k - 2 : ℕ) : ℝ))) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hnpos)]
    have hmain : (Nat.gcd n k.factorial : ℝ) * (∑ x : Fin n, (Nat.gcd n x : ℝ)) ^ (k - 2)
        ≤ (k.factorial : ℝ) * (2 * C0 * (n : ℝ) ^ (1 + ε / ((k:ℝ) - 2))) ^ (k - 2) := by
      refine mul_le_mul hgcd (pow_le_pow_left₀ (by positivity) hS2 (k - 2)) (by positivity)
        (by positivity)
    rw [hpow] at hmain
    refine le_trans (le_trans hcnt hmain) ?_
    have hexp : (1 + ε / ((k:ℝ) - 2)) * (((k - 2 : ℕ) : ℝ)) = ((k:ℝ) - 2) + ε := by
      rw [Nat.cast_sub (by omega : 2 ≤ k), Nat.cast_ofNat]
      field_simp
    rw [hexp, mul_assoc]


/-! ## The phase of the target sum, its periodicity, and linear-phase sums -/

/-- The real phase `x ↦ 2π a x^k / n`. -/
noncomputable def wphase (n : ℕ) (a : ℤ) (k : ℕ) : ℤ → ℝ :=
  fun x => 2 * Real.pi * (a : ℝ) * (x : ℝ) ^ k / (n : ℝ)

/-- `exp(2πi m / n) = 1` exactly when `n ∣ m`. -/
lemma exp_div_two_pi_eq_one_iff (n : ℕ) (hn : 0 < n) (m : ℤ) :
    Complex.exp ((((2 * Real.pi * (m : ℝ)) / (n : ℝ) : ℝ) : ℂ) * Complex.I) = 1
      ↔ (n : ℤ) ∣ m := by
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨j, hj⟩
    have h' : ((((2 * Real.pi * (m : ℝ)) / (n : ℝ) : ℝ) : ℂ)) * Complex.I
        = ((((j : ℝ) * (2 * Real.pi)) : ℝ) : ℂ) * Complex.I := by
      rw [hj]
      push_cast
      ring
    have h'' := mul_right_cancel₀ Complex.I_ne_zero h'
    have hreal : 2 * Real.pi * (m : ℝ) / (n : ℝ) = (j : ℝ) * (2 * Real.pi) :=
      Complex.ofReal_inj.mp h''
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    have hmul : (m : ℝ) = (j : ℝ) * (n : ℝ) := by
      rw [div_eq_iff hnR] at hreal
      have h2 : (2 * Real.pi) * (m : ℝ)
          = (2 * Real.pi) * ((j : ℝ) * (n : ℝ)) := by
        rw [hreal]; ring
      exact mul_left_cancel₀ (by positivity : (2 * Real.pi) ≠ 0) h2
    refine ⟨j, ?_⟩
    have h1 : (m : ℝ) = (n : ℝ) * (j : ℝ) := by linarith
    exact_mod_cast h1
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    rw [hj]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    push_cast
    field_simp

/-- The exponential of `wphase` is periodic of period `n`. -/
lemma Ephase_wphase_add (n : ℕ) (hn : 0 < n) (a : ℤ) (k : ℕ) (x : ℤ) :
    Ephase (wphase n a k) (x + n) = Ephase (wphase n a k) x := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (x + n) ^ k - x ^ k = (n : ℤ) * m := by
    have hmod : (x + n) ^ k ≡ x ^ k [ZMOD (n : ℤ)] := by
      apply Int.ModEq.pow
      rw [Int.modEq_iff_dvd]
      exact ⟨-1, by ring⟩
    have h := Int.modEq_iff_dvd.mp hmod
    have h2 : (n : ℤ) ∣ (x + n) ^ k - x ^ k := by
      rw [show (x + n) ^ k - x ^ k = -(x ^ k - (x + n) ^ k) by ring]
      exact dvd_neg.mpr h
    obtain ⟨m, hm⟩ := h2
    exact ⟨m, hm⟩
  have hmR : ((x + n : ℤ) : ℝ) ^ k - ((x : ℤ) : ℝ) ^ k = (n : ℝ) * (m : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hm
    push_cast at h
    simpa using h
  have hdiff : wphase n a k (x + n) - wphase n a k x
      = 2 * Real.pi * (a : ℝ) * (m : ℝ) := by
    rw [wphase, wphase, div_sub_div_same]
    rw [show 2 * Real.pi * (a : ℝ) * ((x + n : ℤ) : ℝ) ^ k
          - 2 * Real.pi * (a : ℝ) * ((x : ℤ) : ℝ) ^ k
        = 2 * Real.pi * (a : ℝ)
            * (((x + n : ℤ) : ℝ) ^ k - ((x : ℤ) : ℝ) ^ k) by ring, hmR]
    field_simp
  rw [Ephase, Ephase, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨a * m, ?_⟩
  have h := congrArg (fun t : ℝ => (t : ℂ)) hdiff
  push_cast at h
  have hgoal : ((wphase n a k (x + n) : ℝ) : ℂ)
      = ((wphase n a k x : ℝ) : ℂ) + ((a * m : ℤ) : ℂ) * (2 * Real.pi) := by
    push_cast
    linear_combination h
  rw [hgoal]
  ring

/-- The `(k-1)`-fold difference of the phase `wphase n a k` is affine. -/
lemma iterDiff_wphase (n : ℕ) (a : ℤ) (k : ℕ) (hk : 2 ≤ k) (h : Fin (k - 1) → ℤ) :
    ∃ c : ℤ, ∀ x : ℤ,
      iterDiff (wphase n a k) (k - 1) h x
        = 2 * Real.pi * (a : ℝ) / (n : ℝ)
            * ((k.factorial : ℝ) * (∏ i : Fin (k - 1), (h i : ℝ)) * (x : ℝ) + (c : ℝ)) := by
  obtain ⟨c, hc⟩ := iterDiff_pow_affine k hk h
  refine ⟨c, fun x => ?_⟩
  have h1 : wphase n a k = fun y : ℤ => (2 * Real.pi * (a : ℝ) / (n : ℝ)) * (y : ℝ) ^ k := by
    funext y
    rw [wphase]
    ring
  rw [h1, iterDiff_const_mul]
  simp only []
  rw [hc x]

/-- The norm of a complete sum of a linear phase. -/
lemma norm_sum_Ephase_linear (n : ℕ) (hn : 0 < n) (m c : ℤ) :
    ‖∑ x ∈ Finset.range n,
        Ephase (fun y : ℤ => 2 * Real.pi * ((m * y + c : ℤ) : ℝ) / (n : ℝ)) x‖
      = if (n : ℤ) ∣ m then (n : ℝ) else 0 := by
  classical
  set ζ : ℂ := Complex.exp (((((2 * Real.pi * (m : ℝ)) / (n : ℝ)) : ℝ) : ℂ) * Complex.I) with hζdef
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hzn : ζ ^ n = 1 := by
    rw [hζdef, ← Complex.exp_nat_mul]
    rw [show (n : ℂ) * (((((2 * Real.pi * (m : ℝ)) / (n : ℝ)) : ℝ) : ℂ) * Complex.I)
        = (m : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast
      field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I m
  have hiff : ζ = 1 ↔ (n : ℤ) ∣ m := by
    rw [hζdef]
    exact exp_div_two_pi_eq_one_iff n hn m
  have hterm : ∀ x : ℕ, Ephase (fun y : ℤ => 2 * Real.pi * ((m * y + c : ℤ) : ℝ) / (n : ℝ)) x
      = Complex.exp (((((2 * Real.pi * (c : ℝ)) / (n : ℝ)) : ℝ) : ℂ) * Complex.I) * ζ ^ x := by
    intro x
    rw [Ephase, hζdef, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum, sum_range_pow_eq n hzn,
    norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  by_cases h : (n : ℤ) ∣ m
  · rw [if_pos h, if_pos (hiff.mpr h)]
    simp
  · rw [if_neg h, if_neg (fun hh => h (hiff.mp hh)), norm_zero]


/-! ## The final assembly -/

lemma Ephase_wphase_eq (q : ℕ) (a : ℤ) (k : ℕ) (r : ℕ) :
    Complex.exp (↑(2 * Real.pi * a * (r : ℝ) ^ k / q) * Complex.I)
      = Ephase (fun y : ℤ => 2 * Real.pi * a * (y : ℝ) ^ k / (q : ℝ)) (r : ℤ) := by
  rw [Ephase]
  congr 1

lemma le_two_pow_pred (k : ℕ) (hk : 1 ≤ k) : k ≤ 2 ^ (k - 1) := by
  have h : ∀ n : ℕ, n + 1 ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp only [pow_succ]; omega
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact h n

theorem hua_bound (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : ℤ), 0 < q → Int.gcd a (q : ℤ) = 1 →
      ‖((q : ℂ))⁻¹ * ∑ r ∈ Finset.range q,
          Complex.exp (↑(2 * Real.pi * a * (r : ℝ) ^ k / q) * Complex.I)‖
        ≤ C * (q : ℝ) ^ (-(1 / (2 : ℝ) ^ (k - 1)) + ε) := by
  rcases eq_or_lt_of_le hk with h1 | h2
  · refine ⟨1, one_pos, fun q a hq hgcd => ?_⟩
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hsum_eq : (∑ r ∈ Finset.range q,
          Complex.exp (↑(2 * Real.pi * a * (r : ℝ) ^ k / q) * Complex.I))
        = ∑ r ∈ Finset.range q,
            Ephase (fun y : ℤ => 2 * Real.pi * a * (y : ℝ) ^ k / (q : ℝ)) r := by
      apply Finset.sum_congr rfl
      intro r _
      exact Ephase_wphase_eq q a k r
    have hphase_eq : (fun y : ℤ => 2 * Real.pi * a * (y : ℝ) ^ k / (q : ℝ))
        = fun y : ℤ => 2 * Real.pi * ((a * y + 0 : ℤ) : ℝ) / (q : ℝ) := by
      funext y
      have hk1 : (y : ℝ) ^ k = (y : ℝ) := by simp only [← h1, pow_one]
      rw [hk1]
      push_cast
      ring
    have hnorm : ‖(q : ℂ)⁻¹ * ∑ r ∈ Finset.range q,
          Complex.exp (↑(2 * Real.pi * a * (r : ℝ) ^ k / q) * Complex.I)‖
        = (q : ℝ)⁻¹ * ‖∑ r ∈ Finset.range q,
            Complex.exp (↑(2 * Real.pi * a * (r : ℝ) ^ k / q) * Complex.I)‖ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
    have hk1' : k - 1 = 0 := by omega
    have hexp_eq : (-(1 / (2 : ℝ) ^ (k - 1)) + ε) = (-(1 / (1 : ℝ)) + ε) := by
      rw [hk1']; norm_num
    rw [hnorm, hsum_eq, hphase_eq, norm_sum_Ephase_linear q hq a 0, hexp_eq]
    by_cases hqa : (q : ℤ) ∣ a
    · rw [if_pos hqa]
      have hq1 : q = 1 := by
        have hnat : q ∣ Int.natAbs a := by
          have h2 : (q : ℤ) ∣ (Int.natAbs a : ℤ) := by simpa using hqa
          exact_mod_cast h2
        have hgcd' : Nat.gcd (Int.natAbs a) q = 1 := by
          have h5 : Int.gcd a (q : ℤ) = 1 := hgcd
          rwa [Int.gcd_eq_natAbs, Int.natAbs_natCast] at h5
        have h : q ∣ 1 := by
          have h4 : q ∣ Nat.gcd (Int.natAbs a) q := Nat.dvd_gcd hnat dvd_rfl
          rwa [hgcd'] at h4
        exact Nat.dvd_one.mp h
      subst hq1
      norm_num
    · rw [if_neg hqa]
      simp only [mul_zero, norm_zero]
      positivity
  · have hk2 : 2 ≤ k := h2
    obtain ⟨C1, hC1pos, hC1⟩ := cntN_factorial_le k hk2
      (show (0 : ℝ) < ε * (2 : ℝ) ^ (k - 1) by positivity)
    refine ⟨max 1 ((C1 * 2) ^ (1 / (2 : ℝ) ^ (k - 1))),
      lt_max_iff.mpr (Or.inl one_pos), fun q a hq hgcd => ?_⟩
    set m : ℝ := (2 : ℝ) ^ (k - 1) with hmdef
    have hmpos : 0 < m := by positivity
    have hmne : m ≠ 0 := ne_of_gt hmpos
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hsum_eq : (∑ r ∈ Finset.range q,
          Complex.exp (↑(2 * Real.pi * a * (r : ℝ) ^ k / q) * Complex.I))
        = ∑ x ∈ Finset.range q, Ephase (wphase q a k) x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Ephase, wphase]
      congr 1
    rw [hsum_eq]
    have hdiff := norm_sum_pow_le_diff q (k - 1) hq (Ephase (wphase q a k))
      (fun x => Ephase_wphase_add q hq a k x)
    have hinner : ∀ h : Fin (k - 1) → Fin q,
        ‖∑ x ∈ Finset.range q,
            iterSh (Ephase (wphase q a k)) (k - 1) (fun i => (h i : ℤ)) x‖
          = if (q : ℤ) ∣ a * (k.factorial : ℤ) * ∏ i : Fin (k - 1), ((h i : ℕ) : ℤ)
              then (q : ℝ) else 0 := by
      intro h
      rw [iterSh_Ephase]
      obtain ⟨c, hc⟩ := iterDiff_wphase q a k hk2 (fun i => (h i : ℤ))
      have hphase : iterDiff (wphase q a k) (k - 1) (fun i => (h i : ℤ))
          = fun y : ℤ => 2 * Real.pi
              * (((a * (k.factorial : ℤ) * ∏ i : Fin (k - 1), (h i : ℤ)) * y + a * c : ℤ) : ℝ)
              / (q : ℝ) := by
        funext y
        rw [hc y]
        field_simp
        push_cast
        ring
      rw [hphase]
      exact norm_sum_Ephase_linear q hq _ _
    have hgcd' : (q : ℤ).gcd a = 1 := (Int.gcd_comm a (q : ℤ)).symm.trans hgcd
    have hcond : ∀ h : Fin (k - 1) → Fin q,
        ((q : ℤ) ∣ a * (k.factorial : ℤ) * ∏ i : Fin (k - 1), ((h i : ℕ) : ℤ))
          ↔ q ∣ k.factorial * ∏ i : Fin (k - 1), (h i : ℕ) := by
      intro h
      have hM : ((k.factorial : ℤ) * ∏ i : Fin (k - 1), ((h i : ℕ) : ℤ))
          = ((k.factorial * ∏ i : Fin (k - 1), (h i : ℕ) : ℕ) : ℤ) := by
        push_cast
        ring
      constructor
      · intro hp
        have h1 : (q : ℤ) ∣ ((k.factorial : ℤ) * ∏ i : Fin (k - 1), ((h i : ℕ) : ℤ)) * a := by
          have he : ((k.factorial : ℤ) * ∏ i : Fin (k - 1), ((h i : ℕ) : ℤ)) * a
              = a * (k.factorial : ℤ) * ∏ i : Fin (k - 1), ((h i : ℕ) : ℤ) := by ring
          rw [he]; exact hp
        have h2 := Int.dvd_of_dvd_mul_left_of_gcd_one h1 hgcd'
        rw [hM] at h2
        exact_mod_cast h2
      · intro hq'
        have h2 : (q : ℤ) ∣ ((k.factorial * ∏ i : Fin (k - 1), (h i : ℕ) : ℕ) : ℤ) := by
          exact_mod_cast hq'
        rw [← hM] at h2
        have he : a * (k.factorial : ℤ) * ∏ i : Fin (k - 1), ((h i : ℕ) : ℤ)
            = a * ((k.factorial : ℤ) * ∏ i : Fin (k - 1), ((h i : ℕ) : ℤ)) := by ring
        rw [he]
        exact Dvd.dvd.mul_left h2 a
    have hsum_le : (∑ h : Fin (k - 1) → Fin q,
          ‖∑ x ∈ Finset.range q,
            iterSh (Ephase (wphase q a k)) (k - 1) (fun i => (h i : ℤ)) x‖)
        ≤ (q : ℝ) * cntN q (k - 1) k.factorial := by
      rw [Finset.sum_congr rfl (fun h _ => hinner h)]
      have hmul : (∑ h : Fin (k - 1) → Fin q,
            (if (q : ℤ) ∣ a * (k.factorial : ℤ) * ∏ i : Fin (k - 1), ((h i : ℕ) : ℤ)
              then (q : ℝ) else 0))
          = (q : ℝ) * ∑ h : Fin (k - 1) → Fin q,
              (if q ∣ k.factorial * ∏ i : Fin (k - 1), (h i : ℕ) then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        by_cases hp : (q : ℤ) ∣ a * (k.factorial : ℤ) * ∏ i : Fin (k - 1), ((h i : ℕ) : ℤ)
        · have hq' : q ∣ k.factorial * ∏ i : Fin (k - 1), (h i : ℕ) := (hcond h).mp hp
          rw [if_pos hp, if_pos hq']
          ring
        · have hq' : ¬ (q ∣ k.factorial * ∏ i : Fin (k - 1), (h i : ℕ)) :=
            fun hq' => hp ((hcond h).mpr hq')
          rw [if_neg hp, if_neg hq']
          ring
      rw [hmul]
      rw [show (∑ h : Fin (k - 1) → Fin q,
            (if q ∣ k.factorial * ∏ i : Fin (k - 1), (h i : ℕ) then (1 : ℝ) else 0))
          = cntN q (k - 1) k.factorial from by rw [cntN]]
    have hcast : (((2 ^ (k - 1) - (k - 1) - 1 : ℕ)) : ℝ)
        = (2 : ℝ) ^ (k - 1) - (k : ℝ) := by
      have hk_le : k ≤ 2 ^ (k - 1) := le_two_pow_pred k hk
      rw [show 2 ^ (k - 1) - (k - 1) - 1 = 2 ^ (k - 1) - k by omega]
      rw [Nat.cast_sub hk_le, Nat.cast_pow, Nat.cast_ofNat]
    have hpoweq : (q : ℝ) ^ (2 ^ (k - 1) - (k - 1) - 1)
          * (q * (q : ℝ) ^ ((k : ℝ) - 2 + ε * m)) = (q : ℝ) ^ (m - 1 + ε * m) := by
      rw [show (q : ℝ) ^ (2 ^ (k - 1) - (k - 1) - 1)
            * (q * (q : ℝ) ^ ((k : ℝ) - 2 + ε * m))
          = (q : ℝ) ^ (2 ^ (k - 1) - (k - 1) - 1) * q
            * (q : ℝ) ^ ((k : ℝ) - 2 + ε * m) by ring]
      rw [← pow_succ, ← Real.rpow_natCast (q : ℝ) ((2 ^ (k - 1) - (k - 1) - 1) + 1),
        ← Real.rpow_add hqR]
      congr 1
      push_cast
      rw [hcast, hmdef]
      ring
    have hS_le : ‖∑ x ∈ Finset.range q, Ephase (wphase q a k) x‖ ^ (2 ^ (k - 1))
        ≤ C1 * (q : ℝ) ^ (m - 1 + ε * m) := by
      calc ‖∑ x ∈ Finset.range q, Ephase (wphase q a k) x‖ ^ (2 ^ (k - 1))
          ≤ (q : ℝ) ^ (2 ^ (k - 1) - (k - 1) - 1)
              * ((q : ℝ) * cntN q (k - 1) k.factorial) :=
            hdiff.trans (mul_le_mul_of_nonneg_left hsum_le (by positivity))
        _ ≤ (q : ℝ) ^ (2 ^ (k - 1) - (k - 1) - 1)
              * ((q : ℝ) * (C1 * (q : ℝ) ^ ((k : ℝ) - 2 + ε * m))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left (hC1 q hq) (by positivity)
        _ = C1 * ((q : ℝ) ^ (2 ^ (k - 1) - (k - 1) - 1)
              * (q * (q : ℝ) ^ ((k : ℝ) - 2 + ε * m))) := by ring
        _ = C1 * (q : ℝ) ^ (m - 1 + ε * m) := by rw [hpoweq]
    have hS_root : ‖∑ x ∈ Finset.range q, Ephase (wphase q a k) x‖
        ≤ C1 ^ (1 / m) * (q : ℝ) ^ (1 - 1 / m + ε) := by
      have h1 : ‖∑ x ∈ Finset.range q, Ephase (wphase q a k) x‖
          = (‖∑ x ∈ Finset.range q, Ephase (wphase q a k) x‖ ^ m) ^ (1 / m) := by
        rw [← Real.rpow_mul (norm_nonneg _), mul_one_div, div_self hmne, Real.rpow_one]
      rw [h1]
      calc (‖∑ x ∈ Finset.range q, Ephase (wphase q a k) x‖ ^ m) ^ (1 / m)
          ≤ (C1 * (q : ℝ) ^ (m - 1 + ε * m)) ^ (1 / m) := by
            refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
            rw [← Real.rpow_natCast (‖∑ x ∈ Finset.range q, Ephase (wphase q a k) x‖)
              (2 ^ (k - 1)), Nat.cast_pow, Nat.cast_ofNat, ← hmdef] at hS_le
            exact hS_le
        _ = C1 ^ (1 / m) * (q : ℝ) ^ ((m - 1 + ε * m) * (1 / m)) := by
            rw [Real.mul_rpow (le_of_lt hC1pos) (Real.rpow_nonneg (le_of_lt hqR) _),
              ← Real.rpow_mul (le_of_lt hqR)]
        _ = C1 ^ (1 / m) * (q : ℝ) ^ (1 - 1 / m + ε) := by
            congr 1
            rw [mul_comm]
            congr 1
            field_simp
    have hnorm : ‖(q : ℂ)⁻¹ * ∑ x ∈ Finset.range q, Ephase (wphase q a k) x‖
        = (q : ℝ)⁻¹ * ‖∑ x ∈ Finset.range q, Ephase (wphase q a k) x‖ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
    rw [hnorm]
    calc (q : ℝ)⁻¹ * ‖∑ x ∈ Finset.range q, Ephase (wphase q a k) x‖
        ≤ (q : ℝ)⁻¹ * (C1 ^ (1 / m) * (q : ℝ) ^ (1 - 1 / m + ε)) :=
          mul_le_mul_of_nonneg_left hS_root (by positivity)
      _ = C1 ^ (1 / m) * (q : ℝ) ^ (-1 + (1 - 1 / m + ε)) := by
          rw [show (q : ℝ)⁻¹ * (C1 ^ (1 / m) * (q : ℝ) ^ (1 - 1 / m + ε))
              = C1 ^ (1 / m) * ((q : ℝ)⁻¹ * (q : ℝ) ^ (1 - 1 / m + ε)) by ring,
            ← Real.rpow_neg_one (q : ℝ), ← Real.rpow_add hqR]
      _ = C1 ^ (1 / m) * (q : ℝ) ^ (-1 / m + ε) := by
          rw [show -1 + (1 - 1 / m + ε) = -1 / m + ε by ring]
      _ = C1 ^ (1 / m) * (q : ℝ) ^ (-(1 / (2 : ℝ) ^ (k - 1)) + ε) := by
          rw [hmdef]
          ring
      _ ≤ max 1 ((C1 * 2) ^ (1 / (2 : ℝ) ^ (k - 1)))
            * (q : ℝ) ^ (-(1 / (2 : ℝ) ^ (k - 1)) + ε) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (le_of_lt hqR) _)
          rw [← hmdef]
          refine le_trans (Real.rpow_le_rpow (le_of_lt hC1pos) (by linarith)
            (div_nonneg zero_le_one (le_of_lt hmpos))) (le_max_right _ _)

end Commons.Analysis.ExponentialSums