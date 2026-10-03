import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.exists_card_eq_isSS
import Submission.Work.BourgainPlan.IonescuWainger.ss_sum_le_core_sum
import Submission.Work.BourgainPlan.IonescuWainger.binom_half_pow_sum_le
import Submission.Work.BourgainPlan.IonescuWainger.tuple_image_card_le_sum_bound

/-!
# The sunflower bound on square functions

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066,
§3 (`sunflower-sec`), Corollary `sunsquare` (first inequality); the `k = 1` case is
Ionescu–Wainger, Lemma 2.3.

The pointwise (for each `x`) form of the corollary says: if `M` is at least the Erdős–Rado
sunflower threshold `Sun k r` — every family of `M` distinct sets of cardinality at most `k`
contains `r` distinct members forming a sunflower, which is the hypothesis `hsun` below — then for
every weight `w : Finset α → ℝ≥0` on `k`-element subsets,

`(Σ_{|A|=k} w A)^r ≤ (4M)^r Σ_{A₀, |A₀| ≤ k} Σ^{**}_{A_1,…,A_r} ∏_i w (A₀ ∪ A_i)`,

where `Σ^{**}` runs over tuples of pairwise disjoint subsets `A_i ⊆ α \ A₀` with
`|A_i| = k - |A₀|`, i.e. the sets `A₀ ∪ A_1, …, A₀ ∪ A_r` form a sunflower with core `A₀`.

The proof is Tao's.  Normalise `Σ w = 1` and view `w` as the density of a random `k`-subset `A`;
the `Σ^{**}`-sum is exactly the probability that `r` independent copies of `A` form a sunflower.
If some `k`-subset carries mass at least `(4M)^{-1}` then all `r` copies agree with it with
probability at least `(4M)^{-r}`; otherwise `2M` independent copies show a sunflower with
probability at least `1/2` (the "bad" event that they take at most `M - 1` distinct values has
probability at most `1/3`, by `tuple_image_card_le_sum_bound` and `binom_half_pow_sum_le`), so some
`r` of the positions carry an `IsSS` tuple with probability at least
`2^{-1} C(2M,r)^{-1} ≥ (4M)^{-r}` (the union bound, via `sum_ss_restrict` and
`exists_card_eq_isSS`).

The counting lemmas `tuple_image_card_le_sum_bound` (the "first occurrence" bound on the tuples
whose value set is small), `exists_card_eq_isSS` (extraction of a witnessing index set),
`ss_sum_le_core_sum` (the sunflower sum rewritten as a sum over cores and petals) and
`binom_half_pow_sum_le` (the numerical constant) are proved in the sibling files imported above.
-/

open Finset BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.BourgainPlan.IonescuWainger
-- Auxiliary tuple-sum infrastructure (merged into sunflower_square_function.lean)

open Finset BigOperators

/-- Expanding a power of a sum over a finite type as a sum over tuples. -/
theorem sum_pow_pi {γ : Type*} [Fintype γ] (h : γ → NNReal) (n : ℕ) :
    (∑ a : γ, h a) ^ n = ∑ g : Fin n → γ, ∏ i : Fin n, h (g i) := by
  rw [Finset.sum_pow']
  simp [Fintype.piFinset_univ]

/-- The sum over all tuples of a product of a function of one coordinate factorizes. -/
theorem sum_pi_prod {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype γ] (h : γ → NNReal) :
    (∑ f : ι → γ, ∏ i : ι, h (f i)) = (∑ a : γ, h a) ^ (Fintype.card ι) := by
  calc (∑ f : ι → γ, ∏ i : ι, h (f i))
      = ∑ x ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset γ)), ∏ i : ι, h (x i) := by
        rw [Fintype.piFinset_univ]
    _ = ∏ i : ι, ∑ a ∈ (Finset.univ : Finset γ), h a :=
        (Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset γ)) (fun _ a => h a)).symm
    _ = (∑ a : γ, h a) ^ Fintype.card ι := by
        rw [Finset.prod_const, Finset.card_univ]

section Combine

variable {β : Type*}

/-- Glue a pair of functions on `I` and on its complement into a function on `Fin n`. -/
def combinePi {n : ℕ} (I : Finset (Fin n)) (α : (i : ↥I) → β)
    (ψ : (i : ↥(Iᶜ)) → β) : Fin n → β :=
  fun j => if h : j ∈ I then α ⟨j, h⟩ else ψ ⟨j, Finset.mem_compl.mpr h⟩

theorem combinePi_of_mem {n : ℕ} (I : Finset (Fin n)) (α : (i : ↥I) → β)
    (ψ : (i : ↥(Iᶜ)) → β) {j : Fin n} (h : j ∈ I) : combinePi I α ψ j = α ⟨j, h⟩ :=
  dif_pos h

theorem combinePi_of_notMem {n : ℕ} (I : Finset (Fin n)) (α : (i : ↥I) → β)
    (ψ : (i : ↥(Iᶜ)) → β) {j : Fin n} (h : j ∉ I) :
    combinePi I α ψ j = ψ ⟨j, Finset.mem_compl.mpr h⟩ :=
  dif_neg h

theorem combinePi_restrict {n : ℕ} (I : Finset (Fin n)) (g : Fin n → β) :
    combinePi I (fun i => g i.1) (fun j => g j.1) = g := by
  funext j
  by_cases h : j ∈ I
  · rw [combinePi_of_mem I _ _ h]
  · rw [combinePi_of_notMem I _ _ h]

/-- The bijection between functions on `Fin n` and pairs of functions on `I` and on its
complement. -/
noncomputable def combinePiEquiv {n : ℕ} (I : Finset (Fin n)) :
    ((i : ↥I) → β) × ((i : ↥(Iᶜ)) → β) ≃ (Fin n → β) where
  toFun p := combinePi I p.1 p.2
  invFun g := (fun i => g i.1, fun j => g j.1)
  left_inv := by
    rintro ⟨α, ψ⟩
    refine Prod.ext ?_ ?_
    · funext j
      show combinePi I α ψ ↑j = α j
      rw [combinePi_of_mem I α ψ j.2]
    · funext j
      show combinePi I α ψ ↑j = ψ j
      rw [combinePi_of_notMem I α ψ (Finset.mem_compl.mp j.2)]
  right_inv := by
    intro g
    show combinePi I (fun i => g ↑i) (fun j => g ↑j) = g
    exact combinePi_restrict I g

theorem sum_combine {n : ℕ} [Fintype β] (I : Finset (Fin n)) (F : (Fin n → β) → NNReal) :
    (∑ g : Fin n → β, F g) =
      ∑ p : ((i : ↥I) → β) × ((i : ↥(Iᶜ)) → β), F (combinePi I p.1 p.2) := by
  refine Fintype.sum_equiv (combinePiEquiv I).symm (fun g : Fin n → β => F g)
    (fun p : ((i : ↥I) → β) × ((i : ↥(Iᶜ)) → β) => F (combinePi I p.1 p.2)) ?_
  intro g
  show F g = F (combinePi I (fun i => g ↑i) (fun j => g ↑j))
  rw [combinePi_restrict I g]

/-- The product over `Fin n` of a function of `combinePi I α ψ` splits as a product over
`I` and a product over its complement. -/
theorem prod_combinePi {n : ℕ} (I : Finset (Fin n)) (ŵ : β → NNReal)
    (α : (i : ↥I) → β) (ψ : (i : ↥(Iᶜ)) → β) :
    (∏ j : Fin n, ŵ (combinePi I α ψ j)) = (∏ i : ↥I, ŵ (α i)) *
      (∏ j : ↥(Iᶜ), ŵ (ψ j)) := by
  have h1 : (∏ j : Fin n, ŵ (combinePi I α ψ j))
      = ∏ j ∈ (I ∪ Iᶜ : Finset (Fin n)), ŵ (combinePi I α ψ j) := by
    rw [Finset.union_compl]
  have hI : (∏ j ∈ I, ŵ (combinePi I α ψ j)) = ∏ i : ↥I, ŵ (α i) := by
    rw [← Finset.prod_attach I (fun j => ŵ (combinePi I α ψ j)), Finset.attach_eq_univ]
    exact Finset.prod_congr rfl (fun i _ => by rw [combinePi_of_mem I α ψ i.2])
  have hJ : (∏ j ∈ Iᶜ, ŵ (combinePi I α ψ j)) = ∏ j : ↥(Iᶜ), ŵ (ψ j) := by
    rw [← Finset.prod_attach (Iᶜ) (fun j => ŵ (combinePi I α ψ j)), Finset.attach_eq_univ]
    exact Finset.prod_congr rfl (fun i _ => by rw [combinePi_of_notMem I α ψ (Finset.mem_compl.mp i.2)])
  rw [h1, Finset.prod_union (disjoint_compl_right (a := I)), hI, hJ]

end Combine

section SSR

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The weight of the tuples `Fin n → Finset α` whose restriction to the `r`-element set `I` is an
`IsSS` tuple: the restriction contributes the sunflower sum, the complementary coordinates each
contribute the total mass `∑ A, ŵ A`. -/
theorem sum_ss_restrict {n r k : ℕ}
    (I : Finset (Fin n)) (hI : I.card = r) (ŵ : Finset α → NNReal) :
    (∑ g : Fin n → Finset α,
        (if IsSS k (fun i : Fin r => g ↑(I.orderIsoOfFin hI i)) then ∏ j : Fin n, ŵ (g j) else 0))
      = (∑ X : Fin r → Finset α, if IsSS k X then ∏ i : Fin r, ŵ (X i) else 0)
          * (∑ A : Finset α, ŵ A) ^ (n - r) := by
  classical
  rw [sum_combine I]
  have hstep : ∀ p : ((i : ↥I) → Finset α) × ((i : ↥(Iᶜ)) → Finset α),
      (if IsSS k (fun i : Fin r => combinePi I p.1 p.2 ↑(I.orderIsoOfFin hI i)) then
          ∏ j : Fin n, ŵ (combinePi I p.1 p.2 j) else 0)
        = (if IsSS k (fun i : Fin r => p.1 (I.orderIsoOfFin hI i)) then
              ∏ i : ↥I, ŵ (p.1 i) else 0) * (∏ j : ↥(Iᶜ), ŵ (p.2 j)) := by
    intro p
    obtain ⟨f, ψ⟩ := p
    have hcond : (fun i : Fin r => combinePi I f ψ ↑(I.orderIsoOfFin hI i))
        = (fun i : Fin r => f (I.orderIsoOfFin hI i)) := by
      funext i
      rw [combinePi_of_mem I f ψ ((I.orderIsoOfFin hI i).2)]
    rw [hcond, prod_combinePi]
    by_cases h : IsSS k (fun i : Fin r => f (I.orderIsoOfFin hI i))
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [Finset.sum_congr rfl (fun p _ => hstep p), Fintype.sum_prod_type]
  dsimp only
  have hmul : (∑ x : ↥I → Finset α, ∑ y : ↥(Iᶜ) → Finset α,
        (if IsSS k (fun i : Fin r => x (I.orderIsoOfFin hI i)) then ∏ i : ↥I, ŵ (x i) else 0) *
          (∏ j : ↥(Iᶜ), ŵ (y j)))
      = (∑ x : ↥I → Finset α,
            (if IsSS k (fun i : Fin r => x (I.orderIsoOfFin hI i)) then ∏ i : ↥I, ŵ (x i) else 0)) *
        (∑ y : ↥(Iᶜ) → Finset α, ∏ j : ↥(Iᶜ), ŵ (y j)) :=
    (Finset.sum_mul_sum Finset.univ Finset.univ _ _).symm
  have h1 : (∑ x : ↥I → Finset α,
        (if IsSS k (fun i : Fin r => x (I.orderIsoOfFin hI i)) then ∏ i : ↥I, ŵ (x i) else 0))
      = ∑ X : Fin r → Finset α, if IsSS k X then ∏ i : Fin r, ŵ (X i) else 0 := by
    refine Fintype.sum_equiv
      (Equiv.arrowCongr (I.orderIsoOfFin hI : Fin r ≃ ↥I).symm (Equiv.refl (Finset α)))
      (fun f : ↥I → Finset α =>
        if IsSS k (fun i : Fin r => f (I.orderIsoOfFin hI i)) then ∏ i : ↥I, ŵ (f i) else 0)
      (fun X : Fin r → Finset α => if IsSS k X then ∏ i : Fin r, ŵ (X i) else 0) ?_
    intro f
    have hα : (Equiv.arrowCongr (I.orderIsoOfFin hI : Fin r ≃ ↥I).symm
        (Equiv.refl (Finset α))) f = (fun i : Fin r => f (I.orderIsoOfFin hI i)) := by
      funext i
      rfl
    rw [hα]
    simp only []
    congr 1
    exact Fintype.prod_equiv (I.orderIsoOfFin hI : Fin r ≃ ↥I).symm
      (fun i : ↥I => ŵ (f i)) (fun i : Fin r => ŵ (f (I.orderIsoOfFin hI i)))
      (fun i => by simp)
  have h2 : (∑ y : ↥(Iᶜ) → Finset α, ∏ j : ↥(Iᶜ), ŵ (y j)) = (∑ A : Finset α, ŵ A) ^ (n - r) := by
    rw [sum_pi_prod, Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
  rw [hmul, h1, h2]

end SSR

/-- `(x / 4)^a * x^b = x^(a+b) * (1/4)^a` in `ℝ≥0`. -/
lemma pow_div_pow_mul_pow (x : NNReal) (a b : ℕ) :
    (x / 4) ^ a * x ^ b = x ^ (a + b) * (1 / 4 : NNReal) ^ a := by
  have h1 : (x / 4) ^ a = x ^ a * ((4 : NNReal) ^ a)⁻¹ := by rw [div_pow, div_eq_mul_inv]
  have h2 : (1 / 4 : NNReal) ^ a = (((4 : NNReal) ^ a))⁻¹ := by
    rw [div_pow, one_pow, div_eq_mul_inv, one_mul]
  rw [h1, h2, pow_add]
  ring

/-- **The sunflower bound on square functions** (Tao, arXiv:2008.05066, Corollary `sunsquare`, first inequality; the `k = 1` case is Ionescu–Wainger, Lemma 2.3). Pointwise form: if `M` is at least the Erdős–Rado sunflower threshold `Sun k r` (every family of `M` distinct sets of cardinality at most `k` contains `r` distinct members forming a sunflower), then for every weight `w : Finset α → NNReal` on `k`-element subsets,
`(Σ_{|A|=k} w A)^r ≤ (4M)^r Σ_{A₀, |A₀| ≤ k} Σ^{**}_{A_1,…,A_r} ∏_i w (A₀ ∪ A_i)`,
where `Σ^{**}` runs over tuples of pairwise disjoint subsets `A_i ⊆ α ∖ A₀` with `|A_i| = k - |A₀|` (equivalently: the sets `A₀ ∪ A_1, …, A₀ ∪ A_r` form a sunflower with core `A₀`). Proof (Tao §3): if `Σ w = 1`, view `w` as a probability density on `k`-subsets; the probabilistic Erdős–Rado theorem (Lemma `per`) gives that `r` independent samples form a sunflower with probability `≥ (4M)^{-r}`, and the `Σ^{**}`-sum is exactly that probability. -/
theorem sunflower_square_function {α : Type*} [Fintype α] [DecidableEq α]
    (k r M : ℕ) (hr : 2 ≤ r) (hM : 2 ≤ M)
    (hsun : ∀ T : Finset (Finset α), (∀ A ∈ T, A.card ≤ k) → M ≤ T.card →
      ∃ A : Fin r → Finset α, (∀ i, A i ∈ T) ∧ Function.Injective A ∧
        Work.BourgainPlan.IonescuWainger.IsSunflower A)
    (w : Finset α → NNReal) :
    (∑ A : Finset α, if A.card = k then w A else 0) ^ r
      ≤ (4 * M : NNReal) ^ r *
          ∑ A₀ : Finset α, if A₀.card ≤ k then
            ∑ A : Fin r → Finset α,
              (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
                  (∀ i j, i ≠ j → Disjoint (A i) (A j))
               then ∏ i, w (A₀ ∪ A i) else 0)
          else 0 := by
  classical
  set ŵ : Finset α → NNReal := fun A => if A.card = k then w A else 0 with hŵ
  set W : NNReal := ∑ A : Finset α, ŵ A with hW
  set n : ℕ := 2 * M with hn
  set K : ℕ := M - 1 with hK
  set SSsum : NNReal := ∑ X : Fin r → Finset α, if IsSS k X then ∏ i, w (X i) else 0 with hSS
  have hLHS : (∑ A : Finset α, if A.card = k then w A else 0) = W := by
    rw [hW, hŵ]
  -- The sunflower sum is dominated by the sum over cores and petals (Tao's `sunsquare`).
  have hSS_le : SSsum ≤ ∑ A₀ : Finset α, if A₀.card ≤ k then
      ∑ A : Fin r → Finset α,
        (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
            (∀ i j, i ≠ j → Disjoint (A i) (A j))
         then ∏ i, w (A₀ ∪ A i) else 0)
      else 0 := by
    rw [hSS]
    exact ss_sum_le_core_sum k r hr w
  have hmain : W ^ r ≤ (4 * M : NNReal) ^ r * SSsum := by
    by_cases hW0 : W = 0
    · rw [hW0, zero_pow (by omega : r ≠ 0)]
      positivity
    · have hWpos : 0 < W := lt_of_le_of_ne zero_le (Ne.symm hW0)
      by_cases hcase1 : ∃ A : Finset α, A.card = k ∧ W ≤ (4 * M : NNReal) * w A
      · obtain ⟨A, hA, hWA⟩ := hcase1
        have hconst : IsSS k (fun _ : Fin r => A) :=
          ⟨fun _ => hA, A, fun _ => le_refl A, fun i j hij => by simp⟩
        have hsingle : w A ^ r ≤ SSsum := by
          rw [hSS]
          have h1 : (if IsSS k (fun _ : Fin r => A) then
                ∏ i : Fin r, w ((fun _ : Fin r => A) i) else 0) ≤
              ∑ X : Fin r → Finset α, (if IsSS k X then ∏ i, w (X i) else 0) :=
            Finset.single_le_sum
              (f := fun X : Fin r → Finset α => if IsSS k X then ∏ i, w (X i) else 0)
              (fun i _ => by positivity) (Finset.mem_univ _)
          rw [if_pos hconst] at h1
          simpa [Finset.prod_const, Fintype.card_fin] using h1
        calc W ^ r ≤ ((4 * M : NNReal) * w A) ^ r := pow_le_pow_left₀ zero_le hWA r
          _ = (4 * M : NNReal) ^ r * w A ^ r := mul_pow _ _ _
          _ ≤ (4 * M : NNReal) ^ r * SSsum := by gcongr
      · have hcase2 : ∀ A : Finset α, A.card = k → (4 * M : NNReal) * w A < W :=
          fun A hA => not_le.mp (fun hle => hcase1 ⟨A, hA, hle⟩)
        -- Mass of any family of at most `K = M - 1` values
        have hcK : ∀ T : Finset (Finset α), T.card ≤ K → ∑ A ∈ T, ŵ A ≤ W / 4 := by
          intro T hT
          have h1 : (∑ A ∈ T, ŵ A) = ∑ A ∈ T.filter (fun A => A.card = k), w A := by
            simp only [hŵ]
            rw [← Finset.sum_filter]
          rw [h1]
          have h2 : (∑ A ∈ T.filter (fun A => A.card = k), w A) ≤
              (((T.filter (fun A => A.card = k)).card : ℕ) : NNReal) * (W / (4 * M)) := by
            rw [← nsmul_eq_mul, ← Finset.sum_const]
            refine Finset.sum_le_sum (fun A hA => ?_)
            have hcard : A.card = k := (Finset.mem_filter.mp hA).2
            rw [le_div_iff₀ (by positivity : (0 : NNReal) < 4 * M)]
            calc w A * (4 * M) = (4 * M) * w A := by ring
              _ ≤ W := le_of_lt (hcase2 A hcard)
          have h3 : (((T.filter (fun A => A.card = k)).card : ℕ) : NNReal) * (W / (4 * M))
              ≤ (K : NNReal) * (W / (4 * M)) := by
            gcongr
            exact_mod_cast le_trans (Finset.card_filter_le _ _) hT
          have h4 : (K : NNReal) * (W / (4 * M)) ≤ W / 4 := by
            rw [hK]
            have h4Mpos : (0 : NNReal) < 4 * M := by positivity
            refine le_of_mul_le_mul_right ?_ h4Mpos
            rw [mul_assoc, div_mul_cancel₀ W (ne_of_gt h4Mpos)]
            rw [← mul_assoc, div_mul_cancel₀ W (by norm_num : (4 : NNReal) ≠ 0),
              mul_comm (((M - 1 : ℕ) : NNReal)) W]
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le M 1) zero_le
          exact le_trans h2 (le_trans h3 h4)
        -- Definitions of the two parts of the total mass
        set Ev : (Fin n → Finset α) → Prop :=
          fun g => ((Finset.univ.image g).filter (fun A => A.card = k)).card ≤ K with hEv
        set u : (Fin n → Finset α) → NNReal := fun g => ∏ i, ŵ (g i) with hu
        -- The "bad" part: at most `K` distinct `k`-values
        have hEpart : (∑ g : Fin n → Finset α, if Ev g then u g else 0) ≤ (1 / 3) * W ^ n := by
          have hstep1 : (∑ g : Fin n → Finset α, if Ev g then u g else 0) ≤
              ∑ g : Fin n → Finset α, if (Finset.univ.image g).card ≤ K then u g else 0 := by
            refine Finset.sum_le_sum (fun g _ => ?_)
            by_cases hg : Ev g
            · rw [if_pos hg]
              by_cases him : (Finset.univ.image g).card ≤ K
              · rw [if_pos him]
              · rw [if_neg him]
                have hu0 : u g = 0 := by
                  by_contra hne
                  have hall : ∀ i, (g i).card = k := by
                    intro i
                    by_contra hi
                    exact hne (Finset.prod_eq_zero (Finset.mem_univ i)
                      (by simp [hŵ, hi]))
                  have himg : (Finset.univ.image g).filter (fun A => A.card = k) =
                      Finset.univ.image g := by
                    refine Finset.filter_true_of_mem (fun A hA => ?_)
                    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hA
                    exact hall i
                  rw [hEv] at hg
                  rw [himg] at hg
                  exact him hg
                rw [hu0]
            · rw [if_neg hg]
              positivity
          have hstep2 : (∑ g : Fin n → Finset α,
                if (Finset.univ.image g).card ≤ K then u g else 0)
              ≤ ∑ m ∈ Finset.range (K + 1), (n.choose m : NNReal) * (W / 4) ^ (n - m) * W ^ m := by
            have heq : (∑ g : Fin n → Finset α,
                  if (Finset.univ.image g).card ≤ K then u g else 0)
                = ∑ g : Fin n → Finset α,
                  if (Finset.univ.image g).card ≤ K then ∏ i : Fin n, ŵ (g i) else 0 := by
              refine Finset.sum_congr rfl (fun g _ => ?_)
              rw [hu]
            rw [heq]
            have hbound := tuple_image_card_le_sum_bound ŵ n K (W / 4) hcK
            rwa [← hW] at hbound
          have hstep3 : (∑ m ∈ Finset.range (K + 1),
                (n.choose m : NNReal) * (W / 4) ^ (n - m) * W ^ m) ≤ (1 / 3) * W ^ n := by
            rw [hK, show M - 1 + 1 = M by omega]
            have hterm : ∀ m ∈ Finset.range M,
                (n.choose m : NNReal) * (W / 4) ^ (n - m) * W ^ m
                  = W ^ n * ((n.choose m : NNReal) * (1 / 4 : NNReal) ^ (n - m)) := by
              intro m hm
              have hmle : m ≤ n := by
                have := Finset.mem_range.mp hm
                rw [hn]
                omega
              have hk : n - m + m = n := Nat.sub_add_cancel hmle
              calc (n.choose m : NNReal) * (W / 4) ^ (n - m) * W ^ m
                  = (n.choose m : NNReal) * ((W / 4) ^ (n - m) * W ^ m) := by ring
                _ = (n.choose m : NNReal) *
                      (W ^ ((n - m) + m) * (1 / 4 : NNReal) ^ (n - m)) := by
                      rw [pow_div_pow_mul_pow]
                _ = W ^ n * ((n.choose m : NNReal) * (1 / 4 : NNReal) ^ (n - m)) := by
                      rw [hk]; ring
            rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
            calc W ^ n * (∑ m ∈ Finset.range M,
                    (n.choose m : NNReal) * (1 / 4 : NNReal) ^ (n - m))
                ≤ W ^ n * (1 / 3) := by
                  gcongr
                  rw [hn]
                  exact binom_half_pow_sum_le hM
              _ = (1 / 3) * W ^ n := by ring
          exact le_trans hstep1 (le_trans hstep2 hstep3)
        -- The total mass
        have htotal : (∑ g : Fin n → Finset α, u g) = W ^ n := by
          have heq : (∑ g : Fin n → Finset α, u g)
              = ∑ g : Fin n → Finset α, ∏ i : Fin n, ŵ (g i) := by
            refine Finset.sum_congr rfl (fun g _ => ?_)
            rw [hu]
          rw [heq, hW]
          exact (sum_pow_pi ŵ n).symm
        -- The union bound
        set SSsumW : NNReal := ∑ X : Fin r → Finset α, if IsSS k X then ∏ i, ŵ (X i) else 0
          with hSSW
        have hSSWeq : SSsumW = SSsum := by
          rw [hSSW, hSS]
          refine Finset.sum_congr rfl (fun X _ => ?_)
          by_cases h : IsSS k X
          · rw [if_pos h, if_pos h]
            refine Finset.prod_congr rfl (fun i _ => ?_)
            simp [hŵ, h.card_eq i]
          · rw [if_neg h, if_neg h]
        have hsumI : ∀ (I : Finset (Fin n)) (hI : I.card = r),
            (∑ g : Fin n → Finset α,
                if IsSS k (fun i : Fin r => g ↑(I.orderIsoOfFin hI i)) then u g else 0)
              = SSsumW * W ^ (n - r) := by
          intro I hI
          rw [hSSW, hW]
          have heq : (∑ g : Fin n → Finset α,
                if IsSS k (fun i : Fin r => g ↑(I.orderIsoOfFin hI i)) then u g else 0)
              = ∑ g : Fin n → Finset α,
                if IsSS k (fun i : Fin r => g ↑(I.orderIsoOfFin hI i)) then
                  ∏ j : Fin n, ŵ (g j) else 0 := by
            refine Finset.sum_congr rfl (fun g _ => ?_)
            rw [hu]
          rw [heq]
          exact sum_ss_restrict I hI ŵ
        have hpt : ∀ g : Fin n → Finset α, (if ¬ Ev g then u g else 0) ≤
            ∑ I : Finset (Fin n), (if h : I.card = r then
              (if IsSS k (fun i : Fin r => g ↑(I.orderIsoOfFin h i)) then u g else 0) else 0) := by
          intro g
          by_cases hg : Ev g
          · rw [if_neg (not_not_intro hg)]
            positivity
          · rw [if_pos hg]
            by_cases hu0 : u g = 0
            · rw [hu0]
              positivity
            · have hall : ∀ i, (g i).card = k := by
                intro i
                by_contra hi
                exact hu0 (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hŵ, hi]))
              have himg : (Finset.univ.image g).filter (fun A => A.card = k) =
                  Finset.univ.image g := by
                refine Finset.filter_true_of_mem (fun A hA => ?_)
                obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hA
                exact hall i
              have hTcard : M ≤ ((Finset.univ.image g).filter (fun A => A.card = k)).card := by
                rw [hEv] at hg
                dsimp only at hg
                rw [himg, hK] at hg
                rw [himg]
                omega
              obtain ⟨A, hAT, hinj, hsunf⟩ :=
                hsun _ (fun A hA => le_of_eq (Finset.mem_filter.mp hA).2) hTcard
              have hss : IsSS k A :=
                isSS_of_isSunflower (fun i => (Finset.mem_filter.mp (hAT i)).2) hsunf
              obtain ⟨I, hI, hIS⟩ := exists_card_eq_isSS g A hss hinj
                (fun i => (Finset.mem_filter.mp (hAT i)).1)
              have hterm : (if h : I.card = r then
                  (if IsSS k (fun i : Fin r => g ↑(I.orderIsoOfFin h i)) then u g else 0) else 0)
                  = u g := by
                rw [dif_pos hI, if_pos hIS]
              calc u g = (if h : I.card = r then
                    (if IsSS k (fun i : Fin r => g ↑(I.orderIsoOfFin h i)) then u g else 0)
                      else 0) := hterm.symm
                _ ≤ ∑ J : Finset (Fin n), (if h : J.card = r then
                    (if IsSS k (fun i : Fin r => g ↑(J.orderIsoOfFin h i)) then u g else 0)
                      else 0) :=
                  Finset.single_le_sum
                    (f := fun J : Finset (Fin n) => (if h : J.card = r then
                      (if IsSS k (fun i : Fin r => g ↑(J.orderIsoOfFin h i)) then u g else 0)
                        else 0))
                    (fun J _ => by positivity) (Finset.mem_univ I)
        have hcount : (∑ I : Finset (Fin n), (if I.card = r then SSsumW * W ^ (n - r) else 0))
            = (n.choose r : NNReal) * (SSsumW * W ^ (n - r)) := by
          have hcard : (Finset.univ.filter (fun I : Finset (Fin n) => I.card = r)).card
              = n.choose r := by
            have h2 : (Finset.univ.filter (fun I : Finset (Fin n) => I.card = r))
                = (Finset.univ : Finset (Fin n)).powersetCard r := by
              rw [Finset.powersetCard_eq_filter, Finset.powerset_univ]
            rw [h2, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard]
        have hnonE : (∑ g : Fin n → Finset α, if ¬ Ev g then u g else 0)
            ≤ (n.choose r : NNReal) * (SSsumW * W ^ (n - r)) := by
          calc (∑ g : Fin n → Finset α, if ¬ Ev g then u g else 0)
              ≤ ∑ g : Fin n → Finset α, ∑ I : Finset (Fin n), (if h : I.card = r then
                  (if IsSS k (fun i : Fin r => g ↑(I.orderIsoOfFin h i)) then u g else 0)
                    else 0) := Finset.sum_le_sum (fun g _ => hpt g)
            _ = ∑ I : Finset (Fin n), ∑ g : Fin n → Finset α, (if h : I.card = r then
                  (if IsSS k (fun i : Fin r => g ↑(I.orderIsoOfFin h i)) then u g else 0)
                    else 0) := Finset.sum_comm
            _ = ∑ I : Finset (Fin n), (if I.card = r then SSsumW * W ^ (n - r) else 0) := by
                refine Finset.sum_congr rfl (fun I _ => ?_)
                by_cases hI : I.card = r
                · simp only [dif_pos hI, if_pos hI]
                  exact hsumI I hI
                · simp [dif_neg hI, if_neg hI]
            _ = (n.choose r : NNReal) * (SSsumW * W ^ (n - r)) := hcount
        -- (2/3) W^n ≤ (choose n r) SSsumW W^(n-r)
        have htwo : (2 / 3 : NNReal) * W ^ n
            ≤ (n.choose r : NNReal) * (SSsumW * W ^ (n - r)) := by
          have hsum2 : W ^ n = (∑ g : Fin n → Finset α, if Ev g then u g else 0) +
              (∑ g : Fin n → Finset α, if ¬ Ev g then u g else 0) := by
            rw [← htotal]
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun g _ => ?_)
            by_cases hg : Ev g <;> simp [hg]
          have h3 : (2 / 3 : NNReal) * W ^ n + (1 / 3) * W ^ n
              = (∑ g : Fin n → Finset α, if Ev g then u g else 0) +
                (∑ g : Fin n → Finset α, if ¬ Ev g then u g else 0) := by
            rw [hsum2]
            ring
          have h4 : (2 / 3 : NNReal) * W ^ n + (1 / 3) * W ^ n
              ≤ (∑ g : Fin n → Finset α, if ¬ Ev g then u g else 0) + (1 / 3) * W ^ n := by
            rw [h3]
            calc (∑ g : Fin n → Finset α, if Ev g then u g else 0) +
                  (∑ g : Fin n → Finset α, if ¬ Ev g then u g else 0)
                ≤ (1 / 3) * W ^ n + (∑ g : Fin n → Finset α, if ¬ Ev g then u g else 0) :=
                  add_le_add hEpart le_rfl
              _ = (∑ g : Fin n → Finset α, if ¬ Ev g then u g else 0) + (1 / 3) * W ^ n :=
                  add_comm _ _
          have h5 : (2 / 3 : NNReal) * W ^ n
              ≤ ∑ g : Fin n → Finset α, if ¬ Ev g then u g else 0 :=
            (add_le_add_iff_right ((1 / 3) * W ^ n)).mp h4
          exact le_trans h5 hnonE
        -- cancel the total mass and finish
        have hrn : r ≤ n := by
          by_contra hlt
          have hchoose : n.choose r = 0 := Nat.choose_eq_zero_of_lt (by omega)
          have hz : (n.choose r : NNReal) * (SSsumW * W ^ (n - r)) = 0 := by
            rw [hchoose, Nat.cast_zero, zero_mul]
          have hzero : (2 / 3 : NNReal) * W ^ n = 0 := le_antisymm (by rw [← hz]; exact htwo) zero_le
          have hpos : (0 : NNReal) < 2 / 3 := by norm_num
          have hWn : W ^ n = 0 := by nlinarith
          exact hW0 (pow_eq_zero_iff (by omega : n ≠ 0) |>.mp hWn)
        have hcancel : (2 / 3 : NNReal) * W ^ r ≤ (n.choose r : NNReal) * SSsumW := by
          have hsplitn : W ^ n = W ^ r * W ^ (n - r) := by
            rw [← pow_add, Nat.add_sub_cancel' hrn]
          have h1 : ((2 / 3 : NNReal) * W ^ r) * W ^ (n - r)
              ≤ ((n.choose r : NNReal) * SSsumW) * W ^ (n - r) := by
            calc ((2 / 3 : NNReal) * W ^ r) * W ^ (n - r)
                = (2 / 3 : NNReal) * (W ^ r * W ^ (n - r)) := by ring
              _ = (2 / 3 : NNReal) * W ^ n := by rw [← hsplitn]
              _ ≤ (n.choose r : NNReal) * (SSsumW * W ^ (n - r)) := htwo
              _ = ((n.choose r : NNReal) * SSsumW) * W ^ (n - r) := by ring
          exact le_of_mul_le_mul_right h1 (pow_pos hWpos _)
        have h32 : (3 / 2 : NNReal) * (n : NNReal) ^ r ≤ (4 * M : NNReal) ^ r := by
          have hp1 : (3 / 2 : NNReal) ≤ 2 := by
            rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 2)]
            norm_num
          have hp2 : (2 : NNReal) ≤ (2 : NNReal) ^ r := by
            calc (2 : NNReal) = (2 : NNReal) ^ 1 := by ring
              _ ≤ (2 : NNReal) ^ r := pow_le_pow_right₀ (by norm_num) (by omega)
          have hp : (3 / 2 : NNReal) ≤ (2 : NNReal) ^ r := le_trans hp1 hp2
          have hcast : (n : NNReal) = (2 : NNReal) * (M : NNReal) := by
            rw [hn]; push_cast; ring
          rw [hcast]
          calc (3 / 2 : NNReal) * ((2 : NNReal) * (M : NNReal)) ^ r
              = (3 / 2 : NNReal) * ((2 : NNReal) ^ r * (M : NNReal) ^ r) := by rw [mul_pow]
            _ ≤ (2 : NNReal) ^ r * ((2 : NNReal) ^ r * (M : NNReal) ^ r) :=
                mul_le_mul_of_nonneg_right hp (by positivity)
            _ = (((2 : NNReal) * 2) ^ r) * (M : NNReal) ^ r := by rw [mul_pow]; ring
            _ = (((4 : NNReal) * (M : NNReal))) ^ r := by
                rw [show ((2 : NNReal) * 2) = 4 by norm_num, mul_pow]
            _ = (4 * M : NNReal) ^ r := by ring
        calc W ^ r ≤ (3 / 2 : NNReal) * ((n.choose r : NNReal) * SSsumW) := by
              calc W ^ r = (3 / 2 : NNReal) * ((2 / 3 : NNReal) * W ^ r) := by ring
                _ ≤ (3 / 2 : NNReal) * ((n.choose r : NNReal) * SSsumW) := by gcongr
          _ ≤ (3 / 2 : NNReal) * ((n : NNReal) ^ r * SSsumW) := by
              gcongr
              exact_mod_cast Nat.choose_le_pow n r
          _ = ((3 / 2 : NNReal) * (n : NNReal) ^ r) * SSsumW := by ring
          _ ≤ (4 * M : NNReal) ^ r * SSsumW := by
              gcongr
          _ = (4 * M : NNReal) ^ r * SSsum := by rw [hSSWeq]
  have hfinal : (4 * M : NNReal) ^ r * SSsum ≤ (4 * M : NNReal) ^ r *
      (∑ A₀ : Finset α, if A₀.card ≤ k then
        ∑ A : Fin r → Finset α,
          (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
              (∀ i j, i ≠ j → Disjoint (A i) (A j))
           then ∏ i, w (A₀ ∪ A i) else 0)
        else 0) := by
    gcongr
  calc (∑ A : Finset α, if A.card = k then w A else 0) ^ r = W ^ r := by rw [hLHS]
    _ ≤ (4 * M : NNReal) ^ r * SSsum := hmain
    _ ≤ (4 * M : NNReal) ^ r *
          (∑ A₀ : Finset α, if A₀.card ≤ k then
            ∑ A : Fin r → Finset α,
              (if (∀ i, A i ⊆ Finset.univ \ A₀) ∧ (∀ i, (A i).card = k - A₀.card) ∧
                  (∀ i j, i ≠ j → Disjoint (A i) (A j))
               then ∏ i, w (A₀ ∪ A i) else 0)
            else 0) := hfinal
end Work.BourgainPlan.IonescuWainger
