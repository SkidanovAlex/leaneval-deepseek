/-
# The second-order ("Casimir") identity for the `E₈` Kostant partition function

`K δ = E8KostantId.KcountP δ` is the number of multisets of positive roots of `E₈` with
sum `δ`, and `⟪x,y⟫ = ∑ i, x i * (A⁻¹ y) i` is the lattice form.  The main theorem
`E8_Kostant_secondOrder` states

  `⟪δ,δ⟫ * K δ = Σ_{β,β'} Σ_{n,m ≥ 1} ⟪β,β'⟫ * K (δ - nβ - mβ') + 2 Σ_β Σ_{n ≥ 1} n * K (δ - nβ)`.

The proof is a two-marking argument.  The first-order *marking identity*
`bil_marking_PR` says that marking one element of a multiset summing to `δ` gives

  `⟪v,δ⟫ * K δ = Σ_β Σ_{n ≥ 1} ⟪v,β⟫ * K (δ - nβ)`   (`N = (e8ht δ).toNat` truncates the sum),

proved by the bijection `(n, g) ↦ g + n·e_β` between `{(n,g) : g ∈ K δ - nβ}` and the
pairs `(f, n)` with `f ∈ K δ` and `n ≤ f_β` (`kshiftEquiv`).  Applying it with `v = δ` and
then with `v = β`, `δ ↦ δ - nβ`, together with `⟪δ,β⟫ = ⟪β,δ-nβ⟫ + 2n` and `⟪β,β⟫ = 2`,
yields the second-order identity.

The development also provides the reusable ingredients: `Ksol γ` (the type of multisets
summing to `γ`, definitionally the one in `KcountP`), the height bound
`le_e8ht_of_sum_eq`, the `Function.update` shifting lemmas `sum_update_nsmul` /
`sum_update_sub_nsmul`, bilinearity of `bil` (`bil_sum_left_aux`, `bil_sum_right_aux`) and
the elementary count `card_Icc_filter_le`.
-/
import Submission.Commons.Algebra.Lie.E8_Msub_weight_finrank
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_dominant_unique

open scoped BigOperators
open Commons.LinearAlgebra.Matrix.Cartan
noncomputable section
namespace Commons.Algebra.Lie

/-! ## Part 0: generic helpers -/

lemma sum_boole_int {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    ∑ x ∈ s, (if p x then (1:ℤ) else 0) = ((s.filter p).card : ℤ) := by
  rw [Finset.sum_boole]

lemma bil_add_left_aux (a b w : Fin 8 → ℤ) : bil (a + b) w = bil a w + bil b w := by
  simp only [bil, coords, add_dotProduct]

lemma bil_add_right_aux (a b w : Fin 8 → ℤ) : bil a (b + w) = bil a b + bil a w := by
  simp only [bil, coords, Matrix.mulVec_add, dotProduct_add]

lemma bil_sum_left_aux {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℤ) (g : ι → (Fin 8 → ℤ))
    (w : Fin 8 → ℤ) : bil (∑ x ∈ s, c x • g x) w = ∑ x ∈ s, c x * bil (g x) w := by
  induction s using Finset.induction with
  | empty => simp [bil, coords]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, bil_add_left_aux, ih, bil_smul_left]

lemma bil_sum_right_aux {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℤ) (g : ι → (Fin 8 → ℤ))
    (v : Fin 8 → ℤ) : bil v (∑ x ∈ s, c x • g x) = ∑ x ∈ s, c x * bil v (g x) := by
  induction s using Finset.induction with
  | empty => simp [bil, coords]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, bil_add_right_aux, ih, bil_smul_right]

/-! ## Part 0b: shift lemmas for `Function.update` -/

lemma sum_update_nsmul {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    (f : ι → ℕ) (β : ι) (n : ℕ) (v : ι → M) :
    ∑ α, (Function.update f β (f β + n)) α • v α = (∑ α, f α • v α) + n • v β := by
  have h1 : (fun α => (Function.update f β (f β + n)) α • v α)
      = Function.update (fun α => f α • v α) β ((f β + n) • v β) := by
    funext α
    by_cases h : α = β
    · subst h; simp
    · simp [Function.update, h]
  rw [h1, Finset.sum_update_of_mem (Finset.mem_univ β)]
  rw [Finset.sdiff_singleton_eq_erase, ← Finset.add_sum_erase _ _ (Finset.mem_univ β)]
  rw [add_smul]
  abel

lemma sum_update_sub_nsmul {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    (f : ι → ℕ) (β : ι) (n : ℕ) (hn : n ≤ f β) (v : ι → M) :
    ∑ α, (Function.update f β (f β - n)) α • v α = (∑ α, f α • v α) - n • v β := by
  have h1 : (fun α => (Function.update f β (f β - n)) α • v α)
      = Function.update (fun α => f α • v α) β ((f β - n) • v β) := by
    funext α
    by_cases h : α = β
    · subst h; simp
    · simp [Function.update, h]
  have h2 : (f β - n) • v β = f β • v β - n • v β := by
    have : (f β - n) • v β + n • v β = f β • v β := by
      rw [← add_smul, Nat.sub_add_cancel hn]
    exact eq_sub_of_add_eq this
  rw [h1, Finset.sum_update_of_mem (Finset.mem_univ β), h2,
    Finset.sdiff_singleton_eq_erase, ← Finset.add_sum_erase _ _ (Finset.mem_univ β)]
  abel

/-! ## Part 1: solution set, height bounds -/

abbrev Ksol (γ : Fin 8 → ℤ) : Type := {k : PR → ℕ // ∑ α : PR, k α • (α : Fin 8 → ℤ) = γ}

lemma KcountP_eq_card (γ : Fin 8 → ℤ) : E8KostantId.KcountP γ = Nat.card (Ksol γ) := rfl

lemma le_e8ht_of_sum_eq {γ : Fin 8 → ℤ} {f : PR → ℕ}
    (hf : ∑ α, f α • (α : Fin 8 → ℤ) = γ) (α : PR) : (f α : ℤ) ≤ E8NormTwo.e8ht γ := by
  have h := e8ht_sum_nsmul f
  rw [hf] at h
  have h1 : (f α : ℤ) * 1 ≤ (f α : ℤ) * E8NormTwo.e8ht (α : Fin 8 → ℤ) :=
    mul_le_mul_of_nonneg_left (one_le_e8ht_posRoot α) (by positivity)
  have h2 : (f α : ℤ) * E8NormTwo.e8ht (α : Fin 8 → ℤ)
      ≤ ∑ β : PR, (f β : ℤ) * E8NormTwo.e8ht (β : Fin 8 → ℤ) :=
    Finset.single_le_sum (f := fun β : PR => (f β : ℤ) * E8NormTwo.e8ht (β : Fin 8 → ℤ))
      (fun β _ => mul_nonneg (by positivity) (e8ht_posRoot_nonneg β)) (Finset.mem_univ α)
  linarith [h1, h2, h.le, h.ge]

/-! ## Part 2: the shift bijection -/

def kshift (β : PR) (n : ℕ) (f : PR → ℕ) : PR → ℕ := Function.update f β (f β + n)

def kunshift (β : PR) (n : ℕ) (f : PR → ℕ) : PR → ℕ := Function.update f β (f β - n)

lemma sum_kshift (β : PR) (n : ℕ) (f : PR → ℕ) :
    ∑ α, kshift β n f α • (α : Fin 8 → ℤ)
      = (∑ α, f α • (α : Fin 8 → ℤ)) + n • (β : Fin 8 → ℤ) :=
  sum_update_nsmul f β n (fun α : PR => (α : Fin 8 → ℤ))

lemma sum_kunshift (β : PR) (n : ℕ) (f : PR → ℕ) (h : n ≤ f β) :
    ∑ α, kunshift β n f α • (α : Fin 8 → ℤ)
      = (∑ α, f α • (α : Fin 8 → ℤ)) - n • (β : Fin 8 → ℤ) :=
  sum_update_sub_nsmul f β n h (fun α : PR => (α : Fin 8 → ℤ))

lemma kshift_kunshift (β : PR) (n : ℕ) (f : PR → ℕ) (h : n ≤ f β) : kshift β n (kunshift β n f) = f := by
  funext α
  by_cases hα : α = β
  · subst hα; simp [kshift, kunshift, Nat.sub_add_cancel h]
  · simp [kshift, kunshift, hα]

lemma kunshift_kshift (β : PR) (n : ℕ) (f : PR → ℕ) : kunshift β n (kshift β n f) = f := by
  funext α
  by_cases hα : α = β
  · subst hα; simp [kshift, kunshift]
  · simp [kshift, kunshift, hα]

lemma kshift_apply (β : PR) (n : ℕ) (f : PR → ℕ) : kshift β n f β = f β + n := by
  simp [kshift]




lemma card_Icc_filter_le (N J : ℕ) (hJ : J ≤ N) :
    ((Finset.Icc 1 N).filter (fun i => i ≤ J)).card = J := by
  have h : (Finset.Icc 1 N).filter (fun i => i ≤ J) = Finset.Icc 1 J := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [h, Nat.card_Icc]
  omega

lemma Ksol_coord_le (δ : Fin 8 → ℤ) (N : ℕ) (hN : E8NormTwo.e8ht δ ≤ (N : ℤ))
    (f : Ksol δ) (β : PR) : f.1 β ≤ N := by
  have h : (f.1 β : ℤ) ≤ E8NormTwo.e8ht δ := le_e8ht_of_sum_eq f.2 β
  omega

noncomputable def kshiftMem (δ : Fin 8 → ℤ) (β : PR) (n : ℕ)
    (g : Ksol (δ - n • (β : Fin 8 → ℤ))) : Ksol δ :=
  ⟨kshift β n g.1, by rw [sum_kshift, g.2]; abel⟩

noncomputable def kunshiftMem (δ : Fin 8 → ℤ) (β : PR) (n : ℕ)
    (f : Ksol δ) (h : n ≤ f.1 β) : Ksol (δ - n • (β : Fin 8 → ℤ)) :=
  ⟨kunshift β n f.1, by rw [sum_kunshift β n f.1 h, f.2]⟩

lemma le_kshift_apply (β : PR) (n : ℕ) (f : PR → ℕ) : n ≤ kshift β n f β := by
  rw [kshift, Function.update_apply, if_pos rfl]
  omega

noncomputable def kshiftEquiv (δ : Fin 8 → ℤ) (β : PR) (n : ℕ) :
    Ksol (δ - n • (β : Fin 8 → ℤ)) ≃ {f : Ksol δ // n ≤ f.1 β} where
  toFun g := ⟨kshiftMem δ β n g, le_kshift_apply β n g.1⟩
  invFun f := kunshiftMem δ β n f.1 f.2
  left_inv g := by
    refine Subtype.ext ?_
    exact kunshift_kshift β n g.1
  right_inv f := by
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    exact kshift_kunshift β n f.1.1 f.2

/-! ## Part 3: the marking identity -/


lemma sum_coord_eq (δ : Fin 8 → ℤ) (β : PR) (N : ℕ)
    (hN : E8NormTwo.e8ht δ ≤ (N : ℤ)) :
    ∑ f : Ksol δ, (f.1 β : ℤ)
      = ∑ n ∈ Finset.Icc 1 N,
          (E8KostantId.KcountP (δ - n • (β : Fin 8 → ℤ)) : ℤ) := by
  have step1 : ∀ f : Ksol δ,
      (f.1 β : ℤ) = ∑ n ∈ Finset.Icc 1 N, (if n ≤ f.1 β then (1:ℤ) else 0) := by
    intro f
    rw [sum_boole_int]
    congr 1
    exact (card_Icc_filter_le N (f.1 β) (Ksol_coord_le δ N hN f β)).symm
  have step2 : ∀ n : ℕ,
      (∑ f : Ksol δ, (if n ≤ f.1 β then (1:ℤ) else 0))
        = (E8KostantId.KcountP (δ - n • (β : Fin 8 → ℤ)) : ℤ) := by
    intro n
    rw [sum_boole_int]
    have h1 : (Finset.univ.filter (fun f : Ksol δ => n ≤ f.1 β)).card
        = Fintype.card {f : Ksol δ // n ≤ f.1 β} :=
      (Fintype.card_subtype (fun f : Ksol δ => n ≤ f.1 β)).symm
    rw [h1, ← Fintype.card_congr (kshiftEquiv δ β n), KcountP_eq_card,
      Nat.card_eq_fintype_card]
  calc ∑ f : Ksol δ, (f.1 β : ℤ)
      = ∑ f : Ksol δ, ∑ n ∈ Finset.Icc 1 N,
          (if n ≤ f.1 β then (1:ℤ) else 0) :=
        Finset.sum_congr rfl (fun f _ => step1 f)
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ f : Ksol δ,
          (if n ≤ f.1 β then (1:ℤ) else 0) :=
        Finset.sum_comm
    _ = ∑ n ∈ Finset.Icc 1 N,
          (E8KostantId.KcountP (δ - n • (β : Fin 8 → ℤ)) : ℤ) :=
        Finset.sum_congr rfl (fun n _ => step2 n)

theorem bil_marking_PR (v δ : Fin 8 → ℤ) (N : ℕ) (hN : E8NormTwo.e8ht δ ≤ (N : ℤ)) :
    bil v δ * (E8KostantId.KcountP δ : ℤ)
      = ∑ β : PR, ∑ n ∈ Finset.Icc 1 N,
          bil v (β : Fin 8 → ℤ) * (E8KostantId.KcountP (δ - n • (β : Fin 8 → ℤ)) : ℤ) := by
  have h1 : bil v δ * (E8KostantId.KcountP δ : ℤ) = ∑ f : Ksol δ, bil v δ := by
    rw [KcountP_eq_card, Nat.card_eq_fintype_card, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  rw [h1]
  have h2 : ∀ f : Ksol δ, bil v δ = ∑ β : PR, (f.1 β : ℤ) * bil v (β : Fin 8 → ℤ) := by
    intro f
    have hcast : (∑ α : PR, f.1 α • (α : Fin 8 → ℤ))
        = ∑ α : PR, (f.1 α : ℤ) • (α : Fin 8 → ℤ) :=
      Finset.sum_congr rfl (fun α _ =>
        (Nat.cast_smul_eq_nsmul (R := ℤ) (f.1 α) (α : Fin 8 → ℤ)).symm)
    have hsum : (∑ α : PR, (f.1 α : ℤ) • (α : Fin 8 → ℤ)) = δ :=
      hcast.symm.trans f.2
    calc bil v δ = bil v (∑ α : PR, (f.1 α : ℤ) • (α : Fin 8 → ℤ)) := by rw [hsum]
      _ = ∑ β : PR, (f.1 β : ℤ) * bil v (β : Fin 8 → ℤ) := by
            rw [bil_sum_right_aux Finset.univ (fun α : PR => (f.1 α : ℤ))
              (fun α : PR => (α : Fin 8 → ℤ)) v]
  rw [Finset.sum_congr rfl (fun f _ => h2 f), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [← Finset.sum_mul, sum_coord_eq δ β N hN, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  ring


lemma e8ht_sub_nsmul (δ : Fin 8 → ℤ) (β : PR) (n : ℕ) :
    E8NormTwo.e8ht (δ - n • (β : Fin 8 → ℤ))
      = E8NormTwo.e8ht δ - (n : ℤ) * E8NormTwo.e8ht (β : Fin 8 → ℤ) := by
  have h := e8ht_add (δ - n • (β : Fin 8 → ℤ)) (n • (β : Fin 8 → ℤ))
  rw [sub_add_cancel, e8ht_nsmul] at h
  linarith

theorem secondOrder_Ksol (δ : Fin 8 → ℤ) :
    bil δ δ * (E8KostantId.KcountP δ : ℤ)
      = (∑ β : PR, ∑ β' : PR, ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
          ∑ m ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
          bil (β : Fin 8 → ℤ) (β' : Fin 8 → ℤ) *
            (E8KostantId.KcountP (δ - n • (β : Fin 8 → ℤ) - m • (β' : Fin 8 → ℤ)) : ℤ))
        + 2 * (∑ β : PR, ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
            (n : ℤ) * (E8KostantId.KcountP (δ - n • (β : Fin 8 → ℤ)) : ℤ)) := by
  set N := (E8NormTwo.e8ht δ).toNat with hNdef
  have hN : E8NormTwo.e8ht δ ≤ (N : ℤ) := Int.self_le_toNat _
  rw [bil_marking_PR δ δ N hN]
  have hA : ∀ β : PR, ∀ n : ℕ,
      bil δ (β : Fin 8 → ℤ) * (E8KostantId.KcountP (δ - n • (β:Fin 8→ℤ)) : ℤ)
        = bil (β : Fin 8 → ℤ) (δ - n • (β:Fin 8→ℤ))
            * (E8KostantId.KcountP (δ - n • (β:Fin 8→ℤ)) : ℤ)
          + 2 * ((n : ℤ) * (E8KostantId.KcountP (δ - n • (β:Fin 8→ℤ)) : ℤ)) := by
    intro β n
    have hβ2 : bil (β : Fin 8 → ℤ) (β : Fin 8 → ℤ) = 2 := by
      rw [← qZ_eq_bil]; exact posRoot_qZ β
    have hbb : bil δ (β : Fin 8 → ℤ)
        = bil (β : Fin 8 → ℤ) (δ - n • (β:Fin 8→ℤ)) + 2 * (n : ℤ) := by
      rw [bil_comm' δ (β : Fin 8 → ℤ)]
      have hsplit : δ = (δ - n • (β:Fin 8→ℤ)) + n • (β:Fin 8→ℤ) := by abel
      rw [hsplit, bil_add_right_aux]
      rw [← Nat.cast_smul_eq_nsmul (R := ℤ), bil_smul_right, hβ2]
      ring_nf
    rw [hbb]; ring_nf
  rw [Finset.sum_congr rfl (fun β _ => Finset.sum_congr rfl (fun n _ => hA β n))]
  simp only [Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl (fun β _ => ?_)
    have hbound : E8NormTwo.e8ht (δ - (0:ℕ) • (β:Fin 8→ℤ)) ≤ (N : ℤ) := by
      simp only [zero_smul, sub_zero]; exact hN
    have hlt : ∀ n : ℕ, E8NormTwo.e8ht (δ - n • (β : Fin 8 → ℤ)) ≤ (N : ℤ) := by
      intro n
      rw [e8ht_sub_nsmul]
      have h2 : 0 ≤ (n : ℤ) * E8NormTwo.e8ht (β : Fin 8 → ℤ) :=
        mul_nonneg (by positivity) (e8ht_posRoot_nonneg β)
      linarith
    have hmark : ∀ n : ℕ,
        bil (β : Fin 8 → ℤ) (δ - n • (β : Fin 8 → ℤ))
            * (E8KostantId.KcountP (δ - n • (β : Fin 8 → ℤ)) : ℤ)
          = ∑ β' : PR, ∑ m ∈ Finset.Icc 1 N,
              bil (β : Fin 8 → ℤ) (β' : Fin 8 → ℤ)
                * (E8KostantId.KcountP
                    (δ - n • (β : Fin 8 → ℤ) - m • (β' : Fin 8 → ℤ)) : ℤ) :=
      fun n => bil_marking_PR (β : Fin 8 → ℤ) (δ - n • (β : Fin 8 → ℤ)) N (hlt n)
    rw [Finset.sum_congr rfl (fun n _ => hmark n), Finset.sum_comm]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [Finset.mul_sum]

/-! ## Conversion to the `E8posRoots.P`-indexed form -/

lemma sum_P_eq_sum_PR (F : (Fin 8 → ℤ) → ℤ) :
    (∑ β ∈ E8posRoots.P, F β) = ∑ β : PR, F (β : Fin 8 → ℤ) := by
  rw [← Finset.sum_attach, Finset.attach_eq_univ]

lemma bil_eq_sum_ip (x y : Fin 8 → ℤ) :
    bil x y = ∑ i, x i * (E8NormTwo.E8inv.mulVec y) i := rfl

/-- **The second-order ("Casimir") identity for the `E₈` Kostant partition function.**

With `⟪x,y⟫ = Σ i, x i * (A⁻¹ y) i` and `K δ = E8KostantId.KcountP δ` the number of multisets of
positive roots summing to `δ`,

  `⟪δ,δ⟫ * K δ = Σ_{β,β' ∈ P} Σ_{n,m ≥ 1} ⟪β,β'⟫ * K (δ - nβ - mβ') + 2 Σ_{β ∈ P} Σ_{n ≥ 1} n * K (δ - nβ)`.

Combinatorial proof: expand `⟪δ,δ⟫ = Σ_{β,β' ∈ m} ⟪β,β'⟫` over the multiset `m` and identify the
triples `(β,β',n,m,m'')` with pairs `(m, β≠β', n ≤ mult_β m, m ≤ mult_{β'} m)` plus the diagonal
`β = β'` contributions; the diagonal part is compensated by `Σ_β j_β(j_β+1) = 2Σ_{n≥1} n K(δ-nβ)`. -/
theorem E8_Kostant_secondOrder (δ : Fin 8 → ℤ) :
    (∑ i, δ i * (E8NormTwo.E8inv.mulVec δ) i) *
        (Commons.Algebra.Lie.E8KostantId.KcountP δ : ℤ)
      = (∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P,
          ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
          ∑ m ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
          (∑ i, β i * (E8NormTwo.E8inv.mulVec β') i) *
            (Commons.Algebra.Lie.E8KostantId.KcountP (δ - n • β - m • β') : ℤ))
        + 2 * (∑ β ∈ E8posRoots.P,
            ∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht δ).toNat),
            (n : ℤ) * (Commons.Algebra.Lie.E8KostantId.KcountP (δ - n • β) : ℤ)) := by
  have h := secondOrder_Ksol δ
  rw [← bil_eq_sum_ip δ δ]
  rw [h]
  simp only [sum_P_eq_sum_PR, bil_eq_sum_ip]

end Commons.Algebra.Lie
