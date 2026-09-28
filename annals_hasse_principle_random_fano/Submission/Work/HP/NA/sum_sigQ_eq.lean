import Mathlib
import Submission.Work.HP.NA.Setup
import Submission.Work.HP.NA.SumDefs
import Submission.Work.HP.NA.card_primMod
import Submission.Work.HP.NA.not_isUnit_eq_p_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The first moment of `σ(·; p^r)`: `∑_{a primitive} σ(a; p^r)`

We prove `Work.HP.NA.sum_sigQ_eq`:

`∑_{a ∈ 𝔉_{N}(p^r)} σ(a; p^r) = p^{rN} (1 - p^{-(n+1)}) (1 - p^{-(N-1)})`,  `N = N_{d,n}`.

The proof follows the paper (Lemma "first moment sigma"):
* rewrite `σ` as a normalised count of primitive zeros `b` of `f_a` (`sigQ_eq'`);
* exchange the order of summation (Fubini, `fubini_sigQ`), so that for each primitive `b`
  one counts the primitive coefficient vectors `a` with `⟨a, ν_{d,n}(b)⟩ = 0`;
* that count is `(p^r)^{N-1} - p^{(r-1)(N-1)}` (`primKerCount`, because `ν_{d,n}(b)` is
  primitive when `b` is, `veronese_isPrimGen`);
* `#𝔉_N(p^r) = (p^r)^N - p^{(r-1)N}` (`card_primMod_gen` / `card_primMod`);
* a final algebraic identity (`arith_sigQ`).
-/

noncomputable section
open Finset
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.HP.NA

/-! ## Elementary tools -/

/-- `Set.ncard` of a decidable predicate set on a finite type is the filtered cardinality. -/
theorem sigQ1st_ncard_setOf {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Set.ncard {x | p x} = (Finset.univ.filter p).card := by
  classical
  rw [Set.ncard_eq_toFinset_card]
  congr 1
  ext x
  simp

/-- `σ(a;Q)` as a normalised count of the primitive zeros `b` of `f_a`. -/
theorem sigQ_eq' (d n Q : ℕ) [NeZero Q] (a : Mon d n → ZMod Q) :
    sigQ d n Q a = ((Bprim n Q).filter (fun b => fev d n a b = 0)).card / (Q : ℝ) ^ n := by
  classical
  have h1 : Set.ncard {b : Fin (n + 1) → ZMod Q | IsPrimGen Q b ∧ fev d n a b = 0}
      = ((Bprim n Q).filter (fun b => fev d n a b = 0)).card := by
    rw [sigQ1st_ncard_setOf (p := fun b => IsPrimGen Q b ∧ fev d n a b = 0)]
    congr 1
    rw [Bprim, Finset.filter_filter]
  unfold sigQ
  exact congrArg (fun k : ℕ => (k : ℝ) / (Q : ℝ) ^ n) h1

/-- A vector with a unit coordinate generates the unit ideal. -/
theorem isPrimGen_of_isUnit {ι : Type*} [Fintype ι] {Q : ℕ} {x : ι → ZMod Q} {i : ι}
    (h : IsUnit (x i)) : IsPrimGen Q x := by
  rw [IsPrimGen]
  refine top_le_iff.mp ?_
  calc ⊤ = Ideal.span ({x i} : Set (ZMod Q)) := (Ideal.span_singleton_eq_top.mpr h).symm
    _ ≤ Ideal.span (Set.range x) := by
        rw [Ideal.span_le]
        rintro y (rfl : y = x i)
        exact Ideal.subset_span (Set.mem_range_self i)

/-- Over `ZMod (p^r)`, primitivity is the existence of a unit coordinate (general index type). -/
theorem isPrimGen_iff_exists_isUnit {ι : Type*} [Fintype ι] {p r : ℕ} (hp : p.Prime)
    (hr : 1 ≤ r) (c : ι → ZMod (p ^ r)) : IsPrimGen (p ^ r) c ↔ ∃ i, IsUnit (c i) := by
  let e := Fintype.equivFin ι
  have hrange : Set.range (fun j : Fin (Fintype.card ι) => c (e.symm j)) = Set.range c := by
    apply Set.Subset.antisymm
    · rintro _ ⟨j, rfl⟩; exact Set.mem_range_self _
    · rintro _ ⟨i, rfl⟩; exact ⟨e i, by simp⟩
  have hiff : IsPrimGen (p ^ r) c ↔ IsPrimMod (p ^ r) (fun j => c (e.symm j)) := by
    simp only [IsPrimGen, IsPrimMod, hrange]
  rw [hiff, isPrimMod_iff_exists_isUnit p r (Fintype.card ι) hp hr]
  constructor
  · rintro ⟨j, hj⟩; exact ⟨e.symm j, hj⟩
  · rintro ⟨i, hi⟩; exact ⟨e i, by simpa using hi⟩

/-- The exponent vector of the monomial `Xᵢ^d`. -/
def monDi' (d n : ℕ) (i : Fin (n + 1)) : Mon d n :=
  ⟨fun k => ⟨if k = i then d else 0, by split <;> omega⟩,
   by rw [Finset.sum_ite_eq' Finset.univ i (fun _ => d)]; simp⟩

/-- `veronese` at the single-variable monomial `Xᵢ^d`. -/
theorem sigQ1st_veronese_monDi {R : Type*} [CommSemiring R] (d n : ℕ) (x : Fin (n + 1) → R)
    (i : Fin (n + 1)) : veronese d n x (monDi' d n i) = x i ^ d := by
  simp only [veronese, monDi']
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The Veronese image of a primitive vector is primitive. -/
theorem veronese_isPrimGen {d n p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    {b : Fin (n + 1) → ZMod (p ^ r)} (hb : IsPrimGen (p ^ r) b) :
    IsPrimGen (p ^ r) (veronese d n b) := by
  obtain ⟨i0, hi0⟩ := (isPrimGen_iff_exists_isUnit hp hr b).mp hb
  refine isPrimGen_of_isUnit (i := monDi' d n i0) ?_
  rw [sigQ1st_veronese_monDi]
  exact hi0.pow d

/-- `#𝔉_α(Q) = Q^{#α} - p^{(r-1)#α}` for `Q = p^r`, general finite index type. -/
theorem card_primMod_gen {α : Type*} [Fintype α] {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    Nat.card {c : α → ZMod (p ^ r) // IsPrimGen (p ^ r) c}
      = (p ^ r) ^ Fintype.card α - p ^ ((r - 1) * Fintype.card α) := by
  let e := Fintype.equivFin α
  let Φ : (α → ZMod (p^r)) ≃ (Fin (Fintype.card α) → ZMod (p^r)) := e.arrowCongr (Equiv.refl _)
  have hiff : ∀ c, IsPrimGen (p^r) c ↔ IsPrimMod (p^r) (Φ c) := by
    intro c
    have hrange : Set.range (Φ c) = Set.range c := by
      show Set.range (fun j => c (e.symm j)) = Set.range c
      apply Set.Subset.antisymm
      · rintro _ ⟨j, rfl⟩; exact Set.mem_range_self _
      · rintro _ ⟨i, rfl⟩; exact ⟨e i, by simp⟩
    simp only [IsPrimGen, IsPrimMod, hrange]
  rw [Nat.card_congr (Equiv.subtypeEquiv Φ hiff), card_primMod p r (Fintype.card α) hp hr]

/-- Splitting a sum at a chosen index, in terms of the subtype of the remaining indices. -/
theorem sum_split {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [AddCommMonoid R] (i0 : ι)
    (f : ι → R) : (∑ i, f i) = f i0 + ∑ j : {i : ι // i ≠ i0}, f j.1 := by
  classical
  have h1 : (∑ i : ι, f i)
      = ∑ i : ι, ((if i = i0 then f i else 0) + (if i ≠ i0 then f i else 0)) :=
    Finset.sum_congr rfl (fun i _ => by by_cases h : i = i0 <;> simp [h])
  rw [h1, Finset.sum_add_distrib]
  have ha : (∑ i : ι, (if i = i0 then f i else 0)) = f i0 := by
    rw [Finset.sum_ite_eq']; simp
  have hb : (∑ i : ι, (if i ≠ i0 then f i else 0))
      = ∑ j : {i : ι // i ≠ i0}, f j.1 := by
    rw [← Finset.sum_filter,
        Finset.sum_subtype (p := fun i => i ≠ i0)
          (Finset.univ.filter (fun i => i ≠ i0)) (fun x => by simp) f]
  rw [ha, hb]

/-! ## The linear kernel count -/

/-- The number of primitive `a` in the hyperplane `⟨a, v⟩ = 0`, for `v` primitive. -/
theorem primKerCount {ι : Type*} [Fintype ι] {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (v : ι → ZMod (p ^ r)) (hv : IsPrimGen (p ^ r) v) :
    Nat.card {a : ι → ZMod (p ^ r) // IsPrimGen (p ^ r) a ∧ (∑ i, a i * v i) = 0}
      = (p ^ r) ^ (Fintype.card ι - 1) - p ^ ((r - 1) * (Fintype.card ι - 1)) := by
  classical
  obtain ⟨i0, hi0⟩ := (isPrimGen_iff_exists_isUnit hp hr v).mp hv
  set w : ZMod (p ^ r) := ↑((hi0.unit)⁻¹) with hwdef
  have hwv : w * v i0 = 1 := hi0.val_inv_mul
  have hvw : v i0 * w = 1 := by rw [mul_comm]; exact hi0.val_inv_mul
  let J := {i : ι // i ≠ i0}
  let S : (J → ZMod (p ^ r)) → ZMod (p ^ r) := fun c => ∑ j : J, c j * v j.1
  let mk : (J → ZMod (p ^ r)) → (ι → ZMod (p ^ r)) := fun c i =>
    if h : i = i0 then -(w * S c) else c ⟨i, h⟩
  let pick : (ι → ZMod (p ^ r)) → (J → ZMod (p ^ r)) := fun a j => a j.1
  have hmk_apply : ∀ (c : J → ZMod (p^r)) (i : ι),
      mk c i = if h : i = i0 then -(w * S c) else c ⟨i, h⟩ := fun c i => rfl
  have hS_apply : ∀ (c : J → ZMod (p^r)), S c = ∑ j : J, c j * v j.1 := fun c => rfl
  have hpick_val : ∀ (a : ι → ZMod (p^r)) (j : J), pick a j = a j.1 := fun a j => rfl
  have hker : ∀ c : J → ZMod (p ^ r), (∑ i, mk c i * v i) = 0 := by
    intro c
    rw [sum_split i0 (fun i => mk c i * v i)]
    rw [hmk_apply c i0, dif_pos rfl]
    have h2 : ∀ j : J, mk c j.1 * v j.1 = c j * v j.1 := by
      intro j; rw [hmk_apply c j.1, dif_neg j.2]
    rw [Finset.sum_congr rfl (fun j _ => h2 j), hS_apply c]
    have hthis : (-(w * S c)) * v i0 = -(S c) := by
      rw [neg_mul]
      congr 1
      rw [mul_comm w (S c), mul_assoc, hwv, mul_one]
    rw [hthis]; ring
  have hpick_mk : ∀ c : J → ZMod (p ^ r), pick (mk c) = c := by
    intro c
    funext j
    change mk c j.1 = c j
    rw [hmk_apply c j.1, dif_neg j.2]
  have hmk_pick : ∀ a : ι → ZMod (p ^ r), (∑ i, a i * v i) = 0 → mk (pick a) = a := by
    intro a ha
    funext i
    by_cases h : i = i0
    · rw [h]
      rw [hmk_apply (pick a) i0, dif_pos rfl, hS_apply (pick a)]
      have hs := sum_split i0 (fun i => a i * v i)
      rw [ha] at hs
      have hneg : (∑ j : J, (pick a) j * v j.1) = -(a i0 * v i0) := by
        rw [Finset.sum_congr rfl (fun j _ => by rw [hpick_val a j])]
        exact eq_neg_of_add_eq_zero_right hs.symm
      rw [hneg]
      rw [mul_neg, neg_neg, ← mul_assoc, mul_comm w (a i0), mul_assoc, hwv, mul_one]
    · change mk (pick a) i = a i
      rw [hmk_apply (pick a) i, dif_neg h]
  have hprim : ∀ (a : ι → ZMod (p ^ r)), (∑ i, a i * v i) = 0 →
      (IsPrimGen (p ^ r) a ↔ IsPrimGen (p ^ r) (pick a)) := by
    intro a ha
    rw [isPrimGen_iff_exists_isUnit hp hr a, isPrimGen_iff_exists_isUnit hp hr (pick a)]
    constructor
    · rintro ⟨i, hi⟩
      by_cases h : i = i0
      · rw [h] at hi
        by_contra hcon
        rw [not_exists] at hcon
        choose y hy using fun j : J => (not_isUnit_eq_p_mul hp hr (pick a j)).mp (hcon j)
        have hY : (∑ j : J, a j.1 * v j.1)
            = (p : ZMod (p ^ r)) * (∑ j : J, y j * v j.1) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have hj : a j.1 = (p : ZMod (p ^ r)) * y j := hy j
          rw [hj]; ring
        have hs := sum_split i0 (fun i => a i * v i)
        rw [ha] at hs
        have hneg : (∑ j : J, a j.1 * v j.1) = -(a i0 * v i0) :=
          eq_neg_of_add_eq_zero_right hs.symm
        rw [hY] at hneg
        have h2 : a i0 * v i0 = -((p : ZMod (p ^ r)) * (∑ j : J, y j * v j.1)) := by
          rw [hneg, neg_neg]
        have hW : a i0 = (p : ZMod (p ^ r)) * (-((∑ j : J, y j * v j.1) * w)) := by
          calc a i0 = a i0 * 1 := (mul_one _).symm
            _ = a i0 * (v i0 * w) := by rw [hvw]
            _ = (a i0 * v i0) * w := by ring
            _ = (-((p : ZMod (p ^ r)) * (∑ j : J, y j * v j.1))) * w := by rw [h2]
            _ = (p : ZMod (p ^ r)) * (-((∑ j : J, y j * v j.1) * w)) := by ring
        exact (not_isUnit_eq_p_mul hp hr (a i0)).mpr ⟨_, hW⟩ hi
      · exact ⟨⟨i, h⟩, by change IsUnit (pick a ⟨i, h⟩); rw [hpick_val]; exact hi⟩
    · rintro ⟨j, hj⟩
      exact ⟨j.1, by change IsUnit (a j.1); rw [← hpick_val a j]; exact hj⟩
  have hcardJ : Fintype.card J = Fintype.card ι - 1 := by
    have h1 : Fintype.card J = Fintype.card ι - Fintype.card {i : ι // i = i0} :=
      Fintype.card_subtype_compl (fun i : ι => i = i0)
    have h2 : Fintype.card {i : ι // i = i0} = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨⟨i0, rfl⟩, fun y => Subtype.ext y.2⟩
    rw [h1, h2]
  rw [show Nat.card {a : ι → ZMod (p ^ r) // IsPrimGen (p ^ r) a ∧ (∑ i, a i * v i) = 0}
        = Nat.card {c : J → ZMod (p ^ r) // IsPrimGen (p ^ r) c} from
      Nat.card_congr
        { toFun := fun a => ⟨pick a.1, (hprim a.1 a.2.2).mp a.2.1⟩
          invFun := fun c => ⟨mk c.1,
            (hprim (mk c.1) (hker c.1)).mpr (by rw [hpick_mk c.1]; exact c.2), hker c.1⟩
          left_inv := fun a => Subtype.ext (hmk_pick a.1 a.2.2)
          right_inv := fun c => Subtype.ext (hpick_mk c.1) },
      card_primMod_gen (α := J) hp hr, hcardJ]

/-! ## Fubini -/

/-- Exchange of the two summations: `∑_a #{b : primitive zero of f_a} = ∑_b #{a : primitive,
⟨a, ν(b)⟩ = 0}`. -/
theorem fubini_sigQ (d n q : ℕ) [NeZero q] :
    (∑ a ∈ primFinset d n q, (Nat.card {b : Fin (n + 1) → ZMod q //
        IsPrimGen q b ∧ fev d n a b = 0} : ℝ))
      = ∑ b ∈ Bprim n q, (Nat.card {a : Mon d n → ZMod q //
          IsPrimGen q a ∧ fev d n a b = 0} : ℝ) := by
  classical
  have hL : ∀ a : Mon d n → ZMod q,
      (Nat.card {b : Fin (n+1) → ZMod q // IsPrimGen q b ∧ fev d n a b = 0} : ℝ)
        = ∑ b ∈ Bprim n q, (if fev d n a b = 0 then (1:ℝ) else 0) := by
    intro a
    have hcard : Nat.card {b : Fin (n+1) → ZMod q // IsPrimGen q b ∧ fev d n a b = 0}
        = ((Bprim n q).filter (fun b => fev d n a b = 0)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext b
      simp [Bprim, Finset.mem_filter]
    rw [hcard]
    exact (Finset.sum_boole (R := ℝ) (fun b => fev d n a b = 0) (Bprim n q)).symm
  have hR : ∀ b : Fin (n+1) → ZMod q,
      (Nat.card {a : Mon d n → ZMod q // IsPrimGen q a ∧ fev d n a b = 0} : ℝ)
        = ∑ a ∈ primFinset d n q, (if fev d n a b = 0 then (1:ℝ) else 0) := by
    intro b
    have hcard : Nat.card {a : Mon d n → ZMod q // IsPrimGen q a ∧ fev d n a b = 0}
        = ((primFinset d n q).filter (fun a => fev d n a b = 0)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext a
      simp [primFinset, Finset.mem_filter]
    rw [hcard]
    exact (Finset.sum_boole (R := ℝ) (fun a => fev d n a b = 0) (primFinset d n q)).symm
  calc (∑ a ∈ primFinset d n q,
          (Nat.card {b : Fin (n+1) → ZMod q // IsPrimGen q b ∧ fev d n a b = 0} : ℝ))
      = ∑ a ∈ primFinset d n q,
          ∑ b ∈ Bprim n q, (if fev d n a b = 0 then (1:ℝ) else 0) :=
        Finset.sum_congr rfl (fun a _ => hL a)
    _ = ∑ b ∈ Bprim n q,
          ∑ a ∈ primFinset d n q, (if fev d n a b = 0 then (1:ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ b ∈ Bprim n q,
          (Nat.card {a : Mon d n → ZMod q // IsPrimGen q a ∧ fev d n a b = 0} : ℝ) :=
        Finset.sum_congr rfl (fun b _ => (hR b).symm)

/-! ## The final algebraic identity -/

/-- `↑((p^r)^k - p^{(r-1)k}) = p^{rk} - p^{(r-1)k}` in `ℝ`. -/
theorem cast_pow_sub {p r k : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    ((((p ^ r) ^ k - p ^ ((r - 1) * k) : ℕ) : ℝ))
      = (p : ℝ) ^ (r * k) - (p : ℝ) ^ ((r - 1) * k) := by
  have hle : p ^ ((r - 1) * k) ≤ (p ^ r) ^ k := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hp.pos (Nat.mul_le_mul_right _ (Nat.sub_le r 1))
  have h1 : (((p ^ r) ^ k : ℕ) : ℝ) = (p : ℝ) ^ (r * k) := by
    rw [Nat.cast_pow, Nat.cast_pow, ← pow_mul]
  have h2 : ((p ^ ((r - 1) * k) : ℕ) : ℝ) = (p : ℝ) ^ ((r - 1) * k) := by
    rw [Nat.cast_pow]
  rw [Nat.cast_sub hle, h1, h2]

/-- The algebraic identity underlying the first moment. -/
theorem arith_sigQ {p r n N : ℕ} (hp : p.Prime) (hr : 1 ≤ r) (hN : 1 ≤ N) :
    (1 / ((p : ℝ) ^ r) ^ n)
      * ((((p ^ r) ^ (n + 1) - p ^ ((r - 1) * (n + 1)) : ℕ) : ℝ))
      * ((((p ^ r) ^ (N - 1) - p ^ ((r - 1) * (N - 1)) : ℕ) : ℝ))
    = (p : ℝ) ^ (r * N) * (1 - 1 / (p : ℝ) ^ (n + 1)) * (1 - 1 / (p : ℝ) ^ (N - 1)) := by
  have hx : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [cast_pow_sub hp hr (k := n+1), cast_pow_sub hp hr (k := N-1), ← pow_mul]
  have hA : (p:ℝ)^(r*(n+1)) - (p:ℝ)^((r-1)*(n+1))
      = (p:ℝ)^(r*(n+1)) * (1 - 1/(p:ℝ)^(n+1)) := by
    have h1 : r*(n+1) = (r-1)*(n+1) + (n+1) := by
      nth_rewrite 1 [← Nat.sub_add_cancel hr]
      rw [add_mul, one_mul]
    have hfac : (p:ℝ)^(r*(n+1)) = (p:ℝ)^((r-1)*(n+1)) * (p:ℝ)^(n+1) := by
      rw [h1, pow_add]
    have hP : (p:ℝ)^(n+1) ≠ 0 := pow_ne_zero _ hx
    rw [hfac, mul_sub, mul_one, mul_one_div, mul_div_cancel_right₀ _ hP]
  have hB : (p:ℝ)^(r*(N-1)) - (p:ℝ)^((r-1)*(N-1))
      = (p:ℝ)^(r*(N-1)) * (1 - 1/(p:ℝ)^(N-1)) := by
    have h1 : r*(N-1) = (r-1)*(N-1) + (N-1) := by
      nth_rewrite 1 [← Nat.sub_add_cancel hr]
      rw [add_mul, one_mul]
    have hfac : (p:ℝ)^(r*(N-1)) = (p:ℝ)^((r-1)*(N-1)) * (p:ℝ)^(N-1) := by
      rw [h1, pow_add]
    have hP : (p:ℝ)^(N-1) ≠ 0 := pow_ne_zero _ hx
    rw [hfac, mul_sub, mul_one, mul_one_div, mul_div_cancel_right₀ _ hP]
  have hexp : r*(n+1) + r*(N-1) = r*N + r*n := by
    have h1 : r*(n+1) + r*(N-1) = r*((n+1)+(N-1)) := (mul_add r (n+1) (N-1)).symm
    have h2 : (n+1) + (N-1) = n + N := by omega
    rw [h1, h2]; ring
  have hkey : (1/(p:ℝ)^(r*n)) * (p:ℝ)^(r*(n+1)) * (p:ℝ)^(r*(N-1)) = (p:ℝ)^(r*N) := by
    rw [one_div, mul_assoc, ← pow_add, hexp, pow_add,
        mul_comm ((p:ℝ)^(r*N)) ((p:ℝ)^(r*n)), ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero (r*n) hx), one_mul]
  rw [hA, hB, ← hkey]
  ring

/-! ## The theorem -/

theorem sum_sigQ_eq (d n p r : ℕ) [NeZero (p ^ r)] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (hp : p.Prime) (hr : 1 ≤ r) :
    (∑ a ∈ Work.HP.NA.primFinset d n (p ^ r), Work.HP.NA.sigQ d n (p ^ r) a)
      = (p : ℝ) ^ (r * Work.HP.NN d n) * (1 - 1 / (p : ℝ) ^ (n + 1))
          * (1 - 1 / (p : ℝ) ^ (Work.HP.NN d n - 1)) := by
  classical
  have hN1 : 1 ≤ Work.HP.NN d n := by
    have hpos : 0 < Work.HP.NN d n :=
      Fintype.card_pos_iff.mpr ⟨monDi' d n 0⟩
    omega
  -- step 1
  have step1 : (∑ a ∈ primFinset d n (p ^ r), sigQ d n (p ^ r) a)
      = (1 / (((p ^ r : ℕ)) : ℝ) ^ n)
        * (∑ a ∈ primFinset d n (p ^ r),
            (((Bprim n (p ^ r)).filter (fun b => fev d n a b = 0)).card : ℝ)) := by
    rw [Finset.sum_congr rfl (fun a _ => sigQ_eq' d n (p ^ r) a), ← Finset.sum_div]
    rw [one_div, div_eq_mul_inv, mul_comm]
  -- the card ↔ Nat.card bridge
  have hcard_eq_nat : ∀ a : Mon d n → ZMod (p ^ r),
      ((Bprim n (p ^ r)).filter (fun b => fev d n a b = 0)).card
        = Nat.card {b : Fin (n + 1) → ZMod (p ^ r) //
            IsPrimGen (p ^ r) b ∧ fev d n a b = 0} := by
    intro a
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact congrArg Finset.card
      (Finset.ext (fun b => by simp [Bprim, Finset.mem_filter]))
  have hcard_eq : ∀ a : Mon d n → ZMod (p ^ r),
      (((Bprim n (p ^ r)).filter (fun b => fev d n a b = 0)).card : ℝ)
        = (Nat.card {b : Fin (n + 1) → ZMod (p ^ r) //
            IsPrimGen (p ^ r) b ∧ fev d n a b = 0} : ℝ) :=
    fun a => by rw [hcard_eq_nat a]
  -- step 2 (Fubini)
  have step2 : (∑ a ∈ primFinset d n (p ^ r),
        (((Bprim n (p ^ r)).filter (fun b => fev d n a b = 0)).card : ℝ))
      = ∑ b ∈ Bprim n (p ^ r), (Nat.card {a : Mon d n → ZMod (p ^ r) //
          IsPrimGen (p ^ r) a ∧ fev d n a b = 0} : ℝ) := by
    rw [Finset.sum_congr rfl (fun a _ => hcard_eq a)]
    exact fubini_sigQ d n (p ^ r)
  -- step 3 (linear kernel count)
  have hkernel : ∀ b ∈ Bprim n (p ^ r),
      (Nat.card {a : Mon d n → ZMod (p ^ r) // IsPrimGen (p ^ r) a ∧ fev d n a b = 0} : ℝ)
        = ((((p ^ r) ^ (Work.HP.NN d n - 1) - p ^ ((r - 1) * (Work.HP.NN d n - 1)) : ℕ)) : ℝ) := by
    intro b hb
    have hb' : IsPrimGen (p ^ r) b := mem_Bprim.mp hb
    have hv : IsPrimGen (p ^ r) (veronese d n b) := veronese_isPrimGen hp hr hb'
    have h2 : Nat.card {a : Mon d n → ZMod (p ^ r) // IsPrimGen (p ^ r) a ∧ fev d n a b = 0}
        = Nat.card {a : Mon d n → ZMod (p ^ r) //
            IsPrimGen (p ^ r) a ∧ (∑ i, a i * veronese d n b i) = 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun a => by simp only [fev]))
    rw [h2, primKerCount hp hr (veronese d n b) hv]
  have step3 : (∑ b ∈ Bprim n (p ^ r), (Nat.card {a : Mon d n → ZMod (p ^ r) //
          IsPrimGen (p ^ r) a ∧ fev d n a b = 0} : ℝ))
      = ((Bprim n (p ^ r)).card : ℝ)
        * ((((p ^ r) ^ (Work.HP.NN d n - 1) - p ^ ((r - 1) * (Work.HP.NN d n - 1)) : ℕ)) : ℝ) := by
    rw [Finset.sum_congr rfl (fun b hb => hkernel b hb), Finset.sum_const, nsmul_eq_mul]
  -- step 4 (cardinality of 𝔉)
  have hBprim : (Bprim n (p ^ r)).card
      = (p ^ r) ^ (n + 1) - p ^ ((r - 1) * (n + 1)) := by
    have hc : (Bprim n (p ^ r)).card
        = Nat.card {c : Fin (n + 1) → ZMod (p ^ r) // IsPrimMod (p ^ r) c} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rfl
    rw [hc, card_primMod p r (n + 1) hp hr]
  have step4 : ((Bprim n (p ^ r)).card : ℝ)
      = ((((p ^ r) ^ (n + 1) - p ^ ((r - 1) * (n + 1)) : ℕ)) : ℝ) := by
    rw [hBprim]
  rw [step1, step2, step3, step4]
  rw [← mul_assoc, Nat.cast_pow]
  exact arith_sigQ (n := n) (N := Work.HP.NN d n) hp hr hN1

end Work.HP.NA
