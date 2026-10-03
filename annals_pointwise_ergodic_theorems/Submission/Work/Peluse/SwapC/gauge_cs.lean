import Mathlib
import Submission.Work.Peluse.SwapC.hyp_gauge

namespace Work.Peluse.SwapC

set_option autoImplicit false

open scoped BigOperators

noncomputable section

open Work.Peluse

/-! ## Support bookkeeping for the gauge

The Cauchy–Schwarz step of `concatStep` needs the gauge to *vanish off a finite set*: the
`pbox`-hypothesis has its base variable running over `symIcc N`, while (by the node's
translate-support hypothesis) `f` lives on the translate `x₀ + symIcc N`, so
`cauchySchwarz_base` has to be fed a finite set `T` containing both that translate and the
support of the gauge.

`gauge` is a finite average of the `Rest`-products `Rest (incr …) f`; each such product is a
product of shifted copies of `f` over the sign patterns `ω ≠ 0`, so it dies as soon as any one
factor does.  Picking the all-`true` pattern (available because the increment tuple has length
`s + 1 ≥ 1`) isolates the shift `∑_k v k`, and the translate-support of `f` gives the vanishing.

All the bookkeeping lemmas below are `private`: they are the elementary glue of this step and the
chapter's own files carry their own copies.
-/

/-- Iterated conjugation kills `0`. -/
private lemma starIterate_zero' (k : ℕ) : (star^[k]) (0 : ℂ) = 0 :=
  Function.iterate_fixed (by simp) k

/-- A `Rest`-product vanishes if one of its factors does: the factor indexed by the sign pattern
`ω₀` is `(star^[weight ω₀]) (f (y + cornerShift v 0 ω₀))`. -/
private lemma Rest_eq_zero_of_factor {d : ℕ} (v : Fin d → ℤ) (f : ℤ → ℂ) (ω₀ : Fin d → Bool)
    (hω₀ : ω₀ ∈ Finset.univ.erase (0 : Fin d → Bool)) (y : ℤ)
    (h : f (y + Work.Peluse.cornerShift v (fun _ => 0) ω₀) = 0) : Rest v f y = 0 := by
  rw [Rest]
  refine Finset.prod_eq_zero hω₀ ?_
  rw [h, starIterate_zero']

/-- **Translate-support of the `Rest`-product.**  If `f` is, up to the translation `c₀`, supported
in `symIcc L`, then so is `Rest v f`, for the translation `c₀ - cornerShift v 0 (fun _ => true)`
(the sign pattern `ω₀ ≡ true` supplies the vanishing factor, and `ω₀ ≠ 0` as soon as `d ≥ 1`). -/
private lemma Rest_translate_support {d : ℕ} (hd : 1 ≤ d) (v : Fin d → ℤ) {f : ℤ → ℂ} {L : ℕ}
    {c₀ : ℤ} (hf : ∀ x : ℤ, x ∉ symIcc L → f (x + c₀) = 0) :
    ∃ c : ℤ, ∀ x : ℤ, x ∉ symIcc L → Rest v f (x + c) = 0 := by
  refine ⟨c₀ - Work.Peluse.cornerShift v (fun _ => 0) (fun _ => true), fun x hx => ?_⟩
  refine Rest_eq_zero_of_factor v f (fun _ => true) ?_
    (x + (c₀ - Work.Peluse.cornerShift v (fun _ => 0) (fun _ => true))) ?_
  · rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro hcon
    have h0 := congrFun hcon ⟨0, hd⟩
    simp at h0
  · have harg : x + (c₀ - Work.Peluse.cornerShift v (fun _ => 0) (fun _ => true))
        + Work.Peluse.cornerShift v (fun _ => 0) (fun _ => true) = x + c₀ := by ring
    rw [harg]
    exact hf x hx

/-- Translate-support gives finite support. -/
private lemma finSuppZ_of_translate_support {g : ℤ → ℂ} {L : ℕ} {c : ℤ}
    (h : ∀ x : ℤ, x ∉ symIcc L → g (x + c) = 0) : FinSuppZ g := by
  refine ⟨L + c.natAbs, fun x hx => ?_⟩
  have hmem : x - c ∉ symIcc L := by
    intro hc
    have h1 : (x - c).natAbs ≤ L := (mem_symIcc_iff).mp hc
    have h2 : x.natAbs ≤ (x - c).natAbs + c.natAbs := by
      have h3 := Int.natAbs_add_le (x - c) c
      rwa [sub_add_cancel] at h3
    omega
  have h4 := h (x - c) hmem
  rwa [sub_add_cancel] at h4

/-- Finite support of a `Rest`-product. -/
private lemma Rest_finSuppZ {d : ℕ} (hd : 1 ≤ d) (v : Fin d → ℤ) {f : ℤ → ℂ} {L : ℕ} {c₀ : ℤ}
    (hf : ∀ x : ℤ, x ∉ symIcc L → f (x + c₀) = 0) : FinSuppZ (Rest v f) := by
  obtain ⟨c, hc⟩ := Rest_translate_support hd v hf
  exact finSuppZ_of_translate_support hc

/-- `FinSuppZ` is closed under finite sums. -/
private lemma FinSuppZ.sum {α : Type} (t : Finset α) {F : α → ℤ → ℂ}
    (h : ∀ a ∈ t, FinSuppZ (F a)) : FinSuppZ (fun y => ∑ a ∈ t, F a y) := by
  classical
  induction t using Finset.induction with
  | empty => exact ⟨0, fun y _ => by simp⟩
  | insert a t hat ih =>
      have ha : FinSuppZ (F a) := h a (Finset.mem_insert_self a t)
      have ht : ∀ b ∈ t, FinSuppZ (F b) := fun b hb => h b (Finset.mem_insert_of_mem hb)
      obtain ⟨L1, h1⟩ := ha
      obtain ⟨L2, h2⟩ := ih ht
      refine ⟨L1 + L2, fun y hy => ?_⟩
      show (∑ a ∈ insert a t, F a y) = 0
      have e1 : F a y = 0 := h1 y (by omega)
      have e2 : (∑ a ∈ t, F a y) = 0 := h2 y (by omega)
      rw [Finset.sum_insert hat, e1, e2, add_zero]

/-- `FinSuppZ` is closed under sums over a fintype. -/
private lemma FinSuppZ.sum_univ {α : Type} [Fintype α] {F : α → ℤ → ℂ}
    (h : ∀ a, FinSuppZ (F a)) : FinSuppZ (fun y => ∑ a : α, F a y) := by
  have := FinSuppZ.sum (Finset.univ : Finset α) (fun a _ => h a)
  simpa using this

/-- `FinSuppZ` is closed under scalar multiplication. -/
private lemma FinSuppZ.const_mul (c : ℂ) {g : ℤ → ℂ} (h : FinSuppZ g) :
    FinSuppZ (fun y => c * g y) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨L, fun y hy => by show c * g y = 0; rw [hL y hy, mul_zero]⟩

/-- **The gauge is finitely supported** whenever `f` is supported in a translate of `symIcc N`. -/
private lemma gauge_finSuppZ {I : Type} [Fintype I] (s M : ℕ) (qH : I → ℤ)
    (q₁ q₂ : I → Fin s → ℤ) (N : ℕ) (x₀ : ℤ) (f : ℤ → ℂ)
    (hsup : ∀ x : ℤ, x ∉ symIcc N → f (x + x₀) = 0) :
    FinSuppZ (gauge s M qH q₁ q₂ f) := by
  have hd : 1 ≤ s + 1 := by omega
  have h1 : FinSuppZ (fun y => ∑ i : I, ∑ H : Fin (s+1) → Fin M × Fin M,
      ∑ H' : Fin (s+1) → Fin M × Fin M,
        Rest (incr s M (qH i) (q₁ i) (q₂ i) H H') f y) := by
    refine FinSuppZ.sum_univ fun i => ?_
    refine FinSuppZ.sum_univ fun H => ?_
    refine FinSuppZ.sum_univ fun H' => ?_
    exact Rest_finSuppZ hd _ hsup
  have h2 := FinSuppZ.const_mul (((Fintype.card I : ℂ))⁻¹) h1
  have h3 := FinSuppZ.const_mul ((((M : ℂ) ^ 4)⁻¹) ^ (s+1)) h2
  unfold gauge
  exact h3

/-- **The Cauchy–Schwarz step of `concatStep`** (KKL step 3, in the node's own vocabulary): the
`pbox (s + 1)` hypothesis, whose support is the *translate* `x₀ + symIcc N`, implies
`δ² |S| ≤ ∑'_y ‖gauge y‖²`.  This is `hyp_gauge` (the α-form of the hypothesis,
`δ |S| ≤ Re ∑'_y f y · gauge y`) followed by `cauchySchwarz_base`
(`concatAssemble.lean`), applied with `S := x₀ + symIcc N` (whose cardinality is `|symIcc N|`) and
with `T` a finite set containing that translate and the support of the gauge. -/
theorem gauge_cs {I : Type} [Fintype I] [Nonempty I] (s M N : ℕ) (qH : I → ℤ)
    (q₁ q₂ : I → Fin s → ℤ) (δ : ℝ) (f : ℤ → ℂ) (x₀ : ℤ) (hM : 1 ≤ M) (hδ : 0 < δ)
    (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsup : ∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0)
    (h : δ ≤ Work.Peluse.LadderP.Swap.avg (fun i : I =>
        Work.Peluse.LadderP.Swap.pbox (s + 1) (Fin.cons (qH i) (q₁ i)) (Fin.cons 0 (q₂ i)) M
          (Work.Peluse.symIcc N) f)) :
    δ ^ 2 * ((Work.Peluse.symIcc N).card : ℝ)
      ≤ ∑' y : ℤ, ‖Work.Peluse.SwapC.gauge s M qH q₁ q₂ f y‖ ^ 2 := by
  -- (0) The translate-support of `f`, and hence finite support of `f` and of the gauge.
  have ha : ∀ x : ℤ, x ∉ symIcc N → f (x + x₀) = 0 := by
    intro x hx
    apply hsup
    have hnx : ¬ (x.natAbs ≤ N) := fun hle => hx ((mem_symIcc_iff).mpr hle)
    have hN : (N : ℤ) < (x.natAbs : ℤ) := by
      exact_mod_cast (Nat.lt_of_not_le hnx)
    rw [show (x + x₀) - x₀ = x by ring]
    rwa [← Int.natCast_natAbs]
  have hfinf : FinSuppZ f := finSuppZ_of_translate_support (L := N) (c := x₀) ha
  have hfing : FinSuppZ (gauge s M qH q₁ q₂ f) := gauge_finSuppZ s M qH q₁ q₂ N x₀ f ha
  -- (1) The α-form of the hypothesis (`hyp_gauge`).
  have hα := hyp_gauge s M qH q₁ q₂ N δ f hM hδ hbd hfinf h
  -- (2) Cauchy–Schwarz in the base variable, on the translate `S = x₀ + symIcc N`.
  obtain ⟨L, hL⟩ := hfing
  set S : Finset ℤ := (symIcc N).image (fun y => y + x₀) with hS
  have hcard : S.card = (symIcc N).card :=
    Finset.card_image_of_injective _ (add_left_injective x₀)
  have hfS : ∀ x : ℤ, x ∉ S → f x = 0 := by
    intro x hx
    by_contra hne
    have h1 : |x - x₀| ≤ (N : ℤ) := not_lt.mp fun hlt => hne (hsup x hlt)
    have h3 : (x - x₀).natAbs ≤ N := by
      have h4 : (((x - x₀).natAbs : ℕ) : ℤ) ≤ (N : ℤ) := by
        rw [Int.natCast_natAbs]
        exact h1
      exact_mod_cast h4
    exact hx (Finset.mem_image.mpr ⟨x - x₀, (mem_symIcc_iff).mpr h3, by ring⟩)
  have hΦ : ∀ x : ℤ, x ∉ S ∪ symIcc L → gauge s M qH q₁ q₂ f x = 0 := by
    intro x hx
    refine hL x (Nat.lt_of_not_le fun hle => hx ?_)
    exact Finset.mem_union_right S ((mem_symIcc_iff).mpr hle)
  have key := cauchySchwarz_base (S := S) (T := S ∪ symIcc L) (f := f)
    (Φ := gauge s M qH q₁ q₂ f) (δ := δ) hfS hΦ (Finset.subset_union_left) hbd
    (le_of_lt hδ) (by rw [hcard]; exact hα)
  rwa [hcard] at key

end

end Work.Peluse.SwapC
