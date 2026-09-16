import Submission.ZagierHoffmanProof.StepL200
import Submission.ZagierHoffmanProof.Summability

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Polynomial RatFunc
open scoped BigOperators WithZero Topology
open Filter
open WithZero

/-!
# Step L201: the Frobenius relation `ζ_A(q·𝔰) = ζ_A(𝔰)^q`

`q = |F|` is a power of the characteristic `p = ringChar F` (`FiniteField.card'`), so the
`q`-th power map `x ↦ x^q` on the completion `K∞` is additive
(`add_pow_char_pow` after transporting `CharP` to `K∞` via the coercion `K ↪ K∞`).  Hence it
commutes with finite sums and — being continuous — with unconditionally convergent `tsum`s.

Termwise, `(∏_i a_i^{𝔰_i})^{-q} = (∏_i a_i^{q·𝔰_i})^{-1}`, so

  ★★★ `ζ_A F (q·𝔰) = (ζ_A F 𝔰) ^ q`   (`scaleTuple`),

which (Thakur's Frobenius relation for MZVs) transports non-vanishing from `𝔰` to `q·𝔰`;
iterating, the non-vanishing of StepL199/L200 extends from `[1,q]`-entries to
`q^k·[1,q]`-entries.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The algebra map `K ↪ K∞` is injective: a nonzero rational function has a well-defined
valuation at infinity, while `v 0 = 0`. -/
lemma infty_algebraMap_injective :
    Function.Injective (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) := by
  intro a b hab
  by_contra hne
  have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hsub : ((a - b : RatFunc F) : RatFunc.CompletionAtInfty F) = 0 := by
    change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (a - b)) = 0
    rw [map_sub, hab, sub_self]
  have hv := inftyValued_v_ratFunc F (a - b) hne'
  rw [hsub, map_zero] at hv
  exact WithZero.exp_ne_zero hv.symm

/-- `K∞ = CompletionAtInfty F` has the characteristic `p = ringChar F` of `F`. -/
lemma charP_completion : CharP (RatFunc.CompletionAtInfty F) (ringChar F) := by
  haveI : CharP F (ringChar F) := ringChar.charP F
  haveI : CharP (RatFunc F) (ringChar F) := inferInstance
  exact charP_of_injective_algebraMap (R := RatFunc F) (A := RatFunc.CompletionAtInfty F)
    (infty_algebraMap_injective F) (ringChar F)

/-- ★ The `q`-th power map on `K∞` is additive: `(x+y)^q = x^q + y^q`. -/
theorem add_pow_natCard (x y : RatFunc.CompletionAtInfty F) :
    (x + y) ^ (Nat.card F) = x ^ (Nat.card F) + y ^ (Nat.card F) := by
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F (ringChar F) := ringChar.charP F
  rcases FiniteField.card (K := F) (p := ringChar F) with ⟨n, hprime, hcard⟩
  haveI : Fact (Nat.Prime (ringChar F)) := ⟨hprime⟩
  have hcard' : Nat.card F = (ringChar F) ^ (n : ℕ) := by
    rw [← Fintype.card_eq_nat_card]
    exact hcard
  haveI : CharP (RatFunc.CompletionAtInfty F) (ringChar F) := charP_completion F
  rw [hcard']
  exact add_pow_char_pow x y (ringChar F) (n : ℕ)

/-- The `q`-th power map commutes with finite sums. -/
theorem sum_pow_natCard {ι : Type*} (s : Finset ι) (f : ι → RatFunc.CompletionAtInfty F) :
    (∑ i ∈ s, f i) ^ (Nat.card F) = ∑ i ∈ s, (f i) ^ (Nat.card F) := by
  classical
  have hq : Nat.card F ≠ 0 := by
    have h := card_ge_two F
    omega
  induction s using Finset.induction with
  | empty => simp [hq]
  | insert a t hat ih =>
      rw [Finset.sum_insert hat, Finset.sum_insert hat,
        add_pow_natCard F (f a) (∑ x ∈ t, f x), ih]

/-- The `q`-th power map commutes with unconditionally convergent sums. -/
theorem hasSum_pow_natCard {ι : Type*} {f : ι → RatFunc.CompletionAtInfty F}
    {a : RatFunc.CompletionAtInfty F} (h : HasSum f a) :
    HasSum (fun i => (f i) ^ (Nat.card F)) (a ^ (Nat.card F)) := by
  have h' : Tendsto (fun s : Finset ι => ∑ i ∈ s, f i) (SummationFilter.unconditional ι).filter
      (𝓝 a) := h
  have hc : Tendsto (fun x : RatFunc.CompletionAtInfty F => x ^ (Nat.card F)) (𝓝 a)
      (𝓝 (a ^ (Nat.card F))) := (continuous_pow (Nat.card F)).tendsto a
  refine (hc.comp h').congr' (Filter.Eventually.of_forall fun s => ?_)
  exact sum_pow_natCard F s f

/-- ★★ The `q`-th power map commutes with `tsum`. -/
theorem tsum_pow_natCard {ι : Type*} {f : ι → RatFunc.CompletionAtInfty F} (hf : Summable f) :
    (∑' i, f i) ^ (Nat.card F) = ∑' i, (f i) ^ (Nat.card F) := by
  have h := hasSum_pow_natCard F hf.hasSum
  exact h.tsum_eq.symm

/-! ## The scaled tuple and the term-level computation -/

/-- The tuple `q·𝔰` (componentwise scaling by `q`). -/
noncomputable def scaleTuple {r : ℕ} (𝔰 : Fin r → ℕ+) : Fin r → ℕ+ := fun i => qExp F * 𝔰 i

lemma scaleTuple_apply {r : ℕ} (𝔰 : Fin r → ℕ+) (i : Fin r) :
    (scaleTuple F 𝔰 i : ℕ) = (Nat.card F) * (𝔰 i : ℕ) := by
  rw [scaleTuple, PNat.mul_coe]
  rfl

/-- ★ Termwise: the `q`-th power of a zeta summand is the zeta summand of the scaled tuple. -/
theorem zetaTerm_pow_card {r : ℕ} (𝔰 : Fin r → ℕ+) (a : monicStrictAntiNatDegree F r) :
    (zetaTerm F 𝔰 a) ^ (Nat.card F) = zetaTerm F (scaleTuple F 𝔰) a := by
  rw [zetaTerm, zetaTerm, inv_pow]
  congr 1
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [scaleTuple_apply F 𝔰 i, ← pow_mul, mul_comm]

/-- `ζ_A` as a `tsum` of `zetaTerm`s (in the `zetaTerm` rather than `zetaTermAux` form). -/
lemma zeta_eq_tsum_zetaTerm' {r : ℕ} (𝔰 : Fin r → ℕ+) :
    ζ_A F 𝔰 = ∑' a : monicStrictAntiNatDegree F r, zetaTerm F 𝔰 a := by
  rw [ζ_A_eq_tsum_zetaTerm F 𝔰]
  exact tsum_congr (fun a => (zetaTerm_eq_zetaTermAux F 𝔰 a).symm)

/-- Summability of the zeta summands in the `zetaTerm` form. -/
lemma summable_zetaTerm {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) :
    Summable (fun a : monicStrictAntiNatDegree F r => zetaTerm F 𝔰 a) := by
  rw [show (fun a : monicStrictAntiNatDegree F r => zetaTerm F 𝔰 a)
      = (fun a => (∏ i : Fin r, ((a.val i : RatFunc F) : RatFunc.CompletionAtInfty F)
          ^ (𝔰 i : ℕ))⁻¹) from funext (fun a => rfl)]
  exact summable_zeta_term F hr 𝔰

/-- ★★★ Thakur's Frobenius relation for MZVs: `ζ_A(q·𝔰) = (ζ_A(𝔰))^q`. -/
theorem zeta_frobenius {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) :
    ζ_A F (scaleTuple F 𝔰) = (ζ_A F 𝔰) ^ (Nat.card F) := by
  have hsumm := summable_zetaTerm F hr 𝔰
  rw [zeta_eq_tsum_zetaTerm' F (scaleTuple F 𝔰), zeta_eq_tsum_zetaTerm' F 𝔰,
    tsum_pow_natCard F hsumm]
  exact tsum_congr (fun a => (zetaTerm_pow_card F 𝔰 a).symm)

/-- ★★ Non-vanishing is preserved by `q`-scaling of the tuple. -/
theorem zeta_scale_ne_zero {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) (h : ζ_A F 𝔰 ≠ 0) :
    ζ_A F (scaleTuple F 𝔰) ≠ 0 := by
  rw [zeta_frobenius F hr 𝔰]
  exact pow_ne_zero _ h

/-- ★★ Iterated `q`-scaling preserves non-vanishing. -/
theorem zeta_scale_iter_ne_zero {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) (k : ℕ)
    (h : ζ_A F 𝔰 ≠ 0) : ζ_A F ((scaleTuple F)^[k] 𝔰) ≠ 0 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact zeta_scale_ne_zero F hr _ ih

/-- ★★ Combining Frobenius with the `≤ q`-non-vanishing: every MZV whose entries are
`q^k·n` with `n ≤ q` is nonzero. -/
theorem zeta_scale_le_card_ne_zero {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) (k : ℕ)
    (h𝔰 : ∀ j, (𝔰 j : ℕ) ≤ Nat.card F) : ζ_A F ((scaleTuple F)^[k] 𝔰) ≠ 0 :=
  zeta_scale_iter_ne_zero F hr 𝔰 k (zeta_entries_ne_zero F hr 𝔰 h𝔰)

end ZagierHoffmanPositiveChar
