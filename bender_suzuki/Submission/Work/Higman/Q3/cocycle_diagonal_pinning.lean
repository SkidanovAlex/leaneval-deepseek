import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.bilinear_frob
import Submission.Work.Higman.QuadAux
import Submission.Work.Higman.bivariate_monomial_indep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3

/-! ## Helper lemmas

`axis_pinning` pins an equivariant function on `(GaloisField 2 n)ˣ` to a single monomial.
`bivariate_additive_frob` is the two-variable Frobenius expansion of a biadditive map.
`bivariate_frob_resonance` extracts the resonance condition on the coefficients from the
scaling equivariance. -/

/-- **Axis pinning.**  If `orderOf ν = 2 ^ n - 1` (so `ν` generates the multiplicative group)
and `f (ν * α) = lam * f α`, then `f` is completely determined: `f α = f 1 * α ^ a` for any
`a ∈ [1, 2 ^ n - 1]` with `ν ^ a = lam`. -/
lemma axis_pinning {n : ℕ} (hn : 1 ≤ n) {ν lam : (GaloisField 2 n)ˣ}
    (hν : orderOf ν = 2 ^ n - 1)
    (f : GaloisField 2 n → GaloisField 2 n) (hf0 : f 0 = 0)
    (hfeq : ∀ α, f ((ν : GaloisField 2 n) * α) = (lam : GaloisField 2 n) * f α)
    (hne : f 1 ≠ 0) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ 2 ^ n - 1 ∧ (ν : GaloisField 2 n) ^ a = (lam : GaloisField 2 n) ∧
      ∀ α, f α = f 1 * α ^ a := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  have htop : Subgroup.zpowers ν = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hν, Nat.card_units, hcard]
  have hfin : IsOfFinOrder ν := isOfFinOrder_of_finite ν
  have hνval : (ν : GaloisField 2 n) ^ (2 ^ n - 1) = 1 := by
    have h := congrArg (fun u : (GaloisField 2 n)ˣ => (u : GaloisField 2 n))
      (pow_orderOf_eq_one ν)
    rw [hν] at h
    simpa using h
  have hfp : ∀ m : ℕ, f ((ν : GaloisField 2 n) ^ m) =
      (lam : GaloisField 2 n) ^ m * f 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', hfeq, ih, pow_succ]
      ring
  have hgen : ∀ a : ℕ, 1 ≤ a → (ν : GaloisField 2 n) ^ a = (lam : GaloisField 2 n) →
      ∀ α, f α = f 1 * α ^ a := by
    intro a ha1 haν α
    rcases eq_or_ne α 0 with rfl | hα
    · rw [hf0, zero_pow (by omega : a ≠ 0), mul_zero]
    · have hm0 : (Units.mk0 α hα) ∈ Subgroup.zpowers ν := by
        rw [htop]; exact Subgroup.mem_top _
      obtain ⟨m, -, hmν⟩ := Finset.mem_image.mp
        ((IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf hfin).mp hm0)
      have hmval : (ν : GaloisField 2 n) ^ m = α := by
        have h := congrArg (fun u : (GaloisField 2 n)ˣ => (u : GaloisField 2 n)) hmν
        simpa using h
      have hkey : ((ν : GaloisField 2 n) ^ m) ^ a = (lam : GaloisField 2 n) ^ m := by
        rw [← haν, ← pow_mul (ν : GaloisField 2 n) a m,
          ← pow_mul (ν : GaloisField 2 n) m a, Nat.mul_comm a m]
      rw [← hmval, hfp m, hkey, mul_comm]
  obtain ⟨k, hk, hkν⟩ := Finset.mem_image.mp
    ((IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf hfin).mp
      (by rw [htop]; exact Subgroup.mem_top lam))
  rw [Finset.mem_range, hν] at hk
  have hkνval : (ν : GaloisField 2 n) ^ k = (lam : GaloisField 2 n) := by
    have h := congrArg (fun u : (GaloisField 2 n)ˣ => (u : GaloisField 2 n)) hkν
    simpa using h
  have hpow2 : 1 ≤ 2 ^ n - 1 := by
    have h2 : 2 ≤ 2 ^ n := by
      have hlt := Nat.one_lt_pow (n := n) (by omega : n ≠ 0) (by norm_num : 1 < 2)
      omega
    omega
  by_cases hk0 : k = 0
  · have hνlam : (ν : GaloisField 2 n) ^ (2 ^ n - 1) = (lam : GaloisField 2 n) := by
      rw [hνval]
      rw [hk0, pow_zero] at hkνval
      exact hkνval
    exact ⟨2 ^ n - 1, hpow2, le_refl _, hνlam, hgen (2 ^ n - 1) hpow2 hνlam⟩
  · exact ⟨k, by omega, by omega, hkνval, hgen k (by omega) hkνval⟩

/-- **Bivariate Frobenius expansion.**  A biadditive `L : F → F → F` over a finite field
`F` with `Fintype.card F = 2 ^ n` is a sum of Frobenius monomials. -/
lemma bivariate_additive_frob {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (L : F → F → F)
    (h1 : ∀ β α α', L (α + α') β = L α β + L α' β)
    (h2 : ∀ α β β', L α (β + β') = L α β + L α β') :
    ∃ e : ℕ → ℕ → F, ∀ α β, L α β =
      ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, e k l * α ^ (2 ^ k) * β ^ (2 ^ l) := by
  classical
  let g : ℕ → F → F := fun k β => (polyRep (fun α => L α β)).coeff (2 ^ k)
  have hLfrob : ∀ β α, L α β = ∑ k ∈ Finset.range n, g k β * α ^ (2 ^ k) := by
    intro β α
    exact additive_frob hcard (fun α => L α β) (fun α α' => h1 β α α') α
  have hgadd : ∀ k, ∀ β β', g k (β + β') = g k β + g k β' := by
    intro k β β'
    have hp : polyRep (fun α => L α (β + β')) =
        polyRep (fun α => L α β) + polyRep (fun α => L α β') := by
      rw [show (fun α => L α (β + β')) = (fun α => L α β + L α β') from
        funext (fun α => h2 α β β')]
      exact polyRep_add (fun α => L α β) (fun α => L α β')
    show (polyRep (fun α => L α (β + β'))).coeff (2 ^ k) =
      (polyRep (fun α => L α β)).coeff (2 ^ k) + (polyRep (fun α => L α β')).coeff (2 ^ k)
    rw [hp, Polynomial.coeff_add]
  let e : ℕ → ℕ → F := fun k l => (polyRep (g k)).coeff (2 ^ l)
  have hgfrob : ∀ k β, g k β = ∑ l ∈ Finset.range n, e k l * β ^ (2 ^ l) := by
    intro k β
    exact additive_frob hcard (g k) (hgadd k) β
  refine ⟨e, fun α β => ?_⟩
  rw [hLfrob β α]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hgfrob k β, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

/-- **Resonance.**  If a biadditive `L` has Frobenius expansion with coefficients `e` and is
equivariant under `(ν, ν') ↦ lam`, then a nonzero coefficient `e k l` forces the resonance
relation `ν ^ (2 ^ k) * ν' ^ (2 ^ l) = lam`. -/
lemma bivariate_frob_resonance {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) {ν ν' lam : F} (L : F → F → F) (e : ℕ → ℕ → F)
    (hexp : ∀ α β, L α β =
      ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, e k l * α ^ (2 ^ k) * β ^ (2 ^ l))
    (heq : ∀ α β, L (ν * α) (ν' * β) = lam * L α β) :
    ∀ k l, k < n → l < n → e k l ≠ 0 → ν ^ (2 ^ k) * ν' ^ (2 ^ l) = lam := by
  classical
  intro k l hk hl hne
  have h : ∀ α β, ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
      (e k l * (ν ^ (2 ^ k) * ν' ^ (2 ^ l)) - lam * e k l) * α ^ (2 ^ k) * β ^ (2 ^ l)
      = 0 := by
    intro α β
    have h1 : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        e k l * (ν * α) ^ (2 ^ k) * (ν' * β) ^ (2 ^ l))
        = lam * (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
            e k l * α ^ (2 ^ k) * β ^ (2 ^ l)) := by
      rw [← hexp (ν * α) (ν' * β), ← hexp α β]
      exact heq α β
    have hS1 : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        e k l * (ν * α) ^ (2 ^ k) * (ν' * β) ^ (2 ^ l))
        = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
            e k l * (ν * α) ^ (2 ^ k) * (ν' * β) ^ (2 ^ l) := rfl
    have hS2 : lam * (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
            e k l * α ^ (2 ^ k) * β ^ (2 ^ l))
        = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
            lam * (e k l * α ^ (2 ^ k) * β ^ (2 ^ l)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum]
    have hsum : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        (e k l * (ν ^ (2 ^ k) * ν' ^ (2 ^ l)) - lam * e k l) * α ^ (2 ^ k) * β ^ (2 ^ l))
        = (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
            e k l * (ν * α) ^ (2 ^ k) * (ν' * β) ^ (2 ^ l))
          - lam * (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
              e k l * α ^ (2 ^ k) * β ^ (2 ^ l)) := by
      rw [hS1, hS2, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro l _
      rw [mul_pow, mul_pow]; ring
    rw [hsum, h1, sub_self]
  have hc := bivariate_monomial_indep hcard
    (fun k l => e k l * (ν ^ (2 ^ k) * ν' ^ (2 ^ l)) - lam * e k l) h
  have h2 := hc k (Finset.mem_range.mpr hk) l (Finset.mem_range.mpr hl)
  have h3 : (e k l) * (ν ^ (2 ^ k) * ν' ^ (2 ^ l) - lam) = 0 := by
    rw [← h2]; ring
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 hne
  · exact sub_eq_zero.mp h4

theorem cocycle_diagonal_pinning
    {n : ℕ} (hn : 1 ≤ n)
    (b : (GaloisField 2 n × GaloisField 2 n) → (GaloisField 2 n × GaloisField 2 n) →
      GaloisField 2 n) [Biadd b]
    {ν ν' lam : (GaloisField 2 n)ˣ} (hν : orderOf ν = 2 ^ n - 1)
    (hν' : orderOf ν' = 2 ^ n - 1) (hlam : orderOf lam = 2 ^ n - 1)
    (heq : ∀ α β : GaloisField 2 n,
      b (↑ν * α, ↑ν' * β) (↑ν * α, ↑ν' * β) = ↑lam * b (α, β) (α, β))
    (hne1 : ∀ α : GaloisField 2 n, α ≠ 0 → b (α, 0) (α, 0) ≠ 0)
    (hne2 : ∀ β : GaloisField 2 n, β ≠ 0 → b (0, β) (0, β) ≠ 0) :
    ∃ (a a' : ℕ) (C C' : GaloisField 2 n),
      C ≠ 0 ∧ C' ≠ 0 ∧ 1 ≤ a ∧ a ≤ 2 ^ n - 1 ∧ 1 ≤ a' ∧ a' ≤ 2 ^ n - 1 ∧
      (↑ν) ^ a = ↑lam ∧ (↑ν') ^ a' = ↑lam ∧
      (∀ α : GaloisField 2 n, b (α, 0) (α, 0) = C * α ^ a) ∧
      (∀ β : GaloisField 2 n, b (0, β) (0, β) = C' * β ^ a') ∧
      (∃ e : ℕ → ℕ → GaloisField 2 n,
        (∀ k l : ℕ, e k l ≠ 0 → (↑ν) ^ (2 ^ k) * (↑ν') ^ (2 ^ l) = ↑lam) ∧
        ∀ α β : GaloisField 2 n,
          b (α, β) (α, β) = C * α ^ a + C' * β ^ a' +
            ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
              e k l * α ^ (2 ^ k) * β ^ (2 ^ l)) := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hn0 : n ≠ 0 := by omega
  have hcardN : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact hcardN
  -- ## the two axis functions
  have hf0 : (fun α : GaloisField 2 n => b (α, 0) (α, 0)) 0 = 0 := by
    show b (0, 0) (0, 0) = 0
    exact Biadd.zero_left (b := b) (0 : GaloisField 2 n × GaloisField 2 n)
  have hfeq1 : ∀ α : GaloisField 2 n,
      (fun α => b (α, 0) (α, 0)) ((ν : GaloisField 2 n) * α) =
        (lam : GaloisField 2 n) * (fun α => b (α, 0) (α, 0)) α := by
    intro α
    simpa using heq α 0
  have hg0 : (fun β : GaloisField 2 n => b (0, β) (0, β)) 0 = 0 := by
    show b (0, 0) (0, 0) = 0
    exact Biadd.zero_left (b := b) (0 : GaloisField 2 n × GaloisField 2 n)
  have hgeq1 : ∀ β : GaloisField 2 n,
      (fun β => b (0, β) (0, β)) ((ν' : GaloisField 2 n) * β) =
        (lam : GaloisField 2 n) * (fun β => b (0, β) (0, β)) β := by
    intro β
    simpa using heq 0 β
  obtain ⟨a, ha1, haq, haν, hf⟩ :=
    axis_pinning hn hν (fun α => b (α, 0) (α, 0)) hf0 hfeq1 (hne1 1 one_ne_zero)
  obtain ⟨a', ha'1, ha'q, ha'ν, hg⟩ :=
    axis_pinning hn hν' (fun β => b (0, β) (0, β)) hg0 hgeq1 (hne2 1 one_ne_zero)
  let C : GaloisField 2 n := b (1, 0) (1, 0)
  let C' : GaloisField 2 n := b (0, 1) (0, 1)
  have hCne : C ≠ 0 := hne1 1 one_ne_zero
  have hC'ne : C' ≠ 0 := hne2 1 one_ne_zero
  have hfax : ∀ α, b (α, 0) (α, 0) = C * α ^ a := fun α => hf α
  have hfbx : ∀ β, b (0, β) (0, β) = C' * β ^ a' := fun β => hg β
  -- ## the mixed part `R`
  let R : GaloisField 2 n → GaloisField 2 n → GaloisField 2 n :=
    fun α β => b (α, 0) (0, β) + b (0, β) (α, 0)
  have hRadd1 : ∀ β α α', R (α + α') β = R α β + R α' β := by
    intro β α α'
    have hb : b (α + α', 0) (0, β) = b (α, 0) (0, β) + b (α', 0) (0, β) := by
      have h := Biadd.add_left (b := b) (α, 0) (α', 0) (0, β)
      simp only [Prod.mk_add_mk, add_zero, zero_add] at h
      exact h
    have hc : b (0, β) (α + α', 0) = b (0, β) (α, 0) + b (0, β) (α', 0) := by
      have h := Biadd.add_right (b := b) (0, β) (α, 0) (α', 0)
      simp only [Prod.mk_add_mk, add_zero, zero_add] at h
      exact h
    show b (α + α', 0) (0, β) + b (0, β) (α + α', 0)
        = (b (α, 0) (0, β) + b (0, β) (α, 0))
          + (b (α', 0) (0, β) + b (0, β) (α', 0))
    rw [hb, hc]
    ring
  have hRadd2 : ∀ α β β', R α (β + β') = R α β + R α β' := by
    intro α β β'
    have hb : b (α, 0) (0, β + β') = b (α, 0) (0, β) + b (α, 0) (0, β') := by
      have h := Biadd.add_right (b := b) (α, 0) (0, β) (0, β')
      simp only [Prod.mk_add_mk, add_zero, zero_add] at h
      exact h
    have hc : b (0, β + β') (α, 0) = b (0, β) (α, 0) + b (0, β') (α, 0) := by
      have h := Biadd.add_left (b := b) (0, β) (0, β') (α, 0)
      simp only [Prod.mk_add_mk, add_zero, zero_add] at h
      exact h
    show b (α, 0) (0, β + β') + b (0, β + β') (α, 0)
        = (b (α, 0) (0, β) + b (0, β) (α, 0))
          + (b (α, 0) (0, β') + b (0, β') (α, 0))
    rw [hb, hc]
    ring
  have hRQ : ∀ α β, b (α, β) (α, β) = C * α ^ a + C' * β ^ a' + R α β := by
    intro α β
    have h1 : b (α, β) (α, β)
        = b (α, 0) (α, 0) + b (α, 0) (0, β) + b (0, β) (α, 0) + b (0, β) (0, β) := by
      have hL : b (α, β) (α, β) = b (α, 0) (α, β) + b (0, β) (α, β) := by
        have h := Biadd.add_left (b := b) (α, 0) (0, β) (α, β)
        simp only [Prod.mk_add_mk, add_zero, zero_add] at h
        exact h
      have ha : b (α, 0) (α, β) = b (α, 0) (α, 0) + b (α, 0) (0, β) := by
        have h := Biadd.add_right (b := b) (α, 0) (α, 0) (0, β)
        simp only [Prod.mk_add_mk, add_zero, zero_add] at h
        exact h
      have hb : b (0, β) (α, β) = b (0, β) (α, 0) + b (0, β) (0, β) := by
        have h := Biadd.add_right (b := b) (0, β) (α, 0) (0, β)
        simp only [Prod.mk_add_mk, add_zero, zero_add] at h
        exact h
      rw [hL, ha, hb]
      ring
    rw [h1, hfax α, hfbx β]
    show C * α ^ a + b (α, 0) (0, β) + b (0, β) (α, 0) + C' * β ^ a'
        = C * α ^ a + C' * β ^ a' + (b (α, 0) (0, β) + b (0, β) (α, 0))
    ring
  have hRQ' : ∀ α β, R α β = b (α, β) (α, β) + C * α ^ a + C' * β ^ a' := by
    intro α β
    rw [hRQ α β]
    show (b (α, 0) (0, β) + b (0, β) (α, 0))
        = (C * α ^ a + C' * β ^ a' + (b (α, 0) (0, β) + b (0, β) (α, 0)))
          + C * α ^ a + C' * β ^ a'
    rw [show (C * α ^ a + C' * β ^ a' + (b (α, 0) (0, β) + b (0, β) (α, 0)))
          + C * α ^ a + C' * β ^ a'
        = (b (α, 0) (0, β) + b (0, β) (α, 0))
          + ((C * α ^ a + C * α ^ a) + (C' * β ^ a' + C' * β ^ a')) from by abel]
    rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero]
    abel
  -- ## equivariance of `R`
  have heqR : ∀ α β, R ((ν : GaloisField 2 n) * α) ((ν' : GaloisField 2 n) * β)
      = (lam : GaloisField 2 n) * R α β := by
    intro α β
    rw [hRQ' ((ν : GaloisField 2 n) * α) ((ν' : GaloisField 2 n) * β), hRQ' α β, heq α β,
      mul_pow, mul_pow, haν, ha'ν]
    ring
  -- ## expansion and resonance
  obtain ⟨e, hexp⟩ := bivariate_additive_frob hcard R hRadd1 hRadd2
  have hres : ∀ k l, k < n → l < n → e k l ≠ 0 →
      (ν : GaloisField 2 n) ^ (2 ^ k) * (ν' : GaloisField 2 n) ^ (2 ^ l)
        = (lam : GaloisField 2 n) :=
    bivariate_frob_resonance hcard (ν := (ν : GaloisField 2 n))
      (ν' := (ν' : GaloisField 2 n)) (lam := (lam : GaloisField 2 n)) R e hexp heqR
  -- the statement's power equations live in the units group (the identity coercion is chosen)
  have haνu : ν ^ a = lam := Units.ext (by
    rw [Units.val_pow_eq_pow_val]; exact haν)
  have ha'νu : ν' ^ a' = lam := Units.ext (by
    rw [Units.val_pow_eq_pow_val]; exact ha'ν)
  have hresu : ∀ k l, k < n → l < n → e k l ≠ 0 →
      ν ^ (2 ^ k) * ν' ^ (2 ^ l) = lam := by
    intro k l hk hl hne
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    exact hres k l hk hl hne
  -- ## assembly
  refine ⟨a, a', C, C', hCne, hC'ne, ha1, haq, ha'1, ha'q, haνu, ha'νu, hfax, hfbx, ?_⟩
  refine ⟨fun k l => if k < n ∧ l < n then e k l else 0, ?_, ?_⟩
  · intro k l hkl
    change (if k < n ∧ l < n then e k l else 0) ≠ 0 at hkl
    by_cases hkk : k < n ∧ l < n
    · rw [if_pos hkk] at hkl
      exact hresu k l hkk.1 hkk.2 hkl
    · rw [if_neg hkk] at hkl
      exact absurd rfl hkl
  · intro α β
    rw [hRQ α β]
    have hsum : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        (if k < n ∧ l < n then e k l else 0) * α ^ (2 ^ k) * β ^ (2 ^ l))
        = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
            e k l * α ^ (2 ^ k) * β ^ (2 ^ l) := by
      apply Finset.sum_congr rfl; intro k hk
      apply Finset.sum_congr rfl; intro l hl
      rw [if_pos ⟨Finset.mem_range.mp hk, Finset.mem_range.mp hl⟩]
    rw [hsum, ← hexp α β]

end Work.Higman.Q3
