import Mathlib
import Submission.Work.Higman.Q3.L12.case_core
import Submission.Work.Higman.Q3.L12.axis_type_exponents
import Submission.Work.Higman.Q3.L12.case_C
import Submission.Work.Higman.Q3.L12.case_C_II
import Submission.Work.Higman.Q3.L12.case_D
import Submission.Work.Higman.Q3.L12.res_r_ab_pin
import Submission.Work.Higman.Q3.L12.canonical_dispatch

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators

namespace Work.Higman.Q3.L12

/-! ## Arithmetic and bookkeeping helpers for the normalisation

The statement below normalises the *pinned* squaring form
`Q (α,β) = C α^a + C' β^{a'} + Σ e k l α^{2^k} β^{2^l}` (with `ν^a = ν'^{a'} = lam` and the
resonance `e k l ≠ 0 → ν^{2^k} ν'^{2^l} = lam`) into the *canonical* form
`C α^{1+2^r} + C' β^{1+2^s} + Σ g k l α^{2^k} β^{2^l}` by a Frobenius twist
`(α,β) ↦ (α^{2^t}, β^{2^u})`.

The helpers collected here are the arithmetical ingredients:

* `pc_pow_eq_of_modEq` — powers with congruent exponents in `𝔽_{2ⁿ}` agree;
* `pc_two_pow_modEq_of_modEq`, `pc_two_pow_mul_modEq` — the same for the exponents `2 ^ e`;
* `pc_resonance_modEq` — the resonance congruence transforms correctly under the twist;
* `pc_coprime_one_add_two_pow`, `pc_coprime_of_orderOf_pow_eq` — coprimality bookkeeping;
* `pc_axis_rebase` — the ambiguity `A(n,θ) ≅ A(n,θ⁻¹)` in the axis exponent;
* `pc_mod_add_sub`, `pc_mod_sub_add` — the inverse of the shift `k ↦ (k+t) % n` on `range n`;
* `pc_scale_form` — diagonal rescaling of a canonical form. -/

/-- In `𝔽_{2ⁿ}` (`n ≥ 1`), powers with exponents congruent modulo `2 ^ n - 1` agree, provided
both exponents are positive (so that the value `0` is handled). -/
lemma pc_pow_eq_of_modEq {n : ℕ} (hn : 1 ≤ n) {x : GaloisField 2 n} {e₁ e₂ : ℕ}
    (h1 : 1 ≤ e₁) (h2 : 1 ≤ e₂) (h : e₁ ≡ e₂ [MOD 2 ^ n - 1]) : x ^ e₁ = x ^ e₂ := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_pow (by omega), zero_pow (by omega)]
  · have hpos : 0 < 2 ^ n - 1 := by
      have h2n : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    have hM : x ^ (2 ^ n - 1) = 1 := by
      have hh : x ^ (2 ^ n - 1) * x = x := by
        rw [← pow_succ, Nat.sub_add_cancel (by have := Nat.one_le_two_pow (n := n); omega),
          pow_two_pow_card hn x]
      exact mul_right_cancel₀ hx (by rw [hh, one_mul])
    have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨2 ^ n - 1, hpos, hM⟩
    have hdvd : orderOf x ∣ 2 ^ n - 1 := orderOf_dvd_iff_pow_eq_one.mpr hM
    exact (hfin.pow_eq_pow_iff_modEq).mpr (Nat.ModEq.of_dvd hdvd h)

/-- `2 ^ p ≡ 2 ^ q [MOD 2 ^ n - 1]` when `p ≡ q [MOD n]` (`n ≥ 1`). -/
lemma pc_two_pow_modEq_of_modEq {n p q : ℕ} (hn : 1 ≤ n) (h : p ≡ q [MOD n]) :
    2 ^ p ≡ 2 ^ q [MOD 2 ^ n - 1] := by
  have hp : p % n = q % n := h
  refine (pow_two_modEq (n := n) (a := p) (by omega)).trans ?_
  rw [hp]
  exact (pow_two_modEq (n := n) (a := q) (by omega)).symm

/-- If `a ≡ 2 ^ j * (1 + 2 ^ r) [MOD 2 ^ n - 1]` and `(t + j) % n = 0`, then
`2 ^ t * a ≡ 1 + 2 ^ r [MOD 2 ^ n - 1]`. -/
lemma pc_two_pow_mul_modEq {n a r j t : ℕ} (hn : 1 ≤ n)
    (haj : a ≡ 2 ^ j * (1 + 2 ^ r) [MOD 2 ^ n - 1]) (htj : (t + j) % n = 0) :
    2 ^ t * a ≡ 1 + 2 ^ r [MOD 2 ^ n - 1] := by
  have h1 : 2 ^ t * a ≡ 2 ^ t * (2 ^ j * (1 + 2 ^ r)) [MOD 2 ^ n - 1] :=
    Nat.ModEq.mul_left _ haj
  have h2 : 2 ^ t * (2 ^ j * (1 + 2 ^ r)) = 2 ^ (t + j) * (1 + 2 ^ r) := by
    rw [← mul_assoc, ← pow_add]
  have h3 : 2 ^ (t + j) ≡ 2 ^ 0 [MOD 2 ^ n - 1] := by
    refine pc_two_pow_modEq_of_modEq hn ?_
    show (t + j) % n = 0 % n
    rw [htj, Nat.zero_mod]
  rw [pow_zero] at h3
  rw [h2] at h1
  exact h1.trans (by simpa using Nat.ModEq.mul_right (1 + 2 ^ r) h3)

/-- The resonance congruence in the twisted coordinates: multiplying the relation
`a' * 2 ^ k + a * 2 ^ l ≡ a * a'` by `2 ^ (t+u)` and replacing `2 ^ t * a` by `1 + 2 ^ r` and
`2 ^ u * a'` by `1 + 2 ^ s` gives the displayed congruence. -/
lemma pc_resonance_modEq {n a a' r s t u k l K L : ℕ} (hn : 1 ≤ n)
    (h1 : a' * 2 ^ k + a * 2 ^ l ≡ a * a' [MOD 2 ^ n - 1])
    (h2 : 2 ^ t * a ≡ 1 + 2 ^ r [MOD 2 ^ n - 1])
    (h3 : 2 ^ u * a' ≡ 1 + 2 ^ s [MOD 2 ^ n - 1])
    (h4 : (k + t) % n = K) (h5 : (l + u) % n = L) :
    (1 + 2 ^ s) * 2 ^ K + (1 + 2 ^ r) * 2 ^ L ≡ (1 + 2 ^ r) * (1 + 2 ^ s)
      [MOD 2 ^ n - 1] := by
  have hn0 : 0 < n := by omega
  have hKlt : K < n := h4 ▸ Nat.mod_lt _ hn0
  have hLlt : L < n := h5 ▸ Nat.mod_lt _ hn0
  have hK : 2 ^ (t + k) ≡ 2 ^ K [MOD 2 ^ n - 1] := by
    refine pc_two_pow_modEq_of_modEq hn ?_
    show (t + k) % n = K % n
    rw [Nat.add_comm t k, h4, Nat.mod_eq_of_lt hKlt]
  have hL : 2 ^ (u + l) ≡ 2 ^ L [MOD 2 ^ n - 1] := by
    refine pc_two_pow_modEq_of_modEq hn ?_
    show (u + l) % n = L % n
    rw [Nat.add_comm u l, h5, Nat.mod_eq_of_lt hLlt]
  have e1 : 2 ^ (t + u) * (a' * 2 ^ k) = (2 ^ u * a') * 2 ^ (t + k) := by
    rw [pow_add, pow_add]; ring
  have e2 : 2 ^ (t + u) * (a * 2 ^ l) = (2 ^ t * a) * 2 ^ (u + l) := by
    rw [pow_add, pow_add]; ring
  have e3 : 2 ^ (t + u) * (a * a') = (2 ^ t * a) * (2 ^ u * a') := by
    rw [pow_add]; ring
  have s1 : 2 ^ (t + u) * (a' * 2 ^ k) ≡ (1 + 2 ^ s) * 2 ^ K [MOD 2 ^ n - 1] := by
    rw [e1]; exact Nat.ModEq.mul h3 hK
  have s2 : 2 ^ (t + u) * (a * 2 ^ l) ≡ (1 + 2 ^ r) * 2 ^ L [MOD 2 ^ n - 1] := by
    rw [e2]; exact Nat.ModEq.mul h2 hL
  have s3 : 2 ^ (t + u) * (a * a') ≡ (1 + 2 ^ r) * (1 + 2 ^ s) [MOD 2 ^ n - 1] := by
    rw [e3]; exact Nat.ModEq.mul h2 h3
  have hm : 2 ^ (t + u) * (a' * 2 ^ k + a * 2 ^ l) ≡ 2 ^ (t + u) * (a * a')
      [MOD 2 ^ n - 1] := Nat.ModEq.mul_left _ h1
  rw [Nat.mul_add] at hm
  exact (Nat.ModEq.add s1 s2).symm.trans (hm.trans s3)

/-- If `a ≡ 2 ^ j * (1 + 2 ^ r) [MOD 2 ^ n - 1]` and `a` is coprime to `2 ^ n - 1`, then
`1 + 2 ^ r` is coprime to `2 ^ n - 1`. -/
lemma pc_coprime_one_add_two_pow {n a r j : ℕ} (hn : 1 ≤ n)
    (haj : a ≡ 2 ^ j * (1 + 2 ^ r) [MOD 2 ^ n - 1])
    (hcop : Nat.Coprime a (2 ^ n - 1)) : Nat.Coprime (1 + 2 ^ r) (2 ^ n - 1) := by
  have hd1 : (1 + 2 ^ r).gcd (2 ^ n - 1) ∣ 1 + 2 ^ r := Nat.gcd_dvd_left _ _
  have hd2 : (1 + 2 ^ r).gcd (2 ^ n - 1) ∣ 2 ^ n - 1 := Nat.gcd_dvd_right _ _
  have hd3 : (1 + 2 ^ r).gcd (2 ^ n - 1) ∣ 2 ^ j * (1 + 2 ^ r) :=
    dvd_mul_of_dvd_right hd1 _
  have hgcd : (2 ^ j * (1 + 2 ^ r)).gcd (2 ^ n - 1) = 1 := by
    rw [← Nat.ModEq.gcd_eq haj]
    exact hcop
  have hd4 : (1 + 2 ^ r).gcd (2 ^ n - 1) ∣ (2 ^ j * (1 + 2 ^ r)).gcd (2 ^ n - 1) :=
    Nat.dvd_gcd hd3 hd2
  rw [hgcd] at hd4
  exact Nat.dvd_one.mp hd4

/-- If `orderOf x = orderOf y = M > 0` and `x ^ a = y`, then `a` is coprime to `M`.  (Writing
`d = gcd a M`, `a = d * a₁`, `M = d * M₁`, one has `y ^ M₁ = (x ^ M) ^ a₁ = 1`, so
`M ∣ M / d`, forcing `d = 1`.) -/
lemma pc_coprime_of_orderOf_pow_eq {G : Type*} [Monoid G] {x y : G} {a M : ℕ}
    (hM : 0 < M) (hx : orderOf x = M) (hy : orderOf y = M) (h : x ^ a = y) :
    Nat.Coprime a M := by
  set d : ℕ := a.gcd M with hd
  have hda : d ∣ a := Nat.gcd_dvd_left a M
  have hdM : d ∣ M := Nat.gcd_dvd_right a M
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdM hM
  have hkey : (x ^ a) ^ (M / d) = 1 := by
    rw [← pow_mul]
    have hmul : a * (M / d) = M * (a / d) := by
      obtain ⟨a₁, ha₁⟩ := hda
      obtain ⟨M₁, hM₁⟩ := hdM
      rw [ha₁, hM₁, Nat.mul_div_cancel_left M₁ hdpos, Nat.mul_div_cancel_left a₁ hdpos]
      ring
    rw [hmul, pow_mul, ← hx, pow_orderOf_eq_one, one_pow]
  have hdvd : M ∣ M / d := by
    have h1 : orderOf (x ^ a) ∣ M / d := orderOf_dvd_iff_pow_eq_one.mpr hkey
    rwa [h, hy] at h1
  have hle : M ≤ M / d :=
    Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hM hdM) hdpos) hdvd
  have heq : M / d = M := le_antisymm (Nat.div_le_self M d) hle
  have h2 : d * M = M := by simpa [heq] using Nat.mul_div_cancel' hdM
  exact Nat.eq_of_mul_eq_mul_right hM (by rw [h2, one_mul])

/-- The ambiguity `A(n,θ) ≅ A(n,θ⁻¹)`: the pair `(j, s)` of an axis exponent may be replaced by
`((j + s) % n, n - s)`. -/
lemma pc_axis_rebase {n j s : ℕ} (hn : 1 ≤ n) (hs : s < n) :
    2 ^ j * (1 + 2 ^ s) ≡ 2 ^ ((j + s) % n) * (1 + 2 ^ (n - s)) [MOD 2 ^ n - 1] := by
  have hn0 : 0 < n := hn
  have aux : 2 ^ j * (1 + 2 ^ s) ≡ 2 ^ (j + s) * (1 + 2 ^ (n - s)) [MOD 2 ^ n - 1] := by
    have h1 : 2 ^ j * (1 + 2 ^ s) = 2 ^ j + 2 ^ (j + s) := by
      rw [mul_add, mul_one, ← pow_add]
    have h2 : 2 ^ (j + s) * (1 + 2 ^ (n - s)) = 2 ^ (j + s) + 2 ^ (j + n) := by
      rw [mul_add, mul_one, ← pow_add]
      congr 2
      omega
    have h3 : 2 ^ (j + n) ≡ 2 ^ j [MOD 2 ^ n - 1] := by
      refine (pc_two_pow_modEq_of_modEq hn (p := j + n) (q := j) ?_)
      show (j + n) % n = j % n
      rw [Nat.add_mod_right]
    rw [h1, h2, Nat.add_comm (2 ^ j) (2 ^ (j + s))]
    exact Nat.ModEq.add_left _ h3.symm
  refine aux.trans ?_
  exact Nat.ModEq.mul_right _ (pow_two_modEq (n := n) (a := j + s) hn0)

/-- The inverse of the shift `k ↦ (k + t) % n` on `range n`. -/
lemma pc_mod_add_sub {n k t : ℕ} (hn : 0 < n) (hk : k < n) (ht : t < n) :
    ((k + t) % n + n - t) % n = k := by
  rcases lt_or_ge (k + t) n with hlt | hge
  · have h1 : (k + t) % n = k + t := Nat.mod_eq_of_lt hlt
    rw [h1]
    have h2 : k + t + n - t = k + n := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
  · have hsplit : k + t = n + (k + t - n) := by omega
    have hlt : k + t - n < n := by omega
    have h1 : (k + t) % n = k + t - n := by
      have h0 : (n + (k + t - n)) % n = k + t - n := by
        rw [Nat.add_comm n (k + t - n), Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
      rwa [← hsplit] at h0
    rw [h1]
    have h2 : k + t - n + n - t = k := by omega
    rw [h2, Nat.mod_eq_of_lt hk]

/-- The other inverse of the shift `k ↦ (k + t) % n`: `(K + n - t) % n` shifted by `t` is `K`. -/
lemma pc_mod_sub_add {n K t : ℕ} (hn : 0 < n) (hK : K < n) (ht : t < n) :
    ((K + n - t) % n + t) % n = K := by
  rcases lt_or_ge K t with hlt | hle
  · have h1 : (K + n - t) % n = K + n - t := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have h2 : K + n - t + t = K + n := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hK]
  · have hsplit : K + n - t = n + (K - t) := by omega
    have hlt : K - t < n := by omega
    have h1 : (K + n - t) % n = K - t := by
      have h0 : (n + (K - t)) % n = K - t := by
        rw [Nat.add_comm n (K - t), Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
      rwa [← hsplit] at h0
    rw [h1]
    have h2 : K - t + t = K := by omega
    rw [h2, Nat.mod_eq_of_lt hK]

/-- Reindexing a double sum by the shift `(k,l) ↦ ((k+t) % n, (l+u) % n)` with `t, u < n`: the
shift is a bijection of `range n`, and `x ^ (2 ^ (k + t)) = x ^ (2 ^ ((k + t) % n))` in `𝔽_{2ⁿ}`
because `x ^ (2 ^ n) = x`. -/
lemma pc_shift_double {n : ℕ} (hn : 0 < n) {t u : ℕ} (ht : t < n) (hu : u < n)
    (F : ℕ → ℕ → GaloisField 2 n) :
    (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, F ((k + t) % n) ((l + u) % n))
      = ∑ K ∈ Finset.range n, ∑ L ∈ Finset.range n, F K L := by
  have hshiftt : ∀ (f : ℕ → GaloisField 2 n),
      (∑ k ∈ Finset.range n, f ((k + t) % n)) = ∑ K ∈ Finset.range n, f K := by
    intro f
    refine Finset.sum_nbij' (fun k => (k + t) % n) (fun K => (K + n - t) % n) ?_ ?_ ?_ ?_ ?_
    · intro k _; exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
    · intro K _; exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
    · intro k hk; exact pc_mod_add_sub hn (Finset.mem_range.mp hk) ht
    · intro K hK; exact pc_mod_sub_add hn (Finset.mem_range.mp hK) ht
    · intro k _; rfl
  have hshiftu : ∀ (f : ℕ → GaloisField 2 n),
      (∑ l ∈ Finset.range n, f ((l + u) % n)) = ∑ L ∈ Finset.range n, f L := by
    intro f
    refine Finset.sum_nbij' (fun l => (l + u) % n) (fun L => (L + n - u) % n) ?_ ?_ ?_ ?_ ?_
    · intro l _; exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
    · intro L _; exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
    · intro l hl; exact pc_mod_add_sub hn (Finset.mem_range.mp hl) hu
    · intro L hL; exact pc_mod_sub_add hn (Finset.mem_range.mp hL) hu
    · intro l _; rfl
  refine (hshiftt (fun K => ∑ l ∈ Finset.range n, F K ((l + u) % n))).trans ?_
  exact Finset.sum_congr rfl (fun K _ => hshiftu (F K))

lemma pc_sum_shift_reindex {n : ℕ} (hn : 0 < n) {t u : ℕ} (ht : t < n) (hu : u < n)
    (e : ℕ → ℕ → GaloisField 2 n) (α β : GaloisField 2 n) :
    (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        e k l * α ^ (2 ^ (k + t)) * β ^ (2 ^ (l + u)))
      = ∑ K ∈ Finset.range n, ∑ L ∈ Finset.range n,
          e ((K + n - t) % n) ((L + n - u) % n) * α ^ (2 ^ K) * β ^ (2 ^ L) := by
  have hn1 : 1 ≤ n := hn
  have h1 : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        e k l * α ^ (2 ^ (k + t)) * β ^ (2 ^ (l + u)))
      = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          e k l * α ^ (2 ^ ((k + t) % n)) * β ^ (2 ^ ((l + u) % n)) := by
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [pow_two_pow_mod hn1 α (k + t), pow_two_pow_mod hn1 β (l + u)]
  have h2 : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          e k l * α ^ (2 ^ ((k + t) % n)) * β ^ (2 ^ ((l + u) % n)))
      = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          (fun K L => e ((K + n - t) % n) ((L + n - u) % n) * α ^ (2 ^ K) * β ^ (2 ^ L))
            ((k + t) % n) ((l + u) % n) := by
    refine Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun l hl => ?_))
    show e k l * α ^ (2 ^ ((k + t) % n)) * β ^ (2 ^ ((l + u) % n))
      = e (((k + t) % n + n - t) % n) (((l + u) % n + n - u) % n) *
          α ^ (2 ^ ((k + t) % n)) * β ^ (2 ^ ((l + u) % n))
    rw [pc_mod_add_sub hn (Finset.mem_range.mp hk) ht,
      pc_mod_add_sub hn (Finset.mem_range.mp hl) hu]
  rw [h1, h2, pc_shift_double hn ht hu
    (fun K L => e ((K + n - t) % n) ((L + n - u) % n) * α ^ (2 ^ K) * β ^ (2 ^ L))]

/-- Diagonal rescaling of a canonical squaring form. -/
lemma pc_scale_form {n : ℕ} {Q : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n}
    {Φ : GaloisField 2 n × GaloisField 2 n ≃+ GaloisField 2 n × GaloisField 2 n}
    {C₁ C₂ : GaloisField 2 n} {p q : ℕ} {g₁ : ℕ → ℕ → GaloisField 2 n}
    (h : ∀ γ δ, Q (Φ (γ, δ)) = C₁ * γ ^ (1 + 2 ^ p) + C₂ * δ ^ (1 + 2 ^ q) +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g₁ k l * γ ^ (2 ^ k) * δ ^ (2 ^ l))
    {c c' : GaloisField 2 n} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    ∃ (Φe : GaloisField 2 n × GaloisField 2 n ≃+ GaloisField 2 n × GaloisField 2 n)
      (g : ℕ → ℕ → GaloisField 2 n),
      (∀ α β, Q (Φe (α, β)) = (C₁ * c ^ (1 + 2 ^ p)) * α ^ (1 + 2 ^ p) +
          (C₂ * c' ^ (1 + 2 ^ q)) * β ^ (1 + 2 ^ q) +
          ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l)) ∧
      (∀ k l, g k l = g₁ k l * c ^ (2 ^ k) * c' ^ (2 ^ l)) := by
  refine ⟨(AddEquiv.prodCongr (mulLeftAddEquiv c hc) (mulLeftAddEquiv c' hc')).trans Φ,
    fun k l => g₁ k l * c ^ (2 ^ k) * c' ^ (2 ^ l), ?_, fun k l => rfl⟩
  intro α β
  have happ : ((AddEquiv.prodCongr (mulLeftAddEquiv c hc)
      (mulLeftAddEquiv c' hc')).trans Φ) (α, β) = Φ (c * α, c' * β) := rfl
  rw [happ, h (c * α) (c' * β)]
  have hd1 : C₁ * (c * α) ^ (1 + 2 ^ p) = (C₁ * c ^ (1 + 2 ^ p)) * α ^ (1 + 2 ^ p) := by
    rw [mul_pow]; ring
  have hd2 : C₂ * (c' * β) ^ (1 + 2 ^ q) = (C₂ * c' ^ (1 + 2 ^ q)) * β ^ (1 + 2 ^ q) := by
    rw [mul_pow]; ring
  have hs : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        g₁ k l * (c * α) ^ (2 ^ k) * (c' * β) ^ (2 ^ l))
      = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          (g₁ k l * c ^ (2 ^ k) * c' ^ (2 ^ l)) * α ^ (2 ^ k) * β ^ (2 ^ l) := by
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [mul_pow, mul_pow]; ring
  rw [hd1, hd2, hs]

/-! ## The Frobenius twist putting the pinned form into canonical shape -/

/-- **The twist.**  Given the pinned form `Q (α,β) = C α^a + C' β^{a'} + Σ e k l α^{2^k}β^{2^l}`
with axis exponents `a ≡ 2^j (1 + 2^r)`, `a' ≡ 2^{j'} (1 + 2^s)`, the Frobenius twist
`Φe (α,β) = (α^{2^t}, β^{2^u})` (where `t ≡ -j`, `u ≡ -j'` mod `n`) puts the form into the
canonical shape `C α^{1+2^r} + C' β^{1+2^s} + Σ g k l α^{2^k}β^{2^l}`, with the coefficient
function `g k l = e ((k + n - t) % n) ((l + n - u) % n)`.

The congruence (★) `(1+2^s)·2^k + (1+2^r)·2^l ≡ (1+2^r)(1+2^s)` for the support of `g` follows
from the resonance by raising to the power `a·a'`; the coprimalities follow from those of `a`
and `a'`; the nonemptiness of the support is `support_nonempty`. -/
theorem pc_canonical_axis {n : ℕ} (hn : 2 ≤ n)
    {Q : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n}
    {lam : (GaloisField 2 n)ˣ} (hlam : orderOf lam = 2 ^ n - 1)
    {a a' : ℕ} (ha1 : 1 ≤ a) (ha'1 : 1 ≤ a')
    {ν ν' : (GaloisField 2 n)ˣ}
    (haν : (ν : GaloisField 2 n) ^ a = (lam : GaloisField 2 n))
    (ha'ν' : (ν' : GaloisField 2 n) ^ a' = (lam : GaloisField 2 n))
    {C C' : GaloisField 2 n} (hC : C ≠ 0) (hC' : C' ≠ 0)
    {e : ℕ → ℕ → GaloisField 2 n}
    (hres : ∀ k l : ℕ, e k l ≠ 0 →
      (ν : GaloisField 2 n) ^ (2 ^ k) * (ν' : GaloisField 2 n) ^ (2 ^ l) =
        (lam : GaloisField 2 n))
    (hform : ∀ α β : GaloisField 2 n,
      Q (α, β) = C * α ^ a + C' * β ^ a' +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, e k l * α ^ (2 ^ k) * β ^ (2 ^ l))
    (hanis : ∀ v : GaloisField 2 n × GaloisField 2 n, v ≠ 0 → Q v ≠ 0)
    {j r j' s : ℕ} (hj : j < n) (hr : r < n) (hj' : j' < n) (hs : s < n)
    (haj : a ≡ 2 ^ j * (1 + 2 ^ r) [MOD 2 ^ n - 1])
    (ha'j' : a' ≡ 2 ^ j' * (1 + 2 ^ s) [MOD 2 ^ n - 1])
    (hcopa : Nat.Coprime a (2 ^ n - 1)) (hcopa' : Nat.Coprime a' (2 ^ n - 1)) :
    ∃ (g : ℕ → ℕ → GaloisField 2 n)
      (Φe : GaloisField 2 n × GaloisField 2 n ≃+ GaloisField 2 n × GaloisField 2 n),
      (∀ α β : GaloisField 2 n,
        Q (Φe (α, β)) = C * α ^ (1 + 2 ^ r) + C' * β ^ (1 + 2 ^ s) +
          ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l)) ∧
      (∀ k l : ℕ, k < n → l < n → g k l ≠ 0 →
        (1 + 2 ^ s) * 2 ^ k + (1 + 2 ^ r) * 2 ^ l ≡ (1 + 2 ^ r) * (1 + 2 ^ s)
          [MOD 2 ^ n - 1]) ∧
      (∃ k l : ℕ, k < n ∧ l < n ∧ g k l ≠ 0) ∧
      Nat.Coprime (1 + 2 ^ r) (2 ^ n - 1) ∧ Nat.Coprime (1 + 2 ^ s) (2 ^ n - 1) := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hMpos : 0 < 2 ^ n - 1 := by
    have h2n : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  -- the twist exponents
  let t : ℕ := (n - j) % n
  let u : ℕ := (n - j') % n
  have ht_lt : t < n := Nat.mod_lt _ hn0
  have hu_lt : u < n := Nat.mod_lt _ hn0
  have htj : (t + j) % n = 0 := by
    show ((n - j) % n + j) % n = 0
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; simp [Nat.mod_self]
    · have h1 : (n - j) % n = n - j := Nat.mod_eq_of_lt (by omega)
      rw [h1, Nat.sub_add_cancel (by omega), Nat.mod_self]
  have huj : (u + j') % n = 0 := by
    show ((n - j') % n + j') % n = 0
    rcases Nat.eq_zero_or_pos j' with hj0 | hjpos
    · subst hj0; simp [Nat.mod_self]
    · have h1 : (n - j') % n = n - j' := Nat.mod_eq_of_lt (by omega)
      rw [h1, Nat.sub_add_cancel (by omega), Nat.mod_self]
  have h2r : 2 ^ t * a ≡ 1 + 2 ^ r [MOD 2 ^ n - 1] := pc_two_pow_mul_modEq hn1 haj htj
  have h2s : 2 ^ u * a' ≡ 1 + 2 ^ s [MOD 2 ^ n - 1] := pc_two_pow_mul_modEq hn1 ha'j' huj
  have hcopr : Nat.Coprime (1 + 2 ^ r) (2 ^ n - 1) :=
    pc_coprime_one_add_two_pow hn1 haj hcopa
  have hcops : Nat.Coprime (1 + 2 ^ s) (2 ^ n - 1) :=
    pc_coprime_one_add_two_pow hn1 ha'j' hcopa'
  -- the twist and the new coefficient function
  let Φe : GaloisField 2 n × GaloisField 2 n ≃+ GaloisField 2 n × GaloisField 2 n :=
    AddEquiv.prodCongr ((frob n ^ t : GaloisField 2 n ≃+* GaloisField 2 n)).toAddEquiv
      ((frob n ^ u : GaloisField 2 n ≃+* GaloisField 2 n)).toAddEquiv
  let g : ℕ → ℕ → GaloisField 2 n := fun K L => e ((K + n - t) % n) ((L + n - u) % n)
  have hΦe : ∀ α β : GaloisField 2 n, Φe (α, β) = (α ^ (2 ^ t), β ^ (2 ^ u)) := by
    intro α β
    have h1 : Φe (α, β) = ((frob n ^ t : GaloisField 2 n ≃+* GaloisField 2 n) α,
        (frob n ^ u : GaloisField 2 n ≃+* GaloisField 2 n) β) := rfl
    rw [h1, frob_pow_apply, frob_pow_apply]
  have hshape : ∀ α β : GaloisField 2 n,
      Q (Φe (α, β)) = C * α ^ (1 + 2 ^ r) + C' * β ^ (1 + 2 ^ s) +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l) := by
    intro α β
    rw [hΦe α β, hform (α ^ (2 ^ t)) (β ^ (2 ^ u))]
    have hd1 : (α ^ (2 ^ t)) ^ a = α ^ (1 + 2 ^ r) := by
      rw [← pow_mul]
      refine pc_pow_eq_of_modEq hn1 (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
          (Nat.one_le_iff_ne_zero.mp ha1))) (Nat.le_add_right 1 (2 ^ r)) h2r
    have hd2 : (β ^ (2 ^ u)) ^ a' = β ^ (1 + 2 ^ s) := by
      rw [← pow_mul]
      refine pc_pow_eq_of_modEq hn1 (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
          (Nat.one_le_iff_ne_zero.mp ha'1))) (Nat.le_add_right 1 (2 ^ s)) h2s
    have hs : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          e k l * (α ^ (2 ^ t)) ^ (2 ^ k) * (β ^ (2 ^ u)) ^ (2 ^ l))
        = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
            g k l * α ^ (2 ^ k) * β ^ (2 ^ l) := by
      have hcongr : ∀ k l : ℕ,
          e k l * (α ^ (2 ^ t)) ^ (2 ^ k) * (β ^ (2 ^ u)) ^ (2 ^ l)
            = e k l * α ^ (2 ^ (k + t)) * β ^ (2 ^ (l + u)) := by
        intro k l
        rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, Nat.add_comm t k, Nat.add_comm u l]
      rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => hcongr k l))]
      exact pc_sum_shift_reindex hn0 ht_lt hu_lt e α β
    rw [hd1, hd2, hs]
  have hresg : ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 →
      (1 + 2 ^ s) * 2 ^ k + (1 + 2 ^ r) * 2 ^ l ≡ (1 + 2 ^ r) * (1 + 2 ^ s)
        [MOD 2 ^ n - 1] := by
    intro k l hk hl hgkl
    have hres' : (ν : GaloisField 2 n) ^ (2 ^ ((k + n - t) % n)) *
        (ν' : GaloisField 2 n) ^ (2 ^ ((l + n - u) % n)) = (lam : GaloisField 2 n) :=
      hres _ _ hgkl
    have h1 : a' * 2 ^ ((k + n - t) % n) + a * 2 ^ ((l + n - u) % n) ≡ a * a'
        [MOD 2 ^ n - 1] := by
      have hfin : IsOfFinOrder (lam : GaloisField 2 n) :=
        orderOf_ne_zero_iff.mp (by rw [orderOf_units, hlam]; exact ne_of_gt hMpos)
      have key : (lam : GaloisField 2 n) ^ (a' * 2 ^ ((k + n - t) % n) +
            a * 2 ^ ((l + n - u) % n)) = (lam : GaloisField 2 n) ^ (a * a') := by
        have hstep := congrArg (fun z : GaloisField 2 n => z ^ (a * a')) hres'
        rw [mul_pow] at hstep
        have e1 : ((ν : GaloisField 2 n) ^ (2 ^ ((k + n - t) % n))) ^ (a * a') =
            (lam : GaloisField 2 n) ^ (a' * 2 ^ ((k + n - t) % n)) := by
          have h2 : ((ν : GaloisField 2 n) ^ (2 ^ ((k + n - t) % n))) ^ (a * a') =
              ((ν : GaloisField 2 n) ^ a) ^ (a' * 2 ^ ((k + n - t) % n)) := by
            rw [← pow_mul, ← pow_mul]; congr 1; ac_rfl
          rw [h2, haν]
        have e2 : ((ν' : GaloisField 2 n) ^ (2 ^ ((l + n - u) % n))) ^ (a * a') =
            (lam : GaloisField 2 n) ^ (a * 2 ^ ((l + n - u) % n)) := by
          have h2 : ((ν' : GaloisField 2 n) ^ (2 ^ ((l + n - u) % n))) ^ (a * a') =
              ((ν' : GaloisField 2 n) ^ a') ^ (a * 2 ^ ((l + n - u) % n)) := by
            rw [← pow_mul, ← pow_mul]; congr 1; ac_rfl
          rw [h2, ha'ν']
        rw [e1, e2, ← pow_add] at hstep
        exact hstep
      have hmod := hfin.pow_eq_pow_iff_modEq.mp key
      rw [orderOf_units, hlam] at hmod
      exact hmod
    have hkt : (((k + n - t) % n) + t) % n = k := pc_mod_sub_add hn0 hk ht_lt
    have hlu : (((l + n - u) % n) + u) % n = l := pc_mod_sub_add hn0 hl hu_lt
    exact pc_resonance_modEq hn1 h1 h2r h2s hkt hlu
  have hsupp : ∃ k l : ℕ, k < n ∧ l < n ∧ g k l ≠ 0 := by
    refine support_nonempty (s := s) hn hr hC hC' hcopr ?_
    intro α β hne
    rw [← hshape α β]
    exact aniso_comp hanis (α, β) hne
  exact ⟨g, Φe, hshape, hresg, hsupp, hcopr, hcops⟩

/-- **The twisted (swapped) case.**  When the second axis exponent `a' ≡ 2^{j'}(1+2^s)` is
non-abelian (`s ≠ 0`) while the first one is abelian (`a ≡ 2^j · 2`), one applies the previous
theorem to the *swapped* form (exchanging the two coordinates, which exchanges the roles of
`a, ν, C` with `a', ν', C'`) and then rescales the coordinates by `c`, `c'` with
`C' c^{1+2^s} = C` and `C c'^2 = C'` (possible by `pow_surjective`).  The result is the
canonical form with `(r, s) = (s, 0)`, i.e. `C α^{1+2^s} + C' β^2 + Σ g k l α^{2^k}β^{2^l}`. -/
theorem pc_canonical_axis_swap {n : ℕ} (hn : 2 ≤ n)
    {Q : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n}
    {lam : (GaloisField 2 n)ˣ} (hlam : orderOf lam = 2 ^ n - 1)
    {a a' : ℕ} (ha1 : 1 ≤ a) (ha'1 : 1 ≤ a')
    {ν ν' : (GaloisField 2 n)ˣ}
    (haν : (ν : GaloisField 2 n) ^ a = (lam : GaloisField 2 n))
    (ha'ν' : (ν' : GaloisField 2 n) ^ a' = (lam : GaloisField 2 n))
    {C C' : GaloisField 2 n} (hC : C ≠ 0) (hC' : C' ≠ 0)
    {e : ℕ → ℕ → GaloisField 2 n}
    (hres : ∀ k l : ℕ, e k l ≠ 0 →
      (ν : GaloisField 2 n) ^ (2 ^ k) * (ν' : GaloisField 2 n) ^ (2 ^ l) =
        (lam : GaloisField 2 n))
    (hform : ∀ α β : GaloisField 2 n,
      Q (α, β) = C * α ^ a + C' * β ^ a' +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, e k l * α ^ (2 ^ k) * β ^ (2 ^ l))
    (hanis : ∀ v : GaloisField 2 n × GaloisField 2 n, v ≠ 0 → Q v ≠ 0)
    {j j' s : ℕ} (hj : j < n) (hj' : j' < n) (hs : s < n)
    (haj : a ≡ 2 ^ j * (1 + 2 ^ 0) [MOD 2 ^ n - 1])
    (ha'j' : a' ≡ 2 ^ j' * (1 + 2 ^ s) [MOD 2 ^ n - 1])
    (hcopa : Nat.Coprime a (2 ^ n - 1)) (hcopa' : Nat.Coprime a' (2 ^ n - 1)) :
    ∃ (g : ℕ → ℕ → GaloisField 2 n)
      (Φe : GaloisField 2 n × GaloisField 2 n ≃+ GaloisField 2 n × GaloisField 2 n),
      (∀ α β : GaloisField 2 n,
        Q (Φe (α, β)) = C * α ^ (1 + 2 ^ s) + C' * β ^ (1 + 2 ^ 0) +
          ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l)) ∧
      (∀ k l : ℕ, k < n → l < n → g k l ≠ 0 →
        (1 + 2 ^ 0) * 2 ^ k + (1 + 2 ^ s) * 2 ^ l ≡ (1 + 2 ^ s) * (1 + 2 ^ 0)
          [MOD 2 ^ n - 1]) ∧
      (∃ k l : ℕ, k < n ∧ l < n ∧ g k l ≠ 0) ∧
      Nat.Coprime (1 + 2 ^ s) (2 ^ n - 1) ∧ Nat.Coprime (1 + 2 ^ 0) (2 ^ n - 1) := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hCq : C * (C'⁻¹) ≠ 0 := mul_ne_zero hC (inv_ne_zero hC')
  have hC'q : C' * C⁻¹ ≠ 0 := mul_ne_zero hC' (inv_ne_zero hC)
  -- the swapped data
  let ê : ℕ → ℕ → GaloisField 2 n := fun k l => e l k
  let Q1 : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n :=
    fun v => Q (v.2, v.1)
  have hform1 : ∀ α β : GaloisField 2 n,
      Q1 (α, β) = C' * α ^ a' + C * β ^ a +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, ê k l * α ^ (2 ^ k) * β ^ (2 ^ l) := by
    intro α β
    have h := hform β α
    have hsum : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          e k l * β ^ (2 ^ k) * α ^ (2 ^ l))
        = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
            ê k l * α ^ (2 ^ k) * β ^ (2 ^ l) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      show e l k * β ^ (2 ^ l) * α ^ (2 ^ k) = e l k * α ^ (2 ^ k) * β ^ (2 ^ l)
      ring
    show Q (β, α) = C' * α ^ a' + C * β ^ a + _
    rw [h, hsum]
    ring
  have hres1 : ∀ k l : ℕ, ê k l ≠ 0 →
      (ν' : GaloisField 2 n) ^ (2 ^ k) * (ν : GaloisField 2 n) ^ (2 ^ l) =
        (lam : GaloisField 2 n) := by
    intro k l h
    have h' : e l k ≠ 0 := h
    have hkl := hres l k h'
    rwa [mul_comm] at hkl
  have hanis1 : ∀ v : GaloisField 2 n × GaloisField 2 n, v ≠ 0 → Q1 v ≠ 0 := by
    rintro ⟨α, β⟩ hv
    have h1 : (β, α) ≠ 0 := by
      intro h0
      refine hv ?_
      rw [Prod.ext_iff] at h0 ⊢
      exact ⟨h0.2, h0.1⟩
    exact hanis (β, α) h1
  obtain ⟨g₁, Φ₁, hshape₁, hresg₁, hsupp₁, hcopr₁, hcops₁⟩ :=
    pc_canonical_axis (n := n) (hn := hn) (Q := Q1) (lam := lam) (hlam := hlam)
      (a := a') (a' := a) (ha1 := ha'1) (ha'1 := ha1) (ν := ν') (ν' := ν)
      (haν := ha'ν') (ha'ν' := haν) (C := C') (C' := C) (hC := hC') (hC' := hC)
      (e := ê) (hres := hres1) (hform := hform1) (hanis := hanis1)
      (j := j') (r := s) (j' := j) (s := 0)
      (hj := hj') (hr := hs) (hj' := hj) (hs := hn0)
      (haj := ha'j') (ha'j' := haj) (hcopa := hcopa') (hcopa' := hcopa)
  -- the rescaling
  obtain ⟨c, hc_eq⟩ := pow_surjective hn0 (by norm_num : 0 < 1 + 2 ^ s) hcopr₁ (C * C'⁻¹)
  obtain ⟨c', hc'_eq⟩ := pow_surjective hn0 (by norm_num : 0 < 1 + 2 ^ 0)
    (by simpa using hcops₁) (C' * C⁻¹)
  have hcne : c ≠ 0 := by
    intro h0
    exact hCq (by rw [← hc_eq, h0, zero_pow (Nat.pos_iff_ne_zero.mp
      (by positivity : 0 < 1 + 2 ^ s))])
  have hc'ne : c' ≠ 0 := by
    intro h0
    exact hC'q (by rw [← hc'_eq, h0, zero_pow (Nat.pos_iff_ne_zero.mp
      (by positivity : 0 < 1 + 2 ^ 0))])
  have hC1 : C' * c ^ (1 + 2 ^ s) = C := by
    rw [hc_eq, mul_comm C' (C * C'⁻¹), mul_assoc, inv_mul_cancel₀ hC', mul_one]
  have hC2 : C * c' ^ (1 + 2 ^ 0) = C' := by
    rw [hc'_eq, mul_comm C (C' * C⁻¹), mul_assoc, inv_mul_cancel₀ hC, mul_one]
  obtain ⟨Φe₂, g₂, hshape₂, hg₂⟩ :=
    pc_scale_form (n := n) (Q := Q1) (Φ := Φ₁) (C₁ := C') (C₂ := C) (p := s) (q := 0)
      (g₁ := g₁) hshape₁ hcne hc'ne
  refine ⟨g₂, Φe₂.trans (AddEquiv.prodComm), ?_, ?_, ?_, ?_, ?_⟩
  · intro α β
    have h := hshape₂ α β
    rw [hC1, hC2] at h
    change Q (AddEquiv.prodComm (Φe₂ (α, β))) =
      C * α ^ (1 + 2 ^ s) + C' * β ^ (1 + 2 ^ 0) +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g₂ k l * α ^ (2 ^ k) * β ^ (2 ^ l)
    exact h
  · intro k l hk hl hgkl
    have hg₁ : g₁ k l ≠ 0 := by
      intro h0
      exact hgkl (by rw [hg₂ k l, h0, zero_mul, zero_mul])
    exact hresg₁ k l hk hl hg₁
  · obtain ⟨k, l, hk, hl, hne⟩ := hsupp₁
    refine ⟨k, l, hk, hl, fun h0 => hne ?_⟩
    have h := hg₂ k l
    rw [h0] at h
    have h1 : g₁ k l * c ^ (2 ^ k) = 0 :=
      (mul_eq_zero.mp h.symm).resolve_right (pow_ne_zero _ hc'ne)
    exact (mul_eq_zero.mp h1).resolve_right (pow_ne_zero _ hcne)
  · exact hcopr₁
  · simpa using hcops₁

/-- **Normalisation of the pinned squaring form** (Higman Lemma 12, the outer bookkeeping).

`Submission/Work/Higman/Q3/L12/NOTES_PROGRESS.md` §2–§3 has the full recipe.  Summary: with
`𝔽 = 𝔽_{2ⁿ}`, `M = 2ⁿ - 1`:

* `axis_type_exponents` (with `hax`/`haν`, `hax'`/`ha'ν'`) gives `a ≡ 2^j (1 + 2^r)`,
  `a' ≡ 2^{j'} (1 + 2^s)` with `r, s < n` (use `(ν : 𝔽)`, `(ν' : 𝔽)`, and the order equality
  `orderOf (↑u) = orderOf u` for units);
* `ν^a = lam` with `orderOf ν = orderOf lam = M` gives `Nat.gcd a M = 1`, whence
  `Nat.Coprime (1 + 2^r) M` (and the same for `s`);
* the resonance `e k l ≠ 0 → ν^{2^k} ν'^{2^l} = lam` is *equivalent* (raise to the power `a * a'`)
  to `a' * 2^k + a * 2^l ≡ a * a' [MOD M]`;
* twisting `Φe = (α ↦ α^(2^t)) × (β ↦ β^(2^u))` with `t ≡ -j`, `u ≡ -j'` (mod `n`), using
  `pow_two_pow_mod` and `pow_eq_of_modEq` to convert `α ^ (2^t * a)` into `α ^ (1 + 2^r)`
  (`2^t * a ≡ 1 + 2^r [MOD M]`, from `2^t * 2^j ≡ 1`), reindexes the double sum by the bijection
  `(k,l) ↦ ((k+t)%n, (l+u)%n)` (`Finset.sum_bij`), giving the new coefficient
  `g k l = e ((k + n - t) % n) ((l + n - u) % n)` and the congruence (★);
* the support of `g` is nonempty: otherwise `C α^{1+2^r} + C' β^{1+2^s}` would vanish at
  `(α, 1)` for the `α ≠ 0` with `C α^{1+2^r} = C'` (existence from `Nat.Coprime (1+2^r) M`);
* finally choose the representatives: if `r ≠ 0`, `s ≠ 0`, `r ≡ -s` but `r ≠ s`, replace `s` by
  `n - s` and `j'` by `j' + s` (using `2^{j'}(1+2^s) ≡ 2^{j'+s}(1+2^{n-s})`) — this makes `r = s`;
  if `r = 0` and `s ≠ 0`, compose `Φe` with the coordinate swap **and a rescaling**
  `α ↦ c α`, `β ↦ c' β` with `c^{1+2^s} = C/C'`, `c'^2 = C'/C` (`c` exists since
  `Nat.Coprime (1+2^s) M`), which turns the shape into `C α^{1+2^s} + C' β^2 + …`. -/
theorem pinned_canonical {n : ℕ} (hn : 2 ≤ n)
    {V W : Type*} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    {b : V → V → W} [Biadd b]
    (φ : V ≃+ (GaloisField 2 n × GaloisField 2 n)) (ψ : W ≃+ GaloisField 2 n)
    {ν ν' lam : (GaloisField 2 n)ˣ}
    (hν : orderOf ν = 2 ^ n - 1) (hν' : orderOf ν' = 2 ^ n - 1) (hlam : orderOf lam = 2 ^ n - 1)
    {a a' : ℕ} (ha1 : 1 ≤ a) (haq : a ≤ 2 ^ n - 1) (ha'1 : 1 ≤ a') (ha'q : a' ≤ 2 ^ n - 1)
    (haν : (ν : GaloisField 2 n) ^ a = (lam : GaloisField 2 n))
    (ha'ν' : (ν' : GaloisField 2 n) ^ a' = (lam : GaloisField 2 n))
    (hax : ∃ i j : ℕ, i < n ∧ j < n ∧
      (ν : GaloisField 2 n) ^ (2 ^ i) * (ν : GaloisField 2 n) ^ (2 ^ j) = (lam : GaloisField 2 n))
    (hax' : ∃ i j : ℕ, i < n ∧ j < n ∧
      (ν' : GaloisField 2 n) ^ (2 ^ i) * (ν' : GaloisField 2 n) ^ (2 ^ j) = (lam : GaloisField 2 n))
    {C C' : GaloisField 2 n} (hC : C ≠ 0) (hC' : C' ≠ 0) {e : ℕ → ℕ → GaloisField 2 n}
    (hres : ∀ k l : ℕ, e k l ≠ 0 →
      (ν : GaloisField 2 n) ^ (2 ^ k) * (ν' : GaloisField 2 n) ^ (2 ^ l) = (lam : GaloisField 2 n))
    (hform : ∀ α β : GaloisField 2 n,
      ψ (b (φ.symm (α, β)) (φ.symm (α, β))) = C * α ^ a + C' * β ^ a' +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, e k l * α ^ (2 ^ k) * β ^ (2 ^ l))
    (hanis : ∀ α β : GaloisField 2 n, (α, β) ≠ 0 →
      C * α ^ a + C' * β ^ a' +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, e k l * α ^ (2 ^ k) * β ^ (2 ^ l) ≠ 0) :
    ∃ (r s : ℕ) (Φe : GaloisField 2 n × GaloisField 2 n ≃+ GaloisField 2 n × GaloisField 2 n)
      (g : ℕ → ℕ → GaloisField 2 n),
      r < n ∧ s < n ∧
      (∀ α β : GaloisField 2 n,
        ψ (b (φ.symm (Φe (α, β))) (φ.symm (Φe (α, β)))) =
          C * α ^ (1 + 2 ^ r) + C' * β ^ (1 + 2 ^ s) +
            ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l)) ∧
      (∀ k l : ℕ, k < n → l < n → g k l ≠ 0 →
        (1 + 2 ^ s) * 2 ^ k + (1 + 2 ^ r) * 2 ^ l ≡ (1 + 2 ^ r) * (1 + 2 ^ s)
          [MOD 2 ^ n - 1]) ∧
      (∃ k l : ℕ, k < n ∧ l < n ∧ g k l ≠ 0) ∧
      Nat.Coprime (1 + 2 ^ r) (2 ^ n - 1) ∧ Nat.Coprime (1 + 2 ^ s) (2 ^ n - 1) ∧
      ((r = 0 ∧ s = 0) ∨ (r = s ∧ r ≠ 0) ∨ (r ≠ 0 ∧ s = 0) ∨
        (r ≠ 0 ∧ s ≠ 0 ∧ (r + s) % n ≠ 0 ∧ (r + n - s) % n ≠ 0)) := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hMpos : 0 < 2 ^ n - 1 := by
    have h2n : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  -- the squaring form and its anisotropy, in terms of `Q`
  let Q : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n :=
    fun v => ψ (b (φ.symm v) (φ.symm v))
  have hformQ : ∀ α β : GaloisField 2 n,
      Q (α, β) = C * α ^ a + C' * β ^ a' +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, e k l * α ^ (2 ^ k) * β ^ (2 ^ l) :=
    fun α β => hform α β
  have haniQ : ∀ v : GaloisField 2 n × GaloisField 2 n, v ≠ 0 → Q v ≠ 0 := by
    rintro ⟨α, β⟩ hv
    rw [hformQ α β]
    exact hanis α β (by simpa using hv)
  -- the axis exponents of `a` and `a'`
  have hνco : orderOf (ν : GaloisField 2 n) = 2 ^ n - 1 := by rw [orderOf_units]; exact hν
  have hν'co : orderOf (ν' : GaloisField 2 n) = 2 ^ n - 1 := by rw [orderOf_units]; exact hν'
  have haxp : ∃ i j : ℕ, i < n ∧ j < n ∧
      (ν : GaloisField 2 n) ^ (2 ^ i) * (ν : GaloisField 2 n) ^ (2 ^ j) =
        (ν : GaloisField 2 n) ^ a := by
    obtain ⟨i, j, hi, hj, h⟩ := hax
    exact ⟨i, j, hi, hj, by rw [h, haν]⟩
  have hax'p : ∃ i j : ℕ, i < n ∧ j < n ∧
      (ν' : GaloisField 2 n) ^ (2 ^ i) * (ν' : GaloisField 2 n) ^ (2 ^ j) =
        (ν' : GaloisField 2 n) ^ a' := by
    obtain ⟨i, j, hi, hj, h⟩ := hax'
    exact ⟨i, j, hi, hj, by rw [h, ha'ν']⟩
  obtain ⟨j, r, hj, hr, haj⟩ :=
    axis_type_exponents hn1 (Units.ne_zero ν) hνco ha1 haq haxp
  obtain ⟨j', s, hj', hs, ha'j'⟩ :=
    axis_type_exponents hn1 (Units.ne_zero ν') hν'co ha'1 ha'q hax'p
  -- coprimalities
  have hcopa : Nat.Coprime a (2 ^ n - 1) :=
    pc_coprime_of_orderOf_pow_eq hMpos hν hlam
      (Units.ext (by rw [Units.val_pow_eq_pow_val, haν]))
  have hcopa' : Nat.Coprime a' (2 ^ n - 1) :=
    pc_coprime_of_orderOf_pow_eq hMpos hν' hlam
      (Units.ext (by rw [Units.val_pow_eq_pow_val, ha'ν']))
  rcases eq_or_ne r 0 with hr0 | hr0
  · -- the first axis is abelian
    subst hr0
    rcases eq_or_ne s 0 with hs0 | hs0
    · -- `r = 0`, `s = 0`
      subst hs0
      obtain ⟨g, Φe, hshape, hresg, hsupp, hc1, hc2⟩ :=
        pc_canonical_axis hn hlam ha1 ha'1 haν ha'ν' hC hC' hres hformQ haniQ
          hj hr hj' hs haj ha'j' hcopa hcopa'
      exact ⟨0, 0, Φe, g, hn0, hn0, hshape, hresg, hsupp, hc1, hc2, Or.inl ⟨rfl, rfl⟩⟩
    · -- `r = 0`, `s ≠ 0`: swap the coordinates and rescale
      obtain ⟨g, Φe, hshape, hresg, hsupp, hc1, hc2⟩ :=
        pc_canonical_axis_swap hn hlam ha1 ha'1 haν ha'ν' hC hC' hres hformQ haniQ
          hj hj' hs haj ha'j' hcopa hcopa'
      exact ⟨s, 0, Φe, g, hs, hn0, hshape, hresg, hsupp, hc1, hc2,
        Or.inr (Or.inr (Or.inl ⟨hs0, rfl⟩))⟩
  · rcases eq_or_ne s 0 with hs0 | hs0
    · -- `r ≠ 0`, `s = 0`
      subst hs0
      obtain ⟨g, Φe, hshape, hresg, hsupp, hc1, hc2⟩ :=
        pc_canonical_axis hn hlam ha1 ha'1 haν ha'ν' hC hC' hres hformQ haniQ
          hj hr hj' hs haj ha'j' hcopa hcopa'
      exact ⟨r, 0, Φe, g, hr, hn0, hshape, hresg, hsupp, hc1, hc2,
        Or.inr (Or.inr (Or.inl ⟨hr0, rfl⟩))⟩
    · rcases eq_or_ne r s with hrs | hrs
      · -- `r = s ≠ 0`
        obtain ⟨g, Φe, hshape, hresg, hsupp, hc1, hc2⟩ :=
          pc_canonical_axis hn hlam ha1 ha'1 haν ha'ν' hC hC' hres hformQ haniQ
            hj hr hj' hs haj ha'j' hcopa hcopa'
        exact ⟨r, s, Φe, g, hr, hs, hshape, hresg, hsupp, hc1, hc2,
          Or.inr (Or.inl ⟨hrs, hr0⟩)⟩
      · by_cases hsum : (r + s) % n = 0
        · -- `r + s = n`: replace `s` by `n - s = r`
          have hrsn : r + s = n :=
            eq_of_modEq_zero_of_pos_of_lt (n := n) (a := r + s) (by omega) (by omega) (by
              show (r + s) % n = 0 % n
              rw [hsum, Nat.zero_mod])
          have hns : r = n - s := by omega
          have hj'' : (j' + s) % n < n := Nat.mod_lt _ hn0
          have ha'j'' : a' ≡ 2 ^ ((j' + s) % n) * (1 + 2 ^ (n - s)) [MOD 2 ^ n - 1] :=
            ha'j'.trans (pc_axis_rebase hn1 hs)
          obtain ⟨g, Φe, hshape, hresg, hsupp, hc1, hc2⟩ :=
            pc_canonical_axis hn hlam ha1 ha'1 haν ha'ν' hC hC' hres hformQ haniQ
              hj hr hj'' (by omega) haj ha'j'' hcopa hcopa'
          exact ⟨r, n - s, Φe, g, hr, by omega, hshape, hresg, hsupp, hc1, hc2,
            Or.inr (Or.inl ⟨hns, hr0⟩)⟩
        · -- `r, s ≠ 0`, `r ≢ ±s`
          have hdiff : (r + n - s) % n ≠ 0 := by
            intro h0
            have hmod : r + n - s ≡ 0 [MOD n] := by
              show (r + n - s) % n = 0 % n
              rw [h0, Nat.zero_mod]
            have hEq : r + n - s = n :=
              eq_of_modEq_zero_of_pos_of_lt (n := n) (a := r + n - s)
                (by omega) (by omega) hmod
            omega
          obtain ⟨g, Φe, hshape, hresg, hsupp, hc1, hc2⟩ :=
            pc_canonical_axis hn hlam ha1 ha'1 haν ha'ν' hC hC' hres hformQ haniQ
              hj hr hj' hs haj ha'j' hcopa hcopa'
          exact ⟨r, s, Φe, g, hr, hs, hshape, hresg, hsupp, hc1, hc2,
            Or.inr (Or.inr (Or.inr ⟨hr0, hs0, hsum, hdiff⟩))⟩

end Work.Higman.Q3.L12
