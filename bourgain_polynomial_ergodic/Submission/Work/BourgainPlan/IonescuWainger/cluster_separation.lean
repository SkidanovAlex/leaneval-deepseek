import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ZModArcs
import Submission.Work.BourgainPlan.IonescuWainger.sigmaCompDecompSetQ_card_le

/-!
# Separation of the Ionescu–Wainger clusters

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4
(theorem `ortho-apply`), in the finite cyclic group formulation of `ZModArcs.lean`.

For a finite set `S` of pairwise coprime integers `≥ 2` and `A₀ ⊆ S`, the major arcs of order `≤ k`
cluster around the rational points of exact denominator `Q_{A₀}`: the *core* `Σ_{A₀}`
(`sigmaAQ (QA S) A₀`) and the *petals* `Σ_{(A₀)} = ⋃_{A ⊆ S∖A₀, |A| ≤ k−|A₀|} Σ_A`
(`sigmaCompQ (QA S) S k A₀`).

The characteristic feature of a cluster, needed both for the `ℓ²` clustering bound of
`ortho-apply`(i) and for the endpoints of the Rubio de Francia type estimate of `ortho-apply`(ii),
is that *the clusters translate into disjoint frequency regions*:

* for `α ≠ α'` in `Σ_{(A₀)}` and any `A'₀ ⊆ A₀`, the translated clusters `α + Σ_{⊆A'₀}` and
  `α' + Σ_{⊆A'₀}` are disjoint — equivalently, `α − α'` is *not* annihilated by `Q_{A'₀}`.

This file proves the underlying arithmetic statement `sigmaCompQ_separation`: if
`α, α' ∈ Σ_{(A₀)}` and `Q_{A'₀}·(α − α') = 0`, then `α = α'`.

The proof: write `α ∈ Σ_A`, `α' ∈ Σ_{A'}` with `A, A' ⊆ S ∖ A₀`.  Multiplying the relation
`Q_{A'₀}(α − α') = 0` by `Q_{A'}` and using that `α` is annihilated by `Q_A` and `α'` by `Q_{A'}`
gives `Q_A ∣ Q_{A'}·Q_{A'₀}`; as `A ∩ A'₀ = ∅` the factors `Q_A`, `Q_{A'₀}` are coprime, so
`Q_A ∣ Q_{A'}`, and symmetrically `Q_{A'} ∣ Q_A`.  Hence `A = A'` (`QA_injective`), and then
`α − α'` is annihilated both by `Q_A` (difference of two points of `Σ_A`) and by `Q_{A'₀}`, two
coprime integers, so it vanishes.
-/

/-!
## The exact constant of the `ℓ¹` cluster bound on the exact-denominator clusters

The clusters `α + Σ_{A₀}` (`α ∈ Σ_{(A₀)}`) are **not** orthonormal, and — as shown in
`cluster_l1_bound.lean` (with a machine-checked refutation in
`cluster_l1_bound_counterexample.lean`) — **no constant uniform in `S` bounds**
`(1/Q_S)∑_y ‖∑_{α ∈ Σ_{(A₀)}} c_α ∑_{γ ∈ Σ_{A₀}} e((α+γ)y/Q_S)‖` in terms of `(∑_α ‖c_α‖²)^{1/2}`.
The exact operator norm is

`sup_{‖c‖₂ ≤ 1} (1/Q_S)∑_y ‖…‖ = (1/Q_{A₀})∑_{t ∈ ZMod Q_{A₀}} |c_{Q_{A₀}}(t)| = ∏_{p ∣ Q_{A₀}} (2 − 2/p)`,

where `c_{Q_{A₀}}` is the Ramanujan sum and `p` runs over the prime divisors of `Q_{A₀}`.  Indeed:

* every `α ∈ Σ_A` with `A ⊆ S∖A₀` is a multiple of `Q_{A₀}` (both as an integer representative and
  in `ZMod (QA S)`: `Q_{A₀} ∣ Q_S/Q_A`), so `y ↦ e(αy/Q_S)` is constant on the cosets of
  `H_S := ⟨Q_S/Q_{A₀}⟩`; dually every `γ ∈ Σ_{A₀}` is a multiple of `Q_S/Q_{A₀}`, so
  `S(y) := ∑_{γ ∈ Σ_{A₀}} e(γy/Q_S)` is constant on the cosets of `H_A := ⟨Q_{A₀}⟩`;
* `H_S ∩ H_A = {0}` (an element that is a multiple of both `Q_S/Q_{A₀}` and `Q_{A₀}` is `0`) and
  `|H_S|·|H_A| = Q_S` (`mul_div_injective`, `mul_QA_injective`, `exists_mul_QA_of_mul_div_eq_zero`),
  so the addition map `H_S × H_A → ZMod Q_S` is a bijection (cardinalities) and the sum over `y`
  factorises:
  `(1/Q_S)∑_y |A(y)S(y)| = [(1/|H_S|)∑_{h∈H_S}|S(h)|]·[(1/|H_A|)∑_{h∈H_A}|A(h)|]`
  where `A(y) = ∑_{α ∈ Σ_{(A₀)}} c_α e(αy/Q_S)`;
* on `H_A ≅ ZMod (Q_S/Q_{A₀})` the characters `χ_α = e(α·/Q_S)` are orthonormal: the separation
  condition is `Q_{A₀}(α−α') = 0`, which holds whenever `(Q_S/Q_{A₀}) ∣ α−α'`, and then
  `sigmaCompQ_separation` gives `α = α'`.  Hence Cauchy–Schwarz gives
  `(1/|H_A|)∑_{h ∈ H_A}|A(h)| ≤ sqrt((1/|H_A|)∑_{h}|A(h)|²) = sqrt(∑_α ‖c_α‖²)`;
* `S` restricted to `H_S` is the Ramanujan sum over `ZMod Q_{A₀}` (the sum over the units), whose
  `L¹`-mean is `∏_{p ∣ Q_{A₀}}(2−2/p)` (for a prime `q` the mean is `2(q−1)/q`; for a prime power
  `q = p^e` it is `2 − 2/p` for every `e ≥ 1`, by the recursion `c_{p^e}(t) = 0` for `p ∤ t` and
  `c_{p^e}(t) = p·c_{p^{e-1}}(t/p)` for `p ∣ t`).

Beware: `∏_{q ∈ A₀} 2(q−1)/q` is the mean **only when every `q ∈ A₀` is prime**; e.g.
`S = A₀ = {15}` gives `(4/3)(8/5) = 32/15 > 2 = 2^{|A₀|}` (machine-checked in
`cluster_l1_bound_counterexample.lean`), so no bound with the constant `2^{A₀.card}` holds.  For the
Ionescu–Wainger application — where `S = taoSetS ρ N` even contains the single composite element
`∏_{p ≤ N^{ρ/2}} p^{⌊log N/log p⌋}` — this constant is `exp(Θ(N^{ρ/2}/log N))`, so the `ℓ^∞` endpoint
must instead be formulated with the *torsion* clusters `Σ_{⊆A'₀}`
(`cluster_l1_bound_sigmaSub`, constant `1`).
-/


open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- Unfolding of membership in `sigmaCompQ`: `α ∈ Σ_{(A₀)}` means `α ∈ Σ_A` for some
`A ⊆ S ∖ A₀` with `A.card ≤ k − A₀.card`. -/
lemma mem_sigmaCompQ {Q : ℕ} {S : Finset ℕ} {k : ℕ} {A₀ : Finset ℕ} {α : ZMod Q} :
    α ∈ sigmaCompQ Q S k A₀ ↔
      ∃ A, A ⊆ S \ A₀ ∧ A.card ≤ k - A₀.card ∧ α ∈ sigmaAQ Q A := by
  classical
  simp only [sigmaCompQ, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨A, ⟨hA, hc⟩, hα⟩; exact ⟨A, hA, hc, hα⟩
  · rintro ⟨A, hA, hc, hα⟩; exact ⟨A, ⟨hA, hc⟩, hα⟩

/-- **Separation of the clusters `Σ_{(A₀)}` at the level `A'₀ ⊆ A₀`.**

Let `S` be a finite set of pairwise coprime integers `≥ 2`, let `A'₀ ⊆ A₀ ⊆ S` and let
`α, α' ∈ Σ_{(A₀)} = ⋃_{A ⊆ S∖A₀} Σ_A` (with the truncation `|A| ≤ k − |A₀|`).  If
`Q_{A'₀}·(α − α') = 0` in `ZMod (Q_S)` — equivalently, if the cluster characters
`e(α y/Q_S)` and `e(α' y/Q_S)` agree on the torsion subgroup `Σ_{⊆A'₀}` — then `α = α'`.

For `A'₀ = A₀` this says that the clusters `α + Σ_{A₀}`, `α ∈ Σ_{(A₀)}`, are pairwise disjoint
(the uniqueness of the representation `β = α + γ` of `ortho-apply`(i)); for the
`a/Q_{A'₀}`-arcs of `ortho`(i) with `A'₀ ⊆ A₀` it is the disjointness of the translates
`α + Σ_{⊆ A'₀}` used at the `ℓ^∞` endpoint of the Rubio de Francia estimate. -/
theorem sigmaCompQ_separation {S : Finset ℕ} [NeZero (QA S)]
    (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {k : ℕ} {A₀ A'₀ : Finset ℕ} (hA'₀ : A'₀ ⊆ A₀) (hA₀ : A₀ ⊆ S)
    {α α' : ZMod (QA S)}
    (hα : α ∈ sigmaCompQ (QA S) S k A₀) (hα' : α' ∈ sigmaCompQ (QA S) S k A₀)
    (h : (QA A'₀ : ZMod (QA S)) * (α - α') = 0) : α = α' := by
  classical
  obtain ⟨A, hA, -, hαA⟩ := mem_sigmaCompQ.mp hα
  obtain ⟨A', hA', -, hαA'⟩ := mem_sigmaCompQ.mp hα'
  have hAS : A ⊆ S := fun q hq => (Finset.mem_sdiff.mp (hA hq)).1
  have hA'S : A' ⊆ S := fun q hq => (Finset.mem_sdiff.mp (hA' hq)).1
  have hdisj : ∀ q ∈ A, q ∉ A'₀ := fun q hq hq' => (Finset.mem_sdiff.mp (hA hq)).2 (hA'₀ hq')
  have hdisj' : ∀ q ∈ A', q ∉ A'₀ := fun q hq hq' => (Finset.mem_sdiff.mp (hA' hq)).2 (hA'₀ hq')
  have hcopA : Nat.Coprime (QA A) (QA A'₀) :=
    coprime_QA_of_disjoint fun q hq q' hq' =>
      hS q (hAS hq) q' (hA₀ (hA'₀ hq')) (fun he => hdisj q hq (he ▸ hq'))
  have hcopA' : Nat.Coprime (QA A') (QA A'₀) :=
    coprime_QA_of_disjoint fun q hq q' hq' =>
      hS q (hA'S hq) q' (hA₀ (hA'₀ hq')) (fun he => hdisj' q hq (he ▸ hq'))
  have hdivA : QA A ∣ QA S := Finset.prod_dvd_prod_of_subset A S (fun i => i) hAS
  have hdivA' : QA A' ∣ QA S := Finset.prod_dvd_prod_of_subset A' S (fun i => i) hA'S
  -- the two frequencies agree on the torsion subgroup generated by `A'₀`
  have hstep : (QA A'₀ : ZMod (QA S)) * α = (QA A'₀ : ZMod (QA S)) * α' := by
    rw [mul_sub] at h
    exact sub_eq_zero.mp h
  -- multiplying by `Q_{A'}` and killing the `Σ_{A'}`-term gives `Q_A ∣ Q_{A'} Q_{A'₀}`
  have hzero : ((QA A' * QA A'₀ : ℕ) : ZMod (QA S)) * α = 0 := by
    have h2' : (QA A' : ZMod (QA S)) * α' = 0 := sigmaAQ_mul_QA_eq_zero hdivA' hαA'
    rw [Nat.cast_mul]
    calc (QA A' : ZMod (QA S)) * (QA A'₀ : ZMod (QA S)) * α
        = (QA A' : ZMod (QA S)) * ((QA A'₀ : ZMod (QA S)) * α) := by ring
      _ = (QA A' : ZMod (QA S)) * ((QA A'₀ : ZMod (QA S)) * α') := by rw [hstep]
      _ = (QA A' : ZMod (QA S)) * α' * (QA A'₀ : ZMod (QA S)) := by ring
      _ = 0 := by rw [h2', zero_mul]
  have hdvd1 : QA A ∣ QA A' := hcopA.dvd_of_dvd_mul_right
    (dvd_of_sigmaAQ_mul_eq_zero hdivA hαA hzero)
  -- and symmetrically `Q_{A'} ∣ Q_A`
  have hzero' : ((QA A * QA A'₀ : ℕ) : ZMod (QA S)) * α' = 0 := by
    have h2' : (QA A : ZMod (QA S)) * α = 0 := sigmaAQ_mul_QA_eq_zero hdivA hαA
    rw [Nat.cast_mul]
    calc (QA A : ZMod (QA S)) * (QA A'₀ : ZMod (QA S)) * α'
        = (QA A : ZMod (QA S)) * ((QA A'₀ : ZMod (QA S)) * α') := by ring
      _ = (QA A : ZMod (QA S)) * ((QA A'₀ : ZMod (QA S)) * α) := by rw [← hstep]
      _ = (QA A : ZMod (QA S)) * α * (QA A'₀ : ZMod (QA S)) := by ring
      _ = 0 := by rw [h2', zero_mul]
  have hdvd2 : QA A' ∣ QA A := hcopA'.dvd_of_dvd_mul_right
    (dvd_of_sigmaAQ_mul_eq_zero hdivA' hαA' hzero')
  have hQeq : QA A = QA A' := Nat.dvd_antisymm hdvd1 hdvd2
  have hAeq : A = A' := QA_injective h2 hS hAS hA'S hQeq
  have hα'A : α' ∈ sigmaAQ (QA S) A := by rw [hAeq]; exact hαA'
  have hkill : (QA A : ZMod (QA S)) * (α - α') = 0 := by
    rw [mul_sub, sigmaAQ_mul_QA_eq_zero hdivA hαA, sigmaAQ_mul_QA_eq_zero hdivA hα'A, sub_zero]
  exact sub_eq_zero.mp (eq_zero_of_coprime_mul_eq_zero hcopA hkill h)

/-- **Cluster separation at the exact denominator `Q_{A₀}`** (`A'₀ = A₀`): if `α, α' ∈ Σ_{(A₀)}`
and `α` and `α'` agree on the torsion subgroup `Σ_{⊆ A₀}` of the core, then `α = α'`. -/
theorem sigmaCompQ_separation_self {S : Finset ℕ} [NeZero (QA S)]
    (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {k : ℕ} {A₀ : Finset ℕ} (hA₀ : A₀ ⊆ S) {α α' : ZMod (QA S)}
    (hα : α ∈ sigmaCompQ (QA S) S k A₀) (hα' : α' ∈ sigmaCompQ (QA S) S k A₀)
    (h : (QA A₀ : ZMod (QA S)) * (α - α') = 0) : α = α' :=
  sigmaCompQ_separation h2 hS (Subset.refl A₀) hA₀ hα hα' h

/-! ## The character `iwChar` and the multiples of `Q_A` -/

/-- **`iwChar α y = 1` exactly when `α · y = 0`**: the standard additive character of `ZMod Q` is
faithful (`ZMod.injective_stdAddChar`). -/
lemma iwChar_eq_one_iff {Q : ℕ} [NeZero Q] (α y : ZMod Q) : iwChar α y = 1 ↔ α * y = 0 := by
  rw [iwChar_apply, ← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := Q))]
  exact ZMod.injective_stdAddChar.eq_iff

variable {S : Finset ℕ} [NeZero (QA S)]

/-- **Injectivity of the map `a ↦ a · (Q_S/Q_A)` on `{0, …, Q_A − 1}`.** -/
lemma mul_div_injective {A : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q) (hA : A ⊆ S) {a a' : ℕ}
    (ha : a < QA A) (ha' : a' < QA A)
    (he : ((a * (QA S / QA A) : ℕ) : ZMod (QA S))
        = ((a' * (QA S / QA A) : ℕ) : ZMod (QA S))) : a = a' := by
  have hQA : QA A ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hA hq)
  have hQ : QA S ≠ 0 := NeZero.ne (QA S)
  have hdiv : QA A ∣ QA S := Finset.prod_dvd_prod_of_subset A S (fun i => i) hA
  have hd : 0 < QA S / QA A :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hQ) hdiv) (Nat.pos_of_ne_zero hQA)
  have hmul : QA A * (QA S / QA A) = QA S := Nat.mul_div_cancel' hdiv
  have hlt1 : a * (QA S / QA A) < QA S :=
    lt_of_lt_of_eq ((Nat.mul_lt_mul_right hd).mpr ha) hmul
  have hlt2 : a' * (QA S / QA A) < QA S :=
    lt_of_lt_of_eq ((Nat.mul_lt_mul_right hd).mpr ha') hmul
  have hmod : (a * (QA S / QA A)) ≡ (a' * (QA S / QA A)) [MOD QA S] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp he
  exact Nat.mul_right_cancel hd (hmod.eq_of_lt_of_lt hlt1 hlt2)

/-- **Injectivity of the map `m ↦ m · Q_A` on `{0, …, Q_S/Q_A − 1}`.** -/
lemma mul_QA_injective {A : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q) (hA : A ⊆ S) {m m' : ℕ}
    (hm : m < QA S / QA A) (hm' : m' < QA S / QA A)
    (he : ((m * QA A : ℕ) : ZMod (QA S)) = ((m' * QA A : ℕ) : ZMod (QA S))) : m = m' := by
  have hQA : QA A ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hA hq)
  have hQ : QA S ≠ 0 := NeZero.ne (QA S)
  have hdiv : QA A ∣ QA S := Finset.prod_dvd_prod_of_subset A S (fun i => i) hA
  have hd : 0 < QA S / QA A :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hQ) hdiv) (Nat.pos_of_ne_zero hQA)
  have hmul : QA A * (QA S / QA A) = QA S := Nat.mul_div_cancel' hdiv
  have hlt1 : m * QA A < QA S := by
    have h : m * QA A < (QA S / QA A) * QA A :=
      (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hQA)).mpr hm
    rwa [mul_comm (QA S / QA A) (QA A), hmul] at h
  have hlt2 : m' * QA A < QA S := by
    have h : m' * QA A < (QA S / QA A) * QA A :=
      (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hQA)).mpr hm'
    rwa [mul_comm (QA S / QA A) (QA A), hmul] at h
  have hmod : (m * QA A) ≡ (m' * QA A) [MOD QA S] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp he
  exact Nat.mul_right_cancel (Nat.pos_of_ne_zero hQA) (hmod.eq_of_lt_of_lt hlt1 hlt2)

/-- **The kernel of `y ↦ (Q_S/Q_A)·y` consists of the multiples of `Q_A`**: every `y` annihilated by
`Q_S/Q_A` is `Q_A·m` for some `m < Q_S/Q_A`. -/
lemma exists_mul_QA_of_mul_div_eq_zero {A : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q) (hA : A ⊆ S)
    {y : ZMod (QA S)} (hy : ((QA S / QA A : ℕ) : ZMod (QA S)) * y = 0) :
    ∃ m : ℕ, m < QA S / QA A ∧ y = ((QA A * m : ℕ) : ZMod (QA S)) := by
  have hQA : QA A ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hA hq)
  have hQ : QA S ≠ 0 := NeZero.ne (QA S)
  have hdiv : QA A ∣ QA S := Finset.prod_dvd_prod_of_subset A S (fun i => i) hA
  have hd : 0 < QA S / QA A :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hQ) hdiv) (Nat.pos_of_ne_zero hQA)
  have hmul : QA A * (QA S / QA A) = QA S := Nat.mul_div_cancel' hdiv
  -- `y` as the cast of its value
  have hkey : (((QA S / QA A) * y.val : ℕ) : ZMod (QA S)) = 0 := by
    calc (((QA S / QA A) * y.val : ℕ) : ZMod (QA S))
        = ((QA S / QA A : ℕ) : ZMod (QA S)) * ((y.val : ℕ) : ZMod (QA S)) := by
          push_cast; ring
      _ = ((QA S / QA A : ℕ) : ZMod (QA S)) * y := by rw [ZMod.natCast_zmod_val y]
      _ = 0 := hy
  have hdvd : QA S ∣ (QA S / QA A) * y.val := by
    have hZ : (QA S : ℤ) ∣ (((QA S / QA A) * y.val : ℕ) : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by rw [Int.cast_natCast]; exact hkey)
    exact_mod_cast hZ
  have hdvd2 : (QA S / QA A) * QA A ∣ (QA S / QA A) * y.val := by
    have h : (QA S / QA A) * QA A = QA S := by rw [mul_comm]; exact hmul
    rwa [h]
  have hQA' : QA A ∣ y.val := Nat.dvd_of_mul_dvd_mul_left hd hdvd2
  obtain ⟨m, hm⟩ := hQA'
  refine ⟨m, ?_, ?_⟩
  · have hyv : QA A * m < QA A * (QA S / QA A) := by
      rw [← hm, hmul]
      exact ZMod.val_lt y
    exact (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hQA)).mp hyv
  · rw [← ZMod.natCast_zmod_val y, hm]

end Work.BourgainPlan.IonescuWainger
