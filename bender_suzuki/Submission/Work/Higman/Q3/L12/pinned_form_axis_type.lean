import Mathlib
import Submission.Work.Higman.Q3.L12.exists_pinned_form
import Submission.Work.Higman.Q3.L12.axis_realizable
import Submission.Work.Higman.Q3.axis_resonance
import Submission.Work.Higman.Q3.L12.pow_eq_frobenius_of_additive

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3.L12

open Work.Higman

/-! ## Helper lemmas for the axis types -/

/-- `2 ^ k` and `2 ^ (k % n)` are congruent modulo `2 ^ n - 1`. -/
private lemma two_pow_eq_modEq {n k : ℕ} :
    2 ^ k ≡ 2 ^ (k % n) [MOD 2 ^ n - 1] := by
  have h2n : 2 ^ n ≡ 1 [MOD 2 ^ n - 1] := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h := (Nat.modEq_iff_dvd' (n := 2 ^ n - 1) (a := 1) (b := 2 ^ n) h1).mpr dvd_rfl
    simpa using h.symm
  have h2k : 2 ^ k = (2 ^ n) ^ (k / n) * 2 ^ (k % n) := by
    conv_lhs => rw [← Nat.div_add_mod k n]
    rw [pow_add]
    congr 1
    rw [pow_mul]
  have h1 : (2 ^ n) ^ (k / n) ≡ 1 ^ (k / n) [MOD 2 ^ n - 1] := h2n.pow _
  rw [one_pow] at h1
  have h2 : 2 ^ (k % n) * (2 ^ n) ^ (k / n) ≡ 2 ^ (k % n) * 1 [MOD 2 ^ n - 1] :=
    (Nat.ModEq.refl (2 ^ (k % n))).mul h1
  rw [mul_one] at h2
  rw [h2k, mul_comm ((2 ^ n) ^ (k / n)) (2 ^ (k % n))]
  exact h2

/-- **The type of a pinned axis.**  Let `b : V → V → W` be biadditive, `φ : V ≃+ (𝔽 × 𝔽)`,
`ψ : W ≃+ 𝔽` with `𝔽 = 𝔽_{2ⁿ}`, `n ≥ 2`, and suppose the diagonal squaring form on the first
axis (`β = 0`) is the single monomial `α ↦ C α ^ a` with `C ≠ 0`, where `ν`, `λ ∈ 𝔽ˣ` satisfy
`orderOf ν = 2 ^ n - 1` and `ν ^ a = λ`.  Then the axis exponent is a sum of two Frobenius
powers: `ν ^ (2 ^ i) * ν ^ (2 ^ j) = λ` for some `i, j < n`.

This is the eigenvalue bookkeeping of Higman's Lemma 12: the axis `X = ⟨U, W⟩` is either abelian
(`Bp = 0`, and then `a ≡ 1`, i.e. `i = j = n - 1`) or the polar form of the squaring form on the
axis is a nonzero `ξ`-equivariant biadditive form, whose Frobenius expansion
(`Work.Higman.Q3.axis_resonance`) exhibits a nonzero bidegree `(i, j)`. -/
theorem axis_type_of_pinned_axis_aux
    {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    {b : V → V → W} [Biadd b]
    {n : ℕ} (hn : 2 ≤ n) (φ : V ≃+ (GaloisField 2 n × GaloisField 2 n)) (ψ : W ≃+ GaloisField 2 n)
    {ν lam : (GaloisField 2 n)ˣ} (hν : orderOf ν = 2 ^ n - 1)
    (a : ℕ) (C : GaloisField 2 n) (hC : C ≠ 0)
    (haν : (↑ν : GaloisField 2 n) ^ a = ↑lam)
    (hfax : ∀ α : GaloisField 2 n,
      ψ (b (φ.symm (α, 0)) (φ.symm (α, 0))) = C * α ^ a) :
    ∃ i j : ℕ, i < n ∧ j < n ∧
      (↑ν : GaloisField 2 n) ^ (2 ^ i) * (↑ν : GaloisField 2 n) ^ (2 ^ j) = ↑lam := by
  classical
  -- the squaring form in the eigen-coordinates, and its polar form
  let b' : (GaloisField 2 n × GaloisField 2 n) → (GaloisField 2 n × GaloisField 2 n) →
      GaloisField 2 n :=
    fun x y => ψ (b (φ.symm x) (φ.symm y))
  have hb'1 : ∀ x x' y, b' (x + x') y = b' x y + b' x' y := by
    intro x x' y
    show ψ (b (φ.symm (x + x')) (φ.symm y)) =
      ψ (b (φ.symm x) (φ.symm y)) + ψ (b (φ.symm x') (φ.symm y))
    rw [map_add φ.symm x x', Biadd.add_left (b := b) (φ.symm x) (φ.symm x') (φ.symm y), map_add ψ]
  have hb'2 : ∀ x y y', b' x (y + y') = b' x y + b' x y' := by
    intro x y y'
    show ψ (b (φ.symm x) (φ.symm (y + y'))) =
      ψ (b (φ.symm x) (φ.symm y)) + ψ (b (φ.symm x) (φ.symm y'))
    rw [map_add φ.symm y y', Biadd.add_right (b := b) (φ.symm x) (φ.symm y) (φ.symm y'),
      map_add ψ]
  haveI : Biadd b' := ⟨hb'1, hb'2⟩
  let g : GaloisField 2 n → GaloisField 2 n := fun α => b' (α, 0) (α, 0)
  have hg : ∀ α, g α = C * α ^ a := fun α => hfax α
  let Bp : GaloisField 2 n → GaloisField 2 n → GaloisField 2 n :=
    fun α γ => b' (α, 0) (γ, 0) + b' (γ, 0) (α, 0)
  have hpol : ∀ α γ, Bp α γ = g (α + γ) + g α + g γ := by
    intro α γ
    have h := q2_b_polar (b := b') (α, 0) (γ, 0)
    have h' : g (α + γ) + g α + g γ = Bp α γ := by
      show b' (α + γ, 0) (α + γ, 0) + b' (α, 0) (α, 0) + b' (γ, 0) (γ, 0) =
        b' (α, 0) (γ, 0) + b' (γ, 0) (α, 0)
      rw [show ((α + γ, 0) : GaloisField 2 n × GaloisField 2 n) = (α, 0) + (γ, 0) from rfl]
      exact h
    exact h'.symm
  have hBp1 : ∀ α α' γ, Bp (α + α') γ = Bp α γ + Bp α' γ := by
    intro α α' γ
    show b' (α + α', 0) (γ, 0) + b' (γ, 0) (α + α', 0) =
      (b' (α, 0) (γ, 0) + b' (γ, 0) (α, 0)) + (b' (α', 0) (γ, 0) + b' (γ, 0) (α', 0))
    rw [show ((α + α', 0) : GaloisField 2 n × GaloisField 2 n) = (α, 0) + (α', 0) from rfl,
      hb'1 (α, 0) (α', 0) (γ, 0), hb'2 (γ, 0) (α, 0) (α', 0)]
    abel
  have hBp2 : ∀ α γ γ', Bp α (γ + γ') = Bp α γ + Bp α γ' := by
    intro α γ γ'
    show b' (α, 0) (γ + γ', 0) + b' (γ + γ', 0) (α, 0) =
      (b' (α, 0) (γ, 0) + b' (γ, 0) (α, 0)) + (b' (α, 0) (γ', 0) + b' (γ', 0) (α, 0))
    rw [show ((γ + γ', 0) : GaloisField 2 n × GaloisField 2 n) = (γ, 0) + (γ', 0) from rfl,
      hb'2 (α, 0) (γ, 0) (γ', 0), hb'1 (γ, 0) (γ', 0) (α, 0)]
    abel
  haveI hBpi : Biadd Bp := ⟨hBp1, hBp2⟩
  -- `Bp` is `ξ`-equivariant with multiplier `lam` (via `ν ^ a = lam`)
  have hgν : ∀ μ : GaloisField 2 n, g ((↑ν) * μ) = (↑lam) * g μ := by
    intro μ
    rw [hg, hg, mul_pow, haν]
    ring
  have hBpeq : ∀ α γ, Bp ((↑ν) * α) ((↑ν) * γ) = (↑lam) * Bp α γ := by
    intro α γ
    rw [hpol, hpol, ← mul_add, hgν (α + γ), hgν α, hgν γ]
    ring
  -- the arithmetic endgame: `a ≡ 2 ^ r` gives the resonance with `i = j = r - 1`, resp. `n - 1`
  have hmain : ∀ r : ℕ, r < n → a ≡ 2 ^ r [MOD 2 ^ n - 1] →
      ∃ i j : ℕ, i < n ∧ j < n ∧
        (↑ν : GaloisField 2 n) ^ (2 ^ i) * (↑ν : GaloisField 2 n) ^ (2 ^ j) = ↑lam := by
    intro r hr har
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · refine ⟨n - 1, n - 1, by omega, by omega, ?_⟩
      have h2n : 2 ^ n ≡ 2 ^ 0 [MOD 2 ^ n - 1] := by
        have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        have h := (Nat.modEq_iff_dvd' (n := 2 ^ n - 1) (a := 1) (b := 2 ^ n) h1).mpr dvd_rfl
        simpa using h.symm
      have hsum : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
        rw [← two_mul, ← pow_succ']
        congr 1
        omega
      have hmod : 2 ^ n ≡ a [MOD 2 ^ n - 1] := by
        rw [hr0] at har
        simp only [pow_zero] at har
        exact h2n.trans har.symm
      have hu : ν ^ (2 ^ n) = ν ^ a := by
        rw [pow_eq_pow_iff_modEq, hν]; exact hmod
      rw [← pow_add, hsum]
      calc (↑ν : GaloisField 2 n) ^ (2 ^ n) = ↑(ν ^ (2 ^ n)) :=
            (Units.val_pow_eq_pow_val ν (2 ^ n)).symm
        _ = ↑(ν ^ a) := by rw [hu]
        _ = (↑ν : GaloisField 2 n) ^ a := Units.val_pow_eq_pow_val ν a
        _ = ↑lam := haν
    · refine ⟨r - 1, r - 1, by omega, by omega, ?_⟩
      have hsum : 2 ^ (r - 1) + 2 ^ (r - 1) = 2 ^ r := by
        rw [← two_mul, ← pow_succ']
        congr 1
        omega
      have hmod : 2 ^ r ≡ a [MOD 2 ^ n - 1] := har.symm
      have hu : ν ^ (2 ^ r) = ν ^ a := by
        rw [pow_eq_pow_iff_modEq, hν]; exact hmod
      rw [← pow_add, hsum]
      calc (↑ν : GaloisField 2 n) ^ (2 ^ r) = ↑(ν ^ (2 ^ r)) :=
            (Units.val_pow_eq_pow_val ν (2 ^ r)).symm
        _ = ↑(ν ^ a) := by rw [hu]
        _ = (↑ν : GaloisField 2 n) ^ a := Units.val_pow_eq_pow_val ν a
        _ = ↑lam := haν
  by_cases hBp0 : Bp = 0
  · -- the axis is abelian: `g` is additive, so `x ↦ x ^ a` is additive and `a ≡ 2 ^ k`
    have hgadd : ∀ α γ, g (α + γ) = g α + g γ := by
      intro α γ
      have hz : Bp α γ = 0 := by rw [hBp0]; rfl
      have h := hpol α γ
      rw [hz] at h
      exact AddExpTwo.eq_of_add_eq_zero (by rw [← add_assoc]; exact h.symm)
    have hmul : ∀ x y : GaloisField 2 n, (x + y) ^ a = x ^ a + y ^ a := by
      intro x y
      have h2 := hgadd x y
      rw [hg x, hg y, hg (x + y)] at h2
      refine mul_left_cancel₀ hC ?_
      rw [h2, mul_add]
    obtain ⟨k, hk⟩ := pow_eq_frobenius_of_additive (n := n) (a := a) (by omega) hmul
    exact hmain (k % n) (Nat.mod_lt k (by omega)) (hk.trans two_pow_eq_modEq)
  · -- the axis is non-abelian: the Frobenius resonance of `Bp`
    have hne : ∃ x y, Bp x y ≠ 0 := by
      by_contra hcon
      exact hBp0 (funext fun x => funext fun y => by
        by_contra hxy
        exact hcon ⟨x, y, hxy⟩)
    obtain ⟨α, γ, hαγ⟩ := hne
    obtain ⟨i, j, hi, hj, hpow⟩ := axis_resonance (b := Bp) hν hBpeq ⟨α, γ, hαγ⟩
    refine ⟨i, j, hi, hj, ?_⟩
    have h1 : (↑ν : GaloisField 2 n) ^ (2 ^ i + 2 ^ j) = ↑lam := by
      rw [← Units.val_pow_eq_pow_val, hpow]
    rwa [pow_add] at h1

/-- **The pinned shape of the squaring form, with the axis types.**

Same statement as `Work.Higman.Q3.L12.exists_pinned_form`, with two extra conjuncts recording the
*type* of the two order-`q²` subgroups `X = ⟨U,W⟩`, `Y = ⟨U',W⟩`: the axis exponent `a`
(resp. `a'`) is a sum of two Frobenius powers, equivalently `ν^{2^i} ν^{2^j} = λ`
(resp. `ν'^{2^i} ν'^{2^j} = λ`) for some `i, j < n`.

Derivation (the proof of `exists_pinned_form` can be copied and extended; its helpers
`subgroup_singer_aux`, `singer_W_iso_aux`, `decomp_add_equiv_aux` are public in that file):
the restricted form `B(α,γ) := ψ (b (φ.symm (α,0)) (φ.symm (γ,0)))` is biadditive with diagonal
`C α^a` (`C ≠ 0`), and it is equivariant for `(α,γ) ↦ (ν α, ν γ)` with multiplier `λ`: indeed,
since `ξ` is a `MulAut` of `TwoStep V W b` with induced maps `q2XiV`, `q2XiW`, one has
`b (q2XiV u) (q2XiV v) = q2XiW (b u v)` for all `u, v` (from the multiplication law of `TwoStep`;
the diagonal case `u = v` is `Work.Higman.q2_xiV_quad` in `twoStep_q2_normal_form.lean` — the
off-diagonal case follows by expanding the diagonal case at `u + v` and cancelling, or directly
from the definition of the `TwoStep` product).  Feeding this to
`Work.Higman.Q3.L12.axis_realizable` gives the first extra conjunct; the same argument with `U'`
in place of `U` gives the second. -/
theorem pinned_form_axis_type
    {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    [Finite V] [Finite W]
    {b : V → V → W} [Biadd b]
    (hcardV : Nat.card V = Nat.card W ^ 2) (hW : 4 ≤ Nat.card W)
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) (hord : orderOf ξ = Nat.card W - 1)
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y)
    (U U' : AddSubgroup V)
    (hUinv : ∀ v : V, v ∈ U → q2XiV hcenter ξ v ∈ U)
    (hU'inv : ∀ v : V, v ∈ U' → q2XiV hcenter ξ v ∈ U')
    (hsum : ∀ v : V, ∃ u ∈ U, ∃ u' ∈ U', u + u' = v)
    (hdisj : U ⊓ U' = ⊥)
    (hUcard : Nat.card ↥U = Nat.card W) (hU'card : Nat.card ↥U' = Nat.card W)
    (hUtrans : ∀ u : V, u ∈ U → u ≠ 0 → ∀ v : V, v ∈ U → v ≠ 0 →
      ∃ k : ℕ, ((q2XiV hcenter ξ : V → V)^[k]) u = v)
    (hU'trans : ∀ u : V, u ∈ U' → u ≠ 0 → ∀ v : V, v ∈ U' → v ≠ 0 →
      ∃ k : ℕ, ((q2XiV hcenter ξ : V → V)^[k]) u = v) :
    ∃ (n : ℕ) (φ : V ≃+ (GaloisField 2 n × GaloisField 2 n)) (ψ : W ≃+ GaloisField 2 n)
      (ν ν' lam : (GaloisField 2 n)ˣ) (a a' : ℕ) (C C' : GaloisField 2 n)
      (e : ℕ → ℕ → GaloisField 2 n),
      Nat.card W = 2 ^ n ∧ 1 ≤ n ∧
      orderOf ν = 2 ^ n - 1 ∧ orderOf ν' = 2 ^ n - 1 ∧ orderOf lam = 2 ^ n - 1 ∧
      C ≠ 0 ∧ C' ≠ 0 ∧ 1 ≤ a ∧ a ≤ 2 ^ n - 1 ∧ 1 ≤ a' ∧ a' ≤ 2 ^ n - 1 ∧
      (↑ν : GaloisField 2 n) ^ a = ↑lam ∧ (↑ν' : GaloisField 2 n) ^ a' = ↑lam ∧
      (∃ i j : ℕ, i < n ∧ j < n ∧
        (↑ν : GaloisField 2 n) ^ (2 ^ i) * (↑ν : GaloisField 2 n) ^ (2 ^ j) = ↑lam) ∧
      (∃ i j : ℕ, i < n ∧ j < n ∧
        (↑ν' : GaloisField 2 n) ^ (2 ^ i) * (↑ν' : GaloisField 2 n) ^ (2 ^ j) = ↑lam) ∧
      (∀ α : GaloisField 2 n, ψ (b (φ.symm (α, 0)) (φ.symm (α, 0))) = C * α ^ a) ∧
      (∀ β : GaloisField 2 n, ψ (b (φ.symm (0, β)) (φ.symm (0, β))) = C' * β ^ a') ∧
      (∀ k l : ℕ, e k l ≠ 0 →
        (↑ν : GaloisField 2 n) ^ (2 ^ k) * (↑ν' : GaloisField 2 n) ^ (2 ^ l) = ↑lam) ∧
      (∀ α β : GaloisField 2 n,
        ψ (b (φ.symm (α, β)) (φ.symm (α, β))) =
          C * α ^ a + C' * β ^ a' +
            ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, e k l * α ^ (2 ^ k) * β ^ (2 ^ l)) := by
  classical
  obtain ⟨n, φ, ψ, ν, ν', lam, a, a', C, C', e', hWcard, hn1, hνord, hν'ord, hlamord,
    hC, hC', ha1, haq, ha'1, ha'q, haνf, ha'νf, hfax, hfbx, hresf, hexp⟩ :=
    exists_pinned_form hcardV hW hinvol hcenter ξ hord htrans U U' hUinv hU'inv hsum hdisj
      hUcard hU'card hUtrans hU'trans
  have hn2 : 2 ≤ n := by
    have h4 : 2 ^ 2 ≤ 2 ^ n := by rw [← hWcard]; exact hW
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  have hXU : ∃ i j : ℕ, i < n ∧ j < n ∧
      (↑ν : GaloisField 2 n) ^ (2 ^ i) * (↑ν : GaloisField 2 n) ^ (2 ^ j) = ↑lam :=
    axis_type_of_pinned_axis_aux hn2 φ ψ hνord a C hC haνf hfax
  have hXU' : ∃ i j : ℕ, i < n ∧ j < n ∧
      (↑ν' : GaloisField 2 n) ^ (2 ^ i) * (↑ν' : GaloisField 2 n) ^ (2 ^ j) = ↑lam := by
    let φs : V ≃+ (GaloisField 2 n × GaloisField 2 n) := φ.trans AddEquiv.prodComm
    have hφs : ∀ β : GaloisField 2 n, φs.symm (β, 0) = φ.symm (0, β) := by
      intro β
      show φ.symm (AddEquiv.prodComm.symm (β, 0)) = φ.symm (0, β)
      congr 1
    exact axis_type_of_pinned_axis_aux hn2 φs ψ hν'ord a' C' hC' ha'νf
      (fun β => by rw [hφs β]; exact hfbx β)
  exact ⟨n, φ, ψ, ν, ν', lam, a, a', C, C', e', hWcard, hn1, hνord, hν'ord, hlamord,
    hC, hC', ha1, haq, ha'1, ha'q, haνf, ha'νf, hXU, hXU', hfax, hfbx, hresf, hexp⟩

end Work.Higman.Q3.L12
